import Muon.PowerLaw.Participation
import Muon.Drift.Defs
import Muon.DetEquiv.Branch
import Muon.Volatility.HalfCandidates

/-!
# Appendix G: the branch in participation coordinates and the drift at zero ridge, records
(work package L-G.12)

Snapshot `cr-2026-10-23`. Source: `sections/06-power-law/section.tex`, `prop:app-pl-branch`
(l.135–156) and the record of `prop:app-pl-drift-zero` (l.372–390), with the card §3, §5 rows.

Representation choices:

* The spectral measures are not constructed. `ν ν' : FiniteMeasure ℝ` are arguments with the
  defining measure equalities `ν = B⁻¹ ∑ δ_{μ_i}` and `ν' = γ δ_1` as hypotheses, plus
  `μ_i ≤ Cs`, `1 ≤ Cs`. These imply `(ν, ν') ∈ classK Cs γ`, the hypothesis of
  `Muon.DetEquiv.thm_app_de_branch_i`, so `branchSol` is the solution of `def:app-de-branch`.
* The branch is `Muon.DetEquiv.branchSol (Fw (emaW β)) ν ν'`; the coordinates are
  `(σ, σ̃, s̃₁, s₁) = (.1, .2.1, .2.2.1, .2.2.2)`. `q(-s) = s σ σ̃` is written out.
* `m(s)` is taken as an explicit `m ∈ (0,γ)` with `sN m = s` (the unique solution by
  `prop_app_pl_branch_i`), not as `mOf`.
* `𝔡_i(ϱ)` is `Muon.Drift.kernel (emaW β) ν ν' ϱ (μ i) 1` (`eqn:app-drift-kernel` with λ = 1,
  the record of `cor:app-drift-halfaniso`(i)).
* The `volraw_i` clauses of `prop:app-pl-branch`(iii) and `prop:app-pl-drift-zero`(i) use
  `Muon.Volatility.volraw` (`eqn:app-vol-half-candidates`, `Muon/Volatility/HalfCandidates.lean`,
  coordinator ruling: owned by L-G.12).
* The uniform bound `max_i` of `prop:app-pl-drift-zero`(ii) is written as `∀ i`.
-/

set_option linter.style.longLine false

open MeasureTheory Filter Topology Set
open Muon.DetEquiv

noncomputable section

namespace Muon.PowerLaw

/-! ### Private helpers for `prop_app_pl_branch_ii` (fully proved) -/

private lemma bl_gamma_pos {N B : ℕ} (hB : 0 < B) (hN : 0 < N) : 0 < gammaOf N B := by
  unfold gammaOf
  exact div_pos (by exact_mod_cast hN) (by exact_mod_cast hB)

private lemma bl_wseq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) : WeightSeq (emaW β) := by
  refine ⟨fun j => ?_, ?_, ⟨0, ?_⟩⟩
  · unfold emaW
    exact mul_nonneg (by linarith) (pow_nonneg hβ0 j)
  · have hg : Summable (fun j : ℕ => β ^ j) := summable_geometric_of_lt_one hβ0 hβ1
    have := hg.mul_left (1 - β)
    refine this.congr (fun j => ?_)
    simp [emaW]
  · unfold emaW
    rw [pow_zero, mul_one]
    exact (by linarith : (0:ℝ) < 1 - β).ne'

private lemma bl_rW_cont {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ContinuousOn (rW (emaW β)) (Ici 0) := by
  have hFc := (lem_app_de_scalar_ii (bl_wseq hβ0 hβ1)).2.2.1
  exact continuousOn_id.mul hFc

private lemma bl_rW_atTop {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (rW (emaW β)) atTop atTop := by
  have hT := (lem_app_de_scalar_iii (bl_wseq hβ0.le hβ1)).2.2.2.2.2.2
  have hset : {j : ℕ | 0 < emaW β j} = Set.univ := by
    ext j
    simp only [Set.mem_univ, iff_true]
    unfold emaW
    have h1 : (0:ℝ) < 1 - β := by linarith
    exact mul_pos h1 (pow_pos hβ0 j)
  rw [hset, Set.Infinite.encard_eq Set.infinite_univ, ENat.toENNReal_top] at hT
  refine tendsto_atTop.2 (fun K => ?_)
  have hlt : ENNReal.ofReal K < ⊤ := ENNReal.ofReal_lt_top
  filter_upwards [hT.eventually_const_lt hlt] with q hq
  exact ((ENNReal.ofReal_lt_ofReal_iff' ).1 hq).1.le

private lemma bl_rW_surj {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    ∃ a ∈ Ioi (0:ℝ), rW (emaW β) a = m := by
  have hcont := bl_rW_cont hβ0.le hβ1
  have hT := bl_rW_atTop hβ0 hβ1
  have hr0 : rW (emaW β) 0 = 0 := (lem_app_de_scalar_iii (bl_wseq hβ0.le hβ1)).2.2.1
  obtain ⟨b, hb⟩ := ((hT.eventually_gt_atTop m).and (eventually_gt_atTop (0:ℝ))).exists
  have hmem : m ∈ Icc (rW (emaW β) 0) (rW (emaW β) b) :=
    ⟨by rw [hr0]; exact hm.le, hb.1.le⟩
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hb.2.le (hcont.mono Icc_subset_Ici_self) hmem
  have hxpos : 0 < x := by
    rcases hx.1.eq_or_lt with h | h
    · exfalso
      rw [← h, hr0] at hfx
      linarith
    · exact h
  exact ⟨x, Set.mem_Ioi.2 hxpos, hfx⟩

private lemma bl_Qm_spec {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    0 < Qm β m ∧ rW (emaW β) (Qm β m) = m := by
  have hex : ∃ a ∈ Ioi (0:ℝ), rW (emaW β) a = m := bl_rW_surj hβ0 hβ1 hm
  exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩

private lemma bl_enorm_lt {x : ℝ} : ‖x‖ₑ < ⊤ := by
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_lt_top

private lemma bl_int_dirac_sum {N B : ℕ} (μ : Fin N → ℝ) (f : ℝ → ℝ) :
    ∫ t, f t ∂(ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i)) =
      (B : ℝ)⁻¹ * ∑ i, f (μ i) := by
  rw [integral_smul_measure, integral_finsetSum_measure (fun i _ => integrable_dirac bl_enorm_lt)]
  simp only [integral_dirac, ENNReal.toReal_ofReal (inv_nonneg.2 (Nat.cast_nonneg B)), smul_eq_mul]

/-- Auxiliary for the branch identity: the integral against `γ δ_1`. -/
private lemma bl_int_dirac_one (γ : ℝ) (hγ : 0 ≤ γ) (f : ℝ → ℝ) :
    ∫ t, f t ∂(ENNReal.ofReal γ • Measure.dirac (1 : ℝ)) = γ * f 1 := by
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hγ, smul_eq_mul]

private lemma bl_dirac_Icc_compl {a Cs : ℝ} (h : a ∈ Icc (0:ℝ) Cs) :
    Measure.dirac a (Icc 0 Cs)ᶜ = 0 := by
  rw [Measure.dirac_apply' _ measurableSet_Icc.compl]
  exact Set.indicator_of_notMem (show a ∉ (Icc (0:ℝ) Cs)ᶜ from fun hh => hh h) _


/-- `prop:app-pl-branch`(ii), snapshot `cr-2026-10-23`. LaTeX (the whole environment,
verbatim from `section.tex` l.135–156; this declaration is part (ii) of it, part (i) is
`prop_app_pl_branch_i`):

\begin{proposition}[The branch in participation coordinates]\label{prop:app-pl-branch}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item The function $s_N$ is a smooth strictly decreasing bijection of
$(0,\gamma)$ onto $(0,\infty)$, and
$-\frac{\dif}{\dif m}\log s_N(m)=\vartheta_N(m)>0$.
\item For $s>0$ let $m=m(s)\in(0,\gamma)$ be the solution of $s_N(m)=s$. Then
\begin{equation}\label{eqn:app-pl-branch}
\begin{gathered}
q(-s)=Q_m,\qquad \tilde s_1(-s)=s\,\Lambda_N(m),\qquad s_1(-s)=\frac{s\,m}{\gamma-m},\\
\sigma(-s)=\frac{m}{s\,\Lambda_N(m)},\qquad \tilde\sigma(-s)=\frac{\gamma-m}{s},\qquad
\frac{\tilde s_1(-s)\mu_i}{s+\tilde s_1(-s)\mu_i}=f_i(m).
\end{gathered}
\end{equation}
\item For every $\ridge>0$,
\begin{equation}\label{eqn:app-pl-drift-single}
\mathfrak d_i(\ridge)=\frac{\sqrt2}{\pi\gamma}\int_0^\infty
\frac{\Lw(Q_{m(\ridge+u^2)})}{\Fw(Q_{m(\ridge+u^2)})}\,f_i\big(m(\ridge+u^2)\big)\,\dif u,
\qquad \volraw_i(\ridge)=f_i\big(m(\ridge)\big).
\end{equation}
\end{enumerate}
\end{proposition} -/
theorem prop_app_pl_branch_ii {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {ν ν' : FiniteMeasure ℝ} {Cs : ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    (hμCs : ∀ i, μ i ≤ Cs) (h1Cs : 1 ≤ Cs)
    {s m : ℝ} (hs : 0 < s) (hm : m ∈ Ioo 0 (gammaOf N B)) (hsm : sN β B μ m = s) :
    s * (branchSol (Fw (emaW β)) ν ν' s).1 * (branchSol (Fw (emaW β)) ν ν' s).2.1 = Qm β m ∧
      (branchSol (Fw (emaW β)) ν ν' s).2.2.1 = s * partLam B μ m ∧
      (branchSol (Fw (emaW β)) ν ν' s).2.2.2 = s * m / (gammaOf N B - m) ∧
      (branchSol (Fw (emaW β)) ν ν' s).1 = m / (s * partLam B μ m) ∧
      (branchSol (Fw (emaW β)) ν ν' s).2.1 = (gammaOf N B - m) / s ∧
      ∀ i : Fin N,
        (branchSol (Fw (emaW β)) ν ν' s).2.2.1 * μ i /
            (s + (branchSol (Fw (emaW β)) ν ν' s).2.2.1 * μ i) = partF B μ i m := by
  have hγ : 0 < gammaOf N B := bl_gamma_pos hB hN
  have hC : 0 < Cs := lt_of_lt_of_le one_pos h1Cs
  have hw := bl_wseq hβ0.le hβ1
  have hmγ : 0 < gammaOf N B - m := sub_pos.2 hm.2
  have hmγne : gammaOf N B - m ≠ 0 := hmγ.ne'
  have hγne : gammaOf N B ≠ 0 := hγ.ne'
  have hsne : s ≠ 0 := hs.ne'
  obtain ⟨hQ, hrQ⟩ := bl_Qm_spec hβ0 hβ1 hm.1
  have hFQ : Fw (emaW β) (Qm β m) = m / Qm β m := by
    have h' : Qm β m * Fw (emaW β) (Qm β m) = m := hrQ
    exact eq_div_of_mul_eq hQ.ne' (by rw [mul_comm]; exact h')
  obtain ⟨hbMN, hbLam, -, -⟩ := def_app_pl_participation_bij μ hB hN hpos
  have hL : 0 < partLam B μ m := hbLam.mapsTo hm
  have hMN : partMN B μ (partLam B μ m) = m := hbMN.invOn_invFunOn.2 hm
  have hkey : s * (Qm β m * partLam B μ m) = (gammaOf N B - m) * m := by
    have h := hsm
    unfold sN at h
    rw [← h]
    exact div_mul_cancel₀ _ (mul_ne_zero hQ.ne' hL.ne')
  set Q := Qm β m with hQdef
  set L := partLam B μ m with hLdef
  have hLne : L ≠ 0 := hL.ne'
  have hμ1 : ∀ i, 0 < 1 + L * μ i := fun i => by
    have := mul_pos hL (hpos i); linarith
  have hq : s * (m / (s * L)) * ((gammaOf N B - m) / s) = Q := by
    field_simp
    linear_combination -hkey
  have hclass : (ν, ν') ∈ classK Cs (gammaOf N B) := by
    have hd : ∀ i, Measure.dirac (μ i) (Icc 0 Cs) = 1 := fun i =>
      Measure.dirac_apply_of_mem ⟨(hpos i).le, hμCs i⟩
    have hdc : ∀ i, Measure.dirac (μ i) (Icc 0 Cs)ᶜ = 0 := fun i =>
      bl_dirac_Icc_compl ⟨(hpos i).le, hμCs i⟩
    have h1mem : (1 : ℝ) ∈ Icc (0:ℝ) Cs := ⟨zero_le_one, h1Cs⟩
    simp only [classK, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hν]
      simp only [Measure.smul_apply, Measure.finsetSum_apply, hd, smul_eq_mul,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (inv_nonneg.2 (Nat.cast_nonneg B))]
      apply le_of_eq
      congr 1
      unfold gammaOf
      ring
    · rw [hν]
      simp only [Measure.smul_apply, Measure.finsetSum_apply, hdc, smul_eq_mul,
        Finset.sum_const_zero, mul_zero]
    · rw [hν']
      simp only [Measure.smul_apply, Measure.dirac_apply_of_mem h1mem, smul_eq_mul, mul_one]
      exact le_rfl
    · rw [hν', Measure.smul_apply, bl_dirac_Icc_compl h1mem, smul_zero]
  have hsolve := branchSol_spec (Fw_admissible hw) hC hγ hclass hs
  have hcand : IsBranchSol (Fw (emaW β)) ν ν' s
      (m / (s * L), (gammaOf N B - m) / s, s * L, s * m / (gammaOf N B - m)) := by
    unfold IsBranchSol
    dsimp only
    rw [hq, hFQ]
    refine ⟨div_nonneg hm.1.le (mul_nonneg hs.le hL.le), div_nonneg hmγ.le hs.le,
      mul_nonneg hs.le hL.le, div_nonneg (mul_nonneg hs.le hm.1.le) hmγ.le, ?_, ?_, ?_, ?_⟩
    · have hint := bl_int_dirac_sum (B := B) μ (fun t => t / (s * L * t + s))
      rw [hν, hint]
      have hterm : ∀ i, μ i / (s * L * μ i + s) = (s * L)⁻¹ * (L * μ i / (1 + L * μ i)) := by
        intro i
        have h3 : s * L * μ i + s ≠ 0 := by
          have := mul_pos (mul_pos hs hL) (hpos i)
          have := mul_pos hs (hμ1 i)
          nlinarith
        have h1 : 1 + L * μ i ≠ 0 := (hμ1 i).ne'
        have h2 : s * L ≠ 0 := (mul_pos hs hL).ne'
        field_simp
        ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum]
      have hS : (B : ℝ)⁻¹ * ∑ i, L * μ i / (1 + L * μ i) = m := hMN
      linear_combination -(s * L)⁻¹ * hS
    · have hint := bl_int_dirac_one (gammaOf N B) hγ.le (fun t => t / (s * m / (gammaOf N B - m) * t + s))
      rw [hν', hint]
      have hd : s * m / (gammaOf N B - m) * 1 + s = s * gammaOf N B / (gammaOf N B - m) := by
        field_simp
        ring
      rw [hd]
      field_simp
    · have e1 : s * ((gammaOf N B - m) / s) = gammaOf N B - m := by field_simp
      rw [e1]
      field_simp
      linear_combination hkey
    · field_simp
      linear_combination m * hkey
  have hbs := (thm_app_de_branch_i (Fw_admissible hw) hC hγ ν ν' hclass s hs).1.unique hsolve hcand
  rw [hbs]
  refine ⟨?_, rfl, rfl, rfl, rfl, ?_⟩
  · exact hq
  · intro i
    dsimp only
    unfold partF
    rw [← hLdef]
    have h1 : 1 + L * μ i ≠ 0 := (hμ1 i).ne'
    have h2 : s + s * L * μ i ≠ 0 := by
      have := mul_pos hs (hμ1 i)
      nlinarith
    rw [div_eq_div_iff h2 h1]
    ring

/-- Helper: `m(s)` lies in `(0,γ)` and solves `s_N(m) = s`, for `s > 0`. -/
private lemma bl_mOf_spec {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i) {s : ℝ} (hs : 0 < s) :
    mOf β B μ s ∈ Ioo 0 (gammaOf N B) ∧ sN β B μ (mOf β B μ s) = s := by
  have hbij := (prop_app_pl_branch_i μ hβ0 hβ1 hB hN hanti hpos).2.2.1
  obtain ⟨x, hx, hfx⟩ := hbij.surjOn (show s ∈ Ioi (0:ℝ) from hs)
  have hex : ∃ a ∈ Ioo (0:ℝ) (gammaOf N B), sN β B μ a = s := ⟨x, hx, hfx⟩
  unfold mOf
  exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩

/-- Helper: the integrand identity of `prop_app_pl_branch_iii_kernel`, pointwise in `z > 0`. -/
private lemma bl_kernel_pt {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {ν ν' : FiniteMeasure ℝ} {Cs : ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    (hμCs : ∀ i, μ i ≤ Cs) (h1Cs : 1 ≤ Cs)
    {z : ℝ} (hz : 0 < z) (i : Fin N) :
    z * Lw (emaW β) (Muon.Drift.branchQ (emaW β) ν ν' z) * μ i * 1 /
      ((z + (branchSol (Fw (emaW β)) ν ν' z).2.2.1 * μ i) *
        (z + (branchSol (Fw (emaW β)) ν ν' z).2.2.2 * 1)) =
      (gammaOf N B)⁻¹ * Gfun β B μ i z := by
  have hγ : 0 < gammaOf N B := bl_gamma_pos hB hN
  obtain ⟨hmI, hsm⟩ := bl_mOf_spec μ hβ0 hβ1 hB hN hanti hpos hz
  obtain ⟨hbMN, hbLam, -, -⟩ := def_app_pl_participation_bij μ hB hN hpos
  obtain ⟨hb1, hb2, hb3, -, -, -⟩ :=
    prop_app_pl_branch_ii μ hβ0 hβ1 hB hN hanti hpos hν hν' hμCs h1Cs hz hmI hsm
  unfold Gfun
  unfold Muon.Drift.branchQ
  generalize mOf β B μ z = m at *
  obtain ⟨hm0, hmγ⟩ := hmI
  have hmγ' : 0 < gammaOf N B - m := sub_pos.2 hmγ
  have hL : 0 < partLam B μ m := hbLam.mapsTo ⟨hm0, hmγ⟩
  have hQ : 0 < Qm β m := (bl_Qm_spec hβ0 hβ1 hm0).1
  have hrQ : rW (emaW β) (Qm β m) = m := (bl_Qm_spec hβ0 hβ1 hm0).2
  have hFQ : Fw (emaW β) (Qm β m) = m / Qm β m := by
    have h' : Qm β m * Fw (emaW β) (Qm β m) = m := hrQ
    exact eq_div_of_mul_eq hQ.ne' (by rw [mul_comm]; exact h')
  have hkey : z * (Qm β m * partLam B μ m) = (gammaOf N B - m) * m := by
    have hQL : Qm β m * partLam B μ m ≠ 0 := (mul_pos hQ hL).ne'
    rw [← hsm]
    unfold sN
    exact div_mul_cancel₀ _ hQL
  have hμ1 : 0 < 1 + partLam B μ m * μ i := by
    have := mul_pos hL (hpos i)
    linarith
  rw [hb1, hb2, hb3, hFQ]
  unfold partF
  have hz' := hz.ne'
  have hm' := hm0.ne'
  have hmγne := hmγ'.ne'
  have hQne := hQ.ne'
  have hLne := hL.ne'
  have hγne := hγ.ne'
  have hμ1ne := hμ1.ne'
  have e1 : z + z * partLam B μ m * μ i = z * (1 + partLam B μ m * μ i) := by ring
  have e2 : z + z * m / (gammaOf N B - m) * 1 = z * gammaOf N B / (gammaOf N B - m) := by
    field_simp
    ring
  rw [e1, e2]
  field_simp
  congr 1
  linear_combination (-(Lw (emaW β) (Qm β m) * μ i)) * hkey


/-- `prop:app-pl-branch`(iii), first identity of `eqn:app-pl-drift-single`, snapshot
`cr-2026-10-23`. LaTeX: the same environment as `prop_app_pl_branch_ii`, verbatim from
`section.tex` l.135–156 (see that declaration).

The second identity `volraw_i(ϱ) = f_i(m(ϱ))` of part (iii) is stated as
`prop_app_pl_branch_iii_volraw`. -/
theorem prop_app_pl_branch_iii_kernel {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {ν ν' : FiniteMeasure ℝ} {Cs : ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    (hμCs : ∀ i, μ i ≤ Cs) (h1Cs : 1 ≤ Cs)
    {ϱ : ℝ} (hϱ : 0 < ϱ) (i : Fin N) :
    Muon.Drift.kernel (emaW β) ν ν' ϱ (μ i) 1 = dPart β B μ i ϱ := by
  have hγ : 0 < gammaOf N B := bl_gamma_pos hB hN
  have hint : ∫ u in Ioi (0:ℝ),
      (ϱ + u ^ 2) * Lw (emaW β) (Muon.Drift.branchQ (emaW β) ν ν' (ϱ + u ^ 2)) * μ i * 1 /
        ((ϱ + u ^ 2 + (branchSol (Fw (emaW β)) ν ν' (ϱ + u ^ 2)).2.2.1 * μ i) *
          (ϱ + u ^ 2 + (branchSol (Fw (emaW β)) ν ν' (ϱ + u ^ 2)).2.2.2 * 1)) =
      ∫ u in Ioi (0:ℝ), (gammaOf N B)⁻¹ * Gfun β B μ i (ϱ + u ^ 2) :=
    setIntegral_congr_fun measurableSet_Ioi (fun u _ =>
      bl_kernel_pt μ hβ0 hβ1 hB hN hanti hpos hν hν' hμCs h1Cs
        (add_pos_of_pos_of_nonneg hϱ (sq_nonneg u)) i)
  rw [integral_const_mul] at hint
  unfold Muon.Drift.kernel dPart
  rw [hint]
  field_simp

/-- Record of `prop:app-pl-drift-zero`(ii), snapshot `cr-2026-10-23`. LaTeX (the whole
environment, verbatim from `section.tex` l.372–390):

\begin{proposition}[Drift at zero ridge]\label{prop:app-pl-drift-zero}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item As $s\downarrow0$, $Q_{m(s)}\to Q_\gamma<\infty$ and
$s\,\Lambda_N(m(s))^2\to F_\star\,B^{-1}\sum_i\mu_i^{-1}$. For $0<s\le z_1$,
\begin{equation}\label{eqn:app-pl-deficit}
1-\volraw_i(s)=\frac1{1+\Lambda_N(m(s))\mu_i}\le D_i\sqrt s .
\end{equation}
\item The integral
\begin{equation}\label{eqn:app-pl-drift-zero}
\mathfrak d_i(0)\defeq\frac{\sqrt2}{\pi\gamma}\int_0^\infty\mathcal G_i(u^2)\,\dif u
\end{equation}
is finite, and for every $\ridge>0$
\begin{equation}\label{eqn:app-pl-drift-ridge}
\max_{1\le i\le N}\abs{\mathfrak d_i(\ridge)-\mathfrak d_i(0)}\le\frac{C_\bmom}{\gamma}\sqrt\ridge\,\big(1+\sqrt{Q_\gamma}\big),
\end{equation}
with $C_\bmom$ depending only on $\bmom$.
\end{enumerate}
\end{proposition} -/
theorem prop_app_pl_drift_zero_ii_kernel {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C : ℝ, ∀ (N B : ℕ) (μ : Fin N → ℝ) (ν ν' : FiniteMeasure ℝ) (Cs : ℝ),
      0 < B → 0 < N → Antitone μ → (∀ i, 0 < μ i) →
      (∀ i, μ i ≤ Cs) → 1 ≤ Cs →
      (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i) →
      (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ) →
      ∀ ϱ : ℝ, 0 < ϱ → ∀ i : Fin N,
        |Muon.Drift.kernel (emaW β) ν ν' ϱ (μ i) 1 - dZero β B μ i| ≤
          C / gammaOf N B * Real.sqrt ϱ * (1 + Real.sqrt (Qm β (gammaOf N B))) := by
  obtain ⟨C, hC⟩ := prop_app_pl_drift_zero_ii_bound hβ0 hβ1
  refine ⟨C, ?_⟩
  intro N B μ ν ν' Cs hB hN hanti hpos hμCs h1Cs hν hν' ϱ hϱ i
  rw [prop_app_pl_branch_iii_kernel μ hβ0 hβ1 hB hN hanti hpos hν hν' hμCs h1Cs hϱ i]
  exact hC N B μ hB hN hanti hpos ϱ hϱ i

/-- `prop:app-pl-branch`(iii), second conjunct `volraw_i(ϱ) = f_i(m(ϱ))` (`eqn:app-pl-drift-single`),
snapshot `cr-2026-10-23`. LaTeX: the environment of `prop_app_pl_branch_ii`, verbatim from
`section.tex` l.135–156. -/
theorem prop_app_pl_branch_iii_volraw {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {ν ν' : FiniteMeasure ℝ} {Cs : ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    (hμCs : ∀ i, μ i ≤ Cs) (h1Cs : 1 ≤ Cs)
    {ϱ : ℝ} (hϱ : 0 < ϱ) (i : Fin N) :
    Muon.Volatility.volraw β ν ν' (μ i) ϱ = partF B μ i (mOf β B μ ϱ) := by
  obtain ⟨hmI, hsm⟩ := bl_mOf_spec μ hβ0 hβ1 hB hN hanti hpos hϱ
  have h := (prop_app_pl_branch_ii μ hβ0 hβ1 hB hN hanti hpos hν hν' hμCs h1Cs hϱ hmI hsm).2.2.2.2.2 i
  unfold Muon.Volatility.volraw
  exact h

/-- Deficit record of `prop:app-pl-drift-zero`(i), snapshot `cr-2026-10-23`. LaTeX: the environment
of `prop_app_pl_drift_zero_ii_kernel`, verbatim from `section.tex` l.372–390, part (i) with
`volraw_i` (`eqn:app-pl-deficit`). The limits of part (i) are L-G.2's `prop_app_pl_drift_zero_i`. -/
theorem prop_app_pl_drift_zero_i_volraw {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {ν ν' : FiniteMeasure ℝ} {Cs : ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    (hμCs : ∀ i, μ i ≤ Cs) (h1Cs : 1 ≤ Cs)
    (i : Fin N) {s : ℝ} (hs : 0 < s) (hsz : s ≤ sN β B μ (partMN B μ 1)) :
    1 - Muon.Volatility.volraw β ν ν' (μ i) s = 1 / (1 + partLam B μ (mOf β B μ s) * μ i) ∧
      1 / (1 + partLam B μ (mOf β B μ s) * μ i) ≤
        (1 / μ i) * Real.sqrt ((1 + μ ⟨0, hN⟩) /
          (gammaOf N B * Fw (emaW β) (Qm β (gammaOf N B)))) * Real.sqrt s := by
  rw [prop_app_pl_branch_iii_volraw μ hβ0 hβ1 hB hN hanti hpos hν hν' hμCs h1Cs hs i]
  exact (prop_app_pl_drift_zero_i μ hβ0 hβ1 hB hN hanti hpos).2.2 i s hs hsz

end Muon.PowerLaw

end

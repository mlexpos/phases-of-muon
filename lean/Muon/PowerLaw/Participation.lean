import Muon.PowerLaw.Weights

/-!
# Appendix G: participation coordinates and the drift at zero ridge (work package L-G.2)

Snapshot `cr-2026-10-23`. Source: `sections/06-power-law/section.tex`, subsection
"The coefficients at finite spectrum and zero ridge" (`def:app-pl-participation` l.116–130 through
`lem:app-pl-drift-participation` l.1373–1382), with the card §2 representation.

Representation choices:

* Standing objects of the finite-N layer: spectrum `μ : Fin N → ℝ`, `B : ℕ`, `γ = N/B`
  (`gammaOf`), momentum `β`. The EMA functions `Qm`, `Efun`, `Aav` and the scalar functions
  `Fw`, `Lw` are those of `Muon.PowerLaw.Weights` and `Muon.DetEquiv` (reused, not redefined).
* `m_N`, `Λ_N = m_N⁻¹`, `m(s) = s_N⁻¹` are total extensions by `Function.invFunOn` on
  `Ioi 0` (for `Λ`) and `Ioo 0 γ` (for `m(s)`). Their values are meaningful on the stated
  ranges, and the statements below only use them there.
* The source's `volraw_i(s)` is the raw coefficient of `eqn:app-vol-half-candidates` (D).
  Its identity with `f_i(m(s))` is `prop:app-pl-branch`(iii), which belongs to L-G.12. Here
  `prop:app-pl-drift-zero`(i) is stated with `f_i(m(s))` in place of `volraw_i(s)`.
* `dZero` is `𝔡_i(0)` of `eqn:app-pl-drift-zero`. `dPart ϱ` is the right-hand side of
  `eqn:app-pl-drift-single`. Both are participation-coordinate objects. The identification of
  `dPart` with C's `driftKernel` is L-G.12.
* Deferred from this package: the bulk display of `lem:app-pl-drift-participation`
  (`eqn:app-pl-Bi-bulk`, which needs `assum:app-pl-regime` of L-G.3), and `prop:app-pl-branch`
  (ii),(iii) (L-G.12).
-/

set_option linter.style.longLine false

open MeasureTheory Filter Topology Set
open scoped ContDiff
open Muon.DetEquiv

noncomputable section

namespace Muon.PowerLaw

/-! ## Participation coordinates (`def:app-pl-participation`) -/

/-- `γ = N/B` (`section.tex` l.40–46, "The aspect ratio is `γ ≝ N/B`"). -/
def gammaOf (N B : ℕ) : ℝ := (N : ℝ) / (B : ℝ)

/-- Participation function `m_N(Λ) = (1/B) ∑_i Λμ_i/(1+Λμ_i)` (`def:app-pl-participation`,
`eqn:app-pl-participation`, `section.tex` l.116–130). -/
def partMN (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (Λ : ℝ) : ℝ :=
  (B : ℝ)⁻¹ * ∑ i, Λ * μ i / (1 + Λ * μ i)

/-- `Λ_N = m_N⁻¹ : (0,γ) → (0,∞)` (`def:app-pl-participation`, `eqn:app-pl-participation`).
Total extension by `Function.invFunOn` on `Ioi 0`. -/
def partLam (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (m : ℝ) : ℝ :=
  Function.invFunOn (partMN B μ) (Ioi 0) m

/-- `f_i(m) = Λ_N(m)μ_i/(1+Λ_N(m)μ_i)` (`def:app-pl-participation`, `eqn:app-pl-sm`). -/
def partF (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (m : ℝ) : ℝ :=
  partLam B μ m * μ i / (1 + partLam B μ m * μ i)

/-- `s_N(m) = (γ-m) m / (Q_m Λ_N(m))` (`def:app-pl-participation`, `eqn:app-pl-sm`). -/
def sN (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (m : ℝ) : ℝ :=
  (gammaOf N B - m) * m / (Qm β m * partLam B μ m)

/-- `ϑ_N(m) = 1/E(m) + Λ_N'(m)/Λ_N(m) + 1/(γ-m) - 1/m` (`def:app-pl-participation`,
`eqn:app-pl-sm`). -/
def thetaN (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (m : ℝ) : ℝ :=
  1 / Efun β m + deriv (partLam B μ) m / partLam B μ m + 1 / (gammaOf N B - m) - 1 / m

/-- `m(s)`, the solution in `(0,γ)` of `s_N(m) = s` (`prop:app-pl-branch`(ii), `section.tex`
l.141). Total extension by `Function.invFunOn` on `Ioo 0 γ`. -/
def mOf (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (s : ℝ) : ℝ :=
  Function.invFunOn (sN β B μ) (Ioo 0 (gammaOf N B)) s

/-- `𝒢_i(s) = L_β(Q_{m(s)})/F_β(Q_{m(s)}) · f_i(m(s))` (`eqn:app-pl-finite-constants`,
`section.tex` l.367–370). -/
def Gfun (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (s : ℝ) : ℝ :=
  Lw (emaW β) (Qm β (mOf β B μ s)) / Fw (emaW β) (Qm β (mOf β B μ s)) *
    partF B μ i (mOf β B μ s)

/-- `dZero i = (√2/(πγ)) ∫_0^∞ 𝒢_i(u²) du` (`eqn:app-pl-drift-zero`, `section.tex` l.381–383).
This is `𝔡_i(0)` in participation coordinates. -/
def dZero (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) : ℝ :=
  Real.sqrt 2 / (Real.pi * gammaOf N B) * ∫ u in Ioi (0 : ℝ), Gfun β B μ i (u ^ 2)

/-- `dPart β B μ i ϱ = (√2/(πγ)) ∫_0^∞ 𝒢_i(ϱ+u²) du`, the right-hand side of
`eqn:app-pl-drift-single` (`section.tex` l.151–152). Equals `𝔡_i(ϱ)` by
`prop:app-pl-branch`(iii), which is L-G.12. -/
def dPart (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (ϱ : ℝ) : ℝ :=
  Real.sqrt 2 / (Real.pi * gammaOf N B) * ∫ u in Ioi (0 : ℝ), Gfun β B μ i (ϱ + u ^ 2)

/-- `𝓑_i(m) = √((γ-m)/(mΛ_N(m))) f_i(m)` (`lem:app-pl-drift-participation`,
`eqn:app-pl-drift-m`, `section.tex` l.1366–1368). -/
def partBfun (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (m : ℝ) : ℝ :=
  Real.sqrt ((gammaOf N B - m) / (m * partLam B μ m)) * partF B μ i m

/-! ### Private helpers for `def_app_pl_participation_bij` -/

private lemma pl_term_mono {μ : ℝ} (hμ : 0 < μ) :
    StrictMonoOn (fun Λ : ℝ => Λ * μ / (1 + Λ * μ)) (Ici 0) := by
  intro a ha b hb hab
  have ha' : (0:ℝ) ≤ a := ha
  have hb' : (0:ℝ) ≤ b := hb
  have h1 : (0:ℝ) < 1 + a * μ := by nlinarith [mul_nonneg ha' hμ.le]
  have h2 : (0:ℝ) < 1 + b * μ := by nlinarith [mul_nonneg hb' hμ.le]
  change a * μ / (1 + a * μ) < b * μ / (1 + b * μ)
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith [mul_pos (sub_pos.2 hab) hμ]

private lemma pl_term_lt_one {Λ μ : ℝ} (hΛ : 0 < Λ) (hμ : 0 < μ) :
    0 < Λ * μ / (1 + Λ * μ) ∧ Λ * μ / (1 + Λ * μ) < 1 := by
  have h : 0 < Λ * μ := mul_pos hΛ hμ
  exact ⟨div_pos h (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩

private lemma pl_gamma_eq {N B : ℕ} : (B:ℝ)⁻¹ * (N:ℝ) = gammaOf N B := by
  unfold gammaOf
  rw [div_eq_inv_mul]

private lemma pl_partMN_mono {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) : StrictMonoOn (partMN B μ) (Ici 0) := by
  intro a ha b hb hab
  have hBr : (0:ℝ) < (B:ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hB)
  unfold partMN
  refine mul_lt_mul_of_pos_left ?_ hBr
  exact Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.2 ⟨⟨0, hN⟩⟩)
    (fun i _ => pl_term_mono (hpos i) ha hb hab)

private lemma pl_partMN_injOn {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) : Set.InjOn (partMN B μ) (Ioi 0) :=
  (pl_partMN_mono μ hB hN hpos).injOn.mono Ioi_subset_Ici_self

private lemma pl_partMN_mem {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) {Λ : ℝ} (hΛ : 0 < Λ) :
    partMN B μ Λ ∈ Ioo 0 (gammaOf N B) := by
  have hBr : (0:ℝ) < (B:ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hB)
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := Finset.univ_nonempty_iff.2 ⟨⟨0, hN⟩⟩
  rw [← pl_gamma_eq]
  unfold partMN
  constructor
  · exact mul_pos hBr (Finset.sum_pos (fun i _ => (pl_term_lt_one hΛ (hpos i)).1) hne)
  · have hs : ∑ i, Λ * μ i / (1 + Λ * μ i) < ∑ _i : Fin N, (1:ℝ) :=
      Finset.sum_lt_sum_of_nonempty hne (fun i _ => (pl_term_lt_one hΛ (hpos i)).2)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
    exact mul_lt_mul_of_pos_left hs hBr

private lemma pl_partMN_zero {N B : ℕ} (μ : Fin N → ℝ) : partMN B μ 0 = 0 := by
  simp [partMN]

private lemma pl_partMN_contOn {N B : ℕ} (μ : Fin N → ℝ) (hpos : ∀ i, 0 < μ i) :
    ContinuousOn (partMN B μ) (Ici 0) := by
  unfold partMN
  apply ContinuousOn.mul continuousOn_const
  apply continuousOn_finsetSum
  intro i _
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro x hx
  have hx' : (0:ℝ) ≤ x := hx
  have := mul_nonneg hx' (hpos i).le
  exact (show (0:ℝ) < 1 + x * μ i by linarith).ne'

private lemma pl_term_tendsto {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun Λ : ℝ => Λ * μ / (1 + Λ * μ)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun Λ : ℝ => 1 + Λ * μ) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_id.atTop_mul_const hμ)
  have h2 : Tendsto (fun Λ : ℝ => (1 + Λ * μ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h1
  have h3 : Tendsto (fun Λ : ℝ => 1 - (1 + Λ * μ)⁻¹) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub h2
  rw [sub_zero] at h3
  refine h3.congr' ?_
  filter_upwards [h1.eventually_gt_atTop 0] with Λ hΛ
  have hne : (1 + Λ * μ) ≠ 0 := hΛ.ne'
  field_simp
  ring

private lemma pl_partMN_tendsto {N B : ℕ} (μ : Fin N → ℝ) (hpos : ∀ i, 0 < μ i) :
    Tendsto (partMN B μ) atTop (𝓝 ((B:ℝ)⁻¹ * (N:ℝ))) := by
  unfold partMN
  have hs : Tendsto (fun Λ : ℝ => ∑ i, Λ * μ i / (1 + Λ * μ i)) atTop
      (𝓝 (∑ _i : Fin N, (1:ℝ))) :=
    tendsto_finsetSum _ (fun i _ => pl_term_tendsto (hpos i))
  have hsum : ∑ _i : Fin N, (1:ℝ) = (N:ℝ) := by simp
  rw [hsum] at hs
  exact hs.const_mul _

private lemma pl_partMN_surj {N B : ℕ} (μ : Fin N → ℝ) (_hB : 0 < B) (_hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) : Set.SurjOn (partMN B μ) (Ioi 0) (Ioo 0 (gammaOf N B)) := by
  intro t ht
  obtain ⟨ht0, htγ⟩ := ht
  have hlim := pl_partMN_tendsto (B := B) μ hpos
  rw [pl_gamma_eq] at hlim
  have hev := hlim.eventually_const_lt htγ
  obtain ⟨Λ₁, hΛ₁, hΛpos⟩ := (hev.and (eventually_gt_atTop (0:ℝ))).exists
  have hcont : ContinuousOn (partMN B μ) (Icc 0 Λ₁) :=
    (pl_partMN_contOn μ hpos).mono Icc_subset_Ici_self
  have hmem : t ∈ Icc (partMN B μ 0) (partMN B μ Λ₁) := by
    rw [pl_partMN_zero]
    exact ⟨ht0.le, hΛ₁.le⟩
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hΛpos.le hcont hmem
  have hxpos : 0 < x := by
    rcases hx.1.eq_or_lt with h | h
    · exfalso
      rw [← h, pl_partMN_zero] at hfx
      linarith
    · exact h
  exact ⟨x, Set.mem_Ioi.2 hxpos, hfx⟩

private lemma pl_partLam_spec {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    partMN B μ (partLam B μ m) = m ∧ partLam B μ m ∈ Ioi 0 := by
  have hex : ∃ a ∈ Ioi (0:ℝ), partMN B μ a = m := pl_partMN_surj μ hB hN hpos hm
  exact ⟨Function.invFunOn_eq hex, Function.invFunOn_mem hex⟩

private lemma pl_term_hasDeriv {μ x : ℝ} (hμ : 0 < μ) (hx : 0 < x) :
    HasDerivAt (fun Λ : ℝ => Λ * μ / (1 + Λ * μ)) (μ / (1 + x * μ) ^ 2) x := by
  have hne : (1 + x * μ) ≠ 0 := (show (0:ℝ) < 1 + x * μ by nlinarith [mul_pos hx hμ]).ne'
  have h1 : HasDerivAt (fun Λ : ℝ => Λ * μ) μ x := by
    simpa using (hasDerivAt_id x).mul_const μ
  have h2 : HasDerivAt (fun Λ : ℝ => 1 + Λ * μ) μ x := by
    simpa using h1.const_add 1
  have h3 := h1.div h2 hne
  convert h3 using 1
  field_simp
  ring

private lemma pl_partMN_hasDeriv {N B : ℕ} (μ : Fin N → ℝ) (hpos : ∀ i, 0 < μ i) {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt (partMN B μ) ((B:ℝ)⁻¹ * ∑ i, μ i / (1 + x * μ i) ^ 2) x := by
  unfold partMN
  exact HasDerivAt.const_mul _ (HasDerivAt.fun_sum (u := Finset.univ)
    (A := fun i Λ => Λ * μ i / (1 + Λ * μ i)) (A' := fun i => μ i / (1 + x * μ i) ^ 2)
    (fun i _ => pl_term_hasDeriv (hpos i) hx))

private lemma pl_partMN_contDiffAt {N B : ℕ} {μ : Fin N → ℝ} (hpos : ∀ i, 0 < μ i) {a : ℝ}
    (ha : 0 < a) : ContDiffAt ℝ ∞ (partMN B μ) a := by
  unfold partMN
  apply ContDiffAt.mul contDiffAt_const
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.div (by fun_prop) (by fun_prop)
  exact (show (0:ℝ) < 1 + a * μ i by nlinarith [mul_pos ha (hpos i)]).ne'

private lemma pl_partLam_contDiffAt {N B : ℕ} {μ : Fin N → ℝ} (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) {a : ℝ} (ha : 0 < a) :
    ContDiffAt ℝ ∞ (partLam B μ) (partMN B μ a) := by
  have hf : ContDiffAt ℝ ∞ (partMN B μ) a := pl_partMN_contDiffAt hpos ha
  have hder := pl_partMN_hasDeriv (B := B) μ hpos ha
  have hdpos : 0 < (B:ℝ)⁻¹ * ∑ i, μ i / (1 + a * μ i) ^ 2 := by
    apply mul_pos (inv_pos.2 (by exact_mod_cast hB))
    apply Finset.sum_pos (fun i _ => div_pos (hpos i) (pow_pos (by nlinarith [mul_pos ha (hpos i)]) 2))
    exact Finset.univ_nonempty_iff.2 ⟨⟨0, hN⟩⟩
  have hf' := hder.hasFDerivAt_equiv hdpos.ne'
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hgC := hf.to_localInverse hf' hn
  have hga := hf.localInverse_apply_image hf' hn
  have hR := (hf.hasStrictFDerivAt' hf' hn).eventually_right_inverse
  have hgpos : ∀ᶠ y in 𝓝 (partMN B μ a), 0 < hf.localInverse hf' hn y := by
    have hcont := hgC.continuousAt
    have h0 : ContinuousAt (fun _ : ℝ => (0:ℝ)) (partMN B μ a) := continuousAt_const
    refine h0.eventually_lt hcont ?_
    change (0:ℝ) < hf.localInverse hf' hn (partMN B μ a)
    rw [hga]
    exact ha
  have hmem : Ioo (0:ℝ) (gammaOf N B) ∈ 𝓝 (partMN B μ a) :=
    Ioo_mem_nhds (pl_partMN_mem μ hB hN hpos ha).1 (pl_partMN_mem μ hB hN hpos ha).2
  have heq : partLam B μ =ᶠ[𝓝 (partMN B μ a)] hf.localInverse hf' hn := by
    filter_upwards [hmem, hR, hgpos] with y hy hRy hgy
    obtain ⟨h1, h2⟩ := pl_partLam_spec μ hB hN hpos hy
    exact pl_partMN_injOn μ hB hN hpos h2 (Set.mem_Ioi.2 hgy) (h1.trans hRy.symm)
  exact hgC.congr_of_eventuallyEq heq

/-- `def:app-pl-participation` (snapshot `cr-2026-10-23`). Statement of the inline claim
(`section.tex` l.131–133, the paragraph after the definition), with the definition
(`section.tex` l.116–130) verbatim:

\begin{definition}[Participation coordinates]\label{def:app-pl-participation}
The participation function and its inverse are
\begin{equation}\label{eqn:app-pl-participation}
m_N(\Lambda)\defeq\frac1B\sum_{i=1}^N\frac{\Lambda\mu_i}{1+\Lambda\mu_i}\quad(\Lambda\ge0),\qquad
\Lambda_N\defeq m_N^{-1}:(0,\gamma)\to(0,\infty).
\end{equation}
For $0<m<\gamma$ put
\begin{equation}\label{eqn:app-pl-sm}
\begin{gathered}
f_i(m)\defeq\frac{\Lambda_N(m)\mu_i}{1+\Lambda_N(m)\mu_i},\qquad
s_N(m)\defeq\frac{(\gamma-m)\,m}{Q_m\,\Lambda_N(m)},\\
\vartheta_N(m)\defeq\frac1{E(m)}+\frac{\Lambda_N'(m)}{\Lambda_N(m)}+\frac1{\gamma-m}-\frac1m .
\end{gathered}
\end{equation}
\end{definition}


The function $m_N$ is strictly increasing from $0$ to $\gamma$, because each
of its $N$ terms is, so $\Lambda_N$ is well defined, increasing and smooth.

Proved here: `m_N` is a bijection of `(0,∞)` onto `(0,γ)`, `Λ_N` is its inverse, and `Λ_N` is
strictly increasing and smooth. -/
theorem def_app_pl_participation_bij {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) :
    Set.BijOn (partMN B μ) (Ioi 0) (Ioo 0 (gammaOf N B)) ∧
      Set.BijOn (partLam B μ) (Ioo 0 (gammaOf N B)) (Ioi 0) ∧
      StrictMonoOn (partLam B μ) (Ioo 0 (gammaOf N B)) ∧
      ContDiffOn ℝ ∞ (partLam B μ) (Ioo 0 (gammaOf N B)) := by
  have hmono := pl_partMN_mono μ hB hN hpos
  have hinj := pl_partMN_injOn μ hB hN hpos
  refine ⟨⟨fun x hx => pl_partMN_mem μ hB hN hpos (Set.mem_Ioi.1 hx), hinj,
    pl_partMN_surj μ hB hN hpos⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro m hm
    exact (pl_partLam_spec μ hB hN hpos hm).2
  · intro m1 hm1 m2 hm2 h
    have e1 := (pl_partLam_spec μ hB hN hpos hm1).1
    have e2 := (pl_partLam_spec μ hB hN hpos hm2).1
    rw [← e1, ← e2, h]
  · intro x hx
    have hxm := Set.mem_Ioi.1 hx
    have hm := pl_partMN_mem μ hB hN hpos hxm
    have s := pl_partLam_spec μ hB hN hpos hm
    exact ⟨partMN B μ x, hm, hinj (Set.mem_Ioi.2 s.2) hx s.1⟩
  · intro m1 hm1 m2 hm2 h12
    have s1 := pl_partLam_spec μ hB hN hpos hm1
    have s2 := pl_partLam_spec μ hB hN hpos hm2
    rw [← hmono.lt_iff_lt (Set.mem_Ici.2 (le_of_lt (Set.mem_Ioi.1 s1.2)))
      (Set.mem_Ici.2 (le_of_lt (Set.mem_Ioi.1 s2.2))), s1.1, s2.1]
    exact h12
  · intro m hm
    obtain ⟨h1, h2⟩ := pl_partLam_spec μ hB hN hpos hm
    have hc := pl_partLam_contDiffAt hB hN hpos (Set.mem_Ioi.1 h2)
    rw [h1] at hc
    exact hc.contDiffWithinAt

/-! ### Private helpers for `prop_app_pl_branch_i` (the EMA scalar functions) -/

private lemma pl_wseq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) : WeightSeq (emaW β) := by
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

private lemma pl_rW_facts {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ContinuousOn (rW (emaW β)) (Ici 0) ∧ ContDiffOn ℝ ∞ (rW (emaW β)) (Ioi 0) := by
  have hFc := (lem_app_de_scalar_ii (pl_wseq hβ0 hβ1)).2.2.1
  have hFd := (lem_app_de_scalar_ii (pl_wseq hβ0 hβ1)).2.2.2.2.1
  refine ⟨?_, ?_⟩
  · exact continuousOn_id.mul hFc
  · exact ((contDiffOn_id.mul hFd).mono Ioi_subset_Ici_self)

private lemma pl_rW_atTop {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (rW (emaW β)) atTop atTop := by
  have hT := (lem_app_de_scalar_iii (pl_wseq hβ0.le hβ1)).2.2.2.2.2.2
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

private lemma pl_rW_pos {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {a : ℝ} (ha : 0 < a) :
    0 < rW (emaW β) a := by
  have h := (lem_app_de_scalar_iii (pl_wseq hβ0 hβ1)).2.1 (Set.mem_Ici.2 le_rfl)
    (Set.mem_Ici.2 ha.le) ha
  rwa [(lem_app_de_scalar_iii (pl_wseq hβ0 hβ1)).2.2.1] at h

private lemma pl_rW_hasDeriv_pos {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℝ} (hx : 0 < x) :
    ∃ d, HasDerivAt (rW (emaW β)) d x ∧ 0 < d :=
  ⟨_, (lem_app_de_scalar_iii (pl_wseq hβ0 hβ1)).2.2.2.1 x hx,
    (lem_app_de_scalar_iii (pl_wseq hβ0 hβ1)).2.2.2.2.1 x hx⟩

private lemma pl_rW_surj {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    ∃ a ∈ Ioi (0:ℝ), rW (emaW β) a = m := by
  have hcont := (pl_rW_facts hβ0.le hβ1).1
  have hT := pl_rW_atTop hβ0 hβ1
  have hr0 : rW (emaW β) 0 = 0 := (lem_app_de_scalar_iii (pl_wseq hβ0.le hβ1)).2.2.1
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

private lemma pl_Qm_spec {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    0 < Qm β m ∧ rW (emaW β) (Qm β m) = m := by
  have hex : ∃ a ∈ Ioi (0:ℝ), rW (emaW β) a = m := pl_rW_surj hβ0 hβ1 hm
  exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩

private lemma pl_Qm_inv {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {a : ℝ} (ha : 0 < a) :
    Qm β (rW (emaW β) a) = a := by
  have hra := pl_rW_pos hβ0.le hβ1 ha
  obtain ⟨h1, h2⟩ := pl_Qm_spec hβ0 hβ1 hra
  exact (lem_app_de_scalar_iii (pl_wseq hβ0.le hβ1)).2.1.injOn (Set.mem_Ici.2 h1.le)
    (Set.mem_Ici.2 ha.le) h2

private lemma pl_Qm_contDiffAt {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {a : ℝ} (ha : 0 < a) :
    ContDiffAt ℝ ∞ (Qm β) (rW (emaW β) a) := by
  have hf : ContDiffAt ℝ ∞ (rW (emaW β)) a :=
    (pl_rW_facts hβ0.le hβ1).2.contDiffAt (Ioi_mem_nhds ha)
  obtain ⟨d, hder, hdpos⟩ := pl_rW_hasDeriv_pos hβ0.le hβ1 ha
  have hf' := hder.hasFDerivAt_equiv hdpos.ne'
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hgC := hf.to_localInverse hf' hn
  have hga := hf.localInverse_apply_image hf' hn
  have hR := (hf.hasStrictFDerivAt' hf' hn).eventually_right_inverse
  have hra := pl_rW_pos hβ0.le hβ1 ha
  have hgpos : ∀ᶠ y in 𝓝 (rW (emaW β) a), 0 < hf.localInverse hf' hn y := by
    have hcont := hgC.continuousAt
    have h0 : ContinuousAt (fun _ : ℝ => (0:ℝ)) (rW (emaW β) a) := continuousAt_const
    refine h0.eventually_lt hcont ?_
    change (0:ℝ) < hf.localInverse hf' hn (rW (emaW β) a)
    rw [hga]
    exact ha
  have hmem : Ioi (0:ℝ) ∈ 𝓝 (rW (emaW β) a) := Ioi_mem_nhds hra
  have heq : Qm β =ᶠ[𝓝 (rW (emaW β) a)] hf.localInverse hf' hn := by
    filter_upwards [hmem, hR, hgpos] with y hy hRy hgy
    obtain ⟨h1, h2⟩ := pl_Qm_spec hβ0 hβ1 (Set.mem_Ioi.1 hy)
    exact (lem_app_de_scalar_iii (pl_wseq hβ0.le hβ1)).2.1.injOn (Set.mem_Ici.2 h1.le)
      (Set.mem_Ici.2 hgy.le) (h2.trans hRy.symm)
  exact hgC.congr_of_eventuallyEq heq

private lemma pl_Qm_hasDeriv {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (Qm β) (1 / deriv (rW (emaW β)) a) (rW (emaW β) a) := by
  have hra := pl_rW_pos hβ0.le hβ1 ha
  have hQinv := pl_Qm_inv hβ0 hβ1 ha
  obtain ⟨d, hder, hdpos⟩ := pl_rW_hasDeriv_pos hβ0.le hβ1 ha
  have hQdiff : DifferentiableAt ℝ (Qm β) (rW (emaW β) a) :=
    (pl_Qm_contDiffAt hβ0 hβ1 ha).differentiableAt (by simp)
  have hQd := hQdiff.hasDerivAt
  have hcomp : HasDerivAt (rW (emaW β) ∘ Qm β) (d * deriv (Qm β) (rW (emaW β) a))
      (rW (emaW β) a) := by
    apply HasDerivAt.comp
    · rw [hQinv]
      exact hder
    · exact hQd
  have hid : HasDerivAt (rW (emaW β) ∘ Qm β) 1 (rW (emaW β) a) := by
    apply (hasDerivAt_id (rW (emaW β) a)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hra] with y hy
    exact (pl_Qm_spec hβ0 hβ1 (Set.mem_Ioi.1 hy)).2
  have hkey : d * deriv (Qm β) (rW (emaW β) a) = 1 := hcomp.unique hid
  have hdd : deriv (rW (emaW β)) a = d := hder.deriv
  have hQ1 : deriv (Qm β) (rW (emaW β) a) = 1 / d :=
    (eq_div_iff hdpos.ne').2 (by rw [mul_comm]; exact hkey)
  rw [hdd, ← hQ1]
  exact hQd

private lemma pl_partLam_hasDeriv {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    HasDerivAt (partLam B μ)
      (1 / ((B:ℝ)⁻¹ * ∑ i, μ i / (1 + partLam B μ m * μ i) ^ 2)) m := by
  have hΛ : 0 < partLam B μ m := (pl_partLam_spec μ hB hN hpos hm).2
  have hdiffL : DifferentiableAt ℝ (partLam B μ) m :=
    ((def_app_pl_participation_bij μ hB hN hpos).2.2.2.contDiffAt
      (Ioo_mem_nhds hm.1 hm.2)).differentiableAt (by simp)
  have hder := pl_partMN_hasDeriv (B := B) μ hpos hΛ
  have hcomp : HasDerivAt (partMN B μ ∘ partLam B μ)
      (((B:ℝ)⁻¹ * ∑ i, μ i / (1 + partLam B μ m * μ i) ^ 2) * deriv (partLam B μ) m) m :=
    HasDerivAt.comp m hder hdiffL.hasDerivAt
  have hid : HasDerivAt (partMN B μ ∘ partLam B μ) 1 m := by
    apply (hasDerivAt_id m).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hm.1 hm.2] with y hy
    exact (pl_partLam_spec μ hB hN hpos hy).1
  have hkey := hcomp.unique hid
  have hD : (B:ℝ)⁻¹ * ∑ i, μ i / (1 + partLam B μ m * μ i) ^ 2 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hkey
    exact zero_ne_one hkey
  have hL : deriv (partLam B μ) m =
      1 / ((B:ℝ)⁻¹ * ∑ i, μ i / (1 + partLam B μ m * μ i) ^ 2) := by
    rw [eq_div_iff hD, mul_comm]
    exact hkey
  rw [← hL]
  exact hdiffL.hasDerivAt

private lemma pl_Qm_hasDeriv' {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    HasDerivAt (Qm β) (1 / deriv (rW (emaW β)) (Qm β m)) m := by
  obtain ⟨hQ, hr⟩ := pl_Qm_spec hβ0 hβ1 hm
  have h := pl_Qm_hasDeriv hβ0 hβ1 hQ
  rw [hr] at h
  exact h

private lemma pl_Efun_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    0 < Efun β m := by
  obtain ⟨hQ, hr⟩ := pl_Qm_spec hβ0 hβ1 hm
  obtain ⟨d, hd, hdpos⟩ := pl_rW_hasDeriv_pos hβ0.le hβ1 hQ
  unfold Efun
  rw [hd.deriv]
  exact mul_pos hQ hdpos

private lemma pl_LD_lt {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) {Λ : ℝ} (hΛ : 0 < Λ) :
    Λ * ((B:ℝ)⁻¹ * ∑ i, μ i / (1 + Λ * μ i) ^ 2) < partMN B μ Λ := by
  have hBr : (0:ℝ) < (B:ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hB)
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := Finset.univ_nonempty_iff.2 ⟨⟨0, hN⟩⟩
  unfold partMN
  rw [← mul_assoc, mul_comm Λ (B:ℝ)⁻¹, mul_assoc, Finset.mul_sum]
  apply mul_lt_mul_of_pos_left _ hBr
  apply Finset.sum_lt_sum_of_nonempty hne
  intro i _
  have ht : 0 < Λ * μ i := mul_pos hΛ (hpos i)
  have h1 : 1 / (1 + Λ * μ i) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hx : 0 < Λ * μ i / (1 + Λ * μ i) := div_pos ht (by linarith)
  have heq : Λ * (μ i / (1 + Λ * μ i) ^ 2) = Λ * μ i / (1 + Λ * μ i) * (1 / (1 + Λ * μ i)) := by
    have hne' : (1 + Λ * μ i) ≠ 0 := by linarith
    field_simp
  rw [heq]
  exact mul_lt_of_lt_one_right hx h1

private lemma pl_sN_contDiffOn {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i) :
    ContDiffOn ℝ ∞ (sN β B μ) (Ioo 0 (gammaOf N B)) := by
  have hQcd : ContDiffOn ℝ ∞ (Qm β) (Ioo 0 (gammaOf N B)) := by
    intro m hm
    have hQ := (pl_Qm_spec hβ0 hβ1 hm.1).1
    have h := pl_Qm_contDiffAt hβ0 hβ1 hQ
    rw [(pl_Qm_spec hβ0 hβ1 hm.1).2] at h
    exact h.contDiffWithinAt
  have hLcd := (def_app_pl_participation_bij μ hB hN hpos).2.2.2
  have hnum : ContDiffOn ℝ ∞ (fun x : ℝ => (gammaOf N B - x) * x) (Ioo 0 (gammaOf N B)) :=
    (contDiffOn_const.sub contDiffOn_id).mul contDiffOn_id
  have hden : ContDiffOn ℝ ∞ (fun x : ℝ => Qm β x * partLam B μ x) (Ioo 0 (gammaOf N B)) :=
    hQcd.mul hLcd
  have hne : ∀ x ∈ Ioo 0 (gammaOf N B), Qm β x * partLam B μ x ≠ 0 := by
    intro x hx
    have hQ := (pl_Qm_spec hβ0 hβ1 hx.1).1
    have hL := (pl_partLam_spec μ hB hN hpos hx).2
    exact (mul_pos hQ hL).ne'
  exact hnum.div hden hne

private lemma pl_sN_pos {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i) {m : ℝ}
    (hm : m ∈ Ioo 0 (gammaOf N B)) : 0 < sN β B μ m := by
  obtain ⟨hm0, hmg⟩ := hm
  have hQ := (pl_Qm_spec hβ0 hβ1 hm0).1
  have hL := (pl_partLam_spec μ hB hN hpos ⟨hm0, hmg⟩).2
  unfold sN
  exact div_pos (mul_pos (sub_pos.2 hmg) hm0) (mul_pos hQ hL)

private lemma pl_thetaN_pos {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i) {m : ℝ}
    (hm : m ∈ Ioo 0 (gammaOf N B)) : 0 < thetaN β B μ m := by
  obtain ⟨hm0, hmg⟩ := hm
  have hL := (pl_partLam_spec μ hB hN hpos ⟨hm0, hmg⟩)
  have hΛ : 0 < partLam B μ m := hL.2
  have hD : 0 < (B:ℝ)⁻¹ * ∑ i, μ i / (1 + partLam B μ m * μ i) ^ 2 := by
    apply mul_pos (inv_pos.2 (by exact_mod_cast hB))
    apply Finset.sum_pos (fun i _ => div_pos (hpos i) (pow_pos (by nlinarith [mul_pos hΛ (hpos i)]) 2))
    exact Finset.univ_nonempty_iff.2 ⟨⟨0, hN⟩⟩
  have hlt := pl_LD_lt μ hB hN hpos hΛ
  rw [hL.1] at hlt
  have hcrit : 1 / m < 1 / (((B:ℝ)⁻¹ * ∑ i, μ i / (1 + partLam B μ m * μ i) ^ 2) *
      partLam B μ m) :=
    one_div_lt_one_div_of_lt (mul_pos hD hΛ) (by rw [mul_comm]; exact hlt)
  have hE := pl_Efun_pos hβ0 hβ1 hm0
  have hgm : 0 < 1 / (gammaOf N B - m) := one_div_pos.2 (sub_pos.2 hmg)
  have hE' : 0 < 1 / Efun β m := one_div_pos.2 hE
  have hderiv := pl_partLam_hasDeriv μ hB hN hpos ⟨hm0, hmg⟩
  unfold thetaN
  rw [hderiv.deriv, div_div]
  linarith [hcrit, hE', hgm]

private lemma pl_D_pos {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) {Λ : ℝ} (hΛ : 0 < Λ) :
    0 < (B:ℝ)⁻¹ * ∑ i, μ i / (1 + Λ * μ i) ^ 2 := by
  apply mul_pos (inv_pos.2 (by exact_mod_cast hB))
  apply Finset.sum_pos (fun i _ => div_pos (hpos i) (pow_pos (by nlinarith [mul_pos hΛ (hpos i)]) 2))
  exact Finset.univ_nonempty_iff.2 ⟨⟨0, hN⟩⟩

private lemma pl_sN_deriv_eq {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i) {m : ℝ}
    (hm : m ∈ Ioo 0 (gammaOf N B)) :
    deriv (sN β B μ) m = -(thetaN β B μ m) * sN β B μ m := by
  obtain ⟨hm0, hmg⟩ := hm
  have hgm : gammaOf N B - m ≠ 0 := (sub_pos.2 hmg).ne'
  obtain ⟨hQpos, hQr⟩ := pl_Qm_spec hβ0 hβ1 hm0
  have hΛ : 0 < partLam B μ m := (pl_partLam_spec μ hB hN hpos ⟨hm0, hmg⟩).2
  have hL := pl_partLam_hasDeriv μ hB hN hpos ⟨hm0, hmg⟩
  have hQd := pl_Qm_hasDeriv' hβ0 hβ1 hm0
  obtain ⟨rd, hrd, hrdpos⟩ := pl_rW_hasDeriv_pos hβ0.le hβ1 hQpos
  rw [hrd.deriv] at hQd
  have hA := ((hasDerivAt_const m (gammaOf N B)).sub (hasDerivAt_id' m)).mul (hasDerivAt_id' m)
  have hBq := hQd.mul hL
  have hDpos := pl_D_pos μ hB hN hpos hΛ
  have hC := hA.div hBq (mul_pos hQpos hΛ).ne'
  have key : deriv (sN β B μ) m = _ := hC.deriv
  rw [key]
  beta_reduce
  simp only [Pi.mul_apply, Pi.sub_apply]
  unfold thetaN Efun sN
  rw [hrd.deriv, hL.deriv]
  have hQ0 : Qm β m ≠ 0 := hQpos.ne'
  have hΛ0 : partLam B μ m ≠ 0 := hΛ.ne'
  have hD0 : (B:ℝ)⁻¹ * ∑ i, μ i / (1 + partLam B μ m * μ i) ^ 2 ≠ 0 := hDpos.ne'
  have hrd0 : rd ≠ 0 := hrdpos.ne'
  have hm0' : m ≠ 0 := hm0.ne'
  field_simp
  ring

private lemma pl_sN_strictAnti {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i) :
    StrictAntiOn (sN β B μ) (Ioo 0 (gammaOf N B)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    (pl_sN_contDiffOn μ hβ0 hβ1 hB hN hpos).continuousOn ?_
  intro x hx
  rw [interior_Ioo] at hx
  rw [pl_sN_deriv_eq μ hβ0 hβ1 hB hN hpos hx]
  have h1 := pl_thetaN_pos μ hβ0 hβ1 hB hN hpos hx
  have h2 := pl_sN_pos μ hβ0 hβ1 hB hN hpos hx
  have h3 : 0 < thetaN β B μ x * sN β B μ x := mul_pos h1 h2
  linarith


private lemma pl_Qm_contDiffAt_pt {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    ContDiffAt ℝ ∞ (Qm β) m := by
  have hQ := (pl_Qm_spec hβ0 hβ1 hm).1
  have h := pl_Qm_contDiffAt hβ0 hβ1 hQ
  rw [(pl_Qm_spec hβ0 hβ1 hm).2] at h
  exact h

private lemma pl_gamma_pos {N B : ℕ} (hB : 0 < B) (hN : 0 < N) : 0 < gammaOf N B := by
  unfold gammaOf
  exact div_pos (by exact_mod_cast hN) (by exact_mod_cast hB)

private lemma pl_sN_large {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i) (K : ℝ) :
    ∀ᶠ m in 𝓝[>] (0:ℝ), K < sN β B μ m := by
  have hγ := pl_gamma_pos hB hN
  have hs2 : 0 < sPow β 2 := by
    rw [sPow_eq hβ0.le hβ1 le_rfl]
    apply div_pos (pow_pos (by linarith) 2)
    nlinarith
  obtain ⟨c, hc⟩ := (lem_app_pl_weights_i_Q hβ0.le hβ1).isBigO.bound
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = |c| / sPow β 2 + 1 := ⟨_, rfl⟩
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hQC : ∀ᶠ m in 𝓝[>] (0:ℝ), Qm β m ≤ C * m := by
    filter_upwards [hc, self_mem_nhdsWithin] with m hm hm0
    have hm0' : 0 < m := hm0
    have hQ := (pl_Qm_spec hβ0 hβ1 hm0').1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hQ,
      abs_of_pos (div_pos hm0' hs2)] at hm
    have h1 : c * (m / sPow β 2) ≤ |c| * (m / sPow β 2) :=
      mul_le_mul_of_nonneg_right (le_abs_self c) (div_pos hm0' hs2).le
    have h2 : |c| * (m / sPow β 2) = |c| / sPow β 2 * m := by ring
    have h3 : |c| / sPow β 2 * m ≤ C * m := by
      rw [hCdef, add_mul, one_mul]
      linarith
    linarith
  obtain ⟨K', hK'def⟩ : ∃ K' : ℝ, K' = |K| + 1 := ⟨_, rfl⟩
  have hK'pos : 0 < K' := by rw [hK'def]; positivity
  have hKK' : K ≤ K' := by rw [hK'def]; linarith [le_abs_self K]
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = gammaOf N B / (2 * C * K') := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hΛsmall : ∀ᶠ m in 𝓝[>] (0:ℝ), partLam B μ m < ε := by
    have hmem : Ioo (0:ℝ) (partMN B μ ε) ∈ 𝓝[>] (0:ℝ) :=
      Ioo_mem_nhdsGT (pl_partMN_mem μ hB hN hpos hε).1
    filter_upwards [hmem] with m hm
    have hmγ : m ∈ Ioo 0 (gammaOf N B) := ⟨hm.1, hm.2.trans (pl_partMN_mem μ hB hN hpos hε).2⟩
    have hΛ := pl_partLam_spec μ hB hN hpos hmγ
    by_contra hcon
    push_neg at hcon
    have h3 := ((pl_partMN_mono μ hB hN hpos).le_iff_le (Set.mem_Ici.2 hε.le)
      (Set.mem_Ici.2 (le_of_lt (Set.mem_Ioi.1 hΛ.2)))).2 hcon
    rw [hΛ.1] at h3
    linarith [hm.2]
  filter_upwards [hQC, hΛsmall, Ioo_mem_nhdsGT (half_pos hγ)] with m hQle hΛε hmh
  have hm0 : 0 < m := hmh.1
  have hmγ2 : m < gammaOf N B / 2 := hmh.2
  have hQ := (pl_Qm_spec hβ0 hβ1 hm0).1
  have hΛ := (pl_partLam_spec μ hB hN hpos ⟨hm0, by linarith⟩).2
  have hΛ' : 0 < partLam B μ m := hΛ
  unfold sN
  rw [lt_div_iff₀ (mul_pos hQ hΛ')]
  have hA : K * (Qm β m * partLam B μ m) ≤ K' * (Qm β m * partLam B μ m) :=
    mul_le_mul_of_nonneg_right hKK' (mul_pos hQ hΛ').le
  have hB' : K' * (Qm β m * partLam B μ m) ≤ K' * (C * m * partLam B μ m) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hQle hΛ'.le) hK'pos.le
  have hC' : K' * (C * m * partLam B μ m) ≤ K' * (C * m * ε) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΛε.le (by positivity)) hK'pos.le
  have hD' : K' * (C * m * ε) = m * gammaOf N B / 2 := by
    rw [hεdef]
    field_simp
  have hE' : m * gammaOf N B / 2 < (gammaOf N B - m) * m := by
    have : 0 < m * (gammaOf N B / 2 - m) := mul_pos hm0 (by linarith)
    nlinarith [this]
  linarith [hA, hB', hC', hD', hE']

private lemma pl_sN_small {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ m in 𝓝[<] (gammaOf N B), sN β B μ m < s := by
  have hγ := pl_gamma_pos hB hN
  have hQγ : 0 < Qm β (gammaOf N B) := (pl_Qm_spec hβ0 hβ1 hγ).1
  have hQc : ContinuousAt (Qm β) (gammaOf N B) := (pl_Qm_contDiffAt_pt hβ0 hβ1 hγ).continuousAt
  obtain ⟨q0, hq0def⟩ : ∃ q0 : ℝ, q0 = Qm β (gammaOf N B) / 2 := ⟨_, rfl⟩
  have hq0 : 0 < q0 := by rw [hq0def]; positivity
  have hQev : ∀ᶠ m in 𝓝 (gammaOf N B), q0 < Qm β m :=
    hQc.tendsto.eventually (lt_mem_nhds (by rw [hq0def]; linarith))
  have hQ' : ∀ᶠ m in 𝓝[<] (gammaOf N B), q0 < Qm β m :=
    eventually_nhdsWithin_of_eventually_nhds hQev
  have h1γ : partMN B μ 1 < gammaOf N B := (pl_partMN_mem μ hB hN hpos one_pos).2
  have hmemA : Ioo (partMN B μ 1) (gammaOf N B) ∈ 𝓝[<] (gammaOf N B) := Ioo_mem_nhdsLT h1γ
  have hgs : 0 < s * q0 / gammaOf N B := by positivity
  have hmemB : Ioo (gammaOf N B - s * q0 / gammaOf N B) (gammaOf N B) ∈ 𝓝[<] (gammaOf N B) :=
    Ioo_mem_nhdsLT (by linarith)
  filter_upwards [hmemA, hmemB, hQ'] with m hmA hmB hQm
  have hm1 : partMN B μ 1 < m := hmA.1
  have hmγ : m < gammaOf N B := hmA.2
  have hm0 : 0 < m := lt_trans (pl_partMN_mem μ hB hN hpos one_pos).1 hm1
  have hΛ := pl_partLam_spec μ hB hN hpos ⟨hm0, hmγ⟩
  have hΛpos : 0 < partLam B μ m := hΛ.2
  have hΛ1 : 1 < partLam B μ m := by
    by_contra hcon
    push_neg at hcon
    have h3 := ((pl_partMN_mono μ hB hN hpos).le_iff_le (Set.mem_Ici.2 (le_of_lt (Set.mem_Ioi.1 hΛ.2)))
      (Set.mem_Ici.2 zero_le_one)).2 hcon
    rw [hΛ.1] at h3
    linarith
  have hQ := (pl_Qm_spec hβ0 hβ1 hm0).1
  unfold sN
  rw [div_lt_iff₀ (mul_pos hQ hΛpos)]
  have hγm : 0 ≤ gammaOf N B - m := by linarith
  have e1 : (gammaOf N B - m) * m ≤ (gammaOf N B - m) * gammaOf N B :=
    mul_le_mul_of_nonneg_left hmγ.le hγm
  have h1 : gammaOf N B - m < s * q0 / gammaOf N B := by linarith [hmB.1]
  have e2 : (gammaOf N B - m) * gammaOf N B < s * q0 := by
    have := mul_lt_mul_of_pos_right h1 hγ
    rwa [div_mul_cancel₀ _ hγ.ne'] at this
  have e3 : q0 ≤ Qm β m * partLam B μ m := by
    have := le_mul_of_one_le_right hQ.le hΛ1.le
    linarith
  have e4 : s * q0 ≤ s * (Qm β m * partLam B μ m) := mul_le_mul_of_nonneg_left e3 hs.le
  linarith

/-! ## The branch in participation coordinates (`prop:app-pl-branch`) -/

/-- `prop:app-pl-branch`(i) (snapshot `cr-2026-10-23`). LaTeX, verbatim from `section.tex`
l.135–156. This declaration proves part (i) only. Parts (ii) and (iii) are L-G.12.

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
theorem prop_app_pl_branch_i {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i) :
    ContDiffOn ℝ ∞ (sN β B μ) (Ioo 0 (gammaOf N B)) ∧
      StrictAntiOn (sN β B μ) (Ioo 0 (gammaOf N B)) ∧
      Set.BijOn (sN β B μ) (Ioo 0 (gammaOf N B)) (Ioi 0) ∧
      ∀ m ∈ Ioo 0 (gammaOf N B),
        -(deriv (sN β B μ) m / sN β B μ m) = thetaN β B μ m ∧ 0 < thetaN β B μ m := by
  have hγ := pl_gamma_pos hB hN
  have hbij : Set.BijOn (sN β B μ) (Ioo 0 (gammaOf N B)) (Ioi 0) := by
    refine ⟨fun m hm => pl_sN_pos μ hβ0 hβ1 hB hN hpos hm,
      (pl_sN_strictAnti μ hβ0 hβ1 hB hN hpos).injOn, ?_⟩
    intro s hs
    have hs' : 0 < s := hs
    obtain ⟨a, ha_gt, ha_mem⟩ :=
      ((pl_sN_large μ hβ0 hβ1 hB hN hpos s).and (Ioo_mem_nhdsGT hγ)).exists
    obtain ⟨b, hb_lt, hb_mem⟩ :=
      ((pl_sN_small μ hβ0 hβ1 hB hN hpos hs').and (Ioo_mem_nhdsLT hγ)).exists
    have hab : a < b := by
      by_contra h
      push_neg at h
      have := (pl_sN_strictAnti μ hβ0 hβ1 hB hN hpos).antitoneOn hb_mem ha_mem h
      linarith
    have hcont : ContinuousOn (sN β B μ) (Icc a b) :=
      (pl_sN_contDiffOn μ hβ0 hβ1 hB hN hpos).continuousOn.mono
        (Icc_subset_Ioo ha_mem.1 hb_mem.2)
    have hmem : s ∈ Icc (sN β B μ b) (sN β B μ a) := ⟨hb_lt.le, ha_gt.le⟩
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' hab.le hcont hmem
    exact ⟨x, ⟨lt_of_lt_of_le ha_mem.1 hx.1, lt_of_le_of_lt hx.2 hb_mem.2⟩, hfx⟩
  refine ⟨pl_sN_contDiffOn μ hβ0 hβ1 hB hN hpos, pl_sN_strictAnti μ hβ0 hβ1 hB hN hpos,
    hbij, fun m hm => ⟨?_, pl_thetaN_pos μ hβ0 hβ1 hB hN hpos hm⟩⟩
  rw [pl_sN_deriv_eq μ hβ0 hβ1 hB hN hpos hm]
  have hs := (pl_sN_pos μ hβ0 hβ1 hB hN hpos hm).ne'
  field_simp

/-- Private copy of the bijection part of `prop_app_pl_branch_i` (which needs an unused
`Antitone μ` hypothesis that this target does not have). Fully proved. -/
private lemma pl_sN_bijOn {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i) :
    Set.BijOn (sN β B μ) (Ioo 0 (gammaOf N B)) (Ioi 0) := by
  have hγ := pl_gamma_pos hB hN
  refine ⟨fun m hm => pl_sN_pos μ hβ0 hβ1 hB hN hpos hm,
    (pl_sN_strictAnti μ hβ0 hβ1 hB hN hpos).injOn, ?_⟩
  intro s hs
  have hs' : 0 < s := hs
  obtain ⟨a, ha_gt, ha_mem⟩ :=
    ((pl_sN_large μ hβ0 hβ1 hB hN hpos s).and (Ioo_mem_nhdsGT hγ)).exists
  obtain ⟨b, hb_lt, hb_mem⟩ :=
    ((pl_sN_small μ hβ0 hβ1 hB hN hpos hs').and (Ioo_mem_nhdsLT hγ)).exists
  have hab : a < b := by
    by_contra h
    push_neg at h
    have := (pl_sN_strictAnti μ hβ0 hβ1 hB hN hpos).antitoneOn hb_mem ha_mem h
    linarith
  have hcont : ContinuousOn (sN β B μ) (Icc a b) :=
    (pl_sN_contDiffOn μ hβ0 hβ1 hB hN hpos).continuousOn.mono
      (Icc_subset_Ioo ha_mem.1 hb_mem.2)
  have hmem : s ∈ Icc (sN β B μ b) (sN β B μ a) := ⟨hb_lt.le, ha_gt.le⟩
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' hab.le hcont hmem
  exact ⟨x, ⟨lt_of_lt_of_le ha_mem.1 hx.1, lt_of_le_of_lt hx.2 hb_mem.2⟩, hfx⟩

/-! ## Drift in the participation coordinate (`lem:app-pl-drift-participation`) -/

/-- `lem:app-pl-drift-participation` (snapshot `cr-2026-10-23`). LaTeX, verbatim from
`section.tex` l.1373–1382. This declaration is the first identity, which holds for every
finite positive spectrum. The bulk display `eqn:app-pl-Bi-bulk` is deferred to L-G.3, since
it needs `assum:app-pl-regime`.

\begin{lemma}[Drift in the participation coordinate]\label{lem:app-pl-drift-participation}
For every finite positive spectrum,
\begin{equation}\label{eqn:app-pl-drift-m}
\sqrt2\,\mathfrak d_i(0)=\frac1{\pi\gamma}\int_0^\gamma\mathcal A(m)\,\mathcal B_i(m)\,E(m)\vartheta_N(m)\,\dif m .
\end{equation}
Under \cref{assum:app-pl-regime}, with $x=i/N$ and $m=\gamma p$,
\begin{equation}\label{eqn:app-pl-Bi-bulk}
\mathcal B_i(\gamma p)=a_N\sqrt{\frac{1-p}{p\,V_N(p)}}\;\frac{V_N(p)}{V_N(p)+x^\alpha}.
\end{equation}
\end{lemma} -/
theorem lem_app_pl_drift_participation_i {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i) (i : Fin N) :
    Real.sqrt 2 * dZero β B μ i =
      1 / (Real.pi * gammaOf N B) * ∫ m in Ioo 0 (gammaOf N B),
        Aav β m * partBfun B μ i m * Efun β m * thetaN β B μ m := by
  have hγ := pl_gamma_pos hB hN
  have hbij := pl_sN_bijOn μ hβ0 hβ1 hB hN hpos
  have hinj := (pl_sN_strictAnti μ hβ0 hβ1 hB hN hpos).injOn
  set g : ℝ → ℝ := fun y => Gfun β B μ i y / (2 * Real.sqrt y) with hg
  -- Step A: substitute y = u^2 on (0,∞)
  have hA : ∫ u in Ioi (0:ℝ), Gfun β B μ i (u ^ 2) = ∫ y in Ioi (0:ℝ), g y := by
    have himg : (fun u : ℝ => u ^ 2) '' Ioi (0:ℝ) = Ioi (0:ℝ) := by
      ext y
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact pow_pos (Set.mem_Ioi.1 hu) 2
      · intro hy
        exact ⟨Real.sqrt y, Real.sqrt_pos.2 hy, Real.sq_sqrt hy.le⟩
    have hderiv : ∀ u ∈ Ioi (0:ℝ), HasDerivWithinAt (fun u : ℝ => u ^ 2) (2 * u) (Ioi (0:ℝ)) u := by
      intro u _
      exact ((hasDerivAt_pow 2 u).congr_deriv (by ring)).hasDerivWithinAt
    have hinj2 : Set.InjOn (fun u : ℝ => u ^ 2) (Ioi (0:ℝ)) := by
      intro a ha b hb hab
      exact (pow_left_inj₀ (Set.mem_Ioi.1 ha).le (Set.mem_Ioi.1 hb).le two_ne_zero).1 hab
    have key := MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      hderiv hinj2 g
    rw [himg] at key
    rw [key]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    have hu' : 0 < u := Set.mem_Ioi.1 hu
    simp only [hg, smul_eq_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * u), Real.sqrt_sq hu'.le]
    field_simp
  -- Step B: substitute y = s_N(m) on (0,γ)
  have hB2 : ∫ y in Ioi (0:ℝ), g y =
      ∫ m in Ioo 0 (gammaOf N B), |deriv (sN β B μ) m| • g (sN β B μ m) := by
    have hdiff : ∀ m ∈ Ioo 0 (gammaOf N B),
        HasDerivWithinAt (sN β B μ) (deriv (sN β B μ) m) (Ioo 0 (gammaOf N B)) m := by
      intro m hm
      have hca := (pl_sN_contDiffOn μ hβ0 hβ1 hB hN hpos).contDiffAt
        (Ioo_mem_nhds hm.1 hm.2)
      exact (hca.differentiableAt (by simp)).hasDerivAt.hasDerivWithinAt
    have key := MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      hdiff hinj g
    rw [hbij.image_eq] at key
    exact key
  -- Step C: pointwise identity
  have hC : ∀ m ∈ Ioo 0 (gammaOf N B), |deriv (sN β B μ) m| • g (sN β B μ m) =
      1 / 2 * (Aav β m * partBfun B μ i m * Efun β m * thetaN β B μ m) := by
    intro m hm
    obtain ⟨hm0, hmg⟩ := hm
    have hm' : m ∈ Ioo 0 (gammaOf N B) := ⟨hm0, hmg⟩
    have hs : 0 < sN β B μ m := pl_sN_pos μ hβ0 hβ1 hB hN hpos hm'
    have hθ : 0 < thetaN β B μ m := pl_thetaN_pos μ hβ0 hβ1 hB hN hpos hm'
    have hd := pl_sN_deriv_eq μ hβ0 hβ1 hB hN hpos hm'
    have hmOf : mOf β B μ (sN β B μ m) = m :=
      hinj (Function.invFunOn_mem ⟨m, hm', rfl⟩) hm' (Function.invFunOn_eq ⟨m, hm', rfl⟩)
    obtain ⟨hQ, hr⟩ := pl_Qm_spec hβ0 hβ1 hm0
    have hE := pl_Efun_pos hβ0 hβ1 hm0
    have hΛ : 0 < partLam B μ m := (pl_partLam_spec μ hB hN hpos hm').2
    have hX : 0 < (gammaOf N B - m) / (m * partLam B μ m) :=
      div_pos (sub_pos.2 hmg) (mul_pos hm0 hΛ)
    have hr' : Qm β m * Fw (emaW β) (Qm β m) = m := hr
    have hFw : Fw (emaW β) (Qm β m) = m / Qm β m :=
      eq_div_of_mul_eq hQ.ne' (by rw [mul_comm]; exact hr')
    have hsq1 := Real.mul_self_sqrt hs.le
    have hsq2 := Real.mul_self_sqrt hQ.le
    have hSpos := Real.sqrt_pos.2 hs
    have key : Real.sqrt (sN β B μ m) * Real.sqrt (Qm β m) =
        m * Real.sqrt ((gammaOf N B - m) / (m * partLam B μ m)) := by
      rw [← Real.sqrt_mul hs.le, show m * Real.sqrt ((gammaOf N B - m) / (m * partLam B μ m)) =
        Real.sqrt (m ^ 2 * ((gammaOf N B - m) / (m * partLam B μ m))) by
          rw [Real.sqrt_mul (sq_nonneg m), Real.sqrt_sq hm0.le]]
      congr 1
      have hQ0 : Qm β m ≠ 0 := hQ.ne'
      have hΛ0 : partLam B μ m ≠ 0 := hΛ.ne'
      have hm0' : m ≠ 0 := hm0.ne'
      unfold sN
      field_simp
    have hE0 : Efun β m ≠ 0 := hE.ne'
    rw [hd, neg_mul, abs_neg, abs_of_pos (mul_pos hθ hs)]
    simp only [hg, smul_eq_mul]
    unfold Gfun
    rw [hmOf, hFw]
    unfold Aav partBfun
    generalize hS : Real.sqrt (sN β B μ m) = S at hsq1 key hSpos ⊢
    rw [← hsq1]
    have hST : S * Qm β m = m * Real.sqrt (Qm β m) * Real.sqrt ((gammaOf N B - m) / (m * partLam B μ m)) := by
      linear_combination (-S) * hsq2 + Real.sqrt (Qm β m) * key
    have hQ0 : Qm β m ≠ 0 := hQ.ne'
    have hm0' : m ≠ 0 := hm0.ne'
    field_simp
    linear_combination (Lw (emaW β) (Qm β m) * partF B μ i m) * hST
  -- Assemble
  have hI : ∫ u in Ioi (0:ℝ), Gfun β B μ i (u ^ 2) =
      1 / 2 * ∫ m in Ioo 0 (gammaOf N B),
        Aav β m * partBfun B μ i m * Efun β m * thetaN β B μ m := by
    rw [hA, hB2, ← MeasureTheory.integral_const_mul (1 / 2 : ℝ)]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
    intro m hm
    exact hC m hm
  unfold dZero
  rw [hI]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpi : Real.pi * gammaOf N B ≠ 0 := mul_ne_zero Real.pi_ne_zero hγ.ne'
  linear_combination (∫ m in Ioo 0 (gammaOf N B),
        Aav β m * partBfun B μ i m * Efun β m * thetaN β B μ m) / (2 * (Real.pi * gammaOf N B)) * h2

/-- Inverse branch facts: for `s > 0`, `m(s) ∈ (0,γ)` and `s_N(m(s)) = s`. -/
private lemma pl_mOf_spec {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i) {s : ℝ} (hs : 0 < s) :
    mOf β B μ s ∈ Ioo 0 (gammaOf N B) ∧ sN β B μ (mOf β B μ s) = s := by
  have hex : ∃ a, a ∈ Ioo 0 (gammaOf N B) ∧ sN β B μ a = s :=
    (pl_sN_bijOn μ hβ0 hβ1 hB hN hpos).surjOn (show s ∈ Ioi 0 from hs)
  unfold mOf
  exact ⟨(Function.invFunOn_pos hex).1, (Function.invFunOn_pos hex).2⟩

/-- `m(s) → γ` as `s ↓ 0`. -/
private lemma pl_mOf_tendsto {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i) :
    Tendsto (mOf β B μ) (𝓝[>] (0:ℝ)) (𝓝 (gammaOf N B)) := by
  have hγ := pl_gamma_pos hB hN
  rw [tendsto_order]
  constructor
  · intro a ha
    rcases le_or_gt a 0 with h0 | h0
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact lt_of_le_of_lt h0 (pl_mOf_spec μ hβ0 hβ1 hB hN hpos hs).1.1
    · have hsa : 0 < sN β B μ a := pl_sN_pos μ hβ0 hβ1 hB hN hpos ⟨h0, ha⟩
      filter_upwards [Ioo_mem_nhdsGT hsa] with s hs
      have hs0 : 0 < s := hs.1
      have hslt : s < sN β B μ a := hs.2
      obtain ⟨hmI, hmS⟩ := pl_mOf_spec μ hβ0 hβ1 hB hN hpos hs0
      by_contra hle
      push_neg at hle
      have h1 : sN β B μ a ≤ sN β B μ (mOf β B μ s) :=
        (pl_sN_strictAnti μ hβ0 hβ1 hB hN hpos).antitoneOn hmI
          ⟨h0, ha⟩ hle
      linarith
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact lt_trans (pl_mOf_spec μ hβ0 hβ1 hB hN hpos hs).1.2 ha

/-- `Q_{m(s)} → Q_γ` as `s ↓ 0` (conjunct (i) of `prop:app-pl-drift-zero`). -/
private lemma pl_Qm_mOf_tendsto {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i) :
    Tendsto (fun s => Qm β (mOf β B μ s)) (𝓝[>] (0:ℝ)) (𝓝 (Qm β (gammaOf N B))) :=
  ((pl_Qm_contDiffAt_pt hβ0 hβ1 (pl_gamma_pos hB hN)).continuousAt.tendsto).comp
    (pl_mOf_tendsto μ hβ0 hβ1 hB hN hpos)

/-! ### Private helpers for `prop_app_pl_drift_zero_i` -/

private lemma pl_emaW_sq_summable {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Summable (fun j : ℕ => emaW β j ^ 2) := by
  have hg : Summable (fun j : ℕ => (β ^ 2) ^ j) :=
    summable_geometric_of_lt_one (sq_nonneg β) (by nlinarith)
  refine (hg.mul_left ((1 - β) ^ 2)).congr (fun j => ?_)
  simp only [emaW]
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j 2]

private lemma pl_Fw_summable {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    Summable (fun j : ℕ => emaW β j ^ 2 * J (emaW β j ^ 2 * q)) := by
  obtain ⟨hJ0, hJ1⟩ : (∀ x, 0 ≤ x → 0 < J x) ∧ (∀ x, 0 ≤ x → J x ≤ 1) :=
    ⟨fun x hx => (lem_app_de_scalar_i.2.2.1 x hx).1, fun x hx => (lem_app_de_scalar_i.2.2.1 x hx).2⟩
  have hw := pl_wseq hβ0 hβ1
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) (pl_emaW_sq_summable hβ0 hβ1)
  · exact mul_nonneg (sq_nonneg _) (hJ0 _ (mul_nonneg (sq_nonneg _) hq)).le
  · exact mul_le_of_le_one_right (sq_nonneg _) (hJ1 _ (mul_nonneg (sq_nonneg _) hq))

/-- `F_β` is antitone on `[0,∞)`. -/
private lemma pl_Fw_anti {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    AntitoneOn (Fw (emaW β)) (Ici 0) := by
  intro a ha b hb hab
  have ha' : (0:ℝ) ≤ a := ha
  have hb' : (0:ℝ) ≤ b := hb
  show ∑' j, emaW β j ^ 2 * J (emaW β j ^ 2 * b) ≤ ∑' j, emaW β j ^ 2 * J (emaW β j ^ 2 * a)
  refine Summable.tsum_le_tsum (fun j => ?_) (pl_Fw_summable hβ0 hβ1 hb') (pl_Fw_summable hβ0 hβ1 ha')
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  exact lem_app_de_scalar_i.2.1.antitoneOn (Set.mem_Ici.2 (mul_nonneg (sq_nonneg _) ha'))
    (Set.mem_Ici.2 (mul_nonneg (sq_nonneg _) hb')) (mul_le_mul_of_nonneg_left hab (sq_nonneg _))

private lemma pl_Fw_pos {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    0 < Fw (emaW β) q :=
  (Fw_admissible (pl_wseq hβ0 hβ1)).pos q hq

private lemma pl_Fw_le_zero {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    Fw (emaW β) q ≤ Fw (emaW β) 0 :=
  (Fw_admissible (pl_wseq hβ0 hβ1)).le_zero q hq

private lemma pl_Fw_contAt {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 < q) :
    ContinuousAt (Fw (emaW β)) q :=
  (lem_app_pl_weights_ii_F hβ0 hβ1 q hq).1.continuousAt

/-- `Fw(Q_m) = m / Q_m`. -/
private lemma pl_Fw_Qm {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    Fw (emaW β) (Qm β m) = m / Qm β m := by
  obtain ⟨hQ, hr⟩ := pl_Qm_spec hβ0 hβ1 hm
  have hr' : Qm β m * Fw (emaW β) (Qm β m) = m := hr
  exact eq_div_of_mul_eq hQ.ne' (by rw [mul_comm]; exact hr')

/-- `Q_m` is monotone in `m`. -/
private lemma pl_Qm_mono {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m m' : ℝ} (hm : 0 < m)
    (hmm : m ≤ m') : Qm β m ≤ Qm β m' := by
  have hm' : 0 < m' := lt_of_lt_of_le hm hmm
  obtain ⟨h1, h2⟩ := pl_Qm_spec hβ0 hβ1 hm
  obtain ⟨h3, h4⟩ := pl_Qm_spec hβ0 hβ1 hm'
  by_contra hcon
  push_neg at hcon
  have := (lem_app_de_scalar_iii (pl_wseq hβ0.le hβ1)).2.1 (Set.mem_Ici.2 h3.le) (Set.mem_Ici.2 h1.le) hcon
  linarith

/-- `s_N`-inverse branch is antitone. -/
private lemma pl_mOf_anti {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') :
    mOf β B μ s' ≤ mOf β B μ s := by
  have hs' : 0 < s' := lt_of_lt_of_le hs hss
  obtain ⟨h1, h2⟩ := pl_mOf_spec μ hβ0 hβ1 hB hN hpos hs
  obtain ⟨h3, h4⟩ := pl_mOf_spec μ hβ0 hβ1 hB hN hpos hs'
  by_contra hcon
  push_neg at hcon
  have := (pl_sN_strictAnti μ hβ0 hβ1 hB hN hpos) h1 h3 hcon
  linarith

private lemma pl_partLam_mono {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) {m m' : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B))
    (hm' : m' ∈ Ioo 0 (gammaOf N B)) (hmm : m ≤ m') : partLam B μ m ≤ partLam B μ m' := by
  obtain ⟨h1, h2⟩ := pl_partLam_spec μ hB hN hpos hm
  obtain ⟨h3, h4⟩ := pl_partLam_spec μ hB hN hpos hm'
  by_contra hcon
  push_neg at hcon
  have := pl_partMN_mono μ hB hN hpos (Set.mem_Ici.2 (le_of_lt h4)) (Set.mem_Ici.2 (le_of_lt h2)) hcon
  linarith

/-- `s Λ(m(s)) = (γ - m(s)) F_β(Q_{m(s)})` (from `eqn:app-pl-sm`). -/
private lemma pl_s_Lam {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i) {s : ℝ} (hs : 0 < s) :
    s * partLam B μ (mOf β B μ s) =
      (gammaOf N B - mOf β B μ s) * Fw (emaW β) (Qm β (mOf β B μ s)) := by
  obtain ⟨hm, hS⟩ := pl_mOf_spec μ hβ0 hβ1 hB hN hpos hs
  set m := mOf β B μ s
  have hQ : 0 < Qm β m := (pl_Qm_spec hβ0 hβ1 hm.1).1
  have hΛ : 0 < partLam B μ m := (pl_partLam_spec μ hB hN hpos hm).2
  rw [pl_Fw_Qm hβ0 hβ1 hm.1]
  conv_lhs => rw [← hS]
  unfold sN
  field_simp

/-- `(γ - m_N(Λ)) Λ = B⁻¹ ∑ Λ/(1+Λ μ_i)`. -/
private lemma pl_gamma_sub_partMN {N B : ℕ} (μ : Fin N → ℝ) (hpos : ∀ i, 0 < μ i) {Λ : ℝ}
    (hΛ : 0 < Λ) :
    (gammaOf N B - partMN B μ Λ) = (B:ℝ)⁻¹ * ∑ i, 1 / (1 + Λ * μ i) := by
  unfold partMN
  rw [← pl_gamma_eq]
  have hN' : (N:ℝ) = ∑ _i : Fin N, (1:ℝ) := by simp
  rw [hN', ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h : 0 < 1 + Λ * μ i := by have := mul_pos hΛ (hpos i); linarith
  field_simp
  ring

private lemma pl_Lam_tendsto {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i) :
    Tendsto (fun s => partLam B μ (mOf β B μ s)) (𝓝[>] (0:ℝ)) atTop := by
  rw [tendsto_atTop]
  intro b
  set L := max b 1 with hL
  have hL0 : 0 < L := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hlt : partMN B μ L < gammaOf N B := (pl_partMN_mem μ hB hN hpos hL0).2
  filter_upwards [(pl_mOf_tendsto μ hβ0 hβ1 hB hN hpos).eventually (lt_mem_nhds hlt),
    self_mem_nhdsWithin] with s hs hs0
  obtain ⟨hm, _⟩ := pl_mOf_spec μ hβ0 hβ1 hB hN hpos hs0
  obtain ⟨h1, h2⟩ := pl_partLam_spec μ hB hN hpos hm
  have : L ≤ partLam B μ (mOf β B μ s) := by
    by_contra hcon
    push_neg at hcon
    have := pl_partMN_mono μ hB hN hpos (Set.mem_Ici.2 (le_of_lt h2)) (Set.mem_Ici.2 hL0.le) hcon
    linarith
  exact le_trans (le_max_left _ _) this


/-! ### Private helpers for `prop_app_pl_drift_zero_ii_*`: the ratio `R = L_β/F_β` -/

private lemma pl_Lw_nonneg {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ Lw (emaW β) q := by
  have hw := pl_wseq hβ0 hβ1
  refine tsum_nonneg (fun j => mul_nonneg (hw.1 j) ?_)
  exact (lem_app_de_scalar_i.2.2.1 _ (mul_nonneg (sq_nonneg _) hq)).1.le

/-- Bounds on `R = L_β/F_β` on the compact `[0,1]`: continuity and boundedness. -/
private lemma pl_R_small {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ q ∈ Icc (0:ℝ) 1, Lw (emaW β) q / Fw (emaW β) q ≤ M) ∧
      ∀ q ∈ Ioc (0:ℝ) 1, |deriv (fun x => Lw (emaW β) x / Fw (emaW β) x) q| ≤ M := by
  have hw := pl_wseq hβ0 hβ1
  obtain ⟨_, _, hFc, hLc, hFd, hLd, _⟩ := lem_app_de_scalar_ii hw
  have hFpos : ∀ q ∈ Icc (0:ℝ) 1, Fw (emaW β) q ≠ 0 := fun q hq => (pl_Fw_pos hβ0 hβ1 hq.1).ne'
  have hdF : ContinuousOn (derivWithin (Fw (emaW β)) (Ici 0)) (Ici 0) :=
    hFd.continuousOn_derivWithin (uniqueDiffOn_Ici 0) (by simp)
  have hdL : ContinuousOn (derivWithin (Lw (emaW β)) (Ici 0)) (Ici 0) :=
    hLd.continuousOn_derivWithin (uniqueDiffOn_Ici 0) (by simp)
  set Rd : ℝ → ℝ := fun q => (derivWithin (Lw (emaW β)) (Ici 0) q * Fw (emaW β) q -
    Lw (emaW β) q * derivWithin (Fw (emaW β)) (Ici 0) q) / Fw (emaW β) q ^ 2 with hRd
  have hsub : Icc (0:ℝ) 1 ⊆ Ici 0 := Icc_subset_Ici_self
  have hcR : ContinuousOn (fun q => Lw (emaW β) q / Fw (emaW β) q) (Icc 0 1) :=
    (hLc.mono hsub).div (hFc.mono hsub) hFpos
  have hcRd : ContinuousOn Rd (Icc 0 1) := by
    refine (((hdL.mono hsub).mul (hFc.mono hsub)).sub ((hLc.mono hsub).mul (hdF.mono hsub))).div
      ((hFc.mono hsub).pow 2) (fun q hq => pow_ne_zero 2 (hFpos q hq))
  obtain ⟨M1, hM1⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn hcR
  obtain ⟨M2, hM2⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn hcRd
  refine ⟨max (max M1 M2) 0, le_max_right _ _, fun q hq => ?_, fun q hq => ?_⟩
  · exact le_trans (le_trans (le_abs_self _) (hM1 q hq)) (le_trans (le_max_left _ _) (le_max_left _ _))
  · have hq0 : 0 < q := hq.1
    have hqm : Ici (0:ℝ) ∈ 𝓝 q := Ici_mem_nhds hq0
    have hFq := (lem_app_pl_weights_ii_F hβ0 hβ1 q hq0).1
    have hLq := (lem_app_pl_weights_ii_L hβ0 hβ1 q hq0).1
    have hder : deriv (fun x => Lw (emaW β) x / Fw (emaW β) x) q = Rd q := by
      have h2 : deriv (fun x => Lw (emaW β) x / Fw (emaW β) x) q = _ :=
        (hLq.hasDerivAt.div hFq.hasDerivAt (pl_Fw_pos hβ0 hβ1 hq0.le).ne').deriv
      rw [h2]
      simp only [hRd]
      rw [derivWithin_of_mem_nhds hqm, derivWithin_of_mem_nhds hqm]
    rw [hder]
    exact le_trans (le_trans (le_abs_self _) (by simpa using hM2 q (Ioc_subset_Icc_self hq)))
      (le_trans (le_max_right _ _) (le_max_left _ _))

/-- `R(q) ≤ C₂ √q` for `q ≥ 1`. -/
private lemma pl_R_large {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ, 1 ≤ q → Lw (emaW β) q / Fw (emaW β) q ≤ C * Real.sqrt q := by
  obtain ⟨c, C, hc, hcC, h⟩ := lem_app_pl_weights_iii hβ0 hβ1
  have hr1 : 0 < rW (emaW β) 1 := by
    have := lem_app_de_scalar_iii (pl_wseq hβ0.le hβ1)
    have h2 := this.2.1 (Set.mem_Ici.2 (le_refl (0:ℝ))) (Set.mem_Ici.2 zero_le_one) one_pos
    rwa [this.2.2.1] at h2
  refine ⟨C / rW (emaW β) 1, div_nonneg (hc.le.trans hcC) hr1.le, fun q hq => ?_⟩
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hrmono : rW (emaW β) 1 ≤ rW (emaW β) q :=
    (lem_app_de_scalar_iii (pl_wseq hβ0.le hβ1)).2.1.monotoneOn (Set.mem_Ici.2 zero_le_one)
      (Set.mem_Ici.2 hq0.le) hq
  have hFp := pl_Fw_pos hβ0.le hβ1 hq0.le
  have hL := (h q hq).2.2.1
  have hLn := pl_Lw_nonneg hβ0.le hβ1 hq0.le
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
  have hrW : rW (emaW β) q = q * Fw (emaW β) q := rfl
  have key : Lw (emaW β) q / Fw (emaW β) q = (Real.sqrt q * Lw (emaW β) q) * Real.sqrt q /
      rW (emaW β) q := by
    rw [hrW]
    have := Real.mul_self_sqrt hq0.le
    field_simp
    nlinarith [this]
  rw [key]
  have hrq : 0 < rW (emaW β) q := lt_of_lt_of_le hr1 hrmono
  rw [div_le_iff₀ hrq]
  calc Real.sqrt q * Lw (emaW β) q * Real.sqrt q
      ≤ C * Real.sqrt q := mul_le_mul_of_nonneg_right hL hsq.le
    _ = C / rW (emaW β) 1 * Real.sqrt q * rW (emaW β) 1 := by field_simp
    _ ≤ C / rW (emaW β) 1 * Real.sqrt q * rW (emaW β) q :=
        mul_le_mul_of_nonneg_left hrmono (mul_nonneg (div_nonneg (hc.le.trans hcC) hr1.le) hsq.le)

private lemma pl_R_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ q : ℝ, 0 < q →
      0 ≤ Lw (emaW β) q / Fw (emaW β) q ∧ Lw (emaW β) q / Fw (emaW β) q ≤ C0 * (1 + Real.sqrt q) := by
  obtain ⟨M, hM0, hM, _⟩ := pl_R_small hβ0.le hβ1
  obtain ⟨C, hC0, hC⟩ := pl_R_large hβ0 hβ1
  refine ⟨max M C, le_trans hM0 (le_max_left _ _), fun q hq => ⟨?_, ?_⟩⟩
  · exact div_nonneg (pl_Lw_nonneg hβ0.le hβ1 hq.le) (pl_Fw_pos hβ0.le hβ1 hq.le).le
  · have hsq := Real.sqrt_nonneg q
    rcases le_total q 1 with h | h
    · calc _ ≤ M := hM q ⟨hq.le, h⟩
        _ ≤ max M C * 1 := by rw [mul_one]; exact le_max_left _ _
        _ ≤ max M C * (1 + Real.sqrt q) := mul_le_mul_of_nonneg_left (by linarith) (le_trans hM0 (le_max_left _ _))
    · calc _ ≤ C * Real.sqrt q := hC q h
        _ ≤ max M C * Real.sqrt q := mul_le_mul_of_nonneg_right (le_max_right _ _) hsq
        _ ≤ max M C * (1 + Real.sqrt q) := mul_le_mul_of_nonneg_left (by linarith) (le_trans hM0 (le_max_left _ _))

/-- `|R'(q)| ≤ C₁/√q`. -/
private lemma pl_R_deriv {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ q : ℝ, 0 < q →
      DifferentiableAt ℝ (fun x => Lw (emaW β) x / Fw (emaW β) x) q ∧
      |deriv (fun x => Lw (emaW β) x / Fw (emaW β) x) q| ≤ C1 / Real.sqrt q := by
  obtain ⟨M, hM0, _, hM⟩ := pl_R_small hβ0.le hβ1
  obtain ⟨C, hC0, hC⟩ := pl_R_large hβ0 hβ1
  refine ⟨max M (2 * C), le_trans hM0 (le_max_left _ _), fun q hq => ⟨?_, ?_⟩⟩
  · exact ((lem_app_pl_weights_ii_L hβ0.le hβ1 q hq).1).div
      ((lem_app_pl_weights_ii_F hβ0.le hβ1 q hq).1) (pl_Fw_pos hβ0.le hβ1 hq.le).ne'
  · have hsq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
    rcases le_total q 1 with h | h
    · calc _ ≤ M := hM q ⟨hq, h⟩
        _ ≤ max M (2 * C) := le_max_left _ _
        _ ≤ _ := le_div_self (le_trans hM0 (le_max_left _ _)) hsq
            (by rw [Real.sqrt_le_one]; exact h)
    · have hFq := (lem_app_pl_weights_ii_F hβ0.le hβ1 q hq).1
      have hLq := (lem_app_pl_weights_ii_L hβ0.le hβ1 q hq).1
      have hb := pl_Fw_pos hβ0.le hβ1 hq.le
      have ha := pl_Lw_nonneg hβ0.le hβ1 hq.le
      have hbF := (lem_app_pl_weights_ii_F hβ0.le hβ1 q hq).2
      have hbL := (lem_app_pl_weights_ii_L hβ0.le hβ1 q hq).2
      set a := Lw (emaW β) q
      set b := Fw (emaW β) q
      set a' := deriv (Lw (emaW β)) q
      set b' := deriv (Fw (emaW β)) q
      have hder : deriv (fun x => Lw (emaW β) x / Fw (emaW β) x) q = (a' * b - a * b') / b ^ 2 := by
        have h2 : deriv (fun x => Lw (emaW β) x / Fw (emaW β) x) q = _ :=
          (hLq.hasDerivAt.div hFq.hasDerivAt hb.ne').deriv
        rw [h2]
      rw [hder, abs_div, abs_of_pos (pow_pos hb 2)]
      rw [abs_mul, abs_of_pos hq] at hbF hbL
      have hnum : q * |a' * b - a * b'| ≤ 2 * (a * b) := by
        calc q * |a' * b - a * b'| ≤ q * (|a' * b| + |a * b'|) :=
              mul_le_mul_of_nonneg_left (abs_sub _ _) hq.le
          _ = (q * |a'|) * b + a * (q * |b'|) := by
              rw [abs_mul, abs_mul, abs_of_pos hb, abs_of_nonneg ha]; ring
          _ ≤ a * b + a * b := by
              refine add_le_add (mul_le_mul_of_nonneg_right hbL hb.le)
                (mul_le_mul_of_nonneg_left hbF ha)
          _ = 2 * (a * b) := by ring
      have hR := hC q h
      have hsqq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq.le
      rw [div_le_div_iff₀ (pow_pos hb 2) hsq]
      have h1 : |a' * b - a * b'| * Real.sqrt q ≤ 2 * C * b ^ 2 := by
        have hb2 : 0 < b ^ 2 := pow_pos hb 2
        have hab : a ≤ C * Real.sqrt q * b := by
          rwa [div_le_iff₀ hb] at hR
        have : q * |a' * b - a * b'| * Real.sqrt q ≤ 2 * C * Real.sqrt q * b ^ 2 * Real.sqrt q := by
          calc q * |a' * b - a * b'| * Real.sqrt q ≤ 2 * (a * b) * Real.sqrt q :=
                mul_le_mul_of_nonneg_right hnum hsq.le
            _ ≤ 2 * (C * Real.sqrt q * b * b) * Real.sqrt q := by
                have := mul_le_mul_of_nonneg_right hab hb.le
                gcongr
            _ = _ := by ring
        have hqq : 0 < q * Real.sqrt q := mul_pos hq hsq
        nlinarith [this, hsqq, hsq, abs_nonneg (a' * b - a * b')]
      calc |a' * b - a * b'| * Real.sqrt q ≤ 2 * C * b ^ 2 := h1
        _ ≤ max M (2 * C) * b ^ 2 := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_pos hb 2).le

/-- Lipschitz-in-`√q` bound for `R = L_β/F_β`. -/
private lemma pl_R_lip {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ q q' : ℝ, 0 < q' → q' ≤ q →
      |Lw (emaW β) q / Fw (emaW β) q - Lw (emaW β) q' / Fw (emaW β) q'| ≤
        2 * C1 * (Real.sqrt q - Real.sqrt q') := by
  obtain ⟨C1, hC1, hR⟩ := pl_R_deriv hβ0 hβ1
  refine ⟨C1, hC1, fun q q' hq' hqq => ?_⟩
  set R : ℝ → ℝ := fun x => Lw (emaW β) x / Fw (emaW β) x with hRdef
  have hcont : ContinuousOn R (Ioi 0) := fun x hx => (hR x hx).1.continuousAt.continuousWithinAt
  have hsqrt : ∀ x : ℝ, 0 < x → HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x :=
    fun x hx => Real.hasDerivAt_sqrt hx.ne'
  have hcs : ContinuousOn Real.sqrt (Ioi 0) := Real.continuous_sqrt.continuousOn
  have hdiffs : ∀ x ∈ interior (Ioi (0:ℝ)), DifferentiableAt ℝ Real.sqrt x := by
    intro x hx; rw [interior_Ioi] at hx; exact (hsqrt x hx).differentiableAt
  have hq : 0 < q := lt_of_lt_of_le hq' hqq
  have hderiv : ∀ x : ℝ, 0 < x → |deriv R x| ≤ C1 / Real.sqrt x := fun x hx => (hR x hx).2
  have key : ∀ x ∈ interior (Ioi (0:ℝ)), 0 ≤ deriv (fun x => 2 * C1 * Real.sqrt x - R x) x ∧
      0 ≤ deriv (fun x => 2 * C1 * Real.sqrt x + R x) x := by
    intro x hx
    rw [interior_Ioi] at hx
    have hx0 : 0 < x := hx
    have h1 : HasDerivAt (fun x => 2 * C1 * Real.sqrt x) (2 * C1 * (1 / (2 * Real.sqrt x))) x :=
      (hsqrt x hx0).const_mul _
    have h2 : HasDerivAt R (deriv R x) x := (hR x hx0).1.hasDerivAt
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    have hb := hderiv x hx0
    have hv : 2 * C1 * (1 / (2 * Real.sqrt x)) = C1 / Real.sqrt x := by field_simp
    rw [hv] at h1
    have e1 : deriv (fun x => 2 * C1 * Real.sqrt x - R x) x = C1 / Real.sqrt x - deriv R x :=
      (h1.sub h2).deriv
    have e2 : deriv (fun x => 2 * C1 * Real.sqrt x + R x) x = C1 / Real.sqrt x + deriv R x :=
      (h1.add h2).deriv
    rw [e1, e2]
    constructor <;> linarith [abs_le.1 hb]
  have hm1 : MonotoneOn (fun x => 2 * C1 * Real.sqrt x - R x) (Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ((continuousOn_const.mul hcs).sub hcont) ?_
      (fun x hx => (key x hx).1)
    intro x hx; rw [interior_Ioi] at hx
    exact (((hsqrt x hx).const_mul _).differentiableAt).sub (hR x hx).1 |>.differentiableWithinAt |> fun h => h
  have hm2 : MonotoneOn (fun x => 2 * C1 * Real.sqrt x + R x) (Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ((continuousOn_const.mul hcs).add hcont) ?_
      (fun x hx => (key x hx).2)
    intro x hx; rw [interior_Ioi] at hx
    exact (((hsqrt x hx).const_mul _).differentiableAt).add (hR x hx).1 |>.differentiableWithinAt |> fun h => h
  have a1 := hm1 (Set.mem_Ioi.2 hq') (Set.mem_Ioi.2 hq) hqq
  have a2 := hm2 (Set.mem_Ioi.2 hq') (Set.mem_Ioi.2 hq) hqq
  simp only at a1 a2
  rw [abs_le]
  constructor <;> linarith

/-- Antitone shift estimate: for an antitone `φ` with values in `[0,Φ]` and a function `D`
dominated by `φ(u²) - φ(ϱ+u²)`, `∫_0^∞ |D| ≤ Φ √ϱ`. -/
private lemma pl_shift_bound {φ : ℝ → ℝ} {Φ ϱ : ℝ} (hϱ : 0 < ϱ)
    (hanti : AntitoneOn φ (Ioi 0)) (h0 : ∀ s, 0 < s → 0 ≤ φ s) (hΦ : ∀ s, 0 < s → φ s ≤ Φ)
    {D : ℝ → ℝ} (hD : IntegrableOn D (Ioi 0))
    (hDle : ∀ u, 0 < u → |D u| ≤ φ (u ^ 2) - φ (ϱ + u ^ 2)) :
    ∫ u in Ioi (0:ℝ), |D u| ≤ Φ * Real.sqrt ϱ := by
  set δ := Real.sqrt ϱ with hδ
  have hδ0 : 0 < δ := Real.sqrt_pos.2 hϱ
  have hδsq : δ ^ 2 = ϱ := Real.sq_sqrt hϱ.le
  set ψ : ℝ → ℝ := fun v => φ (v ^ 2) with hψ
  have hψanti : AntitoneOn ψ (Ioi 0) := by
    intro a ha b hb hab
    exact hanti (Set.mem_Ioi.2 (pow_pos ha 2)) (Set.mem_Ioi.2 (pow_pos hb 2))
      (pow_le_pow_left₀ (le_of_lt ha) hab 2)
  have hψ0 : ∀ v, 0 < v → 0 ≤ ψ v := fun v hv => h0 _ (pow_pos hv 2)
  have hψΦ : ∀ v, 0 < v → ψ v ≤ Φ := fun v hv => hΦ _ (pow_pos hv 2)
  have hψint : ∀ a, 0 < a → IntegrableOn ψ (Ioc 0 a) := by
    intro a ha
    refine ⟨(aemeasurable_restrict_of_antitoneOn measurableSet_Ioc
        (hψanti.mono Ioc_subset_Ioi_self)).aestronglyMeasurable, ?_⟩
    refine HasFiniteIntegral.restrict_of_bounded (C := |Φ|) (by simp) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun v hv => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hψ0 v hv.1)]
    exact (hψΦ v hv.1).trans (le_abs_self _)
  have hpt : ∀ u, 0 < u → |D u| ≤ ψ u - ψ (u + δ) := by
    intro u hu
    refine (hDle u hu).trans ?_
    have : ψ (u + δ) ≤ φ (ϱ + u ^ 2) := by
      refine hanti (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity)) ?_
      nlinarith [mul_pos hu hδ0]
    show φ (u ^ 2) - φ (ϱ + u ^ 2) ≤ φ (u ^ 2) - ψ (u + δ)
    linarith
  have hT : ∀ T, δ ≤ T → ∫ u in (0:ℝ)..T, |D u| ≤ Φ * δ := by
    intro T hTδ
    have hT0 : 0 < T := lt_of_lt_of_le hδ0 hTδ
    have hDa : IntegrableOn (fun u => |D u|) (Ioc 0 T) := IntegrableOn.mono_set (show IntegrableOn (fun u => |D u|) (Ioi 0) volume from hD.abs) Ioc_subset_Ioi_self
    have hi : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T + δ → IntervalIntegrable ψ volume a b := by
      intro a b ha hab hb
      have := (hψint (T + δ) (by positivity)).mono_set (Ioc_subset_Ioc ha hb)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 this
    have hshift : IntervalIntegrable (fun u => ψ (u + δ)) volume 0 T := by
      have := (hi δ (T + δ) hδ0.le (by linarith) le_rfl).comp_add_right δ
      simpa using this
    have hE : IntervalIntegrable (fun u => ψ u - ψ (u + δ)) volume 0 T :=
      (hi 0 T le_rfl hT0.le (by linarith)).sub hshift
    have h1 : ∫ u in (0:ℝ)..T, |D u| ≤ ∫ u in (0:ℝ)..T, (ψ u - ψ (u + δ)) := by
      rw [intervalIntegral.integral_of_le hT0.le, intervalIntegral.integral_of_le hT0.le]
      exact setIntegral_mono_on hDa ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT0.le).1 hE)
        measurableSet_Ioc (fun u hu => hpt u hu.1)
    have h2 : ∫ u in (0:ℝ)..T, (ψ u - ψ (u + δ)) =
        (∫ u in (0:ℝ)..δ, ψ u) - ∫ u in T..(T + δ), ψ u := by
      have e1 := intervalIntegral.integral_sub (hi 0 T le_rfl hT0.le (by linarith)) hshift
      have e2 := intervalIntegral.integral_comp_add_right (fun x => ψ x) (a := 0) (b := T) δ
      have eA := intervalIntegral.integral_add_adjacent_intervals
        (hi 0 δ le_rfl hδ0.le (by linarith)) (hi δ T hδ0.le hTδ (by linarith))
      have eB := intervalIntegral.integral_add_adjacent_intervals
        (hi δ T hδ0.le hTδ (by linarith)) (hi T (T + δ) hT0.le (by linarith) le_rfl)
      rw [zero_add] at e2
      linarith
    have h3 : 0 ≤ ∫ u in T..(T + δ), ψ u :=
      intervalIntegral.integral_nonneg (by linarith) (fun x hx => hψ0 x (lt_of_lt_of_le hT0 hx.1))
    have h4 : ∫ u in (0:ℝ)..δ, ψ u ≤ Φ * δ := by
      rw [intervalIntegral.integral_of_le hδ0.le]
      have := setIntegral_mono_on ((hψint δ hδ0)) (integrableOn_const (μ := volume) (s := Ioc (0:ℝ) δ)
        (C := Φ) (by simp)) measurableSet_Ioc (fun u hu => hψΦ u hu.1)
      refine this.trans ?_
      rw [setIntegral_const]
      simp [Real.volume_real_Ioc_of_le hδ0.le, mul_comm]
    linarith
  have hDa' : IntegrableOn (fun u => |D u|) (Ioi 0) volume := hD.abs
  have ht := intervalIntegral_tendsto_integral_Ioi (0:ℝ) hDa' (tendsto_id : Tendsto (fun n : ℝ => n) atTop atTop)
  exact le_of_tendsto ht ((eventually_ge_atTop δ).mono (fun T hT' => hT T hT'))


/-! ### Private helpers: monotonicity and majorant of `𝒢_i` -/

private lemma pl_q_facts {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i) {s : ℝ} (hs : 0 < s) :
    0 < Qm β (mOf β B μ s) ∧ Qm β (mOf β B μ s) ≤ Qm β (gammaOf N B) := by
  obtain ⟨hm, _⟩ := pl_mOf_spec μ hβ0 hβ1 hB hN hpos hs
  exact ⟨(pl_Qm_spec hβ0 hβ1 hm.1).1, pl_Qm_mono hβ0 hβ1 hm.1 hm.2.le⟩

private lemma pl_q_anti {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') :
    Qm β (mOf β B μ s') ≤ Qm β (mOf β B μ s) := by
  obtain ⟨hm', _⟩ := pl_mOf_spec μ hβ0 hβ1 hB hN hpos (lt_of_lt_of_le hs hss)
  exact pl_Qm_mono hβ0 hβ1 hm'.1 (pl_mOf_anti μ hβ0 hβ1 hB hN hpos hs hss)

private lemma pl_f_facts {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i) (i : Fin N) {s : ℝ} (hs : 0 < s) :
    0 < partF B μ i (mOf β B μ s) ∧ partF B μ i (mOf β B μ s) < 1 ∧
      partF B μ i (mOf β B μ s) ≤ partLam B μ (mOf β B μ s) * μ i := by
  obtain ⟨hm, _⟩ := pl_mOf_spec μ hβ0 hβ1 hB hN hpos hs
  have hΛ : 0 < partLam B μ (mOf β B μ s) := (pl_partLam_spec μ hB hN hpos hm).2
  obtain ⟨h1, h2⟩ := pl_term_lt_one hΛ (hpos i)
  refine ⟨h1, h2, ?_⟩
  have hx : 0 < partLam B μ (mOf β B μ s) * μ i := mul_pos hΛ (hpos i)
  unfold partF
  exact div_le_self hx.le (by linarith)

private lemma pl_f_anti {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i) (i : Fin N) {s s' : ℝ} (hs : 0 < s)
    (hss : s ≤ s') :
    partF B μ i (mOf β B μ s') ≤ partF B μ i (mOf β B μ s) := by
  obtain ⟨hm, _⟩ := pl_mOf_spec μ hβ0 hβ1 hB hN hpos hs
  obtain ⟨hm', _⟩ := pl_mOf_spec μ hβ0 hβ1 hB hN hpos (lt_of_lt_of_le hs hss)
  have hΛ := pl_partLam_mono μ hB hN hpos hm' hm (pl_mOf_anti μ hβ0 hβ1 hB hN hpos hs hss)
  have hΛ' : 0 < partLam B μ (mOf β B μ s') := (pl_partLam_spec μ hB hN hpos hm').2
  exact (pl_term_mono (hpos i)).monotoneOn (Set.mem_Ici.2 hΛ'.le)
    (Set.mem_Ici.2 (hΛ'.le.trans hΛ)) hΛ

/-- Majorant: `|𝒢_i(s)| ≤ K c/(c+s)`. -/
private lemma pl_G_major {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i) (i : Fin N) :
    ∃ K c : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ s : ℝ, 0 < s → |Gfun β B μ i s| ≤ K * (c / (c + s)) := by
  obtain ⟨C0, hC0, hR⟩ := pl_R_bound hβ0 hβ1
  have hγ := pl_gamma_pos hB hN
  have hF0 : 0 < Fw (emaW β) 0 := pl_Fw_pos hβ0.le hβ1 le_rfl
  set c := gammaOf N B * Fw (emaW β) 0 * μ i with hc
  have hcpos : 0 < c := mul_pos (mul_pos hγ hF0) (hpos i)
  set K := 2 * (C0 * (1 + Real.sqrt (Qm β (gammaOf N B)))) with hK
  refine ⟨K, c, hcpos, by positivity, fun s hs => ?_⟩
  obtain ⟨hq0, hqle⟩ := pl_q_facts μ hβ0 hβ1 hB hN hpos hs
  obtain ⟨hf0, hf1, hfΛ⟩ := pl_f_facts μ hβ0 hβ1 hB hN hpos i hs
  obtain ⟨hR0, hR1⟩ := hR _ hq0
  obtain ⟨hm, _⟩ := pl_mOf_spec μ hβ0 hβ1 hB hN hpos hs
  have hRK : Lw (emaW β) (Qm β (mOf β B μ s)) / Fw (emaW β) (Qm β (mOf β B μ s)) ≤
      C0 * (1 + Real.sqrt (Qm β (gammaOf N B))) :=
    hR1.trans (mul_le_mul_of_nonneg_left (by linarith [Real.sqrt_le_sqrt hqle]) hC0)
  have hG : Gfun β B μ i s = (Lw (emaW β) (Qm β (mOf β B μ s)) /
      Fw (emaW β) (Qm β (mOf β B μ s))) * partF B μ i (mOf β B μ s) := rfl
  have hGn : 0 ≤ Gfun β B μ i s := by rw [hG]; exact mul_nonneg hR0 hf0.le
  rw [abs_of_nonneg hGn, hG]
  -- f ≤ c/s
  have hsl := pl_s_Lam μ hβ0 hβ1 hB hN hpos hs
  have hQm0 := pl_Fw_pos hβ0.le hβ1 hq0.le
  have hFle := pl_Fw_le_zero hβ0.le hβ1 hq0.le
  have hΛs : s * partLam B μ (mOf β B μ s) ≤ gammaOf N B * Fw (emaW β) 0 := by
    rw [hsl]
    exact mul_le_mul (by linarith [hm.1]) hFle hQm0.le hγ.le
  have hfc : partF B μ i (mOf β B μ s) * s ≤ c := by
    calc partF B μ i (mOf β B μ s) * s ≤ (partLam B μ (mOf β B μ s) * μ i) * s :=
          mul_le_mul_of_nonneg_right hfΛ hs.le
      _ = (s * partLam B μ (mOf β B μ s)) * μ i := by ring
      _ ≤ (gammaOf N B * Fw (emaW β) 0) * μ i := mul_le_mul_of_nonneg_right hΛs (hpos i).le
  have hf2 : partF B μ i (mOf β B μ s) ≤ 2 * (c / (c + s)) := by
    rcases le_total s c with h | h
    · refine hf1.le.trans ?_
      rw [← mul_div_assoc, le_div_iff₀ (by linarith)]
      linarith
    · calc partF B μ i (mOf β B μ s) = partF B μ i (mOf β B μ s) * s / s := by field_simp
        _ ≤ c / s := by gcongr
        _ ≤ 2 * (c / (c + s)) := by
          rw [← mul_div_assoc, div_le_div_iff₀ hs (by linarith)]
          nlinarith
  calc _ ≤ (C0 * (1 + Real.sqrt (Qm β (gammaOf N B)))) * (2 * (c / (c + s))) :=
        mul_le_mul hRK hf2 hf0.le (by positivity)
    _ = K * (c / (c + s)) := by rw [hK]; ring

/-- Measurability of `u ↦ 𝒢_i(τ u)` on `(0,∞)` for a monotone `τ` into `(0,∞)`. -/
private lemma pl_G_meas {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i) (i : Fin N) {τ : ℝ → ℝ}
    (hτ : MonotoneOn τ (Ioi 0)) (hτ0 : ∀ u, 0 < u → 0 < τ u) :
    AEStronglyMeasurable (fun u => Gfun β B μ i (τ u)) (volume.restrict (Ioi 0)) := by
  set Rp : ℝ → ℝ := (Ioi (0:ℝ)).piecewise (fun x => Lw (emaW β) x / Fw (emaW β) x) 0 with hRp
  have hRpm : Measurable Rp := by
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const measurableSet_Ioi
    intro x hx
    exact ((lem_app_pl_weights_ii_L hβ0.le hβ1 x hx).1.div
      (lem_app_pl_weights_ii_F hβ0.le hβ1 x hx).1 (pl_Fw_pos hβ0.le hβ1 hx.le).ne').continuousAt.continuousWithinAt
  have hqa : AntitoneOn (fun u => Qm β (mOf β B μ (τ u))) (Ioi 0) := by
    intro a ha b hb hab
    exact pl_q_anti μ hβ0 hβ1 hB hN hpos (hτ0 a ha) (hτ ha hb hab)
  have hfa : AntitoneOn (fun u => partF B μ i (mOf β B μ (τ u))) (Ioi 0) := by
    intro a ha b hb hab
    exact pl_f_anti μ hβ0 hβ1 hB hN hpos i (hτ0 a ha) (hτ ha hb hab)
  have h1 : AEMeasurable (fun u => Qm β (mOf β B μ (τ u))) (volume.restrict (Ioi 0)) :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioi hqa
  have h2 : AEMeasurable (fun u => partF B μ i (mOf β B μ (τ u))) (volume.restrict (Ioi 0)) :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioi hfa
  have h3 : AEMeasurable (fun u => Rp (Qm β (mOf β B μ (τ u))) * partF B μ i (mOf β B μ (τ u)))
      (volume.restrict (Ioi 0)) := (hRpm.comp_aemeasurable h1).mul h2
  refine h3.aestronglyMeasurable.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall (fun u hu => ?_))
  have hq0 := (pl_q_facts μ hβ0 hβ1 hB hN hpos (hτ0 u hu)).1
  simp only [hRp, Set.piecewise_eq_of_mem _ _ _ (Set.mem_Ioi.2 hq0)]
  rfl


private lemma pl_integrable_major {K c : ℝ} (hc : 0 < c) :
    Integrable (fun u : ℝ => K * (c / (c + u ^ 2))) := by
  have h := (integrable_inv_one_add_sq.comp_div (Real.sqrt_pos.2 hc).ne').const_mul K
  refine h.congr (Filter.Eventually.of_forall (fun u => ?_))
  simp only [Function.comp]
  congr 1
  rw [div_pow, Real.sq_sqrt hc.le]
  field_simp

private lemma pl_G_int {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hpos : ∀ i, 0 < μ i) (i : Fin N) {τ : ℝ → ℝ}
    (hτ : MonotoneOn τ (Ioi 0)) (hτ2 : ∀ u, 0 < u → u ^ 2 ≤ τ u) :
    IntegrableOn (fun u => Gfun β B μ i (τ u)) (Ioi 0) := by
  obtain ⟨K, c, hc, hK, hmaj⟩ := pl_G_major μ hβ0 hβ1 hB hN hpos i
  have hτ0 : ∀ u, 0 < u → 0 < τ u := fun u hu => lt_of_lt_of_le (pow_pos hu 2) (hτ2 u hu)
  have hm := pl_G_meas μ hβ0 hβ1 hB hN hpos i hτ hτ0
  refine Integrable.mono' ((pl_integrable_major (K := K) hc).restrict) hm ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall (fun u hu => ?_))
  have hu' : 0 < u := hu
  rw [Real.norm_eq_abs]
  refine (hmaj _ (hτ0 u hu')).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hK
  rw [div_le_div_iff₀ (by have := hτ0 u hu'; linarith) (by positivity)]
  nlinarith [hτ2 u hu', hc]


/-! ## Drift at zero ridge (`prop:app-pl-drift-zero`, part form) -/

/-- `prop:app-pl-drift-zero`(i) (snapshot `cr-2026-10-23`), part form. LaTeX, verbatim from
`section.tex` l.372–390. Here `volraw_i(s)` is replaced by `f_i(m(s))`, which is equal to it
by `prop:app-pl-branch`(iii) (L-G.12). Record declaration: L-G.12.

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
theorem prop_app_pl_drift_zero_i {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i) :
    Tendsto (fun s => Qm β (mOf β B μ s)) (nhdsWithin (0 : ℝ) (Ioi 0))
        (𝓝 (Qm β (gammaOf N B))) ∧
      Tendsto (fun s => s * partLam B μ (mOf β B μ s) ^ 2) (nhdsWithin (0 : ℝ) (Ioi 0))
        (𝓝 (Fw (emaW β) (Qm β (gammaOf N B)) * ((B : ℝ)⁻¹ * ∑ i, (μ i)⁻¹))) ∧
      ∀ i : Fin N, ∀ s : ℝ, 0 < s → s ≤ sN β B μ (partMN B μ 1) →
        1 - partF B μ i (mOf β B μ s) = 1 / (1 + partLam B μ (mOf β B μ s) * μ i) ∧
        1 / (1 + partLam B μ (mOf β B μ s) * μ i) ≤
          (1 / μ i) * Real.sqrt ((1 + μ ⟨0, hN⟩) /
            (gammaOf N B * Fw (emaW β) (Qm β (gammaOf N B)))) * Real.sqrt s := by
  have hγ := pl_gamma_pos hB hN
  have hQγ : 0 < Qm β (gammaOf N B) := (pl_Qm_spec hβ0 hβ1 hγ).1
  refine ⟨pl_Qm_mOf_tendsto μ hβ0 hβ1 hB hN hpos, ?_, ?_⟩
  · -- s Λ² limit
    have hFt : Tendsto (fun s => Fw (emaW β) (Qm β (mOf β B μ s))) (𝓝[>] (0:ℝ))
        (𝓝 (Fw (emaW β) (Qm β (gammaOf N B)))) :=
      ((pl_Fw_contAt hβ0.le hβ1 hQγ).tendsto).comp (pl_Qm_mOf_tendsto μ hβ0 hβ1 hB hN hpos)
    have hg0 : Tendsto (fun Λ : ℝ => ∑ i, Λ / (1 + Λ * μ i)) atTop
        (𝓝 (∑ i, (μ i)⁻¹)) := by
      refine tendsto_finsetSum _ (fun i _ => ?_)
      have h1 := (pl_term_tendsto (hpos i)).const_mul ((μ i)⁻¹)
      rw [mul_one] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with Λ hΛ
      have : 0 < 1 + Λ * μ i := by have := mul_pos hΛ (hpos i); linarith
      have := (hpos i).ne'
      field_simp
    have hg := hg0.const_mul ((B:ℝ)⁻¹)
    have hcomp := hg.comp (pl_Lam_tendsto μ hβ0 hβ1 hB hN hpos)
    have := hFt.mul hcomp
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : 0 < s := hs
    obtain ⟨hm, _⟩ := pl_mOf_spec μ hβ0 hβ1 hB hN hpos hs0
    obtain ⟨h1, h2⟩ := pl_partLam_spec μ hB hN hpos hm
    have hsl := pl_s_Lam μ hβ0 hβ1 hB hN hpos hs0
    have hgs := pl_gamma_sub_partMN (B := B) μ hpos h2
    simp only [Function.comp]
    rw [h1] at hgs
    have e : (B:ℝ)⁻¹ * ∑ i, partLam B μ (mOf β B μ s) / (1 + partLam B μ (mOf β B μ s) * μ i)
        = partLam B μ (mOf β B μ s) * (gammaOf N B - mOf β B μ s) := by
      rw [hgs]
      have hh : ∀ i, partLam B μ (mOf β B μ s) / (1 + partLam B μ (mOf β B μ s) * μ i) =
          partLam B μ (mOf β B μ s) * (1 / (1 + partLam B μ (mOf β B μ s) * μ i)) :=
        fun i => by ring
      simp only [hh, ← Finset.mul_sum]
      ring
    rw [e]
    calc Fw (emaW β) (Qm β (mOf β B μ s)) * (partLam B μ (mOf β B μ s) * (gammaOf N B - mOf β B μ s))
        = (s * partLam B μ (mOf β B μ s)) * partLam B μ (mOf β B μ s) := by
          rw [hsl]; ring
      _ = s * partLam B μ (mOf β B μ s) ^ 2 := by ring
  · intro i s hs hsz
    obtain ⟨hm, hsm⟩ := pl_mOf_spec μ hβ0 hβ1 hB hN hpos hs
    obtain ⟨h1, h2⟩ := pl_partLam_spec μ hB hN hpos hm
    set m := mOf β B μ s with hmdef
    set Λ := partLam B μ m with hΛdef
    have hΛ : 0 < Λ := h2
    have hden : 0 < 1 + Λ * μ i := by have := mul_pos hΛ (hpos i); linarith
    have hid : 1 - partF B μ i m = 1 / (1 + Λ * μ i) := by
      unfold partF
      rw [← hΛdef]
      field_simp
      ring
    refine ⟨hid, ?_⟩
    -- Λ ≥ 1
    have hm1 : m ∈ Ioo 0 (gammaOf N B) := hm
    have hmem1 := pl_partMN_mem μ hB hN hpos one_pos
    have hm1le : partMN B μ 1 ≤ m := by
      by_contra hcon
      push_neg at hcon
      have := (pl_sN_strictAnti μ hβ0 hβ1 hB hN hpos) hm1 hmem1 hcon
      rw [hsm] at this
      linarith
    have hΛ1 : 1 ≤ Λ := by
      by_contra hcon
      push_neg at hcon
      have := pl_partMN_mono μ hB hN hpos (Set.mem_Ici.2 hΛ.le) (Set.mem_Ici.2 zero_le_one) hcon
      rw [h1] at this
      linarith
    -- lower bound on γ - m
    have hμ0 : ∀ j, μ j ≤ μ ⟨0, hN⟩ := fun j => hanti (show (⟨0, hN⟩ : Fin N) ≤ j from Nat.zero_le _)
    have hgs := pl_gamma_sub_partMN (B := B) μ hpos hΛ
    rw [h1] at hgs
    have hden0 : 0 < 1 + Λ * μ ⟨0, hN⟩ := by have := mul_pos hΛ (hpos ⟨0, hN⟩); linarith
    have hgm : gammaOf N B / (1 + Λ * μ ⟨0, hN⟩) ≤ gammaOf N B - m := by
      rw [hgs]
      have : ∑ _j : Fin N, 1 / (1 + Λ * μ ⟨0, hN⟩) ≤ ∑ j, 1 / (1 + Λ * μ j) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        have hj : 0 < 1 + Λ * μ j := by have := mul_pos hΛ (hpos j); linarith
        exact one_div_le_one_div_of_le hj (by nlinarith [hμ0 j])
      calc gammaOf N B / (1 + Λ * μ ⟨0, hN⟩)
          = (B:ℝ)⁻¹ * ∑ _j : Fin N, 1 / (1 + Λ * μ ⟨0, hN⟩) := by
            rw [← pl_gamma_eq]; simp [div_eq_mul_inv]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this (inv_nonneg.2 (Nat.cast_nonneg B))
    -- Fw(Q_m) ≥ F⋆
    have hQle : Qm β m ≤ Qm β (gammaOf N B) := pl_Qm_mono hβ0 hβ1 hm.1 hm.2.le
    have hQpos : 0 < Qm β m := (pl_Qm_spec hβ0 hβ1 hm.1).1
    have hFge : Fw (emaW β) (Qm β (gammaOf N B)) ≤ Fw (emaW β) (Qm β m) :=
      pl_Fw_anti hβ0.le hβ1 (Set.mem_Ici.2 hQpos.le) (Set.mem_Ici.2 (hQpos.le.trans hQle)) hQle
    have hFs : 0 < Fw (emaW β) (Qm β (gammaOf N B)) := pl_Fw_pos hβ0.le hβ1 hQγ.le
    have hFm : 0 < Fw (emaW β) (Qm β m) := pl_Fw_pos hβ0.le hβ1 hQpos.le
    have hsl := pl_s_Lam μ hβ0 hβ1 hB hN hpos hs
    rw [← hmdef, ← hΛdef] at hsl
    set Fs := Fw (emaW β) (Qm β (gammaOf N B)) with hFsdef
    set γ := gammaOf N B with hγdef
    have h1' : γ * Fs / (1 + Λ * μ ⟨0, hN⟩) ≤ s * Λ := by
      rw [hsl]
      calc γ * Fs / (1 + Λ * μ ⟨0, hN⟩) = γ / (1 + Λ * μ ⟨0, hN⟩) * Fs := by ring
        _ ≤ (γ - m) * Fw (emaW β) (Qm β m) :=
            mul_le_mul hgm hFge hFs.le (by linarith [hm.2])
    have h2' : γ * Fs ≤ s * Λ * (1 + Λ * μ ⟨0, hN⟩) := by
      rwa [div_le_iff₀ hden0] at h1'
    have hμ0pos := hpos ⟨0, hN⟩
    have h3' : γ * Fs ≤ (1 + μ ⟨0, hN⟩) * s * Λ ^ 2 := by
      have : s * Λ * (1 + Λ * μ ⟨0, hN⟩) ≤ (1 + μ ⟨0, hN⟩) * s * Λ ^ 2 := by
        have hsΛ : 0 ≤ s * Λ := by positivity
        nlinarith [mul_nonneg hsΛ (mul_nonneg (sub_nonneg.2 hΛ1) hμ0pos.le), mul_nonneg hsΛ (sub_nonneg.2 hΛ1)]
      linarith
    have hinvΛ : 1 / Λ ≤ Real.sqrt ((1 + μ ⟨0, hN⟩) / (γ * Fs)) * Real.sqrt s := by
      rw [← Real.sqrt_mul (by positivity)]
      apply Real.le_sqrt_of_sq_le
      have hgF : 0 < γ * Fs := mul_pos hγ hFs
      rw [div_pow, one_pow, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hgF]
      nlinarith [h3']
    have hμi := hpos i
    calc 1 / (1 + Λ * μ i) ≤ 1 / (Λ * μ i) :=
          one_div_le_one_div_of_le (mul_pos hΛ hμi) (by linarith)
      _ = (1 / μ i) * (1 / Λ) := by field_simp
      _ ≤ (1 / μ i) * (Real.sqrt ((1 + μ ⟨0, hN⟩) / (γ * Fs)) * Real.sqrt s) :=
          mul_le_mul_of_nonneg_left hinvΛ (by positivity)
      _ = _ := by ring

/-- `prop:app-pl-drift-zero`(ii), finiteness, part form (snapshot `cr-2026-10-23`). The
integral `𝔡_i(0)` is finite (`Integrable` on `(0,∞)`). LaTeX, verbatim from `section.tex`
l.372–390; record declaration: L-G.12.

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
theorem prop_app_pl_drift_zero_ii_fin {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    (i : Fin N) :
    Integrable (fun u : ℝ => Gfun β B μ i (u ^ 2)) (volume.restrict (Ioi 0)) := by
  exact pl_G_int μ hβ0 hβ1 hB hN hpos i (τ := fun u => u ^ 2)
    (fun a ha b hb hab => pow_le_pow_left₀ (le_of_lt ha) hab 2) (fun u _ => le_rfl)

/-- `prop:app-pl-drift-zero`(ii), uniform bound, part form (snapshot `cr-2026-10-23`). The
constant `C` depends only on `β`, and the bound is uniform over all finite positive spectra
of this shape, with `dPart` in place of `𝔡_i(ϱ)`. LaTeX, verbatim from `section.tex` l.372–390;
record declaration: L-G.12.

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
theorem prop_app_pl_drift_zero_ii_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C : ℝ, ∀ (N B : ℕ) (μ : Fin N → ℝ), 0 < B → 0 < N → Antitone μ → (∀ i, 0 < μ i) →
      ∀ ϱ : ℝ, 0 < ϱ → ∀ i : Fin N,
        |dPart β B μ i ϱ - dZero β B μ i| ≤
          C / gammaOf N B * Real.sqrt ϱ * (1 + Real.sqrt (Qm β (gammaOf N B))) := by
  obtain ⟨C0, hC0, hR⟩ := pl_R_bound hβ0 hβ1
  obtain ⟨C1, hC1, hlip⟩ := pl_R_lip hβ0 hβ1
  refine ⟨Real.sqrt 2 / Real.pi * (2 * C1 + C0), ?_⟩
  intro N B μ hB hN _hanti hpos ϱ hϱ i
  have hγ := pl_gamma_pos hB hN
  set Qg := Qm β (gammaOf N B) with hQg
  have hQg0 : 0 ≤ Real.sqrt Qg := Real.sqrt_nonneg _
  set K := C0 * (1 + Real.sqrt Qg) with hK
  have hK0 : 0 ≤ K := by positivity
  set φ : ℝ → ℝ := fun s => 2 * C1 * Real.sqrt (Qm β (mOf β B μ s)) +
    K * partF B μ i (mOf β B μ s) with hφ
  set Φ : ℝ := 2 * C1 * Real.sqrt Qg + K with hΦ
  have hφanti : AntitoneOn φ (Ioi 0) := by
    intro a ha b hb hab
    have h1 := pl_q_anti μ hβ0 hβ1 hB hN hpos (Set.mem_Ioi.1 ha) hab
    have h2 := pl_f_anti μ hβ0 hβ1 hB hN hpos i (Set.mem_Ioi.1 ha) hab
    show 2 * C1 * Real.sqrt (Qm β (mOf β B μ b)) + K * partF B μ i (mOf β B μ b) ≤
      2 * C1 * Real.sqrt (Qm β (mOf β B μ a)) + K * partF B μ i (mOf β B μ a)
    have := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1) (by positivity : 0 ≤ 2 * C1)
    have := mul_le_mul_of_nonneg_left h2 hK0
    linarith
  have hφ0 : ∀ s, 0 < s → 0 ≤ φ s := by
    intro s hs
    obtain ⟨hf0, _, _⟩ := pl_f_facts μ hβ0 hβ1 hB hN hpos i hs
    show 0 ≤ 2 * C1 * Real.sqrt (Qm β (mOf β B μ s)) + K * partF B μ i (mOf β B μ s)
    positivity
  have hφΦ : ∀ s, 0 < s → φ s ≤ Φ := by
    intro s hs
    obtain ⟨_, hf1, _⟩ := pl_f_facts μ hβ0 hβ1 hB hN hpos i hs
    obtain ⟨_, hq⟩ := pl_q_facts μ hβ0 hβ1 hB hN hpos hs
    show 2 * C1 * Real.sqrt (Qm β (mOf β B μ s)) + K * partF B μ i (mOf β B μ s) ≤ _
    have := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hq) (by positivity : 0 ≤ 2 * C1)
    have := mul_le_mul_of_nonneg_left hf1.le hK0
    linarith
  -- integrability
  have hI0 := pl_G_int μ hβ0 hβ1 hB hN hpos i (τ := fun u => u ^ 2)
    (fun a ha b hb hab => pow_le_pow_left₀ (le_of_lt ha) hab 2) (fun u _ => le_rfl)
  have hI1 := pl_G_int μ hβ0 hβ1 hB hN hpos i (τ := fun u => ϱ + u ^ 2)
    (fun a ha b hb hab => by
      have := pow_le_pow_left₀ (le_of_lt ha) hab 2
      show ϱ + a ^ 2 ≤ ϱ + b ^ 2
      linarith)
    (fun u _ => by show u ^ 2 ≤ ϱ + u ^ 2; linarith)
  set D : ℝ → ℝ := fun u => Gfun β B μ i (u ^ 2) - Gfun β B μ i (ϱ + u ^ 2) with hD
  have hDint : IntegrableOn D (Ioi 0) := hI0.sub hI1
  have hDle : ∀ u, 0 < u → |D u| ≤ φ (u ^ 2) - φ (ϱ + u ^ 2) := by
    intro u hu
    have ha : 0 < u ^ 2 := pow_pos hu 2
    have hab : u ^ 2 ≤ ϱ + u ^ 2 := by linarith
    have hb : 0 < ϱ + u ^ 2 := by linarith
    have hqab := pl_q_anti μ hβ0 hβ1 hB hN hpos ha hab
    have hfab := pl_f_anti μ hβ0 hβ1 hB hN hpos i ha hab
    obtain ⟨hqb0, hqbg⟩ := pl_q_facts μ hβ0 hβ1 hB hN hpos hb
    obtain ⟨hfa0, hfa1, _⟩ := pl_f_facts μ hβ0 hβ1 hB hN hpos i ha
    obtain ⟨hfb0, _, _⟩ := pl_f_facts μ hβ0 hβ1 hB hN hpos i hb
    obtain ⟨hRb0, hRb1⟩ := hR _ hqb0
    have hRb : Lw (emaW β) (Qm β (mOf β B μ (ϱ + u ^ 2))) / Fw (emaW β) (Qm β (mOf β B μ (ϱ + u ^ 2))) ≤ K :=
      hRb1.trans (mul_le_mul_of_nonneg_left (by linarith [Real.sqrt_le_sqrt hqbg]) hC0)
    have hL := hlip _ _ hqb0 hqab
    set qa := Qm β (mOf β B μ (u ^ 2))
    set qb := Qm β (mOf β B μ (ϱ + u ^ 2))
    set fa := partF B μ i (mOf β B μ (u ^ 2))
    set fb := partF B μ i (mOf β B μ (ϱ + u ^ 2))
    set Ra := Lw (emaW β) qa / Fw (emaW β) qa
    set Rb := Lw (emaW β) qb / Fw (emaW β) qb
    have hsqab : Real.sqrt qb ≤ Real.sqrt qa := Real.sqrt_le_sqrt hqab
    have hD' : D u = (Ra - Rb) * fa + Rb * (fa - fb) := by
      show Gfun β B μ i (u ^ 2) - Gfun β B μ i (ϱ + u ^ 2) = _
      show Ra * fa - Rb * fb = _
      ring
    rw [hD']
    have t1 : |(Ra - Rb) * fa| ≤ 2 * C1 * (Real.sqrt qa - Real.sqrt qb) := by
      rw [abs_mul, abs_of_pos hfa0]
      calc |Ra - Rb| * fa ≤ (2 * C1 * (Real.sqrt qa - Real.sqrt qb)) * fa :=
            mul_le_mul_of_nonneg_right hL hfa0.le
        _ ≤ (2 * C1 * (Real.sqrt qa - Real.sqrt qb)) * 1 :=
            mul_le_mul_of_nonneg_left hfa1.le (mul_nonneg (by positivity) (by linarith))
        _ = _ := mul_one _
    have t2 : |Rb * (fa - fb)| ≤ K * (fa - fb) := by
      rw [abs_mul, abs_of_nonneg hRb0, abs_of_nonneg (by linarith)]
      exact mul_le_mul_of_nonneg_right hRb (by linarith)
    refine (abs_add_le _ _).trans ?_
    show _ ≤ (2 * C1 * Real.sqrt qa + K * fa) - (2 * C1 * Real.sqrt qb + K * fb)
    linarith
  have hshift := pl_shift_bound hϱ hφanti hφ0 hφΦ hDint hDle
  -- assemble
  have hI : (∫ u in Ioi (0:ℝ), Gfun β B μ i (ϱ + u ^ 2)) - ∫ u in Ioi (0:ℝ), Gfun β B μ i (u ^ 2) =
      -∫ u in Ioi (0:ℝ), D u := by
    rw [← integral_neg]
    have : ∀ u, -D u = Gfun β B μ i (ϱ + u ^ 2) - Gfun β B μ i (u ^ 2) := fun u => by simp [hD]
    simp only [this]
    exact (integral_sub hI1 hI0).symm
  have hdiff : dPart β B μ i ϱ - dZero β B μ i =
      Real.sqrt 2 / (Real.pi * gammaOf N B) * (-∫ u in Ioi (0:ℝ), D u) := by
    rw [← hI]; unfold dPart dZero; ring
  have habs : |∫ u in Ioi (0:ℝ), D u| ≤ Φ * Real.sqrt ϱ :=
    (abs_integral_le_integral_abs).trans hshift
  rw [hdiff, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < Real.sqrt 2 / (Real.pi * gammaOf N B))]
  have hΦle : Φ ≤ (2 * C1 + C0) * (1 + Real.sqrt Qg) := by
    simp only [hΦ, hK]; nlinarith [mul_nonneg hC1 hQg0]
  have hsqϱ := Real.sqrt_nonneg ϱ
  calc Real.sqrt 2 / (Real.pi * gammaOf N B) * |∫ u in Ioi (0:ℝ), D u|
      ≤ Real.sqrt 2 / (Real.pi * gammaOf N B) * (Φ * Real.sqrt ϱ) :=
        mul_le_mul_of_nonneg_left habs (by positivity)
    _ ≤ Real.sqrt 2 / (Real.pi * gammaOf N B) * ((2 * C1 + C0) * (1 + Real.sqrt Qg) * Real.sqrt ϱ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΦle hsqϱ) (by positivity)
    _ = _ := by field_simp

end Muon.PowerLaw

end

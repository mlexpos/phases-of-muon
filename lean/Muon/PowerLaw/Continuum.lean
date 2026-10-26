import Muon.PowerLaw.Participation
import Muon.Foundations.RealAnalysis

/-!
# Appendix G: thin-batch power law, continuum and finite participation (work package L-G.3)

Snapshot `cr-2026-10-23`. Source: `sections/06-power-law/section.tex`, subsection
"The power-law regime: statements" (l.750–1006: `assum:app-pl-regime`, `eqn:app-pl-constants`,
`eqn:app-pl-icd`, `eqn:app-pl-icv`, `prop:app-pl-scales`, `eqn:app-pl-kappa`) and subsection
"Power-law participation" (l.1215–1330: `eqn:app-pl-SN`, `eqn:app-pl-Lambda-V`,
`lem:app-pl-continuum`, `lem:app-pl-finite-inverse`, `lem:app-pl-elasticity`), together with
`eqn:app-pl-Bi-bulk`, the bulk display of `lem:app-pl-drift-participation` (coordinator's
assignment, L-G.2 review 2026-10-23). Card: `sections/06-power-law/CARD.md` §2, §3, §5 (L-G.3), §6.

Representation choices:

* Participation objects `gammaOf`, `partMN`, `partLam`, `partF`, `partBfun`, `thetaN`, `Efun`
  are reused from `Muon.PowerLaw.Participation` and `Muon.PowerLaw.Weights`; `sPow` and `emaW`
  are `Muon.sPow`, `Muon.emaW` (`Muon.Foundations.Conventions`).
* The power-law spectrum `μ_i = c_N i^{-α}`, `1 ≤ i ≤ N`, is `plSpec α c N : Fin N → ℝ`; the
  index `i : Fin N` stands for the row `i+1`. The sums `∑_{j=1}^N` of the source are
  `Finset.Icc 1 N` in `finS`.
* Regime. `assum_app_pl_regime` is the sequence-level hypothesis. Statements about limits
  (`∼`, `→`, uniform convergence) quantify over row sequences `n : ℕ` with `atTop`. Pointwise
  identities and bounds quantify over all positive triples `(N, B, c)`, as the source does
  ("independent of `N, B, c_N, Λ`"); the regime enters them only through positivity. Statements
  that involve only `α` (continuum) or `α` and `N` (finite inverse (i),(iii)) carry `0 < α` and
  `0 < N` and no sequence.
* `S_α`, `V_α` and `T` are defined here as `contS`, `contV`, `Tcont`, because
  `lem:app-pl-continuum` needs them. `def:app-pl-profiles` (L-G.4) must reuse these, not copy them.
* `c_0 = √(2/π)` is `c0`.
* `K_α`, `i_c`, `b_N`, `d_α` (`eqn:app-pl-constants`) are defined for every α and are used only
  for α > 1; their values for α ≤ 1 are junk and no statement uses them there.
* `icdD`, `icdIdx`, `icdA` follow `eqn:app-pl-icd` with `if α < 1` splitting the two cases
  (`α = 1` is the `else` branch; for α > 1 the values are junk). `icvIdx` is defined by the first
  form `i_{c,𝔳} = c_0^{2/α} i_{c,𝔡}` and its case form is `eqn_app_pl_icv`.
* Lean `∼` is `Asymptotics.IsEquivalent`. Two-sided `≍` is an explicit `∃ c C > 0` bound.
* Declarations of record follow `kind:app-x-y ↦ Muon.PowerLaw.kind_app_x_y`; numbered parts and
  α-cases get suffixes `_i`, `_ii`, `_i_lt`, `_i_one`, `_i_gt`, … .
* Not in this file: `thm:app-pl-drift`, `thm:app-pl-volatility` (they use `icdIdx` and `icvIdx`
  in their displayed definitions only), `prop:app-pl-profiles` and `def:app-pl-profiles` (L-G.4),
  the `Ψ`-profile lemmas (L-G.4), and `prop:app-pl-branch`(ii),(iii) (L-G.12).
-/

set_option linter.style.longLine false

open MeasureTheory Filter Topology Set Asymptotics
open Muon.DetEquiv

namespace Muon.PowerLaw

/-! ## Constants and the regime (`eqn:app-pl-constants`, `assum:app-pl-regime`) -/

/-- `c_0 = 𝔼|g| = √(2/π)` (`section.tex` l.47–53, "Dimensions and covariances"). -/
noncomputable def c0 : ℝ := Real.sqrt (2 / Real.pi)

/-- The power-law spectrum `μ_i = c_N i^{-α}`, `1 ≤ i ≤ N` (`assum:app-pl-regime`,
`section.tex` l.753–761), indexed by `i : Fin N` as the row `i + 1`. -/
noncomputable def plSpec (α c : ℝ) (N : ℕ) : Fin N → ℝ :=
  fun i => c * (((i : ℕ) : ℝ) + 1) ^ (-α)

/-- `assum:app-pl-regime` (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{assumption}[Thin-batch power law]\label{assum:app-pl-regime}
The exponent $\alpha>0$ and the momentum $\bmom\in(0,1)$ are fixed. Along a
sequence of positive integers $N$ and $B=B_N$,
\[
N\to\infty,\qquad B\to\infty,\qquad \gamma=\frac NB\to\infty,
\]
and the spectrum is $\mu_i=c_Ni^{-\alpha}$ for $1\le i\le N$, with amplitudes
$c_N>0$, with $\Sigmain=\Id_N$ and $\Nout=\Nin=N$.
\end{assumption}
-/
structure assum_app_pl_regime (α β : ℝ) (N B : ℕ → ℕ) (c : ℕ → ℝ) : Prop where
  hα : 0 < α
  hβ0 : 0 < β
  hβ1 : β < 1
  hNpos : ∀ n, 0 < N n
  hBpos : ∀ n, 0 < B n
  hcpos : ∀ n, 0 < c n
  hN : Tendsto (fun n => ((N n : ℕ) : ℝ)) atTop atTop
  hB : Tendsto (fun n => ((B n : ℕ) : ℝ)) atTop atTop
  hγ : Tendsto (fun n => ((N n : ℕ) : ℝ) / ((B n : ℕ) : ℝ)) atTop atTop

/-- `eqn:app-pl-constants` (snapshot `cr-2026-10-23`); defines `a_N`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-constants}
\begin{gathered}
a_N\defeq\sqrt{c_N}\,N^{-\alpha/2},\qquad
K_\alpha\defeq\frac{\pi}{\alpha\sin(\pi/\alpha)},\qquad
i_{\mathrm c}\defeq\frac{B}{K_\alpha},\\
b_N\defeq\sqrt{c_N}\,\big(\gamma\,i_{\mathrm c}^{\alpha}\big)^{-1/2},\qquad
d_\alpha\defeq\frac{c_0\,\pi}{\alpha\cos(\pi/(2\alpha))},
\end{gathered}
\end{equation}
-/
noncomputable def aN (α c : ℝ) (N : ℕ) : ℝ := Real.sqrt c * (N : ℝ) ^ (-α / 2)

/-- `eqn:app-pl-constants` (snapshot `cr-2026-10-23`); defines `K_α` (used for α > 1 only). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-constants}
\begin{gathered}
a_N\defeq\sqrt{c_N}\,N^{-\alpha/2},\qquad
K_\alpha\defeq\frac{\pi}{\alpha\sin(\pi/\alpha)},\qquad
i_{\mathrm c}\defeq\frac{B}{K_\alpha},\\
b_N\defeq\sqrt{c_N}\,\big(\gamma\,i_{\mathrm c}^{\alpha}\big)^{-1/2},\qquad
d_\alpha\defeq\frac{c_0\,\pi}{\alpha\cos(\pi/(2\alpha))},
\end{gathered}
\end{equation}
-/
noncomputable def Kc (α : ℝ) : ℝ := Real.pi / (α * Real.sin (Real.pi / α))

/-- `eqn:app-pl-constants` (snapshot `cr-2026-10-23`); defines `i_c = B/K_α` (used for α > 1 only). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-constants}
\begin{gathered}
a_N\defeq\sqrt{c_N}\,N^{-\alpha/2},\qquad
K_\alpha\defeq\frac{\pi}{\alpha\sin(\pi/\alpha)},\qquad
i_{\mathrm c}\defeq\frac{B}{K_\alpha},\\
b_N\defeq\sqrt{c_N}\,\big(\gamma\,i_{\mathrm c}^{\alpha}\big)^{-1/2},\qquad
d_\alpha\defeq\frac{c_0\,\pi}{\alpha\cos(\pi/(2\alpha))},
\end{gathered}
\end{equation}
-/
noncomputable def icCross (α : ℝ) (B : ℕ) : ℝ := (B : ℝ) / Kc α

/-- `eqn:app-pl-constants` (snapshot `cr-2026-10-23`); defines `b_N` (used for α > 1 only). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-constants}
\begin{gathered}
a_N\defeq\sqrt{c_N}\,N^{-\alpha/2},\qquad
K_\alpha\defeq\frac{\pi}{\alpha\sin(\pi/\alpha)},\qquad
i_{\mathrm c}\defeq\frac{B}{K_\alpha},\\
b_N\defeq\sqrt{c_N}\,\big(\gamma\,i_{\mathrm c}^{\alpha}\big)^{-1/2},\qquad
d_\alpha\defeq\frac{c_0\,\pi}{\alpha\cos(\pi/(2\alpha))},
\end{gathered}
\end{equation}
-/
noncomputable def bN (α c : ℝ) (N B : ℕ) : ℝ :=
  Real.sqrt c * ((N : ℝ) / (B : ℝ) * icCross α B ^ α) ^ (-1 / 2 : ℝ)

/-- `eqn:app-pl-constants` (snapshot `cr-2026-10-23`); defines `d_α` (used for α > 1 only). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-constants}
\begin{gathered}
a_N\defeq\sqrt{c_N}\,N^{-\alpha/2},\qquad
K_\alpha\defeq\frac{\pi}{\alpha\sin(\pi/\alpha)},\qquad
i_{\mathrm c}\defeq\frac{B}{K_\alpha},\\
b_N\defeq\sqrt{c_N}\,\big(\gamma\,i_{\mathrm c}^{\alpha}\big)^{-1/2},\qquad
d_\alpha\defeq\frac{c_0\,\pi}{\alpha\cos(\pi/(2\alpha))},
\end{gathered}
\end{equation}
-/
noncomputable def dAl (α : ℝ) : ℝ := c0 * Real.pi / (α * Real.cos (Real.pi / (2 * α)))

/-! ## Participation sums and the continuum profiles (`eqn:app-pl-SN`, `def:app-pl-profiles`) -/

/-- `eqn:app-pl-SN` (snapshot `cr-2026-10-23`); defines `S_N(V) = (1/N) ∑_{j=1}^N V/(V+(j/N)^α)`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-SN}
S_N(V)\defeq\frac1N\sum_{j=1}^N\frac{V}{V+(j/N)^\alpha},\qquad V_N\defeq S_N^{-1},\qquad
\mathsf T(V)\defeq VS_\alpha'(V)=\int_0^1\frac{Vt^\alpha}{(V+t^\alpha)^2}\,\dif t .
\end{equation}
-/
noncomputable def finS (α : ℝ) (N : ℕ) (V : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 N, V / (V + ((j : ℝ) / (N : ℝ)) ^ α)

/-- `eqn:app-pl-SN` (snapshot `cr-2026-10-23`); defines `V_N = S_N^{-1}`, total extension by `Function.invFunOn` on `Ioi 0`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-SN}
S_N(V)\defeq\frac1N\sum_{j=1}^N\frac{V}{V+(j/N)^\alpha},\qquad V_N\defeq S_N^{-1},\qquad
\mathsf T(V)\defeq VS_\alpha'(V)=\int_0^1\frac{Vt^\alpha}{(V+t^\alpha)^2}\,\dif t .
\end{equation}
-/
noncomputable def finV (α : ℝ) (N : ℕ) (p : ℝ) : ℝ := Function.invFunOn (finS α N) (Ioi 0) p

/-- `eqn:app-pl-SN` (snapshot `cr-2026-10-23`); defines `T(V) = ∫_0^1 V t^α/(V+t^α)^2 dt`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-SN}
S_N(V)\defeq\frac1N\sum_{j=1}^N\frac{V}{V+(j/N)^\alpha},\qquad V_N\defeq S_N^{-1},\qquad
\mathsf T(V)\defeq VS_\alpha'(V)=\int_0^1\frac{Vt^\alpha}{(V+t^\alpha)^2}\,\dif t .
\end{equation}
-/
noncomputable def Tcont (α V : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, V * t ^ α / (V + t ^ α) ^ 2

/-- `S_α(V) = ∫_0^1 V/(V+t^α) dt` for `V > 0` (`def:app-pl-profiles`, `section.tex` l.776–777).
Defined here for `lem:app-pl-continuum`; L-G.4 reuses it. -/
noncomputable def contS (α V : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, V / (V + t ^ α)

/-- `V_α = S_α^{-1}` on `(0,1)` (`def:app-pl-profiles`, `section.tex` l.776–777). Total extension
by `Function.invFunOn` on `Ioi 0`. Defined here for `lem:app-pl-continuum`; L-G.4 reuses it. -/
noncomputable def contV (α p : ℝ) : ℝ := Function.invFunOn (contS α) (Ioi 0) p

private lemma pl_finS_term_strictMono {a : ℝ} (ha : 0 < a) :
    StrictMonoOn (fun V : ℝ => V / (V + a)) (Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0:ℝ) < x := hx
  have hy' : (0:ℝ) < y := hy
  have h1 : (0:ℝ) < x + a := by linarith
  have h2 : (0:ℝ) < y + a := by linarith
  change x / (x + a) < y / (y + a)
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith [mul_pos ha (sub_pos.2 hxy)]

private lemma pl_finS_strictMonoOn {N : ℕ} (α : ℝ) (hN : 0 < N) :
    StrictMonoOn (finS α N) (Ioi 0) := by
  intro x hx y hy hxy
  unfold finS
  apply mul_lt_mul_of_pos_left _ (inv_pos.2 (by exact_mod_cast hN))
  apply Finset.sum_lt_sum_of_nonempty
  · exact ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hN⟩⟩
  · intro j hj
    have hj' := Finset.mem_Icc.1 hj
    have hj0 : (0:ℝ) < (j:ℝ) := by exact_mod_cast (by omega : 0 < j)
    have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
    have ha : (0:ℝ) < ((j:ℝ) / (N:ℝ)) ^ α :=
      Real.rpow_pos_of_pos (div_pos hj0 hNr) α
    exact pl_finS_term_strictMono ha hx hy hxy

private lemma pl_finV_of_eq {N : ℕ} (α : ℝ) (hN : 0 < N) {V p : ℝ} (hV : 0 < V)
    (h : finS α N V = p) : finV α N p = V := by
  have hex : ∃ a ∈ Ioi (0:ℝ), finS α N a = p := ⟨V, hV, h⟩
  have h1 := Function.invFunOn_eq hex
  have h2 := Function.invFunOn_mem hex
  unfold finV
  exact (pl_finS_strictMonoOn α hN).injOn h2 (show V ∈ Ioi (0:ℝ) from hV) (h1.trans h.symm)

private lemma pl_sum_Icc_eq_Fin {N : ℕ} (f : ℕ → ℝ) :
    ∑ i : Fin N, f ((i : ℕ) + 1) = ∑ j ∈ Finset.Icc 1 N, f j := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]

/-- `eqn:app-pl-SN` (snapshot `cr-2026-10-23`); the identity `m_N(Λ) = γ S_N(V)` with `V = c_N Λ N^{-α}`, the sentence after the display. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-SN}
S_N(V)\defeq\frac1N\sum_{j=1}^N\frac{V}{V+(j/N)^\alpha},\qquad V_N\defeq S_N^{-1},\qquad
\mathsf T(V)\defeq VS_\alpha'(V)=\int_0^1\frac{Vt^\alpha}{(V+t^\alpha)^2}\,\dif t .
\end{equation}
-/
theorem eqn_app_pl_SN_mN {N B : ℕ} (α c : ℝ) (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) {Λ : ℝ}
    (hΛ : 0 < Λ) :
    partMN B (plSpec α c N) Λ = gammaOf N B * finS α N (c * Λ * (N : ℝ) ^ (-α)) := by
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hBr : (0:ℝ) < (B:ℝ) := by exact_mod_cast hB
  have hterm : ∀ j : ℕ, 1 ≤ j →
      Λ * (c * ((j:ℝ)) ^ (-α)) / (1 + Λ * (c * ((j:ℝ)) ^ (-α)))
        = (c * Λ * (N : ℝ) ^ (-α)) / (c * Λ * (N : ℝ) ^ (-α) + ((j:ℝ) / (N:ℝ)) ^ α) := by
    intro j hj
    have hj0 : (0:ℝ) < (j:ℝ) := by exact_mod_cast (by omega : 0 < j)
    rw [Real.div_rpow hj0.le hNr.le, Real.rpow_neg hj0.le, Real.rpow_neg hNr.le]
    have hjp : 0 < (j:ℝ) ^ α := Real.rpow_pos_of_pos hj0 α
    have hNp : 0 < (N:ℝ) ^ α := Real.rpow_pos_of_pos hNr α
    have hcΛ : 0 < c * Λ := mul_pos hc hΛ
    have h1 : 0 < 1 + Λ * (c * ((j:ℝ) ^ α)⁻¹) := by
      have := mul_pos hΛ (mul_pos hc (inv_pos.2 hjp)); linarith
    have h2 : 0 < c * Λ * ((N:ℝ) ^ α)⁻¹ + (j:ℝ) ^ α / (N:ℝ) ^ α := by
      have := mul_pos hcΛ (inv_pos.2 hNp)
      have := div_pos hjp hNp
      linarith
    rw [div_eq_div_iff h1.ne' h2.ne']
    field_simp
    ring
  have hsum : ∑ i : Fin N, Λ * (c * (((i:ℕ):ℝ) + 1) ^ (-α)) / (1 + Λ * (c * (((i:ℕ):ℝ) + 1) ^ (-α)))
      = ∑ j ∈ Finset.Icc 1 N, Λ * (c * ((j:ℝ)) ^ (-α)) / (1 + Λ * (c * ((j:ℝ)) ^ (-α))) := by
    rw [← pl_sum_Icc_eq_Fin (N := N)
      (fun j : ℕ => Λ * (c * ((j:ℝ)) ^ (-α)) / (1 + Λ * (c * ((j:ℝ)) ^ (-α))))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    push_cast
    rfl
  simp only [partMN, finS, gammaOf, plSpec]
  rw [hsum, Finset.sum_congr rfl (fun j hj => hterm j (Finset.mem_Icc.1 hj).1)]
  field_simp

/-- `eqn:app-pl-SN` (snapshot `cr-2026-10-23`); the identity `T(V) = V S_α'(V)`, the display's "T(V)≝VS_α'(V)=∫…". LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-SN}
S_N(V)\defeq\frac1N\sum_{j=1}^N\frac{V}{V+(j/N)^\alpha},\qquad V_N\defeq S_N^{-1},\qquad
\mathsf T(V)\defeq VS_\alpha'(V)=\int_0^1\frac{Vt^\alpha}{(V+t^\alpha)^2}\,\dif t .
\end{equation}
-/
theorem eqn_app_pl_SN_T {α : ℝ} (hα : 0 < α) {V : ℝ} (hV : 0 < V) :
    Tcont α V = V * deriv (contS α) V := by
  have hderiv : HasDerivAt (contS α) (∫ t in (0:ℝ)..1, t ^ α / (V + t ^ α) ^ 2) V := by
    change HasDerivAt (fun x => ∫ t in (0:ℝ)..1, x / (x + t ^ α)) _ V
    refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun x t => x / (x + t ^ α)) (F' := fun x t => t ^ α / (x + t ^ α) ^ 2)
      (s := Ioi (V / 2)) (bound := fun _ => 4 / V ^ 2) (Ioi_mem_nhds (by linarith)) ?_ ?_ ?_ ?_ ?_ ?_).2
    · exact Filter.Eventually.of_forall (fun x =>
        (Measurable.div measurable_const
          (measurable_const.add (measurable_id.pow_const α))).aestronglyMeasurable)
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const
        (continuousOn_const.add ((Real.continuous_rpow_const hα.le).continuousOn))
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      have h0 : 0 < V + t ^ α := by linarith [Real.rpow_nonneg ht.1 α]
      exact h0.ne'
    · exact (Measurable.div (measurable_id.pow_const α)
        ((measurable_const.add (measurable_id.pow_const α)).pow_const 2)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
      rw [Set.uIoc_of_le zero_le_one] at ht
      have hx' : V / 2 < x := hx
      have ha0 : 0 ≤ t ^ α := Real.rpow_nonneg ht.1.le α
      have ha1 : t ^ α ≤ 1 := Real.rpow_le_one ht.1.le ht.2 hα.le
      change ‖t ^ α / (x + t ^ α) ^ 2‖ ≤ 4 / V ^ 2
      rw [Real.norm_of_nonneg (div_nonneg ha0 (sq_nonneg _))]
      have hs : V / 2 < x + t ^ α := by linarith
      have hsq : (V / 2) ^ 2 < (x + t ^ α) ^ 2 := by nlinarith
      have hV2 : 0 ≤ V ^ 2 := sq_nonneg V
      rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right ha1 hV2]
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
      rw [Set.uIoc_of_le zero_le_one] at ht
      have hx' : V / 2 < x := hx
      have ha0 : 0 ≤ t ^ α := Real.rpow_nonneg ht.1.le α
      have hd : x + t ^ α ≠ 0 := by
        have : 0 < x + t ^ α := by linarith
        exact this.ne'
      have h := HasDerivAt.div (hasDerivAt_id' x)
        ((hasDerivAt_id' x).add_const (t ^ α)) hd
      convert h using 1
      ring
  rw [hderiv.deriv]
  unfold Tcont
  simp only [mul_div_assoc]
  rw [intervalIntegral.integral_const_mul]

/-- `eqn:app-pl-Lambda-V` (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-Lambda-V}
\Lambda_N(m)=\frac{N^\alpha}{c_N}\,V_N\Big(\frac m\gamma\Big)\qquad(0<m<\gamma).
\end{equation}
-/
theorem eqn_app_pl_Lambda_V {N B : ℕ} (α c : ℝ) (hN : 0 < N) (hB : 0 < B) (hc : 0 < c)
    {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    partLam B (plSpec α c N) m = (N : ℝ) ^ α / c * finV α N (m / gammaOf N B) := by
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hBr : (0:ℝ) < (B:ℝ) := by exact_mod_cast hB
  have hγ : 0 < gammaOf N B := by unfold gammaOf; exact div_pos hNr hBr
  have hpos : ∀ i, 0 < plSpec α c N i := fun i => by
    unfold plSpec
    exact mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)
  have hsurj : ∃ a ∈ Ioi (0:ℝ), partMN B (plSpec α c N) a = m :=
    (def_app_pl_participation_bij (plSpec α c N) hB hN hpos).1.surjOn hm
  have hL : partMN B (plSpec α c N) (partLam B (plSpec α c N) m) = m :=
    Function.invFunOn_eq hsurj
  have hLpos : partLam B (plSpec α c N) m ∈ Ioi (0:ℝ) := Function.invFunOn_mem hsurj
  generalize hLg : partLam B (plSpec α c N) m = L at hL hLpos ⊢
  have hLp : 0 < L := hLpos
  have hmN := eqn_app_pl_SN_mN (N := N) (B := B) α c hN hB hc hLp
  have hfin : finS α N (c * L * (N : ℝ) ^ (-α)) = m / gammaOf N B := by
    rw [eq_div_iff hγ.ne', mul_comm, ← hmN, hL]
  have hV : 0 < c * L * (N : ℝ) ^ (-α) :=
    mul_pos (mul_pos hc hLp) (Real.rpow_pos_of_pos hNr _)
  rw [pl_finV_of_eq α hN hV hfin, Real.rpow_neg hNr.le]
  have hNp : (N:ℝ) ^ α ≠ 0 := (Real.rpow_pos_of_pos hNr α).ne'
  field_simp

/-! ## Continuum participation (`lem:app-pl-continuum`) -/

/-- `lem:app-pl-continuum` (snapshot `cr-2026-10-23`), part (i), case `0 < α < 1`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Continuum participation]\label{lem:app-pl-continuum}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item As $V\downarrow0$, $S_\alpha(V)\sim V/(1-\alpha)$ for $\alpha<1$, $S_1(V)=V\log(1+1/V)\sim V\log(1/V)$,
and $S_\alpha(V)\sim K_\alpha V^{1/\alpha}$ for $\alpha>1$. As $V\to\infty$, $1-S_\alpha(V)\sim((\alpha+1)V)^{-1}$.
\item $\mathsf T(V)\asymp S_\alpha(V)\big(1-S_\alpha(V)\big)$ for $V>0$.
\item As $p\downarrow0$, $V_\alpha(p)\sim(1-\alpha)p$ for $\alpha<1$, $V_1(p)\sim p/\log(1/p)$, and
$V_\alpha(p)\sim(p/K_\alpha)^\alpha$ for $\alpha>1$; and $V_\alpha(p)\asymp(1-p)^{-1}$ for $p\ge1/2$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_continuum_i_lt {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    IsEquivalent (𝓝[>] (0 : ℝ)) (contS α) (fun V => V / (1 - α)) := by
  have hpos1 : (0:ℝ) < 1 - α := by linarith
  have hne1 : (1:ℝ) - α ≠ 0 := hpos1.ne'
  have hI : ∫ t in (0:ℝ)..1, t ^ (-α) = 1 / (1 - α) := by
    rw [integral_rpow (Or.inl (by linarith))]
    rw [Real.one_rpow, Real.zero_rpow (by linarith : -α + 1 ≠ 0)]
    rw [show -α + 1 = 1 - α by ring]
    ring
  have hpt : ∀ c : ℝ, 0 < c → Tendsto (fun V : ℝ => 1 / (V + c)) (𝓝[>] (0:ℝ)) (𝓝 (1 / c)) := by
    intro c hc
    have hcont : ContinuousAt (fun V : ℝ => 1 / (V + c)) 0 :=
      continuousAt_const.div (continuousAt_id.add continuousAt_const) (by simpa using hc.ne')
    have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
    simpa using h
  have hlim : Tendsto (fun V : ℝ => ∫ t in (0:ℝ)..1, 1 / (V + t ^ α)) (𝓝[>] (0:ℝ))
      (𝓝 (∫ t in (0:ℝ)..1, t ^ (-α))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => t ^ (-α))
    · filter_upwards with V
      exact (by fun_prop : Measurable fun t : ℝ => 1 / (V + t ^ α)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with V hV
      have hV' : (0:ℝ) < V := hV
      refine ae_of_all _ (fun t ht => ?_)
      rw [Set.uIoc_of_le zero_le_one] at ht
      have hc : 0 < t ^ α := Real.rpow_pos_of_pos ht.1 α
      rw [Real.norm_eq_abs, abs_of_nonneg (one_div_pos.mpr (by linarith)).le,
        Real.rpow_neg ht.1.le, ← one_div]
      exact one_div_le_one_div_of_le hc (by linarith)
    · exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
    · refine ae_of_all _ (fun t ht => ?_)
      rw [Set.uIoc_of_le zero_le_one] at ht
      have hc : 0 < t ^ α := Real.rpow_pos_of_pos ht.1 α
      rw [Real.rpow_neg ht.1.le, ← one_div]
      exact hpt (t ^ α) hc
  have hm := hlim.const_mul (1 - α)
  rw [hI, show (1 - α) * (1 / (1 - α)) = 1 by field_simp] at hm
  refine isEquivalent_of_tendsto_one (hm.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with V hV
  have hV' : (0:ℝ) < V := hV
  have hVne : V ≠ 0 := hV'.ne'
  change (1 - α) * (∫ t in (0:ℝ)..1, 1 / (V + t ^ α)) = contS α V / (V / (1 - α))
  have e : (fun t : ℝ => V / (V + t ^ α)) = fun t => V * (1 / (V + t ^ α)) := by
    funext t
    ring
  unfold contS
  rw [e, intervalIntegral.integral_const_mul]
  field_simp

/-- `lem:app-pl-continuum` (snapshot `cr-2026-10-23`), part (i), case `α = 1`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Continuum participation]\label{lem:app-pl-continuum}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item As $V\downarrow0$, $S_\alpha(V)\sim V/(1-\alpha)$ for $\alpha<1$, $S_1(V)=V\log(1+1/V)\sim V\log(1/V)$,
and $S_\alpha(V)\sim K_\alpha V^{1/\alpha}$ for $\alpha>1$. As $V\to\infty$, $1-S_\alpha(V)\sim((\alpha+1)V)^{-1}$.
\item $\mathsf T(V)\asymp S_\alpha(V)\big(1-S_\alpha(V)\big)$ for $V>0$.
\item As $p\downarrow0$, $V_\alpha(p)\sim(1-\alpha)p$ for $\alpha<1$, $V_1(p)\sim p/\log(1/p)$, and
$V_\alpha(p)\sim(p/K_\alpha)^\alpha$ for $\alpha>1$; and $V_\alpha(p)\asymp(1-p)^{-1}$ for $p\ge1/2$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_continuum_i_one :
    (∀ V : ℝ, 0 < V → contS 1 V = V * Real.log (1 + 1 / V)) ∧
      IsEquivalent (𝓝[>] (0 : ℝ)) (contS 1) (fun V => V * Real.log (1 / V)) := by
  have key : ∀ V : ℝ, 0 < V → contS 1 V = V * Real.log (1 + 1 / V) := by
    intro V hV
    unfold contS
    simp only [Real.rpow_one]
    have hderiv : ∀ x ∈ uIcc (0:ℝ) 1, HasDerivAt (fun x => V * Real.log (V + x)) (V / (V + x)) x := by
      intro x hx
      rw [Set.uIcc_of_le zero_le_one] at hx
      have hpos : (0:ℝ) < V + x := by linarith [hx.1]
      have h := (((hasDerivAt_id x).const_add V).log hpos.ne').const_mul V
      exact h.congr_deriv (by change V * (1 / (V + x)) = V / (V + x); ring)
    have hint : IntervalIntegrable (fun x => V / (V + x)) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const (continuousOn_const.add continuousOn_id)
      intro x hx
      rw [Set.uIcc_of_le zero_le_one] at hx
      exact (show (0:ℝ) < V + x by linarith [hx.1]).ne'
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    change V * Real.log (V + 1) - V * Real.log (V + 0) = V * Real.log (1 + 1 / V)
    rw [add_zero]
    rw [show (1 + 1 / V) = (V + 1) / V by field_simp, Real.log_div (by linarith) hV.ne']
    ring
  refine ⟨key, ?_⟩
  have hcongr : contS 1 =ᶠ[𝓝[>] (0:ℝ)] (fun V => V * Real.log (1 + 1 / V)) :=
    (eventually_mem_nhdsWithin).mono (fun V hV => key V hV)
  refine IsEquivalent.congr_left ?_ hcongr.symm
  have hlog : (fun V : ℝ => Real.log (1 + 1 / V)) ~[𝓝[>] (0:ℝ)] (fun V => Real.log (1 / V)) := by
    have h1 : Tendsto (fun V : ℝ => 1 + V) (𝓝[>] (0:ℝ)) (𝓝 1) := by
      have hc : Continuous (fun V : ℝ => 1 + V) := continuous_const.add continuous_id
      simpa using (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    have hB : Tendsto (fun V : ℝ => Real.log (1 + V)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa using h1.log one_ne_zero
    have hb : Tendsto (fun V : ℝ => -Real.log V) (𝓝[>] (0:ℝ)) atTop :=
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
    have hq : Tendsto (fun V : ℝ => Real.log (1 + V) / (-Real.log V)) (𝓝[>] (0:ℝ)) (𝓝 0) :=
      hB.div_atTop hb
    have hfinal : Tendsto (fun V : ℝ => 1 + Real.log (1 + V) / (-Real.log V)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
      simpa using tendsto_const_nhds.add hq
    refine isEquivalent_of_tendsto_one (hfinal.congr' ?_)
    filter_upwards [hb.eventually_gt_atTop 0, self_mem_nhdsWithin] with V hb0 hV
    have hV' : (0:ℝ) < V := hV
    have hne : -Real.log V ≠ 0 := hb0.ne'
    change 1 + Real.log (1 + V) / -Real.log V = Real.log (1 + 1 / V) / Real.log (1 / V)
    rw [one_div, Real.log_inv]
    have hVne : V ≠ 0 := hV'.ne'
    have hsplit : Real.log (1 + V⁻¹) = Real.log (1 + V) - Real.log V := by
      rw [show (1 + V⁻¹) = (1 + V) / V by field_simp; ring, Real.log_div (by linarith) hVne]
    rw [hsplit, eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne]
    ring
  exact (IsEquivalent.refl (u := fun V : ℝ => V)).mul hlog

/-- `lem:app-pl-continuum` (snapshot `cr-2026-10-23`), part (i), case `1 < α`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Continuum participation]\label{lem:app-pl-continuum}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item As $V\downarrow0$, $S_\alpha(V)\sim V/(1-\alpha)$ for $\alpha<1$, $S_1(V)=V\log(1+1/V)\sim V\log(1/V)$,
and $S_\alpha(V)\sim K_\alpha V^{1/\alpha}$ for $\alpha>1$. As $V\to\infty$, $1-S_\alpha(V)\sim((\alpha+1)V)^{-1}$.
\item $\mathsf T(V)\asymp S_\alpha(V)\big(1-S_\alpha(V)\big)$ for $V>0$.
\item As $p\downarrow0$, $V_\alpha(p)\sim(1-\alpha)p$ for $\alpha<1$, $V_1(p)\sim p/\log(1/p)$, and
$V_\alpha(p)\sim(p/K_\alpha)^\alpha$ for $\alpha>1$; and $V_\alpha(p)\asymp(1-p)^{-1}$ for $p\ge1/2$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_continuum_i_gt {α : ℝ} (hα1 : 1 < α) :
    IsEquivalent (𝓝[>] (0 : ℝ)) (contS α) (fun V => Kc α * V ^ (1 / α)) := by
  have hα0 : 0 < α := by linarith
  have hne : α ≠ 0 := hα0.ne'
  have hsinpos : 0 < Real.sin (Real.pi / α) := by
    apply Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos hα0)
    rw [div_lt_iff₀ hα0]
    nlinarith [Real.pi_pos]
  have hKc : 0 < Kc α := by
    unfold Kc
    exact div_pos Real.pi_pos (mul_pos hα0 hsinpos)
  have hb1 : 0 < 1 / α := one_div_pos.mpr hα0
  have hb2 : 0 < 1 - 1 / α := by
    have : 1 / α < 1 := by rw [div_lt_one hα0]; exact hα1
    linarith
  -- Beta integral on the half-line, then change of variables t = s^α
  have hJ : ∫ s in Ioi (0:ℝ), 1 / (1 + s ^ α) = Kc α := by
    unfold Kc
    have hb := Muon.Foundations.betaHalfLine hb1 hb2
    rw [show (1 / α + (1 - 1 / α)) = (1:ℝ) by ring] at hb
    simp only [Real.rpow_neg_one] at hb
    rw [Real.Gamma_one, div_one, Real.Gamma_mul_Gamma_one_sub, mul_one_div] at hb
    have hcv : ∫ x in Ioi (0:ℝ), (α * x ^ (α - 1)) • ((x ^ α) ^ (1 / α - 1) * (1 + x ^ α)⁻¹)
        = ∫ y in Ioi (0:ℝ), y ^ (1 / α - 1) * (1 + y)⁻¹ :=
      integral_comp_rpow_Ioi_of_pos (g := fun y : ℝ => y ^ (1 / α - 1) * (1 + y)⁻¹) hα0
    have hpt : ∀ x ∈ Ioi (0:ℝ), (α * x ^ (α - 1)) • ((x ^ α) ^ (1 / α - 1) * (1 + x ^ α)⁻¹)
        = α * (1 / (1 + x ^ α)) := by
      intro x hx
      have hx' : (0:ℝ) < x := hx
      have e1 : (x ^ α) ^ (1 / α - 1) = x ^ (1 - α) := by
        rw [← Real.rpow_mul hx'.le, mul_sub, mul_one_div_cancel hne, mul_one]
      have e2 : x ^ (α - 1) * x ^ (1 - α) = 1 := by
        rw [← Real.rpow_add hx', show α - 1 + (1 - α) = 0 by ring, Real.rpow_zero]
      rw [smul_eq_mul, e1]
      linear_combination (α * (1 + x ^ α)⁻¹) * e2
    have hcongr := setIntegral_congr_fun (μ := volume) measurableSet_Ioi hpt
    rw [hcv, integral_const_mul] at hcongr
    rw [hb] at hcongr
    have hsin : Real.sin (Real.pi / α) ≠ 0 := hsinpos.ne'
    field_simp at hcongr ⊢
    linarith
  have hint : IntegrableOn (fun s : ℝ => 1 / (1 + s ^ α)) (Ioi 0) := by
    by_contra hn
    rw [integral_undef hn] at hJ
    linarith
  -- scaling identity: contS V = V^{1/α} * ∫_0^{V^{-1/α}} 1/(1+s^α)
  have hB : ∀ V : ℝ, 0 < V → contS α V =
      (V ^ (-(1 / α)))⁻¹ * ∫ s in (0:ℝ)..V ^ (-(1 / α)), 1 / (1 + s ^ α) := by
    intro V hV
    have hc : 0 < V ^ (-(1 / α)) := Real.rpow_pos_of_pos hV _
    have hcα : (V ^ (-(1 / α))) ^ α = V⁻¹ := by
      rw [← Real.rpow_mul hV.le, show -(1 / α) * α = -1 by field_simp, Real.rpow_neg_one]
    have hrepr : contS α V = ∫ t in (0:ℝ)..1, 1 / (1 + (V ^ (-(1 / α)) * t) ^ α) := by
      unfold contS
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      change V / (V + t ^ α) = 1 / (1 + (V ^ (-(1 / α)) * t) ^ α)
      have h1 : V + t ^ α ≠ 0 := (add_pos_of_pos_of_nonneg hV (Real.rpow_nonneg ht.1 α)).ne'
      rw [Real.mul_rpow hc.le ht.1, hcα]
      field_simp
    have hcomp := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
      (fun s : ℝ => 1 / (1 + s ^ α)) hc.ne'
    simp only [mul_zero, mul_one, smul_eq_mul] at hcomp
    rw [hrepr, hcomp]
  have hinv : ∀ V : ℝ, 0 < V → (V ^ (-(1 / α)))⁻¹ = V ^ (1 / α) := by
    intro V hV
    rw [Real.rpow_neg hV.le, inv_inv]
  -- limit of the truncated integral as V -> 0+
  have hlimK : Tendsto (fun V : ℝ => ∫ s in (0:ℝ)..V ^ (-(1 / α)), 1 / (1 + s ^ α)) (𝓝[>] (0:ℝ))
      (𝓝 (∫ s in Ioi (0:ℝ), 1 / (1 + s ^ α))) :=
    intervalIntegral_tendsto_integral_Ioi 0 hint (tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos hb1))
  rw [hJ] at hlimK
  have hK2 : Tendsto (fun V : ℝ => (∫ s in (0:ℝ)..V ^ (-(1 / α)), 1 / (1 + s ^ α)) / Kc α)
      (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have := hlimK.div_const (Kc α)
    rwa [div_self hKc.ne'] at this
  refine isEquivalent_of_tendsto_one (hK2.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with V hV
  have hV' : (0:ℝ) < V := hV
  change (∫ s in (0:ℝ)..V ^ (-(1 / α)), 1 / (1 + s ^ α)) / Kc α = contS α V / (Kc α * V ^ (1 / α))
  rw [hB V hV', hinv V hV']
  have hpow : V ^ (1 / α) ≠ 0 := (Real.rpow_pos_of_pos hV' _).ne'
  have hKne : Kc α ≠ 0 := hKc.ne'
  field_simp

/-- `lem:app-pl-continuum` (snapshot `cr-2026-10-23`), part (i), the limit `V → ∞`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Continuum participation]\label{lem:app-pl-continuum}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item As $V\downarrow0$, $S_\alpha(V)\sim V/(1-\alpha)$ for $\alpha<1$, $S_1(V)=V\log(1+1/V)\sim V\log(1/V)$,
and $S_\alpha(V)\sim K_\alpha V^{1/\alpha}$ for $\alpha>1$. As $V\to\infty$, $1-S_\alpha(V)\sim((\alpha+1)V)^{-1}$.
\item $\mathsf T(V)\asymp S_\alpha(V)\big(1-S_\alpha(V)\big)$ for $V>0$.
\item As $p\downarrow0$, $V_\alpha(p)\sim(1-\alpha)p$ for $\alpha<1$, $V_1(p)\sim p/\log(1/p)$, and
$V_\alpha(p)\sim(p/K_\alpha)^\alpha$ for $\alpha>1$; and $V_\alpha(p)\asymp(1-p)^{-1}$ for $p\ge1/2$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_continuum_i_infty {α : ℝ} (hα0 : 0 < α) :
    IsEquivalent atTop (fun V => 1 - contS α V) (fun V => 1 / ((α + 1) * V)) := by
  have hS : ∀ V : ℝ, 0 < V → V * (1 - contS α V) = ∫ t in (0:ℝ)..1, V * (1 - V / (V + t ^ α)) := by
    intro V hV
    have hcont : ContinuousOn (fun t : ℝ => V + t ^ α) (uIcc 0 1) :=
      continuousOn_const.add (continuousOn_id.rpow_const (fun x _ => Or.inr hα0.le))
    have hint : IntervalIntegrable (fun t : ℝ => V / (V + t ^ α)) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const hcont
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      exact (add_pos_of_pos_of_nonneg hV (Real.rpow_nonneg ht.1 α)).ne'
    unfold contS
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub intervalIntegrable_const hint]
    simp
  have hpt : ∀ c : ℝ, 0 < c → Tendsto (fun V : ℝ => V * (1 - V / (V + c))) atTop (𝓝 c) := by
    intro c hc
    have h2 : Tendsto (fun V : ℝ => c / V) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have h3 : Tendsto (fun V : ℝ => 1 / (1 + c / V)) atTop (𝓝 (1 / (1 + 0))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.add h2) (by norm_num)
    have h1 : Tendsto (fun V : ℝ => V / (V + c)) atTop (𝓝 1) := by
      refine (by simpa using h3 : Tendsto (fun V : ℝ => 1 / (1 + c / V)) atTop (𝓝 1)).congr' ?_
      filter_upwards [eventually_gt_atTop 0] with V hV
      have hV' : (0:ℝ) < V := hV
      have : V ≠ 0 := hV'.ne'
      field_simp
    have h4 := (tendsto_const_nhds (x := c)).mul h1
    rw [mul_one] at h4
    refine h4.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with V hV
    have hV' : (0:ℝ) < V := hV
    have : V + c ≠ 0 := (by linarith : (0:ℝ) < V + c).ne'
    field_simp
    ring
  have hlim : Tendsto (fun V : ℝ => ∫ t in (0:ℝ)..1, V * (1 - V / (V + t ^ α))) atTop
      (𝓝 (∫ t in (0:ℝ)..1, t ^ α)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => t ^ α)
    · filter_upwards with V
      exact (by fun_prop : Measurable fun t : ℝ => V * (1 - V / (V + t ^ α))).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop 0] with V hV
      refine ae_of_all _ (fun t ht => ?_)
      rw [Set.uIoc_of_le zero_le_one] at ht
      have hc : 0 ≤ t ^ α := Real.rpow_nonneg ht.1.le α
      have hpos : 0 < V + t ^ α := by linarith
      have e : V * (1 - V / (V + t ^ α)) = V * t ^ α / (V + t ^ α) := by
        field_simp
        ring
      rw [e, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg hV.le hc) hpos.le),
        div_le_iff₀ hpos]
      nlinarith [mul_nonneg hc hc]
    · exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
    · refine ae_of_all _ (fun t ht => ?_)
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact hpt (t ^ α) (Real.rpow_pos_of_pos ht.1 α)
  have hI : ∫ t in (0:ℝ)..1, t ^ α = 1 / (α + 1) := by
    rw [integral_rpow (Or.inl (by linarith))]
    rw [Real.one_rpow, Real.zero_rpow (by linarith : α + 1 ≠ 0)]
    ring
  rw [hI] at hlim
  have hne : α + 1 ≠ 0 := (by linarith : (0:ℝ) < α + 1).ne'
  have hm := hlim.const_mul (α + 1)
  have h1 : (α + 1) * (1 / (α + 1)) = 1 := by field_simp
  rw [h1] at hm
  refine isEquivalent_of_tendsto_one (hm.congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with V hV
  have hV' : (0:ℝ) < V := hV
  have hVne : V ≠ 0 := hV'.ne'
  rw [← hS V hV']
  change (α + 1) * (V * (1 - contS α V)) = (1 - contS α V) / (1 / ((α + 1) * V))
  field_simp

private lemma pl_cont_s_contOn {α V : ℝ} (hα0 : 0 < α) (hV : 0 < V) :
    ContinuousOn (fun t : ℝ => V / (V + t ^ α)) (Set.uIcc 0 1) := by
  apply ContinuousOn.div continuousOn_const
  · exact (continuous_const.add (Real.continuous_rpow_const hα0.le)).continuousOn
  · intro t ht
    have ht' : (0:ℝ) ≤ t := (by rwa [Set.uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1)] at ht : t ∈ Set.Icc (0:ℝ) 1).1
    have h0 : 0 ≤ t ^ α := Real.rpow_nonneg ht' α
    exact (by linarith : (0:ℝ) < V + t ^ α).ne'

private lemma pl_cont_s_le_one {α V : ℝ} (hα0 : 0 < α) (hV : 0 < V) {t : ℝ} (ht : t ∈ Set.uIcc (0:ℝ) 1) :
    0 ≤ V / (V + t ^ α) ∧ V / (V + t ^ α) ≤ 1 := by
  have ht' : (0:ℝ) ≤ t := (by rwa [Set.uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1)] at ht : t ∈ Set.Icc (0:ℝ) 1).1
  have h0 : 0 ≤ t ^ α := Real.rpow_nonneg ht' α
  have hpos : (0:ℝ) < V + t ^ α := by linarith
  refine ⟨div_nonneg hV.le hpos.le, ?_⟩
  rw [div_le_one hpos]
  linarith

/-- Pointwise identity behind `T = ∫ s(1-s)`, `s = V/(V+t^α)`. -/
private lemma pl_T_integrand_eq {α V : ℝ} (hα0 : 0 < α) (hV : 0 < V) {t : ℝ}
    (ht : t ∈ Set.uIcc (0:ℝ) 1) :
    V * t ^ α / (V + t ^ α) ^ 2 = (V / (V + t ^ α)) * (1 - V / (V + t ^ α)) := by
  have ht' : (0:ℝ) ≤ t := (by rwa [Set.uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1)] at ht : t ∈ Set.Icc (0:ℝ) 1).1
  have h0 : 0 ≤ t ^ α := Real.rpow_nonneg ht' α
  have hpos : (0:ℝ) < V + t ^ α := by linarith
  field_simp
  ring

/-- Upper bounds `T ≤ S` and `T ≤ 1 - S` (from `0 ≤ s ≤ 1`). -/
private lemma pl_T_le_S_and_one_sub {α V : ℝ} (hα0 : 0 < α) (hV : 0 < V) :
    Tcont α V ≤ contS α V ∧ Tcont α V ≤ 1 - contS α V := by
  have hs : ContinuousOn (fun t : ℝ => V / (V + t ^ α)) (Set.uIcc 0 1) := pl_cont_s_contOn hα0 hV
  have hsint : IntervalIntegrable (fun t : ℝ => V / (V + t ^ α)) volume 0 1 :=
    hs.intervalIntegrable
  have hwint : IntervalIntegrable (fun t : ℝ => 1 - V / (V + t ^ α)) volume 0 1 :=
    (continuousOn_const.sub hs).intervalIntegrable
  have hprod : IntervalIntegrable (fun t : ℝ => (V / (V + t ^ α)) * (1 - V / (V + t ^ α)))
      volume 0 1 := (hs.mul (continuousOn_const.sub hs)).intervalIntegrable
  have hTeq : Tcont α V = ∫ t in (0:ℝ)..1, (V / (V + t ^ α)) * (1 - V / (V + t ^ α)) := by
    unfold Tcont
    apply intervalIntegral.integral_congr
    intro t ht
    exact pl_T_integrand_eq hα0 hV ht
  have h1 : ∫ t in (0:ℝ)..1, (1:ℝ) = 1 := by simp
  constructor
  · rw [hTeq]
    unfold contS
    apply intervalIntegral.integral_mono_on (zero_le_one : (0:ℝ) ≤ 1) hprod hsint
    intro t ht
    have hh := pl_cont_s_le_one hα0 hV (by rw [Set.uIcc_of_le zero_le_one]; exact ht)
    nlinarith [hh.1, hh.2]
  · rw [hTeq]
    have hsub : contS α V = ∫ t in (0:ℝ)..1, V / (V + t ^ α) := rfl
    have : 1 - contS α V = ∫ t in (0:ℝ)..1, (1 - V / (V + t ^ α)) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hsint, h1]
      rfl
    rw [this]
    apply intervalIntegral.integral_mono_on (zero_le_one : (0:ℝ) ≤ 1) hprod hwint
    intro t ht
    have hh := pl_cont_s_le_one hα0 hV (by rw [Set.uIcc_of_le zero_le_one]; exact ht)
    nlinarith [hh.1, hh.2]

/-- Lower bound `T ≥ (1 - S)/2` for `V ≥ 1` (there `s = V/(V+t^α) ≥ 1/2` on `[0,1]`). -/
private lemma pl_T_ge_half_one_sub {α V : ℝ} (hα0 : 0 < α) (hV1 : 1 ≤ V) :
    (1 - contS α V) / 2 ≤ Tcont α V := by
  have hs : ContinuousOn (fun t : ℝ => V / (V + t ^ α)) (Set.uIcc 0 1) := pl_cont_s_contOn hα0 (by linarith)
  have hsint : IntervalIntegrable (fun t : ℝ => V / (V + t ^ α)) volume 0 1 :=
    hs.intervalIntegrable
  have hwint : IntervalIntegrable (fun t : ℝ => (1 - V / (V + t ^ α)) / 2) volume 0 1 :=
    ((continuousOn_const.sub hs).div_const 2).intervalIntegrable
  have hprod : IntervalIntegrable (fun t : ℝ => (V / (V + t ^ α)) * (1 - V / (V + t ^ α)))
      volume 0 1 := (hs.mul (continuousOn_const.sub hs)).intervalIntegrable
  have hTeq : Tcont α V = ∫ t in (0:ℝ)..1, (V / (V + t ^ α)) * (1 - V / (V + t ^ α)) := by
    unfold Tcont
    apply intervalIntegral.integral_congr
    intro t ht
    exact pl_T_integrand_eq hα0 (by linarith) ht
  have hEq : (1 - contS α V) / 2 = ∫ t in (0:ℝ)..1, (1 - V / (V + t ^ α)) / 2 := by
    have hsub : 1 - contS α V = ∫ t in (0:ℝ)..1, (1 - V / (V + t ^ α)) := by
      unfold contS
      rw [intervalIntegral.integral_sub intervalIntegrable_const hsint]
      simp
    rw [hsub, intervalIntegral.integral_div]
  rw [hEq, hTeq]
  apply intervalIntegral.integral_mono_on (zero_le_one : (0:ℝ) ≤ 1) hwint hprod
  intro t ht
  have hh := pl_cont_s_le_one hα0 (by linarith : (0:ℝ) < V) (Set.Icc_subset_uIcc ht)
  have hta : t ^ α ≤ 1 := Real.rpow_le_one ht.1 ht.2 hα0.le
  have hhalf : 1 / 2 ≤ V / (V + t ^ α) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith [Real.rpow_nonneg ht.1 α])]
    linarith
  nlinarith [hh.1, hh.2]

private lemma pl_s_ii {α V a b : ℝ} (hα0 : 0 < α) (hV : 0 < V) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun t : ℝ => V / (V + t ^ α)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const
  · exact (continuous_const.add (Real.continuous_rpow_const hα0.le)).continuousOn
  · intro t ht
    have h : 0 ≤ t := by
      rcases le_total a b with h | h
      · rw [Set.uIcc_of_le h] at ht; exact ha.trans ht.1
      · rw [Set.uIcc_of_ge h] at ht; exact hb.trans ht.1
    have h0 := Real.rpow_nonneg h α
    exact (by linarith : (0:ℝ) < V + t ^ α).ne'

private lemma pl_u_ii {α V a b : ℝ} (hα0 : 0 < α) (hV : 0 < V) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun t : ℝ => t ^ α / (V + t ^ α)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div (Real.continuous_rpow_const hα0.le).continuousOn
  · exact (continuous_const.add (Real.continuous_rpow_const hα0.le)).continuousOn
  · intro t ht
    have h : 0 ≤ t := by
      rcases le_total a b with h | h
      · rw [Set.uIcc_of_le h] at ht; exact ha.trans ht.1
      · rw [Set.uIcc_of_ge h] at ht; exact hb.trans ht.1
    have h0 := Real.rpow_nonneg h α
    exact (by linarith : (0:ℝ) < V + t ^ α).ne'

private lemma pl_one_sub_eq {α V : ℝ} (hα0 : 0 < α) (hV : 0 < V) :
    1 - contS α V = ∫ t in (0:ℝ)..1, t ^ α / (V + t ^ α) := by
  have hsint := pl_s_ii hα0 hV (a := 0) (b := 1) le_rfl zero_le_one
  have h1 : ∫ t in (0:ℝ)..1, (1:ℝ) = 1 := by simp
  calc 1 - contS α V = (∫ t in (0:ℝ)..1, (1:ℝ)) - ∫ t in (0:ℝ)..1, V / (V + t ^ α) := by
        rw [h1]; rfl
    _ = ∫ t in (0:ℝ)..1, (1 - V / (V + t ^ α)) :=
        (intervalIntegral.integral_sub intervalIntegrable_const hsint).symm
    _ = _ := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : (0:ℝ) ≤ t := (by rwa [Set.uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1)] at ht : t ∈ Set.Icc (0:ℝ) 1).1
        have h0 : 0 ≤ t ^ α := Real.rpow_nonneg ht' α
        have hpos : (0:ℝ) < V + t ^ α := by linarith
        simp only
        field_simp
        ring

private lemma pl_int_rpow {α : ℝ} (hα0 : 0 < α) : ∫ t in (0:ℝ)..1, t ^ α = 1 / (α + 1) := by
  rw [integral_rpow (Or.inl (by linarith))]
  rw [Real.one_rpow, Real.zero_rpow (by linarith : α + 1 ≠ 0)]
  ring

private lemma pl_one_sub_le {α V : ℝ} (hα0 : 0 < α) (hV : 0 < V) :
    1 - contS α V ≤ 1 / ((α + 1) * V) := by
  rw [pl_one_sub_eq hα0 hV]
  have hI : ∫ t in (0:ℝ)..1, t ^ α / V = 1 / ((α + 1) * V) := by
    rw [intervalIntegral.integral_div, pl_int_rpow hα0]
    field_simp
  rw [← hI]
  apply intervalIntegral.integral_mono_on (zero_le_one : (0:ℝ) ≤ 1)
    (pl_u_ii hα0 hV le_rfl zero_le_one)
    ((intervalIntegral.intervalIntegrable_rpow' (by linarith)).div_const V)
  intro t ht
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg ht.1 α) hV (by linarith [Real.rpow_nonneg ht.1 α])

private lemma pl_one_sub_ge {α V : ℝ} (hα0 : 0 < α) (hV : 0 < V) :
    1 / (2 * (α + 1) * max V 1) ≤ 1 - contS α V := by
  rw [pl_one_sub_eq hα0 hV]
  have hM : (0:ℝ) < max V 1 := lt_max_of_lt_right one_pos
  have hI : ∫ t in (0:ℝ)..1, t ^ α / (2 * max V 1) = 1 / (2 * (α + 1) * max V 1) := by
    rw [intervalIntegral.integral_div, pl_int_rpow hα0]
    field_simp
  rw [← hI]
  apply intervalIntegral.integral_mono_on (zero_le_one : (0:ℝ) ≤ 1)
    ((intervalIntegral.intervalIntegrable_rpow' (by linarith)).div_const _)
    (pl_u_ii hα0 hV le_rfl zero_le_one)
  intro t ht
  have h0 := Real.rpow_nonneg ht.1 α
  have h1 : t ^ α ≤ 1 := Real.rpow_le_one ht.1 ht.2 hα0.le
  have h2 : V ≤ max V 1 := le_max_left _ _
  have h3 : (1:ℝ) ≤ max V 1 := le_max_right _ _
  exact div_le_div_of_nonneg_left h0 (by linarith) (by linarith)

private lemma pl_S_le {α V : ℝ} (hα0 : 0 < α) (hV : 0 < V) :
    contS α V ≤ 1 / 4 + V * (4:ℝ) ^ α := by
  have h1 := pl_s_ii hα0 hV (a := 0) (b := 1/4) le_rfl (by norm_num)
  have h2 := pl_s_ii hα0 hV (a := 1/4) (b := 1) (by norm_num) zero_le_one
  have hsplit : contS α V = (∫ t in (0:ℝ)..(1/4), V / (V + t ^ α)) +
      ∫ t in (1/4:ℝ)..1, V / (V + t ^ α) :=
    (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
  have hA : ∫ t in (0:ℝ)..(1/4), V / (V + t ^ α) ≤ 1 / 4 := by
    have := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1/4) h1
      (intervalIntegrable_const (c := (1:ℝ)))
      (fun t ht => (pl_cont_s_le_one hα0 hV (Set.Icc_subset_uIcc
        (by exact ⟨ht.1, by linarith [ht.2]⟩ : t ∈ Set.Icc (0:ℝ) 1))).2)
    simpa using this
  have hB : ∫ t in (1/4:ℝ)..1, V / (V + t ^ α) ≤ V * (4:ℝ) ^ α := by
    have := intervalIntegral.integral_mono_on (by norm_num : (1/4:ℝ) ≤ 1) h2
      (intervalIntegrable_const (c := V * (4:ℝ) ^ α))
      (fun t ht => by
        have h4 : ((1/4:ℝ)) ^ α ≤ t ^ α := Real.rpow_le_rpow (by norm_num) ht.1 hα0.le
        have h5 : ((1/4:ℝ)) ^ α = ((4:ℝ) ^ α)⁻¹ := by
          rw [one_div, Real.inv_rpow (by norm_num)]
        have h6 : (0:ℝ) < (4:ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
        have h7 : 0 ≤ t ^ α := Real.rpow_nonneg (by linarith [ht.1]) α
        calc V / (V + t ^ α) ≤ V / t ^ α := div_le_div_of_nonneg_left hV.le
              (lt_of_lt_of_le (by rw [h5]; positivity) h4) (by linarith)
          _ ≤ V / ((4:ℝ) ^ α)⁻¹ := by
              apply div_le_div_of_nonneg_left hV.le (by positivity); rw [← h5]; exact h4
          _ = V * (4:ℝ) ^ α := by rw [div_inv_eq_mul])
    have h8 : 0 ≤ V * (4:ℝ) ^ α := by positivity
    simp at this
    nlinarith
  linarith

private lemma pl_contS_nonneg {α V : ℝ} (hα0 : 0 < α) (hV : 0 < V) : 0 ≤ contS α V := by
  apply intervalIntegral.integral_nonneg zero_le_one
  intro t ht
  exact (pl_cont_s_le_one hα0 hV (Set.Icc_subset_uIcc ht)).1

private lemma pl_contS_lt_one {α V : ℝ} (hα0 : 0 < α) (hV : 0 < V) : contS α V < 1 := by
  have h := pl_one_sub_ge hα0 hV
  have : (0:ℝ) < 1 / (2 * (α + 1) * max V 1) :=
    one_div_pos.mpr (by have : (0:ℝ) < max V 1 := lt_max_of_lt_right one_pos; positivity)
  linarith

private lemma pl_contS_continuousOn {α ε : ℝ} (hα0 : 0 < α) (hε : 0 < ε) :
    ContinuousOn (contS α) (Set.Ici ε) := by
  have hc : Continuous fun V : ℝ => ∫ t in (0:ℝ)..1, V / (max V ε + |t| ^ α) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    have hden : Continuous fun p : ℝ × ℝ => max p.1 ε + |p.2| ^ α :=
      (continuous_fst.max continuous_const).add
        ((Real.continuous_rpow_const hα0.le).comp continuous_snd.abs)
    apply Continuous.div continuous_fst hden
    intro p
    have h1 : ε ≤ max p.1 ε := le_max_right _ _
    have h2 : 0 ≤ |p.2| ^ α := Real.rpow_nonneg (abs_nonneg _) α
    exact (by linarith : (0:ℝ) < max p.1 ε + |p.2| ^ α).ne'
  refine hc.continuousOn.congr ?_
  intro V hV
  have hV' : ε ≤ V := hV
  unfold contS
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : (0:ℝ) ≤ t := (by rwa [Set.uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1)] at ht : t ∈ Set.Icc (0:ℝ) 1).1
  simp only
  rw [max_eq_left hV', abs_of_nonneg ht']

private lemma pl_T_ge_m_one_sub {α V m : ℝ} (hα0 : 0 < α) (hV : 0 < V) (hm : 0 ≤ m)
    (hmV : m ≤ V / (V + 1)) : m * (1 - contS α V) ≤ Tcont α V := by
  have hs : ContinuousOn (fun t : ℝ => V / (V + t ^ α)) (Set.uIcc 0 1) := pl_cont_s_contOn hα0 hV
  have hsint : IntervalIntegrable (fun t : ℝ => V / (V + t ^ α)) volume 0 1 :=
    hs.intervalIntegrable
  have hwint : IntervalIntegrable (fun t : ℝ => m * (1 - V / (V + t ^ α))) volume 0 1 :=
    (continuousOn_const.mul (continuousOn_const.sub hs)).intervalIntegrable
  have hprod : IntervalIntegrable (fun t : ℝ => (V / (V + t ^ α)) * (1 - V / (V + t ^ α)))
      volume 0 1 := (hs.mul (continuousOn_const.sub hs)).intervalIntegrable
  have hTeq : Tcont α V = ∫ t in (0:ℝ)..1, (V / (V + t ^ α)) * (1 - V / (V + t ^ α)) := by
    unfold Tcont
    apply intervalIntegral.integral_congr
    intro t ht
    exact pl_T_integrand_eq hα0 hV ht
  have hEq : m * (1 - contS α V) = ∫ t in (0:ℝ)..1, m * (1 - V / (V + t ^ α)) := by
    have hsub : 1 - contS α V = ∫ t in (0:ℝ)..1, (1 - V / (V + t ^ α)) := by
      unfold contS
      rw [intervalIntegral.integral_sub intervalIntegrable_const hsint]
      simp
    rw [hsub, intervalIntegral.integral_const_mul]
  rw [hEq, hTeq]
  apply intervalIntegral.integral_mono_on (zero_le_one : (0:ℝ) ≤ 1) hwint hprod
  intro t ht
  have hh := pl_cont_s_le_one hα0 hV (Set.Icc_subset_uIcc ht)
  have hta : t ^ α ≤ 1 := Real.rpow_le_one ht.1 ht.2 hα0.le
  have ht0 := Real.rpow_nonneg ht.1 α
  have hge : V / (V + 1) ≤ V / (V + t ^ α) :=
    div_le_div_of_nonneg_left hV.le (by linarith) (by linarith)
  nlinarith [hh.1, hh.2]

/-- For `0 < a ≤ 1/2`: `S(a^α) ≤ 2(2+2^α) T(a^α)`. -/
private lemma pl_T_ge_small {α a : ℝ} (hα0 : 0 < α) (ha0 : 0 < a) (ha : a ≤ 1 / 2) :
    contS α (a ^ α) ≤ 2 * (2 + (2:ℝ) ^ α) * Tcont α (a ^ α) := by
  have hV : 0 < a ^ α := Real.rpow_pos_of_pos ha0 α
  set V := a ^ α with hVdef
  have hs01 := pl_s_ii hα0 hV (a := 0) (b := a) le_rfl ha0.le
  have hsa1 := pl_s_ii hα0 hV (a := a) (b := 1) ha0.le zero_le_one
  have hsa2 := pl_s_ii hα0 hV (a := a) (b := 2 * a) ha0.le (by linarith)
  have hs2a1 := pl_s_ii hα0 hV (a := 2 * a) (b := 1) (by linarith) zero_le_one
  have hs01' := pl_s_ii hα0 hV (a := 0) (b := 1) le_rfl zero_le_one
  have h2pos : (0:ℝ) < 2 ^ α := Real.rpow_pos_of_pos (by norm_num) α
  -- S = ∫_0^a + ∫_a^1
  have hS : contS α V = (∫ t in (0:ℝ)..a, V / (V + t ^ α)) + ∫ t in a..1, V / (V + t ^ α) :=
    (intervalIntegral.integral_add_adjacent_intervals hs01 hsa1).symm
  have hA : ∫ t in (0:ℝ)..a, V / (V + t ^ α) ≤ a := by
    have := intervalIntegral.integral_mono_on ha0.le hs01
      (intervalIntegrable_const (c := (1:ℝ)))
      (fun t ht => (pl_cont_s_le_one hα0 hV (Set.Icc_subset_uIcc
        (by exact ⟨ht.1, by linarith [ht.2]⟩ : t ∈ Set.Icc (0:ℝ) 1))).2)
    simpa using this
  -- J ≥ a/(1+2^α)
  have hJ : a / (1 + 2 ^ α) ≤ ∫ t in a..1, V / (V + t ^ α) := by
    have hsplit : ∫ t in a..1, V / (V + t ^ α) = (∫ t in a..(2 * a), V / (V + t ^ α)) +
        ∫ t in (2 * a)..1, V / (V + t ^ α) :=
      (intervalIntegral.integral_add_adjacent_intervals hsa2 hs2a1).symm
    have h1 : ∫ t in (2 * a)..1, V / (V + t ^ α) ≥ 0 := by
      apply intervalIntegral.integral_nonneg (by linarith)
      intro t ht
      exact (pl_cont_s_le_one hα0 hV (Set.Icc_subset_uIcc
        (by exact ⟨by linarith [ht.1], ht.2⟩ : t ∈ Set.Icc (0:ℝ) 1))).1
    have h2 := intervalIntegral.integral_mono_on (by linarith : a ≤ 2 * a)
      (intervalIntegrable_const (c := 1 / (1 + (2:ℝ) ^ α))) hsa2
      (fun t ht => by
        have ht0 : 0 ≤ t := by linarith [ht.1]
        have h3 : t ^ α ≤ (2 * a) ^ α := Real.rpow_le_rpow ht0 ht.2 hα0.le
        have h4 : (2 * a) ^ α = 2 ^ α * V := by
          rw [Real.mul_rpow (by norm_num) ha0.le]
        have h0 := Real.rpow_nonneg ht0 α
        calc 1 / (1 + (2:ℝ) ^ α) = V / (V + 2 ^ α * V) := by field_simp
          _ ≤ V / (V + t ^ α) :=
            div_le_div_of_nonneg_left hV.le (by linarith) (by linarith))
    have h5 : ∫ t in a..(2 * a), (1 / (1 + (2:ℝ) ^ α)) = a / (1 + 2 ^ α) := by
      simp
      ring
    linarith
  -- T ≥ J/2
  have hTeq : Tcont α V = ∫ t in (0:ℝ)..1, (V / (V + t ^ α)) * (1 - V / (V + t ^ α)) := by
    unfold Tcont
    apply intervalIntegral.integral_congr
    intro t ht
    exact pl_T_integrand_eq hα0 hV ht
  have hf01 : IntervalIntegrable (fun t : ℝ => (V / (V + t ^ α)) * (1 - V / (V + t ^ α)))
      volume 0 1 := by
    have hs : ContinuousOn (fun t : ℝ => V / (V + t ^ α)) (Set.uIcc 0 1) := pl_cont_s_contOn hα0 hV
    exact (hs.mul (continuousOn_const.sub hs)).intervalIntegrable
  have hf0a : IntervalIntegrable (fun t : ℝ => (V / (V + t ^ α)) * (1 - V / (V + t ^ α)))
      volume 0 a := hf01.mono_set (by
        rw [Set.uIcc_of_le ha0.le, Set.uIcc_of_le zero_le_one]
        exact Set.Icc_subset_Icc le_rfl (by linarith))
  have hfa1 : IntervalIntegrable (fun t : ℝ => (V / (V + t ^ α)) * (1 - V / (V + t ^ α)))
      volume a 1 := hf01.mono_set (by
        rw [Set.uIcc_of_le (by linarith : a ≤ 1), Set.uIcc_of_le zero_le_one]
        exact Set.Icc_subset_Icc ha0.le le_rfl)
  have hT : Tcont α V = (∫ t in (0:ℝ)..a, (V / (V + t ^ α)) * (1 - V / (V + t ^ α))) +
      ∫ t in a..1, (V / (V + t ^ α)) * (1 - V / (V + t ^ α)) := by
    rw [hTeq]; exact (intervalIntegral.integral_add_adjacent_intervals hf0a hfa1).symm
  have hT0 : 0 ≤ ∫ t in (0:ℝ)..a, (V / (V + t ^ α)) * (1 - V / (V + t ^ α)) := by
    apply intervalIntegral.integral_nonneg ha0.le
    intro t ht
    have hh := pl_cont_s_le_one hα0 hV (Set.Icc_subset_uIcc
        (by exact ⟨ht.1, by linarith [ht.2]⟩ : t ∈ Set.Icc (0:ℝ) 1))
    exact mul_nonneg hh.1 (by linarith [hh.2])
  have hT1 : (∫ t in a..1, V / (V + t ^ α)) / 2 ≤
      ∫ t in a..1, (V / (V + t ^ α)) * (1 - V / (V + t ^ α)) := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_mono_on (by linarith : a ≤ 1) (hsa1.div_const 2) hfa1
    intro t ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have hh := pl_cont_s_le_one hα0 hV (Set.Icc_subset_uIcc
        (by exact ⟨ht0, ht.2⟩ : t ∈ Set.Icc (0:ℝ) 1))
    have h3 : V ≤ t ^ α := Real.rpow_le_rpow ha0.le ht.1 hα0.le
    have hhalf : V / (V + t ^ α) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith [Real.rpow_nonneg ht0 α]) (by norm_num)]
      linarith
    nlinarith [hh.1, hh.2]
  have hJp : 0 ≤ ∫ t in a..1, V / (V + t ^ α) := by linarith [hJ, div_nonneg ha0.le (by linarith : (0:ℝ) ≤ 1 + 2 ^ α)]
  -- combine: a ≤ (1+2^α) J
  have hJ' : a ≤ (1 + 2 ^ α) * ∫ t in a..1, V / (V + t ^ α) := by
    rw [div_le_iff₀ (by linarith)] at hJ
    linarith
  set J := ∫ t in a..1, V / (V + t ^ α)
  have : contS α V ≤ (2 + 2 ^ α) * J := by nlinarith
  nlinarith

private lemma pl_T_upper {α V : ℝ} (hα0 : 0 < α) (hV : 0 < V) :
    Tcont α V ≤ 2 * (contS α V * (1 - contS α V)) := by
  obtain ⟨h1, h2⟩ := pl_T_le_S_and_one_sub hα0 hV
  have h3 := pl_contS_nonneg hα0 hV
  have h4 := pl_contS_lt_one hα0 hV
  rcases le_total (contS α V) (1 / 2) with h | h
  · nlinarith
  · nlinarith

/-- `lem:app-pl-continuum` (snapshot `cr-2026-10-23`), part (ii), two-sided `≍` on `(0,∞)`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Continuum participation]\label{lem:app-pl-continuum}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item As $V\downarrow0$, $S_\alpha(V)\sim V/(1-\alpha)$ for $\alpha<1$, $S_1(V)=V\log(1+1/V)\sim V\log(1/V)$,
and $S_\alpha(V)\sim K_\alpha V^{1/\alpha}$ for $\alpha>1$. As $V\to\infty$, $1-S_\alpha(V)\sim((\alpha+1)V)^{-1}$.
\item $\mathsf T(V)\asymp S_\alpha(V)\big(1-S_\alpha(V)\big)$ for $V>0$.
\item As $p\downarrow0$, $V_\alpha(p)\sim(1-\alpha)p$ for $\alpha<1$, $V_1(p)\sim p/\log(1/p)$, and
$V_\alpha(p)\sim(p/K_\alpha)^\alpha$ for $\alpha>1$; and $V_\alpha(p)\asymp(1-p)^{-1}$ for $p\ge1/2$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_continuum_ii {α : ℝ} (hα0 : 0 < α) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ V : ℝ, 0 < V →
      c * (contS α V * (1 - contS α V)) ≤ Tcont α V ∧
        Tcont α V ≤ C * (contS α V * (1 - contS α V)) := by
  have h2pos : (0:ℝ) < 2 ^ α := Real.rpow_pos_of_pos (by norm_num) α
  have hK : (0:ℝ) < 2 * (2 + (2:ℝ) ^ α) := by positivity
  set v0 : ℝ := (1 / 2 : ℝ) ^ α with hv0
  have hv0pos : 0 < v0 := Real.rpow_pos_of_pos (by norm_num) α
  set m : ℝ := v0 / (v0 + 1) with hm
  have hmpos : 0 < m := by positivity
  refine ⟨min (1 / (2 * (2 + (2:ℝ) ^ α))) m, 2, lt_min (by positivity) hmpos, by norm_num, ?_⟩
  intro V hV
  have hS0 := pl_contS_nonneg hα0 hV
  have hS1 := pl_contS_lt_one hα0 hV
  refine ⟨?_, by linarith [pl_T_upper hα0 hV]⟩
  have hprod_le : contS α V * (1 - contS α V) ≤ contS α V := by nlinarith
  rcases lt_or_ge V v0 with hlt | hge
  · -- small V
    set a : ℝ := V ^ (1 / α) with ha
    have hapos : 0 < a := Real.rpow_pos_of_pos hV _
    have haV : a ^ α = V := by
      rw [ha, ← Real.rpow_mul hV.le, one_div_mul_cancel hα0.ne', Real.rpow_one]
    have ha2 : a ≤ 1 / 2 := by
      by_contra hcon
      push_neg at hcon
      have : v0 < a ^ α := Real.rpow_lt_rpow (by norm_num) hcon hα0
      linarith
    have key := pl_T_ge_small hα0 hapos ha2
    rw [haV] at key
    calc min (1 / (2 * (2 + (2:ℝ) ^ α))) m * (contS α V * (1 - contS α V))
        ≤ (1 / (2 * (2 + (2:ℝ) ^ α))) * contS α V := by
          apply mul_le_mul (min_le_left _ _) hprod_le (by nlinarith) (by positivity)
      _ ≤ Tcont α V := by
          rw [one_div, inv_mul_le_iff₀ hK]; linarith
  · -- large V
    have hmV : m ≤ V / (V + 1) := by
      rw [hm, div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    have := pl_T_ge_m_one_sub hα0 hV hmpos.le hmV
    calc min (1 / (2 * (2 + (2:ℝ) ^ α))) m * (contS α V * (1 - contS α V))
        ≤ m * (1 - contS α V) := by
          have h1 : min (1 / (2 * (2 + (2:ℝ) ^ α))) m ≤ m := min_le_right _ _
          have h2 : contS α V * (1 - contS α V) ≤ 1 - contS α V := by nlinarith
          have h3 : 0 ≤ min (1 / (2 * (2 + (2:ℝ) ^ α))) m :=
            (lt_min (by positivity) hmpos).le
          calc _ ≤ m * (contS α V * (1 - contS α V)) :=
                mul_le_mul_of_nonneg_right h1 (by nlinarith)
            _ ≤ m * (1 - contS α V) := mul_le_mul_of_nonneg_left h2 hmpos.le
      _ ≤ Tcont α V := this

/-! ### Helpers for the inversions `V_α = S_α^{-1}` (part (iii)) -/

private lemma pl_contS_pos {α V : ℝ} (hα0 : 0 < α) (hV : 0 < V) : 0 < contS α V := by
  unfold contS
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (pl_cont_s_contOn hα0 hV).intervalIntegrable ?_ zero_lt_one
  intro t ht
  have h0 : 0 ≤ t ^ α := Real.rpow_nonneg ht.1.le α
  exact div_pos hV (by linarith)

private lemma pl_contS_monotoneOn {α : ℝ} (hα0 : 0 < α) :
    MonotoneOn (contS α) (Set.Ioi 0) := by
  intro V hV W hW hVW
  have hV' : (0:ℝ) < V := Set.mem_Ioi.1 hV
  have hW' : (0:ℝ) < W := Set.mem_Ioi.1 hW
  show contS α V ≤ contS α W
  unfold contS
  apply intervalIntegral.integral_mono_on zero_le_one
  · exact (pl_cont_s_contOn hα0 hV').intervalIntegrable
  · exact (pl_cont_s_contOn hα0 hW').intervalIntegrable
  · intro t ht
    have h0 : 0 ≤ t ^ α := Real.rpow_nonneg ht.1 α
    have h1 : 0 < V + t ^ α := by linarith
    have h2 : 0 < W + t ^ α := by linarith
    rw [div_le_div_iff₀ h1 h2]
    nlinarith [mul_le_mul_of_nonneg_right hVW h0]

private lemma pl_small_mem_image {α : ℝ} (hα0 : 0 < α)
    (hS0 : Tendsto (contS α) (𝓝[>] (0:ℝ)) (𝓝 0)) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ contS α 1) :
    p ∈ contS α '' Set.Ioi 0 := by
  have hev : ∀ᶠ a in 𝓝[>] (0:ℝ), contS α a < p := hS0.eventually (gt_mem_nhds hp)
  obtain ⟨a, ha1, ha2⟩ := (hev.and (Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1))).exists
  obtain ⟨V, hV, hVp⟩ := intermediate_value_Icc ha2.2.le
    ((pl_contS_continuousOn hα0 ha2.1).mono Set.Icc_subset_Ici_self)
    (⟨ha1.le, hp1⟩ : p ∈ Set.Icc (contS α a) (contS α 1))
  exact ⟨V, lt_of_lt_of_le ha2.1 hV.1, hVp⟩

private lemma pl_contV_spec {α p : ℝ} (hp : p ∈ contS α '' Set.Ioi 0) :
    0 < contV α p ∧ contS α (contV α p) = p := by
  have h : ∃ a ∈ Set.Ioi (0:ℝ), contS α a = p := hp
  exact ⟨Set.mem_Ioi.1 (Function.invFunOn_mem h), Function.invFunOn_eq h⟩

private lemma pl_contV_tendsto {α : ℝ} (hα0 : 0 < α)
    (hS0 : Tendsto (contS α) (𝓝[>] (0:ℝ)) (𝓝 0)) :
    Tendsto (contV α) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
  have hpos : ∀ᶠ p in 𝓝[>] (0:ℝ), 0 < contV α p ∧ contS α (contV α p) = p := by
    filter_upwards [Ioo_mem_nhdsGT (pl_contS_pos hα0 (zero_lt_one : (0:ℝ) < 1))] with p hp
    exact pl_contV_spec (pl_small_mem_image hα0 hS0 hp.1 hp.2.le)
  refine tendsto_nhdsWithin_iff.2 ⟨?_, hpos.mono fun p hp => hp.1⟩
  rw [tendsto_order]
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · filter_upwards [hpos] with p hp
    linarith [hp.1]
  · filter_upwards [hpos, Ioo_mem_nhdsGT (pl_contS_pos hα0 (half_pos hc))] with p hp hp2
    by_contra hcon
    push_neg at hcon
    have hmono := pl_contS_monotoneOn hα0 (Set.mem_Ioi.2 (half_pos hc))
      (Set.mem_Ioi.2 hp.1) (by linarith : c / 2 ≤ contV α p)
    rw [hp.2] at hmono
    linarith [hp2.2]

/-- Generic inversion step: if `S_α ~ g` at `0⁺`, then `p / g(V_α(p)) → 1`. -/
private lemma pl_contV_ratio {α : ℝ} (hα0 : 0 < α) {g : ℝ → ℝ}
    (hS : IsEquivalent (𝓝[>] (0:ℝ)) (contS α) g) (hg : Tendsto g (𝓝[>] (0:ℝ)) (𝓝 0))
    (hgne : ∀ᶠ V in 𝓝[>] (0:ℝ), g V ≠ 0) :
    Tendsto (fun p => p / g (contV α p)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hS0 : Tendsto (contS α) (𝓝[>] (0:ℝ)) (𝓝 0) := hS.symm.tendsto_nhds hg
  have hratio : Tendsto (fun V => contS α V / g V) (𝓝[>] (0:ℝ)) (𝓝 1) :=
    (isEquivalent_iff_tendsto_one hgne).1 hS
  have hVt := pl_contV_tendsto hα0 hS0
  have hSV : ∀ᶠ p in 𝓝[>] (0:ℝ), contS α (contV α p) = p := by
    filter_upwards [Ioo_mem_nhdsGT (pl_contS_pos hα0 (zero_lt_one : (0:ℝ) < 1))] with p hp
    exact (pl_contV_spec (pl_small_mem_image hα0 hS0 hp.1 hp.2.le)).2
  refine (hratio.comp hVt).congr' ?_
  filter_upwards [hSV] with p hp
  simp only [Function.comp_apply, hp]

/-- `lem:app-pl-continuum` (snapshot `cr-2026-10-23`), part (iii), case `0 < α < 1`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Continuum participation]\label{lem:app-pl-continuum}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item As $V\downarrow0$, $S_\alpha(V)\sim V/(1-\alpha)$ for $\alpha<1$, $S_1(V)=V\log(1+1/V)\sim V\log(1/V)$,
and $S_\alpha(V)\sim K_\alpha V^{1/\alpha}$ for $\alpha>1$. As $V\to\infty$, $1-S_\alpha(V)\sim((\alpha+1)V)^{-1}$.
\item $\mathsf T(V)\asymp S_\alpha(V)\big(1-S_\alpha(V)\big)$ for $V>0$.
\item As $p\downarrow0$, $V_\alpha(p)\sim(1-\alpha)p$ for $\alpha<1$, $V_1(p)\sim p/\log(1/p)$, and
$V_\alpha(p)\sim(p/K_\alpha)^\alpha$ for $\alpha>1$; and $V_\alpha(p)\asymp(1-p)^{-1}$ for $p\ge1/2$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_continuum_iii_lt {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    IsEquivalent (𝓝[>] (0 : ℝ)) (contV α) (fun p => (1 - α) * p) := by
  have hα1' : (0:ℝ) < 1 - α := by linarith
  have hS := lem_app_pl_continuum_i_lt hα0 hα1
  have hg : Tendsto (fun V : ℝ => V / (1 - α)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc : Continuous fun V : ℝ => V / (1 - α) := continuous_id.div_const _
    have h := (hc.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa using h
  have hgne : ∀ᶠ V in 𝓝[>] (0:ℝ), V / (1 - α) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with V hV
    exact (div_pos (Set.mem_Ioi.1 hV) hα1').ne'
  have key := pl_contV_ratio hα0 hS hg hgne
  beta_reduce at key
  refine isEquivalent_of_tendsto_one ?_
  have h2 := key.inv₀ one_ne_zero
  rw [inv_one] at h2
  refine h2.congr (fun p => ?_)
  simp only [Pi.div_apply, inv_div, div_div]

/-- `lem:app-pl-continuum` (snapshot `cr-2026-10-23`), part (iii), case `α = 1`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Continuum participation]\label{lem:app-pl-continuum}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item As $V\downarrow0$, $S_\alpha(V)\sim V/(1-\alpha)$ for $\alpha<1$, $S_1(V)=V\log(1+1/V)\sim V\log(1/V)$,
and $S_\alpha(V)\sim K_\alpha V^{1/\alpha}$ for $\alpha>1$. As $V\to\infty$, $1-S_\alpha(V)\sim((\alpha+1)V)^{-1}$.
\item $\mathsf T(V)\asymp S_\alpha(V)\big(1-S_\alpha(V)\big)$ for $V>0$.
\item As $p\downarrow0$, $V_\alpha(p)\sim(1-\alpha)p$ for $\alpha<1$, $V_1(p)\sim p/\log(1/p)$, and
$V_\alpha(p)\sim(p/K_\alpha)^\alpha$ for $\alpha>1$; and $V_\alpha(p)\asymp(1-p)^{-1}$ for $p\ge1/2$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_continuum_iii_one :
    IsEquivalent (𝓝[>] (0 : ℝ)) (contV 1) (fun p => p / Real.log (1 / p)) := by
  have hα0 : (0:ℝ) < 1 := zero_lt_one
  have hS := lem_app_pl_continuum_i_one.2
  have hgt : Tendsto (fun V : ℝ => V * Real.log (1 / V)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun V : ℝ => V * Real.log V) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have := (Real.continuous_mul_log.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa using this
    have h2 := h1.neg
    rw [neg_zero] at h2
    refine h2.congr (fun V => ?_)
    rw [one_div, Real.log_inv]
    ring
  have hgne : ∀ᶠ V in 𝓝[>] (0:ℝ), V * Real.log (1 / V) ≠ 0 := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with V hV
    exact (mul_pos hV.1 (Real.log_pos (one_lt_one_div hV.1 hV.2))).ne'
  have key := pl_contV_ratio hα0 hS hgt hgne
  beta_reduce at key
  have hVt := pl_contV_tendsto hα0 (hS.symm.tendsto_nhds hgt)
  have hVpos : ∀ᶠ p in 𝓝[>] (0:ℝ), 0 < contV 1 p := hVt.eventually self_mem_nhdsWithin
  have hy : Tendsto (fun p => Real.log (1 / contV 1 p)) (𝓝[>] (0:ℝ)) atTop := by
    have h1 := tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hVt)
    refine h1.congr (fun p => ?_)
    simp [Function.comp, one_div, Real.log_inv]
  have hlogy : Tendsto (fun p => Real.log (Real.log (1 / contV 1 p)) / Real.log (1 / contV 1 p))
      (𝓝[>] (0:ℝ)) (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hy
  have hr := key.log one_ne_zero
  rw [Real.log_one] at hr
  have hid : ∀ᶠ p in 𝓝[>] (0:ℝ), Real.log (1 / p) = Real.log (1 / contV 1 p)
      - Real.log (Real.log (1 / contV 1 p))
      - Real.log (p / (contV 1 p * Real.log (1 / contV 1 p))) := by
    filter_upwards [self_mem_nhdsWithin, hVpos, hy.eventually_gt_atTop 0] with p hp hV hyp
    have hp0 : 0 < p := Set.mem_Ioi.1 hp
    have e1 : Real.log (1 / p) = -Real.log p := by rw [one_div, Real.log_inv]
    have e2 : Real.log (1 / contV 1 p) = -Real.log (contV 1 p) := by rw [one_div, Real.log_inv]
    rw [e1, Real.log_div hp0.ne' (mul_pos hV hyp).ne', Real.log_mul hV.ne' hyp.ne', e2]
    ring
  have hfin : Tendsto (fun p => Real.log (1 / p) / Real.log (1 / contV 1 p))
      (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have h3 := (tendsto_const_nhds (x := (1:ℝ))).sub hlogy |>.sub (hr.div_atTop hy)
    rw [sub_zero, sub_zero] at h3
    refine h3.congr' ?_
    filter_upwards [hid, hy.eventually_gt_atTop 0] with p hidp hyp
    have hyne : Real.log (1 / contV 1 p) ≠ 0 := hyp.ne'
    rw [hidp]
    field_simp
  have h5 := hfin.mul (key.inv₀ one_ne_zero)
  rw [inv_one, mul_one] at h5
  refine isEquivalent_of_tendsto_one (h5.congr' ?_)
  filter_upwards [hy.eventually_gt_atTop 0, self_mem_nhdsWithin] with p hyp hp
  have hp0 : p ≠ 0 := (Set.mem_Ioi.1 hp).ne'
  have hyne : Real.log (1 / contV 1 p) ≠ 0 := hyp.ne'
  simp only [Pi.div_apply, inv_div]
  rw [div_div_eq_mul_div]
  field_simp

/-- `lem:app-pl-continuum` (snapshot `cr-2026-10-23`), part (iii), case `1 < α`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Continuum participation]\label{lem:app-pl-continuum}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item As $V\downarrow0$, $S_\alpha(V)\sim V/(1-\alpha)$ for $\alpha<1$, $S_1(V)=V\log(1+1/V)\sim V\log(1/V)$,
and $S_\alpha(V)\sim K_\alpha V^{1/\alpha}$ for $\alpha>1$. As $V\to\infty$, $1-S_\alpha(V)\sim((\alpha+1)V)^{-1}$.
\item $\mathsf T(V)\asymp S_\alpha(V)\big(1-S_\alpha(V)\big)$ for $V>0$.
\item As $p\downarrow0$, $V_\alpha(p)\sim(1-\alpha)p$ for $\alpha<1$, $V_1(p)\sim p/\log(1/p)$, and
$V_\alpha(p)\sim(p/K_\alpha)^\alpha$ for $\alpha>1$; and $V_\alpha(p)\asymp(1-p)^{-1}$ for $p\ge1/2$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_continuum_iii_gt {α : ℝ} (hα1 : 1 < α) :
    IsEquivalent (𝓝[>] (0 : ℝ)) (contV α) (fun p => (p / Kc α) ^ α) := by
  have hα0 : (0:ℝ) < α := by linarith
  have hKc : 0 < Kc α := by
    unfold Kc
    have hsin : 0 < Real.sin (Real.pi / α) :=
      Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos hα0) (div_lt_self Real.pi_pos hα1)
    exact div_pos Real.pi_pos (mul_pos hα0 hsin)
  have hS := lem_app_pl_continuum_i_gt hα1
  have hg : Tendsto (fun V : ℝ => Kc α * V ^ (1 / α)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc : Continuous fun V : ℝ => Kc α * V ^ (1 / α) :=
      continuous_const.mul (Real.continuous_rpow_const (one_div_pos.2 hα0).le)
    have h : Tendsto (fun V : ℝ => Kc α * V ^ (1 / α)) (𝓝[>] (0:ℝ)) (𝓝 (Kc α * (0:ℝ) ^ (1 / α))) :=
      (hc.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    rwa [Real.zero_rpow (one_div_ne_zero hα0.ne'), mul_zero] at h
  have hgne : ∀ᶠ V in 𝓝[>] (0:ℝ), Kc α * V ^ (1 / α) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with V hV
    exact (mul_pos hKc (Real.rpow_pos_of_pos (Set.mem_Ioi.1 hV) _)).ne'
  have key := pl_contV_ratio hα0 hS hg hgne
  beta_reduce at key
  have hVt := pl_contV_tendsto hα0 (hS.symm.tendsto_nhds hg)
  have hVpos : ∀ᶠ p in 𝓝[>] (0:ℝ), 0 < contV α p := hVt.eventually self_mem_nhdsWithin
  refine isEquivalent_of_tendsto_one ?_
  have h1' := key.rpow_const (p := α) (Or.inl one_ne_zero)
  rw [Real.one_rpow] at h1'
  have h2 := h1'.inv₀ one_ne_zero
  rw [inv_one] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hVpos] with p hp hV
  have hp0 : 0 < p := Set.mem_Ioi.1 hp
  have hW : 0 < contV α p ^ (1 / α) := Real.rpow_pos_of_pos hV _
  have hWα : (contV α p ^ (1 / α)) ^ α = contV α p := by
    rw [one_div]
    exact Real.rpow_inv_rpow hV.le hα0.ne'
  have hpa : 0 < p ^ α := Real.rpow_pos_of_pos hp0 α
  have hKa : 0 < Kc α ^ α := Real.rpow_pos_of_pos hKc α
  simp only [Pi.div_apply]
  rw [Real.div_rpow hp0.le (mul_nonneg hKc.le hW.le) α, Real.mul_rpow hKc.le hW.le, hWα,
    Real.div_rpow hp0.le hKc.le α]
  field_simp

/-- `lem:app-pl-continuum` (snapshot `cr-2026-10-23`), part (iii), the two-sided bound `V_α(p) ≍ (1-p)^{-1}` for `p ≥ 1/2`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Continuum participation]\label{lem:app-pl-continuum}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item As $V\downarrow0$, $S_\alpha(V)\sim V/(1-\alpha)$ for $\alpha<1$, $S_1(V)=V\log(1+1/V)\sim V\log(1/V)$,
and $S_\alpha(V)\sim K_\alpha V^{1/\alpha}$ for $\alpha>1$. As $V\to\infty$, $1-S_\alpha(V)\sim((\alpha+1)V)^{-1}$.
\item $\mathsf T(V)\asymp S_\alpha(V)\big(1-S_\alpha(V)\big)$ for $V>0$.
\item As $p\downarrow0$, $V_\alpha(p)\sim(1-\alpha)p$ for $\alpha<1$, $V_1(p)\sim p/\log(1/p)$, and
$V_\alpha(p)\sim(p/K_\alpha)^\alpha$ for $\alpha>1$; and $V_\alpha(p)\asymp(1-p)^{-1}$ for $p\ge1/2$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_continuum_iii_half {α : ℝ} (hα0 : 0 < α) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ p : ℝ, 1 / 2 ≤ p → p < 1 →
      c / (1 - p) ≤ contV α p ∧ contV α p ≤ C / (1 - p) := by
  
  have h4pos : (0:ℝ) < (4:ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  have h4ge : (1:ℝ) ≤ (4:ℝ) ^ α := Real.one_le_rpow (by norm_num) hα0.le
  have hα1 : (0:ℝ) < α + 1 := by linarith
  set w : ℝ := ((4:ℝ) ^ α)⁻¹ / 4 with hw
  have hwpos : 0 < w := by positivity
  have hw1 : w ≤ 1 := by
    rw [hw, div_le_one (by norm_num)]
    have : ((4:ℝ) ^ α)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h4ge
    linarith
  have hwS : contS α w ≤ 1 / 2 := by
    have := pl_S_le hα0 hwpos
    have e : w * (4:ℝ) ^ α = 1 / 4 := by
      rw [hw]; field_simp
    linarith
  set κ : ℝ := 1 / (2 * (α + 1)) with hκ
  have hκpos : 0 < κ := by positivity
  refine ⟨w * κ, 1 / (α + 1), by positivity, by positivity, ?_⟩
  intro p hp1 hp2
  have hp : 0 < 1 - p := by linarith
  -- existence of a preimage
  set V2 : ℝ := max (1 / ((α + 1) * (1 - p))) 1 with hV2
  have hV2pos : 0 < V2 := lt_max_of_lt_right one_pos
  have hwV2 : w ≤ V2 := by
    have : (1:ℝ) ≤ V2 := le_max_right _ _
    linarith
  have hSV2 : p ≤ contS α V2 := by
    have h1 := pl_one_sub_le hα0 hV2pos
    have h2 : 1 / ((α + 1) * V2) ≤ 1 - p := by
      rw [div_le_iff₀ (by positivity)]
      have h3 : 1 / ((α + 1) * (1 - p)) ≤ V2 := le_max_left _ _
      rw [div_le_iff₀ (by positivity)] at h3
      nlinarith
    linarith
  have hex : ∃ V ∈ Set.Ioi (0:ℝ), contS α V = p := by
    have hcont : ContinuousOn (contS α) (Set.Icc w V2) :=
      (pl_contS_continuousOn hα0 hwpos).mono Set.Icc_subset_Ici_self
    have := intermediate_value_Icc hwV2 hcont
    obtain ⟨V, hV, hVp⟩ := this ⟨by linarith, hSV2⟩
    exact ⟨V, lt_of_lt_of_le hwpos hV.1, hVp⟩
  obtain ⟨hVmem, hVS⟩ := Function.invFunOn_pos hex
  have hVpos : 0 < contV α p := hVmem
  set V := contV α p with hVdef
  have hVS' : contS α V = p := hVS
  have hup := pl_one_sub_le hα0 hVpos
  have hlo := pl_one_sub_ge hα0 hVpos
  rw [hVS'] at hup hlo
  have hSle := pl_S_le hα0 hVpos
  rw [hVS'] at hSle
  have hVw : w ≤ V := by
    by_contra hcon
    rw [not_le] at hcon
    have : V * (4:ℝ) ^ α < w * (4:ℝ) ^ α := mul_lt_mul_of_pos_right hcon h4pos
    have e : w * (4:ℝ) ^ α = 1 / 4 := by
      rw [hw]; field_simp
    linarith
  constructor
  · rw [div_le_iff₀ hp]
    rcases le_total V 1 with hV1 | hV1
    · rw [max_eq_right hV1] at hlo
      have hκle : κ ≤ 1 - p := by
        have : 1 / (2 * (α + 1) * 1) = κ := by rw [hκ]; ring
        linarith
      exact mul_le_mul hVw hκle hκpos.le hVpos.le
    · rw [max_eq_left hV1] at hlo
      rw [div_le_iff₀ (by positivity)] at hlo
      have hh : κ ≤ V * (1 - p) := by
        rw [hκ, div_le_iff₀ (by positivity)]
        nlinarith
      have : w * κ ≤ κ := by nlinarith
      linarith
  · rw [le_div_iff₀ hp]
    rw [le_div_iff₀ (by positivity)] at hup
    rw [le_div_iff₀ hα1]
    nlinarith

/-! ## Finite participation (`lem:app-pl-finite-inverse`) -/

private lemma pl_fi_g_anti {α V : ℝ} (hα0 : 0 < α) (hV : 0 < V) :
    AntitoneOn (fun t : ℝ => V / (V + t ^ α)) (Set.Icc 0 1) := by
  intro s hs t ht hst
  have hs0 : 0 ≤ s := hs.1
  have hpow : s ^ α ≤ t ^ α := Real.rpow_le_rpow hs0 hst hα0.le
  have hpos : 0 < V + s ^ α := by
    have := Real.rpow_nonneg hs0 α
    linarith
  show V / (V + t ^ α) ≤ V / (V + s ^ α)
  exact div_le_div_of_nonneg_left hV.le hpos (by linarith)

private lemma pl_fi_int_ii {α V : ℝ} (hα0 : 0 < α) (hV : 0 < V) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable (fun t : ℝ => V / (V + t ^ α)) MeasureTheory.volume a b :=
  ((pl_fi_g_anti hα0 hV).mono (Set.uIcc_subset_Icc ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩)).intervalIntegrable

private lemma pl_fi_int_bounds {α V : ℝ} (hα0 : 0 < α) (hV : 0 < V) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    V / (V + b ^ α) * (b - a) ≤ ∫ t in a..b, V / (V + t ^ α) ∧
      ∫ t in a..b, V / (V + t ^ α) ≤ V / (V + a ^ α) * (b - a) := by
  have hanti := pl_fi_g_anti hα0 hV
  have hint := pl_fi_int_ii hα0 hV ha hab hb
  have ha1 : a ∈ Set.Icc (0:ℝ) 1 := ⟨ha, hab.trans hb⟩
  have hb1 : b ∈ Set.Icc (0:ℝ) 1 := ⟨ha.trans hab, hb⟩
  constructor
  · calc V / (V + b ^ α) * (b - a)
        = ∫ t in a..b, V / (V + b ^ α) := by
          simp only [intervalIntegral.integral_const, smul_eq_mul]; ring
      _ ≤ ∫ t in a..b, V / (V + t ^ α) :=
          intervalIntegral.integral_mono_on hab intervalIntegrable_const hint
            (fun t ht => hanti (⟨ha.trans ht.1, ht.2.trans hb⟩ : t ∈ Set.Icc (0:ℝ) 1) hb1 ht.2)
  · calc ∫ t in a..b, V / (V + t ^ α)
        ≤ ∫ t in a..b, V / (V + a ^ α) :=
          intervalIntegral.integral_mono_on hab hint intervalIntegrable_const
            (fun t ht => hanti ha1 (⟨ha.trans ht.1, ht.2.trans hb⟩ : t ∈ Set.Icc (0:ℝ) 1) ht.1)
      _ = V / (V + a ^ α) * (b - a) := by
          simp only [intervalIntegral.integral_const, smul_eq_mul]; ring

private lemma pl_fi_sum_range_Icc (f : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, f (k + 1) = ∑ j ∈ Finset.Icc 1 n, f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]

/-- `lem:app-pl-finite-inverse` (snapshot `cr-2026-10-23`), part (i), the first claim `0 ≤ S_α - S_N ≤ 1/N`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Finite participation]\label{lem:app-pl-finite-inverse}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item $0\le S_\alpha(V)-S_N(V)\le1/N$ and $\abs{VS_N'(V)-\mathsf T(V)}\le1/(2N)$ for $V>0$.
\item There is $C$ such that, for $M\ge1$, $B\ge2$ and $M/\gamma\le p\le1-M/\gamma$,
\[
\Big|\log\frac{V_N(p)}{V_\alpha(p)}\Big|\le\frac{C}{BM}.
\]
\item $V_N(p)\asymp(1-p)^{-1}$ for $p\ge1/2$, uniformly in $N$.
\item If $\alpha>1$, $Bm\to\infty$ and $m/\gamma\to0$, then $c_N\Lambda_N(m)\sim(Bm/K_\alpha)^\alpha$ and
$m\Lambda_N'(m)/\Lambda_N(m)\to\alpha$, locally uniformly in $m$ on compact subsets of $(0,\infty)$ when
$m$ is held fixed.
\item If $\alpha>1$, then $c_N\Lambda_N(m)\asymp(Bm)^\alpha$ for $1/B\le m\le\gamma/2$ and
$c_N\Lambda_N(m)\asymp Bm$ for $0<m\le1/B$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_finite_inverse_i_a {α : ℝ} {N : ℕ} (hα : 0 < α) (hN : 0 < N) :
    ∀ V : ℝ, 0 < V → 0 ≤ contS α V - finS α N V ∧ contS α V - finS α N V ≤ 1 / (N : ℝ) := by
  intro V hV
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hNne : (N:ℝ) ≠ 0 := hNr.ne'
  set F : ℕ → ℝ := fun j => V / (V + ((j:ℝ) / (N:ℝ)) ^ α) with hF
  set I : ℕ → ℝ := fun k => ∫ t in ((k:ℝ) / N)..(((k+1:ℕ):ℝ) / N), V / (V + t ^ α) with hI
  have hFsum : finS α N V = (N:ℝ)⁻¹ * ∑ k ∈ Finset.range N, F (k + 1) := by
    rw [pl_fi_sum_range_Icc F N]
    unfold finS
    rfl
  have hsplit : contS α V = ∑ k ∈ Finset.range N, I k := by
    have hint : ∀ k < N, IntervalIntegrable (fun t : ℝ => V / (V + t ^ α)) MeasureTheory.volume
        ((k:ℝ) / N) (((k+1:ℕ):ℝ) / N) := by
      intro k hk
      have hk' : k + 1 ≤ N := hk
      have hk1 : ((k+1:ℕ):ℝ) ≤ N := by exact_mod_cast hk'
      have hab : (k:ℝ) / N ≤ ((k+1:ℕ):ℝ) / N := by
        apply div_le_div_of_nonneg_right _ hNr.le
        push_cast; linarith
      exact pl_fi_int_ii hα hV (by positivity) hab (by rw [div_le_one hNr]; exact hk1)
    have hs := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
      (f := fun t : ℝ => V / (V + t ^ α)) (a := fun k : ℕ => (k:ℝ) / N) (n := N) hint
    rw [Nat.cast_zero, zero_div, div_self hNne] at hs
    unfold contS
    exact hs.symm
  have hterm : ∀ k ∈ Finset.range N, 0 ≤ I k - (N:ℝ)⁻¹ * F (k + 1) ∧
      I k - (N:ℝ)⁻¹ * F (k + 1) ≤ (N:ℝ)⁻¹ * (F k - F (k + 1)) := by
    intro k hk
    have hk' : k + 1 ≤ N := Finset.mem_range.1 hk
    have hk1 : ((k+1:ℕ):ℝ) ≤ N := by exact_mod_cast hk'
    have ha0 : (0:ℝ) ≤ (k:ℝ) / N := by positivity
    have hab : (k:ℝ) / N ≤ ((k+1:ℕ):ℝ) / N := by
      apply div_le_div_of_nonneg_right _ hNr.le
      push_cast; linarith
    have hb1 : ((k+1:ℕ):ℝ) / N ≤ 1 := by rw [div_le_one hNr]; exact hk1
    obtain ⟨hlo, hhi⟩ := pl_fi_int_bounds hα hV ha0 hab hb1
    have hlen : ((k+1:ℕ):ℝ) / N - (k:ℝ) / N = (N:ℝ)⁻¹ := by push_cast; ring
    rw [hlen] at hlo hhi
    have hFk1 : F (k + 1) = V / (V + (((k+1:ℕ):ℝ) / N) ^ α) := rfl
    have hFk : F k = V / (V + ((k:ℝ) / N) ^ α) := rfl
    have hIk : I k = ∫ t in ((k:ℝ) / N)..(((k+1:ℕ):ℝ) / N), V / (V + t ^ α) := rfl
    rw [hFk1, hFk, hIk]
    constructor
    · linarith
    · linarith
  have hdecomp : contS α V - finS α N V = ∑ k ∈ Finset.range N, (I k - (N:ℝ)⁻¹ * F (k + 1)) := by
    rw [hsplit, hFsum, Finset.mul_sum, Finset.sum_sub_distrib]
  have hF0 : F 0 = 1 := by
    simp [hF, Real.zero_rpow hα.ne', hV.ne']
  have hFN : F N = V / (V + 1) := by
    simp [hF, hNne]
  have hnonneg : 0 ≤ V / (V + 1) := div_nonneg hV.le (by linarith)
  refine ⟨?_, ?_⟩
  · rw [hdecomp]
    exact Finset.sum_nonneg (fun k hk => (hterm k hk).1)
  · rw [hdecomp]
    calc ∑ k ∈ Finset.range N, (I k - (N:ℝ)⁻¹ * F (k + 1))
        ≤ ∑ k ∈ Finset.range N, ((N:ℝ)⁻¹ * (F k - F (k + 1))) :=
          Finset.sum_le_sum (fun k hk => (hterm k hk).2)
      _ = (N:ℝ)⁻¹ * (F 0 - F N) := by
          rw [← Finset.mul_sum, Finset.sum_range_sub' F N]
      _ ≤ 1 / (N:ℝ) := by
          rw [hF0, hFN, one_div]
          exact mul_le_of_le_one_right (inv_nonneg.2 hNr.le) (by linarith)

private lemma pl_fi_anti_riemann {g : ℝ → ℝ} {N : ℕ} (hN : 0 < N)
    (hg : AntitoneOn g (Set.Icc 0 1)) :
    0 ≤ (∫ t in (0:ℝ)..1, g t) - (N:ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 N, g ((j:ℝ) / (N:ℝ)) ∧
      (∫ t in (0:ℝ)..1, g t) - (N:ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 N, g ((j:ℝ) / (N:ℝ))
        ≤ (g 0 - g 1) / (N:ℝ) := by
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hNne : (N:ℝ) ≠ 0 := hNr.ne'
  have hint : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ 1 →
      IntervalIntegrable g MeasureTheory.volume a b := fun {a b} ha hab hb =>
    (hg.mono (Set.uIcc_subset_Icc ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩)).intervalIntegrable
  have hbounds : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ 1 →
      g b * (b - a) ≤ ∫ t in a..b, g t ∧ ∫ t in a..b, g t ≤ g a * (b - a) := by
    intro a b ha hab hb
    have ha1 : a ∈ Set.Icc (0:ℝ) 1 := ⟨ha, hab.trans hb⟩
    have hb1 : b ∈ Set.Icc (0:ℝ) 1 := ⟨ha.trans hab, hb⟩
    constructor
    · calc g b * (b - a) = ∫ t in a..b, g b := by
            simp only [intervalIntegral.integral_const, smul_eq_mul]; ring
        _ ≤ ∫ t in a..b, g t :=
            intervalIntegral.integral_mono_on hab intervalIntegrable_const (hint ha hab hb)
              (fun t ht => hg (⟨ha.trans ht.1, ht.2.trans hb⟩ : t ∈ Set.Icc (0:ℝ) 1) hb1 ht.2)
    · calc ∫ t in a..b, g t ≤ ∫ t in a..b, g a :=
            intervalIntegral.integral_mono_on hab (hint ha hab hb) intervalIntegrable_const
              (fun t ht => hg ha1 (⟨ha.trans ht.1, ht.2.trans hb⟩ : t ∈ Set.Icc (0:ℝ) 1) ht.1)
        _ = g a * (b - a) := by
            simp only [intervalIntegral.integral_const, smul_eq_mul]; ring
  set F : ℕ → ℝ := fun j => g ((j:ℝ) / (N:ℝ)) with hF
  set I : ℕ → ℝ := fun k => ∫ t in ((k:ℝ) / N)..(((k+1:ℕ):ℝ) / N), g t with hI
  have hFsum : ∑ j ∈ Finset.Icc 1 N, g ((j:ℝ) / (N:ℝ)) = ∑ k ∈ Finset.range N, F (k + 1) := by
    rw [pl_fi_sum_range_Icc F N]
  have hsplit : (∫ t in (0:ℝ)..1, g t) = ∑ k ∈ Finset.range N, I k := by
    have hint' : ∀ k < N, IntervalIntegrable g MeasureTheory.volume
        ((k:ℝ) / N) (((k+1:ℕ):ℝ) / N) := by
      intro k hk
      have hk' : k + 1 ≤ N := hk
      have hk1 : ((k+1:ℕ):ℝ) ≤ N := by exact_mod_cast hk'
      have hab : (k:ℝ) / N ≤ ((k+1:ℕ):ℝ) / N := by
        apply div_le_div_of_nonneg_right _ hNr.le
        push_cast; linarith
      exact hint (by positivity) hab (by rw [div_le_one hNr]; exact hk1)
    have hs := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
      (f := g) (a := fun k : ℕ => (k:ℝ) / N) (n := N) hint'
    rw [Nat.cast_zero, zero_div, div_self hNne] at hs
    exact hs.symm
  have hterm : ∀ k ∈ Finset.range N, 0 ≤ I k - (N:ℝ)⁻¹ * F (k + 1) ∧
      I k - (N:ℝ)⁻¹ * F (k + 1) ≤ (N:ℝ)⁻¹ * (F k - F (k + 1)) := by
    intro k hk
    have hk' : k + 1 ≤ N := Finset.mem_range.1 hk
    have hk1 : ((k+1:ℕ):ℝ) ≤ N := by exact_mod_cast hk'
    have ha0 : (0:ℝ) ≤ (k:ℝ) / N := by positivity
    have hab : (k:ℝ) / N ≤ ((k+1:ℕ):ℝ) / N := by
      apply div_le_div_of_nonneg_right _ hNr.le
      push_cast; linarith
    have hb1 : ((k+1:ℕ):ℝ) / N ≤ 1 := by rw [div_le_one hNr]; exact hk1
    obtain ⟨hlo, hhi⟩ := hbounds ha0 hab hb1
    have hlen : ((k+1:ℕ):ℝ) / N - (k:ℝ) / N = (N:ℝ)⁻¹ := by push_cast; ring
    rw [hlen] at hlo hhi
    have hFk1 : F (k + 1) = g (((k+1:ℕ):ℝ) / N) := rfl
    have hFk : F k = g ((k:ℝ) / N) := rfl
    have hIk : I k = ∫ t in ((k:ℝ) / N)..(((k+1:ℕ):ℝ) / N), g t := rfl
    rw [hFk1, hFk, hIk]
    constructor
    · linarith
    · linarith
  have hdecomp : (∫ t in (0:ℝ)..1, g t) - (N:ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 N, g ((j:ℝ) / (N:ℝ))
      = ∑ k ∈ Finset.range N, (I k - (N:ℝ)⁻¹ * F (k + 1)) := by
    rw [hsplit, hFsum, Finset.mul_sum, Finset.sum_sub_distrib]
  have hF0 : F 0 = g 0 := by simp [hF]
  have hFN : F N = g 1 := by simp [hF, hNne]
  rw [hdecomp]
  refine ⟨Finset.sum_nonneg (fun k hk => (hterm k hk).1), ?_⟩
  calc ∑ k ∈ Finset.range N, (I k - (N:ℝ)⁻¹ * F (k + 1))
      ≤ ∑ k ∈ Finset.range N, ((N:ℝ)⁻¹ * (F k - F (k + 1))) :=
        Finset.sum_le_sum (fun k hk => (hterm k hk).2)
    _ = (N:ℝ)⁻¹ * (F 0 - F N) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub' F N]
    _ = (g 0 - g 1) / (N:ℝ) := by
        rw [hF0, hFN]; ring

private lemma pl_fi_unimodal_riemann {H : ℝ → ℝ} {N : ℕ} {m P : ℝ} (hN : 0 < N)
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hmono : MonotoneOn H (Set.Icc 0 m)) (hanti : AntitoneOn H (Set.Icc m 1))
    (hH0 : 0 ≤ H 0) (hH1 : 0 ≤ H 1) (hP : H m ≤ P) :
    |(∫ t in (0:ℝ)..1, H t) - (N:ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 N, H ((j:ℝ) / (N:ℝ))| ≤ P / (N:ℝ) := by
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  set f : ℝ → ℝ := fun t => H (min t m) with hf
  set g : ℝ → ℝ := fun t => H (max t m) with hg
  have hfm : MonotoneOn f (Set.Icc 0 1) := by
    intro s hs t ht hst
    exact hmono ⟨le_min hs.1 hm0, min_le_right _ _⟩ ⟨le_min ht.1 hm0, min_le_right _ _⟩
      (min_le_min_right _ hst)
  have hga : AntitoneOn g (Set.Icc 0 1) := by
    intro s hs t ht hst
    exact hanti ⟨le_max_right _ _, max_le hs.2 hm1⟩ ⟨le_max_right _ _, max_le ht.2 hm1⟩
      (max_le_max_right _ hst)
  have hfneg : AntitoneOn (fun t => - f t) (Set.Icc 0 1) := by
    intro s hs t ht hst
    exact neg_le_neg (hfm hs ht hst)
  have hHfg : ∀ t ∈ Set.Icc (0:ℝ) 1, H t = f t + g t - H m := by
    intro t _
    rcases le_total t m with h | h
    · simp [hf, hg, min_eq_left h, max_eq_right h]
    · simp [hf, hg, min_eq_right h, max_eq_left h]
  have hfint : IntervalIntegrable f MeasureTheory.volume 0 1 :=
    (hfm.mono (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable
  have hgint : IntervalIntegrable g MeasureTheory.volume 0 1 :=
    (hga.mono (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable
  have hI : (∫ t in (0:ℝ)..1, H t) = (∫ t in (0:ℝ)..1, f t) + (∫ t in (0:ℝ)..1, g t) - H m := by
    have h1 : (∫ t in (0:ℝ)..1, H t) = ∫ t in (0:ℝ)..1, (f t + g t - H m) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      exact hHfg t ht
    rw [h1, intervalIntegral.integral_sub (hfint.add hgint) intervalIntegrable_const,
      intervalIntegral.integral_add hfint hgint]
    simp
  have hS : ∑ j ∈ Finset.Icc 1 N, H ((j:ℝ) / (N:ℝ))
      = ∑ j ∈ Finset.Icc 1 N, f ((j:ℝ) / (N:ℝ)) + ∑ j ∈ Finset.Icc 1 N, g ((j:ℝ) / (N:ℝ))
        - (N:ℝ) * H m := by
    have : ∀ j ∈ Finset.Icc 1 N, H ((j:ℝ) / (N:ℝ))
        = f ((j:ℝ) / (N:ℝ)) + g ((j:ℝ) / (N:ℝ)) - H m := by
      intro j hj
      have hj' := Finset.mem_Icc.1 hj
      have hj0 : (0:ℝ) ≤ (j:ℝ) := by positivity
      have hjN : (j:ℝ) / N ≤ 1 := by
        rw [div_le_one hNr]; exact_mod_cast hj'.2
      exact hHfg _ ⟨div_nonneg hj0 hNr.le, hjN⟩
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    simp
  have hrel : (∫ t in (0:ℝ)..1, H t) - (N:ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 N, H ((j:ℝ) / (N:ℝ))
      = ((∫ t in (0:ℝ)..1, f t) - (N:ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 N, f ((j:ℝ) / (N:ℝ)))
        + ((∫ t in (0:ℝ)..1, g t) - (N:ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 N, g ((j:ℝ) / (N:ℝ))) := by
    rw [hI, hS]
    field_simp
    ring
  obtain ⟨hg1, hg2⟩ := pl_fi_anti_riemann hN hga
  obtain ⟨hf1, hf2⟩ := pl_fi_anti_riemann hN hfneg
  have hfint' : (∫ t in (0:ℝ)..1, (- f t)) = -∫ t in (0:ℝ)..1, f t := intervalIntegral.integral_neg
  have hfsum : ∑ j ∈ Finset.Icc 1 N, (- f ((j:ℝ) / (N:ℝ))) = -∑ j ∈ Finset.Icc 1 N, f ((j:ℝ) / (N:ℝ)) :=
    Finset.sum_neg_distrib _
  rw [hfint', hfsum] at hf1 hf2
  have hf0 : f 0 = H 0 := by simp [hf, min_eq_left hm0]
  have hf1' : f 1 = H m := by simp [hf, min_eq_right hm1]
  have hg0 : g 0 = H m := by simp [hg, max_eq_right hm0]
  have hg1' : g 1 = H 1 := by simp [hg, max_eq_left hm1]
  rw [hf0, hf1'] at hf2
  rw [hg0, hg1'] at hg2
  rw [hrel, abs_le]
  have e1 : (-H 0 - -H m) / (N:ℝ) = (H m - H 0) / (N:ℝ) := by ring
  have e2 : (H m - H 1) / (N:ℝ) ≤ P / (N:ℝ) :=
    div_le_div_of_nonneg_right (by linarith) hNr.le
  have e3 : (H m - H 0) / (N:ℝ) ≤ P / (N:ℝ) :=
    div_le_div_of_nonneg_right (by linarith) hNr.le
  constructor
  · linarith
  · linarith

private lemma pl_fi_h_inc {V x y : ℝ} (hV : 0 < V) (hx : 0 ≤ x) (hxy : x ≤ y)
    (h : x * y ≤ V ^ 2) : V * x / (V + x) ^ 2 ≤ V * y / (V + y) ^ 2 := by
  have h1 : (0:ℝ) < (V + x) ^ 2 := by positivity
  have h2 : (0:ℝ) < (V + y) ^ 2 := by have : 0 ≤ y := hx.trans hxy; positivity
  rw [div_le_div_iff₀ h1 h2]
  have := mul_nonneg (mul_nonneg hV.le (sub_nonneg.2 hxy)) (sub_nonneg.2 h)
  nlinarith

private lemma pl_fi_h_dec {V x y : ℝ} (hV : 0 < V) (hx : 0 ≤ x) (hxy : x ≤ y)
    (h : V ^ 2 ≤ x * y) : V * y / (V + y) ^ 2 ≤ V * x / (V + x) ^ 2 := by
  have h1 : (0:ℝ) < (V + x) ^ 2 := by positivity
  have h2 : (0:ℝ) < (V + y) ^ 2 := by have : 0 ≤ y := hx.trans hxy; positivity
  rw [div_le_div_iff₀ h2 h1]
  have := mul_nonneg (mul_nonneg hV.le (sub_nonneg.2 hxy)) (sub_nonneg.2 h)
  nlinarith

private lemma pl_fi_h_unimodal {α V : ℝ} (hα : 0 < α) (hV : 0 < V) :
    ∃ m : ℝ, 0 ≤ m ∧ m ≤ 1 ∧
      MonotoneOn (fun t : ℝ => V * t ^ α / (V + t ^ α) ^ 2) (Set.Icc 0 m) ∧
      AntitoneOn (fun t : ℝ => V * t ^ α / (V + t ^ α) ^ 2) (Set.Icc m 1) := by
  rcases le_or_gt 1 V with hV1 | hV1
  · refine ⟨1, zero_le_one, le_rfl, ?_, ?_⟩
    · intro s hs t ht hst
      have hs0 : 0 ≤ s := hs.1
      have h1 : s ^ α ≤ 1 := Real.rpow_le_one hs.1 (hs.2) hα.le
      have h2 : t ^ α ≤ 1 := Real.rpow_le_one ht.1 (ht.2) hα.le
      have h3 : s ^ α ≤ t ^ α := Real.rpow_le_rpow hs0 hst hα.le
      have h4 := Real.rpow_nonneg hs0 α
      apply pl_fi_h_inc hV h4 h3
      nlinarith
    · intro s hs t ht hst
      have : s = t := le_antisymm hst (by linarith [hs.1, ht.2])
      subst this
      exact le_rfl
  · set m : ℝ := V ^ (1 / α) with hm
    have hm0 : 0 ≤ m := Real.rpow_nonneg hV.le _
    have hm1 : m ≤ 1 := Real.rpow_le_one hV.le hV1.le (by positivity)
    have hmα : m ^ α = V := by
      rw [hm, ← Real.rpow_mul hV.le, one_div_mul_cancel hα.ne', Real.rpow_one]
    refine ⟨m, hm0, hm1, ?_, ?_⟩
    · intro s hs t ht hst
      have hs0 : 0 ≤ s := hs.1
      have h1 : s ^ α ≤ V := hmα ▸ Real.rpow_le_rpow hs0 hs.2 hα.le
      have h2 : t ^ α ≤ V := hmα ▸ Real.rpow_le_rpow ht.1 ht.2 hα.le
      have h3 : s ^ α ≤ t ^ α := Real.rpow_le_rpow hs0 hst hα.le
      have h4 := Real.rpow_nonneg hs0 α
      apply pl_fi_h_inc hV h4 h3
      nlinarith
    · intro s hs t ht hst
      have hs0 : 0 ≤ s := hm0.trans hs.1
      have h1 : V ≤ s ^ α := hmα ▸ Real.rpow_le_rpow hm0 hs.1 hα.le
      have h2 : V ≤ t ^ α := hmα ▸ Real.rpow_le_rpow hm0 (hs.1.trans hst) hα.le
      have h3 : s ^ α ≤ t ^ α := Real.rpow_le_rpow hs0 hst hα.le
      have h4 := Real.rpow_nonneg hs0 α
      apply pl_fi_h_dec hV h4 h3
      nlinarith

private lemma pl_fi_one_sub_le {α V : ℝ} {N : ℕ} (hα : 0 < α) (hN : 0 < N) (hV : 0 < V) :
    1 - finS α N V ≤ 1 / V := by
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hterm : ∀ j ∈ Finset.Icc 1 N, (1 - 1 / V) ≤ V / (V + ((j : ℝ) / (N : ℝ)) ^ α) := by
    intro j hj
    have hj' := Finset.mem_Icc.1 hj
    have hj0 : (0:ℝ) < (j:ℝ) := by exact_mod_cast (by omega : 0 < j)
    have ha0 : 0 ≤ ((j : ℝ) / (N : ℝ)) ^ α := Real.rpow_nonneg (div_pos hj0 hNr).le α
    have hjN : (j:ℝ) / N ≤ 1 := by
      rw [div_le_one hNr]; exact_mod_cast hj'.2
    have ha1 : ((j : ℝ) / (N : ℝ)) ^ α ≤ 1 := Real.rpow_le_one (div_pos hj0 hNr).le hjN hα.le
    generalize ((j : ℝ) / (N : ℝ)) ^ α = a at ha0 ha1 ⊢
    have hw : 1 / V * V = 1 := by field_simp
    have hw0 : 0 ≤ 1 / V := by positivity
    rw [le_div_iff₀ (by linarith)]
    nlinarith [mul_nonneg hw0 ha0]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hsum
  simp only [Nat.add_sub_cancel] at hsum
  unfold finS
  have : (N:ℝ)⁻¹ * ((N:ℝ) * (1 - 1 / V)) = 1 - 1 / V := by field_simp
  have h2 := mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hNr.le)
  rw [this] at h2
  linarith

private lemma pl_fi_finS_le {α V : ℝ} {N : ℕ} (hα : 0 < α) (hN : 0 < N) (hV : 0 < V) :
    finS α N V ≤ V / (((1:ℝ) / (N : ℝ)) ^ α) := by
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hA : 0 < ((1:ℝ) / (N : ℝ)) ^ α := Real.rpow_pos_of_pos (by positivity) α
  have hterm : ∀ j ∈ Finset.Icc 1 N, V / (V + ((j : ℝ) / (N : ℝ)) ^ α) ≤ V / (((1:ℝ) / (N : ℝ)) ^ α) := by
    intro j hj
    have hj' := Finset.mem_Icc.1 hj
    have hj1 : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj'.1
    have h1 : ((1:ℝ) / (N : ℝ)) ^ α ≤ ((j : ℝ) / (N : ℝ)) ^ α :=
      Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hj1 hNr.le) hα.le
    calc V / (V + ((j : ℝ) / (N : ℝ)) ^ α) ≤ V / ((j : ℝ) / (N : ℝ)) ^ α :=
          div_le_div_of_nonneg_left hV.le (by linarith) (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_left hV.le hA h1
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hsum
  simp only [Nat.add_sub_cancel] at hsum
  unfold finS
  have : (N:ℝ)⁻¹ * ((N:ℝ) * (V / (((1:ℝ) / (N : ℝ)) ^ α))) = V / (((1:ℝ) / (N : ℝ)) ^ α) := by
    field_simp
  have h2 := mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hNr.le)
  rw [this] at h2
  exact h2

private lemma pl_fi_finS_contOn {α : ℝ} {N : ℕ} (hα : 0 < α) (hN : 0 < N) :
    ContinuousOn (finS α N) (Set.Ioi 0) := by
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  unfold finS
  apply ContinuousOn.mul continuousOn_const
  apply continuousOn_finsetSum
  intro j hj
  have hj' := Finset.mem_Icc.1 hj
  have hj0 : (0:ℝ) < (j:ℝ) := by exact_mod_cast (by omega : 0 < j)
  have ha0 : 0 ≤ ((j : ℝ) / (N : ℝ)) ^ α := Real.rpow_nonneg (div_pos hj0 hNr).le α
  refine ContinuousOn.div continuousOn_id (continuousOn_id.add continuousOn_const) ?_
  intro x hx
  have : (0:ℝ) < x := hx
  linarith


/-- `lem:app-pl-finite-inverse` (snapshot `cr-2026-10-23`), part (i), the second claim `|V S_N'(V) - T(V)| ≤ 1/(2N)`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Finite participation]\label{lem:app-pl-finite-inverse}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item $0\le S_\alpha(V)-S_N(V)\le1/N$ and $\abs{VS_N'(V)-\mathsf T(V)}\le1/(2N)$ for $V>0$.
\item There is $C$ such that, for $M\ge1$, $B\ge2$ and $M/\gamma\le p\le1-M/\gamma$,
\[
\Big|\log\frac{V_N(p)}{V_\alpha(p)}\Big|\le\frac{C}{BM}.
\]
\item $V_N(p)\asymp(1-p)^{-1}$ for $p\ge1/2$, uniformly in $N$.
\item If $\alpha>1$, $Bm\to\infty$ and $m/\gamma\to0$, then $c_N\Lambda_N(m)\sim(Bm/K_\alpha)^\alpha$ and
$m\Lambda_N'(m)/\Lambda_N(m)\to\alpha$, locally uniformly in $m$ on compact subsets of $(0,\infty)$ when
$m$ is held fixed.
\item If $\alpha>1$, then $c_N\Lambda_N(m)\asymp(Bm)^\alpha$ for $1/B\le m\le\gamma/2$ and
$c_N\Lambda_N(m)\asymp Bm$ for $0<m\le1/B$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_finite_inverse_i_b {α : ℝ} {N : ℕ} (hα : 0 < α) (hN : 0 < N) :
    ∀ V : ℝ, 0 < V → |V * deriv (finS α N) V - Tcont α V| ≤ 1 / (2 * (N : ℝ)) := by
  intro V hV
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hterm : ∀ j ∈ Finset.Icc 1 N, HasDerivAt (fun W : ℝ => W / (W + ((j:ℝ) / (N:ℝ)) ^ α))
      (((j:ℝ) / (N:ℝ)) ^ α / (V + ((j:ℝ) / (N:ℝ)) ^ α) ^ 2) V := by
    intro j hj
    have hj' := Finset.mem_Icc.1 hj
    have hj0 : (0:ℝ) < (j:ℝ) := by exact_mod_cast (by omega : 0 < j)
    have ha0 : 0 ≤ ((j:ℝ) / (N:ℝ)) ^ α := Real.rpow_nonneg (div_pos hj0 hNr).le α
    have hne : V + ((j:ℝ) / (N:ℝ)) ^ α ≠ 0 := by linarith
    have h := (hasDerivAt_id V).div ((hasDerivAt_id V).add_const (((j:ℝ) / (N:ℝ)) ^ α)) hne
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have hd : HasDerivAt (finS α N)
      ((N:ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 N, ((j:ℝ) / (N:ℝ)) ^ α / (V + ((j:ℝ) / (N:ℝ)) ^ α) ^ 2) V := by
    unfold finS
    exact (HasDerivAt.fun_sum hterm).const_mul _
  rw [hd.deriv]
  set H : ℝ → ℝ := fun t => V * t ^ α / (V + t ^ α) ^ 2 with hH
  have hVd : V * ((N:ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 N, ((j:ℝ) / (N:ℝ)) ^ α / (V + ((j:ℝ) / (N:ℝ)) ^ α) ^ 2)
      = (N:ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 N, H ((j:ℝ) / (N:ℝ)) := by
    have : V * ∑ j ∈ Finset.Icc 1 N, ((j:ℝ) / (N:ℝ)) ^ α / (V + ((j:ℝ) / (N:ℝ)) ^ α) ^ 2
        = ∑ j ∈ Finset.Icc 1 N, H ((j:ℝ) / (N:ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [hH]
      ring
    rw [mul_left_comm, this]
  rw [hVd]
  have hT : Tcont α V = ∫ t in (0:ℝ)..1, H t := rfl
  rw [hT, abs_sub_comm]
  obtain ⟨m, hm0, hm1, hmono, hanti⟩ := pl_fi_h_unimodal hα hV
  have hHnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ H t := by
    intro t ht
    have := Real.rpow_nonneg ht α
    simp only [hH]
    positivity
  have hHle : ∀ t : ℝ, 0 ≤ t → H t ≤ 1 / 4 := by
    intro t ht
    have h0 := Real.rpow_nonneg ht α
    simp only [hH]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (V - t ^ α)]
  have := pl_fi_unimodal_riemann (H := H) (N := N) (m := m) (P := 1 / 4) hN hm0 hm1 hmono hanti
    (hHnn 0 le_rfl) (hHnn 1 zero_le_one) (hHle m hm0)
  refine this.trans ?_
  rw [div_le_div_iff₀ hNr (by positivity)]
  nlinarith

/-! ### Helpers for part (ii) -/

private lemma pl_ii_S_le_a {α V a : ℝ} (hα0 : 0 < α) (hV : 0 < V) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    contS α V ≤ a + V / a ^ α := by
  have h1 := pl_s_ii hα0 hV (a := 0) (b := a) le_rfl ha0.le
  have h2 := pl_s_ii hα0 hV (a := a) (b := 1) ha0.le zero_le_one
  have hsplit : contS α V = (∫ t in (0:ℝ)..a, V / (V + t ^ α)) +
      ∫ t in a..1, V / (V + t ^ α) :=
    (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
  have hA : ∫ t in (0:ℝ)..a, V / (V + t ^ α) ≤ a := by
    have := intervalIntegral.integral_mono_on ha0.le h1
      (intervalIntegrable_const (c := (1:ℝ)))
      (fun t ht => (pl_cont_s_le_one hα0 hV (Set.Icc_subset_uIcc
        (by exact ⟨ht.1, by linarith [ht.2]⟩ : t ∈ Set.Icc (0:ℝ) 1))).2)
    simpa using this
  have hapos : 0 < a ^ α := Real.rpow_pos_of_pos ha0 α
  have hB : ∫ t in a..1, V / (V + t ^ α) ≤ V / a ^ α := by
    have := intervalIntegral.integral_mono_on ha1 h2
      (intervalIntegrable_const (c := V / a ^ α))
      (fun t ht => by
        have h4 : a ^ α ≤ t ^ α := Real.rpow_le_rpow ha0.le ht.1 hα0.le
        calc V / (V + t ^ α) ≤ V / t ^ α := div_le_div_of_nonneg_left hV.le
              (lt_of_lt_of_le hapos h4) (by linarith)
          _ ≤ V / a ^ α := div_le_div_of_nonneg_left hV.le hapos h4)
    have h8 : 0 ≤ V / a ^ α := by positivity
    simp only [intervalIntegral.integral_const, smul_eq_mul] at this
    nlinarith
  linarith

private lemma pl_ii_exists_cont {α p : ℝ} (hα0 : 0 < α) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ V : ℝ, 0 < V ∧ contS α V = p := by
  have ha0 : 0 < p / 2 := by positivity
  have hapos : 0 < (p / 2) ^ α := Real.rpow_pos_of_pos ha0 α
  set w : ℝ := min 1 (p / 2 * (p / 2) ^ α) with hw
  have hwpos : 0 < w := lt_min one_pos (by positivity)
  have hw1 : w ≤ 1 := min_le_left _ _
  have hwS : contS α w ≤ p := by
    have := pl_ii_S_le_a hα0 hwpos ha0 (by linarith : p / 2 ≤ 1)
    have h2 : w / (p / 2) ^ α ≤ p / 2 := by
      rw [div_le_iff₀ hapos]
      exact (min_le_right _ _).trans (le_of_eq (by ring))
    linarith
  set V2 : ℝ := max (1 / ((α + 1) * (1 - p))) 1 with hV2
  have hV2pos : 0 < V2 := lt_max_of_lt_right one_pos
  have hwV2 : w ≤ V2 := hw1.trans (le_max_right _ _)
  have hp' : 0 < 1 - p := by linarith
  have hSV2 : p ≤ contS α V2 := by
    have h1 := pl_one_sub_le hα0 hV2pos
    have h2 : 1 / ((α + 1) * V2) ≤ 1 - p := by
      rw [div_le_iff₀ (by positivity)]
      have h3 : 1 / ((α + 1) * (1 - p)) ≤ V2 := le_max_left _ _
      rw [div_le_iff₀ (by positivity)] at h3
      nlinarith
    linarith
  have hcont : ContinuousOn (contS α) (Set.Icc w V2) :=
    (pl_contS_continuousOn hα0 hwpos).mono Set.Icc_subset_Ici_self
  obtain ⟨V, hV, hVp⟩ := intermediate_value_Icc hwV2 hcont ⟨hwS, hSV2⟩
  exact ⟨V, lt_of_lt_of_le hwpos hV.1, hVp⟩

private lemma pl_ii_exists_fin {α p : ℝ} {N : ℕ} (hα : 0 < α) (hN : 0 < N) (hp0 : 0 < p)
    (hp1 : p < 1) : ∃ V : ℝ, 0 < V ∧ finS α N V = p := by
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  set q : ℝ := 1 - p with hq
  have hq0 : 0 < q := by rw [hq]; linarith
  have hA : 0 < ((1:ℝ) / (N : ℝ)) ^ α := Real.rpow_pos_of_pos (by positivity) α
  set A : ℝ := ((1:ℝ) / (N : ℝ)) ^ α with hAdef
  have hV1 : (0:ℝ) < 1 / q := by positivity
  have hfV1 : p ≤ finS α N (1 / q) := by
    have := pl_fi_one_sub_le hα hN hV1
    rw [one_div_one_div] at this
    linarith
  set a : ℝ := min (p * A) (1 / q / 2) with hadef
  have ha0 : 0 < a := lt_min (by positivity) (by positivity)
  have haV1 : a ≤ 1 / q := (min_le_right _ _).trans (by linarith)
  have hfa : finS α N a ≤ p := by
    have h1 := pl_fi_finS_le hα hN ha0
    rw [← hAdef] at h1
    have h2 : a / A ≤ p := by
      rw [div_le_iff₀ hA]
      exact min_le_left _ _
    linarith
  obtain ⟨V, hVmem, hVp⟩ : ∃ V ∈ Set.Icc a (1 / q), finS α N V = p := by
    have := intermediate_value_Icc haV1
      ((pl_fi_finS_contOn hα hN).mono (fun x hx => lt_of_lt_of_le ha0 hx.1))
    exact this ⟨hfa, hfV1⟩
  exact ⟨V, lt_of_lt_of_le ha0 hVmem.1, hVp⟩

private lemma pl_ii_phi_deriv {α : ℝ} (hα : 0 < α) (x : ℝ) :
    HasDerivAt (fun y => contS α (Real.exp y)) (Tcont α (Real.exp x)) x := by
  obtain ⟨c, C, hc, hC, hT⟩ := lem_app_pl_continuum_ii hα
  have hV : 0 < Real.exp x := Real.exp_pos x
  have hTpos : 0 < Tcont α (Real.exp x) := by
    have h1 := (hT _ hV).1
    have h2 := pl_contS_pos hα hV
    have h3 := pl_contS_lt_one hα hV
    have : 0 < c * (contS α (Real.exp x) * (1 - contS α (Real.exp x))) :=
      mul_pos hc (mul_pos h2 (by linarith))
    linarith
  have hderiv := eqn_app_pl_SN_T hα hV
  have hne : deriv (contS α) (Real.exp x) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hderiv
    linarith
  have hdiff : DifferentiableAt ℝ (contS α) (Real.exp x) := differentiableAt_of_deriv_ne_zero hne
  have h : HasDerivAt (fun y => contS α (Real.exp y)) _ x :=
    hdiff.hasDerivAt.comp x (Real.hasDerivAt_exp x)
  refine h.congr_deriv ?_
  rw [hderiv]; ring

private lemma pl_ii_core2 {α c p δ x y : ℝ} (hα : 0 < α)
    (hT : ∀ V : ℝ, 0 < V → c * (contS α V * (1 - contS α V)) ≤ Tcont α V)
    (hδ : δ ≤ (1 - p) / 2) (hxy : x < y)
    (hx1 : p ≤ contS α (Real.exp x)) (hx2 : contS α (Real.exp x) ≤ p + δ)
    (hy1 : p ≤ contS α (Real.exp y)) (hy2 : contS α (Real.exp y) ≤ p + δ) (hc : 0 < c) (hp0 : 0 < p) (hp1 : p < 1) :
    c * (p * (1 - p) / 2) * (y - x) ≤ δ := by
  have hcont : ContinuousOn (fun y => contS α (Real.exp y)) (Set.Icc x y) :=
    fun z _ => (pl_ii_phi_deriv hα z).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope (fun y => contS α (Real.exp y))
    (fun z => Tcont α (Real.exp z)) hxy hcont (fun z _ => pl_ii_phi_deriv hα z)
  have hm1 : contS α (Real.exp x) ≤ contS α (Real.exp ξ) :=
    pl_contS_monotoneOn hα (Set.mem_Ioi.2 (Real.exp_pos x)) (Set.mem_Ioi.2 (Real.exp_pos ξ))
      (Real.exp_le_exp.2 hξ.1.le)
  have hm2 : contS α (Real.exp ξ) ≤ contS α (Real.exp y) :=
    pl_contS_monotoneOn hα (Set.mem_Ioi.2 (Real.exp_pos ξ)) (Set.mem_Ioi.2 (Real.exp_pos y))
      (Real.exp_le_exp.2 hξ.2.le)
  set s := contS α (Real.exp ξ) with hs
  have hTξ := hT _ (Real.exp_pos ξ)
  rw [← hs] at hTξ
  have hlow : p * (1 - p) / 2 ≤ s * (1 - s) := by
    have h1 : (1 - p) / 2 ≤ 1 - s := by linarith
    have := mul_le_mul (hx1.trans hm1) h1 (by linarith) (by linarith)
    linarith
  have hyx : 0 < y - x := by linarith
  have hslope : Tcont α (Real.exp ξ) * (y - x) = contS α (Real.exp y) - contS α (Real.exp x) := by
    rw [hξd]; field_simp
  have hTge : c * (p * (1 - p) / 2) ≤ Tcont α (Real.exp ξ) :=
    (mul_le_mul_of_nonneg_left hlow hc.le).trans hTξ
  calc c * (p * (1 - p) / 2) * (y - x) ≤ Tcont α (Real.exp ξ) * (y - x) :=
        mul_le_mul_of_nonneg_right hTge hyx.le
    _ = _ := hslope
    _ ≤ δ := by linarith

/-- `lem:app-pl-finite-inverse` (snapshot `cr-2026-10-23`), part (ii), with `C = C(α)`, `M ≥ 1`, `B ≥ 2`, and the `p`-range. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Finite participation]\label{lem:app-pl-finite-inverse}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item $0\le S_\alpha(V)-S_N(V)\le1/N$ and $\abs{VS_N'(V)-\mathsf T(V)}\le1/(2N)$ for $V>0$.
\item There is $C$ such that, for $M\ge1$, $B\ge2$ and $M/\gamma\le p\le1-M/\gamma$,
\[
\Big|\log\frac{V_N(p)}{V_\alpha(p)}\Big|\le\frac{C}{BM}.
\]
\item $V_N(p)\asymp(1-p)^{-1}$ for $p\ge1/2$, uniformly in $N$.
\item If $\alpha>1$, $Bm\to\infty$ and $m/\gamma\to0$, then $c_N\Lambda_N(m)\sim(Bm/K_\alpha)^\alpha$ and
$m\Lambda_N'(m)/\Lambda_N(m)\to\alpha$, locally uniformly in $m$ on compact subsets of $(0,\infty)$ when
$m$ is held fixed.
\item If $\alpha>1$, then $c_N\Lambda_N(m)\asymp(Bm)^\alpha$ for $1/B\le m\le\gamma/2$ and
$c_N\Lambda_N(m)\asymp Bm$ for $0<m\le1/B$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_finite_inverse_ii {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, ∀ (N B : ℕ) (M p : ℝ), 0 < N → 2 ≤ B → 1 ≤ M →
      M / gammaOf N B ≤ p → p ≤ 1 - M / gammaOf N B →
      |Real.log (finV α N p / contV α p)| ≤ C / ((B : ℝ) * M) := by
  obtain ⟨c, C0, hc, hC0, hT⟩ := lem_app_pl_continuum_ii hα
  refine ⟨4 / c, ?_⟩
  intro N B M p hN hB hM h1 h2
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hBr : (0:ℝ) < (B:ℝ) := by positivity
  have hB2 : (2:ℝ) ≤ (B:ℝ) := by exact_mod_cast hB
  have hγ : 0 < gammaOf N B := by unfold gammaOf; positivity
  have hM0 : 0 < M := by linarith
  have hMγ0 : 0 < M / gammaOf N B := div_pos hM0 hγ
  have hp0 : 0 < p := lt_of_lt_of_le hMγ0 h1
  have hp1 : p < 1 := by linarith
  have hK2 : (2:ℝ) ≤ (B:ℝ) * M := by nlinarith
  have hK0 : 0 < (B:ℝ) * M := by linarith
  have hBMp : (B:ℝ) * M ≤ p * N := by
    rw [div_le_iff₀ hγ] at h1
    unfold gammaOf at h1
    have : p * ((N:ℝ) / B) * B = p * N := by field_simp
    nlinarith
  have hBMq : (B:ℝ) * M ≤ (1 - p) * N := by
    have h3 : M / gammaOf N B ≤ 1 - p := by linarith
    rw [div_le_iff₀ hγ] at h3
    unfold gammaOf at h3
    have : (1 - p) * ((N:ℝ) / B) * B = (1 - p) * N := by field_simp
    nlinarith
  have hδp : 1 / (N:ℝ) ≤ p / ((B:ℝ) * M) := by
    rw [div_le_div_iff₀ hNr hK0]; linarith
  have hδq : 1 / (N:ℝ) ≤ (1 - p) / ((B:ℝ) * M) := by
    rw [div_le_div_iff₀ hNr hK0]; linarith
  have hδ2 : 1 / (N:ℝ) ≤ 2 * (p * (1 - p)) / ((B:ℝ) * M) := by
    rcases le_total p (1 / 2) with hh | hh
    · refine hδp.trans (div_le_div_of_nonneg_right ?_ hK0.le)
      nlinarith
    · refine hδq.trans (div_le_div_of_nonneg_right ?_ hK0.le)
      nlinarith
  have hδhalf : 1 / (N:ℝ) ≤ (1 - p) / 2 := by
    refine hδq.trans ?_
    exact div_le_div_of_nonneg_left (by linarith) (by norm_num) hK2
  -- the two inverses
  obtain ⟨V0, hV0pos, hV0S⟩ := pl_ii_exists_cont (α := α) hα hp0 hp1
  obtain ⟨W, hWpos, hWS⟩ := pl_ii_exists_fin (α := α) (N := N) hα hN hp0 hp1
  have hmem : p ∈ contS α '' Set.Ioi 0 := ⟨V0, hV0pos, hV0S⟩
  obtain ⟨hVpos, hVS⟩ := pl_contV_spec hmem
  rw [pl_finV_of_eq α hN hWpos hWS]
  set V := contV α p with hVdef
  have hiA := lem_app_pl_finite_inverse_i_a hα hN W hWpos
  rw [hWS] at hiA
  have hW1 : p ≤ contS α W := by linarith [hiA.1]
  have hW2 : contS α W ≤ p + 1 / (N:ℝ) := by linarith [hiA.2]
  have hlogV : Real.exp (Real.log V) = V := Real.exp_log hVpos
  have hlogW : Real.exp (Real.log W) = W := Real.exp_log hWpos
  have hD : c * (p * (1 - p) / 2) * |Real.log W - Real.log V| ≤ 1 / (N:ℝ) := by
    rcases lt_trichotomy (Real.log V) (Real.log W) with hlt | heq | hgt
    · have := pl_ii_core2 (α := α) (c := c) (p := p) (δ := 1 / (N:ℝ)) (x := Real.log V)
        (y := Real.log W) hα (fun V hV => (hT V hV).1) hδhalf hlt
        (by rw [hlogV, hVS]) (by rw [hlogV, hVS]; linarith [one_div_pos.2 hNr])
        (by rw [hlogW]; exact hW1) (by rw [hlogW]; exact hW2) hc hp0 hp1
      rwa [abs_of_pos (by linarith)]
    · rw [heq, sub_self, abs_zero, mul_zero]; positivity
    · have := pl_ii_core2 (α := α) (c := c) (p := p) (δ := 1 / (N:ℝ)) (x := Real.log W)
        (y := Real.log V) hα (fun V hV => (hT V hV).1) hδhalf hgt
        (by rw [hlogW]; exact hW1) (by rw [hlogW]; exact hW2)
        (by rw [hlogV, hVS]) (by rw [hlogV, hVS]; linarith [one_div_pos.2 hNr]) hc hp0 hp1
      rw [abs_of_neg (by linarith)]
      linarith
  rw [Real.log_div hWpos.ne' hVpos.ne']
  set D := |Real.log W - Real.log V| with hDdef
  have hD0 : 0 ≤ D := abs_nonneg _
  have hpq : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
  rw [le_div_iff₀ hK0]
  have h5 : c * (p * (1 - p) / 2) * D ≤ 2 * (p * (1 - p)) / ((B:ℝ) * M) := hD.trans hδ2
  rw [le_div_iff₀ hK0] at h5
  rw [le_div_iff₀ hc] at *
  nlinarith

/-- `lem:app-pl-finite-inverse` (snapshot `cr-2026-10-23`), part (iii), `V_N(p) ≍ (1-p)^{-1}` for `p ≥ 1/2`, uniformly in `N`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Finite participation]\label{lem:app-pl-finite-inverse}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item $0\le S_\alpha(V)-S_N(V)\le1/N$ and $\abs{VS_N'(V)-\mathsf T(V)}\le1/(2N)$ for $V>0$.
\item There is $C$ such that, for $M\ge1$, $B\ge2$ and $M/\gamma\le p\le1-M/\gamma$,
\[
\Big|\log\frac{V_N(p)}{V_\alpha(p)}\Big|\le\frac{C}{BM}.
\]
\item $V_N(p)\asymp(1-p)^{-1}$ for $p\ge1/2$, uniformly in $N$.
\item If $\alpha>1$, $Bm\to\infty$ and $m/\gamma\to0$, then $c_N\Lambda_N(m)\sim(Bm/K_\alpha)^\alpha$ and
$m\Lambda_N'(m)/\Lambda_N(m)\to\alpha$, locally uniformly in $m$ on compact subsets of $(0,\infty)$ when
$m$ is held fixed.
\item If $\alpha>1$, then $c_N\Lambda_N(m)\asymp(Bm)^\alpha$ for $1/B\le m\le\gamma/2$ and
$c_N\Lambda_N(m)\asymp Bm$ for $0<m\le1/B$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_finite_inverse_iii {α : ℝ} (hα : 0 < α) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ p : ℝ, 1 / 2 ≤ p → p < 1 →
      c / (1 - p) ≤ finV α N p ∧ finV α N p ≤ C / (1 - p) := by
  have h4 : (0:ℝ) < (4:ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  set m : ℝ := 1 / (4 * (4:ℝ) ^ α) with hm
  have hm0 : 0 < m := by positivity
  have hα1 : (0:ℝ) < 2 * (α + 1) := by linarith
  refine ⟨m / (2 * (α + 1)), 1, by positivity, one_pos, ?_⟩
  intro N hN p hp hp1
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  set q : ℝ := 1 - p with hq
  have hq0 : 0 < q := by rw [hq]; linarith
  have hq1 : q ≤ 1 / 2 := by rw [hq]; linarith
  have hA : 0 < ((1:ℝ) / (N : ℝ)) ^ α := Real.rpow_pos_of_pos (by positivity) α
  set A : ℝ := ((1:ℝ) / (N : ℝ)) ^ α with hAdef
  have hV1 : (0:ℝ) < 1 / q := by positivity
  have hfV1 : p ≤ finS α N (1 / q) := by
    have := pl_fi_one_sub_le hα hN hV1
    rw [one_div_one_div] at this
    linarith
  set a : ℝ := min (p * A) (1 / q / 2) with hadef
  have ha0 : 0 < a := lt_min (by positivity) (by positivity)
  have haV1 : a ≤ 1 / q := (min_le_right _ _).trans (by linarith)
  have hfa : finS α N a ≤ p := by
    have h1 := pl_fi_finS_le hα hN ha0
    rw [← hAdef] at h1
    have h2 : a / A ≤ p := by
      rw [div_le_iff₀ hA]
      exact min_le_left _ _
    linarith
  obtain ⟨V, hVmem, hVp⟩ : ∃ V ∈ Set.Icc a (1 / q), finS α N V = p := by
    have := intermediate_value_Icc haV1
      ((pl_fi_finS_contOn hα hN).mono (fun x hx => lt_of_lt_of_le ha0 hx.1))
    exact this ⟨hfa, hfV1⟩
  have hV0 : 0 < V := lt_of_lt_of_le ha0 hVmem.1
  rw [pl_finV_of_eq α hN hV0 hVp]
  have hVup : V ≤ 1 / q := hVmem.2
  have hup : q ≤ 1 / V := by
    have := pl_fi_one_sub_le hα hN hV0
    rw [hVp] at this
    exact this
  have hiA := lem_app_pl_finite_inverse_i_a hα hN V hV0
  have hlow := pl_one_sub_ge hα hV0
  have hSle := pl_S_le hα hV0
  have hlow2 : 1 / (2 * (α + 1) * max V 1) ≤ q := by
    have : 1 - contS α V ≤ q := by
      rw [hq, ← hVp]; linarith [hiA.1]
    linarith
  refine ⟨?_, ?_⟩
  · have hm1 : m ≤ 1 := by
      have h41 : (1:ℝ) ≤ (4:ℝ) ^ α := Real.one_le_rpow (by norm_num) hα.le
      rw [hm, div_le_one (by positivity)]
      linarith
    rw [div_le_iff₀ hq0, div_le_iff₀ hα1]
    rcases le_total 1 V with hV1' | hV1'
    · rw [max_eq_left hV1'] at hlow2
      rw [div_le_iff₀ (by positivity)] at hlow2
      nlinarith
    · rw [max_eq_right hV1', mul_one, div_le_iff₀ hα1] at hlow2
      have hVm : m ≤ V := by
        rw [hm, div_le_iff₀ (by positivity)]
        have hpS : p ≤ contS α V := by rw [← hVp]; linarith [hiA.1]
        nlinarith
      nlinarith
  · rw [le_div_iff₀ hq0]
    rw [le_div_iff₀ hV0] at hup
    linarith

/-! ### Helpers for part (v), first range -/

private lemma pl_vi_S_le_a {α V a : ℝ} (hα1 : 1 < α) (hV : 0 < V) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    contS α V ≤ a + V * a ^ (1 - α) / (α - 1) := by
  have hα0 : 0 < α := by linarith
  have h1 := pl_s_ii hα0 hV (a := 0) (b := a) le_rfl ha0.le
  have h2 := pl_s_ii hα0 hV (a := a) (b := 1) ha0.le zero_le_one
  have hsplit : contS α V = (∫ t in (0:ℝ)..a, V / (V + t ^ α)) +
      ∫ t in a..1, V / (V + t ^ α) :=
    (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
  have hA : ∫ t in (0:ℝ)..a, V / (V + t ^ α) ≤ a := by
    have := intervalIntegral.integral_mono_on ha0.le h1
      (intervalIntegrable_const (c := (1:ℝ)))
      (fun t ht => (pl_cont_s_le_one hα0 hV (Set.Icc_subset_uIcc
        (by exact ⟨ht.1, by linarith [ht.2]⟩ : t ∈ Set.Icc (0:ℝ) 1))).2)
    simpa using this
  have hint : IntervalIntegrable (fun t : ℝ => V * t ^ (-α)) volume a 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    intro t ht
    rw [Set.uIcc_of_le ha1] at ht
    exact (Real.continuousAt_rpow_const t (-α) (Or.inl (by linarith [ht.1]))).continuousWithinAt
  have hB : ∫ t in a..1, V / (V + t ^ α) ≤ ∫ t in a..1, V * t ^ (-α) := by
    apply intervalIntegral.integral_mono_on ha1 h2 hint
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha0 ht.1
    have hp : 0 < t ^ α := Real.rpow_pos_of_pos ht0 α
    rw [Real.rpow_neg ht0.le, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hV.le hp (by linarith)
  have hC : ∫ t in a..1, V * t ^ (-α) = V * ((1 - a ^ (1 - α)) / (1 - α)) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by linarith, ?_⟩)]
    · have : -α + 1 = 1 - α := by ring
      rw [this, Real.one_rpow]
    · intro h
      rw [Set.uIcc_of_le ha1] at h
      linarith [h.1]
  have hD : V * ((1 - a ^ (1 - α)) / (1 - α)) ≤ V * a ^ (1 - α) / (α - 1) := by
    have hpos : 0 < a ^ (1 - α) := Real.rpow_pos_of_pos ha0 _
    have hα' : 0 < α - 1 := by linarith
    have : (1 - a ^ (1 - α)) / (1 - α) = (a ^ (1 - α) - 1) / (α - 1) := by
      rw [← neg_sub α 1, div_neg, ← neg_div, neg_sub]
    rw [this, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hα'.le
    nlinarith
  linarith

private lemma pl_vi_S_upper {α V : ℝ} (hα1 : 1 < α) (hV : 0 < V) :
    contS α V ≤ α / (α - 1) * V ^ (1 / α) := by
  have hα0 : 0 < α := by linarith
  have hα' : 0 < α - 1 := by linarith
  have hC1 : 1 ≤ α / (α - 1) := by rw [le_div_iff₀ hα']; linarith
  set a : ℝ := V ^ (1 / α) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hV _
  have haV : a ^ α = V := by
    rw [ha, ← Real.rpow_mul hV.le, one_div_mul_cancel hα0.ne', Real.rpow_one]
  rcases le_or_gt 1 a with h1 | h1
  · have := pl_contS_lt_one hα0 hV
    nlinarith
  · have := pl_vi_S_le_a hα1 hV ha0 h1.le
    have e : V * a ^ (1 - α) = a := by
      rw [← haV, ← Real.rpow_add ha0]
      simp
    rw [e] at this
    have e2 : a + a / (α - 1) = α / (α - 1) * a := by field_simp; ring
    linarith

private lemma pl_vi_S_lower {α V : ℝ} (hα0 : 0 < α) (hV : 0 < V) (hV2 : V ≤ 2) :
    2 / 3 * (V / 2) ^ (1 / α) ≤ contS α V := by
  set b : ℝ := (V / 2) ^ (1 / α) with hb
  have hV2' : 0 < V / 2 := by positivity
  have hb0 : 0 < b := Real.rpow_pos_of_pos hV2' _
  have hbV : b ^ α = V / 2 := by
    rw [hb, ← Real.rpow_mul hV2'.le, one_div_mul_cancel hα0.ne', Real.rpow_one]
  have hb1 : b ≤ 1 := by
    by_contra h
    push_neg at h
    have : 1 < b ^ α := Real.one_lt_rpow h hα0
    linarith
  have h1 := pl_s_ii hα0 hV (a := 0) (b := b) le_rfl hb0.le
  have h2 := pl_s_ii hα0 hV (a := b) (b := 1) hb0.le zero_le_one
  have hsplit : contS α V = (∫ t in (0:ℝ)..b, V / (V + t ^ α)) +
      ∫ t in b..1, V / (V + t ^ α) :=
    (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
  have hB : 0 ≤ ∫ t in b..1, V / (V + t ^ α) := by
    apply intervalIntegral.integral_nonneg hb1
    intro t ht
    exact (pl_cont_s_le_one hα0 hV (Set.Icc_subset_uIcc
      (by exact ⟨hb0.le.trans ht.1, ht.2⟩ : t ∈ Set.Icc (0:ℝ) 1))).1
  have hA : 2 / 3 * b ≤ ∫ t in (0:ℝ)..b, V / (V + t ^ α) := by
    have := intervalIntegral.integral_mono_on hb0.le
      (intervalIntegrable_const (c := (2 / 3 : ℝ))) h1
      (fun t ht => by
        have h0 : 0 ≤ t ^ α := Real.rpow_nonneg ht.1 α
        have hle : t ^ α ≤ V / 2 := by
          rw [← hbV]; exact Real.rpow_le_rpow ht.1 ht.2 hα0.le
        rw [div_le_div_iff₀ (by norm_num) (by linarith)]
        linarith)
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
    linarith
  linarith

private lemma pl_vi_W_bounds {α p W : ℝ} {N : ℕ} (hα1 : 1 < α) (hN : 0 < N) (hW : 0 < W)
    (hWS : finS α N W = p) (hp1 : 1 / (N : ℝ) ≤ p) (hp2 : p ≤ 1 / 2) :
    (p / (α / (α - 1))) ^ α ≤ W ∧ W ≤ 2 * 3 ^ α * p ^ α := by
  have hα0 : 0 < α := by linarith
  have hα' : 0 < α - 1 := by linarith
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hCpos : 0 < α / (α - 1) := by positivity
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp1
  have hiA := lem_app_pl_finite_inverse_i_a hα0 hN W hW
  rw [hWS] at hiA
  have hrt : (W ^ (1 / α)) ^ α = W := by
    rw [← Real.rpow_mul hW.le, one_div_mul_cancel hα0.ne', Real.rpow_one]
  constructor
  · have h := pl_vi_S_upper hα1 hW
    have h2 : p / (α / (α - 1)) ≤ W ^ (1 / α) := by
      rw [div_le_iff₀ hCpos]; linarith [hiA.1]
    calc (p / (α / (α - 1))) ^ α ≤ (W ^ (1 / α)) ^ α :=
          Real.rpow_le_rpow (by positivity) h2 hα0.le
      _ = W := hrt
  · have hW2 : W ≤ 2 := by
      have := pl_fi_one_sub_le hα0 hN hW
      rw [hWS] at this
      have h3 : 1 / 2 ≤ 1 / W := by linarith
      rw [div_le_div_iff₀ (by norm_num) hW] at h3
      linarith
    have h := pl_vi_S_lower hα0 hW hW2
    have h2 : (W / 2) ^ (1 / α) ≤ 3 * p := by
      have : 2 / 3 * (W / 2) ^ (1 / α) ≤ 2 * p := by
        have : 1 / (N:ℝ) ≤ p := hp1
        linarith [hiA.2]
      linarith
    have h3 : W / 2 ≤ (3 * p) ^ α := by
      calc W / 2 = ((W / 2) ^ (1 / α)) ^ α := by
            rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hα0.ne', Real.rpow_one]
        _ ≤ (3 * p) ^ α := Real.rpow_le_rpow (by positivity) h2 hα0.le
    rw [Real.mul_rpow (by norm_num) hp0.le] at h3
    nlinarith

private lemma pl_fv_ratio_small {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, ∀ (N B : ℕ) (M p : ℝ), 0 < N → (2:ℝ) ≤ (B:ℝ) → 0 < M → (2:ℝ) ≤ (B:ℝ) * M →
      M / gammaOf N B ≤ p → p ≤ 1 - M / gammaOf N B →
      |Real.log (finV α N p / contV α p)| ≤ C / ((B : ℝ) * M) := by
  obtain ⟨c, C0, hc, hC0, hT⟩ := lem_app_pl_continuum_ii hα
  refine ⟨4 / c, ?_⟩
  intro N B M p hN hB hM0 hK2 h1 h2
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hBr : (0:ℝ) < (B:ℝ) := by linarith
  have hB2 : (2:ℝ) ≤ (B:ℝ) := hB
  have hγ : 0 < gammaOf N B := by unfold gammaOf; positivity
  have hMγ0 : 0 < M / gammaOf N B := div_pos hM0 hγ
  have hp0 : 0 < p := lt_of_lt_of_le hMγ0 h1
  have hp1 : p < 1 := by linarith
  have hK0 : 0 < (B:ℝ) * M := by linarith
  have hBMp : (B:ℝ) * M ≤ p * N := by
    rw [div_le_iff₀ hγ] at h1
    unfold gammaOf at h1
    have : p * ((N:ℝ) / B) * B = p * N := by field_simp
    nlinarith
  have hBMq : (B:ℝ) * M ≤ (1 - p) * N := by
    have h3 : M / gammaOf N B ≤ 1 - p := by linarith
    rw [div_le_iff₀ hγ] at h3
    unfold gammaOf at h3
    have : (1 - p) * ((N:ℝ) / B) * B = (1 - p) * N := by field_simp
    nlinarith
  have hδp : 1 / (N:ℝ) ≤ p / ((B:ℝ) * M) := by
    rw [div_le_div_iff₀ hNr hK0]; linarith
  have hδq : 1 / (N:ℝ) ≤ (1 - p) / ((B:ℝ) * M) := by
    rw [div_le_div_iff₀ hNr hK0]; linarith
  have hδ2 : 1 / (N:ℝ) ≤ 2 * (p * (1 - p)) / ((B:ℝ) * M) := by
    rcases le_total p (1 / 2) with hh | hh
    · refine hδp.trans (div_le_div_of_nonneg_right ?_ hK0.le)
      nlinarith
    · refine hδq.trans (div_le_div_of_nonneg_right ?_ hK0.le)
      nlinarith
  have hδhalf : 1 / (N:ℝ) ≤ (1 - p) / 2 := by
    refine hδq.trans ?_
    exact div_le_div_of_nonneg_left (by linarith) (by norm_num) hK2
  -- the two inverses
  obtain ⟨V0, hV0pos, hV0S⟩ := pl_ii_exists_cont (α := α) hα hp0 hp1
  obtain ⟨W, hWpos, hWS⟩ := pl_ii_exists_fin (α := α) (N := N) hα hN hp0 hp1
  have hmem : p ∈ contS α '' Set.Ioi 0 := ⟨V0, hV0pos, hV0S⟩
  obtain ⟨hVpos, hVS⟩ := pl_contV_spec hmem
  rw [pl_finV_of_eq α hN hWpos hWS]
  set V := contV α p with hVdef
  have hiA := lem_app_pl_finite_inverse_i_a hα hN W hWpos
  rw [hWS] at hiA
  have hW1 : p ≤ contS α W := by linarith [hiA.1]
  have hW2 : contS α W ≤ p + 1 / (N:ℝ) := by linarith [hiA.2]
  have hlogV : Real.exp (Real.log V) = V := Real.exp_log hVpos
  have hlogW : Real.exp (Real.log W) = W := Real.exp_log hWpos
  have hD : c * (p * (1 - p) / 2) * |Real.log W - Real.log V| ≤ 1 / (N:ℝ) := by
    rcases lt_trichotomy (Real.log V) (Real.log W) with hlt | heq | hgt
    · have := pl_ii_core2 (α := α) (c := c) (p := p) (δ := 1 / (N:ℝ)) (x := Real.log V)
        (y := Real.log W) hα (fun V hV => (hT V hV).1) hδhalf hlt
        (by rw [hlogV, hVS]) (by rw [hlogV, hVS]; linarith [one_div_pos.2 hNr])
        (by rw [hlogW]; exact hW1) (by rw [hlogW]; exact hW2) hc hp0 hp1
      rwa [abs_of_pos (by linarith)]
    · rw [heq, sub_self, abs_zero, mul_zero]; positivity
    · have := pl_ii_core2 (α := α) (c := c) (p := p) (δ := 1 / (N:ℝ)) (x := Real.log W)
        (y := Real.log V) hα (fun V hV => (hT V hV).1) hδhalf hgt
        (by rw [hlogW]; exact hW1) (by rw [hlogW]; exact hW2)
        (by rw [hlogV, hVS]) (by rw [hlogV, hVS]; linarith [one_div_pos.2 hNr]) hc hp0 hp1
      rw [abs_of_neg (by linarith)]
      linarith
  rw [Real.log_div hWpos.ne' hVpos.ne']
  set D := |Real.log W - Real.log V| with hDdef
  have hD0 : 0 ≤ D := abs_nonneg _
  have hpq : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
  rw [le_div_iff₀ hK0]
  have h5 : c * (p * (1 - p) / 2) * D ≤ 2 * (p * (1 - p)) / ((B:ℝ) * M) := hD.trans hδ2
  rw [le_div_iff₀ hK0] at h5
  rw [le_div_iff₀ hc] at *
  nlinarith

/-- `lem:app-pl-finite-inverse` (snapshot `cr-2026-10-23`), part (iii), `V_N(p) ≍ (1-p)^{-1}` for `p ≥ 1/2`, uniformly in `N`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Finite participation]\label{lem:app-pl-finite-inverse}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item $0\le S_\alpha(V)-S_N(V)\le1/N$ and $\abs{VS_N'(V)-\mathsf T(V)}\le1/(2N)$ for $V>0$.
\item There is $C$ such that, for $M\ge1$, $B\ge2$ and $M/\gamma\le p\le1-M/\gamma$,
\[
\Big|\log\frac{V_N(p)}{V_\alpha(p)}\Big|\le\frac{C}{BM}.
\]
\item $V_N(p)\asymp(1-p)^{-1}$ for $p\ge1/2$, uniformly in $N$.
\item If $\alpha>1$, $Bm\to\infty$ and $m/\gamma\to0$, then $c_N\Lambda_N(m)\sim(Bm/K_\alpha)^\alpha$ and
$m\Lambda_N'(m)/\Lambda_N(m)\to\alpha$, locally uniformly in $m$ on compact subsets of $(0,\infty)$ when
$m$ is held fixed.
\item If $\alpha>1$, then $c_N\Lambda_N(m)\asymp(Bm)^\alpha$ for $1/B\le m\le\gamma/2$ and
$c_N\Lambda_N(m)\asymp Bm$ for $0<m\le1/B$.
\end{enumerate}
\end{lemma}
-/

private lemma pl_fv_pos_cv_pos {α : ℝ} {N : ℕ} (hα : 0 < α) (hN : 0 < N) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) : 0 < finV α N p ∧ 0 < contV α p := by
  obtain ⟨W, hW, hWS⟩ := pl_ii_exists_fin (α := α) (N := N) hα hN hp0 hp1
  obtain ⟨V, hV, hVS⟩ := pl_ii_exists_cont (α := α) hα hp0 hp1
  have h1 := pl_finV_of_eq α hN hW hWS
  have h2 := (pl_contV_spec ⟨V, hV, hVS⟩).1
  exact ⟨by rw [h1]; exact hW, h2⟩

/-- `lem:app-pl-finite-inverse` (snapshot `cr-2026-10-23`), part (iv), first limit, along a row sequence with `Bm → ∞`, `m/γ → 0`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Finite participation]\label{lem:app-pl-finite-inverse}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item $0\le S_\alpha(V)-S_N(V)\le1/N$ and $\abs{VS_N'(V)-\mathsf T(V)}\le1/(2N)$ for $V>0$.
\item There is $C$ such that, for $M\ge1$, $B\ge2$ and $M/\gamma\le p\le1-M/\gamma$,
\[
\Big|\log\frac{V_N(p)}{V_\alpha(p)}\Big|\le\frac{C}{BM}.
\]
\item $V_N(p)\asymp(1-p)^{-1}$ for $p\ge1/2$, uniformly in $N$.
\item If $\alpha>1$, $Bm\to\infty$ and $m/\gamma\to0$, then $c_N\Lambda_N(m)\sim(Bm/K_\alpha)^\alpha$ and
$m\Lambda_N'(m)/\Lambda_N(m)\to\alpha$, locally uniformly in $m$ on compact subsets of $(0,\infty)$ when
$m$ is held fixed.
\item If $\alpha>1$, then $c_N\Lambda_N(m)\asymp(Bm)^\alpha$ for $1/B\le m\le\gamma/2$ and
$c_N\Lambda_N(m)\asymp Bm$ for $0<m\le1/B$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_finite_inverse_iv_i {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (m : ℕ → ℝ)
    (hBm : Tendsto (fun n => ((B n : ℕ) : ℝ) * m n) atTop atTop)
    (hmγ : Tendsto (fun n => m n / gammaOf (N n) (B n)) atTop (𝓝 0)) :
    IsEquivalent atTop (fun n => c n * partLam (B n) (plSpec α (c n) (N n)) (m n))
      (fun n => (((B n : ℕ) : ℝ) * m n / Kc α) ^ α) := by
  have hα : 0 < α := by linarith
  have hNr : ∀ n, (0:ℝ) < (N n : ℝ) := fun n => by exact_mod_cast R.hNpos n
  have hBr : ∀ n, (0:ℝ) < (B n : ℝ) := fun n => by exact_mod_cast R.hBpos n
  have hγ : ∀ n, 0 < gammaOf (N n) (B n) := fun n => by
    unfold gammaOf; exact div_pos (hNr n) (hBr n)
  have hKc : 0 < Kc α := by
    unfold Kc
    have hsin : 0 < Real.sin (Real.pi / α) :=
      Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos hα) (div_lt_self Real.pi_pos hα1)
    exact div_pos Real.pi_pos (mul_pos hα hsin)
  have hBm0 : ∀ᶠ n in atTop, (2:ℝ) ≤ (B n : ℝ) * m n := hBm.eventually_ge_atTop 2
  have hB2 : ∀ᶠ n in atTop, (2:ℝ) ≤ (B n : ℝ) := R.hB.eventually_ge_atTop 2
  have hmpos : ∀ᶠ n in atTop, 0 < m n := by
    filter_upwards [hBm0] with n hn
    by_contra h
    push_neg at h
    nlinarith [hBr n]
  have hp_tend : Tendsto (fun n => m n / gammaOf (N n) (B n)) atTop (𝓝 0) := hmγ
  have hppos : ∀ᶠ n in atTop, 0 < m n / gammaOf (N n) (B n) := by
    filter_upwards [hmpos] with n hn
    exact div_pos hn (hγ n)
  have hp_half : ∀ᶠ n in atTop, m n / gammaOf (N n) (B n) < 1 / 2 :=
    hp_tend.eventually (gt_mem_nhds (by norm_num))
  have hp_within : Tendsto (fun n => m n / gammaOf (N n) (B n)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hp_tend, by filter_upwards [hppos] with n hn; exact hn⟩
  obtain ⟨C, hC⟩ := pl_fv_ratio_small (α := α) hα
  have hlog : Tendsto (fun n => Real.log (finV α (N n) (m n / gammaOf (N n) (B n)) /
      contV α (m n / gammaOf (N n) (B n)))) atTop (𝓝 0) := by
    have hbound : Tendsto (fun n => C / ((B n : ℝ) * m n)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hBm
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hBm0, hB2, hmpos, hp_half, hppos] with n hn2 hB2n hmn hph hpn
    rw [Real.norm_eq_abs]
    exact hC (N n) (B n) (m n) (m n / gammaOf (N n) (B n)) (R.hNpos n) hB2n hmn hn2
      le_rfl (by linarith)
  have hratio : Tendsto (fun n => finV α (N n) (m n / gammaOf (N n) (B n)) /
      contV α (m n / gammaOf (N n) (B n))) atTop (𝓝 1) := by
    have hexp := (Real.continuous_exp.tendsto 0).comp hlog
    rw [Real.exp_zero] at hexp
    apply hexp.congr'
    filter_upwards [hppos, hp_half] with n hn hh
    obtain ⟨h1, h2⟩ := pl_fv_pos_cv_pos hα (R.hNpos n) hn (by linarith)
    simp only [Function.comp_apply]
    rw [Real.exp_log (div_pos h1 h2)]
  have hcontV : (fun n => contV α (m n / gammaOf (N n) (B n))) ~[atTop]
      (fun n => (m n / gammaOf (N n) (B n) / Kc α) ^ α) :=
    (lem_app_pl_continuum_iii_gt hα1).comp_tendsto hp_within
  have hfinV : (fun n => finV α (N n) (m n / gammaOf (N n) (B n))) ~[atTop]
      (fun n => contV α (m n / gammaOf (N n) (B n))) :=
    isEquivalent_of_tendsto_one hratio
  have hpv := hfinV.trans hcontV
  have hscaled : (fun n => (N n : ℝ) ^ α * finV α (N n) (m n / gammaOf (N n) (B n))) ~[atTop]
      (fun n => (N n : ℝ) ^ α * (m n / gammaOf (N n) (B n) / Kc α) ^ α) :=
    IsEquivalent.mul IsEquivalent.refl hpv
  have hAeq : (fun n => (N n : ℝ) ^ α * finV α (N n) (m n / gammaOf (N n) (B n)))
      =ᶠ[atTop] (fun n => c n * partLam (B n) (plSpec α (c n) (N n)) (m n)) := by
    filter_upwards [hmpos, hp_half] with n hn hh
    have hm : m n ∈ Ioo 0 (gammaOf (N n) (B n)) :=
      ⟨hn, (div_lt_one (hγ n)).1 (by linarith)⟩
    rw [eqn_app_pl_Lambda_V (α := α) (c := c n) (N := N n) (B := B n) (R.hNpos n)
      (R.hBpos n) (R.hcpos n) hm]
    have := (R.hcpos n).ne'
    field_simp
  have hBeq : (fun n => (N n : ℝ) ^ α * (m n / gammaOf (N n) (B n) / Kc α) ^ α)
      =ᶠ[atTop] (fun n => ((B n : ℝ) * m n / Kc α) ^ α) := by
    filter_upwards [hmpos] with n hn
    have hkey : (B n : ℝ) * m n / Kc α = (N n : ℝ) * (m n / gammaOf (N n) (B n) / Kc α) := by
      unfold gammaOf
      have := (hNr n).ne'
      have := (hBr n).ne'
      have := hKc.ne'
      field_simp
    rw [hkey, Real.mul_rpow (hNr n).le (div_nonneg (div_nonneg hn.le (hγ n).le) hKc.le)]
  exact (hscaled.congr_left hAeq).congr_right hBeq

/-! ### Helpers for part (iv), second limit -/

private lemma pl_iv_T_ibp {α V : ℝ} (hα0 : 0 < α) (hV : 0 < V) :
    α * Tcont α V = contS α V - V / (V + 1) := by
  set f : ℝ → ℝ := fun t => t * (V / (V + t ^ α)) with hf
  set f' : ℝ → ℝ := fun t => V / (V + t ^ α) - α * (V * t ^ α / (V + t ^ α) ^ 2) with hf'
  have hS := pl_s_ii hα0 hV (a := 0) (b := 1) le_rfl zero_le_one
  have hTint : IntervalIntegrable (fun t : ℝ => V * t ^ α / (V + t ^ α) ^ 2) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · exact (continuous_const.mul (Real.continuous_rpow_const hα0.le)).continuousOn
    · exact ((continuous_const.add (Real.continuous_rpow_const hα0.le)).pow 2).continuousOn
    · intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      have h0 : 0 ≤ t ^ α := Real.rpow_nonneg ht.1 α
      exact (pow_pos (by linarith : (0:ℝ) < V + t ^ α) 2).ne'
  have hint : IntervalIntegrable f' volume 0 1 := hS.sub (hTint.const_mul α)
  have hcont : ContinuousOn f (Set.Icc 0 1) := by
    apply continuousOn_id.mul
    exact (pl_cont_s_contOn hα0 hV).mono (by rw [Set.uIcc_of_le zero_le_one])
  have hder : ∀ t ∈ Set.Ioo (0:ℝ) 1, HasDerivAt f (f' t) t := by
    intro t ht
    have h0 : 0 < t := ht.1
    have hp : 0 < t ^ α := Real.rpow_pos_of_pos h0 α
    have hne : V + t ^ α ≠ 0 := by linarith
    have hden : HasDerivAt (fun t : ℝ => V + t ^ α) (α * t ^ (α - 1)) t :=
      (Real.hasDerivAt_rpow_const (Or.inl h0.ne')).const_add V
    have hq := (hasDerivAt_const t V).div hden hne
    have h := (hasDerivAt_id t).mul hq
    refine h.congr_deriv ?_
    simp only [id, hf', Pi.div_apply]
    rw [Real.rpow_sub_one h0.ne']
    field_simp
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hder hint
  have h1 : f 1 - f 0 = V / (V + 1) := by
    simp [hf]
  have h2 : ∫ t in (0:ℝ)..1, f' t = contS α V - α * Tcont α V := by
    simp only [hf']
    rw [intervalIntegral.integral_sub hS (hTint.const_mul α), intervalIntegral.integral_const_mul]
    rfl
  linarith

private lemma pl_iv_finS_hasDeriv {α V : ℝ} {N : ℕ} (hα : 0 < α) (hN : 0 < N) (hV : 0 < V) :
    ∃ D : ℝ, 0 < D ∧ HasDerivAt (finS α N) D V := by
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hterm : ∀ j ∈ Finset.Icc 1 N, HasDerivAt (fun W : ℝ => W / (W + ((j:ℝ) / (N:ℝ)) ^ α))
      (((j:ℝ) / (N:ℝ)) ^ α / (V + ((j:ℝ) / (N:ℝ)) ^ α) ^ 2) V := by
    intro j hj
    have hj' := Finset.mem_Icc.1 hj
    have hj0 : (0:ℝ) < (j:ℝ) := by exact_mod_cast (by omega : 0 < j)
    have ha0 : 0 ≤ ((j:ℝ) / (N:ℝ)) ^ α := Real.rpow_nonneg (div_pos hj0 hNr).le α
    have hne : V + ((j:ℝ) / (N:ℝ)) ^ α ≠ 0 := by linarith
    have h := (hasDerivAt_id V).div ((hasDerivAt_id V).add_const (((j:ℝ) / (N:ℝ)) ^ α)) hne
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  refine ⟨(N:ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 N, ((j:ℝ) / (N:ℝ)) ^ α / (V + ((j:ℝ) / (N:ℝ)) ^ α) ^ 2, ?_, ?_⟩
  · apply mul_pos (inv_pos.2 hNr)
    apply Finset.sum_pos
    · intro j hj
      have hj' := Finset.mem_Icc.1 hj
      have hj0 : (0:ℝ) < (j:ℝ) := by exact_mod_cast (by omega : 0 < j)
      have ha : 0 < ((j:ℝ) / (N:ℝ)) ^ α := Real.rpow_pos_of_pos (div_pos hj0 hNr) α
      positivity
    · exact ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hN⟩⟩
  · unfold finS
    exact (HasDerivAt.fun_sum hterm).const_mul _

private lemma pl_iv_finS_pos {α V : ℝ} {N : ℕ} (hN : 0 < N) (hV : 0 < V) : 0 < finS α N V := by
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  unfold finS
  apply mul_pos (inv_pos.2 hNr)
  apply Finset.sum_pos
  · intro j hj
    have hj' := Finset.mem_Icc.1 hj
    have hj0 : (0:ℝ) < (j:ℝ) := by exact_mod_cast (by omega : 0 < j)
    have ha : 0 ≤ ((j:ℝ) / (N:ℝ)) ^ α := Real.rpow_nonneg (div_pos hj0 hNr).le α
    exact div_pos hV (by linarith)
  · exact ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hN⟩⟩

private lemma pl_iv_finV_hasDeriv {α p : ℝ} {N : ℕ} (hα : 0 < α) (hN : 0 < N) (hp0 : 0 < p)
    (hp1 : p < 1) :
    ∃ W D : ℝ, 0 < W ∧ 0 < D ∧ finS α N W = p ∧ finV α N p = W ∧
      HasDerivAt (finS α N) D W ∧ HasDerivAt (finV α N) D⁻¹ p := by
  obtain ⟨W, hW, hWS⟩ := pl_ii_exists_fin (α := α) (N := N) hα hN hp0 hp1
  obtain ⟨D, hD, hDd⟩ := pl_iv_finS_hasDeriv hα hN hW
  have hfV : finV α N p = W := pl_finV_of_eq α hN hW hWS
  have hmem : ∀ y : ℝ, 0 < y → y < 1 → 0 < finV α N y ∧ finS α N (finV α N y) = y := by
    intro y hy0 hy1
    obtain ⟨V, hV, hVS⟩ := pl_ii_exists_fin (α := α) (N := N) hα hN hy0 hy1
    rw [pl_finV_of_eq α hN hV hVS]
    exact ⟨hV, hVS⟩
  have hmono : MonotoneOn (finV α N) (Set.Ioo 0 1) := by
    intro a ha b hb hab
    obtain ⟨h1, h2⟩ := hmem a ha.1 ha.2
    obtain ⟨h3, h4⟩ := hmem b hb.1 hb.2
    rw [← (pl_finS_strictMonoOn α hN).le_iff_le (Set.mem_Ioi.2 h1) (Set.mem_Ioi.2 h3), h2, h4]
    exact hab
  have hcont : ContinuousAt (finV α N) p := by
    apply continuousAt_of_monotoneOn_of_image_mem_nhds hmono
    · exact Ioo_mem_nhds hp0 hp1
    · rw [hfV]
      apply mem_of_superset (Ioi_mem_nhds hW)
      intro y hy
      have hy' : (0:ℝ) < y := hy
      have hlt : finS α N y < 1 := by
        have := lem_app_pl_finite_inverse_i_a hα hN y hy'
        linarith [pl_contS_lt_one hα hy', this.1]
      refine ⟨finS α N y, ⟨pl_iv_finS_pos hN hy', hlt⟩, ?_⟩
      exact pl_finV_of_eq α hN hy' rfl
  refine ⟨W, D, hW, hD, hWS, hfV, hDd, ?_⟩
  apply HasDerivAt.of_local_left_inverse hcont (by rw [hfV]; exact hDd) hD.ne'
  filter_upwards [Ioo_mem_nhds hp0 hp1] with y hy
  exact (hmem y hy.1 hy.2).2

private lemma pl_iv_pt {α : ℝ} (hα1 : 1 < α) {N B : ℕ} {c m : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (hm0 : 0 < m) (hp2 : m / gammaOf N B ≤ 1 / 2)
    (hp1 : 1 / (N : ℝ) ≤ m / gammaOf N B) :
    0 < m * deriv (partLam B (plSpec α c N)) m / partLam B (plSpec α c N) m ∧
      |α / (m * deriv (partLam B (plSpec α c N)) m / partLam B (plSpec α c N) m) - 1| ≤
        (1 + α / 2) * (1 / ((B : ℝ) * m)) + 2 * 3 ^ α * (m / gammaOf N B) ^ (α - 1) := by
  have hα0 : 0 < α := by linarith
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hBr : (0:ℝ) < (B:ℝ) := by exact_mod_cast hB
  have hγ : 0 < gammaOf N B := by unfold gammaOf; positivity
  have hmγ : m ∈ Ioo 0 (gammaOf N B) := ⟨hm0, by linarith [(div_le_iff₀ hγ).1 hp2]⟩
  set p : ℝ := m / gammaOf N B with hp
  have hp0 : 0 < p := by positivity
  have hpe : p = m * B / N := by rw [hp]; unfold gammaOf; field_simp
  obtain ⟨W, D, hW, hD, hWS, hfV, hDd, hVd⟩ :=
    pl_iv_finV_hasDeriv (α := α) (N := N) hα0 hN hp0 (by linarith)
  -- derivative of Λ
  have hev : partLam B (plSpec α c N) =ᶠ[𝓝 m]
      fun m' => (N : ℝ) ^ α / c * finV α N (m' / gammaOf N B) := by
    filter_upwards [Ioo_mem_nhds hmγ.1 hmγ.2] with m' hm'
    exact eqn_app_pl_Lambda_V (N := N) (B := B) α c hN hB hc hm'
  have hin : HasDerivAt (fun m' : ℝ => m' / gammaOf N B) (1 / gammaOf N B) m := by
    simpa using (hasDerivAt_id m).div_const (gammaOf N B)
  have hcomp : HasDerivAt (fun m' => (N : ℝ) ^ α / c * finV α N (m' / gammaOf N B))
      ((N : ℝ) ^ α / c * (D⁻¹ * (1 / gammaOf N B))) m := by
    have h := HasDerivAt.comp m (by rw [← hp]; exact hVd : HasDerivAt (finV α N) D⁻¹ (m / gammaOf N B)) hin
    exact h.const_mul _
  have hder : deriv (partLam B (plSpec α c N)) m = (N : ℝ) ^ α / c * (D⁻¹ * (1 / gammaOf N B)) := by
    rw [hev.deriv_eq]; exact hcomp.deriv
  have hLam : partLam B (plSpec α c N) m = (N : ℝ) ^ α / c * W := by
    rw [eqn_app_pl_Lambda_V (N := N) (B := B) α c hN hB hc hmγ, ← hp, hfV]
  have hNa : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hNr α
  have hg : m * deriv (partLam B (plSpec α c N)) m / partLam B (plSpec α c N) m = p / (W * D) := by
    rw [hder, hLam, hp]
    field_simp
  -- estimate of X = W D
  have hiA := lem_app_pl_finite_inverse_i_a hα0 hN W hW
  rw [hWS] at hiA
  have hib := lem_app_pl_finite_inverse_i_b hα0 hN W hW
  rw [hDd.deriv] at hib
  have hT := pl_iv_T_ibp hα0 hW
  have hWb := (pl_vi_W_bounds hα1 hN hW hWS hp1 hp2).2
  have hWle : W / (W + 1) ≤ W := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hWpos : 0 < W / (W + 1) := by positivity
  have habs := abs_le.1 hib
  have hE : |α * (W * D) - p| ≤ (1 + α / 2) * (1 / (N:ℝ)) + 2 * 3 ^ α * p ^ α := by
    rw [abs_le]
    have h3 : α * (W * D - Tcont α W) ≤ α * (1 / (2 * (N:ℝ))) :=
      mul_le_mul_of_nonneg_left habs.2 hα0.le
    have h4 : α * (-(1 / (2 * (N:ℝ)))) ≤ α * (W * D - Tcont α W) :=
      mul_le_mul_of_nonneg_left habs.1 hα0.le
    have e1 : α * (1 / (2 * (N:ℝ))) = α / 2 * (1 / (N:ℝ)) := by field_simp
    constructor <;> nlinarith [hiA.1, hiA.2]
  have hX : 0 < W * D := mul_pos hW hD
  rw [hg]
  refine ⟨div_pos hp0 hX, ?_⟩
  have : α / (p / (W * D)) - 1 = (α * (W * D) - p) / p := by field_simp
  rw [this, abs_div, abs_of_pos hp0, div_le_iff₀ hp0]
  have e2 : ((1 + α / 2) * (1 / ((B:ℝ) * m)) + 2 * 3 ^ α * p ^ (α - 1)) * p
      = (1 + α / 2) * (1 / (N:ℝ)) + 2 * 3 ^ α * p ^ α := by
    rw [Real.rpow_sub_one hp0.ne']
    rw [hpe]
    field_simp
  rw [e2]
  exact hE

/-- `lem:app-pl-finite-inverse` (snapshot `cr-2026-10-23`), part (iv), second limit `m Λ_N'(m)/Λ_N(m) → α`, along the same sequences. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Finite participation]\label{lem:app-pl-finite-inverse}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item $0\le S_\alpha(V)-S_N(V)\le1/N$ and $\abs{VS_N'(V)-\mathsf T(V)}\le1/(2N)$ for $V>0$.
\item There is $C$ such that, for $M\ge1$, $B\ge2$ and $M/\gamma\le p\le1-M/\gamma$,
\[
\Big|\log\frac{V_N(p)}{V_\alpha(p)}\Big|\le\frac{C}{BM}.
\]
\item $V_N(p)\asymp(1-p)^{-1}$ for $p\ge1/2$, uniformly in $N$.
\item If $\alpha>1$, $Bm\to\infty$ and $m/\gamma\to0$, then $c_N\Lambda_N(m)\sim(Bm/K_\alpha)^\alpha$ and
$m\Lambda_N'(m)/\Lambda_N(m)\to\alpha$, locally uniformly in $m$ on compact subsets of $(0,\infty)$ when
$m$ is held fixed.
\item If $\alpha>1$, then $c_N\Lambda_N(m)\asymp(Bm)^\alpha$ for $1/B\le m\le\gamma/2$ and
$c_N\Lambda_N(m)\asymp Bm$ for $0<m\le1/B$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_finite_inverse_iv_ii {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) (m : ℕ → ℝ)
    (hBm : Tendsto (fun n => ((B n : ℕ) : ℝ) * m n) atTop atTop)
    (hmγ : Tendsto (fun n => m n / gammaOf (N n) (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => m n * deriv (partLam (B n) (plSpec α (c n) (N n))) (m n) /
      partLam (B n) (plSpec α (c n) (N n)) (m n)) atTop (𝓝 α) := by
  have hα : 0 < α := by linarith
  have hNr : ∀ n, (0:ℝ) < (N n : ℝ) := fun n => by exact_mod_cast R.hNpos n
  have hBr : ∀ n, (0:ℝ) < (B n : ℝ) := fun n => by exact_mod_cast R.hBpos n
  have hγ : ∀ n, 0 < gammaOf (N n) (B n) := fun n => by
    unfold gammaOf; exact div_pos (hNr n) (hBr n)
  have hBm1 : ∀ᶠ n in atTop, (1:ℝ) ≤ (B n : ℝ) * m n := hBm.eventually_ge_atTop 1
  have hmpos : ∀ᶠ n in atTop, 0 < m n := by
    filter_upwards [hBm1] with n hn
    by_contra h
    push_neg at h
    nlinarith [hBr n]
  have hp_half : ∀ᶠ n in atTop, m n / gammaOf (N n) (B n) ≤ 1 / 2 :=
    hmγ.eventually (ge_mem_nhds (by norm_num))
  have hpt : ∀ᶠ n in atTop,
      0 < m n * deriv (partLam (B n) (plSpec α (c n) (N n))) (m n) /
        partLam (B n) (plSpec α (c n) (N n)) (m n) ∧
      |α / (m n * deriv (partLam (B n) (plSpec α (c n) (N n))) (m n) /
        partLam (B n) (plSpec α (c n) (N n)) (m n)) - 1| ≤
        (1 + α / 2) * (1 / ((B n : ℝ) * m n)) +
          2 * 3 ^ α * (m n / gammaOf (N n) (B n)) ^ (α - 1) := by
    filter_upwards [hBm1, hmpos, hp_half] with n h1 h2 h3
    have hp1 : 1 / (N n : ℝ) ≤ m n / gammaOf (N n) (B n) := by
      have : m n / gammaOf (N n) (B n) = m n * B n / N n := by
        unfold gammaOf; have := (hBr n).ne'; field_simp
      rw [this]
      exact div_le_div_of_nonneg_right (by linarith) (hNr n).le
    exact pl_iv_pt (α := α) hα1 (R.hNpos n) (R.hBpos n) (R.hcpos n) h2 h3 hp1
  have hε : Tendsto (fun n => (1 + α / 2) * (1 / ((B n : ℝ) * m n)) +
      2 * 3 ^ α * (m n / gammaOf (N n) (B n)) ^ (α - 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => 1 / ((B n : ℝ) * m n)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hBm
    have h2 : Tendsto (fun n => (m n / gammaOf (N n) (B n)) ^ (α - 1)) atTop (𝓝 0) := by
      have hc : ContinuousAt (fun x : ℝ => x ^ (α - 1)) 0 :=
        Real.continuousAt_rpow_const 0 (α - 1) (Or.inr (by linarith))
      have := hc.tendsto.comp hmγ
      rwa [Real.zero_rpow (by linarith)] at this
    simpa using (h1.const_mul (1 + α / 2)).add (h2.const_mul (2 * 3 ^ α))
  have hdiff : Tendsto (fun n => α / (m n * deriv (partLam (B n) (plSpec α (c n) (N n))) (m n) /
      partLam (B n) (plSpec α (c n) (N n)) (m n))) atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm' ?_ hε
    filter_upwards [hpt] with n hn
    rw [norm_norm, Real.norm_eq_abs]
    exact hn.2
  have := (tendsto_const_nhds (x := α)).div hdiff one_ne_zero
  rw [div_one] at this
  refine this.congr' ?_
  filter_upwards [hpt] with n hn
  have hne := hn.1.ne'
  simp only [Pi.div_apply]
  generalize m n * deriv (partLam (B n) (plSpec α (c n) (N n))) (m n) /
    partLam (B n) (plSpec α (c n) (N n)) (m n) = g at hne ⊢
  field_simp

/-- Uniform convergence on a set from convergence along every sequence in the set. -/
private lemma pl_unif_of_seq {F : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {K : Set ℝ}
    (h : ∀ z : ℕ → ℝ, (∀ n, z n ∈ K) → Tendsto (fun n => dist (g (z n)) (F n (z n))) atTop (𝓝 0)) :
    TendstoUniformlyOn F g atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hcon
  have hfreq : ∃ᶠ n in atTop, ∃ x ∈ K, ε ≤ dist (g x) (F n x) := by
    refine (Filter.not_eventually.1 hcon).mono ?_
    intro n hn
    push_neg at hn
    exact hn
  obtain ⟨_, x0, hx0, -⟩ := hfreq.exists
  have hch : ∀ n, ∃ x : ℝ, x ∈ K ∧ ((∃ y ∈ K, ε ≤ dist (g y) (F n y)) → ε ≤ dist (g x) (F n x)) := by
    intro n
    by_cases hP : ∃ y ∈ K, ε ≤ dist (g y) (F n y)
    · obtain ⟨y, hy, hyε⟩ := hP
      exact ⟨y, hy, fun _ => hyε⟩
    · exact ⟨x0, hx0, fun h' => absurd h' hP⟩
  choose z hzK hzε using hch
  have hev := Metric.tendsto_nhds.1 (h z hzK) ε hε
  have hev' : ∀ᶠ n in atTop, dist (g (z n)) (F n (z n)) < ε := by
    filter_upwards [hev] with n hn
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] at hn
  have hfr : ∃ᶠ n in atTop, ε ≤ dist (g (z n)) (F n (z n)) :=
    hfreq.mono (fun n hn => hzε n hn)
  obtain ⟨_, h1, h2⟩ := (hfr.and_eventually hev').exists
  linarith

/-- Sequence-level bounds for points of a compact `K ⊆ (0,∞)`: `B_n z_n → ∞` and `z_n/γ_n → 0`. -/
private lemma pl_iv_seq_bounds {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) {K : Set ℝ} (hK : IsCompact K) (hKpos : K ⊆ Ioi 0)
    {z : ℕ → ℝ} (hz : ∀ n, z n ∈ K) :
    Tendsto (fun n => ((B n : ℕ) : ℝ) * z n) atTop atTop ∧
      Tendsto (fun n => z n / gammaOf (N n) (B n)) atTop (𝓝 0) := by
  obtain ⟨x0, hx0K, hmin⟩ := hK.exists_isMinOn ⟨z 0, hz 0⟩ continuousOn_id
  have hδ : 0 < x0 := Set.mem_Ioi.1 (hKpos hx0K)
  obtain ⟨M, hM⟩ := hK.bddAbove
  constructor
  · have h1 : Tendsto (fun n => x0 * ((B n : ℕ) : ℝ)) atTop atTop := R.hB.const_mul_atTop hδ
    refine tendsto_atTop_mono (fun n => ?_) h1
    have hBn : (0:ℝ) ≤ ((B n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hzn : x0 ≤ z n := isMinOn_iff.1 hmin (z n) (hz n)
    nlinarith
  · have hγpos : ∀ n, 0 < gammaOf (N n) (B n) := fun n => by
      unfold gammaOf
      exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)
    have hγ' : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop := R.hγ
    have hlim : Tendsto (fun n => M / gammaOf (N n) (B n)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hγ'
    refine squeeze_zero (fun n => div_nonneg (Set.mem_Ioi.1 (hKpos (hz n))).le (hγpos n).le)
      (fun n => div_le_div_of_nonneg_right (hM (hz n)) (hγpos n).le) hlim

/-- `lem:app-pl-finite-inverse` (snapshot `cr-2026-10-23`), part (iv), the locally uniform form: for each compact `K ⊆ (0,∞)` both limits hold uniformly in `m ∈ K`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Finite participation]\label{lem:app-pl-finite-inverse}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item $0\le S_\alpha(V)-S_N(V)\le1/N$ and $\abs{VS_N'(V)-\mathsf T(V)}\le1/(2N)$ for $V>0$.
\item There is $C$ such that, for $M\ge1$, $B\ge2$ and $M/\gamma\le p\le1-M/\gamma$,
\[
\Big|\log\frac{V_N(p)}{V_\alpha(p)}\Big|\le\frac{C}{BM}.
\]
\item $V_N(p)\asymp(1-p)^{-1}$ for $p\ge1/2$, uniformly in $N$.
\item If $\alpha>1$, $Bm\to\infty$ and $m/\gamma\to0$, then $c_N\Lambda_N(m)\sim(Bm/K_\alpha)^\alpha$ and
$m\Lambda_N'(m)/\Lambda_N(m)\to\alpha$, locally uniformly in $m$ on compact subsets of $(0,\infty)$ when
$m$ is held fixed.
\item If $\alpha>1$, then $c_N\Lambda_N(m)\asymp(Bm)^\alpha$ for $1/B\le m\le\gamma/2$ and
$c_N\Lambda_N(m)\asymp Bm$ for $0<m\le1/B$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_finite_inverse_iv_iii {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) :
    ∀ K : Set ℝ, IsCompact K → K ⊆ Ioi 0 →
      TendstoUniformlyOn
          (fun n m => c n * partLam (B n) (plSpec α (c n) (N n)) m /
            (((B n : ℕ) : ℝ) * m / Kc α) ^ α) (fun _ => (1 : ℝ)) atTop K ∧
        TendstoUniformlyOn
          (fun n m => m * deriv (partLam (B n) (plSpec α (c n) (N n))) m /
            partLam (B n) (plSpec α (c n) (N n)) m) (fun _ => α) atTop K := by
  have hα0 : 0 < α := R.hα
  have hKc : 0 < Kc α := by
    unfold Kc
    have hsin : 0 < Real.sin (Real.pi / α) :=
      Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos hα0) (div_lt_self Real.pi_pos hα1)
    exact div_pos Real.pi_pos (mul_pos hα0 hsin)
  intro K hK hKpos
  refine ⟨pl_unif_of_seq ?_, pl_unif_of_seq ?_⟩
  · intro z hz
    obtain ⟨hBm, hmγ⟩ := pl_iv_seq_bounds R hK hKpos hz
    have hi := lem_app_pl_finite_inverse_iv_i R hα1 z hBm hmγ
    have hv : ∀ n, (((B n : ℕ) : ℝ) * z n / Kc α) ^ α ≠ 0 := fun n =>
      ne_of_gt (Real.rpow_pos_of_pos
        (div_pos (mul_pos (by exact_mod_cast R.hBpos n) (Set.mem_Ioi.1 (hKpos (hz n)))) hKc) α)
    have hlim := (isEquivalent_iff_tendsto_one (Filter.Eventually.of_forall hv)).1 hi
    exact (tendsto_iff_dist_tendsto_zero.1 hlim).congr (fun n => dist_comm _ _)
  · intro z hz
    obtain ⟨hBm, hmγ⟩ := pl_iv_seq_bounds R hK hKpos hz
    have hii := lem_app_pl_finite_inverse_iv_ii R hα1 z hBm hmγ
    exact (tendsto_iff_dist_tendsto_zero.1 hii).congr (fun n => dist_comm _ _)

/-- `lem:app-pl-finite-inverse` (snapshot `cr-2026-10-23`), part (v), first range `1/B ≤ m ≤ γ/2`, `c_N Λ_N(m) ≍ (Bm)^α`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Finite participation]\label{lem:app-pl-finite-inverse}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item $0\le S_\alpha(V)-S_N(V)\le1/N$ and $\abs{VS_N'(V)-\mathsf T(V)}\le1/(2N)$ for $V>0$.
\item There is $C$ such that, for $M\ge1$, $B\ge2$ and $M/\gamma\le p\le1-M/\gamma$,
\[
\Big|\log\frac{V_N(p)}{V_\alpha(p)}\Big|\le\frac{C}{BM}.
\]
\item $V_N(p)\asymp(1-p)^{-1}$ for $p\ge1/2$, uniformly in $N$.
\item If $\alpha>1$, $Bm\to\infty$ and $m/\gamma\to0$, then $c_N\Lambda_N(m)\sim(Bm/K_\alpha)^\alpha$ and
$m\Lambda_N'(m)/\Lambda_N(m)\to\alpha$, locally uniformly in $m$ on compact subsets of $(0,\infty)$ when
$m$ is held fixed.
\item If $\alpha>1$, then $c_N\Lambda_N(m)\asymp(Bm)^\alpha$ for $1/B\le m\le\gamma/2$ and
$c_N\Lambda_N(m)\asymp Bm$ for $0<m\le1/B$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_finite_inverse_v_i {α : ℝ} (hα1 : 1 < α) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ (N B : ℕ) (c m : ℝ), 0 < N → 0 < B → 0 < c →
      1 / (B : ℝ) ≤ m → m ≤ gammaOf N B / 2 →
      C₁ * ((B : ℝ) * m) ^ α ≤ c * partLam B (plSpec α c N) m ∧
        c * partLam B (plSpec α c N) m ≤ C₂ * ((B : ℝ) * m) ^ α := by
  have hα0 : 0 < α := by linarith
  have hα' : 0 < α - 1 := by linarith
  have hCpos : 0 < α / (α - 1) := by positivity
  refine ⟨1 / (α / (α - 1)) ^ α, 2 * 3 ^ α, by positivity, by positivity, ?_⟩
  intro N B c m hN hB hc h1 h2
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hBr : (0:ℝ) < (B:ℝ) := by exact_mod_cast hB
  have hγ : 0 < gammaOf N B := by unfold gammaOf; positivity
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) h1
  have hmγ : m ∈ Ioo 0 (gammaOf N B) := ⟨hm0, by linarith⟩
  set p : ℝ := m / gammaOf N B with hp
  have hpe : p = m * B / N := by
    rw [hp]; unfold gammaOf; field_simp
  have hp0 : 0 < p := by positivity
  have hp2 : p ≤ 1 / 2 := by
    rw [hp, div_le_iff₀ hγ]; linarith
  have hp1 : 1 / (N:ℝ) ≤ p := by
    rw [hpe]
    apply div_le_div_of_nonneg_right _ hNr.le
    have : 1 / (B:ℝ) * B = 1 := by field_simp
    nlinarith
  obtain ⟨W, hWpos, hWS⟩ := pl_ii_exists_fin (α := α) (N := N) hα0 hN hp0 (by linarith)
  obtain ⟨hlo, hhi⟩ := pl_vi_W_bounds hα1 hN hWpos hWS hp1 hp2
  have hΛ := eqn_app_pl_Lambda_V (N := N) (B := B) α c hN hB hc hmγ
  rw [← hp, pl_finV_of_eq α hN hWpos hWS] at hΛ
  have hcΛ : c * partLam B (plSpec α c N) m = (N:ℝ) ^ α * W := by
    rw [hΛ]; field_simp
  have hBm : (B:ℝ) * m = p * N := by rw [hpe]; field_simp
  have hNa : 0 < (N:ℝ) ^ α := Real.rpow_pos_of_pos hNr α
  rw [hcΛ, hBm, Real.mul_rpow hp0.le hNr.le]
  rw [Real.div_rpow hp0.le hCpos.le] at hlo
  constructor
  · calc 1 / (α / (α - 1)) ^ α * (p ^ α * (N:ℝ) ^ α)
        = (p ^ α / (α / (α - 1)) ^ α) * (N:ℝ) ^ α := by ring
      _ ≤ W * (N:ℝ) ^ α := mul_le_mul_of_nonneg_right hlo hNa.le
      _ = _ := by ring
  · calc (N:ℝ) ^ α * W ≤ (N:ℝ) ^ α * (2 * 3 ^ α * p ^ α) :=
          mul_le_mul_of_nonneg_left hhi hNa.le
      _ = _ := by ring

private lemma pl_vii_summable {α : ℝ} (hα1 : 1 < α) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-α)) := by
  have h : Summable (fun n : ℕ => (n : ℝ) ^ (-α)) := Real.summable_nat_rpow.2 (by linarith)
  have h2 := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-α)) 1).2 h
  simpa using h2

private lemma pl_vii_T_pos {α : ℝ} (hα1 : 1 < α) :
    0 < ∑' n : ℕ, ((n : ℝ) + 1) ^ (-α) := by
  have h1 : ∑ n ∈ Finset.range 1, ((n : ℝ) + 1) ^ (-α) ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (-α) :=
    Summable.sum_le_tsum _ (fun i _ => (Real.rpow_pos_of_pos (by positivity) _).le)
      (pl_vii_summable hα1)
  rw [Finset.sum_range_one] at h1
  norm_num at h1
  linarith

/-- Real-variable core of part (v), second range: with `s = B m` and `y = c Λ`, the equation
`s = ∑_i y a_i/(1 + y a_i)`, `a_i = (i+1)^{-α}`, gives `s ≤ T y` and `y ≤ 2·2^{α+1} s`. -/
private lemma pl_vii_core {α : ℝ} (hα1 : 1 < α) {N : ℕ} (hN : 0 < N) {y s : ℝ} (hy : 0 < y)
    (hs1 : s ≤ 1) (hsN : s ≤ (N : ℝ) / 2)
    (hs : s = ∑ i : Fin N, y * ((((i : ℕ) : ℝ) + 1) ^ (-α)) / (1 + y * ((((i : ℕ) : ℝ) + 1) ^ (-α)))) :
    s ≤ (∑' n : ℕ, ((n : ℝ) + 1) ^ (-α)) * y ∧ y ≤ 2 * 2 ^ (α + 1) * s := by
  have hapos : ∀ i : Fin N, 0 < (((i : ℕ) : ℝ) + 1) ^ (-α) := fun i =>
    Real.rpow_pos_of_pos (by positivity) _
  have hterm_nn : ∀ i : Fin N, 0 ≤ y * ((((i : ℕ) : ℝ) + 1) ^ (-α)) /
      (1 + y * ((((i : ℕ) : ℝ) + 1) ^ (-α))) := fun i => by
    have h1 := mul_pos hy (hapos i)
    exact div_nonneg h1.le (by linarith)
  have hT : ∑ i : Fin N, (((i : ℕ) : ℝ) + 1) ^ (-α) ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (-α) := by
    have e := Fin.sum_univ_eq_sum_range (fun n : ℕ => ((n : ℝ) + 1) ^ (-α)) N
    rw [e]
    exact Summable.sum_le_tsum _ (fun i _ => (Real.rpow_pos_of_pos (by positivity) _).le)
      (pl_vii_summable hα1)
  have hb1 : s ≤ y * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-α) := by
    rw [hs]
    calc ∑ i : Fin N, y * ((((i : ℕ) : ℝ) + 1) ^ (-α)) / (1 + y * ((((i : ℕ) : ℝ) + 1) ^ (-α)))
        ≤ ∑ i : Fin N, y * ((((i : ℕ) : ℝ) + 1) ^ (-α)) := by
          apply Finset.sum_le_sum
          intro i _
          have h1 := mul_pos hy (hapos i)
          exact div_le_self h1.le (by linarith)
      _ = y * ∑ i : Fin N, (((i : ℕ) : ℝ) + 1) ^ (-α) := by rw [Finset.mul_sum]
      _ ≤ y * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-α) := mul_le_mul_of_nonneg_left hT hy.le
  refine ⟨by linarith [hb1, mul_comm y (∑' n : ℕ, ((n : ℝ) + 1) ^ (-α))], ?_⟩
  have hi0 : ((((⟨0, hN⟩ : Fin N) : ℕ) : ℝ) + 1) ^ (-α) = 1 := by norm_num
  have e0 : y * ((((⟨0, hN⟩ : Fin N) : ℕ) : ℝ) + 1) ^ (-α) /
      (1 + y * ((((⟨0, hN⟩ : Fin N) : ℕ) : ℝ) + 1) ^ (-α)) = y / (1 + y) := by
    rw [hi0, mul_one]
  have hsge0 : y / (1 + y) ≤ s := by
    rw [hs, ← e0]
    exact Finset.single_le_sum (f := fun i : Fin N => y * ((((i : ℕ) : ℝ) + 1) ^ (-α)) /
      (1 + y * ((((i : ℕ) : ℝ) + 1) ^ (-α)))) (fun i _ => hterm_nn i) (Finset.mem_univ _)
  have hK1 : (1:ℝ) ≤ 2 ^ (α + 1) := Real.one_le_rpow (by norm_num) (by linarith)
  rcases le_total y 1 with hy1 | hy1
  · have hhalf : y / 2 ≤ y / (1 + y) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      nlinarith
    have hs0 : 0 ≤ s := le_trans (div_pos hy (by linarith)).le hsge0
    nlinarith [mul_nonneg (sub_nonneg.2 hK1) hs0]
  · have hhalf : 1 / 2 ≤ s := by
      have : 1 / 2 ≤ y / (1 + y) := by
        rw [div_le_div_iff₀ (by norm_num) (by linarith)]
        linarith
      linarith
    have hylt : y < 2 ^ (α + 1) := by
      by_contra hcon
      push_neg at hcon
      rcases Nat.lt_or_ge N 2 with hN2 | hN2
      · have hN1 : N = 1 := by omega
        have hNs : (N : ℝ) / 2 = 1 / 2 := by rw [hN1]; norm_num
        have hK3 : (1:ℝ) < 2 ^ (α + 1) := Real.one_lt_rpow (by norm_num) (by linarith)
        have : 1 / 2 < y / (1 + y) := by
          rw [div_lt_div_iff₀ (by norm_num) (by linarith)]
          linarith
        linarith
      · have hi1 : ((((⟨1, by omega⟩ : Fin N) : ℕ) : ℝ) + 1) ^ (-α) = (2 : ℝ) ^ (-α) := by
          norm_num
        have hne : (⟨0, hN⟩ : Fin N) ≠ ⟨1, by omega⟩ := by
          intro h
          have := congrArg Fin.val h
          simp at this
        have hpair : ∑ i ∈ ({(⟨0, hN⟩ : Fin N), ⟨1, by omega⟩} : Finset (Fin N)),
            y * ((((i : ℕ) : ℝ) + 1) ^ (-α)) / (1 + y * ((((i : ℕ) : ℝ) + 1) ^ (-α))) ≤ s := by
          rw [hs]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => hterm_nn i)
        rw [Finset.sum_pair hne, hi0, hi1] at hpair
        have hX1 : (0 : ℝ) ≤ (2 : ℝ) ^ (-α) := by positivity
        have hK2 : (2 : ℝ) ^ (α + 1) * (2 : ℝ) ^ (-α) = 2 := by
          rw [← Real.rpow_add (by norm_num)]
          have : α + 1 + -α = 1 := by ring
          rw [this, Real.rpow_one]
        have ht : (2 : ℝ) ^ (α + 1) * (2 : ℝ) ^ (-α) ≤ y * (2 : ℝ) ^ (-α) :=
          mul_le_mul_of_nonneg_right hcon hX1
        rw [hK2] at ht
        have hA : 1 / 2 ≤ y * 1 / (1 + y * 1) := by
          rw [mul_one, le_div_iff₀ (by linarith)]
          linarith
        have hB : 2 / 3 ≤ y * (2 : ℝ) ^ (-α) / (1 + y * (2 : ℝ) ^ (-α)) := by
          rw [le_div_iff₀ (by nlinarith)]
          linarith
        linarith
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 ^ (α + 1)) (by linarith : (0:ℝ) ≤ 2 * s - 1)]

/-- `lem:app-pl-finite-inverse` (snapshot `cr-2026-10-23`), part (v), second range `0 < m ≤ 1/B`, `c_N Λ_N(m) ≍ Bm`; the extra `m < γ` is the domain of `Λ_N`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Finite participation]\label{lem:app-pl-finite-inverse}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item $0\le S_\alpha(V)-S_N(V)\le1/N$ and $\abs{VS_N'(V)-\mathsf T(V)}\le1/(2N)$ for $V>0$.
\item There is $C$ such that, for $M\ge1$, $B\ge2$ and $M/\gamma\le p\le1-M/\gamma$,
\[
\Big|\log\frac{V_N(p)}{V_\alpha(p)}\Big|\le\frac{C}{BM}.
\]
\item $V_N(p)\asymp(1-p)^{-1}$ for $p\ge1/2$, uniformly in $N$.
\item If $\alpha>1$, $Bm\to\infty$ and $m/\gamma\to0$, then $c_N\Lambda_N(m)\sim(Bm/K_\alpha)^\alpha$ and
$m\Lambda_N'(m)/\Lambda_N(m)\to\alpha$, locally uniformly in $m$ on compact subsets of $(0,\infty)$ when
$m$ is held fixed.
\item If $\alpha>1$, then $c_N\Lambda_N(m)\asymp(Bm)^\alpha$ for $1/B\le m\le\gamma/2$ and
$c_N\Lambda_N(m)\asymp Bm$ for $0<m\le1/B$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_finite_inverse_v_ii {α : ℝ} (hα1 : 1 < α) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ (N B : ℕ) (c m : ℝ), 0 < N → 0 < B → 0 < c →
      0 < m → m ≤ 1 / (B : ℝ) → m ≤ gammaOf N B / 2 →
      C₁ * ((B : ℝ) * m) ≤ c * partLam B (plSpec α c N) m ∧
        c * partLam B (plSpec α c N) m ≤ C₂ * ((B : ℝ) * m) := by
  have hTpos := pl_vii_T_pos hα1
  refine ⟨1 / (∑' n : ℕ, ((n : ℝ) + 1) ^ (-α)), 2 * 2 ^ (α + 1), div_pos one_pos hTpos,
    by positivity, ?_⟩
  intro N B c m hN hB hc hm0 h1 h2
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hBr : (0:ℝ) < (B:ℝ) := by exact_mod_cast hB
  have hγ : 0 < gammaOf N B := by unfold gammaOf; exact div_pos hNr hBr
  have hmγ : m ∈ Ioo 0 (gammaOf N B) := ⟨hm0, by linarith⟩
  have hpos : ∀ i, 0 < plSpec α c N i := fun i => by
    simp only [plSpec]
    exact mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)
  have hsurj : ∃ a ∈ Ioi (0:ℝ), partMN B (plSpec α c N) a = m :=
    (def_app_pl_participation_bij (plSpec α c N) hB hN hpos).1.surjOn hmγ
  have hL : partMN B (plSpec α c N) (partLam B (plSpec α c N) m) = m :=
    Function.invFunOn_eq hsurj
  have hLpos : partLam B (plSpec α c N) m ∈ Ioi (0:ℝ) := Function.invFunOn_mem hsurj
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ, Λ = partLam B (plSpec α c N) m := ⟨_, rfl⟩
  rw [← hΛdef] at hL hLpos ⊢
  have hΛpos : 0 < Λ := hLpos
  have hS : ∑ i : Fin N, Λ * plSpec α c N i / (1 + Λ * plSpec α c N i) = B * m := by
    have h := hL
    unfold partMN at h
    rw [← h, mul_inv_cancel_left₀ hBr.ne']
  have hterm : ∀ i : Fin N, Λ * plSpec α c N i / (1 + Λ * plSpec α c N i) =
      (c * Λ) * (((i : ℕ) : ℝ) + 1) ^ (-α) / (1 + (c * Λ) * (((i : ℕ) : ℝ) + 1) ^ (-α)) := by
    intro i
    simp only [plSpec]
    rw [show Λ * (c * ((((i : ℕ) : ℝ) + 1) ^ (-α))) = (c * Λ) * (((i : ℕ) : ℝ) + 1) ^ (-α) by ring]
  have hs : (B:ℝ) * m = ∑ i : Fin N, (c * Λ) * (((i : ℕ) : ℝ) + 1) ^ (-α) /
      (1 + (c * Λ) * (((i : ℕ) : ℝ) + 1) ^ (-α)) := by
    rw [← hS]
    exact Finset.sum_congr rfl (fun i _ => hterm i)
  have hs1 : (B:ℝ) * m ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left h1 hBr.le
    rwa [mul_one_div_cancel hBr.ne'] at h
  have hsN : (B:ℝ) * m ≤ (N:ℝ) / 2 := by
    have h := mul_le_mul_of_nonneg_left h2 hBr.le
    have e : (B:ℝ) * (gammaOf N B / 2) = (N:ℝ) / 2 := by
      unfold gammaOf; field_simp
    linarith
  have hy : 0 < c * Λ := mul_pos hc hΛpos
  obtain ⟨hcore1, hcore2⟩ := pl_vii_core hα1 hN hy hs1 hsN hs
  refine ⟨?_, hcore2⟩
  calc 1 / (∑' n : ℕ, ((n : ℝ) + 1) ^ (-α)) * ((B : ℝ) * m)
      ≤ 1 / (∑' n : ℕ, ((n : ℝ) + 1) ^ (-α)) * ((∑' n : ℕ, ((n : ℝ) + 1) ^ (-α)) * (c * Λ)) :=
        mul_le_mul_of_nonneg_left hcore1 (div_pos one_pos hTpos).le
    _ = c * Λ := by rw [← mul_assoc, one_div_mul_cancel hTpos.ne', one_mul]

/-! ## Elasticity (`lem:app-pl-elasticity`) -/

private lemma el_g_ge {u t : ℝ} (ht : 0 < t) (hu : 0 < u) (h1 : u ≤ t) (h2 : 1 ≤ u * t) :
    t / (1 + t) ^ 2 ≤ u / (1 + u) ^ 2 := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]

private lemma el_antitone {α A : ℝ} (hα : 0 < α) (hA : 0 < A) {i j : ℕ} (hij : i ≤ j) :
    A / ((j:ℝ)+1) ^ α ≤ A / ((i:ℝ)+1) ^ α := by
  have hij' : (i:ℝ) ≤ j := by exact_mod_cast hij
  apply div_le_div_of_nonneg_left hA.le (by positivity)
  exact Real.rpow_le_rpow (by positivity) (by linarith) hα.le

private lemma el_exists_K {α A : ℝ} (hα : 0 < α) (hA : 0 < A) (N : ℕ) :
    ∃ K : ℕ, K ≤ N ∧ (∀ i, i < K → 1 < A / ((i:ℝ)+1) ^ α) ∧
      (∀ i, K ≤ i → i < N → A / ((i:ℝ)+1) ^ α ≤ 1) := by
  classical
  have hex : ∃ k : ℕ, N ≤ k ∨ A / ((k:ℝ)+1) ^ α ≤ 1 := ⟨N, Or.inl le_rfl⟩
  refine ⟨Nat.find hex, Nat.find_min' hex (Or.inl le_rfl), fun i hi => ?_, fun i hKi hiN => ?_⟩
  · have := Nat.find_min hex hi
    simp only [not_or, not_le] at this
    exact this.2
  · rcases Nat.find_spec hex with h | h
    · omega
    · exact (el_antitone hα hA hKi).trans h

private lemma el_x_le {u : ℝ} (hu : 0 < u) (h : u ≤ 1) : u / (1 + u) ≤ 2 * (u / (1 + u) ^ 2) := by
  rw [← sub_nonneg]
  have : 2 * (u / (1 + u) ^ 2) - u / (1 + u) = u * (1 - u) / (1 + u) ^ 2 := by
    field_simp; ring
  rw [this]
  exact div_nonneg (mul_nonneg hu.le (by linarith)) (by positivity)

private lemma el_y_le {u : ℝ} (hu : 0 < u) (h : 1 ≤ u) : 1 / (1 + u) ≤ 2 * (u / (1 + u) ^ 2) := by
  rw [← sub_nonneg]
  have : 2 * (u / (1 + u) ^ 2) - 1 / (1 + u) = (u - 1) / (1 + u) ^ 2 := by
    field_simp; ring
  rw [this]
  exact div_nonneg (by linarith) (by positivity)

private lemma el_key {α A : ℝ} (hα : 0 < α) (hA : 0 < A) (N : ℕ) (hN : 0 < N) (u : ℕ → ℝ)
    (hu : ∀ i, u i = A / ((i:ℝ)+1) ^ α) :
    ((2:ℝ) ^ α / (1 + (2:ℝ) ^ α) ^ 2) *
        ((∑ i ∈ Finset.range N, u i / (1 + u i)) *
          ((N:ℝ) - ∑ i ∈ Finset.range N, u i / (1 + u i))) ≤
      (2 * ((2:ℝ) ^ α / (1 + (2:ℝ) ^ α) ^ 2) + 2) * N *
        ∑ i ∈ Finset.range N, u i / (1 + u i) ^ 2 := by
  obtain ⟨K, hKN, hK1, hK2⟩ := el_exists_K hα hA N
  simp only [← hu] at hK1 hK2
  set t : ℝ := (2:ℝ) ^ α with htdef
  have ht1 : 1 ≤ t := Real.one_le_rpow (by norm_num) hα.le
  have ht0 : 0 < t := by linarith
  set δ : ℝ := t / (1 + t) ^ 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hup : ∀ i, 0 < u i := fun i => by rw [hu]; positivity
  set S : ℝ := ∑ i ∈ Finset.range N, u i / (1 + u i) with hSdef
  set F : ℝ := ∑ i ∈ Finset.range N, u i / (1 + u i) ^ 2 with hFdef
  set T : ℝ := ∑ i ∈ Finset.range N, 1 / (1 + u i) with hTdef
  have hST : S + T = N := by
    rw [hSdef, hTdef, ← Finset.sum_add_distrib]
    have : ∀ i ∈ Finset.range N, u i / (1 + u i) + 1 / (1 + u i) = 1 := by
      intro i _
      have := (hup i)
      field_simp
      ring
    rw [Finset.sum_congr rfl this]; simp
  have hf0 : ∀ i, 0 ≤ u i / (1 + u i) ^ 2 := fun i => by have := hup i; positivity
  have hx0 : ∀ i, 0 ≤ u i / (1 + u i) := fun i => by have := hup i; positivity
  have hy0 : ∀ i, 0 ≤ 1 / (1 + u i) := fun i => by have := hup i; positivity
  have hx1 : ∀ i, u i / (1 + u i) ≤ 1 := fun i => by
    have := hup i
    rw [div_le_one (by linarith)]; linarith
  have hy1 : ∀ i, 1 / (1 + u i) ≤ 1 := fun i => by
    have := hup i
    rw [div_le_one (by linarith)]; linarith
  have hsub : ∀ a b : ℕ, a ≤ b → b ≤ N → Finset.Ico a b ⊆ Finset.range N := by
    intro a b _ hb i hi
    exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_Ico.1 hi).2 hb)
  have hsubK : Finset.range K ⊆ Finset.range N := Finset.range_subset_range.2 hKN
  have hFsplit := Finset.sum_range_add_sum_Ico (fun i => u i / (1 + u i) ^ 2) hKN
  have hSsplit := Finset.sum_range_add_sum_Ico (fun i => u i / (1 + u i)) hKN
  have hTsplit := Finset.sum_range_add_sum_Ico (fun i => 1 / (1 + u i)) hKN
  have hF1 : 0 ≤ ∑ i ∈ Finset.range K, u i / (1 + u i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => hf0 i)
  have hF2 : 0 ≤ ∑ i ∈ Finset.Ico K N, u i / (1 + u i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => hf0 i)
  have hS : S ≤ 2 * F + K := by
    have h1 : ∑ i ∈ Finset.range K, u i / (1 + u i) ≤ K := by
      calc _ ≤ ∑ i ∈ Finset.range K, (1:ℝ) := Finset.sum_le_sum (fun i _ => hx1 i)
        _ = K := by simp
    have h2 : ∑ i ∈ Finset.Ico K N, u i / (1 + u i) ≤
        2 * ∑ i ∈ Finset.Ico K N, u i / (1 + u i) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.1 hi
      exact el_x_le (hup i) (hK2 i hi1 hi2)
    linarith
  have hT : T ≤ 2 * F + ((N:ℝ) - K) := by
    have h1 : ∑ i ∈ Finset.range K, 1 / (1 + u i) ≤
        2 * ∑ i ∈ Finset.range K, u i / (1 + u i) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.1 hi
      exact el_y_le (hup i) (hK1 i hi').le
    have h2 : ∑ i ∈ Finset.Ico K N, 1 / (1 + u i) ≤ (N:ℝ) - K := by
      calc _ ≤ ∑ i ∈ Finset.Ico K N, (1:ℝ) := Finset.sum_le_sum (fun i _ => hy1 i)
        _ = (N:ℝ) - K := by simp [Nat.cast_sub hKN]
    linarith
  have hwin : ∀ I : Finset ℕ, I ⊆ Finset.range N → (∀ i ∈ I, u i ≤ t ∧ 1 ≤ u i * t) →
      (I.card : ℝ) * δ ≤ F := by
    intro I hI hcond
    calc (I.card : ℝ) * δ = ∑ i ∈ I, δ := by simp
      _ ≤ ∑ i ∈ I, u i / (1 + u i) ^ 2 :=
          Finset.sum_le_sum (fun i hi => el_g_ge ht0 (hup i) (hcond i hi).1 (hcond i hi).2)
      _ ≤ F := Finset.sum_le_sum_of_subset_of_nonneg hI (fun i _ _ => hf0 i)
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => hx0 i)
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun i _ => hy0 i)
  have hF0 : 0 ≤ F := Finset.sum_nonneg (fun i _ => hf0 i)
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hTS : (N:ℝ) - S = T := by linarith
  rw [hTS]
  by_cases hcase : 2 * K ≤ N
  · -- window below the crossing
    have hKlt : K < N := by omega
    have hAK : A ≤ ((K:ℝ)+1) ^ α := by
      have := hK2 K le_rfl hKlt
      rw [hu, div_le_one (by positivity)] at this
      exact this
    have hI : (Finset.Ico (K/2) K).card * δ ≤ F := by
      apply hwin
      · exact (hsub _ _ (Nat.div_le_self _ _) hKN)
      · intro i hi
        obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.1 hi
        have h2i : (K:ℝ) ≤ 2 * (i:ℝ) + 1 := by
          have : K ≤ 2 * i + 1 := by omega
          exact_mod_cast this
        have hp : 0 < ((i:ℝ)+1) ^ α := by positivity
        have hgt : 1 < u i := hK1 i hi2
        have hle : u i ≤ t := by
          rw [hu, div_le_iff₀ hp]
          calc A ≤ ((K:ℝ)+1) ^ α := hAK
            _ ≤ (2 * ((i:ℝ)+1)) ^ α :=
                Real.rpow_le_rpow (by positivity) (by linarith) hα.le
            _ = t * ((i:ℝ)+1) ^ α := by rw [Real.mul_rpow (by norm_num) (by positivity)]
        exact ⟨hle, by nlinarith⟩
    have hcard : (K:ℝ) / 2 ≤ ((Finset.Ico (K/2) K).card : ℝ) := by
      rw [Nat.card_Ico]
      have h1 : ((K / 2 : ℕ) : ℝ) ≤ (K:ℝ) / 2 := Nat.cast_div_le
      have h2 : K / 2 ≤ K := Nat.div_le_self _ _
      rw [Nat.cast_sub h2]; linarith
    have hKδ : (K:ℝ) * δ ≤ 2 * F := by nlinarith
    have hSN : S ≤ 2 * F + K := hS
    have hTN : T ≤ N := by linarith
    calc δ * (S * T) ≤ δ * (S * N) := by
          apply mul_le_mul_of_nonneg_left _ hδ.le
          exact mul_le_mul_of_nonneg_left hTN hS0
      _ ≤ δ * ((2 * F + K) * N) := by
          apply mul_le_mul_of_nonneg_left _ hδ.le
          exact mul_le_mul_of_nonneg_right hSN hNpos.le
      _ ≤ (2 * δ + 2) * N * F := by nlinarith [mul_nonneg hNpos.le hF0, mul_nonneg hNpos.le hδ.le]
  · -- window above the crossing
    have hlt : N < 2 * K := by omega
    have hK0 : 0 < K := by omega
    have hAK : ((K:ℝ)) ^ α < A := by
      have h := hK1 (K - 1) (by omega)
      rw [hu, lt_div_iff₀ (by positivity)] at h
      have e : (((K - 1 : ℕ) : ℝ) + 1) = K := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [e] at h; linarith
    have hI : (Finset.Ico K N).card * δ ≤ F := by
      apply hwin
      · exact (hsub _ _ hKN le_rfl)
      · intro i hi
        obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.1 hi
        have hp : 0 < ((i:ℝ)+1) ^ α := by positivity
        have hle : u i ≤ t := (hK2 i hi1 hi2).trans ht1
        have hi3 : (i:ℝ) + 1 ≤ 2 * K := by
          have : i + 1 ≤ 2 * K := by omega
          exact_mod_cast this
        have hp2 : ((i:ℝ)+1) ^ α ≤ t * (K:ℝ) ^ α := by
          calc ((i:ℝ)+1) ^ α ≤ (2 * (K:ℝ)) ^ α :=
                Real.rpow_le_rpow (by positivity) hi3 hα.le
            _ = t * (K:ℝ) ^ α := by
                rw [Real.mul_rpow (by norm_num) (by positivity)]
        refine ⟨hle, ?_⟩
        rw [hu, div_mul_eq_mul_div, le_div_iff₀ hp, one_mul]
        have hKp : 0 < (K:ℝ) ^ α := by have : (0:ℝ) < K := by exact_mod_cast hK0
                                       positivity
        calc ((i:ℝ)+1) ^ α ≤ t * (K:ℝ) ^ α := hp2
          _ ≤ A * t := by nlinarith
    have hcard : ((Finset.Ico K N).card : ℝ) = (N:ℝ) - K := by
      rw [Nat.card_Ico, Nat.cast_sub hKN]
    rw [hcard] at hI
    have hSN : S ≤ N := by linarith
    have hNS : (N:ℝ) - K ≤ F / δ := by rw [le_div_iff₀ hδ]; exact hI
    calc δ * (S * T) ≤ δ * (N * T) := by
          apply mul_le_mul_of_nonneg_left _ hδ.le
          exact mul_le_mul_of_nonneg_right hSN hT0
      _ ≤ δ * (N * (2 * F + ((N:ℝ) - K))) := by
          apply mul_le_mul_of_nonneg_left _ hδ.le
          exact mul_le_mul_of_nonneg_left hT hNpos.le
      _ ≤ (2 * δ + 2) * N * F := by nlinarith [mul_nonneg hNpos.le hF0, mul_nonneg hNpos.le hδ.le]

private lemma el_term_hasDeriv {μ x : ℝ} (hμ : 0 < μ) (hx : 0 < x) :
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

private lemma el_partMN_hasDeriv {N B : ℕ} (μ : Fin N → ℝ) (hpos : ∀ i, 0 < μ i) {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt (partMN B μ) ((B:ℝ)⁻¹ * ∑ i, μ i / (1 + x * μ i) ^ 2) x := by
  unfold partMN
  exact HasDerivAt.const_mul _ (HasDerivAt.fun_sum (u := Finset.univ)
    (A := fun i Λ => Λ * μ i / (1 + Λ * μ i)) (A' := fun i => μ i / (1 + x * μ i) ^ 2)
    (fun i _ => el_term_hasDeriv (hpos i) hx))

private noncomputable def elCa (α : ℝ) : ℝ :=
  ((2:ℝ) ^ α / (1 + (2:ℝ) ^ α) ^ 2) / (2 * ((2:ℝ) ^ α / (1 + (2:ℝ) ^ α) ^ 2) + 2)

private lemma elCa_pos {α : ℝ} : 0 < elCa α := by
  unfold elCa; positivity

private lemma el_i_bounds {α : ℝ} (hα : 0 < α) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) {Λ : ℝ} (hΛ : 0 < Λ) :
    elCa α * partMN B (plSpec α c N) Λ * (1 - partMN B (plSpec α c N) Λ / gammaOf N B) ≤
        Λ * deriv (partMN B (plSpec α c N)) Λ ∧
      Λ * deriv (partMN B (plSpec α c N)) Λ ≤ partMN B (plSpec α c N) Λ := by
  have hpos : ∀ i : Fin N, 0 < plSpec α c N i := fun i => by
    unfold plSpec; positivity
  set u : ℕ → ℝ := fun i => Λ * c / ((i:ℝ)+1) ^ α with hudef
  have hA : 0 < Λ * c := mul_pos hΛ hc
  have hup : ∀ i, 0 < u i := fun i => by simp only [hudef]; positivity
  have hue : ∀ i : Fin N, Λ * plSpec α c N i = u ((i:ℕ)) := by
    intro i
    simp only [hudef, plSpec, Real.rpow_neg (by positivity : (0:ℝ) ≤ ((i:ℕ):ℝ)+1)]
    field_simp
  have hm : partMN B (plSpec α c N) Λ =
      (B:ℝ)⁻¹ * ∑ i ∈ Finset.range N, u i / (1 + u i) := by
    unfold partMN
    congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun i => u i / (1 + u i)) N]
    exact Finset.sum_congr rfl (fun i _ => by rw [hue i])
  have hd : Λ * deriv (partMN B (plSpec α c N)) Λ =
      (B:ℝ)⁻¹ * ∑ i ∈ Finset.range N, u i / (1 + u i) ^ 2 := by
    rw [(el_partMN_hasDeriv (plSpec α c N) hpos hΛ).deriv, mul_left_comm, Finset.mul_sum]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun i => u i / (1 + u i) ^ 2) N]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hue i]
    have := hpos i
    field_simp
  rw [hm, hd]
  set S := ∑ i ∈ Finset.range N, u i / (1 + u i) with hS
  set F := ∑ i ∈ Finset.range N, u i / (1 + u i) ^ 2 with hF
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  refine ⟨?_, ?_⟩
  · have key := el_key hα hA N hN u (fun i => rfl)
    rw [← hS, ← hF] at key
    set δ : ℝ := (2:ℝ) ^ α / (1 + (2:ℝ) ^ α) ^ 2 with hδ
    have hδ0 : 0 < δ := by positivity
    have hk : elCa α * (S * ((N:ℝ) - S)) ≤ N * F := by
      unfold elCa
      rw [← hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [key]
    have hγ : gammaOf N B = (N:ℝ) / B := rfl
    have e : elCa α * ((B:ℝ)⁻¹ * S) * (1 - (B:ℝ)⁻¹ * S / gammaOf N B) =
        (B:ℝ)⁻¹ * (elCa α * (S * ((N:ℝ) - S)) / N) := by
      rw [hγ]; field_simp
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_iff₀ hNr]; linarith
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro i _
    have := hup i
    apply div_le_div_of_nonneg_left this.le (by positivity)
    nlinarith

private lemma el_lam_bounds {α : ℝ} (hα : 0 < α) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    1 / m ≤ deriv (partLam B (plSpec α c N)) m / partLam B (plSpec α c N) m ∧
      deriv (partLam B (plSpec α c N)) m / partLam B (plSpec α c N) m ≤
        (1 / elCa α) * (1 / m + 1 / (gammaOf N B - m)) := by
  have hpos : ∀ i : Fin N, 0 < plSpec α c N i := fun i => by
    unfold plSpec; positivity
  obtain ⟨⟨hmaps, hinj, hsurj⟩, ⟨hlmaps, _, _⟩, _, hcd⟩ :=
    def_app_pl_participation_bij (plSpec α c N) hB hN hpos
  have hspec : ∀ y ∈ Ioo 0 (gammaOf N B), partMN B (plSpec α c N) (partLam B (plSpec α c N) y) = y := by
    intro y hy
    obtain ⟨x, hx, hxe⟩ := hsurj hy
    exact Function.invFunOn_eq (f := partMN B (plSpec α c N)) (s := Ioi 0) ⟨x, hx, hxe⟩
  set Λ := partLam B (plSpec α c N) m with hΛdef
  have hΛ : 0 < Λ := hlmaps hm
  have hnhds : Ioo 0 (gammaOf N B) ∈ 𝓝 m := Ioo_mem_nhds hm.1 hm.2
  have hdiff : DifferentiableAt ℝ (partLam B (plSpec α c N)) m :=
    ((hcd.contDiffAt hnhds).differentiableAt (by simp))
  have hcomp := (el_partMN_hasDeriv (B := B) (plSpec α c N) hpos (hΛ)).comp m hdiff.hasDerivAt
  have hid : HasDerivAt (partMN B (plSpec α c N) ∘ partLam B (plSpec α c N)) 1 m := by
    have h1 : HasDerivAt (fun y : ℝ => y) 1 m := hasDerivAt_id m
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hnhds] with y hy using hspec y hy
  have huniq := hcomp.unique hid
  rw [← (el_partMN_hasDeriv (B := B) (plSpec α c N) hpos hΛ).deriv] at huniq
  obtain ⟨hlo, hhi⟩ := el_i_bounds hα hN hB hc hΛ
  have hmeq : partMN B (plSpec α c N) Λ = m := hspec m hm
  rw [hmeq] at hlo hhi
  set D := deriv (partMN B (plSpec α c N)) Λ with hD
  set L := deriv (partLam B (plSpec α c N)) m with hL
  have hγm : 0 < gammaOf N B - m := by linarith [hm.2]
  have hm0 : 0 < m := hm.1
  have hγ0 : 0 < gammaOf N B := by linarith [hm.2]
  have hca := elCa_pos (α := α)
  have hP : 0 < elCa α * m * (1 - m / gammaOf N B) := by
    have : 0 < 1 - m / gammaOf N B := by
      rw [sub_pos, div_lt_one hγ0]; exact hm.2
    positivity
  have hPpos : 0 < Λ * D := lt_of_lt_of_le hP hlo
  have hLD : L / Λ = 1 / (Λ * D) := by
    have : L = 1 / D := by
      have hD0 : D ≠ 0 := by
        intro h; rw [h] at hPpos; simp at hPpos
      field_simp; linarith [huniq]
    rw [this]; field_simp
  rw [hLD]
  refine ⟨?_, ?_⟩
  · rw [div_le_div_iff₀ hm0 hPpos]; linarith
  · have e : (1 / elCa α) * (1 / m + 1 / (gammaOf N B - m)) =
        1 / (elCa α * m * (1 - m / gammaOf N B)) := by
      field_simp
      ring
    rw [e]
    exact one_div_le_one_div_of_le hP hlo


/-- `lem:app-pl-elasticity` (snapshot `cr-2026-10-23`), the two displays; one constant `c_α` for both, independent of `N, B, c_N, Λ`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Elasticity]\label{lem:app-pl-elasticity}
There is $c_\alpha>0$, independent of $N$, $B$, $c_N$ and $\Lambda$, such that
\[
c_\alpha\,m_N(\Lambda)\Big(1-\frac{m_N(\Lambda)}{\gamma}\Big)\le\Lambda m_N'(\Lambda)\le m_N(\Lambda),\qquad
\frac1m\le\frac{\Lambda_N'(m)}{\Lambda_N(m)}\le\frac1{c_\alpha}\Big(\frac1m+\frac1{\gamma-m}\Big).
\]
Consequently $\vartheta_N(m)\le C\big(1+m^{-1}+(\gamma-m)^{-1}\big)$, and $E(m)\vartheta_N(m)\ge1$.
\end{lemma}
-/
theorem lem_app_pl_elasticity_i {α : ℝ} (hα : 0 < α) :
    ∃ cα : ℝ, 0 < cα ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c →
      (∀ Λ : ℝ, 0 < Λ →
        cα * partMN B (plSpec α c N) Λ * (1 - partMN B (plSpec α c N) Λ / gammaOf N B) ≤
            Λ * deriv (partMN B (plSpec α c N)) Λ ∧
          Λ * deriv (partMN B (plSpec α c N)) Λ ≤ partMN B (plSpec α c N) Λ) ∧
      (∀ m : ℝ, m ∈ Ioo 0 (gammaOf N B) →
        1 / m ≤ deriv (partLam B (plSpec α c N)) m / partLam B (plSpec α c N) m ∧
          deriv (partLam B (plSpec α c N)) m / partLam B (plSpec α c N) m ≤
            (1 / cα) * (1 / m + 1 / (gammaOf N B - m))) := by
  refine ⟨elCa α, elCa_pos, fun N B c hN hB hc => ⟨fun Λ hΛ => el_i_bounds hα hN hB hc hΛ, ?_⟩⟩
  intro m hm
  exact el_lam_bounds hα hN hB hc hm

/-- `lem:app-pl-elasticity` (snapshot `cr-2026-10-23`), the consequences: `ϑ_N(m) ≤ C(1+m^{-1}+(γ-m)^{-1})` and `E(m) ϑ_N(m) ≥ 1`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Elasticity]\label{lem:app-pl-elasticity}
There is $c_\alpha>0$, independent of $N$, $B$, $c_N$ and $\Lambda$, such that
\[
c_\alpha\,m_N(\Lambda)\Big(1-\frac{m_N(\Lambda)}{\gamma}\Big)\le\Lambda m_N'(\Lambda)\le m_N(\Lambda),\qquad
\frac1m\le\frac{\Lambda_N'(m)}{\Lambda_N(m)}\le\frac1{c_\alpha}\Big(\frac1m+\frac1{\gamma-m}\Big).
\]
Consequently $\vartheta_N(m)\le C\big(1+m^{-1}+(\gamma-m)^{-1}\big)$, and $E(m)\vartheta_N(m)\ge1$.
\end{lemma}
-/
theorem lem_app_pl_elasticity_ii {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C : ℝ, ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c →
      ∀ m : ℝ, m ∈ Ioo 0 (gammaOf N B) →
        thetaN β B (plSpec α c N) m ≤ C * (1 + 1 / m + 1 / (gammaOf N B - m)) ∧
          1 ≤ Efun β m * thetaN β B (plSpec α c N) m := by
  obtain ⟨cE, CE, hcE, -, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  have hca := elCa_pos (α := α)
  refine ⟨1 / cE + 1 / elCa α + 1, fun N B c hN hB hc m hm => ?_⟩
  obtain ⟨hl, hu⟩ := el_lam_bounds hα hN hB hc hm
  have hm0 : 0 < m := hm.1
  have hγm : 0 < gammaOf N B - m := by linarith [hm.2]
  obtain ⟨hE1, -⟩ := hE m hm0
  have hmin : 0 < min m 1 := lt_min hm0 one_pos
  have hEpos : 0 < Efun β m := lt_of_lt_of_le (mul_pos hcE hmin) hE1
  unfold thetaN
  set L := deriv (partLam B (plSpec α c N)) m / partLam B (plSpec α c N) m with hLdef
  refine ⟨?_, ?_⟩
  · have h1 : 1 / Efun β m ≤ (1 / cE) * (1 + 1 / m) := by
      rw [div_le_iff₀ hEpos]
      have hmin' : cE * min m 1 ≤ Efun β m := hE1
      have : 1 ≤ (1 / cE) * (1 + 1 / m) * (cE * min m 1) := by
        have e : (1 / cE) * (1 + 1 / m) * (cE * min m 1) = (1 + 1 / m) * min m 1 := by
          field_simp
        rw [e]
        rcases le_total m 1 with h | h
        · rw [min_eq_left h]; field_simp; linarith
        · rw [min_eq_right h]; have : 0 < 1 / m := by positivity
          linarith
      calc (1:ℝ) ≤ (1 / cE) * (1 + 1 / m) * (cE * min m 1) := this
        _ ≤ (1 / cE) * (1 + 1 / m) * Efun β m :=
            mul_le_mul_of_nonneg_left hmin' (by positivity)
    have hi : 0 < 1 / m := by positivity
    have hj : 0 < 1 / (gammaOf N B - m) := by positivity
    have h2 : L ≤ (1 / elCa α) * (1 / m + 1 / (gammaOf N B - m)) := hu
    have hk : 0 ≤ 1 / cE := by positivity
    have hk2 : 0 ≤ 1 / elCa α := by positivity
    nlinarith [mul_nonneg hk hi.le, mul_nonneg hk2 hi.le, mul_nonneg hk2 hj.le, mul_nonneg hk hj.le]
  · have hj : 0 < 1 / (gammaOf N B - m) := by positivity
    have : 1 / Efun β m ≤ 1 / Efun β m + L + 1 / (gammaOf N B - m) - 1 / m := by linarith
    calc (1:ℝ) = Efun β m * (1 / Efun β m) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left this hEpos.le

/-! ## The bulk display of the drift in participation coordinates (`eqn:app-pl-Bi-bulk`) -/

/-- `eqn:app-pl-Bi-bulk` (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-Bi-bulk}
\mathcal B_i(\gamma p)=a_N\sqrt{\frac{1-p}{p\,V_N(p)}}\;\frac{V_N(p)}{V_N(p)+x^\alpha}.
\end{equation}
-/
theorem eqn_app_pl_Bi_bulk {α : ℝ} (hα : 0 < α) {N B : ℕ} (c : ℝ) (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    partBfun B (plSpec α c N) i (gammaOf N B * p) =
      aN α c N * Real.sqrt ((1 - p) / (p * finV α N p)) *
        (finV α N p / (finV α N p + ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α)) := by
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hBr : (0:ℝ) < (B:ℝ) := by exact_mod_cast hB
  have hγ : 0 < gammaOf N B := by unfold gammaOf; exact div_pos hNr hBr
  have hγp : 0 < gammaOf N B * p := mul_pos hγ hp0
  have hmI : gammaOf N B * p ∈ Ioo 0 (gammaOf N B) := ⟨hγp, by nlinarith⟩
  have hpos : ∀ j, 0 < plSpec α c N j := fun j => by
    unfold plSpec
    exact mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)
  have hLpos : 0 < partLam B (plSpec α c N) (gammaOf N B * p) :=
    (def_app_pl_participation_bij (plSpec α c N) hB hN hpos).2.1.mapsTo hmI
  have hLV := eqn_app_pl_Lambda_V (N := N) (B := B) α c hN hB hc hmI
  rw [mul_div_cancel_left₀ p hγ.ne'] at hLV
  have hNα : 0 < (N:ℝ) ^ α := Real.rpow_pos_of_pos hNr α
  have hVpos : 0 < finV α N p := by
    have h1 : 0 < (N:ℝ) ^ α / c * finV α N p := hLV ▸ hLpos
    exact pos_of_mul_pos_right h1 (div_pos hNα hc).le
  set V := finV α N p with hVdef
  unfold partBfun partF
  rw [hLV]
  have hA : (gammaOf N B - gammaOf N B * p) / (gammaOf N B * p * ((N:ℝ) ^ α / c * V))
      = c * (N:ℝ) ^ (-α) * ((1 - p) / (p * V)) := by
    rw [Real.rpow_neg hNr.le]
    unfold gammaOf
    have := hNr.ne'
    field_simp
  have hsN : Real.sqrt ((N:ℝ) ^ (-α)) = (N:ℝ) ^ (-α / 2) := by
    rw [show (N:ℝ) ^ (-α) = ((N:ℝ) ^ (-α / 2)) ^ 2 by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
      congr 1
      push_cast
      ring]
    exact Real.sqrt_sq (Real.rpow_nonneg hNr.le _)
  have hsq : Real.sqrt (c * (N:ℝ) ^ (-α) * ((1 - p) / (p * V)))
      = aN α c N * Real.sqrt ((1 - p) / (p * V)) := by
    rw [Real.sqrt_mul (mul_nonneg hc.le (Real.rpow_nonneg hNr.le _)),
      Real.sqrt_mul hc.le, hsN]
    unfold aN
    ring
  have hf : (N:ℝ) ^ α / c * V * plSpec α c N i / (1 + (N:ℝ) ^ α / c * V * plSpec α c N i)
      = V / (V + ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α) := by
    have ht : (0:ℝ) < ((i : ℕ) : ℝ) + 1 := by positivity
    have htα : 0 < (((i : ℕ) : ℝ) + 1) ^ α := Real.rpow_pos_of_pos ht α
    unfold plSpec
    rw [Real.div_rpow ht.le hNr.le, Real.rpow_neg ht.le]
    have := hNr.ne'
    have := hc.ne'
    have := hVpos.ne'
    have := htα.ne'
    have := hNα.ne'
    field_simp
    ring
  rw [hA, hsq, hf]

/-! ## Reference scales (`prop:app-pl-scales`) -/

/-- The reference scale `κ = Λ_N(1)` (`prop:app-pl-scales`, `section.tex` l.987–992:
the unique solution of `∑_i κμ_i/(1+κμ_i) = B`). -/
noncomputable def kappaOf (α c : ℝ) (N B : ℕ) : ℝ := partLam B (plSpec α c N) 1

/-- `i_# = (c_N κ)^{1/α}` (`prop:app-pl-scales`, `section.tex` l.987–992). -/
noncomputable def iSharp (α c : ℝ) (N B : ℕ) : ℝ := (c * kappaOf α c N B) ^ (1 / α)

/-- `eqn:app-pl-icd` (snapshot `cr-2026-10-23`); defines `d` (α ≤ 1; `if α < 1` splits the two cases). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-icd}
\begin{gathered}
d\defeq\frac{c_0}{\sqrt{1-\alpha}},\quad i_{\mathrm c,\mathfrak d}\defeq\Big[\frac{BN^{\alpha-1}}{\sw2d^2\log^2\gamma}\Big]^{1/\alpha},\quad
a_{\mathfrak d}\defeq d\,a_N\log\gamma\quad(\alpha<1);\\
d\defeq\frac23c_0,\quad i_{\mathrm c,\mathfrak d}\defeq\frac{B}{\sw2d^2\log^3\gamma},\quad
a_{\mathfrak d}\defeq d\,a_N(\log\gamma)^{3/2}\quad(\alpha=1).
\end{gathered}
\end{equation}
-/
noncomputable def icdD (α : ℝ) : ℝ := if α < 1 then c0 / Real.sqrt (1 - α) else 2 / 3 * c0

/-- `eqn:app-pl-icd` (snapshot `cr-2026-10-23`); defines `i_{c,𝔡}` (α ≤ 1; `if α < 1` splits the two cases). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-icd}
\begin{gathered}
d\defeq\frac{c_0}{\sqrt{1-\alpha}},\quad i_{\mathrm c,\mathfrak d}\defeq\Big[\frac{BN^{\alpha-1}}{\sw2d^2\log^2\gamma}\Big]^{1/\alpha},\quad
a_{\mathfrak d}\defeq d\,a_N\log\gamma\quad(\alpha<1);\\
d\defeq\frac23c_0,\quad i_{\mathrm c,\mathfrak d}\defeq\frac{B}{\sw2d^2\log^3\gamma},\quad
a_{\mathfrak d}\defeq d\,a_N(\log\gamma)^{3/2}\quad(\alpha=1).
\end{gathered}
\end{equation}
-/
noncomputable def icdIdx (β α : ℝ) (N B : ℕ) : ℝ :=
  if α < 1 then
    ((B : ℝ) * (N : ℝ) ^ (α - 1) / (sPow β 2 * icdD α ^ 2 * Real.log (gammaOf N B) ^ 2)) ^
      (1 / α)
  else (B : ℝ) / (sPow β 2 * icdD α ^ 2 * Real.log (gammaOf N B) ^ 3)

/-- `eqn:app-pl-icd` (snapshot `cr-2026-10-23`); defines `a_𝔡` (α ≤ 1; `if α < 1` splits the two cases). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-icd}
\begin{gathered}
d\defeq\frac{c_0}{\sqrt{1-\alpha}},\quad i_{\mathrm c,\mathfrak d}\defeq\Big[\frac{BN^{\alpha-1}}{\sw2d^2\log^2\gamma}\Big]^{1/\alpha},\quad
a_{\mathfrak d}\defeq d\,a_N\log\gamma\quad(\alpha<1);\\
d\defeq\frac23c_0,\quad i_{\mathrm c,\mathfrak d}\defeq\frac{B}{\sw2d^2\log^3\gamma},\quad
a_{\mathfrak d}\defeq d\,a_N(\log\gamma)^{3/2}\quad(\alpha=1).
\end{gathered}
\end{equation}
-/
noncomputable def icdA (α c : ℝ) (N B : ℕ) : ℝ :=
  if α < 1 then icdD α * aN α c N * Real.log (gammaOf N B)
  else icdD α * aN α c N * Real.log (gammaOf N B) ^ ((3 : ℝ) / 2)

/-- `eqn:app-pl-icv` (snapshot `cr-2026-10-23`); defines `i_{c,𝔳} = c_0^{2/α} i_{c,𝔡}` (the first form of the display). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-icv}
i_{\mathrm c,\mathfrak v}\defeq c_0^{2/\alpha}\,i_{\mathrm c,\mathfrak d}=\begin{cases}N\big[(1-\alpha)/(\sw2\gamma\log^2\gamma)\big]^{1/\alpha},&\alpha<1,\\ 9B/(4\sw2\log^3\gamma),&\alpha=1.\end{cases}
\end{equation}
-/
noncomputable def icvIdx (β α : ℝ) (N B : ℕ) : ℝ := c0 ^ (2 / α) * icdIdx β α N B

/-- Private copy: `0 < ∑ w_j^2` for `0 < β < 1` (for `eqn_app_pl_icv`). -/
private lemma pl_eqn_sPow2_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : 0 < sPow β 2 := by
  unfold sPow
  have hs : Summable (fun j : ℕ => emaW β j ^ 2) := by
    have h := (summable_geometric_of_lt_one (sq_nonneg β)
      (by nlinarith : β ^ 2 < 1)).mul_left ((1 - β) ^ 2)
    refine h.congr (fun j => ?_)
    unfold emaW
    ring
  have h1 : 0 < 1 - β := by linarith
  refine hs.tsum_pos (fun j => sq_nonneg _) 0 ?_
  unfold emaW
  simp only [pow_zero, mul_one]
  exact pow_pos h1 2

/-- Private copy: `c0 ^ 2 = 2/π` (for `eqn_app_pl_icv`). -/
private lemma pl_eqn_c0_sq : c0 ^ 2 = 2 / Real.pi := by
  unfold c0
  rw [Real.sq_sqrt (show (0:ℝ) ≤ 2 / Real.pi by positivity)]

/-- Private copy: `icdD α ^ 2 = 2/(π(1-α))` for `α < 1` (for `eqn_app_pl_icv`). -/
private lemma pl_eqn_icdD_sq {α : ℝ} (hα1 : α < 1) : icdD α ^ 2 = 2 / (Real.pi * (1 - α)) := by
  unfold icdD
  rw [if_pos hα1, div_pow, Real.sq_sqrt (show (0:ℝ) ≤ 1 - α by linarith), pl_eqn_c0_sq, div_div]

/-- Private copy: `icdD 1 ^ 2 = 8/(9π)` (for `eqn_app_pl_icv`). -/
private lemma pl_eqn_icdD_one_sq : icdD 1 ^ 2 = 8 / (9 * Real.pi) := by
  unfold icdD
  rw [if_neg (lt_irrefl _), mul_pow, pl_eqn_c0_sq]
  ring

/-- `eqn:app-pl-icv` (snapshot `cr-2026-10-23`), the case form of the display. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-icv}
i_{\mathrm c,\mathfrak v}\defeq c_0^{2/\alpha}\,i_{\mathrm c,\mathfrak d}=\begin{cases}N\big[(1-\alpha)/(\sw2\gamma\log^2\gamma)\big]^{1/\alpha},&\alpha<1,\\ 9B/(4\sw2\log^3\gamma),&\alpha=1.\end{cases}
\end{equation}
-/
theorem eqn_app_pl_icv {β α : ℝ} {N B : ℕ} (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 < α)
    (hα1 : α ≤ 1) (hN : 0 < N) (hB : 0 < B) (hγ : 1 < gammaOf N B) :
    icvIdx β α N B =
      if α < 1 then
        (N : ℝ) * ((1 - α) / (sPow β 2 * gammaOf N B * Real.log (gammaOf N B) ^ 2)) ^ (1 / α)
      else 9 * (B : ℝ) / (4 * sPow β 2 * Real.log (gammaOf N B) ^ 3) := by
  rcases lt_or_eq_of_le hα1 with h | h
  · have hNp : (0:ℝ) < N := by exact_mod_cast hN
    have hBp : (0:ℝ) < B := by exact_mod_cast hB
    have hS : 0 < sPow β 2 := pl_eqn_sPow2_pos hβ0 hβ1
    have hG : gammaOf N B = (N:ℝ) / B := rfl
    have hc0 : 0 ≤ c0 := by unfold c0; positivity
    have hcα : c0 ^ (2 / α) = (c0 ^ 2) ^ (1 / α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0]
      congr 1
      push_cast
      ring
    have hpow : (N:ℝ) ^ α = (N:ℝ) ^ (α - 1) * N := by
      rw [← Real.rpow_add_one hNp.ne']
      congr 1
      ring
    have hXnn : 0 ≤ (B:ℝ) * (N:ℝ) ^ (α - 1) /
        (sPow β 2 * icdD α ^ 2 * Real.log (gammaOf N B) ^ 2) := by
      apply div_nonneg
      · exact mul_nonneg hBp.le (Real.rpow_nonneg hNp.le _)
      · exact mul_nonneg (mul_nonneg hS.le (sq_nonneg _)) (sq_nonneg _)
    have hYnn : 0 ≤ (1 - α) / (sPow β 2 * gammaOf N B * Real.log (gammaOf N B) ^ 2) := by
      apply div_nonneg (by linarith)
      exact mul_nonneg (mul_nonneg hS.le (by rw [hG]; positivity)) (sq_nonneg _)
    have hR : (N:ℝ) * ((1 - α) / (sPow β 2 * gammaOf N B * Real.log (gammaOf N B) ^ 2)) ^ (1 / α)
        = ((N:ℝ) ^ α * ((1 - α) / (sPow β 2 * gammaOf N B * Real.log (gammaOf N B) ^ 2))) ^
            (1 / α) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hNp.le _) hYnn, one_div,
        Real.rpow_rpow_inv hNp.le hα0.ne']
    have h1α : (1 - α) ≠ 0 := (sub_pos.2 h).ne'
    have hSne := hS.ne'
    have hLne := (Real.log_pos hγ).ne'
    have hNne := hNp.ne'
    have hBne := hBp.ne'
    have hpi := Real.pi_pos.ne'
    unfold icvIdx icdIdx
    simp only [if_pos h]
    rw [hcα, hR, ← Real.mul_rpow (pow_nonneg hc0 2) hXnn]
    congr 1
    rw [pl_eqn_c0_sq, pl_eqn_icdD_sq h, hG, hpow]
    field_simp
  · subst h
    have hS := (pl_eqn_sPow2_pos hβ0 hβ1).ne'
    have hLne := (Real.log_pos hγ).ne'
    have hpi := Real.pi_pos.ne'
    unfold icvIdx icdIdx
    simp only [lt_self_iff_false, if_false, div_one, Real.rpow_two]
    rw [pl_eqn_icdD_one_sq, pl_eqn_c0_sq]
    field_simp
    ring

/-- `prop:app-pl-scales` (snapshot `cr-2026-10-23`), the definition of `κ` for `γ > 1`: existence and uniqueness of the solution. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{proposition}[Reference scales]\label{prop:app-pl-scales}
Assume \cref{assum:app-pl-regime}. For $\gamma>1$ let $\resscale\defeq\Lambda_N(1)$ be the
unique solution of
\[
\sum_{i=1}^N\frac{\resscale\mu_i}{1+\resscale\mu_i}=B,
\]
and put $i_\#\defeq(c_N\resscale)^{1/\alpha}$. Then
\begin{equation}\label{eqn:app-pl-kappa}
\begin{gathered}
c_N\resscale\sim\begin{cases}(1-\alpha)BN^{\alpha-1},&\alpha<1,\\ B/\log\gamma,&\alpha=1,\\ (B/K_\alpha)^\alpha,&\alpha>1,\end{cases}
\\
\frac{i_{\mathrm c,\mathfrak d}}{i_\#}\sim\begin{cases}\big(\pi/(2\sw2\log^2\gamma)\big)^{1/\alpha},&\alpha<1,\\ 9\pi/(8\sw2\log^2\gamma),&\alpha=1,\end{cases}
\qquad
\frac{i_{\mathrm c}}{i_\#}\to1\ \ (\alpha>1),
\end{gathered}
\end{equation}
and $i_{\mathrm c,\mathfrak v}/i_\#\sim(\sw2\log^2\gamma)^{-1/\alpha}$ for $\alpha<1$ and
$\sim9/(4\sw2\log^2\gamma)$ for $\alpha=1$.
\end{proposition}
-/
theorem prop_app_pl_scales_i {α : ℝ} {N B : ℕ} (c : ℝ) (hα : 0 < α) (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (hγ : 1 < gammaOf N B) :
    0 < kappaOf α c N B ∧
      ∑ i : Fin N, kappaOf α c N B * plSpec α c N i /
          (1 + kappaOf α c N B * plSpec α c N i) = (B : ℝ) ∧
      ∀ κ : ℝ, 0 < κ →
        ∑ i : Fin N, κ * plSpec α c N i / (1 + κ * plSpec α c N i) = (B : ℝ) →
          κ = kappaOf α c N B := by
  have hpos : ∀ i : Fin N, 0 < plSpec α c N i := fun i => by
    unfold plSpec
    exact mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)
  obtain ⟨hbij, hinv, _, _⟩ := def_app_pl_participation_bij (plSpec α c N) hB hN hpos
  have hB' : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  have h1mem : (1 : ℝ) ∈ Ioo 0 (gammaOf N B) := ⟨zero_lt_one, hγ⟩
  have hκpos : 0 < kappaOf α c N B := by
    unfold kappaOf
    exact hinv.mapsTo h1mem
  have hκeq : partMN B (plSpec α c N) (kappaOf α c N B) = 1 := by
    obtain ⟨x, hx, hxm⟩ := hbij.surjOn h1mem
    unfold kappaOf partLam
    exact Function.invFunOn_eq ⟨x, hx, hxm⟩
  have hsum : ∀ κ : ℝ, partMN B (plSpec α c N) κ = (B : ℝ)⁻¹ *
      ∑ i : Fin N, κ * plSpec α c N i / (1 + κ * plSpec α c N i) := fun κ => rfl
  refine ⟨hκpos, ?_, ?_⟩
  · have h := hκeq
    rw [hsum] at h
    field_simp at h
    linarith
  · intro κ hκ hS
    have hκm : partMN B (plSpec α c N) κ = 1 := by
      rw [hsum, hS]
      field_simp
    have hκmem : κ ∈ Ioi (0:ℝ) := hκ
    have hkmem : kappaOf α c N B ∈ Ioi (0:ℝ) := hκpos
    exact hbij.injOn hκmem hkmem (hκm.trans hκeq.symm)

/-- Private helper: `1/γ_N → 0` within `(0,∞)` along the regime. -/
private lemma pl_scales_p_tend {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) :
    Tendsto (fun n => 1 / gammaOf (N n) (B n)) atTop (𝓝[>] (0:ℝ)) := by
  have h0 : Tendsto (fun n => 1 / gammaOf (N n) (B n)) atTop (𝓝 0) := by
    have hg : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop := R.hγ
    exact Tendsto.congr (fun n => (one_div _).symm) hg.inv_tendsto_atTop
  refine tendsto_nhdsWithin_iff.2 ⟨h0, Eventually.of_forall (fun n => ?_)⟩
  have hN : (0:ℝ) < (N n : ℝ) := by exact_mod_cast R.hNpos n
  have hB : (0:ℝ) < (B n : ℝ) := by exact_mod_cast R.hBpos n
  unfold gammaOf
  exact one_div_pos.2 (div_pos hN hB)

/-- Private helper: `contV α p > 0` for `0 < p < 1`. -/
private lemma pl_scales_contV_pos {α : ℝ} (hα0 : 0 < α) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < contV α p := by
  obtain ⟨V, hV, hVp⟩ := pl_ii_exists_cont hα0 hp0 hp1
  exact (pl_contV_spec ⟨V, hV, hVp⟩).1

/-- Private helper: `finV α N p > 0` for `0 < p < 1`. -/
private lemma pl_scales_finV_pos {α : ℝ} {N : ℕ} (hα0 : 0 < α) (hN : 0 < N) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) : 0 < finV α N p := by
  obtain ⟨V, hV, hVp⟩ := pl_ii_exists_fin hα0 hN hp0 hp1
  rw [pl_finV_of_eq α hN hV hVp]
  exact hV

/-- Private helper: `finV/contV → 1` along the regime, at the points `p_n = 1/γ_n`. -/
private lemma pl_scales_finV_contV {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) :
    IsEquivalent atTop (fun n => finV α (N n) (1 / gammaOf (N n) (B n)))
      (fun n => contV α (1 / gammaOf (N n) (B n))) := by
  obtain ⟨C, hC⟩ := lem_app_pl_finite_inverse_ii R.hα
  have hp0 : Tendsto (fun n => 1 / gammaOf (N n) (B n)) atTop (𝓝 (0:ℝ)) :=
    (pl_scales_p_tend R).mono_right nhdsWithin_le_nhds
  have hB2 : ∀ᶠ n in atTop, 2 ≤ B n := by
    have := R.hB.eventually_ge_atTop (2:ℝ)
    exact this.mono (fun n hn => by exact_mod_cast hn)
  have hhalf : ∀ᶠ n in atTop, 1 / gammaOf (N n) (B n) < 1 / 2 :=
    hp0.eventually (gt_mem_nhds (by norm_num))
  have hlog : Tendsto (fun n => Real.log (finV α (N n) (1 / gammaOf (N n) (B n)) /
      contV α (1 / gammaOf (N n) (B n)))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := C)).div_atTop R.hB)
    filter_upwards [hB2, hhalf] with n hn2 hnh
    have hpos : 0 < 1 / gammaOf (N n) (B n) := by
      have hN : (0:ℝ) < (N n : ℝ) := by exact_mod_cast R.hNpos n
      have hB : (0:ℝ) < (B n : ℝ) := by exact_mod_cast R.hBpos n
      unfold gammaOf
      exact one_div_pos.2 (div_pos hN hB)
    have key := hC (N n) (B n) 1 (1 / gammaOf (N n) (B n)) (R.hNpos n) hn2 le_rfl le_rfl
      (by linarith)
    rw [Real.norm_eq_abs]
    simpa using key
  have hratio : Tendsto (fun n => finV α (N n) (1 / gammaOf (N n) (B n)) /
      contV α (1 / gammaOf (N n) (B n))) atTop (𝓝 1) := by
    have h := (Real.continuous_exp.tendsto 0).comp hlog
    rw [Real.exp_zero] at h
    refine Tendsto.congr' ?_ h
    filter_upwards [hB2, hhalf] with n hn2 hnh
    have hpos : 0 < 1 / gammaOf (N n) (B n) := by
      have hN : (0:ℝ) < (N n : ℝ) := by exact_mod_cast R.hNpos n
      have hB : (0:ℝ) < (B n : ℝ) := by exact_mod_cast R.hBpos n
      unfold gammaOf
      exact one_div_pos.2 (div_pos hN hB)
    have hf := pl_scales_finV_pos R.hα (R.hNpos n) hpos (by linarith)
    have hc := pl_scales_contV_pos R.hα hpos (by linarith)
    simp only [Function.comp_apply]
    rw [Real.exp_log (div_pos hf hc)]
  exact isEquivalent_of_tendsto_one hratio

/-- Private helper: the scale identity `c_N κ = N^α finV(1/γ)` along the regime. -/
private lemma pl_scales_main {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) :
    IsEquivalent atTop (fun n => c n * kappaOf α (c n) (N n) (B n))
      (fun n => ((N n : ℕ) : ℝ) ^ α * finV α (N n) (1 / gammaOf (N n) (B n))) := by
  have hγ1 : ∀ᶠ n in atTop, 1 < gammaOf (N n) (B n) :=
    R.hγ.eventually_gt_atTop 1
  have hEq : (fun n => ((N n : ℕ) : ℝ) ^ α * finV α (N n) (1 / gammaOf (N n) (B n))) =ᶠ[atTop]
      (fun n => c n * kappaOf α (c n) (N n) (B n)) := by
    filter_upwards [hγ1] with n hn
    have h1 : (1:ℝ) ∈ Ioo (0:ℝ) (gammaOf (N n) (B n)) := ⟨zero_lt_one, hn⟩
    have hL := eqn_app_pl_Lambda_V α (c n) (R.hNpos n) (R.hBpos n) (R.hcpos n) h1
    show _ = c n * partLam (B n) (plSpec α (c n) (N n)) 1
    rw [hL]
    have hc : c n ≠ 0 := (R.hcpos n).ne'
    field_simp
  exact (IsEquivalent.refl).congr_left hEq

/-- `eqn:app-pl-kappa` (snapshot `cr-2026-10-23`), first display, case `α < 1`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-kappa}
\begin{gathered}
c_N\resscale\sim\begin{cases}(1-\alpha)BN^{\alpha-1},&\alpha<1,\\ B/\log\gamma,&\alpha=1,\\ (B/K_\alpha)^\alpha,&\alpha>1,\end{cases}
\\
\frac{i_{\mathrm c,\mathfrak d}}{i_\#}\sim\begin{cases}\big(\pi/(2\sw2\log^2\gamma)\big)^{1/\alpha},&\alpha<1,\\ 9\pi/(8\sw2\log^2\gamma),&\alpha=1,\end{cases}
\qquad
\frac{i_{\mathrm c}}{i_\#}\to1\ \ (\alpha>1),
\end{gathered}
\end{equation}
-/
theorem prop_app_pl_scales_ii_lt {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α < 1) :
    IsEquivalent atTop (fun n => c n * kappaOf α (c n) (N n) (B n))
      (fun n => (1 - α) * ((B n : ℕ) : ℝ) * ((N n : ℕ) : ℝ) ^ (α - 1)) := by
  have hmain := pl_scales_main R
  have hfc := pl_scales_finV_contV R
  have hcont : IsEquivalent atTop (fun n => contV α (1 / gammaOf (N n) (B n)))
      (fun n => (1 - α) * (1 / gammaOf (N n) (B n))) :=
    (lem_app_pl_continuum_iii_lt R.hα hα1).comp_tendsto (pl_scales_p_tend R)
  have hfin := hfc.trans hcont
  have hmul := (IsEquivalent.refl (u := fun n => ((N n : ℕ) : ℝ) ^ α)).mul hfin
  refine hmain.trans (hmul.congr_right ?_)
  refine Eventually.of_forall (fun n => ?_)
  have hN : ((N n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (R.hNpos n).ne'
  have hB : ((B n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (R.hBpos n).ne'
  show ((N n : ℕ) : ℝ) ^ α * ((1 - α) * (1 / gammaOf (N n) (B n))) =
    (1 - α) * ((B n : ℕ) : ℝ) * ((N n : ℕ) : ℝ) ^ (α - 1)
  rw [Real.rpow_sub_one hN]
  unfold gammaOf
  field_simp

/-- `eqn:app-pl-kappa` (snapshot `cr-2026-10-23`), first display, case `α = 1`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-kappa}
\begin{gathered}
c_N\resscale\sim\begin{cases}(1-\alpha)BN^{\alpha-1},&\alpha<1,\\ B/\log\gamma,&\alpha=1,\\ (B/K_\alpha)^\alpha,&\alpha>1,\end{cases}
\\
\frac{i_{\mathrm c,\mathfrak d}}{i_\#}\sim\begin{cases}\big(\pi/(2\sw2\log^2\gamma)\big)^{1/\alpha},&\alpha<1,\\ 9\pi/(8\sw2\log^2\gamma),&\alpha=1,\end{cases}
\qquad
\frac{i_{\mathrm c}}{i_\#}\to1\ \ (\alpha>1),
\end{gathered}
\end{equation}
-/
theorem prop_app_pl_scales_ii_one {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α = 1) :
    IsEquivalent atTop (fun n => c n * kappaOf α (c n) (N n) (B n))
      (fun n => ((B n : ℕ) : ℝ) / Real.log (gammaOf (N n) (B n))) := by
  subst hα1
  have hmain := pl_scales_main R
  have hfc := pl_scales_finV_contV R
  have hcont : IsEquivalent atTop (fun n => contV 1 (1 / gammaOf (N n) (B n)))
      (fun n => (1 / gammaOf (N n) (B n)) / Real.log (1 / (1 / gammaOf (N n) (B n)))) :=
    lem_app_pl_continuum_iii_one.comp_tendsto (pl_scales_p_tend R)
  have hfin := hfc.trans hcont
  have hmul := (IsEquivalent.refl (u := fun n => ((N n : ℕ) : ℝ) ^ (1:ℝ))).mul hfin
  refine hmain.trans (hmul.congr_right ?_)
  refine Eventually.of_forall (fun n => ?_)
  have hN : ((N n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (R.hNpos n).ne'
  have hB : ((B n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (R.hBpos n).ne'
  show ((N n : ℕ) : ℝ) ^ (1:ℝ) * ((1 / gammaOf (N n) (B n)) /
      Real.log (1 / (1 / gammaOf (N n) (B n)))) = ((B n : ℕ) : ℝ) / Real.log (gammaOf (N n) (B n))
  rw [Real.rpow_one, one_div_one_div]
  unfold gammaOf
  field_simp

/-- `eqn:app-pl-kappa` (snapshot `cr-2026-10-23`), first display, case `1 < α`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-kappa}
\begin{gathered}
c_N\resscale\sim\begin{cases}(1-\alpha)BN^{\alpha-1},&\alpha<1,\\ B/\log\gamma,&\alpha=1,\\ (B/K_\alpha)^\alpha,&\alpha>1,\end{cases}
\\
\frac{i_{\mathrm c,\mathfrak d}}{i_\#}\sim\begin{cases}\big(\pi/(2\sw2\log^2\gamma)\big)^{1/\alpha},&\alpha<1,\\ 9\pi/(8\sw2\log^2\gamma),&\alpha=1,\end{cases}
\qquad
\frac{i_{\mathrm c}}{i_\#}\to1\ \ (\alpha>1),
\end{gathered}
\end{equation}
-/
theorem prop_app_pl_scales_ii_gt {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) :
    IsEquivalent atTop (fun n => c n * kappaOf α (c n) (N n) (B n))
      (fun n => (((B n : ℕ) : ℝ) / Kc α) ^ α) := by
  have hBm : Tendsto (fun n => ((B n : ℕ) : ℝ) * (fun _ : ℕ => (1:ℝ)) n) atTop atTop := by
    simpa using R.hB
  have hmγ : Tendsto (fun n => (fun _ : ℕ => (1:ℝ)) n / gammaOf (N n) (B n)) atTop (𝓝 0) := by
    have := (pl_scales_p_tend R).mono_right nhdsWithin_le_nhds
    simpa using this
  have key := lem_app_pl_finite_inverse_iv_i R hα1 (fun _ => (1:ℝ)) hBm hmγ
  simp only [mul_one] at key
  exact key

/-- Private helper: `∑_j w_j^2 > 0` for `0 < β < 1`. -/
private lemma pl_sPow2_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : 0 < sPow β 2 := by
  unfold sPow
  have hs : Summable (fun j : ℕ => emaW β j ^ 2) := by
    have h := (summable_geometric_of_lt_one (sq_nonneg β)
      (by nlinarith : β ^ 2 < 1)).mul_left ((1 - β) ^ 2)
    refine h.congr (fun j => ?_)
    unfold emaW
    ring
  have h1 : 0 < 1 - β := by linarith
  refine hs.tsum_pos (fun j => sq_nonneg _) 0 ?_
  unfold emaW
  simp only [pow_zero, mul_one]
  exact pow_pos h1 2

/-- Private helper: `c0 ^ 2 = 2/π`. -/
private lemma pl_c0_sq : c0 ^ 2 = 2 / Real.pi := by
  unfold c0
  rw [Real.sq_sqrt (show (0:ℝ) ≤ 2 / Real.pi by positivity)]

/-- Private helper: `icdD α ^ 2 = 2/(π(1-α))` for `α < 1`. -/
private lemma pl_icdD_sq {α : ℝ} (hα1 : α < 1) : icdD α ^ 2 = 2 / (Real.pi * (1 - α)) := by
  unfold icdD
  rw [if_pos hα1, div_pow, Real.sq_sqrt (show (0:ℝ) ≤ 1 - α by linarith), pl_c0_sq, div_div]

/-- Private helper: `icdD 1 ^ 2 = 8/(9π)`. -/
private lemma pl_icdD_one_sq : icdD 1 ^ 2 = 8 / (9 * Real.pi) := by
  unfold icdD
  rw [if_neg (lt_irrefl _), mul_pow, pl_c0_sq]
  ring

/-- Private helper: `Kc α > 0` for `1 < α`. -/
private lemma pl_Kc_pos {α : ℝ} (hα : 1 < α) : 0 < Kc α := by
  unfold Kc
  apply div_pos Real.pi_pos
  apply mul_pos (by linarith)
  apply Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos (by linarith))
  rw [div_lt_iff₀ (by linarith)]
  exact lt_mul_of_one_lt_right Real.pi_pos hα

/-- Private helper: the product `c_n κ_n` is eventually positive along the regime. -/
private lemma pl_scales_kappa_pos {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) :
    ∀ᶠ n in atTop, 0 < c n * kappaOf α (c n) (N n) (B n) := by
  have hγ1 : ∀ᶠ n in atTop, 1 < gammaOf (N n) (B n) := R.hγ.eventually_gt_atTop 1
  filter_upwards [hγ1] with n hn
  exact mul_pos (R.hcpos n) (prop_app_pl_scales_i (c n) R.hα (R.hNpos n) (R.hBpos n)
    (R.hcpos n) hn).1

/-- Private helper: pointwise ratio identity for `α < 1`, `i_{c,𝔡}/i_#` against `(π/(2 S L²))^{1/α}`. -/
private lemma pl_iii_lt_pt {α S B q L k : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hS : 0 < S)
    (hL : 0 < L) (hB : 0 < B) (hq : 0 < q) (hk : 0 < k) :
    (B * q / (S * icdD α ^ 2 * L ^ 2)) ^ (1 / α) / k ^ (1 / α) /
        (Real.pi / (2 * S * L ^ 2)) ^ (1 / α) = ((1 - α) * B * q / k) ^ (1 / α) := by
  have hX : 0 ≤ B * q / (S * icdD α ^ 2 * L ^ 2) :=
    div_nonneg (mul_nonneg hB.le hq.le) (mul_nonneg (mul_nonneg hS.le (sq_nonneg _)) (sq_nonneg _))
  have hY : 0 ≤ Real.pi / (2 * S * L ^ 2) :=
    div_nonneg Real.pi_pos.le (mul_nonneg (mul_nonneg (by norm_num) hS.le) (sq_nonneg _))
  rw [← Real.div_rpow hX hk.le, ← Real.div_rpow (div_nonneg hX hk.le) hY]
  congr 1
  rw [pl_icdD_sq hα1]
  have := hS.ne'
  have := hL.ne'
  have := hk.ne'
  have := Real.pi_pos.ne'
  have h1 : (0:ℝ) < 1 - α := by linarith
  have := h1.ne'
  field_simp

/-- Private helper: pointwise ratio identity for `α = 1` (after `subst`). -/
private lemma pl_iii_one_pt {S B L k : ℝ} (hS : 0 < S) (hL : 0 < L) (hk : 0 < k) :
    B / (S * icdD 1 ^ 2 * L ^ 3) / k / (9 * Real.pi / (8 * S * L ^ 2)) = B / L / k := by
  rw [pl_icdD_one_sq]
  have := hS.ne'
  have := hL.ne'
  have := hk.ne'
  have := Real.pi_pos.ne'
  field_simp

/-- Private helper: pointwise ratio identity for `α < 1` in the `i_{c,𝔳}` form. -/
private lemma pl_iv_ratio_pt {α S B q L k : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hS : 0 < S)
    (hL : 0 < L) (hB : 0 < B) (hq : 0 < q) (hk : 0 < k) :
    c0 ^ (2 / α) * (B * q / (S * icdD α ^ 2 * L ^ 2)) ^ (1 / α) / k ^ (1 / α) /
        (S * L ^ 2) ^ (-(1 / α)) = ((1 - α) * B * q / k) ^ (1 / α) := by
  have hX : 0 ≤ B * q / (S * icdD α ^ 2 * L ^ 2) :=
    div_nonneg (mul_nonneg hB.le hq.le) (mul_nonneg (mul_nonneg hS.le (sq_nonneg _)) (sq_nonneg _))
  have hSL : 0 < S * L ^ 2 := mul_pos hS (pow_pos hL 2)
  have hc0 : 0 ≤ c0 := by unfold c0; positivity
  have hcpow : c0 ^ (2 / α) = (c0 ^ 2) ^ (1 / α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc0]
    congr 1
    push_cast
    ring
  rw [hcpow, Real.rpow_neg hSL.le, ← Real.inv_rpow hSL.le,
    ← Real.mul_rpow (pow_nonneg hc0 2) hX,
    ← Real.div_rpow (mul_nonneg (pow_nonneg hc0 2) hX) hk.le,
    ← Real.div_rpow (div_nonneg (mul_nonneg (pow_nonneg hc0 2) hX) hk.le)
      (inv_nonneg.2 hSL.le)]
  congr 1
  rw [pl_c0_sq, pl_icdD_sq hα1]
  have := hS.ne'
  have := hL.ne'
  have := hk.ne'
  have := Real.pi_pos.ne'
  have h1 : (0:ℝ) < 1 - α := by linarith
  have := h1.ne'
  field_simp

/-- `eqn:app-pl-kappa` (snapshot `cr-2026-10-23`), second display, `i_{c,𝔡}/i_#` for `α < 1`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-kappa}
\begin{gathered}
c_N\resscale\sim\begin{cases}(1-\alpha)BN^{\alpha-1},&\alpha<1,\\ B/\log\gamma,&\alpha=1,\\ (B/K_\alpha)^\alpha,&\alpha>1,\end{cases}
\\
\frac{i_{\mathrm c,\mathfrak d}}{i_\#}\sim\begin{cases}\big(\pi/(2\sw2\log^2\gamma)\big)^{1/\alpha},&\alpha<1,\\ 9\pi/(8\sw2\log^2\gamma),&\alpha=1,\end{cases}
\qquad
\frac{i_{\mathrm c}}{i_\#}\to1\ \ (\alpha>1),
\end{gathered}
\end{equation}
-/
theorem prop_app_pl_scales_iii_lt {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α < 1) :
    IsEquivalent atTop
      (fun n => icdIdx β α (N n) (B n) / iSharp α (c n) (N n) (B n))
      (fun n => (Real.pi / (2 * sPow β 2 * Real.log (gammaOf (N n) (B n)) ^ 2)) ^ (1 / α)) := by
  have hS : 0 < sPow β 2 := pl_sPow2_pos R.hβ0 R.hβ1
  have hII := pl_scales_kappa_pos R
  have hγ1 : ∀ᶠ n in atTop, 1 < gammaOf (N n) (B n) := R.hγ.eventually_gt_atTop 1
  have hr0 : Tendsto (fun n => (1 - α) * ((B n : ℕ) : ℝ) * ((N n : ℕ) : ℝ) ^ (α - 1) /
      (c n * kappaOf α (c n) (N n) (B n))) atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one (hII.mono fun n h => h.ne')).1
      (prop_app_pl_scales_ii_lt R hα1).symm
  have hr := Filter.Tendsto.rpow_const hr0 (Or.inr (one_div_nonneg.2 R.hα.le))
  rw [Real.one_rpow] at hr
  apply isEquivalent_of_tendsto_one
  refine Tendsto.congr' ?_ hr
  filter_upwards [hγ1, hII] with n hn1 hn2
  simp only [Pi.div_apply]
  unfold icdIdx iSharp
  rw [if_pos hα1]
  exact (pl_iii_lt_pt R.hα hα1 hS (Real.log_pos hn1) (by exact_mod_cast R.hBpos n)
    (Real.rpow_pos_of_pos (by exact_mod_cast R.hNpos n) _) hn2).symm

/-- `eqn:app-pl-kappa` (snapshot `cr-2026-10-23`), second display, `i_{c,𝔡}/i_#` for `α = 1`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-kappa}
\begin{gathered}
c_N\resscale\sim\begin{cases}(1-\alpha)BN^{\alpha-1},&\alpha<1,\\ B/\log\gamma,&\alpha=1,\\ (B/K_\alpha)^\alpha,&\alpha>1,\end{cases}
\\
\frac{i_{\mathrm c,\mathfrak d}}{i_\#}\sim\begin{cases}\big(\pi/(2\sw2\log^2\gamma)\big)^{1/\alpha},&\alpha<1,\\ 9\pi/(8\sw2\log^2\gamma),&\alpha=1,\end{cases}
\qquad
\frac{i_{\mathrm c}}{i_\#}\to1\ \ (\alpha>1),
\end{gathered}
\end{equation}
-/
theorem prop_app_pl_scales_iii_one {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α = 1) :
    IsEquivalent atTop
      (fun n => icdIdx β α (N n) (B n) / iSharp α (c n) (N n) (B n))
      (fun n => 9 * Real.pi / (8 * sPow β 2 * Real.log (gammaOf (N n) (B n)) ^ 2)) := by
  subst hα1
  have hS : 0 < sPow β 2 := pl_sPow2_pos R.hβ0 R.hβ1
  have hII := pl_scales_kappa_pos R
  have hγ1 : ∀ᶠ n in atTop, 1 < gammaOf (N n) (B n) := R.hγ.eventually_gt_atTop 1
  have hr : Tendsto (fun n => ((B n : ℕ) : ℝ) / Real.log (gammaOf (N n) (B n)) /
      (c n * kappaOf 1 (c n) (N n) (B n))) atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one (hII.mono fun n h => h.ne')).1
      (prop_app_pl_scales_ii_one R rfl).symm
  apply isEquivalent_of_tendsto_one
  refine Tendsto.congr' ?_ hr
  filter_upwards [hγ1, hII] with n hn1 hn2
  simp only [Pi.div_apply]
  unfold icdIdx iSharp
  rw [if_neg (lt_irrefl _), div_one, Real.rpow_one]
  exact (pl_iii_one_pt hS (Real.log_pos hn1) hn2).symm

/-- `eqn:app-pl-kappa` (snapshot `cr-2026-10-23`), second display, `i_c/i_# → 1` for `1 < α`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-kappa}
\begin{gathered}
c_N\resscale\sim\begin{cases}(1-\alpha)BN^{\alpha-1},&\alpha<1,\\ B/\log\gamma,&\alpha=1,\\ (B/K_\alpha)^\alpha,&\alpha>1,\end{cases}
\\
\frac{i_{\mathrm c,\mathfrak d}}{i_\#}\sim\begin{cases}\big(\pi/(2\sw2\log^2\gamma)\big)^{1/\alpha},&\alpha<1,\\ 9\pi/(8\sw2\log^2\gamma),&\alpha=1,\end{cases}
\qquad
\frac{i_{\mathrm c}}{i_\#}\to1\ \ (\alpha>1),
\end{gathered}
\end{equation}
-/
theorem prop_app_pl_scales_iii_gt {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : 1 < α) :
    Tendsto (fun n => icCross α (B n) / iSharp α (c n) (N n) (B n)) atTop (𝓝 1) := by
  have hα0 : 0 < α := by linarith
  have hII := pl_scales_kappa_pos R
  have hr0 : Tendsto (fun n => ((((B n : ℕ) : ℝ) / Kc α) ^ α) / (c n * kappaOf α (c n) (N n) (B n)))
      atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one (hII.mono fun n h => h.ne')).1
      (prop_app_pl_scales_ii_gt R hα1).symm
  have hr := Filter.Tendsto.rpow_const hr0 (Or.inr (one_div_nonneg.2 hα0.le))
  rw [Real.one_rpow] at hr
  refine Tendsto.congr' ?_ hr
  filter_upwards [hII] with n hn
  have hKc := pl_Kc_pos hα1
  have hB : (0:ℝ) ≤ ((B n : ℕ) : ℝ) := by positivity
  have hA : 0 ≤ (((B n : ℕ) : ℝ) / Kc α) ^ α := Real.rpow_nonneg (div_nonneg hB hKc.le) α
  unfold icCross iSharp
  rw [Real.div_rpow hA hn.le, one_div, Real.rpow_rpow_inv (div_nonneg hB hKc.le) hα0.ne']

/-- `prop:app-pl-scales` (snapshot `cr-2026-10-23`), the ratio `i_{c,𝔳}/i_#` for `α < 1`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{proposition}[Reference scales]\label{prop:app-pl-scales}
Assume \cref{assum:app-pl-regime}. For $\gamma>1$ let $\resscale\defeq\Lambda_N(1)$ be the
unique solution of
\[
\sum_{i=1}^N\frac{\resscale\mu_i}{1+\resscale\mu_i}=B,
\]
and put $i_\#\defeq(c_N\resscale)^{1/\alpha}$. Then
\begin{equation}\label{eqn:app-pl-kappa}
\begin{gathered}
c_N\resscale\sim\begin{cases}(1-\alpha)BN^{\alpha-1},&\alpha<1,\\ B/\log\gamma,&\alpha=1,\\ (B/K_\alpha)^\alpha,&\alpha>1,\end{cases}
\\
\frac{i_{\mathrm c,\mathfrak d}}{i_\#}\sim\begin{cases}\big(\pi/(2\sw2\log^2\gamma)\big)^{1/\alpha},&\alpha<1,\\ 9\pi/(8\sw2\log^2\gamma),&\alpha=1,\end{cases}
\qquad
\frac{i_{\mathrm c}}{i_\#}\to1\ \ (\alpha>1),
\end{gathered}
\end{equation}
and $i_{\mathrm c,\mathfrak v}/i_\#\sim(\sw2\log^2\gamma)^{-1/\alpha}$ for $\alpha<1$ and
$\sim9/(4\sw2\log^2\gamma)$ for $\alpha=1$.
\end{proposition}
-/
theorem prop_app_pl_scales_iv_lt {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α < 1) :
    IsEquivalent atTop
      (fun n => icvIdx β α (N n) (B n) / iSharp α (c n) (N n) (B n))
      (fun n => (sPow β 2 * Real.log (gammaOf (N n) (B n)) ^ 2) ^ (-(1 / α))) := by
  have hS : 0 < sPow β 2 := pl_sPow2_pos R.hβ0 R.hβ1
  have hII := pl_scales_kappa_pos R
  have hγ1 : ∀ᶠ n in atTop, 1 < gammaOf (N n) (B n) := R.hγ.eventually_gt_atTop 1
  have hr0 : Tendsto (fun n => (1 - α) * ((B n : ℕ) : ℝ) * ((N n : ℕ) : ℝ) ^ (α - 1) /
      (c n * kappaOf α (c n) (N n) (B n))) atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one (hII.mono fun n h => h.ne')).1
      (prop_app_pl_scales_ii_lt R hα1).symm
  have hr := Filter.Tendsto.rpow_const hr0 (Or.inr (one_div_nonneg.2 R.hα.le))
  rw [Real.one_rpow] at hr
  apply isEquivalent_of_tendsto_one
  refine Tendsto.congr' ?_ hr
  filter_upwards [hγ1, hII] with n hn1 hn2
  simp only [Pi.div_apply]
  unfold icvIdx icdIdx iSharp
  rw [if_pos hα1]
  have hBr : (0:ℝ) < ((B n : ℕ) : ℝ) := by exact_mod_cast R.hBpos n
  have hqr : (0:ℝ) < ((N n : ℕ) : ℝ) ^ (α - 1) :=
    Real.rpow_pos_of_pos (by exact_mod_cast R.hNpos n) _
  exact (pl_iv_ratio_pt R.hα hα1 hS (Real.log_pos hn1) hBr hqr hn2).symm

/-- `prop:app-pl-scales` (snapshot `cr-2026-10-23`), the ratio `i_{c,𝔳}/i_#` for `α = 1`. LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{proposition}[Reference scales]\label{prop:app-pl-scales}
Assume \cref{assum:app-pl-regime}. For $\gamma>1$ let $\resscale\defeq\Lambda_N(1)$ be the
unique solution of
\[
\sum_{i=1}^N\frac{\resscale\mu_i}{1+\resscale\mu_i}=B,
\]
and put $i_\#\defeq(c_N\resscale)^{1/\alpha}$. Then
\begin{equation}\label{eqn:app-pl-kappa}
\begin{gathered}
c_N\resscale\sim\begin{cases}(1-\alpha)BN^{\alpha-1},&\alpha<1,\\ B/\log\gamma,&\alpha=1,\\ (B/K_\alpha)^\alpha,&\alpha>1,\end{cases}
\\
\frac{i_{\mathrm c,\mathfrak d}}{i_\#}\sim\begin{cases}\big(\pi/(2\sw2\log^2\gamma)\big)^{1/\alpha},&\alpha<1,\\ 9\pi/(8\sw2\log^2\gamma),&\alpha=1,\end{cases}
\qquad
\frac{i_{\mathrm c}}{i_\#}\to1\ \ (\alpha>1),
\end{gathered}
\end{equation}
and $i_{\mathrm c,\mathfrak v}/i_\#\sim(\sw2\log^2\gamma)^{-1/\alpha}$ for $\alpha<1$ and
$\sim9/(4\sw2\log^2\gamma)$ for $\alpha=1$.
\end{proposition}
-/
theorem prop_app_pl_scales_iv_one {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α = 1) :
    IsEquivalent atTop
      (fun n => icvIdx β α (N n) (B n) / iSharp α (c n) (N n) (B n))
      (fun n => 9 / (4 * sPow β 2 * Real.log (gammaOf (N n) (B n)) ^ 2)) := by
  subst hα1
  have hS : 0 < sPow β 2 := pl_sPow2_pos R.hβ0 R.hβ1
  have hII := pl_scales_kappa_pos R
  have hγ1 : ∀ᶠ n in atTop, 1 < gammaOf (N n) (B n) := R.hγ.eventually_gt_atTop 1
  have hr : Tendsto (fun n => ((B n : ℕ) : ℝ) / Real.log (gammaOf (N n) (B n)) /
      (c n * kappaOf 1 (c n) (N n) (B n))) atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one (hII.mono fun n h => h.ne')).1
      (prop_app_pl_scales_ii_one R rfl).symm
  apply isEquivalent_of_tendsto_one
  refine Tendsto.congr' ?_ hr
  filter_upwards [hγ1, hII] with n hn1 hn2
  simp only [Pi.div_apply]
  have hBr : (0:ℝ) < ((B n : ℕ) : ℝ) := by exact_mod_cast R.hBpos n
  have hLne := (Real.log_pos hn1).ne'
  have hkne := hn2.ne'
  have hSne := hS.ne'
  have hpi := Real.pi_pos.ne'
  unfold icvIdx icdIdx iSharp
  simp only [lt_self_iff_false, if_false, div_one, Real.rpow_one, Real.rpow_two]
  rw [pl_icdD_one_sq, pl_c0_sq]
  field_simp
  ring

end Muon.PowerLaw

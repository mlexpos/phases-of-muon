import Muon.PowerLaw.Weights
import Muon.PowerLaw.Participation
import Muon.PowerLaw.Continuum
import Muon.PowerLaw.Profiles

/-!
# Appendix G: volatility kernel in participation coordinates (work package L-G.5)

Snapshot `cr-2026-10-23`. Source: `sections/06-power-law/section.tex`, the participation kernel
(`eqn:app-pl-participation-kernel`, l.561–571), the participation form of the volatility
(`eqn:app-pl-vol-zero`, l.586–589), the coefficient `𝔳_i[I,J]` (l.1743–1749), and the lemmas
`lem:app-pl-determinant`, `lem:app-pl-age`, `lem:app-pl-localization`, `lem:app-pl-upper`
(subsection "Proof of the volatility statements"). Card §2, §3 and §5 (L-G.5).

Representation choices:

* Power-law spectrum `μ = plSpec α c N` (`Muon.PowerLaw.Continuum`), `γ = gammaOf N B`, momentum
  `β ∈ (0,1)`. Participation objects `partF`, `partLam`, `thetaN`, `gammaOf` and the EMA objects
  `Qm`, `Efun`, `emaW`, `rW`, `DLag`, `DLagNat`, `MLag`, `MLagNat` are reused, not redefined.
* Lags: `DLag`, `MLag`, `deltaN` take `ℓ : ℤ` and follow the source's negative-lag convention
  (`section.tex` l.568–569). `localization(i)` and the first `D`-bound are stated for `ℓ : ℕ`
  with `DLagNat`, as the source's `ℓ ≥ 0`.
* `Zg β g q` is `𝒵_g(q)` of `lem:app-pl-age`, with `∑'` over ages (absolutely summable, so no
  junk value). `Ag β g m` is `𝒜_g(m)`. `vFlat` is `𝔳^flat_i`.
* `lagNumer` is `W_i(m₁)W_i(m₂)𝖣_ℓ(m₁,m₂)`, `lagIntegrand` is the same with `1/Δ^N_ℓ`, and
  `lagTerm I J ℓ` is the iterated integral `∫_I∫_J lagIntegrand` (`dm₂ dm₁`, as in l.1745).
  `vIJ I J = π⁻² ∑_{ℓ∈ℤ} lagTerm I J ℓ` is `𝔳_i[I,J]`; `vIJ (0,γ) (0,γ)` is `𝔳_i(0)` by the
  source's own identity (l.1748–1749).
* `CbarPart i ℓ` is the integral form of `eqn:app-pl-vol-zero`, for all `ℓ ∈ ℤ`. `vPart` is the
  card's helper `1 + 2∑_{ℓ≥1} CbarPart i ℓ`. It is not a restatement of `vIJ`: the identity
  `CbarPart i 0 = 1` is a consequence of `prop:app-pl-vol-zero`(i),(iii), outside this package.
* Finiteness. Where the source asserts that a integral or a series is finite, the statement carries
  `IntegrableOn`, `Integrable`, `IntervalIntegrable`, `HasSum` or `Summable` conjuncts. No
  definition relies on a Bochner or `tsum` junk value.
* Quantifiers: the determinant and localization statements range over all `(N,B,c)` with
  `0 < N`, `0 < B`, `0 < c` (the source's "independent of `N,B,c_N,Λ`"). `lem:app-pl-upper` says
  "for all large `N`" and leaves `B` and `c` unspecified; it is stated along every sequence
  `(N_n, B_n, c_n)` satisfying `assum_app_pl_regime`, eventually in `n`, with `C = C(α,β,η)`.
-/

set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology Set Asymptotics
open Muon.DetEquiv

noncomputable section

namespace Muon.PowerLaw

/-! ## Objects of the volatility kernel -/

/-- `eqn:app-pl-participation-kernel` (`W_i`; snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-participation-kernel}
\begin{gathered}
W_i(m)\defeq\frac{\sqrt{\mu_i\Lambda_N(m)}}{\sqrt m\,\big(1+\mu_i\Lambda_N(m)\big)}\sqrt{1-\frac m\gamma}\;\vartheta_N(m),\qquad
\mathsf T_N(m_1,m_2)\defeq\frac1B\sum_{j=1}^Nf_j(m_1)f_j(m_2),\\
\mathsf D_\ell\defeq\sum_{a\ge0}\EE\frac{\bmom^\ell\sqrt{q_1q_2}\,\emaw a^2g^2}{(1+q_1\emaw a^2g^2)(1+\bmom^{2\ell}q_2\emaw a^2g^2)},\qquad
\mathsf M_\ell\defeq\sum_{a\ge0}\EE\frac{\bmom^{2\ell}q_1q_2\,\emaw a^4g^4}{(1+q_1\emaw a^2g^2)(1+\bmom^{2\ell}q_2\emaw a^2g^2)},\\
\Delta_\ell^N\defeq\Big(1-\frac{\mathsf T_N\mathsf M_\ell}{m_1m_2}\Big)\Big(1-\frac{\mathsf M_\ell}{\gamma}\Big)-\frac{\mathsf T_N\mathsf D_\ell^2}{\gamma\,m_1m_2},
\end{gathered}
\end{equation}
all evaluated at $(m_1,m_2)$; for a negative lag $-\ell$ the three functions
$\mathsf D,\mathsf M,\Delta^N$ are those of the lag $\ell$ at $(m_2,m_1)$.
-/
def Wpart (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (m : ℝ) : ℝ :=
  Real.sqrt (μ i * partLam B μ m) / (Real.sqrt m * (1 + μ i * partLam B μ m)) *
    Real.sqrt (1 - m / gammaOf N B) * thetaN β B μ m

/-- `𝖳_N(m₁,m₂) = B⁻¹ ∑_j f_j(m₁) f_j(m₂)` (`eqn:app-pl-participation-kernel`, `section.tex`
l.559–571; `f_j` is `partF`). -/
def TNpart (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (m₁ m₂ : ℝ) : ℝ :=
  (B : ℝ)⁻¹ * ∑ j : Fin N, partF B μ j m₁ * partF B μ j m₂

/-- `eqn:app-pl-participation-kernel` (`Δ^N_ℓ`; snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-participation-kernel}
\begin{gathered}
W_i(m)\defeq\frac{\sqrt{\mu_i\Lambda_N(m)}}{\sqrt m\,\big(1+\mu_i\Lambda_N(m)\big)}\sqrt{1-\frac m\gamma}\;\vartheta_N(m),\qquad
\mathsf T_N(m_1,m_2)\defeq\frac1B\sum_{j=1}^Nf_j(m_1)f_j(m_2),\\
\mathsf D_\ell\defeq\sum_{a\ge0}\EE\frac{\bmom^\ell\sqrt{q_1q_2}\,\emaw a^2g^2}{(1+q_1\emaw a^2g^2)(1+\bmom^{2\ell}q_2\emaw a^2g^2)},\qquad
\mathsf M_\ell\defeq\sum_{a\ge0}\EE\frac{\bmom^{2\ell}q_1q_2\,\emaw a^4g^4}{(1+q_1\emaw a^2g^2)(1+\bmom^{2\ell}q_2\emaw a^2g^2)},\\
\Delta_\ell^N\defeq\Big(1-\frac{\mathsf T_N\mathsf M_\ell}{m_1m_2}\Big)\Big(1-\frac{\mathsf M_\ell}{\gamma}\Big)-\frac{\mathsf T_N\mathsf D_\ell^2}{\gamma\,m_1m_2},
\end{gathered}
\end{equation}
all evaluated at $(m_1,m_2)$; for a negative lag $-\ell$ the three functions
$\mathsf D,\mathsf M,\Delta^N$ are those of the lag $\ell$ at $(m_2,m_1)$.
-/
def deltaN (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (ℓ : ℤ) (m₁ m₂ : ℝ) : ℝ :=
  (1 - TNpart B μ m₁ m₂ * MLag β (Qm β m₁) (Qm β m₂) ℓ / (m₁ * m₂)) *
      (1 - MLag β (Qm β m₁) (Qm β m₂) ℓ / gammaOf N B) -
    TNpart B μ m₁ m₂ * DLag β (Qm β m₁) (Qm β m₂) ℓ ^ 2 / (gammaOf N B * m₁ * m₂)

/-- The lag-`ℓ` numerator `W_i(m₁) W_i(m₂) 𝖣_ℓ(m₁,m₂)` of `eqn:app-pl-vol-zero` and of
`𝔳_i[I,J]` (`section.tex` l.1745–1749, with `Δ^N_ℓ` removed). -/
def lagNumer (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (ℓ : ℤ) (m₁ m₂ : ℝ) : ℝ :=
  Wpart β B μ i m₁ * Wpart β B μ i m₂ * DLag β (Qm β m₁) (Qm β m₂) ℓ

/-- The lag-`ℓ` integrand `W_i(m₁) W_i(m₂) 𝖣_ℓ(m₁,m₂) / Δ^N_ℓ(m₁,m₂)` of `𝔳_i[I,J]`
(`section.tex` l.1745–1749). -/
def lagIntegrand (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (ℓ : ℤ) (m₁ m₂ : ℝ) : ℝ :=
  lagNumer β B μ i ℓ m₁ m₂ / deltaN β B μ ℓ m₁ m₂

/-- The lag-`ℓ` term `∫_I ∫_J W_i(m₁)W_i(m₂) 𝖣_ℓ/Δ^N_ℓ dm₂ dm₁` of `𝔳_i[I,J]` (without `π⁻²`). -/
def lagTerm (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (I J : Set ℝ) (ℓ : ℤ) : ℝ :=
  ∫ m₁ in I, ∫ m₂ in J, lagIntegrand β B μ i ℓ m₁ m₂

/-- `𝔳_i[I,J]`, the participation form of `eqn:app-pl-vol-zero` (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:


Throughout this subsection the volatility is used in the participation form
\cref{eqn:app-pl-vol-zero}. For intervals $I,J\subset(0,\gamma)$ write
\[
\mathfrak v_i[I,J]\defeq\frac1{\pi^2}\sum_{\ell\in\mathbb Z}\int_I\!\int_JW_i(m_1)W_i(m_2)\,\frac{\mathsf D_\ell(m_1,m_2)}{\Delta^N_\ell(m_1,m_2)}\,\dif m_2\,\dif m_1,
\]
so that $\mathfrak v_i(0)=\mathfrak v_i[(0,\gamma),(0,\gamma)]$, and $m_-\defeq\min(m_1,m_2)$, $m_+\defeq\max(m_1,m_2)$.
-/
def vIJ (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (I J : Set ℝ) : ℝ :=
  (Real.pi ^ 2)⁻¹ * ∑' ℓ : ℤ, lagTerm β B μ i I J ℓ

/-- `eqn:app-pl-vol-zero` (`C̄_{i,ℓ}(0)` integral form; snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{equation}\label{eqn:app-pl-vol-zero}
\overline C_{i,\ell}(0)=\frac4{\pi^2}\int_0^\infty\!\!\int_0^\infty\mathfrak k_{i,\ell}(x^2,y^2)\,\dif x\,\dif y
=\frac1{\pi^2}\int_0^\gamma\!\!\int_0^\gamma W_i(m_1)W_i(m_2)\,\frac{\mathsf D_\ell}{\Delta_\ell^N}\,\dif m_1\,\dif m_2 ,
\end{equation}
-/
def CbarPart (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (ℓ : ℤ) : ℝ :=
  (Real.pi ^ 2)⁻¹ * lagTerm β B μ i (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) ℓ

/-- `vPart i = 1 + 2 ∑_{ℓ≥1} CbarPart i ℓ` (card §2 helper; the `ℓ = 0` term is the constant `1`
of `prop:app-pl-vol-zero`(i)). -/
def vPart (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) : ℝ :=
  1 + 2 * ∑' ℓ : ℕ, CbarPart β B μ i ((ℓ : ℤ) + 1)

/-! ## The age factor (`lem:app-pl-age`) -/

/-- `𝒵_g(q) = √q ∑_{a≥0} w_a g (1 + w_a² q g²)⁻¹` with `w_a = emaW β a` (`lem:app-pl-age`,
`section.tex` l.1805–1806). -/
def Zg (β g q : ℝ) : ℝ :=
  Real.sqrt q * ∑' a : ℕ, emaW β a * g / (1 + emaW β a ^ 2 * q * g ^ 2)

/-- `𝒜_g(m) = 𝒵_g(Q_m)/E(m)` (`lem:app-pl-age`(ii), `section.tex` l.1820–1823). -/
def Ag (β g m : ℝ) : ℝ :=
  Zg β g (Qm β m) / Efun β m

/-- `𝔳^flat_i = 𝔼[(π⁻¹ ∫_0^γ W_i(m) 𝒵_g(Q_m) dm)²]` (`lem:app-pl-age`(iv), `section.tex`
l.1817–1820 and l.1931–1937). -/
def vFlat (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) : ℝ :=
  ∫ g : ℝ, (Real.pi⁻¹ * ∫ m in Ioo 0 (gammaOf N B), Wpart β B μ i m * Zg β g (Qm β m)) ^ 2
    ∂(gaussianReal 0 1)

/-! ## Statements -/

/-! ### Private helpers for the determinant chain (fully proved) -/

private lemma vk_pos_plSpec {α c : ℝ} (hc : 0 < c) (N : ℕ) (i : Fin N) : 0 < plSpec α c N i := by
  unfold plSpec
  have : (0:ℝ) < ((i : ℕ) : ℝ) + 1 := by positivity
  exact mul_pos hc (Real.rpow_pos_of_pos this _)

private lemma vk_partLam_pos {N B : ℕ} {μ : Fin N → ℝ} (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) : 0 < partLam B μ m :=
  (def_app_pl_participation_bij μ hB hN hpos).2.1.mapsTo hm

private lemma vk_partMN_partLam {N B : ℕ} {μ : Fin N → ℝ} (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    partMN B μ (partLam B μ m) = m := by
  have hs := (def_app_pl_participation_bij μ hB hN hpos).1.surjOn hm
  exact Function.invFunOn_eq (f := partMN B μ) (s := Ioi 0) (b := m) hs

private lemma vk_sat_mono {x y μ : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hμ : 0 ≤ μ) :
    x * μ / (1 + x * μ) ≤ y * μ / (1 + y * μ) := by
  have h1 : 0 ≤ x * μ := mul_nonneg hx hμ
  have h2 : x * μ ≤ y * μ := mul_le_mul_of_nonneg_right hxy hμ
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

private lemma vk_sat_nonneg {x μ : ℝ} (hx : 0 ≤ x) (hμ : 0 ≤ μ) :
    0 ≤ x * μ / (1 + x * μ) :=
  div_nonneg (mul_nonneg hx hμ) (by have := mul_nonneg hx hμ; linarith)

private lemma vk_sat_le_one {x μ : ℝ} (hx : 0 ≤ x) (hμ : 0 ≤ μ) :
    x * μ / (1 + x * μ) ≤ 1 := by
  have := mul_nonneg hx hμ
  rw [div_le_one (by linarith)]
  linarith

private lemma vk_partMN_hasDeriv {N B : ℕ} (μ : Fin N → ℝ) {Λ : ℝ} (hΛ : 0 < Λ)
    (hpos : ∀ i, 0 < μ i) :
    deriv (partMN B μ) Λ = (B : ℝ)⁻¹ * ∑ i, μ i / (1 + Λ * μ i) ^ 2 := by
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      HasDerivAt (fun x : ℝ => x * μ i / (1 + x * μ i)) (μ i / (1 + Λ * μ i) ^ 2) Λ := by
    intro i _
    have hμ := hpos i
    have h1 : HasDerivAt (fun x : ℝ => x * μ i) (μ i) Λ := by
      simpa using (hasDerivAt_id Λ).mul_const (μ i)
    have h2 : HasDerivAt (fun x : ℝ => 1 + x * μ i) (μ i) Λ := by
      simpa using h1.const_add 1
    have hne : (1 + Λ * μ i) ≠ 0 := by
      have := mul_pos hΛ hμ
      linarith
    have h3 := h1.div h2 hne
    convert h3 using 1
    field_simp
    ring
  have hsum := HasDerivAt.fun_sum hterm
  have hfun : partMN B μ = fun x : ℝ => (B : ℝ)⁻¹ * ∑ i, x * μ i / (1 + x * μ i) := rfl
  rw [hfun]
  exact ((hsum.const_mul (B : ℝ)⁻¹)).deriv

private lemma vk_diag_identity {N B : ℕ} (μ : Fin N → ℝ) {Λ : ℝ} (hΛ : 0 < Λ)
    (hpos : ∀ i, 0 < μ i) :
    partMN B μ Λ - Λ * deriv (partMN B μ) Λ =
      (B : ℝ)⁻¹ * ∑ i, (Λ * μ i / (1 + Λ * μ i)) ^ 2 := by
  rw [vk_partMN_hasDeriv μ hΛ hpos]
  have hsub : ∑ i, Λ * μ i / (1 + Λ * μ i) - Λ * ∑ i, μ i / (1 + Λ * μ i) ^ 2 =
      ∑ i, (Λ * μ i / (1 + Λ * μ i)) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hμ := hpos i
    have hx : (1 + Λ * μ i) ≠ 0 := by
      have := mul_pos hΛ hμ
      linarith
    field_simp
    ring
  unfold partMN
  have e : (B : ℝ)⁻¹ * ∑ i, Λ * μ i / (1 + Λ * μ i) -
      Λ * ((B : ℝ)⁻¹ * ∑ i, μ i / (1 + Λ * μ i) ^ 2) =
      (B : ℝ)⁻¹ * (∑ i, Λ * μ i / (1 + Λ * μ i) - Λ * ∑ i, μ i / (1 + Λ * μ i) ^ 2) := by
    ring
  rw [e, hsub]

private lemma vk_TN_diag {N B : ℕ} {μ : Fin N → ℝ} (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    TNpart B μ m m = m - partLam B μ m * deriv (partMN B μ) (partLam B μ m) := by
  have hΛ := vk_partLam_pos hB hN hpos hm
  have key := vk_diag_identity (B := B) μ hΛ hpos
  rw [vk_partMN_partLam hB hN hpos hm] at key
  rw [key]
  unfold TNpart partF
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-! ### Private helpers for `lem_app_pl_determinant_i` (fully proved) -/

private lemma vk_emaW_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (a : ℕ) : 0 < emaW β a := by
  unfold emaW
  exact mul_pos (by linarith) (pow_pos hβ0 a)

private lemma vk_emaW_add (β : ℝ) (j d : ℕ) : emaW β (j + d) = β ^ d * emaW β j := by
  unfold emaW
  rw [pow_add]
  ring

private lemma vk_w2_summable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Summable (fun a : ℕ => emaW β a ^ 2) := by
  have hr : β ^ 2 < 1 := pow_lt_one₀ hβ0.le hβ1 (by norm_num)
  have key : (fun j : ℕ => emaW β j ^ 2) = fun j => (1 - β) ^ 2 * (β ^ 2) ^ j := by
    funext j
    unfold emaW
    rw [mul_pow, pow_right_comm β j 2]
  rw [key]
  exact (summable_geometric_of_lt_one (by positivity) hr).mul_left _

private lemma vk_int_summ {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {f : ℕ → ℝ → ℝ} {c : ℝ}
    (hcont : ∀ a, Continuous (f a)) (h0 : ∀ a g, 0 ≤ f a g)
    (hle : ∀ a g, f a g ≤ c * (emaW β a ^ 2 * g ^ 2)) :
    (∀ a, Integrable (f a) (gaussianReal 0 1)) ∧
      Summable (fun a => ∫ g, f a g ∂(gaussianReal 0 1)) := by
  have hi2 := Muon.Foundations.gaussian_integrable_pow 2
  have hb : ∀ a, Integrable (fun g : ℝ => c * (emaW β a ^ 2 * g ^ 2)) (gaussianReal 0 1) :=
    fun a => (hi2.const_mul (emaW β a ^ 2)).const_mul c
  have hint : ∀ a, Integrable (f a) (gaussianReal 0 1) := fun a =>
    Integrable.mono' (hb a) (hcont a).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 a g)]
        exact hle a g)
  refine ⟨hint, ?_⟩
  refine Summable.of_nonneg_of_le (fun a => integral_nonneg (h0 a)) (fun a => ?_)
    ((vk_w2_summable hβ0 hβ1).mul_left c)
  calc ∫ g, f a g ∂(gaussianReal 0 1) ≤ ∫ g, c * (emaW β a ^ 2 * g ^ 2) ∂(gaussianReal 0 1) :=
        integral_mono (hint a) (hb a) (hle a)
    _ = c * emaW β a ^ 2 := by
        rw [integral_const_mul, integral_const_mul, Muon.Foundations.gaussian_moment_two, mul_one,
          mul_comm]

/-- Real Cauchy–Schwarz from the parametric AM-GM bound. -/
private lemma vk_cs {D SA SB : ℝ} (hD : 0 ≤ D) (hA : 0 ≤ SA) (hB : 0 ≤ SB)
    (h : ∀ t : ℝ, 0 < t → 2 * D ≤ t * SA + SB / t) : D ^ 2 ≤ SA * SB := by
  rcases hD.eq_or_lt with h0 | hpos
  · rw [← h0]; nlinarith [mul_nonneg hA hB]
  · rcases hA.eq_or_lt with hA0 | hApos
    · exfalso
      have := h ((SB + 1) / D) (by positivity)
      rw [← hA0, mul_zero, zero_add, div_div_eq_mul_div] at this
      have h2 : SB * D / (SB + 1) < D := by
        rw [div_lt_iff₀ (by linarith)]; nlinarith
      linarith
    · have := h (D / SA) (by positivity)
      have e : D / SA * SA + SB / (D / SA) = D + SB * SA / D := by
        field_simp
      rw [e] at this
      have : D ≤ SB * SA / D := by linarith
      rw [le_div_iff₀ hpos] at this
      nlinarith

/-- Pointwise algebra for the age-integrand. -/
private lemma vk_pw {X Y d t : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hd0 : 0 ≤ d) (hd : d ^ 2 = X * Y)
    (ht : 0 < t) :
    2 * (d / ((1 + X) * (1 + Y))) ≤
      t * (X / ((1 + X) * (1 + Y))) + (Y / ((1 + X) * (1 + Y))) / t := by
  have hden : 0 < (1 + X) * (1 + Y) := by positivity
  have hS : 0 ≤ t * X + Y / t := by positivity
  have hprod : (t * X) * (Y / t) = X * Y := by field_simp
  have key : 2 * d ≤ t * X + Y / t := by
    by_contra hc
    have hc := not_le.1 hc
    nlinarith [sq_nonneg (t * X - Y / t)]
  have e : t * (X / ((1 + X) * (1 + Y))) + (Y / ((1 + X) * (1 + Y))) / t =
      (t * X + Y / t) / ((1 + X) * (1 + Y)) := by
    field_simp
  rw [e, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right key hden.le

private lemma vk_weightSeq {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : WeightSeq (emaW β) := by
  refine ⟨fun j => (vk_emaW_pos hβ0 hβ1 j).le, ?_, ⟨0, (vk_emaW_pos hβ0 hβ1 0).ne'⟩⟩
  have key : emaW β = fun j => (1 - β) * β ^ j := by
    funext j; rfl
  rw [key]
  exact (summable_geometric_of_lt_one hβ0.le hβ1).mul_left _

private lemma vk_pw_split {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    X / ((1 + X) * (1 + Y)) + X * Y / ((1 + X) * (1 + Y)) = X / (1 + X) ∧
    Y / ((1 + X) * (1 + Y)) + X * Y / ((1 + X) * (1 + Y)) = Y / (1 + Y) := by
  have h1 : (1 + X) ≠ 0 := by positivity
  have h2 : (1 + Y) ≠ 0 := by positivity
  constructor <;> field_simp

private lemma vk_pw_bounds {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    X / ((1 + X) * (1 + Y)) ≤ X ∧ Y / ((1 + X) * (1 + Y)) ≤ Y ∧
    X * Y / ((1 + X) * (1 + Y)) ≤ X ∧ X / (1 + X) ≤ X ∧ Y / (1 + Y) ≤ Y := by
  have h1 : 1 ≤ 1 + X := by linarith
  have h2 : 1 ≤ 1 + Y := by linarith
  have h3 : 1 ≤ (1 + X) * (1 + Y) := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact div_le_self hX h3
  · exact div_le_self hY h3
  · rw [div_le_iff₀ (by linarith)]; nlinarith [mul_nonneg hX hY]
  · exact div_le_self hX h1
  · exact div_le_self hY h2

private lemma vk_main {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q1 q2 : ℝ} (hq1 : 0 ≤ q1)
    (hq2 : 0 ≤ q2) (ℓ : ℕ) :
    0 ≤ MLagNat β q1 q2 ℓ ∧ MLagNat β q1 q2 ℓ ≤ rW (emaW β) q1 ∧
      MLagNat β q1 q2 ℓ ≤ rW (emaW β) q2 ∧
      DLagNat β q1 q2 ℓ ^ 2 ≤
        (rW (emaW β) q1 - MLagNat β q1 q2 ℓ) * (rW (emaW β) q2 - MLagNat β q1 q2 ℓ) := by
  have hρ : 0 ≤ β ^ ℓ := pow_nonneg hβ0.le ℓ
  have hs0 : 0 ≤ β ^ (2 * ℓ) := pow_nonneg hβ0.le _
  have hs : (β ^ ℓ) ^ 2 = β ^ (2 * ℓ) := by rw [← pow_mul, mul_comm]
  have hrep := (lem_app_de_scalar_iii (vk_weightSeq hβ0 hβ1)).1
  obtain ⟨X, hX⟩ : ∃ X : ℕ → ℝ → ℝ, ∀ a g, X a g = q1 * emaW β a ^ 2 * g ^ 2 :=
    ⟨fun a g => q1 * emaW β a ^ 2 * g ^ 2, fun _ _ => rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ → ℝ → ℝ, ∀ a g, Y a g = β ^ (2 * ℓ) * q2 * emaW β a ^ 2 * g ^ 2 :=
    ⟨fun a g => β ^ (2 * ℓ) * q2 * emaW β a ^ 2 * g ^ 2, fun _ _ => rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℝ → ℝ,
      ∀ a g, d a g = β ^ ℓ * Real.sqrt (q1 * q2) * emaW β a ^ 2 * g ^ 2 :=
    ⟨fun a g => β ^ ℓ * Real.sqrt (q1 * q2) * emaW β a ^ 2 * g ^ 2, fun _ _ => rfl⟩
  have hX0 : ∀ a g, 0 ≤ X a g := fun a g => by rw [hX]; positivity
  have hY0 : ∀ a g, 0 ≤ Y a g := fun a g => by rw [hY]; positivity
  have hd0 : ∀ a g, 0 ≤ d a g := fun a g => by rw [hd]; positivity
  have hdd : ∀ a g, d a g ^ 2 = X a g * Y a g := by
    intro a g
    rw [hd, hX, hY]
    have := Real.sq_sqrt (mul_nonneg hq1 hq2)
    calc _ = (β ^ ℓ) ^ 2 * (Real.sqrt (q1 * q2)) ^ 2 * (emaW β a ^ 2 * g ^ 2) ^ 2 := by ring
      _ = _ := by rw [this, hs]; ring
  have hXc : ∀ a, Continuous (X a) := fun a => by
    have : X a = fun g => q1 * emaW β a ^ 2 * g ^ 2 := funext (hX a)
    rw [this]; fun_prop
  have hYc : ∀ a, Continuous (Y a) := fun a => by
    have : Y a = fun g => β ^ (2 * ℓ) * q2 * emaW β a ^ 2 * g ^ 2 := funext (hY a)
    rw [this]; fun_prop
  have hdc : ∀ a, Continuous (d a) := fun a => by
    have : d a = fun g => β ^ ℓ * Real.sqrt (q1 * q2) * emaW β a ^ 2 * g ^ 2 := funext (hd a)
    rw [this]; fun_prop
  have hden : ∀ a g, 0 < (1 + X a g) * (1 + Y a g) := fun a g => by
    have := hX0 a g; have := hY0 a g; positivity
  have hdenc : ∀ a, Continuous (fun g => (1 + X a g) * (1 + Y a g)) := fun a =>
    (continuous_const.add (hXc a)).mul (continuous_const.add (hYc a))
  have hXle : ∀ a g, X a g ≤ q1 * (emaW β a ^ 2 * g ^ 2) := fun a g => le_of_eq (by rw [hX]; ring)
  have hYle : ∀ a g, Y a g ≤ (β ^ (2 * ℓ) * q2) * (emaW β a ^ 2 * g ^ 2) :=
    fun a g => le_of_eq (by rw [hY]; ring)
  -- the five integrand families
  have hA := vk_int_summ hβ0 hβ1 (f := fun a g => X a g / ((1 + X a g) * (1 + Y a g))) (c := q1)
    (fun a => (hXc a).div (hdenc a) (fun g => (hden a g).ne'))
    (fun a g => div_nonneg (hX0 a g) (hden a g).le)
    (fun a g => ((vk_pw_bounds (hX0 a g) (hY0 a g)).1).trans (hXle a g))
  have hB := vk_int_summ hβ0 hβ1 (f := fun a g => Y a g / ((1 + X a g) * (1 + Y a g)))
    (c := β ^ (2 * ℓ) * q2)
    (fun a => (hYc a).div (hdenc a) (fun g => (hden a g).ne'))
    (fun a g => div_nonneg (hY0 a g) (hden a g).le)
    (fun a g => ((vk_pw_bounds (hX0 a g) (hY0 a g)).2.1).trans (hYle a g))
  have hM := vk_int_summ hβ0 hβ1 (f := fun a g => X a g * Y a g / ((1 + X a g) * (1 + Y a g)))
    (c := q1)
    (fun a => ((hXc a).mul (hYc a)).div (hdenc a) (fun g => (hden a g).ne'))
    (fun a g => div_nonneg (mul_nonneg (hX0 a g) (hY0 a g)) (hden a g).le)
    (fun a g => ((vk_pw_bounds (hX0 a g) (hY0 a g)).2.2.1).trans (hXle a g))
  have hDle : ∀ a g, d a g / ((1 + X a g) * (1 + Y a g)) ≤
      ((q1 + β ^ (2 * ℓ) * q2) / 2) * (emaW β a ^ 2 * g ^ 2) := by
    intro a g
    have h1 := vk_pw (hX0 a g) (hY0 a g) (hd0 a g) (hdd a g) one_pos
    have h2 := vk_pw_bounds (hX0 a g) (hY0 a g)
    have h3 := hXle a g
    have h4 := hYle a g
    rw [one_mul, div_one] at h1
    linarith [h2.1, h2.2.1]
  have hD := vk_int_summ hβ0 hβ1 (f := fun a g => d a g / ((1 + X a g) * (1 + Y a g)))
    (c := (q1 + β ^ (2 * ℓ) * q2) / 2)
    (fun a => (hdc a).div (hdenc a) (fun g => (hden a g).ne'))
    (fun a g => div_nonneg (hd0 a g) (hden a g).le) hDle
  have hYY := vk_int_summ hβ0 hβ1 (f := fun a g => Y a g / (1 + Y a g))
    (c := β ^ (2 * ℓ) * q2)
    (fun a => (hYc a).div (continuous_const.add (hYc a)) (fun g => by have := hY0 a g; positivity))
    (fun a g => div_nonneg (hY0 a g) (by have := hY0 a g; positivity))
    (fun a g => ((vk_pw_bounds (hX0 a g) (hY0 a g)).2.2.2.2).trans (hYle a g))
  have hR1 := vk_int_summ hβ0 hβ1
    (f := fun a g => emaW β a ^ 2 * q1 * g ^ 2 / (1 + emaW β a ^ 2 * q1 * g ^ 2)) (c := q1)
    (fun a => by
      refine Continuous.div (by fun_prop) (by fun_prop) (fun g => ?_)
      have : 0 ≤ emaW β a ^ 2 * q1 * g ^ 2 := by positivity
      linarith)
    (fun a g => by positivity)
    (fun a g => by
      have h0 : 0 ≤ emaW β a ^ 2 * q1 * g ^ 2 := by positivity
      refine (div_le_self h0 (by linarith)).trans (le_of_eq (by ring)))
  have hR2 := vk_int_summ hβ0 hβ1
    (f := fun a g => emaW β a ^ 2 * q2 * g ^ 2 / (1 + emaW β a ^ 2 * q2 * g ^ 2)) (c := q2)
    (fun a => by
      refine Continuous.div (by fun_prop) (by fun_prop) (fun g => ?_)
      have : 0 ≤ emaW β a ^ 2 * q2 * g ^ 2 := by positivity
      linarith)
    (fun a g => by positivity)
    (fun a g => by
      have h0 : 0 ≤ emaW β a ^ 2 * q2 * g ^ 2 := by positivity
      refine (div_le_self h0 (by linarith)).trans (le_of_eq (by ring)))
  have hMdef : MLagNat β q1 q2 ℓ =
      ∑' a, ∫ g, X a g * Y a g / ((1 + X a g) * (1 + Y a g)) ∂(gaussianReal 0 1) := by
    unfold MLagNat
    refine tsum_congr fun a => integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [hX, hY]
    ring
  have hDdef : DLagNat β q1 q2 ℓ =
      ∑' a, ∫ g, d a g / ((1 + X a g) * (1 + Y a g)) ∂(gaussianReal 0 1) := by
    unfold DLagNat
    simp only [hd, hX, hY]
  have hr1 := hrep q1 hq1
  have hr2 := hrep q2 hq2
  have e1 : ∀ a g, emaW β a ^ 2 * q1 * g ^ 2 / (1 + emaW β a ^ 2 * q1 * g ^ 2) =
      X a g / ((1 + X a g) * (1 + Y a g)) + X a g * Y a g / ((1 + X a g) * (1 + Y a g)) := by
    intro a g
    have : emaW β a ^ 2 * q1 * g ^ 2 = X a g := by rw [hX]; ring
    rw [this, (vk_pw_split (hX0 a g) (hY0 a g)).1]
  have e2 : ∀ a g, Y a g / (1 + Y a g) =
      Y a g / ((1 + X a g) * (1 + Y a g)) + X a g * Y a g / ((1 + X a g) * (1 + Y a g)) := by
    intro a g
    rw [(vk_pw_split (hX0 a g) (hY0 a g)).2]
  have hSA : rW (emaW β) q1 = (∑' a, ∫ g, X a g / ((1 + X a g) * (1 + Y a g)) ∂(gaussianReal 0 1)) +
      MLagNat β q1 q2 ℓ := by
    rw [hr1, hMdef, ← Summable.tsum_add hA.2 hM.2]
    refine tsum_congr fun a => ?_
    rw [← integral_add (hA.1 a) (hM.1 a)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun g => e1 a g)
  have hSB : (∑' a, ∫ g, Y a g / (1 + Y a g) ∂(gaussianReal 0 1)) =
      (∑' a, ∫ g, Y a g / ((1 + X a g) * (1 + Y a g)) ∂(gaussianReal 0 1)) +
      MLagNat β q1 q2 ℓ := by
    rw [hMdef, ← Summable.tsum_add hB.2 hM.2]
    refine tsum_congr fun a => ?_
    rw [← integral_add (hB.1 a) (hM.1 a)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun g => e2 a g)
  have hshift : (∑' a, ∫ g, Y a g / (1 + Y a g) ∂(gaussianReal 0 1)) ≤ rW (emaW β) q2 := by
    rw [hr2]
    have hc := tsum_comp_le_tsum_of_inj hR2.2
      (fun a => integral_nonneg fun g => by positivity) (i := fun a : ℕ => a + ℓ)
      (add_left_injective ℓ)
    refine le_trans (le_of_eq (tsum_congr fun a => ?_)) hc
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [vk_emaW_add]
    have : (β ^ ℓ * emaW β a) ^ 2 * q2 * g ^ 2 = Y a g := by rw [hY, ← hs]; ring
    rw [this]
  have hM0 : 0 ≤ MLagNat β q1 q2 ℓ := by
    rw [hMdef]
    exact tsum_nonneg fun a => integral_nonneg fun g =>
      div_nonneg (mul_nonneg (hX0 a g) (hY0 a g)) (hden a g).le
  have hSA0 : 0 ≤ ∑' a, ∫ g, X a g / ((1 + X a g) * (1 + Y a g)) ∂(gaussianReal 0 1) :=
    tsum_nonneg fun a => integral_nonneg fun g => div_nonneg (hX0 a g) (hden a g).le
  have hSB0 : 0 ≤ ∑' a, ∫ g, Y a g / ((1 + X a g) * (1 + Y a g)) ∂(gaussianReal 0 1) :=
    tsum_nonneg fun a => integral_nonneg fun g => div_nonneg (hY0 a g) (hden a g).le
  have hD0 : 0 ≤ DLagNat β q1 q2 ℓ := by
    rw [hDdef]
    exact tsum_nonneg fun a => integral_nonneg fun g => div_nonneg (hd0 a g) (hden a g).le
  have hDt : ∀ t : ℝ, 0 < t → 2 * DLagNat β q1 q2 ℓ ≤
      t * (∑' a, ∫ g, X a g / ((1 + X a g) * (1 + Y a g)) ∂(gaussianReal 0 1)) +
        (∑' a, ∫ g, Y a g / ((1 + X a g) * (1 + Y a g)) ∂(gaussianReal 0 1)) / t := by
    intro t ht
    rw [hDdef, ← tsum_mul_left, ← tsum_mul_left, ← tsum_div_const, ← Summable.tsum_add (hA.2.mul_left t) (hB.2.div_const t)]
    refine Summable.tsum_le_tsum (fun a => ?_) (hD.2.mul_left 2)
      ((hA.2.mul_left t).add (hB.2.div_const t))
    rw [← integral_const_mul, ← integral_const_mul, ← integral_div, ← integral_add]
    · refine integral_mono ((hD.1 a).const_mul 2) ?_ (fun g => ?_)
      · exact ((hA.1 a).const_mul t).add ((hB.1 a).div_const t)
      · exact vk_pw (hX0 a g) (hY0 a g) (hd0 a g) (hdd a g) ht
    · exact (hA.1 a).const_mul t
    · exact (hB.1 a).div_const t
  have hcs := vk_cs hD0 hSA0 hSB0 hDt
  refine ⟨hM0, by linarith, ?_, ?_⟩
  · linarith
  · rw [hSA]
    have : (∑' a, ∫ g, Y a g / ((1 + X a g) * (1 + Y a g)) ∂(gaussianReal 0 1)) ≤
        rW (emaW β) q2 - MLagNat β q1 q2 ℓ := by linarith
    calc DLagNat β q1 q2 ℓ ^ 2 ≤ _ := hcs
      _ ≤ _ := by
        rw [add_sub_cancel_right]
        exact mul_le_mul_of_nonneg_left this hSA0

private lemma vk_range {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    ∃ a ∈ Ioi (0:ℝ), rW (emaW β) a = m := by
  have hcont : ContinuousOn (rW (emaW β)) (Ici 0) :=
    continuousOn_id.mul (lem_app_de_scalar_ii (vk_weightSeq hβ0 hβ1)).2.2.1
  have hr0 := (lem_app_de_scalar_iii (vk_weightSeq hβ0 hβ1)).2.2.1
  have hT := (lem_app_de_scalar_iii (vk_weightSeq hβ0 hβ1)).2.2.2.2.2.2
  have hinf : {j : ℕ | 0 < emaW β j} = Set.univ := by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact vk_emaW_pos hβ0 hβ1 j
  have hTop : (Set.encard {j : ℕ | 0 < emaW β j}).toENNReal = ⊤ := by
    rw [hinf, Set.encard_univ, ENat.card_eq_top_of_infinite]
    rfl
  rw [hTop] at hT
  have hev : ∀ᶠ q in atTop, ENNReal.ofReal m < ENNReal.ofReal (rW (emaW β) q) :=
    hT.eventually (Ioi_mem_nhds ENNReal.ofReal_lt_top)
  obtain ⟨Q0, hQ0⟩ := (hev.and (eventually_ge_atTop (1:ℝ))).exists
  have hlt : ENNReal.ofReal m < ENNReal.ofReal (rW (emaW β) Q0) := hQ0.1
  have hmQ : m < rW (emaW β) Q0 := (ENNReal.ofReal_lt_ofReal_iff'.1 hlt).1
  have hmem : m ∈ Icc (rW (emaW β) 0) (rW (emaW β) Q0) :=
    ⟨by rw [hr0]; exact hm.le, hmQ.le⟩
  obtain ⟨q, hq, hqe⟩ := intermediate_value_Icc (by linarith [hQ0.2] : (0:ℝ) ≤ Q0)
    (hcont.mono Icc_subset_Ici_self) hmem
  have hqpos : 0 < q := by
    rcases hq.1.eq_or_lt with h | h
    · rw [← h, hr0] at hqe
      linarith
    · exact h
  exact ⟨q, hqpos, hqe⟩

private lemma vk_Qm {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    0 < Qm β m ∧ rW (emaW β) (Qm β m) = m := by
  have hex : ∃ a ∈ Ioi (0:ℝ), rW (emaW β) a = m := vk_range hβ0 hβ1 hm
  exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩

private lemma vk_main_int {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q1 q2 : ℝ} (hq1 : 0 ≤ q1)
    (hq2 : 0 ≤ q2) (ℓ : ℤ) :
    0 ≤ MLag β q1 q2 ℓ ∧ MLag β q1 q2 ℓ ≤ rW (emaW β) q1 ∧ MLag β q1 q2 ℓ ≤ rW (emaW β) q2 ∧
      DLag β q1 q2 ℓ ^ 2 ≤
        (rW (emaW β) q1 - MLag β q1 q2 ℓ) * (rW (emaW β) q2 - MLag β q1 q2 ℓ) := by
  unfold MLag DLag
  split_ifs
  · exact vk_main hβ0 hβ1 hq1 hq2 _
  · obtain ⟨h1, h2, h3, h4⟩ := vk_main hβ0 hβ1 hq2 hq1 (-ℓ).toNat
    exact ⟨h1, h3, h2, by rw [mul_comm]; exact h4⟩

/-- `lem:app-pl-determinant`, scalar part (i) in terms of `m_j = r_β(q_j)`. -/
private lemma vk_det_i {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m₁ m₂ : ℝ} (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) (ℓ : ℤ) :
    0 ≤ MLag β (Qm β m₁) (Qm β m₂) ℓ ∧
      MLag β (Qm β m₁) (Qm β m₂) ℓ ≤ min m₁ m₂ ∧
        DLag β (Qm β m₁) (Qm β m₂) ℓ ^ 2 ≤
          (m₁ - MLag β (Qm β m₁) (Qm β m₂) ℓ) * (m₂ - MLag β (Qm β m₁) (Qm β m₂) ℓ) := by
  obtain ⟨h1, e1⟩ := vk_Qm hβ0 hβ1 hm₁
  obtain ⟨h2, e2⟩ := vk_Qm hβ0 hβ1 hm₂
  obtain ⟨a, b, c, d⟩ := vk_main_int hβ0 hβ1 h1.le h2.le ℓ
  rw [e1] at b d
  rw [e2] at c d
  exact ⟨a, le_min b c, d⟩

/-- `lem:app-pl-determinant`, part (i) (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Determinant]\label{lem:app-pl-determinant}
For every lag and all $m_1,m_2\in(0,\gamma)$,
\[
0\le\mathsf M_\ell\le m_-,\qquad \mathsf D_\ell^2\le(m_1-\mathsf M_\ell)(m_2-\mathsf M_\ell),\]
\[
\Delta^N_\ell\ge\Big(1-\frac{m_-}\gamma\Big)\Big(1-\frac{\mathsf T_N}{m_+}\Big)\ge c_\alpha\Big(1-\frac{m_1}\gamma\Big)\Big(1-\frac{m_2}\gamma\Big),
\]
and $0\le1-\Delta^N_\ell\le m_-\/m_++2m_-\/\gamma$. If $m_1,m_2\le\delta\le1$, then
$1-\Delta^N_\ell\le C_\bmom\delta+2\delta/\gamma$.
\end{lemma}
-/
theorem lem_app_pl_determinant_i {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → ∀ (ℓ : ℤ) (m₁ m₂ : ℝ),
      m₁ ∈ Ioo 0 (gammaOf N B) → m₂ ∈ Ioo 0 (gammaOf N B) →
        0 ≤ MLag β (Qm β m₁) (Qm β m₂) ℓ ∧
          MLag β (Qm β m₁) (Qm β m₂) ℓ ≤ min m₁ m₂ ∧
          DLag β (Qm β m₁) (Qm β m₂) ℓ ^ 2 ≤
            (m₁ - MLag β (Qm β m₁) (Qm β m₂) ℓ) * (m₂ - MLag β (Qm β m₁) (Qm β m₂) ℓ) := by
  intro N B c hN hB hc ℓ m₁ m₂ hm₁ hm₂
  exact vk_det_i hβ0 hβ1 hm₁.1 hm₂.1 ℓ

private lemma vk_TN_comm {N B : ℕ} (μ : Fin N → ℝ) (m₁ m₂ : ℝ) :
    TNpart B μ m₁ m₂ = TNpart B μ m₂ m₁ := by
  unfold TNpart
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma vk_partF_mono {N B : ℕ} {μ : Fin N → ℝ} (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (j : Fin N) {m₁ m₂ : ℝ} (hm₁ : m₁ ∈ Ioo 0 (gammaOf N B))
    (hm₂ : m₂ ∈ Ioo 0 (gammaOf N B)) (h12 : m₁ ≤ m₂) :
    partF B μ j m₁ ≤ partF B μ j m₂ := by
  unfold partF
  exact vk_sat_mono (vk_partLam_pos hB hN hpos hm₁).le
    ((def_app_pl_participation_bij μ hB hN hpos).2.2.1.monotoneOn hm₁ hm₂ h12) (hpos j).le

private lemma vk_partF_nonneg {N B : ℕ} {μ : Fin N → ℝ} (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (j : Fin N) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    0 ≤ partF B μ j m := by
  unfold partF
  exact vk_sat_nonneg (vk_partLam_pos hB hN hpos hm).le (hpos j).le

private lemma vk_TN_mono {N B : ℕ} {μ : Fin N → ℝ} (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) {m₁ m₂ : ℝ} (hm₁ : m₁ ∈ Ioo 0 (gammaOf N B))
    (hm₂ : m₂ ∈ Ioo 0 (gammaOf N B)) (h12 : m₁ ≤ m₂) :
    TNpart B μ m₁ m₂ ≤ TNpart B μ m₂ m₂ := by
  unfold TNpart
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (Nat.cast_nonneg B))
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (vk_partF_mono hB hN hpos j hm₁ hm₂ h12)
    (vk_partF_nonneg hB hN hpos j hm₂)

private lemma vk_chain_le {N B : ℕ} {μ : Fin N → ℝ} (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) {cα : ℝ}
    (hel : ∀ Λ : ℝ, 0 < Λ → cα * partMN B μ Λ * (1 - partMN B μ Λ / gammaOf N B) ≤
      Λ * deriv (partMN B μ) Λ) {m₁ m₂ : ℝ} (hm₁ : m₁ ∈ Ioo 0 (gammaOf N B))
    (hm₂ : m₂ ∈ Ioo 0 (gammaOf N B)) (h12 : m₁ ≤ m₂) :
    cα * ((1 - m₁ / gammaOf N B) * (1 - m₂ / gammaOf N B)) ≤
      (1 - m₁ / gammaOf N B) * (1 - TNpart B μ m₁ m₂ / m₂) := by
  have hm₂pos : 0 < m₂ := hm₂.1
  have hγ : 0 < gammaOf N B := lt_trans hm₂.1 hm₂.2
  have hdiag : TNpart B μ m₂ m₂ ≤ m₂ - cα * m₂ * (1 - m₂ / gammaOf N B) := by
    have h1 := hel (partLam B μ m₂) (vk_partLam_pos hB hN hpos hm₂)
    rw [vk_partMN_partLam hB hN hpos hm₂] at h1
    rw [vk_TN_diag hB hN hpos hm₂]
    linarith
  have hratio : TNpart B μ m₁ m₂ / m₂ ≤ 1 - cα * (1 - m₂ / gammaOf N B) := by
    rw [div_le_iff₀ hm₂pos]
    have hmono := vk_TN_mono hB hN hpos hm₁ hm₂ h12
    have e : (1 - cα * (1 - m₂ / gammaOf N B)) * m₂ = m₂ - cα * m₂ * (1 - m₂ / gammaOf N B) := by
      ring
    rw [e]
    linarith
  have hm₁le : m₁ / gammaOf N B ≤ 1 := by
    rw [div_le_one hγ]
    linarith [hm₁.1, hm₁.2, hm₂.2, h12]
  have h1m : 0 ≤ 1 - m₁ / gammaOf N B := by linarith
  calc cα * ((1 - m₁ / gammaOf N B) * (1 - m₂ / gammaOf N B))
      = (1 - m₁ / gammaOf N B) * (cα * (1 - m₂ / gammaOf N B)) := by ring
    _ ≤ (1 - m₁ / gammaOf N B) * (1 - TNpart B μ m₁ m₂ / m₂) :=
        mul_le_mul_of_nonneg_left (by linarith) h1m

/-- `lem:app-pl-determinant`, the β-free chain of part (ii) (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Determinant]\label{lem:app-pl-determinant}
For every lag and all $m_1,m_2\in(0,\gamma)$,
\[
0\le\mathsf M_\ell\le m_-,\qquad \mathsf D_\ell^2\le(m_1-\mathsf M_\ell)(m_2-\mathsf M_\ell),\]
\[
\Delta^N_\ell\ge\Big(1-\frac{m_-}\gamma\Big)\Big(1-\frac{\mathsf T_N}{m_+}\Big)\ge c_\alpha\Big(1-\frac{m_1}\gamma\Big)\Big(1-\frac{m_2}\gamma\Big),
\]
and $0\le1-\Delta^N_\ell\le m_-\/m_++2m_-\/\gamma$. If $m_1,m_2\le\delta\le1$, then
$1-\Delta^N_\ell\le C_\bmom\delta+2\delta/\gamma$.
\end{lemma}
-/
theorem lem_app_pl_determinant_ii_chain {α : ℝ} (hα : 0 < α) :
    ∃ cα : ℝ, 0 < cα ∧
      ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → ∀ m₁ m₂ : ℝ,
        m₁ ∈ Ioo 0 (gammaOf N B) → m₂ ∈ Ioo 0 (gammaOf N B) →
          cα * ((1 - m₁ / gammaOf N B) * (1 - m₂ / gammaOf N B)) ≤
            (1 - min m₁ m₂ / gammaOf N B) *
              (1 - TNpart B (plSpec α c N) m₁ m₂ / max m₁ m₂) := by
  obtain ⟨cα, hc, hel⟩ := lem_app_pl_elasticity_i hα
  refine ⟨cα, hc, fun N B c hN hB hc0 m₁ m₂ hm₁ hm₂ => ?_⟩
  have hpos : ∀ i : Fin N, 0 < plSpec α c N i := vk_pos_plSpec hc0 N
  have hel' : ∀ Λ : ℝ, 0 < Λ → cα * partMN B (plSpec α c N) Λ *
      (1 - partMN B (plSpec α c N) Λ / gammaOf N B) ≤
        Λ * deriv (partMN B (plSpec α c N)) Λ :=
    fun Λ hΛ => ((hel N B c hN hB hc0).1 Λ hΛ).1
  rcases le_total m₁ m₂ with h | h
  · rw [min_eq_left h, max_eq_right h]
    exact vk_chain_le hB hN hpos hel' hm₁ hm₂ h
  · rw [min_eq_right h, max_eq_left h, vk_TN_comm (B := B) (μ := plSpec α c N) m₁ m₂]
    have := vk_chain_le hB hN hpos hel' hm₂ hm₁ h
    have e : cα * ((1 - m₁ / gammaOf N B) * (1 - m₂ / gammaOf N B)) =
        cα * ((1 - m₂ / gammaOf N B) * (1 - m₁ / gammaOf N B)) := by ring
    rw [e]
    exact this


private lemma vk_alg {T M D2 m1 m2 γ : ℝ} (h1 : 0 < m1) (h12 : m1 ≤ m2) (h2γ : m2 < γ)
    (hT0 : 0 ≤ T) (hT1 : T ≤ m1) (hM0 : 0 ≤ M) (hM1 : M ≤ m1)
    (hD : D2 ≤ (m1 - M) * (m2 - M)) :
    (1 - m1 / γ) * (1 - T / m2) ≤
      (1 - T * M / (m1 * m2)) * (1 - M / γ) - T * D2 / (γ * m1 * m2) := by
  have hm2 : 0 < m2 := lt_of_lt_of_le h1 h12
  have hγ : 0 < γ := lt_trans hm2 h2γ
  have hc : 0 ≤ m1 * m2 + T * (γ - m1 - m2) := by
    rcases le_total (m1 + m2) γ with h | h
    · nlinarith [mul_nonneg hT0 (sub_nonneg.2 h), mul_pos h1 hm2]
    · nlinarith [mul_nonneg (sub_nonneg.2 hT1) (sub_nonneg.2 h),
        mul_nonneg h1.le (sub_nonneg.2 (h12.trans h2γ.le))]
  have hid : (1 - T * M / (m1 * m2)) * (1 - M / γ) - T * D2 / (γ * m1 * m2) -
      (1 - m1 / γ) * (1 - T / m2) =
      T * ((m1 - M) * (m2 - M) - D2) / (γ * (m1 * m2)) +
        (m1 * m2 + T * (γ - m1 - m2)) / (γ * (m1 * m2)) * (m1 - M) := by
    field_simp
    ring
  have hnn : 0 ≤ T * ((m1 - M) * (m2 - M) - D2) / (γ * (m1 * m2)) +
        (m1 * m2 + T * (γ - m1 - m2)) / (γ * (m1 * m2)) * (m1 - M) := by
    have a1 : 0 ≤ T * ((m1 - M) * (m2 - M) - D2) / (γ * (m1 * m2)) :=
      div_nonneg (mul_nonneg hT0 (sub_nonneg.2 hD)) (by positivity)
    have a2 : 0 ≤ (m1 * m2 + T * (γ - m1 - m2)) / (γ * (m1 * m2)) * (m1 - M) :=
      mul_nonneg (div_nonneg hc (by positivity)) (sub_nonneg.2 hM1)
    linarith
  linarith

private lemma vk_T_bd {N B : ℕ} {μ : Fin N → ℝ} (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) {m₁ m₂ : ℝ} (hm₁ : m₁ ∈ Ioo 0 (gammaOf N B))
    (hm₂ : m₂ ∈ Ioo 0 (gammaOf N B)) (h12 : m₁ ≤ m₂) :
    0 ≤ TNpart B μ m₁ m₂ ∧ TNpart B μ m₁ m₂ ≤ m₁ := by
  have hsum : (B : ℝ)⁻¹ * ∑ j : Fin N, partF B μ j m₁ = m₁ := by
    have := vk_partMN_partLam hB hN hpos hm₁
    unfold partMN at this
    unfold partF
    exact this
  refine ⟨?_, ?_⟩
  · unfold TNpart
    exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg B))
      (Finset.sum_nonneg fun j _ => mul_nonneg (vk_partF_nonneg hB hN hpos j hm₁)
        (vk_partF_nonneg hB hN hpos j hm₂))
  · refine le_trans ?_ hsum.le
    unfold TNpart
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (Nat.cast_nonneg B))
    apply Finset.sum_le_sum
    intro j _
    have h1 : partF B μ j m₂ ≤ 1 := by
      unfold partF
      exact vk_sat_le_one (vk_partLam_pos hB hN hpos hm₂).le (hpos j).le
    calc partF B μ j m₁ * partF B μ j m₂ ≤ partF B μ j m₁ * 1 :=
          mul_le_mul_of_nonneg_left h1 (vk_partF_nonneg hB hN hpos j hm₁)
      _ = partF B μ j m₁ := mul_one _

private lemma vk_alg3 {T M D2 m1 m2 γ : ℝ} (h1 : 0 < m1) (h12 : m1 ≤ m2) (h2γ : m2 < γ)
    (hT0 : 0 ≤ T) (hT1 : T ≤ m1) (hM0 : 0 ≤ M) (hM1 : M ≤ m1) (hD0 : 0 ≤ D2)
    (hD : D2 ≤ (m1 - M) * (m2 - M)) :
    0 ≤ 1 - ((1 - T * M / (m1 * m2)) * (1 - M / γ) - T * D2 / (γ * m1 * m2)) ∧
      1 - ((1 - T * M / (m1 * m2)) * (1 - M / γ) - T * D2 / (γ * m1 * m2)) ≤
        m1 / m2 + 2 * m1 / γ := by
  have hm2 : 0 < m2 := lt_of_lt_of_le h1 h12
  have hγ : 0 < γ := lt_trans hm2 h2γ
  have ha0 : 0 ≤ T * M / (m1 * m2) := by positivity
  have ha1 : T * M / (m1 * m2) ≤ m1 / m2 := by
    rw [div_le_div_iff₀ (by positivity) hm2]
    nlinarith [mul_le_mul hT1 hM1 hM0 h1.le, mul_pos h1 hm2]
  have hr1 : m1 / m2 ≤ 1 := by rw [div_le_one hm2]; exact h12
  have hg0 : 0 ≤ M / γ := by positivity
  have hg1 : M / γ ≤ m1 / γ := div_le_div_of_nonneg_right hM1 hγ.le
  have hr2 : m1 / γ ≤ 1 := by rw [div_le_one hγ]; linarith
  have hDle : D2 ≤ m1 * m2 := by
    have : (m1 - M) * (m2 - M) ≤ m1 * m2 := by nlinarith
    linarith
  have hX0 : 0 ≤ T * D2 / (γ * m1 * m2) := by positivity
  have hX1 : T * D2 / (γ * m1 * m2) ≤ m1 / γ := by
    rw [div_le_div_iff₀ (by positivity) hγ]
    nlinarith [mul_le_mul hT1 hDle hD0 h1.le, mul_pos h1 hm2]
  have hid : 1 - ((1 - T * M / (m1 * m2)) * (1 - M / γ) - T * D2 / (γ * m1 * m2)) =
      T * M / (m1 * m2) + M / γ - (T * M / (m1 * m2)) * (M / γ) + T * D2 / (γ * m1 * m2) := by
    ring
  rw [hid]
  have hag : 0 ≤ (T * M / (m1 * m2)) * (M / γ) := mul_nonneg ha0 hg0
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 (ha1.trans hr1)) (sub_nonneg.2 (hg1.trans hr2))]
  · have : 2 * m1 / γ = m1 / γ + m1 / γ := by ring
    linarith

/-- `lem:app-pl-determinant`, part (ii) (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Determinant]\label{lem:app-pl-determinant}
For every lag and all $m_1,m_2\in(0,\gamma)$,
\[
0\le\mathsf M_\ell\le m_-,\qquad \mathsf D_\ell^2\le(m_1-\mathsf M_\ell)(m_2-\mathsf M_\ell),\]
\[
\Delta^N_\ell\ge\Big(1-\frac{m_-}\gamma\Big)\Big(1-\frac{\mathsf T_N}{m_+}\Big)\ge c_\alpha\Big(1-\frac{m_1}\gamma\Big)\Big(1-\frac{m_2}\gamma\Big),
\]
and $0\le1-\Delta^N_\ell\le m_-\/m_++2m_-\/\gamma$. If $m_1,m_2\le\delta\le1$, then
$1-\Delta^N_\ell\le C_\bmom\delta+2\delta/\gamma$.
\end{lemma}
-/
theorem lem_app_pl_determinant_ii {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → ∀ (ℓ : ℤ) (m₁ m₂ : ℝ),
      m₁ ∈ Ioo 0 (gammaOf N B) → m₂ ∈ Ioo 0 (gammaOf N B) →
        (1 - min m₁ m₂ / gammaOf N B) *
            (1 - TNpart B (plSpec α c N) m₁ m₂ / max m₁ m₂) ≤
          deltaN β B (plSpec α c N) ℓ m₁ m₂ := by
  intro N B c hN hB hc ℓ m₁ m₂ hm₁ hm₂
  have hpos := vk_pos_plSpec (α := α) hc N
  obtain ⟨hM0, hMmin, hD⟩ := vk_det_i hβ0 hβ1 hm₁.1 hm₂.1 ℓ
  unfold deltaN
  generalize MLag β (Qm β m₁) (Qm β m₂) ℓ = M at hM0 hMmin hD ⊢
  generalize DLag β (Qm β m₁) (Qm β m₂) ℓ = D at hD ⊢
  rcases le_total m₁ m₂ with h | h
  · rw [min_eq_left h, max_eq_right h]
    obtain ⟨hT0, hT1⟩ := vk_T_bd hB hN hpos hm₁ hm₂ h
    exact vk_alg hm₁.1 h hm₂.2 hT0 hT1 hM0 (hMmin.trans (min_le_left _ _)) hD
  · rw [min_eq_right h, max_eq_left h]
    obtain ⟨hT0, hT1⟩ := vk_T_bd hB hN hpos hm₂ hm₁ h
    rw [vk_TN_comm] at hT0 hT1
    have := vk_alg (D2 := D ^ 2) hm₂.1 h hm₁.2 hT0 hT1 hM0 (hMmin.trans (min_le_right _ _))
      (by linarith [hD, mul_comm (m₁ - M) (m₂ - M)])
    exact this.trans (le_of_eq (by ring))

/-- `lem:app-pl-determinant`, part (iii) (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex` (the slash after a minus sign in the display is written with the LaTeX italic correction `\/`, same rendering):

\begin{lemma}[Determinant]\label{lem:app-pl-determinant}
For every lag and all $m_1,m_2\in(0,\gamma)$,
\[
0\le\mathsf M_\ell\le m_-,\qquad \mathsf D_\ell^2\le(m_1-\mathsf M_\ell)(m_2-\mathsf M_\ell),\]
\[
\Delta^N_\ell\ge\Big(1-\frac{m_-}\gamma\Big)\Big(1-\frac{\mathsf T_N}{m_+}\Big)\ge c_\alpha\Big(1-\frac{m_1}\gamma\Big)\Big(1-\frac{m_2}\gamma\Big),
\]
and $0\le1-\Delta^N_\ell\le m_-\/m_++2m_-\/\gamma$. If $m_1,m_2\le\delta\le1$, then
$1-\Delta^N_\ell\le C_\bmom\delta+2\delta/\gamma$.
\end{lemma}
-/
theorem lem_app_pl_determinant_iii {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → ∀ (ℓ : ℤ) (m₁ m₂ : ℝ),
      m₁ ∈ Ioo 0 (gammaOf N B) → m₂ ∈ Ioo 0 (gammaOf N B) →
        0 ≤ 1 - deltaN β B (plSpec α c N) ℓ m₁ m₂ ∧
          1 - deltaN β B (plSpec α c N) ℓ m₁ m₂ ≤
            min m₁ m₂ / max m₁ m₂ + 2 * min m₁ m₂ / gammaOf N B := by
  intro N B c hN hB hc ℓ m₁ m₂ hm₁ hm₂
  have hpos := vk_pos_plSpec (α := α) hc N
  obtain ⟨hM0, hMmin, hD⟩ := vk_det_i hβ0 hβ1 hm₁.1 hm₂.1 ℓ
  unfold deltaN
  generalize MLag β (Qm β m₁) (Qm β m₂) ℓ = M at hM0 hMmin hD ⊢
  generalize DLag β (Qm β m₁) (Qm β m₂) ℓ = D at hD ⊢
  rcases le_total m₁ m₂ with h | h
  · rw [min_eq_left h, max_eq_right h]
    obtain ⟨hT0, hT1⟩ := vk_T_bd hB hN hpos hm₁ hm₂ h
    exact vk_alg3 (D2 := D ^ 2) hm₁.1 h hm₂.2 hT0 hT1 hM0 (hMmin.trans (min_le_left _ _))
      (sq_nonneg D) hD
  · rw [min_eq_right h, max_eq_left h]
    obtain ⟨hT0, hT1⟩ := vk_T_bd hB hN hpos hm₂ hm₁ h
    rw [vk_TN_comm] at hT0 hT1
    have := vk_alg3 (D2 := D ^ 2) hm₂.1 h hm₁.2 hT0 hT1 hM0
      (hMmin.trans (min_le_right _ _)) (sq_nonneg D)
      (by linarith [hD, mul_comm (m₁ - M) (m₂ - M)])
    have e : (1 - TNpart B (plSpec α c N) m₁ m₂ * M / (m₂ * m₁)) * (1 - M / gammaOf N B) -
        TNpart B (plSpec α c N) m₁ m₂ * D ^ 2 / (gammaOf N B * m₂ * m₁) =
        (1 - TNpart B (plSpec α c N) m₁ m₂ * M / (m₁ * m₂)) * (1 - M / gammaOf N B) -
        TNpart B (plSpec α c N) m₁ m₂ * D ^ 2 / (gammaOf N B * m₁ * m₂) := by ring
    rw [e] at this
    exact this


private lemma vk_Fw_anti {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q q' : ℝ} (hq : 0 ≤ q)
    (hqq : q ≤ q') : Fw (emaW β) q' ≤ Fw (emaW β) q := by
  have hJ := lem_app_de_scalar_i
  have hsum : ∀ x : ℝ, 0 ≤ x → Summable (fun j : ℕ => emaW β j ^ 2 * J (emaW β j ^ 2 * x)) := by
    intro x hx
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) (vk_w2_summable hβ0 hβ1)
    · exact mul_nonneg (sq_nonneg _) (hJ.2.2.1 _ (mul_nonneg (sq_nonneg _) hx)).1.le
    · exact mul_le_of_le_one_right (sq_nonneg _) (hJ.2.2.1 _ (mul_nonneg (sq_nonneg _) hx)).2
  unfold Fw
  refine Summable.tsum_le_tsum (fun j => ?_) (hsum q' (hq.trans hqq)) (hsum q hq)
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  exact hJ.2.1.antitoneOn (Set.mem_Ici.2 (mul_nonneg (sq_nonneg _) hq))
    (Set.mem_Ici.2 (mul_nonneg (sq_nonneg _) (hq.trans hqq)))
    (mul_le_mul_of_nonneg_left hqq (sq_nonneg _))

private lemma vk_Qm_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) :
    Qm β m ≤ Qm β 1 * m := by
  obtain ⟨hQ, hr⟩ := vk_Qm hβ0 hβ1 hm
  obtain ⟨hQ1, hr1⟩ := vk_Qm hβ0 hβ1 (zero_lt_one : (0:ℝ) < 1)
  have hmono := (lem_app_de_scalar_iii (vk_weightSeq hβ0 hβ1)).2.1
  have hle : Qm β m ≤ Qm β 1 := by
    by_contra h
    have h := not_le.1 h
    have := hmono (Set.mem_Ici.2 hQ1.le) (Set.mem_Ici.2 hQ.le) h
    rw [hr, hr1] at this
    linarith
  have hF := vk_Fw_anti hβ0 hβ1 hQ.le hle
  have e1 : Qm β m * Fw (emaW β) (Qm β m) = m := hr
  have e2 : Qm β 1 * Fw (emaW β) (Qm β 1) = 1 := hr1
  -- m = Q F(Q) ≥ Q F(Q1) ; Q1 F(Q1) = 1
  have : Qm β m * Fw (emaW β) (Qm β 1) ≤ m := by
    have := mul_le_mul_of_nonneg_left hF hQ.le
    linarith
  have h2 : Qm β m * (Qm β 1 * Fw (emaW β) (Qm β 1)) ≤ Qm β 1 * m := by
    nlinarith
  rw [e2] at h2
  linarith

private lemma vk_M_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q1 q2 : ℝ} (hq1 : 0 ≤ q1)
    (hq2 : 0 ≤ q2) (ℓ : ℕ) :
    MLagNat β q1 q2 ℓ ≤ (3 * sPow β 4) * (q1 * q2) := by
  have hi4 := Muon.Foundations.gaussian_integrable_pow 4
  have hw4 : Summable (fun a : ℕ => emaW β a ^ 4) := by
    refine Summable.of_nonneg_of_le (fun a => by positivity) (fun a => ?_) (vk_w2_summable hβ0 hβ1)
    have h1 : emaW β a ≤ 1 := by
      unfold emaW
      have : β ^ a ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
      nlinarith [pow_nonneg hβ0.le a]
    have h0 := (vk_emaW_pos hβ0 hβ1 a).le
    have : emaW β a ^ 2 ≤ 1 := pow_le_one₀ h0 h1
    nlinarith [sq_nonneg (emaW β a)]
  have hs1 : β ^ (2 * ℓ) ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
  have hs0 : 0 ≤ β ^ (2 * ℓ) := pow_nonneg hβ0.le _
  have hterm : ∀ a, (∫ g : ℝ, β ^ (2 * ℓ) * q1 * q2 * emaW β a ^ 4 * g ^ 4 /
      ((1 + q1 * emaW β a ^ 2 * g ^ 2) * (1 + β ^ (2 * ℓ) * q2 * emaW β a ^ 2 * g ^ 2))
      ∂(gaussianReal 0 1)) ≤ 3 * (q1 * q2) * emaW β a ^ 4 := by
    intro a
    have hP : ∀ g : ℝ, 0 ≤ q1 * q2 * emaW β a ^ 4 * g ^ 4 := fun g => by positivity
    have : (∫ g : ℝ, q1 * q2 * emaW β a ^ 4 * g ^ 4 ∂(gaussianReal 0 1)) =
        3 * (q1 * q2) * emaW β a ^ 4 := by
      rw [integral_const_mul, Muon.Foundations.gaussian_moment_four]; ring
    rw [← this]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun g => ?_)
      (hi4.const_mul (q1 * q2 * emaW β a ^ 4)) (Filter.Eventually.of_forall fun g => ?_)
    · have := hq1; have := hq2
      positivity
    · have hden : 1 ≤ (1 + q1 * emaW β a ^ 2 * g ^ 2) *
          (1 + β ^ (2 * ℓ) * q2 * emaW β a ^ 2 * g ^ 2) := by
        have h1 : 0 ≤ q1 * emaW β a ^ 2 * g ^ 2 := by positivity
        have h2 : 0 ≤ β ^ (2 * ℓ) * q2 * emaW β a ^ 2 * g ^ 2 := by positivity
        nlinarith [mul_nonneg h1 h2]
      have hnum : β ^ (2 * ℓ) * q1 * q2 * emaW β a ^ 4 * g ^ 4 ≤
          q1 * q2 * emaW β a ^ 4 * g ^ 4 := by
        have := mul_le_mul_of_nonneg_right hs1 (hP g)
        nlinarith
      have hn0 : 0 ≤ β ^ (2 * ℓ) * q1 * q2 * emaW β a ^ 4 * g ^ 4 := by
        have := hq1; have := hq2; positivity
      exact (div_le_self hn0 hden).trans hnum
  unfold MLagNat
  have hnn : ∀ a, 0 ≤ ∫ g : ℝ, β ^ (2 * ℓ) * q1 * q2 * emaW β a ^ 4 * g ^ 4 /
      ((1 + q1 * emaW β a ^ 2 * g ^ 2) * (1 + β ^ (2 * ℓ) * q2 * emaW β a ^ 2 * g ^ 2))
      ∂(gaussianReal 0 1) := fun a => integral_nonneg fun g => by
    have := hq1; have := hq2; positivity
  calc _ ≤ ∑' a : ℕ, 3 * (q1 * q2) * emaW β a ^ 4 :=
        Summable.tsum_le_tsum hterm
          (Summable.of_nonneg_of_le hnn hterm (hw4.mul_left _)) (hw4.mul_left _)
    _ = (3 * sPow β 4) * (q1 * q2) := by
        rw [tsum_mul_left]; unfold sPow; ring

private lemma vk_M_le_int {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q1 q2 : ℝ} (hq1 : 0 ≤ q1)
    (hq2 : 0 ≤ q2) (ℓ : ℤ) :
    MLag β q1 q2 ℓ ≤ (3 * sPow β 4) * (q1 * q2) := by
  unfold MLag
  split_ifs
  · exact vk_M_le hβ0 hβ1 hq1 hq2 _
  · have := vk_M_le hβ0 hβ1 hq2 hq1 (-ℓ).toNat
    rwa [mul_comm q2 q1] at this

private lemma vk_alg4 {T M D2 m1 m2 γ K δ : ℝ} (h1 : 0 < m1) (h12 : m1 ≤ m2) (h2γ : m2 < γ)
    (hT0 : 0 ≤ T) (hT1 : T ≤ m1) (hM0 : 0 ≤ M) (hM1 : M ≤ m1) (hD0 : 0 ≤ D2)
    (hD : D2 ≤ (m1 - M) * (m2 - M)) (hK : 0 ≤ K) (hMK : M ≤ K * (m1 * m2)) (hδ : m1 ≤ δ) :
    1 - ((1 - T * M / (m1 * m2)) * (1 - M / γ) - T * D2 / (γ * m1 * m2)) ≤
      K * δ + 2 * δ / γ := by
  have hm2 : 0 < m2 := lt_of_lt_of_le h1 h12
  have hγ : 0 < γ := lt_trans hm2 h2γ
  have ha0 : 0 ≤ T * M / (m1 * m2) := by positivity
  have ha1 : T * M / (m1 * m2) ≤ K * δ := by
    rw [div_le_iff₀ (by positivity)]
    have h3 : T * M ≤ T * (K * (m1 * m2)) := mul_le_mul_of_nonneg_left hMK hT0
    have h4 : T * K ≤ δ * K := mul_le_mul_of_nonneg_right (hT1.trans hδ) hK
    nlinarith [mul_pos h1 hm2]
  have hg0 : 0 ≤ M / γ := by positivity
  have hg1 : M / γ ≤ δ / γ := div_le_div_of_nonneg_right (hM1.trans hδ) hγ.le
  have hDle : D2 ≤ m1 * m2 := by
    have : (m1 - M) * (m2 - M) ≤ m1 * m2 := by nlinarith
    linarith
  have hX0 : 0 ≤ T * D2 / (γ * m1 * m2) := by positivity
  have hX1 : T * D2 / (γ * m1 * m2) ≤ δ / γ := by
    rw [div_le_div_iff₀ (by positivity) hγ]
    nlinarith [mul_le_mul hT1 hDle hD0 h1.le, mul_pos h1 hm2,
      mul_le_mul_of_nonneg_right hδ (mul_pos h1 hm2).le]
  have hid : 1 - ((1 - T * M / (m1 * m2)) * (1 - M / γ) - T * D2 / (γ * m1 * m2)) =
      T * M / (m1 * m2) + M / γ - (T * M / (m1 * m2)) * (M / γ) + T * D2 / (γ * m1 * m2) := by
    ring
  rw [hid]
  have hag : 0 ≤ (T * M / (m1 * m2)) * (M / γ) := mul_nonneg ha0 hg0
  have : 2 * δ / γ = δ / γ + δ / γ := by ring
  linarith

/-- `lem:app-pl-determinant`, part (iv) (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Determinant]\label{lem:app-pl-determinant}
For every lag and all $m_1,m_2\in(0,\gamma)$,
\[
0\le\mathsf M_\ell\le m_-,\qquad \mathsf D_\ell^2\le(m_1-\mathsf M_\ell)(m_2-\mathsf M_\ell),\]
\[
\Delta^N_\ell\ge\Big(1-\frac{m_-}\gamma\Big)\Big(1-\frac{\mathsf T_N}{m_+}\Big)\ge c_\alpha\Big(1-\frac{m_1}\gamma\Big)\Big(1-\frac{m_2}\gamma\Big),
\]
and $0\le1-\Delta^N_\ell\le m_-\/m_++2m_-\/\gamma$. If $m_1,m_2\le\delta\le1$, then
$1-\Delta^N_\ell\le C_\bmom\delta+2\delta/\gamma$.
\end{lemma}
-/
theorem lem_app_pl_determinant_iv {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ Cβ : ℝ, ∀ (α : ℝ), 0 < α → ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c →
      ∀ (ℓ : ℤ) (m₁ m₂ δ : ℝ),
        m₁ ∈ Ioo 0 (gammaOf N B) → m₂ ∈ Ioo 0 (gammaOf N B) →
          m₁ ≤ δ → m₂ ≤ δ → δ ≤ 1 →
            1 - deltaN β B (plSpec α c N) ℓ m₁ m₂ ≤ Cβ * δ + 2 * δ / gammaOf N B := by
  have hK : 0 ≤ 3 * sPow β 4 :=
    mul_nonneg (by norm_num)
      (tsum_nonneg fun j => pow_nonneg (vk_emaW_pos hβ0 hβ1 j).le 4)
  refine ⟨(3 * sPow β 4) * (Qm β 1) ^ 2, ?_⟩
  intro α hα N B c hN hB hc ℓ m₁ m₂ δ hm₁ hm₂ h1δ h2δ hδ1
  have hpos := vk_pos_plSpec (α := α) hc N
  obtain ⟨hM0, hMmin, hD⟩ := vk_det_i hβ0 hβ1 hm₁.1 hm₂.1 ℓ
  obtain ⟨hq1, -⟩ := vk_Qm hβ0 hβ1 hm₁.1
  obtain ⟨hq2, -⟩ := vk_Qm hβ0 hβ1 hm₂.1
  have hQ1 := vk_Qm_le hβ0 hβ1 hm₁.1 (h1δ.trans hδ1)
  have hQ2 := vk_Qm_le hβ0 hβ1 hm₂.1 (h2δ.trans hδ1)
  have hMK : MLag β (Qm β m₁) (Qm β m₂) ℓ ≤
      ((3 * sPow β 4) * (Qm β 1) ^ 2) * (m₁ * m₂) := by
    refine (vk_M_le_int hβ0 hβ1 hq1.le hq2.le ℓ).trans ?_
    have : Qm β m₁ * Qm β m₂ ≤ (Qm β 1 * m₁) * (Qm β 1 * m₂) :=
      mul_le_mul hQ1 hQ2 hq2.le ((vk_Qm hβ0 hβ1 one_pos).1.le.trans' le_rfl |> fun _ =>
        mul_nonneg (vk_Qm hβ0 hβ1 one_pos).1.le hm₁.1.le)
    have h2 := mul_le_mul_of_nonneg_left this hK
    calc _ ≤ _ := h2
      _ = _ := by ring
  unfold deltaN
  generalize MLag β (Qm β m₁) (Qm β m₂) ℓ = M at hM0 hMmin hD hMK ⊢
  generalize DLag β (Qm β m₁) (Qm β m₂) ℓ = D at hD ⊢
  have hC : 0 ≤ (3 * sPow β 4) * (Qm β 1) ^ 2 := mul_nonneg hK (sq_nonneg _)
  rcases le_total m₁ m₂ with h | h
  · obtain ⟨hT0, hT1⟩ := vk_T_bd hB hN hpos hm₁ hm₂ h
    exact vk_alg4 (D2 := D ^ 2) hm₁.1 h hm₂.2 hT0 hT1 hM0 (hMmin.trans (min_le_left _ _))
      (sq_nonneg D) hD hC hMK h1δ
  · obtain ⟨hT0, hT1⟩ := vk_T_bd hB hN hpos hm₂ hm₁ h
    rw [vk_TN_comm] at hT0 hT1
    have := vk_alg4 (D2 := D ^ 2) hm₂.1 h hm₁.2 hT0 hT1 hM0
      (hMmin.trans (min_le_right _ _)) (sq_nonneg D)
      (by linarith [hD, mul_comm (m₁ - M) (m₂ - M)]) hC
      (by linarith [hMK, mul_comm m₁ m₂]) h2δ
    have e : (1 - TNpart B (plSpec α c N) m₁ m₂ * M / (m₂ * m₁)) * (1 - M / gammaOf N B) -
        TNpart B (plSpec α c N) m₁ m₂ * D ^ 2 / (gammaOf N B * m₂ * m₁) =
        (1 - TNpart B (plSpec α c N) m₁ m₂ * M / (m₁ * m₂)) * (1 - M / gammaOf N B) -
        TNpart B (plSpec α c N) m₁ m₂ * D ^ 2 / (gammaOf N B * m₁ * m₂) := by ring
    rw [e] at this
    exact this

/-! ### Helpers for `lem_app_pl_localization_i` (fully proved) -/

private lemma loc_sqrt_pow {β : ℝ} (hβ0 : 0 < β) (ℓ : ℕ) (q₁ q₂ : ℝ) :
    β ^ ℓ * Real.sqrt (q₁ * q₂) = Real.sqrt (q₁ * (β ^ (2 * ℓ) * q₂)) := by
  have h : q₁ * (β ^ (2 * ℓ) * q₂) = (β ^ ℓ) ^ 2 * (q₁ * q₂) := by ring
  rw [h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hβ0.le _)]

private lemma loc_frac_int {c : ℝ} (hc : 0 ≤ c) :
    Integrable (fun g : ℝ => c * g ^ 2 / (1 + c * g ^ 2)) (gaussianReal 0 1) := by
  have hden : ∀ g : ℝ, 0 < 1 + c * g ^ 2 := fun g => by
    have := mul_nonneg hc (sq_nonneg g)
    linarith
  refine Integrable.mono' ((Muon.Foundations.gaussian_integrable_pow 2).const_mul c)
    (Continuous.div (by fun_prop) (by fun_prop) (fun g => (hden g).ne')).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg hc (sq_nonneg g)) (hden g).le)]
  exact div_le_self (mul_nonneg hc (sq_nonneg g)) (le_add_of_nonneg_right (mul_nonneg hc (sq_nonneg g)))

private lemma loc_frac_le {c : ℝ} (hc : 0 ≤ c) :
    ∫ g : ℝ, c * g ^ 2 / (1 + c * g ^ 2) ∂(gaussianReal 0 1) ≤ c := by
  calc ∫ g : ℝ, c * g ^ 2 / (1 + c * g ^ 2) ∂(gaussianReal 0 1)
      ≤ ∫ g : ℝ, c * g ^ 2 ∂(gaussianReal 0 1) :=
        integral_mono (loc_frac_int hc) ((Muon.Foundations.gaussian_integrable_pow 2).const_mul c)
          (fun g => div_le_self (mul_nonneg hc (sq_nonneg g))
            (le_add_of_nonneg_right (mul_nonneg hc (sq_nonneg g))))
    _ = c := by rw [integral_const_mul, Muon.Foundations.gaussian_moment_two, mul_one]

private lemma loc_frac_summable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {p : ℝ} (hp : 0 ≤ p) :
    Summable (fun j : ℕ => ∫ g : ℝ, emaW β j ^ 2 * p * g ^ 2 / (1 + emaW β j ^ 2 * p * g ^ 2)
      ∂(gaussianReal 0 1)) := by
  refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun g => ?_) (fun j => ?_)
    ((vk_w2_summable hβ0 hβ1).mul_right p)
  · have := mul_nonneg (mul_nonneg (sq_nonneg (emaW β j)) hp) (sq_nonneg g)
    exact div_nonneg this (by linarith)
  · exact loc_frac_le (mul_nonneg (sq_nonneg _) hp)

/-- `r(p) - r(q) = (p - q) · ∑_j E[w_j² g²/((1+q w_j² g²)(1+p w_j² g²))]`. -/
private lemma loc_rW_sub {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    rW (emaW β) p - rW (emaW β) q = (p - q) * ∑' j : ℕ, ∫ g : ℝ,
      emaW β j ^ 2 * g ^ 2 / ((1 + q * emaW β j ^ 2 * g ^ 2) * (1 + p * emaW β j ^ 2 * g ^ 2))
        ∂(gaussianReal 0 1) := by
  have hw := vk_weightSeq hβ0 hβ1
  rw [(lem_app_de_scalar_iii hw).1 p hp, (lem_app_de_scalar_iii hw).1 q hq,
    ← (loc_frac_summable hβ0 hβ1 hp).tsum_sub (loc_frac_summable hβ0 hβ1 hq), ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  have hpj : 0 ≤ emaW β j ^ 2 * p := mul_nonneg (sq_nonneg _) hp
  have hqj : 0 ≤ emaW β j ^ 2 * q := mul_nonneg (sq_nonneg _) hq
  rw [← integral_sub (loc_frac_int (c := emaW β j ^ 2 * p) hpj)
      (loc_frac_int (c := emaW β j ^ 2 * q) hqj), ← integral_const_mul]
  congr 1
  funext g
  have h1 : 0 < 1 + emaW β j ^ 2 * p * g ^ 2 := by
    have := mul_nonneg hpj (sq_nonneg g)
    linarith
  have h2 : 0 < 1 + emaW β j ^ 2 * q * g ^ 2 := by
    have := mul_nonneg hqj (sq_nonneg g)
    linarith
  field_simp
  ring

/-- Factorisation of the lag numerator: `DLagNat = √(q₁ p) · ∑_j E[w_j² g²/((1+q₁ w_j² g²)(1+p w_j² g²))]`, `p = β^{2ℓ} q₂`. -/
private lemma loc_DLagNat_eq {β : ℝ} (hβ0 : 0 < β) (ℓ : ℕ) {q₁ q₂ : ℝ} :
    DLagNat β q₁ q₂ ℓ = Real.sqrt (q₁ * (β ^ (2 * ℓ) * q₂)) * ∑' j : ℕ, ∫ g : ℝ,
      emaW β j ^ 2 * g ^ 2 / ((1 + q₁ * emaW β j ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q₂ * emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1) := by
  unfold DLagNat
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [← loc_sqrt_pow hβ0 ℓ q₁ q₂, ← integral_const_mul]
  congr 1
  funext g
  ring

/-- Coincident case: `DLagNat = E(m₁)` when `β^{2ℓ} Q_{m₂} = Q_{m₁}`. -/
private lemma loc_coincident {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ℓ : ℕ) {m₁ m₂ : ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (h : β ^ (2 * ℓ) * Qm β m₂ = Qm β m₁) :
    DLagNat β (Qm β m₁) (Qm β m₂) ℓ = Efun β m₁ := by
  obtain ⟨hq, -⟩ := vk_Qm hβ0 hβ1 hm₁
  have hder := (lem_app_de_scalar_iii (vk_weightSeq hβ0 hβ1)).2.2.2.1 (Qm β m₁) hq
  unfold Efun
  rw [hder.deriv, loc_DLagNat_eq hβ0 ℓ, h, Real.sqrt_mul_self hq.le]
  congr 1
  refine tsum_congr fun j => ?_
  rw [← integral_const_mul]
  congr 1
  funext g
  ring

private lemma loc_alg {q E S : ℝ} (hE : 0 < E) (hne : E - E⁻¹ ≠ 0) :
    q * E * S = (q * E ^ 2 - q) * S / (E - E⁻¹) := by
  rw [eq_div_iff hne]
  have hEE : E * E⁻¹ = 1 := mul_inv_cancel₀ hE.ne'
  linear_combination (-(q * S)) * hEE

/-- Guarded case: the `sinh` form of `DLagNat`. -/
private lemma loc_guarded {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ℓ : ℕ) {m₁ m₂ : ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (ht : Real.log (β ^ (2 * ℓ) * Qm β m₂ / Qm β m₁) ≠ 0) :
    DLagNat β (Qm β m₁) (Qm β m₂) ℓ =
      (rW (emaW β) (Qm β m₁ * Real.exp (Real.log (β ^ (2 * ℓ) * Qm β m₂ / Qm β m₁)))
        - rW (emaW β) (Qm β m₁)) /
        (2 * Real.sinh (Real.log (β ^ (2 * ℓ) * Qm β m₂ / Qm β m₁) / 2)) := by
  obtain ⟨hq1, -⟩ := vk_Qm hβ0 hβ1 hm₁
  obtain ⟨hq2, -⟩ := vk_Qm hβ0 hβ1 hm₂
  have hratio : 0 < β ^ (2 * ℓ) * Qm β m₂ / Qm β m₁ := by positivity
  have hexp : Qm β m₁ * Real.exp (Real.log (β ^ (2 * ℓ) * Qm β m₂ / Qm β m₁)) =
      β ^ (2 * ℓ) * Qm β m₂ := by
    rw [Real.exp_log hratio]
    field_simp
  rw [hexp]
  set q₁ := Qm β m₁ with hq₁
  set q₂ := Qm β m₂ with hq₂
  set t := Real.log (β ^ (2 * ℓ) * q₂ / q₁) with htd
  set E := Real.exp (t / 2) with hEd
  have hE : 0 < E := Real.exp_pos _
  have hEt : Real.exp t = E ^ 2 := by
    rw [hEd, sq, ← Real.exp_add]
    congr 1
    ring
  have hp_eq : β ^ (2 * ℓ) * q₂ = q₁ * E ^ 2 := by
    rw [← hexp, hEt]
  have hsqrt : Real.sqrt (q₁ * (β ^ (2 * ℓ) * q₂)) = q₁ * E := by
    rw [hp_eq, show q₁ * (q₁ * E ^ 2) = (q₁ * E) ^ 2 by ring]
    exact Real.sqrt_sq (mul_pos hq1 hE).le
  have hsinh : 2 * Real.sinh (t / 2) = E - E⁻¹ := by
    rw [Real.sinh_eq, Real.exp_neg, ← hEd]
    ring
  have hne : E - E⁻¹ ≠ 0 := by
    intro h
    have h1 : E = E⁻¹ := sub_eq_zero.mp h
    have h2 : E * E = 1 := by
      have : E * E = E * E⁻¹ := by rw [← h1]
      exact this.trans (mul_inv_cancel₀ hE.ne')
    have h3 : Real.exp t = 1 := by
      rw [hEt, sq]
      exact h2
    exact ht (by simpa using h3)
  rw [loc_DLagNat_eq hβ0 ℓ, loc_rW_sub hβ0 hβ1 (mul_nonneg (pow_nonneg hβ0.le _) hq2.le) hq1.le,
    hsqrt, hsinh, hp_eq]
  exact loc_alg hE hne

/-! ### Helpers for the upper bound of `lem_app_pl_localization_i` and for `lem_app_pl_localization_ii` (fully proved) -/

private lemma loc_den_pos {c : ℝ} (hc : 0 ≤ c) (g : ℝ) : 0 < 1 + c * g ^ 2 := by
  have := mul_nonneg hc (sq_nonneg g)
  linarith

private lemma loc_int_w {β : ℝ} (j : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    Integrable (fun g : ℝ => emaW β j ^ 2 * g ^ 2 / (1 + c * emaW β j ^ 2 * g ^ 2))
      (gaussianReal 0 1) := by
  have hden : ∀ g : ℝ, 0 < 1 + c * emaW β j ^ 2 * g ^ 2 := fun g => by
    have := mul_nonneg (mul_nonneg hc (sq_nonneg (emaW β j))) (sq_nonneg g)
    linarith
  refine Integrable.mono' ((Muon.Foundations.gaussian_integrable_pow 2).const_mul (emaW β j ^ 2))
    (Continuous.div (by fun_prop) (by fun_prop) (fun g => (hden g).ne')).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg g)) (hden g).le)]
  exact div_le_self (mul_nonneg (sq_nonneg _) (sq_nonneg g))
    (by have := mul_nonneg (mul_nonneg hc (sq_nonneg (emaW β j))) (sq_nonneg g); linarith)

private lemma loc_U_le_w {β : ℝ} (j : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    ∫ g : ℝ, emaW β j ^ 2 * g ^ 2 / (1 + c * emaW β j ^ 2 * g ^ 2) ∂(gaussianReal 0 1) ≤
      emaW β j ^ 2 := by
  have hden : ∀ g : ℝ, 1 ≤ 1 + c * emaW β j ^ 2 * g ^ 2 := fun g => by
    have := mul_nonneg (mul_nonneg hc (sq_nonneg (emaW β j))) (sq_nonneg g)
    linarith
  calc _ ≤ ∫ g : ℝ, emaW β j ^ 2 * g ^ 2 ∂(gaussianReal 0 1) :=
        integral_mono (loc_int_w j hc) ((Muon.Foundations.gaussian_integrable_pow 2).const_mul _)
          (fun g => div_le_self (mul_nonneg (sq_nonneg _) (sq_nonneg g)) (hden g))
    _ = emaW β j ^ 2 := by rw [integral_const_mul, Muon.Foundations.gaussian_moment_two, mul_one]

private lemma loc_U_nonneg {β : ℝ} (j : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ ∫ g : ℝ, emaW β j ^ 2 * g ^ 2 / (1 + c * emaW β j ^ 2 * g ^ 2) ∂(gaussianReal 0 1) :=
  integral_nonneg fun g => by positivity

private lemma loc_T_nonneg {β : ℝ} (j : ℕ) {q p : ℝ} (hq : 0 ≤ q) (hp : 0 ≤ p) :
    0 ≤ ∫ g : ℝ, emaW β j ^ 2 * g ^ 2 /
      ((1 + q * emaW β j ^ 2 * g ^ 2) * (1 + p * emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1) :=
  integral_nonneg fun g => by positivity

private lemma loc_T_le_U {β : ℝ} (j : ℕ) {q p : ℝ} (hq : 0 ≤ q) (hp : 0 ≤ p) :
    ∫ g : ℝ, emaW β j ^ 2 * g ^ 2 /
      ((1 + q * emaW β j ^ 2 * g ^ 2) * (1 + p * emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1) ≤
    ∫ g : ℝ, emaW β j ^ 2 * g ^ 2 / (1 + p * emaW β j ^ 2 * g ^ 2) ∂(gaussianReal 0 1) := by
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun g => ?_) (loc_int_w j hp)
    (Filter.Eventually.of_forall fun g => ?_)
  · show 0 ≤ _
    positivity
  · show _ ≤ _
    have h1 : 1 ≤ 1 + q * emaW β j ^ 2 * g ^ 2 := by
      have := mul_nonneg (mul_nonneg hq (sq_nonneg (emaW β j))) (sq_nonneg g)
      linarith
    have h2 : 0 < 1 + p * emaW β j ^ 2 * g ^ 2 := by
      have := mul_nonneg (mul_nonneg hp (sq_nonneg (emaW β j))) (sq_nonneg g)
      linarith
    exact div_le_div_of_nonneg_left (by positivity) h2 (le_mul_of_one_le_left h2.le h1)

private lemma loc_T_comm {β : ℝ} (j : ℕ) (q p : ℝ) :
    ∫ g : ℝ, emaW β j ^ 2 * g ^ 2 /
      ((1 + q * emaW β j ^ 2 * g ^ 2) * (1 + p * emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1) =
    ∫ g : ℝ, emaW β j ^ 2 * g ^ 2 /
      ((1 + p * emaW β j ^ 2 * g ^ 2) * (1 + q * emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1) := by
  congr 1
  funext g
  rw [mul_comm (1 + q * emaW β j ^ 2 * g ^ 2)]

private lemma loc_T_summable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q p : ℝ} (hq : 0 ≤ q)
    (hp : 0 ≤ p) :
    Summable (fun j : ℕ => ∫ g : ℝ, emaW β j ^ 2 * g ^ 2 /
      ((1 + q * emaW β j ^ 2 * g ^ 2) * (1 + p * emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1)) :=
  Summable.of_nonneg_of_le (fun j => loc_T_nonneg j hq hp)
    (fun j => (loc_T_le_U j hq hp).trans (loc_U_le_w j hp)) (vk_w2_summable hβ0 hβ1)

private lemma loc_U_summable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {p : ℝ} (hp : 0 ≤ p) :
    Summable (fun j : ℕ => ∫ g : ℝ, emaW β j ^ 2 * g ^ 2 / (1 + p * emaW β j ^ 2 * g ^ 2)
      ∂(gaussianReal 0 1)) :=
  Summable.of_nonneg_of_le (fun j => loc_U_nonneg j hp) (fun j => loc_U_le_w j hp)
    (vk_w2_summable hβ0 hβ1)

private lemma loc_Fw_eq (β p : ℝ) :
    Fw (emaW β) p = ∑' j : ℕ, ∫ g : ℝ, emaW β j ^ 2 * g ^ 2 / (1 + p * emaW β j ^ 2 * g ^ 2)
      ∂(gaussianReal 0 1) := by
  unfold Fw
  refine tsum_congr fun j => ?_
  unfold J
  rw [← integral_const_mul]
  congr 1
  funext g
  ring

private lemma loc_Fw_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {p : ℝ} (hp : 0 ≤ p) :
    Fw (emaW β) p ≤ sPow β 2 := by
  rw [loc_Fw_eq]
  unfold sPow
  exact Summable.tsum_le_tsum (fun j => loc_U_le_w j hp) (loc_U_summable hβ0 hβ1 hp)
    (vk_w2_summable hβ0 hβ1)

private lemma loc_sPow_nonneg (β : ℝ) : 0 ≤ sPow β 2 :=
  tsum_nonneg fun j => sq_nonneg _

private lemma loc_r_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {p : ℝ} (hp : 0 ≤ p) :
    rW (emaW β) p ≤ sPow β 2 * p := by
  unfold rW
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (loc_Fw_le hβ0 hβ1 hp) hp

/-- The three upper bounds for `DLagNat` obtained by dropping denominators. -/
private lemma loc_D_drop {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ℓ : ℕ) {q₁ q₂ : ℝ} (h1 : 0 ≤ q₁)
    (h2 : 0 ≤ q₂) :
    0 ≤ DLagNat β q₁ q₂ ℓ ∧
    DLagNat β q₁ q₂ ℓ ≤ Real.sqrt (q₁ * (β ^ (2 * ℓ) * q₂)) * Fw (emaW β) (β ^ (2 * ℓ) * q₂) ∧
    DLagNat β q₁ q₂ ℓ ≤ Real.sqrt (q₁ * (β ^ (2 * ℓ) * q₂)) * Fw (emaW β) q₁ ∧
    DLagNat β q₁ q₂ ℓ ≤ Real.sqrt (q₁ * (β ^ (2 * ℓ) * q₂)) * sPow β 2 := by
  have hp : 0 ≤ β ^ (2 * ℓ) * q₂ := mul_nonneg (pow_nonneg hβ0.le _) h2
  rw [loc_DLagNat_eq hβ0 ℓ]
  have hS0 : 0 ≤ ∑' j : ℕ, ∫ g : ℝ, emaW β j ^ 2 * g ^ 2 / ((1 + q₁ * emaW β j ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q₂ * emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1) :=
    tsum_nonneg fun j => loc_T_nonneg j h1 hp
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) hS0, ?_, ?_, ?_⟩
  · refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    rw [loc_Fw_eq]
    exact Summable.tsum_le_tsum (fun j => loc_T_le_U j h1 hp) (loc_T_summable hβ0 hβ1 h1 hp)
      (loc_U_summable hβ0 hβ1 hp)
  · refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    rw [loc_Fw_eq]
    refine Summable.tsum_le_tsum (fun j => ?_) (loc_T_summable hβ0 hβ1 h1 hp)
      (loc_U_summable hβ0 hβ1 h1)
    rw [loc_T_comm]
    exact loc_T_le_U j hp h1
  · refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    unfold sPow
    exact Summable.tsum_le_tsum (fun j => (loc_T_le_U j h1 hp).trans (loc_U_le_w j hp))
      (loc_T_summable hβ0 hβ1 h1 hp) (vk_w2_summable hβ0 hβ1)

/-- `M_ℓ ≤ r_β(β^{2ℓ} q₂)`. -/
private lemma loc_M_le_r {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ℓ : ℕ) {q₁ q₂ : ℝ} (h1 : 0 ≤ q₁)
    (h2 : 0 ≤ q₂) :
    MLagNat β q₁ q₂ ℓ ≤ rW (emaW β) (β ^ (2 * ℓ) * q₂) := by
  have hp : 0 ≤ β ^ (2 * ℓ) * q₂ := mul_nonneg (pow_nonneg hβ0.le _) h2
  rw [(lem_app_de_scalar_iii (vk_weightSeq hβ0 hβ1)).1 _ hp]
  unfold MLagNat
  have hterm : ∀ a : ℕ, (∫ g : ℝ, β ^ (2 * ℓ) * q₁ * q₂ * emaW β a ^ 4 * g ^ 4 /
      ((1 + q₁ * emaW β a ^ 2 * g ^ 2) * (1 + β ^ (2 * ℓ) * q₂ * emaW β a ^ 2 * g ^ 2))
      ∂(gaussianReal 0 1)) ≤
      ∫ g : ℝ, emaW β a ^ 2 * (β ^ (2 * ℓ) * q₂) * g ^ 2 /
        (1 + emaW β a ^ 2 * (β ^ (2 * ℓ) * q₂) * g ^ 2) ∂(gaussianReal 0 1) := by
    intro a
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun g => ?_)
      (loc_frac_int (c := emaW β a ^ 2 * (β ^ (2 * ℓ) * q₂)) (mul_nonneg (sq_nonneg _) hp))
      (Filter.Eventually.of_forall fun g => ?_)
    · show 0 ≤ _
      have := pow_nonneg hβ0.le (2 * ℓ)
      positivity
    · beta_reduce
      have hA : 0 ≤ q₁ * emaW β a ^ 2 * g ^ 2 := by positivity
      have hC : 0 ≤ β ^ (2 * ℓ) * q₂ * emaW β a ^ 2 * g ^ 2 := by
        have := pow_nonneg hβ0.le (2 * ℓ)
        positivity
      have e1 : β ^ (2 * ℓ) * q₁ * q₂ * emaW β a ^ 4 * g ^ 4 =
          (q₁ * emaW β a ^ 2 * g ^ 2) * (β ^ (2 * ℓ) * q₂ * emaW β a ^ 2 * g ^ 2) := by ring
      have e2 : emaW β a ^ 2 * (β ^ (2 * ℓ) * q₂) * g ^ 2 =
          β ^ (2 * ℓ) * q₂ * emaW β a ^ 2 * g ^ 2 := by ring
      rw [e1, e2]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg hC (add_nonneg zero_le_one hC), mul_nonneg hA (mul_nonneg hC (add_nonneg zero_le_one hC))]
  refine Summable.tsum_le_tsum hterm (Summable.of_nonneg_of_le (fun a => integral_nonneg fun g => ?_) hterm
    (loc_frac_summable hβ0 hβ1 hp)) (loc_frac_summable hβ0 hβ1 hp)
  have := pow_nonneg hβ0.le (2 * ℓ)
  positivity


private lemma loc_Qm_r {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ} (hq : 0 < q) :
    0 < rW (emaW β) q ∧ Qm β (rW (emaW β) q) = q := by
  have hmono := (lem_app_de_scalar_iii (vk_weightSeq hβ0 hβ1)).2.1
  have hr0 := (lem_app_de_scalar_iii (vk_weightSeq hβ0 hβ1)).2.2.1
  have hpos : 0 < rW (emaW β) q := by
    have := hmono (Set.mem_Ici.2 (le_refl (0 : ℝ))) (Set.mem_Ici.2 hq.le) hq
    rwa [hr0] at this
  refine ⟨hpos, ?_⟩
  obtain ⟨hQ, hrQ⟩ := vk_Qm hβ0 hβ1 hpos
  exact hmono.injOn (Set.mem_Ici.2 hQ.le) (Set.mem_Ici.2 hq.le) hrQ

private lemma loc_lip {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ (∀ q : ℝ, 0 < q → q * deriv (rW (emaW β)) q ≤ K) ∧
      ∀ s s' : ℝ, |rW (emaW β) (Real.exp s') - rW (emaW β) (Real.exp s)| ≤ K * |s' - s| := by
  obtain ⟨c, C, hc, hcC, h⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  have hK : ∀ q : ℝ, 0 < q → q * deriv (rW (emaW β)) q ≤ C := by
    intro q hq
    obtain ⟨hm, hQ⟩ := loc_Qm_r hβ0 hβ1 hq
    have := (h _ hm).2
    unfold Efun at this
    rw [hQ] at this
    exact this.trans (mul_le_of_le_one_right (hc.le.trans hcC) (min_le_right _ _))
  have hK0 : 0 ≤ C := hc.le.trans hcC
  refine ⟨C, hK0, hK, fun s s' => ?_⟩
  have hw := vk_weightSeq hβ0 hβ1
  have hd : ∀ s : ℝ, HasDerivAt (fun s => rW (emaW β) (Real.exp s))
      (deriv (rW (emaW β)) (Real.exp s) * Real.exp s) s := by
    intro s
    have h1 := (lem_app_de_scalar_iii hw).2.2.2.1 (Real.exp s) (Real.exp_pos s)
    have h2 := h1.differentiableAt.hasDerivAt
    exact h2.comp s (Real.hasDerivAt_exp s)
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun s => rW (emaW β) (Real.exp s))
    (s := Set.univ) (C := C) (x := s) (y := s') (fun x _ => (hd x).differentiableAt)
    (fun x _ => by
      rw [(hd x).deriv, Real.norm_eq_abs]
      have hpos : 0 < deriv (rW (emaW β)) (Real.exp x) := by
        have h1 := (lem_app_de_scalar_iii hw).2.2.2.1 (Real.exp x) (Real.exp_pos x)
        rw [h1.deriv]
        exact (lem_app_de_scalar_iii hw).2.2.2.2.1 (Real.exp x) (Real.exp_pos x)
      rw [abs_of_nonneg (mul_nonneg hpos.le (Real.exp_pos x).le)]
      have := hK (Real.exp x) (Real.exp_pos x)
      linarith)
    convex_univ (Set.mem_univ s) (Set.mem_univ s')
  simpa [Real.norm_eq_abs] using this

private lemma loc_sinh_core {x : ℝ} (hx : 0 < x) :
    2 * x ≤ (1 + 2 * x) * Real.exp (-x) * (2 * Real.sinh x) := by
  have hEpos := Real.exp_pos x
  have hE2 : 1 + 2 * x ≤ Real.exp x * Real.exp x := by
    have := Real.add_one_le_exp (2 * x)
    rw [two_mul, Real.exp_add] at this
    linarith
  rw [Real.sinh_eq, Real.exp_neg]
  have e : (1 + 2 * x) * (Real.exp x)⁻¹ * (2 * ((Real.exp x - (Real.exp x)⁻¹) / 2)) =
      (1 + 2 * x) * (Real.exp x * Real.exp x - 1) / (Real.exp x * Real.exp x) := by
    field_simp
  rw [e, le_div_iff₀ (by positivity)]
  nlinarith

private lemma loc_sinh_abs {t : ℝ} (ht : t ≠ 0) :
    |t| ≤ (1 + |t|) * Real.exp (-|t| / 2) * |2 * Real.sinh (t / 2)| := by
  have hx : 0 < |t| / 2 := by
    have := abs_pos.2 ht
    positivity
  have h := loc_sinh_core hx
  have e : |2 * Real.sinh (t / 2)| = 2 * Real.sinh (|t| / 2) := by
    rcases le_total 0 t with h0 | h0
    · rw [abs_of_nonneg h0, abs_of_nonneg]
      have := Real.sinh_nonneg_iff.2 (by linarith : 0 ≤ t / 2)
      linarith
    · have e1 : |t| / 2 = -(t / 2) := by rw [abs_of_nonpos h0]; ring
      rw [abs_of_nonpos, e1, Real.sinh_neg]
      · ring
      · have := Real.sinh_nonpos_iff.2 (by linarith : t / 2 ≤ 0)
        linarith
  rw [e]
  have e2 : -|t| / 2 = -(|t| / 2) := by ring
  rw [e2]
  have e3 : 1 + 2 * (|t| / 2) = 1 + |t| := by ring
  rw [e3] at h
  linarith

private lemma loc_div_bound {β : ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hlip : ∀ s s' : ℝ, |rW (emaW β) (Real.exp s') - rW (emaW β) (Real.exp s)| ≤ K * |s' - s|)
    {q t : ℝ} (hq : 0 < q) (ht : t ≠ 0) :
    (rW (emaW β) (q * Real.exp t) - rW (emaW β) q) / (2 * Real.sinh (t / 2)) ≤
      K * ((1 + |t|) * Real.exp (-|t| / 2)) := by
  have hsn : 0 < |2 * Real.sinh (t / 2)| := by
    refine abs_pos.2 ?_
    have : Real.sinh (t / 2) ≠ 0 := by
      intro h
      exact ht (by simpa using Real.sinh_eq_zero.1 h)
    positivity
  have hnum : |rW (emaW β) (q * Real.exp t) - rW (emaW β) q| ≤ K * |t| := by
    have := hlip (Real.log q) (Real.log q + t)
    rw [Real.exp_add, Real.exp_log hq] at this
    simpa using this
  calc _ ≤ |(rW (emaW β) (q * Real.exp t) - rW (emaW β) q) / (2 * Real.sinh (t / 2))| :=
        le_abs_self _
    _ = |rW (emaW β) (q * Real.exp t) - rW (emaW β) q| / |2 * Real.sinh (t / 2)| := abs_div _ _
    _ ≤ K * |t| / |2 * Real.sinh (t / 2)| := by gcongr
    _ ≤ _ := by
        rw [div_le_iff₀ hsn]
        have := loc_sinh_abs ht
        nlinarith [mul_le_mul_of_nonneg_left this hK0]

private lemma loc_D_bd1 {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ℓ : ℕ) (m₁ m₂ : ℝ), 0 < m₁ → 0 < m₂ →
      DLagNat β (Qm β m₁) (Qm β m₂) ℓ ≤
        K * ((1 + |Real.log (β ^ (2 * ℓ) * Qm β m₂ / Qm β m₁)|) *
          Real.exp (-|Real.log (β ^ (2 * ℓ) * Qm β m₂ / Qm β m₁)| / 2)) := by
  obtain ⟨K, hK0, hK, hlip⟩ := loc_lip hβ0 hβ1
  refine ⟨K, hK0, fun ℓ m₁ m₂ h₁ h₂ => ?_⟩
  obtain ⟨hq1, -⟩ := vk_Qm hβ0 hβ1 h₁
  obtain ⟨hq2, -⟩ := vk_Qm hβ0 hβ1 h₂
  by_cases h0 : Real.log (β ^ (2 * ℓ) * Qm β m₂ / Qm β m₁) = 0
  · have hratio : 0 < β ^ (2 * ℓ) * Qm β m₂ / Qm β m₁ := by positivity
    have h1 : β ^ (2 * ℓ) * Qm β m₂ / Qm β m₁ = 1 := by
      have := Real.exp_log hratio
      rw [h0, Real.exp_zero] at this
      exact this.symm
    have hco : β ^ (2 * ℓ) * Qm β m₂ = Qm β m₁ := (div_eq_one_iff_eq hq1.ne').1 h1
    rw [loc_coincident hβ0 hβ1 ℓ h₁ h₂ hco, h0]
    simp only [abs_zero, add_zero, zero_div, neg_zero, Real.exp_zero, mul_one]
    unfold Efun
    exact hK _ hq1
  · rw [loc_guarded hβ0 hβ1 ℓ h₁ h₂ h0]
    exact loc_div_bound hK0 hlip hq1 h0

private lemma loc_r_log {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p : ℝ, 1 ≤ p →
      rW (emaW β) p ≤ A + 1 / (2 * -Real.log β) * Real.log p := by
  obtain ⟨C, hC⟩ := lem_app_pl_weights_iii_logQ hβ0 hβ1
  have hb : 0 < -Real.log β := neg_pos.2 (Real.log_neg hβ0 hβ1)
  have hL : |Real.log β| = -Real.log β := abs_of_neg (Real.log_neg hβ0 hβ1)
  refine ⟨1 + |C| / (2 * -Real.log β), by positivity, fun p hp => ?_⟩
  have hp0 : 0 < p := by linarith
  obtain ⟨hm, hQ⟩ := loc_Qm_r hβ0 hβ1 hp0
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg hp
  have h2b : 0 < 2 * -Real.log β := by positivity
  by_cases hm1 : rW (emaW β) p < 1
  · have : 0 ≤ |C| / (2 * -Real.log β) := by positivity
    have : 0 ≤ 1 / (2 * -Real.log β) * Real.log p := by positivity
    linarith
  · push_neg at hm1
    have := hC _ hm1
    rw [hQ, hL] at this
    have h3 := (abs_le.1 this).1
    have h4 : rW (emaW β) p * (2 * -Real.log β) ≤ Real.log p + |C| := by
      have := le_abs_self C
      nlinarith
    have h5 : rW (emaW β) p ≤ (Real.log p + |C|) / (2 * -Real.log β) := by
      rw [le_div_iff₀ h2b]
      exact h4
    have e : (Real.log p + |C|) / (2 * -Real.log β) =
        |C| / (2 * -Real.log β) + 1 / (2 * -Real.log β) * Real.log p := by ring
    linarith

private lemma loc_G {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ p : ℝ, 0 < p →
      Real.sqrt p * Fw (emaW β) p ≤ K₀ * ((1 + |Real.log p|) * Real.exp (-|Real.log p| / 2)) := by
  obtain ⟨A, hA, hr⟩ := loc_r_log hβ0 hβ1
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = 1 / (2 * -Real.log β) := ⟨_, rfl⟩
  have hB : 0 ≤ B := by
    have := neg_pos.2 (Real.log_neg hβ0 hβ1)
    rw [hBdef]
    positivity
  rw [← hBdef] at hr
  have hs2 := loc_sPow_nonneg β
  refine ⟨max (sPow β 2) (max A B), le_max_of_le_left hs2, fun p hp => ?_⟩
  have hsq : Real.sqrt p = Real.exp (Real.log p / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp]
    congr 1
    ring
  have hKs : sPow β 2 ≤ max (sPow β 2) (max A B) := le_max_left _ _
  have hKA : A ≤ max (sPow β 2) (max A B) := (le_max_left _ _).trans (le_max_right _ _)
  have hKB : B ≤ max (sPow β 2) (max A B) := (le_max_right _ _).trans (le_max_right _ _)
  have hL0 := abs_nonneg (Real.log p)
  rcases le_total p 1 with hp1 | hp1
  · have hlog : Real.log p ≤ 0 := Real.log_nonpos hp.le hp1
    have habs : |Real.log p| = -Real.log p := abs_of_nonpos hlog
    have e : -|Real.log p| / 2 = Real.log p / 2 := by rw [habs]; ring
    rw [e, ← hsq]
    have h1 : Real.sqrt p * Fw (emaW β) p ≤ Real.sqrt p * sPow β 2 :=
      mul_le_mul_of_nonneg_left (loc_Fw_le hβ0 hβ1 hp.le) (Real.sqrt_nonneg _)
    have h2 : sPow β 2 ≤ max (sPow β 2) (max A B) * (1 + |Real.log p|) := by nlinarith
    calc _ ≤ Real.sqrt p * sPow β 2 := h1
      _ ≤ Real.sqrt p * (max (sPow β 2) (max A B) * (1 + |Real.log p|)) :=
          mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
      _ = _ := by ring
  · have hlog : 0 ≤ Real.log p := Real.log_nonneg hp1
    have habs : |Real.log p| = Real.log p := abs_of_nonneg hlog
    rw [habs]
    have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
    have hss : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp.le
    have hexp : Real.exp (-Real.log p / 2) = (Real.sqrt p)⁻¹ := by
      rw [hsq, ← Real.exp_neg]
      congr 1
      ring
    rw [hexp]
    have hrp := hr p hp1
    unfold rW at hrp
    have hK : A + B * Real.log p ≤ max (sPow β 2) (max A B) * (1 + Real.log p) := by
      nlinarith [mul_le_mul_of_nonneg_right hKB hlog]
    have e : ∀ a b c : ℝ, a * (b * c⁻¹) = a * b / c := fun a b c => by ring
    rw [e, le_div_iff₀ hs]
    have e2 : Real.sqrt p * Fw (emaW β) p * Real.sqrt p = p * Fw (emaW β) p := by
      calc _ = (Real.sqrt p * Real.sqrt p) * Fw (emaW β) p := by ring
        _ = _ := by rw [hss]
    rw [e2]
    linarith


private lemma loc_conv {b c x y : ℝ} (hb : 0 < b) (hc : 0 ≤ c) (hy : 0 ≤ y)
    (h : x ≤ 2 * b * y + c) (h' : 2 * b * y - c ≤ x) :
    (1 + x) * Real.exp (-x / 2) ≤
      ((1 + 2 * b + c) * Real.exp (c / 2)) * ((1 + y) * Real.exp (-b * y)) := by
  have h1 : 1 + x ≤ (1 + 2 * b + c) * (1 + y) := by
    nlinarith [mul_nonneg hc hy, mul_nonneg hb.le hy]
  have h2 : Real.exp (-x / 2) ≤ Real.exp (c / 2) * Real.exp (-b * y) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith
  calc (1 + x) * Real.exp (-x / 2)
      ≤ ((1 + 2 * b + c) * (1 + y)) * (Real.exp (c / 2) * Real.exp (-b * y)) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

private lemma loc_conv2 {b c t y : ℝ} (hb : 0 < b) (hc : 0 ≤ c) (h : |t - 2 * b * y| ≤ c) :
    (1 + |t|) * Real.exp (-|t| / 2) ≤
      ((1 + 2 * b + c) * Real.exp (c / 2)) * ((1 + |y|) * Real.exp (-b * |y|)) := by
  have h1 := abs_abs_sub_abs_le_abs_sub t (2 * b * y)
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hb] at h1
  have h2 := abs_le.1 h1
  have h3 := abs_le.1 (h1.trans h)
  exact loc_conv hb hc (abs_nonneg _) (by linarith [h3.2]) (by linarith [h3.1])

private lemma loc_logt {β b : ℝ} (hlog : Real.log β = -b) (hβ0 : 0 < β) (ℓ : ℕ) {Q₁ Q₂ : ℝ}
    (h1 : 0 < Q₁) (h2 : 0 < Q₂) :
    Real.log (β ^ (2 * ℓ) * Q₂ / Q₁) = -(2 * b * ℓ) + Real.log Q₂ - Real.log Q₁ := by
  rw [Real.log_div (by positivity) h1.ne', Real.log_mul (by positivity) h2.ne', Real.log_pow, hlog]
  push_cast
  ring

private lemma loc_logp {β b : ℝ} (hlog : Real.log β = -b) (hβ0 : 0 < β) (ℓ : ℕ) {Q : ℝ}
    (h : 0 < Q) :
    Real.log (β ^ (2 * ℓ) * Q) = -(2 * b * ℓ) + Real.log Q := by
  rw [Real.log_mul (by positivity) h.ne', Real.log_pow, hlog]
  push_cast
  ring

private lemma loc_beta_pow {β b : ℝ} (hlog : Real.log β = -b) (hβ0 : 0 < β) (ℓ : ℕ) :
    β ^ ℓ = Real.exp (-(b * ℓ)) := by
  have : β ^ ℓ = Real.exp (ℓ * Real.log β) := by rw [Real.exp_nat_mul, Real.exp_log hβ0]
  rw [this, hlog]
  congr 1
  ring

private lemma loc_sqrt_p {β : ℝ} (hβ0 : 0 < β) (ℓ : ℕ) (q : ℝ) :
    Real.sqrt (β ^ (2 * ℓ) * q) = β ^ ℓ * Real.sqrt q := by
  have h : β ^ (2 * ℓ) = (β ^ ℓ) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [Real.sqrt_mul (pow_nonneg hβ0.le _), h, Real.sqrt_sq (pow_nonneg hβ0.le _)]

private lemma loc_caseA {β b K c₁ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hb : 0 < b)
    (hlog : Real.log β = -b) (hK0 : 0 ≤ K) (hc₁ : 0 ≤ c₁)
    (hD : ∀ (ℓ : ℕ) (m₁ m₂ : ℝ), 0 < m₁ → 0 < m₂ →
      DLagNat β (Qm β m₁) (Qm β m₂) ℓ ≤
        K * ((1 + |Real.log (β ^ (2 * ℓ) * Qm β m₂ / Qm β m₁)|) *
          Real.exp (-|Real.log (β ^ (2 * ℓ) * Qm β m₂ / Qm β m₁)| / 2)))
    (hQ : ∀ m : ℝ, 1 ≤ m → |Real.log (Qm β m) - 2 * b * m| ≤ c₁)
    (ℓ : ℕ) {m₁ m₂ : ℝ} (h1 : 1 ≤ m₁) (h2 : 1 ≤ m₂) :
    DLagNat β (Qm β m₁) (Qm β m₂) ℓ ≤
      (K * ((1 + 2 * b + 2 * c₁) * Real.exp (2 * c₁ / 2))) *
        ((1 + |m₁ - m₂ + ℓ|) * Real.exp (-b * |m₁ - m₂ + ℓ|)) := by
  have hm1 : 0 < m₁ := by linarith
  have hm2 : 0 < m₂ := by linarith
  obtain ⟨hq1, -⟩ := vk_Qm hβ0 hβ1 hm1
  obtain ⟨hq2, -⟩ := vk_Qm hβ0 hβ1 hm2
  refine (hD ℓ m₁ m₂ hm1 hm2).trans ?_
  have e1 := abs_le.1 (hQ m₁ h1)
  have e2 := abs_le.1 (hQ m₂ h2)
  have hconv := loc_conv2 (b := b) (c := 2 * c₁)
    (t := Real.log (β ^ (2 * ℓ) * Qm β m₂ / Qm β m₁)) (y := -(m₁ - m₂ + ℓ)) hb (by linarith)
    (by
      rw [loc_logt hlog hβ0 ℓ hq1 hq2, abs_le]
      constructor <;> nlinarith [e1.1, e1.2, e2.1, e2.2])
  rw [abs_neg] at hconv
  calc _ ≤ K * (((1 + 2 * b + 2 * c₁) * Real.exp (2 * c₁ / 2)) *
        ((1 + |m₁ - m₂ + ℓ|) * Real.exp (-b * |m₁ - m₂ + ℓ|))) := mul_le_mul_of_nonneg_left hconv hK0
    _ = _ := by ring

private lemma loc_caseB {β b K₀ c₁ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hb : 0 < b)
    (hlog : Real.log β = -b) (hK₀ : 0 ≤ K₀) (hc₁ : 0 ≤ c₁)
    (hG : ∀ p : ℝ, 0 < p → Real.sqrt p * Fw (emaW β) p ≤
      K₀ * ((1 + |Real.log p|) * Real.exp (-|Real.log p| / 2)))
    (hQ : ∀ m : ℝ, 1 ≤ m → |Real.log (Qm β m) - 2 * b * m| ≤ c₁)
    (ℓ : ℕ) {m₁ m₂ : ℝ} (h1 : 0 < m₁) (h1' : m₁ ≤ 1) (h2 : 1 ≤ m₂) :
    DLagNat β (Qm β m₁) (Qm β m₂) ℓ ≤
      (Real.sqrt (Qm β 1) * K₀ * ((1 + 2 * b + (c₁ + 2 * b)) * Real.exp ((c₁ + 2 * b) / 2))) *
        (Real.sqrt m₁ * ((1 + |m₁ - m₂ + ℓ|) * Real.exp (-b * |m₁ - m₂ + ℓ|))) := by
  have hm2 : 0 < m₂ := by linarith
  obtain ⟨hq1, -⟩ := vk_Qm hβ0 hβ1 h1
  obtain ⟨hq2, -⟩ := vk_Qm hβ0 hβ1 hm2
  obtain ⟨hqs, -⟩ := vk_Qm hβ0 hβ1 (zero_lt_one : (0 : ℝ) < 1)
  have hp : 0 < β ^ (2 * ℓ) * Qm β m₂ := by positivity
  have hD := (loc_D_drop hβ0 hβ1 ℓ hq1.le hq2.le).2.1
  rw [Real.sqrt_mul hq1.le] at hD
  have hG' := hG _ hp
  have hsq1 : Real.sqrt (Qm β m₁) ≤ Real.sqrt (Qm β 1) * Real.sqrt m₁ := by
    rw [← Real.sqrt_mul hqs.le]
    exact Real.sqrt_le_sqrt (by
      have := vk_Qm_le hβ0 hβ1 h1 h1'
      linarith)
  have e2 := abs_le.1 (hQ m₂ h2)
  have hconv := loc_conv2 (b := b) (c := c₁ + 2 * b)
    (t := Real.log (β ^ (2 * ℓ) * Qm β m₂)) (y := -(m₁ - m₂ + ℓ)) hb (by linarith)
    (by
      rw [loc_logp hlog hβ0 ℓ hq2, abs_le]
      constructor <;> nlinarith [e2.1, e2.2, mul_le_mul_of_nonneg_left h1' hb.le])
  rw [abs_neg] at hconv
  have hY : 0 ≤ (1 + |m₁ - m₂ + ℓ|) * Real.exp (-b * |m₁ - m₂ + ℓ|) := by positivity
  have hCc : 0 ≤ (1 + 2 * b + (c₁ + 2 * b)) * Real.exp ((c₁ + 2 * b) / 2) := by positivity
  calc _ ≤ Real.sqrt (Qm β m₁) * Real.sqrt (β ^ (2 * ℓ) * Qm β m₂) *
        Fw (emaW β) (β ^ (2 * ℓ) * Qm β m₂) := hD
    _ = Real.sqrt (Qm β m₁) * (Real.sqrt (β ^ (2 * ℓ) * Qm β m₂) *
        Fw (emaW β) (β ^ (2 * ℓ) * Qm β m₂)) := by ring
    _ ≤ Real.sqrt (Qm β m₁) * (K₀ * (((1 + 2 * b + (c₁ + 2 * b)) * Real.exp ((c₁ + 2 * b) / 2)) *
        ((1 + |m₁ - m₂ + ℓ|) * Real.exp (-b * |m₁ - m₂ + ℓ|)))) :=
        mul_le_mul_of_nonneg_left (hG'.trans (mul_le_mul_of_nonneg_left hconv hK₀))
          (Real.sqrt_nonneg _)
    _ ≤ (Real.sqrt (Qm β 1) * Real.sqrt m₁) * (K₀ * (((1 + 2 * b + (c₁ + 2 * b)) *
        Real.exp ((c₁ + 2 * b) / 2)) * ((1 + |m₁ - m₂ + ℓ|) * Real.exp (-b * |m₁ - m₂ + ℓ|)))) :=
        mul_le_mul_of_nonneg_right hsq1 (mul_nonneg hK₀ (mul_nonneg hCc hY))
    _ = _ := by ring

private lemma loc_caseC {β b K₀ c₁ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hb : 0 < b)
    (hlog : Real.log β = -b) (hK₀ : 0 ≤ K₀) (hc₁ : 0 ≤ c₁)
    (hG : ∀ p : ℝ, 0 < p → Real.sqrt p * Fw (emaW β) p ≤
      K₀ * ((1 + |Real.log p|) * Real.exp (-|Real.log p| / 2)))
    (hQ : ∀ m : ℝ, 1 ≤ m → |Real.log (Qm β m) - 2 * b * m| ≤ c₁)
    (ℓ : ℕ) {m₁ m₂ : ℝ} (h1 : 1 ≤ m₁) (h2 : 0 < m₂) (h2' : m₂ ≤ 1) :
    DLagNat β (Qm β m₁) (Qm β m₂) ℓ ≤
      (2 * (Real.sqrt (Qm β 1) * K₀ * ((1 + 2 * b + c₁) * Real.exp (c₁ / 2)))) *
        (Real.sqrt m₂ * ((1 + |m₁ - m₂ + ℓ|) * Real.exp (-b * |m₁ - m₂ + ℓ|))) := by
  have hm1 : 0 < m₁ := by linarith
  obtain ⟨hq1, -⟩ := vk_Qm hβ0 hβ1 hm1
  obtain ⟨hq2, -⟩ := vk_Qm hβ0 hβ1 h2
  obtain ⟨hqs, -⟩ := vk_Qm hβ0 hβ1 (zero_lt_one : (0 : ℝ) < 1)
  have hD := (loc_D_drop hβ0 hβ1 ℓ hq1.le hq2.le).2.2.1
  rw [Real.sqrt_mul hq1.le, loc_sqrt_p hβ0] at hD
  have hG' := hG _ hq1
  have hsq2 : Real.sqrt (Qm β m₂) ≤ Real.sqrt (Qm β 1) * Real.sqrt m₂ := by
    rw [← Real.sqrt_mul hqs.le]
    exact Real.sqrt_le_sqrt (by
      have := vk_Qm_le hβ0 hβ1 h2 h2'
      linarith)
  have hconv := loc_conv2 (b := b) (c := c₁) (t := Real.log (Qm β m₁)) (y := m₁) hb hc₁
    (by
      have := hQ m₁ h1
      exact this)
  rw [abs_of_pos hm1] at hconv
  -- the geometric factor
  have hδ0 : 0 ≤ m₁ - m₂ + ℓ := by
    have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
    linarith
  rw [abs_of_nonneg hδ0]
  have hexp : β ^ ℓ * Real.exp (-b * m₁) ≤ Real.exp (-b * (m₁ - m₂ + ℓ)) := by
    rw [loc_beta_pow hlog hβ0, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
    nlinarith [mul_nonneg hb.le h2.le]
  have h1m : 1 + m₁ ≤ 2 * (1 + (m₁ - m₂ + ℓ)) := by
    have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
    linarith
  have hCc : 0 ≤ (1 + 2 * b + c₁) * Real.exp (c₁ / 2) := by positivity
  have hbl : 0 ≤ β ^ ℓ := pow_nonneg hβ0.le ℓ
  have hX : β ^ ℓ * ((1 + m₁) * Real.exp (-b * m₁)) ≤
      2 * ((1 + (m₁ - m₂ + ℓ)) * Real.exp (-b * (m₁ - m₂ + ℓ))) := by
    calc _ = (1 + m₁) * (β ^ ℓ * Real.exp (-b * m₁)) := by ring
      _ ≤ (2 * (1 + (m₁ - m₂ + ℓ))) * Real.exp (-b * (m₁ - m₂ + ℓ)) :=
          mul_le_mul h1m hexp (mul_nonneg hbl (Real.exp_pos _).le) (by positivity)
      _ = _ := by ring
  calc _ ≤ Real.sqrt (Qm β m₁) * (β ^ ℓ * Real.sqrt (Qm β m₂)) * Fw (emaW β) (Qm β m₁) := hD
    _ = (β ^ ℓ * Real.sqrt (Qm β m₂)) * (Real.sqrt (Qm β m₁) * Fw (emaW β) (Qm β m₁)) := by ring
    _ ≤ (β ^ ℓ * Real.sqrt (Qm β m₂)) * (K₀ * (((1 + 2 * b + c₁) * Real.exp (c₁ / 2)) *
        ((1 + m₁) * Real.exp (-b * m₁)))) :=
        mul_le_mul_of_nonneg_left (hG'.trans (mul_le_mul_of_nonneg_left hconv hK₀))
          (mul_nonneg hbl (Real.sqrt_nonneg _))
    _ ≤ (β ^ ℓ * (Real.sqrt (Qm β 1) * Real.sqrt m₂)) * (K₀ * (((1 + 2 * b + c₁) *
        Real.exp (c₁ / 2)) * ((1 + m₁) * Real.exp (-b * m₁)))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq2 hbl)
          (mul_nonneg hK₀ (mul_nonneg hCc (by positivity)))
    _ = (Real.sqrt (Qm β 1) * K₀ * ((1 + 2 * b + c₁) * Real.exp (c₁ / 2))) * Real.sqrt m₂ *
        (β ^ ℓ * ((1 + m₁) * Real.exp (-b * m₁))) := by ring
    _ ≤ (Real.sqrt (Qm β 1) * K₀ * ((1 + 2 * b + c₁) * Real.exp (c₁ / 2))) * Real.sqrt m₂ *
        (2 * ((1 + (m₁ - m₂ + ℓ)) * Real.exp (-b * (m₁ - m₂ + ℓ)))) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ = _ := by ring

private lemma loc_caseD {β b : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hb : 0 < b)
    (hlog : Real.log β = -b) (ℓ : ℕ) {m₁ m₂ : ℝ} (h1 : 0 < m₁) (h1' : m₁ ≤ 1) (h2 : 0 < m₂)
    (h2' : m₂ ≤ 1) :
    DLagNat β (Qm β m₁) (Qm β m₂) ℓ ≤
      (Qm β 1 * sPow β 2 * Real.exp b) *
        (Real.sqrt (min m₁ m₂) * ((1 + |m₁ - m₂ + ℓ|) * Real.exp (-b * |m₁ - m₂ + ℓ|))) := by
  obtain ⟨hq1, -⟩ := vk_Qm hβ0 hβ1 h1
  obtain ⟨hq2, -⟩ := vk_Qm hβ0 hβ1 h2
  obtain ⟨hqs, -⟩ := vk_Qm hβ0 hβ1 (zero_lt_one : (0 : ℝ) < 1)
  have hD := (loc_D_drop hβ0 hβ1 ℓ hq1.le hq2.le).2.2.2
  rw [Real.sqrt_mul hq1.le, loc_sqrt_p hβ0] at hD
  have hsq1 : Real.sqrt (Qm β m₁) ≤ Real.sqrt (Qm β 1) * Real.sqrt m₁ := by
    rw [← Real.sqrt_mul hqs.le]
    exact Real.sqrt_le_sqrt (by
      have := vk_Qm_le hβ0 hβ1 h1 h1'
      linarith)
  have hsq2 : Real.sqrt (Qm β m₂) ≤ Real.sqrt (Qm β 1) * Real.sqrt m₂ := by
    rw [← Real.sqrt_mul hqs.le]
    exact Real.sqrt_le_sqrt (by
      have := vk_Qm_le hβ0 hβ1 h2 h2'
      linarith)
  have hs2 := loc_sPow_nonneg β
  have hbl : 0 ≤ β ^ ℓ := pow_nonneg hβ0.le ℓ
  have hmm : Real.sqrt m₁ * Real.sqrt m₂ ≤ Real.sqrt (min m₁ m₂) := by
    rcases le_total m₁ m₂ with h | h
    · rw [min_eq_left h]
      have : Real.sqrt m₂ ≤ 1 := by
        rw [Real.sqrt_le_one]
        exact h2'
      nlinarith [Real.sqrt_nonneg m₁]
    · rw [min_eq_right h]
      have : Real.sqrt m₁ ≤ 1 := by
        rw [Real.sqrt_le_one]
        exact h1'
      nlinarith [Real.sqrt_nonneg m₂]
  have hss : Real.sqrt (Qm β 1) * Real.sqrt (Qm β 1) = Qm β 1 := Real.mul_self_sqrt hqs.le
  -- the geometric factor
  have hexp : β ^ ℓ ≤ Real.exp b * Real.exp (-b * |m₁ - m₂ + ℓ|) := by
    rw [loc_beta_pow hlog hβ0, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : |m₁ - m₂ + ℓ| ≤ 1 + ℓ := by
      rw [abs_le]
      constructor <;> linarith
    nlinarith
  have hY : 1 ≤ 1 + |m₁ - m₂ + ℓ| := by linarith [abs_nonneg (m₁ - m₂ + ℓ)]
  have hE0 := (Real.exp_pos (-b * |m₁ - m₂ + ℓ|)).le
  calc _ ≤ Real.sqrt (Qm β m₁) * (β ^ ℓ * Real.sqrt (Qm β m₂)) * sPow β 2 := hD
    _ = β ^ ℓ * (Real.sqrt (Qm β m₁) * Real.sqrt (Qm β m₂)) * sPow β 2 := by ring
    _ ≤ β ^ ℓ * ((Real.sqrt (Qm β 1) * Real.sqrt m₁) * (Real.sqrt (Qm β 1) * Real.sqrt m₂)) *
        sPow β 2 := by
        gcongr
    _ = (Qm β 1 * sPow β 2) * β ^ ℓ * (Real.sqrt m₁ * Real.sqrt m₂) := by
        linear_combination (β ^ ℓ * sPow β 2 * Real.sqrt m₁ * Real.sqrt m₂) * hss
    _ ≤ (Qm β 1 * sPow β 2) * (Real.exp b * Real.exp (-b * |m₁ - m₂ + ℓ|)) *
        Real.sqrt (min m₁ m₂) := by
        gcongr
    _ ≤ (Qm β 1 * sPow β 2) * (Real.exp b * Real.exp (-b * |m₁ - m₂ + ℓ|)) *
        (Real.sqrt (min m₁ m₂) * (1 + |m₁ - m₂ + ℓ|)) := by
        have : 0 ≤ (Qm β 1 * sPow β 2) * (Real.exp b * Real.exp (-b * |m₁ - m₂ + ℓ|)) * Real.sqrt (min m₁ m₂) := by positivity
        nlinarith
    _ = _ := by ring


private lemma loc_D_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : ℕ) (m₁ m₂ : ℝ), 0 < m₁ → 0 < m₂ →
      DLagNat β (Qm β m₁) (Qm β m₂) ℓ ≤
        C * Real.sqrt (min (min m₁ m₂) 1) * (1 + |m₁ - m₂ + ℓ|) *
          Real.exp (-|Real.log β| * |m₁ - m₂ + ℓ|) := by
  obtain ⟨K, hK0, hD⟩ := loc_D_bd1 hβ0 hβ1
  obtain ⟨K₀, hK₀, hG⟩ := loc_G hβ0 hβ1
  obtain ⟨CQ, hCQ⟩ := lem_app_pl_weights_iii_logQ hβ0 hβ1
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = -Real.log β := ⟨_, rfl⟩
  have hb : 0 < b := by rw [hbdef]; exact neg_pos.2 (Real.log_neg hβ0 hβ1)
  have hlog : Real.log β = -b := by rw [hbdef]; ring
  have habs : |Real.log β| = b := by rw [hlog, abs_neg, abs_of_pos hb]
  have hQ : ∀ m : ℝ, 1 ≤ m → |Real.log (Qm β m) - 2 * b * m| ≤ |CQ| := fun m hm => by
    have := hCQ m hm
    rw [habs] at this
    exact this.trans (le_abs_self CQ)
  obtain ⟨c₁, hc₁def⟩ : ∃ c₁ : ℝ, c₁ = |CQ| := ⟨_, rfl⟩
  rw [← hc₁def] at hQ
  have hc₁ : 0 ≤ c₁ := by rw [hc₁def]; exact abs_nonneg _
  obtain ⟨hqs, -⟩ := vk_Qm hβ0 hβ1 (zero_lt_one : (0 : ℝ) < 1)
  have hs2 := loc_sPow_nonneg β
  have hcA : 0 ≤ K * ((1 + 2 * b + 2 * c₁) * Real.exp (2 * c₁ / 2)) := by positivity
  have hcB : 0 ≤ Real.sqrt (Qm β 1) * K₀ * ((1 + 2 * b + (c₁ + 2 * b)) *
      Real.exp ((c₁ + 2 * b) / 2)) := by positivity
  have hcC : 0 ≤ 2 * (Real.sqrt (Qm β 1) * K₀ * ((1 + 2 * b + c₁) * Real.exp (c₁ / 2))) := by
    positivity
  have hcD : 0 ≤ Qm β 1 * sPow β 2 * Real.exp b := by positivity
  refine ⟨K * ((1 + 2 * b + 2 * c₁) * Real.exp (2 * c₁ / 2)) +
    Real.sqrt (Qm β 1) * K₀ * ((1 + 2 * b + (c₁ + 2 * b)) * Real.exp ((c₁ + 2 * b) / 2)) +
    2 * (Real.sqrt (Qm β 1) * K₀ * ((1 + 2 * b + c₁) * Real.exp (c₁ / 2))) +
    Qm β 1 * sPow β 2 * Real.exp b, by positivity, fun ℓ m₁ m₂ h₁ h₂ => ?_⟩
  rw [habs]
  have hY : 0 ≤ (1 + |m₁ - m₂ + ℓ|) * Real.exp (-b * |m₁ - m₂ + ℓ|) := by positivity
  have hR : 0 ≤ Real.sqrt (min (min m₁ m₂) 1) *
      ((1 + |m₁ - m₂ + ℓ|) * Real.exp (-b * |m₁ - m₂ + ℓ|)) := by positivity
  have fin : ∀ c : ℝ, c ≤ K * ((1 + 2 * b + 2 * c₁) * Real.exp (2 * c₁ / 2)) +
      Real.sqrt (Qm β 1) * K₀ * ((1 + 2 * b + (c₁ + 2 * b)) * Real.exp ((c₁ + 2 * b) / 2)) +
      2 * (Real.sqrt (Qm β 1) * K₀ * ((1 + 2 * b + c₁) * Real.exp (c₁ / 2))) +
      Qm β 1 * sPow β 2 * Real.exp b →
      DLagNat β (Qm β m₁) (Qm β m₂) ℓ ≤ c * (Real.sqrt (min (min m₁ m₂) 1) *
        ((1 + |m₁ - m₂ + ℓ|) * Real.exp (-b * |m₁ - m₂ + ℓ|))) →
      DLagNat β (Qm β m₁) (Qm β m₂) ℓ ≤
        (K * ((1 + 2 * b + 2 * c₁) * Real.exp (2 * c₁ / 2)) +
      Real.sqrt (Qm β 1) * K₀ * ((1 + 2 * b + (c₁ + 2 * b)) * Real.exp ((c₁ + 2 * b) / 2)) +
      2 * (Real.sqrt (Qm β 1) * K₀ * ((1 + 2 * b + c₁) * Real.exp (c₁ / 2))) +
      Qm β 1 * sPow β 2 * Real.exp b) * Real.sqrt (min (min m₁ m₂) 1) *
        (1 + |m₁ - m₂ + ℓ|) * Real.exp (-b * |m₁ - m₂ + ℓ|) := by
    intro c hc h
    calc _ ≤ c * _ := h
      _ ≤ _ := mul_le_mul_of_nonneg_right hc hR
      _ = _ := by ring
  by_cases a1 : 1 ≤ m₁
  · by_cases a2 : 1 ≤ m₂
    · have hS : Real.sqrt (min (min m₁ m₂) 1) = 1 := by
        rw [min_eq_right (le_min a1 a2), Real.sqrt_one]
      refine fin (K * ((1 + 2 * b + 2 * c₁) * Real.exp (2 * c₁ / 2))) (by linarith) ?_
      rw [hS, one_mul]
      exact loc_caseA hβ0 hβ1 hb hlog hK0 hc₁ hD hQ ℓ a1 a2
    · have a2' : m₂ < 1 := not_le.1 a2
      have hS : min (min m₁ m₂) 1 = m₂ := by
        rw [min_eq_right (by linarith : m₂ ≤ m₁), min_eq_left a2'.le]
      refine fin (2 * (Real.sqrt (Qm β 1) * K₀ * ((1 + 2 * b + c₁) * Real.exp (c₁ / 2)))) (by linarith) ?_
      rw [hS]
      exact loc_caseC hβ0 hβ1 hb hlog hK₀ hc₁ hG hQ ℓ a1 h₂ a2'.le
  · have a1' : m₁ < 1 := not_le.1 a1
    by_cases a2 : 1 ≤ m₂
    · have hS : min (min m₁ m₂) 1 = m₁ := by
        rw [min_eq_left (by linarith : m₁ ≤ m₂), min_eq_left a1'.le]
      refine fin (Real.sqrt (Qm β 1) * K₀ * ((1 + 2 * b + (c₁ + 2 * b)) * Real.exp ((c₁ + 2 * b) / 2))) (by linarith) ?_
      rw [hS]
      exact loc_caseB hβ0 hβ1 hb hlog hK₀ hc₁ hG hQ ℓ h₁ a1'.le a2
    · have a2' : m₂ < 1 := not_le.1 a2
      have hS : min (min m₁ m₂) 1 = min m₁ m₂ := min_eq_left ((min_le_left _ _).trans a1'.le)
      refine fin (Qm β 1 * sPow β 2 * Real.exp b) (by linarith) ?_
      rw [hS]
      exact loc_caseD hβ0 hβ1 hb hlog ℓ h₁ a1'.le h₂ a2'.le


private lemma loc_logQ_b {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ b c₁ : ℝ, 0 < b ∧ Real.log β = -b ∧ 0 ≤ c₁ ∧
      ∀ m : ℝ, 1 ≤ m → |Real.log (Qm β m) - 2 * b * m| ≤ c₁ := by
  obtain ⟨CQ, hCQ⟩ := lem_app_pl_weights_iii_logQ hβ0 hβ1
  have hb : 0 < -Real.log β := neg_pos.2 (Real.log_neg hβ0 hβ1)
  have habs : |Real.log β| = -Real.log β := abs_of_neg (Real.log_neg hβ0 hβ1)
  refine ⟨-Real.log β, |CQ|, hb, by ring, abs_nonneg _, fun m hm => ?_⟩
  have := hCQ m hm
  rw [habs] at this
  exact this.trans (le_abs_self CQ)

private lemma loc_M_bd {β b c₁ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hb : 0 < b)
    (hlog : Real.log β = -b) (hc₁ : 0 ≤ c₁)
    (hQ : ∀ m : ℝ, 1 ≤ m → |Real.log (Qm β m) - 2 * b * m| ≤ c₁) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (ℓ : ℕ) (m : ℝ), 0 < m →
      rW (emaW β) (β ^ (2 * ℓ) * Qm β m) ≤ max (m - ℓ) 0 + C' := by
  obtain ⟨A, hA, hr⟩ := loc_r_log hβ0 hβ1
  have hB : -Real.log β = b := by rw [hlog]; ring
  rw [hB] at hr
  obtain ⟨hqs, -⟩ := vk_Qm hβ0 hβ1 (zero_lt_one : (0 : ℝ) < 1)
  have hs2 := loc_sPow_nonneg β
  refine ⟨sPow β 2 * Qm β 1 + sPow β 2 + A + c₁ / (2 * b), by positivity, fun ℓ m hm => ?_⟩
  obtain ⟨hq, -⟩ := vk_Qm hβ0 hβ1 hm
  have hp : 0 < β ^ (2 * ℓ) * Qm β m := by positivity
  have hβl : β ^ (2 * ℓ) ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
  have hmax : 0 ≤ max (m - ℓ) 0 := le_max_right _ _
  have hmax2 : m - ℓ ≤ max (m - ℓ) 0 := le_max_left _ _
  have hrp := loc_r_le hβ0 hβ1 hp.le
  have hc2 : 0 ≤ c₁ / (2 * b) := by positivity
  by_cases hm1 : m < 1
  · have hQle := vk_Qm_le hβ0 hβ1 hm hm1.le
    have h1 : β ^ (2 * ℓ) * Qm β m ≤ Qm β 1 := by
      calc _ ≤ 1 * Qm β m := mul_le_mul_of_nonneg_right hβl hq.le
        _ ≤ Qm β 1 * m := by linarith
        _ ≤ Qm β 1 * 1 := mul_le_mul_of_nonneg_left hm1.le hqs.le
        _ = _ := mul_one _
    have h2 := mul_le_mul_of_nonneg_left h1 hs2
    nlinarith
  · push_neg at hm1
    by_cases hp1 : β ^ (2 * ℓ) * Qm β m < 1
    · have h2 := mul_le_mul_of_nonneg_left hp1.le hs2
      nlinarith [mul_nonneg hs2 hqs.le]
    · push_neg at hp1
      have h1 := hr _ hp1
      rw [loc_logp hlog hβ0 ℓ hq] at h1
      have e2 := (abs_le.1 (hQ m hm1)).2
      have h3 : 1 / (2 * b) * (-(2 * b * ℓ) + Real.log (Qm β m)) ≤ (m - ℓ) + c₁ / (2 * b) := by
        have : 1 / (2 * b) * (-(2 * b * ℓ) + Real.log (Qm β m)) ≤
            1 / (2 * b) * (-(2 * b * ℓ) + (2 * b * m + c₁)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        calc _ ≤ _ := this
          _ = (m - ℓ) + c₁ / (2 * b) := by field_simp; ring
      nlinarith [mul_nonneg hs2 hqs.le]

private lemma loc_M_small {β b c₁ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hb : 0 < b)
    (hlog : Real.log β = -b) (hc₁ : 0 ≤ c₁)
    (hQ : ∀ m : ℝ, 1 ≤ m → |Real.log (Qm β m) - 2 * b * m| ≤ c₁) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (ℓ : ℕ) (m : ℝ), 0 < m → 2 * m ≤ ℓ →
      rW (emaW β) (β ^ (2 * ℓ) * Qm β m) ≤ C₁ * m * β ^ ℓ := by
  obtain ⟨hqs, -⟩ := vk_Qm hβ0 hβ1 (zero_lt_one : (0 : ℝ) < 1)
  have hs2 := loc_sPow_nonneg β
  refine ⟨sPow β 2 * (Qm β 1 + Real.exp c₁), by positivity, fun ℓ m hm hmℓ => ?_⟩
  obtain ⟨hq, -⟩ := vk_Qm hβ0 hβ1 hm
  have hp : 0 < β ^ (2 * ℓ) * Qm β m := by positivity
  have hrp := loc_r_le hβ0 hβ1 hp.le
  have hbl : 0 ≤ β ^ ℓ := pow_nonneg hβ0.le ℓ
  have hbl1 : β ^ ℓ ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
  have hsq : β ^ (2 * ℓ) = β ^ ℓ * β ^ ℓ := by rw [two_mul, pow_add]
  by_cases hm1 : m < 1
  · have hQle := vk_Qm_le hβ0 hβ1 hm hm1.le
    have h1 : β ^ (2 * ℓ) * Qm β m ≤ β ^ ℓ * (Qm β 1 * m) := by
      rw [hsq]
      calc _ = β ^ ℓ * (β ^ ℓ * Qm β m) := by ring
        _ ≤ β ^ ℓ * (1 * Qm β m) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbl1 hq.le) hbl
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hbl
    have h2 := mul_le_mul_of_nonneg_left h1 hs2
    have h3 : 0 ≤ sPow β 2 * (Real.exp c₁ * (m * β ^ ℓ)) := by positivity
    nlinarith
  · push_neg at hm1
    have hL := (abs_le.1 (hQ m hm1)).2
    have hQe : Qm β m ≤ Real.exp (b * ℓ + c₁) := by
      calc Qm β m = Real.exp (Real.log (Qm β m)) := (Real.exp_log hq).symm
        _ ≤ _ := Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left hmℓ hb.le])
    have h2l : β ^ (2 * ℓ) = Real.exp (-(b * (2 * ℓ : ℕ))) := loc_beta_pow hlog hβ0 (2 * ℓ)
    have h1 : β ^ (2 * ℓ) * Qm β m ≤ Real.exp c₁ * β ^ ℓ := by
      rw [h2l, loc_beta_pow hlog hβ0 ℓ]
      calc _ ≤ Real.exp (-(b * (2 * ℓ : ℕ))) * Real.exp (b * ℓ + c₁) :=
            mul_le_mul_of_nonneg_left hQe (Real.exp_pos _).le
        _ = _ := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            push_cast
            ring
    have h2 := mul_le_mul_of_nonneg_left h1 hs2
    have h3 : Real.exp c₁ * β ^ ℓ ≤ Real.exp c₁ * (m * β ^ ℓ) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      nlinarith
    have h4 := mul_le_mul_of_nonneg_left h3 hs2
    have h5 : 0 ≤ sPow β 2 * (Qm β 1 * (m * β ^ ℓ)) := by positivity
    nlinarith

private lemma loc_D_sup {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ (ℓ : ℕ) (m₁ m₂ : ℝ), 0 < m₁ → 0 < m₂ →
      DLagNat β (Qm β m₁) (Qm β m₂) ℓ ≤ C₂ := by
  obtain ⟨C, hC0, hC⟩ := loc_D_bound hβ0 hβ1
  have hb : 0 < |Real.log β| := abs_pos.2 (Real.log_ne_zero_of_pos_of_ne_one hβ0 hβ1.ne)
  refine ⟨C * (1 + 1 / |Real.log β|), by positivity, fun ℓ m₁ m₂ h₁ h₂ => ?_⟩
  refine (hC ℓ m₁ m₂ h₁ h₂).trans ?_
  obtain ⟨b, hbd⟩ : ∃ b : ℝ, b = |Real.log β| := ⟨_, rfl⟩
  obtain ⟨x, hxd⟩ : ∃ x : ℝ, x = |m₁ - m₂ + ℓ| := ⟨_, rfl⟩
  rw [← hbd, ← hxd]
  rw [← hbd] at hb
  have hx : 0 ≤ x := by rw [hxd]; exact abs_nonneg _
  have hs : Real.sqrt (min (min m₁ m₂) 1) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact min_le_right _ _
  have hE : (1 + b * x) * Real.exp (-b * x) ≤ 1 := by
    have := Real.add_one_le_exp (b * x)
    calc _ ≤ Real.exp (b * x) * Real.exp (-b * x) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = 1 := by
          rw [← Real.exp_add]
          simp
  have h1 : 1 + x ≤ (1 + b * x) * (1 + 1 / b) := by
    have e : (1 + b * x) * (1 + 1 / b) = 1 + 1 / b + b * x + x := by
      field_simp
      ring
    have : 0 ≤ 1 / b := by positivity
    have : 0 ≤ b * x := mul_nonneg hb.le hx
    linarith
  have hE0 := (Real.exp_pos (-b * x)).le
  calc C * Real.sqrt (min (min m₁ m₂) 1) * (1 + x) * Real.exp (-b * x)
      ≤ C * 1 * (1 + x) * Real.exp (-b * x) := by gcongr
    _ ≤ C * 1 * ((1 + b * x) * (1 + 1 / b)) * Real.exp (-b * x) := by gcongr
    _ = C * (1 + 1 / b) * ((1 + b * x) * Real.exp (-b * x)) := by ring
    _ ≤ C * (1 + 1 / b) * 1 := by
        apply mul_le_mul_of_nonneg_left hE
        positivity
    _ = C * (1 + 1 / b) := mul_one _

private lemma loc_T_bd2 {N B : ℕ} {μ : Fin N → ℝ} (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) {m₁ m₂ : ℝ} (hm₁ : m₁ ∈ Ioo 0 (gammaOf N B))
    (hm₂ : m₂ ∈ Ioo 0 (gammaOf N B)) :
    0 ≤ TNpart B μ m₁ m₂ ∧ TNpart B μ m₁ m₂ ≤ m₁ ∧ TNpart B μ m₁ m₂ ≤ m₂ := by
  rcases le_total m₁ m₂ with h | h
  · obtain ⟨h0, h1⟩ := vk_T_bd hB hN hpos hm₁ hm₂ h
    exact ⟨h0, h1, h1.trans h⟩
  · obtain ⟨h0, h1⟩ := vk_T_bd hB hN hpos hm₂ hm₁ h
    rw [vk_TN_comm] at h0 h1
    exact ⟨h0, h1.trans h, h1⟩

private lemma loc_TD {T D C₂ m₁ m₂ : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ m₁) (hT2 : T ≤ m₂)
    (hD0 : 0 ≤ D) (hDC : D ≤ C₂) (hD2 : D ^ 2 ≤ m₁ * m₂) (hC0 : 0 ≤ C₂) (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) : T * D ^ 2 ≤ C₂ * (m₁ * m₂) := by
  have hDC2 : D ^ 2 ≤ C₂ ^ 2 := pow_le_pow_left₀ hD0 hDC 2
  rcases le_total m₁ m₂ with h | h
  · have h1 : D ^ 2 ≤ C₂ * m₂ := by
      rcases le_total m₁ C₂ with h' | h'
      · calc _ ≤ m₁ * m₂ := hD2
          _ ≤ C₂ * m₂ := mul_le_mul_of_nonneg_right h' hm₂.le
      · calc _ ≤ C₂ ^ 2 := hDC2
          _ = C₂ * C₂ := sq C₂
          _ ≤ C₂ * m₂ := mul_le_mul_of_nonneg_left (h'.trans h) hC0
    calc T * D ^ 2 ≤ m₁ * (C₂ * m₂) := mul_le_mul hT1 h1 (sq_nonneg D) hm₁.le
      _ = _ := by ring
  · have h1 : D ^ 2 ≤ C₂ * m₁ := by
      rcases le_total m₂ C₂ with h' | h'
      · calc _ ≤ m₁ * m₂ := hD2
          _ = m₂ * m₁ := mul_comm _ _
          _ ≤ C₂ * m₁ := mul_le_mul_of_nonneg_right h' hm₁.le
      · calc _ ≤ C₂ ^ 2 := hDC2
          _ = C₂ * C₂ := sq C₂
          _ ≤ C₂ * m₁ := mul_le_mul_of_nonneg_left (h'.trans h) hC0
    calc T * D ^ 2 ≤ m₂ * (C₂ * m₁) := mul_le_mul hT2 h1 (sq_nonneg D) hm₂.le
      _ = _ := by ring

/-- `lem:app-pl-localization`, part (i) (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Localization of the lag kernel]\label{lem:app-pl-localization}
\begin{enumerate}[label=(\roman*)]
\item For $\ell\ge0$, with $t\defeq\log(\bmom^{2\ell}q_2/q_1)$,
\[
\mathsf D_\ell(m_1,m_2)=\frac{r_\bmom(q_1e^t)-r_\bmom(q_1)}{2\sinh(t/2)},\]
\[
\mathsf D_\ell\le C\min(m_1,m_2,1)^{1/2}\big(1+\abs{m_1-m_2+\ell}\big)e^{-\abs{\log\bmom}\abs{m_1-m_2+\ell}} .
\]
\item For every $\tau_0>0$ there is $c>0$ such that $\Delta^N_\ell\ge c$ for all $\ell\ge\tau_0\gamma$, all
$m_1,m_2\in(0,\gamma)$ and all large $\gamma$.
\item Let $n\to\infty$ with $\gamma/n\to\rho_0\in(0,\infty]$, and let $\ell$ be integers with $\ell/n\to\tau>0$. For every
continuous $\varphi$ with compact support in $(0,\rho_0)^2$,
\[
\int\!\!\int\varphi\Big(\frac{m_1}n,\frac{m_2}n\Big)\frac{\mathsf D_\ell(m_1,m_2)}{\pi^2n\,E(m_1)E(m_2)}\,\dif m_1\,\dif m_2\longrightarrow\int\varphi(r,r+\tau)\,\dif r .
\]
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_localization_i {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∀ (ℓ : ℕ) (m₁ m₂ : ℝ), 0 < m₁ → 0 < m₂ →
      β ^ (2 * ℓ) * Qm β m₂ = Qm β m₁ →
      DLagNat β (Qm β m₁) (Qm β m₂) ℓ = Efun β m₁) ∧
    (∀ (ℓ : ℕ) (m₁ m₂ : ℝ), 0 < m₁ → 0 < m₂ →
      Real.log (β ^ (2 * ℓ) * Qm β m₂ / Qm β m₁) ≠ 0 →
      DLagNat β (Qm β m₁) (Qm β m₂) ℓ =
        (rW (emaW β) (Qm β m₁ * Real.exp (Real.log (β ^ (2 * ℓ) * Qm β m₂ / Qm β m₁))) -
            rW (emaW β) (Qm β m₁)) /
          (2 * Real.sinh (Real.log (β ^ (2 * ℓ) * Qm β m₂ / Qm β m₁) / 2))) ∧
    ∃ C : ℝ, ∀ (ℓ : ℕ) (m₁ m₂ : ℝ), 0 < m₁ → 0 < m₂ →
      DLagNat β (Qm β m₁) (Qm β m₂) ℓ ≤
        C * Real.sqrt (min (min m₁ m₂) 1) * (1 + |m₁ - m₂ + ℓ|) *
          Real.exp (-|Real.log β| * |m₁ - m₂ + ℓ|) := by
  refine ⟨fun ℓ m₁ m₂ h₁ h₂ h => loc_coincident hβ0 hβ1 ℓ h₁ h₂ h,
    fun ℓ m₁ m₂ h₁ h₂ ht => loc_guarded hβ0 hβ1 ℓ h₁ h₂ ht, ?_⟩
  obtain ⟨C, -, hC⟩ := loc_D_bound hβ0 hβ1
  exact ⟨C, hC⟩

/-- `lem:app-pl-localization`, part (ii) (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Localization of the lag kernel]\label{lem:app-pl-localization}
\begin{enumerate}[label=(\roman*)]
\item For $\ell\ge0$, with $t\defeq\log(\bmom^{2\ell}q_2/q_1)$,
\[
\mathsf D_\ell(m_1,m_2)=\frac{r_\bmom(q_1e^t)-r_\bmom(q_1)}{2\sinh(t/2)},\]
\[
\mathsf D_\ell\le C\min(m_1,m_2,1)^{1/2}\big(1+\abs{m_1-m_2+\ell}\big)e^{-\abs{\log\bmom}\abs{m_1-m_2+\ell}} .
\]
\item For every $\tau_0>0$ there is $c>0$ such that $\Delta^N_\ell\ge c$ for all $\ell\ge\tau_0\gamma$, all
$m_1,m_2\in(0,\gamma)$ and all large $\gamma$.
\item Let $n\to\infty$ with $\gamma/n\to\rho_0\in(0,\infty]$, and let $\ell$ be integers with $\ell/n\to\tau>0$. For every
continuous $\varphi$ with compact support in $(0,\rho_0)^2$,
\[
\int\!\!\int\varphi\Big(\frac{m_1}n,\frac{m_2}n\Big)\frac{\mathsf D_\ell(m_1,m_2)}{\pi^2n\,E(m_1)E(m_2)}\,\dif m_1\,\dif m_2\longrightarrow\int\varphi(r,r+\tau)\,\dif r .
\]
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_localization_ii {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ τ₀ : ℝ, 0 < τ₀ → ∃ κ : ℝ, 0 < κ ∧ ∃ γ₀ : ℝ,
      ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → γ₀ ≤ gammaOf N B →
        ∀ ℓ : ℤ, τ₀ * gammaOf N B ≤ ℓ →
          ∀ m₁ m₂ : ℝ, m₁ ∈ Ioo 0 (gammaOf N B) → m₂ ∈ Ioo 0 (gammaOf N B) →
            κ ≤ deltaN β B (plSpec α c N) ℓ m₁ m₂ := by
  intro τ₀ hτ₀
  obtain ⟨b, c₁, hb, hlog, hc₁, hQ⟩ := loc_logQ_b hβ0 hβ1
  obtain ⟨C', hC'0, hMbd⟩ := loc_M_bd hβ0 hβ1 hb hlog hc₁ hQ
  obtain ⟨C₁, hC₁0, hMsm⟩ := loc_M_small hβ0 hβ1 hb hlog hc₁ hQ
  obtain ⟨C₂, hC₂0, hDsup⟩ := loc_D_sup hβ0 hβ1
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = min τ₀ 1 := ⟨_, rfl⟩
  have hτ : 0 < τ := by rw [hτdef]; exact lt_min hτ₀ one_pos
  have hτ1 : τ ≤ 1 := by rw [hτdef]; exact min_le_right _ _
  have hττ : τ ≤ τ₀ := by rw [hτdef]; exact min_le_left _ _
  refine ⟨τ ^ 2 / 8, by positivity,
    max (max (4 * C' / τ ^ 2) (2 * C₁ / (b * τ))) (max (8 * C₂ / τ ^ 2) 1), ?_⟩
  intro N B c hN hB hc hγ ℓ hℓ m₁ m₂ hm₁ hm₂
  have hpos := vk_pos_plSpec (α := α) hc N
  have hγ1 : 4 * C' / τ ^ 2 ≤ gammaOf N B := ((le_max_left _ _).trans (le_max_left _ _)).trans hγ
  have hγ2 : 2 * C₁ / (b * τ) ≤ gammaOf N B :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hγ
  have hγ3 : 8 * C₂ / τ ^ 2 ≤ gammaOf N B :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hγ
  have hγ4 : 1 ≤ gammaOf N B := ((le_max_right _ _).trans (le_max_right _ _)).trans hγ
  have hγpos : 0 < gammaOf N B := by linarith
  have hℓτ : τ * gammaOf N B ≤ (ℓ : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_right hττ hγpos.le) hℓ
  have hℓ0 : 0 ≤ ℓ := by
    have : (0 : ℝ) ≤ (ℓ : ℝ) := le_trans (by positivity) hℓτ
    exact_mod_cast this
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hℓ0
  have hn : τ * gammaOf N B ≤ (n : ℝ) := by simpa using hℓτ
  obtain ⟨hq1, -⟩ := vk_Qm hβ0 hβ1 hm₁.1
  obtain ⟨hq2, -⟩ := vk_Qm hβ0 hβ1 hm₂.1
  obtain ⟨hM0, hMmin, hD2⟩ := vk_det_i hβ0 hβ1 hm₁.1 hm₂.1 (n : ℤ)
  have hMdef : MLag β (Qm β m₁) (Qm β m₂) (n : ℤ) = MLagNat β (Qm β m₁) (Qm β m₂) n := by
    simp [MLag]
  have hDdef : DLag β (Qm β m₁) (Qm β m₂) (n : ℤ) = DLagNat β (Qm β m₁) (Qm β m₂) n := by
    simp [DLag]
  rw [hMdef] at hM0 hMmin hD2
  rw [hDdef] at hD2
  have hMr := loc_M_le_r hβ0 hβ1 n hq1.le hq2.le
  have hMθ : MLagNat β (Qm β m₁) (Qm β m₂) n ≤ (1 - τ / 2) * m₂ := by
    refine hMr.trans ?_
    by_cases hc2 : (n : ℝ) ≤ 2 * m₂
    · have h1 := hMbd n m₂ hm₂.1
      have h2 : max (m₂ - n) 0 ≤ (1 - τ) * m₂ := by
        refine max_le ?_ (mul_nonneg (by linarith) hm₂.1.le)
        have h5 : τ * m₂ ≤ τ * gammaOf N B := mul_le_mul_of_nonneg_left hm₂.2.le hτ.le
        have e : (1 - τ) * m₂ = m₂ - τ * m₂ := by ring
        linarith
      have h3 : C' ≤ τ / 2 * m₂ := by
        have h4 : 4 * C' ≤ gammaOf N B * τ ^ 2 := by
          rwa [div_le_iff₀ (by positivity)] at hγ1
        have h5 : τ * (τ * gammaOf N B) ≤ τ * (2 * m₂) :=
          mul_le_mul_of_nonneg_left (hn.trans hc2) hτ.le
        have e : τ * (τ * gammaOf N B) = gammaOf N B * τ ^ 2 := by ring
        linarith
      linarith
    · push_neg at hc2
      have h1 := hMsm n m₂ hm₂.1 hc2.le
      have h2 : 2 * C₁ ≤ b * n := by
        have h4 : 2 * C₁ ≤ gammaOf N B * (b * τ) := by
          rwa [div_le_iff₀ (by positivity)] at hγ2
        have h5 : b * (τ * gammaOf N B) ≤ b * n := mul_le_mul_of_nonneg_left hn hb.le
        have e : gammaOf N B * (b * τ) = b * (τ * gammaOf N B) := by ring
        linarith
      have hβn : 0 ≤ β ^ n := pow_nonneg hβ0.le n
      have h3 : (1 + b * n) * β ^ n ≤ 1 := by
        rw [loc_beta_pow hlog hβ0]
        have := Real.add_one_le_exp (b * n)
        calc _ ≤ Real.exp (b * n) * Real.exp (-(b * n)) :=
              mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
          _ = 1 := by rw [← Real.exp_add]; simp
      have h5 : C₁ * β ^ n ≤ 1 / 2 := by
        have := mul_le_mul_of_nonneg_right h2 hβn
        have e : (1 + b * n) * β ^ n = β ^ n + b * n * β ^ n := by ring
        linarith
      have h6 : C₁ * m₂ * β ^ n ≤ m₂ / 2 := by
        calc _ = m₂ * (C₁ * β ^ n) := by ring
          _ ≤ m₂ * (1 / 2) := mul_le_mul_of_nonneg_left h5 hm₂.1.le
          _ = _ := by ring
      have h7 : m₂ / 2 ≤ (1 - τ / 2) * m₂ := by
        have := mul_nonneg (sub_nonneg.2 hτ1) hm₂.1.le
        have e : (1 - τ) * m₂ = m₂ - τ * m₂ := by ring
        have e2 : (1 - τ / 2) * m₂ = m₂ - τ * m₂ / 2 := by ring
        linarith
      exact h1.trans (h6.trans h7)
  obtain ⟨hD0, -⟩ := loc_D_drop hβ0 hβ1 n hq1.le hq2.le
  have hDle := hDsup n m₁ m₂ hm₁.1 hm₂.1
  obtain ⟨hT0, hT1, hT2⟩ := loc_T_bd2 hB hN hpos hm₁ hm₂
  unfold deltaN
  rw [hMdef, hDdef]
  have hMm1 : MLagNat β (Qm β m₁) (Qm β m₂) n ≤ m₁ := hMmin.trans (min_le_left _ _)
  have hMm2 : MLagNat β (Qm β m₁) (Qm β m₂) n ≤ m₂ := hMmin.trans (min_le_right _ _)
  have hDm : DLagNat β (Qm β m₁) (Qm β m₂) n ^ 2 ≤ m₁ * m₂ := by
    refine hD2.trans ?_
    have a := mul_le_mul_of_nonneg_left hMm1 hM0
    have b' := mul_nonneg hM0 hm₂.1.le
    have e : (m₁ - MLagNat β (Qm β m₁) (Qm β m₂) n) * (m₂ - MLagNat β (Qm β m₁) (Qm β m₂) n) =
        m₁ * m₂ - MLagNat β (Qm β m₁) (Qm β m₂) n * m₁ - MLagNat β (Qm β m₁) (Qm β m₂) n * m₂ +
          MLagNat β (Qm β m₁) (Qm β m₂) n * MLagNat β (Qm β m₁) (Qm β m₂) n := by ring
    linarith
  have hTD := loc_TD hT0 hT1 hT2 hD0 hDle hDm hC₂0 hm₁.1 hm₂.1
  generalize MLagNat β (Qm β m₁) (Qm β m₂) n = M at hM0 hMmin hMθ ⊢
  generalize DLagNat β (Qm β m₁) (Qm β m₂) n = D at hTD ⊢
  generalize TNpart B (plSpec α c N) m₁ m₂ = T at hT0 hT1 hT2 hTD ⊢
  have hm1 := hm₁.1
  have hm2 := hm₂.1
  have hX1 : T * M / (m₁ * m₂) ≤ 1 - τ / 2 := by
    rw [div_le_iff₀ (by positivity)]
    calc T * M ≤ m₁ * M := mul_le_mul_of_nonneg_right hT1 hM0
      _ ≤ m₁ * ((1 - τ / 2) * m₂) := mul_le_mul_of_nonneg_left hMθ hm1.le
      _ = (1 - τ / 2) * (m₁ * m₂) := by ring
  have hX2 : M / gammaOf N B ≤ 1 - τ / 2 := by
    rw [div_le_iff₀ hγpos]
    calc M ≤ (1 - τ / 2) * m₂ := hMθ
      _ ≤ (1 - τ / 2) * gammaOf N B :=
          mul_le_mul_of_nonneg_left hm₂.2.le (by linarith)
  have hprod : τ / 2 * (τ / 2) ≤
      (1 - T * M / (m₁ * m₂)) * (1 - M / gammaOf N B) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hX3 : T * D ^ 2 / (gammaOf N B * m₁ * m₂) ≤ τ ^ 2 / 8 := by
    rw [div_le_iff₀ (by positivity)]
    have h8 : 8 * C₂ ≤ gammaOf N B * τ ^ 2 := by
      rwa [div_le_iff₀ (by positivity)] at hγ3
    have := mul_le_mul_of_nonneg_right h8 (mul_pos hm1 hm2).le
    have e : τ ^ 2 / 8 * (gammaOf N B * m₁ * m₂) = gammaOf N B * τ ^ 2 * (m₁ * m₂) / 8 := by ring
    rw [e]
    linarith
  have e : τ / 2 * (τ / 2) = τ ^ 2 / 4 := by ring
  linarith

private lemma lp_odd_sum : HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1 / 2) ^ 2) (Real.pi ^ 2 / 2) := by
  have hz := hasSum_zeta_two
  have he : HasSum (fun k : ℕ => (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 24) := by
    have h1 := hz.mul_left (1 / 4)
    have e : (fun k : ℕ => (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 2) =
        fun k : ℕ => 1 / 4 * ((1 : ℝ) / (k : ℝ) ^ 2) := by
      funext k
      push_cast
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · have : (k : ℝ) ≠ 0 := by positivity
        field_simp
        norm_num
    rw [e]
    have e2 : Real.pi ^ 2 / 24 = 1 / 4 * (Real.pi ^ 2 / 6) := by ring
    rw [e2]
    exact h1
  have hs : Summable (fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2) :=
    hz.summable.comp_injective (i := fun k : ℕ => 2 * k + 1) (fun a b h => by simpa using h)
  have ho := hs.hasSum
  have htot : HasSum (fun n : ℕ => (1:ℝ)/(n:ℝ)^2)
      (Real.pi ^ 2 / 24 + ∑' k : ℕ, (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2) :=
    HasSum.even_add_odd (f := fun n : ℕ => (1:ℝ)/(n:ℝ)^2) he ho
  have hb := htot.unique hz
  have h8v : (∑' k : ℕ, (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2) = Real.pi ^ 2 / 8 := by linarith
  have h8 : HasSum (fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 8) := by
    rw [← h8v]; exact ho
  have h4 := h8.mul_left 4
  have e : (fun k : ℕ => 1 / ((k : ℝ) + 1 / 2) ^ 2) =
      fun k : ℕ => 4 * ((1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
    funext k
    push_cast
    have : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    have : ((k : ℝ) + 1 / 2) ≠ 0 := by positivity
    field_simp
    ring
  rw [e]
  have e2 : Real.pi ^ 2 / 2 = 4 * (Real.pi ^ 2 / 8) := by ring
  rw [e2]
  exact h4


private lemma lp_integrable_abs {f : ℝ → ℝ} (hf : IntegrableOn (fun x => f |x|) (Ioi (0 : ℝ))) :
    Integrable (fun x => f |x|) := by
  have int_Iic : IntegrableOn (fun x ↦ f |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf
  have := int_Iic.union hf
  rwa [Iic_union_Ioi, integrableOn_univ] at this

private lemma lp_B_int : Integrable (fun t : ℝ => (1 + |t|) * Real.exp (-|t| / 2)) := by
  refine lp_integrable_abs (f := fun x => (1 + x) * Real.exp (-x / 2)) ?_
  have h1 : IntegrableOn (fun x : ℝ => Real.exp (-(1/2 : ℝ) * x)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 (by norm_num)
  have h2 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := 1/2) (by norm_num)
    (by norm_num) (by norm_num)
  have h3 : IntegrableOn (fun x : ℝ => x * Real.exp (-(1/2 : ℝ) * x)) (Ioi 0) := by
    refine h2.congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp
  have h4 := h1.add h3
  refine h4.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx' : |x| = x := abs_of_pos hx
  simp only [hx']
  have : -x / 2 = -(1/2 : ℝ) * x := by ring
  rw [this]
  simp only [Pi.add_apply]
  ring


private lemma lp_w_series {t : ℝ} (ht : 0 < t) :
    t / (2 * Real.sinh (t / 2)) = ∑' k : ℕ, t * Real.exp (-(((k : ℝ) + 1 / 2) * t)) := by
  have hr0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hr1 : Real.exp (-t) < 1 := by
    have := Real.exp_lt_exp.2 (show -t < 0 by linarith)
    simpa using this
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (t * Real.exp (-t / 2))
  have e : (fun k : ℕ => t * Real.exp (-(((k : ℝ) + 1 / 2) * t))) =
      fun k : ℕ => t * Real.exp (-t / 2) * Real.exp (-t) ^ k := by
    funext k
    rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [e, hg.tsum_eq]
  have h1 : 1 - Real.exp (-t) ≠ 0 := by linarith
  have h2 : Real.exp (-t) = Real.exp (-t / 2) * Real.exp (-t / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.sinh (t / 2) = (Real.exp (t / 2) - Real.exp (-(t / 2))) / 2 := Real.sinh_eq _
  have h4 : Real.exp (t / 2) = (Real.exp (-t / 2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  have hE : 0 < Real.exp (-t / 2) := Real.exp_pos _
  have h5 : Real.exp (-(t / 2)) = Real.exp (-t / 2) := by congr 1; ring
  rw [h3, h4, h5, h2]
  rw [h2] at h1
  field_simp

private lemma lp_w_Ioi : ∫ t in Ioi (0 : ℝ), t / (2 * Real.sinh (t / 2)) = Real.pi ^ 2 / 2 := by
  have hF : ∀ k : ℕ, IntegrableOn (fun t : ℝ => t * Real.exp (-(((k : ℝ) + 1 / 2) * t))) (Ioi 0) := by
    intro k
    have h2 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := (k : ℝ) + 1 / 2)
      (by norm_num) (by norm_num) (by positivity)
    refine h2.congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]
    rw [neg_mul]
  have hval : ∀ k : ℕ, ∫ t in Ioi (0 : ℝ), t * Real.exp (-(((k : ℝ) + 1 / 2) * t)) =
      1 / ((k : ℝ) + 1 / 2) ^ 2 := by
    intro k
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := (k : ℝ) + 1 / 2) (by norm_num)
      (by positivity)
    have e : ∫ t in Ioi (0 : ℝ), t * Real.exp (-(((k : ℝ) + 1 / 2) * t)) =
        ∫ t in Ioi (0 : ℝ), t ^ ((2 : ℝ) - 1) * Real.exp (-(((k : ℝ) + 1 / 2) * t)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      norm_num
    rw [e, this]
    have : Real.Gamma 2 = 1 := by
      have := Real.Gamma_nat_eq_factorial 1
      simpa using this
    rw [this]
    have e2 : (1 / ((k : ℝ) + 1 / 2)) ^ (2 : ℝ) = 1 / ((k : ℝ) + 1 / 2) ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div_pow]
    rw [e2]; ring
  have hnorm : ∀ k : ℕ, ∫ t in Ioi (0 : ℝ), ‖t * Real.exp (-(((k : ℝ) + 1 / 2) * t))‖ =
      1 / ((k : ℝ) + 1 / 2) ^ 2 := by
    intro k
    rw [← hval k]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact mul_nonneg (le_of_lt hx) (Real.exp_pos _).le
  have hsum : Summable (fun k : ℕ => ∫ t in Ioi (0 : ℝ), ‖t * Real.exp (-(((k : ℝ) + 1 / 2) * t))‖) := by
    simp_rw [hnorm]
    exact lp_odd_sum.summable
  have := integral_tsum_of_summable_integral_norm (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (k : ℕ) (t : ℝ) => t * Real.exp (-(((k : ℝ) + 1 / 2) * t))) hF hsum
  have e3 : ∫ t in Ioi (0 : ℝ), t / (2 * Real.sinh (t / 2)) =
      ∫ t in Ioi (0 : ℝ), ∑' k : ℕ, t * Real.exp (-(((k : ℝ) + 1 / 2) * t)) :=
    setIntegral_congr_fun measurableSet_Ioi (fun x hx => lp_w_series hx)
  rw [e3, ← this]
  simp_rw [hval]
  exact lp_odd_sum.tsum_eq

private lemma lp_w_even (t : ℝ) :
    t / (2 * Real.sinh (t / 2)) = |t| / (2 * Real.sinh (|t| / 2)) := by
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, show -t / 2 = -(t / 2) by ring, Real.sinh_neg]
    rw [mul_neg, div_neg, neg_div, neg_neg]

private lemma lp_w_val : ∫ t : ℝ, t / (2 * Real.sinh (t / 2)) = Real.pi ^ 2 := by
  have : (fun t : ℝ => t / (2 * Real.sinh (t / 2))) =
      fun t => (fun x : ℝ => x / (2 * Real.sinh (x / 2))) |t| := funext lp_w_even
  rw [this]
  have h2 := integral_comp_abs (f := fun x : ℝ => x / (2 * Real.sinh (x / 2)))
  rw [h2, lp_w_Ioi]
  ring



private lemma lp_div_sinh {K N t : ℝ} (hK : 0 ≤ K) (hN : |N| ≤ K * |t|) :
    |N / (2 * Real.sinh (t / 2))| ≤ K * ((1 + |t|) * Real.exp (-|t| / 2)) := by
  by_cases ht : t = 0
  · subst ht
    simp only [zero_div, Real.sinh_zero, mul_zero, div_zero, abs_zero, abs_zero, neg_zero,
      Real.exp_zero, add_zero, mul_one]
    exact hK
  · have h := loc_sinh_abs ht
    have hs : 0 < |2 * Real.sinh (t / 2)| := by
      rcases le_or_gt (|2 * Real.sinh (t / 2)|) 0 with h0 | h0
      · exfalso
        have : |2 * Real.sinh (t / 2)| = 0 := le_antisymm h0 (abs_nonneg _)
        rw [this, mul_zero] at h
        exact ht (abs_nonpos_iff.1 h)
      · exact h0
    rw [abs_div, div_le_iff₀ hs]
    calc |N| ≤ K * |t| := hN
      _ ≤ K * ((1 + |t|) * Real.exp (-|t| / 2) * |2 * Real.sinh (t / 2)|) :=
          mul_le_mul_of_nonneg_left h hK
      _ = _ := by ring

private lemma lp_R_deriv {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (u : ℝ) :
    HasDerivAt (fun u => rW (emaW β) (Real.exp u))
      (Efun β (rW (emaW β) (Real.exp u))) u := by
  have hw := vk_weightSeq hβ0 hβ1
  have h1 := (lem_app_de_scalar_iii hw).2.2.2.1 (Real.exp u) (Real.exp_pos u)
  have h2 := h1.differentiableAt.hasDerivAt.comp u (Real.hasDerivAt_exp u)
  have e : Efun β (rW (emaW β) (Real.exp u)) = deriv (rW (emaW β)) (Real.exp u) * Real.exp u := by
    unfold Efun
    rw [(loc_Qm_r hβ0 hβ1 (Real.exp_pos u)).2, mul_comm]
  rw [e]
  exact h2

private lemma lp_E_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    0 < Efun β m := by
  obtain ⟨c, C, hc, -, h⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  exact lt_of_lt_of_le (mul_pos hc (lt_min hm one_pos)) (h m hm).1

private lemma lp_R_mono {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    StrictMono (fun u : ℝ => rW (emaW β) (Real.exp u)) := by
  have hmono := (lem_app_de_scalar_iii (vk_weightSeq hβ0 hβ1)).2.1
  intro a b hab
  exact hmono (Set.mem_Ici.2 (Real.exp_pos a).le) (Set.mem_Ici.2 (Real.exp_pos b).le)
    (Real.exp_lt_exp.2 hab)

private lemma lp_R_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (u : ℝ) :
    0 < rW (emaW β) (Real.exp u) := (loc_Qm_r hβ0 hβ1 (Real.exp_pos u)).1

private lemma lp_Qm_R {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (u : ℝ) :
    Qm β (rW (emaW β) (Real.exp u)) = Real.exp u := (loc_Qm_r hβ0 hβ1 (Real.exp_pos u)).2

private lemma lp_R_surj {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    ∃ u : ℝ, rW (emaW β) (Real.exp u) = m := by
  obtain ⟨hq, hr⟩ := vk_Qm hβ0 hβ1 hm
  exact ⟨Real.log (Qm β m), by rw [Real.exp_log hq]; exact hr⟩

private lemma lp_R_asymp {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C0 u1 : ℝ, 0 ≤ C0 ∧ ∀ u : ℝ, u1 ≤ u →
      |rW (emaW β) (Real.exp u) - 1 / (2 * -Real.log β) * u| ≤ C0 := by
  obtain ⟨C, hC⟩ := lem_app_pl_weights_iii_logQ hβ0 hβ1
  have hb : 0 < -Real.log β := neg_pos.2 (Real.log_neg hβ0 hβ1)
  have hL : |Real.log β| = -Real.log β := abs_of_neg (Real.log_neg hβ0 hβ1)
  obtain ⟨hq1, hr1⟩ := vk_Qm hβ0 hβ1 (one_pos : (0 : ℝ) < 1)
  refine ⟨|C| / (2 * -Real.log β), Real.log (Qm β 1), by positivity, fun u hu => ?_⟩
  have hR1 : 1 ≤ rW (emaW β) (Real.exp u) := by
    have h := (lp_R_mono hβ0 hβ1).monotone hu
    rw [Real.exp_log hq1, hr1] at h
    exact h
  have h := hC _ hR1
  rw [lp_Qm_R hβ0 hβ1, Real.log_exp, hL] at h
  have h2b : 0 < 2 * -Real.log β := by positivity
  have e : rW (emaW β) (Real.exp u) - 1 / (2 * -Real.log β) * u =
      -(u - 2 * -Real.log β * rW (emaW β) (Real.exp u)) / (2 * -Real.log β) := by
    have hlog : Real.log β ≠ 0 := (Real.log_neg hβ0 hβ1).ne
    field_simp
    ring
  rw [e, abs_div, abs_neg, abs_of_pos h2b]
  exact div_le_div_of_nonneg_right (h.trans (le_abs_self C)) h2b.le



private lemma lp_Qm_mono {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    MonotoneOn (Qm β) (Ioi 0) := by
  intro a ha b hb hab
  obtain ⟨hQa, hra⟩ := vk_Qm hβ0 hβ1 ha
  obtain ⟨hQb, hrb⟩ := vk_Qm hβ0 hβ1 hb
  by_contra h
  have h := not_le.1 h
  have := (lem_app_de_scalar_iii (vk_weightSeq hβ0 hβ1)).2.1 (Set.mem_Ici.2 hQb.le)
    (Set.mem_Ici.2 hQa.le) h
  rw [hra, hrb] at this
  linarith [this, hab]

private lemma lp_Qm_cont {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ContinuousOn (Qm β) (Ioi 0) := by
  intro a ha
  refine ContinuousAt.continuousWithinAt ?_
  have himg : Qm β '' Ioi 0 = Ioi 0 := by
    ext q
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact (vk_Qm hβ0 hβ1 hm).1
    · intro hq
      exact ⟨rW (emaW β) q, (loc_Qm_r hβ0 hβ1 hq).1, (loc_Qm_r hβ0 hβ1 hq).2⟩
  refine continuousAt_of_monotoneOn_of_image_mem_nhds (lp_Qm_mono hβ0 hβ1)
    (Ioi_mem_nhds ha) ?_
  rw [himg]
  exact Ioi_mem_nhds (vk_Qm hβ0 hβ1 ha).1

private lemma lp_Efun_cont {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ContinuousOn (Efun β) (Ioi 0) := by
  have hw := vk_weightSeq hβ0 hβ1
  have hcd : ContDiffOn ℝ 1 (rW (emaW β)) (Ioi 0) := by
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (Fw (emaW β)) (Ici 0) :=
      (lem_app_de_scalar_ii hw).2.2.2.2.1
    have h2 : ContDiffOn ℝ 1 (fun q : ℝ => q * Fw (emaW β) q) (Ioi 0) :=
      contDiffOn_id.mul (h1.of_le (by exact_mod_cast le_top)|>.mono Ioi_subset_Ici_self)
    exact h2
  have hd : ContinuousOn (deriv (rW (emaW β))) (Ioi 0) :=
    hcd.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  have hQ := lp_Qm_cont hβ0 hβ1
  have hmaps : MapsTo (Qm β) (Ioi 0) (Ioi 0) := fun m hm => (vk_Qm hβ0 hβ1 hm).1
  exact hQ.mul (hd.comp hQ hmaps)



private lemma lp_cont_tsum {S : Set (ℝ × ℝ)} {f : ℕ → ℝ → ℝ × ℝ → ℝ} {c : ℕ → ℝ} {H : ℝ → ℝ}
    (hc : Summable c) (hH : Integrable H (gaussianReal 0 1)) (hH0 : ∀ g, 0 ≤ H g)
    (hmeas : ∀ a q, q ∈ S → AEStronglyMeasurable (fun g => f a g q) (gaussianReal 0 1))
    (hcont : ∀ a g, ContinuousOn (f a g) S)
    (hbd : ∀ a q, q ∈ S → ∀ g, |f a g q| ≤ c a * H g) :
    ContinuousOn (fun q => ∑' a, ∫ g, f a g q ∂(gaussianReal 0 1)) S := by
  refine continuousOn_tsum (u := fun a => c a * ∫ g, H g ∂(gaussianReal 0 1)) (fun a => ?_)
    (hc.mul_right _) (fun a q hq => ?_)
  · exact continuousOn_of_dominated (F := fun q g => f a g q) (bound := fun g => c a * H g)
      (fun q hq => hmeas a q hq)
      (fun q hq => Filter.Eventually.of_forall fun g => by
        rw [Real.norm_eq_abs]; exact hbd a q hq g)
      (hH.const_mul _) (Filter.Eventually.of_forall fun g => hcont a g)
  · calc ‖∫ g, f a g q ∂(gaussianReal 0 1)‖ ≤ ∫ g, c a * H g ∂(gaussianReal 0 1) :=
          norm_integral_le_of_norm_le (hH.const_mul _) (Filter.Eventually.of_forall fun g => by
            rw [Real.norm_eq_abs]; exact hbd a q hq g)
      _ = c a * ∫ g, H g ∂(gaussianReal 0 1) := integral_const_mul _ _

private lemma lp_D_cont_R {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ℓ : ℕ) (R : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => DLagNat β q.1 q.2 ℓ)
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ R ∧ 0 ≤ q.2 ∧ q.2 ≤ R} := by
  unfold DLagNat
  have hρ0 : 0 ≤ β ^ ℓ := pow_nonneg hβ0.le ℓ
  have hρ1 : β ^ ℓ ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
  have hs0 : 0 ≤ β ^ (2 * ℓ) := pow_nonneg hβ0.le _
  refine lp_cont_tsum (c := fun a => R * emaW β a ^ 2) (H := fun g => g ^ 2)
    ((vk_w2_summable hβ0 hβ1).mul_left R) (Muon.Foundations.gaussian_integrable_pow 2)
    (fun g => sq_nonneg g) ?_ ?_ ?_
  · intro a q hq
    refine Continuous.aestronglyMeasurable ?_
    have hq1 : 0 ≤ q.1 := hq.1
    have hq2 : 0 ≤ q.2 := hq.2.2.1
    have hd : ∀ g : ℝ, (1 + q.1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q.2 * emaW β a ^ 2 * g ^ 2) ≠ 0 := fun g => by
      have : 0 < (1 + q.1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q.2 * emaW β a ^ 2 * g ^ 2) := by positivity
      exact this.ne'
    exact (by fun_prop : Continuous fun g : ℝ => β ^ ℓ * Real.sqrt (q.1 * q.2) *
        emaW β a ^ 2 * g ^ 2).div (by fun_prop) hd
  · intro a g
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (by fun_prop : Continuous fun q : ℝ × ℝ => β ^ ℓ * Real.sqrt (q.1 * q.2) *
        emaW β a ^ 2 * g ^ 2).continuousOn
    · exact (by fun_prop : Continuous fun q : ℝ × ℝ => (1 + q.1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q.2 * emaW β a ^ 2 * g ^ 2)).continuousOn
    · intro q hq
      have hq1 : 0 ≤ q.1 := hq.1
      have hq2 : 0 ≤ q.2 := hq.2.2.1
      have : 0 < (1 + q.1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q.2 * emaW β a ^ 2 * g ^ 2) := by positivity
      exact this.ne'
  · intro a q hq g
    obtain ⟨hq1, hq1R, hq2, hq2R⟩ := hq
    have hden : 1 ≤ (1 + q.1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q.2 * emaW β a ^ 2 * g ^ 2) := by
      have h1 : 0 ≤ q.1 * emaW β a ^ 2 * g ^ 2 := by positivity
      have h2 : 0 ≤ β ^ (2 * ℓ) * q.2 * emaW β a ^ 2 * g ^ 2 := by positivity
      nlinarith [mul_nonneg h1 h2]
    have hn0 : 0 ≤ β ^ ℓ * Real.sqrt (q.1 * q.2) * emaW β a ^ 2 * g ^ 2 := by positivity
    rw [abs_of_nonneg (by positivity)]
    refine (div_le_self hn0 hden).trans ?_
    have hsq : Real.sqrt (q.1 * q.2) ≤ R := by
      rw [Real.sqrt_le_iff]
      refine ⟨by linarith, ?_⟩
      nlinarith [mul_le_mul hq1R hq2R hq2 (by linarith : (0:ℝ) ≤ R)]
    have : β ^ ℓ * Real.sqrt (q.1 * q.2) ≤ R := by
      calc _ ≤ 1 * R := mul_le_mul hρ1 hsq (Real.sqrt_nonneg _) zero_le_one
        _ = R := one_mul R
    have h3 : 0 ≤ emaW β a ^ 2 * g ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right this h3]

private lemma lp_cont_of_R {F : ℝ × ℝ → ℝ}
    (h : ∀ R : ℝ, ContinuousOn F {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ R ∧ 0 ≤ q.2 ∧ q.2 ≤ R}) :
    ContinuousOn F {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} := by
  intro x hx
  refine ((h (max x.1 x.2 + 1)) x ⟨hx.1, ?_, hx.2, ?_⟩).mono_of_mem_nhdsWithin ?_
  · linarith [le_max_left x.1 x.2]
  · linarith [le_max_right x.1 x.2]
  · have h1 : {q : ℝ × ℝ | q.1 < max x.1 x.2 + 1 ∧ q.2 < max x.1 x.2 + 1} ∈ 𝓝 x := by
      refine IsOpen.mem_nhds (isOpen_lt continuous_fst continuous_const |>.inter
        (isOpen_lt continuous_snd continuous_const)) ⟨?_, ?_⟩
      · show x.1 < _
        linarith [le_max_left x.1 x.2]
      · show x.2 < _
        linarith [le_max_right x.1 x.2]
    filter_upwards [mem_nhdsWithin_of_mem_nhds h1, self_mem_nhdsWithin] with q hq hq'
    exact ⟨hq'.1, hq.1.le, hq'.2, hq.2.le⟩

private lemma lp_DLag_cont {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ℓ : ℤ) :
    ContinuousOn (fun q : ℝ × ℝ => DLag β q.1 q.2 ℓ) {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} := by
  by_cases hℓ : 0 ≤ ℓ
  · have : (fun q : ℝ × ℝ => DLag β q.1 q.2 ℓ) = fun q => DLagNat β q.1 q.2 ℓ.toNat := by
      funext q; simp [DLag, hℓ]
    rw [this]
    exact lp_cont_of_R (fun R => lp_D_cont_R hβ0 hβ1 _ R)
  · have : (fun q : ℝ × ℝ => DLag β q.1 q.2 ℓ) = fun q => DLagNat β q.2 q.1 (-ℓ).toNat := by
      funext q; simp [DLag, hℓ]
    rw [this]
    have h2 : ContinuousOn (fun q : ℝ × ℝ => DLagNat β q.1 q.2 (-ℓ).toNat)
        {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} :=
      lp_cont_of_R (fun R => lp_D_cont_R hβ0 hβ1 _ R)
    exact h2.comp continuous_swap.continuousOn (fun q hq => ⟨hq.2, hq.1⟩)


private lemma lp_phi_pos {φ : ℝ × ℝ → ℝ} (hφsupp : tsupport φ ⊆ Ioi 0 ×ˢ Ioi 0) {x y : ℝ}
    (h : φ (x, y) ≠ 0) : 0 < x ∧ 0 < y :=
  hφsupp (subset_tsupport φ h)

private lemma lp_integrable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ℓ : ℤ) {s : ℝ} (hs : 0 < s)
    {φ : ℝ × ℝ → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hφsupp : tsupport φ ⊆ Ioi 0 ×ˢ Ioi 0) :
    Integrable (fun p : ℝ × ℝ => φ (p.1 / s, p.2 / s) *
        DLag β (Qm β p.1) (Qm β p.2) ℓ /
          (Real.pi ^ 2 * s * Efun β p.1 * Efun β p.2)) := by
  set f : ℝ × ℝ → ℝ := fun p => φ (p.1 / s, p.2 / s) *
        DLag β (Qm β p.1) (Qm β p.2) ℓ / (Real.pi ^ 2 * s * Efun β p.1 * Efun β p.2) with hf
  set S : Set (ℝ × ℝ) := (fun x : ℝ × ℝ => (s * x.1, s * x.2)) '' tsupport φ with hS
  have hSc : IsCompact S := hφs.isCompact.image (by fun_prop)
  have hST : S ⊆ Ioi 0 ×ˢ Ioi 0 := by
    rintro _ ⟨x, hx, rfl⟩
    have := hφsupp hx
    exact ⟨mul_pos hs this.1, mul_pos hs this.2⟩
  have hsupp : Function.support f ⊆ S := by
    intro p hp
    have hφ : φ (p.1 / s, p.2 / s) ≠ 0 := by
      intro h0
      apply hp
      simp only [hf, h0, zero_mul, zero_div]
    refine ⟨(p.1 / s, p.2 / s), subset_tsupport φ hφ, ?_⟩
    ext <;> simp only [] <;> field_simp
  have hcont : ContinuousOn f (Ioi 0 ×ˢ Ioi 0) := by
    have hT : MapsTo (fun p : ℝ × ℝ => (Qm β p.1, Qm β p.2)) (Ioi 0 ×ˢ Ioi 0)
        {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} := fun p hp =>
      ⟨(vk_Qm hβ0 hβ1 hp.1).1.le, (vk_Qm hβ0 hβ1 hp.2).1.le⟩
    have hQ1 : ContinuousOn (fun p : ℝ × ℝ => Qm β p.1) (Ioi 0 ×ˢ Ioi 0) :=
      (lp_Qm_cont hβ0 hβ1).comp continuous_fst.continuousOn (fun p hp => hp.1)
    have hQ2 : ContinuousOn (fun p : ℝ × ℝ => Qm β p.2) (Ioi 0 ×ˢ Ioi 0) :=
      (lp_Qm_cont hβ0 hβ1).comp continuous_snd.continuousOn (fun p hp => hp.2)
    have hD : ContinuousOn (fun p : ℝ × ℝ => DLag β (Qm β p.1) (Qm β p.2) ℓ)
        (Ioi 0 ×ˢ Ioi 0) :=
      ContinuousOn.comp (g := fun q : ℝ × ℝ => DLag β q.1 q.2 ℓ)
        (f := fun p : ℝ × ℝ => (Qm β p.1, Qm β p.2)) (lp_DLag_cont hβ0 hβ1 ℓ)
        (hQ1.prodMk hQ2) hT
    have hE1 : ContinuousOn (fun p : ℝ × ℝ => Efun β p.1) (Ioi 0 ×ˢ Ioi 0) :=
      (lp_Efun_cont hβ0 hβ1).comp continuous_fst.continuousOn (fun p hp => hp.1)
    have hE2 : ContinuousOn (fun p : ℝ × ℝ => Efun β p.2) (Ioi 0 ×ˢ Ioi 0) :=
      (lp_Efun_cont hβ0 hβ1).comp continuous_snd.continuousOn (fun p hp => hp.2)
    have hφ' : Continuous (fun p : ℝ × ℝ => φ (p.1 / s, p.2 / s)) :=
      hφc.comp (by fun_prop)
    refine (hφ'.continuousOn.mul hD).div
      ((continuousOn_const.mul hE1).mul hE2) (fun p hp => ?_)
    have := lp_E_pos hβ0 hβ1 hp.1
    have := lp_E_pos hβ0 hβ1 hp.2
    positivity
  have hint : IntegrableOn f S := (hcont.mono hST).integrableOn_compact hSc
  exact (integrableOn_iff_integrable_of_support_subset hsupp).1 hint



/-- Change of variables `m = R(u) = r(e^u)`, `dm = E(m) du`. -/
private lemma lp_cov {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {g : ℝ → ℝ}
    (hg : ∀ x, x ≤ 0 → g x = 0) :
    ∫ x, g x = ∫ u, Efun β (rW (emaW β) (Real.exp u)) * g (rW (emaW β) (Real.exp u)) := by
  have himg : (fun u : ℝ => rW (emaW β) (Real.exp u)) '' Set.univ = Ioi 0 := by
    ext m
    constructor
    · rintro ⟨u, -, rfl⟩
      exact lp_R_pos hβ0 hβ1 u
    · intro hm
      obtain ⟨u, hu⟩ := lp_R_surj hβ0 hβ1 hm
      exact ⟨u, Set.mem_univ _, hu⟩
  have h := integral_image_eq_integral_abs_deriv_smul (s := Set.univ)
    (f := fun u : ℝ => rW (emaW β) (Real.exp u))
    (f' := fun u => Efun β (rW (emaW β) (Real.exp u))) MeasurableSet.univ
    (fun u _ => (lp_R_deriv hβ0 hβ1 u).hasDerivWithinAt)
    ((lp_R_mono hβ0 hβ1).injective.injOn) g
  rw [himg] at h
  have h1 : ∫ x, g x = ∫ x in Ioi (0 : ℝ), g x := by
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
    exact hg x (not_lt.1 hx)
  rw [h1, h, Measure.restrict_univ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [smul_eq_mul]
  rw [abs_of_pos (lp_E_pos hβ0 hβ1 (lp_R_pos hβ0 hβ1 u))]



private lemma lp_ratio {β : ℝ} (hβ0 : 0 < β) (ℓ : ℕ) (a t : ℝ) :
    β ^ (2 * ℓ) * Real.exp (t + (a + 2 * ℓ * -Real.log β)) / Real.exp a = Real.exp t := by
  have h1 : β ^ (2 * ℓ) = Real.exp (2 * ℓ * Real.log β) := by
    calc β ^ (2 * ℓ) = Real.exp (Real.log (β ^ (2 * ℓ))) := (Real.exp_log (pow_pos hβ0 _)).symm
      _ = Real.exp (((2 * ℓ : ℕ) : ℝ) * Real.log β) := by rw [Real.log_pow]
      _ = _ := by push_cast; ring_nf
  rw [h1, ← Real.exp_add, ← Real.exp_sub]
  congr 1
  ring

private lemma lp_D_formula {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ℓ : ℕ) (a t : ℝ) (ht : t ≠ 0) :
    DLagNat β (Real.exp a) (Real.exp (t + (a + 2 * ℓ * -Real.log β))) ℓ =
      (rW (emaW β) (Real.exp (a + t)) - rW (emaW β) (Real.exp a)) / (2 * Real.sinh (t / 2)) := by
  set u := t + (a + 2 * ℓ * -Real.log β) with hu
  have hQa := lp_Qm_R hβ0 hβ1 a
  have hQu := lp_Qm_R hβ0 hβ1 u
  have hrat : Real.log (β ^ (2 * ℓ) * Real.exp u / Real.exp a) = t := by
    rw [hu, lp_ratio hβ0 ℓ a t, Real.log_exp]
  have h := loc_guarded hβ0 hβ1 ℓ (lp_R_pos hβ0 hβ1 a) (lp_R_pos hβ0 hβ1 u)
    (by rw [hQa, hQu, hrat]; exact ht)
  rw [hQa, hQu, hrat] at h
  rw [h, ← Real.exp_add]



private lemma lp_ae_ne : ∀ᵐ t : ℝ, t ≠ 0 := by
  rw [ae_iff]
  simp

private lemma lp_phi_zero {φ : ℝ × ℝ → ℝ} (hφsupp : tsupport φ ⊆ Ioi 0 ×ˢ Ioi 0) {s : ℝ}
    (hs : 0 < s) {m₁ m₂ : ℝ} (h : m₁ ≤ 0 ∨ m₂ ≤ 0) : φ (m₁ / s, m₂ / s) = 0 := by
  by_contra hne
  have := lp_phi_pos hφsupp hne
  rcases h with h | h
  · have h1 := this.1
    rw [div_pos_iff_of_pos_right hs] at h1
    linarith
  · have h1 := this.2
    rw [div_pos_iff_of_pos_right hs] at h1
    linarith

private lemma lp_transform {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ℓ : ℕ) {s : ℝ} (hs : 0 < s)
    {φ : ℝ × ℝ → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hφsupp : tsupport φ ⊆ Ioi 0 ×ˢ Ioi 0) (R : ℝ → ℝ)
    (hR : ∀ x, R x = rW (emaW β) (Real.exp x)) :
    ∫ p : ℝ × ℝ, φ (p.1 / s, p.2 / s) * DLag β (Qm β p.1) (Qm β p.2) (ℓ : ℤ) /
        (Real.pi ^ 2 * s * Efun β p.1 * Efun β p.2) =
      ∫ a : ℝ, ∫ t : ℝ, φ (R a / s, R (t + (a + 2 * ℓ * -Real.log β)) / s) *
        ((R (a + t) - R a) / (2 * Real.sinh (t / 2))) / (Real.pi ^ 2 * s) := by
  have hint := lp_integrable hβ0 hβ1 (ℓ : ℤ) hs hφc hφs hφsupp
  have hpi : 0 < Real.pi ^ 2 := by positivity
  set f : ℝ → ℝ → ℝ := fun m₁ m₂ => φ (m₁ / s, m₂ / s) * DLag β (Qm β m₁) (Qm β m₂) (ℓ : ℤ) /
        (Real.pi ^ 2 * s * Efun β m₁ * Efun β m₂) with hf
  have hint' : Integrable (Function.uncurry f) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]; exact hint
  have h1 : ∫ p : ℝ × ℝ, φ (p.1 / s, p.2 / s) * DLag β (Qm β p.1) (Qm β p.2) (ℓ : ℤ) /
        (Real.pi ^ 2 * s * Efun β p.1 * Efun β p.2) = ∫ m₁ : ℝ, ∫ m₂ : ℝ, f m₁ m₂ := by
    have e : (fun p : ℝ × ℝ => φ (p.1 / s, p.2 / s) * DLag β (Qm β p.1) (Qm β p.2) (ℓ : ℤ) /
        (Real.pi ^ 2 * s * Efun β p.1 * Efun β p.2)) = Function.uncurry f := rfl
    rw [e, Measure.volume_eq_prod, integral_prod _ hint']
    rfl
  rw [h1]
  have hf0 : ∀ m₁ m₂ : ℝ, (m₁ ≤ 0 ∨ m₂ ≤ 0) → f m₁ m₂ = 0 := by
    intro m₁ m₂ h
    simp only [hf, lp_phi_zero hφsupp hs h, zero_mul, zero_div]
  have hcov1 : ∀ m₁ : ℝ, ∫ m₂ : ℝ, f m₁ m₂ = ∫ u : ℝ, Efun β (rW (emaW β) (Real.exp u)) *
      f m₁ (rW (emaW β) (Real.exp u)) := fun m₁ =>
    lp_cov hβ0 hβ1 (g := f m₁) (fun x hx => hf0 m₁ x (Or.inr hx))
  have hG0 : ∀ m₁ : ℝ, m₁ ≤ 0 → ∫ m₂ : ℝ, f m₁ m₂ = 0 := fun m₁ hm₁ => by
    simp [hf0 m₁ _ (Or.inl hm₁)]
  rw [lp_cov hβ0 hβ1 (g := fun m₁ => ∫ m₂ : ℝ, f m₁ m₂) hG0]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only []
  rw [hcov1, ← integral_const_mul]
  have hshift : ∫ u : ℝ, Efun β (rW (emaW β) (Real.exp a)) * (Efun β (rW (emaW β) (Real.exp u)) *
      f (rW (emaW β) (Real.exp a)) (rW (emaW β) (Real.exp u))) =
      ∫ t : ℝ, Efun β (rW (emaW β) (Real.exp a)) * (Efun β (rW (emaW β)
        (Real.exp (t + (a + 2 * ℓ * -Real.log β)))) *
      f (rW (emaW β) (Real.exp a)) (rW (emaW β) (Real.exp (t + (a + 2 * ℓ * -Real.log β))))) :=
    (integral_add_right_eq_self (fun u : ℝ => Efun β (rW (emaW β) (Real.exp a)) *
      (Efun β (rW (emaW β) (Real.exp u)) *
      f (rW (emaW β) (Real.exp a)) (rW (emaW β) (Real.exp u)))) (a + 2 * ℓ * -Real.log β)).symm
  rw [hshift]
  refine integral_congr_ae ?_
  filter_upwards [lp_ae_ne] with t ht
  have hEa := lp_E_pos hβ0 hβ1 (lp_R_pos hβ0 hβ1 a)
  have hEu := lp_E_pos hβ0 hβ1 (lp_R_pos hβ0 hβ1 (t + (a + 2 * ℓ * -Real.log β)))
  have hDL : DLag β (Real.exp a) (Real.exp (t + (a + 2 * ℓ * -Real.log β))) (ℓ : ℤ) =
      (rW (emaW β) (Real.exp (a + t)) - rW (emaW β) (Real.exp a)) / (2 * Real.sinh (t / 2)) := by
    rw [← lp_D_formula hβ0 hβ1 ℓ a t ht]
    simp [DLag]
  simp only [hf, lp_Qm_R hβ0 hβ1, hDL, hR]
  generalize Efun β (rW (emaW β) (Real.exp a)) = Ea at hEa ⊢
  generalize Efun β (rW (emaW β) (Real.exp (t + (a + 2 * ℓ * -Real.log β)))) = Eu at hEu ⊢
  field_simp



private lemma lp_bdd {ψ : ℝ → ℝ} (hψ : Continuous ψ) {x0 x1 : ℝ}
    (hsupp : ∀ x, ψ x ≠ 0 → x0 ≤ x ∧ x ≤ x1) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |ψ x| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := x0) (b := x1)).exists_bound_of_continuousOn
    hψ.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : ψ x = 0
  · rw [hx, abs_zero]; exact le_max_right _ _
  · have := hM x (hsupp x hx)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

private lemma lp_trans_cont {ψ : ℝ → ℝ} (hψ : Continuous ψ) {x0 x1 : ℝ}
    (hsupp : ∀ x, ψ x ≠ 0 → x0 ≤ x ∧ x ≤ x1) :
    Tendsto (fun h : ℝ => ∫ x, |ψ (x - h) - ψ x|) (𝓝 0) (𝓝 0) := by
  obtain ⟨M, hM0, hM⟩ := lp_bdd hψ hsupp
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (l := 𝓝 (0 : ℝ))
    (F := fun (h : ℝ) (x : ℝ) => |ψ (x - h) - ψ x|)
    (f := fun _ => (0 : ℝ))
    (bound := fun x => (Icc (x0 - 1) (x1 + 1)).indicator (fun _ => 2 * M) x)
    (Filter.Eventually.of_forall fun h => (by fun_prop : Continuous fun x : ℝ =>
      |ψ (x - h) - ψ x|).aestronglyMeasurable)
    ?_ ?_ ?_
  · simpa using hlim
  · have hdist : ∀ᶠ h in 𝓝 (0 : ℝ), |h| < 1 := by
      have : Metric.ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ one_pos
      filter_upwards [this] with h hh
      simpa using hh
    filter_upwards [hdist] with h hh
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_abs]
    by_cases hx : x ∈ Icc (x0 - 1) (x1 + 1)
    · rw [Set.indicator_of_mem hx]
      calc |ψ (x - h) - ψ x| ≤ |ψ (x - h)| + |ψ x| := abs_sub _ _
        _ ≤ M + M := add_le_add (hM _) (hM _)
        _ = 2 * M := by ring
    · rw [Set.indicator_of_notMem hx]
      have h1 : ψ x = 0 := by
        by_contra hne
        have := hsupp x hne
        exact hx ⟨by linarith [this.1], by linarith [this.2]⟩
      have h2 : ψ (x - h) = 0 := by
        by_contra hne
        have := hsupp _ hne
        have hh' := abs_lt.1 hh
        exact hx ⟨by linarith [this.1], by linarith [this.2]⟩
      rw [h1, h2]; simp
  · exact (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp) enorm_ne_top)
  · refine Filter.Eventually.of_forall fun x => ?_
    have hc : Continuous fun h : ℝ => |ψ (x - h) - ψ x| := by fun_prop
    have := hc.tendsto 0
    simpa using this



private lemma lp_cs_scaled {ψ : ℝ → ℝ} {x0 x1 : ℝ}
    (hsupp : ∀ x, ψ x ≠ 0 → x0 ≤ x ∧ x ≤ x1) {c : ℝ} (hc : 0 < c) :
    HasCompactSupport (fun a : ℝ => ψ (a / c)) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := c * x0) (b := c * x1)) (fun a ha => ?_)
  by_contra hne
  have := hsupp _ hne
  apply ha
  constructor
  · have := (le_div_iff₀ hc).1 this.1
    linarith
  · have := (div_le_iff₀ hc).1 this.2
    linarith

private lemma lp_avg {R : ℝ → ℝ} {b C0 u1 : ℝ} (hb : 0 < b) (hRc : Continuous R)
    (hRa : ∀ u, u1 ≤ u → |R u - u / b| ≤ C0) {ψ : ℝ → ℝ} (hψ : Continuous ψ) {x0 x1 : ℝ}
    (hsupp : ∀ x, ψ x ≠ 0 → x0 ≤ x ∧ x ≤ x1) {s : ℝ} (hs : 0 < s) (t : ℝ)
    (hu : u1 + |t| ≤ b * (s * x0)) :
    |1 / s * (∫ a : ℝ, ψ (a / (b * s)) * (R (a + t) - R a)) - t * (∫ x : ℝ, ψ x)| ≤
      C0 * b * ∫ x : ℝ, |ψ (x - t / (b * s)) - ψ x| := by
  have hbs : 0 < b * s := mul_pos hb hs
  set Ψ : ℝ → ℝ := fun a => ψ (a / (b * s)) with hΨ
  set e : ℝ → ℝ := fun x => R x - x / b with he
  have hΨc : Continuous Ψ := hψ.comp (by fun_prop)
  have hΨs : HasCompactSupport Ψ := lp_cs_scaled hsupp hbs
  have hec : Continuous e := by simp only [he]; fun_prop
  have hI1 : Integrable Ψ := hΨc.integrable_of_hasCompactSupport hΨs
  have hI2 : Integrable (fun a => Ψ a * e (a + t)) :=
    (hΨc.mul (hec.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      (hΨs.mul_right)
  have hI3 : Integrable (fun a => Ψ a * e a) :=
    (hΨc.mul hec).integrable_of_hasCompactSupport (hΨs.mul_right)
  have hpt : ∀ a, Ψ a * (R (a + t) - R a) =
      t / b * Ψ a + (Ψ a * e (a + t) - Ψ a * e a) := by
    intro a
    simp only [he]
    field_simp
    ring
  have hsplit : ∫ a : ℝ, Ψ a * (R (a + t) - R a) =
      t / b * (∫ a, Ψ a) + ((∫ a, Ψ a * e (a + t)) - ∫ a, Ψ a * e a) := by
    have h1 := integral_add (μ := volume) (f := fun a => t / b * Ψ a)
      (g := fun a => Ψ a * e (a + t) - Ψ a * e a) (hI1.const_mul _) (hI2.sub hI3)
    beta_reduce at h1
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), h1, integral_const_mul,
      integral_sub hI2 hI3]
  have hΨint : ∫ a, Ψ a = b * s * ∫ x, ψ x := by
    have := Measure.integral_comp_div (fun x => ψ x) (b * s)
    simp only [hΨ]
    rw [this, abs_of_pos hbs, smul_eq_mul]
  have hshift : ∫ a, Ψ a * e (a + t) = ∫ a, Ψ (a - t) * e a := by
    have := integral_add_right_eq_self (μ := volume) (fun y => Ψ (y - t) * e y) t
    simpa using this
  have hI4 : Integrable (fun a => Ψ (a - t) * e a) := by
    refine ((hΨc.comp (continuous_id.sub continuous_const)).mul hec).integrable_of_hasCompactSupport
      ?_
    exact (hΨs.comp_homeomorph (Homeomorph.subRight t)).mul_right
  have hdiff : Integrable (fun a => |Ψ (a - t) - Ψ a|) :=
    ((hI1.comp_sub_right t).sub hI1).abs
  have hrem : |(∫ a, Ψ a * e (a + t)) - ∫ a, Ψ a * e a| ≤
      C0 * ∫ a, |Ψ (a - t) - Ψ a| := by
    rw [hshift, ← integral_sub hI4 hI3, ← integral_const_mul]
    have := norm_integral_le_of_norm_le (μ := volume)
      (f := fun a => Ψ (a - t) * e a - Ψ a * e a) (g := fun a => C0 * |Ψ (a - t) - Ψ a|)
      (hdiff.const_mul C0) (Filter.Eventually.of_forall fun a => ?_)
    · simpa [Real.norm_eq_abs] using this
    · rw [Real.norm_eq_abs, ← sub_mul, abs_mul, mul_comm C0]
      by_cases h0 : Ψ (a - t) - Ψ a = 0
      · rw [h0]; simp
      · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have hau : u1 ≤ a := by
          by_cases hA : Ψ a = 0
          · have hB : Ψ (a - t) ≠ 0 := by
              intro hB; apply h0; rw [hB, hA]; ring
            have h1 := (hsupp _ hB).1
            rw [le_div_iff₀ hbs] at h1
            have h2 := neg_abs_le t
            nlinarith
          · have h1 := (hsupp _ hA).1
            rw [le_div_iff₀ hbs] at h1
            have h2 := abs_nonneg t
            nlinarith
        exact hRa a hau |>.trans' (le_of_eq (by simp only [he])) 
  have hscale : ∫ a, |Ψ (a - t) - Ψ a| = b * s * ∫ x : ℝ, |ψ (x - t / (b * s)) - ψ x| := by
    have := Measure.integral_comp_div (fun x => |ψ (x - t / (b * s)) - ψ x|) (b * s)
    have e2 : (fun a : ℝ => |Ψ (a - t) - Ψ a|) =
        fun a => (fun x => |ψ (x - t / (b * s)) - ψ x|) (a / (b * s)) := by
      funext a
      simp only [hΨ, sub_div]
    rw [e2, this, abs_of_pos hbs, smul_eq_mul]
  have key : 1 / s * (∫ a : ℝ, Ψ a * (R (a + t) - R a)) - t * (∫ x : ℝ, ψ x) =
      1 / s * ((∫ a, Ψ a * e (a + t)) - ∫ a, Ψ a * e a) := by
    rw [hsplit, hΨint]
    field_simp
    ring
  change |1 / s * (∫ a : ℝ, Ψ a * (R (a + t) - R a)) - t * (∫ x : ℝ, ψ x)| ≤ _
  rw [key, abs_mul, abs_of_pos (one_div_pos.2 hs)]
  calc 1 / s * |(∫ a, Ψ a * e (a + t)) - ∫ a, Ψ a * e a|
      ≤ 1 / s * (C0 * ∫ a, |Ψ (a - t) - Ψ a|) :=
        mul_le_mul_of_nonneg_left hrem (one_div_pos.2 hs).le
    _ = _ := by
        rw [hscale]
        field_simp



private lemma lp_supp_bounds {φ : ℝ × ℝ → ℝ} (hφs : HasCompactSupport φ)
    (hφsupp : tsupport φ ⊆ Ioi 0 ×ˢ Ioi 0) :
    ∃ x0 x1 : ℝ, 0 < x0 ∧ x0 ≤ x1 ∧ ∀ x y : ℝ, φ (x, y) ≠ 0 → x0 ≤ x ∧ x ≤ x1 := by
  have hK : IsCompact (Prod.fst '' tsupport φ) := hφs.isCompact.image continuous_fst
  by_cases hne : (Prod.fst '' tsupport φ).Nonempty
  · obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hne continuous_id.continuousOn
    obtain ⟨x1, hx1, hmax⟩ := hK.exists_isMaxOn hne continuous_id.continuousOn
    refine ⟨x0, x1, ?_, hmin hx1, fun x y h => ?_⟩
    · obtain ⟨p, hp, rfl⟩ := hx0
      exact (hφsupp hp).1
    · have hx : x ∈ Prod.fst '' tsupport φ := ⟨(x, y), subset_tsupport φ h, rfl⟩
      exact ⟨hmin hx, hmax hx⟩
  · refine ⟨1, 1, one_pos, le_rfl, fun x y h => ?_⟩
    exact absurd ⟨x, (x, y), subset_tsupport φ h, rfl⟩ hne



private lemma lp_window {R : ℝ → ℝ} {b C0 u1 x0 x1 s : ℝ} (hb : 0 < b) (hs : 0 < s)
    (hRm : Monotone R) (hRa : ∀ u, u1 ≤ u → |R u - u / b| ≤ C0) (hsW : R u1 < x0 * s)
    {a z : ℝ} (h : x0 ≤ R a / s ∧ R a / s ≤ x1) :
    a ∈ Icc (b * (x0 * s - C0)) (b * (x1 * s + C0)) := by
  obtain ⟨h1, h2⟩ := h
  rw [le_div_iff₀ hs] at h1
  rw [div_le_iff₀ hs] at h2
  have hau : u1 ≤ a := by
    by_contra hlt
    have := hRm (not_le.1 hlt).le
    linarith
  have h3 := abs_le.1 (hRa a hau)
  constructor
  · have : x0 * s - C0 ≤ a / b := by linarith
    rw [le_div_iff₀ hb] at this
    linarith
  · have : a / b ≤ x1 * s + C0 := by linarith
    rw [div_le_iff₀ hb] at this
    linarith

private lemma lp_window_psi {b C0 x0 x1 s : ℝ} (hb : 0 < b) (hs : 0 < s) (hC0 : 0 ≤ C0)
    {a : ℝ} (h : x0 ≤ a / (b * s) ∧ a / (b * s) ≤ x1) :
    a ∈ Icc (b * (x0 * s - C0)) (b * (x1 * s + C0)) := by
  obtain ⟨h1, h2⟩ := h
  have hbs : 0 < b * s := mul_pos hb hs
  rw [le_div_iff₀ hbs] at h1
  rw [div_le_iff₀ hbs] at h2
  constructor <;> nlinarith



private lemma lp_Fn_bd {R : ℝ → ℝ} {b K C0 u1 x0 x1 s c Mφ : ℝ} {φ : ℝ × ℝ → ℝ}
    (hb : 0 < b) (hs : 0 < s) (hK : 0 ≤ K) (hRm : Monotone R)
    (hRl : ∀ x y, |R x - R y| ≤ K * |x - y|) (hRa : ∀ u, u1 ≤ u → |R u - u / b| ≤ C0)
    (hsW : R u1 < x0 * s) (hx : ∀ x y : ℝ, φ (x, y) ≠ 0 → x0 ≤ x ∧ x ≤ x1)
    (hM : ∀ p, |φ p| ≤ Mφ) (a t : ℝ) :
    |φ (R a / s, R (t + (a + c)) / s) * ((R (a + t) - R a) / (2 * Real.sinh (t / 2))) /
        (Real.pi ^ 2 * s)| ≤
      (Icc (b * (x0 * s - C0)) (b * (x1 * s + C0))).indicator
        (fun _ => Mφ * K / (Real.pi ^ 2 * s) * ((1 + |t|) * Real.exp (-|t| / 2))) a := by
  have hMnn : 0 ≤ Mφ := (abs_nonneg _).trans (hM 0)
  have hpi : 0 < Real.pi ^ 2 * s := by positivity
  have hB : 0 ≤ (1 + |t|) * Real.exp (-|t| / 2) := by positivity
  by_cases h0 : φ (R a / s, R (t + (a + c)) / s) = 0
  · rw [h0, zero_mul, zero_div, abs_zero]
    exact Set.indicator_nonneg (fun _ _ => by positivity) _
  · have hwin := lp_window hb hs hRm hRa hsW (z := 0) (hx _ _ h0)
    rw [Set.indicator_of_mem hwin, abs_div, abs_mul, abs_of_pos hpi, div_le_iff₀ hpi]
    have h1 := lp_div_sinh (K := K) (N := R (a + t) - R a) (t := t) hK
      (by have := hRl (a + t) a; simpa using this)
    calc |φ (R a / s, R (t + (a + c)) / s)| * |(R (a + t) - R a) / (2 * Real.sinh (t / 2))|
        ≤ Mφ * (K * ((1 + |t|) * Real.exp (-|t| / 2))) :=
          mul_le_mul (hM _) h1 (abs_nonneg _) hMnn
      _ = _ := by field_simp



private lemma lp_Fn_int {R : ℝ → ℝ} {b K C0 u1 x0 x1 s c Mφ : ℝ} {φ : ℝ × ℝ → ℝ}
    (hb : 0 < b) (hs : 0 < s) (hK : 0 ≤ K) (hC0 : 0 ≤ C0) (hRc : Continuous R)
    (hRm : Monotone R)
    (hRl : ∀ x y, |R x - R y| ≤ K * |x - y|) (hRa : ∀ u, u1 ≤ u → |R u - u / b| ≤ C0)
    (hsW : R u1 < x0 * s) (hx : ∀ x y : ℝ, φ (x, y) ≠ 0 → x0 ≤ x ∧ x ≤ x1) (hx01 : x0 ≤ x1)
    (hM : ∀ p, |φ p| ≤ Mφ) (hφc : Continuous φ) :
    Integrable (fun p : ℝ × ℝ => φ (R p.1 / s, R (p.2 + (p.1 + c)) / s) *
        ((R (p.1 + p.2) - R p.1) / (2 * Real.sinh (p.2 / 2))) / (Real.pi ^ 2 * s))
      (volume.prod volume) := by
  have hmeas : Measurable (fun p : ℝ × ℝ => φ (R p.1 / s, R (p.2 + (p.1 + c)) / s) *
        ((R (p.1 + p.2) - R p.1) / (2 * Real.sinh (p.2 / 2))) / (Real.pi ^ 2 * s)) := by
    have hR := hRc.measurable
    have hφ := hφc.measurable
    have h1 : Measurable (fun p : ℝ × ℝ => φ (R p.1 / s, R (p.2 + (p.1 + c)) / s)) :=
      hφ.comp (by fun_prop)
    have h2 : Measurable (fun p : ℝ × ℝ => (R (p.1 + p.2) - R p.1) / (2 * Real.sinh (p.2 / 2))) :=
      (by fun_prop : Measurable fun p : ℝ × ℝ => R (p.1 + p.2) - R p.1).div
        (by fun_prop)
    exact (h1.mul h2).div_const _
  have hf : Integrable (fun a : ℝ => (Icc (b * (x0 * s - C0)) (b * (x1 * s + C0))).indicator
      (fun _ => Mφ * K / (Real.pi ^ 2 * s)) a) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp) enorm_ne_top)
  have hg := (hf.mul_prod (lp_B_int))
  refine Integrable.mono' hg hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs]
  refine (lp_Fn_bd (c := c) hb hs hK hRm hRl hRa hsW hx hM p.1 p.2).trans (le_of_eq ?_)
  by_cases hp : p.1 ∈ Icc (b * (x0 * s - C0)) (b * (x1 * s + C0))
  · simp only [Set.indicator_of_mem hp]
  · simp only [Set.indicator_of_notMem hp, zero_mul]



private lemma lp_Gn_bd {R : ℝ → ℝ} {b K C0 u1 x0 x1 s c Mφ : ℝ} {φ : ℝ × ℝ → ℝ}
    (hb : 0 < b) (hs : 1 ≤ s) (hK : 0 ≤ K) (hC0 : 0 ≤ C0)
    (hRm : Monotone R)
    (hRl : ∀ x y, |R x - R y| ≤ K * |x - y|) (hRa : ∀ u, u1 ≤ u → |R u - u / b| ≤ C0)
    (hsW : R u1 < x0 * s) (hx : ∀ x y : ℝ, φ (x, y) ≠ 0 → x0 ≤ x ∧ x ≤ x1) (hx01 : x0 ≤ x1)
    (hM : ∀ p, |φ p| ≤ Mφ) (t : ℝ) :
    |∫ a : ℝ, φ (R a / s, R (t + (a + c)) / s) *
        ((R (a + t) - R a) / (2 * Real.sinh (t / 2))) / (Real.pi ^ 2 * s)| ≤
      Mφ * K * (b * (x1 - x0 + 2 * C0)) / Real.pi ^ 2 * ((1 + |t|) * Real.exp (-|t| / 2)) := by
  have hs0 : 0 < s := by linarith
  have hMnn : 0 ≤ Mφ := (abs_nonneg _).trans (hM 0)
  have hpi : 0 < Real.pi ^ 2 := by positivity
  have hB : 0 ≤ (1 + |t|) * Real.exp (-|t| / 2) := by positivity
  have hle : b * (x0 * s - C0) ≤ b * (x1 * s + C0) := by
    refine mul_le_mul_of_nonneg_left ?_ hb.le
    nlinarith
  have hint : Integrable (fun a : ℝ => (Icc (b * (x0 * s - C0)) (b * (x1 * s + C0))).indicator
      (fun _ => Mφ * K / (Real.pi ^ 2 * s) * ((1 + |t|) * Real.exp (-|t| / 2))) a) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp) enorm_ne_top)
  have h := norm_integral_le_of_norm_le (μ := volume) hint
    (f := fun a : ℝ => φ (R a / s, R (t + (a + c)) / s) *
        ((R (a + t) - R a) / (2 * Real.sinh (t / 2))) / (Real.pi ^ 2 * s))
    (Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs]
      exact lp_Fn_bd (c := c) hb hs0 hK hRm hRl hRa hsW hx hM a t)
  rw [Real.norm_eq_abs] at h
  refine h.trans ?_
  rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le hle, smul_eq_mul]
  have hx1 : 0 ≤ x1 - x0 := by linarith
  have e : b * (x1 * s + C0) - b * (x0 * s - C0) = b * ((x1 - x0) * s + 2 * C0) := by ring
  rw [e]
  have h2 : (x1 - x0) * s + 2 * C0 ≤ (x1 - x0 + 2 * C0) * s := by nlinarith
  have h3 : b * ((x1 - x0) * s + 2 * C0) ≤ b * ((x1 - x0 + 2 * C0) * s) :=
    mul_le_mul_of_nonneg_left h2 hb.le
  have hKM : 0 ≤ Mφ * K / (Real.pi ^ 2 * s) * ((1 + |t|) * Real.exp (-|t| / 2)) := by positivity
  calc b * ((x1 - x0) * s + 2 * C0) *
        (Mφ * K / (Real.pi ^ 2 * s) * ((1 + |t|) * Real.exp (-|t| / 2)))
      ≤ b * ((x1 - x0 + 2 * C0) * s) *
        (Mφ * K / (Real.pi ^ 2 * s) * ((1 + |t|) * Real.exp (-|t| / 2))) :=
        mul_le_mul_of_nonneg_right h3 hKM
    _ = _ := by field_simp



private lemma lp_PQ_single {R : ℝ → ℝ} {b K C0 u1 x0 x1 s c τ δ ε1 : ℝ} {φ : ℝ × ℝ → ℝ}
    (hb : 0 < b) (hs : 1 ≤ s) (hK : 0 ≤ K) (hC0 : 0 ≤ C0) (hRc : Continuous R)
    (hRm : Monotone R) (hRl : ∀ x y, |R x - R y| ≤ K * |x - y|)
    (hRa : ∀ u, u1 ≤ u → |R u - u / b| ≤ C0)
    (hsW : R u1 < x0 * s) (hx : ∀ x y : ℝ, φ (x, y) ≠ 0 → x0 ≤ x ∧ x ≤ x1) (hx01 : x0 ≤ x1)
    (hφc : Continuous φ) (hε1 : 0 ≤ ε1)
    (huc : ∀ p q : ℝ × ℝ, |p.1 - q.1| < δ → |p.2 - q.2| < δ → |φ p - φ q| ≤ ε1)
    (t : ℝ) (hu : u1 + |t| + b * C0 ≤ b * (x0 * s))
    (hδ1 : C0 / s < δ) (hδ2 : C0 / s + |t| / (b * s) + |c / (b * s) - τ| < δ) (hc : 0 ≤ c) :
    |1 / s * (∫ a : ℝ, φ (R a / s, R (t + (a + c)) / s) * (R (a + t) - R a)) -
        1 / s * (∫ a : ℝ, φ (a / (b * s), a / (b * s) + τ) * (R (a + t) - R a))| ≤
      ε1 * (K * |t| * (b * (x1 - x0 + 2 * C0))) := by
  have hs0 : 0 < s := by linarith
  have hbs : 0 < b * s := mul_pos hb hs0
  set W : Set ℝ := Icc (b * (x0 * s - C0)) (b * (x1 * s + C0)) with hW
  have hWc : IsCompact W := isCompact_Icc
  have hle : b * (x0 * s - C0) ≤ b * (x1 * s + C0) := by
    refine mul_le_mul_of_nonneg_left ?_ hb.le
    nlinarith
  have hNc : Continuous (fun a : ℝ => R (a + t) - R a) := by fun_prop
  -- integrability of both pieces
  have hI1 : Integrable (fun a : ℝ => φ (R a / s, R (t + (a + c)) / s) * (R (a + t) - R a)) := by
    refine (Continuous.mul ?_ hNc).integrable_of_hasCompactSupport ?_
    · exact hφc.comp (by fun_prop)
    · refine HasCompactSupport.intro hWc (fun a ha => ?_)
      by_contra hne
      have h0 : φ (R a / s, R (t + (a + c)) / s) ≠ 0 := left_ne_zero_of_mul hne
      exact ha (lp_window hb hs0 hRm hRa hsW (z := 0) (hx _ _ h0))
  have hI2 : Integrable (fun a : ℝ => φ (a / (b * s), a / (b * s) + τ) * (R (a + t) - R a)) := by
    refine (Continuous.mul ?_ hNc).integrable_of_hasCompactSupport ?_
    · exact hφc.comp (by fun_prop)
    · refine HasCompactSupport.intro hWc (fun a ha => ?_)
      by_contra hne
      have h0 : φ (a / (b * s), a / (b * s) + τ) ≠ 0 := left_ne_zero_of_mul hne
      exact ha (lp_window_psi hb hs0 hC0 (hx _ _ h0))
  rw [← mul_sub, abs_mul, abs_of_pos (one_div_pos.2 hs0), ← integral_sub hI1 hI2]
  -- pointwise bound
  have hpt : ∀ a : ℝ, |φ (R a / s, R (t + (a + c)) / s) * (R (a + t) - R a) -
      φ (a / (b * s), a / (b * s) + τ) * (R (a + t) - R a)| ≤
      W.indicator (fun _ => ε1 * (K * |t|)) a := by
    intro a
    rw [← sub_mul, abs_mul]
    by_cases ha : a ∈ W
    · rw [Set.indicator_of_mem ha]
      have hbd : b * (x0 * s - C0) ≤ a := ha.1
      have hau : u1 + |t| ≤ a := by nlinarith
      have h1 : |R a - a / b| ≤ C0 := hRa a (by linarith [abs_nonneg t])
      have hu2 : u1 ≤ t + (a + c) := by linarith [neg_abs_le t]
      have h2 : |R (t + (a + c)) - (t + (a + c)) / b| ≤ C0 := hRa _ hu2
      have hd1 : |R a / s - a / (b * s)| < δ := by
        have : R a / s - a / (b * s) = (R a - a / b) / s := by field_simp
        rw [this, abs_div, abs_of_pos hs0]
        calc |R a - a / b| / s ≤ C0 / s := div_le_div_of_nonneg_right h1 hs0.le
          _ < δ := hδ1
      have hd2 : |R (t + (a + c)) / s - (a / (b * s) + τ)| < δ := by
        have e : R (t + (a + c)) / s - (a / (b * s) + τ) =
            (R (t + (a + c)) - (t + (a + c)) / b) / s + (t / (b * s) + (c / (b * s) - τ)) := by
          field_simp
          ring
        rw [e]
        have h5 := abs_add_le ((R (t + (a + c)) - (t + (a + c)) / b) / s)
          (t / (b * s) + (c / (b * s) - τ))
        have h6 := abs_add_le (t / (b * s)) (c / (b * s) - τ)
        have h7 : |(R (t + (a + c)) - (t + (a + c)) / b) / s| ≤ C0 / s := by
          rw [abs_div, abs_of_pos hs0]; exact div_le_div_of_nonneg_right h2 hs0.le
        have h8 : |t / (b * s)| = |t| / (b * s) := by rw [abs_div, abs_of_pos hbs]
        linarith
      have hφd := huc (R a / s, R (t + (a + c)) / s) (a / (b * s), a / (b * s) + τ) hd1 hd2
      have hN : |R (a + t) - R a| ≤ K * |t| := by
        have := hRl (a + t) a
        simpa using this
      exact mul_le_mul hφd hN (abs_nonneg _) hε1
    · rw [Set.indicator_of_notMem ha]
      have h1 : φ (R a / s, R (t + (a + c)) / s) = 0 := by
        by_contra h0
        exact ha (lp_window hb hs0 hRm hRa hsW (z := 0) (hx _ _ h0))
      have h2 : φ (a / (b * s), a / (b * s) + τ) = 0 := by
        by_contra h0
        exact ha (lp_window_psi hb hs0 hC0 (hx _ _ h0))
      rw [h1, h2]; simp
  have hint : Integrable (fun a : ℝ => W.indicator (fun _ => ε1 * (K * |t|)) a) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp) enorm_ne_top)
  have h := norm_integral_le_of_norm_le (μ := volume) hint
    (f := fun a : ℝ => φ (R a / s, R (t + (a + c)) / s) * (R (a + t) - R a) -
      φ (a / (b * s), a / (b * s) + τ) * (R (a + t) - R a))
    (Filter.Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hpt a)
  rw [Real.norm_eq_abs] at h
  have h3 := h.trans (le_of_eq (by
    rw [hW, integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le hle,
      smul_eq_mul]))
  have hx1 : 0 ≤ x1 - x0 := by linarith
  have e : b * (x1 * s + C0) - b * (x0 * s - C0) = b * ((x1 - x0) * s + 2 * C0) := by ring
  rw [e] at h3
  have h2 : (x1 - x0) * s + 2 * C0 ≤ (x1 - x0 + 2 * C0) * s := by nlinarith
  have h4 : b * ((x1 - x0) * s + 2 * C0) ≤ b * ((x1 - x0 + 2 * C0) * s) :=
    mul_le_mul_of_nonneg_left h2 hb.le
  have hKM : 0 ≤ ε1 * (K * |t|) := by positivity
  calc 1 / s * |∫ a, (φ (R a / s, R (t + (a + c)) / s) * (R (a + t) - R a) -
        φ (a / (b * s), a / (b * s) + τ) * (R (a + t) - R a))|
      ≤ 1 / s * (b * ((x1 - x0) * s + 2 * C0) * (ε1 * (K * |t|))) :=
        mul_le_mul_of_nonneg_left h3 (one_div_pos.2 hs0).le
    _ ≤ 1 / s * (b * ((x1 - x0 + 2 * C0) * s) * (ε1 * (K * |t|))) := by
        refine mul_le_mul_of_nonneg_left ?_ (one_div_pos.2 hs0).le
        exact mul_le_mul_of_nonneg_right h4 hKM
    _ = _ := by field_simp



private lemma lp_pointwise {R : ℝ → ℝ} {b K C0 u1 x0 x1 τ : ℝ} {φ : ℝ × ℝ → ℝ}
    (hb : 0 < b) (hK : 0 ≤ K) (hC0 : 0 ≤ C0) (hRc : Continuous R)
    (hRm : Monotone R) (hRl : ∀ x y, |R x - R y| ≤ K * |x - y|)
    (hRa : ∀ u, u1 ≤ u → |R u - u / b| ≤ C0)
    {sn : ℕ → ℝ} (hs : ∀ n, 0 < sn n) (hsT : Tendsto sn atTop atTop) {ℓn : ℕ → ℕ}
    (hℓ : Tendsto (fun n : ℕ => (ℓn n : ℝ) / sn n) atTop (𝓝 τ))
    (hx0 : 0 < x0) (hx : ∀ x y : ℝ, φ (x, y) ≠ 0 → x0 ≤ x ∧ x ≤ x1) (hx01 : x0 ≤ x1)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) (t : ℝ) :
    Tendsto (fun n : ℕ => 1 / sn n * ∫ a : ℝ, φ (R a / sn n, R (t + (a + ℓn n * b)) / sn n) *
        (R (a + t) - R a)) atTop (𝓝 (t * ∫ x : ℝ, φ (x, x + τ))) := by
  set ψ : ℝ → ℝ := fun x => φ (x, x + τ) with hψ
  have hψc : Continuous ψ := hφc.comp (by fun_prop)
  have hψs : ∀ x, ψ x ≠ 0 → x0 ≤ x ∧ x ≤ x1 := fun x h => hx x (x + τ) h
  have hbs : ∀ n, 0 < b * sn n := fun n => mul_pos hb (hs n)
  -- the comparison sequence Q
  have hQ : Tendsto (fun n : ℕ => 1 / sn n * ∫ a : ℝ, φ (a / (b * sn n), a / (b * sn n) + τ) *
      (R (a + t) - R a)) atTop (𝓝 (t * ∫ x : ℝ, ψ x)) := by
    have hh : Tendsto (fun n : ℕ => t / (b * sn n)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (hsT.const_mul_atTop hb)
    have hg : Tendsto (fun n : ℕ => C0 * b * ∫ x : ℝ, |ψ (x - t / (b * sn n)) - ψ x|) atTop
        (𝓝 0) := by
      have := ((lp_trans_cont hψc hψs).comp hh).const_mul (C0 * b)
      simpa using this
    have hev : ∀ᶠ n : ℕ in atTop, u1 + |t| ≤ b * (sn n * x0) := by
      filter_upwards [hsT.eventually_ge_atTop ((u1 + |t|) / (b * x0))] with n hn
      rw [div_le_iff₀ (mul_pos hb hx0)] at hn
      nlinarith
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ hg
    filter_upwards [hev] with n hn
    rw [Real.norm_eq_abs]
    exact lp_avg hb hRc hRa hψc hψs (hs n) t hn
  have hPQ : Tendsto (fun n : ℕ => 1 / sn n * (∫ a : ℝ, φ (R a / sn n, R (t + (a + ℓn n * b)) / sn n) *
        (R (a + t) - R a)) - 1 / sn n * (∫ a : ℝ, φ (a / (b * sn n), a / (b * sn n) + τ) *
      (R (a + t) - R a))) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set M0 : ℝ := K * |t| * (b * (x1 - x0 + 2 * C0)) with hM0def
    have hM0 : 0 ≤ M0 := by
      have : 0 ≤ x1 - x0 := by linarith
      positivity
    set ε1 : ℝ := ε / (2 * (M0 + 1)) with hε1def
    have hε1 : 0 < ε1 := by positivity
    obtain ⟨δ, hδ, hδuc⟩ := Metric.uniformContinuous_iff.1
      (hφs.uniformContinuous_of_continuous hφc) ε1 hε1
    have huc : ∀ p q : ℝ × ℝ, |p.1 - q.1| < δ → |p.2 - q.2| < δ → |φ p - φ q| ≤ ε1 := by
      intro p q h1 h2
      have : dist p q < δ := by
        rw [Prod.dist_eq]
        exact max_lt (by rwa [Real.dist_eq]) (by rwa [Real.dist_eq])
      have := hδuc this
      rw [Real.dist_eq] at this
      exact this.le
    have hg1 : Tendsto (fun n : ℕ => C0 / sn n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hsT
    have hg2 : Tendsto (fun n : ℕ => C0 / sn n + |t| / (b * sn n) +
        |(ℓn n : ℝ) / sn n - τ|) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n : ℕ => |t| / (b * sn n)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (hsT.const_mul_atTop hb)
      have h3 : Tendsto (fun n : ℕ => |(ℓn n : ℝ) / sn n - τ|) atTop (𝓝 0) := by
        have := (hℓ.sub_const τ).abs
        simpa using this
      simpa using (hg1.add h2).add h3
    have e1 : ∀ᶠ n : ℕ in atTop, 1 ≤ sn n := hsT.eventually_ge_atTop 1
    have e2 : ∀ᶠ n : ℕ in atTop, R u1 < x0 * sn n := by
      filter_upwards [hsT.eventually_gt_atTop (R u1 / x0)] with n hn
      rw [div_lt_iff₀ hx0] at hn
      linarith
    have e3 : ∀ᶠ n : ℕ in atTop, u1 + |t| + b * C0 ≤ b * (x0 * sn n) := by
      filter_upwards [hsT.eventually_ge_atTop ((u1 + |t| + b * C0) / (b * x0))] with n hn
      rw [div_le_iff₀ (mul_pos hb hx0)] at hn
      nlinarith
    have e4 : ∀ᶠ n : ℕ in atTop, C0 / sn n < δ := hg1.eventually (gt_mem_nhds hδ)
    have e5 : ∀ᶠ n : ℕ in atTop, C0 / sn n + |t| / (b * sn n) + |(ℓn n : ℝ) / sn n - τ| < δ :=
      hg2.eventually (gt_mem_nhds hδ)
    filter_upwards [e1, e2, e3, e4, e5] with n h1 h2 h3 h4 h5
    rw [Real.dist_eq, sub_zero]
    have hsn := hs n
    have hcn : (ℓn n : ℝ) * b / (b * sn n) = (ℓn n : ℝ) / sn n := by field_simp
    have := lp_PQ_single (c := (ℓn n : ℝ) * b) (τ := τ) (δ := δ) (ε1 := ε1) hb h1 hK hC0 hRc hRm
      hRl hRa h2 hx hx01 hφc hε1.le huc t h3 h4 (by rw [hcn]; exact h5)
      (by positivity)
    refine this.trans_lt ?_
    have h6 : ε1 * M0 ≤ ε / 2 := by
      rw [hε1def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have := hPQ.add hQ
  simpa using this



private lemma lp_abs {R : ℝ → ℝ} {b K C0 u1 τ : ℝ} {φ : ℝ × ℝ → ℝ}
    (hb : 0 < b) (hK : 0 ≤ K) (hC0 : 0 ≤ C0) (hRc : Continuous R)
    (hRm : Monotone R) (hRl : ∀ x y, |R x - R y| ≤ K * |x - y|)
    (hRa : ∀ u, u1 ≤ u → |R u - u / b| ≤ C0)
    {sn : ℕ → ℝ} (hs : ∀ n, 0 < sn n) (hsT : Tendsto sn atTop atTop) {ℓn : ℕ → ℕ}
    (hℓ : Tendsto (fun n : ℕ => (ℓn n : ℝ) / sn n) atTop (𝓝 τ))
    (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hφsupp : tsupport φ ⊆ Ioi 0 ×ˢ Ioi 0) :
    Tendsto (fun n : ℕ => ∫ a : ℝ, ∫ t : ℝ,
      φ (R a / sn n, R (t + (a + ℓn n * b)) / sn n) *
        ((R (a + t) - R a) / (2 * Real.sinh (t / 2))) / (Real.pi ^ 2 * sn n)) atTop
      (𝓝 (∫ r : ℝ, φ (r, r + τ))) := by
  obtain ⟨x0, x1, hx0, hx01, hx⟩ := lp_supp_bounds hφs hφsupp
  obtain ⟨Mφ, hMφ⟩ := hφc.bounded_above_of_compact_support hφs
  have hM : ∀ p, |φ p| ≤ Mφ := fun p => by simpa [Real.norm_eq_abs] using hMφ p
  have hMnn : 0 ≤ Mφ := (abs_nonneg _).trans (hM 0)
  have hpi : 0 < Real.pi ^ 2 := by positivity
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ sn n ∧ R u1 < x0 * sn n := by
    filter_upwards [hsT.eventually_ge_atTop 1, hsT.eventually_gt_atTop (R u1 / x0)] with n h1 h2
    refine ⟨h1, ?_⟩
    rw [div_lt_iff₀ hx0] at h2
    linarith
  set Cb : ℝ := Mφ * K * (b * (x1 - x0 + 2 * C0)) / Real.pi ^ 2 with hCb
  set ψi : ℝ := ∫ x : ℝ, φ (x, x + τ) with hψi
  have key : Tendsto (fun n : ℕ => ∫ t : ℝ, ∫ a : ℝ,
      φ (R a / sn n, R (t + (a + ℓn n * b)) / sn n) *
        ((R (a + t) - R a) / (2 * Real.sinh (t / 2))) / (Real.pi ^ 2 * sn n)) atTop
      (𝓝 (∫ t : ℝ, ψi / Real.pi ^ 2 * (t / (2 * Real.sinh (t / 2))))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (bound := fun t => Cb * ((1 + |t|) * Real.exp (-|t| / 2))) ?_ ?_ ?_ ?_
    · filter_upwards [hev] with n hn
      exact (lp_Fn_int (c := ℓn n * b) hb (hs n) hK hC0 hRc hRm hRl hRa hn.2 hx hx01 hM
        hφc).integral_prod_right.aestronglyMeasurable
    · filter_upwards [hev] with n hn
      refine Filter.Eventually.of_forall fun t => ?_
      rw [Real.norm_eq_abs]
      exact lp_Gn_bd (c := ℓn n * b) hb hn.1 hK hC0 hRm hRl hRa hn.2 hx hx01 hM t
    · exact lp_B_int.const_mul _
    · filter_upwards [lp_ae_ne] with t ht
      have hp := (lp_pointwise hb hK hC0 hRc hRm hRl hRa hs hsT hℓ hx0 hx hx01 hφc hφs t).const_mul
        (1 / (2 * Real.sinh (t / 2) * Real.pi ^ 2))
      have hsinh : Real.sinh (t / 2) ≠ 0 := by
        intro h
        have := Real.sinh_eq_zero.1 h
        apply ht; linarith
      have hlim : ψi / Real.pi ^ 2 * (t / (2 * Real.sinh (t / 2))) =
          1 / (2 * Real.sinh (t / 2) * Real.pi ^ 2) * (t * ψi) := by
        field_simp
      rw [hlim]
      refine hp.congr (fun n => ?_)
      have hsn := hs n
      have e : ∫ a : ℝ, φ (R a / sn n, R (t + (a + ℓn n * b)) / sn n) *
          ((R (a + t) - R a) / (2 * Real.sinh (t / 2))) / (Real.pi ^ 2 * sn n) =
          ∫ a : ℝ, (1 / (2 * Real.sinh (t / 2) * Real.pi ^ 2) * (1 / sn n)) *
            (φ (R a / sn n, R (t + (a + ℓn n * b)) / sn n) * (R (a + t) - R a)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        simp only []
        field_simp
      rw [e, integral_const_mul]
      ring
  have hval : ∫ t : ℝ, ψi / Real.pi ^ 2 * (t / (2 * Real.sinh (t / 2))) = ψi := by
    rw [integral_const_mul, lp_w_val]
    field_simp
  rw [hval] at key
  refine key.congr' ?_
  filter_upwards [hev] with n hn
  symm
  exact integral_integral_swap (lp_Fn_int (c := ℓn n * b) hb (hs n) hK hC0 hRc hRm hRl hRa hn.2 hx
    hx01 hM hφc)


private lemma lp_core {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (ℓn : ℕ → ℤ) (sn : ℕ → ℝ) (hs : ∀ n, 0 < sn n)
    (hsT : Tendsto sn atTop atTop) {τ : ℝ} (hτ : 0 < τ)
    (hℓ : Tendsto (fun n : ℕ => (ℓn n : ℝ) / sn n) atTop (𝓝 τ))
    (φ : ℝ × ℝ → ℝ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hφsupp : tsupport φ ⊆ Ioi 0 ×ˢ Ioi 0) :
    (∀ n : ℕ, Integrable (fun p : ℝ × ℝ => φ (p.1 / sn n, p.2 / sn n) *
        DLag β (Qm β p.1) (Qm β p.2) (ℓn n) /
          (Real.pi ^ 2 * sn n * Efun β p.1 * Efun β p.2))) ∧
    Tendsto (fun n : ℕ => ∫ p : ℝ × ℝ, φ (p.1 / sn n, p.2 / sn n) *
        DLag β (Qm β p.1) (Qm β p.2) (ℓn n) /
          (Real.pi ^ 2 * sn n * Efun β p.1 * Efun β p.2)) atTop
      (𝓝 (∫ r : ℝ, φ (r, r + τ))) := by
  refine ⟨fun n => lp_integrable hβ0 hβ1 (ℓn n) (hs n) hφc hφs hφsupp, ?_⟩
  -- eventually the lag is nonnegative
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < (ℓn n : ℝ) / sn n := hℓ.eventually (lt_mem_nhds hτ)
  have hℓ' : Tendsto (fun n : ℕ => (((ℓn n).toNat : ℕ) : ℝ) / sn n) atTop (𝓝 τ) := by
    refine hℓ.congr' ?_
    filter_upwards [hpos] with n hn
    have h0 : 0 < ℓn n := by
      have : (0 : ℝ) < (ℓn n : ℝ) := by
        by_contra hneg
        have : (ℓn n : ℝ) ≤ 0 := not_lt.1 hneg
        have := div_nonpos_of_nonpos_of_nonneg this (hs n).le
        linarith
      exact_mod_cast this
    have : (((ℓn n).toNat : ℕ) : ℝ) = (ℓn n : ℝ) := by
      have := Int.toNat_of_nonneg h0.le
      exact_mod_cast this
    rw [this]
  -- the function R
  obtain ⟨K, hK0, -, hKl⟩ := loc_lip hβ0 hβ1
  obtain ⟨C0, u1, hC0, hRa⟩ := lp_R_asymp hβ0 hβ1
  have hb : 0 < 2 * -Real.log β := by
    have := Real.log_neg hβ0 hβ1
    linarith
  have hRc : Continuous (fun u : ℝ => rW (emaW β) (Real.exp u)) :=
    continuous_iff_continuousAt.2 fun u => (lp_R_deriv hβ0 hβ1 u).continuousAt
  have habs := lp_abs (R := fun u : ℝ => rW (emaW β) (Real.exp u)) (b := 2 * -Real.log β)
    (K := K) (C0 := C0) (u1 := u1) (τ := τ) (φ := φ) hb hK0 hC0 hRc
    (lp_R_mono hβ0 hβ1).monotone (fun x y => hKl y x)
    (fun u hu => by
      have := hRa u hu
      have e : u / (2 * -Real.log β) = 1 / (2 * -Real.log β) * u := by ring
      rw [e]; exact this)
    hs hsT hℓ' hφc hφs hφsupp
  refine habs.congr' ?_
  filter_upwards [hpos] with n hn
  have h0 : 0 < ℓn n := by
    have : (0 : ℝ) < (ℓn n : ℝ) := by
      by_contra hneg
      have : (ℓn n : ℝ) ≤ 0 := not_lt.1 hneg
      have := div_nonpos_of_nonpos_of_nonneg this (hs n).le
      linarith
    exact_mod_cast this
  have hcast : ((ℓn n).toNat : ℤ) = ℓn n := Int.toNat_of_nonneg h0.le
  have := lp_transform hβ0 hβ1 (ℓn n).toNat (hs n) hφc hφs hφsupp
    (fun u : ℝ => rW (emaW β) (Real.exp u)) (fun _ => rfl)
  rw [hcast] at this
  rw [this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only []
  have e : (2 : ℝ) * ((ℓn n).toNat : ℝ) * -Real.log β = ((ℓn n).toNat : ℝ) * (2 * -Real.log β) := by
    ring
  rw [e]


/-- `lem:app-pl-localization`, part (iii), case `ρ₀ ∈ (0,∞)` (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Localization of the lag kernel]\label{lem:app-pl-localization}
\begin{enumerate}[label=(\roman*)]
\item For $\ell\ge0$, with $t\defeq\log(\bmom^{2\ell}q_2/q_1)$,
\[
\mathsf D_\ell(m_1,m_2)=\frac{r_\bmom(q_1e^t)-r_\bmom(q_1)}{2\sinh(t/2)},\]
\[
\mathsf D_\ell\le C\min(m_1,m_2,1)^{1/2}\big(1+\abs{m_1-m_2+\ell}\big)e^{-\abs{\log\bmom}\abs{m_1-m_2+\ell}} .
\]
\item For every $\tau_0>0$ there is $c>0$ such that $\Delta^N_\ell\ge c$ for all $\ell\ge\tau_0\gamma$, all
$m_1,m_2\in(0,\gamma)$ and all large $\gamma$.
\item Let $n\to\infty$ with $\gamma/n\to\rho_0\in(0,\infty]$, and let $\ell$ be integers with $\ell/n\to\tau>0$. For every
continuous $\varphi$ with compact support in $(0,\rho_0)^2$,
\[
\int\!\!\int\varphi\Big(\frac{m_1}n,\frac{m_2}n\Big)\frac{\mathsf D_\ell(m_1,m_2)}{\pi^2n\,E(m_1)E(m_2)}\,\dif m_1\,\dif m_2\longrightarrow\int\varphi(r,r+\tau)\,\dif r .
\]
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_localization_iii_fin {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (γn : ℕ → ℝ) (ℓn : ℕ → ℤ) (sn : ℕ → ℝ) (hs : ∀ n, 0 < sn n)
    (hsT : Tendsto sn atTop atTop) {ρ₀ τ : ℝ} (hρ₀ : 0 < ρ₀) (hτ : 0 < τ)
    (hγ : Tendsto (fun n : ℕ => γn n / sn n) atTop (𝓝 ρ₀))
    (hℓ : Tendsto (fun n : ℕ => (ℓn n : ℝ) / sn n) atTop (𝓝 τ))
    (φ : ℝ × ℝ → ℝ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hφsupp : tsupport φ ⊆ Ioo 0 ρ₀ ×ˢ Ioo 0 ρ₀) :
    (∀ n : ℕ, Integrable (fun p : ℝ × ℝ => φ (p.1 / sn n, p.2 / sn n) *
        DLag β (Qm β p.1) (Qm β p.2) (ℓn n) /
          (Real.pi ^ 2 * sn n * Efun β p.1 * Efun β p.2))) ∧
    Tendsto (fun n : ℕ => ∫ p : ℝ × ℝ, φ (p.1 / sn n, p.2 / sn n) *
        DLag β (Qm β p.1) (Qm β p.2) (ℓn n) /
          (Real.pi ^ 2 * sn n * Efun β p.1 * Efun β p.2)) atTop
      (𝓝 (∫ r : ℝ, φ (r, r + τ))) :=
  lp_core hβ0 hβ1 ℓn sn hs hsT hτ hℓ φ hφc hφs
    (hφsupp.trans (Set.prod_mono Set.Ioo_subset_Ioi_self Set.Ioo_subset_Ioi_self))

/-- `lem:app-pl-localization`, part (iii), case `ρ₀ = ∞` (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Localization of the lag kernel]\label{lem:app-pl-localization}
\begin{enumerate}[label=(\roman*)]
\item For $\ell\ge0$, with $t\defeq\log(\bmom^{2\ell}q_2/q_1)$,
\[
\mathsf D_\ell(m_1,m_2)=\frac{r_\bmom(q_1e^t)-r_\bmom(q_1)}{2\sinh(t/2)},\]
\[
\mathsf D_\ell\le C\min(m_1,m_2,1)^{1/2}\big(1+\abs{m_1-m_2+\ell}\big)e^{-\abs{\log\bmom}\abs{m_1-m_2+\ell}} .
\]
\item For every $\tau_0>0$ there is $c>0$ such that $\Delta^N_\ell\ge c$ for all $\ell\ge\tau_0\gamma$, all
$m_1,m_2\in(0,\gamma)$ and all large $\gamma$.
\item Let $n\to\infty$ with $\gamma/n\to\rho_0\in(0,\infty]$, and let $\ell$ be integers with $\ell/n\to\tau>0$. For every
continuous $\varphi$ with compact support in $(0,\rho_0)^2$,
\[
\int\!\!\int\varphi\Big(\frac{m_1}n,\frac{m_2}n\Big)\frac{\mathsf D_\ell(m_1,m_2)}{\pi^2n\,E(m_1)E(m_2)}\,\dif m_1\,\dif m_2\longrightarrow\int\varphi(r,r+\tau)\,\dif r .
\]
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_localization_iii_top {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (γn : ℕ → ℝ) (ℓn : ℕ → ℤ) (sn : ℕ → ℝ) (hs : ∀ n, 0 < sn n)
    (hsT : Tendsto sn atTop atTop) {τ : ℝ} (hτ : 0 < τ)
    (hγ : Tendsto (fun n : ℕ => γn n / sn n) atTop atTop)
    (hℓ : Tendsto (fun n : ℕ => (ℓn n : ℝ) / sn n) atTop (𝓝 τ))
    (φ : ℝ × ℝ → ℝ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hφsupp : tsupport φ ⊆ Ioi 0 ×ˢ Ioi 0) :
    (∀ n : ℕ, Integrable (fun p : ℝ × ℝ => φ (p.1 / sn n, p.2 / sn n) *
        DLag β (Qm β p.1) (Qm β p.2) (ℓn n) /
          (Real.pi ^ 2 * sn n * Efun β p.1 * Efun β p.2))) ∧
    Tendsto (fun n : ℕ => ∫ p : ℝ × ℝ, φ (p.1 / sn n, p.2 / sn n) *
        DLag β (Qm β p.1) (Qm β p.2) (ℓn n) /
          (Real.pi ^ 2 * sn n * Efun β p.1 * Efun β p.2)) atTop
      (𝓝 (∫ r : ℝ, φ (r, r + τ))) :=
  lp_core hβ0 hβ1 ℓn sn hs hsT hτ hℓ φ hφc hφs hφsupp

private lemma age_split {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Q : ℝ} (hQ : 0 < Q) :
    ∃ N : ℕ, (∀ j, j < N → 1 ≤ emaW β j ^ 2 * Q) ∧ (∀ j, N ≤ j → emaW β j ^ 2 * Q < 1) := by
  classical
  have hε : 0 < 1 / ((1 - β) ^ 2 * Q) := by
    have : 0 < 1 - β := by linarith
    positivity
  obtain ⟨j0, hj0⟩ := exists_pow_lt_of_lt_one hε hβ1
  have hex : ∃ j : ℕ, emaW β j ^ 2 * Q < 1 := by
    refine ⟨j0, ?_⟩
    have h1 : 0 < 1 - β := by linarith
    have hb1 : β ^ j0 ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
    have hb0 : 0 < β ^ j0 := pow_pos hβ0 j0
    have h2 : (1 - β) ^ 2 * Q * β ^ j0 < 1 := by
      have := mul_lt_mul_of_pos_left hj0 (by positivity : 0 < (1 - β) ^ 2 * Q)
      rwa [mul_one_div_cancel (by positivity)] at this
    have e : emaW β j0 ^ 2 * Q = (1 - β) ^ 2 * Q * (β ^ j0) ^ 2 := by
      unfold emaW; ring
    rw [e]
    calc (1 - β) ^ 2 * Q * (β ^ j0) ^ 2 ≤ (1 - β) ^ 2 * Q * β ^ j0 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith
      _ < 1 := h2
  refine ⟨Nat.find hex, fun j hj => ?_, fun j hj => ?_⟩
  · exact not_lt.1 (Nat.find_min hex hj)
  · have h := Nat.find_spec hex
    have hw : emaW β j ≤ emaW β (Nat.find hex) := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
      rw [vk_emaW_add]
      exact mul_le_of_le_one_left (vk_emaW_pos hβ0 hβ1 _).le (pow_le_one₀ hβ0.le hβ1.le)
    have h0 := (vk_emaW_pos hβ0 hβ1 j).le
    calc emaW β j ^ 2 * Q ≤ emaW β (Nat.find hex) ^ 2 * Q :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 hw 2) hQ.le
      _ < 1 := h

private lemma age_sum_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Q : ℝ} (hQ : 0 < Q)
    (h : ℝ → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : ∀ x, 1 ≤ x → |h x| ≤ a / Real.sqrt x)
    (h2 : ∀ x, 0 ≤ x → x < 1 → |h x| ≤ b * Real.sqrt x) :
    Summable (fun j : ℕ => h (emaW β j ^ 2 * Q)) ∧
      |∑' j : ℕ, h (emaW β j ^ 2 * Q)| ≤ (a + b) / (1 - β) := by
  obtain ⟨N, hN1, hN2⟩ := age_split hβ0 hβ1 hQ
  have hβn : 0 ≤ β := hβ0.le
  set B : ℕ → ℝ := fun j => if j < N then a * β ^ (N - 1 - j) else b * β ^ (j - N) with hBdef
  have hbound : ∀ j, ‖h (emaW β j ^ 2 * Q)‖ ≤ B j := by
    intro j
    rw [Real.norm_eq_abs]
    by_cases hj : j < N
    · simp only [hBdef, if_pos hj]
      have hx := hN1 j hj
      refine (h1 _ hx).trans ?_
      obtain ⟨d, hd⟩ : ∃ d, N - 1 - j = d := ⟨_, rfl⟩
      rw [hd]
      have hNj : N - 1 = j + d := by omega
      have hNq := hN1 (N - 1) (by omega)
      rw [hNj, vk_emaW_add] at hNq
      have hs : 1 ≤ Real.sqrt (emaW β j ^ 2 * Q) * β ^ d := by
        have h3 : Real.sqrt 1 ≤ Real.sqrt ((β ^ d * emaW β j) ^ 2 * Q) := Real.sqrt_le_sqrt hNq
        have e : (β ^ d * emaW β j) ^ 2 * Q = (β ^ d) ^ 2 * (emaW β j ^ 2 * Q) := by ring
        rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hβn d), Real.sqrt_one] at h3
        linarith
      have hpos : 0 < Real.sqrt (emaW β j ^ 2 * Q) := Real.sqrt_pos.2 (by linarith)
      rw [div_le_iff₀ hpos]
      nlinarith
    · simp only [hBdef, if_neg hj]
      have hj' : N ≤ j := not_lt.1 hj
      have hx := hN2 j hj'
      have hx0 : 0 ≤ emaW β j ^ 2 * Q := mul_nonneg (sq_nonneg _) hQ.le
      refine (h2 _ hx0 hx).trans ?_
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj'
      rw [Nat.add_sub_cancel_left]
      apply mul_le_mul_of_nonneg_left _ hb
      rw [vk_emaW_add]
      have e : (β ^ d * emaW β N) ^ 2 * Q = (β ^ d) ^ 2 * (emaW β N ^ 2 * Q) := by ring
      rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hβn d)]
      have h5 : Real.sqrt (emaW β N ^ 2 * Q) ≤ 1 := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (hN2 N le_rfl).le
      exact mul_le_of_le_one_right (pow_nonneg hβn d) h5
  have hgeo : Summable (fun i : ℕ => β ^ i) := summable_geometric_of_lt_one hβn hβ1
  have hBs : Summable B := by
    rw [← summable_nat_add_iff N]
    have e : (fun i : ℕ => B (i + N)) = fun i => b * β ^ i := by
      funext i
      simp [hBdef]
    rw [e]
    exact hgeo.mul_left b
  have hsumm : Summable (fun j : ℕ => h (emaW β j ^ 2 * Q)) :=
    Summable.of_norm_bounded hBs hbound
  refine ⟨hsumm, ?_⟩
  have hB1 : |∑' j : ℕ, h (emaW β j ^ 2 * Q)| ≤ ∑' j, B j := by
    have := tsum_of_norm_bounded hBs.hasSum hbound
    rwa [Real.norm_eq_abs] at this
  refine hB1.trans ?_
  rw [← hBs.sum_add_tsum_nat_add N]
  have e1 : ∑ i ∈ Finset.range N, B i = a * ∑ i ∈ Finset.range N, β ^ i := by
    rw [Finset.mul_sum, ← Finset.sum_range_reflect (fun i => a * β ^ i) N]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [hBdef, Finset.mem_range.1 hi]
  have e2 : ∑' i : ℕ, B (i + N) = b * (1 - β)⁻¹ := by
    have e : (fun i : ℕ => B (i + N)) = fun i => b * β ^ i := by
      funext i
      simp [hBdef]
    rw [e, tsum_mul_left, tsum_geometric_of_lt_one hβn hβ1]
  have e3 : ∑ i ∈ Finset.range N, β ^ i ≤ (1 - β)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hβn hβ1]
    exact hgeo.sum_le_tsum _ (fun i _ => pow_nonneg hβn i)
  rw [e1, e2]
  have : (a + b) / (1 - β) = a * (1 - β)⁻¹ + b * (1 - β)⁻¹ := by ring
  rw [this]
  have := mul_le_mul_of_nonneg_left e3 ha
  linarith

private lemma age_term_abs {β q : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hq : 0 ≤ q) (g : ℝ) (a : ℕ) :
    |emaW β a * g / (1 + emaW β a ^ 2 * q * g ^ 2)| =
      emaW β a * |g| / (1 + emaW β a ^ 2 * q * g ^ 2) := by
  rw [abs_div, abs_mul, abs_of_nonneg (vk_emaW_pos hβ0 hβ1 a).le,
    abs_of_pos (by positivity : 0 < 1 + emaW β a ^ 2 * q * g ^ 2)]

private lemma age_term_summable {β q : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hq : 0 ≤ q) (g : ℝ) :
    Summable (fun a : ℕ => emaW β a * g / (1 + emaW β a ^ 2 * q * g ^ 2)) := by
  refine Summable.of_norm_bounded (((vk_weightSeq hβ0 hβ1).2.1).mul_right |g|) fun a => ?_
  rw [Real.norm_eq_abs, age_term_abs hβ0 hβ1 hq]
  exact div_le_self (mul_nonneg (vk_emaW_pos hβ0 hβ1 a).le (abs_nonneg g))
    (by have := mul_nonneg (mul_nonneg (sq_nonneg (emaW β a)) hq) (sq_nonneg g); linarith)

private lemma age_abs_le {β q : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hq : 0 ≤ q) (g : ℝ) : |Zg β g q| ≤ Real.sqrt q * |g| := by
  have hs := age_term_summable hβ0 hβ1 hq g
  unfold Zg
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg q)]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg q)
  calc |∑' a : ℕ, emaW β a * g / (1 + emaW β a ^ 2 * q * g ^ 2)|
      ≤ ∑' a : ℕ, |emaW β a * g / (1 + emaW β a ^ 2 * q * g ^ 2)| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' a : ℕ, emaW β a * |g| := by
      apply hs.abs.tsum_le_tsum _ (((vk_weightSeq hβ0 hβ1).2.1).mul_right |g|)
      intro a
      rw [age_term_abs hβ0 hβ1 hq]
      exact div_le_self (mul_nonneg (vk_emaW_pos hβ0 hβ1 a).le (abs_nonneg g))
        (by have := mul_nonneg (mul_nonneg (sq_nonneg (emaW β a)) hq) (sq_nonneg g); linarith)
    _ = |g| := by rw [tsum_mul_right, tsum_emaW hβ0.le hβ1, one_mul]

private lemma age_measurable (β q : ℝ) : Measurable (fun g : ℝ => Zg β g q) := by
  unfold Zg
  exact measurable_const.mul (Measurable.tsum (fun a => by fun_prop))

private lemma age_sq_le {β q : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hq : 0 ≤ q) (g : ℝ) : Zg β g q ^ 2 ≤ q * g ^ 2 := by
  have h := pow_le_pow_left₀ (abs_nonneg (Zg β g q)) (age_abs_le hβ0 hβ1 hq g) 2
  simpa only [sq_abs, mul_pow, Real.sq_sqrt hq] using h

private lemma age_uniform {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {q : ℝ} (hq : 0 < q) (g : ℝ) : |Zg β g q| ≤ 2 / (1 - β) := by
  by_cases hg : g = 0
  · simp [hg, Zg, le_of_lt (by positivity : 0 < 2 / (1 - β))]
  have hQ : 0 < q * g ^ 2 := mul_pos hq (sq_pos_of_ne_zero hg)
  have h1 : ∀ x : ℝ, 1 ≤ x → |Real.sqrt x / (1 + x)| ≤ 1 / Real.sqrt x := by
    intro x hx
    have hx0 : 0 < x := by linarith
    rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (Real.sqrt_pos.2 hx0)]
    nlinarith [Real.sq_sqrt hx0.le]
  have h2 : ∀ x : ℝ, 0 ≤ x → x < 1 → |Real.sqrt x / (1 + x)| ≤ 1 * Real.sqrt x := by
    intro x hx _
    rw [one_mul, abs_of_nonneg (by positivity)]
    exact div_le_self (by positivity) (by linarith)
  obtain ⟨hs, hb⟩ := age_sum_bound hβ0 hβ1 hQ (fun x => Real.sqrt x / (1 + x))
    zero_le_one zero_le_one h1 h2
  have he : ∀ a : ℕ,
      Real.sqrt q * |emaW β a * g / (1 + emaW β a ^ 2 * q * g ^ 2)| =
        Real.sqrt (emaW β a ^ 2 * (q * g ^ 2)) / (1 + emaW β a ^ 2 * (q * g ^ 2)) := by
    intro a
    rw [age_term_abs hβ0 hβ1 hq.le, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (vk_emaW_pos hβ0 hβ1 a).le, Real.sqrt_mul hq.le, Real.sqrt_sq_eq_abs]
    ring
  calc |Zg β g q|
      ≤ Real.sqrt q * ∑' a : ℕ, |emaW β a * g / (1 + emaW β a ^ 2 * q * g ^ 2)| := by
        unfold Zg
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg q)]
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg q)
        simpa only [Real.norm_eq_abs] using
          norm_tsum_le_tsum_norm (age_term_summable hβ0 hβ1 hq.le g).norm
    _ = ∑' a : ℕ, Real.sqrt (emaW β a ^ 2 * (q * g ^ 2)) / (1 + emaW β a ^ 2 * (q * g ^ 2)) := by
        rw [← tsum_mul_left]
        exact tsum_congr he
    _ ≤ 2 / (1 - β) := by
        have := (le_abs_self _).trans hb
        norm_num at this ⊢
        exact this

/-- `lem:app-pl-age`, part (i) (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Age factorization]\label{lem:app-pl-age}
For real $g$ and $q>0$ put $\mathcal Z_g(q)\defeq\sqrt q\sum_{a\ge0}\emaw ag\,(1+\emaw a^2qg^2)^{-1}$.
\begin{enumerate}[label=(\roman*)]
\item $\abs{\mathcal Z_g(q)}\le C_\bmom$ and $\EE\,\mathcal Z_g(q)^2\le q$, for $g\sim\mathcal N(0,1)$.
\item For $m_0>0$ and $\mathcal A_g(m)\defeq\mathcal Z_g(Q_m)/E(m)$,
\[
\sup_{t\ge m_0}\Big|\int_{m_0}^t\big(\mathcal A_g(m)-\pi\sign(g)\big)\,\dif m\Big|\le C_{\bmom,m_0}\big(1+\abs{\log\abs g}\big)\qquad(g\ne0).
\]
\item $\sum_{\ell\in\mathbb Z}\mathsf D_\ell(m_1,m_2)=\EE\big[\mathcal Z_g(Q_{m_1})\mathcal Z_g(Q_{m_2})\big]$.
\item The flat coefficient
$\mathfrak v^{\mathrm{flat}}_i\defeq\EE\big[\big(\frac1\pi\int_0^\gamma W_i(m)\mathcal Z_g(Q_m)\,\dif m\big)^2\big]$ satisfies
$0\le\mathfrak v^{\mathrm{flat}}_i\le\mathfrak v_i(0)$, and it is the integral of \cref{eqn:app-pl-vol-zero}
summed over the lags with every $\Delta^N_\ell$ replaced by one.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_age_i {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∃ C : ℝ, ∀ q g : ℝ, 0 < q → |Zg β g q| ≤ C) ∧
    ∀ q : ℝ, 0 < q →
      Integrable (fun g : ℝ => Zg β g q ^ 2) (gaussianReal 0 1) ∧
        ∫ g : ℝ, Zg β g q ^ 2 ∂(gaussianReal 0 1) ≤ q := by
  refine ⟨⟨2 / (1 - β), fun q g hq => age_uniform hβ0 hβ1 hq g⟩, ?_⟩
  intro q hq
  have hi : Integrable (fun g : ℝ => q * g ^ 2) (gaussianReal 0 1) :=
    (Muon.Foundations.gaussian_integrable_pow 2).const_mul q
  have hZ : Integrable (fun g : ℝ => Zg β g q ^ 2) (gaussianReal 0 1) := by
    refine hi.mono' ((age_measurable β q).pow_const 2).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact age_sq_le hβ0 hβ1 hq.le g
  refine ⟨hZ, ?_⟩
  calc ∫ g : ℝ, Zg β g q ^ 2 ∂(gaussianReal 0 1)
      ≤ ∫ g : ℝ, q * g ^ 2 ∂(gaussianReal 0 1) :=
        integral_mono hZ hi (age_sq_le hβ0 hβ1 hq.le)
    _ = q := by rw [integral_const_mul, Muon.Foundations.gaussian_moment_two, mul_one]

private lemma age_nRes {β : ℝ} {Q : ℝ} {N : ℕ} (h1 : ∀ j, j < N → 1 ≤ emaW β j ^ 2 * Q)
    (h2 : ∀ j, N ≤ j → emaW β j ^ 2 * Q < 1) : nRes β Q = N := by
  unfold nRes
  have : {j : ℕ | 1 ≤ emaW β j ^ 2 * Q} = ((Finset.range N : Finset ℕ) : Set ℕ) := by
    ext j
    simp only [Set.mem_setOf_eq, Finset.coe_range, Set.mem_Iio]
    constructor
    · intro h
      by_contra hc
      exact absurd (h2 j (not_lt.1 hc)) (not_lt.2 h)
    · exact h1 j
  rw [this, Set.ncard_coe_finset, Finset.card_range]

private lemma age_arctan_le {u : ℝ} (hu : 0 ≤ u) : Real.arctan u ≤ u := by
  have h0 : 0 ≤ Real.arctan u := Real.arctan_nonneg.2 hu
  have h1 := Real.arctan_lt_pi_div_two u
  have := Real.le_tan h0 h1
  rwa [Real.tan_arctan] at this

private lemma age_arctan_summable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {Q : ℝ} (hQ : 0 ≤ Q) : Summable (fun a : ℕ => 2 * Real.arctan (emaW β a * Real.sqrt Q)) := by
  refine Summable.of_nonneg_of_le (fun a => ?_) (fun a => ?_)
    ((((vk_weightSeq hβ0 hβ1).2.1).mul_right (Real.sqrt Q)).mul_left 2)
  · exact mul_nonneg (by norm_num) (Real.arctan_nonneg.2 (by have := vk_emaW_pos hβ0 hβ1 a; positivity))
  · exact mul_le_mul_of_nonneg_left (age_arctan_le (by have := vk_emaW_pos hβ0 hβ1 a; positivity)) (by norm_num)

private lemma age_arctan_count {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {Q : ℝ} (hQ : 0 < Q) :
    |(∑' a : ℕ, 2 * Real.arctan (emaW β a * Real.sqrt Q)) - Real.pi * (nRes β Q : ℝ)| ≤
      4 / (1 - β) := by
  classical
  set h : ℝ → ℝ := fun x => 2 * Real.arctan (Real.sqrt x) - if 1 ≤ x then Real.pi else 0
  obtain ⟨hs, hb⟩ := age_sum_bound hβ0 hβ1 hQ h (a := 2) (b := 2) (by norm_num) (by norm_num)
    (fun x hx => by
      have hx0 : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
      have h1 := Real.arctan_inv_of_pos hx0
      have h2 := age_arctan_le (inv_nonneg.2 hx0.le)
      have h3 := Real.arctan_lt_pi_div_two (Real.sqrt x)
      dsimp [h]
      rw [if_pos hx, abs_of_nonpos (by linarith)]
      rw [div_eq_mul_inv]
      linarith)
    (fun x hx0 hx1 => by
      dsimp [h]
      rw [if_neg (not_le.2 hx1), sub_zero, abs_of_nonneg (by
        have := Real.arctan_nonneg.2 (Real.sqrt_nonneg x); positivity)]
      exact mul_le_mul_of_nonneg_left (age_arctan_le (Real.sqrt_nonneg x)) (by norm_num))
  obtain ⟨N, hN1, hN2⟩ := age_split hβ0 hβ1 hQ
  have hn := age_nRes hN1 hN2
  have hi : Summable (fun a : ℕ => if 1 ≤ emaW β a ^ 2 * Q then Real.pi else 0) := by
    refine summable_of_ne_finset_zero (s := Finset.range N) fun a ha => ?_
    rw [if_neg (not_le.2 (hN2 a (not_lt.1 (Finset.mem_range.not.1 ha))))]
  have he : ∑' a : ℕ, (if 1 ≤ emaW β a ^ 2 * Q then Real.pi else 0) = Real.pi * (nRes β Q : ℝ) := by
    rw [tsum_eq_sum (s := Finset.range N)]
    · rw [Finset.sum_congr rfl (g := fun _ => Real.pi)]
      · simp [hn, mul_comm]
      · intro a ha
        rw [if_pos (hN1 a (Finset.mem_range.1 ha))]
    · intro a ha
      rw [if_neg (not_le.2 (hN2 a (not_lt.1 (Finset.mem_range.not.1 ha))))]
  have hroot : ∀ a : ℕ, Real.sqrt (emaW β a ^ 2 * Q) = emaW β a * Real.sqrt Q := by
    intro a
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (vk_emaW_pos hβ0 hβ1 a).le]
  have hh : (∑' a : ℕ, h (emaW β a ^ 2 * Q)) =
      (∑' a : ℕ, 2 * Real.arctan (emaW β a * Real.sqrt Q)) - Real.pi * (nRes β Q : ℝ) := by
    simp only [h, hroot]
    rw [(age_arctan_summable hβ0 hβ1 hQ.le).tsum_sub hi, he]
  rw [hh] at hb
  norm_num at hb ⊢
  exact hb

private lemma age_arctan_r {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℝ, 0 < Q →
      |(∑' a : ℕ, 2 * Real.arctan (emaW β a * Real.sqrt Q)) - Real.pi * rW (emaW β) Q| ≤ C := by
  obtain ⟨c, C, hc, hcC, hC⟩ := lem_app_pl_weights_iii hβ0 hβ1
  have hmono := (lem_app_de_scalar_iii (vk_weightSeq hβ0 hβ1)).2.1.monotoneOn
  have hn : ∀ Q : ℝ, 0 < Q → Q ≤ 1 → nRes β Q = 0 := by
    intro Q hQ hQ1
    apply age_nRes (N := 0) (fun _ hj => by omega)
    intro a _
    have hw0 := vk_emaW_pos hβ0 hβ1 a
    have hw1 : emaW β a < 1 := by
      unfold emaW
      have hpow := pow_le_one₀ hβ0.le hβ1.le (n := a)
      nlinarith [pow_nonneg hβ0.le a]
    nlinarith [sq_nonneg (emaW β a), mul_le_mul_of_nonneg_left hQ1 (sq_nonneg (emaW β a))]
  have hC0 : 0 ≤ C := hc.le.trans hcC
  have hR : ∀ Q : ℝ, 0 < Q → |rW (emaW β) Q - (nRes β Q : ℝ)| ≤ C := by
    intro Q hQ
    by_cases hQ1 : 1 ≤ Q
    · exact (hC Q hQ1).1
    · have hQ1 := (not_le.1 hQ1).le
      rw [hn Q hQ hQ1, Nat.cast_zero, sub_zero, abs_of_nonneg (loc_Qm_r hβ0 hβ1 hQ).1.le]
      have h1 := (hC 1 le_rfl).1
      rw [hn 1 one_pos le_rfl, Nat.cast_zero, sub_zero] at h1
      exact (hmono (Set.mem_Ici.2 hQ.le) (Set.mem_Ici.2 zero_le_one) hQ1).trans ((le_abs_self _).trans h1)
  refine ⟨4 / (1 - β) + Real.pi * C, by positivity, fun Q hQ => ?_⟩
  have h1 := age_arctan_count hβ0 hβ1 hQ
  have h2 := hR Q hQ
  calc |(∑' a : ℕ, 2 * Real.arctan (emaW β a * Real.sqrt Q)) - Real.pi * rW (emaW β) Q|
      = |((∑' a : ℕ, 2 * Real.arctan (emaW β a * Real.sqrt Q)) - Real.pi * (nRes β Q : ℝ)) +
          Real.pi * ((nRes β Q : ℝ) - rW (emaW β) Q)| := by congr 1; ring
    _ ≤ |(∑' a : ℕ, 2 * Real.arctan (emaW β a * Real.sqrt Q)) - Real.pi * (nRes β Q : ℝ)| +
          |Real.pi * ((nRes β Q : ℝ) - rW (emaW β) Q)| := abs_add_le _ _
    _ ≤ 4 / (1 - β) + Real.pi * C := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      exact add_le_add h1 (mul_le_mul_of_nonneg_left (by simpa only [abs_sub_comm] using h2) Real.pi_pos.le)

private lemma age_Z_cont {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (g : ℝ) :
    ContinuousOn (Zg β g) (Ici 0) := by
  unfold Zg
  refine Real.continuous_sqrt.continuousOn.mul (continuousOn_tsum (fun a => ?_)
    (((vk_weightSeq hβ0 hβ1).2.1).mul_right |g|) (fun a q hq => ?_))
  · intro q hq
    apply ContinuousAt.continuousWithinAt
    have hq0 : 0 ≤ q := hq
    have hden : 1 + emaW β a ^ 2 * q * g ^ 2 ≠ 0 := by positivity
    fun_prop (disch := assumption)
  · rw [Real.norm_eq_abs, age_term_abs hβ0 hβ1 hq]
    exact div_le_self (mul_nonneg (vk_emaW_pos hβ0 hβ1 a).le (abs_nonneg g))
      (by have := mul_nonneg (mul_nonneg (sq_nonneg (emaW β a)) hq) (sq_nonneg g); linarith)

private lemma age_Z_sign (β g q : ℝ) : Zg β g q = Real.sign g * Zg β |g| q := by
  rcases lt_trichotomy g 0 with hg | rfl | hg
  · simp only [abs_of_neg hg, Real.sign_of_neg hg, neg_one_mul, Zg,
      neg_sq, mul_neg, neg_div, tsum_neg, neg_neg]
  · simp [Zg]
  · simp [abs_of_pos hg, Real.sign_of_pos hg]

private lemma age_inner {w a b z : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, (Real.sqrt x)⁻¹ * (w * z / (1 + w ^ 2 * x * z ^ 2)) =
      2 * Real.arctan (w * z * Real.sqrt b) - 2 * Real.arctan (w * z * Real.sqrt a) := by
  have hd : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun x : ℝ => 2 * Real.arctan (w * z * Real.sqrt x))
      ((Real.sqrt x)⁻¹ * (w * z / (1 + w ^ 2 * x * z ^ 2))) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have h1 := ((Real.hasDerivAt_sqrt hx0.ne').const_mul (w * z)).arctan.const_mul 2
    convert h1 using 1
    have hss := Real.sq_sqrt hx0.le
    have e : 1 + (w * z * Real.sqrt x) ^ 2 = 1 + w ^ 2 * x * z ^ 2 := by
      rw [mul_pow, hss]; ring
    rw [e]
    field_simp
  have hc : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹ * (w * z / (1 + w ^ 2 * x * z ^ 2))) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have hsq : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx0).ne'
    have hden : 1 + w ^ 2 * x * z ^ 2 ≠ 0 := by positivity
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable

private lemma age_q_integral_pos {β a b z : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (ha : 0 < a) (hab : a ≤ b) (hz : 0 ≤ z) :
    ∫ x in a..b, Zg β z x / x =
      (∑' j : ℕ, 2 * Real.arctan (emaW β j * z * Real.sqrt b)) -
        ∑' j : ℕ, 2 * Real.arctan (emaW β j * z * Real.sqrt a) := by
  set F : ℕ → ℝ → ℝ := fun j x => (Real.sqrt x)⁻¹ * (emaW β j * z / (1 + emaW β j ^ 2 * x * z ^ 2))
  set H : ℕ → ℝ → ℝ := fun j x => 2 * Real.arctan (emaW β j * z * Real.sqrt x)
  have hterm : ∀ j, ∫ x in a..b, F j x = H j b - H j a := fun j => age_inner ha hab
  have hFnn : ∀ j, ∀ x ∈ Ioc a b, 0 ≤ F j x := by
    intro j x hx
    have hx0 : 0 < x := ha.trans hx.1
    have hw := vk_emaW_pos hβ0 hβ1 j
    dsimp [F]; positivity
  have hFc : ∀ j, ContinuousOn (F j) (Icc a b) := by
    intro j x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx0).ne'
    have hd : 1 + emaW β j ^ 2 * x * z ^ 2 ≠ 0 := by positivity
    apply ContinuousAt.continuousWithinAt
    dsimp [F]; fun_prop (disch := assumption)
  have hFi : ∀ j, IntegrableOn (F j) (Ioc a b) := fun j =>
    (hFc j).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hnorm : ∀ j, ∫ x in Ioc a b, ‖F j x‖ = H j b - H j a := by
    intro j
    rw [← hterm j, intervalIntegral.integral_of_le hab]
    exact setIntegral_congr_fun measurableSet_Ioc (fun x hx => Real.norm_of_nonneg (hFnn j x hx))
  have hHs : ∀ x : ℝ, 0 ≤ x → Summable (fun j => H j x) := by
    intro x hx
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
      (((((vk_weightSeq hβ0 hβ1).2.1).mul_right z).mul_right (Real.sqrt x)).mul_left 2)
    · dsimp [H]
      have hw := vk_emaW_pos hβ0 hβ1 j
      exact mul_nonneg (by norm_num) (Real.arctan_nonneg.2 (by positivity))
    · dsimp [H]
      have hw := vk_emaW_pos hβ0 hβ1 j
      exact mul_le_mul_of_nonneg_left (age_arctan_le (by positivity)) (by norm_num)
  have hsumnorm : Summable (fun j => ∫ x in Ioc a b, ‖F j x‖) := by
    simp_rw [hnorm]
    exact (hHs b (ha.le.trans hab)).sub (hHs a ha.le)
  have he : ∀ x ∈ Ioc a b, Zg β z x / x = ∑' j, F j x := by
    intro x hx
    have hx0 : 0 < x := ha.trans hx.1
    unfold Zg
    rw [← tsum_mul_left, ← tsum_div_const]
    apply tsum_congr
    intro j
    dsimp [F]
    have hss := Real.sq_sqrt hx0.le
    have hs := (Real.sqrt_pos.2 hx0).ne'
    field_simp
    rw [hss]
    ring
  rw [intervalIntegral.integral_of_le hab]
  rw [setIntegral_congr_fun measurableSet_Ioc he,
    ← (hasSum_integral_of_summable_integral_norm hFi hsumnorm).tsum_eq]
  have ht : ∀ j, ∫ x in Ioc a b, F j x = H j b - H j a := by
    intro j
    rw [← intervalIntegral.integral_of_le hab, hterm]
  simp_rw [ht]
  exact (hHs b (ha.le.trans hab)).tsum_sub (hHs a ha.le)

private lemma age_r_deriv {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (rW (emaW β)) (deriv (rW (emaW β)) x) x ∧ 0 < deriv (rW (emaW β)) x := by
  have h := lem_app_de_scalar_iii (vk_weightSeq hβ0 hβ1)
  have hd := h.2.2.2.1 x hx
  refine ⟨hd.differentiableAt.hasDerivAt, ?_⟩
  rw [hd.deriv]
  exact h.2.2.2.2.1 x hx

private lemma age_cov {β m0 t : ℝ} (g : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hm0 : 0 < m0) (ht : m0 ≤ t) :
    IntervalIntegrable ((Ag β g)) volume m0 t ∧
    ∫ m in m0..t, (Ag β g) m = ∫ x in Qm β m0..Qm β t, Zg β g x / x := by
  obtain ⟨hq0, hr0⟩ := vk_Qm hβ0 hβ1 hm0
  obtain ⟨hqt, hrt⟩ := vk_Qm hβ0 hβ1 (lt_of_lt_of_le hm0 ht)
  have hle : Qm β m0 ≤ Qm β t := lp_Qm_mono hβ0 hβ1 hm0 (lt_of_lt_of_le hm0 ht) ht
  set q0 := Qm β m0
  set Qt := Qm β t
  have hderiv : ∀ x ∈ Icc q0 Qt, HasDerivWithinAt (rW (emaW β)) (deriv (rW (emaW β)) x) (Icc q0 Qt) x :=
    fun x hx => (age_r_deriv hβ0 hβ1 (lt_of_lt_of_le hq0 hx.1)).1.hasDerivWithinAt
  have hcont : ContinuousOn (rW (emaW β)) (Icc q0 Qt) := fun x hx => (hderiv x hx).continuousWithinAt
  have hinj : InjOn (rW (emaW β)) (Icc q0 Qt) :=
    ((lem_app_de_scalar_iii (vk_weightSeq hβ0 hβ1)).2.1.injOn).mono
      (fun x hx => Set.mem_Ici.2 (hq0.le.trans hx.1))
  have himg : rW (emaW β) '' Icc q0 Qt = Icc m0 t := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hmono := (lem_app_de_scalar_iii (vk_weightSeq hβ0 hβ1)).2.1
      constructor
      · rw [← hr0]
        exact hmono.monotoneOn (Set.mem_Ici.2 hq0.le) (Set.mem_Ici.2 (hq0.le.trans hx.1)) hx.1
      · rw [← hrt]
        exact hmono.monotoneOn (Set.mem_Ici.2 (hq0.le.trans hx.1)) (Set.mem_Ici.2 hqt.le) hx.2
    · have := intermediate_value_Icc hle hcont
      rwa [hr0, hrt] at this
  have hpt : ∀ x ∈ Icc q0 Qt, |deriv (rW (emaW β)) x| • (Ag β g) (rW (emaW β) x) =
      Zg β g x / x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hq0 hx.1
    obtain ⟨-, hdp⟩ := age_r_deriv hβ0 hβ1 hx0
    rw [smul_eq_mul, abs_of_pos hdp]
    unfold Ag Efun
    rw [(loc_Qm_r hβ0 hβ1 hx0).2]
    field_simp
  have hcts : ContinuousOn (fun x : ℝ => Zg β g x / x) (Icc q0 Qt) :=
    ((age_Z_cont hβ0 hβ1 g).mono (fun x hx => hq0.le.trans hx.1)).div continuousOn_id
      (fun x hx => (lt_of_lt_of_le hq0 hx.1).ne')
  have hint : IntegrableOn (fun x => |deriv (rW (emaW β)) x| • (Ag β g) (rW (emaW β) x)) (Icc q0 Qt) := by
    refine (hcts.integrableOn_Icc).congr_fun (fun x hx => (hpt x hx).symm) measurableSet_Icc
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc hderiv hinj ((Ag β g))
  rw [himg] at hiff
  have hI : IntegrableOn ((Ag β g)) (Icc m0 t) := hiff.2 hint
  refine ⟨?_, ?_⟩
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le ht).2 hI
  · have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hderiv hinj ((Ag β g))
    rw [himg] at h
    rw [intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc, h,
      intervalIntegral.integral_of_le hle, ← integral_Icc_eq_integral_Ioc]
    exact setIntegral_congr_fun measurableSet_Icc hpt

private lemma age_scaled_primitive {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℝ, g ≠ 0 → ∀ q : ℝ, 0 < q →
      |(∑' a : ℕ, 2 * Real.arctan (emaW β a * |g| * Real.sqrt q)) - Real.pi * rW (emaW β) q| ≤
        C * (1 + |Real.log (|g|)|) := by
  obtain ⟨C, hC0, hC⟩ := age_arctan_r hβ0 hβ1
  obtain ⟨K, hK0, -, hK⟩ := loc_lip hβ0 hβ1
  refine ⟨C + 2 * Real.pi * K, by positivity, fun g hg q hq => ?_⟩
  have hg2 : 0 < g ^ 2 := sq_pos_of_ne_zero hg
  have hqg : 0 < q * g ^ 2 := mul_pos hq hg2
  have hroot : ∀ a : ℕ, emaW β a * |g| * Real.sqrt q = emaW β a * Real.sqrt (q * g ^ 2) := by
    intro a
    rw [Real.sqrt_mul hq.le, Real.sqrt_sq_eq_abs]
    ring
  have h1 := hC (q * g ^ 2) hqg
  simp_rw [← hroot] at h1
  have h2 := hK (Real.log q) (Real.log (q * g ^ 2))
  rw [Real.exp_log hq, Real.exp_log hqg] at h2
  have he : |Real.log (q * g ^ 2) - Real.log q| = 2 * |Real.log (|g|)| := by
    rw [Real.log_mul hq.ne' hg2.ne', Real.log_pow, add_sub_cancel_left,
      abs_mul, Real.log_abs]
    norm_num
  rw [he] at h2
  have h3 : |Real.pi * (rW (emaW β) (q * g ^ 2) - rW (emaW β) q)| ≤
      2 * Real.pi * K * |Real.log (|g|)| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    have := mul_le_mul_of_nonneg_left h2 Real.pi_pos.le
    nlinarith
  calc |(∑' a : ℕ, 2 * Real.arctan (emaW β a * |g| * Real.sqrt q)) - Real.pi * rW (emaW β) q|
      = |((∑' a : ℕ, 2 * Real.arctan (emaW β a * |g| * Real.sqrt q)) - Real.pi * rW (emaW β) (q * g ^ 2)) +
          Real.pi * (rW (emaW β) (q * g ^ 2) - rW (emaW β) q)| := by congr 1; ring
    _ ≤ |(∑' a : ℕ, 2 * Real.arctan (emaW β a * |g| * Real.sqrt q)) - Real.pi * rW (emaW β) (q * g ^ 2)| +
        |Real.pi * (rW (emaW β) (q * g ^ 2) - rW (emaW β) q)| := abs_add_le _ _
    _ ≤ (C + 2 * Real.pi * K) * (1 + |Real.log (|g|)|) := by
      have := add_le_add h1 h3
      nlinarith [mul_nonneg hC0 (abs_nonneg (Real.log |g|)), mul_nonneg Real.pi_pos.le hK0]

/-- `lem:app-pl-age`, part (ii) (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Age factorization]\label{lem:app-pl-age}
For real $g$ and $q>0$ put $\mathcal Z_g(q)\defeq\sqrt q\sum_{a\ge0}\emaw ag\,(1+\emaw a^2qg^2)^{-1}$.
\begin{enumerate}[label=(\roman*)]
\item $\abs{\mathcal Z_g(q)}\le C_\bmom$ and $\EE\,\mathcal Z_g(q)^2\le q$, for $g\sim\mathcal N(0,1)$.
\item For $m_0>0$ and $\mathcal A_g(m)\defeq\mathcal Z_g(Q_m)/E(m)$,
\[
\sup_{t\ge m_0}\Big|\int_{m_0}^t\big(\mathcal A_g(m)-\pi\sign(g)\big)\,\dif m\Big|\le C_{\bmom,m_0}\big(1+\abs{\log\abs g}\big)\qquad(g\ne0).
\]
\item $\sum_{\ell\in\mathbb Z}\mathsf D_\ell(m_1,m_2)=\EE\big[\mathcal Z_g(Q_{m_1})\mathcal Z_g(Q_{m_2})\big]$.
\item The flat coefficient
$\mathfrak v^{\mathrm{flat}}_i\defeq\EE\big[\big(\frac1\pi\int_0^\gamma W_i(m)\mathcal Z_g(Q_m)\,\dif m\big)^2\big]$ satisfies
$0\le\mathfrak v^{\mathrm{flat}}_i\le\mathfrak v_i(0)$, and it is the integral of \cref{eqn:app-pl-vol-zero}
summed over the lags with every $\Delta^N_\ell$ replaced by one.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_age_ii {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ m₀ : ℝ, 0 < m₀ → ∃ C : ℝ, ∀ g : ℝ, g ≠ 0 → ∀ t : ℝ, m₀ ≤ t →
      IntervalIntegrable (Ag β g) volume m₀ t ∧
        |∫ m in m₀..t, (Ag β g m - Real.pi * Real.sign g)| ≤
          C * (1 + |Real.log (|g|)|) := by
  intro m₀ hm₀
  obtain ⟨C, hC0, hC⟩ := age_scaled_primitive hβ0 hβ1
  refine ⟨2 * C, fun g hg t ht => ?_⟩
  obtain ⟨hI, hcov⟩ := age_cov g hβ0 hβ1 hm₀ ht
  refine ⟨hI, ?_⟩
  obtain ⟨hq0, hr0⟩ := vk_Qm hβ0 hβ1 hm₀
  obtain ⟨hqt, hrt⟩ := vk_Qm hβ0 hβ1 (hm₀.trans_le ht)
  have hle := lp_Qm_mono hβ0 hβ1 hm₀ (hm₀.trans_le ht) ht
  have hqint : (∫ x in Qm β m₀..Qm β t, Zg β g x / x) =
      Real.sign g * ((∑' a : ℕ, 2 * Real.arctan (emaW β a * |g| * Real.sqrt (Qm β t))) -
        ∑' a : ℕ, 2 * Real.arctan (emaW β a * |g| * Real.sqrt (Qm β m₀))) := by
    calc (∫ x in Qm β m₀..Qm β t, Zg β g x / x)
        = ∫ x in Qm β m₀..Qm β t, Real.sign g * (Zg β |g| x / x) := by
          apply intervalIntegral.integral_congr
          intro x _
          dsimp only
          rw [age_Z_sign β g x]
          ring
      _ = _ := by rw [intervalIntegral.integral_const_mul,
        age_q_integral_pos hβ0 hβ1 hq0 hle (abs_nonneg g)]
  rw [intervalIntegral.integral_sub hI intervalIntegrable_const, hcov, hqint,
    intervalIntegral.integral_const, smul_eq_mul]
  have hsign : |Real.sign g| = 1 := by
    rcases Real.sign_apply_eq_of_ne_zero g hg with h | h <;> simp [h]
  have he : Real.sign g * ((∑' a : ℕ, 2 * Real.arctan (emaW β a * |g| * Real.sqrt (Qm β t))) -
        ∑' a : ℕ, 2 * Real.arctan (emaW β a * |g| * Real.sqrt (Qm β m₀))) -
      (t - m₀) * (Real.pi * Real.sign g) =
      Real.sign g * (((∑' a : ℕ, 2 * Real.arctan (emaW β a * |g| * Real.sqrt (Qm β t))) - Real.pi * rW (emaW β) (Qm β t)) -
        ((∑' a : ℕ, 2 * Real.arctan (emaW β a * |g| * Real.sqrt (Qm β m₀))) - Real.pi * rW (emaW β) (Qm β m₀))) := by
    rw [hr0, hrt]
    ring
  rw [he, abs_mul, hsign, one_mul]
  exact (abs_sub _ _).trans (by
    have h1 := hC g hg (Qm β t) hqt
    have h2 := hC g hg (Qm β m₀) hq0
    linarith)

private lemma age_lag_bijective : Function.Bijective
    (fun p : ℤ × ℕ => match p.1 with
      | Int.ofNat l => (p.2, p.2 + l)
      | Int.negSucc l => (p.2 + l + 1, p.2)) := by
  constructor
  · rintro ⟨l, a⟩ ⟨k, b⟩ h
    cases l with
    | ofNat l =>
        cases k with
        | ofNat k =>
            change (a, a + l) = (b, b + k) at h
            injection h with hab hs
            subst b
            have : l = k := Nat.add_left_cancel hs
            subst k
            rfl
        | negSucc k =>
            change (a, a + l) = (b + k + 1, b) at h
            injection h with h1 h2
            omega
    | negSucc l =>
        cases k with
        | ofNat k =>
            change (a + l + 1, a) = (b, b + k) at h
            injection h with h1 h2
            omega
        | negSucc k =>
            change (a + l + 1, a) = (b + k + 1, b) at h
            injection h with hs hab
            subst b
            have : l = k := by omega
            subst k
            rfl
  · rintro ⟨a, b⟩
    by_cases h : a ≤ b
    · refine ⟨(Int.ofNat (b - a), a), ?_⟩
      change (a, a + (b - a)) = (a, b)
      congr
      omega
    · refine ⟨(Int.negSucc (a - b - 1), b), ?_⟩
      change (b + (a - b - 1) + 1, b) = (a, b)
      congr
      omega

set_option maxHeartbeats 800000 in
-- The two nested summations, Gaussian domination, and lag reindexing need extra elaboration time.
/-- `lem:app-pl-age`, part (iii) (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Age factorization]\label{lem:app-pl-age}
For real $g$ and $q>0$ put $\mathcal Z_g(q)\defeq\sqrt q\sum_{a\ge0}\emaw ag\,(1+\emaw a^2qg^2)^{-1}$.
\begin{enumerate}[label=(\roman*)]
\item $\abs{\mathcal Z_g(q)}\le C_\bmom$ and $\EE\,\mathcal Z_g(q)^2\le q$, for $g\sim\mathcal N(0,1)$.
\item For $m_0>0$ and $\mathcal A_g(m)\defeq\mathcal Z_g(Q_m)/E(m)$,
\[
\sup_{t\ge m_0}\Big|\int_{m_0}^t\big(\mathcal A_g(m)-\pi\sign(g)\big)\,\dif m\Big|\le C_{\bmom,m_0}\big(1+\abs{\log\abs g}\big)\qquad(g\ne0).
\]
\item $\sum_{\ell\in\mathbb Z}\mathsf D_\ell(m_1,m_2)=\EE\big[\mathcal Z_g(Q_{m_1})\mathcal Z_g(Q_{m_2})\big]$.
\item The flat coefficient
$\mathfrak v^{\mathrm{flat}}_i\defeq\EE\big[\big(\frac1\pi\int_0^\gamma W_i(m)\mathcal Z_g(Q_m)\,\dif m\big)^2\big]$ satisfies
$0\le\mathfrak v^{\mathrm{flat}}_i\le\mathfrak v_i(0)$, and it is the integral of \cref{eqn:app-pl-vol-zero}
summed over the lags with every $\Delta^N_\ell$ replaced by one.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_age_iii {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ m₁ m₂ : ℝ, 0 < m₁ → 0 < m₂ →
      Integrable (fun g : ℝ => Zg β g (Qm β m₁) * Zg β g (Qm β m₂)) (gaussianReal 0 1) ∧
        HasSum (fun ℓ : ℤ => DLag β (Qm β m₁) (Qm β m₂) ℓ)
          (∫ g : ℝ, Zg β g (Qm β m₁) * Zg β g (Qm β m₂) ∂(gaussianReal 0 1)) := by
  intro m₁ m₂ hm₁ hm₂
  obtain ⟨hq₁, -⟩ := vk_Qm hβ0 hβ1 hm₁
  obtain ⟨hq₂, -⟩ := vk_Qm hβ0 hβ1 hm₂
  let q₁ := Qm β m₁
  let q₂ := Qm β m₂
  change 0 < q₁ at hq₁
  change 0 < q₂ at hq₂
  let A : ℝ → ℕ → ℝ → ℝ := fun q a g =>
    Real.sqrt q * (emaW β a * g / (1 + emaW β a ^ 2 * q * g ^ 2))
  let F : ℕ × ℕ → ℝ → ℝ := fun p g => A q₁ p.1 g * A q₂ p.2 g
  have hAabs : ∀ q : ℝ, 0 ≤ q → ∀ a g,
      |A q a g| ≤ Real.sqrt q * emaW β a * |g| := by
    intro q hq a g
    dsimp [A]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg q), age_term_abs hβ0 hβ1 hq]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (div_le_self (mul_nonneg (vk_emaW_pos hβ0 hβ1 a).le (abs_nonneg g))
        (by
          have hx := mul_nonneg (mul_nonneg (sq_nonneg (emaW β a)) hq) (sq_nonneg g)
          exact le_add_of_nonneg_right (by simpa only [mul_assoc] using hx)))
      (Real.sqrt_nonneg q)
  have hF0 : ∀ p g, 0 ≤ F p g := by
    intro p g
    dsimp [F, A]
    have hden₁ : 0 < 1 + emaW β p.1 ^ 2 * q₁ * g ^ 2 := by positivity
    have hden₂ : 0 < 1 + emaW β p.2 ^ 2 * q₂ * g ^ 2 := by positivity
    have hw₁ := vk_emaW_pos hβ0 hβ1 p.1
    have hw₂ := vk_emaW_pos hβ0 hβ1 p.2
    have he :
        (Real.sqrt q₁ * (emaW β p.1 * g / (1 + emaW β p.1 ^ 2 * q₁ * g ^ 2))) *
          (Real.sqrt q₂ * (emaW β p.2 * g / (1 + emaW β p.2 ^ 2 * q₂ * g ^ 2))) =
        (Real.sqrt q₁ * Real.sqrt q₂ * emaW β p.1 * emaW β p.2 * g ^ 2) /
          ((1 + emaW β p.1 ^ 2 * q₁ * g ^ 2) *
            (1 + emaW β p.2 ^ 2 * q₂ * g ^ 2)) := by
      field_simp
    rw [he]
    exact div_nonneg (by positivity) (mul_nonneg hden₁.le hden₂.le)
  have hFle : ∀ p g, ‖F p g‖ ≤
      (Real.sqrt q₁ * emaW β p.1) * (Real.sqrt q₂ * emaW β p.2) * g ^ 2 := by
    intro p g
    rw [Real.norm_eq_abs]
    calc |F p g| = |A q₁ p.1 g| * |A q₂ p.2 g| := by simp [F]
      _ ≤ (Real.sqrt q₁ * emaW β p.1 * |g|) *
          (Real.sqrt q₂ * emaW β p.2 * |g|) := by
          exact mul_le_mul (hAabs q₁ hq₁.le p.1 g) (hAabs q₂ hq₂.le p.2 g)
            (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg q₁) (vk_emaW_pos hβ0 hβ1 p.1).le |>
              fun h => mul_nonneg h (abs_nonneg g))
      _ = _ := by rw [← sq_abs g]; ring
  have hFint : ∀ p, Integrable (F p) (gaussianReal 0 1) := by
    intro p
    have hmajor : Integrable (fun g : ℝ =>
        (Real.sqrt q₁ * emaW β p.1) * (Real.sqrt q₂ * emaW β p.2) * g ^ 2)
        (gaussianReal 0 1) :=
      (Muon.Foundations.gaussian_integrable_pow 2).const_mul _
    refine hmajor.mono' ?_ (Filter.Eventually.of_forall (hFle p))
    apply Continuous.aestronglyMeasurable
    dsimp [F, A]
    apply Continuous.mul
    · apply Continuous.mul continuous_const
      apply Continuous.div (by fun_prop) (by fun_prop)
      intro g
      positivity
    · apply Continuous.mul continuous_const
      apply Continuous.div (by fun_prop) (by fun_prop)
      intro g
      positivity
  have hbound : ∀ p, ∫ g, ‖F p g‖ ∂(gaussianReal 0 1) ≤
      (Real.sqrt q₁ * emaW β p.1) * (Real.sqrt q₂ * emaW β p.2) := by
    intro p
    calc
      (∫ g, ‖F p g‖ ∂(gaussianReal 0 1)) ≤
          ∫ g, (Real.sqrt q₁ * emaW β p.1) *
            (Real.sqrt q₂ * emaW β p.2) * g ^ 2 ∂(gaussianReal 0 1) :=
        integral_mono (hFint p).norm
          ((Muon.Foundations.gaussian_integrable_pow 2).const_mul _) (hFle p)
      _ = _ := by
        rw [integral_const_mul, Muon.Foundations.gaussian_moment_two, mul_one]
  have hs₁ : Summable (fun a : ℕ => Real.sqrt q₁ * emaW β a) :=
    ((vk_weightSeq hβ0 hβ1).2.1).mul_left _
  have hs₂ : Summable (fun a : ℕ => Real.sqrt q₂ * emaW β a) :=
    ((vk_weightSeq hβ0 hβ1).2.1).mul_left _
  have hsMaj : Summable (fun p : ℕ × ℕ =>
      (Real.sqrt q₁ * emaW β p.1) * (Real.sqrt q₂ * emaW β p.2)) :=
    hs₁.mul_of_nonneg hs₂
      (fun a => mul_nonneg (Real.sqrt_nonneg q₁) (vk_emaW_pos hβ0 hβ1 a).le)
      (fun a => mul_nonneg (Real.sqrt_nonneg q₂) (vk_emaW_pos hβ0 hβ1 a).le)
  have hsNorm : Summable (fun p : ℕ × ℕ =>
      ∫ g, ‖F p g‖ ∂(gaussianReal 0 1)) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      hbound hsMaj
  have hpoint : ∀ g, (∑' p : ℕ × ℕ, F p g) = Zg β g q₁ * Zg β g q₂ := by
    intro g
    have ha₁ : Summable (fun a : ℕ => A q₁ a g) :=
      (age_term_summable hβ0 hβ1 hq₁.le g).mul_left _
    have ha₂ : Summable (fun a : ℕ => A q₂ a g) :=
      (age_term_summable hβ0 hβ1 hq₂.le g).mul_left _
    have hp : Summable (fun p : ℕ × ℕ => A q₁ p.1 g * A q₂ p.2 g) := by
      by_cases hg : 0 ≤ g
      · exact ha₁.mul_of_nonneg ha₂
          (fun a => by
            dsimp [A]
            exact mul_nonneg (Real.sqrt_nonneg q₁)
              (div_nonneg (mul_nonneg (vk_emaW_pos hβ0 hβ1 a).le hg)
                (by positivity)))
          (fun a => by
            dsimp [A]
            exact mul_nonneg (Real.sqrt_nonneg q₂)
              (div_nonneg (mul_nonneg (vk_emaW_pos hβ0 hβ1 a).le hg)
                (by positivity)))
      · have hg' : g ≤ 0 := le_of_not_ge hg
        have hAneg : ∀ q : ℝ, 0 ≤ q → ∀ a, A q a g ≤ 0 := by
          intro q hq a
          dsimp [A]
          exact mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg q)
            (div_nonpos_of_nonpos_of_nonneg
              (mul_nonpos_of_nonneg_of_nonpos (vk_emaW_pos hβ0 hβ1 a).le hg') (by positivity))
        have hs := ha₁.neg.mul_of_nonneg ha₂.neg
          (fun a => neg_nonneg.2 (hAneg q₁ hq₁.le a))
          (fun a => neg_nonneg.2 (hAneg q₂ hq₂.le a))
        simpa only [neg_mul_neg] using hs
    rw [← ha₁.tsum_mul_tsum ha₂ hp]
    unfold Zg
    dsimp [A]
    rw [tsum_mul_left, tsum_mul_left]
  have hpair : HasSum (fun p : ℕ × ℕ =>
      ∫ g, F p g ∂(gaussianReal 0 1))
      (∫ g, Zg β g q₁ * Zg β g q₂ ∂(gaussianReal 0 1)) := by
    convert hasSum_integral_of_summable_integral_norm hFint hsNorm using 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun g => (hpoint g).symm
  let e : (ℤ × ℕ) ≃ (ℕ × ℕ) := Equiv.ofBijective _ age_lag_bijective
  have hindexed : HasSum (fun p : ℤ × ℕ =>
      ∫ g, F (e p) g ∂(gaussianReal 0 1))
      (∫ g, Zg β g q₁ * Zg β g q₂ ∂(gaussianReal 0 1)) :=
    e.hasSum_iff.mpr hpair
  have hfiber : ∀ l : ℤ, HasSum (fun a : ℕ =>
      ∫ g, F (e (l, a)) g ∂(gaussianReal 0 1)) (DLag β q₁ q₂ l) := by
    intro l
    cases l with
    | ofNat l =>
        unfold DLag
        simp only [Int.ofNat_eq_coe, Int.natCast_nonneg, if_pos, Int.toNat_natCast]
        change HasSum (fun a : ℕ => ∫ g, F (a, a + l) g ∂(gaussianReal 0 1))
          (DLagNat β q₁ q₂ l)
        have hs : Summable (fun a : ℕ => ∫ g, F (a, a + l) g ∂(gaussianReal 0 1)) :=
          hpair.summable.comp_injective (fun _ _ h => by
            exact congrArg Prod.fst h)
        convert hs.hasSum using 1
        unfold DLagNat
        apply tsum_congr
        intro a
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun g => ?_
        dsimp [F, A]
        rw [vk_emaW_add, Real.sqrt_mul hq₁.le]
        rw [show β ^ (2 * l) = (β ^ l) ^ 2 by rw [← pow_mul]; congr 1 <;> omega]
        field_simp
    | negSucc l =>
        unfold DLag
        rw [if_neg (by omega : ¬ (0 : ℤ) ≤ Int.negSucc l)]
        change HasSum (fun a : ℕ => ∫ g, F (a + l + 1, a) g ∂(gaussianReal 0 1))
          (DLagNat β q₂ q₁ (l + 1))
        have hs : Summable (fun a : ℕ => ∫ g, F (a + l + 1, a) g ∂(gaussianReal 0 1)) :=
          hpair.summable.comp_injective (fun _ _ h => by
            exact congrArg Prod.snd h)
        convert hs.hasSum using 1
        unfold DLagNat
        apply tsum_congr
        intro a
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun g => ?_
        dsimp [F, A]
        rw [show a + l + 1 = a + (l + 1) by omega, vk_emaW_add,
          Real.sqrt_mul hq₂.le]
        rw [show β ^ (2 * (l + 1)) = (β ^ (l + 1)) ^ 2 by
          rw [← pow_mul]; congr 1 <;> omega]
        field_simp
  have hout := HasSum.prod_fiberwise hindexed hfiber
  refine ⟨?_, ?_⟩
  · have hmajor : Integrable (fun g : ℝ =>
        (Real.sqrt q₁ * Real.sqrt q₂) * g ^ 2) (gaussianReal 0 1) :=
      (Muon.Foundations.gaussian_integrable_pow 2).const_mul _
    refine hmajor.mono' ((age_measurable β q₁).mul (age_measurable β q₂)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |Zg β g q₁| * |Zg β g q₂| ≤
          (Real.sqrt q₁ * |g|) * (Real.sqrt q₂ * |g|) :=
        mul_le_mul (age_abs_le hβ0 hβ1 hq₁.le g) (age_abs_le hβ0 hβ1 hq₂.le g)
          (abs_nonneg _) (by positivity)
      _ = (Real.sqrt q₁ * Real.sqrt q₂) * g ^ 2 := by
        rw [← sq_abs]
        ring
  · simpa [q₁, q₂] using hout

private lemma age_DLagNat_nonneg {β : ℝ} (hβ0 : 0 < β) {q₁ q₂ : ℝ}
    (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) (l : ℕ) : 0 ≤ DLagNat β q₁ q₂ l := by
  unfold DLagNat
  refine tsum_nonneg fun a => integral_nonneg fun g => ?_
  have : 0 ≤ β ^ l := pow_nonneg hβ0.le l
  have : 0 ≤ β ^ (2 * l) := pow_nonneg hβ0.le _
  positivity

private lemma age_DLag_nonneg {β : ℝ} (hβ0 : 0 < β) {q₁ q₂ : ℝ}
    (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) (l : ℤ) : 0 ≤ DLag β q₁ q₂ l := by
  unfold DLag
  split_ifs
  · exact age_DLagNat_nonneg hβ0 hq₁ hq₂ _
  · exact age_DLagNat_nonneg hβ0 hq₂ hq₁ _

private lemma age_Wpart_nonneg {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    0 ≤ Wpart β B (plSpec α c N) i m := by
  have hμ := vk_pos_plSpec (α := α) hc N i
  have hΛ := vk_partLam_pos hB hN (vk_pos_plSpec (α := α) hc N) hm
  obtain ⟨cE, CE, hcE, -, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  have hEp : 0 < Efun β m :=
    lt_of_lt_of_le (mul_pos hcE (lt_min hm.1 one_pos)) (hE m hm.1).1
  obtain ⟨C, hC⟩ := lem_app_pl_elasticity_ii hα hβ0 hβ1
  have hθ : 0 ≤ thetaN β B (plSpec α c N) m := by
    have := (hC N B c hN hB hc m hm).2
    nlinarith
  have hγ : 0 < gammaOf N B := hm.1.trans hm.2
  have htail : 0 ≤ 1 - m / gammaOf N B := by
    rw [sub_nonneg, div_le_one hγ]
    exact hm.2.le
  unfold Wpart
  positivity

private lemma age_lagNumer_nonneg {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) (l : ℤ) {m₁ m₂ : ℝ}
    (hm₁ : m₁ ∈ Ioo 0 (gammaOf N B)) (hm₂ : m₂ ∈ Ioo 0 (gammaOf N B)) :
    0 ≤ lagNumer β B (plSpec α c N) i l m₁ m₂ := by
  unfold lagNumer
  exact mul_nonneg (mul_nonneg
    (age_Wpart_nonneg hα hβ0 hβ1 hN hB hc i hm₁)
    (age_Wpart_nonneg hα hβ0 hβ1 hN hB hc i hm₂))
    (age_DLag_nonneg hβ0 (vk_Qm hβ0 hβ1 hm₁.1).1.le
      (vk_Qm hβ0 hβ1 hm₂.1).1.le l)

private lemma age_kernel_order {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) (l : ℤ) {m₁ m₂ : ℝ}
    (hm₁ : m₁ ∈ Ioo 0 (gammaOf N B)) (hm₂ : m₂ ∈ Ioo 0 (gammaOf N B)) :
    0 ≤ lagNumer β B (plSpec α c N) i l m₁ m₂ ∧
      lagNumer β B (plSpec α c N) i l m₁ m₂ ≤
        lagIntegrand β B (plSpec α c N) i l m₁ m₂ := by
  have hγ : 0 < gammaOf N B := hm₁.1.trans hm₁.2
  obtain ⟨k, hk, hchain⟩ := lem_app_pl_determinant_ii_chain hα
  have hm₁' : 0 < 1 - m₁ / gammaOf N B := by
    rw [sub_pos, div_lt_one hγ]
    exact hm₁.2
  have hm₂' : 0 < 1 - m₂ / gammaOf N B := by
    rw [sub_pos, div_lt_one hγ]
    exact hm₂.2
  have hd : 0 < deltaN β B (plSpec α c N) l m₁ m₂ :=
    (mul_pos hk (mul_pos hm₁' hm₂')).trans_le
      ((hchain N B c hN hB hc m₁ m₂ hm₁ hm₂).trans
        (lem_app_pl_determinant_ii hα hβ0 hβ1 N B c hN hB hc l m₁ m₂ hm₁ hm₂))
  have ha := age_lagNumer_nonneg hα hβ0 hβ1 hN hB hc i l hm₁ hm₂
  refine ⟨ha, ?_⟩
  unfold lagIntegrand
  rw [le_div_iff₀ hd]
  have hd1 := (lem_app_pl_determinant_iii hα hβ0 hβ1 N B c hN hB hc l m₁ m₂ hm₁ hm₂).1
  nlinarith

private lemma age_vFlat_nonneg (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) :
    0 ≤ vFlat β B μ i := by
  unfold vFlat
  exact integral_nonneg fun _ => sq_nonneg _


/-! ## Helpers for `lem_app_pl_age_iv` -/

private lemma age_lam_facts {N B : ℕ} {μ : Fin N → ℝ} (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) (i : Fin N) :
    μ i * partLam B μ m ≤ B * m * (1 + μ i * partLam B μ m) ∧
      m ≤ (gammaOf N B - m) * partLam B μ m * ∑ j, μ j := by
  have hΛ := vk_partLam_pos hB hN hpos hm
  have hmeq := vk_partMN_partLam hB hN hpos hm
  unfold partMN at hmeq
  set Λ := partLam B μ m with hΛdef
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hterm : ∀ j, 0 ≤ Λ * μ j / (1 + Λ * μ j) := fun j =>
    vk_sat_nonneg hΛ.le (hpos j).le
  have hsum : ∑ j, Λ * μ j / (1 + Λ * μ j) = B * m := by
    rw [← hmeq]; field_simp
  constructor
  · have h1 : Λ * μ i / (1 + Λ * μ i) ≤ B * m := by
      rw [← hsum]
      exact Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ i)
    have hy : 0 < 1 + Λ * μ i := by have := mul_pos hΛ (hpos i); linarith
    rw [div_le_iff₀ hy] at h1
    nlinarith [h1]
  · have hS : ∀ j, μ j ≤ ∑ k, μ k := fun j =>
      Finset.single_le_sum (f := μ) (fun k _ => (hpos k).le) (Finset.mem_univ j)
    set S := ∑ j, μ j with hSdef
    have hS0 : 0 < S := lt_of_lt_of_le (hpos ⟨0, hN⟩) (hS ⟨0, hN⟩)
    have h1 : ∀ j, 1 / (1 + Λ * S) ≤ 1 - Λ * μ j / (1 + Λ * μ j) := by
      intro j
      have hj : 1 - Λ * μ j / (1 + Λ * μ j) = 1 / (1 + Λ * μ j) := by
        have : (1 + Λ * μ j) ≠ 0 := by have := mul_pos hΛ (hpos j); linarith
        field_simp; ring
      rw [hj]
      apply one_div_le_one_div_of_le
      · have := mul_pos hΛ (hpos j); linarith
      · have := mul_le_mul_of_nonneg_left (hS j) hΛ.le; linarith
    have h2 : (N : ℝ) * (1 / (1 + Λ * S)) ≤ ∑ j, (1 - Λ * μ j / (1 + Λ * μ j)) := by
      have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h1 j)
      simpa using this
    rw [Finset.sum_sub_distrib, hsum] at h2
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    have hγ : gammaOf N B = N / B := rfl
    have hden : 0 < 1 + Λ * S := by have := mul_pos hΛ hS0; linarith
    have h3 : (N : ℝ) / (1 + Λ * S) ≤ N - B * m := by linarith [mul_one_div (N : ℝ) (1 + Λ * S)]
    rw [div_le_iff₀ hden] at h3
    have h4 : gammaOf N B - m = (N - B * m) / B := by rw [hγ]; field_simp
    rw [h4]
    have : (N - B * m) / B * Λ * S = (N - B * m) * (Λ * S) / B := by ring
    rw [this, le_div_iff₀ hBpos]
    nlinarith [h3]

private lemma age_theta_nonneg {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    0 ≤ thetaN β B (plSpec α c N) m := by
  obtain ⟨cE, CE, hcE, -, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  have hEp : 0 < Efun β m :=
    lt_of_lt_of_le (mul_pos hcE (lt_min hm.1 one_pos)) (hE m hm.1).1
  obtain ⟨C, hC⟩ := lem_app_pl_elasticity_ii hα hβ0 hβ1
  have := (hC N B c hN hB hc m hm).2
  nlinarith

private lemma age_aux_sq (x : ℝ) (hx : 0 ≤ x) : x ≤ (x + 1) ^ 2 := by nlinarith

private lemma age_W_bound {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m ∈ Ioo 0 (gammaOf N B),
      Wpart β B (plSpec α c N) i m ≤ K * (1 + 1 / m) := by
  obtain ⟨C, hC⟩ := lem_app_pl_elasticity_ii hα hβ0 hβ1
  set C₀ := max C 0 with hC₀
  have hC₀0 : 0 ≤ C₀ := le_max_right _ _
  have hpos := vk_pos_plSpec (α := α) hc N
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  set S := ∑ j, plSpec α c N j with hSdef
  have hν := hpos i
  set ν := plSpec α c N i with hνdef
  have hS0 : 0 < S := lt_of_lt_of_le hν
    (Finset.single_le_sum (f := plSpec α c N) (fun k _ => (hpos k).le) (Finset.mem_univ i))
  have hγpos : 0 < gammaOf N B := by
    unfold gammaOf; positivity
  refine ⟨max (Real.sqrt B * C₀ * (1 + 2 / gammaOf N B))
    ((S / (ν * gammaOf N B) + 1) * C₀ * (gammaOf N B + 3)), ?_, ?_⟩
  · refine le_max_of_le_left ?_
    positivity
  intro m hm
  have hm0 := hm.1
  have hγm : 0 < gammaOf N B - m := by linarith [hm.2]
  obtain ⟨hθ1, -⟩ := hC N B c hN hB hc m hm
  have hθ0 := age_theta_nonneg hα hβ0 hβ1 hN hB hc hm
  set θ := thetaN β B (plSpec α c N) m with hθdef
  have hθ2 : θ ≤ C₀ * (1 + 1 / m + 1 / (gammaOf N B - m)) :=
    hθ1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  obtain ⟨hy1, hy2⟩ := age_lam_facts hB hN hpos hm i
  have hΛ := vk_partLam_pos hB hN hpos hm
  set Λ := partLam B (plSpec α c N) m with hΛdef
  set y := ν * Λ with hydef
  have hy0 : 0 < y := mul_pos hν hΛ
  have htγ : 0 ≤ 1 - m / gammaOf N B := by
    rw [sub_nonneg, div_le_one hγpos]; exact hm.2.le
  -- square of W
  have hW2 : Wpart β B (plSpec α c N) i m ^ 2 =
      y / (m * (1 + y) ^ 2) * (1 - m / gammaOf N B) * θ ^ 2 := by
    unfold Wpart
    rw [mul_pow, mul_pow, div_pow, mul_pow, Real.sq_sqrt hy0.le, Real.sq_sqrt hm0.le,
      Real.sq_sqrt htγ]
  have hW0 : 0 ≤ Wpart β B (plSpec α c N) i m := age_Wpart_nonneg hα hβ0 hβ1 hN hB hc i hm
  have hQ0 : 0 ≤ y / (m * (1 + y) ^ 2) := by positivity
  rw [← hSdef] at hy2
  clear_value y Λ ν S θ
  rcases le_total m (gammaOf N B / 2) with hcase | hcase
  · -- case 1
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    set K := Real.sqrt B * C₀ * (1 + 2 / gammaOf N B) with hK
    have hQ1 : y / (m * (1 + y) ^ 2) ≤ B := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : y ≤ B * m * (1 + y) := hy1
      have h2 : 1 ≤ 1 + y := by linarith
      nlinarith [mul_pos hBpos hm0, mul_le_mul_of_nonneg_left h2 (mul_pos hBpos hm0).le]
    have hγm2 : 1 / (gammaOf N B - m) ≤ 2 / gammaOf N B := by
      rw [div_le_div_iff₀ hγm hγpos]; linarith
    have hθ3 : θ ≤ C₀ * ((1 + 2 / gammaOf N B) * (1 + 1 / m)) := by
      refine hθ2.trans (mul_le_mul_of_nonneg_left ?_ hC₀0)
      have : 0 ≤ 1 / m := by positivity
      have : 0 ≤ 2 / gammaOf N B := by positivity
      nlinarith
    have hsq : Wpart β B (plSpec α c N) i m ^ 2 ≤ (K * (1 + 1 / m)) ^ 2 := by
      rw [hW2]
      have e1 : 1 - m / gammaOf N B ≤ 1 := by
        have : 0 ≤ m / gammaOf N B := by positivity
        linarith
      calc y / (m * (1 + y) ^ 2) * (1 - m / gammaOf N B) * θ ^ 2
          ≤ B * 1 * (C₀ * ((1 + 2 / gammaOf N B) * (1 + 1 / m))) ^ 2 := by
            refine mul_le_mul (mul_le_mul hQ1 e1 htγ hBpos.le)
              (pow_le_pow_left₀ hθ0 hθ3 2) (sq_nonneg _) (by positivity)
        _ = (K * (1 + 1 / m)) ^ 2 := by
            have e : (K * (1 + 1 / m)) ^ 2 =
                (Real.sqrt B) ^ 2 * (C₀ * ((1 + 2 / gammaOf N B) * (1 + 1 / m))) ^ 2 := by
              rw [hK]; ring
            rw [e, Real.sq_sqrt hBpos.le]; ring
    exact (pow_le_pow_iff_left₀ hW0 (by positivity) (by norm_num : (2:ℕ) ≠ 0)).1 hsq
  · -- case 2
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    set K := (S / (ν * gammaOf N B) + 1) * C₀ * (gammaOf N B + 3) with hK
    obtain ⟨t, ht⟩ : ∃ t, t = gammaOf N B - m := ⟨_, rfl⟩
    rw [← ht] at hy2 hγm hθ2
    have hy3 : ν * m ≤ y * (t * S) := by
      have : m ≤ t * Λ * S := hy2
      calc ν * m ≤ ν * (t * Λ * S) := mul_le_mul_of_nonneg_left this hν.le
        _ = y * (t * S) := by rw [hydef]; ring
    have hQ1 : y / (m * (1 + y) ^ 2) ≤ S * t / (ν * m ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : y ^ 2 ≤ (1 + y) ^ 2 := pow_le_pow_left₀ hy0.le (by linarith) 2
      have h2 : y * (ν * m ^ 2) ≤ m * (1 + y) ^ 2 * (S * t) := by
        have h3 : y * (ν * m ^ 2) = m * (ν * m * y) := by ring
        have h4 : ν * m * y ≤ y * y * (t * S) := by
          calc ν * m * y = y * (ν * m) := by ring
            _ ≤ y * (y * (t * S)) := mul_le_mul_of_nonneg_left hy3 hy0.le
            _ = y * y * (t * S) := by ring
        have h5 : y * y * (t * S) ≤ (1 + y) ^ 2 * (S * t) := by
          have : 0 ≤ S * t := by positivity
          calc y * y * (t * S) = y ^ 2 * (S * t) := by ring
            _ ≤ (1 + y) ^ 2 * (S * t) := mul_le_mul_of_nonneg_right h1 this
        calc y * (ν * m ^ 2) = m * (ν * m * y) := h3
          _ ≤ m * ((1 + y) ^ 2 * (S * t)) := mul_le_mul_of_nonneg_left (h4.trans h5) hm0.le
          _ = _ := by ring
      calc y * (ν * m ^ 2) ≤ m * (1 + y) ^ 2 * (S * t) := h2
        _ = S * t * (m * (1 + y) ^ 2) := by ring
    have hmγ : gammaOf N B / m ≤ 2 := by
      rw [div_le_iff₀ hm0]; linarith
    have htθ : t * θ ≤ C₀ * (gammaOf N B + 3) := by
      have h1 : t * θ ≤ t * (C₀ * (1 + 1 / m + 1 / t)) := mul_le_mul_of_nonneg_left hθ2 hγm.le
      have h2 : t * (C₀ * (1 + 1 / m + 1 / t)) = C₀ * (t + t / m + 1) := by
        field_simp
      have h3 : t + t / m + 1 ≤ gammaOf N B + 3 := by
        have : t ≤ gammaOf N B := by linarith
        have : t / m ≤ gammaOf N B / m := div_le_div_of_nonneg_right this hm0.le
        linarith
      rw [h2] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left h3 hC₀0)
    have hsq : Wpart β B (plSpec α c N) i m ^ 2 ≤ (K * (1 + 1 / m)) ^ 2 := by
      rw [hW2]
      have e1 : 1 - m / gammaOf N B = t / gammaOf N B := by
        rw [ht, sub_div, div_self hγpos.ne']
      have hx : S / (ν * gammaOf N B) ≤ (S / (ν * gammaOf N B) + 1) ^ 2 :=
        age_aux_sq _ (by positivity)
      calc y / (m * (1 + y) ^ 2) * (1 - m / gammaOf N B) * θ ^ 2
          ≤ S * t / (ν * m ^ 2) * (t / gammaOf N B) * θ ^ 2 := by
            rw [e1]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hQ1 (by positivity)) (sq_nonneg _)
        _ = S / (ν * gammaOf N B) * (t * θ) ^ 2 / m ^ 2 := by
            field_simp
        _ ≤ S / (ν * gammaOf N B) * (C₀ * (gammaOf N B + 3)) ^ 2 / m ^ 2 := by
            gcongr
        _ ≤ (S / (ν * gammaOf N B) + 1) ^ 2 * (C₀ * (gammaOf N B + 3)) ^ 2 / m ^ 2 := by
            gcongr
        _ = (K / m) ^ 2 := by
            rw [hK, div_pow]; ring
        _ ≤ (K * (1 + 1 / m)) ^ 2 := by
            refine pow_le_pow_left₀ (by positivity) ?_ 2
            have : 0 ≤ K := by positivity
            have h1 : K / m = K * (1 / m) := by ring
            rw [h1]
            exact mul_le_mul_of_nonneg_left (by linarith) this
    exact (pow_le_pow_iff_left₀ hW0 (by positivity) (by norm_num : (2:ℕ) ≠ 0)).1 hsq

private lemma age_Efun_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    0 < Efun β m := by
  obtain ⟨cE, CE, hcE, -, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  exact lt_of_lt_of_le (mul_pos hcE (lt_min hm one_pos)) (hE m hm).1

private lemma age_W_cont {α β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) :
    ContinuousOn (Wpart β B (plSpec α c N) i) (Ioo 0 (gammaOf N B)) := by
  have hpos := vk_pos_plSpec (α := α) hc N
  have hbij := def_app_pl_participation_bij (plSpec α c N) hB hN hpos
  have hcd := hbij.2.2.2
  have hΛc : ContinuousOn (partLam B (plSpec α c N)) (Ioo 0 (gammaOf N B)) := hcd.continuousOn
  have hdΛ : ContinuousOn (deriv (partLam B (plSpec α c N))) (Ioo 0 (gammaOf N B)) :=
    hcd.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)
  have hEc : ContinuousOn (Efun β) (Ioo 0 (gammaOf N B)) :=
    (lp_Efun_cont hβ0 hβ1).mono (fun m hm => hm.1)
  have hΛpos : ∀ m ∈ Ioo 0 (gammaOf N B), 0 < partLam B (plSpec α c N) m :=
    fun m hm => vk_partLam_pos hB hN hpos hm
  have hyc : ContinuousOn (fun m => plSpec α c N i * partLam B (plSpec α c N) m)
      (Ioo 0 (gammaOf N B)) := continuousOn_const.mul hΛc
  have hθc : ContinuousOn (thetaN β B (plSpec α c N)) (Ioo 0 (gammaOf N B)) := by
    unfold thetaN
    refine ContinuousOn.sub (ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_) ?_
    · exact continuousOn_const.div hEc (fun m hm => (age_Efun_pos hβ0 hβ1 hm.1).ne')
    · exact hdΛ.div hΛc (fun m hm => (hΛpos m hm).ne')
    · exact continuousOn_const.div (continuousOn_const.sub continuousOn_id)
        (fun m hm => (by linarith [hm.2] : gammaOf N B - m ≠ 0))
    · exact continuousOn_const.div continuousOn_id (fun m hm => hm.1.ne')
  unfold Wpart
  refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) hθc
  · refine hyc.sqrt.div (ContinuousOn.mul continuousOn_id.sqrt (continuousOn_const.add hyc)) ?_
    intro m hm
    have h1 : 0 < plSpec α c N i * partLam B (plSpec α c N) m := mul_pos (hpos i) (hΛpos m hm)
    exact (mul_pos (Real.sqrt_pos.2 hm.1) (by linarith)).ne'
  · exact (continuousOn_const.sub (continuousOn_id.div_const _)).sqrt

private lemma age_Q_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {γ : ℝ} (hγ : 0 < γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m ∈ Ioo 0 γ, Qm β m ≤ K * m := by
  obtain ⟨hQ1, -⟩ := vk_Qm hβ0 hβ1 (zero_lt_one : (0:ℝ) < 1)
  obtain ⟨hQγ, -⟩ := vk_Qm hβ0 hβ1 hγ
  refine ⟨Qm β 1 + Qm β γ, by positivity, fun m hm => ?_⟩
  rcases le_total m 1 with h | h
  · have := vk_Qm_le hβ0 hβ1 hm.1 h
    nlinarith [mul_pos hQγ hm.1]
  · have hmono := lp_Qm_mono hβ0 hβ1 (Set.mem_Ioi.2 hm.1) (Set.mem_Ioi.2 hγ) hm.2.le
    nlinarith [mul_nonneg hQγ.le (sub_nonneg.2 h), mul_pos hQ1 hm.1]

private lemma age_sr {s r t : ℝ} (hs : 0 < s) (hr : 0 < r) (ht : 0 < t) (h : s ^ 2 + r ^ 2 = t ^ 2) :
    (s + 1 / s) / r ≤ (2 * (t ^ 2 + 1) / t) * (1 / s + 1 / r) := by
  have hst : s ≤ t := by nlinarith
  have hrt : r ≤ t := by nlinarith
  have hC : 0 ≤ 2 * (t ^ 2 + 1) / t := by positivity
  rcases le_total (t / 2) r with hcase | hcase
  · -- r large
    have h1 : (s + 1 / s) / r ≤ (2 * (t ^ 2 + 1) / t) * (1 / s) := by
      rw [div_le_iff₀ hr]
      have e : (2 * (t ^ 2 + 1) / t) * (1 / s) * r = 2 * (t ^ 2 + 1) * r / (t * s) := by
        field_simp
      rw [e, le_div_iff₀ (by positivity)]
      have : (s + 1 / s) * (t * s) = t * (s ^ 2 + 1) := by field_simp
      rw [this]
      have h2 : s ^ 2 + 1 ≤ t ^ 2 + 1 := by nlinarith
      have h3 : t * (s ^ 2 + 1) ≤ t * (t ^ 2 + 1) := mul_le_mul_of_nonneg_left h2 ht.le
      have h4 : t * (t ^ 2 + 1) ≤ 2 * (t ^ 2 + 1) * r := by nlinarith
      linarith
    have : (2 * (t ^ 2 + 1) / t) * (1 / s) ≤ (2 * (t ^ 2 + 1) / t) * (1 / s + 1 / r) :=
      mul_le_mul_of_nonneg_left (by have : 0 ≤ 1 / r := by positivity
                                    linarith) hC
    linarith
  · -- s large
    have hs2 : t / 2 ≤ s := by
      by_contra hlt
      have hlt := not_le.1 hlt
      nlinarith
    have h1 : (s + 1 / s) / r ≤ (2 * (t ^ 2 + 1) / t) * (1 / r) := by
      have h2 : s + 1 / s ≤ 2 * (t ^ 2 + 1) / t := by
        have h3 : 1 / s ≤ 2 / t := by
          rw [div_le_div_iff₀ hs ht]; linarith
        have h4 : 2 / t + t = (t ^ 2 + 2) / t := by field_simp; ring
        have h5 : (t ^ 2 + 2) / t ≤ 2 * (t ^ 2 + 1) / t :=
          div_le_div_of_nonneg_right (by nlinarith) ht.le
        linarith
      calc (s + 1 / s) / r = (s + 1 / s) * (1 / r) := by ring
        _ ≤ (2 * (t ^ 2 + 1) / t) * (1 / r) := mul_le_mul_of_nonneg_right h2 (by positivity)
    have : (2 * (t ^ 2 + 1) / t) * (1 / r) ≤ (2 * (t ^ 2 + 1) / t) * (1 / s + 1 / r) :=
      mul_le_mul_of_nonneg_left (by have : 0 ≤ 1 / s := by positivity
                                    linarith) hC
    linarith

private lemma age_V_pw {a q m γ K K' : ℝ} (hm : 0 < m) (hmγ : m < γ) (hK : 0 ≤ K) (hK' : 0 ≤ K')
    (ha0 : 0 ≤ a) (ha : a ≤ K * (1 + 1 / m)) (hq0 : 0 ≤ q) (hq : q ≤ K' * m) :
    a * Real.sqrt q / Real.sqrt (1 - m / γ) ≤
      (K * Real.sqrt K' * Real.sqrt γ * (2 * (γ + 1) / Real.sqrt γ)) *
        (1 / Real.sqrt m + 1 / Real.sqrt (γ - m)) := by
  have hγ : 0 < γ := hm.trans hmγ
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hr : 0 < Real.sqrt (γ - m) := Real.sqrt_pos.2 (by linarith)
  have ht : 0 < Real.sqrt γ := Real.sqrt_pos.2 hγ
  have hsr : Real.sqrt m ^ 2 + Real.sqrt (γ - m) ^ 2 = Real.sqrt γ ^ 2 := by
    rw [Real.sq_sqrt hm.le, Real.sq_sqrt (by linarith), Real.sq_sqrt hγ.le]; ring
  have h1 := age_sr hs hr ht hsr
  rw [Real.sq_sqrt hγ.le] at h1
  have e1 : Real.sqrt (1 - m / γ) = Real.sqrt (γ - m) / Real.sqrt γ := by
    rw [← Real.sqrt_div (by linarith)]
    congr 1
    field_simp
  have hsq : Real.sqrt q ≤ Real.sqrt K' * Real.sqrt m := by
    rw [← Real.sqrt_mul hK']
    exact Real.sqrt_le_sqrt hq
  have h2 : a * Real.sqrt m ≤ K * (Real.sqrt m + 1 / Real.sqrt m) := by
    have hm' : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm.le
    calc a * Real.sqrt m ≤ K * (1 + 1 / m) * Real.sqrt m :=
          mul_le_mul_of_nonneg_right ha hs.le
      _ = K * (Real.sqrt m + 1 / Real.sqrt m) := by
          field_simp
          nlinarith [hm']
  rw [e1, div_div_eq_mul_div]
  have h3 : a * Real.sqrt q * Real.sqrt γ ≤ a * (Real.sqrt K' * Real.sqrt m) * Real.sqrt γ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq ha0) ht.le
  rw [div_le_iff₀ hr]
  have h4 : (Real.sqrt m + 1 / Real.sqrt m) ≤
      (2 * (γ + 1) / Real.sqrt γ) * (1 / Real.sqrt m + 1 / Real.sqrt (γ - m)) *
        Real.sqrt (γ - m) := by
    rw [div_le_iff₀ hr] at h1
    exact h1 |> fun h => by simpa [mul_comm, mul_left_comm, mul_assoc] using h
  calc a * Real.sqrt q * Real.sqrt γ ≤ a * (Real.sqrt K' * Real.sqrt m) * Real.sqrt γ := h3
    _ = Real.sqrt K' * Real.sqrt γ * (a * Real.sqrt m) := by ring
    _ ≤ Real.sqrt K' * Real.sqrt γ * (K * (Real.sqrt m + 1 / Real.sqrt m)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ Real.sqrt K' * Real.sqrt γ * (K * ((2 * (γ + 1) / Real.sqrt γ) *
        (1 / Real.sqrt m + 1 / Real.sqrt (γ - m)) * Real.sqrt (γ - m))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hK) (by positivity)
    _ = _ := by ring

private lemma age_inv_sqrt_int {γ : ℝ} (hγ : 0 < γ) :
    IntegrableOn (fun m : ℝ => 1 / Real.sqrt m) (Ioo 0 γ) ∧
      IntegrableOn (fun m : ℝ => 1 / Real.sqrt (γ - m)) (Ioo 0 γ) := by
  have hconv : ∀ x : ℝ, 0 ≤ x → 1 / Real.sqrt x = x ^ (-(1 / 2) : ℝ) := by
    intro x hx
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hx, one_div]
  have h1 : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) (Ioo 0 γ) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hγ).2 (by norm_num)
  constructor
  · refine h1.congr_fun (fun x hx => ?_) measurableSet_Ioo
    exact (hconv x hx.1.le).symm
  · have h2 : IntervalIntegrable (fun x : ℝ => (γ - x) ^ (-(1 / 2) : ℝ)) volume (γ - γ) (γ - 0) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := γ) (r := (-(1 / 2) : ℝ))
        (by norm_num))
      exact (this.comp_sub_left γ).symm
    rw [sub_self, sub_zero, intervalIntegrable_iff_integrableOn_Ioo_of_le hγ.le] at h2
    refine h2.congr_fun (fun x hx => ?_) measurableSet_Ioo
    exact (hconv (γ - x) (by linarith [hx.2])).symm

private lemma age_V_int {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) :
    IntegrableOn (fun m : ℝ => Wpart β B (plSpec α c N) i m * Real.sqrt (Qm β m) /
        Real.sqrt (1 - m / gammaOf N B)) (Ioo 0 (gammaOf N B)) := by
  have hγ : 0 < gammaOf N B := by unfold gammaOf; positivity
  obtain ⟨K, hK0, hK⟩ := age_W_bound hα hβ0 hβ1 hN hB hc i
  obtain ⟨K', hK'0, hK'⟩ := age_Q_bound hβ0 hβ1 hγ
  obtain ⟨h1, h2⟩ := age_inv_sqrt_int hγ
  have hmaj := (h1.add h2).const_mul
    (K * Real.sqrt K' * Real.sqrt (gammaOf N B) * (2 * (gammaOf N B + 1) / Real.sqrt (gammaOf N B)))
  refine Integrable.mono' hmaj ?_ ?_
  · have hWc := age_W_cont (α := α) hβ0 hβ1 hN hB hc i
    have hQc : ContinuousOn (Qm β) (Ioo 0 (gammaOf N B)) :=
      (lp_Qm_cont hβ0 hβ1).mono (fun m hm => hm.1)
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    refine (hWc.mul hQc.sqrt).div ((continuousOn_const.sub (continuousOn_id.div_const _)).sqrt) ?_
    intro m hm
    have : 0 < 1 - m / gammaOf N B := by
      rw [sub_pos, div_lt_one hγ]; exact hm.2
    exact (Real.sqrt_pos.2 this).ne'
  · rw [ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall (fun m hm => ?_)
    have hW0 := age_Wpart_nonneg hα hβ0 hβ1 hN hB hc i hm
    have hQ0 := (vk_Qm hβ0 hβ1 hm.1).1
    have := age_V_pw hm.1 hm.2 hK0 hK'0.le hW0 (hK m hm) hQ0.le (hK' m hm)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simpa using this

private lemma age_Mterm_eq (s q1 q2 w g : ℝ) :
    s * q1 * q2 * w ^ 4 * g ^ 4 / ((1 + q1 * w ^ 2 * g ^ 2) * (1 + s * q2 * w ^ 2 * g ^ 2)) =
      (q1 * w ^ 2 * g ^ 2) * (s * q2 * w ^ 2 * g ^ 2) /
        ((1 + q1 * w ^ 2 * g ^ 2) * (1 + s * q2 * w ^ 2 * g ^ 2)) := by
  congr 1; ring

private lemma age_Mterm {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {s q1 q2 : ℝ} (hs : 0 ≤ s)
    (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) :
    (∀ a : ℕ, Integrable (fun g : ℝ => s * q1 * q2 * emaW β a ^ 4 * g ^ 4 /
      ((1 + q1 * emaW β a ^ 2 * g ^ 2) * (1 + s * q2 * emaW β a ^ 2 * g ^ 2)))
      (gaussianReal 0 1)) ∧
    Summable (fun a : ℕ => ∫ g : ℝ, s * q1 * q2 * emaW β a ^ 4 * g ^ 4 /
      ((1 + q1 * emaW β a ^ 2 * g ^ 2) * (1 + s * q2 * emaW β a ^ 2 * g ^ 2))
      ∂(gaussianReal 0 1)) := by
  have hX : ∀ a g, 0 ≤ q1 * emaW β a ^ 2 * g ^ 2 := fun a g => by positivity
  have hY : ∀ a g, 0 ≤ s * q2 * emaW β a ^ 2 * g ^ 2 := fun a g => by positivity
  refine vk_int_summ hβ0 hβ1 (c := q1)
    (f := fun a g => s * q1 * q2 * emaW β a ^ 4 * g ^ 4 /
      ((1 + q1 * emaW β a ^ 2 * g ^ 2) * (1 + s * q2 * emaW β a ^ 2 * g ^ 2))) ?_ ?_ ?_
  · intro a
    refine Continuous.div (by fun_prop) (by fun_prop) (fun g => ?_)
    have := hX a g; have := hY a g
    positivity
  · intro a g
    have := hX a g; have := hY a g
    positivity
  · intro a g
    rw [age_Mterm_eq]
    refine ((vk_pw_bounds (hX a g) (hY a g)).2.2.1).trans (le_of_eq (by ring))

private lemma age_frac_mono {s s' P u : ℝ} (hs : 0 ≤ s) (hss : s ≤ s') (hP : 0 ≤ P) (hu : 0 ≤ u) :
    P * (s * u) / ((1 + P) * (1 + s * u)) ≤ P * (s' * u) / ((1 + P) * (1 + s' * u)) := by
  have hs' : 0 ≤ s' := hs.trans hss
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 0 ≤ P * u := mul_nonneg hP hu
  have h2 : 0 ≤ (s' - s) * (P * u) * (1 + P) := by
    have := sub_nonneg.2 hss
    positivity
  nlinarith [h2]

private lemma age_Mnat_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q1 q2 : ℝ}
    (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (ℓ : ℕ) :
    MLagNat β q1 q2 ℓ ≤ MLagNat β q1 q2 0 := by
  have hs0 : 0 ≤ β ^ (2 * ℓ) := pow_nonneg hβ0.le _
  have hs1 : β ^ (2 * ℓ) ≤ β ^ (2 * 0) := by
    simpa using pow_le_one₀ hβ0.le hβ1.le
  obtain ⟨hI1, hS1⟩ := age_Mterm hβ0 hβ1 hs0 hq1 hq2
  obtain ⟨hI2, hS2⟩ := age_Mterm hβ0 hβ1 (pow_nonneg hβ0.le (2 * 0)) hq1 hq2
  unfold MLagNat
  refine Summable.tsum_le_tsum (fun a => ?_) hS1 hS2
  refine integral_mono (hI1 a) (hI2 a) (fun g => ?_)
  rw [age_Mterm_eq, age_Mterm_eq]
  have := age_frac_mono (P := q1 * emaW β a ^ 2 * g ^ 2) (u := q2 * emaW β a ^ 2 * g ^ 2) hs0 hs1
    (by positivity) (by positivity)
  convert this using 2 <;> ring

private lemma age_Mnat_symm {β : ℝ} (q1 q2 : ℝ) :
    MLagNat β q1 q2 0 = MLagNat β q2 q1 0 := by
  unfold MLagNat
  refine tsum_congr (fun a => integral_congr_ae (Filter.Eventually.of_forall fun g => ?_))
  simp only
  ring

private lemma age_Mlag_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q1 q2 : ℝ}
    (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (ℓ : ℤ) :
    MLag β q1 q2 ℓ ≤ MLagNat β q1 q2 0 ∧ MLag β q1 q2 ℓ ≤ MLagNat β q2 q1 0 := by
  have h : MLag β q1 q2 ℓ ≤ MLagNat β q1 q2 0 := by
    unfold MLag
    split_ifs
    · exact age_Mnat_le hβ0 hβ1 hq1 hq2 _
    · rw [age_Mnat_symm q1 q2]
      exact age_Mnat_le hβ0 hβ1 hq2 hq1 _
  exact ⟨h, by rwa [age_Mnat_symm q2 q1]⟩

private lemma age_Sterm {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q1 q2 : ℝ}
    (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) :
    (∀ a : ℕ, Integrable (fun g : ℝ => q1 * emaW β a ^ 2 * g ^ 2 /
      ((1 + q1 * emaW β a ^ 2 * g ^ 2) * (1 + q2 * emaW β a ^ 2 * g ^ 2)))
      (gaussianReal 0 1)) ∧
    Summable (fun a : ℕ => ∫ g : ℝ, q1 * emaW β a ^ 2 * g ^ 2 /
      ((1 + q1 * emaW β a ^ 2 * g ^ 2) * (1 + q2 * emaW β a ^ 2 * g ^ 2))
      ∂(gaussianReal 0 1)) := by
  have hX : ∀ a g, 0 ≤ q1 * emaW β a ^ 2 * g ^ 2 := fun a g => by positivity
  have hY : ∀ a g, 0 ≤ q2 * emaW β a ^ 2 * g ^ 2 := fun a g => by positivity
  refine vk_int_summ hβ0 hβ1 (c := q1)
    (f := fun a g => q1 * emaW β a ^ 2 * g ^ 2 /
      ((1 + q1 * emaW β a ^ 2 * g ^ 2) * (1 + q2 * emaW β a ^ 2 * g ^ 2))) ?_ ?_ ?_
  · intro a
    refine Continuous.div (by fun_prop) (by fun_prop) (fun g => ?_)
    have := hX a g; have := hY a g
    positivity
  · intro a g
    have := hX a g; have := hY a g
    positivity
  · intro a g
    refine ((vk_pw_bounds (hX a g) (hY a g)).1).trans (le_of_eq (by ring))

private lemma age_gap_eq {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q1 q2 : ℝ}
    (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) :
    rW (emaW β) q1 - MLagNat β q1 q2 0 =
      ∑' a : ℕ, ∫ g : ℝ, q1 * emaW β a ^ 2 * g ^ 2 /
        ((1 + q1 * emaW β a ^ 2 * g ^ 2) * (1 + q2 * emaW β a ^ 2 * g ^ 2))
        ∂(gaussianReal 0 1) := by
  obtain ⟨hI1, hS1⟩ := age_Sterm hβ0 hβ1 hq1 hq2
  obtain ⟨hI2, hS2⟩ := age_Mterm hβ0 hβ1 (s := β ^ (2 * 0)) (pow_nonneg hβ0.le _) hq1 hq2
  have hr1 := (lem_app_de_scalar_iii (vk_weightSeq hβ0 hβ1)).1 q1 hq1
  have hM : MLagNat β q1 q2 0 = ∑' a : ℕ, ∫ g : ℝ, β ^ (2 * 0) * q1 * q2 * emaW β a ^ 4 * g ^ 4 /
      ((1 + q1 * emaW β a ^ 2 * g ^ 2) * (1 + β ^ (2 * 0) * q2 * emaW β a ^ 2 * g ^ 2))
      ∂(gaussianReal 0 1) := rfl
  rw [hr1, hM]
  have key : (∑' a : ℕ, ∫ g : ℝ, emaW β a ^ 2 * q1 * g ^ 2 / (1 + emaW β a ^ 2 * q1 * g ^ 2)
        ∂(gaussianReal 0 1)) =
      (∑' a : ℕ, ∫ g : ℝ, q1 * emaW β a ^ 2 * g ^ 2 /
        ((1 + q1 * emaW β a ^ 2 * g ^ 2) * (1 + q2 * emaW β a ^ 2 * g ^ 2))
        ∂(gaussianReal 0 1)) +
      ∑' a : ℕ, ∫ g : ℝ, β ^ (2 * 0) * q1 * q2 * emaW β a ^ 4 * g ^ 4 /
      ((1 + q1 * emaW β a ^ 2 * g ^ 2) * (1 + β ^ (2 * 0) * q2 * emaW β a ^ 2 * g ^ 2))
      ∂(gaussianReal 0 1) := by
    rw [← Summable.tsum_add hS1 hS2]
    refine tsum_congr fun a => ?_
    rw [← integral_add (hI1 a) (hI2 a)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [mul_zero, pow_zero, one_mul]
    have h1 : 0 < 1 + q1 * emaW β a ^ 2 * g ^ 2 := by positivity
    have h2 : 0 < 1 + q2 * emaW β a ^ 2 * g ^ 2 := by positivity
    have h3 : 0 < 1 + emaW β a ^ 2 * q1 * g ^ 2 := by positivity
    field_simp
  rw [key]
  ring

private lemma age_gauss_integral_pos {f : ℝ → ℝ} (hf0 : ∀ g, 0 ≤ f g)
    (hfi : Integrable f (gaussianReal 0 1)) (hpos : ∀ g ∈ Ioo (1 : ℝ) 2, 0 < f g) :
    0 < ∫ g, f g ∂(gaussianReal 0 1) := by
  rw [integral_pos_iff_support_of_nonneg hf0 hfi]
  have hsub : Ioo (1 : ℝ) 2 ⊆ Function.support f := fun g hg => (hpos g hg).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  have habs := gaussianReal_absolutelyContinuous' 0 (one_ne_zero : (1 : NNReal) ≠ 0)
  by_contra h
  have h0 : gaussianReal 0 1 (Ioo (1 : ℝ) 2) = 0 := le_antisymm (not_lt.1 h) zero_le
  have h1 := habs h0
  rw [Real.volume_Ioo] at h1
  norm_num at h1

private lemma age_frac2 {X' X Y Y' : ℝ} (hX' : 0 ≤ X') (hXX : X' ≤ X) (hY : 0 ≤ Y)
    (hYY : Y ≤ Y') :
    X' / ((1 + X') * (1 + Y')) ≤ X / ((1 + X) * (1 + Y)) := by
  have hX : 0 ≤ X := hX'.trans hXX
  have hY' : 0 ≤ Y' := hY.trans hYY
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 0 ≤ X - X' := sub_nonneg.2 hXX
  have h2 : 0 ≤ Y' - Y := sub_nonneg.2 hYY
  nlinarith [mul_nonneg h1 hY', mul_nonneg (mul_nonneg hX hY') h1, mul_nonneg h1 (mul_nonneg hX' hY'),
    mul_nonneg (mul_nonneg hX hX') h2, mul_nonneg hX h2]

private lemma age_S_mono {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {qa qb q1 q2 : ℝ}
    (hqa : 0 ≤ qa) (hq2 : 0 ≤ q2) (h1 : qa ≤ q1) (h2 : q2 ≤ qb) :
    (∑' a : ℕ, ∫ g : ℝ, qa * emaW β a ^ 2 * g ^ 2 /
        ((1 + qa * emaW β a ^ 2 * g ^ 2) * (1 + qb * emaW β a ^ 2 * g ^ 2))
        ∂(gaussianReal 0 1)) ≤
    ∑' a : ℕ, ∫ g : ℝ, q1 * emaW β a ^ 2 * g ^ 2 /
        ((1 + q1 * emaW β a ^ 2 * g ^ 2) * (1 + q2 * emaW β a ^ 2 * g ^ 2))
        ∂(gaussianReal 0 1) := by
  have hq1 : 0 ≤ q1 := hqa.trans h1
  have hqb : 0 ≤ qb := hq2.trans h2
  obtain ⟨hI1, hS1⟩ := age_Sterm hβ0 hβ1 hqa hqb
  obtain ⟨hI2, hS2⟩ := age_Sterm hβ0 hβ1 hq1 hq2
  refine Summable.tsum_le_tsum (fun a => ?_) hS1 hS2
  refine integral_mono (hI1 a) (hI2 a) (fun g => ?_)
  refine age_frac2 (by positivity) ?_ (by positivity) ?_
  · have : 0 ≤ emaW β a ^ 2 * g ^ 2 := by positivity
    nlinarith
  · have : 0 ≤ emaW β a ^ 2 * g ^ 2 := by positivity
    nlinarith

private lemma age_S_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {qa qb : ℝ}
    (hqa : 0 < qa) (hqb : 0 ≤ qb) :
    0 < ∑' a : ℕ, ∫ g : ℝ, qa * emaW β a ^ 2 * g ^ 2 /
        ((1 + qa * emaW β a ^ 2 * g ^ 2) * (1 + qb * emaW β a ^ 2 * g ^ 2))
        ∂(gaussianReal 0 1) := by
  obtain ⟨hI, hS⟩ := age_Sterm hβ0 hβ1 hqa.le hqb
  refine hS.tsum_pos (fun a => integral_nonneg fun g => by positivity) 0 ?_
  refine age_gauss_integral_pos (fun g => by positivity) (hI 0) (fun g hg => ?_)
  have hw := vk_emaW_pos hβ0 hβ1 0
  have hg : 0 < g := by linarith [hg.1]
  positivity

/-- Uniform gap: `r_β(q₁) - 𝖬_ℓ(q₁,q₂) ≥ d₀ > 0` for `q₁ ≥ q_a > 0`, `q₂ ≤ q_b`. -/
private lemma age_gap {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {qa qb : ℝ}
    (hqa : 0 < qa) (hqb : 0 ≤ qb) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ q1 q2 : ℝ, qa ≤ q1 → 0 ≤ q2 → q2 ≤ qb → ∀ ℓ : ℤ,
      d₀ ≤ rW (emaW β) q1 - MLag β q1 q2 ℓ ∧ d₀ ≤ rW (emaW β) q1 - MLag β q2 q1 ℓ := by
  refine ⟨_, age_S_pos hβ0 hβ1 hqa hqb, fun q1 q2 h1 hq2 h2 ℓ => ?_⟩
  have hq1 : 0 ≤ q1 := hqa.le.trans h1
  have hmono := age_S_mono hβ0 hβ1 hqa.le hq2 h1 h2
  have heq := age_gap_eq hβ0 hβ1 hq1 hq2
  obtain ⟨hl1, hl2⟩ := age_Mlag_le hβ0 hβ1 hq1 hq2 ℓ
  obtain ⟨hl3, hl4⟩ := age_Mlag_le hβ0 hβ1 hq2 hq1 ℓ
  constructor
  · linarith
  · linarith

private lemma age_core {T M D2 m1 m2 γ cα d0 : ℝ} (h1 : 0 < m1) (h12 : m1 ≤ m2) (h2γ : m2 < γ)
    (hT0 : 0 ≤ T) (hT1 : T ≤ m1) (hM0 : 0 ≤ M) (hM1 : M ≤ m1)
    (hD : D2 ≤ (m1 - M) * (m2 - M)) (hcα : 0 < cα)
    (hch : cα * ((1 - m1 / γ) * (1 - m2 / γ)) ≤ (1 - m1 / γ) * (1 - T / m2))
    (hd0 : 0 < d0) (hgap : γ / 2 < m1 → d0 ≤ m1 - M) :
    min (min (cα / 4) (1 / 3)) (d0 / γ) * (1 - m1 / γ) ≤
      (1 - T * M / (m1 * m2)) * (1 - M / γ) - T * D2 / (γ * m1 * m2) := by
  have hm2 : 0 < m2 := lt_of_lt_of_le h1 h12
  have hγ : 0 < γ := lt_trans hm2 h2γ
  have hbase := vk_alg h1 h12 h2γ hT0 hT1 hM0 hM1 hD
  have ha : 0 < 1 - m1 / γ := by
    rw [sub_pos, div_lt_one hγ]; exact h12.trans_lt h2γ
  set a := 1 - m1 / γ with hadef
  have hκ1 : min (min (cα / 4) (1 / 3)) (d0 / γ) ≤ cα / 4 :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hκ2 : min (min (cα / 4) (1 / 3)) (d0 / γ) ≤ 1 / 3 :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hκ3 : min (min (cα / 4) (1 / 3)) (d0 / γ) ≤ d0 / γ := min_le_right _ _
  rcases le_or_gt m1 (γ / 2) with hm1h | hm1h
  · rcases le_or_gt m2 (3 * γ / 4) with hm2h | hm2h
    · have h4 : 1 / 4 ≤ 1 - m2 / γ := by
        have : m2 / γ ≤ 3 / 4 := by rw [div_le_iff₀ hγ]; linarith
        linarith
      have : cα / 4 * a ≤ cα * (a * (1 - m2 / γ)) := by nlinarith [mul_pos hcα ha]
      calc _ ≤ cα / 4 * a := mul_le_mul_of_nonneg_right hκ1 ha.le
        _ ≤ cα * (a * (1 - m2 / γ)) := this
        _ = cα * (a * (1 - m2 / γ)) := rfl
        _ ≤ a * (1 - T / m2) := by linarith
        _ ≤ _ := hbase
    · have h3 : 1 / 3 ≤ 1 - T / m2 := by
        have hTm : T / m2 ≤ 2 / 3 := by
          rw [div_le_iff₀ hm2]; nlinarith
        linarith
      calc _ ≤ 1 / 3 * a := mul_le_mul_of_nonneg_right hκ2 ha.le
        _ ≤ a * (1 - T / m2) := by nlinarith
        _ ≤ _ := hbase
  · have hd := hgap hm1h
    have hsum : γ < m1 + m2 := by linarith
    have hm2γ : m2 < γ := h2γ
    have hid : (1 - T * M / (m1 * m2)) * (1 - M / γ) - T * D2 / (γ * m1 * m2) -
        a * (1 - T / m2) =
        T * ((m1 - M) * (m2 - M) - D2) / (γ * (m1 * m2)) +
          (m1 * m2 + T * (γ - m1 - m2)) / (γ * (m1 * m2)) * (m1 - M) := by
      rw [hadef]
      field_simp
      ring
    have hb0 : 0 ≤ a * (1 - T / m2) := by
      refine mul_nonneg ha.le ?_
      have : T / m2 ≤ 1 := by rw [div_le_one hm2]; exact hT1.trans h12
      linarith
    have a1 : 0 ≤ T * ((m1 - M) * (m2 - M) - D2) / (γ * (m1 * m2)) :=
      div_nonneg (mul_nonneg hT0 (sub_nonneg.2 hD)) (by positivity)
    have hc : m1 * (γ - m1) ≤ m1 * m2 + T * (γ - m1 - m2) := by
      nlinarith [mul_nonneg (sub_nonneg.2 hT1) (sub_nonneg.2 hsum.le)]
    have hnum : 0 ≤ m1 * m2 + T * (γ - m1 - m2) :=
      le_trans (mul_nonneg h1.le (by linarith)) hc
    have hc2 : a * (γ * m1) ≤ (m1 * m2 + T * (γ - m1 - m2)) := by
      have : a * (γ * m1) = m1 * (γ - m1) := by rw [hadef]; field_simp
      linarith
    have a2 : d0 / γ * a ≤
        (m1 * m2 + T * (γ - m1 - m2)) / (γ * (m1 * m2)) * (m1 - M) := by
      have h5 : a * (γ * m1) / (γ * (m1 * m2)) ≤
          (m1 * m2 + T * (γ - m1 - m2)) / (γ * (m1 * m2)) :=
        div_le_div_of_nonneg_right hc2 (by positivity)
      have h6 : a * (γ * m1) / (γ * (m1 * m2)) = a / m2 := by field_simp
      have h7 : a / γ ≤ a / m2 := div_le_div_of_nonneg_left ha.le hm2 h2γ.le
      have h8 : a / γ ≤ (m1 * m2 + T * (γ - m1 - m2)) / (γ * (m1 * m2)) := by
        rw [h6] at h5; exact h7.trans h5
      calc d0 / γ * a = a / γ * d0 := by ring
        _ ≤ (m1 * m2 + T * (γ - m1 - m2)) / (γ * (m1 * m2)) * (m1 - M) :=
          mul_le_mul h8 hd hd0.le (div_nonneg hnum (by positivity))
    calc min (min (cα / 4) (1 / 3)) (d0 / γ) * a ≤ d0 / γ * a :=
          mul_le_mul_of_nonneg_right hκ3 ha.le
      _ ≤ _ := by linarith [hid, a1, a2, hb0]

private lemma age_delta_lower {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (ℓ : ℤ) (m₁ m₂ : ℝ),
      m₁ ∈ Ioo 0 (gammaOf N B) → m₂ ∈ Ioo 0 (gammaOf N B) →
        κ * (1 - min m₁ m₂ / gammaOf N B) ≤ deltaN β B (plSpec α c N) ℓ m₁ m₂ := by
  have hγ : 0 < gammaOf N B := by unfold gammaOf; positivity
  have hpos := vk_pos_plSpec (α := α) hc N
  obtain ⟨cα, hcα, hchain⟩ := lem_app_pl_determinant_ii_chain hα
  have hγ2 : (0 : ℝ) < gammaOf N B / 2 := by positivity
  obtain ⟨hqa, -⟩ := vk_Qm hβ0 hβ1 hγ2
  obtain ⟨hqb, -⟩ := vk_Qm hβ0 hβ1 hγ
  obtain ⟨d0, hd0, hgap⟩ := age_gap hβ0 hβ1 hqa hqb.le
  refine ⟨min (min (cα / 4) (1 / 3)) (d0 / gammaOf N B), ?_, ?_⟩
  · have : 0 < d0 / gammaOf N B := div_pos hd0 hγ
    exact lt_min (lt_min (by positivity) (by norm_num)) this
  intro ℓ m₁ m₂ hm₁ hm₂
  obtain ⟨hq1, e1⟩ := vk_Qm hβ0 hβ1 hm₁.1
  obtain ⟨hq2, e2⟩ := vk_Qm hβ0 hβ1 hm₂.1
  have hmono := lp_Qm_mono hβ0 hβ1
  have hq1b : Qm β m₁ ≤ Qm β (gammaOf N B) := hmono (Set.mem_Ioi.2 hm₁.1) (Set.mem_Ioi.2 hγ) hm₁.2.le
  have hq2b : Qm β m₂ ≤ Qm β (gammaOf N B) := hmono (Set.mem_Ioi.2 hm₂.1) (Set.mem_Ioi.2 hγ) hm₂.2.le
  have hg1 : gammaOf N B / 2 < m₁ →
      d0 ≤ m₁ - MLag β (Qm β m₁) (Qm β m₂) ℓ := by
    intro h
    have := (hgap (Qm β m₁) (Qm β m₂)
      (hmono (Set.mem_Ioi.2 hγ2) (Set.mem_Ioi.2 hm₁.1) h.le) hq2.le hq2b ℓ).1
    rwa [e1] at this
  have hg2 : gammaOf N B / 2 < m₂ →
      d0 ≤ m₂ - MLag β (Qm β m₁) (Qm β m₂) ℓ := by
    intro h
    have := (hgap (Qm β m₂) (Qm β m₁)
      (hmono (Set.mem_Ioi.2 hγ2) (Set.mem_Ioi.2 hm₂.1) h.le) hq1.le hq1b ℓ).2
    rwa [e2] at this
  obtain ⟨hM0, hMmin, hD⟩ := vk_det_i hβ0 hβ1 hm₁.1 hm₂.1 ℓ
  have hch := hchain N B c hN hB hc m₁ m₂ hm₁ hm₂
  unfold deltaN
  generalize MLag β (Qm β m₁) (Qm β m₂) ℓ = M at hM0 hMmin hD hg1 hg2 ⊢
  generalize DLag β (Qm β m₁) (Qm β m₂) ℓ = D at hD ⊢
  rcases le_total m₁ m₂ with h | h
  · rw [min_eq_left h] at hch ⊢
    rw [max_eq_right h] at hch
    obtain ⟨hT0, hT1⟩ := vk_T_bd hB hN hpos hm₁ hm₂ h
    exact age_core (D2 := D ^ 2) hm₁.1 h hm₂.2 hT0 hT1 hM0 (hMmin.trans (min_le_left _ _)) hD
      hcα (by simpa [mul_comm, mul_left_comm, mul_assoc] using hch) hd0 hg1
  · rw [min_eq_right h] at hch ⊢
    rw [max_eq_left h] at hch
    obtain ⟨hT0, hT1⟩ := vk_T_bd hB hN hpos hm₂ hm₁ h
    rw [vk_TN_comm] at hch ⊢
    have hch' : cα * ((1 - m₂ / gammaOf N B) * (1 - m₁ / gammaOf N B)) ≤
        (1 - m₂ / gammaOf N B) * (1 - TNpart B (plSpec α c N) m₂ m₁ / m₁) := by
      have e : cα * ((1 - m₂ / gammaOf N B) * (1 - m₁ / gammaOf N B)) =
          cα * ((1 - m₁ / gammaOf N B) * (1 - m₂ / gammaOf N B)) := by ring
      rw [e]; exact hch
    have := age_core (D2 := D ^ 2) hm₂.1 h hm₁.2 hT0 hT1 hM0
      (hMmin.trans (min_le_right _ _))
      (by linarith [hD, mul_comm (m₁ - M) (m₂ - M)]) hcα hch' hd0 hg2
    have e : (1 - TNpart B (plSpec α c N) m₂ m₁ * M / (m₂ * m₁)) * (1 - M / gammaOf N B) -
        TNpart B (plSpec α c N) m₂ m₁ * D ^ 2 / (gammaOf N B * m₂ * m₁) =
        (1 - TNpart B (plSpec α c N) m₂ m₁ * M / (m₁ * m₂)) * (1 - M / gammaOf N B) -
        TNpart B (plSpec α c N) m₂ m₁ * D ^ 2 / (gammaOf N B * m₁ * m₂) := by ring
    rw [e] at this
    exact this

private lemma age_M_cont_R {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ℓ : ℕ) (R : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => MLagNat β q.1 q.2 ℓ)
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ R ∧ 0 ≤ q.2 ∧ q.2 ≤ R} := by
  unfold MLagNat
  have hs0 : 0 ≤ β ^ (2 * ℓ) := pow_nonneg hβ0.le _
  refine lp_cont_tsum (c := fun a => R * emaW β a ^ 2) (H := fun g => g ^ 2)
    ((vk_w2_summable hβ0 hβ1).mul_left R) (Muon.Foundations.gaussian_integrable_pow 2)
    (fun g => sq_nonneg g) ?_ ?_ ?_
  · intro a q hq
    refine Continuous.aestronglyMeasurable ?_
    have hq1 : 0 ≤ q.1 := hq.1
    have hq2 : 0 ≤ q.2 := hq.2.2.1
    have hd : ∀ g : ℝ, (1 + q.1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q.2 * emaW β a ^ 2 * g ^ 2) ≠ 0 := fun g => by
      have : 0 < (1 + q.1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q.2 * emaW β a ^ 2 * g ^ 2) := by positivity
      exact this.ne'
    exact (by fun_prop : Continuous fun g : ℝ => β ^ (2 * ℓ) * q.1 * q.2 *
        emaW β a ^ 4 * g ^ 4).div (by fun_prop) hd
  · intro a g
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (by fun_prop : Continuous fun q : ℝ × ℝ => β ^ (2 * ℓ) * q.1 * q.2 *
        emaW β a ^ 4 * g ^ 4).continuousOn
    · exact (by fun_prop : Continuous fun q : ℝ × ℝ => (1 + q.1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q.2 * emaW β a ^ 2 * g ^ 2)).continuousOn
    · intro q hq
      have hq1 : 0 ≤ q.1 := hq.1
      have hq2 : 0 ≤ q.2 := hq.2.2.1
      have : 0 < (1 + q.1 * emaW β a ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * q.2 * emaW β a ^ 2 * g ^ 2) := by positivity
      exact this.ne'
  · intro a q hq g
    obtain ⟨hq1, hq1R, hq2, hq2R⟩ := hq
    have hX : 0 ≤ q.1 * emaW β a ^ 2 * g ^ 2 := by positivity
    have hY : 0 ≤ β ^ (2 * ℓ) * q.2 * emaW β a ^ 2 * g ^ 2 := by positivity
    rw [age_Mterm_eq, abs_of_nonneg (by positivity)]
    refine ((vk_pw_bounds hX hY).2.2.1).trans ?_
    have h3 : 0 ≤ emaW β a ^ 2 * g ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hq1R h3]

private lemma age_MLag_cont {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ℓ : ℤ) :
    ContinuousOn (fun q : ℝ × ℝ => MLag β q.1 q.2 ℓ) {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} := by
  by_cases hℓ : 0 ≤ ℓ
  · have : (fun q : ℝ × ℝ => MLag β q.1 q.2 ℓ) = fun q => MLagNat β q.1 q.2 ℓ.toNat := by
      funext q; simp [MLag, hℓ]
    rw [this]
    exact lp_cont_of_R (fun R => age_M_cont_R hβ0 hβ1 _ R)
  · have : (fun q : ℝ × ℝ => MLag β q.1 q.2 ℓ) = fun q => MLagNat β q.2 q.1 (-ℓ).toNat := by
      funext q; simp [MLag, hℓ]
    rw [this]
    have h2 : ContinuousOn (fun q : ℝ × ℝ => MLagNat β q.1 q.2 (-ℓ).toNat)
        {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} :=
      lp_cont_of_R (fun R => age_M_cont_R hβ0 hβ1 _ R)
    exact h2.comp continuous_swap.continuousOn (fun q hq => ⟨hq.2, hq.1⟩)

private lemma age_Q2_cont {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {γ : ℝ} :
    ContinuousOn (fun p : ℝ × ℝ => (Qm β p.1, Qm β p.2)) (Ioo 0 γ ×ˢ Ioo 0 γ) := by
  have hQc : ContinuousOn (Qm β) (Ioo 0 γ) := (lp_Qm_cont hβ0 hβ1).mono (fun m hm => hm.1)
  exact (hQc.comp continuousOn_fst (fun p hp => hp.1)).prodMk
    (hQc.comp continuousOn_snd (fun p hp => hp.2))

private lemma age_DLag_cont2 {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {γ : ℝ} (ℓ : ℤ) :
    ContinuousOn (fun p : ℝ × ℝ => DLag β (Qm β p.1) (Qm β p.2) ℓ) (Ioo 0 γ ×ˢ Ioo 0 γ) := by
  exact ContinuousOn.comp (g := fun q : ℝ × ℝ => DLag β q.1 q.2 ℓ)
    (f := fun p : ℝ × ℝ => (Qm β p.1, Qm β p.2)) (lp_DLag_cont hβ0 hβ1 ℓ)
    (age_Q2_cont hβ0 hβ1) (fun p hp => ⟨(vk_Qm hβ0 hβ1 hp.1.1).1.le, (vk_Qm hβ0 hβ1 hp.2.1).1.le⟩)

private lemma age_MLag_cont2 {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {γ : ℝ} (ℓ : ℤ) :
    ContinuousOn (fun p : ℝ × ℝ => MLag β (Qm β p.1) (Qm β p.2) ℓ) (Ioo 0 γ ×ˢ Ioo 0 γ) := by
  exact ContinuousOn.comp (g := fun q : ℝ × ℝ => MLag β q.1 q.2 ℓ)
    (f := fun p : ℝ × ℝ => (Qm β p.1, Qm β p.2)) (age_MLag_cont hβ0 hβ1 ℓ)
    (age_Q2_cont hβ0 hβ1) (fun p hp => ⟨(vk_Qm hβ0 hβ1 hp.1.1).1.le, (vk_Qm hβ0 hβ1 hp.2.1).1.le⟩)

private lemma age_TN_cont {α : ℝ} {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) :
    ContinuousOn (fun p : ℝ × ℝ => TNpart B (plSpec α c N) p.1 p.2)
      (Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B)) := by
  have hpos := vk_pos_plSpec (α := α) hc N
  have hbij := def_app_pl_participation_bij (plSpec α c N) hB hN hpos
  have hΛc : ContinuousOn (partLam B (plSpec α c N)) (Ioo 0 (gammaOf N B)) :=
    hbij.2.2.2.continuousOn
  have hF : ∀ j : Fin N, ContinuousOn (partF B (plSpec α c N) j) (Ioo 0 (gammaOf N B)) := by
    intro j
    unfold partF
    refine (hΛc.mul continuousOn_const).div (continuousOn_const.add (hΛc.mul continuousOn_const)) ?_
    intro m hm
    have := mul_pos (vk_partLam_pos hB hN hpos hm) (hpos j)
    linarith
  unfold TNpart
  refine continuousOn_const.mul (continuousOn_finsetSum _ (fun j _ => ?_))
  exact ((hF j).comp continuousOn_fst (fun p hp => hp.1)).mul
    ((hF j).comp continuousOn_snd (fun p hp => hp.2))

private lemma age_delta_cont {α β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {N B : ℕ} {c : ℝ}
    (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) (ℓ : ℤ) :
    ContinuousOn (fun p : ℝ × ℝ => deltaN β B (plSpec α c N) ℓ p.1 p.2)
      (Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B)) := by
  have hγ : 0 < gammaOf N B := by unfold gammaOf; positivity
  have hT := age_TN_cont (α := α) hN hB hc
  have hM := age_MLag_cont2 (γ := gammaOf N B) hβ0 hβ1 ℓ
  have hD := age_DLag_cont2 (γ := gammaOf N B) hβ0 hβ1 ℓ
  have hmm : ContinuousOn (fun p : ℝ × ℝ => p.1 * p.2) (Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B)) :=
    continuousOn_fst.mul continuousOn_snd
  have hne : ∀ p ∈ Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B), p.1 * p.2 ≠ 0 :=
    fun p hp => (mul_pos hp.1.1 hp.2.1).ne'
  unfold deltaN
  refine ContinuousOn.sub (ContinuousOn.mul ?_ ?_) ?_
  · exact continuousOn_const.sub ((hT.mul hM).div hmm hne)
  · exact continuousOn_const.sub (hM.div_const _)
  · refine (hT.mul (hD.pow 2)).div ((continuousOn_const.mul continuousOn_fst).mul continuousOn_snd) ?_
    intro p hp
    exact (mul_pos (mul_pos hγ hp.1.1) hp.2.1).ne'

private lemma age_E_facts {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m₁ m₂ : ℝ} (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) :
    HasSum (fun ℓ : ℤ => DLag β (Qm β m₁) (Qm β m₂) ℓ)
        (∫ g : ℝ, Zg β g (Qm β m₁) * Zg β g (Qm β m₂) ∂(gaussianReal 0 1)) ∧
      0 ≤ ∫ g : ℝ, Zg β g (Qm β m₁) * Zg β g (Qm β m₂) ∂(gaussianReal 0 1) ∧
      ∫ g : ℝ, Zg β g (Qm β m₁) * Zg β g (Qm β m₂) ∂(gaussianReal 0 1) ≤
        Real.sqrt (Qm β m₁) * Real.sqrt (Qm β m₂) ∧
      ∀ ℓ : ℤ, DLag β (Qm β m₁) (Qm β m₂) ℓ ≤
        ∫ g : ℝ, Zg β g (Qm β m₁) * Zg β g (Qm β m₂) ∂(gaussianReal 0 1) := by
  obtain ⟨hint, hsum⟩ := lem_app_pl_age_iii hβ0 hβ1 m₁ m₂ hm₁ hm₂
  obtain ⟨hq₁, -⟩ := vk_Qm hβ0 hβ1 hm₁
  obtain ⟨hq₂, -⟩ := vk_Qm hβ0 hβ1 hm₂
  have hnn : ∀ ℓ : ℤ, 0 ≤ DLag β (Qm β m₁) (Qm β m₂) ℓ := fun ℓ =>
    age_DLag_nonneg hβ0 hq₁.le hq₂.le ℓ
  refine ⟨hsum, hsum.nonneg hnn, ?_, fun ℓ => le_hasSum hsum ℓ (fun j _ => hnn j)⟩
  have hmaj : Integrable (fun g : ℝ => (Real.sqrt (Qm β m₁) * Real.sqrt (Qm β m₂)) * g ^ 2)
      (gaussianReal 0 1) := (Muon.Foundations.gaussian_integrable_pow 2).const_mul _
  calc ∫ g : ℝ, Zg β g (Qm β m₁) * Zg β g (Qm β m₂) ∂(gaussianReal 0 1)
      ≤ ∫ g : ℝ, (Real.sqrt (Qm β m₁) * Real.sqrt (Qm β m₂)) * g ^ 2 ∂(gaussianReal 0 1) := by
        refine integral_mono hint hmaj (fun g => ?_)
        calc Zg β g (Qm β m₁) * Zg β g (Qm β m₂)
            ≤ |Zg β g (Qm β m₁) * Zg β g (Qm β m₂)| := le_abs_self _
          _ = |Zg β g (Qm β m₁)| * |Zg β g (Qm β m₂)| := abs_mul _ _
          _ ≤ (Real.sqrt (Qm β m₁) * |g|) * (Real.sqrt (Qm β m₂) * |g|) :=
              mul_le_mul (age_abs_le hβ0 hβ1 hq₁.le g) (age_abs_le hβ0 hβ1 hq₂.le g)
                (abs_nonneg _) (by positivity)
          _ = (Real.sqrt (Qm β m₁) * Real.sqrt (Qm β m₂)) * g ^ 2 := by
              rw [← sq_abs g]; ring
    _ = Real.sqrt (Qm β m₁) * Real.sqrt (Qm β m₂) := by
        rw [integral_const_mul, Muon.Foundations.gaussian_moment_two, mul_one]

private lemma age_key {P : Measure (ℝ × ℝ)} {F : ℤ → ℝ × ℝ → ℝ} {f : ℝ × ℝ → ℝ}
    (hmeas : ∀ ℓ, AEStronglyMeasurable (F ℓ) P) (h0 : ∀ ℓ, ∀ᵐ p ∂P, 0 ≤ F ℓ p)
    (hlim : ∀ᵐ p ∂P, HasSum (fun ℓ => F ℓ p) (f p)) (hf : Integrable f P) :
    HasSum (fun ℓ => ∫ p, F ℓ p ∂P) (∫ p, f p ∂P) := by
  refine hasSum_integral_of_dominated_convergence F hmeas (fun ℓ => ?_)
    (hlim.mono fun p h => h.summable) ?_ hlim
  · filter_upwards [h0 ℓ] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg hp]
  · exact hf.congr (hlim.mono fun p h => h.tsum_eq.symm)

private lemma age_Zjoint_meas (β : ℝ) : Measurable (fun z : ℝ × ℝ => Zg β z.1 z.2) := by
  unfold Zg
  exact (measurable_snd.sqrt).mul (Measurable.tsum (fun a => by fun_prop))

private lemma age_Qmeas {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {G : Set ℝ}
    (hGm : MeasurableSet G) (hG0 : ∀ m ∈ G, 0 < m) :
    AEMeasurable (Qm β) (volume.restrict G) := by
  have hQc : ContinuousOn (Qm β) G := (lp_Qm_cont hβ0 hβ1).mono (fun m hm => hG0 m hm)
  exact (hQc.aestronglyMeasurable hGm).aemeasurable

private lemma age_ZZ_meas {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {G : Set ℝ}
    (hGm : MeasurableSet G) (hG0 : ∀ m ∈ G, 0 < m) :
    AEStronglyMeasurable (fun z : (ℝ × ℝ) × ℝ => Zg β z.2 (Qm β z.1.1) * Zg β z.2 (Qm β z.1.2))
      (((volume.restrict G).prod (volume.restrict G)).prod (gaussianReal 0 1)) := by
  have hQ := age_Qmeas hβ0 hβ1 hGm hG0
  have hQ1 : AEMeasurable (fun p : ℝ × ℝ => Qm β p.1)
      ((volume.restrict G).prod (volume.restrict G)) := hQ.comp_fst
  have hQ2 : AEMeasurable (fun p : ℝ × ℝ => Qm β p.2)
      ((volume.restrict G).prod (volume.restrict G)) := hQ.comp_snd
  have h1 : AEMeasurable (fun z : (ℝ × ℝ) × ℝ => Qm β z.1.1)
      (((volume.restrict G).prod (volume.restrict G)).prod (gaussianReal 0 1)) := hQ1.comp_fst
  have h2 : AEMeasurable (fun z : (ℝ × ℝ) × ℝ => Qm β z.1.2)
      (((volume.restrict G).prod (volume.restrict G)).prod (gaussianReal 0 1)) := hQ2.comp_fst
  have hZ := age_Zjoint_meas β
  have e1 := hZ.comp_aemeasurable (measurable_snd.aemeasurable.prodMk h1)
  have e2 := hZ.comp_aemeasurable (measurable_snd.aemeasurable.prodMk h2)
  exact (e1.mul e2).aestronglyMeasurable

private lemma age_hae {G : Set ℝ} (hGm : MeasurableSet G) {φ : ℝ × ℝ → Prop}
    (h : ∀ p ∈ G ×ˢ G, φ p) :
    ∀ᵐ p ∂((volume.restrict G).prod (volume.restrict G)), φ p := by
  have hP : (volume.restrict G).prod (volume.restrict G) = volume.restrict (G ×ˢ G) := by
    rw [Measure.prod_restrict]; rfl
  rw [hP]
  exact (ae_restrict_iff' (hGm.prod hGm)).2 (Filter.Eventually.of_forall h)

private lemma age_sum_gen {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {G : Set ℝ}
    (hGm : MeasurableSet G) (hG0 : ∀ m ∈ G, 0 < m)
    {W : ℝ → ℝ} (hWm : AEStronglyMeasurable W (volume.restrict G)) (hWnn : ∀ m ∈ G, 0 ≤ W m)
    {w : ℝ × ℝ → ℝ} (hwm : AEStronglyMeasurable w ((volume.restrict G).prod (volume.restrict G)))
    (hw0 : ∀ p ∈ G ×ˢ G, 0 ≤ w p)
    (hwi : Integrable (fun p : ℝ × ℝ => (W p.1 * Real.sqrt (Qm β p.1)) *
      (W p.2 * Real.sqrt (Qm β p.2)) * w p) ((volume.restrict G).prod (volume.restrict G)))
    (hDm : ∀ ℓ : ℤ, AEStronglyMeasurable
      (fun p : ℝ × ℝ => DLag β (Qm β p.1) (Qm β p.2) ℓ)
      ((volume.restrict G).prod (volume.restrict G))) :
    HasSum (fun ℓ : ℤ => ∫ p, W p.1 * W p.2 * DLag β (Qm β p.1) (Qm β p.2) ℓ * w p
        ∂((volume.restrict G).prod (volume.restrict G)))
      (∫ p, W p.1 * W p.2 * (∫ g : ℝ, Zg β g (Qm β p.1) * Zg β g (Qm β p.2) ∂(gaussianReal 0 1))
        * w p ∂((volume.restrict G).prod (volume.restrict G))) := by
  have hWm1 : AEStronglyMeasurable (fun p : ℝ × ℝ => W p.1)
      ((volume.restrict G).prod (volume.restrict G)) := hWm.comp_fst
  have hWm2 : AEStronglyMeasurable (fun p : ℝ × ℝ => W p.2)
      ((volume.restrict G).prod (volume.restrict G)) := hWm.comp_snd
  have hEm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => ∫ g : ℝ, Zg β g (Qm β p.1) * Zg β g (Qm β p.2) ∂(gaussianReal 0 1))
      ((volume.restrict G).prod (volume.restrict G)) :=
    (age_ZZ_meas hβ0 hβ1 hGm hG0).integral_prod_right'
  refine age_key (f := fun p : ℝ × ℝ => W p.1 * W p.2 *
    (∫ g : ℝ, Zg β g (Qm β p.1) * Zg β g (Qm β p.2) ∂(gaussianReal 0 1)) * w p)
    (fun ℓ => ((hWm1.mul hWm2).mul (hDm ℓ)).mul hwm) (fun ℓ => ?_) ?_ ?_
  · refine age_hae hGm (fun p hp => ?_)
    have := age_DLag_nonneg hβ0 (vk_Qm hβ0 hβ1 (hG0 _ hp.1)).1.le
      (vk_Qm hβ0 hβ1 (hG0 _ hp.2)).1.le ℓ
    have := hWnn _ hp.1
    have := hWnn _ hp.2
    have := hw0 p hp
    positivity
  · refine age_hae hGm (fun p hp => ?_)
    obtain ⟨hs, -, -, -⟩ := age_E_facts hβ0 hβ1 (hG0 _ hp.1) (hG0 _ hp.2)
    have := hs.mul_left (W p.1 * W p.2 * w p)
    convert this using 1
    · funext ℓ; ring
    · ring
  · refine Integrable.mono' hwi (((hWm1.mul hWm2).mul hEm).mul hwm) ?_
    refine age_hae hGm (fun p hp => ?_)
    obtain ⟨-, hE0, hE1, -⟩ := age_E_facts hβ0 hβ1 (hG0 _ hp.1) (hG0 _ hp.2)
    have h1 := hWnn _ hp.1
    have h2 := hWnn _ hp.2
    have h3 := hw0 p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc W p.1 * W p.2 * (∫ g : ℝ, Zg β g (Qm β p.1) * Zg β g (Qm β p.2) ∂(gaussianReal 0 1))
          * w p ≤ W p.1 * W p.2 * (Real.sqrt (Qm β p.1) * Real.sqrt (Qm β p.2)) * w p := by
          gcongr
      _ = _ := by ring

private lemma age_F_int {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {G : Set ℝ}
    (hGm : MeasurableSet G) (hG0 : ∀ m ∈ G, 0 < m)
    {W : ℝ → ℝ} (hWm : AEStronglyMeasurable W (volume.restrict G)) (hWnn : ∀ m ∈ G, 0 ≤ W m)
    {w : ℝ × ℝ → ℝ} (hwm : AEStronglyMeasurable w ((volume.restrict G).prod (volume.restrict G)))
    (hw0 : ∀ p ∈ G ×ˢ G, 0 ≤ w p)
    (hwi : Integrable (fun p : ℝ × ℝ => (W p.1 * Real.sqrt (Qm β p.1)) *
      (W p.2 * Real.sqrt (Qm β p.2)) * w p) ((volume.restrict G).prod (volume.restrict G)))
    (hDm : ∀ ℓ : ℤ, AEStronglyMeasurable
      (fun p : ℝ × ℝ => DLag β (Qm β p.1) (Qm β p.2) ℓ)
      ((volume.restrict G).prod (volume.restrict G))) (ℓ : ℤ) :
    Integrable (fun p : ℝ × ℝ => W p.1 * W p.2 * DLag β (Qm β p.1) (Qm β p.2) ℓ * w p)
      ((volume.restrict G).prod (volume.restrict G)) := by
  have hWm1 : AEStronglyMeasurable (fun p : ℝ × ℝ => W p.1)
      ((volume.restrict G).prod (volume.restrict G)) := hWm.comp_fst
  have hWm2 : AEStronglyMeasurable (fun p : ℝ × ℝ => W p.2)
      ((volume.restrict G).prod (volume.restrict G)) := hWm.comp_snd
  refine Integrable.mono' hwi (((hWm1.mul hWm2).mul (hDm ℓ)).mul hwm) ?_
  refine age_hae hGm (fun p hp => ?_)
  obtain ⟨-, -, -, hE⟩ := age_E_facts hβ0 hβ1 (hG0 _ hp.1) (hG0 _ hp.2)
  obtain ⟨-, -, hE1, -⟩ := age_E_facts hβ0 hβ1 (hG0 _ hp.1) (hG0 _ hp.2)
  have hD0 := age_DLag_nonneg hβ0 (vk_Qm hβ0 hβ1 (hG0 _ hp.1)).1.le
    (vk_Qm hβ0 hβ1 (hG0 _ hp.2)).1.le ℓ
  have h1 := hWnn _ hp.1
  have h2 := hWnn _ hp.2
  have h3 := hw0 p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc W p.1 * W p.2 * DLag β (Qm β p.1) (Qm β p.2) ℓ * w p ≤
        W p.1 * W p.2 * (Real.sqrt (Qm β p.1) * Real.sqrt (Qm β p.2)) * w p := by
        have := (hE ℓ).trans hE1
        gcongr
    _ = _ := by ring

private lemma age_flat_gen {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {G : Set ℝ}
    (hGm : MeasurableSet G) (hG0 : ∀ m ∈ G, 0 < m)
    {W : ℝ → ℝ} (hWm : AEStronglyMeasurable W (volume.restrict G)) (hWnn : ∀ m ∈ G, 0 ≤ W m)
    (hu : Integrable (fun m : ℝ => W m * Real.sqrt (Qm β m)) (volume.restrict G)) :
    Real.pi ^ 2 * ∫ g : ℝ, (Real.pi⁻¹ * ∫ m in G, W m * Zg β g (Qm β m)) ^ 2
        ∂(gaussianReal 0 1) =
      ∫ p, W p.1 * W p.2 * (∫ g : ℝ, Zg β g (Qm β p.1) * Zg β g (Qm β p.2) ∂(gaussianReal 0 1))
        ∂((volume.restrict G).prod (volume.restrict G)) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have huu : Integrable (fun p : ℝ × ℝ => (W p.1 * Real.sqrt (Qm β p.1)) *
      (W p.2 * Real.sqrt (Qm β p.2))) ((volume.restrict G).prod (volume.restrict G)) :=
    hu.mul_prod hu
  have hWm1 : AEStronglyMeasurable (fun z : (ℝ × ℝ) × ℝ => W z.1.1)
      (((volume.restrict G).prod (volume.restrict G)).prod (gaussianReal 0 1)) :=
    (hWm.comp_fst : AEStronglyMeasurable (fun p : ℝ × ℝ => W p.1)
      ((volume.restrict G).prod (volume.restrict G))).comp_fst
  have hWm2 : AEStronglyMeasurable (fun z : (ℝ × ℝ) × ℝ => W z.1.2)
      (((volume.restrict G).prod (volume.restrict G)).prod (gaussianReal 0 1)) :=
    (hWm.comp_snd : AEStronglyMeasurable (fun p : ℝ × ℝ => W p.2)
      ((volume.restrict G).prod (volume.restrict G))).comp_fst
  have hΨ : Integrable (Function.uncurry fun (p : ℝ × ℝ) (g : ℝ) =>
      (W p.1 * Zg β g (Qm β p.1)) * (W p.2 * Zg β g (Qm β p.2)))
      (((volume.restrict G).prod (volume.restrict G)).prod (gaussianReal 0 1)) := by
    have hmaj := Integrable.mul_prod huu (Muon.Foundations.gaussian_integrable_pow 2)
    refine Integrable.mono' hmaj ?_ ?_
    · have := (hWm1.mul hWm2).mul (age_ZZ_meas hβ0 hβ1 hGm hG0)
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Function.uncurry, Pi.mul_apply]
      ring
    · have hPγ : ((volume.restrict G).prod (volume.restrict G)).prod (gaussianReal 0 1) =
          ((volume : Measure (ℝ × ℝ)).prod (gaussianReal 0 1)).restrict ((G ×ˢ G) ×ˢ univ) := by
        have hP : (volume.restrict G).prod (volume.restrict G) = volume.restrict (G ×ˢ G) := by
          rw [Measure.prod_restrict]; rfl
        rw [hP, Measure.restrict_prod_eq_prod_univ]
      rw [hPγ]
      refine (ae_restrict_iff' ((hGm.prod hGm).prod MeasurableSet.univ)).2
        (Filter.Eventually.of_forall fun z hz => ?_)
      obtain ⟨⟨hz1, hz2⟩, -⟩ := hz
      have hq1 := (vk_Qm hβ0 hβ1 (hG0 _ hz1)).1
      have hq2 := (vk_Qm hβ0 hβ1 (hG0 _ hz2)).1
      have h1 := hWnn _ hz1
      have h2 := hWnn _ hz2
      simp only [Function.uncurry]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg h1, abs_of_nonneg h2]
      have b1 := age_abs_le hβ0 hβ1 hq1.le z.2
      have b2 := age_abs_le hβ0 hβ1 hq2.le z.2
      calc W z.1.1 * |Zg β z.2 (Qm β z.1.1)| * (W z.1.2 * |Zg β z.2 (Qm β z.1.2)|)
          ≤ W z.1.1 * (Real.sqrt (Qm β z.1.1) * |z.2|) *
              (W z.1.2 * (Real.sqrt (Qm β z.1.2) * |z.2|)) := by
            gcongr
        _ = (W z.1.1 * Real.sqrt (Qm β z.1.1)) * (W z.1.2 * Real.sqrt (Qm β z.1.2)) * z.2 ^ 2 := by
            rw [← sq_abs z.2]; ring
  have hswap := integral_integral_swap hΨ
  have hinner : ∀ p : ℝ × ℝ, ∫ g : ℝ, (W p.1 * Zg β g (Qm β p.1)) * (W p.2 * Zg β g (Qm β p.2))
      ∂(gaussianReal 0 1) = W p.1 * W p.2 *
        (∫ g : ℝ, Zg β g (Qm β p.1) * Zg β g (Qm β p.2) ∂(gaussianReal 0 1)) := by
    intro p
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only
    ring
  have hsq : ∀ g : ℝ, (Real.pi⁻¹ * ∫ m in G, W m * Zg β g (Qm β m)) ^ 2 =
      (Real.pi⁻¹) ^ 2 * ∫ p, (W p.1 * Zg β g (Qm β p.1)) * (W p.2 * Zg β g (Qm β p.2))
        ∂((volume.restrict G).prod (volume.restrict G)) := by
    intro g
    rw [mul_pow, integral_prod_mul (fun m => W m * Zg β g (Qm β m))
      (fun m => W m * Zg β g (Qm β m))]
    ring
  simp only [hsq]
  rw [integral_const_mul, ← hswap]
  simp only [hinner]
  field_simp

private lemma age_iv_main {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (N B : ℕ) (c : ℝ) (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) (i : Fin N) :
    (∀ ℓ : ℤ, IntegrableOn
        (fun p : ℝ × ℝ => lagNumer β B (plSpec α c N) i ℓ p.1 p.2)
        (Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B))) ∧
    HasSum (fun ℓ : ℤ => ∫ m₁ in Ioo 0 (gammaOf N B), ∫ m₂ in Ioo 0 (gammaOf N B),
        lagNumer β B (plSpec α c N) i ℓ m₁ m₂)
      (Real.pi ^ 2 * vFlat β B (plSpec α c N) i) ∧
    (∀ ℓ : ℤ, IntegrableOn
        (fun p : ℝ × ℝ => lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2)
        (Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B))) ∧
    Summable (fun ℓ : ℤ => lagTerm β B (plSpec α c N) i
      (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) ℓ) ∧
    0 ≤ vFlat β B (plSpec α c N) i ∧
    vFlat β B (plSpec α c N) i ≤ vIJ β B (plSpec α c N) i
      (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) := by
  classical
  have hγ : 0 < gammaOf N B := by unfold gammaOf; positivity
  have hGm : MeasurableSet (Ioo 0 (gammaOf N B)) := measurableSet_Ioo
  have hGG : MeasurableSet (Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B)) := hGm.prod hGm
  have hG0 : ∀ m ∈ Ioo 0 (gammaOf N B), 0 < m := fun m hm => hm.1
  have hWnn : ∀ m ∈ Ioo 0 (gammaOf N B), 0 ≤ Wpart β B (plSpec α c N) i m :=
    fun m hm => age_Wpart_nonneg hα hβ0 hβ1 hN hB hc i hm
  have hWc := age_W_cont (α := α) hβ0 hβ1 hN hB hc i
  have hWm : AEStronglyMeasurable (Wpart β B (plSpec α c N) i)
      (volume.restrict (Ioo 0 (gammaOf N B))) := hWc.aestronglyMeasurable hGm
  have hQc : ContinuousOn (Qm β) (Ioo 0 (gammaOf N B)) :=
    (lp_Qm_cont hβ0 hβ1).mono (fun m hm => hm.1)
  have hP : (volume.restrict (Ioo 0 (gammaOf N B))).prod (volume.restrict (Ioo 0 (gammaOf N B))) =
      volume.restrict (Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B)) := by
    rw [Measure.prod_restrict]; rfl
  -- integrability of V and u
  have hs_pos : ∀ m ∈ Ioo 0 (gammaOf N B), 0 < Real.sqrt (1 - m / gammaOf N B) := by
    intro m hm
    refine Real.sqrt_pos.2 ?_
    rw [sub_pos, div_lt_one hγ]; exact hm.2
  have hs_le : ∀ m ∈ Ioo 0 (gammaOf N B), Real.sqrt (1 - m / gammaOf N B) ≤ 1 := by
    intro m hm
    refine Real.sqrt_le_one.2 ?_
    have : 0 ≤ m / gammaOf N B := by have := hm.1; positivity
    linarith
  have hV : Integrable (fun m : ℝ => Wpart β B (plSpec α c N) i m * Real.sqrt (Qm β m) /
      Real.sqrt (1 - m / gammaOf N B)) (volume.restrict (Ioo 0 (gammaOf N B))) :=
    age_V_int hα hβ0 hβ1 hN hB hc i
  have hu : Integrable (fun m : ℝ => Wpart β B (plSpec α c N) i m * Real.sqrt (Qm β m))
      (volume.restrict (Ioo 0 (gammaOf N B))) := by
    refine Integrable.mono' hV ((hWc.mul hQc.sqrt).aestronglyMeasurable hGm) ?_
    refine (ae_restrict_iff' hGm).2 (Filter.Eventually.of_forall fun m hm => ?_)
    have h0 : 0 ≤ Wpart β B (plSpec α c N) i m * Real.sqrt (Qm β m) :=
      mul_nonneg (hWnn m hm) (Real.sqrt_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact le_div_self h0 (hs_pos m hm) (hs_le m hm)
  have hDm : ∀ ℓ : ℤ, AEStronglyMeasurable (fun p : ℝ × ℝ => DLag β (Qm β p.1) (Qm β p.2) ℓ)
      ((volume.restrict (Ioo 0 (gammaOf N B))).prod (volume.restrict (Ioo 0 (gammaOf N B)))) := by
    intro ℓ
    rw [hP]
    exact (age_DLag_cont2 hβ0 hβ1 ℓ).aestronglyMeasurable hGG
  obtain ⟨ω, hωdef⟩ : ∃ ω : ℝ × ℝ → ℝ, ω = fun p => (Real.sqrt (1 - p.1 / gammaOf N B) *
      Real.sqrt (1 - p.2 / gammaOf N B))⁻¹ := ⟨_, rfl⟩
  have hω0 : ∀ p ∈ Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B), 0 ≤ ω p := by
    intro p hp
    rw [hωdef]
    exact inv_nonneg.2 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hωc : ContinuousOn ω (Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B)) := by
    rw [hωdef]
    refine ContinuousOn.inv₀ ?_ ?_
    · exact ((continuousOn_const.sub (continuousOn_fst.div_const _)).sqrt).mul
        ((continuousOn_const.sub (continuousOn_snd.div_const _)).sqrt)
    · intro p hp
      exact (mul_pos (hs_pos _ hp.1) (hs_pos _ hp.2)).ne'
  have hωm : AEStronglyMeasurable ω
      ((volume.restrict (Ioo 0 (gammaOf N B))).prod (volume.restrict (Ioo 0 (gammaOf N B)))) := by
    rw [hP]; exact hωc.aestronglyMeasurable hGG
  have huu : Integrable (fun p : ℝ × ℝ => (Wpart β B (plSpec α c N) i p.1 * Real.sqrt (Qm β p.1)) *
      (Wpart β B (plSpec α c N) i p.2 * Real.sqrt (Qm β p.2)) * (fun _ : ℝ × ℝ => (1 : ℝ)) p)
      ((volume.restrict (Ioo 0 (gammaOf N B))).prod (volume.restrict (Ioo 0 (gammaOf N B)))) := by
    simpa using hu.mul_prod hu
  have huω : Integrable (fun p : ℝ × ℝ => (Wpart β B (plSpec α c N) i p.1 * Real.sqrt (Qm β p.1)) *
      (Wpart β B (plSpec α c N) i p.2 * Real.sqrt (Qm β p.2)) * ω p)
      ((volume.restrict (Ioo 0 (gammaOf N B))).prod (volume.restrict (Ioo 0 (gammaOf N B)))) := by
    refine (hV.mul_prod hV).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [hωdef, div_eq_mul_inv, mul_inv]
    ring
  have hS1 := age_sum_gen hβ0 hβ1 hGm hG0 hWm hWnn (w := fun _ : ℝ × ℝ => (1 : ℝ))
    aestronglyMeasurable_const (fun _ _ => zero_le_one) huu hDm
  have hSω := age_sum_gen hβ0 hβ1 hGm hG0 hWm hWnn (w := ω) hωm hω0 huω hDm
  have hF1 := age_F_int hβ0 hβ1 hGm hG0 hWm hWnn (w := fun _ : ℝ × ℝ => (1 : ℝ))
    aestronglyMeasurable_const (fun _ _ => zero_le_one) huu hDm
  have hFω := age_F_int hβ0 hβ1 hGm hG0 hWm hWnn (w := ω) hωm hω0 huω hDm
  have hflat := age_flat_gen hβ0 hβ1 hGm hG0 hWm hWnn hu
  have hNint : ∀ ℓ : ℤ, Integrable
      (fun p : ℝ × ℝ => lagNumer β B (plSpec α c N) i ℓ p.1 p.2)
      ((volume.restrict (Ioo 0 (gammaOf N B))).prod (volume.restrict (Ioo 0 (gammaOf N B)))) := by
    intro ℓ
    refine (hF1 ℓ).congr (Filter.Eventually.of_forall fun p => ?_)
    simp [lagNumer]
  obtain ⟨κ, hκ, hκΔ⟩ := age_delta_lower hα hβ0 hβ1 hN hB hc
  have hΔlow : ∀ (ℓ : ℤ), ∀ p ∈ Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B),
      κ * (Real.sqrt (1 - p.1 / gammaOf N B) * Real.sqrt (1 - p.2 / gammaOf N B)) ≤
        deltaN β B (plSpec α c N) ℓ p.1 p.2 := by
    intro ℓ p hp
    refine le_trans ?_ (hκΔ ℓ p.1 p.2 hp.1 hp.2)
    refine mul_le_mul_of_nonneg_left ?_ hκ.le
    have h1 : 0 ≤ 1 - p.1 / gammaOf N B := by
      have := (hs_pos _ hp.1); exact Real.sqrt_pos.1 this |>.le
    have h2 : 0 ≤ 1 - p.2 / gammaOf N B := by
      have := (hs_pos _ hp.2); exact Real.sqrt_pos.1 this |>.le
    rcases le_total p.1 p.2 with h | h
    · rw [min_eq_left h]
      have hle : Real.sqrt (1 - p.2 / gammaOf N B) ≤ Real.sqrt (1 - p.1 / gammaOf N B) :=
        Real.sqrt_le_sqrt (by have := div_le_div_of_nonneg_right h hγ.le; linarith)
      calc Real.sqrt (1 - p.1 / gammaOf N B) * Real.sqrt (1 - p.2 / gammaOf N B)
          ≤ Real.sqrt (1 - p.1 / gammaOf N B) * Real.sqrt (1 - p.1 / gammaOf N B) :=
            mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _)
        _ = 1 - p.1 / gammaOf N B := Real.mul_self_sqrt h1
    · rw [min_eq_right h]
      have hle : Real.sqrt (1 - p.1 / gammaOf N B) ≤ Real.sqrt (1 - p.2 / gammaOf N B) :=
        Real.sqrt_le_sqrt (by have := div_le_div_of_nonneg_right h hγ.le; linarith)
      calc Real.sqrt (1 - p.1 / gammaOf N B) * Real.sqrt (1 - p.2 / gammaOf N B)
          ≤ Real.sqrt (1 - p.2 / gammaOf N B) * Real.sqrt (1 - p.2 / gammaOf N B) := by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _)
        _ = 1 - p.2 / gammaOf N B := Real.mul_self_sqrt h2
  have hΔpos : ∀ (ℓ : ℤ), ∀ p ∈ Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B),
      0 < deltaN β B (plSpec α c N) ℓ p.1 p.2 := by
    intro ℓ p hp
    exact lt_of_lt_of_le (mul_pos hκ (mul_pos (hs_pos _ hp.1) (hs_pos _ hp.2))) (hΔlow ℓ p hp)
  have hIle : ∀ (ℓ : ℤ), ∀ p ∈ Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B),
      0 ≤ lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 ∧
        lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 ≤
          κ⁻¹ * (lagNumer β B (plSpec α c N) i ℓ p.1 p.2 * ω p) := by
    intro ℓ p hp
    have hN0 := age_lagNumer_nonneg hα hβ0 hβ1 hN hB hc i ℓ hp.1 hp.2
    have hd := hΔpos ℓ p hp
    have hs1 := hs_pos _ hp.1
    have hs2 := hs_pos _ hp.2
    refine ⟨div_nonneg hN0 hd.le, ?_⟩
    unfold lagIntegrand
    calc lagNumer β B (plSpec α c N) i ℓ p.1 p.2 / deltaN β B (plSpec α c N) ℓ p.1 p.2
        ≤ lagNumer β B (plSpec α c N) i ℓ p.1 p.2 /
            (κ * (Real.sqrt (1 - p.1 / gammaOf N B) * Real.sqrt (1 - p.2 / gammaOf N B))) :=
          div_le_div_of_nonneg_left hN0 (mul_pos hκ (mul_pos hs1 hs2)) (hΔlow ℓ p hp)
      _ = κ⁻¹ * (lagNumer β B (plSpec α c N) i ℓ p.1 p.2 * ω p) := by
          rw [hωdef]
          field_simp
  have hNc : ∀ ℓ : ℤ, ContinuousOn
      (fun p : ℝ × ℝ => lagNumer β B (plSpec α c N) i ℓ p.1 p.2)
      (Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B)) := by
    intro ℓ
    unfold lagNumer
    exact ((hWc.comp continuousOn_fst (fun p hp => hp.1)).mul
      (hWc.comp continuousOn_snd (fun p hp => hp.2))).mul (age_DLag_cont2 hβ0 hβ1 ℓ)
  have hIcont : ∀ ℓ : ℤ, ContinuousOn
      (fun p : ℝ × ℝ => lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2)
      (Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B)) := by
    intro ℓ
    unfold lagIntegrand
    exact (hNc ℓ).div (age_delta_cont hβ0 hβ1 hN hB hc ℓ) (fun p hp => (hΔpos ℓ p hp).ne')
  have hIint : ∀ ℓ : ℤ, Integrable
      (fun p : ℝ × ℝ => lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2)
      ((volume.restrict (Ioo 0 (gammaOf N B))).prod (volume.restrict (Ioo 0 (gammaOf N B)))) := by
    intro ℓ
    refine Integrable.mono' ((hFω ℓ).const_mul κ⁻¹) ?_ ?_
    · rw [hP]; exact (hIcont ℓ).aestronglyMeasurable hGG
    · refine age_hae hGm (fun p hp => ?_)
      obtain ⟨h0, h1⟩ := hIle ℓ p hp
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact h1
  have hterm_eq : ∀ ℓ : ℤ, lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B))
      (Ioo 0 (gammaOf N B)) ℓ = ∫ p, lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2
        ∂((volume.restrict (Ioo 0 (gammaOf N B))).prod (volume.restrict (Ioo 0 (gammaOf N B)))) :=
    fun ℓ => (integral_prod (fun p : ℝ × ℝ => lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2)
      (hIint ℓ)).symm
  have hnum_eq : ∀ ℓ : ℤ, (∫ m₁ in Ioo 0 (gammaOf N B), ∫ m₂ in Ioo 0 (gammaOf N B),
      lagNumer β B (plSpec α c N) i ℓ m₁ m₂) = ∫ p, lagNumer β B (plSpec α c N) i ℓ p.1 p.2
        ∂((volume.restrict (Ioo 0 (gammaOf N B))).prod (volume.restrict (Ioo 0 (gammaOf N B)))) :=
    fun ℓ => (integral_prod (fun p : ℝ × ℝ => lagNumer β B (plSpec α c N) i ℓ p.1 p.2)
      (hNint ℓ)).symm
  have hsum2 : HasSum (fun ℓ : ℤ => ∫ m₁ in Ioo 0 (gammaOf N B), ∫ m₂ in Ioo 0 (gammaOf N B),
        lagNumer β B (plSpec α c N) i ℓ m₁ m₂)
      (Real.pi ^ 2 * vFlat β B (plSpec α c N) i) := by
    have e : Real.pi ^ 2 * vFlat β B (plSpec α c N) i = ∫ p, Wpart β B (plSpec α c N) i p.1 *
        Wpart β B (plSpec α c N) i p.2 * (∫ g : ℝ, Zg β g (Qm β p.1) * Zg β g (Qm β p.2)
        ∂(gaussianReal 0 1)) * (fun _ : ℝ × ℝ => (1 : ℝ)) p
        ∂((volume.restrict (Ioo 0 (gammaOf N B))).prod
          (volume.restrict (Ioo 0 (gammaOf N B)))) := by
      simp only [mul_one]
      rw [← hflat]
      rfl
    rw [e]
    convert hS1 using 1
    funext ℓ
    rw [hnum_eq ℓ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp [lagNumer]
  have hsum4 : Summable (fun ℓ : ℤ => lagTerm β B (plSpec α c N) i
      (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) ℓ) := by
    refine Summable.of_nonneg_of_le (fun ℓ => ?_) (fun ℓ => ?_) (hSω.summable.mul_left κ⁻¹)
    · rw [hterm_eq ℓ]
      exact integral_nonneg_of_ae ((age_hae hGm (fun p hp => (hIle ℓ p hp).1)))
    · rw [hterm_eq ℓ, ← integral_const_mul]
      refine integral_mono_ae (hIint ℓ) ((hFω ℓ).const_mul κ⁻¹) ?_
      exact age_hae hGm (fun p hp => (hIle ℓ p hp).2)
  refine ⟨fun ℓ => ?_, hsum2, fun ℓ => ?_, hsum4, age_vFlat_nonneg β B _ i, ?_⟩
  · rw [IntegrableOn, ← hP]; exact hNint ℓ
  · rw [IntegrableOn, ← hP]; exact hIint ℓ
  · have hle : Real.pi ^ 2 * vFlat β B (plSpec α c N) i ≤
        ∑' ℓ : ℤ, lagTerm β B (plSpec α c N) i (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) ℓ := by
      refine hasSum_le (fun ℓ => ?_) hsum2 hsum4.hasSum
      rw [hnum_eq ℓ, hterm_eq ℓ]
      refine integral_mono_ae (hNint ℓ) (hIint ℓ) ?_
      exact age_hae hGm (fun p hp => (age_kernel_order hα hβ0 hβ1 hN hB hc i ℓ hp.1 hp.2).2)
    unfold vIJ
    have hpi : 0 < Real.pi ^ 2 := by positivity
    rw [← mul_le_mul_iff_of_pos_left hpi, ← mul_assoc, mul_inv_cancel₀ hpi.ne', one_mul]
    exact hle

/-- `lem:app-pl-age`, part (iv) (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Age factorization]\label{lem:app-pl-age}
For real $g$ and $q>0$ put $\mathcal Z_g(q)\defeq\sqrt q\sum_{a\ge0}\emaw ag\,(1+\emaw a^2qg^2)^{-1}$.
\begin{enumerate}[label=(\roman*)]
\item $\abs{\mathcal Z_g(q)}\le C_\bmom$ and $\EE\,\mathcal Z_g(q)^2\le q$, for $g\sim\mathcal N(0,1)$.
\item For $m_0>0$ and $\mathcal A_g(m)\defeq\mathcal Z_g(Q_m)/E(m)$,
\[
\sup_{t\ge m_0}\Big|\int_{m_0}^t\big(\mathcal A_g(m)-\pi\sign(g)\big)\,\dif m\Big|\le C_{\bmom,m_0}\big(1+\abs{\log\abs g}\big)\qquad(g\ne0).
\]
\item $\sum_{\ell\in\mathbb Z}\mathsf D_\ell(m_1,m_2)=\EE\big[\mathcal Z_g(Q_{m_1})\mathcal Z_g(Q_{m_2})\big]$.
\item The flat coefficient
$\mathfrak v^{\mathrm{flat}}_i\defeq\EE\big[\big(\frac1\pi\int_0^\gamma W_i(m)\mathcal Z_g(Q_m)\,\dif m\big)^2\big]$ satisfies
$0\le\mathfrak v^{\mathrm{flat}}_i\le\mathfrak v_i(0)$, and it is the integral of \cref{eqn:app-pl-vol-zero}
summed over the lags with every $\Delta^N_\ell$ replaced by one.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_age_iv {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (N B : ℕ) (c : ℝ) (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) (i : Fin N) :
    (∀ ℓ : ℤ, IntegrableOn
        (fun p : ℝ × ℝ => lagNumer β B (plSpec α c N) i ℓ p.1 p.2)
        (Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B))) ∧
    HasSum (fun ℓ : ℤ => ∫ m₁ in Ioo 0 (gammaOf N B), ∫ m₂ in Ioo 0 (gammaOf N B),
        lagNumer β B (plSpec α c N) i ℓ m₁ m₂)
      (Real.pi ^ 2 * vFlat β B (plSpec α c N) i) ∧
    (∀ ℓ : ℤ, IntegrableOn
        (fun p : ℝ × ℝ => lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2)
        (Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B))) ∧
    Summable (fun ℓ : ℤ => lagTerm β B (plSpec α c N) i
      (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) ℓ) ∧
    0 ≤ vFlat β B (plSpec α c N) i ∧
    vFlat β B (plSpec α c N) i ≤ vIJ β B (plSpec α c N) i
      (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) := by
  exact age_iv_main hα hβ0 hβ1 N B c hN hB hc i

/-! ### Private helpers for `lem_app_pl_upper` -/

private lemma upper_finiteness {α β η : ℝ} (hα : 0 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hη0 : 0 < η) {N B : ℕ} {c : ℝ} (hN : 0 < N)
    (hB : 0 < B) (hc : 0 < c) (i : Fin N) :
    (∀ ℓ : ℤ, IntegrableOn
        (fun p : ℝ × ℝ => lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2)
        (Ico (η * gammaOf N B) (gammaOf N B) ×ˢ
          Ico (η * gammaOf N B) (gammaOf N B))) ∧
      Summable (fun ℓ : ℤ => lagTerm β B (plSpec α c N) i
        (Ico (η * gammaOf N B) (gammaOf N B))
        (Ico (η * gammaOf N B) (gammaOf N B)) ℓ) := by
  let G : Set ℝ := Ico (η * gammaOf N B) (gammaOf N B)
  let H : Set ℝ := Ioo 0 (gammaOf N B)
  have hγ : 0 < gammaOf N B := by unfold gammaOf; positivity
  have hGH : G ⊆ H := by
    intro m hm
    exact ⟨(mul_pos hη0 hγ).trans_le hm.1, hm.2⟩
  have hGm : MeasurableSet G := measurableSet_Ico
  have hHm : MeasurableSet H := measurableSet_Ioo
  have hsub : G ×ˢ G ⊆ H ×ˢ H := prod_mono hGH hGH
  have hfull := lem_app_pl_age_iv hα hβ0 hβ1 N B c hN hB hc i
  have hInt : ∀ ℓ : ℤ, IntegrableOn
      (fun p : ℝ × ℝ => lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2) (G ×ˢ G) :=
    fun ℓ => (hfull.2.2.1 ℓ).mono_set hsub
  refine ⟨hInt, ?_⟩
  have hP_G : (volume.restrict G).prod (volume.restrict G) =
      volume.restrict (G ×ˢ G) := by rw [Measure.prod_restrict]; rfl
  have hP_H : (volume.restrict H).prod (volume.restrict H) =
      volume.restrict (H ×ˢ H) := by rw [Measure.prod_restrict]; rfl
  have htermG : ∀ ℓ : ℤ, lagTerm β B (plSpec α c N) i G G ℓ =
      ∫ p, lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2
        ∂((volume.restrict G).prod (volume.restrict G)) := by
    intro ℓ
    exact (integral_prod
      (fun p : ℝ × ℝ => lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2)
      (by rw [hP_G]; exact hInt ℓ)).symm
  have htermH : ∀ ℓ : ℤ, lagTerm β B (plSpec α c N) i H H ℓ =
      ∫ p, lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2
        ∂((volume.restrict H).prod (volume.restrict H)) := by
    intro ℓ
    exact (integral_prod
      (fun p : ℝ × ℝ => lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2)
      (by rw [hP_H]; exact hfull.2.2.1 ℓ)).symm
  refine Summable.of_nonneg_of_le (fun ℓ => ?_) (fun ℓ => ?_) hfull.2.2.2.1
  · rw [htermG ℓ, hP_G]
    refine integral_nonneg_of_ae ((ae_restrict_iff' (hGm.prod hGm)).2
      (Filter.Eventually.of_forall fun p hp => ?_))
    exact (age_kernel_order hα hβ0 hβ1 hN hB hc i ℓ (hGH hp.1) (hGH hp.2)).1.trans
      (age_kernel_order hα hβ0 hβ1 hN hB hc i ℓ (hGH hp.1) (hGH hp.2)).2
  · rw [htermG ℓ, htermH ℓ, hP_G, hP_H]
    exact setIntegral_mono_set (hfull.2.2.1 ℓ)
      ((ae_restrict_iff' (hHm.prod hHm)).2
        (Filter.Eventually.of_forall fun p hp =>
          (age_kernel_order hα hβ0 hβ1 hN hB hc i ℓ
            hp.1 hp.2).1.trans
            (age_kernel_order hα hβ0 hβ1 hN hB hc i ℓ
              hp.1 hp.2).2))
      hsub.eventuallySubset

private lemma upper_D_sum {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m₁ m₂ : ℝ, 0 < m₁ → 0 < m₂ →
      HasSum (fun ℓ : ℤ => DLag β (Qm β m₁) (Qm β m₂) ℓ)
        (∫ g : ℝ, Zg β g (Qm β m₁) * Zg β g (Qm β m₂)
          ∂(gaussianReal 0 1)) ∧
      (∫ g : ℝ, Zg β g (Qm β m₁) * Zg β g (Qm β m₂)
          ∂(gaussianReal 0 1)) ≤ C := by
  obtain ⟨C, hC⟩ := (lem_app_pl_age_i hβ0 hβ1).1
  have hC0 : 0 ≤ C := by
    simpa [Zg] using hC 1 0 one_pos
  refine ⟨C ^ 2, sq_nonneg C, fun m₁ m₂ hm₁ hm₂ => ?_⟩
  obtain ⟨hint, hsum⟩ := lem_app_pl_age_iii hβ0 hβ1 m₁ m₂ hm₁ hm₂
  obtain ⟨hq₁, -⟩ := vk_Qm hβ0 hβ1 hm₁
  obtain ⟨hq₂, -⟩ := vk_Qm hβ0 hβ1 hm₂
  refine ⟨hsum, ?_⟩
  have hconst : Integrable (fun _ : ℝ => C ^ 2) (gaussianReal 0 1) := integrable_const _
  calc
    (∫ g : ℝ, Zg β g (Qm β m₁) * Zg β g (Qm β m₂) ∂(gaussianReal 0 1))
        ≤ ∫ _g : ℝ, C ^ 2 ∂(gaussianReal 0 1) := by
          refine integral_mono hint hconst (fun g => ?_)
          calc
            Zg β g (Qm β m₁) * Zg β g (Qm β m₂)
                ≤ |Zg β g (Qm β m₁)| * |Zg β g (Qm β m₂)| := by
                  rw [← abs_mul]
                  exact le_abs_self _
            _ ≤ C * C := mul_le_mul (hC _ _ hq₁) (hC _ _ hq₂) (abs_nonneg _) hC0
            _ = C ^ 2 := by ring
    _ = C ^ 2 := by simp

private lemma upper_finV_pos {α : ℝ} {N B : ℕ} (c : ℝ) (hN : 0 < N)
    (hB : 0 < B) (hc : 0 < c) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < finV α N p := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hBr : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hγ : 0 < gammaOf N B := by unfold gammaOf; exact div_pos hNr hBr
  have hmI : gammaOf N B * p ∈ Ioo 0 (gammaOf N B) :=
    ⟨mul_pos hγ hp0, by nlinarith⟩
  have hLpos : 0 < partLam B (plSpec α c N) (gammaOf N B * p) :=
    (def_app_pl_participation_bij (plSpec α c N) hB hN (vk_pos_plSpec hc N)).2.1.mapsTo hmI
  have hLV := eqn_app_pl_Lambda_V (N := N) (B := B) α c hN hB hc hmI
  rw [mul_div_cancel_left₀ p hγ.ne'] at hLV
  have hNα : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hNr α
  have h1 : 0 < (N : ℝ) ^ α / c * finV α N p := hLV ▸ hLpos
  exact pos_of_mul_pos_right h1 (div_pos hNα hc).le

private lemma upper_aN_pos {α c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 0 < N) :
    0 < aN α c N := by
  unfold aN
  have : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

private lemma upper_B_top {α : ℝ} (hα : 0 < α) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N B : ℕ) (c : ℝ) (i : Fin N), 0 < N → 0 < B → 0 < c →
      ∀ m : ℝ, gammaOf N B / 2 ≤ m → m < gammaOf N B →
        partBfun B (plSpec α c N) i m ≤
          K * aN α c N * ((gammaOf N B - m) / gammaOf N B) := by
  obtain ⟨c₃, C₃, hc₃, hC₃, h₃⟩ := lem_app_pl_finite_inverse_iii hα
  refine ⟨Real.sqrt (2 / c₃), by positivity, fun N B c i hN hB hc m hm1 hm2 => ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  set γ := gammaOf N B with hγ
  have hγ0 : 0 < γ := by rw [hγ]; unfold gammaOf; positivity
  set p := m / γ with hp
  have hp0 : 0 < p := by
    have : 0 < m := by linarith
    positivity
  have hp1 : p < 1 := by rw [hp, div_lt_one hγ0]; exact hm2
  have hphalf : 1 / 2 ≤ p := by rw [hp, le_div_iff₀ hγ0]; linarith
  have hmp : γ * p = m := by rw [hp]; field_simp
  have hbulk := eqn_app_pl_Bi_bulk hα c hN hB hc i hp0 hp1
  rw [← hγ, hmp] at hbulk
  rw [hbulk]
  have hV := upper_finV_pos (α := α) c hN hB hc hp0 hp1
  have hVlo := (h₃ N hN p hphalf hp1).1
  have han := upper_aN_pos (α := α) hc hN
  have h1p : 0 < 1 - p := by linarith
  have e : (γ - m) / γ = 1 - p := by rw [hp]; field_simp
  rw [e]
  set V := finV α N p with hVdef
  set y := ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg (by positivity) _
  have hfrac : V / (V + y) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hfrac0 : 0 ≤ V / (V + y) := by positivity
  have hsq : Real.sqrt ((1 - p) / (p * V)) ≤ Real.sqrt (2 / c₃) * (1 - p) := by
    rw [show Real.sqrt (2 / c₃) * (1 - p) = Real.sqrt (2 / c₃ * (1 - p) ^ 2) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq h1p.le]]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by positivity)]
    have h₄ : c₃ / (1 - p) ≤ V := hVlo
    rw [div_le_iff₀ h1p] at h₄
    have h₅ : c₃ ≤ V * (1 - p) := h₄
    have h₆ : (2 / c₃ * (1 - p) ^ 2) * (p * V) =
        2 * (1 - p) * (p * (V * (1 - p))) / c₃ := by field_simp
    rw [h₆, le_div_iff₀ hc₃]
    nlinarith [mul_pos h1p hp0, mul_nonneg h1p.le hc₃.le]
  calc
    aN α c N * Real.sqrt ((1 - p) / (p * V)) * (V / (V + y))
        ≤ aN α c N * (Real.sqrt (2 / c₃) * (1 - p)) * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hsq han.le) hfrac hfrac0 (by positivity)
    _ = _ := by ring

private lemma upper_sqrt_identity {γ m Λ μ : ℝ} (hγ : 0 < γ) (hm : 0 < m)
    (hmγ : m < γ) (hΛ : 0 < Λ) (hμ : 0 < μ) :
    Real.sqrt (μ * Λ) / (Real.sqrt m * (1 + μ * Λ)) * Real.sqrt (1 - m / γ) =
      Real.sqrt ((γ - m) / (m * Λ)) * (Λ * μ / (1 + Λ * μ)) /
        Real.sqrt (μ * γ) := by
  have hμΛ : 0 ≤ μ * Λ := (mul_pos hμ hΛ).le
  have hm0 : 0 ≤ m := hm.le
  have ht : 0 ≤ 1 - m / γ := by rw [sub_nonneg, div_le_one hγ]; exact hmγ.le
  have hd : 0 ≤ (γ - m) / (m * Λ) := by positivity
  have hμγ : 0 ≤ μ * γ := (mul_pos hμ hγ).le
  have hleft : 0 ≤ Real.sqrt (μ * Λ) / (Real.sqrt m * (1 + μ * Λ)) *
      Real.sqrt (1 - m / γ) := by positivity
  have hright : 0 ≤ Real.sqrt ((γ - m) / (m * Λ)) * (Λ * μ / (1 + Λ * μ)) /
      Real.sqrt (μ * γ) := by positivity
  have hsquare :
      (Real.sqrt (μ * Λ) / (Real.sqrt m * (1 + μ * Λ)) * Real.sqrt (1 - m / γ)) ^ 2 =
        (Real.sqrt ((γ - m) / (m * Λ)) * (Λ * μ / (1 + Λ * μ)) /
          Real.sqrt (μ * γ)) ^ 2 := by
    rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hμΛ, Real.sq_sqrt hm0,
      Real.sq_sqrt ht, div_pow, mul_pow, div_pow, Real.sq_sqrt hd,
      Real.sq_sqrt hμγ]
    field_simp
  nlinarith

private lemma upper_W_eq {α β : ℝ} {N B : ℕ} {c : ℝ} (hN : 0 < N)
    (hB : 0 < B) (hc : 0 < c) (i : Fin N) {m : ℝ}
    (hm : m ∈ Ioo 0 (gammaOf N B)) :
    Wpart β B (plSpec α c N) i m =
      partBfun B (plSpec α c N) i m /
          Real.sqrt (plSpec α c N i * gammaOf N B) *
        thetaN β B (plSpec α c N) m := by
  have hγ : 0 < gammaOf N B := hm.1.trans hm.2
  have hΛ := vk_partLam_pos hB hN (vk_pos_plSpec (α := α) hc N) hm
  have hμ := vk_pos_plSpec (α := α) hc N i
  unfold Wpart partBfun partF
  rw [upper_sqrt_identity hγ hm.1 hm.2 hΛ hμ]

private lemma upper_scalar {K s κ γ d1 d2 a1 a2 D Δ : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hκ : 0 < κ)
    (hγ : 1 ≤ γ) (hd1 : 0 < d1) (hd2 : 0 < d2)
    (ha2 : 0 ≤ a2) (hD : 0 ≤ D) (hΔ0 : 0 < Δ)
    (ha1' : a1 ≤ K * s * ((d1 + 1) / (γ * Real.sqrt γ)))
    (ha2' : a2 ≤ K * s * ((d2 + 1) / (γ * Real.sqrt γ)))
    (hΔ : κ * (max d1 d2 * max (max d1 d2) 1) ≤ γ ^ 2 * Δ) :
    a1 * a2 * D / Δ ≤
      (K ^ 2 / κ) * s ^ 2 / γ * D * (4 + 4 * (1 / (Real.sqrt d1 * Real.sqrt d2))) := by
  have hγ0 : 0 < γ := by linarith
  have hsγ : 0 < Real.sqrt γ := Real.sqrt_pos.2 hγ0
  have hsq : Real.sqrt γ * Real.sqrt γ = γ := Real.mul_self_sqrt hγ0.le
  set d := max d1 d2 with hd
  have hd0 : 0 < d := lt_max_of_lt_left hd1
  set ψ := d * max d 1 with hψ
  have hψ0 : 0 < ψ := mul_pos hd0 (lt_max_of_lt_right one_pos)
  have hs1 : 0 < Real.sqrt d1 := Real.sqrt_pos.2 hd1
  have hs2 : 0 < Real.sqrt d2 := Real.sqrt_pos.2 hd2
  have hprod : Real.sqrt d1 * Real.sqrt d2 ≤ d := by
    have h1 : Real.sqrt d1 ≤ Real.sqrt d := Real.sqrt_le_sqrt (le_max_left _ _)
    have h2 : Real.sqrt d2 ≤ Real.sqrt d := Real.sqrt_le_sqrt (le_max_right _ _)
    calc Real.sqrt d1 * Real.sqrt d2 ≤ Real.sqrt d * Real.sqrt d :=
          mul_le_mul h1 h2 hs2.le (Real.sqrt_nonneg _)
      _ = d := Real.mul_self_sqrt hd0.le
  have hkey : (d1 + 1) * (d2 + 1) ≤ ψ * (4 + 4 * (1 / (Real.sqrt d1 * Real.sqrt d2))) := by
    have hle : (d1 + 1) * (d2 + 1) ≤ (d + 1) ^ 2 := by
      have h1 : d1 + 1 ≤ d + 1 := by linarith [le_max_left d1 d2]
      have h2 : d2 + 1 ≤ d + 1 := by linarith [le_max_right d1 d2]
      nlinarith [mul_le_mul h1 h2 (by linarith) (by linarith)]
    have hinv : 1 / d ≤ 1 / (Real.sqrt d1 * Real.sqrt d2) :=
      one_div_le_one_div_of_le (mul_pos hs1 hs2) hprod
    have hcase : (d + 1) ^ 2 ≤ ψ * (4 + 4 * (1 / d)) := by
      rcases le_total d 1 with h | h
      · have : ψ = d := by rw [hψ, max_eq_right h, mul_one]
        rw [this]
        have : d * (4 + 4 * (1 / d)) = 4 * d + 4 := by field_simp
        rw [this]; nlinarith
      · have : ψ = d * d := by rw [hψ, max_eq_left h]
        rw [this]
        have : d * d * (4 + 4 * (1 / d)) = 4 * d * d + 4 * d := by field_simp
        rw [this]; nlinarith
    calc (d1 + 1) * (d2 + 1) ≤ (d + 1) ^ 2 := hle
      _ ≤ ψ * (4 + 4 * (1 / d)) := hcase
      _ ≤ ψ * (4 + 4 * (1 / (Real.sqrt d1 * Real.sqrt d2))) := by
          apply mul_le_mul_of_nonneg_left _ hψ0.le
          linarith
  have hΔψ : κ * ψ ≤ γ ^ 2 * Δ := hΔ
  have hnum : a1 * a2 ≤ K ^ 2 * s ^ 2 * ((d1 + 1) * (d2 + 1)) / (γ ^ 3) := by
    have := mul_le_mul ha1' ha2' ha2 (by positivity)
    calc a1 * a2 ≤ K * s * ((d1 + 1) / (γ * Real.sqrt γ)) * (K * s * ((d2 + 1) / (γ * Real.sqrt γ))) := this
      _ = K ^ 2 * s ^ 2 * ((d1 + 1) * (d2 + 1)) / (γ ^ 3) := by
        have : (γ * Real.sqrt γ) * (γ * Real.sqrt γ) = γ ^ 3 := by
          calc (γ * Real.sqrt γ) * (γ * Real.sqrt γ) = γ * γ * (Real.sqrt γ * Real.sqrt γ) := by ring
            _ = γ ^ 3 := by rw [hsq]; ring
        field_simp
        rw [Real.sq_sqrt hγ0.le]
  rw [div_le_iff₀ hΔ0]
  have hX : 0 ≤ (K ^ 2 / κ) * s ^ 2 / γ * D := by positivity
  calc a1 * a2 * D ≤ K ^ 2 * s ^ 2 * ((d1 + 1) * (d2 + 1)) / (γ ^ 3) * D :=
        mul_le_mul_of_nonneg_right hnum hD
    _ ≤ K ^ 2 * s ^ 2 * (ψ * (4 + 4 * (1 / (Real.sqrt d1 * Real.sqrt d2)))) / (γ ^ 3) * D := by
        gcongr
    _ = (K ^ 2 / κ) * s ^ 2 / γ * D * (4 + 4 * (1 / (Real.sqrt d1 * Real.sqrt d2))) * (κ * ψ / γ ^ 2) := by
        field_simp
    _ ≤ (K ^ 2 / κ) * s ^ 2 / γ * D * (4 + 4 * (1 / (Real.sqrt d1 * Real.sqrt d2))) * Δ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_iff₀ (by positivity)]; linarith

private lemma upper_int_u {a b : ℝ} (hab : a < b) :
    IntegrableOn (fun m : ℝ => 1 / Real.sqrt (b - m)) (Ico a b) ∧
      ∫ m in Ico a b, 1 / Real.sqrt (b - m) = 2 * Real.sqrt (b - a) := by
  have hfun : ∀ m : ℝ, m ≤ b → 1 / Real.sqrt (b - m) = (b - m) ^ (-(1/2 : ℝ)) := by
    intro m hm
    rw [Real.sqrt_eq_rpow, Real.rpow_neg (by linarith), one_div]
  have hii : IntervalIntegrable (fun x : ℝ => x ^ (-(1/2 : ℝ))) volume 0 (b - a) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h2 := (hii.comp_sub_left b).symm
  simp only [sub_zero, sub_sub_cancel] at h2
  have h4' : IntegrableOn (fun m : ℝ => (b - m) ^ (-(1/2 : ℝ))) (Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).1 h2
  have h4 : IntegrableOn (fun m : ℝ => 1 / Real.sqrt (b - m)) (Ioc a b) :=
    h4'.congr_fun (fun m hm => (hfun m hm.2).symm) measurableSet_Ioc
  have h5 : IntegrableOn (fun m : ℝ => 1 / Real.sqrt (b - m)) (Ico a b) := by
    have := (integrableOn_Ico_iff_integrableOn_Ioo (f := fun m : ℝ => 1 / Real.sqrt (b - m)) (a := a) (b := b)
      (by simp)).2 ((integrableOn_Ioc_iff_integrableOn_Ioo (f := fun m : ℝ => 1 / Real.sqrt (b - m)) (a := a) (b := b)).1 h4)
    exact this
  refine ⟨h5, ?_⟩
  rw [integral_Ico_eq_integral_Ioc]
  rw [setIntegral_congr_fun measurableSet_Ioc (fun m hm => hfun m hm.2)]
  rw [← intervalIntegral.integral_of_le hab.le]
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-(1/2 : ℝ))) b]
  rw [integral_rpow (Or.inl (by norm_num))]
  simp only [sub_self]
  have h0 : (0 : ℝ) ^ (-(1/2 : ℝ) + 1) = 0 := Real.zero_rpow (by norm_num)
  rw [h0]
  have : (b - a) ^ (-(1/2 : ℝ) + 1) = Real.sqrt (b - a) := by
    rw [Real.sqrt_eq_rpow]; norm_num
  rw [this]
  ring

private lemma upper_sum_sqrt (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, 1 / Real.sqrt (j : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    set a := Real.sqrt ((n + 1 : ℕ) : ℝ) with ha
    set b := Real.sqrt (n : ℝ) with hb
    have ha2 : a ^ 2 = (n : ℝ) + 1 := by rw [ha, Real.sq_sqrt (by positivity)]; push_cast; ring
    have hb2 : b ^ 2 = (n : ℝ) := Real.sq_sqrt hn
    have ha0 : 0 < a := Real.sqrt_pos.2 (by positivity)
    have hb0 : 0 ≤ b := Real.sqrt_nonneg _
    have : 1 / a ≤ 2 * a - 2 * b := by
      rw [div_le_iff₀ ha0]
      nlinarith [sq_nonneg (a - b)]
    linarith

private lemma upper_term_le {x a s : ℝ} (hx : 0 < x) (ha : 0 < a) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    x / (x + a) ≤ (x / a) ^ s := by
  have hu : 0 < x / a := div_pos hx ha
  set u := x / a with hu_def
  have e : x / (x + a) = u / (1 + u) := by rw [hu_def]; field_simp; ring
  rw [e]
  rcases le_total u 1 with h | h
  · calc u / (1 + u) ≤ u := by rw [div_le_iff₀ (by linarith)]; nlinarith
      _ = u ^ (1 : ℝ) := (Real.rpow_one u).symm
      _ ≤ u ^ s := Real.rpow_le_rpow_of_exponent_ge hu h hs1
  · calc u / (1 + u) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      _ ≤ u ^ s := Real.one_le_rpow h hs0.le

private lemma upper_finS_le {α : ℝ} (hα : 0 < α) {N : ℕ} (hN : 0 < N) {x : ℝ} (hx : 0 < x) :
    finS α N x ≤ 2 * x ^ (min 1 (1 / (2 * α))) := by
  set s := min 1 (1 / (2 * α)) with hs
  have hs0 : 0 < s := lt_min one_pos (by positivity)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hαs : α * s ≤ 1 / 2 := by
    have : s ≤ 1 / (2 * α) := min_le_right _ _
    calc α * s ≤ α * (1 / (2 * α)) := mul_le_mul_of_nonneg_left this hα.le
      _ = 1 / 2 := by field_simp
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold finS
  have hterm : ∀ j ∈ Finset.Icc 1 N, x / (x + ((j : ℝ) / (N : ℝ)) ^ α) ≤
      x ^ s * (Real.sqrt (N : ℝ) * (1 / Real.sqrt (j : ℝ))) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
    have hjN : j ≤ N := (Finset.mem_Icc.1 hj).2
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    have hja : 0 < ((j : ℝ) / (N : ℝ)) ^ α := Real.rpow_pos_of_pos (div_pos hj0 hNr) α
    refine (upper_term_le hx hja hs0 hs1).trans ?_
    rw [Real.div_rpow hx.le hja.le]
    have h1 : (((j : ℝ) / (N : ℝ)) ^ α) ^ s = ((j : ℝ) / (N : ℝ)) ^ (α * s) := by
      rw [← Real.rpow_mul (div_pos hj0 hNr).le]
    rw [h1]
    have hge : 1 ≤ (N : ℝ) / (j : ℝ) := by
      rw [le_div_iff₀ hj0, one_mul]; exact_mod_cast hjN
    have h2 : (((j : ℝ) / (N : ℝ)) ^ (α * s))⁻¹ ≤ Real.sqrt (N : ℝ) * (1 / Real.sqrt (j : ℝ)) := by
      have e : (((j : ℝ) / (N : ℝ)) ^ (α * s))⁻¹ = ((N : ℝ) / (j : ℝ)) ^ (α * s) := by
        rw [← Real.inv_rpow (div_pos hj0 hNr).le, inv_div]
      rw [e]
      calc ((N : ℝ) / (j : ℝ)) ^ (α * s) ≤ ((N : ℝ) / (j : ℝ)) ^ ((1 : ℝ) / 2) :=
            Real.rpow_le_rpow_of_exponent_le hge hαs
        _ = Real.sqrt (N : ℝ) * (1 / Real.sqrt (j : ℝ)) := by
            rw [← Real.sqrt_eq_rpow, Real.sqrt_div hNr.le]; ring
    calc x ^ s / ((j : ℝ) / (N : ℝ)) ^ (α * s) = x ^ s * (((j : ℝ) / (N : ℝ)) ^ (α * s))⁻¹ := by
          rw [div_eq_mul_inv]
      _ ≤ x ^ s * (Real.sqrt (N : ℝ) * (1 / Real.sqrt (j : ℝ))) :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hx.le _)
  calc (N : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 N, x / (x + ((j : ℝ) / (N : ℝ)) ^ α)
      ≤ (N : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 N, x ^ s * (Real.sqrt (N : ℝ) * (1 / Real.sqrt (j : ℝ))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (inv_nonneg.2 hNr.le)
    _ = (N : ℝ)⁻¹ * (x ^ s * Real.sqrt (N : ℝ) * ∑ j ∈ Finset.Icc 1 N, 1 / Real.sqrt (j : ℝ)) := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
    _ ≤ (N : ℝ)⁻¹ * (x ^ s * Real.sqrt (N : ℝ) * (2 * Real.sqrt (N : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 hNr.le)
        exact mul_le_mul_of_nonneg_left (upper_sum_sqrt N) (by positivity)
    _ = 2 * x ^ s := by
        have : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = N := Real.mul_self_sqrt hNr.le
        field_simp
        nlinarith [this]

private lemma upper_W_alg {t m γ θ y cη η Cθ : ℝ} (hγ1 : 1 ≤ γ) (hηm : η * γ ≤ m) (hmγ : m < γ)
    (hη : 0 < η) (hcη : 0 < cη) (hy : 0 < y) (ht0 : 0 < t)
    (ht : cη / ((1 - m / γ) * y) ≤ t) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ Cθ * (1 + 1 / m + 1 / (γ - m))) (hCθ : 0 ≤ Cθ) :
    Real.sqrt t / (Real.sqrt m * (1 + t)) * Real.sqrt (1 - m / γ) * θ ≤
      Cθ * (1 + 1 / η) / Real.sqrt (η * cη) * Real.sqrt y *
        ((γ - m + 1) / (γ * Real.sqrt γ)) := by
  have hγ0 : 0 < γ := by linarith
  have hm0 : 0 < m := lt_of_lt_of_le (mul_pos hη hγ0) hηm
  have hd0 : 0 < γ - m := by linarith
  set d := γ - m with hd
  set q := 1 - m / γ with hq
  have hqd : q = d / γ := by rw [hq, hd]; field_simp
  have hq0 : 0 < q := by rw [hqd]; positivity
  have hsγ : 0 < Real.sqrt γ := Real.sqrt_pos.2 hγ0
  have hsηc : 0 < Real.sqrt (η * cη) := Real.sqrt_pos.2 (by positivity)
  have hLHS0 : 0 ≤ Real.sqrt t / (Real.sqrt m * (1 + t)) * Real.sqrt q * θ := by positivity
  have hRHS0 : 0 ≤ Cθ * (1 + 1 / η) / Real.sqrt (η * cη) * Real.sqrt y *
        ((d + 1) / (γ * Real.sqrt γ)) := by positivity
  rw [← abs_of_nonneg hLHS0, ← abs_of_nonneg hRHS0]
  apply sq_le_sq.1
  -- squares
  have hL2 : (Real.sqrt t / (Real.sqrt m * (1 + t)) * Real.sqrt q * θ) ^ 2 =
      t / (m * (1 + t) ^ 2) * q * θ ^ 2 := by
    rw [mul_pow, mul_pow, div_pow, mul_pow, Real.sq_sqrt ht0.le, Real.sq_sqrt hm0.le,
      Real.sq_sqrt hq0.le]
  have hR2 : (Cθ * (1 + 1 / η) / Real.sqrt (η * cη) * Real.sqrt y *
        ((d + 1) / (γ * Real.sqrt γ))) ^ 2 =
      Cθ ^ 2 * (1 + 1 / η) ^ 2 / (η * cη) * y * ((d + 1) ^ 2 / (γ ^ 2 * γ)) := by
    have h1 : Real.sqrt (η * cη) ^ 2 = η * cη := Real.sq_sqrt (by positivity)
    have h2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
    have h3 : Real.sqrt γ ^ 2 = γ := Real.sq_sqrt hγ0.le
    simp only [mul_pow, div_pow, h1, h2, h3]
  rw [hL2, hR2]
  -- 1/t bound
  have hinv : 1 / t ≤ q * y / cη := by
    have : cη / (q * y) ≤ t := ht
    rw [div_le_iff₀ (by positivity)] at this
    rw [div_le_div_iff₀ ht0 hcη]
    nlinarith
  have hfrac : t / (1 + t) ^ 2 ≤ 1 / t := by
    rw [div_le_div_iff₀ (by positivity) ht0]
    nlinarith [sq_nonneg t]
  -- qθ bound
  have hm_eta : η ≤ m := by nlinarith
  have hqθ : q * θ ≤ Cθ * (1 + 1 / η) * ((d + 1) / γ) := by
    have h1 : q * θ ≤ q * (Cθ * (1 + 1 / m + 1 / d)) := mul_le_mul_of_nonneg_left hθ hq0.le
    have h2 : 1 / m ≤ 1 / η := one_div_le_one_div_of_le hη hm_eta
    have h3 : q * (Cθ * (1 + 1 / m + 1 / d)) = Cθ * (d / γ + d / γ * (1 / m) + 1 / γ) := by
      rw [hqd]; field_simp
    have h4 : d / γ * (1 / m) ≤ d / γ * (1 / η) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    calc q * θ ≤ Cθ * (d / γ + d / γ * (1 / m) + 1 / γ) := h1.trans (le_of_eq h3)
      _ ≤ Cθ * (d / γ + d / γ * (1 / η) + 1 / γ) := by
          apply mul_le_mul_of_nonneg_left _ hCθ
          linarith
      _ ≤ Cθ * (1 + 1 / η) * ((d + 1) / γ) := by
          have : d / γ + d / γ * (1 / η) + 1 / γ ≤ (1 + 1 / η) * ((d + 1) / γ) := by
            have e : (1 + 1 / η) * ((d + 1) / γ) = d / γ + d / γ * (1 / η) + 1 / γ + 1 / γ * (1 / η) := by
              field_simp; ring
            rw [e]
            have : 0 ≤ 1 / γ * (1 / η) := by positivity
            linarith
          calc Cθ * (d / γ + d / γ * (1 / η) + 1 / γ) ≤ Cθ * ((1 + 1 / η) * ((d + 1) / γ)) :=
                mul_le_mul_of_nonneg_left this hCθ
            _ = _ := by ring
  have hqθ2 : (q * θ) ^ 2 ≤ (Cθ * (1 + 1 / η) * ((d + 1) / γ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hqθ 2
  -- chain
  have hA : t / (m * (1 + t) ^ 2) * q * θ ^ 2 ≤ (q * y / cη) * (q * θ ^ 2) / m := by
    have e : t / (m * (1 + t) ^ 2) * q * θ ^ 2 = (t / (1 + t) ^ 2) * (q * θ ^ 2) / m := by
      field_simp
    rw [e]
    have : (t / (1 + t) ^ 2) * (q * θ ^ 2) ≤ (q * y / cη) * (q * θ ^ 2) :=
      mul_le_mul_of_nonneg_right (hfrac.trans hinv) (by positivity)
    exact div_le_div_of_nonneg_right this hm0.le
  have hB : (q * y / cη) * (q * θ ^ 2) / m = y / (cη * m) * (q * θ) ^ 2 := by
    field_simp
  have hC : y / (cη * m) * (q * θ) ^ 2 ≤
      y / (cη * (η * γ)) * (Cθ * (1 + 1 / η) * ((d + 1) / γ)) ^ 2 := by
    apply mul_le_mul _ hqθ2 (sq_nonneg _) (by positivity)
    apply div_le_div_of_nonneg_left hy.le (by positivity)
    exact mul_le_mul_of_nonneg_left hηm hcη.le
  have hD : y / (cη * (η * γ)) * (Cθ * (1 + 1 / η) * ((d + 1) / γ)) ^ 2 =
      Cθ ^ 2 * (1 + 1 / η) ^ 2 / (η * cη) * y * ((d + 1) ^ 2 / (γ ^ 2 * γ)) := by
    field_simp
  linarith [hA, hB.le, hC, hD.le]

private lemma upper_x_low {α η : ℝ} (hα : 0 < α) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ cη : ℝ, 0 < cη ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → ∀ p : ℝ, η ≤ p → p < 1 →
      cη / (1 - p) ≤ finV α N p := by
  obtain ⟨c₃, C₃, hc₃, hC₃, h₃⟩ := lem_app_pl_finite_inverse_iii hα
  set s := min 1 (1 / (2 * α)) with hs
  have hs0 : 0 < s := lt_min one_pos (by positivity)
  set v0 : ℝ := (η / 2) ^ (1 / s) with hv0
  have hv0pos : 0 < v0 := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨min c₃ (v0 / 2), lt_min hc₃ (by positivity), ?_⟩
  intro N B c hN hB hc p hηp hp1
  have hp0 : 0 < p := lt_of_lt_of_le hη0 hηp
  have h1p : 0 < 1 - p := by linarith
  rcases le_total (1 / 2) p with hp | hp
  · exact (div_le_div_of_nonneg_right (min_le_left _ _) h1p.le).trans (h₃ N hN p hp hp1).1
  · have hVpos := upper_finV_pos (α := α) c hN hB hc hp0 hp1
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hBr : (0 : ℝ) < B := by exact_mod_cast hB
    have hγ : 0 < gammaOf N B := by unfold gammaOf; exact div_pos hNr hBr
    have hpos := vk_pos_plSpec (α := α) hc N
    have hm : gammaOf N B * p ∈ Ioo 0 (gammaOf N B) := ⟨mul_pos hγ hp0, by nlinarith⟩
    have hΛ := vk_partLam_pos hB hN hpos hm
    have hLV := eqn_app_pl_Lambda_V (N := N) (B := B) α c hN hB hc hm
    rw [mul_div_cancel_left₀ p hγ.ne'] at hLV
    have hSN := eqn_app_pl_SN_mN (N := N) (B := B) α c hN hB hc hΛ
    rw [vk_partMN_partLam hB hN hpos hm] at hSN
    have hxV : c * partLam B (plSpec α c N) (gammaOf N B * p) * (N : ℝ) ^ (-α) = finV α N p := by
      rw [hLV, Real.rpow_neg hNr.le]
      have : (N : ℝ) ^ α ≠ 0 := (Real.rpow_pos_of_pos hNr α).ne'
      field_simp
    rw [hxV] at hSN
    have hfin : finS α N (finV α N p) = p := by
      have : gammaOf N B * p = gammaOf N B * finS α N (finV α N p) := hSN
      exact (mul_left_cancel₀ hγ.ne' this).symm
    have hle := upper_finS_le hα hN hVpos
    rw [hfin] at hle
    have hVs : η / 2 ≤ (finV α N p) ^ s := by linarith
    have hV : v0 ≤ finV α N p := by
      by_contra hcon
      push_neg at hcon
      have h := Real.rpow_lt_rpow hVpos.le hcon hs0
      rw [hv0, ← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hs0.ne',
        Real.rpow_one] at h
      linarith
    calc min c₃ (v0 / 2) / (1 - p) ≤ (v0 / 2) / (1 - p) :=
          div_le_div_of_nonneg_right (min_le_right _ _) h1p.le
      _ ≤ v0 := by rw [div_le_iff₀ h1p]; nlinarith
      _ ≤ _ := hV

/-- Wpart bound for `m ∈ [ηγ, γ)`. -/
private lemma upper_W_bound {α β η : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → 1 ≤ gammaOf N B →
      ∀ (i : Fin N) (m : ℝ), η * gammaOf N B ≤ m → m < gammaOf N B →
        Wpart β B (plSpec α c N) i m ≤
          K * Real.sqrt (((((i : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α) *
            ((gammaOf N B - m + 1) / (gammaOf N B * Real.sqrt (gammaOf N B))) := by
  obtain ⟨cη, hcη, hx⟩ := upper_x_low hα hη0 hη1
  obtain ⟨Cθ, hθC⟩ := lem_app_pl_elasticity_ii hα hβ0 hβ1
  obtain ⟨cE, CE, hcE, -, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  refine ⟨max Cθ 0 * (1 + 1 / η) / Real.sqrt (η * cη), by positivity, ?_⟩
  intro N B c hN hB hc hγ1 i m hηm hmγ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hγ0 : 0 < gammaOf N B := by linarith
  have hm0 : 0 < m := lt_of_lt_of_le (mul_pos hη0 hγ0) hηm
  have hmI : m ∈ Ioo 0 (gammaOf N B) := ⟨hm0, hmγ⟩
  have hpos := vk_pos_plSpec (α := α) hc N
  have hΛ := vk_partLam_pos hB hN hpos hmI
  have hp0 : 0 < m / gammaOf N B := div_pos hm0 hγ0
  have hp1 : m / gammaOf N B < 1 := (div_lt_one hγ0).2 hmγ
  have hηp : η ≤ m / gammaOf N B := by rw [le_div_iff₀ hγ0]; exact hηm
  have hLV := eqn_app_pl_Lambda_V (N := N) (B := B) α c hN hB hc hmI
  have hy : 0 < ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α :=
    Real.rpow_pos_of_pos (by positivity) α
  have ht : plSpec α c N i * partLam B (plSpec α c N) m =
      finV α N (m / gammaOf N B) / ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α := by
    have hj : (0 : ℝ) < ((i : ℕ) : ℝ) + 1 := by positivity
    have hja : 0 < (((i : ℕ) : ℝ) + 1) ^ α := Real.rpow_pos_of_pos hj α
    have hNa : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hNr α
    have hμ : plSpec α c N i = c * (((i : ℕ) : ℝ) + 1) ^ (-α) := rfl
    rw [hμ, hLV, Real.div_rpow hj.le hNr.le, Real.rpow_neg hj.le]
    field_simp
  have hV := hx N B c hN hB hc _ hηp hp1
  have ht0 : 0 < plSpec α c N i * partLam B (plSpec α c N) m := mul_pos (hpos i) hΛ
  have htlow : cη / ((1 - m / gammaOf N B) * ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α) ≤
      plSpec α c N i * partLam B (plSpec α c N) m := by
    rw [ht, ← div_div]
    exact div_le_div_of_nonneg_right hV hy.le
  obtain ⟨hθ1, hθ2⟩ := hθC N B c hN hB hc m hmI
  have hEp : 0 < Efun β m :=
    lt_of_lt_of_le (mul_pos hcE (lt_min hm0 one_pos)) (hE m hm0).1
  have hθ0 : 0 ≤ thetaN β B (plSpec α c N) m := by nlinarith
  have hθ' : thetaN β B (plSpec α c N) m ≤
      max Cθ 0 * (1 + 1 / m + 1 / (gammaOf N B - m)) := by
    refine hθ1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    have : 0 < gammaOf N B - m := by linarith
    positivity
  unfold Wpart
  exact upper_W_alg hγ1 hηm hmγ hη0 hcη hy ht0 htlow hθ0 hθ' (le_max_right _ _)

private lemma upper_alg_large {cα γ lo hi T Δ : ℝ} (hcα : 0 < cα) (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hhi : hi < γ) (hT0 : 0 ≤ T) (hT1 : T ≤ lo)
    (hch : cα * ((1 - lo / γ) * (1 - hi / γ)) ≤ (1 - lo / γ) * (1 - T / hi))
    (hΔ : (1 - lo / γ) * (1 - T / hi) ≤ Δ) :
    min (cα / 2) (1 / 2) * (γ - lo) ^ 2 ≤ γ ^ 2 * Δ := by
  have hhi0 : 0 < hi := lt_of_lt_of_le hlo hlohi
  have hγ : 0 < γ := lt_trans hhi0 hhi
  set a := 1 - lo / γ with ha
  set b := 1 - hi / γ with hb
  have hae : γ - lo = γ * a := by rw [ha]; field_simp
  have ha0 : 0 < a := by rw [ha, sub_pos, div_lt_one hγ]; linarith
  have hb0 : 0 < b := by rw [hb, sub_pos, div_lt_one hγ]; exact hhi
  have hκ1 : min (cα / 2) (1 / 2) ≤ cα / 2 := min_le_left _ _
  have hκ2 : min (cα / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hΔa : min (cα / 2) (1 / 2) * a ^ 2 ≤ Δ := by
    rcases le_or_gt (a / 2) b with h | h
    · -- Δ ≥ cα a b ≥ cα a² / 2
      have : cα / 2 * a ^ 2 ≤ cα * (a * b) := by nlinarith [mul_pos hcα ha0]
      calc min (cα / 2) (1 / 2) * a ^ 2 ≤ cα / 2 * a ^ 2 :=
            mul_le_mul_of_nonneg_right hκ1 (sq_nonneg _)
        _ ≤ cα * (a * b) := this
        _ ≤ a * (1 - T / hi) := by linarith
        _ ≤ Δ := hΔ
    · have hdiff : γ * a / 2 < hi - lo := by
        have : hi - lo = γ * (a - b) := by rw [ha, hb]; field_simp; ring
        rw [this]; nlinarith
      have hT : T / hi ≤ lo / hi := div_le_div_of_nonneg_right hT1 hhi0.le
      have h1 : a / 2 ≤ 1 - T / hi := by
        have : 1 - lo / hi = (hi - lo) / hi := by field_simp
        have h2 : a / 2 ≤ (hi - lo) / hi := by
          rw [le_div_iff₀ hhi0]
          nlinarith
        linarith
      calc min (cα / 2) (1 / 2) * a ^ 2 ≤ 1 / 2 * a ^ 2 :=
            mul_le_mul_of_nonneg_right hκ2 (sq_nonneg _)
        _ ≤ a * (1 - T / hi) := by nlinarith
        _ ≤ Δ := hΔ
  calc min (cα / 2) (1 / 2) * (γ - lo) ^ 2 = γ ^ 2 * (min (cα / 2) (1 / 2) * a ^ 2) := by
        rw [hae]; ring
    _ ≤ γ ^ 2 * Δ := mul_le_mul_of_nonneg_left hΔa (sq_nonneg _)

/-- Large-deficit determinant bound. -/
private lemma upper_det_large {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → ∀ (ℓ : ℤ) (m₁ m₂ : ℝ),
      m₁ ∈ Ioo 0 (gammaOf N B) → m₂ ∈ Ioo 0 (gammaOf N B) →
        κ * (gammaOf N B - min m₁ m₂) ^ 2 ≤
          gammaOf N B ^ 2 * deltaN β B (plSpec α c N) ℓ m₁ m₂ := by
  obtain ⟨cα, hcα, hchain⟩ := lem_app_pl_determinant_ii_chain hα
  refine ⟨min (cα / 2) (1 / 2), lt_min (by positivity) (by norm_num), ?_⟩
  intro N B c hN hB hc ℓ m₁ m₂ hm₁ hm₂
  have hpos := vk_pos_plSpec (α := α) hc N
  have h2 := lem_app_pl_determinant_ii hα hβ0 hβ1 N B c hN hB hc ℓ m₁ m₂ hm₁ hm₂
  have h3 := hchain N B c hN hB hc m₁ m₂ hm₁ hm₂
  rcases le_total m₁ m₂ with h | h
  · rw [min_eq_left h, max_eq_right h] at h2 h3
    rw [min_eq_left h]
    obtain ⟨hT0, hT1⟩ := vk_T_bd hB hN hpos hm₁ hm₂ h
    exact upper_alg_large hcα hm₁.1 h hm₂.2 hT0 hT1 h3 h2
  · rw [min_eq_right h, max_eq_left h] at h2 h3
    rw [min_eq_right h]
    obtain ⟨hT0, hT1⟩ := vk_T_bd hB hN hpos hm₂ hm₁ h
    rw [vk_TN_comm] at h2 h3
    rw [mul_comm (1 - m₁ / gammaOf N B)] at h3
    exact upper_alg_large hcα hm₂.1 h hm₁.2 hT0 hT1 h3 h2

private lemma upper_pow_sum {α : ℝ} (hα : 0 < α) (N : ℕ) :
    (N : ℝ) ^ (α + 1) / (α + 1) ≤ ∑ i ∈ Finset.range N, (((i : ℝ) + 1)) ^ α := by
  have hmono : MonotoneOn (fun x : ℝ => x ^ α) (Icc (0 : ℝ) (0 + N)) := by
    intro a ha b hb hab
    exact Real.rpow_le_rpow ha.1 hab hα.le
  have h := hmono.integral_le_sum
  have hint : ∫ x in (0 : ℝ)..(0 + N), x ^ α = (N : ℝ) ^ (α + 1) / (α + 1) := by
    rw [zero_add, integral_rpow (Or.inl (by linarith))]
    rw [Real.zero_rpow (by linarith)]; simp
  rw [hint] at h
  refine h.trans (le_of_eq ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  push_cast; ring_nf

private lemma upper_sum_t {α : ℝ} (hα : 0 < α) {N : ℕ} (hN : 0 < N) :
    (N : ℝ) / (α + 1) ≤ ∑ j : Fin N, ((((j : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := upper_pow_sum hα N
  have h2 : ∑ j : Fin N, ((((j : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α =
      ((N : ℝ) ^ α)⁻¹ * ∑ i ∈ Finset.range N, (((i : ℝ) + 1)) ^ α := by
    rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range (fun i : ℕ => ((N : ℝ) ^ α)⁻¹ * ((i : ℝ) + 1) ^ α) N]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Real.div_rpow (by positivity) hNr.le, div_eq_inv_mul]
  rw [h2]
  have hNa : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hNr α
  have h3 : (N : ℝ) / (α + 1) = ((N : ℝ) ^ α)⁻¹ * ((N : ℝ) ^ (α + 1) / (α + 1)) := by
    rw [Real.rpow_add hNr, Real.rpow_one]
    field_simp
  rw [h3]
  exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hNa.le)

private lemma upper_max_le_avg {α : ℝ} (hα : 0 < α) {N : ℕ} (hN : 0 < N) {P : ℝ} (hP : 0 < P)
    (i : Fin N) :
    ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α / (((((i : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α + P) ≤
      (α + 1) / (N : ℝ) * ∑ j : Fin N, ((((j : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α /
        (((((j : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α + P) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ht0 : ∀ j : Fin N, 0 < ((((j : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α := fun j =>
    Real.rpow_pos_of_pos (by positivity) α
  have ht1 : ∀ j : Fin N, ((((j : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α ≤ 1 := fun j => by
    apply Real.rpow_le_one (by positivity) _ hα.le
    rw [div_le_one hNr]
    have : (j : ℕ) + 1 ≤ N := j.isLt
    exact_mod_cast this
  have hgi : ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α /
      (((((i : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α + P) ≤ 1 / (1 + P) := by
    rw [div_le_div_iff₀ (by linarith [ht0 i]) (by linarith)]
    nlinarith [ht1 i]
  have hgj : ∀ j : Fin N, ((((j : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α / (1 + P) ≤
      ((((j : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α /
        (((((j : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α + P) := fun j => by
    apply div_le_div_of_nonneg_left (ht0 j).le (by linarith [ht0 j]) (by linarith [ht1 j])
  have hsum : (N : ℝ) / (α + 1) / (1 + P) ≤ ∑ j : Fin N, ((((j : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α /
        (((((j : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α + P) := by
    calc (N : ℝ) / (α + 1) / (1 + P)
        ≤ (∑ j : Fin N, ((((j : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α) / (1 + P) :=
          div_le_div_of_nonneg_right (upper_sum_t hα hN) (by linarith)
      _ = ∑ j : Fin N, ((((j : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α / (1 + P) := by rw [Finset.sum_div]
      _ ≤ _ := Finset.sum_le_sum (fun j _ => hgj j)
  have : 1 / (1 + P) ≤ (α + 1) / (N : ℝ) * ((N : ℝ) / (α + 1) / (1 + P)) := by
    have : (α + 1) / (N : ℝ) * ((N : ℝ) / (α + 1) / (1 + P)) = 1 / (1 + P) := by
      field_simp
    rw [this]
  calc _ ≤ 1 / (1 + P) := hgi
    _ ≤ _ := this
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

private lemma upper_sum_g {α : ℝ} {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B) (hc : 0 < c)
    {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    ∑ j : Fin N, (1 - partF B (plSpec α c N) j m) = (B : ℝ) * (gammaOf N B - m) := by
  have hpos := vk_pos_plSpec (α := α) hc N
  have h1 : (B : ℝ)⁻¹ * ∑ j : Fin N, partF B (plSpec α c N) j m = m := by
    have := vk_partMN_partLam hB hN hpos hm
    unfold partMN at this
    unfold partF
    exact this
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have h2 : ∑ j : Fin N, partF B (plSpec α c N) j m = B * m := by
    calc ∑ j : Fin N, partF B (plSpec α c N) j m
        = (B : ℝ) * ((B : ℝ)⁻¹ * ∑ j : Fin N, partF B (plSpec α c N) j m) := by
          rw [← mul_assoc, mul_inv_cancel₀ hBr.ne', one_mul]
      _ = B * m := by rw [h1]
  rw [Finset.sum_sub_distrib, h2]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  unfold gammaOf
  field_simp

private lemma upper_one_minus_f {α : ℝ} (hα : 0 < α) {N B : ℕ} {c : ℝ} (hN : 0 < N)
    (hB : 0 < B) (hc : 0 < c) (i : Fin N) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    1 - partF B (plSpec α c N) i m ≤ (α + 1) * (gammaOf N B - m) / gammaOf N B := by
  have hpos := vk_pos_plSpec (α := α) hc N
  have hΛ := vk_partLam_pos hB hN hpos hm
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hNa : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hNr α
  set Λ := partLam B (plSpec α c N) m with hΛdef
  set P : ℝ := Λ * c * ((N : ℝ) ^ α)⁻¹ with hPdef
  have hP : 0 < P := by positivity
  have key : ∀ j : Fin N, 1 - partF B (plSpec α c N) j m =
      ((((j : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α / (((((j : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α + P) := by
    intro j
    have hj : (0 : ℝ) < ((j : ℕ) : ℝ) + 1 := by positivity
    have hja : 0 < (((j : ℕ) : ℝ) + 1) ^ α := Real.rpow_pos_of_pos hj α
    have hμ : plSpec α c N j = c * (((j : ℕ) : ℝ) + 1) ^ (-α) := rfl
    unfold partF
    rw [← hΛdef, hμ, Real.div_rpow hj.le hNr.le, Real.rpow_neg hj.le, hPdef]
    field_simp
    ring
  have hsum : ∑ j : Fin N, ((((j : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α /
      (((((j : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α + P) = (B : ℝ) * (gammaOf N B - m) := by
    rw [← upper_sum_g (α := α) hN hB hc hm]
    exact Finset.sum_congr rfl (fun j _ => (key j).symm)
  rw [key i]
  refine (upper_max_le_avg hα hN hP i).trans (le_of_eq ?_)
  rw [hsum]
  unfold gammaOf
  field_simp

private lemma upper_T_le {α : ℝ} (hα : 0 < α) {N B : ℕ} {c : ℝ} (hN : 0 < N)
    (hB : 0 < B) (hc : 0 < c) {m₁ m₂ : ℝ} (hm₁ : m₁ ∈ Ioo 0 (gammaOf N B))
    (hm₂ : m₂ ∈ Ioo 0 (gammaOf N B)) :
    TNpart B (plSpec α c N) m₁ m₂ ≤
      m₁ + m₂ - gammaOf N B + (α + 1) * ((gammaOf N B - m₁) * (gammaOf N B - m₂)) / gammaOf N B := by
  have hpos := vk_pos_plSpec (α := α) hc N
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hγ : 0 < gammaOf N B := lt_trans hm₁.1 hm₁.2
  set K : ℝ := (α + 1) * (gammaOf N B - m₁) / gammaOf N B with hK
  have hg0 : ∀ j : Fin N, 0 ≤ 1 - partF B (plSpec α c N) j m₂ := fun j => by
    unfold partF
    have := vk_sat_le_one (vk_partLam_pos hB hN hpos hm₂).le (hpos j).le
    linarith
  have hpt : ∀ j : Fin N, partF B (plSpec α c N) j m₁ * partF B (plSpec α c N) j m₂ ≤
      1 - (1 - partF B (plSpec α c N) j m₁) - (1 - partF B (plSpec α c N) j m₂) +
        K * (1 - partF B (plSpec α c N) j m₂) := fun j => by
    have h1 := upper_one_minus_f hα hN hB hc j hm₁
    have h2 := mul_le_mul_of_nonneg_right h1 (hg0 j)
    nlinarith [h2]
  have hs1 := upper_sum_g (α := α) hN hB hc hm₁
  have hs2 := upper_sum_g (α := α) hN hB hc hm₂
  have hsum : ∑ j : Fin N, partF B (plSpec α c N) j m₁ * partF B (plSpec α c N) j m₂ ≤
      (N : ℝ) - (B : ℝ) * (gammaOf N B - m₁) - (B : ℝ) * (gammaOf N B - m₂) +
        K * ((B : ℝ) * (gammaOf N B - m₂)) := by
    have e : ∀ (g1 g2 : Fin N → ℝ), ∑ j, (1 - g1 j - g2 j + K * g2 j) =
        (N : ℝ) - ∑ j, g1 j - ∑ j, g2 j + K * ∑ j, g2 j := by
      intro g1 g2
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
      simp
    refine (Finset.sum_le_sum (fun j _ => hpt j)).trans (le_of_eq ?_)
    rw [e (fun j => 1 - partF B (plSpec α c N) j m₁) (fun j => 1 - partF B (plSpec α c N) j m₂),
      hs1, hs2]
  unfold TNpart
  calc (B : ℝ)⁻¹ * ∑ j : Fin N, partF B (plSpec α c N) j m₁ * partF B (plSpec α c N) j m₂
      ≤ (B : ℝ)⁻¹ * ((N : ℝ) - (B : ℝ) * (gammaOf N B - m₁) - (B : ℝ) * (gammaOf N B - m₂) +
        K * ((B : ℝ) * (gammaOf N B - m₂))) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hBr.le)
    _ = _ := by
        rw [hK]
        have hNB : (N : ℝ) = (B : ℝ) * gammaOf N B := by unfold gammaOf; field_simp
        rw [hNB]
        field_simp
        ring

private lemma upper_gauss_Ioo : 0 < (gaussianReal 0 1).real (Ioo (1 : ℝ) 2) := by
  have habs := gaussianReal_absolutelyContinuous' 0 (one_ne_zero : (1 : NNReal) ≠ 0)
  have hne : gaussianReal 0 1 (Ioo (1 : ℝ) 2) ≠ 0 := by
    intro h0
    have h1 := habs h0
    rw [Real.volume_Ioo] at h1
    norm_num at h1
  exact ENNReal.toReal_pos hne (measure_ne_top _ _)

private lemma upper_S_lower {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {K : ℝ} (hK : 0 ≤ K) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ q1 q2 : ℝ, 1 / (1 - β) ^ 2 ≤ q1 → 0 ≤ q2 → q2 ≤ K * q1 →
      c0 ≤ ∑' a : ℕ, ∫ g : ℝ, q1 * emaW β a ^ 2 * g ^ 2 /
        ((1 + q1 * emaW β a ^ 2 * g ^ 2) * (1 + q2 * emaW β a ^ 2 * g ^ 2))
        ∂(gaussianReal 0 1) := by
  have hp0pos := upper_gauss_Ioo
  set p0 := (gaussianReal 0 1).real (Ioo (1 : ℝ) 2) with hp0
  refine ⟨β ^ 2 / (2 * (1 + 4 * K)) * p0, by positivity, ?_⟩
  intro q1 q2 hq1 hq2 hqK
  have hb1 : 0 < 1 - β := by linarith
  have hq1pos : 0 < q1 := lt_of_lt_of_le (by positivity) hq1
  have hq1' : 1 ≤ q1 * (1 - β) ^ 2 := by
    rwa [div_le_iff₀ (by positivity)] at hq1
  have hex : ∃ a : ℕ, q1 * emaW β a ^ 2 ≤ 1 := by
    have ht := (vk_w2_summable hβ0 hβ1).tendsto_atTop_zero
    have := (ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / q1 by positivity)))
    obtain ⟨a, ha⟩ := this.exists
    refine ⟨a, ?_⟩
    have : emaW β a ^ 2 < 1 / q1 := ha
    rw [lt_div_iff₀ hq1pos] at this
    nlinarith
  classical
  obtain ⟨a, ha1, ha2⟩ : ∃ a : ℕ, q1 * emaW β a ^ 2 ≤ 1 ∧ β ^ 2 ≤ q1 * emaW β a ^ 2 := by
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]
      have : emaW β 0 = 1 - β := by unfold emaW; simp
      rw [this]
      nlinarith
    · obtain ⟨a', ha'⟩ : ∃ a', Nat.find hex = a' + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hlt : ¬ q1 * emaW β a' ^ 2 ≤ 1 := Nat.find_min hex (by omega)
      push_neg at hlt
      rw [ha']
      have : emaW β (a' + 1) = β * emaW β a' := by
        have := vk_emaW_add β a' 1
        simpa using this
      rw [this]
      have hb2 : β ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg β]
  obtain ⟨hI, hS⟩ := age_Sterm hβ0 hβ1 hq1pos.le hq2
  have hw0 := vk_emaW_pos hβ0 hβ1 a
  set c1 : ℝ := β ^ 2 / (2 * (1 + 4 * K)) with hc1
  have hlow : ∀ g ∈ Ioo (1 : ℝ) 2, c1 ≤ q1 * emaW β a ^ 2 * g ^ 2 /
      ((1 + q1 * emaW β a ^ 2 * g ^ 2) * (1 + q2 * emaW β a ^ 2 * g ^ 2)) := by
    intro g hg
    have hg1 : 1 ≤ g ^ 2 := by nlinarith [hg.1]
    have hg2 : g ^ 2 ≤ 4 := by nlinarith [hg.1, hg.2]
    set x := q1 * emaW β a ^ 2 * g ^ 2 with hx
    set z := q2 * emaW β a ^ 2 * g ^ 2 with hz
    have hx1 : β ^ 2 ≤ x := by
      calc β ^ 2 ≤ q1 * emaW β a ^ 2 := ha2
        _ = q1 * emaW β a ^ 2 * 1 := by ring
        _ ≤ x := mul_le_mul_of_nonneg_left hg1 (by positivity)
    have hx4 : x ≤ 4 := by
      calc x = (q1 * emaW β a ^ 2) * g ^ 2 := rfl
        _ ≤ 1 * 4 := mul_le_mul ha1 hg2 (sq_nonneg g) zero_le_one
        _ = 4 := by norm_num
    have hz0 : 0 ≤ z := by positivity
    have hz4 : z ≤ 4 * K := by
      have : z ≤ K * x := by
        calc z = q2 * (emaW β a ^ 2 * g ^ 2) := by rw [hz]; ring
          _ ≤ (K * q1) * (emaW β a ^ 2 * g ^ 2) :=
              mul_le_mul_of_nonneg_right hqK (by positivity)
          _ = K * x := by rw [hx]; ring
      nlinarith
    have hx0 : 0 ≤ x := le_trans (sq_nonneg β) hx1
    have hb2 : β ^ 2 ≤ 1 := by nlinarith
    have e : x / ((1 + x) * (1 + z)) = (x / (1 + x)) * (1 / (1 + z)) := by
      field_simp
    rw [e, hc1]
    have h1 : β ^ 2 / 2 ≤ x / (1 + x) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      nlinarith
    have h2 : 1 / (1 + 4 * K) ≤ 1 / (1 + z) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    calc β ^ 2 / (2 * (1 + 4 * K)) = (β ^ 2 / 2) * (1 / (1 + 4 * K)) := by field_simp
      _ ≤ (x / (1 + x)) * (1 / (1 + z)) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
  have hterm : c1 * p0 ≤ ∫ g : ℝ, q1 * emaW β a ^ 2 * g ^ 2 /
      ((1 + q1 * emaW β a ^ 2 * g ^ 2) * (1 + q2 * emaW β a ^ 2 * g ^ 2))
      ∂(gaussianReal 0 1) := by
    have hind : ∫ g : ℝ, (Ioo (1 : ℝ) 2).indicator (fun _ => c1) g ∂(gaussianReal 0 1) =
        c1 * p0 := by
      rw [integral_indicator_const _ measurableSet_Ioo, smul_eq_mul, mul_comm]
    rw [← hind]
    refine integral_mono ((integrable_const c1).indicator measurableSet_Ioo) (hI a) (fun g => ?_)
    by_cases hg : g ∈ Ioo (1 : ℝ) 2
    · rw [Set.indicator_of_mem hg]; exact hlow g hg
    · rw [Set.indicator_of_notMem hg]; positivity
  exact hterm.trans (hS.le_tsum a (fun b _ => integral_nonneg fun g => by positivity))

private lemma upper_gap_q {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {K : ℝ} (hK : 0 ≤ K) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ q1 q2 : ℝ, 1 / (1 - β) ^ 2 ≤ q1 → 0 ≤ q2 → q2 ≤ K * q1 → ∀ ℓ : ℤ,
      c0 ≤ rW (emaW β) q1 - MLag β q1 q2 ℓ ∧ c0 ≤ rW (emaW β) q1 - MLag β q2 q1 ℓ := by
  obtain ⟨c0, hc0, h⟩ := upper_S_lower hβ0 hβ1 hK
  refine ⟨c0, hc0, fun q1 q2 h1 hq2 h2 ℓ => ?_⟩
  have hb1 : 0 < 1 - β := by linarith
  have hq1 : 0 ≤ q1 := le_trans (by positivity) h1
  have heq := age_gap_eq hβ0 hβ1 hq1 hq2
  obtain ⟨hl1, hl2⟩ := age_Mlag_le hβ0 hβ1 hq1 hq2 ℓ
  obtain ⟨hl3, hl4⟩ := age_Mlag_le hβ0 hβ1 hq2 hq1 ℓ
  have hS := h q1 q2 h1 hq2 h2
  constructor
  · linarith
  · linarith

private lemma upper_gap_m {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∃ m0 : ℝ, ∀ m1 m2 : ℝ, m0 ≤ m1 → m1 ≤ m2 → m2 ≤ m1 + 1 → ∀ ℓ : ℤ,
      c0 ≤ m1 - MLag β (Qm β m1) (Qm β m2) ℓ ∧ c0 ≤ m1 - MLag β (Qm β m2) (Qm β m1) ℓ := by
  obtain ⟨C, hC⟩ := lem_app_pl_weights_iii_logQ hβ0 hβ1
  have hL : 0 < |Real.log β| := abs_pos.2 (Real.log_neg hβ0 hβ1).ne
  have hb1 : 0 < 1 - β := by linarith
  obtain ⟨c0, hc0, hgap⟩ := upper_gap_q hβ0 hβ1
    (K := Real.exp (2 * C + 2 * |Real.log β|)) (Real.exp_pos _).le
  refine ⟨c0, hc0, max 1 ((Real.log (1 / (1 - β) ^ 2) + C) / (2 * |Real.log β|)), ?_⟩
  intro m1 m2 hm1 h12 h2 ℓ
  have hm1' : 1 ≤ m1 := (le_max_left _ _).trans hm1
  have hm1'' : (Real.log (1 / (1 - β) ^ 2) + C) / (2 * |Real.log β|) ≤ m1 :=
    (le_max_right _ _).trans hm1
  have hm2' : 1 ≤ m2 := hm1'.trans h12
  obtain ⟨hq1, hr1⟩ := vk_Qm hβ0 hβ1 (by linarith : 0 < m1)
  obtain ⟨hq2, hr2⟩ := vk_Qm hβ0 hβ1 (by linarith : 0 < m2)
  have hA := hC m1 hm1'
  have hB := hC m2 hm2'
  rw [abs_le] at hA hB
  have hlow : 1 / (1 - β) ^ 2 ≤ Qm β m1 := by
    have h1 : Real.log (1 / (1 - β) ^ 2) ≤ Real.log (Qm β m1) := by
      rw [div_le_iff₀ (by positivity)] at hm1''
      nlinarith [hA.1]
    exact (Real.log_le_log_iff (by positivity) hq1).1 h1
  have hup : Qm β m2 ≤ Real.exp (2 * C + 2 * |Real.log β|) * Qm β m1 := by
    have h1 : Real.log (Qm β m2) ≤ Real.log (Real.exp (2 * C + 2 * |Real.log β|) * Qm β m1) := by
      rw [Real.log_mul (Real.exp_pos _).ne' hq1.ne', Real.log_exp]
      nlinarith [hA.2, hB.1, hB.2, hA.1, abs_nonneg (Real.log β)]
    exact (Real.log_le_log_iff hq2 (by positivity)).1 h1
  have := hgap (Qm β m1) (Qm β m2) hlow hq2.le hup ℓ
  rw [hr1] at this
  exact this

private lemma upper_alg_small {T M D2 m1 m2 γ g0 C : ℝ} (hC : 0 ≤ C) (hg0 : 0 < g0)
    (hγ : 4 + 2 * C ≤ γ) (hm1 : γ - 1 ≤ m1) (h12 : m1 ≤ m2) (h2γ : m2 < γ)
    (hT0 : 0 ≤ T) (hT1 : T ≤ m1)
    (hTR : T ≤ m1 + m2 - γ + C * ((γ - m1) * (γ - m2)) / γ)
    (hM0 : 0 ≤ M) (hM1 : M ≤ m1) (hD : D2 ≤ (m1 - M) * (m2 - M)) (hgap : g0 ≤ m1 - M) :
    g0 / 2 * (γ - m1) ≤
      γ ^ 2 * ((1 - T * M / (m1 * m2)) * (1 - M / γ) - T * D2 / (γ * m1 * m2)) := by
  have hC4 : 0 ≤ C := hC
  have hγ0 : 0 < γ := by linarith
  have hm1p : 0 < m1 := by linarith
  have hm2p : 0 < m2 := by linarith
  have hd1 : γ - m1 ≤ 1 := by linarith
  have hd2 : 0 < γ - m2 := by linarith
  have hd21 : γ - m2 ≤ γ - m1 := by linarith
  obtain ⟨d1, hd1def⟩ : ∃ d1, d1 = γ - m1 := ⟨_, rfl⟩
  obtain ⟨d2, hd2def⟩ : ∃ d2, d2 = γ - m2 := ⟨_, rfl⟩
  rw [← hd1def] at hd1 hd21 hTR ⊢
  rw [← hd2def] at hd2 hd21 hTR
  have hd1p : 0 < d1 := by linarith
  -- n
  obtain ⟨n, hn⟩ : ∃ n, n = m1 * m2 + T * (γ - m1 - m2) := ⟨_, rfl⟩
  have hsγ : d1 + d2 ≤ γ := by linarith
  have hR : 0 ≤ C * (d1 * d2) / γ := by positivity
  have hn1 : γ * d1 / 2 ≤ n := by
    have hT' : T ≤ γ - (d1 + d2) + C * (d1 * d2) / γ := by
      have : m1 + m2 - γ = γ - (d1 + d2) := by rw [hd1def, hd2def]; ring
      linarith
    have h1 : T * (γ - (d1 + d2)) ≤ (γ - (d1 + d2) + C * (d1 * d2) / γ) * (γ - (d1 + d2)) :=
      mul_le_mul_of_nonneg_right hT' (by linarith)
    have hnn : n = m1 * m2 - T * (γ - (d1 + d2)) := by
      rw [hn, hd1def, hd2def]; ring
    have hmm : m1 * m2 = (γ - d1) * (γ - d2) := by rw [hd1def, hd2def]; ring
    have hRγ : C * (d1 * d2) / γ * γ = C * (d1 * d2) := by field_simp
    have h2 : n ≥ γ * (d1 + d2) + d1 * d2 - (d1 + d2) ^ 2 - C * (d1 * d2) / γ * (γ - (d1 + d2)) := by
      rw [hnn, hmm]; linarith [h1]
    have h3 : C * (d1 * d2) / γ * (γ - (d1 + d2)) ≤ C * (d1 * d2) := by
      have h0 : 0 ≤ C * (d1 * d2) / γ * (d1 + d2) := mul_nonneg hR (by linarith)
      have : C * (d1 * d2) / γ * (γ - (d1 + d2)) =
          C * (d1 * d2) / γ * γ - C * (d1 * d2) / γ * (d1 + d2) := by ring
      rw [this, hRγ]; linarith
    have h4 : d1 * d2 ≤ d1 := by nlinarith
    have h5 : (d1 + d2) ^ 2 ≤ 2 * (d1 + d2) := by nlinarith
    have h6 : C * (d1 * d2) ≤ C * d1 := mul_le_mul_of_nonneg_left h4 hC
    have h7 : C * d1 ≤ C * (d1 + d2) := by nlinarith
    have h8 : (d1 + d2) * (γ / 2) ≤ (d1 + d2) * (γ - 2 - C) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h9 : 0 ≤ γ * d2 := mul_nonneg hγ0.le hd2.le
    have h10 : 0 ≤ d1 * d2 := mul_nonneg hd1p.le hd2.le
    linarith
  have hn0 : 0 ≤ n := by have := mul_pos hγ0 hd1p; linarith
  -- identity
  have hid : (1 - T * M / (m1 * m2)) * (1 - M / γ) - T * D2 / (γ * m1 * m2) =
      (1 - m1 / γ) * (1 - T / m2) + T * ((m1 - M) * (m2 - M) - D2) / (γ * (m1 * m2)) +
        (m1 * m2 + T * (γ - m1 - m2)) / (γ * (m1 * m2)) * (m1 - M) := by
    field_simp; ring
  rw [← hn] at hid
  have hb0 : 0 ≤ (1 - m1 / γ) * (1 - T / m2) := by
    refine mul_nonneg ?_ ?_
    · rw [sub_nonneg, div_le_one hγ0]; linarith
    · rw [sub_nonneg, div_le_one hm2p]; linarith
  have a1 : 0 ≤ T * ((m1 - M) * (m2 - M) - D2) / (γ * (m1 * m2)) :=
    div_nonneg (mul_nonneg hT0 (sub_nonneg.2 hD)) (by positivity)
  have hΔ : n / (γ * (m1 * m2)) * g0 ≤
      (1 - T * M / (m1 * m2)) * (1 - M / γ) - T * D2 / (γ * m1 * m2) := by
    rw [hid]
    have : n / (γ * (m1 * m2)) * g0 ≤ n / (γ * (m1 * m2)) * (m1 - M) :=
      mul_le_mul_of_nonneg_left hgap (div_nonneg hn0 (by positivity))
    linarith
  have hfin : g0 / 2 * d1 ≤ γ ^ 2 * (n / (γ * (m1 * m2)) * g0) := by
    have e : γ ^ 2 * (n / (γ * (m1 * m2)) * g0) = γ * n / (m1 * m2) * g0 := by
      field_simp
    rw [e]
    have : d1 / 2 ≤ γ * n / (m1 * m2) := by
      rw [le_div_iff₀ (mul_pos hm1p hm2p)]
      have hmm : m1 * m2 ≤ γ ^ 2 := by
        rw [sq]; exact mul_le_mul (by linarith) (by linarith) hm2p.le hγ0.le
      calc d1 / 2 * (m1 * m2) ≤ d1 / 2 * γ ^ 2 :=
            mul_le_mul_of_nonneg_left hmm (by positivity)
        _ = γ * (γ * d1 / 2) := by ring
        _ ≤ γ * n := mul_le_mul_of_nonneg_left hn1 hγ0.le
    calc g0 / 2 * d1 = g0 * (d1 / 2) := by ring
      _ ≤ g0 * (γ * n / (m1 * m2)) := mul_le_mul_of_nonneg_left this hg0.le
      _ = _ := by ring
  calc g0 / 2 * d1 ≤ γ ^ 2 * (n / (γ * (m1 * m2)) * g0) := hfin
    _ ≤ _ := mul_le_mul_of_nonneg_left hΔ (sq_nonneg _)

/-- Small-deficit determinant bound (uniform in `N`). -/
private lemma upper_det_small {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ γ0 : ℝ, ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c →
      γ0 ≤ gammaOf N B → ∀ (ℓ : ℤ) (m₁ m₂ : ℝ),
        gammaOf N B - 1 ≤ m₁ → m₁ < gammaOf N B → gammaOf N B - 1 ≤ m₂ → m₂ < gammaOf N B →
          κ * (gammaOf N B - min m₁ m₂) ≤
            gammaOf N B ^ 2 * deltaN β B (plSpec α c N) ℓ m₁ m₂ := by
  obtain ⟨c0, hc0, m0, hgap⟩ := upper_gap_m hβ0 hβ1
  refine ⟨c0 / 2, by positivity, max (m0 + 1) (4 + 2 * (α + 1)), ?_⟩
  intro N B c hN hB hc hγ ℓ m₁ m₂ hm₁ hm₁γ hm₂ hm₂γ
  have hγ4 : 4 + 2 * (α + 1) ≤ gammaOf N B := (le_max_right _ _).trans hγ
  have hγm : m0 + 1 ≤ gammaOf N B := (le_max_left _ _).trans hγ
  have hI₁ : m₁ ∈ Ioo 0 (gammaOf N B) := ⟨by linarith, hm₁γ⟩
  have hI₂ : m₂ ∈ Ioo 0 (gammaOf N B) := ⟨by linarith, hm₂γ⟩
  have hpos := vk_pos_plSpec (α := α) hc N
  have hC0 : (0 : ℝ) ≤ α + 1 := by linarith
  obtain ⟨hM0, hMmin, hD⟩ := vk_det_i hβ0 hβ1 hI₁.1 hI₂.1 ℓ
  unfold deltaN
  rcases le_total m₁ m₂ with h | h
  · have hg := (hgap m₁ m₂ (by linarith) h (by linarith) ℓ).1
    obtain ⟨hT0, hT1⟩ := vk_T_bd hB hN hpos hI₁ hI₂ h
    have hTR := upper_T_le hα hN hB hc hI₁ hI₂
    rw [min_eq_left h]
    generalize MLag β (Qm β m₁) (Qm β m₂) ℓ = M at hM0 hMmin hD hg ⊢
    generalize DLag β (Qm β m₁) (Qm β m₂) ℓ = D at hD ⊢
    exact upper_alg_small hC0 hc0 hγ4 hm₁ h hm₂γ hT0 hT1 hTR hM0
      (hMmin.trans (min_le_left _ _)) hD hg
  · have hg := (hgap m₂ m₁ (by linarith) h (by linarith) ℓ).2
    obtain ⟨hT0, hT1⟩ := vk_T_bd hB hN hpos hI₂ hI₁ h
    have hTR := upper_T_le hα hN hB hc hI₂ hI₁
    rw [min_eq_right h, vk_TN_comm]
    generalize MLag β (Qm β m₁) (Qm β m₂) ℓ = M at hM0 hMmin hD hg ⊢
    generalize DLag β (Qm β m₁) (Qm β m₂) ℓ = D at hD ⊢
    have key := upper_alg_small (D2 := D ^ 2) hC0 hc0 hγ4 hm₂ h hm₁γ hT0 hT1 hTR hM0
      (hMmin.trans (min_le_right _ _)) (by linarith [hD, mul_comm (m₁ - M) (m₂ - M)]) hg
    refine key.trans (le_of_eq ?_)
    ring

private lemma upper_fixed {α β η : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ A γ0 : ℝ, ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c →
      max γ0 1 ≤ gammaOf N B → ∀ i : Fin N,
        ∑' ℓ : ℤ, lagTerm β B (plSpec α c N) i
            (Ico (η * gammaOf N B) (gammaOf N B)) (Ico (η * gammaOf N B) (gammaOf N B)) ℓ ≤
          A * gammaOf N B * ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α := by
  obtain ⟨K0, hK0, hW⟩ := upper_W_bound (η := η) hα hβ0 hβ1 hη0 hη1
  obtain ⟨κ1, hκ1, hdl⟩ := upper_det_large hα hβ0 hβ1
  obtain ⟨κ2, hκ2, γ1, hds⟩ := upper_det_small hα hβ0 hβ1
  obtain ⟨CD, hCD0, hCD⟩ := upper_D_sum hβ0 hβ1
  have hκ : 0 < min κ1 κ2 := lt_min hκ1 hκ2
  refine ⟨(K0 ^ 2 / min κ1 κ2) * CD * 20, γ1, ?_⟩
  intro N B c hN hB hc hγ i
  obtain ⟨hInt, hSum⟩ := upper_finiteness hα hβ0 hβ1 hη0 hN hB hc i
  have hγ1 : γ1 ≤ gammaOf N B := (le_max_left _ _).trans hγ
  have hγ1' : 1 ≤ gammaOf N B := (le_max_right _ _).trans hγ
  have hγ0 : 0 < gammaOf N B := by linarith
  have hy0 : 0 ≤ ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α := Real.rpow_nonneg (by positivity) _
  set γ := gammaOf N B with hγdef
  set y := ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α with hy
  set κ := min κ1 κ2 with hκdef
  set G : Set ℝ := Ico (η * γ) γ with hG
  have hGH : G ⊆ Ioo 0 γ := fun m hm => ⟨(mul_pos hη0 hγ0).trans_le hm.1, hm.2⟩
  have hGm : MeasurableSet G := measurableSet_Ico
  set u : ℝ → ℝ := fun m => 1 / Real.sqrt (γ - m) with hu
  set A0 : ℝ := (K0 ^ 2 / κ) * y / γ with hA0
  have hA00 : 0 ≤ A0 := by positivity
  have hpt : ∀ (ℓ : ℤ) (p : ℝ × ℝ), p ∈ G ×ˢ G →
      lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2 ≤
        A0 * DLag β (Qm β p.1) (Qm β p.2) ℓ * (4 + 4 * (u p.1 * u p.2)) := by
    intro ℓ p hp
    have hm1 : p.1 ∈ G := hp.1
    have hm2 : p.2 ∈ G := hp.2
    have hm1' := hGH hm1
    have hm2' := hGH hm2
    have hd1 : 0 < γ - p.1 := by linarith [hm1.2]
    have hd2 : 0 < γ - p.2 := by linarith [hm2.2]
    have hW1 := age_Wpart_nonneg hα hβ0 hβ1 hN hB hc i hm1'
    have hW2 := age_Wpart_nonneg hα hβ0 hβ1 hN hB hc i hm2'
    have hb1 := hW N B c hN hB hc hγ1' i p.1 hm1.1 hm1.2
    have hb2 := hW N B c hN hB hc hγ1' i p.2 hm2.1 hm2.2
    have hD0 := age_DLag_nonneg hβ0 (vk_Qm hβ0 hβ1 hm1'.1).1.le (vk_Qm hβ0 hβ1 hm2'.1).1.le ℓ
    have hΔ : κ * (max (γ - p.1) (γ - p.2) * max (max (γ - p.1) (γ - p.2)) 1) ≤
        γ ^ 2 * deltaN β B (plSpec α c N) ℓ p.1 p.2 := by
      have hmax : max (γ - p.1) (γ - p.2) = γ - min p.1 p.2 := max_sub_sub_left _ _ _
      rw [hmax]
      have hdpos : 0 < γ - min p.1 p.2 := by
        rw [← hmax]; exact lt_max_of_lt_left hd1
      rcases le_total (γ - min p.1 p.2) 1 with hd | hd
      · rw [max_eq_right hd, mul_one]
        have h := hds N B c hN hB hc hγ1 ℓ p.1 p.2
          (by linarith [min_le_left p.1 p.2]) hm1.2
          (by linarith [min_le_right p.1 p.2]) hm2.2
        calc κ * (γ - min p.1 p.2) ≤ κ2 * (γ - min p.1 p.2) :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) hdpos.le
          _ ≤ _ := h
      · rw [max_eq_left hd]
        have h := hdl N B c hN hB hc ℓ p.1 p.2 hm1' hm2'
        calc κ * ((γ - min p.1 p.2) * (γ - min p.1 p.2)) ≤ κ1 * (γ - min p.1 p.2) ^ 2 := by
              rw [sq]
              exact mul_le_mul_of_nonneg_right (min_le_left _ _) (mul_self_nonneg _)
          _ ≤ _ := h
    have hΔ0 : 0 < deltaN β B (plSpec α c N) ℓ p.1 p.2 := by
      have hpos : 0 < κ * (max (γ - p.1) (γ - p.2) * max (max (γ - p.1) (γ - p.2)) 1) :=
        mul_pos hκ (mul_pos (lt_max_of_lt_left hd1) (lt_max_of_lt_right one_pos))
      exact (mul_pos_iff_of_pos_left (by positivity)).1 (lt_of_lt_of_le hpos hΔ)
    have key := upper_scalar (K := K0) (s := Real.sqrt y) hK0 (Real.sqrt_nonneg _) hκ hγ1' hd1 hd2
      hW2 hD0 hΔ0 hb1 hb2 hΔ
    unfold lagIntegrand lagNumer
    rw [Real.sq_sqrt hy0] at key
    have e : (1 / (Real.sqrt (γ - p.1) * Real.sqrt (γ - p.2))) = u p.1 * u p.2 := by
      simp only [hu, one_div_mul_one_div]
    rw [e] at key
    exact key
  have hDsum : ∀ (p : ℝ × ℝ), p ∈ G ×ˢ G → ∀ S : Finset ℤ,
      ∑ ℓ ∈ S, DLag β (Qm β p.1) (Qm β p.2) ℓ ≤ CD := by
    intro p hp S
    obtain ⟨hsum, hle⟩ := hCD p.1 p.2 (hGH hp.1).1 (hGH hp.2).1
    exact (sum_le_hasSum S (fun ℓ _ => age_DLag_nonneg hβ0 (vk_Qm hβ0 hβ1 (hGH hp.1).1).1.le
      (vk_Qm hβ0 hβ1 (hGH hp.2).1).1.le ℓ) hsum).trans hle
  have hηγ : η * γ < γ := by nlinarith
  have hu_int : IntegrableOn u G := (upper_int_u (a := η * γ) (b := γ) hηγ).1
  have hu_val : ∫ m in G, u m = 2 * Real.sqrt (γ - η * γ) :=
    (upper_int_u (a := η * γ) (b := γ) hηγ).2
  have hP : (volume.restrict G).prod (volume.restrict G) = volume.restrict (G ×ˢ G) := by
    rw [Measure.prod_restrict]; rfl
  have hvol : ∫ _m in G, (1 : ℝ) = γ - η * γ := by
    rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, hG, Real.volume_Ico,
      ENNReal.toReal_ofReal (by nlinarith)]
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict G) := integrable_const _
  have h11 := h1.mul_prod h1
  have h22 := hu_int.mul_prod hu_int
  set g : ℝ × ℝ → ℝ := fun p => CD * A0 * (4 * (1 * 1) + 4 * (u p.1 * u p.2)) with hg
  have hg_int : Integrable g ((volume.restrict G).prod (volume.restrict G)) :=
    (((h11.const_mul 4).add (h22.const_mul 4)).const_mul _)
  have hg_val : ∫ p, g p ∂((volume.restrict G).prod (volume.restrict G)) =
      CD * A0 * (4 * (γ - η * γ) ^ 2 + 4 * (2 * Real.sqrt (γ - η * γ)) ^ 2) := by
    have e1 : ∫ p : ℝ × ℝ, (fun _ : ℝ => (1 : ℝ)) p.1 * (fun _ : ℝ => (1 : ℝ)) p.2
        ∂((volume.restrict G).prod (volume.restrict G)) =
        (∫ x in G, (1 : ℝ)) * ∫ x in G, (1 : ℝ) :=
      integral_prod_mul (fun _ : ℝ => (1 : ℝ)) (fun _ : ℝ => (1 : ℝ))
    have e2 : ∫ p : ℝ × ℝ, u p.1 * u p.2
        ∂((volume.restrict G).prod (volume.restrict G)) =
        (∫ x in G, u x) * ∫ x in G, u x := integral_prod_mul u u
    have ha : ∫ p : ℝ × ℝ, 4 * ((fun _ : ℝ => (1 : ℝ)) p.1 * (fun _ : ℝ => (1 : ℝ)) p.2)
        ∂((volume.restrict G).prod (volume.restrict G)) =
        4 * ((γ - η * γ) * (γ - η * γ)) := by
      rw [integral_const_mul, e1, hvol]
    have hb : ∫ p : ℝ × ℝ, 4 * (u p.1 * u p.2)
        ∂((volume.restrict G).prod (volume.restrict G)) =
        4 * ((2 * Real.sqrt (γ - η * γ)) * (2 * Real.sqrt (γ - η * γ))) := by
      rw [integral_const_mul, e2, hu_val]
    simp only [hg]
    rw [integral_const_mul, integral_add (h11.const_mul 4) (h22.const_mul 4), ha, hb]
    ring
  have hterm : ∀ ℓ : ℤ, lagTerm β B (plSpec α c N) i G G ℓ =
      ∫ p, lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2
        ∂((volume.restrict G).prod (volume.restrict G)) := by
    intro ℓ
    exact (integral_prod
      (fun p : ℝ × ℝ => lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2)
      (by rw [hP]; exact hInt ℓ)).symm
  have hsumS : ∀ S : Finset ℤ, ∑ ℓ ∈ S, lagTerm β B (plSpec α c N) i G G ℓ ≤
      CD * A0 * (4 * (γ - η * γ) ^ 2 + 4 * (2 * Real.sqrt (γ - η * γ)) ^ 2) := by
    intro S
    rw [← hg_val]
    simp_rw [hterm]
    rw [← integral_finsetSum S (fun ℓ _ => by rw [hP]; exact hInt ℓ)]
    rw [hP]
    have hg_int' : Integrable g (volume.restrict (G ×ˢ G)) := by rw [← hP]; exact hg_int
    refine setIntegral_mono_on (integrable_finsetSum S (fun ℓ _ => hInt ℓ)) hg_int'
      (hGm.prod hGm) (fun p hp => ?_)
    have hfac : 0 ≤ 4 + 4 * (u p.1 * u p.2) := by
      have : 0 ≤ u p.1 * u p.2 := mul_nonneg (by simp only [hu]; positivity) (by simp only [hu]; positivity)
      linarith
    calc ∑ ℓ ∈ S, lagIntegrand β B (plSpec α c N) i ℓ p.1 p.2
        ≤ ∑ ℓ ∈ S, A0 * DLag β (Qm β p.1) (Qm β p.2) ℓ * (4 + 4 * (u p.1 * u p.2)) :=
          Finset.sum_le_sum (fun ℓ _ => hpt ℓ p hp)
      _ = A0 * (∑ ℓ ∈ S, DLag β (Qm β p.1) (Qm β p.2) ℓ) * (4 + 4 * (u p.1 * u p.2)) := by
          rw [Finset.mul_sum, Finset.sum_mul]
      _ ≤ A0 * CD * (4 + 4 * (u p.1 * u p.2)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hDsum p hp S) hA00) hfac
      _ = g p := by simp only [hg]; ring
  have hbound : CD * A0 * (4 * (γ - η * γ) ^ 2 + 4 * (2 * Real.sqrt (γ - η * γ)) ^ 2) ≤
      (K0 ^ 2 / κ) * CD * 20 * γ * y := by
    have hs : (2 * Real.sqrt (γ - η * γ)) ^ 2 = 4 * (γ - η * γ) := by
      rw [mul_pow, Real.sq_sqrt (by nlinarith)]; norm_num
    rw [hs]
    have h2 : γ - η * γ ≤ γ := by nlinarith [mul_pos hη0 hγ0]
    have h0 : 0 ≤ γ - η * γ := by nlinarith [mul_pos hη0 hγ0]
    have h1 : (γ - η * γ) ^ 2 ≤ γ ^ 2 := pow_le_pow_left₀ h0 h2 2
    have h3 : 4 * (γ - η * γ) ^ 2 + 4 * (4 * (γ - η * γ)) ≤ 20 * γ ^ 2 := by nlinarith
    have hCA : 0 ≤ CD * A0 := mul_nonneg hCD0 hA00
    calc CD * A0 * (4 * (γ - η * γ) ^ 2 + 4 * (4 * (γ - η * γ)))
        ≤ CD * A0 * (20 * γ ^ 2) := mul_le_mul_of_nonneg_left h3 hCA
      _ = (K0 ^ 2 / κ) * CD * 20 * γ * y := by
          simp only [hA0]; field_simp
  exact (hSum.tsum_le_of_sum_le hsumS).trans hbound


/-- `lem:app-pl-upper` (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Upper participation endpoint]\label{lem:app-pl-upper}
For every $\eta\in(0,1)$ there is $C_\eta$ such that, for all large $N$ and all $1\le i\le N$,
\[
\mathfrak v_i\big[[\eta\gamma,\gamma),[\eta\gamma,\gamma)\big]\le C_\eta\,\gamma\,(i/N)^\alpha .
\]
\end{lemma}
-/
theorem lem_app_pl_upper {α β : ℝ} (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ C : ℝ, ∀ (Nn Bn : ℕ → ℕ) (cn : ℕ → ℝ), assum_app_pl_regime α β Nn Bn cn →
      ∀ᶠ n : ℕ in atTop, ∀ i : Fin (Nn n),
        (∀ ℓ : ℤ, IntegrableOn
            (fun p : ℝ × ℝ => lagIntegrand β (Bn n) (plSpec α (cn n) (Nn n)) i ℓ p.1 p.2)
            (Ico (η * gammaOf (Nn n) (Bn n)) (gammaOf (Nn n) (Bn n)) ×ˢ
              Ico (η * gammaOf (Nn n) (Bn n)) (gammaOf (Nn n) (Bn n)))) ∧
        Summable (fun ℓ : ℤ => lagTerm β (Bn n) (plSpec α (cn n) (Nn n)) i
          (Ico (η * gammaOf (Nn n) (Bn n)) (gammaOf (Nn n) (Bn n)))
          (Ico (η * gammaOf (Nn n) (Bn n)) (gammaOf (Nn n) (Bn n))) ℓ) ∧
        vIJ β (Bn n) (plSpec α (cn n) (Nn n)) i
            (Ico (η * gammaOf (Nn n) (Bn n)) (gammaOf (Nn n) (Bn n)))
            (Ico (η * gammaOf (Nn n) (Bn n)) (gammaOf (Nn n) (Bn n))) ≤
          C * gammaOf (Nn n) (Bn n) * ((((i : ℕ) : ℝ) + 1) / (Nn n : ℝ)) ^ α := by
  by_cases hab : 0 < α ∧ 0 < β ∧ β < 1
  · obtain ⟨hα, hβ0, hβ1⟩ := hab
    obtain ⟨A, γ0, hA⟩ := upper_fixed (η := η) hα hβ0 hβ1 hη0 hη1
    refine ⟨(Real.pi ^ 2)⁻¹ * A, fun Nn Bn cn hreg => ?_⟩
    have hev : ∀ᶠ n : ℕ in atTop, max γ0 1 ≤ gammaOf (Nn n) (Bn n) :=
      hreg.hγ.eventually_ge_atTop (max γ0 1)
    filter_upwards [hev] with n hn i
    obtain ⟨hInt, hSum⟩ := upper_finiteness hα hβ0 hβ1 hη0 (hreg.hNpos n) (hreg.hBpos n)
      (hreg.hcpos n) i
    refine ⟨hInt, hSum, ?_⟩
    have h := hA (Nn n) (Bn n) (cn n) (hreg.hNpos n) (hreg.hBpos n) (hreg.hcpos n) hn i
    unfold vIJ
    calc (Real.pi ^ 2)⁻¹ * ∑' ℓ : ℤ, lagTerm β (Bn n) (plSpec α (cn n) (Nn n)) i
            (Ico (η * gammaOf (Nn n) (Bn n)) (gammaOf (Nn n) (Bn n)))
            (Ico (η * gammaOf (Nn n) (Bn n)) (gammaOf (Nn n) (Bn n))) ℓ
        ≤ (Real.pi ^ 2)⁻¹ * (A * gammaOf (Nn n) (Bn n) *
            ((((i : ℕ) : ℝ) + 1) / (Nn n : ℝ)) ^ α) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by ring
  · exact ⟨0, fun Nn Bn cn hreg => absurd ⟨hreg.hα, hreg.hβ0, hreg.hβ1⟩ hab⟩

end Muon.PowerLaw

end

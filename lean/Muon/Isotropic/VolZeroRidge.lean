import Muon.Isotropic.VolRates
import Muon.Isotropic.Bridge

/-!
# Appendix F: v_iso-dependent parts of the small-aspect volatility and the zero-ridge theorem (task L-F.10b)

Snapshot `cr-2026-10-23`. Source: `sections/05b-isotropic/section.tex`. Labels of this package:

* `thm:app-iso-small-volatility`, second display only (`Muon.Isotropic.thm_app_iso_small_volatility_ii`).
  The first display is `Muon.Isotropic.thm_app_iso_small_volatility_i` in `VolRates.lean` (L-F.10).
* `thm:app-iso-zero-ridge`, part (ii) only (`Muon.Isotropic.thm_app_iso_zero_ridge_ii`). Part (i) is
  `Muon.Isotropic.thm_app_iso_zero_ridge_i` in `ZeroRidge.lean` (L-F.3).

These statements use the zero-ridge isotropic volatility `𝔳_{iso,β}` of `def:app-iso-vol-zero`, which is
`Muon.Isotropic.def_app_iso_vol_zero` (`Bridge.lean`, L-F.12), together with its existence predicate
`Muon.Isotropic.hasIsoZeroRidgeVol`. Nothing is redefined here.

Constants reused: `isoKminus`, `isoKplus` (`𝖪^∓_β`, `VolRates.lean`), `isoGammaCirc` (`γ°_β`, `Helpers.lean`),
`volFactor` (`V_β`, `VolFactor.lean`). The aspect ratio is `Muon.PowerLaw.gammaOf N B = N/B`.

Standing regime (`assum:app-setup-regime`): the dimension hypotheses `0 < B`, `0 < N` and the cap
`gammaOf N B ≤ γ⋆`, `1 ≤ C_Σ` are passed exactly as in `Bridge.prop_app_iso_vol_momentum_ii`. Every
limit is a `limUnder` value (through the definition) and carries its existence as a conjunct.
Card: `sections/05b-isotropic/CARD.md` §2, §3, §5 (L-F.10b).
-/

set_option linter.style.longLine false

open MeasureTheory Filter Topology Set

noncomputable section

namespace Muon.Isotropic

private lemma small_vol_summable_omega {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Summable (fun ℓ : ℕ => volOmega (β ^ (ℓ + 1))) := by
  let G : ℕ → ℕ → ℝ := fun ℓ n => volK n ^ 2 * (β ^ (ℓ + 1)) ^ (2 * n + 1)
  have hK : ∀ n : ℕ, 0 ≤ volK n ∧ volK n ≤ 2 := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    constructor
    · unfold volK; positivity
    · have h1 : 1 / (2 * (n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      have h3 : 1 / (2 * (n : ℝ) + 3) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      unfold volK; linarith
  have hbound : ∀ ℓ n : ℕ, G ℓ n ≤ 4 * (β ^ ℓ * β ^ n) := by
    intro ℓ n
    have hp : β ^ ((ℓ + 1) * (2 * n + 1)) ≤ β ^ (ℓ + n) :=
      pow_le_pow_of_le_one hβ0 hβ1.le (by nlinarith)
    have hk : volK n ^ 2 ≤ 4 := by nlinarith [(hK n).1, (hK n).2]
    calc G ℓ n ≤ 4 * (β ^ (ℓ + 1)) ^ (2 * n + 1) :=
        mul_le_mul_of_nonneg_right hk (by positivity)
      _ ≤ 4 * β ^ (ℓ + n) := by
        rw [← pow_mul]
        exact mul_le_mul_of_nonneg_left hp (by norm_num)
      _ = 4 * (β ^ ℓ * β ^ n) := by rw [pow_add]
  have hgeo := summable_geometric_of_lt_one hβ0 hβ1
  have hprod : Summable (fun p : ℕ × ℕ => 4 * (β ^ p.1 * β ^ p.2)) :=
    (Summable.mul_of_nonneg hgeo hgeo (fun n => pow_nonneg hβ0 n)
      (fun n => pow_nonneg hβ0 n)).mul_left 4
  have hs : Summable (Function.uncurry G) :=
    Summable.of_nonneg_of_le (fun p => by dsimp [G, Function.uncurry]; positivity)
      (fun p => hbound p.1 p.2) hprod
  exact hs.prod.mul_left (4 / Real.pi ^ 2)

private lemma abs_le_max_abs_div {a b x γ : ℝ} (hγ : 0 < γ)
    (hlo : a / γ ≤ x) (hhi : x ≤ b / γ) :
    |x| ≤ max |a| |b| / γ := by
  rw [abs_le]
  constructor
  · apply le_trans ?_ hlo
    rw [← neg_div]
    apply (div_le_div_iff_of_pos_right hγ).2
    exact le_trans (neg_le_neg (le_max_left |a| |b|)) (neg_abs_le a)
  · apply le_trans hhi
    apply (div_le_div_iff_of_pos_right hγ).2
    exact le_trans (le_abs_self b) (le_max_right |a| |b|)

/-- `thm:app-iso-small-volatility`, second display, snapshot `cr-2026-10-23`. Declaration of record for the
second display of the label. Parts: (i) the zero-ridge volatility `𝔳_{iso,β}` exists (`hasIsoZeroRidgeVol`
with `def_app_iso_vol_zero`); (ii) `|𝔳_{iso,β}/N − V_β| ≤ 96γ/(1+β²)·(V_β − 1)`; (iii)
`|𝔳_{iso,β}/(N V_β) − 1| ≤ 96γ`. Hypotheses: `0 < β < 1`, `Nin = Nout = N`, `γ = N/B ≤ (1+β²)/96`, and the
standing regime. The first display is `thm_app_iso_small_volatility_i`. LaTeX, verbatim:

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
theorem thm_app_iso_small_volatility_ii (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : Muon.PowerLaw.gammaOf N B ≤ γstar) (hC1 : 1 ≤ CSig)
    (hsmall : Muon.PowerLaw.gammaOf N B ≤ (1 + β ^ 2) / 96) :
    hasIsoZeroRidgeVol cert γstar CSig β N N B (def_app_iso_vol_zero cert γstar CSig β N N B) ∧
    |def_app_iso_vol_zero cert γstar CSig β N N B / (N : ℝ) - volFactor β|
        ≤ 96 * Muon.PowerLaw.gammaOf N B / (1 + β ^ 2) * (volFactor β - 1) ∧
    |def_app_iso_vol_zero cert γstar CSig β N N B / ((N : ℝ) * volFactor β) - 1|
        ≤ 96 * Muon.PowerLaw.gammaOf N B := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hγpos : 0 < Muon.PowerLaw.gammaOf N B :=
    div_pos hNr (by exact_mod_cast hB)
  let i : Fin N := ⟨0, hN⟩
  obtain ⟨-, -, hcs, -, hex, -, -, hv⟩ :=
    prop_app_iso_vol_momentum_ii cert γstar CSig hB hN hβ0 hβ1 hγ hC1 i
  have hc (ℓ : ℕ) : lagCoeff β (Muon.PowerLaw.gammaOf N B) 0 ℓ =
      Muon.PowerLaw.cbarZero cert γstar CSig β B (fun _ : Fin N => (1 : ℝ)) i ℓ :=
    (lem_app_iso_lag_ii cert γstar CSig hB hN hβ0 hβ1 hγ hC1 i ℓ).2.2.2
  have hsC : Summable (fun ℓ : ℕ => lagCoeff β (Muon.PowerLaw.gammaOf N B) 0 (ℓ + 1)) :=
    hcs.congr (fun ℓ => (hc (ℓ + 1)).symm)
  have hsO := small_vol_summable_omega hβ0.le hβ1
  have hvalue : def_app_iso_vol_zero cert γstar CSig β N N B / (N : ℝ) =
      1 + 2 * ∑' ℓ : ℕ, lagCoeff β (Muon.PowerLaw.gammaOf N B) 0 (ℓ + 1) := by
    rw [hv, mul_div_cancel_left₀ _ hNr.ne', Muon.PowerLaw.vZero]
    congr 2
    exact tsum_congr (fun ℓ => (hc (ℓ + 1)).symm)
  let k : ℝ := 96 * Muon.PowerLaw.gammaOf N B / (1 + β ^ 2)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hpoint (ℓ : ℕ) :
      |lagCoeff β (Muon.PowerLaw.gammaOf N B) 0 (ℓ + 1) - volOmega (β ^ (ℓ + 1))|
        ≤ k * volOmega (β ^ (ℓ + 1)) :=
    thm_app_iso_small_volatility_i hβ0 hβ1 hγpos hsmall (by omega)
  have hsum : |(∑' ℓ : ℕ, lagCoeff β (Muon.PowerLaw.gammaOf N B) 0 (ℓ + 1)) -
      ∑' ℓ : ℕ, volOmega (β ^ (ℓ + 1))| ≤ k * ∑' ℓ : ℕ, volOmega (β ^ (ℓ + 1)) := by
    rw [← hsC.tsum_sub hsO]
    apply abs_le.mpr
    constructor
    · have h := Summable.tsum_le_tsum (fun ℓ => (abs_le.mp (hpoint ℓ)).1)
        ((hsO.mul_left k).neg) (hsC.sub hsO)
      simpa only [tsum_neg, tsum_mul_left] using h
    · have h := Summable.tsum_le_tsum (fun ℓ => (abs_le.mp (hpoint ℓ)).2)
        (hsC.sub hsO) (hsO.mul_left k)
      simpa only [tsum_mul_left] using h
  have hfirst : |def_app_iso_vol_zero cert γstar CSig β N N B / (N : ℝ) - volFactor β|
      ≤ k * (volFactor β - 1) := by
    calc
      _ = 2 * |(∑' ℓ : ℕ, lagCoeff β (Muon.PowerLaw.gammaOf N B) 0 (ℓ + 1)) -
          ∑' ℓ : ℕ, volOmega (β ^ (ℓ + 1))| := by
        rw [hvalue, volFactor, ← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), ← abs_mul]
        congr 1
        ring
      _ ≤ 2 * (k * ∑' ℓ : ℕ, volOmega (β ^ (ℓ + 1))) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = k * (volFactor β - 1) := by unfold volFactor; ring
  have hV : 1 ≤ volFactor β := (lem_app_iso_V_iii hβ0 hβ1).1.le
  have hVpos : 0 < volFactor β := by linarith
  have hkbound : k ≤ 96 * Muon.PowerLaw.gammaOf N B := by
    dsimp [k]
    exact div_le_self (by positivity) (by nlinarith [sq_nonneg β])
  refine ⟨hv.symm ▸ hex, hfirst, ?_⟩
  calc
    _ = |def_app_iso_vol_zero cert γstar CSig β N N B / (N : ℝ) - volFactor β| /
        volFactor β := by
      have heq : def_app_iso_vol_zero cert γstar CSig β N N B /
          ((N : ℝ) * volFactor β) - 1 =
          (def_app_iso_vol_zero cert γstar CSig β N N B / (N : ℝ) - volFactor β) /
            volFactor β := by
        field_simp
      rw [heq, abs_div, abs_of_pos hVpos]
    _ ≤ (k * (volFactor β - 1)) / volFactor β :=
      div_le_div_of_nonneg_right hfirst hVpos.le
    _ ≤ k := by
      apply (div_le_iff₀ hVpos).2
      nlinarith
    _ ≤ 96 * Muon.PowerLaw.gammaOf N B := hkbound

/-- `thm:app-iso-zero-ridge`, part (ii), snapshot `cr-2026-10-23`. Declaration of record for part (ii) of the
label (part (i) is `thm_app_iso_zero_ridge_i`). Parts, with `γ = N/B ≥ γ°_β` and `v := 𝔳_{iso,β}`:
(i) `v` exists (`hasIsoZeroRidgeVol`), and `(1 − 2K^-_β)/γ ≤ v/(Nγ) − 1/2 ≤ (1 + 2K^+_β)/γ`;
(ii) the "in particular" `v = N²/(2B)·(1 + O_β(B/N))`, stated as: there is `C` (depending on `β` and the
regime constants only) such that `|2Bv/N² − 1| ≤ C·B/N` for all admissible `N, B`;
(iii) `v/(Nγ) → 1/2` as `γ → ∞` at fixed `β`, stated along sequences of dimensions satisfying the regime,
with `γ_k → ∞`. Hypotheses: `0 < β < 1`, `Nin = Nout = N`, `γ ≥ γ°_β`, and the standing regime (the
uniform and sequential statements carry the regime for each dimension tuple they quantify over). LaTeX, verbatim:

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
-/
theorem thm_app_iso_zero_ridge_ii (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : Muon.PowerLaw.gammaOf N B ≤ γstar) (hC1 : 1 ≤ CSig)
    (hγβ : isoGammaCirc β ≤ Muon.PowerLaw.gammaOf N B) :
    hasIsoZeroRidgeVol cert γstar CSig β N N B (def_app_iso_vol_zero cert γstar CSig β N N B) ∧
    (1 - 2 * isoKminus β) / Muon.PowerLaw.gammaOf N B
        ≤ def_app_iso_vol_zero cert γstar CSig β N N B / ((N : ℝ) * Muon.PowerLaw.gammaOf N B) - 1 / 2 ∧
    def_app_iso_vol_zero cert γstar CSig β N N B / ((N : ℝ) * Muon.PowerLaw.gammaOf N B) - 1 / 2
        ≤ (1 + 2 * isoKplus β) / Muon.PowerLaw.gammaOf N B := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hBr : 0 < (B : ℝ) := by exact_mod_cast hB
  have hγpos : 0 < Muon.PowerLaw.gammaOf N B := div_pos hNr hBr
  let i : Fin N := ⟨0, hN⟩
  obtain ⟨-, -, hcs, -, hex, -, -, hv⟩ :=
    prop_app_iso_vol_momentum_ii cert γstar CSig hB hN hβ0 hβ1 hγ hC1 i
  have hc (ℓ : ℕ) : lagCoeff β (Muon.PowerLaw.gammaOf N B) 0 ℓ =
      Muon.PowerLaw.cbarZero cert γstar CSig β B (fun _ : Fin N => (1 : ℝ)) i ℓ :=
    (lem_app_iso_lag_ii cert γstar CSig hB hN hβ0 hβ1 hγ hC1 i ℓ).2.2.2
  obtain ⟨S, hS, hSlo, hShi⟩ := thm_app_iso_vol_rate hβ0 hβ1 hγβ
  have hStsum :
      (∑' ℓ : ℕ, Muon.PowerLaw.cbarZero cert γstar CSig β B
        (fun _ : Fin N => (1 : ℝ)) i (ℓ + 1)) = S := by
    calc
      _ = ∑' ℓ : ℕ, lagCoeff β (Muon.PowerLaw.gammaOf N B) 0 (ℓ + 1) :=
        tsum_congr (fun ℓ => (hc (ℓ + 1)).symm)
      _ = S := hS.tsum_eq
  have hvalue : def_app_iso_vol_zero cert γstar CSig β N N B / (N : ℝ) = 1 + 2 * S := by
    rw [hv, mul_div_cancel_left₀ _ hNr.ne', Muon.PowerLaw.vZero, hStsum]
  have hcenter :
      def_app_iso_vol_zero cert γstar CSig β N N B /
          ((N : ℝ) * Muon.PowerLaw.gammaOf N B) - 1 / 2 =
        (1 + 2 * (S - Muon.PowerLaw.gammaOf N B / 4)) /
          Muon.PowerLaw.gammaOf N B := by
    calc
      _ = (def_app_iso_vol_zero cert γstar CSig β N N B / (N : ℝ)) /
          Muon.PowerLaw.gammaOf N B - 1 / 2 := by rw [div_div]
      _ = _ := by rw [hvalue]; field_simp; ring
  refine ⟨hv.symm ▸ hex, ?_, ?_⟩
  · rw [hcenter]
    exact (div_le_div_iff_of_pos_right hγpos).2 (by linarith)
  · rw [hcenter]
    exact (div_le_div_iff_of_pos_right hγpos).2 (by linarith)

/-- The "in particular" of `thm:app-iso-zero-ridge`(ii) and its limit, snapshot `cr-2026-10-23`. Declaration of
record for the two consequences stated after the displayed bounds of part (ii) of the label: (a) the order
`𝔳_{iso,β} = N²/(2B)(1 + O_β(B/N))`, with one constant `C` depending on `β` only, uniform over every cap
`γ⋆`, every `C_Σ ≥ 1` and every admissible `N, B` with `γ = N/B ≥ γ°_β` and `γ ≤ γ⋆`; (b) `𝔳_{iso,β}/(Nγ) → 1/2`
as `γ → ∞` at fixed `β`, along dimension sequences whose cap `gs k` is allowed to grow with `k` (the cap of
`assum:app-setup-regime` is per dimension tuple, not a single constant). Hypotheses: `0 < β < 1` and the
certificate `cert`. LaTeX of the displayed part (ii) is `thm_app_iso_zero_ridge_ii`'s docstring. -/
theorem thm_app_iso_zero_ridge_ii_consequences (cert : Muon.External.GaussianOpNorm)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∃ C : ℝ, ∀ (γstar CSig : ℝ), 1 ≤ CSig → ∀ N B : ℕ, 0 < B → 0 < N →
        Muon.PowerLaw.gammaOf N B ≤ γstar → isoGammaCirc β ≤ Muon.PowerLaw.gammaOf N B →
        |2 * (B : ℝ) * def_app_iso_vol_zero cert γstar CSig β N N B / (N : ℝ) ^ 2 - 1|
          ≤ C * ((B : ℝ) / (N : ℝ))) ∧
    (∀ CSig : ℝ, 1 ≤ CSig → ∀ (Nk Bk : ℕ → ℕ) (gs : ℕ → ℝ), (∀ k, 0 < Bk k) → (∀ k, 0 < Nk k) →
        (∀ k, Muon.PowerLaw.gammaOf (Nk k) (Bk k) ≤ gs k) →
        Tendsto (fun k => Muon.PowerLaw.gammaOf (Nk k) (Bk k)) atTop atTop →
        Tendsto (fun k => def_app_iso_vol_zero cert (gs k) CSig β (Nk k) (Nk k) (Bk k) /
            ((Nk k : ℝ) * Muon.PowerLaw.gammaOf (Nk k) (Bk k))) atTop (𝓝 (1 / 2))) := by
  let M : ℝ := max |1 - 2 * isoKminus β| |1 + 2 * isoKplus β|
  constructor
  · refine ⟨2 * M, ?_⟩
    intro γstar CSig hC1 N B hB hN hγ hγβ
    have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
    have hBr : 0 < (B : ℝ) := by exact_mod_cast hB
    have hγpos : 0 < Muon.PowerLaw.gammaOf N B := div_pos hNr hBr
    obtain ⟨-, hlo, hhi⟩ :=
      thm_app_iso_zero_ridge_ii cert γstar CSig hB hN hβ0 hβ1 hγ hC1 hγβ
    let x : ℝ := def_app_iso_vol_zero cert γstar CSig β N N B /
      ((N : ℝ) * Muon.PowerLaw.gammaOf N B) - 1 / 2
    have hx : |x| ≤ M / Muon.PowerLaw.gammaOf N B :=
      abs_le_max_abs_div hγpos hlo hhi
    have hid :
        2 * (B : ℝ) * def_app_iso_vol_zero cert γstar CSig β N N B / (N : ℝ) ^ 2 - 1 =
          2 * x := by
      dsimp [x, Muon.PowerLaw.gammaOf]
      field_simp
    rw [hid, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      2 * |x| ≤ 2 * (M / Muon.PowerLaw.gammaOf N B) :=
        mul_le_mul_of_nonneg_left hx (by norm_num)
      _ = (2 * M) * ((B : ℝ) / (N : ℝ)) := by
        dsimp [Muon.PowerLaw.gammaOf]
        field_simp
  · intro CSig hC1 Nk Bk gs hB hN hcap hgam
    have hdiff : Tendsto
        (fun k => def_app_iso_vol_zero cert (gs k) CSig β (Nk k) (Nk k) (Bk k) /
            ((Nk k : ℝ) * Muon.PowerLaw.gammaOf (Nk k) (Bk k)) - 1 / 2)
        atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := M)).div_atTop hgam)
      filter_upwards [hgam.eventually_ge_atTop (isoGammaCirc β)] with k hk
      have hNkr : 0 < (Nk k : ℝ) := by exact_mod_cast hN k
      have hBkr : 0 < (Bk k : ℝ) := by exact_mod_cast hB k
      have hγk : 0 < Muon.PowerLaw.gammaOf (Nk k) (Bk k) := div_pos hNkr hBkr
      obtain ⟨-, hlo, hhi⟩ := thm_app_iso_zero_ridge_ii cert (gs k) CSig
        (hB k) (hN k) hβ0 hβ1 (hcap k) hC1 hk
      simpa [Real.norm_eq_abs] using abs_le_max_abs_div hγk hlo hhi
    convert hdiff.add_const (1 / 2) using 1 <;> simp

end Muon.Isotropic

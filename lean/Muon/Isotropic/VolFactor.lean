import Muon.Foundations.Conventions

/-!
# The volatility factor `V_β` (`lem:app-iso-V`, Appendix F, package L-F.8)

Definitions `volK`, `volOmega`, `volFactor` transcribe `eqn:app-iso-Omega` (`section.tex` l.2095–2101)
verbatim:

```latex
\begin{equation}\label{eqn:app-iso-Omega}
\begin{gathered}
k_n\defeq\frac1{2n+1}+\frac1{2n+3},\qquad
\Omega(z)\defeq\frac4{\pi^2}\sum_{n\ge0}k_n^2\,z^{2n+1},\\
V_\bmom\defeq1+2\sum_{\ell\ge1}\Omega(\bmom^\ell)\qquad(\bmom\in(0,1)).
\end{gathered}
\end{equation}
```

Snapshot `cr-2026-10-23`. Shared objects: `Muon.sPow` (`s₂ = sPow β 2`, `Muon.sPow_two`).
Statements only; proofs `sorry` (proof cards in the result JSON).
-/

namespace Muon.Isotropic

/-- `k_n := 1/(2n+1) + 1/(2n+3)` (`eqn:app-iso-Omega`, `section.tex` l.2095–2101). -/
noncomputable def volK (n : ℕ) : ℝ := 1 / (2 * (n : ℝ) + 1) + 1 / (2 * (n : ℝ) + 3)

/-- `Ω(z) := (4/π²) ∑_{n≥0} k_n² z^(2n+1)` (`eqn:app-iso-Omega`, `section.tex` l.2095–2101). -/
noncomputable def volOmega (z : ℝ) : ℝ := 4 / Real.pi ^ 2 * ∑' n : ℕ, volK n ^ 2 * z ^ (2 * n + 1)

/-- `V_β := 1 + 2 ∑_{ℓ≥1} Ω(β^ℓ)` for `β ∈ (0,1)` (`eqn:app-iso-Omega`, `section.tex` l.2095–2101).
The index `ℓ ≥ 1` is written as `ℓ + 1` in the sum over `ℕ`. -/
noncomputable def volFactor (β : ℝ) : ℝ := 1 + 2 * ∑' ℓ : ℕ, volOmega (β ^ (ℓ + 1))

/-- Odd-index part of a `p`-th power series: the odd sum is `(1 - 2^{-p})` times the full sum. -/
private theorem odd_sum_pow_eq (p : ℕ) (hp : 1 < p) :
    ∑' n : ℕ, (1 : ℝ) / (2 * (n : ℝ) + 1) ^ p
      = (1 - 1 / 2 ^ p) * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ p := by
  have hs : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ p) :=
    Real.summable_one_div_nat_pow.mpr hp
  have hinj2 : Function.Injective (fun k : ℕ => 2 * k) := fun a b h => by
    simp only at h; omega
  have hinj1 : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b h => by
    simp only at h; omega
  have hev : ∑' k : ℕ, (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ p
      = 1 / 2 ^ p * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ p := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    push_cast
    ring
  have hsum : ∑' k : ℕ, (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ p
      + ∑' k : ℕ, (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ p
      = ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ p :=
    by
      have he : Summable (fun k : ℕ => (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ p) :=
        hs.comp_injective hinj2
      have ho : Summable (fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ p) :=
        hs.comp_injective hinj1
      exact tsum_even_add_odd (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ p) he ho
  have hodd : ∑' n : ℕ, (1 : ℝ) / (2 * (n : ℝ) + 1) ^ p
      = ∑' k : ℕ, (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ p := by
    refine tsum_congr fun n => ?_
    push_cast
    ring
  rw [hodd]
  linear_combination hsum - hev

/-- Sum over odd x of x⁻² equals π²/8, with x = 2n+1 (CARD §4; used by `lem:app-iso-V`). -/
theorem tsum_odd_inv_sq : ∑' n : ℕ, (1 : ℝ) / (2 * (n : ℝ) + 1) ^ 2 = Real.pi ^ 2 / 8 := by
  rw [odd_sum_pow_eq 2 (by norm_num), hasSum_zeta_two.tsum_eq]
  ring

/-- Sum over odd x of x⁻³ equals (7/8) ζ(3), with x = 2n+1 (CARD §4; used by `lem:app-iso-V`). -/
theorem tsum_odd_inv_cube :
    ∑' n : ℕ, (1 : ℝ) / (2 * (n : ℝ) + 1) ^ 3 = 7 / 8 * (riemannZeta 3).re := by
  have h3 : riemannZeta 3 = ∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ 3 := by
    have := zeta_nat_eq_tsum_of_gt_one (k := 3) (by norm_num)
    simpa using this
  have hre : riemannZeta 3 = ((∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 3 : ℝ) : ℂ) := by
    rw [h3, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    push_cast
    ring
  rw [odd_sum_pow_eq 3 (by norm_num), hre, Complex.ofReal_re]
  ring

/-- Telescoping: sum over odd x of 2/(x(x+2)) equals 1, with x = 2n+1
(CARD §4; used by `lem:app-iso-V`). -/
theorem tsum_odd_telescope :
    ∑' n : ℕ, (2 : ℝ) / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) = 1 := by
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, g = fun n : ℕ => 1 / (2 * (n : ℝ) + 1) := ⟨_, rfl⟩
  have hterm : ∀ n : ℕ, (2 : ℝ) / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) = g n - g (n + 1) := by
    intro n
    simp only [hg]
    push_cast
    have h1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
    have h3 : (2 * ((n : ℝ) + 1) + 1) ≠ 0 := by positivity
    field_simp
    ring
  have hnn : ∀ n : ℕ, 0 ≤ (2 : ℝ) / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) :=
    fun n => by positivity
  have hgrow : Filter.Tendsto (fun n : ℕ => 2 * (n : ℝ) + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1
      (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
  have hlim : Filter.Tendsto g Filter.atTop (nhds 0) := by
    rw [hg]
    exact tendsto_const_nhds.div_atTop hgrow
  have hpart : (fun n : ℕ => ∑ i ∈ Finset.range n,
      (2 : ℝ) / ((2 * (i : ℝ) + 1) * (2 * (i : ℝ) + 3))) = fun n => g 0 - g n := by
    funext n
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    exact Finset.sum_range_sub' g n
  have h1 : Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
      (2 : ℝ) / ((2 * (i : ℝ) + 1) * (2 * (i : ℝ) + 3))) Filter.atTop (nhds (g 0 - 0)) := by
    rw [hpart]
    exact tendsto_const_nhds.sub hlim
  have hg0 : g 0 = 1 := by simp [hg]
  rw [hg0, sub_zero] at h1
  exact ((hasSum_iff_tendsto_nat_of_nonneg hnn 1).mpr h1).tsum_eq

/-- Summability of `(2n+1)⁻²`. -/
private lemma summable_odd_inv_sq' : Summable (fun n : ℕ => (1 : ℝ) / (2 * (n : ℝ) + 1) ^ 2) := by
  have hs : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b h => by
    simp only at h; omega
  refine (hs.comp_injective hinj).congr (fun n => ?_)
  simp

/-- Summability of `(2n+3)⁻²`. -/
private lemma summable_shift_inv_sq' : Summable (fun n : ℕ => (1 : ℝ) / (2 * (n : ℝ) + 3) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) summable_odd_inv_sq'
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine one_div_le_one_div_of_le (by positivity) ?_
  nlinarith

/-- Summability of the telescoping terms `2/((2n+1)(2n+3))`. -/
private lemma summable_telescope' :
    Summable (fun n : ℕ => (2 : ℝ) / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3))) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_odd_inv_sq'.mul_left 2)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Expansion `k_n² = (2n+1)⁻² + 2/((2n+1)(2n+3)) + (2n+3)⁻²`. -/
private lemma volK_sq_eq (n : ℕ) : volK n ^ 2 =
    1 / (2 * (n : ℝ) + 1) ^ 2 + 2 / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3))
      + 1 / (2 * (n : ℝ) + 3) ^ 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have h3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
  unfold volK
  field_simp
  ring

private lemma summable_volK_sq : Summable (fun n : ℕ => volK n ^ 2) :=
  ((summable_odd_inv_sq'.add summable_telescope').add summable_shift_inv_sq').congr
    (fun n => (volK_sq_eq n).symm)

/-- Shift identity: `∑ (2n+3)⁻² = ∑ (2n+1)⁻² - 1`. -/
private lemma shift_tsum :
    ∑' n : ℕ, (1 : ℝ) / (2 * (n : ℝ) + 3) ^ 2 = ∑' n : ℕ, (1 : ℝ) / (2 * (n : ℝ) + 1) ^ 2 - 1 := by
  have h := summable_odd_inv_sq'.tsum_eq_zero_add
  have e : ∑' n : ℕ, (1 : ℝ) / (2 * (n : ℝ) + 3) ^ 2
      = ∑' n : ℕ, (1 : ℝ) / (2 * ((n + 1 : ℕ) : ℝ) + 1) ^ 2 :=
    tsum_congr (fun n => by push_cast; ring)
  have h0 : (1 : ℝ) / (2 * ((0 : ℕ) : ℝ) + 1) ^ 2 = 1 := by norm_num
  rw [e]
  linarith

/-- `∑ k_n² = π²/4`. -/
private lemma tsum_volK_sq : ∑' n : ℕ, volK n ^ 2 = Real.pi ^ 2 / 4 := by
  rw [tsum_congr volK_sq_eq,
    Summable.tsum_add (summable_odd_inv_sq'.add summable_telescope') summable_shift_inv_sq',
    Summable.tsum_add summable_odd_inv_sq' summable_telescope', shift_tsum,
    tsum_odd_telescope, tsum_odd_inv_sq]
  ring

/-- `lem:app-iso-V` (i), snapshot `cr-2026-10-23`. Statement verbatim from `sections/05b-isotropic/section.tex` l.2103–2112:

```latex
\begin{lemma}[The volatility factor]\label{lem:app-iso-V}
$\Omega(1)=1$, and for $\bmom\in(0,1)$
\[
V_\bmom=\frac4{\pi^2}\sum_{n\ge0}k_n^2\,\frac{1+\bmom^{2n+1}}{1-\bmom^{2n+1}},\qquad
1<V_\bmom<\frac1{\sw2}=\frac{1+\bmom}{1-\bmom},
\]
\[
\lim_{\bmom\uparrow1}\sw2V_\bmom=\frac14+\frac1{\pi^2}+\frac{7\zeta(3)}{2\pi^2}=0.77759\ldots .
\]
\end{lemma}
```
-/
theorem lem_app_iso_V_i : volOmega 1 = 1 := by
  unfold volOmega
  simp only [one_pow, mul_one]
  rw [tsum_volK_sq]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- `lem:app-iso-V` (ii), snapshot `cr-2026-10-23`. Statement verbatim from `sections/05b-isotropic/section.tex` l.2103–2112:

```latex
\begin{lemma}[The volatility factor]\label{lem:app-iso-V}
$\Omega(1)=1$, and for $\bmom\in(0,1)$
\[
V_\bmom=\frac4{\pi^2}\sum_{n\ge0}k_n^2\,\frac{1+\bmom^{2n+1}}{1-\bmom^{2n+1}},\qquad
1<V_\bmom<\frac1{\sw2}=\frac{1+\bmom}{1-\bmom},
\]
\[
\lim_{\bmom\uparrow1}\sw2V_\bmom=\frac14+\frac1{\pi^2}+\frac{7\zeta(3)}{2\pi^2}=0.77759\ldots .
\]
\end{lemma}
```
-/
theorem lem_app_iso_V_ii {β : ℝ} (h0 : 0 < β) (h1 : β < 1) :
    volFactor β = 4 / Real.pi ^ 2 * ∑' n : ℕ, volK n ^ 2 * ((1 + β ^ (2 * n + 1)) / (1 - β ^ (2 * n + 1))) := by
  have hβ0 : 0 ≤ β := h0.le
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℕ → ℝ, G = fun ℓ n => volK n ^ 2 * (β ^ (ℓ + 1)) ^ (2 * n + 1) :=
    ⟨_, rfl⟩
  have hGdef : ∀ ℓ n, G ℓ n = volK n ^ 2 * (β ^ (ℓ + 1)) ^ (2 * n + 1) := fun ℓ n => by
    rw [hG]
  have hKnn : ∀ n : ℕ, 0 ≤ volK n := fun n => by unfold volK; positivity
  have hKle : ∀ n : ℕ, volK n ≤ 2 := by
    intro n
    unfold volK
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have a1 : 1 / (2 * (n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have a2 : 1 / (2 * (n : ℝ) + 3) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    linarith
  have hGbound : ∀ ℓ n : ℕ, G ℓ n ≤ 4 * (β ^ ℓ * β ^ n) := by
    intro ℓ n
    rw [hGdef]
    have hexp : β ^ ((ℓ + 1) * (2 * n + 1)) ≤ β ^ (ℓ + n) :=
      pow_le_pow_of_le_one hβ0 h1.le (by nlinarith)
    have hpow : (β ^ (ℓ + 1)) ^ (2 * n + 1) = β ^ ((ℓ + 1) * (2 * n + 1)) :=
      (pow_mul β (ℓ + 1) (2 * n + 1)).symm
    have hsq : volK n ^ 2 ≤ 4 := by nlinarith [hKle n, hKnn n]
    have hp0 : 0 ≤ (β ^ (ℓ + 1)) ^ (2 * n + 1) := pow_nonneg (pow_nonneg hβ0 _) _
    calc volK n ^ 2 * (β ^ (ℓ + 1)) ^ (2 * n + 1)
        ≤ 4 * (β ^ (ℓ + 1)) ^ (2 * n + 1) := mul_le_mul_of_nonneg_right hsq hp0
      _ ≤ 4 * β ^ (ℓ + n) := by
          rw [hpow]; exact mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ = 4 * (β ^ ℓ * β ^ n) := by rw [pow_add]
  have hsumG : Summable (Function.uncurry G) := by
    have hgeo := summable_geometric_of_lt_one hβ0 h1
    have hprod : Summable (fun p : ℕ × ℕ => 4 * (β ^ p.1 * β ^ p.2)) :=
      (Summable.mul_of_nonneg hgeo hgeo (fun n => pow_nonneg hβ0 n)
        (fun n => pow_nonneg hβ0 n)).mul_left 4
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => hGbound p.1 p.2) hprod
    change 0 ≤ G p.1 p.2
    rw [hGdef]
    exact mul_nonneg (sq_nonneg _) (pow_nonneg (pow_nonneg hβ0 _) _)
  have hsumN' : Summable (fun n : ℕ => ∑' ℓ : ℕ, G ℓ n) := hsumG.prod_symm.prod
  have hcomm : ∑' ℓ : ℕ, ∑' n : ℕ, G ℓ n = ∑' n : ℕ, ∑' ℓ : ℕ, G ℓ n :=
    hsumG.tsum_comm.symm
  have hOmega : ∀ z : ℝ, volOmega z = 4 / Real.pi ^ 2 * ∑' n : ℕ, volK n ^ 2 * z ^ (2 * n + 1) :=
    fun z => rfl
  have e1 : ∑' ℓ : ℕ, volOmega (β ^ (ℓ + 1)) = 4 / Real.pi ^ 2 * ∑' n : ℕ, ∑' ℓ : ℕ, G ℓ n := by
    calc ∑' ℓ : ℕ, volOmega (β ^ (ℓ + 1))
        = ∑' ℓ : ℕ, 4 / Real.pi ^ 2 * ∑' n : ℕ, G ℓ n :=
          tsum_congr (fun ℓ => by
            rw [hOmega]
            congr 1
            exact tsum_congr (fun n => (hGdef ℓ n).symm))
      _ = 4 / Real.pi ^ 2 * ∑' ℓ : ℕ, ∑' n : ℕ, G ℓ n := tsum_mul_left
      _ = 4 / Real.pi ^ 2 * ∑' n : ℕ, ∑' ℓ : ℕ, G ℓ n := by rw [hcomm]
  have hV : volFactor β = 1 + 2 * (4 / Real.pi ^ 2 * ∑' n : ℕ, ∑' ℓ : ℕ, G ℓ n) := by
    unfold volFactor
    rw [e1]
  have hone : (1 : ℝ) = 4 / Real.pi ^ 2 * ∑' n : ℕ, volK n ^ 2 := by
    have h := lem_app_iso_V_i
    rw [hOmega] at h
    simp only [one_pow, mul_one] at h
    exact h.symm
  have hS : ∀ n : ℕ, volK n ^ 2 * ((1 + β ^ (2 * n + 1)) / (1 - β ^ (2 * n + 1)))
      = volK n ^ 2 + 2 * ∑' ℓ : ℕ, G ℓ n := by
    intro n
    have hx0 : 0 < β ^ (2 * n + 1) := pow_pos h0 _
    have hx1 : β ^ (2 * n + 1) < 1 := pow_lt_one₀ h0.le h1 (by omega)
    have hne : (1 - β ^ (2 * n + 1)) ≠ 0 := (sub_pos.mpr hx1).ne'
    have hterm : ∀ ℓ : ℕ, (β ^ (ℓ + 1)) ^ (2 * n + 1) = (β ^ (2 * n + 1)) ^ ℓ * β ^ (2 * n + 1) :=
      fun ℓ => by ring
    have hsum_l : ∑' ℓ : ℕ, (β ^ (ℓ + 1)) ^ (2 * n + 1)
        = β ^ (2 * n + 1) / (1 - β ^ (2 * n + 1)) := by
      rw [tsum_congr hterm, tsum_mul_right,
        tsum_geometric_of_lt_one (pow_nonneg hβ0 _) hx1]
      ring
    have hGn : ∑' ℓ : ℕ, G ℓ n = volK n ^ 2 * (β ^ (2 * n + 1) / (1 - β ^ (2 * n + 1))) := by
      rw [← hsum_l, ← tsum_mul_left]
      exact tsum_congr (fun ℓ => hGdef ℓ n)
    rw [hGn]
    field_simp
    ring
  rw [hV, tsum_congr hS, Summable.tsum_add summable_volK_sq (hsumN'.mul_left 2), tsum_mul_left]
  linear_combination hone

/-- `lem:app-iso-V` (iii), snapshot `cr-2026-10-23`. Statement verbatim from `sections/05b-isotropic/section.tex` l.2103–2112:

```latex
\begin{lemma}[The volatility factor]\label{lem:app-iso-V}
$\Omega(1)=1$, and for $\bmom\in(0,1)$
\[
V_\bmom=\frac4{\pi^2}\sum_{n\ge0}k_n^2\,\frac{1+\bmom^{2n+1}}{1-\bmom^{2n+1}},\qquad
1<V_\bmom<\frac1{\sw2}=\frac{1+\bmom}{1-\bmom},
\]
\[
\lim_{\bmom\uparrow1}\sw2V_\bmom=\frac14+\frac1{\pi^2}+\frac{7\zeta(3)}{2\pi^2}=0.77759\ldots .
\]
\end{lemma}
```
-/
theorem lem_app_iso_V_iii {β : ℝ} (h0 : 0 < β) (h1 : β < 1) :
    1 < volFactor β ∧ volFactor β < 1 / sPow β 2 ∧ 1 / sPow β 2 = (1 + β) / (1 - β) := by
  have hs2 : 1 / sPow β 2 = (1 + β) / (1 - β) := by
    rw [sPow_two h0.le h1, one_div_div]
  have hx0 : ∀ n : ℕ, 0 < β ^ (2 * n + 1) := fun n => pow_pos h0 _
  have hx1 : ∀ n : ℕ, β ^ (2 * n + 1) < 1 := fun n => pow_lt_one₀ h0.le h1 (by omega)
  have hV := lem_app_iso_V_ii h0 h1
  have hsumK : ∑' n : ℕ, volK n ^ 2 = Real.pi ^ 2 / 4 := tsum_volK_sq
  have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
  have hpi : (0 : ℝ) < 4 / Real.pi ^ 2 := by positivity
  have hKpos : ∀ n : ℕ, 0 < volK n := fun n => by unfold volK; positivity
  have hf1 : ∀ n : ℕ, 1 ≤ (1 + β ^ (2 * n + 1)) / (1 - β ^ (2 * n + 1)) := by
    intro n
    rw [le_div_iff₀ (sub_pos.mpr (hx1 n))]
    linarith [hx0 n]
  have hmono : ∀ x y : ℝ, 0 < x → x < y → y < 1 →
      (1 + x) / (1 - x) < (1 + y) / (1 - y) := by
    intro x y hx hxy hy
    rw [div_lt_div_iff₀ (sub_pos.mpr (by linarith)) (sub_pos.mpr hy)]
    nlinarith
  have hle : ∀ n : ℕ, β ^ (2 * n + 1) ≤ β := fun n => by
    have := pow_le_pow_of_le_one h0.le h1.le (show 1 ≤ 2 * n + 1 by omega)
    simpa using this
  have hfβ : ∀ n : ℕ, (1 + β ^ (2 * n + 1)) / (1 - β ^ (2 * n + 1)) ≤ (1 + β) / (1 - β) := by
    intro n
    rcases eq_or_lt_of_le (hle n) with h | h
    · rw [h]
    · exact (hmono _ _ (hx0 n) h h1).le
  have hlt3 : β ^ (2 * 1 + 1) < β := by
    norm_num
    nlinarith [mul_pos (mul_pos h0 (sub_pos.mpr h1)) (by linarith : (0:ℝ) < 1 + β)]
  have hstrict : (1 + β ^ (2 * 1 + 1)) / (1 - β ^ (2 * 1 + 1)) < (1 + β) / (1 - β) :=
    hmono _ _ (hx0 1) hlt3 h1
  have hA : Summable (fun n : ℕ => volK n ^ 2 * ((1 + β ^ (2 * n + 1)) / (1 - β ^ (2 * n + 1)))) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (sq_nonneg _) (by linarith [hf1 n]))
      (fun n => mul_le_mul_of_nonneg_left (hfβ n) (sq_nonneg _))
      (summable_volK_sq.mul_right _)
  refine ⟨?_, ?_, hs2⟩
  · have hlt : ∑' n : ℕ, volK n ^ 2 < ∑' n : ℕ, volK n ^ 2 * ((1 + β ^ (2 * n + 1)) / (1 - β ^ (2 * n + 1))) := by
      refine Summable.tsum_lt_tsum (i := 1) (fun n => le_mul_of_one_le_right (sq_nonneg _) (hf1 n)) ?_ summable_volK_sq hA
      have h1lt : (1 : ℝ) < (1 + β ^ (2 * 1 + 1)) / (1 - β ^ (2 * 1 + 1)) :=
        (one_lt_div (sub_pos.mpr (hx1 1))).mpr (by linarith [hx0 1])
      exact lt_of_eq_of_lt (mul_one _).symm (mul_lt_mul_of_pos_left h1lt (pow_pos (hKpos 1) 2))
    rw [hV]
    calc (1 : ℝ) = 4 / Real.pi ^ 2 * ∑' n : ℕ, volK n ^ 2 := by rw [hsumK]; field_simp
      _ < 4 / Real.pi ^ 2 * ∑' n : ℕ, volK n ^ 2 * ((1 + β ^ (2 * n + 1)) / (1 - β ^ (2 * n + 1))) :=
        mul_lt_mul_of_pos_left hlt hpi
  · have hB : ∑' n : ℕ, volK n ^ 2 * ((1 + β) / (1 - β)) = Real.pi ^ 2 / 4 * ((1 + β) / (1 - β)) := by
      rw [tsum_mul_right, hsumK]
    have hlt2 : ∑' n : ℕ, volK n ^ 2 * ((1 + β ^ (2 * n + 1)) / (1 - β ^ (2 * n + 1)))
        < ∑' n : ℕ, volK n ^ 2 * ((1 + β) / (1 - β)) := by
      refine Summable.tsum_lt_tsum (i := 1) (fun n => mul_le_mul_of_nonneg_left (hfβ n) (sq_nonneg _)) ?_ hA
        (summable_volK_sq.mul_right _)
      exact mul_lt_mul_of_pos_left hstrict (pow_pos (hKpos 1) 2)
    rw [hV, hs2]
    calc 4 / Real.pi ^ 2 * ∑' n : ℕ, volK n ^ 2 * ((1 + β ^ (2 * n + 1)) / (1 - β ^ (2 * n + 1)))
        < 4 / Real.pi ^ 2 * (Real.pi ^ 2 / 4 * ((1 + β) / (1 - β))) := by
          rw [← hB]; exact mul_lt_mul_of_pos_left hlt2 hpi
      _ = (1 + β) / (1 - β) := by field_simp

/-- Rational identity: `(1-β)/(1+β) · (1+β^m)/(1-β^m) = (1+β^m)/(1+β) · (∑_{i<m} β^i)⁻¹`. -/
private lemma iso_term_eq (β : ℝ) (h0 : 0 < β) (h1 : β < 1) (m : ℕ) (hm : 0 < m) :
    (1 - β) / (1 + β) * ((1 + β ^ m) / (1 - β ^ m))
      = (1 + β ^ m) / (1 + β) * (∑ i ∈ Finset.range m, β ^ i)⁻¹ := by
  have hxm : β ^ m < 1 := pow_lt_one₀ h0.le h1 hm.ne'
  have hxm' : 1 - β ^ m ≠ 0 := (sub_pos.mpr hxm).ne'
  have hxm1 : β ^ m - 1 ≠ 0 := (sub_neg.mpr hxm).ne
  have h1b : 1 + β ≠ 0 := (by linarith : (0 : ℝ) < 1 + β).ne'
  rw [geom_sum_eq h1.ne m, inv_div]
  field_simp
  ring

/-- Bounds `0 ≤ (1+β^m)/(1+β) · (∑_{i<m} β^i)⁻¹ ≤ 2` for `β ∈ (0,1)`. -/
private lemma iso_G_bounds (β : ℝ) (h0 : 0 < β) (h1 : β < 1) (m : ℕ) (hm : 0 < m) :
    0 ≤ (1 + β ^ m) / (1 + β) * (∑ i ∈ Finset.range m, β ^ i)⁻¹ ∧
      (1 + β ^ m) / (1 + β) * (∑ i ∈ Finset.range m, β ^ i)⁻¹ ≤ 2 := by
  have hS1 : 1 ≤ ∑ i ∈ Finset.range m, β ^ i := by
    have h := Finset.single_le_sum (f := fun i : ℕ => β ^ i) (s := Finset.range m)
      (fun i _ => pow_nonneg h0.le i) (Finset.mem_range.mpr hm)
    simpa using h
  have hB0 : 0 ≤ (∑ i ∈ Finset.range m, β ^ i)⁻¹ := inv_nonneg.mpr (by linarith)
  have hB1 : (∑ i ∈ Finset.range m, β ^ i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hS1
  have hA0 : 0 ≤ (1 + β ^ m) / (1 + β) :=
    div_nonneg (by linarith [pow_nonneg h0.le m]) (by linarith)
  have hA1 : (1 + β ^ m) / (1 + β) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    have : β ^ m ≤ 1 := pow_le_one₀ h0.le h1.le
    linarith
  refine ⟨mul_nonneg hA0 hB0, ?_⟩
  calc (1 + β ^ m) / (1 + β) * (∑ i ∈ Finset.range m, β ^ i)⁻¹ ≤ 2 * 1 :=
        mul_le_mul hA1 hB1 hB0 (by norm_num)
    _ = 2 := by norm_num

/-- Pointwise limit at `β ↑ 1`: `(1+β^m)/(1+β) · (∑_{i<m} β^i)⁻¹ → 1/m`, `m = 2n+1`. -/
private lemma iso_G_tendsto (n : ℕ) :
    Filter.Tendsto (fun β : ℝ => (1 + β ^ (2 * n + 1)) / (1 + β) * (∑ i ∈ Finset.range (2 * n + 1), β ^ i)⁻¹)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (1 / (2 * (n : ℝ) + 1))) := by
  have hc : ContinuousAt (fun β : ℝ => (1 + β ^ (2 * n + 1)) / (1 + β)
      * (∑ i ∈ Finset.range (2 * n + 1), β ^ i)⁻¹) 1 := by
    refine ContinuousAt.mul (ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num))
      (ContinuousAt.inv₀ (by fun_prop) ?_)
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, mul_one, ne_eq]
    exact ne_of_gt (by positivity)
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
  convert h using 2
  norm_num [Finset.sum_const, Finset.card_range]

/-- The identity `sPow β 2 · V_β = (4/π²) ∑ k_n² · (1+β^m)/(1+β) · (∑_{i<m} β^i)⁻¹`. -/
private lemma iso_ident (β : ℝ) (h0 : 0 < β) (h1 : β < 1) :
    sPow β 2 * volFactor β = 4 / Real.pi ^ 2 * ∑' n : ℕ, volK n ^ 2
      * ((1 + β ^ (2 * n + 1)) / (1 + β) * (∑ i ∈ Finset.range (2 * n + 1), β ^ i)⁻¹) := by
  have hterm : ∀ n : ℕ, volK n ^ 2
      * ((1 + β ^ (2 * n + 1)) / (1 + β) * (∑ i ∈ Finset.range (2 * n + 1), β ^ i)⁻¹)
      = (1 - β) / (1 + β) * (volK n ^ 2 * ((1 + β ^ (2 * n + 1)) / (1 - β ^ (2 * n + 1)))) := by
    intro n
    rw [← iso_term_eq β h0 h1 (2 * n + 1) (by omega)]
    ring
  rw [sPow_two h0.le h1, lem_app_iso_V_ii h0 h1, tsum_congr hterm, tsum_mul_left]
  ring

/-- Value of the limit series: `∑ k_n² /(2n+1) = 7ζ(3)/8 + π²/16 + 1/4` (partial fractions). -/
private lemma iso_tsum_value :
    ∑' n : ℕ, volK n ^ 2 * (1 / (2 * (n : ℝ) + 1))
      = 7 / 8 * (riemannZeta 3).re + Real.pi ^ 2 / 16 + 1 / 4 := by
  have s1 : Summable (fun n : ℕ => (1 : ℝ) / (2 * (n : ℝ) + 1) ^ 3) := by
    have hs : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 3) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b h => by
      simp only at h; omega
    refine (hs.comp_injective hinj).congr (fun n => ?_)
    simp
  have H1 : HasSum (fun n : ℕ => (1 : ℝ) / (2 * (n : ℝ) + 1) ^ 3) (7 / 8 * (riemannZeta 3).re) := by
    have h := s1.hasSum
    rwa [tsum_odd_inv_cube] at h
  have H2 : HasSum (fun n : ℕ => (1 : ℝ) / (2 * (n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 8) := by
    have h := summable_odd_inv_sq'.hasSum
    rwa [tsum_odd_inv_sq] at h
  have H3 : HasSum (fun n : ℕ => (2 : ℝ) / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3))) 1 := by
    have h := summable_telescope'.hasSum
    rwa [tsum_odd_telescope] at h
  have H4 : HasSum (fun n : ℕ => (1 : ℝ) / (2 * (n : ℝ) + 3) ^ 2) (Real.pi ^ 2 / 8 - 1) := by
    have h := summable_shift_inv_sq'.hasSum
    rwa [shift_tsum, tsum_odd_inv_sq] at h
  have hpt : ∀ n : ℕ, volK n ^ 2 * (1 / (2 * (n : ℝ) + 1))
      = ((1 : ℝ) / (2 * (n : ℝ) + 1) ^ 3 + (1 : ℝ) / (2 * (n : ℝ) + 1) ^ 2)
        - (1 / 4 * ((2 : ℝ) / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)))
          + 1 / 2 * ((1 : ℝ) / (2 * (n : ℝ) + 3) ^ 2)) := by
    intro n
    have h1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    have h3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
    unfold volK
    field_simp
    ring
  rw [tsum_congr hpt]
  have H := (H1.add H2).sub ((H3.mul_left (1 / 4)).add (H4.mul_left (1 / 2)))
  refine H.tsum_eq.trans ?_
  ring

/-- `lem:app-iso-V` (iv), snapshot `cr-2026-10-23`. Statement verbatim from `sections/05b-isotropic/section.tex` l.2103–2112:

```latex
\begin{lemma}[The volatility factor]\label{lem:app-iso-V}
$\Omega(1)=1$, and for $\bmom\in(0,1)$
\[
V_\bmom=\frac4{\pi^2}\sum_{n\ge0}k_n^2\,\frac{1+\bmom^{2n+1}}{1-\bmom^{2n+1}},\qquad
1<V_\bmom<\frac1{\sw2}=\frac{1+\bmom}{1-\bmom},
\]
\[
\lim_{\bmom\uparrow1}\sw2V_\bmom=\frac14+\frac1{\pi^2}+\frac{7\zeta(3)}{2\pi^2}=0.77759\ldots .
\]
\end{lemma}
```
-/
theorem lem_app_iso_V_iv :
    Filter.Tendsto (fun β : ℝ => sPow β 2 * volFactor β) (nhdsWithin 1 (Set.Iio 1))
      (nhds (1 / 4 + 1 / Real.pi ^ 2 + 7 * (riemannZeta 3).re / (2 * Real.pi ^ 2))) := by
  have hval : (4 / Real.pi ^ 2) * (7 / 8 * (riemannZeta 3).re + Real.pi ^ 2 / 16 + 1 / 4)
      = 1 / 4 + 1 / Real.pi ^ 2 + 7 * (riemannZeta 3).re / (2 * Real.pi ^ 2) := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  have hdom : Filter.Tendsto
      (fun β : ℝ => ∑' n : ℕ, volK n ^ 2
        * ((1 + β ^ (2 * n + 1)) / (1 + β) * (∑ i ∈ Finset.range (2 * n + 1), β ^ i)⁻¹))
      (nhdsWithin 1 (Set.Iio 1))
      (nhds (∑' n : ℕ, volK n ^ 2 * (1 / (2 * (n : ℝ) + 1)))) :=
    tendsto_tsum_of_dominated_convergence (bound := fun n : ℕ => 2 * volK n ^ 2)
      (summable_volK_sq.mul_left 2)
      (fun n => (iso_G_tendsto n).const_mul (volK n ^ 2))
      (by
        filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with β hβ
        intro n
        obtain ⟨hb0, hb1⟩ := hβ
        have hG := iso_G_bounds β hb0 hb1 (2 * n + 1) (by omega)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hG.1)]
        have := mul_le_mul_of_nonneg_left hG.2 (sq_nonneg (volK n))
        linarith)
  have key : Filter.Tendsto
      (fun β : ℝ => 4 / Real.pi ^ 2 * ∑' n : ℕ, volK n ^ 2
        * ((1 + β ^ (2 * n + 1)) / (1 + β) * (∑ i ∈ Finset.range (2 * n + 1), β ^ i)⁻¹))
      (nhdsWithin 1 (Set.Iio 1))
      (nhds (4 / Real.pi ^ 2 * (7 / 8 * (riemannZeta 3).re + Real.pi ^ 2 / 16 + 1 / 4))) := by
    rw [← iso_tsum_value]
    exact hdom.const_mul (4 / Real.pi ^ 2)
  rw [hval] at key
  refine key.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with β hβ
  exact (iso_ident β hβ.1 hβ.2).symm

end Muon.Isotropic

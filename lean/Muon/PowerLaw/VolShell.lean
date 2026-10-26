import Muon.PowerLaw.VolKernel
import Muon.PowerLaw.Profiles
import Muon.PowerLaw.DriftAsymptotics

/-!
# Appendix G: proof-internal steps of `thm:app-pl-volatility`(i) and `lem:app-pl-vector` (task L-G.7b)

Snapshot `cr-2026-10-23`. Decomposition interface: no paper labels. Each sorried theorem is an
intermediate claim that the paper's proof of `thm:app-pl-volatility`(i) (`section.tex` l.2206-2266) or of
`lem:app-pl-vector` (l.1948-2001) states, so that the parked targets
`thm_app_pl_volatility_i_part` (P-G.7.P1, `VolBulk`) and `lem_app_pl_vector` (P-G.8.P1, `VolMeso`)
become short assemblies.

Conventions.
* Regime sequences follow `VolKernel`/`VolMeso`: constants are chosen before the sequence
  (`∃ C, ∀ N B c, assum_app_pl_regime ... → ∀ᶠ n, ...`) for the uniform bounds, and a fixed regime `R` with
  row/lag sequences is used for the limits.
* The source normalizes `c_N = 1` by `lem:app-pl-amplitude`. All objects below (`Wpart`, `partF`, `calV`, `bCoef`)
  are amplitude invariant, so the statements are made for general `c n`.
* Finiteness is carried by `Integrable`/`IntegrableOn` conjuncts, not by Bochner junk values.
* `ϑ_N` bounds are stated for `|thetaN|`, which is what a majorant needs (the source writes `ϑ_N ≤ ...`).
-/

set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology Set Asymptotics

noncomputable section

namespace Muon.PowerLaw

/-! ## Objects -/

/-! ### Definitions moved from `VolMeso` (task L-G.7b, import-cycle fix; unchanged) -/

/-- The 1-based row number `i + 1` of the row `i : Fin N` (the convention of `vPart`, `plSpec`). -/
def rowIdx {N : ℕ} (i : Fin N) : ℝ := ((i : ℕ) : ℝ) + 1

/-- The row fraction `x = i/N` of the source (`rowIdx i / N`). -/
def rowFrac {N : ℕ} (i : Fin N) : ℝ := rowIdx i / (N : ℝ)

/-- `eqn:app-pl-b` (`b_{i,N}`; snapshot `cr-2026-10-23`). The defining paragraph, verbatim from
`sections/06-power-law/section.tex` (l.1926–1937), which also defines `𝒥_i` and `𝒱_i(g)`:

\paragraph{The mesoscopic crossover below and at one.}
Let $0<\alpha\le1$, let $i\to\infty$ with $x\defeq i/N\to0$, and put
\begin{equation}\label{eqn:app-pl-b}
b_{i,N}\defeq\frac{\sqrt\gamma\,x^{\alpha/2}\,\Psi_\alpha(x)}{c_0},\qquad
b_{i,N}^2\sim\begin{cases}\gamma x^\alpha\big[\log(x^{-\alpha})\big]^2/(1-\alpha),&\alpha<1,\\ \frac49\gamma x\big[\log(1/x)\big]^3,&\alpha=1,\end{cases}
\end{equation}
the equivalence by \cref{lem:app-pl-Psi}. Write $b=b_{i,N}$ and
\[
\mathcal J_i(m)\defeq\frac{\sqrt{\mu_i\Lambda_N(m)}}{\sqrt m\,(1+\mu_i\Lambda_N(m))}\sqrt{1-\frac m\gamma}=\frac{\mathcal B_i(m)}{\sqrt{\gamma\mu_i}},\qquad
\mathcal V_i(g)\defeq\frac1\pi\int_0^\gamma W_i(m)\,\mathcal Z_g(Q_m)\,\dif m ,
\]
so that $W_i=\mathcal J_i\vartheta_N$ and $\mathfrak v^{\mathrm{flat}}_i=\EE\,\mathcal V_i(g)^2$.
-/
def bCoef (α : ℝ) (B : ℕ) {N : ℕ} (i : Fin N) : ℝ :=
  Real.sqrt (gammaOf N B) * rowFrac i ^ (α / 2) * profPsi α (rowFrac i) / c0

/-- `𝒱_i(g) = (1/π) ∫_0^γ W_i(m) 𝒵_g(Q_m) dm` (`section.tex` l.1933–1934, in the paragraph of
`lem:app-pl-vector`). Reuses `Wpart` and `Zg`. -/
def calV (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (g : ℝ) : ℝ :=
  (Real.pi)⁻¹ * ∫ m in Ioo 0 (gammaOf N B), Wpart β B μ i m * Zg β g (Qm β m)

/-- The part of `𝒱_i(g)` over `δ < m < M`, as used in the second claim of `lem:app-pl-vector`. -/
def calVpart (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (δ M g : ℝ) : ℝ :=
  (Real.pi)⁻¹ * ∫ m in Ioo δ M, Wpart β B μ i m * Zg β g (Qm β m)

/-- The `L²(gaussianReal 0 1)` norm of a real function of `g`. The integrals are guarded by the
`Integrable` conjuncts of the statements that use it. -/
def l2Norm (f : ℝ → ℝ) : ℝ := Real.sqrt (∫ g, (f g) ^ 2 ∂(gaussianReal 0 1))


/-! ### New objects -/

/-- `g_i(m) = √(f_i(m)(1-f_i(m))) √((γ-m)/m)` (snapshot `cr-2026-10-23`; task L-G.7b; proof of `thm:app-pl-volatility`(i), `section.tex` l.2208). -/
def gRow (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (m : ℝ) : ℝ :=
  Real.sqrt (partF B μ i m * (1 - partF B μ i m)) * Real.sqrt ((gammaOf N B - m) / m)

/-- `𝒥_i(m) = √(μ_iΛ_N(m)) / (√m (1+μ_iΛ_N(m))) √(1-m/γ)` (snapshot `cr-2026-10-23`; task L-G.7b; paragraph before `lem:app-pl-vector`, `section.tex` l.1932). -/
def Jrow (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (m : ℝ) : ℝ :=
  Real.sqrt (μ i * partLam B μ m) / (Real.sqrt m * (1 + μ i * partLam B μ m)) *
    Real.sqrt (1 - m / gammaOf N B)

/-- `A_x(p) = √(f_x(p)(1-f_x(p))(1-p)/p)` (snapshot `cr-2026-10-23`; task L-G.7b; proof of `lem:app-pl-matching`, `section.tex` l.2095). -/
def profA (α x p : ℝ) : ℝ := Real.sqrt (profF α x p * (1 - profF α x p) * (1 - p) / p)

/-- `t(p,q) = (V_q p - V_p q)/(V_q - V_p)` (snapshot `cr-2026-10-23`; task L-G.7b; `section.tex` l.2096; second form). -/
def profTc (α p q : ℝ) : ℝ := (contV α q * p - contV α p * q) / (contV α q - contV α p)

/-- `Δ_c(p,q) = (1-p)(1 - t(p,q)/q)` (snapshot `cr-2026-10-23`; task L-G.7b; `section.tex` l.2102). -/
def profDeltaC (α p q : ℝ) : ℝ := (1 - p) * (1 - profTc α p q / q)

/-- The majorant `γ⁻¹ g_i(m₁) g_i(m₂) |ϑ_N(m₁)| |ϑ_N(m₂)| 𝖣_ℓ` (snapshot `cr-2026-10-23`; task L-G.7b; `section.tex` l.2237-2238). -/
def lagMajorant (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (ℓ : ℤ) (m₁ m₂ : ℝ) : ℝ :=
  (gammaOf N B)⁻¹ * gRow B μ i m₁ * gRow B μ i m₂ * |thetaN β B μ m₁| * |thetaN β B μ m₂| *
    |DLag β (Qm β m₁) (Qm β m₂) ℓ|

/-- `B_i^{[M]} = ∫_M^γ 𝒥_i dm` (snapshot `cr-2026-10-23`; task L-G.7b; `section.tex` l.1949). -/
def tailMass (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (M : ℝ) : ℝ :=
  ∫ m in Ioo M (gammaOf N B), Jrow B μ i m

/-! ## Algebraic identities -/

/-- `W_i = γ^{-1/2} g_i ϑ_N` (task L-G.7b; proof step of `thm:app-pl-volatility`(i), l.2207-2208; snapshot cr-2026-10-23). -/
theorem Wpart_eq_gRow (β : ℝ) (B N : ℕ) (hN : 0 < N) (hB : 0 < B) (μ : Fin N → ℝ) (i : Fin N)
    (hμ : 0 < μ i) (m : ℝ) (hm : m ∈ Ioo 0 (gammaOf N B)) (hΛ : 0 < partLam B μ m) :
    Wpart β B μ i m = (Real.sqrt (gammaOf N B))⁻¹ * gRow B μ i m * thetaN β B μ m := by
  obtain ⟨hm0, hmγ⟩ := hm
  have hγ : 0 < gammaOf N B := by
    unfold gammaOf
    exact div_pos (by exact_mod_cast hN) (by exact_mod_cast hB)
  have hμΛ : 0 < μ i * partLam B μ m := mul_pos hμ hΛ
  have hden : 0 < 1 + μ i * partLam B μ m := by linarith
  have h1 : Real.sqrt (partF B μ i m * (1 - partF B μ i m)) =
      Real.sqrt (μ i * partLam B μ m) / (1 + μ i * partLam B μ m) := by
    have hf : partF B μ i m * (1 - partF B μ i m) =
        (Real.sqrt (μ i * partLam B μ m) / (1 + μ i * partLam B μ m)) ^ 2 := by
      unfold partF
      rw [div_pow, Real.sq_sqrt hμΛ.le]
      field_simp
      ring
    rw [hf, Real.sqrt_sq (div_nonneg (Real.sqrt_nonneg _) hden.le)]
  have hq : 0 ≤ 1 - m / gammaOf N B := by
    have := (div_le_one hγ).2 hmγ.le
    linarith
  have h2 : Real.sqrt ((gammaOf N B - m) / m) =
      Real.sqrt (gammaOf N B) * Real.sqrt (1 - m / gammaOf N B) / Real.sqrt m := by
    have e : (gammaOf N B - m) / m = gammaOf N B * (1 - m / gammaOf N B) / m := by
      field_simp
    rw [e, Real.sqrt_div (mul_nonneg hγ.le hq), Real.sqrt_mul hγ.le]
  have hsγ : 0 < Real.sqrt (gammaOf N B) := Real.sqrt_pos.2 hγ
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
  unfold Wpart gRow
  rw [h1, h2]
  field_simp

/-- `W_i 𝒵_g = 𝒥_i (E ϑ_N) 𝒜_g` (task L-G.7b; proof step of `lem:app-pl-vector`, l.1949-1950; snapshot cr-2026-10-23). -/
theorem Wpart_mul_Zg_factor (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (m g : ℝ)
    (hE : Efun β m ≠ 0) :
    Wpart β B μ i m * Zg β g (Qm β m) = Jrow B μ i m * (Efun β m * thetaN β B μ m) * Ag β g m := by
  have hW : Wpart β B μ i m = Jrow B μ i m * thetaN β B μ m := by
    unfold Wpart Jrow
    ring
  rw [hW, Ag]
  field_simp

/-- `𝒥_i = 𝓑_i / √(γ μ_i)` (task L-G.7b; paragraph before `lem:app-pl-vector`, l.1932-1933; snapshot cr-2026-10-23). -/
theorem Jrow_eq_partBfun (B N : ℕ) (hN : 0 < N) (hB : 0 < B) (μ : Fin N → ℝ) (i : Fin N)
    (hμ : 0 < μ i) (m : ℝ) (hm : m ∈ Ioo 0 (gammaOf N B)) (hΛ : 0 < partLam B μ m) :
    Jrow B μ i m = partBfun B μ i m / Real.sqrt (gammaOf N B * μ i) := by
  obtain ⟨hm0, hmγ⟩ := hm
  have hγ : 0 < gammaOf N B := by
    unfold gammaOf
    exact div_pos (by exact_mod_cast hN) (by exact_mod_cast hB)
  have hγm : 0 < gammaOf N B - m := by linarith
  have hden : 0 < 1 + partLam B μ m * μ i := by
    have := mul_pos hΛ hμ
    linarith
  have s1 : Real.sqrt (1 - m / gammaOf N B) =
      Real.sqrt (gammaOf N B - m) / Real.sqrt (gammaOf N B) := by
    have e : 1 - m / gammaOf N B = (gammaOf N B - m) / gammaOf N B := by
      field_simp
    rw [e, Real.sqrt_div hγm.le]
  have s2 : Real.sqrt ((gammaOf N B - m) / (m * partLam B μ m)) =
      Real.sqrt (gammaOf N B - m) / (Real.sqrt m * Real.sqrt (partLam B μ m)) := by
    rw [Real.sqrt_div hγm.le, Real.sqrt_mul hm0.le]
  have s3 : Real.sqrt (μ i * partLam B μ m) = Real.sqrt (μ i) * Real.sqrt (partLam B μ m) :=
    Real.sqrt_mul hμ.le _
  have s4 : Real.sqrt (gammaOf N B * μ i) = Real.sqrt (gammaOf N B) * Real.sqrt (μ i) :=
    Real.sqrt_mul hγ.le _
  have hsγ : 0 < Real.sqrt (gammaOf N B) := Real.sqrt_pos.2 hγ
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
  have hsμ : 0 < Real.sqrt (μ i) := Real.sqrt_pos.2 hμ
  have hsΛ : 0 < Real.sqrt (partLam B μ m) := Real.sqrt_pos.2 hΛ
  unfold Jrow partBfun partF
  rw [s1, s2, s3, s4]
  field_simp
  rw [Real.sq_sqrt hμ.le, Real.sq_sqrt hΛ.le]

/-- Private: `contV` is a right inverse of `contS` with positive values on `(0,1)`. -/
private lemma vs_contV_spec {α p : ℝ} (hα : 0 < α) (hp : p ∈ Ioo (0:ℝ) 1) :
    0 < contV α p ∧ contS α (contV α p) = p := by
  have h : ∃ a ∈ Ioi (0:ℝ), contS α a = p := (def_app_pl_profiles_S_bij hα).2.surjOn hp
  exact ⟨Set.mem_Ioi.1 (Function.invFunOn_mem h), Function.invFunOn_eq h⟩

/-- Private: `contV` is strictly increasing on `(0,1)`. -/
private lemma vs_contV_lt {α p q : ℝ} (hα : 0 < α) (hp : p ∈ Ioo (0:ℝ) 1)
    (hq : q ∈ Ioo (0:ℝ) 1) (hpq : p < q) : contV α p < contV α q := by
  have hp' := vs_contV_spec hα hp
  have hq' := vs_contV_spec hα hq
  rw [← (def_app_pl_profiles_S_bij hα).1.lt_iff_lt (Set.mem_Ioi.2 hp'.1) (Set.mem_Ioi.2 hq'.1),
    hp'.2, hq'.2]
  exact hpq

/-- Private: the pointwise matching identity `A_x(p)A_x(p+τ)/Δ_c(p,p+τ) = (f_x(p+τ)-f_x(p))/τ · √(U(p)/U(p+τ))`
on `0 < p`, `p+τ < 1`, `τ > 0` (the algebra of `lem:app-pl-matching`). -/
private lemma vs_pointwise {α x p τ : ℝ} (hα : 0 < α) (hx : 0 < x) (hp0 : 0 < p) (hτ : 0 < τ)
    (hpτ : p + τ < 1) :
    profA α x p * profA α x (p + τ) / profDeltaC α p (p + τ) =
      (profF α x (p + τ) - profF α x p) / τ * Real.sqrt (profU α p / profU α (p + τ)) := by
  have hp : p ∈ Ioo (0:ℝ) 1 := ⟨hp0, by linarith⟩
  have hq : p + τ ∈ Ioo (0:ℝ) 1 := ⟨by linarith, hpτ⟩
  have ha := (vs_contV_spec hα hp).1
  have hb := (vs_contV_spec hα hq).1
  have hab : contV α p < contV α (p + τ) := vs_contV_lt hα hp hq (by linarith)
  have hX : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hp1 : 0 < 1 - p := by linarith
  have hq0 : 0 < p + τ := by linarith
  have hq1 : 0 < 1 - (p + τ) := by linarith
  unfold profA profDeltaC profTc profF profU
  generalize contV α p = a at ha hab ⊢
  generalize contV α (p + τ) = b at hb hab ⊢
  generalize x ^ α = X at hX ⊢
  have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
  have hbaP : 0 < b - a := sub_pos.2 hab
  have haX : a + X ≠ 0 := by linarith
  have hbX : b + X ≠ 0 := by linarith
  have hF : a / (a + X) < b / (b + X) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hF0 : 0 ≤ a / (a + X) := div_nonneg ha.le (by linarith)
  have hG0 : 0 ≤ b / (b + X) := div_nonneg hb.le (by linarith)
  have hF1 : a / (a + X) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hG1 : b / (b + X) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hA1 : 0 ≤ a / (a + X) * (1 - a / (a + X)) * (1 - p) / p :=
    div_nonneg (mul_nonneg (mul_nonneg hF0 (by linarith)) hp1.le) hp0.le
  have hA2 : 0 ≤ b / (b + X) * (1 - b / (b + X)) * (1 - (p + τ)) / (p + τ) :=
    div_nonneg (mul_nonneg (mul_nonneg hG0 (by linarith)) hq1.le) hq0.le
  have hc : 0 ≤ (b / (b + X) - a / (a + X)) / τ := div_nonneg (by linarith) hτ.le
  have hr : 0 ≤ a / (p * (1 - p)) / (b / ((p + τ) * (1 - (p + τ)))) :=
    div_nonneg (div_nonneg ha.le (mul_nonneg hp0.le hp1.le))
      (div_nonneg hb.le (mul_nonneg hq0.le hq1.le))
  have hpos : 0 < (1 - p) * b * τ / ((p + τ) * (b - a)) := by
    apply div_pos
    · exact mul_pos (mul_pos hp1 hb) hτ
    · exact mul_pos hq0 hbaP
  have hD0 := hpos.ne'
  have hD : (1 - p) * (1 - (b * p - a * (p + τ)) / (b - a) / (p + τ)) =
      (1 - p) * b * τ / ((p + τ) * (b - a)) := by
    have hq0' : p + τ ≠ 0 := hq0.ne'
    field_simp
    ring
  rw [hD, ← Real.sqrt_mul hA1]
  have hsq : a / (a + X) * (1 - a / (a + X)) * (1 - p) / p *
      (b / (b + X) * (1 - b / (b + X)) * (1 - (p + τ)) / (p + τ)) =
      ((1 - p) * b * τ / ((p + τ) * (b - a)) * ((b / (b + X) - a / (a + X)) / τ)) ^ 2 *
        (a / (p * (1 - p)) / (b / ((p + τ) * (1 - (p + τ))))) := by
    have hp0' : p ≠ 0 := hp0.ne'
    have hp1' : 1 - p ≠ 0 := hp1.ne'
    have hq1' : 1 - (p + τ) ≠ 0 := hq1.ne'
    have hq0' : p + τ ≠ 0 := hq0.ne'
    have hτ' : τ ≠ 0 := hτ.ne'
    have hb0 : b ≠ 0 := hb.ne'
    have ha0 : a ≠ 0 := ha.ne'
    field_simp
    ring
  rw [hsq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hpos.le hc)]
  field_simp

/-- Private: `contV` is monotone (weakly) on `(0,1)`. -/
private lemma vs_contV_le {α p q : ℝ} (hα : 0 < α) (hp : p ∈ Ioo (0:ℝ) 1)
    (hq : q ∈ Ioo (0:ℝ) 1) (hpq : p ≤ q) : contV α p ≤ contV α q := by
  rcases hpq.lt_or_eq with h | h
  · exact (vs_contV_lt hα hp hq h).le
  · rw [h]

/-- Private: `t ↦ V/(V+t^α)` is continuous on `[0,1]` for `V > 0`. -/
private lemma vs_int_cont {α V : ℝ} (hα : 0 < α) (hV : 0 < V) :
    ContinuousOn (fun t : ℝ => V / (V + t ^ α)) (Icc 0 1) := by
  refine continuousOn_const.div (continuousOn_const.add
    (Real.continuous_rpow_const hα.le).continuousOn) ?_
  intro t ht
  have h0 : 0 ≤ t ^ α := Real.rpow_nonneg ht.1 α
  exact (by linarith : (0:ℝ) < V + t ^ α).ne'

/-- Private: `V · S_α(W) ≤ W · S_α(V)` for `0 < V ≤ W` (the monotonicity of `V/p`, as `pgm_K1`). -/
private lemma vs_K1 {α V W : ℝ} (hα : 0 < α) (hV : 0 < V) (hVW : V ≤ W) :
    V * contS α W ≤ W * contS α V := by
  have hW : 0 < W := lt_of_lt_of_le hV hVW
  unfold contS
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on zero_le_one
  · exact ((continuousOn_const.mul (vs_int_cont hα hW)).mono
      (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable
  · exact ((continuousOn_const.mul (vs_int_cont hα hV)).mono
      (by rw [Set.uIcc_of_le zero_le_one])).intervalIntegrable
  intro t ht
  have h0 : 0 ≤ t ^ α := Real.rpow_nonneg ht.1 α
  rw [← mul_div_assoc, ← mul_div_assoc, mul_comm W V]
  exact div_le_div_of_nonneg_left (mul_nonneg hV.le hW.le) (by linarith) (by linarith)

/-- Private: `f_x(p) ∈ [0,1]` on `(0,1)`. -/
private lemma vs_F_mem {α x p : ℝ} (hα : 0 < α) (hx : 0 < x) (hp : p ∈ Ioo (0:ℝ) 1) :
    0 ≤ profF α x p ∧ profF α x p ≤ 1 := by
  have ha := (vs_contV_spec hα hp).1
  have hX : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  unfold profF
  constructor
  · exact div_nonneg ha.le (by linarith)
  · rw [div_le_one (by linarith)]
    linarith

/-- Private: `U_α(p)/U_α(q) ≤ 1` for `0 < p < q < 1`, so its square root is at most one. -/
private lemma vs_sqrtU_le {α p q : ℝ} (hα : 0 < α) (hp : 0 < p) (hpq : p < q) (hq : q < 1) :
    Real.sqrt (profU α p / profU α q) ≤ 1 := by
  have hp' : p ∈ Ioo (0:ℝ) 1 := ⟨hp, by linarith⟩
  have hq' : q ∈ Ioo (0:ℝ) 1 := ⟨by linarith, hq⟩
  obtain ⟨ha, hSa⟩ := vs_contV_spec hα hp'
  obtain ⟨hb, hSb⟩ := vs_contV_spec hα hq'
  have hK := vs_K1 hα ha (vs_contV_le hα hp' hq' hpq.le)
  rw [hSa, hSb] at hK
  have hp1 : 0 < 1 - p := by linarith
  have hq1 : 0 < 1 - q := by linarith
  have hUq : 0 < profU α q := by
    unfold profU
    exact div_pos hb (mul_pos (by linarith) hq1)
  rw [Real.sqrt_le_one, div_le_one hUq]
  unfold profU
  rw [div_le_div_iff₀ (mul_pos hp hp1) (mul_pos (by linarith) hq1)]
  nlinarith [mul_le_mul_of_nonneg_right hK hq1.le,
    mul_le_mul_of_nonneg_left (show 1 - q ≤ 1 - p by linarith) (mul_nonneg hb.le hp.le)]

/-- Private: integrability of the matching integrand on `(0,1-τ)`, via the pointwise identity,
boundedness `|·| ≤ 1/τ`, and monotonicity of `contV`. -/
private lemma vs_interval_integrable {α x τ : ℝ} (hα : 0 < α) (hx : 0 < x)
    (hτ : τ ∈ Ioo (0:ℝ) 1) :
    IntervalIntegrable (fun p => profA α x p * profA α x (p + τ) / profDeltaC α p (p + τ))
      volume 0 (1 - τ) := by
  obtain ⟨hτ0, hτ1⟩ := hτ
  have hsm : MeasurableSet (Ioo (0:ℝ) (1 - τ)) := measurableSet_Ioo
  have hmemS : ∀ p ∈ Ioo (0:ℝ) (1 - τ), p ∈ Ioo (0:ℝ) 1 ∧ p + τ ∈ Ioo (0:ℝ) 1 := by
    intro p hp
    exact ⟨⟨hp.1, by linarith [hp.2]⟩, ⟨by linarith [hp.1], by linarith [hp.2]⟩⟩
  have mono1 : MonotoneOn (fun p => contV α p) (Ioo (0:ℝ) (1 - τ)) := by
    intro p hp q hq hpq
    exact vs_contV_le hα (hmemS p hp).1 (hmemS q hq).1 hpq
  have mono2 : MonotoneOn (fun p => contV α (p + τ)) (Ioo (0:ℝ) (1 - τ)) := by
    intro p hp q hq hpq
    exact vs_contV_le hα (hmemS p hp).2 (hmemS q hq).2 (by linarith)
  have m1 : AEMeasurable (fun p => contV α p) (volume.restrict (Ioo (0:ℝ) (1 - τ))) :=
    aemeasurable_restrict_of_monotoneOn hsm mono1
  have m2 : AEMeasurable (fun p => contV α (p + τ)) (volume.restrict (Ioo (0:ℝ) (1 - τ))) :=
    aemeasurable_restrict_of_monotoneOn hsm mono2
  have mU1 : AEMeasurable (fun p => profU α p) (volume.restrict (Ioo (0:ℝ) (1 - τ))) := by
    unfold profU
    exact m1.div (by fun_prop : Measurable fun p : ℝ => p * (1 - p)).aemeasurable
  have mU2 : AEMeasurable (fun p => profU α (p + τ)) (volume.restrict (Ioo (0:ℝ) (1 - τ))) := by
    unfold profU
    exact m2.div (by fun_prop : Measurable fun p : ℝ => (p + τ) * (1 - (p + τ))).aemeasurable
  have mF1 : AEMeasurable (fun p => profF α x p) (volume.restrict (Ioo (0:ℝ) (1 - τ))) := by
    unfold profF
    exact m1.div (m1.add aemeasurable_const)
  have mF2 : AEMeasurable (fun p => profF α x (p + τ)) (volume.restrict (Ioo (0:ℝ) (1 - τ))) := by
    unfold profF
    exact m2.div (m2.add aemeasurable_const)
  have mR : AEMeasurable (fun p => Real.sqrt (profU α p / profU α (p + τ)))
      (volume.restrict (Ioo (0:ℝ) (1 - τ))) :=
    Real.continuous_sqrt.measurable.comp_aemeasurable (mU1.div mU2)
  have mH : AEStronglyMeasurable
      (fun p => (profF α x (p + τ) - profF α x p) / τ *
        Real.sqrt (profU α p / profU α (p + τ)))
      (volume.restrict (Ioo (0:ℝ) (1 - τ))) :=
    (((mF2.sub mF1).div_const τ).mul mR).aestronglyMeasurable
  have hbd : ∀ᵐ p ∂(volume.restrict (Ioo (0:ℝ) (1 - τ))),
      ‖(fun p => (profF α x (p + τ) - profF α x p) / τ *
        Real.sqrt (profU α p / profU α (p + τ))) p‖ ≤ 1 / τ := by
    rw [ae_restrict_iff' hsm]
    apply ae_of_all
    intro p hp
    dsimp only
    obtain ⟨hp1, hp2⟩ := hmemS p hp
    obtain ⟨h1, h2⟩ := vs_F_mem hα hx hp1
    obtain ⟨h3, h4⟩ := vs_F_mem hα hx hp2
    have hsq0 : 0 ≤ Real.sqrt (profU α p / profU α (p + τ)) := Real.sqrt_nonneg _
    have hsq1 : Real.sqrt (profU α p / profU α (p + τ)) ≤ 1 :=
      vs_sqrtU_le hα hp1.1 (by linarith) hp2.2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsq0, abs_div, abs_of_pos hτ0]
    have hd : |profF α x (p + τ) - profF α x p| ≤ 1 :=
      abs_le.2 ⟨by linarith, by linarith⟩
    have hdiv : |profF α x (p + τ) - profF α x p| / τ ≤ 1 / τ :=
      div_le_div_of_nonneg_right hd hτ0.le
    exact (mul_le_mul_of_nonneg_left hsq1 (div_nonneg (abs_nonneg _) hτ0.le)).trans
      (by rw [mul_one]; exact hdiv)
  have hint : IntegrableOn (fun p => (profF α x (p + τ) - profF α x p) / τ *
        Real.sqrt (profU α p / profU α (p + τ))) (Ioo (0:ℝ) (1 - τ)) volume := by
    have := Measure.integrableOn_of_bounded (μ := volume.restrict (Ioo (0:ℝ) (1 - τ)))
      (s := univ) (by rw [Measure.restrict_apply_univ]; exact measure_Ioo_lt_top.ne) mH
      (M := 1 / τ) (by rw [Measure.restrict_univ]; exact hbd)
    rw [IntegrableOn, Measure.restrict_univ] at this
    exact this
  have heq : (fun p => (profF α x (p + τ) - profF α x p) / τ *
        Real.sqrt (profU α p / profU α (p + τ))) =ᵐ[volume.restrict (Ioo (0:ℝ) (1 - τ))]
      (fun p => profA α x p * profA α x (p + τ) / profDeltaC α p (p + τ)) := by
    refine (ae_restrict_iff' hsm).2 (ae_of_all _ ?_)
    intro p hp
    exact (vs_pointwise hα hx hp.1 hτ0 (by linarith [hp.2])).symm
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith),
    integrableOn_Ioc_iff_integrableOn_Ioo enorm_ne_top]
  exact hint.congr_fun_ae heq

/-- Private: the equality half of `profC_eq_integral_A` (a.e. pointwise identity, no integrability). -/
private lemma vs_profC_eq {α x τ : ℝ} (hα : 0 < α) (hx : 0 < x) (hτ : τ ∈ Ioo (0:ℝ) 1) :
    profC α x τ = ∫ p in (0:ℝ)..(1 - τ),
      profA α x p * profA α x (p + τ) / profDeltaC α p (p + τ) := by
  unfold profC
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [(Set.countable_singleton (1 - τ)).ae_notMem volume] with p hp
  intro hmem
  have hmem' : p ∈ Ioc (0:ℝ) (1 - τ) := by
    rwa [Set.uIoc_of_le (by linarith [hτ.2])] at hmem
  have hlt : p < 1 - τ :=
    lt_of_le_of_ne hmem'.2 (fun h => hp (Set.mem_singleton_iff.2 h))
  exact (vs_pointwise hα hx hmem'.1 hτ.1 (by linarith)).symm

/-- The identity `C_{α,x}(τ) = ∫_0^{1-τ} A_x(p)A_x(p+τ)/Δ_c(p,p+τ) dp` (task L-G.7b; proof step of
`thm:app-pl-volatility`(i), l.2225-2227, via the identity of `lem:app-pl-matching`, l.2100-2105; snapshot cr-2026-10-23). -/
theorem profC_eq_integral_A {α : ℝ} (hα : 0 < α) {x τ : ℝ} (hx : x ∈ Ioc 0 1) (hτ : τ ∈ Ioo 0 1) :
    IntervalIntegrable (fun p => profA α x p * profA α x (p + τ) / profDeltaC α p (p + τ))
        volume 0 (1 - τ) ∧
      profC α x τ = ∫ p in (0:ℝ)..(1 - τ), profA α x p * profA α x (p + τ) / profDeltaC α p (p + τ) := by
  exact ⟨vs_interval_integrable hα hx.1 hτ, vs_profC_eq hα hx.1 hτ⟩

/-! ### Private helpers for the shell asymptotics (task P-G.7b.P2) -/

/-- Private: a compact subset of `(0,1)` lies in some `[a,b] ⊂ (0,1)`. -/
private lemma vs_Kbd (K : Set ℝ) (hK : K ⊆ Ioo 0 1) (hKc : IsCompact K) :
    ∃ a b : ℝ, 0 < a ∧ a < 1 ∧ 0 < b ∧ b < 1 ∧ ∀ p ∈ K, a ≤ p ∧ p ≤ b := by
  rcases K.eq_empty_or_nonempty with h | h
  · exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num, by simp [h]⟩
  · obtain ⟨a, ha, hamin⟩ := hKc.exists_isMinOn h continuousOn_id
    obtain ⟨b, hb, hbmax⟩ := hKc.exists_isMaxOn h continuousOn_id
    exact ⟨a, b, (hK ha).1, (hK ha).2, (hK hb).1, (hK hb).2,
      fun p hp => ⟨isMinOn_iff.1 hamin p hp, isMaxOn_iff.1 hbmax p hp⟩⟩

/-- Private: `|√s - √t| ≤ √|s - t|`. -/
private lemma vs_sqrt_diff {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |Real.sqrt s - Real.sqrt t| ≤ Real.sqrt |s - t| := by
  apply Real.le_sqrt_of_sq_le
  have h1 := Real.sq_sqrt hs
  have h2 := Real.sq_sqrt ht
  have hs0 := Real.sqrt_nonneg s
  have ht0 := Real.sqrt_nonneg t
  have h3 : |Real.sqrt s - Real.sqrt t| ≤ Real.sqrt s + Real.sqrt t := by
    rw [abs_le]; constructor <;> linarith
  calc |Real.sqrt s - Real.sqrt t| ^ 2 = |Real.sqrt s - Real.sqrt t| * |Real.sqrt s - Real.sqrt t| := sq _
    _ ≤ |Real.sqrt s - Real.sqrt t| * (Real.sqrt s + Real.sqrt t) :=
        mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    _ = |s - t| := by
        rw [← abs_of_nonneg (by linarith : 0 ≤ Real.sqrt s + Real.sqrt t), ← abs_mul]
        congr 1
        nlinarith

/-- Private: `f_i(γp) = W/(W + x^α)` with `W = V_N(p) > 0` and `x = i/N`. -/
private lemma vs_partF_eq {α : ℝ} {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B) (hc : 0 < c)
    (i : Fin N) {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) :
    0 < finV α N p ∧
      partF B (plSpec α c N) i (gammaOf N B * p) =
        finV α N p / (finV α N p + rowFrac i ^ α) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  have hγ : 0 < gammaOf N B := by unfold gammaOf; positivity
  have hm : gammaOf N B * p ∈ Ioo 0 (gammaOf N B) :=
    ⟨mul_pos hγ hp.1, mul_lt_of_lt_one_right hγ hp.2⟩
  have hpos : ∀ j, 0 < plSpec α c N j := fun j => by
    unfold plSpec; exact mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)
  have hsurj := (def_app_pl_participation_bij (plSpec α c N) hB hN hpos).1.surjOn hm
  have hLpos : 0 < partLam B (plSpec α c N) (gammaOf N B * p) := Function.invFunOn_mem hsurj
  have hV := eqn_app_pl_Lambda_V (N := N) (B := B) α c hN hB hc hm
  rw [show gammaOf N B * p / gammaOf N B = p by field_simp] at hV
  have hNa : 0 < (N:ℝ) ^ α := Real.rpow_pos_of_pos hNr α
  have hNc : 0 < (N:ℝ) ^ α / c := div_pos hNa hc
  rw [hV] at hLpos
  have hWpos : 0 < finV α N p := by
    by_contra h
    push_neg at h
    nlinarith
  refine ⟨hWpos, ?_⟩
  unfold partF
  rw [hV]
  unfold plSpec rowFrac rowIdx
  have ht : (0:ℝ) < ((i:ℕ):ℝ) + 1 := by positivity
  have hta : 0 < (((i:ℕ):ℝ) + 1) ^ α := Real.rpow_pos_of_pos ht α
  rw [Real.div_rpow ht.le hNr.le, Real.rpow_neg ht.le]
  generalize finV α N p = W at hWpos ⊢
  generalize (N:ℝ) ^ α = A at hNa hNc ⊢
  generalize (((i:ℕ):ℝ) + 1) ^ α = T at hta ⊢
  field_simp
  ring

/-- Private: closeness of `W/(W + x'^α)` and `V/(V + x^α)` in terms of `log` ratios. -/
private lemma vs_f_close {α x x' V W U τ : ℝ} (hα : 0 < α) (hx : 0 < x) (hx' : 0 < x')
    (hV : 0 < V) (hW : 0 < W) (hU : x ^ α / V ≤ U) (hτ : τ ≤ 1 / 2)
    (hlog : α * |Real.log (x' / x)| + |Real.log (W / V)| ≤ τ) :
    |W / (W + x' ^ α) - V / (V + x ^ α)| ≤ 2 * U * τ := by
  have hxa : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hx'a : 0 < x' ^ α := Real.rpow_pos_of_pos hx' α
  set u := x ^ α / V with hu
  have hu0 : 0 < u := div_pos hxa hV
  set r := (x' / x) ^ α * (V / W) with hr
  have hr0 : 0 < r := mul_pos (Real.rpow_pos_of_pos (div_pos hx' hx) α) (div_pos hV hW)
  have hlogr : Real.log r = α * Real.log (x' / x) - Real.log (W / V) := by
    rw [hr, Real.log_mul (Real.rpow_pos_of_pos (div_pos hx' hx) α).ne' (div_pos hV hW).ne',
      Real.log_rpow (div_pos hx' hx), Real.log_div hV.ne' hW.ne', Real.log_div hW.ne' hV.ne']
    ring
  have hlr : |Real.log r| ≤ τ := by
    rw [hlogr]
    calc |α * Real.log (x' / x) - Real.log (W / V)|
        ≤ |α * Real.log (x' / x)| + |Real.log (W / V)| := abs_sub _ _
      _ = α * |Real.log (x' / x)| + |Real.log (W / V)| := by rw [abs_mul, abs_of_pos hα]
      _ ≤ τ := hlog
  have hr1 : |r - 1| ≤ 2 * τ := by
    have h := Real.abs_exp_sub_one_le (x := Real.log r) (hlr.trans (by linarith))
    rw [Real.exp_log hr0] at h
    linarith
  have e : x' ^ α / W = u * r := by
    rw [hu, hr, Real.div_rpow hx'.le hx.le]
    field_simp
  have e1 : W / (W + x' ^ α) = 1 / (1 + u * r) := by
    rw [← e]; field_simp
  have e2 : V / (V + x ^ α) = 1 / (1 + u) := by
    rw [hu]; field_simp
  rw [e1, e2]
  have hur : 0 ≤ u * r := (mul_pos hu0 hr0).le
  have key : 1 / (1 + u * r) - 1 / (1 + u) = u * (1 - r) / ((1 + u * r) * (1 + u)) := by
    field_simp
    ring
  rw [key, abs_div, abs_of_pos (by positivity : 0 < (1 + u * r) * (1 + u)), div_le_iff₀ (by positivity)]
  have hD : 1 ≤ (1 + u * r) * (1 + u) := by nlinarith
  have hn : |u * (1 - r)| ≤ u * (2 * τ) := by
    rw [abs_mul, abs_of_pos hu0, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left hr1 hu0.le
  have hUn : u * (2 * τ) ≤ U * (2 * τ) := by
    have : 0 ≤ 2 * τ := by
      have := abs_nonneg (Real.log r); linarith
    exact mul_le_mul_of_nonneg_right hU this
  have hτ0 : 0 ≤ τ := le_trans (abs_nonneg _) hlr
  have hUt : 0 ≤ U * (2 * τ) := le_trans (mul_nonneg hu0.le (by linarith)) hUn
  calc |u * (1 - r)| ≤ U * (2 * τ) := hn.trans hUn
    _ = U * (2 * τ) * 1 := by ring
    _ ≤ U * (2 * τ) * ((1 + u * r) * (1 + u)) := mul_le_mul_of_nonneg_left hD hUt
    _ = 2 * U * τ * ((1 + u * r) * (1 + u)) := by ring

/-- Private: from closeness of `f` to closeness of `√(f(1-f)) √q`. -/
private lemma vs_g_close {f f' q a ε : ℝ} (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hf0' : 0 ≤ f')
    (hf1' : f' ≤ 1) (hq0 : 0 ≤ q) (ha : 0 < a) (hqa : q ≤ 1 / a) (hε : 0 < ε)
    (hfε : |f' - f| ≤ a * ε ^ 2) :
    |Real.sqrt (f' * (1 - f')) * Real.sqrt q - Real.sqrt (f * (1 - f)) * Real.sqrt q| ≤ ε := by
  rw [← sub_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg q)]
  have hs' : 0 ≤ f' * (1 - f') := mul_nonneg hf0' (by linarith)
  have hs : 0 ≤ f * (1 - f) := mul_nonneg hf0 (by linarith)
  have h1 := vs_sqrt_diff hs' hs
  have h2 : |f' * (1 - f') - f * (1 - f)| ≤ a * ε ^ 2 := by
    have : f' * (1 - f') - f * (1 - f) = (f' - f) * (1 - f' - f) := by ring
    rw [this, abs_mul]
    have h3 : |1 - f' - f| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    calc |f' - f| * |1 - f' - f| ≤ |f' - f| * 1 := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      _ ≤ a * ε ^ 2 := by linarith
  calc |Real.sqrt (f' * (1 - f')) - Real.sqrt (f * (1 - f))| * Real.sqrt q
      ≤ Real.sqrt (a * ε ^ 2) * Real.sqrt (1 / a) :=
        mul_le_mul (h1.trans (Real.sqrt_le_sqrt h2)) (Real.sqrt_le_sqrt hqa)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = ε := by
        rw [← Real.sqrt_mul (by positivity)]
        have : a * ε ^ 2 * (1 / a) = ε ^ 2 := by field_simp
        rw [this, Real.sqrt_sq hε.le]

/-! ## Shell asymptotics for `thm:app-pl-volatility`(i) -/

/-- `f_i(γp) → f_x(p)` and `g_i(γp) → A_x(p)`, uniformly for `p` in a compact subset of `(0,1)`
(task L-G.7b; proof step of `thm:app-pl-volatility`(i), l.2211-2214; snapshot cr-2026-10-23). -/
theorem shell_f_g_tendsto {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) {x : ℝ} (hx : x ∈ Ioc 0 1)
    (i : ∀ n, Fin (N n)) (hix : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 x))
    (K : Set ℝ) (hK : K ⊆ Ioo 0 1) (hKc : IsCompact K) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ p ∈ K,
      |partF (B n) (plSpec α (c n) (N n)) (i n) (gammaOf (N n) (B n) * p) - profF α x p| ≤ ε ∧
      |gRow (B n) (plSpec α (c n) (N n)) (i n) (gammaOf (N n) (B n) * p) - profA α x p| ≤ ε := by
  intro ε hε
  have hα := R.hα
  obtain ⟨a, b, ha0, ha1, hb0, hb1, hab⟩ := vs_Kbd K hK hKc
  obtain ⟨C, hC⟩ := lem_app_pl_finite_inverse_ii hα
  have hx0 : 0 < x := hx.1
  have hVa := (vs_contV_spec hα ⟨ha0, ha1⟩).1
  have hxa : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
  set Vm := contV α a with hVm
  set U := x ^ α / Vm with hUdef
  have hU0 : 0 < U := div_pos hxa hVa
  set ε₁ := min ε (a * ε ^ 2) with hε₁def
  have hε₁ : 0 < ε₁ := lt_min hε (by positivity)
  set τ := min (1 / 2) (ε₁ / (2 * U)) with hτdef
  have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hxlog : Tendsto (fun n => Real.log (rowFrac (i n) / x)) atTop (𝓝 0) := by
    have h : Tendsto (fun n => rowFrac (i n) / x) atTop (𝓝 (x / x)) := hix.div_const x
    rw [div_self hx0.ne'] at h
    have h2 := (Real.continuousAt_log one_ne_zero).tendsto.comp h
    simpa [Function.comp_def] using h2
  have hBinv : Tendsto (fun n => C / ((B n : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop R.hB
  have hs : Tendsto (fun n => α * |Real.log (rowFrac (i n) / x)| + C / ((B n : ℕ) : ℝ)) atTop
      (𝓝 0) := by
    have := (hxlog.abs.const_mul α).add hBinv
    simpa using this
  filter_upwards [hs.eventually (gt_mem_nhds hτ), R.hB.eventually_ge_atTop 2,
    R.hγ.eventually_ge_atTop (max (1 / a) (1 / (1 - b)))] with n hsn hBn hγn
  intro p hp
  have hp' : p ∈ Ioo (0:ℝ) 1 := hK hp
  obtain ⟨hap, hpb⟩ := hab p hp
  have hNn := R.hNpos n
  have hBpos := R.hBpos n
  have hcn := R.hcpos n
  have hB2 : 2 ≤ B n := by exact_mod_cast hBn
  have hNr : (0:ℝ) < (N n : ℝ) := by exact_mod_cast hNn
  have hBr : (0:ℝ) < (B n : ℝ) := by exact_mod_cast hBpos
  have hγ : 0 < gammaOf (N n) (B n) := by unfold gammaOf; positivity
  have hγn' : max (1 / a) (1 / (1 - b)) ≤ gammaOf (N n) (B n) := hγn
  have hγa : 1 / gammaOf (N n) (B n) ≤ p := by
    have h1 : 1 / a ≤ gammaOf (N n) (B n) := (le_max_left _ _).trans hγn'
    rw [div_le_iff₀ ha0] at h1
    rw [div_le_iff₀ hγ]
    nlinarith
  have hγb : p ≤ 1 - 1 / gammaOf (N n) (B n) := by
    have h1 : 1 / (1 - b) ≤ gammaOf (N n) (B n) := (le_max_right _ _).trans hγn'
    rw [div_le_iff₀ (by linarith : 0 < 1 - b)] at h1
    have : 1 / gammaOf (N n) (B n) ≤ 1 - b := by
      rw [div_le_iff₀ hγ]; nlinarith
    linarith
  have hlogb := hC (N n) (B n) 1 p hNn hB2 le_rfl (by simpa using hγa) (by simpa using hγb)
  rw [mul_one] at hlogb
  obtain ⟨hWpos, hF⟩ := vs_partF_eq (α := α) (c := c n) hNn hBpos hcn (i n) hp'
  have hVp : 0 < contV α p := (vs_contV_spec hα hp').1
  have hVle : Vm ≤ contV α p := vs_contV_le hα ⟨ha0, ha1⟩ hp' hap
  have hUle : x ^ α / contV α p ≤ U := div_le_div_of_nonneg_left hxa.le hVa hVle
  have hxn : 0 < rowFrac (i n) := by
    unfold rowFrac rowIdx
    exact div_pos (by positivity) hNr
  have hlog : α * |Real.log (rowFrac (i n) / x)| + |Real.log (finV α (N n) p / contV α p)| ≤ τ := by
    have : α * |Real.log (rowFrac (i n) / x)| + C / ((B n : ℕ) : ℝ) < τ := hsn
    linarith
  have hfc := vs_f_close hα hx0 hxn hVp hWpos hUle (min_le_left _ _) hlog
  have hfε : |finV α (N n) p / (finV α (N n) p + rowFrac (i n) ^ α) - profF α x p| ≤ ε₁ := by
    refine hfc.trans ?_
    have h1 : τ ≤ ε₁ / (2 * U) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  constructor
  · rw [hF]
    exact hfε.trans (min_le_left _ _)
  · obtain ⟨hf0, hf1⟩ := vs_F_mem hα hx0 hp'
    have hxn' : 0 ≤ finV α (N n) p / (finV α (N n) p + rowFrac (i n) ^ α) :=
      div_nonneg hWpos.le (by positivity)
    have hxn1 : finV α (N n) p / (finV α (N n) p + rowFrac (i n) ^ α) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have := Real.rpow_nonneg hxn.le α
      linarith
    have hq : (gammaOf (N n) (B n) - gammaOf (N n) (B n) * p) / (gammaOf (N n) (B n) * p)
        = (1 - p) / p := by
      field_simp [hp'.1.ne']
    unfold gRow profA
    rw [hF, hq, mul_div_assoc, Real.sqrt_mul (mul_nonneg hf0 (by linarith))]
    refine vs_g_close hf0 hf1 hxn' hxn1 (div_nonneg (by linarith [hp'.2]) hp'.1.le) ha0 ?_ hε
      (hfε.trans (min_le_right _ _))
    rw [div_le_div_iff₀ hp'.1 ha0]
    nlinarith [hp'.1]

/-- `ϑ_N(γp) = 1/E(γp) + O(1/γ)` on compact sets of `p` (task L-G.7b; proof step of
`thm:app-pl-volatility`(i), l.2215; snapshot cr-2026-10-23). The constant is chosen before the sequence. -/
theorem shell_theta_approx {α β : ℝ} (K : Set ℝ) (hK : K ⊆ Ioo 0 1) (hKc : IsCompact K) :
    ∃ C : ℝ, ∀ (N B : ℕ → ℕ) (c : ℕ → ℝ), assum_app_pl_regime α β N B c →
      ∀ᶠ n in atTop, ∀ p ∈ K,
        |thetaN β (B n) (plSpec α (c n) (N n)) (gammaOf (N n) (B n) * p) -
            1 / Efun β (gammaOf (N n) (B n) * p)| ≤ C / gammaOf (N n) (B n) := by
  by_cases hα : 0 < α
  swap
  · exact ⟨0, fun N B c R => absurd R.hα hα⟩
  obtain ⟨a, b, ha0, ha1, hb0, hb1, hab⟩ := vs_Kbd K hK hKc
  obtain ⟨cα, hcα, hel⟩ := lem_app_pl_elasticity_i (α := α) hα
  refine ⟨(1 / cα + 1) * (1 / a + 1 / (1 - b)), ?_⟩
  intro N B c R
  refine Filter.Eventually.of_forall (fun n => ?_)
  intro p hp
  obtain ⟨hap, hpb⟩ := hab p hp
  have hp' : p ∈ Ioo (0:ℝ) 1 := hK hp
  have hNn := R.hNpos n
  have hBpos := R.hBpos n
  have hcn := R.hcpos n
  have hNr : (0:ℝ) < (N n : ℝ) := by exact_mod_cast hNn
  have hBr : (0:ℝ) < (B n : ℝ) := by exact_mod_cast hBpos
  have hγ : 0 < gammaOf (N n) (B n) := by unfold gammaOf; positivity
  set γ := gammaOf (N n) (B n) with hγdef
  have hm : γ * p ∈ Ioo 0 γ := ⟨mul_pos hγ hp'.1, mul_lt_of_lt_one_right hγ hp'.2⟩
  obtain ⟨hlo, hhi⟩ := (hel (N n) (B n) (c n) hNn hBpos hcn).2 (γ * p) hm
  have hq1 : 0 < 1 - p := by linarith [hp'.2]
  have e1 : 1 / (γ * p) = (1 / γ) * (1 / p) := by field_simp
  have e2 : 1 / (γ - γ * p) = (1 / γ) * (1 / (1 - p)) := by
    rw [show γ - γ * p = γ * (1 - p) by ring]; field_simp
  have hth : thetaN β (B n) (plSpec α (c n) (N n)) (γ * p) - 1 / Efun β (γ * p) =
      (deriv (partLam (B n) (plSpec α (c n) (N n))) (γ * p) /
        partLam (B n) (plSpec α (c n) (N n)) (γ * p) - 1 / (γ * p)) + 1 / (γ - γ * p) := by
    unfold thetaN
    ring
  rw [hth]
  set L := deriv (partLam (B n) (plSpec α (c n) (N n))) (γ * p) /
        partLam (B n) (plSpec α (c n) (N n)) (γ * p) with hL
  have hg1 : 0 ≤ 1 / (γ - γ * p) := by
    rw [e2]; exact mul_nonneg (one_div_pos.2 hγ).le (one_div_pos.2 hq1).le
  rw [abs_of_nonneg (by linarith)]
  have hu : 1 / p ≤ 1 / a := one_div_le_one_div_of_le ha0 hap
  have hv : 1 / (1 - p) ≤ 1 / (1 - b) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have hu0 : 0 ≤ 1 / p := (one_div_pos.2 hp'.1).le
  have hv0 : 0 ≤ 1 / (1 - p) := (one_div_pos.2 hq1).le
  have hup : L - 1 / (γ * p) + 1 / (γ - γ * p) ≤
      (1 / cα) * ((1 / γ) * (1 / p) + (1 / γ) * (1 / (1 - p))) + (1 / γ) * (1 / (1 - p)) := by
    rw [e1, e2] at hhi
    rw [e1, e2]
    have : 0 ≤ (1 / γ) * (1 / p) := mul_nonneg (one_div_pos.2 hγ).le hu0
    linarith
  refine hup.trans ?_
  have hγi : 0 < 1 / γ := one_div_pos.2 hγ
  have hcα1 : 0 < 1 / cα := one_div_pos.2 hcα
  have hR : (1 / cα + 1) * (1 / a + 1 / (1 - b)) / γ =
      (1 / γ) * ((1 / cα + 1) * (1 / a + 1 / (1 - b))) := by ring
  rw [hR]
  have h1 := mul_le_mul_of_nonneg_left hu hγi.le
  have h2 := mul_le_mul_of_nonneg_left hv hγi.le
  have h3 := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hcα1.le
  have h4 : 0 ≤ 1 / γ * (1 / a) := mul_nonneg hγi.le (one_div_pos.2 ha0).le
  nlinarith [h1, h2, h3, h4]

private lemma vsh_emaW_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (a : ℕ) : 0 < emaW β a := by
  unfold emaW
  exact mul_pos (by linarith) (pow_pos hβ0 a)

private lemma vsh_w2_summable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Summable (fun a : ℕ => emaW β a ^ 2) := by
  have hr : β ^ 2 < 1 := pow_lt_one₀ hβ0.le hβ1 (by norm_num)
  have key : (fun j : ℕ => emaW β j ^ 2) = fun j => (1 - β) ^ 2 * (β ^ 2) ^ j := by
    funext j
    unfold emaW
    rw [mul_pow, pow_right_comm β j 2]
  rw [key]
  exact (summable_geometric_of_lt_one (by positivity) hr).mul_left _

private lemma vsh_int_summ {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {f : ℕ → ℝ → ℝ} {c : ℝ}
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
    ((vsh_w2_summable hβ0 hβ1).mul_left c)
  calc ∫ g, f a g ∂(gaussianReal 0 1) ≤ ∫ g, c * (emaW β a ^ 2 * g ^ 2) ∂(gaussianReal 0 1) :=
        integral_mono (hint a) (hb a) (hle a)
    _ = c * emaW β a ^ 2 := by
        rw [integral_const_mul, integral_const_mul, Muon.Foundations.gaussian_moment_two, mul_one,
          mul_comm]


private lemma vsh_weightSeq {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : Muon.DetEquiv.WeightSeq (emaW β) := by
  refine ⟨fun j => (vsh_emaW_pos hβ0 hβ1 j).le, ?_, ⟨0, (vsh_emaW_pos hβ0 hβ1 0).ne'⟩⟩
  have key : emaW β = fun j => (1 - β) * β ^ j := by
    funext j; rfl
  rw [key]
  exact (summable_geometric_of_lt_one hβ0.le hβ1).mul_left _

private lemma vsh_range {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    ∃ a ∈ Ioi (0:ℝ), Muon.DetEquiv.rW (emaW β) a = m := by
  have hcont : ContinuousOn (Muon.DetEquiv.rW (emaW β)) (Ici 0) :=
    continuousOn_id.mul (Muon.DetEquiv.lem_app_de_scalar_ii (vsh_weightSeq hβ0 hβ1)).2.2.1
  have hr0 := (Muon.DetEquiv.lem_app_de_scalar_iii (vsh_weightSeq hβ0 hβ1)).2.2.1
  have hT := (Muon.DetEquiv.lem_app_de_scalar_iii (vsh_weightSeq hβ0 hβ1)).2.2.2.2.2.2
  have hinf : {j : ℕ | 0 < emaW β j} = Set.univ := by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact vsh_emaW_pos hβ0 hβ1 j
  have hTop : (Set.encard {j : ℕ | 0 < emaW β j}).toENNReal = ⊤ := by
    rw [hinf, Set.encard_univ, ENat.card_eq_top_of_infinite]
    rfl
  rw [hTop] at hT
  have hev : ∀ᶠ q in atTop, ENNReal.ofReal m < ENNReal.ofReal (Muon.DetEquiv.rW (emaW β) q) :=
    hT.eventually (Ioi_mem_nhds ENNReal.ofReal_lt_top)
  obtain ⟨Q0, hQ0⟩ := (hev.and (eventually_ge_atTop (1:ℝ))).exists
  have hlt : ENNReal.ofReal m < ENNReal.ofReal (Muon.DetEquiv.rW (emaW β) Q0) := hQ0.1
  have hmQ : m < Muon.DetEquiv.rW (emaW β) Q0 := (ENNReal.ofReal_lt_ofReal_iff'.1 hlt).1
  have hmem : m ∈ Icc (Muon.DetEquiv.rW (emaW β) 0) (Muon.DetEquiv.rW (emaW β) Q0) :=
    ⟨by rw [hr0]; exact hm.le, hmQ.le⟩
  obtain ⟨q, hq, hqe⟩ := intermediate_value_Icc (by linarith [hQ0.2] : (0:ℝ) ≤ Q0)
    (hcont.mono Icc_subset_Ici_self) hmem
  have hqpos : 0 < q := by
    rcases hq.1.eq_or_lt with h | h
    · rw [← h, hr0] at hqe
      linarith
    · exact h
  exact ⟨q, hqpos, hqe⟩

private lemma vsh_Qm {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    0 < Qm β m ∧ Muon.DetEquiv.rW (emaW β) (Qm β m) = m := by
  have hex : ∃ a ∈ Ioi (0:ℝ), Muon.DetEquiv.rW (emaW β) a = m := vsh_range hβ0 hβ1 hm
  exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩

/-- A comparison with the diagonal resolvent bounds the deficit of the lag kernel. -/
private lemma vsh_M_deficit {β q₁ q₂ d : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (h₁ : 0 < q₁) (h₂ : 0 < q₂) (ℓ : ℕ) (hd : 1 ≤ d)
    (hr : q₁ ≤ d * (β ^ (2 * ℓ) * q₂)) :
    |Muon.DetEquiv.rW (emaW β) q₁ - MLagNat β q₁ q₂ ℓ| ≤
      d * (q₁ * deriv (Muon.DetEquiv.rW (emaW β)) q₁) := by
  let X : ℕ → ℝ → ℝ := fun a g => q₁ * emaW β a ^ 2 * g ^ 2
  let Y : ℕ → ℝ → ℝ := fun a g => β ^ (2 * ℓ) * q₂ * emaW β a ^ 2 * g ^ 2
  have hX : ∀ a g, 0 ≤ X a g := fun a g => by dsimp [X]; positivity
  have hY : ∀ a g, 0 ≤ Y a g := fun a g => by dsimp [Y]; positivity
  have hden : ∀ a g, 0 < (1 + X a g) * (1 + Y a g) := fun a g => by
    have := hX a g; have := hY a g; positivity
  have hbound : ∀ a g, X a g / ((1 + X a g) * (1 + Y a g)) ≤
      q₁ * (emaW β a ^ 2 * g ^ 2) := by
    intro a g
    have hx := hX a g; have hy := hY a g
    have : 1 ≤ (1 + X a g) * (1 + Y a g) := by nlinarith
    exact (div_le_self hx this).trans_eq (by dsimp [X]; ring)
  have hA := vsh_int_summ hβ0 hβ1
    (f := fun a g => X a g / ((1 + X a g) * (1 + Y a g)))
    (fun a => by
      refine Continuous.div (by dsimp [X]; fun_prop) (by dsimp [X, Y]; fun_prop) ?_
      exact fun g => (hden a g).ne')
    (fun a g => div_nonneg (hX a g) (hden a g).le) hbound
  have hM := vsh_int_summ hβ0 hβ1
    (f := fun a g => X a g * Y a g / ((1 + X a g) * (1 + Y a g))) (c := q₁)
    (fun a => by
      refine Continuous.div (by dsimp [X, Y]; fun_prop) (by dsimp [X, Y]; fun_prop) ?_
      exact fun g => (hden a g).ne')
    (fun a g => div_nonneg (mul_nonneg (hX a g) (hY a g)) (hden a g).le)
    (fun a g => by
      have hx := hX a g; have hy := hY a g
      refine le_trans ?_ (show X a g = q₁ * (emaW β a ^ 2 * g ^ 2) by dsimp [X]; ring).le
      rw [div_le_iff₀ (hden a g)]
      nlinarith [mul_nonneg hx hy, mul_nonneg (sq_nonneg (X a g)) hy])
  have hE := vsh_int_summ hβ0 hβ1
    (f := fun a g => X a g / (1 + X a g) ^ 2) (c := q₁)
    (fun a => by
      refine Continuous.div (by dsimp [X]; fun_prop) (by dsimp [X]; fun_prop) ?_
      intro g; have := hX a g; positivity)
    (fun a g => div_nonneg (hX a g) (sq_nonneg _))
    (fun a g => by
      have hx := hX a g
      exact (div_le_self hx (by nlinarith : 1 ≤ (1 + X a g) ^ 2)).trans_eq
        (by dsimp [X]; ring))
  have hMeq : MLagNat β q₁ q₂ ℓ =
      ∑' a, ∫ g, X a g * Y a g / ((1 + X a g) * (1 + Y a g)) ∂(gaussianReal 0 1) := by
    unfold MLagNat
    refine tsum_congr fun a => ?_
    congr 1; funext g; dsimp [X, Y]; ring
  have hsplit : Muon.DetEquiv.rW (emaW β) q₁ =
      (∑' a, ∫ g, X a g / ((1 + X a g) * (1 + Y a g)) ∂(gaussianReal 0 1)) +
        MLagNat β q₁ q₂ ℓ := by
    rw [(Muon.DetEquiv.lem_app_de_scalar_iii (vsh_weightSeq hβ0 hβ1)).1 q₁ h₁.le,
      hMeq, ← hA.2.tsum_add hM.2]
    refine tsum_congr fun a => ?_
    rw [← integral_add (hA.1 a) (hM.1 a)]
    congr 1; funext g
    have hx := hX a g; have hy := hY a g
    have heq : emaW β a ^ 2 * q₁ * g ^ 2 = X a g := by dsimp [X]; ring
    rw [heq]
    field_simp
    <;> ring
  have hdiag : q₁ * deriv (Muon.DetEquiv.rW (emaW β)) q₁ =
      ∑' a, ∫ g, X a g / (1 + X a g) ^ 2 ∂(gaussianReal 0 1) := by
    rw [((Muon.DetEquiv.lem_app_de_scalar_iii (vsh_weightSeq hβ0 hβ1)).2.2.2.1 q₁ h₁).deriv,
      ← tsum_mul_left]
    refine tsum_congr fun a => ?_
    rw [← integral_const_mul, ← integral_const_mul]
    congr 1; funext g; dsimp [X]; ring
  have hnonneg : 0 ≤ Muon.DetEquiv.rW (emaW β) q₁ - MLagNat β q₁ q₂ ℓ := by
    rw [hsplit, add_sub_cancel_right]
    exact tsum_nonneg fun a => integral_nonneg fun g => div_nonneg (hX a g) (hden a g).le
  rw [abs_of_nonneg hnonneg, hsplit, add_sub_cancel_right, hdiag, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _ hA.2 (hE.2.mul_left d)
  intro a
  rw [← integral_const_mul]
  apply integral_mono (hA.1 a) ((hE.1 a).const_mul d)
  intro g
  have hx := hX a g; have hy := hY a g
  have hxy : X a g ≤ d * Y a g := by
    have := mul_le_mul_of_nonneg_right hr (mul_nonneg (sq_nonneg (emaW β a)) (sq_nonneg g))
    simpa [X, Y, mul_assoc] using this
  have hd0 : 0 ≤ d := by linarith
  dsimp only
  rw [← mul_div_assoc, div_le_div_iff₀ (hden a g) (by positivity)]
  nlinarith [mul_nonneg hx (show 0 ≤ d * (1 + Y a g) - (1 + X a g) by linarith),
    mul_nonneg (sq_nonneg (X a g)) (show 0 ≤ d * (1 + Y a g) - (1 + X a g) by linarith)]

/-- On the shell `m₂ = m₁ + ℓ + O(1)`, `m₁ - 𝖬_ℓ = O(1)` (task L-G.7b; proof step of
`thm:app-pl-volatility`(i), l.2215-2217; snapshot cr-2026-10-23). The shell width `C₀` is chosen first. -/
theorem shell_MLag_bound {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) (ℓ : ℕ → ℤ)
    (hℓ : Tendsto (fun n => (ℓ n : ℝ) / gammaOf (N n) (B n)) atTop (𝓝 τ))
    (K : Set ℝ) (hK : K ⊆ Ioo 0 (1 - τ)) (hKc : IsCompact K) (C₀ : ℝ) :
    ∃ C₁ : ℝ, ∀ᶠ n in atTop, ∀ p ∈ K, ∀ m₂ : ℝ,
      |m₂ - (gammaOf (N n) (B n) * p + (ℓ n : ℝ))| ≤ C₀ →
        |gammaOf (N n) (B n) * p -
          MLag β (Qm β (gammaOf (N n) (B n) * p)) (Qm β m₂) (ℓ n)| ≤ C₁ := by
  obtain ⟨a, b, ha0, ha1, hb0, hb1, hab⟩ :=
    vs_Kbd K (fun p hp => ⟨(hK hp).1, lt_trans (hK hp).2 (by linarith [hτ.1])⟩) hKc
  obtain ⟨CQ, hCQ⟩ := lem_app_pl_weights_iii_logQ R.hβ0 R.hβ1
  obtain ⟨cE, CE, hcE, hcCE, hE⟩ := lem_app_pl_weights_iii_E R.hβ0 R.hβ1
  let L := 2 * |CQ| + 2 * |Real.log β| * max C₀ 0
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨Real.exp L * CE, ?_⟩
  filter_upwards [R.hγ.eventually_ge_atTop ((1 + max C₀ 0) / a),
    hℓ.eventually (lt_mem_nhds hτ.1)] with n hγn hln
  have hγ : 0 < gammaOf (N n) (B n) := by
    unfold gammaOf
    exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)
  have hlr : 0 < (ℓ n : ℝ) := (div_pos_iff_of_pos_right hγ).mp hln
  have hl : 0 ≤ ℓ n := by exact_mod_cast hlr.le
  have hcast : ((ℓ n).toNat : ℝ) = (ℓ n : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hl
  intro p hp m₂ hm₂
  have hap := (hab p hp).1
  have hga : 1 + max C₀ 0 ≤ gammaOf (N n) (B n) * a :=
    (div_le_iff₀ ha0).mp hγn
  have hm₁ : 1 ≤ gammaOf (N n) (B n) * p := by
    nlinarith [mul_le_mul_of_nonneg_left hap hγ.le, le_max_right C₀ 0]
  have hm₂' : 1 ≤ m₂ := by
    have hh := (abs_le.mp hm₂).1
    have := le_max_left C₀ 0
    nlinarith [mul_le_mul_of_nonneg_left hap hγ.le]
  obtain ⟨hq₁, hr₁⟩ := vsh_Qm R.hβ0 R.hβ1 (by linarith : 0 < gammaOf (N n) (B n) * p)
  obtain ⟨hq₂, hr₂⟩ := vsh_Qm R.hβ0 R.hβ1 (by linarith : 0 < m₂)
  have hpow : 0 < β ^ (2 * (ℓ n).toNat) * Qm β m₂ := mul_pos (pow_pos R.hβ0 _) hq₂
  have hrat : 0 < Qm β (gammaOf (N n) (B n) * p) /
      (β ^ (2 * (ℓ n).toNat) * Qm β m₂) := div_pos hq₁ hpow
  have hlog : Real.log (Qm β (gammaOf (N n) (B n) * p) /
      (β ^ (2 * (ℓ n).toNat) * Qm β m₂)) ≤ L := by
    rw [Real.log_div hq₁.ne' hpow.ne', Real.log_mul (pow_pos R.hβ0 _).ne' hq₂.ne',
      Real.log_pow]
    push_cast
    rw [hcast]
    have h₁ := (abs_le.mp (hCQ _ hm₁)).2
    have h₂ := (abs_le.mp (hCQ _ hm₂')).1
    have hb : Real.log β = -|Real.log β| := by
      rw [abs_of_neg (Real.log_neg R.hβ0 R.hβ1)]; ring
    have hh : gammaOf (N n) (B n) * p - m₂ + (ℓ n : ℝ) ≤ max C₀ 0 := by
      have := (abs_le.mp hm₂).1
      linarith [le_max_left C₀ 0]
    rw [hb]
    dsimp [L]
    nlinarith [le_abs_self CQ, mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2 * |Real.log β|)]
  have hratle : Qm β (gammaOf (N n) (B n) * p) ≤
      Real.exp L * (β ^ (2 * (ℓ n).toNat) * Qm β m₂) := by
    apply (div_le_iff₀ hpow).mp
    calc _ = Real.exp (Real.log (Qm β (gammaOf (N n) (B n) * p) /
          (β ^ (2 * (ℓ n).toNat) * Qm β m₂))) := (Real.exp_log hrat).symm
      _ ≤ Real.exp L := Real.exp_le_exp.mpr hlog
  have hdef := vsh_M_deficit R.hβ0 R.hβ1 hq₁ hq₂ (ℓ n).toNat
    (Real.one_le_exp_iff.mpr hL) hratle
  rw [hr₁] at hdef
  have hEb : Efun β (gammaOf (N n) (B n) * p) ≤ CE :=
    (hE _ (by linarith)).2.trans
      (mul_le_of_le_one_right (hcE.le.trans hcCE) (min_le_right _ _))
  simp only [MLag, if_pos hl]
  exact hdef.trans (mul_le_mul_of_nonneg_left hEb (Real.exp_pos L).le)

/-- Exact finite-dimensional divided difference for the participation product. -/
private lemma vsh_TN_identity {N B : ℕ} (μ : Fin N → ℝ) (hN : 0 < N) (hB : 0 < B)
    (hμ : ∀ j, 0 < μ j) {u v : ℝ} (hu : u ∈ Ioo 0 (gammaOf N B))
    (hv : v ∈ Ioo 0 (gammaOf N B)) :
    TNpart B μ u v * (partLam B μ v - partLam B μ u) =
      partLam B μ v * u - partLam B μ u * v := by
  have heu := (def_app_pl_participation_bij μ hB hN hμ).1.surjOn hu
  have hev := (def_app_pl_participation_bij μ hB hN hμ).1.surjOn hv
  have hLu : 0 < partLam B μ u := Function.invFunOn_mem heu
  have hLv : 0 < partLam B μ v := Function.invFunOn_mem hev
  have hsu : partMN B μ (partLam B μ u) = u := Function.invFunOn_eq heu
  have hsv : partMN B μ (partLam B μ v) = v := Function.invFunOn_eq hev
  have hsu' : (B : ℝ)⁻¹ * ∑ j, partF B μ j u = u := by simpa [partMN, partF] using hsu
  have hsv' : (B : ℝ)⁻¹ * ∑ j, partF B μ j v = v := by simpa [partMN, partF] using hsv
  calc TNpart B μ u v * (partLam B μ v - partLam B μ u) =
      (B : ℝ)⁻¹ * ∑ j, (partLam B μ v * partF B μ j u - partLam B μ u * partF B μ j v) := by
        unfold TNpart
        rw [mul_assoc, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        have hμj := hμ j
        have hd₁ : 0 < 1 + partLam B μ u * μ j := by positivity
        have hd₂ : 0 < 1 + partLam B μ v * μ j := by positivity
        unfold partF
        field_simp
        <;> ring
    _ = partLam B μ v * ((B : ℝ)⁻¹ * ∑ j, partF B μ j u) -
        partLam B μ u * ((B : ℝ)⁻¹ * ∑ j, partF B μ j v) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          ring
    _ = _ := by rw [hsu', hsv']

/-- Continuity of the inverse continuum participation map. -/
private lemma vsh_contV_cont {α : ℝ} (hα : 0 < α) :
    ContinuousOn (contV α) (Ioo (0 : ℝ) 1) := by
  intro a ha
  apply ContinuousAt.continuousWithinAt
  have hs : Ioo (0 : ℝ) 1 ∈ 𝓝 a := Ioo_mem_nhds ha.1 ha.2
  have hmono : MonotoneOn (contV α) (Ioo (0 : ℝ) 1) :=
    fun p hp q hq hpq => vs_contV_le hα hp hq hpq
  refine continuousAt_of_monotoneOn_of_image_mem_nhds hmono hs ?_
  have himg : contV α '' Ioo (0 : ℝ) 1 = Ioi 0 := by
    ext V
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (vs_contV_spec hα hp).1
    · intro hV
      have hm := (def_app_pl_profiles_S_bij hα).2.mapsTo hV
      refine ⟨contS α V, hm, ?_⟩
      have h := vs_contV_spec hα hm
      exact (def_app_pl_profiles_S_bij hα).1.injOn h.1 hV h.2
  rw [himg]
  exact Ioi_mem_nhds (vs_contV_spec hα ha).1

/-- Finite inverse convergence also holds at moving interior arguments. -/
private lemma vsh_finV_tendsto {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) {p : ℝ} (hp : p ∈ Ioo 0 1)
    (pn : ℕ → ℝ) (hpn : Tendsto pn atTop (𝓝 p)) :
    Tendsto (fun n => finV α (N n) (pn n)) atTop (𝓝 (contV α p)) := by
  obtain ⟨C, hC⟩ := lem_app_pl_finite_inverse_ii R.hα
  have hpi : Tendsto (fun n => 1 / gammaOf (N n) (B n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop R.hγ
  have hC0 : Tendsto (fun n => C / (B n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop R.hB
  have hmem : ∀ᶠ n in atTop, pn n ∈ Ioo (0 : ℝ) 1 :=
    hpn.eventually (Ioo_mem_nhds hp.1 hp.2)
  have hlow : ∀ᶠ n in atTop, 1 / gammaOf (N n) (B n) ≤ pn n :=
    (hpi.eventually_lt hpn hp.1).mono fun n hn => hn.le
  have hupp : ∀ᶠ n in atTop, pn n ≤ 1 - 1 / gammaOf (N n) (B n) := by
    have hh : Tendsto (fun n => 1 - 1 / gammaOf (N n) (B n)) atTop (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.sub hpi
    exact (hpn.eventually_lt hh hp.2).mono fun n hn => hn.le
  have hlog : Tendsto (fun n => Real.log (finV α (N n) (pn n) / contV α (pn n)))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hC0
    filter_upwards [hlow, hupp, R.hB.eventually_ge_atTop 2] with n hn hn' hBn
    have hB2 : 2 ≤ B n := by exact_mod_cast hBn
    simpa [Real.norm_eq_abs] using hC (N n) (B n) 1 (pn n) (R.hNpos n) hB2 le_rfl hn hn'
  have hr : Tendsto (fun n => finV α (N n) (pn n) / contV α (pn n)) atTop (𝓝 1) := by
    have he := Real.continuous_exp.continuousAt.tendsto.comp hlog
    simp only [Real.exp_zero] at he
    apply he.congr'
    filter_upwards [hmem] with n hn
    have hfin := (vs_partF_eq (α := α) (c := c n) (R.hNpos n) (R.hBpos n)
      (R.hcpos n) ⟨0, R.hNpos n⟩ hn).1
    exact Real.exp_log (div_pos hfin (vs_contV_spec R.hα hn).1)
  have hc := ((vsh_contV_cont R.hα).continuousAt (Ioo_mem_nhds hp.1 hp.2)).tendsto.comp hpn
  have hh := hr.mul hc
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [hmem] with n hn
  exact div_mul_cancel₀ _ (vs_contV_spec R.hα hn).1.ne'

/-- Normalized divided difference in finite inverse coordinates. -/
private lemma vsh_TN_normalized {α c : ℝ} {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) {p q : ℝ} (hp : p ∈ Ioo 0 1) (hq : q ∈ Ioo 0 1)
    (hne : finV α N q - finV α N p ≠ 0) :
    TNpart B (plSpec α c N) (gammaOf N B * p) (gammaOf N B * q) / gammaOf N B =
      (finV α N q * p - finV α N p * q) / (finV α N q - finV α N p) := by
  have hγ : 0 < gammaOf N B := by
    unfold gammaOf; exact div_pos (by exact_mod_cast hN) (by exact_mod_cast hB)
  have hμ : ∀ j, 0 < plSpec α c N j := fun j => by
    unfold plSpec; exact mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)
  have hmp : gammaOf N B * p ∈ Ioo 0 (gammaOf N B) :=
    ⟨mul_pos hγ hp.1, mul_lt_of_lt_one_right hγ hp.2⟩
  have hmq : gammaOf N B * q ∈ Ioo 0 (gammaOf N B) :=
    ⟨mul_pos hγ hq.1, mul_lt_of_lt_one_right hγ hq.2⟩
  have hid := vsh_TN_identity (plSpec α c N) hN hB hμ hmp hmq
  have hVp := eqn_app_pl_Lambda_V α c hN hB hc hmp
  have hVq := eqn_app_pl_Lambda_V α c hN hB hc hmq
  rw [show gammaOf N B * p / gammaOf N B = p by field_simp] at hVp
  rw [show gammaOf N B * q / gammaOf N B = q by field_simp] at hVq
  rw [hVp, hVq] at hid
  have hA : (N : ℝ) ^ α / c ≠ 0 := by
    exact (div_pos (Real.rpow_pos_of_pos (by exact_mod_cast hN) α) hc).ne'
  apply (eq_div_iff hne).2
  rw [div_mul_eq_mul_div, div_eq_iff hγ.ne']
  apply mul_left_cancel₀ hA
  linear_combination hid

/-- Sequential convergence of the normalized participation product. -/
private lemma vsh_TN_seq {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) {p q : ℝ} (hp : p ∈ Ioo 0 1)
    (hq : q ∈ Ioo 0 1) (hpq : p < q) (pn qn : ℕ → ℝ)
    (hpn : Tendsto pn atTop (𝓝 p)) (hqn : Tendsto qn atTop (𝓝 q)) :
    Tendsto (fun n => TNpart (B n) (plSpec α (c n) (N n))
        (gammaOf (N n) (B n) * pn n) (gammaOf (N n) (B n) * qn n) / gammaOf (N n) (B n))
      atTop (𝓝 (profTc α p q)) := by
  have hV := vsh_finV_tendsto R hp pn hpn
  have hW := vsh_finV_tendsto R hq qn hqn
  have hne : contV α q - contV α p ≠ 0 := (sub_pos.mpr (vs_contV_lt R.hα hp hq hpq)).ne'
  have hh := ((hW.mul hpn).sub (hV.mul hqn)).div (hW.sub hV) hne
  apply hh.congr'
  filter_upwards [hpn.eventually (Ioo_mem_nhds hp.1 hp.2),
    hqn.eventually (Ioo_mem_nhds hq.1 hq.2),
    (hW.sub hV).eventually (isOpen_ne.mem_nhds hne)] with n hn hn' hnen
  exact (vsh_TN_normalized (R.hNpos n) (R.hBpos n) (R.hcpos n) hn hn' hnen).symm

/-- Continuity of the continuum divided difference off its diagonal. -/
private lemma vsh_Tc_seq {α p q : ℝ} (hα : 0 < α) (hp : p ∈ Ioo 0 1)
    (hq : q ∈ Ioo 0 1) (hpq : p < q) {pn qn : ℕ → ℝ}
    (hpn : Tendsto pn atTop (𝓝 p)) (hqn : Tendsto qn atTop (𝓝 q)) :
    Tendsto (fun n => profTc α (pn n) (qn n)) atTop (𝓝 (profTc α p q)) := by
  have hV := ((vsh_contV_cont hα).continuousAt (Ioo_mem_nhds hp.1 hp.2)).tendsto.comp hpn
  have hW := ((vsh_contV_cont hα).continuousAt (Ioo_mem_nhds hq.1 hq.2)).tendsto.comp hqn
  exact ((hW.mul hpn).sub (hV.mul hqn)).div (hW.sub hV)
    (sub_pos.mpr (vs_contV_lt hα hp hq hpq)).ne'

/-- The two shell limits along a convergent sequence of shell coordinates. -/
private lemma vsh_shell_seq {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) (ℓ : ℕ → ℤ)
    (hℓ : Tendsto (fun n => (ℓ n : ℝ) / gammaOf (N n) (B n)) atTop (𝓝 τ))
    (K : Set ℝ) (hK : K ⊆ Ioo 0 (1 - τ)) (hKc : IsCompact K)
    (pn mn : ℕ → ℝ) (hpnK : ∀ n, pn n ∈ K) {p : ℝ} (hp : p ∈ K)
    (hpn : Tendsto pn atTop (𝓝 p)) (C₀ : ℝ)
    (hshell : ∀ n, |mn n - (gammaOf (N n) (B n) * pn n + (ℓ n : ℝ))| ≤ C₀) :
    Tendsto (fun n => TNpart (B n) (plSpec α (c n) (N n))
        (gammaOf (N n) (B n) * pn n) (mn n) / gammaOf (N n) (B n))
      atTop (𝓝 (profTc α p (p + τ))) ∧
    Tendsto (fun n => deltaN β (B n) (plSpec α (c n) (N n)) (ℓ n)
        (gammaOf (N n) (B n) * pn n) (mn n)) atTop (𝓝 (profDeltaC α p (p + τ))) := by
  let γ := fun n => gammaOf (N n) (B n)
  let qn := fun n => mn n / γ n
  let M := fun n => MLag β (Qm β (γ n * pn n)) (Qm β (mn n)) (ℓ n)
  let D := fun n => DLag β (Qm β (γ n * pn n)) (Qm β (mn n)) (ℓ n)
  let T := fun n => TNpart (B n) (plSpec α (c n) (N n)) (γ n * pn n) (mn n)
  have hγ : ∀ n, 0 < γ n := fun n => by
    dsimp [γ, gammaOf]
    exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)
  have hp0 : p ∈ Ioo (0 : ℝ) 1 := ⟨(hK hp).1, by linarith [(hK hp).2, hτ.1]⟩
  have hq0 : p + τ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp0.1, hτ.1], by linarith [(hK hp).2]⟩
  have he : Tendsto (fun n => qn n - (pn n + (ℓ n : ℝ) / γ n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ (tendsto_const_nhds.div_atTop R.hγ (a := C₀))
    exact Filter.Eventually.of_forall fun n => by
      have heq : qn n - (pn n + (ℓ n : ℝ) / γ n) =
          (mn n - (γ n * pn n + (ℓ n : ℝ))) / γ n := by dsimp [qn]; field_simp [(hγ n).ne']
      rw [Real.norm_eq_abs, heq, abs_div, abs_of_pos (hγ n)]
      exact div_le_div_of_nonneg_right (hshell n) (hγ n).le
  have hqn : Tendsto qn atTop (𝓝 (p + τ)) := by
    simpa only [γ, sub_add_cancel, zero_add] using he.add (hpn.add hℓ)
  have hTN : Tendsto (fun n => T n / γ n) atTop (𝓝 (profTc α p (p + τ))) := by
    have hh := vsh_TN_seq R hp0 hq0 (by linarith [hτ.1]) pn qn hpn hqn
    simpa [T, γ, qn, mul_div_cancel₀ _ (hγ _).ne'] using hh
  refine ⟨hTN, ?_⟩
  obtain ⟨C₁, hC₁⟩ := shell_MLag_bound R hτ ℓ hℓ K hK hKc C₀
  have hdef : Tendsto (fun n => pn n - M n / γ n) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ (tendsto_const_nhds.div_atTop R.hγ (a := C₁))
    filter_upwards [hC₁] with n hn
    have heq : pn n - M n / γ n = (γ n * pn n - M n) / γ n := by field_simp [(hγ n).ne']
    rw [Real.norm_eq_abs, heq, abs_div, abs_of_pos (hγ n)]
    exact div_le_div_of_nonneg_right (hn _ (hpnK n) _ (hshell n)) (hγ n).le
  have hM : Tendsto (fun n => M n / γ n) atTop (𝓝 p) := by
    simpa only [sub_sub_cancel, sub_zero] using hpn.sub hdef
  have hmem : ∀ᶠ n in atTop, pn n ∈ Ioo (0 : ℝ) 1 ∧ qn n ∈ Ioo (0 : ℝ) 1 :=
    (hpn.eventually (Ioo_mem_nhds hp0.1 hp0.2)).and (hqn.eventually (Ioo_mem_nhds hq0.1 hq0.2))
  have hD : Tendsto (fun n => D n ^ 2 / γ n ^ 2) atTop (𝓝 0) := by
    have hup : Tendsto (fun n => (pn n - M n / γ n) * (qn n - M n / γ n)) atTop (𝓝 0) := by
      simpa using (hpn.sub hM).mul (hqn.sub hM)
    apply squeeze_zero' (Filter.Eventually.of_forall fun n => div_nonneg (sq_nonneg _) (sq_nonneg _)) ?_ hup
    filter_upwards [hmem] with n hn
    have h₁ : γ n * pn n ∈ Ioo 0 (gammaOf (N n) (B n)) :=
      ⟨mul_pos (hγ n) hn.1.1, mul_lt_of_lt_one_right (hγ n) hn.1.2⟩
    have h₂ : mn n ∈ Ioo 0 (gammaOf (N n) (B n)) := by
      have heq : mn n = γ n * qn n := by dsimp [qn]; field_simp [(hγ n).ne']
      rw [heq]
      exact ⟨mul_pos (hγ n) hn.2.1, mul_lt_of_lt_one_right (hγ n) hn.2.2⟩
    have hd := (lem_app_pl_determinant_i R.hα R.hβ0 R.hβ1 (N n) (B n) (c n)
      (R.hNpos n) (R.hBpos n) (R.hcpos n) (ℓ n) _ _ h₁ h₂).2.2
    convert div_le_div_of_nonneg_right hd (sq_nonneg (γ n)) using 1
    dsimp [D, M, qn]
    field_simp [(hγ n).ne']
    <;> ring
  have hne : p * (p + τ) ≠ 0 := (mul_pos hp0.1 hq0.1).ne'
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hlim := ((hone.sub ((hTN.mul hM).div (hpn.mul hqn) hne)).mul
    (hone.sub hM)).sub ((hTN.mul hD).div (hpn.mul hqn) hne)
  have hlimval : (1 - profTc α p (p + τ) * p / (p * (p + τ))) * (1 - p) -
      profTc α p (p + τ) * 0 / (p * (p + τ)) = profDeltaC α p (p + τ) := by
    unfold profDeltaC
    field_simp [hp0.1.ne', hq0.1.ne']
    <;> ring
  rw [hlimval] at hlim
  apply hlim.congr'
  filter_upwards [hmem] with n hn
  dsimp only [Pi.div_apply, T, D, M, qn, γ]
  unfold deltaN
  have hγn : gammaOf (N n) (B n) ≠ 0 := (hγ n).ne'
  field_simp [hγn]
  <;> ring

/-- `𝖳_N/γ → t(p,p')` and `Δ^N_ℓ → Δ_c(p,p')` with `p' = p + τ`, uniformly on the shell
(task L-G.7b; proof step of `thm:app-pl-volatility`(i), l.2215-2221; snapshot cr-2026-10-23). -/
theorem shell_TN_delta_tendsto {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) (ℓ : ℕ → ℤ)
    (hℓ : Tendsto (fun n => (ℓ n : ℝ) / gammaOf (N n) (B n)) atTop (𝓝 τ))
    (K : Set ℝ) (hK : K ⊆ Ioo 0 (1 - τ)) (hKc : IsCompact K) (C₀ : ℝ) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ p ∈ K, ∀ m₂ : ℝ,
      |m₂ - (gammaOf (N n) (B n) * p + (ℓ n : ℝ))| ≤ C₀ →
        |TNpart (B n) (plSpec α (c n) (N n)) (gammaOf (N n) (B n) * p) m₂ / gammaOf (N n) (B n) -
            profTc α p (p + τ)| ≤ ε ∧
        |deltaN β (B n) (plSpec α (c n) (N n)) (ℓ n) (gammaOf (N n) (B n) * p) m₂ -
            profDeltaC α p (p + τ)| ≤ ε := by
  classical
  intro ε hε
  by_contra hbad
  have hex : ∀ j : ℕ, ∃ n, j ≤ n ∧ ∃ p ∈ K, ∃ m₂ : ℝ,
      |m₂ - (gammaOf (N n) (B n) * p + (ℓ n : ℝ))| ≤ C₀ ∧
      ¬ (|TNpart (B n) (plSpec α (c n) (N n)) (gammaOf (N n) (B n) * p) m₂ /
            gammaOf (N n) (B n) - profTc α p (p + τ)| ≤ ε ∧
        |deltaN β (B n) (plSpec α (c n) (N n)) (ℓ n)
            (gammaOf (N n) (B n) * p) m₂ - profDeltaC α p (p + τ)| ≤ ε) := by
    have hf := frequently_atTop.mp (not_eventually.mp hbad)
    intro j
    obtain ⟨n, hjn, hn⟩ := hf j
    simp only [not_forall] at hn
    obtain ⟨p, hp, m, hm, hfail⟩ := hn
    exact ⟨n, hjn, p, hp, m, hm, hfail⟩
  choose ns hns pn hpnK mn hshell hfail using hex
  obtain ⟨p, hp, φ, hφ, hconv⟩ := hKc.tendsto_subseq hpnK
  have hnsTop : Tendsto ns atTop atTop := tendsto_atTop_mono hns tendsto_id
  have hsub : Tendsto (ns ∘ φ) atTop atTop := hnsTop.comp hφ.tendsto_atTop
  let R' : assum_app_pl_regime α β (N ∘ ns ∘ φ) (B ∘ ns ∘ φ) (c ∘ ns ∘ φ) :=
    { hα := R.hα, hβ0 := R.hβ0, hβ1 := R.hβ1
      hNpos := fun j => R.hNpos _, hBpos := fun j => R.hBpos _, hcpos := fun j => R.hcpos _
      hN := R.hN.comp hsub, hB := R.hB.comp hsub, hγ := R.hγ.comp hsub }
  have hℓ' : Tendsto (fun j => ((ℓ (ns (φ j))) : ℝ) /
      gammaOf (N (ns (φ j))) (B (ns (φ j)))) atTop (𝓝 τ) := hℓ.comp hsub
  obtain ⟨hTN, hDelta⟩ := vsh_shell_seq R' hτ (ℓ ∘ ns ∘ φ) hℓ' K hK hKc
    (pn ∘ φ) (mn ∘ φ) (fun j => hpnK (φ j)) hp hconv C₀ (fun j => hshell (φ j))
  have hp0 : p ∈ Ioo (0 : ℝ) 1 := ⟨(hK hp).1, by linarith [(hK hp).2, hτ.1]⟩
  have hq0 : p + τ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp0.1, hτ.1], by linarith [(hK hp).2]⟩
  have hconvq : Tendsto (fun j => pn (φ j) + τ) atTop (𝓝 (p + τ)) := hconv.add_const τ
  have hTc := vsh_Tc_seq R.hα hp0 hq0 (by linarith [hτ.1]) hconv hconvq
  have hDc : Tendsto (fun j => profDeltaC α (pn (φ j)) (pn (φ j) + τ))
      atTop (𝓝 (profDeltaC α p (p + τ))) := by
    unfold profDeltaC
    exact (tendsto_const_nhds.sub hconv).mul
      (tendsto_const_nhds.sub (hTc.div hconvq hq0.1.ne'))
  have he₁ := hTN.sub hTc
  have he₂ := hDelta.sub hDc
  simp only [sub_self] at he₁ he₂
  have hev₁ := he₁.abs.eventually (gt_mem_nhds (show |(0 : ℝ)| < ε by simpa using hε))
  have hev₂ := he₂.abs.eventually (gt_mem_nhds (show |(0 : ℝ)| < ε by simpa using hε))
  obtain ⟨j, hj₁, hj₂⟩ := (hev₁.and hev₂).exists
  exact hfail (φ j) ⟨hj₁.le, hj₂.le⟩

/-- Private: localization after changing both integration variables to the scale `s n`. -/
private lemma vsh_localization_scaled {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (s : ℕ → ℝ) (ℓ : ℕ → ℤ) (hs : ∀ n, 0 < s n) (hsT : Tendsto s atTop atTop)
    {τ : ℝ} (hτ : 0 < τ)
    (hℓ : Tendsto (fun n => (ℓ n : ℝ) / s n) atTop (𝓝 τ))
    (φ : ℝ × ℝ → ℝ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hφsupp : tsupport φ ⊆ Ioi 0 ×ˢ Ioi 0) :
    Tendsto (fun n => ∫ p : ℝ × ℝ, φ p * s n *
      DLag β (Qm β (s n * p.1)) (Qm β (s n * p.2)) (ℓ n) /
        (Real.pi ^ 2 * Efun β (s n * p.1) * Efun β (s n * p.2)))
      atTop (𝓝 (∫ r : ℝ, φ (r, r + τ))) := by
  have hγ : Tendsto (fun n => (s n * s n) / s n) atTop atTop := by
    convert hsT using 1
    funext n
    exact mul_div_cancel_right₀ _ (hs n).ne'
  have hloc := (lem_app_pl_localization_iii_top hβ0 hβ1
    (fun n => s n * s n) ℓ s hs hsT hτ hγ hℓ φ hφc hφs hφsupp).2
  refine hloc.congr' (Filter.Eventually.of_forall fun n => ?_)
  let f : ℝ × ℝ → ℝ := fun p => φ (p.1 / s n, p.2 / s n) *
    DLag β (Qm β p.1) (Qm β p.2) (ℓ n) /
      (Real.pi ^ 2 * s n * Efun β p.1 * Efun β p.2)
  have hscale := Measure.integral_comp_smul (μ := (volume : Measure (ℝ × ℝ))) f (s n)
  have hdim : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  rw [hdim, abs_of_pos (inv_pos.mpr (pow_pos (hs n) 2)), smul_eq_mul] at hscale
  have he : ∫ p : ℝ × ℝ, f p = (s n) ^ 2 * ∫ p : ℝ × ℝ, f (s n • p) := by
    rw [hscale]
    field_simp [(hs n).ne']
  change (∫ p : ℝ × ℝ, f p) = _
  rw [he, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with p
  dsimp [f]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    mul_div_cancel_left₀ _ (hs n).ne']
  field_simp
  <;> ring

private lemma vsh_localization_scaled_integrable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (s : ℕ → ℝ) (ℓ : ℕ → ℤ) (hs : ∀ n, 0 < s n) (hsT : Tendsto s atTop atTop)
    {τ : ℝ} (hτ : 0 < τ)
    (hℓ : Tendsto (fun n => (ℓ n : ℝ) / s n) atTop (𝓝 τ))
    (φ : ℝ × ℝ → ℝ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hφsupp : tsupport φ ⊆ Ioi 0 ×ˢ Ioi 0) (n : ℕ) :
    Integrable (fun p : ℝ × ℝ => φ p * s n *
      DLag β (Qm β (s n * p.1)) (Qm β (s n * p.2)) (ℓ n) /
        (Real.pi ^ 2 * Efun β (s n * p.1) * Efun β (s n * p.2))) := by
  have hγ : Tendsto (fun n => (s n * s n) / s n) atTop atTop := by
    convert hsT using 1
    funext j
    exact mul_div_cancel_right₀ _ (hs j).ne'
  have hi := (lem_app_pl_localization_iii_top hβ0 hβ1
    (fun n => s n * s n) ℓ s hs hsT hτ hγ hℓ φ hφc hφs hφsupp).1 n
  let f : ℝ × ℝ → ℝ := fun p => φ (p.1 / s n, p.2 / s n) *
    DLag β (Qm β p.1) (Qm β p.2) (ℓ n) /
      (Real.pi ^ 2 * s n * Efun β p.1 * Efun β p.2)
  have hfi : Integrable f := hi
  have hc := (hfi.comp_smul (hs n).ne').const_mul ((s n) ^ 2)
  apply hc.congr
  filter_upwards with p
  dsimp [f]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    mul_div_cancel_left₀ _ (hs n).ne']
  field_simp
  <;> ring

private lemma vsh_DLag_nonneg {β : ℝ} (hβ0 : 0 < β) {q₁ q₂ : ℝ}
    (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) (l : ℤ) : 0 ≤ DLag β q₁ q₂ l := by
  have hn : ∀ (u v : ℝ), 0 ≤ u → 0 ≤ v → ∀ a : ℕ, 0 ≤ DLagNat β u v a := by
    intro u v hu hv a
    unfold DLagNat
    refine tsum_nonneg fun j => integral_nonneg fun g => ?_
    positivity
  unfold DLag
  split_ifs
  · exact hn q₁ q₂ hq₁ hq₂ _
  · exact hn q₂ q₁ hq₂ hq₁ _

/-- Private: explicit continuous trapezoids used to sandwich an interval indicator. -/
private lemma vsh_trap_exists (l u ε : ℝ) (hε : 0 < ε) :
    ∃ f : ℝ → ℝ, Continuous f ∧ HasCompactSupport f ∧ tsupport f ⊆ Icc l u ∧
      (∀ x, f x ∈ Icc 0 1) ∧
      f l = 0 ∧ f u = 0 ∧
      ∀ x, l + ε ≤ x → x ≤ u - ε → f x = 1 := by
  let f : ℝ → ℝ := fun x =>
    max 0 (min 1 ((x - l) / ε)) * max 0 (min 1 ((u - x) / ε))
  have hfc : Continuous f := by
    dsimp [f]
    fun_prop
  have hfmem : ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
    intro x
    have h₁ : max 0 (min 1 ((x - l) / ε)) ∈ Icc (0 : ℝ) 1 := by
      exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
    have h₂ : max 0 (min 1 ((u - x) / ε)) ∈ Icc (0 : ℝ) 1 := by
      exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
    refine ⟨mul_nonneg h₁.1 h₂.1, ?_⟩
    calc
      _ ≤ 1 * 1 := mul_le_mul h₁.2 h₂.2 h₂.1 zero_le_one
      _ = 1 := one_mul 1
  have hfzero : ∀ x ∉ Icc l u, f x = 0 := by
    intro x hx
    rw [Set.mem_Icc, not_and_or] at hx
    rcases hx with hx | hx
    · have hq : (x - l) / ε < 0 :=
        div_neg_of_neg_of_pos (sub_neg.mpr (lt_of_not_ge hx)) hε
      dsimp [f]
      rw [max_eq_left (min_le_of_right_le hq.le)]
      simp
    · have hq : (u - x) / ε < 0 :=
        div_neg_of_neg_of_pos (sub_neg.mpr (lt_of_not_ge hx)) hε
      dsimp [f]
      rw [max_eq_left (min_le_of_right_le hq.le)]
      ring
  have hfts : tsupport f ⊆ Icc l u := by
    rw [tsupport, isClosed_Icc.closure_subset_iff]
    intro x hx
    by_contra h
    exact hx (hfzero x h)
  refine ⟨f, hfc,
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hfts, hfts, hfmem, ?_, ?_, ?_⟩
  · simp [f]
  · simp [f]
  intro x hxl hxu
  have h₁ : 1 ≤ (x - l) / ε := (le_div_iff₀ hε).2 (by linarith)
  have h₂ : 1 ≤ (u - x) / ε := (le_div_iff₀ hε).2 (by linarith)
  simp [f, min_eq_left h₁, min_eq_left h₂]

/-- Private: a two-parameter squeeze in which the outer approximation is removed afterwards. -/
private lemma vsh_tendsto_of_sandwich (f : ℕ → ℝ) (lo hi : ℕ → ℕ → ℝ)
    (loLim hiLim : ℕ → ℝ) (L : ℝ)
    (hlo : ∀ k, Tendsto (lo k) atTop (𝓝 (loLim k)))
    (hhi : ∀ k, Tendsto (hi k) atTop (𝓝 (hiLim k)))
    (hloL : Tendsto loLim atTop (𝓝 L)) (hhiL : Tendsto hiLim atTop (𝓝 L))
    (hord : ∀ k, ∀ᶠ n in atTop, lo k n ≤ f n ∧ f n ≤ hi k n) :
    Tendsto f atTop (𝓝 L) := by
  rw [tendsto_order]
  constructor
  · intro z hz
    obtain ⟨k, hk⟩ := (hloL.eventually (Ioi_mem_nhds hz)).exists
    filter_upwards [(hlo k).eventually (Ioi_mem_nhds hk), hord k] with n hn horder
    exact hn.trans_le horder.1
  · intro z hz
    obtain ⟨k, hk⟩ := (hhiL.eventually (Iio_mem_nhds hz)).exists
    filter_upwards [(hhi k).eventually (Iio_mem_nhds hk), hord k] with n hn horder
    exact horder.2.trans_lt hn

/-- Private: abstract upper inequality for the shell/off-shell split. -/
private lemma vsh_ineq_upper {D S0 : Set (ℝ × ℝ)} (hS0 : MeasurableSet S0)
    {F κ ψ : ℝ × ℝ → ℝ} {M η : ℝ} (hF : IntegrableOn F D) (hκD : IntegrableOn κ D)
    (hψ : Integrable ψ) (hψ0 : ∀ m, 0 ≤ ψ m) (hκ0 : ∀ m ∈ D, 0 ≤ κ m)
    (hFb : ∀ m ∈ D, |F m| ≤ M * κ m) (hsh : ∀ m ∈ D ∩ S0, F m ≤ ψ m)
    (hoff : ∫ m in D \ S0, κ m ≤ η) (hM : 0 ≤ M) (hD : MeasurableSet D) :
    ∫ m in D, F m ≤ (∫ m, ψ m) + M * η := by
  have hsplit := integral_inter_add_sdiff hS0 hF
  have hFsh : IntegrableOn F (D ∩ S0) := hF.mono_set inter_subset_left
  have hFoff : IntegrableOn F (D \ S0) := hF.mono_set sdiff_subset
  have hκoff : IntegrableOn κ (D \ S0) := hκD.mono_set sdiff_subset
  have h1 : ∫ m in D ∩ S0, F m ≤ ∫ m in D ∩ S0, ψ m :=
    setIntegral_mono_on hFsh hψ.integrableOn (hD.inter hS0) hsh
  have h2 : ∫ m in D ∩ S0, ψ m ≤ ∫ m, ψ m :=
    setIntegral_le_integral hψ (Filter.Eventually.of_forall hψ0)
  have h3 : ∫ m in D \ S0, F m ≤ M * η := by
    have := norm_integral_le_of_norm_le (hκoff.const_mul M) (μ := volume.restrict (D \ S0))
      (f := F) (g := fun m => M * κ m)
      ((ae_restrict_iff' (hD.diff hS0)).2 (Filter.Eventually.of_forall fun m hm => by
        simpa [Real.norm_eq_abs] using hFb m hm.1))
    rw [integral_const_mul] at this
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this) |>.trans
      (mul_le_mul_of_nonneg_left hoff hM)
  linarith

/-- Private: abstract lower inequality for the shell/off-shell split. -/
private lemma vsh_ineq_lower {D S0 : Set (ℝ × ℝ)} (hS0 : MeasurableSet S0)
    {F κ ψ : ℝ × ℝ → ℝ} {M H η : ℝ} (hF : IntegrableOn F D) (hκD : IntegrableOn κ D)
    (hψ : Integrable ψ) (hκ0 : ∀ m ∈ D, 0 ≤ κ m)
    (hFb : ∀ m ∈ D, |F m| ≤ M * κ m) (hψD : ∀ m ∉ D, ψ m = 0)
    (hsh : ∀ m ∈ D ∩ S0, ψ m ≤ F m) (hψb : ∀ m ∈ D \ S0, ψ m ≤ H * κ m)
    (hoff : ∫ m in D \ S0, κ m ≤ η) (hM : 0 ≤ M) (hH : 0 ≤ H) (hD : MeasurableSet D) :
    (∫ m, ψ m) - H * η - M * η ≤ ∫ m in D, F m := by
  have hsplit := integral_inter_add_sdiff hS0 hF
  have hFsh : IntegrableOn F (D ∩ S0) := hF.mono_set inter_subset_left
  have hFoff : IntegrableOn F (D \ S0) := hF.mono_set sdiff_subset
  have hκoff : IntegrableOn κ (D \ S0) := hκD.mono_set sdiff_subset
  have hψint : ∫ m in D, ψ m = ∫ m, ψ m :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hψD
  have hψsplit := integral_inter_add_sdiff hS0 (hψ.integrableOn (s := D))
  have h1 : ∫ m in D ∩ S0, ψ m ≤ ∫ m in D ∩ S0, F m :=
    setIntegral_mono_on (hψ.integrableOn) hFsh (hD.inter hS0) hsh
  have h2 : ∫ m in D \ S0, ψ m ≤ H * η := by
    have := setIntegral_mono_on (hψ.integrableOn) (hκoff.const_mul H) (hD.diff hS0) hψb
    rw [integral_const_mul] at this
    exact this.trans (mul_le_mul_of_nonneg_left hoff hH)
  have h3 : -(M * η) ≤ ∫ m in D \ S0, F m := by
    have := norm_integral_le_of_norm_le (hκoff.const_mul M) (μ := volume.restrict (D \ S0))
      (f := F) (g := fun m => M * κ m)
      ((ae_restrict_iff' (hD.diff hS0)).2 (Filter.Eventually.of_forall fun m hm => by
        simpa [Real.norm_eq_abs] using hFb m hm.1))
    rw [integral_const_mul] at this
    have h4 := (abs_le.mp (by simpa [Real.norm_eq_abs] using this)).1
    have h5 : M * ∫ m in D \ S0, κ m ≤ M * η := mul_le_mul_of_nonneg_left hoff hM
    linarith
  linarith


/-- Private: a product test function `H(p₁) ζ(p₂ - p₁ - τ)`. -/
private lemma vsh_phi {H ζ : ℝ → ℝ} {l u δ τ : ℝ} (hH : Continuous H) (hζ : Continuous ζ)
    (hHs : tsupport H ⊆ Icc l u) (hζs : tsupport ζ ⊆ Icc (-δ) δ)
    (hl : 0 < l) (hδ : δ < τ) :
    Continuous (fun p : ℝ × ℝ => H p.1 * ζ (p.2 - p.1 - τ)) ∧
    HasCompactSupport (fun p : ℝ × ℝ => H p.1 * ζ (p.2 - p.1 - τ)) ∧
    tsupport (fun p : ℝ × ℝ => H p.1 * ζ (p.2 - p.1 - τ)) ⊆ Ioi 0 ×ˢ Ioi 0 ∧
    (∀ p : ℝ × ℝ, H p.1 * ζ (p.2 - p.1 - τ) ≠ 0 → p.1 ∈ Icc l u ∧ p.2 - p.1 - τ ∈ Icc (-δ) δ) ∧
    (∫ r : ℝ, H r * ζ (r + τ - r - τ)) = ζ 0 * ∫ r, H r := by
  have hcont : Continuous (fun p : ℝ × ℝ => H p.1 * ζ (p.2 - p.1 - τ)) := by fun_prop
  have hsupp : ∀ p : ℝ × ℝ, H p.1 * ζ (p.2 - p.1 - τ) ≠ 0 →
      p.1 ∈ Icc l u ∧ p.2 - p.1 - τ ∈ Icc (-δ) δ := by
    intro p hp
    constructor
    · by_contra h
      exact hp (by rw [image_eq_zero_of_notMem_tsupport (fun h' => h (hHs h')), zero_mul])
    · by_contra h
      exact hp (by rw [image_eq_zero_of_notMem_tsupport (fun h' => h (hζs h')), mul_zero])
  let S : Set (ℝ × ℝ) := (fun q : ℝ × ℝ => (q.1, q.1 + τ + q.2)) '' (Icc l u ×ˢ Icc (-δ) δ)
  have hS : IsCompact S :=
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hsub : Function.support (fun p : ℝ × ℝ => H p.1 * ζ (p.2 - p.1 - τ)) ⊆ S := by
    intro p hp
    obtain ⟨h1, h2⟩ := hsupp p hp
    exact ⟨(p.1, p.2 - p.1 - τ), ⟨h1, h2⟩, by ext <;> simp⟩
  have hts : tsupport (fun p : ℝ × ℝ => H p.1 * ζ (p.2 - p.1 - τ)) ⊆ S :=
    closure_minimal hsub hS.isClosed
  refine ⟨hcont, HasCompactSupport.intro hS (fun p hp => ?_), ?_, hsupp, ?_⟩
  · by_contra h
    exact hp (hsub h)
  · refine hts.trans ?_
    rintro _ ⟨q, ⟨hq1, hq2⟩, rfl⟩
    exact ⟨show 0 < q.1 by linarith [hq1.1], show 0 < q.1 + τ + q.2 by linarith [hq1.1, hq2.1]⟩
  · have : ∀ r : ℝ, H r * ζ (r + τ - r - τ) = ζ 0 * H r := by
      intro r; rw [show r + τ - r - τ = 0 by ring]; ring
    simp_rw [this]
    exact integral_const_mul _ _

/-- Private: abstract sandwich core for the compact-`p` limit (all kernel input abstracted). -/
private lemma vsh_core1 (γ : ℕ → ℝ) (hγ0 : ∀ n, 0 < γ n) (hγT : Tendsto γ atTop atTop)
    (ℓ : ℕ → ℤ) {τ : ℝ} (hτ : 0 < τ)
    (hℓ : Tendsto (fun n => (ℓ n : ℝ) / γ n) atTop (𝓝 τ))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbτ : b + τ < 1)
    (κ : ℕ → ℝ × ℝ → ℝ)
    (hκ0 : ∀ n (m : ℝ × ℝ), 0 < m.1 → 0 < m.2 → 0 ≤ κ n m)
    (hκtest : ∀ φ : ℝ × ℝ → ℝ, Continuous φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioi 0 ×ˢ Ioi 0 →
      (∀ n, Integrable (fun m : ℝ × ℝ => φ (m.1 / γ n, m.2 / γ n) * κ n m)) ∧
      Tendsto (fun n => ∫ m : ℝ × ℝ, φ (m.1 / γ n, m.2 / γ n) * κ n m) atTop
        (𝓝 (∫ r : ℝ, φ (r, r + τ))))
    (hκint : ∀ᶠ n in atTop, IntegrableOn (κ n) (Icc (γ n * a) (γ n * b) ×ˢ Ioo 0 (γ n)))
    (hκoff : ∀ η > 0, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ n in atTop,
      ∫ m in Icc (γ n * a) (γ n * b) ×ˢ Ioo 0 (γ n) \ {m : ℝ × ℝ | |m.1 - m.2 + ℓ n| ≤ C₀},
        κ n m ≤ η)
    (Φ : ℕ → ℝ → ℝ → ℝ) (M : ℝ)
    (hΦ : ∀ᶠ n in atTop, ∀ m₁ ∈ Icc (γ n * a) (γ n * b), ∀ m₂ ∈ Ioo 0 (γ n), |Φ n m₁ m₂| ≤ M)
    (G : ℝ → ℝ) (hGc : ContinuousOn G (Icc a b)) (hGpos : ∀ p ∈ Icc a b, 0 < G p)
    (hshell : ∀ ε > 0, ∀ C₀ : ℝ, ∀ᶠ n in atTop, ∀ p ∈ Icc a b, ∀ m₂ : ℝ,
      |m₂ - (γ n * p + ℓ n)| ≤ C₀ → |Φ n (γ n * p) m₂ - G p| ≤ ε)
    (T : ℕ → ℝ)
    (hFint : ∀ᶠ n in atTop, IntegrableOn (fun m : ℝ × ℝ => Φ n m.1 m.2 * κ n m)
      (Icc (γ n * a) (γ n * b) ×ˢ Ioo 0 (γ n)))
    (hT : ∀ᶠ n in atTop, T n = ∫ m in Icc (γ n * a) (γ n * b) ×ˢ Ioo 0 (γ n),
      Φ n m.1 m.2 * κ n m) :
    Tendsto T atTop (𝓝 (∫ p in Icc a b, G p)) := by
  classical
  have hIcc : (Icc a b).Nonempty := ⟨a, left_mem_Icc.2 hab⟩
  obtain ⟨gmin, gmax, hgmin, hGlo, hGhi⟩ : ∃ gmin gmax : ℝ, 0 < gmin ∧
      (∀ p ∈ Icc a b, gmin ≤ G p) ∧ (∀ p ∈ Icc a b, G p ≤ gmax) := by
    obtain ⟨p₀, hp₀, hmin⟩ := isCompact_Icc.exists_isMinOn hIcc hGc
    obtain ⟨p₁, hp₁, hmax⟩ := isCompact_Icc.exists_isMaxOn hIcc hGc
    exact ⟨G p₀, G p₁, hGpos p₀ hp₀, fun p hp => isMinOn_iff.mp hmin p hp,
      fun p hp => isMaxOn_iff.mp hmax p hp⟩
  have hgmax : gmin ≤ gmax := (hGlo a (left_mem_Icc.2 hab)).trans (hGhi a (left_mem_Icc.2 hab))
  -- the continuous extension of `G`
  have hclamp : ∀ p : ℝ, max a (min p b) ∈ Icc a b := fun p =>
    ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  obtain ⟨Gt, hGtc, hGt_eq, hGt_lo, hGt_hi⟩ : ∃ Gt : ℝ → ℝ, Continuous Gt ∧
      (∀ p ∈ Icc a b, Gt p = G p) ∧ (∀ p, gmin ≤ Gt p) ∧ (∀ p, Gt p ≤ gmax) := by
    refine ⟨fun p => G (max a (min p b)), hGc.comp_continuous (by fun_prop) hclamp, ?_,
      fun p => hGlo _ (hclamp p), fun p => hGhi _ (hclamp p)⟩
    intro p hp
    simp only [min_eq_left hp.2, max_eq_right hp.1]
  -- geometry constants
  have hg0 : 0 < 1 - τ - b := by linarith
  obtain ⟨δ₀, hδ₀, hδ₀τ, hδ₀g⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < τ ∧ 4 * δ₀ ≤ 1 - τ - b :=
    ⟨min (τ / 2) ((1 - τ - b) / 4), lt_min (by linarith) (by linarith),
      lt_of_le_of_lt (min_le_left _ _) (by linarith),
      by have := min_le_right (τ / 2) ((1 - τ - b) / 4); linarith⟩
  obtain ⟨e₀, he₀, he₀g, he₀a, he₀h⟩ : ∃ e₀ : ℝ, 0 < e₀ ∧ 2 * e₀ ≤ gmin ∧ 2 * e₀ ≤ a ∧
      4 * e₀ ≤ 1 - τ - b :=
    ⟨min (min (gmin / 2) (a / 2)) ((1 - τ - b) / 4),
      lt_min (lt_min (by linarith) (by linarith)) (by linarith),
      by have h2 : min (min (gmin / 2) (a / 2)) ((1 - τ - b) / 4) ≤ gmin / 2 :=
           (min_le_left _ _).trans (min_le_left _ _)
         linarith,
      by have h2 : min (min (gmin / 2) (a / 2)) ((1 - τ - b) / 4) ≤ a / 2 :=
           (min_le_left _ _).trans (min_le_right _ _)
         linarith,
      by have h2 := min_le_right (min (gmin / 2) (a / 2)) ((1 - τ - b) / 4); linarith⟩
  have he₀1 : e₀ ≤ 1 := by linarith
  obtain ⟨ε, hε0, hεe, hεk, hεT⟩ : ∃ ε : ℕ → ℝ, (∀ k, 0 < ε k) ∧ (∀ k, ε k ≤ e₀) ∧
      (∀ k, ε k ≤ 1 / ((k : ℝ) + 1)) ∧ Tendsto ε atTop (𝓝 0) := by
    refine ⟨fun k => min e₀ (1 / ((k : ℝ) + 1)), fun k => lt_min he₀ (by positivity),
      fun k => min_le_left _ _, fun k => min_le_right _ _, ?_⟩
    have := (tendsto_const_nhds (x := e₀)).min tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [min_eq_right he₀.le] using this
  -- the plateau-one window function
  obtain ⟨ζ, hζc, -, hζs, hζ01, -, -, hζ1⟩ := vsh_trap_exists (-δ₀) δ₀ (δ₀ / 2) (by positivity)
  have hζ0 : ζ 0 = 1 := hζ1 0 (by linarith) (by linarith)
  -- the first-variable trapezoids
  choose trH hrHc hrHcs hrHs hrH01 hrHl hrHu hrH1 using
    fun k => vsh_trap_exists (a - ε k) (b + ε k) (ε k) (hε0 k)
  choose trL hrLc hrLcs hrLs hrL01 hrLl hrLu hrL1 using
    fun k => vsh_trap_exists a b (ε k) (hε0 k)
  obtain ⟨Hhi, hHhi⟩ : ∃ Hhi : ℕ → ℝ → ℝ, ∀ k p, Hhi k p = trH k p * (Gt p + ε k) :=
    ⟨fun k p => trH k p * (Gt p + ε k), fun _ _ => rfl⟩
  obtain ⟨Hlo, hHlo⟩ : ∃ Hlo : ℕ → ℝ → ℝ, ∀ k p, Hlo k p = trL k p * (Gt p - ε k) :=
    ⟨fun k p => trL k p * (Gt p - ε k), fun _ _ => rfl⟩
  have hHhic : ∀ k, Continuous (Hhi k) := fun k => by
    have : Hhi k = fun p => trH k p * (Gt p + ε k) := funext (hHhi k)
    rw [this]; exact (hrHc k).mul (hGtc.add continuous_const)
  have hHloc : ∀ k, Continuous (Hlo k) := fun k => by
    have : Hlo k = fun p => trL k p * (Gt p - ε k) := funext (hHlo k)
    rw [this]; exact (hrLc k).mul (hGtc.sub continuous_const)
  have hHhis : ∀ k, tsupport (Hhi k) ⊆ Icc (a - ε k) (b + ε k) := fun k => by
    have : Hhi k = fun p => trH k p * (Gt p + ε k) := funext (hHhi k)
    rw [this]; exact tsupport_mul_subset_left.trans (hrHs k)
  have hHlos : ∀ k, tsupport (Hlo k) ⊆ Icc a b := fun k => by
    have : Hlo k = fun p => trL k p * (Gt p - ε k) := funext (hHlo k)
    rw [this]; exact tsupport_mul_subset_left.trans (hrLs k)
  have hHhi_nn : ∀ k p, 0 ≤ Hhi k p := fun k p => by
    rw [hHhi]
    exact mul_nonneg (hrH01 k p).1 (by linarith [hGt_lo p, hε0 k, hgmin])
  have hGtε : ∀ k p, 0 ≤ Gt p - ε k := fun k p => by linarith [hGt_lo p, hεe k]
  have hHlo_nn : ∀ k p, 0 ≤ Hlo k p := fun k p => by
    rw [hHlo]; exact mul_nonneg (hrL01 k p).1 (hGtε k p)
  have hHlo_le : ∀ k p, Hlo k p ≤ Gt p - ε k := fun k p => by
    rw [hHlo]
    exact (mul_le_mul_of_nonneg_right (hrL01 k p).2 (hGtε k p)).trans (by rw [one_mul])
  -- the test functions
  have hphiHi := fun k => vsh_phi (H := Hhi k) (ζ := ζ) (l := a - ε k) (u := b + ε k)
    (δ := δ₀) (τ := τ) (hHhic k) hζc (hHhis k) hζs (by linarith [hεe k]) hδ₀τ
  have hphiLo := fun k => vsh_phi (H := Hlo k) (ζ := ζ) (l := a) (u := b)
    (δ := δ₀) (τ := τ) (hHloc k) hζc (hHlos k) hζs ha hδ₀τ
  -- limits of the profile integrals (dominated convergence)
  have hbint : Integrable ((Icc (a - 1) (b + 1)).indicator (fun _ : ℝ => 2 * gmax)) := by
    refine (integrable_indicator_iff measurableSet_Icc).2 ?_
    exact integrableOn_const (by simp)
  have hHhi_bd : ∀ k p, ‖Hhi k p‖ ≤ (Icc (a - 1) (b + 1)).indicator (fun _ : ℝ => 2 * gmax) p := by
    intro k p
    by_cases hp : p ∈ Icc (a - 1) (b + 1)
    · rw [indicator_of_mem hp, Real.norm_eq_abs, abs_of_nonneg (hHhi_nn k p), hHhi]
      calc trH k p * (Gt p + ε k) ≤ 1 * (Gt p + ε k) :=
            mul_le_mul_of_nonneg_right (hrH01 k p).2 (by linarith [hGt_lo p, hε0 k, hgmin])
        _ ≤ 2 * gmax := by linarith [hGt_hi p, hεe k, he₀g, hgmax]
    · have h0 : Hhi k p = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro h
        apply hp
        have := hHhis k h
        exact ⟨by linarith [this.1, hεe k, he₀1], by linarith [this.2, hεe k, he₀1]⟩
      rw [indicator_of_notMem hp, h0]; simp
  have hHlo_bd : ∀ k p, ‖Hlo k p‖ ≤ (Icc (a - 1) (b + 1)).indicator (fun _ : ℝ => 2 * gmax) p := by
    intro k p
    by_cases hp : p ∈ Icc (a - 1) (b + 1)
    · rw [indicator_of_mem hp, Real.norm_eq_abs, abs_of_nonneg (hHlo_nn k p)]
      linarith [hHlo_le k p, hGt_hi p, hε0 k, hgmax, hgmin]
    · have h0 : Hlo k p = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro h
        apply hp
        have := hHlos k h
        exact ⟨by linarith [this.1], by linarith [this.2]⟩
      rw [indicator_of_notMem hp, h0]; simp
  have hHhi_lim : ∀ p, Tendsto (fun k => Hhi k p) atTop (𝓝 ((Icc a b).indicator Gt p)) := by
    intro p
    by_cases hp : p ∈ Icc a b
    · rw [indicator_of_mem hp]
      have : ∀ k, Hhi k p = Gt p + ε k := fun k => by
        rw [hHhi, hrH1 k p (by linarith [hp.1]) (by linarith [hp.2]), one_mul]
      simp_rw [this]
      simpa using (tendsto_const_nhds (x := Gt p)).add hεT
    · rw [indicator_of_notMem hp]
      have hev : ∀ᶠ k in atTop, Hhi k p = 0 := by
        rcases not_and_or.1 hp with h | h
        · filter_upwards [hεT.eventually (gt_mem_nhds (show (0:ℝ) < a - p by linarith [not_le.1 h]))]
            with k hk
          apply image_eq_zero_of_notMem_tsupport
          intro h'
          have := (hHhis k h').1
          linarith
        · filter_upwards [hεT.eventually (gt_mem_nhds (show (0:ℝ) < p - b by linarith [not_le.1 h]))]
            with k hk
          apply image_eq_zero_of_notMem_tsupport
          intro h'
          have := (hHhis k h').2
          linarith
      exact tendsto_const_nhds.congr' (hev.mono fun k hk => hk.symm)
  have hHlo_lim : ∀ p, Tendsto (fun k => Hlo k p) atTop (𝓝 ((Ioo a b).indicator Gt p)) := by
    intro p
    by_cases hp : p ∈ Ioo a b
    · rw [indicator_of_mem hp]
      have hev : ∀ᶠ k in atTop, Hlo k p = Gt p - ε k := by
        filter_upwards [hεT.eventually (gt_mem_nhds (show (0:ℝ) < min (p - a) (b - p) from
          lt_min (by linarith [hp.1]) (by linarith [hp.2])))] with k hk
        rw [hHlo, hrL1 k p (by linarith [(lt_min_iff.1 hk).1, min_le_left (p - a) (b - p)])
          (by linarith [min_le_right (p - a) (b - p)]), one_mul]
      have := (tendsto_const_nhds (x := Gt p)).sub hεT
      simp only [sub_zero] at this
      exact this.congr' (hev.mono fun k hk => hk.symm)
    · rw [indicator_of_notMem hp]
      have h0 : ∀ k, Hlo k p = 0 := by
        intro k
        by_cases hpa : p = a
        · rw [hHlo, hpa, hrLl k, zero_mul]
        by_cases hpb : p = b
        · rw [hHlo, hpb, hrLu k, zero_mul]
        apply image_eq_zero_of_notMem_tsupport
        intro h'
        have := hHlos k h'
        exact hp ⟨lt_of_le_of_ne this.1 (Ne.symm hpa), lt_of_le_of_ne this.2 hpb⟩
      simp_rw [h0]
      exact tendsto_const_nhds
  have hL : (∫ p in Icc a b, G p) = ∫ p in Icc a b, Gt p :=
    setIntegral_congr_fun measurableSet_Icc (fun p hp => (hGt_eq p hp).symm)
  have hIhi : Tendsto (fun k => ∫ p, Hhi k p) atTop (𝓝 (∫ p in Icc a b, G p)) := by
    have := tendsto_integral_of_dominated_convergence _ (fun k => (hHhic k).aestronglyMeasurable)
      hbint (fun k => ae_of_all _ (hHhi_bd k)) (ae_of_all _ hHhi_lim)
    rw [integral_indicator measurableSet_Icc] at this
    rwa [hL]
  have hIlo : Tendsto (fun k => ∫ p, Hlo k p) atTop (𝓝 (∫ p in Icc a b, G p)) := by
    have := tendsto_integral_of_dominated_convergence _ (fun k => (hHloc k).aestronglyMeasurable)
      hbint (fun k => ae_of_all _ (hHlo_bd k)) (ae_of_all _ hHlo_lim)
    rw [integral_indicator measurableSet_Ioo, ← integral_Icc_eq_integral_Ioo] at this
    rwa [hL]
  -- named test functions
  obtain ⟨φu, hφu⟩ : ∃ φu : ℕ → ℝ × ℝ → ℝ, ∀ k p, φu k p = Hhi k p.1 * ζ (p.2 - p.1 - τ) :=
    ⟨fun k p => Hhi k p.1 * ζ (p.2 - p.1 - τ), fun _ _ => rfl⟩
  obtain ⟨φl, hφl⟩ : ∃ φl : ℕ → ℝ × ℝ → ℝ, ∀ k p, φl k p = Hlo k p.1 * ζ (p.2 - p.1 - τ) :=
    ⟨fun k p => Hlo k p.1 * ζ (p.2 - p.1 - τ), fun _ _ => rfl⟩
  have hφu' : ∀ k, φu k = fun p => Hhi k p.1 * ζ (p.2 - p.1 - τ) := fun k => funext (hφu k)
  have hφl' : ∀ k, φl k = fun p => Hlo k p.1 * ζ (p.2 - p.1 - τ) := fun k => funext (hφl k)
  have hcu : ∀ k, Continuous (φu k) := fun k => by rw [hφu' k]; exact (hphiHi k).1
  have hcsu : ∀ k, HasCompactSupport (φu k) := fun k => by rw [hφu' k]; exact (hphiHi k).2.1
  have htsu : ∀ k, tsupport (φu k) ⊆ Ioi 0 ×ˢ Ioi 0 := fun k => by
    rw [hφu' k]; exact (hphiHi k).2.2.1
  have hcl : ∀ k, Continuous (φl k) := fun k => by rw [hφl' k]; exact (hphiLo k).1
  have hcsl : ∀ k, HasCompactSupport (φl k) := fun k => by rw [hφl' k]; exact (hphiLo k).2.1
  have htsl : ∀ k, tsupport (φl k) ⊆ Ioi 0 ×ˢ Ioi 0 := fun k => by
    rw [hφl' k]; exact (hphiLo k).2.2.1
  have hsupl : ∀ k (p : ℝ × ℝ), φl k p ≠ 0 → p.1 ∈ Icc a b ∧ p.2 - p.1 - τ ∈ Icc (-δ₀) δ₀ :=
    fun k p hp => (hphiLo k).2.2.2.1 p (by rwa [hφl] at hp)
  have hvalu : ∀ k, (∫ r : ℝ, φu k (r, r + τ)) = ∫ r, Hhi k r := fun k => by
    have := (hphiHi k).2.2.2.2
    rw [hζ0, one_mul] at this
    simp_rw [hφu]
    exact this
  have hvall : ∀ k, (∫ r : ℝ, φl k (r, r + τ)) = ∫ r, Hlo k r := fun k => by
    have := (hphiLo k).2.2.2.2
    rw [hζ0, one_mul] at this
    simp_rw [hφl]
    exact this
  have hφu_nn : ∀ k p, 0 ≤ φu k p := fun k p => by
    rw [hφu]; exact mul_nonneg (hHhi_nn k _) (hζ01 _).1
  have hφl_nn : ∀ k p, 0 ≤ φl k p := fun k p => by
    rw [hφl]; exact mul_nonneg (hHlo_nn k _) (hζ01 _).1
  -- pointwise nonnegativity of the weighted test functions
  have hψu_nn : ∀ k n (m : ℝ × ℝ), 0 ≤ φu k (m.1 / γ n, m.2 / γ n) * κ n m := by
    intro k n m
    by_cases h0 : φu k (m.1 / γ n, m.2 / γ n) = 0
    · simp [h0]
    · have := htsu k (subset_tsupport _ (Function.mem_support.2 h0))
      have h1 : 0 < m.1 := by
        have := this.1; simp only [mem_Ioi] at this
        exact (div_pos_iff_of_pos_right (hγ0 n)).1 this
      have h2 : 0 < m.2 := by
        have := this.2; simp only [mem_Ioi] at this
        exact (div_pos_iff_of_pos_right (hγ0 n)).1 this
      exact mul_nonneg (hφu_nn k _) (hκ0 n m h1 h2)
  -- parameters of the errors
  set cst : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hcst
  have hMg : 0 < max M 0 + gmax + 1 := by have := le_max_right M 0; linarith
  have hη : ∀ k : ℕ, 0 < cst k / (max M 0 + gmax + 1) := fun k =>
    div_pos (by simp only [hcst]; positivity) hMg
  choose C0 hC0 hoffk using fun k : ℕ => hκoff _ (hη k)
  have hHM : ∀ k : ℕ, (gmax + max M 0) * (cst k / (max M 0 + gmax + 1)) ≤ cst k := by
    intro k
    rw [← mul_div_assoc, div_le_iff₀ hMg]
    have : 0 ≤ cst k := by simp only [hcst]; positivity
    nlinarith
  have hwin : ∀ k : ℕ, ∀ᶠ n in atTop, C0 k / γ n ≤ δ₀ / 4 ∧ |(ℓ n : ℝ) / γ n - τ| ≤ δ₀ / 4 := by
    intro k
    have h1 : Tendsto (fun n => C0 k / γ n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hγT
    have h2 := Metric.tendsto_nhds.1 hℓ (δ₀ / 4) (by positivity)
    filter_upwards [h1.eventually (ge_mem_nhds (show (0 : ℝ) < δ₀ / 4 by positivity)), h2]
      with n hn1 hn2
    exact ⟨hn1, by rw [Real.dist_eq] at hn2; exact hn2.le⟩
  -- the two-sided bound for each `k`
  have hord : ∀ k : ℕ, ∀ᶠ n in atTop,
      (∫ m : ℝ × ℝ, φl k (m.1 / γ n, m.2 / γ n) * κ n m) - cst k ≤ T n ∧
      T n ≤ (∫ m : ℝ × ℝ, φu k (m.1 / γ n, m.2 / γ n) * κ n m) + cst k := by
    intro k
    filter_upwards [hT, hFint, hκint, hΦ, hoffk k, hshell (ε k) (hε0 k) (C0 k), hwin k]
      with n hTn hFn hκn hΦn hoffn hshn hwinn
    have hγn := hγ0 n
    have hDm : MeasurableSet (Icc (γ n * a) (γ n * b) ×ˢ Ioo 0 (γ n)) :=
      measurableSet_Icc.prod measurableSet_Ioo
    have hS0 : MeasurableSet {m : ℝ × ℝ | |m.1 - m.2 + ℓ n| ≤ C0 k} :=
      measurableSet_le (by fun_prop) measurable_const
    have hκD : ∀ m ∈ Icc (γ n * a) (γ n * b) ×ˢ Ioo 0 (γ n), 0 ≤ κ n m := fun m hm =>
      hκ0 n m (lt_of_lt_of_le (mul_pos hγn ha) hm.1.1) hm.2.1
    have hp1 : ∀ m ∈ Icc (γ n * a) (γ n * b) ×ˢ Ioo 0 (γ n), m.1 / γ n ∈ Icc a b :=
      fun m hm => ⟨by rw [le_div_iff₀ hγn, mul_comm]; exact hm.1.1,
        by rw [div_le_iff₀ hγn, mul_comm]; exact hm.1.2⟩
    have hFb : ∀ m ∈ Icc (γ n * a) (γ n * b) ×ˢ Ioo 0 (γ n),
        |Φ n m.1 m.2 * κ n m| ≤ max M 0 * κ n m := fun m hm => by
      rw [abs_mul, abs_of_nonneg (hκD m hm)]
      exact mul_le_mul_of_nonneg_right ((hΦn m.1 hm.1 m.2 hm.2).trans (le_max_left _ _))
        (hκD m hm)
    have hwind : ∀ m ∈ {m : ℝ × ℝ | |m.1 - m.2 + ℓ n| ≤ C0 k},
        |m.2 / γ n - m.1 / γ n - τ| ≤ δ₀ / 2 := by
      intro m hm
      have e : m.2 / γ n - m.1 / γ n - τ =
          (m.2 - m.1 - ℓ n) / γ n + ((ℓ n : ℝ) / γ n - τ) := by
        field_simp; ring
      rw [e]
      calc |(m.2 - m.1 - ℓ n) / γ n + ((ℓ n : ℝ) / γ n - τ)|
          ≤ |(m.2 - m.1 - ℓ n) / γ n| + |(ℓ n : ℝ) / γ n - τ| := abs_add_le _ _
        _ ≤ C0 k / γ n + δ₀ / 4 := by
          refine add_le_add ?_ hwinn.2
          rw [abs_div, abs_of_pos hγn]
          apply div_le_div_of_nonneg_right _ hγn.le
          have : |m.2 - m.1 - ℓ n| = |m.1 - m.2 + ℓ n| := by
            rw [← abs_neg]; ring_nf
          rw [this]; exact hm
        _ ≤ δ₀ / 2 := by linarith [hwinn.1]
    -- shell comparison at a point of the shell
    have hshm : ∀ m ∈ Icc (γ n * a) (γ n * b) ×ˢ Ioo 0 (γ n) ∩ {m : ℝ × ℝ | |m.1 - m.2 + ℓ n| ≤ C0 k},
        |Φ n m.1 m.2 - Gt (m.1 / γ n)| ≤ ε k := by
      intro m ⟨hmD, hmS⟩
      have hp := hp1 m hmD
      have hm1 : γ n * (m.1 / γ n) = m.1 := mul_div_cancel₀ _ hγn.ne'
      have := hshn (m.1 / γ n) hp m.2 (by
        rw [hm1]
        have : |m.2 - (m.1 + ℓ n)| = |m.1 - m.2 + ℓ n| := by rw [← abs_neg]; ring_nf
        rw [this]; exact hmS)
      rw [hm1, ← hGt_eq _ hp] at this
      exact this
    have hφu1 : ∀ m ∈ Icc (γ n * a) (γ n * b) ×ˢ Ioo 0 (γ n) ∩
        {m : ℝ × ℝ | |m.1 - m.2 + ℓ n| ≤ C0 k},
        φu k (m.1 / γ n, m.2 / γ n) = Gt (m.1 / γ n) + ε k := by
      intro m ⟨hmD, hmS⟩
      have hp := hp1 m hmD
      have hw := abs_le.1 (hwind m hmS)
      rw [hφu]
      dsimp only
      rw [hHhi, hrH1 k _ (by linarith [hp.1]) (by linarith [hp.2]),
        hζ1 _ (by linarith [hw.1]) (by linarith [hw.2])]
      ring
    have hFintD : IntegrableOn (fun m : ℝ × ℝ => Φ n m.1 m.2 * κ n m)
        (Icc (γ n * a) (γ n * b) ×ˢ Ioo 0 (γ n)) := hFn
    constructor
    · -- lower bound
      have hlow := vsh_ineq_lower (D := Icc (γ n * a) (γ n * b) ×ˢ Ioo 0 (γ n))
        (S0 := {m : ℝ × ℝ | |m.1 - m.2 + ℓ n| ≤ C0 k}) hS0
        (F := fun m => Φ n m.1 m.2 * κ n m) (κ := κ n)
        (ψ := fun m => φl k (m.1 / γ n, m.2 / γ n) * κ n m) (M := max M 0) (H := gmax)
        (η := cst k / (max M 0 + gmax + 1)) hFintD hκn
        ((hκtest (φl k) (hcl k) (hcsl k) (htsl k)).1 n) hκD hFb ?_ ?_ ?_ hoffn
        (le_max_right _ _) (by linarith) hDm
      · have h0 := hHM k
        rw [hTn]
        linarith
      · -- support in D
        intro m hm
        by_contra hne
        have hφ : φl k (m.1 / γ n, m.2 / γ n) ≠ 0 := fun h => hne (by rw [h, zero_mul])
        obtain ⟨h1, h2⟩ := hsupl k _ hφ
        apply hm
        simp only at h1 h2
        have hm1 : m.1 = γ n * (m.1 / γ n) := (mul_div_cancel₀ _ hγn.ne').symm
        have hm2 : m.2 = γ n * (m.2 / γ n) := (mul_div_cancel₀ _ hγn.ne').symm
        have h2' := abs_le.1 (abs_le.2 h2)
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
        · rw [hm1]; exact mul_le_mul_of_nonneg_left h1.1 hγn.le
        · rw [hm1]; exact mul_le_mul_of_nonneg_left h1.2 hγn.le
        · rw [hm2]; exact mul_pos hγn (by linarith [h2.1, h1.1])
        · rw [hm2]
          exact mul_lt_of_lt_one_right hγn (by linarith [h2.2, h1.2])
      · -- shell
        intro m hm
        have hp := hp1 m hm.1
        have hw := abs_le.1 (hwind m hm.2)
        have hsh' := abs_le.1 (hshm m hm)
        have hφle : φl k (m.1 / γ n, m.2 / γ n) ≤ Gt (m.1 / γ n) - ε k := by
          rw [hφl]
          dsimp only
          exact (mul_le_of_le_one_right (hHlo_nn k _) (hζ01 _).2).trans (hHlo_le k _)
        have : Gt (m.1 / γ n) - ε k ≤ Φ n m.1 m.2 := by linarith [hsh'.1, hsh'.2]
        exact mul_le_mul_of_nonneg_right (hφle.trans this) (hκD m hm.1)
      · -- off shell
        intro m hm
        have hφle : φl k (m.1 / γ n, m.2 / γ n) ≤ gmax := by
          rw [hφl]
          dsimp only
          exact ((mul_le_of_le_one_right (hHlo_nn k _) (hζ01 _).2).trans (hHlo_le k _)).trans
            (by linarith [hGt_hi (m.1 / γ n), hε0 k])
        exact mul_le_mul_of_nonneg_right hφle (hκD m hm.1)
    · -- upper bound
      have hup := vsh_ineq_upper (D := Icc (γ n * a) (γ n * b) ×ˢ Ioo 0 (γ n))
        (S0 := {m : ℝ × ℝ | |m.1 - m.2 + ℓ n| ≤ C0 k}) hS0
        (F := fun m => Φ n m.1 m.2 * κ n m) (κ := κ n)
        (ψ := fun m => φu k (m.1 / γ n, m.2 / γ n) * κ n m) (M := max M 0)
        (η := cst k / (max M 0 + gmax + 1)) hFintD hκn
        ((hκtest (φu k) (hcu k) (hcsu k) (htsu k)).1 n) (hψu_nn k n) hκD hFb ?_ hoffn
        (le_max_right _ _) hDm
      · have h0 := hHM k
        have h1 : max M 0 * (cst k / (max M 0 + gmax + 1)) ≤ cst k := by
          have : 0 ≤ cst k / (max M 0 + gmax + 1) := (hη k).le
          nlinarith [hgmin]
        rw [hTn]
        linarith
      · intro m hm
        have hΦle : Φ n m.1 m.2 ≤ Gt (m.1 / γ n) + ε k := by
          linarith [(abs_le.1 (hshm m hm)).2]
        show Φ n m.1 m.2 * κ n m ≤ φu k (m.1 / γ n, m.2 / γ n) * κ n m
        rw [hφu1 m hm]
        exact mul_le_mul_of_nonneg_right hΦle (hκD m hm.1)
  -- conclude by the two-parameter squeeze
  refine vsh_tendsto_of_sandwich T
    (fun k n => (∫ m : ℝ × ℝ, φl k (m.1 / γ n, m.2 / γ n) * κ n m) - cst k)
    (fun k n => (∫ m : ℝ × ℝ, φu k (m.1 / γ n, m.2 / γ n) * κ n m) + cst k)
    (fun k => (∫ r, Hlo k r) - cst k) (fun k => (∫ r, Hhi k r) + cst k)
    (∫ p in Icc a b, G p) ?_ ?_ ?_ ?_ hord
  · intro k
    have := (hκtest (φl k) (hcl k) (hcsl k) (htsl k)).2.sub_const (cst k)
    rwa [hvall k] at this
  · intro k
    have := (hκtest (φu k) (hcu k) (hcsu k) (htsu k)).2.add_const (cst k)
    rwa [hvalu k] at this
  · have hc0 : Tendsto cst atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using hIlo.sub hc0
  · have hc0 : Tendsto cst atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using hIhi.add hc0


/-- Private: `exp(-μ|v|)` is integrable on the line. -/
private lemma vsh_exp_abs_integrable {μ : ℝ} (hμ : 0 < μ) :
    Integrable (fun v : ℝ => Real.exp (-μ * |v|)) := by
  have h1 : IntegrableOn (fun v : ℝ => Real.exp (-μ * |v|)) (Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi 0 hμ).congr_fun (fun v hv => ?_) measurableSet_Ioi
    simp only
    rw [abs_of_pos hv]
  have h2 : Integrable ((Ioi (0 : ℝ)).indicator (fun v : ℝ => Real.exp (-μ * |v|))) :=
    (integrable_indicator_iff measurableSet_Ioi).2 h1
  have h3 := h2.add h2.comp_neg
  have hne : ∀ᵐ v : ℝ, v ≠ 0 := by
    simpa [ae_iff] using measure_singleton (0 : ℝ)
  refine h3.congr ?_
  filter_upwards [hne] with v hv
  simp only [Pi.add_apply]
  rcases lt_or_gt_of_ne hv with h | h
  · rw [indicator_of_notMem (by simpa using h.le), indicator_of_mem (by simpa using h)]
    simp [abs_neg]
  · rw [indicator_of_mem (by simpa using h), indicator_of_notMem (by simpa using h.le)]
    simp

/-- Private: the two-sided exponential tail function. -/
private lemma vsh_tail {μ : ℝ} (hμ : 0 < μ) {C₀ : ℝ} (hC : 0 ≤ C₀) :
    Integrable ((Ioi C₀).indicator (fun v : ℝ => Real.exp (-μ * |v|)) +
      (Iio (-C₀)).indicator (fun v : ℝ => Real.exp (-μ * |v|))) ∧
    ∫ v, ((Ioi C₀).indicator (fun v : ℝ => Real.exp (-μ * |v|)) v +
      (Iio (-C₀)).indicator (fun v : ℝ => Real.exp (-μ * |v|)) v) = 2 / μ * Real.exp (-μ * C₀) := by
  have hint1 : IntegrableOn (fun v : ℝ => Real.exp (-μ * |v|)) (Ioi C₀) := by
    refine (exp_neg_integrableOn_Ioi C₀ hμ).congr_fun (fun v hv => ?_) measurableSet_Ioi
    simp only
    rw [abs_of_pos (lt_of_le_of_lt hC hv)]
  have hI1 : Integrable ((Ioi C₀).indicator (fun v : ℝ => Real.exp (-μ * |v|))) :=
    (integrable_indicator_iff measurableSet_Ioi).2 hint1
  have hI2 : Integrable ((Iio (-C₀)).indicator (fun v : ℝ => Real.exp (-μ * |v|))) := by
    have := hI1.comp_neg
    refine this.congr (ae_of_all _ fun v => ?_)
    simp only [indicator]
    by_cases h : v < -C₀
    · have h' : C₀ < -v := by linarith
      simp [h, h', abs_neg]
    · have h' : ¬ C₀ < -v := by intro h''; apply h; linarith
      simp [h, h']
  refine ⟨hI1.add hI2, ?_⟩
  rw [integral_add hI1 hI2]
  have hv1 : ∫ v, (Ioi C₀).indicator (fun v : ℝ => Real.exp (-μ * |v|)) v =
      Real.exp (-μ * C₀) / μ := by
    rw [integral_indicator measurableSet_Ioi]
    have : ∫ v in Ioi C₀, Real.exp (-μ * |v|) = ∫ v in Ioi C₀, Real.exp (-μ * v) :=
      setIntegral_congr_fun measurableSet_Ioi (fun v hv => by
        rw [abs_of_pos (lt_of_le_of_lt hC hv)])
    rw [this, integral_exp_mul_Ioi (by linarith) C₀]
    field_simp
  have hv2 : ∫ v, (Iio (-C₀)).indicator (fun v : ℝ => Real.exp (-μ * |v|)) v =
      Real.exp (-μ * C₀) / μ := by
    rw [← hv1, ← integral_neg_eq_self]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only [indicator]
    by_cases h : v < -C₀
    · have h' : C₀ < -v := by linarith
      simp [h, h', abs_neg]
    · have h' : ¬ C₀ < -v := by intro h''; apply h; linarith
      simp [h, h']
  rw [hv1, hv2]; ring

/-- Private: integral of a function of `m₁ - m₂ + c` over a strip `I × ℝ`. -/
private lemma vsh_strip {h : ℝ → ℝ} (hh : Integrable h) (hm : Measurable h) (c : ℝ)
    {I : Set ℝ} (hI : MeasurableSet I) (hIf : volume I ≠ ⊤) :
    IntegrableOn (fun m : ℝ × ℝ => h (m.1 - m.2 + c)) (I ×ˢ univ) ∧
    ∫ m in I ×ˢ univ, h (m.1 - m.2 + c) = (volume I).toReal * ∫ v, h v := by
  haveI : IsFiniteMeasure (volume.restrict I) := ⟨by simpa [lt_top_iff_ne_top] using hIf⟩
  have hfm : Measurable (fun m : ℝ × ℝ => h (m.1 - m.2 + c)) := hm.comp (by fun_prop)
  have hprod : (volume.restrict I).prod (volume.restrict (univ : Set ℝ)) =
      (volume : Measure (ℝ × ℝ)).restrict (I ×ˢ univ) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hint : Integrable (fun m : ℝ × ℝ => h (m.1 - m.2 + c))
      ((volume.restrict I).prod (volume.restrict (univ : Set ℝ))) := by
    rw [Measure.restrict_univ]
    rw [integrable_prod_iff hfm.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun x => ?_, ?_⟩
    · have := hh.comp_sub_left (x + c)
      simpa [show ∀ y : ℝ, x - y + c = x + c - y from fun y => by ring] using this
    · have : (fun x : ℝ => ∫ y, ‖h (x - y + c)‖) = fun _ => ∫ v, ‖h v‖ := by
        funext x
        have := integral_sub_left_eq_self (fun v => ‖h v‖) (volume : Measure ℝ) (x + c)
        simpa [show ∀ y : ℝ, x - y + c = x + c - y from fun y => by ring] using this
      rw [this]
      exact integrable_const _
  rw [hprod] at hint
  refine ⟨hint, ?_⟩
  have h1 := setIntegral_prod (μ := volume) (ν := volume) (fun m : ℝ × ℝ => h (m.1 - m.2 + c))
    (s := I) (t := univ) (by rwa [Measure.volume_eq_prod] at hint)
  rw [Measure.volume_eq_prod, h1]
  have : ∀ x : ℝ, ∫ y in (univ : Set ℝ), h (x - y + c) = ∫ v, h v := by
    intro x
    rw [Measure.restrict_univ]
    have := integral_sub_left_eq_self h (volume : Measure ℝ) (x + c)
    simpa [show ∀ y : ℝ, x - y + c = x + c - y from fun y => by ring] using this
  simp_rw [this]
  rw [setIntegral_const, smul_eq_mul]
  rfl

/-- Private: pointwise bound of the lag kernel `κ` away from `m₁ < 1`. -/
private lemma vsh_kernel_pw {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ K μ : ℝ, 0 < μ ∧ ∀ (s : ℝ) (ℓ : ℤ), 0 < s → 0 ≤ ℓ → ∀ m₁ m₂ : ℝ, 1 ≤ m₁ → 0 < m₂ →
      0 ≤ DLag β (Qm β m₁) (Qm β m₂) ℓ / (Real.pi ^ 2 * s * Efun β m₁ * Efun β m₂) ∧
      DLag β (Qm β m₁) (Qm β m₂) ℓ / (Real.pi ^ 2 * s * Efun β m₁ * Efun β m₂) ≤
        K / s * Real.exp (-μ * |m₁ - m₂ + ℓ|) *
          (1 + (Ioo (0 : ℝ) 1).indicator (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) m₂) := by
  obtain ⟨-, -, C, hC⟩ := lem_app_pl_localization_i hβ0 hβ1
  obtain ⟨cE, CE, hcE, hcCE, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  have hlam : 0 < |Real.log β| := abs_pos.2 (Real.log_neg hβ0 hβ1).ne
  set lam := |Real.log β| with hlamdef
  refine ⟨|C| * (1 + 2 / lam) / (Real.pi ^ 2 * cE ^ 2), lam / 2, by positivity, ?_⟩
  intro s ℓ hs hℓ m₁ m₂ hm₁ hm₂
  have hm₁0 : 0 < m₁ := by linarith
  have hw : 0 < min m₂ 1 := lt_min hm₂ one_pos
  have hE1 : cE ≤ Efun β m₁ := by
    have := (hE m₁ hm₁0).1
    rwa [min_eq_right hm₁, mul_one] at this
  have hE2 : cE * min m₂ 1 ≤ Efun β m₂ := (hE m₂ hm₂).1
  have hE1p : 0 < Efun β m₁ := lt_of_lt_of_le hcE hE1
  have hE2p : 0 < Efun β m₂ := lt_of_lt_of_le (mul_pos hcE hw) hE2
  have hD0 : 0 ≤ DLag β (Qm β m₁) (Qm β m₂) ℓ :=
    vsh_DLag_nonneg hβ0 (vsh_Qm hβ0 hβ1 hm₁0).1.le (vsh_Qm hβ0 hβ1 hm₂).1.le ℓ
  have hden : 0 < Real.pi ^ 2 * s * Efun β m₁ * Efun β m₂ := by positivity
  refine ⟨div_nonneg hD0 hden.le, ?_⟩
  -- the bound on `D`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = ℓ := ⟨ℓ.toNat, Int.toNat_of_nonneg hℓ⟩
  have hDn : DLag β (Qm β m₁) (Qm β m₂) ℓ = DLagNat β (Qm β m₁) (Qm β m₂) n := by
    subst hn; simp [DLag]
  have hncast : ((n : ℤ) : ℝ) = (n : ℝ) := by simp
  have hu : |m₁ - m₂ + ℓ| = |m₁ - m₂ + n| := by rw [← hn]; simp
  have hDb := hC n m₁ m₂ hm₁0 hm₂
  have hexp : (1 + |m₁ - m₂ + n|) * Real.exp (-lam * |m₁ - m₂ + n|) ≤
      (1 + 2 / lam) * Real.exp (-(lam / 2) * |m₁ - m₂ + n|) := by
    set x := |m₁ - m₂ + n| with hx
    have hx0 : 0 ≤ x := abs_nonneg _
    have h1 : 1 + x ≤ (1 + 2 / lam) * Real.exp (lam / 2 * x) := by
      have h2 : 1 + lam / 2 * x ≤ Real.exp (lam / 2 * x) := by linarith [Real.add_one_le_exp (lam / 2 * x)]
      have h3 : 1 + x ≤ (1 + 2 / lam) * (1 + lam / 2 * x) := by
        have : (1 + 2 / lam) * (1 + lam / 2 * x) = 1 + lam / 2 * x + 2 / lam + x := by
          field_simp
          ring
        rw [this]
        have : 0 ≤ lam / 2 * x := by positivity
        have : 0 ≤ 2 / lam := by positivity
        linarith
      exact h3.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    calc (1 + x) * Real.exp (-lam * x) ≤ ((1 + 2 / lam) * Real.exp (lam / 2 * x)) * Real.exp (-lam * x) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = (1 + 2 / lam) * Real.exp (-(lam / 2) * x) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hsq : Real.sqrt (min (min m₁ m₂) 1) ≤ Real.sqrt (min m₂ 1) :=
    Real.sqrt_le_sqrt (min_le_min_right _ (min_le_right _ _))
  have hDle : DLag β (Qm β m₁) (Qm β m₂) ℓ ≤
      |C| * (1 + 2 / lam) * Real.sqrt (min m₂ 1) * Real.exp (-(lam / 2) * |m₁ - m₂ + ℓ|) := by
    rw [hDn, hu]
    refine hDb.trans ?_
    have hs0 : 0 ≤ Real.sqrt (min m₂ 1) := Real.sqrt_nonneg _
    calc C * Real.sqrt (min (min m₁ m₂) 1) * (1 + |m₁ - m₂ + n|) * Real.exp (-lam * |m₁ - m₂ + n|)
        ≤ |C| * Real.sqrt (min m₂ 1) * ((1 + |m₁ - m₂ + n|) * Real.exp (-lam * |m₁ - m₂ + n|)) := by
          have h0 : 0 ≤ (1 + |m₁ - m₂ + n|) * Real.exp (-lam * |m₁ - m₂ + n|) := by positivity
          have : C * Real.sqrt (min (min m₁ m₂) 1) ≤ |C| * Real.sqrt (min m₂ 1) :=
            mul_le_mul (le_abs_self C) hsq (Real.sqrt_nonneg _) (abs_nonneg _)
          calc C * Real.sqrt (min (min m₁ m₂) 1) * (1 + |m₁ - m₂ + n|) * Real.exp (-lam * |m₁ - m₂ + n|)
              = (C * Real.sqrt (min (min m₁ m₂) 1)) *
                ((1 + |m₁ - m₂ + n|) * Real.exp (-lam * |m₁ - m₂ + n|)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right this h0
      _ ≤ |C| * Real.sqrt (min m₂ 1) * ((1 + 2 / lam) * Real.exp (-(lam / 2) * |m₁ - m₂ + n|)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring
  -- combine
  have hmain : DLag β (Qm β m₁) (Qm β m₂) ℓ / (Real.pi ^ 2 * s * Efun β m₁ * Efun β m₂) ≤
      (|C| * (1 + 2 / lam) * Real.sqrt (min m₂ 1) * Real.exp (-(lam / 2) * |m₁ - m₂ + ℓ|)) /
        (Real.pi ^ 2 * s * cE * (cE * min m₂ 1)) := by
    apply div_le_div₀ (by positivity) hDle (by positivity)
    have := mul_le_mul hE1 hE2 (mul_pos hcE hw).le hE1p.le
    calc Real.pi ^ 2 * s * cE * (cE * min m₂ 1) = Real.pi ^ 2 * s * (cE * (cE * min m₂ 1)) := by ring
      _ ≤ Real.pi ^ 2 * s * (Efun β m₁ * Efun β m₂) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  refine hmain.trans ?_
  have hsw : Real.sqrt (min m₂ 1) / min m₂ 1 ≤
      1 + (Ioo (0 : ℝ) 1).indicator (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) m₂ := by
    by_cases h1 : 1 ≤ m₂
    · rw [min_eq_right h1, Real.sqrt_one, indicator_of_notMem (by simp [h1])]
      simp
    · push_neg at h1
      rw [min_eq_left h1.le, indicator_of_mem (show m₂ ∈ Ioo (0 : ℝ) 1 from ⟨hm₂, h1⟩)]
      have : Real.sqrt m₂ / m₂ = m₂ ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_neg hm₂.le, div_eq_mul_inv, ← Real.rpow_neg_one,
          ← Real.rpow_add hm₂]
        rw [← Real.rpow_neg hm₂.le]; congr 1; norm_num
      rw [this]
      linarith
  have e : (|C| * (1 + 2 / lam) * Real.sqrt (min m₂ 1) * Real.exp (-(lam / 2) * |m₁ - m₂ + ℓ|)) /
        (Real.pi ^ 2 * s * cE * (cE * min m₂ 1)) =
      |C| * (1 + 2 / lam) / (Real.pi ^ 2 * cE ^ 2) / s * Real.exp (-(lam / 2) * |m₁ - m₂ + ℓ|) *
        (Real.sqrt (min m₂ 1) / min m₂ 1) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left hsw (by positivity)

/-- Private: `x^(-1/2)` on `(0,1)`. -/
private lemma vsh_rpow_half :
    IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (Ioo 0 1) ∧
    ∫ x in Ioo (0 : ℝ) 1, x ^ (-(1 / 2 : ℝ)) = 2 := by
  have hii : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hio : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hii
  refine ⟨hio.mono_set Ioo_subset_Ioc_self, ?_⟩
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl (by norm_num))]
  norm_num

/-- Private: deterministic integrability and off-shell mass bound for the lag kernel. -/
private lemma vsh_off_det {κ : ℝ × ℝ → ℝ} {s a b K0 μ ℓ : ℝ} (hs : 0 < s) (hab : a ≤ b)
    (hK0 : 0 ≤ K0) (hμ : 0 < μ) (hℓ : 0 ≤ ℓ) (hsa : 1 ≤ s * a)
    (hmeas : AEStronglyMeasurable κ (volume.restrict (Icc (s * a) (s * b) ×ˢ Ioo 0 s)))
    (hκ0 : ∀ m ∈ Icc (s * a) (s * b) ×ˢ Ioo 0 s, 0 ≤ κ m)
    (hκb : ∀ m ∈ Icc (s * a) (s * b) ×ˢ Ioo 0 s, κ m ≤ K0 / s * Real.exp (-μ * |m.1 - m.2 + ℓ|) *
      (1 + (Ioo (0 : ℝ) 1).indicator (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) m.2)) :
    IntegrableOn κ (Icc (s * a) (s * b) ×ˢ Ioo 0 s) ∧
    ∀ C₀ : ℝ, 0 ≤ C₀ →
      ∫ m in Icc (s * a) (s * b) ×ˢ Ioo 0 s \ {m : ℝ × ℝ | |m.1 - m.2 + ℓ| ≤ C₀}, κ m ≤
        (b - a) * K0 * (2 / μ * Real.exp (-μ * C₀) + 2 * Real.exp (-μ * (s * a - 1))) := by
  have hI₁fin : volume (Icc (s * a) (s * b)) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hI₁r : (volume (Icc (s * a) (s * b))).toReal = s * (b - a) := by
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by nlinarith)]; ring
  haveI : IsFiniteMeasure (volume.restrict (Icc (s * a) (s * b))) :=
    ⟨by simpa [lt_top_iff_ne_top] using hI₁fin⟩
  set D : Set (ℝ × ℝ) := Icc (s * a) (s * b) ×ˢ Ioo 0 s with hD
  have hDm : MeasurableSet D := measurableSet_Icc.prod measurableSet_Ioo
  -- the bounding functions
  have hgi := vsh_exp_abs_integrable hμ
  set cB : ℝ := K0 / s * Real.exp (-μ * (s * a - 1)) with hcB
  have hcB0 : 0 ≤ cB := by positivity
  set ind : ℝ → ℝ := (Ioo (0 : ℝ) 1).indicator (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) with hind
  have hind0 : ∀ x, 0 ≤ ind x := fun x => by
    simp only [hind, indicator]
    split_ifs with h
    · exact Real.rpow_nonneg h.1.le _
    · exact le_rfl
  have hindi : Integrable ind := (integrable_indicator_iff measurableSet_Ioo).2 vsh_rpow_half.1
  have hindint : ∫ x, ind x = 2 := by
    rw [hind, integral_indicator measurableSet_Ioo]; exact vsh_rpow_half.2
  have hB1i : Integrable (fun v : ℝ => K0 / s * Real.exp (-μ * |v|)) := hgi.const_mul _
  have hB1m : Measurable (fun v : ℝ => K0 / s * Real.exp (-μ * |v|)) := by fun_prop
  obtain ⟨hs1, -⟩ := vsh_strip hB1i hB1m ℓ measurableSet_Icc hI₁fin
  have hB1D : IntegrableOn (fun m : ℝ × ℝ => K0 / s * Real.exp (-μ * |m.1 - m.2 + ℓ|)) D :=
    hs1.mono_set (prod_mono subset_rfl (subset_univ _))
  -- the second bounding function
  have hB2i : IntegrableOn (fun m : ℝ × ℝ => cB * ind m.2) D := by
    have h1 : Integrable (fun _ : ℝ => cB) (volume.restrict (Icc (s * a) (s * b))) :=
      integrable_const _
    have h2 : Integrable ind (volume.restrict (Ioo 0 s)) := hindi.integrableOn
    have := h1.mul_prod h2
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at this
    exact this
  have hB2int : ∫ m in D, cB * ind m.2 ≤ s * (b - a) * cB * 2 := by
    have := setIntegral_prod_mul (μ := volume) (ν := volume) (fun _ : ℝ => cB) ind
      (Icc (s * a) (s * b)) (Ioo 0 s)
    rw [← Measure.volume_eq_prod] at this
    rw [this, setIntegral_const, smul_eq_mul]
    have h3 : ∫ x in Ioo 0 s, ind x ≤ 2 := by
      rw [← hindint]
      exact setIntegral_le_integral hindi (ae_of_all _ hind0)
    have h4 : (volume.real (Icc (s * a) (s * b))) = s * (b - a) := hI₁r
    rw [h4]
    have h5 : 0 ≤ s * (b - a) * cB := by
      have : 0 ≤ b - a := by linarith
      positivity
    calc s * (b - a) * cB * ∫ x in Ioo 0 s, ind x ≤ s * (b - a) * cB * 2 :=
          mul_le_mul_of_nonneg_left h3 h5
      _ = _ := by ring
  -- pointwise comparison on `D`
  have hpw : ∀ m ∈ D, κ m ≤ K0 / s * Real.exp (-μ * |m.1 - m.2 + ℓ|) + cB * ind m.2 := by
    intro m hm
    refine (hκb m hm).trans ?_
    have key : K0 / s * Real.exp (-μ * |m.1 - m.2 + ℓ|) * ind m.2 ≤ cB * ind m.2 := by
      by_cases h : ind m.2 = 0
      · rw [h]; simp
      · have hm2 : m.2 ∈ Ioo (0 : ℝ) 1 := by
          by_contra hn
          exact h (by simp [hind, indicator_of_notMem hn])
        have hu : s * a - 1 ≤ |m.1 - m.2 + ℓ| := by
          have h1 : s * a ≤ m.1 := hm.1.1
          have : s * a - 1 ≤ m.1 - m.2 + ℓ := by linarith [hm2.2]
          exact this.trans (le_abs_self _)
        have : Real.exp (-μ * |m.1 - m.2 + ℓ|) ≤ Real.exp (-μ * (s * a - 1)) :=
          Real.exp_le_exp.2 (by nlinarith)
        calc K0 / s * Real.exp (-μ * |m.1 - m.2 + ℓ|) * ind m.2
            ≤ K0 / s * Real.exp (-μ * (s * a - 1)) * ind m.2 :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by positivity)) (hind0 _)
          _ = cB * ind m.2 := rfl
    rw [mul_add, mul_one]
    linarith
  have hbd_int : IntegrableOn (fun m : ℝ × ℝ => K0 / s * Real.exp (-μ * |m.1 - m.2 + ℓ|) +
      cB * ind m.2) D := hB1D.add hB2i
  have hκD : IntegrableOn κ D := by
    refine Integrable.mono' hbd_int hmeas ((ae_restrict_iff' hDm).2 (ae_of_all _ fun m hm => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hκ0 m hm)]; exact hpw m hm
  refine ⟨hκD, fun C₀ hC₀ => ?_⟩
  -- tail estimate
  obtain ⟨htail1, htail2⟩ := vsh_tail hμ hC₀
  set hC : ℝ → ℝ := fun v => K0 / s * ((Ioi C₀).indicator (fun v : ℝ => Real.exp (-μ * |v|)) v +
      (Iio (-C₀)).indicator (fun v : ℝ => Real.exp (-μ * |v|)) v) with hhC
  have hhCi : Integrable hC := by
    have := htail1.const_mul (K0 / s)
    exact this
  have hhCm : Measurable hC := by
    simp only [hhC]
    refine Measurable.const_mul (Measurable.add ?_ ?_) _
    · exact (by fun_prop : Measurable fun v : ℝ => Real.exp (-μ * |v|)).indicator measurableSet_Ioi
    · exact (by fun_prop : Measurable fun v : ℝ => Real.exp (-μ * |v|)).indicator measurableSet_Iio
  have hhC0 : ∀ v, 0 ≤ hC v := fun v => by
    simp only [hhC, indicator]
    split_ifs <;> positivity
  obtain ⟨hs2, hs2v⟩ := vsh_strip hhCi hhCm ℓ measurableSet_Icc hI₁fin
  set S0 : Set (ℝ × ℝ) := {m : ℝ × ℝ | |m.1 - m.2 + ℓ| ≤ C₀} with hS0
  have hS0m : MeasurableSet S0 := measurableSet_le (by fun_prop) measurable_const
  have hDS : MeasurableSet (D \ S0) := hDm.diff hS0m
  -- on `D \ S0` the first bound is `hC`
  have hB1eq : ∀ m ∈ D \ S0, K0 / s * Real.exp (-μ * |m.1 - m.2 + ℓ|) = hC (m.1 - m.2 + ℓ) := by
    intro m hm
    have hlt : C₀ < |m.1 - m.2 + ℓ| := by
      by_contra hn; exact hm.2 (not_lt.1 hn)
    simp only [hhC]
    rcases le_or_gt 0 (m.1 - m.2 + ℓ) with h | h
    · rw [abs_of_nonneg h] at hlt
      rw [indicator_of_mem (show m.1 - m.2 + ℓ ∈ Ioi C₀ from hlt),
        indicator_of_notMem (show m.1 - m.2 + ℓ ∉ Iio (-C₀) by simp; linarith), add_zero]
    · rw [abs_of_neg h] at hlt
      rw [indicator_of_mem (show m.1 - m.2 + ℓ ∈ Iio (-C₀) by simp; linarith),
        indicator_of_notMem (show m.1 - m.2 + ℓ ∉ Ioi C₀ by simp; linarith), zero_add]
  have hstep1 : ∫ m in D \ S0, κ m ≤
      ∫ m in D \ S0, (K0 / s * Real.exp (-μ * |m.1 - m.2 + ℓ|) + cB * ind m.2) :=
    setIntegral_mono_on (hκD.mono_set diff_subset) (hbd_int.mono_set diff_subset) hDS
      (fun m hm => hpw m hm.1)
  have hstep2 : ∫ m in D \ S0, (K0 / s * Real.exp (-μ * |m.1 - m.2 + ℓ|) + cB * ind m.2) =
      (∫ m in D \ S0, hC (m.1 - m.2 + ℓ)) + ∫ m in D \ S0, cB * ind m.2 := by
    rw [integral_add ((hB1D.mono_set diff_subset)) (hB2i.mono_set diff_subset)]
    congr 1
    exact setIntegral_congr_fun hDS hB1eq
  have hstep3 : ∫ m in D \ S0, hC (m.1 - m.2 + ℓ) ≤
      ∫ m in Icc (s * a) (s * b) ×ˢ (univ : Set ℝ), hC (m.1 - m.2 + ℓ) :=
    setIntegral_mono_set hs2 (ae_of_all _ fun m => hhC0 _)
      (HasSubset.Subset.eventuallyLE (fun m hm => ⟨hm.1.1, mem_univ _⟩))
  have hstep4 : ∫ m in D \ S0, cB * ind m.2 ≤ ∫ m in D, cB * ind m.2 :=
    setIntegral_mono_set hB2i (ae_of_all _ fun m => mul_nonneg hcB0 (hind0 _))
      (HasSubset.Subset.eventuallyLE diff_subset)
  have hhCint : ∫ v, hC v = K0 / s * (2 / μ * Real.exp (-μ * C₀)) := by
    simp only [hhC]
    rw [integral_const_mul, htail2]
  calc ∫ m in D \ S0, κ m ≤ _ := hstep1.trans (hstep2.le.trans (add_le_add hstep3 hstep4))
    _ ≤ (volume (Icc (s * a) (s * b))).toReal * (K0 / s * (2 / μ * Real.exp (-μ * C₀))) +
        s * (b - a) * cB * 2 := by
        rw [hs2v, hhCint]; linarith
    _ = _ := by
        rw [hI₁r, hcB]
        field_simp

/-- Private: `E(m) > 0` for `m > 0`. -/
private lemma vsh_Efun_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    0 < Efun β m := by
  obtain ⟨cE, CE, hcE, -, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  exact lt_of_lt_of_le (mul_pos hcE (lt_min hm one_pos)) (hE m hm).1

/-- Private: nonnegativity of the lag kernel. -/
private lemma vsh_kernel_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {s : ℝ} (hs : 0 < s) (ℓ : ℤ)
    {m₁ m₂ : ℝ} (h1 : 0 < m₁) (h2 : 0 < m₂) :
    0 ≤ DLag β (Qm β m₁) (Qm β m₂) ℓ / (Real.pi ^ 2 * s * Efun β m₁ * Efun β m₂) := by
  have := vsh_Efun_pos hβ0 hβ1 h1
  have := vsh_Efun_pos hβ0 hβ1 h2
  exact div_nonneg (vsh_DLag_nonneg hβ0 (vsh_Qm hβ0 hβ1 h1).1.le (vsh_Qm hβ0 hβ1 h2).1.le ℓ)
    (by positivity)

/-- Private: the test-function limit for the lag kernel, in the form used by `vsh_core1`. -/
private lemma vsh_kernel_test {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (γ : ℕ → ℝ)
    (hγ0 : ∀ n, 0 < γ n) (hγT : Tendsto γ atTop atTop) (ℓ : ℕ → ℤ) {τ : ℝ} (hτ : 0 < τ)
    (hℓ : Tendsto (fun n => (ℓ n : ℝ) / γ n) atTop (𝓝 τ)) (φ : ℝ × ℝ → ℝ)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hφt : tsupport φ ⊆ Ioi 0 ×ˢ Ioi 0) :
    (∀ n, Integrable (fun m : ℝ × ℝ => φ (m.1 / γ n, m.2 / γ n) *
      (DLag β (Qm β m.1) (Qm β m.2) (ℓ n) /
        (Real.pi ^ 2 * γ n * Efun β m.1 * Efun β m.2)))) ∧
    Tendsto (fun n => ∫ m : ℝ × ℝ, φ (m.1 / γ n, m.2 / γ n) *
      (DLag β (Qm β m.1) (Qm β m.2) (ℓ n) /
        (Real.pi ^ 2 * γ n * Efun β m.1 * Efun β m.2))) atTop (𝓝 (∫ r : ℝ, φ (r, r + τ))) := by
  have hγ : Tendsto (fun n => (γ n * γ n) / γ n) atTop atTop := by
    convert hγT using 1
    funext n
    exact mul_div_cancel_right₀ _ (hγ0 n).ne'
  have hloc := lem_app_pl_localization_iii_top hβ0 hβ1 (fun n => γ n * γ n) ℓ γ hγ0 hγT hτ hγ hℓ
    φ hφc hφs hφt
  simp only [← mul_div_assoc]
  exact hloc

/-- Private: a.e.-strong measurability of the lag kernel on the rectangle, via test functions. -/
private lemma vsh_kernel_meas {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (γ : ℕ → ℝ)
    (hγ0 : ∀ n, 0 < γ n) (hγT : Tendsto γ atTop atTop) (ℓ : ℕ → ℤ) {τ : ℝ} (hτ : 0 < τ)
    (hℓ : Tendsto (fun n => (ℓ n : ℝ) / γ n) atTop (𝓝 τ)) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (n : ℕ) :
    AEStronglyMeasurable (fun m : ℝ × ℝ => DLag β (Qm β m.1) (Qm β m.2) (ℓ n) /
      (Real.pi ^ 2 * γ n * Efun β m.1 * Efun β m.2))
      (volume.restrict (Icc (γ n * a) (γ n * b) ×ˢ Ioo 0 (γ n))) := by
  obtain ⟨f₁, hc1, hcs1, hs1, h011, hl1, hu1, hp1⟩ := vsh_trap_exists (a / 2) (b + a) (a / 2) (by positivity)
  have hej : ∀ j : ℕ, (0 : ℝ) < 1 / (2 * ((j : ℝ) + 2)) := fun j => by positivity
  choose f₂ hc2 hcs2 hs2 h012 hl2 hu2 hp2 using
    fun j : ℕ => vsh_trap_exists (1 / (2 * ((j : ℝ) + 2))) 2 (1 / (2 * ((j : ℝ) + 2))) (hej j)
  let φ : ℕ → ℝ × ℝ → ℝ := fun j p => f₁ p.1 * f₂ j p.2
  have hφc : ∀ j, Continuous (φ j) := fun j => (hc1.comp continuous_fst).mul (hc2 j |>.comp continuous_snd)
  have hφsupp : ∀ j, Function.support (φ j) ⊆ Icc (a / 2) (b + a) ×ˢ Icc (1 / (2 * ((j : ℝ) + 2))) 2 := by
    intro j p hp
    constructor
    · by_contra h
      exact hp (by simp only [φ]; rw [image_eq_zero_of_notMem_tsupport (fun h' => h (hs1 h')), zero_mul])
    · by_contra h
      exact hp (by simp only [φ]; rw [image_eq_zero_of_notMem_tsupport (fun h' => h (hs2 j h')), mul_zero])
  have hφcs : ∀ j, HasCompactSupport (φ j) := fun j =>
    HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc) (fun p hp => by
      by_contra h
      exact hp (hφsupp j h))
  have hφts : ∀ j, tsupport (φ j) ⊆ Ioi 0 ×ˢ Ioi 0 := fun j => by
    refine (closure_minimal (hφsupp j) (isClosed_Icc.prod isClosed_Icc)).trans ?_
    rintro p ⟨h1, h2⟩
    exact ⟨show 0 < p.1 by linarith [h1.1], show 0 < p.2 by linarith [h2.1, hej j]⟩
  have hint := fun j => (vsh_kernel_test hβ0 hβ1 γ hγ0 hγT ℓ hτ hℓ (φ j) (hφc j) (hφcs j) (hφts j)).1 n
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun j m => φ j (m.1 / γ n, m.2 / γ n) *
      (DLag β (Qm β m.1) (Qm β m.2) (ℓ n) / (Real.pi ^ 2 * γ n * Efun β m.1 * Efun β m.2)))
    (fun j => (hint j).aestronglyMeasurable.restrict) ?_
  refine (ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Ioo)).2 (ae_of_all _ fun m hm => ?_)
  have hγn := hγ0 n
  have hm1 : a ≤ m.1 / γ n := by rw [le_div_iff₀ hγn, mul_comm]; exact hm.1.1
  have hm1' : m.1 / γ n ≤ b := by rw [div_le_iff₀ hγn, mul_comm]; exact hm.1.2
  have hm2 : 0 < m.2 / γ n := div_pos hm.2.1 hγn
  have hm2' : m.2 / γ n < 1 := by rw [div_lt_one hγn]; exact hm.2.2
  obtain ⟨j₀, hj₀⟩ := exists_nat_one_div_lt hm2
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop j₀] with j hj
  have hjj : 1 / ((j : ℝ) + 1) ≤ 1 / ((j₀ : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    have : (j₀ : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  have hlow : 1 / (2 * ((j : ℝ) + 2)) + 1 / (2 * ((j : ℝ) + 2)) ≤ m.2 / γ n := by
    have : 1 / (2 * ((j : ℝ) + 2)) + 1 / (2 * ((j : ℝ) + 2)) ≤ 1 / ((j : ℝ) + 1) := by
      have e : 1 / (2 * ((j : ℝ) + 2)) + 1 / (2 * ((j : ℝ) + 2)) = 1 / ((j : ℝ) + 2) := by
        field_simp; ring
      rw [e]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have hup : m.2 / γ n ≤ 2 - 1 / (2 * ((j : ℝ) + 2)) := by
    have : 1 / (2 * ((j : ℝ) + 2)) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
    linarith
  have e1 : f₁ (m.1 / γ n) = 1 := hp1 _ (by linarith) (by linarith)
  have e2 : f₂ j (m.2 / γ n) = 1 := hp2 j _ hlow hup
  simp only [φ]
  rw [e1, e2, one_mul, one_mul]

/-- Private: integrability and off-shell mass of the lag kernel on the compact-`p` rectangle. -/
private lemma vsh_kernel_off {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (γ : ℕ → ℝ)
    (hγ0 : ∀ n, 0 < γ n) (hγT : Tendsto γ atTop atTop) (ℓ : ℕ → ℤ) {τ : ℝ} (hτ : 0 < τ)
    (hℓ : Tendsto (fun n => (ℓ n : ℝ) / γ n) atTop (𝓝 τ)) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    (∀ᶠ n in atTop, IntegrableOn (fun m : ℝ × ℝ => DLag β (Qm β m.1) (Qm β m.2) (ℓ n) /
      (Real.pi ^ 2 * γ n * Efun β m.1 * Efun β m.2))
      (Icc (γ n * a) (γ n * b) ×ˢ Ioo 0 (γ n))) ∧
    ∀ η > 0, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ n in atTop,
      ∫ m in Icc (γ n * a) (γ n * b) ×ˢ Ioo 0 (γ n) \ {m : ℝ × ℝ | |m.1 - m.2 + ℓ n| ≤ C₀},
        DLag β (Qm β m.1) (Qm β m.2) (ℓ n) /
          (Real.pi ^ 2 * γ n * Efun β m.1 * Efun β m.2) ≤ η := by
  obtain ⟨K, μ, hμ, hpw⟩ := vsh_kernel_pw hβ0 hβ1
  have hev : ∀ᶠ n in atTop, 0 ≤ ℓ n ∧ 1 ≤ γ n * a := by
    filter_upwards [(tendsto_order.1 hℓ).1 0 hτ, hγT.eventually_ge_atTop (1 / a)] with n h1 h2
    refine ⟨?_, ?_⟩
    · have : (0 : ℝ) < ℓ n := (div_pos_iff_of_pos_right (hγ0 n)).1 h1
      exact_mod_cast this.le
    · have := (div_le_iff₀ ha).1 h2
      linarith
  have key : ∀ n, 0 ≤ ℓ n → 1 ≤ γ n * a →
      IntegrableOn (fun m : ℝ × ℝ => DLag β (Qm β m.1) (Qm β m.2) (ℓ n) /
        (Real.pi ^ 2 * γ n * Efun β m.1 * Efun β m.2))
        (Icc (γ n * a) (γ n * b) ×ˢ Ioo 0 (γ n)) ∧
      ∀ C₀ : ℝ, 0 ≤ C₀ →
        ∫ m in Icc (γ n * a) (γ n * b) ×ˢ Ioo 0 (γ n) \ {m : ℝ × ℝ | |m.1 - m.2 + ℓ n| ≤ C₀},
          DLag β (Qm β m.1) (Qm β m.2) (ℓ n) /
            (Real.pi ^ 2 * γ n * Efun β m.1 * Efun β m.2) ≤
        (b - a) * |K| * (2 / μ * Real.exp (-μ * C₀) + 2 * Real.exp (-μ * (γ n * a - 1))) := by
    intro n hn0 hn1
    refine vsh_off_det (hγ0 n) hab (abs_nonneg K) hμ (by exact_mod_cast hn0) hn1
      (vsh_kernel_meas hβ0 hβ1 γ hγ0 hγT ℓ hτ hℓ ha hab n) ?_ ?_
    · intro m hm
      exact (hpw (γ n) (ℓ n) (hγ0 n) hn0 m.1 m.2 (hn1.trans hm.1.1) hm.2.1).1
    · intro m hm
      have h1 : 1 ≤ m.1 := hn1.trans hm.1.1
      refine ((hpw (γ n) (ℓ n) (hγ0 n) hn0 m.1 m.2 h1 hm.2.1).2).trans ?_
      have hind : 0 ≤ 1 + (Ioo (0 : ℝ) 1).indicator (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) m.2 :=
        add_nonneg zero_le_one (indicator_nonneg (fun x hx => Real.rpow_nonneg hx.1.le _) _)
      have hK : K / γ n ≤ |K| / γ n := div_le_div_of_nonneg_right (le_abs_self K) (hγ0 n).le
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le) hind
  refine ⟨?_, fun η hη => ?_⟩
  · filter_upwards [hev] with n hn using (key n hn.1 hn.2).1
  · set R : ℝ := (b - a) * |K| with hR
    have hR0 : 0 ≤ R := mul_nonneg (by linarith) (abs_nonneg K)
    have h1 : Tendsto (fun C : ℝ => R * (2 / μ) * Real.exp (-(μ * C))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hμ)).const_mul (R * (2 / μ))
      simpa using this
    obtain ⟨C₀, hC₀, hC₀0⟩ := ((eventually_ge_atTop (0 : ℝ)).and
      (h1.eventually (gt_mem_nhds (show (0 : ℝ) < η / 2 by linarith)))).exists
    refine ⟨C₀, hC₀, ?_⟩
    have h2 : Tendsto (fun n => R * 2 * Real.exp (-(μ * (γ n * a - 1)))) atTop (𝓝 0) := by
      have h3 : Tendsto (fun n => γ n * a - 1) atTop atTop :=
        tendsto_atTop_add_const_right _ (-1) (hγT.atTop_mul_const ha)
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp (h3.const_mul_atTop hμ)).const_mul (R * 2)
      simpa using this
    filter_upwards [hev, h2.eventually (gt_mem_nhds (show (0 : ℝ) < η / 2 by linarith))]
      with n hn hn2
    refine ((key n hn.1 hn.2).2 C₀ hC₀).trans ?_
    have e : (b - a) * |K| * (2 / μ * Real.exp (-μ * C₀) + 2 * Real.exp (-μ * (γ n * a - 1))) =
        R * (2 / μ) * Real.exp (-(μ * C₀)) + R * 2 * Real.exp (-(μ * (γ n * a - 1))) := by
      rw [hR]; ring_nf
    rw [e]
    linarith


/-- Private: sum identity for the participation fractions. -/
private lemma vsh_part_sum {α : ℝ} {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B) (hc : 0 < c)
    {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    0 < partLam B (plSpec α c N) m ∧
      ∑ j : Fin N, partF B (plSpec α c N) j m = (B : ℝ) * m := by
  have hpos : ∀ j, 0 < plSpec α c N j := fun j => by
    unfold plSpec; exact mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)
  have hsurj := (def_app_pl_participation_bij (plSpec α c N) hB hN hpos).1.surjOn hm
  have hΛ : 0 < partLam B (plSpec α c N) m := Function.invFunOn_mem hsurj
  have hMN : partMN B (plSpec α c N) (partLam B (plSpec α c N) m) = m := Function.invFunOn_eq hsurj
  refine ⟨hΛ, ?_⟩
  have hB' : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  unfold partMN at hMN
  unfold partF
  have : ∑ j : Fin N, partLam B (plSpec α c N) m * plSpec α c N j /
      (1 + partLam B (plSpec α c N) m * plSpec α c N j) = (B : ℝ) * m := by
    calc _ = (B : ℝ) * ((B : ℝ)⁻¹ * ∑ i : Fin N, partLam B (plSpec α c N) m * plSpec α c N i /
          (1 + partLam B (plSpec α c N) m * plSpec α c N i)) := by field_simp
      _ = _ := by rw [hMN]
  exact this

/-- Private: the two participation inequalities for a single row. -/
private lemma vsh_row_ineq {α : ℝ} (hα : 0 < α) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    rowFrac i * gammaOf N B * partF B (plSpec α c N) i m ≤ m ∧
    gammaOf N B * (1 - partF B (plSpec α c N) i m) ≤ 2 ^ (1 + α) * (gammaOf N B - m) := by
  obtain ⟨hΛ, hsum⟩ := vsh_part_sum (α := α) hN hB hc hm
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hγ : gammaOf N B = (N : ℝ) / B := rfl
  have hμ : ∀ j : Fin N, 0 < plSpec α c N j := fun j => by
    unfold plSpec; exact mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)
  have hmu_anti : ∀ j k : Fin N, j ≤ k → plSpec α c N k ≤ plSpec α c N j := by
    intro j k hjk
    unfold plSpec
    refine mul_le_mul_of_nonneg_left ?_ hc.le
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (neg_nonpos.2 hα.le)
    have : (j : ℕ) ≤ (k : ℕ) := hjk
    have : ((j : ℕ) : ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  set Λ := partLam B (plSpec α c N) m with hΛdef
  have hf : ∀ j : Fin N, partF B (plSpec α c N) j m = Λ * plSpec α c N j / (1 + Λ * plSpec α c N j) :=
    fun j => rfl
  have hf0 : ∀ j : Fin N, 0 ≤ partF B (plSpec α c N) j m := fun j => by
    rw [hf]; have := hμ j; positivity
  have hf1 : ∀ j : Fin N, 1 - partF B (plSpec α c N) j m = 1 / (1 + Λ * plSpec α c N j) := fun j => by
    rw [hf]; have := hμ j; field_simp; ring
  have hf1pos : ∀ j : Fin N, 0 ≤ 1 - partF B (plSpec α c N) j m := fun j => by
    rw [hf1]; have := hμ j; positivity
  constructor
  · -- first inequality
    have h1 : ∀ j ∈ Finset.Iic i, partF B (plSpec α c N) i m ≤ partF B (plSpec α c N) j m := by
      intro j hj
      have hji : j ≤ i := Finset.mem_Iic.1 hj
      have hmu := hmu_anti j i hji
      rw [hf, hf]
      have := hμ i
      have := hμ j
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hmu hΛ.le]
    have h2 : (Finset.Iic i).card • partF B (plSpec α c N) i m ≤
        ∑ j ∈ Finset.Iic i, partF B (plSpec α c N) j m := Finset.card_nsmul_le_sum _ _ _ h1
    have h3 : ∑ j ∈ Finset.Iic i, partF B (plSpec α c N) j m ≤
        ∑ j : Fin N, partF B (plSpec α c N) j m :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hf0 j)
    rw [nsmul_eq_mul] at h2
    rw [hsum] at h3
    have hi1 : (((Finset.Iic i).card : ℕ) : ℝ) = rowIdx i := by
      rw [Fin.card_Iic]; unfold rowIdx; push_cast; ring
    rw [hi1] at h2
    have hrf : rowFrac i * gammaOf N B = rowIdx i / B := by
      unfold rowFrac; rw [hγ]; field_simp
    rw [hrf, div_mul_eq_mul_div, div_le_iff₀ hBr]
    linarith
  · -- second inequality
    have hsum1 : ∑ j : Fin N, (1 - partF B (plSpec α c N) j m) = (B : ℝ) * (gammaOf N B - m) := by
      rw [Finset.sum_sub_distrib, hsum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      rw [hγ]; field_simp
    set K : Fin N := ⟨N / 2, Nat.div_lt_self hN (by norm_num)⟩ with hK
    have h2a : (1 : ℝ) ≤ (2 : ℝ) ^ α := Real.one_le_rpow (by norm_num) hα.le
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ α := by positivity
    have h1 : ∀ j ∈ Finset.Ici K, (2 : ℝ)⁻¹ ^ α * (1 - partF B (plSpec α c N) i m) ≤
        1 - partF B (plSpec α c N) j m := by
      intro j hj
      have hjK' : K ≤ j := Finset.mem_Ici.1 hj
      have hjK : N / 2 ≤ (j : ℕ) := hjK'
      have hmu : plSpec α c N j ≤ (2 : ℝ) ^ α * plSpec α c N i := by
        unfold plSpec
        have hi1 : ((i : ℕ) : ℝ) + 1 ≤ N := by
          have : (i : ℕ) + 1 ≤ N := i.2
          exact_mod_cast this
        have hj1 : (N : ℝ) / 2 ≤ ((j : ℕ) : ℝ) + 1 := by
          have h2 : N ≤ 2 * (N / 2) + 1 := by omega
          have h3 : ((N / 2 : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hjK
          have h4 : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h2
          linarith
        have hle : (((i : ℕ) : ℝ) + 1) / 2 ≤ ((j : ℕ) : ℝ) + 1 := by linarith
        have hh := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (((i : ℕ) : ℝ) + 1) / 2)
          hle (neg_nonpos.2 hα.le)
        have e : ((((i : ℕ) : ℝ) + 1) / 2) ^ (-α) = (2 : ℝ) ^ α * (((i : ℕ) : ℝ) + 1) ^ (-α) := by
          rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
            Real.rpow_neg (by positivity : (0:ℝ) ≤ ((i : ℕ) : ℝ) + 1)]
          field_simp
        rw [e] at hh
        calc c * (((j : ℕ) : ℝ) + 1) ^ (-α) ≤ c * ((2 : ℝ) ^ α * (((i : ℕ) : ℝ) + 1) ^ (-α)) :=
              mul_le_mul_of_nonneg_left hh hc.le
          _ = _ := by ring
      rw [hf1, hf1]
      have hi := hμ i
      have hj := hμ j
      have h8 : 1 + Λ * plSpec α c N j ≤ (2 : ℝ) ^ α * (1 + Λ * plSpec α c N i) := by
        nlinarith [mul_le_mul_of_nonneg_left hmu hΛ.le]
      have hinv : (2 : ℝ)⁻¹ ^ α = ((2 : ℝ) ^ α)⁻¹ := Real.inv_rpow (by norm_num) α
      rw [hinv, show ((2 : ℝ) ^ α)⁻¹ * (1 / (1 + Λ * plSpec α c N i)) =
        1 / ((2 : ℝ) ^ α * (1 + Λ * plSpec α c N i)) by field_simp]
      exact one_div_le_one_div_of_le (by positivity) h8
    have h2 : (Finset.Ici K).card • ((2 : ℝ)⁻¹ ^ α * (1 - partF B (plSpec α c N) i m)) ≤
        ∑ j ∈ Finset.Ici K, (1 - partF B (plSpec α c N) j m) := Finset.card_nsmul_le_sum _ _ _ h1
    have h3 : ∑ j ∈ Finset.Ici K, (1 - partF B (plSpec α c N) j m) ≤
        ∑ j : Fin N, (1 - partF B (plSpec α c N) j m) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hf1pos j)
    rw [nsmul_eq_mul, hsum1] at *
    have hcard : (N : ℝ) / 2 ≤ (((Finset.Ici K).card : ℕ) : ℝ) := by
      rw [Fin.card_Ici]
      have : N ≤ 2 * (N - K.val) := by simp only [hK]; omega
      have h5 : (N : ℝ) ≤ 2 * ((N - K.val : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    have hinv : (2 : ℝ)⁻¹ ^ α = ((2 : ℝ) ^ α)⁻¹ := Real.inv_rpow (by norm_num) α
    rw [hinv] at h2
    have hf1' := hf1pos i
    have h6 : (N : ℝ) / 2 * (((2 : ℝ) ^ α)⁻¹ * (1 - partF B (plSpec α c N) i m)) ≤
        (B : ℝ) * (gammaOf N B - m) := by
      calc _ ≤ (((Finset.Ici K).card : ℕ) : ℝ) * (((2 : ℝ) ^ α)⁻¹ * (1 - partF B (plSpec α c N) i m)) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ ≤ _ := h2.trans h3
    have h7 : (2 : ℝ) ^ (1 + α) = 2 * (2 : ℝ) ^ α := by
      rw [Real.rpow_add (by norm_num), Real.rpow_one]
    rw [h7, hγ]
    rw [div_mul_eq_mul_div, div_le_iff₀ hBr]
    have : (N : ℝ) * (1 - partF B (plSpec α c N) i m) ≤ 2 * (2 : ℝ) ^ α * ((gammaOf N B - m) * B) := by
      have h9 : (N : ℝ) / 2 * (((2 : ℝ) ^ α)⁻¹ * (1 - partF B (plSpec α c N) i m)) * (2 * (2 : ℝ) ^ α) =
          (N : ℝ) * (1 - partF B (plSpec α c N) i m) := by field_simp
      rw [← h9]
      have := mul_le_mul_of_nonneg_right h6 (by positivity : (0 : ℝ) ≤ 2 * (2 : ℝ) ^ α)
      nlinarith
    rw [hγ] at this
    linarith

/-- Private: `0 < f_i(m) < 1`. -/
private lemma vsh_f_mem {α : ℝ} {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B) (hc : 0 < c)
    (i : Fin N) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    0 < partF B (plSpec α c N) i m ∧ partF B (plSpec α c N) i m < 1 := by
  obtain ⟨hΛ, -⟩ := vsh_part_sum (α := α) hN hB hc hm
  have hμ : 0 < plSpec α c N i := by
    unfold plSpec; exact mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)
  unfold partF
  have h := mul_pos hΛ hμ
  constructor
  · positivity
  · rw [div_lt_one (by linarith)]; linarith

/-- Private: row bounds for `g_i`, uniform in the row (`g² ≤ 1/x`, and `g ≲ (γ-m)/γ` for `m ≥ γ/2`). -/
private lemma vsh_g_bounds {α : ℝ} (hα : 0 < α) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    0 ≤ gRow B (plSpec α c N) i m ∧ gRow B (plSpec α c N) i m ^ 2 ≤ 1 / rowFrac i ∧
    (gammaOf N B / 2 ≤ m → gRow B (plSpec α c N) i m ≤
      Real.sqrt (2 * 2 ^ (1 + α)) * ((gammaOf N B - m) / gammaOf N B)) := by
  obtain ⟨hf0, hf1⟩ := vsh_f_mem (α := α) hN hB hc i hm
  obtain ⟨hr1, hr2⟩ := vsh_row_ineq hα hN hB hc i hm
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hγ : 0 < gammaOf N B := by unfold gammaOf; positivity
  have hm0 := hm.1
  have hmγ := hm.2
  have hrf : 0 < rowFrac i := by unfold rowFrac rowIdx; positivity
  set f := partF B (plSpec α c N) i m with hfdef
  have hq : 0 ≤ (gammaOf N B - m) / m := div_nonneg (by linarith) hm0.le
  have hgeq : gRow B (plSpec α c N) i m = Real.sqrt (f * (1 - f) * ((gammaOf N B - m) / m)) := by
    unfold gRow; rw [← hfdef, Real.sqrt_mul (show 0 ≤ f * (1 - f) by nlinarith) ((gammaOf N B - m) / m)]
  have hg2 : gRow B (plSpec α c N) i m ^ 2 = f * (1 - f) * ((gammaOf N B - m) / m) := by
    rw [hgeq, Real.sq_sqrt (by have := mul_nonneg (mul_nonneg hf0.le (by linarith : 0 ≤ 1 - f)) hq; linarith)]
  have hg0 : 0 ≤ gRow B (plSpec α c N) i m := by
    rw [hgeq]; exact Real.sqrt_nonneg _
  refine ⟨hg0, ?_, ?_⟩
  · rw [hg2]
    have h1 : f * (1 - f) * ((gammaOf N B - m) / m) ≤ f * gammaOf N B / m := by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ hm0.le
      have : (1 - f) * (gammaOf N B - m) ≤ gammaOf N B := by nlinarith
      nlinarith [hf0]
    refine h1.trans ?_
    rw [div_le_div_iff₀ hm0 hrf]
    nlinarith
  · intro hmh
    have hmg : 0 < m := hm0
    rw [hgeq]
    have hfrac : (gammaOf N B - m) / gammaOf N B ≥ 0 := div_nonneg (by linarith) hγ.le
    have hsq : f * (1 - f) * ((gammaOf N B - m) / m) ≤
        2 * 2 ^ (1 + α) * ((gammaOf N B - m) / gammaOf N B) ^ 2 := by
      have h1 : 1 - f ≤ 2 ^ (1 + α) * ((gammaOf N B - m) / gammaOf N B) := by
        rw [mul_div_assoc', le_div_iff₀ hγ]; nlinarith [hr2]
      have h2 : (gammaOf N B - m) / m ≤ 2 * ((gammaOf N B - m) / gammaOf N B) := by
        rw [div_le_iff₀ hm0]
        have : (gammaOf N B - m) / gammaOf N B * 2 * m ≥ gammaOf N B - m := by
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hγ]
          nlinarith
        nlinarith
      have h3 : f * (1 - f) ≤ 1 - f := by nlinarith
      calc f * (1 - f) * ((gammaOf N B - m) / m) ≤ (1 - f) * ((gammaOf N B - m) / m) :=
            mul_le_mul_of_nonneg_right h3 hq
        _ ≤ (2 ^ (1 + α) * ((gammaOf N B - m) / gammaOf N B)) * (2 * ((gammaOf N B - m) / gammaOf N B)) :=
            mul_le_mul h1 h2 hq (by positivity)
        _ = _ := by ring
    calc Real.sqrt (f * (1 - f) * ((gammaOf N B - m) / m))
        ≤ Real.sqrt (2 * 2 ^ (1 + α) * ((gammaOf N B - m) / gammaOf N B) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = _ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hfrac]

/-- Private: uniform bound on `g_i ϑ_N E` over a row family with `x ≥ x₀`. -/
private lemma vsh_q_bound {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) {x₀ : ℝ}
    (hx₀ : 0 < x₀) :
    ∃ Q : ℝ, ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → 1 ≤ gammaOf N B →
      ∀ i : Fin N, x₀ ≤ rowFrac i → ∀ m ∈ Ioo 0 (gammaOf N B),
        0 ≤ gRow B (plSpec α c N) i m * (thetaN β B (plSpec α c N) m * Efun β m) ∧
        gRow B (plSpec α c N) i m * (thetaN β B (plSpec α c N) m * Efun β m) ≤ Q := by
  obtain ⟨Cθ, hCθ⟩ := lem_app_pl_elasticity_ii hα hβ0 hβ1
  obtain ⟨cE, CE, hcE, hcCE, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  refine ⟨4 * |Cθ| * CE * max (Real.sqrt (1 / x₀)) (Real.sqrt (2 * 2 ^ (1 + α))), ?_⟩
  intro N B c hN hB hc hγ1 i hix m hm
  have hγ : 0 < gammaOf N B := by linarith
  have hm0 := hm.1
  have hmγ := hm.2
  obtain ⟨hθ, h1Eθ⟩ := hCθ N B c hN hB hc m hm
  obtain ⟨hg0, hg2, hgB⟩ := vsh_g_bounds hα hN hB hc i hm
  have hmin : 0 < min m 1 := lt_min hm0 one_pos
  have hEpos : 0 < Efun β m := lt_of_lt_of_le (mul_pos hcE hmin) (hE m hm0).1
  have hEle : Efun β m ≤ CE * min m 1 := (hE m hm0).2
  have hθpos : 0 < thetaN β B (plSpec α c N) m := by
    by_contra h
    push_neg at h
    nlinarith
  have hγm : 0 < gammaOf N B - m := by linarith
  set S : ℝ := 1 + 1 / m + 1 / (gammaOf N B - m) with hS
  have hS0 : 0 ≤ S := by positivity
  have hθS : thetaN β B (plSpec α c N) m ≤ |Cθ| * S := hθ.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hS0)
  have hCE0 : 0 ≤ CE := by linarith [mul_pos hcE hmin, hcCE]
  have hθE : thetaN β B (plSpec α c N) m * Efun β m ≤ |Cθ| * S * (CE * min m 1) :=
    mul_le_mul hθS hEle hEpos.le (by positivity)
  have hq0 : 0 ≤ gRow B (plSpec α c N) i m * (thetaN β B (plSpec α c N) m * Efun β m) :=
    mul_nonneg hg0 (mul_nonneg hθpos.le hEpos.le)
  refine ⟨hq0, ?_⟩
  set G1 := Real.sqrt (1 / x₀) with hG1
  set G2 := Real.sqrt (2 * 2 ^ (1 + α)) with hG2
  have hG1' : 0 ≤ G1 := Real.sqrt_nonneg _
  have hG2' : 0 ≤ G2 := Real.sqrt_nonneg _
  have hΘ : 0 ≤ |Cθ| * CE := mul_nonneg (abs_nonneg _) hCE0
  rcases le_or_gt m (gammaOf N B / 2) with hA | hB'
  · -- `m ≤ γ/2`
    have hgG : gRow B (plSpec α c N) i m ≤ G1 := by
      apply Real.le_sqrt_of_sq_le
      refine hg2.trans ?_
      exact one_div_le_one_div_of_le hx₀ hix
    have hSm : S * min m 1 ≤ 4 := by
      have a1 : min m 1 ≤ 1 := min_le_right _ _
      have a2 : (1 / m) * min m 1 ≤ 1 := by
        calc (1 / m) * min m 1 ≤ (1 / m) * m :=
              mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
          _ = 1 := by field_simp
      have a3 : (1 / (gammaOf N B - m)) * min m 1 ≤ 2 := by
        have : 1 / (gammaOf N B - m) ≤ 2 := by
          rw [div_le_iff₀ hγm]; linarith
        calc (1 / (gammaOf N B - m)) * min m 1 ≤ 2 * 1 :=
              mul_le_mul this a1 hmin.le (by norm_num)
          _ = 2 := by ring
      calc S * min m 1 = min m 1 + (1 / m) * min m 1 + (1 / (gammaOf N B - m)) * min m 1 := by
            rw [hS]; ring
        _ ≤ 4 := by linarith
    have hqq : thetaN β B (plSpec α c N) m * Efun β m ≤ 4 * (|Cθ| * CE) := by
      calc _ ≤ |Cθ| * S * (CE * min m 1) := hθE
        _ = |Cθ| * CE * (S * min m 1) := by ring
        _ ≤ |Cθ| * CE * 4 := mul_le_mul_of_nonneg_left hSm hΘ
        _ = _ := by ring
    calc gRow B (plSpec α c N) i m * (thetaN β B (plSpec α c N) m * Efun β m)
        ≤ G1 * (4 * (|Cθ| * CE)) := mul_le_mul hgG hqq (mul_nonneg hθpos.le hEpos.le) hG1'
      _ ≤ max G1 G2 * (4 * (|Cθ| * CE)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = _ := by ring
  · -- `m ≥ γ/2`
    have hgG := hgB hB'.le
    have hfr : 0 ≤ (gammaOf N B - m) / gammaOf N B := div_nonneg hγm.le hγ.le
    have hfr1 : (gammaOf N B - m) / gammaOf N B ≤ 1 := by
      rw [div_le_one hγ]; linarith
    have hSm : (gammaOf N B - m) / gammaOf N B * S ≤ 4 := by
      have b1 : (gammaOf N B - m) / gammaOf N B * 1 ≤ 1 := by linarith
      have b2 : (gammaOf N B - m) / gammaOf N B * (1 / m) ≤ 2 := by
        have : 1 / m ≤ 2 := by
          rw [div_le_iff₀ hm0]; linarith
        calc _ ≤ 1 * 2 := mul_le_mul hfr1 this (by positivity) (by norm_num)
          _ = 2 := by ring
      have b3 : (gammaOf N B - m) / gammaOf N B * (1 / (gammaOf N B - m)) ≤ 1 := by
        have : (gammaOf N B - m) / gammaOf N B * (1 / (gammaOf N B - m)) = 1 / gammaOf N B := by
          field_simp
        rw [this]
        rw [div_le_one hγ]; exact hγ1
      calc (gammaOf N B - m) / gammaOf N B * S =
          (gammaOf N B - m) / gammaOf N B * 1 + (gammaOf N B - m) / gammaOf N B * (1 / m) +
            (gammaOf N B - m) / gammaOf N B * (1 / (gammaOf N B - m)) := by rw [hS]; ring
        _ ≤ 4 := by linarith
    have hmin1 : min m 1 ≤ 1 := min_le_right _ _
    have hqq : thetaN β B (plSpec α c N) m * Efun β m ≤ |Cθ| * CE * S := by
      calc _ ≤ |Cθ| * S * (CE * min m 1) := hθE
        _ ≤ |Cθ| * S * (CE * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmin1 hCE0) (by positivity)
        _ = _ := by ring
    calc gRow B (plSpec α c N) i m * (thetaN β B (plSpec α c N) m * Efun β m)
        ≤ (G2 * ((gammaOf N B - m) / gammaOf N B)) * (|Cθ| * CE * S) :=
          mul_le_mul hgG hqq (mul_nonneg hθpos.le hEpos.le) (by positivity)
      _ = G2 * (|Cθ| * CE) * ((gammaOf N B - m) / gammaOf N B * S) := by ring
      _ ≤ G2 * (|Cθ| * CE) * 4 := mul_le_mul_of_nonneg_left hSm (by positivity)
      _ ≤ max G1 G2 * (|Cθ| * CE) * 4 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hΘ) (by norm_num)
      _ = _ := by ring


/-- Private: uniform lower bound for `Δ^N_ℓ` and uniform bound for the weight ratio `Φ`. -/
private lemma vsh_Phi_bound {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) {x : ℝ} (hx : x ∈ Ioc 0 1)
    (i : ∀ n, Fin (N n)) (hix : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 x))
    {τ : ℝ} (hτ : 0 < τ) (ℓ : ℕ → ℤ)
    (hℓ : Tendsto (fun n => (ℓ n : ℝ) / gammaOf (N n) (B n)) atTop (𝓝 τ))
    (Φ : ℕ → ℝ → ℝ → ℝ)
    (hΦ : ∀ n m₁ m₂, Φ n m₁ m₂ =
      gRow (B n) (plSpec α (c n) (N n)) (i n) m₁ * gRow (B n) (plSpec α (c n) (N n)) (i n) m₂ *
        (thetaN β (B n) (plSpec α (c n) (N n)) m₁ * Efun β m₁) *
        (thetaN β (B n) (plSpec α (c n) (N n)) m₂ * Efun β m₂) /
        deltaN β (B n) (plSpec α (c n) (N n)) (ℓ n) m₁ m₂) :
    ∃ κ₀ M : ℝ, 0 < κ₀ ∧ ∀ᶠ n in atTop, ∀ m₁ ∈ Ioo 0 (gammaOf (N n) (B n)),
      ∀ m₂ ∈ Ioo 0 (gammaOf (N n) (B n)),
        κ₀ ≤ deltaN β (B n) (plSpec α (c n) (N n)) (ℓ n) m₁ m₂ ∧ |Φ n m₁ m₂| ≤ M := by
  have hx0 : 0 < x := hx.1
  obtain ⟨Q, hQ⟩ := vsh_q_bound (α := α) (β := β) R.hα R.hβ0 R.hβ1 (half_pos hx0)
  obtain ⟨κ₀, hκ₀, γ₀, hloc⟩ := lem_app_pl_localization_ii R.hα R.hβ0 R.hβ1 (τ / 2) (half_pos hτ)
  refine ⟨κ₀, Q * Q / κ₀, hκ₀, ?_⟩
  filter_upwards [(tendsto_order.1 hix).1 (x / 2) (half_lt_self hx0),
    R.hγ.eventually_ge_atTop (max γ₀ 1), (tendsto_order.1 hℓ).1 (τ / 2) (half_lt_self hτ)]
    with n hxn hγn hln
  intro m₁ hm₁ m₂ hm₂
  have hγ0 : 0 < gammaOf (N n) (B n) := hm₁.1.trans hm₁.2
  have hγ' : γ₀ ≤ gammaOf (N n) (B n) := (le_max_left _ _).trans hγn
  have hγ1 : 1 ≤ gammaOf (N n) (B n) := (le_max_right _ _).trans hγn
  have hlag : τ / 2 * gammaOf (N n) (B n) ≤ (ℓ n : ℝ) := by
    have := (le_div_iff₀ hγ0).1 hln.le
    exact this
  have hΔ := hloc (N n) (B n) (c n) (R.hNpos n) (R.hBpos n) (R.hcpos n) hγ' (ℓ n) hlag m₁ m₂ hm₁ hm₂
  refine ⟨hΔ, ?_⟩
  obtain ⟨h10, h11⟩ := hQ (N n) (B n) (c n) (R.hNpos n) (R.hBpos n) (R.hcpos n) hγ1 (i n)
    hxn.le m₁ hm₁
  obtain ⟨h20, h21⟩ := hQ (N n) (B n) (c n) (R.hNpos n) (R.hBpos n) (R.hcpos n) hγ1 (i n)
    hxn.le m₂ hm₂
  rw [hΦ]
  have e : gRow (B n) (plSpec α (c n) (N n)) (i n) m₁ * gRow (B n) (plSpec α (c n) (N n)) (i n) m₂ *
      (thetaN β (B n) (plSpec α (c n) (N n)) m₁ * Efun β m₁) *
      (thetaN β (B n) (plSpec α (c n) (N n)) m₂ * Efun β m₂) =
      (gRow (B n) (plSpec α (c n) (N n)) (i n) m₁ *
        (thetaN β (B n) (plSpec α (c n) (N n)) m₁ * Efun β m₁)) *
      (gRow (B n) (plSpec α (c n) (N n)) (i n) m₂ *
        (thetaN β (B n) (plSpec α (c n) (N n)) m₂ * Efun β m₂)) := by ring
  rw [e, abs_div, abs_of_nonneg (mul_nonneg h10 h20),
    abs_of_pos (lt_of_lt_of_le hκ₀ hΔ)]
  calc _ ≤ (Q * Q) / deltaN β (B n) (plSpec α (c n) (N n)) (ℓ n) m₁ m₂ :=
        div_le_div_of_nonneg_right (mul_le_mul h11 h21 h20 (h10.trans h11)) (lt_of_lt_of_le hκ₀ hΔ).le
    _ ≤ Q * Q / κ₀ := div_le_div_of_nonneg_left (mul_nonneg (h10.trans h11) (h10.trans h11)) hκ₀ hΔ

/-- Private: continuity and positivity of the limiting profile integrand on `[a,b]`. -/
private lemma vsh_G_prop {α : ℝ} (hα : 0 < α) {x : ℝ} (hx0 : 0 < x) {τ : ℝ} (hτ : 0 < τ)
    {a b : ℝ} (hK : Icc a b ⊆ Ioo 0 (1 - τ)) :
    ContinuousOn (fun p => profA α x p * profA α x (p + τ) / profDeltaC α p (p + τ))
      (Icc a b) ∧
    ∀ p ∈ Icc a b, 0 < profA α x p * profA α x (p + τ) / profDeltaC α p (p + τ) := by
  have hp01 : ∀ p ∈ Icc a b, p ∈ Ioo (0 : ℝ) 1 := fun p hp =>
    ⟨(hK hp).1, by linarith [(hK hp).2]⟩
  have hq01 : ∀ p ∈ Icc a b, p + τ ∈ Ioo (0 : ℝ) 1 := fun p hp =>
    ⟨by linarith [(hK hp).1], by linarith [(hK hp).2]⟩
  have hcV : ContinuousOn (contV α) (Ioo 0 1) := vsh_contV_cont hα
  have hX : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
  have hF : ContinuousOn (profF α x) (Ioo 0 1) := by
    unfold profF
    refine hcV.div (hcV.add continuousOn_const) (fun p hp => ?_)
    have := (vs_contV_spec hα hp).1
    exact (by positivity : (0 : ℝ) < contV α p + x ^ α).ne'
  have hUpos : ∀ p ∈ Ioo (0 : ℝ) 1, 0 < profU α p := fun p hp => by
    unfold profU
    have := (vs_contV_spec hα hp).1
    have : 0 < p * (1 - p) := mul_pos hp.1 (by linarith [hp.2])
    positivity
  have hU : ContinuousOn (profU α) (Ioo 0 1) := by
    unfold profU
    refine hcV.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id)) (fun p hp => ?_)
    exact (mul_pos hp.1 (by linarith [hp.2])).ne'
  have hshift : ContinuousOn (fun p : ℝ => p + τ) (Icc a b) :=
    (continuous_id.add continuous_const).continuousOn
  have hmaps : MapsTo (fun p : ℝ => p + τ) (Icc a b) (Ioo 0 1) := fun p hp => hq01 p hp
  have hF' : ContinuousOn (fun p => profF α x (p + τ)) (Icc a b) := hF.comp hshift hmaps
  have hU' : ContinuousOn (fun p => profU α (p + τ)) (Icc a b) := hU.comp hshift hmaps
  have hFa : ContinuousOn (profF α x) (Icc a b) := hF.mono (fun p hp => hp01 p hp)
  have hUa : ContinuousOn (profU α) (Icc a b) := hU.mono (fun p hp => hp01 p hp)
  have hform : ContinuousOn (fun p => (profF α x (p + τ) - profF α x p) / τ *
      Real.sqrt (profU α p / profU α (p + τ))) (Icc a b) :=
    ((hF'.sub hFa).div_const τ).mul (Real.continuous_sqrt.comp_continuousOn
      (hUa.div hU' (fun p hp => (hUpos _ (hq01 p hp)).ne')))
  refine ⟨hform.congr (fun p hp =>
    vs_pointwise hα hx0 (hK hp).1 hτ (by linarith [(hK hp).2])), fun p hp => ?_⟩
  rw [vs_pointwise hα hx0 (hK hp).1 hτ (by linarith [(hK hp).2])]
  have ha := (vs_contV_spec hα (hp01 p hp)).1
  have hab : contV α p < contV α (p + τ) :=
    vs_contV_lt hα (hp01 p hp) (hq01 p hp) (by linarith)
  have hF : profF α x p < profF α x (p + τ) := by
    unfold profF
    rw [div_lt_div_iff₀ (by positivity) (by linarith [(vs_contV_spec hα (hq01 p hp)).1])]
    nlinarith
  have h1 : 0 < (profF α x (p + τ) - profF α x p) / τ := div_pos (by linarith) hτ
  have h2 : 0 < Real.sqrt (profU α p / profU α (p + τ)) :=
    Real.sqrt_pos.2 (div_pos (hUpos _ (hp01 p hp)) (hUpos _ (hq01 p hp)))
  positivity

/-- Private: continuity of `p ↦ A_x(p)` on `(0,1)`. -/
private lemma vsh_profA_cont {α : ℝ} (hα : 0 < α) {x : ℝ} (hx0 : 0 < x) :
    ContinuousOn (profA α x) (Ioo 0 1) := by
  have hcV : ContinuousOn (contV α) (Ioo 0 1) := vsh_contV_cont hα
  have hX : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
  have hF : ContinuousOn (profF α x) (Ioo 0 1) := by
    unfold profF
    refine hcV.div (hcV.add continuousOn_const) (fun p hp => ?_)
    have := (vs_contV_spec hα hp).1
    exact (by positivity : (0 : ℝ) < contV α p + x ^ α).ne'
  unfold profA
  refine Real.continuous_sqrt.comp_continuousOn ?_
  refine ContinuousOn.div ((hF.mul (continuousOn_const.sub hF)).mul
    (continuousOn_const.sub continuousOn_id)) continuousOn_id (fun p hp => hp.1.ne')

/-- Private: `ϑ_N E → 1` along sequences eventually inside a compact subset of `(0,1)`. -/
private lemma vsh_thetaE_seq {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (K : Set ℝ) (hK : K ⊆ Ioo 0 1) (hKc : IsCompact K)
    (pn : ℕ → ℝ) (hpn : ∀ᶠ n in atTop, pn n ∈ K) :
    Tendsto (fun n => thetaN β (B n) (plSpec α (c n) (N n)) (gammaOf (N n) (B n) * pn n) *
      Efun β (gammaOf (N n) (B n) * pn n)) atTop (𝓝 1) := by
  obtain ⟨C, hC⟩ := shell_theta_approx (α := α) (β := β) K hK hKc
  obtain ⟨cE, CE, hcE, hcCE, hE⟩ := lem_app_pl_weights_iii_E R.hβ0 R.hβ1
  have hev := hC N B c R
  have hlim : Tendsto (fun n => CE * (|C| / gammaOf (N n) (B n))) atTop (𝓝 0) := by
    have : Tendsto (fun n => |C| / gammaOf (N n) (B n)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop R.hγ
    simpa using this.const_mul CE
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hev, hpn] with n hn hpK
  have hγ : 0 < gammaOf (N n) (B n) := by
    unfold gammaOf; exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)
  have hp := hK hpK
  have hm0 : 0 < gammaOf (N n) (B n) * pn n := mul_pos hγ hp.1
  have hmin : 0 < min (gammaOf (N n) (B n) * pn n) 1 := lt_min hm0 one_pos
  have hEpos : 0 < Efun β (gammaOf (N n) (B n) * pn n) :=
    lt_of_lt_of_le (mul_pos hcE hmin) (hE _ hm0).1
  have hEle : Efun β (gammaOf (N n) (B n) * pn n) ≤ CE := by
    have := (hE _ hm0).2
    exact this.trans (mul_le_of_le_one_right (hcE.le.trans hcCE) (min_le_right _ _))
  have hb := hn (pn n) hpK
  rw [norm_norm, Real.norm_eq_abs]
  have e : thetaN β (B n) (plSpec α (c n) (N n)) (gammaOf (N n) (B n) * pn n) *
      Efun β (gammaOf (N n) (B n) * pn n) - 1 =
      Efun β (gammaOf (N n) (B n) * pn n) *
        (thetaN β (B n) (plSpec α (c n) (N n)) (gammaOf (N n) (B n) * pn n) -
          1 / Efun β (gammaOf (N n) (B n) * pn n)) := by
    field_simp
  rw [e, abs_mul, abs_of_pos hEpos]
  calc Efun β (gammaOf (N n) (B n) * pn n) *
        |thetaN β (B n) (plSpec α (c n) (N n)) (gammaOf (N n) (B n) * pn n) -
          1 / Efun β (gammaOf (N n) (B n) * pn n)| ≤ CE * (C / gammaOf (N n) (B n)) :=
        mul_le_mul hEle hb (abs_nonneg _) (hcE.le.trans hcCE)
    _ ≤ CE * (|C| / gammaOf (N n) (B n)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (le_abs_self C) hγ.le)
          (hcE.le.trans hcCE)

/-- Private: the weight ratio `Φ` converges along sequences of shell coordinates. -/
private lemma vsh_Phi_seq {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) {x : ℝ} (hx : x ∈ Ioc 0 1)
    (i : ∀ n, Fin (N n)) (hix : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 x))
    {τ : ℝ} (hτ : τ ∈ Ioo 0 1) (ℓ : ℕ → ℤ)
    (hℓ : Tendsto (fun n => (ℓ n : ℝ) / gammaOf (N n) (B n)) atTop (𝓝 τ))
    {a b : ℝ} (hK : Icc a b ⊆ Ioo 0 (1 - τ))
    (pn mn : ℕ → ℝ) (hpnK : ∀ n, pn n ∈ Icc a b) {p : ℝ} (hp : p ∈ Icc a b)
    (hpn : Tendsto pn atTop (𝓝 p)) (C₀ : ℝ)
    (hshell : ∀ n, |mn n - (gammaOf (N n) (B n) * pn n + (ℓ n : ℝ))| ≤ C₀) :
    Tendsto (fun n => gRow (B n) (plSpec α (c n) (N n)) (i n) (gammaOf (N n) (B n) * pn n) *
        gRow (B n) (plSpec α (c n) (N n)) (i n) (mn n) *
        (thetaN β (B n) (plSpec α (c n) (N n)) (gammaOf (N n) (B n) * pn n) *
          Efun β (gammaOf (N n) (B n) * pn n)) *
        (thetaN β (B n) (plSpec α (c n) (N n)) (mn n) * Efun β (mn n)) /
        deltaN β (B n) (plSpec α (c n) (N n)) (ℓ n) (gammaOf (N n) (B n) * pn n) (mn n))
      atTop (𝓝 (profA α x p * profA α x (p + τ) / profDeltaC α p (p + τ))) := by
  have hγ : ∀ n, 0 < gammaOf (N n) (B n) := fun n => by
    unfold gammaOf; exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)
  have hab : a ≤ b := hp.1.trans hp.2
  have ha0 : 0 < a := (hK (left_mem_Icc.2 hab)).1
  have hb1 : b < 1 - τ := (hK (right_mem_Icc.2 hab)).2
  have hKsub : Icc a b ⊆ Ioo 0 1 := fun q hq =>
    ⟨(hK hq).1, by linarith [(hK hq).2, hτ.1]⟩
  have hp0 : p ∈ Ioo (0 : ℝ) 1 := hKsub hp
  have hq0 : p + τ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp0.1, hτ.1], by linarith [hp.2]⟩
  -- the moving second coordinate
  set qn : ℕ → ℝ := fun n => mn n / gammaOf (N n) (B n) with hqndef
  have hmq : ∀ n, gammaOf (N n) (B n) * qn n = mn n := fun n => by
    simp only [hqndef]; exact mul_div_cancel₀ _ (hγ n).ne'
  have he : Tendsto (fun n => qn n - (pn n + (ℓ n : ℝ) / gammaOf (N n) (B n))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ (tendsto_const_nhds.div_atTop R.hγ (a := C₀))
    exact Filter.Eventually.of_forall fun n => by
      have heq : qn n - (pn n + (ℓ n : ℝ) / gammaOf (N n) (B n)) =
          (mn n - (gammaOf (N n) (B n) * pn n + (ℓ n : ℝ))) / gammaOf (N n) (B n) := by
        simp only [hqndef]; field_simp [(hγ n).ne']
      rw [Real.norm_eq_abs, heq, abs_div, abs_of_pos (hγ n)]
      exact div_le_div_of_nonneg_right (hshell n) (hγ n).le
  have hqn : Tendsto qn atTop (𝓝 (p + τ)) := by
    simpa only [sub_add_cancel, zero_add] using he.add (hpn.add hℓ)
  -- the shell limits of `Δ`
  obtain ⟨-, hDelta⟩ := vsh_shell_seq R hτ ℓ hℓ (Icc a b) hK isCompact_Icc pn mn hpnK hp hpn
    C₀ hshell
  -- nonvanishing of `Δ_c`
  have hGpos := (vsh_G_prop R.hα hx.1 hτ.1 hK).2 p hp
  have hΔc : profDeltaC α p (p + τ) ≠ 0 := fun h => by
    rw [h, div_zero] at hGpos; exact lt_irrefl _ hGpos
  -- first row coordinate
  have hAc := vsh_profA_cont R.hα hx.1
  have hg1 : Tendsto (fun n => gRow (B n) (plSpec α (c n) (N n)) (i n)
      (gammaOf (N n) (B n) * pn n)) atTop (𝓝 (profA α x p)) := by
    have hunif := shell_f_g_tendsto R hx i hix (Icc a b) hKsub isCompact_Icc
    have hdiff : Tendsto (fun n => gRow (B n) (plSpec α (c n) (N n)) (i n)
        (gammaOf (N n) (B n) * pn n) - profA α x (pn n)) atTop (𝓝 0) :=
      Metric.tendsto_nhds.2 fun ε hε => (hunif (ε / 2) (half_pos hε)).mono fun n hn => by
        rw [Real.dist_eq, sub_zero]
        exact lt_of_le_of_lt (hn (pn n) (hpnK n)).2 (half_lt_self hε)
    have hA : Tendsto (fun n => profA α x (pn n)) atTop (𝓝 (profA α x p)) :=
      (hAc.continuousAt (Ioo_mem_nhds hp0.1 hp0.2)).tendsto.comp hpn
    simpa using hdiff.add hA
  -- second row coordinate
  have hK'sub : Icc (a + τ / 2) ((b + τ + 1) / 2) ⊆ Ioo 0 1 := fun q hq =>
    ⟨by linarith [hq.1, hτ.1], by linarith [hq.2]⟩
  have hqmem : ∀ᶠ n in atTop, qn n ∈ Icc (a + τ / 2) ((b + τ + 1) / 2) :=
    (hqn.eventually (Ioo_mem_nhds (show a + τ / 2 < p + τ by linarith [hp.1, hτ.1])
      (show p + τ < (b + τ + 1) / 2 by linarith [hp.2]))).mono fun n hn => ⟨hn.1.le, hn.2.le⟩
  have hg2 : Tendsto (fun n => gRow (B n) (plSpec α (c n) (N n)) (i n) (mn n)) atTop
      (𝓝 (profA α x (p + τ))) := by
    have hunif := shell_f_g_tendsto R hx i hix (Icc (a + τ / 2) ((b + τ + 1) / 2)) hK'sub
      isCompact_Icc
    have hdiff : Tendsto (fun n => gRow (B n) (plSpec α (c n) (N n)) (i n) (mn n) -
        profA α x (qn n)) atTop (𝓝 0) :=
      Metric.tendsto_nhds.2 fun ε hε => ((hunif (ε / 2) (half_pos hε)).and hqmem).mono
        fun n hn => by
          rw [Real.dist_eq, sub_zero]
          have := (hn.1 (qn n) hn.2).2
          rw [hmq n] at this
          exact lt_of_le_of_lt this (half_lt_self hε)
    have hA : Tendsto (fun n => profA α x (qn n)) atTop (𝓝 (profA α x (p + τ))) :=
      (hAc.continuousAt (Ioo_mem_nhds hq0.1 hq0.2)).tendsto.comp hqn
    simpa using hdiff.add hA
  -- the products `ϑ E`
  have hte1 := vsh_thetaE_seq R (Icc a b) hKsub isCompact_Icc pn
    (Filter.Eventually.of_forall hpnK)
  have hte2 := vsh_thetaE_seq R (Icc (a + τ / 2) ((b + τ + 1) / 2)) hK'sub isCompact_Icc qn hqmem
  simp_rw [hmq] at hte2
  have hmain := (((hg1.mul hg2).mul hte1).mul hte2).div hDelta hΔc
  have h3 : Tendsto (fun n => gRow (B n) (plSpec α (c n) (N n)) (i n) (gammaOf (N n) (B n) * pn n) *
        gRow (B n) (plSpec α (c n) (N n)) (i n) (mn n) *
        (thetaN β (B n) (plSpec α (c n) (N n)) (gammaOf (N n) (B n) * pn n) *
          Efun β (gammaOf (N n) (B n) * pn n)) *
        (thetaN β (B n) (plSpec α (c n) (N n)) (mn n) * Efun β (mn n)) /
        deltaN β (B n) (plSpec α (c n) (N n)) (ℓ n) (gammaOf (N n) (B n) * pn n) (mn n))
      atTop (𝓝 (profA α x p * profA α x (p + τ) * 1 * 1 / profDeltaC α p (p + τ))) := hmain
  simpa using h3

/-- Private: uniform shell convergence of the weight ratio `Φ`. -/
private lemma vsh_Phi_shell {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) {x : ℝ} (hx : x ∈ Ioc 0 1)
    (i : ∀ n, Fin (N n)) (hix : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 x))
    {τ : ℝ} (hτ : τ ∈ Ioo 0 1) (ℓ : ℕ → ℤ)
    (hℓ : Tendsto (fun n => (ℓ n : ℝ) / gammaOf (N n) (B n)) atTop (𝓝 τ))
    {a b : ℝ} (hK : Icc a b ⊆ Ioo 0 (1 - τ))
    (Φ : ℕ → ℝ → ℝ → ℝ)
    (hΦ : ∀ n m₁ m₂, Φ n m₁ m₂ =
      gRow (B n) (plSpec α (c n) (N n)) (i n) m₁ * gRow (B n) (plSpec α (c n) (N n)) (i n) m₂ *
        (thetaN β (B n) (plSpec α (c n) (N n)) m₁ * Efun β m₁) *
        (thetaN β (B n) (plSpec α (c n) (N n)) m₂ * Efun β m₂) /
        deltaN β (B n) (plSpec α (c n) (N n)) (ℓ n) m₁ m₂) :
    ∀ ε > 0, ∀ C₀ : ℝ, ∀ᶠ n in atTop, ∀ p ∈ Icc a b, ∀ m₂ : ℝ,
      |m₂ - (gammaOf (N n) (B n) * p + (ℓ n : ℝ))| ≤ C₀ →
        |Φ n (gammaOf (N n) (B n) * p) m₂ -
          profA α x p * profA α x (p + τ) / profDeltaC α p (p + τ)| ≤ ε := by
  classical
  intro ε hε C₀
  by_contra hbad
  have hex : ∀ j : ℕ, ∃ n, j ≤ n ∧ ∃ p ∈ Icc a b, ∃ m₂ : ℝ,
      |m₂ - (gammaOf (N n) (B n) * p + (ℓ n : ℝ))| ≤ C₀ ∧
      ¬ (|Φ n (gammaOf (N n) (B n) * p) m₂ -
          profA α x p * profA α x (p + τ) / profDeltaC α p (p + τ)| ≤ ε) := by
    have hf := frequently_atTop.mp (not_eventually.mp hbad)
    intro j
    obtain ⟨n, hjn, hn⟩ := hf j
    simp only [not_forall] at hn
    obtain ⟨p, hp, m, hm, hfail⟩ := hn
    exact ⟨n, hjn, p, hp, m, hm, hfail⟩
  choose ns hns pn hpnK mn hshell hfail using hex
  obtain ⟨p, hp, φ, hφ, hconv⟩ := isCompact_Icc.tendsto_subseq hpnK
  have hnsTop : Tendsto ns atTop atTop := tendsto_atTop_mono hns tendsto_id
  have hsub : Tendsto (ns ∘ φ) atTop atTop := hnsTop.comp hφ.tendsto_atTop
  let R' : assum_app_pl_regime α β (N ∘ ns ∘ φ) (B ∘ ns ∘ φ) (c ∘ ns ∘ φ) :=
    { hα := R.hα, hβ0 := R.hβ0, hβ1 := R.hβ1
      hNpos := fun j => R.hNpos _, hBpos := fun j => R.hBpos _, hcpos := fun j => R.hcpos _
      hN := R.hN.comp hsub, hB := R.hB.comp hsub, hγ := R.hγ.comp hsub }
  have hℓ' : Tendsto (fun j => ((ℓ (ns (φ j))) : ℝ) /
      gammaOf (N (ns (φ j))) (B (ns (φ j)))) atTop (𝓝 τ) := hℓ.comp hsub
  have hix' : Tendsto (fun j => rowFrac (i (ns (φ j)))) atTop (𝓝 x) := hix.comp hsub
  have hlim := vsh_Phi_seq R' hx (fun j => i (ns (φ j))) hix' hτ (ℓ ∘ ns ∘ φ) hℓ' hK
    (pn ∘ φ) (mn ∘ φ) (fun j => hpnK (φ j)) hp hconv C₀ (fun j => hshell (φ j))
  have hlim' : Tendsto (fun j => Φ (ns (φ j)) (gammaOf (N (ns (φ j))) (B (ns (φ j))) * pn (φ j))
      (mn (φ j))) atTop (𝓝 (profA α x p * profA α x (p + τ) / profDeltaC α p (p + τ))) := by
    refine hlim.congr (fun j => ?_)
    rw [hΦ]
    rfl
  have hGc := (vsh_G_prop R.hα hx.1 hτ.1 hK).1
  have hGlim : Tendsto (fun j => profA α x (pn (φ j)) * profA α x (pn (φ j) + τ) /
      profDeltaC α (pn (φ j)) (pn (φ j) + τ)) atTop
      (𝓝 (profA α x p * profA α x (p + τ) / profDeltaC α p (p + τ))) :=
    (hGc p hp).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hconv, Filter.Eventually.of_forall (fun j => hpnK (φ j))⟩)
  have hdiff := hlim'.sub hGlim
  rw [sub_self] at hdiff
  obtain ⟨j, hj⟩ := (Metric.tendsto_nhds.1 hdiff ε hε).exists
  rw [Real.dist_eq, sub_zero] at hj
  exact hfail (φ j) hj.le

/-- Private: the iterated lag integral equals the rectangle integral of `Φ κ`. -/
private lemma vsh_T_identity {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (i : ∀ n, Fin (N n)) (ℓ : ℕ → ℤ)
    {a b : ℝ} (ha : 0 < a) (hb1 : b < 1)
    (Φ : ℕ → ℝ → ℝ → ℝ)
    (hΦ : ∀ n m₁ m₂, Φ n m₁ m₂ =
      gRow (B n) (plSpec α (c n) (N n)) (i n) m₁ * gRow (B n) (plSpec α (c n) (N n)) (i n) m₂ *
        (thetaN β (B n) (plSpec α (c n) (N n)) m₁ * Efun β m₁) *
        (thetaN β (B n) (plSpec α (c n) (N n)) m₂ * Efun β m₂) /
        deltaN β (B n) (plSpec α (c n) (N n)) (ℓ n) m₁ m₂)
    (κ : ℕ → ℝ × ℝ → ℝ)
    (hκ : ∀ n (m : ℝ × ℝ), κ n m = DLag β (Qm β m.1) (Qm β m.2) (ℓ n) /
      (Real.pi ^ 2 * gammaOf (N n) (B n) * Efun β m.1 * Efun β m.2))
    (κ₀ : ℝ) (hκ₀ : 0 < κ₀)
    (hΔ : ∀ᶠ n in atTop, ∀ m₁ ∈ Ioo 0 (gammaOf (N n) (B n)),
      ∀ m₂ ∈ Ioo 0 (gammaOf (N n) (B n)),
        κ₀ ≤ deltaN β (B n) (plSpec α (c n) (N n)) (ℓ n) m₁ m₂) :
    ∀ᶠ n in atTop,
      IntegrableOn (fun m : ℝ × ℝ => Φ n m.1 m.2 * κ n m)
        (Icc (gammaOf (N n) (B n) * a) (gammaOf (N n) (B n) * b) ×ˢ Ioo 0 (gammaOf (N n) (B n))) ∧
      (Real.pi ^ 2)⁻¹ * lagTerm β (B n) (plSpec α (c n) (N n)) (i n)
          ((fun p => gammaOf (N n) (B n) * p) '' Icc a b) (Ioo 0 (gammaOf (N n) (B n))) (ℓ n) =
        ∫ m in Icc (gammaOf (N n) (B n) * a) (gammaOf (N n) (B n) * b) ×ˢ
          Ioo 0 (gammaOf (N n) (B n)), Φ n m.1 m.2 * κ n m := by
  filter_upwards [hΔ] with n hΔn
  have hγ : 0 < gammaOf (N n) (B n) := by
    unfold gammaOf; exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)
  have hpos : ∀ j, 0 < plSpec α (c n) (N n) j := fun j => by
    unfold plSpec; exact mul_pos (R.hcpos n) (Real.rpow_pos_of_pos (by positivity) _)
  have hab : a ≤ b ∨ b < a := le_or_gt a b
  -- the rectangle sits inside the square
  have hsub : Icc (gammaOf (N n) (B n) * a) (gammaOf (N n) (B n) * b) ×ˢ Ioo 0 (gammaOf (N n) (B n)) ⊆
      Ioo 0 (gammaOf (N n) (B n)) ×ˢ Ioo 0 (gammaOf (N n) (B n)) := by
    rintro m ⟨h1, h2⟩
    refine ⟨⟨lt_of_lt_of_le (mul_pos hγ ha) h1.1, lt_of_le_of_lt h1.2 ?_⟩, h2⟩
    exact mul_lt_of_lt_one_right hγ hb1 |>.trans_le' le_rfl
  have hf := (lem_app_pl_age_iv R.hα R.hβ0 R.hβ1 (N n) (B n) (c n) (R.hNpos n) (R.hBpos n)
    (R.hcpos n) (i n)).2.2.1 (ℓ n)
  have hfD := hf.mono_set hsub
  -- the pointwise identity
  have hpw : ∀ m ∈ Icc (gammaOf (N n) (B n) * a) (gammaOf (N n) (B n) * b) ×ˢ
      Ioo 0 (gammaOf (N n) (B n)),
      (Real.pi ^ 2)⁻¹ * lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) (ℓ n) m.1 m.2 =
        Φ n m.1 m.2 * κ n m := by
    intro m hm
    have hm' := hsub hm
    have hΔm := lt_of_lt_of_le hκ₀ (hΔn m.1 hm'.1 m.2 hm'.2)
    have hΛ1 := (vsh_part_sum (α := α) (R.hNpos n) (R.hBpos n) (R.hcpos n) hm'.1).1
    have hΛ2 := (vsh_part_sum (α := α) (R.hNpos n) (R.hBpos n) (R.hcpos n) hm'.2).1
    have hE1 := vsh_Efun_pos R.hβ0 R.hβ1 hm'.1.1
    have hE2 := vsh_Efun_pos R.hβ0 R.hβ1 hm'.2.1
    have hW1 := Wpart_eq_gRow β (B n) (N n) (R.hNpos n) (R.hBpos n) (plSpec α (c n) (N n))
      (i n) (hpos (i n)) m.1 hm'.1 hΛ1
    have hW2 := Wpart_eq_gRow β (B n) (N n) (R.hNpos n) (R.hBpos n) (plSpec α (c n) (N n))
      (i n) (hpos (i n)) m.2 hm'.2 hΛ2
    rw [hΦ, hκ]
    unfold lagIntegrand lagNumer
    rw [hW1, hW2]
    have hsq : ((Real.sqrt (gammaOf (N n) (B n)))⁻¹ * (Real.sqrt (gammaOf (N n) (B n)))⁻¹) =
        (gammaOf (N n) (B n))⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hγ.le]
    have e1 : (Real.sqrt (gammaOf (N n) (B n)))⁻¹ * gRow (B n) (plSpec α (c n) (N n)) (i n) m.1 *
          thetaN β (B n) (plSpec α (c n) (N n)) m.1 *
        ((Real.sqrt (gammaOf (N n) (B n)))⁻¹ * gRow (B n) (plSpec α (c n) (N n)) (i n) m.2 *
          thetaN β (B n) (plSpec α (c n) (N n)) m.2) =
        ((Real.sqrt (gammaOf (N n) (B n)))⁻¹ * (Real.sqrt (gammaOf (N n) (B n)))⁻¹) *
          (gRow (B n) (plSpec α (c n) (N n)) (i n) m.1 *
            gRow (B n) (plSpec α (c n) (N n)) (i n) m.2 *
            thetaN β (B n) (plSpec α (c n) (N n)) m.1 *
            thetaN β (B n) (plSpec α (c n) (N n)) m.2) := by ring
    rw [e1, hsq]
    have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
    field_simp
  have hDm : MeasurableSet (Icc (gammaOf (N n) (B n) * a) (gammaOf (N n) (B n) * b) ×ˢ
      Ioo 0 (gammaOf (N n) (B n))) := measurableSet_Icc.prod measurableSet_Ioo
  have hI : IntegrableOn (fun m : ℝ × ℝ => (Real.pi ^ 2)⁻¹ *
      lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) (ℓ n) m.1 m.2)
      (Icc (gammaOf (N n) (B n) * a) (gammaOf (N n) (B n) * b) ×ˢ Ioo 0 (gammaOf (N n) (B n))) :=
    Integrable.const_mul hfD _
  refine ⟨IntegrableOn.congr_fun hI hpw hDm, ?_⟩
  unfold lagTerm
  rw [Set.image_mul_left_Icc' hγ]
  have h1 := setIntegral_prod (μ := volume) (ν := volume)
    (fun z : ℝ × ℝ => lagIntegrand β (B n) (plSpec α (c n) (N n)) (i n) (ℓ n) z.1 z.2)
    (s := Icc (gammaOf (N n) (B n) * a) (gammaOf (N n) (B n) * b)) (t := Ioo 0 (gammaOf (N n) (B n)))
    (by rw [← Measure.volume_eq_prod]; exact hfD)
  rw [← Measure.volume_eq_prod] at h1
  simp only at h1
  rw [← h1, ← integral_const_mul]
  exact setIntegral_congr_fun hDm (fun m hm => hpw m hm)

/-- The compact-`p` limit of the lag-`ℓ` integral: with `m₁ ∈ γK`, `K = [a,b] ⊆ (0,1-τ)` (the source's compact sets of `p`; intervals suffice for its use), the integral
of `eqn:app-pl-vol-zero` tends to `∫_K A_x(p)A_x(p+τ)/Δ_c(p,p+τ) dp` (task L-G.7b; proof step of
`thm:app-pl-volatility`(i), l.2221-2227; snapshot cr-2026-10-23). Uses `lem_app_pl_localization_iii_fin` (with `n = γ`, `ρ₀ = 1`). -/
theorem bulk_compact_limit {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) {x : ℝ} (hx : x ∈ Ioc 0 1)
    (i : ∀ n, Fin (N n)) (hix : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 x))
    {τ : ℝ} (hτ : τ ∈ Ioo 0 1) (ℓ : ℕ → ℤ)
    (hℓ : Tendsto (fun n => (ℓ n : ℝ) / gammaOf (N n) (B n)) atTop (𝓝 τ))
    (a b : ℝ) (hK : Icc a b ⊆ Ioo 0 (1 - τ)) :
    Tendsto (fun n => (Real.pi ^ 2)⁻¹ *
        lagTerm β (B n) (plSpec α (c n) (N n)) (i n)
          ((fun p => gammaOf (N n) (B n) * p) '' Icc a b) (Ioo 0 (gammaOf (N n) (B n))) (ℓ n))
      atTop (𝓝 (∫ p in Icc a b, profA α x p * profA α x (p + τ) / profDeltaC α p (p + τ))) := by
  classical
  by_cases hab : a ≤ b
  swap
  · have h0 : Icc a b = ∅ := Icc_eq_empty hab
    simp only [h0, Set.image_empty, lagTerm, Measure.restrict_empty, integral_zero_measure,
      mul_zero]
    exact tendsto_const_nhds
  have ha : 0 < a := (hK (left_mem_Icc.2 hab)).1
  have hb : b < 1 - τ := (hK (right_mem_Icc.2 hab)).2
  have hγ0 : ∀ n, 0 < gammaOf (N n) (B n) := fun n => by
    unfold gammaOf; exact div_pos (by exact_mod_cast R.hNpos n) (by exact_mod_cast R.hBpos n)
  have hγT : Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop := R.hγ
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℕ → ℝ → ℝ → ℝ, ∀ n m₁ m₂, Φ n m₁ m₂ =
      gRow (B n) (plSpec α (c n) (N n)) (i n) m₁ * gRow (B n) (plSpec α (c n) (N n)) (i n) m₂ *
        (thetaN β (B n) (plSpec α (c n) (N n)) m₁ * Efun β m₁) *
        (thetaN β (B n) (plSpec α (c n) (N n)) m₂ * Efun β m₂) /
        deltaN β (B n) (plSpec α (c n) (N n)) (ℓ n) m₁ m₂ :=
    ⟨fun n m₁ m₂ => gRow (B n) (plSpec α (c n) (N n)) (i n) m₁ *
        gRow (B n) (plSpec α (c n) (N n)) (i n) m₂ *
        (thetaN β (B n) (plSpec α (c n) (N n)) m₁ * Efun β m₁) *
        (thetaN β (B n) (plSpec α (c n) (N n)) m₂ * Efun β m₂) /
        deltaN β (B n) (plSpec α (c n) (N n)) (ℓ n) m₁ m₂, fun _ _ _ => rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℕ → ℝ × ℝ → ℝ, ∀ n (m : ℝ × ℝ), κ n m =
      DLag β (Qm β m.1) (Qm β m.2) (ℓ n) /
        (Real.pi ^ 2 * gammaOf (N n) (B n) * Efun β m.1 * Efun β m.2) :=
    ⟨fun n m => DLag β (Qm β m.1) (Qm β m.2) (ℓ n) /
        (Real.pi ^ 2 * gammaOf (N n) (B n) * Efun β m.1 * Efun β m.2), fun _ _ => rfl⟩
  obtain ⟨κ₀, M, hκ₀, hbd⟩ := vsh_Phi_bound R hx i hix hτ.1 ℓ hℓ Φ hΦ
  have hΔ : ∀ᶠ n in atTop, ∀ m₁ ∈ Ioo 0 (gammaOf (N n) (B n)),
      ∀ m₂ ∈ Ioo 0 (gammaOf (N n) (B n)),
        κ₀ ≤ deltaN β (B n) (plSpec α (c n) (N n)) (ℓ n) m₁ m₂ :=
    hbd.mono (fun n hn m₁ h₁ m₂ h₂ => (hn m₁ h₁ m₂ h₂).1)
  have hident := vsh_T_identity (b := b) R i ℓ ha (by linarith [hτ.1, hb]) Φ hΦ κ hκ κ₀ hκ₀ hΔ
  have hGprop := vsh_G_prop R.hα hx.1 hτ.1 hK
  have hshell := vsh_Phi_shell R hx i hix hτ ℓ hℓ hK Φ hΦ
  obtain ⟨hkint, hkoff⟩ := vsh_kernel_off R.hβ0 R.hβ1 (fun n => gammaOf (N n) (B n)) hγ0 hγT ℓ
    hτ.1 hℓ ha hab
  refine vsh_core1 (fun n => gammaOf (N n) (B n)) hγ0 hγT ℓ hτ.1 hℓ ha hab
    (by linarith [hτ.2, hb]) κ ?_ ?_ ?_ ?_ Φ M ?_ _ hGprop.1 hGprop.2 hshell _ ?_ ?_
  · intro n m h1 h2
    rw [hκ]
    exact vsh_kernel_nonneg R.hβ0 R.hβ1 (hγ0 n) (ℓ n) h1 h2
  · intro φ hc hs ht
    simp_rw [hκ]
    exact vsh_kernel_test R.hβ0 R.hβ1 (fun n => gammaOf (N n) (B n)) hγ0 hγT ℓ hτ.1 hℓ φ hc hs ht
  · have hκfun : ∀ n, κ n = fun m : ℝ × ℝ => DLag β (Qm β m.1) (Qm β m.2) (ℓ n) /
        (Real.pi ^ 2 * gammaOf (N n) (B n) * Efun β m.1 * Efun β m.2) := fun n => funext (hκ n)
    simp_rw [hκfun]
    exact hkint
  · intro η hη
    simp_rw [hκ]
    exact hkoff η hη
  · filter_upwards [hbd] with n hn m₁ hm₁ m₂ hm₂
    refine (hn m₁ ⟨lt_of_lt_of_le (mul_pos (hγ0 n) ha) hm₁.1, lt_of_le_of_lt hm₁.2 ?_⟩ m₂ hm₂).2
    exact mul_lt_of_lt_one_right (hγ0 n) (by linarith [hτ.1, hb])
  · exact (hident.mono fun n hn => hn.1)
  · exact (hident.mono fun n hn => hn.2)

/-! ## Uniform domination on rows `i/N ≥ x₀` -/

/-- Row bounds uniform in `i/N ≥ x₀`: `m ≥ c x₀^α γ f_i(m)`, `g_i ≤ C`, `g_i ≤ C(1-m/γ)` for `m ≥ γ/2`,
`ϑ_N ≤ C(1 + m⁻¹ + (γ-m)⁻¹)` (task L-G.7b; proof step of `thm:app-pl-volatility`(i), l.2229-2236;
snapshot cr-2026-10-23). -/
theorem row_bounds_x0 {α β : ℝ} (x₀ : ℝ) (hx₀ : x₀ ∈ Ioc 0 1) :
    ∃ C κ : ℝ, 0 < κ ∧ ∀ (N B : ℕ → ℕ) (c : ℕ → ℝ), assum_app_pl_regime α β N B c →
      ∀ᶠ n in atTop, ∀ i : Fin (N n), x₀ ≤ rowFrac i →
        ∀ m ∈ Ioo 0 (gammaOf (N n) (B n)),
          κ * x₀ ^ α * gammaOf (N n) (B n) * partF (B n) (plSpec α (c n) (N n)) i m ≤ m ∧
          gRow (B n) (plSpec α (c n) (N n)) i m ≤ C ∧
          (gammaOf (N n) (B n) / 2 ≤ m →
            gRow (B n) (plSpec α (c n) (N n)) i m ≤ C * (1 - m / gammaOf (N n) (B n))) ∧
          |thetaN β (B n) (plSpec α (c n) (N n)) m| ≤
            C * (1 + m⁻¹ + (gammaOf (N n) (B n) - m)⁻¹) := by
  have hx0 : 0 < x₀ := hx₀.1
  by_cases hreg : 0 < α ∧ 0 < β ∧ β < 1
  swap
  · refine ⟨0, 1, one_pos, fun N B c R => ?_⟩
    exact absurd ⟨R.hα, R.hβ0, R.hβ1⟩ hreg
  obtain ⟨hα, hβ0, hβ1⟩ := hreg
  obtain ⟨Cθ, hCθ⟩ := lem_app_pl_elasticity_ii hα hβ0 hβ1
  obtain ⟨cE, CE, hcE, -, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  set S := Real.sqrt (2 * 2 ^ (1 + α)) with hS
  refine ⟨max (Real.sqrt (1 / x₀)) (max S |Cθ|), x₀ / x₀ ^ α, div_pos hx0 (Real.rpow_pos_of_pos hx0 _),
    fun N B c R => Filter.Eventually.of_forall fun n i hix m hm => ?_⟩
  have hN := R.hNpos n
  have hB := R.hBpos n
  have hc := R.hcpos n
  obtain ⟨hr1, -⟩ := vsh_row_ineq hα hN hB hc i hm
  obtain ⟨hf0, hf1⟩ := vsh_f_mem (α := α) hN hB hc i hm
  obtain ⟨hg0, hg2, hgB⟩ := vsh_g_bounds hα hN hB hc i hm
  have hγ : 0 < gammaOf (N n) (B n) := hm.1.trans hm.2
  have hm0 := hm.1
  have hγm : 0 < gammaOf (N n) (B n) - m := by linarith [hm.2]
  have hxpos : 0 < x₀ ^ α := Real.rpow_pos_of_pos hx0 _
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : x₀ / x₀ ^ α * x₀ ^ α = x₀ := by field_simp
    rw [this]
    refine le_trans ?_ hr1
    have := mul_nonneg hγ.le hf0.le
    nlinarith
  · have h1 : gRow (B n) (plSpec α (c n) (N n)) i m ≤ Real.sqrt (1 / x₀) := by
      apply Real.le_sqrt_of_sq_le
      refine hg2.trans ?_
      exact one_div_le_one_div_of_le hx0 hix
    exact h1.trans (le_max_left _ _)
  · intro hmh
    have := hgB hmh
    have e : (gammaOf (N n) (B n) - m) / gammaOf (N n) (B n) = 1 - m / gammaOf (N n) (B n) := by
      field_simp
    rw [e] at this
    refine this.trans ?_
    refine mul_le_mul_of_nonneg_right ((le_max_left S |Cθ|).trans (le_max_right _ _)) ?_
    have : m / gammaOf (N n) (B n) ≤ 1 := by
      rw [div_le_one hγ]; exact hm.2.le
    linarith
  · obtain ⟨hθ, h1Eθ⟩ := hCθ (N n) (B n) (c n) hN hB hc m hm
    obtain ⟨hE1, -⟩ := hE m hm0
    have hmin : 0 < min m 1 := lt_min hm0 one_pos
    have hEpos : 0 < Efun β m := lt_of_lt_of_le (mul_pos hcE hmin) hE1
    have hθpos : 0 < thetaN β (B n) (plSpec α (c n) (N n)) m := by
      by_contra h
      push_neg at h
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hEpos.le h]
    rw [abs_of_pos hθpos]
    have hpos : 0 ≤ 1 + 1 / m + 1 / (gammaOf (N n) (B n) - m) := by positivity
    simp only [one_div] at hθ hpos
    refine hθ.trans ?_
    exact mul_le_mul_of_nonneg_right ((le_abs_self Cθ).trans
      ((le_max_right _ _).trans' (le_max_right _ _))) hpos

/-- Private: `W_i(m) = γ^{-1/2} g_i(m) ϑ_N(m)`. -/
private lemma vsh_W_eq {α β : ℝ} {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B) (hc : 0 < c)
    (i : Fin N) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    Wpart β B (plSpec α c N) i m =
      (Real.sqrt (gammaOf N B))⁻¹ * gRow B (plSpec α c N) i m * thetaN β B (plSpec α c N) m := by
  obtain ⟨hΛ, -⟩ := vsh_part_sum (α := α) hN hB hc hm
  have hμ : 0 < plSpec α c N i := by
    unfold plSpec; exact mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)
  have hm0 := hm.1
  have hγm : 0 < gammaOf N B - m := by linarith [hm.2]
  have hγ : 0 < gammaOf N B := hm0.trans hm.2
  set a := plSpec α c N i * partLam B (plSpec α c N) m with ha
  have ha0 : 0 < a := mul_pos hμ hΛ
  have hf : partF B (plSpec α c N) i m = a / (1 + a) := by
    unfold partF; rw [ha, mul_comm]
  have e1 : partF B (plSpec α c N) i m * (1 - partF B (plSpec α c N) i m) = a / (1 + a) ^ 2 := by
    rw [hf]; field_simp; ring
  unfold Wpart gRow
  rw [e1, ← ha]
  have h1 : Real.sqrt (a / (1 + a) ^ 2) = Real.sqrt a / (1 + a) := by
    rw [Real.sqrt_div ha0.le, Real.sqrt_sq (by linarith)]
  have h2 : Real.sqrt ((gammaOf N B - m) / m) = Real.sqrt (gammaOf N B - m) / Real.sqrt m :=
    Real.sqrt_div hγm.le m
  have h3 : Real.sqrt (1 - m / gammaOf N B) = Real.sqrt (gammaOf N B - m) / Real.sqrt (gammaOf N B) := by
    rw [← Real.sqrt_div hγm.le]; congr 1; field_simp
  rw [h1, h2, h3]
  have : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
  have : 0 < Real.sqrt (gammaOf N B) := Real.sqrt_pos.2 hγ
  have : 0 < 1 + a := by linarith
  field_simp

/-- Domination of the lag integrand for lags `ℓ ≥ τ₀γ` by `C γ⁻¹ g_i g_i ϑ_N ϑ_N 𝖣_ℓ`
(task L-G.7b; proof step of `thm:app-pl-volatility`(i), l.2236-2238, from `lem_app_pl_localization_ii`;
snapshot cr-2026-10-23). -/
theorem lag_integrand_majorant {α β : ℝ} (x₀ τ₀ : ℝ) (hx₀ : x₀ ∈ Ioc 0 1) (hτ₀ : 0 < τ₀) :
    ∃ C : ℝ, ∀ (N B : ℕ → ℕ) (c : ℕ → ℝ), assum_app_pl_regime α β N B c →
      ∀ᶠ n in atTop, ∀ i : Fin (N n), x₀ ≤ rowFrac i → ∀ ℓ : ℤ,
        τ₀ * gammaOf (N n) (B n) ≤ ℓ → ∀ m₁ ∈ Ioo 0 (gammaOf (N n) (B n)),
          ∀ m₂ ∈ Ioo 0 (gammaOf (N n) (B n)),
            |lagIntegrand β (B n) (plSpec α (c n) (N n)) i ℓ m₁ m₂| ≤
              C * lagMajorant β (B n) (plSpec α (c n) (N n)) i ℓ m₁ m₂ := by
  by_cases hreg : 0 < α ∧ 0 < β ∧ β < 1
  swap
  · refine ⟨0, fun N B c R => ?_⟩
    exact absurd ⟨R.hα, R.hβ0, R.hβ1⟩ hreg
  obtain ⟨hα, hβ0, hβ1⟩ := hreg
  obtain ⟨κ, hκ, γ₀, hloc⟩ := lem_app_pl_localization_ii hα hβ0 hβ1 τ₀ hτ₀
  refine ⟨κ⁻¹, fun N B c R => ?_⟩
  filter_upwards [R.hγ.eventually_ge_atTop γ₀] with n hγn
  intro i _ ℓ hℓ m₁ hm₁ m₂ hm₂
  have hΔ := hloc (N n) (B n) (c n) (R.hNpos n) (R.hBpos n) (R.hcpos n) hγn ℓ hℓ m₁ m₂ hm₁ hm₂
  have hγ : 0 < gammaOf (N n) (B n) := hm₁.1.trans hm₁.2
  unfold lagIntegrand lagNumer lagMajorant
  rw [vsh_W_eq (R.hNpos n) (R.hBpos n) (R.hcpos n) i hm₁,
    vsh_W_eq (R.hNpos n) (R.hBpos n) (R.hcpos n) i hm₂ (β := β) (α := α)]
  obtain ⟨hg1, -, -⟩ := vsh_g_bounds hα (R.hNpos n) (R.hBpos n) (R.hcpos n) i hm₁
  obtain ⟨hg2, -, -⟩ := vsh_g_bounds hα (R.hNpos n) (R.hBpos n) (R.hcpos n) i hm₂
  set γ := gammaOf (N n) (B n) with hγdef
  have hs : (Real.sqrt γ)⁻¹ * (Real.sqrt γ)⁻¹ = γ⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hγ.le]
  rw [abs_div, abs_of_pos (lt_of_lt_of_le hκ hΔ), div_eq_mul_inv]
  have hin : κ⁻¹ ≥ (deltaN β (B n) (plSpec α (c n) (N n)) ℓ m₁ m₂)⁻¹ :=
    inv_anti₀ hκ hΔ
  set T := |DLag β (Qm β m₁) (Qm β m₂) ℓ| with hT
  set Th1 := thetaN β (B n) (plSpec α (c n) (N n)) m₁
  set Th2 := thetaN β (B n) (plSpec α (c n) (N n)) m₂
  set g1 := gRow (B n) (plSpec α (c n) (N n)) i m₁
  set g2 := gRow (B n) (plSpec α (c n) (N n)) i m₂
  have hnum : |(Real.sqrt γ)⁻¹ * g1 * Th1 * ((Real.sqrt γ)⁻¹ * g2 * Th2) * DLag β (Qm β m₁) (Qm β m₂) ℓ| =
      γ⁻¹ * g1 * g2 * |Th1| * |Th2| * T := by
    have : (Real.sqrt γ)⁻¹ * g1 * Th1 * ((Real.sqrt γ)⁻¹ * g2 * Th2) * DLag β (Qm β m₁) (Qm β m₂) ℓ =
      ((Real.sqrt γ)⁻¹ * (Real.sqrt γ)⁻¹) * g1 * g2 * Th1 * Th2 * DLag β (Qm β m₁) (Qm β m₂) ℓ := by ring
    rw [this, hs]
    simp only [abs_mul, abs_of_nonneg hg1, abs_of_nonneg hg2, abs_of_nonneg (inv_nonneg.2 hγ.le), hT]
  rw [hnum]
  have h0 : 0 ≤ γ⁻¹ * g1 * g2 * |Th1| * |Th2| * T := by positivity
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right hin h0

/-! ### Helpers for `majorant_shell_mass` -/

private lemma msm_s_facts :
    Integrable ((Ioo (0:ℝ) 1).indicator (fun x : ℝ => x ^ (-(3 / 4 : ℝ)))) ∧
    ∫ x, (Ioo (0:ℝ) 1).indicator (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) x = 4 ∧
    (∀ x, 0 ≤ (Ioo (0:ℝ) 1).indicator (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) x) ∧
    Measurable ((Ioo (0:ℝ) 1).indicator (fun x : ℝ => x ^ (-(3 / 4 : ℝ)))) := by
  have hii : IntervalIntegrable (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hio : IntegrableOn (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hii
  have hio' : IntegrableOn (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) (Ioo 0 1) :=
    hio.mono_set Ioo_subset_Ioc_self
  refine ⟨(integrable_indicator_iff measurableSet_Ioo).2 hio', ?_, ?_, ?_⟩
  · rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by norm_num))]
    norm_num
  · intro x
    exact indicator_nonneg (fun x hx => Real.rpow_nonneg hx.1.le _) x
  · exact (Measurable.pow_const measurable_id _).indicator measurableSet_Ioo

private lemma msm_s_pw {m : ℝ} (hm : 0 < m) :
    (1 + 1 / m) * (min m 1) ^ (1 / 4 : ℝ) ≤
      2 * (1 + (Ioo (0:ℝ) 1).indicator (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) m) := by
  by_cases h1 : 1 ≤ m
  · rw [min_eq_right h1, Real.one_rpow, indicator_of_notMem (by simp [h1])]
    have : 1 / m ≤ 1 := by rw [div_le_one hm]; exact h1
    linarith
  · push_neg at h1
    rw [min_eq_left h1.le, indicator_of_mem (show m ∈ Ioo (0:ℝ) 1 from ⟨hm, h1⟩)]
    have h14 : m ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hm.le h1.le (by norm_num)
    have h34 : 1 ≤ m ^ (-(3 / 4 : ℝ)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hm h1.le (by norm_num)
    have e : (1 / m) * m ^ (1 / 4 : ℝ) = m ^ (-(3 / 4 : ℝ)) := by
      rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_add hm]; norm_num
    calc (1 + 1 / m) * m ^ (1 / 4 : ℝ) = m ^ (1 / 4 : ℝ) + (1 / m) * m ^ (1 / 4 : ℝ) := by ring
      _ ≤ 1 + m ^ (-(3 / 4 : ℝ)) := by rw [e]; linarith
      _ ≤ _ := by linarith

private lemma msm_wstrip {ω h : ℝ → ℝ} {I : Set ℝ} (hI : MeasurableSet I) (hω : IntegrableOn ω I)
    (hωm : Measurable ω) (hh : Integrable h) (hm : Measurable h) (c : ℝ) :
    IntegrableOn (fun m : ℝ × ℝ => ω m.1 * h (m.1 - m.2 + c)) (I ×ˢ univ) ∧
    ∫ m in I ×ˢ univ, ω m.1 * h (m.1 - m.2 + c) = (∫ x in I, ω x) * ∫ v, h v := by
  have hfm : Measurable (fun m : ℝ × ℝ => ω m.1 * h (m.1 - m.2 + c)) :=
    (hωm.comp measurable_fst).mul (hm.comp (by fun_prop))
  have hprod : (volume.restrict I).prod (volume.restrict (univ : Set ℝ)) =
      (volume : Measure (ℝ × ℝ)).restrict (I ×ˢ univ) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hshift : ∀ x : ℝ, ∫ y, h (x - y + c) = ∫ v, h v := by
    intro x
    have := integral_sub_left_eq_self h (volume : Measure ℝ) (x + c)
    simpa [show ∀ y : ℝ, x - y + c = x + c - y from fun y => by ring] using this
  have hint : Integrable (fun m : ℝ × ℝ => ω m.1 * h (m.1 - m.2 + c))
      ((volume.restrict I).prod (volume.restrict (univ : Set ℝ))) := by
    rw [Measure.restrict_univ]
    rw [integrable_prod_iff hfm.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun x => ?_, ?_⟩
    · have := (hh.comp_sub_left (x + c)).const_mul (ω x)
      simpa [show ∀ y : ℝ, x - y + c = x + c - y from fun y => by ring] using this
    · have : (fun x : ℝ => ∫ y, ‖ω x * h (x - y + c)‖) = fun x => ‖ω x‖ * ∫ v, ‖h v‖ := by
        funext x
        simp only [norm_mul]
        rw [integral_const_mul]
        congr 1
        have := integral_sub_left_eq_self (fun v => ‖h v‖) (volume : Measure ℝ) (x + c)
        simpa [show ∀ y : ℝ, x - y + c = x + c - y from fun y => by ring] using this
      rw [this]
      exact hω.norm.mul_const _
  rw [hprod] at hint
  refine ⟨hint, ?_⟩
  have h1 := setIntegral_prod (μ := volume) (ν := volume)
    (fun m : ℝ × ℝ => ω m.1 * h (m.1 - m.2 + c)) (s := I) (t := univ)
    (by rwa [Measure.volume_eq_prod] at hint)
  rw [Measure.volume_eq_prod, h1]
  have : ∀ x : ℝ, ∫ y in (univ : Set ℝ), ω x * h (x - y + c) = ω x * ∫ v, h v := by
    intro x
    rw [Measure.restrict_univ, integral_const_mul, hshift x]
  simp_rw [this]
  rw [integral_mul_const]

private lemma msm_wstrip_swap {h : ℝ → ℝ} {I : Set ℝ} (hI : MeasurableSet I)
    (hh : Integrable h) (hm : Measurable h) (c : ℝ) (hIf : volume I ≠ ⊤) :
    IntegrableOn (fun m : ℝ × ℝ => h (m.1 - m.2 + c)) (univ ×ˢ I) ∧
    ∫ m in univ ×ˢ I, h (m.1 - m.2 + c) = (volume I).toReal * ∫ v, h v := by
  have hω : IntegrableOn (fun _ : ℝ => (1:ℝ)) I := by
    refine integrableOn_const ?_
    exact hIf
  have key := msm_wstrip (ω := fun _ => (1:ℝ)) (h := fun v => h (-v)) hI hω measurable_const
    (hh.comp_neg) (hm.comp measurable_neg) (-c)
  have hsw : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume :=
    Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)
  have hset : (Prod.swap ⁻¹' (I ×ˢ (univ : Set ℝ))) = univ ×ˢ I := by
    ext p; simp
  have hemb : MeasurableEmbedding (Prod.swap : ℝ × ℝ → ℝ × ℝ) := MeasurableEquiv.prodComm.measurableEmbedding
  have hfun : ∀ p : ℝ × ℝ, h (p.1 - p.2 + c) =
      (fun m : ℝ × ℝ => (1:ℝ) * (fun v => h (-v)) (m.1 - m.2 + -c)) (Prod.swap p) := by
    intro p
    simp only [Prod.fst_swap, Prod.snd_swap, one_mul]
    congr 1; ring
  refine ⟨?_, ?_⟩
  · have := (hsw.integrableOn_comp_preimage hemb).2 key.1
    rw [hset] at this
    refine this.congr_fun (fun p _ => (hfun p).symm) (MeasurableSet.univ.prod hI)
  · have := hsw.setIntegral_preimage_emb hemb (fun m : ℝ × ℝ => (1:ℝ) * (fun v => h (-v)) (m.1 - m.2 + -c)) (I ×ˢ univ)
    rw [hset] at this
    simp_rw [← hfun] at this
    rw [this, key.2]
    simp only [one_mul, setIntegral_const, smul_eq_mul]
    rw [integral_neg_eq_self (fun v => h v) volume]
    simp [Measure.real]

private lemma msm_boxmul {a b : ℝ → ℝ} {I J : Set ℝ} (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (ha : IntegrableOn a I) (hb : IntegrableOn b J) :
    IntegrableOn (fun z : ℝ × ℝ => a z.1 * b z.2) (I ×ˢ J) ∧
    ∫ z in I ×ˢ J, a z.1 * b z.2 = (∫ x in I, a x) * ∫ y in J, b y := by
  have hprod : (volume : Measure (ℝ × ℝ)).restrict (I ×ˢ J) = (volume.restrict I).prod (volume.restrict J) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  refine ⟨?_, ?_⟩
  · unfold IntegrableOn
    rw [hprod]
    exact ha.mul_prod hb
  · rw [hprod]
    exact integral_prod_mul a b

private lemma msm_dom {f g : ℝ × ℝ → ℝ} {R : Set (ℝ × ℝ)} (hR : MeasurableSet R)
    (hm : AEStronglyMeasurable f (volume.restrict R)) (hg : IntegrableOn g R)
    (hfg : ∀ m ∈ R, 0 ≤ f m ∧ f m ≤ g m) :
    IntegrableOn f R ∧ ∫ m in R, f m ≤ ∫ m in R, g m := by
  have hint : IntegrableOn f R := by
    refine Integrable.mono' hg hm ?_
    refine (ae_restrict_iff' hR).2 (ae_of_all _ fun m hm => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hfg m hm).1]
    exact (hfg m hm).2
  refine ⟨hint, ?_⟩
  refine integral_mono_of_nonneg ?_ hg ?_
  · exact (ae_restrict_iff' hR).2 (ae_of_all _ fun m hm => (hfg m hm).1)
  · exact (ae_restrict_iff' hR).2 (ae_of_all _ fun m hm => (hfg m hm).2)

private lemma msm_exp_int {μ : ℝ} (hμ : 0 < μ) : ∫ v : ℝ, Real.exp (-μ * |v|) = 2 / μ := by
  have := integral_comp_abs (f := fun x : ℝ => Real.exp (-μ * x))
  rw [this]
  have h2 : ∫ x in Ioi (0:ℝ), Real.exp (-μ * x) = 1 / μ := by
    rw [integral_exp_mul_Ioi (by linarith) 0]
    field_simp
    simp
  rw [h2]; ring

private lemma msm_D_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ K μ : ℝ, 0 ≤ K ∧ 0 < μ ∧ μ = |Real.log β| / 2 ∧ ∀ (ℓ : ℤ), 0 ≤ ℓ → ∀ m₁ m₂ : ℝ, 0 < m₁ → 0 < m₂ →
      DLag β (Qm β m₁) (Qm β m₂) ℓ ≤
        K * (min m₁ 1) ^ (1 / 4 : ℝ) * (min m₂ 1) ^ (1 / 4 : ℝ) * Real.exp (-μ * |m₁ - m₂ + ℓ|) := by
  obtain ⟨-, -, C, hC⟩ := lem_app_pl_localization_i hβ0 hβ1
  have hlam : 0 < |Real.log β| := abs_pos.2 (Real.log_neg hβ0 hβ1).ne
  set lam := |Real.log β| with hlamdef
  refine ⟨|C| * (1 + 2 / lam), lam / 2, by positivity, by positivity, rfl, ?_⟩
  intro ℓ hℓ m₁ m₂ hm₁0 hm₂
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = ℓ := ⟨ℓ.toNat, Int.toNat_of_nonneg hℓ⟩
  have hDn : DLag β (Qm β m₁) (Qm β m₂) ℓ = DLagNat β (Qm β m₁) (Qm β m₂) n := by
    subst hn; simp [DLag]
  have hu : |m₁ - m₂ + ℓ| = |m₁ - m₂ + n| := by rw [← hn]; simp
  have hDb := hC n m₁ m₂ hm₁0 hm₂
  have hexp : (1 + |m₁ - m₂ + n|) * Real.exp (-lam * |m₁ - m₂ + n|) ≤
      (1 + 2 / lam) * Real.exp (-(lam / 2) * |m₁ - m₂ + n|) := by
    set x := |m₁ - m₂ + n| with hx
    have hx0 : 0 ≤ x := abs_nonneg _
    have h1 : 1 + x ≤ (1 + 2 / lam) * Real.exp (lam / 2 * x) := by
      have h2 : 1 + lam / 2 * x ≤ Real.exp (lam / 2 * x) := by linarith [Real.add_one_le_exp (lam / 2 * x)]
      have h3 : 1 + x ≤ (1 + 2 / lam) * (1 + lam / 2 * x) := by
        have : (1 + 2 / lam) * (1 + lam / 2 * x) = 1 + lam / 2 * x + 2 / lam + x := by
          field_simp
          ring
        rw [this]
        have : 0 ≤ lam / 2 * x := by positivity
        have : 0 ≤ 2 / lam := by positivity
        linarith
      exact h3.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    calc (1 + x) * Real.exp (-lam * x) ≤ ((1 + 2 / lam) * Real.exp (lam / 2 * x)) * Real.exp (-lam * x) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = (1 + 2 / lam) * Real.exp (-(lam / 2) * x) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hmin0 : 0 ≤ min (min m₁ m₂) 1 := le_min (le_min hm₁0.le hm₂.le) zero_le_one
  have h14 : Real.sqrt (min (min m₁ m₂) 1) ≤ (min m₁ 1) ^ (1 / 4 : ℝ) * (min m₂ 1) ^ (1 / 4 : ℝ) := by
    set x := min (min m₁ m₂) 1 with hx
    have e : Real.sqrt x = x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add' hmin0 (by norm_num), Real.sqrt_eq_rpow]; norm_num
    rw [e]
    have hxa : x ≤ min m₁ 1 := le_min ((min_le_left _ _).trans (min_le_left _ _)) (min_le_right _ _)
    have hxb : x ≤ min m₂ 1 := le_min ((min_le_left _ _).trans (min_le_right _ _)) (min_le_right _ _)
    exact mul_le_mul (Real.rpow_le_rpow hmin0 hxa (by norm_num)) (Real.rpow_le_rpow hmin0 hxb (by norm_num))
      (Real.rpow_nonneg hmin0 _) (Real.rpow_nonneg (le_min hm₁0.le zero_le_one) _)
  rw [hDn, hu]
  refine hDb.trans ?_
  have h0 : 0 ≤ (1 + |m₁ - m₂ + n|) * Real.exp (-lam * |m₁ - m₂ + n|) := by positivity
  calc C * Real.sqrt (min (min m₁ m₂) 1) * (1 + |m₁ - m₂ + n|) * Real.exp (-lam * |m₁ - m₂ + n|)
      = (C * Real.sqrt (min (min m₁ m₂) 1)) *
        ((1 + |m₁ - m₂ + n|) * Real.exp (-lam * |m₁ - m₂ + n|)) := by ring
    _ ≤ (|C| * ((min m₁ 1) ^ (1 / 4 : ℝ) * (min m₂ 1) ^ (1 / 4 : ℝ))) *
        ((1 + 2 / lam) * Real.exp (-(lam / 2) * |m₁ - m₂ + n|)) := by
        refine mul_le_mul ?_ hexp h0 (by positivity)
        exact mul_le_mul (le_abs_self C) h14 (Real.sqrt_nonneg _) (abs_nonneg _)
    _ = _ := by ring

private lemma msm_DLagNat_meas (β : ℝ) (ℓ : ℕ) : Measurable (fun q : ℝ × ℝ => DLagNat β q.1 q.2 ℓ) := by
  unfold DLagNat
  refine Measurable.tsum ?_
  intro a
  have hf : Measurable (fun z : (ℝ × ℝ) × ℝ =>
      β ^ ℓ * Real.sqrt (z.1.1 * z.1.2) * emaW β a ^ 2 * z.2 ^ 2 /
      ((1 + z.1.1 * emaW β a ^ 2 * z.2 ^ 2) * (1 + β ^ (2 * ℓ) * z.1.2 * emaW β a ^ 2 * z.2 ^ 2))) := by
    fun_prop
  exact (hf.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable

private lemma msm_Qm_mono {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : MonotoneOn (Qm β) (Ioi 0) := by
  intro a ha b hb hab
  obtain ⟨hQa, hra⟩ := vsh_Qm hβ0 hβ1 ha
  obtain ⟨hQb, hrb⟩ := vsh_Qm hβ0 hβ1 hb
  by_contra h
  have h := not_le.1 h
  have := (Muon.DetEquiv.lem_app_de_scalar_iii (vsh_weightSeq hβ0 hβ1)).2.1 (Set.mem_Ici.2 hQb.le)
    (Set.mem_Ici.2 hQa.le) h
  rw [hra, hrb] at this
  linarith [this, hab]

private lemma msm_DLag_meas (β : ℝ) (ℓ : ℤ) : Measurable (fun q : ℝ × ℝ => DLag β q.1 q.2 ℓ) := by
  unfold DLag
  split_ifs
  · exact msm_DLagNat_meas β _
  · exact (msm_DLagNat_meas β _).comp measurable_swap

private lemma msm_lag_eq {α β : ℝ} {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B) (hc : 0 < c)
    (i : Fin N) (ℓ : ℤ) {m₁ m₂ : ℝ} (h₁ : m₁ ∈ Ioo 0 (gammaOf N B)) (h₂ : m₂ ∈ Ioo 0 (gammaOf N B)) :
    lagMajorant β B (plSpec α c N) i ℓ m₁ m₂ =
      |Wpart β B (plSpec α c N) i m₁| * |Wpart β B (plSpec α c N) i m₂| *
        |DLag β (Qm β m₁) (Qm β m₂) ℓ| := by
  have hγ : 0 < gammaOf N B := h₁.1.trans h₁.2
  rw [vsh_W_eq (α := α) (β := β) hN hB hc i h₁, vsh_W_eq (α := α) (β := β) hN hB hc i h₂]
  unfold lagMajorant
  have hg1 : 0 ≤ gRow B (plSpec α c N) i m₁ := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hg2 : 0 ≤ gRow B (plSpec α c N) i m₂ := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hs : (Real.sqrt (gammaOf N B))⁻¹ * (Real.sqrt (gammaOf N B))⁻¹ = (gammaOf N B)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hγ.le]
  simp only [abs_mul, abs_of_nonneg hg1, abs_of_nonneg hg2, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg (gammaOf N B)))]
  rw [← hs]; ring

private lemma msm_meas {α β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) (ℓ : ℤ)
    (hW : AEStronglyMeasurable (Wpart β B (plSpec α c N) i) (volume.restrict (Ioo 0 (gammaOf N B)))) :
    AEStronglyMeasurable (fun q : ℝ × ℝ => lagMajorant β B (plSpec α c N) i ℓ q.1 q.2)
      (volume.restrict (Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B))) := by
  set J := Ioo 0 (gammaOf N B) with hJ
  have hprod : (volume : Measure (ℝ × ℝ)).restrict (J ×ˢ J) = (volume.restrict J).prod (volume.restrict J) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hQm : AEMeasurable (Qm β) (volume.restrict J) :=
    (aemeasurable_restrict_of_monotoneOn measurableSet_Ioi (msm_Qm_mono hβ0 hβ1)).mono_measure
      (Measure.restrict_mono (fun m hm => hm.1) le_rfl)
  have hQ1 : AEMeasurable (fun p : ℝ × ℝ => Qm β p.1) ((volume.restrict J).prod (volume.restrict J)) := hQm.comp_fst
  have hQ2 : AEMeasurable (fun p : ℝ × ℝ => Qm β p.2) ((volume.restrict J).prod (volume.restrict J)) := hQm.comp_snd
  have hD : AEMeasurable (fun p : ℝ × ℝ => DLag β (Qm β p.1) (Qm β p.2) ℓ) ((volume.restrict J).prod (volume.restrict J)) := by
    have h := (msm_DLag_meas β ℓ).comp_aemeasurable (hQ1.prodMk hQ2)
    exact h
  have hW1 : AEMeasurable (fun p : ℝ × ℝ => Wpart β B (plSpec α c N) i p.1) ((volume.restrict J).prod (volume.restrict J)) := by
    have h := hW.aemeasurable.comp_fst (ν := volume.restrict J)
    exact h
  have hW2 : AEMeasurable (fun p : ℝ × ℝ => Wpart β B (plSpec α c N) i p.2) ((volume.restrict J).prod (volume.restrict J)) := by
    have h := hW.aemeasurable.comp_snd (μ := volume.restrict J)
    exact h
  have hF : AEStronglyMeasurable (fun p : ℝ × ℝ => |Wpart β B (plSpec α c N) i p.1| * |Wpart β B (plSpec α c N) i p.2| *
      |DLag β (Qm β p.1) (Qm β p.2) ℓ|) (volume.restrict (J ×ˢ J)) := by
    rw [hprod]
    exact ((hW1.abs.mul hW2.abs).mul hD.abs).aestronglyMeasurable
  refine hF.congr ?_
  refine (ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)).2 (ae_of_all _ fun p hp => ?_)
  exact (msm_lag_eq (α := α) (β := β) hN hB hc i ℓ hp.1 hp.2).symm

private lemma msm_G_bound {γ C g θ m : ℝ} (hγ : 1 ≤ γ) (hC : 0 ≤ C) (hm0 : 0 < m) (hmγ : m < γ)
    (hg0 : 0 ≤ g) (hg : g ≤ C) (hgB : γ / 2 ≤ m → g ≤ C * (1 - m / γ))
    (hθ : |θ| ≤ C * (1 + m⁻¹ + (γ - m)⁻¹)) : g * |θ| ≤ 3 * C ^ 2 * (1 + 1 / m) := by
  have hγm : 0 < γ - m := by linarith
  have hγ0 : 0 < γ := by linarith
  have hm1 : 0 ≤ 1 / m := by positivity
  rw [one_div] at hm1 ⊢
  by_cases hh : γ / 2 ≤ m
  · have h1 := hgB hh
    have e : 1 - m / γ = (γ - m) / γ := by field_simp
    rw [e] at h1
    have hq : 0 ≤ (γ - m) / γ := by positivity
    calc g * |θ| ≤ (C * ((γ - m) / γ)) * (C * (1 + m⁻¹ + (γ - m)⁻¹)) :=
          mul_le_mul h1 hθ (abs_nonneg _) (by positivity)
      _ = C ^ 2 * (((γ - m) / γ) * (1 + m⁻¹) + 1 / γ) := by
          field_simp
      _ ≤ C ^ 2 * (1 * (1 + m⁻¹) + 1) := by
          have hq1 : (γ - m) / γ ≤ 1 := by rw [div_le_one hγ0]; linarith
          have hg1 : 1 / γ ≤ 1 := by rw [div_le_one hγ0]; exact hγ
          gcongr
      _ ≤ 3 * C ^ 2 * (1 + m⁻¹) := by nlinarith [sq_nonneg C, mul_nonneg (sq_nonneg C) hm1]
  · push_neg at hh
    have hinv : (γ - m)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hγm (by norm_num)]; linarith
    calc g * |θ| ≤ C * (C * (1 + m⁻¹ + (γ - m)⁻¹)) := mul_le_mul hg hθ (abs_nonneg _) hC
      _ ≤ C * (C * (1 + m⁻¹ + 2)) := by gcongr
      _ ≤ 3 * C ^ 2 * (1 + m⁻¹) := by nlinarith [sq_nonneg C, mul_nonneg (sq_nonneg C) hm1]

private lemma msm_pw {α β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) (ℓ : ℤ) (hℓ : 0 ≤ ℓ) (hγ1 : 1 ≤ gammaOf N B) {C K1 μ : ℝ} (hC : 0 ≤ C)
    (hK1 : 0 ≤ K1)
    (hrow : ∀ m ∈ Ioo 0 (gammaOf N B),
      gRow B (plSpec α c N) i m ≤ C ∧
      (gammaOf N B / 2 ≤ m → gRow B (plSpec α c N) i m ≤ C * (1 - m / gammaOf N B)) ∧
      |thetaN β B (plSpec α c N) m| ≤ C * (1 + m⁻¹ + (gammaOf N B - m)⁻¹))
    (hD : ∀ m₁ m₂ : ℝ, 0 < m₁ → 0 < m₂ →
      DLag β (Qm β m₁) (Qm β m₂) ℓ ≤
        K1 * (min m₁ 1) ^ (1 / 4 : ℝ) * (min m₂ 1) ^ (1 / 4 : ℝ) * Real.exp (-μ * |m₁ - m₂ + ℓ|))
    {m₁ m₂ : ℝ} (h₁ : m₁ ∈ Ioo 0 (gammaOf N B)) (h₂ : m₂ ∈ Ioo 0 (gammaOf N B)) :
    lagMajorant β B (plSpec α c N) i ℓ m₁ m₂ ≤
      36 * C ^ 4 * K1 * (gammaOf N B)⁻¹ *
        ((1 + (Ioo (0:ℝ) 1).indicator (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) m₁) *
          (1 + (Ioo (0:ℝ) 1).indicator (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) m₂) *
          Real.exp (-μ * |m₁ - m₂ + ℓ|)) := by
  set γ := gammaOf N B with hγdef
  set s := fun x : ℝ => (Ioo (0:ℝ) 1).indicator (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) x with hs
  have hγ0 : 0 < γ := by linarith
  obtain ⟨hg1, hgB1, hθ1⟩ := hrow m₁ h₁
  obtain ⟨hg2, hgB2, hθ2⟩ := hrow m₂ h₂
  have hgn1 : 0 ≤ gRow B (plSpec α c N) i m₁ := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hgn2 : 0 ≤ gRow B (plSpec α c N) i m₂ := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hG1 := msm_G_bound hγ1 hC h₁.1 h₁.2 hgn1 hg1 hgB1 hθ1
  have hG2 := msm_G_bound hγ1 hC h₂.1 h₂.2 hgn2 hg2 hgB2 hθ2
  have hDn : 0 ≤ DLag β (Qm β m₁) (Qm β m₂) ℓ :=
    vsh_DLag_nonneg hβ0 (vsh_Qm hβ0 hβ1 h₁.1).1.le (vsh_Qm hβ0 hβ1 h₂.1).1.le ℓ
  have hDb := hD m₁ m₂ h₁.1 h₂.1
  have hp1 := msm_s_pw h₁.1
  have hp2 := msm_s_pw h₂.1
  have hs1 : 0 ≤ s m₁ := indicator_nonneg (fun x hx => Real.rpow_nonneg hx.1.le _) _
  have hs2 : 0 ≤ s m₂ := indicator_nonneg (fun x hx => Real.rpow_nonneg hx.1.le _) _
  have hmin1 : 0 ≤ (min m₁ 1) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (le_min h₁.1.le zero_le_one) _
  have hmin2 : 0 ≤ (min m₂ 1) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (le_min h₂.1.le zero_le_one) _
  have hexp := (Real.exp_pos (-μ * |m₁ - m₂ + ℓ|)).le
  have hom : lagMajorant β B (plSpec α c N) i ℓ m₁ m₂ =
      γ⁻¹ * (gRow B (plSpec α c N) i m₁ * |thetaN β B (plSpec α c N) m₁|) *
        (gRow B (plSpec α c N) i m₂ * |thetaN β B (plSpec α c N) m₂|) *
        DLag β (Qm β m₁) (Qm β m₂) ℓ := by
    unfold lagMajorant
    rw [abs_of_nonneg hDn]; ring
  rw [hom]
  have hC4 : 0 ≤ C ^ 4 := by positivity
  have hm1p : 0 < m₁ := h₁.1
  have hm2p : 0 < m₂ := h₂.1
  have hA : 0 ≤ 3 * C ^ 2 * (1 + 1 / m₁) := by positivity
  have hA2 : 0 ≤ 3 * C ^ 2 * (1 + 1 / m₂) := by positivity
  calc γ⁻¹ * (gRow B (plSpec α c N) i m₁ * |thetaN β B (plSpec α c N) m₁|) *
        (gRow B (plSpec α c N) i m₂ * |thetaN β B (plSpec α c N) m₂|) *
        DLag β (Qm β m₁) (Qm β m₂) ℓ
      ≤ γ⁻¹ * (3 * C ^ 2 * (1 + 1 / m₁)) * (3 * C ^ 2 * (1 + 1 / m₂)) *
        (K1 * (min m₁ 1) ^ (1 / 4 : ℝ) * (min m₂ 1) ^ (1 / 4 : ℝ) * Real.exp (-μ * |m₁ - m₂ + ℓ|)) := by
        gcongr
    _ = 9 * C ^ 4 * K1 * γ⁻¹ * (((1 + 1 / m₁) * (min m₁ 1) ^ (1 / 4 : ℝ)) *
          ((1 + 1 / m₂) * (min m₂ 1) ^ (1 / 4 : ℝ))) * Real.exp (-μ * |m₁ - m₂ + ℓ|) := by ring
    _ ≤ 9 * C ^ 4 * K1 * γ⁻¹ * ((2 * (1 + s m₁)) * (2 * (1 + s m₂))) * Real.exp (-μ * |m₁ - m₂ + ℓ|) := by
        gcongr
    _ = _ := by ring

private lemma msm_regA {s : ℝ → ℝ} (hs : Integrable s) (hs4 : ∫ x, s x = 4) (hs0 : ∀ x, 0 ≤ s x)
    (hsm : Measurable s) {γ δ K μ ℓ : ℝ} {f : ℝ × ℝ → ℝ} (hγ : 3 ≤ γ) (hδ0 : 0 < δ) (hδ : δ < 1 / 2)
    (hK : 0 ≤ K) (hμ : 0 < μ)
    (hmeas : AEStronglyMeasurable f (volume.restrict (Ioo 0 γ ×ˢ Ioo 0 γ)))
    (hnn : ∀ m ∈ Ioo 0 γ ×ˢ Ioo 0 γ, 0 ≤ f m)
    (hbd : ∀ m ∈ Ioo 0 γ ×ˢ Ioo 0 γ, f m ≤
      K * γ⁻¹ * ((1 + s m.1) * (1 + s m.2) * Real.exp (-μ * |m.1 - m.2 + ℓ|))) :
    IntegrableOn f (Ioo 0 (δ * γ) ×ˢ Ioo 0 γ) ∧
    ∫ m₁ in Ioo 0 (δ * γ), ∫ m₂ in Ioo 0 γ, f (m₁, m₂) ≤ K * (8 / μ + 16) * (δ + Real.log γ / γ) := by
  have hγ0 : 0 < γ := by linarith
  set I : Set ℝ := Ioo 0 (δ * γ) with hI
  set J : Set ℝ := Ioo 0 γ with hJ
  have hIJ : I ⊆ J := Ioo_subset_Ioo_right (by nlinarith)
  have hIm : MeasurableSet I := measurableSet_Ioo
  have hJm : MeasurableSet J := measurableSet_Ioo
  have hIfin : volume I ≠ ⊤ := by rw [hI, Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hvolI : (volume I).toReal = δ * γ := by
    rw [hI, Real.volume_Ioo, ENNReal.toReal_ofReal (by nlinarith)]; ring
  have hsI : IntegrableOn s I := hs.integrableOn
  have hsJ : IntegrableOn s J := hs.integrableOn
  have hsIle : ∫ x in I, s x ≤ 4 := hs4 ▸ setIntegral_le_integral hs (ae_of_all _ hs0)
  have hsJle : ∫ x in J, s x ≤ 4 := hs4 ▸ setIntegral_le_integral hs (ae_of_all _ hs0)
  have hsI0 : 0 ≤ ∫ x in I, s x := setIntegral_nonneg hIm (fun x _ => hs0 x)
  have hsJ0 : 0 ≤ ∫ x in J, s x := setIntegral_nonneg hJm (fun x _ => hs0 x)
  set h : ℝ → ℝ := fun v => Real.exp (-μ * |v|) with hh
  have hhi : Integrable h := vsh_exp_abs_integrable hμ
  have hhm : Measurable h := by simp only [hh]; fun_prop
  have hh0 : ∀ v, 0 ≤ h v := fun v => (Real.exp_pos _).le
  have hh1 : ∀ v, h v ≤ 1 := fun v => Real.exp_le_one_iff.2 (by nlinarith [abs_nonneg v])
  have hhint : ∫ v, h v = 2 / μ := msm_exp_int hμ
  -- the four terms
  obtain ⟨T1i, T1v⟩ := vsh_strip hhi hhm ℓ hIm hIfin
  obtain ⟨T2i, T2v⟩ := msm_wstrip hIm hsI hsm hhi hhm ℓ
  have hone : IntegrableOn (fun _ : ℝ => (1:ℝ)) I := integrableOn_const hIfin
  obtain ⟨T3i, T3v⟩ := msm_boxmul hIm hJm hone hsJ
  obtain ⟨T4i, T4v⟩ := msm_boxmul hIm hJm hsI hsJ
  set R : Set (ℝ × ℝ) := I ×ˢ J with hR
  have hRm : MeasurableSet R := hIm.prod hJm
  have hRsub : R ⊆ I ×ˢ univ := prod_mono le_rfl (subset_univ _)
  have hRJ : R ⊆ Ioo 0 γ ×ˢ Ioo 0 γ := prod_mono hIJ le_rfl
  set g : ℝ × ℝ → ℝ := fun m => K * γ⁻¹ * (h (m.1 - m.2 + ℓ) + s m.1 * h (m.1 - m.2 + ℓ) +
      1 * s m.2 + s m.1 * s m.2) with hg
  have T1R : IntegrableOn (fun m : ℝ × ℝ => h (m.1 - m.2 + ℓ)) R := T1i.mono_set hRsub
  have T2R : IntegrableOn (fun m : ℝ × ℝ => s m.1 * h (m.1 - m.2 + ℓ)) R := T2i.mono_set hRsub
  have gint : IntegrableOn g R := by
    have := (((T1R.add T2R).add T3i).add T4i).const_mul (K * γ⁻¹)
    exact this
  have hdom := msm_dom (f := f) (g := g) hRm (hmeas.mono_measure (Measure.restrict_mono hRJ le_rfl)) gint (by
    intro m hm
    refine ⟨hnn m (hRJ hm), (hbd m (hRJ hm)).trans ?_⟩
    simp only [hg]
    have e1 := hh1 (m.1 - m.2 + ℓ)
    have e0 := hh0 (m.1 - m.2 + ℓ)
    have a1 := hs0 m.1
    have a2 := hs0 m.2
    have hKγ : 0 ≤ K * γ⁻¹ := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hKγ
    have hexp : Real.exp (-μ * |m.1 - m.2 + ℓ|) = h (m.1 - m.2 + ℓ) := rfl
    rw [hexp]
    nlinarith [mul_nonneg a1 (sub_nonneg.2 e1), mul_nonneg a2 (sub_nonneg.2 e1), mul_nonneg (mul_nonneg a1 a2) (sub_nonneg.2 e1)])
  refine ⟨hdom.1, ?_⟩
  have hfint := hdom.1
  have hfint' : IntegrableOn f (I ×ˢ J) := hfint
  have hiter : ∫ m₁ in I, ∫ m₂ in J, f (m₁, m₂) = ∫ m in R, f m := by
    have := setIntegral_prod f (s := I) (t := J) (μ := volume) (ν := volume)
      (by rw [← Measure.volume_eq_prod]; exact hfint')
    rw [Measure.volume_eq_prod, this]
  rw [hiter]
  refine hdom.2.trans ?_
  -- compute ∫_R g
  have e1 : ∫ m in R, h (m.1 - m.2 + ℓ) ≤ δ * γ * (2 / μ) := by
    have := setIntegral_mono_set (μ := volume) T1i (ae_of_all _ (fun m => hh0 _)) (ae_of_all _ hRsub)
    rw [T1v, hvolI, hhint] at this
    exact this
  have e2 : ∫ m in R, s m.1 * h (m.1 - m.2 + ℓ) ≤ 4 * (2 / μ) := by
    have := setIntegral_mono_set (μ := volume) T2i (ae_of_all _ (fun m => mul_nonneg (hs0 _) (hh0 _))) (ae_of_all _ hRsub)
    rw [T2v, hhint] at this
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right hsIle (by positivity)
  have e3 : ∫ m in R, 1 * s m.2 ≤ δ * γ * 4 := by
    rw [T3v]
    simp only [setIntegral_const, smul_eq_mul, mul_one]
    rw [Measure.real, hvolI]
    exact mul_le_mul_of_nonneg_left hsJle (by positivity)
  have e4 : ∫ m in R, s m.1 * s m.2 ≤ 4 * 4 := by
    rw [T4v]
    exact mul_le_mul hsIle hsJle hsJ0 (by norm_num)
  have T3R : IntegrableOn (fun m : ℝ × ℝ => (1:ℝ) * s m.2) R := T3i
  have T4R : IntegrableOn (fun m : ℝ × ℝ => s m.1 * s m.2) R := T4i
  have hsum : ∫ m in R, g m = K * γ⁻¹ * ((∫ m in R, h (m.1 - m.2 + ℓ)) + (∫ m in R, s m.1 * h (m.1 - m.2 + ℓ)) +
      (∫ m in R, 1 * s m.2) + ∫ m in R, s m.1 * s m.2) := by
    simp only [hg]
    have i12 : IntegrableOn (fun m : ℝ × ℝ => h (m.1 - m.2 + ℓ) + s m.1 * h (m.1 - m.2 + ℓ)) R := T1R.add T2R
    have i123 : IntegrableOn (fun m : ℝ × ℝ => h (m.1 - m.2 + ℓ) + s m.1 * h (m.1 - m.2 + ℓ) + 1 * s m.2) R := i12.add T3R
    rw [integral_const_mul, integral_add i123 T4R, integral_add i12 T3R, integral_add T1R T2R]
  rw [hsum]
  have hlog : 1 ≤ Real.log γ := by
    rw [Real.le_log_iff_exp_le hγ0]
    have := Real.exp_one_lt_d9
    linarith
  have hKγ : 0 ≤ K * γ⁻¹ := by positivity
  calc K * γ⁻¹ * ((∫ m in R, h (m.1 - m.2 + ℓ)) + (∫ m in R, s m.1 * h (m.1 - m.2 + ℓ)) +
      (∫ m in R, 1 * s m.2) + ∫ m in R, s m.1 * s m.2)
      ≤ K * γ⁻¹ * (δ * γ * (2 / μ) + 4 * (2 / μ) + δ * γ * 4 + 4 * 4) := by gcongr
    _ = K * ((2 / μ + 4) * δ + (8 / μ + 16) * γ⁻¹) := by
        field_simp
        ring
    _ ≤ K * (8 / μ + 16) * (δ + Real.log γ / γ) := by
        have h1 : (8 / μ + 16) * γ⁻¹ ≤ (8 / μ + 16) * (Real.log γ / γ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [inv_eq_one_div]
          exact div_le_div_of_nonneg_right hlog hγ0.le
        have h2 : (2 / μ + 4) * δ ≤ (8 / μ + 16) * δ := by
          apply mul_le_mul_of_nonneg_right _ hδ0.le
          have : 0 ≤ 6 / μ + 12 := by positivity
          have e : 8 / μ + 16 = (2 / μ + 4) + (6 / μ + 12) := by ring
          linarith
        nlinarith [mul_nonneg hK (sub_nonneg.2 h1), mul_nonneg hK (sub_nonneg.2 h2)]

private lemma msm_regB {s : ℝ → ℝ} (hs : Integrable s) (hs4 : ∫ x, s x = 4) (hs0 : ∀ x, 0 ≤ s x)
    (hsm : Measurable s) (hs1 : ∀ x, 1 ≤ x → s x = 0) {γ δ K μ ℓ : ℝ} {f : ℝ × ℝ → ℝ}
    (hγ : 3 ≤ γ) (hδ0 : 0 < δ) (hδ : δ < 1 / 2)
    (hK : 0 ≤ K) (hμ : 0 < μ)
    (hmeas : AEStronglyMeasurable f (volume.restrict (Ioo 0 γ ×ˢ Ioo 0 γ)))
    (hnn : ∀ m ∈ Ioo 0 γ ×ˢ Ioo 0 γ, 0 ≤ f m)
    (hbd : ∀ m ∈ Ioo 0 γ ×ˢ Ioo 0 γ, f m ≤
      K * γ⁻¹ * ((1 + s m.1) * (1 + s m.2) * Real.exp (-μ * |m.1 - m.2 + ℓ|))) :
    IntegrableOn f (Ioo 0 γ ×ˢ Ioo ((1 - δ) * γ) γ) ∧
    ∫ m₁ in Ioo 0 γ, ∫ m₂ in Ioo ((1 - δ) * γ) γ, f (m₁, m₂) ≤ K * (2 / μ + 4) * δ := by
  have hγ0 : 0 < γ := by linarith
  set I : Set ℝ := Ioo ((1 - δ) * γ) γ with hI
  set J : Set ℝ := Ioo 0 γ with hJ
  have hIJ : I ⊆ J := Ioo_subset_Ioo_left (by nlinarith)
  have hIm : MeasurableSet I := measurableSet_Ioo
  have hJm : MeasurableSet J := measurableSet_Ioo
  have hIfin : volume I ≠ ⊤ := by rw [hI, Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hvolI : (volume I).toReal = δ * γ := by
    rw [hI, Real.volume_Ioo, ENNReal.toReal_ofReal (by nlinarith)]; ring
  have hsJ : IntegrableOn s J := hs.integrableOn
  have hsJle : ∫ x in J, s x ≤ 4 := hs4 ▸ setIntegral_le_integral hs (ae_of_all _ hs0)
  have hsJ0 : 0 ≤ ∫ x in J, s x := setIntegral_nonneg hJm (fun x _ => hs0 x)
  set h : ℝ → ℝ := fun v => Real.exp (-μ * |v|) with hh
  have hhi : Integrable h := vsh_exp_abs_integrable hμ
  have hhm : Measurable h := by simp only [hh]; fun_prop
  have hh0 : ∀ v, 0 ≤ h v := fun v => (Real.exp_pos _).le
  have hh1 : ∀ v, h v ≤ 1 := fun v => Real.exp_le_one_iff.2 (by nlinarith [abs_nonneg v])
  have hhint : ∫ v, h v = 2 / μ := msm_exp_int hμ
  obtain ⟨T1i, T1v⟩ := msm_wstrip_swap hIm hhi hhm ℓ hIfin
  have hone : IntegrableOn (fun _ : ℝ => (1:ℝ)) I := integrableOn_const hIfin
  obtain ⟨T2i, T2v⟩ := msm_boxmul hJm hIm hsJ hone
  set R : Set (ℝ × ℝ) := J ×ˢ I with hR
  have hRm : MeasurableSet R := hJm.prod hIm
  have hRsub : R ⊆ univ ×ˢ I := prod_mono (subset_univ _) le_rfl
  have hRJ : R ⊆ Ioo 0 γ ×ˢ Ioo 0 γ := prod_mono le_rfl hIJ
  set g : ℝ × ℝ → ℝ := fun m => K * γ⁻¹ * (h (m.1 - m.2 + ℓ) + s m.1 * 1) with hg
  have T1R : IntegrableOn (fun m : ℝ × ℝ => h (m.1 - m.2 + ℓ)) R := T1i.mono_set hRsub
  have gint : IntegrableOn g R := (T1R.add T2i).const_mul (K * γ⁻¹)
  have hdom := msm_dom (f := f) (g := g) hRm (hmeas.mono_measure (Measure.restrict_mono hRJ le_rfl)) gint (by
    intro m hm
    refine ⟨hnn m (hRJ hm), (hbd m (hRJ hm)).trans ?_⟩
    simp only [hg]
    have e1 := hh1 (m.1 - m.2 + ℓ)
    have e0 := hh0 (m.1 - m.2 + ℓ)
    have a1 := hs0 m.1
    have hm2 : s m.2 = 0 := hs1 _ (by
      have := hm.2.1
      nlinarith)
    have hKγ : 0 ≤ K * γ⁻¹ := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hKγ
    have hexp : Real.exp (-μ * |m.1 - m.2 + ℓ|) = h (m.1 - m.2 + ℓ) := rfl
    rw [hexp, hm2]
    nlinarith [mul_nonneg a1 (sub_nonneg.2 e1)])
  refine ⟨hdom.1, ?_⟩
  have hfint' : IntegrableOn f (J ×ˢ I) := hdom.1
  have hiter : ∫ m₁ in J, ∫ m₂ in I, f (m₁, m₂) = ∫ m in R, f m := by
    have := setIntegral_prod f (s := J) (t := I) (μ := volume) (ν := volume)
      (by rw [← Measure.volume_eq_prod]; exact hfint')
    rw [Measure.volume_eq_prod, this]
  rw [hiter]
  refine hdom.2.trans ?_
  have e1 : ∫ m in R, h (m.1 - m.2 + ℓ) ≤ δ * γ * (2 / μ) := by
    have := setIntegral_mono_set (μ := volume) T1i (ae_of_all _ (fun m => hh0 _)) (ae_of_all _ hRsub)
    rw [T1v, hvolI, hhint] at this
    exact this
  have e2 : ∫ m in R, s m.1 * 1 ≤ 4 * (δ * γ) := by
    rw [T2v]
    simp only [setIntegral_const, smul_eq_mul, mul_one]
    rw [Measure.real, hvolI]
    exact mul_le_mul_of_nonneg_right hsJle (by positivity)
  have hsum : ∫ m in R, g m = K * γ⁻¹ * ((∫ m in R, h (m.1 - m.2 + ℓ)) + ∫ m in R, s m.1 * 1) := by
    simp only [hg]
    rw [integral_const_mul, integral_add T1R T2i]
  rw [hsum]
  have hKγ : 0 ≤ K * γ⁻¹ := by positivity
  calc K * γ⁻¹ * ((∫ m in R, h (m.1 - m.2 + ℓ)) + ∫ m in R, s m.1 * 1)
      ≤ K * γ⁻¹ * (δ * γ * (2 / μ) + 4 * (δ * γ)) := by gcongr
    _ = K * (2 / μ + 4) * δ := by
        field_simp

private lemma msm_regC {s : ℝ → ℝ} (hs : Integrable s) (hs4 : ∫ x, s x = 4) (hs0 : ∀ x, 0 ≤ s x)
    (hsm : Measurable s) {γ δ K μ ℓ : ℝ} {f : ℝ × ℝ → ℝ}
    (hγ : 4 ≤ γ) (hδ0 : 0 < δ) (hK : 0 ≤ K) (hμ : 0 < μ)
    (hmeas : AEStronglyMeasurable f (volume.restrict (Ioo 0 γ ×ˢ Ioo 0 γ)))
    (hnn : ∀ m ∈ Ioo 0 γ ×ˢ Ioo 0 γ, 0 ≤ f m)
    (hbd : ∀ m ∈ Ioo 0 γ ×ˢ Ioo 0 γ, f m ≤
      K * γ⁻¹ * ((1 + s m.1) * (1 + s m.2) * Real.exp (-μ * |m.1 - m.2 + ℓ|))) :
    IntegrableOn f {q : ℝ × ℝ | q ∈ Ioo 0 γ ×ˢ Ioo 0 γ ∧ δ * γ ≤ |q.1 - q.2 + ℓ|} ∧
    ∫ q in {q : ℝ × ℝ | q ∈ Ioo 0 γ ×ˢ Ioo 0 γ ∧ δ * γ ≤ |q.1 - q.2 + ℓ|}, f q ≤
      4 * K * γ * Real.exp (-μ * (δ * γ)) := by
  have hγ0 : 0 < γ := by linarith
  set J : Set ℝ := Ioo 0 γ with hJ
  have hJm : MeasurableSet J := measurableSet_Ioo
  have hvolJ : (volume J).toReal = γ := by
    rw [hJ, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]; ring
  have hJfin : volume J ≠ ⊤ := by rw [hJ, Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hsJ : IntegrableOn s J := hs.integrableOn
  have hsJle : ∫ x in J, s x ≤ 4 := hs4 ▸ setIntegral_le_integral hs (ae_of_all _ hs0)
  have hsJ0 : 0 ≤ ∫ x in J, s x := setIntegral_nonneg hJm (fun x _ => hs0 x)
  have hc1 : IntegrableOn (fun _ : ℝ => (1:ℝ)) J := integrableOn_const hJfin
  have hoJ : IntegrableOn (fun x : ℝ => 1 + s x) J := hc1.add hsJ
  have hoJv : ∫ x in J, (1 + s x) ≤ 2 * γ := by
    rw [integral_add hc1 hsJ]
    simp only [setIntegral_const, smul_eq_mul, mul_one]
    rw [Measure.real, hvolJ]
    linarith
  have hoJ0 : 0 ≤ ∫ x in J, (1 + s x) := setIntegral_nonneg hJm (fun x _ => by linarith [hs0 x])
  obtain ⟨Ti, Tv⟩ := msm_boxmul hJm hJm hoJ hoJ
  set S : Set (ℝ × ℝ) := {q : ℝ × ℝ | q ∈ J ×ˢ J ∧ δ * γ ≤ |q.1 - q.2 + ℓ|} with hS
  have hSm : MeasurableSet S := by
    have : S = (J ×ˢ J) ∩ {q : ℝ × ℝ | δ * γ ≤ |q.1 - q.2 + ℓ|} := rfl
    rw [this]
    exact (hJm.prod hJm).inter (measurableSet_le measurable_const (by fun_prop))
  have hSsub : S ⊆ J ×ˢ J := fun q hq => hq.1
  set E0 : ℝ := Real.exp (-μ * (δ * γ)) with hE0
  set g : ℝ × ℝ → ℝ := fun m => K * γ⁻¹ * E0 * ((1 + s m.1) * (1 + s m.2)) with hg
  have gI : IntegrableOn g (J ×ˢ J) := Ti.const_mul (K * γ⁻¹ * E0)
  have gint : IntegrableOn g S := gI.mono_set hSsub
  have hdom := msm_dom (f := f) (g := g) hSm (hmeas.mono_measure (Measure.restrict_mono hSsub le_rfl)) gint (by
    intro m hm
    refine ⟨hnn m (hSsub hm), (hbd m (hSsub hm)).trans ?_⟩
    simp only [hg]
    have hexp : Real.exp (-μ * |m.1 - m.2 + ℓ|) ≤ E0 := by
      rw [hE0]; apply Real.exp_le_exp.2
      nlinarith [hm.2]
    have a1 := hs0 m.1
    have a2 := hs0 m.2
    have hKγ : 0 ≤ K * γ⁻¹ := by positivity
    have hp : 0 ≤ (1 + s m.1) * (1 + s m.2) := by positivity
    calc K * γ⁻¹ * ((1 + s m.1) * (1 + s m.2) * Real.exp (-μ * |m.1 - m.2 + ℓ|))
        = K * γ⁻¹ * (((1 + s m.1) * (1 + s m.2)) * Real.exp (-μ * |m.1 - m.2 + ℓ|)) := rfl
      _ ≤ K * γ⁻¹ * (((1 + s m.1) * (1 + s m.2)) * E0) := by gcongr
      _ = _ := by ring)
  refine ⟨hdom.1, hdom.2.trans ?_⟩
  have hbig : ∫ m in S, g m ≤ ∫ m in J ×ˢ J, g m :=
    setIntegral_mono_set gI (ae_of_all _ (fun m => by
      simp only [hg]
      have a1 := hs0 m.1
      have a2 := hs0 m.2
      have : 0 ≤ K * γ⁻¹ * E0 := by positivity
      positivity)) (ae_of_all _ hSsub)
  refine hbig.trans ?_
  have : ∫ m in J ×ˢ J, g m = K * γ⁻¹ * E0 * ((∫ x in J, (1 + s x)) * ∫ x in J, (1 + s x)) := by
    simp only [hg]
    rw [integral_const_mul, Tv]
  rw [this]
  have hKγ : 0 ≤ K * γ⁻¹ * E0 := by positivity
  calc K * γ⁻¹ * E0 * ((∫ x in J, (1 + s x)) * ∫ x in J, (1 + s x))
      ≤ K * γ⁻¹ * E0 * ((2 * γ) * (2 * γ)) := by gcongr
    _ = 4 * K * γ * E0 := by
        field_simp
        ring

private lemma msm_W_meas {α β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {N B : ℕ} {c : ℝ} (hN : 0 < N)
    (hB : 0 < B) (hc : 0 < c) (i : Fin N) :
    AEStronglyMeasurable (Wpart β B (plSpec α c N) i) (volume.restrict (Ioo 0 (gammaOf N B))) := by
  set J := Ioo 0 (gammaOf N B) with hJ
  have hpos : ∀ j, 0 < plSpec α c N j := fun j => by
    unfold plSpec; exact mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)
  have hbij := def_app_pl_participation_bij (plSpec α c N) hB hN hpos
  have hΛc : ContinuousOn (partLam B (plSpec α c N)) J := hbij.2.2.2.continuousOn
  have hΛm : AEMeasurable (partLam B (plSpec α c N)) (volume.restrict J) :=
    hΛc.aemeasurable measurableSet_Ioo
  have hdΛ : AEMeasurable (deriv (partLam B (plSpec α c N))) (volume.restrict J) :=
    (measurable_deriv _).aemeasurable
  have hQm : AEMeasurable (Qm β) (volume.restrict J) :=
    (aemeasurable_restrict_of_monotoneOn measurableSet_Ioi (msm_Qm_mono hβ0 hβ1)).mono_measure
      (Measure.restrict_mono (fun m hm => hm.1) le_rfl)
  have hE : AEMeasurable (Efun β) (volume.restrict J) := by
    unfold Efun
    exact hQm.mul ((measurable_deriv (Muon.DetEquiv.rW (emaW β))).comp_aemeasurable hQm)
  have hθ : AEMeasurable (thetaN β B (plSpec α c N)) (volume.restrict J) := by
    unfold thetaN
    have h1 : AEMeasurable (fun m : ℝ => 1 / Efun β m) (volume.restrict J) := aemeasurable_const.div hE
    have h2 : AEMeasurable (fun m : ℝ => deriv (partLam B (plSpec α c N)) m / partLam B (plSpec α c N) m)
        (volume.restrict J) := hdΛ.div hΛm
    have h3 : AEMeasurable (fun m : ℝ => 1 / (gammaOf N B - m)) (volume.restrict J) := by
      exact (measurable_const.div (measurable_const.sub measurable_id)).aemeasurable
    have h4 : AEMeasurable (fun m : ℝ => 1 / m) (volume.restrict J) := by
      exact (measurable_const.div measurable_id).aemeasurable
    exact ((h1.add h2).add h3).sub h4
  unfold Wpart
  have hy : AEMeasurable (fun m : ℝ => plSpec α c N i * partLam B (plSpec α c N) m) (volume.restrict J) :=
    aemeasurable_const.mul hΛm
  refine AEMeasurable.aestronglyMeasurable ?_
  refine ((hy.sqrt.div ((measurable_id.sqrt.aemeasurable).mul (aemeasurable_const.add hy))).mul
    (((measurable_const.sub (measurable_id.div_const _)).sqrt).aemeasurable)).mul hθ

/-- Shell mass of the majorant (task L-G.7b; proof step of `thm:app-pl-volatility`(i), l.2238-2241;
snapshot cr-2026-10-23; CORRECTIONS row 15). Three bounds: the mass on `m₁ < δγ` is `O(δ + γ⁻¹ log γ)`
(the source treats `1 < m₁ < δγ` and `m₁ ≤ 1` separately, the latter by the factor `min(m₁,1)^{1/2}` of `𝖣_ℓ`;
merged here); the mass on `m₂ > (1-δ)γ` is `O(δ)` (the source's l.2239 says `m₁ > (1-δ)γ`, a slip for `m₂`,
CORRECTIONS row 15); and the off-shell mass over `{|m₁ - m₂ + ℓ| ≥ δγ}` is
`≤ C γ e^{-|log β| δ γ/2}` (the exponential factor of `lem:app-pl-localization`(i), l.2240-2241). -/
theorem majorant_shell_mass {α β : ℝ} (x₀ τ₀ : ℝ) (hx₀ : x₀ ∈ Ioc 0 1) (hτ₀ : 0 < τ₀) :
    ∃ C : ℝ, ∀ (N B : ℕ → ℕ) (c : ℕ → ℝ), assum_app_pl_regime α β N B c →
      ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ᶠ n in atTop, ∀ i : Fin (N n), x₀ ≤ rowFrac i →
        ∀ ℓ : ℤ, τ₀ * gammaOf (N n) (B n) ≤ ℓ →
          IntegrableOn (fun q : ℝ × ℝ => lagMajorant β (B n) (plSpec α (c n) (N n)) i ℓ q.1 q.2)
            (Ioo 0 (δ * gammaOf (N n) (B n)) ×ˢ Ioo 0 (gammaOf (N n) (B n))) ∧
          (∫ m₁ in Ioo 0 (δ * gammaOf (N n) (B n)), ∫ m₂ in Ioo 0 (gammaOf (N n) (B n)),
              lagMajorant β (B n) (plSpec α (c n) (N n)) i ℓ m₁ m₂) ≤
            C * (δ + Real.log (gammaOf (N n) (B n)) / gammaOf (N n) (B n)) ∧
          IntegrableOn (fun q : ℝ × ℝ => lagMajorant β (B n) (plSpec α (c n) (N n)) i ℓ q.1 q.2)
            (Ioo 0 (gammaOf (N n) (B n)) ×ˢ
              Ioo ((1 - δ) * gammaOf (N n) (B n)) (gammaOf (N n) (B n))) ∧
          (∫ m₁ in Ioo 0 (gammaOf (N n) (B n)),
              ∫ m₂ in Ioo ((1 - δ) * gammaOf (N n) (B n)) (gammaOf (N n) (B n)),
                lagMajorant β (B n) (plSpec α (c n) (N n)) i ℓ m₁ m₂) ≤ C * δ ∧
          IntegrableOn (fun q : ℝ × ℝ => lagMajorant β (B n) (plSpec α (c n) (N n)) i ℓ q.1 q.2)
            {q : ℝ × ℝ | q ∈ Ioo 0 (gammaOf (N n) (B n)) ×ˢ Ioo 0 (gammaOf (N n) (B n)) ∧
              δ * gammaOf (N n) (B n) ≤ |q.1 - q.2 + (ℓ : ℝ)|} ∧
          (∫ q in {q : ℝ × ℝ | q ∈ Ioo 0 (gammaOf (N n) (B n)) ×ˢ Ioo 0 (gammaOf (N n) (B n)) ∧
              δ * gammaOf (N n) (B n) ≤ |q.1 - q.2 + (ℓ : ℝ)|},
              lagMajorant β (B n) (plSpec α (c n) (N n)) i ℓ q.1 q.2) ≤
            C * gammaOf (N n) (B n) *
              Real.exp (-|Real.log β| * (δ * gammaOf (N n) (B n)) / 2) := by
  by_cases hreg : 0 < α ∧ 0 < β ∧ β < 1
  swap
  · refine ⟨0, fun N B c R => ?_⟩
    exact absurd ⟨R.hα, R.hβ0, R.hβ1⟩ hreg
  obtain ⟨hα, hβ0, hβ1⟩ := hreg
  obtain ⟨Crow, κ, hκ, hrowall⟩ := row_bounds_x0 (α := α) (β := β) x₀ hx₀
  obtain ⟨K1, μ, hK1, hμ, hμdef, hDall⟩ := msm_D_bound hβ0 hβ1
  obtain ⟨hsI, hs4, hs0, hsm⟩ := msm_s_facts
  have hs1 : ∀ x : ℝ, 1 ≤ x → (Ioo (0:ℝ) 1).indicator (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) x = 0 :=
    fun x hx => indicator_of_notMem (by simp [hx]) _
  set Cc : ℝ := |Crow| with hCc
  have hCc0 : 0 ≤ Cc := abs_nonneg _
  set Kc : ℝ := 36 * Cc ^ 4 * K1 with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  refine ⟨Kc * (8 / μ + 16) + Kc * (2 / μ + 4) + 4 * Kc, fun N B c R δ hδ0 hδ => ?_⟩
  filter_upwards [hrowall N B c R, R.hγ.eventually_ge_atTop 4] with n hrow hγ4
  intro i hix ℓ hℓ
  have hγ4' : (4:ℝ) ≤ gammaOf (N n) (B n) := hγ4
  have hN := R.hNpos n
  have hB := R.hBpos n
  have hc := R.hcpos n
  set γ := gammaOf (N n) (B n) with hγdef
  have hγ0 : 0 < γ := by linarith [hγ4']
  have hℓ0 : 0 ≤ ℓ := by
    have : (0:ℝ) ≤ (ℓ : ℝ) := le_trans (mul_nonneg hτ₀.le hγ0.le) hℓ
    exact_mod_cast this
  have hrow' : ∀ m ∈ Ioo 0 γ,
      gRow (B n) (plSpec α (c n) (N n)) i m ≤ Cc ∧
      (γ / 2 ≤ m → gRow (B n) (plSpec α (c n) (N n)) i m ≤ Cc * (1 - m / γ)) ∧
      |thetaN β (B n) (plSpec α (c n) (N n)) m| ≤ Cc * (1 + m⁻¹ + (γ - m)⁻¹) := by
    intro m hm
    obtain ⟨-, hg, hgB, hθ⟩ := hrow i hix m hm
    have hm0 := hm.1
    have hγm : 0 < γ - m := by linarith [hm.2]
    refine ⟨hg.trans (le_abs_self _), fun hh => ?_, ?_⟩
    · refine (hgB hh).trans ?_
      have : 0 ≤ 1 - m / γ := by
        rw [sub_nonneg, div_le_one hγ0]; exact hm.2.le
      exact mul_le_mul_of_nonneg_right (le_abs_self _) this
    · refine hθ.trans ?_
      have : 0 ≤ 1 + m⁻¹ + (γ - m)⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_right (le_abs_self _) this
  have hmeas := msm_meas (α := α) hβ0 hβ1 hN hB hc i ℓ (msm_W_meas (α := α) hβ0 hβ1 hN hB hc i)
  have hnn : ∀ m ∈ Ioo 0 γ ×ˢ Ioo 0 γ,
      0 ≤ (fun q : ℝ × ℝ => lagMajorant β (B n) (plSpec α (c n) (N n)) i ℓ q.1 q.2) m := by
    intro m hm
    show 0 ≤ lagMajorant β (B n) (plSpec α (c n) (N n)) i ℓ m.1 m.2
    rw [msm_lag_eq (α := α) (β := β) hN hB hc i ℓ hm.1 hm.2]
    positivity
  have hbd : ∀ m ∈ Ioo 0 γ ×ˢ Ioo 0 γ,
      (fun q : ℝ × ℝ => lagMajorant β (B n) (plSpec α (c n) (N n)) i ℓ q.1 q.2) m ≤
        Kc * γ⁻¹ * ((1 + (Ioo (0:ℝ) 1).indicator (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) m.1) *
          (1 + (Ioo (0:ℝ) 1).indicator (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) m.2) *
          Real.exp (-μ * |m.1 - m.2 + ℓ|)) := by
    intro m hm
    exact msm_pw (α := α) hβ0 hβ1 hN hB hc i ℓ hℓ0 (by linarith [hγ4']) hCc0 hK1 hrow'
      (fun m₁ m₂ h1 h2 => hDall ℓ hℓ0 m₁ m₂ h1 h2) hm.1 hm.2
  have hA := msm_regA hsI hs4 hs0 hsm (by linarith [hγ4'] : 3 ≤ γ) hδ0 hδ hKc0 hμ hmeas hnn hbd
  have hB' := msm_regB hsI hs4 hs0 hsm hs1 (by linarith [hγ4'] : 3 ≤ γ) hδ0 hδ hKc0 hμ hmeas hnn hbd
  have hC := msm_regC hsI hs4 hs0 hsm hγ4' hδ0 hKc0 hμ hmeas hnn hbd (δ := δ)
  have hlog : 0 ≤ Real.log γ / γ := div_nonneg (Real.log_nonneg (by linarith [hγ4'])) hγ0.le
  have hX : 0 ≤ δ + Real.log γ / γ := by linarith
  refine ⟨hA.1, ?_, hB'.1, ?_, hC.1, ?_⟩
  · refine hA.2.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hX
    have : 0 ≤ Kc * (2 / μ + 4) := by positivity
    have : 0 ≤ 4 * Kc := by positivity
    linarith
  · refine hB'.2.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hδ0.le
    have : 0 ≤ Kc * (8 / μ + 16) := by positivity
    have : 0 ≤ 4 * Kc := by positivity
    linarith
  · refine hC.2.trans ?_
    have e : -|Real.log β| * (δ * γ) / 2 = -μ * (δ * γ) := by rw [hμdef]; ring
    rw [e]
    have hE := (Real.exp_pos (-μ * (δ * γ))).le
    have hKa : 0 ≤ Kc * (8 / μ + 16) := by positivity
    have hKb : 0 ≤ Kc * (2 / μ + 4) := by positivity
    have : 4 * Kc * γ ≤ (Kc * (8 / μ + 16) + Kc * (2 / μ + 4) + 4 * Kc) * γ :=
      mul_le_mul_of_nonneg_right (by linarith) hγ0.le
    nlinarith [mul_le_mul_of_nonneg_right this hE]

/-! ## Large lags -/

/-- Stein's identity consequence: for `s ≥ 0`,
`𝔼 g⁴/(1+sg²) = 3 𝔼 g²/(1+sg²) - 2s 𝔼 g⁴/(1+sg²)² ≤ 3 𝔼 g²/(1+sg²)`
(task L-G.7b; proof step of `thm:app-pl-volatility`(i), l.2244-2248, via `Muon.Foundations.gaussian_stein`;
snapshot cr-2026-10-23). -/
theorem stein_quartic_bound {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun g : ℝ => g ^ 4 / (1 + s * g ^ 2)) (gaussianReal 0 1) ∧
    Integrable (fun g : ℝ => g ^ 2 / (1 + s * g ^ 2)) (gaussianReal 0 1) ∧
    Integrable (fun g : ℝ => g ^ 4 / (1 + s * g ^ 2) ^ 2) (gaussianReal 0 1) ∧
    (∫ g : ℝ, g ^ 4 / (1 + s * g ^ 2) ∂(gaussianReal 0 1) =
      3 * ∫ g : ℝ, g ^ 2 / (1 + s * g ^ 2) ∂(gaussianReal 0 1) -
        2 * s * ∫ g : ℝ, g ^ 4 / (1 + s * g ^ 2) ^ 2 ∂(gaussianReal 0 1)) ∧
    ∫ g : ℝ, g ^ 4 / (1 + s * g ^ 2) ∂(gaussianReal 0 1) ≤
      3 * ∫ g : ℝ, g ^ 2 / (1 + s * g ^ 2) ∂(gaussianReal 0 1) := by
  have hD : ∀ g : ℝ, 1 ≤ 1 + s * g ^ 2 := fun g => by nlinarith [mul_nonneg hs (sq_nonneg g)]
  have hDp : ∀ g : ℝ, 0 < 1 + s * g ^ 2 := fun g => by linarith [hD g]
  have hP : ∀ n : ℕ, Integrable (fun g : ℝ => g ^ n) (gaussianReal 0 1) :=
    Muon.Foundations.gaussian_integrable_pow
  have hcont : ∀ f : ℝ → ℝ, Continuous f → ∀ k : ℕ, Continuous fun g : ℝ => f g / (1 + s * g ^ 2) ^ k :=
    fun f hf k => hf.div (by fun_prop) (fun g => (pow_pos (hDp g) k).ne')
  have hle : ∀ (n k : ℕ) (g : ℝ), g ^ n / (1 + s * g ^ 2) ^ k ≤ g ^ n ∨ ¬ Even n := by
    intro n k g
    by_cases hn : Even n
    · left
      have h0 : 0 ≤ g ^ n := hn.pow_nonneg g
      exact div_le_self h0 (one_le_pow₀ (hD g))
    · right; exact hn
  have hint : ∀ (n k : ℕ), Even n → Integrable (fun g : ℝ => g ^ n / (1 + s * g ^ 2) ^ k) (gaussianReal 0 1) := by
    intro n k hn
    refine (hP n).mono' (hcont (fun g => g ^ n) (by fun_prop) k).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => ?_)
    have h0 : 0 ≤ g ^ n := hn.pow_nonneg g
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg h0 (pow_pos (hDp g) k).le)]
    exact div_le_self h0 (one_le_pow₀ (hD g))
  have i4 : Integrable (fun g : ℝ => g ^ 4 / (1 + s * g ^ 2)) (gaussianReal 0 1) := by
    simpa using hint 4 1 (by decide)
  have i2 : Integrable (fun g : ℝ => g ^ 2 / (1 + s * g ^ 2)) (gaussianReal 0 1) := by
    simpa using hint 2 1 (by decide)
  have i4' : Integrable (fun g : ℝ => g ^ 4 / (1 + s * g ^ 2) ^ 2) (gaussianReal 0 1) :=
    hint 4 2 (by decide)
  have hφ : ∀ g : ℝ, HasDerivAt (fun g : ℝ => g ^ 3 / (1 + s * g ^ 2))
      (3 * (g ^ 2 / (1 + s * g ^ 2)) - 2 * s * (g ^ 4 / (1 + s * g ^ 2) ^ 2)) g := by
    intro g
    have h1 : HasDerivAt (fun g : ℝ => g ^ 3) (3 * g ^ 2) g := by
      simpa using hasDerivAt_pow 3 g
    have h2 : HasDerivAt (fun g : ℝ => 1 + s * g ^ 2) (s * (2 * g)) g := by
      simpa using ((hasDerivAt_pow 2 g).const_mul s).const_add 1
    convert h1.div h2 (hDp g).ne' using 1
    have := (hDp g).ne'
    field_simp
  have hdφ : ∀ g : ℝ, deriv (fun g : ℝ => g ^ 3 / (1 + s * g ^ 2)) g =
      3 * (g ^ 2 / (1 + s * g ^ 2)) - 2 * s * (g ^ 4 / (1 + s * g ^ 2) ^ 2) :=
    fun g => (hφ g).deriv
  have hCD : ContDiff ℝ 1 (fun g : ℝ => g ^ 3 / (1 + s * g ^ 2)) := by
    refine contDiff_one_iff_deriv.mpr ⟨fun g => (hφ g).differentiableAt, ?_⟩
    have : deriv (fun g : ℝ => g ^ 3 / (1 + s * g ^ 2)) = fun g =>
        3 * (g ^ 2 / (1 + s * g ^ 2)) - 2 * s * (g ^ 4 / (1 + s * g ^ 2) ^ 2) := funext hdφ
    rw [this]
    have a := hcont (fun g => g ^ 2) (by fun_prop) 1
    have b := hcont (fun g => g ^ 4) (by fun_prop) 2
    simp only [pow_one] at a
    exact (a.const_mul 3).sub (b.const_mul _)
  have hb1 : ∃ C : ℝ, ∃ k : ℕ, ∀ x : ℝ, |x ^ 3 / (1 + s * x ^ 2)| ≤ C * (1 + |x| ^ k) := by
    refine ⟨1, 3, fun x => ?_⟩
    rw [abs_div, abs_of_pos (hDp x), abs_pow]
    have : |x| ^ 3 / (1 + s * x ^ 2) ≤ |x| ^ 3 := div_le_self (by positivity) (hD x)
    nlinarith [pow_nonneg (abs_nonneg x) 3]
  have hb2 : ∃ C : ℝ, ∃ k : ℕ, ∀ x : ℝ, |deriv (fun g : ℝ => g ^ 3 / (1 + s * g ^ 2)) x| ≤
      C * (1 + |x| ^ k) := by
    refine ⟨3 + 2 * s, 4, fun x => ?_⟩
    rw [hdφ]
    have e1 : 0 ≤ x ^ 2 / (1 + s * x ^ 2) := div_nonneg (sq_nonneg x) (hDp x).le
    have e2 : 0 ≤ x ^ 4 / (1 + s * x ^ 2) ^ 2 := div_nonneg (by positivity) (by positivity)
    have f1 : x ^ 2 / (1 + s * x ^ 2) ≤ x ^ 2 := div_le_self (sq_nonneg x) (hD x)
    have f2 : x ^ 4 / (1 + s * x ^ 2) ^ 2 ≤ x ^ 4 :=
      div_le_self (by positivity) (one_le_pow₀ (hD x))
    have g4 : |x| ^ 4 = x ^ 4 := by
      rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
    rw [g4]
    have g2 : x ^ 2 ≤ 1 + x ^ 4 := by nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg x]
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg hs (sq_nonneg (x ^ 2)), mul_nonneg hs (sq_nonneg x)]
  have hS := Muon.Foundations.gaussian_stein _ hCD hb1 hb2
  have hlhs : ∫ x : ℝ, x * (x ^ 3 / (1 + s * x ^ 2)) ∂(gaussianReal 0 1) =
      ∫ g : ℝ, g ^ 4 / (1 + s * g ^ 2) ∂(gaussianReal 0 1) := by
    congr 1; funext x; ring
  have hid : ∫ g : ℝ, g ^ 4 / (1 + s * g ^ 2) ∂(gaussianReal 0 1) =
      3 * ∫ g : ℝ, g ^ 2 / (1 + s * g ^ 2) ∂(gaussianReal 0 1) -
        2 * s * ∫ g : ℝ, g ^ 4 / (1 + s * g ^ 2) ^ 2 ∂(gaussianReal 0 1) := by
    rw [← hlhs, hS]
    simp only [hdφ]
    rw [integral_sub (i2.const_mul 3) (i4'.const_mul _), integral_const_mul, integral_const_mul]
  refine ⟨i4, i2, i4', hid, ?_⟩
  rw [hid]
  have : 0 ≤ ∫ g : ℝ, g ^ 4 / (1 + s * g ^ 2) ^ 2 ∂(gaussianReal 0 1) :=
    integral_nonneg fun g => div_nonneg (by positivity) (by positivity)
  nlinarith [mul_nonneg hs this]

private lemma llk_rint {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ} (hq : 0 < q) :
    (∀ a, Integrable (fun g : ℝ => emaW β a ^ 2 * q * g ^ 2 / (1 + emaW β a ^ 2 * q * g ^ 2))
      (gaussianReal 0 1)) ∧
    Summable (fun a => ∫ g : ℝ, emaW β a ^ 2 * q * g ^ 2 / (1 + emaW β a ^ 2 * q * g ^ 2)
      ∂(gaussianReal 0 1)) ∧
    Muon.DetEquiv.rW (emaW β) q = ∑' a, ∫ g : ℝ, emaW β a ^ 2 * q * g ^ 2 /
      (1 + emaW β a ^ 2 * q * g ^ 2) ∂(gaussianReal 0 1) := by
  have hX : ∀ a (g : ℝ), 0 ≤ emaW β a ^ 2 * q * g ^ 2 := fun a g => by positivity
  have h := vsh_int_summ hβ0 hβ1 (c := q)
    (f := fun a g => emaW β a ^ 2 * q * g ^ 2 / (1 + emaW β a ^ 2 * q * g ^ 2))
    (fun a => by
      refine Continuous.div (by fun_prop) (by fun_prop) ?_
      intro g; have := hX a g; positivity)
    (fun a g => div_nonneg (hX a g) (by have := hX a g; positivity))
    (fun a g => by
      have := hX a g
      refine (div_le_self this (by linarith)).trans_eq ?_
      ring)
  exact ⟨h.1, h.2, (Muon.DetEquiv.lem_app_de_scalar_iii (vsh_weightSeq hβ0 hβ1)).1 q hq.le⟩

private lemma llk_r_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ} (hq : 0 < q) :
    Muon.DetEquiv.rW (emaW β) q ≤ q * ∑' a, emaW β a ^ 2 := by
  obtain ⟨hi, hs, he⟩ := llk_rint hβ0 hβ1 hq
  rw [he, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun a => ?_) hs ((vsh_w2_summable hβ0 hβ1).mul_left q)
  have hi2 := Muon.Foundations.gaussian_integrable_pow 2
  calc _ ≤ ∫ g : ℝ, q * emaW β a ^ 2 * g ^ 2 ∂(gaussianReal 0 1) := by
        refine integral_mono (hi a) ((hi2.const_mul (q * emaW β a ^ 2)).congr
          (Filter.Eventually.of_forall fun g => by simp)) (fun g => ?_)
        have : 0 ≤ emaW β a ^ 2 * q * g ^ 2 := by positivity
        refine (div_le_self this (by linarith)).trans_eq ?_
        ring
    _ = q * emaW β a ^ 2 := by
        rw [integral_const_mul, Muon.Foundations.gaussian_moment_two, mul_one]

private lemma llk_r_ratio {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q q' : ℝ} (hq : 0 < q)
    (hqq : q ≤ q') :
    q * Muon.DetEquiv.rW (emaW β) q' ≤ q' * Muon.DetEquiv.rW (emaW β) q := by
  have hq' : 0 < q' := lt_of_lt_of_le hq hqq
  obtain ⟨hi, hs, he⟩ := llk_rint hβ0 hβ1 hq
  obtain ⟨hi', hs', he'⟩ := llk_rint hβ0 hβ1 hq'
  rw [he, he', ← tsum_mul_left, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun a => ?_) (hs'.mul_left q) (hs.mul_left q')
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_mono ((hi' a).const_mul q) ((hi a).const_mul q') (fun g => ?_)
  have hu : 0 ≤ emaW β a ^ 2 * g ^ 2 := by positivity
  show q * (emaW β a ^ 2 * q' * g ^ 2 / (1 + emaW β a ^ 2 * q' * g ^ 2)) ≤
    q' * (emaW β a ^ 2 * q * g ^ 2 / (1 + emaW β a ^ 2 * q * g ^ 2))
  have h1 : 0 < 1 + emaW β a ^ 2 * q' * g ^ 2 := by positivity
  have h2 : 0 < 1 + emaW β a ^ 2 * q * g ^ 2 := by positivity
  rw [← mul_div_assoc, ← mul_div_assoc, div_le_div_iff₀ h1 h2]
  nlinarith [mul_nonneg (mul_nonneg hu hq.le) (mul_nonneg hu (sub_nonneg.2 hqq)),
    mul_nonneg hu (mul_nonneg hq.le (sub_nonneg.2 hqq)), mul_nonneg hq.le hq'.le,
    mul_nonneg (mul_nonneg hq.le hq'.le) (mul_nonneg hu hu)]

private lemma llk_Qratio {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m m' : ℝ} (hm : 0 < m)
    (hmm : m ≤ m') : Qm β m * m' ≤ Qm β m' * m := by
  have hm' : 0 < m' := lt_of_lt_of_le hm hmm
  obtain ⟨hQ, hr⟩ := vsh_Qm hβ0 hβ1 hm
  obtain ⟨hQ', hr'⟩ := vsh_Qm hβ0 hβ1 hm'
  have hmono := msm_Qm_mono hβ0 hβ1 hm hm' hmm
  have := llk_r_ratio hβ0 hβ1 hQ hmono
  rw [hr, hr'] at this
  linarith

private lemma llk_K1 {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m g : ℝ} (hm : 0 < m) (hmg : m ≤ g)
    (hg : 1 ≤ g) : Qm β m ≤ Qm β g * min m 1 := by
  have hg0 : 0 < g := by linarith
  by_cases h1 : 1 ≤ m
  · rw [min_eq_right h1, mul_one]
    exact msm_Qm_mono hβ0 hβ1 hm hg0 hmg
  · push_neg at h1
    rw [min_eq_left h1.le]
    have h := llk_Qratio hβ0 hβ1 hm h1.le
    have hQ1 : Qm β 1 ≤ Qm β g := msm_Qm_mono hβ0 hβ1 (by norm_num : (0:ℝ) < 1) hg0 hg
    have hQm : 0 < Qm β m := (vsh_Qm hβ0 hβ1 hm).1
    nlinarith [mul_le_mul_of_nonneg_right hQ1 hm.le]

private lemma llk_M {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q₁ q₂ : ℝ} (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (ℓ : ℕ) :
    0 ≤ MLagNat β q₁ q₂ ℓ ∧
      MLagNat β q₁ q₂ ℓ ≤ 3 * (1 - β) ^ 2 * β ^ (2 * ℓ) * q₂ * Muon.DetEquiv.rW (emaW β) q₁ := by
  obtain ⟨hi, hs, he⟩ := llk_rint hβ0 hβ1 h₁
  have hw : ∀ a, 0 < emaW β a := vsh_emaW_pos hβ0 hβ1
  have hwle : ∀ a, emaW β a ≤ 1 - β := fun a => by
    unfold emaW
    have : β ^ a ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
    nlinarith [sub_pos.2 hβ1]
  let c : ℕ → ℝ := fun a => β ^ (2 * ℓ) * q₂ * emaW β a ^ 2
  let s : ℕ → ℝ := fun a => emaW β a ^ 2 * q₁
  have hs0 : ∀ a, 0 ≤ s a := fun a => by dsimp [s]; have := hw a; positivity
  have hc0 : ∀ a, 0 ≤ c a := fun a => by dsimp [c]; have := hw a; positivity
  have hden : ∀ a (g : ℝ), 0 < 1 + s a * g ^ 2 := fun a g => by
    have := hs0 a; positivity
  let f : ℕ → ℝ → ℝ := fun a g => β ^ (2 * ℓ) * q₁ * q₂ * emaW β a ^ 4 * g ^ 4 /
      ((1 + q₁ * emaW β a ^ 2 * g ^ 2) * (1 + β ^ (2 * ℓ) * q₂ * emaW β a ^ 2 * g ^ 2))
  let G : ℕ → ℝ → ℝ := fun a g => c a * (s a * (g ^ 4 / (1 + s a * g ^ 2)))
  have hfG : ∀ a g, 0 ≤ f a g ∧ f a g ≤ G a g := by
    intro a g
    have hY : 0 ≤ β ^ (2 * ℓ) * q₂ * emaW β a ^ 2 * g ^ 2 := by have := hw a; positivity
    have hq : (1 + q₁ * emaW β a ^ 2 * g ^ 2) = 1 + s a * g ^ 2 := by dsimp [s]; ring
    have hA : 0 < 1 + q₁ * emaW β a ^ 2 * g ^ 2 := by rw [hq]; exact hden a g
    have hB : 0 < 1 + β ^ (2 * ℓ) * q₂ * emaW β a ^ 2 * g ^ 2 := by positivity
    constructor
    · dsimp only [f]; have := hw a; positivity
    · have e : f a g = G a g / (1 + β ^ (2 * ℓ) * q₂ * emaW β a ^ 2 * g ^ 2) := by
        dsimp only [f, G, c, s]
        have h3 : 0 < 1 + emaW β a ^ 2 * q₁ * g ^ 2 := by
          have := hden a g; dsimp only [s] at this; exact this
        have h4 : (1 + q₁ * emaW β a ^ 2 * g ^ 2) = 1 + emaW β a ^ 2 * q₁ * g ^ 2 := by ring
        rw [h4] at hA ⊢
        field_simp
      rw [e]
      refine div_le_self ?_ (by linarith)
      dsimp only [G]
      have := hc0 a; have := hs0 a; have := hden a g
      positivity
  have hGint : ∀ a, Integrable (G a) (gaussianReal 0 1) := fun a =>
    ((stein_quartic_bound (hs0 a)).1.const_mul (s a)).const_mul (c a)
  have hfm : ∀ a, Continuous (f a) := fun a => by
    refine Continuous.div (by fun_prop) (by fun_prop) ?_
    intro g
    have hq : (1 + q₁ * emaW β a ^ 2 * g ^ 2) = 1 + s a * g ^ 2 := by dsimp [s]; ring
    have hB : 0 < 1 + β ^ (2 * ℓ) * q₂ * emaW β a ^ 2 * g ^ 2 := by
      have := hw a; positivity
    have := hden a g
    rw [← hq] at this
    exact (mul_pos this hB).ne'
  have hfi : ∀ a, Integrable (f a) (gaussianReal 0 1) := fun a =>
    (hGint a).mono' (hfm a).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hfG a g).1]; exact (hfG a g).2)
  have hint_le : ∀ a, ∫ g, f a g ∂(gaussianReal 0 1) ≤
      (3 * (1 - β) ^ 2 * β ^ (2 * ℓ) * q₂) *
        ∫ g : ℝ, emaW β a ^ 2 * q₁ * g ^ 2 / (1 + emaW β a ^ 2 * q₁ * g ^ 2) ∂(gaussianReal 0 1) := by
    intro a
    obtain ⟨-, -, -, -, hst⟩ := stein_quartic_bound (hs0 a)
    have h1 : ∫ g, f a g ∂(gaussianReal 0 1) ≤ ∫ g, G a g ∂(gaussianReal 0 1) :=
      integral_mono (hfi a) (hGint a) (fun g => (hfG a g).2)
    have h2 : ∫ g, G a g ∂(gaussianReal 0 1) = c a * (s a *
        ∫ g : ℝ, g ^ 4 / (1 + s a * g ^ 2) ∂(gaussianReal 0 1)) := by
      dsimp only [G]
      rw [integral_const_mul, integral_const_mul]
    have h3 : ∫ g : ℝ, emaW β a ^ 2 * q₁ * g ^ 2 / (1 + emaW β a ^ 2 * q₁ * g ^ 2) ∂(gaussianReal 0 1) =
        s a * ∫ g : ℝ, g ^ 2 / (1 + s a * g ^ 2) ∂(gaussianReal 0 1) := by
      rw [← integral_const_mul]
      congr 1; funext g; dsimp only [s]; rw [mul_div_assoc]
    have hIa : 0 ≤ ∫ g : ℝ, emaW β a ^ 2 * q₁ * g ^ 2 / (1 + emaW β a ^ 2 * q₁ * g ^ 2) ∂(gaussianReal 0 1) :=
      integral_nonneg fun g => by have := hs0 a; have := hden a g; dsimp only [s] at *; positivity
    have h4 : c a ≤ β ^ (2 * ℓ) * q₂ * (1 - β) ^ 2 := by
      dsimp only [c]
      have := mul_le_mul (hwle a) (hwle a) (hw a).le (sub_nonneg.2 hβ1.le)
      have h5 : emaW β a ^ 2 ≤ (1 - β) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left h5 (by positivity)
    rw [h2] at h1
    refine h1.trans ?_
    calc c a * (s a * ∫ g : ℝ, g ^ 4 / (1 + s a * g ^ 2) ∂(gaussianReal 0 1))
        ≤ c a * (s a * (3 * ∫ g : ℝ, g ^ 2 / (1 + s a * g ^ 2) ∂(gaussianReal 0 1))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hst (hs0 a)) (hc0 a)
      _ = 3 * c a * (s a * ∫ g : ℝ, g ^ 2 / (1 + s a * g ^ 2) ∂(gaussianReal 0 1)) := by ring
      _ ≤ 3 * (β ^ (2 * ℓ) * q₂ * (1 - β) ^ 2) * (s a * ∫ g : ℝ, g ^ 2 / (1 + s a * g ^ 2) ∂(gaussianReal 0 1)) := by
          refine mul_le_mul_of_nonneg_right (by linarith) ?_
          rw [← h3]; exact hIa
      _ = _ := by rw [h3]; ring
  have hsum : Summable (fun a => ∫ g, f a g ∂(gaussianReal 0 1)) :=
    Summable.of_nonneg_of_le (fun a => integral_nonneg (fun g => (hfG a g).1)) hint_le
      (hs.mul_left _)
  have hMeq : MLagNat β q₁ q₂ ℓ = ∑' a, ∫ g, f a g ∂(gaussianReal 0 1) := rfl
  refine ⟨?_, ?_⟩
  · rw [hMeq]; exact tsum_nonneg fun a => integral_nonneg fun g => (hfG a g).1
  · rw [hMeq, he, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hint_le hsum (hs.mul_left _)

private lemma llk_D {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q₁ q₂ : ℝ} (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (ℓ : ℕ) :
    0 ≤ DLagNat β q₁ q₂ ℓ ∧
      DLagNat β q₁ q₂ ℓ ≤ β ^ ℓ * Real.sqrt q₂ / Real.sqrt q₁ * Muon.DetEquiv.rW (emaW β) q₁ := by
  obtain ⟨hi, hs, he⟩ := llk_rint hβ0 hβ1 h₁
  have hw : ∀ a, 0 < emaW β a := vsh_emaW_pos hβ0 hβ1
  have hu0 : 0 < Real.sqrt q₁ := Real.sqrt_pos.2 h₁
  have hv0 : 0 < Real.sqrt q₂ := Real.sqrt_pos.2 h₂
  have hsq : Real.sqrt (q₁ * q₂) = Real.sqrt q₁ * Real.sqrt q₂ := Real.sqrt_mul h₁.le _
  have hq1 : q₁ = Real.sqrt q₁ ^ 2 := (Real.sq_sqrt h₁.le).symm
  generalize Real.sqrt q₁ = u at hu0 hsq hq1 ⊢
  generalize Real.sqrt q₂ = v at hv0 hsq ⊢
  let f : ℕ → ℝ → ℝ := fun a g => β ^ ℓ * Real.sqrt (q₁ * q₂) * emaW β a ^ 2 * g ^ 2 /
      ((1 + q₁ * emaW β a ^ 2 * g ^ 2) * (1 + β ^ (2 * ℓ) * q₂ * emaW β a ^ 2 * g ^ 2))
  have hA : ∀ a (g : ℝ), 0 < 1 + q₁ * emaW β a ^ 2 * g ^ 2 := fun a g => by positivity
  have hB : ∀ a (g : ℝ), 0 < 1 + β ^ (2 * ℓ) * q₂ * emaW β a ^ 2 * g ^ 2 := fun a g => by positivity
  have hnum : ∀ a (g : ℝ), 0 ≤ β ^ ℓ * Real.sqrt (q₁ * q₂) * emaW β a ^ 2 * g ^ 2 := fun a g => by
    positivity
  have hf := vsh_int_summ hβ0 hβ1 (c := β ^ ℓ * Real.sqrt (q₁ * q₂)) (f := f)
    (fun a => by
      refine Continuous.div (by fun_prop) (by fun_prop) ?_
      intro g; exact (mul_pos (hA a g) (hB a g)).ne')
    (fun a g => div_nonneg (hnum a g) (mul_pos (hA a g) (hB a g)).le)
    (fun a g => by
      have h1 : 1 ≤ (1 + q₁ * emaW β a ^ 2 * g ^ 2) * (1 + β ^ (2 * ℓ) * q₂ * emaW β a ^ 2 * g ^ 2) := by
        have := hA a g; have := hB a g
        have h3 : 0 ≤ q₁ * emaW β a ^ 2 * g ^ 2 := by positivity
        have h4 : 0 ≤ β ^ (2 * ℓ) * q₂ * emaW β a ^ 2 * g ^ 2 := by positivity
        nlinarith [mul_nonneg h3 h4]
      refine (div_le_self (hnum a g) h1).trans_eq ?_
      ring)
  let H : ℕ → ℝ → ℝ := fun a g => (β ^ ℓ * v / u) *
    (emaW β a ^ 2 * q₁ * g ^ 2 / (1 + emaW β a ^ 2 * q₁ * g ^ 2))
  have hfH : ∀ a g, f a g ≤ H a g := by
    intro a g
    have h4 : (1 + q₁ * emaW β a ^ 2 * g ^ 2) = 1 + emaW β a ^ 2 * q₁ * g ^ 2 := by ring
    have e : f a g = H a g / (1 + β ^ (2 * ℓ) * q₂ * emaW β a ^ 2 * g ^ 2) := by
      dsimp only [f, H]
      rw [hsq, h4]
      have := hA a g
      rw [h4] at this
      have := hB a g
      field_simp
      rw [hq1]
      ring
    rw [e]
    refine div_le_self ?_ (by have : 0 ≤ β ^ (2 * ℓ) * q₂ * emaW β a ^ 2 * g ^ 2 := by positivity
                              linarith)
    dsimp only [H]
    have := hA a g
    rw [show (1 + q₁ * emaW β a ^ 2 * g ^ 2) = 1 + emaW β a ^ 2 * q₁ * g ^ 2 by ring] at this
    have := hw a
    positivity
  have hint_le : ∀ a, ∫ g, f a g ∂(gaussianReal 0 1) ≤
      (β ^ ℓ * v / u) *
        ∫ g : ℝ, emaW β a ^ 2 * q₁ * g ^ 2 / (1 + emaW β a ^ 2 * q₁ * g ^ 2) ∂(gaussianReal 0 1) := by
    intro a
    rw [← integral_const_mul]
    exact integral_mono (hf.1 a) ((hi a).const_mul _) (hfH a)
  have hDeq : DLagNat β q₁ q₂ ℓ = ∑' a, ∫ g, f a g ∂(gaussianReal 0 1) := rfl
  refine ⟨?_, ?_⟩
  · rw [hDeq]
    exact tsum_nonneg fun a => integral_nonneg fun g =>
      div_nonneg (hnum a g) (mul_pos (hA a g) (hB a g)).le
  · rw [hDeq, he, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hint_le hf.2 (hs.mul_left _)

private lemma llk_K2 {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C2 : ℝ, 0 < C2 ∧ ∀ m : ℝ, 0 < m → m / Real.sqrt (Qm β m) ≤ C2 * Real.sqrt (min m 1) := by
  obtain ⟨Cl, hCl⟩ := lem_app_pl_weights_iii_logQ hβ0 hβ1
  have hlam : 0 < |Real.log β| := abs_pos.2 (Real.log_neg hβ0 hβ1).ne
  set lam := |Real.log β| with hlamdef
  set S := ∑' a, emaW β a ^ 2 with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun a => sq_nonneg _
  refine ⟨Real.sqrt S + Real.exp (Cl / 2) / lam + 1, by positivity, fun m hm => ?_⟩
  obtain ⟨hQ, hr⟩ := vsh_Qm hβ0 hβ1 hm
  set q := Qm β m with hqdef
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.2 hQ
  have hE1 : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
  have hE2 : 0 ≤ Real.exp (Cl / 2) / lam := by positivity
  by_cases h1 : 1 ≤ m
  · rw [min_eq_right h1, Real.sqrt_one, mul_one]
    have hL := (abs_le.1 (hCl m h1)).1
    have hsqe : Real.sqrt q = Real.exp (Real.log q / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hQ]; ring_nf
    have hexp : Real.exp (lam * m - Cl / 2) ≤ Real.sqrt q := by
      rw [hsqe]; apply Real.exp_le_exp.2; linarith
    have hm1 : m ≤ Real.exp (lam * m) / lam := by
      rw [le_div_iff₀ hlam]
      nlinarith [Real.add_one_le_exp (lam * m)]
    rw [div_le_iff₀ hsq]
    have hk : Real.exp (Cl / 2) / lam * Real.exp (lam * m - Cl / 2) = Real.exp (lam * m) / lam := by
      rw [div_mul_eq_mul_div, ← Real.exp_add]; congr 2; ring
    have hk2 : Real.exp (Cl / 2) / lam * Real.exp (lam * m - Cl / 2) ≤
        Real.exp (Cl / 2) / lam * Real.sqrt q := mul_le_mul_of_nonneg_left hexp hE2
    nlinarith [mul_nonneg hE1 hsq.le]
  · push_neg at h1
    rw [min_eq_left h1.le]
    have hrS := llk_r_le hβ0 hβ1 hQ
    rw [hr] at hrS
    have hle : m / Real.sqrt q ≤ Real.sqrt S * Real.sqrt m := by
      rw [← Real.sqrt_mul hS0]
      apply Real.le_sqrt_of_sq_le
      rw [div_pow, Real.sq_sqrt hQ.le, div_le_iff₀ hQ]
      nlinarith
    have hsm : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
    nlinarith [mul_nonneg hsm hE2, hsm]

private lemma llk_T {α : ℝ} {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B) (hc : 0 < c)
    {m₁ m₂ : ℝ} (h₁ : m₁ ∈ Ioo 0 (gammaOf N B)) (h₂ : m₂ ∈ Ioo 0 (gammaOf N B)) :
    0 ≤ TNpart B (plSpec α c N) m₁ m₂ ∧ TNpart B (plSpec α c N) m₁ m₂ ≤ gammaOf N B := by
  have hB' : (0:ℝ) < B := by exact_mod_cast hB
  unfold TNpart
  constructor
  · refine mul_nonneg (inv_nonneg.2 hB'.le) (Finset.sum_nonneg fun j _ => ?_)
    exact mul_nonneg (vsh_f_mem (α := α) hN hB hc j h₁).1.le (vsh_f_mem (α := α) hN hB hc j h₂).1.le
  · have hsum : ∑ j : Fin N, partF B (plSpec α c N) j m₁ * partF B (plSpec α c N) j m₂ ≤ N := by
      calc _ ≤ ∑ j : Fin N, (1:ℝ) := Finset.sum_le_sum fun j _ => by
            have a1 := vsh_f_mem (α := α) hN hB hc j h₁
            have a2 := vsh_f_mem (α := α) hN hB hc j h₂
            nlinarith [a1.1, a1.2, a2.1, a2.2]
        _ = N := by simp
    calc _ ≤ (B : ℝ)⁻¹ * N := mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hB'.le)
      _ = gammaOf N B := by unfold gammaOf; ring

private lemma llk_exists {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C₀ C : ℝ, ∀ {α : ℝ} {N B : ℕ} {c : ℝ}, 0 < N → 0 < B → 0 < c → 1 ≤ gammaOf N B →
      ∀ ℓ : ℕ, gammaOf N B + C₀ ≤ (ℓ : ℝ) →
        ∀ m₁ ∈ Ioo 0 (gammaOf N B), ∀ m₂ ∈ Ioo 0 (gammaOf N B),
          1 - deltaN β B (plSpec α c N) (ℓ : ℤ) m₁ m₂ ≤
              C * (β ^ ℓ) ^ 2 * Qm β (gammaOf N B) ∧
          C * (β ^ ℓ) ^ 2 * Qm β (gammaOf N B) ≤ 1 / 2 ∧
          DLag β (Qm β m₁) (Qm β m₂) (ℓ : ℤ) ≤
            C * β ^ ℓ * Real.sqrt (Qm β (gammaOf N B)) *
              Real.sqrt (min m₁ 1) * Real.sqrt (min m₂ 1) := by
  obtain ⟨Cl, hCl⟩ := lem_app_pl_weights_iii_logQ hβ0 hβ1
  obtain ⟨C2, hC2, hK2⟩ := llk_K2 hβ0 hβ1
  have hlam : 0 < |Real.log β| := abs_pos.2 (Real.log_neg hβ0 hβ1).ne
  set lam := |Real.log β| with hlamdef
  have hlog : Real.log β = -lam := by
    rw [hlamdef, abs_of_neg (Real.log_neg hβ0 hβ1)]; ring
  set S := ∑' a, emaW β a ^ 2 with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun a => sq_nonneg _
  have hw0 : 0 ≤ (1 - β) ^ 2 := sq_nonneg _
  set C := 6 * (1 - β) ^ 2 + S + C2 with hCdef
  have hC0 : 0 ≤ C := by positivity
  refine ⟨max 0 ((Cl + Real.log (2 * C + 1)) / (2 * lam)), C, ?_⟩
  intro α N B c hN hB hc hγ ℓ hℓ m₁ hm₁ m₂ hm₂
  set γ := gammaOf N B with hγdef
  have hγ0 : 0 < γ := by linarith
  have hQg : 0 < Qm β γ := (vsh_Qm hβ0 hβ1 hγ0).1
  set Qg := Qm β γ with hQgdef
  obtain ⟨hq₁, hr₁⟩ := vsh_Qm hβ0 hβ1 hm₁.1
  obtain ⟨hq₂, hr₂⟩ := vsh_Qm hβ0 hβ1 hm₂.1
  set q₁ := Qm β m₁ with hq₁def
  set q₂ := Qm β m₂ with hq₂def
  have ha2 : β ^ (2 * ℓ) = (β ^ ℓ) ^ 2 := by rw [← pow_mul, mul_comm]
  have ha0 : 0 < β ^ ℓ := pow_pos hβ0 ℓ
  set a := β ^ ℓ with hadef
  have hMLag : MLag β q₁ q₂ (ℓ : ℤ) = MLagNat β q₁ q₂ ℓ := by simp [MLag]
  have hDLag : DLag β q₁ q₂ (ℓ : ℤ) = DLagNat β q₁ q₂ ℓ := by simp [DLag]
  obtain ⟨hM0, hMb⟩ := llk_M hβ0 hβ1 hq₁ hq₂ ℓ
  obtain ⟨hD0, hDb⟩ := llk_D hβ0 hβ1 hq₁ hq₂ ℓ
  rw [hr₁, ha2] at hMb
  rw [hr₁] at hDb
  obtain ⟨hT0, hTγ⟩ := llk_T (α := α) hN hB hc hm₁ hm₂
  set T := TNpart B (plSpec α c N) m₁ m₂ with hTdef
  set M := MLagNat β q₁ q₂ ℓ with hMdef
  set D := DLagNat β q₁ q₂ ℓ with hDdef
  have hK0 : q₂ * γ ≤ Qg * m₂ := llk_Qratio hβ0 hβ1 hm₂.1 hm₂.2.le
  have hK1 : q₂ ≤ Qg * min m₂ 1 := llk_K1 hβ0 hβ1 hm₂.1 hm₂.2.le hγ
  have hrq : m₁ ≤ q₁ * S := by
    have := llk_r_le hβ0 hβ1 hq₁; rw [hr₁] at this; exact this
  have hm12 : 0 < m₁ * m₂ := mul_pos hm₁.1 hm₂.1
  set k := 3 * (1 - β) ^ 2 * a ^ 2 with hk
  have hk0 : 0 ≤ k := by positivity
  have hMb' : M ≤ k * q₂ * m₁ := by rw [hk]; linarith [hMb]
  have hq2m : q₂ ≤ Qg * m₂ := by nlinarith
  have hx : T * M / (m₁ * m₂) ≤ k * Qg := by
    rw [div_le_iff₀ hm12]
    calc T * M ≤ γ * (k * q₂ * m₁) := mul_le_mul hTγ hMb' hM0 hγ0.le
      _ = k * m₁ * (q₂ * γ) := by ring
      _ ≤ k * m₁ * (Qg * m₂) := mul_le_mul_of_nonneg_left hK0 (by have := hm₁.1; positivity)
      _ = k * Qg * (m₁ * m₂) := by ring
  have hy : M / γ ≤ k * Qg := by
    rw [div_le_iff₀ hγ0]
    calc M ≤ k * q₂ * m₁ := hMb'
      _ ≤ k * q₂ * γ := mul_le_mul_of_nonneg_left hm₁.2.le (by positivity)
      _ = k * (q₂ * γ) := by ring
      _ ≤ k * (Qg * m₂) := mul_le_mul_of_nonneg_left hK0 hk0
      _ ≤ k * (Qg * γ) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm₂.2.le hQg.le) hk0
      _ = k * Qg * γ := by ring
  have hDE : D ≤ a * Real.sqrt q₂ / Real.sqrt q₁ * m₁ := hDb
  have hE2 : (a * Real.sqrt q₂ / Real.sqrt q₁ * m₁) ^ 2 = a ^ 2 * q₂ * (m₁ * (m₁ / q₁)) := by
    have e1 := Real.sq_sqrt hq₁.le
    have e2 := Real.sq_sqrt hq₂.le
    calc (a * Real.sqrt q₂ / Real.sqrt q₁ * m₁) ^ 2
        = a ^ 2 * (Real.sqrt q₂) ^ 2 / (Real.sqrt q₁) ^ 2 * m₁ ^ 2 := by ring
      _ = _ := by rw [e1, e2]; field_simp
  have hD2 : D ^ 2 ≤ a ^ 2 * q₂ * (m₁ * (m₁ / q₁)) :=
    hE2 ▸ pow_le_pow_left₀ hD0 hDE 2
  have hρ : m₁ / q₁ ≤ S := by rw [div_le_iff₀ hq₁]; linarith
  have hz : T * D ^ 2 / (γ * m₁ * m₂) ≤ S * a ^ 2 * Qg := by
    have hpos : 0 < γ * m₁ * m₂ := by have := hm₁.1; have := hm₂.1; positivity
    rw [div_le_iff₀ hpos]
    have h1 : T * D ^ 2 ≤ γ * (a ^ 2 * q₂ * (m₁ * (m₁ / q₁))) :=
      mul_le_mul hTγ hD2 (sq_nonneg _) hγ0.le
    have h2 : a ^ 2 * q₂ * (m₁ * (m₁ / q₁)) ≤ a ^ 2 * (Qg * m₂) * (m₁ * S) := by
      have hm1 := hm₁.1
      have hm2 := hm₂.1
      refine mul_le_mul (mul_le_mul_of_nonneg_left hq2m (by positivity))
        (mul_le_mul_of_nonneg_left hρ hm1.le) (mul_nonneg hm1.le (div_nonneg hm1.le hq₁.le))
        (mul_nonneg (by positivity) (mul_nonneg hQg.le hm2.le))
    calc T * D ^ 2 ≤ _ := h1
      _ ≤ γ * (a ^ 2 * (Qg * m₂) * (m₁ * S)) := mul_le_mul_of_nonneg_left h2 hγ0.le
      _ = S * a ^ 2 * Qg * (γ * m₁ * m₂) := by ring
  have hx0 : 0 ≤ T * M / (m₁ * m₂) := div_nonneg (mul_nonneg hT0 hM0) hm12.le
  have hy0 : 0 ≤ M / γ := div_nonneg hM0 hγ0.le
  have hz0 : 0 ≤ T * D ^ 2 / (γ * m₁ * m₂) :=
    div_nonneg (mul_nonneg hT0 (sq_nonneg _)) (by have := hm₁.1; have := hm₂.1; positivity)
  have ha2Q : 0 ≤ a ^ 2 * Qg := by positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold deltaN
    rw [hMLag, hDLag]
    have hxy := mul_nonneg hx0 hy0
    have hCe : C * a ^ 2 * Qg = (6 * (1 - β) ^ 2 + S) * (a ^ 2 * Qg) + C2 * (a ^ 2 * Qg) := by
      rw [hCdef]; ring
    have hk2 : k * Qg = 3 * (1 - β) ^ 2 * (a ^ 2 * Qg) := by rw [hk]; ring
    have hzz : S * a ^ 2 * Qg = S * (a ^ 2 * Qg) := by ring
    have := mul_nonneg hC2.le ha2Q
    linarith
  · have hL := (abs_le.1 (hCl γ hγ)).2
    have hQle : Qg ≤ Real.exp (2 * lam * γ + Cl) := by
      rw [← Real.exp_log hQg]
      exact Real.exp_le_exp.2 (by linarith)
    have haeq : a ^ 2 = Real.exp (2 * ℓ * Real.log β) := by
      rw [← Real.exp_log (by positivity : 0 < a ^ 2), Real.log_pow, hadef, Real.log_pow]
      push_cast; ring_nf
    have hC0le : (Cl + Real.log (2 * C + 1)) / (2 * lam) ≤
        max 0 ((Cl + Real.log (2 * C + 1)) / (2 * lam)) := le_max_right _ _
    have hC0' : Cl + Real.log (2 * C + 1) ≤ 2 * lam *
        max 0 ((Cl + Real.log (2 * C + 1)) / (2 * lam)) := by
      have := mul_le_mul_of_nonneg_left hC0le (by positivity : 0 ≤ 2 * lam)
      rwa [mul_div_cancel₀ _ (by positivity : (2 * lam) ≠ 0)] at this
    have hexp : a ^ 2 * Qg ≤ Real.exp (-Real.log (2 * C + 1)) := by
      calc a ^ 2 * Qg ≤ Real.exp (2 * ℓ * Real.log β) * Real.exp (2 * lam * γ + Cl) := by
            rw [haeq]; exact mul_le_mul_of_nonneg_left hQle (Real.exp_pos _).le
        _ = Real.exp (2 * ℓ * Real.log β + (2 * lam * γ + Cl)) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (-Real.log (2 * C + 1)) := by
            refine Real.exp_le_exp.2 ?_
            have hm := mul_le_mul_of_nonneg_left hℓ (by positivity : 0 ≤ 2 * lam)
            rw [hlog]
            linarith
    rw [Real.exp_neg, Real.exp_log (by positivity)] at hexp
    calc C * a ^ 2 * Qg = C * (a ^ 2 * Qg) := by ring
      _ ≤ C * (2 * C + 1)⁻¹ := mul_le_mul_of_nonneg_left hexp hC0
      _ ≤ 1 / 2 := by
        rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
        linarith
  · rw [hDLag]
    have h1 := hK2 m₁ hm₁.1
    rw [← hq₁def] at h1
    have h2 : Real.sqrt q₂ ≤ Real.sqrt Qg * Real.sqrt (min m₂ 1) := by
      rw [← Real.sqrt_mul hQg.le]; exact Real.sqrt_le_sqrt hK1
    have hs1 : 0 < Real.sqrt q₁ := Real.sqrt_pos.2 hq₁
    have e : a * Real.sqrt q₂ / Real.sqrt q₁ * m₁ = a * Real.sqrt q₂ * (m₁ / Real.sqrt q₁) := by ring
    have hs2 : 0 ≤ Real.sqrt q₂ := Real.sqrt_nonneg _
    have hs3 : 0 ≤ Real.sqrt (min m₁ 1) := Real.sqrt_nonneg _
    have hs4 : 0 ≤ Real.sqrt (min m₂ 1) := Real.sqrt_nonneg _
    have hs5 : 0 ≤ Real.sqrt Qg := Real.sqrt_nonneg _
    have hm1s : 0 ≤ m₁ / Real.sqrt q₁ := div_nonneg hm₁.1.le hs1.le
    have hCC : C2 ≤ C := by rw [hCdef]; linarith
    calc D ≤ a * Real.sqrt q₂ / Real.sqrt q₁ * m₁ := hDE
      _ = a * Real.sqrt q₂ * (m₁ / Real.sqrt q₁) := e
      _ ≤ a * (Real.sqrt Qg * Real.sqrt (min m₂ 1)) * (C2 * Real.sqrt (min m₁ 1)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h2 ha0.le) h1 hm1s
            (mul_nonneg ha0.le (mul_nonneg hs5 hs4))
      _ ≤ a * (Real.sqrt Qg * Real.sqrt (min m₂ 1)) * (C * Real.sqrt (min m₁ 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCC hs3)
            (mul_nonneg ha0.le (mul_nonneg hs5 hs4))
      _ = _ := by ring

/-- For `ℓ ≥ γ + C₀`, with `a = β^ℓ`: `1 - Δ^N_ℓ ≤ C a² Q_γ ≤ 1/2` and
`𝖣_ℓ ≤ C a √Q_γ min(m₁,1)^{1/2} min(m₂,1)^{1/2}` (task L-G.7b; proof step of
`thm:app-pl-volatility`(i), l.2249-2253; snapshot cr-2026-10-23). -/
theorem large_lag_kernel_bounds {α β : ℝ} :
    ∃ C₀ C : ℝ, ∀ (N B : ℕ → ℕ) (c : ℕ → ℝ), assum_app_pl_regime α β N B c →
      ∀ᶠ n in atTop, ∀ ℓ : ℕ, gammaOf (N n) (B n) + C₀ ≤ (ℓ : ℝ) →
        ∀ m₁ ∈ Ioo 0 (gammaOf (N n) (B n)), ∀ m₂ ∈ Ioo 0 (gammaOf (N n) (B n)),
          1 - deltaN β (B n) (plSpec α (c n) (N n)) (ℓ : ℤ) m₁ m₂ ≤
              C * (β ^ ℓ) ^ 2 * Qm β (gammaOf (N n) (B n)) ∧
          C * (β ^ ℓ) ^ 2 * Qm β (gammaOf (N n) (B n)) ≤ 1 / 2 ∧
          DLag β (Qm β m₁) (Qm β m₂) (ℓ : ℤ) ≤
            C * β ^ ℓ * Real.sqrt (Qm β (gammaOf (N n) (B n))) *
              Real.sqrt (min m₁ 1) * Real.sqrt (min m₂ 1) := by
  by_cases hβ : 0 < β ∧ β < 1
  · obtain ⟨C₀, C, h⟩ := llk_exists hβ.1 hβ.2
    refine ⟨C₀, C, fun N B c hreg => ?_⟩
    have hev : ∀ᶠ n in atTop, 1 ≤ gammaOf (N n) (B n) :=
      hreg.hγ.eventually_ge_atTop 1
    refine hev.mono fun n hn ℓ hℓ m₁ hm₁ m₂ hm₂ => ?_
    exact h (hreg.hNpos n) (hreg.hBpos n) (hreg.hcpos n) hn ℓ hℓ m₁ hm₁ m₂ hm₂
  · exact ⟨0, 0, fun N B c hreg => absurd ⟨hreg.hβ0, hreg.hβ1⟩ hβ⟩

/-- Private: the elementary inverse-square-root integral used in the weighted mass bound. -/
private lemma wmi_inv_sqrt {γ : ℝ} (hγ : 0 < γ) :
    IntegrableOn (fun m : ℝ => 1 / Real.sqrt m) (Ioo 0 γ) ∧
      ∫ m in Ioo 0 γ, 1 / Real.sqrt m = 2 * Real.sqrt γ := by
  have hconv : ∀ m : ℝ, 0 < m → 1 / Real.sqrt m = m ^ (-(1 / 2) : ℝ) := by
    intro m hm
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hm.le, one_div]
  have hii : IntervalIntegrable (fun m : ℝ => m ^ (-(1 / 2) : ℝ)) volume 0 γ :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hioc : IntegrableOn (fun m : ℝ => m ^ (-(1 / 2) : ℝ)) (Ioc 0 γ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hγ.le).1 hii
  have hioo : IntegrableOn (fun m : ℝ => m ^ (-(1 / 2) : ℝ)) (Ioo 0 γ) :=
    hioc.mono_set Ioo_subset_Ioc_self
  have hinv : IntegrableOn (fun m : ℝ => 1 / Real.sqrt m) (Ioo 0 γ) :=
    hioo.congr_fun (fun m hm => (hconv m hm.1).symm) measurableSet_Ioo
  refine ⟨hinv, ?_⟩
  rw [← integral_Ioc_eq_integral_Ioo]
  have hfun : ∀ m ∈ Ioc 0 γ, 1 / Real.sqrt m = m ^ (-(1 / 2) : ℝ) := by
    intro m hm
    exact hconv m hm.1
  rw [setIntegral_congr_fun measurableSet_Ioc hfun]
  rw [← intervalIntegral.integral_of_le hγ.le, integral_rpow (Or.inl (by norm_num))]
  rw [Real.zero_rpow (by norm_num)]
  rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by ring, Real.sqrt_eq_rpow]
  ring

/-- `∫_0^γ min(m,1)^{1/2} g_i ϑ_N dm ≤ Cγ`, uniformly for `i/N ≥ x₀` (task L-G.7b; proof step of
`thm:app-pl-volatility`(i), l.2253-2254; snapshot cr-2026-10-23). -/
theorem weighted_min_integral {α β : ℝ} (x₀ : ℝ) (hx₀ : x₀ ∈ Ioc 0 1) :
    ∃ C : ℝ, ∀ (N B : ℕ → ℕ) (c : ℕ → ℝ), assum_app_pl_regime α β N B c →
      ∀ᶠ n in atTop, ∀ i : Fin (N n), x₀ ≤ rowFrac i →
        IntegrableOn (fun m => Real.sqrt (min m 1) * gRow (B n) (plSpec α (c n) (N n)) i m *
            |thetaN β (B n) (plSpec α (c n) (N n)) m|) (Ioo 0 (gammaOf (N n) (B n))) ∧
        ∫ m in Ioo 0 (gammaOf (N n) (B n)), Real.sqrt (min m 1) *
            gRow (B n) (plSpec α (c n) (N n)) i m *
            |thetaN β (B n) (plSpec α (c n) (N n)) m| ≤ C * gammaOf (N n) (B n) := by
  by_cases hreg : 0 < α ∧ 0 < β ∧ β < 1
  swap
  · refine ⟨0, fun N B c R => ?_⟩
    exact absurd ⟨R.hα, R.hβ0, R.hβ1⟩ hreg
  obtain ⟨hα, hβ0, hβ1⟩ := hreg
  obtain ⟨Q, hQ⟩ := vsh_q_bound (α := α) (β := β) hα hβ0 hβ1 hx₀.1
  obtain ⟨cE, CE, hcE, hcCE, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  refine ⟨3 * (|Q| / cE), fun N B c R => ?_⟩
  filter_upwards [R.hγ.eventually_ge_atTop 1] with n hγ1
  intro i hix
  set γ := gammaOf (N n) (B n) with hγdef
  set H : ℝ → ℝ := fun m => Real.sqrt (min m 1) *
    gRow (B n) (plSpec α (c n) (N n)) i m *
      |thetaN β (B n) (plSpec α (c n) (N n)) m| with hH
  set G : ℝ → ℝ := fun m => (|Q| / cE) * (1 / Real.sqrt m + 1) with hG
  have hγ0 : 0 < γ := lt_of_lt_of_le zero_lt_one hγ1
  obtain ⟨hinv, hinv_int⟩ := wmi_inv_sqrt hγ0
  have hGint : IntegrableOn G (Ioo 0 γ) := by
    rw [hG]
    exact (hinv.add (integrableOn_const (by simp [hγ0.le]))).const_mul _
  have hWmeas := msm_W_meas (α := α) (β := β) hβ0 hβ1 (R.hNpos n) (R.hBpos n)
    (R.hcpos n) i
  rw [← hγdef] at hWmeas
  have hHmeas : AEStronglyMeasurable H (volume.restrict (Ioo 0 γ)) := by
    have hsmeas : AEStronglyMeasurable (fun m : ℝ => Real.sqrt (min m (1 : ℝ)))
        (volume.restrict (Ioo 0 γ)) :=
      (measurable_id.min measurable_const).sqrt.aemeasurable.aestronglyMeasurable
    have hright : AEStronglyMeasurable (fun m : ℝ =>
        Real.sqrt (min m 1) * Real.sqrt γ *
          |Wpart β (B n) (plSpec α (c n) (N n)) i m|) (volume.restrict (Ioo 0 γ)) := by
      have ht := ((hsmeas.mul hWmeas.norm).const_mul (Real.sqrt γ))
      simpa [Real.norm_eq_abs, mul_assoc, mul_left_comm] using ht
    refine hright.congr ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun m hm => ?_)
    change Real.sqrt (min m 1) * Real.sqrt γ *
        |Wpart β (B n) (plSpec α (c n) (N n)) i m| = H m
    rw [hH, vsh_W_eq (α := α) (β := β) (R.hNpos n) (R.hBpos n) (R.hcpos n) i hm]
    have hg0 := (vsh_g_bounds hα (R.hNpos n) (R.hBpos n) (R.hcpos n) i hm).1
    have hsγ : 0 < Real.sqrt γ := Real.sqrt_pos.2 hγ0
    simp only [abs_mul, abs_of_nonneg hg0, abs_of_pos hsγ, abs_inv]
    rw [← hγdef, abs_of_pos hsγ]
    field_simp
  have hdom : ∀ m ∈ Ioo 0 γ, H m ≤ G m := by
    intro m hm
    have hmin : 0 < min m 1 := lt_min hm.1 one_pos
    have hsmin : 0 < Real.sqrt (min m 1) := Real.sqrt_pos.2 hmin
    have hEpos : 0 < Efun β m :=
      lt_of_lt_of_le (mul_pos hcE hmin) (hE m hm.1).1
    obtain ⟨hq0, hq⟩ := hQ (N n) (B n) (c n) (R.hNpos n) (R.hBpos n)
      (R.hcpos n) hγ1 i hix m hm
    have hg0 := (vsh_g_bounds hα (R.hNpos n) (R.hBpos n) (R.hcpos n) i hm).1
    have habs : gRow (B n) (plSpec α (c n) (N n)) i m *
        |thetaN β (B n) (plSpec α (c n) (N n)) m| * Efun β m =
        gRow (B n) (plSpec α (c n) (N n)) i m *
          (thetaN β (B n) (plSpec α (c n) (N n)) m * Efun β m) := by
      rw [← abs_of_nonneg hq0, abs_mul, abs_mul, abs_of_nonneg hg0, abs_of_pos hEpos]
      ring
    have hgaE : gRow (B n) (plSpec α (c n) (N n)) i m *
        |thetaN β (B n) (plSpec α (c n) (N n)) m| * Efun β m ≤ Q := by
      rw [habs]
      simpa [mul_assoc] using hq
    have hQ0 : 0 ≤ Q := le_trans (mul_nonneg (mul_nonneg hg0 (abs_nonneg _)) hEpos.le) hgaE
    have hsmall : min m 1 * (gRow (B n) (plSpec α (c n) (N n)) i m *
        |thetaN β (B n) (plSpec α (c n) (N n)) m|) ≤ Q / cE := by
      rw [le_div_iff₀ hcE]
      calc min m 1 * (gRow (B n) (plSpec α (c n) (N n)) i m *
            |thetaN β (B n) (plSpec α (c n) (N n)) m|) * cE
          = (gRow (B n) (plSpec α (c n) (N n)) i m *
              |thetaN β (B n) (plSpec α (c n) (N n)) m|) * (cE * min m 1) := by ring
        _ ≤ (gRow (B n) (plSpec α (c n) (N n)) i m *
              |thetaN β (B n) (plSpec α (c n) (N n)) m|) * Efun β m := by gcongr; exact (hE m hm.1).1
        _ = _ := by ring
        _ ≤ Q := hgaE
    have hroot : H m ≤ (Q / cE) / Real.sqrt (min m 1) := by
      rw [hH, le_div_iff₀ hsmin]
      calc Real.sqrt (min m 1) * gRow (B n) (plSpec α (c n) (N n)) i m *
            |thetaN β (B n) (plSpec α (c n) (N n)) m| * Real.sqrt (min m 1)
          = (Real.sqrt (min m 1) * Real.sqrt (min m 1)) *
              (gRow (B n) (plSpec α (c n) (N n)) i m *
                |thetaN β (B n) (plSpec α (c n) (N n)) m|) := by ring
        _ = min m 1 * (gRow (B n) (plSpec α (c n) (N n)) i m *
              |thetaN β (B n) (plSpec α (c n) (N n)) m|) := by
                rw [Real.mul_self_sqrt hmin.le]
        _ ≤ Q / cE := hsmall
    have hinvmin : 1 / Real.sqrt (min m 1) ≤ 1 / Real.sqrt m + 1 := by
      rcases le_total m 1 with hm1 | hm1
      · rw [min_eq_left hm1]
        exact le_add_of_nonneg_right zero_le_one
      · rw [min_eq_right hm1, Real.sqrt_one]
        have : 0 ≤ 1 / Real.sqrt m := by positivity
        linarith
    rw [hG]
    calc H m ≤ (Q / cE) / Real.sqrt (min m 1) := hroot
      _ = (Q / cE) * (1 / Real.sqrt (min m 1)) := by ring
      _ ≤ (Q / cE) * (1 / Real.sqrt m + 1) := mul_le_mul_of_nonneg_left hinvmin (div_nonneg hQ0 hcE.le)
      _ = (|Q| / cE) * (1 / Real.sqrt m + 1) := by rw [abs_of_nonneg hQ0]
  have hHint : IntegrableOn H (Ioo 0 γ) := by
    refine Integrable.mono' hGint hHmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with m hm
    have hg0 := (vsh_g_bounds hα (R.hNpos n) (R.hBpos n) (R.hcpos n) i hm).1
    rw [Real.norm_eq_abs, abs_of_nonneg (by rw [hH]; exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hg0) (abs_nonneg _))]
    exact hdom m hm
  refine ⟨by simpa [hH, hγdef] using hHint, ?_⟩
  have hInt : ∫ m in Ioo 0 γ, H m ≤ ∫ m in Ioo 0 γ, G m :=
    setIntegral_mono_on hHint hGint measurableSet_Ioo hdom
  have hγone : 1 ≤ γ := hγ1
  have hsqrt : Real.sqrt γ ≤ γ := (Real.sqrt_le_iff).2 ⟨hγ0.le, by nlinarith [hγone]⟩
  calc ∫ m in Ioo 0 (gammaOf (N n) (B n)), Real.sqrt (min m 1) *
          gRow (B n) (plSpec α (c n) (N n)) i m *
          |thetaN β (B n) (plSpec α (c n) (N n)) m|
      = ∫ m in Ioo 0 γ, H m := by rw [hγdef, hH]
    _ ≤ ∫ m in Ioo 0 γ, G m := hInt
    _ = (|Q| / cE) * (2 * Real.sqrt γ + γ) := by
      rw [hG, integral_const_mul, integral_add hinv (integrableOn_const (by simp [hγ0.le])),
        hinv_int]
      simp [hγ0.le]
    _ ≤ (|Q| / cE) * (3 * γ) := by gcongr; linarith
    _ = 3 * (|Q| / cE) * gammaOf (N n) (B n) := by rw [hγdef]; ring

/-- Large-lag bound `C̄_{i,ℓ}(0) ≤ Cγ β^ℓ √Q_γ ≤ Cγ e^{-|log β|(ℓ-γ)}` for `ℓ ≥ γ + C₀`, uniformly for `i/N ≥ x₀`
(task L-G.7b; proof step of `thm:app-pl-volatility`(i), l.2244-2257; snapshot cr-2026-10-23). -/
theorem large_lag_bound {α β : ℝ} (x₀ : ℝ) (hx₀ : x₀ ∈ Ioc 0 1) :
    ∃ C₀ C : ℝ, ∀ (N B : ℕ → ℕ) (c : ℕ → ℝ), assum_app_pl_regime α β N B c →
      ∀ᶠ n in atTop, ∀ i : Fin (N n), x₀ ≤ rowFrac i → ∀ ℓ : ℕ,
        gammaOf (N n) (B n) + C₀ ≤ (ℓ : ℝ) →
          CbarPart β (B n) (plSpec α (c n) (N n)) i (ℓ : ℤ) ≤
              C * gammaOf (N n) (B n) * β ^ ℓ * Real.sqrt (Qm β (gammaOf (N n) (B n))) ∧
          CbarPart β (B n) (plSpec α (c n) (N n)) i (ℓ : ℤ) ≤
              C * gammaOf (N n) (B n) *
                Real.exp (-|Real.log β| * ((ℓ : ℝ) - gammaOf (N n) (B n))) := by
  by_cases hreg : 0 < α ∧ 0 < β ∧ β < 1
  swap
  · refine ⟨0, 0, fun N B c R => ?_⟩
    exact absurd ⟨R.hα, R.hβ0, R.hβ1⟩ hreg
  obtain ⟨hα, hβ0, hβ1⟩ := hreg
  obtain ⟨C₀, K, hK⟩ := large_lag_kernel_bounds (α := α) (β := β)
  obtain ⟨A, hA⟩ := weighted_min_integral (α := α) (β := β) x₀ hx₀
  obtain ⟨L, hL⟩ := lem_app_pl_weights_iii_logQ hβ0 hβ1
  set C1 := (Real.pi ^ 2)⁻¹ * (2 * |K| * |A| ^ 2) with hC1
  set C := C1 * (1 + Real.exp (|L| / 2)) with hC
  refine ⟨C₀, C, fun N B c R => ?_⟩
  filter_upwards [hK N B c R, hA N B c R, R.hγ.eventually_ge_atTop 1] with n hKn hAn hγ1
  intro i hix ℓ hℓ
  set γ := gammaOf (N n) (B n) with hγdef
  have hγ0 : 0 < γ := lt_of_lt_of_le zero_lt_one hγ1
  set J := Ioo 0 γ with hJ
  set H : ℝ → ℝ := fun m => Real.sqrt (min m 1) *
    gRow (B n) (plSpec α (c n) (N n)) i m *
      |thetaN β (B n) (plSpec α (c n) (N n)) m| with hH
  obtain ⟨hHint, hIbd⟩ := hAn i hix
  set I := ∫ m in J, H m with hI
  have hIeq : I = ∫ m in Ioo 0 γ, Real.sqrt (min m 1) *
      gRow (B n) (plSpec α (c n) (N n)) i m *
        |thetaN β (B n) (plSpec α (c n) (N n)) m| := by rw [hI, hJ, hH]
  have hIle : I ≤ |A| * γ := by
    rw [hIeq]
    exact hIbd.trans (mul_le_mul_of_nonneg_right (le_abs_self A) hγ0.le)
  have hH0 : ∀ m ∈ J, 0 ≤ H m := by
    intro m hm
    rw [hH]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (vsh_g_bounds hα (R.hNpos n) (R.hBpos n) (R.hcpos n) i (by simpa [hJ] using hm)).1) (abs_nonneg _)
  have hI0 : 0 ≤ I := by
    rw [hI]
    exact setIntegral_nonneg measurableSet_Ioo hH0
  set qγ := Qm β γ with hqγdef
  have hqγ0 : 0 < qγ := (vsh_Qm hβ0 hβ1 hγ0).1
  set D0 := 2 * |K| * β ^ ℓ * Real.sqrt qγ * γ⁻¹ with hD0
  have hD00 : 0 ≤ D0 := by rw [hD0]; positivity
  have hpw : ∀ m₁ ∈ J, ∀ m₂ ∈ J,
      |lagIntegrand β (B n) (plSpec α (c n) (N n)) i (ℓ : ℤ) m₁ m₂| ≤
        D0 * H m₁ * H m₂ := by
    intro m₁ hm₁ m₂ hm₂
    have hm₁' : m₁ ∈ Ioo 0 γ := by simpa [hJ] using hm₁
    have hm₂' : m₂ ∈ Ioo 0 γ := by simpa [hJ] using hm₂
    obtain ⟨hΔ, hhalf, hD⟩ := hKn ℓ hℓ m₁ hm₁' m₂ hm₂'
    have hδ : 1 / 2 ≤ deltaN β (B n) (plSpec α (c n) (N n)) (ℓ : ℤ) m₁ m₂ := by linarith
    have hδ0 : 0 < deltaN β (B n) (plSpec α (c n) (N n)) (ℓ : ℤ) m₁ m₂ :=
      lt_of_lt_of_le (by norm_num) hδ
    have hδinv : (deltaN β (B n) (plSpec α (c n) (N n)) (ℓ : ℤ) m₁ m₂)⁻¹ ≤ 2 := by
      rw [inv_le_iff_one_le_mul₀ hδ0]
      nlinarith
    have hq1 := (vsh_Qm hβ0 hβ1 hm₁'.1).1
    have hq2 := (vsh_Qm hβ0 hβ1 hm₂'.1).1
    have hDn : 0 ≤ DLag β (Qm β m₁) (Qm β m₂) (ℓ : ℤ) :=
      vsh_DLag_nonneg hβ0 hq1.le hq2.le _
    have hD' : |DLag β (Qm β m₁) (Qm β m₂) (ℓ : ℤ)| ≤
        |K| * β ^ ℓ * Real.sqrt qγ * Real.sqrt (min m₁ 1) * Real.sqrt (min m₂ 1) := by
      rw [abs_of_nonneg hDn]
      refine hD.trans ?_
      have hp : 0 ≤ β ^ ℓ * Real.sqrt qγ * Real.sqrt (min m₁ 1) * Real.sqrt (min m₂ 1) := by positivity
      nlinarith [le_abs_self K]
    have hg1 := (vsh_g_bounds hα (R.hNpos n) (R.hBpos n) (R.hcpos n) i hm₁').1
    have hg2 := (vsh_g_bounds hα (R.hNpos n) (R.hBpos n) (R.hcpos n) i hm₂').1
    have hW1 : |Wpart β (B n) (plSpec α (c n) (N n)) i m₁| =
        (Real.sqrt γ)⁻¹ * gRow (B n) (plSpec α (c n) (N n)) i m₁ *
          |thetaN β (B n) (plSpec α (c n) (N n)) m₁| := by
      rw [vsh_W_eq (α := α) (β := β) (R.hNpos n) (R.hBpos n) (R.hcpos n) i hm₁']
      rw [← hγdef]
      simp only [abs_mul, abs_of_nonneg hg1, abs_inv, abs_of_pos (Real.sqrt_pos.2 hγ0)]
    have hW2 : |Wpart β (B n) (plSpec α (c n) (N n)) i m₂| =
        (Real.sqrt γ)⁻¹ * gRow (B n) (plSpec α (c n) (N n)) i m₂ *
          |thetaN β (B n) (plSpec α (c n) (N n)) m₂| := by
      rw [vsh_W_eq (α := α) (β := β) (R.hNpos n) (R.hBpos n) (R.hcpos n) i hm₂']
      rw [← hγdef]
      simp only [abs_mul, abs_of_nonneg hg2, abs_inv, abs_of_pos (Real.sqrt_pos.2 hγ0)]
    unfold lagIntegrand lagNumer
    rw [abs_div, abs_of_pos hδ0, div_eq_mul_inv, abs_mul, abs_mul, hW1, hW2]
    calc (Real.sqrt γ)⁻¹ * gRow (B n) (plSpec α (c n) (N n)) i m₁ *
          |thetaN β (B n) (plSpec α (c n) (N n)) m₁| *
          ((Real.sqrt γ)⁻¹ * gRow (B n) (plSpec α (c n) (N n)) i m₂ *
            |thetaN β (B n) (plSpec α (c n) (N n)) m₂|) *
          |DLag β (Qm β m₁) (Qm β m₂) (ℓ : ℤ)| *
          (deltaN β (B n) (plSpec α (c n) (N n)) (ℓ : ℤ) m₁ m₂)⁻¹
        ≤ (Real.sqrt γ)⁻¹ * gRow (B n) (plSpec α (c n) (N n)) i m₁ *
          |thetaN β (B n) (plSpec α (c n) (N n)) m₁| *
          ((Real.sqrt γ)⁻¹ * gRow (B n) (plSpec α (c n) (N n)) i m₂ *
            |thetaN β (B n) (plSpec α (c n) (N n)) m₂|) *
          (|K| * β ^ ℓ * Real.sqrt qγ * Real.sqrt (min m₁ 1) * Real.sqrt (min m₂ 1)) * 2 := by
            gcongr <;> positivity
      _ = D0 * H m₁ * H m₂ := by
        rw [hD0]
        field_simp
        simp only [hH]
        rw [Real.sq_sqrt hγ0.le]
        ring
  have hinner : ∀ m₁ ∈ J, |∫ m₂ in J,
      lagIntegrand β (B n) (plSpec α (c n) (N n)) i (ℓ : ℤ) m₁ m₂| ≤ D0 * H m₁ * I := by
    intro m₁ hm₁
    have hgint : IntegrableOn (fun m₂ => (D0 * H m₁) * H m₂) J := hHint.const_mul _
    have hb := norm_integral_le_of_norm_le hgint (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with m₂ hm₂
      rw [Real.norm_eq_abs]
      exact hpw m₁ hm₁ m₂ (by simpa [hJ] using hm₂))
    rw [integral_const_mul, ← hI] at hb
    simpa [Real.norm_eq_abs, mul_assoc] using hb
  have houter : |∫ m₁ in J, ∫ m₂ in J,
      lagIntegrand β (B n) (plSpec α (c n) (N n)) i (ℓ : ℤ) m₁ m₂| ≤ D0 * I * I := by
    have hgint : IntegrableOn (fun m₁ => (D0 * I) * H m₁) J := hHint.const_mul _
    have hb := norm_integral_le_of_norm_le hgint (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with m₁ hm₁
      rw [Real.norm_eq_abs]
      have := hinner m₁ (by simpa [hJ] using hm₁)
      simpa [mul_assoc, mul_comm, mul_left_comm] using this)
    rw [integral_const_mul, ← hI] at hb
    simpa [Real.norm_eq_abs, mul_assoc] using hb
  have hmass : CbarPart β (B n) (plSpec α (c n) (N n)) i (ℓ : ℤ) ≤
      C1 * γ * β ^ ℓ * Real.sqrt qγ := by
    have hpi : 0 ≤ (Real.pi ^ 2)⁻¹ := by positivity
    have hIsq : I * I ≤ (|A| * γ) ^ 2 := by nlinarith
    unfold CbarPart lagTerm
    rw [← hJ]
    calc (Real.pi ^ 2)⁻¹ * (∫ m₁ in J, ∫ m₂ in J,
          lagIntegrand β (B n) (plSpec α (c n) (N n)) i (ℓ : ℤ) m₁ m₂)
        ≤ (Real.pi ^ 2)⁻¹ * |∫ m₁ in J, ∫ m₂ in J,
          lagIntegrand β (B n) (plSpec α (c n) (N n)) i (ℓ : ℤ) m₁ m₂| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hpi
      _ ≤ (Real.pi ^ 2)⁻¹ * (D0 * I * I) := mul_le_mul_of_nonneg_left houter hpi
      _ = ((Real.pi ^ 2)⁻¹ * D0) * (I * I) := by ring
      _ ≤ ((Real.pi ^ 2)⁻¹ * D0) * ((|A| * γ) ^ 2) :=
        mul_le_mul_of_nonneg_left hIsq (mul_nonneg hpi hD00)
      _ = (Real.pi ^ 2)⁻¹ * (D0 * ((|A| * γ) ^ 2)) := by ring
      _ = C1 * γ * β ^ ℓ * Real.sqrt qγ := by
        rw [hD0, hC1]
        field_simp
  have hC10 : 0 ≤ C1 := by rw [hC1]; positivity
  have hC1C : C1 ≤ C := by rw [hC]; nlinarith [Real.exp_pos (|L| / 2)]
  have hfirst : CbarPart β (B n) (plSpec α (c n) (N n)) i (ℓ : ℤ) ≤
      C * γ * β ^ ℓ * Real.sqrt qγ := hmass.trans (by gcongr)
  have hlam : 0 < |Real.log β| := abs_pos.2 (Real.log_neg hβ0 hβ1).ne
  set lam := |Real.log β| with hlamdef
  have hlogβ : Real.log β = -lam := by
    rw [hlamdef, abs_of_neg (Real.log_neg hβ0 hβ1)]
    ring
  have hlogQ : Real.log qγ ≤ 2 * lam * γ + |L| := by
    have ht := (abs_le.1 (hL γ hγ1)).2
    linarith [le_abs_self L]
  have hsqe : Real.sqrt qγ = Real.exp (Real.log qγ / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hqγ0]
    ring_nf
  have hbe : β ^ ℓ = Real.exp (-lam * (ℓ : ℝ)) := by
    rw [← Real.exp_log (pow_pos hβ0 ℓ), Real.log_pow, hlogβ]
    push_cast
    ring_nf
  have hdecay : β ^ ℓ * Real.sqrt qγ ≤
      Real.exp (|L| / 2) * Real.exp (-lam * ((ℓ : ℝ) - γ)) := by
    rw [hbe, hsqe, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith
  constructor
  · simpa [hγdef, hqγdef] using hfirst
  · calc CbarPart β (B n) (plSpec α (c n) (N n)) i (ℓ : ℤ)
        ≤ C1 * γ * β ^ ℓ * Real.sqrt qγ := hmass
      _ = (C1 * γ) * (β ^ ℓ * Real.sqrt qγ) := by ring
      _ ≤ (C1 * γ) * (Real.exp (|L| / 2) * Real.exp (-lam * ((ℓ : ℝ) - γ))) :=
        mul_le_mul_of_nonneg_left hdecay (mul_nonneg hC10 hγ0.le)
      _ = C1 * γ * (Real.exp (|L| / 2) * Real.exp (-lam * ((ℓ : ℝ) - γ))) := by ring
      _ ≤ C * γ * Real.exp (-lam * ((ℓ : ℝ) - γ)) := by
        rw [hC]
        have he0 : 0 ≤ Real.exp (-lam * ((ℓ : ℝ) - γ)) := (Real.exp_pos _).le
        have he : Real.exp (|L| / 2) ≤ 1 + Real.exp (|L| / 2) := by linarith
        have hc : C1 * Real.exp (|L| / 2) ≤ C1 * (1 + Real.exp (|L| / 2)) :=
          mul_le_mul_of_nonneg_left he hC10
        calc C1 * γ * (Real.exp (|L| / 2) * Real.exp (-lam * ((ℓ : ℝ) - γ)))
            = (C1 * Real.exp (|L| / 2)) * (γ * Real.exp (-lam * ((ℓ : ℝ) - γ))) := by ring
          _ ≤ (C1 * (1 + Real.exp (|L| / 2))) *
              (γ * Real.exp (-lam * ((ℓ : ℝ) - γ))) :=
                mul_le_mul_of_nonneg_right hc (mul_nonneg hγ0.le he0)
          _ = C1 * (1 + Real.exp (|L| / 2)) * γ *
              Real.exp (-lam * ((ℓ : ℝ) - γ)) := by ring
      _ = C * gammaOf (N n) (B n) *
          Real.exp (-|Real.log β| * ((ℓ : ℝ) - gammaOf (N n) (B n))) := by
            rw [← hγdef, ← hlamdef]

/-! ## Continuity of the profiles and the Riemann sum -/

/-- Private: `profF` is continuous at a point along a continuous parametrisation `(f, g)`. -/
private lemma vsc_profF_at {α : ℝ} (hα : 0 < α) {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {q0 : X} (hf : ContinuousAt f q0) (hg : ContinuousAt g q0)
    (hf0 : 0 < f q0) (hg0 : g q0 ∈ Ioo (0:ℝ) 1) :
    ContinuousAt (fun q => profF α (f q) (g q)) q0 := by
  have hcV : ContinuousAt (contV α) (g q0) :=
    (vsh_contV_cont hα).continuousAt (Ioo_mem_nhds hg0.1 hg0.2)
  have hcVg : ContinuousAt (fun q => contV α (g q)) q0 := hcV.comp hg
  have hX : ContinuousAt (fun q => f q ^ α) q0 := hf.rpow_const (Or.inl hf0.ne')
  have hpos : 0 < contV α (g q0) + f q0 ^ α :=
    add_pos (vs_contV_spec hα hg0).1 (Real.rpow_pos_of_pos hf0 α)
  unfold profF
  exact hcVg.div (hcVg.add hX) hpos.ne'

/-- Private: `profU` is continuous at a point along a continuous parametrisation `g`. -/
private lemma vsc_profU_at {α : ℝ} (hα : 0 < α) {X : Type*} [TopologicalSpace X]
    {g : X → ℝ} {q0 : X} (hg : ContinuousAt g q0) (hg0 : g q0 ∈ Ioo (0:ℝ) 1) :
    ContinuousAt (fun q => profU α (g q)) q0 := by
  have hcV : ContinuousAt (contV α) (g q0) :=
    (vsh_contV_cont hα).continuousAt (Ioo_mem_nhds hg0.1 hg0.2)
  unfold profU
  exact (hcV.comp hg).div (hg.mul (continuousAt_const.sub hg))
    (mul_pos hg0.1 (by linarith [hg0.2])).ne'

/-- Private: `profU` is strictly positive on `(0,1)`. -/
private lemma vsc_profU_pos {α : ℝ} (hα : 0 < α) {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) :
    0 < profU α p := by
  unfold profU
  exact div_pos (vs_contV_spec hα hp).1 (mul_pos hp.1 (by linarith [hp.2]))

/-- Private: the integrand `G_{x,τ}(p)` of `C_{α,x}(τ)` is bounded by `1/τ` on `(0,1-τ)`. -/
private lemma vsc_G_bd {α x τ p : ℝ} (hα : 0 < α) (hx : 0 < x) (hτ : τ ∈ Ioo (0:ℝ) 1)
    (hp : p ∈ Ioo (0:ℝ) (1 - τ)) :
    ‖(profF α x (p + τ) - profF α x p) / τ * Real.sqrt (profU α p / profU α (p + τ))‖ ≤ 1 / τ := by
  obtain ⟨hτ0, hτ1⟩ := hτ
  obtain ⟨hp0, hp1⟩ := hp
  have hp' : p ∈ Ioo (0:ℝ) 1 := ⟨hp0, by linarith⟩
  have hq' : p + τ ∈ Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  obtain ⟨h1, h2⟩ := vs_F_mem hα hx hp'
  obtain ⟨h3, h4⟩ := vs_F_mem hα hx hq'
  have hsq0 : 0 ≤ Real.sqrt (profU α p / profU α (p + τ)) := Real.sqrt_nonneg _
  have hsq1 : Real.sqrt (profU α p / profU α (p + τ)) ≤ 1 :=
    vs_sqrtU_le hα hp0 (by linarith) hq'.2
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsq0, abs_div, abs_of_pos hτ0]
  have hd : |profF α x (p + τ) - profF α x p| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hdiv : |profF α x (p + τ) - profF α x p| / τ ≤ 1 / τ := div_le_div_of_nonneg_right hd hτ0.le
  exact (mul_le_mul_of_nonneg_left hsq1 (div_nonneg (abs_nonneg _) hτ0.le)).trans
    (by rw [mul_one]; exact hdiv)

/-- Private: joint-in-parameters continuity of the Riemann-integrand
`p ↦ (f_x(p+τ)-f_x(p))/τ · √(U(p)/U(p+τ))` at `p = (1-τ)s` (the substitution `p = (1-τ)s`). -/
private lemma vsc_G_cont {α : ℝ} (hα : 0 < α) {X : Type*} [TopologicalSpace X]
    {xf tf sf : X → ℝ} {q0 : X} (hx : ContinuousAt xf q0) (hxpos : 0 < xf q0)
    (ht : ContinuousAt tf q0) (ht0 : tf q0 ∈ Ioo (0:ℝ) 1)
    (hs : ContinuousAt sf q0) (hs0 : sf q0 ∈ Ioo (0:ℝ) 1) :
    ContinuousAt (fun q => (profF α (xf q) ((1 - tf q) * sf q + tf q) -
        profF α (xf q) ((1 - tf q) * sf q)) / tf q *
      Real.sqrt (profU α ((1 - tf q) * sf q) / profU α ((1 - tf q) * sf q + tf q))) q0 := by
  have hp : (1 - tf q0) * sf q0 ∈ Ioo (0:ℝ) 1 :=
    ⟨mul_pos (by linarith [ht0.2]) hs0.1, by nlinarith [mul_pos ht0.1 hs0.1, hs0.2, ht0.2]⟩
  have hq : (1 - tf q0) * sf q0 + tf q0 ∈ Ioo (0:ℝ) 1 :=
    ⟨by nlinarith [mul_pos (sub_pos.2 ht0.2) hs0.1, ht0.1],
      by nlinarith [mul_pos (sub_pos.2 ht0.2) (sub_pos.2 hs0.2)]⟩
  have c1 : ContinuousAt (fun q => 1 - tf q) q0 := continuousAt_const.sub ht
  have cp : ContinuousAt (fun q => (1 - tf q) * sf q) q0 := c1.mul hs
  have cq : ContinuousAt (fun q => (1 - tf q) * sf q + tf q) q0 := cp.add ht
  have hF1 := vsc_profF_at hα hx cq hxpos hq
  have hF2 := vsc_profF_at hα hx cp hxpos hp
  have hU1 := vsc_profU_at hα cp hp
  have hU2 := vsc_profU_at hα cq hq
  have hsqrt : ContinuousAt (fun q => Real.sqrt (profU α ((1 - tf q) * sf q) /
      profU α ((1 - tf q) * sf q + tf q))) q0 :=
    Real.continuous_sqrt.continuousAt.comp (hU1.div hU2 (vsc_profU_pos hα hq).ne')
  exact ((hF1.sub hF2).div ht ht0.1.ne').mul hsqrt

/-- Private: dominated convergence in the substituted form of `C_{α,x}(τ)`, at a point `(x0,τ0)`. -/
private lemma vsc_dct {α : ℝ} (hα : 0 < α) (K : Set ℝ) (hK : K ⊆ Ioc 0 1)
    {η : ℝ} (hη0 : 0 < η) (x0 τ0 : ℝ) (hx0K : x0 ∈ K) (hτ0 : τ0 ∈ Icc η (1 - η)) :
    ContinuousWithinAt (fun q : ℝ × ℝ => ∫ s in (0:ℝ)..1,
      (profF α q.1 ((1 - q.2) * s + q.2) - profF α q.1 ((1 - q.2) * s)) / q.2 *
        Real.sqrt (profU α ((1 - q.2) * s) / profU α ((1 - q.2) * s + q.2)))
      (K ×ˢ Icc η (1 - η)) (x0, τ0) := by
  have hx0 : 0 < x0 := (hK hx0K).1
  have hτ0' : τ0 ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hτ0.1], by linarith [hτ0.2]⟩
  have hA : ∀ᶠ q in 𝓝[K ×ˢ Icc η (1 - η)] (x0, τ0), AEStronglyMeasurable
      (fun s : ℝ => (profF α q.1 ((1 - q.2) * s + q.2) - profF α q.1 ((1 - q.2) * s)) / q.2 *
        Real.sqrt (profU α ((1 - q.2) * s) / profU α ((1 - q.2) * s + q.2)))
      (volume.restrict (Set.uIoc 0 1)) := by
    refine eventually_nhdsWithin_of_forall (fun q hq => ?_)
    have hxq : 0 < q.1 := (hK hq.1).1
    have hτq : q.2 ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩
    rw [Set.uIoc_of_le zero_le_one, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    refine ContinuousOn.aestronglyMeasurable (fun s hs => ?_) measurableSet_Ioo
    exact (vsc_G_cont hα (xf := fun _ : ℝ => q.1) (tf := fun _ : ℝ => q.2)
      (sf := fun t : ℝ => t) (q0 := s) continuousAt_const hxq continuousAt_const hτq
      continuousAt_id hs).continuousWithinAt
  have hB : ∀ᶠ q in 𝓝[K ×ˢ Icc η (1 - η)] (x0, τ0), ∀ᵐ s ∂(volume : Measure ℝ),
      s ∈ Set.uIoc 0 1 → ‖(profF α q.1 ((1 - q.2) * s + q.2) - profF α q.1 ((1 - q.2) * s)) /
        q.2 * Real.sqrt (profU α ((1 - q.2) * s) / profU α ((1 - q.2) * s + q.2))‖ ≤
          (fun _ : ℝ => 1 / η) s := by
    refine eventually_nhdsWithin_of_forall (fun q hq => ?_)
    have hxq : 0 < q.1 := (hK hq.1).1
    have hτq : q.2 ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩
    filter_upwards [(Set.countable_singleton (1:ℝ)).ae_notMem volume] with s hs1 hsI
    rw [Set.uIoc_of_le zero_le_one] at hsI
    have hs : s ∈ Ioo (0:ℝ) 1 :=
      ⟨hsI.1, lt_of_le_of_ne hsI.2 (fun h => hs1 (Set.mem_singleton_iff.2 h))⟩
    have hp : (1 - q.2) * s ∈ Ioo (0:ℝ) (1 - q.2) :=
      ⟨mul_pos (by linarith [hτq.2]) hs.1,
        by nlinarith [mul_pos (sub_pos.2 hτq.2) (sub_pos.2 hs.2)]⟩
    have hG := vsc_G_bd (x := q.1) (τ := q.2) hα hxq hτq hp
    refine hG.trans ?_
    exact one_div_le_one_div_of_le hη0 (by linarith [hq.2.1])
  have hC : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc 0 1 →
      ContinuousWithinAt (fun q : ℝ × ℝ =>
        (profF α q.1 ((1 - q.2) * s + q.2) - profF α q.1 ((1 - q.2) * s)) / q.2 *
          Real.sqrt (profU α ((1 - q.2) * s) / profU α ((1 - q.2) * s + q.2)))
        (K ×ˢ Icc η (1 - η)) (x0, τ0) := by
    filter_upwards [(Set.countable_singleton (1:ℝ)).ae_notMem volume] with s hs1
    intro hsI
    rw [Set.uIoc_of_le zero_le_one] at hsI
    have hs : s ∈ Ioo (0:ℝ) 1 :=
      ⟨hsI.1, lt_of_le_of_ne hsI.2 (fun h => hs1 (Set.mem_singleton_iff.2 h))⟩
    exact (vsc_G_cont hα (xf := fun q : ℝ × ℝ => q.1) (tf := fun q : ℝ × ℝ => q.2)
      (sf := fun _ : ℝ×ℝ => s) (q0 := (x0, τ0)) continuous_fst.continuousAt
      hx0 continuous_snd.continuousAt hτ0' continuousAt_const hs).continuousWithinAt
  exact intervalIntegral.continuousWithinAt_of_dominated_interval hA hB intervalIntegrable_const hC

/-- `(x,τ) ↦ C_{α,x}(τ)` is jointly continuous on `K × [η,1-η]` for `K ⊆ (0,1]` compact
(task L-G.7b; proof step of `thm:app-pl-volatility`(i), l.2261-2266, "the bounds above are locally uniform in
`x`"; snapshot cr-2026-10-23). -/
theorem profC_continuousOn {α : ℝ} (hα : 0 < α) (K : Set ℝ) (hK : K ⊆ Ioc 0 1) (hKc : IsCompact K)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1 / 2) :
    ContinuousOn (fun q : ℝ × ℝ => profC α q.1 q.2) (K ×ˢ Icc η (1 - η)) := by
  -- substitution `p = (1-τ)s` turns the variable upper limit into `[0,1]`
  have hrepr : ∀ x τ : ℝ, 0 < x → τ ∈ Ioo (0:ℝ) 1 →
      profC α x τ = (1 - τ) * ∫ s in (0:ℝ)..1,
        (profF α x ((1 - τ) * s + τ) - profF α x ((1 - τ) * s)) / τ *
          Real.sqrt (profU α ((1 - τ) * s) / profU α ((1 - τ) * s + τ)) := by
    intro x τ _ hτ
    have hc : (1 - τ) ≠ 0 := (sub_pos.2 hτ.2).ne'
    have h := intervalIntegral.integral_comp_mul_left
      (fun p : ℝ => (profF α x (p + τ) - profF α x p) / τ *
        Real.sqrt (profU α p / profU α (p + τ))) (a := 0) (b := 1) hc
    simp only [mul_zero, mul_one, smul_eq_mul] at h
    unfold profC
    rw [h, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have hΦ : ContinuousOn (fun q : ℝ × ℝ => ∫ s in (0:ℝ)..1,
      (profF α q.1 ((1 - q.2) * s + q.2) - profF α q.1 ((1 - q.2) * s)) / q.2 *
        Real.sqrt (profU α ((1 - q.2) * s) / profU α ((1 - q.2) * s + q.2)))
      (K ×ˢ Icc η (1 - η)) := by
    rintro ⟨x0, τ0⟩ ⟨hx0K, hτ0⟩
    exact vsc_dct hα K hK hη0 x0 τ0 hx0K hτ0
  have h1 : ContinuousOn (fun q : ℝ × ℝ => 1 - q.2) (K ×ˢ Icc η (1 - η)) :=
    continuousOn_const.sub continuousOn_snd
  refine ((h1.mul hΦ)).congr (fun q hq => ?_)
  have hxq : 0 < q.1 := (hK hq.1).1
  have hτq : q.2 ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩
  exact hrepr q.1 q.2 hxq hτq

/-- Private: error on one cell of a left-endpoint Riemann sum. -/
private lemma vsc_cell_error {c : ℝ → ℝ} {a b x y γ ε : ℝ} (hγ : 0 < γ)
    (hxy : x ≤ y) (hsub : Icc x y ⊆ Icc a b) (hc : ContinuousOn c (Icc a b))
    (hlen : y - x = γ⁻¹) (hmod : ∀ t ∈ Icc x y, |c t - c x| ≤ ε) :
    |(∫ t in x..y, c t) - γ⁻¹ * c x| ≤ ε / γ := by
  have hci : IntervalIntegrable c volume x y :=
    (hc.mono (by simpa [Set.uIcc_of_le hxy] using hsub)).intervalIntegrable
  have hconst : IntervalIntegrable (fun _ : ℝ => c x) volume x y := intervalIntegrable_const
  have heq : (∫ t in x..y, c t) - γ⁻¹ * c x = ∫ t in x..y, c t - c x := by
    rw [intervalIntegral.integral_sub hci hconst]
    simp [hlen]
  rw [heq, ← Real.norm_eq_abs]
  calc
    ‖∫ t in x..y, c t - c x‖ ≤ ε * |y - x| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (C := ε) fun t ht => by
        rw [Real.norm_eq_abs]
        exact hmod t ((Set.uIcc_of_le hxy).symm ▸ Set.uIoc_subset_uIcc ht)
    _ = ε / γ := by
      rw [abs_of_nonneg (sub_nonneg.2 hxy), hlen]
      field_simp

/-- Private: summing the errors of consecutive cells. -/
private lemma vsc_range_error {c : ℝ → ℝ} {γ ε : ℝ} (p : ℤ) (N : ℕ) (hγ : 0 < γ)
    (hc : Continuous c)
    (hcell : ∀ k < N, |γ⁻¹ * c (((p : ℝ) + k) / γ) -
      ∫ t in ((p : ℝ) + k) / γ..((p : ℝ) + (k + 1)) / γ, c t| ≤ ε / γ) :
    |γ⁻¹ * ∑ k ∈ Finset.range N, c (((p : ℝ) + k) / γ) -
        ∫ t in (p : ℝ) / γ..((p : ℝ) + N) / γ, c t| ≤ (N : ℝ) * (ε / γ) := by
  have hint : ∀ k < N, IntervalIntegrable c volume
      (((p : ℝ) + k) / γ) (((p : ℝ) + (k + 1)) / γ) := by
    intro k _
    exact hc.intervalIntegrable _ _
  have hInt : (∑ k ∈ Finset.range N,
      ∫ t in ((p : ℝ) + k) / γ..((p : ℝ) + (k + 1)) / γ, c t) =
      ∫ t in (p : ℝ) / γ..((p : ℝ) + N) / γ, c t := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (intervalIntegral.sum_integral_adjacent_intervals (f := c)
        (a := fun k : ℕ => ((p : ℝ) + k) / γ) (n := N) (μ := volume) fun k hk => by
          simpa [Nat.cast_add, Nat.cast_one] using hint k hk)
  have hsum : γ⁻¹ * ∑ k ∈ Finset.range N, c (((p : ℝ) + k) / γ) =
      ∑ k ∈ Finset.range N, γ⁻¹ * c (((p : ℝ) + k) / γ) := by
    rw [Finset.mul_sum]
  rw [hsum, ← hInt, ← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ Finset.range N, (γ⁻¹ * c (((p : ℝ) + k) / γ) -
        ∫ t in ((p : ℝ) + k) / γ..((p : ℝ) + (k + 1)) / γ, c t)|
        ≤ ∑ k ∈ Finset.range N, |γ⁻¹ * c (((p : ℝ) + k) / γ) -
          ∫ t in ((p : ℝ) + k) / γ..((p : ℝ) + (k + 1)) / γ, c t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range N, ε / γ := by
      gcongr with k hk
      exact hcell k (Finset.mem_range.1 hk)
    _ = (N : ℝ) * (ε / γ) := by simp

/-- Private: a quantitative lattice Riemann-sum estimate for a globally uniformly continuous,
bounded function. -/
private lemma vsc_global_lattice_error {c : ℝ → ℝ} {a b γ ε δ M : ℝ}
    (hab : a < b) (hγ : 1 ≤ γ) (hwide : 2 < (b - a) * γ) (hε : 0 ≤ ε)
    (hc : Continuous c) (hM : ∀ x, |c x| ≤ M) (hδ : 0 < δ)
    (hmod : ∀ x y, |x - y| < δ → |c x - c y| ≤ ε) (hmesh : γ⁻¹ < δ) :
    |γ⁻¹ * ∑ l ∈ Finset.Icc ⌈a * γ⌉ ⌊b * γ⌋, c ((l : ℝ) / γ) -
        ∫ t in a..b, c t| ≤ (b - a + 2) * ε + 2 * M / γ := by
  let p : ℤ := ⌈a * γ⌉
  let q : ℤ := ⌊b * γ⌋
  let N : ℕ := (q + 1 - p).toNat
  have hγ0 : 0 < γ := zero_lt_one.trans_le hγ
  have hp_lt : (p : ℝ) < a * γ + 1 := by
    simpa [p] using (Int.ceil_lt_add_one (a * γ))
  have hq_lt : b * γ < (q : ℝ) + 1 := by
    simpa [q] using (Int.lt_floor_add_one (b * γ))
  have hpq : p ≤ q := by
    by_contra h
    have hqp : (q : ℝ) < (p : ℝ) := by exact_mod_cast (lt_of_not_ge h)
    nlinarith
  have hNint : (N : ℤ) = q + 1 - p := by
    simp only [N]
    rw [Int.toNat_of_nonneg]
    omega
  have hNreal : (N : ℝ) = (q : ℝ) + 1 - p := by exact_mod_cast hNint
  have hcell : ∀ k < N, |γ⁻¹ * c (((p : ℝ) + k) / γ) -
      ∫ t in ((p : ℝ) + k) / γ..((p : ℝ) + (k + 1)) / γ, c t| ≤ ε / γ := by
    intro k hk
    have hxy : ((p : ℝ) + k) / γ ≤ ((p : ℝ) + (k + 1)) / γ := by
      apply div_le_div_of_nonneg_right _ hγ0.le
      norm_num
    have hlen : ((p : ℝ) + (k + 1)) / γ - ((p : ℝ) + k) / γ = γ⁻¹ := by
      field_simp
      ring
    have hcell' := vsc_cell_error (c := c) (a := ((p : ℝ) + k) / γ)
      (b := ((p : ℝ) + (k + 1)) / γ) hγ0 hxy (by simp) hc.continuousOn hlen
      (fun t ht => by
        apply hmod
        have ht' : |t - ((p : ℝ) + k) / γ| ≤ γ⁻¹ := by
          rw [abs_of_nonneg (sub_nonneg.2 ht.1), ← hlen]
          linarith [ht.2]
        exact lt_of_le_of_lt ht' hmesh)
    simpa [abs_sub_comm] using hcell'
  have hR := vsc_range_error p N hγ0 hc hcell
  have hsum : (∑ l ∈ Finset.Icc p q, c ((l : ℝ) / γ)) =
      ∑ k ∈ Finset.range N, c (((p : ℝ) + k) / γ) := by
    rw [Int.Icc_eq_finset_map]
    simp only [Finset.sum_map, Function.Embedding.coe_trans, Function.comp_apply,
      Nat.castEmbedding_apply, addLeftEmbedding_apply]
    rw [show (q + 1 - p).toNat = N by rfl]
    congr 1
    funext k
    norm_cast
  have hNbd : (N : ℝ) / γ ≤ b - a + 2 := by
    have hq : (q : ℝ) ≤ b * γ := Int.floor_le _
    have hp : a * γ ≤ (p : ℝ) := Int.le_ceil _
    rw [hNreal]
    have hba : 0 < b - a := sub_pos.2 hab
    have hi : 1 / γ ≤ 1 := (div_le_one hγ0).2 hγ
    calc
      ((q : ℝ) + 1 - p) / γ ≤ ((b - a) * γ + 1) / γ := by
        apply div_le_div_of_nonneg_right _ hγ0.le
        linarith
      _ = b - a + 1 / γ := by field_simp
      _ ≤ b - a + 2 := by linarith
  have hR' : |γ⁻¹ * ∑ l ∈ Finset.Icc p q, c ((l : ℝ) / γ) -
      ∫ t in (p : ℝ) / γ..((q : ℝ) + 1) / γ, c t| ≤ (b - a + 2) * ε := by
    rw [hsum]
    have hend : ((p : ℝ) + N) / γ = ((q : ℝ) + 1) / γ := by rw [hNreal]; ring
    rw [← hend]
    refine hR.trans ?_
    calc
      (N : ℝ) * (ε / γ) = ((N : ℝ) / γ) * ε := by ring
      _ ≤ (b - a + 2) * ε := mul_le_mul_of_nonneg_right hNbd hε
  have hP : a ≤ (p : ℝ) / γ := by
    rw [le_div_iff₀ hγ0]
    exact Int.le_ceil _
  have hPlen : (p : ℝ) / γ - a < 1 / γ := by
    calc
      (p : ℝ) / γ - a < (a * γ + 1) / γ - a :=
        sub_lt_sub_right (div_lt_div_of_pos_right hp_lt hγ0) a
      _ = 1 / γ := by field_simp <;> ring
  have hQ : b ≤ ((q : ℝ) + 1) / γ := by
    rw [le_div_iff₀ hγ0]
    exact hq_lt.le
  have hQlen : ((q : ℝ) + 1) / γ - b ≤ 1 / γ := by
    calc
      ((q : ℝ) + 1) / γ - b ≤ (b * γ + 1) / γ - b := by
        apply sub_le_sub_right
        exact div_le_div_of_nonneg_right (by linarith [Int.floor_le (b * γ)]) hγ0.le
      _ = 1 / γ := by field_simp <;> ring
  have hE : |(∫ t in (p : ℝ) / γ..((q : ℝ) + 1) / γ, c t) -
      ∫ t in a..b, c t| ≤ 2 * M / γ := by
    rw [intervalIntegral.integral_interval_sub_interval_comm'
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    refine (abs_sub _ _).trans ?_
    have hM0 : 0 ≤ M := le_trans (abs_nonneg (c 0)) (hM 0)
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := b) (b := ((q : ℝ) + 1) / γ) (C := M) (f := c) fun x _ => by
        simpa [Real.norm_eq_abs] using hM x
    have h2 := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := (p : ℝ) / γ) (C := M) (f := c) fun x _ => by
        simpa [Real.norm_eq_abs] using hM x
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hQ)] at h1
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hP)] at h2
    calc
      |∫ t in b..((q : ℝ) + 1) / γ, c t| + |∫ t in a..(p : ℝ) / γ, c t|
          ≤ M * (1 / γ) + M * (1 / γ) := add_le_add
            (h1.trans (mul_le_mul_of_nonneg_left hQlen hM0))
            (h2.trans (mul_le_mul_of_nonneg_left hPlen.le hM0))
      _ = 2 * M / γ := by ring
  rw [show ⌈a * γ⌉ = p by rfl, show ⌊b * γ⌋ = q by rfl]
  exact (abs_sub_le_iff.2 ⟨by linarith [abs_le.1 hR', abs_le.1 hE],
    by linarith [abs_le.1 hR', abs_le.1 hE]⟩)

/-- Private: a uniform summand error remains uniform after lattice averaging. -/
private lemma vsc_uniform_sum_error {f : ℤ → ℝ} {c : ℝ → ℝ} {a b γ ε : ℝ}
    (hab : a < b) (hγ : 1 ≤ γ) (hwide : 2 < (b - a) * γ) (hε : 0 ≤ ε)
    (hpoint : ∀ l : ℤ, (l : ℝ) / γ ∈ Icc a b → |f l - c ((l : ℝ) / γ)| ≤ ε) :
    |γ⁻¹ * ∑ l ∈ Finset.Icc ⌈a * γ⌉ ⌊b * γ⌋, f l -
      γ⁻¹ * ∑ l ∈ Finset.Icc ⌈a * γ⌉ ⌊b * γ⌋, c ((l : ℝ) / γ)| ≤
        (b - a + 2) * ε := by
  let p : ℤ := ⌈a * γ⌉
  let q : ℤ := ⌊b * γ⌋
  have hγ0 : 0 < γ := zero_lt_one.trans_le hγ
  have hpq : p ≤ q := by
    have hp_lt : (p : ℝ) < a * γ + 1 := by
      simpa [p] using (Int.ceil_lt_add_one (a * γ))
    have hq_lt : b * γ < (q : ℝ) + 1 := by
      simpa [q] using (Int.lt_floor_add_one (b * γ))
    by_contra h
    have hqp : (q : ℝ) < (p : ℝ) := by exact_mod_cast (lt_of_not_ge h)
    nlinarith
  have hcard : ((Finset.Icc p q).card : ℝ) / γ ≤ b - a + 2 := by
    have hcI : ((Finset.Icc p q).card : ℤ) = q + 1 - p :=
      Int.card_Icc_of_le p q (by omega)
    have hcR : ((Finset.Icc p q).card : ℝ) = (q : ℝ) + 1 - p := by exact_mod_cast hcI
    have hq : (q : ℝ) ≤ b * γ := Int.floor_le _
    have hp : a * γ ≤ (p : ℝ) := Int.le_ceil _
    have hi : 1 / γ ≤ 1 := (div_le_one hγ0).2 hγ
    rw [hcR]
    calc
      ((q : ℝ) + 1 - p) / γ ≤ ((b - a) * γ + 1) / γ := by
        apply div_le_div_of_nonneg_right _ hγ0.le
        linarith
      _ = b - a + 1 / γ := by field_simp
      _ ≤ b - a + 2 := by linarith
  rw [show ⌈a * γ⌉ = p by rfl, show ⌊b * γ⌋ = q by rfl,
    ← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_inv, abs_of_pos hγ0]
  calc
    γ⁻¹ * |∑ l ∈ Finset.Icc p q, (f l - c ((l : ℝ) / γ))|
        ≤ γ⁻¹ * ∑ l ∈ Finset.Icc p q, |f l - c ((l : ℝ) / γ)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.2 hγ0.le)
    _ ≤ γ⁻¹ * ((Finset.Icc p q).card * ε) := by
      gcongr
      simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul (Finset.Icc p q)
        (fun l => |f l - c ((l : ℝ) / γ)|) ε fun l hl => hpoint l ⟨by
        rw [le_div_iff₀ hγ0]
        exact (Int.le_ceil _).trans (by exact_mod_cast (Finset.mem_Icc.1 hl).1), by
        rw [div_le_iff₀ hγ0]
        exact (by exact_mod_cast (Finset.mem_Icc.1 hl).2 : (l : ℝ) ≤ q).trans (Int.floor_le _)⟩
    _ ≤ (b - a + 2) * ε := by
      calc
        γ⁻¹ * ((Finset.Icc p q).card * ε) =
            (((Finset.Icc p q).card : ℝ) / γ) * ε := by ring
        _ ≤ (b - a + 2) * ε := mul_le_mul_of_nonneg_right hcard hε

/-- Riemann sums over the remaining lags: if `c_n(ℓ) - c(ℓ/γ_n) → 0` uniformly on `ℓ/γ_n ∈ [η,1-η]`
and `c` is continuous there, then `γ_n⁻¹ ∑_{η γ_n ≤ ℓ ≤ (1-η)γ_n} c_n(ℓ) → ∫_η^{1-η} c`
(task L-G.7b; proof step of `thm:app-pl-volatility`(i), l.2260-2262; snapshot cr-2026-10-23). -/
theorem riemann_lag_sum (γn : ℕ → ℝ) (hγ : Tendsto γn atTop atTop) (cn : ℕ → ℤ → ℝ) (c : ℝ → ℝ)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1 / 2) (hc : ContinuousOn c (Icc η (1 - η)))
    (hunif : ∀ ε > 0, ∀ᶠ n in atTop, ∀ ℓ : ℤ, (ℓ : ℝ) / γn n ∈ Icc η (1 - η) →
      |cn n ℓ - c ((ℓ : ℝ) / γn n)| ≤ ε) :
    Tendsto (fun n => (γn n)⁻¹ *
        ∑ ℓ ∈ Finset.Icc ⌈η * γn n⌉ ⌊(1 - η) * γn n⌋, cn n ℓ)
      atTop (𝓝 (∫ τ in η..(1 - η), c τ)) := by
  have hab : η < 1 - η := by linarith
  let C : ℝ → ℝ := fun x => c (Set.projIcc η (1 - η) hab.le x)
  have hC : Continuous C := by
    exact ((continuousOn_iff_continuous_restrict.1 hc).comp continuous_projIcc)
  have hCeq : ∀ x ∈ Icc η (1 - η), C x = c x := by
    intro x hx
    simp [C, Set.projIcc_of_mem hab.le hx]
  have hInt : (∫ t in η..(1 - η), C t) = ∫ t in η..(1 - η), c t := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hab.le] at hx
    exact hCeq x hx
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (c η)) (hM η ⟨le_rfl, hab.le⟩)
  have hCM : ∀ x, |C x| ≤ M := by
    intro x
    simpa [Real.norm_eq_abs, C] using hM (Set.projIcc η (1 - η) hab.le x)
      (Set.projIcc η (1 - η) hab.le x).property
  have hCU : UniformContinuous C := by
    exact (isCompact_Icc.uniformContinuousOn_of_continuous hc).restrict.comp
      (LipschitzWith.projIcc hab.le).uniformContinuous
  rw [Metric.tendsto_atTop]
  intro ε hε
  let A : ℝ := (1 - η) - η + 2
  have hA : 0 < A := by dsimp [A]; linarith
  let e : ℝ := ε / (4 * A)
  have he : 0 < e := div_pos hε (mul_pos (by norm_num) hA)
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuous_iff.1 hCU) e he
  have hU := hunif e he
  apply eventually_atTop.1
  filter_upwards [hU, hγ.eventually_ge_atTop 1,
    hγ.eventually_gt_atTop (3 / ((1 - η) - η)),
    hγ.eventually_gt_atTop (1 / δ), hγ.eventually_gt_atTop (8 * M / ε)] with n hUn hγ1 hγw hγδ hγM
  have hγ0 : 0 < γn n := zero_lt_one.trans_le hγ1
  have hw0 : 0 < (1 - η) - η := sub_pos.2 hab
  have hwide : 2 < ((1 - η) - η) * γn n := by
    rw [div_lt_iff₀ hw0] at hγw
    linarith
  have hmesh : (γn n)⁻¹ < δ := by
    rw [div_lt_iff₀ hδ] at hγδ
    rw [inv_lt_iff_one_lt_mul₀ hγ0]
    simpa [mul_comm] using hγδ
  have hmod' : ∀ x y, |x - y| < δ → |C x - C y| ≤ e := by
    intro x y hxy
    simpa [Real.dist_eq] using (hmod hxy).le
  have hLat := vsc_global_lattice_error (c := C) (a := η) (b := 1 - η)
    hab hγ1 hwide he.le hC hCM hδ hmod' hmesh
  have hUni := vsc_uniform_sum_error (f := cn n) (c := C) (a := η) (b := 1 - η)
    hab hγ1 hwide he.le (fun l hl => by simpa [hCeq _ hl] using hUn l hl)
  have htail : 2 * M / γn n < ε / 4 := by
    rw [div_lt_iff₀ hε] at hγM
    rw [div_lt_iff₀ hγ0]
    nlinarith
  rw [Real.dist_eq, ← hInt]
  refine (abs_sub_le
    ((γn n)⁻¹ * ∑ l ∈ Finset.Icc ⌈η * γn n⌉ ⌊(1 - η) * γn n⌋, cn n l)
    ((γn n)⁻¹ * ∑ l ∈ Finset.Icc ⌈η * γn n⌉ ⌊(1 - η) * γn n⌋,
      C ((l : ℝ) / γn n))
    (∫ t in η..(1 - η), C t)).trans_lt ?_
  calc
    |(γn n)⁻¹ * ∑ l ∈ Finset.Icc ⌈η * γn n⌉ ⌊(1 - η) * γn n⌋, cn n l -
        (γn n)⁻¹ * ∑ l ∈ Finset.Icc ⌈η * γn n⌉ ⌊(1 - η) * γn n⌋,
          C ((l : ℝ) / γn n)| +
      |(γn n)⁻¹ * ∑ l ∈ Finset.Icc ⌈η * γn n⌉ ⌊(1 - η) * γn n⌋,
          C ((l : ℝ) / γn n) - ∫ t in η..(1 - η), C t|
        ≤ A * e + (A * e + 2 * M / γn n) := add_le_add hUni hLat
    _ < ε := by
      have hAe : A * e = ε / 4 := by dsimp [e]; field_simp
      rw [hAe]
      linarith

/-! ## Steps of `lem:app-pl-vector` -/

private lemma p10_Q_bound {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ1 : 1 ≤ γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m ∈ Ioo 0 γ, Qm β m ≤ K * m := by
  have hγ : 0 < γ := zero_lt_one.trans_le hγ1
  obtain ⟨hQγ, -⟩ := vsh_Qm hβ0 hβ1 hγ
  refine ⟨Qm β γ, hQγ, fun m hm => ?_⟩
  have h := llk_K1 hβ0 hβ1 hm.1 hm.2.le hγ1
  exact h.trans (mul_le_mul_of_nonneg_left (min_le_left m 1) hQγ.le)

private lemma p10_Zjoint_meas (β : ℝ) : Measurable (fun z : ℝ × ℝ => Zg β z.1 z.2) := by
  unfold Zg
  exact (measurable_snd.sqrt).mul (Measurable.tsum (fun a => by fun_prop))

/-- Integrability and measurability: `|W_i(m)| √Q_m` is integrable on `(0,γ)` (`W_i ∼ c/m` at `0`, so `W_i`
itself is not; `‖𝒵_g(q)‖_{L²} ≤ √q` by `lem_app_pl_age_i`), `W_i` is a.e.-strongly measurable, and the product integrand is jointly a.e.-strongly measurable for `Lebesgue|(0,γ) ⊗ N(0,1)` (task L-G.7b; implicit
in the use of Minkowski's integral inequality, `lem:app-pl-vector` proof, l.1949-1956, and in
`eqn:app-pl-head-norm`, l.1968-1972; snapshot cr-2026-10-23). -/
theorem Wpart_integrable_measurable {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) :
    ∀ᶠ n in atTop, ∀ i : Fin (N n),
      IntegrableOn (fun m => |Wpart β (B n) (plSpec α (c n) (N n)) i m| * Real.sqrt (Qm β m))
        (Ioo 0 (gammaOf (N n) (B n))) ∧
      AEStronglyMeasurable (Wpart β (B n) (plSpec α (c n) (N n)) i)
        (volume.restrict (Ioo 0 (gammaOf (N n) (B n)))) ∧
      AEStronglyMeasurable
        (fun q : ℝ × ℝ => Wpart β (B n) (plSpec α (c n) (N n)) i q.1 * Zg β q.2 (Qm β q.1))
        ((volume.restrict (Ioo 0 (gammaOf (N n) (B n)))).prod (gaussianReal 0 1)) := by
  obtain ⟨cE, CE, hcE, hcCE, hE⟩ := lem_app_pl_weights_iii_E R.hβ0 R.hβ1
  filter_upwards [R.hγ.eventually_ge_atTop 1] with n hγ1
  intro i
  set γ := gammaOf (N n) (B n) with hγdef
  set J := Ioo 0 γ with hJdef
  have hγ : 0 < γ := zero_lt_one.trans_le hγ1
  have hJm : MeasurableSet J := measurableSet_Ioo
  have hxi : 0 < rowFrac i := by
    unfold rowFrac rowIdx
    exact div_pos (by positivity) (by exact_mod_cast R.hNpos n)
  obtain ⟨Q, hQ⟩ := vsh_q_bound (α := α) (β := β) R.hα R.hβ0 R.hβ1 hxi
  have hq := hQ (N n) (B n) (c n) (R.hNpos n) (R.hBpos n) (R.hcpos n) hγ1 i le_rfl
  obtain ⟨K, hK0, hK⟩ := p10_Q_bound R.hβ0 R.hβ1 hγ1
  have hWm : AEStronglyMeasurable (Wpart β (B n) (plSpec α (c n) (N n)) i)
      (volume.restrict J) := by
    simpa [J, γ] using msm_W_meas (α := α) (β := β) R.hβ0 R.hβ1
      (R.hNpos n) (R.hBpos n) (R.hcpos n) i
  have hQm : AEMeasurable (Qm β) (volume.restrict J) :=
    (aemeasurable_restrict_of_monotoneOn measurableSet_Ioi
      (msm_Qm_mono R.hβ0 R.hβ1)).mono_measure
        (Measure.restrict_mono (fun m hm => hm.1) le_rfl)
  have hprod : AEStronglyMeasurable
      (fun q : ℝ × ℝ => Wpart β (B n) (plSpec α (c n) (N n)) i q.1 *
        Zg β q.2 (Qm β q.1))
      ((volume.restrict J).prod (gaussianReal 0 1)) := by
    have hW1 := hWm.aemeasurable.comp_fst (ν := gaussianReal 0 1)
    have hQ1 := hQm.comp_fst (ν := gaussianReal 0 1)
    have hZ := (p10_Zjoint_meas β).comp_aemeasurable
      (measurable_snd.aemeasurable.prodMk hQ1)
    exact (hW1.mul hZ).aestronglyMeasurable
  have hsγ : 0 < Real.sqrt γ := Real.sqrt_pos.2 hγ
  set Cq := max (Real.sqrt K / cE) 1 with hCqdef
  set A := (Real.sqrt γ)⁻¹ * Q * Cq with hAdef
  set D := Real.sqrt (K * γ) / cE with hDdef
  have hCq0 : 0 ≤ Cq := le_trans zero_le_one (le_max_right _ _)
  have hD0 : 0 ≤ D := div_nonneg (Real.sqrt_nonneg _) hcE.le
  have hmaj : IntegrableOn (fun m : ℝ => A * (1 / Real.sqrt m + D)) J := by
    have hinv := (wmi_inv_sqrt hγ).1
    have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) J :=
      integrableOn_const (by simp [J, hγ.le])
    change Integrable (fun m : ℝ => A * (1 / Real.sqrt m + D)) (volume.restrict J)
    convert (hinv.add (hone.const_mul D)).const_mul A using 1
    funext m
    simp
  have hint : IntegrableOn
      (fun m => |Wpart β (B n) (plSpec α (c n) (N n)) i m| * Real.sqrt (Qm β m)) J := by
    refine Integrable.mono' hmaj (hWm.norm.mul
      (Real.continuous_sqrt.measurable.comp_aemeasurable hQm).aestronglyMeasurable) ?_
    rw [ae_restrict_iff' hJm]
    refine Filter.Eventually.of_forall fun m hm => ?_
    obtain ⟨hq0, hqQ⟩ := hq m hm
    have hQ0 : 0 ≤ Q := hq0.trans hqQ
    have hm0 := hm.1
    have hmγ := hm.2
    have hEp : 0 < Efun β m :=
      lt_of_lt_of_le (mul_pos hcE (lt_min hm0 one_pos)) (hE m hm0).1
    have hQpos := (vsh_Qm R.hβ0 R.hβ1 hm0).1
    have hWform := vsh_W_eq (α := α) (β := β) (R.hNpos n) (R.hBpos n)
      (R.hcpos n) i hm
    have hgt0 : 0 ≤ gRow (B n) (plSpec α (c n) (N n)) i m *
        thetaN β (B n) (plSpec α (c n) (N n)) m := by
      have : gRow (B n) (plSpec α (c n) (N n)) i m *
          (thetaN β (B n) (plSpec α (c n) (N n)) m * Efun β m) =
          (gRow (B n) (plSpec α (c n) (N n)) i m *
            thetaN β (B n) (plSpec α (c n) (N n)) m) * Efun β m := by ring
      rw [this] at hq0
      by_contra hneg
      have := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hEp
      nlinarith
    rw [show gammaOf (N n) (B n) = γ from hγdef.symm] at hWform
    have hW0 : 0 ≤ Wpart β (B n) (plSpec α (c n) (N n)) i m := by
      rw [hWform]
      rw [show (Real.sqrt γ)⁻¹ * gRow (B n) (plSpec α (c n) (N n)) i m *
          thetaN β (B n) (plSpec α (c n) (N n)) m =
        (Real.sqrt γ)⁻¹ * (gRow (B n) (plSpec α (c n) (N n)) i m *
          thetaN β (B n) (plSpec α (c n) (N n)) m) by ring]
      exact mul_nonneg (inv_nonneg.2 hsγ.le) hgt0
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)),
      abs_of_nonneg hW0, hWform]
    have hQE : Real.sqrt (Qm β m) / Efun β m ≤
        Cq * (1 / Real.sqrt m + D) := by
      rcases le_total m 1 with hm1 | h1m
      · have hsq : Real.sqrt (Qm β m) ≤ Real.sqrt K * Real.sqrt m := by
          rw [← Real.sqrt_mul hK0.le]
          exact Real.sqrt_le_sqrt (hK m hm)
        have hElow : cE * m ≤ Efun β m := by
          have hmin : min m 1 = m := min_eq_left hm1
          simpa [hmin] using (hE m hm0).1
        have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
        have hc : 0 < cE := hcE
        calc
          Real.sqrt (Qm β m) / Efun β m ≤
              (Real.sqrt K * Real.sqrt m) / Efun β m :=
            div_le_div_of_nonneg_right hsq hEp.le
          _ ≤ (Real.sqrt K * Real.sqrt m) / (cE * m) :=
            div_le_div_of_nonneg_left (by positivity) (mul_pos hc hm0) hElow
          _ = Real.sqrt K / cE * (1 / Real.sqrt m) := by
            have hsm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
            field_simp
            nlinarith
          _ ≤ Cq * (1 / Real.sqrt m + D) := by
            calc
              Real.sqrt K / cE * (1 / Real.sqrt m) ≤ Cq * (1 / Real.sqrt m) :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
              _ ≤ Cq * (1 / Real.sqrt m + D) :=
                mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hD0) hCq0
      · have hQγ : Qm β m ≤ K * γ := (hK m hm).trans
            (mul_le_mul_of_nonneg_left hmγ.le hK0.le)
        have hElow : cE ≤ Efun β m := by
          have hmin : min m 1 = 1 := min_eq_right h1m
          simpa [hmin] using (hE m hm0).1
        calc
          Real.sqrt (Qm β m) / Efun β m ≤
              Real.sqrt (K * γ) / Efun β m :=
            div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hQγ) hEp.le
          _ ≤ Real.sqrt (K * γ) / cE :=
            div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hcE hElow
          _ = D := by rw [hDdef]
          _ ≤ Cq * (1 / Real.sqrt m + D) := by
            have hcoef : 1 ≤ Cq := le_max_right _ _
            have hsum : D ≤ 1 / Real.sqrt m + D := by
              linarith [show 0 ≤ 1 / Real.sqrt m by positivity]
            exact hsum.trans (le_mul_of_one_le_left (by positivity) hcoef)
    have heq : (Real.sqrt γ)⁻¹ *
        (gRow (B n) (plSpec α (c n) (N n)) i m *
          thetaN β (B n) (plSpec α (c n) (N n)) m) * Real.sqrt (Qm β m) =
        (Real.sqrt γ)⁻¹ *
          (gRow (B n) (plSpec α (c n) (N n)) i m *
            (thetaN β (B n) (plSpec α (c n) (N n)) m * Efun β m)) *
              (Real.sqrt (Qm β m) / Efun β m) := by
      field_simp
    rw [show (Real.sqrt γ)⁻¹ * gRow (B n) (plSpec α (c n) (N n)) i m *
        thetaN β (B n) (plSpec α (c n) (N n)) m * Real.sqrt (Qm β m) =
      (Real.sqrt γ)⁻¹ * (gRow (B n) (plSpec α (c n) (N n)) i m *
        thetaN β (B n) (plSpec α (c n) (N n)) m) * Real.sqrt (Qm β m) by ring,
      heq, hAdef]
    calc
      (Real.sqrt γ)⁻¹ *
          (gRow (B n) (plSpec α (c n) (N n)) i m *
            (thetaN β (B n) (plSpec α (c n) (N n)) m * Efun β m)) *
            (Real.sqrt (Qm β m) / Efun β m) ≤
          ((Real.sqrt γ)⁻¹ * Q) * (Cq * (1 / Real.sqrt m + D)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hqQ (inv_nonneg.2 hsγ.le)) hQE
          (div_nonneg (Real.sqrt_nonneg _) hEp.le)
          (mul_nonneg (inv_nonneg.2 hsγ.le) hQ0)
      _ = (Real.sqrt γ)⁻¹ * Q * Cq * (1 / Real.sqrt m + D) := by ring
  exact ⟨by simpa [J, γ] using hint, by simpa [J, γ] using hWm,
    by simpa [J, γ] using hprod⟩

/-- Minkowski's integral inequality in `L²(N(0,1))`: `‖∫_S F(m,·) dm‖_{L²} ≤ ∫_S ‖F(m,·)‖_{L²} dm`
(task L-G.7b; proof step of `lem:app-pl-vector`, l.1952-1954; snapshot cr-2026-10-23). -/
private lemma p10_l2_lintegral (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f (gaussianReal 0 1))
    (hsq : Integrable (fun g => f g ^ 2) (gaussianReal 0 1)) :
    (∫⁻ g, ENNReal.ofReal |f g| ^ (2 : ℝ) ∂(gaussianReal 0 1)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (l2Norm f) := by
  have heq : (fun g => ENNReal.ofReal |f g| ^ (2 : ℝ)) =
      fun g => ENNReal.ofReal (f g ^ 2) := by
    funext g
    rw [ENNReal.ofReal_rpow_of_nonneg (p := (2 : ℝ)) (abs_nonneg (f g)) (by norm_num),
      Real.rpow_two, sq_abs]
  rw [heq]
  rw [← ofReal_integral_eq_lintegral_ofReal hsq
    (ae_of_all _ fun g => sq_nonneg (f g))]
  rw [l2Norm, Real.sqrt_eq_rpow,
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun g => sq_nonneg (f g)) (by norm_num)]

private lemma p10_lintegral_abs_le_l2 (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f (gaussianReal 0 1))
    (hsq : Integrable (fun g => f g ^ 2) (gaussianReal 0 1)) :
    (∫⁻ g, ENNReal.ofReal |f g| ∂(gaussianReal 0 1)) ≤ ENNReal.ofReal (l2Norm f) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (p := (2 : ℝ)) (q := (2 : ℝ))
    (f := fun g => ENNReal.ofReal |f g|) (g := fun _ : ℝ => 1) (gaussianReal 0 1)
    (Real.holderConjugate_iff.mpr (by norm_num : 1 < (2 : ℝ) ∧ (2 : ℝ)⁻¹ + 2⁻¹ = 1))
    hf.norm.aemeasurable.ennreal_ofReal aemeasurable_const
  rw [← p10_l2_lintegral f hf hsq]
  simpa [one_div] using h

private lemma p10_sections_integrable (S : Set ℝ) (F : ℝ → ℝ → ℝ)
    (hF : AEStronglyMeasurable (fun q : ℝ × ℝ => F q.1 q.2)
      ((volume.restrict S).prod (gaussianReal 0 1)))
    (hsq : ∀ᵐ m ∂(volume.restrict S), Integrable (fun g => F m g ^ 2) (gaussianReal 0 1))
    (hint : IntegrableOn (fun m => l2Norm (F m)) S) :
    ∀ᵐ g ∂(gaussianReal 0 1), IntegrableOn (fun m => F m g) S := by
  let μ := volume.restrict S
  let ν := gaussianReal 0 1
  have hf : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal |F q.1 q.2|) (μ.prod ν) :=
    hF.norm.aemeasurable.ennreal_ofReal
  have hinner : ∀ᵐ m ∂μ,
      (∫⁻ g, ENNReal.ofReal |F m g| ∂ν) ≤ ENNReal.ofReal (l2Norm (F m)) := by
    filter_upwards [hF.prodMk_left, hsq] with m hm hsm
    exact p10_lintegral_abs_le_l2 (F m) hm hsm
  have hright : (∫⁻ m, ENNReal.ofReal (l2Norm (F m)) ∂μ) < ⊤ := by
    simpa [μ, l2Norm, Real.enorm_of_nonneg] using
      (hasFiniteIntegral_iff_enorm.mp hint.hasFiniteIntegral)
  have htotal : (∫⁻ g, ∫⁻ m, ENNReal.ofReal |F m g| ∂μ ∂ν) < ⊤ := by
    rw [← lintegral_lintegral_swap hf]
    exact (lintegral_mono_ae hinner).trans_lt hright
  filter_upwards [hF.prodMk_right,
    ae_lt_top' hf.lintegral_prod_left' htotal.ne] with g hmg hg
  exact ⟨hmg, by simpa [hasFiniteIntegral_iff_enorm, ← ofReal_norm] using hg⟩

private lemma p10_lintegral_mul_abs_le_l2 (f g : ℝ → ℝ)
    (hf : AEStronglyMeasurable f (gaussianReal 0 1))
    (hg : AEStronglyMeasurable g (gaussianReal 0 1))
    (hsf : Integrable (fun x => f x ^ 2) (gaussianReal 0 1))
    (hsg : Integrable (fun x => g x ^ 2) (gaussianReal 0 1)) :
    (∫⁻ x, ENNReal.ofReal |f x| * ENNReal.ofReal |g x| ∂(gaussianReal 0 1)) ≤
      ENNReal.ofReal (l2Norm f) * ENNReal.ofReal (l2Norm g) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (p := (2 : ℝ)) (q := (2 : ℝ))
    (f := fun x => ENNReal.ofReal |f x|) (g := fun x => ENNReal.ofReal |g x|)
    (gaussianReal 0 1)
    (Real.holderConjugate_iff.mpr (by norm_num : 1 < (2 : ℝ) ∧ (2 : ℝ)⁻¹ + 2⁻¹ = 1))
    hf.norm.aemeasurable.ennreal_ofReal hg.norm.aemeasurable.ennreal_ofReal
  rw [← p10_l2_lintegral f hf hsf, ← p10_l2_lintegral g hg hsg]
  simpa only [Pi.mul_apply, one_div] using h

private lemma p10_minkowski_lintegral (S : Set ℝ) (F : ℝ → ℝ → ℝ)
    (hF : StronglyMeasurable (fun q : ℝ × ℝ => F q.1 q.2))
    (hsq : ∀ᵐ m ∂(volume.restrict S), Integrable (fun g => F m g ^ 2) (gaussianReal 0 1)) :
    (∫⁻ g, (∫⁻ m in S, ENNReal.ofReal |F m g|) ^ (2 : ℝ) ∂(gaussianReal 0 1)) ≤
      (∫⁻ m in S, ENNReal.ofReal (l2Norm (F m))) ^ (2 : ℝ) := by
  let μ := volume.restrict S
  let ν := gaussianReal 0 1
  let f : ℝ × ℝ → ENNReal := fun q => ENNReal.ofReal |F q.1 q.2|
  have hf : Measurable f := hF.norm.measurable.ennreal_ofReal
  let q : (ℝ × ℝ) × ℝ → ENNReal := fun z => f (z.1.1, z.2) * f (z.1.2, z.2)
  have hq : Measurable q := by
    dsimp [q]
    fun_prop
  have ha : Measurable (fun m => ENNReal.ofReal (l2Norm (F m))) := by
    unfold l2Norm
    exact ((hF.pow 2).integral_prod_right' (ν := gaussianReal 0 1)).measurable.sqrt.ennreal_ofReal
  have hpow : ∀ g, (∫⁻ m, f (m, g) ∂μ) ^ (2 : ℝ) =
      ∫⁻ z : ℝ × ℝ, q (z, g) ∂(μ.prod μ) := by
    intro g
    rw [ENNReal.rpow_two, pow_two, ← lintegral_lintegral_mul
      (f := fun m => f (m, g)) (g := fun m => f (m, g))
      (hf.comp (by fun_prop : Measurable (fun m => (m, g)))).aemeasurable
      (hf.comp (by fun_prop : Measurable (fun m => (m, g)))).aemeasurable,
      lintegral_lintegral]
    exact (hq.comp (by fun_prop : Measurable (fun z : ℝ × ℝ => (z, g)))).aemeasurable
  rw [show (∫⁻ g, (∫⁻ m, f (m, g) ∂μ) ^ (2 : ℝ) ∂ν) =
      ∫⁻ g, ∫⁻ z : ℝ × ℝ, q (z, g) ∂(μ.prod μ) ∂ν by
        exact lintegral_congr hpow]
  rw [lintegral_lintegral_swap (μ := ν) (ν := μ.prod μ) (f := fun g z => q (z, g))
    (hq.comp (by fun_prop : Measurable (fun z : ℝ × (ℝ × ℝ) => (z.2, z.1)))).aemeasurable]
  calc
    (∫⁻ z : ℝ × ℝ, ∫⁻ g, q (z, g) ∂ν ∂(μ.prod μ)) ≤
        ∫⁻ z : ℝ × ℝ,
          ENNReal.ofReal (l2Norm (F z.1)) * ENNReal.ofReal (l2Norm (F z.2)) ∂(μ.prod μ) := by
      apply lintegral_mono_ae
      filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hsq,
        (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hsq] with z hz1 hz2
      exact p10_lintegral_mul_abs_le_l2 (F z.1) (F z.2)
        (by simpa [Function.comp_def] using
          (hF.comp_measurable
            (show Measurable (fun g : ℝ => (z.1, g)) from
              measurable_const.prodMk measurable_id)).aestronglyMeasurable)
        (by simpa [Function.comp_def] using
          (hF.comp_measurable
            (show Measurable (fun g : ℝ => (z.2, g)) from
              measurable_const.prodMk measurable_id)).aestronglyMeasurable)
        hz1 hz2
    _ = (∫⁻ m, ENNReal.ofReal (l2Norm (F m)) ∂μ) ^ (2 : ℝ) := by
      rw [ENNReal.rpow_two, pow_two, lintegral_prod_mul
        (f := fun m => ENNReal.ofReal (l2Norm (F m)))
        (g := fun m => ENNReal.ofReal (l2Norm (F m))) (μ := μ) (ν := μ)]
      · exact ha.aemeasurable
      · exact ha.aemeasurable

theorem l2_minkowski_integral (S : Set ℝ) (hS : MeasurableSet S) (F : ℝ → ℝ → ℝ)
    (hF : AEStronglyMeasurable (fun q : ℝ × ℝ => F q.1 q.2)
      ((volume.restrict S).prod (gaussianReal 0 1)))
    (hsq : ∀ᵐ m ∂(volume.restrict S), Integrable (fun g => F m g ^ 2) (gaussianReal 0 1))
    (hint : IntegrableOn (fun m => l2Norm (F m)) S) :
    (∀ᵐ g ∂(gaussianReal 0 1), IntegrableOn (fun m => F m g) S) ∧
    Integrable (fun g => (∫ m in S, F m g) ^ 2) (gaussianReal 0 1) ∧
      l2Norm (fun g => ∫ m in S, F m g) ≤ ∫ m in S, l2Norm (F m) := by
  let μ := volume.restrict S
  let ν := gaussianReal 0 1
  let G : ℝ × ℝ → ℝ := hF.mk (fun q : ℝ × ℝ => F q.1 q.2)
  have hG : StronglyMeasurable G := hF.stronglyMeasurable_mk
  have hm_eq : ∀ᵐ m ∂μ, F m =ᵐ[ν] fun g => G (m, g) :=
    Measure.ae_ae_of_ae_prod hF.ae_eq_mk
  have heqswap : (fun z : ℝ × ℝ => F z.2 z.1) =ᵐ[ν.prod μ]
      fun z => G (z.2, z.1) :=
    (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae_eq_comp
      hF.ae_eq_mk
  have hg_eq : ∀ᵐ g ∂ν, (fun m => F m g) =ᵐ[μ] fun m => G (m, g) :=
    Measure.ae_ae_of_ae_prod heqswap
  have hsqG : ∀ᵐ m ∂μ, Integrable (fun g => G (m, g) ^ 2) ν := by
    filter_upwards [hsq, hm_eq] with m hsm hm
    exact hsm.congr (hm.pow_const 2)
  have hl2eq : (fun m => l2Norm (F m)) =ᵐ[μ] fun m => l2Norm (fun g => G (m, g)) := by
    filter_upwards [hm_eq] with m hm
    unfold l2Norm
    congr 1
    simpa [ν] using integral_congr_ae (μ := ν) (hm.pow_const 2)
  have hcoreG := p10_minkowski_lintegral S (fun m g => G (m, g)) hG hsqG
  have hcore :
      (∫⁻ g, (∫⁻ m in S, ENNReal.ofReal |F m g|) ^ (2 : ℝ) ∂ν) ≤
        (∫⁻ m in S, ENNReal.ofReal (l2Norm (F m))) ^ (2 : ℝ) := by
    calc
      (∫⁻ g, (∫⁻ m, ENNReal.ofReal |F m g| ∂μ) ^ (2 : ℝ) ∂ν) =
          ∫⁻ g, (∫⁻ m, ENNReal.ofReal |G (m, g)| ∂μ) ^ (2 : ℝ) ∂ν := by
        apply lintegral_congr_ae
        filter_upwards [hg_eq] with g hg
        rw [lintegral_congr_ae]
        filter_upwards [hg] with m hm
        rw [hm]
      _ ≤ (∫⁻ m, ENNReal.ofReal (l2Norm (fun g => G (m, g))) ∂μ) ^ (2 : ℝ) := hcoreG
      _ = (∫⁻ m, ENNReal.ofReal (l2Norm (F m)) ∂μ) ^ (2 : ℝ) := by
        congr 1
        apply lintegral_congr_ae
        filter_upwards [hl2eq] with m hm
        rw [hm]
  have hsections := p10_sections_integrable S F hF hsq hint
  refine ⟨hsections, ?_⟩
  let I : ℝ → ℝ := fun g => ∫ m in S, F m g
  have hImeas : AEStronglyMeasurable I ν := by
    exact hF.prod_swap.integral_prod_right'
  have hA_top : (∫⁻ m, ENNReal.ofReal (l2Norm (F m)) ∂μ) < ⊤ := by
    simpa [μ, l2Norm, Real.enorm_of_nonneg] using
      (hasFiniteIntegral_iff_enorm.mp hint.hasFiniteIntegral)
  have hpoint : ∀ g, ENNReal.ofReal |I g| ≤
      ∫⁻ m, ENNReal.ofReal |F m g| ∂μ := by
    intro g
    simpa [I, μ, ← ofReal_norm, Real.norm_eq_abs] using
      (enorm_integral_le_lintegral_enorm (μ := μ) (fun m => F m g))
  have hsquare_le :
      (∫⁻ g, ENNReal.ofReal |I g| ^ (2 : ℝ) ∂ν) ≤
        (∫⁻ m, ENNReal.ofReal (l2Norm (F m)) ∂μ) ^ (2 : ℝ) := by
    exact (lintegral_mono fun g => ENNReal.rpow_le_rpow (hpoint g) (by norm_num)).trans hcore
  have hsquare_top : (∫⁻ g, ENNReal.ofReal |I g| ^ (2 : ℝ) ∂ν) < ⊤ :=
    hsquare_le.trans_lt (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hA_top.ne)
  have hIsq : Integrable (fun g => I g ^ 2) ν := by
    refine ⟨hImeas.pow 2, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    convert hsquare_top using 1
    apply lintegral_congr
    intro g
    rw [← ofReal_norm, Real.norm_eq_abs,
      ENNReal.ofReal_rpow_of_nonneg (p := (2 : ℝ)) (abs_nonneg (I g)) (by norm_num),
      Real.rpow_two, sq_abs, abs_of_nonneg (sq_nonneg (I g))]
  have hAeq : (∫⁻ m, ENNReal.ofReal (l2Norm (F m)) ∂μ) =
      ENNReal.ofReal (∫ m in S, l2Norm (F m)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun m => Real.sqrt_nonneg _)]
  have hsqrt := ENNReal.rpow_le_rpow hsquare_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hnorm : l2Norm I ≤ ∫ m in S, l2Norm (F m) := by
    apply (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun m => Real.sqrt_nonneg _)).mp
    rw [← p10_l2_lintegral I hImeas hIsq]
    change _ ≤ ENNReal.ofReal (∫ m in S, l2Norm (F m))
    rw [← hAeq]
    simpa only [ν, ← ENNReal.rpow_mul, one_div,
      mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_one] using hsqrt
  exact ⟨by simpa [I, ν] using hIsq, by simpa [I] using hnorm⟩

private lemma p10_abs_rpow_integrableOn :
    IntegrableOn (fun x : ℝ => |x| ^ (-1 / 2 : ℝ)) (Icc (-1) 1) volume := by
  have hpint : IntervalIntegrable (fun x : ℝ => x ^ (-1 / 2 : ℝ)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hp : IntegrableOn (fun x : ℝ => |x| ^ (-1 / 2 : ℝ)) (Icc 0 1) volume := by
    refine ((intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).1 hpint).congr_fun ?_
      measurableSet_Icc
    intro x hx
    simpa [abs_of_nonneg hx.1]
  have hnint : IntervalIntegrable (fun x : ℝ => (-x) ^ (-1 / 2 : ℝ)) volume (-1) 0 := by
    rw [← IntervalIntegrable.symm_iff, IntervalIntegrable.iff_comp_neg]
    simpa using hpint
  have hn : IntegrableOn (fun x : ℝ => |x| ^ (-1 / 2 : ℝ)) (Icc (-1) 0) volume := by
    refine ((intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).1 hnint).congr_fun ?_
      measurableSet_Icc
    intro x hx
    simpa [abs_of_nonpos hx.2]
  have hu := hn.union hp
  rw [show Icc (-1 : ℝ) 0 ∪ Icc 0 1 = Icc (-1) 1 by
    ext x
    simp only [mem_union, mem_Icc]
    constructor
    · rintro (h | h) <;> constructor <;> linarith
    · intro h
      by_cases hx : x ≤ 0
      · left; constructor <;> linarith
      · right; constructor <;> linarith] at hu
  exact hu

private lemma p10_abs_rpow_gaussian_integrable :
    Integrable ((Icc (-1 : ℝ) 1).indicator (fun x => |x| ^ (-1 / 2 : ℝ)))
      (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num),
    integrable_withDensity_iff (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp_rw [toReal_gaussianPDF]
  have hprod : IntegrableOn
      (fun x : ℝ => |x| ^ (-1 / 2 : ℝ) * gaussianPDFReal 0 1 x)
      (Icc (-1) 1) volume := by
    apply p10_abs_rpow_integrableOn.mul_continuousOn _ isCompact_Icc
    apply Continuous.continuousOn
    rw [gaussianPDFReal_def]
    fun_prop
  refine (hprod.integrable_indicator measurableSet_Icc).congr ?_
  filter_upwards with x
  by_cases hx : x ∈ Icc (-1 : ℝ) 1 <;> simp [hx]

private lemma p10_log_abs_sq_bound (g : ℝ) :
    (1 + |Real.log (|g|)|) ^ 2 ≤
      2 + 2 * g ^ 2 + 32 * (Icc (-1 : ℝ) 1).indicator
        (fun x => |x| ^ (-1 / 2 : ℝ)) g := by
  by_cases hg0 : g = 0
  · subst g
    norm_num
  have hxpos : 0 < |g| := abs_pos.mpr hg0
  by_cases hx : |g| ≤ 1
  · have hprod := Real.abs_log_mul_self_rpow_lt |g| (1 / 4 : ℝ) hxpos hx (by norm_num)
    have hpowpos : 0 < |g| ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hxpos _
    have hprod' : |Real.log (|g|)| * |g| ^ (1 / 4 : ℝ) < 4 := by
      rw [abs_mul, abs_of_pos hpowpos] at hprod
      norm_num at hprod ⊢
      exact hprod
    have hlog : |Real.log (|g|)| < 4 / (|g| ^ (1 / 4 : ℝ)) := by
      rw [lt_div_iff₀ hpowpos]
      exact hprod'
    have hsq : |Real.log (|g|)| ^ 2 ≤ (4 / (|g| ^ (1 / 4 : ℝ))) ^ 2 := by
      have hdiv : 0 ≤ 4 / (|g| ^ (1 / 4 : ℝ)) := by positivity
      nlinarith [abs_nonneg (Real.log |g|)]
    have hid : (4 / (|g| ^ (1 / 4 : ℝ))) ^ 2 =
        16 * |g| ^ (-1 / 2 : ℝ) := by
      rw [div_pow]
      norm_num
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hxpos.le]
      norm_num
      rw [div_eq_mul_inv, Real.rpow_neg hxpos.le]
    have hlogsq : |Real.log (|g|)| ^ 2 ≤ 16 * |g| ^ (-1 / 2 : ℝ) := hsq.trans_eq hid
    have hmem : g ∈ Icc (-1 : ℝ) 1 := abs_le.mp hx
    rw [Set.indicator_of_mem hmem]
    nlinarith [sq_nonneg (|Real.log (|g|)| - 1), sq_nonneg g,
      Real.rpow_nonneg (abs_nonneg g) (-1 / 2 : ℝ)]
  · have hx1 : 1 < |g| := lt_of_not_ge hx
    have hlog0 : 0 ≤ Real.log |g| := Real.log_nonneg hx1.le
    have hlogle : Real.log |g| ≤ |g| := by
      exact (Real.log_le_sub_one_of_pos hxpos).trans (by linarith)
    have hnotmem : g ∉ Icc (-1 : ℝ) 1 := by
      intro hmem
      exact hx (abs_le.mpr hmem)
    simp only [Set.indicator, hnotmem, ↓reduceIte, mul_zero, add_zero,
      abs_of_nonneg hlog0]
    nlinarith [sq_nonneg (Real.log |g| - 1), sq_abs g]

/-- The age-factor constant has a finite second moment: `𝔼 (1 + |log|g||)² < ∞` (task L-G.7b; proof step of
`lem:app-pl-vector`, l.1951-1953, "whose constant has a finite second moment in `g`"; snapshot cr-2026-10-23). -/
theorem log_abs_sq_integrable :
    Integrable (fun g : ℝ => (1 + |Real.log (|g|)|) ^ 2) (gaussianReal 0 1) := by
  have hsq : Integrable (fun g : ℝ => g ^ 2) (gaussianReal 0 1) := by
    simpa only [id_eq] using
      (ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
  have hmaj : Integrable (fun g : ℝ =>
      2 + 2 * g ^ 2 + 32 * (Icc (-1 : ℝ) 1).indicator
        (fun x => |x| ^ (-1 / 2 : ℝ)) g) (gaussianReal 0 1) := by
    exact ((integrable_const (c := (2 : ℝ))).add (hsq.const_mul 2)).add
      (p10_abs_rpow_gaussian_integrable.const_mul 32)
  have hmeas : Measurable (fun g : ℝ => (1 + |Real.log (|g|)|) ^ 2) := by
    exact (measurable_const.add ((Real.measurable_log.comp measurable_id.abs).abs)).pow_const 2
  apply hmaj.mono' hmeas.aestronglyMeasurable
  filter_upwards with g
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact p10_log_abs_sq_bound g

private lemma p12_pg6_rowNum_pos {N : ℕ} (i : Fin N) : 0 < rowNum i := by
  unfold rowNum; positivity

private lemma p12_pg6_plSpec_eq {α c : ℝ} {N : ℕ} (i : Fin N) :
    plSpec α c N i = c * rowNum i ^ (-α) := rfl

private lemma p12_pg6_plSpec_pos {α c : ℝ} (hc : 0 < c) {N : ℕ} (i : Fin N) : 0 < plSpec α c N i := by
  rw [p12_pg6_plSpec_eq]; exact mul_pos hc (Real.rpow_pos_of_pos (p12_pg6_rowNum_pos i) _)

private lemma p12_pg6_gamma_pos {N B : ℕ} (hB : 0 < B) (hN : 0 < N) : 0 < gammaOf N B := by
  unfold gammaOf
  have : (0 : ℝ) < N := by exact_mod_cast hN
  have : (0 : ℝ) < B := by exact_mod_cast hB
  positivity

private lemma p12_pg6p2_Lam_hasDeriv {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    0 < partLam B μ m ∧ HasDerivAt (partLam B μ) (deriv (partLam B μ) m) m := by
  obtain ⟨-, hb2, -, hcd⟩ := def_app_pl_participation_bij μ hB hN hpos
  refine ⟨hb2.mapsTo hm, ?_⟩
  have hca := hcd.contDiffAt (Ioo_mem_nhds hm.1 hm.2)
  exact (hca.differentiableAt (by simp)).hasDerivAt

private lemma p12_pg6p2_W_deriv {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (i : Fin N) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    0 < partBfun B μ i m ∧
    HasDerivAt (partBfun B μ i)
      (partBfun B μ i m * (-(1 / (2 * (gammaOf N B - m))) - 1 / (2 * m) +
        (1 / 2 - partF B μ i m) * (deriv (partLam B μ) m / partLam B μ m))) m := by
  obtain ⟨hL, hLd⟩ := p12_pg6p2_Lam_hasDeriv μ hB hN hpos hm
  obtain ⟨hm0, hmg⟩ := hm
  have hgm : 0 < gammaOf N B - m := sub_pos.2 hmg
  have hmu := hpos i
  set L := partLam B μ m with hLdef
  set L' := deriv (partLam B μ) m with hL'def
  set γ := gammaOf N B with hγ
  have hden : 0 < m * L := mul_pos hm0 hL
  set u := (γ - m) / (m * L) with hu
  have hu0 : 0 < u := div_pos hgm hden
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.2 hu0
  have hsq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0.le
  have hfL : 0 < 1 + L * μ i := by have := mul_pos hL hmu; linarith
  -- derivatives
  have hd1 : HasDerivAt (fun y : ℝ => γ - y) (-1) m := by
    simpa using (hasDerivAt_id m).const_sub γ
  have hd2 : HasDerivAt (fun y : ℝ => y * partLam B μ y) (L + m * L') m := by
    exact ((hasDerivAt_id' m).mul hLd).congr_deriv (by ring)
  have hdu : HasDerivAt (fun y : ℝ => (γ - y) / (y * partLam B μ y))
      ((-1 * (m * L) - (γ - m) * (L + m * L')) / (m * L) ^ 2) m := hd1.div hd2 hden.ne'
  have hds : HasDerivAt (fun y : ℝ => Real.sqrt ((γ - y) / (y * partLam B μ y)))
      (((-1 * (m * L) - (γ - m) * (L + m * L')) / (m * L) ^ 2) / (2 * Real.sqrt u)) m :=
    hdu.sqrt hu0.ne'
  have hdf : HasDerivAt (fun y : ℝ => partLam B μ y * μ i / (1 + partLam B μ y * μ i))
      ((L' * μ i * (1 + L * μ i) - L * μ i * (L' * μ i)) / (1 + L * μ i) ^ 2) m := by
    have h1 : HasDerivAt (fun y : ℝ => partLam B μ y * μ i) (L' * μ i) m := hLd.mul_const _
    have h2 : HasDerivAt (fun y : ℝ => 1 + partLam B μ y * μ i) (L' * μ i) m := h1.const_add 1
    exact h1.div h2 hfL.ne'
  have hW : HasDerivAt (partBfun B μ i)
      ((((-1 * (m * L) - (γ - m) * (L + m * L')) / (m * L) ^ 2) / (2 * Real.sqrt u)) *
          (L * μ i / (1 + L * μ i)) +
        Real.sqrt u * ((L' * μ i * (1 + L * μ i) - L * μ i * (L' * μ i)) / (1 + L * μ i) ^ 2)) m :=
    hds.mul hdf
  have hWm : partBfun B μ i m = Real.sqrt u * (L * μ i / (1 + L * μ i)) := rfl
  have hfpos : 0 < L * μ i / (1 + L * μ i) := div_pos (mul_pos hL hmu) hfL
  refine ⟨by rw [hWm]; positivity, ?_⟩
  refine hW.congr_deriv ?_
  have hF : partF B μ i m = L * μ i / (1 + L * μ i) := rfl
  rw [hWm, hF]
  have hm0' : m ≠ 0 := hm0.ne'
  have hL0 : L ≠ 0 := hL.ne'
  have hg0 : γ - m ≠ 0 := hgm.ne'
  have hs0 : Real.sqrt u ≠ 0 := hsu.ne'
  have hfL0 : 1 + L * μ i ≠ 0 := hfL.ne'
  have hsq2 : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0.le
  field_simp
  rw [hsq2, hu]
  field_simp
  ring

private lemma p12_pg6p2_W_facts {α : ℝ} (hα : 0 < α) :
    ∃ C4 : ℝ, 0 < C4 ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → ∀ i : Fin N,
      ∀ m ∈ Ioo 0 (gammaOf N B),
        0 < partBfun B (plSpec α c N) i m ∧
        HasDerivAt (partBfun B (plSpec α c N) i)
          (deriv (partBfun B (plSpec α c N) i) m) m ∧
        |deriv (partBfun B (plSpec α c N) i) m| ≤
          C4 * partBfun B (plSpec α c N) i m * (1 / m + 1 / (gammaOf N B - m)) := by
  obtain ⟨cα, hcα, hel⟩ := lem_app_pl_elasticity_i hα
  refine ⟨1 / 2 + 1 / (2 * cα), by positivity, fun N B c hN hB hc i m hm => ?_⟩
  have hpos : ∀ j, 0 < plSpec α c N j := fun j => p12_pg6_plSpec_pos hc j
  obtain ⟨hW0, hWd⟩ := p12_pg6p2_W_deriv (plSpec α c N) hB hN hpos i hm
  refine ⟨hW0, hWd.differentiableAt.hasDerivAt, ?_⟩
  rw [hWd.deriv]
  obtain ⟨-, hlam⟩ := (hel N B c hN hB hc)
  obtain ⟨hl1, hl2⟩ := hlam m hm
  obtain ⟨hL, -⟩ := p12_pg6p2_Lam_hasDeriv (plSpec α c N) hB hN hpos hm
  obtain ⟨hm0, hmg⟩ := hm
  have hgm : 0 < gammaOf N B - m := sub_pos.2 hmg
  set W := partBfun B (plSpec α c N) i m with hWdef
  set r := deriv (partLam B (plSpec α c N)) m / partLam B (plSpec α c N) m with hr
  set f := partF B (plSpec α c N) i m with hf
  have hf0 : 0 < f := by
    rw [hf]; unfold partF
    have := hpos i
    positivity
  have hf1 : f < 1 := by
    rw [hf]; unfold partF
    have := mul_pos hL (hpos i)
    rw [div_lt_one (by linarith)]
    linarith
  have hr0 : 0 ≤ r := by
    have : 0 < 1 / m := by positivity
    linarith
  have hrb : r ≤ (1 / cα) * (1 / m + 1 / (gammaOf N B - m)) := hl2
  have e1 : 0 < 1 / (2 * (gammaOf N B - m)) := by positivity
  have e2 : 0 < 1 / (2 * m) := by positivity
  have h3 : |(1 / 2 - f) * r| ≤ r / 2 := by
    rw [abs_mul, abs_of_nonneg hr0]
    have : |1 / 2 - f| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
    nlinarith
  have habs : |-(1 / (2 * (gammaOf N B - m))) - 1 / (2 * m) + (1 / 2 - f) * r| ≤
      1 / (2 * (gammaOf N B - m)) + 1 / (2 * m) + r / 2 := by
    have := abs_le.1 h3
    rw [abs_le]
    constructor <;> linarith
  rw [abs_mul, abs_of_pos hW0]
  have hb : 1 / (2 * (gammaOf N B - m)) + 1 / (2 * m) + r / 2 ≤
      (1 / 2 + 1 / (2 * cα)) * (1 / m + 1 / (gammaOf N B - m)) := by
    have h1 : 1 / (2 * (gammaOf N B - m)) = 1 / 2 * (1 / (gammaOf N B - m)) := by
      rw [one_div_mul_one_div]
    have h2 : 1 / (2 * m) = 1 / 2 * (1 / m) := by rw [one_div_mul_one_div]
    rw [h1, h2]
    have h4 : r / 2 ≤ 1 / (2 * cα) * (1 / m + 1 / (gammaOf N B - m)) := by
      have : r / 2 ≤ (1 / cα) * (1 / m + 1 / (gammaOf N B - m)) / 2 := by linarith
      calc r / 2 ≤ _ := this
        _ = 1 / (2 * cα) * (1 / m + 1 / (gammaOf N B - m)) := by field_simp
    nlinarith
  calc W * |-(1 / (2 * (gammaOf N B - m))) - 1 / (2 * m) + (1 / 2 - f) * r| ≤
        W * ((1 / 2 + 1 / (2 * cα)) * (1 / m + 1 / (gammaOf N B - m))) :=
        mul_le_mul_of_nonneg_left (habs.trans hb) hW0.le
    _ = _ := by ring

private lemma p12_pg6p2_exp_le {L : ℝ} (hL0 : 0 ≤ L) (hL1 : L ≤ 1) : Real.exp L ≤ (1 + L) ^ 2 := by
  rcases hL0.eq_or_lt with h | h
  · rw [← h]; simp
  have hx : L / 2 < 1 := by linarith
  have h1 := Real.exp_bound_div_one_sub_of_interval' (by linarith : 0 < L / 2) hx
  have h2 : 1 / (1 - L / 2) ≤ 1 + L := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h3 : Real.exp L = Real.exp (L / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h3]
  have := Real.exp_pos (L / 2)
  exact pow_le_pow_left₀ this.le (h1.le.trans h2) 2

private lemma p12_pg6p2_sqrt_ratio {r L : ℝ} (hr : 0 < r) (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (hlog : |Real.log r| ≤ L) : Real.sqrt r ≤ 1 + L ∧ 1 / Real.sqrt r ≤ 1 + L := by
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  have hup : r ≤ Real.exp L := by
    have := (abs_le.1 hlog).2
    calc r = Real.exp (Real.log r) := (Real.exp_log hr).symm
      _ ≤ Real.exp L := Real.exp_le_exp.2 this
  have hlo : Real.exp (-L) ≤ r := by
    have := (abs_le.1 hlog).1
    calc Real.exp (-L) ≤ Real.exp (Real.log r) := Real.exp_le_exp.2 this
      _ = r := Real.exp_log hr
  have hE := p12_pg6p2_exp_le hL0 hL1
  constructor
  · by_contra hnot
    push_neg at hnot
    have : (1 + L) ^ 2 < Real.sqrt r ^ 2 := by
      exact pow_lt_pow_left₀ hnot (by linarith) two_ne_zero
    rw [hsq] at this
    linarith
  · rw [div_le_iff₀ hs]
    by_contra hnot
    push_neg at hnot
    have h1 : 0 < 1 + L := by linarith
    -- 1 > (1+L) s  ⇒ r < 1/(1+L)^2 ≤ exp(-L)
    have h2 : (1 + L) ^ 2 * r < 1 := by
      have : ((1 + L) * Real.sqrt r) ^ 2 < 1 := by
        have h0 : 0 ≤ (1 + L) * Real.sqrt r := by positivity
        nlinarith
      nlinarith [hsq]
    have h3 : Real.exp L * Real.exp (-L) = 1 := by rw [← Real.exp_add]; simp
    have h4 : (1 + L) ^ 2 * Real.exp (-L) ≥ 1 := by
      have hpos : 0 < Real.exp (-L) := Real.exp_pos _
      nlinarith [mul_le_mul_of_nonneg_right hE hpos.le]
    nlinarith [mul_le_mul_of_nonneg_left hlo (by positivity : (0:ℝ) ≤ (1 + L) ^ 2)]

private lemma p12_pg6p2_g_ratio {V V' y q L : ℝ} (hV : 0 < V) (hV' : 0 < V') (hy : 0 ≤ y) (hq : 0 ≤ q)
    (hL0 : 0 ≤ L) (hL1 : L ≤ 1) (hlog : |Real.log (V / V')| ≤ L) :
    |Real.sqrt (q / V) * (V / (V + y)) - Real.sqrt (q / V') * (V' / (V' + y))| ≤
      L * (Real.sqrt (q / V') * (V' / (V' + y))) := by
  set r := V / V' with hr
  have hr0 : 0 < r := div_pos hV hV'
  have hVr : V = r * V' := by rw [hr]; field_simp
  obtain ⟨hs1, hs2⟩ := p12_pg6p2_sqrt_ratio hr0 hL0 hL1 hlog
  set s := Real.sqrt r with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hr0
  have hss : s ^ 2 = r := Real.sq_sqrt hr0.le
  set G := Real.sqrt (q / V') * (V' / (V' + y)) with hG
  have hG0 : 0 ≤ G := by positivity
  have hgV : Real.sqrt (q / V) * (V / (V + y)) = G * (s * (V' + y) / (s ^ 2 * V' + y)) := by
    have e1 : Real.sqrt (q / V) = Real.sqrt (q / V') / s := by
      rw [hVr, mul_comm, ← div_div, Real.sqrt_div (by positivity)]
    rw [e1, hG, hVr, ← hss]
    have : 0 < V' + y := by linarith
    have : 0 < s ^ 2 * V' + y := by positivity
    have : 0 < s := hs0
    field_simp
  set ρ := s * (V' + y) / (s ^ 2 * V' + y) with hρ
  have hden : 0 < s ^ 2 * V' + y := by positivity
  have hden2 : 0 < V' + y := by linarith
  have hρup : ρ ≤ 1 + L := by
    rcases le_total 1 s with h | h
    · have : ρ ≤ s := by
        rw [hρ, div_le_iff₀ hden]
        nlinarith [mul_nonneg hV'.le (sub_nonneg.2 (one_le_pow₀ h : (1:ℝ) ≤ s ^ 2)), hs0]
      linarith
    · have : ρ ≤ 1 / s := by
        rw [hρ, div_le_div_iff₀ hden hs0]
        nlinarith [mul_nonneg hy (sub_nonneg.2 (pow_le_one₀ hs0.le h : s ^ 2 ≤ 1)), hs0]
      linarith
  have hρlo : 1 - L ≤ ρ := by
    have h1 : 1 / (1 + L) ≤ s := by
      rw [div_le_iff₀ (by linarith)]
      rw [div_le_iff₀ hs0] at hs2
      linarith
    have h2 : 1 / (1 + L) ≤ 1 / s := by
      apply one_div_le_one_div_of_le hs0 hs1
    have h3 : 1 / (1 + L) ≤ ρ := by
      rcases le_total 1 s with h | h
      · have : 1 / s ≤ ρ := by
          rw [hρ, div_le_div_iff₀ hs0 hden]
          nlinarith [mul_nonneg hy (sub_nonneg.2 (one_le_pow₀ h : (1:ℝ) ≤ s ^ 2)), hs0]
        linarith
      · have : s ≤ ρ := by
          rw [hρ, le_div_iff₀ hden]
          nlinarith [mul_nonneg hV'.le (sub_nonneg.2 (pow_le_one₀ hs0.le h : s ^ 2 ≤ 1)), hs0]
        linarith
    have h4 : 1 - L ≤ 1 / (1 + L) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    linarith
  rw [hgV]
  have e : G * ρ - G = G * (ρ - 1) := by ring
  rw [e, abs_mul, abs_of_nonneg hG0]
  have : |ρ - 1| ≤ L := by rw [abs_le]; constructor <;> linarith
  nlinarith

private lemma p12_pg6p2_finV_pos {α : ℝ} {N B : ℕ} (c : ℝ) (hN : 0 < N) (hB : 0 < B) (hc : 0 < c)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 < finV α N p := by
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hBr : (0:ℝ) < (B:ℝ) := by exact_mod_cast hB
  have hγ : 0 < gammaOf N B := by unfold gammaOf; exact div_pos hNr hBr
  have hγp : 0 < gammaOf N B * p := mul_pos hγ hp0
  have hmI : gammaOf N B * p ∈ Ioo 0 (gammaOf N B) := ⟨hγp, by nlinarith⟩
  have hpos : ∀ j, 0 < plSpec α c N j := fun j => p12_pg6_plSpec_pos hc j
  have hLpos : 0 < partLam B (plSpec α c N) (gammaOf N B * p) :=
    (def_app_pl_participation_bij (plSpec α c N) hB hN hpos).2.1.mapsTo hmI
  have hLV := eqn_app_pl_Lambda_V (N := N) (B := B) α c hN hB hc hmI
  rw [mul_div_cancel_left₀ p hγ.ne'] at hLV
  have hNα : 0 < (N:ℝ) ^ α := Real.rpow_pos_of_pos hNr α
  have h1 : 0 < (N:ℝ) ^ α / c * finV α N p := hLV ▸ hLpos
  exact pos_of_mul_pos_right h1 (div_pos hNα hc).le

private lemma p12_pg6p2_rowNum_le {N : ℕ} (i : Fin N) : rowNum i ≤ (N : ℝ) := by
  unfold rowNum
  have : ((i : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast i.isLt
  exact this

private lemma p12_pg6p2_aN_pos {α c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 0 < N) : 0 < aN α c N := by
  unfold aN
  have : (0:ℝ) < N := by exact_mod_cast hN
  positivity

private lemma p12_pg6p2_contV_pos {α : ℝ} (hα : 0 < α) {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) :
    0 < contV α p := by
  have hex : ∃ V, V ∈ Ioi (0:ℝ) ∧ contS α V = p := (def_app_pl_profiles_S_bij hα).2.surjOn hp
  exact Function.invFunOn_mem hex

private lemma p12_pg6p2_W_cont {α : ℝ} (hα : 0 < α) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) :
    ContinuousOn (partBfun B (plSpec α c N) i) (Ioo 0 (gammaOf N B)) := by
  obtain ⟨C4, hC4, hW⟩ := p12_pg6p2_W_facts hα
  intro m hm
  exact (hW N B c hN hB hc i m hm).2.1.continuousAt.continuousWithinAt

private lemma p12_pg6p2_S5 {α : ℝ} (hα : 0 < α) :
    ∃ C5 : ℝ, 0 < C5 ∧ ∀ (N B : ℕ) (c : ℝ) (i : Fin N) (M : ℝ), 0 < N → 2 ≤ B → 0 < c → 1 ≤ M →
      2 * M ≤ gammaOf N B → C5 ≤ (B : ℝ) * M →
      (1 - C5 / ((B : ℝ) * M)) *
          ∫ p in (M / gammaOf N B)..(1 - M / gammaOf N B),
            Real.sqrt ((1 - p) / (p * contV α p)) * profF α (rowNum i / (N : ℝ)) p ≤
        (1 / (gammaOf N B * aN α c N)) *
          ∫ m in M..(gammaOf N B - M), partBfun B (plSpec α c N) i m ∧
      (1 / (gammaOf N B * aN α c N)) *
          ∫ m in M..(gammaOf N B - M), partBfun B (plSpec α c N) i m ≤
        (1 + C5 / ((B : ℝ) * M)) *
          ∫ p in (M / gammaOf N B)..(1 - M / gammaOf N B),
            Real.sqrt ((1 - p) / (p * contV α p)) * profF α (rowNum i / (N : ℝ)) p := by
  obtain ⟨C, hC⟩ := lem_app_pl_finite_inverse_ii hα
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun N B c i M hN hB hc hM h2M hCBM => ?_⟩
  set γ := gammaOf N B with hγ
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hBr : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hγ0 : 0 < γ := by rw [hγ]; unfold gammaOf; positivity
  have hM0 : 0 < M := by linarith
  have han : 0 < aN α c N := p12_pg6p2_aN_pos hc hN
  set C5 := max C 1 with hC5
  set L := C5 / ((B : ℝ) * M) with hL
  have hBM : 0 < (B : ℝ) * M := by positivity
  have hL0 : 0 ≤ L := by positivity
  have hL1 : L ≤ 1 := by rw [hL, div_le_one hBM]; exact hCBM
  have ha : 0 < M / γ := by positivity
  have hab : M / γ ≤ 1 - M / γ := by
    have : M / γ ≤ 1 / 2 := by rw [div_le_iff₀ hγ0]; linarith
    linarith
  have hb1 : 1 - M / γ < 1 := by linarith
  set y := (rowNum i / (N : ℝ)) ^ α with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg (div_nonneg (p12_pg6_rowNum_pos i).le hNr.le) _
  -- pointwise
  have hpt : ∀ p ∈ Icc (M / γ) (1 - M / γ),
      (1 - L) * (Real.sqrt ((1 - p) / (p * contV α p)) * profF α (rowNum i / (N : ℝ)) p) ≤
        partBfun B (plSpec α c N) i (γ * p) / aN α c N ∧
      partBfun B (plSpec α c N) i (γ * p) / aN α c N ≤
        (1 + L) * (Real.sqrt ((1 - p) / (p * contV α p)) * profF α (rowNum i / (N : ℝ)) p) := by
    intro p hp
    have hp0 : 0 < p := lt_of_lt_of_le ha hp.1
    have hp1 : p < 1 := lt_of_le_of_lt hp.2 hb1
    have hbulk := eqn_app_pl_Bi_bulk hα c hN (by omega : 0 < B) hc i hp0 hp1
    rw [show ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) = rowNum i / (N : ℝ) from rfl, ← hy] at hbulk
    have hVN : 0 < finV α N p := p12_pg6p2_finV_pos c hN (by omega) hc hp0 hp1
    have hVC : 0 < contV α p := p12_pg6p2_contV_pos hα ⟨hp0, hp1⟩
    have hlog := hC N B M p hN hB hM hp.1 hp.2
    have hlog' : |Real.log (finV α N p / contV α p)| ≤ L := by
      refine hlog.trans ?_
      rw [hL]
      exact div_le_div_of_nonneg_right (le_max_left _ _) hBM.le
    have hq : 0 ≤ (1 - p) / p := div_nonneg (by linarith) hp0.le
    have hrat := p12_pg6p2_g_ratio (V := finV α N p) (V' := contV α p) (y := y) (q := (1 - p) / p) hVN hVC
      hy0 hq hL0 hL1 hlog'
    have e1 : ∀ V : ℝ, Real.sqrt ((1 - p) / (p * V)) = Real.sqrt ((1 - p) / p / V) := fun V => by
      rw [div_div]
    have hW : partBfun B (plSpec α c N) i (γ * p) / aN α c N =
        Real.sqrt ((1 - p) / p / finV α N p) * (finV α N p / (finV α N p + y)) := by
      rw [hbulk, e1]
      field_simp
    rw [hW]
    have hprof : profF α (rowNum i / (N : ℝ)) p = contV α p / (contV α p + y) := rfl
    rw [hprof, e1]
    have := abs_le.1 hrat
    constructor <;> nlinarith [this.1, this.2]
  -- integrals
  have hx01 : rowNum i / (N : ℝ) ∈ Ioc (0:ℝ) 1 :=
    ⟨div_pos (p12_pg6_rowNum_pos i) hNr, (div_le_one hNr).2 (p12_pg6p2_rowNum_le i)⟩
  have hGint : IntervalIntegrable
      (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) * profF α (rowNum i / (N : ℝ)) p)
      volume (M / γ) (1 - M / γ) := by
    refine (lem_app_pl_Psi_i_integrable hα _ hx01).mono_set ?_
    rw [uIcc_of_le zero_le_one, uIcc_of_le hab]
    exact Icc_subset_Icc ha.le (by linarith)
  have hWcont : ContinuousOn (fun p : ℝ => partBfun B (plSpec α c N) i (γ * p) / aN α c N)
      (Icc (M / γ) (1 - M / γ)) := by
    have h1 := p12_pg6p2_W_cont hα hN (by omega : 0 < B) hc i
    refine ContinuousOn.div_const (h1.comp (continuousOn_const.mul continuousOn_id) ?_) _
    intro p hp
    have hp0 : 0 < p := lt_of_lt_of_le ha hp.1
    have hp1 : p < 1 := lt_of_le_of_lt hp.2 hb1
    refine ⟨mul_pos hγ0 hp0, ?_⟩
    show gammaOf N B * p < gammaOf N B
    nlinarith
  have hWint : IntervalIntegrable (fun p : ℝ => partBfun B (plSpec α c N) i (γ * p) / aN α c N)
      volume (M / γ) (1 - M / γ) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hWcont
  -- change of variables
  have hcomp : ∫ p in (M / γ)..(1 - M / γ), partBfun B (plSpec α c N) i (γ * p) =
      γ⁻¹ * ∫ m in M..(γ - M), partBfun B (plSpec α c N) i m := by
    have := intervalIntegral.integral_comp_mul_left (a := M / γ) (b := 1 - M / γ)
      (fun m => partBfun B (plSpec α c N) i m) hγ0.ne'
    rw [this]
    have e1 : γ * (M / γ) = M := by field_simp
    have e2 : γ * (1 - M / γ) = γ - M := by field_simp
    rw [e1, e2, smul_eq_mul]
  have hWeq : ∫ p in (M / γ)..(1 - M / γ), partBfun B (plSpec α c N) i (γ * p) / aN α c N =
      (1 / (γ * aN α c N)) * ∫ m in M..(γ - M), partBfun B (plSpec α c N) i m := by
    rw [intervalIntegral.integral_div, hcomp]
    field_simp
  rw [← hWeq]
  constructor
  · calc (1 - L) * ∫ p in (M / γ)..(1 - M / γ),
          Real.sqrt ((1 - p) / (p * contV α p)) * profF α (rowNum i / (N : ℝ)) p
        = ∫ p in (M / γ)..(1 - M / γ), (1 - L) *
          (Real.sqrt ((1 - p) / (p * contV α p)) * profF α (rowNum i / (N : ℝ)) p) := by
            rw [intervalIntegral.integral_const_mul]
      _ ≤ _ := intervalIntegral.integral_mono_on hab (hGint.const_mul _) hWint
            (fun p hp => (hpt p hp).1)
  · calc ∫ p in (M / γ)..(1 - M / γ), partBfun B (plSpec α c N) i (γ * p) / aN α c N
        ≤ ∫ p in (M / γ)..(1 - M / γ), (1 + L) *
          (Real.sqrt ((1 - p) / (p * contV α p)) * profF α (rowNum i / (N : ℝ)) p) :=
            intervalIntegral.integral_mono_on hab hWint (hGint.const_mul _)
              (fun p hp => (hpt p hp).2)
      _ = _ := by rw [intervalIntegral.integral_const_mul]

private lemma p12_pg6p2_W_top {α : ℝ} (hα : 0 < α) :
    ∃ K6 : ℝ, 0 < K6 ∧ ∀ (N B : ℕ) (c : ℝ) (i : Fin N), 0 < N → 0 < B → 0 < c →
      ∀ m : ℝ, gammaOf N B / 2 ≤ m → m < gammaOf N B →
        partBfun B (plSpec α c N) i m ≤ K6 * aN α c N * ((gammaOf N B - m) / gammaOf N B) := by
  obtain ⟨c3, C3, hc3, hC3, h3⟩ := lem_app_pl_finite_inverse_iii hα
  refine ⟨Real.sqrt (2 / c3), by positivity, fun N B c i hN hB hc m hm1 hm2 => ?_⟩
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
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
  have hV := p12_pg6p2_finV_pos (α := α) c hN hB hc hp0 hp1
  have hVlo := (h3 N hN p hphalf hp1).1
  have han := p12_pg6p2_aN_pos (α := α) hc hN
  have h1p : 0 < 1 - p := by linarith
  have e : (γ - m) / γ = 1 - p := by rw [hp]; field_simp
  rw [e]
  set V := finV α N p with hVdef
  set y := ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg (by positivity) _
  have hfrac : V / (V + y) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hfrac0 : 0 ≤ V / (V + y) := by positivity
  have hsq : Real.sqrt ((1 - p) / (p * V)) ≤ Real.sqrt (2 / c3) * (1 - p) := by
    rw [show Real.sqrt (2 / c3) * (1 - p) = Real.sqrt (2 / c3 * (1 - p) ^ 2) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq h1p.le]]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by positivity)]
    have h4 : c3 / (1 - p) ≤ V := hVlo
    rw [div_le_iff₀ h1p] at h4
    -- (1-p) ≤ p V (1-p)... use p ≥ 1/2: p*V ≥ V/2 ≥ c3/(2(1-p))
    have h5 : c3 ≤ V * (1 - p) := h4
    have h6 : (2 / c3 * (1 - p) ^ 2) * (p * V) = 2 * (1 - p) * (p * (V * (1 - p))) / c3 := by
      field_simp
    rw [h6, le_div_iff₀ hc3]
    nlinarith [mul_pos h1p hp0, mul_nonneg h1p.le hc3.le]
  calc aN α c N * Real.sqrt ((1 - p) / (p * V)) * (V / (V + y))
      ≤ aN α c N * (Real.sqrt (2 / c3) * (1 - p)) * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hsq han.le) hfrac hfrac0 (by positivity)
    _ = _ := by ring

private lemma p12_pg6p2_G_nonneg {α : ℝ} (hα : 0 < α) {x p : ℝ} (hx : 0 < x) (hp : p ∈ Ioo (0:ℝ) 1) :
    0 ≤ Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p := by
  have hV := p12_pg6p2_contV_pos hα hp
  unfold profF
  have : 0 < x ^ α := Real.rpow_pos_of_pos hx _
  have := hp.1
  positivity

private lemma p12_pg6p2_G_top {α : ℝ} (hα : 0 < α) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 0 < x → ∀ p : ℝ, 1 / 2 ≤ p → p < 1 →
      Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ≤ K * (1 - p) := by
  obtain ⟨c3, C3, hc3, hC3, h3⟩ := lem_app_pl_continuum_iii_half hα
  refine ⟨Real.sqrt (2 / c3), by positivity, fun x hx p hphalf hp1 => ?_⟩
  have hp0 : 0 < p := by linarith
  have hV := p12_pg6p2_contV_pos hα ⟨hp0, hp1⟩
  have hVlo := (h3 p hphalf hp1).1
  have h1p : 0 < 1 - p := by linarith
  set V := contV α p with hVdef
  have hy : 0 < x ^ α := Real.rpow_pos_of_pos hx _
  have hfrac : V / (V + x ^ α) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hfrac0 : 0 ≤ V / (V + x ^ α) := by positivity
  have hsq : Real.sqrt ((1 - p) / (p * V)) ≤ Real.sqrt (2 / c3) * (1 - p) := by
    rw [show Real.sqrt (2 / c3) * (1 - p) = Real.sqrt (2 / c3 * (1 - p) ^ 2) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq h1p.le]]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by positivity)]
    have h4 : c3 / (1 - p) ≤ V := hVlo
    rw [div_le_iff₀ h1p] at h4
    have h5 : c3 ≤ V * (1 - p) := h4
    have h6 : (2 / c3 * (1 - p) ^ 2) * (p * V) = 2 * (1 - p) * (p * (V * (1 - p))) / c3 := by
      field_simp
    rw [h6, le_div_iff₀ hc3]
    nlinarith [mul_pos h1p hp0, mul_nonneg h1p.le hc3.le]
  unfold profF
  rw [← hVdef]
  calc Real.sqrt ((1 - p) / (p * V)) * (V / (V + x ^ α))
      ≤ (Real.sqrt (2 / c3) * (1 - p)) * 1 :=
        mul_le_mul hsq hfrac hfrac0 (by positivity)
    _ = _ := by ring

private lemma p12_pg6p2_psi_split {α : ℝ} (hα : 0 < α) :
    ∃ K9 : ℝ, 0 < K9 ∧ ∀ x : ℝ, x ∈ Ioc (0:ℝ) 1 → ∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
      psiRes α η x = c0 * ((∫ p in η..(1 - η), Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) +
        ∫ p in (1 - η)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) ∧
      0 ≤ ∫ p in (1 - η)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ∧
      ∫ p in (1 - η)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ≤ K9 * η ^ 2 := by
  obtain ⟨K, hK, hKt⟩ := p12_pg6p2_G_top hα
  refine ⟨K, hK, fun x hx η hη hη2 => ?_⟩
  have hint := lem_app_pl_Psi_i_integrable hα x hx
  have h1 : IntervalIntegrable (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p)
      volume η (1 - η) := hint.mono_set (by
    rw [uIcc_of_le zero_le_one, uIcc_of_le (by linarith)]
    exact Icc_subset_Icc hη.le (by linarith))
  have h2 : IntervalIntegrable (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p)
      volume (1 - η) 1 := hint.mono_set (by
    rw [uIcc_of_le zero_le_one, uIcc_of_le (by linarith)]
    exact Icc_subset_Icc (by linarith) le_rfl)
  refine ⟨?_, ?_, ?_⟩
  · unfold psiRes
    rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  · rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
    exact setIntegral_nonneg measurableSet_Ioo (fun p hp =>
      p12_pg6p2_G_nonneg hα hx.1 ⟨by linarith [hp.1], hp.2⟩)
  · rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
    have hsub : Ioo (1 - η) 1 ⊆ Ioo 0 1 := Ioo_subset_Ioo (by linarith) le_rfl
    have hI2 : IntegrableOn (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p)
        (Ioo (1 - η) 1) := by
      have := h2
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)] at this
      exact (integrableOn_Ioc_iff_integrableOn_Ioo).1 this
    have hle : ∫ p in Ioo (1 - η) 1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ≤
        ∫ p in Ioo (1 - η) 1, K * η :=
      setIntegral_mono_on hI2 (integrableOn_const (by simp)) measurableSet_Ioo (fun p hp => by
        have := hKt x hx.1 p (by linarith [hp.1]) hp.2
        have h3 : 1 - p ≤ η := by linarith [hp.1]
        nlinarith [hK])
    refine hle.trans ?_
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le (by linarith)]
    have : 1 - (1 - η) = η := by ring
    rw [this]; nlinarith [hK, hη]

private lemma p12_pg6p2_psi_lower {α : ℝ} (hα : 0 < α) :
    ∃ cΨ : ℝ, 0 < cΨ ∧ ∀ x : ℝ, x ∈ Ioc (0:ℝ) 1 → ∀ η : ℝ, 0 < η → η ≤ 1 / 4 →
      cΨ ≤ psiRes α η x := by
  have hc0 : 0 < c0 := by unfold c0; positivity
  have hx1 : (1:ℝ) ∈ Ioc (0:ℝ) 1 := ⟨one_pos, le_rfl⟩
  have hint1 := lem_app_pl_Psi_i_integrable hα 1 hx1
  have hint1' : IntervalIntegrable (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) * profF α 1 p)
      volume (1 / 4) (1 / 2) := hint1.mono_set (by
    rw [uIcc_of_le zero_le_one, uIcc_of_le (by norm_num)]
    exact Icc_subset_Icc (by norm_num) (by norm_num))
  have hpos : 0 < ∫ p in (1 / 4 : ℝ)..(1 / 2), Real.sqrt ((1 - p) / (p * contV α p)) * profF α 1 p := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on hint1' (fun p hp => ?_) (by norm_num)
    have hp0 : 0 < p := by linarith [hp.1]
    have hp1 : p < 1 := by linarith [hp.2]
    have hV := p12_pg6p2_contV_pos hα ⟨hp0, hp1⟩
    unfold profF
    have : (0:ℝ) < 1 ^ α := Real.rpow_pos_of_pos one_pos _
    have h1 : 0 < (1 - p) / (p * contV α p) := div_pos (by linarith) (by positivity)
    have := Real.sqrt_pos.2 h1
    positivity
  refine ⟨c0 * ∫ p in (1 / 4 : ℝ)..(1 / 2), Real.sqrt ((1 - p) / (p * contV α p)) * profF α 1 p,
    mul_pos hc0 hpos, fun x hx η hη hη4 => ?_⟩
  unfold psiRes
  refine mul_le_mul_of_nonneg_left ?_ hc0.le
  have hintx := lem_app_pl_Psi_i_integrable hα x hx
  have hintxη : IntervalIntegrable (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p)
      volume η 1 := hintx.mono_set (by
    rw [uIcc_of_le zero_le_one, uIcc_of_le (by linarith)]
    exact Icc_subset_Icc hη.le le_rfl)
  have hintx' : IntervalIntegrable (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p)
      volume (1 / 4) (1 / 2) := hintx.mono_set (by
    rw [uIcc_of_le zero_le_one, uIcc_of_le (by norm_num)]
    exact Icc_subset_Icc (by norm_num) (by norm_num))
  have h1 : ∫ p in (1 / 4 : ℝ)..(1 / 2), Real.sqrt ((1 - p) / (p * contV α p)) * profF α 1 p ≤
      ∫ p in (1 / 4 : ℝ)..(1 / 2), Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p := by
    refine intervalIntegral.integral_mono_on (by norm_num) hint1' hintx' (fun p hp => ?_)
    have hp0 : 0 < p := by linarith [hp.1]
    have hp1 : p < 1 := by linarith [hp.2]
    have hV := p12_pg6p2_contV_pos hα ⟨hp0, hp1⟩
    unfold profF
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    have hxa : x ^ α ≤ 1 ^ α := Real.rpow_le_rpow hx.1.le hx.2 hα.le
    have hx0a : 0 < x ^ α := Real.rpow_pos_of_pos hx.1 _
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hV hx0a]
  have h2 : ∫ p in (1 / 4 : ℝ)..(1 / 2), Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ≤
      ∫ p in η..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p := by
    refine intervalIntegral.integral_mono_interval hη4 (by norm_num) (by norm_num) ?_ hintxη
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun p hp => ?_)
    simp only [Pi.zero_apply]
    rcases hp.2.eq_or_lt with h | h
    · rw [h]; simp
    · exact p12_pg6p2_G_nonneg hα hx.1 ⟨lt_of_lt_of_le hη hp.1.le, h⟩
  linarith

private lemma p12_J_bounds {α c : ℝ} {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) {M m : ℝ} (hM : 0 < M)
    (hm : m ∈ Ioo M (gammaOf N B)) :
    0 ≤ Jrow B (plSpec α c N) i m ∧
      Jrow B (plSpec α c N) i m ≤ 1 / Real.sqrt M := by
  have hγ := p12_pg6_gamma_pos hB hN
  have hm0 : 0 < m := hM.trans hm.1
  have hμ := p12_pg6_plSpec_pos (α := α) hc i
  have hL := (p12_pg6p2_Lam_hasDeriv (plSpec α c N) hB hN
    (p12_pg6_plSpec_pos hc) ⟨hm0, hm.2⟩).1
  have hu : 0 < plSpec α c N i * partLam B (plSpec α c N) m := mul_pos hμ hL
  have hden : 0 < 1 + plSpec α c N i * partLam B (plSpec α c N) m := by linarith
  have hs : Real.sqrt (plSpec α c N i * partLam B (plSpec α c N) m) ≤
      1 + plSpec α c N i * partLam B (plSpec α c N) m := by
    nlinarith [Real.sq_sqrt hu.le, Real.sqrt_nonneg (plSpec α c N i * partLam B (plSpec α c N) m),
      sq_nonneg (plSpec α c N i * partLam B (plSpec α c N) m)]
  have ht : Real.sqrt (1 - m / gammaOf N B) ≤ 1 := by
    apply (Real.sqrt_le_one).2
    have := div_nonneg hm0.le hγ.le
    linarith
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
  unfold Jrow
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ (1 / Real.sqrt m) * 1 := by
      apply mul_le_mul _ ht (Real.sqrt_nonneg _) (by positivity)
      apply (div_le_div_iff₀ (mul_pos hsm hden) hsm).2
      nlinarith
    _ ≤ 1 / Real.sqrt M := by
      simpa using one_div_le_one_div_of_le hsM (Real.sqrt_le_sqrt hm.1.le)

private lemma p12_W_integrable {α c : ℝ} {N B : ℕ} (hα : 0 < α)
    (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) (i : Fin N) {M : ℝ} (hM : 0 < M) :
    IntegrableOn (partBfun B (plSpec α c N) i) (Ioo M (gammaOf N B)) := by
  have hγ := p12_pg6_gamma_pos hB hN
  have hμ := p12_pg6_plSpec_pos (α := α) hc i
  have hs : 0 < Real.sqrt (gammaOf N B * plSpec α c N i) := Real.sqrt_pos.2 (mul_pos hγ hμ)
  have hcont := (p12_pg6p2_W_cont hα hN hB hc i).mono
    (Ioo_subset_Ioo hM.le le_rfl)
  refine (integrableOn_const (C := Real.sqrt (gammaOf N B * plSpec α c N i) / Real.sqrt M)
    (by simp) : IntegrableOn _ (Ioo M (gammaOf N B))).mono'
      (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  refine Eventually.of_forall fun m hm => ?_
  have hm0 : m ∈ Ioo 0 (gammaOf N B) := ⟨hM.trans hm.1, hm.2⟩
  have hW := (p12_pg6p2_W_facts hα).choose_spec.2 N B c hN hB hc i m hm0
  have he := Jrow_eq_partBfun B N hN hB _ i hμ m hm0
    (p12_pg6p2_Lam_hasDeriv _ hB hN (p12_pg6_plSpec_pos hc) hm0).1
  rw [Real.norm_eq_abs, abs_of_pos hW.1]
  have hb := (p12_J_bounds (α := α) hN hB hc i hM hm).2
  rw [he, div_le_iff₀ hs] at hb
  exact hb.trans_eq (by ring)

private lemma p12_J_integrable {α c : ℝ} {N B : ℕ} (hα : 0 < α)
    (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) (i : Fin N) {M : ℝ} (hM : 0 < M) :
    IntegrableOn (Jrow B (plSpec α c N) i) (Ioo M (gammaOf N B)) := by
  refine ((p12_W_integrable hα hN hB hc i hM).div_const
    (Real.sqrt (gammaOf N B * plSpec α c N i))).congr ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
  refine Eventually.of_forall fun m hm => ?_
  have hm0 : m ∈ Ioo 0 (gammaOf N B) := ⟨hM.trans hm.1, hm.2⟩
  exact (Jrow_eq_partBfun B N hN hB _ i (p12_pg6_plSpec_pos hc i) m hm0
    (p12_pg6p2_Lam_hasDeriv _ hB hN (p12_pg6_plSpec_pos hc) hm0).1).symm

private lemma p12_mass_eq {α c : ℝ} {N B : ℕ}
    (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) (i : Fin N) {M : ℝ} (hM : 0 < M) :
    tailMass B (plSpec α c N) i M =
      (∫ m in Ioo M (gammaOf N B), partBfun B (plSpec α c N) i m) /
        Real.sqrt (gammaOf N B * plSpec α c N i) := by
  rw [← integral_div]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro m hm
  have hm0 : m ∈ Ioo 0 (gammaOf N B) := ⟨hM.trans hm.1, hm.2⟩
  exact Jrow_eq_partBfun B N hN hB _ i (p12_pg6_plSpec_pos hc i) m hm0
    (p12_pg6p2_Lam_hasDeriv _ hB hN (p12_pg6_plSpec_pos hc) hm0).1

private lemma p12_scale {α c : ℝ} {N B : ℕ}
    (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) (i : Fin N) :
    gammaOf N B * aN α c N / Real.sqrt (gammaOf N B * plSpec α c N i) =
      Real.sqrt (gammaOf N B) * rowFrac i ^ (α / 2) := by
  have hγ := p12_pg6_gamma_pos hB hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hr := p12_pg6_rowNum_pos i
  have hsγ : Real.sqrt (gammaOf N B) ≠ 0 := (Real.sqrt_pos.2 hγ).ne'
  have hsc : Real.sqrt c ≠ 0 := (Real.sqrt_pos.2 hc).ne'
  have hμ : Real.sqrt (plSpec α c N i) = Real.sqrt c * rowNum i ^ (-(α / 2)) := by
    rw [p12_pg6_plSpec_eq, Real.sqrt_mul hc.le,
      Real.sqrt_eq_rpow (rowNum i ^ (-α)), ← Real.rpow_mul hr.le]
    congr 2
    ring
  have hrpow : rowNum i ^ (α / 2) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  have hNpow : (N : ℝ) ^ (α / 2) ≠ 0 := (Real.rpow_pos_of_pos hNr _).ne'
  rw [Real.sqrt_mul hγ.le, hμ, aN]
  change _ = Real.sqrt (gammaOf N B) * (rowNum i / (N : ℝ)) ^ (α / 2)
  rw [Real.div_rpow hr.le hNr.le, show -α / 2 = -(α / 2) by ring,
    Real.rpow_neg hr.le, Real.rpow_neg hNr.le]
  field_simp
  rw [Real.sq_sqrt hγ.le]

private lemma p12_W_top_integral {α : ℝ} (hα : 0 < α) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N B : ℕ) (c : ℝ) (i : Fin N) (M : ℝ),
      0 < N → 0 < B → 0 < c → 0 < M → 4 * M ≤ gammaOf N B →
      0 ≤ ∫ m in (gammaOf N B - M)..(gammaOf N B), partBfun B (plSpec α c N) i m ∧
      (∫ m in (gammaOf N B - M)..(gammaOf N B), partBfun B (plSpec α c N) i m) /
        (gammaOf N B * aN α c N) ≤ K * (M / gammaOf N B) ^ 2 := by
  obtain ⟨K, hK, htop⟩ := p12_pg6p2_W_top hα
  refine ⟨K, hK, fun N B c i M hN hB hc hM h4 => ?_⟩
  have hγ := p12_pg6_gamma_pos hB hN
  have ha := p12_pg6p2_aN_pos (α := α) hc hN
  have hgm : 0 < gammaOf N B - M := by linarith
  have hint := p12_W_integrable hα hN hB hc i hgm
  rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
  refine ⟨setIntegral_nonneg measurableSet_Ioo (fun m hm =>
    ((p12_pg6p2_W_facts hα).choose_spec.2 N B c hN hB hc i m
      ⟨hgm.trans hm.1, hm.2⟩).1.le), ?_⟩
  have hb : ∫ m in Ioo (gammaOf N B - M) (gammaOf N B), partBfun B (plSpec α c N) i m ≤
      ∫ m in Ioo (gammaOf N B - M) (gammaOf N B), K * aN α c N * (M / gammaOf N B) := by
    apply setIntegral_mono_on hint (integrableOn_const (by simp)) measurableSet_Ioo
    intro m hm
    refine (htop N B c i hN hB hc m (by linarith [hm.1]) hm.2).trans ?_
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith [hm.1]) hγ.le)
      (mul_nonneg hK.le ha.le)
  rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le (by linarith)] at hb
  apply (div_le_iff₀ (mul_pos hγ ha)).2
  exact hb.trans_eq (by field_simp; ring)

private lemma p12_mass_error {α : ℝ} (hα : 0 < α) :
    ∃ C K d : ℝ, 0 < C ∧ 0 < K ∧ 0 < d ∧
      ∀ (N B : ℕ) (c : ℝ) (i : Fin N) (M : ℝ),
      0 < N → 2 ≤ B → 0 < c → 1 ≤ M → 4 * M ≤ gammaOf N B → C ≤ (B : ℝ) * M →
      |tailMass B (plSpec α c N) i M /
        (Real.sqrt (gammaOf N B) * rowFrac i ^ (α / 2) *
          psiRes α (M / gammaOf N B) (rowFrac i) / c0) - 1| ≤
        C / ((B : ℝ) * M) + K * (M / gammaOf N B) ^ 2 := by
  obtain ⟨C, hC, hmid⟩ := p12_pg6p2_S5 hα
  obtain ⟨K, hK, htop⟩ := p12_W_top_integral hα
  obtain ⟨Kt, hKt, hpsi⟩ := p12_pg6p2_psi_split hα
  obtain ⟨d, hd, hlow⟩ := p12_pg6p2_psi_lower hα
  have hc0 : 0 < c0 := by unfold c0; positivity
  refine ⟨C, (K + Kt) * c0 / d, d, hC, by positivity, hd,
    fun N B c i M hN hB hc hM h4 hCB => ?_⟩
  have hB0 : 0 < B := by omega
  have hγ := p12_pg6_gamma_pos hB0 hN
  have ha := p12_pg6p2_aN_pos (α := α) hc hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hM0 : 0 < M := by linarith
  have hgm : 0 < gammaOf N B - M := by linarith
  have hx : rowFrac i ∈ Ioc (0 : ℝ) 1 :=
    ⟨div_pos (p12_pg6_rowNum_pos i) hNr,
      (div_le_one hNr).2 (p12_pg6p2_rowNum_le i)⟩
  set γ := gammaOf N B
  set a := aN α c N
  set ψ := psiRes α (M / γ) (rowFrac i)
  set J := ∫ m in M..(γ - M), partBfun B (plSpec α c N) i m
  set T := ∫ m in (γ - M)..γ, partBfun B (plSpec α c N) i m
  set P := ∫ p in (M / γ)..(1 - M / γ),
    Real.sqrt ((1 - p) / (p * contV α p)) * profF α (rowFrac i) p
  set Q := ∫ p in (1 - M / γ)..1,
    Real.sqrt ((1 - p) / (p * contV α p)) * profF α (rowFrac i) p
  set L := C / ((B : ℝ) * M)
  have hη : 0 < M / γ := div_pos hM0 hγ
  have hη4 : M / γ ≤ 1 / 4 := by rw [div_le_iff₀ hγ]; linarith
  have hψd : d ≤ ψ := hlow _ hx _ hη hη4
  have hψ : 0 < ψ := hd.trans_le hψd
  obtain ⟨hψeq, hQ0, hQ⟩ := hpsi _ hx _ hη (by linarith : M / γ ≤ 1 / 2)
  change ψ = c0 * (P + Q) at hψeq
  change 0 ≤ Q at hQ0
  change Q ≤ Kt * (M / γ) ^ 2 at hQ
  have hP : 0 ≤ P := by
    dsimp only [P]
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
    exact setIntegral_nonneg measurableSet_Ioo (fun p hp =>
      p12_pg6p2_G_nonneg hα hx.1 ⟨hη.trans hp.1, by linarith [hp.2]⟩)
  obtain ⟨hJl, hJu⟩ := hmid N B c i M hN hB hc hM (by linarith) hCB
  change (1 - L) * P ≤ 1 / (γ * a) * J at hJl
  change 1 / (γ * a) * J ≤ (1 + L) * P at hJu
  obtain ⟨hT0, hT⟩ := htop N B c i M hN hB0 hc hM0 h4
  change 0 ≤ T at hT0
  change T / (γ * a) ≤ K * (M / γ) ^ 2 at hT
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hsum : P + Q = ψ / c0 := by rw [hψeq]; field_simp
  have hPψ : P ≤ ψ / c0 := by rw [← hsum]; linarith
  have herr : |(J + T) / (γ * a) - ψ / c0| ≤
      L * (ψ / c0) + (K + Kt) * (M / γ) ^ 2 := by
    have hTnn : 0 ≤ T / (γ * a) := div_nonneg hT0 (mul_pos hγ ha).le
    rw [one_div_mul_eq_div] at hJl hJu
    rw [add_div, ← hsum, abs_le]
    have hLP : L * P ≤ L * (P + Q) := mul_le_mul_of_nonneg_left (by linarith) hL0
    constructor <;> nlinarith [sq_nonneg (M / γ)]
  have hint := p12_W_integrable hα hN hB0 hc i hM0
  have hint1 : IntervalIntegrable (partBfun B (plSpec α c N) i) volume M (γ - M) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith), integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hint.mono_set (Ioo_subset_Ioo le_rfl (by linarith))
  have hint2 : IntervalIntegrable (partBfun B (plSpec α c N) i) volume (γ - M) γ := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith), integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hint.mono_set (Ioo_subset_Ioo (by linarith) le_rfl)
  have hmass : tailMass B (plSpec α c N) i M =
      (J + T) / Real.sqrt (γ * plSpec α c N i) := by
    rw [p12_mass_eq hN hB0 hc i hM0]
    congr 1
    have hadd := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
    rw [intervalIntegral.integral_of_le (by linarith : M ≤ γ),
      integral_Ioc_eq_integral_Ioo] at hadd
    exact hadd.symm
  have hscale := p12_scale (α := α) hN hB0 hc i
  have hs : 0 < Real.sqrt (γ * plSpec α c N i) :=
    Real.sqrt_pos.2 (mul_pos hγ (p12_pg6_plSpec_pos hc i))
  have heq : tailMass B (plSpec α c N) i M /
      (Real.sqrt γ * rowFrac i ^ (α / 2) * ψ / c0) - 1 =
      ((J + T) / (γ * a) - ψ / c0) / (ψ / c0) := by
    change γ * a / Real.sqrt (γ * plSpec α c N i) =
      Real.sqrt γ * rowFrac i ^ (α / 2) at hscale
    rw [hmass, ← hscale]
    field_simp [hγ.ne', ha.ne', hs.ne', hψ.ne', hc0.ne'] <;> ring
  rw [heq, abs_div, abs_of_pos (div_pos hψ hc0)]
  apply (div_le_iff₀ (div_pos hψ hc0)).2
  refine herr.trans ?_
  have hb : 1 ≤ ψ / d := (le_div_iff₀ hd).2 (by simpa using hψd)
  have hcoeff : K + Kt ≤ ((K + Kt) * c0 / d) * (ψ / c0) := by
    calc K + Kt ≤ (K + Kt) * (ψ / d) := le_mul_of_one_le_right (by positivity) hb
      _ = _ := by field_simp
  have hq := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (M / γ))
  dsimp only [L] at herr ⊢
  nlinarith

private lemma p12_pg6p3_row_pos {N : ℕ} (i : Fin N) : 0 < rowNum i := by
  unfold rowNum
  positivity

private lemma p12_pg6p3_W_formula {α β c : ℝ} (hc : 0 < c) (hβ0 : 0 < β) (hβ1 : β < 1)
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (i : Fin N) :
    cutW β α c N B i = Real.sqrt ((rowNum i / (N : ℝ)) ^ (-α) /
      (gammaOf N B * sPow β 2)) := by
  have hr := p12_pg6p3_row_pos i
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hs : 0 < sPow β 2 := by
    rw [sPow_two hβ0.le hβ1]
    apply div_pos <;> linarith
  have ha : aN α c N = Real.sqrt (c * (N : ℝ) ^ (-α)) := by
    unfold aN
    rw [Real.sqrt_mul hc.le, Real.sqrt_eq_rpow ((N : ℝ) ^ (-α)), ← Real.rpow_mul hNr.le]
    congr 2
    ring
  have hapos : 0 < aN α c N := by
    rw [ha]
    positivity
  have hH : Real.sqrt (plSpec α c N i / (gammaOf N B * sPow β 2)) =
      aN α c N * Real.sqrt ((rowNum i / (N : ℝ)) ^ (-α) / (gammaOf N B * sPow β 2)) := by
    rw [ha, ← Real.sqrt_mul (by positivity)]
    congr 1
    change c * rowNum i ^ (-α) / _ = _
    rw [Real.div_rpow hr.le hNr.le]
    have hp : 0 < (N : ℝ) ^ (-α) := Real.rpow_pos_of_pos hNr _
    field_simp
  unfold cutW
  rw [hH, mul_div_cancel_left₀ _ hapos.ne']

private lemma p12_pg6p3_res_bounds {α x η : ℝ} (hα : 0 < α) (hx : x ∈ Ioc (0 : ℝ) 1)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    0 ≤ psiRes α η x ∧ psiRes α η x ≤ profPsi α x := by
  have hc : 0 ≤ c0 := by unfold c0; positivity
  have hint := lem_app_pl_Psi_i_integrable hα x hx
  have h0η := hint.mono_set (show uIcc 0 η ⊆ uIcc (0 : ℝ) 1 by
    rw [uIcc_of_le hη0, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hη1)
  have hη1i := hint.mono_set (show uIcc η 1 ⊆ uIcc (0 : ℝ) 1 by
    rw [uIcc_of_le hη1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hη0 le_rfl)
  have hnn : ∀ p ∈ Icc (0 : ℝ) 1,
      0 ≤ Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p := by
    intro p hp
    by_cases hp0 : p = 0
    · simp [hp0]
    by_cases hp1 : p = 1
    · simp [hp1]
    have hp' : p ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hp.1 (Ne.symm hp0), lt_of_le_of_ne hp.2 hp1⟩
    have hV : ∃ V ∈ Ioi (0 : ℝ), contS α V = p :=
      (def_app_pl_profiles_S_bij hα).2.surjOn hp'
    have hVp : 0 < contV α p := Function.invFunOn_mem hV
    have hxp : 0 < x ^ α := Real.rpow_pos_of_pos hx.1 _
    unfold profF
    positivity
  have hn0 := intervalIntegral.integral_nonneg (μ := volume) hη0 (fun p hp => hnn p ⟨hp.1, hp.2.trans hη1⟩)
  have hn1 := intervalIntegral.integral_nonneg (μ := volume) hη1 (fun p hp => hnn p ⟨hη0.trans hp.1, hp.2⟩)
  constructor
  · exact mul_nonneg hc hn1
  · unfold psiRes profPsi
    rw [← intervalIntegral.integral_add_adjacent_intervals h0η hη1i]
    exact mul_le_mul_of_nonneg_left (by linarith) hc

private lemma p12_pg6_reg_comp {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    assum_app_pl_regime α β (fun n => N (φ n)) (fun n => B (φ n)) (fun n => c (φ n)) :=
  ⟨hreg.hα, hreg.hβ0, hreg.hβ1, fun n => hreg.hNpos _, fun n => hreg.hBpos _,
    fun n => hreg.hcpos _, hreg.hN.comp hφ, hreg.hB.comp hφ, hreg.hγ.comp hφ⟩

private lemma p12_pg6_reg_one {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) :
    assum_app_pl_regime α β N B (fun _ => 1) :=
  ⟨hreg.hα, hreg.hβ0, hreg.hβ1, hreg.hNpos, hreg.hBpos, fun _ => one_pos, hreg.hN, hreg.hB,
    hreg.hγ⟩

private lemma p12_pg6_trichotomy (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ (Tendsto (fun n => r (ψ n)) atTop (𝓝 0) ∨
      (∃ z : ℝ, 0 < z ∧ Tendsto (fun n => r (ψ n)) atTop (𝓝 z)) ∨
      Tendsto (fun n => r (ψ n)) atTop atTop) := by
  obtain ⟨a, ψ, hψ, ha⟩ := CompactSpace.tendsto_subseq (fun n => ENNReal.ofReal (r n))
  refine ⟨ψ, hψ, ?_⟩
  by_cases htop : a = ⊤
  · right; right
    rw [tendsto_atTop]
    intro b
    have h1 : ENNReal.ofReal (max b 0) < a := by rw [htop]; exact ENNReal.ofReal_lt_top
    filter_upwards [ha.eventually (lt_mem_nhds h1)] with n hn
    have := (ENNReal.ofReal_lt_ofReal_iff' ).1 hn
    exact (le_max_left b 0).trans this.1.le
  · have h1 : Tendsto (fun n => r (ψ n)) atTop (𝓝 a.toReal) := by
      have := (ENNReal.tendsto_toReal htop).comp ha
      refine this.congr (fun n => ?_)
      simp [Function.comp, ENNReal.toReal_ofReal (hr _)]
    rcases (ENNReal.toReal_nonneg (a := a)).eq_or_lt with h0 | h0
    · left; rw [← h0] at h1; exact h1
    · right; left; exact ⟨a.toReal, h0, h1⟩

private lemma p12_cutW_scale {α β : ℝ} {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    (hβ0 : 0 < β) (hβ1 : β < 1) (i : Fin N) :
    0 < cutW β α 1 N B i ∧
      (Real.sqrt (gammaOf N B) * rowFrac i ^ (α / 2)) *
        (c0 * Real.sqrt (sPow β 2) * cutW β α 1 N B i) = c0 := by
  have hγ := p12_pg6_gamma_pos hB hN
  have hx : 0 < rowFrac i :=
    div_pos (p12_pg6_rowNum_pos i) (by exact_mod_cast hN)
  have hs : 0 < sPow β 2 := by
    rw [sPow_two hβ0.le hβ1]
    exact div_pos (by linarith) (by linarith)
  have hform := p12_pg6p3_W_formula (α := α) one_pos hβ0 hβ1 hN hB i
  change cutW β α 1 N B i = Real.sqrt (rowFrac i ^ (-α) / (gammaOf N B * sPow β 2)) at hform
  rw [hform]
  refine ⟨Real.sqrt_pos.2 (by positivity), ?_⟩
  rw [Real.sqrt_div (Real.rpow_nonneg hx.le _), Real.sqrt_mul hγ.le,
    Real.sqrt_eq_rpow (rowFrac i ^ (-α)), ← Real.rpow_mul hx.le,
    show -α * (1 / 2) = -(α / 2) by ring, Real.rpow_neg hx.le]
  have hg0 := (Real.sqrt_pos.2 hγ).ne'
  have hs0 := (Real.sqrt_pos.2 hs).ne'
  have hx0 := (Real.rpow_pos_of_pos hx (α / 2)).ne'
  field_simp

private lemma p12_equiv_normalized {P Q W : ℕ → ℝ} {k : ℝ} (hk : 0 < k)
    (hP : ∀ n, 0 < P n) (hW : ∀ n, 0 < W n) (h : IsEquivalent atTop Q P) :
    Tendsto (fun n => (Q n - P n) / (k * W n + P n)) atTop (𝓝 0) := by
  have ht := (isEquivalent_iff_tendsto_one (Eventually.of_forall fun n => (hP n).ne')).1 h
  have hz : Tendsto (fun n => |Q n / P n - 1|) atTop (𝓝 0) := by
    simpa using (ht.sub_const 1).abs
  refine squeeze_zero_norm' (Eventually.of_forall fun n => ?_) hz
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (add_pos (mul_pos hk (hW n)) (hP n))]
  have he : Q n / P n - 1 = (Q n - P n) / P n := by field_simp [(hP n).ne']
  rw [he, abs_div, abs_of_pos (hP n)]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (hP n) (le_add_of_nonneg_left (mul_pos hk (hW n)).le)

private lemma p12_small_normalized {P Q W : ℕ → ℝ} {k : ℝ} (hk : 0 < k)
    (hP : ∀ n, 0 < P n) (hW : ∀ n, 0 < W n) (hQ : ∀ᶠ n in atTop, 0 ≤ Q n)
    (h : IsLittleO atTop (fun n => P n + Q n) W) :
    Tendsto (fun n => (Q n - P n) / (k * W n + P n)) atTop (𝓝 0) := by
  have hz : Tendsto (fun n => ((P n + Q n) / W n) / k) atTop (𝓝 0) := by
    simpa using h.tendsto_div_nhds_zero.div_const k
  refine squeeze_zero_norm' ?_ hz
  filter_upwards [hQ] with n hn
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (add_pos (mul_pos hk (hW n)) (hP n))]
  have ha : |Q n - P n| ≤ P n + Q n := by
    rw [abs_le]; constructor <;> linarith [hP n]
  calc
    _ ≤ (P n + Q n) / (k * W n + P n) :=
      div_le_div_of_nonneg_right ha (add_pos (mul_pos hk (hW n)) (hP n)).le
    _ ≤ (P n + Q n) / (k * W n) :=
      div_le_div_of_nonneg_left (by linarith [hP n]) (mul_pos hk (hW n)) (by linarith [hP n])
    _ = _ := by ring

private lemma p12_profile_normalized {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (i : ∀ n, Fin (N n)) (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) (M : ℝ) (hM : 0 < M) :
    Tendsto (fun n =>
      (psiRes α (M / gammaOf (N n) (B n)) (rowFrac (i n)) - profPsi α (rowFrac (i n))) /
        (c0 * Real.sqrt (sPow β 2) * cutW β α 1 (N n) (B n) (i n) +
          profPsi α (rowFrac (i n)))) atTop (𝓝 0) := by
  have hk : 0 < c0 * Real.sqrt (sPow β 2) := by
    have hs : 0 < sPow β 2 := by
      rw [sPow_two R.hβ0.le R.hβ1]
      exact div_pos (by linarith [R.hβ0, R.hβ1]) (by linarith [R.hβ0, R.hβ1])
    unfold c0
    positivity
  have hP : ∀ n, 0 < profPsi α (rowFrac (i n)) := fun n =>
    lem_app_pl_Psi_i_pos R.hα _
      ⟨div_pos (p12_pg6_rowNum_pos _) (by exact_mod_cast R.hNpos n),
        (div_le_one (by exact_mod_cast R.hNpos n)).2 (p12_pg6p2_rowNum_le _)⟩
  have hW : ∀ n, 0 < cutW β α 1 (N n) (B n) (i n) := fun n =>
    (p12_cutW_scale (α := α) (R.hNpos n) (R.hBpos n) R.hβ0 R.hβ1 (i n)).1
  have hQ : ∀ᶠ n in atTop, 0 ≤ psiRes α (M / gammaOf (N n) (B n)) (rowFrac (i n)) := by
    filter_upwards [R.hγ.eventually_ge_atTop M] with n hn
    have hγ := p12_pg6_gamma_pos (R.hBpos n) (R.hNpos n)
    exact (p12_pg6p3_res_bounds R.hα
      ⟨div_pos (p12_pg6_rowNum_pos _) (by exact_mod_cast R.hNpos n),
        (div_le_one (by exact_mod_cast R.hNpos n)).2 (p12_pg6p2_rowNum_le _)⟩
      (div_nonneg hM.le hγ.le) ((div_le_one hγ).2 hn)).1
  set r : ℕ → ℝ := fun n => cutW β α 1 (N n) (B n) (i n) /
    Real.log (gammaOf (N n) (B n)) ^ cutNu α
  have hr : ∀ᶠ n in atTop, 0 ≤ r n := by
    filter_upwards [R.hγ.eventually_gt_atTop 1] with n hn
    exact div_nonneg (hW n).le (Real.rpow_nonneg (Real.log_pos hn).le _)
  apply tendsto_of_subseq_tendsto
  intro φ hφ
  obtain ⟨σ, hσ, hcases⟩ := p12_pg6_trichotomy (fun n => max (r (φ n)) 0) (fun _ => le_max_right _ _)
  have hθ : Tendsto (fun n => φ (σ n)) atTop atTop := hφ.comp hσ.tendsto_atTop
  have R' := p12_pg6_reg_one (p12_pg6_reg_comp R hθ)
  have hi' : Tendsto (fun n => rowNum (i (φ (σ n)))) atTop atTop := hi.comp hθ
  have hx' : Tendsto (fun n => rowNum (i (φ (σ n))) / (N (φ (σ n)) : ℝ)) atTop (𝓝 0) := hx.comp hθ
  have hev : ∀ᶠ n in atTop, max (r (φ (σ n))) 0 = r (φ (σ n)) := by
    filter_upwards [hθ.eventually hr] with n hn
    exact max_eq_left hn
  refine ⟨σ, ?_⟩
  rcases hcases with h | ⟨z, hz, h⟩ | h
  · obtain ⟨⟨C, hC⟩, -⟩ := (lem_app_pl_cutoff_iii R' hα1 (fun _ => rfl)
      (fun n => i (φ (σ n))) hi' hx').2 (h.congr' hev)
    have he := (lem_app_pl_cutoff_iii R' hα1 (fun _ => rfl)
      (fun n => i (φ (σ n))) hi' hx').1 M hM C hC
    exact p12_equiv_normalized hk (fun n => hP _) (fun n => hW _) he
  · have he := (lem_app_pl_cutoff_i R' hα1 (fun _ => rfl)
      (fun n => i (φ (σ n))) hi' hx' M hM z hz (h.congr' hev))
    exact p12_equiv_normalized hk (fun n => hP _) (fun n => hW _) (he.1.trans he.2.symm)
  · have he := lem_app_pl_cutoff_ii R' hα1 (fun _ => rfl)
      (fun n => i (φ (σ n))) hi' hx' M hM (h.congr' hev)
    exact p12_small_normalized hk (fun n => hP _) (fun n => hW _) (hθ.eventually hQ) he

private lemma p12_normalized_transfer {a q b : ℕ → ℝ}
    (hq : ∀ᶠ n in atTop, 0 < q n ∧ q n ≤ b n)
    (ha : Tendsto (fun n => a n / q n) atTop (𝓝 1))
    (hb : Tendsto (fun n => (q n - b n) / (1 + b n)) atTop (𝓝 0)) :
    Tendsto (fun n => (a n - b n) / (1 + b n)) atTop (𝓝 0) := by
  have hz : Tendsto (fun n => (a n - q n) / (1 + b n)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using (ha.sub_const 1).abs)
    filter_upwards [hq] with n hn
    have hb0 : 0 < 1 + b n := by linarith [hn.1, hn.2]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hb0]
    have he : a n / q n - 1 = (a n - q n) / q n := by field_simp [hn.1.ne']
    rw [he, abs_div, abs_of_pos hn.1]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hn.1 (by linarith [hn.2])
  convert hz.add hb using 1 <;> try simp
  funext n
  ring

private lemma p12_pg6p2_Phi_bounds {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C3 : ℝ, 0 < C3 ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c →
      ∀ m ∈ Ioo 0 (gammaOf N B),
        1 ≤ Efun β m * thetaN β B (plSpec α c N) m ∧
        Efun β m * thetaN β B (plSpec α c N) m ≤
          1 + C3 * (1 / m + 1 / (gammaOf N B - m)) := by
  obtain ⟨cα, hcα, hel⟩ := lem_app_pl_elasticity_i hα
  obtain ⟨C2, hC2⟩ := lem_app_pl_elasticity_ii hα hβ0 hβ1
  obtain ⟨cE, CE, hcE, hcCE, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  have hCE : 0 < CE := lt_of_lt_of_le hcE hcCE
  refine ⟨CE * (1 / cα + 1), by positivity, fun N B c hN hB hc m hm => ?_⟩
  refine ⟨(hC2 N B c hN hB hc m hm).2, ?_⟩
  obtain ⟨-, hlam⟩ := (hel N B c hN hB hc)
  obtain ⟨hl1, hl2⟩ := hlam m hm
  obtain ⟨hm0, hmg⟩ := hm
  have hgm : 0 < gammaOf N B - m := sub_pos.2 hmg
  obtain ⟨-, hE2⟩ := hE m hm0
  have hEC : Efun β m ≤ CE := hE2.trans (mul_le_of_le_one_right hCE.le (min_le_right _ _))
  have hEpos : 0 < Efun β m := by
    have := hE m hm0
    have h1 : 0 < cE * min m 1 := mul_pos hcE (lt_min hm0 one_pos)
    linarith [this.1]
  set r := deriv (partLam B (plSpec α c N)) m / partLam B (plSpec α c N) m with hr
  have hrb : r ≤ (1 / cα) * (1 / m + 1 / (gammaOf N B - m)) := hl2
  have hkey : Efun β m * thetaN β B (plSpec α c N) m =
      1 + Efun β m * (r - 1 / m + 1 / (gammaOf N B - m)) := by
    unfold thetaN
    rw [← hr]
    field_simp
    ring
  rw [hkey]
  have hS : 0 < 1 / m + 1 / (gammaOf N B - m) := by positivity
  have h1 : r - 1 / m + 1 / (gammaOf N B - m) ≤ (1 / cα + 1) * (1 / m + 1 / (gammaOf N B - m)) := by
    have : 0 < 1 / m := by positivity
    have : 0 ≤ 1 / (gammaOf N B - m) := by positivity
    nlinarith
  have hnn : 0 ≤ (r - 1 / m + 1 / (gammaOf N B - m)) := by
    have : 1 / m ≤ r := hl1
    have : 0 ≤ 1 / (gammaOf N B - m) := by positivity
    linarith
  have h2 : Efun β m * (r - 1 / m + 1 / (gammaOf N B - m)) ≤
      CE * ((1 / cα + 1) * (1 / m + 1 / (gammaOf N B - m))) :=
    mul_le_mul hEC h1 hnn hCE.le
  linarith [h2]

private lemma p12_pg6p2_W_cd {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (i : Fin N) :
    ContDiffOn ℝ 1 (partBfun B μ i) (Ioo 0 (gammaOf N B)) := by
  obtain ⟨-, hb2, -, hcd⟩ := def_app_pl_participation_bij μ hB hN hpos
  have hΛ : ContDiffOn ℝ 1 (partLam B μ) (Ioo 0 (gammaOf N B)) := hcd.of_le (by exact_mod_cast le_top)
  have hmu := hpos i
  have hLp : ∀ m ∈ Ioo 0 (gammaOf N B), 0 < partLam B μ m := fun m hm => hb2.mapsTo hm
  have hu : ContDiffOn ℝ 1 (fun m => (gammaOf N B - m) / (m * partLam B μ m)) (Ioo 0 (gammaOf N B)) := by
    refine (contDiffOn_const.sub contDiffOn_id).div (contDiffOn_id.mul hΛ) (fun m hm => ?_)
    exact (mul_pos hm.1 (hLp m hm)).ne'
  have hs : ContDiffOn ℝ 1 (fun m => Real.sqrt ((gammaOf N B - m) / (m * partLam B μ m)))
      (Ioo 0 (gammaOf N B)) := by
    refine hu.sqrt (fun m hm => ?_)
    exact (div_pos (sub_pos.2 hm.2) (mul_pos hm.1 (hLp m hm))).ne'
  have hf : ContDiffOn ℝ 1 (fun m => partLam B μ m * μ i / (1 + partLam B μ m * μ i))
      (Ioo 0 (gammaOf N B)) := by
    refine (hΛ.mul contDiffOn_const).div (contDiffOn_const.add (hΛ.mul contDiffOn_const)) (fun m hm => ?_)
    have := mul_pos (hLp m hm) hmu
    linarith
  exact hs.mul hf

private lemma p12_pg6p2_W_left {α : ℝ} (hα : 0 < α) :
    ∃ C4 : ℝ, 0 < C4 ∧ ∀ (N B : ℕ) (c : ℝ) (i : Fin N) (M : ℝ), 0 < N → 0 < B → 0 < c → 1 ≤ M →
      4 * M ≤ gammaOf N B →
      partBfun B (plSpec α c N) i M ≤
        Real.exp (2 * C4) / M * ∫ m in M..(2 * M), partBfun B (plSpec α c N) i m := by
  obtain ⟨C4, hC4, hW⟩ := p12_pg6p2_W_facts hα
  refine ⟨C4, hC4, fun N B c i M hN hB hc hM h4 => ?_⟩
  have hM0 : 0 < M := by linarith
  set γ := gammaOf N B with hγdef
  set W := partBfun B (plSpec α c N) i with hWdef
  have hIcc : ∀ m ∈ Icc M (2 * M), m ∈ Ioo 0 γ := fun m hm => ⟨by linarith [hm.1], by linarith [hm.2]⟩
  -- log-derivative bound
  have hlog : ∀ m ∈ Icc M (2 * M), HasDerivWithinAt (fun x => Real.log (W x))
      (deriv W m / W m) (Icc M (2 * M)) m := by
    intro m hm
    obtain ⟨hpos, hd, -⟩ := hW N B c hN hB hc i m (hIcc m hm)
    exact (hd.log hpos.ne').hasDerivWithinAt
  have hbd : ∀ m ∈ Icc M (2 * M), ‖deriv W m / W m‖ ≤ 2 * C4 / M := by
    intro m hm
    obtain ⟨hpos, -, hder⟩ := hW N B c hN hB hc i m (hIcc m hm)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    refine hder.trans ?_
    have h1 : 1 / m ≤ 1 / M := one_div_le_one_div_of_le hM0 hm.1
    have h2 : 1 / (γ - m) ≤ 1 / M := by
      apply one_div_le_one_div_of_le hM0; linarith [hm.2]
    have : (1 / m + 1 / (γ - m)) ≤ 2 / M := by
      have : 2 / M = 1 / M + 1 / M := by ring
      linarith
    calc C4 * W m * (1 / m + 1 / (γ - m)) ≤ C4 * W m * (2 / M) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * C4 / M * W m := by ring
  have hmvt : ∀ m ∈ Icc M (2 * M), Real.log (W M) ≤ Real.log (W m) + 2 * C4 := by
    intro m hm
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hlog hbd (convex_Icc M (2 * M))
      (show M ∈ Icc M (2 * M) from ⟨le_rfl, by linarith⟩) hm
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
    have h1 := (abs_le.1 this).1
    have h2 : 2 * C4 / M * |m - M| ≤ 2 * C4 := by
      rw [abs_of_nonneg (by linarith [hm.1])]
      rw [div_mul_eq_mul_div, div_le_iff₀ hM0]
      nlinarith [hm.2]
    linarith
  have hWpos : ∀ m ∈ Icc M (2 * M), 0 < W m := fun m hm => (hW N B c hN hB hc i m (hIcc m hm)).1
  have hWM : ∀ m ∈ Icc M (2 * M), W M ≤ Real.exp (2 * C4) * W m := by
    intro m hm
    have hM1 : 0 < W M := hWpos M ⟨le_rfl, by linarith⟩
    have := hmvt m hm
    have h2 : W M ≤ Real.exp (Real.log (W m) + 2 * C4) := by
      calc W M = Real.exp (Real.log (W M)) := (Real.exp_log hM1).symm
        _ ≤ _ := Real.exp_le_exp.2 this
    rw [Real.exp_add, Real.exp_log (hWpos m hm)] at h2
    linarith
  have hcontW : ContinuousOn W (Icc M (2 * M)) := fun m hm =>
    (hW N B c hN hB hc i m (hIcc m hm)).2.1.continuousAt.continuousWithinAt
  have hint : IntervalIntegrable W volume M (2 * M) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    exact hcontW
  have e : Real.exp (2 * C4) * Real.exp (-(2 * C4)) = 1 := by rw [← Real.exp_add]; simp
  have hmono : ∫ m in M..(2 * M), W M * Real.exp (-(2 * C4)) ≤ ∫ m in M..(2 * M), W m := by
    refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const hint (fun m hm => ?_)
    have := hWM m hm
    have hep := Real.exp_pos (-(2 * C4))
    calc W M * Real.exp (-(2 * C4)) ≤ (Real.exp (2 * C4) * W m) * Real.exp (-(2 * C4)) :=
          mul_le_mul_of_nonneg_right this hep.le
      _ = W m * (Real.exp (2 * C4) * Real.exp (-(2 * C4))) := by ring
      _ = W m := by rw [e, mul_one]
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have e1 : (2 * M - M) = M := by ring
  rw [e1] at hmono
  have hep := Real.exp_pos (2 * C4)
  rw [div_mul_eq_mul_div, le_div_iff₀ hM0]
  have : M * (W M * Real.exp (-(2 * C4))) * Real.exp (2 * C4) = M * W M := by
    calc _ = M * W M * (Real.exp (2 * C4) * Real.exp (-(2 * C4))) := by ring
      _ = _ := by rw [e, mul_one]
  nlinarith [mul_le_mul_of_nonneg_right hmono hep.le]

private lemma p12_primitive_ibp (f : ℝ → ℝ) (m0 C0 : ℝ)
    (hC0nn : 0 ≤ C0)
    (hfi : ∀ t : ℝ, m0 ≤ t → IntervalIntegrable f volume m0 t)
    (hC0 : ∀ t : ℝ, m0 ≤ t → |∫ m in m0..t, f m| ≤ C0)
    (a c : ℝ) (hma : m0 ≤ a) (hac : a ≤ c) (W : ℝ → ℝ)
    (hW : ContDiffOn ℝ 1 W (Icc a c)) :
    |∫ m in a..c, f m * W m| ≤
      C0 * (|W a| + |W c| + ∫ m in a..c, |derivWithin W (Icc a c) m|) := by
  rcases eq_or_lt_of_le hac with rfl | hlt
  · simp only [intervalIntegral.integral_same, abs_zero]
    nlinarith [abs_nonneg (W a)]
  have hIcc : Set.uIcc a c = Set.Icc a c := Set.uIcc_of_le hac
  have hint : IntervalIntegrable (fun m => f m) volume m0 c :=
    hfi c (hma.trans hac)
  have hsub : Set.uIcc a c ⊆ Set.uIcc m0 c :=
    Set.uIcc_subset_uIcc (Set.mem_uIcc.2 (Or.inl ⟨hma, hac⟩))
      (Set.mem_uIcc.2 (Or.inl ⟨hma.trans hac, le_rfl⟩))
  have hG : AbsolutelyContinuousOnInterval
      (fun x => ∫ m in m0..x, (f m)) a c :=
    (hint.absolutelyContinuousOnInterval_intervalIntegral Set.left_mem_uIcc).mono hsub
  have hWac : AbsolutelyContinuousOnInterval W a c := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [hIcc]
    exact hW
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc a c →
      deriv (fun x => ∫ m in m0..x, (f m)) x
        = f x := by
    filter_upwards [hint.ae_hasDerivAt_integral] with x hx hxI
    have hxm : x ∈ Set.uIcc m0 c := hsub (Set.uIoc_subset_uIcc hxI)
    exact (hx hxm m0 Set.left_mem_uIcc).deriv
  have hderiv_eq : ∫ x in a..c, deriv (fun x => ∫ m in m0..x, (f m)) x * W x
      = ∫ x in a..c, (f x) * W x :=
    intervalIntegral.integral_congr_ae (hae.mono fun x hx hxI => by rw [hx hxI])
  have hIBP := hG.integral_mul_deriv_eq_deriv_mul hWac
  have hGc : |∫ m in m0..c, (f m)| ≤ C0 :=
    hC0 c (hma.trans hac)
  have hGa : |∫ m in m0..a, (f m)| ≤ C0 := hC0 a hma
  have hcont : ContinuousOn (derivWithin W (Icc a c)) (Icc a c) :=
    hW.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) (by norm_num)
  have hdWint : IntervalIntegrable (fun x => |derivWithin W (Icc a c) x|) volume a c := by
    apply ContinuousOn.intervalIntegrable
    rw [hIcc]
    exact hcont.abs
  have hI2 : |∫ x in a..c, (∫ m in m0..x, (f m)) * deriv W x|
      ≤ C0 * ∫ x in a..c, |derivWithin W (Icc a c) x| := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f := fun x =>
        (∫ m in m0..x, (f m)) * deriv W x)
      (g := fun x => C0 * |derivWithin W (Icc a c) x|) hac
      (by
        filter_upwards [Measure.ae_ne volume c] with x hxc hx
        have hxIoo : x ∈ Set.Ioo a c := ⟨hx.1, lt_of_le_of_ne hx.2 hxc⟩
        have hd : deriv W x = derivWithin W (Icc a c) x :=
          (derivWithin_of_mem_nhds (Icc_mem_nhds hxIoo.1 hxIoo.2)).symm
        have hxm : m0 ≤ x := hma.trans hx.1.le
        rw [Real.norm_eq_abs, abs_mul, hd]
        exact mul_le_mul_of_nonneg_right (hC0 x hxm) (abs_nonneg _))
      (hdWint.const_mul C0)
    rw [Real.norm_eq_abs] at hb
    rw [intervalIntegral.integral_const_mul] at hb
    exact hb
  have tri : ∀ x y z : ℝ, |x - y - z| ≤ |x| + |y| + |z| := by
    intro x y z
    rw [abs_le]
    constructor <;> linarith [neg_abs_le x, neg_abs_le y, neg_abs_le z, le_abs_self x,
      le_abs_self y, le_abs_self z, neg_le_abs y, neg_le_abs z]
  have hA1 : |(∫ m in m0..c, (f m)) * W c| ≤
      C0 * |W c| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hGc (abs_nonneg _)
  have hA2 : |(∫ m in m0..a, (f m)) * W a| ≤
      C0 * |W a| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hGa (abs_nonneg _)
  have hI1 : ∫ x in a..c, (f x) * W x =
      (∫ m in m0..c, (f m)) * W c
        - (∫ m in m0..a, (f m)) * W a
        - ∫ x in a..c, (∫ m in m0..x, (f m)) * deriv W x := by
    rw [← hderiv_eq]
    linarith [hIBP]
  rw [hI1]
  have hT := tri ((∫ m in m0..c, (f m)) * W c)
    ((∫ m in m0..a, (f m)) * W a)
    (∫ x in a..c, (∫ m in m0..x, (f m)) * deriv W x)
  nlinarith [hT, hA1, hA2, hI2]

private lemma p12_mid {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (CA Cavg : ℝ) (hCA : 0 < CA) (hCavg0 : 0 ≤ Cavg) :
    ∃ K8 : ℝ, 0 < K8 ∧ ∀ (N B : ℕ) (c : ℝ) (i : Fin N) (M : ℝ),
      0 < N → 0 < B → 0 < c → 1 ≤ M → 4 * M ≤ gammaOf N B →
      ∀ (A : ℝ → ℝ) (s : ℝ),
      (∀ t, 1 ≤ t → IntervalIntegrable A volume 1 t) →
      (∀ t, 1 ≤ t → |∫ m in 1..t, (A m - s)| ≤ Cavg) →
      (∀ m, 1 ≤ m → |A m| ≤ CA) →
      IntegrableOn (fun m => A m * partBfun B (plSpec α c N) i m * Efun β m *
        thetaN β B (plSpec α c N) m) (Ioo M (gammaOf N B)) →
      |(∫ m in M..(gammaOf N B - M),
          A m * partBfun B (plSpec α c N) i m * Efun β m * thetaN β B (plSpec α c N) m) -
        s * ∫ m in M..(gammaOf N B - M), partBfun B (plSpec α c N) i m| ≤
        K8 / M * (∫ m in M..(gammaOf N B - M), partBfun B (plSpec α c N) i m) +
          K8 * aN α c N * M / gammaOf N B := by
  obtain ⟨K6, hK6, hWtop⟩ := p12_pg6p2_W_top hα
  obtain ⟨C3, hC3, hPhi⟩ := p12_pg6p2_Phi_bounds hα hβ0 hβ1
  obtain ⟨C4w, hC4w, hWf⟩ := p12_pg6p2_W_facts hα
  obtain ⟨C4l, hC4l, hWleft⟩ := p12_pg6p2_W_left hα
  refine ⟨(|Cavg| * (Real.exp (2 * C4l) + 2 * C4w) + 2 * CA * C3) + |Cavg| * K6, by positivity,
    fun N B c i M hN hB hc hM h4 A s hAint hCavg hA hfint => ?_⟩
  have hγ := p12_pg6_gamma_pos hB hN
  have han := p12_pg6p2_aN_pos (α := α) hc hN
  have hpos := fun j => p12_pg6_plSpec_pos (α := α) hc (N := N) j
  have hM0 : 0 < M := by linarith
  set γ := gammaOf N B with hγdef
  set μ := plSpec α c N with hμ
  set W := partBfun B μ i with hWdef
  set M' := γ - M with hM'
  have hMM' : M < M' := by rw [hM']; linarith
  have hM2 : 2 * M ≤ M' := by rw [hM']; linarith
  have hIcc : ∀ m ∈ Icc M M', m ∈ Ioo 0 γ := fun m hm => ⟨by linarith [hm.1], by rw [hM'] at hm; linarith [hm.2]⟩
  have hWc : ContinuousOn W (Icc M M') := fun m hm =>
    (hWf N B c hN hB hc i m (hIcc m hm)).2.1.continuousAt.continuousWithinAt
  have hWi : IntervalIntegrable W volume M M' := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hMM'.le]; exact hWc
  have hW0 : ∀ m ∈ Icc M M', 0 < W m := fun m hm => (hWf N B c hN hB hc i m (hIcc m hm)).1
  set J := ∫ m in M..M', W m with hJ
  have hJ0 : 0 ≤ J := intervalIntegral.integral_nonneg hMM'.le (fun m hm => (hW0 m hm).le)
  have hAi : IntervalIntegrable (A) volume M M' :=
    ((hAint M' (by linarith)).mono_set (by
      rw [uIcc_of_le hMM'.le, uIcc_of_le (by linarith : (1:ℝ) ≤ M')]
      exact Icc_subset_Icc hM le_rfl))
  have hAW : IntervalIntegrable (fun m => A m * W m) volume M M' := by
    refine hAi.mul_continuousOn ?_
    rw [uIcc_of_le hMM'.le]; exact hWc
  set f : ℝ → ℝ := fun m => A m * W m * Efun β m * thetaN β B μ m with hf
  have hfi : IntervalIntegrable f volume M M' := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hMM'.le,
      integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hfint.mono_set (Ioo_subset_Ioo le_rfl (by rw [hM']; linarith))
  -- splitting
  have hR2 : ∫ m in M..M', f m = (∫ m in M..M', A m * W m) + ∫ m in M..M', (f m - A m * W m) := by
    rw [intervalIntegral.integral_sub hfi hAW]; ring
  have hR1 : ∫ m in M..M', A m * W m = (∫ m in M..M', (A m - s) * W m) + s * J := by
    have : ∫ m in M..M', (A m - s) * W m = (∫ m in M..M', A m * W m) - s * J := by
      rw [hJ, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hAW (hWi.const_mul s)]
      congr 1; ext m; ring
    linarith
  -- bound on R2
  have hR2b : |∫ m in M..M', (f m - A m * W m)| ≤ 2 * CA * C3 / M * J := by
    have hpt : ∀ m ∈ Ioo M M', |f m - A m * W m| ≤ 2 * CA * C3 / M * W m := by
      intro m hm
      have hmI := hIcc m ⟨hm.1.le, hm.2.le⟩
      obtain ⟨hP1, hP2⟩ := hPhi N B c hN hB hc m hmI
      have hAm := hA m (by linarith [hm.1])
      have hWm := hW0 m ⟨hm.1.le, hm.2.le⟩
      have hfeq : f m - A m * W m = A m * W m * (Efun β m * thetaN β B μ m - 1) := by
        simp only [hf]; ring
      rw [hfeq, abs_mul, abs_mul, abs_of_pos hWm, abs_of_nonneg (by linarith :
        0 ≤ Efun β m * thetaN β B μ m - 1)]
      have hsum : 1 / m + 1 / (γ - m) ≤ 2 / M := by
        have h1 : 1 / m ≤ 1 / M := one_div_le_one_div_of_le hM0 hm.1.le
        have h2 : 1 / (γ - m) ≤ 1 / M := by
          apply one_div_le_one_div_of_le hM0
          have := hm.2; rw [hM'] at this; linarith
        linarith [show 2 / M = 1 / M + 1 / M by ring]
      have hΦ1 : Efun β m * thetaN β B μ m - 1 ≤ C3 * (2 / M) := by
        nlinarith [mul_le_mul_of_nonneg_left hsum hC3.le]
      calc |A m| * W m * (Efun β m * thetaN β B μ m - 1) ≤
          (CA * W m) * (C3 * (2 / M)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hAm hWm.le) hΦ1 (by linarith) (by positivity)
        _ = _ := by ring
    have hb := intervalIntegral.norm_integral_le_of_norm_le
      (f := fun m => f m - A m * W m) (g := fun m => 2 * CA * C3 / M * W m) hMM'.le
      (by
        filter_upwards [Measure.ae_ne volume M'] with m hn hm
        rw [Real.norm_eq_abs]
        exact hpt m ⟨hm.1, lt_of_le_of_ne hm.2 hn⟩) (hWi.const_mul _)
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul] at hb
    exact hb
  -- bound on R1 by averaging
  have hWcd : ContDiffOn ℝ 1 W (Icc M M') :=
    (p12_pg6p2_W_cd μ hB hN hpos i).mono hIcc
  have hibp := p12_primitive_ibp (fun m => A m - s) 1 Cavg hCavg0
    (fun t ht => (hAint t ht).sub intervalIntegrable_const) hCavg M M' hM hMM'.le W hWcd
  have hWM : W M ≤ Real.exp (2 * C4l) / M * J := by
    have h1 := hWleft N B c i M hN hB hc hM h4
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine intervalIntegral.integral_mono_interval le_rfl (by linarith) hM2 ?_ hWi
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall (fun m hm => (hW0 m ⟨hm.1.le, hm.2⟩).le)
  have hWM' : W M' ≤ K6 * aN α c N * M / γ := by
    have := hWtop N B c i hN hB hc M' (by rw [hM']; linarith) (by rw [hM']; linarith)
    have e : (γ - M') / γ = M / γ := by rw [hM']; ring
    rw [e] at this
    calc W M' ≤ K6 * aN α c N * (M / γ) := this
      _ = K6 * aN α c N * M / γ := by ring
  have hdw : ∫ m in M..M', |derivWithin W (Icc M M') m| ≤ 2 * C4w / M * J := by
    have hcd := hWcd.continuousOn_derivWithin (uniqueDiffOn_Icc hMM') (le_refl 1)
    have hint : IntervalIntegrable (fun m => |derivWithin W (Icc M M') m|) volume M M' := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hMM'.le]
      exact hcd.abs
    calc ∫ m in M..M', |derivWithin W (Icc M M') m| ≤ ∫ m in M..M', 2 * C4w / M * W m := by
          refine intervalIntegral.integral_mono_on_of_le_Ioo hMM'.le hint (hWi.const_mul _) ?_
          intro m hm
          have hmI := hIcc m ⟨hm.1.le, hm.2.le⟩
          rw [derivWithin_of_mem_nhds (Icc_mem_nhds hm.1 hm.2)]
          obtain ⟨hp, -, hd⟩ := hWf N B c hN hB hc i m hmI
          refine hd.trans ?_
          have h1 : 1 / m ≤ 1 / M := one_div_le_one_div_of_le hM0 hm.1.le
          have h2 : 1 / (γ - m) ≤ 1 / M := by
            apply one_div_le_one_div_of_le hM0
            have := hm.2; rw [hM'] at this; linarith
          have : 1 / m + 1 / (γ - m) ≤ 2 / M := by
            have : 2 / M = 1 / M + 1 / M := by ring
            linarith
          calc C4w * W m * (1 / m + 1 / (γ - m)) ≤ C4w * W m * (2 / M) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = 2 * C4w / M * W m := by ring
      _ = 2 * C4w / M * J := by rw [intervalIntegral.integral_const_mul]
  have hR1b : |∫ m in M..M', (A m - s) * W m| ≤
      |Cavg| * ((Real.exp (2 * C4l) + 2 * C4w) / M * J + K6 * aN α c N * M / γ) := by
    refine hibp.trans ?_
    rw [abs_of_pos (hW0 M ⟨le_rfl, hMM'.le⟩), abs_of_pos (hW0 M' ⟨hMM'.le, le_rfl⟩)]
    have hbr : W M + W M' + ∫ m in M..M', |derivWithin W (Icc M M') m| ≤
        (Real.exp (2 * C4l) + 2 * C4w) / M * J + K6 * aN α c N * M / γ := by
      have : (Real.exp (2 * C4l) + 2 * C4w) / M * J =
          Real.exp (2 * C4l) / M * J + 2 * C4w / M * J := by ring
      linarith
    exact (mul_le_mul_of_nonneg_right (le_abs_self Cavg) (by
      have := hW0 M ⟨le_rfl, hMM'.le⟩
      have := hW0 M' ⟨hMM'.le, le_rfl⟩
      have : 0 ≤ ∫ m in M..M', |derivWithin W (Icc M M') m| :=
        intervalIntegral.integral_nonneg hMM'.le (fun m _ => abs_nonneg _)
      linarith)).trans (mul_le_mul_of_nonneg_left hbr (abs_nonneg _))
  -- assemble
  have e : (∫ m in M..M', f m) - s * J =
      (∫ m in M..M', (A m - s) * W m) + ∫ m in M..M', (f m - A m * W m) := by
    rw [hR2, hR1]; ring
  show |(∫ m in M..M', f m) - s * J| ≤ _
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have h1 := hR1b
  have h2 := hR2b
  have hdiff : ((|Cavg| * (Real.exp (2 * C4l) + 2 * C4w) + 2 * CA * C3) + |Cavg| * K6) / M * J +
      ((|Cavg| * (Real.exp (2 * C4l) + 2 * C4w) + 2 * CA * C3) + |Cavg| * K6) * aN α c N * M / γ -
      (|Cavg| * ((Real.exp (2 * C4l) + 2 * C4w) / M * J + K6 * aN α c N * M / γ) +
        2 * CA * C3 / M * J) =
      |Cavg| * K6 / M * J +
        (|Cavg| * (Real.exp (2 * C4l) + 2 * C4w) + 2 * CA * C3) * aN α c N * M / γ := by
    field_simp
    ring
  have hnn : 0 ≤ |Cavg| * K6 / M * J +
        (|Cavg| * (Real.exp (2 * C4l) + 2 * C4w) + 2 * CA * C3) * aN α c N * M / γ := by
    positivity
  simp only [hJ] at h1 h2 hnn hdiff
  linarith

private lemma p12_top {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (CA : ℝ) (hCA : 0 < CA) :
    ∃ K7 : ℝ, 0 < K7 ∧ ∀ (N B : ℕ) (c : ℝ) (i : Fin N) (M : ℝ),
      0 < N → 0 < B → 0 < c → 1 ≤ M → 4 * M ≤ gammaOf N B →
      ∀ A : ℝ → ℝ, (∀ m, 1 ≤ m → |A m| ≤ CA) →
      IntegrableOn (fun m => A m * partBfun B (plSpec α c N) i m * Efun β m *
        thetaN β B (plSpec α c N) m) (Ioo M (gammaOf N B)) →
      |∫ m in (gammaOf N B - M)..(gammaOf N B),
        A m * partBfun B (plSpec α c N) i m * Efun β m * thetaN β B (plSpec α c N) m| ≤
        K7 * aN α c N * M ^ 2 / gammaOf N B := by
  obtain ⟨K6, hK6, hW⟩ := p12_pg6p2_W_top hα
  obtain ⟨C3, hC3, hPhi⟩ := p12_pg6p2_Phi_bounds hα hβ0 hβ1
  refine ⟨CA * K6 * (1 + 2 * C3), by positivity, fun N B c i M hN hB hc hM h4 A hA hfint => ?_⟩
  have hγ := p12_pg6_gamma_pos hB hN
  have han := p12_pg6p2_aN_pos (α := α) hc hN
  have hpos := fun j => p12_pg6_plSpec_pos (α := α) (hc) (N := N) j
  set γ := gammaOf N B with hγdef
  set μ := plSpec α c N with hμ
  set f : ℝ → ℝ := fun m => A m * partBfun B μ i m * Efun β m * thetaN β B μ m with hf
  have hsub : Ioo (γ - M) γ ⊆ Ioo M γ := Ioo_subset_Ioo (by linarith) le_rfl
  have hMK : 0 < M := by linarith
  have hle : γ - M ≤ γ := by linarith
  rw [intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo]
  set Kpt := CA * K6 * (1 + 2 * C3) * aN α c N * M / γ with hKpt
  have hpt : ∀ m ∈ Ioo (γ - M) γ, |f m| ≤ Kpt := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := hm
    have hm0 : 0 < m := by linarith
    have hmI : m ∈ Ioo 0 γ := ⟨hm0, hm2⟩
    have hm3 : 1 ≤ m := by linarith
    have hgm : 0 < γ - m := by linarith
    have hAm := hA m hm3
    have hAm0 : 0 ≤ |A m| := abs_nonneg _
    have hWm := hW N B c i hN hB hc m (by linarith) hm2
    have hW0 := (p12_pg6p2_W_facts hα).choose_spec.2 N B c hN hB hc i m hmI
    obtain ⟨hP1, hP2⟩ := hPhi N B c hN hB hc m hmI
    have hΦ : Efun β m * thetaN β B μ m ≤ 1 + C3 + C3 / (γ - m) := by
      have : 1 / m ≤ 1 := by rw [div_le_one hm0]; exact hm3
      calc _ ≤ 1 + C3 * (1 / m + 1 / (γ - m)) := hP2
        _ ≤ 1 + C3 * (1 + 1 / (γ - m)) := by nlinarith
        _ = _ := by ring
    have hWm0 : 0 ≤ partBfun B μ i m := hW0.1.le
    have hfeq : f m = A m * partBfun B μ i m * (Efun β m * thetaN β B μ m) := by
      simp only [hf]; ring
    have hΦ0 : 0 ≤ Efun β m * thetaN β B μ m := by linarith
    rw [hfeq, abs_mul, abs_mul, abs_of_nonneg hWm0, abs_of_nonneg hΦ0]
    calc |A m| * partBfun B μ i m * (Efun β m * thetaN β B μ m)
        ≤ CA * (K6 * aN α c N * ((γ - m) / γ)) * (1 + C3 + C3 / (γ - m)) := by
          apply mul_le_mul (mul_le_mul hAm hWm hWm0 hCA.le) hΦ hΦ0 (by positivity)
      _ = CA * K6 * aN α c N * (((1 + C3) * (γ - m) + C3) / γ) := by
          field_simp
      _ ≤ CA * K6 * aN α c N * (((1 + C3) * M + C3) / γ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply div_le_div_of_nonneg_right _ hγ.le
          nlinarith
      _ ≤ Kpt := by
          rw [hKpt]
          have : (1 + C3) * M + C3 ≤ (1 + 2 * C3) * M := by nlinarith
          calc CA * K6 * aN α c N * (((1 + C3) * M + C3) / γ)
              ≤ CA * K6 * aN α c N * (((1 + 2 * C3) * M) / γ) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact div_le_div_of_nonneg_right this hγ.le
            _ = _ := by ring
  have h1 : ∫ m in Ioo (γ - M) γ, |f m| ≤ ∫ m in Ioo (γ - M) γ, Kpt :=
    setIntegral_mono_on (hfint.mono_set hsub).abs (integrableOn_const (by simp)) measurableSet_Ioo hpt
  have hnorm : |∫ m in Ioo (γ - M) γ, f m| ≤ ∫ m in Ioo (γ - M) γ, |f m| := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm f (μ := volume.restrict (Ioo (γ - M) γ)))
  refine (hnorm.trans h1).trans ?_
  rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le (by linarith)]
  rw [hKpt]
  have : γ - (γ - M) = M := by ring
  rw [this]
  have hfin : M * (CA * K6 * (1 + 2 * C3) * aN α c N * M / γ) =
      CA * K6 * (1 + 2 * C3) * aN α c N * M ^ 2 / γ := by ring
  rw [hfin]

private lemma p12_average_tail {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (CA Cavg : ℝ) (hCA : 0 < CA) (hCavg : 0 ≤ Cavg) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N B : ℕ) (c : ℝ) (i : Fin N) (M : ℝ),
      0 < N → 0 < B → 0 < c → 1 ≤ M → 4 * M ≤ gammaOf N B →
      ∀ (A : ℝ → ℝ) (s : ℝ),
      (∀ t, 1 ≤ t → IntervalIntegrable A volume 1 t) →
      (∀ t, 1 ≤ t → |∫ m in 1..t, (A m - s)| ≤ Cavg) →
      (∀ m, 1 ≤ m → |A m| ≤ CA) → |s| ≤ Real.pi →
      IntegrableOn (fun m => A m * partBfun B (plSpec α c N) i m * Efun β m *
        thetaN β B (plSpec α c N) m) (Ioo M (gammaOf N B)) →
      |(∫ m in Ioo M (gammaOf N B),
          A m * partBfun B (plSpec α c N) i m * Efun β m * thetaN β B (plSpec α c N) m) -
        s * ∫ m in Ioo M (gammaOf N B), partBfun B (plSpec α c N) i m| ≤
        K / M * (∫ m in Ioo M (gammaOf N B), partBfun B (plSpec α c N) i m) +
          K * aN α c N * M ^ 2 / gammaOf N B := by
  obtain ⟨K8, hK8, hmid⟩ := p12_mid hα hβ0 hβ1 CA Cavg hCA hCavg
  obtain ⟨K7, hK7, htop⟩ := p12_top hα hβ0 hβ1 CA hCA
  obtain ⟨K6, hK6, hWtop⟩ := p12_W_top_integral hα
  set K := K8 + K7 + Real.pi * K6
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, fun N B c i M hN hB hc hM h4 A s hAi hAv hA hs hf => ?_⟩
  have hγ := p12_pg6_gamma_pos hB hN
  have ha := p12_pg6p2_aN_pos (α := α) hc hN
  have hM0 : 0 < M := by linarith
  set γ := gammaOf N B
  set a := aN α c N
  set W := partBfun B (plSpec α c N) i
  set f := fun m => A m * W m * Efun β m * thetaN β B (plSpec α c N) m
  have hWi := p12_W_integrable hα hN hB hc i hM0
  have hsub1 : Ioo M (γ - M) ⊆ Ioo M γ := Ioo_subset_Ioo le_rfl (by linarith)
  have hsub2 : Ioo (γ - M) γ ⊆ Ioo M γ := Ioo_subset_Ioo (by linarith) le_rfl
  have hf1 : IntervalIntegrable f volume M (γ - M) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith), integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hf.mono_set hsub1
  have hf2 : IntervalIntegrable f volume (γ - M) γ := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith), integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hf.mono_set hsub2
  have hW1 : IntervalIntegrable W volume M (γ - M) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith), integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hWi.mono_set hsub1
  have hW2 : IntervalIntegrable W volume (γ - M) γ := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith), integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hWi.mono_set hsub2
  have hfs := intervalIntegral.integral_add_adjacent_intervals hf1 hf2
  have hWs := intervalIntegral.integral_add_adjacent_intervals hW1 hW2
  rw [intervalIntegral.integral_of_le (by linarith : M ≤ γ), integral_Ioc_eq_integral_Ioo] at hfs hWs
  set J := ∫ m in M..(γ - M), W m
  set T := ∫ m in (γ - M)..γ, W m
  have hJ : 0 ≤ J := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro m hm
    exact ((p12_pg6p2_W_facts hα).choose_spec.2 N B c hN hB hc i m
      ⟨by linarith [hm.1], by linarith [hm.2]⟩).1.le
  obtain ⟨hT, hTb⟩ := hWtop N B c i M hN hB hc hM0 h4
  change 0 ≤ T at hT
  change T / (γ * a) ≤ K6 * (M / γ) ^ 2 at hTb
  have hTbound : T ≤ K6 * a * M ^ 2 / γ := by
    rw [div_le_iff₀ (mul_pos hγ ha)] at hTb
    exact hTb.trans_eq (by field_simp <;> ring)
  have hm := hmid N B c i M hN hB hc hM h4 A s hAi hAv hA hf
  have ht := htop N B c i M hN hB hc hM h4 A hA hf
  change |(∫ m in M..(γ - M), f m) - s * J| ≤ K8 / M * J + K8 * a * M / γ at hm
  change |∫ m in (γ - M)..γ, f m| ≤ K7 * a * M ^ 2 / γ at ht
  have hst : |s * T| ≤ Real.pi * (K6 * a * M ^ 2 / γ) := by
    rw [abs_mul, abs_of_nonneg hT]
    exact mul_le_mul hs hTbound hT Real.pi_pos.le
  change |(∫ m in Ioo M γ, f m) - s * ∫ m in Ioo M γ, W m| ≤ _
  rw [← hfs, ← hWs]
  have he : (∫ m in M..(γ - M), f m) + (∫ m in (γ - M)..γ, f m) - s * (J + T) =
      ((∫ m in M..(γ - M), f m) - s * J) + ((∫ m in (γ - M)..γ, f m) - s * T) := by ring
  rw [he]
  refine (abs_add_le _ _).trans ((add_le_add hm ((abs_sub _ _).trans (add_le_add ht hst))).trans ?_)
  have hK8le : K8 ≤ K := by
    dsimp [K]
    linarith [mul_pos Real.pi_pos hK6]
  have hJb : K8 / M * J ≤ K / M * (J + T) := by
    apply mul_le_mul (div_le_div_of_nonneg_right hK8le hM0.le) (by linarith) hJ (by positivity)
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have hMb := mul_le_mul_of_nonneg_left hM2 (div_nonneg (mul_nonneg hK8.le ha.le) hγ.le)
  have hMb' : K8 * a * M / γ ≤ K8 * a * M ^ 2 / γ := by
    convert hMb using 1 <;> ring
  calc
    _ ≤ (K / M * (J + T) + K8 * a * M ^ 2 / γ) +
        (K7 * a * M ^ 2 / γ + Real.pi * (K6 * a * M ^ 2 / γ)) :=
      add_le_add (add_le_add hJb hMb') le_rfl
    _ = _ := by dsimp [K]; ring

private lemma p12_Ag_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ CA : ℝ, 0 < CA ∧ ∀ g m : ℝ, 1 ≤ m → |Ag β g m| ≤ CA := by
  obtain ⟨CZ, hZ⟩ := (lem_app_pl_age_i hβ0 hβ1).1
  obtain ⟨cE, CE, hcE, _, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  refine ⟨(|CZ| + 1) / cE, by positivity, fun g m hm => ?_⟩
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hEm : cE ≤ Efun β m := by simpa [min_eq_right hm] using (hE m hm0).1
  have hEp : 0 < Efun β m := hcE.trans_le hEm
  rw [Ag, abs_div, abs_of_pos hEp]
  exact (div_le_div_of_nonneg_right ((hZ _ g (vsh_Qm hβ0 hβ1 hm0).1).trans
    (by linarith [le_abs_self CZ])) hEp.le).trans
    (div_le_div_of_nonneg_left (by positivity) hcE hEm)

private lemma p12_Ag_tail {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N B : ℕ) (c : ℝ) (i : Fin N) (M : ℝ),
      0 < N → 0 < B → 0 < c → 1 ≤ M → 4 * M ≤ gammaOf N B →
      ∀ g : ℝ, g ≠ 0 →
      IntegrableOn (fun m => Wpart β B (plSpec α c N) i m * Zg β g (Qm β m))
        (Ioo M (gammaOf N B)) →
      |calVpart β B (plSpec α c N) i M (gammaOf N B) g -
        tailMass B (plSpec α c N) i M * Real.sign g| ≤
      (1 + |Real.log (|g|)|) * (K / M * tailMass B (plSpec α c N) i M +
        K * (gammaOf N B * aN α c N / Real.sqrt (gammaOf N B * plSpec α c N i)) *
          (M / gammaOf N B) ^ 2) := by
  obtain ⟨CA, hCA, hA⟩ := p12_Ag_bound hβ0 hβ1
  obtain ⟨Cavg, hAv⟩ := lem_app_pl_age_ii hβ0 hβ1 1 one_pos
  obtain ⟨K, hK, htail⟩ := p12_average_tail hα hβ0 hβ1 CA (|Cavg| + 1) hCA (by positivity)
  refine ⟨K / Real.pi, by positivity, fun N B c i M hN hB hc hM h4 g hg hf => ?_⟩
  have hγ := p12_pg6_gamma_pos hB hN
  have hμ := p12_pg6_plSpec_pos (α := α) hc i
  have hM0 : 0 < M := by linarith
  set γ := gammaOf N B
  set H := 1 + |Real.log (|g|)|
  have hH1 : 1 ≤ H := by dsimp [H]; linarith [abs_nonneg (Real.log |g|)]
  have hH : 0 < H := zero_lt_one.trans_le hH1
  set S := Real.sqrt (γ * plSpec α c N i)
  have hS : 0 < S := Real.sqrt_pos.2 (mul_pos hγ hμ)
  set A := fun m => Ag β g m / H
  set s := Real.pi * Real.sign g / H
  have hAi : ∀ t, 1 ≤ t → IntervalIntegrable A volume 1 t := fun t ht =>
    ((hAv g hg t ht).1).div_const H
  have hAp : ∀ t, 1 ≤ t → |∫ m in 1..t, (A m - s)| ≤ |Cavg| + 1 := by
    intro t ht
    have he : (fun m => A m - s) = fun m => (Ag β g m - Real.pi * Real.sign g) / H := by
      funext m; dsimp [A, s]; ring
    rw [he, intervalIntegral.integral_div, abs_div, abs_of_pos hH, div_le_iff₀ hH]
    exact ((hAv g hg t ht).2).trans (by nlinarith [le_abs_self Cavg])
  have hAb : ∀ m, 1 ≤ m → |A m| ≤ CA := by
    intro m hm
    dsimp [A]
    rw [abs_div, abs_of_pos hH]
    exact (div_le_div_of_nonneg_right (hA g m hm) hH.le).trans (div_le_self hCA.le hH1)
  have hs : |s| ≤ Real.pi := by
    dsimp [s]
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hH]
    have hsign : |Real.sign g| ≤ 1 := by
      rcases lt_trichotomy g 0 with hn | he | hp <;> simp [Real.sign_of_neg, Real.sign_of_pos, *]
    exact (div_le_div_of_nonneg_right (mul_le_of_le_one_right Real.pi_pos.le hsign) hH.le).trans
      (div_le_self Real.pi_pos.le hH1)
  set f := fun m => A m * partBfun B (plSpec α c N) i m * Efun β m * thetaN β B (plSpec α c N) m
  have he : ∀ m ∈ Ioo M γ,
      f m = (S / H) * (Wpart β B (plSpec α c N) i m * Zg β g (Qm β m)) := by
    intro m hm
    have hmI : m ∈ Ioo 0 γ := ⟨hM0.trans hm.1, hm.2⟩
    have hEp := vsh_Efun_pos hβ0 hβ1 hmI.1
    have hw := Wpart_mul_Zg_factor β B (plSpec α c N) i m g hEp.ne'
    have hj := Jrow_eq_partBfun B N hN hB _ i hμ m hmI
      (p12_pg6p2_Lam_hasDeriv _ hB hN (p12_pg6_plSpec_pos hc) hmI).1
    change Jrow B (plSpec α c N) i m = partBfun B (plSpec α c N) i m / S at hj
    rw [hw, hj]
    dsimp only [f, A]
    field_simp [hS.ne', hH.ne'] <;> ring
  have hfi : IntegrableOn f (Ioo M γ) := by
    refine (hf.const_mul (S / H)).congr ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
    exact Eventually.of_forall (fun m hm => (he m hm).symm)
  have hi := htail N B c i M hN hB hc hM h4 A s hAi hAp hAb hs hfi
  have hfval : ∫ m in Ioo M γ, f m =
      (S / H) * (Real.pi * calVpart β B (plSpec α c N) i M γ g) := by
    rw [show (∫ m in Ioo M γ, f m) =
      ∫ m in Ioo M γ, (S / H) * (Wpart β B (plSpec α c N) i m * Zg β g (Qm β m)) from
      setIntegral_congr_fun measurableSet_Ioo he, integral_const_mul, calVpart]
    field_simp
  have hmval : (∫ m in Ioo M γ, partBfun B (plSpec α c N) i m) =
      S * tailMass B (plSpec α c N) i M := by
    have hm := p12_mass_eq (α := α) hN hB hc i hM0
    change tailMass B (plSpec α c N) i M =
      (∫ m in Ioo M γ, partBfun B (plSpec α c N) i m) / S at hm
    rw [hm]
    field_simp [hS.ne']
  change |(∫ m in Ioo M γ, f m) - s * ∫ m in Ioo M γ, partBfun B (plSpec α c N) i m| ≤ _ at hi
  rw [hfval, hmval] at hi
  have hfac : (S / H) * (Real.pi * calVpart β B (plSpec α c N) i M γ g) -
      s * (S * tailMass B (plSpec α c N) i M) =
      (S * Real.pi / H) * (calVpart β B (plSpec α c N) i M γ g -
        tailMass B (plSpec α c N) i M * Real.sign g) := by dsimp [s]; ring
  rw [hfac, abs_mul, abs_of_pos (by positivity : 0 < S * Real.pi / H)] at hi
  have ht := mul_le_mul_of_nonneg_left hi (show 0 ≤ H / (S * Real.pi) by positivity)
  have heleft : H / (S * Real.pi) * ((S * Real.pi / H) *
      |calVpart β B (plSpec α c N) i M γ g - tailMass B (plSpec α c N) i M * Real.sign g|) =
      |calVpart β B (plSpec α c N) i M γ g - tailMass B (plSpec α c N) i M * Real.sign g| := by
    field_simp
  rw [heleft] at ht
  refine ht.trans_eq ?_
  change H / (S * Real.pi) * (K / M * (S * tailMass B (plSpec α c N) i M) +
      K * aN α c N * M ^ 2 / γ) =
    H * ((K / Real.pi) / M * tailMass B (plSpec α c N) i M +
      (K / Real.pi) * (γ * aN α c N / S) * (M / γ) ^ 2)
  field_simp [hS.ne', hH.ne', hγ.ne', hM0.ne', Real.pi_ne_zero] <;> ring

private lemma p12_Zg_sq {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (q : ℝ) :
    Integrable (fun g : ℝ => Zg β g q ^ 2) (gaussianReal 0 1) ∧
      ∫ g : ℝ, Zg β g q ^ 2 ∂(gaussianReal 0 1) ≤ (Real.sqrt q) ^ 2 := by
  rcases lt_or_ge 0 q with hq | hq
  · obtain ⟨h1, h2⟩ := (lem_app_pl_age_i hβ0 hβ1).2 q hq
    refine ⟨h1, ?_⟩
    rwa [Real.sq_sqrt hq.le]
  · have hz : ∀ g, Zg β g q = 0 := fun g => by
      unfold Zg
      rw [Real.sqrt_eq_zero_of_nonpos hq, zero_mul]
    simp [hz]

private lemma p12_minkowski {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (W Q : ℝ → ℝ) (S : Set ℝ) (hS : MeasurableSet S)
    (hI : IntegrableOn (fun m => |W m| * Real.sqrt (Q m)) S)
    (hF : AEStronglyMeasurable (fun q : ℝ × ℝ => W q.1 * Zg β q.2 (Q q.1))
      ((volume.restrict S).prod (gaussianReal 0 1))) :
    (∀ᵐ g ∂(gaussianReal 0 1), IntegrableOn (fun m => W m * Zg β g (Q m)) S) ∧
    Integrable (fun g => (∫ m in S, W m * Zg β g (Q m)) ^ 2) (gaussianReal 0 1) ∧
      l2Norm (fun g => ∫ m in S, W m * Zg β g (Q m)) ≤
        ∫ m in S, |W m| * Real.sqrt (Q m) := by
  have hbound : ∀ m, l2Norm (fun g => W m * Zg β g (Q m)) ≤
      |W m| * Real.sqrt (Q m) := by
    intro m
    unfold l2Norm
    have h1 : ∫ g, (W m * Zg β g (Q m)) ^ 2 ∂(gaussianReal 0 1) =
        W m ^ 2 * ∫ g, Zg β g (Q m) ^ 2 ∂(gaussianReal 0 1) := by
      simp_rw [mul_pow]
      exact integral_const_mul _ _
    rw [h1]
    calc
      _ ≤ Real.sqrt (W m ^ 2 * (Real.sqrt (Q m)) ^ 2) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
          (p12_Zg_sq hβ0 hβ1 (Q m)).2 (sq_nonneg _))
      _ = |W m| * Real.sqrt (Q m) := by
        rw [← mul_pow, Real.sqrt_sq_eq_abs, abs_mul,
          abs_of_nonneg (Real.sqrt_nonneg _)]
  have hmeas : AEStronglyMeasurable
      (fun m => l2Norm (fun g => W m * Zg β g (Q m))) (volume.restrict S) := by
    have h := (hF.mul hF).integral_prod_right'
    have h2 := Real.continuous_sqrt.comp_aestronglyMeasurable h
    refine h2.congr (Eventually.of_forall fun m => ?_)
    simp only [l2Norm, sq, Pi.mul_apply]
  have hint : IntegrableOn (fun m => l2Norm (fun g => W m * Zg β g (Q m))) S := by
    refine Integrable.mono' hI hmeas (Eventually.of_forall fun m => ?_)
    rw [Real.norm_of_nonneg (by unfold l2Norm; exact Real.sqrt_nonneg _)]
    exact hbound m
  have hsq : ∀ᵐ m ∂(volume.restrict S),
      Integrable (fun g => (W m * Zg β g (Q m)) ^ 2) (gaussianReal 0 1) :=
    Eventually.of_forall fun m => by
      simp_rw [mul_pow]
      exact (p12_Zg_sq hβ0 hβ1 (Q m)).1.const_mul _
  obtain ⟨hsections, hsquare, hnorm⟩ := l2_minkowski_integral S hS
    (fun m g => W m * Zg β g (Q m)) hF hsq hint
  refine ⟨hsections, hsquare, hnorm.trans ?_⟩
  exact integral_mono_ae hint hI
    (Eventually.of_forall fun m => by
      exact hbound m)

private lemma p12_tail_lower {α : ℝ} (hα : 0 < α) :
    ∃ d : ℝ, 0 < d ∧ ∀ {β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ},
      assum_app_pl_regime α β N B c → ∀ M : ℝ, 1 ≤ M →
      ∀ᶠ n in atTop, ∀ i : Fin (N n),
        d * (Real.sqrt (gammaOf (N n) (B n)) * rowFrac i ^ (α / 2)) ≤
          tailMass (B n) (plSpec α (c n) (N n)) i M := by
  obtain ⟨C, K, _, hC, hK, _, herr⟩ := p12_mass_error hα
  obtain ⟨d, hd, hlow⟩ := p12_pg6p2_psi_lower hα
  have hc0 : 0 < c0 := by unfold c0; positivity
  refine ⟨d / (2 * c0), by positivity, fun {β N B c} R M hM => ?_⟩
  have hM0 : 0 < M := by linarith
  have hB : Tendsto (fun n => (B n : ℝ) * M) atTop atTop := R.hB.atTop_mul_const hM0
  have h1 : Tendsto (fun n => C / ((B n : ℝ) * M)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hB
  have h2 : Tendsto (fun n => K * (M / gammaOf (N n) (B n)) ^ 2) atTop (𝓝 0) := by
    have hz : Tendsto (fun n => M / gammaOf (N n) (B n)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop R.hγ
    simpa using (hz.pow 2).const_mul K
  have hsmall : ∀ᶠ n in atTop, C / ((B n : ℝ) * M) + K * (M / gammaOf (N n) (B n)) ^ 2 ≤ 1 / 2 :=
    (by simpa using (h1.add h2) : Tendsto _ atTop (𝓝 (0 : ℝ))).eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hsmall, R.hB.eventually_ge_atTop 2, hB.eventually_ge_atTop C,
    R.hγ.eventually_ge_atTop (4 * M)] with n hn hBn hCB h4 i
  have hγ := p12_pg6_gamma_pos (R.hBpos n) (R.hNpos n)
  have hB2 : 2 ≤ B n := by exact_mod_cast hBn
  change 4 * M ≤ gammaOf (N n) (B n) at h4
  have hx : rowFrac i ∈ Ioc (0 : ℝ) 1 :=
    ⟨div_pos (p12_pg6_rowNum_pos _) (by exact_mod_cast R.hNpos n),
      (div_le_one (by exact_mod_cast R.hNpos n)).2 (p12_pg6p2_rowNum_le _)⟩
  have hψd := hlow _ hx _ (div_pos hM0 hγ)
    (by rw [div_le_iff₀ hγ]; linarith : M / gammaOf (N n) (B n) ≤ 1 / 4)
  set S := Real.sqrt (gammaOf (N n) (B n)) * rowFrac i ^ (α / 2)
  set ψ := psiRes α (M / gammaOf (N n) (B n)) (rowFrac i)
  have hS : 0 < S := mul_pos (Real.sqrt_pos.2 hγ) (Real.rpow_pos_of_pos hx.1 _)
  have hψ : 0 < ψ := hd.trans_le hψd
  have hb := (abs_le.1 ((herr (N n) (B n) (c n) i M (R.hNpos n) hB2 (R.hcpos n)
    hM h4 hCB).trans hn)).1
  have hr : 1 / 2 ≤ tailMass (B n) (plSpec α (c n) (N n)) i M / (S * ψ / c0) := by linarith
  rw [le_div_iff₀ (by positivity : 0 < S * ψ / c0)] at hr
  have hSd : 0 ≤ S / (2 * c0) := by positivity
  have hψbound := mul_le_mul_of_nonneg_left hψd hSd
  change d / (2 * c0) * S ≤ _
  nlinarith [show S / (2 * c0) * ψ = 1 / 2 * (S * ψ / c0) by ring,
    show S / (2 * c0) * d = d / (2 * c0) * S by ring]

private lemma p12_sign_meas : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const)

private lemma p12_l2_envelope (f : ℝ → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hf : AEStronglyMeasurable f (gaussianReal 0 1))
    (hb : ∀ᵐ g ∂(gaussianReal 0 1), |f g| ≤ R * (1 + |Real.log (|g|)|)) :
    Integrable (fun g => f g ^ 2) (gaussianReal 0 1) ∧
      l2Norm f ≤ R * l2Norm (fun g => 1 + |Real.log (|g|)|) := by
  have hmaj : Integrable (fun g : ℝ => R ^ 2 * (1 + |Real.log (|g|)|) ^ 2) (gaussianReal 0 1) :=
    log_abs_sq_integrable.const_mul _
  have hs : ∀ᵐ g ∂(gaussianReal 0 1), f g ^ 2 ≤ R ^ 2 * (1 + |Real.log (|g|)|) ^ 2 := by
    filter_upwards [hb] with g hg
    have := (sq_le_sq₀ (abs_nonneg (f g)) (by positivity : 0 ≤ R * (1 + |Real.log (|g|)|))).2 hg
    simpa only [sq_abs, mul_pow] using this
  have hi : Integrable (fun g => f g ^ 2) (gaussianReal 0 1) := by
    refine hmaj.mono' (hf.pow 2) ?_
    filter_upwards [hs] with g hg
    rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f g))]
  refine ⟨hi, ?_⟩
  unfold l2Norm
  calc
    _ ≤ Real.sqrt (∫ g, R ^ 2 * (1 + |Real.log (|g|)|) ^ 2 ∂(gaussianReal 0 1)) :=
      Real.sqrt_le_sqrt (integral_mono_ae hi hmaj hs)
    _ = _ := by rw [integral_const_mul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hR]

/-- Tail `L²` averaging: for `M ≥ M₀`,
`‖(1/π)∫_M^γ W_i 𝒵_g dm - B_i^{[M]} sign g‖_{L²} ≤ (C/M + o(1)) B_i^{[M]}`, uniformly over the rows
(task L-G.7b; proof step of `lem:app-pl-vector`, l.1949-1957, using `lem_app_pl_tail`-type averaging
with `𝒥_i` and `lem_app_pl_age_ii` at `m₀ = 1`; snapshot cr-2026-10-23). -/
theorem tail_L2_averaging {α β : ℝ} :
    ∃ C M₀ : ℝ, 0 < M₀ ∧ ∀ (N B : ℕ → ℕ) (c : ℕ → ℝ), assum_app_pl_regime α β N B c →
      ∀ M : ℝ, M₀ ≤ M → ∀ ε > 0, ∀ᶠ n in atTop, ∀ i : Fin (N n),
        IntegrableOn (Jrow (B n) (plSpec α (c n) (N n)) i) (Ioo M (gammaOf (N n) (B n))) ∧
        Integrable (fun g => (calVpart β (B n) (plSpec α (c n) (N n)) i M (gammaOf (N n) (B n)) g -
            tailMass (B n) (plSpec α (c n) (N n)) i M * Real.sign g) ^ 2) (gaussianReal 0 1) ∧
        l2Norm (fun g => calVpart β (B n) (plSpec α (c n) (N n)) i M (gammaOf (N n) (B n)) g -
            tailMass (B n) (plSpec α (c n) (N n)) i M * Real.sign g) ≤
          (C / M + ε) * tailMass (B n) (plSpec α (c n) (N n)) i M := by
  by_cases hab : 0 < α ∧ 0 < β ∧ β < 1
  · obtain ⟨K, hK, hdet⟩ := p12_Ag_tail hab.1 hab.2.1 hab.2.2
    obtain ⟨d, hd, hlow⟩ := p12_tail_lower hab.1
    set L := l2Norm (fun g => 1 + |Real.log (|g|)|) + 1
    have hL : 0 < L := by dsimp [L, l2Norm]; positivity
    refine ⟨K * L, 1, one_pos, fun N B c R M hM ε hε => ?_⟩
    have hM0 : 0 < M := zero_lt_one.trans_le hM
    have hη : Tendsto (fun n => K * L * (M / gammaOf (N n) (B n)) ^ 2) atTop (𝓝 0) := by
      have hz : Tendsto (fun n => M / gammaOf (N n) (B n)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop R.hγ
      simpa using (hz.pow 2).const_mul (K * L)
    have hsmall : ∀ᶠ n in atTop, K * L * (M / gammaOf (N n) (B n)) ^ 2 ≤ ε * d :=
      hη.eventually (eventually_le_nhds (mul_pos hε hd))
    filter_upwards [hlow R M hM, Wpart_integrable_measurable R,
      R.hγ.eventually_ge_atTop (4 * M), hsmall] with n hlo hmeas h4 hεn i
    have hγ := p12_pg6_gamma_pos (R.hBpos n) (R.hNpos n)
    change 4 * M ≤ gammaOf (N n) (B n) at h4
    set γ := gammaOf (N n) (B n)
    set μ := plSpec α (c n) (N n)
    set T := tailMass (B n) μ i M
    set S := Real.sqrt γ * rowFrac i ^ (α / 2)
    have hx : 0 < rowFrac i :=
      div_pos (p12_pg6_rowNum_pos _) (by exact_mod_cast R.hNpos n)
    have hS : 0 < S := mul_pos (Real.sqrt_pos.2 hγ) (Real.rpow_pos_of_pos hx _)
    have hTl : d * S ≤ T := hlo i
    have hT : 0 < T := (mul_pos hd hS).trans_le hTl
    have hsub : Ioo M γ ⊆ Ioo 0 γ := Ioo_subset_Ioo hM0.le le_rfl
    obtain ⟨hI, hW, hF⟩ := hmeas i
    have hFr : AEStronglyMeasurable
        (fun q : ℝ × ℝ => Wpart β (B n) μ i q.1 * Zg β q.2 (Qm β q.1))
        ((volume.restrict (Ioo M γ)).prod (gaussianReal 0 1)) :=
      hF.mono_measure (Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl)
    have hIr : IntegrableOn (fun m => |Wpart β (B n) μ i m| * Real.sqrt (Qm β m)) (Ioo M γ) :=
      hI.mono_set hsub
    obtain ⟨hsections, _, _⟩ := p12_minkowski R.hβ0 R.hβ1 (Wpart β (B n) μ i) (Qm β)
      (Ioo M γ) measurableSet_Ioo hIr hFr
    set f := fun g => calVpart β (B n) μ i M γ g - T * Real.sign g
    set E := K / M * T + K * S * (M / γ) ^ 2
    have hE : 0 ≤ E := by dsimp [E]; positivity
    have hfm : AEStronglyMeasurable f (gaussianReal 0 1) :=
      (hFr.prod_swap.integral_prod_right'.const_mul Real.pi⁻¹).sub
        (p12_sign_meas.aestronglyMeasurable.const_mul T)
    have hfb : ∀ᵐ g ∂(gaussianReal 0 1), |f g| ≤ E * (1 + |Real.log (|g|)|) := by
      filter_upwards [hsections] with g hg
      by_cases hg0 : g = 0
      · subst g
        have hz : f 0 = 0 := by simp [f, calVpart, Zg]
        rw [hz, abs_zero]
        exact mul_nonneg hE (by positivity)
      · have hb := hdet (N n) (B n) (c n) i M (R.hNpos n) (R.hBpos n) (R.hcpos n)
          hM h4 g hg0 hg
        rw [p12_scale (α := α) (R.hNpos n) (R.hBpos n) (R.hcpos n) i] at hb
        exact hb.trans_eq (by dsimp [E, f, T, S, μ, γ]; ring)
    obtain ⟨hsq, hnorm⟩ := p12_l2_envelope f hE hfm hfb
    refine ⟨p12_J_integrable R.hα (R.hNpos n) (R.hBpos n) (R.hcpos n) i hM0, hsq, ?_⟩
    change l2Norm f ≤ (K * L / M + ε) * T
    calc
      l2Norm f ≤ E * l2Norm (fun g => 1 + |Real.log (|g|)|) := hnorm
      _ ≤ E * L := mul_le_mul_of_nonneg_left (by dsimp [L]; linarith) hE
      _ ≤ (K * L / M + ε) * T := by
        have h1 := mul_le_mul_of_nonneg_right hεn hS.le
        have h2 := mul_le_mul_of_nonneg_left hTl hε.le
        have he : E * L = K * L / M * T + (K * L * (M / γ) ^ 2) * S := by dsimp [E]; ring
        rw [he]
        change K * L * (M / γ) ^ 2 * S ≤ ε * d * S at h1
        nlinarith
  · exact ⟨1, 1, one_pos, fun N B c R => (hab ⟨R.hα, R.hβ0, R.hβ1⟩).elim⟩

/-- `B_i^{[M]} = (1+o(1)) √γ x^{α/2} Ψ_α^{[M/γ]}(x) / c₀` (task L-G.7b; proof step of `lem:app-pl-vector`,
l.1957-1961, from `lem_app_pl_tail` and `eqn:app-pl-Bi-bulk`; snapshot cr-2026-10-23). -/
theorem tailMass_asymp {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (i : ∀ n, Fin (N n)) (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) (M : ℝ) (hM : 0 < M) (hM1 : 1 ≤ M) :
    Tendsto (fun n => tailMass (B n) (plSpec α (c n) (N n)) (i n) M /
        (Real.sqrt (gammaOf (N n) (B n)) * rowFrac (i n) ^ (α / 2) *
          psiRes α (M / gammaOf (N n) (B n)) (rowFrac (i n)) / c0)) atTop (𝓝 1) := by
  obtain ⟨C, K, d, hC, hK, hd, herr⟩ := p12_mass_error R.hα
  have hB : Tendsto (fun n => (B n : ℝ) * M) atTop atTop :=
    R.hB.atTop_mul_const hM
  have h1 : Tendsto (fun n => C / ((B n : ℝ) * M)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hB
  have h2 : Tendsto (fun n => K * (M / gammaOf (N n) (B n)) ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul
      ((tendsto_const_nhds.div_atTop R.hγ (a := M)).pow 2) :
      Tendsto (fun n => K * (M / gammaOf (N n) (B n)) ^ 2) atTop (𝓝 (K * 0 ^ 2)))
  have hbnd : ∀ᶠ n in atTop,
      |tailMass (B n) (plSpec α (c n) (N n)) (i n) M /
        (Real.sqrt (gammaOf (N n) (B n)) * rowFrac (i n) ^ (α / 2) *
          psiRes α (M / gammaOf (N n) (B n)) (rowFrac (i n)) / c0) - 1| ≤
        C / ((B n : ℝ) * M) + K * (M / gammaOf (N n) (B n)) ^ 2 := by
    filter_upwards [R.hB.eventually_ge_atTop 2, R.hγ.eventually_ge_atTop (4 * M),
      hB.eventually_ge_atTop C] with n hn hγ hCB
    have hBn : 2 ≤ B n := by exact_mod_cast hn
    exact herr (N n) (B n) (c n) (i n) M (R.hNpos n) hBn (R.hcpos n) hM1 hγ hCB
  have hz : Tendsto (fun n => tailMass (B n) (plSpec α (c n) (N n)) (i n) M /
      (Real.sqrt (gammaOf (N n) (B n)) * rowFrac (i n) ^ (α / 2) *
        psiRes α (M / gammaOf (N n) (B n)) (rowFrac (i n)) / c0) - 1) atTop (𝓝 0) :=
    squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using hbnd)
      (by simpa using h1.add h2)
  have ht := hz.add_const 1
  simpa using ht

/-- `B_i^{[M]} = b + o(1+b)` (task L-G.7b; proof step of `lem:app-pl-vector`, l.1962-1966, via
`lem_app_pl_cutoff_iii`; snapshot cr-2026-10-23). -/
theorem tailMass_sub_b {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (i : ∀ n, Fin (N n)) (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) (M : ℝ) (hM : 0 < M) (hM1 : 1 ≤ M) :
    Tendsto (fun n => (tailMass (B n) (plSpec α (c n) (N n)) (i n) M - bCoef α (B n) (i n)) /
        (1 + bCoef α (B n) (i n))) atTop (𝓝 0) := by
  set q : ℕ → ℝ := fun n => Real.sqrt (gammaOf (N n) (B n)) * rowFrac (i n) ^ (α / 2) *
    psiRes α (M / gammaOf (N n) (B n)) (rowFrac (i n)) / c0
  have hc0 : 0 < c0 := by unfold c0; positivity
  have hx01 : ∀ n, rowFrac (i n) ∈ Ioc (0 : ℝ) 1 := fun n =>
    ⟨div_pos (p12_pg6_rowNum_pos _) (by exact_mod_cast R.hNpos n),
      (div_le_one (by exact_mod_cast R.hNpos n)).2 (p12_pg6p2_rowNum_le _)⟩
  have hq : ∀ᶠ n in atTop, 0 < q n ∧ q n ≤ bCoef α (B n) (i n) := by
    obtain ⟨d, hd, hlow⟩ := p12_pg6p2_psi_lower R.hα
    filter_upwards [R.hγ.eventually_ge_atTop (4 * M)] with n hn
    change 4 * M ≤ gammaOf (N n) (B n) at hn
    have hxpos := (hx01 n).1
    have hγ := p12_pg6_gamma_pos (R.hBpos n) (R.hNpos n)
    have hη : M / gammaOf (N n) (B n) ≤ 1 / 4 := by
      rw [div_le_iff₀ hγ]; linarith
    have hψ : 0 < psiRes α (M / gammaOf (N n) (B n)) (rowFrac (i n)) :=
      hd.trans_le (hlow _ (hx01 n) _ (div_pos hM hγ) hη)
    have hle := (p12_pg6p3_res_bounds R.hα (hx01 n) (div_nonneg hM.le hγ.le)
      (by linarith : M / gammaOf (N n) (B n) ≤ 1)).2
    refine ⟨by dsimp [q]; positivity, ?_⟩
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hle (by positivity)) hc0.le
  apply p12_normalized_transfer hq (tailMass_asymp R hα1 i hi hx M hM hM1)
  have hn := p12_profile_normalized R hα1 i hi hx M hM
  refine hn.congr (fun n => ?_)
  have hs := (p12_cutW_scale (α := α) (R.hNpos n) (R.hBpos n) R.hβ0 R.hβ1 (i n)).2
  set A := Real.sqrt (gammaOf (N n) (B n)) * rowFrac (i n) ^ (α / 2)
  set D := c0 * Real.sqrt (sPow β 2) * cutW β α 1 (N n) (B n) (i n)
  set P := profPsi α (rowFrac (i n))
  set Q := psiRes α (M / gammaOf (N n) (B n)) (rowFrac (i n))
  change A * D = c0 at hs
  have hγ := p12_pg6_gamma_pos (R.hBpos n) (R.hNpos n)
  have hA : 0 < A := mul_pos (Real.sqrt_pos.2 hγ) (Real.rpow_pos_of_pos (hx01 n).1 _)
  have hD : 0 < D := (mul_pos_iff_of_pos_left hA).1 (hs.symm ▸ hc0)
  have hP : 0 < P := lem_app_pl_Psi_i_pos R.hα _ (hx01 n)
  change (Q - P) / (D + P) = (A * Q / c0 - A * P / c0) / (1 + A * P / c0)
  rw [← hs]
  field_simp [hA.ne', hD.ne', (add_pos hD hP).ne'] <;> ring

private lemma p11_Zg_sq {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (q : ℝ) :
    Integrable (fun g : ℝ => Zg β g q ^ 2) (gaussianReal 0 1) ∧
      ∫ g : ℝ, Zg β g q ^ 2 ∂(gaussianReal 0 1) ≤ (Real.sqrt q) ^ 2 := by
  rcases lt_or_ge 0 q with hq | hq
  · obtain ⟨h1, h2⟩ := (lem_app_pl_age_i hβ0 hβ1).2 q hq
    refine ⟨h1, ?_⟩
    rwa [Real.sq_sqrt hq.le]
  · have hz : ∀ g, Zg β g q = 0 := fun g => by
      unfold Zg
      rw [Real.sqrt_eq_zero_of_nonpos hq, zero_mul]
    simp [hz]

private lemma p11_minkowski_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (W Q : ℝ → ℝ) (S : Set ℝ) (hS : MeasurableSet S)
    (hI : IntegrableOn (fun m => |W m| * Real.sqrt (Q m)) S)
    (hF : AEStronglyMeasurable (fun q : ℝ × ℝ => W q.1 * Zg β q.2 (Q q.1))
      ((volume.restrict S).prod (gaussianReal 0 1))) :
    Integrable (fun g => (∫ m in S, W m * Zg β g (Q m)) ^ 2) (gaussianReal 0 1) ∧
      l2Norm (fun g => ∫ m in S, W m * Zg β g (Q m)) ≤
        ∫ m in S, |W m| * Real.sqrt (Q m) := by
  have hbound : ∀ m, l2Norm (fun g => W m * Zg β g (Q m)) ≤
      |W m| * Real.sqrt (Q m) := by
    intro m
    unfold l2Norm
    have h1 : ∫ g, (W m * Zg β g (Q m)) ^ 2 ∂(gaussianReal 0 1) =
        W m ^ 2 * ∫ g, Zg β g (Q m) ^ 2 ∂(gaussianReal 0 1) := by
      simp_rw [mul_pow]
      exact integral_const_mul _ _
    rw [h1]
    calc
      _ ≤ Real.sqrt (W m ^ 2 * (Real.sqrt (Q m)) ^ 2) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
          (p11_Zg_sq hβ0 hβ1 (Q m)).2 (sq_nonneg _))
      _ = |W m| * Real.sqrt (Q m) := by
        rw [← mul_pow, Real.sqrt_sq_eq_abs, abs_mul,
          abs_of_nonneg (Real.sqrt_nonneg _)]
  have hmeas : AEStronglyMeasurable
      (fun m => l2Norm (fun g => W m * Zg β g (Q m))) (volume.restrict S) := by
    have h := (hF.mul hF).integral_prod_right'
    have h2 := Real.continuous_sqrt.comp_aestronglyMeasurable h
    refine h2.congr (Eventually.of_forall fun m => ?_)
    simp only [l2Norm, sq, Pi.mul_apply]
  have hint : IntegrableOn (fun m => l2Norm (fun g => W m * Zg β g (Q m))) S := by
    refine Integrable.mono' hI hmeas (Eventually.of_forall fun m => ?_)
    rw [Real.norm_of_nonneg (by unfold l2Norm; exact Real.sqrt_nonneg _)]
    exact hbound m
  have hsq : ∀ᵐ m ∂(volume.restrict S),
      Integrable (fun g => (W m * Zg β g (Q m)) ^ 2) (gaussianReal 0 1) :=
    Eventually.of_forall fun m => by
      simp_rw [mul_pow]
      exact (p11_Zg_sq hβ0 hβ1 (Q m)).1.const_mul _
  obtain ⟨-, hsquare, hnorm⟩ := l2_minkowski_integral S hS
    (fun m g => W m * Zg β g (Q m)) hF hsq hint
  refine ⟨hsquare, hnorm.trans ?_⟩
  exact integral_mono_ae hint hI
    (Eventually.of_forall fun m => by
      exact hbound m)

private lemma p11_pos_plSpec {α c : ℝ} (hc : 0 < c) (N : ℕ) (i : Fin N) :
    0 < plSpec α c N i := by
  unfold plSpec
  exact mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)

private lemma p11_lam_div_mono {α : ℝ} (hα : 0 < α) {N B : ℕ} {c : ℝ}
    (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) :
    MonotoneOn (fun m : ℝ => partLam B (plSpec α c N) m / m)
      (Ioo 0 (gammaOf N B)) := by
  obtain ⟨cα, hcα, hel⟩ := lem_app_pl_elasticity_i hα
  obtain ⟨-, -, -, hcd⟩ :=
    def_app_pl_participation_bij (plSpec α c N) hB hN (p11_pos_plSpec hc N)
  obtain ⟨-, hbL, -, -⟩ :=
    def_app_pl_participation_bij (plSpec α c N) hB hN (p11_pos_plSpec hc N)
  have hdiff : ∀ m ∈ Ioo 0 (gammaOf N B),
      DifferentiableAt ℝ (partLam B (plSpec α c N)) m := by
    intro m hm
    exact ((hcd.contDiffAt (Ioo_mem_nhds hm.1 hm.2)).differentiableAt (by simp))
  have hpos : ∀ m ∈ Ioo 0 (gammaOf N B), 0 < partLam B (plSpec α c N) m :=
    fun m hm => hbL.mapsTo hm
  refine monotoneOn_of_deriv_nonneg (convex_Ioo _ _) ?_ ?_ ?_
  · intro m hm
    exact ((hdiff m hm).div differentiableAt_id hm.1.ne').continuousAt.continuousWithinAt
  · intro m hm
    rw [interior_Ioo] at hm
    exact ((hdiff m hm).div differentiableAt_id hm.1.ne').differentiableWithinAt
  · intro m hm
    rw [interior_Ioo] at hm
    have hd := (hdiff m hm).hasDerivAt.div (hasDerivAt_id' m) hm.1.ne'
    have hderiv : deriv (fun m : ℝ => partLam B (plSpec α c N) m / m) m =
        (deriv (partLam B (plSpec α c N)) m * m -
          partLam B (plSpec α c N) m * 1) / m ^ 2 := by
      have hd' : HasDerivAt (fun m : ℝ => partLam B (plSpec α c N) m / m)
          ((deriv (partLam B (plSpec α c N)) m * m -
            partLam B (plSpec α c N) m * 1) / m ^ 2) m := hd
      exact hd'.deriv
    rw [hderiv]
    apply div_nonneg _ (sq_nonneg _)
    have h1 := ((hel N B c hN hB hc).2 m hm).1
    have hL := hpos m hm
    rw [le_div_iff₀ hL] at h1
    have h2 : partLam B (plSpec α c N) m ≤
        deriv (partLam B (plSpec α c N)) m * m := by
      have h := mul_le_mul_of_nonneg_right h1 hm.1.le
      rw [show 1 / m * partLam B (plSpec α c N) m * m =
        partLam B (plSpec α c N) m by field_simp [hm.1.ne']] at h
      exact h
    linarith

private lemma p11_m0_facts {α : ℝ} {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) :
    partMN B (plSpec α c N) (1 / plSpec α c N i) ∈ Ioo 0 (gammaOf N B) ∧
      partLam B (plSpec α c N)
        (partMN B (plSpec α c N) (1 / plSpec α c N i)) =
          1 / plSpec α c N i := by
  have hp := p11_pos_plSpec (α := α) hc N
  obtain ⟨hbM, -, -, -⟩ :=
    def_app_pl_participation_bij (plSpec α c N) hB hN hp
  have hx : (1 / plSpec α c N i) ∈ Ioi (0 : ℝ) := one_div_pos.2 (hp i)
  refine ⟨hbM.mapsTo hx, ?_⟩
  exact hbM.invOn_invFunOn.1 hx

private lemma p11_row_shape_bound {α : ℝ} (hα : 0 < α) {N B : ℕ} {c : ℝ}
    (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) (i : Fin N) {m : ℝ}
    (hm : m ∈ Ioo 0 (gammaOf N B)) :
    plSpec α c N i * partLam B (plSpec α c N) m /
        (1 + plSpec α c N i * partLam B (plSpec α c N) m) ^ 2 ≤
      min (m / partMN B (plSpec α c N) (1 / plSpec α c N i))
        (partMN B (plSpec α c N) (1 / plSpec α c N i) / m) := by
  obtain ⟨hm0, hL0⟩ := p11_m0_facts (α := α) hN hB hc i
  set m₀ := partMN B (plSpec α c N) (1 / plSpec α c N i) with hm₀
  have hμ := p11_pos_plSpec (α := α) hc N i
  obtain ⟨-, hbL, -, -⟩ :=
    def_app_pl_participation_bij (plSpec α c N) hB hN (p11_pos_plSpec hc N)
  have hLpos : 0 < partLam B (plSpec α c N) m := hbL.mapsTo hm
  set u := plSpec α c N i * partLam B (plSpec α c N) m with hu
  have hu0 : 0 < u := mul_pos hμ hLpos
  have hmono := p11_lam_div_mono hα hN hB hc
  have hm₀pos := hm0.1
  have hlt : u / (1 + u) ^ 2 ≤ u := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg u]
  have hlt2 : u / (1 + u) ^ 2 ≤ 1 / u := by
    rw [div_le_div_iff₀ (by positivity) hu0]
    nlinarith [sq_nonneg u]
  have hLm : partLam B (plSpec α c N) m₀ / m₀ =
      1 / plSpec α c N i / m₀ := by rw [hL0]
  rcases le_total m m₀ with h | h
  · have hh := hmono hm hm0 h
    simp only at hh
    rw [hLm] at hh
    have h1 : u / m ≤ 1 / m₀ := by
      have ht : plSpec α c N i * (partLam B (plSpec α c N) m / m) ≤
          plSpec α c N i * (1 / plSpec α c N i / m₀) :=
        mul_le_mul_of_nonneg_left hh hμ.le
      calc
        u / m = plSpec α c N i * (partLam B (plSpec α c N) m / m) := by
          rw [hu]
          ring
        _ ≤ _ := ht
        _ = 1 / m₀ := by field_simp
    have h2 : u ≤ m / m₀ := by
      rw [div_le_iff₀ hm.1] at h1
      calc
        u ≤ 1 / m₀ * m := h1
        _ = m / m₀ := by ring
    have h3 : m / m₀ ≤ m₀ / m := by
      rw [div_le_div_iff₀ hm₀pos hm.1]
      nlinarith [mul_le_mul h h hm.1.le hm₀pos.le]
    exact le_min (hlt.trans h2) ((hlt.trans h2).trans h3)
  · have hh := hmono hm0 hm h
    simp only at hh
    rw [hLm] at hh
    have h1 : 1 / m₀ ≤ u / m := by
      have ht : plSpec α c N i * (1 / plSpec α c N i / m₀) ≤
          plSpec α c N i * (partLam B (plSpec α c N) m / m) :=
        mul_le_mul_of_nonneg_left hh hμ.le
      calc
        1 / m₀ = plSpec α c N i * (1 / plSpec α c N i / m₀) := by field_simp
        _ ≤ _ := ht
        _ = u / m := by rw [hu]; ring
    have h2 : m / m₀ ≤ u := by
      rw [le_div_iff₀ hm.1] at h1
      calc
        m / m₀ = 1 / m₀ * m := by ring
        _ ≤ u := h1
    have h4 : 1 / u ≤ m₀ / m := by
      rw [div_le_div_iff₀ hu0 hm.1]
      rw [div_le_iff₀ hm₀pos] at h2
      nlinarith
    have h5 : m₀ / m ≤ m / m₀ := by
      rw [div_le_div_iff₀ hm.1 hm₀pos]
      nlinarith [mul_le_mul h h hm₀pos.le hm.1.le]
    exact le_min ((hlt2.trans h4).trans h5) (hlt2.trans h4)

private lemma p11_low_integral {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (hta : t ≤ a) :
    IntegrableOn (fun m : ℝ => 1 / (Real.sqrt a * Real.sqrt m)) (Ioo 0 t) ∧
      ∫ m in Ioo 0 t, 1 / (Real.sqrt a * Real.sqrt m) ≤ 2 := by
  have hsqa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hbase := wmi_inv_sqrt (γ := t) ht
  have heq : ∀ m ∈ Ioo (0 : ℝ) t,
      1 / (Real.sqrt a * Real.sqrt m) = (1 / Real.sqrt a) * (1 / Real.sqrt m) := by
    intro m hm
    field_simp
  have hint : IntegrableOn (fun m : ℝ => 1 / (Real.sqrt a * Real.sqrt m)) (Ioo 0 t) :=
    (hbase.1.const_mul (1 / Real.sqrt a)).congr
      (ae_restrict_iff' measurableSet_Ioo |>.2 (Eventually.of_forall fun m hm => (heq m hm).symm))
  refine ⟨hint, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioo heq, integral_const_mul, hbase.2]
  have hsq : Real.sqrt t ≤ Real.sqrt a := Real.sqrt_le_sqrt hta
  calc
    1 / Real.sqrt a * (2 * Real.sqrt t) ≤
        1 / Real.sqrt a * (2 * Real.sqrt a) := by gcongr
    _ = 2 := by field_simp

private lemma p11_high_form {a m : ℝ} (ha : 0 < a) (hm : 0 < m) :
    Real.sqrt a / (m * Real.sqrt m) = Real.sqrt a * m ^ (-3 / 2 : ℝ) := by
  rw [show (-3 / 2 : ℝ) = -(3 / 2) by ring, Real.rpow_neg hm.le]
  congr 1
  rw [Real.sqrt_eq_rpow]
  calc
    m * m ^ (1 / 2 : ℝ) = m ^ (1 : ℝ) * m ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
    _ = m ^ ((1 : ℝ) + 1 / 2) := (Real.rpow_add hm _ _).symm
    _ = m ^ (3 / 2 : ℝ) := by norm_num

private lemma p11_high_integral {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    IntegrableOn (fun m : ℝ => Real.sqrt a / (m * Real.sqrt m)) (Ioo a t) ∧
      ∫ m in Ioo a t, Real.sqrt a / (m * Real.sqrt m) ≤ 2 := by
  rcases lt_or_ge a t with hat | hta
  swap
  · have hempty : Ioo a t = ∅ := Ioo_eq_empty (not_lt_of_ge hta)
    simp [hempty]
  have hzero : (0 : ℝ) ∉ uIcc a t := by
    rw [uIcc_of_le hat.le]
    intro h
    exact (not_le_of_gt ha) h.1
  have hii : IntervalIntegrable (fun m : ℝ => m ^ (-3 / 2 : ℝ)) volume a t :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hzero)
  have hioc : IntegrableOn (fun m : ℝ => m ^ (-3 / 2 : ℝ)) (Ioc a t) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hat.le).1 hii
  have hioo : IntegrableOn (fun m : ℝ => m ^ (-3 / 2 : ℝ)) (Ioo a t) :=
    hioc.mono_set Ioo_subset_Ioc_self
  have hform : ∀ m ∈ Ioo a t,
      Real.sqrt a / (m * Real.sqrt m) = Real.sqrt a * m ^ (-3 / 2 : ℝ) :=
    fun m hm => p11_high_form ha (ha.trans hm.1)
  have hint : IntegrableOn (fun m : ℝ => Real.sqrt a / (m * Real.sqrt m)) (Ioo a t) :=
    (hioo.const_mul (Real.sqrt a)).congr
      (ae_restrict_iff' measurableSet_Ioo |>.2 (Eventually.of_forall fun m hm => (hform m hm).symm))
  refine ⟨hint, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioo hform, integral_const_mul]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hat.le,
    integral_rpow (Or.inr ⟨by norm_num, hzero⟩)]
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hnonneg : 0 ≤ t ^ (-1 / 2 : ℝ) := Real.rpow_nonneg ht.le _
  have hid : Real.sqrt a * a ^ (-1 / 2 : ℝ) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ha]
    norm_num
  rw [show (-3 / 2 : ℝ) + 1 = -1 / 2 by ring]
  calc
    Real.sqrt a * ((t ^ (-1 / 2 : ℝ) - a ^ (-1 / 2 : ℝ)) / (-1 / 2 : ℝ)) =
        2 * (Real.sqrt a * a ^ (-1 / 2 : ℝ) -
          Real.sqrt a * t ^ (-1 / 2 : ℝ)) := by ring
    _ ≤ 2 * (Real.sqrt a * a ^ (-1 / 2 : ℝ)) := by
      nlinarith [mul_nonneg hsa.le hnonneg]
    _ = 2 := by rw [hid]; norm_num

private lemma p11_shape_integral {a M : ℝ} (ha : 0 < a) (hM : 0 < M) :
    IntegrableOn (fun m : ℝ => if m ≤ a then
        1 / (Real.sqrt a * Real.sqrt m) else Real.sqrt a / (m * Real.sqrt m)) (Ioo 0 M) ∧
      ∫ m in Ioo 0 M, (if m ≤ a then
        1 / (Real.sqrt a * Real.sqrt m) else Real.sqrt a / (m * Real.sqrt m)) ≤ 4 := by
  have ht : 0 < min a M := lt_min ha hM
  have hta : min a M ≤ a := min_le_left _ _
  have hlow := p11_low_integral ha ht hta
  have hhigh := p11_high_integral ha hM
  let L : ℝ → ℝ := (Ioo 0 (min a M)).indicator
    (fun m => 1 / (Real.sqrt a * Real.sqrt m))
  let H : ℝ → ℝ := (Ioo a M).indicator
    (fun m => Real.sqrt a / (m * Real.sqrt m))
  have hLint : Integrable L := hlow.1.integrable_indicator measurableSet_Ioo
  have hHint : Integrable H := hhigh.1.integrable_indicator measurableSet_Ioo
  have hsum : Integrable (fun m => L m + H m) := hLint.add hHint
  have hnonneg : ∀ m, 0 ≤ L m + H m := by
    intro m
    apply add_nonneg
    · by_cases hm : m ∈ Ioo 0 (min a M)
      · rw [show L m = 1 / (Real.sqrt a * Real.sqrt m) by simp [L, hm]]
        positivity
      · simp [L, hm]
    · by_cases hm : m ∈ Ioo a M
      · rw [show H m = Real.sqrt a / (m * Real.sqrt m) by simp [H, hm]]
        have hm0 : 0 < m := ha.trans hm.1
        positivity
      · simp [H, hm]
  have hne : ∀ᵐ m ∂(volume.restrict (Ioo (0 : ℝ) M)), m ≠ a :=
    ae_restrict_of_ae (volume.ae_ne a)
  have hpoint : ∀ᵐ m ∂(volume.restrict (Ioo (0 : ℝ) M)),
      (if m ≤ a then 1 / (Real.sqrt a * Real.sqrt m)
        else Real.sqrt a / (m * Real.sqrt m)) = L m + H m := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo, hne] with m hm hma
    by_cases hma' : m ≤ a
    · have hma'' : m < a := lt_of_le_of_ne hma' hma
      have hmt : m < min a M := lt_min hma'' hm.2
      have hmL : m ∈ Ioo 0 (min a M) := ⟨hm.1, hmt⟩
      have hmH : m ∉ Ioo a M := fun h => (not_lt_of_ge hma') h.1
      simp [hma', L, H, hmL, hmH]
    · have ham : a < m := lt_of_not_ge hma'
      have hmL : m ∉ Ioo 0 (min a M) := fun h => (not_lt_of_ge (min_le_left a M))
        (ham.trans h.2)
      have hmH : m ∈ Ioo a M := ⟨ham, hm.2⟩
      simp [hma', L, H, hmL, hmH]
  have hpint : IntegrableOn (fun m : ℝ => if m ≤ a then
      1 / (Real.sqrt a * Real.sqrt m) else Real.sqrt a / (m * Real.sqrt m)) (Ioo 0 M) :=
    hsum.integrableOn.congr (hpoint.mono fun m hm => hm.symm)
  refine ⟨hpint, ?_⟩
  calc
    (∫ m in Ioo 0 M, (if m ≤ a then 1 / (Real.sqrt a * Real.sqrt m)
        else Real.sqrt a / (m * Real.sqrt m))) =
        ∫ m in Ioo 0 M, (L m + H m) := integral_congr_ae hpoint
    _ ≤ ∫ m, (L m + H m) := setIntegral_le_integral hsum
      (Eventually.of_forall hnonneg)
    _ = (∫ m in Ioo 0 (min a M), 1 / (Real.sqrt a * Real.sqrt m)) +
        ∫ m in Ioo a M, Real.sqrt a / (m * Real.sqrt m) := by
      rw [integral_add hLint hHint]
      simp [L, H, integral_indicator]
    _ ≤ 2 + 2 := add_le_add hlow.2 hhigh.2
    _ = 4 := by norm_num

private lemma p11_head_pointwise {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    {N B : ℕ} {c M G : ℝ} (hN : 0 < N) (hB : 0 < B) (hc : 0 < c)
    (hM : 0 < M) (hMG : M ≤ G) (hG1 : 1 ≤ G)
    (hγ : 2 * G ≤ gammaOf N B) (i : Fin N) {m : ℝ} (hm : m ∈ Ioo 0 M) :
    |Wpart β B (plSpec α c N) i m| * Real.sqrt (Qm β m) ≤
      Real.sqrt (Qm β G) * (max (Classical.choose
        (lem_app_pl_elasticity_ii hα hβ0 hβ1)) 0 * (G + 2)) *
        (if m ≤ partMN B (plSpec α c N) (1 / plSpec α c N i) then
          1 / (Real.sqrt (partMN B (plSpec α c N) (1 / plSpec α c N i)) * Real.sqrt m)
        else Real.sqrt (partMN B (plSpec α c N) (1 / plSpec α c N i)) /
          (m * Real.sqrt m)) := by
  let C0 := Classical.choose (lem_app_pl_elasticity_ii hα hβ0 hβ1)
  have hC0 := Classical.choose_spec (lem_app_pl_elasticity_ii hα hβ0 hβ1)
  set μ := plSpec α c N i with hμ
  set Λ := partLam B (plSpec α c N) m with hΛ
  set u := μ * Λ with hu
  set a := partMN B (plSpec α c N) (1 / μ) with ha
  have hγ0 : 0 < gammaOf N B := by linarith
  have hmγ : m ∈ Ioo 0 (gammaOf N B) := ⟨hm.1, lt_of_lt_of_le hm.2 (hMG.trans (by linarith))⟩
  have hμ0 : 0 < μ := by rw [hμ]; exact p11_pos_plSpec hc N i
  obtain ⟨-, hbΛ, -, -⟩ :=
    def_app_pl_participation_bij (plSpec α c N) hB hN (p11_pos_plSpec hc N)
  have hΛ0 : 0 < Λ := by rw [hΛ]; exact hbΛ.mapsTo hmγ
  have hu0 : 0 < u := mul_pos hμ0 hΛ0
  have ha0 : 0 < a := by
    rw [ha, hμ]
    exact (p11_m0_facts (α := α) hN hB hc i).1.1
  have hmG : m ≤ G := hm.2.le.trans hMG
  have hγm : G ≤ gammaOf N B - m := by linarith
  have hθraw := hC0 N B c hN hB hc m hmγ
  obtain ⟨cE, CE, hcE, hcCE, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  have hEp : 0 < Efun β m :=
    lt_of_lt_of_le (mul_pos hcE (lt_min hm.1 one_pos)) (hE m hm.1).1
  have hθ0 : 0 ≤ thetaN β B (plSpec α c N) m := by
    nlinarith [hθraw.2]
  have hγm0 : 0 < gammaOf N B - m := by linarith
  have hm_inv0 : 0 ≤ 1 / m := (one_div_pos.2 hm.1).le
  have hγm_inv0 : 0 ≤ 1 / (gammaOf N B - m) := (one_div_pos.2 hγm0).le
  have hsum0 : 0 ≤ 1 + 1 / m + 1 / (gammaOf N B - m) := by
    linarith
  have hθ1 : thetaN β B (plSpec α c N) m ≤
      max C0 0 * (1 + 1 / m + 1 / (gammaOf N B - m)) :=
    hθraw.1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hsum0)
  have hone : 1 ≤ G / m := by
    rw [le_div_iff₀ hm.1]
    simpa using hmG
  have hend : 1 / (gammaOf N B - m) ≤ 1 / m :=
    one_div_le_one_div_of_le hm.1 (hmG.trans hγm)
  have hsum : 1 + 1 / m + 1 / (gammaOf N B - m) ≤ (G + 2) / m := by
    calc
      1 + 1 / m + 1 / (gammaOf N B - m) ≤ G / m + 1 / m + 1 / m := by
        linarith
      _ = (G + 2) / m := by ring
  have hθ : thetaN β B (plSpec α c N) m ≤ max C0 0 * (G + 2) / m := by
    calc
      thetaN β B (plSpec α c N) m ≤
          max C0 0 * (1 + 1 / m + 1 / (gammaOf N B - m)) := hθ1
      _ ≤ max C0 0 * ((G + 2) / m) :=
        mul_le_mul_of_nonneg_left hsum (le_max_right _ _)
      _ = max C0 0 * (G + 2) / m := by ring
  have hQ := llk_K1 hβ0 hβ1 hm.1 hmG hG1
  have hminm : min m 1 ≤ m := min_le_left _ _
  have hQle : Qm β m ≤ Qm β G * m :=
    hQ.trans (mul_le_mul_of_nonneg_left hminm (vsh_Qm hβ0 hβ1 (lt_of_lt_of_le one_pos hG1)).1.le)
  have hQ0 := (vsh_Qm hβ0 hβ1 hm.1).1
  have hQG0 := (vsh_Qm hβ0 hβ1 (lt_of_lt_of_le one_pos hG1)).1
  have hsQ : Real.sqrt (Qm β m) ≤ Real.sqrt (Qm β G) * Real.sqrt m := by
    rw [← Real.sqrt_mul hQG0.le]
    exact Real.sqrt_le_sqrt hQle
  have hshell : Real.sqrt (1 - m / gammaOf N B) ≤ 1 := by
    rw [Real.sqrt_le_one]
    have : 0 ≤ m / gammaOf N B := div_nonneg hm.1.le hγ0.le
    linarith
  have hs0 : 0 ≤ Real.sqrt u / (1 + u) := by positivity
  have hrow := p11_row_shape_bound hα hN hB hc i hmγ
  rw [← hμ, ← hΛ, ← hu, ← ha] at hrow
  have hs_sq : (Real.sqrt u / (1 + u)) ^ 2 = u / (1 + u) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hu0.le]
  have hshape : Real.sqrt u / (1 + u) / m ≤
      if m ≤ a then 1 / (Real.sqrt a * Real.sqrt m)
      else Real.sqrt a / (m * Real.sqrt m) := by
    by_cases hma : m ≤ a
    · rw [if_pos hma, div_le_iff₀ hm.1]
      have hr0 : 0 ≤ Real.sqrt m / Real.sqrt a := by positivity
      have hsq : (Real.sqrt u / (1 + u)) ^ 2 ≤
          (Real.sqrt m / Real.sqrt a) ^ 2 := by
        rw [hs_sq, div_pow, Real.sq_sqrt hm.1.le, Real.sq_sqrt ha0.le]
        exact hrow.trans (min_le_left _ _)
      have hs := (sq_le_sq₀ hs0 hr0).1 hsq
      calc
        Real.sqrt u / (1 + u) ≤ Real.sqrt m / Real.sqrt a := hs
        _ = 1 / (Real.sqrt a * Real.sqrt m) * m := by
          have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm.1
          field_simp
          rw [Real.sq_sqrt hm.1.le]
    · rw [if_neg hma, div_le_iff₀ hm.1]
      have hr0 : 0 ≤ Real.sqrt a / Real.sqrt m := by positivity
      have hsq : (Real.sqrt u / (1 + u)) ^ 2 ≤
          (Real.sqrt a / Real.sqrt m) ^ 2 := by
        rw [hs_sq, div_pow, Real.sq_sqrt hm.1.le, Real.sq_sqrt ha0.le]
        exact hrow.trans (min_le_right _ _)
      have hs := (sq_le_sq₀ hs0 hr0).1 hsq
      calc
        Real.sqrt u / (1 + u) ≤ Real.sqrt a / Real.sqrt m := hs
        _ = Real.sqrt a / (m * Real.sqrt m) * m := by
          have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm.1
          field_simp [hm.1.ne']
  have hW0 : 0 ≤ Wpart β B (plSpec α c N) i m := by
    unfold Wpart
    positivity
  rw [abs_of_nonneg hW0]
  have hrewrite : Wpart β B (plSpec α c N) i m * Real.sqrt (Qm β m) =
      (Real.sqrt u / (1 + u)) * (Real.sqrt (Qm β m) / Real.sqrt m) *
        Real.sqrt (1 - m / gammaOf N B) * thetaN β B (plSpec α c N) m := by
    unfold Wpart
    rw [← hμ, ← hΛ, ← hu]
    field_simp
  rw [hrewrite]
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm.1
  have hratioQ : Real.sqrt (Qm β m) / Real.sqrt m ≤ Real.sqrt (Qm β G) := by
    rw [div_le_iff₀ hsm]
    exact hsQ
  have hcoef0 : 0 ≤ max C0 0 * (G + 2) := by positivity
  calc
    (Real.sqrt u / (1 + u)) * (Real.sqrt (Qm β m) / Real.sqrt m) *
        Real.sqrt (1 - m / gammaOf N B) * thetaN β B (plSpec α c N) m ≤
      (Real.sqrt u / (1 + u)) * Real.sqrt (Qm β G) * 1 *
        (max C0 0 * (G + 2) / m) := by gcongr
    _ = Real.sqrt (Qm β G) * (max C0 0 * (G + 2)) *
        (Real.sqrt u / (1 + u) / m) := by ring
    _ ≤ Real.sqrt (Qm β G) * (max C0 0 * (G + 2)) *
        (if m ≤ a then 1 / (Real.sqrt a * Real.sqrt m)
        else Real.sqrt a / (m * Real.sqrt m)) := by gcongr
    _ = _ := by simp only [C0, a]

/-- Head-norm bound `eqn:app-pl-head-norm`: for fixed `M`, `‖(1/π)∫_0^M W_i 𝒵_g dm‖_{L²} ≤ C_M`, uniformly over the
rows (task L-G.7b; `lem:app-pl-vector` proof, l.1968-1972; snapshot cr-2026-10-23). -/
theorem head_norm_bound {α β : ℝ} (M : ℝ) (hM : 0 < M) :
    ∃ C : ℝ, ∀ (N B : ℕ → ℕ) (c : ℕ → ℝ), assum_app_pl_regime α β N B c →
      ∀ᶠ n in atTop, ∀ i : Fin (N n),
        Integrable (fun g => calVpart β (B n) (plSpec α (c n) (N n)) i 0 M g ^ 2) (gaussianReal 0 1) ∧
        l2Norm (fun g => calVpart β (B n) (plSpec α (c n) (N n)) i 0 M g) ≤ C := by
  by_cases hreg : 0 < α ∧ 0 < β ∧ β < 1
  swap
  · refine ⟨0, ?_⟩
    intro N B c R
    exact (hreg ⟨R.hα, R.hβ0, R.hβ1⟩).elim
  obtain ⟨hα, hβ0, hβ1⟩ := hreg
  let G := max M 1
  let C0 := Classical.choose (lem_app_pl_elasticity_ii hα hβ0 hβ1)
  let A := Real.sqrt (Qm β G) * (max C0 0 * (G + 2))
  refine ⟨Real.pi⁻¹ * (A * 4), ?_⟩
  intro N B c R
  have hMG : M ≤ G := le_max_left _ _
  have hG1 : 1 ≤ G := le_max_right _ _
  have hG0 : 0 < G := hM.trans_le hMG
  filter_upwards [Wpart_integrable_measurable R,
    R.hγ.eventually_ge_atTop (2 * G)] with n hdata hγ
  intro i
  specialize hdata i
  have hGγ : G ≤ gammaOf (N n) (B n) := by
    have hG2 : G ≤ 2 * G := by linarith
    exact hG2.trans hγ
  have hsub : Ioo (0 : ℝ) M ⊆ Ioo 0 (gammaOf (N n) (B n)) := by
    intro m hm
    exact ⟨hm.1, lt_of_lt_of_le hm.2 (hMG.trans hGγ)⟩
  have hI : IntegrableOn
      (fun m => |Wpart β (B n) (plSpec α (c n) (N n)) i m| * Real.sqrt (Qm β m))
      (Ioo 0 M) := hdata.1.mono_set hsub
  have hF : AEStronglyMeasurable
      (fun q : ℝ × ℝ => Wpart β (B n) (plSpec α (c n) (N n)) i q.1 *
        Zg β q.2 (Qm β q.1))
      ((volume.restrict (Ioo 0 M)).prod (gaussianReal 0 1)) :=
    hdata.2.2.mono_measure (Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl)
  have hmk := p11_minkowski_bound R.hβ0 R.hβ1
    (Wpart β (B n) (plSpec α (c n) (N n)) i) (Qm β) (Ioo 0 M)
    measurableSet_Ioo hI hF
  have hcalint : Integrable
      (fun g => calVpart β (B n) (plSpec α (c n) (N n)) i 0 M g ^ 2)
      (gaussianReal 0 1) := by
    unfold calVpart
    simpa only [mul_pow] using hmk.1.const_mul ((Real.pi⁻¹) ^ 2)
  refine ⟨hcalint, ?_⟩
  set a := partMN (B n) (plSpec α (c n) (N n))
    (1 / plSpec α (c n) (N n) i) with ha
  let s : ℝ → ℝ := fun m => if m ≤ a then
    1 / (Real.sqrt a * Real.sqrt m) else Real.sqrt a / (m * Real.sqrt m)
  have ha0 : 0 < a := by
    rw [ha]
    exact (p11_m0_facts (R.hNpos n) (R.hBpos n) (R.hcpos n) i).1.1
  have hs := p11_shape_integral ha0 hM
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  have hmajor : IntegrableOn (fun m => A * s m) (Ioo 0 M) :=
    hs.1.const_mul A
  have hmass : (∫ m in Ioo 0 M,
      |Wpart β (B n) (plSpec α (c n) (N n)) i m| * Real.sqrt (Qm β m)) ≤ A * 4 := by
    calc
      (∫ m in Ioo 0 M,
          |Wpart β (B n) (plSpec α (c n) (N n)) i m| * Real.sqrt (Qm β m)) ≤
          ∫ m in Ioo 0 M, A * s m := integral_mono_ae hI hmajor
            (ae_restrict_iff' measurableSet_Ioo |>.2 (Eventually.of_forall fun m hm => by
              dsimp [A, C0, G, s]
              simpa only [ha] using p11_head_pointwise R.hα R.hβ0 R.hβ1
                (R.hNpos n) (R.hBpos n) (R.hcpos n) hM hMG hG1 hγ i hm))
      _ = A * (∫ m in Ioo 0 M, s m) := by rw [integral_const_mul]
      _ ≤ A * 4 := mul_le_mul_of_nonneg_left hs.2 hA0
  have hraw : l2Norm (fun g => ∫ m in Ioo 0 M,
      Wpart β (B n) (plSpec α (c n) (N n)) i m * Zg β g (Qm β m)) ≤ A * 4 :=
    hmk.2.trans hmass
  have hscale : l2Norm
      (fun g => calVpart β (B n) (plSpec α (c n) (N n)) i 0 M g) =
      Real.pi⁻¹ * l2Norm (fun g => ∫ m in Ioo 0 M,
        Wpart β (B n) (plSpec α (c n) (N n)) i m * Zg β g (Qm β m)) := by
    unfold l2Norm calVpart
    simp_rw [mul_pow]
    rw [integral_const_mul, Real.sqrt_mul (sq_nonneg Real.pi⁻¹),
      Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.2 Real.pi_pos)]
  rw [hscale]
  exact mul_le_mul_of_nonneg_left hraw (inv_pos.2 Real.pi_pos).le

private lemma p11_lam_ratio {α : ℝ} (hα : 0 < α) {N B : ℕ} {c d G : ℝ}
    (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) (hd : 0 < d) (hd1 : d ≤ 1)
    (hG1 : 1 ≤ G) (hγ : 2 * G ≤ gammaOf N B) {m : ℝ} (hm : m ∈ Icc d G) :
    Real.exp (-((1 / Classical.choose (lem_app_pl_elasticity_i hα)) *
        (1 / d + 1 / G) * (G + 1))) ≤
        partLam B (plSpec α c N) m / partLam B (plSpec α c N) 1 ∧
      partLam B (plSpec α c N) m / partLam B (plSpec α c N) 1 ≤
        Real.exp ((1 / Classical.choose (lem_app_pl_elasticity_i hα)) *
          (1 / d + 1 / G) * (G + 1)) := by
  let L := partLam B (plSpec α c N)
  let e := Classical.choose (lem_app_pl_elasticity_i hα)
  have he := Classical.choose_spec (lem_app_pl_elasticity_i hα)
  let K := (1 / e) * (1 / d + 1 / G)
  have hG0 : 0 < G := zero_lt_one.trans_le hG1
  have hGγ : G < gammaOf N B := by linarith
  have hsub : Icc d G ⊆ Ioo (0 : ℝ) (gammaOf N B) := by
    intro x hx
    exact ⟨hd.trans_le hx.1, hx.2.trans_lt hGγ⟩
  obtain ⟨-, hLmap, -, hLdiff⟩ :=
    def_app_pl_participation_bij (plSpec α c N) hB hN (p11_pos_plSpec hc N)
  have hpos : ∀ x ∈ Icc d G, 0 < L x := fun x hx => hLmap.mapsTo (hsub hx)
  have hder : ∀ x ∈ Icc d G, DifferentiableAt ℝ (fun x => Real.log (L x)) x := by
    intro x hx
    exact ((hLdiff.contDiffAt (Ioo_mem_nhds (hsub hx).1 (hsub hx).2)).differentiableAt
      (by simp)).log (hpos x hx).ne'
  have hdbound : ∀ x ∈ Icc d G, ‖deriv (fun x => Real.log (L x)) x‖ ≤ K := by
    intro x hx
    have hxd := hsub hx
    have hex := (he.2 N B c hN hB hc).2 x hxd
    have hlog := ((hLdiff.contDiffAt (Ioo_mem_nhds hxd.1 hxd.2)).differentiableAt
      (by simp)).hasDerivAt.log (hpos x hx).ne'
    have hder0 : 0 ≤ deriv (partLam B (plSpec α c N)) x /
        partLam B (plSpec α c N) x := (one_div_pos.2 hxd.1).le.trans hex.1
    rw [hlog.deriv, Real.norm_eq_abs, abs_of_nonneg hder0]
    have hxinv : 1 / x ≤ 1 / d := one_div_le_one_div_of_le hd hx.1
    have hgx : G ≤ gammaOf N B - x := by
      calc
        G ≤ 2 * G - x := by linarith [hx.2]
        _ ≤ gammaOf N B - x := sub_le_sub_right hγ x
    have hginv : 1 / (gammaOf N B - x) ≤ 1 / G :=
      one_div_le_one_div_of_le hG0 hgx
    exact hex.2.trans (mul_le_mul_of_nonneg_left (add_le_add hxinv hginv)
      (one_div_pos.2 he.1).le)
  have h1mem : (1 : ℝ) ∈ Icc d G := ⟨hd1, hG1⟩
  have hlip := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun x => Real.log (L x))
    (s := Icc d G) (C := K) (x := 1) (y := m) hder hdbound (convex_Icc _ _) h1mem hm
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hlip
  have hdist : |m - 1| ≤ G + 1 := by
    rw [abs_le]
    constructor
    · linarith [hd.trans_le hm.1]
    · linarith [hm.2]
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (one_div_nonneg.2 he.1.le)
      (add_nonneg (one_div_nonneg.2 hd.le) (one_div_nonneg.2 hG0.le))
  have hlogle : |Real.log (L m) - Real.log (L 1)| ≤ K * (G + 1) :=
    hlip.trans (mul_le_mul_of_nonneg_left hdist hK0)
  have hratio : L m / L 1 = Real.exp (Real.log (L m) - Real.log (L 1)) := by
    rw [Real.exp_sub, Real.exp_log (hpos m hm), Real.exp_log (hpos 1 h1mem)]
  rw [hratio]
  constructor
  · exact Real.exp_le_exp.mpr (neg_le_of_abs_le hlogle)
  · exact Real.exp_le_exp.mpr (le_of_abs_le hlogle)

private lemma p11_amp_ratio {y r lo hi : ℝ} (hy : 0 < y) (hr : 0 < r)
    (hlo : 0 < lo) (hlor : lo ≤ r) (hrhi : r ≤ hi) :
    Real.sqrt (y * r) / (1 + y * r) ≤
      max (Real.sqrt hi) (Real.sqrt lo)⁻¹ * min (Real.sqrt y) (Real.sqrt y)⁻¹ := by
  have hu : 0 < y * r := mul_pos hy hr
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hslo : 0 < Real.sqrt lo := Real.sqrt_pos.2 hlo
  have hfirst : Real.sqrt (y * r) / (1 + y * r) ≤
      max (Real.sqrt hi) (Real.sqrt lo)⁻¹ * Real.sqrt y := by
    have hden : 1 ≤ 1 + y * r := by linarith
    have hamp : Real.sqrt (y * r) / (1 + y * r) ≤ Real.sqrt (y * r) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.sqrt_nonneg (y * r)]
    calc
      _ ≤ Real.sqrt (y * r) := hamp
      _ = Real.sqrt y * Real.sqrt r := Real.sqrt_mul hy.le r
      _ ≤ Real.sqrt y * max (Real.sqrt hi) (Real.sqrt lo)⁻¹ :=
        mul_le_mul_of_nonneg_left
          ((Real.sqrt_le_sqrt hrhi).trans (le_max_left _ _)) hsy.le
      _ = _ := by ring
  have hsecond : Real.sqrt (y * r) / (1 + y * r) ≤
      max (Real.sqrt hi) (Real.sqrt lo)⁻¹ * (Real.sqrt y)⁻¹ := by
    have hamp : Real.sqrt (y * r) / (1 + y * r) ≤ (Real.sqrt (y * r))⁻¹ := by
      rw [div_le_iff₀ (by positivity), le_inv_mul_iff₀ (Real.sqrt_pos.2 hu)]
      rw [Real.mul_self_sqrt hu.le]
      linarith
    have hinv : (Real.sqrt r)⁻¹ ≤ (Real.sqrt lo)⁻¹ :=
      (inv_le_inv₀ hsr hslo).2 (Real.sqrt_le_sqrt hlor)
    calc
      _ ≤ (Real.sqrt (y * r))⁻¹ := hamp
      _ = (Real.sqrt y)⁻¹ * (Real.sqrt r)⁻¹ := by
        rw [Real.sqrt_mul hy.le, mul_inv_rev]
        ring
      _ ≤ (Real.sqrt y)⁻¹ * (Real.sqrt lo)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (inv_nonneg.2 hsy.le)
      _ ≤ (Real.sqrt y)⁻¹ * max (Real.sqrt hi) (Real.sqrt lo)⁻¹ :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (inv_nonneg.2 hsy.le)
      _ = _ := by ring
  rw [mul_min_of_nonneg _ _ (by positivity)]
  exact le_min hfirst hsecond

private lemma p11_middle_pointwise {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    {δ M d G : ℝ} (hδ : 0 < δ) (hδM : δ < M) (hd : 0 < d) (hdδ : d ≤ δ)
    (hd1 : d ≤ 1) (hMG : M ≤ G) (hG1 : 1 ≤ G) {N B : ℕ} {c : ℝ}
    (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) (hγ : 2 * G ≤ gammaOf N B)
    (i : Fin N) {m : ℝ} (hm : m ∈ Ioo δ M) :
    |Wpart β B (plSpec α c N) i m| * Real.sqrt (Qm β m) ≤
      Real.sqrt (Qm β G) *
        (max (Classical.choose (lem_app_pl_elasticity_ii hα hβ0 hβ1)) 0 *
          (1 + 1 / δ + 1 / G)) *
        max (Real.sqrt (Real.exp ((1 / Classical.choose (lem_app_pl_elasticity_i hα)) *
          (1 / d + 1 / G) * (G + 1))))
          (Real.sqrt (Real.exp (-((1 / Classical.choose (lem_app_pl_elasticity_i hα)) *
            (1 / d + 1 / G) * (G + 1)))))⁻¹ *
        min (Real.sqrt (plSpec α c N i * partLam B (plSpec α c N) 1))
          (Real.sqrt (plSpec α c N i * partLam B (plSpec α c N) 1))⁻¹ := by
  let C0 := Classical.choose (lem_app_pl_elasticity_ii hα hβ0 hβ1)
  let L0 := (1 / Classical.choose (lem_app_pl_elasticity_i hα)) *
    (1 / d + 1 / G) * (G + 1)
  set μ := plSpec α c N i with hμ
  set Λ := partLam B (plSpec α c N) m with hΛ
  set Λ1 := partLam B (plSpec α c N) 1 with hΛ1
  set y := μ * Λ1 with hy
  set r := Λ / Λ1 with hr
  have hG0 : 0 < G := zero_lt_one.trans_le hG1
  have hmG : m ≤ G := hm.2.le.trans hMG
  have hmγ : m ∈ Ioo 0 (gammaOf N B) := by
    have hGγ : G ≤ gammaOf N B := by linarith
    exact ⟨hδ.trans hm.1, hm.2.trans_le (hMG.trans hGγ)⟩
  have h1γ : (1 : ℝ) ∈ Ioo 0 (gammaOf N B) := by
    have : 1 < gammaOf N B := by linarith
    exact ⟨one_pos, this⟩
  have hμ0 : 0 < μ := by rw [hμ]; exact p11_pos_plSpec hc N i
  obtain ⟨-, hLmap, -, -⟩ :=
    def_app_pl_participation_bij (plSpec α c N) hB hN (p11_pos_plSpec hc N)
  have hΛ0 : 0 < Λ := by rw [hΛ]; exact hLmap.mapsTo hmγ
  have hΛ10 : 0 < Λ1 := by rw [hΛ1]; exact hLmap.mapsTo h1γ
  have hy0 : 0 < y := mul_pos hμ0 hΛ10
  have hr0 : 0 < r := div_pos hΛ0 hΛ10
  have hmDG : m ∈ Icc d G := ⟨hdδ.trans hm.1.le, hmG⟩
  have hrat := p11_lam_ratio hα hN hB hc hd hd1 hG1 hγ hmDG
  rw [← hΛ, ← hΛ1, ← hr] at hrat
  have hamp := p11_amp_ratio hy0 hr0 (Real.exp_pos (-L0)) hrat.1 hrat.2
  have huy : μ * Λ = y * r := by rw [hy, hr]; field_simp
  rw [← huy] at hamp
  have hθraw := (Classical.choose_spec (lem_app_pl_elasticity_ii hα hβ0 hβ1))
    N B c hN hB hc m hmγ
  obtain ⟨cE, CE, hcE, hcCE, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  have hEp : 0 < Efun β m :=
    lt_of_lt_of_le (mul_pos hcE (lt_min (hδ.trans hm.1) one_pos)) (hE m (hδ.trans hm.1)).1
  have hθ0 : 0 ≤ thetaN β B (plSpec α c N) m := by
    nlinarith [hθraw.2]
  have hsum0 : 0 ≤ 1 + 1 / m + 1 / (gammaOf N B - m) := by
    have hgm0 : 0 < gammaOf N B - m := by linarith [hmγ.2]
    have hm0 : 0 ≤ 1 / m := (one_div_pos.2 (hδ.trans hm.1)).le
    have hgm0' : 0 ≤ 1 / (gammaOf N B - m) := (one_div_pos.2 hgm0).le
    linarith
  have hθ : thetaN β B (plSpec α c N) m ≤
      max C0 0 * (1 + 1 / δ + 1 / G) := by
    have hm_inv : 1 / m ≤ 1 / δ := one_div_le_one_div_of_le hδ hm.1.le
    have hgm : G ≤ gammaOf N B - m := by linarith
    have hg_inv : 1 / (gammaOf N B - m) ≤ 1 / G :=
      one_div_le_one_div_of_le hG0 hgm
    exact hθraw.1.trans <| (mul_le_mul_of_nonneg_right (le_max_left C0 0) hsum0).trans
      (mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl hm_inv) hg_inv)
        (le_max_right _ _))
  have hQ := llk_K1 hβ0 hβ1 (hδ.trans hm.1) hmG hG1
  have hQle : Qm β m ≤ Qm β G * m :=
    hQ.trans (mul_le_mul_of_nonneg_left (min_le_left m 1)
      (vsh_Qm hβ0 hβ1 hG0).1.le)
  have hsQ : Real.sqrt (Qm β m) ≤ Real.sqrt (Qm β G) * Real.sqrt m := by
    rw [← Real.sqrt_mul (vsh_Qm hβ0 hβ1 hG0).1.le]
    exact Real.sqrt_le_sqrt hQle
  have hshell : Real.sqrt (1 - m / gammaOf N B) ≤ 1 := by
    rw [Real.sqrt_le_one]
    have hγ0 : 0 < gammaOf N B := hmγ.1.trans hmγ.2
    exact sub_le_self _ (div_nonneg hmγ.1.le hγ0.le)
  have hW0 : 0 ≤ Wpart β B (plSpec α c N) i m := by unfold Wpart; positivity
  rw [abs_of_nonneg hW0]
  have hre : Wpart β B (plSpec α c N) i m * Real.sqrt (Qm β m) =
      (Real.sqrt (μ * Λ) / (1 + μ * Λ)) *
        (Real.sqrt (Qm β m) / Real.sqrt m) * Real.sqrt (1 - m / gammaOf N B) *
          thetaN β B (plSpec α c N) m := by
    unfold Wpart
    rw [← hμ, ← hΛ]
    field_simp
  rw [hre]
  have hratioQ : Real.sqrt (Qm β m) / Real.sqrt m ≤ Real.sqrt (Qm β G) := by
    rw [div_le_iff₀ (Real.sqrt_pos.2 (hδ.trans hm.1))]
    exact hsQ
  calc
    _ ≤ (max (Real.sqrt (Real.exp L0)) (Real.sqrt (Real.exp (-L0)))⁻¹ *
        min (Real.sqrt y) (Real.sqrt y)⁻¹) * Real.sqrt (Qm β G) * 1 *
          (max C0 0 * (1 + 1 / δ + 1 / G)) := by gcongr
    _ = _ := by simp only [C0, L0, y]; ring

/-- Middle-range norm: for `0 < δ < M`, `‖(1/π)∫_δ^M W_i 𝒵_g dm‖_{L²} ≤ C_{δ,M} min(√y, y^{-1/2})` with
`y = μ_iΛ_N(1)` (task L-G.7b; proof step of `lem:app-pl-vector`, l.1996-1998; snapshot cr-2026-10-23). -/
theorem middle_norm_bound {α β : ℝ} (δ M : ℝ) (hδ : 0 < δ) (hδM : δ < M) :
    ∃ C : ℝ, ∀ (N B : ℕ → ℕ) (c : ℕ → ℝ), assum_app_pl_regime α β N B c →
      ∀ᶠ n in atTop, ∀ i : Fin (N n),
        Integrable (fun g => calVpart β (B n) (plSpec α (c n) (N n)) i δ M g ^ 2) (gaussianReal 0 1) ∧
        l2Norm (fun g => calVpart β (B n) (plSpec α (c n) (N n)) i δ M g) ≤
          C * min (Real.sqrt (plSpec α (c n) (N n) i * partLam (B n) (plSpec α (c n) (N n)) 1))
            (Real.sqrt (plSpec α (c n) (N n) i * partLam (B n) (plSpec α (c n) (N n)) 1))⁻¹ := by
  by_cases hreg : 0 < α ∧ 0 < β ∧ β < 1
  swap
  · refine ⟨0, ?_⟩
    intro N B c R
    exact (hreg ⟨R.hα, R.hβ0, R.hβ1⟩).elim
  obtain ⟨hα, hβ0, hβ1⟩ := hreg
  let d := min δ 1
  let G := max M 1
  let C0 := Classical.choose (lem_app_pl_elasticity_ii hα hβ0 hβ1)
  let L0 := (1 / Classical.choose (lem_app_pl_elasticity_i hα)) *
    (1 / d + 1 / G) * (G + 1)
  let D := max (Real.sqrt (Real.exp L0)) (Real.sqrt (Real.exp (-L0)))⁻¹
  let A := Real.sqrt (Qm β G) * (max C0 0 * (1 + 1 / δ + 1 / G)) * D
  refine ⟨Real.pi⁻¹ * (A * (M - δ)), ?_⟩
  intro N B c R
  have hd : 0 < d := lt_min hδ one_pos
  have hdδ : d ≤ δ := min_le_left _ _
  have hd1 : d ≤ 1 := min_le_right _ _
  have hMG : M ≤ G := le_max_left _ _
  have hG1 : 1 ≤ G := le_max_right _ _
  have hG0 : 0 < G := one_pos.trans_le hG1
  have hA0 : 0 ≤ A := by dsimp [A, D]; positivity
  filter_upwards [Wpart_integrable_measurable R,
    R.hγ.eventually_ge_atTop (2 * G)] with n hdata hγ
  intro i
  specialize hdata i
  have hGγ : G ≤ gammaOf (N n) (B n) := by
    have hG2 : G ≤ 2 * G := by linarith
    exact hG2.trans hγ
  have hsub : Ioo δ M ⊆ Ioo (0 : ℝ) (gammaOf (N n) (B n)) := by
    intro m hm
    exact ⟨hδ.trans hm.1, hm.2.trans_le (hMG.trans hGγ)⟩
  have hI : IntegrableOn
      (fun m => |Wpart β (B n) (plSpec α (c n) (N n)) i m| * Real.sqrt (Qm β m))
      (Ioo δ M) := hdata.1.mono_set hsub
  have hF : AEStronglyMeasurable
      (fun q : ℝ × ℝ => Wpart β (B n) (plSpec α (c n) (N n)) i q.1 *
        Zg β q.2 (Qm β q.1))
      ((volume.restrict (Ioo δ M)).prod (gaussianReal 0 1)) :=
    hdata.2.2.mono_measure (Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl)
  have hmk := p11_minkowski_bound R.hβ0 R.hβ1
    (Wpart β (B n) (plSpec α (c n) (N n)) i) (Qm β) (Ioo δ M)
    measurableSet_Ioo hI hF
  have hcalint : Integrable
      (fun g => calVpart β (B n) (plSpec α (c n) (N n)) i δ M g ^ 2)
      (gaussianReal 0 1) := by
    unfold calVpart
    simpa only [mul_pow] using hmk.1.const_mul ((Real.pi⁻¹) ^ 2)
  refine ⟨hcalint, ?_⟩
  let z := min
    (Real.sqrt (plSpec α (c n) (N n) i * partLam (B n) (plSpec α (c n) (N n)) 1))
    (Real.sqrt (plSpec α (c n) (N n) i * partLam (B n) (plSpec α (c n) (N n)) 1))⁻¹
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hmajor : IntegrableOn (fun _ : ℝ => A * z) (Ioo δ M) :=
    integrableOn_const (hs := measure_Ioo_lt_top.ne)
  have hmass : (∫ m in Ioo δ M,
      |Wpart β (B n) (plSpec α (c n) (N n)) i m| * Real.sqrt (Qm β m)) ≤
        (A * (M - δ)) * z := by
    calc
      _ ≤ ∫ _m in Ioo δ M, A * z := integral_mono_ae hI hmajor
        (ae_restrict_iff' measurableSet_Ioo |>.2 (Eventually.of_forall fun m hm => by
          dsimp [A, D, C0, L0, d, G, z]
          exact p11_middle_pointwise hα hβ0 hβ1 hδ hδM (lt_min hδ one_pos)
            (min_le_left _ _) (min_le_right _ _) (le_max_left _ _) (le_max_right _ _)
            (R.hNpos n) (R.hBpos n) (R.hcpos n) hγ i hm))
      _ = (M - δ) * (A * z) := by simp [hδM.le]
      _ = (A * (M - δ)) * z := by ring
  have hraw : l2Norm (fun g => ∫ m in Ioo δ M,
      Wpart β (B n) (plSpec α (c n) (N n)) i m * Zg β g (Qm β m)) ≤
        (A * (M - δ)) * z := hmk.2.trans hmass
  have hscale : l2Norm
      (fun g => calVpart β (B n) (plSpec α (c n) (N n)) i δ M g) =
      Real.pi⁻¹ * l2Norm (fun g => ∫ m in Ioo δ M,
        Wpart β (B n) (plSpec α (c n) (N n)) i m * Zg β g (Qm β m)) := by
    unfold l2Norm calVpart
    simp_rw [mul_pow]
    rw [integral_const_mul, Real.sqrt_mul (sq_nonneg Real.pi⁻¹),
      Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.2 Real.pi_pos)]
  rw [hscale]
  change Real.pi⁻¹ * l2Norm (fun g => ∫ m in Ioo δ M,
      Wpart β (B n) (plSpec α (c n) (N n)) i m * Zg β g (Qm β m)) ≤
        (Real.pi⁻¹ * (A * (M - δ))) * z
  calc
    Real.pi⁻¹ * l2Norm (fun g => ∫ m in Ioo δ M,
        Wpart β (B n) (plSpec α (c n) (N n)) i m * Zg β g (Qm β m)) ≤
      Real.pi⁻¹ * ((A * (M - δ)) * z) :=
        mul_le_mul_of_nonneg_left hraw (inv_pos.2 Real.pi_pos).le
    _ = (Real.pi⁻¹ * (A * (M - δ))) * z := by ring

private lemma p14_row_mem {N : ℕ} (i : Fin N) : rowFrac i ∈ Ioc (0 : ℝ) 1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hi : 0 < rowIdx i := by unfold rowIdx; positivity
  have hiN : rowIdx i ≤ (N : ℝ) := by
    unfold rowIdx
    exact_mod_cast (Nat.succ_le_of_lt i.isLt)
  exact ⟨div_pos hi hN, (div_le_one hN).2 hiN⟩

private lemma p14_partMN_eq {α c : ℝ} {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) :
    partMN B (plSpec α c N) (1 / plSpec α c N i) =
      gammaOf N B * finS α N (rowFrac i ^ α) := by
  have hi : 0 < rowIdx i := by unfold rowIdx; positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [eqn_app_pl_SN_mN α c hN hB hc (by
    exact div_pos one_pos (p11_pos_plSpec hc N i))]
  congr 2
  change c * (1 / (c * rowIdx i ^ (-α))) * (N : ℝ) ^ (-α) =
    (rowIdx i / (N : ℝ)) ^ α
  rw [Real.div_rpow hi.le hNr.le, Real.rpow_neg hi.le, Real.rpow_neg hNr.le]
  field_simp

private lemma p14_fin_equiv {α : ℝ} {N : ℕ → ℕ} {V W : ℕ → ℝ}
    (hα : 0 < α) (hN : ∀ n, 0 < N n) (hV : ∀ n, 0 < V n)
    (hW : ∀ᶠ n in atTop, 0 < W n)
    (hNW : Tendsto (fun n => (N n : ℝ) * W n) atTop atTop)
    (he : IsEquivalent atTop (fun n => contS α (V n)) W) :
    IsEquivalent atTop (fun n => finS α (N n) (V n)) W := by
  have hz : Tendsto (fun n => (finS α (N n) (V n) - contS α (V n)) / W n)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (hNW.const_div_atTop 1)
    filter_upwards [hW] with n hn
    obtain ⟨he0, he1⟩ := lem_app_pl_finite_inverse_i_a hα (hN n) (V n) (hV n)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hn, abs_sub_comm,
      abs_of_nonneg he0]
    calc
      (contS α (V n) - finS α (N n) (V n)) / W n ≤ (1 / (N n : ℝ)) / W n :=
        div_le_div_of_nonneg_right he1 hn.le
      _ = 1 / ((N n : ℝ) * W n) := by ring
  have ht := (isEquivalent_iff_tendsto_one (hW.mono fun _ h => h.ne')).1 he
  apply isEquivalent_of_tendsto_one
  convert hz.add ht using 1
  · funext n
    simp only [Pi.div_apply]
    ring
  · norm_num

private lemma p14_NV_top {α : ℝ} (hα1 : α ≤ 1) {N : ℕ → ℕ}
    (i : ∀ n, Fin (N n)) (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop) :
    Tendsto (fun n => (N n : ℝ) * rowFrac (i n) ^ α) atTop atTop := by
  apply tendsto_atTop_mono _ hi
  intro n
  have hx := p14_row_mem (i n)
  have hpow : rowFrac (i n) ≤ rowFrac (i n) ^ α := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 hα1
  have hNr : (0 : ℝ) < N n := by exact_mod_cast (Nat.zero_lt_of_lt (i n).isLt)
  calc
    rowIdx (i n) = (N n : ℝ) * rowFrac (i n) := by unfold rowFrac; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow hNr.le

private lemma p14_x_tendsto {N : ℕ → ℕ} (i : ∀ n, Fin (N n))
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    Tendsto (fun n => rowFrac (i n)) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall fun n => (p14_row_mem (i n)).1⟩

private lemma p14_log_top {N : ℕ → ℕ} (i : ∀ n, Fin (N n))
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    Tendsto (fun n => Real.log (1 / rowFrac (i n))) atTop atTop := by
  simpa only [one_div, Function.comp_def] using Real.tendsto_log_atTop.comp
    (tendsto_inv_nhdsGT_zero.comp (p14_x_tendsto i hx))

private lemma p14_fin_lt {α : ℝ} {N : ℕ → ℕ} (hα : 0 < α) (hα1 : α < 1)
    (hN : ∀ n, 0 < N n) (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    IsEquivalent atTop (fun n => finS α (N n) (rowFrac (i n) ^ α))
      (fun n => rowFrac (i n) ^ α / (1 - α)) := by
  have hV : Tendsto (fun n => rowFrac (i n) ^ α) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
      Real.rpow_pos_of_pos (p14_row_mem (i n)).1 α⟩
    simpa only [Real.zero_rpow hα.ne', Function.comp_def] using
      (Real.continuous_rpow_const hα.le).continuousAt.tendsto.comp hx
  apply p14_fin_equiv hα hN (fun n => Real.rpow_pos_of_pos (p14_row_mem (i n)).1 α)
    (Eventually.of_forall fun n => div_pos (Real.rpow_pos_of_pos (p14_row_mem (i n)).1 α)
      (sub_pos.2 hα1))
  · simpa only [mul_div_assoc] using Filter.Tendsto.atTop_div_const (sub_pos.2 hα1) (p14_NV_top hα1.le i hi)
  · exact (lem_app_pl_continuum_i_lt hα hα1).comp_tendsto hV

private lemma p14_fin_one {N : ℕ → ℕ} (hN : ∀ n, 0 < N n) (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    IsEquivalent atTop (fun n => finS 1 (N n) (rowFrac (i n)))
      (fun n => rowFrac (i n) * Real.log (1 / rowFrac (i n))) := by
  have hL := p14_log_top i hx
  apply p14_fin_equiv one_pos hN (fun n => (p14_row_mem (i n)).1)
    ((hL.eventually_gt_atTop 0).mono fun n hn => mul_pos (p14_row_mem (i n)).1 hn)
  · apply tendsto_atTop_mono' _ _ hi
    filter_upwards [hL.eventually_ge_atTop 1] with n hn
    have hNr : (0 : ℝ) < N n := by exact_mod_cast hN n
    have he : (N n : ℝ) * rowFrac (i n) = rowIdx (i n) := by unfold rowFrac; field_simp
    rw [← mul_assoc, he]
    exact le_mul_of_one_le_right (by unfold rowIdx; positivity) hn
  · exact lem_app_pl_continuum_i_one.2.comp_tendsto (p14_x_tendsto i hx)

private lemma p14_b_pos {α : ℝ} (hα : 0 < α) {N B : ℕ} (hN : 0 < N)
    (hB : 0 < B) (i : Fin N) : 0 < bCoef α B i := by
  have hc0 : 0 < c0 := by unfold c0; positivity
  exact div_pos (mul_pos (mul_pos (Real.sqrt_pos.2 (p12_pg6_gamma_pos hB hN))
    (Real.rpow_pos_of_pos (p14_row_mem i).1 _))
    (lem_app_pl_Psi_i_pos hα _ (p14_row_mem i))) hc0

private lemma p14_b_sq {α : ℝ} {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (i : Fin N) :
    bCoef α B i ^ 2 = gammaOf N B * rowFrac i ^ α * profPsi α (rowFrac i) ^ 2 / c0 ^ 2 := by
  have hp : (rowFrac i ^ (α / 2)) ^ 2 = rowFrac i ^ α := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (p14_row_mem i).1.le]
    congr 1
    norm_num
  simp only [bCoef, div_pow, mul_pow, Real.sq_sqrt (p12_pg6_gamma_pos hB hN).le, hp]

private lemma p14_fin_ratio_zero {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {N : ℕ → ℕ} (hN : ∀ n, 0 < N n) (i : ∀ n, Fin (N n))
    (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    Tendsto (fun n => finS α (N n) (rowFrac (i n) ^ α) /
      (rowFrac (i n) ^ α * profPsi α (rowFrac (i n)) ^ 2)) atTop (𝓝 0) := by
  have hL := p14_log_top i hx
  have hL2 : Tendsto (fun n => Real.log (1 / rowFrac (i n)) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hL
  have hc0 : 0 < c0 := by unfold c0; positivity
  rcases lt_or_eq_of_le hα1 with hlt | rfl
  · have hψ := (lem_app_pl_Psi_ii_lt hα hlt).comp_tendsto (p14_x_tendsto i hx)
    have he := (p14_fin_lt hα hlt hN i hi hx).div
      ((IsEquivalent.refl (l := atTop) (u := fun n => rowFrac (i n) ^ α)).mul (hψ.pow 2))
    apply he.symm.tendsto_nhds
    have ht := hL2.const_div_atTop (1 / ((1 - α) * (c0 / Real.sqrt (1 - α) * α) ^ 2))
    apply ht.congr'
    filter_upwards [hL.eventually_gt_atTop 0] with n hn
    have hx0 := (p14_row_mem (i n)).1
    have hxp := (Real.rpow_pos_of_pos hx0 α).ne'
    have hl : Real.log (rowFrac (i n) ^ (-α)) = α * Real.log (1 / rowFrac (i n)) := by
      rw [Real.log_rpow hx0, one_div, Real.log_inv]
      ring
    simp only [Pi.div_apply, Pi.mul_apply, Pi.pow_apply, Function.comp_apply, hl]
    field_simp
    <;> ring
  · have hψ := (lem_app_pl_Psi_ii_one rfl).comp_tendsto (p14_x_tendsto i hx)
    have he := (p14_fin_one hN i hi hx).div
      ((IsEquivalent.refl (l := atTop) (u := fun n => rowFrac (i n))).mul (hψ.pow 2))
    simp only [Real.rpow_one]
    apply he.symm.tendsto_nhds
    have ht := hL2.const_div_atTop (1 / (2 / 3 * c0) ^ 2)
    apply ht.congr'
    filter_upwards [hL.eventually_gt_atTop 0] with n hn
    have hx0 := (p14_row_mem (i n)).1
    have hp : (Real.log (1 / rowFrac (i n)) ^ (3 / 2 : ℝ)) ^ 2 =
        Real.log (1 / rowFrac (i n)) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
      norm_num
    simp only [Pi.div_apply, Pi.mul_apply, Pi.pow_apply, Function.comp_apply, mul_pow, hp]
    field_simp
    <;> ring

private lemma p14_ratio_zero {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (i : ∀ n, Fin (N n)) (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    Tendsto (fun n => partMN (B n) (plSpec α (c n) (N n))
      (1 / plSpec α (c n) (N n) (i n)) / bCoef α (B n) (i n) ^ 2) atTop (𝓝 0) := by
  have ht := (p14_fin_ratio_zero R.hα hα1 R.hNpos i hi hx).const_mul (c0 ^ 2)
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [] with n
  rw [p14_partMN_eq (R.hNpos n) (R.hBpos n) (R.hcpos n),
    p14_b_sq (R.hNpos n) (R.hBpos n)]
  have hγ := (p12_pg6_gamma_pos (R.hBpos n) (R.hNpos n)).ne'
  have hxp := (Real.rpow_pos_of_pos (p14_row_mem (i n)).1 α).ne'
  have hψ := (lem_app_pl_Psi_i_pos R.hα _ (p14_row_mem (i n))).ne'
  have hc0 : c0 ≠ 0 := ne_of_gt (by unfold c0; positivity)
  field_simp
  <;> ring

private lemma p14_partMN_mono {N B : ℕ} (μ : Fin N → ℝ)
    (hμ : ∀ j, 0 < μ j) : MonotoneOn (partMN B μ) (Ici 0) := by
  intro x hx y hy hxy
  unfold partMN
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j _
  have hxj : 0 ≤ x * μ j := mul_nonneg hx (hμ j).le
  have hyj : 0 ≤ y * μ j := mul_nonneg hy (hμ j).le
  have hxyj := mul_le_mul_of_nonneg_right hxy (hμ j).le
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

private lemma p14_partMN_scale {N B : ℕ} (μ : Fin N → ℝ)
    (hμ : ∀ j, 0 < μ j) {s t : ℝ} (hs : 1 ≤ s) (ht : 0 ≤ t) :
    partMN B μ (s * t) ≤ s * partMN B μ t := by
  unfold partMN
  rw [show s * ((B : ℝ)⁻¹ * ∑ j, t * μ j / (1 + t * μ j)) =
    (B : ℝ)⁻¹ * ∑ j, s * (t * μ j / (1 + t * μ j)) by
      rw [← Finset.mul_sum]; ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j _
  have htj : 0 ≤ t * μ j := mul_nonneg ht (hμ j).le
  have hstj : 0 ≤ s * (t * μ j) := mul_nonneg (by linarith) htj
  rw [← mul_div_assoc, mul_assoc]
  exact div_le_div_of_nonneg_left hstj (by positivity) (by nlinarith)

private lemma p14_partMN_scaled_bound {N B : ℕ} (μ : Fin N → ℝ)
    (hμ : ∀ j, 0 < μ j) (i : Fin N) {u : ℝ} (hu : 0 ≤ u) :
    partMN B μ (u / μ i) ≤ max u 1 * partMN B μ (1 / μ i) := by
  have hi := hμ i
  have hmax : 0 ≤ max u 1 := le_trans zero_le_one (le_max_right _ _)
  calc
    partMN B μ (u / μ i) ≤ partMN B μ (max u 1 * (1 / μ i)) := by
      apply p14_partMN_mono μ hμ (div_nonneg hu (hμ i).le)
        (show 0 ≤ max u 1 * (1 / μ i) by positivity)
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_right (le_max_left u 1) (inv_nonneg.2 (hμ i).le)
    _ ≤ _ := p14_partMN_scale μ hμ (le_max_right _ _) (by positivity)

/-- If `y = μ_iΛ_N(1)` stays in a compact subset of `(0,∞)` then `b → ∞`: `a_i ≍ 1` and `b² ≍ a_i T² → ∞`
(task L-G.7b; proof step of `lem:app-pl-vector`, l.1998-2000; snapshot cr-2026-10-23). -/
theorem b_large_of_y_compact {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (i : ∀ n, Fin (N n)) (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) {y₀ y₁ : ℝ} (hy₀ : 0 < y₀) (L : ℝ) :
    ∀ᶠ n in atTop,
      plSpec α (c n) (N n) (i n) * partLam (B n) (plSpec α (c n) (N n)) 1 ∈ Icc y₀ y₁ →
        L ≤ bCoef α (B n) (i n) := by
  let K : ℝ := max y₁ 1
  let M : ℝ := max L 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hδ : 0 < 1 / (K * M ^ 2) := by positivity
  filter_upwards [(p14_ratio_zero R hα1 i hi hx).eventually (eventually_lt_nhds hδ),
    R.hγ.eventually_gt_atTop 1] with n hn hγ
  intro hy
  have hp := p11_pos_plSpec (α := α) (R.hcpos n) (N n)
  have hbpos := p14_b_pos R.hα (R.hNpos n) (R.hBpos n) (i n)
  have hapos := (p11_m0_facts (α := α) (R.hNpos n) (R.hBpos n) (R.hcpos n) (i n)).1.1
  have hbij := (def_app_pl_participation_bij _ (R.hBpos n) (R.hNpos n) hp).1
  have hinv : partMN (B n) (plSpec α (c n) (N n))
      (partLam (B n) (plSpec α (c n) (N n)) 1) = 1 :=
    hbij.invOn_invFunOn.2 ⟨zero_lt_one, hγ⟩
  have hbound := p14_partMN_scaled_bound (B := B n) _ hp (i n) (le_trans hy₀.le hy.1)
  rw [mul_div_cancel_left₀ _ (hp (i n)).ne', hinv] at hbound
  have ha : 1 ≤ K * partMN (B n) (plSpec α (c n) (N n))
      (1 / plSpec α (c n) (N n) (i n)) :=
    hbound.trans (mul_le_mul_of_nonneg_right (max_le_max hy.2 le_rfl) hapos.le)
  by_contra h
  have hbM : bCoef α (B n) (i n) ≤ M := (lt_of_not_ge h).le.trans (le_max_left _ _)
  have hb2 := pow_le_pow_left₀ hbpos.le hbM 2
  rw [div_lt_div_iff₀ (sq_pos_of_pos hbpos) (mul_pos hK (sq_pos_of_pos hM))] at hn
  have ham := mul_le_mul_of_nonneg_right ha (sq_nonneg M)
  nlinarith

/-- `a_i = m_N(1/μ_i)`: `a_i ∼ γ x^α/(1-α)` for `α < 1` (task L-G.7b; proof step of `lem:app-pl-vector`,
l.1991-1993; snapshot cr-2026-10-23). -/
theorem aRow_asymp_lt {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α < 1)
    (i : ∀ n, Fin (N n)) (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    IsEquivalent atTop
      (fun n => partMN (B n) (plSpec α (c n) (N n)) (1 / plSpec α (c n) (N n) (i n)))
      (fun n => gammaOf (N n) (B n) * rowFrac (i n) ^ α / (1 - α)) := by
  have he := (IsEquivalent.refl (l := atTop) (u := fun n => gammaOf (N n) (B n))).mul
    (p14_fin_lt R.hα hα1 R.hNpos i hi hx)
  refine (he.congr_left ?_).congr_right ?_
  · filter_upwards [] with n
    rw [p14_partMN_eq (R.hNpos n) (R.hBpos n) (R.hcpos n)]
    rfl
  · filter_upwards [] with n
    simp only [Pi.mul_apply, mul_div_assoc]

/-- `a_i = m_N(1/μ_i)`: `a_i ∼ γ x log(1/x)` for `α = 1` (task L-G.7b; proof step of `lem:app-pl-vector`,
l.1991-1993; snapshot cr-2026-10-23). -/
theorem aRow_asymp_one {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α = 1)
    (i : ∀ n, Fin (N n)) (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0)) :
    IsEquivalent atTop
      (fun n => partMN (B n) (plSpec α (c n) (N n)) (1 / plSpec α (c n) (N n) (i n)))
      (fun n => gammaOf (N n) (B n) * rowFrac (i n) * Real.log (1 / rowFrac (i n))) := by
  subst α
  have he := (IsEquivalent.refl (l := atTop) (u := fun n => gammaOf (N n) (B n))).mul
    (p14_fin_one R.hNpos i hi hx)
  refine (he.congr_left ?_).congr_right ?_
  · filter_upwards [] with n
    rw [p14_partMN_eq (R.hNpos n) (R.hBpos n) (R.hcpos n), Real.rpow_one]
    rfl
  · filter_upwards [] with n
    simp only [Pi.mul_apply, mul_assoc]

/-- If `b` is bounded then `a_i → 0` (`a_i ≍ b²/T² → 0`) (task L-G.7b; proof step of `lem:app-pl-vector`,
l.1993-1994; snapshot cr-2026-10-23). -/
theorem aRow_tendsto_zero_of_b_bounded {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1)
    (i : ∀ n, Fin (N n)) (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowFrac (i n)) atTop (𝓝 0))
    (L : ℝ) (hb : ∀ᶠ n in atTop, bCoef α (B n) (i n) ≤ L) :
    Tendsto (fun n => partMN (B n) (plSpec α (c n) (N n)) (1 / plSpec α (c n) (N n) (i n)))
      atTop (𝓝 0) := by
  let M : ℝ := max L 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have ht := (p14_ratio_zero R hα1 i hi hx).mul_const (M ^ 2)
  simp only [zero_mul] at ht
  refine squeeze_zero' ?_ ?_ ht
  · exact Eventually.of_forall fun n =>
      (p11_m0_facts (α := α) (R.hNpos n) (R.hBpos n) (R.hcpos n) (i n)).1.1.le
  · filter_upwards [hb] with n hn
    have hp := p14_b_pos R.hα (R.hNpos n) (R.hBpos n) (i n)
    have ha := (p11_m0_facts (α := α) (R.hNpos n) (R.hBpos n) (R.hcpos n) (i n)).1.1
    have hbM : bCoef α (B n) (i n) ≤ M := hn.trans (le_max_left _ _)
    have hs := pow_le_pow_left₀ hp.le hbM 2
    have hm := mul_le_mul_of_nonneg_left hs (div_nonneg ha.le (sq_nonneg (bCoef α (B n) (i n))))
    simpa only [div_mul_cancel₀ _ (pow_ne_zero 2 hp.ne')] using hm

private lemma p13_partMN_mono {N B : ℕ} (μ : Fin N → ℝ)
    (hμ : ∀ j, 0 < μ j) : MonotoneOn (partMN B μ) (Ici 0) := by
  intro x hx y hy hxy
  unfold partMN
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j _
  have hxj : 0 ≤ x * μ j := mul_nonneg hx (hμ j).le
  have hyj : 0 ≤ y * μ j := mul_nonneg hy (hμ j).le
  have hxyj := mul_le_mul_of_nonneg_right hxy (hμ j).le
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

private lemma p13_partMN_scale {N B : ℕ} (μ : Fin N → ℝ)
    (hμ : ∀ j, 0 < μ j) {s t : ℝ} (hs : 1 ≤ s) (ht : 0 ≤ t) :
    partMN B μ (s * t) ≤ s * partMN B μ t := by
  unfold partMN
  rw [show s * ((B : ℝ)⁻¹ * ∑ j, t * μ j / (1 + t * μ j)) =
    (B : ℝ)⁻¹ * ∑ j, s * (t * μ j / (1 + t * μ j)) by
      rw [← Finset.mul_sum]; ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j _
  have htj : 0 ≤ t * μ j := mul_nonneg ht (hμ j).le
  have hstj : 0 ≤ s * (t * μ j) := mul_nonneg (by linarith) htj
  rw [← mul_div_assoc, mul_assoc]
  exact div_le_div_of_nonneg_left hstj (by positivity) (by nlinarith)

private lemma p13_partMN_scaled_bound {N B : ℕ} (μ : Fin N → ℝ)
    (hμ : ∀ j, 0 < μ j) (i : Fin N) {u : ℝ} (hu : 0 ≤ u) :
    partMN B μ (u / μ i) ≤ max u 1 * partMN B μ (1 / μ i) := by
  have hi := hμ i
  have hmax : 0 ≤ max u 1 := le_trans zero_le_one (le_max_right _ _)
  calc
    partMN B μ (u / μ i) ≤ partMN B μ (max u 1 * (1 / μ i)) := by
      apply p13_partMN_mono μ hμ (div_nonneg hu (hμ i).le)
        (show 0 ≤ max u 1 * (1 / μ i) by positivity)
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_right (le_max_left u 1) (inv_nonneg.2 (hμ i).le)
    _ ≤ _ := p13_partMN_scale μ hμ (le_max_right _ _) (by positivity)

private lemma p13_scaled_partMN_tendsto {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (i : ∀ n, Fin (N n))
    (ha : Tendsto (fun n => partMN (B n) (plSpec α (c n) (N n))
      (1 / plSpec α (c n) (N n) (i n))) atTop (𝓝 0)) {u : ℝ} (hu : 0 < u) :
    Tendsto (fun n => partMN (B n) (plSpec α (c n) (N n))
      (u / plSpec α (c n) (N n) (i n))) atTop (𝓝[>] 0) := by
  have hpos : ∀ n, 0 < partMN (B n) (plSpec α (c n) (N n))
      (u / plSpec α (c n) (N n) (i n)) := fun n =>
    ((def_app_pl_participation_bij _ (R.hBpos n) (R.hNpos n)
      (p11_pos_plSpec (R.hcpos n) _)).1.mapsTo
        (div_pos hu (p11_pos_plSpec (R.hcpos n) _ _))).1
  apply tendsto_nhdsWithin_iff.2
  refine ⟨?_, Eventually.of_forall hpos⟩
  have hupper : Tendsto (fun n => max u 1 * partMN (B n) (plSpec α (c n) (N n))
      (1 / plSpec α (c n) (N n) (i n))) atTop (𝓝 0) := by
    simpa using ha.const_mul (max u 1)
  exact squeeze_zero (fun n => (hpos n).le)
    (fun n => p13_partMN_scaled_bound _ (p11_pos_plSpec (R.hcpos n) _) _ hu.le) hupper

private lemma p13_cutoff_tendsto {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (i : ∀ n, Fin (N n))
    (ha : Tendsto (fun n => partMN (B n) (plSpec α (c n) (N n))
      (1 / plSpec α (c n) (N n) (i n))) atTop (𝓝 0)) {M : ℝ} (hM : 0 < M) :
    Tendsto (fun n => plSpec α (c n) (N n) (i n) *
      partLam (B n) (plSpec α (c n) (N n)) M) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  let u := max b 1
  have hu : 0 < u := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have ht := (p13_scaled_partMN_tendsto R i ha hu).mono_right nhdsWithin_le_nhds
  filter_upwards [ht.eventually (eventually_lt_nhds hM),
    R.hγ.eventually_gt_atTop M] with n hn hγ
  have hp := p11_pos_plSpec (α := α) (R.hcpos n) (N n)
  obtain ⟨hbM, _, hmono, _⟩ := def_app_pl_participation_bij _ (R.hBpos n) (R.hNpos n) hp
  have hx : u / plSpec α (c n) (N n) (i n) ∈ Ioi (0 : ℝ) := div_pos hu (hp _)
  have hinv : partLam (B n) (plSpec α (c n) (N n))
      (partMN (B n) (plSpec α (c n) (N n)) (u / plSpec α (c n) (N n) (i n))) =
      u / plSpec α (c n) (N n) (i n) := hbM.invOn_invFunOn.1 hx
  have hlt := hmono (hbM.mapsTo hx) ⟨hM, hγ⟩ hn
  rw [hinv, div_lt_iff₀ (hp _)] at hlt
  exact (show b ≤ u from le_max_left b 1).trans (by simpa [mul_comm] using hlt.le)

private lemma p13_lam_deriv_bounds {α : ℝ} (hα : 0 < α) {N B : ℕ} {c : ℝ}
    (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) {m : ℝ}
    (hm : m ∈ Ioo 0 (gammaOf N B)) :
    0 < deriv (partLam B (plSpec α c N)) m ∧
      0 ≤ partLam B (plSpec α c N) m / deriv (partLam B (plSpec α c N)) m ∧
      partLam B (plSpec α c N) m / deriv (partLam B (plSpec α c N)) m ≤ m := by
  obtain ⟨_, _, he⟩ := lem_app_pl_elasticity_i hα
  have h := ((he N B c hN hB hc).2 m hm).1
  have hL := (p12_pg6p2_Lam_hasDeriv (plSpec α c N) hB hN (p11_pos_plSpec hc _) hm).1
  have hd : 0 < deriv (partLam B (plSpec α c N)) m := by
    have hq := lt_of_lt_of_le (one_div_pos.2 hm.1) h
    exact (div_pos_iff_of_pos_right hL).mp hq
  refine ⟨hd, (div_pos hL hd).le, ?_⟩
  rw [div_le_iff₀ hd]
  rw [div_le_div_iff₀ hm.1 hL] at h
  simpa only [one_mul, mul_comm] using h

private lemma p13_change_variable {α : ℝ} (hα : 0 < α) {N B : ℕ} {c M : ℝ}
    (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) (i : Fin N)
    (hM : M ∈ Ioo 0 (gammaOf N B)) (H : ℝ → ℝ) :
    (∫ m in Ioo 0 M, H m) =
      ∫ u in Ioo 0 (plSpec α c N i * partLam B (plSpec α c N) M),
        H (partMN B (plSpec α c N) (u / plSpec α c N i)) /
          (plSpec α c N i * deriv (partLam B (plSpec α c N))
            (partMN B (plSpec α c N) (u / plSpec α c N i))) := by
  let μ := plSpec α c N
  let f := fun m => μ i * partLam B μ m
  have hp := p11_pos_plSpec (α := α) hc N
  obtain ⟨hbM, hbL, hmono, _⟩ := def_app_pl_participation_bij μ hB hN hp
  have hsub : Ioo (0 : ℝ) M ⊆ Ioo 0 (gammaOf N B) := fun m hm => ⟨hm.1, hm.2.trans hM.2⟩
  have hright : ∀ m ∈ Ioo 0 (gammaOf N B), partMN B μ (partLam B μ m) = m :=
    fun m hm => hbM.invOn_invFunOn.2 hm
  have himage : f '' Ioo 0 M = Ioo 0 (μ i * partLam B μ M) := by
    ext u
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨mul_pos (hp _) (hbL.mapsTo (hsub hm)),
        mul_lt_mul_of_pos_left (hmono (hsub hm) hM hm.2) (hp _)⟩
    · intro hu
      have hx : u / μ i ∈ Ioi (0 : ℝ) := div_pos hu.1 (hp _)
      have hinv : partLam B μ (partMN B μ (u / μ i)) = u / μ i := hbM.invOn_invFunOn.1 hx
      refine ⟨partMN B μ (u / μ i), ⟨(hbM.mapsTo hx).1, ?_⟩, ?_⟩
      · apply (hmono.lt_iff_lt (hbM.mapsTo hx) hM).mp
        rw [hinv, div_lt_iff₀ (hp _)]
        simpa only [mul_comm] using hu.2
      · dsimp [f]
        rw [hinv, mul_div_cancel₀ _ (hp _).ne']
  have hder : ∀ m ∈ Ioo 0 M, HasDerivWithinAt f
      (μ i * deriv (partLam B μ) m) (Ioo 0 M) m := by
    intro m hm
    exact ((p12_pg6p2_Lam_hasDeriv μ hB hN hp (hsub hm)).2.const_mul (μ i)).hasDerivWithinAt
  have hinj : InjOn f (Ioo 0 M) := by
    intro x hx y hy hxy
    apply hmono.injOn (hsub hx) (hsub hy)
    exact mul_left_cancel₀ (hp _).ne' hxy
  have hcv := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hder hinj
    (fun u => H (partMN B μ (u / μ i)) /
      (μ i * deriv (partLam B μ) (partMN B μ (u / μ i))))
  rw [himage] at hcv
  refine Eq.trans ?_ hcv.symm
  apply setIntegral_congr_fun measurableSet_Ioo
  intro m hm
  have hd := (p13_lam_deriv_bounds hα hN hB hc (hsub hm)).1
  have he : partMN B μ (f m / μ i) = m := by
    dsimp [f]
    rw [mul_div_cancel_left₀ _ (hp _).ne', hright m (hsub hm)]
  dsimp only
  rw [he, abs_of_pos (mul_pos (hp _) hd)]
  simp only [smul_eq_mul]
  exact (mul_div_cancel₀ _ (mul_pos (hp _) hd).ne').symm

private lemma p13_kernel_integral :
    IntegrableOn (fun u : ℝ => 1 / (Real.sqrt u * (1 + u))) (Ioi 0) ∧
      (∫ u : ℝ in Ioi 0, 1 / (Real.sqrt u * (1 + u))) = Real.pi := by
  have him : (fun v : ℝ => v ^ 2) '' Ioi 0 = Ioi 0 := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact sq_pos_of_pos (show 0 < v from hv)
    · intro hu
      exact ⟨Real.sqrt u, Real.sqrt_pos.2 hu, Real.sq_sqrt hu.le⟩
  have hd : ∀ v ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun v : ℝ => v ^ 2)
      (2 * v) (Ioi 0) v := by
    intro v _
    simpa using (hasDerivAt_pow 2 v).hasDerivWithinAt (s := Ioi (0 : ℝ))
  have hinj : InjOn (fun v : ℝ => v ^ 2) (Ioi 0) := by
    intro x hx y hy he
    change 0 < x at hx
    change 0 < y at hy
    change x ^ 2 = y ^ 2 at he
    nlinarith
  have he : ∀ v ∈ Ioi (0 : ℝ), |2 * v| • (1 / (Real.sqrt (v ^ 2) * (1 + v ^ 2))) =
      2 * (1 + v ^ 2)⁻¹ := by
    intro v hv
    rw [abs_of_pos (mul_pos (by norm_num) hv), Real.sqrt_sq hv.le, smul_eq_mul]
    field_simp [ne_of_gt (show 0 < v from hv)]
  have hi : IntegrableOn (fun v : ℝ => 2 * (1 + v ^ 2)⁻¹) (Ioi 0) :=
    integrable_inv_one_add_sq.integrableOn.const_mul 2
  have hcv := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj
    (fun u : ℝ => 1 / (Real.sqrt u * (1 + u)))
  have hci := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd hinj
    (fun u : ℝ => 1 / (Real.sqrt u * (1 + u)))
  rw [him] at hcv hci
  refine ⟨hci.mpr (hi.congr (ae_restrict_iff' measurableSet_Ioi |>.2
    (Eventually.of_forall fun v hv => (he v hv).symm))), ?_⟩
  calc
    _ = ∫ v : ℝ in Ioi 0, |2 * v| • (1 / (Real.sqrt (v ^ 2) * (1 + v ^ 2))) := hcv
    _ = ∫ v : ℝ in Ioi 0, 2 * (1 + v ^ 2)⁻¹ := setIntegral_congr_fun measurableSet_Ioi he
    _ = Real.pi := by rw [integral_const_mul, integral_Ioi_inv_one_add_sq,
      Real.arctan_zero]; ring

private lemma p13_Z_term_bound {β q : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hq : 0 ≤ q) (g : ℝ) (a : ℕ) :
    ‖emaW β a * g / (1 + emaW β a ^ 2 * q * g ^ 2)‖ ≤ emaW β a * |g| := by
  have hw := (vsh_emaW_pos hβ0 hβ1 a).le
  have hden : 1 ≤ 1 + emaW β a ^ 2 * q * g ^ 2 :=
    le_add_of_nonneg_right (mul_nonneg (mul_nonneg (sq_nonneg _) hq) (sq_nonneg _))
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hw,
    abs_of_pos (lt_of_lt_of_le zero_lt_one hden)]
  exact div_le_self (mul_nonneg hw (abs_nonneg g)) hden

private lemma p13_Z_abs_le {β q : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hq : 0 ≤ q) (g : ℝ) : |Zg β g q| ≤ Real.sqrt q * |g| := by
  have hs := ((vsh_weightSeq hβ0 hβ1).2.1).mul_right |g|
  have hz := Summable.of_norm_bounded hs (p13_Z_term_bound hβ0 hβ1 hq g)
  unfold Zg
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg q)]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg q)
  calc
    _ ≤ ∑' a, ‖emaW β a * g / (1 + emaW β a ^ 2 * q * g ^ 2)‖ :=
      norm_tsum_le_tsum_norm hz.norm
    _ ≤ ∑' a, emaW β a * |g| :=
      hz.norm.tsum_le_tsum (p13_Z_term_bound hβ0 hβ1 hq g) hs
    _ = |g| := by rw [tsum_mul_right, tsum_emaW hβ0.le hβ1, one_mul]

private lemma p13_Z_small {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (g : ℝ) :
    Tendsto (fun q : ℝ => Zg β g q / Real.sqrt q) (𝓝[>] 0) (𝓝 g) := by
  have ht : Tendsto (fun q : ℝ => ∑' a : ℕ,
      emaW β a * g / (1 + emaW β a ^ 2 * q * g ^ 2)) (𝓝[>] 0)
      (𝓝 (∑' a : ℕ, emaW β a * g)) := by
    apply tendsto_tsum_of_dominated_convergence
      (((vsh_weightSeq hβ0 hβ1).2.1).mul_right |g|)
    · intro a
      have hq : Tendsto (fun q : ℝ => q) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      convert tendsto_const_nhds.div
        (tendsto_const_nhds.add ((hq.const_mul (emaW β a ^ 2)).mul_const (g ^ 2)))
        (by norm_num : (1 + emaW β a ^ 2 * (0 : ℝ) * g ^ 2) ≠ 0) using 1 <;> simp
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact p13_Z_term_bound hβ0 hβ1 hq.le g
  rw [tsum_mul_right, tsum_emaW hβ0.le hβ1, one_mul] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  unfold Zg
  exact (mul_div_cancel_left₀ _ (Real.sqrt_pos.2 hq).ne').symm

private lemma p13_small_weights {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun m : ℝ => m / Efun β m) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (fun m : ℝ => Real.sqrt (Qm β m) / Real.sqrt m) (𝓝[>] 0)
      (𝓝 (1 / Real.sqrt (sPow β 2))) ∧
    Tendsto (Qm β) (𝓝[>] 0) (𝓝[>] 0) := by
  have hs2 : 0 < sPow β 2 := by
    rw [sPow_two hβ0.le hβ1]; apply div_pos <;> linarith
  have hmne : ∀ᶠ m : ℝ in 𝓝[>] 0, m ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with m hm
    exact ne_of_gt hm
  have hQ := (isEquivalent_iff_tendsto_one (hmne.mono fun m hm => div_ne_zero hm hs2.ne')).1
    (lem_app_pl_weights_i_Q hβ0.le hβ1)
  have hE := (isEquivalent_iff_tendsto_one hmne).1 (lem_app_pl_weights_i_E hβ0.le hβ1)
  have hQm : Tendsto (fun m : ℝ => Qm β m / m) (𝓝[>] 0) (𝓝 (1 / sPow β 2)) := by
    convert hQ.div_const (sPow β 2) using 1 <;> simp [Pi.div_apply, div_div, hs2.ne']
  have hEm : Tendsto (fun m : ℝ => m / Efun β m) (𝓝[>] 0) (𝓝 1) := by
    simpa only [Pi.div_apply, inv_div, inv_one] using hE.inv₀ one_ne_zero
  refine ⟨hEm, ?_, ?_⟩
  · have hsq := (Real.continuous_sqrt.tendsto _).comp hQm
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one] at hsq
    refine hsq.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with m hm
    exact Real.sqrt_div (vsh_Qm hβ0 hβ1 hm).1.le _
  · apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, ?_⟩
    · have hz := hQm.mul (tendsto_id.mono_left nhdsWithin_le_nhds)
      rw [mul_zero] at hz
      refine hz.congr' ?_
      filter_upwards [hmne] with m hm
      exact div_mul_cancel₀ _ hm
    · filter_upwards [self_mem_nhdsWithin] with m hm
      exact (vsh_Qm hβ0 hβ1 hm).1

private lemma p13_theta_error {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B) (hc : 0 < c)
    {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    0 ≤ thetaN β B (plSpec α c N) m *
      (partLam B (plSpec α c N) m / deriv (partLam B (plSpec α c N)) m) - 1 ∧
    thetaN β B (plSpec α c N) m *
      (partLam B (plSpec α c N) m / deriv (partLam B (plSpec α c N)) m) - 1 ≤
        m / Efun β m - 1 + m / (gammaOf N B - m) := by
  have hL := (p12_pg6p2_Lam_hasDeriv (plSpec α c N) hB hN (p11_pos_plSpec hc _) hm).1
  obtain ⟨hd, hr0, hrm⟩ := p13_lam_deriv_bounds hα hN hB hc hm
  have hE := vsh_Efun_pos hβ0 hβ1 hm.1
  have hEm := lem_app_pl_weights_ii_E hβ0 hβ1 m hm.1
  have hgap : 0 < gammaOf N B - m := sub_pos.2 hm.2
  have hdiff : 0 ≤ 1 / Efun β m - 1 / m :=
    sub_nonneg.2 (one_div_le_one_div_of_le hE hEm)
  have hid : thetaN β B (plSpec α c N) m *
      (partLam B (plSpec α c N) m / deriv (partLam B (plSpec α c N)) m) - 1 =
      (partLam B (plSpec α c N) m / deriv (partLam B (plSpec α c N)) m) *
        (1 / Efun β m - 1 / m + 1 / (gammaOf N B - m)) := by
    unfold thetaN
    field_simp [hL.ne', hd.ne']
    <;> ring
  rw [hid]
  refine ⟨mul_nonneg hr0 (add_nonneg hdiff (one_div_pos.2 hgap).le), ?_⟩
  calc
    _ ≤ m * (1 / Efun β m - 1 / m + 1 / (gammaOf N B - m)) :=
      mul_le_mul_of_nonneg_right hrm (add_nonneg hdiff (one_div_pos.2 hgap).le)
    _ = _ := by field_simp [hm.1.ne', hE.ne', hgap.ne']

private lemma p13_theta_tendsto {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) {m : ℕ → ℝ}
    (hm : Tendsto m atTop (𝓝[>] 0))
    (hmg : ∀ᶠ n in atTop, m n < gammaOf (N n) (B n)) :
    Tendsto (fun n => thetaN β (B n) (plSpec α (c n) (N n)) (m n) *
      (partLam (B n) (plSpec α (c n) (N n)) (m n) /
        deriv (partLam (B n) (plSpec α (c n) (N n))) (m n))) atTop (𝓝 1) := by
  have hm0 := hm.mono_right nhdsWithin_le_nhds
  have hgap : Tendsto (fun n => gammaOf (N n) (B n) - m n) atTop atTop :=
    tendsto_atTop.2 fun b => by
      filter_upwards [R.hγ.eventually_ge_atTop (b + 1),
        hm0.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with n hn hmn
      change b + 1 ≤ gammaOf (N n) (B n) at hn
      linarith
  have htail : Tendsto (fun n => m n / (gammaOf (N n) (B n) - m n)) atTop (𝓝 0) :=
    hm0.div_atTop hgap
  have hupper := (((p13_small_weights R.hβ0 R.hβ1).1.comp hm).sub_const 1).add htail
  simp only [sub_self, add_zero] at hupper
  have he : Tendsto (fun n => thetaN β (B n) (plSpec α (c n) (N n)) (m n) *
      (partLam (B n) (plSpec α (c n) (N n)) (m n) /
        deriv (partLam (B n) (plSpec α (c n) (N n))) (m n)) - 1) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hupper
    · filter_upwards [hm.eventually self_mem_nhdsWithin, hmg] with n hn hgn
      exact (p13_theta_error R.hα R.hβ0 R.hβ1 (R.hNpos n) (R.hBpos n) (R.hcpos n) ⟨hn, hgn⟩).1
    · filter_upwards [hm.eventually self_mem_nhdsWithin, hmg] with n hn hgn
      exact (p13_theta_error R.hα R.hβ0 R.hβ1 (R.hNpos n) (R.hBpos n) (R.hcpos n) ⟨hn, hgn⟩).2
  simpa only [sub_add_cancel, zero_add] using he.add_const 1

private lemma p13_density_eq {α β : ℝ} (hα : 0 < α) {N B : ℕ} {c : ℝ}
    (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) (i : Fin N) {u : ℝ} (hu : 0 < u) (g : ℝ) :
    let m := partMN B (plSpec α c N) (u / plSpec α c N i)
    Wpart β B (plSpec α c N) i m * Zg β g (Qm β m) /
      (plSpec α c N i * deriv (partLam B (plSpec α c N)) m) =
    1 / (Real.sqrt u * (1 + u)) *
      (Real.sqrt (1 - m / gammaOf N B) *
        (thetaN β B (plSpec α c N) m *
          (partLam B (plSpec α c N) m / deriv (partLam B (plSpec α c N)) m)) *
        (Zg β g (Qm β m) / Real.sqrt m)) := by
  dsimp only
  let μ := plSpec α c N
  let m := partMN B μ (u / μ i)
  have hp := p11_pos_plSpec (α := α) hc N
  have hb := (def_app_pl_participation_bij μ hB hN hp).1
  have hx : u / μ i ∈ Ioi (0 : ℝ) := div_pos hu (hp _)
  have hm := hb.mapsTo hx
  have hL : partLam B μ m = u / μ i := hb.invOn_invFunOn.1 hx
  have hd := (p13_lam_deriv_bounds hα hN hB hc hm).1
  change Wpart β B μ i m * Zg β g (Qm β m) / (μ i * deriv (partLam B μ) m) = _
  unfold Wpart
  change _ = 1 / (Real.sqrt u * (1 + u)) *
    (Real.sqrt (1 - m / gammaOf N B) *
      (thetaN β B μ m * (partLam B μ m / deriv (partLam B μ) m)) *
      (Zg β g (Qm β m) / Real.sqrt m))
  rw [hL, mul_div_cancel₀ _ (hp _).ne']
  have hsu := Real.sq_sqrt hu.le
  have hsu0 := (Real.sqrt_pos.2 hu).ne'
  have hsm0 := (Real.sqrt_pos.2 hm.1).ne'
  field_simp [hsu0, hsm0, hd.ne', (hp _).ne']
  rw [hsu]

private lemma p13_density_tendsto {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (i : ∀ n, Fin (N n))
    (ha : Tendsto (fun n => partMN (B n) (plSpec α (c n) (N n))
      (1 / plSpec α (c n) (N n) (i n))) atTop (𝓝 0)) {u : ℝ} (hu : 0 < u) (g : ℝ) :
    Tendsto (fun n =>
      let m := partMN (B n) (plSpec α (c n) (N n)) (u / plSpec α (c n) (N n) (i n))
      Wpart β (B n) (plSpec α (c n) (N n)) (i n) m * Zg β g (Qm β m) /
        (plSpec α (c n) (N n) (i n) * deriv (partLam (B n) (plSpec α (c n) (N n))) m))
      atTop (𝓝 (1 / (Real.sqrt u * (1 + u)) * (g / Real.sqrt (sPow β 2)))) := by
  let m := fun n => partMN (B n) (plSpec α (c n) (N n)) (u / plSpec α (c n) (N n) (i n))
  have hm := p13_scaled_partMN_tendsto R i ha hu
  have hm0 := hm.mono_right nhdsWithin_le_nhds
  have hmg : ∀ n, m n ∈ Ioo 0 (gammaOf (N n) (B n)) := fun n =>
    (def_app_pl_participation_bij _ (R.hBpos n) (R.hNpos n)
      (p11_pos_plSpec (R.hcpos n) _)).1.mapsTo
        (div_pos hu (p11_pos_plSpec (R.hcpos n) _ _))
  have hshell : Tendsto (fun n => Real.sqrt (1 - m n / gammaOf (N n) (B n))) atTop (𝓝 1) := by
    have ht := ((tendsto_const_nhds (x := (1 : ℝ))).sub (hm0.div_atTop R.hγ)).sqrt
    simpa [m, gammaOf] using ht
  have htheta := p13_theta_tendsto R hm (Eventually.of_forall fun n => (hmg n).2)
  have hq := (p13_small_weights R.hβ0 R.hβ1).2.2.comp hm
  have hZ := (p13_Z_small R.hβ0 R.hβ1 g).comp hq
  have hs := (p13_small_weights R.hβ0 R.hβ1).2.1.comp hm
  have hZs : Tendsto (fun n => Zg β g (Qm β (m n)) / Real.sqrt (m n)) atTop
      (𝓝 (g / Real.sqrt (sPow β 2))) := by
    have ht := hZ.mul hs
    simp only [mul_one_div] at ht
    refine ht.congr' (Eventually.of_forall fun n => ?_)
    have hsq := (Real.sqrt_pos.2 (vsh_Qm R.hβ0 R.hβ1 (hmg n).1).1).ne'
    change Zg β g (Qm β (m n)) / Real.sqrt (Qm β (m n)) *
      (Real.sqrt (Qm β (m n)) / Real.sqrt (m n)) = _
    field_simp [hsq]
  have ht := ((hshell.mul htheta).mul hZs).const_mul (1 / (Real.sqrt u * (1 + u)))
  simp only [one_mul] at ht
  refine ht.congr' (Eventually.of_forall fun n => ?_)
  exact (p13_density_eq R.hα (R.hNpos n) (R.hBpos n) (R.hcpos n) (i n) hu g).symm

private lemma p13_theta_bound {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    {N B : ℕ} {c G e : ℝ} (hN : 0 < N) (hB : 0 < B) (hc : 0 < c)
    (hG : 1 ≤ G) (he : 0 < e) (hE : ∀ m, 0 < m → e * min m 1 ≤ Efun β m)
    (hγ : 2 * G ≤ gammaOf N B) {m : ℝ} (hm : 0 < m) (hmG : m ≤ G) :
    0 ≤ thetaN β B (plSpec α c N) m *
      (partLam B (plSpec α c N) m / deriv (partLam B (plSpec α c N)) m) ∧
    thetaN β B (plSpec α c N) m *
      (partLam B (plSpec α c N) m / deriv (partLam B (plSpec α c N)) m) ≤ G / e + 1 := by
  have hmγ : m < gammaOf N B := by linarith
  obtain ⟨hlo, hhi⟩ := p13_theta_error hα hβ0 hβ1 hN hB hc ⟨hm, hmγ⟩
  have hEp := vsh_Efun_pos hβ0 hβ1 hm
  have hmin : m ≤ G * min m 1 := by
    rcases le_total m 1 with h | h
    · rw [min_eq_left h]
      nlinarith
    · rw [min_eq_right h, mul_one]
      exact hmG
  have hme : m / Efun β m ≤ G / e := by
    rw [div_le_div_iff₀ hEp he]
    have := mul_le_mul_of_nonneg_left (hE m hm) (by linarith : 0 ≤ G)
    nlinarith
  have htail : m / (gammaOf N B - m) ≤ 1 := by
    rw [div_le_one (by linarith : 0 < gammaOf N B - m)]
    linarith
  constructor <;> linarith

private lemma p13_density_bound {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    {N B : ℕ} {c G e : ℝ} (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) (i : Fin N)
    (hG : 1 ≤ G) (he : 0 < e) (hE : ∀ m, 0 < m → e * min m 1 ≤ Efun β m)
    (hγ : 2 * G ≤ gammaOf N B) {u : ℝ} (hu : 0 < u)
    (hmG : partMN B (plSpec α c N) (u / plSpec α c N i) ≤ G) (g : ℝ) :
    let m := partMN B (plSpec α c N) (u / plSpec α c N i)
    |Wpart β B (plSpec α c N) i m * Zg β g (Qm β m) /
      (plSpec α c N i * deriv (partLam B (plSpec α c N)) m)| ≤
      1 / (Real.sqrt u * (1 + u)) * ((G / e + 1) * Real.sqrt (Qm β G) * |g|) := by
  let m := partMN B (plSpec α c N) (u / plSpec α c N i)
  have hm := (def_app_pl_participation_bij (plSpec α c N) hB hN (p11_pos_plSpec hc _)).1.mapsTo
    (div_pos hu (p11_pos_plSpec (α := α) hc _ i))
  have hγ0 : 0 < gammaOf N B := by linarith
  obtain ⟨hθ0, hθ⟩ := p13_theta_bound hα hβ0 hβ1 hN hB hc hG he hE hγ hm.1 hmG
  have hQG := (vsh_Qm hβ0 hβ1 (by linarith : 0 < G)).1
  have hQ := (llk_K1 hβ0 hβ1 hm.1 hmG hG).trans
    (mul_le_mul_of_nonneg_left (min_le_left m 1) hQG.le)
  have hsQ : Real.sqrt (Qm β m) / Real.sqrt m ≤ Real.sqrt (Qm β G) := by
    rw [div_le_iff₀ (Real.sqrt_pos.2 hm.1), ← Real.sqrt_mul hQG.le]
    exact Real.sqrt_le_sqrt hQ
  have hshell : Real.sqrt (1 - m / gammaOf N B) ≤ 1 := by
    rw [Real.sqrt_le_one]
    have := div_nonneg hm.1.le hγ0.le
    linarith
  dsimp only
  rw [p13_density_eq (β := β) hα hN hB hc i hu g]
  change |1 / (Real.sqrt u * (1 + u)) *
    (Real.sqrt (1 - m / gammaOf N B) *
      (thetaN β B (plSpec α c N) m *
        (partLam B (plSpec α c N) m / deriv (partLam B (plSpec α c N)) m)) *
      (Zg β g (Qm β m) / Real.sqrt m))| ≤ _
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (Real.sqrt u * (1 + u))),
    abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hθ0,
    abs_div, abs_of_nonneg (Real.sqrt_nonneg m)]
  have hZ : |Zg β g (Qm β m)| / Real.sqrt m ≤ Real.sqrt (Qm β G) * |g| := by
    calc
      _ ≤ (Real.sqrt (Qm β m) * |g|) / Real.sqrt m :=
        div_le_div_of_nonneg_right (p13_Z_abs_le hβ0 hβ1 (vsh_Qm hβ0 hβ1 hm.1).1.le g)
          (Real.sqrt_nonneg m)
      _ = (Real.sqrt (Qm β m) / Real.sqrt m) * |g| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsQ (abs_nonneg g)
  calc
    _ ≤ 1 / (Real.sqrt u * (1 + u)) * (1 * (G / e + 1) * (Real.sqrt (Qm β G) * |g|)) := by
      gcongr
    _ = _ := by ring

private lemma p13_density_meas {α β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) (i : Fin N) (g : ℝ) :
    AEStronglyMeasurable (fun u : ℝ =>
      let m := partMN B (plSpec α c N) (u / plSpec α c N i)
      Wpart β B (plSpec α c N) i m * Zg β g (Qm β m) /
        (plSpec α c N i * deriv (partLam B (plSpec α c N)) m)) (volume.restrict (Ioi 0)) := by
  let μ := plSpec α c N
  let m : ℝ → ℝ := fun u => partMN B μ (u / μ i)
  have hp := p11_pos_plSpec (α := α) hc N
  have hb := (def_app_pl_participation_bij μ hB hN hp).1
  have hm : ∀ u : Ioi (0 : ℝ), 0 < m u := fun u =>
    (hb.mapsTo (div_pos u.property (hp _))).1
  have hL : ∀ u : Ioi (0 : ℝ), partLam B μ (m u) = (u : ℝ) / μ i := fun u =>
    hb.invOn_invFunOn.1 (div_pos u.property (hp _))
  have hmm : Measurable (fun u : Ioi (0 : ℝ) => m u) := by
    dsimp [m, partMN]
    fun_prop
  have hQmono : Monotone (fun x : Ioi (0 : ℝ) => Qm β x) :=
    fun x y hxy => msm_Qm_mono hβ0 hβ1 x.property y.property hxy
  have hQ : Measurable (fun u : Ioi (0 : ℝ) => Qm β (m u)) :=
    hQmono.measurable.comp (hmm.subtype_mk (h := hm))
  have hLm : Measurable (fun u : Ioi (0 : ℝ) => partLam B μ (m u)) := by
    simp_rw [hL]
    exact measurable_subtype_coe.div_const _
  have hD : Measurable (fun u : Ioi (0 : ℝ) => deriv (partLam B μ) (m u)) :=
    (measurable_deriv _).comp hmm
  have hE : Measurable (fun u : Ioi (0 : ℝ) => Efun β (m u)) :=
    hQ.mul ((measurable_deriv _).comp hQ)
  have hθ : Measurable (fun u : Ioi (0 : ℝ) => thetaN β B μ (m u)) :=
    (((measurable_const.div hE).add (hD.div hLm)).add
      (measurable_const.div (measurable_const.sub hmm))).sub (measurable_const.div hmm)
  have hW : Measurable (fun u : Ioi (0 : ℝ) => Wpart β B μ i (m u)) := by
    unfold Wpart
    exact (((measurable_const.mul hLm).sqrt.div
      (hmm.sqrt.mul (measurable_const.add (measurable_const.mul hLm)))).mul
      (measurable_const.sub (hmm.div_const _)).sqrt).mul hθ
  have hZ : Measurable (fun u : Ioi (0 : ℝ) => Zg β g (Qm β (m u))) :=
    (p10_Zjoint_meas β).comp (measurable_const.prodMk hQ)
  exact (aemeasurable_restrict_of_measurable_subtype measurableSet_Ioi
    ((hW.mul hZ).div (measurable_const.mul hD))).aestronglyMeasurable

private lemma p13_scaled_lt_cutoff {α : ℝ} {N B : ℕ} {c M u : ℝ}
    (hN : 0 < N) (hB : 0 < B) (hc : 0 < c) (i : Fin N)
    (hM : M ∈ Ioo 0 (gammaOf N B)) (hu : 0 < u)
    (huM : u < plSpec α c N i * partLam B (plSpec α c N) M) :
    partMN B (plSpec α c N) (u / plSpec α c N i) < M := by
  have hp := p11_pos_plSpec (α := α) hc N
  obtain ⟨hbM, _, hmono, _⟩ := def_app_pl_participation_bij _ hB hN hp
  have hx : u / plSpec α c N i ∈ Ioi (0 : ℝ) := div_pos hu (hp _)
  apply (hmono.lt_iff_lt (hbM.mapsTo hx) hM).mp
  rw [show partLam B (plSpec α c N) (partMN B (plSpec α c N)
    (u / plSpec α c N i)) = u / plSpec α c N i from hbM.invOn_invFunOn.1 hx,
    div_lt_iff₀ (hp _)]
  simpa only [mul_comm] using huM

private lemma p13_head_u_limit {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c) (i : ∀ n, Fin (N n))
    (ha : Tendsto (fun n => partMN (B n) (plSpec α (c n) (N n))
      (1 / plSpec α (c n) (N n) (i n))) atTop (𝓝 0)) {M : ℝ} (hM : 0 < M) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ᶠ n in atTop, ∀ g : ℝ,
        |calVpart β (B n) (plSpec α (c n) (N n)) (i n) 0 M g| ≤ C * |g|) ∧
      ∀ g : ℝ, Tendsto (fun n => calVpart β (B n) (plSpec α (c n) (N n)) (i n) 0 M g)
        atTop (𝓝 (g / Real.sqrt (sPow β 2))) := by
  obtain ⟨e, _, he, _, hE⟩ := lem_app_pl_weights_iii_E R.hβ0 R.hβ1
  let G := max M 1
  let C := (G / e + 1) * Real.sqrt (Qm β G)
  let U := fun n => plSpec α (c n) (N n) (i n) * partLam (B n) (plSpec α (c n) (N n)) M
  let D := fun n u g =>
    let m := partMN (B n) (plSpec α (c n) (N n)) (u / plSpec α (c n) (N n) (i n))
    Wpart β (B n) (plSpec α (c n) (N n)) (i n) m * Zg β g (Qm β m) /
      (plSpec α (c n) (N n) (i n) * deriv (partLam (B n) (plSpec α (c n) (N n))) m)
  let F := fun n g => (Ioo 0 (U n)).indicator (fun u => D n u g)
  let k := fun u : ℝ => 1 / (Real.sqrt u * (1 + u))
  have hG : 1 ≤ G := le_max_right _ _
  have hMG : M ≤ G := le_max_left _ _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hγ : ∀ᶠ n in atTop, 2 * G ≤ gammaOf (N n) (B n) := R.hγ.eventually_ge_atTop _
  have hFM : ∀ n g, AEStronglyMeasurable (F n g) (volume.restrict (Ioi 0)) := fun n g =>
    (p13_density_meas R.hβ0 R.hβ1 (R.hNpos n) (R.hBpos n) (R.hcpos n) (i n) g).indicator
      measurableSet_Ioo
  have hbound : ∀ᶠ n in atTop, ∀ g u : ℝ, 0 < u → |F n g u| ≤ k u * (C * |g|) := by
    filter_upwards [hγ] with n hgn
    intro g u hu
    by_cases huU : u ∈ Ioo 0 (U n)
    · rw [show F n g u = D n u g from indicator_of_mem huU _]
      have hMγ : M ∈ Ioo 0 (gammaOf (N n) (B n)) := ⟨hM, by linarith⟩
      have hmu := p13_scaled_lt_cutoff (R.hNpos n) (R.hBpos n) (R.hcpos n) (i n) hMγ hu huU.2
      exact p13_density_bound R.hα R.hβ0 R.hβ1 (R.hNpos n) (R.hBpos n) (R.hcpos n)
        (i n) hG he (fun m hm => (hE m hm).1) hgn hu (hmu.le.trans hMG) g
    · rw [show F n g u = 0 from indicator_of_notMem huU _ , abs_zero]
      exact mul_nonneg (by dsimp [k]; positivity) (mul_nonneg hC (abs_nonneg _))
  have heq : ∀ᶠ n in atTop, ∀ g : ℝ,
      calVpart β (B n) (plSpec α (c n) (N n)) (i n) 0 M g =
        Real.pi⁻¹ * ∫ u in Ioi 0, F n g u := by
    filter_upwards [hγ] with n hgn
    intro g
    unfold calVpart
    rw [p13_change_variable R.hα (R.hNpos n) (R.hBpos n) (R.hcpos n) (i n) ⟨hM, by linarith⟩]
    dsimp only [F]
    rw [setIntegral_indicator measurableSet_Ioo, inter_eq_right.mpr Ioo_subset_Ioi_self]
  refine ⟨C, hC, ?_, ?_⟩
  · filter_upwards [hbound, heq] with n hn heqn
    intro g
    rw [heqn g, abs_mul, abs_of_pos (inv_pos.2 Real.pi_pos)]
    have hb : |∫ u in Ioi 0, F n g u| ≤ Real.pi * (C * |g|) := by
      have ht := norm_integral_le_of_norm_le (f := F n g) (p13_kernel_integral.1.mul_const (C * |g|))
        (ae_restrict_iff' measurableSet_Ioi |>.2 (Eventually.of_forall fun u hu => by
          simpa only [Real.norm_eq_abs] using hn g u hu))
      simpa only [Real.norm_eq_abs, integral_mul_const, p13_kernel_integral.2] using ht
    calc
      _ ≤ Real.pi⁻¹ * (Real.pi * (C * |g|)) :=
        mul_le_mul_of_nonneg_left hb (inv_pos.2 Real.pi_pos).le
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]
  · intro g
    have hlim : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))),
        Tendsto (fun n => F n g u) atTop (𝓝 (k u * (g / Real.sqrt (sPow β 2)))) := by
      apply ae_restrict_iff' measurableSet_Ioi |>.2
      apply Eventually.of_forall
      intro u hu
      have hU := p13_cutoff_tendsto R i ha hM
      refine (p13_density_tendsto R i ha hu g).congr' ?_
      filter_upwards [hU.eventually_gt_atTop u] with n hn
      exact (indicator_of_mem (show u ∈ Ioo 0 (U n) from ⟨hu, hn⟩) (fun v => D n v g)).symm
    have ht := tendsto_integral_filter_of_dominated_convergence
      (fun u => k u * (C * |g|)) (Eventually.of_forall fun n => hFM n g)
      (hbound.mono fun n hn => ae_restrict_iff' measurableSet_Ioi |>.2
        (Eventually.of_forall fun u hu => by simpa only [Real.norm_eq_abs] using hn g u hu))
      (p13_kernel_integral.1.mul_const (C * |g|)) hlim
    have hv : (∫ u in Ioi 0, k u * (g / Real.sqrt (sPow β 2))) =
        Real.pi * (g / Real.sqrt (sPow β 2)) := by
      rw [integral_mul_const]
      exact congrArg (fun x => x * (g / Real.sqrt (sPow β 2))) p13_kernel_integral.2
    rw [hv] at ht
    have ht' := ht.const_mul Real.pi⁻¹
    rw [← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul] at ht'
    exact ht'.congr' (heq.mono fun n hn => (hn g).symm)

/-- Head limit: if `a_i = m_N(1/μ_i) → 0` and `i → ∞`, then for fixed `M`,
`(1/π)∫_0^M W_i 𝒵_g dm → g/√ς₂` in `L²` (task L-G.7b; proof step of `lem:app-pl-vector`, l.1974-1989;
snapshot cr-2026-10-23). -/
theorem head_limit {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (R : assum_app_pl_regime α β N B c)
    (i : ∀ n, Fin (N n)) (hi : Tendsto (fun n => rowIdx (i n)) atTop atTop)
    (ha : Tendsto (fun n => partMN (B n) (plSpec α (c n) (N n)) (1 / plSpec α (c n) (N n) (i n)))
      atTop (𝓝 0)) (M : ℝ) (hM : 0 < M) :
    (∀ᶠ n in atTop, Integrable (fun g => (calVpart β (B n) (plSpec α (c n) (N n)) (i n) 0 M g -
        g / Real.sqrt (sPow β 2)) ^ 2) (gaussianReal 0 1)) ∧
    Tendsto (fun n => l2Norm (fun g => calVpart β (B n) (plSpec α (c n) (N n)) (i n) 0 M g -
        g / Real.sqrt (sPow β 2))) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb, ht⟩ := p13_head_u_limit R i ha hM
  let f := fun n g => calVpart β (B n) (plSpec α (c n) (N n)) (i n) 0 M g -
    g / Real.sqrt (sPow β 2)
  let A := C + 1 / Real.sqrt (sPow β 2)
  have hA : 0 ≤ A := add_nonneg hC (one_div_nonneg.2 (Real.sqrt_nonneg _))
  have hfm : ∀ᶠ n in atTop, AEStronglyMeasurable (f n) (gaussianReal 0 1) := by
    filter_upwards [Wpart_integrable_measurable R, R.hγ.eventually_gt_atTop M] with n hn hgn
    have hsub : Ioo (0 : ℝ) M ⊆ Ioo 0 (gammaOf (N n) (B n)) :=
      fun m hm => ⟨hm.1, hm.2.trans hgn⟩
    have hF := (hn (i n)).2.2.mono_measure
      (Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl)
    exact (hF.prod_swap.integral_prod_right'.const_mul Real.pi⁻¹).sub
      (measurable_id.div_const _).aestronglyMeasurable
  have hbound : ∀ᶠ n in atTop, ∀ g : ℝ, ‖f n g ^ 2‖ ≤ A ^ 2 * g ^ 2 := by
    filter_upwards [hb] with n hn
    intro g
    have hfg : |f n g| ≤ A * |g| := by
      calc
        _ ≤ |calVpart β (B n) (plSpec α (c n) (N n)) (i n) 0 M g| +
            |g / Real.sqrt (sPow β 2)| := abs_sub _ _
        _ ≤ C * |g| + |g / Real.sqrt (sPow β 2)| := add_le_add (hn g) le_rfl
        _ = A * |g| := by
          rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
          dsimp [A]
          ring
    have hs := (sq_le_sq₀ (abs_nonneg (f n g)) (mul_nonneg hA (abs_nonneg g))).2 hfg
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f n g))]
    simpa only [sq_abs, mul_pow] using hs
  have hmajor : Integrable (fun g : ℝ => A ^ 2 * g ^ 2) (gaussianReal 0 1) :=
    (Muon.Foundations.gaussian_integrable_pow 2).const_mul _
  have hsq : ∀ᶠ n in atTop, Integrable (fun g => f n g ^ 2) (gaussianReal 0 1) := by
    filter_upwards [hfm, hbound] with n hmn hbn
    exact hmajor.mono' (hmn.pow 2) (Eventually.of_forall hbn)
  refine ⟨hsq, ?_⟩
  have hlim : ∀ᵐ g ∂(gaussianReal 0 1),
      Tendsto (fun n => f n g ^ 2) atTop (𝓝 (0 : ℝ)) := by
    apply Eventually.of_forall
    intro g
    simpa only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using ((ht g).sub_const
      (g / Real.sqrt (sPow β 2))).pow 2
  have hint := tendsto_integral_filter_of_dominated_convergence
    (fun g => A ^ 2 * g ^ 2) (hfm.mono fun n hn => hn.pow 2)
    (hbound.mono fun n hn => Eventually.of_forall hn) hmajor hlim
  simp only [integral_zero] at hint
  simpa [l2Norm, f, Pi.pow_apply] using hint.sqrt

end Muon.PowerLaw

end

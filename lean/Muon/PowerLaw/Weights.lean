import Muon.Foundations.Conventions
import Muon.DetEquiv.Scalar

/-!
# Appendix G: EMA weight functions and averages (work package L-G.1)

Snapshot `cr-2026-10-23`. Source: `sections/06-power-law/section.tex`, subsection
"The weight functions" (l.213–245), "Averaging in the participation coordinate" (l.304–320),
"The two-time row response" (l.444–464) and the participation kernel (l.558–571), with the
card §2 representation.

Representation choices:

* The scalar functions `J`, `Fw`, `Lw`, `rW` are Appendix B's (`Muon.DetEquiv`, frozen), applied to
  the EMA weights `Muon.emaW β` (`w_j = (1-β) β^j`). The power sums `\sw p` are `Muon.sPow β p`.
* `Qm β m` is `Q_m = r_β^{-1}(m)`, defined by `Function.invFunOn` on `Ioi 0`. The inverse is
  meaningful for `m > 0` (for `m` in the range of `r_β`); outside that range its value is junk,
  as the source's `Q_m` is only used there.
* `Efun β m` is `E(m) = Q_m r_β'(Q_m)` with `r_β'` the Fréchet derivative `deriv`, which
  Appendix B's `lem_app_de_scalar_iii` identifies with the displayed series for `q > 0`.
* Lags `ℓ ∈ ℤ` for `𝖣_ℓ, 𝖬_ℓ` follow the source's negative-lag convention by cases.
  The arguments `q₁, q₂` of `𝖣_ℓ, 𝖬_ℓ` are the coordinates `q_k = Q_{m_k}` of
  `eqn:app-pl-participation-kernel` (l.558–559), so the source's evaluation at `(m₁,m₂)` is
  `DLag β (Qm β m₁) (Qm β m₂) ℓ`.
* Every series `∑_{j≥0} E[·]` is `∑' j, ∫ g, · ∂(gaussianReal 0 1)`. Finiteness of the sums is
  not an assumption of the definitions; it is a consequence that the proofs must supply.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Asymptotics Muon.DetEquiv

noncomputable section

namespace Muon.PowerLaw

/-! ## Resolved-age count -/

/-- Number of ages `j ≥ 0` whose EMA weight is resolved at scale `Q`:
`n(Q) = #{j ≥ 0 : w_j² Q ≥ 1}`, with `w_j = (1-β) β^j` (`section.tex` l.217–221, "The weight
functions"). The set is finite for `0 ≤ β < 1`, so `Set.ncard` is its cardinality. -/
def nRes (β Q : ℝ) : ℕ :=
  Set.ncard {j : ℕ | 1 ≤ emaW β j ^ 2 * Q}

/-! ## Expectation sums over EMA ages

Each sum is `∑_{j≥0} E[·]` with `g ∼ N(0,1)`, written as `∑' j, ∫ g, · ∂(gaussianReal 0 1)`.
The source's `\EE` is this Gaussian expectation (`section.tex` l.47–53, `g ∼ N(0,1)`). -/

/-- Lag-`ℓ` coefficient `b_ℓ(q,q')` of `eqn:app-pl-UV` (`section.tex` l.450–458), for a
lag `ℓ ≥ 0`:
`b_ℓ = ∑_{j≥0} E[β^ℓ w_j² g² / ((1+q w_j² g²)(1+β^{2ℓ} q' w_j² g²))]`. -/
def bLag (β q q' : ℝ) (ℓ : ℕ) : ℝ :=
  ∑' j : ℕ, ∫ g : ℝ,
    β ^ ℓ * emaW β j ^ 2 * g ^ 2 /
      ((1 + q * emaW β j ^ 2 * g ^ 2) * (1 + β ^ (2 * ℓ) * q' * emaW β j ^ 2 * g ^ 2))
    ∂(gaussianReal 0 1)

/-- Lag-`ℓ` coefficient `e_ℓ(q,q')` of `eqn:app-pl-UV` (`section.tex` l.450–458), for a
lag `ℓ ≥ 0`:
`e_ℓ = ∑_{j≥0} E[β^{2ℓ} w_j⁴ g⁴ / ((1+q w_j² g²)(1+β^{2ℓ} q' w_j² g²))]`. -/
def eLag (β q q' : ℝ) (ℓ : ℕ) : ℝ :=
  ∑' j : ℕ, ∫ g : ℝ,
    β ^ (2 * ℓ) * emaW β j ^ 4 * g ^ 4 /
      ((1 + q * emaW β j ^ 2 * g ^ 2) * (1 + β ^ (2 * ℓ) * q' * emaW β j ^ 2 * g ^ 2))
    ∂(gaussianReal 0 1)

/-- `𝖣_ℓ(q₁,q₂)` of `eqn:app-pl-participation-kernel` (`section.tex` l.559–569), for a lag
`ℓ ≥ 0`:
`𝖣_ℓ = ∑_{a≥0} E[β^ℓ √(q₁q₂) w_a² g² / ((1+q₁ w_a² g²)(1+β^{2ℓ} q₂ w_a² g²))]`. -/
def DLagNat (β q₁ q₂ : ℝ) (ℓ : ℕ) : ℝ :=
  ∑' a : ℕ, ∫ g : ℝ,
    β ^ ℓ * Real.sqrt (q₁ * q₂) * emaW β a ^ 2 * g ^ 2 /
      ((1 + q₁ * emaW β a ^ 2 * g ^ 2) * (1 + β ^ (2 * ℓ) * q₂ * emaW β a ^ 2 * g ^ 2))
    ∂(gaussianReal 0 1)

/-- `𝖬_ℓ(q₁,q₂)` of `eqn:app-pl-participation-kernel` (`section.tex` l.559–569), for a lag
`ℓ ≥ 0`:
`𝖬_ℓ = ∑_{a≥0} E[β^{2ℓ} q₁ q₂ w_a⁴ g⁴ / ((1+q₁ w_a² g²)(1+β^{2ℓ} q₂ w_a² g²))]`. -/
def MLagNat (β q₁ q₂ : ℝ) (ℓ : ℕ) : ℝ :=
  ∑' a : ℕ, ∫ g : ℝ,
    β ^ (2 * ℓ) * q₁ * q₂ * emaW β a ^ 4 * g ^ 4 /
      ((1 + q₁ * emaW β a ^ 2 * g ^ 2) * (1 + β ^ (2 * ℓ) * q₂ * emaW β a ^ 2 * g ^ 2))
    ∂(gaussianReal 0 1)

/-- `𝖣_ℓ` on all integer lags. For a negative lag `-ℓ` the function is that of lag `ℓ` at
`(q₂,q₁)` (`section.tex` l.568–569: "for a negative lag `-ℓ` the three functions `𝖣, 𝖬, Δ^N`
are those of the lag `ℓ` at `(m₂,m₁)`"). -/
def DLag (β q₁ q₂ : ℝ) (ℓ : ℤ) : ℝ :=
  if 0 ≤ ℓ then DLagNat β q₁ q₂ ℓ.toNat else DLagNat β q₂ q₁ (-ℓ).toNat

/-- `𝖬_ℓ` on all integer lags, with the same negative-lag convention as `DLag`
(`section.tex` l.568–569). -/
def MLag (β q₁ q₂ : ℝ) (ℓ : ℤ) : ℝ :=
  if 0 ≤ ℓ then MLagNat β q₁ q₂ ℓ.toNat else MLagNat β q₂ q₁ (-ℓ).toNat

/-! ## Scalar functions at the EMA weights

`Fw (emaW β)`, `Lw (emaW β)`, `rW (emaW β)` are Appendix B's `F_w`, `L_w`, `r_w`
(`Muon.DetEquiv`, frozen) at the EMA weights. -/

/-- `Q_m = r_β^{-1}(m)` (`eqn:app-pl-Q`, `section.tex` l.95–97), for `m > 0`. Total extension by
`Function.invFunOn` on `Ioi 0`; the value is meaningful where `m` lies in the range of `r_β`. -/
def Qm (β m : ℝ) : ℝ :=
  Function.invFunOn (rW (emaW β)) (Ioi 0) m

/-- `E(m) = Q_m r_β'(Q_m)` (`eqn:app-pl-Q`, `section.tex` l.95–97), for `m > 0`. -/
def Efun (β m : ℝ) : ℝ :=
  Qm β m * deriv (rW (emaW β)) (Qm β m)

/-- `𝒜(m) = √(Q_m) L_β(Q_m) / E(m)`, for `m > 0` (`lem:app-pl-average`, `section.tex` l.310). -/
def Aav (β m : ℝ) : ℝ :=
  Real.sqrt (Qm β m) * Lw (emaW β) (Qm β m) / Efun β m

/-! ## Statements -/

/-! ### Private helpers for `lem_app_pl_weights_i_F`, `lem_app_pl_weights_i_L` (fully proved) -/

private lemma summable_emaW_pow_P1 {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {p : ℕ} (hp : 1 ≤ p) :
    Summable (fun j : ℕ => emaW β j ^ p) := by
  have hr : β ^ p < 1 := pow_lt_one₀ hβ0 hβ1 (by omega)
  have key : (fun j : ℕ => emaW β j ^ p) = fun j => (1 - β) ^ p * (β ^ p) ^ j := by
    funext j
    unfold emaW
    rw [mul_pow, pow_right_comm β j p]
  rw [key]
  exact (summable_geometric_of_lt_one (pow_nonneg hβ0 p) hr).mul_left _

/-- `J(x) = 1 - 3x + x² I(x)` with `0 ≤ I(x) ≤ 15` for `x ≥ 0`, from the Gaussian moments
`E g² = 1`, `E g⁴ = 3`, `E g⁶ = 15`. -/
private lemma J_expand_P1 {x : ℝ} (hx : 0 ≤ x) :
    ∃ I : ℝ, J x = 1 - 3 * x + x ^ 2 * I ∧ 0 ≤ I ∧ I ≤ 15 := by
  have hpos : ∀ g : ℝ, 0 < 1 + x * g ^ 2 := fun g => by
    have := mul_nonneg hx (sq_nonneg g)
    linarith
  have hi2 := Muon.Foundations.gaussian_integrable_pow 2
  have hi4 := Muon.Foundations.gaussian_integrable_pow 4
  have hi6 := Muon.Foundations.gaussian_integrable_pow 6
  have hI6 : Integrable (fun g : ℝ => g ^ 6 / (1 + x * g ^ 2)) (gaussianReal 0 1) := by
    refine Integrable.mono' hi6 ?_ ?_
    · exact (Continuous.div (by fun_prop) (by fun_prop) (fun g => (hpos g).ne')).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun g => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by positivity) (hpos g).le)]
      exact div_le_self (by positivity) (le_add_of_nonneg_right (mul_nonneg hx (sq_nonneg g)))
  have key : ∀ g : ℝ, g ^ 2 / (1 + x * g ^ 2)
      = g ^ 2 - x * g ^ 4 + x ^ 2 * (g ^ 6 / (1 + x * g ^ 2)) := by
    intro g
    have h := (hpos g).ne'
    field_simp <;> ring
  have hJ : J x = ∫ g, (g ^ 2 - x * g ^ 4 + x ^ 2 * (g ^ 6 / (1 + x * g ^ 2)))
      ∂(gaussianReal 0 1) := by
    unfold J
    congr 1
    funext g
    exact key g
  have hint : ∫ g, (g ^ 2 - x * g ^ 4 + x ^ 2 * (g ^ 6 / (1 + x * g ^ 2)))
      ∂(gaussianReal 0 1)
      = (∫ g, g ^ 2 ∂(gaussianReal 0 1)) - x * (∫ g, g ^ 4 ∂(gaussianReal 0 1))
        + x ^ 2 * ∫ g, g ^ 6 / (1 + x * g ^ 2) ∂(gaussianReal 0 1) := by
    have hi4x : Integrable (fun g : ℝ => x * g ^ 4) (gaussianReal 0 1) := hi4.const_mul x
    have hA2 : Integrable (fun g : ℝ => g ^ 2 - x * g ^ 4) (gaussianReal 0 1) := hi2.sub hi4x
    have hB2 : Integrable (fun g : ℝ => x ^ 2 * (g ^ 6 / (1 + x * g ^ 2))) (gaussianReal 0 1) :=
      hI6.const_mul (x ^ 2)
    rw [integral_add hA2 hB2, integral_sub hi2 hi4x, integral_const_mul, integral_const_mul]
  have hJ2 : J x = 1 - 3 * x + x ^ 2 * ∫ g, g ^ 6 / (1 + x * g ^ 2) ∂(gaussianReal 0 1) := by
    rw [hJ, hint, Muon.Foundations.gaussian_moment_two, Muon.Foundations.gaussian_moment_four]
    ring
  refine ⟨∫ g, g ^ 6 / (1 + x * g ^ 2) ∂(gaussianReal 0 1), hJ2,
    integral_nonneg (fun g => div_nonneg (by positivity) (hpos g).le), ?_⟩
  calc ∫ g, g ^ 6 / (1 + x * g ^ 2) ∂(gaussianReal 0 1)
      ≤ ∫ g, g ^ 6 ∂(gaussianReal 0 1) :=
        integral_mono hI6 hi6 (fun g => div_le_self (by positivity)
          (le_add_of_nonneg_right (mul_nonneg hx (sq_nonneg g))))
    _ = 15 := Muon.Foundations.gaussian_moment_six

/-- `lem:app-pl-weights`(i), first conjunct: the expansion of `F_β`, snapshot `cr-2026-10-23`.
LaTeX (`sections/06-power-law/section.tex` l.223–244):
\begin{lemma}[Weight functions]\label{lem:app-pl-weights}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item For $q\ge0$,
\[
\begin{gathered}
\Fw(q)=\sw2-3\sw4q+R_F(q),\quad 0\le R_F\le15\sw6q^2,\\
\Lw(q)=1-3\sw3q+R_L(q),\quad 0\le R_L\le15\sw5q^2 .
\end{gathered}
\]
Consequently $r_\bmom(q)=\sw2q+O(q^2)$, and $Q_m\sim m/\sw2$ and $E(m)\sim m$ as $m\downarrow0$.
\item For $q>0$, $\abs{q\Fw'(q)}\le\Fw(q)$ and $\abs{q\Lw'(q)}\le\Lw(q)$. For $m>0$, $E(m)\le m$.
\item There are $0<c_\bmom\le C_\bmom<\infty$ such that, for $Q\ge1$,
\[
\abs{r_\bmom(Q)-n(Q)}\le C_\bmom,\qquad
c_\bmom\le\sqrt Q\,\Lw(Q)\le C_\bmom,\qquad
c_\bmom\le Q\,r_\bmom'(Q)\le C_\bmom .
\]
Consequently $E(m)\asymp\min(m,1)$ for all $m>0$, and
$\abs{\log Q_m-2\abs{\log\bmom}\,m}\le C_\bmom$ for $m\ge1$.
\end{enumerate}
\end{lemma} -/
theorem lem_app_pl_weights_i_F {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∀ q : ℝ, 0 ≤ q → ∃ RF : ℝ,
      Fw (emaW β) q = sPow β 2 - 3 * sPow β 4 * q + RF ∧
      0 ≤ RF ∧ RF ≤ 15 * sPow β 6 * q ^ 2 := by
  intro q hq
  have hs : ∀ p : ℕ, 1 ≤ p → Summable (fun j : ℕ => emaW β j ^ p) :=
    fun p hp => summable_emaW_pow_P1 hβ0 hβ1 hp
  have hemaW : ∀ j : ℕ, 0 ≤ emaW β j := fun j => by
    unfold emaW
    exact mul_nonneg (by linarith) (pow_nonneg hβ0 j)
  have hJ : ∀ j : ℕ, ∃ I : ℝ,
      J (emaW β j ^ 2 * q) = 1 - 3 * (emaW β j ^ 2 * q) + (emaW β j ^ 2 * q) ^ 2 * I ∧
        0 ≤ I ∧ I ≤ 15 :=
    fun j => J_expand_P1 (mul_nonneg (sq_nonneg _) hq)
  choose Ic hIeq hI0 hI15 using hJ
  have hnn : ∀ j : ℕ, 0 ≤ emaW β j ^ 6 * q ^ 2 * Ic j := fun j =>
    mul_nonneg (mul_nonneg (pow_nonneg (hemaW j) 6) (sq_nonneg q)) (hI0 j)
  have hsum6 : Summable (fun j : ℕ => emaW β j ^ 6 * q ^ 2 * Ic j) := by
    refine Summable.of_nonneg_of_le hnn (fun j => ?_)
      ((hs 6 (by norm_num)).mul_left (15 * q ^ 2))
    have h1 := hI15 j
    have h2 : 0 ≤ emaW β j ^ 6 * q ^ 2 := mul_nonneg (pow_nonneg (hemaW j) 6) (sq_nonneg q)
    nlinarith [mul_nonneg h2 (sub_nonneg.2 h1)]
  have hA : Summable (fun j : ℕ => emaW β j ^ 2) := hs 2 (by norm_num)
  have hB : Summable (fun j : ℕ => 3 * q * emaW β j ^ 4) :=
    (hs 4 (by norm_num)).mul_left (3 * q)
  have hEq : Fw (emaW β) q
      = ∑' j : ℕ, (emaW β j ^ 2 - 3 * q * emaW β j ^ 4 + emaW β j ^ 6 * q ^ 2 * Ic j) := by
    unfold Fw
    refine tsum_congr (fun j => ?_)
    rw [hIeq j]
    ring
  have hBs : ∑' j : ℕ, 3 * q * emaW β j ^ 4 = 3 * q * sPow β 4 := tsum_mul_left
  have h15 : ∑' j : ℕ, 15 * q ^ 2 * emaW β j ^ 6 = 15 * q ^ 2 * sPow β 6 := tsum_mul_left
  have hpt : ∀ j : ℕ, emaW β j ^ 6 * q ^ 2 * Ic j ≤ 15 * q ^ 2 * emaW β j ^ 6 := fun j => by
    have h1 := hI15 j
    have h2 : 0 ≤ emaW β j ^ 6 * q ^ 2 := mul_nonneg (pow_nonneg (hemaW j) 6) (sq_nonneg q)
    nlinarith [mul_nonneg h2 (sub_nonneg.2 h1)]
  refine ⟨∑' j : ℕ, emaW β j ^ 6 * q ^ 2 * Ic j, ?_, tsum_nonneg hnn, ?_⟩
  · rw [hEq, Summable.tsum_add (hA.sub hB) hsum6, Summable.tsum_sub hA hB, hBs]
    unfold sPow
    ring
  · have hb := Summable.tsum_le_tsum hpt hsum6 ((hs 6 (by norm_num)).mul_left (15 * q ^ 2))
    rw [h15] at hb
    calc ∑' j : ℕ, emaW β j ^ 6 * q ^ 2 * Ic j ≤ 15 * q ^ 2 * sPow β 6 := hb
      _ = 15 * sPow β 6 * q ^ 2 := by ring

/-- `lem:app-pl-weights`(i), second conjunct: the expansion of `L_β`, snapshot `cr-2026-10-23`.
LaTeX (`sections/06-power-law/section.tex` l.223–244):
\begin{lemma}[Weight functions]\label{lem:app-pl-weights}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item For $q\ge0$,
\[
\begin{gathered}
\Fw(q)=\sw2-3\sw4q+R_F(q),\quad 0\le R_F\le15\sw6q^2,\\
\Lw(q)=1-3\sw3q+R_L(q),\quad 0\le R_L\le15\sw5q^2 .
\end{gathered}
\]
Consequently $r_\bmom(q)=\sw2q+O(q^2)$, and $Q_m\sim m/\sw2$ and $E(m)\sim m$ as $m\downarrow0$.
\item For $q>0$, $\abs{q\Fw'(q)}\le\Fw(q)$ and $\abs{q\Lw'(q)}\le\Lw(q)$. For $m>0$, $E(m)\le m$.
\item There are $0<c_\bmom\le C_\bmom<\infty$ such that, for $Q\ge1$,
\[
\abs{r_\bmom(Q)-n(Q)}\le C_\bmom,\qquad
c_\bmom\le\sqrt Q\,\Lw(Q)\le C_\bmom,\qquad
c_\bmom\le Q\,r_\bmom'(Q)\le C_\bmom .
\]
Consequently $E(m)\asymp\min(m,1)$ for all $m>0$, and
$\abs{\log Q_m-2\abs{\log\bmom}\,m}\le C_\bmom$ for $m\ge1$.
\end{enumerate}
\end{lemma} -/
theorem lem_app_pl_weights_i_L {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∀ q : ℝ, 0 ≤ q → ∃ RL : ℝ,
      Lw (emaW β) q = 1 - 3 * sPow β 3 * q + RL ∧
      0 ≤ RL ∧ RL ≤ 15 * sPow β 5 * q ^ 2 := by
  intro q hq
  have hs : ∀ p : ℕ, 1 ≤ p → Summable (fun j : ℕ => emaW β j ^ p) :=
    fun p hp => summable_emaW_pow_P1 hβ0 hβ1 hp
  have hemaW : ∀ j : ℕ, 0 ≤ emaW β j := fun j => by
    unfold emaW
    exact mul_nonneg (by linarith) (pow_nonneg hβ0 j)
  have hJ : ∀ j : ℕ, ∃ I : ℝ,
      J (emaW β j ^ 2 * q) = 1 - 3 * (emaW β j ^ 2 * q) + (emaW β j ^ 2 * q) ^ 2 * I ∧
        0 ≤ I ∧ I ≤ 15 :=
    fun j => J_expand_P1 (mul_nonneg (sq_nonneg _) hq)
  choose Ic hIeq hI0 hI15 using hJ
  have hnn : ∀ j : ℕ, 0 ≤ emaW β j ^ 5 * q ^ 2 * Ic j := fun j =>
    mul_nonneg (mul_nonneg (pow_nonneg (hemaW j) 5) (sq_nonneg q)) (hI0 j)
  have hsum5 : Summable (fun j : ℕ => emaW β j ^ 5 * q ^ 2 * Ic j) := by
    refine Summable.of_nonneg_of_le hnn (fun j => ?_)
      ((hs 5 (by norm_num)).mul_left (15 * q ^ 2))
    have h1 := hI15 j
    have h2 : 0 ≤ emaW β j ^ 5 * q ^ 2 := mul_nonneg (pow_nonneg (hemaW j) 5) (sq_nonneg q)
    nlinarith [mul_nonneg h2 (sub_nonneg.2 h1)]
  have hA1 : Summable (fun j : ℕ => emaW β j) := by
    simpa only [pow_one] using hs 1 le_rfl
  have hB3 : Summable (fun j : ℕ => 3 * q * emaW β j ^ 3) :=
    (hs 3 (by norm_num)).mul_left (3 * q)
  have hEq : Lw (emaW β) q
      = ∑' j : ℕ, (emaW β j - 3 * q * emaW β j ^ 3 + emaW β j ^ 5 * q ^ 2 * Ic j) := by
    unfold Lw
    refine tsum_congr (fun j => ?_)
    rw [hIeq j]
    ring
  have hBs : ∑' j : ℕ, 3 * q * emaW β j ^ 3 = 3 * q * sPow β 3 := tsum_mul_left
  have h15 : ∑' j : ℕ, 15 * q ^ 2 * emaW β j ^ 5 = 15 * q ^ 2 * sPow β 5 := tsum_mul_left
  have hpt : ∀ j : ℕ, emaW β j ^ 5 * q ^ 2 * Ic j ≤ 15 * q ^ 2 * emaW β j ^ 5 := fun j => by
    have h1 := hI15 j
    have h2 : 0 ≤ emaW β j ^ 5 * q ^ 2 := mul_nonneg (pow_nonneg (hemaW j) 5) (sq_nonneg q)
    nlinarith [mul_nonneg h2 (sub_nonneg.2 h1)]
  refine ⟨∑' j : ℕ, emaW β j ^ 5 * q ^ 2 * Ic j, ?_, tsum_nonneg hnn, ?_⟩
  · rw [hEq, Summable.tsum_add (hA1.sub hB3) hsum5, Summable.tsum_sub hA1 hB3, hBs,
      tsum_emaW hβ0 hβ1]
    unfold sPow
    ring
  · have hb := Summable.tsum_le_tsum hpt hsum5 ((hs 5 (by norm_num)).mul_left (15 * q ^ 2))
    rw [h15] at hb
    calc ∑' j : ℕ, emaW β j ^ 5 * q ^ 2 * Ic j ≤ 15 * q ^ 2 * sPow β 5 := hb
      _ = 15 * sPow β 5 * q ^ 2 := by ring

/-- `lem:app-pl-weights`(i), consequence `r_β(q) = \sw2 q + O(q²)` as `q ↓ 0`, snapshot
`cr-2026-10-23`. LaTeX (`sections/06-power-law/section.tex` l.223–244):
\begin{lemma}[Weight functions]\label{lem:app-pl-weights}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item For $q\ge0$,
\[
\begin{gathered}
\Fw(q)=\sw2-3\sw4q+R_F(q),\quad 0\le R_F\le15\sw6q^2,\\
\Lw(q)=1-3\sw3q+R_L(q),\quad 0\le R_L\le15\sw5q^2 .
\end{gathered}
\]
Consequently $r_\bmom(q)=\sw2q+O(q^2)$, and $Q_m\sim m/\sw2$ and $E(m)\sim m$ as $m\downarrow0$.
\item For $q>0$, $\abs{q\Fw'(q)}\le\Fw(q)$ and $\abs{q\Lw'(q)}\le\Lw(q)$. For $m>0$, $E(m)\le m$.
\item There are $0<c_\bmom\le C_\bmom<\infty$ such that, for $Q\ge1$,
\[
\abs{r_\bmom(Q)-n(Q)}\le C_\bmom,\qquad
c_\bmom\le\sqrt Q\,\Lw(Q)\le C_\bmom,\qquad
c_\bmom\le Q\,r_\bmom'(Q)\le C_\bmom .
\]
Consequently $E(m)\asymp\min(m,1)$ for all $m>0$, and
$\abs{\log Q_m-2\abs{\log\bmom}\,m}\le C_\bmom$ for $m\ge1$.
\end{enumerate}
\end{lemma} -/
theorem lem_app_pl_weights_i_r {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    IsBigO (𝓝[>] (0 : ℝ)) (fun q => rW (emaW β) q - sPow β 2 * q) (fun q => q ^ 2) := by
  have hnn : ∀ j : ℕ, 0 ≤ emaW β j := fun j => by
    unfold emaW
    exact mul_nonneg (by linarith) (pow_nonneg hβ0 j)
  have hs4 : 0 ≤ sPow β 4 := tsum_nonneg fun j => pow_nonneg (hnn j) 4
  have hs6 : 0 ≤ sPow β 6 := tsum_nonneg fun j => pow_nonneg (hnn j) 6
  refine IsBigO.of_bound (3 * sPow β 4 + 15 * sPow β 6) ?_
  have hq1 : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) := nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  filter_upwards [hq1, self_mem_nhdsWithin] with q hq1' hqpos
  show ‖rW (emaW β) q - sPow β 2 * q‖ ≤ (3 * sPow β 4 + 15 * sPow β 6) * ‖q ^ 2‖
  have hq0 : (0:ℝ) < q := hqpos
  have hq1'' : q < 1 := hq1'
  obtain ⟨RF, hRF, hRF0, hRF15⟩ := lem_app_pl_weights_i_F hβ0 hβ1 q hq0.le
  have hrw : rW (emaW β) q - sPow β 2 * q = q * (-(3 * sPow β 4 * q) + RF) := by
    unfold rW
    rw [hRF]
    ring
  have hA := mul_le_mul_of_nonneg_left hRF15 hq0.le
  have hB := mul_nonneg (mul_nonneg hs6 (sq_nonneg q)) (sub_nonneg.2 hq1''.le)
  have hC := mul_nonneg hs4 (sq_nonneg q)
  have hD := mul_nonneg hq0.le hRF0
  have hE := mul_nonneg hs6 (sq_nonneg q)
  rw [hrw, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg q), abs_le]
  constructor <;> nlinarith

/-! ### Private helpers for `lem_app_pl_weights_i_Q`, `lem_app_pl_weights_i_E` (fully proved) -/

private lemma P2_weightSeq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) : WeightSeq (emaW β) :=
  ⟨fun j => by unfold emaW; exact mul_nonneg (by linarith) (pow_nonneg hβ0 j),
    by simpa only [pow_one] using summable_emaW_pow_P1 hβ0 hβ1 (p := 1) le_rfl,
    ⟨0, by unfold emaW; rw [pow_zero, mul_one]; exact (by linarith : (0:ℝ) < 1 - β).ne'⟩⟩

private lemma P2_s2_pos {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) : 0 < sPow β 2 := by
  unfold sPow
  refine (summable_emaW_pow_P1 hβ0 hβ1 (p := 2) (by norm_num)).tsum_pos (fun j => sq_nonneg _) 0 ?_
  unfold emaW
  rw [pow_zero, mul_one]
  exact pow_pos (by linarith) 2

private lemma P2_tendsto_sub (a C : ℝ) : Tendsto (fun q : ℝ => a - C * q) (𝓝[>] (0:ℝ)) (𝓝 a) := by
  have hc : Continuous (fun q : ℝ => a - C * q) := by fun_prop
  have h := hc.tendsto 0
  simp only [mul_zero, sub_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

private lemma P2_tendsto_add (a C : ℝ) : Tendsto (fun q : ℝ => a + C * q) (𝓝[>] (0:ℝ)) (𝓝 a) := by
  have hc : Continuous (fun q : ℝ => a + C * q) := by fun_prop
  have h := hc.tendsto 0
  simp only [mul_zero, add_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- For `x ≥ 0`: `0 ≤ E[g²/(1+xg²)²]`, `1 - 6x ≤ E[g²/(1+xg²)²] ≤ 1`. -/
private lemma P2_int_bounds {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ ∫ g : ℝ, g ^ 2 / (1 + x * g ^ 2) ^ 2 ∂(gaussianReal 0 1) ∧
    1 - 6 * x ≤ ∫ g : ℝ, g ^ 2 / (1 + x * g ^ 2) ^ 2 ∂(gaussianReal 0 1) ∧
    ∫ g : ℝ, g ^ 2 / (1 + x * g ^ 2) ^ 2 ∂(gaussianReal 0 1) ≤ 1 := by
  have hpos : ∀ g : ℝ, 0 < 1 + x * g ^ 2 := fun g => by
    have := mul_nonneg hx (sq_nonneg g)
    linarith
  have hi2 := Muon.Foundations.gaussian_integrable_pow 2
  have hi4 := Muon.Foundations.gaussian_integrable_pow 4
  have hc : Continuous fun g : ℝ => g ^ 2 / (1 + x * g ^ 2) ^ 2 :=
    Continuous.div (by fun_prop) (by fun_prop) (fun g => pow_ne_zero 2 (hpos g).ne')
  have h1 : ∀ g : ℝ, 1 ≤ (1 + x * g ^ 2) ^ 2 := fun g =>
    one_le_pow₀ (by nlinarith [mul_nonneg hx (sq_nonneg g)])
  have hint : Integrable (fun g : ℝ => g ^ 2 / (1 + x * g ^ 2) ^ 2) (gaussianReal 0 1) := by
    refine Integrable.mono' hi2 hc.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg g) (pow_nonneg (hpos g).le 2))]
    exact div_le_self (sq_nonneg g) (h1 g)
  have hlo_int : Integrable (fun g : ℝ => g ^ 2 - 2 * x * g ^ 4) (gaussianReal 0 1) :=
    hi2.sub (hi4.const_mul (2 * x))
  have hpt : ∀ g : ℝ, g ^ 2 - 2 * x * g ^ 4 ≤ g ^ 2 / (1 + x * g ^ 2) ^ 2 := by
    intro g
    rw [le_div_iff₀ (pow_pos (hpos g) 2)]
    have hy : 0 ≤ x * g ^ 2 := mul_nonneg hx (sq_nonneg g)
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg g) (sq_nonneg (x * g ^ 2)))
      (by linarith : (0:ℝ) ≤ 3 + 2 * (x * g ^ 2))]
  have hlow : ∫ g : ℝ, (g ^ 2 - 2 * x * g ^ 4) ∂(gaussianReal 0 1) = 1 - 6 * x := by
    rw [integral_sub hi2 (hi4.const_mul (2 * x)), integral_const_mul,
      Muon.Foundations.gaussian_moment_two, Muon.Foundations.gaussian_moment_four]
    ring
  refine ⟨integral_nonneg fun g => div_nonneg (sq_nonneg g) (pow_nonneg (hpos g).le 2), ?_, ?_⟩
  · rw [← hlow]
    exact integral_mono hlo_int hint hpt
  · calc ∫ g : ℝ, g ^ 2 / (1 + x * g ^ 2) ^ 2 ∂(gaussianReal 0 1)
        ≤ ∫ g : ℝ, g ^ 2 ∂(gaussianReal 0 1) :=
          integral_mono hint hi2 (fun g => div_le_self (sq_nonneg g) (h1 g))
      _ = 1 := Muon.Foundations.gaussian_moment_two

/-- Termwise-summed derivative bounds: `s₂ - 6 s₄ q ≤ ∑_j w_j² E[g²/(1+w_j² q g²)²] ≤ s₂`. -/
private lemma P2_deriv_bounds {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    sPow β 2 - 6 * sPow β 4 * q ≤
      ∑' j : ℕ, emaW β j ^ 2 * ∫ g : ℝ, g ^ 2 / (1 + emaW β j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1) ∧
    ∑' j : ℕ, emaW β j ^ 2 * ∫ g : ℝ, g ^ 2 / (1 + emaW β j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1)
      ≤ sPow β 2 := by
  have hs : ∀ p : ℕ, 1 ≤ p → Summable (fun j : ℕ => emaW β j ^ p) :=
    fun p hp => summable_emaW_pow_P1 hβ0 hβ1 hp
  have hT_nn : ∀ j : ℕ, 0 ≤ emaW β j ^ 2 * ∫ g : ℝ, g ^ 2 / (1 + emaW β j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1) :=
    fun j => mul_nonneg (sq_nonneg _) (P2_int_bounds (x := emaW β j ^ 2 * q) (mul_nonneg (sq_nonneg _) hq)).1
  have hT_le : ∀ j : ℕ, emaW β j ^ 2 * ∫ g : ℝ, g ^ 2 / (1 + emaW β j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1) ≤ emaW β j ^ 2 :=
    fun j => mul_le_of_le_one_right (sq_nonneg _)
      (P2_int_bounds (x := emaW β j ^ 2 * q) (mul_nonneg (sq_nonneg _) hq)).2.2
  have hTs := Summable.of_nonneg_of_le hT_nn hT_le (hs 2 (by norm_num))
  constructor
  · have hL : Summable (fun j : ℕ => emaW β j ^ 2 - 6 * q * emaW β j ^ 4) :=
      (hs 2 (by norm_num)).sub ((hs 4 (by norm_num)).mul_left (6 * q))
    have hLsum : ∑' j : ℕ, (emaW β j ^ 2 - 6 * q * emaW β j ^ 4) = sPow β 2 - 6 * sPow β 4 * q := by
      rw [Summable.tsum_sub (hs 2 (by norm_num)) ((hs 4 (by norm_num)).mul_left (6 * q)), tsum_mul_left]
      unfold sPow
      ring
    rw [← hLsum]
    refine Summable.tsum_le_tsum (fun j => ?_) hL hTs
    show emaW β j ^ 2 - 6 * q * emaW β j ^ 4 ≤ _
    have h1 := (P2_int_bounds (x := emaW β j ^ 2 * q) (mul_nonneg (sq_nonneg _) hq)).2.1
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (emaW β j))
    nlinarith [h2]
  · exact Summable.tsum_le_tsum hT_le hTs (hs 2 (by norm_num))

/-- Derivative of `r_β` along the sum: `r_β'(q) → s₂` as `q ↓ 0`. -/
private lemma P2_deriv_tendsto {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Tendsto (fun q : ℝ => deriv (rW (emaW β)) q) (𝓝[>] (0:ℝ)) (𝓝 (sPow β 2)) := by
  have hlo := P2_tendsto_sub (sPow β 2) (6 * sPow β 4)
  have hhi : Tendsto (fun _ : ℝ => sPow β 2) (𝓝[>] (0:ℝ)) (𝓝 (sPow β 2)) := tendsto_const_nhds
  have hpos : ∀ᶠ q in 𝓝[>] (0:ℝ), 0 < q := self_mem_nhdsWithin
  have hD : ∀ᶠ q in 𝓝[>] (0:ℝ), deriv (rW (emaW β)) q = ∑' j : ℕ,
      emaW β j ^ 2 * ∫ g : ℝ, g ^ 2 / (1 + emaW β j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1) := by
    filter_upwards [hpos] with q hq
    exact ((lem_app_de_scalar_iii (P2_weightSeq hβ0 hβ1)).2.2.2.1 q hq).deriv
  have hDt : Tendsto (fun q : ℝ => ∑' j : ℕ,
      emaW β j ^ 2 * ∫ g : ℝ, g ^ 2 / (1 + emaW β j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1))
      (𝓝[>] (0:ℝ)) (𝓝 (sPow β 2)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
      (hpos.mono fun q hq => (P2_deriv_bounds hβ0 hβ1 hq.le).1)
      (hpos.mono fun q hq => (P2_deriv_bounds hβ0 hβ1 hq.le).2)
  exact hDt.congr' (hD.mono fun q h => h.symm)

/-- `r_β` is continuous on `[0,∞)`, strictly increasing, and `r_β` is onto `(0, r_β(q₁))`
near `0`: the range statement for `Q_m`. -/
private lemma P2_range {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q1 : ℝ} (hq1 : 0 < q1) :
    ∀ᶠ m in 𝓝[>] (0:ℝ), Qm β m ∈ Ioo 0 q1 ∧ rW (emaW β) (Qm β m) = m := by
  have hF := (lem_app_de_scalar_ii (P2_weightSeq hβ0 hβ1)).2.2.1
  have hcont : ContinuousOn (rW (emaW β)) (Ici 0) := continuousOn_id.mul hF
  have hmono := (lem_app_de_scalar_iii (P2_weightSeq hβ0 hβ1)).2.1
  have hr0 := (lem_app_de_scalar_iii (P2_weightSeq hβ0 hβ1)).2.2.1
  have hm0 : 0 < rW (emaW β) q1 := by
    have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hq1.le) hq1
    rwa [hr0] at this
  filter_upwards [Ioo_mem_nhdsGT hm0] with m hm
  obtain ⟨q, hq, hrq⟩ := intermediate_value_Icc hq1.le (hcont.mono Icc_subset_Ici_self)
    (show m ∈ Icc (rW (emaW β) 0) (rW (emaW β) q1) from
      ⟨by rw [hr0]; exact hm.1.le, hm.2.le⟩)
  have hqpos : 0 < q := by
    rcases hq.1.eq_or_lt with h | h
    · rw [← h, hr0] at hrq
      linarith [hm.1]
    · exact h
  have hex : ∃ a ∈ Ioi (0:ℝ), rW (emaW β) a = m := ⟨q, hqpos, hrq⟩
  have hQ : Qm β m ∈ Ioi (0:ℝ) := Function.invFunOn_mem hex
  have hQe : rW (emaW β) (Qm β m) = m := Function.invFunOn_eq hex
  refine ⟨⟨hQ, ?_⟩, hQe⟩
  by_contra hcon
  push_neg at hcon
  have hle := hmono.monotoneOn (Set.mem_Ici.2 hq1.le) (Set.mem_Ici.2 (Set.mem_Ioi.1 hQ).le) hcon
  linarith [hm.2, hQe, hle]

private lemma P2_Qm_tendsto {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Tendsto (fun m => Qm β m) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, (P2_range hβ0 hβ1 one_pos).mono fun m hm => hm.1.1⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [P2_range hβ0 hβ1 hε] with m hm
  have hpos : 0 < Qm β m := hm.1.1
  rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
  exact hm.1.2

/-- `r_β(q)/q → s₂` as `q ↓ 0`, from the `O(q²)` remainder of `lem_app_pl_weights_i_r`. -/
private lemma P2_ratio {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Tendsto (fun q : ℝ => rW (emaW β) q / q) (𝓝[>] (0:ℝ)) (𝓝 (sPow β 2)) := by
  obtain ⟨C, hC⟩ := (lem_app_pl_weights_i_r hβ0 hβ1).bound
  have hpos : ∀ᶠ q in 𝓝[>] (0:ℝ), 0 < q := self_mem_nhdsWithin
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (P2_tendsto_sub (sPow β 2) C)
    (P2_tendsto_add (sPow β 2) C) ?_ ?_
  · filter_upwards [hC, hpos] with q hq hq0
    show sPow β 2 - C * q ≤ rW (emaW β) q / q
    simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg q)] at hq
    obtain ⟨h1a, _⟩ := abs_le.mp hq
    rw [le_div_iff₀ hq0]
    nlinarith [h1a]
  · filter_upwards [hC, hpos] with q hq hq0
    show rW (emaW β) q / q ≤ sPow β 2 + C * q
    simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg q)] at hq
    obtain ⟨_, h1b⟩ := abs_le.mp hq
    rw [div_le_iff₀ hq0]
    nlinarith [h1b]

private lemma P2_ratio_m {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Tendsto (fun m => m / Qm β m) (𝓝[>] (0 : ℝ)) (𝓝 (sPow β 2)) := by
  refine Tendsto.congr' ?_ ((P2_ratio hβ0 hβ1).comp (P2_Qm_tendsto hβ0 hβ1))
  filter_upwards [P2_range hβ0 hβ1 one_pos] with m hm
  show rW (emaW β) (Qm β m) / Qm β m = m / Qm β m
  rw [hm.2]

/-- `Q_m / (m / s₂) → 1` as `m ↓ 0`. -/
private lemma P2_Qratio {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Tendsto (fun m => Qm β m / (m / sPow β 2)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hs2 := P2_s2_pos hβ0 hβ1
  have h2 : Tendsto (fun m => sPow β 2 / (m / Qm β m)) (𝓝[>] (0 : ℝ))
      (𝓝 (sPow β 2 / sPow β 2)) :=
    tendsto_const_nhds.div (P2_ratio_m hβ0 hβ1) hs2.ne'
  rw [div_self hs2.ne'] at h2
  refine Tendsto.congr (fun m => ?_) h2
  show sPow β 2 / (m / Qm β m) = Qm β m / (m / sPow β 2)
  rw [div_div_eq_mul_div, div_div_eq_mul_div]
  ring

/-- `lem:app-pl-weights`(i), consequence `Q_m ∼ m/\sw2` as `m ↓ 0`, snapshot `cr-2026-10-23`.
LaTeX (`sections/06-power-law/section.tex` l.223–244):
\begin{lemma}[Weight functions]\label{lem:app-pl-weights}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item For $q\ge0$,
\[
\begin{gathered}
\Fw(q)=\sw2-3\sw4q+R_F(q),\quad 0\le R_F\le15\sw6q^2,\\
\Lw(q)=1-3\sw3q+R_L(q),\quad 0\le R_L\le15\sw5q^2 .
\end{gathered}
\]
Consequently $r_\bmom(q)=\sw2q+O(q^2)$, and $Q_m\sim m/\sw2$ and $E(m)\sim m$ as $m\downarrow0$.
\item For $q>0$, $\abs{q\Fw'(q)}\le\Fw(q)$ and $\abs{q\Lw'(q)}\le\Lw(q)$. For $m>0$, $E(m)\le m$.
\item There are $0<c_\bmom\le C_\bmom<\infty$ such that, for $Q\ge1$,
\[
\abs{r_\bmom(Q)-n(Q)}\le C_\bmom,\qquad
c_\bmom\le\sqrt Q\,\Lw(Q)\le C_\bmom,\qquad
c_\bmom\le Q\,r_\bmom'(Q)\le C_\bmom .
\]
Consequently $E(m)\asymp\min(m,1)$ for all $m>0$, and
$\abs{\log Q_m-2\abs{\log\bmom}\,m}\le C_\bmom$ for $m\ge1$.
\end{enumerate}
\end{lemma} -/
theorem lem_app_pl_weights_i_Q {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    IsEquivalent (𝓝[>] (0 : ℝ)) (fun m => Qm β m) (fun m => m / sPow β 2) := by
  exact isEquivalent_of_tendsto_one (P2_Qratio hβ0 hβ1)

/-- `lem:app-pl-weights`(i), consequence `E(m) ∼ m` as `m ↓ 0`, snapshot `cr-2026-10-23`.
LaTeX (`sections/06-power-law/section.tex` l.223–244):
\begin{lemma}[Weight functions]\label{lem:app-pl-weights}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item For $q\ge0$,
\[
\begin{gathered}
\Fw(q)=\sw2-3\sw4q+R_F(q),\quad 0\le R_F\le15\sw6q^2,\\
\Lw(q)=1-3\sw3q+R_L(q),\quad 0\le R_L\le15\sw5q^2 .
\end{gathered}
\]
Consequently $r_\bmom(q)=\sw2q+O(q^2)$, and $Q_m\sim m/\sw2$ and $E(m)\sim m$ as $m\downarrow0$.
\item For $q>0$, $\abs{q\Fw'(q)}\le\Fw(q)$ and $\abs{q\Lw'(q)}\le\Lw(q)$. For $m>0$, $E(m)\le m$.
\item There are $0<c_\bmom\le C_\bmom<\infty$ such that, for $Q\ge1$,
\[
\abs{r_\bmom(Q)-n(Q)}\le C_\bmom,\qquad
c_\bmom\le\sqrt Q\,\Lw(Q)\le C_\bmom,\qquad
c_\bmom\le Q\,r_\bmom'(Q)\le C_\bmom .
\]
Consequently $E(m)\asymp\min(m,1)$ for all $m>0$, and
$\abs{\log Q_m-2\abs{\log\bmom}\,m}\le C_\bmom$ for $m\ge1$.
\end{enumerate}
\end{lemma} -/
theorem lem_app_pl_weights_i_E {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    IsEquivalent (𝓝[>] (0 : ℝ)) (fun m => Efun β m) (fun m => m) := by
  have hs2 := P2_s2_pos hβ0 hβ1
  have hD : Tendsto (fun m => deriv (rW (emaW β)) (Qm β m) / sPow β 2) (𝓝[>] (0:ℝ))
      (𝓝 (sPow β 2 / sPow β 2)) :=
    ((P2_deriv_tendsto hβ0 hβ1).comp (P2_Qm_tendsto hβ0 hβ1)).div_const _
  rw [div_self hs2.ne'] at hD
  have hprod := (P2_Qratio hβ0 hβ1).mul hD
  rw [one_mul] at hprod
  refine isEquivalent_of_tendsto_one ?_
  show Tendsto (fun m => Efun β m / m) (𝓝[>] (0:ℝ)) (𝓝 1)
  refine Tendsto.congr' ?_ hprod
  filter_upwards [self_mem_nhdsWithin] with m hm
  have hm0 : m ≠ 0 := (Set.mem_Ioi.1 hm).ne'
  have hs2' : sPow β 2 ≠ 0 := hs2.ne'
  unfold Efun
  field_simp

/-! ### Private helpers for `lem_app_pl_weights_ii_F`, `_ii_L`, `_ii_E` (fully proved) -/

private lemma P3_int_J {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun g : ℝ => g ^ 2 / (1 + x * g ^ 2)) (gaussianReal 0 1) := by
  have hpos : ∀ g : ℝ, 0 < 1 + x * g ^ 2 := fun g => by
    have := mul_nonneg hx (sq_nonneg g)
    linarith
  refine Integrable.mono' (Muon.Foundations.gaussian_integrable_pow 2)
    (Continuous.div (by fun_prop) (by fun_prop) (fun g => (hpos g).ne')).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg g) (hpos g).le)]
  exact div_le_self (sq_nonneg g) (le_add_of_nonneg_right (mul_nonneg hx (sq_nonneg g)))

private lemma P3_J_bounds {x : ℝ} (hx : 0 ≤ x) : 0 ≤ J x ∧ J x ≤ 1 := by
  have hpos : ∀ g : ℝ, 0 < 1 + x * g ^ 2 := fun g => by
    have := mul_nonneg hx (sq_nonneg g)
    linarith
  refine ⟨integral_nonneg fun g => div_nonneg (sq_nonneg g) (hpos g).le, ?_⟩
  unfold J
  calc ∫ g : ℝ, g ^ 2 / (1 + x * g ^ 2) ∂(gaussianReal 0 1)
      ≤ ∫ g : ℝ, g ^ 2 ∂(gaussianReal 0 1) :=
        integral_mono (P3_int_J hx) (Muon.Foundations.gaussian_integrable_pow 2)
          (fun g => div_le_self (sq_nonneg g) (le_add_of_nonneg_right (mul_nonneg hx (sq_nonneg g))))
    _ = 1 := Muon.Foundations.gaussian_moment_two

private lemma P3_D_le_J {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ ∫ g : ℝ, g ^ 2 / (1 + x * g ^ 2) ^ 2 ∂(gaussianReal 0 1) ∧
    ∫ g : ℝ, g ^ 2 / (1 + x * g ^ 2) ^ 2 ∂(gaussianReal 0 1) ≤ J x := by
  have hpos : ∀ g : ℝ, 0 < 1 + x * g ^ 2 := fun g => by
    have := mul_nonneg hx (sq_nonneg g)
    linarith
  have hD : Integrable (fun g : ℝ => g ^ 2 / (1 + x * g ^ 2) ^ 2) (gaussianReal 0 1) := by
    refine Integrable.mono' (Muon.Foundations.gaussian_integrable_pow 2)
      (Continuous.div (by fun_prop) (by fun_prop)
        (fun g => pow_ne_zero 2 (hpos g).ne')).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg g) (pow_nonneg (hpos g).le 2))]
    exact div_le_self (sq_nonneg g) (one_le_pow₀ (le_add_of_nonneg_right (mul_nonneg hx (sq_nonneg g))))
  refine ⟨integral_nonneg fun g => div_nonneg (sq_nonneg g) (pow_nonneg (hpos g).le 2), ?_⟩
  unfold J
  refine integral_mono hD (P3_int_J hx) (fun g => ?_)
  exact div_le_div_of_nonneg_left (sq_nonneg g) (hpos g)
    (by nlinarith [mul_nonneg hx (sq_nonneg g), sq_nonneg (x * g ^ 2)])

/-- Termwise bound `r_β'(q) ≤ F_β(q)` for `q ≥ 0`. -/
private lemma P3_R_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    ∑' j : ℕ, emaW β j ^ 2 * ∫ g : ℝ, g ^ 2 / (1 + emaW β j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1)
      ≤ Fw (emaW β) q := by
  have hs2 : Summable (fun j : ℕ => emaW β j ^ 2) :=
    summable_emaW_pow_P1 hβ0 hβ1 (p := 2) (by norm_num)
  have hL : Summable (fun j : ℕ => emaW β j ^ 2 *
      ∫ g : ℝ, g ^ 2 / (1 + emaW β j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1)) := by
    refine Summable.of_nonneg_of_le
      (fun j => mul_nonneg (sq_nonneg _)
        (P3_D_le_J (mul_nonneg (sq_nonneg _) hq)).1)
      (fun j => ?_) hs2
    exact mul_le_of_le_one_right (sq_nonneg _)
      (le_trans (P3_D_le_J (mul_nonneg (sq_nonneg _) hq)).2 (P3_J_bounds (mul_nonneg (sq_nonneg _) hq)).2)
  have hR : Summable (fun j : ℕ => emaW β j ^ 2 * J (emaW β j ^ 2 * q)) := by
    refine Summable.of_nonneg_of_le
      (fun j => mul_nonneg (sq_nonneg _) (P3_J_bounds (mul_nonneg (sq_nonneg _) hq)).1)
      (fun j => mul_le_of_le_one_right (sq_nonneg _) (P3_J_bounds (mul_nonneg (sq_nonneg _) hq)).2)
      hs2
  unfold Fw
  refine Summable.tsum_le_tsum (fun j => ?_) hL hR
  exact mul_le_mul_of_nonneg_left (P3_D_le_J (mul_nonneg (sq_nonneg _) hq)).2 (sq_nonneg _)

/-- `F_β` has derivative `(r_β'(q) q - r_β(q)) / q²` at `q > 0`, from `r_β = q F_β`. -/
private lemma P3_Fw_hasDeriv {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (Fw (emaW β))
      (((∑' j : ℕ, emaW β j ^ 2 * ∫ g : ℝ, g ^ 2 / (1 + emaW β j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1)) * q
        - rW (emaW β) q * 1) / q ^ 2) q := by
  have hr := (lem_app_de_scalar_iii (P2_weightSeq hβ0 hβ1)).2.2.2.1 q hq
  have hdiv := hr.div (hasDerivAt_id' (x := q)) hq.ne'
  have hEq : (fun y : ℝ => rW (emaW β) y / y) =ᶠ[𝓝 q] Fw (emaW β) := by
    filter_upwards [Ioi_mem_nhds hq] with y hy
    exact mul_div_cancel_left₀ _ (Set.mem_Ioi.1 hy).ne'
  exact hdiv.congr_of_eventuallyEq hEq.symm

private lemma P3_int_Dm {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun g : ℝ => g ^ 4 / (1 + x * g ^ 2) ^ 2) (gaussianReal 0 1) := by
  have hpos : ∀ g : ℝ, 0 < 1 + x * g ^ 2 := fun g => by
    have := mul_nonneg hx (sq_nonneg g)
    linarith
  refine Integrable.mono' (Muon.Foundations.gaussian_integrable_pow 4)
    (Continuous.div (by fun_prop) (by fun_prop)
      (fun g => pow_ne_zero 2 (hpos g).ne')).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg ((by positivity)) (pow_nonneg (hpos g).le 2))]
  exact div_le_self (by positivity) (one_le_pow₀ (le_add_of_nonneg_right (mul_nonneg hx (sq_nonneg g))))

private lemma P3_Dm {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ ∫ g : ℝ, g ^ 4 / (1 + x * g ^ 2) ^ 2 ∂(gaussianReal 0 1) ∧
    ∫ g : ℝ, g ^ 4 / (1 + x * g ^ 2) ^ 2 ∂(gaussianReal 0 1) ≤ 3 := by
  have hpos : ∀ g : ℝ, 0 < 1 + x * g ^ 2 := fun g => by
    have := mul_nonneg hx (sq_nonneg g)
    linarith
  refine ⟨integral_nonneg fun g => div_nonneg (by positivity) (pow_nonneg (hpos g).le 2), ?_⟩
  calc ∫ g : ℝ, g ^ 4 / (1 + x * g ^ 2) ^ 2 ∂(gaussianReal 0 1)
      ≤ ∫ g : ℝ, g ^ 4 ∂(gaussianReal 0 1) :=
        integral_mono (P3_int_Dm hx) (Muon.Foundations.gaussian_integrable_pow 4)
          (fun g => div_le_self (by positivity) (one_le_pow₀ (le_add_of_nonneg_right (mul_nonneg hx (sq_nonneg g)))))
    _ = 3 := Muon.Foundations.gaussian_moment_four

/-- `x · E[g⁴/(1+xg²)²] ≤ J(x)` for `x ≥ 0` (pointwise `x g⁴/(1+xg²)² ≤ g²/(1+xg²)`). -/
private lemma P3_xDm_le {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x * ∫ g : ℝ, g ^ 4 / (1 + x * g ^ 2) ^ 2 ∂(gaussianReal 0 1) ∧
    x * ∫ g : ℝ, g ^ 4 / (1 + x * g ^ 2) ^ 2 ∂(gaussianReal 0 1) ≤ J x := by
  refine ⟨mul_nonneg hx (P3_Dm hx).1, ?_⟩
  rw [← integral_const_mul]
  unfold J
  refine integral_mono ((P3_int_Dm hx).const_mul x) (P3_int_J hx) (fun g => ?_)
  dsimp only
  have hp : 0 < 1 + x * g ^ 2 := by
    have := mul_nonneg hx (sq_nonneg g)
    linarith
  rw [← mul_div_assoc, div_le_div_iff₀ (pow_pos hp 2) hp]
  nlinarith [mul_nonneg (sq_nonneg g) hp.le]

/-- Derivative of `J` at `x0 > 0`: `J'(x0) = -E[g⁴/(1+x0 g²)²]`. -/
private lemma P3_J_hasDeriv {x0 : ℝ} (hx0 : 0 < x0) :
    HasDerivAt J (-∫ g : ℝ, g ^ 4 / (1 + x0 * g ^ 2) ^ 2 ∂(gaussianReal 0 1)) x0 := by
  have hpos : ∀ x : ℝ, 0 < x → ∀ g : ℝ, 0 < 1 + x * g ^ 2 := fun x hx g => by
    have := mul_nonneg hx.le (sq_nonneg g)
    linarith
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := fun (x : ℝ) (g : ℝ) => g ^ 2 / (1 + x * g ^ 2))
    (F' := fun (x : ℝ) (g : ℝ) => -(g ^ 4 / (1 + x * g ^ 2) ^ 2))
    (x₀ := x0) (s := Ioi 0) (bound := fun g : ℝ => g ^ 4)
    (Ioi_mem_nhds hx0) ?_ (P3_int_J hx0.le) ?_ ?_ (Muon.Foundations.gaussian_integrable_pow 4) ?_).2
  · unfold J
    simpa only [integral_neg] using h
  · filter_upwards [Ioi_mem_nhds hx0] with x hx
    have hx' : (0:ℝ) < x := hx
    exact (Continuous.div (by fun_prop) (by fun_prop)
      (fun g => (hpos x hx' g).ne')).aestronglyMeasurable
  · exact (Continuous.neg (Continuous.div (by fun_prop) (by fun_prop)
      (fun g => pow_ne_zero 2 (hpos x0 hx0 g).ne'))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun g x hx => ?_
    have hx' : (0:ℝ) < x := hx
    show ‖-(g ^ 4 / (1 + x * g ^ 2) ^ 2)‖ ≤ g ^ 4
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ((by positivity)) (pow_nonneg (hpos x hx' g).le 2))]
    exact div_le_self ((by positivity))
      (one_le_pow₀ (le_add_of_nonneg_right (mul_nonneg hx'.le (sq_nonneg g))))
  · refine Filter.Eventually.of_forall fun g x hx => ?_
    have hx' : (0:ℝ) < x := hx
    have hne : 1 + x * g ^ 2 ≠ 0 := (hpos x hx' g).ne'
    have h1 : HasDerivAt (fun y : ℝ => 1 + y * g ^ 2) (g ^ 2) x := by
      have := ((hasDerivAt_id' (x := x)).mul_const (g ^ 2)).const_add 1
      simpa using this
    have h2 := (hasDerivAt_const x (g ^ 2)).div h1 hne
    convert h2 using 1
    field_simp
    ring

/-- The `n`-th term of `L_β`: derivative in `q` at `q > 0`. -/
private lemma P3_term_hasDeriv {β : ℝ} (n : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun z : ℝ => emaW β n * J (emaW β n ^ 2 * z))
      (emaW β n * (-(∫ g : ℝ, g ^ 4 / (1 + emaW β n ^ 2 * y * g ^ 2) ^ 2 ∂(gaussianReal 0 1)))
        * emaW β n ^ 2) y := by
  by_cases h0 : emaW β n = 0
  · simp only [h0]
    simpa using hasDerivAt_const y (0 : ℝ)
  · have hw2 : 0 < emaW β n ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0))
    have hx : 0 < emaW β n ^ 2 * y := mul_pos hw2 hy
    have hlin : HasDerivAt (fun z : ℝ => emaW β n ^ 2 * z) (emaW β n ^ 2 * 1) y :=
      (hasDerivAt_id' (x := y)).const_mul _
    have hJ := (P3_J_hasDeriv hx).comp y hlin
    have hc := hJ.const_mul (emaW β n)
    exact hc.congr_deriv (by ring)

/-- Bound on the `n`-th derivative term, uniform in `y > 0`. -/
private lemma P3_term_bound {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    ‖emaW β n * (-(∫ g : ℝ, g ^ 4 / (1 + emaW β n ^ 2 * y * g ^ 2) ^ 2 ∂(gaussianReal 0 1)))
      * emaW β n ^ 2‖ ≤ 3 * emaW β n ^ 3 := by
  have hw : 0 ≤ emaW β n := (P2_weightSeq hβ0 hβ1).1 n
  obtain ⟨hI0, hI3⟩ := P3_Dm (x := emaW β n ^ 2 * y) (mul_nonneg (sq_nonneg _) hy.le)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [mul_nonneg (pow_nonneg hw 3) hI0, mul_nonneg (pow_nonneg hw 3) (sub_nonneg.2 hI3)]

/-- Summability of the `J`-series defining `L_β(q)`, `q ≥ 0`. -/
private lemma P3_Lw_summable {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    Summable (fun n : ℕ => emaW β n * J (emaW β n ^ 2 * q)) :=
  Summable.of_nonneg_of_le
    (fun n => mul_nonneg ((P2_weightSeq hβ0 hβ1).1 n) (P3_J_bounds (mul_nonneg (sq_nonneg _) hq)).1)
    (fun n => mul_le_of_le_one_right ((P2_weightSeq hβ0 hβ1).1 n) (P3_J_bounds (mul_nonneg (sq_nonneg _) hq)).2)
    (P2_weightSeq hβ0 hβ1).2.1

/-- Termwise-differentiated series: derivative of `L_β` at `q > 0`. -/
private lemma P3_Lw_hasDeriv {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (Lw (emaW β))
      (∑' n : ℕ, emaW β n * (-(∫ g : ℝ, g ^ 4 / (1 + emaW β n ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1)))
        * emaW β n ^ 2) q := by
  have hu : Summable (fun n : ℕ => 3 * emaW β n ^ 3) :=
    (summable_emaW_pow_P1 hβ0 hβ1 (p := 3) (by norm_num)).mul_left 3
  exact hasDerivAt_tsum_of_isPreconnected
    (g := fun (n : ℕ) (z : ℝ) => emaW β n * J (emaW β n ^ 2 * z))
    (g' := fun (n : ℕ) (y : ℝ) => emaW β n * (-(∫ g : ℝ, g ^ 4 / (1 + emaW β n ^ 2 * y * g ^ 2) ^ 2 ∂(gaussianReal 0 1)))
        * emaW β n ^ 2)
    (u := fun n : ℕ => 3 * emaW β n ^ 3)
    (t := Ioi (0:ℝ)) (y₀ := q)
    hu isOpen_Ioi isPreconnected_Ioi
    (fun n y hy => P3_term_hasDeriv (β := β) n hy)
    (fun n y hy => P3_term_bound hβ0 hβ1 n hy)
    (Set.mem_Ioi.2 hq) (P3_Lw_summable hβ0 hβ1 hq.le) (Set.mem_Ioi.2 hq)

/-- For `0 < β < 1` every `m > 0` lies in the range of `r_β` on `(0,∞)`. -/
private lemma P3_range {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    ∃ a ∈ Ioi (0:ℝ), rW (emaW β) a = m := by
  have hcont : ContinuousOn (rW (emaW β)) (Ici 0) :=
    continuousOn_id.mul (lem_app_de_scalar_ii (P2_weightSeq hβ0.le hβ1)).2.2.1
  have hr0 := (lem_app_de_scalar_iii (P2_weightSeq hβ0.le hβ1)).2.2.1
  have hT := (lem_app_de_scalar_iii (P2_weightSeq hβ0.le hβ1)).2.2.2.2.2.2
  have hinf : {j : ℕ | 0 < emaW β j} = Set.univ := by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    unfold emaW
    exact mul_pos (by linarith) (pow_pos hβ0 j)
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

/-- `lem:app-pl-weights`(ii), the derivative bound for `F_β`, snapshot `cr-2026-10-23`. The
differentiability clause records that `F_β'` in the displayed bound exists for `q > 0`.
LaTeX (`sections/06-power-law/section.tex` l.223–244):
\begin{lemma}[Weight functions]\label{lem:app-pl-weights}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item For $q\ge0$,
\[
\begin{gathered}
\Fw(q)=\sw2-3\sw4q+R_F(q),\quad 0\le R_F\le15\sw6q^2,\\
\Lw(q)=1-3\sw3q+R_L(q),\quad 0\le R_L\le15\sw5q^2 .
\end{gathered}
\]
Consequently $r_\bmom(q)=\sw2q+O(q^2)$, and $Q_m\sim m/\sw2$ and $E(m)\sim m$ as $m\downarrow0$.
\item For $q>0$, $\abs{q\Fw'(q)}\le\Fw(q)$ and $\abs{q\Lw'(q)}\le\Lw(q)$. For $m>0$, $E(m)\le m$.
\item There are $0<c_\bmom\le C_\bmom<\infty$ such that, for $Q\ge1$,
\[
\abs{r_\bmom(Q)-n(Q)}\le C_\bmom,\qquad
c_\bmom\le\sqrt Q\,\Lw(Q)\le C_\bmom,\qquad
c_\bmom\le Q\,r_\bmom'(Q)\le C_\bmom .
\]
Consequently $E(m)\asymp\min(m,1)$ for all $m>0$, and
$\abs{\log Q_m-2\abs{\log\bmom}\,m}\le C_\bmom$ for $m\ge1$.
\end{enumerate}
\end{lemma} -/
theorem lem_app_pl_weights_ii_F {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∀ q : ℝ, 0 < q →
      DifferentiableAt ℝ (Fw (emaW β)) q ∧
      |q * deriv (Fw (emaW β)) q| ≤ Fw (emaW β) q := by
  intro q hq
  have hd := P3_Fw_hasDeriv hβ0 hβ1 hq
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.deriv]
  have hR := P3_R_le hβ0 hβ1 hq.le
  have hRpos := (lem_app_de_scalar_iii (P2_weightSeq hβ0 hβ1)).2.2.2.2.1 q hq
  have hq0 : q ≠ 0 := hq.ne'
  set R := (∑' j : ℕ, emaW β j ^ 2 * ∫ g : ℝ, g ^ 2 / (1 + emaW β j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1)) with hRdef
  have hrw : rW (emaW β) q = q * Fw (emaW β) q := rfl
  have key : q * ((R * q - rW (emaW β) q * 1) / q ^ 2) = R - Fw (emaW β) q := by
    rw [hrw]
    field_simp <;> ring
  rw [key, abs_le]
  constructor <;> linarith

/-- `lem:app-pl-weights`(ii), the derivative bound for `L_β`, snapshot `cr-2026-10-23`. The
differentiability clause records that `L_β'` in the displayed bound exists for `q > 0`.
LaTeX (`sections/06-power-law/section.tex` l.223–244):
\begin{lemma}[Weight functions]\label{lem:app-pl-weights}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item For $q\ge0$,
\[
\begin{gathered}
\Fw(q)=\sw2-3\sw4q+R_F(q),\quad 0\le R_F\le15\sw6q^2,\\
\Lw(q)=1-3\sw3q+R_L(q),\quad 0\le R_L\le15\sw5q^2 .
\end{gathered}
\]
Consequently $r_\bmom(q)=\sw2q+O(q^2)$, and $Q_m\sim m/\sw2$ and $E(m)\sim m$ as $m\downarrow0$.
\item For $q>0$, $\abs{q\Fw'(q)}\le\Fw(q)$ and $\abs{q\Lw'(q)}\le\Lw(q)$. For $m>0$, $E(m)\le m$.
\item There are $0<c_\bmom\le C_\bmom<\infty$ such that, for $Q\ge1$,
\[
\abs{r_\bmom(Q)-n(Q)}\le C_\bmom,\qquad
c_\bmom\le\sqrt Q\,\Lw(Q)\le C_\bmom,\qquad
c_\bmom\le Q\,r_\bmom'(Q)\le C_\bmom .
\]
Consequently $E(m)\asymp\min(m,1)$ for all $m>0$, and
$\abs{\log Q_m-2\abs{\log\bmom}\,m}\le C_\bmom$ for $m\ge1$.
\end{enumerate}
\end{lemma} -/
theorem lem_app_pl_weights_ii_L {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∀ q : ℝ, 0 < q →
      DifferentiableAt ℝ (Lw (emaW β)) q ∧
      |q * deriv (Lw (emaW β)) q| ≤ Lw (emaW β) q := by
  intro q hq
  have hd := P3_Lw_hasDeriv hβ0 hβ1 hq
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.deriv]
  have hW := P2_weightSeq hβ0 hβ1
  have hg0 := P3_Lw_summable hβ0 hβ1 hq.le
  have hA_le : ∀ n : ℕ, emaW β n * ((emaW β n ^ 2 * q) * ∫ g : ℝ, g ^ 4 / (1 + emaW β n ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1))
      ≤ emaW β n * J (emaW β n ^ 2 * q) :=
    fun n => mul_le_mul_of_nonneg_left (P3_xDm_le (mul_nonneg (sq_nonneg _) hq.le)).2 (hW.1 n)
  have hA_nn : ∀ n : ℕ, 0 ≤ emaW β n * ((emaW β n ^ 2 * q) * ∫ g : ℝ, g ^ 4 / (1 + emaW β n ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1)) :=
    fun n => mul_nonneg (hW.1 n) (P3_xDm_le (mul_nonneg (sq_nonneg _) hq.le)).1
  have hAs : Summable (fun n : ℕ => emaW β n * ((emaW β n ^ 2 * q) * ∫ g : ℝ, g ^ 4 / (1 + emaW β n ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1))) :=
    Summable.of_nonneg_of_le hA_nn hA_le hg0
  have hS : q * ∑' n : ℕ, emaW β n * (-(∫ g : ℝ, g ^ 4 / (1 + emaW β n ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1)))
        * emaW β n ^ 2
      = ∑' n : ℕ, -(emaW β n * ((emaW β n ^ 2 * q) * ∫ g : ℝ, g ^ 4 / (1 + emaW β n ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1))) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by ring
  rw [hS]
  unfold Lw
  rw [abs_le]
  constructor
  · have h : ∑' n : ℕ, emaW β n * ((emaW β n ^ 2 * q) * ∫ g : ℝ, g ^ 4 / (1 + emaW β n ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1))
        ≤ ∑' n : ℕ, emaW β n * J (emaW β n ^ 2 * q) :=
      Summable.tsum_le_tsum hA_le hAs hg0
    rw [tsum_neg]
    linarith
  · have h1 : ∑' n : ℕ, -(emaW β n * ((emaW β n ^ 2 * q) * ∫ g : ℝ, g ^ 4 / (1 + emaW β n ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1)))
        ≤ 0 :=
      tsum_nonpos fun n => neg_nonpos.2 (hA_nn n)
    have h2 : 0 ≤ ∑' n : ℕ, emaW β n * J (emaW β n ^ 2 * q) :=
      tsum_nonneg fun n => mul_nonneg (hW.1 n) (P3_J_bounds (mul_nonneg (sq_nonneg _) hq.le)).1
    linarith

/-- `lem:app-pl-weights`(ii), the bound `E(m) ≤ m`, snapshot `cr-2026-10-23`. The source
fixes `β ∈ (0,1)`: at `β = 0` the range of `r_0` is `(0,1)`, so `Q_m` is junk for `m ≥ 1`.
LaTeX (`sections/06-power-law/section.tex` l.223–244):
\begin{lemma}[Weight functions]\label{lem:app-pl-weights}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item For $q\ge0$,
\[
\begin{gathered}
\Fw(q)=\sw2-3\sw4q+R_F(q),\quad 0\le R_F\le15\sw6q^2,\\
\Lw(q)=1-3\sw3q+R_L(q),\quad 0\le R_L\le15\sw5q^2 .
\end{gathered}
\]
Consequently $r_\bmom(q)=\sw2q+O(q^2)$, and $Q_m\sim m/\sw2$ and $E(m)\sim m$ as $m\downarrow0$.
\item For $q>0$, $\abs{q\Fw'(q)}\le\Fw(q)$ and $\abs{q\Lw'(q)}\le\Lw(q)$. For $m>0$, $E(m)\le m$.
\item There are $0<c_\bmom\le C_\bmom<\infty$ such that, for $Q\ge1$,
\[
\abs{r_\bmom(Q)-n(Q)}\le C_\bmom,\qquad
c_\bmom\le\sqrt Q\,\Lw(Q)\le C_\bmom,\qquad
c_\bmom\le Q\,r_\bmom'(Q)\le C_\bmom .
\]
Consequently $E(m)\asymp\min(m,1)$ for all $m>0$, and
$\abs{\log Q_m-2\abs{\log\bmom}\,m}\le C_\bmom$ for $m\ge1$.
\end{enumerate}
\end{lemma} -/
theorem lem_app_pl_weights_ii_E {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ m : ℝ, 0 < m → Efun β m ≤ m := by
  intro m hm
  have hex : ∃ a ∈ Ioi (0:ℝ), rW (emaW β) a = m := P3_range hβ0 hβ1 hm
  have hQ : Qm β m ∈ Ioi (0:ℝ) := Function.invFunOn_mem hex
  have hQe : rW (emaW β) (Qm β m) = m := Function.invFunOn_eq hex
  have hq : 0 < Qm β m := hQ
  have hfin : Qm β m * Fw (emaW β) (Qm β m) = m := by
    have h : Qm β m * Fw (emaW β) (Qm β m) = rW (emaW β) (Qm β m) := rfl
    rw [h, hQe]
  unfold Efun
  rw [((lem_app_de_scalar_iii (P2_weightSeq hβ0.le hβ1)).2.2.2.1 (Qm β m) hq).deriv]
  exact le_trans (mul_le_mul_of_nonneg_left (P3_R_le hβ0.le hβ1 hq.le) hq.le) hfin.le

/-! ### Private helpers for `lem_app_pl_weights_iii`, `_iii_E`, `_iii_logQ` -/

private lemma P4_den_pos {x : ℝ} (hx : 0 ≤ x) (g : ℝ) : 0 < 1 + x * g ^ 2 := by
  have := mul_nonneg hx (sq_nonneg g)
  linarith

private lemma P4_int_inv {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun g : ℝ => 1 / (1 + x * g ^ 2)) (gaussianReal 0 1) := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (Filter.Eventually.of_forall fun g => ?_)
  · exact (Continuous.div continuous_const (by fun_prop)
      (fun g => (P4_den_pos hx g).ne')).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg zero_le_one (P4_den_pos hx g).le)]
    exact (div_le_one (P4_den_pos hx g)).2
      (le_add_of_nonneg_right (mul_nonneg hx (sq_nonneg g)))

private lemma P4_int_D {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun g : ℝ => g ^ 2 / (1 + x * g ^ 2) ^ 2) (gaussianReal 0 1) := by
  refine Integrable.mono' (Muon.Foundations.gaussian_integrable_pow 2)
    (Continuous.div (by fun_prop) (by fun_prop)
      (fun g => pow_ne_zero 2 (P4_den_pos hx g).ne')).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg g) (pow_nonneg (P4_den_pos hx g).le 2))]
  exact div_le_self (sq_nonneg g)
    (one_le_pow₀ (le_add_of_nonneg_right (mul_nonneg hx (sq_nonneg g))))

private lemma P4_one_sub {x : ℝ} (hx : 0 ≤ x) :
    1 - x * J x = ∫ g : ℝ, 1 / (1 + x * g ^ 2) ∂(gaussianReal 0 1) := by
  have h1 : ∫ g : ℝ, (1 - x * (g ^ 2 / (1 + x * g ^ 2))) ∂(gaussianReal 0 1)
      = 1 - ∫ g : ℝ, x * (g ^ 2 / (1 + x * g ^ 2)) ∂(gaussianReal 0 1) := by
    rw [integral_sub (integrable_const (1 : ℝ)) ((P3_int_J hx).const_mul x)]
    simp
  unfold J
  rw [← integral_const_mul, ← h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  have := (P4_den_pos hx g).ne'
  field_simp
  ring

private lemma P4_f_bounds {x : ℝ} (hx : 0 ≤ x) : 0 ≤ x * J x ∧ x * J x ≤ 1 ∧ x * J x ≤ x := by
  refine ⟨mul_nonneg hx (P3_J_bounds hx).1, ?_, ?_⟩
  · have h : 0 ≤ 1 - x * J x := by
      rw [P4_one_sub hx]
      exact integral_nonneg fun g => div_nonneg zero_le_one (P4_den_pos hx g).le
    linarith
  · exact mul_le_of_le_one_right hx (P3_J_bounds hx).2

private lemma P4_inv_int_scaled {x : ℝ} (hx : 0 < x) :
    Integrable (fun y : ℝ => 1 / (1 + x * y ^ 2)) := by
  have h := integrable_inv_one_add_sq.comp_mul_left' (R := Real.sqrt x)
    (Real.sqrt_pos.mpr hx).ne'
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  show (1 + (Real.sqrt x * y) ^ 2)⁻¹ = 1 / (1 + x * y ^ 2)
  rw [mul_pow, Real.sq_sqrt hx.le, one_div]

private lemma P4_lebesgue_int {x : ℝ} (hx : 0 < x) :
    ∫ y : ℝ, 1 / (1 + x * y ^ 2) = Real.pi / Real.sqrt x := by
  have h := Measure.integral_comp_mul_left (fun z : ℝ => (1 + z ^ 2)⁻¹) (Real.sqrt x)
  have e : (fun y : ℝ => 1 / (1 + x * y ^ 2)) =
      fun y : ℝ => (fun z : ℝ => (1 + z ^ 2)⁻¹) (Real.sqrt x * y) := by
    funext y
    show 1 / (1 + x * y ^ 2) = (1 + (Real.sqrt x * y) ^ 2)⁻¹
    rw [mul_pow, Real.sq_sqrt hx.le, one_div]
  rw [e, h, integral_univ_inv_one_add_sq, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hx)),
    smul_eq_mul]
  ring

private lemma P4_gauss_inv_le {x : ℝ} (hx : 0 < x) :
    ∫ g, 1 / (1 + x * g ^ 2) ∂(gaussianReal 0 1) ≤ Real.sqrt (Real.pi / 2) / Real.sqrt x := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have hint : Integrable (fun g : ℝ => 1 / (1 + x * g ^ 2)) := P4_inv_int_scaled hx
  have hpt : ∀ g : ℝ, gaussianPDFReal 0 1 g • (1 / (1 + x * g ^ 2)) ≤
      (1 / Real.sqrt (2 * Real.pi)) • (1 / (1 + x * g ^ 2)) := fun g => by
    rw [smul_eq_mul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_right (Muon.Foundations.gaussian_pdf_le g)
      (div_nonneg zero_le_one (P4_den_pos hx.le g).le)
  have hmeas : AEStronglyMeasurable (fun g : ℝ => gaussianPDFReal 0 1 g • (1 / (1 + x * g ^ 2)))
      volume :=
    ((measurable_gaussianPDFReal 0 1).smul (by fun_prop)).aestronglyMeasurable
  have hI : Integrable (fun g : ℝ => gaussianPDFReal 0 1 g • (1 / (1 + x * g ^ 2))) :=
    Integrable.mono' (hint.const_mul (1 / Real.sqrt (2 * Real.pi))) hmeas
      (Filter.Eventually.of_forall fun g => by
        rw [Real.norm_eq_abs, smul_eq_mul, abs_of_nonneg (mul_nonneg
          (gaussianPDFReal_nonneg 0 1 g) (div_nonneg zero_le_one (P4_den_pos hx.le g).le))]
        exact mul_le_mul_of_nonneg_right (Muon.Foundations.gaussian_pdf_le g)
          (div_nonneg zero_le_one (P4_den_pos hx.le g).le))
  have key : Real.sqrt (Real.pi / 2) * Real.sqrt (2 * Real.pi) = Real.pi := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show Real.pi / 2 * (2 * Real.pi) = Real.pi ^ 2 by ring]
    exact Real.sqrt_sq Real.pi_pos.le
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hs2 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  calc ∫ g, gaussianPDFReal 0 1 g • (1 / (1 + x * g ^ 2))
      ≤ ∫ g, (1 / Real.sqrt (2 * Real.pi)) • (1 / (1 + x * g ^ 2)) :=
        integral_mono hI (hint.const_mul _) hpt
    _ = 1 / Real.sqrt (2 * Real.pi) * (Real.pi / Real.sqrt x) := by
        rw [integral_smul, smul_eq_mul, P4_lebesgue_int hx]
    _ = Real.sqrt (Real.pi / 2) / Real.sqrt x := by
        field_simp
        linear_combination (-1 : ℝ) * key

/-- `1 - f(x) ≤ √(π/2) / √x`. -/
private lemma P4_one_sub_le {x : ℝ} (hx : 0 < x) :
    1 - x * J x ≤ Real.sqrt (Real.pi / 2) / Real.sqrt x := by
  rw [P4_one_sub hx.le]
  exact P4_gauss_inv_le hx

private lemma P4_k_bounds {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x * ∫ g : ℝ, g ^ 2 / (1 + x * g ^ 2) ^ 2 ∂(gaussianReal 0 1) ∧
    x * ∫ g : ℝ, g ^ 2 / (1 + x * g ^ 2) ^ 2 ∂(gaussianReal 0 1) ≤ x * J x ∧
    x * ∫ g : ℝ, g ^ 2 / (1 + x * g ^ 2) ^ 2 ∂(gaussianReal 0 1) ≤ 1 - x * J x := by
  obtain ⟨h0, h1⟩ := P3_D_le_J hx
  refine ⟨mul_nonneg hx h0, mul_le_mul_of_nonneg_left h1 hx, ?_⟩
  rw [P4_one_sub hx, ← integral_const_mul]
  refine integral_mono ((P4_int_D hx).const_mul x) (P4_int_inv hx) (fun g => ?_)
  have hA := P4_den_pos hx g
  have e : x * (g ^ 2 / (1 + x * g ^ 2) ^ 2) = (x * g ^ 2) / (1 + x * g ^ 2) ^ 2 := by ring
  show x * (g ^ 2 / (1 + x * g ^ 2) ^ 2) ≤ 1 / (1 + x * g ^ 2)
  rw [e, div_le_div_iff₀ (pow_pos hA 2) hA]
  nlinarith [hA, mul_nonneg hx (sq_nonneg g)]

/-- Cauchy–Schwarz in the form `J(x)² ≤ ∫ g²/(1+xg²)²`. -/
private lemma P4_D_ge {x : ℝ} (hx : 0 ≤ x) :
    J x ^ 2 ≤ ∫ g : ℝ, g ^ 2 / (1 + x * g ^ 2) ^ 2 ∂(gaussianReal 0 1) := by
  have hpt : ∀ g : ℝ, 2 * J x * (g ^ 2 / (1 + x * g ^ 2)) - J x ^ 2 * g ^ 2
      ≤ g ^ 2 / (1 + x * g ^ 2) ^ 2 := by
    intro g
    have hA := (P4_den_pos hx g).ne'
    rw [← sub_nonneg]
    have : g ^ 2 / (1 + x * g ^ 2) ^ 2 - (2 * J x * (g ^ 2 / (1 + x * g ^ 2)) - J x ^ 2 * g ^ 2)
        = g ^ 2 * (1 / (1 + x * g ^ 2) - J x) ^ 2 := by
      field_simp
      ring
    rw [this]
    positivity
  have hJ : ∫ g : ℝ, g ^ 2 / (1 + x * g ^ 2) ∂(gaussianReal 0 1) = J x := rfl
  calc J x ^ 2 = ∫ g : ℝ, (2 * J x * (g ^ 2 / (1 + x * g ^ 2)) - J x ^ 2 * g ^ 2)
          ∂(gaussianReal 0 1) := by
        rw [integral_sub ((P3_int_J hx).const_mul _)
          ((Muon.Foundations.gaussian_integrable_pow 2).const_mul _),
          integral_const_mul, integral_const_mul, hJ, Muon.Foundations.gaussian_moment_two]
        ring
    _ ≤ _ := integral_mono (((P3_int_J hx).const_mul _).sub
          ((Muon.Foundations.gaussian_integrable_pow 2).const_mul _)) (P4_int_D hx) hpt

private lemma P4_emaW_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (j : ℕ) : 0 < emaW β j := by
  unfold emaW
  exact mul_pos (by linarith) (pow_pos hβ0 j)

private lemma P4_emaW_le_one {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (j : ℕ) : emaW β j ≤ 1 := by
  unfold emaW
  have h1 : β ^ j ≤ 1 := pow_le_one₀ hβ0 hβ1.le
  calc (1 - β) * β ^ j ≤ 1 * β ^ j :=
        mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hβ0 j)
    _ ≤ 1 := by linarith

/-- `w_{j+d} = β^d w_j`. -/
private lemma P4_emaW_add (β : ℝ) (j d : ℕ) : emaW β (j + d) = β ^ d * emaW β j := by
  unfold emaW
  rw [pow_add]
  ring

private lemma P4_split {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Q : ℝ} (hQ : 0 < Q) :
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
      rw [P4_emaW_add]
      exact mul_le_of_le_one_left (P4_emaW_pos hβ0 hβ1 _).le (pow_le_one₀ hβ0.le hβ1.le)
    have h0 := (P4_emaW_pos hβ0 hβ1 j).le
    calc emaW β j ^ 2 * Q ≤ emaW β (Nat.find hex) ^ 2 * Q :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 hw 2) hQ.le
      _ < 1 := h

private lemma P4_nRes {β : ℝ} {Q : ℝ} {N : ℕ} (h1 : ∀ j, j < N → 1 ≤ emaW β j ^ 2 * Q)
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

/-- Geometric comparison of a series over the ages, split at the resolved-age count. -/
private lemma P4_sum_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Q : ℝ} (hQ : 0 < Q)
    (h : ℝ → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : ∀ x, 1 ≤ x → |h x| ≤ a / Real.sqrt x)
    (h2 : ∀ x, 0 ≤ x → x < 1 → |h x| ≤ b * Real.sqrt x) :
    Summable (fun j : ℕ => h (emaW β j ^ 2 * Q)) ∧
      |∑' j : ℕ, h (emaW β j ^ 2 * Q)| ≤ (a + b) / (1 - β) := by
  obtain ⟨N, hN1, hN2⟩ := P4_split hβ0 hβ1 hQ
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
      rw [hNj, P4_emaW_add] at hNq
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
      rw [P4_emaW_add]
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

private lemma P4_le_sqrt {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) : x ≤ Real.sqrt x := by
  have h1 : Real.sqrt x ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hx1.le
  have h2 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
  nlinarith [Real.sqrt_nonneg x]

private lemma P4_r_eq (β Q : ℝ) :
    rW (emaW β) Q = ∑' j : ℕ, (emaW β j ^ 2 * Q) * J (emaW β j ^ 2 * Q) := by
  unfold rW Fw
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  ring

private lemma P4_L_eq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {Q : ℝ} (hQ : 0 ≤ Q) :
    Real.sqrt Q * Lw (emaW β) Q = ∑' j : ℕ, Real.sqrt (emaW β j ^ 2 * Q) * J (emaW β j ^ 2 * Q) := by
  unfold Lw
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  have hw : 0 ≤ emaW β j := by
    unfold emaW
    exact mul_nonneg (by linarith) (pow_nonneg hβ0 j)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hw]
  ring

private lemma P4_k_eq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {Q : ℝ} (hQ : 0 < Q) :
    Q * deriv (rW (emaW β)) Q = ∑' j : ℕ, (emaW β j ^ 2 * Q) *
      ∫ g : ℝ, g ^ 2 / (1 + (emaW β j ^ 2 * Q) * g ^ 2) ^ 2 ∂(gaussianReal 0 1) := by
  rw [((lem_app_de_scalar_iii (P2_weightSeq hβ0 hβ1)).2.2.2.1 Q hQ).deriv, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  ring

private lemma P4_r_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Q : ℝ} (hQ : 0 < Q) :
    |rW (emaW β) Q - (nRes β Q : ℝ)| ≤ (Real.sqrt (Real.pi / 2) + 1) / (1 - β) := by
  obtain ⟨N, hN1, hN2⟩ := P4_split hβ0 hβ1 hQ
  rw [P4_nRes hN1 hN2, P4_r_eq]
  have hC0 : 0 ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
  have h1 : ∀ x : ℝ, 1 ≤ x →
      |x * J x - (if 1 ≤ x then (1 : ℝ) else 0)| ≤ Real.sqrt (Real.pi / 2) / Real.sqrt x := by
    intro x hx
    rw [if_pos hx]
    have hx0 : 0 < x := by linarith
    have hb := P4_f_bounds hx0.le
    have hc := P4_one_sub_le hx0
    have hp : 0 ≤ Real.sqrt (Real.pi / 2) / Real.sqrt x := by positivity
    rw [abs_le]
    constructor <;> linarith [hb.1, hb.2.1]
  have h2 : ∀ x : ℝ, 0 ≤ x → x < 1 →
      |x * J x - (if 1 ≤ x then (1 : ℝ) else 0)| ≤ 1 * Real.sqrt x := by
    intro x hx0 hx1
    rw [if_neg (not_le.2 hx1), sub_zero, one_mul]
    have hb := P4_f_bounds hx0
    rw [abs_of_nonneg hb.1]
    exact hb.2.2.trans (P4_le_sqrt hx0 hx1)
  obtain ⟨hs, hb⟩ := P4_sum_bound hβ0 hβ1 hQ
    (fun x => x * J x - (if 1 ≤ x then (1 : ℝ) else 0)) hC0 zero_le_one h1 h2
  have hind : ∀ j : ℕ, (if 1 ≤ emaW β j ^ 2 * Q then (1 : ℝ) else 0) = if j < N then 1 else 0 := by
    intro j
    by_cases hj : j < N
    · simp [hj, hN1 j hj]
    · have := hN2 j (not_lt.1 hj)
      simp [hj, not_le.2 this]
  have hnot : ∀ j, j ∉ Finset.range N → (if j < N then (1 : ℝ) else 0) = 0 := by
    intro j hj
    have : ¬ j < N := by simpa using hj
    simp [this]
  have hsi : Summable (fun j : ℕ => if j < N then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := Finset.range N) fun j hj => hnot j hj
  have hind_sum : ∑' j : ℕ, (if j < N then (1 : ℝ) else 0) = N := by
    rw [tsum_eq_sum (s := Finset.range N) fun j hj => hnot j hj]
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) (fun j hj => if_pos (Finset.mem_range.1 hj))]
    simp
  have hs' : Summable (fun j : ℕ => (emaW β j ^ 2 * Q) * J (emaW β j ^ 2 * Q) -
      (if 1 ≤ emaW β j ^ 2 * Q then (1 : ℝ) else 0)) := hs
  have hsum : ∑' j : ℕ, (emaW β j ^ 2 * Q) * J (emaW β j ^ 2 * Q) =
      ∑' j : ℕ, ((emaW β j ^ 2 * Q) * J (emaW β j ^ 2 * Q) -
        (if 1 ≤ emaW β j ^ 2 * Q then (1 : ℝ) else 0)) + N := by
    rw [← hind_sum, ← hs'.tsum_add hsi]
    refine tsum_congr fun j => ?_
    rw [hind j]
    ring
  rw [hsum, add_sub_cancel_right]
  exact hb

private lemma P4_L_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Q : ℝ} (hQ : 0 < Q) :
    Summable (fun j : ℕ => Real.sqrt (emaW β j ^ 2 * Q) * J (emaW β j ^ 2 * Q)) ∧
      Real.sqrt Q * Lw (emaW β) Q ≤ 2 / (1 - β) := by
  rw [P4_L_eq hβ0.le hβ1 hQ.le]
  have h1 : ∀ x : ℝ, 1 ≤ x → |Real.sqrt x * J x| ≤ 1 / Real.sqrt x := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hb := P4_f_bounds hx0.le
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    rw [abs_of_nonneg (mul_nonneg hs.le (P3_J_bounds hx0.le).1), le_div_iff₀ hs]
    have h2 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    nlinarith
  have h2 : ∀ x : ℝ, 0 ≤ x → x < 1 → |Real.sqrt x * J x| ≤ 1 * Real.sqrt x := by
    intro x hx0 hx1
    rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg x) (P3_J_bounds hx0).1), one_mul]
    exact mul_le_of_le_one_right (Real.sqrt_nonneg x) (P3_J_bounds hx0).2
  obtain ⟨hs, hb⟩ := P4_sum_bound hβ0 hβ1 hQ (fun x => Real.sqrt x * J x) zero_le_one zero_le_one h1 h2
  refine ⟨hs, ?_⟩
  have := (le_abs_self _).trans hb
  convert this using 2
  norm_num

private lemma P4_k_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Q : ℝ} (hQ : 0 < Q) :
    Summable (fun j : ℕ => (emaW β j ^ 2 * Q) *
      ∫ g : ℝ, g ^ 2 / (1 + (emaW β j ^ 2 * Q) * g ^ 2) ^ 2 ∂(gaussianReal 0 1)) ∧
    Q * deriv (rW (emaW β)) Q ≤ (Real.sqrt (Real.pi / 2) + 1) / (1 - β) := by
  rw [P4_k_eq hβ0.le hβ1 hQ]
  have hC0 : 0 ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
  have h1 : ∀ x : ℝ, 1 ≤ x →
      |x * ∫ g : ℝ, g ^ 2 / (1 + x * g ^ 2) ^ 2 ∂(gaussianReal 0 1)| ≤
        Real.sqrt (Real.pi / 2) / Real.sqrt x := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hk := P4_k_bounds hx0.le
    have hc := P4_one_sub_le hx0
    rw [abs_of_nonneg hk.1]
    linarith [hk.2.2]
  have h2 : ∀ x : ℝ, 0 ≤ x → x < 1 →
      |x * ∫ g : ℝ, g ^ 2 / (1 + x * g ^ 2) ^ 2 ∂(gaussianReal 0 1)| ≤ 1 * Real.sqrt x := by
    intro x hx0 hx1
    have hk := P4_k_bounds hx0
    have hb := P4_f_bounds hx0
    rw [abs_of_nonneg hk.1, one_mul]
    exact (hk.2.1.trans hb.2.2).trans (P4_le_sqrt hx0 hx1)
  obtain ⟨hs, hb⟩ := P4_sum_bound hβ0 hβ1 hQ
    (fun x => x * ∫ g : ℝ, g ^ 2 / (1 + x * g ^ 2) ^ 2 ∂(gaussianReal 0 1)) hC0 zero_le_one h1 h2
  exact ⟨hs, (le_abs_self _).trans hb⟩

private lemma P4_exists_j {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Q : ℝ} (hQ : 1 ≤ Q) :
    ∃ j : ℕ, (1 - β) ^ 2 ≤ emaW β j ^ 2 * Q ∧ emaW β j ^ 2 * Q * β ^ 2 ≤ 1 := by
  have hQ0 : 0 < Q := by linarith
  obtain ⟨N, hN1, hN2⟩ := P4_split hβ0 hβ1 hQ0
  have hβ2 : β ^ 2 ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
  have h1b : (1 - β) ^ 2 ≤ 1 := by nlinarith
  rcases N with _ | M
  · refine ⟨0, ?_, ?_⟩
    · have : emaW β 0 = 1 - β := by simp [emaW]
      rw [this]
      nlinarith [sq_nonneg (1 - β)]
    · have h := hN2 0 le_rfl
      nlinarith [sq_nonneg (emaW β 0), mul_nonneg (sq_nonneg (emaW β 0)) hQ0.le]
  · refine ⟨M, ?_, ?_⟩
    · exact h1b.trans (hN1 M (Nat.lt_succ_self M))
    · have h := hN2 (M + 1) le_rfl
      have e := P4_emaW_add β M 1
      rw [pow_one] at e
      rw [e] at h
      nlinarith

private lemma P4_lower_pts {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {x : ℝ}
    (hx1 : (1 - β) ^ 2 ≤ x) (hx2 : x * β ^ 2 ≤ 1) :
    (1 - β) * J (1 / β ^ 2) ≤ Real.sqrt x * J x ∧
    (1 - β) ^ 2 * J (1 / β ^ 2) ^ 2 ≤
      x * ∫ g : ℝ, g ^ 2 / (1 + x * g ^ 2) ^ 2 ∂(gaussianReal 0 1) := by
  have hb : 0 < 1 - β := by linarith
  have hx0 : 0 ≤ x := le_trans (sq_nonneg _) hx1
  have hβ2 : 0 < β ^ 2 := pow_pos hβ0 2
  have hxle : x ≤ 1 / β ^ 2 := by
    rw [le_div_iff₀ hβ2]; exact hx2
  have hJm := (lem_app_de_scalar_i.2.1).antitoneOn (Set.mem_Ici.2 hx0)
    (Set.mem_Ici.2 (by positivity : (0 : ℝ) ≤ 1 / β ^ 2)) hxle
  have hJpos : 0 < J (1 / β ^ 2) := (lem_app_de_scalar_i.2.2.1 _ (by positivity)).1
  have hsq : 1 - β ≤ Real.sqrt x := by
    calc 1 - β = Real.sqrt ((1 - β) ^ 2) := (Real.sqrt_sq hb.le).symm
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx1
  refine ⟨mul_le_mul hsq hJm hJpos.le (Real.sqrt_nonneg x), ?_⟩
  have hD := P4_D_ge hx0
  have h1 : J (1 / β ^ 2) ^ 2 ≤ J x ^ 2 := pow_le_pow_left₀ hJpos.le hJm 2
  calc (1 - β) ^ 2 * J (1 / β ^ 2) ^ 2 ≤ x * J (1 / β ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_right hx1 (sq_nonneg _)
    _ ≤ x * J x ^ 2 := mul_le_mul_of_nonneg_left h1 hx0
    _ ≤ _ := mul_le_mul_of_nonneg_left hD hx0

private lemma P4_lower {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Q : ℝ} (hQ : 1 ≤ Q) :
    (1 - β) * J (1 / β ^ 2) ≤ Real.sqrt Q * Lw (emaW β) Q ∧
    (1 - β) ^ 2 * J (1 / β ^ 2) ^ 2 ≤ Q * deriv (rW (emaW β)) Q := by
  have hQ0 : 0 < Q := by linarith
  obtain ⟨j, hj1, hj2⟩ := P4_exists_j hβ0 hβ1 hQ
  have hx0 : ∀ i : ℕ, 0 ≤ emaW β i ^ 2 * Q := fun i => mul_nonneg (sq_nonneg _) hQ0.le
  obtain ⟨hsL, -⟩ := P4_L_bound hβ0 hβ1 hQ0
  obtain ⟨hsk, -⟩ := P4_k_bound hβ0 hβ1 hQ0
  have hp := P4_lower_pts hβ0 hβ1 hj1 hj2
  constructor
  · rw [P4_L_eq hβ0.le hβ1 hQ0.le]
    exact hp.1.trans (hsL.le_tsum j fun i _ =>
      mul_nonneg (Real.sqrt_nonneg _) (P3_J_bounds (hx0 i)).1)
  · rw [P4_k_eq hβ0.le hβ1 hQ0]
    exact hp.2.trans (hsk.le_tsum j fun i _ =>
      mul_nonneg (hx0 i) (integral_nonneg fun g =>
        div_nonneg (sq_nonneg g) (pow_nonneg (P4_den_pos (hx0 i) g).le 2)))

/-- `lem:app-pl-weights`(iii), the two-sided bounds for `Q ≥ 1`, snapshot `cr-2026-10-23`.
The constants are existential, depending on `β` only.
LaTeX (`sections/06-power-law/section.tex` l.223–244):
\begin{lemma}[Weight functions]\label{lem:app-pl-weights}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item For $q\ge0$,
\[
\begin{gathered}
\Fw(q)=\sw2-3\sw4q+R_F(q),\quad 0\le R_F\le15\sw6q^2,\\
\Lw(q)=1-3\sw3q+R_L(q),\quad 0\le R_L\le15\sw5q^2 .
\end{gathered}
\]
Consequently $r_\bmom(q)=\sw2q+O(q^2)$, and $Q_m\sim m/\sw2$ and $E(m)\sim m$ as $m\downarrow0$.
\item For $q>0$, $\abs{q\Fw'(q)}\le\Fw(q)$ and $\abs{q\Lw'(q)}\le\Lw(q)$. For $m>0$, $E(m)\le m$.
\item There are $0<c_\bmom\le C_\bmom<\infty$ such that, for $Q\ge1$,
\[
\abs{r_\bmom(Q)-n(Q)}\le C_\bmom,\qquad
c_\bmom\le\sqrt Q\,\Lw(Q)\le C_\bmom,\qquad
c_\bmom\le Q\,r_\bmom'(Q)\le C_\bmom .
\]
Consequently $E(m)\asymp\min(m,1)$ for all $m>0$, and
$\abs{\log Q_m-2\abs{\log\bmom}\,m}\le C_\bmom$ for $m\ge1$.
\end{enumerate}
\end{lemma} -/
theorem lem_app_pl_weights_iii {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ Q : ℝ, 1 ≤ Q →
      |rW (emaW β) Q - (nRes β Q : ℝ)| ≤ C ∧
      c ≤ Real.sqrt Q * Lw (emaW β) Q ∧ Real.sqrt Q * Lw (emaW β) Q ≤ C ∧
      c ≤ Q * deriv (rW (emaW β)) Q ∧ Q * deriv (rW (emaW β)) Q ≤ C := by
  have hJpos : 0 < J (1 / β ^ 2) := (lem_app_de_scalar_i.2.2.1 _ (by positivity)).1
  have hc1 : 0 < (1 - β) * J (1 / β ^ 2) := mul_pos (by linarith) hJpos
  have hc2 : 0 < (1 - β) ^ 2 * J (1 / β ^ 2) ^ 2 :=
    mul_pos (pow_pos (by linarith) 2) (pow_pos hJpos 2)
  refine ⟨min ((1 - β) * J (1 / β ^ 2)) ((1 - β) ^ 2 * J (1 / β ^ 2) ^ 2),
    max (max ((Real.sqrt (Real.pi / 2) + 1) / (1 - β)) (2 / (1 - β)))
      (min ((1 - β) * J (1 / β ^ 2)) ((1 - β) ^ 2 * J (1 / β ^ 2) ^ 2)),
    lt_min hc1 hc2, le_max_right _ _, fun Q hQ => ?_⟩
  have hQ0 : 0 < Q := by linarith
  obtain ⟨hl1, hl2⟩ := P4_lower hβ0 hβ1 hQ
  exact ⟨(P4_r_bound hβ0 hβ1 hQ0).trans ((le_max_left _ _).trans (le_max_left _ _)),
    (min_le_left _ _).trans hl1,
    (P4_L_bound hβ0 hβ1 hQ0).2.trans ((le_max_right _ _).trans (le_max_left _ _)),
    (min_le_right _ _).trans hl2,
    (P4_k_bound hβ0 hβ1 hQ0).2.trans ((le_max_left _ _).trans (le_max_left _ _))⟩

/-! ### Helpers for `lem_app_pl_weights_iii_E` and `lem_app_pl_weights_iii_logQ` -/

private lemma P4_Qm {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    0 < Qm β m ∧ rW (emaW β) (Qm β m) = m := by
  have hex : ∃ a ∈ Ioi (0:ℝ), rW (emaW β) a = m := P3_range hβ0 hβ1 hm
  exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩

private lemma P4_f_summable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Q : ℝ} (hQ : 0 ≤ Q) :
    Summable (fun j : ℕ => (emaW β j ^ 2 * Q) * J (emaW β j ^ 2 * Q)) := by
  have hx0 : ∀ i : ℕ, 0 ≤ emaW β i ^ 2 * Q := fun i => mul_nonneg (sq_nonneg _) hQ
  have hw : Summable (fun j => Q * emaW β j) := ((P2_weightSeq hβ0.le hβ1).2.1).mul_left Q
  refine Summable.of_nonneg_of_le (fun j => (P4_f_bounds (hx0 j)).1) (fun j => ?_) hw
  calc (emaW β j ^ 2 * Q) * J (emaW β j ^ 2 * Q) ≤ emaW β j ^ 2 * Q := (P4_f_bounds (hx0 j)).2.2
    _ ≤ Q * emaW β j := by
      have h1 := P4_emaW_le_one hβ0.le hβ1 j
      have h2 := (P4_emaW_pos hβ0 hβ1 j).le
      nlinarith [mul_nonneg (mul_nonneg hQ h2) (sub_nonneg.2 h1)]

private lemma P4_r_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Q : ℝ} (hQ : 0 ≤ Q) :
    rW (emaW β) Q ≤ Q := by
  have hx0 : ∀ i : ℕ, 0 ≤ emaW β i ^ 2 * Q := fun i => mul_nonneg (sq_nonneg _) hQ
  have hw : Summable (fun j => Q * emaW β j) := ((P2_weightSeq hβ0.le hβ1).2.1).mul_left Q
  rw [P4_r_eq]
  calc ∑' j : ℕ, (emaW β j ^ 2 * Q) * J (emaW β j ^ 2 * Q) ≤ ∑' j : ℕ, Q * emaW β j := by
        refine Summable.tsum_le_tsum (fun j => ?_) (P4_f_summable hβ0 hβ1 hQ) hw
        calc (emaW β j ^ 2 * Q) * J (emaW β j ^ 2 * Q) ≤ emaW β j ^ 2 * Q :=
              (P4_f_bounds (hx0 j)).2.2
          _ ≤ Q * emaW β j := by
            have h1 := P4_emaW_le_one hβ0.le hβ1 j
            have h2 := (P4_emaW_pos hβ0 hβ1 j).le
            nlinarith [mul_nonneg (mul_nonneg hQ h2) (sub_nonneg.2 h1)]
    _ = Q := by rw [tsum_mul_left, tsum_emaW hβ0.le hβ1, mul_one]

private lemma P4_Qm_ge {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 1 ≤ m) :
    1 ≤ Qm β m := by
  obtain ⟨hq, hr⟩ := P4_Qm hβ0 hβ1 (by linarith : (0 : ℝ) < m)
  have := P4_r_le hβ0 hβ1 hq.le
  rw [hr] at this
  linarith

private lemma P4_k_lower {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Q X : ℝ} (hQ : 0 < Q)
    (hQX : Q ≤ X) :
    J X * rW (emaW β) Q ≤ Q * deriv (rW (emaW β)) Q := by
  have hx0 : ∀ i : ℕ, 0 ≤ emaW β i ^ 2 * Q := fun i => mul_nonneg (sq_nonneg _) hQ.le
  have hJX : 0 ≤ J X := (P3_J_bounds (hQ.le.trans hQX)).1
  obtain ⟨hsk, -⟩ := P4_k_bound hβ0 hβ1 hQ
  rw [P4_k_eq hβ0.le hβ1 hQ, P4_r_eq, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun j => ?_) ((P4_f_summable hβ0 hβ1 hQ.le).mul_left _) hsk
  have hxX : emaW β j ^ 2 * Q ≤ X := by
    have h1 := P4_emaW_le_one hβ0.le hβ1 j
    have h2 := (P4_emaW_pos hβ0 hβ1 j).le
    have : emaW β j ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hJ := (lem_app_de_scalar_i.2.1).antitoneOn (Set.mem_Ici.2 (hx0 j))
    (Set.mem_Ici.2 (hQ.le.trans hQX)) hxX
  have hD := P4_D_ge (hx0 j)
  have hJj := (P3_J_bounds (hx0 j)).1
  calc J X * ((emaW β j ^ 2 * Q) * J (emaW β j ^ 2 * Q))
      = (emaW β j ^ 2 * Q) * (J X * J (emaW β j ^ 2 * Q)) := by ring
    _ ≤ (emaW β j ^ 2 * Q) * J (emaW β j ^ 2 * Q) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (hx0 j)
        nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hD (hx0 j)

private lemma P4_logw {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Q : ℝ} (hQ : 0 < Q) (n : ℕ) :
    Real.log (emaW β n ^ 2 * Q) =
      Real.log Q + 2 * Real.log (1 - β) + 2 * (n : ℝ) * Real.log β := by
  have hb : 0 < 1 - β := by linarith
  have e : emaW β n ^ 2 * Q = (1 - β) ^ 2 * (β ^ n) ^ 2 * Q := by unfold emaW; ring
  rw [e, Real.log_mul (mul_pos (pow_pos hb 2) (pow_pos (pow_pos hβ0 n) 2)).ne' hQ.ne',
    Real.log_mul (pow_pos hb 2).ne' (pow_pos (pow_pos hβ0 n) 2).ne', Real.log_pow, Real.log_pow,
    Real.log_pow]
  push_cast
  ring

/-- `lem:app-pl-weights`(iii), consequence `E(m) ≍ min(m,1)` for all `m > 0`, snapshot
`cr-2026-10-23`. LaTeX (`sections/06-power-law/section.tex` l.223–244):
\begin{lemma}[Weight functions]\label{lem:app-pl-weights}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item For $q\ge0$,
\[
\begin{gathered}
\Fw(q)=\sw2-3\sw4q+R_F(q),\quad 0\le R_F\le15\sw6q^2,\\
\Lw(q)=1-3\sw3q+R_L(q),\quad 0\le R_L\le15\sw5q^2 .
\end{gathered}
\]
Consequently $r_\bmom(q)=\sw2q+O(q^2)$, and $Q_m\sim m/\sw2$ and $E(m)\sim m$ as $m\downarrow0$.
\item For $q>0$, $\abs{q\Fw'(q)}\le\Fw(q)$ and $\abs{q\Lw'(q)}\le\Lw(q)$. For $m>0$, $E(m)\le m$.
\item There are $0<c_\bmom\le C_\bmom<\infty$ such that, for $Q\ge1$,
\[
\abs{r_\bmom(Q)-n(Q)}\le C_\bmom,\qquad
c_\bmom\le\sqrt Q\,\Lw(Q)\le C_\bmom,\qquad
c_\bmom\le Q\,r_\bmom'(Q)\le C_\bmom .
\]
Consequently $E(m)\asymp\min(m,1)$ for all $m>0$, and
$\abs{\log Q_m-2\abs{\log\bmom}\,m}\le C_\bmom$ for $m\ge1$.
\end{enumerate}
\end{lemma} -/
theorem lem_app_pl_weights_iii_E {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ m : ℝ, 0 < m →
      c * min m 1 ≤ Efun β m ∧ Efun β m ≤ C * min m 1 := by
  obtain ⟨c0, C0, hc0, hcC, h⟩ := lem_app_pl_weights_iii hβ0 hβ1
  obtain ⟨hX0, hX1⟩ := P4_Qm hβ0 hβ1 (zero_lt_one : (0 : ℝ) < 1)
  have hJX : 0 < J (Qm β 1) := (lem_app_de_scalar_i.2.2.1 _ hX0.le).1
  refine ⟨min c0 (J (Qm β 1)), max C0 1, lt_min hc0 hJX,
    (min_le_left _ _).trans (hcC.trans (le_max_left _ _)), fun m hm => ?_⟩
  obtain ⟨hq, hr⟩ := P4_Qm hβ0 hβ1 hm
  by_cases hm1 : 1 ≤ m
  · rw [min_eq_right hm1, mul_one, mul_one]
    have hE := h (Qm β m) (P4_Qm_ge hβ0 hβ1 hm1)
    exact ⟨(min_le_left _ _).trans hE.2.2.2.1, hE.2.2.2.2.trans (le_max_left _ _)⟩
  · have hm1' : m ≤ 1 := (not_le.1 hm1).le
    rw [min_eq_left hm1']
    refine ⟨?_, ?_⟩
    · have hQX : Qm β m ≤ Qm β 1 := by
        by_contra hc
        have hlt := (lem_app_de_scalar_iii (P2_weightSeq hβ0.le hβ1)).2.1
          (Set.mem_Ici.2 hX0.le) (Set.mem_Ici.2 hq.le) (not_le.1 hc)
        rw [hX1, hr] at hlt
        linarith
      have h1 := P4_k_lower hβ0 hβ1 hq hQX
      rw [hr] at h1
      calc min c0 (J (Qm β 1)) * m ≤ J (Qm β 1) * m :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hm.le
        _ ≤ Efun β m := h1
    · have := lem_app_pl_weights_ii_E hβ0 hβ1 m hm
      calc Efun β m ≤ m := this
        _ ≤ max C0 1 * m := by
          have : (1 : ℝ) ≤ max C0 1 := le_max_right _ _
          nlinarith

/-- `lem:app-pl-weights`(iii), consequence `|log Q_m - 2|log β| m| ≤ C_β` for `m ≥ 1`, snapshot
`cr-2026-10-23`. LaTeX (`sections/06-power-law/section.tex` l.223–244):
\begin{lemma}[Weight functions]\label{lem:app-pl-weights}
\leavevmode
\begin{enumerate}[label=(\roman*)]
\item For $q\ge0$,
\[
\begin{gathered}
\Fw(q)=\sw2-3\sw4q+R_F(q),\quad 0\le R_F\le15\sw6q^2,\\
\Lw(q)=1-3\sw3q+R_L(q),\quad 0\le R_L\le15\sw5q^2 .
\end{gathered}
\]
Consequently $r_\bmom(q)=\sw2q+O(q^2)$, and $Q_m\sim m/\sw2$ and $E(m)\sim m$ as $m\downarrow0$.
\item For $q>0$, $\abs{q\Fw'(q)}\le\Fw(q)$ and $\abs{q\Lw'(q)}\le\Lw(q)$. For $m>0$, $E(m)\le m$.
\item There are $0<c_\bmom\le C_\bmom<\infty$ such that, for $Q\ge1$,
\[
\abs{r_\bmom(Q)-n(Q)}\le C_\bmom,\qquad
c_\bmom\le\sqrt Q\,\Lw(Q)\le C_\bmom,\qquad
c_\bmom\le Q\,r_\bmom'(Q)\le C_\bmom .
\]
Consequently $E(m)\asymp\min(m,1)$ for all $m>0$, and
$\abs{\log Q_m-2\abs{\log\bmom}\,m}\le C_\bmom$ for $m\ge1$.
\end{enumerate}
\end{lemma} -/
theorem lem_app_pl_weights_iii_logQ {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C : ℝ, ∀ m : ℝ, 1 ≤ m →
      |Real.log (Qm β m) - 2 * |Real.log β| * m| ≤ C := by
  obtain ⟨c, C, hc, hcC, h⟩ := lem_app_pl_weights_iii hβ0 hβ1
  have hL : |Real.log β| = -Real.log β := abs_of_neg (Real.log_neg hβ0 hβ1)
  have hLp : 0 < -Real.log β := neg_pos.2 (Real.log_neg hβ0 hβ1)
  refine ⟨|2 * Real.log (1 - β)| + 2 * (-Real.log β) + 2 * (-Real.log β) * C, fun m hm => ?_⟩
  have hm0 : (0 : ℝ) < m := by linarith
  obtain ⟨hq, hr⟩ := P4_Qm hβ0 hβ1 hm0
  have hQ1 := P4_Qm_ge hβ0 hβ1 hm
  have hrn := (h (Qm β m) hQ1).1
  rw [hr] at hrn
  obtain ⟨N, hN1, hN2⟩ := P4_split hβ0 hβ1 hq
  rw [P4_nRes hN1 hN2] at hrn
  have hlogQ : 0 ≤ Real.log (Qm β m) := Real.log_nonneg hQ1
  have hw0 : ∀ n : ℕ, 0 < emaW β n ^ 2 * Qm β m := fun n =>
    mul_pos (pow_pos (P4_emaW_pos hβ0 hβ1 n) 2) hq
  have hA := neg_abs_le (2 * Real.log (1 - β))
  have hK : |Real.log (Qm β m) - 2 * (-Real.log β) * N| ≤
      |2 * Real.log (1 - β)| + 2 * (-Real.log β) := by
    rcases N with _ | M
    · have h2 := Real.log_neg (hw0 0) (hN2 0 le_rfl)
      rw [P4_logw hβ0 hβ1 hq] at h2
      simp only [Nat.cast_zero, mul_zero, add_zero] at h2
      rw [abs_le]
      constructor <;> push_cast <;> nlinarith [le_abs_self (2 * Real.log (1 - β))]
    · have h1 := Real.log_nonneg (hN1 M (Nat.lt_succ_self M))
      have h2 := Real.log_neg (hw0 (M + 1)) (hN2 (M + 1) le_rfl)
      rw [P4_logw hβ0 hβ1 hq] at h1 h2
      push_cast at h2 ⊢
      rw [abs_le]
      constructor <;> nlinarith [le_abs_self (2 * Real.log (1 - β))]
  rw [hL]
  have e : Real.log (Qm β m) - 2 * (-Real.log β) * m =
      (Real.log (Qm β m) - 2 * (-Real.log β) * N) + 2 * (-Real.log β) * ((N : ℝ) - m) := by ring
  rw [e]
  have h3 : |2 * (-Real.log β) * ((N : ℝ) - m)| ≤ 2 * (-Real.log β) * C := by
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 2 * (-Real.log β)), abs_sub_comm]
    exact mul_le_mul_of_nonneg_left hrn (by linarith)
  have := abs_add_le (Real.log (Qm β m) - 2 * (-Real.log β) * N) (2 * (-Real.log β) * ((N : ℝ) - m))
  linarith

/-! ### Helpers for `lem_app_pl_average_i` (fully proved) -/

private lemma P5_Lw_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ} (hq : 0 < q) :
    0 < Lw (emaW β) q := by
  have hJ : ∀ j : ℕ, 0 < J (emaW β j ^ 2 * q) ∧ J (emaW β j ^ 2 * q) ≤ 1 := fun j =>
    lem_app_de_scalar_i.2.2.1 _ (mul_nonneg (sq_nonneg _) hq.le)
  have hs : Summable (fun j : ℕ => emaW β j * J (emaW β j ^ 2 * q)) :=
    Summable.of_nonneg_of_le
      (fun j => mul_nonneg (P4_emaW_pos hβ0 hβ1 j).le (hJ j).1.le)
      (fun j => mul_le_of_le_one_right (P4_emaW_pos hβ0 hβ1 j).le (hJ j).2)
      (P2_weightSeq hβ0.le hβ1).2.1
  unfold Lw
  exact hs.tsum_pos (fun j => mul_nonneg (P4_emaW_pos hβ0 hβ1 j).le (hJ j).1.le) 0
    (mul_pos (P4_emaW_pos hβ0 hβ1 0) (hJ 0).1)

private lemma P5_Qm_ge {β m0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hm0 : 0 < m0) {m : ℝ}
    (hm : m0 ≤ m) : Qm β m0 ≤ Qm β m := by
  obtain ⟨ha, hra⟩ := P4_Qm hβ0 hβ1 hm0
  obtain ⟨hq, hr⟩ := P4_Qm hβ0 hβ1 (lt_of_lt_of_le hm0 hm)
  by_contra hc
  replace hc := lt_of_not_ge hc
  have hlt := (lem_app_de_scalar_iii (P2_weightSeq hβ0.le hβ1)).2.1
    (Set.mem_Ici.2 hq.le) (Set.mem_Ici.2 ha.le) hc
  rw [hr, hra] at hlt
  linarith

private lemma P5_f_bounds {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {a : ℝ} (ha : 0 < a) :
    ∃ lo hi : ℝ, 0 < lo ∧ ∀ q : ℝ, a ≤ q →
      lo ≤ Real.sqrt q * Lw (emaW β) q ∧ Real.sqrt q * Lw (emaW β) q ≤ hi := by
  have hcont : ContinuousOn (fun q : ℝ => Real.sqrt q * Lw (emaW β) q) (Icc a (max a 1)) := by
    refine Real.continuous_sqrt.continuousOn.mul
      ((lem_app_de_scalar_ii (P2_weightSeq hβ0.le hβ1)).2.2.2.1.mono ?_)
    intro q hq
    exact Set.mem_Ici.2 (ha.le.trans hq.1)
  obtain ⟨x, hx, hxmin⟩ := (isCompact_Icc (a := a) (b := max a 1)).exists_isMinOn
    (nonempty_Icc.2 (le_max_left a 1)) hcont
  obtain ⟨y, hy, hymax⟩ := (isCompact_Icc (a := a) (b := max a 1)).exists_isMaxOn
    (nonempty_Icc.2 (le_max_left a 1)) hcont
  obtain ⟨c, C, hc, -, h⟩ := lem_app_pl_weights_iii hβ0 hβ1
  have hxpos : 0 < Real.sqrt x * Lw (emaW β) x :=
    mul_pos (Real.sqrt_pos.2 (lt_of_lt_of_le ha hx.1)) (P5_Lw_pos hβ0 hβ1 (lt_of_lt_of_le ha hx.1))
  refine ⟨min (Real.sqrt x * Lw (emaW β) x) c, max (Real.sqrt y * Lw (emaW β) y) C,
    lt_min hxpos hc, fun q hq => ?_⟩
  rcases le_total q 1 with h1 | h1
  · have hqK : q ∈ Icc a (max a 1) := ⟨hq, h1.trans (le_max_right a 1)⟩
    have hmin : Real.sqrt x * Lw (emaW β) x ≤ Real.sqrt q * Lw (emaW β) q :=
      isMinOn_iff.1 hxmin q hqK
    have hmax : Real.sqrt q * Lw (emaW β) q ≤ Real.sqrt y * Lw (emaW β) y :=
      isMaxOn_iff.1 hymax q hqK
    exact ⟨(min_le_left _ _).trans hmin, hmax.trans (le_max_left _ _)⟩
  · have hh := h q h1
    exact ⟨(min_le_right _ _).trans hh.2.1, hh.2.2.1.trans (le_max_right _ _)⟩

/-- `lem:app-pl-average`(i), snapshot `cr-2026-10-23`: `𝒜 ≍ 1` on `[m₀,∞)` with constants
depending on `(β, m₀)`.
LaTeX (`sections/06-power-law/section.tex` l.309–320):
\begin{lemma}[Averaging in the participation coordinate]\label{lem:app-pl-average}
Put $\mathcal A(m)\defeq\sqrt{Q_m}\,\Lw(Q_m)/E(m)$ for $m>0$. For every $m_0>0$,
$\mathcal A\asymp1$ on $[m_0,\infty)$ with constants depending on $(\bmom,m_0)$, and
\begin{equation}\label{eqn:app-pl-average}
\sup_{t\ge m_0}\Big|\int_{m_0}^t\big(\mathcal A(m)-\sqrt{2\pi}\big)\,\dif m\Big|\le C_{\bmom,m_0}.
\end{equation}
Consequently, for every $[a,c]\subset[m_0,\infty)$ and every continuously
differentiable $W$ on $[a,c]$,
\begin{equation}\label{eqn:app-pl-average-ibp}
\Big|\int_a^c\big(\mathcal A(m)-\sqrt{2\pi}\big)W(m)\,\dif m\Big|\le C_{\bmom,m_0}\Big(\abs{W(a)}+\abs{W(c)}+\int_a^c\abs{W'(m)}\,\dif m\Big).
\end{equation}
\end{lemma} -/
theorem lem_app_pl_average_i {β m0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hm0 : 0 < m0) :
    ∃ c C : ℝ, 0 < c ∧ ∀ m : ℝ, m0 ≤ m → c ≤ Aav β m ∧ Aav β m ≤ C := by
  obtain ⟨hmQ, -⟩ := P4_Qm hβ0 hβ1 hm0
  obtain ⟨lo, hi, hlo, hf⟩ := P5_f_bounds hβ0 hβ1 hmQ
  obtain ⟨cE, CE, hcE, hcCE, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  have hCE : 0 < CE := lt_of_lt_of_le hcE hcCE
  have hμ : 0 < min m0 1 := lt_min hm0 one_pos
  refine ⟨lo / CE, hi / (cE * min m0 1), div_pos hlo hCE, fun m hm => ?_⟩
  have hm' : 0 < m := lt_of_lt_of_le hm0 hm
  have hN := hf (Qm β m) (P5_Qm_ge hβ0 hβ1 hm0 hm)
  obtain ⟨hE1, hE2⟩ := hE m hm'
  have hminpos : 0 < min m 1 := lt_min hm' one_pos
  have hminle : min m 1 ≤ 1 := min_le_right _ _
  have hminge : min m0 1 ≤ min m 1 := le_min ((min_le_left _ _).trans hm) (min_le_right _ _)
  have hEpos : 0 < Efun β m := lt_of_lt_of_le (mul_pos hcE hminpos) hE1
  have hEE : Efun β m ≤ CE := hE2.trans (mul_le_of_le_one_right hCE.le hminle)
  have hEge : cE * min m0 1 ≤ Efun β m := (mul_le_mul_of_nonneg_left hminge hcE.le).trans hE1
  unfold Aav
  constructor
  · rw [div_le_div_iff₀ hCE hEpos]
    have h1 : lo * Efun β m ≤ lo * CE := mul_le_mul_of_nonneg_left hEE hlo.le
    have h2 : lo * CE ≤ Real.sqrt (Qm β m) * Lw (emaW β) (Qm β m) * CE :=
      mul_le_mul_of_nonneg_right hN.1 hCE.le
    linarith
  · rw [div_le_div_iff₀ hEpos (mul_pos hcE hμ)]
    exact mul_le_mul hN.2 hEge (mul_pos hcE hμ).le (hlo.trans_le (hN.1.trans hN.2)).le

/-! ### Helpers for `lem_app_pl_average_ii` (fully proved) -/


private lemma P5_arctan_le {u : ℝ} (hu : 0 ≤ u) : Real.arctan u ≤ u := by
  have h0 : 0 ≤ Real.arctan u := Real.arctan_nonneg.2 hu
  have h1 := Real.arctan_lt_pi_div_two u
  have := Real.le_tan h0 h1
  rwa [Real.tan_arctan] at this

private lemma P5_abs_int : Integrable (fun g : ℝ => |g|) (gaussianReal 0 1) := by
  have := (Muon.Foundations.gaussian_integrable_pow 1)
  simpa using this.abs

private lemma P5_H_int {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun g : ℝ => 2 * |g| * Real.arctan (|g| * s)) (gaussianReal 0 1) := by
  refine Integrable.mono' (P5_abs_int.const_mul Real.pi) ?_ (Filter.Eventually.of_forall fun g => ?_)
  · exact (by fun_prop : Continuous fun g : ℝ => 2 * |g| * Real.arctan (|g| * s)).aestronglyMeasurable
  · have h0 : 0 ≤ Real.arctan (|g| * s) := Real.arctan_nonneg.2 (mul_nonneg (abs_nonneg _) hs)
    have h1 := Real.arctan_lt_pi_div_two (|g| * s)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [abs_nonneg g]

private lemma P5_H_bounds {s : ℝ} (hs : 0 < s) :
    0 ≤ ∫ g, 2 * |g| * Real.arctan (|g| * s) ∂(gaussianReal 0 1) ∧
    ∫ g, 2 * |g| * Real.arctan (|g| * s) ∂(gaussianReal 0 1) ≤ 2 * s ∧
    ∫ g, 2 * |g| * Real.arctan (|g| * s) ∂(gaussianReal 0 1) ≤ Real.sqrt (2 * Real.pi) ∧
    Real.sqrt (2 * Real.pi) - 2 / s ≤ ∫ g, 2 * |g| * Real.arctan (|g| * s) ∂(gaussianReal 0 1) := by
  have hI := P5_H_int hs.le
  have hE : Real.pi * ∫ g, |g| ∂(gaussianReal 0 1) = Real.sqrt (2 * Real.pi) := by
    rw [Muon.Foundations.gaussian_abs_moment, Real.sqrt_div (by norm_num), Real.sqrt_mul (by norm_num)]
    have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
    have h2 : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
    have hs2 : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    nlinarith [h2]
  refine ⟨integral_nonneg fun g => ?_, ?_, ?_, ?_⟩
  · exact mul_nonneg (by positivity) (Real.arctan_nonneg.2 (mul_nonneg (abs_nonneg _) hs.le))
  · have : ∫ g, 2 * |g| * Real.arctan (|g| * s) ∂(gaussianReal 0 1) ≤ ∫ g, 2 * s * g ^ 2 ∂(gaussianReal 0 1) :=
      integral_mono hI ((Muon.Foundations.gaussian_integrable_pow 2).const_mul _) (fun g => by
        have h1 := P5_arctan_le (mul_nonneg (abs_nonneg g) hs.le)
        have : g ^ 2 = |g| ^ 2 := (sq_abs g).symm
        show 2 * |g| * Real.arctan (|g| * s) ≤ 2 * s * g ^ 2
        rw [this]
        nlinarith [abs_nonneg g])
    rw [integral_const_mul, Muon.Foundations.gaussian_moment_two] at this
    linarith
  · have : ∫ g, 2 * |g| * Real.arctan (|g| * s) ∂(gaussianReal 0 1) ≤ ∫ g, Real.pi * |g| ∂(gaussianReal 0 1) :=
      integral_mono hI (P5_abs_int.const_mul _) (fun g => by
        have h1 := Real.arctan_lt_pi_div_two (|g| * s)
        show 2 * |g| * Real.arctan (|g| * s) ≤ Real.pi * |g|
        nlinarith [abs_nonneg g])
    rw [integral_const_mul, hE] at this
    exact this
  · have : ∫ g, (Real.pi * |g| - 2 / s) ∂(gaussianReal 0 1) ≤ ∫ g, 2 * |g| * Real.arctan (|g| * s) ∂(gaussianReal 0 1) := by
      refine integral_mono ((P5_abs_int.const_mul _).sub (integrable_const _)) hI (fun g => ?_)
      show Real.pi * |g| - 2 / s ≤ 2 * |g| * Real.arctan (|g| * s)
      rcases (abs_nonneg g).eq_or_lt with h | h
      · rw [← h]; simp; positivity
      · have hu : 0 < |g| * s := mul_pos h hs
        have h1 := Real.arctan_inv_of_pos hu
        have h2 := P5_arctan_le (inv_nonneg.2 hu.le)
        have h3 : 2 * |g| * (|g| * s)⁻¹ = 2 / s := by field_simp
        nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 2 * |g|)]
    rw [integral_sub (P5_abs_int.const_mul _) (integrable_const _), integral_const_mul, hE] at this
    simpa using this

private lemma P5_inner {w a b g : ℝ} (hw : 0 < w) (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, (Real.sqrt x)⁻¹ * (w * (g ^ 2 / (1 + w ^ 2 * x * g ^ 2))) =
      2 * |g| * Real.arctan (|g| * (w * Real.sqrt b)) - 2 * |g| * Real.arctan (|g| * (w * Real.sqrt a)) := by
  have hd : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun x : ℝ => 2 * |g| * Real.arctan (|g| * (w * Real.sqrt x)))
      ((Real.sqrt x)⁻¹ * (w * (g ^ 2 / (1 + w ^ 2 * x * g ^ 2)))) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have hsq : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    have h1 : HasDerivAt (fun x : ℝ => |g| * (w * Real.sqrt x)) (|g| * (w * (1 / (2 * Real.sqrt x)))) x := by
      have := (Real.hasDerivAt_sqrt hx0.ne')
      exact (this.const_mul w).const_mul |g|
    have h2 := (h1.arctan).const_mul (2 * |g|)
    convert h2 using 1
    have hss : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
    have hg2 : |g| ^ 2 = g ^ 2 := sq_abs g
    have hden : 0 < 1 + (|g| * (w * Real.sqrt x)) ^ 2 := by positivity
    have e : 1 + (|g| * (w * Real.sqrt x)) ^ 2 = 1 + w ^ 2 * x * g ^ 2 := by
      rw [mul_pow, mul_pow, hss, hg2]; ring
    rw [e] at hden ⊢
    field_simp
    rw [← hg2]
  have hc : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹ * (w * (g ^ 2 / (1 + w ^ 2 * x * g ^ 2)))) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have hsq : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx0).ne'
    have hden : 1 + w ^ 2 * x * g ^ 2 ≠ 0 := by positivity
    refine ContinuousAt.continuousWithinAt ?_
    fun_prop (disch := assumption)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)

private lemma P5_term_int {w a b : ℝ} (hw : 0 < w) (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, (Real.sqrt x)⁻¹ * (w * J (w ^ 2 * x)) =
      (∫ g, 2 * |g| * Real.arctan (|g| * (w * Real.sqrt b)) ∂(gaussianReal 0 1)) -
      ∫ g, 2 * |g| * Real.arctan (|g| * (w * Real.sqrt a)) ∂(gaussianReal 0 1) := by
  have h1 : ∀ x : ℝ, (Real.sqrt x)⁻¹ * (w * J (w ^ 2 * x)) =
      ∫ g, (Real.sqrt x)⁻¹ * (w * (g ^ 2 / (1 + w ^ 2 * x * g ^ 2))) ∂(gaussianReal 0 1) := by
    intro x
    unfold J
    rw [← integral_const_mul, ← integral_const_mul]
  simp_rw [h1]
  rw [intervalIntegral.integral_of_le hab]
  rw [integral_integral_swap]
  · have : ∀ g : ℝ, ∫ x in Set.Ioc a b, (Real.sqrt x)⁻¹ * (w * (g ^ 2 / (1 + w ^ 2 * x * g ^ 2))) =
        2 * |g| * Real.arctan (|g| * (w * Real.sqrt b)) - 2 * |g| * Real.arctan (|g| * (w * Real.sqrt a)) := by
      intro g
      rw [← intervalIntegral.integral_of_le hab]
      exact P5_inner hw ha hab
    simp_rw [this]
    rw [integral_sub (P5_H_int (by positivity)) (P5_H_int (by positivity))]
  · have hf : IntegrableOn (fun x : ℝ => (Real.sqrt x)⁻¹) (Set.Ioc a b) := by
      have : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (Set.Icc a b) := by
        intro x hx
        have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
        refine ContinuousAt.continuousWithinAt ?_
        exact (Real.continuous_sqrt.continuousAt).inv₀ (Real.sqrt_pos.2 hx0).ne'
      exact (this.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    have hg := (Muon.Foundations.gaussian_integrable_pow 2).const_mul w
    have hprod := Integrable.mul_prod (μ := volume.restrict (Set.Ioc a b)) (ν := gaussianReal 0 1) hf hg
    refine Integrable.mono' hprod ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact Measurable.aestronglyMeasurable (by fun_prop)
    · obtain ⟨x, g⟩ := p
      simp only [Function.uncurry_apply_pair]
      rcases lt_or_ge x 0 with hx | hx
      · simp [Real.sqrt_eq_zero_of_nonpos hx.le]
      · have hden : 1 ≤ 1 + w ^ 2 * x * g ^ 2 := by nlinarith [mul_nonneg (mul_nonneg (sq_nonneg w) hx) (sq_nonneg g)]
        have hq : g ^ 2 / (1 + w ^ 2 * x * g ^ 2) ≤ g ^ 2 := div_le_self (sq_nonneg g) hden
        have hq0 : 0 ≤ g ^ 2 / (1 + w ^ 2 * x * g ^ 2) := by positivity
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have hs : 0 ≤ (Real.sqrt x)⁻¹ := by positivity
        calc (Real.sqrt x)⁻¹ * (w * (g ^ 2 / (1 + w ^ 2 * x * g ^ 2))) ≤ (Real.sqrt x)⁻¹ * (w * g ^ 2) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq hw.le) hs
          _ = _ := rfl

private lemma P5_H_bounds0 {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ ∫ g, 2 * |g| * Real.arctan (|g| * s) ∂(gaussianReal 0 1) ∧
    ∫ g, 2 * |g| * Real.arctan (|g| * s) ∂(gaussianReal 0 1) ≤ 2 * s ∧
    ∫ g, 2 * |g| * Real.arctan (|g| * s) ∂(gaussianReal 0 1) ≤ Real.sqrt (2 * Real.pi) := by
  rcases hs.eq_or_lt with h | h
  · subst h
    simp [Real.sqrt_nonneg]
  · exact ⟨(P5_H_bounds h).1, (P5_H_bounds h).2.1, (P5_H_bounds h).2.2.1⟩

private lemma P5_F_cont {w a b : ℝ} (hw : 0 < w) (ha : 0 < a) :
    ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹ * (w * J (w ^ 2 * x))) (Set.Icc a b) := by
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
  refine ContinuousAt.continuousWithinAt ?_
  have h1 : ContinuousAt (fun x : ℝ => (Real.sqrt x)⁻¹) x :=
    (Real.continuous_sqrt.continuousAt).inv₀ (Real.sqrt_pos.2 hx0).ne'
  have h2 : ContinuousAt (fun x : ℝ => J (w ^ 2 * x)) x := by
    have hJ := (lem_app_de_scalar_i.1).continuousAt (Ici_mem_nhds (by positivity : (0:ℝ) < w ^ 2 * x))
    exact hJ.comp (f := fun x : ℝ => w ^ 2 * x) (by fun_prop)
  exact h1.mul (h2.const_mul w)

private lemma P5_avg_q {β q0 Q : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hq0 : 0 < q0) (hQ : q0 ≤ Q) :
    |(∫ x in q0..Q, (Real.sqrt x)⁻¹ * Lw (emaW β) x) -
      Real.sqrt (2 * Real.pi) * (nRes β Q : ℝ)| ≤ 2 * Real.sqrt q0 + 4 / (1 - β) := by
  set H : ℝ → ℝ := fun s => ∫ g, 2 * |g| * Real.arctan (|g| * s) ∂(gaussianReal 0 1) with hH
  have hQ0 : 0 < Q := lt_of_lt_of_le hq0 hQ
  have hwpos := P4_emaW_pos hβ0 hβ1
  set F : ℕ → ℝ → ℝ := fun j x => (Real.sqrt x)⁻¹ * (emaW β j * J (emaW β j ^ 2 * x)) with hF
  have hterm : ∀ j, ∫ x in q0..Q, F j x = H (emaW β j * Real.sqrt Q) - H (emaW β j * Real.sqrt q0) :=
    fun j => P5_term_int (hwpos j) hq0 hQ
  have hFnn : ∀ j, ∀ x ∈ Set.Ioc q0 Q, 0 ≤ F j x := by
    intro j x hx
    have hx0 : 0 < x := lt_of_lt_of_le hq0 hx.1.le
    have := (lem_app_de_scalar_i.2.2.1 (emaW β j ^ 2 * x) (by positivity)).1
    simp only [hF]
    have := (hwpos j)
    positivity
  have hFint : ∀ j, Integrable (F j) (volume.restrict (Set.Ioc q0 Q)) := fun j =>
    ((P5_F_cont (hwpos j) hq0 (b := Q)).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hnorm : ∀ j, ∫ x in Set.Ioc q0 Q, ‖F j x‖ = H (emaW β j * Real.sqrt Q) - H (emaW β j * Real.sqrt q0) := by
    intro j
    rw [← hterm j, intervalIntegral.integral_of_le hQ]
    refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    exact Real.norm_of_nonneg (hFnn j x hx)
  have hsq0 : 0 ≤ Real.sqrt q0 := Real.sqrt_nonneg _
  have hsQ0 : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg _
  have hHq0 : ∀ j, 0 ≤ H (emaW β j * Real.sqrt q0) ∧ H (emaW β j * Real.sqrt q0) ≤ 2 * (emaW β j * Real.sqrt q0) :=
    fun j => ⟨(P5_H_bounds0 (mul_nonneg (hwpos j).le hsq0)).1, (P5_H_bounds0 (mul_nonneg (hwpos j).le hsq0)).2.1⟩
  have hHQ : ∀ j, 0 ≤ H (emaW β j * Real.sqrt Q) ∧ H (emaW β j * Real.sqrt Q) ≤ 2 * (emaW β j * Real.sqrt Q) :=
    fun j => ⟨(P5_H_bounds0 (mul_nonneg (hwpos j).le hsQ0)).1, (P5_H_bounds0 (mul_nonneg (hwpos j).le hsQ0)).2.1⟩
  have hwsum : Summable (emaW β) := (P2_weightSeq hβ0.le hβ1).2.1
  have hsumQ : Summable (fun j => H (emaW β j * Real.sqrt Q)) :=
    Summable.of_nonneg_of_le (fun j => (hHQ j).1) (fun j => (hHQ j).2)
      ((hwsum.mul_right (Real.sqrt Q)).mul_left 2)
  have hsum0 : Summable (fun j => H (emaW β j * Real.sqrt q0)) :=
    Summable.of_nonneg_of_le (fun j => (hHq0 j).1) (fun j => (hHq0 j).2)
      ((hwsum.mul_right (Real.sqrt q0)).mul_left 2)
  have hsumnorm : Summable (fun j => ∫ x in Set.Ioc q0 Q, ‖F j x‖) := by
    simp_rw [hnorm]
    exact hsumQ.sub hsum0
  have hHS := hasSum_integral_of_summable_integral_norm hFint hsumnorm
  have hLw : ∀ x, (Real.sqrt x)⁻¹ * Lw (emaW β) x = ∑' j, F j x := by
    intro x
    unfold Lw
    rw [← tsum_mul_left]
  have hint : (∫ x in q0..Q, (Real.sqrt x)⁻¹ * Lw (emaW β) x) =
      ∑' j, (H (emaW β j * Real.sqrt Q) - H (emaW β j * Real.sqrt q0)) := by
    rw [intervalIntegral.integral_of_le hQ]
    simp_rw [hLw]
    rw [← hHS.tsum_eq]
    refine tsum_congr (fun j => ?_)
    rw [← hnorm j]
    refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    exact (Real.norm_of_nonneg (hFnn j x hx)).symm
  rw [hint, hsumQ.tsum_sub hsum0]
  -- split the Q-series
  set h : ℝ → ℝ := fun x => H (Real.sqrt x) - if 1 ≤ x then Real.sqrt (2 * Real.pi) else 0 with hh
  have hcalc : ∀ j, H (emaW β j * Real.sqrt Q) = H (Real.sqrt (emaW β j ^ 2 * Q)) := by
    intro j
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hwpos j).le]
  obtain ⟨hsum_h, hbd_h⟩ := P4_sum_bound hβ0 hβ1 hQ0 h (a := 2) (b := 2) (by norm_num) (by norm_num)
    (fun x hx => by
      have hxs : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
      have hb := P5_H_bounds hxs
      have hh1 : h x = H (Real.sqrt x) - Real.sqrt (2 * Real.pi) := by simp [hh, hx]
      rw [hh1, abs_of_nonpos (by linarith [hb.2.2.1]), div_eq_mul_inv]
      have := hb.2.2.2
      have e : 2 / Real.sqrt x = 2 * (Real.sqrt x)⁻¹ := div_eq_mul_inv _ _
      linarith)
    (fun x hx0 hx1 => by
      have hh1 : h x = H (Real.sqrt x) := by simp [hh, not_le.2 hx1]
      have hb := P5_H_bounds0 (Real.sqrt_nonneg x)
      rw [hh1, abs_of_nonneg hb.1]
      exact hb.2.1)
  obtain ⟨N, hN1, hN2⟩ := P4_split hβ0 hβ1 hQ0
  have hnres := P4_nRes hN1 hN2
  have hind : ∑' j : ℕ, (if 1 ≤ emaW β j ^ 2 * Q then Real.sqrt (2 * Real.pi) else 0) =
      Real.sqrt (2 * Real.pi) * (nRes β Q : ℝ) := by
    rw [tsum_eq_sum (s := Finset.range N)]
    · rw [Finset.sum_congr rfl (g := fun _ => Real.sqrt (2 * Real.pi))]
      · simp [hnres, mul_comm]
      · intro j hj
        rw [if_pos (hN1 j (Finset.mem_range.1 hj))]
    · intro j hj
      rw [if_neg (not_le.2 (hN2 j (not_lt.1 (Finset.mem_range.not.1 hj))))]
  have hind_summ : Summable (fun j : ℕ => (if 1 ≤ emaW β j ^ 2 * Q then Real.sqrt (2 * Real.pi) else 0)) := by
    refine summable_of_ne_finset_zero (s := Finset.range N) (fun j hj => ?_)
    rw [if_neg (not_le.2 (hN2 j (not_lt.1 (Finset.mem_range.not.1 hj))))]
  have hQsplit : ∑' j, H (emaW β j * Real.sqrt Q) =
      ∑' j, h (emaW β j ^ 2 * Q) + Real.sqrt (2 * Real.pi) * (nRes β Q : ℝ) := by
    rw [← hind, ← hsum_h.tsum_add hind_summ]
    refine tsum_congr (fun j => ?_)
    simp only [hh]
    rw [hcalc j]
    ring
  have h0le : 0 ≤ ∑' j, H (emaW β j * Real.sqrt q0) := tsum_nonneg (fun j => (hHq0 j).1)
  have h0ge : ∑' j, H (emaW β j * Real.sqrt q0) ≤ 2 * Real.sqrt q0 := by
    calc ∑' j, H (emaW β j * Real.sqrt q0) ≤ ∑' j, 2 * (emaW β j * Real.sqrt q0) :=
          hsum0.tsum_le_tsum (fun j => (hHq0 j).2) ((hwsum.mul_right (Real.sqrt q0)).mul_left 2)
      _ = 2 * Real.sqrt q0 := by
          rw [tsum_mul_left, tsum_mul_right, tsum_emaW hβ0.le hβ1]; ring
  rw [hQsplit]
  have hbd := abs_le.1 hbd_h
  have e4 : (2 + 2) / (1 - β) = 4 / (1 - β) := by norm_num
  rw [e4] at hbd
  rw [abs_le]
  constructor <;> linarith [hbd.1, hbd.2]

private lemma P5_Qm_rW {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {x : ℝ} (hx : 0 < x) :
    Qm β (rW (emaW β) x) = x := by
  have hex : ∃ a ∈ Ioi (0:ℝ), rW (emaW β) a = rW (emaW β) x := ⟨x, hx, rfl⟩
  have h1 : Qm β (rW (emaW β) x) ∈ Ioi (0:ℝ) := Function.invFunOn_mem hex
  have h2 : rW (emaW β) (Qm β (rW (emaW β) x)) = rW (emaW β) x := Function.invFunOn_eq hex
  exact ((lem_app_de_scalar_iii (P2_weightSeq hβ0.le hβ1)).2.1.injOn
    (Set.mem_Ici.2 h1.out.le) (Set.mem_Ici.2 hx.le) h2)

private lemma P5_deriv {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (rW (emaW β)) (deriv (rW (emaW β)) x) x ∧ 0 < deriv (rW (emaW β)) x := by
  have h := lem_app_de_scalar_iii (P2_weightSeq hβ0.le hβ1)
  have hd := h.2.2.2.1 x hx
  refine ⟨hd.differentiableAt.hasDerivAt, ?_⟩
  rw [hd.deriv]
  exact h.2.2.2.2.1 x hx

private lemma P5_cov {β m0 t : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hm0 : 0 < m0) (ht : m0 ≤ t) :
    IntervalIntegrable (Aav β) volume m0 t ∧
    ∫ m in m0..t, Aav β m = ∫ x in Qm β m0..Qm β t, (Real.sqrt x)⁻¹ * Lw (emaW β) x := by
  obtain ⟨hq0, hr0⟩ := P4_Qm hβ0 hβ1 hm0
  obtain ⟨hqt, hrt⟩ := P4_Qm hβ0 hβ1 (lt_of_lt_of_le hm0 ht)
  have hle : Qm β m0 ≤ Qm β t := P5_Qm_ge hβ0 hβ1 hm0 ht
  set q0 := Qm β m0
  set Qt := Qm β t
  have hderiv : ∀ x ∈ Icc q0 Qt, HasDerivWithinAt (rW (emaW β)) (deriv (rW (emaW β)) x) (Icc q0 Qt) x :=
    fun x hx => (P5_deriv hβ0 hβ1 (lt_of_lt_of_le hq0 hx.1)).1.hasDerivWithinAt
  have hcont : ContinuousOn (rW (emaW β)) (Icc q0 Qt) := fun x hx => (hderiv x hx).continuousWithinAt
  have hinj : InjOn (rW (emaW β)) (Icc q0 Qt) :=
    ((lem_app_de_scalar_iii (P2_weightSeq hβ0.le hβ1)).2.1.injOn).mono
      (fun x hx => Set.mem_Ici.2 (hq0.le.trans hx.1))
  have himg : rW (emaW β) '' Icc q0 Qt = Icc m0 t := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hmono := (lem_app_de_scalar_iii (P2_weightSeq hβ0.le hβ1)).2.1
      constructor
      · rw [← hr0]
        exact hmono.monotoneOn (Set.mem_Ici.2 hq0.le) (Set.mem_Ici.2 (hq0.le.trans hx.1)) hx.1
      · rw [← hrt]
        exact hmono.monotoneOn (Set.mem_Ici.2 (hq0.le.trans hx.1)) (Set.mem_Ici.2 hqt.le) hx.2
    · have := intermediate_value_Icc hle hcont
      rwa [hr0, hrt] at this
  have hpt : ∀ x ∈ Icc q0 Qt, |deriv (rW (emaW β)) x| • Aav β (rW (emaW β) x) =
      (Real.sqrt x)⁻¹ * Lw (emaW β) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hq0 hx.1
    obtain ⟨-, hdp⟩ := P5_deriv hβ0 hβ1 hx0
    have hsq : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    have hss : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
    rw [smul_eq_mul, abs_of_pos hdp]
    unfold Aav Efun
    rw [P5_Qm_rW hβ0 hβ1 hx0]
    field_simp
    rw [hss]
    ring
  have hcts : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹ * Lw (emaW β) x) (Icc q0 Qt) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hq0 hx.1
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun x : ℝ => (Real.sqrt x)⁻¹) x :=
      (Real.continuous_sqrt.continuousAt).inv₀ (Real.sqrt_pos.2 hx0).ne'
    have h2 : ContinuousAt (Lw (emaW β)) x :=
      ((lem_app_de_scalar_ii (P2_weightSeq hβ0.le hβ1)).2.2.2.1).continuousAt (Ici_mem_nhds hx0)
    exact h1.mul h2
  have hint : IntegrableOn (fun x => |deriv (rW (emaW β)) x| • Aav β (rW (emaW β) x)) (Icc q0 Qt) := by
    refine (hcts.integrableOn_Icc).congr_fun (fun x hx => (hpt x hx).symm) measurableSet_Icc
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc hderiv hinj (Aav β)
  rw [himg] at hiff
  have hI : IntegrableOn (Aav β) (Icc m0 t) := hiff.2 hint
  refine ⟨?_, ?_⟩
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le ht).2 hI
  · have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hderiv hinj (Aav β)
    rw [himg] at h
    rw [intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc, h,
      intervalIntegral.integral_of_le hle, ← integral_Icc_eq_integral_Ioc]
    exact setIntegral_congr_fun measurableSet_Icc hpt

/-- `lem:app-pl-average`(ii), snapshot `cr-2026-10-23`: the integrability of `𝒜` on the
intervals `[m₀,t]` (implicit in the source's integral) and the uniform bound
`eqn:app-pl-average`, with `C` depending on `(β, m₀)`.
LaTeX (`sections/06-power-law/section.tex` l.309–320):
\begin{lemma}[Averaging in the participation coordinate]\label{lem:app-pl-average}
Put $\mathcal A(m)\defeq\sqrt{Q_m}\,\Lw(Q_m)/E(m)$ for $m>0$. For every $m_0>0$,
$\mathcal A\asymp1$ on $[m_0,\infty)$ with constants depending on $(\bmom,m_0)$, and
\begin{equation}\label{eqn:app-pl-average}
\sup_{t\ge m_0}\Big|\int_{m_0}^t\big(\mathcal A(m)-\sqrt{2\pi}\big)\,\dif m\Big|\le C_{\bmom,m_0}.
\end{equation}
Consequently, for every $[a,c]\subset[m_0,\infty)$ and every continuously
differentiable $W$ on $[a,c]$,
\begin{equation}\label{eqn:app-pl-average-ibp}
\Big|\int_a^c\big(\mathcal A(m)-\sqrt{2\pi}\big)W(m)\,\dif m\Big|\le C_{\bmom,m_0}\Big(\abs{W(a)}+\abs{W(c)}+\int_a^c\abs{W'(m)}\,\dif m\Big).
\end{equation}
\end{lemma} -/
theorem lem_app_pl_average_ii {β m0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hm0 : 0 < m0) :
    (∀ t : ℝ, m0 ≤ t → IntervalIntegrable (Aav β) volume m0 t) ∧
    ∃ C : ℝ, ∀ t : ℝ, m0 ≤ t →
      |∫ m in m0..t, (Aav β m - Real.sqrt (2 * Real.pi))| ≤ C := by
  refine ⟨fun t ht => (P5_cov hβ0 hβ1 hm0 ht).1, ?_⟩
  obtain ⟨c, CA, hc, hA⟩ := lem_app_pl_average_i hβ0 hβ1 hm0
  obtain ⟨c3, C3, hc3, hcC3, h3⟩ := lem_app_pl_weights_iii hβ0 hβ1
  obtain ⟨hq0, -⟩ := P4_Qm hβ0 hβ1 hm0
  set s := Real.sqrt (2 * Real.pi) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hCA : 0 ≤ CA := (hc.le.trans (hA m0 le_rfl).1).trans (hA m0 le_rfl).2
  have hC3 : 0 ≤ C3 := hc3.le.trans hcC3
  refine ⟨(CA + s) + (2 * Real.sqrt (Qm β m0) + 4 / (1 - β)) + s * C3 + s * m0, fun t ht => ?_⟩
  have hK : 0 ≤ 2 * Real.sqrt (Qm β m0) + 4 / (1 - β) := by
    have : 0 < 1 - β := by linarith
    positivity
  have hsC3 : 0 ≤ s * C3 := mul_nonneg hs0 hC3
  have hsm : 0 ≤ s * m0 := mul_nonneg hs0 hm0.le
  rcases le_total t 1 with h1 | h1
  · have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := m0) (b := t) (f := fun m => Aav β m - s) (C := CA + s) (fun x hx => by
        rw [Set.uIoc_of_le ht] at hx
        obtain ⟨hlo, hhi⟩ := hA x hx.1.le
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith)
    rw [Real.norm_eq_abs] at hb
    have : |t - m0| ≤ 1 := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have h2 : (CA + s) * |t - m0| ≤ CA + s := mul_le_of_le_one_right (by linarith) this
    linarith
  · have hti := (P5_cov hβ0 hβ1 hm0 ht)
    have hQ1 : 1 ≤ Qm β t := P4_Qm_ge hβ0 hβ1 h1
    obtain ⟨-, hrt⟩ := P4_Qm hβ0 hβ1 (by linarith : (0:ℝ) < t)
    have hle : Qm β m0 ≤ Qm β t := P5_Qm_ge hβ0 hβ1 hm0 ht
    have hav := P5_avg_q hβ0 hβ1 hq0 hle
    have hn := (h3 (Qm β t) hQ1).1
    rw [hrt] at hn
    rw [← hti.2] at hav
    have e : ∫ m in m0..t, (Aav β m - s) = (∫ m in m0..t, Aav β m) - s * (t - m0) := by
      rw [intervalIntegral.integral_sub hti.1 intervalIntegrable_const]
      simp
      ring
    rw [e]
    have hsn : |s * (nRes β (Qm β t) : ℝ) - s * t| ≤ s * C3 := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hs0, abs_sub_comm]
      exact mul_le_mul_of_nonneg_left hn hs0
    have htri := abs_add_le ((∫ m in m0..t, Aav β m) - s * (nRes β (Qm β t) : ℝ))
      (s * (nRes β (Qm β t) : ℝ) - s * t)
    have htri2 := abs_add_le ((∫ m in m0..t, Aav β m) - s * (nRes β (Qm β t) : ℝ) +
      (s * (nRes β (Qm β t) : ℝ) - s * t)) (s * m0)
    have e2 : (∫ m in m0..t, Aav β m) - s * (t - m0) =
        ((∫ m in m0..t, Aav β m) - s * (nRes β (Qm β t) : ℝ) +
          (s * (nRes β (Qm β t) : ℝ) - s * t)) + s * m0 := by ring
    rw [e2]
    rw [abs_of_nonneg hsm] at htri2
    linarith [abs_nonneg (s * (nRes β (Qm β t) : ℝ) - s * t), le_abs_self (s * m0)]

/-- `lem:app-pl-average`(iii), snapshot `cr-2026-10-23`: the integration-by-parts bound
`eqn:app-pl-average-ibp`. The constant depends on `(β, m₀)` only, not on `[a,c]` or `W`.
LaTeX (`sections/06-power-law/section.tex` l.309–320):
\begin{lemma}[Averaging in the participation coordinate]\label{lem:app-pl-average}
Put $\mathcal A(m)\defeq\sqrt{Q_m}\,\Lw(Q_m)/E(m)$ for $m>0$. For every $m_0>0$,
$\mathcal A\asymp1$ on $[m_0,\infty)$ with constants depending on $(\bmom,m_0)$, and
\begin{equation}\label{eqn:app-pl-average}
\sup_{t\ge m_0}\Big|\int_{m_0}^t\big(\mathcal A(m)-\sqrt{2\pi}\big)\,\dif m\Big|\le C_{\bmom,m_0}.
\end{equation}
Consequently, for every $[a,c]\subset[m_0,\infty)$ and every continuously
differentiable $W$ on $[a,c]$,
\begin{equation}\label{eqn:app-pl-average-ibp}
\Big|\int_a^c\big(\mathcal A(m)-\sqrt{2\pi}\big)W(m)\,\dif m\Big|\le C_{\bmom,m_0}\Big(\abs{W(a)}+\abs{W(c)}+\int_a^c\abs{W'(m)}\,\dif m\Big).
\end{equation}
\end{lemma} -/
theorem lem_app_pl_average_iii {β m0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hm0 : 0 < m0) :
    ∃ C : ℝ, ∀ a c : ℝ, m0 ≤ a → a ≤ c → ∀ W : ℝ → ℝ, ContDiffOn ℝ 1 W (Icc a c) →
      |∫ m in a..c, (Aav β m - Real.sqrt (2 * Real.pi)) * W m| ≤
        C * (|W a| + |W c| + ∫ m in a..c, |derivWithin W (Icc a c) m|) := by
  obtain ⟨-, C0, hC0⟩ := lem_app_pl_average_ii hβ0 hβ1 hm0
  have hC0nn : 0 ≤ C0 := (abs_nonneg _).trans (hC0 m0 le_rfl)
  refine ⟨C0, fun a c hma hac W hW => ?_⟩
  rcases eq_or_lt_of_le hac with rfl | hlt
  · simp only [intervalIntegral.integral_same, abs_zero]
    nlinarith [abs_nonneg (W a)]
  have hIcc : Set.uIcc a c = Set.Icc a c := Set.uIcc_of_le hac
  have hint : IntervalIntegrable (fun m => Aav β m - Real.sqrt (2 * Real.pi)) volume m0 c :=
    ((lem_app_pl_average_ii hβ0 hβ1 hm0).1 c (hma.trans hac)).sub intervalIntegrable_const
  have hsub : Set.uIcc a c ⊆ Set.uIcc m0 c :=
    Set.uIcc_subset_uIcc (Set.mem_uIcc.2 (Or.inl ⟨hma, hac⟩))
      (Set.mem_uIcc.2 (Or.inl ⟨hma.trans hac, le_rfl⟩))
  have hG : AbsolutelyContinuousOnInterval
      (fun x => ∫ m in m0..x, (Aav β m - Real.sqrt (2 * Real.pi))) a c :=
    (hint.absolutelyContinuousOnInterval_intervalIntegral Set.left_mem_uIcc).mono hsub
  have hWac : AbsolutelyContinuousOnInterval W a c := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [hIcc]
    exact hW
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc a c →
      deriv (fun x => ∫ m in m0..x, (Aav β m - Real.sqrt (2 * Real.pi))) x
        = Aav β x - Real.sqrt (2 * Real.pi) := by
    filter_upwards [hint.ae_hasDerivAt_integral] with x hx hxI
    have hxm : x ∈ Set.uIcc m0 c := hsub (Set.uIoc_subset_uIcc hxI)
    exact (hx hxm m0 Set.left_mem_uIcc).deriv
  have hderiv_eq : ∫ x in a..c, deriv (fun x => ∫ m in m0..x, (Aav β m - Real.sqrt (2 * Real.pi))) x * W x
      = ∫ x in a..c, (Aav β x - Real.sqrt (2 * Real.pi)) * W x :=
    intervalIntegral.integral_congr_ae (hae.mono fun x hx hxI => by rw [hx hxI])
  have hIBP := hG.integral_mul_deriv_eq_deriv_mul hWac
  have hGc : |∫ m in m0..c, (Aav β m - Real.sqrt (2 * Real.pi))| ≤ C0 :=
    hC0 c (hma.trans hac)
  have hGa : |∫ m in m0..a, (Aav β m - Real.sqrt (2 * Real.pi))| ≤ C0 := hC0 a hma
  have hcont : ContinuousOn (derivWithin W (Icc a c)) (Icc a c) :=
    hW.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) (by norm_num)
  have hdWint : IntervalIntegrable (fun x => |derivWithin W (Icc a c) x|) volume a c := by
    apply ContinuousOn.intervalIntegrable
    rw [hIcc]
    exact hcont.abs
  have hI2 : |∫ x in a..c, (∫ m in m0..x, (Aav β m - Real.sqrt (2 * Real.pi))) * deriv W x|
      ≤ C0 * ∫ x in a..c, |derivWithin W (Icc a c) x| := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f := fun x =>
        (∫ m in m0..x, (Aav β m - Real.sqrt (2 * Real.pi))) * deriv W x)
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
  have hA1 : |(∫ m in m0..c, (Aav β m - Real.sqrt (2 * Real.pi))) * W c| ≤
      C0 * |W c| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hGc (abs_nonneg _)
  have hA2 : |(∫ m in m0..a, (Aav β m - Real.sqrt (2 * Real.pi))) * W a| ≤
      C0 * |W a| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hGa (abs_nonneg _)
  have hI1 : ∫ x in a..c, (Aav β x - Real.sqrt (2 * Real.pi)) * W x =
      (∫ m in m0..c, (Aav β m - Real.sqrt (2 * Real.pi))) * W c
        - (∫ m in m0..a, (Aav β m - Real.sqrt (2 * Real.pi))) * W a
        - ∫ x in a..c, (∫ m in m0..x, (Aav β m - Real.sqrt (2 * Real.pi))) * deriv W x := by
    rw [← hderiv_eq]
    linarith [hIBP]
  rw [hI1]
  have hT := tri ((∫ m in m0..c, (Aav β m - Real.sqrt (2 * Real.pi))) * W c)
    ((∫ m in m0..a, (Aav β m - Real.sqrt (2 * Real.pi))) * W a)
    (∫ x in a..c, (∫ m in m0..x, (Aav β m - Real.sqrt (2 * Real.pi))) * deriv W x)
  nlinarith [hT, hA1, hA2, hI2]

/-! ### Helpers for `eqn_app_pl_divided` (fully proved) -/

private lemma P7_pos {d : ℝ} (hd : 0 ≤ d) (g : ℝ) : 0 < 1 + d * g ^ 2 := by
  have := mul_nonneg hd (sq_nonneg g)
  linarith

private lemma P7_integrable {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (k : ℕ) :
    Integrable (fun g : ℝ => c * g ^ 2 / (1 + d * g ^ 2) ^ k) (gaussianReal 0 1) := by
  refine Integrable.mono' ((Muon.Foundations.gaussian_integrable_pow 2).const_mul c) ?_ ?_
  · exact (Measurable.div (by fun_prop) (by fun_prop)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun g => ?_
    have h1 : 1 ≤ (1 + d * g ^ 2) ^ k := one_le_pow₀ (by linarith [mul_nonneg hd (sq_nonneg g)])
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg hc (sq_nonneg g))
      (pow_nonneg (P7_pos hd g).le k))]
    exact div_le_self (mul_nonneg hc (sq_nonneg g)) h1

private lemma P7_summ_gen (c d : ℕ → ℝ) (hc : ∀ j, 0 ≤ c j) (hd : ∀ j, 0 ≤ d j)
    (hs : Summable c) (k : ℕ) :
    Summable (fun j : ℕ => ∫ g : ℝ, c j * g ^ 2 / (1 + d j * g ^ 2) ^ k ∂(gaussianReal 0 1)) := by
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
    (hs.mul_right (∫ g : ℝ, g ^ 2 ∂(gaussianReal 0 1)))
  · exact integral_nonneg fun g => div_nonneg (mul_nonneg (hc j) (sq_nonneg g))
      (pow_nonneg (P7_pos (hd j) g).le k)
  · calc ∫ g : ℝ, c j * g ^ 2 / (1 + d j * g ^ 2) ^ k ∂(gaussianReal 0 1)
        ≤ ∫ g : ℝ, c j * g ^ 2 ∂(gaussianReal 0 1) :=
          integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun g => div_nonneg (mul_nonneg (hc j) (sq_nonneg g))
              (pow_nonneg (P7_pos (hd j) g).le k))
            ((Muon.Foundations.gaussian_integrable_pow 2).const_mul (c j))
            (Filter.Eventually.of_forall fun g => div_le_self (mul_nonneg (hc j) (sq_nonneg g))
              (one_le_pow₀ (by linarith [mul_nonneg (hd j) (sq_nonneg g)])))
      _ = c j * ∫ g : ℝ, g ^ 2 ∂(gaussianReal 0 1) := integral_const_mul _ _

private lemma P7_summF {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (q : ℝ) (hq : 0 ≤ q) :
    Summable (fun j : ℕ => ∫ g : ℝ, emaW β j ^ 2 * g ^ 2 / (1 + emaW β j ^ 2 * q * g ^ 2)
      ∂(gaussianReal 0 1)) := by
  have := P7_summ_gen (fun j => emaW β j ^ 2) (fun j => emaW β j ^ 2 * q)
    (fun j => sq_nonneg _) (fun j => mul_nonneg (sq_nonneg _) hq)
    (summable_emaW_pow_P1 (p := 2) hβ0 hβ1 (by norm_num)) 1
  simpa only [pow_one] using this

private lemma P7_pt_diff {a x y : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∫ g : ℝ, a * x * g ^ 2 / (1 + a * x * g ^ 2) ∂(gaussianReal 0 1)
      - ∫ g : ℝ, a * y * g ^ 2 / (1 + a * y * g ^ 2) ∂(gaussianReal 0 1)
    = (x - y) * ∫ g : ℝ, a * g ^ 2 / ((1 + a * x * g ^ 2) * (1 + a * y * g ^ 2))
        ∂(gaussianReal 0 1) := by
  have hI1 := P7_integrable (c := a * x) (d := a * x) (mul_nonneg ha hx) (mul_nonneg ha hx) 1
  have hI2 := P7_integrable (c := a * y) (d := a * y) (mul_nonneg ha hy) (mul_nonneg ha hy) 1
  simp only [pow_one] at hI1 hI2
  rw [← integral_sub hI1 hI2, ← integral_const_mul]
  congr 1
  funext g
  have d1 := (P7_pos (mul_nonneg ha hx) g).ne'
  have d2 := (P7_pos (mul_nonneg ha hy) g).ne'
  field_simp
  ring

private lemma P7_pt_F {a x y : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∫ g : ℝ, a * g ^ 2 / (1 + a * x * g ^ 2) ∂(gaussianReal 0 1)
      - ∫ g : ℝ, a * g ^ 2 / (1 + a * y * g ^ 2) ∂(gaussianReal 0 1)
    = (y - x) * ∫ g : ℝ, a ^ 2 * g ^ 4 / ((1 + a * x * g ^ 2) * (1 + a * y * g ^ 2))
        ∂(gaussianReal 0 1) := by
  have hI1 := P7_integrable (c := a) (d := a * x) ha (mul_nonneg ha hx) 1
  have hI2 := P7_integrable (c := a) (d := a * y) ha (mul_nonneg ha hy) 1
  simp only [pow_one] at hI1 hI2
  rw [← integral_sub hI1 hI2, ← integral_const_mul]
  congr 1
  funext g
  have d1 := (P7_pos (mul_nonneg ha hx) g).ne'
  have d2 := (P7_pos (mul_nonneg ha hy) g).ne'
  field_simp
  ring

private lemma P7_pt_coinc {a q : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q) :
    ∫ g : ℝ, a * q * g ^ 2 / (1 + a * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1)
      - ∫ g : ℝ, a * q * g ^ 2 / (1 + a * q * g ^ 2) ∂(gaussianReal 0 1)
    = -(q ^ 2 * ∫ g : ℝ, a ^ 2 * g ^ 4 / (1 + a * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1)) := by
  have hU := P7_integrable (c := a * q) (d := a * q) (mul_nonneg ha hq) (mul_nonneg ha hq) 2
  have hV := P7_integrable (c := a * q) (d := a * q) (mul_nonneg ha hq) (mul_nonneg ha hq) 1
  simp only [pow_one] at hV
  rw [← integral_sub hU hV, ← integral_const_mul, ← integral_neg]
  congr 1
  funext g
  have d := (P7_pos (mul_nonneg ha hq) g).ne'
  field_simp
  ring

private lemma P7_Fw_sum (β q : ℝ) :
    Fw (emaW β) q = ∑' j : ℕ, ∫ g : ℝ, emaW β j ^ 2 * g ^ 2 / (1 + emaW β j ^ 2 * q * g ^ 2)
      ∂(gaussianReal 0 1) := by
  unfold Fw
  refine tsum_congr fun j => ?_
  unfold J
  rw [← integral_const_mul]
  congr 1
  funext g
  ring

/-- `eqn:app-pl-divided`, snapshot `cr-2026-10-23`: the divided-difference forms of
`b_ℓ, e_ℓ` for `q, q' > 0` (the displayed forms, valid off the coincidence `q = β^{2ℓ} q'`),
with the derivative values on the coincidence (the source's "with derivatives at coincident
arguments").
LaTeX (`sections/06-power-law/section.tex` l.459–463):
\begin{equation}\label{eqn:app-pl-divided}
b_\ell=\bmom^\ell\,\frac{r_\bmom(q)-r_\bmom(\bmom^{2\ell}q')}{q-\bmom^{2\ell}q'},\qquad
e_\ell=\bmom^{2\ell}\,\frac{\Fw(q)-\Fw(\bmom^{2\ell}q')}{\bmom^{2\ell}q'-q},
\end{equation} -/
theorem eqn_app_pl_divided {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {ℓ : ℕ} {q q' : ℝ}
    (hq : 0 < q) (hq' : 0 < q') :
    (q ≠ β ^ (2 * ℓ) * q' →
      bLag β q q' ℓ =
          β ^ ℓ * (rW (emaW β) q - rW (emaW β) (β ^ (2 * ℓ) * q')) / (q - β ^ (2 * ℓ) * q') ∧
      eLag β q q' ℓ =
          β ^ (2 * ℓ) * (Fw (emaW β) q - Fw (emaW β) (β ^ (2 * ℓ) * q')) /
            (β ^ (2 * ℓ) * q' - q)) ∧
    (q = β ^ (2 * ℓ) * q' →
      bLag β q q' ℓ = β ^ ℓ * deriv (rW (emaW β)) q ∧
      eLag β q q' ℓ = -(β ^ (2 * ℓ) * deriv (Fw (emaW β)) q)) := by
  have hw : WeightSeq (emaW β) := P2_weightSeq hβ0 hβ1
  have hc0 : 0 ≤ β ^ (2 * ℓ) := pow_nonneg hβ0 _
  have hsumm : Summable (fun j : ℕ => emaW β j ^ 2) :=
    summable_emaW_pow_P1 (p := 2) hβ0 hβ1 (by norm_num)
  have hSq : Summable (fun j : ℕ => ∫ g : ℝ, emaW β j ^ 2 * q * g ^ 2 /
      (1 + emaW β j ^ 2 * q * g ^ 2) ∂(gaussianReal 0 1)) := by
    have := P7_summ_gen (fun j => emaW β j ^ 2 * q) (fun j => emaW β j ^ 2 * q)
      (fun j => mul_nonneg (sq_nonneg _) hq.le) (fun j => mul_nonneg (sq_nonneg _) hq.le)
      (hsumm.mul_right q) 1
    simpa only [pow_one] using this
  constructor
  · intro hne
    have hy : 0 ≤ β ^ (2 * ℓ) * q' := mul_nonneg hc0 hq'.le
    have hsub : q - β ^ (2 * ℓ) * q' ≠ 0 := sub_ne_zero.2 hne
    have hsub' : β ^ (2 * ℓ) * q' - q ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    have hSy : Summable (fun j : ℕ => ∫ g : ℝ, emaW β j ^ 2 * (β ^ (2 * ℓ) * q') * g ^ 2 /
        (1 + emaW β j ^ 2 * (β ^ (2 * ℓ) * q') * g ^ 2) ∂(gaussianReal 0 1)) := by
      have := P7_summ_gen (fun j => emaW β j ^ 2 * (β ^ (2 * ℓ) * q'))
        (fun j => emaW β j ^ 2 * (β ^ (2 * ℓ) * q'))
        (fun j => mul_nonneg (sq_nonneg _) hy) (fun j => mul_nonneg (sq_nonneg _) hy)
        (hsumm.mul_right _) 1
      simpa only [pow_one] using this
    have hRdiff : rW (emaW β) q - rW (emaW β) (β ^ (2 * ℓ) * q') =
        (q - β ^ (2 * ℓ) * q') * ∑' j : ℕ, ∫ g : ℝ, emaW β j ^ 2 * g ^ 2 /
          ((1 + emaW β j ^ 2 * q * g ^ 2) * (1 + emaW β j ^ 2 * (β ^ (2 * ℓ) * q') * g ^ 2))
          ∂(gaussianReal 0 1) := by
      rw [(lem_app_de_scalar_iii hw).1 q hq.le, (lem_app_de_scalar_iii hw).1 _ hy,
        ← Summable.tsum_sub hSq hSy, ← tsum_mul_left]
      exact tsum_congr fun j => P7_pt_diff (a := emaW β j ^ 2) (x := q)
        (y := β ^ (2 * ℓ) * q') (sq_nonneg _) hq.le hy
    have hF : Fw (emaW β) q - Fw (emaW β) (β ^ (2 * ℓ) * q') =
        (β ^ (2 * ℓ) * q' - q) * ∑' j : ℕ, ∫ g : ℝ, (emaW β j ^ 2) ^ 2 * g ^ 4 /
          ((1 + emaW β j ^ 2 * q * g ^ 2) * (1 + emaW β j ^ 2 * (β ^ (2 * ℓ) * q') * g ^ 2))
          ∂(gaussianReal 0 1) := by
      rw [P7_Fw_sum β q, P7_Fw_sum β (β ^ (2 * ℓ) * q'),
        ← Summable.tsum_sub (P7_summF hβ0 hβ1 q hq.le) (P7_summF hβ0 hβ1 _ hy), ← tsum_mul_left]
      exact tsum_congr fun j => P7_pt_F (a := emaW β j ^ 2) (x := q)
        (y := β ^ (2 * ℓ) * q') (sq_nonneg _) hq.le hy
    refine ⟨?_, ?_⟩
    · unfold bLag
      rw [hRdiff, mul_left_comm (β ^ ℓ), mul_div_cancel_left₀ _ hsub, ← tsum_mul_left]
      refine tsum_congr fun j => ?_
      rw [← integral_const_mul]
      congr 1
      funext g
      rw [show (1 + q * emaW β j ^ 2 * g ^ 2) = 1 + emaW β j ^ 2 * q * g ^ 2 by ring,
        show (1 + β ^ (2 * ℓ) * q' * emaW β j ^ 2 * g ^ 2)
          = 1 + emaW β j ^ 2 * (β ^ (2 * ℓ) * q') * g ^ 2 by ring]
      ring
    · unfold eLag
      rw [hF, mul_left_comm (β ^ (2 * ℓ)), mul_div_cancel_left₀ _ hsub', ← tsum_mul_left]
      refine tsum_congr fun j => ?_
      rw [← integral_const_mul]
      congr 1
      funext g
      rw [show (1 + q * emaW β j ^ 2 * g ^ 2) = 1 + emaW β j ^ 2 * q * g ^ 2 by ring,
        show (1 + β ^ (2 * ℓ) * q' * emaW β j ^ 2 * g ^ 2)
          = 1 + emaW β j ^ 2 * (β ^ (2 * ℓ) * q') * g ^ 2 by ring]
      ring
  · intro hEq
    have hRd := (lem_app_de_scalar_iii hw).2.2.2.1 q hq
    have hFeq : Fw (emaW β) =ᶠ[𝓝 q] fun x => rW (emaW β) x / x := by
      filter_upwards [Ioi_mem_nhds hq] with x hx
      show Fw (emaW β) x = rW (emaW β) x / x
      rw [rW, mul_div_cancel_left₀ _ (Set.mem_Ioi.1 hx).ne']
    have hS : deriv (Fw (emaW β)) q = -∑' j : ℕ, ∫ g : ℝ,
        (emaW β j ^ 2) ^ 2 * g ^ 4 / (1 + emaW β j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1) := by
      have hdiv := hRd.div (hasDerivAt_id' q) hq.ne'
      have hFd := hdiv.congr_of_eventuallyEq hFeq
      have hU : Summable (fun j : ℕ => ∫ g : ℝ, emaW β j ^ 2 * q * g ^ 2 /
          (1 + emaW β j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1)) :=
        P7_summ_gen (fun j => emaW β j ^ 2 * q) (fun j => emaW β j ^ 2 * q)
          (fun j => mul_nonneg (sq_nonneg _) hq.le) (fun j => mul_nonneg (sq_nonneg _) hq.le)
          (hsumm.mul_right q) 2
      have hDq : (∑' j : ℕ, emaW β j ^ 2 * ∫ g : ℝ, g ^ 2 / (1 + emaW β j ^ 2 * q * g ^ 2) ^ 2
          ∂(gaussianReal 0 1)) * q
          = ∑' j : ℕ, ∫ g : ℝ, emaW β j ^ 2 * q * g ^ 2 /
            (1 + emaW β j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1) := by
        rw [← tsum_mul_right]
        refine tsum_congr fun j => ?_
        rw [← integral_const_mul, ← integral_mul_const]
        congr 1
        funext g
        ring
      have hsplit : (∑' j : ℕ, ∫ g : ℝ, emaW β j ^ 2 * q * g ^ 2 /
            (1 + emaW β j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1))
          - ∑' j : ℕ, ∫ g : ℝ, emaW β j ^ 2 * q * g ^ 2 /
            (1 + emaW β j ^ 2 * q * g ^ 2) ∂(gaussianReal 0 1)
          = -(q ^ 2 * ∑' j : ℕ, ∫ g : ℝ, (emaW β j ^ 2) ^ 2 * g ^ 4 /
            (1 + emaW β j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1)) := by
        rw [← Summable.tsum_sub hU hSq, tsum_congr (fun j => P7_pt_coinc (a := emaW β j ^ 2) (q := q)
          (sq_nonneg _) hq.le), tsum_neg, tsum_mul_left]
      have hD : deriv (Fw (emaW β)) q = ((∑' j : ℕ, emaW β j ^ 2 *
          ∫ g : ℝ, g ^ 2 / (1 + emaW β j ^ 2 * q * g ^ 2) ^ 2 ∂(gaussianReal 0 1)) * q
          - rW (emaW β) q * 1) / q ^ 2 := hFd.deriv
      rw [hD, mul_one, hDq, (lem_app_de_scalar_iii hw).1 q hq.le, hsplit, neg_div,
        mul_div_cancel_left₀ _ (pow_ne_zero 2 hq.ne')]
    refine ⟨?_, ?_⟩
    · unfold bLag
      rw [hRd.deriv, ← tsum_mul_left, ← hEq]
      refine tsum_congr fun j => ?_
      rw [← integral_const_mul, ← integral_const_mul]
      congr 1
      funext g
      rw [show (1 + q * emaW β j ^ 2 * g ^ 2) = 1 + emaW β j ^ 2 * q * g ^ 2 by ring]
      ring
    · unfold eLag
      rw [hS, mul_neg, neg_neg, ← tsum_mul_left, ← hEq]
      refine tsum_congr fun j => ?_
      rw [← integral_const_mul]
      congr 1
      funext g
      rw [show (1 + q * emaW β j ^ 2 * g ^ 2) = 1 + emaW β j ^ 2 * q * g ^ 2 by ring]
      ring

end Muon.PowerLaw

end

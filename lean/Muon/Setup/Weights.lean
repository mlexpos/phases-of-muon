import Muon.Foundations.Conventions

/-!
# Appendix A: EMA weight identities

Snapshot `cr-2026-10-23`. Source: `sections/01-setup/section.tex`: `eqn:app-setup-weights`
(l.451–455), the scalar content of `lem:app-setup-ema-law`(v) (l.748–756),
`prop:app-setup-startup` (l.819–827) and `lem:app-setup-truncation`(i) (l.872–873). Card:
`sections/01-setup/CARD.md` §5 row L-A.6.

The weights `emaW`, the power sums `sPow`, and the three identities of `eqn:app-setup-weights`
(`tsum_emaW`, `sPow_eq`, `sPow_two`) are shared and live in `Muon.Foundations.Conventions`.
They are not redefined here: this module re-exports them as the declarations of record
`eqn_app_setup_weights_{i,ii,iii}`, and adds the finite-sum, tail and limit identities that the
stationary-law, startup and truncation statements use. Every helper below is a real-number identity
in `β` (and `T`, `t`, `J`); none is a probabilistic statement.
-/

noncomputable section

open Filter Topology

namespace Muon.Setup

/-- `eqn:app-setup-weights` (snapshot `cr-2026-10-23`, part (i)).

Declaration of record of the first identity. The statement is `tsum_emaW` in `Muon.Foundations.Conventions`, re-exported here without a second proof.

LaTeX (`section.tex` l.451–455):
```latex
\begin{equation}\label{eqn:app-setup-weights}
\sum_{j\ge0}\emaw{j}=1,\qquad
\sw{p}\defeq\sum_{j\ge0}\emaw{j}^p=\frac{(1-\bmom)^p}{1-\bmom^p}\quad(p\ge2),\qquad
\sw{2}=\frac{1-\bmom}{1+\bmom}.
\end{equation}
```
-/
theorem eqn_app_setup_weights_i {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∑' j : ℕ, emaW β j = 1 :=
  tsum_emaW hβ0 hβ1

/-- `eqn:app-setup-weights` (snapshot `cr-2026-10-23`, part (ii)).

Declaration of record of the power-sum closed form, `p ≥ 2`. Re-export of `sPow_eq`.

LaTeX (`section.tex` l.451–455):
```latex
\begin{equation}\label{eqn:app-setup-weights}
\sum_{j\ge0}\emaw{j}=1,\qquad
\sw{p}\defeq\sum_{j\ge0}\emaw{j}^p=\frac{(1-\bmom)^p}{1-\bmom^p}\quad(p\ge2),\qquad
\sw{2}=\frac{1-\bmom}{1+\bmom}.
\end{equation}
```
-/
theorem eqn_app_setup_weights_ii {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {p : ℕ} (hp : 2 ≤ p) :
    sPow β p = (1 - β) ^ p / (1 - β ^ p) :=
  sPow_eq hβ0 hβ1 hp

/-- `eqn:app-setup-weights` (snapshot `cr-2026-10-23`, part (iii)).

Declaration of record of `S_2(β)`. Re-export of `sPow_two`.

LaTeX (`section.tex` l.451–455):
```latex
\begin{equation}\label{eqn:app-setup-weights}
\sum_{j\ge0}\emaw{j}=1,\qquad
\sw{p}\defeq\sum_{j\ge0}\emaw{j}^p=\frac{(1-\bmom)^p}{1-\bmom^p}\quad(p\ge2),\qquad
\sw{2}=\frac{1-\bmom}{1+\bmom}.
\end{equation}
```
-/
theorem eqn_app_setup_weights_iii {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    sPow β 2 = (1 - β) / (1 + β) :=
  sPow_two hβ0 hβ1

private lemma ema_geom_mul (β : ℝ) (T : ℕ) :
    (1 - β) * ∑ ℓ ∈ Finset.range T, β ^ ℓ = 1 - β ^ T := by
  induction T with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, mul_add, ih, pow_succ]; ring

private lemma ema_A_rec (β : ℝ) (T : ℕ) :
    ∑ ℓ ∈ Finset.range (T + 1), (((T + 1 : ℕ) : ℝ) - (ℓ : ℝ)) * β ^ ℓ
      = ∑ ℓ ∈ Finset.range T, ((T : ℝ) - (ℓ : ℝ)) * β ^ ℓ
        + ∑ ℓ ∈ Finset.range (T + 1), β ^ ℓ := by
  have h : ∀ ℓ ∈ Finset.range T, (((T + 1 : ℕ) : ℝ) - (ℓ : ℝ)) * β ^ ℓ
      = ((T : ℝ) - (ℓ : ℝ)) * β ^ ℓ + β ^ ℓ := by
    intro ℓ _
    push_cast
    ring
  rw [Finset.sum_range_succ, Finset.sum_congr rfl h, Finset.sum_add_distrib,
    Finset.sum_range_succ (fun ℓ => β ^ ℓ) T]
  push_cast
  ring

private lemma ema_A_closed (β : ℝ) (T : ℕ) :
    (1 - β) ^ 2 * ∑ ℓ ∈ Finset.range T, ((T : ℝ) - (ℓ : ℝ)) * β ^ ℓ
      = (1 - β) * (T : ℝ) - β * (1 - β ^ T) := by
  induction T with
  | zero => simp
  | succ n ih =>
    have hG := ema_geom_mul β (n + 1)
    rw [ema_A_rec, mul_add, ih]
    push_cast
    linear_combination (1 - β) * hG

private lemma ema_range_split (β : ℝ) (T : ℕ) :
    ∑ ℓ ∈ Finset.range T, ((T : ℝ) - (ℓ : ℝ)) * β ^ ℓ
      = (T : ℝ) + ∑ ℓ ∈ Finset.Ico 1 T, ((T : ℝ) - (ℓ : ℝ)) * β ^ ℓ := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp
  · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hT]
    simp

/-- Scalar identity behind `lem:app-setup-ema-law`(v), the finite-`T` covariance of the buffer sum (`eqn:app-setup-block-cov`, cr-2026-10-23). Stated for `0 < T`. Source: l.748–753.

\item For every positive integer $T$,
\begin{equation}\label{eqn:app-setup-block-cov}
\Cov\Big(\sum_{t=1}^T\operatorname{vec}(\Mt-\EE\Gt)\Big)
=\sw2\Big[T+2\sum_{\ell=1}^{T-1}(T-\ell)\bmom^\ell\Big]\Sigma_G
=\Big[T-\frac{2\bmom(1-\bmom^T)}{1-\bmom^2}\Big]\Sigma_G ,
\end{equation} -/
theorem ema_block_scalar {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {T : ℕ} (hT : 0 < T) :
    sPow β 2 * ((T : ℝ) + 2 * ∑ ℓ ∈ Finset.Ico 1 T, ((T : ℝ) - (ℓ : ℝ)) * β ^ ℓ)
      = (T : ℝ) - 2 * β * (1 - β ^ T) / (1 - β ^ 2) := by
  have hA := ema_A_closed β T
  rw [ema_range_split β T] at hA
  have hne1 : (1 - β) ≠ 0 := by intro h; linarith
  have hne2 : (1 + β) ≠ 0 := by intro h; linarith
  have hne3 : (1 - β ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 - β ^ 2 := by nlinarith
    exact this.ne'
  have hX : (T : ℝ) + 2 * ∑ ℓ ∈ Finset.Ico 1 T, ((T : ℝ) - (ℓ : ℝ)) * β ^ ℓ
      = ((1 - β) * (1 + β) * (T : ℝ) - 2 * β * (1 - β ^ T)) / (1 - β) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hne1)]
    linear_combination 2 * hA
  rw [sPow_two hβ0 hβ1, hX]
  field_simp
  ring

/-- Limit part of `lem:app-setup-ema-law`(v): the scalar form of `T^{-1}Cov(∑_{t≤T}vec(M_t−EG_t)) → Σ_G` (cr-2026-10-23). Source: l.756.

$T^{-1}\Cov(\sum_{t\le T}\operatorname{vec}(\Mt-\EE\Gt))\to\Sigma_G$ as $T\to\infty$. -/
theorem ema_block_scalar_tendsto {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Tendsto (fun T : ℕ => ((T : ℝ))⁻¹ *
        (sPow β 2 * ((T : ℝ) + 2 * ∑ ℓ ∈ Finset.Ico 1 T, ((T : ℝ) - (ℓ : ℝ)) * β ^ ℓ)))
      atTop (𝓝 1) := by
  have hne3 : (1 - β ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 - β ^ 2 := by nlinarith
    exact this.ne'
  have hpow : Tendsto (fun T : ℕ => β ^ T) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1
  have hinv : Tendsto (fun T : ℕ => ((T : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun T : ℕ => 1 - (2 * β / (1 - β ^ 2)) * ((1 - β ^ T) * ((T : ℝ))⁻¹))
      atTop (𝓝 (1 - (2 * β / (1 - β ^ 2)) * ((1 - 0) * 0))) :=
    (tendsto_const_nhds.sub
      ((((tendsto_const_nhds (x := (1 : ℝ))).sub hpow).mul hinv).const_mul _))
  rw [show (1 : ℝ) - (2 * β / (1 - β ^ 2)) * ((1 - 0) * 0) = 1 by ring] at hlim
  refine Tendsto.congr' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hTne : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [ema_block_scalar hβ0 hβ1 (by omega : 0 < T)]
  field_simp

/-- Scalar part of the two-sided lag sum in `lem:app-setup-ema-law`(v): `∑_{ℓ∈ℤ} β^{|ℓ|} S_2(β) = 1` (cr-2026-10-23). Source: l.754–755.

the two-sided lag sum $\sum_{\ell\in\mathbb Z}\Cov(\operatorname{vec}\Mt,\operatorname{vec}M_{t+\ell})$
converges absolutely and equals $\Sigma_G$, and -/
theorem ema_two_sided_lag_scalar {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    HasSum (fun ℓ : ℤ => β ^ ℓ.natAbs * sPow β 2) 1 := by
  have hne1 : (1 - β) ≠ 0 := by intro h; linarith
  have hne2 : (1 + β) ≠ 0 := by intro h; linarith
  have hg : HasSum (fun n : ℕ => β ^ n) (1 - β)⁻¹ := hasSum_geometric_of_lt_one hβ0 hβ1
  have hnat : ∀ n : ℕ, ((n : ℤ)).natAbs = n := fun n => Int.natAbs_natCast n
  have hneg : ∀ n : ℕ, (-((n : ℤ) + 1)).natAbs = n + 1 := fun n => by omega
  have h1 : HasSum (fun n : ℕ => β ^ ((n : ℤ)).natAbs * sPow β 2) ((1 - β)⁻¹ * sPow β 2) := by
    have e : (fun n : ℕ => β ^ ((n : ℤ)).natAbs * sPow β 2) = fun n : ℕ => β ^ n * sPow β 2 := by
      funext n; rw [hnat n]
    rw [e]
    exact hg.mul_right (sPow β 2)
  have h2 : HasSum (fun n : ℕ => β ^ (-((n : ℤ) + 1)).natAbs * sPow β 2)
      (β * ((1 - β)⁻¹ * sPow β 2)) := by
    have e : (fun n : ℕ => β ^ (-((n : ℤ) + 1)).natAbs * sPow β 2)
        = fun n : ℕ => β * (β ^ n * sPow β 2) := by
      funext n; rw [hneg n, pow_succ]; ring
    rw [e]
    exact (hg.mul_right (sPow β 2)).mul_left β
  have h : HasSum (fun ℓ : ℤ => β ^ ℓ.natAbs * sPow β 2)
      ((1 - β)⁻¹ * sPow β 2 + β * ((1 - β)⁻¹ * sPow β 2)) :=
    HasSum.of_nat_of_neg_add_one (f := fun ℓ : ℤ => β ^ ℓ.natAbs * sPow β 2) h1 h2
  have hval : (1 - β)⁻¹ * sPow β 2 + β * ((1 - β)⁻¹ * sPow β 2) = 1 := by
    rw [sPow_two hβ0 hβ1]
    field_simp
  rw [hval] at h
  exact h

/-- Finite weight sum at startup, `prop:app-setup-startup` (cr-2026-10-23). The mean of `M_t^K` uses `∑_{j≤t} w_j = 1 − β^{t+1}`. Source: l.819–825.

\begin{equation}\label{eqn:app-setup-startup}
\begin{gathered}
M_t^K=\bmom^{t+1}K+\sum_{j=0}^t\emaw{j}G_{t+1-j},\qquad
\EE M_t^K=\bmom^{t+1}K+(1-\bmom^{t+1})\,\EE\Gt,\\
\Cov(\operatorname{vec}M_t^K)=\sw2\big(1-\bmom^{2(t+1)}\big)\Sigma_G .
\end{gathered}
\end{equation} -/
theorem startup_weight_sum {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (t : ℕ) :
    ∑ j ∈ Finset.range (t + 1), emaW β j = 1 - β ^ (t + 1) := by
  simp only [emaW]
  rw [← Finset.mul_sum]
  exact ema_geom_mul β (t + 1)

/-- Finite squared-weight sum at startup, `prop:app-setup-startup` (cr-2026-10-23): `∑_{j≤t} w_j² = S_2(β)(1 − β^{2(t+1)})`. Source: l.819–825.

\begin{equation}\label{eqn:app-setup-startup}
\begin{gathered}
M_t^K=\bmom^{t+1}K+\sum_{j=0}^t\emaw{j}G_{t+1-j},\qquad
\EE M_t^K=\bmom^{t+1}K+(1-\bmom^{t+1})\,\EE\Gt,\\
\Cov(\operatorname{vec}M_t^K)=\sw2\big(1-\bmom^{2(t+1)}\big)\Sigma_G .
\end{gathered}
\end{equation} -/
theorem startup_weight_sq_sum {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (t : ℕ) :
    ∑ j ∈ Finset.range (t + 1), emaW β j ^ 2 = sPow β 2 * (1 - β ^ (2 * (t + 1))) := by
  have h2 : sPow β 2 = (1 - β) / (1 + β) := sPow_two hβ0 hβ1
  have hne : (1 + β) ≠ 0 := by intro h; linarith
  have hg := ema_geom_mul (β ^ 2) (t + 1)
  have hX : (β ^ 2) ^ (t + 1) = β ^ (2 * (t + 1)) := (pow_mul β 2 (t + 1)).symm
  rw [hX] at hg
  have hsum : ∑ j ∈ Finset.range (t + 1), emaW β j ^ 2
      = (1 - β) ^ 2 * ∑ ℓ ∈ Finset.range (t + 1), (β ^ 2) ^ ℓ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [emaW]
    ring
  rw [hsum, h2, div_mul_eq_mul_div, eq_div_iff hne]
  linear_combination (1 - β) * hg

/-- Bias-correction variance at startup, `prop:app-setup-startup` (cr-2026-10-23): the covariance factor of `M̃_t = M_t^0/(1−β^{t+1})` equals `S_2(β)(1+β^{t+1})/(1−β^{t+1})`. Source: l.826–827.

The bias-corrected zero-start buffer $\widetilde M_t\defeq M_t^0/(1-\bmom^{t+1})$
has mean $\EE\Gt$ and covariance $\sw2\,\frac{1+\bmom^{t+1}}{1-\bmom^{t+1}}\Sigma_G$. -/
theorem startup_bias_corrected_variance_scalar {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (t : ℕ) :
    sPow β 2 * (1 - β ^ (2 * (t + 1))) / (1 - β ^ (t + 1)) ^ 2
      = sPow β 2 * (1 + β ^ (t + 1)) / (1 - β ^ (t + 1)) := by
  have hu : β ^ (2 * (t + 1)) = (β ^ (t + 1)) ^ 2 := by ring
  have hlt : β ^ (t + 1) < 1 := pow_lt_one₀ hβ0 hβ1 (by omega)
  have hne1 : (1 - β ^ (t + 1)) ≠ 0 := by intro h; linarith
  have hne2 : (1 - β ^ (t + 1)) ^ 2 ≠ 0 := pow_ne_zero 2 hne1
  rw [hu, div_eq_div_iff hne2 hne1]
  ring

/-- Tail weight sum of `lem:app-setup-truncation`(i), `∑_{j>J} w_j = β^{J+1}` (cr-2026-10-23). Source: l.872–873.

\item $\EE\big(\Mt-M^{(J)}\big)=\bmom^{J+1}\,\EE\Gt$ and
$\EE\norm{\Mt-M^{(J)}}_\F^2=\bmom^{2(J+1)}\big(\norm{\EE\Gt}_\F^2+\sw2\mathsf V_B\big)$. -/
theorem truncation_tail_weight_sum {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (J : ℕ) :
    ∑' j : ℕ, (if J < j then emaW β j else 0) = β ^ (J + 1) := by
  have hs1 : Summable (fun j : ℕ => emaW β j) :=
    (summable_geometric_of_lt_one hβ0 hβ1).mul_left (1 - β)
  have hg : Summable (fun j : ℕ => if j < J + 1 then emaW β j else 0) :=
    summable_of_ne_finset_zero (s := Finset.range (J + 1)) (fun j hj => by
      have : ¬ j < J + 1 := by simpa using hj
      simp [this])
  have key : (fun j : ℕ => if J < j then emaW β j else 0)
      = fun j => emaW β j - (if j < J + 1 then emaW β j else 0) := by
    funext j
    by_cases h : J < j
    · have h' : ¬ j < J + 1 := by omega
      simp [h, h']
    · have h' : j < J + 1 := by omega
      simp [h, h']
  have hfin : ∑' j : ℕ, (if j < J + 1 then emaW β j else 0)
      = ∑ j ∈ Finset.range (J + 1), emaW β j := by
    rw [tsum_eq_sum (s := Finset.range (J + 1)) (fun j hj => by
      have : ¬ j < J + 1 := by simpa using hj
      simp [this])]
    exact Finset.sum_congr rfl (fun j hj => by
      have : j < J + 1 := Finset.mem_range.1 hj
      simp [this])
  rw [key, Summable.tsum_sub hs1 hg, tsum_emaW hβ0 hβ1, hfin, startup_weight_sum hβ0 hβ1 J]
  ring

/-- Tail squared-weight sum of `lem:app-setup-truncation`(i), `∑_{j>J} w_j² = S_2(β) β^{2(J+1)}` (cr-2026-10-23). Source: l.872–873.

\item $\EE\big(\Mt-M^{(J)}\big)=\bmom^{J+1}\,\EE\Gt$ and
$\EE\norm{\Mt-M^{(J)}}_\F^2=\bmom^{2(J+1)}\big(\norm{\EE\Gt}_\F^2+\sw2\mathsf V_B\big)$. -/
theorem truncation_tail_weight_sq_sum {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (J : ℕ) :
    ∑' j : ℕ, (if J < j then emaW β j ^ 2 else 0) = sPow β 2 * β ^ (2 * (J + 1)) := by
  have hs2 : Summable (fun j : ℕ => emaW β j ^ 2) := by
    have h := (summable_geometric_of_lt_one (sq_nonneg β)
      (by nlinarith : β ^ 2 < 1)).mul_left ((1 - β) ^ 2)
    refine h.congr (fun j => ?_)
    simp only [emaW]
    ring
  have hg : Summable (fun j : ℕ => if j < J + 1 then emaW β j ^ 2 else 0) :=
    summable_of_ne_finset_zero (s := Finset.range (J + 1)) (fun j hj => by
      have : ¬ j < J + 1 := by simpa using hj
      simp [this])
  have key : (fun j : ℕ => if J < j then emaW β j ^ 2 else 0)
      = fun j => emaW β j ^ 2 - (if j < J + 1 then emaW β j ^ 2 else 0) := by
    funext j
    by_cases h : J < j
    · have h' : ¬ j < J + 1 := by omega
      simp [h, h']
    · have h' : j < J + 1 := by omega
      simp [h, h']
  have hfin : ∑' j : ℕ, (if j < J + 1 then emaW β j ^ 2 else 0)
      = ∑ j ∈ Finset.range (J + 1), emaW β j ^ 2 := by
    rw [tsum_eq_sum (s := Finset.range (J + 1)) (fun j hj => by
      have : ¬ j < J + 1 := by simpa using hj
      simp [this])]
    exact Finset.sum_congr rfl (fun j hj => by
      have : j < J + 1 := Finset.mem_range.1 hj
      simp [this])
  have hS : ∑' j : ℕ, emaW β j ^ 2 = sPow β 2 := rfl
  rw [key, Summable.tsum_sub hs2 hg, hS, hfin, startup_weight_sq_sum hβ0 hβ1 J]
  ring

end Muon.Setup

end

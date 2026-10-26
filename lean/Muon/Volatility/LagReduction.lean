import Muon.Volatility.Defs
import Muon.Dynamics.Basic
import Muon.Setup.Truncation

/-!
# Appendix D, work package L-D.10a: lag summation and lag reduction (i)–(iii)

Snapshot `cr-2026-10-23`. Source: `sections/04-volatility/section.tex`: `thm:app-vol-lag-reduction`
(l.866–894, parts (i)–(iii)) and `lem:app-vol-lagsum` (l.904–910). Card:
`sections/04-volatility/CARD.md` §2, §3 and the L-D.10a row of §5. Part (iv) of the theorem and
its proof are work package L-D.10b, not stated here.

Reused, not redefined: `Muon.Volatility.FrozenParams`-level objects `centredUpd`, `def_app_vol_lag`,
`integratedLag`, `indepUpd`, `indepSpaceLaw`, `SizeFin` (`Muon.Volatility.Defs`, which imports
`Muon.Setup.Frozen`); `Muon.Dynamics.kStar` (`eqn:app-vol-K`, `Muon.Dynamics.Basic`); `Muon.opNorm`.

Encoding decisions:
* Fixed dimension, as in the source statement. The regime is the hypothesis bundle `hS`, `hCSig`,
  `hϱ` and the membership `ϱ, ϱ' ∈ [ϱ₋, ϱ₊]`. No limit appears in (i)–(iii).
* `K_⋆` is `kStar CSig γstar ϱlo` (its `ϱ₋` argument is the lower end of the regime interval).
* (i)–(iii) are stated for every time `t : ℤ`. The source's `C_ℓ` carries no time; its
  stationarity is the ema-law, which the statement does not assume.
* The left side of `eqn:app-vol-finite-time` is the helper `finiteTimeCov`. The independent
  covariances `C^g_ℓ` of `cor:app-vol-filtered-replacement` are written inline in (ii) (no
  definition is made here; L-D.7 owns that corollary).
* `lem:app-vol-lagsum` takes the dimension index `k : ℕ` and parameter sets `PP k`. "`sup_p → 0`" is
  read as `∀ ε > 0, ∀ᶠ k, ∀ p ∈ PP k, |…| ≤ ε`. The momentum `β ∈ [0,1)` is an explicit hypothesis:
  the source states no range, but its proof divides by `1 − β`.
-/

noncomputable section

open scoped Matrix MatrixOrder
open MeasureTheory ProbabilityTheory Filter Topology
open Muon Muon.Setup

namespace Muon.Volatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}

/-! ## The left side of the finite-time identity -/

/-- Finite-time tested second moment `(1/(BT)) 𝔼 Tr[F S_T(ϱ) G S_T(ϱ')ᵀ]` with
`S_T(ϱ) = ∑_{t'=1}^T S^c_{t'}(ϱ)`: the left side of `eqn:app-vol-finite-time` (helper, not a
labelled declaration). -/
def finiteTimeCov (F : FrozenParams m n B) (S : FrozenSamples P m n B) (T : ℕ) (ϱ ϱ' : ℝ)
    (Fo : Mat m m) (Gi : Mat n n) : ℝ :=
  ((B : ℝ) * (T : ℝ))⁻¹ * ∫ ω,
    Matrix.trace (Fo * (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), centredUpd F S ϱ s ω) * Gi *
      (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), centredUpd F S ϱ' s ω)ᵀ) ∂P

/-! ## Lag summation -/

/-- Helper (private, fully proved): a real sequence dominated by `c β^ℓ` for `ℓ ≥ 1` is summable
and its tail after the first `L ≥ 1` terms is at most `c β^L/(1-β)`. -/
private lemma lagsum_tail_aux (g : ℕ → ℝ) (c β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hg : ∀ ℓ : ℕ, 1 ≤ ℓ → |g ℓ| ≤ c * β ^ ℓ) (L : ℕ) (hL : 1 ≤ L) :
    Summable g ∧ |∑' ℓ, g ℓ - ∑ ℓ ∈ Finset.range L, g ℓ| ≤ c * β ^ L / (1 - β) := by
  have hgeo : Summable fun n : ℕ => c * β ^ n :=
    (summable_geometric_of_lt_one hβ0 hβ1).mul_left c
  have hsh : Summable fun n : ℕ => g (n + 1) :=
    Summable.of_norm_bounded ((summable_nat_add_iff 1).2 hgeo)
      (fun i => by rw [Real.norm_eq_abs]; exact hg (i + 1) (by omega))
  have hsumg : Summable g := (summable_nat_add_iff 1).1 hsh
  have hdec : ∑ ℓ ∈ Finset.range L, g ℓ + ∑' i : ℕ, g (i + L) = ∑' ℓ, g ℓ :=
    hsumg.sum_add_tsum_nat_add L
  have hh : Summable fun i : ℕ => g (i + L) := (summable_nat_add_iff L).2 hsumg
  have hgeo' : Summable fun i : ℕ => c * β ^ L * β ^ i :=
    (summable_geometric_of_lt_one hβ0 hβ1).mul_left (c * β ^ L)
  have hbd : ∀ i : ℕ, ‖g (i + L)‖ ≤ c * β ^ L * β ^ i := by
    intro i
    rw [Real.norm_eq_abs, show c * β ^ L * β ^ i = c * β ^ (i + L) by ring]
    exact hg (i + L) (by omega)
  have habs : Summable fun i : ℕ => ‖g (i + L)‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hbd hgeo'
  have htail : ‖∑' i : ℕ, g (i + L)‖ ≤ c * β ^ L * (1 - β)⁻¹ := by
    have h1 : ‖∑' i : ℕ, g (i + L)‖ ≤ ∑' i : ℕ, ‖g (i + L)‖ := norm_tsum_le_tsum_norm habs
    have h2 : ∑' i : ℕ, ‖g (i + L)‖ ≤ ∑' i : ℕ, c * β ^ L * β ^ i :=
      Summable.tsum_le_tsum hbd habs hgeo'
    have h3 : ∑' i : ℕ, c * β ^ L * β ^ i = c * β ^ L * (1 - β)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hβ0 hβ1]
    linarith
  refine ⟨hsumg, ?_⟩
  have hEq : ∑' ℓ, g ℓ - ∑ ℓ ∈ Finset.range L, g ℓ = ∑' i : ℕ, g (i + L) := by linarith
  rw [hEq, ← Real.norm_eq_abs, div_eq_mul_inv]
  exact htail


/-- `lem:app-vol-lagsum`, snapshot `cr-2026-10-23`. Declaration of record for this part. The
statement, verbatim from `section.tex` (header and this part of the theorem):
```latex
\begin{lemma}[Lag summation]\label{lem:app-vol-lagsum}
For each dimension let $(a_\ell(p))_{\ell\ge0}$ and $(b_\ell(p))_{\ell\ge0}$ be
real sequences indexed by a parameter $p$ in a set $\mathcal P$, with
$\abs{a_\ell(p)}+\abs{b_\ell(p)}\le K\bmom^\ell$ for $\ell\ge1$, uniformly in $p$
and in the dimension, and with $\sup_{p\in\mathcal P}\abs{a_\ell(p)-b_\ell(p)}\to0$
for every fixed $\ell\ge0$. Then $\sup_{p\in\mathcal P}\abs{\sum_{\ell\ge0}(a_\ell(p)-b_\ell(p))}\to0$.
\end{lemma}
```
The lemma holds for every dimension, and for each parameter `p` the series is summable by the
geometric bound; `β` is the regime momentum, required to lie in `[0,1)` (the proof divides by `1 −
β`). Sorried: proof card P1.
-/
theorem lem_app_vol_lagsum {ι : Type*} (PP : ℕ → Set ι) (a b : ℕ → ℕ → ι → ℝ) (K β : ℝ)
    (hβ : 0 ≤ β ∧ β < 1)
    (hbd : ∀ k : ℕ, ∀ p ∈ PP k, ∀ ℓ : ℕ, 1 ≤ ℓ → |a k ℓ p| + |b k ℓ p| ≤ K * β ^ ℓ)
    (hlim : ∀ ℓ : ℕ, ∀ ε > 0, ∀ᶠ k in atTop, ∀ p ∈ PP k, |a k ℓ p - b k ℓ p| ≤ ε) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ p ∈ PP k, |∑' ℓ : ℕ, (a k ℓ p - b k ℓ p)| ≤ ε := by
  intro ε hε
  obtain ⟨hβ0, hβ1⟩ := hβ
  -- truncation point L ≥ 1 with geometric tail below ε/3
  have hpow : Tendsto (fun L : ℕ => |K| * β ^ L / (1 - β)) atTop (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).const_mul |K|).div_const (1 - β)
    simpa using h
  obtain ⟨L, hLε, hL1⟩ := ((hpow.eventually (gt_mem_nhds (by positivity : (0:ℝ) < ε / 3))).and
    (eventually_ge_atTop 1)).exists
  -- head tolerance δ, so that the L head terms sum to at most ε/3
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε / (3 * ((L : ℝ) + 1)) := ⟨_, rfl⟩
  have hLpos : (L : ℝ) + 1 ≠ 0 := by positivity
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hLδ : ((L : ℝ) + 1) * δ = ε / 3 := by rw [hδdef]; field_simp
  have hhead_ev : ∀ᶠ k in atTop, ∀ ℓ ∈ Finset.range L, ∀ p ∈ PP k,
      |a k ℓ p - b k ℓ p| ≤ δ :=
    (Filter.eventually_all_finset (Finset.range L)).2 (fun ℓ _ => hlim ℓ δ hδpos)
  filter_upwards [hhead_ev] with k hk
  intro p hp
  have hgb : ∀ ℓ : ℕ, 1 ≤ ℓ → |a k ℓ p - b k ℓ p| ≤ |K| * β ^ ℓ := fun ℓ hℓ =>
    (abs_sub _ _).trans ((hbd k p hp ℓ hℓ).trans
      (mul_le_mul_of_nonneg_right (le_abs_self K) (pow_nonneg hβ0 ℓ)))
  obtain ⟨_, htail⟩ := lagsum_tail_aux (fun ℓ => a k ℓ p - b k ℓ p) |K| β hβ0 hβ1 hgb L hL1
  have htail' : |∑' ℓ, (a k ℓ p - b k ℓ p) - ∑ ℓ ∈ Finset.range L, (a k ℓ p - b k ℓ p)| ≤ ε / 3 :=
    le_trans htail hLε.le
  have hhead : |∑ ℓ ∈ Finset.range L, (a k ℓ p - b k ℓ p)| ≤ ε / 3 := by
    calc |∑ ℓ ∈ Finset.range L, (a k ℓ p - b k ℓ p)|
        ≤ ∑ ℓ ∈ Finset.range L, |a k ℓ p - b k ℓ p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ℓ ∈ Finset.range L, δ := Finset.sum_le_sum (fun ℓ hℓ => hk ℓ hℓ p hp)
      _ = (L : ℝ) * δ := by simp
      _ ≤ ε / 3 := by nlinarith
  have hsplit : ∑' ℓ, (a k ℓ p - b k ℓ p) = ∑ ℓ ∈ Finset.range L, (a k ℓ p - b k ℓ p) +
      (∑' ℓ, (a k ℓ p - b k ℓ p) - ∑ ℓ ∈ Finset.range L, (a k ℓ p - b k ℓ p)) := by ring
  rw [hsplit]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ ε / 3 + ε / 3 := add_le_add hhead htail'
    _ ≤ ε := by linarith

/-! ## Lag reduction, parts (i)–(iii) -/

private lemma lr_fro_nn {k l : ℕ} (A : Mat k l) : 0 ≤ fro A := Real.sqrt_nonneg _

private lemma lr_fro_transpose {k l : ℕ} (A : Mat k l) : fro Aᵀ = fro A := by
  unfold fro
  congr 1
  exact Finset.sum_comm

private lemma lr_opNorm_transpose {k l : ℕ} (A : Mat k l) : opNorm Aᵀ = opNorm A := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

private lemma lr_opNorm_nonneg {k l : ℕ} (A : Mat k l) : 0 ≤ opNorm A := by
  unfold opNorm
  exact norm_nonneg _

private lemma lr_fro_sq {k l : ℕ} (A : Mat k l) : fro A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma lr_fro_mul_le_left {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ opNorm M * fro N := by
  have hcol : ∀ j : Fin r, ∑ i, (M * N) i j ^ 2 ≤ opNorm M ^ 2 * ∑ k, N k j ^ 2 := by
    intro j
    obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin q), ∀ k, v.ofLp k = N k j :=
      ⟨(EuclideanSpace.equiv (Fin q) ℝ).symm (fun k => N k j), fun k => rfl⟩
    have h1 : ‖(EuclideanSpace.equiv (Fin p) ℝ).symm (M *ᵥ v)‖ ≤ opNorm M * ‖v‖ := by
      rw [opNorm_eq_norm]
      exact Matrix.l2_opNorm_mulVec M v
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at h2
    have e1 : ∀ i, ((EuclideanSpace.equiv (Fin p) ℝ).symm (M *ᵥ v)).ofLp i = (M * N) i j := by
      intro i
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, hv]
    have e2 : ∑ k, v.ofLp k ^ 2 = ∑ k, N k j ^ 2 :=
      Finset.sum_congr rfl fun k _ => by rw [hv]
    simp only [e1, e2] at h2
    exact h2
  have hfro : fro (M * N) ^ 2 ≤ (opNorm M * fro N) ^ 2 := by
    rw [lr_fro_sq, mul_pow, lr_fro_sq, Finset.sum_comm]
    calc ∑ j, ∑ i, (M * N) i j ^ 2 ≤ ∑ j : Fin r, opNorm M ^ 2 * ∑ k, N k j ^ 2 :=
          Finset.sum_le_sum fun j _ => hcol j
      _ = opNorm M ^ 2 * ∑ k, ∑ j, N k j ^ 2 := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
  exact (pow_le_pow_iff_left₀ (lr_fro_nn _) (mul_nonneg (lr_opNorm_nonneg M) (lr_fro_nn N))
    two_ne_zero).mp hfro

private lemma lr_fro_mul_le_right {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ fro M * opNorm N := by
  have h := lr_fro_mul_le_left Nᵀ Mᵀ
  rw [lr_opNorm_transpose, lr_fro_transpose, ← Matrix.transpose_mul, lr_fro_transpose] at h
  linarith [mul_comm (opNorm N) (fro M)]

private lemma lr_fro_sandwich {m n : ℕ} (F : Mat m m) (D : Mat m n) (G : Mat n n)
    (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1) : fro (F * D * G) ≤ fro D := by
  have h1 : opNorm F * fro D ≤ fro D := mul_le_of_le_one_left (lr_fro_nn D) hF
  calc fro (F * D * G) ≤ fro (F * D) * opNorm G := lr_fro_mul_le_right _ _
    _ ≤ (opNorm F * fro D) * opNorm G :=
        mul_le_mul_of_nonneg_right (lr_fro_mul_le_left _ _) (lr_opNorm_nonneg _)
    _ ≤ fro D * 1 := mul_le_mul h1 hG (lr_opNorm_nonneg G) (lr_fro_nn D)
    _ = fro D := mul_one _

private lemma lr_trace_mul_transpose_le {m n : ℕ} (X C : Mat m n) :
    |Matrix.trace (X * Cᵀ)| ≤ fro X * fro C := by
  have htr : Matrix.trace (X * Cᵀ) = ∑ p : Fin m × Fin n, X p.1 p.2 * C p.1 p.2 := by
    simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [htr]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m × Fin n))
    (fun p => X p.1 p.2) (fun p => C p.1 p.2)
  have hX : ∑ p : Fin m × Fin n, X p.1 p.2 ^ 2 = fro X ^ 2 := by
    rw [lr_fro_sq, Fintype.sum_prod_type]
  have hC : ∑ p : Fin m × Fin n, C p.1 p.2 ^ 2 = fro C ^ 2 := by
    rw [lr_fro_sq, Fintype.sum_prod_type]
  rw [hX, hC] at cs
  refine (pow_le_pow_iff_left₀ (abs_nonneg _) (mul_nonneg (lr_fro_nn X) (lr_fro_nn C))
    two_ne_zero).mp ?_
  rw [sq_abs, mul_pow]
  exact cs

/-- Tested pairing bound `|Tr[F X G Yᵀ]| ≤ ‖X‖_F ‖Y‖_F` for contractions `F`, `G`. -/
private lemma lr_tested_le {m n : ℕ} (Fo : Mat m m) (Gi : Mat n n) (hF : opNorm Fo ≤ 1)
    (hG : opNorm Gi ≤ 1) (X Y : Mat m n) :
    |Matrix.trace (Fo * X * Gi * Yᵀ)| ≤ fro X * fro Y :=
  (lr_trace_mul_transpose_le (Fo * X * Gi) Y).trans
    (mul_le_mul_of_nonneg_right (lr_fro_sandwich Fo X Gi hF hG) (lr_fro_nn Y))

private lemma lr_abs_entry_le_fro {m n : ℕ} (K : Mat m n) (i : Fin m) (j : Fin n) :
    |K i j| ≤ fro K := by
  unfold fro
  apply Real.abs_le_sqrt
  have h1 : ‖K i j‖ ^ 2 ≤ ∑ j', ‖K i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖K i j'‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', ‖K i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖K i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖K i' j'‖ ^ 2)
      (fun i' _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ i)
  have h3 : ‖K i j‖ ^ 2 = K i j ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  linarith

private lemma lr_fro_le_of_entries {m n : ℕ} (K : Mat m n) (a : ℝ) (ha : 0 ≤ a)
    (h : ∀ i j, |K i j| ≤ a) : fro K ≤ Real.sqrt ((m : ℝ) * n) * a := by
  have h1 : fro K ^ 2 ≤ ((m : ℝ) * n) * a ^ 2 := by
    rw [lr_fro_sq]
    calc ∑ i, ∑ j, K i j ^ 2 ≤ ∑ _i : Fin m, ∑ _j : Fin n, a ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h i j) 2
      _ = ((m : ℝ) * n) * a ^ 2 := by simp [mul_assoc]
  have h2 : Real.sqrt (((m : ℝ) * n) * a ^ 2) = Real.sqrt ((m : ℝ) * n) * a := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq ha]
  rw [← h2]
  exact Real.le_sqrt_of_sq_le h1

/-! ### Measurability and boundedness of the centred updates -/

private lemma lr_borel (m n : ℕ) : BorelSpace (Mat m n) :=
  inferInstanceAs (BorelSpace (Fin m → Fin n → ℝ))

private lemma lr_sc (m n : ℕ) : SecondCountableTopology (Mat m n) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))

private lemma lr_batch_meas (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) :
    Measurable (frozenBatchG F S s) := by
  haveI := lr_borel m n
  haveI := lr_sc m n
  unfold frozenBatchG
  refine Measurable.const_smul ?_ ((B : ℝ))⁻¹
  refine Finset.measurable_sum _ fun a _ => ?_
  have hc : Continuous (fun p : Vec m × Vec n =>
      (dotProduct p.1 (Matrix.mulVec F.A p.2)) • (rOut F.C * outer p.1 p.2 * rIn F.C)) := by
    fun_prop
  exact hc.measurable.comp (S.meas s a)

private lemma lr_tsum_meas {Ω' : Type*} (m1 : MeasurableSpace Ω') (f : ℕ → Ω' → Mat m n)
    (hf : ∀ j, Measurable[m1] (f j)) : Measurable[m1] (fun ω => ∑' j, f j ω) := by
  letI : MeasurableSpace Ω' := m1
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  exact Measurable.tsum hf

private lemma lr_buf_meas (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) :
    Measurable (frozenBuf F S t) := by
  unfold frozenBuf
  exact lr_tsum_meas _ _ fun j => (lr_batch_meas F S _).const_smul (emaW F.β j)

private lemma lr_Q_meas {ϱ : ℝ} (hϱ : 0 ≤ ϱ) : Measurable (fun K : Mat m n => Q ϱ K) :=
  (measurable_Q (m := m) (n := n)).comp
    ((measurable_const (a := (⟨ϱ, hϱ⟩ : Set.Ici (0 : ℝ)))).prodMk measurable_id)

private lemma lr_upd_meas (F : FrozenParams m n B) (S : FrozenSamples P m n B) {ϱ : ℝ}
    (hϱ : 0 ≤ ϱ) (t : ℤ) : Measurable (frozenUpd F S ϱ t) :=
  (lr_Q_meas hϱ).comp (lr_buf_meas F S t)

private lemma lr_cen_meas (F : FrozenParams m n B) (S : FrozenSamples P m n B) {ϱ : ℝ}
    (hϱ : 0 ≤ ϱ) (t : ℤ) : Measurable (centredUpd F S ϱ t) := by
  haveI := lr_borel m n
  haveI := lr_sc m n
  unfold centredUpd
  exact ((continuous_id.sub continuous_const).measurable).comp (lr_upd_meas F S hϱ t)

private lemma lr_upd_fro_sq (F : FrozenParams m n B) (S : FrozenSamples P m n B) {ϱ : ℝ}
    (hϱ : 0 ≤ ϱ) (t : ℤ) (ω : Ω) : fro (frozenUpd F S ϱ t ω) ^ 2 ≤ (min m n : ℕ) := by
  obtain ⟨-, h2, h3, -⟩ := lem_app_setup_filter_i ϱ hϱ (frozenBuf F S t ω)
  exact h2.trans (by exact_mod_cast h3)

private lemma lr_upd_entry (F : FrozenParams m n B) (S : FrozenSamples P m n B) {ϱ : ℝ}
    (hϱ : 0 ≤ ϱ) (t : ℤ) (ω : Ω) (i : Fin m) (j : Fin n) :
    |frozenUpd F S ϱ t ω i j| ≤ Real.sqrt ((min m n : ℕ) : ℝ) := by
  refine (lr_abs_entry_le_fro _ i j).trans ?_
  exact Real.le_sqrt_of_sq_le (lr_upd_fro_sq F S hϱ t ω)

private lemma lr_mean_entry [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (t : ℤ) (i : Fin m) (j : Fin n) :
    |mean P (frozenUpd F S ϱ t) i j| ≤ Real.sqrt ((min m n : ℕ) : ℝ) := by
  have h := norm_integral_le_of_norm_le_const (μ := P) (f := fun ω => frozenUpd F S ϱ t ω i j)
    (C := Real.sqrt ((min m n : ℕ) : ℝ))
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact lr_upd_entry F S hϱ t ω i j)
  simpa [mean, Real.norm_eq_abs] using h

/-- Uniform Frobenius bound for the centred updates. -/
private lemma lr_cen_fro_le [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (t : ℤ) (ω : Ω) :
    fro (centredUpd F S ϱ t ω) ≤
      Real.sqrt ((m : ℝ) * n) * (2 * Real.sqrt ((min m n : ℕ) : ℝ)) := by
  refine lr_fro_le_of_entries _ _ (by positivity) fun i j => ?_
  have h1 := lr_upd_entry F S hϱ t ω i j
  have h2 := lr_mean_entry F S hϱ t i j
  simp only [centredUpd, Matrix.sub_apply]
  calc |frozenUpd F S ϱ t ω i j - mean P (frozenUpd F S ϱ t) i j|
      ≤ |frozenUpd F S ϱ t ω i j| + |mean P (frozenUpd F S ϱ t) i j| := abs_sub _ _
    _ ≤ 2 * Real.sqrt ((min m n : ℕ) : ℝ) := by linarith

private lemma lr_trace_cont {m n : ℕ} (Fo : Mat m m) (Gi : Mat n n) :
    Continuous (fun p : Mat m n × Mat m n => Matrix.trace (Fo * p.1 * Gi * p.2ᵀ)) := by
  fun_prop

private lemma lr_meas_trace {α : Type*} [MeasurableSpace α] (Fo : Mat m m) (Gi : Mat n n)
    (f g : α → Mat m n) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => Matrix.trace (Fo * f x * Gi * (g x)ᵀ)) := by
  haveI := lr_borel m n
  haveI := lr_sc m n
  have h := ((lr_trace_cont Fo Gi).measurable).comp (hf.prodMk hg)
  exact h

/-- Integrability of the tested pairing of two bounded measurable random matrices. -/
private lemma lr_trace_integrable [IsProbabilityMeasure P] (Fo : Mat m m) (Gi : Mat n n)
    (hF : opNorm Fo ≤ 1) (hG : opNorm Gi ≤ 1) (X Y : Ω → Mat m n) (hX : Measurable X)
    (hY : Measurable Y) (D D' : ℝ) (hXD : ∀ ω, fro (X ω) ≤ D) (hYD : ∀ ω, fro (Y ω) ≤ D') :
    Integrable (fun ω => Matrix.trace (Fo * X ω * Gi * (Y ω)ᵀ)) P := by
  haveI := lr_borel m n
  haveI := lr_sc m n
  refine Integrable.of_bound (C := D * D') ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact ((lr_trace_cont Fo Gi).measurable.comp (hX.prodMk hY)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact (lr_tested_le Fo Gi hF hG _ _).trans
      (mul_le_mul (hXD ω) (hYD ω) (lr_fro_nn _) ((lr_fro_nn _).trans (hXD ω)))


/-! ### Stationarity of the tested pairing -/

private lemma lr_stat {E : Type*} [MeasurableSpace E] (X : ℤ → Ω → E)
    (hst : StrictlyStationary P X) (Φ : (ℤ → E) → ℝ) (hΦ : Measurable Φ) (k : ℤ) :
    ∫ ω, Φ (fun t => X (t + k) ω) ∂P = ∫ ω, Φ (fun t => X t ω) ∂P := by
  have hsh : Measurable (fun x : ℤ → E => fun t => x (t + k)) :=
    measurable_pi_iff.mpr (fun t => measurable_pi_apply (t + k))
  have h1 : AEMeasurable (fun ω t => X (t + k) ω) P := hsh.comp_aemeasurable hst.1
  calc ∫ ω, Φ (fun t => X (t + k) ω) ∂P
      = ∫ x, Φ x ∂(P.map (fun ω t => X (t + k) ω)) :=
        (integral_map h1 hΦ.aestronglyMeasurable).symm
    _ = ∫ x, Φ x ∂(P.map (fun ω t => X t ω)) := by rw [hst.2 k]
    _ = ∫ ω, Φ (fun t => X t ω) ∂P := integral_map hst.1 hΦ.aestronglyMeasurable

private lemma lr_mean_shift [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (s k : ℤ) :
    mean P (frozenUpd F S ϱ (s + k)) = mean P (frozenUpd F S ϱ s) := by
  haveI := lr_borel m n
  haveI := lr_sc m n
  have hst := (lem_app_setup_ema_law_ii F S).2
  ext i j
  simp only [mean, Matrix.of_apply]
  have := lr_stat (frozenBuf F S) hst (fun x => Q ϱ (x s) i j) (by
    have h1 : Measurable (fun x : ℤ → Mat m n => Q ϱ (x s)) :=
      (lr_Q_meas hϱ).comp (measurable_pi_apply s)
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp h1)) k
  simpa [frozenUpd] using this

private lemma lr_shift [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) {ϱ ϱ' : ℝ} (hϱ : 0 ≤ ϱ) (hϱ' : 0 ≤ ϱ')
    (Fo : Mat m m) (Gi : Mat n n) (s s' k : ℤ) :
    ∫ ω, Matrix.trace (Fo * centredUpd F S ϱ (s + k) ω * Gi *
        (centredUpd F S ϱ' (s' + k) ω)ᵀ) ∂P =
      ∫ ω, Matrix.trace (Fo * centredUpd F S ϱ s ω * Gi * (centredUpd F S ϱ' s' ω)ᵀ) ∂P := by
  haveI := lr_borel m n
  haveI := lr_sc m n
  have hst := (lem_app_setup_ema_law_ii F S).2
  have e1 := lr_mean_shift F S hϱ s k
  have e2 := lr_mean_shift F S hϱ' s' k
  have hmeas : Measurable (fun x : ℤ → Mat m n =>
      Matrix.trace (Fo * (Q ϱ (x s) - mean P (frozenUpd F S ϱ s)) * Gi *
        (Q ϱ' (x s') - mean P (frozenUpd F S ϱ' s'))ᵀ)) := by
    have h1 : Measurable (fun x : ℤ → Mat m n => Q ϱ (x s) - mean P (frozenUpd F S ϱ s)) :=
      ((continuous_id.sub continuous_const).measurable).comp
        ((lr_Q_meas hϱ).comp (measurable_pi_apply s))
    have h2 : Measurable (fun x : ℤ → Mat m n => Q ϱ' (x s') - mean P (frozenUpd F S ϱ' s')) :=
      ((continuous_id.sub continuous_const).measurable).comp
        ((lr_Q_meas hϱ').comp (measurable_pi_apply s'))
    exact lr_meas_trace Fo Gi _ _ h1 h2
  have key := lr_stat (frozenBuf F S) hst (fun x : ℤ → Mat m n =>
      Matrix.trace (Fo * (Q ϱ (x s) - mean P (frozenUpd F S ϱ s)) * Gi *
        (Q ϱ' (x s') - mean P (frozenUpd F S ϱ' s'))ᵀ)) hmeas k
  simp only [centredUpd, e1, e2]
  exact key

private lemma lr_diff [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) {ϱ ϱ' : ℝ} (hϱ : 0 ≤ ϱ) (hϱ' : 0 ≤ ϱ')
    (Fo : Mat m m) (Gi : Mat n n) (s s' t : ℤ) :
    ∫ ω, Matrix.trace (Fo * centredUpd F S ϱ s ω * Gi * (centredUpd F S ϱ' s' ω)ᵀ) ∂P =
      ∫ ω, Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (centredUpd F S ϱ' (t + (s' - s)) ω)ᵀ) ∂P := by
  have h := lr_shift F S hϱ hϱ' Fo Gi s s' (t - s)
  have e1 : s + (t - s) = t := by ring
  have e2 : s' + (t - s) = t + (s' - s) := by ring
  rw [e1, e2] at h
  exact h.symm

private lemma lr_symm (Fo : Mat m m) (Gi : Mat n n) (hFs : Fo.transpose = Fo)
    (hGs : Gi.transpose = Gi) (X Y : Mat m n) :
    Matrix.trace (Fo * X * Gi * Yᵀ) = Matrix.trace (Fo * Y * Gi * Xᵀ) := by
  have h1 : Matrix.trace (Fo * X * Gi * Yᵀ) = Matrix.trace ((Fo * X * Gi * Yᵀ)ᵀ) :=
    (Matrix.trace_transpose _).symm
  have h2 : (Fo * X * Gi * Yᵀ)ᵀ = Y * Gi * Xᵀ * Fo := by
    simp [Matrix.transpose_mul, hFs, hGs, Matrix.mul_assoc]
  rw [h1, h2]
  have h3 : Matrix.trace (Y * Gi * Xᵀ * Fo) = Matrix.trace (Fo * (Y * Gi * Xᵀ)) :=
    Matrix.trace_mul_comm _ _
  rw [h3]
  simp [Matrix.mul_assoc]

/-! ### The triangular count -/

private lemma lr_Icc_sum (g : ℤ → ℝ) (T : ℕ) :
    ∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), g s = ∑ a ∈ Finset.range T, g ((a : ℤ) + 1) := by
  have : Finset.Icc (1 : ℤ) (T : ℤ) = (Finset.range T).image (fun a : ℕ => (a : ℤ) + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(x - 1).toNat, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      omega
  rw [this, Finset.sum_image (fun a _ b _ h => by simpa using h)]

private lemma lr_count_aux (f : ℤ → ℝ) (T : ℕ) :
    ∑ a ∈ Finset.range T, ∑ b ∈ Finset.range T, f ((b : ℤ) - (a : ℤ)) =
      ∑ ℓ ∈ Finset.range T, ((T : ℝ) - ℓ) * (f ℓ + f (-(ℓ : ℤ))) - (T : ℝ) * f 0 := by
  induction T with
  | zero => simp
  | succ T ih =>
    have e1 : ∑ a ∈ Finset.range (T + 1), ∑ b ∈ Finset.range (T + 1), f ((b : ℤ) - (a : ℤ)) =
        ∑ a ∈ Finset.range T, ∑ b ∈ Finset.range T, f ((b : ℤ) - (a : ℤ))
        + ∑ a ∈ Finset.range T, f ((T : ℤ) - (a : ℤ))
        + ∑ b ∈ Finset.range T, f ((b : ℤ) - (T : ℤ)) + f 0 := by
      rw [Finset.sum_range_succ]
      simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
      simp
      ring
    have r1 : ∑ a ∈ Finset.range T, f ((T : ℤ) - (a : ℤ)) =
        ∑ ℓ ∈ Finset.range (T + 1), f (ℓ : ℤ) - f 0 := by
      rw [Finset.sum_range_succ', ← Finset.sum_range_reflect]
      simp only [Nat.cast_zero]
      have : ∀ j ∈ Finset.range T, f ((T : ℤ) - ((T - 1 - j : ℕ) : ℤ)) = f (((j + 1 : ℕ)) : ℤ) := by
        intro j hj
        rw [Finset.mem_range] at hj
        congr 1
        omega
      rw [Finset.sum_congr rfl this]
      ring
    have r2 : ∑ b ∈ Finset.range T, f ((b : ℤ) - (T : ℤ)) =
        ∑ ℓ ∈ Finset.range (T + 1), f (-(ℓ : ℤ)) - f 0 := by
      rw [Finset.sum_range_succ', ← Finset.sum_range_reflect]
      simp only [Nat.cast_zero, neg_zero]
      have : ∀ j ∈ Finset.range T, f (((T - 1 - j : ℕ) : ℤ) - (T : ℤ)) = f (-(((j + 1 : ℕ)) : ℤ)) := by
        intro j hj
        rw [Finset.mem_range] at hj
        congr 1
        omega
      rw [Finset.sum_congr rfl this]
      ring
    have e3 : ∑ ℓ ∈ Finset.range (T + 1), (((T + 1 : ℕ) : ℝ) - ℓ) * (f ℓ + f (-(ℓ : ℤ))) =
        ∑ ℓ ∈ Finset.range T, ((T : ℝ) - ℓ) * (f ℓ + f (-(ℓ : ℤ)))
        + ∑ ℓ ∈ Finset.range (T + 1), (f (ℓ : ℤ) + f (-(ℓ : ℤ))) := by
      have : ∀ ℓ ∈ Finset.range T, (((T + 1 : ℕ) : ℝ) - ℓ) * (f ℓ + f (-(ℓ : ℤ))) =
          ((T : ℝ) - ℓ) * (f ℓ + f (-(ℓ : ℤ))) + (f ℓ + f (-(ℓ : ℤ))) := by
        intro ℓ _
        push_cast
        ring
      rw [Finset.sum_range_succ, Finset.sum_congr rfl this, Finset.sum_add_distrib,
        Finset.sum_range_succ (fun ℓ : ℕ => f (ℓ : ℤ) + f (-(ℓ : ℤ))) T]
      push_cast
      ring
    rw [e1, ih, r1, r2, e3]
    simp only [Finset.sum_add_distrib]
    push_cast
    ring

private lemma lr_count (f : ℤ → ℝ) (T : ℕ) (hT : 1 ≤ T) :
    ∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), ∑ s' ∈ Finset.Icc (1 : ℤ) (T : ℤ), f (s' - s) =
      (T : ℝ) * f 0 + ∑ ℓ ∈ Finset.Ico 1 T, ((T : ℝ) - ℓ) * (f ℓ + f (-(ℓ : ℤ))) := by
  rw [lr_Icc_sum (fun s => ∑ s' ∈ Finset.Icc (1 : ℤ) (T : ℤ), f (s' - s)) T]
  simp only [lr_Icc_sum (fun s' => f (s' - _)) T]
  have : ∀ a ∈ Finset.range T, ∑ b ∈ Finset.range T, f (((b : ℤ) + 1) - ((a : ℤ) + 1)) =
      ∑ b ∈ Finset.range T, f ((b : ℤ) - (a : ℤ)) := by
    intro a _
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    ring
  rw [Finset.sum_congr rfl this, lr_count_aux, Finset.sum_range_eq_add_Ico _ (by omega : 0 < T)]
  simp
  ring

/-! ### Same-time bound -/

private lemma lr_entry_meas (F : FrozenParams m n B) (S : FrozenSamples P m n B) {ϱ : ℝ}
    (hϱ : 0 ≤ ϱ) (t : ℤ) (i : Fin m) (j : Fin n) :
    Measurable (fun ω => frozenUpd F S ϱ t ω i j) :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (lr_upd_meas F S hϱ t))

private lemma lr_cen_sq_int_le [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (t : ℤ) :
    ∫ ω, fro (centredUpd F S ϱ t ω) ^ 2 ∂P ≤ ((min m n : ℕ) : ℝ) := by
  have hmem : ∀ i j, MemLp (fun ω => frozenUpd F S ϱ t ω i j) 2 P := fun i j =>
    MemLp.of_bound (lr_entry_meas F S hϱ t i j).aestronglyMeasurable
      (Real.sqrt ((min m n : ℕ) : ℝ)) (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact lr_upd_entry F S hϱ t ω i j)
  have hsq : ∀ i j, Integrable (fun ω => frozenUpd F S ϱ t ω i j ^ 2) P := fun i j =>
    (hmem i j).integrable_sq
  have hcsq : ∀ i j, Integrable (fun ω => (frozenUpd F S ϱ t ω i j -
      mean P (frozenUpd F S ϱ t) i j) ^ 2) P := fun i j => by
    have : MemLp (fun ω => frozenUpd F S ϱ t ω i j - mean P (frozenUpd F S ϱ t) i j) 2 P :=
      (hmem i j).sub (memLp_const _)
    exact this.integrable_sq
  have hent : ∀ i j, ∫ ω, (frozenUpd F S ϱ t ω i j - mean P (frozenUpd F S ϱ t) i j) ^ 2 ∂P ≤
      ∫ ω, frozenUpd F S ϱ t ω i j ^ 2 ∂P := by
    intro i j
    have h1 := variance_eq_integral (μ := P) (lr_entry_meas F S hϱ t i j).aemeasurable
    have h2 := variance_le_expectation_sq (μ := P)
      (lr_entry_meas F S hϱ t i j).aestronglyMeasurable
    have h3 : mean P (frozenUpd F S ϱ t) i j = ∫ ω, frozenUpd F S ϱ t ω i j ∂P := rfl
    rw [h3]
    simp only [Pi.pow_apply] at h2
    rw [← h1]
    exact h2
  have hcen_sq : ∀ ω, fro (centredUpd F S ϱ t ω) ^ 2 = ∑ i, ∑ j,
      (frozenUpd F S ϱ t ω i j - mean P (frozenUpd F S ϱ t) i j) ^ 2 := by
    intro ω
    rw [lr_fro_sq]
    rfl
  have hint1 : ∫ ω, fro (centredUpd F S ϱ t ω) ^ 2 ∂P ≤
      ∫ ω, fro (frozenUpd F S ϱ t ω) ^ 2 ∂P := by
    simp_rw [hcen_sq, lr_fro_sq]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hcsq i j)),
      integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hsq i j))]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => hcsq i j), integral_finsetSum _ (fun j _ => hsq i j)]
    exact Finset.sum_le_sum fun j _ => hent i j
  have hint2 : Integrable (fun ω => fro (frozenUpd F S ϱ t ω) ^ 2) P := by
    simp_rw [lr_fro_sq]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hsq i j
  refine hint1.trans ?_
  calc ∫ ω, fro (frozenUpd F S ϱ t ω) ^ 2 ∂P ≤ ∫ _ω, ((min m n : ℕ) : ℝ) ∂P :=
        integral_mono hint2 (integrable_const _) fun ω => lr_upd_fro_sq F S hϱ t ω
    _ = ((min m n : ℕ) : ℝ) := by simp

/-- `ℓ = 0` clause of `thm:app-vol-lag-reduction`(ii). -/
private lemma lr_lag_zero [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (γstar CSig : ℝ) (hS : SizeFin F.C B γstar CSig)
    (Fo : Mat m m) (Gi : Mat n n) (hF : opNorm Fo ≤ 1) (hG : opNorm Gi ≤ 1)
    {ϱ ϱ' : ℝ} (hϱ : 0 ≤ ϱ) (hϱ' : 0 ≤ ϱ') (t : ℤ) :
    |def_app_vol_lag F S 0 t Fo Gi ϱ ϱ'| ≤ γstar := by
  haveI := lr_borel m n
  haveI := lr_sc m n
  have hBpos : (0 : ℝ) < B := by exact_mod_cast F.hB
  have hX := lr_cen_meas F S hϱ t
  have hY := lr_cen_meas F S hϱ' t
  have hXi := lr_cen_fro_le F S hϱ t
  have hYi := lr_cen_fro_le F S hϱ' t
  have hint : Integrable (fun ω => Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
      (centredUpd F S ϱ' t ω)ᵀ)) P :=
    lr_trace_integrable Fo Gi hF hG _ _ hX hY _ _ hXi hYi
  have hsqX : Integrable (fun ω => fro (centredUpd F S ϱ t ω) ^ 2) P := by
    refine Integrable.of_bound (C := (Real.sqrt ((m : ℝ) * n) * (2 * Real.sqrt ((min m n : ℕ) : ℝ))) ^ 2) ?_
      (Filter.Eventually.of_forall fun ω => ?_)
    · have hfro : Measurable (fun K : Mat m n => fro K ^ 2) := by
        unfold fro; fun_prop
      exact (hfro.comp hX).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (lr_fro_nn _) (hXi ω) 2
  have hsqY : Integrable (fun ω => fro (centredUpd F S ϱ' t ω) ^ 2) P := by
    refine Integrable.of_bound (C := (Real.sqrt ((m : ℝ) * n) * (2 * Real.sqrt ((min m n : ℕ) : ℝ))) ^ 2) ?_
      (Filter.Eventually.of_forall fun ω => ?_)
    · have hfro : Measurable (fun K : Mat m n => fro K ^ 2) := by
        unfold fro; fun_prop
      exact (hfro.comp hY).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (lr_fro_nn _) (hYi ω) 2
  have h1 : |∫ ω, Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi * (centredUpd F S ϱ' t ω)ᵀ) ∂P|
      ≤ ∫ ω, (fro (centredUpd F S ϱ t ω) ^ 2 / 2 + fro (centredUpd F S ϱ' t ω) ^ 2 / 2) ∂P := by
    refine (abs_integral_le_integral_abs).trans ?_
    refine integral_mono hint.abs ((hsqX.div_const 2).add (hsqY.div_const 2)) fun ω => ?_
    refine (lr_tested_le Fo Gi hF hG _ _).trans ?_
    nlinarith [sq_nonneg (fro (centredUpd F S ϱ t ω) - fro (centredUpd F S ϱ' t ω))]
  have h2 : ∫ ω, (fro (centredUpd F S ϱ t ω) ^ 2 / 2 + fro (centredUpd F S ϱ' t ω) ^ 2 / 2) ∂P
      ≤ ((min m n : ℕ) : ℝ) := by
    rw [integral_add (hsqX.div_const 2) (hsqY.div_const 2), integral_div, integral_div]
    have a1 := lr_cen_sq_int_le F S hϱ t
    have a2 := lr_cen_sq_int_le F S hϱ' t
    linarith
  have h3 : ((min m n : ℕ) : ℝ) ≤ γstar * B :=
    le_trans (by exact_mod_cast min_le_max) hS.1
  unfold def_app_vol_lag
  simp only [Nat.cast_zero, add_zero]
  rw [abs_mul, abs_of_pos (inv_pos.mpr hBpos), inv_mul_le_iff₀ hBpos]
  linarith

/-! ### Independence of the past buffer from a later truncated buffer -/

private lemma lr_batch_meas_sub (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) (T : Set (ℤ × Fin B)) (hT : ∀ a, (s, a) ∈ T) :
    Measurable[⨆ i ∈ T, MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance]
      (frozenBatchG F S s) := by
  have h : ∀ a, Measurable[⨆ i ∈ T, MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance]
      (S.zw s a) := fun a => Measurable.of_comap_le (le_iSup₂
      (f := fun i (_ : i ∈ T) =>
        MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance) (s, a) (hT a))
  generalize (⨆ i ∈ T, MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance) = m1 at h ⊢
  letI : MeasurableSpace Ω := m1
  haveI := lr_borel m n
  haveI := lr_sc m n
  unfold frozenBatchG
  refine Measurable.const_smul ?_ ((B : ℝ))⁻¹
  refine Finset.measurable_sum _ fun a _ => ?_
  have hc : Continuous (fun p : Vec m × Vec n =>
      (dotProduct p.1 (Matrix.mulVec F.A p.2)) • (rOut F.C * outer p.1 p.2 * rIn F.C)) := by
    fun_prop
  exact hc.measurable.comp (h a)

private lemma lr_fsum_meas {Ω' : Type*} {m1 : MeasurableSpace Ω'} (f : ℕ → Ω' → Mat m n) (s : Finset ℕ)
    (hf : ∀ j ∈ s, Measurable[m1] (f j)) : Measurable[m1] (fun ω => ∑ j ∈ s, f j ω) := by
  letI : MeasurableSpace Ω' := m1
  haveI := lr_borel m n
  haveI := lr_sc m n
  exact Finset.measurable_sum _ hf

private lemma lr_indep [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t t' : ℤ) (J : ℕ) (h : t + 2 ≤ t' + 1 - (J : ℤ)) :
    IndepFun (frozenBuf F S t) (fun ω => ∑ j ∈ Finset.range (J + 1),
      emaW F.β j • frozenBatchG F S (t' + 1 - (j : ℤ)) ω) P := by
  have hind := (iIndepFun_iff_iIndep
    (fun _ : ℤ × Fin B => (inferInstance : MeasurableSpace (Vec m × Vec n)))
    (fun p : ℤ × Fin B => fun ω => S.zw p.1 p.2 ω) P).mp S.indep
  have hdisj : Disjoint {p : ℤ × Fin B | p.1 ≤ t + 1} {p : ℤ × Fin B | t + 2 ≤ p.1} := by
    rw [Set.disjoint_left]
    intro p h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2
    omega
  have key := indep_iSup_of_disjoint (fun p : ℤ × Fin B => (S.meas p.1 p.2).comap_le) hind hdisj
  have hbat1 : ∀ s : ℤ, s ≤ t + 1 → Measurable[⨆ i ∈ {p : ℤ × Fin B | p.1 ≤ t + 1},
      MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance] (frozenBatchG F S s) :=
    fun s hs => lr_batch_meas_sub F S s _ (fun a => hs)
  have hbat2 : ∀ s : ℤ, t + 2 ≤ s → Measurable[⨆ i ∈ {p : ℤ × Fin B | t + 2 ≤ p.1},
      MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance] (frozenBatchG F S s) :=
    fun s hs => lr_batch_meas_sub F S s _ (fun a => hs)
  have hA : Measurable[⨆ i ∈ {p : ℤ × Fin B | p.1 ≤ t + 1},
      MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance] (frozenBuf F S t) := by
    unfold frozenBuf
    refine lr_tsum_meas _ _ fun j => ?_
    exact (hbat1 _ (by omega)).const_smul (emaW F.β j)
  have hB : Measurable[⨆ i ∈ {p : ℤ × Fin B | t + 2 ≤ p.1},
      MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance] (fun ω => ∑ j ∈ Finset.range (J + 1),
      emaW F.β j • frozenBatchG F S (t' + 1 - (j : ℤ)) ω) := by
    refine lr_fsum_meas _ _ fun j hj => ?_
    rw [Finset.mem_range] at hj
    exact (hbat2 _ (by omega)).const_smul (emaW F.β j)
  exact (IndepFun_iff_Indep _ _ P).mpr
    (indep_of_indep_of_le_left (indep_of_indep_of_le_right key (measurable_iff_comap_le.mp hB))
      (measurable_iff_comap_le.mp hA))

/-! ### Vanishing of the centred pairing against independent or constant matrices -/

private lemma lr_expand (Fo : Mat m m) (Gi : Mat n n) (X N : Mat m n) :
    Matrix.trace (Fo * X * Gi * Nᵀ) = ∑ a, ∑ b, X a b * (Gi * Nᵀ * Fo) b a := by
  have h : Matrix.trace (Fo * X * Gi * Nᵀ) = Matrix.trace (X * (Gi * Nᵀ * Fo)) := by
    rw [show Fo * X * Gi * Nᵀ = Fo * (X * Gi * Nᵀ) by simp [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp [Matrix.mul_assoc]
  rw [h]
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

private lemma lr_zero_const [IsProbabilityMeasure P] (Fo : Mat m m) (Gi : Mat n n)
    (X : Ω → Mat m n) (hX : ∀ a b, Integrable (fun ω => X ω a b) P)
    (h0 : ∀ a b, ∫ ω, X ω a b ∂P = 0) (A : Mat m n) :
    ∫ ω, Matrix.trace (Fo * X ω * Gi * Aᵀ) ∂P = 0 := by
  simp_rw [lr_expand]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => (hX a b).mul_const _))]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [integral_finsetSum _ (fun b _ => (hX a b).mul_const _)]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [integral_mul_const, h0, zero_mul]

private lemma lr_cen_entry_int [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (t : ℤ) (a : Fin m) (b : Fin n) :
    Integrable (fun ω => centredUpd F S ϱ t ω a b) P := by
  refine Integrable.of_bound (C := Real.sqrt ((m : ℝ) * n) * (2 * Real.sqrt ((min m n : ℕ) : ℝ)))
    ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp
      (lr_cen_meas F S hϱ t))).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact (lr_abs_entry_le_fro _ a b).trans (lr_cen_fro_le F S hϱ t ω)

private lemma lr_cen_entry_zero [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (t : ℤ) (a : Fin m) (b : Fin n) :
    ∫ ω, centredUpd F S ϱ t ω a b ∂P = 0 := by
  have hint : Integrable (fun ω => frozenUpd F S ϱ t ω a b) P :=
    Integrable.of_bound (C := Real.sqrt ((min m n : ℕ) : ℝ))
      (lr_entry_meas F S hϱ t a b).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact lr_upd_entry F S hϱ t ω a b)
  simp only [centredUpd, Matrix.sub_apply]
  rw [integral_sub hint (integrable_const _), integral_const]
  simp [mean]

private lemma lr_Q_fro_le {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (K : Mat m n) :
    fro (Q ϱ K) ≤ Real.sqrt ((min m n : ℕ) : ℝ) := by
  obtain ⟨-, h2, h3, -⟩ := lem_app_setup_filter_i ϱ hϱ K
  exact Real.le_sqrt_of_sq_le (h2.trans (by exact_mod_cast h3))

private lemma lr_int_mul_bdd [IsProbabilityMeasure P] (φ ψ : Ω → ℝ) (hφ : Measurable φ)
    (hψ : Measurable ψ) (c d : ℝ) (hc : ∀ ω, |φ ω| ≤ c) (hd : ∀ ω, |ψ ω| ≤ d) :
    Integrable (fun ω => φ ω * ψ ω) P := by
  refine Integrable.of_bound (C := c * d) (hφ.mul hψ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hc ω) (hd ω) (abs_nonneg _) ((abs_nonneg _).trans (hc ω))

private lemma lr_zero_indep [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (Fo : Mat m m) (Gi : Mat n n) (hF : opNorm Fo ≤ 1)
    (hG : opNorm Gi ≤ 1) {ϱ ϱ' : ℝ} (hϱ : 0 ≤ ϱ) (hϱ' : 0 ≤ ϱ') (t : ℤ)
    (Mtr : Ω → Mat m n) (htr : Measurable Mtr) (hind : IndepFun (frozenBuf F S t) Mtr P) :
    ∫ ω, Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
      (Q ϱ' (Mtr ω))ᵀ) ∂P = 0 := by
  haveI := lr_borel m n
  haveI := lr_sc m n
  obtain ⟨f, hf⟩ : ∃ f : Fin m → Fin n → Mat m n → ℝ, f = fun a b K =>
      (Q ϱ K - mean P (frozenUpd F S ϱ t)) a b := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Fin m → Fin n → Mat m n → ℝ, g = fun a b K =>
      (Gi * (Q ϱ' K)ᵀ * Fo) b a := ⟨_, rfl⟩
  have hfm : ∀ a b, Measurable (f a b) := fun a b => by
    rw [hf]
    have hsub : Measurable (fun K : Mat m n => K - mean P (frozenUpd F S ϱ t)) :=
      (continuous_id.sub continuous_const).measurable
    exact (measurable_pi_apply b).comp ((measurable_pi_apply a).comp
      (hsub.comp (lr_Q_meas hϱ)))
  have hgm : ∀ a b, Measurable (g a b) := fun a b => by
    rw [hg]
    have hc : Continuous (fun N : Mat m n => (Gi * Nᵀ * Fo) b a) := by fun_prop
    exact hc.measurable.comp (lr_Q_meas hϱ')
  have hbuf := lr_buf_meas F S t
  have e1 : ∀ ω, Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
      (Q ϱ' (Mtr ω))ᵀ) = ∑ a, ∑ b,
        f a b (frozenBuf F S t ω) * g a b (Mtr ω) := by
    intro ω
    rw [lr_expand, hf, hg]
    rfl
  have hint : ∀ a b, Integrable (fun ω => f a b (frozenBuf F S t ω) *
      g a b (Mtr ω)) P := by
    intro a b
    refine lr_int_mul_bdd _ _ ((hfm a b).comp hbuf) ((hgm a b).comp htr)
      (Real.sqrt ((m : ℝ) * n) * (2 * Real.sqrt ((min m n : ℕ) : ℝ)))
      (Real.sqrt ((min m n : ℕ) : ℝ)) (fun ω => ?_) (fun ω => ?_)
    · have : f a b (frozenBuf F S t ω) = centredUpd F S ϱ t ω a b := by rw [hf]; rfl
      rw [this]
      exact (lr_abs_entry_le_fro _ a b).trans (lr_cen_fro_le F S hϱ t ω)
    · have : g a b (Mtr ω) = (Gi * (Q ϱ' (Mtr ω))ᵀ * Fo) b a := by
        rw [hg]
      rw [this]
      refine (lr_abs_entry_le_fro _ b a).trans ?_
      refine (lr_fro_sandwich Gi _ Fo hG hF).trans ?_
      rw [lr_fro_transpose]
      exact lr_Q_fro_le hϱ' _
  simp_rw [e1]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hint a b))]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [integral_finsetSum _ (fun b _ => hint a b)]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [hind.integral_fun_comp_mul_comp hbuf.aemeasurable htr.aemeasurable
    (hfm a b).aestronglyMeasurable (hgm a b).aestronglyMeasurable]
  have : ∫ ω, f a b (frozenBuf F S t ω) ∂P = 0 := by
    have e : ∀ ω, f a b (frozenBuf F S t ω) = centredUpd F S ϱ t ω a b := by
      intro ω; rw [hf]; rfl
    simp_rw [e]
    exact lr_cen_entry_zero F S hϱ t a b
  rw [this, zero_mul]

/-! ### Cauchy–Schwarz and the lag bound -/

private lemma lr_cs [IsProbabilityMeasure P] (a b : Ω → ℝ) (ha : Measurable a)
    (hb : Measurable b) (hA : Integrable (fun ω => a ω ^ 2) P)
    (hB : Integrable (fun ω => b ω ^ 2) P) :
    (∫ ω, a ω * b ω ∂P) ^ 2 ≤ (∫ ω, a ω ^ 2 ∂P) * (∫ ω, b ω ^ 2 ∂P) := by
  have hab : Integrable (fun ω => a ω * b ω) P := by
    refine Integrable.mono' ((hA.add hB).div_const 2) (ha.mul hb).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    simp only [Pi.add_apply]
    refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith [sq_nonneg (a ω + b ω), sq_nonneg (a ω - b ω)]
  have hq : ∀ x : ℝ, 0 ≤ (∫ ω, a ω ^ 2 ∂P) * (x * x) + (-2 * ∫ ω, a ω * b ω ∂P) * x +
      ∫ ω, b ω ^ 2 ∂P := by
    intro x
    have h1 : ∫ ω, (x * a ω - b ω) ^ 2 ∂P = (∫ ω, a ω ^ 2 ∂P) * (x * x) +
        (-2 * ∫ ω, a ω * b ω ∂P) * x + ∫ ω, b ω ^ 2 ∂P := by
      have e : (fun ω => (x * a ω - b ω) ^ 2) =
          fun ω => (x * x) * a ω ^ 2 - (2 * x) * (a ω * b ω) + b ω ^ 2 := by
        funext ω; ring
      have i1 : Integrable (fun ω => (x * x) * a ω ^ 2) P := hA.const_mul _
      have i2 : Integrable (fun ω => (2 * x) * (a ω * b ω)) P := hab.const_mul _
      have i3 : Integrable (fun ω => (x * x) * a ω ^ 2 - (2 * x) * (a ω * b ω)) P := i1.sub i2
      rw [e, integral_add i3 hB, integral_sub i1 i2, integral_const_mul,
        integral_const_mul]
      ring
    rw [← h1]
    exact integral_nonneg fun ω => sq_nonneg _
  have := discrim_le_zero hq
  unfold discrim at this
  nlinarith [this]

/-! ### The numerical constant -/

private lemma lr_numeric (γ CSig ϱlo ϱ' β b I0 x0 d0 mm nn c1 s2 V : ℝ) (ℓ : ℕ)
    (hb : 1 ≤ b) (hγ : 0 ≤ γ) (hC : 0 ≤ CSig) (hϱlo : 0 < ϱlo) (hϱ' : ϱlo ≤ ϱ')
    (hβ : 0 ≤ β) (hI : I0 ^ 2 ≤ x0 * d0) (hx0 : x0 ≤ γ * b) (hx0n : 0 ≤ x0)
    (hd0n : 0 ≤ d0) (hd0 : d0 ≤ ϱ'⁻¹ * (β ^ (2 * ℓ) * (c1 + s2 * V)))
    (hc1 : 0 ≤ c1) (hc1' : c1 ≤ CSig ^ 2) (hs2 : 0 ≤ s2) (hs2' : s2 ≤ 1)
    (hV : 0 ≤ V) (hV' : V ≤ CSig ^ 2 * (mm * nn + 2 * mm + 2 * nn + 3) / b)
    (hmm : 0 ≤ mm) (hmm' : mm ≤ γ * b) (hnn : 0 ≤ nn) (hnn' : nn ≤ γ * b) :
    |b⁻¹ * I0| ≤ CSig * Real.sqrt (2 * γ * (γ ^ 2 + 4 * γ + 3) / ϱlo) * β ^ ℓ := by
  have hbpos : 0 < b := by linarith
  have hZ : 0 ≤ 2 * γ * (γ ^ 2 + 4 * γ + 3) / ϱlo := by positivity
  have hR : 0 ≤ CSig * Real.sqrt (2 * γ * (γ ^ 2 + 4 * γ + 3) / ϱlo) * β ^ ℓ := by positivity
  refine abs_le_of_sq_le_sq ?_ hR
  have hVb : V ≤ CSig ^ 2 * (γ ^ 2 * b ^ 2 + 4 * γ * b + 3) / b := by
    refine hV'.trans ?_
    refine div_le_div_of_nonneg_right ?_ hbpos.le
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    nlinarith [mul_le_mul hmm' hnn' hnn (by positivity : 0 ≤ γ * b)]
  have hsV : s2 * V ≤ V := mul_le_of_le_one_left hV hs2'
  have hinv : ϱ'⁻¹ ≤ ϱlo⁻¹ := inv_anti₀ hϱlo hϱ'
  have hbeta : 0 ≤ β ^ (2 * ℓ) := by positivity
  have hd1 : d0 ≤ ϱlo⁻¹ * (β ^ (2 * ℓ) * (CSig ^ 2 +
      CSig ^ 2 * (γ ^ 2 * b ^ 2 + 4 * γ * b + 3) / b)) := by
    refine hd0.trans ?_
    have h1 : c1 + s2 * V ≤ CSig ^ 2 + CSig ^ 2 * (γ ^ 2 * b ^ 2 + 4 * γ * b + 3) / b := by
      linarith
    have h2 : 0 ≤ c1 + s2 * V := by positivity
    calc ϱ'⁻¹ * (β ^ (2 * ℓ) * (c1 + s2 * V))
        ≤ ϱlo⁻¹ * (β ^ (2 * ℓ) * (c1 + s2 * V)) :=
          mul_le_mul_of_nonneg_right hinv (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hbeta) (by positivity)
  have hkey : (1 + (γ ^ 2 * b ^ 2 + 4 * γ * b + 3) / b) / b ≤ γ ^ 2 + 4 * γ + 4 := by
    have e : (1 + (γ ^ 2 * b ^ 2 + 4 * γ * b + 3) / b) / b =
        (b + γ ^ 2 * b ^ 2 + 4 * γ * b + 3) / b ^ 2 := by
      field_simp
      ring
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hγ (sub_nonneg.mpr hb), sq_nonneg (b - 1), mul_nonneg hγ hbpos.le]
  have hfin : (b⁻¹ * I0) ^ 2 ≤ γ * d0 / b := by
    calc (b⁻¹ * I0) ^ 2 = I0 ^ 2 / b ^ 2 := by field_simp
      _ ≤ (x0 * d0) / b ^ 2 := div_le_div_of_nonneg_right hI (by positivity)
      _ ≤ (γ * b * d0) / b ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hx0 hd0n) (by positivity)
      _ = γ * d0 / b := by field_simp
  have hRsq : (CSig * Real.sqrt (2 * γ * (γ ^ 2 + 4 * γ + 3) / ϱlo) * β ^ ℓ) ^ 2 =
      ϱlo⁻¹ * (β ^ (2 * ℓ) * (CSig ^ 2 * (2 * γ * (γ ^ 2 + 4 * γ + 3)))) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hZ, ← pow_mul, mul_comm ℓ 2]
    field_simp
  rw [hRsq]
  calc (b⁻¹ * I0) ^ 2 ≤ γ * d0 / b := hfin
    _ ≤ γ * (ϱlo⁻¹ * (β ^ (2 * ℓ) * (CSig ^ 2 +
          CSig ^ 2 * (γ ^ 2 * b ^ 2 + 4 * γ * b + 3) / b))) / b :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd1 hγ) hbpos.le
    _ = ϱlo⁻¹ * (β ^ (2 * ℓ) * (CSig ^ 2 * γ *
          ((1 + (γ ^ 2 * b ^ 2 + 4 * γ * b + 3) / b) / b))) := by
        field_simp
    _ ≤ ϱlo⁻¹ * (β ^ (2 * ℓ) * (CSig ^ 2 * γ * (γ ^ 2 + 4 * γ + 4))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hbeta) (by positivity)
        exact mul_le_mul_of_nonneg_left hkey (by positivity)
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hbeta) (by positivity)
        nlinarith [mul_nonneg (sq_nonneg CSig) hγ, mul_nonneg (mul_nonneg (sq_nonneg CSig) hγ)
          (by positivity : (0:ℝ) ≤ γ ^ 2 + 4 * γ + 2)]

/-! ### The lag bound for `ℓ ≥ 1` -/

private lemma lr_fro_triangle (K L : Mat m n) : fro (K - L) ≤ fro K + fro L := by
  have h := lr_fro_sq (K - L)
  have hK := lr_fro_sq K
  have hL := lr_fro_sq L
  have hcs : (∑ i, ∑ j, K i j * L i j) ≤ fro K * fro L := by
    have := lr_trace_mul_transpose_le K L
    have htr : Matrix.trace (K * Lᵀ) = ∑ i, ∑ j, K i j * L i j := by
      simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    rw [htr] at this
    exact (le_abs_self _).trans this
  have hexp : fro (K - L) ^ 2 = fro K ^ 2 + fro L ^ 2 - 2 * ∑ i, ∑ j, K i j * L i j := by
    rw [h, hK, hL]
    simp only [Matrix.sub_apply, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.mul_sum]
    ring_nf
  have hle : fro (K - L) ^ 2 ≤ (fro K + fro L) ^ 2 := by
    rw [hexp]
    have : 0 ≤ ∑ i, ∑ j, K i j * L i j + fro K * fro L := by
      have h0 := lr_trace_mul_transpose_le K L
      have htr : Matrix.trace (K * Lᵀ) = ∑ i, ∑ j, K i j * L i j := by
        simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
      rw [htr] at h0
      have := neg_abs_le (∑ i, ∑ j, K i j * L i j)
      linarith
    nlinarith
  exact (pow_le_pow_iff_left₀ (lr_fro_nn _) (add_nonneg (lr_fro_nn _) (lr_fro_nn _))
    two_ne_zero).mp hle

private lemma lr_fro_meas : Measurable (fun K : Mat m n => fro K) := by
  unfold fro
  fun_prop

private lemma lr_lag_pos [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (γstar CSig ϱlo ϱhi : ℝ) (hS : SizeFin F.C B γstar CSig)
    (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi) (Fo : Mat m m) (Gi : Mat n n)
    (hF : opNorm Fo ≤ 1) (hG : opNorm Gi ≤ 1) (ϱ ϱ' : ℝ) (hϱI : ϱ ∈ Set.Icc ϱlo ϱhi)
    (hϱ'I : ϱ' ∈ Set.Icc ϱlo ϱhi) (t : ℤ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (Mtr : Ω → Mat m n) (htr : Measurable Mtr)
    (hind : IndepFun (frozenBuf F S t) Mtr P)
    (hd : ∫ ω, (fro (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) - Q ϱ' (Mtr ω))) ^ 2 ∂P ≤
      ϱ'⁻¹ * (F.β ^ (2 * ℓ) *
        (fro (mean P (frozenBatchG F S (t + (ℓ : ℤ) + 1))) ^ 2 + sPow F.β 2 * frozenVB S F)))
    (hmean : fro (mean P (frozenBatchG F S (t + (ℓ : ℤ) + 1))) ≤ CSig)
    (hVB : frozenVB S F ≤ CSig ^ 2 * ((m : ℝ) * n + 2 * m + 2 * n + 3) / (B : ℝ)) :
    |def_app_vol_lag F S ℓ t Fo Gi ϱ ϱ'| ≤ Muon.Dynamics.kStar CSig γstar ϱlo * F.β ^ ℓ := by
  haveI := lr_borel m n
  haveI := lr_sc m n
  have hϱ0 : 0 ≤ ϱ := le_trans hϱ.1.le hϱI.1
  have hϱ'pos : 0 < ϱ' := lt_of_lt_of_le hϱ.1 hϱ'I.1
  have hϱ'0 : 0 ≤ ϱ' := hϱ'pos.le
  have hBpos : (0 : ℝ) < B := by exact_mod_cast F.hB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast F.hB
  obtain ⟨hβ0, hβ1⟩ := F.hβ
  -- measurable ingredients
  have hbuf := lr_buf_meas F S (t + (ℓ : ℤ))
  have hX := lr_cen_meas F S hϱ0 t
  have hNt : Measurable (fun ω => Q ϱ' (Mtr ω)) :=
    (lr_Q_meas hϱ'0).comp htr
  have hUn : Measurable (fun ω => Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω)) :=
    (lr_Q_meas hϱ'0).comp hbuf
  have hDd : Measurable (fun ω => Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
      Q ϱ' (Mtr ω)) := by
    have hsub : Measurable (fun p : Mat m n × Mat m n => p.1 - p.2) :=
      (continuous_fst.sub continuous_snd).measurable
    exact hsub.comp (hUn.prodMk hNt)
  have hsq : Real.sqrt ((min m n : ℕ) : ℝ) ≥ 0 := Real.sqrt_nonneg _
  have hXi := lr_cen_fro_le F S hϱ0 t
  -- bounds on Nt, Dd
  have hNtb : ∀ ω, fro (Q ϱ' (Mtr ω)) ≤
      Real.sqrt ((min m n : ℕ) : ℝ) := fun ω => lr_Q_fro_le hϱ'0 _
  have hDdb : ∀ ω, fro (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
      Q ϱ' (Mtr ω)) ≤ 2 * Real.sqrt ((min m n : ℕ) : ℝ) := by
    intro ω
    have h1 := lr_Q_fro_le hϱ'0 (frozenBuf F S (t + (ℓ : ℤ)) ω)
    have h2 := lr_Q_fro_le hϱ'0 (Mtr ω)
    have h3 : fro (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
        Q ϱ' (Mtr ω)) ≤
        fro (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω)) +
        fro (Q ϱ' (Mtr ω)) := by
      have := lr_fro_triangle (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω))
        (Q ϱ' (Mtr ω))
      exact this
    linarith
  -- the three pieces of the pairing
  set ν := mean P (frozenUpd F S ϱ' (t + (ℓ : ℤ))) with hν
  have hνb : ∀ i j, |ν i j| ≤ Real.sqrt ((min m n : ℕ) : ℝ) :=
    fun i j => lr_mean_entry F S hϱ'0 _ i j
  have hνf : fro ν ≤ Real.sqrt ((m : ℝ) * n) * Real.sqrt ((min m n : ℕ) : ℝ) :=
    lr_fro_le_of_entries ν _ hsq hνb
  have hpt : ∀ ω, Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (centredUpd F S ϱ' (t + (ℓ : ℤ)) ω)ᵀ) =
      Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) - Q ϱ' (Mtr ω))ᵀ) +
      Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (Q ϱ' (Mtr ω))ᵀ) -
      Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi * νᵀ) := by
    intro ω
    have e : centredUpd F S ϱ' (t + (ℓ : ℤ)) ω =
        (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) - Q ϱ' (Mtr ω)) +
          Q ϱ' (Mtr ω) - ν := by
      simp only [centredUpd, frozenUpd, hν]
      abel
    rw [e]
    simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.mul_add, Matrix.mul_sub,
      Matrix.trace_add, Matrix.trace_sub]
  have iA : Integrable (fun ω => Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
          Q ϱ' (Mtr ω))ᵀ)) P :=
    lr_trace_integrable Fo Gi hF hG _ _ hX hDd _ _ hXi hDdb
  have iB : Integrable (fun ω => Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (Q ϱ' (Mtr ω))ᵀ)) P :=
    lr_trace_integrable Fo Gi hF hG _ _ hX hNt _ _ hXi hNtb
  have iC : Integrable (fun ω => Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi * νᵀ)) P :=
    lr_trace_integrable Fo Gi hF hG _ (fun _ => ν) hX measurable_const _ _ hXi (fun _ => hνf)
  have zB := lr_zero_indep F S Fo Gi hF hG hϱ0 hϱ'0 t Mtr htr hind
  have zC := lr_zero_const (P := P) Fo Gi (centredUpd F S ϱ t)
    (lr_cen_entry_int F S hϱ0 t) (lr_cen_entry_zero F S hϱ0 t) ν
  have hI0 : ∫ ω, Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (centredUpd F S ϱ' (t + (ℓ : ℤ)) ω)ᵀ) ∂P =
      ∫ ω, Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
          Q ϱ' (Mtr ω))ᵀ) ∂P := by
    have iAB : Integrable (fun ω => Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
          Q ϱ' (Mtr ω))ᵀ) +
        Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (Q ϱ' (Mtr ω))ᵀ)) P := iA.add iB
    simp_rw [hpt]
    rw [integral_sub iAB iC, integral_add iA iB, zB, zC]
    ring
  -- Cauchy–Schwarz
  have hsqint : ∀ (f : Ω → ℝ), Measurable f → ∀ c : ℝ, (∀ ω, |f ω| ≤ c) →
      Integrable (fun ω => f ω ^ 2) P := fun f hf c hc =>
    Integrable.of_bound (C := c ^ 2) (hf.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hc ω) 2)
  have haM : Measurable (fun ω => fro (centredUpd F S ϱ t ω)) := lr_fro_meas.comp hX
  have hbM : Measurable (fun ω => fro (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
      Q ϱ' (Mtr ω))) := lr_fro_meas.comp hDd
  have haI := hsqint _ haM _ (fun ω => by
    rw [abs_of_nonneg (lr_fro_nn _)]; exact hXi ω)
  have hbI := hsqint _ hbM _ (fun ω => by
    rw [abs_of_nonneg (lr_fro_nn _)]; exact hDdb ω)
  have hcs := lr_cs _ _ haM hbM haI hbI
  have habI : Integrable (fun ω => fro (centredUpd F S ϱ t ω) *
      fro (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
        Q ϱ' (Mtr ω))) P :=
    lr_int_mul_bdd _ _ haM hbM _ _
      (fun ω => by rw [abs_of_nonneg (lr_fro_nn _)]; exact hXi ω)
      (fun ω => by rw [abs_of_nonneg (lr_fro_nn _)]; exact hDdb ω)
  have hI1 : |∫ ω, Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
          Q ϱ' (Mtr ω))ᵀ) ∂P| ≤
      ∫ ω, fro (centredUpd F S ϱ t ω) * fro (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
        Q ϱ' (Mtr ω)) ∂P :=
    (abs_integral_le_integral_abs).trans
      (integral_mono iA.abs habI fun ω => lr_tested_le Fo Gi hF hG _ _)
  have hI1' : 0 ≤ ∫ ω, fro (centredUpd F S ϱ t ω) * fro (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
        Q ϱ' (Mtr ω)) ∂P :=
    integral_nonneg fun ω => mul_nonneg (lr_fro_nn _) (lr_fro_nn _)
  -- the second moment of the difference, by the truncation lemma
  have hs2 : sPow F.β 2 = (1 - F.β) / (1 + F.β) := eqn_app_setup_weights_iii hβ0 hβ1
  have hs2n : 0 ≤ sPow F.β 2 := by rw [hs2]; exact div_nonneg (by linarith) (by linarith)
  have hs2l : sPow F.β 2 ≤ 1 := by
    rw [hs2, div_le_one (by linarith)]; linarith
  have hVn : 0 ≤ frozenVB S F := integral_nonneg fun ω => sq_nonneg _
  have hmeanf : fro (mean P (frozenBatchG F S (t + (ℓ : ℤ) + 1))) ≥ 0 := lr_fro_nn _
  have hγ : 0 ≤ γstar := by
    have h1 : (0 : ℝ) ≤ ((max m n : ℕ) : ℝ) := Nat.cast_nonneg _
    have := hS.1
    by_contra hneg
    push_neg at hneg
    nlinarith [mul_neg_of_neg_of_pos hneg hBpos]
  have hCs : 0 ≤ CSig := le_trans (lr_opNorm_nonneg _) hS.2.1
  -- assemble
  have hx0 : ∫ ω, fro (centredUpd F S ϱ t ω) ^ 2 ∂P ≤ γstar * B := by
    refine (lr_cen_sq_int_le F S hϱ0 t).trans ?_
    exact le_trans (by exact_mod_cast min_le_max) hS.1
  have hmm' : (m : ℝ) ≤ γstar * B := le_trans (by exact_mod_cast le_max_left m n) hS.1
  have hnn' : (n : ℝ) ≤ γstar * B := le_trans (by exact_mod_cast le_max_right m n) hS.1
  have hnum := lr_numeric γstar CSig ϱlo ϱ' F.β (B : ℝ)
    (∫ ω, Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi * (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
        Q ϱ' (Mtr ω))ᵀ) ∂P)
    (∫ ω, fro (centredUpd F S ϱ t ω) ^ 2 ∂P)
    (∫ ω, fro (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
        Q ϱ' (Mtr ω)) ^ 2 ∂P)
    (m : ℝ) (n : ℝ) (fro (mean P (frozenBatchG F S (t + (ℓ : ℤ) + 1))) ^ 2) (sPow F.β 2)
    (frozenVB S F) ℓ hB1 hγ hCs hϱ.1 hϱ'I.1 hβ0
    ?_ hx0 (integral_nonneg fun ω => sq_nonneg _) (integral_nonneg fun ω => sq_nonneg _) hd
    (sq_nonneg _) ?_ hs2n hs2l hVn ?_ (Nat.cast_nonneg _) hmm' (Nat.cast_nonneg _) hnn'
  · -- the final step
    unfold def_app_vol_lag
    rw [hI0]
    unfold Muon.Dynamics.kStar
    exact hnum
  · -- Cauchy–Schwarz
    refine le_trans ?_ hcs
    have h1 := hI1
    have h2 := abs_nonneg (∫ ω, Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) - Q ϱ' (Mtr ω))ᵀ) ∂P)
    calc _ = |∫ ω, Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
          (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) -
            Q ϱ' (Mtr ω))ᵀ) ∂P| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ h2 h1 2
  · exact (pow_le_pow_left₀ (lr_fro_nn _) hmean 2)
  · exact hVB


/-- `thm:app-vol-lag-reduction`, part (i), snapshot `cr-2026-10-23`. Declaration of record for
this part. The statement, verbatim from `section.tex` (header and this part of the theorem):
```latex
\begin{theorem}[Lag reduction]\label{thm:app-vol-lag-reduction}
Under \cref{assum:app-setup-regime}, let $F,G$ be symmetric with
$\norm F,\norm G\le1$ and $\ridge,\ridge'\in I$.
\begin{enumerate}[label=(\roman*)]
\item For every integer $T\ge1$, with $S_T(\ridge)\defeq\sum_{t'=1}^T{\mathsf S}^{\mathrm c}_{t'}(\ridge)$,
\begin{equation}\label{eqn:app-vol-finite-time}
\begin{aligned}
&\frac1{BT}\EE\Tr\big[F\,S_T(\ridge)\,G\,S_T(\ridge')^\T\big]\\
&\qquad=C_0[F,G](\ridge,\ridge')+\sum_{\ell=1}^{T-1}\Big(1-\frac\ell T\Big)\Big(C_\ell[F,G](\ridge,\ridge')+C_\ell[F,G](\ridge',\ridge)\Big).
\end{aligned}
\end{equation}
\end{theorem}
```
The regime hypotheses of `assum:app-setup-regime` enter as fixed-dimension hypotheses: `SizeFin`
(dimensions, `‖Σ‖ ≤ C_Σ`), `1 ≤ C_Σ`, `0 < ϱ₋ ≤ ϱ₊` and `ϱ, ϱ' ∈ [ϱ₋, ϱ₊]`; the momentum `β = F.β
∈ [0,1)` is a field of `FrozenParams`. `F`, `G` are the symmetric test matrices with `‖·‖ ≤ 1`.
The `C_ℓ` carry the time `t`, and the statement is for every `t` (stationarity is
`lem:app-setup-ema-law`(ii), a theorem, not a hypothesis).
-/
theorem thm_app_vol_lag_reduction_i (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    [IsProbabilityMeasure P]
    (γstar CSig ϱlo ϱhi : ℝ) (hS : SizeFin F.C B γstar CSig) (hCSig : 1 ≤ CSig)
    (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi)
    (Fo : Mat m m) (Gi : Mat n n) (hFs : Fo.transpose = Fo) (hGs : Gi.transpose = Gi)
    (hF : opNorm Fo ≤ 1) (hG : opNorm Gi ≤ 1)
    (ϱ ϱ' : ℝ) (hϱI : ϱ ∈ Set.Icc ϱlo ϱhi) (hϱ'I : ϱ' ∈ Set.Icc ϱlo ϱhi)
    (T : ℕ) (hT : 1 ≤ T) (t : ℤ) :
    finiteTimeCov F S T ϱ ϱ' Fo Gi =
      def_app_vol_lag F S 0 t Fo Gi ϱ ϱ' +
        ∑ ℓ ∈ Finset.Ico 1 T, (1 - (ℓ : ℝ) / (T : ℝ)) *
          (def_app_vol_lag F S ℓ t Fo Gi ϱ ϱ' + def_app_vol_lag F S ℓ t Fo Gi ϱ' ϱ) := by
  haveI := lr_borel m n
  haveI := lr_sc m n
  have hϱ0 : 0 ≤ ϱ := le_trans hϱ.1.le hϱI.1
  have hϱ0' : 0 ≤ ϱ' := le_trans hϱ.1.le hϱ'I.1
  have hBpos : (0 : ℝ) < B := by exact_mod_cast F.hB
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hint : ∀ (r r' : ℝ), 0 ≤ r → 0 ≤ r' → ∀ s s' : ℤ,
      Integrable (fun ω => Matrix.trace (Fo * centredUpd F S r s ω * Gi *
        (centredUpd F S r' s' ω)ᵀ)) P := fun r r' hr hr' s s' =>
    lr_trace_integrable Fo Gi hF hG _ _ (lr_cen_meas F S hr s) (lr_cen_meas F S hr' s') _ _
      (lr_cen_fro_le F S hr s) (lr_cen_fro_le F S hr' s')
  have hexp : ∀ ω, Matrix.trace (Fo * (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), centredUpd F S ϱ s ω) *
        Gi * (∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), centredUpd F S ϱ' s ω)ᵀ) =
      ∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ), ∑ s' ∈ Finset.Icc (1 : ℤ) (T : ℤ),
        Matrix.trace (Fo * centredUpd F S ϱ s ω * Gi * (centredUpd F S ϱ' s' ω)ᵀ) := by
    intro ω
    simp only [Matrix.transpose_sum, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
    exact Finset.sum_comm
  obtain ⟨f, hf⟩ : ∃ f : ℤ → ℝ, f = fun d => ∫ ω, Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
      (centredUpd F S ϱ' (t + d) ω)ᵀ) ∂P := ⟨_, rfl⟩
  have hpair : ∀ s s' : ℤ, ∫ ω, Matrix.trace (Fo * centredUpd F S ϱ s ω * Gi *
      (centredUpd F S ϱ' s' ω)ᵀ) ∂P = f (s' - s) := by
    intro s s'
    rw [hf]
    exact lr_diff F S hϱ0 hϱ0' Fo Gi s s' t
  have hfp : ∀ ℓ : ℕ, f (ℓ : ℤ) = (B : ℝ) * def_app_vol_lag F S ℓ t Fo Gi ϱ ϱ' := by
    intro ℓ
    rw [hf]
    simp only [def_app_vol_lag]
    field_simp
  have hfn : ∀ ℓ : ℕ, f (-(ℓ : ℤ)) = (B : ℝ) * def_app_vol_lag F S ℓ t Fo Gi ϱ' ϱ := by
    intro ℓ
    have h1 : f (-(ℓ : ℤ)) = ∫ ω, Matrix.trace (Fo * centredUpd F S ϱ' (t + -(ℓ : ℤ)) ω * Gi *
        (centredUpd F S ϱ t ω)ᵀ) ∂P := by
      rw [hf]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        lr_symm Fo Gi hFs hGs _ _)
    rw [h1, lr_diff F S hϱ0' hϱ0 Fo Gi (t + -(ℓ : ℤ)) t t]
    have e : t + (t - (t + -(ℓ : ℤ))) = t + (ℓ : ℤ) := by ring
    rw [e]
    simp only [def_app_vol_lag]
    field_simp
  have hmain : finiteTimeCov F S T ϱ ϱ' Fo Gi =
      ((B : ℝ) * (T : ℝ))⁻¹ * ∑ s ∈ Finset.Icc (1 : ℤ) (T : ℤ),
        ∑ s' ∈ Finset.Icc (1 : ℤ) (T : ℤ), f (s' - s) := by
    unfold finiteTimeCov
    congr 1
    simp_rw [hexp]
    rw [integral_finset_sum _ (fun s _ => integrable_finset_sum _ (fun s' _ => hint ϱ ϱ' hϱ0 hϱ0' s s'))]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [integral_finset_sum _ (fun s' _ => hint ϱ ϱ' hϱ0 hϱ0' s s')]
    exact Finset.sum_congr rfl fun s' _ => hpair s s'
  rw [hmain, lr_count f T hT]
  have h0 : f ((0 : ℕ) : ℤ) = (B : ℝ) * def_app_vol_lag F S 0 t Fo Gi ϱ ϱ' := hfp 0
  simp only [Nat.cast_zero] at h0
  rw [h0, mul_add, Finset.mul_sum]
  have : ∀ ℓ ∈ Finset.Ico 1 T,
      ((B : ℝ) * (T : ℝ))⁻¹ * (((T : ℝ) - ℓ) * (f ℓ + f (-(ℓ : ℤ)))) =
      (1 - (ℓ : ℝ) / (T : ℝ)) * (def_app_vol_lag F S ℓ t Fo Gi ϱ ϱ' +
        def_app_vol_lag F S ℓ t Fo Gi ϱ' ϱ) := by
    intro ℓ _
    rw [hfp ℓ, hfn ℓ]
    field_simp
  rw [Finset.sum_congr rfl this]
  field_simp

/-- `thm:app-vol-lag-reduction`, part (ii) (actual covariances), snapshot `cr-2026-10-23`.
Declaration of record for this part. The statement, verbatim from `section.tex` (header and this
part of the theorem):
```latex
\begin{theorem}[Lag reduction]\label{thm:app-vol-lag-reduction}
Under \cref{assum:app-setup-regime}, let $F,G$ be symmetric with
$\norm F,\norm G\le1$ and $\ridge,\ridge'\in I$.
\begin{enumerate}[label=(\roman*)]
\item $\abs{C_0[F,G](\ridge,\ridge')}\le\gamma_\star$ and
$\abs{C_\ell[F,G](\ridge,\ridge')}\le\mathsf K_\star\bmom^\ell$ for $\ell\ge1$; at
$\bmom=0$, $C_\ell[F,G]=0$ for every $\ell\ge1$. The same bounds hold for the
independent covariances $C^{\mathrm g}_\ell[F,G]$ of
\cref{cor:app-vol-filtered-replacement}, under the size conditions.
\end{theorem}
```
The regime hypotheses of `assum:app-setup-regime` enter as fixed-dimension hypotheses: `SizeFin`
(dimensions, `‖Σ‖ ≤ C_Σ`), `1 ≤ C_Σ`, `0 < ϱ₋ ≤ ϱ₊` and `ϱ, ϱ' ∈ [ϱ₋, ϱ₊]`; the momentum `β = F.β
∈ [0,1)` is a field of `FrozenParams`. `F`, `G` are the symmetric test matrices with `‖·‖ ≤ 1`.
The `C_ℓ` carry the time `t`, and the statement is for every `t` (stationarity is
`lem:app-setup-ema-law`(ii), a theorem, not a hypothesis). Declared as three theorems: the bounds
for the actual covariances (`_ii_actual`), the vanishing at `β = 0` (`_ii_zero`), and the bounds
for the independent covariances (`_ii_indep`). Sorried: proof cards P2–P4.
-/
theorem thm_app_vol_lag_reduction_ii_actual (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    [IsProbabilityMeasure P]
    (γstar CSig ϱlo ϱhi : ℝ) (hS : SizeFin F.C B γstar CSig) (hCSig : 1 ≤ CSig)
    (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi)
    (Fo : Mat m m) (Gi : Mat n n) (hFs : Fo.transpose = Fo) (hGs : Gi.transpose = Gi)
    (hF : opNorm Fo ≤ 1) (hG : opNorm Gi ≤ 1)
    (ϱ ϱ' : ℝ) (hϱI : ϱ ∈ Set.Icc ϱlo ϱhi) (hϱ'I : ϱ' ∈ Set.Icc ϱlo ϱhi)
    (t : ℤ) :
    |def_app_vol_lag F S 0 t Fo Gi ϱ ϱ'| ≤ γstar ∧
      ∀ ℓ : ℕ, 1 ≤ ℓ → |def_app_vol_lag F S ℓ t Fo Gi ϱ ϱ'| ≤
        Muon.Dynamics.kStar CSig γstar ϱlo * F.β ^ ℓ := by
  have hϱ0 : 0 ≤ ϱ := le_trans hϱ.1.le hϱI.1
  have hϱ'pos : 0 < ϱ' := lt_of_lt_of_le hϱ.1 hϱ'I.1
  refine ⟨lr_lag_zero F S γstar CSig hS Fo Gi hF hG hϱ0 hϱ'pos.le t, fun ℓ hℓ => ?_⟩
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, J + 1 = ℓ := ⟨ℓ - 1, by omega⟩
  obtain ⟨-, hd⟩ := lem_app_setup_truncation_ii ϱ' hϱ'pos F S (t + (ℓ : ℤ)) J
  obtain ⟨hmean, hVB⟩ := lem_app_setup_truncation_iv ϱ' hϱ'pos F S (t + (ℓ : ℤ)) CSig hS.2.1 hS.2.2
  have hexp : 2 * (J + 1) = 2 * ℓ := by omega
  rw [hexp] at hd
  have hind := lr_indep F S t (t + (ℓ : ℤ)) J (by omega)
  have hmeas : Measurable (fun ω => ∑ j ∈ Finset.range (J + 1),
      emaW F.β j • frozenBatchG F S (t + (ℓ : ℤ) + 1 - (j : ℤ)) ω) := by
    haveI := lr_borel m n
    haveI := lr_sc m n
    exact Finset.measurable_sum _ fun j _ => (lr_batch_meas F S _).const_smul (emaW F.β j)
  exact lr_lag_pos F S γstar CSig ϱlo ϱhi hS hϱ Fo Gi hF hG ϱ ϱ' hϱI hϱ'I t ℓ hℓ _ hmeas hind hd
    hmean hVB

/-- At zero momentum the frozen buffer is the single current batch. -/
private lemma lr_buf_beta0 (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (hβ0 : F.β = 0) (s : ℤ) (ω : Ω) :
    frozenBuf F S s ω = frozenBatchG F S (s + 1) ω := by
  unfold frozenBuf
  rw [tsum_eq_single 0]
  · simp [emaW, hβ0]
  · intro j hj
    simp [emaW, hβ0, zero_pow hj]

/-- At zero momentum, `M_s` is the one-batch sum in the form used by `lr_indep`. -/
private lemma lr_buf_beta0_sum (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (hβ0 : F.β = 0) (s : ℤ) :
    frozenBuf F S s = fun ω => ∑ j ∈ Finset.range (0 + 1),
      emaW F.β j • frozenBatchG F S (s + 1 - (j : ℤ)) ω := by
  funext ω
  rw [lr_buf_beta0 F S hβ0 s ω]
  simp [hβ0, emaW]

/-- At zero momentum, buffers at lags `t` and `t + ℓ` (`ℓ ≥ 1`) are independent. -/
private lemma lr_zero_ind_beta0 [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (hβ0 : F.β = 0) (t : ℤ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    IndepFun (frozenBuf F S t) (frozenBuf F S (t + (ℓ : ℤ))) P := by
  have hI := lr_indep F S t (t + (ℓ : ℤ)) 0 (by push_cast; omega)
  rw [← lr_buf_beta0_sum F S hβ0 (t + (ℓ : ℤ))] at hI
  exact hI

/-- Expansion of the trace pairing against a difference in the second slot. -/
private lemma lr_trace_sub_right {m n : ℕ} (Fo : Mat m m) (Gi : Mat n n) (X Y N : Mat m n) :
    Matrix.trace (Fo * X * Gi * (Y - N)ᵀ) =
      Matrix.trace (Fo * X * Gi * Yᵀ) - Matrix.trace (Fo * X * Gi * Nᵀ) := by
  rw [Matrix.transpose_sub, Matrix.mul_sub, Matrix.trace_sub]

/-- `thm:app-vol-lag-reduction`, part (ii), zero-momentum clause (`_ii_zero`), snapshot
`cr-2026-10-23`. Statement: the clause `at \bmom=0, C_\ell[F,G]=0 for every \ell\ge1` of item (ii)
above. Sorried: proof card P3. -/
theorem thm_app_vol_lag_reduction_ii_zero (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    [IsProbabilityMeasure P]
    (γstar CSig ϱlo ϱhi : ℝ) (hS : SizeFin F.C B γstar CSig) (hCSig : 1 ≤ CSig)
    (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi)
    (Fo : Mat m m) (Gi : Mat n n) (hFs : Fo.transpose = Fo) (hGs : Gi.transpose = Gi)
    (hF : opNorm Fo ≤ 1) (hG : opNorm Gi ≤ 1)
    (ϱ ϱ' : ℝ) (hϱI : ϱ ∈ Set.Icc ϱlo ϱhi) (hϱ'I : ϱ' ∈ Set.Icc ϱlo ϱhi)
    (t : ℤ) (hβ0 : F.β = 0) :
    ∀ ℓ : ℕ, 1 ≤ ℓ → def_app_vol_lag F S ℓ t Fo Gi ϱ ϱ' = 0 := by
  intro ℓ hℓ
  haveI := lr_borel m n
  haveI := lr_sc m n
  have hϱ0 : 0 ≤ ϱ := le_trans hϱ.1.le hϱI.1
  have hϱ'0 : 0 ≤ ϱ' := le_trans hϱ.1.le hϱ'I.1
  have hind := lr_zero_ind_beta0 F S hβ0 t ℓ hℓ
  have hD := lr_zero_indep F S Fo Gi hF hG hϱ0 hϱ'0 t (frozenBuf F S (t + (ℓ : ℤ)))
    (lr_buf_meas F S _) hind
  have hX := lr_cen_meas F S hϱ0 t
  have hYm : Measurable (fun ω => Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω)) :=
    (lr_Q_meas hϱ'0).comp (lr_buf_meas F S _)
  have hYb : ∀ ω, fro (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω)) ≤
      Real.sqrt ((min m n : ℕ) : ℝ) := fun ω => lr_Q_fro_le hϱ'0 _
  have hmu : fro (mean P (frozenUpd F S ϱ' (t + (ℓ : ℤ)))) ≤
      Real.sqrt ((m : ℝ) * n) * Real.sqrt ((min m n : ℕ) : ℝ) :=
    lr_fro_le_of_entries _ _ (Real.sqrt_nonneg _) (fun i j => lr_mean_entry F S hϱ'0 _ i j)
  have hA : Integrable (fun ω => Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
      (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω))ᵀ)) P :=
    lr_trace_integrable Fo Gi hF hG _ _ hX hYm _ _ (fun ω => lr_cen_fro_le F S hϱ0 t ω) hYb
  have hC : Integrable (fun ω => Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
      (mean P (frozenUpd F S ϱ' (t + (ℓ : ℤ))))ᵀ)) P :=
    lr_trace_integrable Fo Gi hF hG _ (fun _ => mean P (frozenUpd F S ϱ' (t + (ℓ : ℤ))))
      hX measurable_const _ _ (fun ω => lr_cen_fro_le F S hϱ0 t ω) (fun _ => hmu)
  have h2 := lr_zero_const Fo Gi (centredUpd F S ϱ t)
    (fun a b => lr_cen_entry_int F S hϱ0 t a b) (fun a b => lr_cen_entry_zero F S hϱ0 t a b)
    (mean P (frozenUpd F S ϱ' (t + (ℓ : ℤ))))
  have e : ∀ ω, Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
      (centredUpd F S ϱ' (t + (ℓ : ℤ)) ω)ᵀ) =
      Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi * (Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω))ᵀ) -
      Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (mean P (frozenUpd F S ϱ' (t + (ℓ : ℤ))))ᵀ) := fun ω => by
    have hc : centredUpd F S ϱ' (t + (ℓ : ℤ)) ω =
        Q ϱ' (frozenBuf F S (t + (ℓ : ℤ)) ω) - mean P (frozenUpd F S ϱ' (t + (ℓ : ℤ))) := rfl
    rw [hc, lr_trace_sub_right]
  have key : ∫ ω, Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
      (centredUpd F S ϱ' (t + (ℓ : ℤ)) ω)ᵀ) ∂P = 0 := by
    simp_rw [e]
    rw [integral_sub hA hC, hD, h2, sub_zero]
  unfold def_app_vol_lag
  rw [key, mul_zero]

/-- Zero-lag clause of the independent product model: the pointwise bound
`|Tr[F Q_ϱ(M) G Q_ϱ'(M)ᵀ]| ≤ min(m,n)` (from `‖Q_ϱ(·)‖_F ≤ sqrt(min(m,n))`) and `min(m,n) ≤ γ⋆B`. -/
private lemma lr_indep_lag_zero (F : FrozenParams m n B) (γstar CSig : ℝ)
    (hS : SizeFin F.C B γstar CSig) (Fo : Mat m m) (Gi : Mat n n)
    (hF : opNorm Fo ≤ 1) (hG : opNorm Gi ≤ 1) (ϱ ϱ' : ℝ) (hϱ0 : 0 ≤ ϱ) (hϱ'0 : 0 ≤ ϱ')
    (t : ℤ) :
    |(B : ℝ)⁻¹ * ∫ ω, Matrix.trace (Fo * indepUpd F ϱ ω t * Gi * (indepUpd F ϱ' ω t)ᵀ)
        ∂(indepSpaceLaw m n B)| ≤ γstar := by
  have hB : (0 : ℝ) < B := by exact_mod_cast F.hB
  have hmin : ((min m n : ℕ) : ℝ) ≤ γstar * B :=
    le_trans (by exact_mod_cast (min_le_max : min m n ≤ max m n)) hS.1
  haveI : IsProbabilityMeasure (indepSpaceLaw m n B) := by
    unfold indepSpaceLaw indepSlotLaw
    infer_instance
  have hpt : ∀ ω, |Matrix.trace (Fo * indepUpd F ϱ ω t * Gi * (indepUpd F ϱ' ω t)ᵀ)| ≤
      ((min m n : ℕ) : ℝ) := by
    intro ω
    have h := lr_tested_le Fo Gi hF hG (indepUpd F ϱ ω t) (indepUpd F ϱ' ω t)
    have h1 : fro (indepUpd F ϱ ω t) ≤ Real.sqrt ((min m n : ℕ) : ℝ) :=
      lr_Q_fro_le hϱ0 _
    have h2 : fro (indepUpd F ϱ' ω t) ≤ Real.sqrt ((min m n : ℕ) : ℝ) :=
      lr_Q_fro_le hϱ'0 _
    have h3 : fro (indepUpd F ϱ ω t) * fro (indepUpd F ϱ' ω t) ≤
        Real.sqrt ((min m n : ℕ) : ℝ) * Real.sqrt ((min m n : ℕ) : ℝ) :=
      mul_le_mul h1 h2 (lr_fro_nn _) (Real.sqrt_nonneg _)
    rw [Real.mul_self_sqrt (Nat.cast_nonneg _)] at h3
    exact h.trans h3
  have hbound : ∀ᵐ ω ∂(indepSpaceLaw m n B),
      ‖Matrix.trace (Fo * indepUpd F ϱ ω t * Gi * (indepUpd F ϱ' ω t)ᵀ)‖ ≤
        ((min m n : ℕ) : ℝ) :=
    Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hpt ω
  have hI := norm_integral_le_of_norm_le_const hbound
  have hI' : |∫ ω, Matrix.trace (Fo * indepUpd F ϱ ω t * Gi * (indepUpd F ϱ' ω t)ᵀ)
      ∂(indepSpaceLaw m n B)| ≤ ((min m n : ℕ) : ℝ) := by
    rw [← Real.norm_eq_abs]
    simpa using hI
  rw [abs_mul, abs_of_pos (inv_pos.mpr hB), inv_mul_eq_div]
  rw [div_le_iff₀ hB]
  calc |∫ ω, Matrix.trace (Fo * indepUpd F ϱ ω t * Gi * (indepUpd F ϱ' ω t)ᵀ)
      ∂(indepSpaceLaw m n B)| ≤ ((min m n : ℕ) : ℝ) := hI'
    _ ≤ γstar * B := hmin

/-! ### Independent-model lag bound for `ℓ ≥ 1` (helpers, P4) -/

private lemma lri_prob (m n B : ℕ) : IsProbabilityMeasure (indepSpaceLaw m n B) := by
  unfold indepSpaceLaw indepSlotLaw
  infer_instance

private lemma lri_fro_smul {k l : ℕ} (c : ℝ) (K : Mat k l) : fro (c • K) = |c| * fro K := by
  have h : ∀ i j, ‖(c • K) i j‖ ^ 2 = c ^ 2 * ‖K i j‖ ^ 2 := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs, mul_pow, sq_abs]
  unfold fro
  simp only [h, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

private lemma lri_batch_meas_sub (F : FrozenParams m n B) (s : ℤ) (T : Set (ℤ × Fin B))
    (hT : ∀ a, (s, a) ∈ T) :
    Measurable[⨆ i ∈ T, MeasurableSpace.comap
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω i) inferInstance]
      (fun ω => indepBatchG F ω s) := by
  have h : ∀ a, Measurable[⨆ i ∈ T, MeasurableSpace.comap
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω i) inferInstance]
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω (s, a)) := fun a =>
    Measurable.of_comap_le (le_iSup₂ (f := fun i (_ : i ∈ T) => MeasurableSpace.comap
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω i) inferInstance) (s, a) (hT a))
  generalize (⨆ i ∈ T, MeasurableSpace.comap
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω i) inferInstance) = m1 at h ⊢
  letI : MeasurableSpace ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) := m1
  haveI := lr_borel m n
  haveI := lr_sc m n
  unfold indepBatchG
  refine Measurable.const_smul ?_ ((B : ℝ))⁻¹
  refine Finset.measurable_sum _ fun a _ => ?_
  have hc : Continuous (fun p : ℝ × (Vec m × Vec n) =>
      p.1 • (rOut F.C * outer p.2.1 p.2.2 * rIn F.C)) := by
    fun_prop
  exact hc.measurable.comp (h a)

private lemma lri_prod_meas (F : FrozenParams m n B) (s : ℤ) :
    Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => def_app_vol_product F ω s) := by
  haveI := lr_borel m n
  haveI := lr_sc m n
  unfold def_app_vol_product
  refine lr_tsum_meas _ _ fun j => ?_
  refine Measurable.const_smul ?_ (emaW F.β j)
  unfold indepBatchG
  refine Measurable.const_smul ?_ ((B : ℝ))⁻¹
  refine Finset.measurable_sum _ fun a _ => ?_
  have hc : Continuous (fun p : ℝ × (Vec m × Vec n) =>
      p.1 • (rOut F.C * outer p.2.1 p.2.2 * rIn F.C)) := by
    fun_prop
  exact hc.measurable.comp (measurable_pi_apply (s + 1 - (j : ℤ), a))

private lemma lri_batch_meas (F : FrozenParams m n B) (s : ℤ) :
    Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => indepBatchG F ω s) := by
  haveI := lr_borel m n
  haveI := lr_sc m n
  unfold indepBatchG
  refine Measurable.const_smul ?_ ((B : ℝ))⁻¹
  refine Finset.measurable_sum _ fun a _ => ?_
  have hc : Continuous (fun p : ℝ × (Vec m × Vec n) =>
      p.1 • (rOut F.C * outer p.2.1 p.2.2 * rIn F.C)) := by
    fun_prop
  exact hc.measurable.comp (measurable_pi_apply (s, a))

private lemma lri_indep (F : FrozenParams m n B) (t : ℤ) (ℓ : ℕ) :
    IndepFun (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => def_app_vol_product F ω t)
      (fun ω => ∑ j ∈ Finset.range ℓ,
        emaW F.β j • indepBatchG F ω (t + (ℓ : ℤ) + 1 - (j : ℤ)))
      (indepSpaceLaw m n B) := by
  haveI := lri_prob m n B
  have hI : iIndepFun (fun (p : ℤ × Fin B) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) => ω p)
      (indepSpaceLaw m n B) :=
    iIndepFun_infinitePi (P := fun _ : ℤ × Fin B => indepSlotLaw m n)
      (X := fun _ x => x) (fun _ => measurable_id)
  have hind := (iIndepFun_iff_iIndep
    (fun _ : ℤ × Fin B => (inferInstance : MeasurableSpace (ℝ × (Vec m × Vec n))))
    (fun (p : ℤ × Fin B) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) => ω p)
    (indepSpaceLaw m n B)).mp hI
  have hdisj : Disjoint {p : ℤ × Fin B | p.1 ≤ t + 1} {p : ℤ × Fin B | t + 2 ≤ p.1} := by
    rw [Set.disjoint_left]
    intro p h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2
    omega
  have key := indep_iSup_of_disjoint
    (fun p : ℤ × Fin B => (measurable_pi_apply (X := fun _ : ℤ × Fin B => ℝ × (Vec m × Vec n)) p).comap_le)
    hind hdisj
  have hA : Measurable[⨆ i ∈ {p : ℤ × Fin B | p.1 ≤ t + 1}, MeasurableSpace.comap
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω i) inferInstance]
      (fun ω => def_app_vol_product F ω t) := by
    unfold def_app_vol_product
    refine lr_tsum_meas _ _ fun j => ?_
    refine Measurable.const_smul ?_ (emaW F.β j)
    exact lri_batch_meas_sub F _ _ (fun a => by
      show t + 1 - (j : ℤ) ≤ t + 1
      omega)
  have hB : Measurable[⨆ i ∈ {p : ℤ × Fin B | t + 2 ≤ p.1}, MeasurableSpace.comap
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω i) inferInstance]
      (fun ω => ∑ j ∈ Finset.range ℓ,
        emaW F.β j • indepBatchG F ω (t + (ℓ : ℤ) + 1 - (j : ℤ))) := by
    refine lr_fsum_meas _ _ fun j hj => ?_
    rw [Finset.mem_range] at hj
    refine Measurable.const_smul ?_ (emaW F.β j)
    exact lri_batch_meas_sub F _ _ (fun a => by
      show t + 2 ≤ t + (ℓ : ℤ) + 1 - (j : ℤ)
      omega)
  exact (IndepFun_iff_Indep _ _ (indepSpaceLaw m n B)).mpr
    (indep_of_indep_of_le_left (indep_of_indep_of_le_right key (measurable_iff_comap_le.mp hB))
      (measurable_iff_comap_le.mp hA))

private lemma lri_mean_zero (F : FrozenParams m n B) {ϱ : ℝ} (hϱ : 0 < ϱ) (t : ℤ)
    (a : Fin m) (b : Fin n) :
    ∫ ω, Q ϱ (def_app_vol_product F ω t) a b ∂(indepSpaceLaw m n B) = 0 := by
  have hodd : ∀ x : ℝ, omegaF ϱ (-x) = -omegaF ϱ x := by
    intro x
    simp [omegaF, neg_div]
  have hbdd : ∃ M : ℝ, ∀ x : ℝ, |omegaF ϱ x| ≤ M := by
    refine ⟨1, fun x => ?_⟩
    have hpos : 0 < Real.sqrt (x ^ 2 + ϱ) := Real.sqrt_pos.mpr (by positivity)
    unfold omegaF
    rw [abs_div, abs_of_pos hpos, div_le_one hpos]
    exact Real.abs_le_sqrt (by linarith)
  have h := def_app_vol_product_mean_oddSharp F (omegaF ϱ) hodd hbdd t
  have h2 := congrFun (congrFun h a) b
  simp only [mean, Matrix.of_apply, Matrix.zero_apply] at h2
  have e : ∀ ω, oddSharp (omegaF ϱ) (def_app_vol_product F ω t) =
      Q ϱ (def_app_vol_product F ω t) := fun ω => eqn_app_vol_filters_sharp_ii hϱ _
  simp_rw [e] at h2
  exact h2

open scoped Matrix.Norms.Frobenius in
private lemma lri_decomp (F : FrozenParams m n B) (t : ℤ) (ℓ : ℕ) :
    ∀ᵐ ω ∂(indepSpaceLaw m n B), def_app_vol_product F ω (t + (ℓ : ℤ)) =
      (∑ j ∈ Finset.range ℓ, emaW F.β j • indepBatchG F ω (t + (ℓ : ℤ) + 1 - (j : ℤ))) +
      F.β ^ ℓ • def_app_vol_product F ω t := by
  filter_upwards [def_app_vol_product_summable F] with ω hω
  have hs : Summable fun j : ℕ =>
      emaW F.β j • indepBatchG F ω (t + (ℓ : ℤ) + 1 - (j : ℤ)) := by
    refine Summable.of_norm ?_
    simpa [fro_eq_norm] using hω (t + (ℓ : ℤ))
  unfold def_app_vol_product
  rw [← Summable.sum_add_tsum_nat_add' ((summable_nat_add_iff ℓ).2 hs)]
  congr 1
  have hshift : ∀ i : ℕ, emaW F.β (i + ℓ) • indepBatchG F ω (t + (ℓ : ℤ) + 1 - ((i + ℓ : ℕ) : ℤ)) =
      F.β ^ ℓ • (emaW F.β i • indepBatchG F ω (t + 1 - (i : ℤ))) := by
    intro i
    have e1 : t + (ℓ : ℤ) + 1 - ((i + ℓ : ℕ) : ℤ) = t + 1 - (i : ℤ) := by push_cast; ring
    have e2 : emaW F.β (i + ℓ) = F.β ^ ℓ * emaW F.β i := by
      unfold emaW; ring
    rw [e1, e2, smul_smul]
  simp_rw [hshift]
  exact tsum_const_smul'' _

private lemma lri_moment (F : FrozenParams m n B) (γstar CSig : ℝ)
    (hS : SizeFin F.C B γstar CSig) (t : ℤ) :
    Integrable (fun ω => fro (def_app_vol_product F ω t) ^ 2) (indepSpaceLaw m n B) ∧
    ∫ ω, fro (def_app_vol_product F ω t) ^ 2 ∂(indepSpaceLaw m n B) ≤
      CSig ^ 2 * γstar ^ 2 * B := by
  have hB : (0 : ℝ) < B := by exact_mod_cast F.hB
  have hβ0 := F.hβ.1
  have hβ1 := F.hβ.2
  refine ⟨?_, ?_⟩
  · by_contra hni
    have h0 := integral_undef hni
    have hm := def_app_vol_product_moment F t
    rw [h0, mul_zero, sPow_two hβ0 hβ1] at hm
    have hs2 : 0 < (1 - F.β) / (1 + F.β) := div_pos (by linarith) (by linarith)
    have hB2 : (0 : ℝ) < (B : ℝ) ^ 2 := by positivity
    have hprod : Matrix.trace F.C.Sout * Matrix.trace F.C.Sin = 0 := by
      have h1 : (1 - F.β) / (1 + F.β) / (B : ℝ) ^ 2 * Matrix.trace F.C.Sout *
          Matrix.trace F.C.Sin = 0 := hm.symm
      have h2 : (1 - F.β) / (1 + F.β) / (B : ℝ) ^ 2 ≠ 0 := (div_pos hs2 hB2).ne'
      rw [mul_assoc] at h1
      exact (mul_eq_zero.mp h1).resolve_left h2
    have hG : ∀ ω s, indepBatchG F ω s = 0 := by
      intro ω s
      rcases mul_eq_zero.mp hprod with h | h
      · have h0 : F.C.Sout = 0 := (F.C.psdOut.trace_eq_zero_iff).mp h
        unfold indepBatchG
        simp [rOut, h0, CFC.sqrt_zero]
      · have h0 : F.C.Sin = 0 := (F.C.psdIn.trace_eq_zero_iff).mp h
        unfold indepBatchG
        simp [rIn, h0, CFC.sqrt_zero]
    have hz : ∀ ω, def_app_vol_product F ω t = 0 := by
      intro ω
      unfold def_app_vol_product
      simp [hG]
    apply hni
    have : (fun ω => fro (def_app_vol_product F ω t) ^ 2) = fun _ => 0 := by
      funext ω
      rw [hz]
      simp [fro]
    rw [this]
    exact integrable_zero _ _ _
  · have h := def_app_vol_product_moment_le F γstar CSig hS t
    rw [inv_mul_le_iff₀ hB] at h
    calc _ ≤ (B : ℝ) * (CSig ^ 2 * γstar ^ 2) := h
      _ = _ := by ring

private lemma lri_zero (F : FrozenParams m n B) (Fo : Mat m m) (Gi : Mat n n)
    (hF : opNorm Fo ≤ 1) (hG : opNorm Gi ≤ 1) {ϱ ϱ' : ℝ} (hϱ : 0 < ϱ) (hϱ' : 0 ≤ ϱ') (t : ℤ)
    (Ntr : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → Mat m n) (htr : Measurable Ntr)
    (hind : IndepFun (fun ω => def_app_vol_product F ω t) Ntr (indepSpaceLaw m n B)) :
    ∫ ω, Matrix.trace (Fo * Q ϱ (def_app_vol_product F ω t) * Gi * (Q ϱ' (Ntr ω))ᵀ)
      ∂(indepSpaceLaw m n B) = 0 := by
  haveI := lri_prob m n B
  haveI := lr_borel m n
  haveI := lr_sc m n
  obtain ⟨f, hf⟩ : ∃ f : Fin m → Fin n → Mat m n → ℝ, f = fun a b K => (Q ϱ K) a b :=
    ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Fin m → Fin n → Mat m n → ℝ, g = fun a b K =>
      (Gi * (Q ϱ' K)ᵀ * Fo) b a := ⟨_, rfl⟩
  have hfm : ∀ a b, Measurable (f a b) := fun a b => by
    rw [hf]
    exact (measurable_pi_apply b).comp ((measurable_pi_apply a).comp (lr_Q_meas hϱ.le))
  have hgm : ∀ a b, Measurable (g a b) := fun a b => by
    rw [hg]
    have hc : Continuous (fun N : Mat m n => (Gi * Nᵀ * Fo) b a) := by fun_prop
    exact hc.measurable.comp (lr_Q_meas hϱ')
  have hbuf := lri_prod_meas F t
  have e1 : ∀ ω, Matrix.trace (Fo * Q ϱ (def_app_vol_product F ω t) * Gi *
      (Q ϱ' (Ntr ω))ᵀ) = ∑ a, ∑ b,
        f a b (def_app_vol_product F ω t) * g a b (Ntr ω) := by
    intro ω
    rw [lr_expand, hf, hg]
  have hint : ∀ a b, Integrable (fun ω => f a b (def_app_vol_product F ω t) *
      g a b (Ntr ω)) (indepSpaceLaw m n B) := by
    intro a b
    refine lr_int_mul_bdd _ _ ((hfm a b).comp hbuf) ((hgm a b).comp htr)
      (Real.sqrt ((min m n : ℕ) : ℝ)) (Real.sqrt ((min m n : ℕ) : ℝ)) (fun ω => ?_) (fun ω => ?_)
    · have : f a b (def_app_vol_product F ω t) = Q ϱ (def_app_vol_product F ω t) a b := by
        rw [hf]
      rw [this]
      exact (lr_abs_entry_le_fro _ a b).trans (lr_Q_fro_le hϱ.le _)
    · have : g a b (Ntr ω) = (Gi * (Q ϱ' (Ntr ω))ᵀ * Fo) b a := by
        rw [hg]
      rw [this]
      refine (lr_abs_entry_le_fro _ b a).trans ?_
      refine (lr_fro_sandwich Gi _ Fo hG hF).trans ?_
      rw [lr_fro_transpose]
      exact lr_Q_fro_le hϱ' _
  simp_rw [e1]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hint a b))]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [integral_finsetSum _ (fun b _ => hint a b)]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [hind.integral_fun_comp_mul_comp hbuf.aemeasurable htr.aemeasurable
    (hfm a b).aestronglyMeasurable (hgm a b).aestronglyMeasurable]
  have : ∫ ω, f a b (def_app_vol_product F ω t) ∂(indepSpaceLaw m n B) = 0 := by
    have e : ∀ ω, f a b (def_app_vol_product F ω t) = Q ϱ (def_app_vol_product F ω t) a b := by
      intro ω; rw [hf]
    simp_rw [e]
    exact lri_mean_zero F hϱ t a b
  rw [this, zero_mul]

/-- `thm:app-vol-lag-reduction`, part (ii), independent-covariance clause (`_ii_indep`), snapshot
`cr-2026-10-23`. Statement: the sentence `The same bounds hold for the independent covariances
C^g_ℓ[F,G] ... under the size conditions` of item (ii) above, with `C^g_ℓ` written as `B⁻¹ 𝔼 Tr[F
S^g_t G (S^g_{t+ℓ})ᵀ]` (`eqn:app-vol-product`, uncentred). Sorried: proof card P4. -/
theorem thm_app_vol_lag_reduction_ii_indep (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    [IsProbabilityMeasure P]
    (γstar CSig ϱlo ϱhi : ℝ) (hS : SizeFin F.C B γstar CSig) (hCSig : 1 ≤ CSig)
    (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi)
    (Fo : Mat m m) (Gi : Mat n n) (hFs : Fo.transpose = Fo) (hGs : Gi.transpose = Gi)
    (hF : opNorm Fo ≤ 1) (hG : opNorm Gi ≤ 1)
    (ϱ ϱ' : ℝ) (hϱI : ϱ ∈ Set.Icc ϱlo ϱhi) (hϱ'I : ϱ' ∈ Set.Icc ϱlo ϱhi)
    (t : ℤ) :
    |(B : ℝ)⁻¹ * ∫ ω, Matrix.trace (Fo * indepUpd F ϱ ω t * Gi * (indepUpd F ϱ' ω t)ᵀ)
        ∂(indepSpaceLaw m n B)| ≤ γstar ∧
      ∀ ℓ : ℕ, 1 ≤ ℓ →
        |(B : ℝ)⁻¹ * ∫ ω, Matrix.trace (Fo * indepUpd F ϱ ω t * Gi *
            (indepUpd F ϱ' ω (t + (ℓ : ℤ)))ᵀ) ∂(indepSpaceLaw m n B)| ≤
          Muon.Dynamics.kStar CSig γstar ϱlo * F.β ^ ℓ := by
  have hϱ0' : 0 < ϱ := lt_of_lt_of_le hϱ.1 hϱI.1
  have hϱ'pos : 0 < ϱ' := lt_of_lt_of_le hϱ.1 hϱ'I.1
  refine ⟨lr_indep_lag_zero F γstar CSig hS Fo Gi hF hG ϱ ϱ' hϱ0'.le hϱ'pos.le t,
    fun ℓ hℓ => ?_⟩
  haveI := lri_prob m n B
  haveI := lr_borel m n
  haveI := lr_sc m n
  have hBpos : (0 : ℝ) < B := by exact_mod_cast F.hB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast F.hB
  obtain ⟨hβ0, hβ1⟩ := F.hβ
  have hγ : 0 ≤ γstar := by
    have h1 : (0 : ℝ) ≤ ((max m n : ℕ) : ℝ) := Nat.cast_nonneg _
    have := hS.1
    by_contra hneg
    push_neg at hneg
    nlinarith [mul_neg_of_neg_of_pos hneg hBpos]
  have hCs : 0 ≤ CSig := le_trans (lr_opNorm_nonneg _) hS.2.1
  have hminle : ((min m n : ℕ) : ℝ) ≤ γstar * B :=
    le_trans (by exact_mod_cast (min_le_max : min m n ≤ max m n)) hS.1
  obtain ⟨Nl, hNl⟩ : ∃ Nl : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → Mat m n,
      Nl = fun ω => ∑ j ∈ Finset.range ℓ,
        emaW F.β j • indepBatchG F ω (t + (ℓ : ℤ) + 1 - (j : ℤ)) := ⟨_, rfl⟩
  have hNlm : Measurable Nl := by
    rw [hNl]
    exact Finset.measurable_sum _ fun j _ =>
      (lri_batch_meas F (t + (ℓ : ℤ) + 1 - (j : ℤ))).const_smul (emaW F.β j)
  have hind : IndepFun (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => def_app_vol_product F ω t)
      Nl (indepSpaceLaw m n B) := by
    rw [hNl]
    exact lri_indep F t ℓ
  obtain ⟨X, hXd⟩ : ∃ X : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → Mat m n,
      X = fun ω => Q ϱ (def_app_vol_product F ω t) := ⟨_, rfl⟩
  obtain ⟨Y, hYd⟩ : ∃ Y : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → Mat m n,
      Y = fun ω => Q ϱ' (def_app_vol_product F ω (t + (ℓ : ℤ))) := ⟨_, rfl⟩
  obtain ⟨Nq, hNqd⟩ : ∃ Nq : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → Mat m n,
      Nq = fun ω => Q ϱ' (Nl ω) := ⟨_, rfl⟩
  have hXm : Measurable X := by
    rw [hXd]; exact (lr_Q_meas hϱ0'.le).comp (lri_prod_meas F t)
  have hYm : Measurable Y := by
    rw [hYd]; exact (lr_Q_meas hϱ'pos.le).comp (lri_prod_meas F _)
  have hNqm : Measurable Nq := by
    rw [hNqd]; exact (lr_Q_meas hϱ'pos.le).comp hNlm
  have hXb : ∀ ω, fro (X ω) ≤ Real.sqrt ((min m n : ℕ) : ℝ) := fun ω => by
    rw [hXd]; exact lr_Q_fro_le hϱ0'.le _
  have hYb : ∀ ω, fro (Y ω) ≤ Real.sqrt ((min m n : ℕ) : ℝ) := fun ω => by
    rw [hYd]; exact lr_Q_fro_le hϱ'pos.le _
  have hNqb : ∀ ω, fro (Nq ω) ≤ Real.sqrt ((min m n : ℕ) : ℝ) := fun ω => by
    rw [hNqd]; exact lr_Q_fro_le hϱ'pos.le _
  have hDm : Measurable (fun ω => Y ω - Nq ω) := by
    have hsub : Measurable (fun p : Mat m n × Mat m n => p.1 - p.2) :=
      (continuous_fst.sub continuous_snd).measurable
    exact hsub.comp (hYm.prodMk hNqm)
  have hDb : ∀ ω, fro (Y ω - Nq ω) ≤ 2 * Real.sqrt ((min m n : ℕ) : ℝ) := fun ω => by
    have := lr_fro_triangle (Y ω) (Nq ω)
    linarith [hYb ω, hNqb ω]
  have hz : ∫ ω, Matrix.trace (Fo * X ω * Gi * (Nq ω)ᵀ) ∂(indepSpaceLaw m n B) = 0 := by
    rw [hXd, hNqd]
    exact lri_zero F Fo Gi hF hG hϱ0' hϱ'pos.le t Nl hNlm hind
  have hpt : ∀ ω, Matrix.trace (Fo * X ω * Gi * (Y ω)ᵀ) =
      Matrix.trace (Fo * X ω * Gi * (Y ω - Nq ω)ᵀ) +
      Matrix.trace (Fo * X ω * Gi * (Nq ω)ᵀ) := fun ω => by
    rw [lr_trace_sub_right]; ring
  have iA : Integrable (fun ω => Matrix.trace (Fo * X ω * Gi * (Y ω - Nq ω)ᵀ))
      (indepSpaceLaw m n B) :=
    lr_trace_integrable Fo Gi hF hG _ _ hXm hDm _ _ hXb hDb
  have iB : Integrable (fun ω => Matrix.trace (Fo * X ω * Gi * (Nq ω)ᵀ))
      (indepSpaceLaw m n B) :=
    lr_trace_integrable Fo Gi hF hG _ _ hXm hNqm _ _ hXb hNqb
  have hI0 : ∫ ω, Matrix.trace (Fo * X ω * Gi * (Y ω)ᵀ) ∂(indepSpaceLaw m n B) =
      ∫ ω, Matrix.trace (Fo * X ω * Gi * (Y ω - Nq ω)ᵀ) ∂(indepSpaceLaw m n B) := by
    simp_rw [hpt]
    rw [integral_add iA iB, hz, add_zero]
  -- Cauchy–Schwarz
  have hsqint : ∀ (f : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → ℝ), Measurable f → ∀ c : ℝ,
      (∀ ω, |f ω| ≤ c) → Integrable (fun ω => f ω ^ 2) (indepSpaceLaw m n B) :=
    fun f hf c hc =>
    Integrable.of_bound (C := c ^ 2) (hf.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hc ω) 2)
  have haM : Measurable (fun ω => fro (X ω)) := lr_fro_meas.comp hXm
  have hbM : Measurable (fun ω => fro (Y ω - Nq ω)) := lr_fro_meas.comp hDm
  have haI := hsqint _ haM _ (fun ω => by
    rw [abs_of_nonneg (lr_fro_nn _)]; exact hXb ω)
  have hbI := hsqint _ hbM _ (fun ω => by
    rw [abs_of_nonneg (lr_fro_nn _)]; exact hDb ω)
  have hcs := lr_cs _ _ haM hbM haI hbI
  have habI : Integrable (fun ω => fro (X ω) * fro (Y ω - Nq ω)) (indepSpaceLaw m n B) :=
    lr_int_mul_bdd _ _ haM hbM _ _
      (fun ω => by rw [abs_of_nonneg (lr_fro_nn _)]; exact hXb ω)
      (fun ω => by rw [abs_of_nonneg (lr_fro_nn _)]; exact hDb ω)
  have hI1 : |∫ ω, Matrix.trace (Fo * X ω * Gi * (Y ω - Nq ω)ᵀ) ∂(indepSpaceLaw m n B)| ≤
      ∫ ω, fro (X ω) * fro (Y ω - Nq ω) ∂(indepSpaceLaw m n B) :=
    (abs_integral_le_integral_abs).trans
      (integral_mono iA.abs habI fun ω => lr_tested_le Fo Gi hF hG _ _)
  -- second moment of the difference
  have hmom := lri_moment F γstar CSig hS t
  have hdec := lri_decomp F t ℓ
  have hρ : (ϱ' ^ (-(1 / 2 : ℝ))) ^ 2 = ϱ'⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hϱ'pos.le]
    norm_num
    exact Real.rpow_neg_one ϱ'
  have hpw : ∀ᵐ ω ∂(indepSpaceLaw m n B), fro (Y ω - Nq ω) ^ 2 ≤
      ϱ'⁻¹ * (F.β ^ (2 * ℓ) * fro (def_app_vol_product F ω t) ^ 2) := by
    filter_upwards [hdec] with ω hω
    have h1 := Muon.Foundations.fro_Q_sub_Q_le hϱ'pos (def_app_vol_product F ω (t + (ℓ : ℤ))) (Nl ω)
    have h2 : def_app_vol_product F ω (t + (ℓ : ℤ)) - Nl ω =
        F.β ^ ℓ • def_app_vol_product F ω t := by
      rw [hω, hNl]
      abel
    rw [h2, lri_fro_smul, abs_of_nonneg (pow_nonneg hβ0 _)] at h1
    have h3 : fro (Y ω - Nq ω) ≤ ϱ' ^ (-(1 / 2 : ℝ)) *
        (F.β ^ ℓ * fro (def_app_vol_product F ω t)) := by
      rw [hYd, hNqd]
      exact h1
    calc fro (Y ω - Nq ω) ^ 2 ≤ (ϱ' ^ (-(1 / 2 : ℝ)) *
        (F.β ^ ℓ * fro (def_app_vol_product F ω t))) ^ 2 :=
          pow_le_pow_left₀ (lr_fro_nn _) h3 2
      _ = ϱ'⁻¹ * (F.β ^ (2 * ℓ) * fro (def_app_vol_product F ω t) ^ 2) := by
          rw [mul_pow, mul_pow, ← pow_mul, mul_comm ℓ 2, hρ]
  have hg_int : Integrable (fun ω => ϱ'⁻¹ * (F.β ^ (2 * ℓ) *
      fro (def_app_vol_product F ω t) ^ 2)) (indepSpaceLaw m n B) :=
    (hmom.1.const_mul _).const_mul _
  have hd1 : ∫ ω, fro (Y ω - Nq ω) ^ 2 ∂(indepSpaceLaw m n B) ≤
      ∫ ω, ϱ'⁻¹ * (F.β ^ (2 * ℓ) * fro (def_app_vol_product F ω t) ^ 2)
        ∂(indepSpaceLaw m n B) := integral_mono_ae hbI hg_int hpw
  have hd2 : ∫ ω, ϱ'⁻¹ * (F.β ^ (2 * ℓ) * fro (def_app_vol_product F ω t) ^ 2)
        ∂(indepSpaceLaw m n B) =
      ϱ'⁻¹ * (F.β ^ (2 * ℓ) * ∫ ω, fro (def_app_vol_product F ω t) ^ 2
        ∂(indepSpaceLaw m n B)) := by
    rw [integral_const_mul, integral_const_mul]
  have hd0 : ∫ ω, fro (Y ω - Nq ω) ^ 2 ∂(indepSpaceLaw m n B) ≤
      ϱ'⁻¹ * (F.β ^ (2 * ℓ) * (0 + 1 * (CSig ^ 2 * γstar ^ 2 * B))) := by
    refine hd1.trans ?_
    rw [hd2]
    have hb : 0 ≤ F.β ^ (2 * ℓ) := by positivity
    have h5 : ∫ ω, fro (def_app_vol_product F ω t) ^ 2 ∂(indepSpaceLaw m n B) ≤
        0 + 1 * (CSig ^ 2 * γstar ^ 2 * B) := by linarith [hmom.2]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 hb) (inv_nonneg.2 hϱ'pos.le)
  have hx0 : ∫ ω, fro (X ω) ^ 2 ∂(indepSpaceLaw m n B) ≤ γstar * B := by
    have hle : ∀ ω, fro (X ω) ^ 2 ≤ γstar * B := fun ω => by
      have h1 := pow_le_pow_left₀ (lr_fro_nn _) (hXb ω) 2
      rw [Real.sq_sqrt (Nat.cast_nonneg _)] at h1
      linarith
    calc ∫ ω, fro (X ω) ^ 2 ∂(indepSpaceLaw m n B) ≤
        ∫ _ω, γstar * B ∂(indepSpaceLaw m n B) := integral_mono haI (integrable_const _) hle
      _ = γstar * B := by simp
  have hI : (∫ ω, Matrix.trace (Fo * X ω * Gi * (Y ω - Nq ω)ᵀ) ∂(indepSpaceLaw m n B)) ^ 2 ≤
      (∫ ω, fro (X ω) ^ 2 ∂(indepSpaceLaw m n B)) *
        (∫ ω, fro (Y ω - Nq ω) ^ 2 ∂(indepSpaceLaw m n B)) := by
    refine le_trans ?_ hcs
    have h1 := hI1
    have h2 := abs_nonneg (∫ ω, Matrix.trace (Fo * X ω * Gi * (Y ω - Nq ω)ᵀ)
      ∂(indepSpaceLaw m n B))
    calc _ = |∫ ω, Matrix.trace (Fo * X ω * Gi * (Y ω - Nq ω)ᵀ)
          ∂(indepSpaceLaw m n B)| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ h2 h1 2
  have hV : 0 ≤ CSig ^ 2 * γstar ^ 2 * B := by positivity
  have hV' : CSig ^ 2 * γstar ^ 2 * B ≤
      CSig ^ 2 * ((γstar * B) * (γstar * B) + 2 * (γstar * B) + 2 * (γstar * B) + 3) / B := by
    rw [le_div_iff₀ hBpos]
    have h1 : 0 ≤ CSig ^ 2 * (4 * (γstar * B) + 3) := by positivity
    nlinarith [h1]
  have hGB : 0 ≤ γstar * B := by positivity
  have hnum := lr_numeric γstar CSig ϱlo ϱ' F.β (B : ℝ)
    (∫ ω, Matrix.trace (Fo * X ω * Gi * (Y ω - Nq ω)ᵀ) ∂(indepSpaceLaw m n B))
    (∫ ω, fro (X ω) ^ 2 ∂(indepSpaceLaw m n B))
    (∫ ω, fro (Y ω - Nq ω) ^ 2 ∂(indepSpaceLaw m n B))
    (γstar * B) (γstar * B) 0 1 (CSig ^ 2 * γstar ^ 2 * B) ℓ hB1 hγ hCs hϱ.1 hϱ'I.1 hβ0
    hI hx0 (integral_nonneg fun ω => sq_nonneg _) (integral_nonneg fun ω => sq_nonneg _) hd0
    le_rfl (sq_nonneg _) zero_le_one le_rfl hV hV' hGB le_rfl hGB le_rfl
  have key : |(B : ℝ)⁻¹ * ∫ ω, Matrix.trace (Fo * X ω * Gi * (Y ω)ᵀ)
      ∂(indepSpaceLaw m n B)| ≤ Muon.Dynamics.kStar CSig γstar ϱlo * F.β ^ ℓ := by
    rw [hI0]
    unfold Muon.Dynamics.kStar
    exact hnum
  rw [hXd, hYd] at key
  exact key

/-- Private helper (fully proved): the summation/tail/middle estimate behind `_iii_bound`. -/
private lemma lrIII_core (c : ℕ → ℝ) (M β : ℝ) (hM : 0 ≤ M) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hc : ∀ ℓ : ℕ, 1 ≤ ℓ → |c ℓ| ≤ M * β ^ ℓ) (T : ℕ) (hT : 1 ≤ T) (a0 : ℝ) :
    |(a0 + ∑' ℓ : ℕ, c (ℓ + 1)) - (a0 + ∑ ℓ ∈ Finset.Ico 1 T, (1 - (ℓ : ℝ) / (T : ℝ)) * c ℓ)| ≤
      M * (β ^ T / (1 - β) + β / ((T : ℝ) * (1 - β) ^ 2)) := by
  obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
  push_cast
  have hr : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1
  have hgeo : Summable (fun n : ℕ => β ^ n) := summable_geometric_of_lt_one hβ0 hβ1
  have hgeo1 : Summable (fun n : ℕ => β ^ (n + 1)) := (summable_nat_add_iff 1).mpr hgeo
  have hsl : Summable (fun n : ℕ => (n : ℝ) * β ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hsumg : Summable (fun j : ℕ => c (j + 1)) :=
    Summable.of_norm_bounded (hgeo1.mul_left M) (fun j => by
      rw [Real.norm_eq_abs]; exact hc (j + 1) (by omega))
  have hsplit : ∑ j ∈ Finset.range T', c (j + 1) + ∑' i : ℕ, c (i + T' + 1) =
      ∑' j : ℕ, c (j + 1) := hsumg.sum_add_tsum_nat_add T'
  have hIco : ∑ j ∈ Finset.range T', c (j + 1) = ∑ ℓ ∈ Finset.Ico 1 (T' + 1), c ℓ := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    exact Finset.sum_congr rfl fun j _ => by rw [add_comm]
  -- tail
  have hb : Summable (fun j : ℕ => M * β ^ (j + T' + 1)) := by
    have h1 : Summable (fun j : ℕ => β ^ (j + (T' + 1))) :=
      (summable_nat_add_iff (T' + 1)).mpr hgeo
    have h2 : Summable (fun j : ℕ => β ^ (j + T' + 1)) := by
      simpa only [add_assoc] using h1
    exact h2.mul_left M
  have hab : Summable (fun j : ℕ => |c (j + T' + 1)|) :=
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) (fun j => hc _ (by omega)) hb
  have htail : |∑' j : ℕ, c (j + T' + 1)| ≤ M * β ^ (T' + 1) / (1 - β) := by
    have hab' : Summable (fun j : ℕ => ‖c (j + T' + 1)‖) := by
      simpa only [Real.norm_eq_abs] using hab
    have e1 := norm_tsum_le_tsum_norm hab'
    have e2 : ∑' j : ℕ, |c (j + T' + 1)| ≤ ∑' j : ℕ, M * β ^ (j + T' + 1) :=
      Summable.tsum_le_tsum (fun j => hc (j + T' + 1) (by omega)) hab hb
    have e3 : ∑' j : ℕ, M * β ^ (j + T' + 1) = M * β ^ (T' + 1) / (1 - β) := by
      have : (fun j : ℕ => M * β ^ (j + T' + 1)) = fun j => (M * β ^ (T' + 1)) * β ^ j :=
        funext fun j => by ring
      rw [this, tsum_mul_left, tsum_geometric_of_lt_one hβ0 hβ1, div_eq_mul_inv]
    simp only [Real.norm_eq_abs] at e1
    linarith
  -- middle
  have hW1 : |∑ ℓ ∈ Finset.Ico 1 (T' + 1), ((ℓ : ℝ) / ((T' : ℝ) + 1)) * c ℓ| ≤
      ∑ ℓ ∈ Finset.Ico 1 (T' + 1), (M / ((T' : ℝ) + 1)) * ((ℓ : ℝ) * β ^ ℓ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ℓ hℓ => ?_)
    have hℓ1 : 1 ≤ ℓ := (Finset.mem_Ico.mp hℓ).1
    have hnn : (0 : ℝ) ≤ (ℓ : ℝ) / ((T' : ℝ) + 1) := by positivity
    rw [abs_mul, abs_of_nonneg hnn]
    calc (ℓ : ℝ) / ((T' : ℝ) + 1) * |c ℓ| ≤ (ℓ : ℝ) / ((T' : ℝ) + 1) * (M * β ^ ℓ) :=
          mul_le_mul_of_nonneg_left (hc ℓ hℓ1) hnn
      _ = (M / ((T' : ℝ) + 1)) * ((ℓ : ℝ) * β ^ ℓ) := by ring
  have hW2 : ∑ ℓ ∈ Finset.Ico 1 (T' + 1), (M / ((T' : ℝ) + 1)) * ((ℓ : ℝ) * β ^ ℓ) ≤
      M / ((T' : ℝ) + 1) * (β / (1 - β) ^ 2) := by
    have h := Summable.sum_le_tsum (Finset.Ico 1 (T' + 1)) (fun ℓ _ => mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg hβ0 _)) hsl
    rw [tsum_coe_mul_geometric_of_norm_lt_one hr] at h
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left h (div_nonneg hM (by positivity))
  -- assembly
  have hid : ∑ ℓ ∈ Finset.Ico 1 (T' + 1), (1 - (ℓ : ℝ) / ((T' : ℝ) + 1)) * c ℓ =
      ∑ ℓ ∈ Finset.Ico 1 (T' + 1), c ℓ -
        ∑ ℓ ∈ Finset.Ico 1 (T' + 1), ((ℓ : ℝ) / ((T' : ℝ) + 1)) * c ℓ := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ℓ _ => by ring
  have key : (a0 + ∑' j : ℕ, c (j + 1)) - (a0 + ∑ ℓ ∈ Finset.Ico 1 (T' + 1),
      (1 - (ℓ : ℝ) / ((T' : ℝ) + 1)) * c ℓ) =
      ∑' i : ℕ, c (i + T' + 1) + ∑ ℓ ∈ Finset.Ico 1 (T' + 1),
        ((ℓ : ℝ) / ((T' : ℝ) + 1)) * c ℓ := by
    rw [hid, ← hIco, ← hsplit]
    ring
  rw [key]
  have hβ1' : (0 : ℝ) < 1 - β := sub_pos.mpr hβ1
  calc _ ≤ |∑' i : ℕ, c (i + T' + 1)| + |∑ ℓ ∈ Finset.Ico 1 (T' + 1),
        ((ℓ : ℝ) / ((T' : ℝ) + 1)) * c ℓ| := abs_add_le _ _
    _ ≤ M * β ^ (T' + 1) / (1 - β) + M / ((T' : ℝ) + 1) * (β / (1 - β) ^ 2) :=
        add_le_add htail (hW1.trans hW2)
    _ = M * (β ^ (T' + 1) / (1 - β) + β / (((T' : ℝ) + 1) * (1 - β) ^ 2)) := by
        field_simp

/- `thm:app-vol-lag-reduction`, part (iii), snapshot `cr-2026-10-23`. Source for the two
declarations below. The statement, verbatim from `section.tex` (header and this part of the
theorem):
```latex
\begin{theorem}[Lag reduction]\label{thm:app-vol-lag-reduction}
Under \cref{assum:app-setup-regime}, let $F,G$ be symmetric with
$\norm F,\norm G\le1$ and $\ridge,\ridge'\in I$.
\begin{enumerate}[label=(\roman*)]
\item The series \cref{eqn:app-vol-Gamma} converges absolutely, and the left
side of \cref{eqn:app-vol-finite-time} differs from $\Gamma[F,G](\ridge,\ridge')$
by at most
\begin{equation}\label{eqn:app-vol-finite-time-error}
2\mathsf K_\star\Big(\frac{\bmom^T}{1-\bmom}+\frac{\bmom}{T(1-\bmom)^2}\Big).
\end{equation}
\end{theorem}
```
The regime hypotheses of `assum:app-setup-regime` enter as fixed-dimension hypotheses: `SizeFin`
(dimensions, `‖Σ‖ ≤ C_Σ`), `1 ≤ C_Σ`, `0 < ϱ₋ ≤ ϱ₊` and `ϱ, ϱ' ∈ [ϱ₋, ϱ₊]`; the momentum `β = F.β
∈ [0,1)` is a field of `FrozenParams`. `F`, `G` are the symmetric test matrices with `‖·‖ ≤ 1`.
The `C_ℓ` carry the time `t`, and the statement is for every `t` (stationarity is
`lem:app-setup-ema-law`(ii), a theorem, not a hypothesis). Declared as two theorems: absolute
convergence of the series in `eqn:app-vol-Gamma` (`_iii_summable`) and the finite-time error bound
(`_iii_bound`). Sorried: proof card P5.
-/
/-- `thm:app-vol-lag-reduction`, part (iii), absolute convergence (`_iii_summable`), snapshot
`cr-2026-10-23`. Statement: the first sentence of item (iii) above. Sorried: proof card P5. -/
theorem thm_app_vol_lag_reduction_iii_summable (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    [IsProbabilityMeasure P]
    (γstar CSig ϱlo ϱhi : ℝ) (hS : SizeFin F.C B γstar CSig) (hCSig : 1 ≤ CSig)
    (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi)
    (Fo : Mat m m) (Gi : Mat n n) (hFs : Fo.transpose = Fo) (hGs : Gi.transpose = Gi)
    (hF : opNorm Fo ≤ 1) (hG : opNorm Gi ≤ 1)
    (ϱ ϱ' : ℝ) (hϱI : ϱ ∈ Set.Icc ϱlo ϱhi) (hϱ'I : ϱ' ∈ Set.Icc ϱlo ϱhi)
    (t : ℤ) :
    Summable fun ℓ : ℕ => |def_app_vol_lag F S (ℓ + 1) t Fo Gi ϱ ϱ' +
      def_app_vol_lag F S (ℓ + 1) t Fo Gi ϱ' ϱ| := by
  have hCs : 0 ≤ CSig := le_trans (lr_opNorm_nonneg _) hS.2.1
  have hK : 0 ≤ Muon.Dynamics.kStar CSig γstar ϱlo := by
    unfold Muon.Dynamics.kStar
    exact mul_nonneg hCs (Real.sqrt_nonneg _)
  obtain ⟨hβ0, hβ1⟩ := F.hβ
  have hA := (thm_app_vol_lag_reduction_ii_actual F S γstar CSig ϱlo ϱhi hS hCSig hϱ Fo Gi
    hFs hGs hF hG ϱ ϱ' hϱI hϱ'I t).2
  have hA' := (thm_app_vol_lag_reduction_ii_actual F S γstar CSig ϱlo ϱhi hS hCSig hϱ Fo Gi
    hFs hGs hF hG ϱ' ϱ hϱ'I hϱI t).2
  have hgeo : Summable (fun n : ℕ => F.β ^ n) := summable_geometric_of_lt_one hβ0 hβ1
  have hgeo1 : Summable (fun n : ℕ => F.β ^ (n + 1)) := (summable_nat_add_iff 1).mpr hgeo
  refine Summable.of_nonneg_of_le (fun ℓ => abs_nonneg _) (fun ℓ => ?_)
    (hgeo1.mul_left (2 * Muon.Dynamics.kStar CSig γstar ϱlo))
  have h1 := hA (ℓ + 1) (by omega)
  have h2 := hA' (ℓ + 1) (by omega)
  calc _ ≤ |def_app_vol_lag F S (ℓ + 1) t Fo Gi ϱ ϱ'| +
        |def_app_vol_lag F S (ℓ + 1) t Fo Gi ϱ' ϱ| := abs_add_le _ _
    _ ≤ Muon.Dynamics.kStar CSig γstar ϱlo * F.β ^ (ℓ + 1) +
        Muon.Dynamics.kStar CSig γstar ϱlo * F.β ^ (ℓ + 1) := add_le_add h1 h2
    _ = 2 * Muon.Dynamics.kStar CSig γstar ϱlo * F.β ^ (ℓ + 1) := by ring

/-- `thm:app-vol-lag-reduction`, part (iii), finite-time error (`_iii_bound`), snapshot
`cr-2026-10-23`. Statement: the error display `eqn:app-vol-finite-time-error` of item (iii) above,
with the left side of `eqn:app-vol-finite-time` written as `finiteTimeCov`. Sorried: proof card
P5. -/
theorem thm_app_vol_lag_reduction_iii_bound (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    [IsProbabilityMeasure P]
    (γstar CSig ϱlo ϱhi : ℝ) (hS : SizeFin F.C B γstar CSig) (hCSig : 1 ≤ CSig)
    (hϱ : 0 < ϱlo ∧ ϱlo ≤ ϱhi)
    (Fo : Mat m m) (Gi : Mat n n) (hFs : Fo.transpose = Fo) (hGs : Gi.transpose = Gi)
    (hF : opNorm Fo ≤ 1) (hG : opNorm Gi ≤ 1)
    (ϱ ϱ' : ℝ) (hϱI : ϱ ∈ Set.Icc ϱlo ϱhi) (hϱ'I : ϱ' ∈ Set.Icc ϱlo ϱhi)
    (T : ℕ) (hT : 1 ≤ T) (t : ℤ) :
    |finiteTimeCov F S T ϱ ϱ' Fo Gi - integratedLag F S t Fo Gi ϱ ϱ'| ≤
      2 * Muon.Dynamics.kStar CSig γstar ϱlo *
        (F.β ^ T / (1 - F.β) + F.β / ((T : ℝ) * (1 - F.β) ^ 2)) := by
  have hCs : 0 ≤ CSig := le_trans (lr_opNorm_nonneg _) hS.2.1
  have hK : 0 ≤ Muon.Dynamics.kStar CSig γstar ϱlo := by
    unfold Muon.Dynamics.kStar
    exact mul_nonneg hCs (Real.sqrt_nonneg _)
  obtain ⟨hβ0, hβ1⟩ := F.hβ
  have hI := thm_app_vol_lag_reduction_i F S γstar CSig ϱlo ϱhi hS hCSig hϱ Fo Gi hFs hGs
    hF hG ϱ ϱ' hϱI hϱ'I T hT t
  have hA := thm_app_vol_lag_reduction_ii_actual F S γstar CSig ϱlo ϱhi hS hCSig hϱ Fo Gi
    hFs hGs hF hG ϱ ϱ' hϱI hϱ'I t
  have hA' := thm_app_vol_lag_reduction_ii_actual F S γstar CSig ϱlo ϱhi hS hCSig hϱ Fo Gi
    hFs hGs hF hG ϱ' ϱ hϱ'I hϱI t
  have hc : ∀ ℓ : ℕ, 1 ≤ ℓ →
      |def_app_vol_lag F S ℓ t Fo Gi ϱ ϱ' + def_app_vol_lag F S ℓ t Fo Gi ϱ' ϱ| ≤
        2 * Muon.Dynamics.kStar CSig γstar ϱlo * F.β ^ ℓ := fun ℓ hℓ => by
    have h1 := hA.2 ℓ hℓ
    have h2 := hA'.2 ℓ hℓ
    calc _ ≤ |def_app_vol_lag F S ℓ t Fo Gi ϱ ϱ'| + |def_app_vol_lag F S ℓ t Fo Gi ϱ' ϱ| :=
          abs_add_le _ _
      _ ≤ Muon.Dynamics.kStar CSig γstar ϱlo * F.β ^ ℓ +
          Muon.Dynamics.kStar CSig γstar ϱlo * F.β ^ ℓ := add_le_add h1 h2
      _ = 2 * Muon.Dynamics.kStar CSig γstar ϱlo * F.β ^ ℓ := by ring
  have h := lrIII_core
    (fun ℓ => def_app_vol_lag F S ℓ t Fo Gi ϱ ϱ' + def_app_vol_lag F S ℓ t Fo Gi ϱ' ϱ)
    (2 * Muon.Dynamics.kStar CSig γstar ϱlo) F.β (by linarith) hβ0 hβ1 hc T hT
    (def_app_vol_lag F S 0 t Fo Gi ϱ ϱ')
  rw [hI, abs_sub_comm]
  unfold integratedLag
  exact h

end Muon.Volatility

end

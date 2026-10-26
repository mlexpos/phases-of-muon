import Muon.Setup.Frozen
import Muon.Setup.Basic
import Muon.Volatility.OddSpectral

/-!
# Appendix D, part 2: tested lag covariances and the independent product model

Work package L-D.2 (interface draft). Snapshot `cr-2026-10-23`. Source of record:
`sections/04-volatility/section.tex`: `def:app-vol-lag` (l.397–417, with `eqn:app-vol-Cl`,
`eqn:app-vol-Gamma`, `eqn:app-vol-Cil`) and `def:app-vol-product` (l.618–629, with
`eqn:app-vol-product`). Card: `sections/04-volatility/CARD.md` §2, §3, §5 (row L-D.2).

Reused, not redefined: `Muon.Setup.FrozenParams`, `Muon.Setup.FrozenSamples`, `Muon.Setup.frozenUpd`
(`Muon.Setup.Frozen`); `Muon.Setup.rOut`, `Muon.Setup.rIn`, `Muon.Setup.SpectralData`
(`Muon.Setup.Basic`); `Muon.mean`, `Muon.Q`, `Muon.emaW`, `Muon.outer`, `Muon.Foundations.stdGaussianPi`.

Encoding decisions:
* `C_ℓ[F,G](ϱ,ϱ')` is defined for all test matrices `F`, `G`, as the card's correction R11 requires;
  the paper's "symmetric" restriction is not encoded. The series `Γ` is a `tsum` (junk off its
  summable set; summability is a theorem of L-D.10a, not assumed here).
* The lag covariances are stated at a general time `t : ℤ`. Their independence of `t` is the
  stationarity of `lem:app-setup-ema-law`(ii), a theorem for later, not a hypothesis here.
* Ridges are real numbers. Positivity `ϱ, ϱ' > 0` is a hypothesis of the theorems that use these
  definitions, not of the definitions.
* The independent model lives on the product space `(ℤ × Fin B) → ℝ × (Vec m × Vec n)`, with law
  `Measure.infinitePi` of one slot law `N(0,1) ⊗ N(0,I_m) ⊗ N(0,I_n)`: the scalar `g_{t'a}` and the
  features `(z_{t'a}, w_{t'a})` are independent across slots, and `g` is independent of the features.
* The buffer of the independent model is written directly as the `emaW`-weighted series of its batches.
  It is not `Muon.DetEquiv.WeightedBuf`: that buffer is built on `FrozenSamples`, whose batch
  carries the factor `d = zᵀ A w`, while the independent batch carries a free scalar `g`.
-/

noncomputable section

open scoped Matrix MatrixOrder
open MeasureTheory ProbabilityTheory Filter Topology
open Muon Muon.Setup

namespace Muon.Volatility

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}

/-! ## Centred updates and tested lag covariances -/

/-- Centred update `S^c_t(ϱ) = S_t(ϱ) − 𝔼 S_t(ϱ)` (`eqn:app-vol-Cl`, with `S_t(ϱ) = Q_ϱ(M_t)`
from `eqn:app-vol-U`). -/
def centredUpd (F : FrozenParams m n B) (S : FrozenSamples P m n B) (ϱ : ℝ) (t : ℤ) :
    Ω → Mat m n :=
  fun ω => frozenUpd F S ϱ t ω - mean P (frozenUpd F S ϱ t)

/-- `def:app-vol-lag`, snapshot `cr-2026-10-23`. Declaration of record. The tested lag covariance `C_ℓ[F,G](ϱ,ϱ') = (1/B) 𝔼 Tr[F S^c_t(ϱ) G (S^c_{t+ℓ}(ϱ'))ᵀ]` at time `t`, for all test matrices `F`, `G` (see the module note). The definition, verbatim from `section.tex`:
```latex
\begin{definition}[Tested lag covariances]\label{def:app-vol-lag}
For symmetric deterministic $F\in\R^{\Nout\times\Nout}$ and $G\in\R^{\Nin\times\Nin}$,
ridges $\ridge,\ridge'>0$ and a lag $\ell\ge0$, the tested lag covariance is
\begin{equation}\label{eqn:app-vol-Cl}
C_\ell[F,G](\ridge,\ridge')\defeq\frac1B\,\EE\Tr\big[F\,{\mathsf S}^{\mathrm c}_t(\ridge)\,G\,{\mathsf S}^{\mathrm c}_{t+\ell}(\ridge')^\T\big],
\end{equation}
and, when the series converges absolutely, the integrated covariance is
\begin{equation}\label{eqn:app-vol-Gamma}
\Gamma[F,G](\ridge,\ridge')\defeq C_0[F,G](\ridge,\ridge')
+\sum_{\ell\ge1}\Big(C_\ell[F,G](\ridge,\ridge')+C_\ell[F,G](\ridge',\ridge)\Big).
\end{equation}
The covariance-weighted case is written $C_\ell\defeq C_\ell[\Sigmaout,\Sigmain]$
and $\Gamma\defeq\Gamma[\Sigmaout,\Sigmain]$, so that
$C_\ell(\ridge,\ridge')=B^{-1}\EE\langle {\mathsf S}^{\mathrm c}_t(\ridge),{\mathsf S}^{\mathrm c}_{t+\ell}(\ridge')\rangle_\Sigma$.
When $\Sigmain=\Id$, the row covariances are
\begin{equation}\label{eqn:app-vol-Cil}
C_{i,\ell}(\ridge,\ridge')\defeq B\,C_\ell[u_i\tensor u_i,\Id](\ridge,\ridge')
=\EE\big\langle {\mathsf S}^{\mathrm c}_t(\ridge)^\T u_i,\;{\mathsf S}^{\mathrm c}_{t+\ell}(\ridge')^\T u_i\big\rangle ,
\end{equation}
and $\Gamma_i$ is their integrated sum, defined as in \cref{eqn:app-vol-Gamma}.
\end{definition}
```
-/
def def_app_vol_lag (F : FrozenParams m n B) (S : FrozenSamples P m n B) (ℓ : ℕ) (t : ℤ)
    (Fo : Mat m m) (Gi : Mat n n) (ϱ ϱ' : ℝ) : ℝ :=
  ((B : ℝ))⁻¹ * ∫ ω,
    Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi * (centredUpd F S ϱ' (t + (ℓ : ℤ)) ω)ᵀ) ∂P

/-- Integrated tested covariance `Γ[F,G](ϱ,ϱ') = C_0[F,G](ϱ,ϱ') + ∑_{ℓ≥1} (C_ℓ[F,G](ϱ,ϱ') +
C_ℓ[F,G](ϱ',ϱ))` (`eqn:app-vol-Gamma`). The series is a `tsum`; it is meaningful when the series
converges absolutely, which is a theorem to be proved later. -/
def integratedLag (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
    (Fo : Mat m m) (Gi : Mat n n) (ϱ ϱ' : ℝ) : ℝ :=
  def_app_vol_lag F S 0 t Fo Gi ϱ ϱ' +
    ∑' ℓ : ℕ, (def_app_vol_lag F S (ℓ + 1) t Fo Gi ϱ ϱ' + def_app_vol_lag F S (ℓ + 1) t Fo Gi ϱ' ϱ)

/-- The covariance-weighted lag covariance `C_ℓ := C_ℓ[Σ_out, Σ_in]` (`eqn:app-vol-Cl` and the
sentence after `eqn:app-vol-Gamma`). -/
def weightedLag (F : FrozenParams m n B) (S : FrozenSamples P m n B) (ℓ : ℕ) (t : ℤ)
    (ϱ ϱ' : ℝ) : ℝ :=
  def_app_vol_lag F S ℓ t F.C.Sout F.C.Sin ϱ ϱ'

/-- The covariance-weighted integrated covariance `Γ := Γ[Σ_out, Σ_in]` (`eqn:app-vol-Gamma`). -/
def weightedGamma (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (ϱ ϱ' : ℝ) : ℝ :=
  integratedLag F S t F.C.Sout F.C.Sin ϱ ϱ'

/-- Row covariance `C_{i,ℓ}(ϱ,ϱ') = B · C_ℓ[u_i ⊗ u_i, Id](ϱ,ϱ')` (`eqn:app-vol-Cil`), for the
output eigenvector `u_i = Sp.u i` of `Σ_out`. -/
def rowLag (F : FrozenParams m n B) (S : FrozenSamples P m n B) (Sp : SpectralData F.C)
    (i : Fin m) (ℓ : ℕ) (t : ℤ) (ϱ ϱ' : ℝ) : ℝ :=
  (B : ℝ) * def_app_vol_lag F S ℓ t (outer (Sp.u i) (Sp.u i)) (1 : Mat n n) ϱ ϱ'

/-- Integrated row covariance `Γ_i`, the integrated sum of `C_{i,ℓ}` as in `eqn:app-vol-Gamma`
(`eqn:app-vol-Cil`). -/
def rowGamma (F : FrozenParams m n B) (S : FrozenSamples P m n B) (Sp : SpectralData F.C)
    (i : Fin m) (t : ℤ) (ϱ ϱ' : ℝ) : ℝ :=
  rowLag F S Sp i 0 t ϱ ϱ' +
    ∑' ℓ : ℕ, (rowLag F S Sp i (ℓ + 1) t ϱ ϱ' + rowLag F S Sp i (ℓ + 1) t ϱ' ϱ)

/-! ## The independent product model -/

/-- Law of one slot `(g, z, w)`: `g ∼ N(0,1)`, `z ∼ N(0, I_m)`, `w ∼ N(0, I_n)`, independent. -/
abbrev indepSlotLaw (m n : ℕ) : Measure (ℝ × (Vec m × Vec n)) :=
  (gaussianReal 0 1).prod ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))

/-- Sample space of the independent model: the slots `(g_{s a}, z_{s a}, w_{s a})`, `s ∈ ℤ`,
`a ≤ B`, independent across slots (`Measure.infinitePi`). -/
def indepSpaceLaw (m n B : ℕ) : Measure ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) :=
  Measure.infinitePi fun _ : ℤ × Fin B => indepSlotLaw m n

/-- Independent batch `G^g_{s} = (1/B) ∑_a g_{sa} Σ_out^{1/2} (z_{sa} ⊗ w_{sa}) Σ_in^{1/2}`
(`eqn:app-vol-product`). -/
def indepBatchG (F : FrozenParams m n B) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) (s : ℤ) :
    Mat m n :=
  ((B : ℝ))⁻¹ • ∑ a : Fin B,
    (ω (s, a)).1 • (rOut F.C * outer (ω (s, a)).2.1 (ω (s, a)).2.2 * rIn F.C)

/-- `def:app-vol-product`, snapshot `cr-2026-10-23`. Declaration of record. The independent product model `(G^g, M^g)` on `indepSpaceLaw`; the declaration of record is the buffer `M^g_t` (`def_app_vol_product`), with `indepBatchG` for `G^g` and `indepUpd` for `S^g`. The definition, verbatim from `section.tex`:
```latex
\begin{definition}[Independent product model]\label{def:app-vol-product}
In the frozen-state model with samples indexed by time, let
$(g_{t'a})_{t'\in\mathbb Z,\,a\le B}$ be independent standard Gaussian scalars,
independent of the features, and put
\begin{equation}\label{eqn:app-vol-product}
\begin{gathered}
G^{\mathrm g}_{t'}\defeq\frac1B\sum_{a=1}^Bg_{t'a}\,\Sigmaout^{1/2}(z_{t'a}\tensor w_{t'a})\Sigmain^{1/2},\\
M^{\mathrm g}_{t'}\defeq\sum_{j\ge0}\emaw jG^{\mathrm g}_{t'+1-j},\qquad
{\mathsf S}^{\mathrm g}_{t'}(\ridge)\defeq\Qridge\ridge(M^{\mathrm g}_{t'}).
\end{gathered}
\end{equation}
\end{definition}
```
-/
def def_app_vol_product (F : FrozenParams m n B) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n))
    (t : ℤ) : Mat m n :=
  ∑' j : ℕ, emaW F.β j • indepBatchG F ω (t + 1 - (j : ℤ))

/-- Independent update `S^g_t(ϱ) = Q_ϱ(M^g_t)` (`eqn:app-vol-product`). -/
def indepUpd (F : FrozenParams m n B) (ϱ : ℝ) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) (t : ℤ) :
    Mat m n :=
  Q ϱ (def_app_vol_product F ω t)



/-! ## Size conditions and same-time totals -/

/-- Size conditions in one dimension (`section.tex` l.631–634): `max(N_out, N_in) ≤ γ⋆ B` and
`‖Σ_out‖, ‖Σ_in‖ ≤ C_Σ`. Sizes are read off the covariance type. -/
def SizeFin {m n : ℕ} (C : Covariances m n) (B : ℕ) (γstar CSig : ℝ) : Prop :=
  ((max m n : ℕ) : ℝ) ≤ γstar * (B : ℝ) ∧ opNorm C.Sout ≤ CSig ∧ opNorm C.Sin ≤ CSig

/-- Size conditions along a sequence of dimensions (`section.tex` l.631–634): `SizeFin` at every
index, and `N_in / B → γ_in`, `N_out / B → γ_out`. -/
def SizeSeq {m n B : ℕ → ℕ} (C : ∀ k : ℕ, Covariances (m k) (n k)) (γstar CSig γout γin : ℝ) :
    Prop :=
  (∀ k : ℕ, SizeFin (C k) (B k) γstar CSig) ∧ Tendsto B atTop atTop ∧
    Tendsto (fun k : ℕ => ((n k : ℕ) : ℝ) / ((B k : ℕ) : ℝ)) atTop (𝓝 γin) ∧
    Tendsto (fun k : ℕ => ((m k : ℕ) : ℝ) / ((B k : ℕ) : ℝ)) atTop (𝓝 γout)

/-- Same-time total `Z(ϱ) = (1/B) ‖S_t(ϱ)‖_Σ²` (`eqn:app-vol-Z`), with `‖V‖_Σ² = pairSigma C V V`
(`Muon.Setup.pairSigma`). -/
def sameTimeZ (F : FrozenParams m n B) (S : FrozenSamples P m n B) (ϱ : ℝ) (t : ℤ) (ω : Ω) :
    ℝ :=
  ((B : ℝ))⁻¹ * pairSigma F.C (frozenUpd F S ϱ t ω) (frozenUpd F S ϱ t ω)

/-- Centred same-time total `Z^c(ϱ) = (1/B) ‖S^c_t(ϱ)‖_Σ²` (`eqn:app-vol-Z`). -/
def sameTimeZc (F : FrozenParams m n B) (S : FrozenSamples P m n B) (ϱ : ℝ) (t : ℤ) (ω : Ω) :
    ℝ :=
  ((B : ℝ))⁻¹ * pairSigma F.C (centredUpd F S ϱ t ω) (centredUpd F S ϱ t ω)

/-! ## Statements of the independent model -/

/-! ### Helpers for the almost-sure summability of the independent buffer (private) -/

private lemma indep_coord_abs_integrable (k : ℕ) (i : Fin k) :
    Integrable (fun z : Vec k => |z i|) (Muon.Foundations.stdGaussianPi k) := by
  have hm : MeasurePreserving (fun z : Vec k => z i) (Muon.Foundations.stdGaussianPi k)
      (gaussianReal 0 1) := measurePreserving_eval _ i
  have hx : Integrable (fun x : ℝ => |x|) (gaussianReal 0 1) := by
    simpa using (Muon.Foundations.gaussian_integrable_pow 1).abs
  exact (hm.integrable_comp (g := fun x : ℝ => |x|) (by fun_prop)).2 hx

private lemma indep_slot_abs_integrable (i : Fin m) (k : Fin n) :
    Integrable (fun p : ℝ × (Vec m × Vec n) => |p.1| * (|p.2.1 i| * |p.2.2 k|))
      (indepSlotLaw m n) := by
  have hg : Integrable (fun x : ℝ => |x|) (gaussianReal 0 1) := by
    simpa using (Muon.Foundations.gaussian_integrable_pow 1).abs
  exact hg.mul_prod ((indep_coord_abs_integrable m i).mul_prod (indep_coord_abs_integrable n k))

private lemma indep_psi_integrable :
    Integrable (fun p : ℝ × (Vec m × Vec n) =>
      ∑ x : Fin m, ∑ y : Fin n, |p.1| * (|p.2.1 x| * |p.2.2 y|)) (indepSlotLaw m n) :=
  integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ => indep_slot_abs_integrable x y

private lemma indep_emaW_nonneg {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (j : ℕ) :
    0 ≤ emaW β j := by
  unfold emaW
  exact mul_nonneg (by linarith) (pow_nonneg hβ0 j)

private lemma indep_fro_le_abs_sum (K : Mat m n) : fro K ≤ ∑ i, ∑ k, |K i k| := by
  unfold fro
  refine Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => abs_nonneg _, ?_⟩
  have h : ∀ i k, ‖K i k‖ ^ 2 = |K i k| ^ 2 := fun i k => by rw [Real.norm_eq_abs]
  simp only [h]
  calc ∑ i, ∑ k, |K i k| ^ 2 ≤ ∑ i, (∑ k, |K i k|) ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => abs_nonneg _
    _ ≤ (∑ i, ∑ k, |K i k|) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => Finset.sum_nonneg fun k _ => abs_nonneg _

private lemma indep_outer_entry_le (L : Mat m m) (R : Mat n n) (z : Vec m) (v : Vec n)
    (i : Fin m) (k : Fin n) :
    |(L * Muon.outer z v * R) i k| ≤
      (∑ p, ∑ q, |L i p| * |R q k|) * ∑ x, ∑ y, |z x| * |v y| := by
  have hexp : (L * Muon.outer z v * R) i k = ∑ p, ∑ q, L i p * (z p * v q) * R q k := by
    simp only [Matrix.mul_apply, Muon.outer, Matrix.vecMulVec_apply, Finset.sum_mul]
    refine (Finset.sum_comm).trans ?_
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  have hpair : ∀ p q, |z p| * |v q| ≤ ∑ x, ∑ y, |z x| * |v y| := by
    intro p q
    have h1 : |z p| * |v q| ≤ ∑ y, |z p| * |v y| :=
      Finset.single_le_sum (f := fun y => |z p| * |v y|) (fun y _ => by positivity)
        (Finset.mem_univ q)
    have h2 : ∑ y, |z p| * |v y| ≤ ∑ x, ∑ y, |z x| * |v y| :=
      Finset.single_le_sum (f := fun x => ∑ y, |z x| * |v y|)
        (fun x _ => Finset.sum_nonneg fun y _ => by positivity) (Finset.mem_univ p)
    exact h1.trans h2
  have hterm : ∀ p q, |L i p * (z p * v q) * R q k| ≤
      (|L i p| * |R q k|) * ∑ x, ∑ y, |z x| * |v y| := by
    intro p q
    rw [abs_mul, abs_mul, abs_mul]
    have h0 : 0 ≤ |L i p| * |R q k| := by positivity
    calc |L i p| * (|z p| * |v q|) * |R q k|
        = (|L i p| * |R q k|) * (|z p| * |v q|) := by ring
      _ ≤ (|L i p| * |R q k|) * ∑ x, ∑ y, |z x| * |v y| :=
          mul_le_mul_of_nonneg_left (hpair p q) h0
  rw [hexp]
  calc |∑ p, ∑ q, L i p * (z p * v q) * R q k|
      ≤ ∑ p, |∑ q, L i p * (z p * v q) * R q k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p, ∑ q, |L i p * (z p * v q) * R q k| :=
        Finset.sum_le_sum fun p _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p, ∑ q, (|L i p| * |R q k|) * ∑ x, ∑ y, |z x| * |v y| :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hterm p q
    _ = (∑ p, ∑ q, |L i p| * |R q k|) * ∑ x, ∑ y, |z x| * |v y| := by
        simp only [Finset.sum_mul]

private lemma indep_entry_le (F : FrozenParams m n B) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n))
    (s : ℤ) (i : Fin m) (k : Fin n) :
    |indepBatchG F ω s i k| ≤
      (B : ℝ)⁻¹ * ((∑ p, ∑ q, |rOut F.C i p| * |rIn F.C q k|) *
        ∑ a : Fin B, ∑ x : Fin m, ∑ y : Fin n,
          |(ω (s, a)).1| * (|(ω (s, a)).2.1 x| * |(ω (s, a)).2.2 y|)) := by
  have hG : indepBatchG F ω s i k = (B : ℝ)⁻¹ * ∑ a : Fin B,
      (ω (s, a)).1 * (rOut F.C * Muon.outer (ω (s, a)).2.1 (ω (s, a)).2.2 * rIn F.C) i k := by
    simp only [indepBatchG, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rw [hG, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (B : ℝ)⁻¹)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [abs_mul]
  have hM := indep_outer_entry_le (rOut F.C) (rIn F.C) (ω (s, a)).2.1 (ω (s, a)).2.2 i k
  calc |(ω (s, a)).1| * |(rOut F.C * Muon.outer (ω (s, a)).2.1 (ω (s, a)).2.2 * rIn F.C) i k|
      ≤ |(ω (s, a)).1| * ((∑ p, ∑ q, |rOut F.C i p| * |rIn F.C q k|) *
          ∑ x, ∑ y, |(ω (s, a)).2.1 x| * |(ω (s, a)).2.2 y|) :=
        mul_le_mul_of_nonneg_left hM (abs_nonneg _)
    _ = (∑ p, ∑ q, |rOut F.C i p| * |rIn F.C q k|) *
          ∑ x, ∑ y, |(ω (s, a)).1| * (|(ω (s, a)).2.1 x| * |(ω (s, a)).2.2 y|) := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        ring

private lemma indep_fro_smul_le (F : FrozenParams m n B) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n))
    (s : ℤ) (c : ℝ) (hc : 0 ≤ c) :
    fro (c • indepBatchG F ω s) ≤
      ((∑ i, ∑ k, ∑ p, ∑ q, |rOut F.C i p| * |rIn F.C q k|) * (B : ℝ)⁻¹) *
        ∑ a : Fin B, c * ∑ x : Fin m, ∑ y : Fin n,
          |(ω (s, a)).1| * (|(ω (s, a)).2.1 x| * |(ω (s, a)).2.2 y|) := by
  refine (indep_fro_le_abs_sum _).trans ?_
  have hterm : ∀ i k, |(c • indepBatchG F ω s) i k| ≤
      c * ((B : ℝ)⁻¹ * ((∑ p, ∑ q, |rOut F.C i p| * |rIn F.C q k|) *
        ∑ a : Fin B, ∑ x : Fin m, ∑ y : Fin n,
          |(ω (s, a)).1| * (|(ω (s, a)).2.1 x| * |(ω (s, a)).2.2 y|))) := by
    intro i k
    rw [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (indep_entry_le F ω s i k) hc
  refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hterm i k).trans (le_of_eq ?_)
  calc ∑ i, ∑ k, c * ((B : ℝ)⁻¹ * ((∑ p, ∑ q, |rOut F.C i p| * |rIn F.C q k|) *
        ∑ a : Fin B, ∑ x : Fin m, ∑ y : Fin n,
          |(ω (s, a)).1| * (|(ω (s, a)).2.1 x| * |(ω (s, a)).2.2 y|)))
      = (∑ i, ∑ k, ∑ p, ∑ q, |rOut F.C i p| * |rIn F.C q k|) *
          (c * (B : ℝ)⁻¹ * ∑ a : Fin B, ∑ x : Fin m, ∑ y : Fin n,
            |(ω (s, a)).1| * (|(ω (s, a)).2.1 x| * |(ω (s, a)).2.2 y|)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = ((∑ i, ∑ k, ∑ p, ∑ q, |rOut F.C i p| * |rIn F.C q k|) * (B : ℝ)⁻¹) *
          ∑ a : Fin B, c * ∑ x : Fin m, ∑ y : Fin n,
            |(ω (s, a)).1| * (|(ω (s, a)).2.1 x| * |(ω (s, a)).2.2 y|) := by
        rw [← Finset.mul_sum]
        ring

private lemma indep_summable_time (F : FrozenParams m n B) (t : ℤ) :
    ∀ᵐ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) ∂(indepSpaceLaw m n B),
      Summable fun p : ℕ × Fin B =>
      emaW F.β p.1 * ∑ x : Fin m, ∑ y : Fin n,
        |(ω (t + 1 - (p.1 : ℤ), p.2)).1| *
          (|(ω (t + 1 - (p.1 : ℤ), p.2)).2.1 x| * |(ω (t + 1 - (p.1 : ℤ), p.2)).2.2 y|) := by
  have hβ0 : 0 ≤ F.β := F.hβ.1
  have hβ1 : F.β < 1 := F.hβ.2
  have hΨm : Measurable (fun p : ℝ × (Vec m × Vec n) =>
      ∑ x : Fin m, ∑ y : Fin n, |p.1| * (|p.2.1 x| * |p.2.2 y|)) := by
    apply Continuous.measurable
    fun_prop
  have hKfin : (∫⁻ p, ENNReal.ofReal (∑ x : Fin m, ∑ y : Fin n,
      |p.1| * (|p.2.1 x| * |p.2.2 y|)) ∂(indepSlotLaw m n)) < ⊤ :=
    (indep_psi_integrable (m := m) (n := n)).lintegral_lt_top
  have hlint : ∀ (s : ℤ) (a : Fin B), ∫⁻ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n), ENNReal.ofReal (∑ x : Fin m, ∑ y : Fin n,
      |(ω (s, a)).1| * (|(ω (s, a)).2.1 x| * |(ω (s, a)).2.2 y|)) ∂(indepSpaceLaw m n B)
      = ∫⁻ p, ENNReal.ofReal (∑ x : Fin m, ∑ y : Fin n,
          |p.1| * (|p.2.1 x| * |p.2.2 y|)) ∂(indepSlotLaw m n) := by
    intro s a
    rw [← lintegral_map (hΨm.ennreal_ofReal) (measurable_pi_apply (s, a))]
    unfold indepSpaceLaw
    rw [Measure.infinitePi_map_eval]
  have hbound : ∀ (j : ℕ) (a : Fin B),
      ∫⁻ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n), ENNReal.ofReal (emaW F.β j * ∑ x : Fin m, ∑ y : Fin n,
          |(ω (t + 1 - (j : ℤ), a)).1| *
            (|(ω (t + 1 - (j : ℤ), a)).2.1 x| * |(ω (t + 1 - (j : ℤ), a)).2.2 y|))
        ∂(indepSpaceLaw m n B)
      = ENNReal.ofReal (emaW F.β j) * ∫⁻ p, ENNReal.ofReal (∑ x : Fin m, ∑ y : Fin n,
          |p.1| * (|p.2.1 x| * |p.2.2 y|)) ∂(indepSlotLaw m n) := by
    intro j a
    rw [← hlint (t + 1 - (j : ℤ)) a, ← lintegral_const_mul]
    · refine lintegral_congr fun ω => ?_
      rw [ENNReal.ofReal_mul (indep_emaW_nonneg hβ0 hβ1 j)]
    · exact (hΨm.comp (measurable_pi_apply _)).ennreal_ofReal
  have hmeas : ∀ p : ℕ × Fin B, Measurable fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ENNReal.ofReal (emaW F.β p.1 *
      ∑ x : Fin m, ∑ y : Fin n, |(ω (t + 1 - (p.1 : ℤ), p.2)).1| *
        (|(ω (t + 1 - (p.1 : ℤ), p.2)).2.1 x| * |(ω (t + 1 - (p.1 : ℤ), p.2)).2.2 y|)) :=
    fun p => (((hΨm.comp (measurable_pi_apply _)).const_mul _)).ennreal_ofReal
  have hsum : Summable (fun j : ℕ => emaW F.β j) := by
    unfold emaW
    exact (summable_geometric_of_lt_one hβ0 hβ1).mul_left (1 - F.β)
  have hfin : ∑' p : ℕ × Fin B, ENNReal.ofReal (emaW F.β p.1) ≠ ⊤ := by
    rw [show (∑' p : ℕ × Fin B, ENNReal.ofReal (emaW F.β p.1)) =
        ∑' a : ℕ, ∑' _ : Fin B, ENNReal.ofReal (emaW F.β a) from
          ENNReal.tsum_prod (f := fun a _ => ENNReal.ofReal (emaW F.β a))]
    simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg
      (fun j => indep_emaW_nonneg hβ0 hβ1 j) hsum, tsum_emaW hβ0 hβ1, ENNReal.ofReal_one]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top B) ENNReal.one_ne_top
  have hsum_lint : ∫⁻ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n), ∑' p : ℕ × Fin B, ENNReal.ofReal (emaW F.β p.1 *
      ∑ x : Fin m, ∑ y : Fin n, |(ω (t + 1 - (p.1 : ℤ), p.2)).1| *
        (|(ω (t + 1 - (p.1 : ℤ), p.2)).2.1 x| * |(ω (t + 1 - (p.1 : ℤ), p.2)).2.2 y|))
      ∂(indepSpaceLaw m n B) ≠ ⊤ := by
    rw [lintegral_tsum (fun p => (hmeas p).aemeasurable)]
    refine ne_of_lt ?_
    calc ∑' p : ℕ × Fin B, ∫⁻ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n), ENNReal.ofReal (emaW F.β p.1 *
          ∑ x : Fin m, ∑ y : Fin n, |(ω (t + 1 - (p.1 : ℤ), p.2)).1| *
            (|(ω (t + 1 - (p.1 : ℤ), p.2)).2.1 x| * |(ω (t + 1 - (p.1 : ℤ), p.2)).2.2 y|))
          ∂(indepSpaceLaw m n B)
        = ∑' p : ℕ × Fin B, ENNReal.ofReal (emaW F.β p.1) *
            ∫⁻ q, ENNReal.ofReal (∑ x : Fin m, ∑ y : Fin n,
              |q.1| * (|q.2.1 x| * |q.2.2 y|)) ∂(indepSlotLaw m n) :=
          tsum_congr fun p => hbound p.1 p.2
      _ = (∑' p : ℕ × Fin B, ENNReal.ofReal (emaW F.β p.1)) *
            ∫⁻ q, ENNReal.ofReal (∑ x : Fin m, ∑ y : Fin n,
              |q.1| * (|q.2.1 x| * |q.2.2 y|)) ∂(indepSlotLaw m n) :=
          ENNReal.tsum_mul_right
      _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hfin) hKfin
  have hae := ae_lt_top (Measurable.ennreal_tsum fun p => hmeas p) hsum_lint
  filter_upwards [hae] with ω hω
  refine (ENNReal.summable_toReal hω.ne).congr fun p => ?_
  rw [ENNReal.toReal_ofReal (mul_nonneg (indep_emaW_nonneg hβ0 hβ1 p.1)
    (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => by positivity))]

/-- Almost-sure convergence of the series defining the independent buffer `M^g_t`
(`eqn:app-vol-product`; the series convergence of `def:app-vol-product`'s helper lemmas, l.634–640).
For almost every sample point, at every time `t'`, the Frobenius norms of the terms are summable.
Sorried: proof card P1. -/
theorem def_app_vol_product_summable (F : FrozenParams m n B) :
    ∀ᵐ ω ∂(indepSpaceLaw m n B), ∀ t' : ℤ, Summable fun j : ℕ =>
      fro (emaW F.β j • indepBatchG F ω (t' + 1 - (j : ℤ))) := by
  filter_upwards [ae_all_iff.2 (fun t => indep_summable_time F t)] with ω hω
  intro t'
  have hω' := hω t'
  have hJ : Summable fun j : ℕ => ∑ a : Fin B, emaW F.β j * ∑ x : Fin m, ∑ y : Fin n,
      |(ω (t' + 1 - (j : ℤ), a)).1| *
        (|(ω (t' + 1 - (j : ℤ), a)).2.1 x| * |(ω (t' + 1 - (j : ℤ), a)).2.2 y|) := by
    refine summable_sum fun a _ => ?_
    exact hω'.comp_injective (i := fun j : ℕ => ((j, a) : ℕ × Fin B))
      (fun j1 j2 h => by simpa using h)
  refine Summable.of_nonneg_of_le (fun j => by unfold fro; positivity) (fun j => ?_)
    (hJ.mul_left ((∑ i, ∑ k, ∑ p, ∑ q, |rOut F.C i p| * |rIn F.C q k|) * (B : ℝ)⁻¹))
  exact indep_fro_smul_le F ω (t' + 1 - (j : ℤ)) (emaW F.β j)
    (indep_emaW_nonneg F.hβ.1 F.hβ.2 j)

/-! ### Sign-flip invariance of the independent model (private, for P2) -/

private lemma cfc_odd_neg_aux {k : ℕ} (f : ℝ → ℝ) (hodd : ∀ x : ℝ, f (-x) = -f x)
    (A : Matrix (Fin k) (Fin k) ℝ) : cfc f (-A) = -cfc f A := by
  by_cases hp : IsSelfAdjoint A
  · have hcont : ContinuousOn f ((fun x : ℝ => -x) '' spectrum ℝ A) :=
      ((Matrix.finite_spectrum A).image (fun x : ℝ => -x)).continuousOn f
    have hfn : (fun x : ℝ => f (-x)) = fun x => -(f x) := funext hodd
    rw [← cfc_comp_neg f A hcont hp]
    exact (congrArg (fun g => cfc g A) hfn).trans (cfc_neg f A)
  · have hp' : ¬ IsSelfAdjoint (-A) := fun h => hp (by simpa using h.neg)
    rw [cfc_apply_of_not_predicate A hp, cfc_apply_of_not_predicate (-A) hp', neg_zero]

private lemma oddSharp_neg_aux {m n : ℕ} (f : ℝ → ℝ) (hodd : ∀ x : ℝ, f (-x) = -f x)
    (K : Mat m n) : oddSharp f (-K) = -oddSharp f K := by
  have hB : Matrix.fromBlocks (0 : Mat m m) (-K) (-Kᵀ) (0 : Mat n n) =
      -Matrix.fromBlocks (0 : Mat m m) K Kᵀ 0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp
  have hD : Muon.Foundations.hermDilation (-K) = -Muon.Foundations.hermDilation K := by
    unfold Muon.Foundations.hermDilation
    rw [Matrix.transpose_neg, hB]
    ext i j
    simp [Matrix.reindex_apply]
  unfold oddSharp
  rw [hD, cfc_odd_neg_aux f hodd]
  ext i j
  simp [Muon.Foundations.upperRight]

private lemma indep_flip_measurePreserving {m n B : ℕ} :
    MeasurePreserving (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => fun i => (-(ω i).1, (ω i).2))
      (indepSpaceLaw m n B) (indepSpaceLaw m n B) := by
  have hmeasS : Measurable (fun p : ℝ × (Vec m × Vec n) => (-p.1, p.2)) := by fun_prop
  have hS : MeasurePreserving (fun p : ℝ × (Vec m × Vec n) => (-p.1, p.2))
      (indepSlotLaw m n) (indepSlotLaw m n) := by
    have hg : MeasurePreserving (fun x : ℝ => -x) (gaussianReal 0 1) (gaussianReal 0 1) :=
      ⟨measurable_neg, by rw [gaussianReal_map_neg, neg_zero]⟩
    exact hg.prod (MeasurePreserving.id _)
  have hmap := Measure.infinitePi_map_pi (μ := fun _ : ℤ × Fin B => indepSlotLaw m n)
    (f := fun _ p => (-p.1, p.2)) (fun _ => hmeasS)
  simp only [hS.map_eq] at hmap
  refine ⟨measurable_pi_iff.2 fun i => hmeasS.comp (measurable_pi_apply i), ?_⟩
  unfold indepSpaceLaw
  exact hmap

/-- `def:app-vol-product` (l.634): `𝔼 f^♯(M^g_{t'}) = 0` for every odd bounded `f`, where `f^♯` is
`Muon.Volatility.oddSharp`. Sorried: proof card P2. -/
theorem def_app_vol_product_mean_oddSharp (F : FrozenParams m n B) (f : ℝ → ℝ)
    (hodd : ∀ x : ℝ, f (-x) = -f x) (hbdd : ∃ M : ℝ, ∀ x : ℝ, |f x| ≤ M) (t : ℤ) :
    mean (indepSpaceLaw m n B) (fun ω => oddSharp f (def_app_vol_product F ω t)) = 0 := by
  ext i j
  simp only [mean, Matrix.of_apply, Matrix.zero_apply]
  have hT := indep_flip_measurePreserving (m := m) (n := n) (B := B)
  let e : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) ≃ᵐ ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) :=
    { toFun := fun ω i => (-(ω i).1, (ω i).2)
      invFun := fun ω i => (-(ω i).1, (ω i).2)
      left_inv := fun ω => by funext i; simp
      right_inv := fun ω => by funext i; simp
      measurable_toFun := hT.measurable
      measurable_invFun := hT.measurable }
  have hTe : MeasurePreserving e (indepSpaceLaw m n B) (indepSpaceLaw m n B) := hT
  have hdef : ∀ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n),
      def_app_vol_product F (fun i => (-(ω i).1, (ω i).2)) t = -def_app_vol_product F ω t := by
    intro ω
    have hbatch : ∀ s : ℤ, indepBatchG F (fun i => (-(ω i).1, (ω i).2)) s = -indepBatchG F ω s := by
      intro s
      unfold indepBatchG
      simp [Finset.sum_neg_distrib, neg_smul, smul_neg]
    unfold def_app_vol_product
    simp only [hbatch, smul_neg, tsum_neg]
  have hkey : ∀ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n),
      oddSharp f (def_app_vol_product F (fun i => (-(ω i).1, (ω i).2)) t) i j =
        -(oddSharp f (def_app_vol_product F ω t) i j) := by
    intro ω
    rw [hdef, oddSharp_neg_aux f hodd, Matrix.neg_apply]
  have h1 : ∫ ω, oddSharp f (def_app_vol_product F (fun i => (-(ω i).1, (ω i).2)) t) i j
      ∂(indepSpaceLaw m n B) =
      ∫ ω, oddSharp f (def_app_vol_product F ω t) i j ∂(indepSpaceLaw m n B) :=
    hTe.integral_comp' (fun ω => oddSharp f (def_app_vol_product F ω t) i j)
  have h2 : ∫ ω, oddSharp f (def_app_vol_product F (fun i => (-(ω i).1, (ω i).2)) t) i j
      ∂(indepSpaceLaw m n B) =
      -∫ ω, oddSharp f (def_app_vol_product F ω t) i j ∂(indepSpaceLaw m n B) := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => hkey ω)
  linarith [h1, h2]

/-! ### Second moments of the independent model (private, for P3) -/

private lemma indep3_rOut_symm (C : Covariances m n) : (rOut C)ᵀ = rOut C := by
  have h : (CFC.sqrt C.Sout)ᴴ = CFC.sqrt C.Sout :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sout)).isHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

private lemma indep3_rIn_symm (C : Covariances m n) : (rIn C)ᵀ = rIn C := by
  have h : (CFC.sqrt C.Sin)ᴴ = CFC.sqrt C.Sin :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sin)).isHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

private lemma indep3_rOut_mul (C : Covariances m n) : rOut C * rOut C = C.Sout :=
  CFC.sqrt_mul_sqrt_self C.Sout (Matrix.nonneg_iff_posSemidef.mpr C.psdOut)

private lemma indep3_rIn_mul (C : Covariances m n) : rIn C * rIn C = C.Sin :=
  CFC.sqrt_mul_sqrt_self C.Sin (Matrix.nonneg_iff_posSemidef.mpr C.psdIn)

private lemma indep3_sq_coord_integrable (k : ℕ) (i : Fin k) :
    Integrable (fun z : Vec k => z i ^ 2) (Muon.Foundations.stdGaussianPi k) := by
  have hm : MeasurePreserving (fun z : Vec k => z i) (Muon.Foundations.stdGaussianPi k)
      (gaussianReal 0 1) := measurePreserving_eval _ i
  exact (hm.integrable_comp (g := fun x : ℝ => x ^ 2) (by fun_prop)).2
    (Muon.Foundations.gaussian_integrable_pow 2)

private lemma indep3_coord_mul_integrable (k : ℕ) (i j : Fin k) :
    Integrable (fun z : Vec k => z i * z j) (Muon.Foundations.stdGaussianPi k) := by
  refine ((((indep3_sq_coord_integrable k i).add (indep3_sq_coord_integrable k j)).div_const 2)).mono'
    (Continuous.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall fun z => ?_)
  show ‖z i * z j‖ ≤ (z i ^ 2 + z j ^ 2) / 2
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|z i| - |z j|), sq_abs (z i), sq_abs (z j)]

private lemma indep3_quad_sq (k : ℕ) (L : Matrix (Fin k) (Fin k) ℝ) :
    Integrable (fun z : Vec k => ∑ l, (L.mulVec z) l ^ 2) (Muon.Foundations.stdGaussianPi k) ∧
    ∫ z : Vec k, ∑ l, (L.mulVec z) l ^ 2 ∂(Muon.Foundations.stdGaussianPi k)
      = Matrix.trace (Lᵀ * L) := by
  have e : ∀ z : Vec k, ∑ l, (L.mulVec z) l ^ 2 = ∑ i, ∑ j, (Lᵀ * L) i j * (z i * z j) := by
    intro z
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, sq,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have e2 : ∀ z : Vec k, ∑ i, ∑ j, (Lᵀ * L) i j * (z i * z j)
      = ∑ i, ∑ j, z i * (Lᵀ * L) i j * z j := fun z =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (indep3_coord_mul_integrable k i j).const_mul _, ?_⟩
  simp_rw [e2]
  exact Muon.Foundations.stdGaussianPi_quadratic_mean k (Lᵀ * L)

private lemma indep3_rOut_outer_rIn (F : FrozenParams m n B) (z : Vec m) (w : Vec n) :
    rOut F.C * outer z w * rIn F.C =
      outer (Matrix.mulVec (rOut F.C) z) (Matrix.mulVec (rIn F.C) w) := by
  have hv : Matrix.vecMul w (rIn F.C) = Matrix.mulVec (rIn F.C) w := by
    rw [← Matrix.vecMul_transpose, indep3_rIn_symm]
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hv]

private lemma indep3_slot_sq (F : FrozenParams m n B) :
    Integrable (fun p : ℝ × (Vec m × Vec n) =>
      ∑ i, ∑ k, (p.1 • (rOut F.C * outer p.2.1 p.2.2 * rIn F.C)) i k ^ 2) (indepSlotLaw m n) ∧
    ∫ p : ℝ × (Vec m × Vec n),
      ∑ i, ∑ k, (p.1 • (rOut F.C * outer p.2.1 p.2.2 * rIn F.C)) i k ^ 2 ∂(indepSlotLaw m n)
      = Matrix.trace F.C.Sout * Matrix.trace F.C.Sin := by
  have hpt : ∀ p : ℝ × (Vec m × Vec n),
      ∑ i, ∑ k, (p.1 • (rOut F.C * outer p.2.1 p.2.2 * rIn F.C)) i k ^ 2 =
      p.1 ^ 2 * ((∑ i, ((rOut F.C).mulVec p.2.1) i ^ 2) *
        (∑ k, ((rIn F.C).mulVec p.2.2) k ^ 2)) := by
    intro p
    rw [indep3_rOut_outer_rIn]
    simp only [Matrix.smul_apply, outer, Matrix.vecMulVec_apply, smul_eq_mul]
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hq1 := indep3_quad_sq m (rOut F.C)
  have hq2 := indep3_quad_sq n (rIn F.C)
  have hg2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
    Muon.Foundations.gaussian_integrable_pow 2
  have hprod : Integrable (fun q : Vec m × Vec n =>
      (∑ i, ((rOut F.C).mulVec q.1) i ^ 2) * (∑ k, ((rIn F.C).mulVec q.2) k ^ 2))
      ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) :=
    hq1.1.mul_prod hq2.1
  simp_rw [hpt]
  refine ⟨hg2.mul_prod hprod, ?_⟩
  rw [integral_prod_mul (f := fun x : ℝ => x ^ 2)
    (g := fun q : Vec m × Vec n =>
      (∑ i, ((rOut F.C).mulVec q.1) i ^ 2) * (∑ k, ((rIn F.C).mulVec q.2) k ^ 2)),
    Muon.Foundations.gaussian_moment_two,
    integral_prod_mul (f := fun z : Vec m => ∑ i, ((rOut F.C).mulVec z) i ^ 2)
      (g := fun w : Vec n => ∑ k, ((rIn F.C).mulVec w) k ^ 2), hq1.2, hq2.2,
    indep3_rOut_symm, indep3_rIn_symm, indep3_rOut_mul, indep3_rIn_mul]
  ring

private lemma indep3_flip_slot (p : ℤ × Fin B) :
    MeasurePreserving (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      fun i => if i = p then (-(ω i).1, (ω i).2) else ω i)
      (indepSpaceLaw m n B) (indepSpaceLaw m n B) := by
  classical
  have hmeasS : Measurable (fun x : ℝ × (Vec m × Vec n) => (-x.1, x.2)) := by fun_prop
  have hS : MeasurePreserving (fun x : ℝ × (Vec m × Vec n) => (-x.1, x.2))
      (indepSlotLaw m n) (indepSlotLaw m n) := by
    have hg : MeasurePreserving (fun x : ℝ => -x) (gaussianReal 0 1) (gaussianReal 0 1) :=
      ⟨measurable_neg, by rw [gaussianReal_map_neg, neg_zero]⟩
    exact hg.prod (MeasurePreserving.id _)
  have hmeas : ∀ i : ℤ × Fin B, Measurable (fun x : ℝ × (Vec m × Vec n) =>
      if i = p then (-x.1, x.2) else x) := fun i => by
    by_cases h : i = p
    · simpa [h] using hmeasS
    · simp only [h, if_false]; exact measurable_id
  have hmap := Measure.infinitePi_map_pi (μ := fun _ : ℤ × Fin B => indepSlotLaw m n)
    (f := fun i x => if i = p then (-x.1, x.2) else x) hmeas
  have hmapi : ∀ i : ℤ × Fin B, (indepSlotLaw m n).map (fun x : ℝ × (Vec m × Vec n) =>
      if i = p then (-x.1, x.2) else x) = indepSlotLaw m n := fun i => by
    by_cases h : i = p
    · simpa [h] using hS.map_eq
    · simp [h]
  simp only [hmapi] at hmap
  refine ⟨measurable_pi_iff.2 fun i => (hmeas i).comp (measurable_pi_apply i), ?_⟩
  unfold indepSpaceLaw
  exact hmap

private lemma indep3_cross_zero (F : FrozenParams m n B) {p q : ℤ × Fin B} (hpq : p ≠ q) :
    ∫ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n),
      ∑ i, ∑ k, ((ω p).1 • (rOut F.C * outer (ω p).2.1 (ω p).2.2 * rIn F.C)) i k *
        ((ω q).1 • (rOut F.C * outer (ω q).2.1 (ω q).2.2 * rIn F.C)) i k
      ∂(indepSpaceLaw m n B) = 0 := by
  classical
  have hT := indep3_flip_slot (m := m) (n := n) (B := B) p
  let e : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) ≃ᵐ ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) :=
    { toFun := fun ω i => if i = p then (-(ω i).1, (ω i).2) else ω i
      invFun := fun ω i => if i = p then (-(ω i).1, (ω i).2) else ω i
      left_inv := fun ω => by funext i; by_cases h : i = p <;> simp [h]
      right_inv := fun ω => by funext i; by_cases h : i = p <;> simp [h]
      measurable_toFun := hT.measurable
      measurable_invFun := hT.measurable }
  have hTe : MeasurePreserving e (indepSpaceLaw m n B) (indepSpaceLaw m n B) := hT
  set f : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → ℝ := fun ω =>
      ∑ i, ∑ k, ((ω p).1 • (rOut F.C * outer (ω p).2.1 (ω p).2.2 * rIn F.C)) i k *
        ((ω q).1 • (rOut F.C * outer (ω q).2.1 (ω q).2.2 * rIn F.C)) i k with hf
  have hkey : ∀ ω, f (e ω) = -f ω := by
    intro ω
    have h1 : (e ω) p = (-(ω p).1, (ω p).2) := by simp [e]
    have h2 : (e ω) q = ω q := by simp [e, hpq.symm]
    simp only [hf, h1, h2, neg_smul, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]
  have h1 : ∫ ω, f (e ω) ∂(indepSpaceLaw m n B) = ∫ ω, f ω ∂(indepSpaceLaw m n B) :=
    hTe.integral_comp' f
  have h2 : ∫ ω, f (e ω) ∂(indepSpaceLaw m n B) = -∫ ω, f ω ∂(indepSpaceLaw m n B) := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => hkey ω)
  linarith [h1, h2]

private lemma indep3_entry (F : FrozenParams m n B) (g : ℝ) (z : Vec m) (w : Vec n)
    (i : Fin m) (k : Fin n) :
    (g • (rOut F.C * outer z w * rIn F.C)) i k =
      g * ((Matrix.mulVec (rOut F.C) z) i * (Matrix.mulVec (rIn F.C) w) k) := by
  rw [indep3_rOut_outer_rIn]
  simp [outer, Matrix.vecMulVec_apply]

private lemma indep3_entry_meas (F : FrozenParams m n B) (p : ℤ × Fin B) (i : Fin m) (k : Fin n) :
    Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      ((ω p).1 • (rOut F.C * outer (ω p).2.1 (ω p).2.2 * rIn F.C)) i k) := by
  simp_rw [indep3_entry]
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

private lemma indep3_diag (F : FrozenParams m n B) (p : ℤ × Fin B) :
    Integrable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      ∑ i, ∑ k, ((ω p).1 • (rOut F.C * outer (ω p).2.1 (ω p).2.2 * rIn F.C)) i k ^ 2)
      (indepSpaceLaw m n B) ∧
    ∫ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n),
      ∑ i, ∑ k, ((ω p).1 • (rOut F.C * outer (ω p).2.1 (ω p).2.2 * rIn F.C)) i k ^ 2
      ∂(indepSpaceLaw m n B) = Matrix.trace F.C.Sout * Matrix.trace F.C.Sin := by
  have hm : MeasurePreserving (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω p)
      (indepSpaceLaw m n B) (indepSlotLaw m n) :=
    ⟨measurable_pi_apply p, by unfold indepSpaceLaw; exact Measure.infinitePi_map_eval _ p⟩
  obtain ⟨h1, h2⟩ := indep3_slot_sq F
  refine ⟨hm.integrable_comp_of_integrable h1, ?_⟩
  have h1' := h1.aestronglyMeasurable
  rw [← hm.map_eq] at h1'
  have h3 := integral_map (μ := indepSpaceLaw m n B) hm.measurable.aemeasurable h1'
  rw [hm.map_eq] at h3
  exact h3.symm.trans h2

private lemma indep3_fro_sq (K : Mat m n) : fro K ^ 2 = ∑ i, ∑ k, K i k ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma indep3_finite_moment (F : FrozenParams m n B) {κ : Type*} (S : Finset κ)
    (φ : κ → ℤ × Fin B) (hφ : Function.Injective φ) (c : κ → ℝ)
    (Y : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → κ → Mat m n)
    (hY : ∀ ω x, Y ω x = (ω (φ x)).1 •
      (rOut F.C * outer (ω (φ x)).2.1 (ω (φ x)).2.2 * rIn F.C)) :
    Integrable (fun ω => fro (∑ x ∈ S, c x • Y ω x) ^ 2) (indepSpaceLaw m n B) ∧
    ∫ ω, fro (∑ x ∈ S, c x • Y ω x) ^ 2 ∂(indepSpaceLaw m n B) =
      (∑ x ∈ S, c x ^ 2) * (Matrix.trace F.C.Sout * Matrix.trace F.C.Sin) := by
  classical
  set μ := indepSpaceLaw m n B with hμ
  have hYe : ∀ x i k, Measurable (fun ω => Y ω x i k) := fun x i k => by
    simp_rw [hY]; exact indep3_entry_meas F (φ x) i k
  have hD : ∀ x, Integrable (fun ω => ∑ i, ∑ k, (Y ω x i k) ^ 2) μ ∧
      ∫ ω, ∑ i, ∑ k, (Y ω x i k) ^ 2 ∂μ = Matrix.trace F.C.Sout * Matrix.trace F.C.Sin := by
    intro x
    simp_rw [hY]
    exact indep3_diag F (φ x)
  have hI : ∀ x y, Integrable (fun ω => ∑ i, ∑ k, Y ω x i k * Y ω y i k) μ := by
    intro x y
    refine (((hD x).1.add (hD y).1).div_const 2).mono'
      (Measurable.aestronglyMeasurable
        (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ =>
          (hYe x i k).mul (hYe y i k)))
      (Filter.Eventually.of_forall fun ω => ?_)
    show ‖∑ i, ∑ k, Y ω x i k * Y ω y i k‖ ≤
      ((∑ i, ∑ k, (Y ω x i k) ^ 2) + (∑ i, ∑ k, (Y ω y i k) ^ 2)) / 2
    rw [← Finset.sum_add_distrib, Finset.sum_div, Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (Y ω x i k - Y ω y i k), sq_nonneg (Y ω x i k + Y ω y i k)]
  have hexp : ∀ ω, fro (∑ x ∈ S, c x • Y ω x) ^ 2 =
      ∑ x ∈ S, ∑ y ∈ S, c x * c y * ∑ i, ∑ k, Y ω x i k * Y ω y i k := by
    intro ω
    have hik : ∀ i k, (∑ x ∈ S, c x * Y ω x i k) ^ 2 =
        ∑ x ∈ S, ∑ y ∈ S, c x * c y * (Y ω x i k * Y ω y i k) := by
      intro i k
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [indep3_fro_sq]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    simp_rw [hik]
    calc _ = ∑ i, ∑ x ∈ S, ∑ k, ∑ y ∈ S, c x * c y * (Y ω x i k * Y ω y i k) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact Finset.sum_comm
      _ = ∑ i, ∑ x ∈ S, ∑ y ∈ S, ∑ k, c x * c y * (Y ω x i k * Y ω y i k) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
          exact Finset.sum_comm
      _ = ∑ x ∈ S, ∑ i, ∑ y ∈ S, ∑ k, c x * c y * (Y ω x i k * Y ω y i k) := Finset.sum_comm
      _ = ∑ x ∈ S, ∑ y ∈ S, ∑ i, ∑ k, c x * c y * (Y ω x i k * Y ω y i k) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          exact Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
  have hint : ∀ x y, Integrable (fun ω => c x * c y * ∑ i, ∑ k, Y ω x i k * Y ω y i k) μ :=
    fun x y => (hI x y).const_mul _
  have hval : ∀ x y, ∫ ω, ∑ i, ∑ k, Y ω x i k * Y ω y i k ∂μ =
      if x = y then Matrix.trace F.C.Sout * Matrix.trace F.C.Sin else 0 := by
    intro x y
    by_cases h : x = y
    · subst h
      simp only [if_true]
      rw [← (hD x).2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only [sq]
    · simp only [h, if_false]
      have := indep3_cross_zero F (m := m) (n := n) (B := B)
        (p := φ x) (q := φ y) (fun hh => h (hφ hh))
      simp_rw [hY]
      exact this
  simp_rw [hexp]
  refine ⟨integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ => hint x y, ?_⟩
  rw [integral_finset_sum _ fun x _ => integrable_finsetSum _ fun y _ => hint x y]
  have : ∀ x ∈ S, ∫ ω, ∑ y ∈ S, c x * c y * ∑ i, ∑ k, Y ω x i k * Y ω y i k ∂μ =
      c x ^ 2 * (Matrix.trace F.C.Sout * Matrix.trace F.C.Sin) := by
    intro x hx
    rw [integral_finset_sum _ fun y _ => hint x y]
    simp_rw [integral_const_mul, hval]
    simp [mul_ite, Finset.sum_ite_eq, hx, sq]
  rw [Finset.sum_congr rfl this, Finset.sum_mul]

private lemma indep3_partial_moment (F : FrozenParams m n B) (t : ℤ) (J : Finset ℕ) :
    Integrable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      fro (∑ j ∈ J, emaW F.β j • indepBatchG F ω (t + 1 - (j : ℤ))) ^ 2) (indepSpaceLaw m n B) ∧
    ∫ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n),
      fro (∑ j ∈ J, emaW F.β j • indepBatchG F ω (t + 1 - (j : ℤ))) ^ 2 ∂(indepSpaceLaw m n B) =
      (∑ j ∈ J, emaW F.β j ^ 2) * (B : ℝ)⁻¹ *
        (Matrix.trace F.C.Sout * Matrix.trace F.C.Sin) := by
  classical
  have hφ : Function.Injective (fun x : ℕ × Fin B => ((t + 1 - (x.1 : ℤ), x.2) : ℤ × Fin B)) := by
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (by exact_mod_cast (by linarith [h.1] : (x.1 : ℤ) = y.1)) h.2
  have hfun : ∀ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n),
      ∑ j ∈ J, emaW F.β j • indepBatchG F ω (t + 1 - (j : ℤ)) =
      ∑ x ∈ J ×ˢ (Finset.univ : Finset (Fin B)), (emaW F.β x.1 / (B : ℝ)) •
        ((ω (t + 1 - (x.1 : ℤ), x.2)).1 •
          (rOut F.C * outer (ω (t + 1 - (x.1 : ℤ), x.2)).2.1 (ω (t + 1 - (x.1 : ℤ), x.2)).2.2
            * rIn F.C)) := by
    intro ω
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold indepBatchG
    rw [Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_smul, div_eq_mul_inv]
  have hmain := indep3_finite_moment F (J ×ˢ (Finset.univ : Finset (Fin B)))
    (fun x : ℕ × Fin B => ((t + 1 - (x.1 : ℤ), x.2) : ℤ × Fin B)) hφ
    (fun x : ℕ × Fin B => emaW F.β x.1 / (B : ℝ))
    (fun ω x => (ω (t + 1 - (x.1 : ℤ), x.2)).1 •
          (rOut F.C * outer (ω (t + 1 - (x.1 : ℤ), x.2)).2.1 (ω (t + 1 - (x.1 : ℤ), x.2)).2.2
            * rIn F.C)) (fun ω x => rfl)
  simp_rw [hfun]
  refine ⟨hmain.1, hmain.2.trans ?_⟩
  congr 1
  rw [Finset.sum_product, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  by_cases hB : (B : ℝ) = 0
  · simp [hB]
  · field_simp

private lemma indep3_fro_continuous : Continuous (fun K : Mat m n => fro K) := by
  unfold fro
  fun_prop

open scoped Matrix.Norms.Frobenius in
private lemma indep3_partial_tendsto (F : FrozenParams m n B) (t : ℤ) :
    ∀ᵐ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) ∂(indepSpaceLaw m n B),
      Filter.Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N,
        emaW F.β j • indepBatchG F ω (t + 1 - (j : ℤ))) Filter.atTop
        (𝓝 (def_app_vol_product F ω t)) := by
  filter_upwards [def_app_vol_product_summable F] with ω hω
  have hs : Summable fun j : ℕ => emaW F.β j • indepBatchG F ω (t + 1 - (j : ℤ)) := by
    refine Summable.of_norm ?_
    simpa [fro_eq_norm] using hω t
  exact hs.hasSum.tendsto_sum_nat

private lemma indep3_fatou {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'}
    (f : ℕ → Ω' → ENNReal) (g : Ω' → ENNReal) (hf : ∀ n, AEMeasurable (f n) μ)
    (hlim : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => f n ω) Filter.atTop (𝓝 (g ω))) :
    ∫⁻ ω, g ω ∂μ ≤ Filter.liminf (fun n => ∫⁻ ω, f n ω ∂μ) Filter.atTop := by
  calc ∫⁻ ω, g ω ∂μ = ∫⁻ ω, Filter.liminf (fun n => f n ω) Filter.atTop ∂μ :=
        lintegral_congr_ae (hlim.mono fun ω h => h.liminf_eq.symm)
    _ ≤ _ := lintegral_liminf_le' hf

open scoped Matrix.Norms.Frobenius in
private lemma indep3_fro_tri (K L : Mat m n) : fro K ≤ fro L + fro (L - K) := by
  rw [fro_eq_norm, fro_eq_norm, fro_eq_norm]
  calc ‖K‖ = ‖L - (L - K)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖L‖ + ‖L - K‖ := norm_sub_le _ _

private lemma indep3_sq_le (a b c δ : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (ha : 0 ≤ a) (hδ : 0 < δ)
    (h : a ≤ b + c) : a ^ 2 ≤ (1 + δ) * b ^ 2 + (1 + 1 / δ) * c ^ 2 := by
  have h1 : a ^ 2 ≤ (b + c) ^ 2 := by nlinarith
  have h2 : 2 * b * c ≤ δ * b ^ 2 + (1 / δ) * c ^ 2 := by
    have : 0 ≤ (Real.sqrt δ * b - c / Real.sqrt δ) ^ 2 := sq_nonneg _
    have hs : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ.le
    have hpos : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
    have e : (Real.sqrt δ * b - c / Real.sqrt δ) ^ 2 =
        δ * b ^ 2 + (1 / δ) * c ^ 2 - 2 * b * c := by
      field_simp
      rw [hs]
      ring
    linarith
  nlinarith

private lemma indep3_L2_upper {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'}
    (P : ℕ → Ω' → Mat m n) (M : Ω' → Mat m n) (s : ℕ → ℝ) (S K : ℝ)
    (hconv : ∀ᵐ ω ∂μ, Filter.Tendsto (fun N => P N ω) Filter.atTop (𝓝 (M ω)))
    (hs : Filter.Tendsto s Filter.atTop (𝓝 S))
    (hint : ∀ N, Integrable (fun ω => fro (P N ω) ^ 2) μ)
    (hmom : ∀ N, ∫ ω, fro (P N ω) ^ 2 ∂μ = s N * K) :
    AEMeasurable (fun ω => fro (M ω) ^ 2) μ ∧
    ∫⁻ ω, ENNReal.ofReal (fro (M ω) ^ 2) ∂μ ≤ ENNReal.ofReal (S * K) := by
  have hMlim : ∀ᵐ ω ∂μ, Filter.Tendsto (fun N => fro (P N ω) ^ 2) Filter.atTop
      (𝓝 (fro (M ω) ^ 2)) :=
    hconv.mono fun ω h => ((indep3_fro_continuous.tendsto _).comp h).pow 2
  refine ⟨aemeasurable_of_tendsto_metrizable_ae Filter.atTop
    (fun N => (hint N).aemeasurable) hMlim, ?_⟩
  have h1 := indep3_fatou (μ := μ) (fun N ω => ENNReal.ofReal (fro (P N ω) ^ 2))
    (fun ω => ENNReal.ofReal (fro (M ω) ^ 2))
    (fun N => (hint N).aemeasurable.ennreal_ofReal)
    (hMlim.mono fun ω h => ENNReal.tendsto_ofReal h)
  have h2 : ∀ N, ∫⁻ ω, ENNReal.ofReal (fro (P N ω) ^ 2) ∂μ = ENNReal.ofReal (s N * K) := by
    intro N
    rw [← hmom N, ofReal_integral_eq_lintegral_ofReal (hint N)
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
  simp_rw [h2] at h1
  have h3 : Filter.Tendsto (fun N => ENNReal.ofReal (s N * K)) Filter.atTop
      (𝓝 (ENNReal.ofReal (S * K))) :=
    ENNReal.tendsto_ofReal (hs.mul_const K)
  rwa [h3.liminf_eq] at h1

private lemma indep3_L2_tail {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'}
    (P : ℕ → Ω' → Mat m n) (M : Ω' → Mat m n) (s : ℕ → ℝ) (S K : ℝ)
    (hconv : ∀ᵐ ω ∂μ, Filter.Tendsto (fun N => P N ω) Filter.atTop (𝓝 (M ω)))
    (hs : Filter.Tendsto s Filter.atTop (𝓝 S))
    (hdint : ∀ N k : ℕ, Integrable (fun ω => fro (P (N + k) ω - P N ω) ^ 2) μ)
    (hdmom : ∀ N k : ℕ, ∫ ω, fro (P (N + k) ω - P N ω) ^ 2 ∂μ = (s (N + k) - s N) * K)
    (N : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (fro (M ω - P N ω) ^ 2) ∂μ ≤ ENNReal.ofReal ((S - s N) * K) := by
  have hlim : ∀ᵐ ω ∂μ, Filter.Tendsto (fun k : ℕ => ENNReal.ofReal (fro (P (N + k) ω - P N ω) ^ 2))
      Filter.atTop (𝓝 (ENNReal.ofReal (fro (M ω - P N ω) ^ 2))) := by
    filter_upwards [hconv] with ω h
    have hN : Filter.Tendsto (fun k : ℕ => N + k) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun k => Nat.le_add_left k N) Filter.tendsto_id
    have h' := (h.comp hN).sub_const (P N ω)
    exact ENNReal.tendsto_ofReal (((indep3_fro_continuous.tendsto _).comp h').pow 2)
  have h1 := indep3_fatou (μ := μ)
    (fun k ω => ENNReal.ofReal (fro (P (N + k) ω - P N ω) ^ 2))
    (fun ω => ENNReal.ofReal (fro (M ω - P N ω) ^ 2))
    (fun k => (hdint N k).aemeasurable.ennreal_ofReal) hlim
  have h2 : ∀ k, ∫⁻ ω, ENNReal.ofReal (fro (P (N + k) ω - P N ω) ^ 2) ∂μ
      = ENNReal.ofReal ((s (N + k) - s N) * K) := by
    intro k
    rw [← hdmom N k, ofReal_integral_eq_lintegral_ofReal (hdint N k)
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
  simp_rw [h2] at h1
  have h3 : Filter.Tendsto (fun k : ℕ => ENNReal.ofReal ((s (N + k) - s N) * K)) Filter.atTop
      (𝓝 (ENNReal.ofReal ((S - s N) * K))) := by
    have hN : Filter.Tendsto (fun k : ℕ => N + k) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun k => Nat.le_add_left k N) Filter.tendsto_id
    have h4 : Filter.Tendsto (fun k : ℕ => s (N + k)) Filter.atTop (𝓝 S) := hs.comp hN
    exact ENNReal.tendsto_ofReal ((h4.sub_const (s N)).mul_const K)
  rwa [h3.liminf_eq] at h1

private lemma indep3_L2_final {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'}
    (P : ℕ → Ω' → Mat m n) (M : Ω' → Mat m n) (s : ℕ → ℝ) (S K : ℝ)
    (hconv : ∀ᵐ ω ∂μ, Filter.Tendsto (fun N => P N ω) Filter.atTop (𝓝 (M ω)))
    (hs : Filter.Tendsto s Filter.atTop (𝓝 S)) (hs0 : ∀ N, 0 ≤ s N) (hsS : ∀ N, s N ≤ S)
    (hK0 : 0 ≤ K)
    (hint : ∀ N, Integrable (fun ω => fro (P N ω) ^ 2) μ)
    (hmom : ∀ N, ∫ ω, fro (P N ω) ^ 2 ∂μ = s N * K)
    (hdint : ∀ N k : ℕ, Integrable (fun ω => fro (P (N + k) ω - P N ω) ^ 2) μ)
    (hdmom : ∀ N k : ℕ, ∫ ω, fro (P (N + k) ω - P N ω) ^ 2 ∂μ = (s (N + k) - s N) * K) :
    ∫ ω, fro (M ω) ^ 2 ∂μ = S * K := by
  obtain ⟨hMae, hU⟩ := indep3_L2_upper P M s S K hconv hs hint hmom
  have hT := indep3_L2_tail P M s S K hconv hs hdint hdmom
  have hS0 : 0 ≤ S := (hs0 0).trans (hsS 0)
  have hLfin : ∫⁻ ω, ENNReal.ofReal (fro (M ω) ^ 2) ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hU
  set ℓ : ℝ := (∫⁻ ω, ENNReal.ofReal (fro (M ω) ^ 2) ∂μ).toReal with hℓ
  have hLℓ : ∫⁻ ω, ENNReal.ofReal (fro (M ω) ^ 2) ∂μ = ENNReal.ofReal ℓ :=
    (ENNReal.ofReal_toReal hLfin).symm
  have hℓ0 : 0 ≤ ℓ := ENNReal.toReal_nonneg
  have hℓU : ℓ ≤ S * K := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hU
    rwa [ENNReal.toReal_ofReal (mul_nonneg hS0 hK0)] at this
  have hLow : ∀ δ : ℝ, 0 < δ → ∀ N : ℕ,
      s N * K ≤ (1 + δ) * ℓ + (1 + 1 / δ) * ((S - s N) * K) := by
    intro δ hδ N
    have hpt : ∀ ω, ENNReal.ofReal (fro (P N ω) ^ 2) ≤
        ENNReal.ofReal (1 + δ) * ENNReal.ofReal (fro (M ω) ^ 2) +
        ENNReal.ofReal (1 + 1 / δ) * ENNReal.ofReal (fro (M ω - P N ω) ^ 2) := by
      intro ω
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      exact indep3_sq_le _ _ _ δ (by unfold fro; positivity) (by unfold fro; positivity)
        (by unfold fro; positivity) hδ (indep3_fro_tri _ _)
    have hA : AEMeasurable (fun ω => ENNReal.ofReal (1 + δ) * ENNReal.ofReal (fro (M ω) ^ 2)) μ :=
      hMae.ennreal_ofReal.const_mul _
    have hchain : ∫⁻ ω, ENNReal.ofReal (fro (P N ω) ^ 2) ∂μ ≤
        ENNReal.ofReal (1 + δ) * ENNReal.ofReal ℓ +
        ENNReal.ofReal (1 + 1 / δ) * ENNReal.ofReal ((S - s N) * K) := by
      calc ∫⁻ ω, ENNReal.ofReal (fro (P N ω) ^ 2) ∂μ
          ≤ ∫⁻ ω, (ENNReal.ofReal (1 + δ) * ENNReal.ofReal (fro (M ω) ^ 2) +
            ENNReal.ofReal (1 + 1 / δ) * ENNReal.ofReal (fro (M ω - P N ω) ^ 2)) ∂μ :=
            lintegral_mono hpt
        _ = ENNReal.ofReal (1 + δ) * ∫⁻ ω, ENNReal.ofReal (fro (M ω) ^ 2) ∂μ +
            ENNReal.ofReal (1 + 1 / δ) *
              ∫⁻ ω, ENNReal.ofReal (fro (M ω - P N ω) ^ 2) ∂μ := by
            rw [lintegral_add_left' hA, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ _ := by
            rw [hLℓ]
            gcongr
            exact hT N
    have hI : ∫⁻ ω, ENNReal.ofReal (fro (P N ω) ^ 2) ∂μ = ENNReal.ofReal (s N * K) := by
      rw [← hmom N, ofReal_integral_eq_lintegral_ofReal (hint N)
        (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
    rw [hI] at hchain
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity)
        (mul_nonneg (by positivity) (mul_nonneg (sub_nonneg.2 (hsS N)) hK0))] at hchain
    exact (ENNReal.ofReal_le_ofReal_iff (by
      have := mul_nonneg (by positivity : (0 : ℝ) ≤ 1 + 1 / δ) (mul_nonneg (sub_nonneg.2 (hsS N)) hK0)
      positivity)).1 hchain
  have hSK : S * K ≤ ℓ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set δ : ℝ := ε / (ℓ + 1) with hδ
    have hδ0 : 0 < δ := by positivity
    have hlim : S * K ≤ (1 + δ) * ℓ + (1 + 1 / δ) * ((S - S) * K) := by
      refine le_of_tendsto_of_tendsto' (hs.mul_const K)
        ((((tendsto_const_nhds (x := S)).sub hs).mul_const K).const_mul (1 + 1 / δ) |>.const_add
          ((1 + δ) * ℓ)) (hLow δ hδ0)
    simp only [sub_self, zero_mul, mul_zero, add_zero] at hlim
    have : δ * ℓ ≤ ε := by
      rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hEq : ℓ = S * K := le_antisymm hℓU hSK
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => sq_nonneg _)
    hMae.aestronglyMeasurable, hLℓ, ENNReal.toReal_ofReal hℓ0, hEq]

private lemma indep3_limit_moment (F : FrozenParams m n B) (t : ℤ) :
    ∫ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n), fro (def_app_vol_product F ω t) ^ 2
      ∂(indepSpaceLaw m n B) =
      sPow F.β 2 * (B : ℝ)⁻¹ * (Matrix.trace F.C.Sout * Matrix.trace F.C.Sin) := by
  classical
  have hw2 : HasSum (fun j : ℕ => emaW F.β j ^ 2) (sPow F.β 2) := by
    have hsum : Summable (fun j : ℕ => emaW F.β j ^ 2) := by
      have : (fun j : ℕ => emaW F.β j ^ 2) = fun j : ℕ => (1 - F.β) ^ 2 * (F.β ^ 2) ^ j := by
        funext j
        unfold emaW
        rw [mul_pow, pow_right_comm F.β j 2]
      rw [this]
      exact (summable_geometric_of_lt_one (by have := F.hβ.1; positivity)
        (by have := F.hβ.1; have := F.hβ.2; nlinarith)).mul_left _
    exact hsum.hasSum
  have hκ : 0 ≤ Matrix.trace F.C.Sout * Matrix.trace F.C.Sin :=
    mul_nonneg F.C.psdOut.trace_nonneg F.C.psdIn.trace_nonneg
  have hK0 : 0 ≤ (B : ℝ)⁻¹ * (Matrix.trace F.C.Sout * Matrix.trace F.C.Sin) :=
    mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg B)) hκ
  have hPm := fun J => indep3_partial_moment F t J
  have key := indep3_L2_final (μ := indepSpaceLaw m n B)
    (fun (N : ℕ) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) =>
      ∑ j ∈ Finset.range N, emaW F.β j • indepBatchG F ω (t + 1 - (j : ℤ)))
    (fun ω => def_app_vol_product F ω t)
    (fun N => ∑ j ∈ Finset.range N, emaW F.β j ^ 2) (sPow F.β 2)
    ((B : ℝ)⁻¹ * (Matrix.trace F.C.Sout * Matrix.trace F.C.Sin))
    (indep3_partial_tendsto F t) hw2.tendsto_sum_nat
    (fun N => Finset.sum_nonneg fun j _ => sq_nonneg _)
    (fun N => sum_le_hasSum (Finset.range N) (fun j _ => sq_nonneg _) hw2) hK0
    (fun N => (hPm (Finset.range N)).1)
    (fun N => by rw [(hPm (Finset.range N)).2]; ring)
    (fun N k => by
      have hdiff : ∀ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n),
          ∑ j ∈ Finset.range (N + k), emaW F.β j • indepBatchG F ω (t + 1 - (j : ℤ)) -
          ∑ j ∈ Finset.range N, emaW F.β j • indepBatchG F ω (t + 1 - (j : ℤ)) =
          ∑ j ∈ Finset.Ico N (N + k), emaW F.β j • indepBatchG F ω (t + 1 - (j : ℤ)) := by
        intro ω
        rw [Finset.sum_Ico_eq_sub _ (Nat.le_add_right N k)]
      simp_rw [hdiff]
      exact (hPm _).1)
    (fun N k => by
      have hdiff : ∀ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n),
          ∑ j ∈ Finset.range (N + k), emaW F.β j • indepBatchG F ω (t + 1 - (j : ℤ)) -
          ∑ j ∈ Finset.range N, emaW F.β j • indepBatchG F ω (t + 1 - (j : ℤ)) =
          ∑ j ∈ Finset.Ico N (N + k), emaW F.β j • indepBatchG F ω (t + 1 - (j : ℤ)) := by
        intro ω
        rw [Finset.sum_Ico_eq_sub _ (Nat.le_add_right N k)]
      simp_rw [hdiff]
      rw [(hPm _).2, Finset.sum_Ico_eq_sub _ (Nat.le_add_right N k)]
      ring)
  rw [key]
  ring

open scoped Matrix.Norms.L2Operator in
private lemma indep3_abs_entry_le_opNorm {p q : ℕ} (K : Mat p q) (i : Fin p) (j : Fin q) :
    |K i j| ≤ opNorm K := by
  have h1 := Matrix.l2_opNorm_mulVec K (EuclideanSpace.single j (1 : ℝ))
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin p) ℝ).symm
    (K *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ)))) i
  have h3 : ((EuclideanSpace.equiv (Fin p) ℝ).symm
      (K *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ)))) i = K i j := by
    simp [Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]
  simp only [EuclideanSpace.norm_single, norm_one, mul_one] at h1
  rw [h3, Real.norm_eq_abs] at h2
  rw [opNorm_eq_norm]
  linarith

private lemma indep3_trace_le {k : ℕ} (A : Mat k k) (hA : A.PosSemidef) (c : ℝ)
    (hc : opNorm A ≤ c) : Matrix.trace A ≤ (k : ℝ) * c := by
  unfold Matrix.trace
  calc ∑ i, A.diag i = ∑ i : Fin k, A i i := rfl
    _ ≤ ∑ _i : Fin k, c := Finset.sum_le_sum fun i _ =>
        (le_abs_self _).trans ((indep3_abs_entry_le_opNorm A i i).trans hc)
    _ = (k : ℝ) * c := by simp


/-- `eqn:app-vol-product-moments`, identity: `(1/B) 𝔼‖M^g_{t'}‖_F² = (S_2 / B²) Tr Σ_out Tr Σ_in`,
with `S_2 = sPow β 2` (`Muon.Setup.sPow`). Sorried: proof card P3. -/
theorem def_app_vol_product_moment (F : FrozenParams m n B) (t : ℤ) :
    ((B : ℝ))⁻¹ * ∫ ω, fro (def_app_vol_product F ω t) ^ 2 ∂(indepSpaceLaw m n B) =
      sPow F.β 2 / ((B : ℝ) ^ 2) * Matrix.trace F.C.Sout * Matrix.trace F.C.Sin := by
  rw [indep3_limit_moment]
  have hB : (B : ℝ) ≠ 0 := by exact_mod_cast F.hB.ne'
  field_simp

/-- `eqn:app-vol-product-moments`, bound: under the size conditions `SizeFin`,
`(1/B) 𝔼‖M^g_{t'}‖_F² ≤ C_Σ² γ⋆²`. Sorried: proof card P3. -/
theorem def_app_vol_product_moment_le (F : FrozenParams m n B) (γstar CSig : ℝ)
    (hS : SizeFin F.C B γstar CSig) (t : ℤ) :
    ((B : ℝ))⁻¹ * ∫ ω, fro (def_app_vol_product F ω t) ^ 2 ∂(indepSpaceLaw m n B) ≤
      CSig ^ 2 * γstar ^ 2 := by
  rw [def_app_vol_product_moment]
  obtain ⟨hsz, hout, hin⟩ := hS
  have hB : (0 : ℝ) < B := by exact_mod_cast F.hB
  have hβ0 := F.hβ.1
  have hβ1 := F.hβ.2
  have hS2 : sPow F.β 2 ≤ 1 := by
    rw [sPow_two hβ0 hβ1, div_le_one (by linarith)]
    linarith
  have hS2n : 0 ≤ sPow F.β 2 := by
    rw [sPow_two hβ0 hβ1]
    exact div_nonneg (by linarith) (by linarith)
  have hmax1 : (m : ℝ) ≤ γstar * B := le_trans (by exact_mod_cast le_max_left m n) hsz
  have hmax2 : (n : ℝ) ≤ γstar * B := le_trans (by exact_mod_cast le_max_right m n) hsz
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hC0 : 0 ≤ CSig := le_trans (by unfold opNorm; exact norm_nonneg _) hout
  have hT1 := indep3_trace_le F.C.Sout F.C.psdOut CSig hout
  have hT2 := indep3_trace_le F.C.Sin F.C.psdIn CSig hin
  have hT10 : 0 ≤ Matrix.trace F.C.Sout := F.C.psdOut.trace_nonneg
  have hT20 : 0 ≤ Matrix.trace F.C.Sin := F.C.psdIn.trace_nonneg
  have hprod : Matrix.trace F.C.Sout * Matrix.trace F.C.Sin ≤ ((m : ℝ) * CSig) * ((n : ℝ) * CSig) :=
    mul_le_mul hT1 hT2 hT20 (mul_nonneg hm0 hC0)
  have hmn : (m : ℝ) * n ≤ (γstar * B) ^ 2 := by
    rw [sq]
    exact mul_le_mul hmax1 hmax2 hn0 (hm0.trans hmax1)
  have hB2 : (0 : ℝ) < (B : ℝ) ^ 2 := by positivity
  rw [mul_assoc, div_mul_eq_mul_div, div_le_iff₀ hB2]
  calc sPow F.β 2 * (Matrix.trace F.C.Sout * Matrix.trace F.C.Sin)
      ≤ 1 * (((m : ℝ) * CSig) * ((n : ℝ) * CSig)) :=
        mul_le_mul hS2 hprod (mul_nonneg hT10 hT20) zero_le_one
    _ = CSig ^ 2 * ((m : ℝ) * n) := by ring
    _ ≤ CSig ^ 2 * (γstar * B) ^ 2 :=
        mul_le_mul_of_nonneg_left hmn (sq_nonneg _)
    _ = CSig ^ 2 * γstar ^ 2 * (B : ℝ) ^ 2 := by ring


end Muon.Volatility

end

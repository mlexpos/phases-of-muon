import Muon.Volatility.Closed.Profile
import Muon.Volatility.Closed.Trees
import Muon.Volatility.LagKernel

/-!
# Appendix D, work package L-D.17: one-buffer sums and the path decomposition

Work package L-D.17 (interface draft). Snapshot `cr-2026-10-23`. Source of record:
`sections/04-volatility/section.tex`: the assignment, value and corner-weight
paragraphs (l.2180–2228),
`lem:app-vol-closed-onebuffer` (l.2234–2248), the path paragraph and `lem:app-vol-closed-path`
(l.2359–2368). Card: `sections/04-volatility/CARD.md` §2 (assignments, `val`, one-buffer sums, path
data), §3 (the two rows of this package), §5 (row L-D.17), §6 (R22).

Reused, not redefined: `treeK`, `TypedTrees`, `TypedOrdTree`, `VType`, `CyclicAlt` (`TreeDef`,
`Closed.Trees`); `PlaneTree`, `PlaneTree.vtxs`, `PlaneTree.contour`, `PlaneTree.childCount`,
`PlaneTree.degAt` (`Closed.Trees`); `cutoffLabels`, `cutoffXi`, `IsStdGaussianFamily`, `profileF`,
`pairedB`, `branchPt`, `toutT`, `tinT`, `profileDelta` (`Closed.Profile`); `lagRespCut`, `volDR`
(`LagKernel`, `TreeClosure`); `iotaF` (`OddSpectral`); `FrozenParams`, `SpectralData` (`Setup`);
`SizeFin` (`Defs`).

Encoding decisions:
* Assignments `𝔞` are functions on vertex addresses with values in `AsgLab m n 𝒜`: an output index
  `i : Fin m` for an output vertex, an input index `j : Fin n` for an input vertex, and a label
  `α ∈ 𝒜 = cutoffLabels J ℓ` (finite) for a latent vertex. `TreeAsg` is the subtype of
  such functions
  whose support is the vertex set and whose values match the vertex types. The value at an absent
  address is `none`, so every sum over assignments is a `tsum` over a finite type.
* The source's "externally rooted typed ordered tree with root type `t`" is `RootedTypedTree t k`.
  It has the fields of `TypedOrdTree` (Closed.Trees), but `TypedOrdTree` fixes the root type to `o`;
  here the root type is the parameter `t` with `t ≠ lat`.
* Index sets of the tree sums are the sigma types `OneBufIdx` (one-buffer trees with root value
  `x`) and `PathIdx` (all `(a₁,a₂,T,𝔞)`). Absolute summability is stated explicitly where the
  source states it.
* Latent corners: a latent vertex `y` has the corners at the odd contour times `τ` with
  `c(τ) = y`; the corner at `τ` carries label `1` iff `τ < p*`, else `2` (source l.2119–2128).
* Arc counts: `n₁` and `n₂` are the numbers of even contour times in `[0,p*]` and `[p*,2k]`, with
  `p* = 2(2a₁+1)`, so the weight `Z(T)` is the source's `ζ₁^{n₁}ζ₂^{n₂}`.
* The kernel `𝔎_ξ` of `eqn:app-vol-closed-profile-kernel` contains a division by `Δ_ξ`. The path
  lemma's `_ii` asserts `Δ_ξ ≠ 0` as a conjunct, since the identity is meaningless otherwise
  (see the
  open question on this in the result file).
* Standing assumptions: `SizeFin` (one dimension), `Σ_out, Σ_in ≠ 0`, `IsProbabilityMeasure`, and
  `IsStdGaussianFamily` for the cutoff Gaussians `g`. The regime parameter `s_R` is `sRad`.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Matrix MatrixOrder
open Muon Muon.Setup

namespace Muon.Volatility

/-! ## Assignments, one-buffer trees and their values -/

/-- Values of an assignment (l.2181–2187): an output index `i ∈ {1,…,N_out}`, an input index `j`, or a
latent label `α ∈ 𝒜`; the label set is `L` (finite for the cutoff profile). -/
abbrev AsgLab (m n : ℕ) (L : Finset ℤ) : Type := Fin m ⊕ (Fin n ⊕ {α : ℤ // α ∈ L})

/-- A value (`none` off the vertex set) is compatible with a vertex type: output vertices take output
indices, input vertices take input indices, latent vertices take labels (l.2181–2187). -/
def AsgCompat {m n : ℕ} {L : Finset ℤ} : VType → Option (AsgLab m n L) → Prop
  | VType.out, some (Sum.inl _) => True
  | VType.inp, some (Sum.inr (Sum.inl _)) => True
  | VType.lat, some (Sum.inr (Sum.inr _)) => True
  | _, _ => False

/-- Assignments of the tree with vertex set `P.vtxs` and types `ty` (l.2181–2187): a function on
addresses, defined exactly on the vertex set, with values compatible with the vertex types. -/
abbrev TreeAsg (P : PlaneTree) (ty : List ℕ → VType) (m n : ℕ) (L : Finset ℤ) : Type :=
  {a : List ℕ → Option (AsgLab m n L) //
    (∀ u, u ∈ P.vtxs ↔ a u ≠ none) ∧ ∀ u ∈ P.vtxs, AsgCompat (ty u) (a u)}

/-- Externally rooted typed ordered trees with `k` edges and root type `t` (l.2084–2117, "typed ordered
tree" with the root external). `TypedOrdTree` (Closed.Trees) fixes the root type to `o`; this structure
has the same fields with the root type `t` (`root_ty`, `root_ext`). -/
structure RootedTypedTree (t : VType) (k : ℕ) where
  /-- The underlying plane tree. -/
  tree : PlaneTree
  /-- The vertex types (`lat` for latent vertices). -/
  ty : List ℕ → VType
  card_vtx : tree.vtxs.length = k + 1
  off_support : ∀ u, u ∉ tree.vtxs → ty u = VType.out
  root_ty : ty [] = t
  root_ext : t ≠ VType.lat
  edge_joins : ∀ u ∈ tree.vtxs, ∀ v ∈ tree.vtxs, v ≠ [] → v.dropLast = u →
    (ty u = VType.lat ↔ ¬ ty v = VType.lat)
  latent_alt : ∀ u ∈ tree.vtxs, u ≠ [] → ty u = VType.lat →
    CyclicAlt (ty u.dropLast :: (List.range (tree.childCount u)).map fun i => ty (u ++ [i]))

/-- The corner weight `ζ_t = (i√t)^{-1}` of a buffer with parameter `t` (l.2181–2183). -/
def zetaT (t : ℝ) : ℂ := (Complex.I * (Real.sqrt t : ℂ))⁻¹

/-- The scalar of an assignment value: `μ_i` (output), `λ_j` (input), and `0` otherwise. The same
function with `Fd`, `Gd` in place of `μ`, `λ` gives the test entries `F_{a(x)}`, `G_{a(x)}` (l.2181–2187). -/
def asgVal {m n : ℕ} {L : Finset ℤ} (f : Fin m → ℝ) (h : Fin n → ℝ) : Option (AsgLab m n L) → ℝ
  | some (Sum.inl i) => f i
  | some (Sum.inr (Sum.inl j)) => h j
  | _ => 0

/-- The cutoff label `α` of a latent value, and `0` otherwise (l.2181–2187). -/
def asgLabel {m n : ℕ} {L : Finset ℤ} : Option (AsgLab m n L) → ℤ
  | some (Sum.inr (Sum.inr α)) => α.1
  | _ => 0

/-- The one-buffer value `val_ℓ(X,𝔞)` of an externally rooted typed tree `X` with `n` edges
(l.2207–2228): `ζ_l^{n+1} 𝗄_root^{deg_X root} ∏_{x ext, x ≠ root} 𝗄_x^{deg_X x}/B ∏_{y latent}
𝔼 ξ_{l,𝔞(y)}^{deg_X y}`, with `𝗄_x = μ_{𝔞(x)}` or `λ_{𝔞(x)}` and the degrees taken in `X`. -/
def oneBufVal {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ)
    {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (g : ℤ → Ω → ℝ) (l : ℕ) (t : ℝ)
    {tr : VType} {k : ℕ} (X : RootedTypedTree tr k)
    (a : TreeAsg X.tree X.ty m n (cutoffLabels J ℓ)) : ℂ :=
  zetaT t ^ (k + 1) * ((asgVal μ lam (a.1 []) ^ X.tree.degAt [] : ℝ) : ℂ) *
    (∏ u ∈ X.tree.vtxs.toFinset.filter (fun u => u ≠ [] ∧ X.ty u ≠ VType.lat),
      ((asgVal μ lam (a.1 u) ^ X.tree.degAt u / (B : ℝ) : ℝ) : ℂ)) *
    (∏ u ∈ X.tree.vtxs.toFinset.filter (fun u => X.ty u = VType.lat),
      ((∫ ω, (cutoffXi β ℓ J R l g (asgLabel (a.1 u)) ω) ^ X.tree.degAt u ∂P : ℝ) : ℂ))

/-- The index set of the one-buffer sum `∑_X ∑_{𝔞 : 𝔞(root) = x} val_ℓ(X,𝔞)` (l.2207–2228): trees
`X` with root type `tr` and any number of edges, with an assignment whose root value is `x`. -/
abbrev OneBufIdx (m n J ℓ : ℕ) (tr : VType) (x : AsgLab m n (cutoffLabels J ℓ)) : Type :=
  Σ k : ℕ, Σ X : RootedTypedTree tr k,
    {a : TreeAsg X.tree X.ty m n (cutoffLabels J ℓ) // a.1 [] = some x}

/-- The one-buffer sum `g_{𝗍,l}(x)` of l.2207–2228: the sum of `val_ℓ` over `OneBufIdx`. -/
def oneBufG {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ)
    {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (g : ℤ → Ω → ℝ) (l : ℕ) (t : ℝ)
    (tr : VType) (x : AsgLab m n (cutoffLabels J ℓ)) : ℂ :=
  ∑' q : OneBufIdx m n J ℓ tr x, oneBufVal P β ℓ J R B μ lam g l t q.2.1 q.2.2.1

/-- The trace `m_{o,l} = (1/B) ∑_i μ_i g_{o,l}(i)` (l.2229–2233). -/
def oneBufMo {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ)
    {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (g : ℤ → Ω → ℝ) (l : ℕ) (t : ℝ) : ℂ :=
  (B : ℂ)⁻¹ * ∑ i : Fin m, (μ i : ℂ) * oneBufG P β ℓ J R B μ lam g l t VType.out (Sum.inl i)

/-- The trace `m_{in,l} = (1/B) ∑_j λ_j g_{in,l}(j)` (l.2229–2233). -/
def oneBufMin {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ)
    {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (g : ℤ → Ω → ℝ) (l : ℕ) (t : ℝ) : ℂ :=
  (B : ℂ)⁻¹ * ∑ j : Fin n, (lam j : ℂ) * oneBufG P β ℓ J R B μ lam g l t VType.inp (Sum.inr (Sum.inl j))

/-- The marginal branch point `(σ_l, σ̃_l, s̃_{1,l}, s_{1,l})` of the cutoff marginal profile `ξ_l` at
`t` (l.2234–2236). Its existence is `lem_app_vol_closed_branch_i` (Closed.Profile); the value is junk
without it. -/
def marginalBranch {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ) (R : ℝ)
    {m n : ℕ} (C : Muon.Covariances m n) (B : ℕ) (l : ℕ) (g : ℤ → Ω → ℝ) (t : ℝ) :
    ℝ × ℝ × ℝ × ℝ :=
  branchPt (profileF P (cutoffXi β ℓ J R l g)) C B t

/-- The regime radius `s_R = max(64 γ₁² C₁² R₁², 2 D_R²)` with `γ₁ = max(1, γ⋆)`, `C₁ = max(1, C_Σ)`,
`R₁ = max(1, R)` and `D_R` the radius of `lem:app-vol-norm` (`volDR`) (l.2227). -/
def sRad (cert : Muon.External.GaussianOpNorm) (γstar CSig R : ℝ) : ℝ :=
  max (64 * (max 1 γstar) ^ 2 * (max 1 CSig) ^ 2 * (max 1 R) ^ 2)
    (2 * (volDR cert R CSig γstar) ^ 2)

/-! ## The path decomposition -/

/-- The corner label of the contour time `τ` (l.2119–2128, arcs and the G-vertex): `1` if `τ < p*`, else `2`, where
`p* = 2(2a₁+1)`. -/
def cornerLabel (a1 τ : ℕ) : ℕ := if τ < 2 * (2 * a1 + 1) then 1 else 2

/-- The number of even contour times in `[lo, hi]` (l.2119–2128, arcs). -/
def arcEven (lo hi : ℕ) : ℕ := ((Finset.Icc lo hi).filter (fun τ => τ % 2 = 0)).card

/-- The corner weight `Z(T) = ζ₁^{n₁} ζ₂^{n₂}` (l.2195–2205, `eqn:app-vol-closed-Z`) for `T ∈ 𝒯_{a₁,a₂}`,
`p = (a₁,a₂)`: `n₁` counts the even contour times in arc 1 `[0,p*]`, `n₂` those in arc 2
`[p*,2k]`, with `p* = 2(2a₁+1)` and `k = 2a₁+2a₂+2`. -/
def pathZ (s u : ℝ) (p : ℕ × ℕ) : ℂ :=
  zetaT s ^ arcEven 0 (2 * (2 * p.1 + 1)) *
    zetaT u ^ arcEven (2 * (2 * p.1 + 1)) (2 * treeK p.1 p.2)

/-- The value `val(T,𝔞)` of a two-buffer tree `T ∈ 𝒯_{a₁,a₂}` (l.2181–2194): the product over external
vertices of `𝗄_x^{deg_T x}/B` with the test entries `F_{𝔞(x)}` at the root and `G_{𝔞(x)}` at the
`G`-vertex `c(p*)`, times the product over latent vertices `y` of `𝔼 ∏_{corners c of y} ξ_{l(c),𝔞(y)}`.
The corners of `y` are the odd contour times `τ < 2k` with `c(τ) = y`. -/
def pathVal {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ)
    {m n : ℕ} (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (g : ℤ → Ω → ℝ) (p : ℕ × ℕ) (T : TypedTrees p.1 p.2)
    (a : TreeAsg T.tree T.ty m n (cutoffLabels J ℓ)) : ℂ :=
  ((∏ u ∈ T.tree.vtxs.toFinset.filter (fun u => T.ty u ≠ VType.lat),
      ((asgVal μ lam (a.1 u) ^ T.tree.degAt u / (B : ℝ) *
          (if u = [] then asgVal Fd (fun _ : Fin n => (0 : ℝ)) (a.1 u) else 1) *
          (if u = T.tree.contour.getD (2 * (2 * p.1 + 1)) [] then
            asgVal (fun _ : Fin m => (0 : ℝ)) Gd (a.1 u) else 1) : ℝ) : ℂ)) : ℂ) *
  (∏ y ∈ T.tree.vtxs.toFinset.filter (fun y => T.ty y = VType.lat),
      ((∫ ω, (∏ τ ∈ (Finset.range (2 * treeK p.1 p.2)).filter
            (fun τ => τ % 2 = 1 ∧ T.tree.contour.getD τ [] = y),
          cutoffXi β ℓ J R (cornerLabel p.1 τ) g (asgLabel (a.1 y)) ω) ∂P : ℝ) : ℂ))

/-- The index set of the path sum: all `(a₁,a₂)`, `T ∈ 𝒯_{a₁,a₂}` and assignments `𝔞`
(`lem:app-vol-closed-path` family). -/
abbrev PathIdx (m n J ℓ : ℕ) : Type :=
  Σ p : ℕ × ℕ, Σ T : TypedTrees p.1 p.2, TreeAsg T.tree T.ty m n (cutoffLabels J ℓ)

/-- The summand `Z(T) val(T,𝔞)` of the path sum. -/
def pathTerm {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ)
    {m n : ℕ} (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (g : ℤ → Ω → ℝ) (s u : ℝ) (q : PathIdx m n J ℓ) : ℂ :=
  pathZ s u q.1 * pathVal P β ℓ J R B Fd Gd μ lam g q.1 q.2.1 q.2.2

/-- The closed-form kernel `𝔎_ξ[F,G](s,u) = su b T^out[F] T^in[G] / Δ_ξ` of `eqn:app-vol-closed-profile-kernel`
for the paired profile `(ξ₁, ξ₂)`, with the branch points of `ξ₁` at `s` and of `ξ₂` at `u`, `b = b(q, q')`
at `q = s σ σ̃`, `q' = u σ' σ̃'`, and test matrices `Fm`, `Gm`. Division by `0` is junk; `Δ_ξ ≠ 0`
is asserted separately where it is used. -/
def profileKernel {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {m n : ℕ}
    (C : Muon.Covariances m n) (B : ℕ) {ι : Type} [Countable ι] (ξ₁ ξ₂ : ι → Ω → ℝ)
    (Fm : Matrix (Fin m) (Fin m) ℝ) (Gm : Matrix (Fin n) (Fin n) ℝ) (s u : ℝ) : ℝ :=
  let x := branchPt (profileF P ξ₁) C B s
  let y := branchPt (profileF P ξ₂) C B u
  s * u * pairedB P ξ₁ ξ₂ (s * x.1 * x.2.1) (u * y.1 * y.2.1) *
    toutT C B x y s u Fm * tinT C B x y s u Gm / profileDelta P C B ξ₁ ξ₂ s u

/-! ## Statements -/

/-- `lem:app-vol-closed-encoding` (corner labels), snapshot `cr-2026-10-23`. Declaration of record for the
clause "the labels `l_r` being the corner labels" (ruling Q9): the corner label of the contour time `2s+1`
(paper corner `2r-1`, `r = s+1`) is the label `treeLabel a s` of TreeDef. Both are `1` iff `s ≤ 2a`.
Sorried; the proof is the arithmetic `2s+1 < 2(2a+1) ↔ s ≤ 2a`.

LaTeX (`sections/04-volatility/section.tex` l.2130–2139, verbatim):
```latex
\begin{lemma}[Encoding of retained pairings]\label{lem:app-vol-closed-encoding}
For $a_1,a_2\ge0$ there is a bijection between the retained pairings of the word
$\mathsf W_{a_1,a_2}$ in \cref{def:app-vol-tree} and $\mathcal T_{a_1,a_2}$. Under it the vertex
classes are the fibres of the contour $c$ on $\{0,\dots,2k-1\}$: the polygon
vertex $\mathsf e_r$ lies in the class of $c(2r)$ and $\mathsf l_r$ in the class of
$c(2r-1)$. Consequently, for the class $V$ of a tree vertex $x$: $p_V=\deg x$ if
$x$ is external; $S_V=\{r:c(2r-1)=x\}$ if $x$ is latent, the labels $l_r$ being the
corner labels; $\mathsf e_0\in V$ if and only if $x$ is the root; and
$\mathsf e_{2a_1+1}\in V$ if and only if $x$ is the $G$-vertex.
\end{lemma}
```
-/
theorem cornerLabel_eq_treeLabel (a b : ℕ) (s : Fin (treeK a b)) :
    cornerLabel a (2 * s.val + 1) = treeLabel a s := by
  unfold cornerLabel treeLabel
  by_cases h : s.val ≤ 2 * a
  · simp only [h, if_true, show 2 * s.val + 1 < 2 * (2 * a + 1) by omega]
  · have h2 : ¬ (2 * s.val + 1 < 2 * (2 * a + 1)) := by omega
    simp only [h, h2, if_false]

private lemma cutoff_trunc_moment {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {g : ℤ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    (α : ℤ) (d : ℕ) (R : ℝ) :
    (∫ ω, (if |g α ω| ≤ R then g α ω else 0) ^ d ∂P) = treeTruncMoment d R := by
  have hs : MeasurableSet {x : ℝ | |x| ≤ R} := by measurability
  have hm : Measurable (fun x : ℝ => (if |x| ≤ R then x else 0) ^ d) :=
    (Measurable.ite hs measurable_id measurable_const).pow_const d
  change (∫ ω, ((fun x : ℝ => (if |x| ≤ R then x else 0) ^ d) ∘ g α) ω ∂P) = _
  rw [(hg.2.2 α).integral_comp hm.aestronglyMeasurable]
  unfold treeTruncMoment
  by_cases hd : d = 0
  · subst d
    simp
  · rw [if_neg hd]
    apply integral_congr_ae
    filter_upwards with x
    split_ifs with hx
    · rfl
    · simp [zero_pow hd]

/-- Latent value of the cutoff paired profile, snapshot `cr-2026-10-23`. Declaration of record for the
clause (l.1709–1710): the latent value of a class `V` in `def:app-vol-tree` is `∑_α 𝔼 ∏_{r ∈ S_V} ξ_{l_r,α}`.
For the cutoff profile `ξ_{l,α} = ϖ_{l,α} g̃_α` with `g̃_α = g_α 1_{|g_α| ≤ R}`, the sum over `α ∈ 𝒜` equals
`m_{|S|}(R)` times `∑_α ∏_{r ∈ S} ϖ_{l_r,α}` (`treeTruncMoment`, `treeVarpi`), for every `β`, including
`S = ∅` (where `m_0 = 1`). Sorried. Standing: `IsStdGaussianFamily` (each `g_α` standard Gaussian) and
`IsProbabilityMeasure`.

LaTeX (`sections/04-volatility/section.tex` l.1709–1710, verbatim):
```latex
and the latent value of a class $V$ in \cref{def:app-vol-tree} is
$\sum_\alpha\EE\prod_{r\in S_V}\xi_{l_r,\alpha}$.
```
-/
theorem cutoff_latent_value {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {g : ℤ → Ω → ℝ} (hg : IsStdGaussianFamily P g) (β : ℝ) (ℓ J : ℕ) (R : ℝ) {k : ℕ} (a : ℕ)
    (S : Finset (Fin k)) :
    ∑ α ∈ cutoffLabels J ℓ, ∫ ω, (∏ r ∈ S, cutoffXi β ℓ J R (treeLabel a r) g α ω) ∂P =
      treeTruncMoment S.card R *
        ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ), ∏ r ∈ S, treeVarpi β ℓ (treeLabel a r) α := by
  have hlabels : cutoffLabels J ℓ = Finset.Icc (-(J : ℤ)) (ℓ : ℤ) := by
    ext α
    simp only [cutoffLabels, Finset.mem_union, Finset.mem_Icc]
    omega
  rw [← hlabels]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  simp only [cutoffXi, cutoffVarpi, hα, if_true]
  have hp : (fun ω => ∏ r ∈ S,
      treeVarpi β ℓ (treeLabel a r) α * (if |g α ω| ≤ R then g α ω else 0)) =
      fun ω => (∏ r ∈ S, treeVarpi β ℓ (treeLabel a r) α) *
        (if |g α ω| ≤ R then g α ω else 0) ^ S.card := by
    funext ω
    simp only [Finset.prod_mul_distrib, Finset.prod_const]
  rw [hp, integral_const_mul, cutoff_trunc_moment hg α S.card R]
  ring



private def ob_inc : List ℕ → List ℕ
  | [] => []
  | a :: u => (a + 1) :: u

private theorem ob_inc_ne_nil {u : List ℕ} (h : u ≠ []) : ob_inc u ≠ [] := by
  cases u with
  | nil => exact absurd rfl h
  | cons a u => simp [ob_inc]

private theorem ob_inc_inj {u v : List ℕ} (h : ob_inc u = ob_inc v) : u = v := by
  match u, v with
  | [], [] => rfl
  | [], b :: v => simp [ob_inc] at h
  | a :: u, [] => simp [ob_inc] at h
  | a :: u, b :: v => simp [ob_inc] at h; obtain ⟨h1, h2⟩ := h; subst h1; subst h2; rfl

private theorem ob_vtxsForest_succ (cs : List PlaneTree) (i : ℕ) :
    vtxsForest cs (i + 1) = (vtxsForest cs i).map ob_inc := by
  induction cs generalizing i with
  | nil => simp [vtxsForest]
  | cons c cs ih =>
    simp only [vtxsForest, List.map_append, List.map_map, ih (i+1)]
    congr 1

private theorem ob_vtxsForest_ne_nil {cs : List PlaneTree} {i : ℕ} {u : List ℕ}
    (h : u ∈ vtxsForest cs i) : u ≠ [] := by
  induction cs generalizing i with
  | nil => simp [vtxsForest] at h
  | cons c cs ih =>
    simp only [vtxsForest, List.mem_append, List.mem_map] at h
    rcases h with ⟨w, _, rfl⟩ | h
    · simp
    · exact ih h

private theorem ob_vtxs_node (cs : List PlaneTree) :
    (PlaneTree.node cs).vtxs = [] :: vtxsForest cs 0 := by
  simp [PlaneTree.vtxs]

private theorem ob_vtxs_node_cons (P1 : PlaneTree) (cs : List PlaneTree) :
    (PlaneTree.node (P1 :: cs)).vtxs =
      [] :: (P1.vtxs.map (List.cons 0) ++ (vtxsForest cs 0).map ob_inc) := by
  simp [PlaneTree.vtxs, vtxsForest, ob_vtxsForest_succ]

private theorem ob_mem_vtxs_cons {P1 : PlaneTree} {cs : List PlaneTree} {v : List ℕ} :
    v ∈ (PlaneTree.node (P1 :: cs)).vtxs ↔
      v = [] ∨ (∃ w ∈ P1.vtxs, v = 0 :: w) ∨
        (∃ w ∈ (PlaneTree.node cs).vtxs, w ≠ [] ∧ v = ob_inc w) := by
  rw [ob_vtxs_node_cons, ob_vtxs_node]
  simp only [List.mem_cons, List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨w, hw, h⟩ | ⟨w, hw, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨w, hw, h.symm⟩)
    · exact Or.inr (Or.inr ⟨w, Or.inr hw, ob_vtxsForest_ne_nil hw, h.symm⟩)
  · rintro (h | ⟨w, hw, h⟩ | ⟨w, hw | hw, hne, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨w, hw, h.symm⟩)
    · exact absurd hw hne
    · exact Or.inr (Or.inr ⟨w, hw, h.symm⟩)

private theorem ob_mem_cons0 {P1 : PlaneTree} {cs : List PlaneTree} {w : List ℕ} :
    0 :: w ∈ (PlaneTree.node (P1 :: cs)).vtxs ↔ w ∈ P1.vtxs := by
  rw [ob_mem_vtxs_cons]
  constructor
  · rintro (h | ⟨x, hx, h⟩ | ⟨x, hx, hne, h⟩)
    · simp at h
    · simp at h; rw [h]; exact hx
    · exfalso
      match x, hne, h with
      | a :: y, _, h => simp [ob_inc] at h
  · intro h; exact Or.inr (Or.inl ⟨w, h, rfl⟩)

private theorem ob_mem_inc {P1 : PlaneTree} {cs : List PlaneTree} {w : List ℕ} :
    ob_inc w ∈ (PlaneTree.node (P1 :: cs)).vtxs ↔ w ∈ (PlaneTree.node cs).vtxs := by
  rw [ob_mem_vtxs_cons]
  constructor
  · rintro (h | ⟨x, hx, h⟩ | ⟨x, hx, hne, h⟩)
    · have : w = [] := by
        match w, h with
        | [], _ => rfl
      subst this
      rw [ob_vtxs_node]; simp
    · exfalso
      match w, h with
      | [], h => simp [ob_inc] at h
      | a :: y, h => simp [ob_inc] at h
    · have := ob_inc_inj h; subst this; exact hx
  · intro h
    by_cases hw : w = []
    · subst hw; exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨w, h, hw, rfl⟩)

private theorem ob_pt_vtxs_pos (P : PlaneTree) : 1 ≤ P.vtxs.length := by
  cases P with
  | node cs => rw [ob_vtxs_node]; simp

private theorem ob_pt_vtxs_len (P1 : PlaneTree) (cs : List PlaneTree) :
    (PlaneTree.node (P1 :: cs)).vtxs.length = P1.vtxs.length + (PlaneTree.node cs).vtxs.length := by
  have h1 : P1.vtxs.length = 1 + (match P1 with | .node c => (vtxsForest c 0).length) := by
    cases P1 with
    | node c => rw [ob_vtxs_node]; simp; omega
  rw [ob_vtxs_node_cons, ob_vtxs_node]
  simp only [List.length_cons, List.length_append, List.length_map]
  rw [h1]
  cases P1 with
  | node c => simp only [ob_vtxs_node, List.length_cons]; omega

private theorem ob_plane_ind (M : PlaneTree → Prop) (h0 : M (.node []))
    (h1 : ∀ P1 cs, M P1 → M (.node cs) → M (.node (P1 :: cs))) : ∀ P, M P := by
  intro P
  induction hn : P.vtxs.length using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    cases P with
    | node cs =>
      cases cs with
      | nil => exact h0
      | cons P1 cs =>
        rw [ob_pt_vtxs_len] at hn
        have a1 := ob_pt_vtxs_pos P1
        have a2 := ob_pt_vtxs_pos (PlaneTree.node cs)
        exact h1 P1 cs (ih _ (by omega) P1 rfl) (ih _ (by omega) (PlaneTree.node cs) rfl)

private theorem ob_pt_nodup (P : PlaneTree) : P.vtxs.Nodup := by
  refine ob_plane_ind (fun P => P.vtxs.Nodup) (by simp [PlaneTree.vtxs, vtxsForest]) ?_ P
  intro P1 cs h1 h2
  rw [ob_vtxs_node] at h2
  rw [ob_vtxs_node_cons]
  have h2' := List.nodup_cons.mp h2
  refine List.nodup_cons.mpr ⟨?_, ?_⟩
  · simp only [List.mem_append, List.mem_map, not_or]
    refine ⟨?_, ?_⟩
    · rintro ⟨w, _, hw⟩; simp at hw
    · rintro ⟨w, hw, hw'⟩
      exact ob_inc_ne_nil (ob_vtxsForest_ne_nil hw) hw'
  · rw [List.nodup_append]
    refine ⟨h1.map (fun a b h => by simpa using h), h2'.2.map (fun a b h => ob_inc_inj h), ?_⟩
    intro x hx y hy hxy
    simp only [List.mem_map] at hx hy
    obtain ⟨w, _, rfl⟩ := hx
    obtain ⟨w', hw', rfl⟩ := hy
    have hne := ob_vtxsForest_ne_nil hw'
    match w', hne with
    | a :: u, _ => simp [ob_inc] at hxy

private theorem ob_pt_mem_idx (cs : List PlaneTree) (a : ℕ) (w : List ℕ) :
    (a :: w) ∈ (PlaneTree.node cs).vtxs ↔ ∃ h : a < cs.length, w ∈ (cs[a]).vtxs := by
  induction cs generalizing a with
  | nil => simp [ob_vtxs_node, vtxsForest]
  | cons P1 cs ih =>
    cases a with
    | zero => rw [ob_mem_cons0]; simp
    | succ a =>
      have : (a + 1) :: w = ob_inc (a :: w) := rfl
      rw [this, ob_mem_inc, ih]
      simp

private theorem ob_pt_root_mem (P : PlaneTree) : ([] : List ℕ) ∈ P.vtxs := by
  cases P with
  | node cs => rw [ob_vtxs_node]; simp

private theorem ob_pt_parent_mem (u : List ℕ) : ∀ (P : PlaneTree) (i : ℕ),
    u ++ [i] ∈ P.vtxs → u ∈ P.vtxs := by
  induction u with
  | nil => intro P i _; exact ob_pt_root_mem P
  | cons a u ih =>
    intro P i h
    cases P with
    | node cs =>
      rw [List.cons_append, ob_pt_mem_idx] at h
      obtain ⟨hl, hm⟩ := h
      rw [ob_pt_mem_idx]
      exact ⟨hl, ih _ i hm⟩

private theorem ob_pt_prefix_closed (u : List ℕ) : ∀ (P : PlaneTree) (i j : ℕ), i < j →
    u ++ [j] ∈ P.vtxs → u ++ [i] ∈ P.vtxs := by
  induction u with
  | nil =>
    intro P i j hij h
    cases P with
    | node cs =>
      rw [List.nil_append, ob_pt_mem_idx] at h
      obtain ⟨hl, hm⟩ := h
      rw [List.nil_append, ob_pt_mem_idx]
      exact ⟨by omega, ob_pt_root_mem _⟩
  | cons a u ih =>
    intro P i j hij h
    cases P with
    | node cs =>
      rw [List.cons_append, ob_pt_mem_idx] at h
      obtain ⟨hl, hm⟩ := h
      rw [List.cons_append, ob_pt_mem_idx]
      exact ⟨hl, ih _ i j hij hm⟩

private theorem ob_downclosed_iff (l : List ℕ) (hl : l.Nodup) (hd : ∀ i ∈ l, ∀ j < i, j ∈ l) (i : ℕ) :
    i ∈ l ↔ i < l.length := by
  have hcard : l.toFinset.card = l.length := List.toFinset_card_of_nodup hl
  constructor
  · intro hi
    have : Finset.range (i + 1) ⊆ l.toFinset := by
      intro x hx
      rw [Finset.mem_range] at hx
      rw [List.mem_toFinset]
      rcases Nat.lt_or_ge x i with h | h
      · exact hd i hi x h
      · have : x = i := by omega
        rw [this]; exact hi
    have := Finset.card_le_card this
    rw [Finset.card_range, hcard] at this
    omega
  · intro hi
    by_contra hni
    have : l.toFinset ⊆ Finset.range i := by
      intro x hx
      rw [List.mem_toFinset] at hx
      rw [Finset.mem_range]
      by_contra hge
      exact hni (by
        rcases Nat.eq_or_lt_of_le (not_lt.mp hge) with h | h
        · rw [h]; exact hx
        · exact hd x hx i h)
    have := Finset.card_le_card this
    rw [Finset.card_range, hcard] at this
    omega

private theorem ob_pt_childCount_iff (P : PlaneTree) (u : List ℕ) (i : ℕ) :
    u ++ [i] ∈ P.vtxs ↔ u ∈ P.vtxs ∧ i < P.childCount u := by
  classical
  set F := P.vtxs.filter (fun v => v ≠ [] ∧ v.dropLast = u) with hF
  have hFl : P.childCount u = F.length := rfl
  set l := F.map (fun v => v.getLastD 0) with hl
  have hFmem : ∀ v, v ∈ F ↔ ∃ i, v = u ++ [i] ∧ u ++ [i] ∈ P.vtxs := by
    intro v
    rw [hF, List.mem_filter]
    constructor
    · rintro ⟨hv, hd⟩
      simp only [decide_eq_true_eq] at hd
      obtain ⟨hne, hdl⟩ := hd
      refine ⟨v.getLastD 0, ?_, ?_⟩
      · rw [← hdl]
        have := List.dropLast_append_getLast hne
        rw [List.getLastD_eq_getLast?]
        rw [List.getLast?_eq_getLast_of_ne_nil hne]
        simpa using this.symm
      · have : v = u ++ [v.getLastD 0] := by
          rw [← hdl]
          have := List.dropLast_append_getLast hne
          rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast_of_ne_nil hne]
          simpa using this.symm
        rw [← this]; exact hv
    · rintro ⟨i, rfl, hi⟩
      refine ⟨hi, ?_⟩
      simp
  have hlmem : ∀ i, i ∈ l ↔ u ++ [i] ∈ P.vtxs := by
    intro i
    rw [hl, List.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨j, rfl, hj⟩ := (hFmem v).mp hv
      simpa using hj
    · intro h
      exact ⟨u ++ [i], (hFmem _).mpr ⟨i, rfl, h⟩, by simp⟩
  have hnd : l.Nodup := by
    rw [hl]
    refine List.Nodup.map_on ?_ ((ob_pt_nodup P).filter _)
    intro x hx y hy hxy
    obtain ⟨i, rfl, _⟩ := (hFmem x).mp hx
    obtain ⟨j, rfl, _⟩ := (hFmem y).mp hy
    simp at hxy
    rw [hxy]
  have hdc : ∀ i ∈ l, ∀ j < i, j ∈ l := by
    intro i hi j hj
    rw [hlmem] at hi ⊢
    exact ob_pt_prefix_closed u P j i hj hi
  have hlen : l.length = P.childCount u := by rw [hl, List.length_map]; rfl
  constructor
  · intro h
    refine ⟨ob_pt_parent_mem u P i h, ?_⟩
    rw [← hlen, ← ob_downclosed_iff l hnd hdc]
    exact (hlmem i).mpr h
  · rintro ⟨_, h⟩
    rw [← hlmem, ob_downclosed_iff l hnd hdc, hlen]
    exact h

/-! ## Helpers for `lem_app_vol_closed_onebuffer_i` (task P-D.17.P1) -/

private theorem ob_parent_mem (P : PlaneTree) {v : List ℕ} (hv : v ∈ P.vtxs) (hne : v ≠ []) :
    v.dropLast ∈ P.vtxs := by
  have h := List.dropLast_append_getLast hne
  rw [← h] at hv
  exact ob_pt_parent_mem _ P _ hv

private theorem ob_childCount_eq (P : PlaneTree) (u : List ℕ) :
    P.childCount u = (P.vtxs.toFinset.filter (fun v => v ≠ [] ∧ v.dropLast = u)).card := by
  classical
  unfold PlaneTree.childCount
  rw [← List.toFinset_card_of_nodup ((ob_pt_nodup P).filter _), List.toFinset_filter]
  simp

private theorem ob_card_vtxs {tr : VType} {k : ℕ} (X : RootedTypedTree tr k) :
    X.tree.vtxs.toFinset.card = k + 1 := by
  rw [List.toFinset_card_of_nodup (ob_pt_nodup _), X.card_vtx]

/-- Sum of child counts over a parent-closed predicate. -/
private theorem ob_sum_childCount (P : PlaneTree) (p : List ℕ → Prop) [DecidablePred p] :
    ∑ u ∈ P.vtxs.toFinset.filter p, P.childCount u =
      ((P.vtxs.toFinset.filter (fun v => v ≠ [])).filter (fun v => p v.dropLast)).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := List.dropLast) (t := P.vtxs.toFinset.filter p)]
  · refine Finset.sum_congr rfl fun u hu => ?_
    rw [ob_childCount_eq]
    congr 1
    ext v
    simp only [Finset.mem_filter, List.mem_toFinset] at hu ⊢
    constructor
    · rintro ⟨hv, hne, hd⟩
      exact ⟨⟨⟨hv, hne⟩, by rw [hd]; exact hu.2⟩, hd⟩
    · rintro ⟨⟨⟨hv, hne⟩, _⟩, hd⟩
      exact ⟨hv, hne, hd⟩
  · intro v hv
    simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_coe] at hv ⊢
    exact ⟨ob_parent_mem P hv.1.1 hv.1.2, hv.2⟩

private theorem ob_deg_sums {tr : VType} {k : ℕ} (X : RootedTypedTree tr k) :
    ∑ u ∈ X.tree.vtxs.toFinset.filter (fun u => X.ty u ≠ VType.lat), X.tree.degAt u = k ∧
    ∑ u ∈ X.tree.vtxs.toFinset.filter (fun u => X.ty u = VType.lat), X.tree.degAt u = k ∧
    (X.tree.vtxs.toFinset.filter (fun u => u ≠ [] ∧ X.ty u ≠ VType.lat)).card ≤ k ∧
    ∀ u ∈ X.tree.vtxs, X.ty u = VType.lat → 1 ≤ X.tree.degAt u := by
  classical
  set V := X.tree.vtxs.toFinset with hV
  set E := V.filter (fun v => v ≠ []) with hE
  have hroot : ([] : List ℕ) ∈ X.tree.vtxs := ob_pt_root_mem _
  have hEcard : E.card = k := by
    have : E = V.erase [] := by
      ext v; simp [hE, Finset.mem_erase, and_comm]
    rw [this, Finset.card_erase_of_mem (by simpa [hV] using hroot), hV, ob_card_vtxs]; rfl
  have hroot_ty : X.ty [] ≠ VType.lat := by rw [X.root_ty]; exact X.root_ext
  have hdeg : ∀ (q : List ℕ → Prop) [DecidablePred q],
      ∑ u ∈ V.filter q, X.tree.degAt u =
        ∑ u ∈ V.filter q, X.tree.childCount u + (E.filter q).card := by
    intro q _
    unfold PlaneTree.degAt
    rw [Finset.sum_add_distrib]
    congr 1
    rw [hE, Finset.filter_filter, Finset.card_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h1 : q u <;> by_cases h2 : u = [] <;> simp [h1, h2]
  have hjoin : ∀ v ∈ E, (X.ty v.dropLast = VType.lat ↔ ¬ X.ty v = VType.lat) := by
    intro v hv
    have hv' : v ∈ X.tree.vtxs := by
      simpa [hE, hV] using (Finset.mem_filter.mp hv).1
    have hne : v ≠ [] := (Finset.mem_filter.mp hv).2
    exact X.edge_joins _ (ob_parent_mem _ hv' hne) v hv' hne rfl
  have hsplit : ∀ (q : List ℕ → Prop) [DecidablePred q],
      (E.filter q).card + (E.filter (fun v => ¬ q v)).card = k := by
    intro q _
    rw [Finset.card_filter_add_card_filter_not, hEcard]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdeg, ob_sum_childCount]
    have h1 : (E.filter (fun v => X.ty v.dropLast ≠ VType.lat)) =
        E.filter (fun v => X.ty v = VType.lat) := by
      refine Finset.filter_congr fun v hv => ?_
      have := hjoin v hv
      constructor
      · intro h; by_contra h2; exact h (this.mpr h2)
      · intro h h2; exact (this.mp h2) h
    rw [hE] at h1 ⊢
    rw [h1]
    have := hsplit (fun v => X.ty v = VType.lat)
    rw [hE] at this
    exact this
  · rw [hdeg, ob_sum_childCount]
    have h1 : (E.filter (fun v => X.ty v.dropLast = VType.lat)) =
        E.filter (fun v => ¬ X.ty v = VType.lat) := by
      refine Finset.filter_congr fun v hv => ?_
      exact hjoin v hv
    rw [hE] at h1 ⊢
    rw [h1]
    have := hsplit (fun v => X.ty v = VType.lat)
    rw [hE] at this
    omega
  · have : V.filter (fun u => u ≠ [] ∧ X.ty u ≠ VType.lat) = E.filter (fun u => X.ty u ≠ VType.lat) := by
      rw [hE, Finset.filter_filter]
    rw [this]
    exact le_trans (Finset.card_filter_le _ _) hEcard.le
  · intro u hu hl
    have hne : u ≠ [] := by rintro rfl; exact hroot_ty hl
    unfold PlaneTree.degAt; simp [hne]

/-! ### Counting rooted typed trees -/

private def ob_f0 : VType → VType
  | VType.out => VType.inp
  | VType.inp => VType.out
  | VType.lat => VType.lat

private def ob_fT (t : VType) (x : VType) : VType := if t = VType.out then x else ob_f0 x

private theorem ob_fT_inj (t : VType) : Function.Injective (ob_fT t) := by
  intro x y h
  unfold ob_fT at h
  by_cases ht : t = VType.out
  · simpa [ht] using h
  · simp only [ht, if_false] at h
    cases x <;> cases y <;> simp_all [ob_f0]

private theorem ob_fT_lat (t : VType) : ob_fT t VType.lat = VType.lat := by
  unfold ob_fT; by_cases ht : t = VType.out <;> simp [ht, ob_f0]

private theorem ob_fT_eq_lat (t : VType) (x : VType) : ob_fT t x = VType.lat ↔ x = VType.lat := by
  constructor
  · intro h
    rw [← ob_fT_lat t] at h
    exact ob_fT_inj t h
  · rintro rfl; exact ob_fT_lat t

private theorem ob_fT_root (t : VType) (ht : t ≠ VType.lat) : ob_fT t t = VType.out := by
  unfold ob_fT
  by_cases h : t = VType.out
  · simp [h]
  · simp only [h, if_false]
    cases t <;> simp_all [ob_f0]

private theorem ob_cyclicAlt_map (L : List VType) (hL : CyclicAlt L) (f : VType → VType)
    (hf : Function.Injective f) (hlat : f VType.lat = VType.lat) (hlat' : ∀ x, f x = VType.lat → x = VType.lat) :
    CyclicAlt (L.map f) := by
  have hget : ∀ j, (L.map f).getD j VType.lat = f (L.getD j VType.lat) := by
    intro j
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases L[j]? <;> simp [hlat]
  intro j hj
  rw [List.length_map] at hj ⊢
  rw [hget, hget]
  obtain ⟨h1, h2⟩ := hL j hj
  exact ⟨fun h => h1 (hlat' _ h), fun h => h2 (hf h)⟩

private def ob_toOrd {tr : VType} {k : ℕ} (X : RootedTypedTree tr k) : TypedOrdTree k where
  tree := X.tree
  ty := fun u => if u ∈ X.tree.vtxs then ob_fT tr (X.ty u) else VType.out
  card_vtx := X.card_vtx
  off_support := by intro u hu; simp [hu]
  root_out := by simp [ob_pt_root_mem, X.root_ty, ob_fT_root tr X.root_ext]
  edge_joins := by
    intro u hu v hv hne hd
    simp only [hu, hv, if_true, ob_fT_eq_lat]
    exact X.edge_joins u hu v hv hne hd
  latent_alt := by
    intro u hu hne hl
    simp only [hu, if_true, ob_fT_eq_lat] at hl
    have hpar : u.dropLast ∈ X.tree.vtxs := ob_parent_mem _ hu hne
    have h := ob_cyclicAlt_map _ (X.latent_alt u hu hne hl) (ob_fT tr) (ob_fT_inj tr) (ob_fT_lat tr)
      (fun x hx => (ob_fT_eq_lat tr x).mp hx)
    convert h using 1
    simp only [List.map_cons, List.map_map, hpar, if_true]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    have hi' : i < X.tree.childCount u := List.mem_range.mp hi
    have : u ++ [i] ∈ X.tree.vtxs := (ob_pt_childCount_iff X.tree u i).mpr ⟨hu, hi'⟩
    simp [this]

private theorem ob_toOrd_inj {tr : VType} {k : ℕ} : Function.Injective (ob_toOrd (tr := tr) (k := k)) := by
  intro X Y h
  have h1 : X.tree = Y.tree := congrArg TypedOrdTree.tree h
  have h2 : X.ty = Y.ty := by
    funext u
    have := congrFun (congrArg TypedOrdTree.ty h) u
    by_cases hu : u ∈ X.tree.vtxs
    · have hu' : u ∈ Y.tree.vtxs := h1 ▸ hu
      change (if u ∈ X.tree.vtxs then _ else _) = (if u ∈ Y.tree.vtxs then _ else _) at this
      simp only [hu, hu', if_true] at this
      exact ob_fT_inj tr this
    · have hu' : u ∉ Y.tree.vtxs := h1 ▸ hu
      rw [X.off_support u hu, Y.off_support u hu']
  cases X; cases Y
  simp only at h1 h2
  subst h1; subst h2; rfl

private theorem ob_card_rooted (tr : VType) (k : ℕ) :
    Finite (RootedTypedTree tr k) ∧ Nat.card (RootedTypedTree tr k) ≤ 4 ^ k := by
  obtain ⟨hf, hc⟩ := typedOrdTree_card_le k
  haveI := hf
  exact ⟨Finite.of_injective _ ob_toOrd_inj,
    le_trans (Nat.card_le_card_of_injective _ ob_toOrd_inj) hc⟩

/-! ### Elementary bounds -/

open scoped Matrix.Norms.L2Operator in
private theorem ob_abs_eig_le {m : ℕ} (S U : Matrix (Fin m) (Fin m) ℝ) (μ : ℝ) (i : Fin m)
    (hU : Uᵀ * U = 1) (h : S *ᵥ (fun k => U k i) = μ • (fun k => U k i)) : |μ| ≤ opNorm S := by
  rw [opNorm_eq_norm]
  set x : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun k => U k i) with hxdef
  have hx : ‖x‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have h1 : ∑ k, ‖x k‖ ^ 2 = 1 := by
      have := congrFun (congrFun hU i) i
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at this
      simp only [hxdef, Real.norm_eq_abs, sq_abs, PiLp.toLp_apply]
      rw [← this]; refine Finset.sum_congr rfl fun k _ => by ring
    rw [h1]; simp
  have := Matrix.l2_opNorm_mulVec S x
  have e : (EuclideanSpace.equiv (Fin m) ℝ).symm (S *ᵥ x) = μ • x := by
    ext k
    have hk := congrFun h k
    simpa [hxdef, Matrix.mulVec] using hk
  rw [e, norm_smul, hx, mul_one, Real.norm_eq_abs] at this
  simpa [hx] using this

private theorem ob_ext_sum {N B : ℕ} (v : Fin N → ℝ) (γ C : ℝ) (hγ : 1 ≤ γ) (hC : 1 ≤ C)
    (hv : ∀ i, |v i| ≤ C) (hN : (N : ℝ) ≤ γ * B) (p : ℕ) :
    ∑ i, |v i ^ p / (B : ℝ)| ≤ γ * C ^ p := by
  have hCp : 0 ≤ C ^ p := by positivity
  have h1 : ∀ i, |v i ^ p / (B : ℝ)| ≤ C ^ p / (B : ℝ) := by
    intro i
    rw [abs_div, abs_pow, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hv i) p) (Nat.cast_nonneg _)
  refine (Finset.sum_le_sum fun i _ => h1 i).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos B with hB | hB
  · subst hB; simp; positivity
  · have hB' : (0 : ℝ) < B := by exact_mod_cast hB
    rw [← mul_div_assoc, div_le_iff₀ hB']
    calc (N : ℝ) * C ^ p ≤ γ * B * C ^ p := mul_le_mul_of_nonneg_right hN hCp
      _ = γ * C ^ p * B := by ring

private theorem ob_sum_opt {m n : ℕ} {L : Finset ℤ} (f : Option (AsgLab m n L) → ℝ) :
    ∑ o, f o = f none + ∑ i : Fin m, f (some (Sum.inl i)) +
      ∑ j : Fin n, f (some (Sum.inr (Sum.inl j))) +
      ∑ α : {α : ℤ // α ∈ L}, f (some (Sum.inr (Sum.inr α))) := by
  rw [Fintype.sum_option, Fintype.sum_sum_type, Fintype.sum_sum_type]
  ring

/-! ### Cutoff coefficients -/

private theorem ob_emaW_nonneg {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (j : ℕ) : 0 ≤ Muon.emaW β j := by
  unfold Muon.emaW
  have := hβ.1; have := hβ.2
  exact mul_nonneg (by linarith) (pow_nonneg hβ.1 j)

private theorem ob_emaW_le_one {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (j : ℕ) : Muon.emaW β j ≤ 1 := by
  unfold Muon.emaW
  have h1 : β ^ j ≤ 1 := pow_le_one₀ hβ.1 hβ.2.le
  nlinarith [hβ.1, hβ.2, pow_nonneg hβ.1 j]

private theorem ob_treeVarpi_range {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (ℓ l : ℕ) (α : ℤ) :
    0 ≤ treeVarpi β ℓ l α ∧ treeVarpi β ℓ l α ≤ 1 := by
  unfold treeVarpi
  have hb : β ^ ℓ ≤ 1 := pow_le_one₀ hβ.1 hβ.2.le
  have hb0 : 0 ≤ β ^ ℓ := pow_nonneg hβ.1 ℓ
  have e0 := ob_emaW_nonneg hβ
  have e1 := ob_emaW_le_one hβ
  split_ifs
  · exact ⟨e0 _, e1 _⟩
  · exact ⟨mul_nonneg hb0 (e0 _), by nlinarith [e0 α.natAbs, e1 α.natAbs]⟩
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨e0 _, e1 _⟩

private theorem ob_cutoffVarpi_range {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (ℓ J l : ℕ) (α : ℤ) :
    0 ≤ cutoffVarpi β ℓ J l α ∧ cutoffVarpi β ℓ J l α ≤ 1 := by
  unfold cutoffVarpi
  split_ifs
  · exact ob_treeVarpi_range hβ ℓ l α
  · exact ⟨le_rfl, zero_le_one⟩

private theorem ob_geom (β : ℝ) (n : ℕ) : ∑ i ∈ Finset.range n, (1 - β) * β ^ i = 1 - β ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

private theorem ob_cutoffVarpi_sum {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (ℓ J l : ℕ) :
    ∑ α ∈ cutoffLabels J ℓ, cutoffVarpi β ℓ J l α ≤ 1 := by
  have hdisj : Disjoint (Finset.Icc (-(J : ℤ)) 0) (Finset.Icc 1 (ℓ : ℤ)) := by
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_Icc] at ha hb; omega
  have hsub : ∀ α ∈ cutoffLabels J ℓ, cutoffVarpi β ℓ J l α = treeVarpi β ℓ l α := by
    intro α hα; unfold cutoffVarpi; rw [if_pos hα]
  unfold cutoffLabels
  rw [Finset.sum_union hdisj]
  have hA : ∑ α ∈ Finset.Icc (-(J : ℤ)) 0, cutoffVarpi β ℓ J l α =
      (if l = 1 then 1 else β ^ ℓ) * (1 - β ^ (J + 1)) := by
    have himg : Finset.Icc (-(J : ℤ)) 0 = (Finset.range (J + 1)).image (fun j : ℕ => -(j : ℤ)) := by
      ext a; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · intro h; exact ⟨a.natAbs, by omega, by omega⟩
      · rintro ⟨j, hj, rfl⟩; omega
    rw [himg, Finset.sum_image (by intro a _ b _ h; simpa using h)]
    have : ∀ j ∈ Finset.range (J + 1), cutoffVarpi β ℓ J l (-(j : ℤ)) =
        (if l = 1 then 1 else β ^ ℓ) * ((1 - β) * β ^ j) := by
      intro j hj
      rw [hsub _ (by
        unfold cutoffLabels
        simp only [Finset.mem_range] at hj
        simp only [Finset.mem_union, Finset.mem_Icc]; left; omega)]
      unfold treeVarpi
      by_cases hl : l = 1
      · simp [hl, Muon.emaW]
      · simp [hl, Muon.emaW]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, ob_geom]
  have hB : ∑ α ∈ Finset.Icc 1 (ℓ : ℤ), cutoffVarpi β ℓ J l α =
      if l = 1 then 0 else 1 - β ^ ℓ := by
    have himg : Finset.Icc 1 (ℓ : ℤ) = (Finset.range ℓ).image (fun j : ℕ => (j : ℤ) + 1) := by
      ext a; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · intro h; exact ⟨(a - 1).toNat, by omega, by omega⟩
      · rintro ⟨j, hj, rfl⟩; omega
    rw [himg, Finset.sum_image (by intro a _ b _ h; simpa using h)]
    by_cases hl : l = 1
    · rw [if_pos hl]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [hsub _ (by
        unfold cutoffLabels
        simp only [Finset.mem_range] at hj
        simp only [Finset.mem_union, Finset.mem_Icc]; right; omega)]
      unfold treeVarpi
      simp [hl]
    · rw [if_neg hl]
      have : ∀ j ∈ Finset.range ℓ, cutoffVarpi β ℓ J l ((j : ℤ) + 1) = (1 - β) * β ^ (ℓ - 1 - j) := by
        intro j hj
        rw [hsub _ (by
          unfold cutoffLabels
          simp only [Finset.mem_range] at hj
          simp only [Finset.mem_union, Finset.mem_Icc]; right; omega)]
        unfold treeVarpi
        have h1 : ¬ ((j : ℤ) + 1 ≤ 0) := by omega
        simp only [h1, if_false, hl]
        simp only [Muon.emaW]
        have h2 : ((j : ℤ) + 1).toNat = j + 1 := by omega
        rw [h2]
        congr 2
        omega
      rw [Finset.sum_congr rfl this, Finset.sum_range_reflect (fun j => (1 - β) * β ^ j) ℓ, ob_geom]
  rw [hA, hB]
  have hb : 0 ≤ β ^ ℓ := pow_nonneg hβ.1 ℓ
  have hb1 : β ^ ℓ ≤ 1 := pow_le_one₀ hβ.1 hβ.2.le
  have hc : 0 ≤ β ^ (J + 1) := pow_nonneg hβ.1 _
  by_cases hl : l = 1
  · simp only [hl, if_true]; nlinarith
  · simp only [hl, if_false]; nlinarith [mul_nonneg hb hc]

private theorem ob_lat_bound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (ℓ J : ℕ) (R : ℝ) (g : ℤ → Ω → ℝ) (l : ℕ) (p : ℕ) (hp : 1 ≤ p) :
    ∑ α ∈ cutoffLabels J ℓ, |∫ ω, (cutoffXi β ℓ J R l g α ω) ^ p ∂P| ≤ (max 1 R) ^ p := by
  have hR1 : (0 : ℝ) ≤ max 1 R := le_trans zero_le_one (le_max_left _ _)
  have h1 : ∀ α, |∫ ω, (cutoffXi β ℓ J R l g α ω) ^ p ∂P| ≤ cutoffVarpi β ℓ J l α * (max 1 R) ^ p := by
    intro α
    obtain ⟨h0, h1⟩ := ob_cutoffVarpi_range hβ ℓ J l α
    have hpt : ∀ ω, ‖(cutoffXi β ℓ J R l g α ω) ^ p‖ ≤ (cutoffVarpi β ℓ J l α * max 1 R) ^ p := by
      intro ω
      rw [norm_pow, Real.norm_eq_abs]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ p
      unfold cutoffXi
      rw [abs_mul, abs_of_nonneg h0]
      refine mul_le_mul_of_nonneg_left ?_ h0
      split_ifs with h
      · exact h.trans (le_max_right _ _)
      · simpa using hR1
    have := MeasureTheory.norm_integral_le_of_norm_le_const (μ := P) (f := fun ω => (cutoffXi β ℓ J R l g α ω) ^ p)
      (C := (cutoffVarpi β ℓ J l α * max 1 R) ^ p) (Filter.Eventually.of_forall hpt)
    simp only [probReal_univ, mul_one, Real.norm_eq_abs] at this
    refine this.trans ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_of_le_one h0 h1 (by omega)) (pow_nonneg hR1 p)
  refine (Finset.sum_le_sum fun α _ => h1 α).trans ?_
  rw [← Finset.sum_mul]
  calc (∑ α ∈ cutoffLabels J ℓ, cutoffVarpi β ℓ J l α) * (max 1 R) ^ p ≤ 1 * (max 1 R) ^ p :=
        mul_le_mul_of_nonneg_right (ob_cutoffVarpi_sum hβ ℓ J l) (pow_nonneg hR1 p)
    _ = _ := one_mul _

/-! ### Vertex weights and the factorization -/

open Classical in
/-- The vertex weight: the absolute value of the vertex factor of `oneBufVal` evaluated at the
value `o`, zero for incompatible values and (at the root) for values other than `x`. -/
private noncomputable def ob_W {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ) (R : ℝ)
    (B : ℕ) {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (g : ℤ → Ω → ℝ) (l : ℕ)
    {tr : VType} {k : ℕ} (X : RootedTypedTree tr k) (x : AsgLab m n (cutoffLabels J ℓ))
    (u : List ℕ) (o : Option (AsgLab m n (cutoffLabels J ℓ))) : ℝ :=
  if AsgCompat (X.ty u) o then
    (if u = [] then (if o = some x then |asgVal μ lam o| ^ X.tree.degAt u else 0)
     else if X.ty u = VType.lat then
       |∫ ω, (cutoffXi β ℓ J R l g (asgLabel o) ω) ^ X.tree.degAt u ∂P|
     else |asgVal μ lam o ^ X.tree.degAt u / (B : ℝ)|)
  else 0

private theorem ob_W_nonneg {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ) (R : ℝ)
    (B : ℕ) {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (g : ℤ → Ω → ℝ) (l : ℕ)
    {tr : VType} {k : ℕ} (X : RootedTypedTree tr k) (x : AsgLab m n (cutoffLabels J ℓ))
    (u : List ℕ) (o : Option (AsgLab m n (cutoffLabels J ℓ))) :
    0 ≤ ob_W P β ℓ J R B μ lam g l X x u o := by
  unfold ob_W
  split_ifs <;> first | positivity | exact le_rfl

private theorem ob_val_norm {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ) (R : ℝ)
    (B : ℕ) {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (g : ℤ → Ω → ℝ) (l : ℕ) (t : ℝ)
    {tr : VType} {k : ℕ} (X : RootedTypedTree tr k) (x : AsgLab m n (cutoffLabels J ℓ))
    (a : TreeAsg X.tree X.ty m n (cutoffLabels J ℓ)) (ha : a.1 [] = some x) :
    ‖oneBufVal P β ℓ J R B μ lam g l t X a‖ =
      ‖zetaT t‖ ^ (k + 1) * ∏ u ∈ X.tree.vtxs.toFinset, ob_W P β ℓ J R B μ lam g l X x u (a.1 u) := by
  classical
  have hroot_ty : X.ty [] ≠ VType.lat := by rw [X.root_ty]; exact X.root_ext
  have hroot : ([] : List ℕ) ∈ X.tree.vtxs.toFinset := by simpa using ob_pt_root_mem X.tree
  have key : ∏ u ∈ X.tree.vtxs.toFinset, ob_W P β ℓ J R B μ lam g l X x u (a.1 u) =
      ((if ([] : List ℕ) = [] then |asgVal μ lam (a.1 [])| ^ X.tree.degAt [] else 1) *
      (∏ u ∈ X.tree.vtxs.toFinset.filter (fun u => u ≠ [] ∧ X.ty u ≠ VType.lat),
        |asgVal μ lam (a.1 u) ^ X.tree.degAt u / (B : ℝ)|)) *
      (∏ u ∈ X.tree.vtxs.toFinset.filter (fun u => X.ty u = VType.lat),
        |∫ ω, (cutoffXi β ℓ J R l g (asgLabel (a.1 u)) ω) ^ X.tree.degAt u ∂P|) := by
    have hpt : ∀ u ∈ X.tree.vtxs.toFinset, ob_W P β ℓ J R B μ lam g l X x u (a.1 u) =
        ((if u = [] then |asgVal μ lam (a.1 u)| ^ X.tree.degAt u else 1) *
        (if (u ≠ [] ∧ X.ty u ≠ VType.lat) then |asgVal μ lam (a.1 u) ^ X.tree.degAt u / (B : ℝ)| else 1)) *
        (if X.ty u = VType.lat then
          |∫ ω, (cutoffXi β ℓ J R l g (asgLabel (a.1 u)) ω) ^ X.tree.degAt u ∂P| else 1) := by
      intro u hu
      have hu' : u ∈ X.tree.vtxs := by simpa using hu
      have hc := a.2.2 u hu'
      by_cases h0 : u = []
      · subst h0
        rw [ha] at hc
        simp [ob_W, hc, ha, hroot_ty]
      · by_cases hl : X.ty u = VType.lat
        · rw [hl] at hc
          simp [ob_W, hc, h0, hl]
        · simp [ob_W, hc, h0, hl]
    rw [Finset.prod_congr rfl hpt, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_ite_eq' _ _ (fun u => |asgVal μ lam (a.1 u)| ^ X.tree.degAt u), if_pos hroot,
      ← Finset.prod_filter, ← Finset.prod_filter]
    simp
  rw [key]
  unfold oneBufVal
  rw [norm_mul, norm_mul, norm_mul, norm_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs, norm_prod, abs_pow]
  simp only [if_true]
  ring

private theorem ob_asgVal_le {m n : ℕ} {L : Finset ℤ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hμ : ∀ i, |μ i| ≤ C) (hlam : ∀ j, |lam j| ≤ C) (o : Option (AsgLab m n L)) :
    |asgVal μ lam o| ≤ C := by
  rcases o with _ | (i | j | α)
  · simpa [asgVal] using hC
  · exact hμ i
  · exact hlam j
  · simpa [asgVal] using hC

private theorem ob_vertex_sum {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (ℓ J : ℕ) (R : ℝ) (B : ℕ) {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (g : ℤ → Ω → ℝ) (l : ℕ) (γ C : ℝ) (hγ : 1 ≤ γ) (hC : 1 ≤ C)
    (hμ : ∀ i, |μ i| ≤ C) (hlam : ∀ j, |lam j| ≤ C) (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B)
    {tr : VType} {k : ℕ} (X : RootedTypedTree tr k) (x : AsgLab m n (cutoffLabels J ℓ))
    (u : List ℕ) (hu : u ∈ X.tree.vtxs) :
    ∑ o, ob_W P β ℓ J R B μ lam g l X x u o ≤
      γ ^ (if u ≠ [] ∧ X.ty u ≠ VType.lat then 1 else 0) *
        C ^ (if X.ty u ≠ VType.lat then X.tree.degAt u else 0) *
        (max 1 R) ^ (if X.ty u = VType.lat then X.tree.degAt u else 0) := by
  classical
  have hroot_ty : X.ty [] ≠ VType.lat := by rw [X.root_ty]; exact X.root_ext
  have hC0 : 0 ≤ C := by linarith
  have hR1 : 1 ≤ max 1 R := le_max_left _ _
  by_cases h0 : u = []
  · subst h0
    simp only [ne_eq, not_true_eq_false, false_and, if_false, hroot_ty, not_false_eq_true, if_true,
      pow_zero, one_mul, mul_one]
    calc ∑ o, ob_W P β ℓ J R B μ lam g l X x [] o
        ≤ ∑ o : Option (AsgLab m n (cutoffLabels J ℓ)), (if o = some x then C ^ X.tree.degAt [] else 0) := by
          refine Finset.sum_le_sum fun o _ => ?_
          unfold ob_W
          by_cases hc : AsgCompat (X.ty []) o
          · simp only [hc, if_true]
            by_cases ho : o = some x
            · simp only [ho, if_true]
              exact pow_le_pow_left₀ (abs_nonneg _) (ob_asgVal_le μ lam C hC0 hμ hlam _) _
            · simp [ho]
          · simp only [hc, if_false]; split_ifs <;> positivity
      _ = C ^ X.tree.degAt [] := by simp
  · by_cases hl : X.ty u = VType.lat
    · have hdeg := (ob_deg_sums X).2.2.2 u hu hl
      simp only [h0, ne_eq, not_false_eq_true, true_and, hl, not_true_eq_false, if_false, if_true,
        pow_zero, one_mul]
      rw [ob_sum_opt]
      have e : ∑ α : {α : ℤ // α ∈ cutoffLabels J ℓ},
          ob_W P β ℓ J R B μ lam g l X x u (some (Sum.inr (Sum.inr α))) =
          ∑ α ∈ cutoffLabels J ℓ, |∫ ω, (cutoffXi β ℓ J R l g α ω) ^ X.tree.degAt u ∂P| := by
        rw [← Finset.sum_coe_sort (cutoffLabels J ℓ)
          (fun α => |∫ ω, (cutoffXi β ℓ J R l g α ω) ^ X.tree.degAt u ∂P|)]
        refine Finset.sum_congr rfl fun α _ => ?_
        simp [ob_W, hl, h0, AsgCompat, asgLabel]
      have z1 : ob_W P β ℓ J R B μ lam g l X x u none = 0 := by simp [ob_W, hl, AsgCompat]
      have z2 : ∀ i : Fin m, ob_W P β ℓ J R B μ lam g l X x u (some (Sum.inl i)) = 0 := by
        intro i; simp [ob_W, hl, AsgCompat]
      have z3 : ∀ j : Fin n, ob_W P β ℓ J R B μ lam g l X x u (some (Sum.inr (Sum.inl j))) = 0 := by
        intro j; simp [ob_W, hl, AsgCompat]
      rw [e, z1, Finset.sum_eq_zero (fun i _ => z2 i), Finset.sum_eq_zero (fun j _ => z3 j)]
      simp only [zero_add]
      exact ob_lat_bound P hβ ℓ J R g l _ hdeg
    · simp only [h0, ne_eq, not_false_eq_true, true_and, hl, if_false, if_true, pow_zero, mul_one, pow_one]
      rw [ob_sum_opt]
      have z1 : ob_W P β ℓ J R B μ lam g l X x u none = 0 := by
        cases hty : X.ty u <;> simp [ob_W, hty, AsgCompat]
      cases hty : X.ty u
      · have z3 : ∀ j : Fin n, ob_W P β ℓ J R B μ lam g l X x u (some (Sum.inr (Sum.inl j))) = 0 := by
          intro j; simp [ob_W, hty, AsgCompat]
        have z4 : ∀ α : {α : ℤ // α ∈ cutoffLabels J ℓ},
            ob_W P β ℓ J R B μ lam g l X x u (some (Sum.inr (Sum.inr α))) = 0 := by
          intro α; simp [ob_W, hty, AsgCompat]
        rw [z1, Finset.sum_eq_zero (fun j _ => z3 j), Finset.sum_eq_zero (fun j _ => z4 j)]
        simp only [zero_add, add_zero]
        have := ob_ext_sum (B := B) μ γ C hγ hC hμ hm (X.tree.degAt u)
        refine le_trans (le_of_eq ?_) this
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [ob_W, hty, h0, AsgCompat, asgVal]
      · have z3 : ∀ i : Fin m, ob_W P β ℓ J R B μ lam g l X x u (some (Sum.inl i)) = 0 := by
          intro i; simp [ob_W, hty, AsgCompat]
        have z4 : ∀ α : {α : ℤ // α ∈ cutoffLabels J ℓ},
            ob_W P β ℓ J R B μ lam g l X x u (some (Sum.inr (Sum.inr α))) = 0 := by
          intro α; simp [ob_W, hty, AsgCompat]
        rw [z1, Finset.sum_eq_zero (fun j _ => z3 j), Finset.sum_eq_zero (fun j _ => z4 j)]
        simp only [zero_add, add_zero]
        have := ob_ext_sum (B := B) lam γ C hγ hC hlam hn (X.tree.degAt u)
        refine le_trans (le_of_eq ?_) this
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [ob_W, hty, h0, AsgCompat, asgVal]
      · exact absurd hty hl

private theorem ob_finite_asg (P : PlaneTree) (ty : List ℕ → VType) (m n : ℕ) (L : Finset ℤ) :
    Finite (TreeAsg P ty m n L) := by
  classical
  refine Finite.of_injective
    (fun a : TreeAsg P ty m n L => fun u : {u // u ∈ P.vtxs.toFinset} => a.1 u.1) ?_
  intro a b h
  apply Subtype.ext
  funext u
  by_cases hu : u ∈ P.vtxs
  · exact congrFun h ⟨u, by simpa using hu⟩
  · have ha : a.1 u = none := by
      by_contra hne; exact hu ((a.2.1 u).mpr hne)
    have hb : b.1 u = none := by
      by_contra hne; exact hu ((b.2.1 u).mpr hne)
    rw [ha, hb]

private theorem ob_tree_bound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (ℓ J : ℕ) (R : ℝ) (B : ℕ) {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (g : ℤ → Ω → ℝ) (l : ℕ) (t : ℝ) (γ C : ℝ) (hγ : 1 ≤ γ) (hC : 1 ≤ C)
    (hμ : ∀ i, |μ i| ≤ C) (hlam : ∀ j, |lam j| ≤ C) (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B)
    {tr : VType} {k : ℕ} (X : RootedTypedTree tr k) (x : AsgLab m n (cutoffLabels J ℓ)) :
    ∑' a : {a : TreeAsg X.tree X.ty m n (cutoffLabels J ℓ) // a.1 [] = some x},
      ‖oneBufVal P β ℓ J R B μ lam g l t X a.1‖ ≤ ‖zetaT t‖ ^ (k + 1) * (γ * C * max 1 R) ^ k := by
  classical
  haveI : Finite (TreeAsg X.tree X.ty m n (cutoffLabels J ℓ)) := ob_finite_asg _ _ _ _ _
  haveI : Fintype {a : TreeAsg X.tree X.ty m n (cutoffLabels J ℓ) // a.1 [] = some x} :=
    Fintype.ofFinite _
  set V := X.tree.vtxs.toFinset with hV
  have hR1 : 1 ≤ max 1 R := le_max_left _ _
  let ι : {a : TreeAsg X.tree X.ty m n (cutoffLabels J ℓ) // a.1 [] = some x} →
      ({u // u ∈ V} → Option (AsgLab m n (cutoffLabels J ℓ))) := fun a u => a.1.1 u.1
  have hι : Function.Injective ι := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    funext u
    by_cases hu : u ∈ X.tree.vtxs
    · exact congrFun h ⟨u, by simpa [hV] using hu⟩
    · have ha : a.1.1 u = none := by
        by_contra hne; exact hu ((a.1.2.1 u).mpr hne)
      have hb : b.1.1 u = none := by
        by_contra hne; exact hu ((b.1.2.1 u).mpr hne)
      rw [ha, hb]
  rw [tsum_fintype]
  have h1 : ∑ a : {a : TreeAsg X.tree X.ty m n (cutoffLabels J ℓ) // a.1 [] = some x},
      ‖oneBufVal P β ℓ J R B μ lam g l t X a.1‖ =
      ‖zetaT t‖ ^ (k + 1) * ∑ a, ∏ u : {u // u ∈ V}, ob_W P β ℓ J R B μ lam g l X x u.1 (ι a u) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ob_val_norm P β ℓ J R B μ lam g l t X x a.1 a.2,
      ← Finset.prod_coe_sort V (fun u => ob_W P β ℓ J R B μ lam g l X x u (a.1.1 u))]
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  let bnd : List ℕ → ℝ := fun u =>
    γ ^ (if u ≠ [] ∧ X.ty u ≠ VType.lat then 1 else 0) *
        C ^ (if X.ty u ≠ VType.lat then X.tree.degAt u else 0) *
        (max 1 R) ^ (if X.ty u = VType.lat then X.tree.degAt u else 0)
  calc ∑ a, ∏ u : {u // u ∈ V}, ob_W P β ℓ J R B μ lam g l X x u.1 (ι a u)
      = ∑ φ ∈ Finset.univ.image ι, ∏ u : {u // u ∈ V}, ob_W P β ℓ J R B μ lam g l X x u.1 (φ u) := by
        rw [Finset.sum_image (fun a _ b _ h => hι h)]
    _ ≤ ∑ φ : ({u // u ∈ V} → Option (AsgLab m n (cutoffLabels J ℓ))),
          ∏ u : {u // u ∈ V}, ob_W P β ℓ J R B μ lam g l X x u.1 (φ u) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun φ _ _ => ?_
        exact Finset.prod_nonneg fun u _ => ob_W_nonneg P β ℓ J R B μ lam g l X x u.1 _
    _ = ∏ u : {u // u ∈ V}, ∑ o, ob_W P β ℓ J R B μ lam g l X x u.1 o := by
        rw [Finset.prod_univ_sum]
        simp [Fintype.piFinset_univ]
    _ ≤ ∏ u : {u // u ∈ V}, bnd u.1 := by
        refine Finset.prod_le_prod₀ (fun u _ => Finset.sum_nonneg fun o _ =>
          ob_W_nonneg P β ℓ J R B μ lam g l X x u.1 o) (fun u _ => ?_)
        exact ob_vertex_sum P hβ ℓ J R B μ lam g l γ C hγ hC hμ hlam hm hn X x u.1 (List.mem_toFinset.mp u.2)
    _ = ∏ u ∈ V, bnd u := Finset.prod_coe_sort V bnd
    _ ≤ (γ * C * max 1 R) ^ k := by
        obtain ⟨hs1, hs2, hs3, -⟩ := ob_deg_sums X
        have e1 : ∏ u ∈ V, γ ^ (if u ≠ [] ∧ X.ty u ≠ VType.lat then 1 else 0) =
            γ ^ (V.filter (fun u => u ≠ [] ∧ X.ty u ≠ VType.lat)).card := by
          rw [Finset.prod_pow_eq_pow_sum, Finset.card_filter]
        have e2 : ∏ u ∈ V, C ^ (if X.ty u ≠ VType.lat then X.tree.degAt u else 0) = C ^ k := by
          rw [Finset.prod_pow_eq_pow_sum, ← Finset.sum_filter, hs1]
        have e3 : ∏ u ∈ V, (max 1 R) ^ (if X.ty u = VType.lat then X.tree.degAt u else 0) =
            (max 1 R) ^ k := by
          rw [Finset.prod_pow_eq_pow_sum, ← Finset.sum_filter, hs2]
        change ∏ u ∈ V, (γ ^ _ * C ^ _ * (max 1 R) ^ _) ≤ _
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, e1, e2, e3, mul_pow, mul_pow]
        gcongr

private theorem ob_zeta_norm {t : ℝ} (ht : 0 < t) : ‖zetaT t‖ = (Real.sqrt t)⁻¹ := by
  unfold zetaT
  have : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  rw [norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos this]

private theorem ob_main {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (ℓ J : ℕ) (R : ℝ) (B : ℕ) {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (g : ℤ → Ω → ℝ) (l : ℕ) (t : ℝ) (γ C : ℝ) (hγ : 1 ≤ γ) (hC : 1 ≤ C)
    (hμ : ∀ i, |μ i| ≤ C) (hlam : ∀ j, |lam j| ≤ C) (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B)
    (ht : 64 * (γ * C * max 1 R) ^ 2 ≤ t) (tr : VType) (x : AsgLab m n (cutoffLabels J ℓ)) :
    Summable (fun q : OneBufIdx m n J ℓ tr x => ‖oneBufVal P β ℓ J R B μ lam g l t q.2.1 q.2.2.1‖) ∧
    ∑' q : OneBufIdx m n J ℓ tr x, ‖oneBufVal P β ℓ J R B μ lam g l t q.2.1 q.2.2.1‖ ≤
      2 / Real.sqrt t := by
  classical
  set K := γ * C * max 1 R with hKdef
  have hR1 : 1 ≤ max 1 R := le_max_left _ _
  have hK1 : 1 ≤ K := by
    have : 1 ≤ γ * C := by nlinarith
    nlinarith
  have htpos : 0 < t := by nlinarith
  set s := Real.sqrt t with hsdef
  have hs8 : 8 * K ≤ s := by
    rw [hsdef]; apply Real.le_sqrt_of_sq_le; nlinarith
  have hspos : 0 < s := by linarith
  have hz : ‖zetaT t‖ = s⁻¹ := ob_zeta_norm htpos
  obtain ⟨f, hfdef⟩ : ∃ f : OneBufIdx m n J ℓ tr x → ℝ,
      f = fun q => ‖oneBufVal P β ℓ J R B μ lam g l t q.2.1 q.2.2.1‖ := ⟨_, rfl⟩
  rw [← hfdef]
  have hf0 : ∀ q, 0 ≤ f q := fun q => by rw [hfdef]; exact norm_nonneg _
  -- inner sums
  have hfin : ∀ k, Finite (Σ X : RootedTypedTree tr k,
      {a : TreeAsg X.tree X.ty m n (cutoffLabels J ℓ) // a.1 [] = some x}) := by
    intro k
    haveI := (ob_card_rooted tr k).1
    haveI : ∀ X : RootedTypedTree tr k, Finite
        {a : TreeAsg X.tree X.ty m n (cutoffLabels J ℓ) // a.1 [] = some x} := fun X => by
      haveI := ob_finite_asg X.tree X.ty m n (cutoffLabels J ℓ)
      infer_instance
    infer_instance
  have hinner : ∀ k, ∑' p : (Σ X : RootedTypedTree tr k,
      {a : TreeAsg X.tree X.ty m n (cutoffLabels J ℓ) // a.1 [] = some x}), f ⟨k, p⟩ ≤
        s⁻¹ * (1 / 2) ^ k := by
    intro k
    haveI := hfin k
    haveI := (ob_card_rooted tr k).1
    have hb : ∀ X : RootedTypedTree tr k,
        ∑' a : {a : TreeAsg X.tree X.ty m n (cutoffLabels J ℓ) // a.1 [] = some x}, f ⟨k, ⟨X, a⟩⟩ ≤
          s⁻¹ ^ (k + 1) * K ^ k := by
      intro X
      have := ob_tree_bound P hβ ℓ J R B μ lam g l t γ C hγ hC hμ hlam hm hn X x
      rw [hz] at this
      refine le_trans (le_of_eq (tsum_congr fun a => ?_)) this
      rw [hfdef]
    have hsum : ∀ X : RootedTypedTree tr k, Summable
        (fun a : {a : TreeAsg X.tree X.ty m n (cutoffLabels J ℓ) // a.1 [] = some x} => f ⟨k, ⟨X, a⟩⟩) := by
      intro X
      haveI := ob_finite_asg X.tree X.ty m n (cutoffLabels J ℓ)
      exact Summable.of_finite
    have hSig : Summable (fun p : (Σ X : RootedTypedTree tr k,
        {a : TreeAsg X.tree X.ty m n (cutoffLabels J ℓ) // a.1 [] = some x}) => f ⟨k, p⟩) :=
      Summable.of_finite
    rw [Summable.tsum_sigma' (fun X => (hsum X)) hSig]
    letI : Fintype (RootedTypedTree tr k) := Fintype.ofFinite _
    rw [tsum_fintype]
    calc ∑ X : RootedTypedTree tr k, ∑' a : {a : TreeAsg X.tree X.ty m n (cutoffLabels J ℓ) // a.1 [] = some x}, f ⟨k, ⟨X, a⟩⟩
        ≤ ∑ X : RootedTypedTree tr k, s⁻¹ ^ (k + 1) * K ^ k := Finset.sum_le_sum fun X _ => hb X
      _ = (Nat.card (RootedTypedTree tr k) : ℝ) * (s⁻¹ ^ (k + 1) * K ^ k) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
      _ ≤ (4 : ℝ) ^ k * (s⁻¹ ^ (k + 1) * K ^ k) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast (ob_card_rooted tr k).2
      _ = s⁻¹ * (4 * K * s⁻¹) ^ k := by rw [mul_pow, mul_pow, pow_succ]; ring
      _ ≤ s⁻¹ * (1 / 2) ^ k := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ k) (by positivity)
          rw [← div_eq_mul_inv, div_le_iff₀ hspos]; linarith
  have hsumk : Summable (fun k : ℕ => ∑' p : (Σ X : RootedTypedTree tr k,
      {a : TreeAsg X.tree X.ty m n (cutoffLabels J ℓ) // a.1 [] = some x}), f ⟨k, p⟩) := by
    refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun p => hf0 _) hinner ?_
    exact (summable_geometric_two).mul_left _
  have hsumf : Summable f := by
    rw [summable_sigma_of_nonneg hf0]
    refine ⟨fun k => ?_, hsumk⟩
    haveI := hfin k
    exact Summable.of_finite
  refine ⟨hsumf, ?_⟩
  rw [Summable.tsum_sigma' (fun k => by haveI := hfin k; exact Summable.of_finite) hsumf]
  calc ∑' k : ℕ, ∑' p : (Σ X : RootedTypedTree tr k,
      {a : TreeAsg X.tree X.ty m n (cutoffLabels J ℓ) // a.1 [] = some x}), f ⟨k, p⟩
      ≤ ∑' k : ℕ, s⁻¹ * (1 / 2) ^ k := Summable.tsum_le_tsum hinner hsumk ((summable_geometric_two).mul_left _)
    _ = 2 / s := by
        rw [tsum_mul_left, tsum_geometric_two]; field_simp

/-- `lem:app-vol-closed-onebuffer`(i), snapshot `cr-2026-10-23`. Declaration of record, absolute summability
and the bound `2/√t`. Hypotheses: `SizeFin` (standing size condition), `Σ_out, Σ_in ≠ 0`, the cutoff
Gaussians `g` (a standard independent family), `l ∈ {1,2}`, and `t ≥ s_R`.

LaTeX (`sections/04-volatility/section.tex` l.2234–2248, verbatim):
```latex
\begin{lemma}[One-buffer sums are the branch]\label{lem:app-vol-closed-onebuffer}
Let $\Sigmaout,\Sigmain\ne0$, fix $l\in\{1,2\}$ and $t\ge s_R$, use the corner weight
$\zeta_l=(i\sqrt t)^{-1}$, and let $(\sigma_l,\tilde\sigma_l,\tilde s_{1,l},s_{1,l})$ be the branch
point of the marginal profile $\xi_l$ at $t$, with $q_l=t\sigma_l\tilde\sigma_l$. Then the
families defining $g_{\mathsf t,l}$ are absolutely summable,
\[
\sum_X\sum_{\mathfrak a:\mathfrak a(\mathrm{root})=i}\abs{\operatorname{val}_l(X,\mathfrak a)}\le\frac2{\sqrt t},
\]
and
\[
g_{\mathrm o,l}(i)=\frac{-i\sqrt t}{t+\tilde s_{1,l}\mu_i},\qquad g_{\mathrm{in},l}(j)=\frac{-i\sqrt t}{t+s_{1,l}\lambda_j},\qquad
m_{\mathrm o,l}=-i\sqrt t\,\sigma_l,\qquad m_{\mathrm{in},l}=-i\sqrt t\,\tilde\sigma_l,
\]
so that $-m_{\mathrm o,l}m_{\mathrm{in},l}=q_l$.
\end{lemma}
```
-/
theorem lem_app_vol_closed_onebuffer_i {Ω : Type} [MeasurableSpace Ω] {m n B : ℕ}
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) (Fp : FrozenParams m n B)
    (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hout : Fp.C.Sout ≠ 0) (hin : Fp.C.Sin ≠ 0)
    {P : Measure Ω} [IsProbabilityMeasure P] (ℓ J : ℕ) (R : ℝ)
    {g : ℤ → Ω → ℝ} (hg : IsStdGaussianFamily P g) (l : ℕ) (hl : l = 1 ∨ l = 2)
    (t : ℝ) (ht : sRad cert γstar CSig R ≤ t) :
    (∀ i : Fin m,
      Summable (fun q : OneBufIdx m n J ℓ VType.out (Sum.inl i) =>
        ‖oneBufVal P Fp.β ℓ J R B S.μ S.lam g l t q.2.1 q.2.2.1‖) ∧
      ∑' q : OneBufIdx m n J ℓ VType.out (Sum.inl i),
        ‖oneBufVal P Fp.β ℓ J R B S.μ S.lam g l t q.2.1 q.2.2.1‖ ≤ 2 / Real.sqrt t) ∧
    (∀ j : Fin n,
      Summable (fun q : OneBufIdx m n J ℓ VType.inp (Sum.inr (Sum.inl j)) =>
        ‖oneBufVal P Fp.β ℓ J R B S.μ S.lam g l t q.2.1 q.2.2.1‖) ∧
      ∑' q : OneBufIdx m n J ℓ VType.inp (Sum.inr (Sum.inl j)),
        ‖oneBufVal P Fp.β ℓ J R B S.μ S.lam g l t q.2.1 q.2.2.1‖ ≤ 2 / Real.sqrt t) := by
  classical
  obtain ⟨hS1, hS2, hS3⟩ := hS
  have hγ : 1 ≤ max 1 γstar := le_max_left _ _
  have hC : 1 ≤ max 1 CSig := le_max_left _ _
  have hμ : ∀ i, |S.μ i| ≤ max 1 CSig := fun i =>
    (ob_abs_eig_le Fp.C.Sout S.uOut (S.μ i) i S.huOut (S.eigOut i)).trans (hS2.trans (le_max_right _ _))
  have hlam : ∀ j, |S.lam j| ≤ max 1 CSig := fun j =>
    (ob_abs_eig_le Fp.C.Sin S.vIn (S.lam j) j S.hvIn (S.eigIn j)).trans (hS3.trans (le_max_right _ _))
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hmn : ∀ q : ℕ, q ≤ max m n → (q : ℝ) ≤ max 1 γstar * B := fun q hq =>
    ((Nat.cast_le.mpr hq).trans hS1).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hB)
  have ht' : 64 * (max 1 γstar * max 1 CSig * max 1 R) ^ 2 ≤ t := by
    refine le_trans ?_ ht
    unfold sRad
    refine le_trans (le_of_eq ?_) (le_max_left _ _)
    ring
  exact ⟨fun i => ob_main P Fp.hβ ℓ J R B S.μ S.lam g l t (max 1 γstar) (max 1 CSig) hγ hC hμ hlam
      (hmn m (le_max_left _ _)) (hmn n (le_max_right _ _)) ht' VType.out (Sum.inl i),
    fun j => ob_main P Fp.hβ ℓ J R B S.μ S.lam g l t (max 1 γstar) (max 1 CSig) hγ hC hμ hlam
      (hmn m (le_max_left _ _)) (hmn n (le_max_right _ _)) ht' VType.inp (Sum.inr (Sum.inl j))⟩

private lemma ob_ext_swap {a b : VType} (ha : a ≠ VType.lat)
    (hb : b ≠ VType.lat) (hab : a ≠ b) : b = ob_f0 a := by
  cases a <;> cases b <;> simp_all [ob_f0]

private lemma ob_cyclicAlt_get (s : List VType) (hs : CyclicAlt s) :
    ∀ j, j < s.length →
      s.getD j VType.lat =
        if j % 2 = 0 then s.getD 0 VType.lat else ob_f0 (s.getD 0 VType.lat) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hj' : j < s.length := by omega
    have hnext := (hs j hj').2
    rw [Nat.mod_eq_of_lt hj] at hnext
    have he := ob_ext_swap (hs j hj').1 (hs (j + 1) hj).1 hnext
    rw [he, ih hj']
    have hzero := (hs 0 (by omega)).1
    by_cases hpar : j % 2 = 0
    · have hp : (j + 1) % 2 ≠ 0 := by omega
      simp [hpar, hp]
    · have hp : (j + 1) % 2 = 0 := by omega
      simp only [hpar, ite_false, hp, ite_true]
      cases h : s.getD 0 VType.lat <;> simp_all [ob_f0]

private lemma ob_cyclicAlt_length (s : List VType) (hs : CyclicAlt s)
    (hne : 0 < s.length) : ∃ p : ℕ, s.length = 2 * p + 2 := by
  have heven : s.length % 2 = 0 := by
    by_contra hodd
    have hlast : s.length - 1 < s.length := by omega
    have hpar : (s.length - 1) % 2 = 0 := by omega
    have h := (hs (s.length - 1) hlast).2
    rw [show s.length - 1 + 1 = s.length by omega, Nat.mod_self,
      ob_cyclicAlt_get s hs _ hlast, if_pos hpar] at h
    exact h rfl
  exact ⟨s.length / 2 - 1, by omega⟩

private lemma ob_latent_children {tr : VType} {k : ℕ} (X : RootedTypedTree tr k)
    (u : List ℕ) (hu : u ∈ X.tree.vtxs) (hne : u ≠ []) (hlat : X.ty u = VType.lat) :
    ∃ p : ℕ, X.tree.childCount u = 2 * p + 1 ∧ X.tree.degAt u = 2 * p + 2 ∧
      ∀ j, j < X.tree.childCount u →
        X.ty (u ++ [j]) = if j % 2 = 0 then ob_f0 (X.ty u.dropLast) else X.ty u.dropLast := by
  let s := X.ty u.dropLast :: (List.range (X.tree.childCount u)).map
    (fun j => X.ty (u ++ [j]))
  have hs : CyclicAlt s := X.latent_alt u hu hne hlat
  obtain ⟨p, hp⟩ := ob_cyclicAlt_length s hs (by simp [s])
  have hcount : X.tree.childCount u = 2 * p + 1 := by
    simp only [s, List.length_cons, List.length_map, List.length_range] at hp
    omega
  refine ⟨p, hcount, ?_, ?_⟩
  · simp only [PlaneTree.degAt, hne, ite_false, hcount]
  · intro j hj
    have hget := ob_cyclicAlt_get s hs (j + 1) (by simpa [s] using hj)
    have he : s.getD (j + 1) VType.lat = X.ty (u ++ [j]) := by
      simp only [s, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
        List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.getD_some]
    rw [he] at hget
    simp only [s, List.getD_cons_zero] at hget
    by_cases hpar : j % 2 = 0
    · simpa only [hpar, ite_true, show (j + 1) % 2 ≠ 0 by omega, ite_false] using hget
    · simpa only [hpar, ite_false, show (j + 1) % 2 = 0 by omega, ite_true] using hget

private lemma ob_pt_cc_root (cs : List PlaneTree) :
    (PlaneTree.node cs).childCount [] = cs.length := by
  have hiff : ∀ i, i < (PlaneTree.node cs).childCount [] ↔ i < cs.length := by
    intro i
    have h := ob_pt_childCount_iff (PlaneTree.node cs) [] i
    rw [List.nil_append, ob_pt_mem_idx] at h
    exact ⟨fun hi => (h.mpr ⟨ob_pt_root_mem _, hi⟩).choose,
      fun hi => (h.mp ⟨hi, ob_pt_root_mem _⟩).2⟩
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := (hiff _).mpr h; omega
  · have := (hiff _).mp h; omega

private lemma ob_pt_cc_idx (cs : List PlaneTree) (a : ℕ) (ha : a < cs.length)
    (u : List ℕ) (hu : u ∈ (cs[a]).vtxs) :
    (PlaneTree.node cs).childCount (a :: u) = (cs[a]).childCount u := by
  have hiff : ∀ i, i < (PlaneTree.node cs).childCount (a :: u) ↔
      i < (cs[a]).childCount u := by
    intro i
    have hmem : a :: u ∈ (PlaneTree.node cs).vtxs := (ob_pt_mem_idx cs a u).mpr ⟨ha, hu⟩
    have h := ob_pt_childCount_iff (PlaneTree.node cs) (a :: u) i
    rw [List.cons_append, ob_pt_mem_idx] at h
    exact ⟨fun hi => (ob_pt_childCount_iff _ u i).mp (h.mpr ⟨hmem, hi⟩).choose_spec |>.2,
      fun hi => (h.mp ⟨ha, (ob_pt_childCount_iff _ u i).mpr ⟨hu, hi⟩⟩).2⟩
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := (hiff _).mpr h; omega
  · have := (hiff _).mp h; omega

/-- Restrict a plane tree to the descendants of a vertex, preserving its child counts. -/
private lemma ob_pt_subtree (u : List ℕ) (P : PlaneTree) (hu : u ∈ P.vtxs) :
    ∃ Q : PlaneTree,
      (∀ v, v ∈ Q.vtxs ↔ u ++ v ∈ P.vtxs) ∧
      (∀ v ∈ Q.vtxs, Q.childCount v = P.childCount (u ++ v)) := by
  induction u generalizing P with
  | nil => exact ⟨P, by simp⟩
  | cons a u ih =>
    cases P with
    | node cs =>
      obtain ⟨ha, hu⟩ := (ob_pt_mem_idx cs a u).mp hu
      obtain ⟨Q, hQ, hc⟩ := ih (cs[a]) hu
      refine ⟨Q, ?_, ?_⟩
      · intro v
        rw [List.cons_append, ob_pt_mem_idx]
        exact (hQ v).trans ⟨fun h => ⟨ha, h⟩, fun h => h.choose_spec⟩
      · intro v hv
        rw [List.cons_append, ob_pt_cc_idx cs a ha _ ((hQ v).mp hv)]
        exact hc v hv

private lemma ob_pt_ext (P Q : PlaneTree)
    (hmem : ∀ u, u ∈ P.vtxs ↔ u ∈ Q.vtxs) : P = Q := by
  revert Q
  refine ob_plane_ind (fun P => ∀ Q, (∀ u, u ∈ P.vtxs ↔ u ∈ Q.vtxs) → P = Q) ?_ ?_ P
  · intro Q hQ
    cases Q with
    | node cs =>
      cases cs with
      | nil => rfl
      | cons Q1 cs =>
        have h : [0] ∈ (PlaneTree.node (Q1 :: cs)).vtxs :=
          ob_mem_cons0.mpr (ob_pt_root_mem Q1)
        have := (hQ [0]).mpr h
        simp only [PlaneTree.vtxs, vtxsForest, List.mem_singleton, List.cons_ne_self] at this
  · intro P1 cs ih1 ih2 Q hQ
    cases Q with
    | node ds =>
      cases ds with
      | nil =>
        have h : [0] ∈ (PlaneTree.node (P1 :: cs)).vtxs :=
          ob_mem_cons0.mpr (ob_pt_root_mem P1)
        have := (hQ [0]).mp h
        simp only [PlaneTree.vtxs, vtxsForest, List.mem_singleton, List.cons_ne_self] at this
      | cons Q1 ds =>
        have h1 : P1 = Q1 := ih1 Q1 fun u => by
          simpa only [ob_mem_cons0] using hQ (0 :: u)
        have h2 : PlaneTree.node cs = PlaneTree.node ds := ih2 _ fun u => by
          simpa only [ob_mem_inc] using hQ (ob_inc u)
        cases h2
        rw [h1]

/-- A rooted typed tree is determined by its plane tree and its typing on the support. -/
private lemma ob_rooted_ext {tr : VType} {k : ℕ} (X Y : RootedTypedTree tr k)
    (htree : X.tree = Y.tree)
    (hty : ∀ u ∈ X.tree.vtxs, X.ty u = Y.ty u) : X = Y := by
  cases X with
  | mk PX tyX cardX offX rootX extX edgeX altX =>
    cases Y with
    | mk PY tyY cardY offY rootY extY edgeY altY =>
      dsimp only at htree
      subst PY
      have hty' : tyX = tyY := by
        funext u
        by_cases hu : u ∈ PX.vtxs
        · exact hty u hu
        · rw [offX u hu, offY u hu]
      subst tyY
      rfl

/-- An assignment is determined by its values on the vertex set. -/
private lemma ob_asg_ext {m n : ℕ} {L : Finset ℤ} (P : PlaneTree)
    (ty : List ℕ → VType) (a b : TreeAsg P ty m n L)
    (h : ∀ u ∈ P.vtxs, a.1 u = b.1 u) : a = b := by
  apply Subtype.ext
  funext u
  by_cases hu : u ∈ P.vtxs
  · exact h u hu
  · have ha : a.1 u = none := not_ne_iff.mp (not_congr (a.2.1 u) |>.mp hu)
    have hb : b.1 u = none := not_ne_iff.mp (not_congr (b.2.1 u) |>.mp hu)
    rw [ha, hb]

/-- Each child of the external root is latent and has an odd alternating list of children. -/
private lemma ob_root_children {tr : VType} {k : ℕ} (X : RootedTypedTree tr k)
    (r : ℕ) (hr : r < X.tree.childCount []) :
    X.ty [r] = VType.lat ∧
      ∃ p : ℕ, X.tree.childCount [r] = 2 * p + 1 ∧ X.tree.degAt [r] = 2 * p + 2 ∧
        ∀ j, j < X.tree.childCount [r] →
          X.ty [r, j] = if j % 2 = 0 then ob_f0 tr else tr := by
  have hm : [r] ∈ X.tree.vtxs := (ob_pt_childCount_iff X.tree [] r).mpr
    ⟨ob_pt_root_mem _, hr⟩
  have hlat : X.ty [r] = VType.lat := by
    by_contra h
    have he := X.edge_joins [] (ob_pt_root_mem _) [r] hm (by simp) (by simp)
    exact X.root_ext (X.root_ty ▸ he.mpr h)
  refine ⟨hlat, ?_⟩
  simpa only [List.dropLast_singleton, List.singleton_append, X.root_ty] using
    ob_latent_children X [r] hm (by simp) hlat

/-- An external descendant, with its inherited typing, is again an externally rooted typed tree. -/
private lemma ob_rooted_subtree {tr : VType} {k : ℕ} (X : RootedTypedTree tr k)
    (u : List ℕ) (hu : u ∈ X.tree.vtxs) (hext : X.ty u ≠ VType.lat) :
    ∃ (r : ℕ) (Y : RootedTypedTree (X.ty u) r),
      (∀ v, v ∈ Y.tree.vtxs ↔ u ++ v ∈ X.tree.vtxs) ∧
      (∀ v ∈ Y.tree.vtxs, Y.ty v = X.ty (u ++ v)) ∧
      (∀ v ∈ Y.tree.vtxs, Y.tree.childCount v = X.tree.childCount (u ++ v)) := by
  classical
  obtain ⟨Q, hQ, hc⟩ := ob_pt_subtree u X.tree hu
  let ty := fun v => if v ∈ Q.vtxs then X.ty (u ++ v) else VType.out
  have hty : ∀ v ∈ Q.vtxs, ty v = X.ty (u ++ v) := by
    intro v hv; exact if_pos hv
  let Y : RootedTypedTree (X.ty u) (Q.vtxs.length - 1) := {
    tree := Q
    ty := ty
    card_vtx := by have := ob_pt_vtxs_pos Q; omega
    off_support := by intro v hv; exact if_neg hv
    root_ty := by simpa only [List.append_nil] using hty [] (ob_pt_root_mem Q)
    root_ext := hext
    edge_joins := by
      intro v hv w hw hwne hd
      rw [hty v hv, hty w hw]
      apply X.edge_joins _ ((hQ v).mp hv) _ ((hQ w).mp hw)
      · intro h; exact hwne (List.eq_nil_of_append_eq_nil h).2
      · rw [List.dropLast_append_of_ne_nil hwne, hd]
    latent_alt := by
      intro v hv hvne hlat
      have hv' := (hQ v).mp hv
      have hvp : v.dropLast ∈ Q.vtxs := ob_parent_mem Q hv hvne
      have hne : u ++ v ≠ [] := by
        intro h; exact hvne (List.eq_nil_of_append_eq_nil h).2
      have hlat' : X.ty (u ++ v) = VType.lat := (hty v hv).symm.trans hlat
      have halt := X.latent_alt (u ++ v) hv' hne hlat'
      have hlist : ty v.dropLast :: (List.range (Q.childCount v)).map (fun i => ty (v ++ [i])) =
          X.ty (u ++ v).dropLast :: (List.range (X.tree.childCount (u ++ v))).map
            (fun i => X.ty ((u ++ v) ++ [i])) := by
        rw [List.dropLast_append_of_ne_nil hvne, hty _ hvp, hc v hv]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hi' : i < Q.childCount v := by simpa only [List.mem_range, hc v hv] using hi
        rw [hty _ ((ob_pt_childCount_iff Q v i).mpr ⟨hv, hi'⟩), List.append_assoc]
      rw [hlist]
      exact halt }
  exact ⟨Q.vtxs.length - 1, Y, hQ, hty, hc⟩

/-- Assignments restrict without any extra choice once the subtree has been extracted. -/
private lemma ob_asg_subtree {tr tr' : VType} {k r m n : ℕ} {L : Finset ℤ}
    (X : RootedTypedTree tr k) (Y : RootedTypedTree tr' r) (u : List ℕ)
    (hmem : ∀ v, v ∈ Y.tree.vtxs ↔ u ++ v ∈ X.tree.vtxs)
    (hty : ∀ v ∈ Y.tree.vtxs, Y.ty v = X.ty (u ++ v))
    (a : TreeAsg X.tree X.ty m n L) :
    ∃ b : TreeAsg Y.tree Y.ty m n L, ∀ v, b.1 v = a.1 (u ++ v) := by
  refine ⟨⟨fun v => a.1 (u ++ v), ?_, ?_⟩, fun _ => rfl⟩
  · intro v; exact (hmem v).trans (a.2.1 (u ++ v))
  · intro v hv
    rw [hty v hv]
    exact a.2.2 _ ((hmem v).mp hv)

private lemma ob_compat_ne_none {m n : ℕ} {L : Finset ℤ} {tr : VType}
    {o : Option (AsgLab m n L)} (ho : AsgCompat tr o) : o ≠ none := by
  intro h; subst h; cases tr <;> exact ho

open Classical in
/-- Finite Fubini for the assignments of a fixed tree, including the prescribed root label. -/
private lemma ob_asg_prod_sum {m n : ℕ} {L : Finset ℤ} (P : PlaneTree)
    (ty : List ℕ → VType) (x : AsgLab m n L)
    (W : List ℕ → Option (AsgLab m n L) → ℂ) :
    (∑' a : {a : TreeAsg P ty m n L // a.1 [] = some x},
      ∏ u ∈ P.vtxs.toFinset, W u (a.1.1 u)) =
      ∏ u : {u // u ∈ P.vtxs.toFinset},
        ∑ o : {o : Option (AsgLab m n L) //
          AsgCompat (ty u.1) o ∧ (u.1 = [] → o = some x)}, W u.1 o.1 := by
  classical
  let V := {u // u ∈ P.vtxs.toFinset}
  let D := fun u : V => {o : Option (AsgLab m n L) //
    AsgCompat (ty u.1) o ∧ (u.1 = [] → o = some x)}
  haveI : Finite (TreeAsg P ty m n L) := ob_finite_asg _ _ _ _ _
  letI : Fintype {a : TreeAsg P ty m n L // a.1 [] = some x} := Fintype.ofFinite _
  let e : {a : TreeAsg P ty m n L // a.1 [] = some x} ≃ ((u : V) → D u) := {
    toFun := fun a u => ⟨a.1.1 u.1, a.1.2.2 _ (List.mem_toFinset.mp u.2), by
      intro hu; simpa only [hu] using a.2⟩
    invFun := fun f => ⟨⟨fun u => if hu : u ∈ P.vtxs.toFinset then (f ⟨u, hu⟩).1 else none,
      by
        intro u
        dsimp only
        by_cases hu : u ∈ P.vtxs.toFinset
        · rw [dif_pos hu]
          exact iff_of_true (List.mem_toFinset.mp hu) (ob_compat_ne_none (f ⟨u, hu⟩).2.1)
        · simp only [dif_neg hu, ne_eq, not_true_eq_false, iff_false]
          simpa only [List.mem_toFinset] using hu,
      by
        intro u hu
        have hu' : u ∈ P.vtxs.toFinset := List.mem_toFinset.mpr hu
        simpa only [dif_pos hu'] using (f ⟨u, hu'⟩).2.1⟩, by
      have hr : ([] : List ℕ) ∈ P.vtxs.toFinset := List.mem_toFinset.mpr (ob_pt_root_mem P)
      simpa only [dif_pos hr] using (f ⟨[], hr⟩).2.2 rfl⟩
    left_inv := by
      intro a
      apply Subtype.ext
      apply Subtype.ext
      funext u
      dsimp only
      by_cases hu : u ∈ P.vtxs.toFinset
      · exact dif_pos hu
      · rw [dif_neg hu]
        symm
        by_contra h
        exact hu (List.mem_toFinset.mpr ((a.1.2.1 u).mpr h))
    right_inv := by
      intro f
      funext u
      apply Subtype.ext
      exact dif_pos u.2 }
  rw [tsum_fintype]
  calc ∑ a : {a : TreeAsg P ty m n L // a.1 [] = some x},
        ∏ u ∈ P.vtxs.toFinset, W u (a.1.1 u) =
      ∑ f : ((u : V) → D u), ∏ u : V, W u.1 (f u).1 := by
        apply Fintype.sum_equiv e
        intro a
        exact (Finset.prod_coe_sort P.vtxs.toFinset (fun u => W u (a.1.1 u))).symm
    _ = _ := (Fintype.prod_sum (fun (u : V) (o : D u) => W u.1 o.1)).symm

/-- The signed one-buffer weight as a product of independent vertex weights. -/
private lemma ob_val_prod {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) {m n : ℕ} (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (g : ℤ → Ω → ℝ) (l : ℕ) (t : ℝ)
    {tr : VType} {k : ℕ} (X : RootedTypedTree tr k)
    (a : TreeAsg X.tree X.ty m n (cutoffLabels J ℓ)) :
    oneBufVal P β ℓ J R B μ lam g l t X a = zetaT t ^ (k + 1) *
      ∏ u ∈ X.tree.vtxs.toFinset,
        if u = [] then ((asgVal μ lam (a.1 u) ^ X.tree.degAt u : ℝ) : ℂ)
        else if X.ty u = VType.lat then
          ((∫ ω, cutoffXi β ℓ J R l g (asgLabel (a.1 u)) ω ^ X.tree.degAt u ∂P : ℝ) : ℂ)
        else ((asgVal μ lam (a.1 u) ^ X.tree.degAt u / (B : ℝ) : ℝ) : ℂ) := by
  classical
  have hroot_ty : X.ty [] ≠ VType.lat := by rw [X.root_ty]; exact X.root_ext
  have hroot : ([] : List ℕ) ∈ X.tree.vtxs.toFinset := List.mem_toFinset.mpr (ob_pt_root_mem _)
  have hpt : ∀ u ∈ X.tree.vtxs.toFinset,
      (if u = [] then ((asgVal μ lam (a.1 u) ^ X.tree.degAt u : ℝ) : ℂ)
       else if X.ty u = VType.lat then
         ((∫ ω, cutoffXi β ℓ J R l g (asgLabel (a.1 u)) ω ^ X.tree.degAt u ∂P : ℝ) : ℂ)
       else ((asgVal μ lam (a.1 u) ^ X.tree.degAt u / (B : ℝ) : ℝ) : ℂ)) =
      ((if u = [] then ((asgVal μ lam (a.1 u) ^ X.tree.degAt u : ℝ) : ℂ) else 1) *
        (if u ≠ [] ∧ X.ty u ≠ VType.lat then
          ((asgVal μ lam (a.1 u) ^ X.tree.degAt u / (B : ℝ) : ℝ) : ℂ) else 1)) *
        (if X.ty u = VType.lat then
          ((∫ ω, cutoffXi β ℓ J R l g (asgLabel (a.1 u)) ω ^ X.tree.degAt u ∂P : ℝ) : ℂ)
          else 1) := by
    intro u _
    by_cases h0 : u = []
    · subst h0; simp only [hroot_ty, ite_true, ne_eq, not_true_eq_false, false_and,
        ite_false, mul_one]
    · by_cases hl : X.ty u = VType.lat <;> simp only [h0, hl, ite_false, ite_true,
        not_false_eq_true, ne_eq, not_true_eq_false, true_and, mul_one, one_mul]
  rw [Finset.prod_congr rfl hpt, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_ite_eq' _ _ (fun u => ((asgVal μ lam (a.1 u) ^ X.tree.degAt u : ℝ) : ℂ)),
    if_pos hroot, ← Finset.prod_filter, ← Finset.prod_filter]
  unfold oneBufVal
  ring

open Classical in
/-- Exact finite Fubini for a one-buffer tree before summing over tree shapes. -/
private lemma ob_tree_asg_factor {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) {m n : ℕ} (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (g : ℤ → Ω → ℝ) (l : ℕ) (t : ℝ)
    {tr : VType} {k : ℕ} (X : RootedTypedTree tr k)
    (x : AsgLab m n (cutoffLabels J ℓ)) :
    let W : List ℕ → Option (AsgLab m n (cutoffLabels J ℓ)) → ℂ := fun u o =>
      if u = [] then ((asgVal μ lam o ^ X.tree.degAt u : ℝ) : ℂ)
      else if X.ty u = VType.lat then
        ((∫ ω, cutoffXi β ℓ J R l g (asgLabel o) ω ^ X.tree.degAt u ∂P : ℝ) : ℂ)
      else ((asgVal μ lam o ^ X.tree.degAt u / (B : ℝ) : ℝ) : ℂ)
    (∑' a : {a : TreeAsg X.tree X.ty m n (cutoffLabels J ℓ) // a.1 [] = some x},
      oneBufVal P β ℓ J R B μ lam g l t X a.1) =
      zetaT t ^ (k + 1) * ∏ u : {u // u ∈ X.tree.vtxs.toFinset},
        ∑ o : {o : Option (AsgLab m n (cutoffLabels J ℓ)) //
          AsgCompat (X.ty u.1) o ∧ (u.1 = [] → o = some x)}, W u.1 o.1 := by
  dsimp only
  simp_rw [ob_val_prod]
  rw [tsum_mul_left]
  congr 1
  exact ob_asg_prod_sum X.tree X.ty x (fun u o =>
    if u = [] then ((asgVal μ lam o ^ X.tree.degAt u : ℝ) : ℂ)
    else if X.ty u = VType.lat then
      ((∫ ω, cutoffXi β ℓ J R l g (asgLabel o) ω ^ X.tree.degAt u ∂P : ℝ) : ℂ)
    else ((asgVal μ lam o ^ X.tree.degAt u / (B : ℝ) : ℝ) : ℂ))

private lemma ob_corner_node (cs : List PlaneTree) (ζ : ℂ) :
    ζ ^ (PlaneTree.node cs).vtxs.length = ζ *
      (cs.map (fun Y => ζ ^ Y.vtxs.length)).prod := by
  induction cs with
  | nil => simp only [PlaneTree.vtxs, vtxsForest, List.length_singleton, pow_one,
      List.map_nil, List.prod_nil, mul_one]
  | cons Y cs ih =>
    rw [ob_pt_vtxs_len, pow_add, ih, List.map_cons, List.prod_cons]
    ring

/-- The corner-power factorization at the root and its latent children. -/
private lemma ob_root_corner_factor (cs : List PlaneTree) (ζ : ℂ) :
    ζ ^ (PlaneTree.node cs).vtxs.length = ζ ^ (cs.length + 1) *
      (cs.map (fun Y => PlaneTree.casesOn Y
        (fun ds => (ds.map (fun Z => ζ ^ Z.vtxs.length)).prod))).prod := by
  have h : (cs.map (fun Y => ζ ^ Y.vtxs.length)).prod = ζ ^ cs.length *
      (cs.map (fun Y => PlaneTree.casesOn Y
        (fun ds => (ds.map (fun Z => ζ ^ Z.vtxs.length)).prod))).prod := by
    induction cs with
    | nil => simp only [List.map_nil, List.prod_nil, List.length_nil, pow_zero, mul_one]
    | cons Y cs ih =>
      cases Y with
      | node ds =>
        simp only [List.map_cons, List.prod_cons, List.length_cons]
        rw [ob_corner_node ds, ih, pow_succ]
        ring
  rw [ob_corner_node, h, pow_succ]
  ring

/-- Summing the root list gives the scalar resolvent once its ratio is inside the unit disc. -/
private lemma ob_root_geometric {z : ℂ} (hz : z ≠ 0) (x : ℂ)
    (h : ‖z⁻¹ * x‖ < 1) :
    (∑' m : ℕ, (z⁻¹) ^ (m + 1) * x ^ m) = (z - x)⁻¹ := by
  have he : ∀ m : ℕ, (z⁻¹) ^ (m + 1) * x ^ m = z⁻¹ * (z⁻¹ * x) ^ m := by
    intro m
    rw [pow_succ, mul_pow]
    ring
  simp_rw [he]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one h]
  have hfac : 1 - z⁻¹ * x = z⁻¹ * (z - x) := by
    rw [mul_sub, inv_mul_cancel₀ hz]
  rw [hfac, mul_inv_rev, inv_inv]
  calc z⁻¹ * ((z - x)⁻¹ * z) = (z - x)⁻¹ * (z⁻¹ * z) := by ring
    _ = (z - x)⁻¹ := by rw [inv_mul_cancel₀ hz, mul_one]

/-- The scalar resolvent obtained after inserting a branch equation into the root recursion. -/
private lemma ob_branch_resolvent (t a x : ℝ) (ht : 0 < t)
    (hden : t + a * x ≠ 0) :
    ((Complex.I * (Real.sqrt t : ℂ)) - (x : ℂ) *
      (-(Complex.I * ((a / Real.sqrt t : ℝ) : ℂ))))⁻¹ =
      -(Complex.I * (Real.sqrt t : ℂ)) / ((t : ℂ) + (a : ℂ) * (x : ℂ)) := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have hdenC : (t : ℂ) + (a : ℂ) * (x : ℂ) ≠ 0 := by
    exact_mod_cast hden
  have hsC : (Real.sqrt t : ℂ) ^ 2 = (t : ℂ) := by
    exact_mod_cast Real.sq_sqrt ht.le
  have hshape : (Complex.I * (Real.sqrt t : ℂ)) - (x : ℂ) *
      (-(Complex.I * ((a / Real.sqrt t : ℝ) : ℂ))) =
      Complex.I * ((t : ℂ) + (a : ℂ) * (x : ℂ)) / (Real.sqrt t : ℂ) := by
    push_cast
    field_simp
    rw [hsC]
    ring
  have hleft : (Complex.I * (Real.sqrt t : ℂ)) - (x : ℂ) *
      (-(Complex.I * ((a / Real.sqrt t : ℝ) : ℂ))) ≠ 0 := by
    rw [hshape]
    exact div_ne_zero (mul_ne_zero Complex.I_ne_zero hdenC) (by exact_mod_cast hs)
  apply (mul_eq_one_iff_inv_eq₀ hleft).mp
  rw [hshape]
  field_simp
  rw [Complex.I_sq]
  simp [hs]

/-- The pointwise geometric series behind the profile transform. -/
private lemma ob_moment_geometric (y q : ℝ) (hq : ‖(q * y ^ 2 : ℂ)‖ < 1) :
    (∑' p : ℕ, ((y : ℂ) ^ (2 * p + 2)) * (-q : ℂ) ^ p) =
      ((y ^ 2 / (1 + q * y ^ 2) : ℝ) : ℂ) := by
  have he : ∀ p : ℕ, ((y : ℂ) ^ (2 * p + 2)) * (-q : ℂ) ^ p =
      (y : ℂ) ^ 2 * (-(q * y ^ 2) : ℂ) ^ p := by
    intro p
    push_cast
    rw [show 2 * p + 2 = 2 + 2 * p by omega, pow_add, pow_mul]
    ring
  simp_rw [he]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
  · push_cast
    congr 1
    ring
  · simpa only [norm_neg] using hq


/-! ### Sums over finite tuples -/

private lemma ob_pi_tsum {R : Type} [NormedField R] [CompleteSpace R] :
    ∀ (n : ℕ) (A : Fin n → Type) (w : ∀ i, A i → R),
    (∀ i, Summable (fun a => ‖w i a‖)) →
    Summable (fun f : (∀ i, A i) => ‖∏ i, w i (f i)‖) ∧
    ∑' f : (∀ i, A i), ∏ i, w i (f i) = ∏ i, ∑' a, w i a := by
  intro n
  induction n with
  | zero =>
    intro A w _
    refine ⟨Summable.of_finite, ?_⟩
    simp
  | succ n ih =>
    intro A w hw
    obtain ⟨h1, h2⟩ := ih (fun i => A i.succ) (fun i => w i.succ) (fun i => hw i.succ)
    let e := Fin.consEquiv A
    have hprod : ∀ p : A 0 × (∀ i : Fin n, A i.succ),
        ∏ i, w i (e p i) = w 0 p.1 * ∏ i : Fin n, w i.succ (p.2 i) := by
      intro p
      rw [Fin.prod_univ_succ]
      rfl
    have hs : Summable (fun p : A 0 × (∀ i : Fin n, A i.succ) => ‖∏ i, w i (e p i)‖) := by
      simp_rw [hprod, norm_mul]
      exact (hw 0).mul_norm h1 |>.congr (fun p => by simp)
    refine ⟨?_, ?_⟩
    · exact (e.summable_iff (f := fun f : (∀ i, A i) => ‖∏ i, w i (f i)‖)).mp hs
    · rw [← e.tsum_eq]
      simp_rw [hprod]
      rw [Fin.prod_univ_succ, ← h2, tsum_mul_tsum_of_summable_norm (hw 0) h1]

/-! ### Root decomposition of externally rooted typed trees -/

private abbrev OE (τ : VType) : Type := Σ k : ℕ, RootedTypedTree τ k

private def ob_ty (t : VType) (c : ℕ) : VType := if c % 2 = 0 then ob_f0 t else t

private abbrev OBlk (t : VType) : Type := Σ p : ℕ, ∀ c : Fin (2 * p + 1), OE (ob_ty t c.val)

private abbrev ODec (t : VType) : Type := Σ m : ℕ, Fin m → OBlk t

private lemma ob_ty_ne_lat {t : VType} (ht : t ≠ VType.lat) (c : ℕ) : ob_ty t c ≠ VType.lat := by
  unfold ob_ty
  split_ifs
  · cases t <;> simp_all [ob_f0]
  · exact ht

private def ob_Rel {t : VType} {k : ℕ} (X : RootedTypedTree t k) (d : ODec t) : Prop :=
  X.tree.childCount [] = d.1 ∧
  ∀ r : Fin d.1, X.tree.childCount [r.val] = 2 * (d.2 r).1 + 1 ∧
    ∀ c : Fin (2 * (d.2 r).1 + 1),
      (∀ v, v ∈ ((d.2 r).2 c).2.tree.vtxs ↔ [r.val, c.val] ++ v ∈ X.tree.vtxs) ∧
      ∀ v ∈ ((d.2 r).2 c).2.tree.vtxs, ((d.2 r).2 c).2.ty v = X.ty ([r.val, c.val] ++ v)

private lemma ob_OE_ext {τ : VType} (a b : OE τ) (htree : a.2.tree = b.2.tree)
    (hty : ∀ u ∈ a.2.tree.vtxs, a.2.ty u = b.2.ty u) : a = b := by
  obtain ⟨k, X⟩ := a
  obtain ⟨k', Y⟩ := b
  dsimp only at htree hty
  have hk : k = k' := by
    have h1 := X.card_vtx
    have h2 := Y.card_vtx
    rw [htree] at h1; omega
  subst hk
  have := ob_rooted_ext X Y htree hty
  subst this; rfl

private lemma ob_pt_prefix_mem (P : PlaneTree) (w w' : List ℕ) (h : w ++ w' ∈ P.vtxs) :
    w ∈ P.vtxs := by
  induction w' using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton w'' i ih =>
    apply ih
    apply ob_pt_parent_mem (w ++ w'') P i
    simpa [List.append_assoc] using h

private lemma ob_Rel_exists {t : VType} {k : ℕ} (X : RootedTypedTree t k) :
    ∃ d : ODec t, ob_Rel X d := by
  classical
  set m := X.tree.childCount [] with hm
  have hp : ∀ r : Fin m, ∃ p : ℕ, X.tree.childCount [r.val] = 2 * p + 1 := fun r => by
    obtain ⟨_, p, hp, -⟩ := ob_root_children X r.val r.2
    exact ⟨p, hp⟩
  choose p hp using hp
  have hY : ∀ (r : Fin m) (c : Fin (2 * p r + 1)), ∃ Y : OE (ob_ty t c.val),
      (∀ v, v ∈ Y.2.tree.vtxs ↔ [r.val, c.val] ++ v ∈ X.tree.vtxs) ∧
      ∀ v ∈ Y.2.tree.vtxs, Y.2.ty v = X.ty ([r.val, c.val] ++ v) := by
    intro r c
    have hr : [r.val] ∈ X.tree.vtxs :=
      (ob_pt_childCount_iff X.tree [] r.val).mpr ⟨ob_pt_root_mem _, r.2⟩
    have hrc : [r.val, c.val] ∈ X.tree.vtxs :=
      (ob_pt_childCount_iff X.tree [r.val] c.val).mpr ⟨hr, by rw [hp r]; exact c.2⟩
    obtain ⟨-, q, hq, -, hq3⟩ := ob_root_children X r.val r.2
    have hty : X.ty [r.val, c.val] = ob_ty t c.val := by
      have := hq3 c.val (by rw [hp r]; exact c.2)
      simpa [ob_ty] using this
    have hext : X.ty [r.val, c.val] ≠ VType.lat := by
      rw [hty]; exact ob_ty_ne_lat X.root_ext _
    have key : ∀ τ : VType, X.ty [r.val, c.val] = τ → ∃ Y : OE τ,
        (∀ v, v ∈ Y.2.tree.vtxs ↔ [r.val, c.val] ++ v ∈ X.tree.vtxs) ∧
        ∀ v ∈ Y.2.tree.vtxs, Y.2.ty v = X.ty ([r.val, c.val] ++ v) := by
      intro τ hτ
      subst hτ
      obtain ⟨r', Y, h1, h2, -⟩ := ob_rooted_subtree X [r.val, c.val] hrc hext
      exact ⟨⟨r', Y⟩, h1, h2⟩
    exact key _ hty
  choose Y hY using hY
  exact ⟨⟨m, fun r => ⟨p r, Y r⟩⟩, rfl, fun r => ⟨hp r, fun c => hY r c⟩⟩

private lemma ob_Rel_mem {t : VType} {k : ℕ} (X : RootedTypedTree t k) (d : ODec t)
    (h : ob_Rel X d) (u : List ℕ) :
    u ∈ X.tree.vtxs ↔ u = [] ∨ (∃ r : Fin d.1, u = [r.val]) ∨
      ∃ (r : Fin d.1) (c : Fin (2 * (d.2 r).1 + 1)) (v : List ℕ),
        v ∈ ((d.2 r).2 c).2.tree.vtxs ∧ u = [r.val, c.val] ++ v := by
  obtain ⟨h0, h1⟩ := h
  constructor
  · intro hu
    rcases u with _ | ⟨a, u'⟩
    · exact Or.inl rfl
    · have ha : [a] ∈ X.tree.vtxs := ob_pt_prefix_mem X.tree [a] u' hu
      have ha' := (ob_pt_childCount_iff X.tree [] a).mp ha
      have hlt : a < d.1 := by rw [← h0]; exact ha'.2
      rcases u' with _ | ⟨b, v⟩
      · exact Or.inr (Or.inl ⟨⟨a, hlt⟩, rfl⟩)
      · have hb : [a, b] ∈ X.tree.vtxs := ob_pt_prefix_mem X.tree [a, b] v hu
        have hb' := (ob_pt_childCount_iff X.tree [a] b).mp hb
        obtain ⟨hc, hY⟩ := h1 ⟨a, hlt⟩
        have hlt2 : b < 2 * (d.2 ⟨a, hlt⟩).1 + 1 := by rw [← hc]; exact hb'.2
        refine Or.inr (Or.inr ⟨⟨a, hlt⟩, ⟨b, hlt2⟩, v, ?_, rfl⟩)
        exact ((hY ⟨b, hlt2⟩).1 v).mpr hu
  · rintro (rfl | ⟨r, rfl⟩ | ⟨r, c, v, hv, rfl⟩)
    · exact ob_pt_root_mem _
    · exact (ob_pt_childCount_iff X.tree [] r.val).mpr ⟨ob_pt_root_mem _, by rw [h0]; exact r.2⟩
    · exact ((h1 r).2 c).1 v |>.mp hv

private lemma ob_Rel_unique {t : VType} {k : ℕ} (X : RootedTypedTree t k) (d d' : ODec t)
    (h : ob_Rel X d) (h' : ob_Rel X d') : d = d' := by
  obtain ⟨m, f⟩ := d
  obtain ⟨m', f'⟩ := d'
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  dsimp only at h1 h1' h2 h2'
  have hm : m = m' := h1.symm.trans h1'
  subst hm
  have key : ∀ r, f r = f' r := by
    intro r
    have e1 := h2 r
    have e2 := h2' r
    revert e1 e2
    generalize f r = a
    generalize f' r = a'
    obtain ⟨p, Y⟩ := a
    obtain ⟨p', Y'⟩ := a'
    intro e1 e2
    dsimp only at e1 e2
    have hp : p = p' := by have := e1.1; have := e2.1; omega
    subst hp
    have : Y = Y' := by
      funext c
      apply ob_OE_ext
      · apply ob_pt_ext
        intro v
        rw [(e1.2 c).1 v, (e2.2 c).1 v]
      · intro v hv
        have hv' : v ∈ (Y' c).2.tree.vtxs := by
          rw [(e2.2 c).1 v, ← (e1.2 c).1 v]; exact hv
        rw [(e1.2 c).2 v hv, (e2.2 c).2 v hv']
    rw [this]
  have : f = f' := funext key
  rw [this]

private lemma ob_Rel_inj {t : VType} {k k' : ℕ} (X : RootedTypedTree t k)
    (X' : RootedTypedTree t k') (d : ODec t) (h : ob_Rel X d) (h' : ob_Rel X' d) :
    (⟨k, X⟩ : OE t) = ⟨k', X'⟩ := by
  apply ob_OE_ext
  · dsimp only
    apply ob_pt_ext
    intro u
    rw [ob_Rel_mem X d h, ob_Rel_mem X' d h']
  · intro u hu
    dsimp only at hu ⊢
    have hu' := (ob_Rel_mem X d h u).mp hu
    rcases hu' with rfl | ⟨r, rfl⟩ | ⟨r, c, v, hv, rfl⟩
    · rw [X.root_ty, X'.root_ty]
    · have e1 := (ob_root_children X r.val (by rw [h.1]; exact r.2)).1
      have e2 := (ob_root_children X' r.val (by rw [h'.1]; exact r.2)).1
      rw [e1, e2]
    · rw [← ((h.2 r).2 c).2 v hv, ← ((h'.2 r).2 c).2 v hv]

private def ob_asmTree {t : VType} (d : ODec t) : PlaneTree :=
  PlaneTree.node (List.ofFn fun r : Fin d.1 =>
    PlaneTree.node (List.ofFn fun c : Fin (2 * (d.2 r).1 + 1) => ((d.2 r).2 c).2.tree))

private def ob_asmTy {t : VType} (d : ODec t) : List ℕ → VType
  | [] => t
  | [r] => if r < d.1 then VType.lat else VType.out
  | r :: c :: v =>
    if h : r < d.1 then
      (if h' : c < 2 * (d.2 ⟨r, h⟩).1 + 1 then ((d.2 ⟨r, h⟩).2 ⟨c, h'⟩).2.ty v else VType.out)
    else VType.out

private lemma ob_asm_mem_cons {t : VType} (d : ODec t) (a : ℕ) (w : List ℕ) :
    a :: w ∈ (ob_asmTree d).vtxs ↔ ∃ h : a < d.1,
      w ∈ (PlaneTree.node (List.ofFn fun c : Fin (2 * (d.2 ⟨a, h⟩).1 + 1) =>
        ((d.2 ⟨a, h⟩).2 c).2.tree)).vtxs := by
  unfold ob_asmTree
  rw [ob_pt_mem_idx]
  simp [List.getElem_ofFn]

private lemma ob_asm_mem_cons2 {t : VType} (d : ODec t) (a b : ℕ) (v : List ℕ) :
    a :: b :: v ∈ (ob_asmTree d).vtxs ↔ ∃ (h : a < d.1) (h' : b < 2 * (d.2 ⟨a, h⟩).1 + 1),
      v ∈ ((d.2 ⟨a, h⟩).2 ⟨b, h'⟩).2.tree.vtxs := by
  rw [ob_asm_mem_cons]
  constructor
  · rintro ⟨h, hh⟩
    rw [ob_pt_mem_idx] at hh
    obtain ⟨h', hh'⟩ := hh
    simp only [List.length_ofFn, List.getElem_ofFn] at h' hh'
    exact ⟨h, h', hh'⟩
  · rintro ⟨h, h', hh⟩
    refine ⟨h, ?_⟩
    rw [ob_pt_mem_idx]
    simp only [List.length_ofFn, List.getElem_ofFn]
    exact ⟨h', hh⟩

private lemma ob_asm_mem {t : VType} (d : ODec t) (u : List ℕ) :
    u ∈ (ob_asmTree d).vtxs ↔ u = [] ∨ (∃ r : Fin d.1, u = [r.val]) ∨
      ∃ (r : Fin d.1) (c : Fin (2 * (d.2 r).1 + 1)) (v : List ℕ),
        v ∈ ((d.2 r).2 c).2.tree.vtxs ∧ u = [r.val, c.val] ++ v := by
  rcases u with _ | ⟨a, w⟩
  · simp only [true_or, iff_true]; exact ob_pt_root_mem _
  · rcases w with _ | ⟨b, v⟩
    · rw [ob_asm_mem_cons]
      constructor
      · rintro ⟨h, -⟩
        exact Or.inr (Or.inl ⟨⟨a, h⟩, rfl⟩)
      · rintro (h | ⟨r, hr⟩ | ⟨r, c, v, -, hv⟩)
        · simp at h
        · have : a = r.val := by simpa using hr
          exact ⟨this ▸ r.2, ob_pt_root_mem _⟩
        · simp at hv
    · rw [ob_asm_mem_cons2]
      constructor
      · rintro ⟨h, h', hh⟩
        exact Or.inr (Or.inr ⟨⟨a, h⟩, ⟨b, h'⟩, v, hh, rfl⟩)
      · rintro (h | ⟨r, hr⟩ | ⟨r, c, v', hv', hv⟩)
        · simp at h
        · simp at hr
        · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hv
          obtain ⟨rfl, rfl, rfl⟩ := hv
          exact ⟨r.2, c.2, hv'⟩

private lemma ob_asm_cc_root {t : VType} (d : ODec t) :
    (ob_asmTree d).childCount [] = d.1 := by
  unfold ob_asmTree
  rw [ob_pt_cc_root]
  simp

private lemma ob_asm_cc_r {t : VType} (d : ODec t) (r : Fin d.1) :
    (ob_asmTree d).childCount [r.val] = 2 * (d.2 r).1 + 1 := by
  unfold ob_asmTree
  have := ob_pt_cc_idx (List.ofFn fun r : Fin d.1 =>
    PlaneTree.node (List.ofFn fun c : Fin (2 * (d.2 r).1 + 1) => ((d.2 r).2 c).2.tree))
    r.val (by simp) [] (by simp [ob_pt_root_mem])
  simp only [List.getElem_ofFn] at this
  rw [this, ob_pt_cc_root]
  simp

private lemma ob_asm_cc_rcv {t : VType} (d : ODec t) (r : Fin d.1) (c : Fin (2 * (d.2 r).1 + 1))
    (v : List ℕ) (hv : v ∈ ((d.2 r).2 c).2.tree.vtxs) :
    (ob_asmTree d).childCount ([r.val, c.val] ++ v) = ((d.2 r).2 c).2.tree.childCount v := by
  unfold ob_asmTree
  have h1 := ob_pt_cc_idx (List.ofFn fun r : Fin d.1 =>
    PlaneTree.node (List.ofFn fun c : Fin (2 * (d.2 r).1 + 1) => ((d.2 r).2 c).2.tree))
    r.val (by rw [List.length_ofFn]; exact r.2) (c.val :: v) (by
      simp only [List.getElem_ofFn]
      rw [ob_pt_mem_idx]
      exact ⟨by rw [List.length_ofFn]; exact c.2, by simpa only [List.getElem_ofFn] using hv⟩)
  simp only [List.getElem_ofFn] at h1
  rw [List.cons_append, List.singleton_append, h1]
  have h2 := ob_pt_cc_idx (List.ofFn fun c : Fin (2 * (d.2 r).1 + 1) => ((d.2 r).2 c).2.tree)
    c.val (by rw [List.length_ofFn]; exact c.2) v (by simpa only [List.getElem_ofFn] using hv)
  simp only [List.getElem_ofFn] at h2
  exact h2

private lemma ob_asmTy_rcv {t : VType} (d : ODec t) (r : Fin d.1) (c : Fin (2 * (d.2 r).1 + 1))
    (v : List ℕ) : ob_asmTy d ([r.val, c.val] ++ v) = ((d.2 r).2 c).2.ty v := by
  simp [ob_asmTy, r.2, c.2]

private lemma ob_asmTy_r {t : VType} (d : ODec t) (r : Fin d.1) :
    ob_asmTy d [r.val] = VType.lat := by
  simp [ob_asmTy, r.2]

private lemma ob_f0_ne {t : VType} (ht : t ≠ VType.lat) : t ≠ ob_f0 t ∧ ob_f0 t ≠ VType.lat := by
  cases t <;> simp_all [ob_f0]

private lemma ob_cyclicAlt_pat {t : VType} (ht : t ≠ VType.lat) (p : ℕ) :
    CyclicAlt (t :: (List.range (2 * p + 1)).map (ob_ty t)) := by
  obtain ⟨hne, hf⟩ := ob_f0_ne ht
  have hget : ∀ j, j < 2 * p + 2 → (t :: (List.range (2 * p + 1)).map (ob_ty t)).getD j VType.lat =
      if j % 2 = 0 then t else ob_f0 t := by
    intro j hj
    rcases j with _ | j
    · simp
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_map,
        List.getElem?_range (show j < 2 * p + 1 by omega), Option.map_some, Option.getD_some]
      unfold ob_ty
      by_cases h : j % 2 = 0
      · simp [h, show (j + 1) % 2 ≠ 0 by omega]
      · simp [h, show (j + 1) % 2 = 0 by omega]
  intro j hj
  simp only [List.length_cons, List.length_map, List.length_range] at hj ⊢
  have hlen : 2 * p + 1 + 1 = 2 * p + 2 := by omega
  rw [hlen] at hj ⊢
  rw [hget j hj]
  by_cases hjm : j + 1 < 2 * p + 2
  · rw [Nat.mod_eq_of_lt hjm, hget (j + 1) hjm]
    by_cases h : j % 2 = 0
    · simp [h, show (j + 1) % 2 ≠ 0 by omega, ht, hne, hf]
    · simp [h, show (j + 1) % 2 = 0 by omega, ht, hne.symm, hf]
  · have hj' : j = 2 * p + 1 := by omega
    subst hj'
    rw [show 2 * p + 1 + 1 = 2 * p + 2 by omega, Nat.mod_self, hget 0 (by omega)]
    simp [show (2 * p + 1) % 2 ≠ 0 by omega, ht, hne.symm, hf]

private lemma ob_asm_exists {t : VType} (ht : t ≠ VType.lat) (d : ODec t) :
    ∃ (k : ℕ) (X : RootedTypedTree t k), ob_Rel X d := by
  classical
  have hpos := ob_pt_vtxs_pos (ob_asmTree d)
  have hoff : ∀ u, u ∉ (ob_asmTree d).vtxs → ob_asmTy d u = VType.out := by
    intro u hu
    rcases u with _ | ⟨a, w⟩
    · exact absurd (ob_pt_root_mem _) hu
    · rcases w with _ | ⟨b, v⟩
      · by_cases h : a < d.1
        · exact absurd ((ob_asm_mem d _).mpr (Or.inr (Or.inl ⟨⟨a, h⟩, rfl⟩))) hu
        · simp [ob_asmTy, h]
      · by_cases h : a < d.1
        · by_cases h' : b < 2 * (d.2 ⟨a, h⟩).1 + 1
          · have hv : v ∉ ((d.2 ⟨a, h⟩).2 ⟨b, h'⟩).2.tree.vtxs := fun hv =>
              hu ((ob_asm_mem_cons2 d a b v).mpr ⟨h, h', hv⟩)
            have := ((d.2 ⟨a, h⟩).2 ⟨b, h'⟩).2.off_support v hv
            simpa [ob_asmTy, h, h'] using this
          · simp [ob_asmTy, h, h']
        · simp [ob_asmTy, h]
  have hedge : ∀ u ∈ (ob_asmTree d).vtxs, ∀ v ∈ (ob_asmTree d).vtxs, v ≠ [] → v.dropLast = u →
      (ob_asmTy d u = VType.lat ↔ ¬ ob_asmTy d v = VType.lat) := by
    intro u hu v hv hne hd
    rcases (ob_asm_mem d v).mp hv with h | ⟨r, rfl⟩ | ⟨r, c, w, hw, rfl⟩
    · exact absurd h hne
    · simp only [List.dropLast_singleton] at hd
      subst hd
      rw [ob_asmTy_r]
      simp [ob_asmTy, ht]
    · by_cases hw0 : w = []
      · subst hw0
        have hu' : u = [r.val] := by rw [← hd]; rfl
        subst hu'
        rw [ob_asmTy_r, ob_asmTy_rcv d r c [], ((d.2 r).2 c).2.root_ty]
        exact ⟨fun _ => ob_ty_ne_lat ht _, fun _ => rfl⟩
      · have hu' : u = [r.val, c.val] ++ w.dropLast := by
          rw [← hd, List.dropLast_append_of_ne_nil hw0]
        subst hu'
        rw [ob_asmTy_rcv, ob_asmTy_rcv]
        exact ((d.2 r).2 c).2.edge_joins _ (ob_parent_mem _ hw hw0) w hw hw0 rfl
  have halt : ∀ u ∈ (ob_asmTree d).vtxs, u ≠ [] → ob_asmTy d u = VType.lat →
      CyclicAlt (ob_asmTy d u.dropLast :: (List.range ((ob_asmTree d).childCount u)).map
        fun i => ob_asmTy d (u ++ [i])) := by
    intro u hu hne hl
    rcases (ob_asm_mem d u).mp hu with h | ⟨r, rfl⟩ | ⟨r, c, w, hw, rfl⟩
    · exact absurd h hne
    · rw [ob_asm_cc_r]
      have e : (List.range (2 * (d.2 r).1 + 1)).map (fun i => ob_asmTy d ([r.val] ++ [i])) =
          (List.range (2 * (d.2 r).1 + 1)).map (ob_ty t) := by
        refine List.map_congr_left fun i hi => ?_
        have hi' : i < 2 * (d.2 r).1 + 1 := List.mem_range.mp hi
        have := ob_asmTy_rcv d r ⟨i, hi'⟩ []
        simp only [List.append_nil] at this
        change ob_asmTy d [r.val, i] = _
        rw [this, ((d.2 r).2 ⟨i, hi'⟩).2.root_ty]
      rw [e]
      exact ob_cyclicAlt_pat ht _
    · by_cases hw0 : w = []
      · subst hw0
        rw [ob_asmTy_rcv d r c [], ((d.2 r).2 c).2.root_ty] at hl
        exact absurd hl (ob_ty_ne_lat ht _)
      · have hl' : ((d.2 r).2 c).2.ty w = VType.lat := by
          rw [← ob_asmTy_rcv]; exact hl
        have halt' := ((d.2 r).2 c).2.latent_alt w hw hw0 hl'
        rw [ob_asm_cc_rcv d r c w hw, List.dropLast_append_of_ne_nil hw0, ob_asmTy_rcv]
        have e : (List.range (((d.2 r).2 c).2.tree.childCount w)).map
            (fun i => ob_asmTy d (([r.val, c.val] ++ w) ++ [i])) =
            (List.range (((d.2 r).2 c).2.tree.childCount w)).map
            (fun i => ((d.2 r).2 c).2.ty (w ++ [i])) := by
          refine List.map_congr_left fun i hi => ?_
          rw [List.append_assoc, ob_asmTy_rcv]
        rw [e]
        exact halt'
  have hpos' : ∀ k, k = (ob_asmTree d).vtxs.length - 1 → (ob_asmTree d).vtxs.length = k + 1 := by
    intro k hk; omega
  refine ⟨(ob_asmTree d).vtxs.length - 1, ⟨ob_asmTree d, ob_asmTy d, hpos' _ rfl, hoff, rfl, ht, hedge, halt⟩, ?_⟩
  refine ⟨ob_asm_cc_root d, fun r => ⟨ob_asm_cc_r d r, fun c => ⟨?_, ?_⟩⟩⟩
  · intro v
    show v ∈ _ ↔ r.val :: c.val :: v ∈ (ob_asmTree d).vtxs
    rw [ob_asm_mem_cons2]
    exact ⟨fun hv => ⟨r.2, c.2, hv⟩, fun ⟨_, _, hv⟩ => hv⟩
  · intro v hv
    exact (ob_asmTy_rcv d r c v).symm

private noncomputable def ob_decMap {t : VType} (X : OE t) : ODec t :=
  Classical.choose (ob_Rel_exists X.2)

private lemma ob_decMap_rel {t : VType} (X : OE t) : ob_Rel X.2 (ob_decMap X) :=
  Classical.choose_spec (ob_Rel_exists X.2)

private lemma ob_decMap_bij {t : VType} (ht : t ≠ VType.lat) :
    Function.Bijective (ob_decMap (t := t)) := by
  constructor
  · intro X X' h
    have h1 := ob_decMap_rel X
    have h2 := ob_decMap_rel X'
    rw [← h] at h2
    exact ob_Rel_inj X.2 X'.2 _ h1 h2
  · intro d
    obtain ⟨k, X, hX⟩ := ob_asm_exists ht d
    exact ⟨⟨k, X⟩, ob_Rel_unique X _ _ (ob_decMap_rel ⟨k, X⟩) hX⟩

private noncomputable def ob_decEquiv {t : VType} (ht : t ≠ VType.lat) : OE t ≃ ODec t :=
  Equiv.ofBijective _ (ob_decMap_bij ht)

private lemma ob_decEquiv_rel {t : VType} (ht : t ≠ VType.lat) (X : OE t) :
    ob_Rel X.2 (ob_decEquiv ht X) := ob_decMap_rel X

private lemma ob_prod_split {t : VType} {k : ℕ} (X : RootedTypedTree t k) (d : ODec t)
    (h : ob_Rel X d) (f : List ℕ → ℂ) :
    ∏ u ∈ X.tree.vtxs.toFinset, f u =
      f [] * ∏ r : Fin d.1, (f [r.val] * ∏ c : Fin (2 * (d.2 r).1 + 1),
        ∏ v ∈ ((d.2 r).2 c).2.tree.vtxs.toFinset, f ([r.val, c.val] ++ v)) := by
  classical
  have hV : X.tree.vtxs.toFinset = insert [] (Finset.univ.biUnion fun r : Fin d.1 =>
      insert [r.val] (Finset.univ.biUnion fun c : Fin (2 * (d.2 r).1 + 1) =>
        (((d.2 r).2 c).2.tree.vtxs.toFinset).image (fun v => [r.val, c.val] ++ v))) := by
    ext u
    simp only [List.mem_toFinset, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image]
    rw [ob_Rel_mem X d h]
    constructor
    · rintro (h1 | ⟨r, h1⟩ | ⟨r, c, v, hv, h1⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨r, Or.inl h1⟩
      · exact Or.inr ⟨r, Or.inr ⟨c, v, hv, h1.symm⟩⟩
    · rintro (h1 | ⟨r, h1 | ⟨c, v, hv, h1⟩⟩)
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨r, h1⟩)
      · exact Or.inr (Or.inr ⟨r, c, v, hv, h1.symm⟩)
  rw [hV, Finset.prod_insert, Finset.prod_biUnion]
  · congr 1
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [Finset.prod_insert, Finset.prod_biUnion]
    · congr 1
      refine Finset.prod_congr rfl fun c _ => ?_
      rw [Finset.prod_image]
      intro v _ v' _ hvv
      exact List.append_cancel_left hvv
    · intro c _ c' _ hcc
      rw [Function.onFun, Finset.disjoint_left]
      intro u hu hu'
      simp only [Finset.mem_image] at hu hu'
      obtain ⟨v, _, rfl⟩ := hu
      obtain ⟨v', _, hv'⟩ := hu'
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hv'
      exact hcc (Fin.ext hv'.2.1.symm)
    · intro hmem
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hmem
      obtain ⟨c, v, _, hv⟩ := hmem
      simp at hv
  · intro r _ r' _ hrr
    rw [Function.onFun, Finset.disjoint_left]
    intro u hu hu'
    simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image] at hu hu'
    have key : ∀ (r : Fin d.1) (u : List ℕ), (u = [r.val] ∨ ∃ c : Fin (2 * (d.2 r).1 + 1),
        ∃ v ∈ ((d.2 r).2 c).2.tree.vtxs.toFinset, [r.val, c.val] ++ v = u) → u.head? = some r.val := by
      intro r u hu
      rcases hu with rfl | ⟨c, v, _, rfl⟩ <;> rfl
    have h1 := key r u hu
    have h2 := key r' u hu'
    rw [h1] at h2
    exact hrr (Fin.ext (Option.some_injective _ h2))
  · intro hmem
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_image] at hmem
    obtain ⟨r, h1 | ⟨c, v, _, h1⟩⟩ := hmem <;> simp at h1

private def ob_loc (cdf : ℕ → ℂ) (Mf : VType → ℕ → ℂ) {tr : VType} {k : ℕ}
    (X : RootedTypedTree tr k) (u : List ℕ) : ℂ :=
  if X.ty u = VType.lat then cdf (X.tree.degAt u) else Mf (X.ty u) (X.tree.degAt u)

private def ob_rest (ζ : ℂ) (cdf : ℕ → ℂ) (Mf : VType → ℕ → ℂ) {tr : VType} {k : ℕ}
    (X : RootedTypedTree tr k) : ℂ :=
  ζ ^ (k + 1) * ∏ u ∈ X.tree.vtxs.toFinset.filter (fun u => u ≠ []), ob_loc cdf Mf X u

private def ob_C (ζ : ℂ) (cdf : ℕ → ℂ) (Mf : VType → ℕ → ℂ) {τ : VType} (Y : OE τ) : ℂ :=
  Mf τ (Y.2.tree.degAt [] + 1) * ob_rest ζ cdf Mf Y.2

private lemma ob_cc_congr (P Q : PlaneTree) (u u' : List ℕ) (hu : u ∈ P.vtxs) (hu' : u' ∈ Q.vtxs)
    (h : ∀ i, u ++ [i] ∈ P.vtxs ↔ u' ++ [i] ∈ Q.vtxs) : P.childCount u = Q.childCount u' := by
  have key : ∀ i, i < P.childCount u ↔ i < Q.childCount u' := fun i => by
    have a := ob_pt_childCount_iff P u i
    have b := ob_pt_childCount_iff Q u' i
    constructor
    · intro hi; exact (b.mp ((h i).mp (a.mpr ⟨hu, hi⟩))).2
    · intro hi; exact (a.mp ((h i).mpr (b.mpr ⟨hu', hi⟩))).2
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd ((key _).mpr hlt) (lt_irrefl _)
  · exact absurd ((key _).mp hlt) (lt_irrefl _)

private lemma ob_C_prod (ζ : ℂ) (cdf : ℕ → ℂ) (Mf : VType → ℕ → ℂ) {τ : VType} {k : ℕ}
    (Y : RootedTypedTree τ k) (F : List ℕ → ℂ)
    (hF : ∀ v ∈ Y.tree.vtxs, F v = if v = [] then Mf τ (Y.tree.degAt [] + 1)
      else ob_loc cdf Mf Y v) :
    ∏ v ∈ Y.tree.vtxs.toFinset, (ζ * F v) =
      ob_C ζ cdf Mf (⟨k, Y⟩ : OE τ) := by
  classical
  rw [Finset.prod_mul_distrib, Finset.prod_const, ob_card_vtxs]
  unfold ob_C ob_rest
  have hroot : ([] : List ℕ) ∈ Y.tree.vtxs.toFinset := List.mem_toFinset.mpr (ob_pt_root_mem _)
  rw [← Finset.mul_prod_erase _ F hroot, hF [] (ob_pt_root_mem _), if_pos rfl, ← Finset.filter_ne']
  dsimp only
  have : ∏ x ∈ Y.tree.vtxs.toFinset.filter (fun a => a ≠ []), F x =
      ∏ x ∈ Y.tree.vtxs.toFinset.filter (fun a => a ≠ []), ob_loc cdf Mf Y x := by
    refine Finset.prod_congr rfl fun v hv => ?_
    simp only [Finset.mem_filter, List.mem_toFinset] at hv
    rw [hF v hv.1, if_neg hv.2]
  rw [this]
  ring

private lemma ob_Rel_cc {t : VType} {k : ℕ} (X : RootedTypedTree t k) (d : ODec t)
    (h : ob_Rel X d) (r : Fin d.1) (c : Fin (2 * (d.2 r).1 + 1)) (v : List ℕ)
    (hv : v ∈ ((d.2 r).2 c).2.tree.vtxs) :
    X.tree.childCount ([r.val, c.val] ++ v) = ((d.2 r).2 c).2.tree.childCount v := by
  have hY := (h.2 r).2 c
  symm
  apply ob_cc_congr _ _ _ _ hv ((hY.1 v).mp hv)
  intro i
  rw [hY.1 (v ++ [i]), List.append_assoc]

private lemma ob_rest_dec (ζ : ℂ) (cdf : ℕ → ℂ) (Mf : VType → ℕ → ℂ) {t : VType} {k : ℕ}
    (X : RootedTypedTree t k) (d : ODec t) (h : ob_Rel X d) :
    ob_rest ζ cdf Mf X = ζ * ∏ r : Fin d.1, (ζ * cdf (2 * (d.2 r).1 + 2) *
      ∏ c : Fin (2 * (d.2 r).1 + 1), ob_C ζ cdf Mf ((d.2 r).2 c)) := by
  classical
  have step1 : ob_rest ζ cdf Mf X = ∏ u ∈ X.tree.vtxs.toFinset,
      (ζ * (if u ≠ [] then ob_loc cdf Mf X u else 1)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, ob_card_vtxs, ← Finset.prod_filter]
    rfl
  rw [step1, ob_prod_split X d h]
  have hroot : (if ([] : List ℕ) ≠ [] then ob_loc cdf Mf X [] else 1) = 1 := by simp
  rw [hroot, mul_one]
  congr 1
  refine Finset.prod_congr rfl fun r _ => ?_
  have hm : r.val < X.tree.childCount [] := by rw [h.1]; exact r.2
  obtain ⟨hlat, -⟩ := ob_root_children X r.val hm
  have hloc : ζ * (if [r.val] ≠ [] then ob_loc cdf Mf X [r.val] else 1) =
      ζ * cdf (2 * (d.2 r).1 + 2) := by
    simp only [ne_eq, List.cons_ne_self, not_false_eq_true, if_true]
    unfold ob_loc PlaneTree.degAt
    rw [hlat, if_pos rfl, (h.2 r).1]
    simp
  rw [hloc]
  congr 1
  refine Finset.prod_congr rfl fun c _ => ?_
  have hY := (h.2 r).2 c
  have := ob_C_prod ζ cdf Mf ((d.2 r).2 c).2 (fun v =>
    if ([r.val, c.val] ++ v) ≠ [] then ob_loc cdf Mf X ([r.val, c.val] ++ v) else 1) ?_
  · rw [← this]
  · intro v hv
    have hne : ([r.val, c.val] ++ v) ≠ [] := by simp
    simp only [hne, ne_eq, not_false_eq_true, if_true]
    unfold ob_loc
    rw [← hY.2 v hv]
    have hcc := ob_Rel_cc X d h r c v hv
    have hdeg : X.tree.degAt ([r.val, c.val] ++ v) = X.tree.childCount ([r.val, c.val] ++ v) + 1 := by
      unfold PlaneTree.degAt; simp
    rw [hdeg, hcc]
    by_cases hv0 : v = []
    · subst hv0
      rw [if_pos rfl, ((d.2 r).2 c).2.root_ty]
      have hnl : ob_ty t c.val ≠ VType.lat := ((d.2 r).2 c).2.root_ext
      rw [if_neg hnl]
      unfold PlaneTree.degAt
      simp
    · rw [if_neg hv0]
      unfold PlaneTree.degAt
      simp [hv0]

private lemma ob_prod_ty {M : Type} [CommMonoid M] (F : VType → M) (t : VType) (p : ℕ) :
    ∏ c : Fin (2 * p + 1), F (ob_ty t c.val) = F (ob_f0 t) ^ (p + 1) * F t ^ p := by
  rw [Fin.prod_univ_eq_prod_range (fun c => F (ob_ty t c)) (2 * p + 1)]
  induction p with
  | zero => simp [ob_ty]
  | succ p ih =>
    rw [show 2 * (p + 1) + 1 = 2 * p + 1 + 1 + 1 by ring, Finset.prod_range_succ,
      Finset.prod_range_succ, ih]
    have h1 : ob_ty t (2 * p + 1) = t := by simp [ob_ty]
    have h2 : ob_ty t (2 * p + 1 + 1) = ob_f0 t := by
      simp only [ob_ty]; rw [if_pos (by omega)]
    rw [h1, h2, pow_succ (F (ob_f0 t)) (p + 1), pow_succ (F t) p]
    ac_rfl

private def ob_m (ζ : ℂ) (cdf : ℕ → ℂ) (Mf : VType → ℕ → ℂ) (τ : VType) : ℂ :=
  ∑' Y : OE τ, ob_C ζ cdf Mf Y

private def ob_κ (ζ : ℂ) (cdf : ℕ → ℂ) (Mf : VType → ℕ → ℂ) (τ : VType) : ℝ :=
  ∑' Y : OE τ, ‖ob_C ζ cdf Mf Y‖

private lemma ob_blk_sums (ζ : ℂ) (cdf : ℕ → ℂ) (Mf : VType → ℕ → ℂ) (t : VType)
    (hC : ∀ τ, τ ≠ VType.lat → Summable (fun Y : OE τ => ‖ob_C ζ cdf Mf Y‖))
    (ht : t ≠ VType.lat) (p : ℕ) :
    Summable (fun g : (∀ c : Fin (2 * p + 1), OE (ob_ty t c.val)) =>
      ‖∏ c, ob_C ζ cdf Mf (g c)‖) ∧
    ∑' g : (∀ c : Fin (2 * p + 1), OE (ob_ty t c.val)), ∏ c, ob_C ζ cdf Mf (g c) =
      ob_m ζ cdf Mf (ob_f0 t) ^ (p + 1) * ob_m ζ cdf Mf t ^ p ∧
    ∑' g : (∀ c : Fin (2 * p + 1), OE (ob_ty t c.val)), ‖∏ c, ob_C ζ cdf Mf (g c)‖ =
      ob_κ ζ cdf Mf (ob_f0 t) ^ (p + 1) * ob_κ ζ cdf Mf t ^ p := by
  have hsum : ∀ c : Fin (2 * p + 1), Summable (fun Y : OE (ob_ty t c.val) => ‖ob_C ζ cdf Mf Y‖) :=
    fun c => hC _ (ob_ty_ne_lat ht _)
  obtain ⟨h1, h2⟩ := ob_pi_tsum (R := ℂ) (2 * p + 1) (fun c => OE (ob_ty t c.val))
    (fun c Y => ob_C ζ cdf Mf Y) hsum
  have hsumR : ∀ c : Fin (2 * p + 1),
      Summable (fun Y : OE (ob_ty t c.val) => ‖(‖ob_C ζ cdf Mf Y‖ : ℝ)‖) := by
    intro c; simpa only [norm_norm] using hsum c
  obtain ⟨h3, h4⟩ := ob_pi_tsum (R := ℝ) (2 * p + 1) (fun c => OE (ob_ty t c.val))
    (fun c Y => ‖ob_C ζ cdf Mf Y‖) hsumR
  refine ⟨h1, ?_, ?_⟩
  · rw [h2]
    have := ob_prod_ty (fun τ => ∑' Y : OE τ, ob_C ζ cdf Mf Y) t p
    exact this
  · simp_rw [norm_prod]
    rw [h4]
    exact ob_prod_ty (fun τ => ∑' Y : OE τ, ‖ob_C ζ cdf Mf Y‖) t p

private lemma ob_tree_sum (ζ : ℂ) (cdf : ℕ → ℂ) (Mf : VType → ℕ → ℂ) (t : VType)
    (ht : t ≠ VType.lat)
    (hC : ∀ τ, τ ≠ VType.lat → Summable (fun Y : OE τ => ‖ob_C ζ cdf Mf Y‖))
    (z : ℂ)
    (hη : Summable (fun p : ℕ => ‖cdf (2 * p + 2)‖ * ob_κ ζ cdf Mf (ob_f0 t) ^ (p + 1) *
      ob_κ ζ cdf Mf t ^ p))
    (hz : ‖z‖ * (‖ζ‖ * ∑' p : ℕ, ‖cdf (2 * p + 2)‖ * ob_κ ζ cdf Mf (ob_f0 t) ^ (p + 1) *
      ob_κ ζ cdf Mf t ^ p) < 1) :
    ∑' X : OE t, z ^ X.2.tree.degAt [] * ob_rest ζ cdf Mf X.2 =
      ζ / (1 - z * ζ * ∑' p : ℕ, cdf (2 * p + 2) * ob_m ζ cdf Mf (ob_f0 t) ^ (p + 1) *
        ob_m ζ cdf Mf t ^ p) := by
  classical
  set e := ob_decEquiv ht with he
  have hrel := ob_decEquiv_rel ht
  set κ1 := ob_κ ζ cdf Mf (ob_f0 t) with hκ1
  set κ2 := ob_κ ζ cdf Mf t with hκ2
  set m1 := ob_m ζ cdf Mf (ob_f0 t) with hm1
  set m2 := ob_m ζ cdf Mf t with hm2
  set ηabs := ∑' p : ℕ, ‖cdf (2 * p + 2)‖ * κ1 ^ (p + 1) * κ2 ^ p with hηabs
  let w : OBlk t → ℂ := fun b => ζ * cdf (2 * b.1 + 2) * ∏ c, ob_C ζ cdf Mf (b.2 c)
  let Gd : ODec t → ℂ := fun d => z ^ d.1 * (ζ * ∏ r : Fin d.1, w (d.2 r))
  have hG : ∀ X : OE t, z ^ X.2.tree.degAt [] * ob_rest ζ cdf Mf X.2 = Gd (e X) := by
    intro X
    have h := hrel X
    rw [ob_rest_dec ζ cdf Mf X.2 _ h]
    have : X.2.tree.degAt [] = (e X).1 := by unfold PlaneTree.degAt; simpa using h.1
    rw [this]
  simp_rw [hG]
  rw [Equiv.tsum_eq e Gd]
  -- block sums
  have hblk : ∀ p, Summable (fun g : (∀ c : Fin (2 * p + 1), OE (ob_ty t c.val)) => ‖w ⟨p, g⟩‖) ∧
      ∑' g : (∀ c : Fin (2 * p + 1), OE (ob_ty t c.val)), ‖w ⟨p, g⟩‖ =
        ‖ζ‖ * (‖cdf (2 * p + 2)‖ * κ1 ^ (p + 1) * κ2 ^ p) := by
    intro p
    obtain ⟨h1, -, h3⟩ := ob_blk_sums ζ cdf Mf t hC ht p
    have e1 : ∀ g : (∀ c : Fin (2 * p + 1), OE (ob_ty t c.val)), ‖w ⟨p, g⟩‖ =
        ‖ζ‖ * ‖cdf (2 * p + 2)‖ * ‖∏ c, ob_C ζ cdf Mf (g c)‖ := by
      intro g; simp only [w, norm_mul]
    simp_rw [e1]
    refine ⟨h1.mul_left _, ?_⟩
    rw [tsum_mul_left, h3]; ring
  have hwsum : Summable (fun b : OBlk t => ‖w b‖) := by
    rw [summable_sigma_of_nonneg (fun b => norm_nonneg _)]
    refine ⟨fun p => (hblk p).1, ?_⟩
    simp_rw [(hblk _).2]
    exact hη.mul_left _
  have hWabs : ∑' b : OBlk t, ‖w b‖ = ‖ζ‖ * ηabs := by
    rw [Summable.tsum_sigma' (fun p => (hblk p).1) hwsum]
    simp_rw [(hblk _).2]
    rw [tsum_mul_left]
  have hWeq : ∑' b : OBlk t, w b = ζ * ∑' p : ℕ, cdf (2 * p + 2) * m1 ^ (p + 1) * m2 ^ p := by
    rw [Summable.tsum_sigma' (fun p => ((hblk p).1.of_norm)) hwsum.of_norm]
    have : ∀ p, ∑' g : (∀ c : Fin (2 * p + 1), OE (ob_ty t c.val)), w ⟨p, g⟩ =
        ζ * (cdf (2 * p + 2) * m1 ^ (p + 1) * m2 ^ p) := by
      intro p
      obtain ⟨-, h2, -⟩ := ob_blk_sums ζ cdf Mf t hC ht p
      have e1 : ∀ g : (∀ c : Fin (2 * p + 1), OE (ob_ty t c.val)), w ⟨p, g⟩ =
          (ζ * cdf (2 * p + 2)) * ∏ c, ob_C ζ cdf Mf (g c) := fun g => rfl
      simp_rw [e1]
      rw [tsum_mul_left, h2]; ring
    simp_rw [this]
    rw [tsum_mul_left]
  -- the outer sum
  have hnormW : ‖∑' b : OBlk t, w b‖ ≤ ‖ζ‖ * ηabs := by
    rw [← hWabs]; exact norm_tsum_le_tsum_norm hwsum
  have hzW : ‖z * ∑' b : OBlk t, w b‖ < 1 := by
    rw [norm_mul]
    calc ‖z‖ * ‖∑' b : OBlk t, w b‖ ≤ ‖z‖ * (‖ζ‖ * ηabs) :=
          mul_le_mul_of_nonneg_left hnormW (norm_nonneg _)
      _ < 1 := hz
  have hfib : ∀ m : ℕ, Summable (fun f : Fin m → OBlk t => ‖∏ r, w (f r)‖) ∧
      ∑' f : Fin m → OBlk t, ∏ r, w (f r) = (∑' b : OBlk t, w b) ^ m := by
    intro m
    obtain ⟨h1, h2⟩ := ob_pi_tsum m (fun _ => OBlk t) (fun _ b => w b) (fun _ => hwsum)
    refine ⟨h1, ?_⟩
    rw [h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hfibabs : ∀ m : ℕ, ∑' f : Fin m → OBlk t, ‖∏ r, w (f r)‖ = (‖ζ‖ * ηabs) ^ m := by
    intro m
    obtain ⟨-, h2⟩ := ob_pi_tsum (R := ℝ) m (fun _ => OBlk t) (fun _ b => ‖w b‖)
      (fun _ => by simpa only [norm_norm] using hwsum)
    simp_rw [norm_prod]
    rw [h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hWabs]
  have hGsum : Summable (fun d : ODec t => ‖Gd d‖) := by
    rw [summable_sigma_of_nonneg (fun b => norm_nonneg _)]
    have e1 : ∀ (m : ℕ) (f : Fin m → OBlk t), ‖Gd ⟨m, f⟩‖ = ‖z‖ ^ m * ‖ζ‖ * ‖∏ r, w (f r)‖ := by
      intro m f; simp only [Gd, norm_mul, norm_pow]; ring
    refine ⟨fun m => ?_, ?_⟩
    · simp_rw [e1]; exact (hfib m).1.mul_left _
    · simp_rw [e1]
      simp_rw [tsum_mul_left, hfibabs]
      have hκ1 : 0 ≤ κ1 := tsum_nonneg fun _ => norm_nonneg _
      have hκ2 : 0 ≤ κ2 := tsum_nonneg fun _ => norm_nonneg _
      have hη0 : 0 ≤ ηabs := tsum_nonneg fun p =>
        mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hκ1 _)) (pow_nonneg hκ2 _)
      have hg : ‖‖z‖ * (‖ζ‖ * ηabs)‖ < 1 := by
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) hη0))]
        exact hz
      have := (summable_geometric_of_norm_lt_one hg).mul_left ‖ζ‖
      refine this.congr fun m => ?_
      rw [mul_pow]; ring
  rw [Summable.tsum_sigma' (fun m => ((hGsum.sigma_factor m).of_norm)) hGsum.of_norm]
  have e2 : ∀ m : ℕ, ∑' f : Fin m → OBlk t, Gd ⟨m, f⟩ = ζ * (z * ∑' b : OBlk t, w b) ^ m := by
    intro m
    have : ∀ f : Fin m → OBlk t, Gd ⟨m, f⟩ = (z ^ m * ζ) * ∏ r, w (f r) := by
      intro f; simp only [Gd]; ring
    simp_rw [this]
    rw [tsum_mul_left, (hfib m).2, mul_pow]; ring
  simp_rw [e2]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hzW, hWeq]
  rw [div_eq_mul_inv]
  congr 2
  ring

/-! ### The physical weights -/

private noncomputable def ob_cdf {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ)
    (R : ℝ) (g : ℤ → Ω → ℝ) (l : ℕ) (d : ℕ) : ℂ :=
  ((∑ α ∈ cutoffLabels J ℓ, ∫ ω, cutoffXi β ℓ J R l g α ω ^ d ∂P : ℝ) : ℂ)

private noncomputable def ob_Mf {m n : ℕ} (B : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (τ : VType) (d : ℕ) : ℂ :=
  if τ = VType.out then (((B : ℝ)⁻¹ * ∑ i, μ i ^ d : ℝ) : ℂ)
  else (((B : ℝ)⁻¹ * ∑ j, lam j ^ d : ℝ) : ℂ)

private lemma ob_sum_opt_c {m n : ℕ} {L : Finset ℤ} (f : Option (AsgLab m n L) → ℂ) :
    ∑ o, f o = f none + ∑ i : Fin m, f (some (Sum.inl i)) +
      ∑ j : Fin n, f (some (Sum.inr (Sum.inl j))) +
      ∑ α : {α : ℤ // α ∈ L}, f (some (Sum.inr (Sum.inr α))) := by
  rw [Fintype.sum_option, Fintype.sum_sum_type, Fintype.sum_sum_type]; ring

open Classical in
private lemma ob_sub_sum {m n : ℕ} {L : Finset ℤ} (p : Option (AsgLab m n L) → Prop)
    (f : Option (AsgLab m n L) → ℂ) :
    ∑ o : {o // p o}, f o.1 = ∑ o, if p o then f o else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

open Classical in
private lemma ob_vertex_exact {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ)
    (R : ℝ) (B : ℕ) {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (g : ℤ → Ω → ℝ) (l : ℕ)
    {tr : VType} {k : ℕ} (X : RootedTypedTree tr k) (x : AsgLab m n (cutoffLabels J ℓ))
    (u : List ℕ) (hu : u ∈ X.tree.vtxs) (hne : u ≠ []) :
    (∑ o : {o : Option (AsgLab m n (cutoffLabels J ℓ)) //
        AsgCompat (X.ty u) o ∧ (u = [] → o = some x)},
      (if u = [] then ((asgVal μ lam o.1 ^ X.tree.degAt u : ℝ) : ℂ)
      else if X.ty u = VType.lat then
        ((∫ ω, cutoffXi β ℓ J R l g (asgLabel o.1) ω ^ X.tree.degAt u ∂P : ℝ) : ℂ)
      else ((asgVal μ lam o.1 ^ X.tree.degAt u / (B : ℝ) : ℝ) : ℂ))) =
    ob_loc (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) X u := by
  have h := ob_sub_sum (fun o => AsgCompat (X.ty u) o ∧ (u = [] → o = some x))
    (fun o => if u = [] then ((asgVal μ lam o ^ X.tree.degAt u : ℝ) : ℂ)
      else if X.ty u = VType.lat then
        ((∫ ω, cutoffXi β ℓ J R l g (asgLabel o) ω ^ X.tree.degAt u ∂P : ℝ) : ℂ)
      else ((asgVal μ lam o ^ X.tree.degAt u / (B : ℝ) : ℝ) : ℂ))
  beta_reduce at h
  have h3 : (∑ o : {o : Option (AsgLab m n (cutoffLabels J ℓ)) //
        AsgCompat (X.ty u) o ∧ (u = [] → o = some x)},
      (if u = [] then ((asgVal μ lam o.1 ^ X.tree.degAt u : ℝ) : ℂ)
      else if X.ty u = VType.lat then
        ((∫ ω, cutoffXi β ℓ J R l g (asgLabel o.1) ω ^ X.tree.degAt u ∂P : ℝ) : ℂ)
      else ((asgVal μ lam o.1 ^ X.tree.degAt u / (B : ℝ) : ℝ) : ℂ))) =
      ∑ o : Option (AsgLab m n (cutoffLabels J ℓ)),
        (if (AsgCompat (X.ty u) o ∧ (u = [] → o = some x)) then
          (if u = [] then ((asgVal μ lam o ^ X.tree.degAt u : ℝ) : ℂ)
          else if X.ty u = VType.lat then
            ((∫ ω, cutoffXi β ℓ J R l g (asgLabel o) ω ^ X.tree.degAt u ∂P : ℝ) : ℂ)
          else ((asgVal μ lam o ^ X.tree.degAt u / (B : ℝ) : ℝ) : ℂ)) else 0) := by
    convert h
  rw [h3, ob_sum_opt_c]
  clear h h3
  unfold ob_loc ob_cdf ob_Mf
  simp only [hne, if_false, imp_false, not_false_eq_true, and_true]
  cases hty : X.ty u
  · simp [AsgCompat, asgVal, Finset.mul_sum, Complex.ofReal_sum, div_eq_mul_inv, mul_comm]
  · simp [AsgCompat, asgVal, Finset.mul_sum, Complex.ofReal_sum, div_eq_mul_inv, mul_comm]
  · simp [AsgCompat, asgLabel, Complex.ofReal_sum]
    exact Finset.sum_attach (cutoffLabels J ℓ) (fun α => ((∫ ω, cutoffXi β ℓ J R l g α ω ^ X.tree.degAt u ∂P : ℝ) : ℂ))

open Classical in
private lemma ob_tree_val_sum {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ)
    (R : ℝ) (B : ℕ) {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (g : ℤ → Ω → ℝ) (l : ℕ) (t : ℝ)
    {tr : VType} {k : ℕ} (X : RootedTypedTree tr k) (x : AsgLab m n (cutoffLabels J ℓ))
    (hx : AsgCompat tr (some x)) :
    ∑' a : {a : TreeAsg X.tree X.ty m n (cutoffLabels J ℓ) // a.1 [] = some x},
      oneBufVal P β ℓ J R B μ lam g l t X a.1 =
      ((asgVal μ lam (some x) ^ X.tree.degAt [] : ℝ) : ℂ) *
        ob_rest (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) X := by
  have h := ob_tree_asg_factor P β ℓ J R B μ lam g l t X x
  simp only at h
  rw [h]
  clear h
  rw [Finset.prod_coe_sort X.tree.vtxs.toFinset (fun u =>
    ∑ o : {o : Option (AsgLab m n (cutoffLabels J ℓ)) //
        AsgCompat (X.ty u) o ∧ (u = [] → o = some x)},
      (if u = [] then ((asgVal μ lam o.1 ^ X.tree.degAt u : ℝ) : ℂ)
      else if X.ty u = VType.lat then
        ((∫ ω, cutoffXi β ℓ J R l g (asgLabel o.1) ω ^ X.tree.degAt u ∂P : ℝ) : ℂ)
      else ((asgVal μ lam o.1 ^ X.tree.degAt u / (B : ℝ) : ℝ) : ℂ)))]
  have hroot : ([] : List ℕ) ∈ X.tree.vtxs.toFinset := List.mem_toFinset.mpr (ob_pt_root_mem _)
  rw [← Finset.mul_prod_erase _ _ hroot]
  unfold ob_rest
  rw [← Finset.filter_ne']
  have hx' : AsgCompat (X.ty []) (some x) := by rw [X.root_ty]; exact hx
  have hr : (∑ o : {o : Option (AsgLab m n (cutoffLabels J ℓ)) //
        AsgCompat (X.ty []) o ∧ (([] : List ℕ) = [] → o = some x)},
      (if ([] : List ℕ) = [] then ((asgVal μ lam o.1 ^ X.tree.degAt [] : ℝ) : ℂ)
      else if X.ty [] = VType.lat then
        ((∫ ω, cutoffXi β ℓ J R l g (asgLabel o.1) ω ^ X.tree.degAt [] ∂P : ℝ) : ℂ)
      else ((asgVal μ lam o.1 ^ X.tree.degAt [] / (B : ℝ) : ℝ) : ℂ))) =
      ((asgVal μ lam (some x) ^ X.tree.degAt [] : ℝ) : ℂ) := by
    rw [Fintype.sum_eq_single (⟨some x, hx', fun _ => rfl⟩ :
      {o : Option (AsgLab m n (cutoffLabels J ℓ)) //
        AsgCompat (X.ty []) o ∧ (([] : List ℕ) = [] → o = some x)})]
    · simp
    · rintro ⟨o, ho1, ho2⟩ hne
      exact absurd (Subtype.ext (ho2 rfl)) hne
  rw [hr]
  have hv : ∀ u ∈ X.tree.vtxs.toFinset.filter (fun a => a ≠ []),
      (∑ o : {o : Option (AsgLab m n (cutoffLabels J ℓ)) //
        AsgCompat (X.ty u) o ∧ (u = [] → o = some x)},
      (if u = [] then ((asgVal μ lam o.1 ^ X.tree.degAt u : ℝ) : ℂ)
      else if X.ty u = VType.lat then
        ((∫ ω, cutoffXi β ℓ J R l g (asgLabel o.1) ω ^ X.tree.degAt u ∂P : ℝ) : ℂ)
      else ((asgVal μ lam o.1 ^ X.tree.degAt u / (B : ℝ) : ℝ) : ℂ))) =
      ob_loc (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) X u := by
    intro u hu
    simp only [Finset.mem_filter, List.mem_toFinset] at hu
    exact ob_vertex_exact P β ℓ J R B μ lam g l X x u hu.1 hu.2
  rw [Finset.prod_congr rfl hv]
  ring

private lemma ob_G_eq {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ)
    (R : ℝ) (B : ℕ) {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (g : ℤ → Ω → ℝ) (l : ℕ) (t : ℝ)
    (tr : VType) (x : AsgLab m n (cutoffLabels J ℓ)) (hx : AsgCompat tr (some x))
    (hsum : Summable (fun q : OneBufIdx m n J ℓ tr x =>
      ‖oneBufVal P β ℓ J R B μ lam g l t q.2.1 q.2.2.1‖)) :
    oneBufG P β ℓ J R B μ lam g l t tr x =
      ∑' Y : OE tr, ((asgVal μ lam (some x) ^ Y.2.tree.degAt [] : ℝ) : ℂ) *
        ob_rest (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) Y.2 := by
  classical
  unfold oneBufG
  set f : OneBufIdx m n J ℓ tr x → ℂ := fun q => oneBufVal P β ℓ J R B μ lam g l t q.2.1 q.2.2.1
    with hf
  set e := Equiv.sigmaAssoc (fun (k : ℕ) (X : RootedTypedTree tr k) =>
    {a : TreeAsg X.tree X.ty m n (cutoffLabels J ℓ) // a.1 [] = some x}) with he
  rw [← e.tsum_eq f]
  have hs0 : Summable f := Summable.of_norm hsum
  have hs : Summable (f ∘ e) := (Equiv.summable_iff e (f := f)).mpr hs0
  have hfin : ∀ Y : OE tr, Finite {a : TreeAsg Y.2.tree Y.2.ty m n (cutoffLabels J ℓ) // a.1 [] = some x} :=
    fun Y => by
      haveI := ob_finite_asg Y.2.tree Y.2.ty m n (cutoffLabels J ℓ)
      infer_instance
  have h1 : ∑' c, f (e c) = ∑' Y : OE tr, ∑' a, (f ∘ e) ⟨Y, a⟩ :=
    Summable.tsum_sigma' (fun Y => by haveI := hfin Y; exact Summable.of_finite) hs
  rw [h1]
  refine tsum_congr fun Y => ?_
  exact ob_tree_val_sum P β ℓ J R B μ lam g l t Y.2 x hx

private lemma ob_N_sum {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ)
    (R : ℝ) (B : ℕ) {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (g : ℤ → Ω → ℝ) (l : ℕ) (t : ℝ)
    (tr : VType) (x : AsgLab m n (cutoffLabels J ℓ))
    (hsum : Summable (fun q : OneBufIdx m n J ℓ tr x =>
      ‖oneBufVal P β ℓ J R B μ lam g l t q.2.1 q.2.2.1‖)) :
    Summable (fun Y : OE tr => ∑' a : {a : TreeAsg Y.2.tree Y.2.ty m n (cutoffLabels J ℓ) //
        a.1 [] = some x}, ‖oneBufVal P β ℓ J R B μ lam g l t Y.2 a.1‖) ∧
    ∑' Y : OE tr, ∑' a : {a : TreeAsg Y.2.tree Y.2.ty m n (cutoffLabels J ℓ) // a.1 [] = some x},
      ‖oneBufVal P β ℓ J R B μ lam g l t Y.2 a.1‖ =
    ∑' q : OneBufIdx m n J ℓ tr x, ‖oneBufVal P β ℓ J R B μ lam g l t q.2.1 q.2.2.1‖ := by
  classical
  set f : OneBufIdx m n J ℓ tr x → ℝ :=
    fun q => ‖oneBufVal P β ℓ J R B μ lam g l t q.2.1 q.2.2.1‖ with hf
  set e := Equiv.sigmaAssoc (fun (k : ℕ) (X : RootedTypedTree tr k) =>
    {a : TreeAsg X.tree X.ty m n (cutoffLabels J ℓ) // a.1 [] = some x}) with he
  have hs : Summable (f ∘ e) := (Equiv.summable_iff e (f := f)).mpr hsum
  have hfin : ∀ Y : OE tr, Finite {a : TreeAsg Y.2.tree Y.2.ty m n (cutoffLabels J ℓ) //
      a.1 [] = some x} := fun Y => by
    haveI := ob_finite_asg Y.2.tree Y.2.ty m n (cutoffLabels J ℓ)
    infer_instance
  have h1 : ∑' c, f (e c) = ∑' Y : OE tr, ∑' a, (f ∘ e) ⟨Y, a⟩ :=
    Summable.tsum_sigma' (fun Y => by haveI := hfin Y; exact Summable.of_finite) hs
  refine ⟨hs.sigma, ?_⟩
  have h2 : ∑' q, f q = ∑' c, f (e c) := (Equiv.tsum_eq e f).symm
  exact (h1.symm.trans h2.symm).symm ▸ rfl

private lemma ob_C_out {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ)
    (R : ℝ) (B : ℕ) {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (g : ℤ → Ω → ℝ) (l : ℕ) (t : ℝ)
    (Y : OE VType.out) :
    ob_C (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) Y =
      ((B : ℂ))⁻¹ * ∑ i : Fin m, (μ i : ℂ) *
        ∑' a : {a : TreeAsg Y.2.tree Y.2.ty m n (cutoffLabels J ℓ) // a.1 [] = some (Sum.inl i)},
          oneBufVal P β ℓ J R B μ lam g l t Y.2 a.1 := by
  have h : ∀ i : Fin m, ∑' a : {a : TreeAsg Y.2.tree Y.2.ty m n (cutoffLabels J ℓ) //
      a.1 [] = some (Sum.inl i)}, oneBufVal P β ℓ J R B μ lam g l t Y.2 a.1 =
      ((μ i ^ Y.2.tree.degAt [] : ℝ) : ℂ) *
        ob_rest (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) Y.2 := by
    intro i
    exact ob_tree_val_sum P β ℓ J R B μ lam g l t Y.2 (Sum.inl i) (by simp [AsgCompat])
  simp_rw [h]
  unfold ob_C ob_Mf
  simp only [if_true]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_succ]; ring

private lemma ob_C_inp {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ)
    (R : ℝ) (B : ℕ) {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (g : ℤ → Ω → ℝ) (l : ℕ) (t : ℝ)
    (Y : OE VType.inp) :
    ob_C (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) Y =
      ((B : ℂ))⁻¹ * ∑ j : Fin n, (lam j : ℂ) *
        ∑' a : {a : TreeAsg Y.2.tree Y.2.ty m n (cutoffLabels J ℓ) //
            a.1 [] = some (Sum.inr (Sum.inl j))},
          oneBufVal P β ℓ J R B μ lam g l t Y.2 a.1 := by
  have h : ∀ j : Fin n, ∑' a : {a : TreeAsg Y.2.tree Y.2.ty m n (cutoffLabels J ℓ) //
      a.1 [] = some (Sum.inr (Sum.inl j))}, oneBufVal P β ℓ J R B μ lam g l t Y.2 a.1 =
      ((lam j ^ Y.2.tree.degAt [] : ℝ) : ℂ) *
        ob_rest (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) Y.2 := by
    intro j
    exact ob_tree_val_sum P β ℓ J R B μ lam g l t Y.2 (Sum.inr (Sum.inl j)) (by simp [AsgCompat])
  simp_rw [h]
  unfold ob_C ob_Mf
  rw [if_neg (by decide)]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_succ]; ring

private lemma ob_abs_bound {E ι : Type} [Fintype ι] (Cf : E → ℂ) (N : ι → E → ℝ) (c : ι → ℝ)
    (Bi : ℝ) (hB : 0 ≤ Bi) (hN : ∀ i, Summable (N i)) (hN0 : ∀ i Y, 0 ≤ N i Y)
    (hle : ∀ Y, ‖Cf Y‖ ≤ Bi * ∑ i, |c i| * N i Y) :
    Summable (fun Y => ‖Cf Y‖) ∧
      ∑' Y, ‖Cf Y‖ ≤ Bi * ∑ i, |c i| * ∑' Y, N i Y := by
  have hs : Summable (fun Y => Bi * ∑ i, |c i| * N i Y) :=
    (summable_sum (fun i _ => (hN i).mul_left |c i|)).mul_left Bi
  have hsum : Summable (fun Y => ‖Cf Y‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs
  refine ⟨hsum, ?_⟩
  calc ∑' Y, ‖Cf Y‖ ≤ ∑' Y, Bi * ∑ i, |c i| * N i Y := Summable.tsum_le_tsum hle hsum hs
    _ = Bi * ∑ i, |c i| * ∑' Y, N i Y := by
      rw [tsum_mul_left, Summable.tsum_finsetSum (fun i _ => (hN i).mul_left |c i|)]
      simp_rw [tsum_mul_left]

private lemma ob_fin_bound {ι : Type} [Fintype ι] (c S : ι → ℝ) (C s γ Bi : ℝ)
    (hC : ∀ i, |c i| ≤ C) (hS0 : ∀ i, 0 ≤ S i) (hS : ∀ i, S i ≤ s) (hBi : 0 ≤ Bi)
    (hcard : Bi * (Fintype.card ι : ℝ) ≤ γ) (hC0 : 0 ≤ C) (hs : 0 ≤ s) :
    Bi * ∑ i, |c i| * S i ≤ γ * (C * s) := by
  have h1 : ∑ i, |c i| * S i ≤ ∑ _i : ι, C * s :=
    Finset.sum_le_sum fun i _ => mul_le_mul (hC i) (hS i) (hS0 i) hC0
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
  calc Bi * ∑ i, |c i| * S i ≤ Bi * ((Fintype.card ι : ℝ) * (C * s)) :=
        mul_le_mul_of_nonneg_left h1 hBi
    _ = (Bi * (Fintype.card ι : ℝ)) * (C * s) := by ring
    _ ≤ γ * (C * s) := mul_le_mul_of_nonneg_right hcard (mul_nonneg hC0 hs)

private lemma ob_C_bound_out {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ)
    (R : ℝ) (B : ℕ) {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (g : ℤ → Ω → ℝ) (l : ℕ) (t : ℝ)
    (C γ : ℝ) (hC0 : 0 ≤ C) (hγ : 0 ≤ γ) (hμ : ∀ i, |μ i| ≤ C) (hm : (m : ℝ) ≤ γ * B)
    (s : ℝ) (hs : 0 ≤ s)
    (hsum : ∀ i : Fin m, Summable (fun q : OneBufIdx m n J ℓ VType.out (Sum.inl i) =>
      ‖oneBufVal P β ℓ J R B μ lam g l t q.2.1 q.2.2.1‖))
    (hbd : ∀ i : Fin m, ∑' q : OneBufIdx m n J ℓ VType.out (Sum.inl i),
      ‖oneBufVal P β ℓ J R B μ lam g l t q.2.1 q.2.2.1‖ ≤ s) :
    Summable (fun Y : OE VType.out =>
      ‖ob_C (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) Y‖) ∧
    ∑' Y : OE VType.out, ‖ob_C (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) Y‖ ≤
      γ * (C * s) := by
  classical
  let N : Fin m → OE VType.out → ℝ := fun i Y =>
    ∑' a : {a : TreeAsg Y.2.tree Y.2.ty m n (cutoffLabels J ℓ) // a.1 [] = some (Sum.inl i)},
      ‖oneBufVal P β ℓ J R B μ lam g l t Y.2 a.1‖
  have hN := fun i => ob_N_sum P β ℓ J R B μ lam g l t VType.out (Sum.inl i) (hsum i)
  have hfin : ∀ (i : Fin m) (Y : OE VType.out), Finite
      {a : TreeAsg Y.2.tree Y.2.ty m n (cutoffLabels J ℓ) // a.1 [] = some (Sum.inl i)} :=
    fun i Y => by
      haveI := ob_finite_asg Y.2.tree Y.2.ty m n (cutoffLabels J ℓ)
      infer_instance
  have hB0 : (0 : ℝ) ≤ (B : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hle : ∀ Y : OE VType.out,
      ‖ob_C (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) Y‖ ≤
        (B : ℝ)⁻¹ * ∑ i, |μ i| * N i Y := by
    intro Y
    rw [ob_C_out]
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ hB0
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    haveI := hfin i Y
    exact norm_tsum_le_tsum_norm Summable.of_finite
  obtain ⟨h1, h2⟩ := ob_abs_bound _ N μ _ hB0 (fun i => (hN i).1)
    (fun i Y => tsum_nonneg fun _ => norm_nonneg _) hle
  refine ⟨h1, h2.trans ?_⟩
  refine ob_fin_bound μ _ C s γ _ hμ (fun i => ?_) (fun i => ?_) hB0 ?_ hC0 hs
  · exact tsum_nonneg fun Y => tsum_nonneg fun _ => norm_nonneg _
  · rw [(hN i).2]; exact hbd i
  · rw [Fintype.card_fin]
    by_cases hB : (B : ℝ) = 0
    · rw [hB]; simp [hγ]
    · rw [inv_mul_le_iff₀ (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hB))]
      linarith

private lemma ob_C_bound_inp {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ)
    (R : ℝ) (B : ℕ) {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (g : ℤ → Ω → ℝ) (l : ℕ) (t : ℝ)
    (C γ : ℝ) (hC0 : 0 ≤ C) (hγ : 0 ≤ γ) (hμ : ∀ j, |lam j| ≤ C) (hm : (n : ℝ) ≤ γ * B)
    (s : ℝ) (hs : 0 ≤ s)
    (hsum : ∀ i : Fin n, Summable (fun q : OneBufIdx m n J ℓ VType.inp (Sum.inr (Sum.inl i)) =>
      ‖oneBufVal P β ℓ J R B μ lam g l t q.2.1 q.2.2.1‖))
    (hbd : ∀ i : Fin n, ∑' q : OneBufIdx m n J ℓ VType.inp (Sum.inr (Sum.inl i)),
      ‖oneBufVal P β ℓ J R B μ lam g l t q.2.1 q.2.2.1‖ ≤ s) :
    Summable (fun Y : OE VType.inp =>
      ‖ob_C (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) Y‖) ∧
    ∑' Y : OE VType.inp, ‖ob_C (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) Y‖ ≤
      γ * (C * s) := by
  classical
  let N : Fin n → OE VType.inp → ℝ := fun i Y =>
    ∑' a : {a : TreeAsg Y.2.tree Y.2.ty m n (cutoffLabels J ℓ) // a.1 [] = some (Sum.inr (Sum.inl i))},
      ‖oneBufVal P β ℓ J R B μ lam g l t Y.2 a.1‖
  have hN := fun i => ob_N_sum P β ℓ J R B μ lam g l t VType.inp (Sum.inr (Sum.inl i)) (hsum i)
  have hfin : ∀ (i : Fin n) (Y : OE VType.inp), Finite
      {a : TreeAsg Y.2.tree Y.2.ty m n (cutoffLabels J ℓ) // a.1 [] = some (Sum.inr (Sum.inl i))} :=
    fun i Y => by
      haveI := ob_finite_asg Y.2.tree Y.2.ty m n (cutoffLabels J ℓ)
      infer_instance
  have hB0 : (0 : ℝ) ≤ (B : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hle : ∀ Y : OE VType.inp,
      ‖ob_C (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) Y‖ ≤
        (B : ℝ)⁻¹ * ∑ i, |lam i| * N i Y := by
    intro Y
    rw [ob_C_inp]
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ hB0
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    haveI := hfin i Y
    exact norm_tsum_le_tsum_norm Summable.of_finite
  obtain ⟨h1, h2⟩ := ob_abs_bound _ N lam _ hB0 (fun i => (hN i).1)
    (fun i Y => tsum_nonneg fun _ => norm_nonneg _) hle
  refine ⟨h1, h2.trans ?_⟩
  refine ob_fin_bound lam _ C s γ _ hμ (fun i => ?_) (fun i => ?_) hB0 ?_ hC0 hs
  · exact tsum_nonneg fun Y => tsum_nonneg fun _ => norm_nonneg _
  · rw [(hN i).2]; exact hbd i
  · rw [Fintype.card_fin]
    by_cases hB : (B : ℝ) = 0
    · rw [hB]; simp [hγ]
    · rw [inv_mul_le_iff₀ (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hB))]
      linarith

private lemma ob_m_out_eq {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ)
    (R : ℝ) (B : ℕ) {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (g : ℤ → Ω → ℝ) (l : ℕ) (t : ℝ)
    (hsum : ∀ i : Fin m, Summable (fun q : OneBufIdx m n J ℓ VType.out (Sum.inl i) =>
      ‖oneBufVal P β ℓ J R B μ lam g l t q.2.1 q.2.2.1‖)) :
    ob_m (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) VType.out =
      oneBufMo P β ℓ J R B μ lam g l t := by
  classical
  let S : Fin m → OE VType.out → ℂ := fun i Y =>
    ((μ i ^ Y.2.tree.degAt [] : ℝ) : ℂ) *
      ob_rest (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) Y.2
  have hS : ∀ i, Summable (S i) := by
    intro i
    have hN := ob_N_sum P β ℓ J R B μ lam g l t VType.out (Sum.inl i) (hsum i)
    refine Summable.of_norm_bounded hN.1 (fun Y => ?_)
    have hfin : Finite {a : TreeAsg Y.2.tree Y.2.ty m n (cutoffLabels J ℓ) //
        a.1 [] = some (Sum.inl i)} := by
      haveI := ob_finite_asg Y.2.tree Y.2.ty m n (cutoffLabels J ℓ)
      infer_instance
    have := ob_tree_val_sum P β ℓ J R B μ lam g l t Y.2 (Sum.inl i) (by simp [AsgCompat])
    have h2 : S i Y = ∑' a : {a : TreeAsg Y.2.tree Y.2.ty m n (cutoffLabels J ℓ) //
        a.1 [] = some (Sum.inl i)}, oneBufVal P β ℓ J R B μ lam g l t Y.2 a.1 := this.symm
    rw [h2]
    haveI := hfin
    exact norm_tsum_le_tsum_norm Summable.of_finite
  have hC : ∀ Y : OE VType.out,
      ob_C (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) Y =
        ((B : ℂ))⁻¹ * ∑ i : Fin m, (μ i : ℂ) * S i Y := by
    intro Y
    rw [ob_C_out]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact ob_tree_val_sum P β ℓ J R B μ lam g l t Y.2 (Sum.inl i) (by simp [AsgCompat])
  unfold ob_m oneBufMo
  simp_rw [hC]
  rw [tsum_mul_left, Summable.tsum_finsetSum (fun i _ => (hS i).mul_left _)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tsum_mul_left]
  congr 1
  exact (ob_G_eq P β ℓ J R B μ lam g l t VType.out (Sum.inl i) (by simp [AsgCompat]) (hsum i)).symm

private lemma ob_m_inp_eq {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ)
    (R : ℝ) (B : ℕ) {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (g : ℤ → Ω → ℝ) (l : ℕ) (t : ℝ)
    (hsum : ∀ i : Fin n, Summable (fun q : OneBufIdx m n J ℓ VType.inp (Sum.inr (Sum.inl i)) =>
      ‖oneBufVal P β ℓ J R B μ lam g l t q.2.1 q.2.2.1‖)) :
    ob_m (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) VType.inp =
      oneBufMin P β ℓ J R B μ lam g l t := by
  classical
  let S : Fin n → OE VType.inp → ℂ := fun i Y =>
    ((lam i ^ Y.2.tree.degAt [] : ℝ) : ℂ) *
      ob_rest (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) Y.2
  have hS : ∀ i, Summable (S i) := by
    intro i
    have hN := ob_N_sum P β ℓ J R B μ lam g l t VType.inp (Sum.inr (Sum.inl i)) (hsum i)
    refine Summable.of_norm_bounded hN.1 (fun Y => ?_)
    have hfin : Finite {a : TreeAsg Y.2.tree Y.2.ty m n (cutoffLabels J ℓ) //
        a.1 [] = some (Sum.inr (Sum.inl i))} := by
      haveI := ob_finite_asg Y.2.tree Y.2.ty m n (cutoffLabels J ℓ)
      infer_instance
    have := ob_tree_val_sum P β ℓ J R B μ lam g l t Y.2 (Sum.inr (Sum.inl i)) (by simp [AsgCompat])
    have h2 : S i Y = ∑' a : {a : TreeAsg Y.2.tree Y.2.ty m n (cutoffLabels J ℓ) //
        a.1 [] = some (Sum.inr (Sum.inl i))}, oneBufVal P β ℓ J R B μ lam g l t Y.2 a.1 := this.symm
    rw [h2]
    haveI := hfin
    exact norm_tsum_le_tsum_norm Summable.of_finite
  have hC : ∀ Y : OE VType.inp,
      ob_C (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) Y =
        ((B : ℂ))⁻¹ * ∑ i : Fin n, (lam i : ℂ) * S i Y := by
    intro Y
    rw [ob_C_inp]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact ob_tree_val_sum P β ℓ J R B μ lam g l t Y.2 (Sum.inr (Sum.inl i)) (by simp [AsgCompat])
  unfold ob_m oneBufMin
  simp_rw [hC]
  rw [tsum_mul_left, Summable.tsum_finsetSum (fun i _ => (hS i).mul_left _)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tsum_mul_left]
  congr 1
  exact (ob_G_eq P β ℓ J R B μ lam g l t VType.inp (Sum.inr (Sum.inl i)) (by simp [AsgCompat]) (hsum i)).symm

/-! ### The contraction estimate -/

private lemma ob_term_diff (A : ℂ) (s : ℝ) (hA : ‖A‖ = s) (hs : 0 < s) (x C : ℝ) (hx : |x| ≤ C)
    (w1 w2 : ℂ) (h1 : ‖(x : ℂ) * w1‖ ≤ s / 2) (h2 : ‖(x : ℂ) * w2‖ ≤ s / 2) :
    ‖(x : ℂ) / (A - x * w1) - x / (A - x * w2)‖ ≤ 4 * C ^ 2 / s ^ 2 * ‖w1 - w2‖ := by
  have hD1 : s / 2 ≤ ‖A - x * w1‖ := by
    have := norm_sub_norm_le A ((x : ℂ) * w1)
    rw [hA] at this; linarith
  have hD2 : s / 2 ≤ ‖A - x * w2‖ := by
    have := norm_sub_norm_le A ((x : ℂ) * w2)
    rw [hA] at this; linarith
  have hp1 : (A - x * w1) ≠ 0 := by
    intro h; rw [h, norm_zero] at hD1; linarith
  have hp2 : (A - x * w2) ≠ 0 := by
    intro h; rw [h, norm_zero] at hD2; linarith
  have hid : (x : ℂ) / (A - x * w1) - x / (A - x * w2) =
      (x : ℂ) * x * (w1 - w2) / ((A - x * w1) * (A - x * w2)) := by
    field_simp
    ring
  rw [hid, norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mul]
  have hden : (s / 2) * (s / 2) ≤ ‖A - x * w1‖ * ‖A - x * w2‖ :=
    mul_le_mul hD1 hD2 (by positivity) (norm_nonneg _)
  have hpos : 0 < (s / 2) * (s / 2) := by positivity
  rw [div_le_iff₀ (lt_of_lt_of_le hpos hden)]
  have hx2 : |x| * |x| ≤ C ^ 2 := by nlinarith [abs_nonneg x]
  calc |x| * |x| * ‖w1 - w2‖ ≤ C ^ 2 * ‖w1 - w2‖ :=
        mul_le_mul_of_nonneg_right hx2 (norm_nonneg _)
    _ = 4 * C ^ 2 / s ^ 2 * ‖w1 - w2‖ * ((s / 2) * (s / 2)) := by field_simp; norm_num
    _ ≤ 4 * C ^ 2 / s ^ 2 * ‖w1 - w2‖ * (‖A - x * w1‖ * ‖A - x * w2‖) := by
        gcongr

private lemma ob_avg_diff {ι : Type} [Fintype ι] (x : ι → ℝ) (A : ℂ) (s : ℝ) (hA : ‖A‖ = s)
    (hs : 0 < s) (C γ : ℝ) (B : ℕ) (hC0 : 0 ≤ C) (hγ : 0 ≤ γ) (hx : ∀ i, |x i| ≤ C)
    (hcard : (Fintype.card ι : ℝ) ≤ γ * B) (w1 w2 : ℂ) (W : ℝ) (hW : ‖w1 - w2‖ ≤ W)
    (h1 : ∀ i, ‖(x i : ℂ) * w1‖ ≤ s / 2) (h2 : ∀ i, ‖(x i : ℂ) * w2‖ ≤ s / 2) :
    ‖(B : ℂ)⁻¹ * ∑ i, (x i : ℂ) / (A - x i * w1) -
        (B : ℂ)⁻¹ * ∑ i, (x i : ℂ) / (A - x i * w2)‖ ≤ γ * (4 * C ^ 2 / s ^ 2 * W) := by
  have hW0 : 0 ≤ W := le_trans (norm_nonneg _) hW
  have hB0 : (0 : ℝ) ≤ (B : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ i, ((x i : ℂ) / (A - x i * w1) - x i / (A - x i * w2))‖ ≤
      (Fintype.card ι : ℝ) * (4 * C ^ 2 / s ^ 2 * W) := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ i ∈ (Finset.univ : Finset ι), ‖(x i : ℂ) / (A - x i * w1) - x i / (A - x i * w2)‖ ≤
        4 * C ^ 2 / s ^ 2 * W := by
      intro i _
      refine (ob_term_diff A s hA hs (x i) C (hx i) w1 w2 (h1 i) (h2 i)).trans ?_
      exact mul_le_mul_of_nonneg_left hW (by positivity)
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc (B : ℝ)⁻¹ * ‖∑ i, ((x i : ℂ) / (A - x i * w1) - x i / (A - x i * w2))‖
      ≤ (B : ℝ)⁻¹ * ((Fintype.card ι : ℝ) * (4 * C ^ 2 / s ^ 2 * W)) :=
        mul_le_mul_of_nonneg_left hsum hB0
    _ = ((B : ℝ)⁻¹ * (Fintype.card ι : ℝ)) * (4 * C ^ 2 / s ^ 2 * W) := by ring
    _ ≤ γ * (4 * C ^ 2 / s ^ 2 * W) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        by_cases hB : (B : ℝ) = 0
        · rw [hB]; simp [hγ]
        · rw [inv_mul_le_iff₀ (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hB))]
          linarith

private lemma ob_unique {m n B : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (A : ℂ) (s : ℝ)
    (hA : ‖A‖ = s) (hs : 0 < s) (Fs : ℂ → ℂ) (δ K0 K1 C γ : ℝ)
    (hδ : 0 ≤ δ) (hK0 : 0 ≤ K0) (hK1 : 0 ≤ K1) (hC0 : 0 ≤ C) (hγ : 0 ≤ γ)
    (hμ : ∀ i, |μ i| ≤ C) (hlam : ∀ j, |lam j| ≤ C) (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B)
    (hF0 : ∀ w, ‖w‖ ≤ δ ^ 2 → ‖Fs w‖ ≤ K0)
    (hF1 : ∀ w w', ‖w‖ ≤ δ ^ 2 → ‖w'‖ ≤ δ ^ 2 → ‖Fs w - Fs w'‖ ≤ K1 * ‖w - w'‖)
    (hden : C * δ * K0 ≤ s / 2)
    (hL : 4 * γ * C ^ 2 * (K0 + 2 * δ ^ 2 * K1) < s ^ 2)
    (u v u' v' : ℂ) (hu : ‖u‖ ≤ δ) (hv : ‖v‖ ≤ δ) (hu' : ‖u'‖ ≤ δ) (hv' : ‖v'‖ ≤ δ)
    (h1 : u = (B : ℂ)⁻¹ * ∑ i, (μ i : ℂ) / (A - μ i * (v * Fs (u * v))))
    (h2 : v = (B : ℂ)⁻¹ * ∑ j, (lam j : ℂ) / (A - lam j * (u * Fs (u * v))))
    (h1' : u' = (B : ℂ)⁻¹ * ∑ i, (μ i : ℂ) / (A - μ i * (v' * Fs (u' * v'))))
    (h2' : v' = (B : ℂ)⁻¹ * ∑ j, (lam j : ℂ) / (A - lam j * (u' * Fs (u' * v')))) :
    u = u' ∧ v = v' := by
  set e := max ‖u - u'‖ ‖v - v'‖ with he
  have he0 : 0 ≤ e := le_max_of_le_left (norm_nonneg _)
  have huv : ‖u * v‖ ≤ δ ^ 2 := by
    rw [norm_mul, sq]; exact mul_le_mul hu hv (norm_nonneg _) hδ
  have huv' : ‖u' * v'‖ ≤ δ ^ 2 := by
    rw [norm_mul, sq]; exact mul_le_mul hu' hv' (norm_nonneg _) hδ
  have hdiff : ‖u * v - u' * v'‖ ≤ 2 * δ * e := by
    have : u * v - u' * v' = (u - u') * v + u' * (v - v') := by ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖u - u'‖ * ‖v‖ ≤ e * δ :=
      mul_le_mul (le_max_left _ _) hv (norm_nonneg _) he0
    have h2 : ‖u'‖ * ‖v - v'‖ ≤ δ * e :=
      mul_le_mul hu' (le_max_right _ _) (norm_nonneg _) hδ
    linarith
  have hFd : ‖Fs (u * v) - Fs (u' * v')‖ ≤ K1 * (2 * δ * e) :=
    (hF1 _ _ huv huv').trans (mul_le_mul_of_nonneg_left hdiff hK1)
  have hFu := hF0 _ huv
  have hFu' := hF0 _ huv'
  have hWv : ‖v * Fs (u * v) - v' * Fs (u' * v')‖ ≤ (K0 + 2 * δ ^ 2 * K1) * e := by
    have : v * Fs (u * v) - v' * Fs (u' * v') =
        (v - v') * Fs (u * v) + v' * (Fs (u * v) - Fs (u' * v')) := by ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have a1 : ‖v - v'‖ * ‖Fs (u * v)‖ ≤ e * K0 :=
      mul_le_mul (le_max_right _ _) hFu (norm_nonneg _) he0
    have a2 : ‖v'‖ * ‖Fs (u * v) - Fs (u' * v')‖ ≤ δ * (K1 * (2 * δ * e)) :=
      mul_le_mul hv' hFd (norm_nonneg _) hδ
    nlinarith
  have hWu : ‖u * Fs (u * v) - u' * Fs (u' * v')‖ ≤ (K0 + 2 * δ ^ 2 * K1) * e := by
    have : u * Fs (u * v) - u' * Fs (u' * v') =
        (u - u') * Fs (u * v) + u' * (Fs (u * v) - Fs (u' * v')) := by ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have a1 : ‖u - u'‖ * ‖Fs (u * v)‖ ≤ e * K0 :=
      mul_le_mul (le_max_left _ _) hFu (norm_nonneg _) he0
    have a2 : ‖u'‖ * ‖Fs (u * v) - Fs (u' * v')‖ ≤ δ * (K1 * (2 * δ * e)) :=
      mul_le_mul hu' hFd (norm_nonneg _) hδ
    nlinarith
  have hbv : ‖v * Fs (u * v)‖ ≤ δ * K0 := by
    rw [norm_mul]; exact mul_le_mul hv hFu (norm_nonneg _) hδ
  have hbv' : ‖v' * Fs (u' * v')‖ ≤ δ * K0 := by
    rw [norm_mul]; exact mul_le_mul hv' hFu' (norm_nonneg _) hδ
  have hbu : ‖u * Fs (u * v)‖ ≤ δ * K0 := by
    rw [norm_mul]; exact mul_le_mul hu hFu (norm_nonneg _) hδ
  have hbu' : ‖u' * Fs (u' * v')‖ ≤ δ * K0 := by
    rw [norm_mul]; exact mul_le_mul hu' hFu' (norm_nonneg _) hδ
  have hx : ∀ (x : ℝ), |x| ≤ C → ∀ w : ℂ, ‖w‖ ≤ δ * K0 → ‖(x : ℂ) * w‖ ≤ s / 2 := by
    intro x hx w hw
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |x| * ‖w‖ ≤ C * (δ * K0) := mul_le_mul hx hw (norm_nonneg _) hC0
      _ = C * δ * K0 := by ring
      _ ≤ s / 2 := hden
  have r1 : ‖u - u'‖ ≤ γ * (4 * C ^ 2 / s ^ 2 * ((K0 + 2 * δ ^ 2 * K1) * e)) := by
    have := ob_avg_diff (ι := Fin m) μ A s hA hs C γ B hC0 hγ hμ (by simpa using hm) _ _
      _ hWv (fun i => hx _ (hμ i) _ hbv) (fun i => hx _ (hμ i) _ hbv')
    refine le_trans (le_of_eq ?_) this
    conv_lhs => rw [h1, h1']
  have r2 : ‖v - v'‖ ≤ γ * (4 * C ^ 2 / s ^ 2 * ((K0 + 2 * δ ^ 2 * K1) * e)) := by
    have := ob_avg_diff (ι := Fin n) lam A s hA hs C γ B hC0 hγ hlam (by simpa using hn) _ _
      _ hWu (fun i => hx _ (hlam i) _ hbu) (fun i => hx _ (hlam i) _ hbu')
    refine le_trans (le_of_eq ?_) this
    conv_lhs => rw [h2, h2']
  have hLe : e ≤ (4 * γ * C ^ 2 * (K0 + 2 * δ ^ 2 * K1) / s ^ 2) * e := by
    refine max_le ?_ ?_
    · refine r1.trans (le_of_eq ?_); ring
    · refine r2.trans (le_of_eq ?_); ring
  have hLlt : 4 * γ * C ^ 2 * (K0 + 2 * δ ^ 2 * K1) / s ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]; exact hL
  have : e = 0 := by
    by_contra hne
    have hpos : 0 < e := lt_of_le_of_ne he0 (Ne.symm hne)
    nlinarith
  have h3 : ‖u - u'‖ = 0 := le_antisymm (this ▸ le_max_left _ _) (norm_nonneg _)
  have h4 : ‖v - v'‖ = 0 := le_antisymm (this ▸ le_max_right _ _) (norm_nonneg _)
  exact ⟨sub_eq_zero.mp (norm_eq_zero.mp h3), sub_eq_zero.mp (norm_eq_zero.mp h4)⟩

/-! ### The profile power series -/

private noncomputable def ob_Fs (cdf : ℕ → ℂ) (w : ℂ) : ℂ := ∑' p : ℕ, cdf (2 * p + 2) * w ^ p

private lemma ob_pow_diff (w w' : ℂ) (ϑ : ℝ) (hw : ‖w‖ ≤ ϑ) (hw' : ‖w'‖ ≤ ϑ) (p : ℕ) :
    ‖w ^ (p + 1) - w' ^ (p + 1)‖ ≤ (p + 1) * ϑ ^ p * ‖w - w'‖ := by
  have hϑ : 0 ≤ ϑ := le_trans (norm_nonneg _) hw
  induction p with
  | zero => simp
  | succ p ih =>
    have : w ^ (p + 1 + 1) - w' ^ (p + 1 + 1) =
        w * (w ^ (p + 1) - w' ^ (p + 1)) + (w - w') * w' ^ (p + 1) := by ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow]
    have a1 : ‖w‖ * ‖w ^ (p + 1) - w' ^ (p + 1)‖ ≤ ϑ * ((p + 1) * ϑ ^ p * ‖w - w'‖) :=
      mul_le_mul hw ih (norm_nonneg _) hϑ
    have a2 : ‖w - w'‖ * ‖w'‖ ^ (p + 1) ≤ ‖w - w'‖ * ϑ ^ (p + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw' _) (norm_nonneg _)
    push_cast
    have e1 : ϑ * ((p + 1) * ϑ ^ p * ‖w - w'‖) = (p + 1) * ϑ ^ (p + 1) * ‖w - w'‖ := by ring
    have e2 : ‖w - w'‖ * ϑ ^ (p + 1) = ϑ ^ (p + 1) * ‖w - w'‖ := by ring
    linarith

private lemma ob_Fs_bounds (cdf : ℕ → ℂ) (R1 : ℝ) (hR1 : 1 ≤ R1)
    (hcd : ∀ d : ℕ, 1 ≤ d → ‖cdf d‖ ≤ R1 ^ d) (ϑ : ℝ) (hϑ : R1 ^ 2 * ϑ ≤ 1 / 16) :
    (∀ w : ℂ, ‖w‖ ≤ ϑ → Summable (fun p : ℕ => ‖cdf (2 * p + 2) * w ^ p‖) ∧
        ‖ob_Fs cdf w‖ ≤ 16 / 15 * R1 ^ 2) ∧
    (∀ w w' : ℂ, ‖w‖ ≤ ϑ → ‖w'‖ ≤ ϑ →
      ‖ob_Fs cdf w - ob_Fs cdf w'‖ ≤ 8 / 7 * R1 ^ 4 * ‖w - w'‖) := by
  have hR0 : 0 < R1 := by linarith
  have hϑ0 : 0 ≤ ϑ ∨ ϑ < 0 := le_or_gt 0 ϑ
  -- the geometric comparison
  have hterm : ∀ (w : ℂ), ‖w‖ ≤ ϑ → ∀ p : ℕ, ‖cdf (2 * p + 2) * w ^ p‖ ≤ R1 ^ 2 * (1 / 16) ^ p := by
    intro w hw p
    have hϑ' : 0 ≤ ϑ := le_trans (norm_nonneg _) hw
    rw [norm_mul, norm_pow]
    calc ‖cdf (2 * p + 2)‖ * ‖w‖ ^ p ≤ R1 ^ (2 * p + 2) * ϑ ^ p :=
          mul_le_mul (hcd _ (by omega)) (pow_le_pow_left₀ (norm_nonneg _) hw _)
            (by positivity) (by positivity)
      _ = R1 ^ 2 * (R1 ^ 2 * ϑ) ^ p := by rw [mul_pow, pow_add, pow_mul]; ring
      _ ≤ R1 ^ 2 * (1 / 16) ^ p := by
          gcongr
  have hgeom : Summable (fun p : ℕ => R1 ^ 2 * (1 / 16 : ℝ) ^ p) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  refine ⟨fun w hw => ?_, fun w w' hw hw' => ?_⟩
  · have hs : Summable (fun p : ℕ => ‖cdf (2 * p + 2) * w ^ p‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hterm w hw) hgeom
    refine ⟨hs, ?_⟩
    unfold ob_Fs
    calc ‖∑' p : ℕ, cdf (2 * p + 2) * w ^ p‖ ≤ ∑' p : ℕ, ‖cdf (2 * p + 2) * w ^ p‖ :=
          norm_tsum_le_tsum_norm hs
      _ ≤ ∑' p : ℕ, R1 ^ 2 * (1 / 16 : ℝ) ^ p := Summable.tsum_le_tsum (hterm w hw) hs hgeom
      _ = 16 / 15 * R1 ^ 2 := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring
  · have hs := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hterm w hw) hgeom
    have hs' := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hterm w' hw') hgeom
    unfold ob_Fs
    rw [← Summable.tsum_sub hs.of_norm hs'.of_norm]
    have hsd : Summable (fun p : ℕ => cdf (2 * p + 2) * w ^ p - cdf (2 * p + 2) * w' ^ p) :=
      hs.of_norm.sub hs'.of_norm
    have hϑ' : 0 ≤ ϑ := le_trans (norm_nonneg _) hw
    have hb : ∀ p : ℕ, ‖cdf (2 * (p + 1) + 2) * w ^ (p + 1) - cdf (2 * (p + 1) + 2) * w' ^ (p + 1)‖ ≤
        R1 ^ 4 * ‖w - w'‖ * (1 / 8) ^ p := by
      intro p
      rw [← mul_sub, norm_mul]
      have h1 := ob_pow_diff w w' ϑ hw hw' p
      have h2 : ‖cdf (2 * (p + 1) + 2)‖ ≤ R1 ^ (2 * p + 4) := by
        have := hcd (2 * (p + 1) + 2) (by omega)
        rwa [show 2 * (p + 1) + 2 = 2 * p + 4 by ring] at this
      have h3 : ((p : ℝ) + 1) ≤ 2 ^ p := by
        have := Nat.lt_two_pow_self (n := p)
        exact_mod_cast this
      calc ‖cdf (2 * (p + 1) + 2)‖ * ‖w ^ (p + 1) - w' ^ (p + 1)‖
          ≤ R1 ^ (2 * p + 4) * ((p + 1) * ϑ ^ p * ‖w - w'‖) :=
            mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
        _ = R1 ^ 4 * ‖w - w'‖ * ((p + 1) * (R1 ^ 2 * ϑ) ^ p) := by
            rw [mul_pow, pow_add, pow_mul]; ring
        _ ≤ R1 ^ 4 * ‖w - w'‖ * (2 ^ p * (1 / 16) ^ p) := by
            gcongr
        _ = R1 ^ 4 * ‖w - w'‖ * (1 / 8) ^ p := by
            rw [← mul_pow]; norm_num
    have hgeom8 : Summable (fun p : ℕ => R1 ^ 4 * ‖w - w'‖ * (1 / 8 : ℝ) ^ p) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    rw [Summable.tsum_eq_zero_add hsd]
    have h0 : cdf (2 * 0 + 2) * w ^ 0 - cdf (2 * 0 + 2) * w' ^ 0 = 0 := by simp
    rw [h0, zero_add]
    have hsd' : Summable (fun p : ℕ => ‖cdf (2 * (p + 1) + 2) * w ^ (p + 1) -
        cdf (2 * (p + 1) + 2) * w' ^ (p + 1)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hgeom8
    calc ‖∑' p : ℕ, (cdf (2 * (p + 1) + 2) * w ^ (p + 1) - cdf (2 * (p + 1) + 2) * w' ^ (p + 1))‖
        ≤ ∑' p : ℕ, ‖cdf (2 * (p + 1) + 2) * w ^ (p + 1) - cdf (2 * (p + 1) + 2) * w' ^ (p + 1)‖ :=
          norm_tsum_le_tsum_norm hsd'
      _ ≤ ∑' p : ℕ, R1 ^ 4 * ‖w - w'‖ * (1 / 8 : ℝ) ^ p := Summable.tsum_le_tsum hb hsd' hgeom8
      _ = 8 / 7 * R1 ^ 4 * ‖w - w'‖ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring

private lemma ob_cdf_bound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (ℓ J : ℕ) (R : ℝ) (g : ℤ → Ω → ℝ) (l : ℕ) (d : ℕ) (hd : 1 ≤ d) :
    ‖ob_cdf P β ℓ J R g l d‖ ≤ (max 1 R) ^ d := by
  unfold ob_cdf
  rw [Complex.norm_real, Real.norm_eq_abs]
  refine le_trans ?_ (ob_lat_bound P hβ ℓ J R g l d hd)
  exact Finset.abs_sum_le_sum_abs _ _

private lemma ob_xi_meas {Ω : Type} [MeasurableSpace Ω] {g : ℤ → Ω → ℝ}
    (hg : ∀ α, Measurable (g α)) (β : ℝ) (ℓ J : ℕ) (R : ℝ) (l : ℕ) (α : ℤ) :
    Measurable (cutoffXi β ℓ J R l g α) := by
  unfold cutoffXi
  exact measurable_const.mul
    (Measurable.ite (measurableSet_le (hg α).abs measurable_const) (hg α) measurable_const)

private lemma ob_xi_le {Ω : Type} {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (ℓ J : ℕ) (R : ℝ)
    (g : ℤ → Ω → ℝ) (l : ℕ) (α : ℤ) (ω : Ω) :
    |cutoffXi β ℓ J R l g α ω| ≤ max 1 R := by
  have hR1 : (0 : ℝ) ≤ max 1 R := le_trans zero_le_one (le_max_left _ _)
  obtain ⟨h0, h1⟩ := ob_cutoffVarpi_range hβ ℓ J l α
  unfold cutoffXi
  rw [abs_mul, abs_of_nonneg h0]
  calc cutoffVarpi β ℓ J l α * |if |g α ω| ≤ R then g α ω else 0|
      ≤ cutoffVarpi β ℓ J l α * max 1 R := by
        refine mul_le_mul_of_nonneg_left ?_ h0
        split_ifs with h
        · exact h.trans (le_max_right _ _)
        · simpa using hR1
    _ ≤ 1 * max 1 R := mul_le_mul_of_nonneg_right h1 hR1
    _ = max 1 R := one_mul _

private lemma ob_geom_real (y q : ℝ) (hq : |q * y ^ 2| < 1) :
    ∑' p : ℕ, y ^ (2 * p + 2) * (-q) ^ p = y ^ 2 / (1 + q * y ^ 2) := by
  have he : ∀ p : ℕ, y ^ (2 * p + 2) * (-q) ^ p = y ^ 2 * (-(q * y ^ 2)) ^ p := by
    intro p
    rw [show 2 * p + 2 = 2 + 2 * p by omega, pow_add, pow_mul, neg_pow, neg_pow (q * y ^ 2), mul_pow]
    ring
  simp_rw [he]
  rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (by rwa [abs_neg])]
  rw [sub_neg_eq_add, div_eq_mul_inv]

private lemma ob_alpha_series {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) {g : ℤ → Ω → ℝ} (hg : ∀ α, Measurable (g α))
    (ℓ J : ℕ) (R : ℝ) (l : ℕ) (α : ℤ) (q0 : ℝ) (hq : (max 1 R) ^ 2 * |q0| ≤ 1 / 16) :
    HasSum (fun p : ℕ => ∫ ω, cutoffXi β ℓ J R l g α ω ^ (2 * p + 2) * (-q0) ^ p ∂P)
      (∫ ω, cutoffXi β ℓ J R l g α ω ^ 2 / (1 + q0 * cutoffXi β ℓ J R l g α ω ^ 2) ∂P) := by
  have hR1 : (1 : ℝ) ≤ max 1 R := le_max_left _ _
  set ξ := cutoffXi β ℓ J R l g α with hξ
  have hmeas : Measurable ξ := ob_xi_meas hg β ℓ J R l α
  have hle : ∀ ω, |ξ ω| ≤ max 1 R := fun ω => ob_xi_le hβ ℓ J R g l α ω
  have hpt : ∀ (p : ℕ) (ω : Ω), ‖ξ ω ^ (2 * p + 2) * (-q0) ^ p‖ ≤
      (max 1 R) ^ 2 * ((max 1 R) ^ 2 * |q0|) ^ p := by
    intro p ω
    rw [norm_mul, norm_pow, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
    calc |ξ ω| ^ (2 * p + 2) * |q0| ^ p ≤ (max 1 R) ^ (2 * p + 2) * |q0| ^ p :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hle ω) _) (by positivity)
      _ = (max 1 R) ^ 2 * ((max 1 R) ^ 2 * |q0|) ^ p := by
          rw [mul_pow, pow_add, pow_mul]; ring
  have hint : ∀ p : ℕ, Integrable (fun ω => ξ ω ^ (2 * p + 2) * (-q0) ^ p) P := by
    intro p
    refine Integrable.of_bound ?_ ((max 1 R) ^ 2 * ((max 1 R) ^ 2 * |q0|) ^ p)
      (Filter.Eventually.of_forall (hpt p))
    exact ((hmeas.pow_const _).mul_const _).aestronglyMeasurable
  have hsumint : Summable (fun p : ℕ => ∫ ω, ‖ξ ω ^ (2 * p + 2) * (-q0) ^ p‖ ∂P) := by
    have hr0 : 0 ≤ (max 1 R) ^ 2 * |q0| := by positivity
    refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun ω => norm_nonneg _)
      (fun p => ?_) ((summable_geometric_of_lt_one (r := (max 1 R) ^ 2 * |q0|) hr0
        (by linarith)).mul_left ((max 1 R) ^ 2))
    have h := MeasureTheory.norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => ‖ξ ω ^ (2 * p + 2) * (-q0) ^ p‖)
      (C := (max 1 R) ^ 2 * ((max 1 R) ^ 2 * |q0|) ^ p)
      (Filter.Eventually.of_forall fun ω => by rw [norm_norm]; exact hpt p ω)
    rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have h1 := hasSum_integral_of_summable_integral_norm hint hsumint
  convert h1 using 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  symm
  apply ob_geom_real
  rw [abs_mul, abs_pow]
  calc |q0| * |ξ ω| ^ 2 ≤ |q0| * (max 1 R) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hle ω) 2) (abs_nonneg _)
    _ ≤ 1 / 16 := by linarith
    _ < 1 := by norm_num

private lemma ob_Fs_profile {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) {g : ℤ → Ω → ℝ} (hg : ∀ α, Measurable (g α))
    (ℓ J : ℕ) (R : ℝ) (l : ℕ) (q0 : ℝ) (hq : (max 1 R) ^ 2 * |q0| ≤ 1 / 16) :
    ob_Fs (ob_cdf P β ℓ J R g l) ((-q0 : ℝ) : ℂ) =
      ((profileF P (cutoffXi β ℓ J R l g) q0 : ℝ) : ℂ) := by
  have hzero : ∀ α ∉ cutoffLabels J ℓ,
      ∫ ω, cutoffXi β ℓ J R l g α ω ^ 2 / (1 + q0 * cutoffXi β ℓ J R l g α ω ^ 2) ∂P = 0 := by
    intro α hα
    have hv : cutoffVarpi β ℓ J l α = 0 := by unfold cutoffVarpi; rw [if_neg hα]
    have h0 : ∀ ω, cutoffXi β ℓ J R l g α ω = 0 := by
      intro ω; simp [cutoffXi, hv]
    simp [h0]
  have hprof : profileF P (cutoffXi β ℓ J R l g) q0 = ∑ α ∈ cutoffLabels J ℓ,
      ∫ ω, cutoffXi β ℓ J R l g α ω ^ 2 / (1 + q0 * cutoffXi β ℓ J R l g α ω ^ 2) ∂P := by
    unfold profileF
    exact tsum_eq_sum hzero
  have hser := fun α => ob_alpha_series P hβ hg ℓ J R l α q0 hq
  rw [hprof]
  have h1 : ∑ α ∈ cutoffLabels J ℓ,
      ∫ ω, cutoffXi β ℓ J R l g α ω ^ 2 / (1 + q0 * cutoffXi β ℓ J R l g α ω ^ 2) ∂P =
      ∑' p : ℕ, ∑ α ∈ cutoffLabels J ℓ,
        ∫ ω, cutoffXi β ℓ J R l g α ω ^ (2 * p + 2) * (-q0) ^ p ∂P := by
    rw [Summable.tsum_finsetSum (fun α _ => (hser α).summable)]
    exact Finset.sum_congr rfl fun α _ => (hser α).tsum_eq.symm
  rw [h1]
  unfold ob_Fs ob_cdf
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun p => ?_
  have hint : ∀ α, Integrable (fun ω => cutoffXi β ℓ J R l g α ω ^ (2 * p + 2)) P := by
    intro α
    refine Integrable.of_bound ?_ ((max 1 R) ^ (2 * p + 2))
      (Filter.Eventually.of_forall fun ω => ?_)
    · exact ((ob_xi_meas hg β ℓ J R l α).pow_const _).aestronglyMeasurable
    · rw [norm_pow, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (ob_xi_le hβ ℓ J R g l α ω) _
  push_cast
  simp_rw [integral_mul_const]
  push_cast
  rw [Finset.sum_mul]

private lemma ob_eta_bounds (cdf : ℕ → ℂ) (R1 : ℝ) (hR1 : 1 ≤ R1)
    (hcd : ∀ d : ℕ, 1 ≤ d → ‖cdf d‖ ≤ R1 ^ d) (κ1 κ2 δ : ℝ)
    (h10 : 0 ≤ κ1) (h1 : κ1 ≤ δ) (h20 : 0 ≤ κ2) (h2 : κ2 ≤ δ) (hRδ : R1 ^ 2 * δ ^ 2 ≤ 1 / 16) :
    Summable (fun p : ℕ => ‖cdf (2 * p + 2)‖ * κ1 ^ (p + 1) * κ2 ^ p) ∧
    ∑' p : ℕ, ‖cdf (2 * p + 2)‖ * κ1 ^ (p + 1) * κ2 ^ p ≤ 16 / 15 * (R1 ^ 2 * δ) := by
  have hδ0 : 0 ≤ δ := le_trans h10 h1
  have hb : ∀ p : ℕ, ‖cdf (2 * p + 2)‖ * κ1 ^ (p + 1) * κ2 ^ p ≤
      R1 ^ 2 * δ * (1 / 16 : ℝ) ^ p := by
    intro p
    calc ‖cdf (2 * p + 2)‖ * κ1 ^ (p + 1) * κ2 ^ p ≤ R1 ^ (2 * p + 2) * δ ^ (p + 1) * δ ^ p := by
          gcongr
          exact hcd _ (by omega)
      _ = R1 ^ 2 * δ * (R1 ^ 2 * δ ^ 2) ^ p := by
          ring
      _ ≤ R1 ^ 2 * δ * (1 / 16) ^ p := by gcongr
  have hgeom : Summable (fun p : ℕ => R1 ^ 2 * δ * (1 / 16 : ℝ) ^ p) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hnn : ∀ p : ℕ, 0 ≤ ‖cdf (2 * p + 2)‖ * κ1 ^ (p + 1) * κ2 ^ p := fun p => by positivity
  have hs := Summable.of_nonneg_of_le hnn hb hgeom
  refine ⟨hs, ?_⟩
  calc ∑' p : ℕ, ‖cdf (2 * p + 2)‖ * κ1 ^ (p + 1) * κ2 ^ p ≤ ∑' p : ℕ, R1 ^ 2 * δ * (1 / 16 : ℝ) ^ p :=
        Summable.tsum_le_tsum hb hs hgeom
    _ = 16 / 15 * (R1 ^ 2 * δ) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring

private lemma ob_eta_eq (cdf : ℕ → ℂ) (m1 m2 : ℂ) :
    ∑' p : ℕ, cdf (2 * p + 2) * m1 ^ (p + 1) * m2 ^ p = m1 * ob_Fs cdf (m1 * m2) := by
  unfold ob_Fs
  rw [← tsum_mul_left]
  refine tsum_congr fun p => ?_
  rw [mul_pow, pow_succ]; ring

private lemma ob_zeta_res (A z η : ℂ) (hA : A ≠ 0) :
    A⁻¹ / (1 - z * A⁻¹ * η) = (A - z * η)⁻¹ := by
  by_cases h : A - z * η = 0
  · have h1 : 1 - z * A⁻¹ * η = 0 := by
      have : 1 - z * A⁻¹ * η = A⁻¹ * (A - z * η) := by field_simp
      rw [this, h, mul_zero]
    rw [h, h1]; simp
  · have h1 : 1 - z * A⁻¹ * η = A⁻¹ * (A - z * η) := by field_simp
    rw [h1, div_eq_mul_inv, mul_inv, inv_inv]
    field_simp

private lemma ob_both {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (ℓ J : ℕ) (R : ℝ) (B : ℕ) {m n : ℕ} (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (g : ℤ → Ω → ℝ) (l : ℕ) (t : ℝ) (γ C : ℝ) (hγ : 1 ≤ γ) (hC : 1 ≤ C)
    (hμ : ∀ i, |μ i| ≤ C) (hlam : ∀ j, |lam j| ≤ C) (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B)
    (ht : 64 * (γ * C * max 1 R) ^ 2 ≤ t)
    (hsumo : ∀ i : Fin m, Summable (fun q : OneBufIdx m n J ℓ VType.out (Sum.inl i) =>
      ‖oneBufVal P β ℓ J R B μ lam g l t q.2.1 q.2.2.1‖))
    (hbdo : ∀ i : Fin m, ∑' q : OneBufIdx m n J ℓ VType.out (Sum.inl i),
      ‖oneBufVal P β ℓ J R B μ lam g l t q.2.1 q.2.2.1‖ ≤ 2 / Real.sqrt t)
    (hsumi : ∀ j : Fin n, Summable (fun q : OneBufIdx m n J ℓ VType.inp (Sum.inr (Sum.inl j)) =>
      ‖oneBufVal P β ℓ J R B μ lam g l t q.2.1 q.2.2.1‖))
    (hbdi : ∀ j : Fin n, ∑' q : OneBufIdx m n J ℓ VType.inp (Sum.inr (Sum.inl j)),
      ‖oneBufVal P β ℓ J R B μ lam g l t q.2.1 q.2.2.1‖ ≤ 2 / Real.sqrt t) :
    ‖oneBufMo P β ℓ J R B μ lam g l t‖ ≤ 2 * γ * C / Real.sqrt t ∧
    ‖oneBufMin P β ℓ J R B μ lam g l t‖ ≤ 2 * γ * C / Real.sqrt t ∧
    (∀ i : Fin m, oneBufG P β ℓ J R B μ lam g l t VType.out (Sum.inl i) =
      (Complex.I * (Real.sqrt t : ℂ) - μ i * (oneBufMin P β ℓ J R B μ lam g l t *
        ob_Fs (ob_cdf P β ℓ J R g l) (oneBufMo P β ℓ J R B μ lam g l t *
          oneBufMin P β ℓ J R B μ lam g l t)))⁻¹) ∧
    (∀ j : Fin n, oneBufG P β ℓ J R B μ lam g l t VType.inp (Sum.inr (Sum.inl j)) =
      (Complex.I * (Real.sqrt t : ℂ) - lam j * (oneBufMo P β ℓ J R B μ lam g l t *
        ob_Fs (ob_cdf P β ℓ J R g l) (oneBufMo P β ℓ J R B μ lam g l t *
          oneBufMin P β ℓ J R B μ lam g l t)))⁻¹) := by
  classical
  set R1 := max 1 R with hR1def
  have hR1 : 1 ≤ R1 := le_max_left _ _
  set K := γ * C * R1 with hK
  have hK1 : 1 ≤ K := by
    have h1 : 1 ≤ γ * C := by nlinarith
    nlinarith
  have htpos : 0 < t := by nlinarith
  set s := Real.sqrt t with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr htpos
  have hs2 : s ^ 2 = t := Real.sq_sqrt htpos.le
  have hs8 : 8 * K ≤ s := by
    rw [hs]; apply Real.le_sqrt_of_sq_le; nlinarith
  set δ := 2 * γ * C / s with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hRδ : R1 ^ 2 * δ ^ 2 ≤ 1 / 16 := by
    have h1 : R1 * δ = 2 * K / s := by rw [hδ, hK]; field_simp
    have h2 : 2 * K / s ≤ 1 / 4 := by rw [div_le_iff₀ hs0]; linarith
    have h3 : 0 ≤ 2 * K / s := by positivity
    calc R1 ^ 2 * δ ^ 2 = (R1 * δ) ^ 2 := by ring
      _ = (2 * K / s) ^ 2 := by rw [h1]
      _ ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ h3 h2 2
      _ = 1 / 16 := by norm_num
  have hout := ob_C_bound_out P β ℓ J R B μ lam g l t C γ (by linarith) (by linarith) hμ hm
    (2 / s) (by positivity) hsumo hbdo
  have hinp := ob_C_bound_inp P β ℓ J R B μ lam g l t C γ (by linarith) (by linarith) hlam hn
    (2 / s) (by positivity) hsumi hbdi
  set ζ := zetaT t with hζ
  set cdf := ob_cdf P β ℓ J R g l with hcdf
  set Mf := ob_Mf B μ lam with hMf
  have hCsum : ∀ τ, τ ≠ VType.lat → Summable (fun Y : OE τ => ‖ob_C ζ cdf Mf Y‖) := by
    intro τ hτ
    cases τ
    · exact hout.1
    · exact hinp.1
    · exact absurd rfl hτ
  have hδeq : γ * (C * (2 / s)) = δ := by rw [hδ]; ring
  have hκo : ob_κ ζ cdf Mf VType.out ≤ δ := by
    have := hout.2; rw [hδeq] at this; exact this
  have hκi : ob_κ ζ cdf Mf VType.inp ≤ δ := by
    have := hinp.2; rw [hδeq] at this; exact this
  have hκo0 : 0 ≤ ob_κ ζ cdf Mf VType.out := tsum_nonneg fun _ => norm_nonneg _
  have hκi0 : 0 ≤ ob_κ ζ cdf Mf VType.inp := tsum_nonneg fun _ => norm_nonneg _
  have hmo : ‖ob_m ζ cdf Mf VType.out‖ ≤ δ :=
    (norm_tsum_le_tsum_norm (hout.1)).trans hκo
  have hmi : ‖ob_m ζ cdf Mf VType.inp‖ ≤ δ :=
    (norm_tsum_le_tsum_norm (hinp.1)).trans hκi
  have hu : oneBufMo P β ℓ J R B μ lam g l t = ob_m ζ cdf Mf VType.out :=
    (ob_m_out_eq P β ℓ J R B μ lam g l t hsumo).symm
  have hv : oneBufMin P β ℓ J R B μ lam g l t = ob_m ζ cdf Mf VType.inp :=
    (ob_m_inp_eq P β ℓ J R B μ lam g l t hsumi).symm
  have hcd : ∀ d : ℕ, 1 ≤ d → ‖cdf d‖ ≤ R1 ^ d := fun d hd => ob_cdf_bound P hβ ℓ J R g l d hd
  have hzeta : ‖ζ‖ = s⁻¹ := ob_zeta_norm htpos
  have hAne : (Complex.I * (s : ℂ)) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hs0.ne')
  have hζA : ζ = (Complex.I * (s : ℂ))⁻¹ := rfl
  -- smallness of the geometric parameter
  have hzgen : ∀ (x : ℝ), |x| ≤ C → ∀ ηs : ℝ, 0 ≤ ηs → ηs ≤ 16 / 15 * (R1 ^ 2 * δ) →
      ‖(x : ℂ)‖ * (‖ζ‖ * ηs) < 1 := by
    intro x hx ηs hη0 hη1
    rw [Complex.norm_real, Real.norm_eq_abs, hzeta]
    have h1 : |x| * (s⁻¹ * ηs) ≤ C * (s⁻¹ * (16 / 15 * (R1 ^ 2 * δ))) :=
      mul_le_mul hx (mul_le_mul_of_nonneg_left hη1 (by positivity)) (by positivity) (by linarith)
    have h2 : C * (s⁻¹ * (16 / 15 * (R1 ^ 2 * δ))) = 32 / 15 * (γ * C ^ 2 * R1 ^ 2) / s ^ 2 := by
      rw [hδ]; field_simp; ring
    have h3 : γ * C ^ 2 * R1 ^ 2 ≤ K ^ 2 := by
      rw [hK]; nlinarith [mul_nonneg (sub_nonneg.2 hγ) (sq_nonneg (C * R1))]
    have h4 : 64 * K ^ 2 ≤ s ^ 2 := by rw [hs2]; exact ht
    have h5 : 32 / 15 * (γ * C ^ 2 * R1 ^ 2) / s ^ 2 < 1 := by
      rw [div_lt_one (by positivity)]; nlinarith [sq_nonneg K]
    linarith
  have hη_o := ob_eta_bounds cdf R1 hR1 hcd (ob_κ ζ cdf Mf VType.inp) (ob_κ ζ cdf Mf VType.out)
    δ hκi0 hκi hκo0 hκo hRδ
  have hη_i := ob_eta_bounds cdf R1 hR1 hcd (ob_κ ζ cdf Mf VType.out) (ob_κ ζ cdf Mf VType.inp)
    δ hκo0 hκo hκi0 hκi hRδ
  have hnn_o : 0 ≤ ∑' p : ℕ, ‖cdf (2 * p + 2)‖ * ob_κ ζ cdf Mf VType.inp ^ (p + 1) *
      ob_κ ζ cdf Mf VType.out ^ p := tsum_nonneg fun p => by positivity
  have hnn_i : 0 ≤ ∑' p : ℕ, ‖cdf (2 * p + 2)‖ * ob_κ ζ cdf Mf VType.out ^ (p + 1) *
      ob_κ ζ cdf Mf VType.inp ^ p := tsum_nonneg fun p => by positivity
  have hGo : ∀ i : Fin m, oneBufG P β ℓ J R B μ lam g l t VType.out (Sum.inl i) =
      ζ / (1 - (μ i : ℂ) * ζ * ∑' p : ℕ, cdf (2 * p + 2) * ob_m ζ cdf Mf VType.inp ^ (p + 1) *
        ob_m ζ cdf Mf VType.out ^ p) := by
    intro i
    rw [ob_G_eq P β ℓ J R B μ lam g l t VType.out (Sum.inl i) (by simp [AsgCompat]) (hsumo i)]
    rw [← hζ, ← hcdf, ← hMf]
    have e1 : ∀ Y : OE VType.out,
        ((asgVal (L := cutoffLabels J ℓ) μ lam (some (Sum.inl i)) ^ Y.2.tree.degAt [] : ℝ) : ℂ) *
          ob_rest ζ cdf Mf Y.2 = (μ i : ℂ) ^ Y.2.tree.degAt [] * ob_rest ζ cdf Mf Y.2 := by
      intro Y
      change (((μ i) ^ Y.2.tree.degAt [] : ℝ) : ℂ) * _ = _
      simp only [Complex.ofReal_pow]
    simp_rw [e1]
    exact ob_tree_sum ζ cdf Mf VType.out (by decide) hCsum (μ i : ℂ) hη_o.1
      (hzgen (μ i) (hμ i) _ hnn_o hη_o.2)
  have hGi : ∀ j : Fin n, oneBufG P β ℓ J R B μ lam g l t VType.inp (Sum.inr (Sum.inl j)) =
      ζ / (1 - (lam j : ℂ) * ζ * ∑' p : ℕ, cdf (2 * p + 2) * ob_m ζ cdf Mf VType.out ^ (p + 1) *
        ob_m ζ cdf Mf VType.inp ^ p) := by
    intro j
    rw [ob_G_eq P β ℓ J R B μ lam g l t VType.inp (Sum.inr (Sum.inl j)) (by simp [AsgCompat])
      (hsumi j)]
    rw [← hζ, ← hcdf, ← hMf]
    have e1 : ∀ Y : OE VType.inp,
        ((asgVal (L := cutoffLabels J ℓ) μ lam (some (Sum.inr (Sum.inl j))) ^ Y.2.tree.degAt [] : ℝ) : ℂ) *
          ob_rest ζ cdf Mf Y.2 = (lam j : ℂ) ^ Y.2.tree.degAt [] * ob_rest ζ cdf Mf Y.2 := by
      intro Y
      change (((lam j) ^ Y.2.tree.degAt [] : ℝ) : ℂ) * _ = _
      simp only [Complex.ofReal_pow]
    simp_rw [e1]
    exact ob_tree_sum ζ cdf Mf VType.inp (by decide) hCsum (lam j : ℂ) hη_i.1
      (hzgen (lam j) (hlam j) _ hnn_i hη_i.2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hu]; exact hmo.trans (le_of_eq hδ.symm)
  · rw [hv]; exact hmi.trans (le_of_eq hδ.symm)
  · intro i
    rw [hGo i, ob_eta_eq cdf (ob_m ζ cdf Mf VType.inp) (ob_m ζ cdf Mf VType.out), hu, hv,
      mul_comm (ob_m ζ cdf Mf VType.inp) (ob_m ζ cdf Mf VType.out), hζA]
    exact ob_zeta_res _ _ _ hAne
  · intro j
    rw [hGi j, ob_eta_eq cdf (ob_m ζ cdf Mf VType.out) (ob_m ζ cdf Mf VType.inp), hu, hv, hζA]
    exact ob_zeta_res _ _ _ hAne

private lemma ob_sigma_le {ι : Type} [Fintype ι] (x : ι → ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hx0 : ∀ i, 0 ≤ x i)
    (hx : ∀ i, x i ≤ C) (t a γ : ℝ) (B : ℕ) (ht : 0 < t) (ha : 0 ≤ a) (hγ : 0 ≤ γ)
    (hcard : (Fintype.card ι : ℝ) ≤ γ * B) :
    (B : ℝ)⁻¹ * ∑ i, x i / (t + a * x i) ≤ γ * C / t := by
  have hB0 : (0 : ℝ) ≤ (B : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hterm : ∀ i, x i / (t + a * x i) ≤ C / t := by
    intro i
    have h1 : x i / (t + a * x i) ≤ x i / t :=
      div_le_div_of_nonneg_left (hx0 i) ht (by nlinarith [hx0 i])
    exact h1.trans (div_le_div_of_nonneg_right (hx i) ht.le)
  have hsum : ∑ i, x i / (t + a * x i) ≤ (Fintype.card ι : ℝ) * (C / t) := by
    refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc (B : ℝ)⁻¹ * ∑ i, x i / (t + a * x i) ≤ (B : ℝ)⁻¹ * ((Fintype.card ι : ℝ) * (C / t)) :=
        mul_le_mul_of_nonneg_left hsum hB0
    _ = ((B : ℝ)⁻¹ * (Fintype.card ι : ℝ)) * (C / t) := by ring
    _ ≤ γ * (C / t) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        by_cases hB : (B : ℝ) = 0
        · rw [hB]; simp [hγ]
        · rw [inv_mul_le_iff₀ (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hB))]
          linarith
    _ = γ * C / t := by ring

private lemma ob_trace_spectral_resolvent {d : ℕ}
    (A U : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ)
    (hU : Uᵀ * U = 1) (hA : A = U * Matrix.diagonal v * Uᵀ)
    (t a : ℝ) (hd : ∀ i, t + a * v i ≠ 0) :
    (A * (t • (1 : Matrix (Fin d) (Fin d) ℝ) + a • A)⁻¹).trace =
      ∑ i, v i / (t + a * v i) := by
  classical
  have hUU : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have hden : t • (1 : Matrix (Fin d) (Fin d) ℝ) + a • A =
      U * Matrix.diagonal (fun i => t + a * v i) * Uᵀ := by
    have he : Matrix.diagonal (fun i => t + a * v i) =
        t • (1 : Matrix (Fin d) (Fin d) ℝ) + a • Matrix.diagonal v := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
    rw [he, Matrix.mul_add, Matrix.add_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUU, ← hA]
  have hdiag : Matrix.diagonal (fun i => t + a * v i) *
      Matrix.diagonal (fun i => (t + a * v i)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij, hd]
  have hinv : (t • (1 : Matrix (Fin d) (Fin d) ℝ) + a • A)⁻¹ =
      U * Matrix.diagonal (fun i => (t + a * v i)⁻¹) * Uᵀ := by
    apply Matrix.inv_eq_right_inv
    rw [hden]
    calc U * Matrix.diagonal (fun i => t + a * v i) * Uᵀ *
          (U * Matrix.diagonal (fun i => (t + a * v i)⁻¹) * Uᵀ) =
        U * (Matrix.diagonal (fun i => t + a * v i) *
          Matrix.diagonal (fun i => (t + a * v i)⁻¹)) * Uᵀ := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
      _ = 1 := by rw [hdiag, Matrix.mul_one, hUU]
  rw [hinv, hA]
  calc (U * Matrix.diagonal v * Uᵀ *
        (U * Matrix.diagonal (fun i => (t + a * v i)⁻¹) * Uᵀ)).trace =
      (U * (Matrix.diagonal v * Matrix.diagonal (fun i => (t + a * v i)⁻¹)) * Uᵀ).trace := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
    _ = (Matrix.diagonal v * Matrix.diagonal (fun i => (t + a * v i)⁻¹)).trace := by
      rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hU, Matrix.one_mul]
    _ = _ := by simp [Matrix.diagonal_mul_diagonal, div_eq_mul_inv]

private lemma ob_trace_scalar_inv {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    {t : ℝ} (ht : 0 < t) :
    (A * (t • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹).trace = A.trace / t := by
  haveI : Invertible t := invertibleOfNonzero ht.ne'
  rw [Matrix.inv_smul (A := (1 : Matrix (Fin d) (Fin d) ℝ)) t (by simp),
    invOf_eq_inv, inv_one, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_smul]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

private lemma ob_marginal_spec {Ω : Type} [MeasurableSpace Ω] {m n B : ℕ}
    (γstar CSig : ℝ) (Fp : FrozenParams m n B) (hS : SizeFin Fp.C B γstar CSig)
    (hout : Fp.C.Sout ≠ 0) (hin : Fp.C.Sin ≠ 0)
    {P : Measure Ω} [IsProbabilityMeasure P] (ℓ J : ℕ) (R : ℝ)
    {g : ℤ → Ω → ℝ} (hg : IsStdGaussianFamily P g) (l : ℕ) (hl : l = 1 ∨ l = 2)
    (t : ℝ) (ht : 0 < t) :
    IsBranchPoint (profileF P (cutoffXi Fp.β ℓ J R l g)) Fp.C B t
      (marginalBranch P Fp.β ℓ J R Fp.C B l g t) := by
  have hex : ∃ x, IsBranchPoint (profileF P (cutoffXi Fp.β ℓ J R l g)) Fp.C B t x := by
    by_cases hR : 0 < R
    · have hp := lem_app_vol_closed_cutoff_paired Fp.hβ.1 Fp.hβ.2 hR hg (ℓ := ℓ) (J := J)
      have hpl : def_app_vol_closed_profile P (cutoffXi Fp.β ℓ J R l g) := by
        rcases hl with rfl | rfl
        · exact hp.profile₁
        · exact hp.profile₂
      exact (lem_app_vol_closed_branch_ii Fp.hB hpl ht Fp.C hout hin γstar
        (by simpa only [Nat.cast_max] using hS.1)).1.exists
    · have hzero : ∀ α ω, cutoffXi Fp.β ℓ J R l g α ω = 0 := by
        intro α ω
        unfold cutoffXi
        split_ifs with h
        · have hz : g α ω = 0 := abs_eq_zero.mp (le_antisymm (h.trans (le_of_not_gt hR)) (abs_nonneg _))
          simp [hz]
        · simp
      have hF : profileF P (cutoffXi Fp.β ℓ J R l g) = 0 := by
        funext q
        simp [profileF, hzero]
      refine ⟨((B : ℝ)⁻¹ * Fp.C.Sout.trace / t,
        (B : ℝ)⁻¹ * Fp.C.Sin.trace / t, 0, 0), ?_⟩
      simp only [IsBranchPoint, hF, Pi.zero_apply, zero_smul, add_zero]
      have ho := Fp.C.psdOut.trace_nonneg
      have hi := Fp.C.psdIn.trace_nonneg
      refine ⟨by positivity, by positivity, le_rfl, le_rfl, ?_, ?_, by ring, by ring⟩
      · rw [ob_trace_scalar_inv _ ht]; ring
      · rw [ob_trace_scalar_inv _ ht]; ring
  unfold marginalBranch branchPt
  rw [dif_pos hex]
  exact hex.choose_spec


private lemma ob_ii_main {Ω : Type} [MeasurableSpace Ω] {m n B : ℕ}
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) (Fp : FrozenParams m n B)
    (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hout : Fp.C.Sout ≠ 0) (hin : Fp.C.Sin ≠ 0)
    {P : Measure Ω} [IsProbabilityMeasure P] (ℓ J : ℕ) (R : ℝ)
    {g : ℤ → Ω → ℝ} (hg : IsStdGaussianFamily P g) (l : ℕ) (hl : l = 1 ∨ l = 2)
    (t : ℝ) (ht : sRad cert γstar CSig R ≤ t) :
    (∀ i : Fin m,
      oneBufG P Fp.β ℓ J R B S.μ S.lam g l t VType.out (Sum.inl i) =
        -(Complex.I * (Real.sqrt t : ℂ)) /
          ((t : ℂ) + ((marginalBranch P Fp.β ℓ J R Fp.C B l g t).2.2.1 : ℂ) * (S.μ i : ℂ))) ∧
    (∀ j : Fin n,
      oneBufG P Fp.β ℓ J R B S.μ S.lam g l t VType.inp (Sum.inr (Sum.inl j)) =
        -(Complex.I * (Real.sqrt t : ℂ)) /
          ((t : ℂ) + ((marginalBranch P Fp.β ℓ J R Fp.C B l g t).2.2.2 : ℂ) * (S.lam j : ℂ))) := by
  classical
  have hone := lem_app_vol_closed_onebuffer_i cert γstar CSig Fp S hS hout hin ℓ J R hg l hl t ht
  have hS' := hS
  obtain ⟨hS1, hS2, hS3⟩ := hS'
  have hγ : 1 ≤ max 1 γstar := le_max_left _ _
  have hC : 1 ≤ max 1 CSig := le_max_left _ _
  have hμ : ∀ i, |S.μ i| ≤ max 1 CSig := fun i =>
    (ob_abs_eig_le Fp.C.Sout S.uOut (S.μ i) i S.huOut (S.eigOut i)).trans
      (hS2.trans (le_max_right _ _))
  have hlam : ∀ j, |S.lam j| ≤ max 1 CSig := fun j =>
    (ob_abs_eig_le Fp.C.Sin S.vIn (S.lam j) j S.hvIn (S.eigIn j)).trans
      (hS3.trans (le_max_right _ _))
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hmn : ∀ q : ℕ, q ≤ max m n → (q : ℝ) ≤ max 1 γstar * B := fun q hq =>
    ((Nat.cast_le.mpr hq).trans hS1).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hB)
  have hm := hmn m (le_max_left _ _)
  have hn := hmn n (le_max_right _ _)
  have ht' : 64 * (max 1 γstar * max 1 CSig * max 1 R) ^ 2 ≤ t := by
    refine le_trans ?_ ht
    unfold sRad
    refine le_trans (le_of_eq ?_) (le_max_left _ _)
    ring
  have htpos : 0 < t := lt_of_lt_of_le (by positivity)
    (le_trans (le_max_left (64 * (max 1 γstar) ^ 2 * (max 1 CSig) ^ 2 * (max 1 R) ^ 2)
      (2 * (volDR cert R CSig γstar) ^ 2)) ht)
  obtain ⟨hMo, hMi, hGo, hGi⟩ := ob_both P Fp.hβ ℓ J R B S.μ S.lam g l t (max 1 γstar)
    (max 1 CSig) hγ hC hμ hlam hm hn ht' (fun i => (hone.1 i).1) (fun i => (hone.1 i).2)
    (fun j => (hone.2 j).1) (fun j => (hone.2 j).2)
  have hspec := ob_marginal_spec γstar CSig Fp hS hout hin ℓ J R hg l hl t htpos
  rcases hb : marginalBranch P Fp.β ℓ J R Fp.C B l g t with ⟨σ, σ', a, c⟩
  rw [hb] at hspec
  simp only [hb]
  obtain ⟨hσ0, hσ'0, ha0, hc0, hσ, hσ', haF, hcF⟩ := hspec
  rw [ob_trace_spectral_resolvent Fp.C.Sout S.uOut S.μ S.huOut (Sout_eq_spectral S) t a
    (fun i => (add_pos_of_pos_of_nonneg htpos (mul_nonneg ha0 (μ_nonneg S i))).ne')] at hσ
  rw [ob_trace_spectral_resolvent Fp.C.Sin S.vIn S.lam S.hvIn (Sin_eq_spectral S) t c
    (fun j => (add_pos_of_pos_of_nonneg htpos (mul_nonneg hc0 (lam_nonneg S j))).ne')] at hσ'
  have hσC : (σ : ℂ) = (B : ℂ)⁻¹ * ∑ i, (S.μ i : ℂ) / ((t : ℂ) + (a : ℂ) * (S.μ i : ℂ)) := by
    have he := congrArg (fun x : ℝ => (x : ℂ)) hσ
    push_cast at he
    exact he
  have hσ'C : (σ' : ℂ) = (B : ℂ)⁻¹ * ∑ j, (S.lam j : ℂ) / ((t : ℂ) + (c : ℂ) * (S.lam j : ℂ)) := by
    have he := congrArg (fun x : ℝ => (x : ℂ)) hσ'
    push_cast at he
    exact he
  set R1 := max 1 R with hR1def
  have hR1 : 1 ≤ R1 := le_max_left _ _
  set γ := max 1 γstar with hγdef
  set C := max 1 CSig with hCdef
  set K := γ * C * R1 with hK
  have hK1 : 1 ≤ K := by
    have h1 : 1 ≤ γ * C := by nlinarith
    nlinarith
  set s := Real.sqrt t with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr htpos
  have hs2 : s ^ 2 = t := Real.sq_sqrt htpos.le
  have hs8 : 8 * K ≤ s := by
    rw [hs]; apply Real.le_sqrt_of_sq_le; nlinarith
  set δ := 2 * γ * C / s with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hRδ : R1 ^ 2 * δ ^ 2 ≤ 1 / 16 := by
    have h1 : R1 * δ = 2 * K / s := by rw [hδ, hK]; field_simp
    have h2 : 2 * K / s ≤ 1 / 4 := by rw [div_le_iff₀ hs0]; linarith
    have h3 : 0 ≤ 2 * K / s := by positivity
    calc R1 ^ 2 * δ ^ 2 = (R1 * δ) ^ 2 := by ring
      _ = (2 * K / s) ^ 2 := by rw [h1]
      _ ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ h3 h2 2
      _ = 1 / 16 := by norm_num
  set A : ℂ := Complex.I * (s : ℂ) with hAdef
  have hAnorm : ‖A‖ = s := by
    rw [hAdef, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs0]
  have hA2 : A ^ 2 = -(t : ℂ) := by
    rw [hAdef, mul_pow, Complex.I_sq]
    have : (s : ℂ) ^ 2 = (t : ℂ) := by exact_mod_cast hs2
    rw [this]; ring
  have hAne : A ≠ 0 := by
    intro h; rw [h, norm_zero] at hAnorm; linarith
  -- real bounds on the branch coordinates
  have hσle : σ ≤ γ * C / t := by
    rw [hσ]
    exact ob_sigma_le S.μ C (by linarith) (fun i => μ_nonneg S i)
      (fun i => (le_abs_self _).trans (hμ i)) t a γ B htpos ha0 (by linarith) (by simpa using hm)
  have hσ'le : σ' ≤ γ * C / t := by
    rw [hσ']
    exact ob_sigma_le S.lam C (by linarith) (fun j => lam_nonneg S j)
      (fun j => (le_abs_self _).trans (hlam j)) t c γ B htpos hc0 (by linarith) (by simpa using hn)
  set F := profileF P (cutoffXi Fp.β ℓ J R l g) (t * σ * σ') with hFdef
  have hq0nn : 0 ≤ t * σ * σ' := mul_nonneg (mul_nonneg htpos.le hσ0) hσ'0
  have hq0 : R1 ^ 2 * |t * σ * σ'| ≤ 1 / 16 := by
    rw [abs_of_nonneg hq0nn]
    have h1 : t * σ * σ' ≤ t * (γ * C / t) * (γ * C / t) := by
      have := mul_le_mul hσle hσ'le hσ'0 (by positivity)
      calc t * σ * σ' = t * (σ * σ') := by ring
        _ ≤ t * ((γ * C / t) * (γ * C / t)) := mul_le_mul_of_nonneg_left this htpos.le
        _ = t * (γ * C / t) * (γ * C / t) := by ring
    have h2 : t * (γ * C / t) * (γ * C / t) = (γ * C) ^ 2 / t := by field_simp
    have h3 : R1 ^ 2 * ((γ * C) ^ 2 / t) = K ^ 2 / t := by rw [hK]; ring
    have h4 : K ^ 2 / t ≤ 1 / 64 := by
      rw [div_le_iff₀ htpos]; linarith only [ht']
    calc R1 ^ 2 * (t * σ * σ') ≤ R1 ^ 2 * ((γ * C) ^ 2 / t) := by
          refine mul_le_mul_of_nonneg_left (h1.trans (le_of_eq h2)) (by positivity)
      _ = K ^ 2 / t := h3
      _ ≤ 1 / 16 := by linarith
  set cdf := ob_cdf P Fp.β ℓ J R g l with hcdf
  have hFs : ob_Fs cdf ((-(A * σ)) * (-(A * σ'))) = (F : ℂ) := by
    have h1 : (-(A * σ)) * (-(A * σ')) = ((-(t * σ * σ') : ℝ) : ℂ) := by
      push_cast
      have : (-(A * σ)) * (-(A * σ')) = A ^ 2 * σ * σ' := by ring
      rw [this, hA2]; ring
    rw [h1]
    exact ob_Fs_profile P Fp.hβ hg.1 ℓ J R l (t * σ * σ') hq0
  have hRa : ((a / s : ℝ) : ℂ) = (s : ℂ) * σ' * F := by
    have : a / s = s * σ' * F := by
      rw [haF, ← hs2]; field_simp
    rw [this]; push_cast; ring
  have hRc : ((c / s : ℝ) : ℂ) = (s : ℂ) * σ * F := by
    have : c / s = s * σ * F := by
      rw [hcF, ← hs2]; field_simp
    rw [this]; push_cast; ring
  have hvF : (-(A * σ')) * (F : ℂ) = -(Complex.I * ((a / s : ℝ) : ℂ)) := by
    rw [hRa, hAdef]; ring
  have huF : (-(A * σ)) * (F : ℂ) = -(Complex.I * ((c / s : ℝ) : ℂ)) := by
    rw [hRc, hAdef]; ring
  have hden_o : ∀ i, t + a * S.μ i ≠ 0 := fun i =>
    (add_pos_of_pos_of_nonneg htpos (mul_nonneg ha0 (μ_nonneg S i))).ne'
  have hden_i : ∀ j, t + c * S.lam j ≠ 0 := fun j =>
    (add_pos_of_pos_of_nonneg htpos (mul_nonneg hc0 (lam_nonneg S j))).ne'
  have hres_o : ∀ i, ((S.μ i : ℝ) : ℂ) / (A - (S.μ i : ℂ) *
      ((-(A * σ')) * ob_Fs cdf ((-(A * σ)) * (-(A * σ'))))) =
      -A * ((S.μ i : ℂ) / ((t : ℂ) + (a : ℂ) * (S.μ i : ℂ))) := by
    intro i
    rw [hFs, hvF]
    have h := ob_branch_resolvent t a (S.μ i) htpos (hden_o i)
    rw [div_eq_mul_inv]
    change (S.μ i : ℂ) * (Complex.I * (Real.sqrt t : ℂ) - (S.μ i : ℂ) *
      (-(Complex.I * ((a / Real.sqrt t : ℝ) : ℂ))))⁻¹ = _
    rw [h]; ring
  have hres_i : ∀ j, ((S.lam j : ℝ) : ℂ) / (A - (S.lam j : ℂ) *
      ((-(A * σ)) * ob_Fs cdf ((-(A * σ)) * (-(A * σ'))))) =
      -A * ((S.lam j : ℂ) / ((t : ℂ) + (c : ℂ) * (S.lam j : ℂ))) := by
    intro j
    rw [hFs, huF]
    have h := ob_branch_resolvent t c (S.lam j) htpos (hden_i j)
    rw [div_eq_mul_inv]
    change (S.lam j : ℂ) * (Complex.I * (Real.sqrt t : ℂ) - (S.lam j : ℂ) *
      (-(Complex.I * ((c / Real.sqrt t : ℝ) : ℂ))))⁻¹ = _
    rw [h]; ring
  have hfix_u : (-(A * σ) : ℂ) = (B : ℂ)⁻¹ * ∑ i, (S.μ i : ℂ) / (A - (S.μ i : ℂ) *
      ((-(A * σ')) * ob_Fs cdf ((-(A * σ)) * (-(A * σ'))))) := by
    simp_rw [hres_o]
    rw [← Finset.mul_sum]
    calc -(A * (σ : ℂ)) = -A * ((B : ℂ)⁻¹ * ∑ i, (S.μ i : ℂ) / ((t : ℂ) + (a : ℂ) * (S.μ i : ℂ))) := by
          rw [← hσC]; ring
      _ = _ := by ring
  have hfix_v : (-(A * σ') : ℂ) = (B : ℂ)⁻¹ * ∑ j, (S.lam j : ℂ) / (A - (S.lam j : ℂ) *
      ((-(A * σ)) * ob_Fs cdf ((-(A * σ)) * (-(A * σ'))))) := by
    simp_rw [hres_i]
    rw [← Finset.mul_sum]
    calc -(A * (σ' : ℂ)) = -A * ((B : ℂ)⁻¹ * ∑ j, (S.lam j : ℂ) / ((t : ℂ) + (c : ℂ) * (S.lam j : ℂ))) := by
          rw [← hσ'C]; ring
      _ = _ := by ring
  -- the tree sums satisfy the same equations
  have hu1 : oneBufMo P Fp.β ℓ J R B S.μ S.lam g l t = (B : ℂ)⁻¹ * ∑ i, (S.μ i : ℂ) /
      (A - (S.μ i : ℂ) * (oneBufMin P Fp.β ℓ J R B S.μ S.lam g l t *
        ob_Fs cdf (oneBufMo P Fp.β ℓ J R B S.μ S.lam g l t *
          oneBufMin P Fp.β ℓ J R B S.μ S.lam g l t))) := by
    conv_lhs => unfold oneBufMo
    simp_rw [hGo]
    congr 1
  have hv1 : oneBufMin P Fp.β ℓ J R B S.μ S.lam g l t = (B : ℂ)⁻¹ * ∑ j, (S.lam j : ℂ) /
      (A - (S.lam j : ℂ) * (oneBufMo P Fp.β ℓ J R B S.μ S.lam g l t *
        ob_Fs cdf (oneBufMo P Fp.β ℓ J R B S.μ S.lam g l t *
          oneBufMin P Fp.β ℓ J R B S.μ S.lam g l t))) := by
    conv_lhs => unfold oneBufMin
    simp_rw [hGi]
    congr 1
  -- numerical facts for the contraction
  have hcd : ∀ d : ℕ, 1 ≤ d → ‖cdf d‖ ≤ R1 ^ d := fun d hd =>
    ob_cdf_bound P Fp.hβ ℓ J R g l d hd
  obtain ⟨hFb0, hFb1⟩ := ob_Fs_bounds cdf R1 hR1 hcd (δ ^ 2) hRδ
  have h3 : γ * C ^ 2 * R1 ^ 2 ≤ K ^ 2 := by
    rw [hK]
    nlinarith only [mul_nonneg (mul_nonneg (zero_le_one.trans hγ) (sub_nonneg.2 hγ))
      (sq_nonneg (C * R1))]
  have h4 : 64 * K ^ 2 ≤ s ^ 2 := by rw [hs2]; exact ht'
  have hden : C * δ * (16 / 15 * R1 ^ 2) ≤ s / 2 := by
    have e : C * δ * (16 / 15 * R1 ^ 2) = 32 / 15 * (γ * C ^ 2 * R1 ^ 2) / s := by
      rw [hδ]; field_simp; ring
    rw [e, div_le_iff₀ hs0]
    nlinarith only [h3, h4, hs0]
  have hL : 4 * γ * C ^ 2 * (16 / 15 * R1 ^ 2 + 2 * δ ^ 2 * (8 / 7 * R1 ^ 4)) < s ^ 2 := by
    have e1 : 16 / 15 * R1 ^ 2 + 2 * δ ^ 2 * (8 / 7 * R1 ^ 4) ≤ 2 * R1 ^ 2 := by
      have : δ ^ 2 * R1 ^ 4 ≤ R1 ^ 2 / 16 := by
        have := mul_le_mul_of_nonneg_right hRδ (sq_nonneg R1)
        nlinarith only [this]
      nlinarith only [this, sq_nonneg R1]
    have e2 : 4 * γ * C ^ 2 * (16 / 15 * R1 ^ 2 + 2 * δ ^ 2 * (8 / 7 * R1 ^ 4)) ≤
        4 * γ * C ^ 2 * (2 * R1 ^ 2) :=
      mul_le_mul_of_nonneg_left e1 (by positivity)
    nlinarith only [e2, h3, h4, hK1]
  have hnorm_u0 : ‖-(A * (σ : ℂ))‖ ≤ δ := by
    rw [norm_neg, norm_mul, hAnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ0]
    have : s * σ ≤ s * (γ * C / t) := mul_le_mul_of_nonneg_left hσle hs0.le
    have e : s * (γ * C / t) = γ * C / s := by rw [← hs2]; field_simp
    rw [hδ]
    have : 0 ≤ γ * C / s := by positivity
    calc s * σ ≤ γ * C / s := by linarith only [‹s * σ ≤ s * (γ * C / t)›, e]
      _ ≤ 2 * γ * C / s := by
          rw [show 2 * γ * C / s = 2 * (γ * C / s) by ring]; linarith only [this]
  have hnorm_v0 : ‖-(A * (σ' : ℂ))‖ ≤ δ := by
    rw [norm_neg, norm_mul, hAnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ'0]
    have : s * σ' ≤ s * (γ * C / t) := mul_le_mul_of_nonneg_left hσ'le hs0.le
    have e : s * (γ * C / t) = γ * C / s := by rw [← hs2]; field_simp
    rw [hδ]
    have : 0 ≤ γ * C / s := by positivity
    calc s * σ' ≤ γ * C / s := by linarith only [‹s * σ' ≤ s * (γ * C / t)›, e]
      _ ≤ 2 * γ * C / s := by
          rw [show 2 * γ * C / s = 2 * (γ * C / s) by ring]; linarith only [this]
  obtain ⟨huu, hvv⟩ := ob_unique S.μ S.lam A s hAnorm hs0 (ob_Fs cdf) δ (16 / 15 * R1 ^ 2)
    (8 / 7 * R1 ^ 4) C γ hδ0 (by positivity) (by positivity) (by linarith) (by linarith) hμ hlam
    hm hn (fun w hw => (hFb0 w hw).2) (fun w w' hw hw' => hFb1 w w' hw hw') hden hL
    (oneBufMo P Fp.β ℓ J R B S.μ S.lam g l t) (oneBufMin P Fp.β ℓ J R B S.μ S.lam g l t)
    (-(A * (σ : ℂ))) (-(A * (σ' : ℂ))) hMo hMi hnorm_u0 hnorm_v0 hu1 hv1 hfix_u hfix_v
  refine ⟨fun i => ?_, fun j => ?_⟩
  · rw [hGo i, huu, hvv, hFs, hvF]
    exact ob_branch_resolvent t a (S.μ i) htpos (hden_o i)
  · rw [hGi j, huu, hvv, hFs, huF]
    exact ob_branch_resolvent t c (S.lam j) htpos (hden_i j)

/-- `lem:app-vol-closed-onebuffer`(ii), snapshot `cr-2026-10-23`. Declaration of record, the two formulas
`g_{o,l}(i) = -i√t/(t + s̃_{1,l} μ_i)` and `g_{in,l}(j) = -i√t/(t + s_{1,l} λ_j)`, where
`(σ_l, σ̃_l, s̃_{1,l}, s_{1,l})` is the marginal branch point of `marginalBranch`.

LaTeX (`sections/04-volatility/section.tex` l.2234–2248, verbatim):
```latex
\begin{lemma}[One-buffer sums are the branch]\label{lem:app-vol-closed-onebuffer}
Let $\Sigmaout,\Sigmain\ne0$, fix $l\in\{1,2\}$ and $t\ge s_R$, use the corner weight
$\zeta_l=(i\sqrt t)^{-1}$, and let $(\sigma_l,\tilde\sigma_l,\tilde s_{1,l},s_{1,l})$ be the branch
point of the marginal profile $\xi_l$ at $t$, with $q_l=t\sigma_l\tilde\sigma_l$. Then the
families defining $g_{\mathsf t,l}$ are absolutely summable,
\[
\sum_X\sum_{\mathfrak a:\mathfrak a(\mathrm{root})=i}\abs{\operatorname{val}_l(X,\mathfrak a)}\le\frac2{\sqrt t},
\]
and
\[
g_{\mathrm o,l}(i)=\frac{-i\sqrt t}{t+\tilde s_{1,l}\mu_i},\qquad g_{\mathrm{in},l}(j)=\frac{-i\sqrt t}{t+s_{1,l}\lambda_j},\qquad
m_{\mathrm o,l}=-i\sqrt t\,\sigma_l,\qquad m_{\mathrm{in},l}=-i\sqrt t\,\tilde\sigma_l,
\]
so that $-m_{\mathrm o,l}m_{\mathrm{in},l}=q_l$.
\end{lemma}
```
-/
theorem lem_app_vol_closed_onebuffer_ii {Ω : Type} [MeasurableSpace Ω] {m n B : ℕ}
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) (Fp : FrozenParams m n B)
    (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hout : Fp.C.Sout ≠ 0) (hin : Fp.C.Sin ≠ 0)
    {P : Measure Ω} [IsProbabilityMeasure P] (ℓ J : ℕ) (R : ℝ)
    {g : ℤ → Ω → ℝ} (hg : IsStdGaussianFamily P g) (l : ℕ) (hl : l = 1 ∨ l = 2)
    (t : ℝ) (ht : sRad cert γstar CSig R ≤ t) :
    (∀ i : Fin m,
      oneBufG P Fp.β ℓ J R B S.μ S.lam g l t VType.out (Sum.inl i) =
        -(Complex.I * (Real.sqrt t : ℂ)) /
          ((t : ℂ) + ((marginalBranch P Fp.β ℓ J R Fp.C B l g t).2.2.1 : ℂ) * (S.μ i : ℂ))) ∧
    (∀ j : Fin n,
      oneBufG P Fp.β ℓ J R B S.μ S.lam g l t VType.inp (Sum.inr (Sum.inl j)) =
        -(Complex.I * (Real.sqrt t : ℂ)) /
          ((t : ℂ) + ((marginalBranch P Fp.β ℓ J R Fp.C B l g t).2.2.2 : ℂ) * (S.lam j : ℂ))) := by
  exact ob_ii_main cert γstar CSig Fp S hS hout hin ℓ J R hg l hl t ht


/-- `lem:app-vol-closed-onebuffer`(iii), snapshot `cr-2026-10-23`. Declaration of record, the traces
`m_{o,l} = -i√t σ_l`, `m_{in,l} = -i√t σ̃_l` and the identity `-m_{o,l} m_{in,l} = q_l = t σ_l σ̃_l`.

LaTeX (`sections/04-volatility/section.tex` l.2234–2248, verbatim):
```latex
\begin{lemma}[One-buffer sums are the branch]\label{lem:app-vol-closed-onebuffer}
Let $\Sigmaout,\Sigmain\ne0$, fix $l\in\{1,2\}$ and $t\ge s_R$, use the corner weight
$\zeta_l=(i\sqrt t)^{-1}$, and let $(\sigma_l,\tilde\sigma_l,\tilde s_{1,l},s_{1,l})$ be the branch
point of the marginal profile $\xi_l$ at $t$, with $q_l=t\sigma_l\tilde\sigma_l$. Then the
families defining $g_{\mathsf t,l}$ are absolutely summable,
\[
\sum_X\sum_{\mathfrak a:\mathfrak a(\mathrm{root})=i}\abs{\operatorname{val}_l(X,\mathfrak a)}\le\frac2{\sqrt t},
\]
and
\[
g_{\mathrm o,l}(i)=\frac{-i\sqrt t}{t+\tilde s_{1,l}\mu_i},\qquad g_{\mathrm{in},l}(j)=\frac{-i\sqrt t}{t+s_{1,l}\lambda_j},\qquad
m_{\mathrm o,l}=-i\sqrt t\,\sigma_l,\qquad m_{\mathrm{in},l}=-i\sqrt t\,\tilde\sigma_l,
\]
so that $-m_{\mathrm o,l}m_{\mathrm{in},l}=q_l$.
\end{lemma}
```
-/
theorem lem_app_vol_closed_onebuffer_iii {Ω : Type} [MeasurableSpace Ω] {m n B : ℕ}
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) (Fp : FrozenParams m n B)
    (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hout : Fp.C.Sout ≠ 0) (hin : Fp.C.Sin ≠ 0)
    {P : Measure Ω} [IsProbabilityMeasure P] (ℓ J : ℕ) (R : ℝ)
    {g : ℤ → Ω → ℝ} (hg : IsStdGaussianFamily P g) (l : ℕ) (hl : l = 1 ∨ l = 2)
    (t : ℝ) (ht : sRad cert γstar CSig R ≤ t) :
    oneBufMo P Fp.β ℓ J R B S.μ S.lam g l t =
        -(Complex.I * (Real.sqrt t : ℂ)) * ((marginalBranch P Fp.β ℓ J R Fp.C B l g t).1 : ℂ) ∧
    oneBufMin P Fp.β ℓ J R B S.μ S.lam g l t =
        -(Complex.I * (Real.sqrt t : ℂ)) * ((marginalBranch P Fp.β ℓ J R Fp.C B l g t).2.1 : ℂ) ∧
    -(oneBufMo P Fp.β ℓ J R B S.μ S.lam g l t * oneBufMin P Fp.β ℓ J R B S.μ S.lam g l t) =
        ((t * (marginalBranch P Fp.β ℓ J R Fp.C B l g t).1 *
          (marginalBranch P Fp.β ℓ J R Fp.C B l g t).2.1 : ℝ) : ℂ) := by
  classical
  have htpos : 0 < t := lt_of_lt_of_le (by positivity)
    (le_trans (le_max_left (64 * (max 1 γstar) ^ 2 * (max 1 CSig) ^ 2 * (max 1 R) ^ 2)
      (2 * (volDR cert R CSig γstar) ^ 2)) ht)
  have hspec := ob_marginal_spec γstar CSig Fp hS hout hin ℓ J R hg l hl t htpos
  obtain ⟨hgo, hgi⟩ := lem_app_vol_closed_onebuffer_ii cert γstar CSig Fp S hS hout hin
    ℓ J R hg l hl t ht
  rcases hb : marginalBranch P Fp.β ℓ J R Fp.C B l g t with ⟨σ, σ', a, c⟩
  rw [hb] at hspec
  simp only [hb] at hgo hgi ⊢
  obtain ⟨hσ0, hσ'0, ha0, hc0, hσ, hσ', -, -⟩ := hspec
  rw [ob_trace_spectral_resolvent Fp.C.Sout S.uOut S.μ S.huOut (Sout_eq_spectral S) t a
    (fun i => (add_pos_of_pos_of_nonneg htpos (mul_nonneg ha0 (μ_nonneg S i))).ne')] at hσ
  rw [ob_trace_spectral_resolvent Fp.C.Sin S.vIn S.lam S.hvIn (Sin_eq_spectral S) t c
    (fun j => (add_pos_of_pos_of_nonneg htpos (mul_nonneg hc0 (lam_nonneg S j))).ne')] at hσ'
  have hσC : (σ : ℂ) = (B : ℂ)⁻¹ * ∑ i, (S.μ i : ℂ) / ((t : ℂ) + (a : ℂ) * (S.μ i : ℂ)) := by
    have he := congrArg (fun x : ℝ => (x : ℂ)) hσ
    push_cast at he
    exact he
  have hσ'C : (σ' : ℂ) = (B : ℂ)⁻¹ * ∑ j, (S.lam j : ℂ) / ((t : ℂ) + (c : ℂ) * (S.lam j : ℂ)) := by
    have he := congrArg (fun x : ℝ => (x : ℂ)) hσ'
    push_cast at he
    exact he
  have hmo : oneBufMo P Fp.β ℓ J R B S.μ S.lam g l t =
      -(Complex.I * (Real.sqrt t : ℂ)) * (σ : ℂ) := by
    unfold oneBufMo
    simp_rw [hgo]
    rw [hσC, mul_left_comm]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hmi : oneBufMin P Fp.β ℓ J R B S.μ S.lam g l t =
      -(Complex.I * (Real.sqrt t : ℂ)) * (σ' : ℂ) := by
    unfold oneBufMin
    simp_rw [hgi]
    rw [hσ'C, mul_left_comm]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  refine ⟨hmo, hmi, ?_⟩
  rw [hmo, hmi]
  have hsqrt : (Real.sqrt t : ℂ) ^ 2 = (t : ℂ) := by
    exact_mod_cast Real.sq_sqrt htpos.le
  push_cast
  calc -(-(Complex.I * (Real.sqrt t : ℂ)) * (σ : ℂ) *
      (-(Complex.I * (Real.sqrt t : ℂ)) * (σ' : ℂ))) =
      -(Complex.I ^ 2) * (Real.sqrt t : ℂ) ^ 2 * (σ : ℂ) * (σ' : ℂ) := by ring
    _ = _ := by rw [Complex.I_sq, hsqrt]; ring


private lemma pd_tree_monomial {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ)
    (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (a b : ℕ) :
    def_app_vol_tree β ℓ J R B μ lam Fd Gd
        (Polynomial.X ^ (2 * a + 1)) (Polynomial.X ^ (2 * b + 1)) =
      treeMono β ℓ J R B μ lam Fd Gd a b := by
  unfold def_app_vol_tree
  rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow]
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp [Polynomial.coeff_X_pow]
  · intro b' _ hb'
    simp [Polynomial.coeff_X_pow, hb']
  · intro hb; exfalso; apply hb; simp; omega
  · intro a' _ ha'
    apply Finset.sum_eq_zero
    intro b' _
    simp [Polynomial.coeff_X_pow, ha']
  · intro ha; exfalso; apply ha; simp; omega

private lemma pd_arcEven_left (a : ℕ) : arcEven 0 (2 * (2 * a + 1)) = 2 * a + 2 := by
  unfold arcEven
  rw [show (Finset.Icc 0 (2 * (2 * a + 1))).filter (fun τ => τ % 2 = 0) =
      Finset.image (fun r => 2 * r) (Finset.Icc 0 (2 * a + 1)) by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h0, hτ⟩, he⟩
      refine ⟨τ / 2, ⟨by omega, by omega⟩, ?_⟩
      omega
    · rintro ⟨r, ⟨hr0, hr⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, by omega⟩]
  rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Nat.card_Icc]
  omega

private lemma pd_arcEven_right (a b : ℕ) :
    arcEven (2 * (2 * a + 1)) (2 * treeK a b) = 2 * b + 2 := by
  unfold arcEven
  rw [show (Finset.Icc (2 * (2 * a + 1)) (2 * treeK a b)).filter (fun τ => τ % 2 = 0) =
      Finset.image (fun r => 2 * r) (Finset.Icc (2 * a + 1) (treeK a b)) by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, he⟩
      refine ⟨τ / 2, ⟨by omega, by omega⟩, ?_⟩
      omega
    · rintro ⟨r, ⟨hrlo, hrhi⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, by omega⟩]
  rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Nat.card_Icc]
  unfold treeK
  omega

private lemma pd_pathZ_norm (s u : ℝ) (a b : ℕ) (hs : 0 < s) (hu : 0 < u) :
    ‖pathZ s u (a, b)‖ =
      (Real.sqrt s)⁻¹ ^ (2 * a + 2) * (Real.sqrt u)⁻¹ ^ (2 * b + 2) := by
  rw [pathZ, norm_mul, norm_pow, norm_pow, pd_arcEven_left, pd_arcEven_right,
    ob_zeta_norm hs, ob_zeta_norm hu]

private lemma pd_zeta_even (t : ℝ) (a : ℕ) (ht : 0 < t) :
    zetaT t ^ (2 * a + 2) = (((-1 : ℝ) ^ (a + 1) * t⁻¹ ^ (a + 1) : ℝ) : ℂ) := by
  have hsqrt : (Real.sqrt t : ℂ) ^ 2 = (t : ℂ) := by
    exact_mod_cast Real.sq_sqrt ht.le
  have hz : zetaT t ^ 2 = -((t⁻¹ : ℝ) : ℂ) := by
    unfold zetaT
    rw [inv_pow]
    rw [show (Complex.I * (Real.sqrt t : ℂ)) ^ 2 = -(t : ℂ) by
      rw [mul_pow, Complex.I_sq, hsqrt]; ring]
    push_cast
    rw [inv_neg]
  rw [show 2 * a + 2 = 2 * (a + 1) by omega, pow_mul, hz]
  push_cast
  ring

private lemma pd_pathZ_eq (s u : ℝ) (a b : ℕ) (hs : 0 < s) (hu : 0 < u) :
    pathZ s u (a, b) =
      ((((-1 : ℝ) ^ (a + b) * s⁻¹ ^ (a + 1) * u⁻¹ ^ (b + 1) : ℝ)) : ℂ) := by
  rw [pathZ, pd_arcEven_left, pd_arcEven_right, pd_zeta_even s a hs, pd_zeta_even u b hu]
  push_cast
  rw [show (-1 : ℂ) ^ (a + b) = (-1 : ℂ) ^ (a + 1) * (-1 : ℂ) ^ (b + 1) by
    rw [pow_add, pow_succ, pow_succ]; ring]
  ring

private lemma pd_sRad_pos (cert : Muon.External.GaussianOpNorm) (γstar CSig R s : ℝ)
    (hs : sRad cert γstar CSig R ≤ s) : 0 < s := by
  have hbase : 0 < 64 * (max 1 γstar) ^ 2 * (max 1 CSig) ^ 2 * (max 1 R) ^ 2 := by
    positivity
  unfold sRad at hs
  exact hbase.trans_le ((le_max_left _ _).trans hs)

private lemma pd_volDR_sq_lt (cert : Muon.External.GaussianOpNorm) (γstar CSig R s : ℝ)
    (hs : sRad cert γstar CSig R ≤ s) : (volDR cert R CSig γstar) ^ 2 < s := by
  have hbase : 0 < 64 * (max 1 γstar) ^ 2 * (max 1 CSig) ^ 2 * (max 1 R) ^ 2 := by
    positivity
  have hright : 2 * (volDR cert R CSig γstar) ^ 2 ≤ s := by
    exact (le_max_right _ _).trans hs
  by_cases hD : volDR cert R CSig γstar = 0
  · rw [hD, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    exact hbase.trans_le ((le_max_left _ _).trans hs)
  · have hD2 : 0 < (volDR cert R CSig γstar) ^ 2 := sq_pos_of_ne_zero hD
    linarith

open Classical in
private lemma pd_asg_prod_sum {m n : ℕ} {L : Finset ℤ} (P : PlaneTree)
    (ty : List ℕ → VType) (W : List ℕ → Option (AsgLab m n L) → ℂ) :
    (∑' a : TreeAsg P ty m n L, ∏ u ∈ P.vtxs.toFinset, W u (a.1 u)) =
      ∏ u : {u // u ∈ P.vtxs.toFinset},
        ∑ o : {o : Option (AsgLab m n L) // AsgCompat (ty u.1) o}, W u.1 o.1 := by
  let V := {u // u ∈ P.vtxs.toFinset}
  let D := fun u : V => {o : Option (AsgLab m n L) // AsgCompat (ty u.1) o}
  haveI : Finite (TreeAsg P ty m n L) := ob_finite_asg _ _ _ _ _
  letI : Fintype (TreeAsg P ty m n L) := Fintype.ofFinite _
  let e : TreeAsg P ty m n L ≃ ((u : V) → D u) := {
    toFun := fun a u => ⟨a.1 u.1, a.2.2 _ (List.mem_toFinset.mp u.2)⟩
    invFun := fun f => ⟨fun u => if hu : u ∈ P.vtxs.toFinset then (f ⟨u, hu⟩).1 else none,
      by
        intro u
        dsimp only
        by_cases hu : u ∈ P.vtxs.toFinset
        · rw [dif_pos hu]
          exact iff_of_true (List.mem_toFinset.mp hu) (ob_compat_ne_none (f ⟨u, hu⟩).2)
        · simp only [dif_neg hu, ne_eq, not_true_eq_false, iff_false]
          simpa only [List.mem_toFinset] using hu,
      by
        intro u hu
        have hu' : u ∈ P.vtxs.toFinset := List.mem_toFinset.mpr hu
        simpa only [dif_pos hu'] using (f ⟨u, hu'⟩).2⟩
    left_inv := by
      intro a
      apply Subtype.ext
      funext u
      dsimp only
      by_cases hu : u ∈ P.vtxs.toFinset
      · exact dif_pos hu
      · rw [dif_neg hu]
        symm
        by_contra h
        exact hu (List.mem_toFinset.mpr ((a.2.1 u).mpr h))
    right_inv := by
      intro f
      funext u
      apply Subtype.ext
      exact dif_pos u.2 }
  rw [tsum_fintype]
  calc ∑ a : TreeAsg P ty m n L, ∏ u ∈ P.vtxs.toFinset, W u (a.1 u) =
      ∑ f : ((u : V) → D u), ∏ u : V, W u.1 (f u).1 := by
        apply Fintype.sum_equiv e
        intro a
        exact (Finset.prod_coe_sort P.vtxs.toFinset (fun u => W u (a.1 u))).symm
    _ = _ := (Fintype.prod_sum (fun (u : V) (o : D u) => W u.1 o.1)).symm

private lemma pd_pathVal_prod {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) {m n : ℕ}
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (g : ℤ → Ω → ℝ) (p : ℕ × ℕ) (T : TypedTrees p.1 p.2)
    (a : TreeAsg T.tree T.ty m n (cutoffLabels J ℓ)) :
    pathVal P β ℓ J R B Fd Gd μ lam g p T a =
      ∏ v ∈ T.tree.vtxs.toFinset,
        if T.ty v ≠ VType.lat then
          (((asgVal μ lam (a.1 v) ^ T.tree.degAt v / (B : ℝ)) *
            (if v = [] then asgVal Fd (fun _ : Fin n => (0 : ℝ)) (a.1 v) else 1) *
            (if v = T.tree.contour.getD (2 * (2 * p.1 + 1)) [] then
              asgVal (fun _ : Fin m => (0 : ℝ)) Gd (a.1 v) else 1) : ℝ) : ℂ)
        else
          ((∫ ω, (∏ τ ∈ (Finset.range (2 * treeK p.1 p.2)).filter
              (fun τ => τ % 2 = 1 ∧ T.tree.contour.getD τ [] = v),
            cutoffXi β ℓ J R (cornerLabel p.1 τ) g (asgLabel (a.1 v)) ω) ∂P : ℝ) : ℂ) := by
  classical
  unfold pathVal
  rw [Finset.prod_filter, Finset.prod_filter, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v hv
  by_cases hlat : T.ty v = VType.lat
  · simp [hlat]
  · simp [hlat]

/-! ## Retained-pairing bridge -/

/-! ### Contour typing (copied privately from `Closed/Trees.lean`, names prefixed `pd_`) -/

private def pd_inc : List ℕ → List ℕ
  | [] => []
  | a :: u => (a + 1) :: u

private theorem pd_inc_ne_nil {u : List ℕ} (h : u ≠ []) : pd_inc u ≠ [] := by
  cases u with
  | nil => exact absurd rfl h
  | cons a u => simp [pd_inc]

private theorem pd_inc_dropLast (u : List ℕ) : (pd_inc u).dropLast = pd_inc u.dropLast := by
  match u with
  | [] => rfl
  | [a] => rfl
  | a :: b :: u => simp [pd_inc, List.dropLast]

private theorem pd_inc_inj {u v : List ℕ} (h : pd_inc u = pd_inc v) : u = v := by
  match u, v with
  | [], [] => rfl
  | [], b :: v => simp [pd_inc] at h
  | a :: u, [] => simp [pd_inc] at h
  | a :: u, b :: v => simp [pd_inc] at h; obtain ⟨h1, h2⟩ := h; subst h1; subst h2; rfl

private theorem pd_contourForest_succ (cs : List PlaneTree) (i : ℕ) :
    contourForest cs (i + 1) = (contourForest cs i).map pd_inc := by
  induction cs generalizing i with
  | nil => simp [contourForest]
  | cons c cs ih =>
    simp only [contourForest, List.map_append, List.map_map, ih (i+1)]
    congr 1

private theorem pd_vtxsForest_succ (cs : List PlaneTree) (i : ℕ) :
    vtxsForest cs (i + 1) = (vtxsForest cs i).map pd_inc := by
  induction cs generalizing i with
  | nil => simp [vtxsForest]
  | cons c cs ih =>
    simp only [vtxsForest, List.map_append, List.map_map, ih (i+1)]
    congr 1

private theorem pd_vtxsForest_ne_nil {cs : List PlaneTree} {i : ℕ} {u : List ℕ}
    (h : u ∈ vtxsForest cs i) : u ≠ [] := by
  induction cs generalizing i with
  | nil => simp [vtxsForest] at h
  | cons c cs ih =>
    simp only [vtxsForest, List.mem_append, List.mem_map] at h
    rcases h with ⟨w, _, rfl⟩ | h
    · simp
    · exact ih h

private theorem pd_contour_node (cs : List PlaneTree) :
    (PlaneTree.node cs).contour = [] :: contourForest cs 0 := by
  simp [PlaneTree.contour]

private theorem pd_contour_node_cons (P1 : PlaneTree) (cs : List PlaneTree) :
    (PlaneTree.node (P1 :: cs)).contour =
      [] :: (P1.contour.map (List.cons 0) ++ [[]] ++ (contourForest cs 0).map pd_inc) := by
  simp [PlaneTree.contour, contourForest, pd_contourForest_succ]

private theorem pd_vtxs_node (cs : List PlaneTree) :
    (PlaneTree.node cs).vtxs = [] :: vtxsForest cs 0 := by
  simp [PlaneTree.vtxs]

private theorem pd_vtxs_node_cons (P1 : PlaneTree) (cs : List PlaneTree) :
    (PlaneTree.node (P1 :: cs)).vtxs =
      [] :: (P1.vtxs.map (List.cons 0) ++ (vtxsForest cs 0).map pd_inc) := by
  simp [PlaneTree.vtxs, vtxsForest, pd_vtxsForest_succ]

private theorem pd_pos_b (P1 : PlaneTree) (cs : List PlaneTree) (L1 s1 : ℕ)
    (h1 : P1.contour.length = L1 + 1) (hs : s1 ≤ L1) :
    (PlaneTree.node (P1 :: cs)).contour.getD (s1 + 1) [] = 0 :: P1.contour.getD s1 [] := by
  rw [pd_contour_node_cons, List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.append_assoc,
    List.getElem?_append_left (by simpa using by omega), List.getElem?_map,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  simp

private theorem pd_pos_c (P1 : PlaneTree) (cs : List PlaneTree) (L1 L2 q : ℕ)
    (h1 : P1.contour.length = L1 + 1) (h2 : (contourForest cs 0).length = L2) (hq : q ≤ L2) :
    (PlaneTree.node (P1 :: cs)).contour.getD (L1 + 2 + q) [] =
      pd_inc ((PlaneTree.node cs).contour.getD q []) := by
  rw [pd_contour_node_cons, pd_contour_node, List.getD_eq_getElem?_getD]
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · rw [show L1 + 2 + 0 = (L1 + 1) + 1 by omega, List.getElem?_cons_succ, List.append_assoc,
      List.getElem?_append_right (by simpa using by omega)]
    simp [h1, pd_inc]
  · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [show L1 + 2 + (q' + 1) = (L1 + 2 + q') + 1 by omega, List.getElem?_cons_succ,
      List.append_assoc, List.getElem?_append_right (by simpa using by omega)]
    simp only [List.length_map, h1]
    rw [show L1 + 2 + q' - (L1 + 1) = q' + 1 by omega, List.singleton_append,
      List.getElem?_cons_succ, List.getElem?_map, List.getD_cons_succ, List.getD_eq_getElem?_getD]
    cases (contourForest cs 0)[q']? <;> simp [pd_inc]

private theorem pd_pos_d (P1 : PlaneTree) (cs : List PlaneTree) (L1 L2 s : ℕ)
    (h1 : P1.contour.length = L1 + 1) (h2 : (contourForest cs 0).length = L2) (hs : L1 + L2 + 2 < s) :
    (PlaneTree.node (P1 :: cs)).contour.getD s [] = [] := by
  rw [pd_contour_node_cons, List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · simp [h1, h2]; omega

private theorem pd_mem_vtxs_cons {P1 : PlaneTree} {cs : List PlaneTree} {v : List ℕ} :
    v ∈ (PlaneTree.node (P1 :: cs)).vtxs ↔
      v = [] ∨ (∃ w ∈ P1.vtxs, v = 0 :: w) ∨
        (∃ w ∈ (PlaneTree.node cs).vtxs, w ≠ [] ∧ v = pd_inc w) := by
  rw [pd_vtxs_node_cons, pd_vtxs_node]
  simp only [List.mem_cons, List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨w, hw, h⟩ | ⟨w, hw, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨w, hw, h.symm⟩)
    · exact Or.inr (Or.inr ⟨w, Or.inr hw, pd_vtxsForest_ne_nil hw, h.symm⟩)
  · rintro (h | ⟨w, hw, h⟩ | ⟨w, hw | hw, hne, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨w, hw, h.symm⟩)
    · exact absurd hw hne
    · exact Or.inr (Or.inr ⟨w, hw, h.symm⟩)

private theorem pd_mem_cons0 {P1 : PlaneTree} {cs : List PlaneTree} {w : List ℕ} :
    0 :: w ∈ (PlaneTree.node (P1 :: cs)).vtxs ↔ w ∈ P1.vtxs := by
  rw [pd_mem_vtxs_cons]
  constructor
  · rintro (h | ⟨x, hx, h⟩ | ⟨x, hx, hne, h⟩)
    · simp at h
    · simp at h; rw [h]; exact hx
    · exfalso
      match x, hne, h with
      | a :: y, _, h => simp [pd_inc] at h
  · intro h; exact Or.inr (Or.inl ⟨w, h, rfl⟩)

private theorem pd_mem_inc {P1 : PlaneTree} {cs : List PlaneTree} {w : List ℕ} :
    pd_inc w ∈ (PlaneTree.node (P1 :: cs)).vtxs ↔ w ∈ (PlaneTree.node cs).vtxs := by
  rw [pd_mem_vtxs_cons]
  constructor
  · rintro (h | ⟨x, hx, h⟩ | ⟨x, hx, hne, h⟩)
    · have : w = [] := by
        match w, h with
        | [], _ => rfl
      subst this
      rw [pd_vtxs_node]; simp
    · exfalso
      match w, h with
      | [], h => simp [pd_inc] at h
      | a :: y, h => simp [pd_inc] at h
    · have := pd_inc_inj h; subst this; exact hx
  · intro h
    by_cases hw : w = []
    · subst hw; exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨w, h, hw, rfl⟩)

private def pd_PC (a b : List ℕ) : Prop := (b ≠ [] ∧ b.dropLast = a) ∨ (a ≠ [] ∧ a.dropLast = b)

private theorem pd_PC_cons0 {a b : List ℕ} (h : pd_PC a b) : pd_PC (0 :: a) (0 :: b) := by
  rcases h with ⟨hb, h⟩ | ⟨ha, h⟩
  · left; refine ⟨by simp, ?_⟩
    rw [List.dropLast_cons_of_ne_nil hb, h]
  · right; refine ⟨by simp, ?_⟩
    rw [List.dropLast_cons_of_ne_nil ha, h]

private theorem pd_PC_inc {a b : List ℕ} (h : pd_PC a b) : pd_PC (pd_inc a) (pd_inc b) := by
  rcases h with ⟨hb, h⟩ | ⟨ha, h⟩
  · left; exact ⟨pd_inc_ne_nil hb, by rw [pd_inc_dropLast, h]⟩
  · right; exact ⟨pd_inc_ne_nil ha, by rw [pd_inc_dropLast, h]⟩

private def pd_PInv (L : ℕ) (P : PlaneTree) : Prop :=
  P.contour.length = L + 1 ∧
  P.contour.getD L [] = [] ∧
  (∀ s ≤ L, P.contour.getD s [] ∈ P.vtxs) ∧
  (∀ u ∈ P.vtxs, ∃ s ≤ L, P.contour.getD s [] = u) ∧
  (∀ s < L, pd_PC (P.contour.getD s []) (P.contour.getD (s + 1) [])) ∧
  (∀ v ∈ P.vtxs, v ≠ [] →
    ∃ s < L, P.contour.getD s [] = v.dropLast ∧ P.contour.getD (s + 1) [] = v) ∧
  (∀ (u : List ℕ) (i j s : ℕ), u ++ [i] ∈ P.vtxs → u ++ [j] ∈ P.vtxs → i < j →
    P.contour.getD s [] = u ++ [j] → ∃ s' < s, P.contour.getD s' [] = u ++ [i])

private theorem pd_contour_getD_zero (P : PlaneTree) : P.contour.getD 0 [] = [] := by
  cases P with
  | node cs => rw [pd_contour_node]; rfl

private theorem pd_pinv_base : pd_PInv 0 (PlaneTree.node []) := by
  refine ⟨by simp [PlaneTree.contour, contourForest], rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have : s = 0 := by omega
    subst this; simp [PlaneTree.contour, contourForest, PlaneTree.vtxs, vtxsForest]
  · intro u hu
    have : u = [] := by simpa [PlaneTree.vtxs, vtxsForest] using hu
    subst this
    exact ⟨0, le_refl _, pd_contour_getD_zero _⟩
  · intro s hs; omega
  · intro v hv hne
    simp [PlaneTree.vtxs, vtxsForest] at hv; exact absurd hv hne
  · intro u i j s hi hj hij
    simp [PlaneTree.vtxs, vtxsForest] at hi
    
private theorem pd_pinv_combine {P1 : PlaneTree} {cs : List PlaneTree} {L1 L2 : ℕ}
    (h1 : pd_PInv L1 P1) (h2 : pd_PInv L2 (PlaneTree.node cs)) :
    pd_PInv (L1 + L2 + 2) (PlaneTree.node (P1 :: cs)) := by
  obtain ⟨l1, e1, m1, c1, ch1, p1, o1⟩ := h1
  obtain ⟨l2, e2, m2, c2, ch2, p2, o2⟩ := h2
  have hF : (contourForest cs 0).length = L2 := by
    rw [pd_contour_node] at l2; simpa using l2
  have hb : ∀ s1 ≤ L1, (PlaneTree.node (P1 :: cs)).contour.getD (s1 + 1) [] =
      0 :: P1.contour.getD s1 [] := fun s1 hs => pd_pos_b P1 cs L1 s1 l1 hs
  have hc : ∀ q ≤ L2, (PlaneTree.node (P1 :: cs)).contour.getD (L1 + 2 + q) [] =
      pd_inc ((PlaneTree.node cs).contour.getD q []) := fun q hq => pd_pos_c P1 cs L1 L2 q l1 hF hq
  have hd : ∀ s, L1 + L2 + 2 < s → (PlaneTree.node (P1 :: cs)).contour.getD s [] = [] :=
    fun s hs => pd_pos_d P1 cs L1 L2 s l1 hF hs
  have ha := pd_contour_getD_zero (PlaneTree.node (P1 :: cs))
  have hc0 := pd_contour_getD_zero P1
  have hc20 := pd_contour_getD_zero (PlaneTree.node cs)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pd_contour_node_cons]; simp [l1, hF]; omega
  · have := hc L2 le_rfl
    rw [e2] at this
    rw [show L1 + L2 + 2 = L1 + 2 + L2 by omega, this]; rfl
  · intro s hs
    rcases Nat.eq_zero_or_pos s with rfl | hs0
    · rw [ha, pd_vtxs_node_cons]; simp
    · by_cases hs1 : s ≤ L1 + 1
      · obtain ⟨s1, rfl⟩ : ∃ s1, s = s1 + 1 := ⟨s - 1, by omega⟩
        rw [hb s1 (by omega), pd_mem_cons0]
        exact m1 s1 (by omega)
      · have hq : s = L1 + 2 + (s - (L1 + 2)) := by omega
        rw [hq, hc _ (by omega), pd_mem_inc]
        exact m2 _ (by omega)
  · intro v hv
    rw [pd_mem_vtxs_cons] at hv
    rcases hv with rfl | ⟨w, hw, rfl⟩ | ⟨w, hw, -, rfl⟩
    · exact ⟨0, by omega, ha⟩
    · obtain ⟨s1, hs1, hs1e⟩ := c1 w hw
      exact ⟨s1 + 1, by omega, by rw [hb s1 hs1, hs1e]⟩
    · obtain ⟨q, hq, hqe⟩ := c2 w hw
      exact ⟨L1 + 2 + q, by omega, by rw [hc q hq, hqe]⟩
  · intro s hs
    rcases Nat.eq_zero_or_pos s with rfl | hs0
    · rw [ha, hb 0 (by omega), hc0]
      left; exact ⟨by simp, rfl⟩
    · by_cases hs1 : s ≤ L1
      · obtain ⟨s1, rfl⟩ : ∃ s1, s = s1 + 1 := ⟨s - 1, by omega⟩
        rw [hb s1 (by omega), hb (s1 + 1) (by omega)]
        exact pd_PC_cons0 (ch1 s1 (by omega))
      · by_cases hs2 : s = L1 + 1
        · subst hs2
          have := hc 0 (by omega)
          rw [hb L1 le_rfl, e1, show L1 + 1 + 1 = L1 + 2 + 0 by omega, this, hc20]
          right; exact ⟨by simp, rfl⟩
        · obtain ⟨q, rfl⟩ : ∃ q, s = L1 + 2 + q := ⟨s - (L1 + 2), by omega⟩
          rw [hc q (by omega), show L1 + 2 + q + 1 = L1 + 2 + (q + 1) by omega,
            hc (q + 1) (by omega)]
          exact pd_PC_inc (ch2 q (by omega))
  · intro v hv hne
    rw [pd_mem_vtxs_cons] at hv
    rcases hv with rfl | ⟨w, hw, rfl⟩ | ⟨w, hw, hwne, rfl⟩
    · exact absurd rfl hne
    · by_cases hw0 : w = []
      · subst hw0
        exact ⟨0, by omega, by rw [ha]; rfl, by rw [hb 0 (by omega), hc0]⟩
      · obtain ⟨s1, hs1, hs1a, hs1b⟩ := p1 w hw hw0
        refine ⟨s1 + 1, by omega, ?_, ?_⟩
        · rw [hb s1 (by omega), hs1a, List.dropLast_cons_of_ne_nil hw0]
        · rw [hb (s1 + 1) (by omega), hs1b]
    · obtain ⟨q, hq, hqa, hqb⟩ := p2 w hw hwne
      refine ⟨L1 + 2 + q, by omega, ?_, ?_⟩
      · rw [hc q (by omega), hqa, pd_inc_dropLast]
      · rw [show L1 + 2 + q + 1 = L1 + 2 + (q + 1) by omega, hc (q + 1) (by omega), hqb]
  · intro u i j s hi hj hij hs
    rcases Nat.eq_zero_or_pos s with rfl | hs0
    · rw [ha] at hs; simp at hs
    · by_cases hs1 : s ≤ L1 + 1
      · obtain ⟨s1, rfl⟩ : ∃ s1, s = s1 + 1 := ⟨s - 1, by omega⟩
        rw [hb s1 (by omega)] at hs
        cases u with
        | nil =>
          simp at hs
          omega
        | cons a u' =>
          simp at hs
          obtain ⟨rfl, hs⟩ := hs
          have hi' : u' ++ [i] ∈ P1.vtxs := by
            have : 0 :: (u' ++ [i]) ∈ (PlaneTree.node (P1 :: cs)).vtxs := by simpa using hi
            exact pd_mem_cons0.mp this
          have hj' : u' ++ [j] ∈ P1.vtxs := by
            have : 0 :: (u' ++ [j]) ∈ (PlaneTree.node (P1 :: cs)).vtxs := by simpa using hj
            exact pd_mem_cons0.mp this
          obtain ⟨s', hs', he⟩ := o1 u' i j s1 hi' hj' hij hs
          exact ⟨s' + 1, by omega, by rw [hb s' (by omega), he]; rfl⟩
      · by_cases hs2 : s ≤ L1 + L2 + 2
        · obtain ⟨q, rfl⟩ : ∃ q, s = L1 + 2 + q := ⟨s - (L1 + 2), by omega⟩
          rw [hc q (by omega)] at hs
          have hwv := m2 q (by omega)
          generalize hw : (PlaneTree.node cs).contour.getD q [] = w at hs hwv
          rcases w with _ | ⟨a, y⟩
          · simp [pd_inc] at hs
          · cases u with
            | nil =>
              simp [pd_inc] at hs
              obtain ⟨rfl, rfl⟩ := hs
              rcases Nat.eq_zero_or_pos i with rfl | hi0
              · exact ⟨1, by omega, by rw [hb 0 (by omega), hc0]; rfl⟩
              · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
                have hi' : pd_inc [i'] ∈ (PlaneTree.node (P1 :: cs)).vtxs := by simpa [pd_inc] using hi
                have hi'' := pd_mem_inc.mp hi'
                obtain ⟨q', hq', he⟩ := o2 [] i' a q (by simpa using hi'') (by simpa using hwv)
                  (by omega) (by simpa using hw)
                refine ⟨L1 + 2 + q', by omega, ?_⟩
                rw [hc q' (by omega)]
                rw [he]; rfl
            | cons b u'' =>
              simp [pd_inc] at hs
              obtain ⟨rfl, hs⟩ := hs
              subst hs
              have hi' : pd_inc (a :: (u'' ++ [i])) ∈ (PlaneTree.node (P1 :: cs)).vtxs := by
                simpa [pd_inc] using hi
              have hi'' := pd_mem_inc.mp hi'
              have hj'' : (a :: u'') ++ [j] ∈ (PlaneTree.node cs).vtxs := by
                simpa using hwv
              obtain ⟨q', hq', he⟩ := o2 (a :: u'') i j q (by simpa using hi'') hj'' hij
                (by simpa using hw)
              refine ⟨L1 + 2 + q', by omega, ?_⟩
              rw [hc q' (by omega), he]
              simp [pd_inc]
        · rw [hd s (by omega)] at hs; simp at hs

private theorem pd_pt_vtxs_pos (P : PlaneTree) : 1 ≤ P.vtxs.length := by
  cases P with
  | node cs => rw [pd_vtxs_node]; simp

private theorem pd_pt_vtxs_len (P1 : PlaneTree) (cs : List PlaneTree) :
    (PlaneTree.node (P1 :: cs)).vtxs.length = P1.vtxs.length + (PlaneTree.node cs).vtxs.length := by
  have h1 : P1.vtxs.length = 1 + (match P1 with | .node c => (vtxsForest c 0).length) := by
    cases P1 with
    | node c => rw [pd_vtxs_node]; simp; omega
  rw [pd_vtxs_node_cons, pd_vtxs_node]
  simp only [List.length_cons, List.length_append, List.length_map]
  rw [h1]
  cases P1 with
  | node c => simp only [pd_vtxs_node, List.length_cons]; omega

private theorem pd_plane_ind (M : PlaneTree → Prop) (h0 : M (.node []))
    (h1 : ∀ P1 cs, M P1 → M (.node cs) → M (.node (P1 :: cs))) : ∀ P, M P := by
  intro P
  induction hn : P.vtxs.length using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    cases P with
    | node cs =>
      cases cs with
      | nil => exact h0
      | cons P1 cs =>
        rw [pd_pt_vtxs_len] at hn
        have a1 := pd_pt_vtxs_pos P1
        have a2 := pd_pt_vtxs_pos (PlaneTree.node cs)
        exact h1 P1 cs (ih _ (by omega) P1 rfl) (ih _ (by omega) (PlaneTree.node cs) rfl)

private theorem pd_pt_nodup (P : PlaneTree) : P.vtxs.Nodup := by
  refine pd_plane_ind (fun P => P.vtxs.Nodup) (by simp [PlaneTree.vtxs, vtxsForest]) ?_ P
  intro P1 cs h1 h2
  rw [pd_vtxs_node] at h2
  rw [pd_vtxs_node_cons]
  have h2' := List.nodup_cons.mp h2
  refine List.nodup_cons.mpr ⟨?_, ?_⟩
  · simp only [List.mem_append, List.mem_map, not_or]
    refine ⟨?_, ?_⟩
    · rintro ⟨w, _, hw⟩; simp at hw
    · rintro ⟨w, hw, hw'⟩
      exact pd_inc_ne_nil (pd_vtxsForest_ne_nil hw) hw'
  · rw [List.nodup_append]
    refine ⟨h1.map (fun a b h => by simpa using h), h2'.2.map (fun a b h => pd_inc_inj h), ?_⟩
    intro x hx y hy hxy
    simp only [List.mem_map] at hx hy
    obtain ⟨w, _, rfl⟩ := hx
    obtain ⟨w', hw', rfl⟩ := hy
    have hne := pd_vtxsForest_ne_nil hw'
    match w', hne with
    | a :: u, _ => simp [pd_inc] at hxy

private theorem pd_pt_contour_len (P : PlaneTree) : P.contour.length + 1 = 2 * P.vtxs.length := by
  refine pd_plane_ind (fun P => P.contour.length + 1 = 2 * P.vtxs.length)
    (by simp [PlaneTree.contour, contourForest, PlaneTree.vtxs, vtxsForest]) ?_ P
  intro P1 cs h1 h2
  rw [pd_pt_vtxs_len, pd_contour_node_cons]
  rw [pd_contour_node] at h2
  simp only [List.length_cons, List.length_append, List.length_map, List.length_singleton, List.length_nil] at h1 h2 ⊢
  omega

private theorem pd_pt_mem_idx (cs : List PlaneTree) (a : ℕ) (w : List ℕ) :
    (a :: w) ∈ (PlaneTree.node cs).vtxs ↔ ∃ h : a < cs.length, w ∈ (cs[a]).vtxs := by
  induction cs generalizing a with
  | nil => simp [pd_vtxs_node, vtxsForest]
  | cons P1 cs ih =>
    cases a with
    | zero => rw [pd_mem_cons0]; simp
    | succ a =>
      have : (a + 1) :: w = pd_inc (a :: w) := rfl
      rw [this, pd_mem_inc, ih]
      simp

private theorem pd_pt_root_mem (P : PlaneTree) : ([] : List ℕ) ∈ P.vtxs := by
  cases P with
  | node cs => rw [pd_vtxs_node]; simp

private theorem pd_pt_parent_mem (u : List ℕ) : ∀ (P : PlaneTree) (i : ℕ),
    u ++ [i] ∈ P.vtxs → u ∈ P.vtxs := by
  induction u with
  | nil => intro P i _; exact pd_pt_root_mem P
  | cons a u ih =>
    intro P i h
    cases P with
    | node cs =>
      rw [List.cons_append, pd_pt_mem_idx] at h
      obtain ⟨hl, hm⟩ := h
      rw [pd_pt_mem_idx]
      exact ⟨hl, ih _ i hm⟩

private theorem pd_pt_prefix_closed (u : List ℕ) : ∀ (P : PlaneTree) (i j : ℕ), i < j →
    u ++ [j] ∈ P.vtxs → u ++ [i] ∈ P.vtxs := by
  induction u with
  | nil =>
    intro P i j hij h
    cases P with
    | node cs =>
      rw [List.nil_append, pd_pt_mem_idx] at h
      obtain ⟨hl, hm⟩ := h
      rw [List.nil_append, pd_pt_mem_idx]
      exact ⟨by omega, pd_pt_root_mem _⟩
  | cons a u ih =>
    intro P i j hij h
    cases P with
    | node cs =>
      rw [List.cons_append, pd_pt_mem_idx] at h
      obtain ⟨hl, hm⟩ := h
      rw [List.cons_append, pd_pt_mem_idx]
      exact ⟨hl, ih _ i j hij hm⟩

private theorem pd_downclosed_iff (l : List ℕ) (hl : l.Nodup) (hd : ∀ i ∈ l, ∀ j < i, j ∈ l) (i : ℕ) :
    i ∈ l ↔ i < l.length := by
  have hcard : l.toFinset.card = l.length := List.toFinset_card_of_nodup hl
  constructor
  · intro hi
    have : Finset.range (i + 1) ⊆ l.toFinset := by
      intro x hx
      rw [Finset.mem_range] at hx
      rw [List.mem_toFinset]
      rcases Nat.lt_or_ge x i with h | h
      · exact hd i hi x h
      · have : x = i := by omega
        rw [this]; exact hi
    have := Finset.card_le_card this
    rw [Finset.card_range, hcard] at this
    omega
  · intro hi
    by_contra hni
    have : l.toFinset ⊆ Finset.range i := by
      intro x hx
      rw [List.mem_toFinset] at hx
      rw [Finset.mem_range]
      by_contra hge
      exact hni (by
        rcases Nat.eq_or_lt_of_le (not_lt.mp hge) with h | h
        · rw [h]; exact hx
        · exact hd x hx i h)
    have := Finset.card_le_card this
    rw [Finset.card_range, hcard] at this
    omega

private theorem pd_pt_childCount_iff (P : PlaneTree) (u : List ℕ) (i : ℕ) :
    u ++ [i] ∈ P.vtxs ↔ u ∈ P.vtxs ∧ i < P.childCount u := by
  classical
  set F := P.vtxs.filter (fun v => v ≠ [] ∧ v.dropLast = u) with hF
  have hFl : P.childCount u = F.length := rfl
  set l := F.map (fun v => v.getLastD 0) with hl
  have hFmem : ∀ v, v ∈ F ↔ ∃ i, v = u ++ [i] ∧ u ++ [i] ∈ P.vtxs := by
    intro v
    rw [hF, List.mem_filter]
    constructor
    · rintro ⟨hv, hd⟩
      simp only [decide_eq_true_eq] at hd
      obtain ⟨hne, hdl⟩ := hd
      refine ⟨v.getLastD 0, ?_, ?_⟩
      · rw [← hdl]
        have := List.dropLast_append_getLast hne
        rw [List.getLastD_eq_getLast?]
        rw [List.getLast?_eq_getLast_of_ne_nil hne]
        simpa using this.symm
      · have : v = u ++ [v.getLastD 0] := by
          rw [← hdl]
          have := List.dropLast_append_getLast hne
          rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast_of_ne_nil hne]
          simpa using this.symm
        rw [← this]; exact hv
    · rintro ⟨i, rfl, hi⟩
      refine ⟨hi, ?_⟩
      simp
  have hlmem : ∀ i, i ∈ l ↔ u ++ [i] ∈ P.vtxs := by
    intro i
    rw [hl, List.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨j, rfl, hj⟩ := (hFmem v).mp hv
      simpa using hj
    · intro h
      exact ⟨u ++ [i], (hFmem _).mpr ⟨i, rfl, h⟩, by simp⟩
  have hnd : l.Nodup := by
    rw [hl]
    refine List.Nodup.map_on ?_ ((pd_pt_nodup P).filter _)
    intro x hx y hy hxy
    obtain ⟨i, rfl, _⟩ := (hFmem x).mp hx
    obtain ⟨j, rfl, _⟩ := (hFmem y).mp hy
    simp at hxy
    rw [hxy]
  have hdc : ∀ i ∈ l, ∀ j < i, j ∈ l := by
    intro i hi j hj
    rw [hlmem] at hi ⊢
    exact pd_pt_prefix_closed u P j i hj hi
  have hlen : l.length = P.childCount u := by rw [hl, List.length_map]; rfl
  constructor
  · intro h
    refine ⟨pd_pt_parent_mem u P i h, ?_⟩
    rw [← hlen, ← pd_downclosed_iff l hnd hdc]
    exact (hlmem i).mpr h
  · rintro ⟨_, h⟩
    rw [← hlmem, pd_downclosed_iff l hnd hdc, hlen]
    exact h

private theorem pd_nat_eq_of_lt_iff {a b : ℕ} (h : ∀ i, i < a ↔ i < b) : a = b := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h3 | h3
  · have := (h a).mpr h3
    omega
  · have := (h b).mp h3
    omega

private theorem pd_pt_cc_nil (cs : List PlaneTree) : (PlaneTree.node cs).childCount [] = cs.length := by
  apply pd_nat_eq_of_lt_iff
  intro i
  have h1 := pd_pt_childCount_iff (PlaneTree.node cs) [] i
  rw [List.nil_append, pd_pt_mem_idx] at h1
  constructor
  · intro hi
    have := h1.mpr ⟨pd_pt_root_mem _, hi⟩
    obtain ⟨h, _⟩ := this
    exact h
  · intro hi
    exact (h1.mp ⟨hi, pd_pt_root_mem _⟩).2

private theorem pd_pt_cc_idx (cs : List PlaneTree) (a : ℕ) (h : a < cs.length) (u : List ℕ)
    (hu : u ∈ (cs[a]).vtxs) : (PlaneTree.node cs).childCount (a :: u) = (cs[a]).childCount u := by
  apply pd_nat_eq_of_lt_iff
  intro i
  have h1 := pd_pt_childCount_iff (PlaneTree.node cs) (a :: u) i
  have h2 := pd_pt_childCount_iff (cs[a]) u i
  rw [List.cons_append, pd_pt_mem_idx] at h1
  have hmem : a :: u ∈ (PlaneTree.node cs).vtxs := (pd_pt_mem_idx cs a u).mpr ⟨h, hu⟩
  constructor
  · intro hi
    exact (h2.mp (h1.mpr ⟨hmem, hi⟩).choose_spec).2
  · intro hi
    exact (h1.mp (by exact ⟨h, h2.mpr ⟨hu, hi⟩⟩)).2

private def pd_cpre (u : List ℕ) (j : ℕ) : List ℕ := if j = 0 then u.dropLast else u ++ [j - 1]

private def pd_cpost (u : List ℕ) (m j : ℕ) : List ℕ := if j = m then u.dropLast else u ++ [j]

private theorem pd_cpre_zero (u : List ℕ) : pd_cpre u 0 = u.dropLast := by simp [pd_cpre]

private theorem pd_cpre_succ (u : List ℕ) (j : ℕ) : pd_cpre u (j + 1) = u ++ [j] := by simp [pd_cpre]

private theorem pd_cpost_self (u : List ℕ) (m : ℕ) : pd_cpost u m m = u.dropLast := by simp [pd_cpost]

private theorem pd_cpost_ne (u : List ℕ) {m j : ℕ} (h : j ≠ m) : pd_cpost u m j = u ++ [j] := by
  simp [pd_cpost, h]

private theorem pd_cpre_cons0 {w : List ℕ} (hw : w ≠ []) (j : ℕ) : pd_cpre (0 :: w) j = 0 :: pd_cpre w j := by
  unfold pd_cpre
  split_ifs
  · exact List.dropLast_cons_of_ne_nil hw
  · rfl

private theorem pd_cpost_cons0 {w : List ℕ} (hw : w ≠ []) (m j : ℕ) :
    pd_cpost (0 :: w) m j = 0 :: pd_cpost w m j := by
  unfold pd_cpost
  split_ifs
  · exact List.dropLast_cons_of_ne_nil hw
  · rfl

private theorem pd_inc_append_single {w : List ℕ} (hw : w ≠ []) (j : ℕ) :
    pd_inc (w ++ [j]) = pd_inc w ++ [j] := by
  match w, hw with
  | a :: w, _ => rfl

private theorem pd_cpre_inc {w : List ℕ} (hw : w ≠ []) (j : ℕ) : pd_cpre (pd_inc w) j = pd_inc (pd_cpre w j) := by
  unfold pd_cpre
  split_ifs
  · exact pd_inc_dropLast w
  · exact (pd_inc_append_single hw _).symm

private theorem pd_cpost_inc {w : List ℕ} (hw : w ≠ []) (m j : ℕ) :
    pd_cpost (pd_inc w) m j = pd_inc (pd_cpost w m j) := by
  unfold pd_cpost
  split_ifs
  · exact pd_inc_dropLast w
  · exact (pd_inc_append_single hw _).symm

private def pd_CI (L : ℕ) (P : PlaneTree) : Prop :=
  (1 ≤ P.childCount [] → P.contour.getD 1 [] = [0]) ∧
  (1 ≤ P.childCount [] → P.contour.getD (L - 1) [] = [P.childCount [] - 1]) ∧
  (P.childCount [] = 0 → L = 0) ∧
  (∀ s, 1 ≤ s → s + 1 ≤ L → ∃ j ≤ P.childCount (P.contour.getD s []),
    (P.contour.getD s [] = [] → 0 < j ∧ j < P.childCount []) ∧
    P.contour.getD (s - 1) [] = pd_cpre (P.contour.getD s []) j ∧
    P.contour.getD (s + 1) [] = pd_cpost (P.contour.getD s []) (P.childCount (P.contour.getD s [])) j) ∧
  (∀ u ∈ P.vtxs, ∀ j ≤ P.childCount u, (u = [] → 0 < j ∧ j < P.childCount []) →
    ∃ s, 1 ≤ s ∧ s + 1 ≤ L ∧ P.contour.getD s [] = u ∧
      P.contour.getD (s - 1) [] = pd_cpre u j ∧
      P.contour.getD (s + 1) [] = pd_cpost u (P.childCount u) j)

private theorem pd_ci_base : pd_CI 0 (PlaneTree.node []) := by
  have hcc : (PlaneTree.node []).childCount [] = 0 := by rw [pd_pt_cc_nil]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; omega
  · intro h; omega
  · intro _; rfl
  · intro s h1 h2; omega
  · intro u hu j hj hr
    have : u = [] := by simpa [PlaneTree.vtxs, vtxsForest] using hu
    have := hr this
    omega

private theorem pd_getD_lt_of_ne (C : List (List ℕ)) (s : ℕ) (h : C.getD s [] ≠ []) : s < C.length := by
  by_contra hh
  apply h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

private theorem pd_ci_combine {P1 : PlaneTree} {cs : List PlaneTree} {L1 L2 : ℕ}
    (h1 : pd_PInv L1 P1) (h2 : pd_PInv L2 (PlaneTree.node cs))
    (k1 : pd_CI L1 P1) (k2 : pd_CI L2 (PlaneTree.node cs)) :
    pd_CI (L1 + L2 + 2) (PlaneTree.node (P1 :: cs)) := by
  obtain ⟨l1, e1, m1, c1, ch1, p1, o1⟩ := h1
  obtain ⟨l2, e2, m2, c2, ch2, p2, o2⟩ := h2
  obtain ⟨r1a, r1b, r1c, bw1, fw1⟩ := k1
  obtain ⟨r2a, r2b, r2c, bw2, fw2⟩ := k2
  have hF : (contourForest cs 0).length = L2 := by
    rw [pd_contour_node] at l2; simpa using l2
  have hb : ∀ s1 ≤ L1, (PlaneTree.node (P1 :: cs)).contour.getD (s1 + 1) [] =
      0 :: P1.contour.getD s1 [] := fun s1 hs => pd_pos_b P1 cs L1 s1 l1 hs
  have hc : ∀ q ≤ L2, (PlaneTree.node (P1 :: cs)).contour.getD (L1 + 2 + q) [] =
      pd_inc ((PlaneTree.node cs).contour.getD q []) := fun q hq => pd_pos_c P1 cs L1 L2 q l1 hF hq
  have hd : ∀ s, L1 + L2 + 2 < s → (PlaneTree.node (P1 :: cs)).contour.getD s [] = [] :=
    fun s hs => pd_pos_d P1 cs L1 L2 s l1 hF hs
  have ha := pd_contour_getD_zero (PlaneTree.node (P1 :: cs))
  have hc0 := pd_contour_getD_zero P1
  have hc20 := pd_contour_getD_zero (PlaneTree.node cs)
  have hm : (PlaneTree.node (P1 :: cs)).childCount [] = cs.length + 1 := by
    rw [pd_pt_cc_nil]; rfl
  have hm2 : (PlaneTree.node cs).childCount [] = cs.length := pd_pt_cc_nil cs
  rw [hm2] at r2a r2b r2c bw2 fw2
  have hcc0 : ∀ w ∈ P1.vtxs, (PlaneTree.node (P1 :: cs)).childCount (0 :: w) = P1.childCount w := by
    intro w hw
    have := pd_pt_cc_idx (P1 :: cs) 0 (by simp) w (by simpa using hw)
    simpa using this
  have hcci : ∀ w ∈ (PlaneTree.node cs).vtxs, w ≠ [] →
      (PlaneTree.node (P1 :: cs)).childCount (pd_inc w) = (PlaneTree.node cs).childCount w := by
    intro w hw hne
    match w, hne with
    | a :: w', _ =>
      obtain ⟨hl, hmm⟩ := (pd_pt_mem_idx cs a w').mp hw
      have := pd_pt_cc_idx (P1 :: cs) (a + 1) (by simp; omega) w' (by simpa using hmm)
      simp only [List.getElem_cons_succ] at this
      show (PlaneTree.node (P1 :: cs)).childCount ((a + 1) :: w') = _
      rw [this, pd_pt_cc_idx cs a hl w' hmm]
  -- boundary facts for the first and last corners of the root of P1 (the vertex `[0]` of P)
  have hL1m : P1.childCount [] = 0 ↔ L1 = 0 := by
    constructor
    · exact r1c
    · intro hL
      by_contra hne
      have := r1a (by omega)
      have := pd_getD_lt_of_ne _ _ (by rw [this]; simp)
      omega
  have hpre : ∀ s1 ≤ L1, (PlaneTree.node (P1 :: cs)).contour.getD (s1 + 1 - 1) [] =
      (if s1 = 0 then [] else 0 :: P1.contour.getD (s1 - 1) []) := by
    intro s1 hs1
    rcases Nat.eq_zero_or_pos s1 with rfl | hpos
    · simpa using ha
    · obtain ⟨t, rfl⟩ : ∃ t, s1 = t + 1 := ⟨s1 - 1, by omega⟩
      rw [Nat.add_sub_cancel, if_neg (by omega), Nat.add_sub_cancel]
      exact hb t (by omega)
  have hpost : ∀ s1 ≤ L1, (PlaneTree.node (P1 :: cs)).contour.getD (s1 + 1 + 1) [] =
      (if s1 = L1 then [] else 0 :: P1.contour.getD (s1 + 1) []) := by
    intro s1 hs1
    by_cases hh : s1 = L1
    · rw [if_pos hh, show s1 + 1 + 1 = L1 + 2 + 0 by omega, hc 0 (by omega), hc20]
      rfl
    · rw [if_neg hh]
      exact hb (s1 + 1) (by omega)
  have hmemP : ∀ s ≤ L1, P1.contour.getD s [] ∈ P1.vtxs := m1
  have hroot1 : ([] : List ℕ) ∈ P1.vtxs := pd_pt_root_mem P1
  have hroot2 : ([] : List ℕ) ∈ (PlaneTree.node cs).vtxs := pd_pt_root_mem _
  -- first corner of `[0]`: the step from position 1 to 2
  have hfirst : (PlaneTree.node (P1 :: cs)).contour.getD (0 + 1 + 1) [] =
      pd_cpost [0] (P1.childCount []) 0 := by
    rw [hpost 0 (Nat.zero_le _)]
    by_cases hz : P1.childCount [] = 0
    · have hL : L1 = 0 := r1c hz
      rw [if_pos hL.symm, hz, pd_cpost_self]; rfl
    · have hL : L1 ≠ 0 := fun h => hz (hL1m.mpr h)
      rw [if_neg (Ne.symm hL), pd_cpost_ne _ (Ne.symm hz), r1a (by omega)]
      rfl
  -- last corner of `[0]`: position `L1 + 1`
  have hlastpre : 1 ≤ P1.childCount [] → (PlaneTree.node (P1 :: cs)).contour.getD (L1 + 1 - 1) [] =
      pd_cpre [0] (P1.childCount []) := by
    intro hm1
    have hL : L1 ≠ 0 := fun h => by have := hL1m.mpr h; omega
    rw [hpre L1 le_rfl, if_neg hL, r1b hm1]
    obtain ⟨t, ht⟩ : ∃ t, P1.childCount [] = t + 1 := ⟨P1.childCount [] - 1, by omega⟩
    rw [ht, pd_cpre_succ]
    simp
  have hlastpost : (PlaneTree.node (P1 :: cs)).contour.getD (L1 + 1 + 1) [] = [] := by
    rw [hpost L1 le_rfl, if_pos rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro _
    have := hb 0 (Nat.zero_le _)
    rw [hc0] at this
    exact this
  · intro _
    rw [hm]
    by_cases hN : cs.length = 0
    · have hL2 : L2 = 0 := r2c hN
      rw [show L1 + L2 + 2 - 1 = L1 + 1 by omega, hb L1 le_rfl, e1]
      simp [hN]
    · have hL2 : 1 ≤ L2 := by
        have := r2a (by omega)
        have := pd_getD_lt_of_ne _ _ (by rw [this]; simp)
        omega
      rw [show L1 + L2 + 2 - 1 = L1 + 2 + (L2 - 1) by omega, hc (L2 - 1) (by omega), r2b (by omega)]
      simp [pd_inc]
      omega
  · intro h
    rw [hm] at h
    omega
  · -- backward corners
    intro s hs1 hs2
    by_cases hs : s ≤ L1 + 1
    · obtain ⟨s1, rfl⟩ : ∃ s1, s = s1 + 1 := ⟨s - 1, by omega⟩
      have hs1L : s1 ≤ L1 := by omega
      rw [hb s1 hs1L, hpre s1 hs1L, hpost s1 hs1L, hm]
      by_cases hw : P1.contour.getD s1 [] = []
      · rw [hw]
        have hcc : (PlaneTree.node (P1 :: cs)).childCount [0] = P1.childCount [] :=
          hcc0 [] hroot1
        rw [hcc]
        by_cases h0 : s1 = 0
        · subst h0
          refine ⟨0, Nat.zero_le _, ?_, ?_, ?_⟩
          · intro h; simp at h
          · simp [pd_cpre_zero]
          · have := hfirst
            rw [hpost 0 (Nat.zero_le _)] at this
            exact this
        · by_cases hL' : s1 = L1
          · have hm1 : 1 ≤ P1.childCount [] := by
              by_contra hh
              have := r1c (by omega)
              omega
            refine ⟨P1.childCount [], le_rfl, ?_, ?_, ?_⟩
            · intro h; simp at h
            · have := hlastpre hm1
              rw [← hL'] at this
              rw [if_neg h0]
              rw [hL'] at this ⊢
              rw [hpre L1 le_rfl, if_neg (by omega)] at this
              exact this
            · rw [if_pos hL', pd_cpost_self]; rfl
          · have hs1pos : 1 ≤ s1 := by omega
            obtain ⟨j, hj, hjr, hjpre, hjpost⟩ := bw1 s1 hs1pos (by omega)
            rw [hw] at hjr hjpre hjpost hj
            obtain ⟨hj0, hjm⟩ := hjr rfl
            obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
            refine ⟨t + 1, hj, ?_, ?_, ?_⟩
            · intro h; simp at h
            · rw [if_neg h0, hjpre, pd_cpre_succ, pd_cpre_succ]; rfl
            · rw [if_neg hL', hjpost, pd_cpost_ne _ (by omega), pd_cpost_ne _ (by omega)]; rfl
      · have hs1pos : 1 ≤ s1 := by
          rcases Nat.eq_zero_or_pos s1 with rfl | h
          · exact absurd hc0 hw
          · exact h
        have hs1lt : s1 < L1 := by
          rcases Nat.lt_or_ge s1 L1 with h | h
          · exact h
          · exact absurd (by rw [show s1 = L1 by omega]; exact e1) hw
        obtain ⟨j, hj, hjr, hjpre, hjpost⟩ := bw1 s1 hs1pos (by omega)
        have hwmem := m1 s1 hs1L
        refine ⟨j, by rw [hcc0 _ hwmem]; exact hj, ?_, ?_, ?_⟩
        · intro h; simp at h
        · rw [if_neg (by omega), pd_cpre_cons0 hw, hjpre]
        · rw [if_neg (by omega), hcc0 _ hwmem, pd_cpost_cons0 hw, hjpost]
    · obtain ⟨q, rfl⟩ : ∃ q, s = L1 + 2 + q := ⟨s - (L1 + 2), by omega⟩
      have hq : q + 1 ≤ L2 := by omega
      have hN : 1 ≤ cs.length := by
        by_contra hh
        have := r2c (by omega)
        omega
      rw [hm]
      by_cases hq0 : q = 0
      · subst hq0
        have hS : (PlaneTree.node (P1 :: cs)).contour.getD (L1 + 2 + 0) [] = [] := by
          rw [hc 0 (by omega), hc20]; rfl
        have hPre : (PlaneTree.node (P1 :: cs)).contour.getD (L1 + 2 + 0 - 1) [] = [0] := by
          rw [show L1 + 2 + 0 - 1 = L1 + 1 by omega, hb L1 le_rfl, e1]
        have hPost : (PlaneTree.node (P1 :: cs)).contour.getD (L1 + 2 + 0 + 1) [] = [1] := by
          rw [show L1 + 2 + 0 + 1 = L1 + 2 + 1 by omega, hc 1 (by omega), r2a hN]
          rfl
        rw [hS, hPre, hPost, hm]
        refine ⟨1, by omega, ?_, ?_, ?_⟩
        · intro _; omega
        · rw [pd_cpre_succ]; rfl
        · rw [pd_cpost_ne _ (by omega)]; rfl
      · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
        have hS : (PlaneTree.node (P1 :: cs)).contour.getD (L1 + 2 + (q' + 1)) [] =
            pd_inc ((PlaneTree.node cs).contour.getD (q' + 1) []) := hc _ (by omega)
        have hPre : (PlaneTree.node (P1 :: cs)).contour.getD (L1 + 2 + (q' + 1) - 1) [] =
            pd_inc ((PlaneTree.node cs).contour.getD q' []) := by
          rw [show L1 + 2 + (q' + 1) - 1 = L1 + 2 + q' by omega]; exact hc _ (by omega)
        have hPost : (PlaneTree.node (P1 :: cs)).contour.getD (L1 + 2 + (q' + 1) + 1) [] =
            pd_inc ((PlaneTree.node cs).contour.getD (q' + 1 + 1) []) := by
          rw [show L1 + 2 + (q' + 1) + 1 = L1 + 2 + (q' + 1 + 1) by omega]; exact hc _ (by omega)
        rw [hS, hPre, hPost]
        obtain ⟨j, hj, hjr, hjpre, hjpost⟩ := bw2 (q' + 1) (by omega) (by omega)
        rw [Nat.add_sub_cancel] at hjpre
        have hwmem := m2 (q' + 1) (by omega)
        by_cases hw : (PlaneTree.node cs).contour.getD (q' + 1) [] = []
        · rw [hw] at hjr hjpre hjpost hj
          rw [hw, show pd_inc ([] : List ℕ) = [] from rfl, hm]
          obtain ⟨hj0, hjm⟩ := hjr rfl
          obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
          refine ⟨t + 2, ?_, ?_, ?_, ?_⟩
          · omega
          · intro _; omega
          · rw [hjpre, pd_cpre_succ, pd_cpre_succ]; rfl
          · rw [hjpost, pd_cpost_ne _ (by omega), pd_cpost_ne _ (by omega)]; rfl
        · have hwmem' := hwmem
          rw [hcci _ hwmem hw]
          refine ⟨j, hj, ?_, ?_, ?_⟩
          · intro h; exact absurd h (pd_inc_ne_nil hw)
          · rw [pd_cpre_inc hw, hjpre]
          · rw [pd_cpost_inc hw, hjpost]
  · -- forward corners
    intro u hu j hj hr
    rw [pd_mem_vtxs_cons] at hu
    rcases hu with rfl | ⟨w, hw, rfl⟩ | ⟨w, hw, hwne, rfl⟩
    · -- the root
      obtain ⟨hj0, hjm⟩ := hr rfl
      rw [hm] at hjm hj ⊢
      have hN : 2 ≤ cs.length + 1 := by omega
      have hL2 : 1 ≤ L2 := by
        have := r2a (by omega)
        have := pd_getD_lt_of_ne _ _ (by rw [this]; simp)
        omega
      by_cases hj1 : j = 1
      · subst hj1
        have hS : (PlaneTree.node (P1 :: cs)).contour.getD (L1 + 2) [] = [] := by
          rw [show L1 + 2 = L1 + 2 + 0 by omega, hc 0 (by omega), hc20]; rfl
        refine ⟨L1 + 2, by omega, by omega, hS, ?_, ?_⟩
        · rw [show L1 + 2 - 1 = L1 + 1 by omega, hb L1 le_rfl, e1, pd_cpre_succ]; rfl
        · rw [show L1 + 2 + 1 = L1 + 2 + 1 from rfl, hc 1 (by omega), r2a (by omega),
            pd_cpost_ne _ (by omega)]; rfl
      · obtain ⟨s', hs1', hs2', hsu, hsp, hspost⟩ :=
          fw2 [] hroot2 (j - 1) (by rw [hm2]; omega)
            (fun _ => ⟨by have := hm2; omega, by have := hm2; omega⟩)
        refine ⟨L1 + 2 + s', by omega, by omega, ?_, ?_, ?_⟩
        · rw [hc s' (by omega), hsu]; rfl
        · rw [show L1 + 2 + s' - 1 = L1 + 2 + (s' - 1) by omega, hc (s' - 1) (by omega), hsp]
          obtain ⟨t, rfl⟩ : ∃ t, j = t + 2 := ⟨j - 2, by omega⟩
          rw [show t + 2 - 1 = t + 1 by omega, pd_cpre_succ, pd_cpre_succ]; rfl
        · have hh := hc (s' + 1) (by omega)
          rw [show L1 + 2 + s' + 1 = L1 + 2 + (s' + 1) by omega, hh, hspost]
          obtain ⟨t, rfl⟩ : ∃ t, j = t + 2 := ⟨j - 2, by omega⟩
          rw [show t + 2 - 1 = t + 1 by omega, pd_cpost_ne _ (by omega), pd_cpost_ne _ (by omega)]; rfl
    · -- vertices of the first subtree
      rw [hcc0 w hw] at hj ⊢
      by_cases hw0 : w = []
      · subst hw0
        by_cases hj0 : j = 0
        · subst hj0
          refine ⟨1, le_rfl, by omega, ?_, ?_, ?_⟩
          · have := hb 0 (Nat.zero_le _)
            rw [hc0] at this
            exact this
          · rw [pd_cpre_zero]; exact ha
          · have := hfirst
            exact this
        · by_cases hjm : j = P1.childCount []
          · have hm1 : 1 ≤ P1.childCount [] := by omega
            have hL : L1 ≠ 0 := fun h => by have := hL1m.mpr h; omega
            refine ⟨L1 + 1, by omega, by omega, ?_, ?_, ?_⟩
            · have := hb L1 le_rfl
              rw [e1] at this
              exact this
            · rw [hjm]; exact hlastpre hm1
            · rw [hlastpost, hjm, pd_cpost_self]; rfl
          · obtain ⟨s1, hs1a, hs1b, hs1u, hs1p, hs1q⟩ :=
              fw1 [] hroot1 j hj (fun _ => ⟨by omega, by omega⟩)
            refine ⟨s1 + 1, by omega, by omega, ?_, ?_, ?_⟩
            · rw [hb s1 (by omega), hs1u]
            · rw [hpre s1 (by omega), if_neg (by omega), hs1p]
              obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
              rw [pd_cpre_succ, pd_cpre_succ]; rfl
            · rw [hpost s1 (by omega), if_neg (by omega), hs1q, pd_cpost_ne _ (by omega),
                pd_cpost_ne _ (by omega)]; rfl
      · obtain ⟨s1, hs1a, hs1b, hs1u, hs1p, hs1q⟩ := fw1 w hw j hj (fun h => absurd h hw0)
        refine ⟨s1 + 1, by omega, by omega, ?_, ?_, ?_⟩
        · rw [hb s1 (by omega), hs1u]
        · rw [hpre s1 (by omega), if_neg (by omega), pd_cpre_cons0 hw0, hs1p]
        · rw [hpost s1 (by omega), if_neg (by omega), pd_cpost_cons0 hw0, hs1q]
    · -- vertices of the remaining subtrees
      rw [hcci w hw hwne] at hj ⊢
      obtain ⟨s', hs1', hs2', hsu, hsp, hspost⟩ := fw2 w hw j hj (fun h => absurd h hwne)
      refine ⟨L1 + 2 + s', by omega, by omega, ?_, ?_, ?_⟩
      · rw [hc s' (by omega), hsu]
      · rw [show L1 + 2 + s' - 1 = L1 + 2 + (s' - 1) by omega, hc (s' - 1) (by omega), hsp,
          pd_cpre_inc hwne]
      · rw [show L1 + 2 + s' + 1 = L1 + 2 + (s' + 1) by omega, hc (s' + 1) (by omega), hspost,
          pd_cpost_inc hwne]

private theorem pd_pt_pinv_ci (P : PlaneTree) : pd_PInv (P.contour.length - 1) P ∧ pd_CI (P.contour.length - 1) P := by
  have : ∃ L, pd_PInv L P ∧ pd_CI L P := by
    refine pd_plane_ind (fun P => ∃ L, pd_PInv L P ∧ pd_CI L P) ⟨0, pd_pinv_base, pd_ci_base⟩ ?_ P
    intro P1 cs ⟨L1, h1, k1⟩ ⟨L2, h2, k2⟩
    exact ⟨_, pd_pinv_combine h1 h2, pd_ci_combine h1 h2 k1 k2⟩
  obtain ⟨L, hL, kL⟩ := this
  have := hL.1
  rw [this]
  simpa using ⟨hL, kL⟩

private theorem pd_alt_getD_comp (ty : List ℕ → VType) (u : List ℕ) (m j : ℕ) (hj : j ≤ m) :
    (ty u.dropLast :: (List.range m).map fun i => ty (u ++ [i])).getD j VType.lat = ty (pd_cpre u j) ∧
    (ty u.dropLast :: (List.range m).map fun i => ty (u ++ [i])).getD ((j + 1) % (m + 1)) VType.lat =
      ty (pd_cpost u m j) := by
  constructor
  · rcases j with _ | j
    · simp [pd_cpre_zero]
    · rw [pd_cpre_succ]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_map]
      rw [List.getElem?_range (show j < m by omega)]
      simp
  · by_cases hjm : j = m
    · subst hjm
      rw [pd_cpost_self, Nat.mod_self]
      simp
    · rw [pd_cpost_ne _ hjm, Nat.mod_eq_of_lt (by omega)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_map]
      rw [List.getElem?_range (show j < m by omega)]
      simp

/-- Alternation of the types at the corners of the contour. -/
private def pd_CornerAlt (P : PlaneTree) (ty : List ℕ → VType) : Prop :=
  ∀ s, 1 ≤ s → s + 1 ≤ P.contour.length - 1 → ty (P.contour.getD s []) = VType.lat →
    ty (P.contour.getD (s - 1) []) ≠ VType.lat ∧ ty (P.contour.getD (s + 1) []) ≠ VType.lat ∧
    ty (P.contour.getD (s - 1) []) ≠ ty (P.contour.getD (s + 1) [])

private theorem pd_corner_of_latent_alt {k : ℕ} (T : TypedOrdTree k) : pd_CornerAlt T.tree T.ty := by
  intro s hs1 hs2 hty
  obtain ⟨-, -, -, bw, -⟩ := (pd_pt_pinv_ci T.tree).2
  have hne : T.tree.contour.getD s [] ≠ [] := by
    intro h; rw [h, T.root_out] at hty; exact absurd hty (by decide)
  obtain ⟨j, hj, hjr, hjpre, hjpost⟩ := bw s hs1 hs2
  have hmem := (pd_pt_pinv_ci T.tree).1.2.2.1 s (by omega)
  have halt := T.latent_alt _ hmem hne hty
  obtain ⟨g1, g2⟩ := pd_alt_getD_comp T.ty (T.tree.contour.getD s []) (T.tree.childCount (T.tree.contour.getD s [])) j hj
  have h1 := halt j (by simp only [List.length_cons, List.length_map, List.length_range]; omega)
  have h2 := halt ((j + 1) % (T.tree.childCount (T.tree.contour.getD s []) + 1))
    (by simp only [List.length_cons, List.length_map, List.length_range]
        exact Nat.mod_lt _ (by omega))
  simp only [List.length_cons, List.length_map, List.length_range] at h1 h2
  rw [g1, g2] at h1
  rw [g2] at h2
  rw [hjpre, hjpost]
  exact ⟨h1.1, h2.1, h1.2⟩

private theorem pd_tt_len {k : ℕ} (T : TypedOrdTree k) : T.tree.contour.length = 2 * k + 1 := by
  have := pd_pt_contour_len T.tree
  have := T.card_vtx
  omega

private theorem pd_tt_pinv {k : ℕ} (T : TypedOrdTree k) : pd_PInv (2 * k) T.tree := by
  have := (pd_pt_pinv_ci T.tree).1
  rwa [show T.tree.contour.length - 1 = 2 * k by have := pd_tt_len T; omega] at this

private theorem pd_tt_mem {k : ℕ} (T : TypedOrdTree k) {j : ℕ} (hj : j ≤ 2 * k) :
    T.tree.contour.getD j [] ∈ T.tree.vtxs := (pd_tt_pinv T).2.2.1 j hj

private theorem pd_tt_zero {k : ℕ} (T : TypedOrdTree k) : T.tree.contour.getD 0 [] = [] :=
  pd_contour_getD_zero _

private theorem pd_tt_pc {k : ℕ} (T : TypedOrdTree k) {i : ℕ} (hi : i < 2 * k) :
    pd_PC (T.tree.contour.getD i []) (T.tree.contour.getD (i + 1) []) :=
  (pd_tt_pinv T).2.2.2.2.1 i hi

private theorem pd_tt_adj_lat {k : ℕ} (T : TypedOrdTree k) {i : ℕ} (hi : i < 2 * k) :
    T.ty (T.tree.contour.getD i []) = VType.lat ↔ ¬ T.ty (T.tree.contour.getD (i + 1) []) = VType.lat := by
  rcases pd_tt_pc T hi with ⟨hne, hdl⟩ | ⟨hne, hdl⟩
  · exact T.edge_joins _ (pd_tt_mem T (by omega)) _ (pd_tt_mem T (by omega)) hne hdl
  · have := T.edge_joins _ (pd_tt_mem T (by omega)) _ (pd_tt_mem T (by omega)) hne hdl
    tauto

private theorem pd_vtype_cases (a b : VType) (ha : a ≠ VType.lat) (hb : b ≠ VType.lat) (hab : a ≠ b) :
    (a = VType.out ∧ b = VType.inp) ∨ (a = VType.inp ∧ b = VType.out) := by
  cases a <;> cases b <;> simp_all

/-- The type pattern along the contour: odd positions are latent, even positions alternate
`o, in, o, in, …` starting with `o`. -/
private theorem pd_tt_ty {k : ℕ} (T : TypedOrdTree k) :
    ∀ j ≤ 2 * k, (j % 2 = 1 → T.ty (T.tree.contour.getD j []) = VType.lat) ∧
      (j % 2 = 0 → T.ty (T.tree.contour.getD j []) = if j % 4 = 0 then VType.out else VType.inp) := by
  have hCA := pd_corner_of_latent_alt T
  have hlen := pd_tt_len T
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
      rw [pd_tt_zero, T.root_out]
      simp
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hj' := ih j' (by omega) (by omega)
      have hadj := pd_tt_adj_lat T (show j' < 2 * k by omega)
      by_cases hj'e : j' % 2 = 0
      · -- an even position is followed by a latent one
        have h1 := hj'.2 hj'e
        have : ¬ T.ty (T.tree.contour.getD j' []) = VType.lat := by
          rw [h1]; split_ifs <;> simp
        refine ⟨fun _ => ?_, fun h => absurd h (by omega)⟩
        by_contra hc
        exact this (hadj.mpr hc)
      · -- an odd position is followed by an external one
        have h1 := hj'.1 (by omega)
        have hnl : ¬ T.ty (T.tree.contour.getD (j' + 1) []) = VType.lat := hadj.mp h1
        refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
        obtain ⟨c1, c2, c3⟩ := hCA j' (by omega) (by rw [hlen]; omega) h1
        have hj'' := ih (j' - 1) (by omega) (by omega)
        have h2 := hj''.2 (by omega)
        rcases pd_vtype_cases _ _ c1 c2 c3 with ⟨a1, a2⟩ | ⟨a1, a2⟩
        · rw [a2]
          rw [a1] at h2
          have h4 : (j' - 1) % 4 = 0 := by
            by_contra hh; rw [if_neg hh] at h2; exact absurd h2 (by decide)
          rw [if_neg (by omega)]
        · rw [a2]
          rw [a1] at h2
          have h4 : ¬ (j' - 1) % 4 = 0 := by
            intro hh; rw [if_pos hh] at h2; exact absurd h2 (by decide)
          rw [if_pos (by omega)]

private theorem pd_tt_lat {k : ℕ} (T : TypedOrdTree k) {j : ℕ} (hj : j ≤ 2 * k) :
    T.ty (T.tree.contour.getD j []) = VType.lat ↔ j % 2 = 1 := by
  obtain ⟨h1, h2⟩ := pd_tt_ty T j hj
  constructor
  · intro h
    by_contra hh
    rw [h2 (by omega)] at h
    split_ifs at h
  · exact h1

private theorem pd_tt_ty_val {k : ℕ} (T : TypedOrdTree k) {j : ℕ} (hj : j ≤ 2 * k) :
    T.ty (T.tree.contour.getD j []) =
      (if j % 2 = 1 then VType.lat else if j % 4 = 0 then VType.out else VType.inp) := by
  obtain ⟨h1, h2⟩ := pd_tt_ty T j hj
  by_cases h : j % 2 = 1
  · rw [if_pos h]; exact h1 h
  · rw [if_neg h]; exact h2 (by omega)




private lemma pd_treePos_le {k : ℕ} (hk : 0 < k) (x : TreeVtx k) : treePos x ≤ 2 * k := by
  cases x with
  | inl s => exact (Nat.mod_lt _ (by omega) : 2 * (s.val + 1) % (2 * k) < 2 * k).le
  | inr s => have := s.isLt; show 2 * s.val + 1 ≤ 2 * k; omega

private lemma pd_ty_inl (a b : ℕ) (T : TypedTrees a b) (s : Fin (treeK a b)) :
    T.ty (T.tree.contour.getD (treePos (Sum.inl s)) []) =
      if s.val % 2 = 1 then VType.out else VType.inp := by
  have hk : treeK a b = 2 * a + 2 * b + 2 := rfl
  have hs := s.isLt
  have hlt : treePos (Sum.inl s : TreeVtx (treeK a b)) ≤ 2 * treeK a b :=
    pd_treePos_le (by omega) _
  rw [pd_tt_ty_val T hlt]
  have hpos : treePos (Sum.inl s : TreeVtx (treeK a b)) =
      if s.val + 1 < treeK a b then 2 * (s.val + 1) else 0 := by
    show 2 * (s.val + 1) % (2 * treeK a b) = _
    split_ifs with h
    · exact Nat.mod_eq_of_lt (by omega)
    · have h2 : s.val + 1 = treeK a b := by omega
      rw [h2]; simp
  rw [hpos]
  split_ifs <;> first | rfl | (exfalso; omega)

private lemma pd_ty_inr (a b : ℕ) (T : TypedTrees a b) (r : Fin (treeK a b)) :
    T.ty (T.tree.contour.getD (treePos (Sum.inr r)) []) = VType.lat := by
  have hr := r.isLt
  have hlt : treePos (Sum.inr r : TreeVtx (treeK a b)) ≤ 2 * treeK a b :=
    pd_treePos_le (by unfold treeK; omega) _
  rw [pd_tt_ty_val T hlt]
  have : treePos (Sum.inr r : TreeVtx (treeK a b)) % 2 = 1 := by
    show (2 * r.val + 1) % 2 = 1; omega
  rw [if_pos this]

private lemma pd_ty_G (a b : ℕ) (T : TypedTrees a b) :
    T.ty (T.tree.contour.getD (2 * (2 * a + 1)) []) = VType.inp := by
  have hlt : 2 * (2 * a + 1) ≤ 2 * treeK a b := by unfold treeK; omega
  rw [pd_tt_ty_val T hlt]
  split_ifs <;> first | rfl | (exfalso; omega)

open Classical in
private lemma pd_cs_sum {m n : ℕ} {L : Finset ℤ} (t : VType) (f : Option (AsgLab m n L) → ℝ) :
    ∑ o : {o : Option (AsgLab m n L) // AsgCompat t o}, f o.1 =
      match t with
      | VType.out => ∑ i : Fin m, f (some (Sum.inl i))
      | VType.inp => ∑ j : Fin n, f (some (Sum.inr (Sum.inl j)))
      | VType.lat => ∑ α : {α : ℤ // α ∈ L}, f (some (Sum.inr (Sum.inr α))) := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun o => AsgCompat t o)) (fun o => by simp) f,
    Finset.sum_filter]
  rw [show (∑ o : Option (AsgLab m n L), if AsgCompat t o then f o else 0) =
      ∑ o : Option (AsgLab m n L), (fun o => if AsgCompat t o then f o else 0) o from rfl,
    ob_sum_opt (fun o => if AsgCompat t o then f o else 0)]
  cases t <;> simp [AsgCompat]


/-! ### Bridge definitions and statements -/

/-- A typed ordered tree (root type `o`) as a rooted typed tree. -/
private def pd_toRooted {k : ℕ} (T : TypedOrdTree k) : RootedTypedTree VType.out k where
  tree := T.tree
  ty := T.ty
  card_vtx := T.card_vtx
  off_support := T.off_support
  root_ty := T.root_out
  root_ext := by decide
  edge_joins := T.edge_joins
  latent_alt := T.latent_alt

open Classical in
/-- The vertex weight of `pathVal`: the factor at the vertex `u` evaluated at the value `o`. -/
private noncomputable def pd_Wr {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ)
    (R : ℝ) (B : ℕ) {m n : ℕ} (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (g : ℤ → Ω → ℝ) (a b : ℕ) (T : TypedTrees a b) (u : List ℕ)
    (o : Option (AsgLab m n (cutoffLabels J ℓ))) : ℝ :=
  if T.ty u ≠ VType.lat then
    (asgVal μ lam o ^ T.tree.degAt u / (B : ℝ)) *
      (if u = [] then asgVal Fd (fun _ : Fin n => (0 : ℝ)) o else 1) *
      (if u = T.tree.contour.getD (2 * (2 * a + 1)) [] then
        asgVal (fun _ : Fin m => (0 : ℝ)) Gd o else 1)
  else
    ∫ ω, (∏ τ ∈ (Finset.range (2 * treeK a b)).filter
        (fun τ => τ % 2 = 1 ∧ T.tree.contour.getD τ [] = u),
      cutoffXi β ℓ J R (cornerLabel a τ) g (asgLabel o) ω) ∂P

open Classical in
private lemma pd_val_sum {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ)
    (R : ℝ) (B : ℕ) {m n : ℕ} (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (g : ℤ → Ω → ℝ) (a b : ℕ) (T : TypedTrees a b) :
    (∑' x : TreeAsg T.tree T.ty m n (cutoffLabels J ℓ),
        pathVal P β ℓ J R B Fd Gd μ lam g (a, b) T x) =
      ∏ u : {u // u ∈ T.tree.vtxs.toFinset},
        ∑ o : {o : Option (AsgLab m n (cutoffLabels J ℓ)) // AsgCompat (T.ty u.1) o},
          ((pd_Wr P β ℓ J R B Fd Gd μ lam g a b T u.1 o.1 : ℝ) : ℂ) := by
  have h1 : ∀ x : TreeAsg T.tree T.ty m n (cutoffLabels J ℓ),
      pathVal P β ℓ J R B Fd Gd μ lam g (a, b) T x =
        ∏ v ∈ T.tree.vtxs.toFinset,
          ((pd_Wr P β ℓ J R B Fd Gd μ lam g a b T v (x.1 v) : ℝ) : ℂ) := by
    intro x
    rw [pd_pathVal_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    unfold pd_Wr
    by_cases hv : T.ty v ≠ VType.lat
    · simp only [hv, if_true, ne_eq, not_false_eq_true]
    · simp only [hv, if_false]
  rw [tsum_congr h1]
  exact pd_asg_prod_sum T.tree T.ty (fun v o => ((pd_Wr P β ℓ J R B Fd Gd μ lam g a b T v o : ℝ) : ℂ))

open Classical in
private lemma pd_class_prod {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {g : ℤ → Ω → ℝ} (hg : IsStdGaussianFamily P g) (β : ℝ) (ℓ J : ℕ)
    (R : ℝ) (B : ℕ) {m n : ℕ} (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (a b : ℕ)
    (e : {p : TreeMatch (treeK a b) × TreeMatch (treeK a b) // treeRetained p} ≃ TypedTrees a b)
    (he : ClassFibreMap a b e)
    (π : {p : TreeMatch (treeK a b) × TreeMatch (treeK a b) // treeRetained p}) :
    ∏ V : Quotient (treeSetoid π.1), treeClassFactor β ℓ J R B μ lam Fd Gd a b π.1 V =
      ∏ u : {u // u ∈ (e π).tree.vtxs.toFinset},
        ∑ o : {o : Option (AsgLab m n (cutoffLabels J ℓ)) // AsgCompat ((e π).ty u.1) o},
          pd_Wr P β ℓ J R B Fd Gd μ lam g a b (e π) u.1 o.1 := by
  obtain ⟨hA, hB, hC, hD⟩ := lem_app_vol_closed_encoding_ii a b e he
  obtain ⟨ι, hinj, hmem, hsurj, hι⟩ := he π
  have hk0 : 0 < treeK a b := by unfold treeK; omega
  have hkdef : treeK a b = 2 * a + 2 * b + 2 := rfl
  have key : ∀ V : Quotient (treeSetoid π.1),
      treeClassFactor β ℓ J R B μ lam Fd Gd a b π.1 V =
        ∑ o : {o : Option (AsgLab m n (cutoffLabels J ℓ)) // AsgCompat ((e π).ty (ι V)) o},
          pd_Wr P β ℓ J R B Fd Gd μ lam g a b (e π) (ι V) o.1 := by
    intro V
    induction V using Quotient.inductionOn with
    | _ x =>
    change treeClassFactor β ℓ J R B μ lam Fd Gd a b π.1 (treeMk π.1 x) =
      ∑ o : {o : Option (AsgLab m n (cutoffLabels J ℓ)) // AsgCompat ((e π).ty (ι (treeMk π.1 x))) o},
          pd_Wr P β ℓ J R B Fd Gd μ lam g a b (e π) (ι (treeMk π.1 x)) o.1
    rw [hι x]
    cases x with
    | inr r =>
      have hlat := pd_ty_inr a b (e π) r
      rw [pd_cs_sum _ (fun o => pd_Wr P β ℓ J R B Fd Gd μ lam g a b (e π)
        ((e π).tree.contour.getD (treePos (Sum.inr r)) []) o)]
      rw [hlat]
      dsimp only
      have hne : ¬ ∃ e' : Fin (treeK a b), treeMk π.1 (Sum.inl e') = treeMk π.1 (Sum.inr r) := by
        rintro ⟨e', h⟩
        have h1 := congrArg ι h
        rw [hι, hι] at h1
        have h2 := (hA π e').1
        rw [h1] at h2
        exact h2 hlat
      unfold treeClassFactor
      rw [if_neg hne]
      have hS := hB π r
      have hW : ∀ α : {α : ℤ // α ∈ cutoffLabels J ℓ},
          pd_Wr P β ℓ J R B Fd Gd μ lam g a b (e π)
            ((e π).tree.contour.getD (treePos (Sum.inr r)) []) (some (Sum.inr (Sum.inr α))) =
          ∫ ω, (∏ r' ∈ Finset.univ.filter (fun r' : Fin (treeK a b) =>
              treeMk π.1 (Sum.inr r') = treeMk π.1 (Sum.inr r)),
            cutoffXi β ℓ J R (treeLabel a r') g α.1 ω) ∂P := by
        intro α
        rw [pd_Wr, if_neg (not_not.mpr hlat)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        dsimp only
        rw [hS]
        symm
        refine Finset.prod_bij (fun r' _ => 2 * r'.val + 1) ?_ ?_ ?_ ?_
        · intro r' hr'
          have hr'' := (Finset.mem_filter.mp hr').2
          have hr3 := r'.isLt
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega, hr''⟩
        · intro r1 _ r2 _ h
          exact Fin.ext (by omega)
        · intro τ hτ
          obtain ⟨hτ1, hτ2, hτ3⟩ := Finset.mem_filter.mp hτ
          have hτ4 := Finset.mem_range.mp hτ1
          refine ⟨⟨τ / 2, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by show 2 * (τ / 2) + 1 = τ; omega⟩
          show (e π).tree.contour.getD (2 * (τ / 2) + 1) [] = _
          rw [show 2 * (τ / 2) + 1 = τ by omega]
          exact hτ3
        · intro r' _
          rw [cornerLabel_eq_treeLabel a b r']
          rfl
      rw [Fintype.sum_congr _ _ hW]
      rw [Finset.sum_coe_sort (cutoffLabels J ℓ)
        (fun α => ∫ ω, (∏ r' ∈ Finset.univ.filter (fun r' : Fin (treeK a b) =>
              treeMk π.1 (Sum.inr r') = treeMk π.1 (Sum.inr r)),
            cutoffXi β ℓ J R (treeLabel a r') g α ω) ∂P)]
      exact (cutoff_latent_value hg β ℓ J R a _).symm
    | inl s =>
      obtain ⟨hext, hcard⟩ := hA π s
      have htyS := pd_ty_inl a b (e π) s
      have hex : ∃ e' : Fin (treeK a b), treeMk π.1 (Sum.inl e') = treeMk π.1 (Sum.inl s) :=
        ⟨s, rfl⟩
      unfold treeClassFactor
      rw [if_pos hex]
      by_cases hs : s.val % 2 = 1
      · have hout : (e π).ty ((e π).tree.contour.getD (treePos (Sum.inl s)) []) = VType.out := by
          rw [htyS, if_pos hs]
        have hodd : ∃ e' : Fin (treeK a b), treeMk π.1 (Sum.inl e') = treeMk π.1 (Sum.inl s) ∧
            e'.val % 2 = 1 := ⟨s, rfl, hs⟩
        rw [pd_cs_sum _ (fun o => pd_Wr P β ℓ J R B Fd Gd μ lam g a b (e π)
          ((e π).tree.contour.getD (treePos (Sum.inl s)) []) o)]
        rw [hout]
        dsimp only
        have hnG : (e π).tree.contour.getD (treePos (Sum.inl s)) [] ≠
            (e π).tree.contour.getD (2 * (2 * a + 1)) [] := by
          intro h
          rw [h, pd_ty_G] at hout
          exact absurd hout (by decide)
        rw [if_pos hodd, hcard]
        simp only [hC π (Sum.inl s)]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        unfold pd_Wr
        have hnl : (e π).ty ((e π).tree.contour.getD (treePos (Sum.inl s)) []) ≠ VType.lat := by
          rw [hout]; decide
        rw [if_pos hnl]
        rw [if_neg hnG]
        by_cases hu0 : (e π).tree.contour.getD (treePos (Sum.inl s)) [] = []
        · simp only [if_pos hu0, asgVal, div_eq_inv_mul, pow_one, mul_one]
          ring
        · simp only [if_neg hu0, asgVal, div_eq_inv_mul, pow_zero, mul_one]
      · have hinp : (e π).ty ((e π).tree.contour.getD (treePos (Sum.inl s)) []) = VType.inp := by
          rw [htyS, if_neg hs]
        have hnodd : ¬ ∃ e' : Fin (treeK a b), treeMk π.1 (Sum.inl e') = treeMk π.1 (Sum.inl s) ∧
            e'.val % 2 = 1 := by
          rintro ⟨e', h1, h2⟩
          have h3 := congrArg ι h1
          rw [hι, hι] at h3
          have h4 := pd_ty_inl a b (e π) e'
          rw [h3, htyS, if_pos h2, if_neg hs] at h4
          exact absurd h4 (by decide)
        rw [pd_cs_sum _ (fun o => pd_Wr P β ℓ J R B Fd Gd μ lam g a b (e π)
          ((e π).tree.contour.getD (treePos (Sum.inl s)) []) o)]
        rw [hinp]
        dsimp only
        have hn0 : (e π).tree.contour.getD (treePos (Sum.inl s)) [] ≠ [] := by
          intro h
          have h5 := (e π).root_out
          rw [← h, hinp] at h5
          exact absurd h5 (by decide)
        have hnl : (e π).ty ((e π).tree.contour.getD (treePos (Sum.inl s)) []) ≠ VType.lat := by
          rw [hinp]; decide
        rw [if_neg hnodd, hcard]
        simp only [hD π (Sum.inl s)]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        unfold pd_Wr
        rw [if_pos hnl, if_neg hn0]
        by_cases hug : (e π).tree.contour.getD (treePos (Sum.inl s)) [] =
            (e π).tree.contour.getD (2 * (2 * a + 1)) []
        · simp only [if_pos hug, asgVal, div_eq_inv_mul, pow_one, mul_one]
          ring
        · simp only [if_neg hug, asgVal, div_eq_inv_mul, pow_zero, mul_one]
  have hbij : Function.Bijective (fun V : Quotient (treeSetoid π.1) =>
      (⟨ι V, List.mem_toFinset.mpr (hmem V)⟩ : {u // u ∈ (e π).tree.vtxs.toFinset})) := by
    refine ⟨fun V W h => hinj (congrArg Subtype.val h), fun u => ?_⟩
    obtain ⟨V, hV⟩ := hsurj u.1 (List.mem_toFinset.mp u.2)
    exact ⟨V, Subtype.ext hV⟩
  exact Fintype.prod_bijective _ hbij _ _ (fun V => key V)

private lemma pd_mono_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {g : ℤ → Ω → ℝ} (hg : IsStdGaussianFamily P g) (β : ℝ) (ℓ J : ℕ)
    (R : ℝ) (B : ℕ) {m n : ℕ} (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (a b : ℕ) :
    ((treeMono β ℓ J R B μ lam Fd Gd a b : ℝ) : ℂ) =
      ∑' T : TypedTrees a b, ∑' x : TreeAsg T.tree T.ty m n (cutoffLabels J ℓ),
        pathVal P β ℓ J R B Fd Gd μ lam g (a, b) T x := by
  classical
  obtain ⟨e, he⟩ := lem_app_vol_closed_encoding_i a b
  haveI : Finite (TypedTrees a b) := (typedOrdTree_card_le (treeK a b)).1
  letI : Fintype (TypedTrees a b) := Fintype.ofFinite _
  have hfin : ∀ T : TypedTrees a b, Finite (TreeAsg T.tree T.ty m n (cutoffLabels J ℓ)) :=
    fun T => ob_finite_asg _ _ _ _ _
  have hT : ∀ T : TypedTrees a b, ∑' x : TreeAsg T.tree T.ty m n (cutoffLabels J ℓ),
      pathVal P β ℓ J R B Fd Gd μ lam g (a, b) T x =
      ∏ u : {u // u ∈ T.tree.vtxs.toFinset},
        ∑ o : {o : Option (AsgLab m n (cutoffLabels J ℓ)) // AsgCompat (T.ty u.1) o},
          ((pd_Wr P β ℓ J R B Fd Gd μ lam g a b T u.1 o.1 : ℝ) : ℂ) :=
    fun T => pd_val_sum P β ℓ J R B Fd Gd μ lam g a b T
  rw [tsum_fintype]
  unfold treeMono
  rw [Complex.ofReal_sum]
  simp only [apply_ite Complex.ofReal, Complex.ofReal_zero]
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun p => treeRetained p) (Finset.univ.filter (fun p => treeRetained p))
    (fun p => by simp) (fun p => ((∏ V : Quotient (treeSetoid p), treeClassFactor β ℓ J R B μ lam Fd Gd a b p V : ℝ) : ℂ))]
  rw [← Equiv.sum_comp e (fun T => ∑' x : TreeAsg T.tree T.ty m n (cutoffLabels J ℓ),
      pathVal P β ℓ J R B Fd Gd μ lam g (a, b) T x)]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [hT, pd_class_prod hg β ℓ J R B Fd Gd μ lam a b e he π]
  push_cast
  rfl

open Classical in
private lemma pd_cs_ite {m n : ℕ} {L : Finset ℤ} (t : VType) (f : Option (AsgLab m n L) → ℝ) :
    ∑ o : Option (AsgLab m n L), (if AsgCompat t o then f o else 0) =
      match t with
      | VType.out => ∑ i : Fin m, f (some (Sum.inl i))
      | VType.inp => ∑ j : Fin n, f (some (Sum.inr (Sum.inl j)))
      | VType.lat => ∑ α : {α : ℤ // α ∈ L}, f (some (Sum.inr (Sum.inr α))) := by
  rw [ob_sum_opt (fun o => if AsgCompat t o then f o else 0)]
  cases t <;> simp [AsgCompat]

private lemma pd_xi_abs_le {Ω : Type} {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (ℓ J : ℕ) (R : ℝ)
    (g : ℤ → Ω → ℝ) (l : ℕ) (α : ℤ) (ω : Ω) :
    |cutoffXi β ℓ J R l g α ω| ≤ cutoffVarpi β ℓ J l α * max 1 R := by
  have hR1 : (0 : ℝ) ≤ max 1 R := le_trans zero_le_one (le_max_left _ _)
  obtain ⟨h0, -⟩ := ob_cutoffVarpi_range hβ ℓ J l α
  unfold cutoffXi
  rw [abs_mul, abs_of_nonneg h0]
  refine mul_le_mul_of_nonneg_left ?_ h0
  split_ifs with h
  · exact h.trans (le_max_right _ _)
  · simpa using hR1

private lemma pd_lat_bound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (ℓ J : ℕ) (R : ℝ) (g : ℤ → Ω → ℝ) (lab : ℕ → ℕ)
    (Cu : Finset ℕ) (hCu : Cu.Nonempty) :
    ∑ α ∈ cutoffLabels J ℓ, |∫ ω, (∏ τ ∈ Cu, cutoffXi β ℓ J R (lab τ) g α ω) ∂P| ≤
      (max 1 R) ^ Cu.card := by
  obtain ⟨τ0, hτ0⟩ := hCu
  have hR1 : (1 : ℝ) ≤ max 1 R := le_max_left _ _
  have hR0 : (0 : ℝ) ≤ max 1 R := le_trans zero_le_one hR1
  have h1 : ∀ α, |∫ ω, (∏ τ ∈ Cu, cutoffXi β ℓ J R (lab τ) g α ω) ∂P| ≤
      cutoffVarpi β ℓ J (lab τ0) α * (max 1 R) ^ Cu.card := by
    intro α
    have hpt : ∀ ω, ‖∏ τ ∈ Cu, cutoffXi β ℓ J R (lab τ) g α ω‖ ≤
        cutoffVarpi β ℓ J (lab τ0) α * (max 1 R) ^ Cu.card := by
      intro ω
      rw [norm_prod]
      calc ∏ τ ∈ Cu, ‖cutoffXi β ℓ J R (lab τ) g α ω‖
          ≤ ∏ τ ∈ Cu, (cutoffVarpi β ℓ J (lab τ) α * max 1 R) := by
            refine Finset.prod_le_prod₀ (fun τ _ => norm_nonneg _) (fun τ _ => ?_)
            rw [Real.norm_eq_abs]
            exact pd_xi_abs_le hβ ℓ J R g (lab τ) α ω
        _ = (cutoffVarpi β ℓ J (lab τ0) α * max 1 R) *
              ∏ τ ∈ Cu.erase τ0, (cutoffVarpi β ℓ J (lab τ) α * max 1 R) :=
            (Finset.mul_prod_erase Cu _ hτ0).symm
        _ ≤ (cutoffVarpi β ℓ J (lab τ0) α * max 1 R) * ∏ τ ∈ Cu.erase τ0, max 1 R := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (ob_cutoffVarpi_range hβ ℓ J _ α).1 hR0)
            refine Finset.prod_le_prod₀ (fun τ _ => mul_nonneg (ob_cutoffVarpi_range hβ ℓ J _ α).1 hR0)
              (fun τ _ => ?_)
            calc cutoffVarpi β ℓ J (lab τ) α * max 1 R ≤ 1 * max 1 R :=
                  mul_le_mul_of_nonneg_right (ob_cutoffVarpi_range hβ ℓ J _ α).2 hR0
              _ = max 1 R := one_mul _
        _ = cutoffVarpi β ℓ J (lab τ0) α * (max 1 R) ^ Cu.card := by
            rw [Finset.prod_const, Finset.card_erase_of_mem hτ0]
            have hc : 1 ≤ Cu.card := Finset.card_pos.mpr ⟨τ0, hτ0⟩
            obtain ⟨c, hc'⟩ : ∃ c, Cu.card = c + 1 := ⟨Cu.card - 1, by omega⟩
            rw [hc']
            simp only [Nat.add_sub_cancel]
            ring
    have := MeasureTheory.norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => ∏ τ ∈ Cu, cutoffXi β ℓ J R (lab τ) g α ω)
      (C := cutoffVarpi β ℓ J (lab τ0) α * (max 1 R) ^ Cu.card) (Filter.Eventually.of_forall hpt)
    simpa using this
  refine (Finset.sum_le_sum fun α _ => h1 α).trans ?_
  rw [← Finset.sum_mul]
  calc (∑ α ∈ cutoffLabels J ℓ, cutoffVarpi β ℓ J (lab τ0) α) * (max 1 R) ^ Cu.card
      ≤ 1 * (max 1 R) ^ Cu.card :=
        mul_le_mul_of_nonneg_right (ob_cutoffVarpi_sum hβ ℓ J _) (pow_nonneg hR0 _)
    _ = _ := one_mul _


private lemma pd_ext_term_bound {N B : ℕ} (v fF fG : Fin N → ℝ) (γ C bF bG : ℝ) (hγ : 1 ≤ γ)
    (hC : 1 ≤ C) (hv : ∀ i, |v i| ≤ C) (hN : (N : ℝ) ≤ γ * B) (hbF : 0 ≤ bF) (hbG : 0 ≤ bG)
    (hf : ∀ i, |fF i| ≤ bF) (hg : ∀ i, |fG i| ≤ bG) (p : ℕ) :
    ∑ i, |v i ^ p / (B : ℝ) * fF i * fG i| ≤ γ * C ^ p * bF * bG := by
  have h1 : ∀ i, |v i ^ p / (B : ℝ) * fF i * fG i| ≤ |v i ^ p / (B : ℝ)| * bF * bG := by
    intro i
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _)) (hg i) (abs_nonneg _)
      (mul_nonneg (abs_nonneg _) hbF)
  calc ∑ i, |v i ^ p / (B : ℝ) * fF i * fG i| ≤ ∑ i, |v i ^ p / (B : ℝ)| * bF * bG :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = (∑ i, |v i ^ p / (B : ℝ)|) * bF * bG := by rw [← Finset.sum_mul, ← Finset.sum_mul]
    _ ≤ (γ * C ^ p) * bF * bG := by
        have := ob_ext_sum (B := B) v γ C hγ hC hv hN p
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hbF) hbG

open Classical in
/-- The per-vertex bound function of the path sum. -/
private noncomputable def pd_bnd (R γ C CF CG : ℝ) (a b : ℕ) (T : TypedTrees a b) (u : List ℕ) : ℝ :=
  (if T.ty u ≠ VType.lat then γ else 1) * C ^ (if T.ty u ≠ VType.lat then T.tree.degAt u else 0) *
    (if u = [] then CF else 1) * (if u = T.tree.contour.getD (2 * (2 * a + 1)) [] then CG else 1) *
    (max 1 R) ^ (if T.ty u = VType.lat then
      ((Finset.range (2 * treeK a b)).filter
        (fun τ => τ % 2 = 1 ∧ T.tree.contour.getD τ [] = u)).card else 0)

open Classical in
private lemma pd_vertex_bound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (ℓ J : ℕ) (R : ℝ) (B : ℕ) {m n : ℕ}
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (μ : Fin m → ℝ) (lam : Fin n → ℝ) (g : ℤ → Ω → ℝ)
    (γ C CF CG : ℝ) (hγ : 1 ≤ γ) (hC : 1 ≤ C) (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (hμ : ∀ i, |μ i| ≤ C) (hlam : ∀ j, |lam j| ≤ C) (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B)
    (hF : ∀ i, |Fd i| ≤ CF) (hG : ∀ j, |Gd j| ≤ CG) (a b : ℕ) (T : TypedTrees a b)
    (u : List ℕ) (hu : u ∈ T.tree.vtxs) :
    ∑ o : Option (AsgLab m n (cutoffLabels J ℓ)),
        (if AsgCompat (T.ty u) o then |pd_Wr P β ℓ J R B Fd Gd μ lam g a b T u o| else 0) ≤
      pd_bnd R γ C CF CG a b T u := by
  classical
  have hk : treeK a b = 2 * a + 2 * b + 2 := rfl
  by_cases hl : T.ty u = VType.lat
  · have hu0 : u ≠ [] := by
      rintro rfl; rw [T.root_out] at hl; exact absurd hl (by decide)
    have huG : u ≠ T.tree.contour.getD (2 * (2 * a + 1)) [] := by
      intro h; rw [h, pd_ty_G] at hl; exact absurd hl (by decide)
    obtain ⟨j, hj, hju⟩ := (pd_tt_pinv T).2.2.2.1 u hu
    have hjodd : j % 2 = 1 := (pd_tt_lat T hj).mp (by rw [hju]; exact hl)
    have hCu : ((Finset.range (2 * treeK a b)).filter
        (fun τ => τ % 2 = 1 ∧ T.tree.contour.getD τ [] = u)).Nonempty :=
      ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hjodd, hju⟩⟩
    rw [pd_cs_ite]
    rw [hl]
    dsimp only
    unfold pd_bnd
    simp only [hl, hu0, huG, ne_eq, not_true_eq_false, if_false, if_true, pow_zero, one_mul,
      mul_one]
    have hW : ∀ α : {α : ℤ // α ∈ cutoffLabels J ℓ},
        |pd_Wr P β ℓ J R B Fd Gd μ lam g a b T u (some (Sum.inr (Sum.inr α)))| =
        |∫ ω, (∏ τ ∈ (Finset.range (2 * treeK a b)).filter
            (fun τ => τ % 2 = 1 ∧ T.tree.contour.getD τ [] = u),
          cutoffXi β ℓ J R (cornerLabel a τ) g α.1 ω) ∂P| := by
      intro α
      rw [pd_Wr, if_neg (not_not.mpr hl)]
      rfl
    rw [Fintype.sum_congr _ _ hW]
    rw [Finset.sum_coe_sort (cutoffLabels J ℓ)
      (fun α => |∫ ω, (∏ τ ∈ (Finset.range (2 * treeK a b)).filter
            (fun τ => τ % 2 = 1 ∧ T.tree.contour.getD τ [] = u),
          cutoffXi β ℓ J R (cornerLabel a τ) g α ω) ∂P|)]
    exact pd_lat_bound P hβ ℓ J R g (cornerLabel a) _ hCu
  · have hnl : T.ty u ≠ VType.lat := hl
    have hbF : 0 ≤ (if u = [] then CF else 1) := by split_ifs <;> linarith
    have hbG : 0 ≤ (if u = T.tree.contour.getD (2 * (2 * a + 1)) [] then CG else 1) := by
      split_ifs <;> linarith
    rw [pd_cs_ite]
    unfold pd_bnd
    simp only [hnl, ne_eq, not_false_eq_true, if_true, hl, if_false, pow_zero, mul_one]
    cases hty : T.ty u
    · dsimp only
      have hbd := pd_ext_term_bound (B := B) μ
        (fun i => if u = [] then asgVal Fd (fun _ : Fin n => (0 : ℝ))
          (some (Sum.inl i) : Option (AsgLab m n (cutoffLabels J ℓ))) else 1)
        (fun i => if u = T.tree.contour.getD (2 * (2 * a + 1)) [] then
          asgVal (fun _ : Fin m => (0 : ℝ)) Gd
            (some (Sum.inl i) : Option (AsgLab m n (cutoffLabels J ℓ))) else 1)
        γ C _ _ hγ hC hμ hm hbF hbG
        (fun i => by
          split_ifs
          · simpa [asgVal] using hF i
          · simp)
        (fun i => by
          split_ifs
          · simpa [asgVal] using hCG
          · simp) (T.tree.degAt u)
      refine le_trans (le_of_eq ?_) hbd
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold pd_Wr
      rw [if_pos hnl]
      rfl
    · dsimp only
      have hbd := pd_ext_term_bound (B := B) lam
        (fun j => if u = [] then asgVal Fd (fun _ : Fin n => (0 : ℝ))
          (some (Sum.inr (Sum.inl j)) : Option (AsgLab m n (cutoffLabels J ℓ))) else 1)
        (fun j => if u = T.tree.contour.getD (2 * (2 * a + 1)) [] then
          asgVal (fun _ : Fin m => (0 : ℝ)) Gd
            (some (Sum.inr (Sum.inl j)) : Option (AsgLab m n (cutoffLabels J ℓ))) else 1)
        γ C _ _ hγ hC hlam hn hbF hbG
        (fun j => by
          split_ifs
          · simpa [asgVal] using hCF
          · simp)
        (fun j => by
          split_ifs
          · simpa [asgVal] using hG j
          · simp) (T.tree.degAt u)
      refine le_trans (le_of_eq ?_) hbd
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold pd_Wr
      rw [if_pos hnl]
      rfl
    · exact absurd hty hl


private lemma pd_card_odd (k : ℕ) :
    ((Finset.range (2 * k)).filter (fun τ => τ % 2 = 1)).card = k := by
  rw [show (Finset.range (2 * k)).filter (fun τ => τ % 2 = 1) =
      Finset.image (fun r => 2 * r + 1) (Finset.range k) by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨τ / 2, by omega, by omega⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨by omega, by omega⟩]
  rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]

private lemma pd_lat_corner_sum (a b : ℕ) (T : TypedTrees a b) :
    ∑ u ∈ T.tree.vtxs.toFinset.filter (fun u => T.ty u = VType.lat),
      ((Finset.range (2 * treeK a b)).filter
        (fun τ => τ % 2 = 1 ∧ T.tree.contour.getD τ [] = u)).card = treeK a b := by
  classical
  have hk : 0 < treeK a b := by unfold treeK; omega
  refine Eq.trans ?_ (pd_card_odd (treeK a b))
  rw [Finset.card_eq_sum_card_fiberwise (f := fun τ => T.tree.contour.getD τ [])
    (t := T.tree.vtxs.toFinset.filter (fun u => T.ty u = VType.lat))]
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.filter_filter]
  · intro τ hτ
    have hτ' := Finset.mem_filter.mp (Finset.mem_coe.mp hτ)
    have hlt := Finset.mem_range.mp hτ'.1
    simp only [Finset.mem_coe, Finset.mem_filter, List.mem_toFinset]
    exact ⟨pd_tt_mem T (by omega), (pd_tt_lat T (by omega)).mpr hτ'.2⟩

open Classical in
private lemma pd_bnd_prod (R γ C CF CG : ℝ) (hγ : 1 ≤ γ) (hC : 1 ≤ C) (hCF : 0 ≤ CF)
    (hCG : 0 ≤ CG) (a b : ℕ) (T : TypedTrees a b) :
    ∏ u ∈ T.tree.vtxs.toFinset, pd_bnd R γ C CF CG a b T u ≤
      CF * CG * γ * (γ * C * max 1 R) ^ (treeK a b) := by
  have hR1 : 1 ≤ max 1 R := le_max_left _ _
  obtain ⟨hs1, hs2, -, -⟩ := ob_deg_sums (pd_toRooted T)
  have hs1' : ∑ u ∈ T.tree.vtxs.toFinset.filter (fun u => T.ty u ≠ VType.lat), T.tree.degAt u
      = treeK a b := hs1
  have hroot : ([] : List ℕ) ∈ T.tree.vtxs.toFinset := by
    simpa using ob_pt_root_mem T.tree
  have hGv : T.tree.contour.getD (2 * (2 * a + 1)) [] ∈ T.tree.vtxs.toFinset := by
    simpa using pd_tt_mem T (show 2 * (2 * a + 1) ≤ 2 * treeK a b by unfold treeK; omega)
  have hcard : T.tree.vtxs.toFinset.card = treeK a b + 1 := by
    rw [List.toFinset_card_of_nodup (ob_pt_nodup _), T.card_vtx]
  unfold pd_bnd
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib]
  have e1 : ∏ u ∈ T.tree.vtxs.toFinset, (if T.ty u ≠ VType.lat then γ else 1) =
      γ ^ (T.tree.vtxs.toFinset.filter (fun u => T.ty u ≠ VType.lat)).card := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  have e2 : ∏ u ∈ T.tree.vtxs.toFinset, C ^ (if T.ty u ≠ VType.lat then T.tree.degAt u else 0) =
      C ^ treeK a b := by
    rw [Finset.prod_pow_eq_pow_sum, ← Finset.sum_filter, hs1']
  have e3 : ∏ u ∈ T.tree.vtxs.toFinset, (if u = [] then CF else 1) = CF := by
    rw [Finset.prod_ite_eq' _ _ (fun _ => CF), if_pos hroot]
  have e4 : ∏ u ∈ T.tree.vtxs.toFinset,
      (if u = T.tree.contour.getD (2 * (2 * a + 1)) [] then CG else 1) = CG := by
    rw [Finset.prod_ite_eq' _ _ (fun _ => CG), if_pos hGv]
  have e5 : ∏ u ∈ T.tree.vtxs.toFinset, (max 1 R) ^ (if T.ty u = VType.lat then
      ((Finset.range (2 * treeK a b)).filter
        (fun τ => τ % 2 = 1 ∧ T.tree.contour.getD τ [] = u)).card else 0) = (max 1 R) ^ treeK a b := by
    rw [Finset.prod_pow_eq_pow_sum, ← Finset.sum_filter, pd_lat_corner_sum]
  rw [e1, e2, e3, e4, e5]
  have hext : (T.tree.vtxs.toFinset.filter (fun u => T.ty u ≠ VType.lat)).card ≤ treeK a b + 1 :=
    hcard ▸ Finset.card_filter_le _ _
  have hg1 : γ ^ (T.tree.vtxs.toFinset.filter (fun u => T.ty u ≠ VType.lat)).card ≤
      γ ^ (treeK a b + 1) := pow_le_pow_right₀ hγ hext
  have hRR : 0 ≤ (max 1 R) ^ treeK a b := by positivity
  calc γ ^ (T.tree.vtxs.toFinset.filter (fun u => T.ty u ≠ VType.lat)).card * C ^ treeK a b *
        CF * CG * (max 1 R) ^ treeK a b
      ≤ γ ^ (treeK a b + 1) * C ^ treeK a b * CF * CG * (max 1 R) ^ treeK a b := by
        gcongr
    _ = CF * CG * γ * (γ * C * max 1 R) ^ (treeK a b) := by
        rw [mul_pow, mul_pow, pow_succ]; ring


private lemma pd_val_bound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (ℓ J : ℕ) (R : ℝ) (B : ℕ) {m n : ℕ}
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (μ : Fin m → ℝ) (lam : Fin n → ℝ) (g : ℤ → Ω → ℝ)
    (γ C CF CG : ℝ) (hγ : 1 ≤ γ) (hC : 1 ≤ C) (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (hμ : ∀ i, |μ i| ≤ C) (hlam : ∀ j, |lam j| ≤ C) (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B)
    (hF : ∀ i, |Fd i| ≤ CF) (hG : ∀ j, |Gd j| ≤ CG) (a b : ℕ) (T : TypedTrees a b) :
    ∑' x : TreeAsg T.tree T.ty m n (cutoffLabels J ℓ),
        ‖pathVal P β ℓ J R B Fd Gd μ lam g (a, b) T x‖ ≤
      CF * CG * γ * (γ * C * max 1 R) ^ (treeK a b) := by
  classical
  haveI : Finite (TreeAsg T.tree T.ty m n (cutoffLabels J ℓ)) := ob_finite_asg _ _ _ _ _
  letI : Fintype (TreeAsg T.tree T.ty m n (cutoffLabels J ℓ)) := Fintype.ofFinite _
  rw [tsum_fintype]
  set V := T.tree.vtxs.toFinset with hV
  let W' : List ℕ → Option (AsgLab m n (cutoffLabels J ℓ)) → ℝ := fun u o =>
    if AsgCompat (T.ty u) o then |pd_Wr P β ℓ J R B Fd Gd μ lam g a b T u o| else 0
  have hW'0 : ∀ u o, 0 ≤ W' u o := by
    intro u o; simp only [W']; split_ifs <;> first | exact abs_nonneg _ | exact le_rfl
  have hnorm : ∀ x : TreeAsg T.tree T.ty m n (cutoffLabels J ℓ),
      ‖pathVal P β ℓ J R B Fd Gd μ lam g (a, b) T x‖ = ∏ u : {u // u ∈ V}, W' u.1 (x.1 u.1) := by
    intro x
    have h1 : pathVal P β ℓ J R B Fd Gd μ lam g (a, b) T x =
        ∏ v ∈ T.tree.vtxs.toFinset,
          ((pd_Wr P β ℓ J R B Fd Gd μ lam g a b T v (x.1 v) : ℝ) : ℂ) := by
      rw [pd_pathVal_prod]
      refine Finset.prod_congr rfl fun v _ => ?_
      unfold pd_Wr
      by_cases hv : T.ty v ≠ VType.lat
      · simp only [hv, if_true, ne_eq, not_false_eq_true]
      · simp only [hv, if_false]
    rw [h1, norm_prod, ← Finset.prod_coe_sort V]
    refine Finset.prod_congr rfl fun u _ => ?_
    have hc := x.2.2 u.1 (List.mem_toFinset.mp u.2)
    simp only [W', hc, if_true, Complex.norm_real, Real.norm_eq_abs]
  let ι : TreeAsg T.tree T.ty m n (cutoffLabels J ℓ) →
      ({u // u ∈ V} → Option (AsgLab m n (cutoffLabels J ℓ))) := fun x u => x.1 u.1
  have hι : Function.Injective ι := by
    intro x y h
    apply Subtype.ext
    funext u
    by_cases hu : u ∈ T.tree.vtxs
    · exact congrFun h ⟨u, by simpa [hV] using hu⟩
    · have hx : x.1 u = none := by
        by_contra hne; exact hu ((x.2.1 u).mpr hne)
      have hy : y.1 u = none := by
        by_contra hne; exact hu ((y.2.1 u).mpr hne)
      rw [hx, hy]
  calc ∑ x : TreeAsg T.tree T.ty m n (cutoffLabels J ℓ),
        ‖pathVal P β ℓ J R B Fd Gd μ lam g (a, b) T x‖
      = ∑ x : TreeAsg T.tree T.ty m n (cutoffLabels J ℓ), ∏ u : {u // u ∈ V}, W' u.1 (ι x u) :=
        Finset.sum_congr rfl fun x _ => hnorm x
    _ = ∑ φ ∈ Finset.univ.image ι, ∏ u : {u // u ∈ V}, W' u.1 (φ u) := by
        rw [Finset.sum_image (fun x _ y _ h => hι h)]
    _ ≤ ∑ φ : ({u // u ∈ V} → Option (AsgLab m n (cutoffLabels J ℓ))),
          ∏ u : {u // u ∈ V}, W' u.1 (φ u) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun φ _ _ => ?_
        exact Finset.prod_nonneg fun u _ => hW'0 _ _
    _ = ∏ u : {u // u ∈ V}, ∑ o, W' u.1 o := by
        rw [Finset.prod_univ_sum]
        simp [Fintype.piFinset_univ]
    _ ≤ ∏ u : {u // u ∈ V}, pd_bnd R γ C CF CG a b T u.1 := by
        refine Finset.prod_le_prod₀ (fun u _ => Finset.sum_nonneg fun o _ => hW'0 _ _)
          (fun u _ => ?_)
        exact pd_vertex_bound P hβ ℓ J R B Fd Gd μ lam g γ C CF CG hγ hC hCF hCG hμ hlam hm hn hF hG
          a b T u.1 (List.mem_toFinset.mp u.2)
    _ = ∏ u ∈ V, pd_bnd R γ C CF CG a b T u := Finset.prod_coe_sort V _
    _ ≤ _ := pd_bnd_prod R γ C CF CG hγ hC hCF hCG a b T


/-! ### BRIDGE-MARKER -/

/-! ### Analytic part: the odd geometric expansion of `iotaF` and the extension bound -/

/-- Coefficient `(-1)^a s^{-(a+1)}` of the odd expansion `ι_s(x) = ∑_a (-1)^a s^{-a-1} x^{2a+1}`. -/
private def pd_cf (s : ℝ) (a : ℕ) : ℝ := (-1 : ℝ) ^ a * s⁻¹ ^ (a + 1)

/-- Partial sums of the odd expansion, as an odd polynomial. -/
private noncomputable def pd_polyN (s : ℝ) (N : ℕ) : Polynomial ℝ :=
  ∑ a ∈ Finset.range N, Polynomial.C (pd_cf s a) * Polynomial.X ^ (2 * a + 1)

private lemma pd_polyN_eval (s : ℝ) (N : ℕ) (x : ℝ) :
    (pd_polyN s N).eval x = ∑ a ∈ Finset.range N, pd_cf s a * x ^ (2 * a + 1) := by
  simp [pd_polyN, Polynomial.eval_finset_sum]

private lemma pd_polyN_odd (s : ℝ) (N : ℕ) (x : ℝ) :
    (pd_polyN s N).eval (-x) = -(pd_polyN s N).eval x := by
  rw [pd_polyN_eval, pd_polyN_eval, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Odd.neg_pow ⟨a, by ring⟩]; ring

private lemma pd_polyN_coeff (s : ℝ) (N a : ℕ) :
    (pd_polyN s N).coeff (2 * a + 1) = if a < N then pd_cf s a else 0 := by
  simp only [pd_polyN, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : a < N
  · rw [Finset.sum_eq_single a]
    · simp [h]
    · intro a' _ ha'
      simp [Ne.symm ha']
    · intro ha; exact absurd (Finset.mem_range.mpr h) ha
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun a' ha' => ?_
    have hne : a ≠ a' := fun h2 => h (by have := Finset.mem_range.mp ha'; omega)
    simp [hne]

private lemma pd_iota_err (s : ℝ) (hs : 0 < s) (N : ℕ) (x : ℝ) :
    iotaF s x - ∑ a ∈ Finset.range N, pd_cf s a * x ^ (2 * a + 1) =
      (-1 : ℝ) ^ N * s⁻¹ ^ N * x ^ (2 * N + 1) / (x ^ 2 + s) := by
  have hx : x ^ 2 + s ≠ 0 := by positivity
  have hs0 : s ≠ 0 := hs.ne'
  induction N with
  | zero => simp [iotaF]
  | succ N ih =>
    rw [Finset.sum_range_succ, ← sub_sub, ih]
    unfold pd_cf
    have hst : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0
    field_simp
    linear_combination (-(x * x ^ (N * 2) * s⁻¹ ^ N * (-1) ^ N)) * hst

private lemma pd_iota_err_bound (s D : ℝ) (hs : 0 < s) (N : ℕ) (x : ℝ) (hx : |x| ≤ D) :
    |iotaF s x - ∑ a ∈ Finset.range N, pd_cf s a * x ^ (2 * a + 1)| ≤
      D / s * (D ^ 2 / s) ^ N := by
  rw [pd_iota_err s hs N x]
  have hD : 0 ≤ D := (abs_nonneg x).trans hx
  have hx2 : x ^ 2 ≤ D ^ 2 := by
    have := sq_le_sq' (by linarith [abs_le.mp hx]) (abs_le.mp hx).2
    exact this
  have hpos : 0 < x ^ 2 + s := by positivity
  rw [abs_div, abs_of_pos hpos, abs_mul, abs_mul, abs_pow, abs_pow, abs_pow, abs_neg, abs_one,
    one_pow, one_mul, abs_inv, abs_of_pos hs, div_le_iff₀ hpos]
  have h1 : |x| ^ (2 * N + 1) = |x| * (x ^ 2) ^ N := by
    rw [pow_succ, pow_mul, sq_abs]; ring
  rw [h1]
  have h2 : (x ^ 2) ^ N ≤ (D ^ 2) ^ N := pow_le_pow_left₀ (sq_nonneg x) hx2 N
  have h3 : s ≤ x ^ 2 + s := by nlinarith
  calc s⁻¹ ^ N * (|x| * (x ^ 2) ^ N)
      ≤ s⁻¹ ^ N * (D * (D ^ 2) ^ N) := by
        gcongr
    _ = D / s * (D ^ 2 / s) ^ N * s := by
        rw [div_pow, inv_pow]; field_simp
    _ ≤ D / s * (D ^ 2 / s) ^ N * (x ^ 2 + s) := by
        gcongr

section PdOrth
open scoped Matrix.Norms.L2Operator

private lemma pd_norm_left_orth {a b : ℕ} (U : Matrix (Fin a) (Fin a) ℝ) (hU : Uᵀ * U = 1)
    (X : Matrix (Fin a) (Fin b) ℝ) : ‖U * X‖ = ‖X‖ := by
  have hUh : Uᴴ * U = 1 := by rw [Matrix.conjTranspose_eq_transpose_of_trivial]; exact hU
  have h : ‖U * X‖ * ‖U * X‖ = ‖X‖ * ‖X‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, ← Matrix.l2_opNorm_conjTranspose_mul_self]
    congr 1
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U X, hUh, Matrix.one_mul]
  exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).mp h

private lemma pd_norm_right_orth {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℝ)
    (W : Matrix (Fin b) (Fin b) ℝ) (hW : Wᵀ * W = 1) : ‖X * W‖ = ‖X‖ := by
  calc ‖X * W‖ = ‖(X * W)ᴴ‖ := (Matrix.l2_opNorm_conjTranspose _).symm
    _ = ‖Wᴴ * Xᴴ‖ := by rw [Matrix.conjTranspose_mul]
    _ = ‖Xᴴ‖ := by
      refine pd_norm_left_orth Wᴴ ?_ Xᴴ
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
      exact mul_eq_one_comm.mp hW
    _ = ‖X‖ := Matrix.l2_opNorm_conjTranspose X

private theorem pd_opNorm_conj_diag {k : ℕ} (U : Matrix (Fin k) (Fin k) ℝ) (hU : Uᵀ * U = 1)
    (d : Fin k → ℝ) (hd : ∀ i, |d i| ≤ 1) : opNorm (U * Matrix.diagonal d * Uᵀ) ≤ 1 := by
  rw [opNorm_eq_norm]
  rw [pd_norm_right_orth _ Uᵀ (by rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp hU),
    pd_norm_left_orth U hU, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simpa using hd i

end PdOrth

private lemma pd_supOn_le (D : ℝ) (h : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hh : ∀ x ∈ Set.Icc (-D) D, |h x| ≤ M) : supOn D h ≤ M := by
  unfold supOn
  exact Real.iSup_le (fun x => hh x.1 x.2) hM

private lemma pd_supOn_nonneg (D : ℝ) (h : ℝ → ℝ) : 0 ≤ supOn D h := by
  unfold supOn
  exact Real.iSup_nonneg fun _ => abs_nonneg _

/-- The extension bound for arbitrary (unnormalised) diagonal tests. -/
private lemma pd_ext_bound (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (ℓ J : ℕ) (R : ℝ) (D : ℝ) (hD : volDR cert R CSig γstar ≤ D) (f g : ℝ → ℝ)
    (hfc : ContinuousOn f (Set.Icc (-D) D)) (hfo : ∀ x ∈ Set.Icc (-D) D, f (-x) = -f x)
    (hgc : ContinuousOn g (Set.Icc (-D) D)) (hgo : ∀ x ∈ Set.Icc (-D) D, g (-x) = -g x)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) :
    |treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f g| ≤
      γstar * ((1 + ∑ i, |Fd i|) * (1 + ∑ j, |Gd j|)) * supOn D f * supOn D g := by
  obtain ⟨-, hb, -, hdF, hdG, -, -, -⟩ :=
    lem_app_vol_tree_extension_ii cert γstar CSig Fp S hS ℓ J R D hD f g hfc hfo hgc hgo
  set sF := 1 + ∑ i, |Fd i| with hsF
  set sG := 1 + ∑ j, |Gd j| with hsG
  have hsF0 : 1 ≤ sF := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (Fd i)); linarith
  have hsG0 : 1 ≤ sG := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (Gd i)); linarith
  have hz : ∀ Gd' : Fin n → ℝ, treeRespExt Fp.β ℓ J R B S.μ S.lam (0 : Fin m → ℝ) Gd' D f g = 0 := by
    intro Gd'
    have h := hdF 1 (0 : Fin m → ℝ) (0 : Fin m → ℝ) Gd'
    simp only [Pi.zero_apply, mul_zero, add_zero, one_mul] at h
    have h2 : (fun _ : Fin m => (0 : ℝ)) = (0 : Fin m → ℝ) := rfl
    rw [h2] at h
    linarith
  have hzG : ∀ Fd' : Fin m → ℝ, treeRespExt Fp.β ℓ J R B S.μ S.lam Fd' (0 : Fin n → ℝ) D f g = 0 := by
    intro Fd'
    have h := hdG 1 Fd' (0 : Fin n → ℝ) (0 : Fin n → ℝ)
    simp only [Pi.zero_apply, mul_zero, add_zero, one_mul] at h
    have h2 : (fun _ : Fin n => (0 : ℝ)) = (0 : Fin n → ℝ) := rfl
    rw [h2] at h
    linarith
  have hF1 : ∀ (Fd' : Fin m → ℝ) (Gd' : Fin n → ℝ) (c : ℝ),
      treeRespExt Fp.β ℓ J R B S.μ S.lam (fun i => c * Fd' i) Gd' D f g =
        c * treeRespExt Fp.β ℓ J R B S.μ S.lam Fd' Gd' D f g := by
    intro Fd' Gd' c
    have h := hdF c Fd' (0 : Fin m → ℝ) Gd'
    simp only [Pi.zero_apply, add_zero] at h
    rw [h, hz Gd'] 
    ring
  have hG1 : ∀ (Fd' : Fin m → ℝ) (Gd' : Fin n → ℝ) (c : ℝ),
      treeRespExt Fp.β ℓ J R B S.μ S.lam Fd' (fun j => c * Gd' j) D f g =
        c * treeRespExt Fp.β ℓ J R B S.μ S.lam Fd' Gd' D f g := by
    intro Fd' Gd' c
    have h := hdG c Fd' Gd' (0 : Fin n → ℝ)
    simp only [Pi.zero_apply, add_zero] at h
    rw [h, hzG Fd']
    ring
  have hFd : (fun i => sF * (sF⁻¹ * Fd i)) = Fd := by
    funext i; rw [← mul_assoc, mul_inv_cancel₀ (by linarith), one_mul]
  have hGd : (fun j => sG * (sG⁻¹ * Gd j)) = Gd := by
    funext j; rw [← mul_assoc, mul_inv_cancel₀ (by linarith), one_mul]
  have hnF : opNorm (S.uOut * Matrix.diagonal (fun i => sF⁻¹ * Fd i) * S.uOutᵀ) ≤ 1 := by
    refine pd_opNorm_conj_diag _ S.huOut _ fun i => ?_
    rw [abs_mul, abs_inv, abs_of_pos (by linarith : 0 < sF)]
    rw [inv_mul_le_iff₀ (by linarith)]
    have : |Fd i| ≤ ∑ i, |Fd i| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (Fd j)) (Finset.mem_univ i)
    linarith
  have hnG : opNorm (S.vIn * Matrix.diagonal (fun j => sG⁻¹ * Gd j) * S.vInᵀ) ≤ 1 := by
    refine pd_opNorm_conj_diag _ S.hvIn _ fun j => ?_
    rw [abs_mul, abs_inv, abs_of_pos (by linarith : 0 < sG)]
    rw [inv_mul_le_iff₀ (by linarith)]
    have : |Gd j| ≤ ∑ j, |Gd j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (Gd j)) (Finset.mem_univ j)
    linarith
  have h := hb (fun i => sF⁻¹ * Fd i) (fun j => sG⁻¹ * Gd j) _ _ rfl rfl hnF hnG
  have e : treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f g =
      sF * (sG * treeRespExt Fp.β ℓ J R B S.μ S.lam (fun i => sF⁻¹ * Fd i)
        (fun j => sG⁻¹ * Gd j) D f g) := by
    rw [← hG1, ← hF1, hFd, hGd]
  rw [e, abs_mul, abs_mul, abs_of_pos (by linarith : 0 < sF), abs_of_pos (by linarith : 0 < sG)]
  calc sF * (sG * |treeRespExt Fp.β ℓ J R B S.μ S.lam (fun i => sF⁻¹ * Fd i)
        (fun j => sG⁻¹ * Gd j) D f g|)
      ≤ sF * (sG * (γstar * supOn D f * supOn D g)) := by gcongr
    _ = γstar * (sF * sG) * supOn D f * supOn D g := by ring

private lemma pd_iota_abs (s : ℝ) (hs : 0 < s) (x : ℝ) : |iotaF s x| ≤ |x| / s := by
  unfold iotaF
  have hpos : 0 < x ^ 2 + s := by positivity
  rw [abs_div, abs_of_pos hpos]
  exact div_le_div_of_nonneg_left (abs_nonneg x) hs (by nlinarith)

private lemma pd_iota_cont (s : ℝ) (hs : 0 < s) : Continuous (iotaF s) := by
  unfold iotaF
  exact continuous_id.div (by fun_prop) (fun x => by positivity)

private lemma pd_iota_odd (s x : ℝ) : iotaF s (-x) = -iotaF s x := by
  unfold iotaF
  rw [neg_sq, neg_div]

/-- Odd and continuous on `[-D, D]`. -/
private def pd_COI (D : ℝ) (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Icc (-D) D) ∧ ∀ x ∈ Set.Icc (-D) D, f (-x) = -f x

private lemma pd_coi_comb (D : ℝ) (f f' : ℝ → ℝ) (c : ℝ) (hf : pd_COI D f) (hf' : pd_COI D f') :
    pd_COI D (fun x => f x + c * f' x) :=
  ⟨hf.1.add (hf'.1.const_smul c), fun x hx => by
    simp only [hf.2 x hx, hf'.2 x hx]; ring⟩

private lemma pd_coi_iota (D s : ℝ) (hs : 0 < s) : pd_COI D (iotaF s) :=
  ⟨(pd_iota_cont s hs).continuousOn, fun x _ => pd_iota_odd s x⟩

private lemma pd_coi_poly (D s : ℝ) (N : ℕ) : pd_COI D (fun x => (pd_polyN s N).eval x) :=
  ⟨(Polynomial.continuous _).continuousOn, fun x _ => pd_polyN_odd s N x⟩

private lemma pd_gamma_nonneg {m n B : ℕ} (Fp : FrozenParams m n B) (γstar CSig : ℝ)
    (hS : SizeFin Fp.C B γstar CSig) : 0 ≤ γstar := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · have h := Fp.hA; subst h0; simp [fro] at h
    · exact h0
  have h1 := hS.1
  have h2 : (1 : ℝ) ≤ ((max m n : ℕ) : ℝ) := by exact_mod_cast le_max_of_le_left hm
  have h3 : (0 : ℝ) < B := by exact_mod_cast Fp.hB
  by_contra h
  push_neg at h
  nlinarith

/-- The error of replacing `(ι_s, ι_u)` by the partial sums `(P_N^s, P_N^u)` in the extension. -/
private lemma pd_series_err (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (ℓ J : ℕ) (R : ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (s u : ℝ) (hs0 : 0 < s) (hu0 : 0 < u)
    (Dp : ℝ) (hDp0 : 0 ≤ Dp) (hDpD : ∀ x ∈ Set.Icc (-(volDR cert R CSig γstar)) (volDR cert R CSig γstar),
      |x| ≤ Dp) (hDps : Dp ^ 2 < s) (hDpu : Dp ^ 2 < u) (N : ℕ) :
    |treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd (volDR cert R CSig γstar) (iotaF s) (iotaF u) -
        treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd (volDR cert R CSig γstar)
          (fun x => (pd_polyN s N).eval x) (fun x => (pd_polyN u N).eval x)| ≤
      γstar * ((1 + ∑ i, |Fd i|) * (1 + ∑ j, |Gd j|)) *
        ((Dp / s * (Dp ^ 2 / s) ^ N) * (Dp / u) + (2 * Dp / s) * (Dp / u * (Dp ^ 2 / u) ^ N)) := by
  set D := volDR cert R CSig γstar with hDdef
  set K := γstar * ((1 + ∑ i, |Fd i|) * (1 + ∑ j, |Gd j|)) with hK
  have hqs0 : 0 ≤ Dp ^ 2 / s := by positivity
  have hqu0 : 0 ≤ Dp ^ 2 / u := by positivity
  have hι1 := pd_coi_iota D s hs0
  have hι2 := pd_coi_iota D u hu0
  have hP1 := pd_coi_poly D s N
  have hP2 := pd_coi_poly D u N
  -- (E1)
  obtain ⟨-, -, -, -, -, he1, -, -⟩ :=
    lem_app_vol_tree_extension_ii cert γstar CSig Fp S hS ℓ J R D le_rfl (iotaF s) (iotaF u)
      hι1.1 hι1.2 hι2.1 hι2.2
  obtain ⟨-, -, -, -, -, -, he2, -⟩ :=
    lem_app_vol_tree_extension_ii cert γstar CSig Fp S hS ℓ J R D le_rfl
      (fun x => (pd_polyN s N).eval x) (iotaF u) hP1.1 hP1.2 hι2.1 hι2.2
  have E1 := he1 (-1) _ hP1.1 hP1.2 Fd Gd
  have E2 := he2 (-1) _ hP2.1 hP2.2 Fd Gd
  set Ψ := fun f g => treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D f g with hΨ
  have hdecomp : Ψ (iotaF s) (iotaF u) - Ψ (fun x => (pd_polyN s N).eval x) (fun x => (pd_polyN u N).eval x) =
      Ψ (fun x => iotaF s x + (-1) * (pd_polyN s N).eval x) (iotaF u) +
        Ψ (fun x => (pd_polyN s N).eval x) (fun x => iotaF u x + (-1) * (pd_polyN u N).eval x) := by
    simp only [hΨ] at E1 E2 ⊢
    rw [E1, E2]; ring
  -- bounds
  have hh := pd_coi_comb D _ _ (-1) hι1 hP1
  have hk := pd_coi_comb D _ _ (-1) hι2 hP2
  have b1 := pd_ext_bound cert γstar CSig Fp S hS ℓ J R D le_rfl _ _ hh.1 hh.2 hι2.1 hι2.2 Fd Gd
  have b2 := pd_ext_bound cert γstar CSig Fp S hS ℓ J R D le_rfl _ _ hP1.1 hP1.2 hk.1 hk.2 Fd Gd
  have hγ : 0 ≤ K := by
    have h0 := pd_gamma_nonneg Fp γstar CSig hS
    rw [hK]; positivity
  have hDs : Dp ^ 2 / s ≤ 1 := by rw [div_le_one hs0]; exact hDps.le
  have hDu : Dp ^ 2 / u ≤ 1 := by rw [div_le_one hu0]; exact hDpu.le
  have hMh : supOn D (fun x => iotaF s x + (-1) * (pd_polyN s N).eval x) ≤
      Dp / s * (Dp ^ 2 / s) ^ N := by
    refine pd_supOn_le D _ _ (by positivity) fun x hx => ?_
    have := pd_iota_err_bound s Dp hs0 N x (hDpD x hx)
    rw [← pd_polyN_eval] at this
    convert this using 2
    ring
  have hMk : supOn D (fun x => iotaF u x + (-1) * (pd_polyN u N).eval x) ≤
      Dp / u * (Dp ^ 2 / u) ^ N := by
    refine pd_supOn_le D _ _ (by positivity) fun x hx => ?_
    have := pd_iota_err_bound u Dp hu0 N x (hDpD x hx)
    rw [← pd_polyN_eval] at this
    convert this using 2
    ring
  have hMι : supOn D (iotaF u) ≤ Dp / u := by
    refine pd_supOn_le D _ _ (by positivity) fun x hx => ?_
    exact (pd_iota_abs u hu0 x).trans (div_le_div_of_nonneg_right (hDpD x hx) hu0.le)
  have hMP : supOn D (fun x => (pd_polyN s N).eval x) ≤ 2 * Dp / s := by
    refine pd_supOn_le D _ _ (by positivity) fun x hx => ?_
    have e1 := pd_iota_err_bound s Dp hs0 N x (hDpD x hx)
    rw [← pd_polyN_eval] at e1
    have e2 := pd_iota_abs s hs0 x
    have e3 : |x| / s ≤ Dp / s := div_le_div_of_nonneg_right (hDpD x hx) hs0.le
    have e4 : (Dp ^ 2 / s) ^ N ≤ 1 := pow_le_one₀ hqs0 hDs
    have e5 : Dp / s * (Dp ^ 2 / s) ^ N ≤ Dp / s := by
      calc Dp / s * (Dp ^ 2 / s) ^ N ≤ Dp / s * 1 :=
            mul_le_mul_of_nonneg_left e4 (by positivity)
        _ = Dp / s := mul_one _
    have e6 : |(pd_polyN s N).eval x| ≤ |iotaF s x| + |iotaF s x - (pd_polyN s N).eval x| := by
      have := abs_sub_abs_le_abs_sub (iotaF s x) ((pd_polyN s N).eval x)
      have h7 := abs_sub_comm (iotaF s x) ((pd_polyN s N).eval x)
      calc |(pd_polyN s N).eval x| = |iotaF s x - (iotaF s x - (pd_polyN s N).eval x)| := by ring_nf
        _ ≤ |iotaF s x| + |iotaF s x - (pd_polyN s N).eval x| := abs_sub _ _
    calc |(pd_polyN s N).eval x| ≤ |iotaF s x| + |iotaF s x - (pd_polyN s N).eval x| := e6
      _ ≤ Dp / s + Dp / s := by linarith
      _ = 2 * Dp / s := by ring
  have hdiff : |Ψ (iotaF s) (iotaF u) -
      Ψ (fun x => (pd_polyN s N).eval x) (fun x => (pd_polyN u N).eval x)| ≤
      K * supOn D (fun x => iotaF s x + (-1) * (pd_polyN s N).eval x) * supOn D (iotaF u) +
      K * supOn D (fun x => (pd_polyN s N).eval x) *
        supOn D (fun x => iotaF u x + (-1) * (pd_polyN u N).eval x) := by
    rw [hdecomp]
    refine (abs_add_le _ _).trans (add_le_add b1 b2)
  refine hdiff.trans ?_
  have n1 := pd_supOn_nonneg D (iotaF u)
  have n2 := pd_supOn_nonneg D (fun x => (pd_polyN s N).eval x)
  have n3 := pd_supOn_nonneg D (fun x => iotaF s x + (-1) * (pd_polyN s N).eval x)
  have n4 := pd_supOn_nonneg D (fun x => iotaF u x + (-1) * (pd_polyN u N).eval x)
  have s1 : K * supOn D (fun x => iotaF s x + (-1) * (pd_polyN s N).eval x) * supOn D (iotaF u) ≤
      K * ((Dp / s * (Dp ^ 2 / s) ^ N) * (Dp / u)) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hMh hMι n1 (by positivity)) hγ
  have s2 : K * supOn D (fun x => (pd_polyN s N).eval x) *
      supOn D (fun x => iotaF u x + (-1) * (pd_polyN u N).eval x) ≤
      K * ((2 * Dp / s) * (Dp / u * (Dp ^ 2 / u) ^ N)) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hMP hMk n4 (by positivity)) hγ
  calc _ ≤ K * ((Dp / s * (Dp ^ 2 / s) ^ N) * (Dp / u)) +
        K * ((2 * Dp / s) * (Dp / u * (Dp ^ 2 / u) ^ N)) := add_le_add s1 s2
    _ = _ := by ring

private lemma pd_sum_trunc (p : Polynomial ℝ) (N : ℕ) (Q : ℕ → ℝ)
    (hN : ∀ a, N ≤ a → p.coeff (2 * a + 1) = 0) :
    ∑ a ∈ Finset.range (p.natDegree + 1), p.coeff (2 * a + 1) * Q a =
      ∑ a ∈ Finset.range N, p.coeff (2 * a + 1) * Q a := by
  have h1 : ∑ a ∈ Finset.range (p.natDegree + 1), p.coeff (2 * a + 1) * Q a =
      ∑ a ∈ Finset.range (p.natDegree + 1 + N), p.coeff (2 * a + 1) * Q a := by
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun a _ ha => ?_
    have : p.natDegree < 2 * a + 1 := by
      have := Finset.mem_range.not.mp ha; omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt this, zero_mul]
  have h2 : ∑ a ∈ Finset.range N, p.coeff (2 * a + 1) * Q a =
      ∑ a ∈ Finset.range (p.natDegree + 1 + N), p.coeff (2 * a + 1) * Q a := by
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun a _ ha => ?_
    rw [hN a (by have := Finset.mem_range.not.mp ha; omega), zero_mul]
  rw [h1, h2]

private lemma pd_def_sum {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (s u : ℝ) (N : ℕ) :
    def_app_vol_tree β ℓ J R B μ lam Fd Gd (pd_polyN s N) (pd_polyN u N) =
      ∑ p ∈ Finset.range N ×ˢ Finset.range N,
        pd_cf s p.1 * pd_cf u p.2 * treeMono β ℓ J R B μ lam Fd Gd p.1 p.2 := by
  have hs : ∀ a, N ≤ a → (pd_polyN s N).coeff (2 * a + 1) = 0 := fun a ha => by
    rw [pd_polyN_coeff, if_neg (by omega)]
  have hu : ∀ a, N ≤ a → (pd_polyN u N).coeff (2 * a + 1) = 0 := fun a ha => by
    rw [pd_polyN_coeff, if_neg (by omega)]
  unfold def_app_vol_tree
  have inner : ∀ a : ℕ, ∑ b ∈ Finset.range ((pd_polyN u N).natDegree + 1),
      (pd_polyN s N).coeff (2 * a + 1) * (pd_polyN u N).coeff (2 * b + 1) *
        treeMono β ℓ J R B μ lam Fd Gd a b =
      (pd_polyN s N).coeff (2 * a + 1) * ∑ b ∈ Finset.range N,
        (pd_polyN u N).coeff (2 * b + 1) * treeMono β ℓ J R B μ lam Fd Gd a b := by
    intro a
    have h := pd_sum_trunc (pd_polyN u N) N (fun b => treeMono β ℓ J R B μ lam Fd Gd a b) hu
    calc _ = (pd_polyN s N).coeff (2 * a + 1) * ∑ b ∈ Finset.range ((pd_polyN u N).natDegree + 1),
          (pd_polyN u N).coeff (2 * b + 1) * treeMono β ℓ J R B μ lam Fd Gd a b := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => by ring
      _ = _ := by rw [h]
  simp only [inner]
  rw [pd_sum_trunc (pd_polyN s N) N (fun a => ∑ b ∈ Finset.range N,
    (pd_polyN u N).coeff (2 * b + 1) * treeMono β ℓ J R B μ lam Fd Gd a b) hs]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [pd_polyN_coeff, pd_polyN_coeff, if_pos (Finset.mem_range.mp ha), if_pos (Finset.mem_range.mp hb)]
  ring


private lemma pd_series (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (ℓ J : ℕ) (R : ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (s u : ℝ) (hs0 : 0 < s) (hu0 : 0 < u)
    (hs : (volDR cert R CSig γstar) ^ 2 < s) (hu : (volDR cert R CSig γstar) ^ 2 < u)
    (hsum : Summable (fun p : ℕ × ℕ =>
      pd_cf s p.1 * pd_cf u p.2 * treeMono Fp.β ℓ J R B S.μ S.lam Fd Gd p.1 p.2)) :
    treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd (volDR cert R CSig γstar) (iotaF s) (iotaF u) =
      ∑' p : ℕ × ℕ, pd_cf s p.1 * pd_cf u p.2 * treeMono Fp.β ℓ J R B S.μ S.lam Fd Gd p.1 p.2 := by
  set D := volDR cert R CSig γstar with hDdef
  set Dp := max D 0 with hDp
  have hDp0 : 0 ≤ Dp := le_max_right _ _
  have hDpD : ∀ x ∈ Set.Icc (-D) D, |x| ≤ Dp := fun x hx =>
    (abs_le.mpr ⟨hx.1, hx.2⟩).trans (le_max_left _ _)
  have hDps : Dp ^ 2 < s := by
    rcases le_total D 0 with h | h
    · rw [hDp, max_eq_right h]; simpa using hs0
    · rw [hDp, max_eq_left h]; exact hs
  have hDpu : Dp ^ 2 < u := by
    rcases le_total D 0 with h | h
    · rw [hDp, max_eq_right h]; simpa using hu0
    · rw [hDp, max_eq_left h]; exact hu
  set K := γstar * ((1 + ∑ i, |Fd i|) * (1 + ∑ j, |Gd j|)) with hK
  set w : ℕ × ℕ → ℝ := fun p =>
    pd_cf s p.1 * pd_cf u p.2 * treeMono Fp.β ℓ J R B S.μ S.lam Fd Gd p.1 p.2 with hw
  -- the partial sums
  set aN : ℕ → ℝ := fun N => treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D
    (fun x => (pd_polyN s N).eval x) (fun x => (pd_polyN u N).eval x) with haN
  have haN_eq : ∀ N, aN N = ∑ p ∈ Finset.range N ×ˢ Finset.range N, w p := by
    intro N
    have hι1 := pd_coi_iota D s hs0
    have hι2 := pd_coi_iota D u hu0
    obtain ⟨-, -, -, -, -, -, -, hf⟩ :=
      lem_app_vol_tree_extension_ii cert γstar CSig Fp S hS ℓ J R D le_rfl (iotaF s) (iotaF u)
        hι1.1 hι1.2 hι2.1 hι2.2
    rw [haN]
    simp only
    rw [hf (pd_polyN s N) (pd_polyN u N) (pd_polyN_odd s N) (pd_polyN_odd u N) Fd Gd]
    exact pd_def_sum Fp.β ℓ J R B S.μ S.lam Fd Gd s u N
  -- convergence of the partial sums to the sum
  have hT1 : Filter.Tendsto aN Filter.atTop (nhds (∑' p, w p)) := by
    have hmono : Monotone (fun N : ℕ => Finset.range N ×ˢ Finset.range N) := by
      intro N M h
      exact Finset.product_subset_product (Finset.range_subset_range.mpr h)
        (Finset.range_subset_range.mpr h)
    have hcov : Filter.Tendsto (fun N : ℕ => Finset.range N ×ˢ Finset.range N) Filter.atTop
        Filter.atTop := by
      refine Filter.tendsto_atTop_finset_of_monotone hmono fun p => ⟨max p.1 p.2 + 1, ?_⟩
      simp only [Finset.mem_product, Finset.mem_range]
      omega
    have := (hsum.hasSum).comp hcov
    refine this.congr fun N => ?_
    simp only [Function.comp]
    exact (haN_eq N).symm
  -- convergence of the partial sums to the extension
  have hT2 : Filter.Tendsto aN Filter.atTop
      (nhds (treeRespExt Fp.β ℓ J R B S.μ S.lam Fd Gd D (iotaF s) (iotaF u))) := by
    have hqs0 : 0 ≤ Dp ^ 2 / s := by positivity
    have hqu0 : 0 ≤ Dp ^ 2 / u := by positivity
    have hqs1 : Dp ^ 2 / s < 1 := by rw [div_lt_one hs0]; exact hDps
    have hqu1 : Dp ^ 2 / u < 1 := by rw [div_lt_one hu0]; exact hDpu
    have hε : Filter.Tendsto (fun N : ℕ => K * ((Dp / s * (Dp ^ 2 / s) ^ N) * (Dp / u) +
        (2 * Dp / s) * (Dp / u * (Dp ^ 2 / u) ^ N))) Filter.atTop (nhds 0) := by
      have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one hqs0 hqs1
      have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hqu0 hqu1
      have h3 := ((((h1.const_mul (Dp / s)).mul_const (Dp / u)).add
        ((h2.const_mul (Dp / u)).const_mul (2 * Dp / s))).const_mul K)
      simpa using h3
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hε
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact pd_series_err cert γstar CSig Fp S hS ℓ J R Fd Gd s u hs0 hu0 Dp hDp0 hDpD hDps hDpu N
  exact tendsto_nhds_unique hT2 hT1


private lemma pd_pathZ_norm' (s u : ℝ) (a b : ℕ) (hs : 0 < s) (hu : 0 < u) :
    ‖pathZ s u (a, b)‖ = s⁻¹ ^ (a + 1) * u⁻¹ ^ (b + 1) := by
  rw [pd_pathZ_eq s u a b hs hu, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
    abs_neg, abs_one, one_pow, one_mul, abs_of_pos (by positivity), abs_of_pos (by positivity)]

private lemma pd_geom_alg (Kc s u : ℝ) (hK : 1 ≤ Kc) (hs : 0 < s) (hu : 0 < u) (a b : ℕ) :
    s⁻¹ ^ (a + 1) * u⁻¹ ^ (b + 1) * (4 ^ (2 * a + 2 * b + 2) * Kc ^ (2 * a + 2 * b + 2)) ≤
      (16 * Kc ^ 2 / s) ^ (a + 1) * (16 * Kc ^ 2 / u) ^ (b + 1) := by
  have h1 : (4 : ℝ) ^ (2 * a + 2 * b + 2) * Kc ^ (2 * a + 2 * b + 2) =
      (16 * Kc ^ 2) ^ (a + b + 1) := by
    rw [← mul_pow, show 2 * a + 2 * b + 2 = 2 * (a + b + 1) by ring, pow_mul]
    congr 1; ring
  have h2 : (16 * Kc ^ 2 / s) ^ (a + 1) * (16 * Kc ^ 2 / u) ^ (b + 1) =
      s⁻¹ ^ (a + 1) * u⁻¹ ^ (b + 1) * ((16 * Kc ^ 2) ^ (a + b + 1) * (16 * Kc ^ 2)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_pow, mul_pow]
    rw [show (16 * Kc ^ 2) ^ (a + b + 1) * (16 * Kc ^ 2) =
      (16 * Kc ^ 2) ^ (a + 1) * (16 * Kc ^ 2) ^ (b + 1) by rw [← pow_add, ← pow_succ]; congr 1; ring]
    ring
  rw [h1, h2]
  have hpos : 0 ≤ s⁻¹ ^ (a + 1) * u⁻¹ ^ (b + 1) * (16 * Kc ^ 2) ^ (a + b + 1) := by positivity
  have h16 : 1 ≤ 16 * Kc ^ 2 := by nlinarith
  calc s⁻¹ ^ (a + 1) * u⁻¹ ^ (b + 1) * (16 * Kc ^ 2) ^ (a + b + 1)
      = s⁻¹ ^ (a + 1) * u⁻¹ ^ (b + 1) * (16 * Kc ^ 2) ^ (a + b + 1) * 1 := by ring
    _ ≤ s⁻¹ ^ (a + 1) * u⁻¹ ^ (b + 1) * (16 * Kc ^ 2) ^ (a + b + 1) * (16 * Kc ^ 2) :=
        mul_le_mul_of_nonneg_left h16 hpos
    _ = _ := by ring


/-- `lem:app-vol-closed-path`(i), snapshot `cr-2026-10-23`. Declaration of record, absolute summability of
`Z(T) val(T,𝔞)` over `(a₁,a₂,T,𝔞)` and the identification of its sum with the cutoff response
`𝔑^{J,R}_ℓ[F,G](ι_s, ι_u)` (`lagRespCut`, radius `D_R`). Hypotheses: `SizeFin`, `Σ_out, Σ_in ≠ 0`,
`IsProbabilityMeasure`, the cutoff Gaussians `g`, `F = diag(Fd)` and `G = diag(Gd)` in the eigenbases of
`S` (the test entries enter only through `Fd`, `Gd`), and `s, u ≥ s_R`.

LaTeX (`sections/04-volatility/section.tex` l.2359–2368, verbatim):
```latex
\begin{lemma}[Path decomposition]\label{lem:app-vol-closed-path}
Let $\Sigmaout,\Sigmain\ne0$, and let $s,u\ge s_R$. The family
$\{Z(T)\operatorname{val}(T,\mathfrak a):a_1,a_2\ge0,\ T\in\mathcal T_{a_1,a_2},\ \mathfrak a\}$ is absolutely summable,
and its sum is
\[
\mathfrak k^{J,R}_\ell[F,G](s,u)\defeq\mathfrak R^{J,R}_\ell[F,G](\iota_s,\iota_u).
\]
This sum equals $\mathfrak K^{J,R}[F,G](s,u)$ of \cref{eqn:app-vol-closed-profile-kernel},
formed with the branch point of $\xi_1$ at $s$ and of $\xi_2$ at $u$.
\end{lemma}
```
-/
theorem lem_app_vol_closed_path_i {Ω : Type} [MeasurableSpace Ω] {m n B : ℕ}
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) (Fp : FrozenParams m n B)
    (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hout : Fp.C.Sout ≠ 0) (hin : Fp.C.Sin ≠ 0)
    {P : Measure Ω} [IsProbabilityMeasure P] (ℓ J : ℕ) (R : ℝ)
    {g : ℤ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (s u : ℝ)
    (hs : sRad cert γstar CSig R ≤ s) (hu : sRad cert γstar CSig R ≤ u) :
    Summable (fun q : PathIdx m n J ℓ =>
        ‖pathTerm P Fp.β ℓ J R B Fd Gd S.μ S.lam g s u q‖) ∧
    ∑' q : PathIdx m n J ℓ, pathTerm P Fp.β ℓ J R B Fd Gd S.μ S.lam g s u q =
      ((lagRespCut cert γstar CSig Fp.β ℓ J R B S.μ S.lam Fd Gd (iotaF s) (iotaF u) : ℝ) : ℂ) := by
  classical
  have hs0 : 0 < s := pd_sRad_pos cert γstar CSig R s hs
  have hu0 : 0 < u := pd_sRad_pos cert γstar CSig R u hu
  have hsD := pd_volDR_sq_lt cert γstar CSig R s hs
  have huD := pd_volDR_sq_lt cert γstar CSig R u hu
  -- constants
  obtain ⟨hS1, hS2, hS3⟩ := hS
  have hS' : SizeFin Fp.C B γstar CSig := ⟨hS1, hS2, hS3⟩
  set γ := max 1 γstar with hγdef
  set C := max 1 CSig with hCdef
  set Kc := γ * C * max 1 R with hKc
  have hγ : 1 ≤ γ := le_max_left _ _
  have hC : 1 ≤ C := le_max_left _ _
  have hR1 : 1 ≤ max 1 R := le_max_left _ _
  have hμ : ∀ i, |S.μ i| ≤ C := fun i =>
    (ob_abs_eig_le Fp.C.Sout S.uOut (S.μ i) i S.huOut (S.eigOut i)).trans
      (hS2.trans (le_max_right _ _))
  have hlam : ∀ j, |S.lam j| ≤ C := fun j =>
    (ob_abs_eig_le Fp.C.Sin S.vIn (S.lam j) j S.hvIn (S.eigIn j)).trans
      (hS3.trans (le_max_right _ _))
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hmn : ∀ q : ℕ, q ≤ max m n → (q : ℝ) ≤ γ * B := fun q hq =>
    ((Nat.cast_le.mpr hq).trans hS1).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hB)
  have hm : (m : ℝ) ≤ γ * B := hmn m (le_max_left _ _)
  have hn : (n : ℝ) ≤ γ * B := hmn n (le_max_right _ _)
  have hK1 : 1 ≤ Kc := by
    have : 1 ≤ γ * C := by nlinarith
    nlinarith
  have hsK : 64 * Kc ^ 2 ≤ s := by
    refine le_trans ?_ hs
    unfold sRad
    refine le_trans (le_of_eq ?_) (le_max_left _ _)
    rw [hKc]; ring
  have huK : 64 * Kc ^ 2 ≤ u := by
    refine le_trans ?_ hu
    unfold sRad
    refine le_trans (le_of_eq ?_) (le_max_left _ _)
    rw [hKc]; ring
  set CF := ∑ i, |Fd i| with hCF
  set CG := ∑ j, |Gd j| with hCG
  have hCF0 : 0 ≤ CF := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hCG0 : 0 ≤ CG := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hF : ∀ i, |Fd i| ≤ CF := fun i =>
    Finset.single_le_sum (fun j _ => abs_nonneg (Fd j)) (Finset.mem_univ i)
  have hG : ∀ j, |Gd j| ≤ CG := fun j =>
    Finset.single_le_sum (fun j _ => abs_nonneg (Gd j)) (Finset.mem_univ j)
  -- finiteness
  haveI hfinT : ∀ k : ℕ, Finite (TypedOrdTree k) := fun k => (typedOrdTree_card_le k).1
  haveI hfinA : ∀ (T : TypedOrdTree (treeK 0 0)), True := fun _ => trivial
  have hfinY : ∀ p : ℕ × ℕ, Finite (Σ T : TypedTrees p.1 p.2,
      TreeAsg T.tree T.ty m n (cutoffLabels J ℓ)) := by
    intro p
    haveI := hfinT (treeK p.1 p.2)
    haveI : ∀ T : TypedTrees p.1 p.2, Finite (TreeAsg T.tree T.ty m n (cutoffLabels J ℓ)) :=
      fun T => ob_finite_asg _ _ _ _ _
    infer_instance
  -- the family
  set f : PathIdx m n J ℓ → ℝ :=
    fun q => ‖pathTerm P Fp.β ℓ J R B Fd Gd S.μ S.lam g s u q‖ with hf
  have hf0 : ∀ q, 0 ≤ f q := fun q => norm_nonneg _
  have hfibre : ∀ p : ℕ × ℕ, ∑' y : (Σ T : TypedTrees p.1 p.2,
        TreeAsg T.tree T.ty m n (cutoffLabels J ℓ)), f ⟨p, y⟩ ≤
      CF * CG * γ * ((16 * Kc ^ 2 / s) ^ (p.1 + 1) * (16 * Kc ^ 2 / u) ^ (p.2 + 1)) := by
    rintro ⟨a, b⟩
    haveI := hfinY (a, b)
    haveI := hfinT (treeK a b)
    letI : Fintype (TypedTrees a b) := Fintype.ofFinite _
    haveI hfinA : ∀ T : TypedTrees a b, Finite (TreeAsg T.tree T.ty m n (cutoffLabels J ℓ)) :=
      fun T => ob_finite_asg _ _ _ _ _
    have hT : ∀ T : TypedTrees a b,
        ∑' x : TreeAsg T.tree T.ty m n (cutoffLabels J ℓ), f ⟨(a, b), ⟨T, x⟩⟩ ≤
          s⁻¹ ^ (a + 1) * u⁻¹ ^ (b + 1) * (CF * CG * γ * Kc ^ (treeK a b)) := by
      intro T
      have e : ∀ x : TreeAsg T.tree T.ty m n (cutoffLabels J ℓ), f ⟨(a, b), ⟨T, x⟩⟩ =
          (s⁻¹ ^ (a + 1) * u⁻¹ ^ (b + 1)) *
            ‖pathVal P Fp.β ℓ J R B Fd Gd S.μ S.lam g (a, b) T x‖ := by
        intro x
        simp only [hf, pathTerm]
        rw [norm_mul, pd_pathZ_norm' s u a b hs0 hu0]
      rw [tsum_congr e, tsum_mul_left]
      exact mul_le_mul_of_nonneg_left
        (pd_val_bound P Fp.hβ ℓ J R B Fd Gd S.μ S.lam g γ C CF CG hγ hC hCF0 hCG0 hμ hlam hm hn
          hF hG a b T) (by positivity)
    calc ∑' y : (Σ T : TypedTrees (a, b).1 (a, b).2,
          TreeAsg T.tree T.ty m n (cutoffLabels J ℓ)), f ⟨(a, b), y⟩
        = ∑' T : TypedTrees a b, ∑' x : TreeAsg T.tree T.ty m n (cutoffLabels J ℓ),
            f ⟨(a, b), ⟨T, x⟩⟩ :=
          Summable.tsum_sigma' (fun T => Summable.of_finite) Summable.of_finite
      _ ≤ ∑' T : TypedTrees a b, s⁻¹ ^ (a + 1) * u⁻¹ ^ (b + 1) * (CF * CG * γ * Kc ^ (treeK a b)) :=
          Summable.tsum_le_tsum hT Summable.of_finite Summable.of_finite
      _ = (Nat.card (TypedTrees a b) : ℝ) *
            (s⁻¹ ^ (a + 1) * u⁻¹ ^ (b + 1) * (CF * CG * γ * Kc ^ (treeK a b))) := by
          rw [tsum_const, nsmul_eq_mul]
      _ ≤ (4 : ℝ) ^ (treeK a b) *
            (s⁻¹ ^ (a + 1) * u⁻¹ ^ (b + 1) * (CF * CG * γ * Kc ^ (treeK a b))) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast (typedOrdTree_card_le (treeK a b)).2
      _ = CF * CG * γ * (s⁻¹ ^ (a + 1) * u⁻¹ ^ (b + 1) *
            (4 ^ (2 * a + 2 * b + 2) * Kc ^ (2 * a + 2 * b + 2))) := by
          unfold treeK; ring
      _ ≤ CF * CG * γ * ((16 * Kc ^ 2 / s) ^ (a + 1) * (16 * Kc ^ 2 / u) ^ (b + 1)) :=
          mul_le_mul_of_nonneg_left (pd_geom_alg Kc s u hK1 hs0 hu0 a b) (by positivity)
  -- summability of the geometric majorant
  have hrs : 16 * Kc ^ 2 / s ≤ 1 / 4 := by
    rw [div_le_iff₀ hs0]; nlinarith
  have hru : 16 * Kc ^ 2 / u ≤ 1 / 4 := by
    rw [div_le_iff₀ hu0]; nlinarith
  have hrs0 : 0 ≤ 16 * Kc ^ 2 / s := by positivity
  have hru0 : 0 ≤ 16 * Kc ^ 2 / u := by positivity
  have hgeo : Summable (fun p : ℕ × ℕ =>
      (16 * Kc ^ 2 / s) ^ (p.1 + 1) * (16 * Kc ^ 2 / u) ^ (p.2 + 1)) := by
    refine summable_mul_of_summable_norm (f := fun a : ℕ => (16 * Kc ^ 2 / s) ^ (a + 1))
      (g := fun b : ℕ => (16 * Kc ^ 2 / u) ^ (b + 1)) ?_ ?_
    · simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hrs0 _)]
      exact (summable_nat_add_iff 1).mpr
        (summable_geometric_of_lt_one hrs0 (by linarith))
    · simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hru0 _)]
      exact (summable_nat_add_iff 1).mpr
        (summable_geometric_of_lt_one hru0 (by linarith))
  have hsumfib : Summable (fun p : ℕ × ℕ => ∑' y : (Σ T : TypedTrees p.1 p.2,
      TreeAsg T.tree T.ty m n (cutoffLabels J ℓ)), f ⟨p, y⟩) :=
    Summable.of_nonneg_of_le (fun p => tsum_nonneg fun y => hf0 _) hfibre (hgeo.mul_left _)
  have hsumf : Summable f := by
    rw [summable_sigma_of_nonneg hf0]
    refine ⟨fun p => ?_, hsumfib⟩
    haveI := hfinY p
    exact Summable.of_finite
  refine ⟨hsumf, ?_⟩
  -- the sum
  have hpt : Summable (fun q : PathIdx m n J ℓ =>
      pathTerm P Fp.β ℓ J R B Fd Gd S.μ S.lam g s u q) := Summable.of_norm hsumf
  have hfib : ∀ p : ℕ × ℕ, ∑' y : (Σ T : TypedTrees p.1 p.2,
        TreeAsg T.tree T.ty m n (cutoffLabels J ℓ)),
      pathTerm P Fp.β ℓ J R B Fd Gd S.μ S.lam g s u ⟨p, y⟩ =
        ((pd_cf s p.1 * pd_cf u p.2 * treeMono Fp.β ℓ J R B S.μ S.lam Fd Gd p.1 p.2 : ℝ) : ℂ) := by
    rintro ⟨a, b⟩
    haveI := hfinY (a, b)
    haveI := hfinT (treeK a b)
    haveI hfinA : ∀ T : TypedTrees a b, Finite (TreeAsg T.tree T.ty m n (cutoffLabels J ℓ)) :=
      fun T => ob_finite_asg _ _ _ _ _
    rw [Summable.tsum_sigma' (fun T => Summable.of_finite) Summable.of_finite]
    have e : ∀ T : TypedTrees a b, ∑' x : TreeAsg T.tree T.ty m n (cutoffLabels J ℓ),
        pathTerm P Fp.β ℓ J R B Fd Gd S.μ S.lam g s u ⟨(a, b), ⟨T, x⟩⟩ =
        pathZ s u (a, b) * ∑' x : TreeAsg T.tree T.ty m n (cutoffLabels J ℓ),
          pathVal P Fp.β ℓ J R B Fd Gd S.μ S.lam g (a, b) T x := by
      intro T
      rw [← tsum_mul_left]
      rfl
    rw [tsum_congr e, tsum_mul_left, ← pd_mono_eq hg Fp.β ℓ J R B Fd Gd S.μ S.lam a b,
      pd_pathZ_eq s u a b hs0 hu0]
    unfold pd_cf
    push_cast
    ring
  rw [Summable.tsum_sigma' (fun p => by haveI := hfinY p; exact Summable.of_finite) hpt]
  rw [tsum_congr hfib]
  have hwsum : Summable (fun p : ℕ × ℕ =>
      pd_cf s p.1 * pd_cf u p.2 * treeMono Fp.β ℓ J R B S.μ S.lam Fd Gd p.1 p.2) := by
    have h1 := hpt.sigma
    have h2 : Summable (fun p : ℕ × ℕ =>
        ((pd_cf s p.1 * pd_cf u p.2 * treeMono Fp.β ℓ J R B S.μ S.lam Fd Gd p.1 p.2 : ℝ) : ℂ)) := by
      refine h1.congr fun p => hfib p
    exact Complex.summable_ofReal.mp h2
  rw [← Complex.ofReal_tsum]
  congr 1
  exact (pd_series cert γstar CSig Fp S hS' ℓ J R Fd Gd s u hs0 hu0 hsD huD hwsum).symm

private lemma pd_cutoff_delta_ne {Ω : Type} [MeasurableSpace Ω] {m n B : ℕ}
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) (Fp : FrozenParams m n B)
    (hout : Fp.C.Sout ≠ 0) (hin : Fp.C.Sin ≠ 0)
    {P : Measure Ω} [IsProbabilityMeasure P] (ℓ J : ℕ) {R : ℝ} (hR : 0 < R)
    {g : ℤ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    (s u : ℝ) (hs : sRad cert γstar CSig R ≤ s) (hu : sRad cert γstar CSig R ≤ u) :
    profileDelta P Fp.C B (cutoffXi Fp.β ℓ J R 1 g) (cutoffXi Fp.β ℓ J R 2 g) s u ≠ 0 := by
  have hs0 : 0 < s := pd_sRad_pos cert γstar CSig R s hs
  have hu0 : 0 < u := pd_sRad_pos cert γstar CSig R u hu
  have hp := lem_app_vol_closed_cutoff_paired (ℓ := ℓ) (J := J) Fp.hβ.1 Fp.hβ.2 hR hg
  have hm1 := lem_app_vol_closed_cutoff_masses (ℓ := ℓ) (J := J)
    Fp.hβ.1 Fp.hβ.2 hR hg (Or.inl rfl)
  have hm2 := lem_app_vol_closed_cutoff_masses (ℓ := ℓ) (J := J)
    Fp.hβ.1 Fp.hβ.2 hR hg (Or.inr rfl)
  have hd := lem_app_vol_closed_determinant_ii Fp.hB hp hm1.2.2.2 hm2.2.2.2
    Fp.C hout hin hs0 hu0
  exact ne_of_gt (lt_of_lt_of_le hd.2 hd.1)

private lemma pd4_eqvgen_isLeft {k : ℕ} (p : TreeMatch k × TreeMatch k) (x y : TreeVtx k)
    (h : Relation.EqvGen (treeRel p) x y) : x.isLeft = y.isLeft := by
  induction h with
  | rel x y hr =>
    obtain ⟨r, h | h | h | h⟩ := hr <;> obtain ⟨hx, hy⟩ := h <;>
      subst hx <;> subst hy <;> rfl
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

private lemma pd4_truncMoment_zero (d : ℕ) (hd : d ≠ 0) (R : ℝ) (hR : R ≤ 0) :
    treeTruncMoment d R = 0 := by
  unfold treeTruncMoment
  rw [if_neg hd]
  have hz : (fun x : ℝ => if |x| ≤ R then x ^ d else 0) = fun _ => 0 := by
    funext x
    split_ifs with h
    · have hx : x = 0 := abs_eq_zero.mp (le_antisymm (h.trans hR) (abs_nonneg x))
      subst x
      simp [hd]
    · rfl
  rw [hz]
  simp

open Classical in
private lemma pd4_treeMono_zero {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (hR : R ≤ 0) (B : ℕ)
    (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (a b : ℕ) :
    treeMono β ℓ J R B μ lam Fd Gd a b = 0 := by
  unfold treeMono
  apply Finset.sum_eq_zero
  intro p _
  split_ifs with hp
  · have hk : 0 < treeK a b := by unfold treeK; omega
    set r0 : Fin (treeK a b) := ⟨0, hk⟩ with hr0
    apply Finset.prod_eq_zero (Finset.mem_univ (treeMk p (Sum.inr r0)))
    unfold treeClassFactor
    have hno : ¬ ∃ e : Fin (treeK a b), treeMk p (Sum.inl e) = treeMk p (Sum.inr r0) := by
      rintro ⟨e, he⟩
      have h1 := pd4_eqvgen_isLeft p _ _ (Quotient.exact he)
      simp at h1
    rw [if_neg hno]
    have hcard : (Finset.univ.filter fun r =>
        treeMk p (Sum.inr r) = treeMk p (Sum.inr r0)).card ≠ 0 := by
      apply Finset.card_ne_zero_of_mem (a := r0)
      simp
    simp only [pd4_truncMoment_zero _ hcard R hR, zero_mul]
  · rfl

private lemma pd4_tree_zero_of_nonpos {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (hR : R ≤ 0)
    (B : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (f₁ f₂ : Polynomial ℝ) :
    def_app_vol_tree β ℓ J R B μ lam Fd Gd f₁ f₂ = 0 := by
  unfold def_app_vol_tree
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  rw [pd4_treeMono_zero β ℓ J R hR B μ lam Fd Gd a b, mul_zero]

private lemma pd4_lagRespCut_nonpos (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (hR : R ≤ 0) (B : ℕ)
    (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (f₁ f₂ : ℝ → ℝ) :
    lagRespCut cert γstar CSig β ℓ J R B μ lam Fd Gd f₁ f₂ = 0 := by
  unfold lagRespCut treeRespExt
  have hz : (fun k : ℕ => def_app_vol_tree β ℓ J R B μ lam Fd Gd
      (treeApprox (volDR cert R CSig γstar) f₁ k)
      (treeApprox (volDR cert R CSig γstar) f₂ k)) = fun _ => 0 := by
    funext k
    exact pd4_tree_zero_of_nonpos β ℓ J R hR B μ lam Fd Gd _ _
  rw [hz]
  exact (tendsto_const_nhds (x := (0 : ℝ))).limUnder_eq

private lemma pd4_cutoffXi_zero {Ω : Type} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (hR : R ≤ 0)
    (l : ℕ) (g : ℤ → Ω → ℝ) : cutoffXi β ℓ J R l g = 0 := by
  funext α ω
  unfold cutoffXi
  split_ifs with h
  · have hx : g α ω = 0 := abs_eq_zero.mp (le_antisymm (h.trans hR) (abs_nonneg _))
    simp [hx]
  · simp

private lemma pd4_profileKernel_nonpos {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {m n : ℕ} (C : Muon.Covariances m n) (B : ℕ) (β : ℝ) (ℓ J : ℕ) (R : ℝ)
    (hR : R ≤ 0) (g : ℤ → Ω → ℝ) (Fm : Matrix (Fin m) (Fin m) ℝ)
    (Gm : Matrix (Fin n) (Fin n) ℝ) (s u : ℝ) :
    profileKernel P C B (cutoffXi β ℓ J R 1 g) (cutoffXi β ℓ J R 2 g) Fm Gm s u = 0 ∧
    profileDelta P C B (cutoffXi β ℓ J R 1 g) (cutoffXi β ℓ J R 2 g) s u = 1 := by
  have h1 := pd4_cutoffXi_zero β ℓ J R hR 1 g
  have h2 := pd4_cutoffXi_zero β ℓ J R hR 2 g
  rw [h1, h2]
  have hb : pairedB P (0 : ℤ → Ω → ℝ) 0 = fun _ _ => 0 := by
    funext q₁ q₂
    simp [pairedB]
  have he : pairedE P (0 : ℤ → Ω → ℝ) 0 = fun _ _ => 0 := by
    funext q₁ q₂
    simp [pairedE]
  constructor
  · simp [profileKernel, hb]
  · simp [profileDelta, closedDelta, hb, he]

private lemma pd4_path_nonpos {Ω : Type} [MeasurableSpace Ω] {m n B : ℕ}
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) (Fp : FrozenParams m n B)
    (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hout : Fp.C.Sout ≠ 0) (hin : Fp.C.Sin ≠ 0)
    {P : Measure Ω} [IsProbabilityMeasure P] (ℓ J : ℕ) (R : ℝ) (hR : R ≤ 0)
    {g : ℤ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (Fm : Matrix (Fin m) (Fin m) ℝ) (Gm : Matrix (Fin n) (Fin n) ℝ)
    (s u : ℝ) (hs : sRad cert γstar CSig R ≤ s) (hu : sRad cert γstar CSig R ≤ u) :
    ∑' q : PathIdx m n J ℓ, pathTerm P Fp.β ℓ J R B Fd Gd S.μ S.lam g s u q =
        ((profileKernel P Fp.C B (cutoffXi Fp.β ℓ J R 1 g)
          (cutoffXi Fp.β ℓ J R 2 g) Fm Gm s u : ℝ) : ℂ) ∧
    profileDelta P Fp.C B (cutoffXi Fp.β ℓ J R 1 g)
      (cutoffXi Fp.β ℓ J R 2 g) s u ≠ 0 := by
  have hsum := (lem_app_vol_closed_path_i cert γstar CSig Fp S hS hout hin
    ℓ J R hg Fd Gd s u hs hu).2
  have hlag := pd4_lagRespCut_nonpos cert γstar CSig Fp.β ℓ J R hR B
    S.μ S.lam Fd Gd (iotaF s) (iotaF u)
  have hk := pd4_profileKernel_nonpos P Fp.C B Fp.β ℓ J R hR g Fm Gm s u
  constructor
  · rw [hsum, hlag, hk.1]
  · rw [hk.2]
    norm_num

/-! ## P-D.17.P4: pointed trees and the path sum -/

/-! ## Before-counts of contour corners -/

/-- The number of visits of `w` strictly before the mark corner `(v, j)` (the `j`-th visit of `v`),
where `t = childCount w + 1` is the total number of visits of `w`. -/
private def pp_nbC (t : ℕ) : List ℕ → List ℕ → ℕ → ℕ
  | [], [], j => j
  | [], b :: _, _ => b + 1
  | a :: _, [], j => if a < j then t else 0
  | a :: w, b :: v, j => if a = b then pp_nbC t w v j else if a < b then t else 0

private lemma pp_cnt_map_cons0 (L : List (List ℕ)) (w : List ℕ) :
    (L.map (List.cons 0)).count (0 :: w) = L.count w :=
  List.count_map_of_injective _ _ (fun a b h => by simpa using h) _

private lemma pp_cnt_map_cons0_zero (L : List (List ℕ)) (w : List ℕ) (hw : ∀ w', w ≠ 0 :: w') :
    (L.map (List.cons 0)).count w = 0 := by
  rw [List.count_eq_zero]
  simp only [List.mem_map, not_exists, not_and]
  intro x _ h
  exact hw x h.symm

private lemma pp_cnt_map_inc (L : List (List ℕ)) (w : List ℕ) :
    (L.map pd_inc).count (pd_inc w) = L.count w :=
  List.count_map_of_injective _ _ (fun a b h => pd_inc_inj h) _

private lemma pp_cnt_map_inc_zero (L : List (List ℕ)) (w1 : List ℕ) :
    (L.map pd_inc).count (0 :: w1) = 0 := by
  rw [List.count_eq_zero]
  simp only [List.mem_map, not_exists, not_and]
  intro x _ h
  cases x with
  | nil => simp [pd_inc] at h
  | cons a y => simp [pd_inc] at h

private lemma pp_inc_eq_nil_iff (x : List ℕ) : pd_inc x = [] ↔ x = [] := by
  cases x <;> simp [pd_inc]

private lemma pp_contour_node_cons (P1 : PlaneTree) (cs : List PlaneTree) :
    (PlaneTree.node (P1 :: cs)).contour =
      [] :: (P1.contour.map (List.cons 0) ++ (PlaneTree.node cs).contour.map pd_inc) := by
  rw [pd_contour_node_cons, pd_contour_node]
  simp [pd_inc]

private lemma pp_cc_cons0 (P1 : PlaneTree) (cs : List PlaneTree) (w : List ℕ)
    (hw : w ∈ P1.vtxs) :
    (PlaneTree.node (P1 :: cs)).childCount (0 :: w) = P1.childCount w := by
  have := pd_pt_cc_idx (P1 :: cs) 0 (by simp) w (by simpa using hw)
  simpa using this

private lemma pp_cc_consinc (P1 : PlaneTree) (cs : List PlaneTree) (a : ℕ) (w : List ℕ)
    (hw : a :: w ∈ (PlaneTree.node cs).vtxs) :
    (PlaneTree.node (P1 :: cs)).childCount ((a + 1) :: w) = (PlaneTree.node cs).childCount (a :: w) := by
  have h1 := (pd_pt_mem_idx cs a w).mp hw
  obtain ⟨ha, hw'⟩ := h1
  have := pd_pt_cc_idx (P1 :: cs) (a + 1) (by simpa using ha) w (by simpa using hw')
  have h2 := pd_pt_cc_idx cs a ha w hw'
  simpa [h2] using this



private lemma pp_cnt_full (P : PlaneTree) : ∀ w ∈ P.vtxs, P.contour.count w = P.childCount w + 1 := by
  refine pd_plane_ind (fun P => ∀ w ∈ P.vtxs, P.contour.count w = P.childCount w + 1) ?_ ?_ P
  · intro w hw
    simp [PlaneTree.vtxs, vtxsForest] at hw
    subst hw
    simp [PlaneTree.contour, contourForest, pd_pt_cc_nil]
  · intro P1 cs ih1 ih2 w hw
    rw [pp_contour_node_cons]
    rcases (pd_mem_vtxs_cons.mp hw) with h | ⟨w1, hw1, rfl⟩ | ⟨w2, hw2, hne, rfl⟩
    · subst h
      have h2 := ih2 [] (pd_pt_root_mem _)
      rw [pd_pt_cc_nil] at h2 ⊢
      rw [List.count_cons, List.count_append]
      have e1 : (P1.contour.map (List.cons 0)).count [] = 0 :=
        pp_cnt_map_cons0_zero _ _ (by simp)
      have e2 : ((PlaneTree.node cs).contour.map pd_inc).count [] =
          (PlaneTree.node cs).contour.count [] := by
        have := pp_cnt_map_inc (PlaneTree.node cs).contour []
        simpa [pd_inc] using this
      rw [e1, e2, h2]
      simp
    · rw [pp_cc_cons0 P1 cs w1 hw1, List.count_cons, List.count_append, pp_cnt_map_cons0,
        pp_cnt_map_inc_zero, ih1 w1 hw1]
      simp
    · obtain ⟨a, w3, rfl⟩ : ∃ a w3, w2 = a :: w3 := by
        cases w2 with
        | nil => exact absurd rfl hne
        | cons a w3 => exact ⟨a, w3, rfl⟩
      have hw2' := hw2
      have hinc : pd_inc (a :: w3) = (a + 1) :: w3 := rfl
      rw [hinc, pp_cc_consinc P1 cs a w3 hw2]
      rw [List.count_cons, List.count_append]
      have e1 : (P1.contour.map (List.cons 0)).count ((a + 1) :: w3) = 0 :=
        pp_cnt_map_cons0_zero _ _ (by simp)
      have := pp_cnt_map_inc (PlaneTree.node cs).contour (a :: w3)
      rw [hinc] at this
      rw [e1, this, ih2 _ hw2']
      simp



private lemma pp_getD_map_lt {α : Type} (f : α → List ℕ) (l : List α) (n : ℕ) (h : n < l.length)
    (d : α) : (l.map f).getD n [] = f (l.getD n d) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]

private theorem pp_nl_main (P : PlaneTree) : ∀ p < P.contour.length, ∀ w ∈ P.vtxs,
    (P.contour.take p).count w =
      pp_nbC (P.childCount w + 1) w (P.contour.getD p [])
        ((P.contour.take p).count (P.contour.getD p [])) := by
  refine pd_plane_ind (fun P => ∀ p < P.contour.length, ∀ w ∈ P.vtxs,
    (P.contour.take p).count w =
      pp_nbC (P.childCount w + 1) w (P.contour.getD p [])
        ((P.contour.take p).count (P.contour.getD p []))) ?_ ?_ P
  · intro p hp w hw
    simp [PlaneTree.contour, contourForest] at hp
    subst hp
    simp [PlaneTree.vtxs, vtxsForest] at hw
    subst hw
    simp [PlaneTree.contour, contourForest, pp_nbC]
  · intro P1 cs ih1 ih2 p hp w hw
    have hC := pp_contour_node_cons P1 cs
    have hlen : (PlaneTree.node (P1 :: cs)).contour.length =
        1 + (P1.contour.length + (PlaneTree.node cs).contour.length) := by
      rw [hC]; simp; omega
    rcases p with _ | q
    · -- the starting corner of the root
      rw [hC]
      rcases (pd_mem_vtxs_cons.mp hw) with h | ⟨w1, hw1, rfl⟩ | ⟨w2, hw2, hne, rfl⟩
      · subst h; simp [pp_nbC]
      · simp [pp_nbC]
      · cases w2 with
        | nil => exact absurd rfl hne
        | cons a w3 => simp [pp_nbC, pd_inc]
    by_cases hq : q < P1.contour.length
    · -- the mark lies in the first child
      have e_take : (PlaneTree.node (P1 :: cs)).contour.take (q + 1) =
          [] :: (P1.contour.take q).map (List.cons 0) := by
        rw [hC, List.take_succ_cons, List.take_append_of_le_length (by simp; omega), List.map_take]
      have e_get : (PlaneTree.node (P1 :: cs)).contour.getD (q + 1) [] =
          0 :: P1.contour.getD q [] := by
        rw [hC, List.getD_cons_succ, List.getD_append _ _ _ _ (by simpa using hq),
          pp_getD_map_lt _ _ _ hq []]
      rw [e_take, e_get]
      have ejv : ((([] : List ℕ) :: (P1.contour.take q).map (List.cons 0)).count
          (0 :: P1.contour.getD q [])) = (P1.contour.take q).count (P1.contour.getD q []) := by
        rw [List.count_cons, pp_cnt_map_cons0]; simp
      rw [ejv]
      have ih1' := ih1 q hq
      rcases (pd_mem_vtxs_cons.mp hw) with h | ⟨w1, hw1, rfl⟩ | ⟨w2, hw2, hne, rfl⟩
      · subst h
        rw [List.count_cons, pp_cnt_map_cons0_zero _ _ (by simp)]
        simp [pp_nbC]
      · rw [pp_cc_cons0 P1 cs w1 hw1, List.count_cons, pp_cnt_map_cons0, ih1' w1 hw1]
        simp [pp_nbC]
      · cases w2 with
        | nil => exact absurd rfl hne
        | cons a w3 =>
          have hinc : pd_inc (a :: w3) = (a + 1) :: w3 := rfl
          rw [hinc, List.count_cons, pp_cnt_map_cons0_zero _ _ (by simp)]
          simp [pp_nbC]
    · -- the mark lies in the remaining tree
      push_neg at hq
      obtain ⟨q', rfl⟩ : ∃ q', q = P1.contour.length + q' := ⟨q - P1.contour.length, by omega⟩
      have hq' : q' < (PlaneTree.node cs).contour.length := by omega
      have e_take : (PlaneTree.node (P1 :: cs)).contour.take (P1.contour.length + q' + 1) =
          [] :: (P1.contour.map (List.cons 0) ++
            ((PlaneTree.node cs).contour.take q').map pd_inc) := by
        rw [hC, show P1.contour.length + q' + 1 = (P1.contour.length + q') + 1 from rfl,
          List.take_succ_cons]
        have : P1.contour.length + q' = (P1.contour.map (List.cons 0)).length + q' := by simp
        rw [this, List.take_append, List.map_take]
        simp
      have e_get : (PlaneTree.node (P1 :: cs)).contour.getD (P1.contour.length + q' + 1) [] =
          pd_inc ((PlaneTree.node cs).contour.getD q' []) := by
        rw [hC, List.getD_cons_succ, List.getD_append_right _ _ _ _ (by simp)]
        simp only [List.length_map, Nat.add_sub_cancel_left]
        rw [pp_getD_map_lt _ _ _ hq' []]
      rw [e_take, e_get]
      have ih2' := ih2 q' hq'
      generalize (PlaneTree.node cs).contour.getD q' [] = v2 at ih2' ⊢
      have hjv : (([] : List ℕ) :: (P1.contour.map (List.cons 0) ++
          ((PlaneTree.node cs).contour.take q').map pd_inc)).count (pd_inc v2) =
          ((PlaneTree.node cs).contour.take q').count v2 + (if v2 = [] then 1 else 0) := by
        rw [List.count_cons, List.count_append, pp_cnt_map_inc,
          pp_cnt_map_cons0_zero _ _ (by intro w'; cases v2 <;> simp [pd_inc])]
        cases v2 with
        | nil => simp [pd_inc]
        | cons b y => simp [pd_inc]
      rw [hjv]
      rcases (pd_mem_vtxs_cons.mp hw) with h | ⟨w1, hw1, rfl⟩ | ⟨w2, hw2, hne, rfl⟩
      · subst h
        have h2 := ih2' [] (pd_pt_root_mem _)
        rw [List.count_cons, List.count_append, pp_cnt_map_cons0_zero _ _ (by simp)]
        have e2 : (((PlaneTree.node cs).contour.take q').map pd_inc).count [] =
            ((PlaneTree.node cs).contour.take q').count [] := by
          have := pp_cnt_map_inc ((PlaneTree.node cs).contour.take q') []
          simpa [pd_inc] using this
        rw [e2, h2]
        cases v2 with
        | nil => simp [pp_nbC, pd_inc] <;> omega
        | cons b y => simp [pp_nbC, pd_inc] <;> omega
      · rw [pp_cc_cons0 P1 cs w1 hw1, List.count_cons, List.count_append, pp_cnt_map_cons0,
          pp_cnt_map_inc_zero, pp_cnt_full P1 w1 hw1]
        cases v2 with
        | nil => simp [pp_nbC, pd_inc]
        | cons b y => simp [pp_nbC, pd_inc]
      · cases w2 with
        | nil => exact absurd rfl hne
        | cons a w3 =>
          have hinc : pd_inc (a :: w3) = (a + 1) :: w3 := rfl
          have h2 := ih2' (a :: w3) hw2
          rw [hinc, pp_cc_consinc P1 cs a w3 hw2, List.count_cons, List.count_append,
            pp_cnt_map_cons0_zero _ _ (by simp)]
          have e2 := pp_cnt_map_inc ((PlaneTree.node cs).contour.take q') (a :: w3)
          rw [hinc] at e2
          rw [e2, h2]
          cases v2 with
          | nil =>
            simp only [pp_nbC, pd_inc]
            simp
          | cons b y =>
            simp only [pp_nbC, pd_inc]
            simp



private lemma pp_sum_corners {M : Type} [AddCommMonoid M] (L : List (List ℕ)) (F : List ℕ → ℕ → M) :
    ∑ p ∈ Finset.range L.length, F (L.getD p []) ((L.take p).count (L.getD p [])) =
      ∑ x ∈ L.toFinset, ∑ j ∈ Finset.range (L.count x), F x j := by
  classical
  induction L using List.reverseRecOn with
  | nil => simp
  | append_singleton L y ih =>
    rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
    have e1 : ∀ p ∈ Finset.range L.length,
        F ((L ++ [y]).getD p []) (((L ++ [y]).take p).count ((L ++ [y]).getD p [])) =
          F (L.getD p []) ((L.take p).count (L.getD p [])) := by
      intro p hp
      have hp' := Finset.mem_range.mp hp
      rw [List.getD_append _ _ _ _ hp', List.take_append_of_le_length hp'.le]
    rw [Finset.sum_congr rfl e1, ih]
    have e2 : (L ++ [y]).getD L.length [] = y := by simp
    have e3 : ((L ++ [y]).take L.length) = L := by simp
    rw [e2, e3]
    have e4 : ∀ x, (L ++ [y]).count x = L.count x + (if x = y then 1 else 0) := by
      intro x
      rw [List.count_append]
      by_cases h : x = y
      · subst h; simp
      · have : [y].count x = 0 := List.count_eq_zero.mpr (by simpa [eq_comm] using h)
        simp [h, this]
    have e5 : ∀ x, ∑ j ∈ Finset.range ((L ++ [y]).count x), F x j =
        ∑ j ∈ Finset.range (L.count x), F x j + (if x = y then F y (L.count y) else 0) := by
      intro x
      rw [e4]
      by_cases h : x = y
      · subst h; simp [Finset.sum_range_succ]
      · simp [h]
    rw [List.toFinset_append]
    have e6 : L.toFinset ∪ [y].toFinset = insert y L.toFinset := by
      ext x; simp [or_comm]
    rw [e6, Finset.sum_congr rfl (fun x _ => e5 x), Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_insert, true_or, if_true]
    by_cases hy : y ∈ L.toFinset
    · rw [Finset.insert_eq_of_mem hy]
    · rw [Finset.sum_insert hy]
      have : L.count y = 0 := List.count_eq_zero.mpr (by simpa using hy)
      simp [this]



private lemma pp_sum_split {t : VType} {k : ℕ} (X : RootedTypedTree t k) (d : ODec t)
    (h : ob_Rel X d) (f : List ℕ → ℂ) :
    ∑ u ∈ X.tree.vtxs.toFinset, f u =
      f [] + ∑ r : Fin d.1, (f [r.val] + ∑ c : Fin (2 * (d.2 r).1 + 1),
        ∑ v ∈ ((d.2 r).2 c).2.tree.vtxs.toFinset, f ([r.val, c.val] ++ v)) := by
  classical
  have hV : X.tree.vtxs.toFinset = insert [] (Finset.univ.biUnion fun r : Fin d.1 =>
      insert [r.val] (Finset.univ.biUnion fun c : Fin (2 * (d.2 r).1 + 1) =>
        (((d.2 r).2 c).2.tree.vtxs.toFinset).image (fun v => [r.val, c.val] ++ v))) := by
    ext u
    simp only [List.mem_toFinset, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image]
    rw [ob_Rel_mem X d h]
    constructor
    · rintro (h1 | ⟨r, h1⟩ | ⟨r, c, v, hv, h1⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨r, Or.inl h1⟩
      · exact Or.inr ⟨r, Or.inr ⟨c, v, hv, h1.symm⟩⟩
    · rintro (h1 | ⟨r, h1 | ⟨c, v, hv, h1⟩⟩)
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨r, h1⟩)
      · exact Or.inr (Or.inr ⟨r, c, v, hv, h1.symm⟩)
  rw [hV, Finset.sum_insert, Finset.sum_biUnion]
  · congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_insert, Finset.sum_biUnion]
    · congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_image]
      intro v _ v' _ hvv
      exact List.append_cancel_left hvv
    · intro c _ c' _ hcc
      rw [Function.onFun, Finset.disjoint_left]
      intro u hu hu'
      simp only [Finset.mem_image] at hu hu'
      obtain ⟨v, _, rfl⟩ := hu
      obtain ⟨v', _, hv'⟩ := hu'
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hv'
      exact hcc (Fin.ext hv'.2.1.symm)
    · intro hmem
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hmem
      obtain ⟨c, v, _, hv⟩ := hmem
      simp at hv
  · intro r _ r' _ hrr
    rw [Function.onFun, Finset.disjoint_left]
    intro u hu hu'
    simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image] at hu hu'
    have key : ∀ (r : Fin d.1) (u : List ℕ), (u = [r.val] ∨ ∃ c : Fin (2 * (d.2 r).1 + 1),
        ∃ v ∈ ((d.2 r).2 c).2.tree.vtxs.toFinset, [r.val, c.val] ++ v = u) → u.head? = some r.val := by
      intro r u hu
      rcases hu with rfl | ⟨c, v, _, rfl⟩ <;> rfl
    have h1 := key r u hu
    have h2 := key r' u hu'
    rw [h1] at h2
    exact hrr (Fin.ext (Option.some_injective _ h2))
  · intro hmem
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_image] at hmem
    obtain ⟨r, h1 | ⟨c, v, _, h1⟩⟩ := hmem <;> simp at h1




/-! ## Pointed weights -/

/-- Parameters of the pointed weights. -/
private structure PtK where
  z1 : ℂ
  z2 : ℂ
  cp : ℕ → ℕ → ℂ
  Mf : VType → ℕ → ℂ
  Mg : ℕ → ℂ

private def PtK.cdf1 (K : PtK) (d : ℕ) : ℂ := K.cp d 0
private def PtK.cdf2 (K : PtK) (d : ℕ) : ℂ := K.cp 0 d

open Classical in
/-- The vertex weight of the pointed tree `(Y, (v, j))`. -/
private def ptW (K : PtK) {τ : VType} {k : ℕ} (Y : RootedTypedTree τ k) (δ : ℕ)
    (ρ : VType → ℕ → ℂ) (v : List ℕ) (j : ℕ) (w : List ℕ) : ℂ :=
  if Y.ty w = VType.lat then
    K.cp (pp_nbC (Y.tree.childCount w + 1) w v j)
      (Y.tree.childCount w + 1 - pp_nbC (Y.tree.childCount w + 1) w v j)
  else if w = v then
    K.z1 ^ (pp_nbC (Y.tree.childCount w + 1) w v j + 1) *
      K.z2 ^ (Y.tree.childCount w + 1 - pp_nbC (Y.tree.childCount w + 1) w v j) *
      K.Mg (Y.tree.degAt w + (if w = [] then δ else 0))
  else
    K.z1 ^ (pp_nbC (Y.tree.childCount w + 1) w v j) *
      K.z2 ^ (Y.tree.childCount w + 1 - pp_nbC (Y.tree.childCount w + 1) w v j) *
      (if w = [] then ρ (Y.ty w) (Y.tree.degAt w + δ) else K.Mf (Y.ty w) (Y.tree.degAt w))

open Classical in
/-- The total weight of all marks `(v, j)` (an input vertex `v` and a corner `j`) of `Y`. -/
private def ptSum (K : PtK) {τ : VType} {k : ℕ} (Y : RootedTypedTree τ k) (δ : ℕ)
    (ρ : VType → ℕ → ℂ) : ℂ :=
  ∑ v ∈ Y.tree.vtxs.toFinset.filter (fun v => Y.ty v = VType.inp),
    ∑ j ∈ Finset.range (Y.tree.childCount v + 1),
      ∏ w ∈ Y.tree.vtxs.toFinset, ptW K Y δ ρ v j w

/-- Complete block weight (all corners with the same label). -/
private def ptBw (z : ℂ) (cdf : ℕ → ℂ) (K : PtK) {τ : VType} (b : OBlk τ) : ℂ :=
  z * cdf (2 * b.1 + 2) * ∏ c : Fin (2 * b.1 + 1), ob_C z cdf K.Mf (b.2 c)

open Classical in
/-- The block containing the mark at the child `c0`, with `m` the weight of the marked child. -/
private def ptBmk (K : PtK) {τ : VType} (b : OBlk τ) (c0 : Fin (2 * b.1 + 1)) (m : ℂ) : ℂ :=
  K.z2 * K.cp (c0.val + 1) (2 * b.1 + 1 - c0.val) *
    ∏ c' : Fin (2 * b.1 + 1),
      (if c' < c0 then ob_C K.z1 K.cdf1 K.Mf (b.2 c')
       else if c' = c0 then m
       else ob_C K.z2 K.cdf2 K.Mf (b.2 c'))

/-- The block containing the mark. -/
private def ptBm (K : PtK) {τ : VType} (b : OBlk τ) : ℂ :=
  ∑ c0 : Fin (2 * b.1 + 1), ptBmk K b c0 (ptSum K (b.2 c0).2 1 K.Mf)

open Classical in
private def ptRhs (K : PtK) (τ : VType) (δ : ℕ) (ρ : VType → ℕ → ℂ) (d : ODec τ) : ℂ :=
  (if τ = VType.inp then ∑ j ∈ Finset.range (d.1 + 1),
      K.z1 * K.z2 * K.Mg (d.1 + δ) *
        ∏ r : Fin d.1, (if r.val < j then ptBw K.z1 K.cdf1 K (d.2 r)
                        else ptBw K.z2 K.cdf2 K (d.2 r))
    else 0) +
  ∑ r0 : Fin d.1, ρ τ (d.1 + δ) * K.z1 *
    ∏ r : Fin d.1, (if r < r0 then ptBw K.z1 K.cdf1 K (d.2 r)
                    else if r = r0 then ptBm K (d.2 r)
                    else ptBw K.z2 K.cdf2 K (d.2 r))


private lemma pp_degAt_root {P : PlaneTree} : P.degAt [] = P.childCount [] := by
  simp [PlaneTree.degAt]

private lemma pp_degAt_ne {P : PlaneTree} {w : List ℕ} (h : w ≠ []) :
    P.degAt w = P.childCount w + 1 := by
  simp [PlaneTree.degAt, h]

private lemma pp_CW (z : ℂ) (cdf : ℕ → ℂ) (Mf : VType → ℕ → ℂ) {σ : VType} {k : ℕ}
    (Z : RootedTypedTree σ k) :
    ∏ w ∈ Z.tree.vtxs.toFinset,
      (if Z.ty w = VType.lat then cdf (Z.tree.childCount w + 1)
       else z ^ (Z.tree.childCount w + 1) * Mf (Z.ty w) (Z.tree.childCount w + 1)) =
      ob_C z cdf Mf (⟨k, Z⟩ : OE σ) := by
  classical
  have hroot : ([] : List ℕ) ∈ Z.tree.vtxs.toFinset := List.mem_toFinset.mpr (ob_pt_root_mem _)
  have hrt : Z.ty [] ≠ VType.lat := by rw [Z.root_ty]; exact Z.root_ext
  obtain ⟨hs1, -, -, -⟩ := ob_deg_sums Z
  -- the exponent of z
  have hsum : (∑ w ∈ Z.tree.vtxs.toFinset, (if Z.ty w = VType.lat then 0 else Z.tree.degAt w)) = k := by
    refine Eq.trans ?_ hs1
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h : Z.ty w = VType.lat <;> simp [h]
  have hsum' : (Z.tree.childCount []) + (∑ w ∈ Z.tree.vtxs.toFinset.erase [],
      (if Z.ty w = VType.lat then 0 else Z.tree.degAt w)) = k := by
    refine Eq.trans ?_ hsum
    rw [← Finset.add_sum_erase _ _ hroot]
    simp [hrt, pp_degAt_root]
  rw [← Finset.mul_prod_erase _ _ hroot]
  have hpt : ∀ w ∈ Z.tree.vtxs.toFinset.erase [],
      (if Z.ty w = VType.lat then cdf (Z.tree.childCount w + 1)
       else z ^ (Z.tree.childCount w + 1) * Mf (Z.ty w) (Z.tree.childCount w + 1)) =
      z ^ (if Z.ty w = VType.lat then 0 else Z.tree.degAt w) * ob_loc cdf Mf Z w := by
    intro w hw
    have hne : w ≠ [] := (Finset.mem_erase.mp hw).1
    unfold ob_loc
    rw [pp_degAt_ne hne]
    by_cases h : Z.ty w = VType.lat <;> simp [h]
  rw [Finset.prod_congr rfl hpt, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  unfold ob_C ob_rest
  simp only [if_neg hrt, pp_degAt_root]
  rw [← Finset.filter_ne']
  have : z ^ (Z.tree.childCount [] + 1) * z ^ (∑ w ∈ Z.tree.vtxs.toFinset.erase [],
      (if Z.ty w = VType.lat then 0 else Z.tree.degAt w)) = z ^ (k + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [Finset.filter_ne'] at *
  calc _ = (z ^ (Z.tree.childCount [] + 1) * z ^ (∑ w ∈ Z.tree.vtxs.toFinset.erase [],
      (if Z.ty w = VType.lat then 0 else Z.tree.degAt w))) * Mf (Z.ty []) (Z.tree.childCount [] + 1) *
        ∏ w ∈ Z.tree.vtxs.toFinset.erase [], ob_loc cdf Mf Z w := by ring
    _ = _ := by rw [this, Z.root_ty]; ring_nf



private lemma pp_prod_lt {M : Type*} [CommMonoid M] (a b : M) (N j : ℕ) (hj : j ≤ N) :
    ∏ r : Fin N, (if r.val < j then a else b) = a ^ j * b ^ (N - j) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => if i < j then a else b) N]
  induction N, hj using Nat.le_induction with
  | base =>
    rw [Finset.prod_congr rfl (fun i hi => if_pos (Finset.mem_range.mp hi))]
    simp
  | succ N hN ih =>
    rw [Finset.prod_range_succ, ih, if_neg (by omega)]
    rw [show N + 1 - j = (N - j) + 1 by omega, pow_succ, mul_assoc]

private lemma pp_prod_mid {M : Type*} [CommMonoid M] (a c b : M) (N r0 : ℕ) (hr : r0 < N) :
    ∏ r : Fin N, (if r.val < r0 then a else if r.val = r0 then c else b) =
      a ^ r0 * c * b ^ (N - 1 - r0) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => if i < r0 then a else if i = r0 then c else b) N]
  induction N, hr using Nat.le_induction with
  | base =>
    rw [Finset.prod_range_succ, Finset.prod_congr rfl (fun i hi => if_pos (Finset.mem_range.mp hi))]
    simp
  | succ N hN ih =>
    rw [Finset.prod_range_succ, ih, if_neg (by omega), if_neg (by omega)]
    rw [show N + 1 - 1 - r0 = (N - 1 - r0) + 1 by omega, pow_succ, mul_assoc (a ^ r0 * c)]

private lemma ptW_comp1 (K : PtK) {τ : VType} {k : ℕ} (Y : RootedTypedTree τ k) (δ : ℕ)
    (ρ : VType → ℕ → ℂ) (v : List ℕ) (j : ℕ) (w : List ℕ) (hne : w ≠ []) (hwv : w ≠ v)
    (hnb : pp_nbC (Y.tree.childCount w + 1) w v j = Y.tree.childCount w + 1) :
    ptW K Y δ ρ v j w = if Y.ty w = VType.lat then K.cdf1 (Y.tree.childCount w + 1)
      else K.z1 ^ (Y.tree.childCount w + 1) * K.Mf (Y.ty w) (Y.tree.childCount w + 1) := by
  unfold ptW
  rw [hnb]
  by_cases hl : Y.ty w = VType.lat
  · simp [hl, PtK.cdf1]
  · simp [hl, hwv, hne, pp_degAt_ne hne]

private lemma ptW_comp2 (K : PtK) {τ : VType} {k : ℕ} (Y : RootedTypedTree τ k) (δ : ℕ)
    (ρ : VType → ℕ → ℂ) (v : List ℕ) (j : ℕ) (w : List ℕ) (hne : w ≠ []) (hwv : w ≠ v)
    (hnb : pp_nbC (Y.tree.childCount w + 1) w v j = 0) :
    ptW K Y δ ρ v j w = if Y.ty w = VType.lat then K.cdf2 (Y.tree.childCount w + 1)
      else K.z2 ^ (Y.tree.childCount w + 1) * K.Mf (Y.ty w) (Y.tree.childCount w + 1) := by
  unfold ptW
  rw [hnb]
  by_cases hl : Y.ty w = VType.lat
  · simp [hl, PtK.cdf2]
  · simp [hl, hwv, hne, pp_degAt_ne hne]



private lemma pp_Rel_ty_r {τ : VType} {k : ℕ} (Y : RootedTypedTree τ k) (d : ODec τ)
    (h : ob_Rel Y d) (r : Fin d.1) : Y.ty [r.val] = VType.lat := by
  have hm : r.val < Y.tree.childCount [] := by rw [h.1]; exact r.2
  exact (ob_root_children Y r.val hm).1

private lemma pp_Rel_mem {τ : VType} {k : ℕ} (Y : RootedTypedTree τ k) (d : ODec τ)
    (h : ob_Rel Y d) (r : Fin d.1) (c : Fin (2 * (d.2 r).1 + 1)) (v : List ℕ)
    (hv : v ∈ ((d.2 r).2 c).2.tree.vtxs) : [r.val, c.val] ++ v ∈ Y.tree.vtxs :=
  (((h.2 r).2 c).1 v).mp hv

private lemma pp_Rel_ty_rcv {τ : VType} {k : ℕ} (Y : RootedTypedTree τ k) (d : ODec τ)
    (h : ob_Rel Y d) (r : Fin d.1) (c : Fin (2 * (d.2 r).1 + 1)) (v : List ℕ)
    (hv : v ∈ ((d.2 r).2 c).2.tree.vtxs) : Y.ty ([r.val, c.val] ++ v) = ((d.2 r).2 c).2.ty v :=
  (((h.2 r).2 c).2 v hv).symm

private lemma pp_child_comp1 (K : PtK) {τ : VType} {k : ℕ} (Y : RootedTypedTree τ k) (d : ODec τ)
    (h : ob_Rel Y d) (δ : ℕ) (ρ : VType → ℕ → ℂ) (v : List ℕ) (j : ℕ)
    (r : Fin d.1) (c : Fin (2 * (d.2 r).1 + 1)) (hwv : ∀ v', [r.val, c.val] ++ v' ≠ v)
    (hl : ∀ v' ∈ ((d.2 r).2 c).2.tree.vtxs,
        pp_nbC (Y.tree.childCount ([r.val, c.val] ++ v') + 1) ([r.val, c.val] ++ v') v j =
          Y.tree.childCount ([r.val, c.val] ++ v') + 1) :
    ∏ v' ∈ ((d.2 r).2 c).2.tree.vtxs.toFinset, ptW K Y δ ρ v j ([r.val, c.val] ++ v') =
      ob_C K.z1 K.cdf1 K.Mf ((d.2 r).2 c) := by
  classical
  rw [← pp_CW K.z1 K.cdf1 K.Mf ((d.2 r).2 c).2]
  refine Finset.prod_congr rfl fun v' hv' => ?_
  have hv'' := List.mem_toFinset.mp hv'
  rw [ptW_comp1 K Y δ ρ v j _ (by simp) (hwv v') (hl v' hv''), pp_Rel_ty_rcv Y d h r c v' hv'',
    ob_Rel_cc Y d h r c v' hv'']

private lemma pp_child_comp2 (K : PtK) {τ : VType} {k : ℕ} (Y : RootedTypedTree τ k) (d : ODec τ)
    (h : ob_Rel Y d) (δ : ℕ) (ρ : VType → ℕ → ℂ) (v : List ℕ) (j : ℕ)
    (r : Fin d.1) (c : Fin (2 * (d.2 r).1 + 1)) (hwv : ∀ v', [r.val, c.val] ++ v' ≠ v)
    (hl : ∀ v' ∈ ((d.2 r).2 c).2.tree.vtxs,
        pp_nbC (Y.tree.childCount ([r.val, c.val] ++ v') + 1) ([r.val, c.val] ++ v') v j = 0) :
    ∏ v' ∈ ((d.2 r).2 c).2.tree.vtxs.toFinset, ptW K Y δ ρ v j ([r.val, c.val] ++ v') =
      ob_C K.z2 K.cdf2 K.Mf ((d.2 r).2 c) := by
  classical
  rw [← pp_CW K.z2 K.cdf2 K.Mf ((d.2 r).2 c).2]
  refine Finset.prod_congr rfl fun v' hv' => ?_
  have hv'' := List.mem_toFinset.mp hv'
  rw [ptW_comp2 K Y δ ρ v j _ (by simp) (hwv v') (hl v' hv''), pp_Rel_ty_rcv Y d h r c v' hv'',
    ob_Rel_cc Y d h r c v' hv'']



private lemma pt_root_prod (K : PtK) {τ : VType} {k : ℕ} (Y : RootedTypedTree τ k) (d : ODec τ)
    (h : ob_Rel Y d) (hτ : τ = VType.inp) (δ : ℕ) (ρ : VType → ℕ → ℂ) (j : ℕ) (hj : j ≤ d.1) :
    ∏ w ∈ Y.tree.vtxs.toFinset, ptW K Y δ ρ [] j w =
      K.z1 * K.z2 * K.Mg (d.1 + δ) * ∏ r : Fin d.1,
        (if r.val < j then ptBw K.z1 K.cdf1 K (d.2 r) else ptBw K.z2 K.cdf2 K (d.2 r)) := by
  classical
  rw [ob_prod_split Y d h]
  have hroot : ptW K Y δ ρ [] j [] = K.z1 ^ (j + 1) * K.z2 ^ (d.1 + 1 - j) * K.Mg (d.1 + δ) := by
    have h0 : Y.tree.childCount [] = d.1 := h.1
    have ht : Y.ty [] = VType.inp := by rw [Y.root_ty, hτ]
    unfold ptW
    simp [ht, h0, pp_nbC, pp_degAt_root]
  have hblock : ∀ r : Fin d.1,
      ptW K Y δ ρ [] j [r.val] * ∏ c : Fin (2 * (d.2 r).1 + 1),
        ∏ v ∈ ((d.2 r).2 c).2.tree.vtxs.toFinset, ptW K Y δ ρ [] j ([r.val, c.val] ++ v) =
      (if r.val < j then K.cdf1 (2 * (d.2 r).1 + 2) * ∏ c, ob_C K.z1 K.cdf1 K.Mf ((d.2 r).2 c)
       else K.cdf2 (2 * (d.2 r).1 + 2) * ∏ c, ob_C K.z2 K.cdf2 K.Mf ((d.2 r).2 c)) := by
    intro r
    have hcc : Y.tree.childCount [r.val] = 2 * (d.2 r).1 + 1 := (h.2 r).1
    have hlat := pp_Rel_ty_r Y d h r
    by_cases hr : r.val < j
    · rw [if_pos hr]
      congr 1
      · unfold ptW
        simp [hlat, hcc, pp_nbC, hr, PtK.cdf1]
      · refine Finset.prod_congr rfl fun c _ => ?_
        refine pp_child_comp1 K Y d h δ ρ [] j r c (by simp) ?_
        intro v' _
        simp [pp_nbC, hr]
    · rw [if_neg hr]
      congr 1
      · unfold ptW
        simp [hlat, hcc, pp_nbC, hr, PtK.cdf2]
      · refine Finset.prod_congr rfl fun c _ => ?_
        refine pp_child_comp2 K Y d h δ ρ [] j r c (by simp) ?_
        intro v' _
        simp [pp_nbC, hr]
  rw [hroot, Finset.prod_congr rfl (fun r _ => hblock r)]
  have hz : K.z1 ^ (j + 1) * K.z2 ^ (d.1 + 1 - j) =
      K.z1 * K.z2 * (K.z1 ^ j * K.z2 ^ (d.1 - j)) := by
    rw [show d.1 + 1 - j = (d.1 - j) + 1 by omega]; ring
  have hprod : ∏ r : Fin d.1, (if r.val < j then ptBw K.z1 K.cdf1 K (d.2 r) else ptBw K.z2 K.cdf2 K (d.2 r)) =
      (K.z1 ^ j * K.z2 ^ (d.1 - j)) * ∏ r : Fin d.1,
        (if r.val < j then K.cdf1 (2 * (d.2 r).1 + 2) * ∏ c, ob_C K.z1 K.cdf1 K.Mf ((d.2 r).2 c)
       else K.cdf2 (2 * (d.2 r).1 + 2) * ∏ c, ob_C K.z2 K.cdf2 K.Mf ((d.2 r).2 c)) := by
    rw [← pp_prod_lt K.z1 K.z2 d.1 j hj, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun r _ => ?_
    by_cases hr : r.val < j <;> simp [hr, ptBw, mul_assoc]
  rw [hprod, hz]
  ring



private lemma pp_nbC_two (t r c : ℕ) (w v : List ℕ) (j : ℕ) :
    pp_nbC t (r :: c :: w) (r :: c :: v) j = pp_nbC t w v j := by
  simp [pp_nbC]

private lemma ptW_marked_child (K : PtK) {τ : VType} {k : ℕ} (Y : RootedTypedTree τ k) (d : ODec τ)
    (h : ob_Rel Y d) (δ : ℕ) (ρ : VType → ℕ → ℂ)
    (r : Fin d.1) (c : Fin (2 * (d.2 r).1 + 1)) (v' : List ℕ) (j : ℕ) (w' : List ℕ)
    (hw' : w' ∈ ((d.2 r).2 c).2.tree.vtxs) :
    ptW K Y δ ρ ([r.val, c.val] ++ v') j ([r.val, c.val] ++ w') =
      ptW K ((d.2 r).2 c).2 1 K.Mf v' j w' := by
  have hcc : Y.tree.childCount (r.val :: c.val :: w') = ((d.2 r).2 c).2.tree.childCount w' := by
    simpa using ob_Rel_cc Y d h r c w' hw'
  have hty : Y.ty (r.val :: c.val :: w') = ((d.2 r).2 c).2.ty w' := by
    simpa using pp_Rel_ty_rcv Y d h r c w' hw'
  unfold ptW
  simp only [List.cons_append, List.nil_append, pp_nbC_two, hcc, hty]
  have hdeg : Y.tree.degAt (r.val :: c.val :: w') =
      ((d.2 r).2 c).2.tree.degAt w' + (if w' = [] then 1 else 0) := by
    rw [pp_degAt_ne (by simp : (r.val :: c.val :: w') ≠ [])]
    by_cases hw0 : w' = []
    · subst hw0; simp [pp_degAt_root, hcc]
    · simp [pp_degAt_ne hw0, hw0, hcc]
  simp only [List.cons.injEq, true_and, hdeg]
  by_cases hl : ((d.2 r).2 c).2.ty w' = VType.lat
  · simp [hl]
  · by_cases hwv : w' = v'
    · subst hwv; simp [hl]
    · by_cases hw0 : w' = []
      · subst hw0; simp [hl, hwv, pp_degAt_root]
      · simp [hl, hwv, hw0, pp_degAt_ne hw0]



private lemma pt_child_prod (K : PtK) {τ : VType} {k : ℕ} (Y : RootedTypedTree τ k) (d : ODec τ)
    (h : ob_Rel Y d) (δ : ℕ) (ρ : VType → ℕ → ℂ) (r0 : Fin d.1)
    (c0 : Fin (2 * (d.2 r0).1 + 1)) (v' : List ℕ) (j : ℕ) :
    ∏ w ∈ Y.tree.vtxs.toFinset, ptW K Y δ ρ ([r0.val, c0.val] ++ v') j w =
      ρ τ (d.1 + δ) * K.z1 * ∏ r : Fin d.1,
        (if r < r0 then ptBw K.z1 K.cdf1 K (d.2 r)
         else if r = r0 then ptBmk K (d.2 r0) c0
           (∏ w' ∈ ((d.2 r0).2 c0).2.tree.vtxs.toFinset, ptW K ((d.2 r0).2 c0).2 1 K.Mf v' j w')
         else ptBw K.z2 K.cdf2 K (d.2 r)) := by
  classical
  rw [ob_prod_split Y d h]
  have hroot : ptW K Y δ ρ ([r0.val, c0.val] ++ v') j [] =
      K.z1 ^ (r0.val + 1) * K.z2 ^ (d.1 - r0.val) * ρ τ (d.1 + δ) := by
    have h0 : Y.tree.childCount [] = d.1 := h.1
    have ht : Y.ty [] = τ := Y.root_ty
    have hnl : τ ≠ VType.lat := by rw [← Y.root_ty]; exact fun e => Y.root_ext (Y.root_ty ▸ e)
    unfold ptW
    simp [ht, h0, pp_nbC, pp_degAt_root, hnl]
  have hblock : ∀ r : Fin d.1,
      ptW K Y δ ρ ([r0.val, c0.val] ++ v') j [r.val] * ∏ c : Fin (2 * (d.2 r).1 + 1),
        ∏ v ∈ ((d.2 r).2 c).2.tree.vtxs.toFinset,
          ptW K Y δ ρ ([r0.val, c0.val] ++ v') j ([r.val, c.val] ++ v) =
      (if r < r0 then K.cdf1 (2 * (d.2 r).1 + 2) * ∏ c, ob_C K.z1 K.cdf1 K.Mf ((d.2 r).2 c)
       else if r = r0 then K.cp (c0.val + 1) (2 * (d.2 r0).1 + 1 - c0.val) *
         ∏ c' : Fin (2 * (d.2 r0).1 + 1),
           (if c' < c0 then ob_C K.z1 K.cdf1 K.Mf ((d.2 r0).2 c')
            else if c' = c0 then
              (∏ w' ∈ ((d.2 r0).2 c0).2.tree.vtxs.toFinset, ptW K ((d.2 r0).2 c0).2 1 K.Mf v' j w')
            else ob_C K.z2 K.cdf2 K.Mf ((d.2 r0).2 c'))
       else K.cdf2 (2 * (d.2 r).1 + 2) * ∏ c, ob_C K.z2 K.cdf2 K.Mf ((d.2 r).2 c)) := by
    intro r
    have hcc : Y.tree.childCount [r.val] = 2 * (d.2 r).1 + 1 := (h.2 r).1
    have hlat := pp_Rel_ty_r Y d h r
    rcases lt_trichotomy r r0 with hlt | heq | hgt
    · -- before the mark
      have hrne : r.val ≠ r0.val := by intro e; exact absurd (Fin.ext e) hlt.ne
      have hrlt : r.val < r0.val := hlt
      rw [if_pos hlt]
      congr 1
      · unfold ptW
        simp [hlat, hcc, pp_nbC, hrne, hrlt, PtK.cdf1]
      · refine Finset.prod_congr rfl fun c _ => ?_
        refine pp_child_comp1 K Y d h δ ρ _ j r c ?_ ?_
        · intro v' e; simp at e; exact hrne e.1
        · intro v'' _; simp [pp_nbC, hrne, hrlt]
    · subst heq
      rw [if_neg (lt_irrefl _), if_pos rfl]
      congr 1
      · unfold ptW
        have hc0 : c0.val < 2 * (d.2 r).1 + 1 := c0.2
        have e1 : 2 * (d.2 r).1 + 1 + 1 - (c0.val + 1) = 2 * (d.2 r).1 + 1 - c0.val := by omega
        simp [hlat, hcc, pp_nbC, e1]
      · refine Finset.prod_congr rfl fun c _ => ?_
        rcases lt_trichotomy c c0 with hc | hc | hc
        · have hcne : c.val ≠ c0.val := by intro e; exact absurd (Fin.ext e) hc.ne
          have hclt : c.val < c0.val := hc
          rw [if_pos hc]
          refine pp_child_comp1 K Y d h δ ρ _ j r c ?_ ?_
          · intro v' e; simp at e; exact hcne e.1
          · intro v'' _; simp [pp_nbC, hcne, hclt]
        · subst hc
          rw [if_neg (lt_irrefl _), if_pos rfl]
          refine Finset.prod_congr rfl fun w' hw' => ?_
          exact ptW_marked_child K Y d h δ ρ r c v' j w' (List.mem_toFinset.mp hw')
        · have hcne : c.val ≠ c0.val := by intro e; exact absurd (Fin.ext e) hc.ne'
          have hclt : ¬ c.val < c0.val := by
            intro hh; exact absurd hh (not_lt.mpr (le_of_lt hc))
          rw [if_neg (not_lt.mpr hc.le), if_neg hc.ne']
          refine pp_child_comp2 K Y d h δ ρ _ j r c ?_ ?_
          · intro v' e; simp at e; exact hcne e.1
          · intro v'' _; simp [pp_nbC, hcne, hclt]
    · -- after the mark
      have hrne : r.val ≠ r0.val := by intro e; exact absurd (Fin.ext e) hgt.ne'
      have hrlt : ¬ r.val < r0.val := by
        intro hh; exact absurd hh (not_lt.mpr (le_of_lt hgt))
      rw [if_neg (not_lt.mpr hgt.le), if_neg hgt.ne']
      congr 1
      · unfold ptW
        simp [hlat, hcc, pp_nbC, hrne, hrlt, PtK.cdf2]
      · refine Finset.prod_congr rfl fun c _ => ?_
        refine pp_child_comp2 K Y d h δ ρ _ j r c ?_ ?_
        · intro v' e; simp at e; exact hrne e.1
        · intro v'' _; simp [pp_nbC, hrne, hrlt]
  rw [hroot, Finset.prod_congr rfl (fun r _ => hblock r)]
  have hzf : ∏ r : Fin d.1, (if r < r0 then K.z1 else K.z2) =
      K.z1 ^ r0.val * K.z2 ^ (d.1 - r0.val) := by
    rw [← pp_prod_lt K.z1 K.z2 d.1 r0.val r0.2.le]
    refine Finset.prod_congr rfl fun r _ => ?_
    rfl
  have hR : ∏ r : Fin d.1,
      (if r < r0 then ptBw K.z1 K.cdf1 K (d.2 r)
         else if r = r0 then ptBmk K (d.2 r0) c0
           (∏ w' ∈ ((d.2 r0).2 c0).2.tree.vtxs.toFinset, ptW K ((d.2 r0).2 c0).2 1 K.Mf v' j w')
         else ptBw K.z2 K.cdf2 K (d.2 r)) =
      (∏ r : Fin d.1, (if r < r0 then K.z1 else K.z2)) *
      ∏ r : Fin d.1,
      (if r < r0 then K.cdf1 (2 * (d.2 r).1 + 2) * ∏ c, ob_C K.z1 K.cdf1 K.Mf ((d.2 r).2 c)
       else if r = r0 then K.cp (c0.val + 1) (2 * (d.2 r0).1 + 1 - c0.val) *
         ∏ c' : Fin (2 * (d.2 r0).1 + 1),
           (if c' < c0 then ob_C K.z1 K.cdf1 K.Mf ((d.2 r0).2 c')
            else if c' = c0 then
              (∏ w' ∈ ((d.2 r0).2 c0).2.tree.vtxs.toFinset, ptW K ((d.2 r0).2 c0).2 1 K.Mf v' j w')
            else ob_C K.z2 K.cdf2 K.Mf ((d.2 r0).2 c'))
       else K.cdf2 (2 * (d.2 r).1 + 2) * ∏ c, ob_C K.z2 K.cdf2 K.Mf ((d.2 r).2 c)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun r _ => ?_
    by_cases h1 : r < r0
    · simp [h1, ptBw]; ring
    · by_cases h2 : r = r0
      · subst h2; simp [h1, ptBmk]; ring
      · simp [h1, h2, ptBw]; ring
  rw [hR, hzf]
  ring



private lemma ptBmk_eq (K : PtK) {τ : VType} (b : OBlk τ) (c0 : Fin (2 * b.1 + 1)) (m : ℂ) :
    ptBmk K b c0 m = (K.z2 * K.cp (c0.val + 1) (2 * b.1 + 1 - c0.val) *
      ∏ c' ∈ Finset.univ.erase c0, (if c' < c0 then ob_C K.z1 K.cdf1 K.Mf (b.2 c')
        else ob_C K.z2 K.cdf2 K.Mf (b.2 c'))) * m := by
  classical
  unfold ptBmk
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c0), if_neg (lt_irrefl _), if_pos rfl]
  have : ∏ c' ∈ Finset.univ.erase c0, (if c' < c0 then ob_C K.z1 K.cdf1 K.Mf (b.2 c')
        else if c' = c0 then m else ob_C K.z2 K.cdf2 K.Mf (b.2 c')) =
      ∏ c' ∈ Finset.univ.erase c0, (if c' < c0 then ob_C K.z1 K.cdf1 K.Mf (b.2 c')
        else ob_C K.z2 K.cdf2 K.Mf (b.2 c')) := by
    refine Finset.prod_congr rfl fun c' hc' => ?_
    have := (Finset.mem_erase.mp hc').1
    simp [this]
  rw [this]; ring

private lemma pp_prodMark {M : Type*} [CommMonoid M] {N : ℕ} (r0 : Fin N) (a b : Fin N → M) (m : M) :
    ∏ r : Fin N, (if r < r0 then a r else if r = r0 then m else b r) =
      (∏ r ∈ Finset.univ.erase r0, (if r < r0 then a r else b r)) * m := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r0), if_neg (lt_irrefl _), if_pos rfl,
    mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun r hr => ?_
  have := (Finset.mem_erase.mp hr).1
  simp [this]


private lemma pt_DL (K : PtK) {τ : VType} {k : ℕ} (Y : RootedTypedTree τ k) (d : ODec τ)
    (h : ob_Rel Y d) (δ : ℕ) (ρ : VType → ℕ → ℂ) : ptSum K Y δ ρ = ptRhs K τ δ ρ d := by
  classical
  unfold ptSum ptRhs
  rw [Finset.sum_filter, pp_sum_split Y d h]
  have h0 : (if Y.ty [] = VType.inp then ∑ j ∈ Finset.range (Y.tree.childCount [] + 1),
        ∏ w ∈ Y.tree.vtxs.toFinset, ptW K Y δ ρ [] j w else 0) =
      (if τ = VType.inp then ∑ j ∈ Finset.range (d.1 + 1),
        K.z1 * K.z2 * K.Mg (d.1 + δ) *
          ∏ r : Fin d.1, (if r.val < j then ptBw K.z1 K.cdf1 K (d.2 r)
                          else ptBw K.z2 K.cdf2 K (d.2 r)) else 0) := by
    rw [Y.root_ty, h.1]
    by_cases hτ : τ = VType.inp
    · simp only [hτ, if_true]
      refine Finset.sum_congr rfl fun j hj => ?_
      exact pt_root_prod K Y d h hτ δ ρ j (by simpa [Nat.lt_succ_iff] using hj)
    · simp [hτ]
  have h1 : ∀ r : Fin d.1, (if Y.ty [r.val] = VType.inp then
        ∑ j ∈ Finset.range (Y.tree.childCount [r.val] + 1),
          ∏ w ∈ Y.tree.vtxs.toFinset, ptW K Y δ ρ [r.val] j w else 0) = 0 := by
    intro r
    rw [pp_Rel_ty_r Y d h r]; simp
  have h2 : ∀ r0 : Fin d.1, ∑ c : Fin (2 * (d.2 r0).1 + 1),
      ∑ v' ∈ ((d.2 r0).2 c).2.tree.vtxs.toFinset,
        (if Y.ty ([r0.val, c.val] ++ v') = VType.inp then
          ∑ j ∈ Finset.range (Y.tree.childCount ([r0.val, c.val] ++ v') + 1),
            ∏ w ∈ Y.tree.vtxs.toFinset, ptW K Y δ ρ ([r0.val, c.val] ++ v') j w else 0) =
      ρ τ (d.1 + δ) * K.z1 * ∏ r : Fin d.1,
        (if r < r0 then ptBw K.z1 K.cdf1 K (d.2 r)
         else if r = r0 then ptBm K (d.2 r)
         else ptBw K.z2 K.cdf2 K (d.2 r)) := by
    intro r0
    set Aff : ℂ := ∏ r ∈ Finset.univ.erase r0,
      (if r < r0 then ptBw K.z1 K.cdf1 K (d.2 r) else ptBw K.z2 K.cdf2 K (d.2 r)) with hAff
    have key : ∀ (c : Fin (2 * (d.2 r0).1 + 1)) (v' : List ℕ),
        v' ∈ ((d.2 r0).2 c).2.tree.vtxs →
        (if Y.ty ([r0.val, c.val] ++ v') = VType.inp then
          ∑ j ∈ Finset.range (Y.tree.childCount ([r0.val, c.val] ++ v') + 1),
            ∏ w ∈ Y.tree.vtxs.toFinset, ptW K Y δ ρ ([r0.val, c.val] ++ v') j w else 0) =
        (ρ τ (d.1 + δ) * K.z1 * Aff *
          (K.z2 * K.cp (c.val + 1) (2 * (d.2 r0).1 + 1 - c.val) *
            ∏ c' ∈ Finset.univ.erase c, (if c' < c then ob_C K.z1 K.cdf1 K.Mf ((d.2 r0).2 c')
              else ob_C K.z2 K.cdf2 K.Mf ((d.2 r0).2 c')))) *
          (if ((d.2 r0).2 c).2.ty v' = VType.inp then
            ∑ j ∈ Finset.range (((d.2 r0).2 c).2.tree.childCount v' + 1),
              ∏ w' ∈ ((d.2 r0).2 c).2.tree.vtxs.toFinset, ptW K ((d.2 r0).2 c).2 1 K.Mf v' j w'
           else 0) := by
      intro c v' hv'
      rw [pp_Rel_ty_rcv Y d h r0 c v' hv', ob_Rel_cc Y d h r0 c v' hv']
      by_cases hty : ((d.2 r0).2 c).2.ty v' = VType.inp
      · simp only [hty, if_true]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pt_child_prod K Y d h δ ρ r0 c v' j, pp_prodMark, ptBmk_eq]
        ring
      · simp [hty]
    have hL : ∑ c : Fin (2 * (d.2 r0).1 + 1),
        ∑ v' ∈ ((d.2 r0).2 c).2.tree.vtxs.toFinset,
          (if Y.ty ([r0.val, c.val] ++ v') = VType.inp then
            ∑ j ∈ Finset.range (Y.tree.childCount ([r0.val, c.val] ++ v') + 1),
              ∏ w ∈ Y.tree.vtxs.toFinset, ptW K Y δ ρ ([r0.val, c.val] ++ v') j w else 0) =
        ρ τ (d.1 + δ) * K.z1 * Aff * ∑ c : Fin (2 * (d.2 r0).1 + 1),
          (K.z2 * K.cp (c.val + 1) (2 * (d.2 r0).1 + 1 - c.val) *
            ∏ c' ∈ Finset.univ.erase c, (if c' < c then ob_C K.z1 K.cdf1 K.Mf ((d.2 r0).2 c')
              else ob_C K.z2 K.cdf2 K.Mf ((d.2 r0).2 c'))) *
          ptSum K ((d.2 r0).2 c).2 1 K.Mf := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_congr rfl (fun v' hv' => key c v' (List.mem_toFinset.mp hv')), ← Finset.mul_sum]
      unfold ptSum
      rw [Finset.sum_filter]
      ring
    have hR : ∏ r : Fin d.1,
        (if r < r0 then ptBw K.z1 K.cdf1 K (d.2 r)
         else if r = r0 then ptBm K (d.2 r)
         else ptBw K.z2 K.cdf2 K (d.2 r)) = Aff * ptBm K (d.2 r0) := by
      have : ∏ r : Fin d.1,
          (if r < r0 then ptBw K.z1 K.cdf1 K (d.2 r)
           else if r = r0 then ptBm K (d.2 r)
           else ptBw K.z2 K.cdf2 K (d.2 r)) =
          ∏ r : Fin d.1,
          (if r < r0 then ptBw K.z1 K.cdf1 K (d.2 r)
           else if r = r0 then ptBm K (d.2 r0)
           else ptBw K.z2 K.cdf2 K (d.2 r)) := by
        refine Finset.prod_congr rfl fun r _ => ?_
        by_cases h1 : r < r0
        · simp [h1]
        · by_cases h2 : r = r0
          · subst h2; simp
          · simp [h1, h2]
      rw [this, pp_prodMark]
    rw [hL, hR]
    unfold ptBm
    simp only [ptBmk_eq]
    ring
  rw [h0]
  congr 1
  refine Finset.sum_congr rfl fun r0 _ => ?_
  rw [h1 r0, zero_add]
  exact h2 r0



private lemma pt_Bw_sum (z : ℂ) (cdf : ℕ → ℂ) (K : PtK) (τ : VType) (hτ : τ ≠ VType.lat)
    (hC : ∀ σ, σ ≠ VType.lat → Summable (fun Y : OE σ => ‖ob_C z cdf K.Mf Y‖))
    (hη : Summable (fun p : ℕ => ‖cdf (2 * p + 2)‖ * ob_κ z cdf K.Mf (ob_f0 τ) ^ (p + 1) *
      ob_κ z cdf K.Mf τ ^ p)) :
    Summable (fun b : OBlk τ => ‖ptBw z cdf K b‖) ∧
    ∑' b : OBlk τ, ‖ptBw z cdf K b‖ = ‖z‖ * ∑' p : ℕ, ‖cdf (2 * p + 2)‖ *
      ob_κ z cdf K.Mf (ob_f0 τ) ^ (p + 1) * ob_κ z cdf K.Mf τ ^ p ∧
    ∑' b : OBlk τ, ptBw z cdf K b = z * ∑' p : ℕ, cdf (2 * p + 2) *
      ob_m z cdf K.Mf (ob_f0 τ) ^ (p + 1) * ob_m z cdf K.Mf τ ^ p := by
  classical
  set κ1 := ob_κ z cdf K.Mf (ob_f0 τ) with hκ1
  set κ2 := ob_κ z cdf K.Mf τ with hκ2
  set m1 := ob_m z cdf K.Mf (ob_f0 τ) with hm1
  set m2 := ob_m z cdf K.Mf τ with hm2
  have hblk : ∀ p, Summable (fun g : (∀ c : Fin (2 * p + 1), OE (ob_ty τ c.val)) =>
      ‖ptBw z cdf K ⟨p, g⟩‖) ∧
      ∑' g : (∀ c : Fin (2 * p + 1), OE (ob_ty τ c.val)), ‖ptBw z cdf K ⟨p, g⟩‖ =
        ‖z‖ * (‖cdf (2 * p + 2)‖ * κ1 ^ (p + 1) * κ2 ^ p) := by
    intro p
    obtain ⟨h1, -, h3⟩ := ob_blk_sums z cdf K.Mf τ hC hτ p
    have e1 : ∀ g : (∀ c : Fin (2 * p + 1), OE (ob_ty τ c.val)), ‖ptBw z cdf K ⟨p, g⟩‖ =
        ‖z‖ * ‖cdf (2 * p + 2)‖ * ‖∏ c, ob_C z cdf K.Mf (g c)‖ := by
      intro g; simp only [ptBw, norm_mul]
    simp_rw [e1]
    refine ⟨h1.mul_left _, ?_⟩
    rw [tsum_mul_left, h3]; ring
  have hwsum : Summable (fun b : OBlk τ => ‖ptBw z cdf K b‖) := by
    rw [summable_sigma_of_nonneg (fun b => norm_nonneg _)]
    refine ⟨fun p => (hblk p).1, ?_⟩
    simp_rw [(hblk _).2]
    exact hη.mul_left _
  have hWabs : ∑' b : OBlk τ, ‖ptBw z cdf K b‖ = ‖z‖ * ∑' p : ℕ, ‖cdf (2 * p + 2)‖ * κ1 ^ (p + 1) * κ2 ^ p := by
    rw [Summable.tsum_sigma' (fun p => (hblk p).1) hwsum]
    simp_rw [(hblk _).2]
    rw [tsum_mul_left]
  have hWeq : ∑' b : OBlk τ, ptBw z cdf K b = z * ∑' p : ℕ, cdf (2 * p + 2) * m1 ^ (p + 1) * m2 ^ p := by
    rw [Summable.tsum_sigma' (fun p => ((hblk p).1.of_norm)) hwsum.of_norm]
    have : ∀ p, ∑' g : (∀ c : Fin (2 * p + 1), OE (ob_ty τ c.val)), ptBw z cdf K ⟨p, g⟩ =
        z * (cdf (2 * p + 2) * m1 ^ (p + 1) * m2 ^ p) := by
      intro p
      obtain ⟨-, h2, -⟩ := ob_blk_sums z cdf K.Mf τ hC hτ p
      have e1 : ∀ g : (∀ c : Fin (2 * p + 1), OE (ob_ty τ c.val)), ptBw z cdf K ⟨p, g⟩ =
          (z * cdf (2 * p + 2)) * ∏ c, ob_C z cdf K.Mf (g c) := fun g => rfl
      simp_rw [e1]
      rw [tsum_mul_left, h2]; ring
    simp_rw [this]
    rw [tsum_mul_left]
  exact ⟨hwsum, hWabs, hWeq⟩



/-- Product weights over a finite family: the marked-position sums. -/
private lemma pp_AL_mark {E : Type} (w1 w2 wm : E → ℂ)
    (h1 : Summable (fun e => ‖w1 e‖)) (h2 : Summable (fun e => ‖w2 e‖))
    (hm : Summable (fun e => ‖wm e‖)) (N : ℕ) (r0 : Fin N) :
    Summable (fun f : Fin N → E => ‖∏ r : Fin N,
        (if r < r0 then w1 (f r) else if r = r0 then wm (f r) else w2 (f r))‖) ∧
    ∑' f : Fin N → E, ∏ r : Fin N,
        (if r < r0 then w1 (f r) else if r = r0 then wm (f r) else w2 (f r)) =
      (∑' e, w1 e) ^ r0.val * (∑' e, wm e) * (∑' e, w2 e) ^ (N - 1 - r0.val) ∧
    ∑' f : Fin N → E, ‖∏ r : Fin N,
        (if r < r0 then w1 (f r) else if r = r0 then wm (f r) else w2 (f r))‖ =
      (∑' e, ‖w1 e‖) ^ r0.val * (∑' e, ‖wm e‖) * (∑' e, ‖w2 e‖) ^ (N - 1 - r0.val) := by
  classical
  have hW : ∀ r : Fin N, Summable (fun e => ‖(if r < r0 then w1 e else if r = r0 then wm e else w2 e)‖) := by
    intro r
    by_cases a : r < r0
    · simpa [a] using h1
    · by_cases b : r = r0
      · simpa [a, b] using hm
      · simpa [a, b] using h2
  obtain ⟨hs, ht⟩ := ob_pi_tsum (R := ℂ) N (fun _ => E)
    (fun r e => if r < r0 then w1 e else if r = r0 then wm e else w2 e) hW
  have hWn : ∀ r : Fin N, Summable (fun e => ‖(‖(if r < r0 then w1 e else if r = r0 then wm e else w2 e)‖ : ℝ)‖) := by
    intro r; simpa only [norm_norm] using hW r
  obtain ⟨-, htn⟩ := ob_pi_tsum (R := ℝ) N (fun _ => E)
    (fun r e => ‖(if r < r0 then w1 e else if r = r0 then wm e else w2 e)‖) hWn
  refine ⟨hs, ?_, ?_⟩
  · rw [ht]
    have : ∀ r : Fin N, ∑' e, (if r < r0 then w1 e else if r = r0 then wm e else w2 e) =
        (if r.val < r0.val then ∑' e, w1 e else if r.val = r0.val then ∑' e, wm e else ∑' e, w2 e) := by
      intro r
      by_cases a : r < r0
      · simp [a, Fin.lt_def.mp a]
      · by_cases b : r = r0
        · subst b; simp
        · have : ¬ r.val < r0.val := fun h => a h
          have : r.val ≠ r0.val := fun h => b (Fin.ext h)
          simp [a, b, *]
    rw [Finset.prod_congr rfl (fun r _ => this r)]
    exact pp_prod_mid _ _ _ N r0.val r0.2
  · have hn : ∀ f : Fin N → E, ‖∏ r : Fin N,
        (if r < r0 then w1 (f r) else if r = r0 then wm (f r) else w2 (f r))‖ =
        ∏ r : Fin N, ‖(if r < r0 then w1 (f r) else if r = r0 then wm (f r) else w2 (f r))‖ :=
      fun f => norm_prod _ _
    simp_rw [hn]
    rw [htn]
    have : ∀ r : Fin N, ∑' e, ‖(if r < r0 then w1 e else if r = r0 then wm e else w2 e)‖ =
        (if r.val < r0.val then ∑' e, ‖w1 e‖ else if r.val = r0.val then ∑' e, ‖wm e‖ else ∑' e, ‖w2 e‖) := by
      intro r
      by_cases a : r < r0
      · simp [a, Fin.lt_def.mp a]
      · by_cases b : r = r0
        · subst b; simp
        · have : ¬ r.val < r0.val := fun h => a h
          have : r.val ≠ r0.val := fun h => b (Fin.ext h)
          simp [a, b, *]
    rw [Finset.prod_congr rfl (fun r _ => this r)]
    exact pp_prod_mid _ _ _ N r0.val r0.2



private lemma pp_fin_sum_pow {M : Type*} [CommSemiring M] (a b : M) (n : ℕ) :
    ∑ r0 : Fin (n + 1), a ^ r0.val * b ^ (n + 1 - 1 - r0.val) =
      ∑ k ∈ Finset.range (n + 1), a ^ k * b ^ (n - k) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => a ^ k * b ^ (n + 1 - 1 - k)) (n + 1)]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2

/-- The Cauchy-product evaluation of the marked geometric series. -/
private lemma pp_geo_mark {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] (a b : 𝕜)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    Summable (fun n : ℕ => ‖∑ k ∈ Finset.range (n + 1), a ^ k * b ^ (n - k)‖) ∧
    ∑' n : ℕ, ∑ k ∈ Finset.range (n + 1), a ^ k * b ^ (n - k) = ((1 - a) * (1 - b))⁻¹ := by
  have h1 : Summable (fun k : ℕ => ‖a ^ k‖) := by
    simp_rw [norm_pow]; exact summable_geometric_of_lt_one (norm_nonneg _) ha
  have h2 : Summable (fun k : ℕ => ‖b ^ k‖) := by
    simp_rw [norm_pow]; exact summable_geometric_of_lt_one (norm_nonneg _) hb
  refine ⟨summable_norm_sum_mul_range_of_summable_norm h1 h2, ?_⟩
  rw [← tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm h1 h2, tsum_geometric_of_norm_lt_one ha,
    tsum_geometric_of_norm_lt_one hb, mul_inv]

private lemma pp_AL_sum {E : Type} (w1 w2 wm : E → ℂ)
    (h1 : Summable (fun e => ‖w1 e‖)) (h2 : Summable (fun e => ‖w2 e‖))
    (hm : Summable (fun e => ‖wm e‖)) (x : ℂ)
    (hx1 : ‖x‖ * ∑' e, ‖w1 e‖ < 1) (hx2 : ‖x‖ * ∑' e, ‖w2 e‖ < 1) :
    Summable (fun d : (Σ N : ℕ, Fin N → E) => ‖x ^ d.1 * ∑ r0 : Fin d.1, ∏ r : Fin d.1,
        (if r < r0 then w1 (d.2 r) else if r = r0 then wm (d.2 r) else w2 (d.2 r))‖) ∧
    ∑' d : (Σ N : ℕ, Fin N → E), x ^ d.1 * ∑ r0 : Fin d.1, ∏ r : Fin d.1,
        (if r < r0 then w1 (d.2 r) else if r = r0 then wm (d.2 r) else w2 (d.2 r)) =
      x * (∑' e, wm e) / ((1 - x * ∑' e, w1 e) * (1 - x * ∑' e, w2 e)) := by
  set n1 := ∑' e, ‖w1 e‖ with hn1
  set n2 := ∑' e, ‖w2 e‖ with hn2
  set nm := ∑' e, ‖wm e‖ with hnm
  set s1 := ∑' e, w1 e with hs1
  set s2 := ∑' e, w2 e with hs2
  set sm := ∑' e, wm e with hsm
  have hn1_0 : 0 ≤ n1 := tsum_nonneg fun _ => norm_nonneg _
  have hn2_0 : 0 ≤ n2 := tsum_nonneg fun _ => norm_nonneg _
  have hnm_0 : 0 ≤ nm := tsum_nonneg fun _ => norm_nonneg _
  have hs1n : ‖s1‖ ≤ n1 := norm_tsum_le_tsum_norm h1
  have hs2n : ‖s2‖ ≤ n2 := norm_tsum_le_tsum_norm h2
  have hsmn : ‖sm‖ ≤ nm := norm_tsum_le_tsum_norm hm
  let G : (Σ N : ℕ, Fin N → E) → ℂ := fun d => x ^ d.1 * ∑ r0 : Fin d.1, ∏ r : Fin d.1,
        (if r < r0 then w1 (d.2 r) else if r = r0 then wm (d.2 r) else w2 (d.2 r))
  have hmark := fun N (r0 : Fin N) => pp_AL_mark w1 w2 wm h1 h2 hm N r0
  have hfib : ∀ N : ℕ, Summable (fun f : Fin N → E => ‖G ⟨N, f⟩‖) := by
    intro N
    have hs : Summable (fun f : Fin N → E => ∑ r0 : Fin N, ‖x ^ N‖ * ‖∏ r : Fin N,
        (if r < r0 then w1 (f r) else if r = r0 then wm (f r) else w2 (f r))‖) :=
      summable_sum fun r0 _ => ((hmark N r0).1).mul_left _
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun f => ?_) hs
    simp only [G]
    rw [norm_mul]
    calc ‖x ^ N‖ * ‖∑ r0 : Fin N, ∏ r : Fin N,
          (if r < r0 then w1 (f r) else if r = r0 then wm (f r) else w2 (f r))‖
        ≤ ‖x ^ N‖ * ∑ r0 : Fin N, ‖∏ r : Fin N,
          (if r < r0 then w1 (f r) else if r = r0 then wm (f r) else w2 (f r))‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
      _ = _ := by rw [Finset.mul_sum]
  have hfibsum : ∀ N : ℕ, ∑' f : Fin N → E, ‖G ⟨N, f⟩‖ ≤
      ‖x‖ ^ N * ∑ r0 : Fin N, n1 ^ r0.val * nm * n2 ^ (N - 1 - r0.val) := by
    intro N
    have hs : Summable (fun f : Fin N → E => ∑ r0 : Fin N, ‖x ^ N‖ * ‖∏ r : Fin N,
        (if r < r0 then w1 (f r) else if r = r0 then wm (f r) else w2 (f r))‖) :=
      summable_sum fun r0 _ => ((hmark N r0).1).mul_left _
    calc ∑' f : Fin N → E, ‖G ⟨N, f⟩‖ ≤ ∑' f : Fin N → E, ∑ r0 : Fin N, ‖x ^ N‖ * ‖∏ r : Fin N,
          (if r < r0 then w1 (f r) else if r = r0 then wm (f r) else w2 (f r))‖ := by
          refine Summable.tsum_le_tsum (fun f => ?_) (hfib N) hs
          simp only [G]
          rw [norm_mul]
          calc ‖x ^ N‖ * ‖∑ r0 : Fin N, ∏ r : Fin N,
                (if r < r0 then w1 (f r) else if r = r0 then wm (f r) else w2 (f r))‖
              ≤ ‖x ^ N‖ * ∑ r0 : Fin N, ‖∏ r : Fin N,
                (if r < r0 then w1 (f r) else if r = r0 then wm (f r) else w2 (f r))‖ :=
                mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
            _ = _ := by rw [Finset.mul_sum]
      _ = ∑ r0 : Fin N, ‖x ^ N‖ * ∑' f : Fin N → E, ‖∏ r : Fin N,
          (if r < r0 then w1 (f r) else if r = r0 then wm (f r) else w2 (f r))‖ := by
          rw [Summable.tsum_finsetSum (fun r0 _ => ((hmark N r0).1).mul_left _)]
          refine Finset.sum_congr rfl fun r0 _ => ?_
          rw [tsum_mul_left]
      _ = ‖x‖ ^ N * ∑ r0 : Fin N, n1 ^ r0.val * nm * n2 ^ (N - 1 - r0.val) := by
          rw [norm_pow, Finset.mul_sum]
          refine Finset.sum_congr rfl fun r0 _ => ?_
          rw [(hmark N r0).2.2]
  have hgeo : Summable (fun N : ℕ => ‖x‖ ^ N * ∑ r0 : Fin N, n1 ^ r0.val * nm * n2 ^ (N - 1 - r0.val)) := by
    rw [← summable_nat_add_iff 1]
    have hX1 : ‖‖x‖ * n1‖ < 1 := by
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hn1_0)]; exact hx1
    have hX2 : ‖‖x‖ * n2‖ < 1 := by
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hn2_0)]; exact hx2
    have hc := ((pp_geo_mark (‖x‖ * n1) (‖x‖ * n2) hX1 hX2).1).of_norm
    refine (hc.mul_left (‖x‖ * nm)).congr fun n => ?_
    have h3 : ∀ r0 : Fin (n + 1), n1 ^ r0.val * nm * n2 ^ (n + 1 - 1 - r0.val) =
        nm * (n1 ^ r0.val * n2 ^ (n + 1 - 1 - r0.val)) := fun r0 => by ring
    simp_rw [h3]
    rw [← Finset.mul_sum, pp_fin_sum_pow n1 n2 n]
    have h4 : ∑ k ∈ Finset.range (n + 1), (‖x‖ * n1) ^ k * (‖x‖ * n2) ^ (n - k) =
        ‖x‖ ^ n * ∑ k ∈ Finset.range (n + 1), n1 ^ k * n2 ^ (n - k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [mul_pow, mul_pow, show ‖x‖ ^ n = ‖x‖ ^ k * ‖x‖ ^ (n - k) by rw [← pow_add]; congr 1; omega]
      ring
    rw [h4]; ring
  have hsumN : Summable (fun N : ℕ => ∑' f : Fin N → E, ‖G ⟨N, f⟩‖) :=
    Summable.of_nonneg_of_le (fun N => tsum_nonneg fun _ => norm_nonneg _) hfibsum hgeo
  have hsig : Summable (fun d : (Σ N : ℕ, Fin N → E) => ‖G d‖) :=
    (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr ⟨hfib, hsumN⟩
  refine ⟨hsig, ?_⟩
  rw [Summable.tsum_sigma' (fun N => (hfib N).of_norm) hsig.of_norm]
  have hN : ∀ N : ℕ, ∑' f : Fin N → E, G ⟨N, f⟩ =
      x ^ N * ∑ r0 : Fin N, s1 ^ r0.val * sm * s2 ^ (N - 1 - r0.val) := by
    intro N
    have h1 : ∑' f : Fin N → E, ∑ r0 : Fin N, ∏ r : Fin N,
        (if r < r0 then w1 (f r) else if r = r0 then wm (f r) else w2 (f r)) =
        ∑ r0 : Fin N, ∑' f : Fin N → E, ∏ r : Fin N,
        (if r < r0 then w1 (f r) else if r = r0 then wm (f r) else w2 (f r)) :=
      Summable.tsum_finsetSum (fun r0 _ => (hmark N r0).1.of_norm)
    simp only [G]
    rw [tsum_mul_left, h1]
    congr 1
    refine Finset.sum_congr rfl fun r0 _ => ?_
    exact (hmark N r0).2.1
  simp_rw [hN]
  have hf : Summable (fun N : ℕ => x ^ N * ∑ r0 : Fin N, s1 ^ r0.val * sm * s2 ^ (N - 1 - r0.val)) := by
    refine Summable.of_norm_bounded hgeo (fun N => ?_)
    rw [norm_mul, norm_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r0 _ => ?_)
    rw [norm_mul, norm_mul, norm_pow, norm_pow]
    gcongr
  have ha : ‖x * s1‖ < 1 := by
    rw [norm_mul]; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hs1n (norm_nonneg _)) hx1
  have hb : ‖x * s2‖ < 1 := by
    rw [norm_mul]; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hs2n (norm_nonneg _)) hx2
  rw [hf.tsum_eq_zero_add]
  have e : ∀ n : ℕ, x ^ (n + 1) * ∑ r0 : Fin (n + 1), s1 ^ r0.val * sm * s2 ^ (n + 1 - 1 - r0.val) =
      (x * sm) * ∑ k ∈ Finset.range (n + 1), (x * s1) ^ k * (x * s2) ^ (n - k) := by
    intro n
    have h3 : ∀ r0 : Fin (n + 1), s1 ^ r0.val * sm * s2 ^ (n + 1 - 1 - r0.val) =
        sm * (s1 ^ r0.val * s2 ^ (n + 1 - 1 - r0.val)) := fun r0 => by ring
    simp_rw [h3]
    rw [← Finset.mul_sum, pp_fin_sum_pow s1 s2 n]
    have h4 : ∑ k ∈ Finset.range (n + 1), (x * s1) ^ k * (x * s2) ^ (n - k) =
        x ^ n * ∑ k ∈ Finset.range (n + 1), s1 ^ k * s2 ^ (n - k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [mul_pow, mul_pow, show x ^ n = x ^ k * x ^ (n - k) by rw [← pow_add]; congr 1; omega]
      ring
    rw [h4]; ring
  simp only [e, Fin.sum_univ_zero, mul_zero, pow_zero, zero_add]
  rw [tsum_mul_left, (pp_geo_mark _ _ ha hb).2]
  field_simp



private lemma pp_AL_rootfib {E : Type} (w1 w2 : E → ℂ)
    (h1 : Summable (fun e => ‖w1 e‖)) (h2 : Summable (fun e => ‖w2 e‖)) (N j : ℕ) (hj : j ≤ N) :
    Summable (fun f : Fin N → E => ‖∏ r : Fin N, (if r.val < j then w1 (f r) else w2 (f r))‖) ∧
    ∑' f : Fin N → E, ∏ r : Fin N, (if r.val < j then w1 (f r) else w2 (f r)) =
      (∑' e, w1 e) ^ j * (∑' e, w2 e) ^ (N - j) ∧
    ∑' f : Fin N → E, ‖∏ r : Fin N, (if r.val < j then w1 (f r) else w2 (f r))‖ =
      (∑' e, ‖w1 e‖) ^ j * (∑' e, ‖w2 e‖) ^ (N - j) := by
  have hW : ∀ r : Fin N, Summable (fun e => ‖(if r.val < j then w1 e else w2 e)‖) := by
    intro r
    by_cases a : r.val < j
    · simpa [a] using h1
    · simpa [a] using h2
  obtain ⟨hs, ht⟩ := ob_pi_tsum (R := ℂ) N (fun _ => E)
    (fun r e => if r.val < j then w1 e else w2 e) hW
  have hWn : ∀ r : Fin N, Summable (fun e => ‖(‖(if r.val < j then w1 e else w2 e)‖ : ℝ)‖) := by
    intro r; simpa only [norm_norm] using hW r
  obtain ⟨-, htn⟩ := ob_pi_tsum (R := ℝ) N (fun _ => E)
    (fun r e => ‖(if r.val < j then w1 e else w2 e)‖) hWn
  refine ⟨hs, ?_, ?_⟩
  · rw [ht]
    have : ∀ r : Fin N, ∑' e, (if r.val < j then w1 e else w2 e) =
        (if r.val < j then ∑' e, w1 e else ∑' e, w2 e) := by
      intro r
      by_cases a : r.val < j <;> simp [a]
    rw [Finset.prod_congr rfl (fun r _ => this r)]
    exact pp_prod_lt _ _ N j hj
  · have hn : ∀ f : Fin N → E, ‖∏ r : Fin N, (if r.val < j then w1 (f r) else w2 (f r))‖ =
        ∏ r : Fin N, ‖(if r.val < j then w1 (f r) else w2 (f r))‖ := fun f => norm_prod _ _
    simp_rw [hn]
    rw [htn]
    have : ∀ r : Fin N, ∑' e, ‖(if r.val < j then w1 e else w2 e)‖ =
        (if r.val < j then ∑' e, ‖w1 e‖ else ∑' e, ‖w2 e‖) := by
      intro r
      by_cases a : r.val < j <;> simp [a]
    rw [Finset.prod_congr rfl (fun r _ => this r)]
    exact pp_prod_lt _ _ N j hj

private lemma pp_AL_root {E : Type} (w1 w2 : E → ℂ)
    (h1 : Summable (fun e => ‖w1 e‖)) (h2 : Summable (fun e => ‖w2 e‖)) (x : ℂ)
    (hx1 : ‖x‖ * ∑' e, ‖w1 e‖ < 1) (hx2 : ‖x‖ * ∑' e, ‖w2 e‖ < 1) :
    Summable (fun d : (Σ N : ℕ, Fin N → E) => ‖x ^ d.1 * ∑ j ∈ Finset.range (d.1 + 1),
        ∏ r : Fin d.1, (if r.val < j then w1 (d.2 r) else w2 (d.2 r))‖) ∧
    ∑' d : (Σ N : ℕ, Fin N → E), x ^ d.1 * ∑ j ∈ Finset.range (d.1 + 1),
        ∏ r : Fin d.1, (if r.val < j then w1 (d.2 r) else w2 (d.2 r)) =
      ((1 - x * ∑' e, w1 e) * (1 - x * ∑' e, w2 e))⁻¹ := by
  set n1 := ∑' e, ‖w1 e‖ with hn1
  set n2 := ∑' e, ‖w2 e‖ with hn2
  set s1 := ∑' e, w1 e with hs1
  set s2 := ∑' e, w2 e with hs2
  have hn1_0 : 0 ≤ n1 := tsum_nonneg fun _ => norm_nonneg _
  have hn2_0 : 0 ≤ n2 := tsum_nonneg fun _ => norm_nonneg _
  have hs1n : ‖s1‖ ≤ n1 := norm_tsum_le_tsum_norm h1
  have hs2n : ‖s2‖ ≤ n2 := norm_tsum_le_tsum_norm h2
  let G : (Σ N : ℕ, Fin N → E) → ℂ := fun d => x ^ d.1 * ∑ j ∈ Finset.range (d.1 + 1),
        ∏ r : Fin d.1, (if r.val < j then w1 (d.2 r) else w2 (d.2 r))
  have hfibj := fun N (j : ℕ) (hj : j ∈ Finset.range (N + 1)) =>
    pp_AL_rootfib w1 w2 h1 h2 N j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  have hfib : ∀ N : ℕ, Summable (fun f : Fin N → E => ‖G ⟨N, f⟩‖) := by
    intro N
    have hs : Summable (fun f : Fin N → E => ∑ j ∈ Finset.range (N + 1), ‖x ^ N‖ * ‖∏ r : Fin N,
        (if r.val < j then w1 (f r) else w2 (f r))‖) :=
      summable_sum fun j hj => ((hfibj N j hj).1).mul_left _
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun f => ?_) hs
    simp only [G]
    rw [norm_mul]
    calc ‖x ^ N‖ * ‖∑ j ∈ Finset.range (N + 1), ∏ r : Fin N,
          (if r.val < j then w1 (f r) else w2 (f r))‖
        ≤ ‖x ^ N‖ * ∑ j ∈ Finset.range (N + 1), ‖∏ r : Fin N,
          (if r.val < j then w1 (f r) else w2 (f r))‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
      _ = _ := by rw [Finset.mul_sum]
  have hfibsum : ∀ N : ℕ, ∑' f : Fin N → E, ‖G ⟨N, f⟩‖ ≤
      ‖x‖ ^ N * ∑ j ∈ Finset.range (N + 1), n1 ^ j * n2 ^ (N - j) := by
    intro N
    have hs : Summable (fun f : Fin N → E => ∑ j ∈ Finset.range (N + 1), ‖x ^ N‖ * ‖∏ r : Fin N,
        (if r.val < j then w1 (f r) else w2 (f r))‖) :=
      summable_sum fun j hj => ((hfibj N j hj).1).mul_left _
    calc ∑' f : Fin N → E, ‖G ⟨N, f⟩‖ ≤ ∑' f : Fin N → E, ∑ j ∈ Finset.range (N + 1), ‖x ^ N‖ * ‖∏ r : Fin N,
          (if r.val < j then w1 (f r) else w2 (f r))‖ := by
          refine Summable.tsum_le_tsum (fun f => ?_) (hfib N) hs
          simp only [G]
          rw [norm_mul]
          calc ‖x ^ N‖ * ‖∑ j ∈ Finset.range (N + 1), ∏ r : Fin N,
                (if r.val < j then w1 (f r) else w2 (f r))‖
              ≤ ‖x ^ N‖ * ∑ j ∈ Finset.range (N + 1), ‖∏ r : Fin N,
                (if r.val < j then w1 (f r) else w2 (f r))‖ :=
                mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
            _ = _ := by rw [Finset.mul_sum]
      _ = ∑ j ∈ Finset.range (N + 1), ‖x ^ N‖ * ∑' f : Fin N → E, ‖∏ r : Fin N,
          (if r.val < j then w1 (f r) else w2 (f r))‖ := by
          rw [Summable.tsum_finsetSum (fun j hj => ((hfibj N j hj).1).mul_left _)]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [tsum_mul_left]
      _ = ‖x‖ ^ N * ∑ j ∈ Finset.range (N + 1), n1 ^ j * n2 ^ (N - j) := by
          rw [norm_pow, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [(hfibj N j hj).2.2]
  have hgeo : Summable (fun N : ℕ => ‖x‖ ^ N * ∑ j ∈ Finset.range (N + 1), n1 ^ j * n2 ^ (N - j)) := by
    have hX1 : ‖‖x‖ * n1‖ < 1 := by
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hn1_0)]; exact hx1
    have hX2 : ‖‖x‖ * n2‖ < 1 := by
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hn2_0)]; exact hx2
    have hc := ((pp_geo_mark (‖x‖ * n1) (‖x‖ * n2) hX1 hX2).1).of_norm
    refine hc.congr fun N => ?_
    have h4 : ∑ k ∈ Finset.range (N + 1), (‖x‖ * n1) ^ k * (‖x‖ * n2) ^ (N - k) =
        ‖x‖ ^ N * ∑ k ∈ Finset.range (N + 1), n1 ^ k * n2 ^ (N - k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [mul_pow, mul_pow, show ‖x‖ ^ N = ‖x‖ ^ k * ‖x‖ ^ (N - k) by rw [← pow_add]; congr 1; omega]
      ring
    exact h4
  have hsumN : Summable (fun N : ℕ => ∑' f : Fin N → E, ‖G ⟨N, f⟩‖) :=
    Summable.of_nonneg_of_le (fun N => tsum_nonneg fun _ => norm_nonneg _) hfibsum hgeo
  have hsig : Summable (fun d : (Σ N : ℕ, Fin N → E) => ‖G d‖) :=
    (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr ⟨hfib, hsumN⟩
  refine ⟨hsig, ?_⟩
  rw [Summable.tsum_sigma' (fun N => (hfib N).of_norm) hsig.of_norm]
  have hN : ∀ N : ℕ, ∑' f : Fin N → E, G ⟨N, f⟩ =
      x ^ N * ∑ j ∈ Finset.range (N + 1), s1 ^ j * s2 ^ (N - j) := by
    intro N
    have h1' : ∑' f : Fin N → E, ∑ j ∈ Finset.range (N + 1), ∏ r : Fin N,
        (if r.val < j then w1 (f r) else w2 (f r)) =
        ∑ j ∈ Finset.range (N + 1), ∑' f : Fin N → E, ∏ r : Fin N,
        (if r.val < j then w1 (f r) else w2 (f r)) :=
      Summable.tsum_finsetSum (fun j hj => ((hfibj N j hj).1).of_norm)
    simp only [G]
    rw [tsum_mul_left, h1']
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    exact (hfibj N j hj).2.1
  simp_rw [hN]
  have ha : ‖x * s1‖ < 1 := by
    rw [norm_mul]; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hs1n (norm_nonneg _)) hx1
  have hb : ‖x * s2‖ < 1 := by
    rw [norm_mul]; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hs2n (norm_nonneg _)) hx2
  have e : ∀ N : ℕ, x ^ N * ∑ j ∈ Finset.range (N + 1), s1 ^ j * s2 ^ (N - j) =
      ∑ k ∈ Finset.range (N + 1), (x * s1) ^ k * (x * s2) ^ (N - k) := by
    intro N
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [mul_pow, mul_pow, show x ^ N = x ^ k * x ^ (N - k) by rw [← pow_add]; congr 1; omega]
    ring
  simp_rw [e]
  exact (pp_geo_mark _ _ ha hb).2



private lemma pt_tsum (K : PtK) (τ : VType) (hτ : τ ≠ VType.lat) (δ : ℕ) (ρ : VType → ℕ → ℂ)
    {ι : Type} [Fintype ι] (c κ : ι → ℂ) (hρ : ∀ d, ρ τ d = ∑ i, c i * κ i ^ d)
    {ι' : Type} [Fintype ι'] (c' κ' : ι' → ℂ) (hMg : ∀ d, K.Mg d = ∑ i, c' i * κ' i ^ d)
    (h1 : Summable (fun b : OBlk τ => ‖ptBw K.z1 K.cdf1 K b‖))
    (h2 : Summable (fun b : OBlk τ => ‖ptBw K.z2 K.cdf2 K b‖))
    (hm : Summable (fun b : OBlk τ => ‖ptBm K b‖))
    (hs1 : ∀ i, ‖κ i‖ * ∑' b : OBlk τ, ‖ptBw K.z1 K.cdf1 K b‖ < 1)
    (hs2 : ∀ i, ‖κ i‖ * ∑' b : OBlk τ, ‖ptBw K.z2 K.cdf2 K b‖ < 1)
    (hs1' : ∀ i, ‖κ' i‖ * ∑' b : OBlk τ, ‖ptBw K.z1 K.cdf1 K b‖ < 1)
    (hs2' : ∀ i, ‖κ' i‖ * ∑' b : OBlk τ, ‖ptBw K.z2 K.cdf2 K b‖ < 1) :
    ∑' Y : OE τ, ptSum K Y.2 δ ρ =
      (if τ = VType.inp then K.z1 * K.z2 * ∑ i, c' i * κ' i ^ δ *
          ((1 - κ' i * ∑' b : OBlk τ, ptBw K.z1 K.cdf1 K b) *
            (1 - κ' i * ∑' b : OBlk τ, ptBw K.z2 K.cdf2 K b))⁻¹ else 0) +
      K.z1 * ∑ i, c i * κ i ^ δ * (κ i * (∑' b : OBlk τ, ptBm K b) /
        ((1 - κ i * ∑' b : OBlk τ, ptBw K.z1 K.cdf1 K b) *
          (1 - κ i * ∑' b : OBlk τ, ptBw K.z2 K.cdf2 K b))) := by
  classical
  set e := ob_decEquiv hτ with he
  have hrel := ob_decEquiv_rel hτ
  have hY : ∀ Y : OE τ, ptSum K Y.2 δ ρ = ptRhs K τ δ ρ (e Y) := fun Y => pt_DL K Y.2 (e Y) (hrel Y) δ ρ
  simp_rw [hY]
  rw [e.tsum_eq (fun d => ptRhs K τ δ ρ d)]
  -- the two families
  set w1 := fun b : OBlk τ => ptBw K.z1 K.cdf1 K b with hw1
  set w2 := fun b : OBlk τ => ptBw K.z2 K.cdf2 K b with hw2
  set wm := fun b : OBlk τ => ptBm K b with hwm
  let GM : ι → ODec τ → ℂ := fun i d => κ i ^ d.1 * ∑ r0 : Fin d.1, ∏ r : Fin d.1,
    (if r < r0 then w1 (d.2 r) else if r = r0 then wm (d.2 r) else w2 (d.2 r))
  let GR : ι' → ODec τ → ℂ := fun i d => κ' i ^ d.1 * ∑ j ∈ Finset.range (d.1 + 1),
    ∏ r : Fin d.1, (if r.val < j then w1 (d.2 r) else w2 (d.2 r))
  have hGM : ∀ i, Summable (GM i) ∧ ∑' d, GM i d = κ i * (∑' b, wm b) /
      ((1 - κ i * ∑' b, w1 b) * (1 - κ i * ∑' b, w2 b)) := by
    intro i
    obtain ⟨a, b⟩ := pp_AL_sum w1 w2 wm h1 h2 hm (κ i) (hs1 i) (hs2 i)
    exact ⟨a.of_norm, b⟩
  have hGR : ∀ i, Summable (GR i) ∧ ∑' d, GR i d = ((1 - κ' i * ∑' b, w1 b) * (1 - κ' i * ∑' b, w2 b))⁻¹ := by
    intro i
    obtain ⟨a, b⟩ := pp_AL_root w1 w2 h1 h2 (κ' i) (hs1' i) (hs2' i)
    exact ⟨a.of_norm, b⟩
  have hform1 : ∀ d : ODec τ,
      (if τ = VType.inp then ∑ j ∈ Finset.range (d.1 + 1), K.z1 * K.z2 * K.Mg (d.1 + δ) *
          ∏ r : Fin d.1, (if r.val < j then w1 (d.2 r) else w2 (d.2 r)) else 0) =
      (if τ = VType.inp then K.z1 * K.z2 * ∑ i, c' i * κ' i ^ δ * GR i d else 0) := by
    intro d
    by_cases hτi : τ = VType.inp
    · simp only [hτi, if_true]
      have e1 : ∑ j ∈ Finset.range (d.1 + 1), K.z1 * K.z2 * K.Mg (d.1 + δ) *
          ∏ r : Fin d.1, (if r.val < j then w1 (d.2 r) else w2 (d.2 r)) =
          K.z1 * K.z2 * (K.Mg (d.1 + δ) * ∑ j ∈ Finset.range (d.1 + 1),
            ∏ r : Fin d.1, (if r.val < j then w1 (d.2 r) else w2 (d.2 r))) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e1, hMg, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [GR]
      rw [pow_add]; ring
    · simp [hτi]
  have hform2 : ∀ d : ODec τ,
      ∑ r0 : Fin d.1, ρ τ (d.1 + δ) * K.z1 * ∏ r : Fin d.1,
        (if r < r0 then w1 (d.2 r) else if r = r0 then wm (d.2 r) else w2 (d.2 r)) =
      K.z1 * ∑ i, c i * κ i ^ δ * GM i d := by
    intro d
    rw [hρ, Finset.mul_sum]
    simp only [GM, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun r0 _ => ?_
    rw [pow_add]; ring
  have hform : ∀ d : ODec τ, ptRhs K τ δ ρ d =
      (if τ = VType.inp then K.z1 * K.z2 * ∑ i, c' i * κ' i ^ δ * GR i d else 0) +
      K.z1 * ∑ i, c i * κ i ^ δ * GM i d := by
    intro d
    exact congrArg₂ (· + ·) (hform1 d) (hform2 d)
  simp_rw [hform]
  have hA : Summable (fun d : ODec τ => (if τ = VType.inp then K.z1 * K.z2 * ∑ i, c' i * κ' i ^ δ * GR i d else 0)) := by
    by_cases hτi : τ = VType.inp
    · simp only [hτi, if_true]
      exact (summable_sum (fun i _ => ((hGR i).1.mul_left (c' i * κ' i ^ δ)))).mul_left _
    · simp only [hτi, if_false]; exact summable_zero
  have hB : Summable (fun d : ODec τ => K.z1 * ∑ i, c i * κ i ^ δ * GM i d) :=
    (summable_sum (fun i _ => ((hGM i).1.mul_left (c i * κ i ^ δ)))).mul_left _
  rw [hA.tsum_add hB, tsum_mul_left]
  congr 1
  · by_cases hτi : τ = VType.inp
    · simp only [hτi, if_true]
      rw [tsum_mul_left, Summable.tsum_finsetSum (fun i _ => ((hGR i).1.mul_left (c' i * κ' i ^ δ)))]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [tsum_mul_left, (hGR i).2]
    · simp [hτi]
  · congr 1
    rw [Summable.tsum_finsetSum (fun i _ => ((hGM i).1.mul_left (c i * κ i ^ δ)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tsum_mul_left, (hGM i).2]



private lemma pp_exists_occ {α : Type} [BEq α] [LawfulBEq α] (C : List α) (v : α) (j : ℕ)
    (hj : j < C.count v) (d : α) :
    ∃ p, p < C.length ∧ C.getD p d = v ∧ (C.take p).count v = j := by
  induction C using List.reverseRecOn with
  | nil => simp at hj
  | append_singleton L y ih =>
    rw [List.count_append] at hj
    by_cases hjL : j < L.count v
    · obtain ⟨p, hp, h1, h2⟩ := ih hjL
      refine ⟨p, by simp; omega, ?_, ?_⟩
      · rw [List.getD_append _ _ _ _ hp]; exact h1
      · rw [List.take_append_of_le_length hp.le]; exact h2
    · have hy : y = v ∧ j = L.count v := by
        by_cases e : y = v
        · subst e
          have : [y].count y = 1 := by simp
          constructor
          · rfl
          · omega
        · have : [y].count v = 0 := List.count_eq_zero.mpr (by simpa [eq_comm] using e)
          omega
      refine ⟨L.length, by simp, ?_, ?_⟩
      · simp [hy.1]
      · simp [hy.2]

private lemma pp_nbC_le {τ : VType} {k : ℕ} (Y : RootedTypedTree τ k) (v : List ℕ)
    (hv : v ∈ Y.tree.vtxs) (j : ℕ) (hj : j ≤ Y.tree.childCount v) (w : List ℕ)
    (hw : w ∈ Y.tree.vtxs) :
    pp_nbC (Y.tree.childCount w + 1) w v j ≤ Y.tree.childCount w + 1 := by
  classical
  have hjv : j < Y.tree.contour.count v := by rw [pp_cnt_full Y.tree v hv]; omega
  obtain ⟨p, hp, hpv, hpj⟩ := pp_exists_occ Y.tree.contour v j hjv []
  have h := pp_nl_main Y.tree p hp w hw
  rw [hpv, hpj] at h
  rw [← h, ← pp_cnt_full Y.tree w hw]
  exact (List.take_sublist _ _).count_le _



private lemma pp_sum_cc {τ : VType} {k : ℕ} (Y : RootedTypedTree τ k) :
    ∑ v ∈ Y.tree.vtxs.toFinset, (Y.tree.childCount v + 1) = 2 * k + 1 := by
  classical
  have h1 := ob_sum_childCount Y.tree (fun _ => True)
  simp only [Finset.filter_true_of_mem (fun _ _ => trivial), Finset.filter_true] at h1
  have hroot : ([] : List ℕ) ∈ Y.tree.vtxs.toFinset := List.mem_toFinset.mpr (ob_pt_root_mem _)
  have hE : (Y.tree.vtxs.toFinset.filter (fun v => v ≠ [])).card = k := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem hroot, ob_card_vtxs]; rfl
  rw [Finset.sum_add_distrib, h1, hE, Finset.sum_const, ob_card_vtxs]
  simp; omega

open Classical in
private lemma pt_vertex_bound (K : PtK) {τ : VType} {k : ℕ} (Y : RootedTypedTree τ k) (δ : ℕ)
    (ρ : VType → ℕ → ℂ)
    (z0 R1 γ C CG Cρ : ℝ) (hz0 : 0 ≤ z0) (hR1 : 1 ≤ R1) (hγ : 1 ≤ γ) (hC : 1 ≤ C)
    (hCG : 1 ≤ CG) (hCρ : 1 ≤ Cρ)
    (hz1 : ‖K.z1‖ ≤ z0) (hz2 : ‖K.z2‖ ≤ z0)
    (hcp : ∀ n1 n2, 1 ≤ n1 + n2 → ‖K.cp n1 n2‖ ≤ R1 ^ (n1 + n2))
    (hMf : ∀ σ d, σ ≠ VType.lat → ‖K.Mf σ d‖ ≤ γ * C ^ d)
    (hMg : ∀ d, ‖K.Mg d‖ ≤ CG * (γ * C ^ d))
    (hρ : ∀ d, ‖ρ τ d‖ ≤ Cρ * (γ * C ^ d))
    (v : List ℕ) (hv : v ∈ Y.tree.vtxs) (hvt : Y.ty v ≠ VType.lat) (j : ℕ)
    (hj : j ≤ Y.tree.childCount v)
    (w : List ℕ) (hw : w ∈ Y.tree.vtxs) :
    ‖ptW K Y δ ρ v j w‖ ≤
      (if Y.ty w = VType.lat then R1 ^ (Y.tree.childCount w + 1) else 1) *
      (if Y.ty w = VType.lat then 1 else z0 ^ (Y.tree.childCount w + 1 + (if w = v then 1 else 0))) *
      (if Y.ty w = VType.lat then 1 else γ) *
      (if Y.ty w = VType.lat then 1 else C ^ (Y.tree.degAt w + (if w = [] then δ else 0))) *
      (if w = v then CG else 1) * (if w = [] then (if [] = v then 1 else Cρ) else 1) := by
  have hnb := pp_nbC_le Y v hv j hj w hw
  have hτ : τ ≠ VType.lat := by rw [← Y.root_ty]; exact fun e => Y.root_ext (Y.root_ty ▸ e)
  have hz : ∀ a b : ℕ, ‖K.z1 ^ a * K.z2 ^ b‖ ≤ z0 ^ (a + b) := by
    intro a b
    rw [norm_mul, norm_pow, norm_pow, pow_add]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz1 a) (pow_le_pow_left₀ (norm_nonneg _) hz2 b)
      (by positivity) (by positivity)
  set t := Y.tree.childCount w + 1 with ht
  set nb := pp_nbC t w v j with hnb'
  have hγ0 : 0 ≤ γ := by linarith
  have hC0 : 0 < C := by linarith
  have hz0' : 0 ≤ z0 := hz0
  unfold ptW
  by_cases hl : Y.ty w = VType.lat
  · have hwv : w ≠ v := fun e => hvt (e ▸ hl)
    have hw0 : w ≠ [] := by
      rintro rfl; exact hτ (by rw [← Y.root_ty]; exact hl)
    simp only [hl, if_true, hwv, hw0, if_false, one_mul, mul_one]
    refine (hcp _ _ (by omega)).trans ?_
    rw [show nb + (t - nb) = t by omega]
  · by_cases hwv : w = v
    · subst hwv
      simp only [hl, if_false, if_true, one_mul]
      have hroot : (if w = [] then (if ([] : List ℕ) = w then (1 : ℝ) else Cρ) else 1) = 1 := by
        by_cases h0 : w = [] <;> simp [h0, eq_comm]
      rw [hroot, mul_one]
      rw [norm_mul]
      calc ‖K.z1 ^ (nb + 1) * K.z2 ^ (t - nb)‖ * ‖K.Mg (Y.tree.degAt w + if w = [] then δ else 0)‖
          ≤ z0 ^ (t + 1) * (CG * (γ * C ^ (Y.tree.degAt w + if w = [] then δ else 0))) := by
            refine mul_le_mul ?_ (hMg _) (norm_nonneg _) (by positivity)
            refine (hz _ _).trans ?_
            rw [show nb + 1 + (t - nb) = t + 1 by omega]
        _ = _ := by ring
    · simp only [hl, if_false, hwv]
      by_cases h0 : w = []
      · subst h0
        simp only [if_true]
        have : ([] : List ℕ) ≠ v := fun e => hwv e
        simp only [this, if_false, one_mul]
        rw [norm_mul]
        calc ‖K.z1 ^ nb * K.z2 ^ (t - nb)‖ * ‖ρ (Y.ty []) (Y.tree.degAt [] + δ)‖
            ≤ z0 ^ t * (Cρ * (γ * C ^ (Y.tree.degAt [] + δ))) := by
              refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
              · refine (hz _ _).trans ?_
                rw [show nb + (t - nb) = t by omega]
              · rw [Y.root_ty]; exact hρ _
          _ = _ := by ring
      · simp only [h0, if_false, one_mul, mul_one]
        rw [norm_mul]
        calc ‖K.z1 ^ nb * K.z2 ^ (t - nb)‖ * ‖K.Mf (Y.ty w) (Y.tree.degAt w)‖
            ≤ z0 ^ t * (γ * C ^ (Y.tree.degAt w)) := by
              refine mul_le_mul ?_ (hMf _ _ hl) (norm_nonneg _) (by positivity)
              refine (hz _ _).trans ?_
              rw [show nb + (t - nb) = t by omega]
          _ = _ := by ring



open Classical in
private lemma pt_prod_bound (K : PtK) {τ : VType} {k : ℕ} (Y : RootedTypedTree τ k) (δ : ℕ)
    (ρ : VType → ℕ → ℂ)
    (z0 R1 γ C CG Cρ : ℝ) (hz0 : 0 ≤ z0) (hR1 : 1 ≤ R1) (hγ : 1 ≤ γ) (hC : 1 ≤ C)
    (hCG : 1 ≤ CG) (hCρ : 1 ≤ Cρ)
    (hz1 : ‖K.z1‖ ≤ z0) (hz2 : ‖K.z2‖ ≤ z0)
    (hcp : ∀ n1 n2, 1 ≤ n1 + n2 → ‖K.cp n1 n2‖ ≤ R1 ^ (n1 + n2))
    (hMf : ∀ σ d, σ ≠ VType.lat → ‖K.Mf σ d‖ ≤ γ * C ^ d)
    (hMg : ∀ d, ‖K.Mg d‖ ≤ CG * (γ * C ^ d))
    (hρ : ∀ d, ‖ρ τ d‖ ≤ Cρ * (γ * C ^ d))
    (v : List ℕ) (hv : v ∈ Y.tree.vtxs) (hvt : Y.ty v ≠ VType.lat) (j : ℕ)
    (hj : j ≤ Y.tree.childCount v) :
    ‖∏ w ∈ Y.tree.vtxs.toFinset, ptW K Y δ ρ v j w‖ ≤
      Cρ * CG * γ * C ^ δ * z0 ^ 2 * (γ * C * R1 * z0) ^ k := by
  have hτ : τ ≠ VType.lat := by rw [← Y.root_ty]; exact fun e => Y.root_ext (Y.root_ty ▸ e)
  have hroot : ([] : List ℕ) ∈ Y.tree.vtxs.toFinset := List.mem_toFinset.mpr (ob_pt_root_mem _)
  have hroot_ty : Y.ty [] ≠ VType.lat := by rw [Y.root_ty]; exact hτ
  have hvm : v ∈ Y.tree.vtxs.toFinset := List.mem_toFinset.mpr hv
  obtain ⟨hs1, hs2, hs3, hs4⟩ := ob_deg_sums Y
  rw [norm_prod]
  have hnn : ∀ w ∈ Y.tree.vtxs.toFinset, 0 ≤ ‖ptW K Y δ ρ v j w‖ := fun _ _ => norm_nonneg _
  refine (Finset.prod_le_prod₀ hnn (fun w hw => pt_vertex_bound K Y δ ρ z0 R1 γ C CG Cρ hz0 hR1 hγ hC hCG hCρ
    hz1 hz2 hcp hMf hMg hρ v hv hvt j hj w (List.mem_toFinset.mp hw))).trans ?_
  simp only [Finset.prod_mul_distrib]
  have hγ0 : 0 ≤ γ := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hR0 : 0 ≤ R1 := by linarith
  have hCG0 : 0 ≤ CG := by linarith
  have hCρ0 : 0 ≤ Cρ := by linarith
  -- degrees: cc + 1 = degAt for non-root
  have hdeg : ∀ w : List ℕ, w ≠ [] → Y.tree.childCount w + 1 = Y.tree.degAt w := fun w hw =>
    (pp_degAt_ne hw).symm
  -- P1
  have P1 : ∏ w ∈ Y.tree.vtxs.toFinset, (if Y.ty w = VType.lat then R1 ^ (Y.tree.childCount w + 1) else 1) =
      R1 ^ k := by
    have : ∀ w ∈ Y.tree.vtxs.toFinset, (if Y.ty w = VType.lat then R1 ^ (Y.tree.childCount w + 1) else 1) =
        R1 ^ (if Y.ty w = VType.lat then Y.tree.degAt w else 0) := by
      intro w _
      by_cases hl : Y.ty w = VType.lat
      · have hw0 : w ≠ [] := by rintro rfl; exact hroot_ty hl
        simp [hl, hdeg w hw0]
      · simp [hl]
    rw [Finset.prod_congr rfl this, Finset.prod_pow_eq_pow_sum, ← Finset.sum_filter]
    exact congrArg _ hs2
  -- P2
  have P2 : ∏ w ∈ Y.tree.vtxs.toFinset,
      (if Y.ty w = VType.lat then (1 : ℝ) else z0 ^ (Y.tree.childCount w + 1 + (if w = v then 1 else 0))) =
      z0 ^ (k + 2) := by
    have : ∀ w ∈ Y.tree.vtxs.toFinset,
        (if Y.ty w = VType.lat then (1 : ℝ) else z0 ^ (Y.tree.childCount w + 1 + (if w = v then 1 else 0))) =
        z0 ^ ((if Y.ty w = VType.lat then 0 else Y.tree.degAt w) + (if w = [] then 1 else 0) +
          (if w = v then 1 else 0)) := by
      intro w _
      by_cases hl : Y.ty w = VType.lat
      · have hw0 : w ≠ [] := by rintro rfl; exact hroot_ty hl
        have hwv : w ≠ v := fun e => hvt (e ▸ hl)
        simp [hl, hw0, hwv]
      · by_cases hw0 : w = []
        · subst hw0; simp [hl, pp_degAt_root]
        · simp [hl, hw0, pp_degAt_ne hw0]
    rw [Finset.prod_congr rfl this, Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
    congr 1
    have e1 : ∑ w ∈ Y.tree.vtxs.toFinset, (if Y.ty w = VType.lat then 0 else Y.tree.degAt w) = k := by
      refine Eq.trans ?_ hs1
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun w _ => ?_
      by_cases hl : Y.ty w = VType.lat <;> simp [hl]
    have e2 : ∑ w ∈ Y.tree.vtxs.toFinset, (if w = [] then 1 else 0) = 1 := by
      simp [Finset.sum_ite_eq', hroot]
    have e3 : ∑ w ∈ Y.tree.vtxs.toFinset, (if w = v then 1 else 0) = 1 := by
      simp [Finset.sum_ite_eq', hvm]
    omega
  have P3 : ∏ w ∈ Y.tree.vtxs.toFinset, (if Y.ty w = VType.lat then (1 : ℝ) else γ) ≤ γ ^ (k + 1) := by
    rw [Finset.prod_ite, Finset.prod_const_one, Finset.prod_const, one_mul]
    refine pow_le_pow_right₀ hγ ?_
    calc _ ≤ Y.tree.vtxs.toFinset.card := Finset.card_filter_le _ _
      _ = k + 1 := ob_card_vtxs Y
  have P4 : ∏ w ∈ Y.tree.vtxs.toFinset,
      (if Y.ty w = VType.lat then (1 : ℝ) else C ^ (Y.tree.degAt w + (if w = [] then δ else 0))) =
      C ^ (k + δ) := by
    have : ∀ w ∈ Y.tree.vtxs.toFinset,
        (if Y.ty w = VType.lat then (1 : ℝ) else C ^ (Y.tree.degAt w + (if w = [] then δ else 0))) =
        C ^ ((if Y.ty w = VType.lat then 0 else Y.tree.degAt w) + (if w = [] then δ else 0)) := by
      intro w _
      by_cases hl : Y.ty w = VType.lat
      · have hw0 : w ≠ [] := by rintro rfl; exact hroot_ty hl
        simp [hl, hw0]
      · simp [hl]
    rw [Finset.prod_congr rfl this, Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib]
    congr 1
    have e1 : ∑ w ∈ Y.tree.vtxs.toFinset, (if Y.ty w = VType.lat then 0 else Y.tree.degAt w) = k := by
      refine Eq.trans ?_ hs1
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun w _ => ?_
      by_cases hl : Y.ty w = VType.lat <;> simp [hl]
    have e2 : ∑ w ∈ Y.tree.vtxs.toFinset, (if w = [] then δ else 0) = δ := by
      simp [Finset.sum_ite_eq', hroot]
    omega
  have P5 : ∏ w ∈ Y.tree.vtxs.toFinset, (if w = v then CG else 1) = CG := by
    simp [Finset.prod_ite_eq', hvm]
  have P6 : ∏ w ∈ Y.tree.vtxs.toFinset,
      (if w = [] then (if ([] : List ℕ) = v then (1 : ℝ) else Cρ) else 1) ≤ Cρ := by
    have : ∏ w ∈ Y.tree.vtxs.toFinset,
        (if w = [] then (if ([] : List ℕ) = v then (1 : ℝ) else Cρ) else 1) =
        (if ([] : List ℕ) = v then (1 : ℝ) else Cρ) := by
      simp [Finset.prod_ite_eq', hroot]
    rw [this]
    split_ifs <;> linarith
  rw [P1, P2, P4, P5]
  have hz0' : 0 ≤ z0 ^ (k + 2) := by positivity
  calc R1 ^ k * z0 ^ (k + 2) * (∏ w ∈ Y.tree.vtxs.toFinset, (if Y.ty w = VType.lat then (1 : ℝ) else γ)) *
        C ^ (k + δ) * CG *
        (∏ w ∈ Y.tree.vtxs.toFinset, (if w = [] then (if ([] : List ℕ) = v then (1 : ℝ) else Cρ) else 1))
      ≤ R1 ^ k * z0 ^ (k + 2) * γ ^ (k + 1) * C ^ (k + δ) * CG * Cρ := by
        gcongr
    _ = _ := by ring



open Classical in
private lemma pt_sum_le (K : PtK) {τ : VType} {k : ℕ} (Y : RootedTypedTree τ k) (δ : ℕ)
    (ρ : VType → ℕ → ℂ)
    (z0 R1 γ C CG Cρ : ℝ) (hz0 : 0 ≤ z0) (hR1 : 1 ≤ R1) (hγ : 1 ≤ γ) (hC : 1 ≤ C)
    (hCG : 1 ≤ CG) (hCρ : 1 ≤ Cρ)
    (hz1 : ‖K.z1‖ ≤ z0) (hz2 : ‖K.z2‖ ≤ z0)
    (hcp : ∀ n1 n2, 1 ≤ n1 + n2 → ‖K.cp n1 n2‖ ≤ R1 ^ (n1 + n2))
    (hMf : ∀ σ d, σ ≠ VType.lat → ‖K.Mf σ d‖ ≤ γ * C ^ d)
    (hMg : ∀ d, ‖K.Mg d‖ ≤ CG * (γ * C ^ d))
    (hρ : ∀ d, ‖ρ τ d‖ ≤ Cρ * (γ * C ^ d)) :
    ‖ptSum K Y δ ρ‖ ≤ (2 * k + 1) *
      (Cρ * CG * γ * C ^ δ * z0 ^ 2 * (γ * C * R1 * z0) ^ k) := by
  set B := Cρ * CG * γ * C ^ δ * z0 ^ 2 * (γ * C * R1 * z0) ^ k with hB
  have hB0 : 0 ≤ B := by
    have : 0 ≤ γ := by linarith
    have : 0 ≤ C := by linarith
    have : 0 ≤ R1 := by linarith
    have : 0 ≤ CG := by linarith
    have : 0 ≤ Cρ := by linarith
    positivity
  unfold ptSum
  calc ‖∑ v ∈ Y.tree.vtxs.toFinset.filter (fun v => Y.ty v = VType.inp),
        ∑ j ∈ Finset.range (Y.tree.childCount v + 1),
          ∏ w ∈ Y.tree.vtxs.toFinset, ptW K Y δ ρ v j w‖
      ≤ ∑ v ∈ Y.tree.vtxs.toFinset.filter (fun v => Y.ty v = VType.inp),
        ∑ j ∈ Finset.range (Y.tree.childCount v + 1), B := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v hv => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
        have hv' := Finset.mem_filter.mp hv
        exact pt_prod_bound K Y δ ρ z0 R1 γ C CG Cρ hz0 hR1 hγ hC hCG hCρ hz1 hz2 hcp hMf hMg hρ v
          (List.mem_toFinset.mp hv'.1) (by rw [hv'.2]; decide) j
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    _ = ∑ v ∈ Y.tree.vtxs.toFinset.filter (fun v => Y.ty v = VType.inp),
        ((Y.tree.childCount v + 1 : ℕ) : ℝ) * B := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ∑ v ∈ Y.tree.vtxs.toFinset, ((Y.tree.childCount v + 1 : ℕ) : ℝ) * B := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun v _ _ => ?_
        positivity
    _ = ((2 * k + 1 : ℕ) : ℝ) * B := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, pp_sum_cc Y]
    _ = _ := by push_cast; ring

private lemma pt_sum_summable (K : PtK) (τ : VType) (hτ : τ ≠ VType.lat) (δ : ℕ)
    (ρ : VType → ℕ → ℂ)
    (z0 R1 γ C CG Cρ : ℝ) (hz0 : 0 ≤ z0) (hR1 : 1 ≤ R1) (hγ : 1 ≤ γ) (hC : 1 ≤ C)
    (hCG : 1 ≤ CG) (hCρ : 1 ≤ Cρ)
    (hz1 : ‖K.z1‖ ≤ z0) (hz2 : ‖K.z2‖ ≤ z0)
    (hcp : ∀ n1 n2, 1 ≤ n1 + n2 → ‖K.cp n1 n2‖ ≤ R1 ^ (n1 + n2))
    (hMf : ∀ σ d, σ ≠ VType.lat → ‖K.Mf σ d‖ ≤ γ * C ^ d)
    (hMg : ∀ d, ‖K.Mg d‖ ≤ CG * (γ * C ^ d))
    (hρ : ∀ d, ‖ρ τ d‖ ≤ Cρ * (γ * C ^ d))
    (hϑ : 8 * (γ * C * R1 * z0) ≤ 1) :
    Summable (fun Y : OE τ => ‖ptSum K Y.2 δ ρ‖) := by
  classical
  set ϑ := γ * C * R1 * z0 with hϑdef
  set A := Cρ * CG * γ * C ^ δ * z0 ^ 2 with hA
  have hγ0 : 0 ≤ γ := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hR0 : 0 ≤ R1 := by linarith
  have hCG0 : 0 ≤ CG := by linarith
  have hCρ0 : 0 ≤ Cρ := by linarith
  have hϑ0 : 0 ≤ ϑ := by positivity
  have hA0 : 0 ≤ A := by positivity
  have hf0 : ∀ Y : OE τ, 0 ≤ ‖ptSum K Y.2 δ ρ‖ := fun _ => norm_nonneg _
  have hinner : ∀ k : ℕ, ∑' X : RootedTypedTree τ k, ‖ptSum K X δ ρ‖ ≤
      (2 * k + 1) * A * (1 / 2) ^ k := by
    intro k
    haveI := (ob_card_rooted τ k).1
    letI : Fintype (RootedTypedTree τ k) := Fintype.ofFinite _
    rw [tsum_fintype]
    calc ∑ X : RootedTypedTree τ k, ‖ptSum K X δ ρ‖
        ≤ ∑ X : RootedTypedTree τ k, (2 * k + 1) * (A * ϑ ^ k) := by
          refine Finset.sum_le_sum fun X _ => ?_
          have := pt_sum_le K X δ ρ z0 R1 γ C CG Cρ hz0 hR1 hγ hC hCG hCρ hz1 hz2 hcp hMf hMg hρ
          calc _ ≤ _ := this
            _ = _ := by rw [hA, hϑdef]
      _ = (Nat.card (RootedTypedTree τ k) : ℝ) * ((2 * k + 1) * (A * ϑ ^ k)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
      _ ≤ (4 : ℝ) ^ k * ((2 * k + 1) * (A * ϑ ^ k)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast (ob_card_rooted τ k).2
      _ = (2 * k + 1) * A * (4 * ϑ) ^ k := by rw [mul_pow]; ring
      _ ≤ (2 * k + 1) * A * (1 / 2) ^ k := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) k) (by positivity)
  have hsumk : Summable (fun k : ℕ => (2 * k + 1) * A * (1 / 2 : ℝ) ^ k) := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 / 2 : ℝ)) (by norm_num [abs_of_pos])
    have h2 : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have := ((h1.mul_left (2 * A)).add (h2.mul_left A))
    refine this.congr fun k => ?_
    simp only [pow_one]; ring
  rw [summable_sigma_of_nonneg hf0]
  refine ⟨fun k => ?_, ?_⟩
  · haveI := (ob_card_rooted τ k).1
    exact Summable.of_finite
  · refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun _ => norm_nonneg _) (fun k => ?_) hsumk
    exact hinner k



/-! ### The marked block sum -/

private def ptM1 (K : PtK) (σ : VType) : ℂ := ob_m K.z1 K.cdf1 K.Mf σ
private def ptM2 (K : PtK) (σ : VType) : ℂ := ob_m K.z2 K.cdf2 K.Mf σ
private noncomputable def ptP (K : PtK) (σ : VType) : ℂ := ∑' Y : OE σ, ptSum K Y.2 1 K.Mf
private def ptK1 (K : PtK) (σ : VType) : ℝ := ob_κ K.z1 K.cdf1 K.Mf σ
private def ptK2 (K : PtK) (σ : VType) : ℝ := ob_κ K.z2 K.cdf2 K.Mf σ
private noncomputable def ptKP (K : PtK) (σ : VType) : ℝ := ∑' Y : OE σ, ‖ptSum K Y.2 1 K.Mf‖

open Classical in
private noncomputable def ptTerm (K : PtK) (τ : VType) (p : ℕ) (c0 : Fin (2 * p + 1)) : ℂ :=
  K.z2 * K.cp (c0.val + 1) (2 * p + 1 - c0.val) *
    ∏ c' : Fin (2 * p + 1), (if c' < c0 then ptM1 K (ob_ty τ c'.val)
      else if c' = c0 then ptP K (ob_ty τ c'.val) else ptM2 K (ob_ty τ c'.val))

open Classical in
private noncomputable def ptTermN (K : PtK) (τ : VType) (p : ℕ) (c0 : Fin (2 * p + 1)) : ℝ :=
  ‖K.z2‖ * ‖K.cp (c0.val + 1) (2 * p + 1 - c0.val)‖ *
    ∏ c' : Fin (2 * p + 1), (if c' < c0 then ptK1 K (ob_ty τ c'.val)
      else if c' = c0 then ptKP K (ob_ty τ c'.val) else ptK2 K (ob_ty τ c'.val))

open Classical in
private lemma pt_blk_mk (K : PtK) (τ : VType) (p : ℕ) (c0 : Fin (2 * p + 1))
    (hC1 : ∀ σ, σ ≠ VType.lat → Summable (fun Y : OE σ => ‖ob_C K.z1 K.cdf1 K.Mf Y‖))
    (hC2 : ∀ σ, σ ≠ VType.lat → Summable (fun Y : OE σ => ‖ob_C K.z2 K.cdf2 K.Mf Y‖))
    (hP : ∀ σ, σ ≠ VType.lat → Summable (fun Y : OE σ => ‖ptSum K Y.2 1 K.Mf‖))
    (hτ : τ ≠ VType.lat) :
    Summable (fun g : (∀ c : Fin (2 * p + 1), OE (ob_ty τ c.val)) =>
      ‖ptBmk K ⟨p, g⟩ c0 (ptSum K (g c0).2 1 K.Mf)‖) ∧
    ∑' g : (∀ c : Fin (2 * p + 1), OE (ob_ty τ c.val)),
      ptBmk K ⟨p, g⟩ c0 (ptSum K (g c0).2 1 K.Mf) = ptTerm K τ p c0 ∧
    ∑' g : (∀ c : Fin (2 * p + 1), OE (ob_ty τ c.val)),
      ‖ptBmk K ⟨p, g⟩ c0 (ptSum K (g c0).2 1 K.Mf)‖ = ptTermN K τ p c0 := by
  let F : ∀ c : Fin (2 * p + 1), OE (ob_ty τ c.val) → ℂ := fun c' Y =>
    if c' < c0 then ob_C K.z1 K.cdf1 K.Mf Y
    else if c' = c0 then ptSum K Y.2 1 K.Mf else ob_C K.z2 K.cdf2 K.Mf Y
  have hF : ∀ c', Summable (fun Y : OE (ob_ty τ c'.val) => ‖F c' Y‖) := by
    intro c'
    have hn := ob_ty_ne_lat hτ c'.val
    by_cases a : c' < c0
    · simpa [F, a] using hC1 _ hn
    · by_cases b : c' = c0
      · simpa [F, a, b] using hP _ hn
      · simpa [F, a, b] using hC2 _ hn
  have hFn : ∀ c', Summable (fun Y : OE (ob_ty τ c'.val) => ‖(‖F c' Y‖ : ℝ)‖) := by
    intro c'; simpa only [norm_norm] using hF c'
  obtain ⟨hs1, ht1⟩ := ob_pi_tsum (R := ℂ) (2 * p + 1) (fun c => OE (ob_ty τ c.val)) F hF
  obtain ⟨-, ht2⟩ := ob_pi_tsum (R := ℝ) (2 * p + 1) (fun c => OE (ob_ty τ c.val))
    (fun c' Y => ‖F c' Y‖) hFn
  have hbk : ∀ g : (∀ c : Fin (2 * p + 1), OE (ob_ty τ c.val)),
      ptBmk K ⟨p, g⟩ c0 (ptSum K (g c0).2 1 K.Mf) =
        (K.z2 * K.cp (c0.val + 1) (2 * p + 1 - c0.val)) * ∏ c', F c' (g c') := by
    intro g
    unfold ptBmk
    congr 1
    refine Finset.prod_congr rfl fun c' _ => ?_
    by_cases a : c' < c0
    · simp [F, a]
    · by_cases b : c' = c0
      · subst b; simp [F]
      · simp [F, a, b]
  simp_rw [hbk]
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [norm_mul]
    exact hs1.mul_left _
  · rw [tsum_mul_left, ht1]
    unfold ptTerm
    congr 1
    refine Finset.prod_congr rfl fun c' _ => ?_
    by_cases a : c' < c0
    · simp [F, a, ptM1, ob_m]
    · by_cases b : c' = c0
      · subst b; simp [F, ptP]
      · simp [F, a, b, ptM2, ob_m]
  · simp_rw [norm_mul, norm_prod]
    rw [tsum_mul_left, ht2]
    unfold ptTermN
    congr 1
    refine Finset.prod_congr rfl fun c' _ => ?_
    by_cases a : c' < c0
    · simp [F, a, ptK1, ob_κ]
    · by_cases b : c' = c0
      · subst b; simp [F, ptKP]
      · simp [F, a, b, ptK2, ob_κ]



open Classical in
private lemma pt_termN_le (K : PtK) (τ : VType) (hτ : τ ≠ VType.lat) (p : ℕ) (c0 : Fin (2 * p + 1))
    (z0 R1 δ KP : ℝ) (hz2 : ‖K.z2‖ ≤ z0) (hR1 : 1 ≤ R1) (hδ : 0 ≤ δ) (hKP : 0 ≤ KP)
    (hcp : ∀ n1 n2, 1 ≤ n1 + n2 → ‖K.cp n1 n2‖ ≤ R1 ^ (n1 + n2))
    (hk1 : ∀ σ, σ ≠ VType.lat → 0 ≤ ptK1 K σ ∧ ptK1 K σ ≤ δ)
    (hk2 : ∀ σ, σ ≠ VType.lat → 0 ≤ ptK2 K σ ∧ ptK2 K σ ≤ δ)
    (hkP : ∀ σ, σ ≠ VType.lat → 0 ≤ ptKP K σ ∧ ptKP K σ ≤ KP) :
    ptTermN K τ p c0 ≤ z0 * (R1 ^ (2 * p + 2) * (KP * δ ^ (2 * p))) := by
  unfold ptTermN
  have hz0 : 0 ≤ z0 := (norm_nonneg _).trans hz2
  have hc0 : c0.val ≤ 2 * p := Nat.lt_succ_iff.mp c0.2
  have hcp' : ‖K.cp (c0.val + 1) (2 * p + 1 - c0.val)‖ ≤ R1 ^ (2 * p + 2) := by
    refine (hcp _ _ (by omega)).trans ?_
    rw [show c0.val + 1 + (2 * p + 1 - c0.val) = 2 * p + 2 by omega]
  set Fv : Fin (2 * p + 1) → ℝ := fun c' => if c' < c0 then ptK1 K (ob_ty τ c'.val)
      else if c' = c0 then ptKP K (ob_ty τ c'.val) else ptK2 K (ob_ty τ c'.val) with hFv
  have hFn : ∀ c', 0 ≤ Fv c' := by
    intro c'
    have hn := ob_ty_ne_lat hτ c'.val
    simp only [hFv]
    split_ifs
    · exact (hk1 _ hn).1
    · exact (hkP _ hn).1
    · exact (hk2 _ hn).1
  have hprod : ∏ c', Fv c' ≤ KP * δ ^ (2 * p) := by
    rw [← Finset.mul_prod_erase Finset.univ Fv (Finset.mem_univ c0)]
    have h1 : Fv c0 ≤ KP := by
      simp only [hFv, lt_irrefl, if_false, if_true]
      exact (hkP _ (ob_ty_ne_lat hτ c0.val)).2
    have h2 : ∏ c' ∈ Finset.univ.erase c0, Fv c' ≤ δ ^ (2 * p) := by
      calc ∏ c' ∈ Finset.univ.erase c0, Fv c' ≤ ∏ c' ∈ Finset.univ.erase c0, δ := by
            refine Finset.prod_le_prod₀ (fun c' _ => hFn c') (fun c' hc' => ?_)
            have hn := ob_ty_ne_lat hτ c'.val
            have hne := (Finset.mem_erase.mp hc').1
            simp only [hFv, hne, if_false]
            split_ifs
            · exact (hk1 _ hn).2
            · exact (hk2 _ hn).2
        _ = δ ^ (2 * p) := by
            rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
              Fintype.card_fin]; congr 1
    exact mul_le_mul h1 h2 (Finset.prod_nonneg fun c' _ => hFn c') hKP
  calc ‖K.z2‖ * ‖K.cp (c0.val + 1) (2 * p + 1 - c0.val)‖ * ∏ c', Fv c'
      ≤ z0 * R1 ^ (2 * p + 2) * (KP * δ ^ (2 * p)) := by
        refine mul_le_mul (mul_le_mul hz2 hcp' (norm_nonneg _) hz0) hprod
          (Finset.prod_nonneg fun c' _ => hFn c') (by positivity)
    _ = _ := by ring

open Classical in
private lemma pt_Bm_sum (K : PtK) (τ : VType) (hτ : τ ≠ VType.lat)
    (hC1 : ∀ σ, σ ≠ VType.lat → Summable (fun Y : OE σ => ‖ob_C K.z1 K.cdf1 K.Mf Y‖))
    (hC2 : ∀ σ, σ ≠ VType.lat → Summable (fun Y : OE σ => ‖ob_C K.z2 K.cdf2 K.Mf Y‖))
    (hP : ∀ σ, σ ≠ VType.lat → Summable (fun Y : OE σ => ‖ptSum K Y.2 1 K.Mf‖))
    (z0 R1 δ KP : ℝ) (hz2 : ‖K.z2‖ ≤ z0) (hR1 : 1 ≤ R1) (hδ : 0 ≤ δ) (hKP : 0 ≤ KP)
    (hRδ : R1 ^ 2 * δ ^ 2 ≤ 1 / 16)
    (hcp : ∀ n1 n2, 1 ≤ n1 + n2 → ‖K.cp n1 n2‖ ≤ R1 ^ (n1 + n2))
    (hk1 : ∀ σ, σ ≠ VType.lat → 0 ≤ ptK1 K σ ∧ ptK1 K σ ≤ δ)
    (hk2 : ∀ σ, σ ≠ VType.lat → 0 ≤ ptK2 K σ ∧ ptK2 K σ ≤ δ)
    (hkP : ∀ σ, σ ≠ VType.lat → 0 ≤ ptKP K σ ∧ ptKP K σ ≤ KP) :
    Summable (fun b : OBlk τ => ‖ptBm K b‖) ∧
    ∑' b : OBlk τ, ptBm K b = ∑' p : ℕ, ∑ c0 : Fin (2 * p + 1), ptTerm K τ p c0 := by
  have hz0 : 0 ≤ z0 := (norm_nonneg _).trans hz2
  have hblk := fun p (c0 : Fin (2 * p + 1)) => pt_blk_mk K τ p c0 hC1 hC2 hP hτ
  have hfib : ∀ p : ℕ, Summable (fun g : (∀ c : Fin (2 * p + 1), OE (ob_ty τ c.val)) =>
      ‖ptBm K ⟨p, g⟩‖) := by
    intro p
    have hs : Summable (fun g : (∀ c : Fin (2 * p + 1), OE (ob_ty τ c.val)) =>
        ∑ c0 : Fin (2 * p + 1), ‖ptBmk K ⟨p, g⟩ c0 (ptSum K (g c0).2 1 K.Mf)‖) :=
      summable_sum fun c0 _ => (hblk p c0).1
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun g => ?_) hs
    unfold ptBm
    exact norm_sum_le _ _
  have hfibsum : ∀ p : ℕ, ∑' g : (∀ c : Fin (2 * p + 1), OE (ob_ty τ c.val)), ‖ptBm K ⟨p, g⟩‖ ≤
      (2 * p + 1) * (z0 * (R1 ^ (2 * p + 2) * (KP * δ ^ (2 * p)))) := by
    intro p
    have hs : Summable (fun g : (∀ c : Fin (2 * p + 1), OE (ob_ty τ c.val)) =>
        ∑ c0 : Fin (2 * p + 1), ‖ptBmk K ⟨p, g⟩ c0 (ptSum K (g c0).2 1 K.Mf)‖) :=
      summable_sum fun c0 _ => (hblk p c0).1
    calc ∑' g : (∀ c : Fin (2 * p + 1), OE (ob_ty τ c.val)), ‖ptBm K ⟨p, g⟩‖
        ≤ ∑' g : (∀ c : Fin (2 * p + 1), OE (ob_ty τ c.val)),
          ∑ c0 : Fin (2 * p + 1), ‖ptBmk K ⟨p, g⟩ c0 (ptSum K (g c0).2 1 K.Mf)‖ := by
          refine Summable.tsum_le_tsum (fun g => ?_) (hfib p) hs
          unfold ptBm
          exact norm_sum_le _ _
      _ = ∑ c0 : Fin (2 * p + 1), ptTermN K τ p c0 := by
          rw [Summable.tsum_finsetSum (fun c0 _ => (hblk p c0).1)]
          exact Finset.sum_congr rfl fun c0 _ => (hblk p c0).2.2
      _ ≤ ∑ c0 : Fin (2 * p + 1), z0 * (R1 ^ (2 * p + 2) * (KP * δ ^ (2 * p))) :=
          Finset.sum_le_sum fun c0 _ => pt_termN_le K τ hτ p c0 z0 R1 δ KP hz2 hR1 hδ hKP hcp hk1 hk2 hkP
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  have hgeo : Summable (fun p : ℕ => ((2 * p + 1 : ℕ) : ℝ) * (z0 * (R1 ^ (2 * p + 2) * (KP * δ ^ (2 * p))))) := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 / 16 : ℝ)) (by norm_num [abs_of_pos])
    have h2 : Summable (fun p : ℕ => (1 / 16 : ℝ) ^ p) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have h3 := (h1.mul_left (2 * (z0 * R1 ^ 2 * KP))).add (h2.mul_left (z0 * R1 ^ 2 * KP))
    refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) h3
    have hq : R1 ^ (2 * p + 2) * δ ^ (2 * p) = R1 ^ 2 * (R1 ^ 2 * δ ^ 2) ^ p := by
      rw [mul_pow, ← pow_mul, ← pow_mul, pow_add]; ring
    have hq2 : (R1 ^ 2 * δ ^ 2) ^ p ≤ (1 / 16 : ℝ) ^ p := pow_le_pow_left₀ (by positivity) hRδ p
    calc ((2 * p + 1 : ℕ) : ℝ) * (z0 * (R1 ^ (2 * p + 2) * (KP * δ ^ (2 * p))))
        = ((2 * p + 1 : ℕ) : ℝ) * (z0 * R1 ^ 2 * KP) * (R1 ^ 2 * δ ^ 2) ^ p := by
          calc ((2 * p + 1 : ℕ) : ℝ) * (z0 * (R1 ^ (2 * p + 2) * (KP * δ ^ (2 * p))))
              = ((2 * p + 1 : ℕ) : ℝ) * (z0 * KP) * (R1 ^ (2 * p + 2) * δ ^ (2 * p)) := by ring
            _ = _ := by rw [hq]; ring
      _ ≤ ((2 * p + 1 : ℕ) : ℝ) * (z0 * R1 ^ 2 * KP) * (1 / 16 : ℝ) ^ p :=
          mul_le_mul_of_nonneg_left hq2 (by positivity)
      _ = _ := by push_cast; simp only [pow_one]; ring
  have hsumN : Summable (fun p : ℕ => ∑' g : (∀ c : Fin (2 * p + 1), OE (ob_ty τ c.val)),
      ‖ptBm K ⟨p, g⟩‖) :=
    Summable.of_nonneg_of_le (fun p => tsum_nonneg fun _ => norm_nonneg _)
      (fun p => by simpa using hfibsum p) hgeo
  have hsum : Summable (fun b : OBlk τ => ‖ptBm K b‖) :=
    (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr ⟨hfib, hsumN⟩
  refine ⟨hsum, ?_⟩
  rw [Summable.tsum_sigma' (fun p => (hfib p).of_norm) hsum.of_norm]
  refine tsum_congr fun p => ?_
  have : ∑' g : (∀ c : Fin (2 * p + 1), OE (ob_ty τ c.val)), ptBm K ⟨p, g⟩ =
      ∑' g : (∀ c : Fin (2 * p + 1), OE (ob_ty τ c.val)),
        ∑ c0 : Fin (2 * p + 1), ptBmk K ⟨p, g⟩ c0 (ptSum K (g c0).2 1 K.Mf) := rfl
  rw [this, Summable.tsum_finsetSum (fun c0 _ => (hblk p c0).1.of_norm)]
  exact Finset.sum_congr rfl fun c0 _ => (hblk p c0).2.1



/-! ### Parity evaluation of the marked block sum -/

private lemma pp_prod_ty_range (F : VType → ℂ) (τ : VType) (n : ℕ) :
    ∏ i ∈ Finset.range n, F (ob_ty τ i) = F (ob_f0 τ) ^ ((n + 1) / 2) * F τ ^ (n / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    by_cases h : n % 2 = 0
    · have h1 : ob_ty τ n = ob_f0 τ := by simp [ob_ty, h]
      rw [h1]
      have e1 : (n + 1 + 1) / 2 = (n + 1) / 2 + 1 := by omega
      have e2 : (n + 1) / 2 = n / 2 := by omega
      rw [e1, e2, pow_succ]; ring
    · have h1 : ob_ty τ n = τ := by simp [ob_ty, h]
      rw [h1]
      have e1 : (n + 1 + 1) / 2 = (n + 1) / 2 := by omega
      have e2 : (n + 1) / 2 = n / 2 + 1 := by omega
      rw [e1, e2, pow_succ]; ring

private lemma pp_ob_ty_reflect (τ : VType) (p j : ℕ) (hj : j ≤ 2 * p) :
    ob_ty τ (2 * p - j) = ob_ty τ j := by
  unfold ob_ty
  have : (2 * p - j) % 2 = j % 2 := by omega
  simp [this]

open Classical in
private lemma pp_prod_before (F : VType → ℂ) (τ : VType) (p : ℕ) (c0 : Fin (2 * p + 1)) :
    ∏ c' : Fin (2 * p + 1), (if c' < c0 then F (ob_ty τ c'.val) else 1) =
      F (ob_f0 τ) ^ ((c0.val + 1) / 2) * F τ ^ (c0.val / 2) := by
  simp only [Fin.lt_def]
  rw [Fin.prod_univ_eq_prod_range (fun i => if i < c0.val then F (ob_ty τ i) else 1) (2 * p + 1)]
  have : ∏ i ∈ Finset.range (2 * p + 1), (if i < c0.val then F (ob_ty τ i) else 1) =
      ∏ i ∈ Finset.range c0.val, F (ob_ty τ i) := by
    rw [← Finset.prod_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨by omega, h⟩
  rw [this, pp_prod_ty_range]
  all_goals first | rfl | (simp only [Fin.lt_def])

open Classical in
private lemma pp_prod_after (F : VType → ℂ) (τ : VType) (p : ℕ) (c0 : Fin (2 * p + 1)) :
    ∏ c' : Fin (2 * p + 1), (if c0 < c' then F (ob_ty τ c'.val) else 1) =
      F (ob_f0 τ) ^ ((2 * p - c0.val + 1) / 2) * F τ ^ ((2 * p - c0.val) / 2) := by
  simp only [Fin.lt_def]
  rw [Fin.prod_univ_eq_prod_range (fun i => if c0.val < i then F (ob_ty τ i) else 1) (2 * p + 1)]
  rw [← Finset.prod_range_reflect (fun i => if c0.val < i then F (ob_ty τ i) else 1) (2 * p + 1)]
  have : ∏ j ∈ Finset.range (2 * p + 1), (if c0.val < 2 * p + 1 - 1 - j then
      F (ob_ty τ (2 * p + 1 - 1 - j)) else 1) = ∏ j ∈ Finset.range (2 * p - c0.val), F (ob_ty τ j) := by
    rw [← Finset.prod_filter]
    have hc0 : c0.val ≤ 2 * p := Nat.lt_succ_iff.mp c0.2
    rw [show (Finset.range (2 * p + 1)).filter (fun j => c0.val < 2 * p + 1 - 1 - j) =
      Finset.range (2 * p - c0.val) by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · exact fun h => by omega
        · exact fun h => ⟨by omega, by omega⟩]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [show 2 * p + 1 - 1 - j = 2 * p - j by omega, pp_ob_ty_reflect τ p j (by omega)]
  rw [this, pp_prod_ty_range]

open Classical in
private lemma pp_prod_three {n : ℕ} (A B C : Fin n → ℂ) (c0 : Fin n) :
    ∏ c' : Fin n, (if c' < c0 then A c' else if c' = c0 then B c' else C c') =
      (∏ c', if c' < c0 then A c' else 1) * B c0 * (∏ c', if c0 < c' then C c' else 1) := by
  have h : ∀ c' : Fin n, (if c' < c0 then A c' else if c' = c0 then B c' else C c') =
      ((if c' < c0 then A c' else 1) * (if c' = c0 then B c' else 1)) * (if c0 < c' then C c' else 1) := by
    intro c'
    rcases lt_trichotomy c' c0 with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.mpr h.le]
  rw [Finset.prod_congr rfl (fun c' _ => h c'), Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp [Finset.prod_ite_eq']



private def ptGB (K : PtK) (τ : VType) (e f : ℕ) : ℂ :=
  K.cp (2 * e + 1) (2 * f + 1) * (ptM1 K (ob_f0 τ) * ptM1 K τ) ^ e * (ptM2 K (ob_f0 τ) * ptM2 K τ) ^ f

private def ptGE (K : PtK) (τ : VType) (e f : ℕ) : ℂ :=
  K.cp (2 * e + 2) (2 * f + 2) * (ptM1 K (ob_f0 τ) * ptM1 K τ) ^ e * (ptM2 K (ob_f0 τ) * ptM2 K τ) ^ f

open Classical in
private lemma ptTerm_formula (K : PtK) (τ : VType) (p : ℕ) (c0 : Fin (2 * p + 1)) :
    ptTerm K τ p c0 = K.z2 * K.cp (c0.val + 1) (2 * p + 1 - c0.val) *
      ((ptM1 K (ob_f0 τ) ^ ((c0.val + 1) / 2) * ptM1 K τ ^ (c0.val / 2)) *
        ptP K (ob_ty τ c0.val) *
        (ptM2 K (ob_f0 τ) ^ ((2 * p - c0.val + 1) / 2) * ptM2 K τ ^ ((2 * p - c0.val) / 2))) := by
  unfold ptTerm
  rw [mul_assoc, pp_prod_three (fun c' : Fin (2 * p + 1) => ptM1 K (ob_ty τ c'.val))
    (fun c' : Fin (2 * p + 1) => ptP K (ob_ty τ c'.val))
    (fun c' : Fin (2 * p + 1) => ptM2 K (ob_ty τ c'.val)) c0,
    pp_prod_before (ptM1 K) τ p c0, pp_prod_after (ptM2 K) τ p c0]
  ring

private lemma ptTerm_even (K : PtK) (τ : VType) (p e : ℕ) (he : 2 * e < 2 * p + 1) :
    ptTerm K τ p ⟨2 * e, he⟩ = K.z2 * ptP K (ob_f0 τ) * ptGB K τ e (p - e) := by
  rw [ptTerm_formula]
  have hep : e ≤ p := by omega
  have h1 : (2 * e + 1) / 2 = e := by omega
  have h2 : 2 * e / 2 = e := by omega
  have h3 : (2 * p - 2 * e + 1) / 2 = p - e := by omega
  have h4 : (2 * p - 2 * e) / 2 = p - e := by omega
  have h5 : 2 * p + 1 - 2 * e = 2 * (p - e) + 1 := by omega
  have h6 : ob_ty τ (2 * e) = ob_f0 τ := by simp [ob_ty]
  simp only [h1, h2, h3, h4, h5, h6, ptGB]
  ring

private lemma ptTerm_odd (K : PtK) (τ : VType) (p e : ℕ) (he : 2 * e + 1 < 2 * p + 1) :
    ptTerm K τ p ⟨2 * e + 1, he⟩ = K.z2 * (ptM1 K (ob_f0 τ) * ptM2 K (ob_f0 τ)) * ptP K τ *
      ptGE K τ e (p - 1 - e) := by
  rw [ptTerm_formula]
  have hep : e + 1 ≤ p := by omega
  have h1 : (2 * e + 1 + 1) / 2 = e + 1 := by omega
  have h2 : (2 * e + 1) / 2 = e := by omega
  have h3 : (2 * p - (2 * e + 1) + 1) / 2 = (p - 1 - e) + 1 := by omega
  have h4 : (2 * p - (2 * e + 1)) / 2 = p - 1 - e := by omega
  have h5 : 2 * p + 1 - (2 * e + 1) = 2 * (p - 1 - e) + 2 := by omega
  have h6 : ob_ty τ (2 * e + 1) = τ := by simp [ob_ty]
  simp only [h1, h2, h3, h4, h5, h6, ptGE, pow_succ]
  ring

private lemma pp_sum_range_even_odd {M : Type*} [AddCommMonoid M] (f : ℕ → M) (p : ℕ) :
    ∑ c ∈ Finset.range (2 * p + 1), f c =
      ∑ e ∈ Finset.range (p + 1), f (2 * e) + ∑ e ∈ Finset.range p, f (2 * e + 1) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [show 2 * (p + 1) + 1 = 2 * p + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ (fun e => f (2 * e)) (p + 1), Finset.sum_range_succ (fun e => f (2 * e + 1)) p]
    have e1 : 2 * p + 1 = 2 * p + 1 := rfl
    have e2 : 2 * (p + 1) = 2 * p + 1 + 1 := by ring
    rw [e2]
    abel

private lemma ptTerm_sum (K : PtK) (τ : VType) (p : ℕ) :
    ∑ c0 : Fin (2 * p + 1), ptTerm K τ p c0 =
      ∑ e ∈ Finset.range (p + 1), K.z2 * ptP K (ob_f0 τ) * ptGB K τ e (p - e) +
      ∑ e ∈ Finset.range p, K.z2 * (ptM1 K (ob_f0 τ) * ptM2 K (ob_f0 τ)) * ptP K τ * ptGE K τ e (p - 1 - e) := by
  classical
  let T : ℕ → ℂ := fun c => if h : c < 2 * p + 1 then ptTerm K τ p ⟨c, h⟩ else 0
  have h1 : ∑ c0 : Fin (2 * p + 1), ptTerm K τ p c0 = ∑ c ∈ Finset.range (2 * p + 1), T c := by
    rw [← Fin.sum_univ_eq_sum_range T (2 * p + 1)]
    refine Finset.sum_congr rfl fun c0 _ => ?_
    show ptTerm K τ p c0 = (if h : c0.val < 2 * p + 1 then ptTerm K τ p ⟨c0.val, h⟩ else 0)
    rw [dif_pos c0.2]
  rw [h1, pp_sum_range_even_odd]
  congr 1
  · refine Finset.sum_congr rfl fun e he => ?_
    have he' : 2 * e < 2 * p + 1 := by have := Finset.mem_range.mp he; omega
    simp only [T, dif_pos he']
    exact ptTerm_even K τ p e he'
  · refine Finset.sum_congr rfl fun e he => ?_
    have he' : 2 * e + 1 < 2 * p + 1 := by have := Finset.mem_range.mp he; omega
    simp only [T, dif_pos he']
    exact ptTerm_odd K τ p e he'



private lemma pp_antidiag (g : ℕ × ℕ → ℂ) (hg : Summable (fun x => ‖g x‖)) :
    Summable (fun n : ℕ => ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, g x) ∧
    ∑' n : ℕ, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, g x = ∑' x, g x := by
  classical
  have e := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ))
  have hs : Summable (fun x : (Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n) => g (x.2 : ℕ × ℕ)) :=
    (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).summable_iff.mpr hg.of_norm
  have hfib : ∀ n : ℕ, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, g x = ∑' a : Finset.HasAntidiagonal.antidiagonal n, g (a : ℕ × ℕ) := by
    intro n
    exact (Finset.tsum_subtype (Finset.HasAntidiagonal.antidiagonal n) (fun x : ℕ × ℕ => g x)).symm
  refine ⟨?_, ?_⟩
  · simp_rw [hfib]
    exact hs.sigma' fun n => Summable.of_finite
  · simp_rw [hfib]
    rw [← hs.tsum_sigma' (fun n => Summable.of_finite)]
    exact (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq g

private lemma pt_GB_summable (K : PtK) (τ : VType) (hτ : τ ≠ VType.lat) (R1 δ : ℝ) (hR1 : 1 ≤ R1)
    (hδ : 0 ≤ δ) (hRδ : R1 ^ 2 * δ ^ 2 ≤ 1 / 16)
    (hcp : ∀ n1 n2, 1 ≤ n1 + n2 → ‖K.cp n1 n2‖ ≤ R1 ^ (n1 + n2))
    (hm1 : ∀ σ, σ ≠ VType.lat → ‖ptM1 K σ‖ ≤ δ) (hm2 : ∀ σ, σ ≠ VType.lat → ‖ptM2 K σ‖ ≤ δ) :
    Summable (fun x : ℕ × ℕ => ‖ptGB K τ x.1 x.2‖) ∧ Summable (fun x : ℕ × ℕ => ‖ptGE K τ x.1 x.2‖) := by
  have hτ' : ob_f0 τ ≠ VType.lat := (ob_f0_ne hτ).2
  have ha1 : ‖ptM1 K (ob_f0 τ) * ptM1 K τ‖ ≤ δ ^ 2 := by
    rw [norm_mul, pow_two]
    exact mul_le_mul (hm1 _ hτ') (hm1 _ hτ) (norm_nonneg _) hδ
  have ha2 : ‖ptM2 K (ob_f0 τ) * ptM2 K τ‖ ≤ δ ^ 2 := by
    rw [norm_mul, pow_two]
    exact mul_le_mul (hm2 _ hτ') (hm2 _ hτ) (norm_nonneg _) hδ
  have hgeo : Summable (fun x : ℕ × ℕ => R1 ^ 4 * (((1 / 16 : ℝ)) ^ x.1 * (1 / 16 : ℝ) ^ x.2)) := by
    have h : Summable (fun k : ℕ => (1 / 16 : ℝ) ^ k) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    exact (h.mul_of_nonneg h (fun _ => by positivity) (fun _ => by positivity)).mul_left _
  have key : ∀ (a b : ℕ) (e f c : ℕ), a + b = 2 * e + 2 * f + c → c ≤ 4 → 2 ≤ c →
      ‖K.cp a b‖ * (‖ptM1 K (ob_f0 τ) * ptM1 K τ‖ ^ e * ‖ptM2 K (ob_f0 τ) * ptM2 K τ‖ ^ f) ≤
        R1 ^ 4 * ((1 / 16 : ℝ) ^ e * (1 / 16 : ℝ) ^ f) := by
    intro a b e f c hab hc4 hc2
    calc ‖K.cp a b‖ * (‖ptM1 K (ob_f0 τ) * ptM1 K τ‖ ^ e * ‖ptM2 K (ob_f0 τ) * ptM2 K τ‖ ^ f)
        ≤ R1 ^ (2 * e + 2 * f + c) * ((δ ^ 2) ^ e * (δ ^ 2) ^ f) := by
          refine mul_le_mul ?_ (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ha1 e)
            (pow_le_pow_left₀ (norm_nonneg _) ha2 f) (by positivity) (by positivity)) (by positivity)
            (by positivity)
          rw [← hab]; exact hcp _ _ (by omega)
      _ = R1 ^ c * ((R1 ^ 2 * δ ^ 2) ^ e * (R1 ^ 2 * δ ^ 2) ^ f) := by
          rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, pow_add, pow_add]; ring
      _ ≤ R1 ^ 4 * ((1 / 16 : ℝ) ^ e * (1 / 16 : ℝ) ^ f) := by
          refine mul_le_mul (pow_le_pow_right₀ hR1 hc4) (mul_le_mul (pow_le_pow_left₀ (by positivity) hRδ e)
            (pow_le_pow_left₀ (by positivity) hRδ f) (by positivity) (by positivity)) (by positivity)
            (by positivity)
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_) hgeo,
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_) hgeo⟩
  · unfold ptGB
    rw [norm_mul, norm_mul, norm_pow, norm_pow, mul_assoc]
    exact key (2 * x.1 + 1) (2 * x.2 + 1) x.1 x.2 2 (by omega) (by omega) (by omega)
  · unfold ptGE
    rw [norm_mul, norm_mul, norm_pow, norm_pow, mul_assoc]
    exact key (2 * x.1 + 2) (2 * x.2 + 2) x.1 x.2 4 (by omega) (by omega) (by omega)

private lemma pt_Wm_eval (K : PtK) (τ : VType) (hτ : τ ≠ VType.lat) (R1 δ : ℝ) (hR1 : 1 ≤ R1)
    (hδ : 0 ≤ δ) (hRδ : R1 ^ 2 * δ ^ 2 ≤ 1 / 16)
    (hcp : ∀ n1 n2, 1 ≤ n1 + n2 → ‖K.cp n1 n2‖ ≤ R1 ^ (n1 + n2))
    (hm1 : ∀ σ, σ ≠ VType.lat → ‖ptM1 K σ‖ ≤ δ) (hm2 : ∀ σ, σ ≠ VType.lat → ‖ptM2 K σ‖ ≤ δ) :
    ∑' p : ℕ, ∑ c0 : Fin (2 * p + 1), ptTerm K τ p c0 =
      K.z2 * (ptP K (ob_f0 τ) * ∑' x : ℕ × ℕ, ptGB K τ x.1 x.2 +
        ptM1 K (ob_f0 τ) * ptM2 K (ob_f0 τ) * ptP K τ * ∑' x : ℕ × ℕ, ptGE K τ x.1 x.2) := by
  obtain ⟨hB, hE⟩ := pt_GB_summable K τ hτ R1 δ hR1 hδ hRδ hcp hm1 hm2
  obtain ⟨hB1, hB2⟩ := pp_antidiag (fun x => ptGB K τ x.1 x.2) hB
  obtain ⟨hE1, hE2⟩ := pp_antidiag (fun x => ptGE K τ x.1 x.2) hE
  have hA : ∀ p : ℕ, ∑ e ∈ Finset.range (p + 1), K.z2 * ptP K (ob_f0 τ) * ptGB K τ e (p - e) =
      K.z2 * ptP K (ob_f0 τ) * ∑ x ∈ Finset.HasAntidiagonal.antidiagonal p, ptGB K τ x.1 x.2 := by
    intro p
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  have hBp : ∀ p : ℕ, ∑ e ∈ Finset.range p, K.z2 * (ptM1 K (ob_f0 τ) * ptM2 K (ob_f0 τ)) * ptP K τ *
      ptGE K τ e (p - 1 - e) = if p = 0 then 0 else K.z2 * (ptM1 K (ob_f0 τ) * ptM2 K (ob_f0 τ)) * ptP K τ *
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (p - 1), ptGE K τ x.1 x.2 := by
    intro p
    rcases p with _ | n
    · simp
    · simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  simp_rw [ptTerm_sum, hA, hBp]
  have hsA : Summable (fun p : ℕ => K.z2 * ptP K (ob_f0 τ) * ∑ x ∈ Finset.HasAntidiagonal.antidiagonal p, ptGB K τ x.1 x.2) :=
    hB1.mul_left _
  have hsB : Summable (fun p : ℕ => if p = 0 then (0 : ℂ) else K.z2 * (ptM1 K (ob_f0 τ) * ptM2 K (ob_f0 τ)) *
      ptP K τ * ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (p - 1), ptGE K τ x.1 x.2) := by
    rw [← summable_nat_add_iff 1]
    simpa using hE1.mul_left (K.z2 * (ptM1 K (ob_f0 τ) * ptM2 K (ob_f0 τ)) * ptP K τ)
  rw [hsA.tsum_add hsB, tsum_mul_left, hB2, hsB.tsum_eq_zero_add]
  simp only [if_true, zero_add, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
  rw [tsum_mul_left, hE2]
  ring



private lemma pt_both {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (ℓ J : ℕ) (R : ℝ) (B : ℕ) {m n : ℕ} (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (g : ℤ → Ω → ℝ) (l : ℕ) (t : ℝ) (γ C : ℝ) (hγ : 1 ≤ γ) (hC : 1 ≤ C)
    (hμ : ∀ i, |μ i| ≤ C) (hlam : ∀ j, |lam j| ≤ C) (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B)
    (ht : 64 * (γ * C * max 1 R) ^ 2 ≤ t)
    (hsumo : ∀ i : Fin m, Summable (fun q : OneBufIdx m n J ℓ VType.out (Sum.inl i) =>
      ‖oneBufVal P β ℓ J R B μ lam g l t q.2.1 q.2.2.1‖))
    (hbdo : ∀ i : Fin m, ∑' q : OneBufIdx m n J ℓ VType.out (Sum.inl i),
      ‖oneBufVal P β ℓ J R B μ lam g l t q.2.1 q.2.2.1‖ ≤ 2 / Real.sqrt t)
    (hsumi : ∀ j : Fin n, Summable (fun q : OneBufIdx m n J ℓ VType.inp (Sum.inr (Sum.inl j)) =>
      ‖oneBufVal P β ℓ J R B μ lam g l t q.2.1 q.2.2.1‖))
    (hbdi : ∀ j : Fin n, ∑' q : OneBufIdx m n J ℓ VType.inp (Sum.inr (Sum.inl j)),
      ‖oneBufVal P β ℓ J R B μ lam g l t q.2.1 q.2.2.1‖ ≤ 2 / Real.sqrt t) :
    (∀ σ : VType, σ ≠ VType.lat → Summable (fun Y : OE σ =>
      ‖ob_C (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) Y‖)) ∧
    (0 ≤ ob_κ (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) VType.out ∧
      ob_κ (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) VType.out ≤ 2 * γ * C / Real.sqrt t) ∧
    (0 ≤ ob_κ (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) VType.inp ∧
      ob_κ (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) VType.inp ≤ 2 * γ * C / Real.sqrt t) ∧
    ((max 1 R) ^ 2 * (2 * γ * C / Real.sqrt t) ^ 2 ≤ 1 / 16) ∧
    (∀ x : ℝ, |x| ≤ C → ‖(x : ℂ)‖ * (‖zetaT t‖ *
      (16 / 15 * ((max 1 R) ^ 2 * (2 * γ * C / Real.sqrt t)))) < 1) ∧
    ‖zetaT t‖ = (Real.sqrt t)⁻¹ ∧
    (Summable (fun p : ℕ => ‖ob_cdf P β ℓ J R g l (2 * p + 2)‖ *
        ob_κ (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) VType.inp ^ (p + 1) *
        ob_κ (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) VType.out ^ p) ∧
      ∑' p : ℕ, ‖ob_cdf P β ℓ J R g l (2 * p + 2)‖ *
        ob_κ (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) VType.inp ^ (p + 1) *
        ob_κ (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) VType.out ^ p ≤
        16 / 15 * ((max 1 R) ^ 2 * (2 * γ * C / Real.sqrt t))) ∧
    (Summable (fun p : ℕ => ‖ob_cdf P β ℓ J R g l (2 * p + 2)‖ *
        ob_κ (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) VType.out ^ (p + 1) *
        ob_κ (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) VType.inp ^ p) ∧
      ∑' p : ℕ, ‖ob_cdf P β ℓ J R g l (2 * p + 2)‖ *
        ob_κ (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) VType.out ^ (p + 1) *
        ob_κ (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) VType.inp ^ p ≤
        16 / 15 * ((max 1 R) ^ 2 * (2 * γ * C / Real.sqrt t))) ∧
    (∀ i : Fin m, oneBufG P β ℓ J R B μ lam g l t VType.out (Sum.inl i) =
      zetaT t / (1 - (μ i : ℂ) * zetaT t * ∑' p : ℕ, ob_cdf P β ℓ J R g l (2 * p + 2) *
        ob_m (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) VType.inp ^ (p + 1) *
        ob_m (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) VType.out ^ p)) ∧
    (∀ j : Fin n, oneBufG P β ℓ J R B μ lam g l t VType.inp (Sum.inr (Sum.inl j)) =
      zetaT t / (1 - (lam j : ℂ) * zetaT t * ∑' p : ℕ, ob_cdf P β ℓ J R g l (2 * p + 2) *
        ob_m (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) VType.out ^ (p + 1) *
        ob_m (zetaT t) (ob_cdf P β ℓ J R g l) (ob_Mf B μ lam) VType.inp ^ p)) := by
  classical
  set R1 := max 1 R with hR1def
  have hR1 : 1 ≤ R1 := le_max_left _ _
  set K := γ * C * R1 with hK
  have hK1 : 1 ≤ K := by
    have h1 : 1 ≤ γ * C := by nlinarith
    nlinarith
  have htpos : 0 < t := by nlinarith
  set s := Real.sqrt t with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr htpos
  have hs2 : s ^ 2 = t := Real.sq_sqrt htpos.le
  have hs8 : 8 * K ≤ s := by
    rw [hs]; apply Real.le_sqrt_of_sq_le; nlinarith
  set δ := 2 * γ * C / s with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hRδ : R1 ^ 2 * δ ^ 2 ≤ 1 / 16 := by
    have h1 : R1 * δ = 2 * K / s := by rw [hδ, hK]; field_simp
    have h2 : 2 * K / s ≤ 1 / 4 := by rw [div_le_iff₀ hs0]; linarith
    have h3 : 0 ≤ 2 * K / s := by positivity
    calc R1 ^ 2 * δ ^ 2 = (R1 * δ) ^ 2 := by ring
      _ = (2 * K / s) ^ 2 := by rw [h1]
      _ ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ h3 h2 2
      _ = 1 / 16 := by norm_num
  have hout := ob_C_bound_out P β ℓ J R B μ lam g l t C γ (by linarith) (by linarith) hμ hm
    (2 / s) (by positivity) hsumo hbdo
  have hinp := ob_C_bound_inp P β ℓ J R B μ lam g l t C γ (by linarith) (by linarith) hlam hn
    (2 / s) (by positivity) hsumi hbdi
  set ζ := zetaT t with hζ
  set cdf := ob_cdf P β ℓ J R g l with hcdf
  set Mf := ob_Mf B μ lam with hMf
  have hCsum : ∀ τ, τ ≠ VType.lat → Summable (fun Y : OE τ => ‖ob_C ζ cdf Mf Y‖) := by
    intro τ hτ
    cases τ
    · exact hout.1
    · exact hinp.1
    · exact absurd rfl hτ
  have hδeq : γ * (C * (2 / s)) = δ := by rw [hδ]; ring
  have hκo : ob_κ ζ cdf Mf VType.out ≤ δ := by
    have := hout.2; rw [hδeq] at this; exact this
  have hκi : ob_κ ζ cdf Mf VType.inp ≤ δ := by
    have := hinp.2; rw [hδeq] at this; exact this
  have hκo0 : 0 ≤ ob_κ ζ cdf Mf VType.out := tsum_nonneg fun _ => norm_nonneg _
  have hκi0 : 0 ≤ ob_κ ζ cdf Mf VType.inp := tsum_nonneg fun _ => norm_nonneg _
  have hmo : ‖ob_m ζ cdf Mf VType.out‖ ≤ δ :=
    (norm_tsum_le_tsum_norm (hout.1)).trans hκo
  have hmi : ‖ob_m ζ cdf Mf VType.inp‖ ≤ δ :=
    (norm_tsum_le_tsum_norm (hinp.1)).trans hκi
  have hu : oneBufMo P β ℓ J R B μ lam g l t = ob_m ζ cdf Mf VType.out :=
    (ob_m_out_eq P β ℓ J R B μ lam g l t hsumo).symm
  have hv : oneBufMin P β ℓ J R B μ lam g l t = ob_m ζ cdf Mf VType.inp :=
    (ob_m_inp_eq P β ℓ J R B μ lam g l t hsumi).symm
  have hcd : ∀ d : ℕ, 1 ≤ d → ‖cdf d‖ ≤ R1 ^ d := fun d hd => ob_cdf_bound P hβ ℓ J R g l d hd
  have hzeta : ‖ζ‖ = s⁻¹ := ob_zeta_norm htpos
  have hAne : (Complex.I * (s : ℂ)) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hs0.ne')
  have hζA : ζ = (Complex.I * (s : ℂ))⁻¹ := rfl
  -- smallness of the geometric parameter
  have hzgen : ∀ (x : ℝ), |x| ≤ C → ∀ ηs : ℝ, 0 ≤ ηs → ηs ≤ 16 / 15 * (R1 ^ 2 * δ) →
      ‖(x : ℂ)‖ * (‖ζ‖ * ηs) < 1 := by
    intro x hx ηs hη0 hη1
    rw [Complex.norm_real, Real.norm_eq_abs, hzeta]
    have h1 : |x| * (s⁻¹ * ηs) ≤ C * (s⁻¹ * (16 / 15 * (R1 ^ 2 * δ))) :=
      mul_le_mul hx (mul_le_mul_of_nonneg_left hη1 (by positivity)) (by positivity) (by linarith)
    have h2 : C * (s⁻¹ * (16 / 15 * (R1 ^ 2 * δ))) = 32 / 15 * (γ * C ^ 2 * R1 ^ 2) / s ^ 2 := by
      rw [hδ]; field_simp; ring
    have h3 : γ * C ^ 2 * R1 ^ 2 ≤ K ^ 2 := by
      rw [hK]; nlinarith [mul_nonneg (sub_nonneg.2 hγ) (sq_nonneg (C * R1))]
    have h4 : 64 * K ^ 2 ≤ s ^ 2 := by rw [hs2]; exact ht
    have h5 : 32 / 15 * (γ * C ^ 2 * R1 ^ 2) / s ^ 2 < 1 := by
      rw [div_lt_one (by positivity)]; nlinarith [sq_nonneg K]
    linarith
  have hη_o := ob_eta_bounds cdf R1 hR1 hcd (ob_κ ζ cdf Mf VType.inp) (ob_κ ζ cdf Mf VType.out)
    δ hκi0 hκi hκo0 hκo hRδ
  have hη_i := ob_eta_bounds cdf R1 hR1 hcd (ob_κ ζ cdf Mf VType.out) (ob_κ ζ cdf Mf VType.inp)
    δ hκo0 hκo hκi0 hκi hRδ
  have hnn_o : 0 ≤ ∑' p : ℕ, ‖cdf (2 * p + 2)‖ * ob_κ ζ cdf Mf VType.inp ^ (p + 1) *
      ob_κ ζ cdf Mf VType.out ^ p := tsum_nonneg fun p => by positivity
  have hnn_i : 0 ≤ ∑' p : ℕ, ‖cdf (2 * p + 2)‖ * ob_κ ζ cdf Mf VType.out ^ (p + 1) *
      ob_κ ζ cdf Mf VType.inp ^ p := tsum_nonneg fun p => by positivity
  have hGo : ∀ i : Fin m, oneBufG P β ℓ J R B μ lam g l t VType.out (Sum.inl i) =
      ζ / (1 - (μ i : ℂ) * ζ * ∑' p : ℕ, cdf (2 * p + 2) * ob_m ζ cdf Mf VType.inp ^ (p + 1) *
        ob_m ζ cdf Mf VType.out ^ p) := by
    intro i
    rw [ob_G_eq P β ℓ J R B μ lam g l t VType.out (Sum.inl i) (by simp [AsgCompat]) (hsumo i)]
    rw [← hζ, ← hcdf, ← hMf]
    have e1 : ∀ Y : OE VType.out,
        ((asgVal (L := cutoffLabels J ℓ) μ lam (some (Sum.inl i)) ^ Y.2.tree.degAt [] : ℝ) : ℂ) *
          ob_rest ζ cdf Mf Y.2 = (μ i : ℂ) ^ Y.2.tree.degAt [] * ob_rest ζ cdf Mf Y.2 := by
      intro Y
      change (((μ i) ^ Y.2.tree.degAt [] : ℝ) : ℂ) * _ = _
      simp only [Complex.ofReal_pow]
    simp_rw [e1]
    exact ob_tree_sum ζ cdf Mf VType.out (by decide) hCsum (μ i : ℂ) hη_o.1
      (hzgen (μ i) (hμ i) _ hnn_o hη_o.2)
  have hGi : ∀ j : Fin n, oneBufG P β ℓ J R B μ lam g l t VType.inp (Sum.inr (Sum.inl j)) =
      ζ / (1 - (lam j : ℂ) * ζ * ∑' p : ℕ, cdf (2 * p + 2) * ob_m ζ cdf Mf VType.out ^ (p + 1) *
        ob_m ζ cdf Mf VType.inp ^ p) := by
    intro j
    rw [ob_G_eq P β ℓ J R B μ lam g l t VType.inp (Sum.inr (Sum.inl j)) (by simp [AsgCompat])
      (hsumi j)]
    rw [← hζ, ← hcdf, ← hMf]
    have e1 : ∀ Y : OE VType.inp,
        ((asgVal (L := cutoffLabels J ℓ) μ lam (some (Sum.inr (Sum.inl j))) ^ Y.2.tree.degAt [] : ℝ) : ℂ) *
          ob_rest ζ cdf Mf Y.2 = (lam j : ℂ) ^ Y.2.tree.degAt [] * ob_rest ζ cdf Mf Y.2 := by
      intro Y
      change (((lam j) ^ Y.2.tree.degAt [] : ℝ) : ℂ) * _ = _
      simp only [Complex.ofReal_pow]
    simp_rw [e1]
    exact ob_tree_sum ζ cdf Mf VType.inp (by decide) hCsum (lam j : ℂ) hη_i.1
      (hzgen (lam j) (hlam j) _ hnn_i hη_i.2)
  refine ⟨hCsum, ⟨hκo0, ?_⟩, ⟨hκi0, ?_⟩, hRδ, ?_, hzeta, ⟨hη_o.1, ?_⟩, ⟨hη_i.1, ?_⟩, hGo, hGi⟩
  · exact hκo.trans (le_of_eq hδ.symm)
  · exact hκi.trans (le_of_eq hδ.symm)
  · intro x hx
    exact hzgen x hx _ (by positivity) le_rfl
  · exact hη_o.2
  · exact hη_i.2



private lemma pp_solve (po pin fo fin a d b Po Pin T : ℂ)
    (h1 : Po = po * (a * Po + b * Pin)) (h2 : Pin = fin + pin * (b * Po + d * Pin))
    (h3 : T = fo * (a * Po + b * Pin))
    (hΔ : (1 - po * a) * (1 - pin * d) - po * pin * b ^ 2 ≠ 0) :
    T = fo * fin * b / ((1 - po * a) * (1 - pin * d) - po * pin * b ^ 2) := by
  have e1 : ((1 - po * a) * (1 - pin * d) - po * pin * b ^ 2) * Po = po * b * fin := by
    linear_combination (1 - pin * d) * h1 + po * b * h2
  have e2 : ((1 - po * a) * (1 - pin * d) - po * pin * b ^ 2) * Pin = (1 - po * a) * fin := by
    linear_combination (1 - po * a) * h2 + pin * b * h1
  have e4 : ((1 - po * a) * (1 - pin * d) - po * pin * b ^ 2) * (a * Po + b * Pin) = b * fin := by
    linear_combination a * e1 + b * e2
  rw [h3, eq_div_iff hΔ]
  linear_combination fo * e4



private lemma pp_alpha_pair {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) {g : ℤ → Ω → ℝ} (hg : ∀ α, Measurable (g α))
    (ℓ J : ℕ) (R : ℝ) (α : ℤ) (q1 q2 : ℝ) (h1 : (max 1 R) ^ 2 * |q1| ≤ 1 / 16)
    (h2 : (max 1 R) ^ 2 * |q2| ≤ 1 / 16) (r : ℕ) :
    HasSum (fun x : ℕ × ℕ => ∫ ω, cutoffXi β ℓ J R 1 g α ω ^ (2 * x.1 + r) *
        cutoffXi β ℓ J R 2 g α ω ^ (2 * x.2 + r) * ((-q1) ^ x.1 * (-q2) ^ x.2) ∂P)
      (∫ ω, cutoffXi β ℓ J R 1 g α ω ^ r * cutoffXi β ℓ J R 2 g α ω ^ r /
        ((1 + q1 * cutoffXi β ℓ J R 1 g α ω ^ 2) * (1 + q2 * cutoffXi β ℓ J R 2 g α ω ^ 2)) ∂P) := by
  have hR1 : (1 : ℝ) ≤ max 1 R := le_max_left _ _
  set ξ1 := cutoffXi β ℓ J R 1 g α with hξ1
  set ξ2 := cutoffXi β ℓ J R 2 g α with hξ2
  have hm1 : Measurable ξ1 := ob_xi_meas hg β ℓ J R 1 α
  have hm2 : Measurable ξ2 := ob_xi_meas hg β ℓ J R 2 α
  have hle1 : ∀ ω, |ξ1 ω| ≤ max 1 R := fun ω => ob_xi_le hβ ℓ J R g 1 α ω
  have hle2 : ∀ ω, |ξ2 ω| ≤ max 1 R := fun ω => ob_xi_le hβ ℓ J R g 2 α ω
  set a := (max 1 R) ^ 2 * |q1| with ha
  set b := (max 1 R) ^ 2 * |q2| with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hpt : ∀ (x : ℕ × ℕ) (ω : Ω), ‖ξ1 ω ^ (2 * x.1 + r) * ξ2 ω ^ (2 * x.2 + r) *
      ((-q1) ^ x.1 * (-q2) ^ x.2)‖ ≤ (max 1 R) ^ (2 * r) * (a ^ x.1 * b ^ x.2) := by
    intro x ω
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, norm_pow, Real.norm_eq_abs,
      Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_neg]
    calc |ξ1 ω| ^ (2 * x.1 + r) * |ξ2 ω| ^ (2 * x.2 + r) * (|q1| ^ x.1 * |q2| ^ x.2)
        ≤ (max 1 R) ^ (2 * x.1 + r) * (max 1 R) ^ (2 * x.2 + r) * (|q1| ^ x.1 * |q2| ^ x.2) := by
          refine mul_le_mul (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hle1 ω) _)
            (pow_le_pow_left₀ (abs_nonneg _) (hle2 ω) _) (by positivity) (by positivity))
            le_rfl (by positivity) (by positivity)
      _ = (max 1 R) ^ (2 * r) * (a ^ x.1 * b ^ x.2) := by
          rw [ha, hb, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
          rw [show (max 1 R) ^ (2 * x.1 + r) * (max 1 R) ^ (2 * x.2 + r) =
            (max 1 R) ^ (2 * x.1) * (max 1 R) ^ (2 * x.2) * (max 1 R) ^ (2 * r) by
              rw [pow_add, pow_add, pow_mul]; ring]
          rw [pow_mul, pow_mul]
          ring
  have hint : ∀ x : ℕ × ℕ, Integrable (fun ω => ξ1 ω ^ (2 * x.1 + r) * ξ2 ω ^ (2 * x.2 + r) *
      ((-q1) ^ x.1 * (-q2) ^ x.2)) P := by
    intro x
    refine Integrable.of_bound ?_ ((max 1 R) ^ (2 * r) * (a ^ x.1 * b ^ x.2))
      (Filter.Eventually.of_forall (hpt x))
    exact (((hm1.pow_const _).mul (hm2.pow_const _)).mul_const _).aestronglyMeasurable
  have hgeo : Summable (fun x : ℕ × ℕ => (max 1 R) ^ (2 * r) * (a ^ x.1 * b ^ x.2)) := by
    have ha1 : a < 1 := by linarith
    have hb1 : b < 1 := by linarith
    exact ((summable_geometric_of_lt_one ha0 ha1).mul_of_nonneg (summable_geometric_of_lt_one hb0 hb1)
      (fun _ => by positivity) (fun _ => by positivity)).mul_left _
  have hsumint : Summable (fun x : ℕ × ℕ => ∫ ω, ‖ξ1 ω ^ (2 * x.1 + r) * ξ2 ω ^ (2 * x.2 + r) *
      ((-q1) ^ x.1 * (-q2) ^ x.2)‖ ∂P) := by
    refine Summable.of_nonneg_of_le (fun x => integral_nonneg fun ω => norm_nonneg _)
      (fun x => ?_) hgeo
    have h := MeasureTheory.norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => ‖ξ1 ω ^ (2 * x.1 + r) * ξ2 ω ^ (2 * x.2 + r) * ((-q1) ^ x.1 * (-q2) ^ x.2)‖)
      (C := (max 1 R) ^ (2 * r) * (a ^ x.1 * b ^ x.2))
      (Filter.Eventually.of_forall fun ω => by rw [norm_norm]; exact hpt x ω)
    rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hS := hasSum_integral_of_summable_integral_norm hint hsumint
  convert hS using 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  symm
  have hx1 : |q1 * ξ1 ω ^ 2| < 1 := by
    rw [abs_mul, abs_pow]
    calc |q1| * |ξ1 ω| ^ 2 ≤ |q1| * (max 1 R) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hle1 ω) 2) (abs_nonneg _)
      _ ≤ 1 / 16 := by rw [mul_comm]; exact h1
      _ < 1 := by norm_num
  have hx2 : |q2 * ξ2 ω ^ 2| < 1 := by
    rw [abs_mul, abs_pow]
    calc |q2| * |ξ2 ω| ^ 2 ≤ |q2| * (max 1 R) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hle2 ω) 2) (abs_nonneg _)
      _ ≤ 1 / 16 := by rw [mul_comm]; exact h2
      _ < 1 := by norm_num
  have e : ∀ x : ℕ × ℕ, ξ1 ω ^ (2 * x.1 + r) * ξ2 ω ^ (2 * x.2 + r) * ((-q1) ^ x.1 * (-q2) ^ x.2) =
      (ξ1 ω ^ r * ξ2 ω ^ r) * ((-(q1 * ξ1 ω ^ 2)) ^ x.1 * (-(q2 * ξ2 ω ^ 2)) ^ x.2) := by
    intro x
    rw [pow_add, pow_add, pow_mul, pow_mul, neg_pow q1, neg_pow q2, neg_pow (q1 * ξ1 ω ^ 2),
      neg_pow (q2 * ξ2 ω ^ 2), mul_pow, mul_pow]
    ring
  simp_rw [e]
  rw [tsum_mul_left]
  have s1 : Summable (fun k : ℕ => ‖(-(q1 * ξ1 ω ^ 2)) ^ k‖) := by
    simp_rw [norm_pow, Real.norm_eq_abs, abs_neg]
    exact summable_geometric_of_lt_one (abs_nonneg _) hx1
  have s2 : Summable (fun k : ℕ => ‖(-(q2 * ξ2 ω ^ 2)) ^ k‖) := by
    simp_rw [norm_pow, Real.norm_eq_abs, abs_neg]
    exact summable_geometric_of_lt_one (abs_nonneg _) hx2
  rw [← tsum_mul_tsum_of_summable_norm s1 s2, tsum_geometric_of_abs_lt_one (by rwa [abs_neg]),
    tsum_geometric_of_abs_lt_one (by rwa [abs_neg])]
  rw [sub_neg_eq_add, sub_neg_eq_add]
  field_simp



private lemma pp_series_core {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) {g : ℤ → Ω → ℝ} (hg : ∀ α, Measurable (g α))
    (ℓ J : ℕ) (R : ℝ) (q1 q2 : ℝ) (h1 : (max 1 R) ^ 2 * |q1| ≤ 1 / 16)
    (h2 : (max 1 R) ^ 2 * |q2| ≤ 1 / 16) (r : ℕ) :
    HasSum (fun x : ℕ × ℕ => (∑ α ∈ cutoffLabels J ℓ, ∫ ω, cutoffXi β ℓ J R 1 g α ω ^ (2 * x.1 + r) *
        cutoffXi β ℓ J R 2 g α ω ^ (2 * x.2 + r) ∂P) * ((-q1) ^ x.1 * (-q2) ^ x.2))
      (∑ α ∈ cutoffLabels J ℓ, ∫ ω, cutoffXi β ℓ J R 1 g α ω ^ r * cutoffXi β ℓ J R 2 g α ω ^ r /
        ((1 + q1 * cutoffXi β ℓ J R 1 g α ω ^ 2) * (1 + q2 * cutoffXi β ℓ J R 2 g α ω ^ 2)) ∂P) := by
  have hα : ∀ α ∈ cutoffLabels J ℓ, HasSum (fun x : ℕ × ℕ => (∫ ω, cutoffXi β ℓ J R 1 g α ω ^ (2 * x.1 + r) *
        cutoffXi β ℓ J R 2 g α ω ^ (2 * x.2 + r) ∂P) * ((-q1) ^ x.1 * (-q2) ^ x.2))
      (∫ ω, cutoffXi β ℓ J R 1 g α ω ^ r * cutoffXi β ℓ J R 2 g α ω ^ r /
        ((1 + q1 * cutoffXi β ℓ J R 1 g α ω ^ 2) * (1 + q2 * cutoffXi β ℓ J R 2 g α ω ^ 2)) ∂P) := by
    intro α _
    have := pp_alpha_pair P hβ hg ℓ J R α q1 q2 h1 h2 r
    simp_rw [integral_mul_const] at this
    exact this
  have := hasSum_sum hα
  simpa only [Finset.sum_mul] using this

private lemma pp_pairedB_series {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) {g : ℤ → Ω → ℝ} (hg : ∀ α, Measurable (g α))
    (ℓ J : ℕ) (R : ℝ) (q1 q2 : ℝ) (h1 : (max 1 R) ^ 2 * |q1| ≤ 1 / 16)
    (h2 : (max 1 R) ^ 2 * |q2| ≤ 1 / 16) :
    HasSum (fun x : ℕ × ℕ => (∑ α ∈ cutoffLabels J ℓ, ∫ ω, cutoffXi β ℓ J R 1 g α ω ^ (2 * x.1 + 1) *
        cutoffXi β ℓ J R 2 g α ω ^ (2 * x.2 + 1) ∂P) * ((-q1) ^ x.1 * (-q2) ^ x.2))
      (pairedB P (cutoffXi β ℓ J R 1 g) (cutoffXi β ℓ J R 2 g) q1 q2) := by
  have h := pp_series_core P hβ hg ℓ J R q1 q2 h1 h2 1
  have hz : ∀ α ∉ cutoffLabels J ℓ, ∫ ω, cutoffXi β ℓ J R 1 g α ω * cutoffXi β ℓ J R 2 g α ω /
      ((1 + q1 * cutoffXi β ℓ J R 1 g α ω ^ 2) * (1 + q2 * cutoffXi β ℓ J R 2 g α ω ^ 2)) ∂P = 0 := by
    intro α hα
    have hv : cutoffVarpi β ℓ J 1 α = 0 := by unfold cutoffVarpi; rw [if_neg hα]
    have h0 : ∀ ω, cutoffXi β ℓ J R 1 g α ω = 0 := by intro ω; simp [cutoffXi, hv]
    simp [h0]
  have hpB : pairedB P (cutoffXi β ℓ J R 1 g) (cutoffXi β ℓ J R 2 g) q1 q2 =
      ∑ α ∈ cutoffLabels J ℓ, ∫ ω, cutoffXi β ℓ J R 1 g α ω * cutoffXi β ℓ J R 2 g α ω /
        ((1 + q1 * cutoffXi β ℓ J R 1 g α ω ^ 2) * (1 + q2 * cutoffXi β ℓ J R 2 g α ω ^ 2)) ∂P := by
    unfold pairedB
    exact tsum_eq_sum hz
  rw [hpB]
  simpa only [pow_one] using h

private lemma pp_pairedE_series {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) {g : ℤ → Ω → ℝ} (hg : ∀ α, Measurable (g α))
    (ℓ J : ℕ) (R : ℝ) (q1 q2 : ℝ) (h1 : (max 1 R) ^ 2 * |q1| ≤ 1 / 16)
    (h2 : (max 1 R) ^ 2 * |q2| ≤ 1 / 16) :
    HasSum (fun x : ℕ × ℕ => (∑ α ∈ cutoffLabels J ℓ, ∫ ω, cutoffXi β ℓ J R 1 g α ω ^ (2 * x.1 + 2) *
        cutoffXi β ℓ J R 2 g α ω ^ (2 * x.2 + 2) ∂P) * ((-q1) ^ x.1 * (-q2) ^ x.2))
      (pairedE P (cutoffXi β ℓ J R 1 g) (cutoffXi β ℓ J R 2 g) q1 q2) := by
  have h := pp_series_core P hβ hg ℓ J R q1 q2 h1 h2 2
  have hz : ∀ α ∉ cutoffLabels J ℓ, ∫ ω, cutoffXi β ℓ J R 1 g α ω ^ 2 * cutoffXi β ℓ J R 2 g α ω ^ 2 /
      ((1 + q1 * cutoffXi β ℓ J R 1 g α ω ^ 2) * (1 + q2 * cutoffXi β ℓ J R 2 g α ω ^ 2)) ∂P = 0 := by
    intro α hα
    have hv : cutoffVarpi β ℓ J 1 α = 0 := by unfold cutoffVarpi; rw [if_neg hα]
    have h0 : ∀ ω, cutoffXi β ℓ J R 1 g α ω = 0 := by intro ω; simp [cutoffXi, hv]
    simp [h0]
  have hpE : pairedE P (cutoffXi β ℓ J R 1 g) (cutoffXi β ℓ J R 2 g) q1 q2 =
      ∑ α ∈ cutoffLabels J ℓ, ∫ ω, cutoffXi β ℓ J R 1 g α ω ^ 2 * cutoffXi β ℓ J R 2 g α ω ^ 2 /
        ((1 + q1 * cutoffXi β ℓ J R 1 g α ω ^ 2) * (1 + q2 * cutoffXi β ℓ J R 2 g α ω ^ 2)) ∂P := by
    unfold pairedE
    exact tsum_eq_sum hz
  rw [hpE]
  exact h



private lemma pp_xi_le2 {Ω : Type} {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (ℓ J : ℕ) (R : ℝ)
    (g : ℤ → Ω → ℝ) (l : ℕ) (α : ℤ) (ω : Ω) :
    |cutoffXi β ℓ J R l g α ω| ≤ cutoffVarpi β ℓ J l α * max 1 R := by
  have hR1 : (0 : ℝ) ≤ max 1 R := le_trans zero_le_one (le_max_left _ _)
  obtain ⟨h0, h1⟩ := ob_cutoffVarpi_range hβ ℓ J l α
  unfold cutoffXi
  rw [abs_mul, abs_of_nonneg h0]
  refine mul_le_mul_of_nonneg_left ?_ h0
  split_ifs with h
  · exact h.trans (le_max_right _ _)
  · simpa using hR1

private lemma pp_cp_bound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (ℓ J : ℕ) (R : ℝ) (g : ℤ → Ω → ℝ) (n1 n2 : ℕ)
    (hn : 1 ≤ n1 + n2) :
    |∑ α ∈ cutoffLabels J ℓ, ∫ ω, cutoffXi β ℓ J R 1 g α ω ^ n1 * cutoffXi β ℓ J R 2 g α ω ^ n2 ∂P| ≤
      (max 1 R) ^ (n1 + n2) := by
  have hR1 : (0 : ℝ) ≤ max 1 R := le_trans zero_le_one (le_max_left _ _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ α, |∫ ω, cutoffXi β ℓ J R 1 g α ω ^ n1 * cutoffXi β ℓ J R 2 g α ω ^ n2 ∂P| ≤
      (cutoffVarpi β ℓ J 1 α ^ n1 * cutoffVarpi β ℓ J 2 α ^ n2) * (max 1 R) ^ (n1 + n2) := by
    intro α
    obtain ⟨a0, a1⟩ := ob_cutoffVarpi_range hβ ℓ J 1 α
    obtain ⟨b0, b1⟩ := ob_cutoffVarpi_range hβ ℓ J 2 α
    have hpt : ∀ ω, ‖cutoffXi β ℓ J R 1 g α ω ^ n1 * cutoffXi β ℓ J R 2 g α ω ^ n2‖ ≤
        (cutoffVarpi β ℓ J 1 α ^ n1 * cutoffVarpi β ℓ J 2 α ^ n2) * (max 1 R) ^ (n1 + n2) := by
      intro ω
      rw [norm_mul, norm_pow, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |cutoffXi β ℓ J R 1 g α ω| ^ n1 * |cutoffXi β ℓ J R 2 g α ω| ^ n2
          ≤ (cutoffVarpi β ℓ J 1 α * max 1 R) ^ n1 * (cutoffVarpi β ℓ J 2 α * max 1 R) ^ n2 :=
            mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (pp_xi_le2 hβ ℓ J R g 1 α ω) _)
              (pow_le_pow_left₀ (abs_nonneg _) (pp_xi_le2 hβ ℓ J R g 2 α ω) _) (by positivity)
              (by positivity)
        _ = (cutoffVarpi β ℓ J 1 α ^ n1 * cutoffVarpi β ℓ J 2 α ^ n2) * (max 1 R) ^ (n1 + n2) := by
            rw [mul_pow, mul_pow, pow_add]; ring
    have := MeasureTheory.norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => cutoffXi β ℓ J R 1 g α ω ^ n1 * cutoffXi β ℓ J R 2 g α ω ^ n2)
      (C := (cutoffVarpi β ℓ J 1 α ^ n1 * cutoffVarpi β ℓ J 2 α ^ n2) * (max 1 R) ^ (n1 + n2))
      (Filter.Eventually.of_forall hpt)
    simpa only [probReal_univ, mul_one, Real.norm_eq_abs] using this
  have h2 : ∀ α, cutoffVarpi β ℓ J 1 α ^ n1 * cutoffVarpi β ℓ J 2 α ^ n2 ≤
      (if 1 ≤ n1 then cutoffVarpi β ℓ J 1 α else cutoffVarpi β ℓ J 2 α) := by
    intro α
    obtain ⟨a0, a1⟩ := ob_cutoffVarpi_range hβ ℓ J 1 α
    obtain ⟨b0, b1⟩ := ob_cutoffVarpi_range hβ ℓ J 2 α
    by_cases hn1 : 1 ≤ n1
    · rw [if_pos hn1]
      calc cutoffVarpi β ℓ J 1 α ^ n1 * cutoffVarpi β ℓ J 2 α ^ n2
          ≤ cutoffVarpi β ℓ J 1 α * 1 :=
            mul_le_mul (pow_le_of_le_one a0 a1 (by omega)) (pow_le_one₀ b0 b1) (by positivity) a0
        _ = _ := mul_one _
    · rw [if_neg hn1]
      have hn1' : n1 = 0 := by omega
      subst hn1'
      calc cutoffVarpi β ℓ J 1 α ^ 0 * cutoffVarpi β ℓ J 2 α ^ n2 ≤ 1 * cutoffVarpi β ℓ J 2 α :=
            mul_le_mul (by simp) (pow_le_of_le_one b0 b1 (by omega)) (by positivity) zero_le_one
        _ = _ := one_mul _
  calc ∑ α ∈ cutoffLabels J ℓ, |∫ ω, cutoffXi β ℓ J R 1 g α ω ^ n1 * cutoffXi β ℓ J R 2 g α ω ^ n2 ∂P|
      ≤ ∑ α ∈ cutoffLabels J ℓ, (cutoffVarpi β ℓ J 1 α ^ n1 * cutoffVarpi β ℓ J 2 α ^ n2) *
        (max 1 R) ^ (n1 + n2) := Finset.sum_le_sum fun α _ => h1 α
    _ = (∑ α ∈ cutoffLabels J ℓ, cutoffVarpi β ℓ J 1 α ^ n1 * cutoffVarpi β ℓ J 2 α ^ n2) *
        (max 1 R) ^ (n1 + n2) := by rw [Finset.sum_mul]
    _ ≤ 1 * (max 1 R) ^ (n1 + n2) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc ∑ α ∈ cutoffLabels J ℓ, cutoffVarpi β ℓ J 1 α ^ n1 * cutoffVarpi β ℓ J 2 α ^ n2
            ≤ ∑ α ∈ cutoffLabels J ℓ, (if 1 ≤ n1 then cutoffVarpi β ℓ J 1 α else cutoffVarpi β ℓ J 2 α) :=
              Finset.sum_le_sum fun α _ => h2 α
          _ ≤ 1 := by
              by_cases hn1 : 1 ≤ n1
              · simp only [hn1, if_true]; exact ob_cutoffVarpi_sum hβ ℓ J 1
              · simp only [hn1, if_false]; exact ob_cutoffVarpi_sum hβ ℓ J 2
    _ = _ := one_mul _



/-! ### The top-level reduction: marks of a typed tree -/

private lemma pp_typed_even {k : ℕ} (T : TypedOrdTree k) : k % 2 = 0 := by
  have h1 := pd_tt_ty_val T (j := 2 * k) le_rfl
  have h2 := (pd_tt_pinv T).2.1
  rw [h2, T.root_out] at h1
  by_contra h
  have h3 : (2 * k) % 4 ≠ 0 := by omega
  have h4 : ¬ (2 * k) % 2 = 1 := by omega
  rw [if_neg h4, if_neg h3] at h1
  exact absurd h1 (by decide)

/-- The rooted version of a typed ordered tree (as in the retained-pairing bridge). -/
private lemma pp_toRooted_tree {k : ℕ} (T : TypedOrdTree k) : (pd_toRooted T).tree = T.tree := rfl

private lemma pp_toRooted_ty {k : ℕ} (T : TypedOrdTree k) : (pd_toRooted T).ty = T.ty := rfl

open Classical in
private lemma pp_ptSum_marks (K : PtK) {k : ℕ} (T : TypedOrdTree k) (δ : ℕ) (ρ : VType → ℕ → ℂ) :
    ptSum K (pd_toRooted T) δ ρ =
      ∑ a1 ∈ Finset.range (k / 2),
        ∏ w ∈ T.tree.vtxs.toFinset, ptW K (pd_toRooted T) δ ρ
          (T.tree.contour.getD (4 * a1 + 2) [])
          ((T.tree.contour.take (4 * a1 + 2)).count (T.tree.contour.getD (4 * a1 + 2) [])) w := by
  have hev := pp_typed_even T
  obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
  have hlen := pd_tt_len T
  set C := T.tree.contour with hC
  let Φ : List ℕ → ℕ → ℂ := fun v j =>
    ∏ w ∈ T.tree.vtxs.toFinset, ptW K (pd_toRooted T) δ ρ v j w
  -- cover and counts
  have hcnt : ∀ v ∈ T.tree.vtxs, C.count v = T.tree.childCount v + 1 := fun v hv => pp_cnt_full _ v hv
  have hfin : T.tree.vtxs.toFinset = C.toFinset := by
    ext v
    simp only [List.mem_toFinset]
    constructor
    · intro hv
      have := hcnt v hv
      exact List.count_pos_iff.mp (by omega)
    · intro hv
      obtain ⟨s, hs', rfl⟩ := List.getElem_of_mem hv
      have hs'' : s < 2 * (2 * m) + 1 := by rw [← hlen]; exact hs'
      have := pd_tt_mem T (j := s) (by omega)
      rwa [List.getD_eq_getElem _ _ hs'] at this
  let G : List ℕ → ℕ → ℂ := fun v j => if T.ty v = VType.inp then Φ v j else 0
  have hstep1 : ptSum K (pd_toRooted T) δ ρ =
      ∑ v ∈ C.toFinset, ∑ j ∈ Finset.range (C.count v), G v j := by
    unfold ptSum
    rw [Finset.sum_filter, ← hfin]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hv' : v ∈ T.tree.vtxs := List.mem_toFinset.mp hv
    rw [hcnt v hv']
    by_cases hty : T.ty v = VType.inp
    · have hty' : (pd_toRooted T).ty v = VType.inp := hty
      simp only [G, hty, hty', if_true, Φ]
      rfl
    · have hty' : ¬ (pd_toRooted T).ty v = VType.inp := hty
      simp only [G, hty, hty', if_false, Finset.sum_const_zero]
  rw [hstep1, ← pp_sum_corners C G, hlen]
  have hterm : ∀ p ∈ Finset.range (2 * (2 * m) + 1),
      G (C.getD p []) ((C.take p).count (C.getD p [])) =
        if p % 4 = 2 then Φ (C.getD (4 * (p / 4) + 2) []) ((C.take (4 * (p / 4) + 2)).count
          (C.getD (4 * (p / 4) + 2) [])) else 0 := by
    intro p hp
    have hp' := Finset.mem_range.mp hp
    have hty := pd_tt_ty_val T (j := p) (by omega)
    by_cases h2 : p % 4 = 2
    · have : 4 * (p / 4) + 2 = p := by omega
      rw [this, if_pos h2]
      have hi : T.ty (C.getD p []) = VType.inp := by
        rw [hty, if_neg (by omega), if_neg (by omega)]
      simp only [G, hi, if_true]
    · have hni : ¬ T.ty (C.getD p []) = VType.inp := by
        rw [hty]
        by_cases h1 : p % 2 = 1
        · rw [if_pos h1]; decide
        · rw [if_neg h1, if_pos (by omega)]; decide
      simp only [G, hni, h2, if_false]
  rw [Finset.sum_congr rfl hterm]
  have himg : (Finset.range (2 * (2 * m) + 1)).filter (fun p => p % 4 = 2) =
      (Finset.range m).image (fun a => 4 * a + 2) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨p / 4, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨by omega, by omega⟩
  rw [← Finset.sum_filter, himg, Finset.sum_image (fun a _ b _ h => by omega)]
  refine Finset.sum_congr (by congr 1; omega) fun a _ => ?_
  have : 4 * ((4 * a + 2) / 4) + 2 = 4 * a + 2 := by omega
  rw [this]



section TopLevel

variable {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ)
  {m n : ℕ} (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
  (g : ℤ → Ω → ℝ) (s u : ℝ)

/-- The physical pointed-weight parameters. -/
private noncomputable def physK : PtK where
  z1 := zetaT s
  z2 := zetaT u
  cp := fun n1 n2 => ((∑ α ∈ cutoffLabels J ℓ, ∫ ω, cutoffXi β ℓ J R 1 g α ω ^ n1 *
    cutoffXi β ℓ J R 2 g α ω ^ n2 ∂P : ℝ) : ℂ)
  Mf := ob_Mf B μ lam
  Mg := fun d => (((B : ℝ)⁻¹ * ∑ j, lam j ^ d * Gd j : ℝ) : ℂ)

/-- The physical root scalar (with the test `F`). -/
private noncomputable def physRho : VType → ℕ → ℂ := fun τ d =>
  if τ = VType.out then (((B : ℝ)⁻¹ * ∑ i, μ i ^ d * Fd i : ℝ) : ℂ) else 0

open Classical in
private lemma pp_Wr_ext_eq {a b : ℕ} (T : TypedTrees a b) (w : List ℕ) (hext : T.ty w ≠ VType.lat)
    (c : List ℕ) (hc : c = T.tree.contour.getD (2 * (2 * a + 1)) [])
    (o : Option (AsgLab m n (cutoffLabels J ℓ))) :
    pd_Wr P β ℓ J R B Fd Gd μ lam g a b T w o =
      (asgVal μ lam o ^ T.tree.degAt w / (B : ℝ)) *
        (if w = [] then asgVal Fd (fun _ : Fin n => (0 : ℝ)) o else 1) *
        (if w = c then asgVal (fun _ : Fin m => (0 : ℝ)) Gd o else 1) := by
  subst hc
  unfold pd_Wr
  rw [if_pos hext]

open Classical in
/-- The non-`ζ` part of the vertex weight of the pointed tree: the sum of the vertex factor over the
admissible values at the vertex `w`, for the mark at contour time `p`. -/
private lemma pp_vertex_ext {a b : ℕ} (T : TypedTrees a b) (w : List ℕ)
    (hext : T.ty w ≠ VType.lat) (c : List ℕ) (hc : c = T.tree.contour.getD (2 * (2 * a + 1)) [])
    (hv : T.ty c = VType.inp) :
    ∑ o : {o : Option (AsgLab m n (cutoffLabels J ℓ)) // AsgCompat (T.ty w) o},
      ((pd_Wr P β ℓ J R B Fd Gd μ lam g a b T w o.1 : ℝ) : ℂ) =
    if w = c then
      (physK P β ℓ J R B Gd μ lam g s u).Mg (T.tree.degAt w)
    else if w = [] then physRho B Fd μ VType.out (T.tree.degAt w)
    else ob_Mf B μ lam (T.ty w) (T.tree.degAt w) := by
  rw [← Complex.ofReal_sum]
  have hcs := pd_cs_sum (L := cutoffLabels J ℓ) (T.ty w)
    (fun o => pd_Wr P β ℓ J R B Fd Gd μ lam g a b T w o)
  rw [hcs]
  cases hty : T.ty w with
  | out =>
    have hwc : w ≠ c := fun e => by rw [e, hv] at hty; exact absurd hty (by decide)
    simp only [pp_Wr_ext_eq P β ℓ J R B Fd Gd μ lam g T w hext c hc, if_neg hwc, asgVal]
    by_cases h0 : w = []
    · simp only [h0, if_true, physRho, ob_Mf]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    · simp only [h0, if_false, ob_Mf, if_true]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
  | inp =>
    have h0 : w ≠ [] := by
      rintro rfl; rw [T.root_out] at hty; exact absurd hty (by decide)
    by_cases hwc : w = c
    · simp only [pp_Wr_ext_eq P β ℓ J R B Fd Gd μ lam g T w hext c hc, if_pos hwc, asgVal, physK,
        h0, if_false]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · simp only [pp_Wr_ext_eq P β ℓ J R B Fd Gd μ lam g T w hext c hc, if_neg hwc, asgVal, ob_Mf, h0]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
  | lat => exact absurd hty hext

end TopLevel



private lemma pp_cnt_range {β' : Type} [BEq β'] [LawfulBEq β'] [DecidableEq β'] (L : List β') (x d : β') (p : ℕ)
    (hp : p ≤ L.length) :
    (L.take p).count x = ((Finset.range p).filter (fun τ => L.getD τ d = x)).card := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hp' : p < L.length := hp
    have hg : L[p]? = some (L.getD p d) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp']; rfl
    have e : L.take (p + 1) = L.take p ++ [L.getD p d] := by
      rw [List.take_succ, hg]; rfl
    rw [e, List.count_append, ih hp'.le, Finset.range_add_one, Finset.filter_insert]
    by_cases h : L.getD p d = x
    · have c1 : [L.getD p d].count x = 1 := by rw [h]; exact List.count_singleton_self
      rw [if_pos h, Finset.card_insert_of_notMem (by simp), c1]
    · have c0 : [L.getD p d].count x = 0 := List.count_eq_zero.mpr (by simpa [eq_comm] using h)
      rw [if_neg h, c0, add_zero]



section TopLevel2

variable {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ)
  {m n : ℕ} (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
  (g : ℤ → Ω → ℝ) (s u : ℝ)

open Classical in
private lemma pp_vertex_lat {a b : ℕ} (T : TypedTrees a b) (w : List ℕ) (hw : w ∈ T.tree.vtxs)
    (hlat : T.ty w = VType.lat) :
    ∑ o : {o : Option (AsgLab m n (cutoffLabels J ℓ)) // AsgCompat (T.ty w) o},
      ((pd_Wr P β ℓ J R B Fd Gd μ lam g a b T w o.1 : ℝ) : ℂ) =
    (physK P β ℓ J R B Gd μ lam g s u).cp ((T.tree.contour.take (2 * (2 * a + 1))).count w)
      (T.tree.childCount w + 1 - (T.tree.contour.take (2 * (2 * a + 1))).count w) := by
  rw [← Complex.ofReal_sum]
  have hcs := pd_cs_sum (L := cutoffLabels J ℓ) (T.ty w)
    (fun o => pd_Wr P β ℓ J R B Fd Gd μ lam g a b T w o)
  rw [hcs]
  simp only [hlat]
  set C := T.tree.contour with hC
  set p0 := 2 * (2 * a + 1) with hp0
  have hk : treeK a b = 2 * a + 2 * b + 2 := rfl
  have hlen : C.length = 2 * treeK a b + 1 := pd_tt_len T
  have hp0k : p0 ≤ 2 * treeK a b := by rw [hp0, hk]; omega
  have hw0 : w ≠ [] := by rintro rfl; rw [T.root_out] at hlat; exact absurd hlat (by decide)
  set S := (Finset.range (2 * treeK a b)).filter (fun τ => τ % 2 = 1 ∧ C.getD τ [] = w) with hS
  have hSc : ∀ τ, τ ≤ 2 * treeK a b → C.getD τ [] = w → τ % 2 = 1 := by
    intro τ hτ hcw
    exact (pd_tt_lat T (j := τ) hτ).mp (by rw [hcw]; exact hlat)
  have hn1 : (C.take p0).count w = (S.filter (fun τ => τ < p0)).card := by
    rw [pp_cnt_range C w [] p0 (by omega)]
    congr 1
    ext τ
    simp only [hS, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by omega, hSc τ (by omega) h2, h2⟩, h1⟩
    · rintro ⟨⟨_, _, h3⟩, h4⟩
      exact ⟨h4, h3⟩
  have hSc2 : S.card = T.tree.childCount w + 1 := by
    rw [← pp_cnt_full T.tree w hw]
    have h1 : C.count w = ((Finset.range (2 * treeK a b + 1)).filter (fun τ => C.getD τ [] = w)).card := by
      have := pp_cnt_range C w [] C.length le_rfl
      rw [List.take_length, hlen] at this
      exact this
    rw [h1, Finset.range_add_one, Finset.filter_insert]
    have hlast : C.getD (2 * treeK a b) [] = [] := (pd_tt_pinv T).2.1
    rw [if_neg (by rw [hlast]; exact fun e => hw0 e.symm)]
    congr 1
    ext τ
    simp only [hS, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, _, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨h1, hSc τ (by omega) h3, h3⟩
  have hn2 : (S.filter (fun τ => ¬ τ < p0)).card = T.tree.childCount w + 1 - (C.take p0).count w := by
    have := Finset.card_filter_add_card_filter_not (s := S) (fun τ => τ < p0)
    rw [hn1]; omega
  -- the label sum
  have hG : ∀ α : {α : ℤ // α ∈ cutoffLabels J ℓ},
      pd_Wr P β ℓ J R B Fd Gd μ lam g a b T w (some (Sum.inr (Sum.inr α))) =
      ∫ ω, cutoffXi β ℓ J R 1 g α.1 ω ^ ((C.take p0).count w) *
        cutoffXi β ℓ J R 2 g α.1 ω ^ (T.tree.childCount w + 1 - (C.take p0).count w) ∂P := by
    intro α
    unfold pd_Wr
    rw [if_neg (by simp [hlat])]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have hpt : ∀ τ ∈ S, cutoffXi β ℓ J R (cornerLabel a τ) g α.1 ω =
        if τ < p0 then cutoffXi β ℓ J R 1 g α.1 ω else cutoffXi β ℓ J R 2 g α.1 ω := by
      intro τ _
      simp only [cornerLabel, hp0]
      split_ifs <;> rfl
    show ∏ τ ∈ S, cutoffXi β ℓ J R (cornerLabel a τ) g α.1 ω = _
    rw [Finset.prod_congr rfl hpt, Finset.prod_ite, Finset.prod_const, Finset.prod_const, hn2, ← hn1]
  rw [Finset.sum_congr rfl (fun α _ => hG α)]
  rw [Finset.sum_coe_sort (cutoffLabels J ℓ) (fun α : ℤ => ∫ ω, cutoffXi β ℓ J R 1 g α ω ^ ((C.take p0).count w) *
        cutoffXi β ℓ J R 2 g α ω ^ (T.tree.childCount w + 1 - (C.take p0).count w) ∂P)]
  rfl

end TopLevel2



private lemma pp_card_even (n : ℕ) :
    ((Finset.range n).filter (fun τ => τ % 2 = 0)).card = (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases h : n % 2 = 0
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp), ih]; omega
    · rw [if_neg h, ih]; omega

open Classical in
/-- The number of visits to external vertices before the mark. -/
private lemma pp_ext_before {k : ℕ} (T : TypedOrdTree k) (p : ℕ) (hp : p ≤ 2 * k + 1) :
    ∑ w ∈ T.tree.vtxs.toFinset.filter (fun w => T.ty w ≠ VType.lat),
      (T.tree.contour.take p).count w = (p + 1) / 2 := by
  set C := T.tree.contour with hC
  have hlen : C.length = 2 * k + 1 := pd_tt_len T
  have hcard : ((Finset.range p).filter (fun τ => T.ty (C.getD τ []) ≠ VType.lat)).card = (p + 1) / 2 := by
    rw [← pp_card_even p]
    congr 1
    ext τ
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      by_contra h
      exact h2 ((pd_tt_lat T (j := τ) (by omega)).mpr (by omega))
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun h => ?_⟩
      have := (pd_tt_lat T (j := τ) (by omega)).mp h
      omega
  rw [← hcard, Finset.card_eq_sum_card_fiberwise (f := fun τ => C.getD τ [])
    (t := T.tree.vtxs.toFinset.filter (fun w => T.ty w ≠ VType.lat))]
  · refine Finset.sum_congr rfl fun w hw => ?_
    have hw' := Finset.mem_filter.mp hw
    rw [pp_cnt_range C w [] p (by omega)]
    congr 1
    ext τ
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, by rw [h2]; exact (Finset.mem_filter.mp hw).2⟩, h2⟩
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, h2⟩
  · intro τ hτ
    have hτ' := Finset.mem_filter.mp (Finset.mem_coe.mp hτ)
    have hlt := Finset.mem_range.mp hτ'.1
    simp only [Finset.mem_coe, Finset.mem_filter, List.mem_toFinset]
    exact ⟨pd_tt_mem T (by omega), hτ'.2⟩

open Classical in
private lemma pp_ext_total {τ : VType} {k : ℕ} (Y : RootedTypedTree τ k) :
    ∑ w ∈ Y.tree.vtxs.toFinset.filter (fun w => Y.ty w ≠ VType.lat), (Y.tree.childCount w + 1) = k + 1 := by
  obtain ⟨hs1, -, -, -⟩ := ob_deg_sums Y
  have hroot : ([] : List ℕ) ∈ Y.tree.vtxs.toFinset.filter (fun w => Y.ty w ≠ VType.lat) := by
    simp only [Finset.mem_filter, List.mem_toFinset]
    exact ⟨ob_pt_root_mem _, by rw [Y.root_ty]; exact Y.root_ext⟩
  have : ∀ w ∈ Y.tree.vtxs.toFinset.filter (fun w => Y.ty w ≠ VType.lat),
      Y.tree.childCount w + 1 = Y.tree.degAt w + (if w = [] then 1 else 0) := by
    intro w _
    by_cases h0 : w = []
    · subst h0; simp [pp_degAt_root]
    · simp [h0, pp_degAt_ne h0]
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, hs1]
  simp [Finset.sum_ite_eq', hroot]



section TopLevel3

variable {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ)
  {m n : ℕ} (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
  (g : ℤ → Ω → ℝ) (s u : ℝ)

open Classical in
private lemma pp_tree_term {a b : ℕ} (T : TypedTrees a b) :
    ∑' x : TreeAsg T.tree T.ty m n (cutoffLabels J ℓ),
      pathTerm P β ℓ J R B Fd Gd μ lam g s u ⟨(a, b), ⟨T, x⟩⟩ =
    ∏ w ∈ T.tree.vtxs.toFinset, ptW (physK P β ℓ J R B Gd μ lam g s u) (pd_toRooted T) 0
      (physRho B Fd μ) (T.tree.contour.getD (4 * a + 2) [])
      ((T.tree.contour.take (4 * a + 2)).count (T.tree.contour.getD (4 * a + 2) [])) w := by
  set C := T.tree.contour with hC
  have hp0 : 4 * a + 2 = 2 * (2 * a + 1) := by ring
  rw [hp0]
  set p0 := 2 * (2 * a + 1) with hp0'
  have hk : treeK a b = 2 * a + 2 * b + 2 := rfl
  have hlen : C.length = 2 * treeK a b + 1 := pd_tt_len T
  have hp0k : p0 ≤ 2 * treeK a b := by rw [hp0', hk]; omega
  set v := C.getD p0 [] with hv
  set j := (C.take p0).count v with hj
  have hvmem : v ∈ T.tree.vtxs := pd_tt_mem T hp0k
  have hvty : T.ty v = VType.inp := by
    rw [hv, pd_tt_ty_val T hp0k, if_neg (by omega), if_neg (by omega)]
  have hlen2 : T.tree.contour.length = 2 * treeK a b + 1 := pd_tt_len T
  have hcnt : ∀ w ∈ T.tree.vtxs, (C.take p0).count w =
      pp_nbC (T.tree.childCount w + 1) w v j := fun w hw =>
    pp_nl_main T.tree p0 (by omega) w hw
  -- step 1: the asgmt sum
  have h1 : ∑' x : TreeAsg T.tree T.ty m n (cutoffLabels J ℓ),
      pathTerm P β ℓ J R B Fd Gd μ lam g s u ⟨(a, b), ⟨T, x⟩⟩ =
      pathZ s u (a, b) * ∑' x : TreeAsg T.tree T.ty m n (cutoffLabels J ℓ),
        pathVal P β ℓ J R B Fd Gd μ lam g (a, b) T x := by
    rw [← tsum_mul_left]; rfl
  rw [h1, pd_val_sum P β ℓ J R B Fd Gd μ lam g a b T]
  have hZ : pathZ s u (a, b) = zetaT s ^ (2 * a + 2) * zetaT u ^ (2 * b + 2) := by
    rw [pathZ, pd_arcEven_left, pd_arcEven_right]
  rw [hZ, Finset.prod_coe_sort T.tree.vtxs.toFinset
    (fun w => ∑ o : {o : Option (AsgLab m n (cutoffLabels J ℓ)) // AsgCompat (T.ty w) o},
      ((pd_Wr P β ℓ J R B Fd Gd μ lam g a b T w o.1 : ℝ) : ℂ))]
  have hcc_le : ∀ w ∈ T.tree.vtxs, (C.take p0).count w ≤ T.tree.childCount w + 1 := by
    intro w hw
    rw [← pp_cnt_full T.tree w hw]
    exact (List.take_sublist _ _).count_le _
  let sc : List ℕ → ℂ := fun w =>
    if T.ty w = VType.lat then
      (physK P β ℓ J R B Gd μ lam g s u).cp ((C.take p0).count w)
        (T.tree.childCount w + 1 - (C.take p0).count w)
    else if w = v then (physK P β ℓ J R B Gd μ lam g s u).Mg (T.tree.degAt w)
    else if w = [] then physRho B Fd μ VType.out (T.tree.degAt w)
    else ob_Mf B μ lam (T.ty w) (T.tree.degAt w)
  let zf : List ℕ → ℂ := fun w =>
    if T.ty w = VType.lat then 1
    else zetaT s ^ ((C.take p0).count w + (if w = v then 1 else 0)) *
      zetaT u ^ (T.tree.childCount w + 1 - (C.take p0).count w)
  have hsc : ∀ w ∈ T.tree.vtxs.toFinset,
      ∑ o : {o : Option (AsgLab m n (cutoffLabels J ℓ)) // AsgCompat (T.ty w) o},
        ((pd_Wr P β ℓ J R B Fd Gd μ lam g a b T w o.1 : ℝ) : ℂ) = sc w := by
    intro w hw
    have hw' := List.mem_toFinset.mp hw
    by_cases hl : T.ty w = VType.lat
    · simp only [sc, hl, if_true]
      exact pp_vertex_lat P β ℓ J R B Fd Gd μ lam g s u T w hw' hl
    · simp only [sc, hl, if_false]
      exact pp_vertex_ext P β ℓ J R B Fd Gd μ lam g s u T w hl v hv hvty
  have hptw : ∀ w ∈ T.tree.vtxs.toFinset,
      ptW (physK P β ℓ J R B Gd μ lam g s u) (pd_toRooted T) 0 (physRho B Fd μ) v j w = zf w * sc w := by
    intro w hw
    have hw' := List.mem_toFinset.mp hw
    have hnb := (hcnt w hw').symm
    unfold ptW
    simp only [pp_toRooted_tree, pp_toRooted_ty]
    rw [hnb]
    by_cases hl : T.ty w = VType.lat
    · simp only [zf, sc, hl, if_true, one_mul]
    · by_cases hwv : w = v
      · have hvl : ¬ T.ty v = VType.lat := by rw [hvty]; decide
        simp only [zf, sc, hl, if_false, hwv, if_true, physK, hvl]
        simp
      · by_cases h0 : w = []
        · subst h0
          simp only [zf, sc, hl, if_false, hwv, if_true, physK, T.root_out, add_zero]
          simp
        · simp only [zf, sc, hl, if_false, hwv, h0, physK, add_zero]
  rw [Finset.prod_congr rfl hsc, Finset.prod_congr rfl hptw, Finset.prod_mul_distrib]
  congr 1
  have hzf : ∏ w ∈ T.tree.vtxs.toFinset, zf w =
      ∏ w ∈ T.tree.vtxs.toFinset.filter (fun w => T.ty w ≠ VType.lat),
        (zetaT s ^ ((C.take p0).count w + (if w = v then 1 else 0)) *
          zetaT u ^ (T.tree.childCount w + 1 - (C.take p0).count w)) := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun w _ => ?_
    simp only [zf]
    by_cases hl : T.ty w = VType.lat <;> simp [hl]
  rw [hzf, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
    Finset.sum_add_distrib]
  have e1 := pp_ext_before T p0 (by omega)
  have hvext : v ∈ T.tree.vtxs.toFinset.filter (fun w => T.ty w ≠ VType.lat) := by
    simp only [Finset.mem_filter, List.mem_toFinset]
    exact ⟨hvmem, by rw [hvty]; decide⟩
  have e2 : ∑ w ∈ T.tree.vtxs.toFinset.filter (fun w => T.ty w ≠ VType.lat),
      (if w = v then 1 else 0) = 1 := by
    simp [Finset.sum_ite_eq', hvext]
  have e3 := pp_ext_total (pd_toRooted T)
  have e4 : ∑ w ∈ T.tree.vtxs.toFinset.filter (fun w => T.ty w ≠ VType.lat),
      (T.tree.childCount w + 1 - (C.take p0).count w) = 2 * b + 2 := by
    rw [Finset.sum_tsub_distrib _ (fun w hw => hcc_le w
      (List.mem_toFinset.mp (Finset.mem_filter.mp hw).1))]
    have e3' : ∑ w ∈ T.tree.vtxs.toFinset.filter (fun w => T.ty w ≠ VType.lat),
        (T.tree.childCount w + 1) = treeK a b + 1 := e3
    rw [e3', e1, hk]; omega
  rw [e2, e4]
  have : (∑ w ∈ T.tree.vtxs.toFinset.filter (fun w => T.ty w ≠ VType.lat),
      (C.take p0).count w) + 1 = 2 * a + 2 := by rw [e1]; omega
  rw [this]

end TopLevel3



section TopLevel4

variable {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ)
  {m n : ℕ} (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
  (g : ℤ → Ω → ℝ) (s u : ℝ)

/-- The weight of the mark at contour time `4 a₁ + 2` of a typed tree. -/
private noncomputable def Fterm (K : PtK) (ρ : VType → ℕ → ℂ) {k : ℕ} (T : TypedOrdTree k) (a1 : ℕ) : ℂ :=
  ∏ w ∈ T.tree.vtxs.toFinset, ptW K (pd_toRooted T) 0 ρ (T.tree.contour.getD (4 * a1 + 2) [])
    ((T.tree.contour.take (4 * a1 + 2)).count (T.tree.contour.getD (4 * a1 + 2) [])) w

private lemma pp_fcast (K : PtK) (ρ : VType → ℕ → ℂ) (a b : ℕ) (k : ℕ) (h : treeK a b = k) (a1 : ℕ) :
    ∑' T : TypedTrees a b, Fterm K ρ T a1 = ∑' T : TypedOrdTree k, Fterm K ρ T a1 := by
  subst h; rfl

/-- The equivalence between typed ordered trees and rooted typed trees with root type `out`. -/
private noncomputable def pp_toRootedEquiv (k : ℕ) : TypedOrdTree k ≃ RootedTypedTree VType.out k :=
  Equiv.ofBijective pd_toRooted (by
    constructor
    · intro T T' h
      have h1 : T.tree = T'.tree := congrArg RootedTypedTree.tree h
      have h2 : T.ty = T'.ty := congrArg RootedTypedTree.ty h
      cases T; cases T'
      simp only at h1 h2
      subst h1; subst h2; rfl
    · intro X
      refine ⟨ob_toOrd X, ?_⟩
      have h1 : (pd_toRooted (ob_toOrd X)).tree = X.tree := rfl
      have h2 : (pd_toRooted (ob_toOrd X)).ty = X.ty := by
        funext w
        change (if w ∈ X.tree.vtxs then ob_fT VType.out (X.ty w) else VType.out) = X.ty w
        by_cases hw : w ∈ X.tree.vtxs
        · simp [hw, ob_fT]
        · simp [hw, X.off_support w hw]
      exact ob_rooted_ext _ _ h1 (fun w _ => congrFun h2 w))

private lemma pp_typed_empty {k : ℕ} (hk : k % 2 = 1) : IsEmpty (TypedOrdTree k) :=
  ⟨fun T => by have := pp_typed_even T; omega⟩

open Classical in
private lemma pp_top_reduction
    (hsum : Summable (fun q : PathIdx m n J ℓ => ‖pathTerm P β ℓ J R B Fd Gd μ lam g s u q‖))
    (hPsum : Summable (fun Y : OE VType.out =>
      ‖ptSum (physK P β ℓ J R B Gd μ lam g s u) Y.2 0 (physRho B Fd μ)‖)) :
    ∑' q : PathIdx m n J ℓ, pathTerm P β ℓ J R B Fd Gd μ lam g s u q =
      ∑' Y : OE VType.out, ptSum (physK P β ℓ J R B Gd μ lam g s u) Y.2 0 (physRho B Fd μ) := by
  set K := physK P β ℓ J R B Gd μ lam g s u with hK
  set ρ := physRho B Fd μ with hρ
  haveI hfinT : ∀ k : ℕ, Finite (TypedOrdTree k) := fun k => (typedOrdTree_card_le k).1
  have hfinY : ∀ p : ℕ × ℕ, Finite (Σ T : TypedTrees p.1 p.2,
      TreeAsg T.tree T.ty m n (cutoffLabels J ℓ)) := by
    intro p
    haveI := hfinT (treeK p.1 p.2)
    haveI : ∀ T : TypedTrees p.1 p.2, Finite (TreeAsg T.tree T.ty m n (cutoffLabels J ℓ)) :=
      fun T => ob_finite_asg _ _ _ _ _
    infer_instance
  have hpt := hsum.of_norm
  -- the left side as a sum over `p`
  let f : ℕ × ℕ → ℂ := fun p => ∑' T : TypedTrees p.1 p.2, Fterm K ρ T p.1
  have hfib : ∀ p : ℕ × ℕ, ∑' y : (Σ T : TypedTrees p.1 p.2,
      TreeAsg T.tree T.ty m n (cutoffLabels J ℓ)), pathTerm P β ℓ J R B Fd Gd μ lam g s u ⟨p, y⟩ =
      f p := by
    rintro ⟨a, b⟩
    haveI := hfinT (treeK a b)
    haveI : ∀ T : TypedTrees a b, Finite (TreeAsg T.tree T.ty m n (cutoffLabels J ℓ)) :=
      fun T => ob_finite_asg _ _ _ _ _
    rw [Summable.tsum_sigma' (fun T => Summable.of_finite) Summable.of_finite]
    exact tsum_congr fun T => pp_tree_term P β ℓ J R B Fd Gd μ lam g s u T
  rw [Summable.tsum_sigma' (fun p => by haveI := hfinY p; exact Summable.of_finite) hpt]
  simp_rw [hfib]
  have hfnorm : Summable (fun p : ℕ × ℕ => ‖f p‖) := by
    have h1 : Summable (fun p : ℕ × ℕ => ∑' y : (Σ T : TypedTrees p.1 p.2,
        TreeAsg T.tree T.ty m n (cutoffLabels J ℓ)), ‖pathTerm P β ℓ J R B Fd Gd μ lam g s u ⟨p, y⟩‖) :=
      hsum.sigma' (fun p => by haveI := hfinY p; exact Summable.of_finite)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) h1
    rw [← hfib p]
    haveI := hfinY p
    exact norm_tsum_le_tsum_norm Summable.of_finite
  -- the right side as a sum over `k`
  have hfinR : ∀ k : ℕ, Finite (RootedTypedTree VType.out k) := fun k => (ob_card_rooted VType.out k).1
  rw [Summable.tsum_sigma' (fun k => by haveI := hfinR k; exact Summable.of_finite) hPsum.of_norm]
  let G : ℕ → ℂ := fun k => ∑' T : TypedOrdTree k, ptSum K (pd_toRooted T) 0 ρ
  have hG : ∀ k : ℕ, ∑' X : RootedTypedTree VType.out k, ptSum K X 0 ρ = G k := by
    intro k
    exact (Equiv.tsum_eq (pp_toRootedEquiv k) (fun X : RootedTypedTree VType.out k => ptSum K X 0 ρ)).symm
  show ∑' p : ℕ × ℕ, f p = ∑' k : ℕ, ∑' X : RootedTypedTree VType.out k, ptSum K X 0 ρ
  simp_rw [hG]
  have hGeven : ∀ m' : ℕ, G (2 * m') = ∑ a1 ∈ Finset.range m', ∑' T : TypedOrdTree (2 * m'), Fterm K ρ T a1 := by
    intro m'
    simp only [G]
    have : ∀ T : TypedOrdTree (2 * m'), ptSum K (pd_toRooted T) 0 ρ =
        ∑ a1 ∈ Finset.range m', Fterm K ρ T a1 := by
      intro T
      rw [pp_ptSum_marks K T 0 ρ, show 2 * m' / 2 = m' by omega]
      rfl
    simp_rw [this]
    rw [Summable.tsum_finsetSum (fun a1 _ => Summable.of_finite)]
  have hGodd : ∀ k : ℕ, k % 2 = 1 → G k = 0 := by
    intro k hk
    haveI := pp_typed_empty hk
    simp [G]
  have hGs : Summable G := by
    have := hPsum.of_norm.sigma' (fun k => by haveI := hfinR k; exact Summable.of_finite)
    simp_rw [hG] at this
    exact this
  have hinj : Function.Injective (fun m' : ℕ => 2 * m') := fun a b h => by simpa using h
  have hsupp : Function.support G ⊆ Set.range (fun m' : ℕ => 2 * m') := by
    intro k hk
    by_cases h : k % 2 = 1
    · exact absurd (hGodd k h) hk
    · exact ⟨k / 2, by simp only; omega⟩
  rw [← hinj.tsum_eq hsupp]
  have hGs2 : Summable (fun m' : ℕ => G (2 * m')) := hGs.comp_injective hinj
  rw [hGs2.tsum_eq_zero_add]
  have hG0 : G (2 * 0) = 0 := by rw [hGeven 0]; simp
  have hG1 : ∀ n' : ℕ, G (2 * (n' + 1)) = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n', f x := by
    intro n'
    rw [hGeven (n' + 1), Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun a1 ha1 => ?_
    have ha1' := Finset.mem_range.mp ha1
    rw [← pp_fcast K ρ a1 (n' - a1) (2 * (n' + 1)) (by unfold treeK; omega) a1]
  simp only [hG0, zero_add, hG1]
  exact ((pp_antidiag f hfnorm).2).symm

end TopLevel4



/-! ### The abstract solution of the path equations -/

private noncomputable def ptA1 (K : PtK) (τ : VType) : ℂ := ∑' b : OBlk τ, ptBw K.z1 K.cdf1 K b
private noncomputable def ptA2 (K : PtK) (τ : VType) : ℂ := ∑' b : OBlk τ, ptBw K.z2 K.cdf2 K b
private noncomputable def ptWm (K : PtK) (τ : VType) : ℂ := ∑' b : OBlk τ, ptBm K b
private noncomputable def ptBs (K : PtK) : ℂ := ∑' x : ℕ × ℕ, ptGB K VType.out x.1 x.2
private noncomputable def ptEs (K : PtK) : ℂ := ∑' x : ℕ × ℕ, ptGE K VType.out x.1 x.2
private noncomputable def ptDen (K : PtK) (τ : VType) (κ : ℂ) : ℂ :=
  (1 - κ * ptA1 K τ) * (1 - κ * ptA2 K τ)

/-- `ptA` and `ptWm` are the sums that occur in `pt_tsum`; the abstract solution. -/
private lemma pt_abstract (K : PtK) {ι1 ι2 : Type} [Fintype ι1] [Fintype ι2]
    (cF cM1 κ1 : ι1 → ℂ) (cM2 cG κ2 : ι2 → ℂ) (ρ : VType → ℕ → ℂ)
    (hρ : ∀ d, ρ VType.out d = ∑ i, cF i * κ1 i ^ d)
    (hMfo : ∀ d, K.Mf VType.out d = ∑ i, cM1 i * κ1 i ^ d)
    (hMfi : ∀ d, K.Mf VType.inp d = ∑ j, cM2 j * κ2 j ^ d)
    (hMg : ∀ d, K.Mg d = ∑ j, cG j * κ2 j ^ d)
    (h1o : Summable (fun b : OBlk VType.out => ‖ptBw K.z1 K.cdf1 K b‖))
    (h2o : Summable (fun b : OBlk VType.out => ‖ptBw K.z2 K.cdf2 K b‖))
    (h1i : Summable (fun b : OBlk VType.inp => ‖ptBw K.z1 K.cdf1 K b‖))
    (h2i : Summable (fun b : OBlk VType.inp => ‖ptBw K.z2 K.cdf2 K b‖))
    (hmo : Summable (fun b : OBlk VType.out => ‖ptBm K b‖))
    (hmi : Summable (fun b : OBlk VType.inp => ‖ptBm K b‖))
    (so1 : ∀ i, ‖κ1 i‖ * ∑' b : OBlk VType.out, ‖ptBw K.z1 K.cdf1 K b‖ < 1)
    (so2 : ∀ i, ‖κ1 i‖ * ∑' b : OBlk VType.out, ‖ptBw K.z2 K.cdf2 K b‖ < 1)
    (si1 : ∀ i, ‖κ1 i‖ * ∑' b : OBlk VType.inp, ‖ptBw K.z1 K.cdf1 K b‖ < 1)
    (si2 : ∀ i, ‖κ1 i‖ * ∑' b : OBlk VType.inp, ‖ptBw K.z2 K.cdf2 K b‖ < 1)
    (to1 : ∀ j, ‖κ2 j‖ * ∑' b : OBlk VType.out, ‖ptBw K.z1 K.cdf1 K b‖ < 1)
    (to2 : ∀ j, ‖κ2 j‖ * ∑' b : OBlk VType.out, ‖ptBw K.z2 K.cdf2 K b‖ < 1)
    (ti1 : ∀ j, ‖κ2 j‖ * ∑' b : OBlk VType.inp, ‖ptBw K.z1 K.cdf1 K b‖ < 1)
    (ti2 : ∀ j, ‖κ2 j‖ * ∑' b : OBlk VType.inp, ‖ptBw K.z2 K.cdf2 K b‖ < 1)
    (hWmo : ptWm K VType.out = K.z2 * (ptP K VType.inp * ptBs K +
      ptM1 K VType.inp * ptM2 K VType.inp * ptP K VType.out * ptEs K))
    (hWmi : ptWm K VType.inp = K.z2 * (ptP K VType.out * ptBs K +
      ptM1 K VType.out * ptM2 K VType.out * ptP K VType.inp * ptEs K))
    (po pin fo fin : ℂ)
    (hpo : po = K.z2 * (K.z1 * ∑ i, cM1 i * (κ1 i ^ 2 / ptDen K VType.out (κ1 i))))
    (hpin : pin = K.z2 * (K.z1 * ∑ j, cM2 j * (κ2 j ^ 2 / ptDen K VType.inp (κ2 j))))
    (hfo : fo = K.z2 * (K.z1 * ∑ i, cF i * (κ1 i / ptDen K VType.out (κ1 i))))
    (hfin : fin = K.z1 * K.z2 * ∑ j, cG j * (κ2 j / ptDen K VType.inp (κ2 j)))
    (hΔ : (1 - po * (ptM1 K VType.inp * ptM2 K VType.inp * ptEs K)) *
        (1 - pin * (ptM1 K VType.out * ptM2 K VType.out * ptEs K)) - po * pin * ptBs K ^ 2 ≠ 0) :
    ∑' Y : OE VType.out, ptSum K Y.2 0 ρ = fo * fin * ptBs K /
      ((1 - po * (ptM1 K VType.inp * ptM2 K VType.inp * ptEs K)) *
        (1 - pin * (ptM1 K VType.out * ptM2 K VType.out * ptEs K)) - po * pin * ptBs K ^ 2) := by
  have hout : (VType.out : VType) ≠ VType.lat := by decide
  have hinp : (VType.inp : VType) ≠ VType.lat := by decide
  -- the three tsum evaluations
  have eT := pt_tsum K VType.out hout 0 ρ cF κ1 hρ cG κ2 hMg h1o h2o hmo so1 so2 to1 to2
  have eP := pt_tsum K VType.out hout 1 K.Mf cM1 κ1 hMfo cG κ2 hMg h1o h2o hmo so1 so2 to1 to2
  have eQ := pt_tsum K VType.inp hinp 1 K.Mf cM2 κ2 hMfi cG κ2 hMg h1i h2i hmi ti1 ti2 ti1 ti2
  simp only [if_neg (show ¬ (VType.out = VType.inp) by decide), zero_add] at eT eP
  simp only [if_true] at eQ
  simp only [ptA1, ptA2, ptWm, ptDen] at hpo hpin hfo hfin hWmo hWmi
  have eT' : ∑' Y : OE VType.out, ptSum K Y.2 0 ρ = (∑' b : OBlk VType.out, ptBm K b) *
      (K.z1 * ∑ i, cF i * (κ1 i / ((1 - κ1 i * ∑' b : OBlk VType.out, ptBw K.z1 K.cdf1 K b) *
        (1 - κ1 i * ∑' b : OBlk VType.out, ptBw K.z2 K.cdf2 K b)))) := by
    rw [eT, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [pow_zero]; ring
  have eP' : ptP K VType.out = (∑' b : OBlk VType.out, ptBm K b) *
      (K.z1 * ∑ i, cM1 i * (κ1 i ^ 2 / ((1 - κ1 i * ∑' b : OBlk VType.out, ptBw K.z1 K.cdf1 K b) *
        (1 - κ1 i * ∑' b : OBlk VType.out, ptBw K.z2 K.cdf2 K b)))) := by
    unfold ptP
    rw [eP, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [pow_one]; ring
  have eQ' : ptP K VType.inp = K.z1 * K.z2 * ∑ j, cG j * (κ2 j /
        ((1 - κ2 j * ∑' b : OBlk VType.inp, ptBw K.z1 K.cdf1 K b) *
          (1 - κ2 j * ∑' b : OBlk VType.inp, ptBw K.z2 K.cdf2 K b))) +
      (∑' b : OBlk VType.inp, ptBm K b) * (K.z1 * ∑ j, cM2 j * (κ2 j ^ 2 /
        ((1 - κ2 j * ∑' b : OBlk VType.inp, ptBw K.z1 K.cdf1 K b) *
          (1 - κ2 j * ∑' b : OBlk VType.inp, ptBw K.z2 K.cdf2 K b)))) := by
    unfold ptP
    rw [eQ]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [pow_one]; ring
    · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [pow_one]; ring
  subst hpo hpin hfo hfin
  set Po := ptP K VType.out with hPo
  set Pin := ptP K VType.inp with hPin
  set Wo := ∑' b : OBlk VType.out, ptBm K b with hWo
  set Wi := ∑' b : OBlk VType.inp, ptBm K b with hWi
  set Sf := K.z1 * ∑ i, cF i * (κ1 i / ((1 - κ1 i * ∑' b : OBlk VType.out, ptBw K.z1 K.cdf1 K b) *
        (1 - κ1 i * ∑' b : OBlk VType.out, ptBw K.z2 K.cdf2 K b))) with hSf
  set So := K.z1 * ∑ i, cM1 i * (κ1 i ^ 2 / ((1 - κ1 i * ∑' b : OBlk VType.out, ptBw K.z1 K.cdf1 K b) *
        (1 - κ1 i * ∑' b : OBlk VType.out, ptBw K.z2 K.cdf2 K b))) with hSo
  set Si := K.z1 * ∑ j, cM2 j * (κ2 j ^ 2 /
        ((1 - κ2 j * ∑' b : OBlk VType.inp, ptBw K.z1 K.cdf1 K b) *
          (1 - κ2 j * ∑' b : OBlk VType.inp, ptBw K.z2 K.cdf2 K b))) with hSi
  refine pp_solve _ _ _ _ _ _ _ Po Pin _ ?_ ?_ ?_ hΔ
  · linear_combination eP' + So * hWmo
  · linear_combination eQ' + Si * hWmi
  · linear_combination eT' + Sf * hWmo


private lemma pp_ext_sum_w {N B : ℕ} (v w : Fin N → ℝ) (γ C W : ℝ) (hγ : 1 ≤ γ) (hC : 1 ≤ C)
    (hW : 0 ≤ W) (hv : ∀ i, |v i| ≤ C) (hw : ∀ i, |w i| ≤ W) (hN : (N : ℝ) ≤ γ * B) (p : ℕ) :
    ∑ i, |v i ^ p * w i / (B : ℝ)| ≤ W * (γ * C ^ p) := by
  calc ∑ i, |v i ^ p * w i / (B : ℝ)| ≤ ∑ i, W * |v i ^ p / (B : ℝ)| := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [mul_div_right_comm, abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hw i) (abs_nonneg _)
    _ = W * ∑ i, |v i ^ p / (B : ℝ)| := by rw [Finset.mul_sum]
    _ ≤ W * (γ * C ^ p) := mul_le_mul_of_nonneg_left (ob_ext_sum v γ C hγ hC hv hN p) hW

private lemma pp_Mf_bound {m n B : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (γ C : ℝ) (hγ : 1 ≤ γ)
    (hC : 1 ≤ C) (hμ : ∀ i, |μ i| ≤ C) (hlam : ∀ j, |lam j| ≤ C) (hm : (m : ℝ) ≤ γ * B)
    (hn : (n : ℝ) ≤ γ * B) (σ : VType) (hσ : σ ≠ VType.lat) (d : ℕ) :
    ‖ob_Mf B μ lam σ d‖ ≤ γ * C ^ d := by
  cases σ with
  | out =>
    unfold ob_Mf
    rw [if_pos rfl, Complex.norm_real, Real.norm_eq_abs]
    refine le_trans ?_ (ob_ext_sum μ γ C hγ hC hμ hm d)
    simp only [inv_mul_eq_div]
    rw [show (∑ i, μ i ^ d) / (B : ℝ) = ∑ i, μ i ^ d / (B : ℝ) by rw [Finset.sum_div]]
    exact Finset.abs_sum_le_sum_abs _ _
  | inp =>
    unfold ob_Mf
    rw [if_neg (by decide), Complex.norm_real, Real.norm_eq_abs]
    refine le_trans ?_ (ob_ext_sum lam γ C hγ hC hlam hn d)
    simp only [inv_mul_eq_div]
    rw [show (∑ j, lam j ^ d) / (B : ℝ) = ∑ j, lam j ^ d / (B : ℝ) by rw [Finset.sum_div]]
    exact Finset.abs_sum_le_sum_abs _ _
  | lat => exact absurd rfl hσ

private lemma pp_Mw_bound {N B : ℕ} (v w : Fin N → ℝ) (γ C : ℝ) (hγ : 1 ≤ γ) (hC : 1 ≤ C)
    (hv : ∀ i, |v i| ≤ C) (hN : (N : ℝ) ≤ γ * B) (d : ℕ) :
    ‖(((B : ℝ)⁻¹ * ∑ i, v i ^ d * w i : ℝ) : ℂ)‖ ≤ (1 + ∑ i, |w i|) * (γ * C ^ d) := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hW : 0 ≤ 1 + ∑ i, |w i| := by positivity
  refine le_trans ?_ (pp_ext_sum_w v w γ C (1 + ∑ i, |w i|) hγ hC hW hv (fun i => ?_) hN d)
  · simp only [inv_mul_eq_div]
    rw [show (∑ i, v i ^ d * w i) / (B : ℝ) = ∑ i, v i ^ d * w i / (B : ℝ) by rw [Finset.sum_div]]
    exact Finset.abs_sum_le_sum_abs _ _
  · have := Finset.single_le_sum (fun j _ => abs_nonneg (w j)) (Finset.mem_univ i)
    linarith

private lemma pp_cp_bound_c {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {β : ℝ} (hβ : 0 ≤ β ∧ β < 1) (ℓ J : ℕ) (R : ℝ) (g : ℤ → Ω → ℝ) (n1 n2 : ℕ)
    (hn : 1 ≤ n1 + n2) :
    ‖(((∑ α ∈ cutoffLabels J ℓ, ∫ ω, cutoffXi β ℓ J R 1 g α ω ^ n1 *
        cutoffXi β ℓ J R 2 g α ω ^ n2 ∂P : ℝ)) : ℂ)‖ ≤ (max 1 R) ^ (n1 + n2) := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact pp_cp_bound P hβ ℓ J R g n1 n2 hn



private lemma pt_Bw_facts (z : ℂ) (cdf : ℕ → ℂ) (K : PtK) (τ : VType) (hτ : τ ≠ VType.lat)
    (hC : ∀ σ, σ ≠ VType.lat → Summable (fun Y : OE σ => ‖ob_C z cdf K.Mf Y‖))
    (hη : Summable (fun p : ℕ => ‖cdf (2 * p + 2)‖ * ob_κ z cdf K.Mf (ob_f0 τ) ^ (p + 1) *
      ob_κ z cdf K.Mf τ ^ p)) (ηb C : ℝ)
    (hηb : ∑' p : ℕ, ‖cdf (2 * p + 2)‖ * ob_κ z cdf K.Mf (ob_f0 τ) ^ (p + 1) *
      ob_κ z cdf K.Mf τ ^ p ≤ ηb)
    (hsm : ∀ x : ℝ, |x| ≤ C → ‖(x : ℂ)‖ * (‖z‖ * ηb) < 1) :
    Summable (fun b : OBlk τ => ‖ptBw z cdf K b‖) ∧
    (∀ x : ℝ, |x| ≤ C → ‖(x : ℂ)‖ * ∑' b : OBlk τ, ‖ptBw z cdf K b‖ < 1) ∧
    ∑' b : OBlk τ, ptBw z cdf K b = z * ∑' p : ℕ, cdf (2 * p + 2) *
      ob_m z cdf K.Mf (ob_f0 τ) ^ (p + 1) * ob_m z cdf K.Mf τ ^ p := by
  obtain ⟨h1, h2, h3⟩ := pt_Bw_sum z cdf K τ hτ hC hη
  refine ⟨h1, fun x hx => ?_, h3⟩
  rw [h2]
  calc ‖(x : ℂ)‖ * (‖z‖ * ∑' p : ℕ, ‖cdf (2 * p + 2)‖ * ob_κ z cdf K.Mf (ob_f0 τ) ^ (p + 1) *
        ob_κ z cdf K.Mf τ ^ p) ≤ ‖(x : ℂ)‖ * (‖z‖ * ηb) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hηb (norm_nonneg _)) (norm_nonneg _)
    _ < 1 := hsm x hx



private lemma pp_trace_two {d : ℕ}
    (A U : Matrix (Fin d) (Fin d) ℝ) (v w : Fin d → ℝ)
    (hU : Uᵀ * U = 1) (hA : A = U * Matrix.diagonal v * Uᵀ)
    (F : Matrix (Fin d) (Fin d) ℝ) (hF : F = U * Matrix.diagonal w * Uᵀ)
    (s a u c : ℝ) (hs : ∀ i, s + a * v i ≠ 0) (hu : ∀ i, u + c * v i ≠ 0) :
    (F * A * (s • (1 : Matrix (Fin d) (Fin d) ℝ) + a • A)⁻¹ *
      (u • (1 : Matrix (Fin d) (Fin d) ℝ) + c • A)⁻¹).trace =
        ∑ i, w i * v i / ((s + a * v i) * (u + c * v i)) := by
  classical
  have hUU : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have hinv : ∀ (t b : ℝ), (∀ i, t + b * v i ≠ 0) →
      (t • (1 : Matrix (Fin d) (Fin d) ℝ) + b • A)⁻¹ =
        U * Matrix.diagonal (fun i => (t + b * v i)⁻¹) * Uᵀ := by
    intro t b hden
    have he : Matrix.diagonal (fun i => t + b * v i) =
        t • (1 : Matrix (Fin d) (Fin d) ℝ) + b • Matrix.diagonal v := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
    have hfac : t • (1 : Matrix (Fin d) (Fin d) ℝ) + b • A =
        U * Matrix.diagonal (fun i => t + b * v i) * Uᵀ := by
      rw [he, Matrix.mul_add, Matrix.add_mul]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUU, ← hA]
    have hdiag : Matrix.diagonal (fun i => t + b * v i) *
        Matrix.diagonal (fun i => (t + b * v i)⁻¹) = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij, hden]
    apply Matrix.inv_eq_right_inv
    rw [hfac]
    calc U * Matrix.diagonal (fun i => t + b * v i) * Uᵀ *
          (U * Matrix.diagonal (fun i => (t + b * v i)⁻¹) * Uᵀ) =
        U * (Matrix.diagonal (fun i => t + b * v i) *
          Matrix.diagonal (fun i => (t + b * v i)⁻¹)) * Uᵀ := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
      _ = 1 := by rw [hdiag, Matrix.mul_one, hUU]
  rw [hinv s a hs, hinv u c hu, hA, hF]
  calc
    (U * Matrix.diagonal w * Uᵀ * (U * Matrix.diagonal v * Uᵀ) *
        (U * Matrix.diagonal (fun i => (s + a * v i)⁻¹) * Uᵀ) *
        (U * Matrix.diagonal (fun i => (u + c * v i)⁻¹) * Uᵀ)).trace =
      (U * (Matrix.diagonal w * Matrix.diagonal v *
        Matrix.diagonal (fun i => (s + a * v i)⁻¹) *
        Matrix.diagonal (fun i => (u + c * v i)⁻¹)) * Uᵀ).trace := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul,
            ← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul,
            ← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
    _ = (Matrix.diagonal w * Matrix.diagonal v *
        Matrix.diagonal (fun i => (s + a * v i)⁻¹) *
        Matrix.diagonal (fun i => (u + c * v i)⁻¹)).trace := by
          rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hU, Matrix.one_mul]
    _ = _ := by
      simp only [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, div_eq_mul_inv]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_inv]
      ring



private lemma pp_conv (s u U V Tout Tin b e σ σ' σt σt' : ℝ) (hs : 0 < s) (hu : 0 < u)
    (po pin fo fin A D bb : ℂ)
    (hpo : po = ((-(Real.sqrt s * Real.sqrt u * U) : ℝ) : ℂ))
    (hpin : pin = ((-(Real.sqrt s * Real.sqrt u * V) : ℝ) : ℂ))
    (hfo : fo = ((-(Real.sqrt s * Real.sqrt u * Tout) : ℝ) : ℂ))
    (hfin : fin = ((-(Real.sqrt s * Real.sqrt u * Tin) : ℝ) : ℂ))
    (hA : A = ((-(Real.sqrt s * Real.sqrt u * σt * σt' * e) : ℝ) : ℂ))
    (hD : D = ((-(Real.sqrt s * Real.sqrt u * σ * σ' * e) : ℝ) : ℂ))
    (hb : bb = (b : ℂ)) :
    (1 - po * A) * (1 - pin * D) - po * pin * bb ^ 2 =
      (((1 - s * u * U * σt * σt' * e) * (1 - s * u * V * σ * σ' * e) - s * u * U * V * b ^ 2 : ℝ) : ℂ) ∧
    fo * fin * bb = ((s * u * Tout * Tin * b : ℝ) : ℂ) := by
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have huu : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu.le
  subst hpo hpin hfo hfin hA hD hb
  have hs2 : (Real.sqrt s : ℂ) ^ 2 = (s : ℂ) := by exact_mod_cast Real.sq_sqrt hs.le
  have hu2 : (Real.sqrt u : ℂ) ^ 2 = (u : ℂ) := by exact_mod_cast Real.sq_sqrt hu.le
  constructor
  · push_cast
    rw [← hs2, ← hu2]
    ring
  · push_cast
    rw [← hs2, ← hu2]
    ring



private lemma pp_tout_eq {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (x y : ℝ × ℝ × ℝ × ℝ) (hx : 0 ≤ x.2.2.1) (hy : 0 ≤ y.2.2.1) (s u : ℝ) (hs : 0 < s) (hu : 0 < u)
    (Fd : Fin m → ℝ) (Fm : Matrix (Fin m) (Fin m) ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ) :
    toutT Fp.C B x y s u Fm = (B : ℝ)⁻¹ * ∑ i, Fd i * S.μ i /
      ((s + x.2.2.1 * S.μ i) * (u + y.2.2.1 * S.μ i)) := by
  have hso : ∀ i, s + x.2.2.1 * S.μ i ≠ 0 := fun i => ne_of_gt
    (add_pos_of_pos_of_nonneg hs (mul_nonneg hx (μ_nonneg S i)))
  have huo : ∀ i, u + y.2.2.1 * S.μ i ≠ 0 := fun i => ne_of_gt
    (add_pos_of_pos_of_nonneg hu (mul_nonneg hy (μ_nonneg S i)))
  unfold toutT
  rw [pp_trace_two Fp.C.Sout S.uOut S.μ Fd S.huOut (Sout_eq_spectral S) Fm hFd s x.2.2.1 u y.2.2.1 hso huo]

private lemma pp_tin_eq {m n B : ℕ} (Fp : FrozenParams m n B) (S : SpectralData Fp.C)
    (x y : ℝ × ℝ × ℝ × ℝ) (hx : 0 ≤ x.2.2.2) (hy : 0 ≤ y.2.2.2) (s u : ℝ) (hs : 0 < s) (hu : 0 < u)
    (Gd : Fin n → ℝ) (Gm : Matrix (Fin n) (Fin n) ℝ)
    (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ) :
    tinT Fp.C B x y s u Gm = (B : ℝ)⁻¹ * ∑ j, Gd j * S.lam j /
      ((s + x.2.2.2 * S.lam j) * (u + y.2.2.2 * S.lam j)) := by
  have hsi : ∀ j, s + x.2.2.2 * S.lam j ≠ 0 := fun j => ne_of_gt
    (add_pos_of_pos_of_nonneg hs (mul_nonneg hx (lam_nonneg S j)))
  have hui : ∀ j, u + y.2.2.2 * S.lam j ≠ 0 := fun j => ne_of_gt
    (add_pos_of_pos_of_nonneg hu (mul_nonneg hy (lam_nonneg S j)))
  unfold tinT
  rw [pp_trace_two Fp.C.Sin S.vIn S.lam Gd S.hvIn (Sin_eq_spectral S) Gm hGd s x.2.2.2 u y.2.2.2 hsi hui]



private lemma pp_g12 (s u a a' κ : ℝ) (hd1 : 0 < s + a * κ) (hd2 : 0 < u + a' * κ) :
    (-(Complex.I * (Real.sqrt s : ℂ)) / ((s : ℂ) + (a : ℂ) * (κ : ℂ))) *
      (-(Complex.I * (Real.sqrt u : ℂ)) / ((u : ℂ) + (a' : ℂ) * (κ : ℂ))) =
      ((-(Real.sqrt s * Real.sqrt u) / ((s + a * κ) * (u + a' * κ)) : ℝ) : ℂ) := by
  have h1 : ((s : ℂ) + (a : ℂ) * (κ : ℂ)) ≠ 0 := by exact_mod_cast hd1.ne'
  have h2 : ((u : ℂ) + (a' : ℂ) * (κ : ℂ)) ≠ 0 := by exact_mod_cast hd2.ne'
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

private lemma pp_form (z1 z2 A1 A2 : ℂ) (κ c : ℝ) (e : ℕ) (g1 g2 : ℂ)
    (h1 : z1 / (1 - (κ : ℂ) * A1) = g1) (h2 : z2 / (1 - (κ : ℂ) * A2) = g2) :
    z2 * (z1 * ((c : ℂ) * ((κ : ℂ) ^ e / ((1 - (κ : ℂ) * A1) * (1 - (κ : ℂ) * A2))))) =
      (c : ℂ) * (κ : ℂ) ^ e * (g1 * g2) := by
  generalize (1 - (κ : ℂ) * A1) = D1 at h1 ⊢
  generalize (1 - (κ : ℂ) * A2) = D2 at h2 ⊢
  rw [← h1, ← h2]
  ring



private lemma pp_branch_nonneg {m n B : ℕ} {F : ℝ → ℝ} {C : Muon.Covariances m n} {s : ℝ}
    {x : ℝ × ℝ × ℝ × ℝ} (h : IsBranchPoint F C B s x) :
    0 ≤ x.1 ∧ 0 ≤ x.2.1 ∧ 0 ≤ x.2.2.1 ∧ 0 ≤ x.2.2.2 := by
  obtain ⟨σ, σ', a, c⟩ := x
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩



private lemma pp_sum_ident {ι : Type} [Fintype ι] (s u a a' : ℝ) (z1 z2 A1 A2 : ℂ) (κ c : ι → ℝ)
    (e : ℕ) (hd1 : ∀ i, 0 < s + a * κ i) (hd2 : ∀ i, 0 < u + a' * κ i)
    (h1 : ∀ i, z1 / (1 - (κ i : ℂ) * A1) =
      -(Complex.I * (Real.sqrt s : ℂ)) / ((s : ℂ) + (a : ℂ) * (κ i : ℂ)))
    (h2 : ∀ i, z2 / (1 - (κ i : ℂ) * A2) =
      -(Complex.I * (Real.sqrt u : ℂ)) / ((u : ℂ) + (a' : ℂ) * (κ i : ℂ))) :
    z2 * (z1 * ∑ i, (c i : ℂ) * ((κ i : ℂ) ^ e /
        ((1 - (κ i : ℂ) * A1) * (1 - (κ i : ℂ) * A2)))) =
      ((-(Real.sqrt s * Real.sqrt u) * ∑ i, c i * κ i ^ e /
        ((s + a * κ i) * (u + a' * κ i)) : ℝ) : ℂ) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pp_form z1 z2 A1 A2 (κ i) (c i) e _ _ (h1 i) (h2 i), pp_g12 s u a a' (κ i) (hd1 i) (hd2 i)]
  push_cast
  ring



/-! ### The main evaluation -/

set_option maxHeartbeats 4000000 in
private lemma pt_main {Ω : Type} [MeasurableSpace Ω] {m n B : ℕ}
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) (Fp : FrozenParams m n B)
    (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hout : Fp.C.Sout ≠ 0) (hin : Fp.C.Sin ≠ 0)
    {P : Measure Ω} [IsProbabilityMeasure P] (ℓ J : ℕ) (R : ℝ)
    {g : ℤ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (Fm : Matrix (Fin m) (Fin m) ℝ) (Gm : Matrix (Fin n) (Fin n) ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ)
    (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ)
    (s u : ℝ) (hs : sRad cert γstar CSig R ≤ s) (hu : sRad cert γstar CSig R ≤ u)
    (hdelta : profileDelta P Fp.C B (cutoffXi Fp.β ℓ J R 1 g) (cutoffXi Fp.β ℓ J R 2 g) s u ≠ 0) :
    ∑' q : PathIdx m n J ℓ, pathTerm P Fp.β ℓ J R B Fd Gd S.μ S.lam g s u q =
      ((profileKernel P Fp.C B (cutoffXi Fp.β ℓ J R 1 g) (cutoffXi Fp.β ℓ J R 2 g) Fm Gm s u : ℝ) : ℂ) := by
  classical
  have hs0 : 0 < s := pd_sRad_pos cert γstar CSig R s hs
  have hu0 : 0 < u := pd_sRad_pos cert γstar CSig R u hu
  -- constants
  obtain ⟨hS1, hS2, hS3⟩ := hS
  have hS' : SizeFin Fp.C B γstar CSig := ⟨hS1, hS2, hS3⟩
  set γ := max 1 γstar with hγdef
  set C := max 1 CSig with hCdef
  set R1 := max 1 R with hR1def
  set Kc := γ * C * R1 with hKc
  have hγ : 1 ≤ γ := le_max_left _ _
  have hC : 1 ≤ C := le_max_left _ _
  have hR1 : 1 ≤ R1 := le_max_left _ _
  have hμ : ∀ i, |S.μ i| ≤ C := fun i =>
    (ob_abs_eig_le Fp.C.Sout S.uOut (S.μ i) i S.huOut (S.eigOut i)).trans
      (hS2.trans (le_max_right _ _))
  have hlam : ∀ j, |S.lam j| ≤ C := fun j =>
    (ob_abs_eig_le Fp.C.Sin S.vIn (S.lam j) j S.hvIn (S.eigIn j)).trans
      (hS3.trans (le_max_right _ _))
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hmn : ∀ q : ℕ, q ≤ max m n → (q : ℝ) ≤ γ * B := fun q hq =>
    ((Nat.cast_le.mpr hq).trans hS1).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hB)
  have hm : (m : ℝ) ≤ γ * B := hmn m (le_max_left _ _)
  have hn : (n : ℝ) ≤ γ * B := hmn n (le_max_right _ _)
  have hK1 : 1 ≤ Kc := by
    have : 1 ≤ γ * C := by nlinarith
    nlinarith
  have hsK : 64 * Kc ^ 2 ≤ s := by
    refine le_trans ?_ hs
    unfold sRad
    refine le_trans (le_of_eq ?_) (le_max_left _ _)
    rw [hKc]; ring
  have huK : 64 * Kc ^ 2 ≤ u := by
    refine le_trans ?_ hu
    unfold sRad
    refine le_trans (le_of_eq ?_) (le_max_left _ _)
    rw [hKc]; ring
  have hsK' : 64 * (γ * C * max 1 R) ^ 2 ≤ s := hsK
  have huK' : 64 * (γ * C * max 1 R) ^ 2 ≤ u := huK
  -- one-buffer data
  have hone1 := lem_app_vol_closed_onebuffer_i cert γstar CSig Fp S hS' hout hin ℓ J R hg 1
    (Or.inl rfl) s hs
  have hone2 := lem_app_vol_closed_onebuffer_i cert γstar CSig Fp S hS' hout hin ℓ J R hg 2
    (Or.inr rfl) u hu
  obtain ⟨hC1, ⟨hko1, hko1'⟩, ⟨hki1, hki1'⟩, hRδ1, hsm1, hz1, hηo1, hηi1, hGo1, hGi1⟩ :=
    pt_both P Fp.hβ ℓ J R B S.μ S.lam g 1 s γ C hγ hC hμ hlam hm hn hsK'
      (fun i => (hone1.1 i).1) (fun i => (hone1.1 i).2)
      (fun j => (hone1.2 j).1) (fun j => (hone1.2 j).2)
  obtain ⟨hC2, ⟨hko2, hko2'⟩, ⟨hki2, hki2'⟩, hRδ2, hsm2, hz2, hηo2, hηi2, hGo2, hGi2⟩ :=
    pt_both P Fp.hβ ℓ J R B S.μ S.lam g 2 u γ C hγ hC hμ hlam hm hn huK'
      (fun i => (hone2.1 i).1) (fun i => (hone2.1 i).2)
      (fun j => (hone2.2 j).1) (fun j => (hone2.2 j).2)
  obtain ⟨hv1o, hv1i⟩ := lem_app_vol_closed_onebuffer_ii cert γstar CSig Fp S hS' hout hin ℓ J R hg 1
    (Or.inl rfl) s hs
  obtain ⟨hv2o, hv2i⟩ := lem_app_vol_closed_onebuffer_ii cert γstar CSig Fp S hS' hout hin ℓ J R hg 2
    (Or.inr rfl) u hu
  obtain ⟨hm1o, hm1i, hq1⟩ := lem_app_vol_closed_onebuffer_iii cert γstar CSig Fp S hS' hout hin ℓ J R hg 1
    (Or.inl rfl) s hs
  obtain ⟨hm2o, hm2i, hq2⟩ := lem_app_vol_closed_onebuffer_iii cert γstar CSig Fp S hS' hout hin ℓ J R hg 2
    (Or.inr rfl) u hu
  -- the pointed parameters
  set K := physK P Fp.β ℓ J R B Gd S.μ S.lam g s u with hK
  set ρ := physRho B Fd S.μ with hρdef
  have hcdf1 : K.cdf1 = ob_cdf P Fp.β ℓ J R g 1 := by
    funext d; simp [K, physK, PtK.cdf1, ob_cdf]
  have hcdf2 : K.cdf2 = ob_cdf P Fp.β ℓ J R g 2 := by
    funext d; simp [K, physK, PtK.cdf2, ob_cdf]
  have hKz1 : K.z1 = zetaT s := rfl
  have hKz2 : K.z2 = zetaT u := rfl
  have hKMf : K.Mf = ob_Mf B S.μ S.lam := rfl
  have hC1K : ∀ σ, σ ≠ VType.lat → Summable (fun Y : OE σ => ‖ob_C K.z1 K.cdf1 K.Mf Y‖) := by
    intro σ hσ; rw [hcdf1]; exact hC1 σ hσ
  have hC2K : ∀ σ, σ ≠ VType.lat → Summable (fun Y : OE σ => ‖ob_C K.z2 K.cdf2 K.Mf Y‖) := by
    intro σ hσ; rw [hcdf2]; exact hC2 σ hσ
  -- norm bounds of the parameters
  set z0 : ℝ := (8 * Kc)⁻¹ with hz0def
  have hKc0 : 0 < Kc := by linarith
  have hz0pos : 0 < z0 := by positivity
  have hz1K : ‖K.z1‖ ≤ z0 := by
    rw [hKz1, hz1, hz0def]
    refine inv_anti₀ (by positivity) ?_
    apply Real.le_sqrt_of_sq_le; nlinarith
  have hz2K : ‖K.z2‖ ≤ z0 := by
    rw [hKz2, hz2, hz0def]
    refine inv_anti₀ (by positivity) ?_
    apply Real.le_sqrt_of_sq_le; nlinarith
  have hϑ : 8 * (γ * C * R1 * z0) ≤ 1 := by
    rw [hz0def]
    have : γ * C * R1 = Kc := rfl
    rw [this]; field_simp; exact le_rfl
  set CG : ℝ := 1 + ∑ j, |Gd j| with hCG
  set CF : ℝ := 1 + ∑ i, |Fd i| with hCF
  have hCG1 : 1 ≤ CG := by
    have : 0 ≤ ∑ j, |Gd j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hCF1 : 1 ≤ CF := by
    have : 0 ≤ ∑ i, |Fd i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hMfK : ∀ σ d, σ ≠ VType.lat → ‖K.Mf σ d‖ ≤ γ * C ^ d := fun σ d hσ =>
    pp_Mf_bound S.μ S.lam γ C hγ hC hμ hlam hm hn σ hσ d
  have hMgK : ∀ d, ‖K.Mg d‖ ≤ CG * (γ * C ^ d) := fun d =>
    pp_Mw_bound S.lam Gd γ C hγ hC hlam hn d
  have hρK : ∀ d, ‖ρ VType.out d‖ ≤ CF * (γ * C ^ d) := by
    intro d
    simp only [ρ, physRho, if_true]
    exact pp_Mw_bound S.μ Fd γ C hγ hC hμ hm d
  have hρK' : ∀ σ d, σ ≠ VType.lat → ‖K.Mf σ d‖ ≤ CF * (γ * C ^ d) := fun σ d hσ =>
    (hMfK σ d hσ).trans (le_mul_of_one_le_left (by positivity) hCF1)
  have hcpK : ∀ n1 n2, 1 ≤ n1 + n2 → ‖K.cp n1 n2‖ ≤ R1 ^ (n1 + n2) := fun n1 n2 hn12 =>
    pp_cp_bound_c P Fp.hβ ℓ J R g n1 n2 hn12
  -- summability of the pointed sums
  have hout' : (VType.out : VType) ≠ VType.lat := by decide
  have hinp' : (VType.inp : VType) ≠ VType.lat := by decide
  have hPtop : Summable (fun Y : OE VType.out => ‖ptSum K Y.2 0 ρ‖) :=
    pt_sum_summable K VType.out hout' 0 ρ z0 R1 γ C CG CF hz0pos.le hR1 hγ hC hCG1 hCF1 hz1K hz2K
      hcpK (fun σ d hσ => hMfK σ d hσ) hMgK hρK hϑ
  have hPch : ∀ σ, σ ≠ VType.lat → Summable (fun Y : OE σ => ‖ptSum K Y.2 1 K.Mf‖) := by
    intro σ hσ
    exact pt_sum_summable K σ hσ 1 K.Mf z0 R1 γ C CG CF hz0pos.le hR1 hγ hC hCG1 hCF1 hz1K hz2K
      hcpK (fun σ d hσ => hMfK σ d hσ) hMgK (fun d => hρK' σ d hσ) hϑ
  -- the block sums
  have hηo1' : Summable (fun p : ℕ => ‖K.cdf1 (2 * p + 2)‖ * ob_κ K.z1 K.cdf1 K.Mf (ob_f0 VType.out) ^ (p + 1) *
      ob_κ K.z1 K.cdf1 K.Mf VType.out ^ p) := by rw [hcdf1]; exact hηo1.1
  have hηi1' : Summable (fun p : ℕ => ‖K.cdf1 (2 * p + 2)‖ * ob_κ K.z1 K.cdf1 K.Mf (ob_f0 VType.inp) ^ (p + 1) *
      ob_κ K.z1 K.cdf1 K.Mf VType.inp ^ p) := by rw [hcdf1]; exact hηi1.1
  have hηo2' : Summable (fun p : ℕ => ‖K.cdf2 (2 * p + 2)‖ * ob_κ K.z2 K.cdf2 K.Mf (ob_f0 VType.out) ^ (p + 1) *
      ob_κ K.z2 K.cdf2 K.Mf VType.out ^ p) := by rw [hcdf2]; exact hηo2.1
  have hηi2' : Summable (fun p : ℕ => ‖K.cdf2 (2 * p + 2)‖ * ob_κ K.z2 K.cdf2 K.Mf (ob_f0 VType.inp) ^ (p + 1) *
      ob_κ K.z2 K.cdf2 K.Mf VType.inp ^ p) := by rw [hcdf2]; exact hηi2.1
  set δ1 : ℝ := 2 * γ * C / Real.sqrt s with hδ1
  set δ2 : ℝ := 2 * γ * C / Real.sqrt u with hδ2
  obtain ⟨h1o, so1, A1o⟩ := pt_Bw_facts K.z1 K.cdf1 K VType.out hout' hC1K hηo1' (16 / 15 * (R1 ^ 2 * δ1)) C
    (by rw [hcdf1]; exact hηo1.2) (by rw [hKz1]; exact hsm1)
  obtain ⟨h1i, si1, A1i⟩ := pt_Bw_facts K.z1 K.cdf1 K VType.inp hinp' hC1K hηi1' (16 / 15 * (R1 ^ 2 * δ1)) C
    (by rw [hcdf1]; exact hηi1.2) (by rw [hKz1]; exact hsm1)
  obtain ⟨h2o, so2, A2o⟩ := pt_Bw_facts K.z2 K.cdf2 K VType.out hout' hC2K hηo2' (16 / 15 * (R1 ^ 2 * δ2)) C
    (by rw [hcdf2]; exact hηo2.2) (by rw [hKz2]; exact hsm2)
  obtain ⟨h2i, si2, A2i⟩ := pt_Bw_facts K.z2 K.cdf2 K VType.inp hinp' hC2K hηi2' (16 / 15 * (R1 ^ 2 * δ2)) C
    (by rw [hcdf2]; exact hηi2.2) (by rw [hKz2]; exact hsm2)
  -- the marked blocks
  set δ : ℝ := max δ1 δ2 with hδ
  have hδ1d : δ1 ≤ δ := le_max_left _ _
  have hδ2d : δ2 ≤ δ := le_max_right _ _
  have hδ0 : 0 ≤ δ := by
    have : 0 ≤ δ1 := by rw [hδ1]; positivity
    exact this.trans hδ1d
  have hRδ : R1 ^ 2 * δ ^ 2 ≤ 1 / 16 := by
    rcases le_total δ1 δ2 with h | h
    · rw [hδ, max_eq_right h]; exact hRδ2
    · rw [hδ, max_eq_left h]; exact hRδ1
  set KP : ℝ := ptKP K VType.out + ptKP K VType.inp with hKP
  have hKPo : 0 ≤ ptKP K VType.out := tsum_nonneg fun _ => norm_nonneg _
  have hKPi : 0 ≤ ptKP K VType.inp := tsum_nonneg fun _ => norm_nonneg _
  have hkP : ∀ σ, σ ≠ VType.lat → 0 ≤ ptKP K σ ∧ ptKP K σ ≤ KP := by
    intro σ hσ
    cases σ with
    | out => exact ⟨hKPo, by rw [hKP]; linarith⟩
    | inp => exact ⟨hKPi, by rw [hKP]; linarith⟩
    | lat => exact absurd rfl hσ
  have hk1 : ∀ σ, σ ≠ VType.lat → 0 ≤ ptK1 K σ ∧ ptK1 K σ ≤ δ := by
    intro σ hσ
    cases σ with
    | out => exact ⟨by unfold ptK1; rw [hcdf1]; exact hko1, by
        unfold ptK1; rw [hcdf1]; exact hko1'.trans hδ1d⟩
    | inp => exact ⟨by unfold ptK1; rw [hcdf1]; exact hki1, by
        unfold ptK1; rw [hcdf1]; exact hki1'.trans hδ1d⟩
    | lat => exact absurd rfl hσ
  have hk2 : ∀ σ, σ ≠ VType.lat → 0 ≤ ptK2 K σ ∧ ptK2 K σ ≤ δ := by
    intro σ hσ
    cases σ with
    | out => exact ⟨by unfold ptK2; rw [hcdf2]; exact hko2, by
        unfold ptK2; rw [hcdf2]; exact hko2'.trans hδ2d⟩
    | inp => exact ⟨by unfold ptK2; rw [hcdf2]; exact hki2, by
        unfold ptK2; rw [hcdf2]; exact hki2'.trans hδ2d⟩
    | lat => exact absurd rfl hσ
  have hBm : ∀ τ, τ ≠ VType.lat → Summable (fun b : OBlk τ => ‖ptBm K b‖) ∧
      ∑' b : OBlk τ, ptBm K b = ∑' p : ℕ, ∑ c0 : Fin (2 * p + 1), ptTerm K τ p c0 := fun τ hτ =>
    pt_Bm_sum K τ hτ hC1K hC2K hPch z0 R1 δ KP hz2K hR1 hδ0 (add_nonneg hKPo hKPi) hRδ hcpK hk1 hk2 hkP
  have hm1 : ∀ σ, σ ≠ VType.lat → ‖ptM1 K σ‖ ≤ δ := by
    intro σ hσ
    exact (norm_tsum_le_tsum_norm (hC1K σ hσ)).trans (le_trans (hk1 σ hσ).2 le_rfl)
  have hm2 : ∀ σ, σ ≠ VType.lat → ‖ptM2 K σ‖ ≤ δ := by
    intro σ hσ
    exact (norm_tsum_le_tsum_norm (hC2K σ hσ)).trans (le_trans (hk2 σ hσ).2 le_rfl)
  -- the Wm formulas
  have hGBsym : ∀ e f, ptGB K VType.inp e f = ptGB K VType.out e f := by
    intro e f; simp only [ptGB, ob_f0, mul_comm]
  have hGEsym : ∀ e f, ptGE K VType.inp e f = ptGE K VType.out e f := by
    intro e f; simp only [ptGE, ob_f0, mul_comm]
  have hWmo : ptWm K VType.out = K.z2 * (ptP K VType.inp * ptBs K +
      ptM1 K VType.inp * ptM2 K VType.inp * ptP K VType.out * ptEs K) := by
    unfold ptWm ptBs ptEs
    rw [(hBm _ hout').2]
    exact pt_Wm_eval K VType.out hout' R1 δ hR1 hδ0 hRδ hcpK hm1 hm2
  have hWmi : ptWm K VType.inp = K.z2 * (ptP K VType.out * ptBs K +
      ptM1 K VType.out * ptM2 K VType.out * ptP K VType.inp * ptEs K) := by
    unfold ptWm ptBs ptEs
    rw [(hBm _ hinp').2, pt_Wm_eval K VType.inp hinp' R1 δ hR1 hδ0 hRδ hcpK hm1 hm2]
    simp only [ob_f0, hGBsym, hGEsym]
  -- the coefficient families
  set cF : Fin m → ℂ := fun i => (((B : ℝ)⁻¹ * Fd i : ℝ) : ℂ) with hcF
  set cM1 : Fin m → ℂ := fun _ => (((B : ℝ)⁻¹ : ℝ) : ℂ) with hcM1
  set κ1 : Fin m → ℂ := fun i => ((S.μ i : ℝ) : ℂ) with hκ1
  set cM2 : Fin n → ℂ := fun _ => (((B : ℝ)⁻¹ : ℝ) : ℂ) with hcM2
  set cG : Fin n → ℂ := fun j => (((B : ℝ)⁻¹ * Gd j : ℝ) : ℂ) with hcG
  set κ2 : Fin n → ℂ := fun j => ((S.lam j : ℝ) : ℂ) with hκ2
  have hρ' : ∀ d, ρ VType.out d = ∑ i, cF i * κ1 i ^ d := by
    intro d
    simp only [ρ, physRho, if_true, cF, κ1]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hMfo' : ∀ d, K.Mf VType.out d = ∑ i, cM1 i * κ1 i ^ d := by
    intro d
    simp only [hKMf, ob_Mf, if_true, cM1, κ1]
    push_cast
    rw [Finset.mul_sum]
  have hMfi' : ∀ d, K.Mf VType.inp d = ∑ j, cM2 j * κ2 j ^ d := by
    intro d
    simp only [hKMf, ob_Mf, cM2, κ2]
    rw [if_neg (by decide)]
    push_cast
    rw [Finset.mul_sum]
  have hMg' : ∀ d, K.Mg d = ∑ j, cG j * κ2 j ^ d := by
    intro d
    simp only [K, physK, cG, κ2]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have so1' : ∀ i, ‖κ1 i‖ * ∑' b : OBlk VType.out, ‖ptBw K.z1 K.cdf1 K b‖ < 1 := fun i => so1 (S.μ i) (hμ i)
  have so2' : ∀ i, ‖κ1 i‖ * ∑' b : OBlk VType.out, ‖ptBw K.z2 K.cdf2 K b‖ < 1 := fun i => so2 (S.μ i) (hμ i)
  have si1' : ∀ i, ‖κ1 i‖ * ∑' b : OBlk VType.inp, ‖ptBw K.z1 K.cdf1 K b‖ < 1 := fun i => si1 (S.μ i) (hμ i)
  have si2' : ∀ i, ‖κ1 i‖ * ∑' b : OBlk VType.inp, ‖ptBw K.z2 K.cdf2 K b‖ < 1 := fun i => si2 (S.μ i) (hμ i)
  have to1' : ∀ j, ‖κ2 j‖ * ∑' b : OBlk VType.out, ‖ptBw K.z1 K.cdf1 K b‖ < 1 := fun j => so1 (S.lam j) (hlam j)
  have to2' : ∀ j, ‖κ2 j‖ * ∑' b : OBlk VType.out, ‖ptBw K.z2 K.cdf2 K b‖ < 1 := fun j => so2 (S.lam j) (hlam j)
  have ti1' : ∀ j, ‖κ2 j‖ * ∑' b : OBlk VType.inp, ‖ptBw K.z1 K.cdf1 K b‖ < 1 := fun j => si1 (S.lam j) (hlam j)
  have ti2' : ∀ j, ‖κ2 j‖ * ∑' b : OBlk VType.inp, ‖ptBw K.z2 K.cdf2 K b‖ < 1 := fun j => si2 (S.lam j) (hlam j)
  -- the branch points
  set x := marginalBranch P Fp.β ℓ J R Fp.C B 1 g s with hx
  set y := marginalBranch P Fp.β ℓ J R Fp.C B 2 g u with hy
  have hxspec := ob_marginal_spec γstar CSig Fp hS' hout hin ℓ J R hg 1 (Or.inl rfl) s hs0
  have hyspec := ob_marginal_spec γstar CSig Fp hS' hout hin ℓ J R hg 2 (Or.inr rfl) u hu0
  obtain ⟨hxσ, hxσt, hxa, hxc⟩ := pp_branch_nonneg hxspec
  obtain ⟨hyσ, hyσt, hya, hyc⟩ := pp_branch_nonneg hyspec
  -- the masses
  have eM1o : ptM1 K VType.out = oneBufMo P Fp.β ℓ J R B S.μ S.lam g 1 s := by
    unfold ptM1; rw [hcdf1]
    exact ob_m_out_eq P Fp.β ℓ J R B S.μ S.lam g 1 s (fun i => (hone1.1 i).1)
  have eM1i : ptM1 K VType.inp = oneBufMin P Fp.β ℓ J R B S.μ S.lam g 1 s := by
    unfold ptM1; rw [hcdf1]
    exact ob_m_inp_eq P Fp.β ℓ J R B S.μ S.lam g 1 s (fun j => (hone1.2 j).1)
  have eM2o : ptM2 K VType.out = oneBufMo P Fp.β ℓ J R B S.μ S.lam g 2 u := by
    unfold ptM2; rw [hcdf2]
    exact ob_m_out_eq P Fp.β ℓ J R B S.μ S.lam g 2 u (fun i => (hone2.1 i).1)
  have eM2i : ptM2 K VType.inp = oneBufMin P Fp.β ℓ J R B S.μ S.lam g 2 u := by
    unfold ptM2; rw [hcdf2]
    exact ob_m_inp_eq P Fp.β ℓ J R B S.μ S.lam g 2 u (fun j => (hone2.2 j).1)
  have hM1o : ptM1 K VType.out = -(Complex.I * (Real.sqrt s : ℂ)) * (x.1 : ℂ) := eM1o.trans hm1o
  have hM1i : ptM1 K VType.inp = -(Complex.I * (Real.sqrt s : ℂ)) * (x.2.1 : ℂ) := eM1i.trans hm1i
  have hM2o : ptM2 K VType.out = -(Complex.I * (Real.sqrt u : ℂ)) * (y.1 : ℂ) := eM2o.trans hm2o
  have hM2i : ptM2 K VType.inp = -(Complex.I * (Real.sqrt u : ℂ)) * (y.2.1 : ℂ) := eM2i.trans hm2i
  set q1 : ℝ := s * x.1 * x.2.1 with hq1def
  set q2 : ℝ := u * y.1 * y.2.1 with hq2def
  have hMq1 : ptM1 K VType.inp * ptM1 K VType.out = ((-q1 : ℝ) : ℂ) := by
    rw [mul_comm, eM1o, eM1i]; push_cast; linear_combination -hq1
  have hMq2 : ptM2 K VType.inp * ptM2 K VType.out = ((-q2 : ℝ) : ℂ) := by
    rw [mul_comm, eM2o, eM2i]; push_cast; linear_combination -hq2
  have hq1s : R1 ^ 2 * |q1| ≤ 1 / 16 := by
    have h1 : |q1| ≤ δ ^ 2 := by
      have := congrArg norm hMq1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg] at this
      rw [← this, pow_two]
      exact mul_le_mul (hm1 _ hinp') (hm1 _ hout') (norm_nonneg _) hδ0
    calc R1 ^ 2 * |q1| ≤ R1 ^ 2 * δ ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 1 / 16 := hRδ
  have hq2s : R1 ^ 2 * |q2| ≤ 1 / 16 := by
    have h1 : |q2| ≤ δ ^ 2 := by
      have := congrArg norm hMq2
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg] at this
      rw [← this, pow_two]
      exact mul_le_mul (hm2 _ hinp') (hm2 _ hout') (norm_nonneg _) hδ0
    calc R1 ^ 2 * |q2| ≤ R1 ^ 2 * δ ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 1 / 16 := hRδ
  -- the two-point functions
  have hmeas : ∀ α, Measurable (g α) := hg.1
  have hBs : ptBs K = ((pairedB P (cutoffXi Fp.β ℓ J R 1 g) (cutoffXi Fp.β ℓ J R 2 g) q1 q2 : ℝ) : ℂ) := by
    have hS := pp_pairedB_series P Fp.hβ hmeas ℓ J R q1 q2 hq1s hq2s
    have hS' := (Complex.hasSum_ofReal).mpr hS
    unfold ptBs
    rw [← hS'.tsum_eq]
    refine tsum_congr fun x => ?_
    unfold ptGB
    simp only [ob_f0]
    rw [hMq1, hMq2]
    simp only [K, physK]
    push_cast
    ring
  have hEs : ptEs K = ((pairedE P (cutoffXi Fp.β ℓ J R 1 g) (cutoffXi Fp.β ℓ J R 2 g) q1 q2 : ℝ) : ℂ) := by
    have hS := pp_pairedE_series P Fp.hβ hmeas ℓ J R q1 q2 hq1s hq2s
    have hS' := (Complex.hasSum_ofReal).mpr hS
    unfold ptEs
    rw [← hS'.tsum_eq]
    refine tsum_congr fun x => ?_
    unfold ptGE
    simp only [ob_f0]
    rw [hMq1, hMq2]
    simp only [K, physK]
    push_cast
    ring
  -- the one-buffer sums
  have hg1o : ∀ i, K.z1 / (1 - (S.μ i : ℂ) * ptA1 K VType.out) =
      -(Complex.I * (Real.sqrt s : ℂ)) / ((s : ℂ) + (x.2.2.1 : ℂ) * (S.μ i : ℂ)) := by
    intro i
    have h := (hGo1 i).symm.trans (hv1o i)
    rw [← h]
    unfold ptA1
    rw [A1o]
    rw [hcdf1]
    rw [← mul_assoc]
    rfl
  have hg1i : ∀ j, K.z1 / (1 - (S.lam j : ℂ) * ptA1 K VType.inp) =
      -(Complex.I * (Real.sqrt s : ℂ)) / ((s : ℂ) + (x.2.2.2 : ℂ) * (S.lam j : ℂ)) := by
    intro j
    have h := (hGi1 j).symm.trans (hv1i j)
    rw [← h]
    unfold ptA1
    rw [A1i, hcdf1, ← mul_assoc]
    rfl
  have hg2o : ∀ i, K.z2 / (1 - (S.μ i : ℂ) * ptA2 K VType.out) =
      -(Complex.I * (Real.sqrt u : ℂ)) / ((u : ℂ) + (y.2.2.1 : ℂ) * (S.μ i : ℂ)) := by
    intro i
    have h := (hGo2 i).symm.trans (hv2o i)
    rw [← h]
    unfold ptA2
    rw [A2o, hcdf2, ← mul_assoc]
    rfl
  have hg2i : ∀ j, K.z2 / (1 - (S.lam j : ℂ) * ptA2 K VType.inp) =
      -(Complex.I * (Real.sqrt u : ℂ)) / ((u : ℂ) + (y.2.2.2 : ℂ) * (S.lam j : ℂ)) := by
    intro j
    have h := (hGi2 j).symm.trans (hv2i j)
    rw [← h]
    unfold ptA2
    rw [A2i, hcdf2, ← mul_assoc]
    rfl
  have hd1o : ∀ i, 0 < s + x.2.2.1 * S.μ i := fun i =>
    add_pos_of_pos_of_nonneg hs0 (mul_nonneg hxa (μ_nonneg S i))
  have hd2o : ∀ i, 0 < u + y.2.2.1 * S.μ i := fun i =>
    add_pos_of_pos_of_nonneg hu0 (mul_nonneg hya (μ_nonneg S i))
  have hd1i : ∀ j, 0 < s + x.2.2.2 * S.lam j := fun j =>
    add_pos_of_pos_of_nonneg hs0 (mul_nonneg hxc (lam_nonneg S j))
  have hd2i : ∀ j, 0 < u + y.2.2.2 * S.lam j := fun j =>
    add_pos_of_pos_of_nonneg hu0 (mul_nonneg hyc (lam_nonneg S j))
  have hU := pp_tout_eq Fp S x y hxa hya s u hs0 hu0 S.μ Fp.C.Sout (Sout_eq_spectral S)
  have hV := pp_tin_eq Fp S x y hxc hyc s u hs0 hu0 S.lam Fp.C.Sin (Sin_eq_spectral S)
  have hTo := pp_tout_eq Fp S x y hxa hya s u hs0 hu0 Fd Fm hFd
  have hTi := pp_tin_eq Fp S x y hxc hyc s u hs0 hu0 Gd Gm hGd
  -- the four coefficients
  set po : ℂ := K.z2 * (K.z1 * ∑ i, cM1 i * (κ1 i ^ 2 / ptDen K VType.out (κ1 i))) with hpo
  set pin : ℂ := K.z2 * (K.z1 * ∑ j, cM2 j * (κ2 j ^ 2 / ptDen K VType.inp (κ2 j))) with hpin
  set fo : ℂ := K.z2 * (K.z1 * ∑ i, cF i * (κ1 i / ptDen K VType.out (κ1 i))) with hfo
  set fin : ℂ := K.z1 * K.z2 * ∑ j, cG j * (κ2 j / ptDen K VType.inp (κ2 j)) with hfin
  have hpoE : po = ((-(Real.sqrt s * Real.sqrt u * toutT Fp.C B x y s u Fp.C.Sout) : ℝ) : ℂ) := by
    have h := pp_sum_ident s u x.2.2.1 y.2.2.1 K.z1 K.z2 (ptA1 K VType.out) (ptA2 K VType.out) S.μ
      (fun _ => (B : ℝ)⁻¹) 2 hd1o hd2o hg1o hg2o
    refine h.trans ?_
    congr 1
    rw [hU]
    have : ∑ i, (B : ℝ)⁻¹ * S.μ i ^ 2 / ((s + x.2.2.1 * S.μ i) * (u + y.2.2.1 * S.μ i)) =
        (B : ℝ)⁻¹ * ∑ i, S.μ i * S.μ i / ((s + x.2.2.1 * S.μ i) * (u + y.2.2.1 * S.μ i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [this]; ring
  have hpinE : pin = ((-(Real.sqrt s * Real.sqrt u * tinT Fp.C B x y s u Fp.C.Sin) : ℝ) : ℂ) := by
    have h := pp_sum_ident s u x.2.2.2 y.2.2.2 K.z1 K.z2 (ptA1 K VType.inp) (ptA2 K VType.inp) S.lam
      (fun _ => (B : ℝ)⁻¹) 2 hd1i hd2i hg1i hg2i
    refine h.trans ?_
    congr 1
    rw [hV]
    have : ∑ j, (B : ℝ)⁻¹ * S.lam j ^ 2 / ((s + x.2.2.2 * S.lam j) * (u + y.2.2.2 * S.lam j)) =
        (B : ℝ)⁻¹ * ∑ j, S.lam j * S.lam j / ((s + x.2.2.2 * S.lam j) * (u + y.2.2.2 * S.lam j)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this]; ring
  have hfoE : fo = ((-(Real.sqrt s * Real.sqrt u * toutT Fp.C B x y s u Fm) : ℝ) : ℂ) := by
    have h := pp_sum_ident s u x.2.2.1 y.2.2.1 K.z1 K.z2 (ptA1 K VType.out) (ptA2 K VType.out) S.μ
      (fun i => (B : ℝ)⁻¹ * Fd i) 1 hd1o hd2o hg1o hg2o
    simp only [pow_one] at h
    refine h.trans ?_
    congr 1
    rw [hTo]
    have : ∑ i, (B : ℝ)⁻¹ * Fd i * S.μ i / ((s + x.2.2.1 * S.μ i) * (u + y.2.2.1 * S.μ i)) =
        (B : ℝ)⁻¹ * ∑ i, Fd i * S.μ i / ((s + x.2.2.1 * S.μ i) * (u + y.2.2.1 * S.μ i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [this]; ring
  have hfinE : fin = ((-(Real.sqrt s * Real.sqrt u * tinT Fp.C B x y s u Gm) : ℝ) : ℂ) := by
    have h := pp_sum_ident s u x.2.2.2 y.2.2.2 K.z1 K.z2 (ptA1 K VType.inp) (ptA2 K VType.inp) S.lam
      (fun j => (B : ℝ)⁻¹ * Gd j) 1 hd1i hd2i hg1i hg2i
    simp only [pow_one] at h
    rw [hfin, mul_comm K.z1 K.z2, mul_assoc]
    refine h.trans ?_
    congr 1
    rw [hTi]
    have : ∑ j, (B : ℝ)⁻¹ * Gd j * S.lam j / ((s + x.2.2.2 * S.lam j) * (u + y.2.2.2 * S.lam j)) =
        (B : ℝ)⁻¹ * ∑ j, Gd j * S.lam j / ((s + x.2.2.2 * S.lam j) * (u + y.2.2.2 * S.lam j)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this]; ring
  -- the entries `𝖺`, `𝖽`
  have hA : ptM1 K VType.inp * ptM2 K VType.inp * ptEs K =
      ((-(Real.sqrt s * Real.sqrt u * x.2.1 * y.2.1 *
        pairedE P (cutoffXi Fp.β ℓ J R 1 g) (cutoffXi Fp.β ℓ J R 2 g) q1 q2) : ℝ) : ℂ) := by
    rw [hM1i, hM2i, hEs]
    push_cast
    linear_combination ((Real.sqrt s : ℂ) * (Real.sqrt u : ℂ) * (x.2.1 : ℂ) * (y.2.1 : ℂ) *
      (pairedE P (cutoffXi Fp.β ℓ J R 1 g) (cutoffXi Fp.β ℓ J R 2 g) q1 q2 : ℂ)) * Complex.I_sq
  have hD : ptM1 K VType.out * ptM2 K VType.out * ptEs K =
      ((-(Real.sqrt s * Real.sqrt u * x.1 * y.1 *
        pairedE P (cutoffXi Fp.β ℓ J R 1 g) (cutoffXi Fp.β ℓ J R 2 g) q1 q2) : ℝ) : ℂ) := by
    rw [hM1o, hM2o, hEs]
    push_cast
    linear_combination ((Real.sqrt s : ℂ) * (Real.sqrt u : ℂ) * (x.1 : ℂ) * (y.1 : ℂ) *
      (pairedE P (cutoffXi Fp.β ℓ J R 1 g) (cutoffXi Fp.β ℓ J R 2 g) q1 q2 : ℂ)) * Complex.I_sq
  obtain ⟨hΔe, hFe⟩ := pp_conv s u (toutT Fp.C B x y s u Fp.C.Sout) (tinT Fp.C B x y s u Fp.C.Sin)
    (toutT Fp.C B x y s u Fm) (tinT Fp.C B x y s u Gm)
    (pairedB P (cutoffXi Fp.β ℓ J R 1 g) (cutoffXi Fp.β ℓ J R 2 g) q1 q2)
    (pairedE P (cutoffXi Fp.β ℓ J R 1 g) (cutoffXi Fp.β ℓ J R 2 g) q1 q2) x.1 y.1 x.2.1 y.2.1 hs0 hu0
    po pin fo fin _ _ (ptBs K) hpoE hpinE hfoE hfinE hA hD hBs
  have hΔ : (1 - po * (ptM1 K VType.inp * ptM2 K VType.inp * ptEs K)) *
      (1 - pin * (ptM1 K VType.out * ptM2 K VType.out * ptEs K)) - po * pin * ptBs K ^ 2 ≠ 0 := by
    rw [hΔe]
    exact_mod_cast hdelta
  have hsum := (lem_app_vol_closed_path_i cert γstar CSig Fp S hS' hout hin ℓ J R hg Fd Gd s u hs hu).1
  rw [pp_top_reduction P Fp.β ℓ J R B Fd Gd S.μ S.lam g s u hsum hPtop]
  rw [pt_abstract K cF cM1 κ1 cM2 cG κ2 ρ hρ' hMfo' hMfi' hMg' h1o h2o h1i h2i (hBm _ hout').1
    (hBm _ hinp').1 so1' so2' si1' si2' to1' to2' ti1' ti2' hWmo hWmi po pin fo fin rfl rfl rfl rfl hΔ]
  rw [hFe, hΔe, ← Complex.ofReal_div]
  congr 1
  have hx' : branchPt (profileF P (cutoffXi Fp.β ℓ J R 1 g)) Fp.C B s = x := rfl
  have hy' : branchPt (profileF P (cutoffXi Fp.β ℓ J R 2 g)) Fp.C B u = y := rfl
  unfold profileKernel profileDelta closedDelta
  simp only [hx', hy', hq1def, hq2def]
  ring


/-- `lem:app-vol-closed-path`(ii), snapshot `cr-2026-10-23`. Declaration of record, the identification of the
path sum with the closed-form kernel `𝔎^{J,R}[F,G](s,u)` of the cutoff paired profile, together with
`Δ^{J,R}(s,u) ≠ 0` (the identity presupposes it; see the open question in the result file). Same
hypotheses as `lem_app_vol_closed_path_i`, with the matrices `Fm = U_out diag(Fd) U_outᵀ`,
`Gm = V_in diag(Gd) V_inᵀ`.

LaTeX (`sections/04-volatility/section.tex` l.2359–2368, verbatim):
```latex
\begin{lemma}[Path decomposition]\label{lem:app-vol-closed-path}
Let $\Sigmaout,\Sigmain\ne0$, and let $s,u\ge s_R$. The family
$\{Z(T)\operatorname{val}(T,\mathfrak a):a_1,a_2\ge0,\ T\in\mathcal T_{a_1,a_2},\ \mathfrak a\}$ is absolutely summable,
and its sum is
\[
\mathfrak k^{J,R}_\ell[F,G](s,u)\defeq\mathfrak R^{J,R}_\ell[F,G](\iota_s,\iota_u).
\]
This sum equals $\mathfrak K^{J,R}[F,G](s,u)$ of \cref{eqn:app-vol-closed-profile-kernel},
formed with the branch point of $\xi_1$ at $s$ and of $\xi_2$ at $u$.
\end{lemma}
```
-/
theorem lem_app_vol_closed_path_ii {Ω : Type} [MeasurableSpace Ω] {m n B : ℕ}
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) (Fp : FrozenParams m n B)
    (S : SpectralData Fp.C) (hS : SizeFin Fp.C B γstar CSig)
    (hout : Fp.C.Sout ≠ 0) (hin : Fp.C.Sin ≠ 0)
    {P : Measure Ω} [IsProbabilityMeasure P] (ℓ J : ℕ) (R : ℝ)
    {g : ℤ → Ω → ℝ} (hg : IsStdGaussianFamily P g)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (Fm : Matrix (Fin m) (Fin m) ℝ) (Gm : Matrix (Fin n) (Fin n) ℝ)
    (hFd : Fm = S.uOut * Matrix.diagonal Fd * S.uOutᵀ)
    (hGd : Gm = S.vIn * Matrix.diagonal Gd * S.vInᵀ)
    (s u : ℝ) (hs : sRad cert γstar CSig R ≤ s) (hu : sRad cert γstar CSig R ≤ u) :
    ∑' q : PathIdx m n J ℓ, pathTerm P Fp.β ℓ J R B Fd Gd S.μ S.lam g s u q =
        ((profileKernel P Fp.C B (cutoffXi Fp.β ℓ J R 1 g) (cutoffXi Fp.β ℓ J R 2 g) Fm Gm s u : ℝ) : ℂ) ∧
    profileDelta P Fp.C B (cutoffXi Fp.β ℓ J R 1 g) (cutoffXi Fp.β ℓ J R 2 g) s u ≠ 0 := by
  by_cases hR : R ≤ 0
  · exact pd4_path_nonpos cert γstar CSig Fp S hS hout hin ℓ J R hR hg
      Fd Gd Fm Gm s u hs hu
  · have hRpos : 0 < R := lt_of_not_ge hR
    have hdelta := pd_cutoff_delta_ne cert γstar CSig Fp hout hin
      ℓ J hRpos hg s u hs hu
    exact ⟨pt_main cert γstar CSig Fp S hS hout hin ℓ J R hg Fd Gd Fm Gm hFd hGd s u hs hu hdelta,
      hdelta⟩

end Muon.Volatility

end

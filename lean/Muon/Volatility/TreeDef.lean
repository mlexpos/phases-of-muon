import Muon.Volatility.Defs
import Muon.Volatility.Replication

/-!
# Appendix D, part 11: the tree-moment response

Work package L-D.11 (interface draft). Snapshot `cr-2026-10-23`. Source of record:
`sections/04-volatility/section.tex`: `eqn:app-vol-word` (l.1012–1015), `eqn:app-vol-tree-coefficients`
(l.987–990), `eqn:app-vol-truncated-moments` (l.993–995), `def:app-vol-tree` (l.1025–1057) and the
paragraph after it (l.1059–1074, the shortest word, linearity and the limit), and the replication
invariance sentence of `lem:app-vol-tree-closure` (l.1083–1084). Card: `sections/04-volatility/CARD.md`
§2 (row "Tree data"), §3 (row `def:app-vol-tree`), §5 (row L-D.11), §6 (R3, R11, R5).

Reused, not redefined: `Muon.Covariances`, `Muon.Foundations` `emaW`, `sPow` (`Muon.Foundations.Conventions`);
`Muon.Setup.FrozenParams`; `def_app_vol_product`,
`indepSpaceLaw` (`Muon.Volatility.Defs`, L-D.2); `replIdx` (`Muon.Volatility.Replication`, L-D.8).

Encoding decisions (Lean representation of the source's polygon):
* Test matrices enter through their diagonal entries `Fd : Fin m → ℝ`, `Gd : Fin n → ℝ` in the
  eigenbases `u_i`, `v_j`, and the covariance spectra through `μ : Fin m → ℝ`, `lam : Fin n → ℝ`. The
  response depends on `F`, `G` only through these (every quantity in the tree rule is spectral).
* Odd polynomials `f₁, f₂` are `Polynomial ℝ`; the bilinear extension reads their odd coefficients
  `coeff (2a+1)`. The extension is the paper's on odd polynomials; the value on non-odd polynomials is
  the one of the odd part and is not used.
* Polygon: `k = 2a+2b+2` external vertices `e_s` and latent vertices `l_s`, `s : Fin k` (0-based, so the
  paper's `e_r` is `e_{r-1}`). Vertex type `TreeVtx k = Fin k ⊕ Fin k` (`inl` external, `inr` latent).
  The factor `X_s` is untransposed iff `s` even (`treeUntransposed`); its label is `1` iff `s ≤ 2a`
  (`treeLabel`); its z-edge goes to the output endpoint `treeOutV s`, its w-edge to the input endpoint
  `treeInV s`. The output vertex `e_k` carries `F` (`treeFMark`), the input vertex `e_{2a+1}` carries `G`
  (`treeGMark`).
* Perfect matchings of the `k` z-edges (resp. w-edges) are fixed-point-free involutions `TreeMatch k`.
* The quotient is `Quotient` of the `Relation.EqvGen` of the identifications `treeRel`. Retained iff
  `Nat.card` of the quotient is `k+1` (the paper's "that is" clause).
* The cutoff coefficients `ϖ_{l,α}` (`treeVarpi`) are indexed by `α ∈ 𝒜 = {-J,…,ℓ} ⊂ ℤ`, the batch
  labels `-j` (age `j`) and `m` (time `t+1+m`), as `Finset.Icc (-(J:ℤ)) ℓ`.
* The response is a `Finset` sum over pairs of matchings, with `if` on retention; the class product is
  over `Quotient` (finite, via classical decidability).
* Momentum `β` is a real parameter; the limit and exact-value statements carry the frozen-model standing
  assumption `0 ≤ β < 1` (from `FrozenParams.hβ`), which the source uses but does not repeat in the
  paragraph.
-/

noncomputable section

open scoped Matrix MatrixOrder
open MeasureTheory ProbabilityTheory Filter Topology Polynomial
open Muon Muon.Setup

namespace Muon.Volatility

variable {m n B : ℕ}

/-! ## The word `W_{a,b}` and its factor pattern -/

/-- `eqn:app-vol-word`, snapshot `cr-2026-10-23`. The word
`W_{a,b} = F (K₁K₁ᵀ)^a K₁ G K₂ᵀ (K₂K₂ᵀ)^b`, verbatim from `section.tex`:
```latex
\begin{equation}\label{eqn:app-vol-word}
\mathsf W_{a,b}\defeq F\,(\mathsf K_1\mathsf K_1^\T)^a\mathsf K_1\,G\,\mathsf K_2^\T(\mathsf K_2\mathsf K_2^\T)^b
\end{equation}
is a cyclic product of $k\defeq2a+2b+2$ factors $X_1,\dots,X_k$: $X_r=\mathsf K_1$
```
-/
def treeWord (F : Mat m m) (G : Mat n n) (K₁ K₂ : Mat m n) (a b : ℕ) : Mat m m :=
  F * (K₁ * K₁ᵀ) ^ a * K₁ * G * K₂ᵀ * (K₂ * K₂ᵀ) ^ b

/-- Number of factors of `W_{a,b}`: `k = 2a + 2b + 2` (`eqn:app-vol-word`). -/
abbrev treeK (a b : ℕ) : ℕ := 2 * a + 2 * b + 2

/-- Vertices of the polygon: `inl s` is the external vertex `e_s`, `inr s` the latent vertex `l_s`
(0-based indices `s ∈ Fin k`). -/
abbrev TreeVtx (k : ℕ) := Fin k ⊕ Fin k

/-- The factor `X_s` (0-based) is untransposed iff `s` is even, i.e. the paper's `X_r = K_l` for odd
`r` and `X_r = K_l^T` for even `r` (`eqn:app-vol-word`). -/
abbrev treeUntransposed {k : ℕ} (s : Fin k) : Prop := s.val % 2 = 0

/-- Label `l_s ∈ {1,2}` of the factor `X_s`: `1` for `s ≤ 2a` (paper `r ≤ 2a+1`), `2` otherwise. -/
def treeLabel {k : ℕ} (a : ℕ) (s : Fin k) : ℕ := if s.val ≤ 2 * a then 1 else 2

/-- The cyclic predecessor `s - 1 (mod k)`. -/
def treePrev {k : ℕ} (s : Fin k) : Fin k :=
  ⟨(s.val + (k - 1)) % k, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt)⟩

open Classical in
/-- Output endpoint of the z-edge of `X_s`: the vertex `e_{s-1}` on its left if untransposed, `e_s`
on its right otherwise (`def:app-vol-tree`(1): the vertex `e_r` sits between `X_r` and `X_{r+1}`). -/
def treeOutV {k : ℕ} (s : Fin k) : Fin k := if treeUntransposed s then treePrev s else s

open Classical in
/-- Input endpoint of the w-edge of `X_s` (the other side of `treeOutV`). -/
def treeInV {k : ℕ} (s : Fin k) : Fin k := if treeUntransposed s then s else treePrev s

/-- The external vertex carrying the mark `F`: the output vertex `e_k` (0-based `k-1`). -/
def treeFMark (a b : ℕ) : Fin (treeK a b) := ⟨2 * a + 2 * b + 1, by unfold treeK; omega⟩

/-- The external vertex carrying the mark `G`: the input vertex `e_{2a+1}` (0-based `2a`). -/
def treeGMark (a b : ℕ) : Fin (treeK a b) := ⟨2 * a, by unfold treeK; omega⟩

/-! ## Cutoff coefficients and truncated moments -/

/-- `eqn:app-vol-tree-coefficients`, snapshot `cr-2026-10-23`. The paired coefficients
`ϖ_{l,α}` for the label `α ∈ ℤ` (`α = -j` is the batch of age `j`, `α = m ≥ 1` the batch of time
`t+1+m`), verbatim from `section.tex`:
```latex
\begin{equation}\label{eqn:app-vol-tree-coefficients}
(\varpi_{1,-j},\varpi_{2,-j})\defeq(\emaw j,\bmom^\ell\emaw j),\qquad
(\varpi_{1,m},\varpi_{2,m})\defeq(0,\emaw{\ell-m}),
\end{equation}
```
-/
def treeVarpi (β : ℝ) (ℓ l : ℕ) (α : ℤ) : ℝ :=
  if α ≤ 0 then
    (if l = 1 then Muon.emaW β α.natAbs else β ^ ℓ * Muon.emaW β α.natAbs)
  else if l = 1 then 0 else Muon.emaW β (ℓ - α.toNat)

/-- `eqn:app-vol-truncated-moments`, snapshot `cr-2026-10-23`. The truncated Gaussian moments
`m_d(R) = 𝔼[g^d 1_{|g| ≤ R}]` for `d ≥ 1` and `m_0(R) = 1`, under `g ∼ N(0,1)`, verbatim from
`section.tex`:
```latex
\begin{equation}\label{eqn:app-vol-truncated-moments}
m_d(R)\defeq\EE\big[g^d\mathbf 1_{\abs g\le R}\big]\quad(d\ge1),\qquad m_0(R)\defeq1,
\end{equation}
```
-/
def treeTruncMoment (d : ℕ) (R : ℝ) : ℝ :=
  if d = 0 then 1 else ∫ x, (if |x| ≤ R then x ^ d else 0) ∂(gaussianReal 0 1)

/-! ## Matchings, quotient and retention -/

/-- Perfect matchings of the `k` edges of one kind, as fixed-point-free involutions of `Fin k`
(`def:app-vol-tree`(2)). -/
abbrev TreeMatch (k : ℕ) := {σ : Equiv.Perm (Fin k) // (∀ x, σ (σ x) = x) ∧ ∀ x, σ x ≠ x}

/-- The identifications of a pairing `p = (π, π')` (`def:app-vol-tree`(2)): for a matched pair
`{s, π s}` of z-edges, the latent endpoints `l_s, l_{π s}` and the output endpoints are identified;
for a matched pair of w-edges, the latent endpoints and the input endpoints are identified. -/
def treeRel {k : ℕ} (p : TreeMatch k × TreeMatch k) : TreeVtx k → TreeVtx k → Prop :=
  fun x y => ∃ s : Fin k,
    (x = Sum.inr s ∧ y = Sum.inr (p.1.1 s)) ∨ (x = Sum.inr s ∧ y = Sum.inr (p.2.1 s)) ∨
    (x = Sum.inl (treeOutV s) ∧ y = Sum.inl (treeOutV (p.1.1 s))) ∨
    (x = Sum.inl (treeInV s) ∧ y = Sum.inl (treeInV (p.2.1 s)))

/-- The setoid generated by the identifications of a pairing. -/
def treeSetoid {k : ℕ} (p : TreeMatch k × TreeMatch k) : Setoid (TreeVtx k) :=
  Relation.EqvGen.setoid (treeRel p)

/-- The vertex class of `x` in the quotient multigraph of the pairing `p`. -/
def treeMk {k : ℕ} (p : TreeMatch k × TreeMatch k) (x : TreeVtx k) : Quotient (treeSetoid p) :=
  Quotient.mk (treeSetoid p) x

open Classical in
/-- A pairing is retained iff its quotient has exactly `k + 1` vertices, the paper's "tree, that is"
(`def:app-vol-tree`(2)). -/
def treeRetained {k : ℕ} (p : TreeMatch k × TreeMatch k) : Prop :=
  Nat.card (Quotient (treeSetoid p)) = k + 1

/-! ## Class factors and the response -/

open Classical in
/-- Factor of one vertex class `V` (`def:app-vol-tree`(3)). An external class containing an
output vertex (odd index) contributes `B⁻¹ ∑_i μ_i^{p_V} F_i^{m_V}`; an input class contributes
`B⁻¹ ∑_j λ_j^{p_V} G_j^{n_V}`; a latent class with factor set `S_V` contributes
`m_{|S_V|}(R) ∑_{α} ∏_{r ∈ S_V} ϖ_{l_r,α}`. -/
def treeClassFactor {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (a b : ℕ)
    (p : TreeMatch (treeK a b) × TreeMatch (treeK a b)) (V : Quotient (treeSetoid p)) : ℝ :=
  if ∃ e : Fin (treeK a b), treeMk p (Sum.inl e) = V then
    let pV : ℕ := (Finset.univ.filter fun e : Fin (treeK a b) => treeMk p (Sum.inl e) = V).card
    if ∃ e : Fin (treeK a b), treeMk p (Sum.inl e) = V ∧ e.val % 2 = 1 then
      let mV : ℕ := if treeMk p (Sum.inl (treeFMark a b)) = V then 1 else 0
      ((B : ℝ))⁻¹ * ∑ i : Fin m, μ i ^ pV * Fd i ^ mV
    else
      let nV : ℕ := if treeMk p (Sum.inl (treeGMark a b)) = V then 1 else 0
      ((B : ℝ))⁻¹ * ∑ j : Fin n, lam j ^ pV * Gd j ^ nV
  else
    let S : Finset (Fin (treeK a b)) := Finset.univ.filter fun r => treeMk p (Sum.inr r) = V
    treeTruncMoment S.card R *
      ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ), ∏ r ∈ S, treeVarpi β ℓ (treeLabel a r) α

open Classical in
/-- The response on the monomials `(x^{2a+1}, x^{2b+1})`: the sum over all pairs of matchings of the
retained pairings of the products of their class factors (`def:app-vol-tree`(4)). Non-retained
pairings contribute `0`. -/
def treeMono {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (a b : ℕ) : ℝ :=
  ∑ p : TreeMatch (treeK a b) × TreeMatch (treeK a b),
    if treeRetained p then
      ∏ V : Quotient (treeSetoid p), treeClassFactor β ℓ J R B μ lam Fd Gd a b p V
    else 0

/-- `def:app-vol-tree`, snapshot `cr-2026-10-23`. Declaration of record: the tree-moment response
`𝔑^{J,R}_ℓ[F,G](f₁,f₂)` of the odd polynomials `f₁, f₂`, given by the monomial response `treeMono` and
its bilinear extension, with `F`, `G` through their eigenvalue data `Fd`, `Gd` and the covariance
spectra `μ`, `lam`, batch size `B`, momentum `β`, lag `ℓ`, history cutoff `J`, scalar cutoff `R`.
Verbatim LaTeX of the definition:
```latex
\begin{definition}[Tree moment equations]\label{def:app-vol-tree}
Fix $(\ell,J,R)$, diagonal $F,G$, and integers $a,b\ge0$, with $k=2a+2b+2$ and
the factors $X_r$ and labels $l_r$ of \cref{eqn:app-vol-word}.
\begin{enumerate}[label=(\arabic*)]
\item \emph{The polygon.} Take $k$ external vertices $\mathsf e_1,\dots,\mathsf e_k$
and $k$ latent vertices $\mathsf l_1,\dots,\mathsf l_k$, indices modulo $k$. The
vertex $\mathsf e_r$ sits between $X_r$ and $X_{r+1}$; it has the input type
if $X_r$ is untransposed and the output type otherwise. The output vertex
$\mathsf e_k$ carries the mark $F$ and the input vertex $\mathsf e_{2a+1}$ carries
the mark $G$. Each factor $X_r$ contributes a $z$-edge joining $\mathsf l_r$ to
the output vertex among $\mathsf e_{r-1},\mathsf e_r$, and a $w$-edge joining $\mathsf l_r$
to the input vertex among them.
\item \emph{Pairings.} A pairing is a pair $(\pi,\pi')$ of a perfect matching
$\pi$ of the $k$ $z$-edges and a perfect matching $\pi'$ of the $k$ $w$-edges.
For each matched pair of edges, identify their two latent endpoints and their
two external endpoints. The quotient multigraph has one edge for each matched
pair, hence $k$ edges, and it is connected. The pairing is \emph{retained} if
the quotient is a tree, that is, if it has exactly $k+1$ vertices.
\item \emph{Values.} For a retained pairing, every vertex class $V$ of the
quotient contributes a factor. An output class $V$ containing $p_V$ original
external vertices contributes $B^{-1}\sum_i\mu_i^{p_V}F_i^{m_V}$, where $m_V=1$ if
$\mathsf e_k\in V$ and $m_V=0$ otherwise. An input class contributes
$B^{-1}\sum_j\lambda_j^{p_V}G_j^{n_V}$, with $n_V=1$ if $\mathsf e_{2a+1}\in V$ and
$n_V=0$ otherwise. A latent class $V$ with set of factors $S_V\subset\{1,\dots,k\}$
contributes
\[
m_{\abs{S_V}}(R)\sum_{\alpha\in\mathcal A}\prod_{r\in S_V}\varpi_{l_r,\alpha}.
\]
\item \emph{The response.} $\mathfrak R^{J,R}_\ell[F,G](x^{2a+1},x^{2b+1})$ is the sum,
over the retained pairings, of the products of the factors of their classes.
It is extended bilinearly to pairs of odd polynomials.
\end{enumerate}
\end{definition}
```
-/
def def_app_vol_tree {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (f₁ f₂ : Polynomial ℝ) : ℝ :=
  ∑ a ∈ Finset.range (f₁.natDegree + 1), ∑ b ∈ Finset.range (f₂.natDegree + 1),
    f₁.coeff (2 * a + 1) * f₂.coeff (2 * b + 1) * treeMono β ℓ J R B μ lam Fd Gd a b

/-! ## Helper statements of the definition (paragraph after `def:app-vol-tree`, l.1059–1074)

Helper statements, proofs sorried (card §3 row `def:app-vol-tree`). -/

/-! ### Fixed-point-free involutions (used by the pairing counts) -/

open Finset in
private lemma tree_fpf_card_lt_eq {k : ℕ} (σ : Equiv.Perm (Fin k))
    (hinv : ∀ x, σ (σ x) = x) (hfp : ∀ x, σ x ≠ x) :
    (univ.filter fun s : Fin k => s.val < (σ s).val).card =
      (univ.filter fun s : Fin k => ¬ (s.val < (σ s).val)).card := by
  apply Finset.card_nbij' σ σ
  · intro s hs
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    rw [hinv]
    omega
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    rw [hinv]
    have hne : (σ t).val ≠ t.val := fun h => hfp t (Fin.ext h)
    omega
  · intro x _
    exact hinv x
  · intro x _
    exact hinv x

open Finset in
private lemma tree_fpf_iff_cycleType {k : ℕ} (σ : Equiv.Perm (Fin k)) (p : ℕ) (hk : k = 2 * p) :
    ((∀ x, σ (σ x) = x) ∧ ∀ x, σ x ≠ x) ↔ σ.cycleType = Multiset.replicate p 2 := by
  constructor
  · rintro ⟨hinv, hfp⟩
    have hsq : σ ^ 2 = 1 := by
      ext x
      simp [pow_two, hinv]
    have hall : ∀ c ∈ σ.cycleType, c = 2 := (Equiv.Perm.pow_prime_eq_one_iff (p := 2)).1 hsq
    have hc : σ.cycleType = Multiset.replicate σ.cycleType.card 2 := Multiset.eq_replicate.2 ⟨rfl, hall⟩
    have hsup : σ.support = univ := Finset.eq_univ_iff_forall.2 fun x => Equiv.Perm.mem_support.2 (hfp x)
    have hs : σ.cycleType.sum = k := by
      rw [Equiv.Perm.sum_cycleType, hsup, Finset.card_univ, Fintype.card_fin]
    have hs2 := congrArg Multiset.sum hc
    rw [Multiset.sum_replicate, smul_eq_mul] at hs2
    have hcard : σ.cycleType.card = p := by omega
    rw [hcard] at hc
    exact hc
  · intro hc
    have hall : ∀ c ∈ σ.cycleType, c = 2 := by
      rw [hc]
      intro c hc'
      exact Multiset.eq_of_mem_replicate hc'
    have hsq : σ ^ 2 = 1 := (Equiv.Perm.pow_prime_eq_one_iff (p := 2)).2 hall
    have hinv : ∀ x, σ (σ x) = x := by
      intro x
      have := congrArg (fun τ : Equiv.Perm (Fin k) => τ x) hsq
      simpa [pow_two] using this
    have hs : σ.cycleType.sum = k := by
      rw [hc, Multiset.sum_replicate, smul_eq_mul, hk]; ring
    rw [Equiv.Perm.sum_cycleType] at hs
    have hsup : σ.support = univ := by
      apply Finset.eq_univ_of_card
      rw [hs, Fintype.card_fin]
    exact ⟨hinv, fun x => Equiv.Perm.mem_support.1 (by rw [hsup]; exact mem_univ x)⟩

open Finset in
private lemma tree_fpf_card {k p : ℕ} (hp : 1 ≤ p) (hk : k = 2 * p) :
    Nat.card {σ : Equiv.Perm (Fin k) // (∀ x, σ (σ x) = x) ∧ ∀ x, σ x ≠ x} =
      (k - 1).doubleFactorial := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [show (univ.filter fun σ : Equiv.Perm (Fin k) => (∀ x, σ (σ x) = x) ∧ ∀ x, σ x ≠ x) =
      univ.filter fun σ : Equiv.Perm (Fin k) => σ.cycleType = Multiset.replicate p 2 from
    Finset.filter_congr fun σ _ => tree_fpf_iff_cycleType σ p hk]
  rw [Equiv.Perm.card_of_cycleType]
  have hcond : (Multiset.replicate p 2).sum ≤ Fintype.card (Fin k) ∧
      ∀ a ∈ Multiset.replicate p 2, 2 ≤ a := by
    refine ⟨?_, fun a ha => le_of_eq (Multiset.eq_of_mem_replicate ha).symm⟩
    rw [Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin]
    omega
  rw [if_pos hcond]
  have hsum : (Multiset.replicate p 2).sum = 2 * p := by
    rw [Multiset.sum_replicate, smul_eq_mul]; ring
  have hprod : (Multiset.replicate p 2).prod = 2 ^ p := by
    rw [Multiset.prod_replicate]
  have hfin : (Multiset.replicate p 2).toFinset = {2} := by
    rw [Multiset.toFinset_replicate]
    simp [Nat.pos_iff_ne_zero.mp hp]
  have hcount : (Multiset.replicate p 2).count 2 = p := Multiset.count_replicate_self 2 p
  rw [Fintype.card_fin, hsum, hprod, hfin, Finset.prod_singleton, hcount]
  have h0 : k - 2 * p = 0 := by omega
  have hkd : Nat.factorial k = Nat.doubleFactorial (k - 1) * (2 ^ p * Nat.factorial p) := by
    have h1 := Nat.factorial_eq_mul_doubleFactorial (k - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at h1
    have h2 := Nat.doubleFactorial_two_mul p
    rw [← hk] at h2
    rw [h1, h2, mul_comm]
  rw [h0, Nat.factorial_zero, one_mul, hkd, Nat.mul_div_cancel _ (by positivity)]

/-- Helper of `def:app-vol-tree`, snapshot `cr-2026-10-23`: the count of pairings, `((k-1)!!)^2`
pairs (l.1059–1061). Verbatim:
```latex
The definition is a finite computation for each pair $(a,b)$: enumerate the
$((k-1)!!)^2$ pairings, form the quotient, keep it if it has $k+1$ vertices,
and multiply the factors. Its only inputs are the normalized traces
```
Sorried. -/
theorem def_app_vol_tree_pairings_card (a b : ℕ) :
    Nat.card (TreeMatch (treeK a b) × TreeMatch (treeK a b)) =
      ((treeK a b - 1).doubleFactorial) ^ 2 := by
  rw [Nat.card_prod]
  have h := tree_fpf_card (k := treeK a b) (p := a + b + 1) (by omega) (by unfold treeK; ring)
  rw [h, sq]

/-- Helper of `def:app-vol-tree`(2), snapshot `cr-2026-10-23`: the quotient multigraph has one edge
for each matched pair, hence `k` edges: the number of matched pairs of z-edges plus those of w-edges is
`k` (l.1030–1043). Verbatim definition:
```latex
\begin{definition}[Tree moment equations]\label{def:app-vol-tree}
Fix $(\ell,J,R)$, diagonal $F,G$, and integers $a,b\ge0$, with $k=2a+2b+2$ and
the factors $X_r$ and labels $l_r$ of \cref{eqn:app-vol-word}.
\begin{enumerate}[label=(\arabic*)]
\item \emph{The polygon.} Take $k$ external vertices $\mathsf e_1,\dots,\mathsf e_k$
and $k$ latent vertices $\mathsf l_1,\dots,\mathsf l_k$, indices modulo $k$. The
vertex $\mathsf e_r$ sits between $X_r$ and $X_{r+1}$; it has the input type
if $X_r$ is untransposed and the output type otherwise. The output vertex
$\mathsf e_k$ carries the mark $F$ and the input vertex $\mathsf e_{2a+1}$ carries
the mark $G$. Each factor $X_r$ contributes a $z$-edge joining $\mathsf l_r$ to
the output vertex among $\mathsf e_{r-1},\mathsf e_r$, and a $w$-edge joining $\mathsf l_r$
to the input vertex among them.
\item \emph{Pairings.} A pairing is a pair $(\pi,\pi')$ of a perfect matching
$\pi$ of the $k$ $z$-edges and a perfect matching $\pi'$ of the $k$ $w$-edges.
For each matched pair of edges, identify their two latent endpoints and their
two external endpoints. The quotient multigraph has one edge for each matched
pair, hence $k$ edges, and it is connected. The pairing is \emph{retained} if
the quotient is a tree, that is, if it has exactly $k+1$ vertices.
\item \emph{Values.} For a retained pairing, every vertex class $V$ of the
quotient contributes a factor. An output class $V$ containing $p_V$ original
external vertices contributes $B^{-1}\sum_i\mu_i^{p_V}F_i^{m_V}$, where $m_V=1$ if
$\mathsf e_k\in V$ and $m_V=0$ otherwise. An input class contributes
$B^{-1}\sum_j\lambda_j^{p_V}G_j^{n_V}$, with $n_V=1$ if $\mathsf e_{2a+1}\in V$ and
$n_V=0$ otherwise. A latent class $V$ with set of factors $S_V\subset\{1,\dots,k\}$
contributes
\[
m_{\abs{S_V}}(R)\sum_{\alpha\in\mathcal A}\prod_{r\in S_V}\varpi_{l_r,\alpha}.
\]
\item \emph{The response.} $\mathfrak R^{J,R}_\ell[F,G](x^{2a+1},x^{2b+1})$ is the sum,
over the retained pairings, of the products of the factors of their classes.
It is extended bilinearly to pairs of odd polynomials.
\end{enumerate}
\end{definition}
```
Sorried. -/
theorem def_app_vol_tree_edges (a b : ℕ) (p : TreeMatch (treeK a b) × TreeMatch (treeK a b)) :
    (Finset.univ.filter fun s : Fin (treeK a b) => s.val < (p.1.1 s).val).card +
      (Finset.univ.filter fun s : Fin (treeK a b) => s.val < (p.2.1 s).val).card = treeK a b := by
  have h1 := tree_fpf_card_lt_eq p.1.1 p.1.2.1 p.1.2.2
  have h2 := tree_fpf_card_lt_eq p.2.1 p.2.2.1 p.2.2.2
  have e1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (treeK a b))))
    (fun s : Fin (treeK a b) => s.val < (p.1.1 s).val)
  have e2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (treeK a b))))
    (fun s : Fin (treeK a b) => s.val < (p.2.1 s).val)
  simp only [Finset.card_univ, Fintype.card_fin] at e1 e2
  omega

/-- Private helper: the identifications preserve the side (latent / external) of a vertex. -/
private lemma tree_setoid_isLeft {k : ℕ} (p : TreeMatch k × TreeMatch k) {x y : TreeVtx k}
    (h : treeSetoid p x y) : x.isLeft = y.isLeft := by
  change Relation.EqvGen (treeRel p) x y at h
  induction h with
  | rel x y hxy =>
    unfold treeRel at hxy
    obtain ⟨s, h1 | h1 | h1 | h1⟩ := hxy <;> obtain ⟨h1a, h1b⟩ := h1 <;>
      subst h1a <;> subst h1b <;> rfl
  | refl => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- Private helper: `s` and `s-1` are each one of the two endpoints of the factor `X_s`. -/
private lemma tree_out_in {k : ℕ} (s : Fin k) :
    (s = treeOutV s ∨ s = treeInV s) ∧ (treePrev s = treeOutV s ∨ treePrev s = treeInV s) := by
  unfold treeOutV treeInV
  split_ifs <;> simp

/-- Private helper: the cyclic predecessor of `j+1` is `j` when `j+1 < k`. -/
private lemma tree_prev_succ (k j : ℕ) (h : j + 1 < k) :
    treePrev (⟨j + 1, h⟩ : Fin k) = ⟨j, by omega⟩ := by
  apply Fin.ext
  change (j + 1 + (k - 1)) % k = j
  have e : j + 1 + (k - 1) = j + k := by omega
  rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (show j < k by omega)]

/-- Private helper: adjacency of a latent vertex with the external vertex of one of its endpoints. -/
private lemma tree_adj_of {k : ℕ} (p : TreeMatch k × TreeMatch k) (s t : Fin k)
    (ht : t = treeOutV s ∨ t = treeInV s) :
    (SimpleGraph.fromRel fun x y : Quotient (treeSetoid p) =>
      ∃ s : Fin k,
        (x = treeMk p (Sum.inr s) ∧ y = treeMk p (Sum.inl (treeOutV s))) ∨
        (x = treeMk p (Sum.inr s) ∧ y = treeMk p (Sum.inl (treeInV s)))).Adj
      (treeMk p (Sum.inr s)) (treeMk p (Sum.inl t)) := by
  rw [SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl ⟨s, ?_⟩⟩
  · intro h
    unfold treeMk at h
    have h' := tree_setoid_isLeft p (Quotient.exact h)
    simp at h'
  · rcases ht with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩

/-- Private helper: a connected graph is obtained from a chain of adjacencies along a cycle
`I 0 - E 0 - I 1 - E 1 - ...` covering all vertices. -/
private lemma tree_chain_connected {V : Type*} (G : SimpleGraph V) {k : ℕ} (hk : 0 < k)
    (I E : Fin k → V) (hA : ∀ s, G.Adj (I s) (E s))
    (hB : ∀ (j : ℕ) (h : j + 1 < k), G.Adj (I ⟨j + 1, h⟩) (E ⟨j, by omega⟩))
    (hcov : ∀ v : V, (∃ s, v = I s) ∨ (∃ t, v = E t)) : G.Connected := by
  have chain : ∀ j (hj : j < k), G.Reachable (I ⟨0, hk⟩) (I ⟨j, hj⟩) := by
    intro j
    induction j with
    | zero => intro _; exact SimpleGraph.Reachable.refl _
    | succ j ih =>
      intro hj
      have h1 : G.Reachable (I ⟨0, hk⟩) (I ⟨j, by omega⟩) := ih (by omega)
      have h2 : G.Reachable (I ⟨j, by omega⟩) (E ⟨j, by omega⟩) := (hA ⟨j, by omega⟩).reachable
      have h3 : G.Reachable (E ⟨j, by omega⟩) (I ⟨j + 1, hj⟩) := (hB j hj).reachable.symm
      exact h1.trans (h2.trans h3)
  have hr : ∀ w, G.Reachable (I ⟨0, hk⟩) w := by
    intro w
    rcases hcov w with ⟨s, rfl⟩ | ⟨t, rfl⟩
    · exact chain s.val s.isLt
    · exact (chain t.val t.isLt).trans (hA t).reachable
  rw [SimpleGraph.connected_iff]
  exact ⟨fun u v => (hr u).symm.trans (hr v), ⟨I ⟨0, hk⟩⟩⟩

/-- Private helper: the quotient multigraph of every pairing is connected (assembled from
`tree_chain_connected`). -/
private lemma tree_quot_connected {k : ℕ} (hk : 0 < k) (p : TreeMatch k × TreeMatch k) :
    (SimpleGraph.fromRel fun x y : Quotient (treeSetoid p) =>
      ∃ s : Fin k,
        (x = treeMk p (Sum.inr s) ∧ y = treeMk p (Sum.inl (treeOutV s))) ∨
        (x = treeMk p (Sum.inr s) ∧ y = treeMk p (Sum.inl (treeInV s)))).Connected := by
  refine tree_chain_connected _ hk (fun s => treeMk p (Sum.inr s))
    (fun t => treeMk p (Sum.inl t)) (fun s => tree_adj_of p s s (tree_out_in s).1)
    (fun j h => ?_) (fun v => ?_)
  · have hp := (tree_out_in (⟨j + 1, h⟩ : Fin k)).2
    rw [tree_prev_succ k j h] at hp
    exact tree_adj_of p _ _ hp
  · obtain ⟨x, rfl⟩ := Quotient.exists_rep v
    cases x with
    | inl t => exact Or.inr ⟨t, rfl⟩
    | inr s => exact Or.inl ⟨s, rfl⟩

/-- Helper of `def:app-vol-tree`(2), snapshot `cr-2026-10-23`: the quotient multigraph of every pairing
is connected (the source's "and it is connected"). The graph has the classes as vertices and one edge
for each z-edge (latent to output endpoint) and each w-edge (latent to input endpoint). Verbatim:
```latex
\begin{definition}[Tree moment equations]\label{def:app-vol-tree}
Fix $(\ell,J,R)$, diagonal $F,G$, and integers $a,b\ge0$, with $k=2a+2b+2$ and
the factors $X_r$ and labels $l_r$ of \cref{eqn:app-vol-word}.
\begin{enumerate}[label=(\arabic*)]
\item \emph{The polygon.} Take $k$ external vertices $\mathsf e_1,\dots,\mathsf e_k$
and $k$ latent vertices $\mathsf l_1,\dots,\mathsf l_k$, indices modulo $k$. The
vertex $\mathsf e_r$ sits between $X_r$ and $X_{r+1}$; it has the input type
if $X_r$ is untransposed and the output type otherwise. The output vertex
$\mathsf e_k$ carries the mark $F$ and the input vertex $\mathsf e_{2a+1}$ carries
the mark $G$. Each factor $X_r$ contributes a $z$-edge joining $\mathsf l_r$ to
the output vertex among $\mathsf e_{r-1},\mathsf e_r$, and a $w$-edge joining $\mathsf l_r$
to the input vertex among them.
\item \emph{Pairings.} A pairing is a pair $(\pi,\pi')$ of a perfect matching
$\pi$ of the $k$ $z$-edges and a perfect matching $\pi'$ of the $k$ $w$-edges.
For each matched pair of edges, identify their two latent endpoints and their
two external endpoints. The quotient multigraph has one edge for each matched
pair, hence $k$ edges, and it is connected. The pairing is \emph{retained} if
the quotient is a tree, that is, if it has exactly $k+1$ vertices.
\item \emph{Values.} For a retained pairing, every vertex class $V$ of the
quotient contributes a factor. An output class $V$ containing $p_V$ original
external vertices contributes $B^{-1}\sum_i\mu_i^{p_V}F_i^{m_V}$, where $m_V=1$ if
$\mathsf e_k\in V$ and $m_V=0$ otherwise. An input class contributes
$B^{-1}\sum_j\lambda_j^{p_V}G_j^{n_V}$, with $n_V=1$ if $\mathsf e_{2a+1}\in V$ and
$n_V=0$ otherwise. A latent class $V$ with set of factors $S_V\subset\{1,\dots,k\}$
contributes
\[
m_{\abs{S_V}}(R)\sum_{\alpha\in\mathcal A}\prod_{r\in S_V}\varpi_{l_r,\alpha}.
\]
\item \emph{The response.} $\mathfrak R^{J,R}_\ell[F,G](x^{2a+1},x^{2b+1})$ is the sum,
over the retained pairings, of the products of the factors of their classes.
It is extended bilinearly to pairs of odd polynomials.
\end{enumerate}
\end{definition}
```
Sorried. -/
theorem def_app_vol_tree_connected (a b : ℕ) (p : TreeMatch (treeK a b) × TreeMatch (treeK a b)) :
    (SimpleGraph.fromRel fun x y : Quotient (treeSetoid p) =>
      ∃ s : Fin (treeK a b),
        (x = treeMk p (Sum.inr s) ∧ y = treeMk p (Sum.inl (treeOutV s))) ∨
        (x = treeMk p (Sum.inr s) ∧ y = treeMk p (Sum.inl (treeInV s)))).Connected :=
  tree_quot_connected (by unfold treeK; omega) p

/-- Private helper: the parity of an external index (`2` on latent vertices). -/
private def treePar {k : ℕ} : TreeVtx k → ℕ
  | Sum.inl e => e.val % 2
  | Sum.inr _ => 2

private lemma tree_prev_val {k : ℕ} (s : Fin k) :
    (treePrev s).val = if s.val = 0 then k - 1 else s.val - 1 := by
  obtain ⟨v, hv⟩ := s
  unfold treePrev
  dsimp only
  rcases Nat.eq_zero_or_pos v with rfl | hpos
  · simp [Nat.mod_eq_of_lt (show k - 1 < k by omega)]
  · rw [if_neg (show ¬ (v = 0) by omega)]
    have e : v + (k - 1) = (v - 1) + k := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (show v - 1 < k by omega)]

private lemma tree_outV_odd {k : ℕ} (hk : k % 2 = 0) (s : Fin k) :
    (treeOutV s).val % 2 = 1 := by
  have hs := s.isLt
  unfold treeOutV
  split_ifs with h
  · have h' : s.val % 2 = 0 := h
    rw [tree_prev_val]
    split_ifs with h0 <;> omega
  · have h' : ¬ s.val % 2 = 0 := h
    omega

private lemma tree_inV_even {k : ℕ} (s : Fin k) : (treeInV s).val % 2 = 0 := by
  have hs := s.isLt
  unfold treeInV
  split_ifs with h
  · have h' : s.val % 2 = 0 := h
    exact h'
  · have h' : ¬ s.val % 2 = 0 := h
    rw [tree_prev_val]
    split_ifs with h0 <;> omega

/-- Private helper: the identifications preserve the parity of external indices. -/
private lemma tree_setoid_par {k : ℕ} (hk : k % 2 = 0) (p : TreeMatch k × TreeMatch k) {x y : TreeVtx k}
    (h : treeSetoid p x y) : treePar x = treePar y := by
  change Relation.EqvGen (treeRel p) x y at h
  induction h with
  | rel x y hxy =>
    unfold treeRel at hxy
    obtain ⟨s, h1 | h1 | h1 | h1⟩ := hxy
    · obtain ⟨h1a, h1b⟩ := h1
      subst h1a; subst h1b; rfl
    · obtain ⟨h1a, h1b⟩ := h1
      subst h1a; subst h1b; rfl
    · obtain ⟨h1a, h1b⟩ := h1
      subst h1a; subst h1b
      simp only [treePar]
      rw [tree_outV_odd hk s, tree_outV_odd hk (p.1.1 s)]
    · obtain ⟨h1a, h1b⟩ := h1
      subst h1a; subst h1b
      simp only [treePar]
      rw [tree_inV_even s, tree_inV_even (p.2.1 s)]
  | refl => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- Private helper: the class of the `G`-mark contains no odd (output) external vertex. -/
private lemma tree_gmark_pure (a b : ℕ) (p : TreeMatch (treeK a b) × TreeMatch (treeK a b)) :
    ¬ ∃ e : Fin (treeK a b),
      treeMk p (Sum.inl e) = treeMk p (Sum.inl (treeGMark a b)) ∧ e.val % 2 = 1 := by
  rintro ⟨e, heq, hodd⟩
  unfold treeMk at heq
  have h2 := tree_setoid_par (by unfold treeK; omega) p (Quotient.exact heq)
  simp only [treePar, treeGMark, Fin.val_mk] at h2
  omega

/-- Private helper: a bilinear sum identity (the weights `w i` do not depend on the test data). -/
private lemma tree_sum_lin {ι : Type*} [Fintype ι] (B c : ℝ) (w x y : ι → ℝ) :
    B * ∑ i, w i * (c * x i + y i) = c * (B * ∑ i, w i * x i) + B * ∑ i, w i * y i := by
  have h : ∑ i, w i * (c * x i + y i) = c * ∑ i, w i * x i + ∑ i, w i * y i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h]; ring

open Classical in
/-- Private helper: the factor of a class other than the `F`-mark class does not depend on `Fd`. -/
private lemma tree_cf_F_indep {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Gd : Fin n → ℝ) (a b : ℕ) (p : TreeMatch (treeK a b) × TreeMatch (treeK a b))
    (V : Quotient (treeSetoid p)) (hne : V ≠ treeMk p (Sum.inl (treeFMark a b)))
    (Fd Fd' : Fin m → ℝ) :
    treeClassFactor β ℓ J R B μ lam Fd Gd a b p V =
      treeClassFactor β ℓ J R B μ lam Fd' Gd a b p V := by
  unfold treeClassFactor
  simp only [Ne.symm hne, ↓reduceIte, pow_zero, mul_one]

open Classical in
/-- Private helper: the factor of a class other than the `G`-mark class does not depend on `Gd`. -/
private lemma tree_cf_G_indep {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (a b : ℕ) (p : TreeMatch (treeK a b) × TreeMatch (treeK a b))
    (V : Quotient (treeSetoid p)) (hne : V ≠ treeMk p (Sum.inl (treeGMark a b)))
    (Gd Gd' : Fin n → ℝ) :
    treeClassFactor β ℓ J R B μ lam Fd Gd a b p V =
      treeClassFactor β ℓ J R B μ lam Fd Gd' a b p V := by
  unfold treeClassFactor
  simp only [Ne.symm hne, ↓reduceIte, pow_zero, mul_one]

open Classical in
/-- Private helper: the `F`-mark class factor is linear in `Fd`. -/
private lemma tree_cf_F_lin {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Gd : Fin n → ℝ) (a b : ℕ) (p : TreeMatch (treeK a b) × TreeMatch (treeK a b))
    (c : ℝ) (Fd₁ Fd₂ : Fin m → ℝ) :
    treeClassFactor β ℓ J R B μ lam (c • Fd₁ + Fd₂) Gd a b p (treeMk p (Sum.inl (treeFMark a b))) =
      c * treeClassFactor β ℓ J R B μ lam Fd₁ Gd a b p (treeMk p (Sum.inl (treeFMark a b))) +
        treeClassFactor β ℓ J R B μ lam Fd₂ Gd a b p (treeMk p (Sum.inl (treeFMark a b))) := by
  have hex : ∃ e : Fin (treeK a b),
      treeMk p (Sum.inl e) = treeMk p (Sum.inl (treeFMark a b)) := ⟨_, rfl⟩
  have hodd : ∃ e : Fin (treeK a b),
      treeMk p (Sum.inl e) = treeMk p (Sum.inl (treeFMark a b)) ∧ e.val % 2 = 1 :=
    ⟨treeFMark a b, rfl, by unfold treeFMark; dsimp only; omega⟩
  unfold treeClassFactor
  simp only [if_pos hex, if_pos hodd, if_true, pow_one, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  exact tree_sum_lin _ _ _ _ _

open Classical in
/-- Private helper: the `G`-mark class factor is linear in `Gd`. -/
private lemma tree_cf_G_lin {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (a b : ℕ) (p : TreeMatch (treeK a b) × TreeMatch (treeK a b))
    (c : ℝ) (Gd₁ Gd₂ : Fin n → ℝ) :
    treeClassFactor β ℓ J R B μ lam Fd (c • Gd₁ + Gd₂) a b p (treeMk p (Sum.inl (treeGMark a b))) =
      c * treeClassFactor β ℓ J R B μ lam Fd Gd₁ a b p (treeMk p (Sum.inl (treeGMark a b))) +
        treeClassFactor β ℓ J R B μ lam Fd Gd₂ a b p (treeMk p (Sum.inl (treeGMark a b))) := by
  have hex : ∃ e : Fin (treeK a b),
      treeMk p (Sum.inl e) = treeMk p (Sum.inl (treeGMark a b)) := ⟨_, rfl⟩
  have hnot := tree_gmark_pure a b p
  unfold treeClassFactor
  simp only [if_pos hex, if_neg hnot, if_true, pow_one, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  exact tree_sum_lin _ _ _ _ _

open Classical in
/-- Private helper: the product over the classes of a pairing is linear in `Fd` (the `F`-mark class
is the only class that depends on `Fd`, and it does so linearly). -/
private lemma tree_prod_F {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Gd : Fin n → ℝ) (a b : ℕ) (p : TreeMatch (treeK a b) × TreeMatch (treeK a b))
    (c : ℝ) (Fd₁ Fd₂ : Fin m → ℝ) :
    ∏ V : Quotient (treeSetoid p), treeClassFactor β ℓ J R B μ lam (c • Fd₁ + Fd₂) Gd a b p V =
      c * ∏ V : Quotient (treeSetoid p), treeClassFactor β ℓ J R B μ lam Fd₁ Gd a b p V +
        ∏ V : Quotient (treeSetoid p), treeClassFactor β ℓ J R B μ lam Fd₂ Gd a b p V := by
  have hmem := Finset.mem_univ (treeMk p (Sum.inl (treeFMark a b)))
  rw [← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hmem,
    ← Finset.mul_prod_erase _ _ hmem]
  beta_reduce
  have hP1 : ∏ V ∈ Finset.univ.erase (treeMk p (Sum.inl (treeFMark a b))),
      treeClassFactor β ℓ J R B μ lam (c • Fd₁ + Fd₂) Gd a b p V =
      ∏ V ∈ Finset.univ.erase (treeMk p (Sum.inl (treeFMark a b))),
      treeClassFactor β ℓ J R B μ lam Fd₁ Gd a b p V :=
    Finset.prod_congr rfl (fun V hV => tree_cf_F_indep β ℓ J R B μ lam Gd a b p V
      (Finset.ne_of_mem_erase hV) _ _)
  have hP2 : ∏ V ∈ Finset.univ.erase (treeMk p (Sum.inl (treeFMark a b))),
      treeClassFactor β ℓ J R B μ lam Fd₂ Gd a b p V =
      ∏ V ∈ Finset.univ.erase (treeMk p (Sum.inl (treeFMark a b))),
      treeClassFactor β ℓ J R B μ lam Fd₁ Gd a b p V :=
    Finset.prod_congr rfl (fun V hV => tree_cf_F_indep β ℓ J R B μ lam Gd a b p V
      (Finset.ne_of_mem_erase hV) _ _)
  rw [hP1, hP2, tree_cf_F_lin β ℓ J R B μ lam Gd a b p c Fd₁ Fd₂]
  ring

open Classical in
/-- Private helper: the product over the classes of a pairing is linear in `Gd`. -/
private lemma tree_prod_G {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (a b : ℕ) (p : TreeMatch (treeK a b) × TreeMatch (treeK a b))
    (c : ℝ) (Gd₁ Gd₂ : Fin n → ℝ) :
    ∏ V : Quotient (treeSetoid p), treeClassFactor β ℓ J R B μ lam Fd (c • Gd₁ + Gd₂) a b p V =
      c * ∏ V : Quotient (treeSetoid p), treeClassFactor β ℓ J R B μ lam Fd Gd₁ a b p V +
        ∏ V : Quotient (treeSetoid p), treeClassFactor β ℓ J R B μ lam Fd Gd₂ a b p V := by
  have hmem := Finset.mem_univ (treeMk p (Sum.inl (treeGMark a b)))
  rw [← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hmem,
    ← Finset.mul_prod_erase _ _ hmem]
  beta_reduce
  have hP1 : ∏ V ∈ Finset.univ.erase (treeMk p (Sum.inl (treeGMark a b))),
      treeClassFactor β ℓ J R B μ lam Fd (c • Gd₁ + Gd₂) a b p V =
      ∏ V ∈ Finset.univ.erase (treeMk p (Sum.inl (treeGMark a b))),
      treeClassFactor β ℓ J R B μ lam Fd Gd₁ a b p V :=
    Finset.prod_congr rfl (fun V hV => tree_cf_G_indep β ℓ J R B μ lam Fd a b p V
      (Finset.ne_of_mem_erase hV) _ _)
  have hP2 : ∏ V ∈ Finset.univ.erase (treeMk p (Sum.inl (treeGMark a b))),
      treeClassFactor β ℓ J R B μ lam Fd Gd₂ a b p V =
      ∏ V ∈ Finset.univ.erase (treeMk p (Sum.inl (treeGMark a b))),
      treeClassFactor β ℓ J R B μ lam Fd Gd₁ a b p V :=
    Finset.prod_congr rfl (fun V hV => tree_cf_G_indep β ℓ J R B μ lam Fd a b p V
      (Finset.ne_of_mem_erase hV) _ _)
  rw [hP1, hP2, tree_cf_G_lin β ℓ J R B μ lam Fd a b p c Gd₁ Gd₂]
  ring

open Classical in
/-- Private helper: the monomial response is linear in `Fd`. -/
private lemma tree_mono_F_lin {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Gd : Fin n → ℝ) (a b : ℕ) (c : ℝ) (Fd₁ Fd₂ : Fin m → ℝ) :
    treeMono β ℓ J R B μ lam (c • Fd₁ + Fd₂) Gd a b =
      c * treeMono β ℓ J R B μ lam Fd₁ Gd a b + treeMono β ℓ J R B μ lam Fd₂ Gd a b := by
  unfold treeMono
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases hr : treeRetained p
  · simp only [if_pos hr]
    exact tree_prod_F β ℓ J R B μ lam Gd a b p c Fd₁ Fd₂
  · simp only [if_neg hr, mul_zero, add_zero]

open Classical in
/-- Private helper: the monomial response is linear in `Gd`. -/
private lemma tree_mono_G_lin {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (a b : ℕ) (c : ℝ) (Gd₁ Gd₂ : Fin n → ℝ) :
    treeMono β ℓ J R B μ lam Fd (c • Gd₁ + Gd₂) a b =
      c * treeMono β ℓ J R B μ lam Fd Gd₁ a b + treeMono β ℓ J R B μ lam Fd Gd₂ a b := by
  unfold treeMono
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases hr : treeRetained p
  · simp only [if_pos hr]
    exact tree_prod_G β ℓ J R B μ lam Fd a b p c Gd₁ Gd₂
  · simp only [if_neg hr, mul_zero, add_zero]

/-- Helper of `def:app-vol-tree`(3), snapshot `cr-2026-10-23`: the response is linear in `F` and in
`G` (l.1066–1067: "each mark lies in exactly one class"). Verbatim:
```latex
covariance square root each. The response is linear in $F$ and in $G$, since
each mark lies in exactly one class. For the shortest word, $a=b=0$, there is
```
Sorried. -/
theorem def_app_vol_tree_linear_F (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd₁ Fd₂ : Fin m → ℝ) (Gd : Fin n → ℝ) (c : ℝ) (f₁ f₂ : Polynomial ℝ) :
    def_app_vol_tree β ℓ J R B μ lam (c • Fd₁ + Fd₂) Gd f₁ f₂ =
      c * def_app_vol_tree β ℓ J R B μ lam Fd₁ Gd f₁ f₂ +
        def_app_vol_tree β ℓ J R B μ lam Fd₂ Gd f₁ f₂ := by
  unfold def_app_vol_tree
  simp only [tree_mono_F_lin]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- Helper of `def:app-vol-tree`(3), snapshot `cr-2026-10-23`: linearity in `G` (l.1066–1067). Sorried. -/
theorem def_app_vol_tree_linear_G (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd₁ Gd₂ : Fin n → ℝ) (c : ℝ) (f₁ f₂ : Polynomial ℝ) :
    def_app_vol_tree β ℓ J R B μ lam Fd (c • Gd₁ + Gd₂) f₁ f₂ =
      c * def_app_vol_tree β ℓ J R B μ lam Fd Gd₁ f₁ f₂ +
        def_app_vol_tree β ℓ J R B μ lam Fd Gd₂ f₁ f₂ := by
  unfold def_app_vol_tree
  simp only [tree_mono_G_lin]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-! ### The shortest word `a = b = 0` (`k = 2`): private helpers -/

private lemma tree00_outV_val (s : Fin (treeK 0 0)) : (treeOutV s).val = 1 := by
  obtain ⟨v, hv⟩ := s
  have hv' : v < 2 := by simpa [treeK] using hv
  interval_cases v <;> simp [treeOutV, treeUntransposed, treePrev, treeK]

private lemma tree00_inV_val (s : Fin (treeK 0 0)) : (treeInV s).val = 0 := by
  obtain ⟨v, hv⟩ := s
  have hv' : v < 2 := by simpa [treeK] using hv
  interval_cases v <;> simp [treeInV, treeUntransposed, treePrev, treeK]

/-- Class label of a vertex of the shortest word: `0` for `e_1`, `1` for `e_2`, `2` for latent vertices. -/
private def tree00Tri (x : TreeVtx (treeK 0 0)) : Fin 3 :=
  Sum.elim (fun e => if e.val = 0 then 0 else 1) (fun _ => 2) x

private lemma tree00_tri_respect (p : TreeMatch (treeK 0 0) × TreeMatch (treeK 0 0))
    (x y : TreeVtx (treeK 0 0)) (h : treeSetoid p x y) : tree00Tri x = tree00Tri y := by
  change Relation.EqvGen (treeRel p) x y at h
  induction h with
  | rel x y hxy =>
    obtain ⟨s, h1 | h1 | h1 | h1⟩ := hxy <;> obtain ⟨h1a, h1b⟩ := h1 <;> subst h1a <;> subst h1b <;>
      first
        | rfl
        | exact congrArg (fun e => tree00Tri (Sum.inl e)) (Fin.ext (by rw [tree00_outV_val, tree00_outV_val]))
        | exact congrArg (fun e => tree00Tri (Sum.inl e)) (Fin.ext (by rw [tree00_inV_val, tree00_inV_val]))
  | refl => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

private def tree00Map (p : TreeMatch (treeK 0 0) × TreeMatch (treeK 0 0)) :
    Quotient (treeSetoid p) → Fin 3 :=
  Quotient.lift tree00Tri (fun x y h => tree00_tri_respect p x y h)

private def tree00Pt : TreeMatch (treeK 0 0) :=
  ⟨Equiv.swap ⟨0, by unfold treeK; omega⟩ ⟨1, by unfold treeK; omega⟩, by decide, by decide⟩

private lemma tree00_perm_eq (σ : TreeMatch (treeK 0 0)) (s t : Fin (treeK 0 0)) (h : s ≠ t) :
    σ.1 s = t := by
  have h1 : σ.1 s ≠ s := σ.2.2 s
  have hs := s.isLt
  have ht := t.isLt
  have hσ := (σ.1 s).isLt
  have h3 : s.val ≠ t.val := fun e => h (Fin.ext e)
  by_contra hc
  have h2 : (σ.1 s).val ≠ t.val := fun e => hc (Fin.ext e)
  have h1' : (σ.1 s).val ≠ s.val := fun e => h1 (Fin.ext e)
  unfold treeK at hs ht hσ
  omega

private instance tree00_match_subsingleton : Subsingleton (TreeMatch (treeK 0 0)) :=
  ⟨fun σ τ => by
    apply Subtype.ext
    apply Equiv.ext
    intro s
    exact tree00_perm_eq σ s (τ.1 s) (fun h => τ.2.2 s h.symm)⟩

private lemma tree00_quot_bij (p : TreeMatch (treeK 0 0) × TreeMatch (treeK 0 0)) :
    Function.Bijective (tree00Map p) := by
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := Quotient.exists_rep a
    obtain ⟨y, rfl⟩ := Quotient.exists_rep b
    change tree00Tri x = tree00Tri y at hab
    apply Quotient.sound
    rcases x with e | s <;> rcases y with f | t
    · have he := e.isLt
      have hf := f.isLt
      unfold treeK at he hf
      have hef : e = f := by
        apply Fin.ext
        simp only [tree00Tri, Sum.elim_inl] at hab
        split_ifs at hab <;> first | omega | exact absurd hab (by decide)
      rw [hef]
    · simp only [tree00Tri, Sum.elim_inl, Sum.elim_inr] at hab
      split_ifs at hab <;> exact absurd hab (by decide)
    · simp only [tree00Tri, Sum.elim_inl, Sum.elim_inr] at hab
      split_ifs at hab <;> exact absurd hab (by decide)
    · by_cases hst : s = t
      · rw [hst]
      · exact Relation.EqvGen.rel _ _
          ⟨s, Or.inl ⟨rfl, congrArg Sum.inr (tree00_perm_eq p.1 s t hst).symm⟩⟩
  · intro i
    fin_cases i
    · exact ⟨Quotient.mk _ (Sum.inl ⟨0, by unfold treeK; omega⟩), rfl⟩
    · exact ⟨Quotient.mk _ (Sum.inl ⟨1, by unfold treeK; omega⟩), rfl⟩
    · exact ⟨Quotient.mk _ (Sum.inr ⟨0, by unfold treeK; omega⟩), rfl⟩

private lemma tree00_quot_card (p : TreeMatch (treeK 0 0) × TreeMatch (treeK 0 0)) :
    Nat.card (Quotient (treeSetoid p)) = 3 := by
  rw [Nat.card_eq_of_bijective _ (tree00_quot_bij p)]
  simp

private lemma tree00_mk_iff (p : TreeMatch (treeK 0 0) × TreeMatch (treeK 0 0))
    (x y : TreeVtx (treeK 0 0)) :
    treeMk p x = treeMk p y ↔ tree00Tri x = tree00Tri y := by
  constructor
  · intro h
    exact congrArg (tree00Map p) h
  · intro h
    exact (tree00_quot_bij p).1 h

private lemma tree00_inl_eq (p : TreeMatch (treeK 0 0) × TreeMatch (treeK 0 0))
    (e f : Fin (treeK 0 0)) : treeMk p (Sum.inl e) = treeMk p (Sum.inl f) ↔ e = f := by
  rw [tree00_mk_iff]
  constructor
  · intro h
    simp only [tree00Tri, Sum.elim_inl] at h
    have he := e.isLt
    have hf := f.isLt
    unfold treeK at he hf
    apply Fin.ext
    split_ifs at h <;> first | omega | exact absurd h (by decide)
  · rintro rfl
    rfl

private lemma tree00_inr_ne_inl (p : TreeMatch (treeK 0 0) × TreeMatch (treeK 0 0))
    (s e : Fin (treeK 0 0)) : treeMk p (Sum.inr s) ≠ treeMk p (Sum.inl e) := by
  intro h
  rw [tree00_mk_iff] at h
  simp only [tree00Tri, Sum.elim_inl, Sum.elim_inr] at h
  split_ifs at h <;> exact absurd h (by decide)

private lemma tree00_sum_icc (β : ℝ) (ℓ J : ℕ) :
    ∑ α ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ), ∏ r : Fin (treeK 0 0), treeVarpi β ℓ (treeLabel 0 r) α =
      β ^ ℓ * ∑ j ∈ Finset.range (J + 1), Muon.emaW β j ^ 2 := by
  have hprod : ∀ α : ℤ, ∏ r : Fin (treeK 0 0), treeVarpi β ℓ (treeLabel 0 r) α =
      treeVarpi β ℓ 1 α * treeVarpi β ℓ 2 α := by
    intro α
    rw [Fin.prod_univ_two]
    rfl
  simp only [hprod]
  have hsub : Finset.Icc (-(J : ℤ)) 0 ⊆ Finset.Icc (-(J : ℤ)) (ℓ : ℤ) :=
    Finset.Icc_subset_Icc (le_refl _) (by omega)
  have hzero : ∀ x ∈ Finset.Icc (-(J : ℤ)) (ℓ : ℤ), x ∉ Finset.Icc (-(J : ℤ)) 0 →
      treeVarpi β ℓ 1 x * treeVarpi β ℓ 2 x = 0 := by
    intro x hx hx'
    simp only [Finset.mem_Icc] at hx hx'
    have hpos : 0 < x := by
      by_contra hc
      exact hx' ⟨hx.1, by omega⟩
    have h1 : treeVarpi β ℓ 1 x = 0 := by
      unfold treeVarpi
      rw [if_neg (show ¬ x ≤ 0 by omega)]
      simp
    rw [h1, zero_mul]
  rw [← Finset.sum_subset hsub hzero, Finset.mul_sum]
  apply Finset.sum_nbij' (fun α : ℤ => α.natAbs) (fun n : ℕ => -(n : ℤ))
  · intro α hα
    simp only [Finset.mem_Icc, Finset.mem_range] at hα ⊢
    have := Int.ofNat_natAbs_of_nonpos hα.2
    omega
  · intro n hn
    simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢
    omega
  · intro α hα
    simp only [Finset.mem_Icc] at hα
    have := Int.ofNat_natAbs_of_nonpos hα.2
    omega
  · intro n _
    simp
  · intro α hα
    simp only [Finset.mem_Icc] at hα
    unfold treeVarpi
    simp [hα.2] <;> ring

open Classical in
private lemma tree00_cls_A (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (p : TreeMatch (treeK 0 0) × TreeMatch (treeK 0 0)) :
    treeClassFactor β ℓ J R B μ lam Fd Gd 0 0 p
        (treeMk p (Sum.inl ⟨0, by unfold treeK; omega⟩)) =
      (B : ℝ)⁻¹ * ∑ j, lam j * Gd j := by
  unfold treeClassFactor
  dsimp only
  have hex : ∃ e : Fin (treeK 0 0), treeMk p (Sum.inl e) =
      treeMk p (Sum.inl ⟨0, by unfold treeK; omega⟩) := ⟨_, rfl⟩
  have hno : ¬ ∃ e : Fin (treeK 0 0), treeMk p (Sum.inl e) =
      treeMk p (Sum.inl ⟨0, by unfold treeK; omega⟩) ∧ e.val % 2 = 1 := by
    rintro ⟨e, he, ho⟩
    rw [tree00_inl_eq] at he
    subst he
    simp at ho
  rw [if_pos hex, if_neg hno]
  have hG : treeMk p (Sum.inl (treeGMark 0 0)) =
      treeMk p (Sum.inl ⟨0, by unfold treeK; omega⟩) := by
    rw [tree00_inl_eq]
    rfl
  have hp : (Finset.univ.filter fun e : Fin (treeK 0 0) =>
      treeMk p (Sum.inl e) = treeMk p (Sum.inl ⟨0, by unfold treeK; omega⟩)).card = 1 := by
    simp only [tree00_inl_eq]
    rw [Finset.filter_eq']
    simp
  rw [if_pos hG, hp]
  simp

open Classical in
private lemma tree00_cls_B (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (p : TreeMatch (treeK 0 0) × TreeMatch (treeK 0 0)) :
    treeClassFactor β ℓ J R B μ lam Fd Gd 0 0 p
        (treeMk p (Sum.inl ⟨1, by unfold treeK; omega⟩)) =
      (B : ℝ)⁻¹ * ∑ i, μ i * Fd i := by
  unfold treeClassFactor
  dsimp only
  have hex : ∃ e : Fin (treeK 0 0), treeMk p (Sum.inl e) =
      treeMk p (Sum.inl ⟨1, by unfold treeK; omega⟩) := ⟨_, rfl⟩
  have hodd : ∃ e : Fin (treeK 0 0), treeMk p (Sum.inl e) =
      treeMk p (Sum.inl ⟨1, by unfold treeK; omega⟩) ∧ e.val % 2 = 1 :=
    ⟨⟨1, by unfold treeK; omega⟩, rfl, rfl⟩
  rw [if_pos hex, if_pos hodd]
  have hF : treeMk p (Sum.inl (treeFMark 0 0)) =
      treeMk p (Sum.inl ⟨1, by unfold treeK; omega⟩) := by
    rw [tree00_inl_eq]
    rfl
  have hp : (Finset.univ.filter fun e : Fin (treeK 0 0) =>
      treeMk p (Sum.inl e) = treeMk p (Sum.inl ⟨1, by unfold treeK; omega⟩)).card = 1 := by
    simp only [tree00_inl_eq]
    rw [Finset.filter_eq']
    simp
  rw [if_pos hF, hp]
  simp

open Classical in
private lemma tree00_cls_C (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (p : TreeMatch (treeK 0 0) × TreeMatch (treeK 0 0)) :
    treeClassFactor β ℓ J R B μ lam Fd Gd 0 0 p
        (treeMk p (Sum.inr ⟨0, by unfold treeK; omega⟩)) =
      treeTruncMoment 2 R * (β ^ ℓ * ∑ j ∈ Finset.range (J + 1), Muon.emaW β j ^ 2) := by
  unfold treeClassFactor
  dsimp only
  have hno : ¬ ∃ e : Fin (treeK 0 0), treeMk p (Sum.inl e) =
      treeMk p (Sum.inr ⟨0, by unfold treeK; omega⟩) := by
    rintro ⟨e, he⟩
    exact tree00_inr_ne_inl p _ e he.symm
  rw [if_neg hno]
  have hS : (Finset.univ.filter fun r : Fin (treeK 0 0) =>
      treeMk p (Sum.inr r) = treeMk p (Sum.inr ⟨0, by unfold treeK; omega⟩)) = Finset.univ :=
    Finset.filter_true_of_mem fun r _ => (tree00_mk_iff p _ _).2 rfl
  have hc : (Finset.univ : Finset (Fin (treeK 0 0))).card = 2 := by simp [treeK]
  rw [hS, hc, tree00_sum_icc]

open Classical in
private lemma tree00_mono_eq (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ)
    (p : TreeMatch (treeK 0 0) × TreeMatch (treeK 0 0)) :
    (if treeRetained p then
      ∏ V : Quotient (treeSetoid p), treeClassFactor β ℓ J R B μ lam Fd Gd 0 0 p V else 0) =
      ((B : ℝ)⁻¹ * ∑ j, lam j * Gd j) * ((B : ℝ)⁻¹ * ∑ i, μ i * Fd i) *
        (treeTruncMoment 2 R * (β ^ ℓ * ∑ j ∈ Finset.range (J + 1), Muon.emaW β j ^ 2)) := by
  have hret : treeRetained p := by
    unfold treeRetained
    rw [tree00_quot_card]
  rw [if_pos hret]
  obtain ⟨E, hE⟩ : ∃ E : Quotient (treeSetoid p) ≃ Fin 3, ∀ V, E V = tree00Map p V :=
    ⟨Equiv.ofBijective _ (tree00_quot_bij p), fun V => rfl⟩
  rw [← Equiv.prod_comp E.symm, Fin.prod_univ_three]
  have h0 : E.symm 0 = treeMk p (Sum.inl ⟨0, by unfold treeK; omega⟩) := by
    rw [Equiv.symm_apply_eq, hE]
    rfl
  have h1 : E.symm 1 = treeMk p (Sum.inl ⟨1, by unfold treeK; omega⟩) := by
    rw [Equiv.symm_apply_eq, hE]
    rfl
  have h2 : E.symm 2 = treeMk p (Sum.inr ⟨0, by unfold treeK; omega⟩) := by
    rw [Equiv.symm_apply_eq, hE]
    rfl
  rw [h0, h1, h2]
  rw [tree00_cls_A, tree00_cls_B, tree00_cls_C]

private lemma tree00_outer_sum (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) :
    ∑ a ∈ Finset.range ((Polynomial.X : Polynomial ℝ).natDegree + 1),
      ∑ b ∈ Finset.range ((Polynomial.X : Polynomial ℝ).natDegree + 1),
        (Polynomial.X : Polynomial ℝ).coeff (2 * a + 1) * (Polynomial.X : Polynomial ℝ).coeff (2 * b + 1) *
          treeMono β ℓ J R B μ lam Fd Gd a b =
      treeMono β ℓ J R B μ lam Fd Gd 0 0 := by
  simp [Polynomial.natDegree_X, Polynomial.coeff_X]

private lemma tree00_mono_full (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) :
    treeMono β ℓ J R B μ lam Fd Gd 0 0 =
      ((B : ℝ)⁻¹ * ∑ j, lam j * Gd j) * ((B : ℝ)⁻¹ * ∑ i, μ i * Fd i) *
        (treeTruncMoment 2 R * (β ^ ℓ * ∑ j ∈ Finset.range (J + 1), Muon.emaW β j ^ 2)) := by
  unfold treeMono
  have pt : TreeMatch (treeK 0 0) × TreeMatch (treeK 0 0) := (tree00Pt, tree00Pt)
  rw [Fintype.sum_subsingleton _ pt]
  exact tree00_mono_eq β ℓ J R B μ lam Fd Gd pt

/-- Helper of `def:app-vol-tree`, snapshot `cr-2026-10-23`, the shortest word `a = b = 0` (l.1067–1071): exactly one pairing,
which identifies `l₁` with `l₂`, and the quotient has three vertices. Verbatim:
```latex
each mark lies in exactly one class. For the shortest word, $a=b=0$, there is
one pairing; it identifies $\mathsf l_1$ with $\mathsf l_2$, the quotient has the three
vertices $\{\mathsf e_1\},\{\mathsf e_2\},\{\mathsf l_1,\mathsf l_2\}$, and
\[
\mathfrak R^{J,R}_\ell[F,G](x,x)=\frac{\Tr(\Sigmaout F)}{B}\,\frac{\Tr(\Sigmain G)}{B}\,m_2(R)\,\bmom^\ell\sum_{j\le J}\emaw j^2,
```
Sorried. -/
theorem def_app_vol_tree_shortest_pairing :
    Nat.card (TreeMatch (treeK 0 0)) = 1 := by
  exact Nat.card_eq_one_iff_exists.2 ⟨tree00Pt, fun σ => Subsingleton.elim σ tree00Pt⟩

/-- Helper of `def:app-vol-tree`, snapshot `cr-2026-10-23`, the shortest word (l.1067–1071): every pairing of the shortest word
identifies the two latent vertices and has exactly three vertex classes, so it is retained. Sorried. -/
theorem def_app_vol_tree_shortest_quotient
    (p : TreeMatch (treeK 0 0) × TreeMatch (treeK 0 0)) :
    treeMk p (Sum.inr ⟨0, by simp [treeK]⟩) = treeMk p (Sum.inr ⟨1, by simp [treeK]⟩) ∧
      Nat.card (Quotient (treeSetoid p)) = 3 := by
  exact ⟨by rw [tree00_mk_iff]; rfl, tree00_quot_card p⟩

/-- Helper of `def:app-vol-tree`, snapshot `cr-2026-10-23`, the shortest word (l.1067–1074), closed form: the monomial response at
`a = b = 0` equals `Tr(Σ_out F)/B · Tr(Σ_in G)/B · m_2(R) β^ℓ ∑_{j≤J} w_j^2`, written in eigenvalue data.
Verbatim:
```latex
each mark lies in exactly one class. For the shortest word, $a=b=0$, there is
one pairing; it identifies $\mathsf l_1$ with $\mathsf l_2$, the quotient has the three
vertices $\{\mathsf e_1\},\{\mathsf e_2\},\{\mathsf l_1,\mathsf l_2\}$, and
\[
\mathfrak R^{J,R}_\ell[F,G](x,x)=\frac{\Tr(\Sigmaout F)}{B}\,\frac{\Tr(\Sigmain G)}{B}\,m_2(R)\,\bmom^\ell\sum_{j\le J}\emaw j^2,
\]
which tends, as $J,R\to\infty$, to $\bmom^\ell\sw2B^{-2}\Tr(\Sigmaout F)\Tr(\Sigmain G)$,
the exact value of $B^{-1}\EE\Tr[F\,M^{\mathrm g}_tG\,M^{\mathrm g\,\T}_{t+\ell}]$.
```
Sorried. -/
theorem def_app_vol_tree_shortest (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) :
    def_app_vol_tree β ℓ J R B μ lam Fd Gd Polynomial.X Polynomial.X =
      ((B : ℝ)⁻¹ * ∑ i, μ i * Fd i) * ((B : ℝ)⁻¹ * ∑ j, lam j * Gd j) *
        treeTruncMoment 2 R * (β ^ ℓ * ∑ j ∈ Finset.range (J + 1), Muon.emaW β j ^ 2) := by
  unfold def_app_vol_tree
  rw [tree00_outer_sum, tree00_mono_full]
  ring

/-- Private helper: the truncated Gaussian second moment `m_2(R)` tends to `1` as `R → ∞`
(dominated convergence against `x^2`, `Muon.Foundations.gaussian_moment_two`). -/
private lemma tree_lim_trunc_two :
    Tendsto (fun R : ℝ => treeTruncMoment 2 R) atTop (𝓝 1) := by
  have hfun : (fun R : ℝ => treeTruncMoment 2 R) =
      fun R => ∫ x, (if |x| ≤ R then x ^ 2 else 0) ∂(gaussianReal 0 1) := by
    funext R
    rw [treeTruncMoment, if_neg two_ne_zero]
  have hmeas : ∀ R : ℝ, AEStronglyMeasurable (fun x : ℝ => if |x| ≤ R then x ^ 2 else 0)
      (gaussianReal 0 1) := by
    intro R
    refine Measurable.aestronglyMeasurable ?_
    exact Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
      (measurable_id.pow_const 2) measurable_const
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := gaussianReal 0 1)
    (l := atTop) (F := fun (R : ℝ) (x : ℝ) => if |x| ≤ R then x ^ 2 else 0)
    (f := fun x : ℝ => x ^ 2) (fun x : ℝ => x ^ 2)
    (Eventually.of_forall hmeas)
    (Eventually.of_forall fun R => ae_of_all _ fun x => by
      split_ifs with h
      · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      · rw [norm_zero]; positivity)
    (Muon.Foundations.gaussian_integrable_pow 2)
    (ae_of_all _ fun x => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop |x|] with R hR
      rw [if_pos hR])
  rw [hfun]
  convert hlim using 2
  exact Muon.Foundations.gaussian_moment_two.symm

/-- Private helper: `∑_j w_j^2` is summable for `0 ≤ β < 1`. -/
private lemma tree_lim_emaW_sq_summable {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Summable (fun j : ℕ => Muon.emaW β j ^ 2) := by
  have h : (fun j : ℕ => Muon.emaW β j ^ 2) = fun j => (1 - β) ^ 2 * (β ^ 2) ^ j := by
    funext j
    unfold Muon.emaW
    ring
  rw [h]
  exact (summable_geometric_of_lt_one (sq_nonneg β) (by nlinarith)).mul_left _

/-- Private helper: the partial sums `∑_{j ≤ J} w_j^2` tend to `sPow β 2`. -/
private lemma tree_lim_sum_emaW {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Tendsto (fun J : ℕ => ∑ j ∈ Finset.range (J + 1), Muon.emaW β j ^ 2) atTop
      (𝓝 (Muon.sPow β 2)) := by
  have h := (tree_lim_emaW_sq_summable hβ0 hβ1).hasSum.tendsto_sum_nat
  unfold Muon.sPow
  exact h.comp (tendsto_add_atTop_nat 1)

/-- Helper of `def:app-vol-tree`, snapshot `cr-2026-10-23`, the limit (l.1072–1074): as `J, R → ∞` the response tends to
`β^ℓ s_2 B^{-2} Tr(Σ_out F) Tr(Σ_in G)` (eigenvalue data), for `0 ≤ β < 1` (the frozen-model
standing assumption, `FrozenParams.hβ`, under which `s_2 = ∑_j w_j^2` converges). Verbatim:
```latex
\]
which tends, as $J,R\to\infty$, to $\bmom^\ell\sw2B^{-2}\Tr(\Sigmaout F)\Tr(\Sigmain G)$,
the exact value of $B^{-1}\EE\Tr[F\,M^{\mathrm g}_tG\,M^{\mathrm g\,\T}_{t+\ell}]$.
```
Sorried. -/
theorem def_app_vol_tree_limit (β : ℝ) (hβ : 0 ≤ β ∧ β < 1) (ℓ : ℕ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) :
    Tendsto (fun p : ℕ × ℝ => def_app_vol_tree β ℓ p.1 p.2 B μ lam Fd Gd Polynomial.X Polynomial.X)
      (Filter.atTop ×ˢ Filter.atTop)
      (𝓝 (β ^ ℓ * sPow β 2 * ((B : ℝ)⁻¹) ^ 2 * (∑ i, μ i * Fd i) * (∑ j, lam j * Gd j))) := by
  have hfun : (fun p : ℕ × ℝ => def_app_vol_tree β ℓ p.1 p.2 B μ lam Fd Gd Polynomial.X Polynomial.X) =
      fun p : ℕ × ℝ => ((B : ℝ)⁻¹ * ∑ i, μ i * Fd i) * ((B : ℝ)⁻¹ * ∑ j, lam j * Gd j) *
        treeTruncMoment 2 p.2 * (β ^ ℓ * ∑ j ∈ Finset.range (p.1 + 1), Muon.emaW β j ^ 2) := by
    funext p
    exact def_app_vol_tree_shortest β ℓ p.1 p.2 B μ lam Fd Gd
  rw [hfun]
  have hT : Tendsto (fun p : ℕ × ℝ => treeTruncMoment 2 p.2) (Filter.atTop ×ˢ Filter.atTop) (𝓝 1) :=
    tree_lim_trunc_two.comp Filter.tendsto_snd
  have hS : Tendsto (fun p : ℕ × ℝ => β ^ ℓ * ∑ j ∈ Finset.range (p.1 + 1), Muon.emaW β j ^ 2)
      (Filter.atTop ×ˢ Filter.atTop) (𝓝 (β ^ ℓ * Muon.sPow β 2)) :=
    ((tree_lim_sum_emaW hβ.1 hβ.2).comp Filter.tendsto_fst).const_mul _
  have key := (hT.const_mul (((B : ℝ)⁻¹ * ∑ i, μ i * Fd i) * ((B : ℝ)⁻¹ * ∑ j, lam j * Gd j))).mul hS
  convert key using 2
  ring

/-! ### Helpers for `def_app_vol_tree_exact` (private copies of Defs-private lemmas and new entry-level moments) -/

private lemma tdx_rOut_symm (C : Covariances m n) : (rOut C)ᵀ = rOut C := by
  have h : (CFC.sqrt C.Sout)ᴴ = CFC.sqrt C.Sout :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sout)).isHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

private lemma tdx_rIn_symm (C : Covariances m n) : (rIn C)ᵀ = rIn C := by
  have h : (CFC.sqrt C.Sin)ᴴ = CFC.sqrt C.Sin :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sin)).isHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

private lemma tdx_rOut_mul (C : Covariances m n) : rOut C * rOut C = C.Sout :=
  CFC.sqrt_mul_sqrt_self C.Sout (Matrix.nonneg_iff_posSemidef.mpr C.psdOut)

private lemma tdx_rIn_mul (C : Covariances m n) : rIn C * rIn C = C.Sin :=
  CFC.sqrt_mul_sqrt_self C.Sin (Matrix.nonneg_iff_posSemidef.mpr C.psdIn)

private lemma tdx_sq_coord_integrable (k : ℕ) (i : Fin k) :
    Integrable (fun z : Vec k => z i ^ 2) (Muon.Foundations.stdGaussianPi k) := by
  have hm : MeasurePreserving (fun z : Vec k => z i) (Muon.Foundations.stdGaussianPi k)
      (gaussianReal 0 1) := measurePreserving_eval _ i
  exact (hm.integrable_comp (g := fun x : ℝ => x ^ 2) (by fun_prop)).2
    (Muon.Foundations.gaussian_integrable_pow 2)

private lemma tdx_coord_mul_integrable (k : ℕ) (i j : Fin k) :
    Integrable (fun z : Vec k => z i * z j) (Muon.Foundations.stdGaussianPi k) := by
  refine ((((tdx_sq_coord_integrable k i).add (tdx_sq_coord_integrable k j)).div_const 2)).mono'
    (Continuous.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall fun z => ?_)
  show ‖z i * z j‖ ≤ (z i ^ 2 + z j ^ 2) / 2
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|z i| - |z j|), sq_abs (z i), sq_abs (z j)]

private lemma tdx_zz (k : ℕ) (L : Matrix (Fin k) (Fin k) ℝ) (b a : Fin k) :
    Integrable (fun z : Vec k => L.mulVec z b * L.mulVec z a) (Muon.Foundations.stdGaussianPi k) ∧
    ∫ z : Vec k, L.mulVec z b * L.mulVec z a ∂(Muon.Foundations.stdGaussianPi k)
      = (L * Lᵀ) b a := by
  have e : ∀ z : Vec k, L.mulVec z b * L.mulVec z a =
      ∑ i, ∑ j, (L b i * L a j) * (z i * z j) := by
    intro z
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∀ z : Vec k, L.mulVec z b * L.mulVec z a =
      ∑ i, ∑ j, z i * (Matrix.of fun i j => L b i * L a j) i j * z j := by
    intro z
    rw [e z]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      simp only [Matrix.of_apply]; ring
  refine ⟨?_, ?_⟩
  · simp_rw [e]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (tdx_coord_mul_integrable k i j).const_mul _
  · simp_rw [e2]
    rw [Muon.Foundations.stdGaussianPi_quadratic_mean k]
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]

private lemma tdx_slot (F : FrozenParams m n B) (b a : Fin m) (c d : Fin n) :
    Integrable (fun x : ℝ × (Vec m × Vec n) =>
      (x.1 * ((rOut F.C).mulVec x.2.1 b * (rIn F.C).mulVec x.2.2 c)) *
        (x.1 * ((rOut F.C).mulVec x.2.1 a * (rIn F.C).mulVec x.2.2 d))) (indepSlotLaw m n) ∧
    ∫ x : ℝ × (Vec m × Vec n),
      (x.1 * ((rOut F.C).mulVec x.2.1 b * (rIn F.C).mulVec x.2.2 c)) *
        (x.1 * ((rOut F.C).mulVec x.2.1 a * (rIn F.C).mulVec x.2.2 d)) ∂(indepSlotLaw m n)
      = F.C.Sout b a * F.C.Sin c d := by
  have hfun : (fun x : ℝ × (Vec m × Vec n) =>
      (x.1 * ((rOut F.C).mulVec x.2.1 b * (rIn F.C).mulVec x.2.2 c)) *
        (x.1 * ((rOut F.C).mulVec x.2.1 a * (rIn F.C).mulVec x.2.2 d))) =
      fun x => x.1 ^ 2 * (((rOut F.C).mulVec x.2.1 b * (rOut F.C).mulVec x.2.1 a) *
        ((rIn F.C).mulVec x.2.2 c * (rIn F.C).mulVec x.2.2 d)) := by
    funext x; ring
  rw [hfun]
  have h1 := tdx_zz m (rOut F.C) b a
  have h2 := tdx_zz n (rIn F.C) c d
  have hg2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
    Muon.Foundations.gaussian_integrable_pow 2
  refine ⟨hg2.mul_prod (h1.1.mul_prod h2.1), ?_⟩
  rw [integral_prod_mul (f := fun x : ℝ => x ^ 2)
    (g := fun q : Vec m × Vec n =>
      ((rOut F.C).mulVec q.1 b * (rOut F.C).mulVec q.1 a) *
        ((rIn F.C).mulVec q.2 c * (rIn F.C).mulVec q.2 d)),
    Muon.Foundations.gaussian_moment_two,
    integral_prod_mul (f := fun z : Vec m => (rOut F.C).mulVec z b * (rOut F.C).mulVec z a)
      (g := fun w : Vec n => (rIn F.C).mulVec w c * (rIn F.C).mulVec w d), h1.2, h2.2]
  have e1 : (rOut F.C * (rOut F.C)ᵀ) b a = F.C.Sout b a := by
    rw [tdx_rOut_symm, tdx_rOut_mul]
  have e2 : (rIn F.C * (rIn F.C)ᵀ) c d = F.C.Sin c d := by
    rw [tdx_rIn_symm, tdx_rIn_mul]
  rw [e1, e2]; ring

private lemma tdx_diag (F : FrozenParams m n B) (p : ℤ × Fin B) (b a : Fin m) (c d : Fin n) :
    Integrable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      ((ω p).1 * ((rOut F.C).mulVec (ω p).2.1 b * (rIn F.C).mulVec (ω p).2.2 c)) *
        ((ω p).1 * ((rOut F.C).mulVec (ω p).2.1 a * (rIn F.C).mulVec (ω p).2.2 d)))
      (indepSpaceLaw m n B) ∧
    ∫ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n),
      ((ω p).1 * ((rOut F.C).mulVec (ω p).2.1 b * (rIn F.C).mulVec (ω p).2.2 c)) *
        ((ω p).1 * ((rOut F.C).mulVec (ω p).2.1 a * (rIn F.C).mulVec (ω p).2.2 d))
      ∂(indepSpaceLaw m n B) = F.C.Sout b a * F.C.Sin c d := by
  have hm : MeasurePreserving (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω p)
      (indepSpaceLaw m n B) (indepSlotLaw m n) :=
    ⟨measurable_pi_apply p, by unfold indepSpaceLaw; exact Measure.infinitePi_map_eval _ p⟩
  obtain ⟨h1, h2⟩ := tdx_slot F b a c d
  refine ⟨hm.integrable_comp_of_integrable h1, ?_⟩
  have h1' := h1.aestronglyMeasurable
  rw [← hm.map_eq] at h1'
  have h3 := integral_map (μ := indepSpaceLaw m n B) hm.measurable.aemeasurable h1'
  rw [hm.map_eq] at h3
  exact h3.symm.trans h2

private lemma tdx_flip_slot (p : ℤ × Fin B) :
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
    · simp only [h, ite_false]; exact measurable_id
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

private lemma tdx_hh_meas (F : FrozenParams m n B) (p : ℤ × Fin B) (b : Fin m) (c : Fin n) :
    Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      (ω p).1 * ((rOut F.C).mulVec (ω p).2.1 b * (rIn F.C).mulVec (ω p).2.2 c)) := by
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

private lemma tdx_cross (F : FrozenParams m n B) {p q : ℤ × Fin B} (hpq : p ≠ q)
    (b a : Fin m) (c d : Fin n) :
    Integrable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      ((ω p).1 * ((rOut F.C).mulVec (ω p).2.1 b * (rIn F.C).mulVec (ω p).2.2 c)) *
        ((ω q).1 * ((rOut F.C).mulVec (ω q).2.1 a * (rIn F.C).mulVec (ω q).2.2 d)))
      (indepSpaceLaw m n B) ∧
    ∫ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n),
      ((ω p).1 * ((rOut F.C).mulVec (ω p).2.1 b * (rIn F.C).mulVec (ω p).2.2 c)) *
        ((ω q).1 * ((rOut F.C).mulVec (ω q).2.1 a * (rIn F.C).mulVec (ω q).2.2 d))
      ∂(indepSpaceLaw m n B) = 0 := by
  classical
  set U : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → ℝ := fun ω =>
    (ω p).1 * ((rOut F.C).mulVec (ω p).2.1 b * (rIn F.C).mulVec (ω p).2.2 c) with hU
  set V : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → ℝ := fun ω =>
    (ω q).1 * ((rOut F.C).mulVec (ω q).2.1 a * (rIn F.C).mulVec (ω q).2.2 d) with hV
  have hUm : Measurable U := tdx_hh_meas F p b c
  have hVm : Measurable V := tdx_hh_meas F q a d
  have hUU : Integrable (fun ω => U ω * U ω) (indepSpaceLaw m n B) := (tdx_diag F p b b c c).1
  have hVV : Integrable (fun ω => V ω * V ω) (indepSpaceLaw m n B) := (tdx_diag F q a a d d).1
  have hint : Integrable (fun ω => U ω * V ω) (indepSpaceLaw m n B) := by
    refine ((hUU.add hVV).div_const 2).mono' (hUm.mul hVm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    show ‖U ω * V ω‖ ≤ (U ω * U ω + V ω * V ω) / 2
    rw [Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (U ω - V ω), sq_nonneg (U ω + V ω)]
  refine ⟨hint, ?_⟩
  have hT := tdx_flip_slot (m := m) (n := n) (B := B) p
  let e : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) ≃ᵐ ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) :=
    { toFun := fun ω i => if i = p then (-(ω i).1, (ω i).2) else ω i
      invFun := fun ω i => if i = p then (-(ω i).1, (ω i).2) else ω i
      left_inv := fun ω => by funext i; by_cases h : i = p <;> simp [h]
      right_inv := fun ω => by funext i; by_cases h : i = p <;> simp [h]
      measurable_toFun := hT.measurable
      measurable_invFun := hT.measurable }
  have hTe : MeasurePreserving e (indepSpaceLaw m n B) (indepSpaceLaw m n B) := hT
  have hkey : ∀ ω, (fun ω => U ω * V ω) (e ω) = -(U ω * V ω) := by
    intro ω
    have h1 : (e ω) p = (-(ω p).1, (ω p).2) := by simp [e]
    have h2 : (e ω) q = ω q := by simp [e, hpq.symm]
    simp only [hU, hV, h1, h2]
    ring
  have h1 : ∫ ω, (fun ω => U ω * V ω) (e ω) ∂(indepSpaceLaw m n B) =
      ∫ ω, U ω * V ω ∂(indepSpaceLaw m n B) :=
    hTe.integral_comp' (fun ω => U ω * V ω)
  have h2 : ∫ ω, (fun ω => U ω * V ω) (e ω) ∂(indepSpaceLaw m n B) =
      -∫ ω, U ω * V ω ∂(indepSpaceLaw m n B) := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => hkey ω)
  linarith [h1, h2]

private lemma tdx_rOut_outer_rIn (F : FrozenParams m n B) (z : Vec m) (w : Vec n) :
    rOut F.C * outer z w * rIn F.C =
      outer (Matrix.mulVec (rOut F.C) z) (Matrix.mulVec (rIn F.C) w) := by
  have hv : Matrix.vecMul w (rIn F.C) = Matrix.mulVec (rIn F.C) w := by
    rw [← Matrix.vecMul_transpose, tdx_rIn_symm]
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hv]

private lemma tdx_batch_entry (F : FrozenParams m n B)
    (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) (s : ℤ) (b : Fin m) (c : Fin n) :
    indepBatchG F ω s b c = (B : ℝ)⁻¹ * ∑ a' : Fin B, (ω (s, a')).1 *
      ((rOut F.C).mulVec (ω (s, a')).2.1 b * (rIn F.C).mulVec (ω (s, a')).2.2 c) := by
  unfold indepBatchG
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [tdx_rOut_outer_rIn]
  simp [outer, Matrix.vecMulVec_apply]

private lemma tdx_pair (F : FrozenParams m n B) (p q : ℤ × Fin B) (b a : Fin m) (c d : Fin n) :
    Integrable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      ((ω p).1 * ((rOut F.C).mulVec (ω p).2.1 b * (rIn F.C).mulVec (ω p).2.2 c)) *
        ((ω q).1 * ((rOut F.C).mulVec (ω q).2.1 a * (rIn F.C).mulVec (ω q).2.2 d)))
      (indepSpaceLaw m n B) ∧
    ∫ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n),
      ((ω p).1 * ((rOut F.C).mulVec (ω p).2.1 b * (rIn F.C).mulVec (ω p).2.2 c)) *
        ((ω q).1 * ((rOut F.C).mulVec (ω q).2.1 a * (rIn F.C).mulVec (ω q).2.2 d))
      ∂(indepSpaceLaw m n B) = if p = q then F.C.Sout b a * F.C.Sin c d else 0 := by
  by_cases h : p = q
  · subst h
    simp only [ite_true]
    exact tdx_diag F p b a c d
  · simp only [h, ite_false]
    exact tdx_cross F h b a c d

private lemma tdx_batch_cov (F : FrozenParams m n B) (s s' : ℤ) (b a : Fin m) (c d : Fin n) :
    Integrable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      indepBatchG F ω s b c * indepBatchG F ω s' a d) (indepSpaceLaw m n B) ∧
    ∫ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n),
      indepBatchG F ω s b c * indepBatchG F ω s' a d ∂(indepSpaceLaw m n B) =
      if s = s' then (B : ℝ)⁻¹ * (F.C.Sout b a * F.C.Sin c d) else 0 := by
  classical
  have hfun : ∀ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n),
      indepBatchG F ω s b c * indepBatchG F ω s' a d =
      ((B : ℝ)⁻¹ * (B : ℝ)⁻¹) * ∑ a1 : Fin B, ∑ a2 : Fin B,
        (((ω (s, a1)).1 * ((rOut F.C).mulVec (ω (s, a1)).2.1 b *
            (rIn F.C).mulVec (ω (s, a1)).2.2 c)) *
          ((ω (s', a2)).1 * ((rOut F.C).mulVec (ω (s', a2)).2.1 a *
            (rIn F.C).mulVec (ω (s', a2)).2.2 d))) := by
    intro ω
    rw [tdx_batch_entry, tdx_batch_entry, mul_mul_mul_comm, Finset.sum_mul_sum]
  simp_rw [hfun]
  refine ⟨(integrable_finsetSum _ fun a1 _ => integrable_finsetSum _ fun a2 _ =>
    (tdx_pair F (s, a1) (s', a2) b a c d).1).const_mul _, ?_⟩
  rw [integral_const_mul, integral_finsetSum _ fun a1 _ =>
    integrable_finsetSum _ fun a2 _ => (tdx_pair F (s, a1) (s', a2) b a c d).1]
  have h1 : ∀ a1 : Fin B, ∫ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n), ∑ a2 : Fin B,
      (((ω (s, a1)).1 * ((rOut F.C).mulVec (ω (s, a1)).2.1 b *
            (rIn F.C).mulVec (ω (s, a1)).2.2 c)) *
          ((ω (s', a2)).1 * ((rOut F.C).mulVec (ω (s', a2)).2.1 a *
            (rIn F.C).mulVec (ω (s', a2)).2.2 d))) ∂(indepSpaceLaw m n B) =
      ∑ a2 : Fin B, (if (s, a1) = (s', a2) then F.C.Sout b a * F.C.Sin c d else 0) := by
    intro a1
    rw [integral_finsetSum _ fun a2 _ => (tdx_pair F (s, a1) (s', a2) b a c d).1]
    exact Finset.sum_congr rfl fun a2 _ => (tdx_pair F (s, a1) (s', a2) b a c d).2
  simp_rw [h1]
  by_cases hs : s = s'
  · subst hs
    simp only [Prod.mk.injEq, true_and, ite_true, Finset.sum_ite_eq, Finset.mem_univ,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    by_cases hB : (B : ℝ) = 0
    · simp [hB]
    · field_simp
  · simp [hs]

private lemma tdx_batch_abs (F : FrozenParams m n B) (s s' : ℤ) (b a : Fin m) (c d : Fin n) :
    Integrable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      indepBatchG F ω s b c * indepBatchG F ω s' a d) (indepSpaceLaw m n B) ∧
    ∫ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n),
      ‖indepBatchG F ω s b c * indepBatchG F ω s' a d‖ ∂(indepSpaceLaw m n B) ≤
      ((B : ℝ)⁻¹ * (F.C.Sout b b * F.C.Sin c c) + (B : ℝ)⁻¹ * (F.C.Sout a a * F.C.Sin d d)) / 2 := by
  have h1 := tdx_batch_cov F s s b b c c
  have h2 := tdx_batch_cov F s' s' a a d d
  refine ⟨(tdx_batch_cov F s s' b a c d).1, ?_⟩
  have hint := (tdx_batch_cov F s s' b a c d).1
  have hle : ∫ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n),
      ‖indepBatchG F ω s b c * indepBatchG F ω s' a d‖ ∂(indepSpaceLaw m n B) ≤
      ∫ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n),
        (indepBatchG F ω s b c * indepBatchG F ω s b c +
          indepBatchG F ω s' a d * indepBatchG F ω s' a d) / 2 ∂(indepSpaceLaw m n B) := by
    refine integral_mono hint.norm ((h1.1.add h2.1).div_const 2) fun ω => ?_
    show ‖indepBatchG F ω s b c * indepBatchG F ω s' a d‖ ≤ _
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [sq_nonneg (indepBatchG F ω s b c - indepBatchG F ω s' a d),
      sq_nonneg (indepBatchG F ω s b c + indepBatchG F ω s' a d)]
  refine hle.trans (le_of_eq ?_)
  rw [integral_div, integral_add h1.1 h2.1, h1.2, h2.2]
  simp

private lemma tdx_abs_entry_le_fro (K : Mat m n) (i : Fin m) (k : Fin n) : |K i k| ≤ fro K := by
  unfold fro
  refine Real.abs_le_sqrt ?_
  have h1 : ‖K i k‖ ^ 2 ≤ ∑ k', ‖K i k'‖ ^ 2 :=
    Finset.single_le_sum (f := fun k' => ‖K i k'‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ k)
  have h2 : ∑ k', ‖K i k'‖ ^ 2 ≤ ∑ i', ∑ k', ‖K i' k'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ k', ‖K i' k'‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)
  have h3 : K i k ^ 2 = ‖K i k‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  rw [h3]
  exact h1.trans h2

private lemma tdx_emaW_nonneg (F : FrozenParams m n B) (j : ℕ) : 0 ≤ emaW F.β j := by
  unfold emaW
  exact mul_nonneg (by linarith [F.hβ.2]) (pow_nonneg F.hβ.1 j)

private lemma tdx_emaW_summable (F : FrozenParams m n B) : Summable (fun j : ℕ => emaW F.β j) := by
  unfold emaW
  exact (summable_geometric_of_lt_one F.hβ.1 F.hβ.2).mul_left _

open scoped Matrix.Norms.Frobenius in
private lemma tdx_ae_hasSum (F : FrozenParams m n B) :
    ∀ᵐ ω ∂(indepSpaceLaw m n B), ∀ (t' : ℤ) (b : Fin m) (c : Fin n),
      HasSum (fun j : ℕ => emaW F.β j * indepBatchG F ω (t' + 1 - (j : ℤ)) b c)
        (def_app_vol_product F ω t' b c) ∧
      Summable (fun j : ℕ => |emaW F.β j * indepBatchG F ω (t' + 1 - (j : ℤ)) b c|) := by
  filter_upwards [def_app_vol_product_summable F] with ω hω t' b c
  have hs : Summable fun j : ℕ => emaW F.β j • indepBatchG F ω (t' + 1 - (j : ℤ)) := by
    refine Summable.of_norm ?_
    simpa [fro_eq_norm] using hω t'
  refine ⟨?_, ?_⟩
  · have h := hs.hasSum
    have h2 := Pi.hasSum.mp h b
    have h3 := Pi.hasSum.mp h2 c
    simpa [def_app_vol_product] using h3
  · refine Summable.of_nonneg_of_le (fun j => abs_nonneg _) (fun j => ?_) (hω t')
    have := tdx_abs_entry_le_fro (emaW F.β j • indepBatchG F ω (t' + 1 - (j : ℤ))) b c
    simpa using this

private lemma tdx_batch_meas (F : FrozenParams m n B) (s : ℤ) (b : Fin m) (c : Fin n) :
    Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => indepBatchG F ω s b c) := by
  simp_rw [tdx_batch_entry]
  exact Measurable.const_mul (Finset.measurable_sum _ fun a' _ => tdx_hh_meas F (s, a') b c) _

private lemma tdx_entry_aem (F : FrozenParams m n B) (t : ℤ) (b : Fin m) (c : Fin n) :
    AEMeasurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      def_app_vol_product F ω t b c) (indepSpaceLaw m n B) := by
  refine aemeasurable_of_tendsto_metrizable_ae Filter.atTop
    (f := fun (N : ℕ) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) =>
      ∑ j ∈ Finset.range N, emaW F.β j * indepBatchG F ω (t + 1 - (j : ℤ)) b c)
    (fun N => by
      have : Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
          ∑ j ∈ Finset.range N, emaW F.β j * indepBatchG F ω (t + 1 - (j : ℤ)) b c) :=
        Finset.measurable_sum _ fun j _ =>
          (tdx_batch_meas F (t + 1 - (j : ℤ)) b c).const_mul (emaW F.β j)
      exact this.aemeasurable) ?_
  filter_upwards [tdx_ae_hasSum F] with ω hω
  exact (hω t b c).1.tendsto_sum_nat

private lemma tdx_entry_cov (F : FrozenParams m n B) (ℓ : ℕ) (t : ℤ) (b a : Fin m) (c d : Fin n) :
    Integrable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
      def_app_vol_product F ω t b c * def_app_vol_product F ω (t + (ℓ : ℤ)) a d)
      (indepSpaceLaw m n B) ∧
    ∫ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n),
      def_app_vol_product F ω t b c * def_app_vol_product F ω (t + (ℓ : ℤ)) a d
      ∂(indepSpaceLaw m n B) =
      F.β ^ ℓ * sPow F.β 2 * ((B : ℝ)⁻¹ * (F.C.Sout b a * F.C.Sin c d)) := by
  classical
  set μ := indepSpaceLaw m n B with hμ
  set w : ℕ → ℝ := fun j => emaW F.β j with hw
  set Kc : ℝ := (B : ℝ)⁻¹ * (F.C.Sout b a * F.C.Sin c d) with hKc
  set K0 : ℝ := ((B : ℝ)⁻¹ * (F.C.Sout b b * F.C.Sin c c) +
    (B : ℝ)⁻¹ * (F.C.Sout a a * F.C.Sin d d)) / 2 with hK0
  set Fz : ℕ × ℕ → ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → ℝ := fun z ω =>
    (w z.1 * indepBatchG F ω (t + 1 - (z.1 : ℤ)) b c) *
      (w z.2 * indepBatchG F ω (t + (ℓ : ℤ) + 1 - (z.2 : ℤ)) a d) with hFz
  have hw0 : ∀ j, 0 ≤ w j := fun j => tdx_emaW_nonneg F j
  have hwS : Summable w := tdx_emaW_summable F
  have hFeq : ∀ z ω, Fz z ω = (w z.1 * w z.2) *
      (indepBatchG F ω (t + 1 - (z.1 : ℤ)) b c *
        indepBatchG F ω (t + (ℓ : ℤ) + 1 - (z.2 : ℤ)) a d) := fun z ω => by
    simp only [hFz]; ring
  have hFint : ∀ z, Integrable (Fz z) μ ∧ ∫ ω, Fz z ω ∂μ =
      w z.1 * w z.2 * (if (t + 1 - (z.1 : ℤ)) = (t + (ℓ : ℤ) + 1 - (z.2 : ℤ)) then Kc else 0) := by
    intro z
    have h := tdx_batch_cov F (t + 1 - (z.1 : ℤ)) (t + (ℓ : ℤ) + 1 - (z.2 : ℤ)) b a c d
    have e : Fz z = fun ω => (w z.1 * w z.2) *
        (indepBatchG F ω (t + 1 - (z.1 : ℤ)) b c *
          indepBatchG F ω (t + (ℓ : ℤ) + 1 - (z.2 : ℤ)) a d) := funext (hFeq z)
    rw [e]
    refine ⟨h.1.const_mul _, ?_⟩
    rw [integral_const_mul, h.2]
  have hnorm : ∀ z, ∫ ω, ‖Fz z ω‖ ∂μ ≤ w z.1 * w z.2 * K0 := by
    intro z
    have h := tdx_batch_abs F (t + 1 - (z.1 : ℤ)) (t + (ℓ : ℤ) + 1 - (z.2 : ℤ)) b a c d
    have hn : ∀ ω, ‖Fz z ω‖ = (w z.1 * w z.2) *
        ‖indepBatchG F ω (t + 1 - (z.1 : ℤ)) b c *
          indepBatchG F ω (t + (ℓ : ℤ) + 1 - (z.2 : ℤ)) a d‖ := by
      intro ω
      rw [hFeq, norm_mul, Real.norm_of_nonneg (mul_nonneg (hw0 _) (hw0 _))]
    simp_rw [hn]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left h.2 (mul_nonneg (hw0 _) (hw0 _))
  have hwS2 : Summable (fun z : ℕ × ℕ => w z.1 * w z.2) :=
    hwS.mul_of_nonneg hwS (fun j => hw0 j) (fun j => hw0 j)
  have hsumm : Summable (fun z => ∫ ω, ‖Fz z ω‖ ∂μ) :=
    Summable.of_nonneg_of_le (fun z => integral_nonneg fun ω => norm_nonneg _) hnorm
      (hwS2.mul_right K0)
  -- almost sure product formula
  have hae : ∀ᵐ ω ∂μ, def_app_vol_product F ω t b c * def_app_vol_product F ω (t + (ℓ : ℤ)) a d
      = ∑' z, Fz z ω := by
    filter_upwards [tdx_ae_hasSum F] with ω hω
    obtain ⟨h1, h1'⟩ := hω t b c
    obtain ⟨h2, h2'⟩ := hω (t + (ℓ : ℤ)) a d
    rw [← h1.tsum_eq, ← h2.tsum_eq]
    exact tsum_mul_tsum_of_summable_norm (by simpa using h1') (by simpa using h2')
  have hlin : ∑' z, ∫⁻ ω, ‖Fz z ω‖ₑ ∂μ ≠ ⊤ := by
    have h1 : ∀ z, ∫⁻ ω, ‖Fz z ω‖ₑ ∂μ = ENNReal.ofReal (∫ ω, ‖Fz z ω‖ ∂μ) := fun z =>
      (ofReal_integral_norm_eq_lintegral_enorm (hFint z).1).symm
    simp_rw [h1]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun z => integral_nonneg fun ω => norm_nonneg _) hsumm]
    exact ENNReal.ofReal_ne_top
  have hint : Integrable (fun ω => def_app_vol_product F ω t b c *
      def_app_vol_product F ω (t + (ℓ : ℤ)) a d) μ := by
    refine ⟨((tdx_entry_aem F t b c).mul (tdx_entry_aem F (t + (ℓ : ℤ)) a d)).aestronglyMeasurable,
      ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ ω, ‖def_app_vol_product F ω t b c * def_app_vol_product F ω (t + (ℓ : ℤ)) a d‖ₑ ∂μ
        = ∫⁻ ω, ‖∑' z, Fz z ω‖ₑ ∂μ := lintegral_congr_ae (hae.mono fun ω h => congrArg (fun x => ‖x‖ₑ) h)
      _ ≤ ∫⁻ ω, ∑' z, ‖Fz z ω‖ₑ ∂μ := lintegral_mono fun ω => enorm_tsum_le_tsum_enorm
      _ = ∑' z, ∫⁻ ω, ‖Fz z ω‖ₑ ∂μ :=
          lintegral_tsum fun z => (hFint z).1.aemeasurable.enorm
      _ < ⊤ := lt_top_iff_ne_top.2 hlin
  refine ⟨hint, ?_⟩
  rw [integral_congr_ae hae, integral_tsum (fun z => (hFint z).1.aestronglyMeasurable) hlin]
  simp_rw [fun z => (hFint z).2]
  -- evaluation of the double series
  have hcond : ∀ j j' : ℕ, ((t + 1 - (j : ℤ)) = (t + (ℓ : ℤ) + 1 - (j' : ℤ))) ↔ j' = j + ℓ := by
    intro j j'
    constructor
    · intro h; omega
    · intro h; subst h; push_cast; ring
  have hsumF : Summable (fun z : ℕ × ℕ => w z.1 * w z.2 *
      (if (t + 1 - (z.1 : ℤ)) = (t + (ℓ : ℤ) + 1 - (z.2 : ℤ)) then Kc else 0)) := by
    refine Summable.of_norm_bounded (hwS2.mul_right |Kc|) fun z => ?_
    rw [norm_mul, Real.norm_of_nonneg (mul_nonneg (hw0 _) (hw0 _))]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hw0 _) (hw0 _))
    split_ifs
    · exact le_of_eq (Real.norm_eq_abs _)
    · simp
  rw [hsumF.tsum_prod' (fun j => hsumF.prod_factor j)]
  have hinner : ∀ j : ℕ, ∑' j' : ℕ, w j * w j' *
      (if (t + 1 - (j : ℤ)) = (t + (ℓ : ℤ) + 1 - (j' : ℤ)) then Kc else 0) =
      w j * w (j + ℓ) * Kc := by
    intro j
    have : (fun j' : ℕ => w j * w j' *
        (if (t + 1 - (j : ℤ)) = (t + (ℓ : ℤ) + 1 - (j' : ℤ)) then Kc else 0)) =
        fun j' => if j' = j + ℓ then w j * w (j + ℓ) * Kc else 0 := by
      funext j'
      by_cases h : j' = j + ℓ
      · subst h
        rw [if_pos ((hcond j (j + ℓ)).2 rfl), if_pos rfl]
      · rw [if_neg (fun h' => h ((hcond j j').1 h')), if_neg h]; simp
    rw [this, tsum_ite_eq]
  simp_rw [hinner]
  have hshift : ∀ j : ℕ, w j * w (j + ℓ) * Kc = (F.β ^ ℓ * Kc) * w j ^ 2 := by
    intro j
    simp only [hw, emaW]
    ring
  simp_rw [hshift]
  rw [tsum_mul_left]
  have : sPow F.β 2 = ∑' j : ℕ, w j ^ 2 := rfl
  rw [this]
  ring

private lemma tdx_trace_expand (Fm : Mat m m) (Gm : Mat n n) (X Y : Mat m n) :
    Matrix.trace (Fm * X * Gm * Yᵀ) =
      ∑ a : Fin m, ∑ d : Fin n, ∑ c : Fin n, ∑ b : Fin m,
        (Fm a b * Gm c d) * (X b c * Y a d) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring

private lemma tdx_sum_reorder (P : Fin m → Fin n → Fin n → Fin m → ℝ) :
    ∑ a : Fin m, ∑ d : Fin n, ∑ c : Fin n, ∑ b : Fin m, P a d c b =
      ∑ c : Fin n, ∑ d : Fin n, ∑ b : Fin m, ∑ a : Fin m, P a d c b := by
  calc ∑ a : Fin m, ∑ d : Fin n, ∑ c : Fin n, ∑ b : Fin m, P a d c b
      = ∑ d : Fin n, ∑ a : Fin m, ∑ c : Fin n, ∑ b : Fin m, P a d c b := Finset.sum_comm
    _ = ∑ d : Fin n, ∑ c : Fin n, ∑ a : Fin m, ∑ b : Fin m, P a d c b :=
        Finset.sum_congr rfl fun d _ => Finset.sum_comm
    _ = ∑ d : Fin n, ∑ c : Fin n, ∑ b : Fin m, ∑ a : Fin m, P a d c b :=
        Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c : Fin n, ∑ d : Fin n, ∑ b : Fin m, ∑ a : Fin m, P a d c b := Finset.sum_comm

private lemma tdx_trace_sums (F : FrozenParams m n B) (Fm : Mat m m) (Gm : Mat n n) (K : ℝ) :
    ∑ a : Fin m, ∑ d : Fin n, ∑ c : Fin n, ∑ b : Fin m,
        (Fm a b * Gm c d) * (K * (F.C.Sout b a * F.C.Sin c d)) =
      K * (Matrix.trace (F.C.Sout * Fm) * Matrix.trace (F.C.Sin * Gm)) := by
  have hsym : ∀ c d : Fin n, F.C.Sin d c = F.C.Sin c d := fun c d => by
    have := F.C.psdIn.isHermitian.apply c d
    simpa using this
  have htr1 : Matrix.trace (F.C.Sout * Fm) = ∑ b : Fin m, ∑ a : Fin m, F.C.Sout b a * Fm a b := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  have htr2 : Matrix.trace (F.C.Sin * Gm) = ∑ c : Fin n, ∑ d : Fin n, F.C.Sin c d * Gm c d := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by rw [hsym]
  rw [tdx_sum_reorder (fun a d c b => (Fm a b * Gm c d) * (K * (F.C.Sout b a * F.C.Sin c d))),
    htr1, htr2]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

private lemma tdx_final (Fp : FrozenParams m n B) (ℓ : ℕ) (Fm : Mat m m) (Gm : Mat n n)
    (t : ℤ) :
    Integrable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
        (B : ℝ)⁻¹ * Matrix.trace
          (Fm * def_app_vol_product Fp ω t * Gm * (def_app_vol_product Fp ω (t + (ℓ : ℤ)))ᵀ))
      (indepSpaceLaw m n B) ∧
    ∫ ω, (B : ℝ)⁻¹ * Matrix.trace
          (Fm * def_app_vol_product Fp ω t * Gm * (def_app_vol_product Fp ω (t + (ℓ : ℤ)))ᵀ)
        ∂(indepSpaceLaw m n B) =
      Fp.β ^ ℓ * sPow Fp.β 2 * ((B : ℝ)⁻¹) ^ 2 *
        Matrix.trace (Fp.C.Sout * Fm) * Matrix.trace (Fp.C.Sin * Gm) := by
  classical
  simp_rw [tdx_trace_expand]
  have hI : ∀ (a : Fin m) (d : Fin n) (c : Fin n) (b : Fin m),
      Integrable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
        (Fm a b * Gm c d) * (def_app_vol_product Fp ω t b c *
          def_app_vol_product Fp ω (t + (ℓ : ℤ)) a d)) (indepSpaceLaw m n B) :=
    fun a d c b => (tdx_entry_cov Fp ℓ t b a c d).1.const_mul _
  have hval : ∀ (a : Fin m) (d : Fin n) (c : Fin n) (b : Fin m),
      ∫ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n), (Fm a b * Gm c d) *
        (def_app_vol_product Fp ω t b c * def_app_vol_product Fp ω (t + (ℓ : ℤ)) a d)
        ∂(indepSpaceLaw m n B) =
      (Fm a b * Gm c d) * ((Fp.β ^ ℓ * sPow Fp.β 2 * (B : ℝ)⁻¹) *
        (Fp.C.Sout b a * Fp.C.Sin c d)) := by
    intro a d c b
    rw [integral_const_mul, (tdx_entry_cov Fp ℓ t b a c d).2]
    ring
  refine ⟨(integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun d _ =>
    integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun b _ => hI a d c b).const_mul _, ?_⟩
  rw [integral_const_mul, integral_finsetSum _ fun a _ => integrable_finsetSum _ fun d _ =>
    integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun b _ => hI a d c b]
  have h1 : ∀ a : Fin m, ∫ ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n), ∑ d : Fin n, ∑ c : Fin n,
      ∑ b : Fin m, (Fm a b * Gm c d) *
        (def_app_vol_product Fp ω t b c * def_app_vol_product Fp ω (t + (ℓ : ℤ)) a d)
      ∂(indepSpaceLaw m n B) = ∑ d : Fin n, ∑ c : Fin n, ∑ b : Fin m, (Fm a b * Gm c d) *
        ((Fp.β ^ ℓ * sPow Fp.β 2 * (B : ℝ)⁻¹) * (Fp.C.Sout b a * Fp.C.Sin c d)) := by
    intro a
    rw [integral_finsetSum _ fun d _ => integrable_finsetSum _ fun c _ =>
      integrable_finsetSum _ fun b _ => hI a d c b]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun b _ => hI a d c b]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_finsetSum _ fun b _ => hI a d c b]
    exact Finset.sum_congr rfl fun b _ => hval a d c b
  simp_rw [h1]
  rw [tdx_trace_sums Fp Fm Gm]
  ring

/-- Helper of `def:app-vol-tree`, snapshot `cr-2026-10-23`, the exact value (l.1072–1074): for the independent product model
`M^g` of `def:app-vol-product` on `indepSpaceLaw`, `B^{-1} 𝔼 Tr[F M^g_t G (M^g_{t+ℓ})ᵀ]` is integrable
and equals `β^ℓ s_2 B^{-2} Tr(Σ_out F) Tr(Σ_in G)`, for arbitrary test matrices `F`, `G`. The statement
asserts integrability as part of "the exact value" (the expectation is asserted to exist). Sorried. -/
theorem def_app_vol_tree_exact (Fp : FrozenParams m n B) (ℓ : ℕ) (Fm : Mat m m) (Gm : Mat n n)
    (t : ℤ) :
    Integrable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) =>
        (B : ℝ)⁻¹ * Matrix.trace
          (Fm * def_app_vol_product Fp ω t * Gm * (def_app_vol_product Fp ω (t + (ℓ : ℤ)))ᵀ))
      (indepSpaceLaw m n B) ∧
    ∫ ω, (B : ℝ)⁻¹ * Matrix.trace
          (Fm * def_app_vol_product Fp ω t * Gm * (def_app_vol_product Fp ω (t + (ℓ : ℤ)))ᵀ)
        ∂(indepSpaceLaw m n B) =
      Fp.β ^ ℓ * sPow Fp.β 2 * ((B : ℝ)⁻¹) ^ 2 *
        Matrix.trace (Fp.C.Sout * Fm) * Matrix.trace (Fp.C.Sin * Gm) := by
  exact tdx_final Fp ℓ Fm Gm t

/-- Private helper: summing over the replicated index set `Fin (N * m)` multiplies by `N`. -/
private lemma tree_repl_sum {m N : ℕ} (f : Fin m → ℝ) :
    ∑ x : Fin (N * m), f ((replIdx m N).symm x).1 = (N : ℝ) * ∑ i, f i := by
  have h := Equiv.sum_comp (replIdx m N).symm (fun y : Fin m × Fin N => f y.1)
  rw [h, Fintype.sum_prod_type]
  simp [Finset.mul_sum]

/-- Private helper: the replicated batch-normalised weighted sum equals the original one. -/
private lemma tree_repl_fac {m N B : ℕ} (hN : 1 ≤ N) (μ Fd : Fin m → ℝ) (p q : ℕ) :
    ((N * B : ℕ) : ℝ)⁻¹ * ∑ x : Fin (N * m), μ ((replIdx m N).symm x).1 ^ p *
        Fd ((replIdx m N).symm x).1 ^ q =
      (B : ℝ)⁻¹ * ∑ i, μ i ^ p * Fd i ^ q := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hfac : ((N : ℝ) * B)⁻¹ * N = (B : ℝ)⁻¹ := by
    rw [mul_inv, mul_comm (N : ℝ)⁻¹, mul_assoc, inv_mul_cancel₀ hNr, mul_one]
  have key := tree_repl_sum (N := N) (fun i => μ i ^ p * Fd i ^ q)
  rw [key, Nat.cast_mul, ← mul_assoc, hfac]

/-- Private helper: the class factor is invariant under the replication (`N B` batch, `N` copies). -/
private lemma tree_repl_class {m n : ℕ} (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B N : ℕ) (hN : 1 ≤ N)
    (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (a b : ℕ)
    (p : TreeMatch (treeK a b) × TreeMatch (treeK a b)) (V : Quotient (treeSetoid p)) :
    treeClassFactor β ℓ J R (N * B) (fun x => μ ((replIdx m N).symm x).1)
        (fun y => lam ((replIdx n N).symm y).1) (fun x => Fd ((replIdx m N).symm x).1)
        (fun y => Gd ((replIdx n N).symm y).1) a b p V =
      treeClassFactor β ℓ J R B μ lam Fd Gd a b p V := by
  dsimp only [treeClassFactor]
  split_ifs <;> first
    | exact tree_repl_fac hN μ Fd _ _
    | exact tree_repl_fac hN lam Gd _ _
    | rfl

/-- Helper of `lem:app-vol-tree-closure`, snapshot `cr-2026-10-23` (l.1083–1084): the response is unchanged under the replications of
`def:app-vol-replication` (`N ≥ 1`): replicated eigenvalues `μ_i`, `λ_j` and diagonal test entries are
repeated `N` times, the batch size becomes `NB`. Verbatim:
```latex
The response is unchanged under the replications of
\cref{def:app-vol-replication}.
```
Sorried. -/
theorem def_app_vol_tree_replication (β : ℝ) (ℓ J : ℕ) (R : ℝ) (B : ℕ) (μ : Fin m → ℝ)
    (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (N : ℕ) (hN : 1 ≤ N)
    (f₁ f₂ : Polynomial ℝ) :
    def_app_vol_tree β ℓ J R (N * B) (fun x => μ ((replIdx m N).symm x).1)
        (fun y => lam ((replIdx n N).symm y).1) (fun x => Fd ((replIdx m N).symm x).1)
        (fun y => Gd ((replIdx n N).symm y).1) f₁ f₂ =
      def_app_vol_tree β ℓ J R B μ lam Fd Gd f₁ f₂ := by
  unfold def_app_vol_tree
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  unfold treeMono
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs
  · exact Finset.prod_congr rfl fun V _ => tree_repl_class β ℓ J R B N hN μ lam Fd Gd a b p V
  · rfl

private lemma tw_upperRight_reindex {m n : ℕ} (M : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ) :
    Muon.Foundations.upperRight (Matrix.reindex finSumFinEquiv finSumFinEquiv M) = M.toBlocks₁₂ := by
  ext i j
  simp [Muon.Foundations.upperRight, Matrix.reindex_apply, Matrix.toBlocks₁₂]

private lemma tw_ur_add {m n : ℕ} (X Y : Mat (m + n) (m + n)) :
    Muon.Foundations.upperRight (X + Y) = Muon.Foundations.upperRight X + Muon.Foundations.upperRight Y := by
  ext i j; simp [Muon.Foundations.upperRight]

private lemma tw_ur_smul {m n : ℕ} (c : ℝ) (X : Mat (m + n) (m + n)) :
    Muon.Foundations.upperRight (c • X) = c • Muon.Foundations.upperRight X := by
  ext i j; simp [Muon.Foundations.upperRight]

private lemma tw_ur_sum {m n : ℕ} {ι : Type*} (s : Finset ι) (X : ι → Mat (m + n) (m + n)) :
    Muon.Foundations.upperRight (∑ i ∈ s, X i) = ∑ i ∈ s, Muon.Foundations.upperRight (X i) := by
  ext i j; simp [Muon.Foundations.upperRight, Matrix.sum_apply]

private lemma tw_blocks_sq {m n : ℕ} (K : Mat m n) :
    Matrix.fromBlocks (0 : Mat m m) K Kᵀ (0 : Mat n n) * Matrix.fromBlocks (0 : Mat m m) K Kᵀ (0 : Mat n n)
      = Matrix.fromBlocks (K * Kᵀ) 0 0 (Kᵀ * K) := by
  rw [Matrix.fromBlocks_multiply]; simp

private lemma tw_blocks_sq_pow {m n : ℕ} (K : Mat m n) (a : ℕ) :
    (Matrix.fromBlocks (K * Kᵀ) 0 0 (Kᵀ * K)) ^ a
      = Matrix.fromBlocks ((K * Kᵀ) ^ a) 0 0 ((Kᵀ * K) ^ a) := by
  induction a with
  | zero => simp [Matrix.fromBlocks_one]
  | succ a ih => rw [pow_succ, ih, Matrix.fromBlocks_multiply]; simp [pow_succ]

private lemma tw_dil_pow_odd {m n : ℕ} (K : Mat m n) (a : ℕ) :
    Muon.Foundations.upperRight ((Muon.Foundations.hermDilation K) ^ (2 * a + 1))
      = (K * Kᵀ) ^ a * K := by
  have h1 : (Muon.Foundations.hermDilation K) ^ (2 * a + 1)
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          ((Matrix.fromBlocks (0 : Mat m m) K Kᵀ (0 : Mat n n)) ^ (2 * a + 1)) := by
    unfold Muon.Foundations.hermDilation
    exact (map_pow (Matrix.reindexAlgEquiv ℝ ℝ finSumFinEquiv) _ _).symm
  rw [h1, tw_upperRight_reindex, pow_succ, pow_mul, pow_two, tw_blocks_sq, tw_blocks_sq_pow,
    Matrix.fromBlocks_multiply]
  ext i j
  simp [Matrix.toBlocks₁₂]

private lemma tw_sum_reindex {M : Type*} [AddCommMonoid M] (g : ℕ → M) (N : ℕ)
    (he : ∀ a, g (2 * a) = 0) (hN : ∀ i, N < i → g i = 0) :
    ∑ i ∈ Finset.range (N + 1), g i = ∑ a ∈ Finset.range (N + 1), g (2 * a + 1) := by
  have h1 : ∑ i ∈ Finset.range (N + 1), g i = ∑ i ∈ Finset.range (2 * (N + 1)), g i := by
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) ?_
    intro i hi hi'
    exact hN i (by simp at hi hi'; omega)
  have h2 : ∀ n, ∑ i ∈ Finset.range (2 * n), g i = ∑ a ∈ Finset.range n, (g (2 * a) + g (2 * a + 1)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, ih, Finset.sum_range_succ (fun a => g (2 * a) + g (2 * a + 1)), add_assoc]
  rw [h1, h2]
  simp [he]

private lemma tw_oddSharp_poly {m n : ℕ} (f : Polynomial ℝ) (hf : ∀ a : ℕ, f.coeff (2 * a) = 0)
    (K : Mat m n) :
    oddSharp (fun x => f.eval x) K =
      ∑ a ∈ Finset.range (f.natDegree + 1), f.coeff (2 * a + 1) • ((K * Kᵀ) ^ a * K) := by
  unfold oddSharp
  have hH := Muon.Foundations.hermDilation_isHermitian K
  rw [cfc_polynomial f _ (by exact hH), Polynomial.aeval_eq_sum_range]
  have hg := tw_sum_reindex (fun i => f.coeff i • (Muon.Foundations.hermDilation K) ^ i) f.natDegree
    (fun a => by simp [hf a]) (fun i hi => by simp [Polynomial.coeff_eq_zero_of_natDegree_lt hi])
  rw [hg, tw_ur_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [tw_ur_smul, tw_dil_pow_odd]

private lemma tw_transpose_odd {m n : ℕ} (K : Mat m n) (b : ℕ) :
    ((K * Kᵀ) ^ b * K)ᵀ = Kᵀ * (K * Kᵀ) ^ b := by
  rw [Matrix.transpose_mul, Matrix.transpose_pow, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- Word expansion of the paragraph after `def:app-vol-tree`, snapshot `cr-2026-10-23`, unlabelled
display (l.1017–1023): for odd polynomials `f₁ = ∑_a c_a x^{2a+1}` and `f₂ = ∑_b c'_b x^{2b+1}`
(encoded by `Polynomial ℝ` with vanishing even coefficients, the paper's "odd polynomials"),
`(1/B) Tr[F f₁^♯(K₁) G f₂^♯(K₂)ᵀ] = ∑_{a,b} c_a c'_b (1/B) Tr W_{a,b}`, with `W_{a,b} = treeWord`,
`f^♯ = oddSharp` (`eqn:app-vol-sharp`). Verbatim LaTeX:
```latex
even $r\ge2a+2$, and $X_r=\mathsf K_2$ for odd $r\ge2a+3$. The factor $X_r$ has
the label $l_r=1$ if $r\le2a+1$ and $l_r=2$ otherwise. For odd polynomials
$f_1(x)=\sum_ac_ax^{2a+1}$ and $f_2(x)=\sum_bc'_bx^{2b+1}$,
\[
\frac1B\Tr\big[F\,f_1^\sharp(\mathsf K_1)\,G\,f_2^\sharp(\mathsf K_2)^\T\big]=\sum_{a,b}c_ac'_b\,\frac1B\Tr\mathsf W_{a,b},
\]
by \cref{eqn:app-vol-sharp} and $(x^{2b+1})^\sharp(K)^\T=K^\T(KK^\T)^b$.
```
Sorried. -/
theorem def_app_vol_tree_word_expansion {m n B : ℕ} (F : Mat m m) (G : Mat n n) (K₁ K₂ : Mat m n)
    (f₁ f₂ : Polynomial ℝ) (hf₁ : ∀ a : ℕ, f₁.coeff (2 * a) = 0)
    (hf₂ : ∀ b : ℕ, f₂.coeff (2 * b) = 0) :
    (B : ℝ)⁻¹ * Matrix.trace
        (F * oddSharp (fun x => f₁.eval x) K₁ * G * (oddSharp (fun x => f₂.eval x) K₂)ᵀ) =
      ∑ a ∈ Finset.range (f₁.natDegree + 1), ∑ b ∈ Finset.range (f₂.natDegree + 1),
        f₁.coeff (2 * a + 1) * f₂.coeff (2 * b + 1) *
          ((B : ℝ)⁻¹ * Matrix.trace (treeWord F G K₁ K₂ a b)) := by
  rw [tw_oddSharp_poly f₁ hf₁ K₁, tw_oddSharp_poly f₂ hf₂ K₂, Matrix.transpose_sum]
  simp only [Matrix.transpose_smul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, tw_transpose_odd, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  unfold treeWord
  simp only [Matrix.mul_assoc]
  ring

end Muon.Volatility

end

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Muon.Volatility.TreeDef

/-!
# Appendix D, part 16: closed walks, plane trees and the encoding of retained pairings

Work package L-D.16 (interface draft). Snapshot `cr-2026-10-23`. Source of record:
`sections/04-volatility/section.tex`: the contour paragraph and `lem:app-vol-closed-contour`
(l.2069–2083), the typed-tree and arc paragraphs (l.2084–2128), `lem:app-vol-closed-encoding`
(l.2130–2139, proof l.2140–2171). Card: `sections/04-volatility/CARD.md` §2 (row "Ordered trees"),
§3 (rows `lem:app-vol-closed-contour`, `lem:app-vol-closed-encoding`), §5 (row L-D.16), §6 (F8, F16),
§8 Q9.

Reused, not redefined: `treeK`, `TreeVtx`, `TreeMatch`, `treeSetoid`, `treeMk`, `treeRetained`,
`treeFMark`, `treeGMark` (`Muon.Volatility`, L-D.11, `Muon/Volatility/TreeDef.lean`).

Encoding decisions (Lean representation of plane trees and contours; Q9):
* Plane trees: the nested inductive `PlaneTree` (a node with an ordered list of children). Vertices
  are their root-to-vertex addresses `List ℕ` (the child index at each level). The root is `[]`, the
  children of `u` are the vertices `u ++ [i]`. The contour `c(0),…,c(2n)` is a list of addresses.
  Mathlib has no plane trees; Catalan counting is stated through `TypedOrdTree`.
* Typed ordered trees: `TypedOrdTree k` is a plane tree with `k` edges, a typing `ty : List ℕ → VType`,
  root type `o`, every edge joining a latent to an external vertex, and cyclic alternation of
  `o`/`in` around every latent vertex. The typing is fixed to `o` off the vertex set, so that the type
  is finite (typing is determined by the tree; see `typedOrdTree_typing_unique`).
* Positions: `treePos` gives the 0-based contour position of a polygon vertex (paper `e_{s+1}` at
  `2(s+1)` mod `2k`, `l_{s+1}` at `2s+1`).
* The bijection of `lem:app-vol-closed-encoding` is stated with the class map `ι` as an explicit
  witness (`ClassFibreMap`), so that the "fibres of the contour" clause is literal.
* Walk hypotheses: `W : ℕ → V` on `0,…,2n`; "traverses every edge exactly twice" is the count of steps
  `i < 2n` whose edge is `e`, equal to `2`; `n` is `Nat.card T.edgeSet`.
-/

noncomputable section

open Muon Muon.Volatility

namespace Muon.Volatility

/-! ## Plane trees, addresses and contours -/

/-- Ordered (plane) rooted trees: a node with an ordered list of children (l.2069–2077). -/
inductive PlaneTree : Type where
  | node : List PlaneTree → PlaneTree

mutual

/-- Vertices of a plane tree as addresses: the root is `[]`; the vertices of the subtree of the `i`-th
child are the addresses of that subtree prefixed by `i`. -/
def PlaneTree.vtxs : PlaneTree → List (List ℕ)
  | .node cs => [] :: vtxsForest cs 0

/-- Vertex addresses of a list of subtrees, the first subtree having child index `i`. -/
def vtxsForest : List PlaneTree → ℕ → List (List ℕ)
  | [], _ => []
  | c :: cs, i => (PlaneTree.vtxs c).map (List.cons i) ++ vtxsForest cs (i + 1)

end

mutual

/-- The contour of a plane tree (l.2069–2077), as a list of addresses: the contour of a vertex `x` with
children `x₁,…,x_m` is `x`, the contour of `x₁`, `x`, …, the contour of `x_m`, `x`. Its length is
`2n+1` for `n` edges. -/
def PlaneTree.contour : PlaneTree → List (List ℕ)
  | .node cs => [] :: contourForest cs 0

/-- Contour of a list of subtrees, the first subtree having child index `i`; each subtree is followed by
the parent's visit. -/
def contourForest : List PlaneTree → ℕ → List (List ℕ)
  | [], _ => []
  | c :: cs, i => (PlaneTree.contour c).map (List.cons i) ++ [[]] ++ contourForest cs (i + 1)

end

/-- Number of children of the address `u` in `P`. -/
def PlaneTree.childCount (P : PlaneTree) (u : List ℕ) : ℕ :=
  (P.vtxs.filter fun v => v ≠ [] ∧ v.dropLast = u).length

/-- Degree of the vertex at address `u` in `P`: its children, plus its parent unless it is the root. -/
def PlaneTree.degAt (P : PlaneTree) (u : List ℕ) : ℕ :=
  P.childCount u + if u = [] then 0 else 1

/-! ## Typed ordered trees -/

/-- Vertex types: output `o`, input `in`, latent `lat`. -/
inductive VType : Type where
  | out
  | inp
  | lat
  deriving DecidableEq

/-- Cyclic alternation of `o` and `in` along a list (l.2084–2117): no entry is latent, and cyclically
consecutive entries are distinct. -/
def CyclicAlt (s : List VType) : Prop :=
  ∀ j < s.length,
    s.getD j VType.lat ≠ VType.lat ∧
      s.getD j VType.lat ≠ s.getD ((j + 1) % s.length) VType.lat

/-- Typed ordered trees with `k` edges and root type `o` (l.2084–2117). The typing is fixed to `o`
off the vertex set. Every edge joins a latent vertex to an external one, and around every latent vertex
`y` with parent `x` and children `x₁,…,x_m` the cyclic sequence `(x,x₁,…,x_m)` alternates between `o`
and `in`. -/
structure TypedOrdTree (k : ℕ) where
  tree : PlaneTree
  ty : List ℕ → VType
  card_vtx : tree.vtxs.length = k + 1
  off_support : ∀ u, u ∉ tree.vtxs → ty u = VType.out
  root_out : ty [] = VType.out
  edge_joins : ∀ u ∈ tree.vtxs, ∀ v ∈ tree.vtxs, v ≠ [] → v.dropLast = u →
    (ty u = VType.lat ↔ ¬ ty v = VType.lat)
  latent_alt : ∀ u ∈ tree.vtxs, u ≠ [] → ty u = VType.lat →
    CyclicAlt (ty u.dropLast :: (List.range (tree.childCount u)).map fun i => ty (u ++ [i]))

/-- The set `𝒯_{a,b}` of typed ordered trees with `k = 2a+2b+2` edges and root type `o` (l.2084–2117). -/
abbrev TypedTrees (a b : ℕ) : Type := TypedOrdTree (treeK a b)

/-! ## Polygon positions and the class map -/

/-- Contour position of a polygon vertex (0-based indices): the external vertex `e_s` (paper `e_{s+1}`)
sits at position `2(s+1)` mod `2k`, the latent vertex `l_s` (paper `l_{s+1}`) at `2s+1`
(`lem:app-vol-closed-encoding`). -/
def treePos {k : ℕ} : TreeVtx k → ℕ
  | Sum.inl s => (2 * (s.val + 1)) % (2 * k)
  | Sum.inr s => 2 * s.val + 1

open Classical in
/-- The vertex classes of the retained pairings are the fibres of the contour under `e`: for every
retained pairing `p` there is a bijection `ι` from the classes of `p` onto the vertices of the tree
`e p`, sending the class of a polygon vertex `x` to the contour address `c(treePos x)`
(`lem:app-vol-closed-encoding`). -/
def ClassFibreMap (a b : ℕ)
    (e : {p : TreeMatch (treeK a b) × TreeMatch (treeK a b) // treeRetained p} ≃ TypedTrees a b) :
    Prop :=
  ∀ p : {p : TreeMatch (treeK a b) × TreeMatch (treeK a b) // treeRetained p},
    ∃ ι : Quotient (treeSetoid p.1) → List ℕ,
      Function.Injective ι ∧ (∀ V, ι V ∈ (e p).tree.vtxs) ∧
      (∀ u ∈ (e p).tree.vtxs, ∃ V, ι V = u) ∧
      ∀ x : TreeVtx (treeK a b), ι (treeMk p.1 x) = (e p).tree.contour.getD (treePos x) []

/-! ## Closed walks on trees -/

/-- First visit time of a vertex by the walk `W` (least `s` with `W s = x`). -/
def firstVisit {V : Type} (W : ℕ → V) (x : V) : ℕ :=
  sInf {s : ℕ | W s = x}

/-! ### Helpers for `lem_app_vol_closed_contour` (plane-tree contours and first-return splitting) -/

private def inc : List ℕ → List ℕ
  | [] => []
  | a :: u => (a + 1) :: u

private theorem inc_ne_nil {u : List ℕ} (h : u ≠ []) : inc u ≠ [] := by
  cases u with
  | nil => exact absurd rfl h
  | cons a u => simp [inc]

private theorem inc_dropLast (u : List ℕ) : (inc u).dropLast = inc u.dropLast := by
  match u with
  | [] => rfl
  | [a] => rfl
  | a :: b :: u => simp [inc, List.dropLast]

private theorem inc_inj {u v : List ℕ} (h : inc u = inc v) : u = v := by
  match u, v with
  | [], [] => rfl
  | [], b :: v => simp [inc] at h
  | a :: u, [] => simp [inc] at h
  | a :: u, b :: v => simp [inc] at h; obtain ⟨h1, h2⟩ := h; subst h1; subst h2; rfl

private theorem contourForest_succ (cs : List PlaneTree) (i : ℕ) :
    contourForest cs (i + 1) = (contourForest cs i).map inc := by
  induction cs generalizing i with
  | nil => simp [contourForest]
  | cons c cs ih =>
    simp only [contourForest, List.map_append, List.map_map, ih (i+1)]
    congr 1

private theorem vtxsForest_succ (cs : List PlaneTree) (i : ℕ) :
    vtxsForest cs (i + 1) = (vtxsForest cs i).map inc := by
  induction cs generalizing i with
  | nil => simp [vtxsForest]
  | cons c cs ih =>
    simp only [vtxsForest, List.map_append, List.map_map, ih (i+1)]
    congr 1

private theorem vtxsForest_ne_nil {cs : List PlaneTree} {i : ℕ} {u : List ℕ}
    (h : u ∈ vtxsForest cs i) : u ≠ [] := by
  induction cs generalizing i with
  | nil => simp [vtxsForest] at h
  | cons c cs ih =>
    simp only [vtxsForest, List.mem_append, List.mem_map] at h
    rcases h with ⟨w, _, rfl⟩ | h
    · simp
    · exact ih h

private theorem contour_node (cs : List PlaneTree) :
    (PlaneTree.node cs).contour = [] :: contourForest cs 0 := by
  simp [PlaneTree.contour]

private theorem contour_node_cons (P1 : PlaneTree) (cs : List PlaneTree) :
    (PlaneTree.node (P1 :: cs)).contour =
      [] :: (P1.contour.map (List.cons 0) ++ [[]] ++ (contourForest cs 0).map inc) := by
  simp [PlaneTree.contour, contourForest, contourForest_succ]

private theorem vtxs_node (cs : List PlaneTree) :
    (PlaneTree.node cs).vtxs = [] :: vtxsForest cs 0 := by
  simp [PlaneTree.vtxs]

private theorem vtxs_node_cons (P1 : PlaneTree) (cs : List PlaneTree) :
    (PlaneTree.node (P1 :: cs)).vtxs =
      [] :: (P1.vtxs.map (List.cons 0) ++ (vtxsForest cs 0).map inc) := by
  simp [PlaneTree.vtxs, vtxsForest, vtxsForest_succ]

private theorem pos_b (P1 : PlaneTree) (cs : List PlaneTree) (L1 s1 : ℕ)
    (h1 : P1.contour.length = L1 + 1) (hs : s1 ≤ L1) :
    (PlaneTree.node (P1 :: cs)).contour.getD (s1 + 1) [] = 0 :: P1.contour.getD s1 [] := by
  rw [contour_node_cons, List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.append_assoc,
    List.getElem?_append_left (by simpa using by omega), List.getElem?_map,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  simp

private theorem pos_c (P1 : PlaneTree) (cs : List PlaneTree) (L1 L2 q : ℕ)
    (h1 : P1.contour.length = L1 + 1) (h2 : (contourForest cs 0).length = L2) (hq : q ≤ L2) :
    (PlaneTree.node (P1 :: cs)).contour.getD (L1 + 2 + q) [] =
      inc ((PlaneTree.node cs).contour.getD q []) := by
  rw [contour_node_cons, contour_node, List.getD_eq_getElem?_getD]
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · rw [show L1 + 2 + 0 = (L1 + 1) + 1 by omega, List.getElem?_cons_succ, List.append_assoc,
      List.getElem?_append_right (by simpa using by omega)]
    simp [h1, inc]
  · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [show L1 + 2 + (q' + 1) = (L1 + 2 + q') + 1 by omega, List.getElem?_cons_succ,
      List.append_assoc, List.getElem?_append_right (by simpa using by omega)]
    simp only [List.length_map, h1]
    rw [show L1 + 2 + q' - (L1 + 1) = q' + 1 by omega, List.singleton_append,
      List.getElem?_cons_succ, List.getElem?_map, List.getD_cons_succ, List.getD_eq_getElem?_getD]
    cases (contourForest cs 0)[q']? <;> simp [inc]

private theorem pos_d (P1 : PlaneTree) (cs : List PlaneTree) (L1 L2 s : ℕ)
    (h1 : P1.contour.length = L1 + 1) (h2 : (contourForest cs 0).length = L2) (hs : L1 + L2 + 2 < s) :
    (PlaneTree.node (P1 :: cs)).contour.getD s [] = [] := by
  rw [contour_node_cons, List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · simp [h1, h2]; omega

private theorem mem_vtxs_cons {P1 : PlaneTree} {cs : List PlaneTree} {v : List ℕ} :
    v ∈ (PlaneTree.node (P1 :: cs)).vtxs ↔
      v = [] ∨ (∃ w ∈ P1.vtxs, v = 0 :: w) ∨
        (∃ w ∈ (PlaneTree.node cs).vtxs, w ≠ [] ∧ v = inc w) := by
  rw [vtxs_node_cons, vtxs_node]
  simp only [List.mem_cons, List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨w, hw, h⟩ | ⟨w, hw, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨w, hw, h.symm⟩)
    · exact Or.inr (Or.inr ⟨w, Or.inr hw, vtxsForest_ne_nil hw, h.symm⟩)
  · rintro (h | ⟨w, hw, h⟩ | ⟨w, hw | hw, hne, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨w, hw, h.symm⟩)
    · exact absurd hw hne
    · exact Or.inr (Or.inr ⟨w, hw, h.symm⟩)

private theorem mem_cons0 {P1 : PlaneTree} {cs : List PlaneTree} {w : List ℕ} :
    0 :: w ∈ (PlaneTree.node (P1 :: cs)).vtxs ↔ w ∈ P1.vtxs := by
  rw [mem_vtxs_cons]
  constructor
  · rintro (h | ⟨x, hx, h⟩ | ⟨x, hx, hne, h⟩)
    · simp at h
    · simp at h; rw [h]; exact hx
    · exfalso
      match x, hne, h with
      | a :: y, _, h => simp [inc] at h
  · intro h; exact Or.inr (Or.inl ⟨w, h, rfl⟩)

private theorem mem_inc {P1 : PlaneTree} {cs : List PlaneTree} {w : List ℕ} :
    inc w ∈ (PlaneTree.node (P1 :: cs)).vtxs ↔ w ∈ (PlaneTree.node cs).vtxs := by
  rw [mem_vtxs_cons]
  constructor
  · rintro (h | ⟨x, hx, h⟩ | ⟨x, hx, hne, h⟩)
    · have : w = [] := by
        match w, h with
        | [], _ => rfl
      subst this
      rw [vtxs_node]; simp
    · exfalso
      match w, h with
      | [], h => simp [inc] at h
      | a :: y, h => simp [inc] at h
    · have := inc_inj h; subst this; exact hx
  · intro h
    by_cases hw : w = []
    · subst hw; exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨w, h, hw, rfl⟩)

private def PC (a b : List ℕ) : Prop := (b ≠ [] ∧ b.dropLast = a) ∨ (a ≠ [] ∧ a.dropLast = b)

private theorem PC_cons0 {a b : List ℕ} (h : PC a b) : PC (0 :: a) (0 :: b) := by
  rcases h with ⟨hb, h⟩ | ⟨ha, h⟩
  · left; refine ⟨by simp, ?_⟩
    rw [List.dropLast_cons_of_ne_nil hb, h]
  · right; refine ⟨by simp, ?_⟩
    rw [List.dropLast_cons_of_ne_nil ha, h]

private theorem PC_inc {a b : List ℕ} (h : PC a b) : PC (inc a) (inc b) := by
  rcases h with ⟨hb, h⟩ | ⟨ha, h⟩
  · left; exact ⟨inc_ne_nil hb, by rw [inc_dropLast, h]⟩
  · right; exact ⟨inc_ne_nil ha, by rw [inc_dropLast, h]⟩

private def PInv (L : ℕ) (P : PlaneTree) : Prop :=
  P.contour.length = L + 1 ∧
  P.contour.getD L [] = [] ∧
  (∀ s ≤ L, P.contour.getD s [] ∈ P.vtxs) ∧
  (∀ u ∈ P.vtxs, ∃ s ≤ L, P.contour.getD s [] = u) ∧
  (∀ s < L, PC (P.contour.getD s []) (P.contour.getD (s + 1) [])) ∧
  (∀ v ∈ P.vtxs, v ≠ [] →
    ∃ s < L, P.contour.getD s [] = v.dropLast ∧ P.contour.getD (s + 1) [] = v) ∧
  (∀ (u : List ℕ) (i j s : ℕ), u ++ [i] ∈ P.vtxs → u ++ [j] ∈ P.vtxs → i < j →
    P.contour.getD s [] = u ++ [j] → ∃ s' < s, P.contour.getD s' [] = u ++ [i])

private theorem contour_getD_zero (P : PlaneTree) : P.contour.getD 0 [] = [] := by
  cases P with
  | node cs => rw [contour_node]; rfl

private theorem pinv_base : PInv 0 (PlaneTree.node []) := by
  refine ⟨by simp [PlaneTree.contour, contourForest], rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have : s = 0 := by omega
    subst this; simp [PlaneTree.contour, contourForest, PlaneTree.vtxs, vtxsForest]
  · intro u hu
    have : u = [] := by simpa [PlaneTree.vtxs, vtxsForest] using hu
    subst this
    exact ⟨0, le_refl _, contour_getD_zero _⟩
  · intro s hs; omega
  · intro v hv hne
    simp [PlaneTree.vtxs, vtxsForest] at hv; exact absurd hv hne
  · intro u i j s hi hj hij
    simp [PlaneTree.vtxs, vtxsForest] at hi
    
private theorem pinv_combine {P1 : PlaneTree} {cs : List PlaneTree} {L1 L2 : ℕ}
    (h1 : PInv L1 P1) (h2 : PInv L2 (PlaneTree.node cs)) :
    PInv (L1 + L2 + 2) (PlaneTree.node (P1 :: cs)) := by
  obtain ⟨l1, e1, m1, c1, ch1, p1, o1⟩ := h1
  obtain ⟨l2, e2, m2, c2, ch2, p2, o2⟩ := h2
  have hF : (contourForest cs 0).length = L2 := by
    rw [contour_node] at l2; simpa using l2
  have hb : ∀ s1 ≤ L1, (PlaneTree.node (P1 :: cs)).contour.getD (s1 + 1) [] =
      0 :: P1.contour.getD s1 [] := fun s1 hs => pos_b P1 cs L1 s1 l1 hs
  have hc : ∀ q ≤ L2, (PlaneTree.node (P1 :: cs)).contour.getD (L1 + 2 + q) [] =
      inc ((PlaneTree.node cs).contour.getD q []) := fun q hq => pos_c P1 cs L1 L2 q l1 hF hq
  have hd : ∀ s, L1 + L2 + 2 < s → (PlaneTree.node (P1 :: cs)).contour.getD s [] = [] :=
    fun s hs => pos_d P1 cs L1 L2 s l1 hF hs
  have ha := contour_getD_zero (PlaneTree.node (P1 :: cs))
  have hc0 := contour_getD_zero P1
  have hc20 := contour_getD_zero (PlaneTree.node cs)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [contour_node_cons]; simp [l1, hF]; omega
  · have := hc L2 le_rfl
    rw [e2] at this
    rw [show L1 + L2 + 2 = L1 + 2 + L2 by omega, this]; rfl
  · intro s hs
    rcases Nat.eq_zero_or_pos s with rfl | hs0
    · rw [ha, vtxs_node_cons]; simp
    · by_cases hs1 : s ≤ L1 + 1
      · obtain ⟨s1, rfl⟩ : ∃ s1, s = s1 + 1 := ⟨s - 1, by omega⟩
        rw [hb s1 (by omega), mem_cons0]
        exact m1 s1 (by omega)
      · have hq : s = L1 + 2 + (s - (L1 + 2)) := by omega
        rw [hq, hc _ (by omega), mem_inc]
        exact m2 _ (by omega)
  · intro v hv
    rw [mem_vtxs_cons] at hv
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
        exact PC_cons0 (ch1 s1 (by omega))
      · by_cases hs2 : s = L1 + 1
        · subst hs2
          have := hc 0 (by omega)
          rw [hb L1 le_rfl, e1, show L1 + 1 + 1 = L1 + 2 + 0 by omega, this, hc20]
          right; exact ⟨by simp, rfl⟩
        · obtain ⟨q, rfl⟩ : ∃ q, s = L1 + 2 + q := ⟨s - (L1 + 2), by omega⟩
          rw [hc q (by omega), show L1 + 2 + q + 1 = L1 + 2 + (q + 1) by omega,
            hc (q + 1) (by omega)]
          exact PC_inc (ch2 q (by omega))
  · intro v hv hne
    rw [mem_vtxs_cons] at hv
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
      · rw [hc q (by omega), hqa, inc_dropLast]
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
            exact mem_cons0.mp this
          have hj' : u' ++ [j] ∈ P1.vtxs := by
            have : 0 :: (u' ++ [j]) ∈ (PlaneTree.node (P1 :: cs)).vtxs := by simpa using hj
            exact mem_cons0.mp this
          obtain ⟨s', hs', he⟩ := o1 u' i j s1 hi' hj' hij hs
          exact ⟨s' + 1, by omega, by rw [hb s' (by omega), he]; rfl⟩
      · by_cases hs2 : s ≤ L1 + L2 + 2
        · obtain ⟨q, rfl⟩ : ∃ q, s = L1 + 2 + q := ⟨s - (L1 + 2), by omega⟩
          rw [hc q (by omega)] at hs
          have hwv := m2 q (by omega)
          generalize hw : (PlaneTree.node cs).contour.getD q [] = w at hs hwv
          rcases w with _ | ⟨a, y⟩
          · simp [inc] at hs
          · cases u with
            | nil =>
              simp [inc] at hs
              obtain ⟨rfl, rfl⟩ := hs
              rcases Nat.eq_zero_or_pos i with rfl | hi0
              · exact ⟨1, by omega, by rw [hb 0 (by omega), hc0]; rfl⟩
              · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
                have hi' : inc [i'] ∈ (PlaneTree.node (P1 :: cs)).vtxs := by simpa [inc] using hi
                have hi'' := mem_inc.mp hi'
                obtain ⟨q', hq', he⟩ := o2 [] i' a q (by simpa using hi'') (by simpa using hwv)
                  (by omega) (by simpa using hw)
                refine ⟨L1 + 2 + q', by omega, ?_⟩
                rw [hc q' (by omega)]
                rw [he]; rfl
            | cons b u'' =>
              simp [inc] at hs
              obtain ⟨rfl, hs⟩ := hs
              subst hs
              have hi' : inc (a :: (u'' ++ [i])) ∈ (PlaneTree.node (P1 :: cs)).vtxs := by
                simpa [inc] using hi
              have hi'' := mem_inc.mp hi'
              have hj'' : (a :: u'') ++ [j] ∈ (PlaneTree.node cs).vtxs := by
                simpa using hwv
              obtain ⟨q', hq', he⟩ := o2 (a :: u'') i j q (by simpa using hi'') hj'' hij
                (by simpa using hw)
              refine ⟨L1 + 2 + q', by omega, ?_⟩
              rw [hc q' (by omega), he]
              simp [inc]
        · rw [hd s (by omega)] at hs; simp at hs

private theorem reach_of_steps {V : Type} (G : SimpleGraph V) (W : ℕ → V) (a : ℕ) :
    ∀ k : ℕ, (∀ i < k, G.Adj (W (a + i)) (W (a + i + 1))) → G.Reachable (W a) (W (a + k)) := by
  intro k
  induction k with
  | zero => intro _; exact SimpleGraph.Reachable.refl _
  | succ k ih =>
    intro h
    have h1 := ih (fun i hi => h i (by omega))
    exact h1.trans (h k (by omega)).reachable

private theorem sum_split (f : ℕ → ℕ) (L1 L2 : ℕ) :
    ∑ i ∈ Finset.range (L1 + L2 + 2), f i =
      f 0 + ∑ x ∈ Finset.range L1, f (1 + x) + f (L1 + 1) + ∑ x ∈ Finset.range L2, f (L1 + 2 + x) := by
  rw [show L1 + L2 + 2 = 1 + (L1 + (1 + L2)) by omega, Finset.sum_range_add, Finset.sum_range_add,
    Finset.sum_range_add]
  simp only [Finset.sum_range_one, add_zero]
  have e1 : ∀ x, 1 + (L1 + (1 + x)) = L1 + 2 + x := fun x => by omega
  have e2 : 1 + L1 = L1 + 1 := by omega
  simp only [e1, e2]
  simp only [add_assoc]

private theorem bridge_nreach {V : Type} {G : SimpleGraph V} (hG : G.IsAcyclic) {x y : V}
    (hxy : G.Adj x y) : ¬ (G.deleteEdges {s(x, y)}).Reachable x y :=
  SimpleGraph.isBridge_iff.mp ((SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hG) hxy)

private theorem sym2_mem_aux {V : Type} {a b c d : V} (h : s(a, b) = s(c, d)) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := Sym2.eq_iff.mp h

private theorem split_first {V : Type} (G : SimpleGraph V) (hG : G.IsAcyclic) (W : ℕ → V) (L : ℕ)
    (hstep : ∀ i < L, G.Adj (W i) (W (i + 1))) (hcl : W L = W 0) (hL : 0 < L) :
    ∃ t, 2 ≤ t ∧ t ≤ L ∧ W t = W 0 ∧ W (t - 1) = W 1 ∧ (∀ k, 1 ≤ k → k < t → W k ≠ W 0) := by
  classical
  have hbr := bridge_nreach hG (hstep 0 hL)
  have hex : ∃ t, 1 ≤ t ∧ W t = W 0 := ⟨L, hL, hcl⟩
  obtain ⟨ht1, htW⟩ := Nat.find_spec hex
  have hmin : ∀ k, 1 ≤ k → k < Nat.find hex → W k ≠ W 0 := fun k hk hkt hW =>
    Nat.find_min hex hkt ⟨hk, hW⟩
  have htL : Nat.find hex ≤ L := Nat.find_min' hex ⟨hL, hcl⟩
  have ht2 : 2 ≤ Nat.find hex := by
    by_contra hlt
    have : Nat.find hex = 1 := by omega
    rw [this] at htW
    exact (hstep 0 hL).ne htW.symm
  refine ⟨Nat.find hex, ht2, htL, htW, ?_, hmin⟩
  by_contra hne
  set t := Nat.find hex with ht
  have hk : ∀ i, 1 ≤ i → i + 1 < t →
      (G.deleteEdges {s(W 0, W 1)}).Adj (W i) (W (i + 1)) := by
    intro i hi hit
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨hstep i (by omega), ?_⟩
    intro hmem
    rcases sym2_mem_aux (Set.mem_singleton_iff.mp hmem) with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact hmin i hi (by omega) h1
    · exact hmin (i + 1) (by omega) hit h2
  have hr := reach_of_steps (G.deleteEdges {s(W 0, W 1)}) W 1 (t - 2)
    (fun i hi => hk (1 + i) (by omega) (by omega))
  rw [show 1 + (t - 2) = t - 1 by omega] at hr
  have hadj : (G.deleteEdges {s(W 0, W 1)}).Adj (W (t - 1)) (W 0) := by
    rw [SimpleGraph.deleteEdges_adj]
    have hs := hstep (t - 1) (by omega)
    rw [show t - 1 + 1 = t by omega, htW] at hs
    refine ⟨hs, ?_⟩
    intro hmem
    rcases sym2_mem_aux (Set.mem_singleton_iff.mp hmem) with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hmin (t - 1) (by omega) (by omega) h1
    · exact hne h1
  exact hbr (hr.trans hadj.reachable).symm

private theorem split_counts {V : Type} [DecidableEq V] (G : SimpleGraph V) (hG : G.IsAcyclic) (W : ℕ → V)
    (L t : ℕ) (hstep : ∀ i < L, G.Adj (W i) (W (i + 1))) (ht2 : 2 ≤ t) (htL : t ≤ L)
    (htW : W t = W 0) (hcl1 : W (t - 1) = W 1)
    (hcount : ∀ e : Sym2 V, (∑ i ∈ Finset.range L, if s(W i, W (i + 1)) = e then 1 else 0) = 0 ∨
      (∑ i ∈ Finset.range L, if s(W i, W (i + 1)) = e then 1 else 0) = 2) :
    (∀ a b, 1 ≤ a → a < t → t ≤ b → b ≤ L → W a ≠ W b) ∧
    (∀ e : Sym2 V, (∑ x ∈ Finset.range (t - 2), if s(W (1 + x), W (1 + x + 1)) = e then 1 else 0) = 0 ∨
      (∑ x ∈ Finset.range (t - 2), if s(W (1 + x), W (1 + x + 1)) = e then 1 else 0) = 2) ∧
    (∀ e : Sym2 V, (∑ x ∈ Finset.range (L - t), if s(W (t + x), W (t + x + 1)) = e then 1 else 0) = 0 ∨
      (∑ x ∈ Finset.range (L - t), if s(W (t + x), W (t + x + 1)) = e then 1 else 0) = 2) := by
  obtain ⟨L1, hL1⟩ : ∃ L1, L1 = t - 2 := ⟨_, rfl⟩
  obtain ⟨L2, hL2⟩ : ∃ L2, L2 = L - t := ⟨_, rfl⟩
  rw [← hL1, ← hL2]
  have hLe : L = L1 + L2 + 2 := by omega
  have htt : t = L1 + 2 := by omega
  subst htt
  have hbr := bridge_nreach hG (hstep 0 (by omega))
  have hsplit : ∀ e : Sym2 V,
      (∑ i ∈ Finset.range L, if s(W i, W (i + 1)) = e then 1 else 0) =
        (if s(W 0, W 1) = e then 1 else 0) +
        (∑ x ∈ Finset.range L1, if s(W (1 + x), W (1 + x + 1)) = e then 1 else 0) +
        (if s(W (L1 + 1), W (L1 + 1 + 1)) = e then 1 else 0) +
        (∑ x ∈ Finset.range L2, if s(W (L1 + 2 + x), W (L1 + 2 + x + 1)) = e then 1 else 0) := by
    intro e
    rw [hLe]
    exact sum_split (fun i => if s(W i, W (i + 1)) = e then 1 else 0) L1 L2
  have hW1 : W (L1 + 1) = W 1 := by
    have := hcl1; rwa [show L1 + 2 - 1 = L1 + 1 by omega] at this
  have hW2 : W (L1 + 1 + 1) = W 0 := htW
  have hmid : s(W (L1 + 1), W (L1 + 1 + 1)) = s(W 0, W 1) := by
    rw [hW1, hW2, Sym2.eq_swap]
  -- the edge e0 is used exactly by the two bracketing steps
  have hA0B0 : (∑ x ∈ Finset.range L1,
        if s(W (1 + x), W (1 + x + 1)) = s(W 0, W 1) then 1 else 0) = 0 ∧
      (∑ x ∈ Finset.range L2,
        if s(W (L1 + 2 + x), W (L1 + 2 + x + 1)) = s(W 0, W 1) then 1 else 0) = 0 := by
    have h := hsplit (s(W 0, W 1))
    rw [hmid] at h
    simp only [if_true] at h
    rcases hcount (s(W 0, W 1)) with h0 | h0 <;> omega
  have hB0 : ∀ y < L2, s(W (L1 + 2 + y), W (L1 + 2 + y + 1)) ≠ s(W 0, W 1) := by
    intro y hy heq
    have := (Finset.sum_eq_zero_iff.mp hA0B0.2) y (Finset.mem_range.mpr hy)
    simp [heq] at this
  have hA0 : ∀ x < L1, s(W (1 + x), W (1 + x + 1)) ≠ s(W 0, W 1) := by
    intro x hx heq
    have := (Finset.sum_eq_zero_iff.mp hA0B0.1) x (Finset.mem_range.mpr hx)
    simp [heq] at this
  have hV : ∀ a b, 1 ≤ a → a < L1 + 2 → L1 + 2 ≤ b → b ≤ L → W a ≠ W b := by
    intro a b ha hat hb hbL hab
    have hr1 := reach_of_steps (G.deleteEdges {s(W 0, W 1)}) W 1 (a - 1) (by
      intro i hi
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨hstep (1 + i) (by omega), ?_⟩
      intro hmem
      exact hA0 i (by omega) (Set.mem_singleton_iff.mp hmem))
    rw [show 1 + (a - 1) = a by omega] at hr1
    have hr2 := reach_of_steps (G.deleteEdges {s(W 0, W 1)}) W (L1 + 2) (b - (L1 + 2)) (by
      intro i hi
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨hstep (L1 + 2 + i) (by omega), ?_⟩
      intro hmem
      exact hB0 i (by omega) (Set.mem_singleton_iff.mp hmem))
    rw [show L1 + 2 + (b - (L1 + 2)) = b by omega, htW] at hr2
    exact hbr (hr2.trans (hab ▸ hr1.symm))
  have hfin : ∀ e : Sym2 V, e ≠ s(W 0, W 1) →
      ((∑ x ∈ Finset.range L1, if s(W (1 + x), W (1 + x + 1)) = e then 1 else 0) = 0 ∨
        (∑ x ∈ Finset.range L1, if s(W (1 + x), W (1 + x + 1)) = e then 1 else 0) = 2) ∧
      ((∑ x ∈ Finset.range L2,
          if s(W (L1 + 2 + x), W (L1 + 2 + x + 1)) = e then 1 else 0) = 0 ∨
        (∑ x ∈ Finset.range L2,
          if s(W (L1 + 2 + x), W (L1 + 2 + x + 1)) = e then 1 else 0) = 2) := by
    intro e he
    have h := hsplit e
    have hf0 : (if s(W 0, W 1) = e then 1 else 0) = 0 := by
      rw [if_neg]; exact fun h => he h.symm
    have hf1 : (if s(W (L1 + 1), W (L1 + 1 + 1)) = e then 1 else 0) = 0 := by
      rw [if_neg]; rw [hmid]; exact fun h => he h.symm
    rw [hf0, hf1] at h
    have hdis : (∑ x ∈ Finset.range L1, if s(W (1 + x), W (1 + x + 1)) = e then 1 else 0) ≠ 0 →
        (∑ x ∈ Finset.range L2,
          if s(W (L1 + 2 + x), W (L1 + 2 + x + 1)) = e then 1 else 0) = 0 := by
      intro hA
      by_contra hB
      obtain ⟨x, hx, hxne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hA
      obtain ⟨y, hy, hyne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hB
      have hx' : s(W (1 + x), W (1 + x + 1)) = e := by
        by_contra hc; rw [if_neg hc] at hxne; exact hxne rfl
      have hy' : s(W (L1 + 2 + y), W (L1 + 2 + y + 1)) = e := by
        by_contra hc; rw [if_neg hc] at hyne; exact hyne rfl
      have hxm := Finset.mem_range.mp hx
      have hym := Finset.mem_range.mp hy
      rw [← hx'] at hy'
      rcases sym2_mem_aux hy' with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hV (1 + x) (L1 + 2 + y) (by omega) (by omega) (by omega) (by omega) h1.symm
      · exact hV (1 + x) (L1 + 2 + y + 1) (by omega) (by omega) (by omega) (by omega) h2.symm
    rcases hcount e with h0 | h0 <;> omega
  refine ⟨hV, fun e => ?_, fun e => ?_⟩
  · by_cases he : e = s(W 0, W 1)
    · subst he; left; exact hA0B0.1
    · exact (hfin e he).1
  · by_cases he : e = s(W 0, W 1)
    · subst he; left; exact hA0B0.2
    · exact (hfin e he).2

private theorem core {V : Type} [DecidableEq V] (G : SimpleGraph V) (hG : G.IsAcyclic) :
    ∀ (L : ℕ) (W : ℕ → V), (∀ i < L, G.Adj (W i) (W (i + 1))) → W L = W 0 →
      (∀ e : Sym2 V, (∑ i ∈ Finset.range L, if s(W i, W (i + 1)) = e then 1 else 0) = 0 ∨
        (∑ i ∈ Finset.range L, if s(W i, W (i + 1)) = e then 1 else 0) = 2) →
      ∃ (P : PlaneTree) (ψ : List ℕ → V), PInv L P ∧
        (∀ u ∈ P.vtxs, ∀ v ∈ P.vtxs, ψ u = ψ v → u = v) ∧ ψ [] = W 0 ∧
        ∀ s ≤ L, W s = ψ (P.contour.getD s []) := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  intro W hstep hcl hcount
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · refine ⟨PlaneTree.node [], fun _ => W 0, pinv_base, ?_, rfl, ?_⟩
    · intro u hu v hv _
      simp [PlaneTree.vtxs, vtxsForest] at hu hv; rw [hu, hv]
    · intro s hs
      have : s = 0 := by omega
      subst this; rfl
  · obtain ⟨t, ht2, htL, htW, hcl1, hmin⟩ := split_first G hG W L hstep hcl hL
    obtain ⟨hV, hc1, hc2⟩ := split_counts G hG W L t hstep ht2 htL htW hcl1 hcount
    obtain ⟨L1, hL1⟩ : ∃ L1, L1 = t - 2 := ⟨_, rfl⟩
    obtain ⟨L2, hL2⟩ : ∃ L2, L2 = L - t := ⟨_, rfl⟩
    have hLe : L = L1 + L2 + 2 := by omega
    have htt : t = L1 + 2 := by omega
    rw [← hL1] at hc1
    rw [← hL2] at hc2
    obtain ⟨P1, ψ1, hI1, hinj1, hψ1, hW1⟩ := ih L1 (by omega) (fun i => W (1 + i))
      (fun i hi => hstep (1 + i) (by omega))
      (by
        show W (1 + L1) = W (1 + 0)
        rw [show 1 + L1 = t - 1 by omega]; simpa using hcl1)
      (fun e => hc1 e)
    obtain ⟨P2, ψ2, hI2, hinj2, hψ2, hW2⟩ := ih L2 (by omega) (fun i => W (t + i))
      (fun i hi => hstep (t + i) (by omega))
      (by
        show W (t + L2) = W (t + 0)
        rw [show t + L2 = L by omega]; simpa using hcl.trans htW.symm)
      (fun e => hc2 e)
    cases P2 with
    | node cs =>
    obtain ⟨ψ, hψnil, hψ0, hψs⟩ : ∃ ψ : List ℕ → V, ψ [] = W 0 ∧ (∀ w, ψ (0 :: w) = ψ1 w) ∧
        (∀ a w, ψ ((a + 1) :: w) = ψ2 (a :: w)) :=
      ⟨fun u => match u with
        | [] => W 0
        | 0 :: u' => ψ1 u'
        | (a + 1) :: u' => ψ2 (a :: u'), rfl, fun _ => rfl, fun _ _ => rfl⟩
    have hψ2nil : ψ2 [] = W 0 := by
      have : ψ2 [] = W (t + 0) := hψ2
      rw [this]; simpa using htW
    have hψinc : ∀ w, ψ (inc w) = ψ2 w := by
      intro w
      cases w with
      | nil => rw [show inc [] = [] from rfl, hψnil, hψ2nil]
      | cons a w => exact hψs a w
    have hS1 : ∀ w ∈ P1.vtxs, ∃ k, 1 ≤ k ∧ k < t ∧ ψ1 w = W k := by
      intro w hw
      obtain ⟨s, hs, hse⟩ := hI1.2.2.2.1 w hw
      refine ⟨1 + s, by omega, by omega, ?_⟩
      have := hW1 s hs
      rw [hse] at this
      exact this.symm
    have hS2 : ∀ w ∈ (PlaneTree.node cs).vtxs, ∃ k, t ≤ k ∧ k ≤ L ∧ ψ2 w = W k := by
      intro w hw
      obtain ⟨s, hs, hse⟩ := hI2.2.2.2.1 w hw
      refine ⟨t + s, by omega, by omega, ?_⟩
      have := hW2 s hs
      rw [hse] at this
      exact this.symm
    have hnil2 : ([] : List ℕ) ∈ (PlaneTree.node cs).vtxs := by rw [vtxs_node]; simp
    refine ⟨PlaneTree.node (P1 :: cs), ψ, ?_, ?_, hψnil, ?_⟩
    · have := pinv_combine hI1 hI2
      rw [hLe]; exact this
    · intro u hu v hv huv
      rw [mem_vtxs_cons] at hu hv
      rcases hu with rfl | ⟨w, hw, rfl⟩ | ⟨w, hw, hwne, rfl⟩ <;>
        rcases hv with rfl | ⟨w', hw', rfl⟩ | ⟨w', hw', hwne', rfl⟩
      · rfl
      · rw [hψnil, hψ0] at huv
        obtain ⟨k, hk1, hk2, hk⟩ := hS1 w' hw'
        exact absurd (huv.trans hk).symm (hmin k hk1 hk2)
      · rw [hψnil, hψinc] at huv
        have := hinj2 [] hnil2 w' hw' (hψ2nil.trans huv)
        exact absurd this.symm hwne'
      · rw [hψnil, hψ0] at huv
        obtain ⟨k, hk1, hk2, hk⟩ := hS1 w hw
        exact absurd (huv.symm.trans hk).symm (hmin k hk1 hk2)
      · rw [hψ0, hψ0] at huv
        rw [hinj1 w hw w' hw' huv]
      · rw [hψ0, hψinc] at huv
        obtain ⟨k, hk1, hk2, hk⟩ := hS1 w hw
        obtain ⟨k', hk1', hk2', hk'⟩ := hS2 w' hw'
        exact absurd (hk.symm.trans (huv.trans hk')) (hV k k' hk1 hk2 hk1' hk2')
      · rw [hψnil, hψinc] at huv
        have := hinj2 w hw [] hnil2 (by rw [hψ2nil]; exact huv)
        exact absurd this hwne
      · rw [hψ0, hψinc] at huv
        obtain ⟨k, hk1, hk2, hk⟩ := hS1 w' hw'
        obtain ⟨k', hk1', hk2', hk'⟩ := hS2 w hw
        exact absurd (hk.symm.trans (huv.symm.trans hk')) (hV k k' hk1 hk2 hk1' hk2')
      · rw [hψinc, hψinc] at huv
        rw [hinj2 w hw w' hw' huv]
    · intro s hs
      have hl1 := hI1.1
      have hl2 := hI2.1
      have hF : (contourForest cs 0).length = L2 := by
        rw [contour_node] at hl2; simpa using hl2
      rcases Nat.eq_zero_or_pos s with rfl | hs0
      · rw [contour_getD_zero, hψnil]
      · by_cases hs1 : s ≤ L1 + 1
        · obtain ⟨s1, rfl⟩ : ∃ s1, s = s1 + 1 := ⟨s - 1, by omega⟩
          rw [pos_b P1 cs L1 s1 hl1 (by omega), hψ0]
          have := hW1 s1 (by omega)
          rw [show s1 + 1 = 1 + s1 by omega]
          exact this
        · obtain ⟨q, rfl⟩ : ∃ q, s = L1 + 2 + q := ⟨s - (L1 + 2), by omega⟩
          rw [pos_c P1 cs L1 L2 q hl1 hF (by omega), hψinc]
          have := hW2 q (by omega)
          rw [show L1 + 2 + q = t + q by omega]
          exact this

/-- `lem:app-vol-closed-contour`, snapshot `cr-2026-10-23`. Declaration of record. The walk `W` is
`W_0,…,W_{2n}` on the vertices of the finite tree `T` with `n = Nat.card T.edgeSet` edges; the conclusion
says that `W` is the contour of the ordered tree obtained by rooting `T` at `W_0` and ordering the
children of each vertex by first visit: there are a plane tree `P` and an identification `ψ` of its
vertices with those of `T` (a bijection, root to `W_0`, parent-child pairs to edges) such that the
children of each vertex are ordered by first visit and `W` is `ψ` applied to the contour of `P`.
Verbatim LaTeX of the lemma statement:
```latex
\begin{lemma}[Closed walks on trees]\label{lem:app-vol-closed-contour}
Let $T$ be a finite tree with $n$ edges and $W=(W_0,\dots,W_{2n})$ a closed walk
in $T$ that traverses every edge exactly twice. Root $T$ at $W_0$ and order the
children of every vertex by the time of their first visit. Then $W$ is the
contour of this ordered tree.
\end{lemma}
```
-/
theorem lem_app_vol_closed_contour {V : Type} [Finite V] [DecidableEq V] (T : SimpleGraph V)
    (hT : T.IsTree) (n : ℕ) (hn : Nat.card T.edgeSet = n) (W : ℕ → V)
    (hstep : ∀ i < 2 * n, T.Adj (W i) (W (i + 1)))
    (hclosed : W (2 * n) = W 0)
    (htwice : ∀ e ∈ T.edgeSet,
      ((Finset.range (2 * n)).filter fun i => s(W i, W (i + 1)) = e).card = 2) :
    ∃ (P : PlaneTree) (ψ : List ℕ → V),
      (∀ u ∈ P.vtxs, ∀ v ∈ P.vtxs, ψ u = ψ v → u = v) ∧
      (∀ x : V, ∃ u ∈ P.vtxs, ψ u = x) ∧
      ψ [] = W 0 ∧
      (∀ u ∈ P.vtxs, ∀ v ∈ P.vtxs,
        T.Adj (ψ u) (ψ v) ↔ ((v ≠ [] ∧ v.dropLast = u) ∨ (u ≠ [] ∧ u.dropLast = v))) ∧
      (∀ u i j, u ++ [i] ∈ P.vtxs → u ++ [j] ∈ P.vtxs → i < j →
        firstVisit W (ψ (u ++ [i])) < firstVisit W (ψ (u ++ [j]))) ∧
      (∀ i ≤ 2 * n, W i = ψ (P.contour.getD i [])) := by
  have hstepEx : ∀ e ∈ T.edgeSet, ∃ j < 2 * n, s(W j, W (j + 1)) = e := by
    intro e he
    have h2 := htwice e he
    have hpos : 0 < ((Finset.range (2 * n)).filter fun i => s(W i, W (i + 1)) = e).card := by
      omega
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter, Finset.mem_range] at hj
    exact ⟨j, hj.1, hj.2⟩
  have hcount : ∀ e : Sym2 V,
      (∑ i ∈ Finset.range (2 * n), if s(W i, W (i + 1)) = e then 1 else 0) = 0 ∨
      (∑ i ∈ Finset.range (2 * n), if s(W i, W (i + 1)) = e then 1 else 0) = 2 := by
    intro e
    rw [← Finset.card_filter]
    by_cases he : e ∈ T.edgeSet
    · right; exact htwice e he
    · left
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i hi heq
      apply he
      rw [← heq]
      exact (SimpleGraph.mem_edgeSet T).mpr (hstep i (Finset.mem_range.mp hi))
  obtain ⟨P, ψ, hI, hinj, hψ0, hWc⟩ := core T hT.isAcyclic (2 * n) W hstep hclosed hcount
  obtain ⟨hlen, hlast, hmem, hcov, hch, hpar, hord⟩ := hI
  refine ⟨P, ψ, hinj, ?_, hψ0, ?_, ?_, hWc⟩
  · -- surjectivity
    have hreach : ∀ (u v : V) (p : T.Walk u v), (∃ i ≤ 2 * n, W i = u) → ∃ i ≤ 2 * n, W i = v := by
      intro u v p
      induction p with
      | nil => exact id
      | cons h p ih =>
        rename_i a b c
        intro ⟨i, hi, hWi⟩
        apply ih
        obtain ⟨j, hj, hje⟩ := hstepEx s(a, b) ((SimpleGraph.mem_edgeSet T).mpr h)
        rcases sym2_mem_aux hje with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact ⟨j + 1, by omega, h2⟩
        · exact ⟨j, by omega, by assumption⟩
    intro x
    obtain ⟨p⟩ := hT.1.preconnected (W 0) x
    obtain ⟨i, hi, hWi⟩ := hreach _ _ p ⟨0, Nat.zero_le _, rfl⟩
    exact ⟨_, hmem i hi, by rw [← hWc i hi, hWi]⟩
  · -- adjacency
    intro u hu v hv
    constructor
    · intro h
      obtain ⟨j, hj, hje⟩ := hstepEx s(ψ u, ψ v) ((SimpleGraph.mem_edgeSet T).mpr h)
      have hj1 := hmem j (by omega)
      have hj2 := hmem (j + 1) (by omega)
      have e1 := hWc j (by omega)
      have e2 := hWc (j + 1) (by omega)
      have hc := hch j hj
      rcases sym2_mem_aux hje with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have a1 := hinj _ hj1 u hu (by rw [← e1]; exact h1)
        have a2 := hinj _ hj2 v hv (by rw [← e2]; exact h2)
        rw [a1, a2] at hc
        exact hc
      · have a1 := hinj _ hj1 v hv (by rw [← e1]; exact h1)
        have a2 := hinj _ hj2 u hu (by rw [← e2]; exact h2)
        rw [a1, a2] at hc
        exact hc.symm
    · rintro (⟨hne, hdl⟩ | ⟨hne, hdl⟩)
      · obtain ⟨s, hs, h1, h2⟩ := hpar v hv hne
        have := hstep s (by omega)
        rw [hWc s (by omega), hWc (s + 1) (by omega), h1, h2, hdl] at this
        exact this
      · obtain ⟨s, hs, h1, h2⟩ := hpar u hu hne
        have := hstep s (by omega)
        rw [hWc s (by omega), hWc (s + 1) (by omega), h1, h2, hdl] at this
        exact this.symm
  · -- first-visit order
    intro u i j hi hj hij
    obtain ⟨a, ha, hae⟩ := hcov _ hj
    have hne : ({s : ℕ | W s = ψ (u ++ [j])}).Nonempty := ⟨a, by show W a = _; rw [hWc a ha, hae]⟩
    have hmemfv := Nat.sInf_mem hne
    have hle : sInf {s : ℕ | W s = ψ (u ++ [j])} ≤ a := Nat.sInf_le (by
      show W a = _
      rw [hWc a ha, hae])
    set sj := sInf {s : ℕ | W s = ψ (u ++ [j])} with hsj
    have hsj2 : sj ≤ 2 * n := by omega
    have hcj : P.contour.getD sj [] = u ++ [j] :=
      hinj _ (hmem sj hsj2) _ hj (by rw [← hWc sj hsj2]; exact hmemfv)
    obtain ⟨s', hs', hse⟩ := hord u i j sj hi hj hij hcj
    have : firstVisit W (ψ (u ++ [i])) ≤ s' := Nat.sInf_le (by
      show W s' = _
      rw [hWc s' (by omega), hse])
    show firstVisit W (ψ (u ++ [i])) < sj
    omega

/-! ## Plane-tree structure lemmas for the encoding (helpers of `lem_app_vol_closed_encoding_i`) -/

private theorem pt_vtxs_pos (P : PlaneTree) : 1 ≤ P.vtxs.length := by
  cases P with
  | node cs => rw [vtxs_node]; simp

private theorem pt_vtxs_len (P1 : PlaneTree) (cs : List PlaneTree) :
    (PlaneTree.node (P1 :: cs)).vtxs.length = P1.vtxs.length + (PlaneTree.node cs).vtxs.length := by
  have h1 : P1.vtxs.length = 1 + (match P1 with | .node c => (vtxsForest c 0).length) := by
    cases P1 with
    | node c => rw [vtxs_node]; simp; omega
  rw [vtxs_node_cons, vtxs_node]
  simp only [List.length_cons, List.length_append, List.length_map]
  rw [h1]
  cases P1 with
  | node c => simp only [vtxs_node, List.length_cons]; omega

private theorem plane_ind (M : PlaneTree → Prop) (h0 : M (.node []))
    (h1 : ∀ P1 cs, M P1 → M (.node cs) → M (.node (P1 :: cs))) : ∀ P, M P := by
  intro P
  induction hn : P.vtxs.length using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    cases P with
    | node cs =>
      cases cs with
      | nil => exact h0
      | cons P1 cs =>
        rw [pt_vtxs_len] at hn
        have a1 := pt_vtxs_pos P1
        have a2 := pt_vtxs_pos (PlaneTree.node cs)
        exact h1 P1 cs (ih _ (by omega) P1 rfl) (ih _ (by omega) (PlaneTree.node cs) rfl)

private theorem pt_pinv (P : PlaneTree) : PInv (P.contour.length - 1) P := by
  have : ∃ L, PInv L P := by
    refine plane_ind (fun P => ∃ L, PInv L P) ⟨0, pinv_base⟩ ?_ P
    intro P1 cs ⟨L1, h1⟩ ⟨L2, h2⟩
    exact ⟨_, pinv_combine h1 h2⟩
  obtain ⟨L, hL⟩ := this
  have := hL.1
  rw [this]; simpa using hL

private theorem pt_nodup (P : PlaneTree) : P.vtxs.Nodup := by
  refine plane_ind (fun P => P.vtxs.Nodup) (by simp [PlaneTree.vtxs, vtxsForest]) ?_ P
  intro P1 cs h1 h2
  rw [vtxs_node] at h2
  rw [vtxs_node_cons]
  have h2' := List.nodup_cons.mp h2
  refine List.nodup_cons.mpr ⟨?_, ?_⟩
  · simp only [List.mem_append, List.mem_map, not_or]
    refine ⟨?_, ?_⟩
    · rintro ⟨w, _, hw⟩; simp at hw
    · rintro ⟨w, hw, hw'⟩
      exact inc_ne_nil (vtxsForest_ne_nil hw) hw'
  · rw [List.nodup_append]
    refine ⟨h1.map (fun a b h => by simpa using h), h2'.2.map (fun a b h => inc_inj h), ?_⟩
    intro x hx y hy hxy
    simp only [List.mem_map] at hx hy
    obtain ⟨w, _, rfl⟩ := hx
    obtain ⟨w', hw', rfl⟩ := hy
    have hne := vtxsForest_ne_nil hw'
    match w', hne with
    | a :: u, _ => simp [inc] at hxy

private theorem pt_contour_len (P : PlaneTree) : P.contour.length + 1 = 2 * P.vtxs.length := by
  refine plane_ind (fun P => P.contour.length + 1 = 2 * P.vtxs.length)
    (by simp [PlaneTree.contour, contourForest, PlaneTree.vtxs, vtxsForest]) ?_ P
  intro P1 cs h1 h2
  rw [pt_vtxs_len, contour_node_cons]
  rw [contour_node] at h2
  simp only [List.length_cons, List.length_append, List.length_map, List.length_singleton, List.length_nil] at h1 h2 ⊢
  omega

private theorem pt_mem_idx (cs : List PlaneTree) (a : ℕ) (w : List ℕ) :
    (a :: w) ∈ (PlaneTree.node cs).vtxs ↔ ∃ h : a < cs.length, w ∈ (cs[a]).vtxs := by
  induction cs generalizing a with
  | nil => simp [vtxs_node, vtxsForest]
  | cons P1 cs ih =>
    cases a with
    | zero => rw [mem_cons0]; simp
    | succ a =>
      have : (a + 1) :: w = inc (a :: w) := rfl
      rw [this, mem_inc, ih]
      simp

private theorem pt_root_mem (P : PlaneTree) : ([] : List ℕ) ∈ P.vtxs := by
  cases P with
  | node cs => rw [vtxs_node]; simp

private theorem pt_parent_mem (u : List ℕ) : ∀ (P : PlaneTree) (i : ℕ),
    u ++ [i] ∈ P.vtxs → u ∈ P.vtxs := by
  induction u with
  | nil => intro P i _; exact pt_root_mem P
  | cons a u ih =>
    intro P i h
    cases P with
    | node cs =>
      rw [List.cons_append, pt_mem_idx] at h
      obtain ⟨hl, hm⟩ := h
      rw [pt_mem_idx]
      exact ⟨hl, ih _ i hm⟩

private theorem pt_prefix_closed (u : List ℕ) : ∀ (P : PlaneTree) (i j : ℕ), i < j →
    u ++ [j] ∈ P.vtxs → u ++ [i] ∈ P.vtxs := by
  induction u with
  | nil =>
    intro P i j hij h
    cases P with
    | node cs =>
      rw [List.nil_append, pt_mem_idx] at h
      obtain ⟨hl, hm⟩ := h
      rw [List.nil_append, pt_mem_idx]
      exact ⟨by omega, pt_root_mem _⟩
  | cons a u ih =>
    intro P i j hij h
    cases P with
    | node cs =>
      rw [List.cons_append, pt_mem_idx] at h
      obtain ⟨hl, hm⟩ := h
      rw [List.cons_append, pt_mem_idx]
      exact ⟨hl, ih _ i j hij hm⟩

private theorem downclosed_iff (l : List ℕ) (hl : l.Nodup) (hd : ∀ i ∈ l, ∀ j < i, j ∈ l) (i : ℕ) :
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

private theorem pt_childCount_iff (P : PlaneTree) (u : List ℕ) (i : ℕ) :
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
    refine List.Nodup.map_on ?_ ((pt_nodup P).filter _)
    intro x hx y hy hxy
    obtain ⟨i, rfl, _⟩ := (hFmem x).mp hx
    obtain ⟨j, rfl, _⟩ := (hFmem y).mp hy
    simp at hxy
    rw [hxy]
  have hdc : ∀ i ∈ l, ∀ j < i, j ∈ l := by
    intro i hi j hj
    rw [hlmem] at hi ⊢
    exact pt_prefix_closed u P j i hj hi
  have hlen : l.length = P.childCount u := by rw [hl, List.length_map]; rfl
  constructor
  · intro h
    refine ⟨pt_parent_mem u P i h, ?_⟩
    rw [← hlen, ← downclosed_iff l hnd hdc]
    exact (hlmem i).mpr h
  · rintro ⟨_, h⟩
    rw [← hlmem, downclosed_iff l hnd hdc, hlen]
    exact h

private theorem nat_eq_of_lt_iff {a b : ℕ} (h : ∀ i, i < a ↔ i < b) : a = b := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h3 | h3
  · have := (h a).mpr h3
    omega
  · have := (h b).mp h3
    omega

private theorem pt_cc_nil (cs : List PlaneTree) : (PlaneTree.node cs).childCount [] = cs.length := by
  apply nat_eq_of_lt_iff
  intro i
  have h1 := pt_childCount_iff (PlaneTree.node cs) [] i
  rw [List.nil_append, pt_mem_idx] at h1
  constructor
  · intro hi
    have := h1.mpr ⟨pt_root_mem _, hi⟩
    obtain ⟨h, _⟩ := this
    exact h
  · intro hi
    exact (h1.mp ⟨hi, pt_root_mem _⟩).2

private theorem pt_cc_idx (cs : List PlaneTree) (a : ℕ) (h : a < cs.length) (u : List ℕ)
    (hu : u ∈ (cs[a]).vtxs) : (PlaneTree.node cs).childCount (a :: u) = (cs[a]).childCount u := by
  apply nat_eq_of_lt_iff
  intro i
  have h1 := pt_childCount_iff (PlaneTree.node cs) (a :: u) i
  have h2 := pt_childCount_iff (cs[a]) u i
  rw [List.cons_append, pt_mem_idx] at h1
  have hmem : a :: u ∈ (PlaneTree.node cs).vtxs := (pt_mem_idx cs a u).mpr ⟨h, hu⟩
  constructor
  · intro hi
    exact (h2.mp (h1.mpr ⟨hmem, hi⟩).choose_spec).2
  · intro hi
    exact (h1.mp (by exact ⟨h, h2.mpr ⟨hu, hi⟩⟩)).2

private def cpre (u : List ℕ) (j : ℕ) : List ℕ := if j = 0 then u.dropLast else u ++ [j - 1]

private def cpost (u : List ℕ) (m j : ℕ) : List ℕ := if j = m then u.dropLast else u ++ [j]

private theorem cpre_zero (u : List ℕ) : cpre u 0 = u.dropLast := by simp [cpre]

private theorem cpre_succ (u : List ℕ) (j : ℕ) : cpre u (j + 1) = u ++ [j] := by simp [cpre]

private theorem cpost_self (u : List ℕ) (m : ℕ) : cpost u m m = u.dropLast := by simp [cpost]

private theorem cpost_ne (u : List ℕ) {m j : ℕ} (h : j ≠ m) : cpost u m j = u ++ [j] := by
  simp [cpost, h]

private theorem cpre_cons0 {w : List ℕ} (hw : w ≠ []) (j : ℕ) : cpre (0 :: w) j = 0 :: cpre w j := by
  unfold cpre
  split_ifs
  · exact List.dropLast_cons_of_ne_nil hw
  · rfl

private theorem cpost_cons0 {w : List ℕ} (hw : w ≠ []) (m j : ℕ) :
    cpost (0 :: w) m j = 0 :: cpost w m j := by
  unfold cpost
  split_ifs
  · exact List.dropLast_cons_of_ne_nil hw
  · rfl

private theorem inc_append_single {w : List ℕ} (hw : w ≠ []) (j : ℕ) :
    inc (w ++ [j]) = inc w ++ [j] := by
  match w, hw with
  | a :: w, _ => rfl

private theorem cpre_inc {w : List ℕ} (hw : w ≠ []) (j : ℕ) : cpre (inc w) j = inc (cpre w j) := by
  unfold cpre
  split_ifs
  · exact inc_dropLast w
  · exact (inc_append_single hw _).symm

private theorem cpost_inc {w : List ℕ} (hw : w ≠ []) (m j : ℕ) :
    cpost (inc w) m j = inc (cpost w m j) := by
  unfold cpost
  split_ifs
  · exact inc_dropLast w
  · exact (inc_append_single hw _).symm

private def CI (L : ℕ) (P : PlaneTree) : Prop :=
  (1 ≤ P.childCount [] → P.contour.getD 1 [] = [0]) ∧
  (1 ≤ P.childCount [] → P.contour.getD (L - 1) [] = [P.childCount [] - 1]) ∧
  (P.childCount [] = 0 → L = 0) ∧
  (∀ s, 1 ≤ s → s + 1 ≤ L → ∃ j ≤ P.childCount (P.contour.getD s []),
    (P.contour.getD s [] = [] → 0 < j ∧ j < P.childCount []) ∧
    P.contour.getD (s - 1) [] = cpre (P.contour.getD s []) j ∧
    P.contour.getD (s + 1) [] = cpost (P.contour.getD s []) (P.childCount (P.contour.getD s [])) j) ∧
  (∀ u ∈ P.vtxs, ∀ j ≤ P.childCount u, (u = [] → 0 < j ∧ j < P.childCount []) →
    ∃ s, 1 ≤ s ∧ s + 1 ≤ L ∧ P.contour.getD s [] = u ∧
      P.contour.getD (s - 1) [] = cpre u j ∧
      P.contour.getD (s + 1) [] = cpost u (P.childCount u) j)

private theorem ci_base : CI 0 (PlaneTree.node []) := by
  have hcc : (PlaneTree.node []).childCount [] = 0 := by rw [pt_cc_nil]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; omega
  · intro h; omega
  · intro _; rfl
  · intro s h1 h2; omega
  · intro u hu j hj hr
    have : u = [] := by simpa [PlaneTree.vtxs, vtxsForest] using hu
    have := hr this
    omega

private theorem getD_lt_of_ne (C : List (List ℕ)) (s : ℕ) (h : C.getD s [] ≠ []) : s < C.length := by
  by_contra hh
  apply h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

private theorem ci_combine {P1 : PlaneTree} {cs : List PlaneTree} {L1 L2 : ℕ}
    (h1 : PInv L1 P1) (h2 : PInv L2 (PlaneTree.node cs))
    (k1 : CI L1 P1) (k2 : CI L2 (PlaneTree.node cs)) :
    CI (L1 + L2 + 2) (PlaneTree.node (P1 :: cs)) := by
  obtain ⟨l1, e1, m1, c1, ch1, p1, o1⟩ := h1
  obtain ⟨l2, e2, m2, c2, ch2, p2, o2⟩ := h2
  obtain ⟨r1a, r1b, r1c, bw1, fw1⟩ := k1
  obtain ⟨r2a, r2b, r2c, bw2, fw2⟩ := k2
  have hF : (contourForest cs 0).length = L2 := by
    rw [contour_node] at l2; simpa using l2
  have hb : ∀ s1 ≤ L1, (PlaneTree.node (P1 :: cs)).contour.getD (s1 + 1) [] =
      0 :: P1.contour.getD s1 [] := fun s1 hs => pos_b P1 cs L1 s1 l1 hs
  have hc : ∀ q ≤ L2, (PlaneTree.node (P1 :: cs)).contour.getD (L1 + 2 + q) [] =
      inc ((PlaneTree.node cs).contour.getD q []) := fun q hq => pos_c P1 cs L1 L2 q l1 hF hq
  have hd : ∀ s, L1 + L2 + 2 < s → (PlaneTree.node (P1 :: cs)).contour.getD s [] = [] :=
    fun s hs => pos_d P1 cs L1 L2 s l1 hF hs
  have ha := contour_getD_zero (PlaneTree.node (P1 :: cs))
  have hc0 := contour_getD_zero P1
  have hc20 := contour_getD_zero (PlaneTree.node cs)
  have hm : (PlaneTree.node (P1 :: cs)).childCount [] = cs.length + 1 := by
    rw [pt_cc_nil]; rfl
  have hm2 : (PlaneTree.node cs).childCount [] = cs.length := pt_cc_nil cs
  rw [hm2] at r2a r2b r2c bw2 fw2
  have hcc0 : ∀ w ∈ P1.vtxs, (PlaneTree.node (P1 :: cs)).childCount (0 :: w) = P1.childCount w := by
    intro w hw
    have := pt_cc_idx (P1 :: cs) 0 (by simp) w (by simpa using hw)
    simpa using this
  have hcci : ∀ w ∈ (PlaneTree.node cs).vtxs, w ≠ [] →
      (PlaneTree.node (P1 :: cs)).childCount (inc w) = (PlaneTree.node cs).childCount w := by
    intro w hw hne
    match w, hne with
    | a :: w', _ =>
      obtain ⟨hl, hmm⟩ := (pt_mem_idx cs a w').mp hw
      have := pt_cc_idx (P1 :: cs) (a + 1) (by simp; omega) w' (by simpa using hmm)
      simp only [List.getElem_cons_succ] at this
      show (PlaneTree.node (P1 :: cs)).childCount ((a + 1) :: w') = _
      rw [this, pt_cc_idx cs a hl w' hmm]
  -- boundary facts for the first and last corners of the root of P1 (the vertex `[0]` of P)
  have hL1m : P1.childCount [] = 0 ↔ L1 = 0 := by
    constructor
    · exact r1c
    · intro hL
      by_contra hne
      have := r1a (by omega)
      have := getD_lt_of_ne _ _ (by rw [this]; simp)
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
  have hroot1 : ([] : List ℕ) ∈ P1.vtxs := pt_root_mem P1
  have hroot2 : ([] : List ℕ) ∈ (PlaneTree.node cs).vtxs := pt_root_mem _
  -- first corner of `[0]`: the step from position 1 to 2
  have hfirst : (PlaneTree.node (P1 :: cs)).contour.getD (0 + 1 + 1) [] =
      cpost [0] (P1.childCount []) 0 := by
    rw [hpost 0 (Nat.zero_le _)]
    by_cases hz : P1.childCount [] = 0
    · have hL : L1 = 0 := r1c hz
      rw [if_pos hL.symm, hz, cpost_self]; rfl
    · have hL : L1 ≠ 0 := fun h => hz (hL1m.mpr h)
      rw [if_neg (Ne.symm hL), cpost_ne _ (Ne.symm hz), r1a (by omega)]
      rfl
  -- last corner of `[0]`: position `L1 + 1`
  have hlastpre : 1 ≤ P1.childCount [] → (PlaneTree.node (P1 :: cs)).contour.getD (L1 + 1 - 1) [] =
      cpre [0] (P1.childCount []) := by
    intro hm1
    have hL : L1 ≠ 0 := fun h => by have := hL1m.mpr h; omega
    rw [hpre L1 le_rfl, if_neg hL, r1b hm1]
    obtain ⟨t, ht⟩ : ∃ t, P1.childCount [] = t + 1 := ⟨P1.childCount [] - 1, by omega⟩
    rw [ht, cpre_succ]
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
        have := getD_lt_of_ne _ _ (by rw [this]; simp)
        omega
      rw [show L1 + L2 + 2 - 1 = L1 + 2 + (L2 - 1) by omega, hc (L2 - 1) (by omega), r2b (by omega)]
      simp [inc]
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
          · simp [cpre_zero]
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
            · rw [if_pos hL', cpost_self]; rfl
          · have hs1pos : 1 ≤ s1 := by omega
            obtain ⟨j, hj, hjr, hjpre, hjpost⟩ := bw1 s1 hs1pos (by omega)
            rw [hw] at hjr hjpre hjpost hj
            obtain ⟨hj0, hjm⟩ := hjr rfl
            obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
            refine ⟨t + 1, hj, ?_, ?_, ?_⟩
            · intro h; simp at h
            · rw [if_neg h0, hjpre, cpre_succ, cpre_succ]; rfl
            · rw [if_neg hL', hjpost, cpost_ne _ (by omega), cpost_ne _ (by omega)]; rfl
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
        · rw [if_neg (by omega), cpre_cons0 hw, hjpre]
        · rw [if_neg (by omega), hcc0 _ hwmem, cpost_cons0 hw, hjpost]
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
        · rw [cpre_succ]; rfl
        · rw [cpost_ne _ (by omega)]; rfl
      · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
        have hS : (PlaneTree.node (P1 :: cs)).contour.getD (L1 + 2 + (q' + 1)) [] =
            inc ((PlaneTree.node cs).contour.getD (q' + 1) []) := hc _ (by omega)
        have hPre : (PlaneTree.node (P1 :: cs)).contour.getD (L1 + 2 + (q' + 1) - 1) [] =
            inc ((PlaneTree.node cs).contour.getD q' []) := by
          rw [show L1 + 2 + (q' + 1) - 1 = L1 + 2 + q' by omega]; exact hc _ (by omega)
        have hPost : (PlaneTree.node (P1 :: cs)).contour.getD (L1 + 2 + (q' + 1) + 1) [] =
            inc ((PlaneTree.node cs).contour.getD (q' + 1 + 1) []) := by
          rw [show L1 + 2 + (q' + 1) + 1 = L1 + 2 + (q' + 1 + 1) by omega]; exact hc _ (by omega)
        rw [hS, hPre, hPost]
        obtain ⟨j, hj, hjr, hjpre, hjpost⟩ := bw2 (q' + 1) (by omega) (by omega)
        rw [Nat.add_sub_cancel] at hjpre
        have hwmem := m2 (q' + 1) (by omega)
        by_cases hw : (PlaneTree.node cs).contour.getD (q' + 1) [] = []
        · rw [hw] at hjr hjpre hjpost hj
          rw [hw, show inc ([] : List ℕ) = [] from rfl, hm]
          obtain ⟨hj0, hjm⟩ := hjr rfl
          obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
          refine ⟨t + 2, ?_, ?_, ?_, ?_⟩
          · omega
          · intro _; omega
          · rw [hjpre, cpre_succ, cpre_succ]; rfl
          · rw [hjpost, cpost_ne _ (by omega), cpost_ne _ (by omega)]; rfl
        · have hwmem' := hwmem
          rw [hcci _ hwmem hw]
          refine ⟨j, hj, ?_, ?_, ?_⟩
          · intro h; exact absurd h (inc_ne_nil hw)
          · rw [cpre_inc hw, hjpre]
          · rw [cpost_inc hw, hjpost]
  · -- forward corners
    intro u hu j hj hr
    rw [mem_vtxs_cons] at hu
    rcases hu with rfl | ⟨w, hw, rfl⟩ | ⟨w, hw, hwne, rfl⟩
    · -- the root
      obtain ⟨hj0, hjm⟩ := hr rfl
      rw [hm] at hjm hj ⊢
      have hN : 2 ≤ cs.length + 1 := by omega
      have hL2 : 1 ≤ L2 := by
        have := r2a (by omega)
        have := getD_lt_of_ne _ _ (by rw [this]; simp)
        omega
      by_cases hj1 : j = 1
      · subst hj1
        have hS : (PlaneTree.node (P1 :: cs)).contour.getD (L1 + 2) [] = [] := by
          rw [show L1 + 2 = L1 + 2 + 0 by omega, hc 0 (by omega), hc20]; rfl
        refine ⟨L1 + 2, by omega, by omega, hS, ?_, ?_⟩
        · rw [show L1 + 2 - 1 = L1 + 1 by omega, hb L1 le_rfl, e1, cpre_succ]; rfl
        · rw [show L1 + 2 + 1 = L1 + 2 + 1 from rfl, hc 1 (by omega), r2a (by omega),
            cpost_ne _ (by omega)]; rfl
      · obtain ⟨s', hs1', hs2', hsu, hsp, hspost⟩ :=
          fw2 [] hroot2 (j - 1) (by rw [hm2]; omega)
            (fun _ => ⟨by have := hm2; omega, by have := hm2; omega⟩)
        refine ⟨L1 + 2 + s', by omega, by omega, ?_, ?_, ?_⟩
        · rw [hc s' (by omega), hsu]; rfl
        · rw [show L1 + 2 + s' - 1 = L1 + 2 + (s' - 1) by omega, hc (s' - 1) (by omega), hsp]
          obtain ⟨t, rfl⟩ : ∃ t, j = t + 2 := ⟨j - 2, by omega⟩
          rw [show t + 2 - 1 = t + 1 by omega, cpre_succ, cpre_succ]; rfl
        · have hh := hc (s' + 1) (by omega)
          rw [show L1 + 2 + s' + 1 = L1 + 2 + (s' + 1) by omega, hh, hspost]
          obtain ⟨t, rfl⟩ : ∃ t, j = t + 2 := ⟨j - 2, by omega⟩
          rw [show t + 2 - 1 = t + 1 by omega, cpost_ne _ (by omega), cpost_ne _ (by omega)]; rfl
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
          · rw [cpre_zero]; exact ha
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
            · rw [hlastpost, hjm, cpost_self]; rfl
          · obtain ⟨s1, hs1a, hs1b, hs1u, hs1p, hs1q⟩ :=
              fw1 [] hroot1 j hj (fun _ => ⟨by omega, by omega⟩)
            refine ⟨s1 + 1, by omega, by omega, ?_, ?_, ?_⟩
            · rw [hb s1 (by omega), hs1u]
            · rw [hpre s1 (by omega), if_neg (by omega), hs1p]
              obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
              rw [cpre_succ, cpre_succ]; rfl
            · rw [hpost s1 (by omega), if_neg (by omega), hs1q, cpost_ne _ (by omega),
                cpost_ne _ (by omega)]; rfl
      · obtain ⟨s1, hs1a, hs1b, hs1u, hs1p, hs1q⟩ := fw1 w hw j hj (fun h => absurd h hw0)
        refine ⟨s1 + 1, by omega, by omega, ?_, ?_, ?_⟩
        · rw [hb s1 (by omega), hs1u]
        · rw [hpre s1 (by omega), if_neg (by omega), cpre_cons0 hw0, hs1p]
        · rw [hpost s1 (by omega), if_neg (by omega), cpost_cons0 hw0, hs1q]
    · -- vertices of the remaining subtrees
      rw [hcci w hw hwne] at hj ⊢
      obtain ⟨s', hs1', hs2', hsu, hsp, hspost⟩ := fw2 w hw j hj (fun h => absurd h hwne)
      refine ⟨L1 + 2 + s', by omega, by omega, ?_, ?_, ?_⟩
      · rw [hc s' (by omega), hsu]
      · rw [show L1 + 2 + s' - 1 = L1 + 2 + (s' - 1) by omega, hc (s' - 1) (by omega), hsp,
          cpre_inc hwne]
      · rw [show L1 + 2 + s' + 1 = L1 + 2 + (s' + 1) by omega, hc (s' + 1) (by omega), hspost,
          cpost_inc hwne]

private theorem pt_pinv_ci (P : PlaneTree) : PInv (P.contour.length - 1) P ∧ CI (P.contour.length - 1) P := by
  have : ∃ L, PInv L P ∧ CI L P := by
    refine plane_ind (fun P => ∃ L, PInv L P ∧ CI L P) ⟨0, pinv_base, ci_base⟩ ?_ P
    intro P1 cs ⟨L1, h1, k1⟩ ⟨L2, h2, k2⟩
    exact ⟨_, pinv_combine h1 h2, ci_combine h1 h2 k1 k2⟩
  obtain ⟨L, hL, kL⟩ := this
  have := hL.1
  rw [this]
  simpa using ⟨hL, kL⟩

private theorem list_split_unique {α : Type} {x : α} : ∀ (A A' B B' : List α), x ∉ A → x ∉ A' →
    A ++ x :: B = A' ++ x :: B' → A = A' ∧ B = B' := by
  intro A
  induction A with
  | nil =>
    intro A' B B' _ hA' h
    cases A' with
    | nil => simpa using h
    | cons a A'' =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (by rw [h.1]; exact List.mem_cons_self) hA'
  | cons a A ih =>
    intro A' B B' hA hA' h
    cases A' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (by rw [← h.1]; exact List.mem_cons_self) hA
    | cons a' A'' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      have := ih A'' B B' (fun hh => hA (List.mem_cons_of_mem _ hh))
        (fun hh => hA' (List.mem_cons_of_mem _ hh)) h2
      exact ⟨by rw [this.1], this.2⟩

private theorem pt_contour_inj : ∀ P : PlaneTree, ∀ Q : PlaneTree, P.contour = Q.contour → P = Q := by
  refine plane_ind (fun P => ∀ Q : PlaneTree, P.contour = Q.contour → P = Q) ?_ ?_
  · intro Q h
    cases Q with
    | node ds =>
      cases ds with
      | nil => rfl
      | cons Q1 ds' =>
        exfalso
        have h1 := pt_contour_len (PlaneTree.node [])
        have h2 := pt_contour_len (PlaneTree.node (Q1 :: ds'))
        rw [h] at h1
        rw [pt_vtxs_len] at h2
        have := pt_vtxs_pos Q1
        have := pt_vtxs_pos (PlaneTree.node ds')
        have h3 : (PlaneTree.node ([] : List PlaneTree)).vtxs.length = 1 := by
          simp [PlaneTree.vtxs, vtxsForest]
        omega
  · intro P1 cs ih1 ih2 Q h
    cases Q with
    | node ds =>
      cases ds with
      | nil =>
        exfalso
        have h1 := pt_contour_len (PlaneTree.node (P1 :: cs))
        have h2 := pt_contour_len (PlaneTree.node ([] : List PlaneTree))
        rw [← h] at h2
        rw [pt_vtxs_len] at h1
        have := pt_vtxs_pos P1
        have := pt_vtxs_pos (PlaneTree.node cs)
        have h3 : (PlaneTree.node ([] : List PlaneTree)).vtxs.length = 1 := by
          simp [PlaneTree.vtxs, vtxsForest]
        omega
      | cons Q1 ds' =>
        rw [contour_node_cons, contour_node_cons] at h
        have h' : [] :: (P1.contour.map (List.cons 0) ++ [[]] ++ (contourForest cs 0).map inc) =
            [] :: (Q1.contour.map (List.cons 0) ++ [[]] ++ (contourForest ds' 0).map inc) := h
        have h'' := List.cons.inj h' |>.2
        rw [List.append_assoc, List.append_assoc] at h''
        have hn1 : ([] : List ℕ) ∉ P1.contour.map (List.cons 0) := by simp
        have hn2 : ([] : List ℕ) ∉ Q1.contour.map (List.cons 0) := by simp
        obtain ⟨hA, hB⟩ := list_split_unique _ _ _ _ hn1 hn2 (by simpa using h'')
        have hP1 : P1.contour = Q1.contour := List.map_injective_iff.mpr
          (fun a b hab => by simpa using hab) hA
        have hcs : (contourForest cs 0) = (contourForest ds' 0) :=
          List.map_injective_iff.mpr (fun a b hab => inc_inj hab) hB
        have e1 := ih1 Q1 hP1
        have e2 := ih2 (PlaneTree.node ds') (by rw [contour_node, contour_node, hcs])
        injection e2 with e2
        rw [e1, e2]

private theorem eq_append_getLastD {x u : List ℕ} (hne : x ≠ []) (hdl : x.dropLast = u) :
    x = u ++ [x.getLastD 0] := by
  subst hdl
  rcases List.eq_nil_or_concat x with h | ⟨L', b, rfl⟩
  · exact absurd h hne
  · simp

private theorem pt_prefix_visited {L : ℕ} {P : PlaneTree} (h : PInv L P) :
    ∀ i ≤ L, ∀ v, v <+: P.contour.getD i [] → ∃ i'' ≤ i, P.contour.getD i'' [] = v := by
  obtain ⟨l, e, m, c, ch, p, o⟩ := h
  intro i
  induction i with
  | zero =>
    intro _ v hv
    rw [contour_getD_zero] at hv
    have : v = [] := List.prefix_nil.mp hv
    exact ⟨0, le_rfl, by rw [this]; exact contour_getD_zero P⟩
  | succ i ih =>
    intro hi v hv
    have hstep := ch i (by omega)
    rcases hstep with ⟨hne, hdl⟩ | ⟨hne, hdl⟩
    · -- child step
      have hx := eq_append_getLastD hne hdl
      rw [hx] at hv
      rcases List.prefix_concat_iff.mp hv with hv | hv
      · exact ⟨i + 1, le_rfl, hx.trans hv.symm⟩
      · obtain ⟨j, hj, hje⟩ := ih (by omega) v hv
        exact ⟨j, by omega, hje⟩
    · -- parent step
      rw [← hdl] at hv
      have hv' : v <+: P.contour.getD i [] := hv.trans (List.dropLast_prefix _)
      obtain ⟨j, hj, hje⟩ := ih (by omega) v hv'
      exact ⟨j, by omega, hje⟩

private theorem pt_parent_visited {L : ℕ} {P : PlaneTree} (h : PInv L P) (i : ℕ) (hi : i ≤ L)
    (hne : P.contour.getD i [] ≠ []) :
    ∃ i'' < i, P.contour.getD i'' [] = (P.contour.getD i []).dropLast := by
  obtain ⟨j, hj, hje⟩ := pt_prefix_visited h i hi _ (List.dropLast_prefix _)
  refine ⟨j, ?_, hje⟩
  rcases Nat.lt_or_ge j i with h1 | h1
  · exact h1
  · have : j = i := by omega
    rw [this] at hje
    exfalso
    have := congrArg List.length hje
    rw [List.length_dropLast] at this
    have hpos : 0 < (P.contour.getD i []).length := List.length_pos_iff.mpr hne
    omega

private theorem pt_determ_step {L : ℕ} {P Q : PlaneTree} (hP : PInv L P) (hQ : PInv L Q)
    (heq : ∀ i j, i ≤ L → j ≤ L →
      (P.contour.getD i [] = P.contour.getD j [] ↔ Q.contour.getD i [] = Q.contour.getD j []))
    (i : ℕ) (hi : i + 1 ≤ L)
    (hq : ∀ i' ≤ i, P.contour.getD i' [] = Q.contour.getD i' []) :
    P.contour.getD (i + 1) [] = Q.contour.getD (i + 1) [] := by
  obtain ⟨u, hu1⟩ : ∃ u, P.contour.getD i [] = u := ⟨_, rfl⟩
  have hu2 : Q.contour.getD i [] = u := by rw [← hq i le_rfl, hu1]
  obtain ⟨x, hx1⟩ : ∃ x, P.contour.getD (i + 1) [] = x := ⟨_, rfl⟩
  obtain ⟨y, hy1⟩ : ∃ y, Q.contour.getD (i + 1) [] = y := ⟨_, rfl⟩
  have hstepP := hP.2.2.2.2.1 i (by omega)
  have hstepQ := hQ.2.2.2.2.1 i (by omega)
  rw [hu1, hx1] at hstepP
  rw [hu2, hy1] at hstepQ
  rw [hx1, hy1]
  have hvP : ∀ s ≤ L, P.contour.getD s [] ∈ P.vtxs := hP.2.2.1
  have hvQ : ∀ s ≤ L, Q.contour.getD s [] ∈ Q.vtxs := hQ.2.2.1
  rcases hstepP with ⟨hxne, hxdl⟩ | ⟨hune, hxdl⟩ <;>
    rcases hstepQ with ⟨hyne, hydl⟩ | ⟨hune', hydl⟩
  · -- child, child
    have ex := eq_append_getLastD hxne hxdl
    have ey := eq_append_getLastD hyne hydl
    by_contra hxy
    have hab : x.getLastD 0 ≠ y.getLastD 0 := fun h => hxy (by rw [ex, ey, h])
    rcases Nat.lt_or_gt_of_ne hab with hlt | hgt
    · have hyv : u ++ [y.getLastD 0] ∈ Q.vtxs := by
        have := hvQ (i + 1) hi
        rw [hy1, ey] at this; exact this
      have hxv : u ++ [x.getLastD 0] ∈ Q.vtxs := pt_prefix_closed u Q _ _ hlt hyv
      obtain ⟨s', hs', hse⟩ := hQ.2.2.2.2.2.2 u _ _ (i + 1) hxv hyv hlt (by rw [hy1]; exact ey)
      have h1 : P.contour.getD s' [] = P.contour.getD (i + 1) [] := by
        rw [hq s' (by omega), hse, hx1]; exact ex.symm
      have h2 := (heq s' (i + 1) (by omega) hi).mp h1
      rw [hse, hy1, ey] at h2
      exact hab (by simpa using List.append_cancel_left h2)
    · have hxv : u ++ [x.getLastD 0] ∈ P.vtxs := by
        have := hvP (i + 1) hi
        rw [hx1, ex] at this; exact this
      have hyv : u ++ [y.getLastD 0] ∈ P.vtxs := pt_prefix_closed u P _ _ hgt hxv
      obtain ⟨s', hs', hse⟩ := hP.2.2.2.2.2.2 u _ _ (i + 1) hyv hxv hgt (by rw [hx1]; exact ex)
      have h1 : Q.contour.getD s' [] = Q.contour.getD (i + 1) [] := by
        rw [← hq s' (by omega), hse, hy1]; exact ey.symm
      have h2 := (heq s' (i + 1) (by omega) hi).mpr h1
      rw [hse, hx1, ex] at h2
      exact hab (by simpa using (List.append_cancel_left h2).symm)
  · -- P child, Q parent
    exfalso
    obtain ⟨i'', hi'', hie⟩ := pt_parent_visited hQ i (by omega) (by rw [hu2]; exact hune')
    rw [hu2] at hie
    have h1 : Q.contour.getD i'' [] = Q.contour.getD (i + 1) [] := by rw [hie, hy1]; exact hydl
    have h2 := (heq i'' (i + 1) (by omega) hi).mpr h1
    rw [hq i'' (by omega), hie, hx1] at h2
    have h3 := congrArg List.length h2
    have h4 := congrArg List.length hxdl
    rw [List.length_dropLast] at h3 h4
    have := List.length_pos_iff.mpr hune'
    have := List.length_pos_iff.mpr hxne
    omega
  · -- P parent, Q child
    exfalso
    obtain ⟨i'', hi'', hie⟩ := pt_parent_visited hP i (by omega) (by rw [hu1]; exact hune)
    rw [hu1] at hie
    have h1 : P.contour.getD i'' [] = P.contour.getD (i + 1) [] := by rw [hie, hx1]; exact hxdl
    have h2 := (heq i'' (i + 1) (by omega) hi).mp h1
    rw [← hq i'' (by omega), hie, hy1] at h2
    have h3 := congrArg List.length h2
    have h4 := congrArg List.length hydl
    rw [List.length_dropLast] at h3 h4
    have := List.length_pos_iff.mpr hune
    have := List.length_pos_iff.mpr hyne
    omega
  · exact hxdl.symm.trans hydl

private theorem pt_determ (P Q : PlaneTree) (hlen : P.contour.length = Q.contour.length)
    (heq : ∀ i j, i < P.contour.length → j < P.contour.length →
      (P.contour.getD i [] = P.contour.getD j [] ↔ Q.contour.getD i [] = Q.contour.getD j [])) :
    P = Q := by
  have hP := (pt_pinv_ci P).1
  have hQ : PInv (P.contour.length - 1) Q := by rw [hlen]; exact (pt_pinv_ci Q).1
  obtain ⟨L, hL⟩ : ∃ L, L = P.contour.length - 1 := ⟨_, rfl⟩
  rw [← hL] at hP hQ
  have hlP : P.contour.length = L + 1 := hP.1
  have hlQ : Q.contour.length = L + 1 := hQ.1
  have key : ∀ i ≤ L, P.contour.getD i [] = Q.contour.getD i [] := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · intro _; rw [contour_getD_zero, contour_getD_zero]
      · intro hi
        obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        exact pt_determ_step hP hQ (fun a b ha hb => heq a b (by omega) (by omega)) i hi
          (fun i' hi' => ih i' (by omega) (by omega))
  have hlist : P.contour = Q.contour := by
    apply List.ext_getElem (by omega)
    intro i h1 h2
    have := key i (by omega)
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at this
    simpa using this
  exact pt_contour_inj P Q hlist

/-! ## The polygon walk and the quotient graph (helpers of `lem_app_vol_closed_encoding_i`) -/

/-- Step index of the z-edge of factor `s` along the polygon (positions `0,…,2k`). -/
private def zi (s : ℕ) : ℕ := 2 * s + s % 2

/-- Step index of the w-edge of factor `s` along the polygon. -/
private def wi (s : ℕ) : ℕ := 2 * s + (s + 1) % 2

/-- The polygon vertex at position `i` (position `0` is `e_{k-1}`, `2s+1` is `l_s`, `2s+2` is `e_s`). -/
private def vAt (k : ℕ) [NeZero k] (i : ℕ) : TreeVtx k :=
  if i % 2 = 0 then Sum.inl (Fin.ofNat k (i / 2 + k - 1)) else Sum.inr (Fin.ofNat k (i / 2))

private theorem vAt_even (k : ℕ) [NeZero k] (r : ℕ) :
    vAt k (2 * r) = Sum.inl (Fin.ofNat k (r + k - 1)) := by
  simp [vAt]

private theorem vAt_odd (k : ℕ) [NeZero k] (r : ℕ) :
    vAt k (2 * r + 1) = Sum.inr (Fin.ofNat k r) := by
  have h1 : (2 * r + 1) % 2 = 1 := by omega
  have h2 : (2 * r + 1) / 2 = r := by omega
  simp [vAt, h1, h2]

private theorem fin_ofNat_val {k : ℕ} [NeZero k] (s : Fin k) : Fin.ofNat k s.val = s := by
  apply Fin.ext
  rw [Fin.val_ofNat]
  exact Nat.mod_eq_of_lt s.isLt

private theorem outV_even {k : ℕ} [NeZero k] (s : Fin k) (h : s.val % 2 = 0) :
    treeOutV s = Fin.ofNat k (s.val + k - 1) := by
  unfold treeOutV
  rw [if_pos h]
  apply Fin.ext
  unfold treePrev
  rw [Fin.val_ofNat]
  have := NeZero.pos k
  show (s.val + (k - 1)) % k = (s.val + k - 1) % k
  congr 1
  omega

private theorem outV_odd {k : ℕ} (s : Fin k) (h : s.val % 2 = 1) : treeOutV s = s := by
  unfold treeOutV
  rw [if_neg (by omega)]

private theorem inV_even {k : ℕ} (s : Fin k) (h : s.val % 2 = 0) : treeInV s = s := by
  unfold treeInV
  rw [if_pos h]

private theorem inV_odd {k : ℕ} [NeZero k] (s : Fin k) (h : s.val % 2 = 1) :
    treeInV s = Fin.ofNat k (s.val + k - 1) := by
  unfold treeInV
  rw [if_neg (by omega)]
  apply Fin.ext
  unfold treePrev
  rw [Fin.val_ofNat]
  have := NeZero.pos k
  show (s.val + (k - 1)) % k = (s.val + k - 1) % k
  congr 1
  omega

private theorem stepZ {k : ℕ} [NeZero k] (s : Fin k) :
    (s.val % 2 = 0 → vAt k (zi s.val) = Sum.inl (treeOutV s) ∧ vAt k (zi s.val + 1) = Sum.inr s) ∧
    (s.val % 2 = 1 → vAt k (zi s.val) = Sum.inr s ∧ vAt k (zi s.val + 1) = Sum.inl (treeOutV s)) := by
  constructor
  · intro h
    have e : zi s.val = 2 * s.val := by unfold zi; omega
    rw [e, vAt_even, outV_even s h, show 2 * s.val + 1 = 2 * s.val + 1 from rfl, vAt_odd,
      fin_ofNat_val]
    exact ⟨rfl, rfl⟩
  · intro h
    have e : zi s.val = 2 * s.val + 1 := by unfold zi; omega
    rw [e, vAt_odd, show 2 * s.val + 1 + 1 = 2 * (s.val + 1) by omega, vAt_even, outV_odd s h,
      fin_ofNat_val]
    refine ⟨rfl, ?_⟩
    congr 2
    apply Fin.ext
    rw [Fin.val_ofNat]
    have := s.isLt
    have : s.val + 1 + k - 1 = s.val + k := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt s.isLt]

private theorem stepW {k : ℕ} [NeZero k] (s : Fin k) :
    (s.val % 2 = 0 → vAt k (wi s.val) = Sum.inr s ∧ vAt k (wi s.val + 1) = Sum.inl (treeInV s)) ∧
    (s.val % 2 = 1 → vAt k (wi s.val) = Sum.inl (treeInV s) ∧ vAt k (wi s.val + 1) = Sum.inr s) := by
  constructor
  · intro h
    have e : wi s.val = 2 * s.val + 1 := by unfold wi; omega
    rw [e, vAt_odd, show 2 * s.val + 1 + 1 = 2 * (s.val + 1) by omega, vAt_even, inV_even s h,
      fin_ofNat_val]
    refine ⟨rfl, ?_⟩
    congr 2
    apply Fin.ext
    rw [Fin.val_ofNat]
    have := s.isLt
    have : s.val + 1 + k - 1 = s.val + k := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt s.isLt]
  · intro h
    have e : wi s.val = 2 * s.val := by unfold wi; omega
    rw [e, vAt_even, inV_odd s h, vAt_odd, fin_ofNat_val]
    exact ⟨rfl, rfl⟩

private theorem treePos_lt {k : ℕ} [NeZero k] (x : TreeVtx k) : treePos x < 2 * k := by
  cases x with
  | inl s =>
    show 2 * (s.val + 1) % (2 * k) < 2 * k
    exact Nat.mod_lt _ (by have := NeZero.pos k; omega)
  | inr s =>
    show 2 * s.val + 1 < 2 * k
    have := s.isLt; omega

private theorem vAt_treePos {k : ℕ} [NeZero k] (x : TreeVtx k) : vAt k (treePos x) = x := by
  cases x with
  | inl s =>
    show vAt k (2 * (s.val + 1) % (2 * k)) = _
    have hs := s.isLt
    by_cases h : s.val + 1 < k
    · rw [Nat.mod_eq_of_lt (by omega), vAt_even]
      congr 1
      apply Fin.ext
      rw [Fin.val_ofNat]
      have : s.val + 1 + k - 1 = s.val + k := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt s.isLt]
    · have h1 : s.val + 1 = k := by omega
      rw [h1, Nat.mod_self, show (0 : ℕ) = 2 * 0 from rfl, vAt_even]
      congr 1
      apply Fin.ext
      rw [Fin.val_ofNat]
      have : 0 + k - 1 = s.val := by omega
      rw [this, Nat.mod_eq_of_lt s.isLt]
  | inr s =>
    show vAt k (2 * s.val + 1) = _
    rw [vAt_odd, fin_ofNat_val]

private theorem treePos_vAt {k : ℕ} [NeZero k] {i : ℕ} (hi : i < 2 * k) : treePos (vAt k i) = i := by
  rcases Nat.even_or_odd' i with ⟨r, rfl | rfl⟩
  · rw [vAt_even]
    show 2 * ((Fin.ofNat k (r + k - 1)).val + 1) % (2 * k) = 2 * r
    rw [Fin.val_ofNat]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · have h1 : (0 + k - 1) % k = k - 1 := by
        have := NeZero.pos k
        rw [show 0 + k - 1 = k - 1 by omega]
        exact Nat.mod_eq_of_lt (by omega)
      have h2 : 2 * (k - 1 + 1) = 2 * k := by have := NeZero.pos k; congr 1; omega
      rw [h1, h2, Nat.mod_self]
    · have h1 : (r + k - 1) % k = r - 1 := by
        rw [show r + k - 1 = (r - 1) + k by omega, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      have h2 : 2 * (r - 1 + 1) = 2 * r := by congr 1; omega
      rw [h1, h2, Nat.mod_eq_of_lt hi]
  · rw [vAt_odd]
    show 2 * (Fin.ofNat k r).val + 1 = 2 * r + 1
    rw [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem treePos_surj {k : ℕ} [NeZero k] {i : ℕ} (hi : i < 2 * k) : ∃ x : TreeVtx k, treePos x = i :=
  ⟨vAt k i, treePos_vAt hi⟩

/-! ### Types of classes -/

private theorem prev_val {k : ℕ} (s : Fin k) :
    (treePrev s).val = if s.val = 0 then k - 1 else s.val - 1 := by
  obtain ⟨v, hv⟩ := s
  unfold treePrev
  dsimp only
  rcases Nat.eq_zero_or_pos v with rfl | hpos
  · simp [Nat.mod_eq_of_lt (show k - 1 < k by omega)]
  · rw [if_neg (show ¬ (v = 0) by omega)]
    have e : v + (k - 1) = (v - 1) + k := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (show v - 1 < k by omega)]

private theorem outV_val_odd {k : ℕ} (hk : k % 2 = 0) (s : Fin k) : (treeOutV s).val % 2 = 1 := by
  have hs := s.isLt
  unfold treeOutV
  split_ifs with h
  · have h' : s.val % 2 = 0 := h
    rw [prev_val]
    split_ifs with h0 <;> omega
  · have h' : ¬ s.val % 2 = 0 := h
    omega

private theorem inV_val_even {k : ℕ} (s : Fin k) : (treeInV s).val % 2 = 0 := by
  have hs := s.isLt
  unfold treeInV
  split_ifs with h
  · exact h
  · have h' : ¬ s.val % 2 = 0 := h
    rw [prev_val]
    split_ifs with h0 <;> omega

private def vty {k : ℕ} : TreeVtx k → VType
  | Sum.inl e => if e.val % 2 = 1 then VType.out else VType.inp
  | Sum.inr _ => VType.lat

private theorem vty_resp {k : ℕ} (hk : k % 2 = 0) (p : TreeMatch k × TreeMatch k) {x y : TreeVtx k}
    (h : treeSetoid p x y) : vty x = vty y := by
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
      simp only [vty]
      rw [if_pos (outV_val_odd hk s), if_pos (outV_val_odd hk (p.1.1 s))]
    · obtain ⟨h1a, h1b⟩ := h1
      subst h1a; subst h1b
      simp only [vty]
      rw [if_neg (by have := inV_val_even s; omega), if_neg (by have := inV_val_even (p.2.1 s); omega)]
  | refl => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

private def ctype {k : ℕ} (hk : k % 2 = 0) (p : TreeMatch k × TreeMatch k) :
    Quotient (treeSetoid p) → VType :=
  Quotient.lift vty (fun _ _ h => vty_resp hk p h)

private theorem ctype_mk {k : ℕ} (hk : k % 2 = 0) (p : TreeMatch k × TreeMatch k) (x : TreeVtx k) :
    ctype hk p (treeMk p x) = vty x := rfl

/-! ### The quotient graph -/

private def qg {k : ℕ} (p : TreeMatch k × TreeMatch k) : SimpleGraph (Quotient (treeSetoid p)) :=
  SimpleGraph.fromRel fun x y : Quotient (treeSetoid p) =>
    ∃ s : Fin k,
      (x = treeMk p (Sum.inr s) ∧ y = treeMk p (Sum.inl (treeOutV s))) ∨
      (x = treeMk p (Sum.inr s) ∧ y = treeMk p (Sum.inl (treeInV s)))

private theorem mk_inr_ne_inl {k : ℕ} (hk : k % 2 = 0) (p : TreeMatch k × TreeMatch k) (s e : Fin k) :
    treeMk p (Sum.inr s) ≠ treeMk p (Sum.inl e) := by
  intro h
  have := vty_resp hk p (Quotient.exact h)
  revert this
  simp only [vty]
  split_ifs <;> simp

private theorem qg_adj_out {k : ℕ} (hk : k % 2 = 0) (p : TreeMatch k × TreeMatch k) (s : Fin k) :
    (qg p).Adj (treeMk p (Sum.inr s)) (treeMk p (Sum.inl (treeOutV s))) := by
  unfold qg
  rw [SimpleGraph.fromRel_adj]
  exact ⟨mk_inr_ne_inl hk p _ _, Or.inl ⟨s, Or.inl ⟨rfl, rfl⟩⟩⟩

private theorem qg_adj_in {k : ℕ} (hk : k % 2 = 0) (p : TreeMatch k × TreeMatch k) (s : Fin k) :
    (qg p).Adj (treeMk p (Sum.inr s)) (treeMk p (Sum.inl (treeInV s))) := by
  unfold qg
  rw [SimpleGraph.fromRel_adj]
  exact ⟨mk_inr_ne_inl hk p _ _, Or.inl ⟨s, Or.inr ⟨rfl, rfl⟩⟩⟩

/-- Edges of the quotient graph are the z- and w-edges of the factors. -/
private theorem qg_edge_cases {k : ℕ} (p : TreeMatch k × TreeMatch k) {e : Sym2 (Quotient (treeSetoid p))}
    (he : e ∈ (qg p).edgeSet) :
    ∃ s : Fin k, e = s(treeMk p (Sum.inr s), treeMk p (Sum.inl (treeOutV s))) ∨
      e = s(treeMk p (Sum.inr s), treeMk p (Sum.inl (treeInV s))) := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [SimpleGraph.mem_edgeSet] at he
    unfold qg at he
    rw [SimpleGraph.fromRel_adj] at he
    obtain ⟨_, ⟨s, h1 | h1⟩ | ⟨s, h1 | h1⟩⟩ := he
    · obtain ⟨rfl, rfl⟩ := h1; exact ⟨s, Or.inl rfl⟩
    · obtain ⟨rfl, rfl⟩ := h1; exact ⟨s, Or.inr rfl⟩
    · obtain ⟨rfl, rfl⟩ := h1; exact ⟨s, Or.inl (Sym2.eq_swap)⟩
    · obtain ⟨rfl, rfl⟩ := h1; exact ⟨s, Or.inr (Sym2.eq_swap)⟩

private def phi {k : ℕ} [NeZero k] (p : TreeMatch k × TreeMatch k) (i : ℕ) : Quotient (treeSetoid p) :=
  treeMk p (vAt k i)

private theorem phi_zi {k : ℕ} [NeZero k] (p : TreeMatch k × TreeMatch k) (s : Fin k) :
    s(phi p (zi s.val), phi p (zi s.val + 1)) =
      s(treeMk p (Sum.inr s), treeMk p (Sum.inl (treeOutV s))) := by
  rcases Nat.mod_two_eq_zero_or_one s.val with h | h
  · obtain ⟨a, b⟩ := (stepZ s).1 h
    unfold phi; rw [a, b]; exact Sym2.eq_swap
  · obtain ⟨a, b⟩ := (stepZ s).2 h
    unfold phi; rw [a, b]

private theorem phi_wi {k : ℕ} [NeZero k] (p : TreeMatch k × TreeMatch k) (s : Fin k) :
    s(phi p (wi s.val), phi p (wi s.val + 1)) =
      s(treeMk p (Sum.inr s), treeMk p (Sum.inl (treeInV s))) := by
  rcases Nat.mod_two_eq_zero_or_one s.val with h | h
  · obtain ⟨a, b⟩ := (stepW s).1 h
    unfold phi; rw [a, b]
  · obtain ⟨a, b⟩ := (stepW s).2 h
    unfold phi; rw [a, b]; exact Sym2.eq_swap

/-- The pairing `p` matches the steps of the walk `W`: matched z-steps (resp. w-steps) traverse the same
edge. -/
private def Compat {k : ℕ} {X : Type} (W : ℕ → X) (p : TreeMatch k × TreeMatch k) : Prop :=
  (∀ s : Fin k, s(W (zi (p.1.1 s).val), W (zi (p.1.1 s).val + 1)) = s(W (zi s.val), W (zi s.val + 1))) ∧
  (∀ s : Fin k, s(W (wi (p.2.1 s).val), W (wi (p.2.1 s).val + 1)) = s(W (wi s.val), W (wi s.val + 1)))

private theorem mk_eq_of_rel {k : ℕ} (p : TreeMatch k × TreeMatch k) {x y : TreeVtx k}
    (h : treeRel p x y) : treeMk p x = treeMk p y :=
  Quotient.sound (Relation.EqvGen.rel _ _ h)

private theorem compat_phi {k : ℕ} [NeZero k] (p : TreeMatch k × TreeMatch k) : Compat (phi p) p := by
  constructor
  · intro s
    rw [phi_zi, phi_zi]
    have h1 : treeMk p (Sum.inr (p.1.1 s)) = treeMk p (Sum.inr s) :=
      (mk_eq_of_rel p ⟨s, Or.inl ⟨rfl, rfl⟩⟩).symm
    have h2 : treeMk p (Sum.inl (treeOutV (p.1.1 s))) = treeMk p (Sum.inl (treeOutV s)) :=
      (mk_eq_of_rel p ⟨s, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩).symm
    rw [h1, h2]
  · intro s
    rw [phi_wi, phi_wi]
    have h1 : treeMk p (Sum.inr (p.2.1 s)) = treeMk p (Sum.inr s) :=
      (mk_eq_of_rel p ⟨s, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩).symm
    have h2 : treeMk p (Sum.inl (treeInV (p.2.1 s))) = treeMk p (Sum.inl (treeInV s)) :=
      (mk_eq_of_rel p ⟨s, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩).symm
    rw [h1, h2]

private theorem qg_edge_card_le {k : ℕ} (p : TreeMatch k × TreeMatch k)
    (hedges : (Finset.univ.filter fun s : Fin k => s.val < (p.1.1 s).val).card +
      (Finset.univ.filter fun s : Fin k => s.val < (p.2.1 s).val).card = k) :
    Nat.card (qg p).edgeSet ≤ k := by
  classical
  let EZ : Fin k → Sym2 (Quotient (treeSetoid p)) :=
    fun s => s(treeMk p (Sum.inr s), treeMk p (Sum.inl (treeOutV s)))
  let EW : Fin k → Sym2 (Quotient (treeSetoid p)) :=
    fun s => s(treeMk p (Sum.inr s), treeMk p (Sum.inl (treeInV s)))
  have hEZ : ∀ s, EZ (p.1.1 s) = EZ s := by
    intro s
    show s(treeMk p (Sum.inr (p.1.1 s)), treeMk p (Sum.inl (treeOutV (p.1.1 s)))) = _
    rw [(mk_eq_of_rel p ⟨s, Or.inl ⟨rfl, rfl⟩⟩).symm,
      (mk_eq_of_rel p ⟨s, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩).symm]
  have hEW : ∀ s, EW (p.2.1 s) = EW s := by
    intro s
    show s(treeMk p (Sum.inr (p.2.1 s)), treeMk p (Sum.inl (treeInV (p.2.1 s)))) = _
    rw [(mk_eq_of_rel p ⟨s, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩).symm,
      (mk_eq_of_rel p ⟨s, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩).symm]
  let F : Finset (Sym2 (Quotient (treeSetoid p))) :=
    (Finset.univ.filter fun s : Fin k => s.val < (p.1.1 s).val).image EZ ∪
      (Finset.univ.filter fun s : Fin k => s.val < (p.2.1 s).val).image EW
  have hsub : (qg p).edgeSet ⊆ (F : Set _) := by
    intro e he
    obtain ⟨s, h | h⟩ := qg_edge_cases p he
    · subst h
      simp only [F, Finset.coe_union, Finset.coe_image, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_union, Set.mem_image, Set.mem_setOf_eq]
      left
      have hne := p.1.2.2 s
      rcases Nat.lt_or_gt_of_ne (fun h : s.val = (p.1.1 s).val => hne (Fin.ext h.symm)) with hlt | hgt
      · exact ⟨s, hlt, rfl⟩
      · refine ⟨p.1.1 s, ?_, hEZ s⟩
        rw [p.1.2.1 s]; exact hgt
    · subst h
      simp only [F, Finset.coe_union, Finset.coe_image, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_union, Set.mem_image, Set.mem_setOf_eq]
      right
      have hne := p.2.2.2 s
      rcases Nat.lt_or_gt_of_ne (fun h : s.val = (p.2.1 s).val => hne (Fin.ext h.symm)) with hlt | hgt
      · exact ⟨s, hlt, rfl⟩
      · refine ⟨p.2.1 s, ?_, hEW s⟩
        rw [p.2.2.1 s]; exact hgt
  calc Nat.card (qg p).edgeSet = (qg p).edgeSet.ncard := (Nat.card_coe_set_eq _)
    _ ≤ (F : Set _).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet F)
    _ = F.card := Set.ncard_coe_finset F
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ k := by
      refine le_trans (add_le_add Finset.card_image_le Finset.card_image_le) (le_of_eq hedges)

/-! ### Corner alternation versus the cyclic alternation of a typing -/

private theorem alt_getD_comp (ty : List ℕ → VType) (u : List ℕ) (m j : ℕ) (hj : j ≤ m) :
    (ty u.dropLast :: (List.range m).map fun i => ty (u ++ [i])).getD j VType.lat = ty (cpre u j) ∧
    (ty u.dropLast :: (List.range m).map fun i => ty (u ++ [i])).getD ((j + 1) % (m + 1)) VType.lat =
      ty (cpost u m j) := by
  constructor
  · rcases j with _ | j
    · simp [cpre_zero]
    · rw [cpre_succ]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_map]
      rw [List.getElem?_range (show j < m by omega)]
      simp
  · by_cases hjm : j = m
    · subst hjm
      rw [cpost_self, Nat.mod_self]
      simp
    · rw [cpost_ne _ hjm, Nat.mod_eq_of_lt (by omega)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_map]
      rw [List.getElem?_range (show j < m by omega)]
      simp

/-- Alternation of the types at the corners of the contour. -/
private def CornerAlt (P : PlaneTree) (ty : List ℕ → VType) : Prop :=
  ∀ s, 1 ≤ s → s + 1 ≤ P.contour.length - 1 → ty (P.contour.getD s []) = VType.lat →
    ty (P.contour.getD (s - 1) []) ≠ VType.lat ∧ ty (P.contour.getD (s + 1) []) ≠ VType.lat ∧
    ty (P.contour.getD (s - 1) []) ≠ ty (P.contour.getD (s + 1) [])

private theorem latent_alt_of_corner (P : PlaneTree) (ty : List ℕ → VType) (hCA : CornerAlt P ty) :
    ∀ u ∈ P.vtxs, u ≠ [] → ty u = VType.lat →
      CyclicAlt (ty u.dropLast :: (List.range (P.childCount u)).map fun i => ty (u ++ [i])) := by
  intro u hu hne hty j hj
  have hj' : j ≤ P.childCount u := by
    simp only [List.length_cons, List.length_map, List.length_range] at hj; omega
  obtain ⟨-, -, -, -, fw⟩ := (pt_pinv_ci P).2
  obtain ⟨s, hs1, hs2, hsu, hspre, hspost⟩ := fw u hu j hj' (fun h => absurd h hne)
  obtain ⟨c1, c2, c3⟩ := hCA s hs1 hs2 (by rw [hsu]; exact hty)
  obtain ⟨g1, g2⟩ := alt_getD_comp ty u (P.childCount u) j hj'
  rw [hspre] at c1 c3
  rw [hspost] at c2 c3
  simp only [List.length_cons, List.length_map, List.length_range]
  rw [g1, g2]
  exact ⟨c1, c3⟩

private theorem corner_of_latent_alt {k : ℕ} (T : TypedOrdTree k) : CornerAlt T.tree T.ty := by
  intro s hs1 hs2 hty
  obtain ⟨-, -, -, bw, -⟩ := (pt_pinv_ci T.tree).2
  have hne : T.tree.contour.getD s [] ≠ [] := by
    intro h; rw [h, T.root_out] at hty; exact absurd hty (by decide)
  obtain ⟨j, hj, hjr, hjpre, hjpost⟩ := bw s hs1 hs2
  have hmem := (pt_pinv_ci T.tree).1.2.2.1 s (by omega)
  have halt := T.latent_alt _ hmem hne hty
  obtain ⟨g1, g2⟩ := alt_getD_comp T.ty (T.tree.contour.getD s []) (T.tree.childCount (T.tree.contour.getD s [])) j hj
  have h1 := halt j (by simp only [List.length_cons, List.length_map, List.length_range]; omega)
  have h2 := halt ((j + 1) % (T.tree.childCount (T.tree.contour.getD s []) + 1))
    (by simp only [List.length_cons, List.length_map, List.length_range]
        exact Nat.mod_lt _ (by omega))
  simp only [List.length_cons, List.length_map, List.length_range] at h1 h2
  rw [g1, g2] at h1
  rw [g2] at h2
  rw [hjpre, hjpost]
  exact ⟨h1.1, h2.1, h1.2⟩

private theorem vty_vAt_lat {k : ℕ} [NeZero k] (i : ℕ) : vty (vAt k i) = VType.lat ↔ i % 2 = 1 := by
  unfold vAt
  by_cases h : i % 2 = 0
  · rw [if_pos h]
    simp only [vty]
    constructor
    · intro h'; split_ifs at h'
    · intro h'; omega
  · rw [if_neg h]
    simp only [vty]
    constructor
    · intro _; omega
    · intro _; trivial

private theorem vty_vAt_adj {k : ℕ} [NeZero k] (hk : k % 2 = 0) {s : ℕ} (hs : s % 2 = 1) (hs2 : s + 1 ≤ 2 * k) :
    vty (vAt k (s - 1)) ≠ VType.lat ∧ vty (vAt k (s + 1)) ≠ VType.lat ∧
      vty (vAt k (s - 1)) ≠ vty (vAt k (s + 1)) := by
  have hk0 := NeZero.pos k
  obtain ⟨r, rfl⟩ : ∃ r, s = 2 * r + 1 := ⟨s / 2, by omega⟩
  have hr : r < k := by omega
  have e1 : 2 * r + 1 - 1 = 2 * r := by omega
  have e2 : 2 * r + 1 + 1 = 2 * (r + 1) := by omega
  rw [e1, e2, vAt_even, vAt_even]
  simp only [vty]
  rw [Fin.val_ofNat, Fin.val_ofNat]
  have hb : (r + 1 + k - 1) % k = r := by
    rw [show r + 1 + k - 1 = r + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hr]
  rw [hb]
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · have ha : (0 + k - 1) % k = k - 1 := by
      rw [show 0 + k - 1 = k - 1 by omega]; exact Nat.mod_eq_of_lt (by omega)
    rw [ha]
    refine ⟨by split_ifs <;> simp, by split_ifs <;> simp, ?_⟩
    rw [if_pos (by omega), if_neg (by omega)]
    simp
  · have ha : (r + k - 1) % k = r - 1 := by
      rw [show r + k - 1 = (r - 1) + k by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [ha]
    refine ⟨by split_ifs <;> simp, by split_ifs <;> simp, ?_⟩
    by_cases hr2 : r % 2 = 0
    · rw [if_pos (by omega), if_neg (by omega)]; simp
    · rw [if_neg (by omega), if_pos (by omega)]; simp

/-! ### From a retained pairing to a tree -/

private theorem retained_isTree {k : ℕ} (p : TreeMatch k × TreeMatch k) (hconn : (qg p).Connected)
    (hedges : (Finset.univ.filter fun s : Fin k => s.val < (p.1.1 s).val).card +
      (Finset.univ.filter fun s : Fin k => s.val < (p.2.1 s).val).card = k)
    (hret : Nat.card (Quotient (treeSetoid p)) = k + 1) :
    (qg p).IsTree ∧ Nat.card (qg p).edgeSet = k := by
  have h1 := qg_edge_card_le p hedges
  have h2 := hconn.card_vert_le_card_edgeSet_add_one
  have h3 : Nat.card (qg p).edgeSet = k := by omega
  refine ⟨?_, h3⟩
  rw [SimpleGraph.isTree_iff_connected_and_card]
  exact ⟨hconn, by omega⟩

private theorem step_cases {k : ℕ} {i : ℕ} (hi : i < 2 * k) :
    (∃ s : Fin k, i = zi s.val) ∨ ∃ s : Fin k, i = wi s.val := by
  have hs : i / 2 < k := by omega
  by_cases h : i % 2 = (i / 2) % 2
  · left; exact ⟨⟨i / 2, hs⟩, by unfold zi; dsimp only; omega⟩
  · right; exact ⟨⟨i / 2, hs⟩, by unfold wi; dsimp only; omega⟩

private theorem phi_step_mem {k : ℕ} [NeZero k] (hk : k % 2 = 0) (p : TreeMatch k × TreeMatch k)
    {i : ℕ} (hi : i < 2 * k) : s(phi p i, phi p (i + 1)) ∈ (qg p).edgeSet := by
  rcases step_cases hi with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · rw [phi_zi, SimpleGraph.mem_edgeSet]; exact qg_adj_out hk p s
  · rw [phi_wi, SimpleGraph.mem_edgeSet]; exact qg_adj_in hk p s

private theorem zi_lt {k : ℕ} (s : Fin k) : zi s.val < 2 * k := by
  have := s.isLt; unfold zi; omega

private theorem wi_lt {k : ℕ} (s : Fin k) : wi s.val < 2 * k := by
  have := s.isLt; unfold wi; omega

private theorem zi_inj {a b : ℕ} (h : zi a = zi b) : a = b := by unfold zi at h; omega

private theorem wi_inj {a b : ℕ} (h : wi a = wi b) : a = b := by unfold wi at h; omega

private theorem retained_twice {k : ℕ} [NeZero k] (hk : k % 2 = 0) (p : TreeMatch k × TreeMatch k)
    [DecidableEq (Quotient (treeSetoid p))]
    (hconn : (qg p).Connected)
    (hedges : (Finset.univ.filter fun s : Fin k => s.val < (p.1.1 s).val).card +
      (Finset.univ.filter fun s : Fin k => s.val < (p.2.1 s).val).card = k)
    (hret : Nat.card (Quotient (treeSetoid p)) = k + 1) :
    ∀ e ∈ (qg p).edgeSet,
      ((Finset.range (2 * k)).filter fun i => s(phi p i, phi p (i + 1)) = e).card = 2 := by
  classical
  obtain ⟨-, hE⟩ := retained_isTree p hconn hedges hret
  letI : Fintype (qg p).edgeSet := Fintype.ofFinite _
  have hcardE : (qg p).edgeFinset.card = k := by
    rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]; exact hE
  -- every fibre has at least two elements
  have hge : ∀ e ∈ (qg p).edgeSet,
      2 ≤ ((Finset.range (2 * k)).filter fun i => s(phi p i, phi p (i + 1)) = e).card := by
    intro e he
    obtain ⟨s, h | h⟩ := qg_edge_cases p he
    · have hne : (p.1.1 s).val ≠ s.val := fun h' => p.1.2.2 s (Fin.ext h')
      have hcp := (compat_phi p).1 s
      rw [phi_zi, phi_zi] at hcp
      have hsub : ({zi s.val, zi (p.1.1 s).val} : Finset ℕ) ⊆
          (Finset.range (2 * k)).filter fun i => s(phi p i, phi p (i + 1)) = e := by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rw [Finset.mem_filter, Finset.mem_range]
        rcases hi with rfl | rfl
        · exact ⟨zi_lt s, by rw [phi_zi, h]⟩
        · exact ⟨zi_lt _, by rw [phi_zi, hcp, h]⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_pair (a := zi s.val) (b := zi (p.1.1 s).val) (fun h' => hne (zi_inj h').symm)] at this
      exact this
    · have hne : (p.2.1 s).val ≠ s.val := fun h' => p.2.2.2 s (Fin.ext h')
      have hcp := (compat_phi p).2 s
      rw [phi_wi, phi_wi] at hcp
      have hsub : ({wi s.val, wi (p.2.1 s).val} : Finset ℕ) ⊆
          (Finset.range (2 * k)).filter fun i => s(phi p i, phi p (i + 1)) = e := by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rw [Finset.mem_filter, Finset.mem_range]
        rcases hi with rfl | rfl
        · exact ⟨wi_lt s, by rw [phi_wi, h]⟩
        · exact ⟨wi_lt _, by rw [phi_wi, hcp, h]⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_pair (a := wi s.val) (b := wi (p.2.1 s).val) (fun h' => hne (wi_inj h').symm)] at this
      exact this
  -- the fibres add up to `2k`
  have hsum : ∑ e ∈ (qg p).edgeFinset,
      ((Finset.range (2 * k)).filter fun i => s(phi p i, phi p (i + 1)) = e).card = 2 * k := by
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.range (2 * k)) (t := (qg p).edgeFinset)
      (f := fun i => s(phi p i, phi p (i + 1)))
      (fun i hi => by
        simp only [Finset.mem_coe, SimpleGraph.mem_edgeFinset]
        exact phi_step_mem hk p (Finset.mem_range.mp (Finset.mem_coe.mp hi)))
    rw [Finset.card_range] at this
    exact this.symm
  have hsum2 : ∑ e ∈ (qg p).edgeFinset, 2 = 2 * k := by
    rw [Finset.sum_const, hcardE, smul_eq_mul, mul_comm]
  have key := (Finset.sum_eq_sum_iff_of_le (s := (qg p).edgeFinset) (f := fun _ => 2)
    (g := fun e => ((Finset.range (2 * k)).filter fun i => s(phi p i, phi p (i + 1)) = e).card)
    (fun e he => hge e (SimpleGraph.mem_edgeFinset.mp he))).mp (hsum2.trans hsum.symm)
  intro e he
  exact (key e (SimpleGraph.mem_edgeFinset.mpr he)).symm

private theorem qg_adj_type {k : ℕ} (hk : k % 2 = 0) (p : TreeMatch k × TreeMatch k)
    {x y : Quotient (treeSetoid p)} (h : (qg p).Adj x y) :
    (ctype hk p x = VType.lat ↔ ¬ ctype hk p y = VType.lat) := by
  unfold qg at h
  rw [SimpleGraph.fromRel_adj] at h
  obtain ⟨_, ⟨s, h1 | h1⟩ | ⟨s, h1 | h1⟩⟩ := h
  · obtain ⟨rfl, rfl⟩ := h1
    simp only [ctype_mk, vty]; split_ifs <;> simp
  · obtain ⟨rfl, rfl⟩ := h1
    simp only [ctype_mk, vty]; split_ifs <;> simp
  · obtain ⟨rfl, rfl⟩ := h1
    simp only [ctype_mk, vty]; split_ifs <;> simp
  · obtain ⟨rfl, rfl⟩ := h1
    simp only [ctype_mk, vty]; split_ifs <;> simp

private theorem phi_closed {k : ℕ} [NeZero k] (p : TreeMatch k × TreeMatch k) : phi p (2 * k) = phi p 0 := by
  unfold phi
  congr 1
  have h1 : vAt k (2 * k) = vAt k (2 * k) := rfl
  rw [show 2 * k = 2 * k from rfl, vAt_even, show (0 : ℕ) = 2 * 0 from rfl, vAt_even]
  congr 1
  apply Fin.ext
  rw [Fin.val_ofNat, Fin.val_ofNat]
  have := NeZero.pos k
  rw [show k + k - 1 = (k - 1) + k by omega, Nat.add_mod_right, show 0 + k - 1 = k - 1 by omega]

private theorem retained_tree {k : ℕ} [NeZero k] (hk : k % 2 = 0) (p : TreeMatch k × TreeMatch k)
    (hconn : (qg p).Connected)
    (hedges : (Finset.univ.filter fun s : Fin k => s.val < (p.1.1 s).val).card +
      (Finset.univ.filter fun s : Fin k => s.val < (p.2.1 s).val).card = k)
    (hret : Nat.card (Quotient (treeSetoid p)) = k + 1) :
    ∃ T : TypedOrdTree k, Compat (fun i => T.tree.contour.getD i []) p := by
  classical
  obtain ⟨hT, hE⟩ := retained_isTree p hconn hedges hret
  have hstep : ∀ i < 2 * k, (qg p).Adj (phi p i) (phi p (i + 1)) :=
    fun i hi => (SimpleGraph.mem_edgeSet _).mp (phi_step_mem hk p hi)
  obtain ⟨P, ψ, hinj, hsurj, hroot, hadj, hord, hW⟩ :=
    lem_app_vol_closed_contour (qg p) hT k hE (phi p) hstep (phi_closed p)
      (retained_twice hk p hconn hedges hret)
  haveI : Fintype (Quotient (treeSetoid p)) := Fintype.ofFinite _
  have hvl : P.vtxs.length = k + 1 := by
    have h1 : P.vtxs.toFinset.card = (Finset.univ : Finset (Quotient (treeSetoid p))).card :=
      Finset.card_bij (fun u _ => ψ u) (fun _ _ => Finset.mem_univ _)
        (fun a ha b hb hab => hinj a (List.mem_toFinset.mp ha) b (List.mem_toFinset.mp hb) hab)
        (fun x _ => by
          obtain ⟨u, hu, hux⟩ := hsurj x
          exact ⟨u, List.mem_toFinset.mpr hu, hux⟩)
    rw [List.toFinset_card_of_nodup (pt_nodup P), Finset.card_univ, ← Nat.card_eq_fintype_card,
      hret] at h1
    exact h1
  have hlenC : P.contour.length = 2 * k + 1 := by
    have := pt_contour_len P
    omega
  obtain ⟨hPI, -⟩ := pt_pinv_ci P
  have hLeq : P.contour.length - 1 = 2 * k := by omega
  rw [hLeq] at hPI
  have hmemC : ∀ i ≤ 2 * k, P.contour.getD i [] ∈ P.vtxs := hPI.2.2.1
  -- the typing
  let ty : List ℕ → VType := fun u => if u ∈ P.vtxs then ctype hk p (ψ u) else VType.out
  have hty : ∀ i ≤ 2 * k, ty (P.contour.getD i []) = vty (vAt k i) := by
    intro i hi
    show (if P.contour.getD i [] ∈ P.vtxs then _ else _) = _
    rw [if_pos (hmemC i hi), ← hW i hi]
    rfl
  have hCA : CornerAlt P ty := by
    intro s hs1 hs2 hl
    rw [hLeq] at hs2
    rw [hty s (by omega)] at hl
    have hodd : s % 2 = 1 := (vty_vAt_lat s).mp hl
    rw [hty (s - 1) (by omega), hty (s + 1) (by omega)]
    exact vty_vAt_adj hk hodd hs2
  refine ⟨⟨P, ty, hvl, fun u hu => if_neg hu, ?_, ?_, latent_alt_of_corner P ty hCA⟩, ?_⟩
  · -- root type
    have h0 := hty 0 (by omega)
    rw [contour_getD_zero] at h0
    rw [h0]
    show vty (vAt k 0) = VType.out
    have hk0 := NeZero.pos k
    rw [show (0 : ℕ) = 2 * 0 from rfl, vAt_even]
    simp only [vty]
    have : (Fin.ofNat k (0 + k - 1)).val % 2 = 1 := by
      rw [Fin.val_ofNat, show 0 + k - 1 = k - 1 by omega, Nat.mod_eq_of_lt (show k - 1 < k by omega)]
      omega
    rw [if_pos this]
  · -- edges join latent and external vertices
    intro u hu v hv hvne hvu
    have hA := (hadj u hu v hv).mpr (Or.inl ⟨hvne, hvu⟩)
    have := qg_adj_type hk p hA
    show (if u ∈ P.vtxs then _ else _) = VType.lat ↔ ¬ (if v ∈ P.vtxs then _ else _) = VType.lat
    rw [if_pos hu, if_pos hv]
    exact this
  · -- the pairing matches the contour
    have hsym : ∀ a b : ℕ, a + 1 ≤ 2 * k → b + 1 ≤ 2 * k →
        s(phi p a, phi p (a + 1)) = s(phi p b, phi p (b + 1)) →
        s(P.contour.getD a [], P.contour.getD (a + 1) []) =
          s(P.contour.getD b [], P.contour.getD (b + 1) []) := by
      intro a b ha hb h
      rw [hW a (by omega), hW (a + 1) (by omega), hW b (by omega), hW (b + 1) (by omega)] at h
      have ma := hmemC a (by omega)
      have ma1 := hmemC (a + 1) (by omega)
      have mb := hmemC b (by omega)
      have mb1 := hmemC (b + 1) (by omega)
      rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hinj _ ma _ mb h1, hinj _ ma1 _ mb1 h2]
      · rw [hinj _ ma _ mb1 h1, hinj _ ma1 _ mb h2, Sym2.eq_swap]
    obtain ⟨c1, c2⟩ := compat_phi p
    constructor
    · intro s
      have := hsym _ _ (by have := zi_lt (p.1.1 s); omega) (by have := zi_lt s; omega) (c1 s)
      exact this
    · intro s
      have := hsym _ _ (by have := wi_lt (p.2.1 s); omega) (by have := wi_lt s; omega) (c2 s)
      exact this

/-! ## From a typed ordered tree to a pairing -/

private theorem tt_len {k : ℕ} (T : TypedOrdTree k) : T.tree.contour.length = 2 * k + 1 := by
  have := pt_contour_len T.tree
  have := T.card_vtx
  omega

private theorem tt_pinv {k : ℕ} (T : TypedOrdTree k) : PInv (2 * k) T.tree := by
  have := (pt_pinv_ci T.tree).1
  rwa [show T.tree.contour.length - 1 = 2 * k by have := tt_len T; omega] at this

private theorem tt_mem {k : ℕ} (T : TypedOrdTree k) {j : ℕ} (hj : j ≤ 2 * k) :
    T.tree.contour.getD j [] ∈ T.tree.vtxs := (tt_pinv T).2.2.1 j hj

private theorem tt_cover {k : ℕ} (T : TypedOrdTree k) {u : List ℕ} (hu : u ∈ T.tree.vtxs) :
    ∃ j ≤ 2 * k, T.tree.contour.getD j [] = u := (tt_pinv T).2.2.2.1 u hu

private theorem tt_zero {k : ℕ} (T : TypedOrdTree k) : T.tree.contour.getD 0 [] = [] :=
  contour_getD_zero _

private theorem tt_last {k : ℕ} (T : TypedOrdTree k) : T.tree.contour.getD (2 * k) [] = [] :=
  (tt_pinv T).2.1

private theorem tt_pc {k : ℕ} (T : TypedOrdTree k) {i : ℕ} (hi : i < 2 * k) :
    PC (T.tree.contour.getD i []) (T.tree.contour.getD (i + 1) []) :=
  (tt_pinv T).2.2.2.2.1 i hi

private theorem tt_adj_lat {k : ℕ} (T : TypedOrdTree k) {i : ℕ} (hi : i < 2 * k) :
    T.ty (T.tree.contour.getD i []) = VType.lat ↔ ¬ T.ty (T.tree.contour.getD (i + 1) []) = VType.lat := by
  rcases tt_pc T hi with ⟨hne, hdl⟩ | ⟨hne, hdl⟩
  · exact T.edge_joins _ (tt_mem T (by omega)) _ (tt_mem T (by omega)) hne hdl
  · have := T.edge_joins _ (tt_mem T (by omega)) _ (tt_mem T (by omega)) hne hdl
    tauto

private theorem vtype_cases (a b : VType) (ha : a ≠ VType.lat) (hb : b ≠ VType.lat) (hab : a ≠ b) :
    (a = VType.out ∧ b = VType.inp) ∨ (a = VType.inp ∧ b = VType.out) := by
  cases a <;> cases b <;> simp_all

/-- The type pattern along the contour: odd positions are latent, even positions alternate
`o, in, o, in, …` starting with `o`. -/
private theorem tt_ty {k : ℕ} (T : TypedOrdTree k) :
    ∀ j ≤ 2 * k, (j % 2 = 1 → T.ty (T.tree.contour.getD j []) = VType.lat) ∧
      (j % 2 = 0 → T.ty (T.tree.contour.getD j []) = if j % 4 = 0 then VType.out else VType.inp) := by
  have hCA := corner_of_latent_alt T
  have hlen := tt_len T
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
      rw [tt_zero, T.root_out]
      simp
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hj' := ih j' (by omega) (by omega)
      have hadj := tt_adj_lat T (show j' < 2 * k by omega)
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
        rcases vtype_cases _ _ c1 c2 c3 with ⟨a1, a2⟩ | ⟨a1, a2⟩
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

private abbrev cE (C : List (List ℕ)) (i : ℕ) : Sym2 (List ℕ) := s(C.getD i [], C.getD (i + 1) [])

private def lab (C : List (List ℕ)) (i : ℕ) : List ℕ × Bool :=
  if C.getD (i + 1) [] ≠ [] ∧ (C.getD (i + 1) []).dropLast = C.getD i [] then (C.getD (i + 1) [], true)
  else (C.getD i [], false)

private theorem sym2_parent_inj {v w : List ℕ} (hv : v ≠ []) (hw : w ≠ [])
    (h : s(v, v.dropLast) = s(w, w.dropLast)) : v = w := by
  rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact h1
  · exfalso
    have a1 := congrArg List.length h1
    have a2 := congrArg List.length h2
    rw [List.length_dropLast] at a1 a2
    have := List.length_pos_iff.mpr hv
    have := List.length_pos_iff.mpr hw
    omega

private theorem lab_edge {k : ℕ} (T : TypedOrdTree k) {i : ℕ} (hi : i < 2 * k) :
    (lab T.tree.contour i).1 ≠ [] ∧
      cE T.tree.contour i = s((lab T.tree.contour i).1, (lab T.tree.contour i).1.dropLast) := by
  unfold lab
  by_cases h : T.tree.contour.getD (i + 1) [] ≠ [] ∧
      (T.tree.contour.getD (i + 1) []).dropLast = T.tree.contour.getD i []
  · rw [if_pos h]
    refine ⟨h.1, ?_⟩
    show s(_, _) = s(_, _)
    rw [h.2, Sym2.eq_swap]
  · rw [if_neg h]
    rcases tt_pc T hi with h1 | ⟨h1, h2⟩
    · exact absurd h1 h
    · refine ⟨h1, ?_⟩
      show s(_, _) = s(_, _)
      rw [h2]

private theorem lab_mem {k : ℕ} (T : TypedOrdTree k) {i : ℕ} (hi : i < 2 * k) :
    (lab T.tree.contour i).1 ∈ T.tree.vtxs := by
  unfold lab
  split_ifs
  · exact tt_mem T (by omega)
  · exact tt_mem T (by omega)

private theorem lab_surj {k : ℕ} (T : TypedOrdTree k) {v : List ℕ} (hv : v ∈ T.tree.vtxs) (hne : v ≠ [])
    (b : Bool) : ∃ i < 2 * k, lab T.tree.contour i = (v, b) := by
  cases b
  · obtain ⟨-, -, -, -, fw⟩ := (pt_pinv_ci T.tree).2
    obtain ⟨s, hs1, hs2, hsu, -, hspost⟩ := fw v hv (T.tree.childCount v) le_rfl (fun h => absurd h hne)
    have hL := tt_len T
    refine ⟨s, by omega, ?_⟩
    rw [cpost_self] at hspost
    unfold lab
    rw [if_neg, hsu]
    rintro ⟨_, h2⟩
    rw [hspost, hsu] at h2
    have := congrArg List.length h2
    rw [List.length_dropLast, List.length_dropLast] at this
    have := List.length_pos_iff.mpr hne
    omega
  · obtain ⟨s, hs, hs1, hs2⟩ := (tt_pinv T).2.2.2.2.2.1 v hv hne
    refine ⟨s, by omega, ?_⟩
    unfold lab
    rw [if_pos ⟨by rw [hs2]; exact hne, by rw [hs2, hs1]⟩, hs2]

private theorem tt_mult {k : ℕ} (T : TypedOrdTree k) :
    (∀ i < 2 * k, ∃ i' < 2 * k, i' ≠ i ∧ cE T.tree.contour i' = cE T.tree.contour i) ∧
    (∀ i < 2 * k, ∀ i' < 2 * k, ∀ i'' < 2 * k, cE T.tree.contour i' = cE T.tree.contour i →
      cE T.tree.contour i'' = cE T.tree.contour i → i' = i'' ∨ i' = i ∨ i'' = i) := by
  classical
  let NR : Finset (List ℕ) := T.tree.vtxs.toFinset.erase []
  have hNR : NR.card = k := by
    have := Finset.card_erase_of_mem (s := T.tree.vtxs.toFinset) (a := []) (by
      rw [List.mem_toFinset]; exact pt_root_mem _)
    rw [List.toFinset_card_of_nodup (pt_nodup T.tree), T.card_vtx] at this
    simpa [NR] using this
  let Tg : Finset (List ℕ × Bool) := NR ×ˢ (Finset.univ : Finset Bool)
  have hTg : Tg.card = 2 * k := by
    simp [Tg, Finset.card_product, hNR]; ring
  have hmaps : Set.MapsTo (lab T.tree.contour) (↑(Finset.range (2 * k))) (↑Tg) := by
    intro i hi
    have hi' := Finset.mem_range.mp (Finset.mem_coe.mp hi)
    simp only [Finset.mem_coe, Tg, NR, Finset.mem_product, Finset.mem_erase, List.mem_toFinset,
      Finset.mem_univ, and_true]
    exact ⟨(lab_edge T hi').1, lab_mem T hi'⟩
  have hsurj : Set.SurjOn (lab T.tree.contour) (↑(Finset.range (2 * k))) (↑Tg) := by
    intro x hx
    have hx' := Finset.mem_coe.mp hx
    simp only [Tg, NR, Finset.mem_product, Finset.mem_erase, List.mem_toFinset, Finset.mem_univ,
      and_true] at hx'
    obtain ⟨i, hi, he⟩ := lab_surj T hx'.2 hx'.1 x.2
    exact ⟨i, Finset.mem_coe.mpr (Finset.mem_range.mpr hi), by rw [he]⟩
  have hinj := Finset.injOn_of_surjOn_of_card_le (lab T.tree.contour) hmaps hsurj
    (by rw [Finset.card_range, hTg])
  constructor
  · intro i hi
    obtain ⟨hne, hE⟩ := lab_edge T hi
    obtain ⟨i', hi', he⟩ := lab_surj T (lab_mem T hi) hne (!(lab T.tree.contour i).2)
    refine ⟨i', hi', ?_, ?_⟩
    · intro h
      subst h
      have h3 := congrArg Prod.snd he
      cases hb : (lab T.tree.contour i').2 <;> simp [hb] at h3
    · rw [hE, (lab_edge T hi').2, he]
  · intro i hi i' hi' i'' hi'' h1 h2
    obtain ⟨hne, hE⟩ := lab_edge T hi
    obtain ⟨hne', hE'⟩ := lab_edge T hi'
    obtain ⟨hne'', hE''⟩ := lab_edge T hi''
    have e1 : (lab T.tree.contour i').1 = (lab T.tree.contour i).1 :=
      sym2_parent_inj hne' hne (by rw [← hE', ← hE]; exact h1)
    have e2 : (lab T.tree.contour i'').1 = (lab T.tree.contour i).1 :=
      sym2_parent_inj hne'' hne (by rw [← hE'', ← hE]; exact h2)
    have hI : ∀ a b, a < 2 * k → b < 2 * k → lab T.tree.contour a = lab T.tree.contour b → a = b :=
      fun a b ha hb h => hinj (Finset.mem_coe.mpr (Finset.mem_range.mpr ha))
        (Finset.mem_coe.mpr (Finset.mem_range.mpr hb)) h
    have key : lab T.tree.contour i' = lab T.tree.contour i'' ∨ lab T.tree.contour i' = lab T.tree.contour i ∨
        lab T.tree.contour i'' = lab T.tree.contour i := by
      have p1 : lab T.tree.contour i' = ((lab T.tree.contour i).1, (lab T.tree.contour i').2) :=
        Prod.ext e1 rfl
      have p2 : lab T.tree.contour i'' = ((lab T.tree.contour i).1, (lab T.tree.contour i'').2) :=
        Prod.ext e2 rfl
      have p3 : lab T.tree.contour i = ((lab T.tree.contour i).1, (lab T.tree.contour i).2) := rfl
      rw [p1, p2]
      conv => rhs; rw [p3]
      cases (lab T.tree.contour i').2 <;> cases (lab T.tree.contour i'').2 <;>
        cases (lab T.tree.contour i).2 <;> simp
    rcases key with h | h | h
    · exact Or.inl (hI _ _ hi' hi'' h)
    · exact Or.inr (Or.inl (hI _ _ hi' hi h))
    · exact Or.inr (Or.inr (hI _ _ hi'' hi h))

private theorem tt_lat {k : ℕ} (T : TypedOrdTree k) {j : ℕ} (hj : j ≤ 2 * k) :
    T.ty (T.tree.contour.getD j []) = VType.lat ↔ j % 2 = 1 := by
  obtain ⟨h1, h2⟩ := tt_ty T j hj
  constructor
  · intro h
    by_contra hh
    rw [h2 (by omega)] at h
    split_ifs at h
  · exact h1

private theorem tt_par_eq {k : ℕ} (T : TypedOrdTree k) {j j' : ℕ} (hj : j ≤ 2 * k) (hj' : j' ≤ 2 * k)
    (h : T.tree.contour.getD j [] = T.tree.contour.getD j' []) : j % 2 = j' % 2 := by
  have a := tt_lat T hj
  have b := tt_lat T hj'
  rw [h] at a
  have c := a.symm.trans b
  omega

/-- The two endpoints of the step `i`: the external one sits at an even position, the latent one at an
odd position. -/
private theorem tt_E_pos {k : ℕ} (T : TypedOrdTree k) {i i' : ℕ} (hi : i < 2 * k) (hi' : i' < 2 * k)
    (h : cE T.tree.contour i = cE T.tree.contour i') :
    T.tree.contour.getD (i + i % 2) [] = T.tree.contour.getD (i' + i' % 2) [] ∧
    T.tree.contour.getD (i + (i + 1) % 2) [] = T.tree.contour.getD (i' + (i' + 1) % 2) [] := by
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hp := tt_par_eq T (by omega) (by omega) h1
    rcases Nat.mod_two_eq_zero_or_one i with a | a <;> rcases Nat.mod_two_eq_zero_or_one i' with b | b
    · rw [a, b]; simp only [Nat.add_zero]; rw [show (i + 1) % 2 = 1 by omega, show (i' + 1) % 2 = 1 by omega]
      exact ⟨h1, h2⟩
    · omega
    · omega
    · rw [a, b, show (i + 1) % 2 = 0 by omega, show (i' + 1) % 2 = 0 by omega]
      simp only [Nat.add_zero]
      exact ⟨h2, h1⟩
  · have hp := tt_par_eq T (by omega) (by omega) h1
    rcases Nat.mod_two_eq_zero_or_one i with a | a <;> rcases Nat.mod_two_eq_zero_or_one i' with b | b
    · omega
    · rw [a, b, show (i + 1) % 2 = 1 by omega, show (i' + 1) % 2 = 0 by omega]
      simp only [Nat.add_zero]
      exact ⟨h1, h2⟩
    · rw [a, b, show (i + 1) % 2 = 0 by omega, show (i' + 1) % 2 = 1 by omega]
      simp only [Nat.add_zero]
      exact ⟨h2, h1⟩
    · omega

private theorem tt_Z_cons {k : ℕ} (T : TypedOrdTree k) {i i' : ℕ} (hi : i < 2 * k) (hi' : i' < 2 * k)
    (h : cE T.tree.contour i = cE T.tree.contour i') :
    (i % 4 = 0 ∨ i % 4 = 3) ↔ (i' % 4 = 0 ∨ i' % 4 = 3) := by
  obtain ⟨h1, -⟩ := tt_E_pos T hi hi' h
  have e1 := (tt_ty T (i + i % 2) (by omega)).2 (by omega)
  have e2 := (tt_ty T (i' + i' % 2) (by omega)).2 (by omega)
  rw [h1, e2] at e1
  by_cases ha : (i + i % 2) % 4 = 0 <;> by_cases hb : (i' + i' % 2) % 4 = 0 <;>
    simp only [ha, hb, if_true, if_false] at e1 <;> first | omega | exact absurd e1 (by decide)

private theorem zi_of_Z {i : ℕ} (h : i % 4 = 0 ∨ i % 4 = 3) : zi (i / 2) = i := by
  unfold zi; omega

private theorem wi_of_notZ {i : ℕ} (h : ¬ (i % 4 = 0 ∨ i % 4 = 3)) : wi (i / 2) = i := by
  unfold wi; omega

private theorem zi_Z (s : ℕ) : zi s % 4 = 0 ∨ zi s % 4 = 3 := by
  unfold zi
  rcases Nat.mod_two_eq_zero_or_one s with h | h <;> rw [h] <;> omega

private theorem wi_notZ (s : ℕ) : ¬ (wi s % 4 = 0 ∨ wi s % 4 = 3) := by
  unfold wi
  rcases Nat.mod_two_eq_zero_or_one s with h | h <;> [rw [show (s + 1) % 2 = 1 by omega]; rw [show (s + 1) % 2 = 0 by omega]] <;> omega

private theorem exists_match {k : ℕ} {X : Type} (g : Fin k → X)
    (hex : ∀ s, ∃ s', s' ≠ s ∧ g s' = g s)
    (huniq : ∀ s s' s'', s' ≠ s → g s' = g s → s'' ≠ s → g s'' = g s → s' = s'') :
    ∃ σ : TreeMatch k, ∀ s, g (σ.1 s) = g s := by
  classical
  let π : Fin k → Fin k := fun s => Classical.choose (hex s)
  have hπ : ∀ s, π s ≠ s ∧ g (π s) = g s := fun s => Classical.choose_spec (hex s)
  have hinv : ∀ s, π (π s) = s := by
    intro s
    apply huniq (π s) (π (π s)) s (hπ (π s)).1 (hπ (π s)).2 (hπ s).1.symm
    rw [(hπ s).2]
  refine ⟨⟨(Function.Involutive.toPerm π hinv), ?_, ?_⟩, ?_⟩
  · intro x; exact hinv x
  · intro x; exact (hπ x).1
  · intro s; exact (hπ s).2

private theorem match_unique {k : ℕ} {X : Type} (g : Fin k → X)
    (huniq : ∀ s s' s'', s' ≠ s → g s' = g s → s'' ≠ s → g s'' = g s → s' = s'')
    (σ σ' : TreeMatch k) (h : ∀ s, g (σ.1 s) = g s) (h' : ∀ s, g (σ'.1 s) = g s) : σ = σ' := by
  apply Subtype.ext
  apply Equiv.ext
  intro s
  exact huniq s _ _ (σ.2.2 s) (h s) (σ'.2.2 s) (h' s)

private theorem tt_z_hyps {k : ℕ} (T : TypedOrdTree k) :
    (∀ s : Fin k, ∃ s' : Fin k, s' ≠ s ∧ cE T.tree.contour (zi s'.val) = cE T.tree.contour (zi s.val)) ∧
    (∀ s s' s'' : Fin k, s' ≠ s → cE T.tree.contour (zi s'.val) = cE T.tree.contour (zi s.val) →
      s'' ≠ s → cE T.tree.contour (zi s''.val) = cE T.tree.contour (zi s.val) → s' = s'') := by
  obtain ⟨hM1, hM2⟩ := tt_mult T
  constructor
  · intro s
    obtain ⟨i', hi', hne, hE⟩ := hM1 (zi s.val) (zi_lt s)
    have hZ := (tt_Z_cons T hi' (zi_lt s) hE).mpr (zi_Z _)
    refine ⟨⟨i' / 2, by omega⟩, ?_, ?_⟩
    · intro h
      apply hne
      have := congrArg Fin.val h
      simp only at this
      rw [← zi_of_Z hZ, this]
    · show cE T.tree.contour (zi (i' / 2)) = _
      rw [zi_of_Z hZ]; exact hE
  · intro s s' s'' h1 h2 h3 h4
    rcases hM2 (zi s.val) (zi_lt s) _ (zi_lt s') _ (zi_lt s'') h2 h4 with h | h | h
    · exact Fin.ext (zi_inj h)
    · exact absurd (Fin.ext (zi_inj h)) h1
    · exact absurd (Fin.ext (zi_inj h)) h3

private theorem tt_w_hyps {k : ℕ} (T : TypedOrdTree k) :
    (∀ s : Fin k, ∃ s' : Fin k, s' ≠ s ∧ cE T.tree.contour (wi s'.val) = cE T.tree.contour (wi s.val)) ∧
    (∀ s s' s'' : Fin k, s' ≠ s → cE T.tree.contour (wi s'.val) = cE T.tree.contour (wi s.val) →
      s'' ≠ s → cE T.tree.contour (wi s''.val) = cE T.tree.contour (wi s.val) → s' = s'') := by
  obtain ⟨hM1, hM2⟩ := tt_mult T
  constructor
  · intro s
    obtain ⟨i', hi', hne, hE⟩ := hM1 (wi s.val) (wi_lt s)
    have hZ : ¬ (i' % 4 = 0 ∨ i' % 4 = 3) := fun h =>
      wi_notZ s.val ((tt_Z_cons T hi' (wi_lt s) hE).mp h)
    refine ⟨⟨i' / 2, by omega⟩, ?_, ?_⟩
    · intro h
      apply hne
      have := congrArg Fin.val h
      simp only at this
      rw [← wi_of_notZ hZ, this]
    · show cE T.tree.contour (wi (i' / 2)) = _
      rw [wi_of_notZ hZ]; exact hE
  · intro s s' s'' h1 h2 h3 h4
    rcases hM2 (wi s.val) (wi_lt s) _ (wi_lt s') _ (wi_lt s'') h2 h4 with h | h | h
    · exact Fin.ext (wi_inj h)
    · exact absurd (Fin.ext (wi_inj h)) h1
    · exact absurd (Fin.ext (wi_inj h)) h3

private theorem tt_exists_pair {k : ℕ} (T : TypedOrdTree k) :
    ∃ p : TreeMatch k × TreeMatch k, Compat (fun i => T.tree.contour.getD i []) p := by
  obtain ⟨σ, hσ⟩ := exists_match (fun s : Fin k => cE T.tree.contour (zi s.val)) (tt_z_hyps T).1
    (tt_z_hyps T).2
  obtain ⟨σ', hσ'⟩ := exists_match (fun s : Fin k => cE T.tree.contour (wi s.val)) (tt_w_hyps T).1
    (tt_w_hyps T).2
  exact ⟨(σ, σ'), hσ, hσ'⟩

private theorem tt_pair_unique {k : ℕ} (T : TypedOrdTree k) (p p' : TreeMatch k × TreeMatch k)
    (h : Compat (fun i => T.tree.contour.getD i []) p)
    (h' : Compat (fun i => T.tree.contour.getD i []) p') : p = p' := by
  have e1 := match_unique (fun s : Fin k => cE T.tree.contour (zi s.val)) (tt_z_hyps T).2 p.1 p'.1
    h.1 h'.1
  have e2 := match_unique (fun s : Fin k => cE T.tree.contour (wi s.val)) (tt_w_hyps T).2 p.2 p'.2
    h.2 h'.2
  exact Prod.ext e1 e2

private theorem vAt_two_k {k : ℕ} [NeZero k] : vAt k (2 * k) = vAt k 0 := by
  rw [vAt_even, show (0 : ℕ) = 2 * 0 from rfl, vAt_even]
  congr 1
  apply Fin.ext
  rw [Fin.val_ofNat, Fin.val_ofNat]
  have := NeZero.pos k
  rw [show k + k - 1 = (k - 1) + k by omega, Nat.add_mod_right, show 0 + k - 1 = k - 1 by omega]

private theorem treePos_vAt_le {k : ℕ} [NeZero k] {j : ℕ} (hj : j ≤ 2 * k) :
    treePos (vAt k j) = j % (2 * k) := by
  have hk0 := NeZero.pos k
  rcases Nat.lt_or_ge j (2 * k) with h | h
  · rw [treePos_vAt h, Nat.mod_eq_of_lt h]
  · have : j = 2 * k := by omega
    subst this
    rw [vAt_two_k, treePos_vAt (by omega), Nat.mod_self]

private theorem tt_mod {k : ℕ} (T : TypedOrdTree k) {j : ℕ} (hj : j ≤ 2 * k) :
    T.tree.contour.getD (j % (2 * k)) [] = T.tree.contour.getD j [] := by
  rcases Nat.lt_or_ge j (2 * k) with h | h
  · rw [Nat.mod_eq_of_lt h]
  · have : j = 2 * k := by omega
    subst this
    rw [Nat.mod_self, tt_zero, tt_last]

private theorem zi_pos_lat (s : ℕ) : zi s + (zi s + 1) % 2 = 2 * s + 1 := by
  unfold zi
  rcases Nat.mod_two_eq_zero_or_one s with h | h <;> rw [h] <;> omega

private theorem wi_pos_lat (s : ℕ) : wi s + (wi s + 1) % 2 = 2 * s + 1 := by
  unfold wi
  rcases Nat.mod_two_eq_zero_or_one s with h | h
  · rw [show (s + 1) % 2 = 1 by omega]; omega
  · rw [show (s + 1) % 2 = 0 by omega]; omega

private theorem treePos_outV {k : ℕ} [NeZero k] (s : Fin k) :
    treePos (Sum.inl (treeOutV s) : TreeVtx k) = (zi s.val + zi s.val % 2) % (2 * k) := by
  have hs := s.isLt
  have hz : zi s.val ≤ 2 * k := by have := zi_lt s; omega
  have hv : vAt k (zi s.val + zi s.val % 2) = Sum.inl (treeOutV s) := by
    rcases Nat.mod_two_eq_zero_or_one s.val with h | h
    · have : zi s.val % 2 = 0 := by unfold zi; omega
      rw [this, Nat.add_zero]
      exact ((stepZ s).1 h).1
    · have : zi s.val % 2 = 1 := by unfold zi; omega
      rw [this]
      exact ((stepZ s).2 h).2
  rw [← hv]
  exact treePos_vAt_le (by rcases Nat.mod_two_eq_zero_or_one s.val with h | h <;> unfold zi <;> omega)

private theorem treePos_inV {k : ℕ} [NeZero k] (s : Fin k) :
    treePos (Sum.inl (treeInV s) : TreeVtx k) = (wi s.val + wi s.val % 2) % (2 * k) := by
  have hs := s.isLt
  have hv : vAt k (wi s.val + wi s.val % 2) = Sum.inl (treeInV s) := by
    rcases Nat.mod_two_eq_zero_or_one s.val with h | h
    · have : wi s.val % 2 = 1 := by unfold wi; omega
      rw [this]
      exact ((stepW s).1 h).2
    · have : wi s.val % 2 = 0 := by unfold wi; omega
      rw [this, Nat.add_zero]
      exact ((stepW s).2 h).1
  rw [← hv]
  exact treePos_vAt_le (by rcases Nat.mod_two_eq_zero_or_one s.val with h | h <;> unfold wi <;> omega)

private theorem tt_fibre_rel {k : ℕ} [NeZero k] (T : TypedOrdTree k) (p : TreeMatch k × TreeMatch k)
    (hc : Compat (fun i => T.tree.contour.getD i []) p) {x y : TreeVtx k} (h : treeRel p x y) :
    T.tree.contour.getD (treePos x) [] = T.tree.contour.getD (treePos y) [] := by
  obtain ⟨s, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
  · -- z-edge, latent endpoints
    obtain ⟨-, h2⟩ := tt_E_pos T (zi_lt (p.1.1 s)) (zi_lt s) (hc.1 s)
    rw [zi_pos_lat, zi_pos_lat] at h2
    exact h2.symm
  · obtain ⟨-, h2⟩ := tt_E_pos T (wi_lt (p.2.1 s)) (wi_lt s) (hc.2 s)
    rw [wi_pos_lat, wi_pos_lat] at h2
    exact h2.symm
  · obtain ⟨h1, -⟩ := tt_E_pos T (zi_lt s) (zi_lt (p.1.1 s)) (hc.1 s).symm
    rw [treePos_outV, treePos_outV, tt_mod T (by have := zi_lt s; unfold zi at *; omega),
      tt_mod T (by have := zi_lt (p.1.1 s); unfold zi at *; omega)]
    exact h1
  · obtain ⟨h1, -⟩ := tt_E_pos T (wi_lt s) (wi_lt (p.2.1 s)) (hc.2 s).symm
    rw [treePos_inV, treePos_inV, tt_mod T (by have := wi_lt s; unfold wi at *; omega),
      tt_mod T (by have := wi_lt (p.2.1 s); unfold wi at *; omega)]
    exact h1

private theorem tt_fibre_resp {k : ℕ} [NeZero k] (T : TypedOrdTree k) (p : TreeMatch k × TreeMatch k)
    (hc : Compat (fun i => T.tree.contour.getD i []) p) {x y : TreeVtx k} (h : treeSetoid p x y) :
    T.tree.contour.getD (treePos x) [] = T.tree.contour.getD (treePos y) [] := by
  change Relation.EqvGen (treeRel p) x y at h
  induction h with
  | rel x y hxy => exact tt_fibre_rel T p hc hxy
  | refl => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- The class map of a pairing compatible with the contour of `T`. -/
private def ccls {k : ℕ} [NeZero k] (T : TypedOrdTree k) (p : TreeMatch k × TreeMatch k)
    (hc : Compat (fun i => T.tree.contour.getD i []) p) : Quotient (treeSetoid p) → List ℕ :=
  Quotient.lift (fun x => T.tree.contour.getD (treePos x) []) (fun _ _ h => tt_fibre_resp T p hc h)

private theorem ccls_mk {k : ℕ} [NeZero k] (T : TypedOrdTree k) (p : TreeMatch k × TreeMatch k)
    (hc : Compat (fun i => T.tree.contour.getD i []) p) (x : TreeVtx k) :
    ccls T p hc (treeMk p x) = T.tree.contour.getD (treePos x) [] := rfl

private theorem ccls_mem {k : ℕ} [NeZero k] (T : TypedOrdTree k) (p : TreeMatch k × TreeMatch k)
    (hc : Compat (fun i => T.tree.contour.getD i []) p) (V : Quotient (treeSetoid p)) :
    ccls T p hc V ∈ T.tree.vtxs := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep V
  exact tt_mem T (by have := treePos_lt x; omega)

private theorem ccls_surj {k : ℕ} [NeZero k] (T : TypedOrdTree k) (p : TreeMatch k × TreeMatch k)
    (hc : Compat (fun i => T.tree.contour.getD i []) p) {u : List ℕ} (hu : u ∈ T.tree.vtxs) :
    ∃ V, ccls T p hc V = u := by
  have hk0 := NeZero.pos k
  obtain ⟨j, hj, hje⟩ := tt_cover T hu
  rcases Nat.lt_or_ge j (2 * k) with h | h
  · obtain ⟨x, hx⟩ := treePos_surj (k := k) h
    exact ⟨treeMk p x, by rw [ccls_mk, hx, hje]⟩
  · have : j = 2 * k := by omega
    subst this
    obtain ⟨x, hx⟩ := treePos_surj (k := k) (show 0 < 2 * k by omega)
    exact ⟨treeMk p x, by rw [ccls_mk, hx, tt_zero, ← hje, tt_last]⟩

private theorem tt_fibre {k : ℕ} [NeZero k] (T : TypedOrdTree k) (p : TreeMatch k × TreeMatch k)
    (hc : Compat (fun i => T.tree.contour.getD i []) p)
    (hconn : (qg p).Connected)
    (hedges : (Finset.univ.filter fun s : Fin k => s.val < (p.1.1 s).val).card +
      (Finset.univ.filter fun s : Fin k => s.val < (p.2.1 s).val).card = k) :
    Nat.card (Quotient (treeSetoid p)) = k + 1 ∧ Function.Injective (ccls T p hc) := by
  classical
  have hle : Nat.card (Quotient (treeSetoid p)) ≤ k + 1 := by
    have h1 := qg_edge_card_le p hedges
    have h2 := hconn.card_vert_le_card_edgeSet_add_one
    omega
  let f : Quotient (treeSetoid p) → {u // u ∈ T.tree.vtxs} := fun V => ⟨ccls T p hc V, ccls_mem T p hc V⟩
  have hsurj : Function.Surjective f := by
    intro ⟨u, hu⟩
    obtain ⟨V, hV⟩ := ccls_surj T p hc hu
    exact ⟨V, Subtype.ext hV⟩
  have hcard : Nat.card {u // u ∈ T.tree.vtxs} = k + 1 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun u => (List.mem_toFinset (l := T.tree.vtxs)).symm)),
      Nat.card_eq_finsetCard, List.toFinset_card_of_nodup (pt_nodup T.tree), T.card_vtx]
  have hbij := hsurj.bijective_of_nat_card_le (by omega)
  refine ⟨?_, ?_⟩
  · rw [Nat.card_eq_of_bijective f hbij, hcard]
  · intro V W h
    exact hbij.1 (Subtype.ext h)

private theorem tt_ty_val {k : ℕ} (T : TypedOrdTree k) {j : ℕ} (hj : j ≤ 2 * k) :
    T.ty (T.tree.contour.getD j []) =
      (if j % 2 = 1 then VType.lat else if j % 4 = 0 then VType.out else VType.inp) := by
  obtain ⟨h1, h2⟩ := tt_ty T j hj
  by_cases h : j % 2 = 1
  · rw [if_pos h]; exact h1 h
  · rw [if_neg h]; exact h2 (by omega)

private theorem tt_ext {k : ℕ} (T T' : TypedOrdTree k) (htree : T.tree = T'.tree) : T = T' := by
  have hty : T.ty = T'.ty := by
    funext u
    by_cases hu : u ∈ T.tree.vtxs
    · obtain ⟨j, hj, hje⟩ := tt_cover T hu
      have hje' : T'.tree.contour.getD j [] = u := by rw [← htree]; exact hje
      have e1 := tt_ty_val T hj
      have e2 := tt_ty_val T' hj
      rw [hje] at e1
      rw [hje'] at e2
      rw [e1, e2]
    · have hu' : u ∉ T'.tree.vtxs := by rw [← htree]; exact hu
      rw [T.off_support u hu, T'.off_support u hu']
  obtain ⟨t, ty, a1, a2, a3, a4, a5⟩ := T
  obtain ⟨t', ty', b1, b2, b3, b4, b5⟩ := T'
  simp only at htree hty
  subst htree
  subst hty
  rfl

private theorem encoding_core (a b : ℕ) :
    ∃ e : {p : TreeMatch (treeK a b) × TreeMatch (treeK a b) // treeRetained p} ≃ TypedTrees a b,
      ClassFibreMap a b e := by
  classical
  haveI : NeZero (treeK a b) := ⟨by unfold treeK; omega⟩
  have hk : treeK a b % 2 = 0 := by unfold treeK; omega
  have hconn : ∀ p : TreeMatch (treeK a b) × TreeMatch (treeK a b), (qg p).Connected :=
    fun p => def_app_vol_tree_connected a b p
  have hedges := def_app_vol_tree_edges a b
  -- the map from typed trees to retained pairings
  let G0 : TypedTrees a b → TreeMatch (treeK a b) × TreeMatch (treeK a b) :=
    fun T => Classical.choose (tt_exists_pair T)
  have hG0 : ∀ T : TypedTrees a b, Compat (fun i => T.tree.contour.getD i []) (G0 T) :=
    fun T => Classical.choose_spec (tt_exists_pair T)
  have hret : ∀ T : TypedTrees a b, treeRetained (G0 T) := fun T =>
    (tt_fibre T (G0 T) (hG0 T) (hconn _) (hedges _)).1
  let G : TypedTrees a b → {p : TreeMatch (treeK a b) × TreeMatch (treeK a b) // treeRetained p} :=
    fun T => ⟨G0 T, hret T⟩
  have hinj : Function.Injective G := by
    intro T T' h
    have hp : G0 T = G0 T' := congrArg Subtype.val h
    have c1 := hG0 T
    have c2 : Compat (fun i => T'.tree.contour.getD i []) (G0 T) := by rw [hp]; exact hG0 T'
    have i1 := (tt_fibre T (G0 T) c1 (hconn _) (hedges _)).2
    have i2 := (tt_fibre T' (G0 T) c2 (hconn _) (hedges _)).2
    have hpos : ∀ i ≤ 2 * treeK a b, ∃ x : TreeVtx (treeK a b), treePos x = i % (2 * treeK a b) ∧
        T.tree.contour.getD i [] = T.tree.contour.getD (treePos x) [] ∧
        T'.tree.contour.getD i [] = T'.tree.contour.getD (treePos x) [] := by
      intro i hi
      obtain ⟨x, hx⟩ := treePos_surj (k := treeK a b) (i := i % (2 * treeK a b))
        (Nat.mod_lt _ (by have := NeZero.pos (treeK a b); omega))
      exact ⟨x, hx, by rw [hx, tt_mod T hi], by rw [hx, tt_mod T' hi]⟩
    have heq : ∀ i j, i < T.tree.contour.length → j < T.tree.contour.length →
        (T.tree.contour.getD i [] = T.tree.contour.getD j [] ↔
          T'.tree.contour.getD i [] = T'.tree.contour.getD j []) := by
      intro i j hi hj
      have hl := tt_len T
      obtain ⟨x, -, hx1, hx2⟩ := hpos i (by omega)
      obtain ⟨y, -, hy1, hy2⟩ := hpos j (by omega)
      rw [hx1, hy1, hx2, hy2]
      constructor
      · intro h
        have : treeMk (G0 T) x = treeMk (G0 T) y := i1 (by rw [ccls_mk, ccls_mk]; exact h)
        have := congrArg (ccls T' (G0 T) c2) this
        rw [ccls_mk, ccls_mk] at this
        exact this
      · intro h
        have : treeMk (G0 T) x = treeMk (G0 T) y := i2 (by rw [ccls_mk, ccls_mk]; exact h)
        have := congrArg (ccls T (G0 T) c1) this
        rw [ccls_mk, ccls_mk] at this
        exact this
    have htree : T.tree = T'.tree :=
      pt_determ T.tree T'.tree (by rw [tt_len T, tt_len T']) heq
    exact tt_ext T T' htree
  have hsurj : Function.Surjective G := by
    intro q
    obtain ⟨T, hT⟩ := retained_tree hk q.1 (hconn _) (hedges _) q.2
    refine ⟨T, Subtype.ext ?_⟩
    exact tt_pair_unique T (G0 T) q.1 (hG0 T) hT
  have hbij : Function.Bijective G := ⟨hinj, hsurj⟩
  refine ⟨(Equiv.ofBijective G hbij).symm, ?_⟩
  intro p
  obtain ⟨T, hT⟩ : ∃ T, (Equiv.ofBijective G hbij).symm p = T := ⟨_, rfl⟩
  have hp : G T = p := by
    rw [← hT]
    exact Equiv.ofBijective_apply_symm_apply G hbij p
  rw [hT]
  subst hp
  have hc := hG0 T
  obtain ⟨-, hinjc⟩ := tt_fibre T (G0 T) hc (hconn _) (hedges _)
  exact ⟨ccls T (G0 T) hc, hinjc, ccls_mem T (G0 T) hc, fun u hu => ccls_surj T (G0 T) hc hu,
    fun x => ccls_mk T (G0 T) hc x⟩
/-! ## Encoding of retained pairings -/

open Classical in
/-- `lem:app-vol-closed-encoding`, snapshot `cr-2026-10-23`. Declaration of record, existence part: there
is a bijection between the retained pairings of `W_{a,b}` and `𝒯_{a,b}` under which the vertex classes
are the fibres of the contour (`ClassFibreMap`). Verbatim LaTeX of the lemma statement:
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
theorem lem_app_vol_closed_encoding_i (a b : ℕ) :
    ∃ e : {p : TreeMatch (treeK a b) × TreeMatch (treeK a b) // treeRetained p} ≃ TypedTrees a b,
      ClassFibreMap a b e := by
  exact encoding_core a b

/-! ### Helpers for `lem_app_vol_closed_encoding_ii` (class data read off the fibre map) -/

private theorem enc_iff (a b : ℕ)
    (e : {p : TreeMatch (treeK a b) × TreeMatch (treeK a b) // treeRetained p} ≃ TypedTrees a b)
    (he : ClassFibreMap a b e)
    (p : {p : TreeMatch (treeK a b) × TreeMatch (treeK a b) // treeRetained p})
    (x y : TreeVtx (treeK a b)) :
    treeMk p.1 x = treeMk p.1 y ↔
      (e p).tree.contour.getD (treePos x) [] = (e p).tree.contour.getD (treePos y) [] := by
  obtain ⟨ι, hinj, -, -, hι⟩ := he p
  constructor
  · intro h; rw [← hι, ← hι, h]
  · intro h; apply hinj; rw [hι, hι, h]

private theorem lab_next {k : ℕ} (T : TypedOrdTree k) {i : ℕ} (hi : i < 2 * k) :
    T.tree.contour.getD (i + 1) [] =
      if (lab T.tree.contour i).2 then (lab T.tree.contour i).1
      else (lab T.tree.contour i).1.dropLast := by
  unfold lab
  by_cases h : T.tree.contour.getD (i + 1) [] ≠ [] ∧
      (T.tree.contour.getD (i + 1) []).dropLast = T.tree.contour.getD i []
  · rw [if_pos h]; simp
  · rw [if_neg h]
    simp only [Bool.false_eq_true, if_false]
    rcases tt_pc T hi with h1 | ⟨h1, h2⟩
    · exact absurd h1 h
    · exact h2.symm

private theorem lab_bijOn {k : ℕ} (T : TypedOrdTree k) :
    Set.BijOn (lab T.tree.contour) (↑(Finset.range (2 * k)))
      (↑((T.tree.vtxs.toFinset.erase ([] : List ℕ)) ×ˢ (Finset.univ : Finset Bool))) := by
  classical
  let NR : Finset (List ℕ) := T.tree.vtxs.toFinset.erase []
  have hNR : NR.card = k := by
    have := Finset.card_erase_of_mem (s := T.tree.vtxs.toFinset) (a := []) (by
      rw [List.mem_toFinset]; exact pt_root_mem _)
    rw [List.toFinset_card_of_nodup (pt_nodup T.tree), T.card_vtx] at this
    simpa [NR] using this
  let Tg : Finset (List ℕ × Bool) := NR ×ˢ (Finset.univ : Finset Bool)
  have hTg : Tg.card = 2 * k := by
    simp [Tg, Finset.card_product, hNR]; ring
  have hmaps : Set.MapsTo (lab T.tree.contour) (↑(Finset.range (2 * k))) (↑Tg) := by
    intro i hi
    have hi' := Finset.mem_range.mp (Finset.mem_coe.mp hi)
    simp only [Finset.mem_coe, Tg, NR, Finset.mem_product, Finset.mem_erase, List.mem_toFinset,
      Finset.mem_univ, and_true]
    exact ⟨(lab_edge T hi').1, lab_mem T hi'⟩
  have hsurj : Set.SurjOn (lab T.tree.contour) (↑(Finset.range (2 * k))) (↑Tg) := by
    intro x hx
    have hx' := Finset.mem_coe.mp hx
    simp only [Tg, NR, Finset.mem_product, Finset.mem_erase, List.mem_toFinset, Finset.mem_univ,
      and_true] at hx'
    obtain ⟨i, hi, he⟩ := lab_surj T hx'.2 hx'.1 x.2
    exact ⟨i, Finset.mem_coe.mpr (Finset.mem_range.mpr hi), by rw [he]⟩
  have hinj := Finset.injOn_of_surjOn_of_card_le (lab T.tree.contour) hmaps hsurj
    (by rw [Finset.card_range, hTg])
  exact ⟨hmaps, hinj, hsurj⟩

private theorem tt_visit_succ {k : ℕ} (T : TypedOrdTree k) {x : List ℕ} (hx : x ∈ T.tree.vtxs) :
    ((Finset.range (2 * k)).filter fun i => T.tree.contour.getD (i + 1) [] = x).card =
      T.tree.degAt x := by
  classical
  let NR : Finset (List ℕ) := T.tree.vtxs.toFinset.erase []
  have hb := lab_bijOn T
  have step1 : ((Finset.range (2 * k)).filter fun i => T.tree.contour.getD (i + 1) [] = x).card =
      ((NR ×ˢ (Finset.univ : Finset Bool)).filter
        fun q => (if q.2 then q.1 else q.1.dropLast) = x).card := by
    apply Finset.card_bij (fun i _ => lab T.tree.contour i)
    · intro i hi
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨hb.mapsTo (Finset.mem_coe.mpr hi.1), ?_⟩
      rw [← lab_next T (Finset.mem_range.mp hi.1)]; exact hi.2
    · intro i hi j hj h
      exact hb.injOn (Finset.mem_coe.mpr (Finset.mem_filter.mp hi).1)
        (Finset.mem_coe.mpr (Finset.mem_filter.mp hj).1) h
    · intro q hq
      rw [Finset.mem_filter] at hq
      obtain ⟨i, hi, hiq⟩ := hb.surjOn (Finset.mem_coe.mpr hq.1)
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hi, ?_⟩, hiq⟩
      rw [lab_next T (Finset.mem_range.mp (Finset.mem_coe.mp hi)), hiq]; exact hq.2
  have step2 : ((NR ×ˢ (Finset.univ : Finset Bool)).filter
        fun q => (if q.2 then q.1 else q.1.dropLast) = x).card =
      (NR.filter fun v => v = x).card + (NR.filter fun v => v.dropLast = x).card := by
    simp only [Finset.card_filter, Finset.sum_product, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rw [Fintype.sum_bool]
    simp [add_comm]
  have step3 : (NR.filter fun v => v = x).card = if x = [] then 0 else 1 := by
    rw [Finset.filter_eq' NR x]
    by_cases hx0 : x = []
    · subst hx0; simp [NR]
    · have : x ∈ NR := by
        simp only [NR, Finset.mem_erase, List.mem_toFinset]; exact ⟨hx0, hx⟩
      simp [this, hx0]
  have step4 : (NR.filter fun v => v.dropLast = x).card = T.tree.childCount x := by
    unfold PlaneTree.childCount
    rw [← List.toFinset_card_of_nodup ((pt_nodup T.tree).filter _), List.toFinset_filter]
    congr 1
    ext v
    simp only [NR, Finset.mem_filter, Finset.mem_erase, List.mem_toFinset, decide_eq_true_eq]
    tauto
  rw [step1, step2, step3, step4, PlaneTree.degAt]
  omega

private theorem tt_visit_card {k : ℕ} (T : TypedOrdTree k) {x : List ℕ} (hx : x ∈ T.tree.vtxs) :
    ((Finset.range (2 * k)).filter fun j => T.tree.contour.getD j [] = x).card =
      T.tree.degAt x := by
  classical
  rw [← tt_visit_succ T hx]
  simp only [Finset.card_filter]
  have h1 := Finset.sum_range_succ (fun j => if T.tree.contour.getD j [] = x then 1 else 0) (2 * k)
  have h2 := Finset.sum_range_succ' (fun j => if T.tree.contour.getD j [] = x then 1 else 0) (2 * k)
  rw [tt_zero] at h2
  rw [tt_last] at h1
  omega

private theorem treePos_inl_even {k : ℕ} (s : Fin k) : treePos (Sum.inl s : TreeVtx k) % 2 = 0 := by
  show 2 * (s.val + 1) % (2 * k) % 2 = 0
  have := s.isLt
  rcases Nat.lt_or_ge (s.val + 1) k with h | h
  · have h1 : 2 * (s.val + 1) % (2 * k) = 2 * (s.val + 1) := Nat.mod_eq_of_lt (by omega)
    rw [h1]; omega
  · have h2 : 2 * (s.val + 1) = 2 * k := by omega
    rw [h2, Nat.mod_self]

private theorem enc_ii_a (a b : ℕ)
    (e : {p : TreeMatch (treeK a b) × TreeMatch (treeK a b) // treeRetained p} ≃ TypedTrees a b)
    (he : ClassFibreMap a b e)
    (p : {p : TreeMatch (treeK a b) × TreeMatch (treeK a b) // treeRetained p})
    (s : Fin (treeK a b)) :
    (e p).ty ((e p).tree.contour.getD (treePos (Sum.inl s)) []) ≠ VType.lat ∧
      (@Finset.filter _ (fun s' : Fin (treeK a b) =>
            treeMk p.1 (Sum.inl s') = treeMk p.1 (Sum.inl s)) (fun _ => Classical.propDecidable _)
          Finset.univ).card =
        (e p).tree.degAt ((e p).tree.contour.getD (treePos (Sum.inl s)) []) := by
  have hk : NeZero (treeK a b) := ⟨by unfold treeK; omega⟩
  set T := e p with hT
  have hlt := treePos_lt (Sum.inl s : TreeVtx (treeK a b))
  have hev := treePos_inl_even s
  have hmem := tt_mem T (show treePos (Sum.inl s : TreeVtx (treeK a b)) ≤ 2 * treeK a b by omega)
  refine ⟨?_, ?_⟩
  · rw [Ne, tt_lat T (by omega)]; omega
  · rw [← tt_visit_card T hmem]
    have : (@Finset.filter _ (fun s' : Fin (treeK a b) =>
            treeMk p.1 (Sum.inl s') = treeMk p.1 (Sum.inl s)) (fun _ => Classical.propDecidable _)
          Finset.univ) = Finset.univ.filter (fun s' : Fin (treeK a b) =>
            T.tree.contour.getD (treePos (Sum.inl s')) [] =
              T.tree.contour.getD (treePos (Sum.inl s)) []) := by
      ext s'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact enc_iff a b e he p _ _
    rw [this]
    apply Finset.card_bij (fun s' _ => treePos (Sum.inl s' : TreeVtx (treeK a b)))
    · intro s' hs'
      rw [Finset.mem_filter] at hs' ⊢
      exact ⟨Finset.mem_range.mpr (treePos_lt _), hs'.2⟩
    · intro s1 _ s2 _ h
      have := congrArg (vAt (treeK a b)) h
      rw [vAt_treePos, vAt_treePos] at this
      exact Sum.inl_injective this
    · intro j hj
      rw [Finset.mem_filter, Finset.mem_range] at hj
      have hpar := tt_par_eq T (show j ≤ 2 * treeK a b by omega)
        (show treePos (Sum.inl s : TreeVtx (treeK a b)) ≤ 2 * treeK a b by omega) hj.2
      obtain ⟨x', hx'⟩ := treePos_surj hj.1
      cases x' with
      | inl s' =>
        refine ⟨s', ?_, hx'⟩
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by rw [hx']; exact hj.2⟩
      | inr s' =>
        exfalso
        have : treePos (Sum.inr s' : TreeVtx (treeK a b)) % 2 = 1 := by
          show (2 * s'.val + 1) % 2 = 1; omega
        omega

private theorem treePos_F (a b : ℕ) : treePos (Sum.inl (treeFMark a b) : TreeVtx (treeK a b)) = 0 := by
  show 2 * ((treeFMark a b).val + 1) % (2 * treeK a b) = 0
  have : 2 * ((treeFMark a b).val + 1) = 2 * treeK a b := by
    change 2 * (2 * a + 2 * b + 1 + 1) = 2 * (2 * a + 2 * b + 2)
    omega
  rw [this, Nat.mod_self]

private theorem treePos_G (a b : ℕ) :
    treePos (Sum.inl (treeGMark a b) : TreeVtx (treeK a b)) = 2 * (2 * a + 1) := by
  show 2 * ((treeGMark a b).val + 1) % (2 * treeK a b) = 2 * (2 * a + 1)
  have h : 2 * ((treeGMark a b).val + 1) = 2 * (2 * a + 1) := by
    change 2 * (2 * a + 1) = 2 * (2 * a + 1)
    rfl
  rw [h]
  apply Nat.mod_eq_of_lt
  unfold treeK; omega

open Classical in
/-- `lem:app-vol-closed-encoding`, snapshot `cr-2026-10-23`. Declaration of record, class-data part
(the "consequently" clauses), for any bijection `e` with the fibre property `ClassFibreMap`: (a) an
external class `V` has `p_V = deg x`, where `x` is its tree vertex; (b) a latent class has
`S_V = {r : c(2r-1) = x}`; (c) `e_0 ∈ V` iff `x` is the root; (d) `e_{2a+1} ∈ V` iff `x` is the
`G`-vertex `c(2(2a+1))`. Here `e_s` is the 0-based polygon vertex `inl s` and `l_s` is `inr s`.
Verbatim LaTeX of the lemma statement:
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
theorem lem_app_vol_closed_encoding_ii (a b : ℕ)
    (e : {p : TreeMatch (treeK a b) × TreeMatch (treeK a b) // treeRetained p} ≃ TypedTrees a b)
    (he : ClassFibreMap a b e) :
    (∀ p : {p : TreeMatch (treeK a b) × TreeMatch (treeK a b) // treeRetained p},
      ∀ s : Fin (treeK a b),
        (e p).ty ((e p).tree.contour.getD (treePos (Sum.inl s)) []) ≠ VType.lat ∧
        (Finset.univ.filter fun s' : Fin (treeK a b) =>
            treeMk p.1 (Sum.inl s') = treeMk p.1 (Sum.inl s)).card =
          (e p).tree.degAt ((e p).tree.contour.getD (treePos (Sum.inl s)) [])) ∧
    (∀ p : {p : TreeMatch (treeK a b) × TreeMatch (treeK a b) // treeRetained p},
      ∀ s : Fin (treeK a b),
        Finset.univ.filter (fun r : Fin (treeK a b) => treeMk p.1 (Sum.inr r) = treeMk p.1 (Sum.inr s)) =
          Finset.univ.filter (fun r : Fin (treeK a b) =>
            (e p).tree.contour.getD (2 * r.val + 1) [] =
              (e p).tree.contour.getD (treePos (Sum.inr s)) [])) ∧
    (∀ p : {p : TreeMatch (treeK a b) × TreeMatch (treeK a b) // treeRetained p},
      ∀ x : TreeVtx (treeK a b),
        treeMk p.1 (Sum.inl (treeFMark a b)) = treeMk p.1 x ↔
          (e p).tree.contour.getD (treePos x) [] = []) ∧
    (∀ p : {p : TreeMatch (treeK a b) × TreeMatch (treeK a b) // treeRetained p},
      ∀ x : TreeVtx (treeK a b),
        treeMk p.1 (Sum.inl (treeGMark a b)) = treeMk p.1 x ↔
          (e p).tree.contour.getD (treePos x) [] =
            (e p).tree.contour.getD (2 * (2 * a + 1)) []) := by
  refine ⟨fun p s => by convert enc_ii_a a b e he p s, ?_, ?_, ?_⟩
  · intro p s
    apply Finset.filter_congr
    intro r _
    exact enc_iff a b e he p _ _
  · intro p x
    rw [enc_iff a b e he p, treePos_F, tt_zero]
    exact eq_comm
  · intro p x
    rw [enc_iff a b e he p, treePos_G]
    exact eq_comm

/-! ## Helpers: typings and the Catalan bound (l.2110–2117) -/

/-- Typing uniqueness (l.2113–2117): the typing of a typed ordered tree is determined by its plane tree,
since the root has type `o` and the edge and alternation rules determine every other type. -/
theorem typedOrdTree_typing_unique {k : ℕ} (T₁ T₂ : TypedOrdTree k) (h : T₁.tree = T₂.tree) :
    ∀ u ∈ T₁.tree.vtxs, T₁.ty u = T₂.ty u := by
  cases tt_ext T₁ T₂ h
  intro u _
  rfl

private theorem pt_binary_encoding :
    ∃ f : PlaneTree → BinaryTree Unit, Function.Injective f ∧
      ∀ P, (f P).numNodes + 1 = P.vtxs.length := by
  classical
  let decode : BinaryTree Unit → PlaneTree :=
    BinaryTree.rec (.node []) (fun _ _ _ l r =>
      match r with | .node cs => .node (l :: cs))
  have hex : ∀ P : PlaneTree, ∃ b : BinaryTree Unit,
      decode b = P ∧ b.numNodes + 1 = P.vtxs.length := by
    apply plane_ind
    · exact ⟨.nil, rfl, by simp [PlaneTree.vtxs, vtxsForest]⟩
    · intro P cs hP hcs
      obtain ⟨l, hl, hln⟩ := hP
      obtain ⟨r, hr, hrn⟩ := hcs
      refine ⟨.node () l r, ?_, ?_⟩
      · change (match decode r with | .node ds => PlaneTree.node (decode l :: ds)) = _
        rw [hl, hr]
      · rw [BinaryTree.numNodes, pt_vtxs_len]
        omega
  choose f hf hn using hex
  refine ⟨f, ?_, hn⟩
  intro P Q h
  rw [← hf P, ← hf Q, h]

/-- Catalan bound (l.2110–2117): there are finitely many typed ordered trees with `k` edges and at most
`4^k` of them, since their number is at most the Catalan number `(1/(k+1)) binom(2k,k) ≤ 4^k`. -/
theorem typedOrdTree_card_le (k : ℕ) :
    Finite (TypedOrdTree k) ∧ Nat.card (TypedOrdTree k) ≤ 4 ^ k := by
  classical
  obtain ⟨f, hf, hn⟩ := pt_binary_encoding
  let g : TypedOrdTree k → ↥(BinaryTree.treesOfNumNodesEq k) := fun T =>
    ⟨f T.tree, BinaryTree.mem_treesOfNumNodesEq.mpr (by
      have h := hn T.tree
      rw [T.card_vtx] at h
      omega)⟩
  have hg : Function.Injective g := by
    intro T T' h
    apply tt_ext T T'
    exact hf (congrArg Subtype.val h)
  haveI : Finite (TypedOrdTree k) := Finite.of_injective g hg
  refine ⟨inferInstance, ?_⟩
  calc
    Nat.card (TypedOrdTree k) ≤ Nat.card ↥(BinaryTree.treesOfNumNodesEq k) :=
      Nat.card_le_card_of_injective g hg
    _ = catalan k := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe,
        BinaryTree.treesOfNumNodesEq_card_eq_catalan]
    _ ≤ 4 ^ k := by
      rw [catalan_eq_centralBinom_div]
      exact (Nat.div_le_self _ _).trans (Nat.centralBinom_le_four_pow k)

end Muon.Volatility

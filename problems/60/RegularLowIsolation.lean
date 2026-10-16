import CompletionBasic

/-! Source correspondence: COUNT-BASED-COMPLETION-PROOF-v2.md Section 2,
paragraph identifying the isolated neighbor. This module proves genuine local
prerequisites only; it DOES NOT prove isolated=low.

Remaining concrete bridge: under the contrary pairing of the degree-q neighbor,
for each of the q-2 matched full cells Ci away from that pair, derive from the
actual partition and cross-cell matchings the total degree inequality
  (sum x in Ci, degree x) + 2 <= (q+1)*card Ci.
The required two lost units are (1) odd internal matching, supplied below, and
(2) at most card(Ci)-1 edges to the smaller low-index cell. This still needs an
actual finite incidence decomposition of degree sums over the partition and
cardinality formulas |C_low|=q-2, |Ci|=q-1, |C_isolated|=q.
Then two_low_of_degree_sum applies in every such cell missing deep vertices;
disjoint cells and global budgets must imply |S| >= 2*(q-2-|D|), contrary to the
stated 1.001q/.001q budgets. These counting/decomposition statements are unpaid,
not source assumptions, and are not hidden hypotheses of a claimed isolation
result. All six actual prerequisites below compile without additional axioms.
-/
namespace Erdos60.Completion
variable {V : Type*}

/-- Cells indexed by adjacent local neighbors have no edges between them. -/
theorem paired_cells_no_edges (G : SimpleGraph V) (hG : NoFourCycle G)
    {v a b x y : V} (hva : G.Adj v a) (hvb : G.Adj v b) (hab : G.Adj a b)
    (hx : x ∈ cell G v a) (hy : y ∈ cell G v b) : ¬G.Adj x y := by
  intro hxy
  have hay : a ≠ y := by intro h; exact hy.2.2 (h ▸ hva)
  have hxb : x ≠ b := by intro h; exact hx.2.2 (h.symm ▸ hvb)
  exact hG hay hxb hx.1 hxy hy.1.symm hab.symm

/-- Edges between distinct outside cells form an actual matching at either side. -/
theorem cross_cell_neighbor_unique (G : SimpleGraph V) (hG : NoFourCycle G)
    {v a b x y z : V} (hva : G.Adj v a)
    (hx : x ∈ cell G v a) (hy : y ∈ cell G v a) (hz : z ∈ cell G v b)
    (hxz : G.Adj x z) (hyz : G.Adj y z) : x = y := by
  have haz : a ≠ z := by intro h; exact hz.2.2 (h ▸ hva)
  exact common_neighbor_unique hG haz hx.1 hxz.symm hy.1 hyz.symm

/-- The induced graph inside one cell is itself a matching. -/
theorem within_cell_neighbor_unique (G : SimpleGraph V) (hG : NoFourCycle G)
    {v a x y z : V} (hx : x ∈ cell G v a) (hy : y ∈ cell G v a)
    (hz : z ∈ cell G v a) (hxy : G.Adj x y) (hxz : G.Adj x z) : y = z :=
  neighborhood_neighbor_unique hG hx.1 hy.1 hz.1 hxy hxz

/-- Every cell point has precisely its own index as neighbor in the center's neighborhood. -/
theorem cell_center_neighbor_iff (G : SimpleGraph V) (hG : NoFourCycle G)
    {v a x b : V} (hva : G.Adj v a) (hx : x ∈ cell G v a) (hvb : G.Adj v b) :
    G.Adj x b ↔ b = a := by
  constructor
  · intro hxb
    exact common_neighbor_unique hG hx.2.1 hxb hvb hx.1.symm hva
  · intro h
    exact h ▸ hx.1.symm

/-- Two units of actual total degree deficiency force two low vertices in a
cell with no deeply deficient vertex. This does not assume a low-vertex witness. -/
theorem two_low_of_degree_sum [Fintype V] (G : SimpleGraph V) (q : ℕ)
    (s : Finset V)
    (hmin : ∀ x ∈ s, letI := Classical.decRel G.Adj; q ≤ G.degree x)
    (hsum : letI := Classical.decRel G.Adj;
      (∑ x ∈ s, G.degree x) + 2 ≤ (q+1)*s.card) :
    letI := Classical.decRel G.Adj
    2 ≤ (s.filter (fun x => G.degree x ≤ q)).card := by
  classical
  have hpoint : ∀ x ∈ s, q+1 ≤ G.degree x + (if G.degree x ≤ q then 1 else 0) := by
    intro x hx
    have hm := hmin x hx
    split_ifs <;> omega
  have hs := Finset.sum_le_sum hpoint
  have hi : (∑ x ∈ s, if G.degree x ≤ q then 1 else 0) =
      (s.filter (fun x => G.degree x ≤ q)).card := by simp
  simp only [Finset.sum_const,smul_eq_mul,Finset.sum_add_distrib] at hs
  rw [hi, Nat.mul_comm s.card (q+1)] at hs
  omega

/-- The actual graph induced on an odd set of neighbors has at least one
missing internal degree, by C4-freeness and handshaking. -/
theorem odd_neighbor_set_internal_bound [Fintype V] (G : SimpleGraph V)
    (hG : NoFourCycle G) (a : V) (s : Finset V)
    (hs : ∀ x ∈ s, G.Adj a x) (hodd : Odd s.card) :
    letI := Classical.decRel G.Adj
    let H : SimpleGraph s := G.comap Subtype.val
    (∑ x : s, H.degree x) + 1 ≤ s.card := by
  classical
  let H : SimpleGraph s := G.comap Subtype.val
  change (∑ x : s, H.degree x) + 1 ≤ s.card
  have hd : ∀ x : s, H.degree x ≤ 1 := by
    intro x
    rw [← H.card_neighborFinset_eq_degree]
    apply Finset.card_le_one.mpr
    intro y hy z hz
    apply Subtype.ext
    have hxy : G.Adj x.val y.val := by simpa only [SimpleGraph.mem_neighborFinset, H, SimpleGraph.comap_adj] using hy
    have hxz : G.Adj x.val z.val := by simpa only [SimpleGraph.mem_neighborFinset, H, SimpleGraph.comap_adj] using hz
    exact neighborhood_neighbor_unique hG (hs x.val x.property)
      (hs y.val y.property) (hs z.val z.property) hxy hxz
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset s)) => hd x)
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,Fintype.card_coe] at hsum
  have he := H.sum_degrees_eq_twice_card_edges
  obtain ⟨k,hk⟩ := hodd
  omega

#print axioms odd_neighbor_set_internal_bound
#print axioms two_low_of_degree_sum
#print axioms paired_cells_no_edges
#print axioms cross_cell_neighbor_unique
#print axioms within_cell_neighbor_unique
#print axioms cell_center_neighbor_iff
end Erdos60.Completion

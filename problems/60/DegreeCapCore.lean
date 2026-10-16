import ActualSupport
import Mathlib.Tactic
namespace Erdos60.Core
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Select actual edges to enforce a degree cap, paying at most total positive excess. -/
theorem exists_degree_cap_edges (G : SimpleGraph V) (c : ℕ) :
    ∃ D : Finset (Sym2 V), D ⊆ G.edgeFinset ∧
      D.card ≤ ∑ v : V, (G.degree v - c) ∧
      ∀ v, (G \ SimpleGraph.fromEdgeSet (D : Set (Sym2 V))).degree v ≤ c := by
  classical
  have hex : ∀ v, ∃ N : Finset V, N ⊆ G.neighborFinset v ∧ N.card = G.degree v - c := by
    intro v
    apply Finset.exists_subset_card_eq
    rw [G.card_neighborFinset_eq_degree]
    exact Nat.sub_le _ _
  choose N hN hcard using hex
  let D := Finset.univ.biUnion fun v => (N v).image (fun w => s(v,w))
  have hsub : D ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨v,hv,he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp he
    simpa using (G.mem_neighborFinset v w).mp (hN v hw)
  refine ⟨D,hsub,?_,?_⟩
  · calc
      D.card ≤ ∑ v ∈ Finset.univ, ((N v).image (fun w => s(v,w))).card := Finset.card_biUnion_le
      _ ≤ ∑ v : V, (G.degree v - c) := by
        apply Finset.sum_le_sum
        intro v hv
        exact (Finset.card_image_le).trans_eq (hcard v)
  · intro v
    have hs : (G \ SimpleGraph.fromEdgeSet (D : Set (Sym2 V))).neighborFinset v ⊆
        G.neighborFinset v \ N v := by
      intro w hw
      have hw' : G.Adj v w ∧ ¬(SimpleGraph.fromEdgeSet (D : Set (Sym2 V))).Adj v w := by
        simpa using hw
      refine Finset.mem_sdiff.mpr ⟨by simpa using hw'.1,?_⟩
      intro hn
      apply hw'.2
      rw [SimpleGraph.fromEdgeSet_adj]
      refine ⟨?_,hw'.1.ne⟩
      exact Finset.mem_biUnion.mpr ⟨v,Finset.mem_univ _,Finset.mem_image.mpr ⟨w,hn,rfl⟩⟩
    have hb := Finset.card_le_card hs
    rw [Finset.card_sdiff_of_subset (hN v), hcard v, G.card_neighborFinset_eq_degree,
      SimpleGraph.card_neighborFinset_eq_degree] at hb
    omega

/-- All vertices incident to one of the selected actual edges. -/
def endpoints (D : Finset (Sym2 V)) : Finset V := D.biUnion Sym2.toFinset

omit [Fintype V] in
theorem endpoints_card (D : Finset (Sym2 V)) : (endpoints D).card ≤ 2*D.card := by
  calc
    _ ≤ ∑ e ∈ D, e.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ D, 2 := by
      apply Finset.sum_le_sum
      intro e he
      rw [Sym2.card_toFinset]
      split_ifs <;> omega
    _ = _ := by simp [mul_comm]

/-- Delete precisely original edges with both endpoints in the given support. -/
def outsideGraph (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ ¬(a ∈ S ∧ b ∈ S)
  symm := ⟨fun _a _b h => ⟨h.1.symm,fun hh => h.2 ⟨hh.2,hh.1⟩⟩⟩
  loopless := ⟨fun _a h => G.ne_of_adj h.1 rfl⟩

/-- One simultaneous enlarged core pays selected endpoints and caps degree.
Every edge with an endpoint outside the core is retained exactly. -/
theorem exists_capped_core (G : SimpleGraph V) (S₀ : Finset V) (c : ℕ) :
    ∃ S : Finset V, S₀ ⊆ S ∧
      S.card ≤ S₀.card + 2*(∑ v : V, (G.degree v-c)) ∧
      (∀ v, (outsideGraph G S).degree v ≤ c) ∧
      (∀ a b, a ∉ S → ((outsideGraph G S).Adj a b ↔ G.Adj a b)) := by
  classical
  obtain ⟨D,hD,hcard,hcap⟩ := exists_degree_cap_edges G c
  let S := S₀ ∪ endpoints D
  have hle : outsideGraph G S ≤ G \ SimpleGraph.fromEdgeSet (D : Set (Sym2 V)) := by
    intro a b hab
    refine ⟨hab.1,?_⟩
    intro hd
    have hed : s(a,b) ∈ D := hd.1
    apply hab.2
    constructor
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨s(a,b),hed,by simp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨s(a,b),hed,by simp⟩)
  refine ⟨S,Finset.subset_union_left,?_,?_,?_⟩
  · have hu := Finset.card_union_le S₀ (endpoints D)
    have he := endpoints_card D
    dsimp [S]
    omega
  · intro v
    exact ((outsideGraph G S).degree_le_of_le hle).trans (hcap v)
  · intro a b ha
    change (G.Adj a b ∧ ¬(a ∈ S ∧ b ∈ S)) ↔ G.Adj a b
    simp [ha]

/-- The exact actual-cycle cover interface supplied by localization. -/
def SupportsEveryFourCycle (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ a b c d, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
    (a ∈ S ∧ b ∈ S) ∨ (b ∈ S ∧ c ∈ S) ∨ (c ∈ S ∧ d ∈ S) ∨ (d ∈ S ∧ a ∈ S)

def NoFourCycle (G : SimpleGraph V) : Prop :=
  ∀ a b c d, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → False

omit [Fintype V] [DecidableEq V] in
/-- Global cycle destruction is preserved when the actual support is enlarged. -/
theorem outsideGraph_no_four_cycle (G : SimpleGraph V) (S₀ S : Finset V)
    (hS : S₀ ⊆ S) (hc : SupportsEveryFourCycle G S₀) : NoFourCycle (outsideGraph G S) := by
  intro a b c d hac hbd hab hbc hcd hda
  rcases hc a b c d hac hbd hab.1 hbc.1 hcd.1 hda.1 with h|h|h|h
  · exact hab.2 ⟨hS h.1,hS h.2⟩
  · exact hbc.2 ⟨hS h.1,hS h.2⟩
  · exact hcd.2 ⟨hS h.1,hS h.2⟩
  · exact hda.2 ⟨hS h.1,hS h.2⟩

/-- Deleting internal support edges costs each vertex at most the support size. -/
theorem degree_loss_le_core (G : SimpleGraph V) (S : Finset V) (v : V) :
    G.degree v ≤ (outsideGraph G S).degree v + S.card := by
  classical
  have hs : G.neighborFinset v ⊆ (outsideGraph G S).neighborFinset v ∪ S := by
    intro w hw
    by_cases hws : w ∈ S
    · exact Finset.mem_union_right _ hws
    · apply Finset.mem_union_left
      rw [SimpleGraph.mem_neighborFinset]
      exact ⟨by simpa using hw,fun h => hws h.2⟩
  have hh := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hh

omit [DecidableEq V] in
/-- Vertices outside the core have exactly their original degrees. -/
theorem degree_outside_core (G : SimpleGraph V) (S : Finset V) {v : V} (hv : v ∉ S) :
    (outsideGraph G S).degree v = G.degree v := by
  classical
  have he : (outsideGraph G S).neighborFinset v = G.neighborFinset v := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset]
    change (G.Adj v w ∧ ¬(v ∈ S ∧ w ∈ S)) ↔ G.Adj v w
    simp [hv]
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using congrArg Finset.card he

/-- Simultaneous construction of the C4-free, degree-capped core. The only
cycle premise is the original actual support, not existence of selected edges. -/
theorem exists_simultaneous_core (G : SimpleGraph V) (S₀ : Finset V) (c : ℕ)
    (hc : SupportsEveryFourCycle G S₀) :
    ∃ S : Finset V, S₀ ⊆ S ∧
      S.card ≤ S₀.card + 2*(∑ v : V, (G.degree v-c)) ∧
      NoFourCycle (outsideGraph G S) ∧
      (∀ v, (outsideGraph G S).degree v ≤ c) ∧
      (∀ v, G.degree v ≤ (outsideGraph G S).degree v + S.card) ∧
      (∀ v, v ∉ S → (outsideGraph G S).degree v = G.degree v) := by
  obtain ⟨S,hS,hcard,hcap,hout⟩ := exists_capped_core G S₀ c
  exact ⟨S,hS,hcard,outsideGraph_no_four_cycle G S₀ S hS hc,hcap,
    degree_loss_le_core G S,fun _ hv => degree_outside_core G S hv⟩

/-- Numerical interface of completion §1, conditional only on the original
localization support and simultaneous original-graph statistics. -/
theorem exists_core_292 (G : SimpleGraph V) (S₀ : Finset V) (q : ℕ) (T : ℝ)
    (hc : SupportsEveryFourCycle G S₀)
    (hsize : (S₀.card : ℝ) ≤ 252*T)
    (hexcess : ((∑ v : V, (G.degree v-(q+1)) : ℕ) : ℝ) ≤ 20*T)
    (hmin : ∀ v, (q : ℝ)+1-26*T ≤ G.degree v)
    (hout : ∀ v, v ∉ S₀ → G.degree v = q ∨ G.degree v = q+1) :
    ∃ S : Finset V, S₀ ⊆ S ∧ (S.card : ℝ) ≤ 292*T ∧
      NoFourCycle (outsideGraph G S) ∧
      (∀ v, (outsideGraph G S).degree v ≤ q+1) ∧
      (∀ v, (q : ℝ)-318*T ≤ (outsideGraph G S).degree v) ∧
      (∀ v, v ∉ S → (outsideGraph G S).degree v = G.degree v ∧
        ((outsideGraph G S).degree v = q ∨ (outsideGraph G S).degree v = q+1)) := by
  obtain ⟨S,hS,hs,hfree,hcap,hloss,hretain⟩ := exists_simultaneous_core G S₀ (q+1) hc
  have hsreal : (S.card : ℝ) ≤ 292*T := by
    have hh : (S.card : ℝ) ≤ (S₀.card : ℝ) +
        2*((∑ v : V, (G.degree v-(q+1)) : ℕ) : ℝ) := by exact_mod_cast hs
    linarith
  refine ⟨S,hS,hsreal,hfree,hcap,?_,?_⟩
  · intro v
    have hh : (G.degree v : ℝ) ≤ ((outsideGraph G S).degree v : ℝ) + S.card := by
      exact_mod_cast hloss v
    have hmv := hmin v
    linarith
  · intro v hv
    have hv₀ : v ∉ S₀ := fun h => hv (hS h)
    exact ⟨hretain v hv,by rw [hretain v hv]; exact hout v hv₀⟩

/-- Actual deficient vertices, relative to baseline degree q+1. -/
noncomputable def deficientVertices (G : SimpleGraph V) (q : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => G.degree v ≤ q

/-- Deficit at least two relative to baseline degree q+1. -/
noncomputable def deepVertices (G : SimpleGraph V) (q : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => G.degree v < q

/-- All newly deficient vertices lie in the core, since outside degrees agree. -/
theorem deficient_count_le (G : SimpleGraph V) (S : Finset V) (q : ℕ) :
    (deficientVertices (outsideGraph G S) q).card ≤ (deficientVertices G q).card + S.card := by
  classical
  have hs : deficientVertices (outsideGraph G S) q ⊆ deficientVertices G q ∪ S := by
    intro v hv
    by_cases hvs : v ∈ S
    · exact Finset.mem_union_right _ hvs
    · apply Finset.mem_union_left
      have hh : (outsideGraph G S).degree v ≤ q := (Finset.mem_filter.mp hv).2
      rw [degree_outside_core G S hvs] at hh
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

/-- The simultaneous outside-degree restriction locates every deep deficit. -/
theorem deep_vertices_subset_core (G : SimpleGraph V) (S : Finset V) (q : ℕ)
    (hout : ∀ v, v ∉ S → (outsideGraph G S).degree v = q ∨
      (outsideGraph G S).degree v = q+1) :
    deepVertices (outsideGraph G S) q ⊆ S := by
  classical
  intro v hv
  by_contra hvs
  have hh : (outsideGraph G S).degree v < q := (Finset.mem_filter.mp hv).2
  rcases hout v hvs with h|h <;> omega

/-- Completion-ready simultaneous numerical core, including deficient and
deep-deficient populations from the same constructed graph. -/
theorem exists_core_292_with_deficiency (G : SimpleGraph V) (S₀ : Finset V) (q : ℕ) (T : ℝ)
    (hc : SupportsEveryFourCycle G S₀)
    (hsize : (S₀.card : ℝ) ≤ 252*T)
    (hexcess : ((∑ v : V, (G.degree v-(q+1)) : ℕ) : ℝ) ≤ 20*T)
    (hmin : ∀ v, (q : ℝ)+1-26*T ≤ G.degree v)
    (hout : ∀ v, v ∉ S₀ → G.degree v = q ∨ G.degree v = q+1)
    (hdef : ((deficientVertices G q).card : ℝ) ≤ (q : ℝ)-1+20*T) :
    ∃ S : Finset V, S₀ ⊆ S ∧ (S.card : ℝ) ≤ 292*T ∧
      NoFourCycle (outsideGraph G S) ∧
      (∀ v, (outsideGraph G S).degree v ≤ q+1) ∧
      (∀ v, (q : ℝ)-318*T ≤ (outsideGraph G S).degree v) ∧
      (∀ v, v ∉ S → (outsideGraph G S).degree v = G.degree v ∧
        ((outsideGraph G S).degree v = q ∨ (outsideGraph G S).degree v = q+1)) ∧
      ((deficientVertices (outsideGraph G S) q).card : ℝ) ≤ (q : ℝ)-1+312*T ∧
      deepVertices (outsideGraph G S) q ⊆ S ∧
      ((deepVertices (outsideGraph G S) q).card : ℝ) ≤ 292*T := by
  obtain ⟨S,hS,hs,hfree,hcap,hminF,houtF⟩ := exists_core_292 G S₀ q T hc hsize hexcess hmin hout
  have hd := deficient_count_le G S q
  have hdreal : ((deficientVertices (outsideGraph G S) q).card : ℝ) ≤
      ((deficientVertices G q).card : ℝ) + S.card := by exact_mod_cast hd
  have hdeep : deepVertices (outsideGraph G S) q ⊆ S :=
    deep_vertices_subset_core G S q (fun v hv => (houtF v hv).2)
  have hdeepreal : ((deepVertices (outsideGraph G S) q).card : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_le_card hdeep
  refine ⟨S,hS,hs,hfree,hcap,hminF,houtF,?_,hdeep,?_⟩ <;> linarith

#print axioms deficient_count_le
#print axioms deep_vertices_subset_core
#print axioms exists_core_292_with_deficiency
#print axioms exists_core_292
#print axioms exists_degree_cap_edges
#print axioms exists_capped_core
#print axioms exists_simultaneous_core
end Erdos60.Core

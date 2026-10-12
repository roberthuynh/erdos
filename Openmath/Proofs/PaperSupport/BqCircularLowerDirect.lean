import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic
/- Owned literal circular all-q lower family after CENTRAL e985e3d7.
Only authenticated generic birth/label/original-Subgraph mechanics are credited.
New circular seed and all-support exclusion are proved below.
Development compilation is not project RESULT:PASS. -/

/- OWN flattened component BqCircularCore.lean. Import lines removed only. -/

/- 
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
/- 
-/

/- 
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open Finset SimpleGraph
namespace BqCircularLowerFamily
variable {V : Type*} [DecidableEq V]

/-- Actual graph extension with one new vertex and precisely the selected old neighbors. -/
def extendGraph (G : SimpleGraph V) (N : Finset V) : SimpleGraph (Option V) where
  Adj x y := match x, y with
    | some v, some w => G.Adj v w
    | none, some v => v ∈ N
    | some v, none => v ∈ N
    | none, none => False
  symm := ⟨by
    intro x y
    cases x <;> cases y <;> simp [G.adj_comm]⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

instance extendGraphDecidable (G : SimpleGraph V) [DecidableRel G.Adj] (N : Finset V) :
    DecidableRel (extendGraph G N).Adj := fun x y => by
  cases x <;> cases y <;> unfold extendGraph <;> infer_instance

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (N : Finset V)

@[simp] theorem degree_none : (extendGraph G N).degree none = N.card := by
  have hn : (extendGraph G N).neighborFinset none = N.image some := by
    ext x
    rw [SimpleGraph.mem_neighborFinset]
    cases x <;> simp [extendGraph]
  rw [← card_neighborFinset_eq_degree, hn, card_image_of_injective _ (Option.some_injective V)]

@[simp] theorem degree_some (v : V) :
    (extendGraph G N).degree (some v) = G.degree v + if v ∈ N then 1 else 0 := by
  have hn : (extendGraph G N).neighborFinset (some v) =
      (G.neighborFinset v).image some ∪ if v ∈ N then {none} else ∅ := by
    ext x
    rw [SimpleGraph.mem_neighborFinset]
    cases x <;> by_cases hv : v ∈ N <;> simp [extendGraph, hv]
  have hd : Disjoint ((G.neighborFinset v).image some)
      (if v ∈ N then {none} else ∅) := by
    split_ifs <;> simp
  rw [← card_neighborFinset_eq_degree, hn, card_union_of_disjoint hd,
    card_image_of_injective _ (Option.some_injective V), card_neighborFinset_eq_degree]
  split_ifs <;> simp

theorem edges_extend : (extendGraph G N).edgeFinset.card = G.edgeFinset.card + N.card := by
  have hs : (∑ x : Option V, (extendGraph G N).degree x) =
      (∑ v : V, G.degree v) + 2 * N.card := by
    rw [Fintype.sum_option]
    simp only [degree_none, degree_some, sum_add_distrib]
    have hind : (∑ v : V, if v ∈ N then 1 else 0) = N.card := by simp
    rw [hind]
    omega
  have h0 := SimpleGraph.sum_degrees_eq_twice_card_edges G
  have h1 := SimpleGraph.sum_degrees_eq_twice_card_edges (extendGraph G N)
  omega

noncomputable instance finiteSubgraphLocallyFinite {W : Type*} [Finite W]
    (K : SimpleGraph W) (H : K.Subgraph) : H.coe.LocallyFinite := fun _ => Fintype.ofFinite _

/-- Absence of arbitrary nonempty original q-regular Subgraphs. -/
def NoRegular (q : ℕ) {W : Type*} [Finite W] (K : SimpleGraph W) : Prop :=
  ¬ ∃ H : K.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q

/-- Actual degree-(q-1) birth preserves arbitrary original-support absence. -/
theorem noRegular_extend (q : ℕ) (hq : 1 ≤ q) (hN : N.card = q - 1) (hG : NoRegular q G) :
    NoRegular q (extendGraph G N) := by
  classical
  rintro ⟨H, hne, hreg⟩
  have hnone : none ∉ H.verts := by
    intro hn
    have h4 : H.degree none = q :=
      (Subgraph.coe_degree H ⟨none, hn⟩).symm.trans (hreg.degree_eq _)
    have hle := H.degree_le none
    rw [degree_none, hN] at hle
    omega
  let H0 : G.Subgraph := {
    verts := {v | some v ∈ H.verts}
    Adj := fun v w => H.Adj (some v) (some w)
    adj_sub := fun h => H.adj_sub h
    edge_vert := fun h => H.edge_vert h
    symm := ⟨by intro v w h; exact h.symm⟩ }
  let : ∀ v : V, Fintype (H0.neighborSet v) := fun _ => Fintype.ofFinite _
  have h0ne : H0.verts.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    cases x with
    | none => exact (hnone hx).elim
    | some v => exact ⟨v, hx⟩
  have hdeg (v : V) : H0.degree v = H.degree (some v) := by
    let f : H0.neighborSet v → H.neighborSet (some v) := fun w => ⟨some w.val, w.property⟩
    have hinj : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact Option.some_injective V (congrArg Subtype.val hxy)
    have hsurj : Function.Surjective f := by
      intro w
      rcases w with ⟨x, hx⟩
      cases x with
      | none => exact (hnone hx.snd_mem).elim
      | some u => exact ⟨⟨u, hx⟩, rfl⟩
    exact Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  apply hG
  refine ⟨H0, h0ne, ?_⟩
  intro v
  rw [Subgraph.coe_degree]
  rw [hdeg v.val]
  exact (Subgraph.coe_degree H ⟨some v.val, v.property⟩).symm.trans (hreg.degree_eq _)


/-- Finite actual slot units force r distinct unsaturated original vertices. -/
theorem capacity_slots {X : Type*} [DecidableEq X] (r : ℕ) (hr : 3 ≤ r)
    (S : Finset X) (g : X → ℕ)
    (hd : ∀ v ∈ S, r ≤ g v ∧ g v ≤ 2*r)
    (hc : r*(r-1)+2 ≤ ∑ v ∈ S, (2*r-g v)) :
    r ≤ (S.filter fun v => g v ≤ 2*r-1).card := by
  have hle : (∑ v ∈ S, (2*r-g v)) ≤
      ∑ v ∈ S, if g v ≤ 2*r-1 then r else 0 := by
    apply sum_le_sum
    intro v hv
    have hvd := hd v hv
    split_ifs <;> omega
  have heq : (∑ v ∈ S, if g v ≤ 2*r-1 then r else 0) =
      r * (S.filter fun v => g v ≤ 2*r-1).card := by
    rw [← sum_filter]
    simp [mul_comm]
  rw [heq] at hle
  by_contra hnot
  have hn : (S.filter fun v => g v ≤ 2*r-1).card ≤ r-1 := by omega
  have hmul := Nat.mul_le_mul_left r hn
  omega

/-- Same actual edges and smaller-shore balance pay opposite capacity. -/
theorem opposite_slots (r a b m c C : ℕ) (hab : a ≤ b)
    (hm : m+c=r*(a+b))
    (hC : C+m=2*r*b) : c ≤ C := by
  have hmul := Nat.mul_le_mul_left r hab
  nlinarith

#print axioms degree_none
#print axioms degree_some
#print axioms edges_extend
#print axioms noRegular_extend
#print axioms capacity_slots
#print axioms opposite_slots
end BqCircularLowerFamily

/- 
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open Finset SimpleGraph
namespace BqCircularLowerFamily
variable {V : Type*} [DecidableEq V] [Fintype V]
variable (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] (N : Finset V)
/-- Strong actual-graph induction data; no extension-success assumption is present. -/
structure Good (A B : Finset V) : Prop where
  disjoint : Disjoint A B
  cover : A ∪ B = univ
  bipartite : G.IsBipartiteWith ↑A ↑B
  balance_left : A.card ≤ B.card + 1
  balance_right : B.card ≤ A.card + 1
  degree_bounds : ∀ v, q-1 ≤ G.degree v ∧ G.degree v ≤ 2*(q-1)
  edge_density : G.edgeFinset.card + ((q-1)*(q-2)+2) = (q-1) * Fintype.card V
  no_regular : NoRegular q G

theorem Good.swap {A B : Finset V} (h : Good q G A B) : Good q G B A where
  disjoint := h.disjoint.symm
  cover := by rw [union_comm, h.cover]
  bipartite := h.bipartite.symm
  balance_left := h.balance_right
  balance_right := h.balance_left
  degree_bounds := h.degree_bounds
  edge_density := h.edge_density
  no_regular := h.no_regular

/-- Once the actual selected neighbors are supplied, every graph invariant is preserved. -/
theorem extend_good_selected (hq : 5 ≤ q) {A B : Finset V} (h : Good q G A B)
    (hsmall : A.card ≤ B.card) (hNB : N ⊆ B) (hN : N.card = q-1)
    (hload : ∀ v ∈ N, G.degree v ≤ 2*(q-1)-1) :
    Good q (extendGraph G N) (insert none (A.image some)) (B.image some) := by
  have hAc : (insert none (A.image some)).card = A.card + 1 := by
    rw [card_insert_of_notMem (by simp), card_image_of_injective _ (Option.some_injective V)]
  have hBc : (B.image some).card = B.card :=
    card_image_of_injective _ (Option.some_injective V)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro x hxA hxB
    cases x with
    | none => simp at hxB
    | some v =>
      exact Finset.disjoint_left.mp h.disjoint (by simpa using hxA) (by simpa using hxB)
  · ext x
    cases x with
    | none => simp
    | some v =>
      have hv : v ∈ A ∪ B := by rw [h.cover]; exact mem_univ _
      simpa using hv
  · refine ⟨?_, ?_⟩
    · rw [disjoint_coe]
      apply Finset.disjoint_left.mpr
      intro x hxA hxB
      cases x with
      | none => simp at hxB
      | some v => exact Finset.disjoint_left.mp h.disjoint (by simpa using hxA) (by simpa using hxB)
    · intro x y hxy
      cases x with
      | none =>
        cases y with
        | none => exact hxy.elim
        | some v => exact Or.inl ⟨by simp, by simpa using hNB hxy⟩
      | some v =>
        cases y with
        | none => exact Or.inr ⟨by simpa using hNB hxy, by simp⟩
        | some w => simpa using h.bipartite.mem_of_adj hxy
  · rw [hAc, hBc]
    omega
  · rw [hAc, hBc]
    have := h.balance_right
    omega
  · intro x
    cases x with
    | none => simp [hN]; omega
    | some v =>
      rw [degree_some]
      have hd := h.degree_bounds v
      by_cases hv : v ∈ N
      · have hl := hload v hv
        simp [hv]
        omega
      · simp [hv]
        omega
  · rw [edges_extend, hN, Fintype.card_option]
    have := h.edge_density
    nlinarith
  · exact noRegular_extend G N q (by omega) hN h.no_regular


/-- The required neighbor CARDINALITY follows from actual shore degree sums. -/
theorem eligible_card (hq : 5 ≤ q) {A B : Finset V}
    (h : Good q G A B) (hsmall : A.card ≤ B.card) :
    q-1 ≤ (B.filter fun v => G.degree v ≤ 2*(q-1)-1).card := by
  have hcard : A.card+B.card = Fintype.card V := by
    rw [← card_union_of_disjoint h.disjoint, h.cover, card_univ]
  have hdensity : G.edgeFinset.card + ((q-1)*(q-2)+2) = (q-1)*(A.card+B.card) := by
    rw [hcard]
    exact h.edge_density
  have hcapacity : (∑ v ∈ B, (2*(q-1)-G.degree v))+G.edgeFinset.card =
      2*(q-1)*B.card := by
    calc
      _ = (∑ v ∈ B, (2*(q-1)-G.degree v)) + ∑ v ∈ B, G.degree v := by
        rw [SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' h.bipartite]
      _ = ∑ _v ∈ B, 2*(q-1) := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro v _
        exact Nat.sub_add_cancel (h.degree_bounds v).2
      _ = 2*(q-1)*B.card := by simp [mul_comm]
  have hcap := opposite_slots (q-1) A.card B.card G.edgeFinset.card
    ((q-1)*(q-2)+2) (∑ v ∈ B, (2*(q-1)-G.degree v)) hsmall hdensity hcapacity
  apply capacity_slots (q-1) (by omega) B (fun v => G.degree v)
    (fun v _ => h.degree_bounds v)
  simpa [Nat.sub_sub] using hcap

#print axioms Good.swap
#print axioms extend_good_selected
#print axioms eligible_card
end BqCircularLowerFamily

/- 
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
open Finset SimpleGraph
namespace BqCircularLowerFamily
variable {V : Type*}

def leastLabels (r : ℕ) (S : Finset V) (label : V → ℕ) : Finset ℕ :=
  (((S.image label).sort (· ≤ ·)).take r).toFinset

def leastNeighbors (r : ℕ) (S : Finset V) (label : V → ℕ) : Finset V :=
  S.filter fun v => label v ∈ leastLabels r S label

theorem leastLabels_subset (r : ℕ) (S : Finset V) (label : V → ℕ) :
    leastLabels r S label ⊆ S.image label := by
  intro x hx
  have ht : x ∈ ((S.image label).sort (· ≤ ·)).take r := by
    simpa [leastLabels] using hx
  have hsort := List.mem_of_mem_take ht
  exact (mem_sort (· ≤ ·)).mp hsort

theorem leastLabels_card (r : ℕ) (S : Finset V) (label : V → ℕ)
    (hinj : Function.Injective label) (hcard : r ≤ S.card) :
    (leastLabels r S label).card = r := by
  have hnodup := ((S.image label).sort_nodup (· ≤ ·)).take (i := r)
  unfold leastLabels
  rw [List.toFinset_card_of_nodup hnodup, List.length_take,
      length_sort, card_image_of_injective _ hinj, Nat.min_eq_left hcard]

theorem leastNeighbors_image (r : ℕ) (S : Finset V) (label : V → ℕ) :
    (leastNeighbors r S label).image label = leastLabels r S label := by
  ext x
  constructor
  · intro hx
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hx
    exact (mem_filter.mp hv).2
  · intro hx
    have hxs := leastLabels_subset r S label hx
    obtain ⟨v,hv,hvx⟩ := mem_image.mp hxs
    exact mem_image.mpr ⟨v,mem_filter.mpr ⟨hv,hvx ▸ hx⟩,hvx⟩

theorem leastNeighbors_card (r : ℕ) (S : Finset V) (label : V → ℕ)
    (hinj : Function.Injective label) (hcard : r ≤ S.card) :
    (leastNeighbors r S label).card = r := by
  rw [← card_image_of_injective _ hinj, leastNeighbors_image]
  exact leastLabels_card r S label hinj hcard

theorem leastNeighbors_le_omitted (r : ℕ) (S : Finset V) (label : V → ℕ)
    (v w : V) (hv : v ∈ leastNeighbors r S label) (hw : w ∈ S)
    (hwn : w ∉ leastNeighbors r S label) : label v ≤ label w := by
  let L := (S.image label).sort (· ≤ ·)
  have hvT : label v ∈ L.take r := by simpa [leastNeighbors,leastLabels,L] using (mem_filter.mp hv).2
  have hvL : label v ∈ L := List.mem_of_mem_take hvT
  have hwL : label w ∈ L := (mem_sort (· ≤ ·)).mpr (mem_image.mpr ⟨w,hw,rfl⟩)
  have hwT : label w ∉ L.take r := by
    intro ht
    apply hwn
    exact mem_filter.mpr ⟨hw,by simpa [leastLabels,L] using ht⟩
  have hvi := (List.mem_take_iff_idxOf_lt hvL).mp hvT
  have hwi : r ≤ L.idxOf (label w) := by
    have hn := mt (List.mem_take_iff_idxOf_lt hwL).mpr hwT
    omega
  have hiv := List.idxOf_lt_length_of_mem hvL
  have hiw := List.idxOf_lt_length_of_mem hwL
  have hsort : L.Pairwise (· ≤ ·) := (S.image label).pairwise_sort (· ≤ ·)
  have hle : L.get ⟨L.idxOf (label v),hiv⟩ ≤ L.get ⟨L.idxOf (label w),hiw⟩ :=
    hsort.rel_get_of_le (by change L.idxOf (label v) ≤ L.idxOf (label w); omega)
  simpa only [List.idxOf_get] using hle

#print axioms leastLabels_subset
#print axioms leastLabels_card
#print axioms leastNeighbors_card
#print axioms leastNeighbors_le_omitted
end BqCircularLowerFamily

/- 
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
open Finset SimpleGraph
namespace BqCircularLowerFamily

structure Labeling (V : Type*) [Fintype V] where
  label : V → ℕ
  injective : Function.Injective label
  bounded : ∀ v, label v < Fintype.card V

def Labeling.extend {V : Type*} [Fintype V] (L : Labeling V) : Labeling (Option V) where
  label := fun x => match x with
    | none => Fintype.card V
    | some v => L.label v
  injective := by
    intro x y hxy
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some v =>
        have hv := L.bounded v
        change Fintype.card V = L.label v at hxy
        omega
    | some v =>
      cases y with
      | none =>
        have hv := L.bounded v
        change L.label v = Fintype.card V at hxy
        omega
      | some w => exact congrArg some (L.injective hxy)
  bounded := by
    intro x
    rw [Fintype.card_option]
    cases x with
    | none => exact Nat.lt_succ_self _
    | some v => exact (L.bounded v).trans (Nat.lt_succ_self _)

theorem Labeling.image_range {V : Type*} [Fintype V] (L : Labeling V) :
    univ.image L.label = range (Fintype.card V) := by
  have hsub : univ.image L.label ⊆ range (Fintype.card V) := by
    intro k hk
    obtain ⟨v,_hv,rfl⟩ := mem_image.mp hk
    exact mem_range.mpr (L.bounded v)
  apply eq_of_subset_of_card_le hsub
  rw [card_range,card_image_of_injective _ L.injective,card_univ]

#print axioms Labeling.extend
#print axioms Labeling.image_range
end BqCircularLowerFamily

/- 
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 4000
open Finset SimpleGraph
namespace BqCircularLowerFamily
variable {V : Type*} [Fintype V] [DecidableEq V]

def nextNeighbors (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (L : Labeling V) : Finset V :=
  let opposite := if A.card ≤ B.card then B else A
  leastNeighbors (q-1) (opposite.filter fun v => G.degree v ≤ 2*(q-1)-1) L.label

def nextA (A B : Finset V) : Finset (Option V) :=
  if A.card ≤ B.card then insert none (A.image some) else A.image some

def nextB (A B : Finset V) : Finset (Option V) :=
  if A.card ≤ B.card then B.image some else insert none (B.image some)

theorem literalNext_good (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (L : Labeling V) (hq : 5 ≤ q) (h : Good q G A B) :
    Good q (extendGraph G (nextNeighbors q G A B L)) (nextA A B) (nextB A B) := by
  by_cases hsmall : A.card ≤ B.card
  · let S := B.filter fun v => G.degree v ≤ 2*(q-1)-1
    have hN : nextNeighbors q G A B L = leastNeighbors (q-1) S L.label := by
      simp [nextNeighbors,hsmall,S]
    have hNS : nextNeighbors q G A B L ⊆ S := by
      rw [hN]
      exact filter_subset _ S
    have hNB : nextNeighbors q G A B L ⊆ B := by
      intro v hv
      exact (mem_filter.mp (hNS hv)).1
    have hNc : (nextNeighbors q G A B L).card = q-1 := by
      rw [hN]
      exact leastNeighbors_card (q-1) S L.label L.injective (eligible_card q G hq h hsmall)
    have hload : ∀ v ∈ nextNeighbors q G A B L, G.degree v ≤ 2*(q-1)-1 := by
      intro v hv
      exact (mem_filter.mp (hNS hv)).2
    have hn := extend_good_selected q G (nextNeighbors q G A B L) hq h hsmall hNB hNc hload
    simpa [nextA,nextB,hsmall] using hn
  · have hsmall' : B.card ≤ A.card := by omega
    let S := A.filter fun v => G.degree v ≤ 2*(q-1)-1
    have hN : nextNeighbors q G A B L = leastNeighbors (q-1) S L.label := by
      simp [nextNeighbors,hsmall,S]
    have hNS : nextNeighbors q G A B L ⊆ S := by
      rw [hN]
      exact filter_subset _ S
    have hNA : nextNeighbors q G A B L ⊆ A := by
      intro v hv
      exact (mem_filter.mp (hNS hv)).1
    have hNc : (nextNeighbors q G A B L).card = q-1 := by
      rw [hN]
      exact leastNeighbors_card (q-1) S L.label L.injective (eligible_card q G hq h.swap hsmall')
    have hload : ∀ v ∈ nextNeighbors q G A B L, G.degree v ≤ 2*(q-1)-1 := by
      intro v hv
      exact (mem_filter.mp (hNS hv)).2
    have hn := extend_good_selected q G (nextNeighbors q G A B L) hq h.swap hsmall' hNA hNc hload
    simpa [nextA,nextB,hsmall] using hn.swap

theorem nextNeighbors_card (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (L : Labeling V) (hq : 5 ≤ q) (h : Good q G A B) :
    (nextNeighbors q G A B L).card = q-1 := by
  by_cases hsmall : A.card ≤ B.card
  · simpa [nextNeighbors,hsmall] using
      leastNeighbors_card (q-1) (B.filter fun v => G.degree v ≤ 2*(q-1)-1)
        L.label L.injective (eligible_card q G hq h hsmall)
  · have hrev : B.card ≤ A.card := by omega
    simpa [nextNeighbors,hsmall] using
      leastNeighbors_card (q-1) (A.filter fun v => G.degree v ≤ 2*(q-1)-1)
        L.label L.injective (eligible_card q G hq h.swap hrev)

omit [DecidableEq V] in
theorem nextNeighbors_least (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (L : Labeling V) (v w : V)
    (hv : v ∈ nextNeighbors q G A B L)
    (hw : w ∈ (if A.card ≤ B.card then B else A).filter
      fun x => G.degree x ≤ 2*(q-1)-1)
    (hwn : w ∉ nextNeighbors q G A B L) : L.label v ≤ L.label w := by
  exact leastNeighbors_le_omitted (q-1)
    ((if A.card ≤ B.card then B else A).filter fun x => G.degree x ≤ 2*(q-1)-1)
    L.label v w hv hw hwn

omit [DecidableEq V] in
@[simp] theorem extend_label_old (L : Labeling V) (v : V) :
    L.extend.label (some v) = L.label v := rfl
omit [DecidableEq V] in
@[simp] theorem extend_label_new (L : Labeling V) :
    L.extend.label none = Fintype.card V := rfl

#print axioms literalNext_good
#print axioms nextNeighbors_card
#print axioms nextNeighbors_least
end BqCircularLowerFamily

/- OWN flattened component BqCircularIntervals.lean. Import lines removed only. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
open Finset SimpleGraph
namespace BqCircularLowerFamily

/-- The literal ordinary circular missing interval, with original indices. -/
def missing (z i : ℕ) : Finset ℕ := (range z).image fun t => (2*i+t) % (2*z+1)

theorem mod_once (a m : ℕ) (ha : a < 2*m) :
    a % m = a ∨ a = a % m + m := by
  by_cases h : a < m
  · exact Or.inl (Nat.mod_eq_of_lt h)
  · right
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

theorem missing_lt {z i x : ℕ} (hx : x ∈ missing z i) : x < 2*z+1 := by
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hx
  exact Nat.mod_lt _ (by omega)

theorem missing_card (z i : ℕ) (hi : i < z) : (missing z i).card = z := by
  unfold missing
  rw [card_image_of_injOn, card_range]
  intro t ht u hu heq
  change (2*i+t) % (2*z+1) = (2*i+u) % (2*z+1) at heq
  have ht' := mem_range.mp ht
  have hu' := mem_range.mp hu
  have hmt := mod_once (2*i+t) (2*z+1) (by omega)
  have hmu := mod_once (2*i+u) (2*z+1) (by omega)
  rcases hmt with hmt | hmt <;> rcases hmu with hmu | hmu <;> omega

/-- Backward original circular distance from start2i to the common column x. -/
def back (z i x : ℕ) : ℕ := if 2*i ≤ x then x-2*i else x+(2*z+1)-2*i

theorem back_lt {z i x : ℕ} (hi : i < z) (hx : x ∈ missing z i) :
    back z i x < z := by
  obtain ⟨t, ht, htx⟩ := mem_image.mp hx
  have ht' := mem_range.mp ht
  have hmod := mod_once (2*i+t) (2*z+1) (by omega)
  have hx' : x < 2*z+1 := by rw [← htx]; exact Nat.mod_lt _ (by omega)
  unfold back
  split_ifs <;> rcases hmod with hmod | hmod <;> omega

theorem back_inj_rows {z x i j : ℕ} (hi : i < z) (hj : j < z)
    (_hx : x < 2*z+1) (heq : back z i x = back z j x) : i = j := by
  unfold back at heq
  split_ifs at heq <;> omega

theorem back_no_adjacent {z x i j : ℕ} (hi : i < z) (hj : j < z)
    (_hx : x < 2*z+1) : back z i x + 1 ≠ back z j x := by
  intro h
  unfold back at h
  split_ifs at h <;> omega

theorem back_inj_columns {z i x y : ℕ} (hi : i < z)
    (hx : x < 2*z+1) (hy : y < 2*z+1)
    (heq : back z i x = back z i y) : x = y := by
  unfold back at heq
  split_ifs at heq <;> omega

/-- Two intersecting short intervals use the SAME lift at both original columns. -/
theorem back_cross_sum {z i j x y : ℕ} (hi : i < z) (hj : j < z)
    (_hx : x < 2*z+1) (_hy : y < 2*z+1)
    (hix : back z i x < z) (hjx : back z j x < z)
    (hiy : back z i y < z) (hjy : back z j y < z) :
    back z i x + back z j y = back z j x + back z i y := by
  have eqn (k v : ℕ) (hk : k < z) :
      2*k+back z k v = v ∨ 2*k+back z k v = v+(2*z+1) := by
    unfold back
    split_ifs <;> omega
  have eix := eqn i x hi
  have ejx := eqn j x hj
  have eiy := eqn i y hi
  have ejy := eqn j y hj
  rcases eix with eix | eix <;> rcases ejx with ejx | ejx <;>
    rcases eiy with eiy | eiy <;> rcases ejy with ejy | ejy <;> omega

/-- Uniform actual common-missing cardinality, for every chosen forced-row set.
The T nonempty premise is supplied by a proper active shore in the seed proof. -/
theorem common_missing_card (z : ℕ) (I T : Finset ℕ)
    (hI : ∀ i ∈ I, i < z) (hI2 : 2 ≤ I.card)
    (hT : ∀ x ∈ T, x < 2*z+1) (hTne : T.Nonempty)
    (hmiss : ∀ i ∈ I, ∀ x ∈ T, x ∈ missing z i) : T.card + I.card ≤ z := by
  obtain ⟨x, hxT⟩ := hTne
  let S := I.image fun i => back z i x
  have hSc : S.card = I.card := by
    apply card_image_of_injOn
    intro i hi j hj heq
    exact back_inj_rows (hI i hi) (hI j hj) (hT x hxT) heq
  have hSne : S.Nonempty := by
    apply card_pos.mp
    rw [hSc]
    omega
  let lo := S.min' hSne
  let high := S.max' hSne
  have hlo : lo ∈ S := S.min'_mem hSne
  have hhigh : high ∈ S := S.max'_mem hSne
  have hle : lo ≤ high := S.min'_le_max' hSne
  have hlt : lo < high := by
    by_contra hn
    have heq : lo = high := by omega
    have hsub : S ⊆ {lo} := by
      intro v hv
      have h0 := S.min'_le v hv
      have h1 := S.le_max' v hv
      simp only [mem_singleton]
      change lo ≤ v at h0
      change v ≤ high at h1
      omega
    have hc := card_le_card hsub
    simp only [card_singleton] at hc
    omega
  have hhole : lo+1 ∉ S := by
    intro hh
    obtain ⟨i, hi, hix⟩ := mem_image.mp hlo
    obtain ⟨j, hj, hjx⟩ := mem_image.mp hh
    apply back_no_adjacent (hI i hi) (hI j hj) (hT x hxT)
    omega
  have hSsub : S ⊆ (Icc lo high).erase (lo+1) := by
    intro v hv
    have h0 := S.min'_le v hv
    have h1 := S.le_max' v hv
    have hne : v ≠ lo+1 := by intro heq; exact hhole (heq ▸ hv)
    exact mem_erase.mpr ⟨hne, mem_Icc.mpr ⟨h0, h1⟩⟩
  have hSbound : I.card ≤ high-lo := by
    have hc := card_le_card hSsub
    have hh := card_erase_add_one (s := Icc lo high) (a := lo+1)
      (mem_Icc.mpr (by omega : lo ≤ lo+1 ∧ lo+1 ≤ high))
    rw [Nat.card_Icc] at hh
    omega
  obtain ⟨i, hi, hix⟩ := mem_image.mp hhigh
  obtain ⟨j, hj, hjx⟩ := mem_image.mp hlo
  have hi_lt := hI i hi
  have hj_lt := hI j hj
  have hhigh_lt : high < z := by rw [← hix]; exact back_lt hi_lt (hmiss i hi x hxT)
  have himage : (T.image fun y => back z i y).card = T.card := by
    apply card_image_of_injOn
    intro y hy v hv heq
    exact back_inj_columns hi_lt (hT y hy) (hT v hv) heq
  have hTsub : (T.image fun y => back z i y) ⊆ Icc (high-lo) (z-1) := by
    intro v hv
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hv
    have hay := back_lt hi_lt (hmiss i hi y hy)
    have hby := back_lt hj_lt (hmiss j hj y hy)
    have hxlt := hT x hxT
    have hylt := hT y hy
    have hax := back_lt hi_lt (hmiss i hi x hxT)
    have hbx := back_lt hj_lt (hmiss j hj x hxT)
    have hc := back_cross_sum hi_lt hj_lt hxlt hylt hax hbx hay hby
    rw [hix, hjx] at hc
    exact mem_Icc.mpr (by omega)
  have hTc := card_le_card hTsub
  rw [himage, Nat.card_Icc] at hTc
  omega

#print axioms missing_card
#print axioms back_cross_sum
#print axioms common_missing_card
end BqCircularLowerFamily

/- OWN flattened component BqCircularSeed.lean. Import lines removed only. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open Finset SimpleGraph
namespace BqCircularLowerFamily

def seedAdj (q : ℕ) (i : Fin (2*(q-2)+1)) (j : Fin (2*(q-2)+2)) : Prop :=
  if i.val < q-2 then j.val ∉ missing (q-2) i.val
  else if i.val < 2*(q-2) then True else j.val < 2*(q-2)+1

instance seedAdjDecidable (q : ℕ) (i : Fin (2*(q-2)+1)) (j : Fin (2*(q-2)+2)) :
    Decidable (seedAdj q i j) := by unfold seedAdj; infer_instance

def seedGraph (q : ℕ) : SimpleGraph (Fin (2*(q-2)+1) ⊕ Fin (2*(q-2)+2)) where
  Adj x y := match x,y with
    | .inl i, .inr j => seedAdj q i j
    | .inr j, .inl i => seedAdj q i j
    | _,_ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> simp⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

instance seedGraphDecidable (q : ℕ) : DecidableRel (seedGraph q).Adj := by
  intro x y
  cases x <;> cases y <;> unfold seedGraph <;> infer_instance

def seedRowDegree (q : ℕ) (Q : Finset (Fin (2*(q-2)+2)))
    (i : Fin (2*(q-2)+1)) : ℕ := (Q.filter fun j => seedAdj q i j).card

def seedColumnDegree (q : ℕ) (P : Finset (Fin (2*(q-2)+1)))
    (j : Fin (2*(q-2)+2)) : ℕ := (P.filter fun i => seedAdj q i j).card

theorem fin_lt_card (a b : ℕ) (hab : b ≤ a) :
    (univ.filter fun i : Fin a => i.val < b).card = b := by
  have heq : (univ.filter fun i : Fin a => i.val < b).image Fin.val = range b := by
    ext t
    constructor
    · intro ht
      obtain ⟨i, hi, rfl⟩ := mem_image.mp ht
      exact mem_range.mpr (mem_filter.mp hi).2
    · intro ht
      have ht' := mem_range.mp ht
      exact mem_image.mpr ⟨⟨t, lt_of_lt_of_le ht' hab⟩, by simp [ht'], rfl⟩
  have hc := card_image_of_injective
    (univ.filter fun i : Fin a => i.val < b) Fin.val_injective
  rw [heq, card_range] at hc
  exact hc.symm

theorem fin_ge_card (a b : ℕ) (hab : b ≤ a) :
    (univ.filter fun i : Fin a => b ≤ i.val).card = a-b := by
  have heq : (univ.filter fun i : Fin a => ¬ i.val < b) =
      (univ.filter fun i : Fin a => b ≤ i.val) := by ext i; simp
  have hc := card_filter_add_card_filter_not (s := univ (α := Fin a)) (p := fun i => i.val < b)
  rw [fin_lt_card a b hab, heq, card_univ, Fintype.card_fin] at hc
  omega

theorem fin_between_card (a b c : ℕ) (_hbc : b ≤ c) (hca : c ≤ a) :
    (univ.filter fun i : Fin a => b ≤ i.val ∧ i.val < c).card = c-b := by
  have heq : (univ.filter fun i : Fin a => b ≤ i.val ∧ i.val < c).image Fin.val = Ico b c := by
    ext t
    constructor
    · intro ht
      obtain ⟨i, hi, rfl⟩ := mem_image.mp ht
      exact mem_Ico.mpr (mem_filter.mp hi).2
    · intro ht
      obtain ⟨hb, hc⟩ := mem_Ico.mp ht
      exact mem_image.mpr ⟨⟨t, lt_of_lt_of_le hc hca⟩, by simp [hb,hc], rfl⟩
  have hc := card_image_of_injective
    (univ.filter fun i : Fin a => b ≤ i.val ∧ i.val < c) Fin.val_injective
  rw [heq, Nat.card_Ico] at hc
  exact hc.symm

theorem missing_fin_card (q : ℕ) (i : Fin (2*(q-2)+1)) (hi : i.val < q-2) :
    (univ.filter fun j : Fin (2*(q-2)+2) => j.val ∈ missing (q-2) i.val).card = q-2 := by
  have heq : (univ.filter fun j : Fin (2*(q-2)+2) => j.val ∈ missing (q-2) i.val).image Fin.val =
      missing (q-2) i.val := by
    ext t
    constructor
    · intro ht
      obtain ⟨j, hj, rfl⟩ := mem_image.mp ht
      exact (mem_filter.mp hj).2
    · intro ht
      have hlt := missing_lt ht
      exact mem_image.mpr ⟨⟨t, by omega⟩, by simp [ht], rfl⟩
  have hc := card_image_of_injective
    (univ.filter fun j : Fin (2*(q-2)+2) => j.val ∈ missing (q-2) i.val) Fin.val_injective
  rw [heq, missing_card (q-2) i.val hi] at hc
  exact hc.symm

theorem seed_forced_degree (q : ℕ) (hq : 5 ≤ q) (i : Fin (2*(q-2)+1))
    (hi : i.val < q-2) : seedRowDegree q univ i = q := by
  have hc := card_filter_add_card_filter_not
    (s := univ (α := Fin (2*(q-2)+2))) (p := fun j => j.val ∈ missing (q-2) i.val)
  rw [missing_fin_card q i hi, card_univ, Fintype.card_fin] at hc
  unfold seedRowDegree
  simp only [seedAdj, hi, if_true]
  omega

theorem seed_row_degree (q : ℕ) (hq : 5 ≤ q) (i : Fin (2*(q-2)+1)) :
    seedRowDegree q univ i =
      if i.val < q-2 then q else if i.val < 2*(q-2) then 2*(q-2)+2 else 2*(q-2)+1 := by
  by_cases hi : i.val < q-2
  · simp only [hi, if_true]
    exact seed_forced_degree q hq i hi
  · by_cases hj : i.val < 2*(q-2)
    · simp [seedRowDegree, seedAdj, hi, hj]
    · simp only [hi, hj, if_false]
      unfold seedRowDegree
      simp only [seedAdj, hi, hj, if_false]
      exact fin_lt_card _ _ (by omega)

theorem seed_reserved_adj (q : ℕ) (i : Fin (2*(q-2)+1)) (hi : i.val < 2*(q-2)) :
    seedAdj q i ⟨2*(q-2)+1, by omega⟩ := by
  by_cases h0 : i.val < q-2
  · simp only [seedAdj, h0, if_true]
    intro h
    have := missing_lt h
    omega
  · simp [seedAdj, h0, hi]

theorem seed_column_bounds (q : ℕ) (hq : 5 ≤ q) (j : Fin (2*(q-2)+2)) :
    q-1 ≤ seedColumnDegree q univ j ∧ seedColumnDegree q univ j ≤ 2*(q-1) := by
  have hu : seedColumnDegree q univ j ≤ 2*(q-2)+1 := by
    unfold seedColumnDegree
    exact card_filter_le _ _ |>.trans_eq (by simp)
  refine ⟨?_, by omega⟩
  by_cases hj : j.val < 2*(q-2)+1
  · have hsub : (univ.filter fun i : Fin (2*(q-2)+1) => q-2 ≤ i.val) ⊆
        (univ.filter fun i => seedAdj q i j) := by
      intro i hi
      have hi' := (mem_filter.mp hi).2
      apply mem_filter.mpr ⟨mem_univ _, ?_⟩
      simp only [seedAdj, show ¬ i.val < q-2 by omega, if_false]
      split_ifs; simp_all
    have hc := card_le_card hsub
    rw [fin_ge_card _ _ (by omega)] at hc
    change _ ≤ seedColumnDegree q univ j at hc
    omega
  · have hjval : j.val = 2*(q-2)+1 := by have := j.isLt; omega
    have hsub : (univ.filter fun i : Fin (2*(q-2)+1) => i.val < 2*(q-2)) ⊆
        (univ.filter fun i => seedAdj q i j) := by
      intro i hi
      have hi' := (mem_filter.mp hi).2
      apply mem_filter.mpr ⟨mem_univ _, ?_⟩
      have heq : j = ⟨2*(q-2)+1, by omega⟩ := Fin.ext hjval
      rw [heq]
      exact seed_reserved_adj q i hi'
    have hc := card_le_card hsub
    rw [fin_lt_card _ _ (by omega)] at hc
    change _ ≤ seedColumnDegree q univ j at hc
    omega

#print axioms seed_forced_degree
#print axioms seed_row_degree
#print axioms seed_column_bounds
end BqCircularLowerFamily

/- OWN flattened component BqCircularSupport.lean. Import lines removed only. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open Finset SimpleGraph
namespace BqCircularLowerFamily

theorem seed_w_not_reserved (q : ℕ) :
    ¬ seedAdj q ⟨2*(q-2), by omega⟩ ⟨2*(q-2)+1, by omega⟩ := by
  simp only [seedAdj]
  split_ifs <;> omega

/-- All active-support sizes, using only actual host neighbors in the same shore. -/
theorem seed_no_balanced_support (q : ℕ) (hq : 5 ≤ q)
    (P : Finset (Fin (2*(q-2)+1))) (Q : Finset (Fin (2*(q-2)+2)))
    (hPne : P.Nonempty) (hbalance : P.card = Q.card)
    (hrows : ∀ i ∈ P, q ≤ seedRowDegree q Q i) : False := by
  let PF := P.filter fun i => i.val < q-2
  have hPF (i : Fin (2*(q-2)+1)) : i ∈ PF ↔ i ∈ P ∧ i.val < q-2 := by simp [PF]
  have hwhole (i : Fin (2*(q-2)+1)) (hiP : i ∈ P) (hi : i.val < q-2) :
      (univ.filter fun j => seedAdj q i j) ⊆ Q := by
    let R := univ.filter fun j => seedAdj q i j
    let S := Q.filter fun j => seedAdj q i j
    have hsub : S ⊆ R := by intro j hj; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hj).2⟩
    have hR : R.card = q := seed_forced_degree q hq i hi
    have hS : q ≤ S.card := hrows i hiP
    have heq : S = R := eq_of_subset_of_card_le hsub (by omega)
    intro j hj
    have hjs : j ∈ S := heq.symm ▸ hj
    exact (mem_filter.mp hjs).1
  have hsize : q ≤ P.card := by
    obtain ⟨i, hi⟩ := hPne
    have hlow := hrows i hi
    have hle : seedRowDegree q Q i ≤ Q.card := card_filter_le _ _
    omega
  have hPupper : P.card ≤ PF.card+(q-2)+1 := by
    have hsub : (P.filter fun i => ¬ i.val < q-2) ⊆
        (univ.filter fun i : Fin (2*(q-2)+1) => q-2 ≤ i.val) := by
      intro i hi
      exact mem_filter.mpr ⟨mem_univ _, by have := (mem_filter.mp hi).2; omega⟩
    have hle := card_le_card hsub
    rw [fin_ge_card _ _ (by omega)] at hle
    have hc := card_filter_add_card_filter_not (s := P) (p := fun i => i.val < q-2)
    change PF.card + _ = P.card at hc
    omega
  have hPFpos : 0 < PF.card := by omega
  have hPFne : PF.Nonempty := card_pos.mp hPFpos
  by_cases hsingle : PF.card = 1
  · have hPc : P.card = q := by omega
    let w : Fin (2*(q-2)+1) := ⟨2*(q-2), by omega⟩
    let h : Fin (2*(q-2)+2) := ⟨2*(q-2)+1, by omega⟩
    have hw : w ∈ P := by
      by_contra hnot
      let U := univ.filter fun i : Fin (2*(q-2)+1) => q-2 ≤ i.val ∧ i.val < 2*(q-2)
      have hUc : U.card = q-2 := by
        dsimp [U]
        rw [fin_between_card _ _ _ (by omega) (by omega)]
        omega
      have hsub : P ⊆ PF ∪ U := by
        intro i hi
        by_cases hif : i.val < q-2
        · exact mem_union.mpr (Or.inl ((hPF i).mpr ⟨hi, hif⟩))
        · have hne : i.val ≠ 2*(q-2) := by
            intro heq
            have hiw : i = w := Fin.ext heq
            exact hnot (hiw ▸ hi)
          have hil := i.isLt
          exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨mem_univ _, by omega⟩))
      have hc := card_le_card hsub
      have hu := card_union_le PF U
      omega
    obtain ⟨i, hiPF⟩ := hPFne
    obtain ⟨hiP, hiF⟩ := (hPF i).mp hiPF
    have hh : h ∈ Q := hwhole i hiP hiF (mem_filter.mpr
      ⟨mem_univ _, seed_reserved_adj q i (by omega)⟩)
    have hsub : (Q.filter fun j => seedAdj q w j) ⊆ Q.erase h := by
      intro j hj
      obtain ⟨hjQ, haj⟩ := mem_filter.mp hj
      apply mem_erase.mpr ⟨?_, hjQ⟩
      intro heq
      subst j
      exact seed_w_not_reserved q haj
    have hc := card_le_card hsub
    rw [card_erase_of_mem hh] at hc
    have hl := hrows w hw
    change q ≤ (Q.filter fun j => seedAdj q w j).card at hl
    omega
  · have hPF2 : 2 ≤ PF.card := by omega
    let T := univ.filter fun j : Fin (2*(q-2)+2) => j ∉ Q
    have hTc : Q.card+T.card = 2*(q-2)+2 := by
      simpa [T] using card_filter_add_card_filter_not
        (s := univ (α := Fin (2*(q-2)+2))) (p := fun j => j ∈ Q)
    have hQbound : Q.card ≤ 2*(q-2)+1 := by
      have := card_le_univ P
      simp only [Fintype.card_fin] at this
      omega
    have hTne : T.Nonempty := card_pos.mp (by omega)
    have hmiss (i : Fin (2*(q-2)+1)) (hi : i ∈ PF)
        (j : Fin (2*(q-2)+2)) (hj : j ∈ T) : j.val ∈ missing (q-2) i.val := by
      obtain ⟨hiP, hiF⟩ := (hPF i).mp hi
      have hjQ := (mem_filter.mp hj).2
      have hnot : ¬ seedAdj q i j := by
        intro haj
        exact hjQ (hwhole i hiP hiF (mem_filter.mpr ⟨mem_univ _, haj⟩))
      simpa [seedAdj, hiF] using hnot
    let I := PF.image Fin.val
    let J := T.image Fin.val
    have hIc : I.card = PF.card := card_image_of_injective _ Fin.val_injective
    have hJc : J.card = T.card := card_image_of_injective _ Fin.val_injective
    have hIlt : ∀ i ∈ I, i < q-2 := by
      intro i hi
      obtain ⟨u, hu, rfl⟩ := mem_image.mp hi
      exact ((hPF u).mp hu).2
    have hJne : J.Nonempty := hTne.image Fin.val
    have hIJ : ∀ i ∈ I, ∀ j ∈ J, j ∈ missing (q-2) i := by
      intro i hi j hj
      obtain ⟨u, hu, rfl⟩ := mem_image.mp hi
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hj
      exact hmiss u hu v hv
    have hJlt : ∀ j ∈ J, j < 2*(q-2)+1 := by
      obtain ⟨i, hi⟩ := hPFne
      intro j hj
      exact missing_lt (hIJ i.val (mem_image.mpr ⟨i, hi, rfl⟩) j hj)
    have hc := common_missing_card (q-2) I J hIlt (by omega) hJlt hJne hIJ
    omega

#print axioms seed_no_balanced_support
end BqCircularLowerFamily

/- OWN flattened component BqCircularMatrix.lean. Import lines removed only. -/
/- Original-edge matrix/Subgraph bridge adapted from authenticated generic source
0ab7e9f4. The support exclusion supplier is the new proved circular lemma,
not the old five-missing seed theorem. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
open Finset SimpleGraph
namespace BqCircularLowerFamily
variable (q : ℕ)
def matrixRowDegree (F : Finset (Fin (2*(q-2)+1) × Fin (2*(q-2)+2))) (i : Fin (2*(q-2)+1)) : ℕ :=
  (F.filter fun x => x.1 = i).card

def matrixColumnDegree (F : Finset (Fin (2*(q-2)+1) × Fin (2*(q-2)+2))) (j : Fin (2*(q-2)+2)) : ℕ :=
  (F.filter fun x => x.2 = j).card

/-- Actual selected edges cannot have all nonzero row and column degrees equal to q. -/
theorem seed_no_regular_matrix (hq : 5 ≤ q) (F : Finset (Fin (2*(q-2)+1) × Fin (2*(q-2)+2)))
    (hne : F.Nonempty) (hsub : ∀ x ∈ F, seedAdj q x.1 x.2)
    (hrow : ∀ i, matrixRowDegree q F i = 0 ∨ matrixRowDegree q F i = q)
    (hcol : ∀ j, matrixColumnDegree q F j = 0 ∨ matrixColumnDegree q F j = q) : False := by
  let P := univ.filter fun i => 0 < matrixRowDegree q F i
  let Q := univ.filter fun j => 0 < matrixColumnDegree q F j
  have hP (i : Fin (2*(q-2)+1)) : i ∈ P ↔ 0 < matrixRowDegree q F i := by simp [P]
  have hQ (j : Fin (2*(q-2)+2)) : j ∈ Q ↔ 0 < matrixColumnDegree q F j := by simp [Q]
  have hP4 (i : Fin (2*(q-2)+1)) (hi : i ∈ P) : matrixRowDegree q F i = q :=
    (hrow i).resolve_left (Nat.ne_of_gt ((hP i).mp hi))
  have hQ4 (j : Fin (2*(q-2)+2)) (hj : j ∈ Q) : matrixColumnDegree q F j = q :=
    (hcol j).resolve_left (Nat.ne_of_gt ((hQ j).mp hj))
  have hFrow : F.card = ∑ i : Fin (2*(q-2)+1), matrixRowDegree q F i :=
    card_eq_sum_card_fiberwise (f := Prod.fst) (s := F) (t := univ) (by simp)
  have hFcol : F.card = ∑ j : Fin (2*(q-2)+2), matrixColumnDegree q F j :=
    card_eq_sum_card_fiberwise (f := Prod.snd) (s := F) (t := univ) (by simp)
  have hsumP : (∑ i : Fin (2*(q-2)+1), matrixRowDegree q F i) = q * P.card := by
    calc
      _ = ∑ i : Fin (2*(q-2)+1), if i ∈ P then q else 0 := by
        apply sum_congr rfl
        intro i _
        by_cases hi : i ∈ P
        · simp [hi, hP4 i hi]
        · have hz : matrixRowDegree q F i = 0 := by
            have hn := mt (hP i).mpr hi
            omega
          simp [hi, hz]
      _ = q * P.card := by simp [mul_comm]
  have hsumQ : (∑ j : Fin (2*(q-2)+2), matrixColumnDegree q F j) = q * Q.card := by
    calc
      _ = ∑ j : Fin (2*(q-2)+2), if j ∈ Q then q else 0 := by
        apply sum_congr rfl
        intro j _
        by_cases hj : j ∈ Q
        · simp [hj, hQ4 j hj]
        · have hz : matrixColumnDegree q F j = 0 := by
            have hn := mt (hQ j).mpr hj
            omega
          simp [hj, hz]
      _ = q * Q.card := by simp [mul_comm]
  have hbalance : P.card = Q.card := by nlinarith
  have hPne : P.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨x.1, (hP x.1).mpr ?_⟩
    exact card_pos.mpr ⟨x, mem_filter.mpr ⟨hx, rfl⟩⟩
  have hrowlower (i : Fin (2*(q-2)+1)) (hi : i ∈ P) : q ≤ seedRowDegree q Q i := by
    let T := F.filter fun x => x.1 = i
    have hcard : (T.image Prod.snd).card = T.card := by
      apply card_image_of_injOn
      intro x hx y hy hxy
      have hxi := (mem_filter.mp hx).2
      have hyi := (mem_filter.mp hy).2
      exact Prod.ext (hxi.trans hyi.symm) hxy
    have hsubset : T.image Prod.snd ⊆ Q.filter fun j => seedAdj q i j := by
      intro j hj
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hj
      obtain ⟨hxF, hxi⟩ := mem_filter.mp hx
      refine mem_filter.mpr ⟨(hQ x.2).mpr ?_, ?_⟩
      · exact card_pos.mpr ⟨x, mem_filter.mpr ⟨hxF, rfl⟩⟩
      · exact hxi ▸ hsub x hxF
    have hle := card_le_card hsubset
    rw [hcard] at hle
    change matrixRowDegree q F i ≤ seedRowDegree q Q i at hle
    rwa [hP4 i hi] at hle
  exact seed_no_balanced_support q hq P Q hPne hbalance hrowlower

theorem row_card_matrix (r : Fin (2*(q-2)+1) → Fin (2*(q-2)+2) → Prop) [∀ i j, Decidable (r i j)]
    (i : Fin (2*(q-2)+1)) :
    matrixRowDegree q (univ.filter fun x : Fin (2*(q-2)+1) × Fin (2*(q-2)+2) => r x.1 x.2) i =
      (univ.filter fun j => r i j).card := by
  unfold matrixRowDegree
  rw [filter_filter]
  have heq : (univ.filter fun x : Fin (2*(q-2)+1) × Fin (2*(q-2)+2) => r x.1 x.2 ∧ x.1 = i) =
      ({i} ×ˢ (univ.filter fun j => r i j)) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton]
    constructor
    · rintro ⟨hr, hi⟩
      exact ⟨hi, hi ▸ hr⟩
    · rintro ⟨hi, hr⟩
      exact ⟨hi ▸ hr, hi⟩
  rw [heq, card_product, card_singleton, one_mul]

theorem column_card_matrix (r : Fin (2*(q-2)+1) → Fin (2*(q-2)+2) → Prop) [∀ i j, Decidable (r i j)]
    (j : Fin (2*(q-2)+2)) :
    matrixColumnDegree q (univ.filter fun x : Fin (2*(q-2)+1) × Fin (2*(q-2)+2) => r x.1 x.2) j =
      (univ.filter fun i => r i j).card := by
  unfold matrixColumnDegree
  rw [filter_filter]
  have heq : (univ.filter fun x : Fin (2*(q-2)+1) × Fin (2*(q-2)+2) => r x.1 x.2 ∧ x.2 = j) =
      ((univ.filter fun i => r i j) ×ˢ {j}) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton]
    constructor
    · rintro ⟨hr, hj⟩
      exact ⟨hj ▸ hr, hj⟩
    · rintro ⟨hr, hj⟩
      exact ⟨hj ▸ hr, hj⟩
  rw [heq, card_product, card_singleton, mul_one]

theorem degree_left_matrix (K : SimpleGraph (Fin (2*(q-2)+1) ⊕ Fin (2*(q-2)+2))) [DecidableRel K.Adj]
    (hK : K ≤ seedGraph q) (i : Fin (2*(q-2)+1)) :
    K.degree (Sum.inl i) = (univ.filter fun j => K.Adj (Sum.inl i) (Sum.inr j)).card := by
  have hn : K.neighborFinset (Sum.inl i) =
      (univ.filter fun j => K.Adj (Sum.inl i) (Sum.inr j)).image Sum.inr := by
    ext v
    cases v with
    | inl i' =>
      have hnot : ¬ K.Adj (Sum.inl i) (Sum.inl i') := by
        intro h
        exact hK h
      simp [hnot]
    | inr j => simp
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hn,
    card_image_of_injective _ Sum.inr_injective]

theorem degree_right_matrix (K : SimpleGraph (Fin (2*(q-2)+1) ⊕ Fin (2*(q-2)+2))) [DecidableRel K.Adj]
    (hK : K ≤ seedGraph q) (j : Fin (2*(q-2)+2)) :
    K.degree (Sum.inr j) = (univ.filter fun i => K.Adj (Sum.inl i) (Sum.inr j)).card := by
  have hn : K.neighborFinset (Sum.inr j) =
      (univ.filter fun i => K.Adj (Sum.inl i) (Sum.inr j)).image Sum.inl := by
    ext v
    cases v with
    | inl i => simp [K.adj_comm]
    | inr j' =>
      have hnot : ¬ K.Adj (Sum.inr j) (Sum.inr j') := by
        intro h
        exact hK h
      simp [hnot]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hn,
    card_image_of_injective _ Sum.inl_injective]

/-- Literal arbitrary q-regular Subgraph absence for the actual all-q seed. -/
theorem seed_no_regular_subgraph (hq : 5 ≤ q) :
    ¬ ∃ H : (seedGraph q).Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  classical
  rintro ⟨H, hne, hregular⟩
  let F := univ.filter fun x : Fin (2*(q-2)+1) × Fin (2*(q-2)+2) => H.Adj (Sum.inl x.1) (Sum.inr x.2)
  have hleft (i : Fin (2*(q-2)+1)) : matrixRowDegree q F i = H.degree (Sum.inl i) := by
    dsimp [F]
    rw [row_card_matrix q (fun i j => H.Adj (Sum.inl i) (Sum.inr j)) i]
    exact (degree_left_matrix q H.spanningCoe H.spanningCoe_le i).symm.trans
      (SimpleGraph.Subgraph.degree_spanningCoe _)
  have hright (j : Fin (2*(q-2)+2)) : matrixColumnDegree q F j = H.degree (Sum.inr j) := by
    dsimp [F]
    rw [column_card_matrix q (fun i j => H.Adj (Sum.inl i) (Sum.inr j)) j]
    exact (degree_right_matrix q H.spanningCoe H.spanningCoe_le j).symm.trans
      (SimpleGraph.Subgraph.degree_spanningCoe _)
  have hdegrees (v : Fin (2*(q-2)+1) ⊕ Fin (2*(q-2)+2)) : H.degree v = 0 ∨ H.degree v = q := by
    by_cases hv : v ∈ H.verts
    · right
      exact (SimpleGraph.Subgraph.coe_degree H ⟨v, hv⟩).symm.trans (hregular.degree_eq _)
    · left
      exact SimpleGraph.Subgraph.degree_of_notMem_verts hv
  have hFne : F.Nonempty := by
    obtain ⟨v, hv⟩ := hne
    have hd : H.degree v = q :=
      (SimpleGraph.Subgraph.coe_degree H ⟨v, hv⟩).symm.trans (hregular.degree_eq _)
    obtain ⟨w, hvw⟩ := (SimpleGraph.Subgraph.degree_pos_iff_exists_adj).mp (by omega : 0 < H.degree v)
    have hg := H.adj_sub hvw
    cases v with
    | inl i =>
      cases w with
      | inl i' => exact hg.elim
      | inr j => exact ⟨(i, j), mem_filter.mpr ⟨mem_univ _, hvw⟩⟩
    | inr j =>
      cases w with
      | inl i => exact ⟨(i, j), mem_filter.mpr ⟨mem_univ _, hvw.symm⟩⟩
      | inr j' => exact hg.elim
  apply seed_no_regular_matrix q hq F hFne
  · intro x hx
    exact H.adj_sub (mem_filter.mp hx).2
  · intro i
    rw [hleft]
    exact hdegrees _
  · intro j
    rw [hright]
    exact hdegrees _


#print axioms seed_no_regular_matrix
#print axioms seed_no_regular_subgraph
end BqCircularLowerFamily

/- OWN flattened component BqCircularInvariant.lean. Import lines removed only. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open Finset SimpleGraph
namespace BqCircularLowerFamily
/- Generic Sum-shore cover/bipartite/matrix count mechanics adapted from the
exact authenticated BqSeedInvariant source. No old seed invariant is imported. -/
def seedA (q : ℕ) : Finset (Fin (2*(q-2)+1) ⊕ Fin (2*(q-2)+2)) := univ.image Sum.inl
def seedB (q : ℕ) : Finset (Fin (2*(q-2)+1) ⊕ Fin (2*(q-2)+2)) := univ.image Sum.inr
def seedMatrix (q : ℕ) : Finset (Fin (2*(q-2)+1) × Fin (2*(q-2)+2)) :=
  univ.filter fun x => seedAdj q x.1 x.2

theorem seedA_card (q : ℕ) : (seedA q).card = 2*(q-2)+1 := by
  rw [seedA,card_image_of_injective _ Sum.inl_injective,card_univ,Fintype.card_fin]
theorem seedB_card (q : ℕ) : (seedB q).card = 2*(q-2)+2 := by
  rw [seedB,card_image_of_injective _ Sum.inr_injective,card_univ,Fintype.card_fin]

theorem seed_disjoint (q : ℕ) : Disjoint (seedA q) (seedB q) := by
  apply Finset.disjoint_left.mpr
  intro x hxA hxB
  cases x <;> simp_all [seedA,seedB]

theorem seed_cover (q : ℕ) : seedA q ∪ seedB q = univ := by
  ext x
  cases x <;> simp [seedA,seedB]

theorem seed_bipartite (q : ℕ) :
    (seedGraph q).IsBipartiteWith ↑(seedA q) ↑(seedB q) := by
  refine ⟨?_,?_⟩
  · rw [disjoint_coe]
    exact seed_disjoint q
  · intro x y hxy
    cases x <;> cases y <;> simp_all [seedGraph,seedA,seedB]

theorem seed_graph_matrix_card (q : ℕ) :
    (seedGraph q).edgeFinset.card = (seedMatrix q).card := by
  have hFrow : (seedMatrix q).card = ∑ i : Fin (2*(q-2)+1), matrixRowDegree q (seedMatrix q) i :=
    card_eq_sum_card_fiberwise (f := Prod.fst) (s := seedMatrix q) (t := univ) (by simp)
  rw [← SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges (seed_bipartite q)]
  rw [seedA,sum_image (by intro x _ y _ h; exact Sum.inl_injective h)]
  rw [hFrow]
  apply sum_congr rfl
  intro i _
  rw [seedMatrix,row_card_matrix]
  exact degree_left_matrix q (seedGraph q) le_rfl i

theorem seed_degree_bounds (q : ℕ) (hq : 5 ≤ q) :
    ∀ v, q-1 ≤ (seedGraph q).degree v ∧ (seedGraph q).degree v ≤ 2*(q-1) := by
  intro v
  cases v with
  | inl i =>
    have heq : (seedGraph q).degree (.inl i) = seedRowDegree q univ i :=
      degree_left_matrix q (seedGraph q) le_rfl i
    rw [heq, seed_row_degree q hq]
    split_ifs <;> omega
  | inr j =>
    have heq : (seedGraph q).degree (.inr j) = seedColumnDegree q univ j :=
      degree_right_matrix q (seedGraph q) le_rfl j
    rw [heq]
    exact seed_column_bounds q hq j

theorem summed_indicator {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → Prop) [DecidablePred p] (m : ℕ) :
    (∑ i : X, if p i then m else 0) = m*(univ.filter p).card := by
  rw [← sum_filter]
  simp [mul_comm]

theorem seed_row_sum (q : ℕ) (hq : 5 ≤ q) :
    (∑ i : Fin (2*(q-2)+1), seedRowDegree q univ i) =
      q*(q-2)+(2*(q-2)+2)*(q-2)+(2*(q-2)+1) := by
  have hparts (i : Fin (2*(q-2)+1)) : seedRowDegree q univ i =
      (if i.val < q-2 then q else 0) +
      (if q-2 ≤ i.val ∧ i.val < 2*(q-2) then 2*(q-2)+2 else 0) +
      (if i.val = 2*(q-2) then 2*(q-2)+1 else 0) := by
    rw [seed_row_degree q hq]
    have hi := i.isLt
    split_ifs <;> omega
  have hlast : (univ.filter fun i : Fin (2*(q-2)+1) => i.val = 2*(q-2)).card = 1 := by
    have heq : (univ.filter fun i : Fin (2*(q-2)+1) => i.val = 2*(q-2)) =
        {⟨2*(q-2), by omega⟩} := by ext i; simp [Fin.ext_iff]
    rw [heq, card_singleton]
  calc
    _ = ∑ i : Fin (2*(q-2)+1),
        ((if i.val < q-2 then q else 0) +
        (if q-2 ≤ i.val ∧ i.val < 2*(q-2) then 2*(q-2)+2 else 0) +
        (if i.val = 2*(q-2) then 2*(q-2)+1 else 0)) := by
      apply sum_congr rfl
      intro i _
      exact hparts i
    _ = q*(q-2)+(2*(q-2)+2)*(q-2)+(2*(q-2)+1) := by
      rw [sum_add_distrib, sum_add_distrib, summed_indicator, summed_indicator, summed_indicator,
        fin_lt_card _ _ (by omega), fin_between_card _ _ _ (by omega) (by omega), hlast]
      have hz : 2*(q-2)-(q-2) = q-2 := by omega
      rw [hz, mul_one]

theorem seed_edge_count (q : ℕ) (hq : 5 ≤ q) :
    (seedGraph q).edgeFinset.card + ((q-1)*(q-2)+2) = (q-1)*(4*q-5) := by
  have heq : (seedGraph q).edgeFinset.card = ∑ i : Fin (2*(q-2)+1), seedRowDegree q univ i := by
    rw [← SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges (seed_bipartite q)]
    rw [seedA, sum_image (by intro x _ y _ h; exact Sum.inl_injective h)]
    apply sum_congr rfl
    intro i _
    exact degree_left_matrix q (seedGraph q) le_rfl i
  rw [heq, seed_row_sum q hq]
  have hqz : q-2+2 = q := by omega
  have hr : q-1 = (q-2)+1 := by omega
  have hn : 4*q-5 = 4*(q-2)+3 := by omega
  rw [hr, hn]
  nlinarith

theorem seed_good (q : ℕ) (hq : 5 ≤ q) :
    Good q (seedGraph q) (seedA q) (seedB q) := by
  refine ⟨seed_disjoint q, seed_cover q, seed_bipartite q, ?_, ?_,
    seed_degree_bounds q hq, ?_, seed_no_regular_subgraph q hq⟩
  · rw [seedA_card, seedB_card]
    omega
  · rw [seedA_card, seedB_card]
  · rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    have hn : (2*(q-2)+1)+(2*(q-2)+2) = 4*q-5 := by omega
    rw [hn]
    exact seed_edge_count q hq

#print axioms seed_row_sum
#print axioms seed_edge_count
#print axioms seed_good
end BqCircularLowerFamily

/- OWN flattened component BqCircularFamily.lean. Import lines removed only. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
open Finset SimpleGraph
namespace BqCircularLowerFamily
/- The original literal seed coordinate labels. Pattern credited to the
older generic Sum-shore labeling proof; dimensions and labels changed here. -/
def seedLabel (q : ℕ) : (Fin (2*(q-2)+1) ⊕ Fin (2*(q-2)+2)) → ℕ
  | .inl i => i.val
  | .inr j => 2*(q-2)+1+j.val

def seedLabeling (q : ℕ) : Labeling (Fin (2*(q-2)+1) ⊕ Fin (2*(q-2)+2)) where
  label := seedLabel q
  injective := by
    intro x y hxy
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (Fin.ext hxy)
      | inr j =>
        dsimp [seedLabel] at hxy
        have hi := i.isLt
        omega
    | inr i =>
      cases y with
      | inl j =>
        dsimp [seedLabel] at hxy
        have hj := j.isLt
        omega
      | inr j =>
        dsimp [seedLabel] at hxy
        exact congrArg Sum.inr (Fin.ext (Nat.add_left_cancel hxy))
  bounded := by
    intro x
    simp only [Fintype.card_sum,Fintype.card_fin]
    cases x with
    | inl i =>
      dsimp [seedLabel]
      have hi := i.isLt
      omega
    | inr j =>
      dsimp [seedLabel]
      have hj := j.isLt
      omega

def HasLabeledGood (q n : ℕ) : Prop :=
  ∃ (W : Type) (wf : Fintype W) (wd : DecidableEq W),
    letI := wf
    letI := wd
    ∃ (K : SimpleGraph W) (kd : DecidableRel K.Adj),
      letI := kd
      Fintype.card W = n ∧ ∃ (_L : Labeling W) (A B : Finset W), Good q K A B

theorem hasLabeledGood_seed (q : ℕ) (hq : 5 ≤ q) : HasLabeledGood q (4*q-5) := by
  refine ⟨Fin (2*(q-2)+1) ⊕ Fin (2*(q-2)+2),inferInstance,inferInstance,
    seedGraph q,inferInstance,?_,seedLabeling q,seedA q,seedB q,seed_good q hq⟩
  simp only [Fintype.card_sum,Fintype.card_fin]
  omega

theorem hasLabeledGood_succ (q : ℕ) (hq : 5 ≤ q) (n : ℕ)
    (h : HasLabeledGood q n) : HasLabeledGood q (n+1) := by
  rcases h with ⟨W,wf,wd,h⟩
  let : Fintype W := wf
  let : DecidableEq W := wd
  rcases h with ⟨K,kd,hcard,L,A,B,hgood⟩
  let : DecidableRel K.Adj := kd
  let N := nextNeighbors q K A B L
  have hnext := literalNext_good q K A B L hq hgood
  refine ⟨Option W,inferInstance,inferInstance,extendGraph K N,inferInstance,?_,
    L.extend,nextA A B,nextB A B,hnext⟩
  rw [Fintype.card_option,hcard]

theorem hasLabeledGood_all_orders (q : ℕ) (hq : 5 ≤ q) (n : ℕ)
    (hn : 4*q-5 ≤ n) : HasLabeledGood q n := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction t with
  | zero => simpa using hasLabeledGood_seed q hq
  | succ t ih =>
    have hs := hasLabeledGood_succ q hq (4*q-5+t) ih
    simpa [Nat.add_assoc] using hs

theorem deficit_eq (q : ℕ) (hq : 5 ≤ q) :
    (q-1)*(q-2)+2 = q^2-3*q+4 := by
  have h1 : q-1+1 = q := by omega
  have h2 : q-2+2 = q := by omega
  have h3 : 3*q ≤ q^2 := by nlinarith
  have h4 := Nat.sub_add_cancel h3
  nlinarith

def LowerEndpoint : Prop :=
  ∀ (q : ℕ), 5 ≤ q → ∀ (n : ℕ), 4*q-5 ≤ n →
    ∃ (V : Type) (vf : Fintype V) (vd : DecidableEq V),
      letI := vf
      letI := vd
      ∃ (G : SimpleGraph V) (gd : DecidableRel G.Adj),
        letI := gd
        Fintype.card V = n ∧ G.IsBipartite ∧
          (∀ v, q-1 ≤ G.degree v) ∧ G.maxDegree ≤ 2*q-2 ∧
          G.edgeFinset.card = (q-1)*n-(q^2-3*q+4) ∧
          ¬ (∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q)

/-- Bare all-q/all-order endpoint: every seed/choice/extension obligation is internal. -/
theorem all_orders (q : ℕ) (hq : 5 ≤ q) (n : ℕ) (hn : 4*q-5 ≤ n) :
    ∃ (V : Type) (vf : Fintype V) (vd : DecidableEq V),
      letI := vf
      letI := vd
      ∃ (G : SimpleGraph V) (gd : DecidableRel G.Adj),
        letI := gd
        Fintype.card V = n ∧ G.IsBipartite ∧
          (∀ v, q-1 ≤ G.degree v) ∧ G.maxDegree ≤ 2*q-2 ∧
          G.edgeFinset.card = (q-1)*n-(q^2-3*q+4) ∧
          ¬ (∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q) := by
  rcases hasLabeledGood_all_orders q hq n hn with ⟨W,wf,wd,h⟩
  let : Fintype W := wf
  let : DecidableEq W := wd
  rcases h with ⟨K,kd,hcard,_L,A,B,hgood⟩
  let : DecidableRel K.Adj := kd
  refine ⟨W,wf,wd,K,kd,hcard,hgood.bipartite.isBipartite,
    fun v => (hgood.degree_bounds v).1,?_,?_,hgood.no_regular⟩
  · have hmax := K.maxDegree_le_of_forall_degree_le (2*(q-1))
      (fun v => (hgood.degree_bounds v).2)
    have heq : 2*(q-1)=2*q-2 := by omega
    rwa [heq] at hmax
  · have he := hgood.edge_density
    rw [hcard, deficit_eq q hq] at he
    omega

theorem lowerEndpoint : LowerEndpoint := by
  intro q hq n hn
  exact all_orders q hq n hn

#print LowerEndpoint
#check all_orders
#print axioms seedLabeling
#print axioms hasLabeledGood_seed
#print axioms hasLabeledGood_succ
#print axioms hasLabeledGood_all_orders
#print axioms deficit_eq
#print axioms all_orders
#print axioms lowerEndpoint
end BqCircularLowerFamily

/- All explicit authored declared-name type and axiom audit. -/
#check BqCircularLowerFamily.extendGraph
#print axioms BqCircularLowerFamily.extendGraph
#check BqCircularLowerFamily.extendGraphDecidable
#print axioms BqCircularLowerFamily.extendGraphDecidable
#check BqCircularLowerFamily.degree_none
#print axioms BqCircularLowerFamily.degree_none
#check BqCircularLowerFamily.degree_some
#print axioms BqCircularLowerFamily.degree_some
#check BqCircularLowerFamily.edges_extend
#print axioms BqCircularLowerFamily.edges_extend
#check BqCircularLowerFamily.finiteSubgraphLocallyFinite
#print axioms BqCircularLowerFamily.finiteSubgraphLocallyFinite
#check BqCircularLowerFamily.NoRegular
#print axioms BqCircularLowerFamily.NoRegular
#check BqCircularLowerFamily.noRegular_extend
#print axioms BqCircularLowerFamily.noRegular_extend
#check BqCircularLowerFamily.capacity_slots
#print axioms BqCircularLowerFamily.capacity_slots
#check BqCircularLowerFamily.opposite_slots
#print axioms BqCircularLowerFamily.opposite_slots
#check BqCircularLowerFamily.Good
#print axioms BqCircularLowerFamily.Good
#check BqCircularLowerFamily.Good.swap
#print axioms BqCircularLowerFamily.Good.swap
#check BqCircularLowerFamily.extend_good_selected
#print axioms BqCircularLowerFamily.extend_good_selected
#check BqCircularLowerFamily.eligible_card
#print axioms BqCircularLowerFamily.eligible_card
#check BqCircularLowerFamily.leastLabels
#print axioms BqCircularLowerFamily.leastLabels
#check BqCircularLowerFamily.leastNeighbors
#print axioms BqCircularLowerFamily.leastNeighbors
#check BqCircularLowerFamily.leastLabels_subset
#print axioms BqCircularLowerFamily.leastLabels_subset
#check BqCircularLowerFamily.leastLabels_card
#print axioms BqCircularLowerFamily.leastLabels_card
#check BqCircularLowerFamily.leastNeighbors_image
#print axioms BqCircularLowerFamily.leastNeighbors_image
#check BqCircularLowerFamily.leastNeighbors_card
#print axioms BqCircularLowerFamily.leastNeighbors_card
#check BqCircularLowerFamily.leastNeighbors_le_omitted
#print axioms BqCircularLowerFamily.leastNeighbors_le_omitted
#check BqCircularLowerFamily.Labeling
#print axioms BqCircularLowerFamily.Labeling
#check BqCircularLowerFamily.Labeling.extend
#print axioms BqCircularLowerFamily.Labeling.extend
#check BqCircularLowerFamily.Labeling.image_range
#print axioms BqCircularLowerFamily.Labeling.image_range
#check BqCircularLowerFamily.nextNeighbors
#print axioms BqCircularLowerFamily.nextNeighbors
#check BqCircularLowerFamily.nextA
#print axioms BqCircularLowerFamily.nextA
#check BqCircularLowerFamily.nextB
#print axioms BqCircularLowerFamily.nextB
#check BqCircularLowerFamily.literalNext_good
#print axioms BqCircularLowerFamily.literalNext_good
#check BqCircularLowerFamily.nextNeighbors_card
#print axioms BqCircularLowerFamily.nextNeighbors_card
#check BqCircularLowerFamily.nextNeighbors_least
#print axioms BqCircularLowerFamily.nextNeighbors_least
#check BqCircularLowerFamily.extend_label_old
#print axioms BqCircularLowerFamily.extend_label_old
#check BqCircularLowerFamily.extend_label_new
#print axioms BqCircularLowerFamily.extend_label_new
#check BqCircularLowerFamily.missing
#print axioms BqCircularLowerFamily.missing
#check BqCircularLowerFamily.mod_once
#print axioms BqCircularLowerFamily.mod_once
#check BqCircularLowerFamily.missing_lt
#print axioms BqCircularLowerFamily.missing_lt
#check BqCircularLowerFamily.missing_card
#print axioms BqCircularLowerFamily.missing_card
#check BqCircularLowerFamily.back
#print axioms BqCircularLowerFamily.back
#check BqCircularLowerFamily.back_lt
#print axioms BqCircularLowerFamily.back_lt
#check BqCircularLowerFamily.back_inj_rows
#print axioms BqCircularLowerFamily.back_inj_rows
#check BqCircularLowerFamily.back_no_adjacent
#print axioms BqCircularLowerFamily.back_no_adjacent
#check BqCircularLowerFamily.back_inj_columns
#print axioms BqCircularLowerFamily.back_inj_columns
#check BqCircularLowerFamily.back_cross_sum
#print axioms BqCircularLowerFamily.back_cross_sum
#check BqCircularLowerFamily.common_missing_card
#print axioms BqCircularLowerFamily.common_missing_card
#check BqCircularLowerFamily.seedAdj
#print axioms BqCircularLowerFamily.seedAdj
#check BqCircularLowerFamily.seedAdjDecidable
#print axioms BqCircularLowerFamily.seedAdjDecidable
#check BqCircularLowerFamily.seedGraph
#print axioms BqCircularLowerFamily.seedGraph
#check BqCircularLowerFamily.seedGraphDecidable
#print axioms BqCircularLowerFamily.seedGraphDecidable
#check BqCircularLowerFamily.seedRowDegree
#print axioms BqCircularLowerFamily.seedRowDegree
#check BqCircularLowerFamily.seedColumnDegree
#print axioms BqCircularLowerFamily.seedColumnDegree
#check BqCircularLowerFamily.fin_lt_card
#print axioms BqCircularLowerFamily.fin_lt_card
#check BqCircularLowerFamily.fin_ge_card
#print axioms BqCircularLowerFamily.fin_ge_card
#check BqCircularLowerFamily.fin_between_card
#print axioms BqCircularLowerFamily.fin_between_card
#check BqCircularLowerFamily.missing_fin_card
#print axioms BqCircularLowerFamily.missing_fin_card
#check BqCircularLowerFamily.seed_forced_degree
#print axioms BqCircularLowerFamily.seed_forced_degree
#check BqCircularLowerFamily.seed_row_degree
#print axioms BqCircularLowerFamily.seed_row_degree
#check BqCircularLowerFamily.seed_reserved_adj
#print axioms BqCircularLowerFamily.seed_reserved_adj
#check BqCircularLowerFamily.seed_column_bounds
#print axioms BqCircularLowerFamily.seed_column_bounds
#check BqCircularLowerFamily.seed_w_not_reserved
#print axioms BqCircularLowerFamily.seed_w_not_reserved
#check BqCircularLowerFamily.seed_no_balanced_support
#print axioms BqCircularLowerFamily.seed_no_balanced_support
#check BqCircularLowerFamily.matrixRowDegree
#print axioms BqCircularLowerFamily.matrixRowDegree
#check BqCircularLowerFamily.matrixColumnDegree
#print axioms BqCircularLowerFamily.matrixColumnDegree
#check BqCircularLowerFamily.seed_no_regular_matrix
#print axioms BqCircularLowerFamily.seed_no_regular_matrix
#check BqCircularLowerFamily.row_card_matrix
#print axioms BqCircularLowerFamily.row_card_matrix
#check BqCircularLowerFamily.column_card_matrix
#print axioms BqCircularLowerFamily.column_card_matrix
#check BqCircularLowerFamily.degree_left_matrix
#print axioms BqCircularLowerFamily.degree_left_matrix
#check BqCircularLowerFamily.degree_right_matrix
#print axioms BqCircularLowerFamily.degree_right_matrix
#check BqCircularLowerFamily.seed_no_regular_subgraph
#print axioms BqCircularLowerFamily.seed_no_regular_subgraph
#check BqCircularLowerFamily.seedA
#print axioms BqCircularLowerFamily.seedA
#check BqCircularLowerFamily.seedB
#print axioms BqCircularLowerFamily.seedB
#check BqCircularLowerFamily.seedMatrix
#print axioms BqCircularLowerFamily.seedMatrix
#check BqCircularLowerFamily.seedA_card
#print axioms BqCircularLowerFamily.seedA_card
#check BqCircularLowerFamily.seedB_card
#print axioms BqCircularLowerFamily.seedB_card
#check BqCircularLowerFamily.seed_disjoint
#print axioms BqCircularLowerFamily.seed_disjoint
#check BqCircularLowerFamily.seed_cover
#print axioms BqCircularLowerFamily.seed_cover
#check BqCircularLowerFamily.seed_bipartite
#print axioms BqCircularLowerFamily.seed_bipartite
#check BqCircularLowerFamily.seed_graph_matrix_card
#print axioms BqCircularLowerFamily.seed_graph_matrix_card
#check BqCircularLowerFamily.seed_degree_bounds
#print axioms BqCircularLowerFamily.seed_degree_bounds
#check BqCircularLowerFamily.summed_indicator
#print axioms BqCircularLowerFamily.summed_indicator
#check BqCircularLowerFamily.seed_row_sum
#print axioms BqCircularLowerFamily.seed_row_sum
#check BqCircularLowerFamily.seed_edge_count
#print axioms BqCircularLowerFamily.seed_edge_count
#check BqCircularLowerFamily.seed_good
#print axioms BqCircularLowerFamily.seed_good
#check BqCircularLowerFamily.seedLabel
#print axioms BqCircularLowerFamily.seedLabel
#check BqCircularLowerFamily.seedLabeling
#print axioms BqCircularLowerFamily.seedLabeling
#check BqCircularLowerFamily.HasLabeledGood
#print axioms BqCircularLowerFamily.HasLabeledGood
#check BqCircularLowerFamily.hasLabeledGood_seed
#print axioms BqCircularLowerFamily.hasLabeledGood_seed
#check BqCircularLowerFamily.hasLabeledGood_succ
#print axioms BqCircularLowerFamily.hasLabeledGood_succ
#check BqCircularLowerFamily.hasLabeledGood_all_orders
#print axioms BqCircularLowerFamily.hasLabeledGood_all_orders
#check BqCircularLowerFamily.deficit_eq
#print axioms BqCircularLowerFamily.deficit_eq
#check BqCircularLowerFamily.LowerEndpoint
#print axioms BqCircularLowerFamily.LowerEndpoint
#check BqCircularLowerFamily.all_orders
#print axioms BqCircularLowerFamily.all_orders
#check BqCircularLowerFamily.lowerEndpoint
#print axioms BqCircularLowerFamily.lowerEndpoint

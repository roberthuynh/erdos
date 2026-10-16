import C4Counting
import CycleIncidence

namespace Erdos60.Statistics
open Finset
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def codegree (G : SimpleGraph V) (x y : V) : ℕ := by
  classical
  exact (G.neighborFinset x ∩ G.neighborFinset y).card

noncomputable def vertexCycleStatistic (G : SimpleGraph V) (x : V) : ℕ :=
  ∑ y ∈ Finset.univ.erase x, (codegree G x y).choose 2

 theorem codegree_symm (G : SimpleGraph V) (x y : V) :
    codegree G x y = codegree G y x := by
  classical
  simp [codegree, inter_comm]

 theorem codegree_eq_sum (G : SimpleGraph V) (x y : V) :
    codegree G x y = ∑ w ∈ G.neighborFinset x, if G.Adj y w then 1 else 0 := by
  classical
  unfold codegree
  rw [Finset.sum_boole]
  congr 1
  ext w
  simp

 theorem twoPath_count (G : SimpleGraph V) (x : V) :
    (∑ y ∈ Finset.univ.erase x, codegree G x y) =
      ∑ w ∈ G.neighborFinset x, (G.degree w - 1) := by
  classical
  simp_rw [codegree_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  have hx : x ∈ G.neighborFinset w := by
    simpa using G.adj_symm ((G.mem_neighborFinset x w).mp hw)
  calc
    (∑ y ∈ Finset.univ.erase x, if G.Adj y w then 1 else 0) =
        ((G.neighborFinset w).erase x).card := by
      rw [Finset.sum_boole]
      simp only [Nat.cast_id]
      congr 1
      ext y
      simp [SimpleGraph.adj_comm]
    _ = G.degree w - 1 := by
      rw [Finset.card_erase_of_mem hx, G.card_neighborFinset_eq_degree]

/-- Distinct vertices with no common neighbor with x. -/
noncomputable def zeroCodegreeCount (G : SimpleGraph V) (x : V) : ℕ :=
  ((Finset.univ.erase x).filter fun y => codegree G x y = 0).card

 theorem choose_two_lower (n : ℕ) :
    n + (if n = 0 then 1 else 0) ≤ n.choose 2 + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn : n = 0
    · subst n; simp
    · rw [Nat.choose_succ_succ, Nat.choose_one_right]
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
        ↓reduceIte, add_zero]
      have hp : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      omega

/-- Source §1's binomial path lower bound, including the zero-codegree term.
The later vertexCycleStatistic_eq_card supplies its actual cycle interpretation. -/
 theorem vertexCycleStatistic_lower (G : SimpleGraph V) (x : V) :
    (∑ w ∈ G.neighborFinset x, (G.degree w - 1)) + zeroCodegreeCount G x ≤
      vertexCycleStatistic G x + (Fintype.card V - 1) := by
  classical
  rw [← twoPath_count]
  unfold zeroCodegreeCount vertexCycleStatistic
  have hs := Finset.sum_le_sum (s := Finset.univ.erase x)
    (fun y _ => choose_two_lower (codegree G x y))
  simp only [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id,
    Finset.sum_const, smul_eq_mul, mul_one] at hs
  simpa using hs

/-- Every two distinct common neighbors of distinct vertices produce an actual
ordinary edge-set cycle, with ambient diagonals allowed. -/
theorem commonNeighbors_cycle (G : SimpleGraph V) {x y a b : V}
    (hxy : x ≠ y) (hab : a ≠ b)
    (hxa : G.Adj x a) (hya : G.Adj y a)
    (hxb : G.Adj x b) (hyb : G.Adj y b) :
    Erdos60.Counting.fourEdges x a y b ∈ Erdos60.Counting.cycles G := by
  classical
  apply (Erdos60.Counting.mem_cycles G _).mpr
  constructor
  · intro e he
    simp only [Erdos60.Counting.fourEdges, Finset.mem_insert,
      Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · simpa using hxa
    · simpa using hya.symm
    · simpa using hyb
    · simpa using hxb.symm
  · refine ⟨x, a, y, b, ?_, rfl⟩
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true, not_or]
    exact ⟨⟨hxa.ne, hxy, hxb.ne⟩, ⟨hya.ne.symm, hab⟩, hyb.ne⟩

/-- The opposite common-neighbor pair can be recovered from its cycle edge set.
This is a fixed-opposite-pair injectivity step for the normalization bridge. -/
theorem recover_commonNeighborPair {x y a b : V}
    (hxy : x ≠ y) (hxa : x ≠ a) (hxb : x ≠ b) :
    (Finset.univ.filter fun w => s(x,w) ∈ Erdos60.Counting.fourEdges x a y b) =
      {a,b} := by
  ext w
  simp [Erdos60.Counting.fourEdges, hxy, hxa, hxb]

theorem commonNeighborPair_injective {x y a b c d : V}
    (hxy : x ≠ y) (hxa : x ≠ a) (hxb : x ≠ b)
    (hxc : x ≠ c) (hxd : x ≠ d)
    (h : Erdos60.Counting.fourEdges x a y b =
      Erdos60.Counting.fourEdges x c y d) : ({a,b} : Finset V) = {c,d} := by
  rw [← recover_commonNeighborPair hxy hxa hxb,
    ← recover_commonNeighborPair hxy hxc hxd, h]

noncomputable def commonNeighborPairs (G : SimpleGraph V) (x y : V) :
    Finset (Finset V) := by
  classical
  exact (G.neighborFinset x ∩ G.neighborFinset y).powersetCard 2

noncomputable def pairEdges (x y : V) (S : Finset V) : Finset (Sym2 V) :=
  S.biUnion fun a => {s(x,a), s(y,a)}

omit [Fintype V] in
 theorem pairEdges_pair (x y a b : V) :
    pairEdges x y {a,b} = Erdos60.Counting.fourEdges x a y b := by
  classical
  ext e
  simp [pairEdges, Erdos60.Counting.fourEdges, Sym2.eq_swap,
    or_comm, or_left_comm]

 theorem pairEdges_mem_cycles (G : SimpleGraph V) {x y : V}
    (hxy : x ≠ y) {S : Finset V} (hS : S ∈ commonNeighborPairs G x y) :
    pairEdges x y S ∈ Erdos60.Counting.cycles G := by
  classical
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hcard
  have ha := hsub (by simp : a ∈ ({a,b} : Finset V))
  have hb := hsub (by simp : b ∈ ({a,b} : Finset V))
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at ha hb
  rw [pairEdges_pair]
  exact commonNeighbors_cycle G hxy hab ha.1 ha.2 hb.1 hb.2

 theorem pairEdges_injOn (G : SimpleGraph V) {x y : V} (hxy : x ≠ y) :
    Set.InjOn (pairEdges x y) (commonNeighborPairs G x y : Set (Finset V)) := by
  classical
  intro S hS T hT heq
  obtain ⟨hSsub, hScard⟩ := Finset.mem_powersetCard.mp hS
  obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hT
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hScard
  obtain ⟨c,d,hcd,rfl⟩ := Finset.card_eq_two.mp hTcard
  have ha := hSsub (by simp : a ∈ ({a,b} : Finset V))
  have hb := hSsub (by simp : b ∈ ({a,b} : Finset V))
  have hc := hTsub (by simp : c ∈ ({c,d} : Finset V))
  have hd := hTsub (by simp : d ∈ ({c,d} : Finset V))
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at ha hb hc hd
  exact commonNeighborPair_injective hxy ha.1.ne hb.1.ne hc.1.ne hd.1.ne
    (by simpa only [pairEdges_pair] using heq)

/-- An exact counting theorem for the actual cycle family with fixed opposite pair.
This fixed-pair identity is used in the vertex-cycle normalization below. -/
theorem fixedOppositePair_count (G : SimpleGraph V) {x y : V} (hxy : x ≠ y) :
    ((commonNeighborPairs G x y).image (pairEdges x y)).card =
      (codegree G x y).choose 2 := by
  classical
  rw [Finset.card_image_iff.mpr (pairEdges_injOn G hxy)]
  exact Finset.card_powersetCard 2 _

def cycleVertices (C : Finset (Sym2 V)) : Finset V :=
  C.biUnion Sym2.toFinset

omit [Fintype V] in
theorem fourEdges_vertices (x a y b : V) :
    cycleVertices (Erdos60.Counting.fourEdges x a y b) = {x,a,y,b} := by
  ext w
  simp [cycleVertices, Erdos60.Counting.fourEdges, Sym2.mem_toFinset,
    or_comm, or_left_comm]

/-- With a fixed distinguished vertex, the opposite vertex is uniquely
recoverable from an ordinary cycle edge set. Ambient chords play no role. -/
theorem opposite_unique {x y z a b c d : V}
    (hxy : x ≠ y) (hxz : x ≠ z)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) (hxd : x ≠ d)
    (hya : y ≠ a) (hyb : y ≠ b)
    (heq : Erdos60.Counting.fourEdges x a y b =
      Erdos60.Counting.fourEdges x c z d) : y = z := by
  have hp : ({a,b} : Finset V) = {c,d} := by
    rw [← recover_commonNeighborPair hxy hxa hxb,
      ← recover_commonNeighborPair hxz hxc hxd, heq]
  have hc : y ≠ c := by
    intro h
    have : y ∈ ({a,b} : Finset V) := hp.symm ▸ (by simp [h])
    simp [hya, hyb] at this
  have hd : y ≠ d := by
    intro h
    have : y ∈ ({a,b} : Finset V) := hp.symm ▸ (by simp [h])
    simp [hya, hyb] at this
  have hv := congrArg cycleVertices heq
  rw [fourEdges_vertices, fourEdges_vertices] at hv
  have hy : y ∈ ({x,c,z,d} : Finset V) := hv ▸ (by simp)
  simpa [hxy.symm, hc, hd] using hy

noncomputable def pairCycleFamily (G : SimpleGraph V) (x y : V) :
    Finset (Finset (Sym2 V)) :=
  (commonNeighborPairs G x y).image (pairEdges x y)

 theorem mem_pairCycleFamily (G : SimpleGraph V) {x y : V} (_hxy : x ≠ y)
    {C : Finset (Sym2 V)} : C ∈ pairCycleFamily G x y ↔
      ∃ a b, a ≠ b ∧ G.Adj x a ∧ G.Adj y a ∧ G.Adj x b ∧ G.Adj y b ∧
        C = Erdos60.Counting.fourEdges x a y b := by
  classical
  constructor
  · intro hC
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp hS
    obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hcard
    have ha := hsub (by simp : a ∈ ({a,b} : Finset V))
    have hb := hsub (by simp : b ∈ ({a,b} : Finset V))
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at ha hb
    exact ⟨a,b,hab,ha.1,ha.2,hb.1,hb.2,pairEdges_pair _ _ _ _⟩
  · rintro ⟨a,b,hab,hxa,hya,hxb,hyb,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨{a,b}, ?_, pairEdges_pair _ _ _ _⟩
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl <;> simp_all
    · simp [hab]

 theorem pairCycleFamily_disjoint (G : SimpleGraph V) {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Disjoint (pairCycleFamily G x y) (pairCycleFamily G x z) := by
  classical
  apply Finset.disjoint_left.mpr
  intro C hC hD
  obtain ⟨a,b,_,hxa,hya,hxb,hyb,hCeq⟩ := (mem_pairCycleFamily G hxy).mp hC
  obtain ⟨c,d,_,hxc,_,hxd,_,hDeq⟩ := (mem_pairCycleFamily G hxz).mp hD
  exact hyz (opposite_unique hxy hxz hxa.ne hxb.ne hxc.ne hxd.ne
    hya.ne hyb.ne (hCeq.symm.trans hDeq))

omit [Fintype V] in
 theorem cycle_at_vertex {C : Finset (Sym2 V)}
    (hC : Erdos60.Counting.IsFourCycle C) {x : V} (hx : x ∈ cycleVertices C) :
    ∃ a y b, [x,a,y,b].Nodup ∧ C = Erdos60.Counting.fourEdges x a y b := by
  obtain ⟨a,b,c,d,hd,rfl⟩ := hC
  rw [fourEdges_vertices] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨b,c,d,hd,rfl⟩
  · refine ⟨c,d,a,?_, (Erdos60.Counting.fourEdges_rotate a x c d).symm⟩
    simp_all only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true, not_or]
    grind
  · refine ⟨d,a,b,?_, ?_⟩
    · simp_all only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
        not_false_eq_true, List.nodup_nil, and_true, not_or]
      grind
    · rw [Erdos60.Counting.fourEdges_rotate, Erdos60.Counting.fourEdges_rotate]
  · refine ⟨a,b,c,?_, ?_⟩
    · simp_all only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
        not_false_eq_true, List.nodup_nil, and_true, not_or]
      grind
    · rw [Erdos60.Counting.fourEdges_rotate]

noncomputable def vertexCycles (G : SimpleGraph V) (x : V) :
    Finset (Finset (Sym2 V)) :=
  (Erdos60.Counting.cycles G).filter fun C => x ∈ cycleVertices C

 theorem vertexCycles_eq_biUnion (G : SimpleGraph V) (x : V) :
    vertexCycles G x = (Finset.univ.erase x).biUnion (pairCycleFamily G x) := by
  classical
  ext C
  constructor
  · intro h
    obtain ⟨hC,hx⟩ := Finset.mem_filter.mp h
    obtain ⟨hsub,hshape⟩ := (Erdos60.Counting.mem_cycles G C).mp hC
    obtain ⟨a,y,b,hd,rfl⟩ := cycle_at_vertex hshape hx
    have hn := hd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true, not_or] at hn
    apply Finset.mem_biUnion.mpr
    refine ⟨y, by simp [Ne.symm hn.1.2.1], ?_⟩
    apply (mem_pairCycleFamily G hn.1.2.1).mpr
    refine ⟨a,b,hn.2.1.2,?_,?_,?_,?_,rfl⟩
    · simpa using hsub (by simp [Erdos60.Counting.fourEdges] :
        s(x,a) ∈ Erdos60.Counting.fourEdges x a y b)
    · have := hsub (by simp [Erdos60.Counting.fourEdges] :
        s(a,y) ∈ Erdos60.Counting.fourEdges x a y b)
      simpa [SimpleGraph.adj_comm] using this
    · have := hsub (by simp [Erdos60.Counting.fourEdges] :
        s(b,x) ∈ Erdos60.Counting.fourEdges x a y b)
      simpa [SimpleGraph.adj_comm] using this
    · simpa using hsub (by simp [Erdos60.Counting.fourEdges] :
        s(y,b) ∈ Erdos60.Counting.fourEdges x a y b)
  · intro h
    obtain ⟨y,hy,hC⟩ := Finset.mem_biUnion.mp h
    have hxy : x ≠ y := (Finset.mem_erase.mp hy).1.symm
    obtain ⟨a,b,hab,hxa,hya,hxb,hyb,rfl⟩ := (mem_pairCycleFamily G hxy).mp hC
    apply Finset.mem_filter.mpr
    exact ⟨commonNeighbors_cycle G hxy hab hxa hya hxb hyb, by
      rw [fourEdges_vertices]; simp⟩

 theorem vertexCycleStatistic_eq_card (G : SimpleGraph V) (x : V) :
    vertexCycleStatistic G x = (vertexCycles G x).card := by
  classical
  rw [vertexCycles_eq_biUnion]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro y hy
    exact (fixedOppositePair_count G (Finset.mem_erase.mp hy).1.symm).symm
  · intro y hy z hz hyz
    exact pairCycleFamily_disjoint G (Finset.mem_erase.mp hy).1.symm
      (Finset.mem_erase.mp hz).1.symm hyz

 theorem vertexCycleStatistic_sum (G : SimpleGraph V) :
    (∑ x : V, vertexCycleStatistic G x) =
      ∑ C ∈ Erdos60.Counting.cycles G, (cycleVertices C).card := by
  classical
  simp_rw [vertexCycleStatistic_eq_card, vertexCycles, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C hC
  rw [Finset.sum_boole]
  simp

 theorem actual_vertexCycle_lower (G : SimpleGraph V) (x : V) :
    (∑ w ∈ G.neighborFinset x, (G.degree w - 1)) + zeroCodegreeCount G x ≤
      (vertexCycles G x).card + (Fintype.card V - 1) := by
  rw [← vertexCycleStatistic_eq_card]
  exact vertexCycleStatistic_lower G x

 theorem vertexCycleStatistic_sum_eq_four (G : SimpleGraph V) :
    (∑ x : V, vertexCycleStatistic G x) = 4 * Erdos60.Counting.cycleCount G := by
  classical
  rw [vertexCycleStatistic_sum]
  calc
    (∑ C ∈ Erdos60.Counting.cycles G, (cycleVertices C).card) =
        ∑ C ∈ Erdos60.Counting.cycles G, 4 := by
      apply Finset.sum_congr rfl
      intro C hC
      exact Erdos60.Counting.IsFourCycle.vertices_card
        ((Erdos60.Counting.mem_cycles G C).mp hC).2
    _ = 4 * Erdos60.Counting.cycleCount G := by
      simp [Erdos60.Counting.cycleCount, Nat.mul_comm]

noncomputable def pairWeight (G : SimpleGraph V) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun x y => (codegree G x y).choose 2,
    fun x y => by dsimp; rw [codegree_symm]⟩

@[simp] theorem pairWeight_mk (G : SimpleGraph V) (x y : V) :
    pairWeight G s(x,y) = (codegree G x y).choose 2 := by
  rfl

/-- All ordinary unordered pairs of distinct vertices. -/
noncomputable def unorderedPairs : Finset (Sym2 V) :=
  (Finset.univ : Finset V).offDiag.image Sym2.mk.uncurry

 theorem two_mul_unorderedPair_sum (G : SimpleGraph V) :
    2 * (∑ p ∈ unorderedPairs (V := V), pairWeight G p) =
      ∑ x : V, vertexCycleStatistic G x := by
  classical
  have hfiber (a b : V) (hab : a ≠ b) :
      {z ∈ (Finset.univ : Finset V).offDiag | Sym2.mk.uncurry z = s(a,b)} =
        {(a,b),(b,a)} := by
    ext z
    rcases z with ⟨u,v⟩
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ,
      true_and, Function.uncurry_apply_pair, Sym2.eq_iff, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    aesop
  have hsum : (∑ p ∈ unorderedPairs (V := V), 2 * pairWeight G p) =
      ∑ p ∈ (Finset.univ : Finset V).offDiag, pairWeight G (Sym2.mk.uncurry p) := by
    apply Finset.sum_image'
    intro p hp
    rcases p with ⟨a,b⟩
    have hab : a ≠ b := (Finset.mem_offDiag.mp hp).2.2
    calc
      2 * pairWeight G (Sym2.mk.uncurry (a,b)) =
          ∑ j ∈ ({(a,b),(b,a)} : Finset (V × V)),
            pairWeight G (Sym2.mk.uncurry j) := by
        simp [hab, pairWeight_mk, codegree_symm G b a, two_mul]
      _ = _ := congrArg
        (fun S : Finset (V × V) => ∑ j ∈ S, pairWeight G (Sym2.mk.uncurry j))
        (hfiber a b hab).symm
  rw [Finset.mul_sum] 
  rw [hsum]
  have hoff : (Finset.univ : Finset V).offDiag =
      (Finset.univ ×ˢ Finset.univ).filter (fun p : V × V => p.1 ≠ p.2) := by
    ext p
    simp
  rw [hoff, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x hx
  unfold vertexCycleStatistic
  have he : (Finset.univ : Finset V).erase x =
      Finset.univ.filter (fun y => x ≠ y) := by
    ext y
    simp [ne_comm]
  rw [he, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y hy
  simp only [Function.uncurry_apply_pair, pairWeight_mk]

/-- Exact ordinary-unlabelled-C4 normalization from source §1. -/
theorem unorderedPair_sum_eq_twice (G : SimpleGraph V) :
    (∑ p ∈ unorderedPairs (V := V), pairWeight G p) =
      2 * Erdos60.Counting.cycleCount G := by
  have h := two_mul_unorderedPair_sum G
  rw [vertexCycleStatistic_sum_eq_four] at h
  omega

end Erdos60.Statistics

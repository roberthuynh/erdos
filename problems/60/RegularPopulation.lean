import RegularTransport
import DisjointCellBudget

/-! Source: COUNT-BASED-COMPLETION-PROOF-v2.md Section 3, first paragraph.
Frozen source SHA256: d07eaa46889ac5a9808a097f281e43c25a768e5057e19ddefe5b72952d9eacbb.
This proves the required strict population threshold for actual regular neighbors.
A weaker aggregate count than the displayed source .957q count suffices: discard
the at-most-2|Sx| unsafe neighbors, then charge every nonregular clean cell two
actual deficient vertices. DisjointCellBudget pays cells meeting deep vertices.
No regular population, projective embedding, or headline conclusion is assumed.
-/

namespace Erdos60.Completion
open scoped Classical
variable {V : Type*} [Fintype V]

/-- An actual induced neighborhood has at most one neighbor at any vertex. -/
theorem local_neighbor_card_le_one (G : SimpleGraph V) (hG : NoFourCycle G)
    (x a : V) (hxa : G.Adj x a) :
    letI := Classical.decRel G.Adj
    ((G.neighborFinset x).filter (G.Adj a)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro b hb c hc
  simp only [Finset.mem_filter,SimpleGraph.mem_neighborFinset] at hb hc
  exact neighborhood_neighbor_unique hG hxa hb.1 hc.1 hb.2 hc.2

/-- Genuine graph supplier for Section 3. The weaker cell budget already gives
far more than the required q/100+1 actual regular neighbors. -/
theorem many_regular_neighbors (G : SimpleGraph V) (hG : NoFourCycle G)
    (q : ℕ) (heven : Even q) (hq : 100000000 ≤ q)
    (hN : Fintype.card V = q^2+q+1)
    (hcap : ∀ v, letI := Classical.decRel G.Adj; G.degree v ≤ q+1)
    (hS : letI := Classical.decRel G.Adj
      1000 * (Finset.univ.filter (fun v : V => G.degree v ≤ q)).card ≤ 1001*q)
    (hD : letI := Classical.decRel G.Adj
      1000 * (Finset.univ.filter (fun v : V => G.degree v ≤ q-1)).card ≤ q)
    (x : V) (hx : letI := Classical.decRel G.Adj; G.degree x = q+1)
    (hxS : letI := Classical.decRel G.Adj
      100 * ((G.neighborFinset x).filter (fun v => G.degree v ≤ q)).card < q) :
    letI := Classical.decRel G.Adj
    letI := Classical.decPred (IsRegularVertex G q)
    100 * ((G.neighborFinset x).filter (IsRegularVertex G q)).card > q+100 := by
  classical
  let S := Finset.univ.filter (fun v : V => G.degree v ≤ q)
  let D := Finset.univ.filter (fun v : V => G.degree v ≤ q-1)
  let Nx := G.neighborFinset x
  let Sx := Nx.filter (fun v => G.degree v ≤ q)
  let P := Sx.biUnion (fun a => Nx.filter (G.Adj a))
  let star := Sx ∪ P
  let K := Nx \ star
  let J := K.filter (fun z => ¬IsRegularVertex G q z)
  let R := K.filter (IsRegularVertex G q)
  let C : V → Finset V := fun z => Finset.univ.filter (fun a => a ∈ cell G x z)
  have hNx : Nx.card = q+1 := by simpa only [Nx,G.card_neighborFinset_eq_degree] using hx
  have hP : P.card ≤ Sx.card := by
    have hh := Finset.card_biUnion_le (s := Sx) (t := fun a => Nx.filter (G.Adj a))
    have hb : (∑ a ∈ Sx, (Nx.filter (G.Adj a)).card) ≤ ∑ _a ∈ Sx, 1 := by
      apply Finset.sum_le_sum
      intro a ha
      exact local_neighbor_card_le_one G hG x a
        (by simpa only [Sx,Nx,Finset.mem_filter,SimpleGraph.mem_neighborFinset] using (Finset.mem_filter.mp ha).1)
    simpa only [Finset.sum_const,smul_eq_mul,mul_one] using hh.trans hb
  have hstar : star.card ≤ 2*Sx.card := by
    have hh := Finset.card_union_le Sx P
    change (Sx ∪ P).card ≤ _
    omega
  have hstarSub : star ⊆ Nx := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact (Finset.mem_filter.mp ha).1
    · obtain ⟨b,hb,ha⟩ := Finset.mem_biUnion.mp ha
      exact (Finset.mem_filter.mp ha).1
  have hK : K.card + star.card = q+1 := by
    rw [show K = Nx \ star from rfl,Finset.card_sdiff_of_subset hstarSub,hNx]
    have hh := Finset.card_le_card hstarSub
    omega
  have hdis : (J : Set V).PairwiseDisjoint C := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro w hwa hwb
    have hax : G.Adj x a := by
      have h := (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha).1).1
      simpa only [Nx,SimpleGraph.mem_neighborFinset] using h
    have hbx : G.Adj x b := by
      have h := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hb).1).1
      simpa only [Nx,SimpleGraph.mem_neighborFinset] using h
    exact Set.disjoint_left.mp (cells_disjoint hG hax hbx hab)
      (Finset.mem_filter.mp hwa).2 (Finset.mem_filter.mp hwb).2
  have hclean : ∀ z ∈ J, Disjoint (C z) D → 2 ≤ (C z ∩ S).card := by
    intro z hz hcz
    have hzk := (Finset.mem_filter.mp hz).1
    have hnotreg := (Finset.mem_filter.mp hz).2
    have hzx : G.Adj x z := by
      simpa only [Nx,SimpleGraph.mem_neighborFinset] using (Finset.mem_sdiff.mp hzk).1
    have hzstar := (Finset.mem_sdiff.mp hzk).2
    have hzfull : G.degree z = q+1 := by
      have hn : ¬G.degree z ≤ q := by
        intro h
        apply hzstar
        apply Finset.mem_union_left
        exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hzk).1,h⟩
      have hc := hcap z
      omega
    have low_in_cell : ∀ a, G.Adj z a → G.degree a ≤ q → a ∈ C z := by
      intro a hza hda
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,hza,?_,?_⟩
      · intro he
        subst a
        omega
      · intro hxa
        apply hzstar
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨a,Finset.mem_filter.mpr ⟨?_,hda⟩,?_⟩
        · simpa only [Nx,SimpleGraph.mem_neighborFinset] using hxa
        · exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hzk).1,hza.symm⟩
    by_contra htwo
    have hone : (C z ∩ S).card ≤ 1 := by omega
    obtain ⟨a,hza,hda⟩ := full_vertex_has_deficient_neighbor G hG q heven hN hcap z hzfull
    have haC := low_in_cell a hza hda
    have haq : G.degree a = q := by
      have hn : ¬G.degree a < q := by
        intro h
        exact Finset.disjoint_left.mp hcz haC (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩)
      omega
    apply hnotreg
    refine ⟨hzfull,a,hza,haq,?_⟩
    intro b hzb hba
    have hn : ¬G.degree b ≤ q := by
      intro hdb
      have hbC := low_in_cell b hzb hdb
      have hab := Finset.card_le_one.mp hone b
        (Finset.mem_inter.mpr ⟨hbC,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hdb⟩⟩) a
        (Finset.mem_inter.mpr ⟨haC,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hda⟩⟩)
      exact hba hab
    have hc := hcap b
    omega
  have hbudget := disjoint_cell_budget J C S D hdis hclean
  have hsplit : R.card + J.card = K.card := by
    exact Finset.card_filter_add_card_filter_not (s := K) (p := IsRegularVertex G q)
  have hR : R.card ≤ ((G.neighborFinset x).filter (IsRegularVertex G q)).card := by
    apply Finset.card_le_card
    intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).1,
      (Finset.mem_filter.mp hz).2⟩
  change 1000*S.card ≤ 1001*q at hS
  change 1000*D.card ≤ q at hD
  change 100*Sx.card < q at hxS
  omega

#print axioms local_neighbor_card_le_one
#print axioms many_regular_neighbors
end Erdos60.Completion

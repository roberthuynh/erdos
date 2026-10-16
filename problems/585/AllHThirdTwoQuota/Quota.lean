import AllHThirdTwoQuota.Tiny

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.AllHThirdTwoQuota
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace Data
variable {h q a j : ℕ} {A B : Finset V} (d : Data h q a j G A B)
include d

omit d [DecidableEq V] in
lemma degree_zero_of_avoid {O : Finset V} {x : V}
    (havoid : ∀ z∈O, ¬G.Adj x z) : dg G O x=0 := by
  change #(O.filter (fun z => G.Adj x z))=0
  apply card_eq_zero.mpr
  apply filter_eq_empty_iff.mpr
  intro z hz
  exact havoid z hz

lemma two_cover {x y : V} (hx : x∈d.fragileRows) (hy : y∈d.fragileRows)
    (hxy : x≠y) : ∀ v∈d.fragileRows, v=x ∨ v=y := by
  intro v hv
  by_contra hn
  have hvx : v≠x := by tauto
  have hvy : v≠y := by tauto
  have hsub : ({x,y,v}:Finset V)⊆d.fragileRows := by
    intro z hz
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with rfl|rfl|rfl
    · exact hx
    · exact hy
    · exact hv
  have hc : #({x,y,v}:Finset V)=3 := by
    simp [hxy,Ne.symm hvx,Ne.symm hvy]
  have hh := (card_le_card hsub).trans d.fragile_card
  rw [hc] at hh
  omega

/-- One actual weak row has at least j original nonneighbors at the literal cutoff. -/
lemma quota_single {x : V} (hx : x∈d.fragileRows)
    (honly : ∀ v∈d.fragileRows, v=x) : ∃ O, d.QuotaFeasible O := by
  have hB := d.shore_B_large
  have hd := (d.mem_fragile.mp hx).2
  have hc := card_sdiff_add_card_eq_card (d.neighbors_subset x)
  rw [d.neighbors_card] at hc
  have hn := d.parameters.numeric
  have hj := d.parameters.surplus_int
  have hh := d.parameters.height_int
  have hav : j≤#(B\d.neighbors x) := by omega
  obtain ⟨O,hO,hOj⟩ := exists_subset_card_eq hav
  refine ⟨O,hO.trans sdiff_subset,hOj,?_⟩
  intro v hv
  have he := honly v hv
  subst v
  have hz := degree_zero_of_avoid (G:=G) (x:=x) (by
    intro z hz hadj
    exact (mem_sdiff.mp (hO hz)).2 (d.mem_neighbors.mpr ⟨(mem_sdiff.mp (hO hz)).1,hadj⟩))
  rw [hz]
  exact Nat.zero_le _

/-- The scalar bound constructs one actual two-quota omission.
At the literal cutoff, the exclusive cells are large whenever the outside cell is small. -/
lemma quota_two {x y : V} (hx : x∈d.fragileRows) (hy : y∈d.fragileRows)
    (hxy : x≠y)
    (hscalar : j≤#(B.filter (fun z => ¬G.Adj x z ∧ ¬G.Adj y z))+
      (dg G B x-q)+(dg G B y-q)) : ∃ O, d.QuotaFeasible O := by
  let P := B.filter (fun z => ¬G.Adj x z ∧ ¬G.Adj y z)
  let U := B.filter (fun z => G.Adj x z ∧ ¬G.Adj y z)
  let W := B.filter (fun z => ¬G.Adj x z ∧ G.Adj y z)
  have hcover := d.two_cover hx hy hxy
  have hP : P⊆B := filter_subset _ _
  have hU : U⊆B := filter_subset _ _
  have hW : W⊆B := filter_subset _ _
  by_cases hlarge : j≤#P
  · obtain ⟨O,hOP,hOj⟩ := exists_subset_card_eq hlarge
    have hOB := hOP.trans hP
    refine ⟨O,hOB,hOj,?_⟩
    intro v hv
    have hz : dg G O v=0 := by
      apply degree_zero_of_avoid (G:=G)
      intro z hz
      have hp := (mem_filter.mp (hOP hz)).2
      rcases hcover v hv with rfl|rfl
      · exact hp.1
      · exact hp.2
    rw [hz]
    exact Nat.zero_le _
  · have hPx : #P<j := by omega
    have hB := d.shore_B_large
    have hdx := (d.mem_fragile.mp hx).2
    have hdy := (d.mem_fragile.mp hy).2
    have hnum := d.parameters.numeric
    have hj := d.parameters.surplus_int
    have hh := d.parameters.height_int
    have h10 : (10:ℤ)*h<q := by nlinarith [sq_nonneg (h:ℤ)]
    have hBU : B⊆d.neighbors y∪(P∪U) := by
      intro z hz
      by_cases hay : G.Adj y z
      · exact mem_union_left _ (d.mem_neighbors.mpr ⟨hz,hay⟩)
      · by_cases hax : G.Adj x z
        · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hz,hax,hay⟩))
        · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hz,hax,hay⟩))
    have hBW : B⊆d.neighbors x∪(P∪W) := by
      intro z hz
      by_cases hax : G.Adj x z
      · exact mem_union_left _ (d.mem_neighbors.mpr ⟨hz,hax⟩)
      · by_cases hay : G.Adj y z
        · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hz,hax,hay⟩))
        · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hz,hax,hay⟩))
    have hcardU := (card_le_card hBU).trans (card_union_le _ _)
    have hcardW := (card_le_card hBW).trans (card_union_le _ _)
    rw [d.neighbors_card] at hcardU hcardW
    have hPU := card_union_le P U
    have hPW := card_union_le P W
    have hUj : j≤#U := by omega
    have hWj : j≤#W := by omega
    let sx := min (dg G B x-q) (j-#P)
    let sy := j-#P-sx
    have hsx : sx≤dg G B x-q := min_le_left _ _
    have hsxj : sx≤j-#P := min_le_right _ _
    have hsy : sy≤dg G B y-q := by
      dsimp [sx,sy]
      change j≤#P+(dg G B x-q)+(dg G B y-q) at hscalar
      omega
    have hsum : #P+sx+sy=j := by dsimp [sy]; omega
    obtain ⟨EX,hEX,hcEX⟩ := exists_subset_card_eq (show sx≤#U by omega)
    obtain ⟨EY,hEY,hcEY⟩ := exists_subset_card_eq (show sy≤#W by dsimp [sy]; omega)
    have hEXEY : Disjoint EX EY := disjoint_left.mpr (by
      intro z hzX hzY
      exact (mem_filter.mp (hEY hzY)).2.1 (mem_filter.mp (hEX hzX)).2.1)
    have hPEX : Disjoint P EX := disjoint_left.mpr (by
      intro z hzP hzX
      exact (mem_filter.mp hzP).2.1 (mem_filter.mp (hEX hzX)).2.1)
    have hPEY : Disjoint P EY := disjoint_left.mpr (by
      intro z hzP hzY
      exact (mem_filter.mp hzP).2.2 (mem_filter.mp (hEY hzY)).2.2)
    let O := P∪(EX∪EY)
    have hOB : O⊆B := union_subset hP (union_subset (hEX.trans hU) (hEY.trans hW))
    have hOj : #O=j := by
      rw [card_union_of_disjoint (disjoint_union_right.mpr ⟨hPEX,hPEY⟩),
        card_union_of_disjoint hEXEY,hcEX,hcEY]
      omega
    have hdegreeX : dg G O x=#EX := by
      change #(O.filter (fun z => G.Adj x z))=#EX
      congr 1
      ext z
      constructor
      · intro hz
        obtain ⟨hzO,hadj⟩ := mem_filter.mp hz
        rcases mem_union.mp hzO with hzP|hzE
        · exact False.elim ((mem_filter.mp hzP).2.1 hadj)
        · rcases mem_union.mp hzE with hzX|hzY
          · exact hzX
          · exact False.elim ((mem_filter.mp (hEY hzY)).2.1 hadj)
      · intro hzX
        exact mem_filter.mpr ⟨mem_union_right _ (mem_union_left _ hzX),
          (mem_filter.mp (hEX hzX)).2.1⟩
    have hdegreeY : dg G O y=#EY := by
      change #(O.filter (fun z => G.Adj y z))=#EY
      congr 1
      ext z
      constructor
      · intro hz
        obtain ⟨hzO,hadj⟩ := mem_filter.mp hz
        rcases mem_union.mp hzO with hzP|hzE
        · exact False.elim ((mem_filter.mp hzP).2.2 hadj)
        · rcases mem_union.mp hzE with hzX|hzY
          · exact False.elim ((mem_filter.mp (hEX hzX)).2.2 hadj)
          · exact hzY
      · intro hzY
        exact mem_filter.mpr ⟨mem_union_right _ (mem_union_right _ hzY),
          (mem_filter.mp (hEY hzY)).2.2⟩
    refine ⟨O,hOB,hOj,?_⟩
    intro v hv
    rcases hcover v hv with rfl|rfl
    · rw [hdegreeX,hcEX]
      exact hsx
    · rw [hdegreeY,hcEY]
      exact hsy

/-- Zero, one and two fragile rows are derived and handled internally. -/
lemma quota_exists (hpair : d.PairCondition) : ∃ O, d.QuotaFeasible O := by
  by_cases hex : ∃ x∈d.fragileRows, ∃ y∈d.fragileRows, x≠y
  · obtain ⟨x,hx,y,hy,hxy⟩ := hex
    exact d.quota_two hx hy hxy (hpair x hx y hy hxy)
  · by_cases hne : d.fragileRows.Nonempty
    · obtain ⟨x,hx⟩ := hne
      apply d.quota_single hx
      intro v hv
      by_contra hneq
      exact hex ⟨v,hv,x,hx,hneq⟩
    · have he : d.fragileRows=∅ := not_nonempty_iff_eq_empty.mp hne
      have hav : j≤#B := by have hs:=d.shores_large; omega
      obtain ⟨O,hOB,hOj⟩ := exists_subset_card_eq hav
      refine ⟨O,hOB,hOj,?_⟩
      intro x hx
      rw [he] at hx
      simp at hx

/-- Each selected point outside the outside-both cell spends at least one actual quota. -/
lemma pair_of_quota {O : Finset V} (ho : d.QuotaFeasible O) : d.PairCondition := by
  intro x hx y hy _
  let P := B.filter (fun z => ¬G.Adj x z ∧ ¬G.Adj y z)
  let X := O.filter (fun z => G.Adj x z)
  let Y := O.filter (fun z => G.Adj y z)
  have hsub : O⊆P∪(X∪Y) := by
    intro z hz
    by_cases hax : G.Adj x z
    · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hz,hax⟩))
    · by_cases hay : G.Adj y z
      · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hz,hay⟩))
      · exact mem_union_left _ (mem_filter.mpr ⟨ho.1 hz,hax,hay⟩)
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  have hXY := card_union_le X Y
  have hdx : #X=dg G O x := rfl
  have hdy : #Y=dg G O y := rfl
  have hxq := ho.2.2 x hx
  have hyq := ho.2.2 y hy
  rw [ho.2.1] at hc
  rw [hdx,hdy] at hXY
  change j≤#P+(dg G B x-q)+(dg G B y-q)
  omega

lemma quota_iff_pair : (∃ O, d.QuotaFeasible O)↔d.PairCondition :=
  ⟨fun ⟨_,ho⟩ => d.pair_of_quota ho,d.quota_exists⟩

end Data
end Erdos585.AllHThirdTwoQuota

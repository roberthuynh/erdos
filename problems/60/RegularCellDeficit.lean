import RegularVertex
import RegularLowIsolation
import DisjointCellBudget

/-! Exact source correspondence: COUNT-BASED-COMPLETION-PROOF-v2.md §2,
regular-neighbor isolation paragraph. Source SHA256:
d07eaa46889ac5a9808a097f281e43c25a768e5057e19ddefe5b72952d9eacbb.

This file discharges the formerly unpaid aggregate bridge. It partitions each
actual neighborFinset using the certified outside-cell partition, proves exact
row cardinal sums, transposes actual cross incidences, and bounds both sides by
matching. Three special cell indices produce paired-cell contribution zero,
odd internal matching loss one, and smaller low-index cell loss one. All cell
sizes are proved from literal neighborFinset equalities. For each of the q-2
remaining matched full indices, a deep-free cell consequently contains at least
two low vertices. DisjointCellBudget supplies the proved global set-count
inequality, contradicting the exact integer forms of the source budgets.

The endpoint regular_low_isolated assumes only the actual regular vertex
hypotheses, even q>=10^8, actual graph order, and the two global filtered-vertex
count inequalities. It assumes neither the desired isolation nor a percell
sum/deficiency bound. Full completion and regular transport are separate.
-/
namespace Erdos60.Completion
open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

noncomputable def cellFinset (G : SimpleGraph V) (v a : V) : Finset V :=
  Finset.univ.filter (fun x => x ∈ cell G v a)

@[simp] theorem mem_cellFinset (G : SimpleGraph V) (v a x : V) :
    x ∈ cellFinset G v a ↔ x ∈ cell G v a := by
  classical
  simp [cellFinset]

/-- Actual incidence decomposition, before any degree upper bound is imposed. -/
theorem cell_neighbor_decomposition (G : SimpleGraph V) (hG : NoFourCycle G)
    (v a x : V) (hva : G.Adj v a) (hx : x ∈ cell G v a)
    (hpart : ∀ y, y ≠ v → ¬G.Adj v y → ∃ b, G.Adj v b ∧ y ∈ cell G v b) :
    letI := Classical.decRel G.Adj
    G.neighborFinset x = insert a ((G.neighborFinset v).biUnion
      (fun b => G.neighborFinset x ∩ cellFinset G v b)) := by
  classical
  ext y
  simp only [SimpleGraph.mem_neighborFinset,Finset.mem_insert,Finset.mem_biUnion,
    Finset.mem_inter,mem_cellFinset]
  constructor
  · intro hxy
    by_cases hvy : G.Adj v y
    · exact Or.inl ((cell_center_neighbor_iff G hG hva hx hvy).mp hxy)
    · have hyv : y ≠ v := by intro h; exact hx.2.2 (h ▸ hxy).symm
      obtain ⟨b,hvb,hyb⟩ := hpart y hyv hvy
      exact Or.inr ⟨b,hvb,hxy,hyb⟩
  · rintro (rfl | ⟨b,hvb,hxy,hyb⟩)
    · exact hx.1.symm
    · exact hxy

/-- Exact cardinal decomposition of one actual vertex's degree over outside cells. -/
theorem cell_degree_decomposition (G : SimpleGraph V) (hG : NoFourCycle G)
    (v a x : V) (hva : G.Adj v a) (hx : x ∈ cell G v a)
    (hpart : ∀ y, y ≠ v → ¬G.Adj v y → ∃ b, G.Adj v b ∧ y ∈ cell G v b) :
    letI := Classical.decRel G.Adj
    G.degree x = 1 + ∑ b ∈ G.neighborFinset v,
      (G.neighborFinset x ∩ cellFinset G v b).card := by
  classical
  rw [← G.card_neighborFinset_eq_degree]
  conv_lhs => rw [cell_neighbor_decomposition G hG v a x hva hx hpart]
  have hnot : a ∉ (G.neighborFinset v).biUnion
      (fun b => G.neighborFinset x ∩ cellFinset G v b) := by
    simp only [Finset.mem_biUnion,Finset.mem_inter,mem_cellFinset,not_exists,not_and]
    intro b hb hab hac
    exact hac.2.2 hva
  rw [Finset.card_insert_of_notMem hnot]
  have hd : (G.neighborFinset v : Set V).PairwiseDisjoint
      (fun b => G.neighborFinset x ∩ cellFinset G v b) := by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro y hyb hyc
    exact Set.disjoint_left.mp (cells_disjoint hG (by simpa using hb)
      (by simpa using hc) hbc) (by simpa using (Finset.mem_inter.mp hyb).2)
      (by simpa using (Finset.mem_inter.mp hyc).2)
  rw [Finset.card_biUnion hd]
  omega

theorem neighbor_inter_card (G : SimpleGraph V) (x : V) (s : Finset V) :
    (G.neighborFinset x ∩ s).card = ∑ y ∈ s, if G.Adj x y then 1 else 0 := by
  classical
  have he : G.neighborFinset x ∩ s = s.filter (G.Adj x) := by
    ext y; simp [and_comm]
  rw [he]
  simp

theorem cross_sum_symm (G : SimpleGraph V) (s t : Finset V) :
    (∑ x ∈ s, (G.neighborFinset x ∩ t).card) =
      ∑ y ∈ t, (G.neighborFinset y ∩ s).card := by
  classical
  simp_rw [neighbor_inter_card]
  rw [Finset.sum_comm]
  simp only [G.adj_comm]

/-- Each actual vertex outside the center's neighborhood sees at most one point per cell. -/
theorem cell_cross_degree_le_one (G : SimpleGraph V) (hG : NoFourCycle G)
    {v b x : V} (hvb : G.Adj v b) (hnx : ¬G.Adj v x) :
    (G.neighborFinset x ∩ cellFinset G v b).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro y hy z hz
  have hxy : G.Adj x y := by simpa using (Finset.mem_inter.mp hy).1
  have hxz : G.Adj x z := by simpa using (Finset.mem_inter.mp hz).1
  have hby : G.Adj b y := ((mem_cellFinset G v b y).mp (Finset.mem_inter.mp hy).2).1
  have hbz : G.Adj b z := ((mem_cellFinset G v b z).mp (Finset.mem_inter.mp hz).2).1
  have hxb : x ≠ b := by intro h; exact hnx (h.symm ▸ hvb)
  exact common_neighbor_unique hG hxb hxy hby hxz hbz

theorem cell_cross_sum_le_left (G : SimpleGraph V) (hG : NoFourCycle G)
    {v a b : V} (hvb : G.Adj v b) :
    (∑ x ∈ cellFinset G v a, (G.neighborFinset x ∩ cellFinset G v b).card) ≤
      (cellFinset G v a).card := by
  classical
  have hh := Finset.sum_le_sum (fun x (hx : x ∈ cellFinset G v a) =>
    cell_cross_degree_le_one G hG hvb ((mem_cellFinset G v a x).mp hx).2.2)
  simpa using hh

theorem cell_cross_sum_le_right (G : SimpleGraph V) (hG : NoFourCycle G)
    {v a b : V} (hva : G.Adj v a) :
    (∑ x ∈ cellFinset G v a, (G.neighborFinset x ∩ cellFinset G v b).card) ≤
      (cellFinset G v b).card := by
  rw [cross_sum_symm]
  exact cell_cross_sum_le_left G hG hva

theorem induced_degree_eq_cross (G : SimpleGraph V) (s : Finset V) (x : s) :
    (G.comap (Subtype.val : s → V)).degree x = (G.neighborFinset x.val ∩ s).card := by
  classical
  let H : SimpleGraph s := G.comap Subtype.val
  let e : H.neighborSet x ≃ ↥(G.neighborFinset x.val ∩ s) := {
    toFun := fun y => ⟨y.val.val,Finset.mem_inter.mpr
      ⟨by simpa only [SimpleGraph.mem_neighborFinset,SimpleGraph.mem_neighborSet,H,SimpleGraph.comap_adj] using y.property,y.val.property⟩⟩
    invFun := fun y => ⟨⟨y.val,(Finset.mem_inter.mp y.property).2⟩,
      by simpa only [SimpleGraph.mem_neighborFinset,SimpleGraph.mem_neighborSet,H,SimpleGraph.comap_adj] using (Finset.mem_inter.mp y.property).1⟩
    left_inv := fun y => by apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := fun y => by apply Subtype.ext; rfl }
  have hc := Fintype.card_congr e
  rw [H.card_neighborSet_eq_degree,Fintype.card_coe] at hc
  exact hc

/-- The missing aggregate source bound, from the actual cell partition, odd
internal matching, paired-cell exclusion, and a smaller low-index cell. -/
theorem actual_cell_degree_sum_deficit_two (G : SimpleGraph V) (hG : NoFourCycle G)
    (v i j low : V) (q : ℕ) (hv : G.degree v = q+1)
    (hvi : G.Adj v i) (hvj : G.Adj v j) (hvl : G.Adj v low)
    (hij : G.Adj i j) (hil : i ≠ low) (hjl : j ≠ low)
    (hodd : Odd (cellFinset G v i).card)
    (hsmall : (cellFinset G v low).card + 1 ≤ (cellFinset G v i).card)
    (hpart : ∀ y, y ≠ v → ¬G.Adj v y → ∃ b, G.Adj v b ∧ y ∈ cell G v b) :
    (∑ x ∈ cellFinset G v i, G.degree x) + 2 ≤ (q+1)*(cellFinset G v i).card := by
  classical
  let C := cellFinset G v i
  let m := C.card
  let W : V → ℕ := fun b => ∑ x ∈ C, (G.neighborFinset x ∩ cellFinset G v b).card
  have hle : ∀ b, G.Adj v b → W b ≤ m := by
    intro b hb
    exact cell_cross_sum_le_left G hG hb
  have hi : W i + 1 ≤ m := by
    have hh := odd_neighbor_set_internal_bound G hG i C
      (fun x hx => ((mem_cellFinset G v i x).mp hx).1) hodd
    change (∑ x : C, (G.comap (Subtype.val : C → V)).degree x) + 1 ≤ m at hh
    simp_rw [induced_degree_eq_cross] at hh
    rw [Finset.sum_coe_sort C (fun x : V => (G.neighborFinset x ∩ C).card)] at hh
    exact hh
  have hl : W low + 1 ≤ m := by
    have hh := cell_cross_sum_le_right G hG (b := low) hvi
    exact (Nat.add_le_add_right hh 1).trans hsmall
  have hj : W j = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact paired_cells_no_edges G hG hvi hvj hij
      ((mem_cellFinset G v i x).mp hx)
      ((mem_cellFinset G v j y).mp (Finset.mem_inter.mp hy).2)
      (by simpa using (Finset.mem_inter.mp hy).1)
  have hp : ∀ b ∈ G.neighborFinset v,
      W b + (if b=i then 1 else 0) + (if b=low then 1 else 0) +
        (if b=j then m else 0) ≤ m := by
    intro b hb
    have hbv : G.Adj v b := by simpa using hb
    by_cases hbi : b=i
    · subst b
      simpa [hil,hij.ne] using hi
    by_cases hbl : b=low
    · subst b
      simpa [hil.symm,hjl.symm] using hl
    by_cases hbj : b=j
    · subst b
      simp [hj,hij.ne.symm,hjl]
    · simpa [hbi,hbl,hbj] using hle b hbv
  have hsum := Finset.sum_le_sum hp
  simp only [Finset.sum_add_distrib] at hsum
  have hmi : i ∈ G.neighborFinset v := by simpa using hvi
  have hml : low ∈ G.neighborFinset v := by simpa using hvl
  have hmj : j ∈ G.neighborFinset v := by simpa using hvj
  simp only [Finset.sum_ite_eq',hmi,hml,hmj,if_true,Finset.sum_const,smul_eq_mul,
    G.card_neighborFinset_eq_degree,hv] at hsum
  have hdegree : (∑ x ∈ C, G.degree x) = m + ∑ b ∈ G.neighborFinset v, W b := by
    calc
      _ = ∑ x ∈ C, (1 + ∑ b ∈ G.neighborFinset v,
          (G.neighborFinset x ∩ cellFinset G v b).card) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact cell_degree_decomposition G hG v i x hvi ((mem_cellFinset G v i x).mp hx) hpart
      _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_comm]; simp only [Finset.sum_const,smul_eq_mul,mul_one]; rfl
  change (∑ x ∈ C, G.degree x) + 2 ≤ (q+1)*m
  rw [hdegree]
  omega

theorem matched_cell_card (G : SimpleGraph V) (hG : NoFourCycle G)
    {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b) (hab : G.Adj a b) :
    (cellFinset G v a).card + 2 = G.degree a := by
  classical
  have he : G.neighborFinset a = insert v (insert b (cellFinset G v a)) := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_insert,mem_cellFinset]
    constructor
    · intro hax
      by_cases hxv : x=v
      · exact Or.inl hxv
      by_cases hvx : G.Adj v x
      · exact Or.inr (Or.inl (neighborhood_neighbor_unique hG hva hvx hvb hax hab))
      · exact Or.inr (Or.inr ⟨hax,hxv,hvx⟩)
    · rintro (rfl | rfl | hx)
      · exact hva.symm
      · exact hab
      · exact hx.1
  have hnv : v ∉ cellFinset G v a := by simp [cell]
  have hnb : b ∉ cellFinset G v a := by
    intro h
    exact ((mem_cellFinset G v a b).mp h).2.2 hvb
  rw [← G.card_neighborFinset_eq_degree,he,
    Finset.card_insert_of_notMem (by simp [hnv,hvb.ne]),Finset.card_insert_of_notMem hnb]

theorem isolated_cell_card (G : SimpleGraph V)
    {v a : V} (hva : G.Adj v a) (hiso : ∀ b, G.Adj v b → ¬G.Adj a b) :
    (cellFinset G v a).card + 1 = G.degree a := by
  classical
  have he : G.neighborFinset a = insert v (cellFinset G v a) := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_insert,mem_cellFinset]
    constructor
    · intro hax
      by_cases hxv : x=v
      · exact Or.inl hxv
      · exact Or.inr ⟨hax,hxv,fun hvx => hiso x hvx hax⟩
    · rintro (rfl | hx)
      · exact hva.symm
      · exact hx.1
  have hnv : v ∉ cellFinset G v a := by simp [cell]
  rw [← G.card_neighborFinset_eq_degree,he,Finset.card_insert_of_notMem hnv]

/-- The isolated local neighbor is genuinely the degree-q neighbor under the
count-based global budgets, with no assumption of the desired isolation. -/
theorem regular_low_isolated (G : SimpleGraph V) (hG : NoFourCycle G)
    (q : ℕ) (hq : 100000000 ≤ q) (heven : Even q)
    (hN : Fintype.card V = q^2+q+1)
    (v low : V) (hv : G.degree v = q+1)
    (hlow : G.Adj v low) (hdl : G.degree low = q)
    (hfull : ∀ a, G.Adj v a → a ≠ low → G.degree a = q+1)
    (hS : 1000*(Finset.univ.filter (fun x => G.degree x ≤ q)).card ≤ 1001*q)
    (hD : 1000*(Finset.univ.filter (fun x => G.degree x ≤ q-1)).card ≤ q) :
    ∀ a, G.Adj v a → ¬G.Adj low a := by
  classical
  by_contra hnot
  push Not at hnot
  obtain ⟨partner,hvp,hpair⟩ := hnot
  obtain ⟨w,hvw,hw,hm,hpart⟩ := regular_vertex_structure G hG q heven hN v low hv hlow hdl hfull
  have hwl : w ≠ low := by intro h; exact hw partner hvp (h.symm ▸ hpair)
  have hwp : w ≠ partner := by intro h; exact hw low hlow (h.symm ▸ hpair.symm)
  let J := (((G.neighborFinset v).erase low).erase partner).erase w
  let S := Finset.univ.filter (fun x => G.degree x ≤ q)
  let D := Finset.univ.filter (fun x => G.degree x ≤ q-1)
  have hcardJ : J.card = q-2 := by
    have hl : low ∈ G.neighborFinset v := by simpa using hlow
    have hp : partner ∈ (G.neighborFinset v).erase low := by simp [hpair.ne.symm,hvp]
    have hww : w ∈ ((G.neighborFinset v).erase low).erase partner := by simp [hwl,hwp,hvw]
    simp only [J,Finset.card_erase_of_mem hww,Finset.card_erase_of_mem hp,
      Finset.card_erase_of_mem hl,G.card_neighborFinset_eq_degree,hv]
    omega
  have hd : (J : Set V).PairwiseDisjoint (cellFinset G v) := by
    intro a ha b hb hab
    have hva : G.Adj v a := by simpa using
      (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).2).2
    have hvb : G.Adj v b := by simpa using
      (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).2).2
    apply Finset.disjoint_left.mpr
    intro x hxa hxb
    exact Set.disjoint_left.mp (cells_disjoint hG hva hvb hab)
      ((mem_cellFinset G v a x).mp hxa) ((mem_cellFinset G v b x).mp hxb)
  have hclean : ∀ i ∈ J, Disjoint (cellFinset G v i) D →
      2 ≤ (cellFinset G v i ∩ S).card := by
    intro i hi hdis
    have hiw : i ≠ w := (Finset.mem_erase.mp hi).1
    have hip : i ≠ partner := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    have hil : i ≠ low := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2).1
    have hvi : G.Adj v i := by simpa using
      (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2).2
    obtain ⟨j,⟨hvj,hij⟩,_⟩ := hm i hvi hiw
    have hjl : j ≠ low := by
      intro he
      have hei : partner = i := neighborhood_neighbor_unique hG hlow hvp hvi hpair (he ▸ hij.symm)
      exact hip hei.symm
    have hci := matched_cell_card G hG hvi hvj hij
    have hcl := matched_cell_card G hG hlow hvp hpair
    rw [hfull i hvi hil] at hci
    rw [hdl] at hcl
    have hodd : Odd (cellFinset G v i).card := by
      obtain ⟨k,hk⟩ := heven
      exact ⟨k-1,by omega⟩
    have hsmall : (cellFinset G v low).card+1 ≤ (cellFinset G v i).card := by omega
    have hbound := actual_cell_degree_sum_deficit_two G hG v i j low q hv hvi hvj hlow
      hij hil hjl hodd hsmall (fun y hy hny => by
        obtain ⟨a,ha,_⟩ := hpart y hy hny
        exact ⟨a,ha⟩)
    have hmin : ∀ x ∈ cellFinset G v i, q ≤ G.degree x := by
      intro x hx
      have hnotD : x ∉ D := fun hxd => Finset.disjoint_left.mp hdis hx hxd
      have hn : ¬G.degree x ≤ q-1 := by simpa [D] using hnotD
      omega
    have hh := two_low_of_degree_sum G q (cellFinset G v i) hmin hbound
    have he : (cellFinset G v i).filter (fun x => G.degree x ≤ q) = cellFinset G v i ∩ S := by
      ext x; simp [S]
    rwa [he] at hh
  have hbudget := disjoint_cell_budget J (cellFinset G v) S D hd hclean
  change 2*J.card ≤ S.card+2*D.card at hbudget
  rw [hcardJ] at hbudget
  change 1000*S.card ≤ 1001*q at hS
  change 1000*D.card ≤ q at hD
  omega

#print axioms regular_low_isolated
#print axioms matched_cell_card
#print axioms isolated_cell_card
#print axioms actual_cell_degree_sum_deficit_two
#print axioms cell_cross_sum_le_right
#print axioms cell_degree_decomposition
end Erdos60.Completion

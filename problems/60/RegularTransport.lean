import RegularCellDeficit

namespace Erdos60.Completion
open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

/-- Literal source regular vertex: full, with exactly one degree-q neighbor. -/
def IsRegularVertex (G : SimpleGraph V) (q : ℕ) (z : V) : Prop :=
  G.degree z = q+1 ∧ ∃ low, G.Adj z low ∧ G.degree low = q ∧
    ∀ a, G.Adj z a → a ≠ low → G.degree a = q+1

/-- Exact actual common-neighbor transport from a regular vertex. Global low
budgets are used only to derive that its degree-q neighbor is isolated. -/
theorem regular_transport (G : SimpleGraph V) (hG : NoFourCycle G)
    (q : ℕ) (hq : 100000000 ≤ q) (heven : Even q)
    (hN : Fintype.card V = q^2+q+1)
    (hS : 1000*(Finset.univ.filter (fun x => G.degree x ≤ q)).card ≤ 1001*q)
    (hD : 1000*(Finset.univ.filter (fun x => G.degree x ≤ q-1)).card ≤ q)
    {z u i : V} (hreg : IsRegularVertex G q z)
    (hu : G.degree u = q+1) (huz : u ≠ z) (hzu : ¬G.Adj z u)
    (hzi : G.Adj z i) (hui : G.Adj u i) (hi : G.degree i = q+1) :
    ∀ b, G.Adj z b → ∃! y, G.Adj u y ∧ G.Adj b y := by
  classical
  obtain ⟨hz,low,hzl,hdl,hfull⟩ := hreg
  have hiso := regular_low_isolated G hG q hq heven hN z low hz hzl hdl hfull hS hD
  obtain ⟨w,hzw,hw,hm,hpart⟩ := regular_vertex_structure G hG q heven hN z low hz hzl hdl hfull
  have hwl : w=low := by
    by_contra hne
    obtain ⟨a,ha,_⟩ := hm low hzl (fun h => hne h.symm)
    exact hiso a ha.1 ha.2
  have hil : i ≠ low := by intro h; have hh := h ▸ hi; omega
  obtain ⟨j,⟨hzj,hij⟩,_⟩ := hm i hzi (hwl ▸ hil)
  have huc : u ∈ cell G z i := ⟨hui.symm,huz,hzu⟩
  have hp : ∀ y, y ≠ z → ¬G.Adj z y → ∃ b, G.Adj z b ∧ y ∈ cell G z b := by
    intro y hy hny
    obtain ⟨b,hb,_⟩ := hpart y hy hny
    exact ⟨b,hb⟩
  let f : V → ℕ := fun b => (G.neighborFinset u ∩ cellFinset G z b).card
  have hf : ∀ b ∈ G.neighborFinset z, f b ≤ 1 := by
    intro b hb
    exact cell_cross_degree_le_one G hG (by simpa using hb) hzu
  have hfj : f j = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact paired_cells_no_edges G hG hzi hzj hij huc
      ((mem_cellFinset G z j y).mp (Finset.mem_inter.mp hy).2)
      (by simpa using (Finset.mem_inter.mp hy).1)
  have hs : (∑ b ∈ G.neighborFinset z, f b) = q := by
    have hh := cell_degree_decomposition G hG z i u hzi huc hp
    change G.degree u = 1 + ∑ b ∈ G.neighborFinset z, f b at hh
    rw [hu] at hh
    omega
  have hjmem : j ∈ G.neighborFinset z := by simpa using hzj
  have hcard : ((G.neighborFinset z).erase j).card = q := by
    rw [Finset.card_erase_of_mem hjmem,G.card_neighborFinset_eq_degree,hz]
    omega
  have hone : ∀ b ∈ G.neighborFinset z, b ≠ j → f b = 1 := by
    intro b hb hbj
    by_contra hnot
    have hb0 : f b = 0 := by have hh := hf b hb; omega
    have hlt := Finset.sum_lt_sum
      (fun t (ht : t ∈ (G.neighborFinset z).erase j) => hf t (Finset.mem_erase.mp ht).2)
      (show ∃ t ∈ (G.neighborFinset z).erase j, f t < 1 from
        ⟨b,Finset.mem_erase.mpr ⟨hbj,hb⟩,by omega⟩)
    rw [Finset.sum_erase (G.neighborFinset z) hfj,hs] at hlt
    simp only [Finset.sum_const,smul_eq_mul,mul_one,hcard] at hlt
    omega
  intro b hzb
  have hub : u ≠ b := by intro h; exact hzu (h.symm ▸ hzb)
  by_cases hbj : b=j
  · subst b
    refine ⟨i,⟨hui,hij.symm⟩,?_⟩
    intro y hy
    exact common_neighbor_unique hG hub hy.1 hy.2 hui hij.symm
  · have hc := hone b (by simpa using hzb) hbj
    change (G.neighborFinset u ∩ cellFinset G z b).card = 1 at hc
    obtain ⟨y,hy⟩ := Finset.card_pos.mp (show 0 < (G.neighborFinset u ∩ cellFinset G z b).card by omega)
    have huy : G.Adj u y := by simpa using (Finset.mem_inter.mp hy).1
    have hby : G.Adj b y := ((mem_cellFinset G z b y).mp (Finset.mem_inter.mp hy).2).1
    refine ⟨y,⟨huy,hby⟩,?_⟩
    intro r hr
    exact common_neighbor_unique hG hub hr.1 hr.2 huy hby

#print axioms regular_transport
end Erdos60.Completion

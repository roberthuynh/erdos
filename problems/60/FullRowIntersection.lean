import RegularTransport
import RegularPopulation

/-! Source correspondence: COUNT-BASED-COMPLETION.md Sections 2-3.
Historical source SHA256 (before public exposition edits):
d07eaa46889ac5a9808a097f281e43c25a768e5057e19ddefe5b72952d9eacbb.

RegularTransport proves actual common-neighbor transport from the exact cell
partition and saturation of all cells except the paired one; its low-isolation
input is proved internally from actual global budgets. RegularPopulation proves
the actual >q/100+1 regular-neighbor population needed here. The adjacent-row
case chooses a genuine regular neighbor different from y and transports through
it. For a nonedge, each genuine regular neighbor z of x produces a degree-q
neighbor w of y. A repeated w would violate actual C4-freeness, so the population
injects into y's actual low-neighbor set, contradicting the good-y bound.

Final endpoints full_rows_intersect, full_rows_intersection_card and
full_rows_distinct assume only actual graph, parity/order/degree cap and S,D
budgets, and the stated full/good conditions on x,y. Neither regular population,
row intersection nor a completion supplier is assumed by those endpoints.
The separate _of_regular_count lemma is an intermediate proof decomposition.
-/
namespace Erdos60.Completion
open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

/-- For disjoint full rows, each actual regular neighbor of x supplies a
low common neighbor with y. This is an intermediate actual geometric lemma. -/
theorem disjoint_rows_regular_neighbor_low (G : SimpleGraph V) (hG : NoFourCycle G)
    (q : ℕ) (hq : 100000000 ≤ q) (heven : Even q)
    (hN : Fintype.card V = q^2+q+1)
    (hS : 1000*(Finset.univ.filter (fun x => G.degree x ≤ q)).card ≤ 1001*q)
    (hD : 1000*(Finset.univ.filter (fun x => G.degree x ≤ q-1)).card ≤ q)
    {x y z : V} (_hx : G.degree x = q+1) (hy : G.degree y = q+1)
    (hnxy : ¬G.Adj x y) (hnone : ∀ a, ¬(G.Adj x a ∧ G.Adj y a))
    (hxz : G.Adj x z) (hreg : IsRegularVertex G q z) :
    ∃ w, G.Adj y w ∧ G.degree w = q ∧ G.Adj z w := by
  classical
  have hyz : y ≠ z := by intro h; exact hnxy (h.symm ▸ hxz)
  have hnzy : ¬G.Adj z y := fun h => hnone z ⟨hxz,h.symm⟩
  obtain ⟨hz,low,hzl,hdl,hfull⟩ := hreg
  have hr : IsRegularVertex G q z := ⟨hz,low,hzl,hdl,hfull⟩
  obtain ⟨iso,hzi,hiso,hm,hpart⟩ := regular_vertex_structure G hG q heven hN z low hz hzl hdl hfull
  obtain ⟨w,⟨hzw,hycell⟩,_⟩ := hpart y hyz hnzy
  have hyw : G.Adj y w := hycell.1.symm
  have hwlow : w=low := by
    by_contra hne
    have hwfull := hfull w hzw hne
    obtain ⟨a,ha,_⟩ := regular_transport G hG q hq heven hN hS hD hr hy hyz hnzy hzw hyw hwfull x hxz.symm
    exact hnone a ⟨ha.2,ha.1⟩
  exact ⟨w,hyw,hwlow.symm ▸ hdl,hzw⟩

/-- Geometric/injective step of the row-intersection proof. The population
bound is supplied by a separate actual count theorem in the final wrapper. -/
theorem full_rows_intersect_of_regular_count (G : SimpleGraph V) (hG : NoFourCycle G)
    (q : ℕ) (hq : 100000000 ≤ q) (heven : Even q)
    (hN : Fintype.card V = q^2+q+1)
    (hS : 1000*(Finset.univ.filter (fun x => G.degree x ≤ q)).card ≤ 1001*q)
    (hD : 1000*(Finset.univ.filter (fun x => G.degree x ≤ q-1)).card ≤ q)
    {x y : V} (hx : G.degree x = q+1) (hy : G.degree y = q+1)
    (hxy : x ≠ y)
    (hpop : q+100 < 100*((G.neighborFinset x).filter (IsRegularVertex G q)).card)
    (hygood : 100*((G.neighborFinset y).filter (fun a => G.degree a ≤ q)).card < q) :
    ∃! a, G.Adj x a ∧ G.Adj y a := by
  classical
  have hex : ∃ a, G.Adj x a ∧ G.Adj y a := by
    by_contra hnot
    have hnone : ∀ a, ¬(G.Adj x a ∧ G.Adj y a) := by simpa only [not_exists] using hnot
    let R := (G.neighborFinset x).filter (IsRegularVertex G q)
    by_cases hxyedge : G.Adj x y
    · have hR : 1 < R.card := by change 1 < ((G.neighborFinset x).filter (IsRegularVertex G q)).card; omega
      obtain ⟨z,hz,hzy⟩ := Finset.exists_mem_ne hR y
      have hxz : G.Adj x z := by simpa using (Finset.mem_filter.mp hz).1
      have hreg : IsRegularVertex G q z := (Finset.mem_filter.mp hz).2
      have hnzy : ¬G.Adj z y := fun h => hnone z ⟨hxz,h.symm⟩
      obtain ⟨a,ha,_⟩ := regular_transport G hG q hq heven hN hS hD hreg hy hzy.symm hnzy
        hxz.symm hxyedge.symm hx x hxz.symm
      exact hnone a ⟨ha.2,ha.1⟩
    · let L := (G.neighborFinset y).filter (fun a => G.degree a ≤ q)
      have hw : ∀ z : R, ∃ w : L, G.Adj z.val w.val := by
        intro z
        have hxz : G.Adj x z.val := by simpa using (Finset.mem_filter.mp z.property).1
        have hreg : IsRegularVertex G q z.val := (Finset.mem_filter.mp z.property).2
        obtain ⟨w,hyw,hdw,hzw⟩ := disjoint_rows_regular_neighbor_low G hG q hq heven hN hS hD
          hx hy hxyedge hnone hxz hreg
        exact ⟨⟨w,Finset.mem_filter.mpr ⟨by simpa using hyw,by omega⟩⟩,hzw⟩
      choose f hf using hw
      have hinj : Function.Injective f := by
        intro z t hft
        have hxz : G.Adj x z.val := by simpa using (Finset.mem_filter.mp z.property).1
        have hxt : G.Adj x t.val := by simpa using (Finset.mem_filter.mp t.property).1
        have hyw : G.Adj y (f z).val := by simpa using (Finset.mem_filter.mp (f z).property).1
        have hxw : x ≠ (f z).val := by intro h; exact hxyedge (h ▸ hyw).symm
        apply Subtype.ext
        exact common_neighbor_unique hG hxw hxz (hf z).symm hxt
          (by rw [hft]; exact (hf t).symm)
      have hc := Fintype.card_le_of_injective f hinj
      simp only [Fintype.card_coe] at hc
      change R.card ≤ L.card at hc
      change q+100 < 100*R.card at hpop
      change 100*L.card < q at hygood
      omega
  obtain ⟨a,ha⟩ := hex
  exact ⟨a,ha,fun b hb => common_neighbor_unique hG hxy hb.1 hb.2 ha.1 ha.2⟩

/-- Actual source Section3 conclusion, including a proved population supplier.
No regular-neighbor count or row-intersection assertion is assumed. -/
theorem full_rows_intersect (G : SimpleGraph V) (hG : NoFourCycle G)
    (q : ℕ) (hq : 100000000 ≤ q) (heven : Even q)
    (hN : Fintype.card V = q^2+q+1)
    (hcap : ∀ a, G.degree a ≤ q+1)
    (hS : 1000*(Finset.univ.filter (fun a => G.degree a ≤ q)).card ≤ 1001*q)
    (hD : 1000*(Finset.univ.filter (fun a => G.degree a ≤ q-1)).card ≤ q)
    {x y : V} (hx : G.degree x = q+1) (hy : G.degree y = q+1) (hxy : x ≠ y)
    (hxgood : 100*((G.neighborFinset x).filter (fun a => G.degree a ≤ q)).card < q)
    (hygood : 100*((G.neighborFinset y).filter (fun a => G.degree a ≤ q)).card < q) :
    ∃! a, G.Adj x a ∧ G.Adj y a := by
  have hpop := many_regular_neighbors G hG q heven hq hN hcap hS hD x hx hxgood
  exact full_rows_intersect_of_regular_count G hG q hq heven hN hS hD hx hy hxy hpop hygood

/-- The actual full rows have intersection cardinality exactly one. -/
theorem full_rows_intersection_card (G : SimpleGraph V) (hG : NoFourCycle G)
    (q : ℕ) (hq : 100000000 ≤ q) (heven : Even q)
    (hN : Fintype.card V = q^2+q+1)
    (hcap : ∀ a, G.degree a ≤ q+1)
    (hS : 1000*(Finset.univ.filter (fun a => G.degree a ≤ q)).card ≤ 1001*q)
    (hD : 1000*(Finset.univ.filter (fun a => G.degree a ≤ q-1)).card ≤ q)
    {x y : V} (hx : G.degree x = q+1) (hy : G.degree y = q+1) (hxy : x ≠ y)
    (hxgood : 100*((G.neighborFinset x).filter (fun a => G.degree a ≤ q)).card < q)
    (hygood : 100*((G.neighborFinset y).filter (fun a => G.degree a ≤ q)).card < q) :
    (G.neighborFinset x ∩ G.neighborFinset y).card = 1 := by
  have hh := full_rows_intersect G hG q hq heven hN hcap hS hD hx hy hxy hxgood hygood
  apply Finset.card_eq_one_iff_existsUnique.mpr
  simpa only [Finset.mem_inter,SimpleGraph.mem_neighborFinset] using hh

/-- Distinct good full vertices yield genuinely distinct rows, not repeated lines. -/
theorem full_rows_distinct (G : SimpleGraph V) (hG : NoFourCycle G)
    (q : ℕ) (hq : 100000000 ≤ q) (heven : Even q)
    (hN : Fintype.card V = q^2+q+1)
    (hcap : ∀ a, G.degree a ≤ q+1)
    (hS : 1000*(Finset.univ.filter (fun a => G.degree a ≤ q)).card ≤ 1001*q)
    (hD : 1000*(Finset.univ.filter (fun a => G.degree a ≤ q-1)).card ≤ q)
    {x y : V} (hx : G.degree x = q+1) (hy : G.degree y = q+1) (hxy : x ≠ y)
    (hxgood : 100*((G.neighborFinset x).filter (fun a => G.degree a ≤ q)).card < q)
    (hygood : 100*((G.neighborFinset y).filter (fun a => G.degree a ≤ q)).card < q) :
    G.neighborFinset x ≠ G.neighborFinset y := by
  intro heq
  have hh := full_rows_intersection_card G hG q hq heven hN hcap hS hD hx hy hxy hxgood hygood
  rw [← heq,Finset.inter_self,G.card_neighborFinset_eq_degree,hx] at hh
  omega

#print axioms full_rows_intersect
#print axioms full_rows_intersection_card
#print axioms full_rows_distinct
#print axioms full_rows_intersect_of_regular_count
end Erdos60.Completion

import Openmath.AllHTopCritical.SmallFloors

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.AllHTopCritical
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {h q : ℕ} {A B X Y : Finset V}

omit [Fintype V] in
lemma lowRoots_subset (q : ℕ) (X Y : Finset V) : lowRoots q G X Y ⊆ X := filter_subset _ _
omit [Fintype V] in
lemma lowRoots_degree {q : ℕ} {X Y : Finset V} {v : V} (hv : v ∈ lowRoots q G X Y) : dg G Y v = q-1 :=
  (mem_filter.mp hv).2
omit [Fintype V] in
lemma lowRoots_edges (q : ℕ) (X Y : Finset V) : ec G (lowRoots q G X Y) Y = (q-1)*#(lowRoots q G X Y) := by
  unfold ec
  calc
    _ = ∑ _v ∈ lowRoots q G X Y, (q-1) := sum_congr rfl fun v hv => lowRoots_degree hv
    _ = _ := by simp [mul_comm]


omit [Fintype V] in
lemma retained_subset (q : ℕ) (X Y : Finset V) : retained q G X Y ⊆ X∪Y := union_subset_union sdiff_subset Subset.rfl

/-- A proved internal diagonal interface. It is never a public endpoint premise. -/
structure Diagonal (h q : ℕ) (G : SimpleGraph V) (A B X Y : Finset V) : Prop where
  X_subset : X ⊆ A
  Y_subset : Y ⊆ B
  surplus : #X = #Y+(h-1)
  smaller_order : 2*q-h-1 ≤ #Y
  proper : #X+#Y < Fintype.card V
  deficit : coreDefect q G X Y = (constant h q : ℤ)+1
  saturated : ∀ v ∈ Y, G.degree v = 2*q-2
  crossing : (ec G Y (A\X) : ℤ) = (q : ℤ)+h-offset h

namespace Diagonal
variable (host : Host h q G A B) (d : Diagonal h q G A B X Y)
include host d

lemma disjoint : Disjoint X Y := host.disjoint.mono d.X_subset d.Y_subset
lemma order : 2*q+1 ≤ #X+#Y := by
  have hw := d.smaller_order
  have hi := d.surplus
  have hn := host.parameters.numeric
  have hh := host.parameters.height
  omega
lemma minimum_X : ∀ v ∈ X, q-1 ≤ dg G Y v :=
  host.internal_min_left d.X_subset d.Y_subset (d.order host) d.proper d.deficit
lemma minimum_Y : ∀ v ∈ Y, q-1 ≤ dg G X v := by
  apply host.swap.internal_min_left d.Y_subset d.X_subset
    (by have ho := d.order host; omega) (by have hp := d.proper; omega)
  rw [← coreDefect_symm]
  exact d.deficit

lemma strong_minimum_Y {v : V} (hv : v ∈ Y) :
    (q : ℤ)+(offset h : ℤ)-h-2 ≤ dg G X v := by
  have hs := d.saturated v hv
  have hd := dg_sdiff_add (G := G) d.X_subset v
  rw [dg_eq_degree host.bipartite.symm (d.Y_subset hv), hs] at hd
  have he := dg_le_ec_left (G := G) (Y := A\X) hv
  have hc := d.crossing
  have hq := host.parameters.q_pos
  zify at hd he
  have hD : ((2*q-2 : ℕ) : ℤ) = 2*(q : ℤ)-2 := by omega
  rw [hD] at hd
  linarith

omit d in
lemma cap_internal {v : V} : dg G Y v ≤ 2*q-2 :=
  (dg_le_ambient Y v).trans (host.cap_degree v)

lemma low_bound : #(lowRoots q G X Y) ≤ 2*h-2 := by
  have hq := host.parameters.q_pos
  have hD : ((2*q-2 : ℕ) : ℤ) = 2*(q : ℤ)-2 := by omega
  have hr : ((q-1 : ℕ) : ℤ) = (q : ℤ)-1 := by omega
  have hlo := deficiency_le_subset (G := G) (2*(q : ℤ)-2) (lowRoots_subset (G := G) q X Y)
    (fun v _ => show (dg G Y v : ℤ) ≤ 2*q-2 by have hc := Diagonal.cap_internal host (Y := Y) (v := v); omega)
  rw [deficiency_eq, deficiency_eq] at hlo
  have he := (lowRoots_edges (G := G) q X Y)
  have hi := d.surplus
  have hf := d.deficit
  have hc := host.parameters.constant_cast
  have hs := host.parameters.surplus_cast
  have hk := host.parameters.kappa
  have hh := host.parameters.height_int
  zify at he hi
  rw [hr] at he
  unfold coreDefect at hf
  by_contra hn
  have hnz : 2*(h : ℤ)-1 ≤ #(lowRoots q G X Y) := by omega
  have hp := mul_nonneg (show 0 ≤ (q : ℤ)-1 by omega)
    (show 0 ≤ (#(lowRoots q G X Y) : ℤ)-(2*h-1) by omega)
  nlinarith

lemma retained_deficit : coreDefect q G (X\lowRoots q G X Y) Y =
    (constant h q : ℤ)+1 := by
  have he := ec_sdiff_add_left (G := G) (lowRoots_subset (G := G) q X Y) Y
  have hc := card_sdiff_add_card_eq_card (lowRoots_subset (G := G) q X Y)
  have hl := (lowRoots_edges (G := G) q X Y)
  have hf := d.deficit
  have hq := host.parameters.q_pos
  have hr : ((q-1 : ℕ) : ℤ) = (q : ℤ)-1 := by omega
  zify at he hc hl
  rw [hr] at hl
  unfold coreDefect at hf ⊢
  nlinarith

lemma retained_disjoint : Disjoint (X\lowRoots q G X Y) Y := d.disjoint host |>.mono sdiff_subset Subset.rfl
lemma retained_card : #(retained q G X Y) = #(X\lowRoots q G X Y)+#Y :=
  card_union_of_disjoint (d.retained_disjoint host)
lemma retained_proper : #(retained q G X Y) < Fintype.card V := by
  have hc := d.retained_card host
  have hl := card_le_card (sdiff_subset : X\lowRoots q G X Y ⊆ X)
  have hp := d.proper
  omega

lemma retained_min_X {v : V} (hv : v ∈ X\lowRoots q G X Y) : q ≤ dg G Y v := by
  have hm := d.minimum_X host v (mem_sdiff.mp hv).1
  have hn : dg G Y v ≠ q-1 := by
    intro he
    exact (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨(mem_sdiff.mp hv).1, he⟩)
  omega

lemma retained_min_Y {v : V} (hv : v ∈ Y) : q ≤ dg G (X\lowRoots q G X Y) v := by
  have hm := d.strong_minimum_Y host hv
  have hd := dg_sdiff_add (G := G) (lowRoots_subset (G := G) q X Y) v
  have hb := dg_le_card (G := G) (lowRoots q G X Y) v
  have hk := d.low_bound host
  have hn := host.parameters.numeric
  have hh := host.parameters.height_int
  omega

lemma retained_minimum : ∀ v ∈ retained q G X Y, q ≤ dg G (retained q G X Y) v := by
  intro v hv
  rcases mem_union.mp hv with hx | hy
  · rw [retained, host.dg_union_left (sdiff_subset.trans d.X_subset) d.Y_subset
      (d.X_subset (mem_sdiff.mp hx).1)]
    exact d.retained_min_X host hx
  · rw [retained, host.dg_union_right (sdiff_subset.trans d.X_subset) d.Y_subset (d.Y_subset hy)]
    exact d.retained_min_Y host hy

omit d in
lemma retained_cap : ∀ v ∈ retained q G X Y, dg G (retained q G X Y) v ≤ 2*q-2 := by
  intro v _
  exact (dg_le_ambient _ v).trans (host.cap_degree v)

lemma retained_order : 4*q-3*h-1 ≤ #(retained q G X Y) := by
  have hw := d.smaller_order
  have hi := d.surplus
  have hc := card_sdiff_add_card_eq_card (lowRoots_subset (G := G) q X Y)
  have hk := d.low_bound host
  have hs := d.retained_card host
  have hn := host.parameters.numeric
  have hh := host.parameters.height
  omega

lemma retained_eligible : 2*q ≤ #(retained q G X Y) := by
  have ho := d.retained_order host
  have hn := host.parameters.numeric
  have hh := host.parameters.height
  omega

lemma retained_floor : ∀ Z ⊆ retained q G X Y, h ≤ #Z →
    (constant h q : ℤ)+1 ≤ ((q : ℤ)-1)*#Z-
      ((G.induce (Z : Set V)).edgeSet.ncard : ℤ) := by
  intro Z hZ hl
  exact host.extended_floor (d.retained_proper host) hZ hl

lemma actual_qcore : IsOriginalQCore q G (X∪Y) (retained q G X Y) := by
  refine ⟨(retained_subset (G := G) q X Y), ?_, d.retained_minimum host, ?_⟩
  · have ho := d.retained_eligible host
    have hq := host.parameters.q_pos
    exact card_pos.mp (by omega)
  · intro Z hZ hm v hv
    rcases mem_union.mp (hZ hv) with hx | hy
    · by_cases hl : v ∈ lowRoots q G X Y
      · have hd := dg_mono (G := G) hZ v
        rw [host.dg_union_left d.X_subset d.Y_subset (d.X_subset hx), lowRoots_degree hl] at hd
        have hvq := hm v hv
        have hq := host.parameters.q_pos
        omega
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hx, hl⟩)
    · exact mem_union_right _ hy

end Diagonal
end Erdos585.AllHTopCritical

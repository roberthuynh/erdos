import Openmath.AllHTopCritical.Rigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.AllHTopCritical
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {h q : ℕ} {A B : Finset V}

namespace Host
variable (host : Host h q G A B)
include host

lemma swap : Host h q G B A := by
  refine ⟨host.parameters, host.disjoint.symm, ?_, host.balanced.symm,
    host.bipartite.symm, host.order, host.min_degree, host.cap_degree,
    host.edges, host.no_regular, host.proper⟩
  rw [union_comm]
  exact host.cover

lemma induced_quadratic (Z : Finset V) :
    4*((G.induce (Z : Set V)).edgeSet.ncard : ℤ) ≤ (#Z : ℤ)^2 := by
  have hd : Disjoint (Z∩A) (Z∩B) := host.disjoint.mono inter_subset_right inter_subset_right
  have hu : (Z∩A)∪(Z∩B) = Z := by
    rw [← inter_union_distrib_left, host.cover, inter_univ]
  have hc := card_union_of_disjoint hd
  rw [hu] at hc
  have he := induced_edges_eq_ec host.disjoint host.bipartite
    (inter_subset_right : Z∩A ⊆ A) (inter_subset_right : Z∩B ⊆ B)
  rw [hu] at he
  have hb := ec_le_product (G := G) (Z∩A) (Z∩B)
  zify at hc hb
  rw [he]
  nlinarith [sq_nonneg ((#(Z∩A) : ℤ)-#(Z∩B))]

/-- Both the original eligible floor and every newly needed small-order floor. -/
lemma extended_floor {W : Finset V} (hp : #W < Fintype.card V)
    {Z : Finset V} (hZ : Z ⊆ W) (hl : h ≤ #Z) :
    (constant h q : ℤ)+1 ≤ ((q : ℤ)-1)*#Z-
      ((G.induce (Z : Set V)).edgeSet.ncard : ℤ) := by
  by_cases he : 2*q ≤ #Z
  · exact host.proper Z he (lt_of_le_of_lt (card_le_card hZ) hp)
  · exact host.parameters.small_floor hl (by omega) (host.induced_quadratic Z)

lemma dg_same {X : Finset V} (hX : X ⊆ A) {v : V} (hv : v ∈ A) : dg G X v = 0 := by
  unfold dg
  apply card_eq_zero.mpr
  apply eq_empty_of_forall_notMem
  intro w hw
  have hh := mem_filter.mp hw
  exact Finset.disjoint_left.mp host.disjoint (hX hh.1)
    (host.bipartite.mem_of_mem_adj hv hh.2)

lemma dg_union_left {X Y : Finset V} (hX : X ⊆ A) (hY : Y ⊆ B)
    {v : V} (hv : v ∈ A) : dg G (X∪Y) v = dg G Y v := by
  rw [dg_union_of_disjoint (G := G) (host.disjoint.mono hX hY), host.dg_same hX hv, zero_add]

lemma dg_union_right {X Y : Finset V} (hX : X ⊆ A) (hY : Y ⊆ B)
    {v : V} (hv : v ∈ B) : dg G (X∪Y) v = dg G X v := by
  rw [union_comm]
  exact host.swap.dg_union_left hY hX hv

lemma internal_min_left {X Y : Finset V} (hX : X ⊆ A) (hY : Y ⊆ B)
    (hl : 2*q+1 ≤ #X+#Y) (hp : #X+#Y < Fintype.card V)
    (hf : coreDefect q G X Y = (constant h q : ℤ)+1) :
    ∀ v ∈ X, q-1 ≤ dg G Y v := by
  intro v hv
  have hs := host.paired_floor ((erase_subset v X).trans hX) hY
    (by have hc := card_erase_add_one hv; omega)
    (by have hc := card_erase_le (a := v) (s := X); omega)
  have he := potential_erase_left (G := G) (2*(q : ℤ)-2) hv Y
  have ht := twice_coreDefect (G := G) q X Y
  have hu := twice_coreDefect (G := G) q (X.erase v) Y
  have hq := host.parameters.q_pos
  have hz : (q : ℤ)-1 ≤ dg G Y v := by nlinarith
  omega

end Host
end Erdos585.AllHTopCritical

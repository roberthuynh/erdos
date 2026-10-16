import EvenFactor.Canonical

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Finset SimpleGraph Function
namespace Erdos585.EvenFactorCriterion
open QB4 FactorMatching
universe u
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma dg_induce (A : Finset V) (v : (A : Set V)) :
    dg G A v = (G.induce (A : Set V)).degree v := by
  classical
  have hh := congrArg Finset.card (G.map_neighborFinset_induce v)
  have he : A.filter (G.Adj v) = G.neighborFinset v ∩ A := by
    ext w
    simp [and_comm]
  unfold dg
  rw [he]
  have hc := hh.symm
  simp only [card_map, card_neighborFinset_eq_degree] at hc
  simp only [Finset.toFinset_coe] at hc
  exact hc.trans (FactorMatching.degree_fintype_irrel (G.induce (A : Set V)) v _ _)

/-- Handshaking on the ACTUAL original induced support, not a parity supplier. -/
theorem ec_self_even (A : Finset V) : Even (ec G A A) := by
  classical
  have he : ec G A A = ∑ v : (A : Set V), (G.induce (A : Set V)).degree v := by
    unfold ec
    simp_rw [← dg_induce]
    exact (Finset.sum_coe_sort A (fun v : V => dg G A v)).symm
  rw [he, (G.induce (A : Set V)).sum_degrees_eq_twice_card_edges]
  exact even_two_mul _

lemma mem_componentVerts_iff (R : Finset V)
    (C : (G.induce (R : Set V)).ConnectedComponent) (v : V) :
    v ∈ componentVerts G R C ↔
      ∃ hv : v ∈ R, (⟨v,hv⟩ : (R : Set V)) ∈ C.supp := by
  classical
  unfold componentVerts
  simp only [mem_image, Set.mem_toFinset]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w.property,hw⟩
  · rintro ⟨hv,hC⟩
    exact ⟨⟨v,hv⟩,hC,rfl⟩

/-- No original edge can leave an ACTUAL remainder component inside R. -/
theorem component_no_external_edge (R : Finset V)
    (C : (G.induce (R : Set V)).ConnectedComponent) (v w : V)
    (hv : v ∈ componentVerts G R C) (hw : w ∈ R) (hadj : G.Adj v w) :
    w ∈ componentVerts G R C := by
  obtain ⟨hvr,hvC⟩ := (mem_componentVerts_iff G R C v).mp hv
  apply (mem_componentVerts_iff G R C w).mpr
  refine ⟨hw, ?_⟩
  exact C.mem_supp_of_adj_mem_supp hvC hadj

lemma dg_component (R : Finset V)
    (C : (G.induce (R : Set V)).ConnectedComponent) (v : V)
    (hv : v ∈ componentVerts G R C) :
    dg G R v = dg G (componentVerts G R C) v := by
  unfold dg
  congr 1
  ext w
  simp only [mem_filter]
  exact ⟨fun h => ⟨component_no_external_edge G R C v w hv h.1 h.2,h.2⟩,
    fun h => ⟨componentVerts_subset G R C h.1,h.2⟩⟩

lemma dg_full_degree (v : V) : dg G univ v = G.degree v := by
  rw [← card_neighborFinset_eq_degree]
  unfold dg
  congr 1
  ext w
  simp

/-- Actual original degree partition around one actual remainder component. -/
theorem component_degree_partition (S T : Finset V) (hST : Disjoint S T)
    (C : (G.induce ((univ \ (S ∪ T) : Finset V) : Set V)).ConnectedComponent) :
    (∑ v ∈ componentVerts G (univ \ (S ∪ T)) C, G.degree v) =
      ec G (componentVerts G (univ \ (S ∪ T)) C)
        (componentVerts G (univ \ (S ∪ T)) C) +
      ec G (componentVerts G (univ \ (S ∪ T)) C) S +
      ec G (componentVerts G (univ \ (S ∪ T)) C) T := by
  classical
  unfold ec
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro v hv
  have hr := dg_sdiff_add (G := G) (S := univ) (T := S ∪ T)
    (subset_univ (S ∪ T)) v
  rw [dg_union_of_disjoint hST, dg_full_degree G v,
    dg_component G (univ \ (S ∪ T)) C v hv] at hr
  omega

/-- The cardinal expression of the proposed lifted component has precisely
original odd-to-T parity; no component bijection is asserted by this leaf. -/
theorem component_lifted_parity (q : ℕ) (heven : Even q)
    (S T : Finset V) (hST : Disjoint S T)
    (C : (G.induce ((univ \ (S ∪ T) : Finset V) : Set V)).ConnectedComponent) :
    Odd (q * #(componentVerts G (univ \ (S ∪ T)) C) +
      (∑ v ∈ componentVerts G (univ \ (S ∪ T)) C, G.degree v) +
      ec G S (componentVerts G (univ \ (S ∪ T)) C)) ↔
    Odd (ec G (componentVerts G (univ \ (S ∪ T)) C) T) := by
  let A := componentVerts G (univ \ (S ∪ T)) C
  have he := component_degree_partition G S T hST C
  change (∑ v ∈ A, G.degree v) = ec G A A + ec G A S + ec G A T at he
  have hi := ec_self_even G A
  obtain ⟨a,ha⟩ := heven
  obtain ⟨b,hb⟩ := hi
  change Odd (q * #A + (∑ v ∈ A, G.degree v) + ec G S A) ↔ Odd (ec G A T)
  rw [he, ec_comm S A]
  have hh : q * #A + (ec G A A + ec G A S + ec G A T) + ec G A S =
      2 * (a * #A + b + ec G A S) + ec G A T := by
    rw [ha,hb]
    ring
  rw [hh, Nat.odd_iff, Nat.odd_iff]
  simp [Nat.add_mod, Nat.mul_mod]

end Erdos585.EvenFactorCriterion

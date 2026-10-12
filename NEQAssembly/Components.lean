import NEQPort.EmptyBarrier

/- 
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
namespace Erdos585.NEQAssembly
open QB4 B5 NEQ
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

lemma mem_componentVerts {R : Finset V}
    (C : (G.induce (R : Set V)).ConnectedComponent) (v : V) :
    v ∈ componentVerts G R C ↔
      ∃ h : v ∈ R, (G.induce (R : Set V)).connectedComponentMk ⟨v, h⟩ = C := by
  classical
  constructor
  · intro hv
    obtain ⟨w, hw, heq⟩ := mem_image.mp hv
    subst v
    exact ⟨w.property, by simpa only [Set.mem_toFinset, ConnectedComponent.mem_supp_iff] using hw⟩
  · rintro ⟨hv, hC⟩
    exact mem_image.mpr ⟨⟨v, hv⟩,
      by simpa only [Set.mem_toFinset, ConnectedComponent.mem_supp_iff] using hC, rfl⟩

lemma componentVerts_subset {R : Finset V}
    (C : (G.induce (R : Set V)).ConnectedComponent) :
    componentVerts G R C ⊆ R := by
  intro v hv
  exact ((mem_componentVerts C v).mp hv).choose

lemma componentVerts_nonempty {R : Finset V}
    (C : (G.induce (R : Set V)).ConnectedComponent) :
    (componentVerts G R C).Nonempty := by
  obtain ⟨v, hv⟩ := C.nonempty_supp
  exact ⟨v, (mem_componentVerts C v).mpr ⟨v.property, hv⟩⟩

lemma componentVerts_disjoint {R : Finset V}
    {C E : (G.induce (R : Set V)).ConnectedComponent} (hCE : C ≠ E) :
    Disjoint (componentVerts G R C) (componentVerts G R E) := by
  apply Finset.disjoint_left.mpr
  intro v hvC hvE
  obtain ⟨hC, heC⟩ := (mem_componentVerts C v).mp hvC
  obtain ⟨hE, heE⟩ := (mem_componentVerts E v).mp hvE
  exact hCE (heC.symm.trans heE)

lemma componentVerts_adj_closed {R : Finset V}
    (C : (G.induce (R : Set V)).ConnectedComponent) {v w : V}
    (hv : v ∈ componentVerts G R C) (hw : w ∈ R) (ha : G.Adj v w) :
    w ∈ componentVerts G R C := by
  obtain ⟨hvR, hvC⟩ := (mem_componentVerts C v).mp hv
  apply (mem_componentVerts C w).mpr
  refine ⟨hw, ?_⟩
  have hh : (G.induce (R : Set V)).Adj ⟨v, hvR⟩ ⟨w, hw⟩ := ha
  exact (C.mem_supp_congr_adj hh).mp hvC

lemma components_biUnion (R : Finset V)
    [Fintype (G.induce (R : Set V)).ConnectedComponent] :
    (univ : Finset (G.induce (R : Set V)).ConnectedComponent).biUnion
      (componentVerts G R) = R := by
  ext v
  constructor
  · intro hv
    obtain ⟨C, _, hvC⟩ := mem_biUnion.mp hv
    exact componentVerts_subset C hvC
  · intro hv
    exact mem_biUnion.mpr ⟨(G.induce (R : Set V)).connectedComponentMk ⟨v, hv⟩,
      mem_univ _, (mem_componentVerts _ v).mpr ⟨hv, rfl⟩⟩

lemma sum_components (R : Finset V)
    [Fintype (G.induce (R : Set V)).ConnectedComponent] (f : V → ℤ) :
    (∑ C : (G.induce (R : Set V)).ConnectedComponent,
      ∑ v ∈ componentVerts G R C, f v) = ∑ v ∈ R, f v := by
  have hp : ((univ : Finset (G.induce (R : Set V)).ConnectedComponent) :
      Set (G.induce (R : Set V)).ConnectedComponent).PairwiseDisjoint
      (componentVerts G R) := by
    intro C _ E _ hCE
    exact componentVerts_disjoint hCE
  rw [← sum_biUnion hp, components_biUnion]

lemma sum_component_ec (R X : Finset V)
    [Fintype (G.induce (R : Set V)).ConnectedComponent] :
    (∑ C : (G.induce (R : Set V)).ConnectedComponent,
      (ec G (componentVerts G R C) X : ℤ)) = ec G R X := by
  simp only [ec, Nat.cast_sum]
  exact sum_components R (fun v => (dg G X v : ℤ))

lemma sum_component_deficiency (D : ℤ) (R : Finset V)
    [Fintype (G.induce (R : Set V)).ConnectedComponent] :
    (∑ C : (G.induce (R : Set V)).ConnectedComponent,
      deficiency D G univ (componentVerts G R C)) = deficiency D G univ R :=
  sum_components R (fun v => D - (dg G univ v : ℤ))

lemma component_cross_complement_zero {R : Finset V}
    (C : (G.induce (R : Set V)).ConnectedComponent) :
    ec G (componentVerts G R C) (R \ componentVerts G R C) = 0 := by
  unfold ec
  apply sum_eq_zero
  intro v hv
  unfold dg
  apply card_eq_zero.mpr
  apply Finset.eq_empty_of_forall_notMem
  intro w hw
  obtain ⟨hwR, ha⟩ := mem_filter.mp hw
  have hx := componentVerts_adj_closed C hv (mem_sdiff.mp hwR).1 ha
  exact (mem_sdiff.mp hwR).2 hx

lemma component_internal_eq {R : Finset V}
    (C : (G.induce (R : Set V)).ConnectedComponent) :
    ec G (componentVerts G R C) R =
      ec G (componentVerts G R C) (componentVerts G R C) := by
  have h := ec_sdiff_add_right (G := G) (componentVerts_subset C) (componentVerts G R C)
  rw [component_cross_complement_zero, zero_add] at h
  exact h.symm

lemma induced_degree_eq_dg (X : Finset V) (v : (X : Set V)) :
    (G.induce (X : Set V)).degree v = dg G X v := by
  rw [← card_neighborFinset_eq_degree]
  unfold dg
  apply card_bij (fun (w : (X : Set V)) _ => (w : V))
  · intro w hw
    exact mem_filter.mpr ⟨w.property,
      by simpa only [SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj] using hw⟩
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro w hw
    obtain ⟨hwX, hvw⟩ := mem_filter.mp hw
    exact ⟨⟨w, hwX⟩,
      by simpa only [SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj] using hvw, rfl⟩

lemma ec_self_eq_twice_induced_edges (X : Finset V) :
    ec G X X = 2 * (G.induce (X : Set V)).edgeSet.ncard := by
  have h := ec_univ_eq_twice_edges (G := G.induce (X : Set V))
  unfold ec at h
  simp_rw [dg_univ_eq_degree, induced_degree_eq_dg] at h
  have hu : (univ : Finset (X : Set V)) = X.attach := by ext v; simp
  rw [hu] at h
  exact (sum_attach X (fun v : V => dg G X v)).symm.trans h

lemma ec_self_even (X : Finset V) : Even (ec G X X) := by
  rw [ec_self_eq_twice_induced_edges]
  exact even_two_mul _

#print axioms mem_componentVerts
#print axioms componentVerts_subset
#print axioms componentVerts_nonempty
#print axioms componentVerts_disjoint
#print axioms componentVerts_adj_closed
#print axioms components_biUnion
#print axioms sum_components
#print axioms sum_component_ec
#print axioms sum_component_deficiency
#print axioms component_cross_complement_zero
#print axioms component_internal_eq
#print axioms induced_degree_eq_dg
#print axioms ec_self_eq_twice_induced_edges
#print axioms ec_self_even
end Erdos585.NEQAssembly

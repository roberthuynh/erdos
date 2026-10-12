import Openmath.AllHTopCritical.LowRoots

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

namespace Host
variable (host : Host h q G A B)
include host

/-- The largest selector is called only after every paired resource is derived. -/
lemma exclude_largest {P Q : Finset V} (hP : P ⊆ A) (hQ : Q ⊆ B)
    (hc : #Q = #P+(h-1)) (hPn : P.Nonempty)
    (hmP : ∀ v ∈ P, q ≤ dg G Q v) (hmQ : ∀ v ∈ Q, q ≤ dg G P v)
    (hf : coreDefect q G P Q = (constant h q : ℤ)+1)
    (hfloor : ∀ Z ⊆ P∪Q, h ≤ #Z → (constant h q : ℤ)+1 ≤
      ((q : ℤ)-1)*#Z-((G.induce (Z : Set V)).edgeSet.ncard : ℤ)) : False := by
  have p := host.parameters
  have d : AllHLargestNonstrict.Data h q (selectorOffset h) (h-1) G P Q := by
    refine ⟨p.largest_parameters, host.disjoint.mono hP hQ, hc, hmP, ?_, hmQ, ?_, ?_, ?_⟩
    · intro v _; exact (dg_le_ambient Q v).trans (host.cap_degree v)
    · intro v _; exact (dg_le_ambient P v).trans (host.cap_degree v)
    · rw [deficiency_eq]
      have hconstant := p.constant_cast
      have hoff := p.selector_cast
      zify at hc
      unfold coreDefect at hf
      nlinarith
    · intro P' hP' Q' hQ' hl _
      have hd := host.disjoint.mono (hP'.trans hP) (hQ'.trans hQ)
      have hcard := card_union_of_disjoint hd
      have ff := hfloor (P'∪Q') (union_subset_union hP' hQ') (by omega)
      rw [induced_edges_eq_ec host.disjoint host.bipartite (hP'.trans hP) (hQ'.trans hQ), hcard] at ff
      have hconstant := p.constant_cast
      have hoff := p.selector_cast
      unfold potential
      push_cast at ff ⊢
      nlinarith
  obtain ⟨O, hO, hcO, hcuts⟩ := d.common_omission (AllHLargestNonstrict.petal_escape (G := G))
  have ff := factor_of_common_omission q (h-1) hc hO hcO hcuts
  obtain ⟨H, _, hne, hreg⟩ := factor_exact_subgraph p.q_pos hPn
    ((host.disjoint.mono hP hQ).mono_right sdiff_subset) ff
  exact host.no_regular ⟨H, hne, hreg⟩

/-- The next selector uses the SAME original pairs and the same shifted offset. -/
lemma exclude_next {P Q : Finset V} (hP : P ⊆ A) (hQ : Q ⊆ B)
    (hc : #Q = #P+(h-2)) (hPn : P.Nonempty)
    (hmP : ∀ v ∈ P, q ≤ dg G Q v) (hmQ : ∀ v ∈ Q, q ≤ dg G P v)
    (hf : coreDefect q G P Q = (constant h q : ℤ)+1)
    (hfloor : ∀ Z ⊆ P∪Q, h ≤ #Z → (constant h q : ℤ)+1 ≤
      ((q : ℤ)-1)*#Z-((G.induce (Z : Set V)).edgeSet.ncard : ℤ)) : False := by
  have p := host.parameters
  have d : AllHNextNonstrict.Data h q (selectorOffset h) (h-2) G P Q := by
    refine ⟨p.next_parameters, host.disjoint.mono hP hQ, hc, hmP, ?_, hmQ, ?_, ?_, ?_⟩
    · intro v _; exact (dg_le_ambient Q v).trans (host.cap_degree v)
    · intro v _; exact (dg_le_ambient P v).trans (host.cap_degree v)
    · rw [deficiency_eq]
      have hconstant := p.constant_cast
      have hoff := p.selector_cast
      zify at hc
      unfold coreDefect at hf
      nlinarith
    · intro P' hP' Q' hQ' hl _
      have hd := host.disjoint.mono (hP'.trans hP) (hQ'.trans hQ)
      have hcard := card_union_of_disjoint hd
      have ff := hfloor (P'∪Q') (union_subset_union hP' hQ') (by omega)
      rw [induced_edges_eq_ec host.disjoint host.bipartite (hP'.trans hP) (hQ'.trans hQ), hcard] at ff
      have hconstant := p.constant_cast
      have hoff := p.selector_cast
      unfold potential
      push_cast at ff ⊢
      nlinarith
  obtain ⟨O, hO, hcO, hcuts⟩ := d.common_omission
    (AllHNextNonstrict.petal_escape (G := G)) (AllHNextNonstrict.top_escape (G := G))
  have ff := factor_of_common_omission q (h-2) hc hO hcO hcuts
  obtain ⟨H, _, hne, hreg⟩ := factor_exact_subgraph p.q_pos hPn
    ((host.disjoint.mono hP hQ).mono_right sdiff_subset) ff
  exact host.no_regular ⟨H, hne, hreg⟩

end Host

namespace Diagonal
variable (host : Host h q G A B) (d : Diagonal h q G A B X Y)
include host d

lemma retained_shores : q ≤ #Y ∧ q ≤ #(X\lowRoots q G X Y) := by
  have hw := d.smaller_order
  have hn := host.parameters.numeric
  have hh := host.parameters.height
  have hq := host.parameters.q_pos
  have hY : q ≤ #Y := by omega
  obtain ⟨v, hv⟩ := card_pos.mp (show 0 < #Y by omega)
  have hm := d.retained_min_Y host hv
  have hc := dg_le_card (G := G) (X\lowRoots q G X Y) v
  exact ⟨hY, by omega⟩

lemma exclude_low_counts : #(lowRoots q G X Y) ≠ 0 ∧ #(lowRoots q G X Y) ≠ 1 := by
  have hc := card_sdiff_add_card_eq_card (lowRoots_subset (G := G) q X Y)
  have hi := d.surplus
  have hh := host.parameters.height
  have hp : Y.Nonempty := card_pos.mp (by have hs := d.retained_shores host; have hq := host.parameters.q_pos; omega)
  have hf : coreDefect q G Y (X\lowRoots q G X Y) = (constant h q : ℤ)+1 := by
    rw [← coreDefect_symm]
    exact d.retained_deficit host
  have hfloor : ∀ Z ⊆ Y∪(X\lowRoots q G X Y), h ≤ #Z →
      (constant h q : ℤ)+1 ≤ ((q : ℤ)-1)*#Z-
        ((G.induce (Z : Set V)).edgeSet.ncard : ℤ) := by
    rw [union_comm]
    exact d.retained_floor host
  constructor
  · intro hk
    exact host.swap.exclude_largest d.Y_subset (sdiff_subset.trans d.X_subset)
      (by omega) hp (fun v hv => d.retained_min_Y host hv)
      (fun v hv => d.retained_min_X host hv) hf hfloor
  · intro hk
    exact host.swap.exclude_next d.Y_subset (sdiff_subset.trans d.X_subset)
      (by omega) hp (fun v hv => d.retained_min_Y host hv)
      (fun v hv => d.retained_min_X host hv) hf hfloor

lemma exclude_high_counts : #(lowRoots q G X Y) ≠ 2*h-3 ∧ #(lowRoots q G X Y) ≠ 2*h-2 := by
  have hc := card_sdiff_add_card_eq_card (lowRoots_subset (G := G) q X Y)
  have hi := d.surplus
  have hh := host.parameters.height
  have hp : (X\lowRoots q G X Y).Nonempty := card_pos.mp
    (by have hs := d.retained_shores host; have hq := host.parameters.q_pos; omega)
  constructor
  · intro hk
    exact host.exclude_next (sdiff_subset.trans d.X_subset) d.Y_subset
      (by omega) hp (fun v hv => d.retained_min_X host hv)
      (fun v hv => d.retained_min_Y host hv) (d.retained_deficit host) (d.retained_floor host)
  · intro hk
    exact host.exclude_largest (sdiff_subset.trans d.X_subset) d.Y_subset
      (by omega) hp (fun v hv => d.retained_min_X host hv)
      (fun v hv => d.retained_min_Y host hv) (d.retained_deficit host) (d.retained_floor host)

theorem deleted_count : 2 ≤ #(lowRoots q G X Y) ∧ #(lowRoots q G X Y) ≤ 2*h-4 := by
  have hl := d.exclude_low_counts host
  have hu := d.exclude_high_counts host
  have hb := d.low_bound host
  have hh := host.parameters.height
  omega

lemma exact_minimum : ∃ v ∈ X, dg G Y v = q-1 := by
  have hc := d.deleted_count host
  obtain ⟨v, hv⟩ := card_pos.mp (show 0 < #(lowRoots q G X Y) by omega)
  exact ⟨v, (lowRoots_subset (G := G) q X Y) hv, lowRoots_degree hv⟩

theorem conclusion : DiagonalConclusion h q G X Y := by
  exact ⟨d.surplus, d.smaller_order, d.deficit, d.minimum_X host, d.minimum_Y host,
    d.exact_minimum host, d.deleted_count host, d.retained_deficit host,
    d.retained_minimum host, Diagonal.retained_cap host, d.retained_order host,
    d.retained_eligible host, d.retained_floor host, d.actual_qcore host⟩

end Diagonal
end Erdos585.AllHTopCritical

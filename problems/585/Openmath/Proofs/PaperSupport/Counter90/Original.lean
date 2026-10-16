import Openmath.Proofs.PaperSupport.Counter90.Matrix
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
open Finset SimpleGraph
namespace Erdos585.Counter90

/-- Actual arbitrary-support subgraphs, with every original selected-edge fiber paid. -/
theorem core_no_regular_subgraph :
    ¬ ∃ H : (coreGraph).Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 6 := by
  classical
  rintro ⟨H, hne, hregular⟩
  let F := univ.filter fun x : Fin 10 × Fin 12 => H.Adj (Sum.inl x.1) (Sum.inr x.2)
  have hleft (i : Fin 10) : matrixRowDegree F i = H.degree (Sum.inl i) := by
    dsimp [F]
    rw [row_card_matrix (fun i j => H.Adj (Sum.inl i) (Sum.inr j)) i]
    exact (degree_left_matrix H.spanningCoe H.spanningCoe_le i).symm.trans
      (SimpleGraph.Subgraph.degree_spanningCoe _)
  have hright (j : Fin 12) : matrixColumnDegree F j = H.degree (Sum.inr j) := by
    dsimp [F]
    rw [column_card_matrix (fun i j => H.Adj (Sum.inl i) (Sum.inr j)) j]
    exact (degree_right_matrix H.spanningCoe H.spanningCoe_le j).symm.trans
      (SimpleGraph.Subgraph.degree_spanningCoe _)
  have hdegrees (v : Fin 10 ⊕ Fin 12) : H.degree v = 0 ∨ H.degree v = 6 := by
    by_cases hv : v ∈ H.verts
    · right
      exact (SimpleGraph.Subgraph.coe_degree H ⟨v, hv⟩).symm.trans (hregular.degree_eq _)
    · left
      exact SimpleGraph.Subgraph.degree_of_notMem_verts hv
  have hFne : F.Nonempty := by
    obtain ⟨v, hv⟩ := hne
    have hd : H.degree v = 6 :=
      (SimpleGraph.Subgraph.coe_degree H ⟨v, hv⟩).symm.trans (hregular.degree_eq _)
    obtain ⟨w, hvw⟩ := (SimpleGraph.Subgraph.degree_pos_iff_exists_adj).mp (by omega : 0 < H.degree v)
    have hg := H.adj_sub hvw
    cases v with
    | inl i =>
      cases w with
      | inl i' => exact hg.elim
      | inr j => exact ⟨(i, j), mem_filter.mpr ⟨mem_univ _, hvw⟩⟩
    | inr j =>
      cases w with
      | inl i => exact ⟨(i, j), mem_filter.mpr ⟨mem_univ _, hvw.symm⟩⟩
      | inr j' => exact hg.elim
  apply seed_no_regular_matrix F hFne
  · intro x hx
    exact H.adj_sub (mem_filter.mp hx).2
  · intro i
    rw [hleft]
    exact hdegrees _
  · intro j
    rw [hright]
    exact hdegrees _



/-- Pull back the SAME selected original subgraph along the explicit vertex bijection. -/
theorem seed_no_regular_subgraph :
    ¬ ∃ H : graph.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 6 := by
  classical
  rintro ⟨H,hne,hreg⟩
  let H0 : coreGraph.Subgraph := {
    verts := {v | labelEquiv v ∈ H.verts}
    Adj := fun v w => H.Adj (labelEquiv v) (labelEquiv w)
    adj_sub := by
      intro v w h
      have hg := H.adj_sub h
      change coreGraph.Adj (labelEquiv.symm (labelEquiv v))
        (labelEquiv.symm (labelEquiv w)) at hg
      simpa only [Equiv.symm_apply_apply] using hg
    edge_vert := fun h => H.edge_vert h
    symm := ⟨by intro v w h; exact h.symm⟩ }
  let : ∀ v : CoreVertex, Fintype (H0.neighborSet v) := fun _ => Fintype.ofFinite _
  have h0ne : H0.verts.Nonempty := by
    obtain ⟨x,hx⟩ := hne
    refine ⟨labelEquiv.symm x,?_⟩
    change labelEquiv (labelEquiv.symm x) ∈ H.verts
    simpa only [Equiv.apply_symm_apply] using hx
  have hdegree (v : CoreVertex) : H0.degree v = H.degree (labelEquiv v) := by
    let f : H0.neighborSet v → H.neighborSet (labelEquiv v) :=
      fun w => ⟨labelEquiv w.val,w.property⟩
    have hinj : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact labelEquiv.injective (congrArg Subtype.val hxy)
    have hsurj : Function.Surjective f := by
      intro w
      refine ⟨⟨labelEquiv.symm w.val,?_⟩,?_⟩
      · change H.Adj (labelEquiv v) (labelEquiv (labelEquiv.symm w.val))
        have hw : H.Adj (labelEquiv v) w.val := w.property
        simpa only [Equiv.apply_symm_apply] using hw
      · apply Subtype.ext
        exact labelEquiv.apply_symm_apply w.val
    exact Fintype.card_congr (Equiv.ofBijective f ⟨hinj,hsurj⟩)
  apply core_no_regular_subgraph
  refine ⟨H0,h0ne,?_⟩
  intro v
  rw [Subgraph.coe_degree,hdegree]
  exact (Subgraph.coe_degree H ⟨labelEquiv v.val,v.property⟩).symm.trans (hreg.degree_eq _)

end Erdos585.Counter90

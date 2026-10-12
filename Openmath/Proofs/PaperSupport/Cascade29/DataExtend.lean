import Openmath.Proofs.PaperSupport.Cascade29.Invariants

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
open Finset SimpleGraph
namespace Erdos585.Cascade29

theorem data_add_good (D : GraphData) (h : DataGood D) (b : Bool)
    (N : Finset D.Carrier) (hN : N.card = 6)
    (hsub : N ⊆ if b then D.right else D.left)
    (hload : ∀ v ∈ N, D.graph.degree v < 12) : DataGood (D.add b N) := by
  cases b with
  | true => exact extend_good D.graph h N hsub hN hload
  | false => exact (extend_good D.graph h.swap N hsub hN hload).swap

theorem data_add_unique (D : GraphData) (N : Finset D.Carrier) (hN : N.card = 6)
    (z : D.Carrier) (hz : D.graph.degree z = 6) (hzN : z ∈ N)
    (hothers : ∀ v, v ≠ z → 7 ≤ D.graph.degree v) :
    ∀ v : Option D.Carrier, v ≠ none →
      7 ≤ (BqCircularLowerFamily.extendGraph D.graph N).degree v := by
  intro v hv
  cases v with
  | none => exact (hv rfl).elim
  | some v =>
    rw [BqCircularLowerFamily.degree_some]
    by_cases hvz : v = z
    · subst v
      simp [hzN, hz]
    · have hd := hothers v hvz
      split_ifs <;> omega

theorem normal_add_left (D : GraphData) (h : DataGood D)
    (N : Finset D.Carrier) (hN : N.card = 6)
    (hsub : N ⊆ D.right) (hload : ∀ v ∈ N, D.graph.degree v < 12)
    (z : D.Carrier) (hz : D.graph.degree z = 6) (hzN : z ∈ N)
    (hothers : ∀ v, v ≠ z → 7 ≤ D.graph.degree v)
    (hshape : D.right.card = D.left.card + 1) : Normal (D.add true N) := by
  refine ⟨data_add_good D h true N hN hsub hload, ?_⟩
  refine ⟨none, ?_, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
  · exact (BqCircularLowerFamily.degree_none D.graph N).trans hN
  · exact data_add_unique D N hN z hz hzN hothers
  · change Fintype.card D.Carrier + 1 = Fintype.card (Option D.Carrier)
    rw [Fintype.card_option]
  · change (insert none (D.left.image some)).card = (D.right.image some).card
    rw [card_insert_of_notMem (by simp),
      card_image_of_injective _ (Option.some_injective D.Carrier),
      card_image_of_injective _ (Option.some_injective D.Carrier)]
    omega
  · change none ∈ insert none (D.left.image some)
    exact mem_insert_self _ _

theorem normal_add_right (D : GraphData) (h : DataGood D)
    (N : Finset D.Carrier) (hN : N.card = 6)
    (hsub : N ⊆ D.left) (hload : ∀ v ∈ N, D.graph.degree v < 12)
    (z : D.Carrier) (hz : D.graph.degree z = 6) (hzN : z ∈ N)
    (hothers : ∀ v, v ≠ z → 7 ≤ D.graph.degree v)
    (hshape : D.left.card = D.right.card) : Normal (D.add false N) := by
  refine ⟨data_add_good D h false N hN hsub hload, ?_⟩
  refine ⟨none, ?_, ?_, ?_, Or.inr ⟨?_, ?_⟩⟩
  · exact (BqCircularLowerFamily.degree_none D.graph N).trans hN
  · exact data_add_unique D N hN z hz hzN hothers
  · change Fintype.card D.Carrier + 1 = Fintype.card (Option D.Carrier)
    rw [Fintype.card_option]
  · change (insert none (D.right.image some)).card = (D.left.image some).card + 1
    rw [card_insert_of_notMem (by simp),
      card_image_of_injective _ (Option.some_injective D.Carrier),
      card_image_of_injective _ (Option.some_injective D.Carrier)]
    omega
  · change none ∈ insert none (D.right.image some)
    exact mem_insert_self _ _

end Erdos585.Cascade29

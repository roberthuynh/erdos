import Openmath.Proofs.PaperSupport.Cascade29.Types
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
open Finset SimpleGraph
namespace Erdos585.Cascade29

def matrixRowDegree (F : Finset (Fin 12 × Fin 13)) (i : Fin 12) : ℕ :=
  (F.filter fun x => x.1 = i).card
def matrixColumnDegree (F : Finset (Fin 12 × Fin 13)) (j : Fin 13) : ℕ :=
  (F.filter fun x => x.2 = j).card

theorem row_card_matrix (r : Fin 12 → Fin 13 → Prop) [∀ i j, Decidable (r i j)]
    (i : Fin 12) :
    matrixRowDegree (univ.filter fun x : Fin 12 × Fin 13 => r x.1 x.2) i =
      (univ.filter fun j => r i j).card := by
  unfold matrixRowDegree
  rw [filter_filter]
  have heq : (univ.filter fun x : Fin 12 × Fin 13 => r x.1 x.2 ∧ x.1 = i) =
      ({i} ×ˢ (univ.filter fun j => r i j)) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton]
    constructor
    · rintro ⟨hr, hi⟩
      exact ⟨hi, hi ▸ hr⟩
    · rintro ⟨hi, hr⟩
      exact ⟨hi ▸ hr, hi⟩
  rw [heq, card_product, card_singleton, one_mul]

theorem column_card_matrix (r : Fin 12 → Fin 13 → Prop) [∀ i j, Decidable (r i j)]
    (j : Fin 13) :
    matrixColumnDegree (univ.filter fun x : Fin 12 × Fin 13 => r x.1 x.2) j =
      (univ.filter fun i => r i j).card := by
  unfold matrixColumnDegree
  rw [filter_filter]
  have heq : (univ.filter fun x : Fin 12 × Fin 13 => r x.1 x.2 ∧ x.2 = j) =
      ((univ.filter fun i => r i j) ×ˢ {j}) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton]
    constructor
    · rintro ⟨hr, hj⟩
      exact ⟨hj ▸ hr, hj⟩
    · rintro ⟨hr, hj⟩
      exact ⟨hj ▸ hr, hj⟩
  rw [heq, card_product, card_singleton, mul_one]

theorem degree_left_matrix (K : SimpleGraph (Fin 12 ⊕ Fin 13)) [DecidableRel K.Adj]
    (hK : K ≤ seedGraph) (i : Fin 12) :
    K.degree (Sum.inl i) = (univ.filter fun j => K.Adj (Sum.inl i) (Sum.inr j)).card := by
  have hn : K.neighborFinset (Sum.inl i) =
      (univ.filter fun j => K.Adj (Sum.inl i) (Sum.inr j)).image Sum.inr := by
    ext v
    cases v with
    | inl i' =>
      have hnot : ¬ K.Adj (Sum.inl i) (Sum.inl i') := by
        intro h
        exact hK h
      simp [hnot]
    | inr j => simp
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hn,
    card_image_of_injective _ Sum.inr_injective]

theorem degree_right_matrix (K : SimpleGraph (Fin 12 ⊕ Fin 13)) [DecidableRel K.Adj]
    (hK : K ≤ seedGraph) (j : Fin 13) :
    K.degree (Sum.inr j) = (univ.filter fun i => K.Adj (Sum.inl i) (Sum.inr j)).card := by
  have hn : K.neighborFinset (Sum.inr j) =
      (univ.filter fun i => K.Adj (Sum.inl i) (Sum.inr j)).image Sum.inl := by
    ext v
    cases v with
    | inl i => simp [K.adj_comm]
    | inr j' =>
      have hnot : ¬ K.Adj (Sum.inr j) (Sum.inr j') := by
        intro h
        exact hK h
      simp [hnot]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hn,
    card_image_of_injective _ Sum.inl_injective]


end Erdos585.Cascade29

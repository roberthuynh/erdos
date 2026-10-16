import Openmath.Proofs.PaperSupport.Counter90.SupportExclusion
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
open Finset SimpleGraph
namespace Erdos585.Counter90

def matrixRowDegree (F : Finset (Fin 10 × Fin 12)) (i : Fin 10) : ℕ :=
  (F.filter fun x => x.1 = i).card

def matrixColumnDegree (F : Finset (Fin 10 × Fin 12)) (j : Fin 12) : ℕ :=
  (F.filter fun x => x.2 = j).card

/-- Every nonempty original selected cross-edge set fails degree-six regularity. -/
theorem seed_no_regular_matrix (F : Finset (Fin 10 × Fin 12))
    (hne : F.Nonempty) (hsub : ∀ x ∈ F, rel x.1 x.2)
    (hrow : ∀ i, matrixRowDegree F i = 0 ∨ matrixRowDegree F i = 6)
    (hcol : ∀ j, matrixColumnDegree F j = 0 ∨ matrixColumnDegree F j = 6) : False := by
  let P := univ.filter fun i => 0 < matrixRowDegree F i
  let Q := univ.filter fun j => 0 < matrixColumnDegree F j
  have hP (i : Fin 10) : i ∈ P ↔ 0 < matrixRowDegree F i := by simp [P]
  have hQ (j : Fin 12) : j ∈ Q ↔ 0 < matrixColumnDegree F j := by simp [Q]
  have hP4 (i : Fin 10) (hi : i ∈ P) : matrixRowDegree F i = 6 :=
    (hrow i).resolve_left (Nat.ne_of_gt ((hP i).mp hi))
  have hQ4 (j : Fin 12) (hj : j ∈ Q) : matrixColumnDegree F j = 6 :=
    (hcol j).resolve_left (Nat.ne_of_gt ((hQ j).mp hj))
  have hFrow : F.card = ∑ i : Fin 10, matrixRowDegree F i :=
    card_eq_sum_card_fiberwise (f := Prod.fst) (s := F) (t := univ) (by simp)
  have hFcol : F.card = ∑ j : Fin 12, matrixColumnDegree F j :=
    card_eq_sum_card_fiberwise (f := Prod.snd) (s := F) (t := univ) (by simp)
  have hsumP : (∑ i : Fin 10, matrixRowDegree F i) = 6 * P.card := by
    calc
      _ = ∑ i : Fin 10, if i ∈ P then 6 else 0 := by
        apply sum_congr rfl
        intro i _
        by_cases hi : i ∈ P
        · simp [hi, hP4 i hi]
        · have hz : matrixRowDegree F i = 0 := by
            have hn := mt (hP i).mpr hi
            omega
          simp [hi, hz]
      _ = 6 * P.card := by simp [mul_comm]
  have hsumQ : (∑ j : Fin 12, matrixColumnDegree F j) = 6 * Q.card := by
    calc
      _ = ∑ j : Fin 12, if j ∈ Q then 6 else 0 := by
        apply sum_congr rfl
        intro j _
        by_cases hj : j ∈ Q
        · simp [hj, hQ4 j hj]
        · have hz : matrixColumnDegree F j = 0 := by
            have hn := mt (hQ j).mpr hj
            omega
          simp [hj, hz]
      _ = 6 * Q.card := by simp [mul_comm]
  have hbalance : P.card = Q.card := by nlinarith
  have hPne : P.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨x.1, (hP x.1).mpr ?_⟩
    exact card_pos.mpr ⟨x, mem_filter.mpr ⟨hx, rfl⟩⟩
  have hrowlower (i : Fin 10) (hi : i ∈ P) : 6 ≤ rowDegree Q i := by
    let T := F.filter fun x => x.1 = i
    have hcard : (T.image Prod.snd).card = T.card := by
      apply card_image_of_injOn
      intro x hx y hy hxy
      have hxi := (mem_filter.mp hx).2
      have hyi := (mem_filter.mp hy).2
      exact Prod.ext (hxi.trans hyi.symm) hxy
    have hsubset : T.image Prod.snd ⊆ Q ∩ rowNeighbors i := by
      intro j hj
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hj
      obtain ⟨hxF, hxi⟩ := mem_filter.mp hx
      refine mem_inter.mpr ⟨(hQ x.2).mpr ?_, ?_⟩
      · exact card_pos.mpr ⟨x, mem_filter.mpr ⟨hxF, rfl⟩⟩
      · exact (mem_rowNeighbors _ _).mpr (hxi ▸ hsub x hxF)
    have hle := card_le_card hsubset
    rw [hcard] at hle
    change matrixRowDegree F i ≤ rowDegree Q i at hle
    rwa [hP4 i hi] at hle
  have hcollower (j : Fin 12) (hj : j ∈ Q) : 6 ≤ columnDegree P j := by
    let T := F.filter fun x => x.2 = j
    have hcard : (T.image Prod.fst).card = T.card := by
      apply card_image_of_injOn
      intro x hx y hy hxy
      have hxj := (mem_filter.mp hx).2
      have hyj := (mem_filter.mp hy).2
      exact Prod.ext hxy (hxj.trans hyj.symm)
    have hsubset : T.image Prod.fst ⊆ P ∩ columnNeighbors j := by
      intro i hi
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hi
      obtain ⟨hxF, hxj⟩ := mem_filter.mp hx
      refine mem_inter.mpr ⟨(hP x.1).mpr ?_, ?_⟩
      · exact card_pos.mpr ⟨x, mem_filter.mpr ⟨hxF, rfl⟩⟩
      · exact (mem_columnNeighbors _ _).mpr (hxj ▸ hsub x hxF)
    have hle := card_le_card hsubset
    rw [hcard] at hle
    change matrixColumnDegree F j ≤ columnDegree P j at hle
    rwa [hQ4 j hj] at hle
  exact no_balanced_support P Q hPne hbalance hrowlower hcollower


theorem row_card_matrix (r : Fin 10 → Fin 12 → Prop) [∀ i j, Decidable (r i j)]
    (i : Fin 10) :
    matrixRowDegree (univ.filter fun x : Fin 10 × Fin 12 => r x.1 x.2) i =
      (univ.filter fun j => r i j).card := by
  unfold matrixRowDegree
  rw [filter_filter]
  have heq : (univ.filter fun x : Fin 10 × Fin 12 => r x.1 x.2 ∧ x.1 = i) =
      ({i} ×ˢ (univ.filter fun j => r i j)) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton]
    constructor
    · rintro ⟨hr, hi⟩
      exact ⟨hi, hi ▸ hr⟩
    · rintro ⟨hi, hr⟩
      exact ⟨hi ▸ hr, hi⟩
  rw [heq, card_product, card_singleton, one_mul]

theorem column_card_matrix (r : Fin 10 → Fin 12 → Prop) [∀ i j, Decidable (r i j)]
    (j : Fin 12) :
    matrixColumnDegree (univ.filter fun x : Fin 10 × Fin 12 => r x.1 x.2) j =
      (univ.filter fun i => r i j).card := by
  unfold matrixColumnDegree
  rw [filter_filter]
  have heq : (univ.filter fun x : Fin 10 × Fin 12 => r x.1 x.2 ∧ x.2 = j) =
      ((univ.filter fun i => r i j) ×ˢ {j}) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton]
    constructor
    · rintro ⟨hr, hj⟩
      exact ⟨hj ▸ hr, hj⟩
    · rintro ⟨hr, hj⟩
      exact ⟨hj ▸ hr, hj⟩
  rw [heq, card_product, card_singleton, mul_one]

theorem degree_left_matrix (K : SimpleGraph (Fin 10 ⊕ Fin 12)) [DecidableRel K.Adj]
    (hK : K ≤ coreGraph) (i : Fin 10) :
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

theorem degree_right_matrix (K : SimpleGraph (Fin 10 ⊕ Fin 12)) [DecidableRel K.Adj]
    (hK : K ≤ coreGraph) (j : Fin 12) :
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

end Erdos585.Counter90

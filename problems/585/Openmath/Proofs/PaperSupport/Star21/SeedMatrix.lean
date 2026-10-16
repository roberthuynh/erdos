import Openmath.Proofs.PaperSupport.Star21.SeedSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
open Finset SimpleGraph
namespace Erdos585.Star21

/- Actual matrix/Subgraph transport follows the credited direct source, with the
literal 9-by-12 graph and our newly proved disjoint-hole exclusion as supplier. -/
def matrixRowDegree (F : Finset (Fin 9 × Fin 12)) (i : Fin 9) : ℕ :=
  (F.filter fun x => x.1 = i).card

def matrixColumnDegree (F : Finset (Fin 9 × Fin 12)) (j : Fin 12) : ℕ :=
  (F.filter fun x => x.2 = j).card

/-- Actual selected edges cannot have all nonzero row and column degrees equal to 7. -/
theorem seed_no_regular_matrix (F : Finset (Fin 9 × Fin 12))
    (hne : F.Nonempty) (hsub : ∀ x ∈ F, seedRel x.1 x.2)
    (hrow : ∀ i, matrixRowDegree F i = 0 ∨ matrixRowDegree F i = 7)
    (hcol : ∀ j, matrixColumnDegree F j = 0 ∨ matrixColumnDegree F j = 7) : False := by
  let P := univ.filter fun i => 0 < matrixRowDegree F i
  let Q := univ.filter fun j => 0 < matrixColumnDegree F j
  have hP (i : Fin 9) : i ∈ P ↔ 0 < matrixRowDegree F i := by simp [P]
  have hQ (j : Fin 12) : j ∈ Q ↔ 0 < matrixColumnDegree F j := by simp [Q]
  have hP4 (i : Fin 9) (hi : i ∈ P) : matrixRowDegree F i = 7 :=
    (hrow i).resolve_left (Nat.ne_of_gt ((hP i).mp hi))
  have hQ4 (j : Fin 12) (hj : j ∈ Q) : matrixColumnDegree F j = 7 :=
    (hcol j).resolve_left (Nat.ne_of_gt ((hQ j).mp hj))
  have hFrow : F.card = ∑ i : Fin 9, matrixRowDegree F i :=
    card_eq_sum_card_fiberwise (f := Prod.fst) (s := F) (t := univ) (by simp)
  have hFcol : F.card = ∑ j : Fin 12, matrixColumnDegree F j :=
    card_eq_sum_card_fiberwise (f := Prod.snd) (s := F) (t := univ) (by simp)
  have hsumP : (∑ i : Fin 9, matrixRowDegree F i) = 7 * P.card := by
    calc
      _ = ∑ i : Fin 9, if i ∈ P then 7 else 0 := by
        apply sum_congr rfl
        intro i _
        by_cases hi : i ∈ P
        · simp [hi, hP4 i hi]
        · have hz : matrixRowDegree F i = 0 := by
            have hn := mt (hP i).mpr hi
            omega
          simp [hi, hz]
      _ = 7 * P.card := by simp [mul_comm]
  have hsumQ : (∑ j : Fin 12, matrixColumnDegree F j) = 7 * Q.card := by
    calc
      _ = ∑ j : Fin 12, if j ∈ Q then 7 else 0 := by
        apply sum_congr rfl
        intro j _
        by_cases hj : j ∈ Q
        · simp [hj, hQ4 j hj]
        · have hz : matrixColumnDegree F j = 0 := by
            have hn := mt (hQ j).mpr hj
            omega
          simp [hj, hz]
      _ = 7 * Q.card := by simp [mul_comm]
  have hbalance : P.card = Q.card := by nlinarith
  have hPne : P.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨x.1, (hP x.1).mpr ?_⟩
    exact card_pos.mpr ⟨x, mem_filter.mpr ⟨hx, rfl⟩⟩
  have hrowlower (i : Fin 9) (hi : i ∈ P) : 7 ≤ seedRowDegree Q i := by
    let T := F.filter fun x => x.1 = i
    have hcard : (T.image Prod.snd).card = T.card := by
      apply card_image_of_injOn
      intro x hx y hy hxy
      have hxi := (mem_filter.mp hx).2
      have hyi := (mem_filter.mp hy).2
      exact Prod.ext (hxi.trans hyi.symm) hxy
    have hsubset : T.image Prod.snd ⊆ Q.filter fun j => seedRel i j := by
      intro j hj
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hj
      obtain ⟨hxF, hxi⟩ := mem_filter.mp hx
      refine mem_filter.mpr ⟨(hQ x.2).mpr ?_, ?_⟩
      · exact card_pos.mpr ⟨x, mem_filter.mpr ⟨hxF, rfl⟩⟩
      · exact hxi ▸ hsub x hxF
    have hle := card_le_card hsubset
    rw [hcard] at hle
    change matrixRowDegree F i ≤ seedRowDegree Q i at hle
    rwa [hP4 i hi] at hle
  exact seed_no_balanced_support P Q hPne hbalance hrowlower

theorem row_card_matrix (r : Fin 9 → Fin 12 → Prop) [∀ i j, Decidable (r i j)]
    (i : Fin 9) :
    matrixRowDegree (univ.filter fun x : Fin 9 × Fin 12 => r x.1 x.2) i =
      (univ.filter fun j => r i j).card := by
  unfold matrixRowDegree
  rw [filter_filter]
  have heq : (univ.filter fun x : Fin 9 × Fin 12 => r x.1 x.2 ∧ x.1 = i) =
      ({i} ×ˢ (univ.filter fun j => r i j)) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton]
    constructor
    · rintro ⟨hr, hi⟩
      exact ⟨hi, hi ▸ hr⟩
    · rintro ⟨hi, hr⟩
      exact ⟨hi ▸ hr, hi⟩
  rw [heq, card_product, card_singleton, one_mul]

theorem column_card_matrix (r : Fin 9 → Fin 12 → Prop) [∀ i j, Decidable (r i j)]
    (j : Fin 12) :
    matrixColumnDegree (univ.filter fun x : Fin 9 × Fin 12 => r x.1 x.2) j =
      (univ.filter fun i => r i j).card := by
  unfold matrixColumnDegree
  rw [filter_filter]
  have heq : (univ.filter fun x : Fin 9 × Fin 12 => r x.1 x.2 ∧ x.2 = j) =
      ((univ.filter fun i => r i j) ×ˢ {j}) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton]
    constructor
    · rintro ⟨hr, hj⟩
      exact ⟨hj ▸ hr, hj⟩
    · rintro ⟨hr, hj⟩
      exact ⟨hj ▸ hr, hj⟩
  rw [heq, card_product, card_singleton, mul_one]

theorem degree_left_matrix (K : SimpleGraph (Fin 9 ⊕ Fin 12)) [DecidableRel K.Adj]
    (hK : K ≤ seedGraph) (i : Fin 9) :
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

theorem degree_right_matrix (K : SimpleGraph (Fin 9 ⊕ Fin 12)) [DecidableRel K.Adj]
    (hK : K ≤ seedGraph) (j : Fin 12) :
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

/-- Literal arbitrary 7-regular Subgraph absence for the actual all-7 seed. -/
theorem seed_no_regular_subgraph :
    ¬ ∃ H : (seedGraph).Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 7 := by
  classical
  rintro ⟨H, hne, hregular⟩
  let F := univ.filter fun x : Fin 9 × Fin 12 => H.Adj (Sum.inl x.1) (Sum.inr x.2)
  have hleft (i : Fin 9) : matrixRowDegree F i = H.degree (Sum.inl i) := by
    dsimp [F]
    rw [row_card_matrix (fun i j => H.Adj (Sum.inl i) (Sum.inr j)) i]
    exact (degree_left_matrix H.spanningCoe H.spanningCoe_le i).symm.trans
      (SimpleGraph.Subgraph.degree_spanningCoe _)
  have hright (j : Fin 12) : matrixColumnDegree F j = H.degree (Sum.inr j) := by
    dsimp [F]
    rw [column_card_matrix (fun i j => H.Adj (Sum.inl i) (Sum.inr j)) j]
    exact (degree_right_matrix H.spanningCoe H.spanningCoe_le j).symm.trans
      (SimpleGraph.Subgraph.degree_spanningCoe _)
  have hdegrees (v : Fin 9 ⊕ Fin 12) : H.degree v = 0 ∨ H.degree v = 7 := by
    by_cases hv : v ∈ H.verts
    · right
      exact (SimpleGraph.Subgraph.coe_degree H ⟨v, hv⟩).symm.trans (hregular.degree_eq _)
    · left
      exact SimpleGraph.Subgraph.degree_of_notMem_verts hv
  have hFne : F.Nonempty := by
    obtain ⟨v, hv⟩ := hne
    have hd : H.degree v = 7 :=
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


#print axioms seed_no_regular_matrix
#print axioms seed_no_regular_subgraph

end Erdos585.Star21

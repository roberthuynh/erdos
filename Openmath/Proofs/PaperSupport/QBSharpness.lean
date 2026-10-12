import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Tactic

/- 



-/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open Finset

namespace Erdos585.QBSharpness

/-- The literal five deleted edges of the independently suggested eleven-vertex seed. -/
def seedAdj (i : Fin 5) (j : Fin 6) : Prop :=
  ¬ ((i = 0 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨
     (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 4))

instance seedAdjDecidable : DecidableRel seedAdj := fun _ _ => by
  unfold seedAdj
  infer_instance

def seedRowDegree (Q : Finset (Fin 6)) (i : Fin 5) : ℕ :=
  (Q.filter fun j => seedAdj i j).card

def seedColumnDegree (P : Finset (Fin 5)) (j : Fin 6) : ℕ :=
  (P.filter fun i => seedAdj i j).card

theorem seed_edges : ∑ i : Fin 5, seedRowDegree univ i = 25 := by decide

theorem seed_degree_bounds :
    (∀ i : Fin 5, 4 ≤ seedRowDegree univ i ∧ seedRowDegree univ i ≤ 6) ∧
    (∀ j : Fin 6, 4 ≤ seedColumnDegree univ j ∧ seedColumnDegree univ j ≤ 6) := by decide

/-- Stronger than quartic absence: no nonempty balanced induced support has minimum degree4. -/
theorem seed_no_balanced_support : ∀ (P : Finset (Fin 5)) (Q : Finset (Fin 6)),
    P.Nonempty → P.card = Q.card →
    (∀ i ∈ P, 4 ≤ seedRowDegree Q i) →
    (∀ j ∈ Q, 4 ≤ seedColumnDegree P j) → False := by decide

def matrixRowDegree (F : Finset (Fin 5 × Fin 6)) (i : Fin 5) : ℕ :=
  (F.filter fun x => x.1 = i).card

def matrixColumnDegree (F : Finset (Fin 5 × Fin 6)) (j : Fin 6) : ℕ :=
  (F.filter fun x => x.2 = j).card

/-- Actual selected edges cannot have all nonzero row and column degrees equal to4. -/
theorem seed_no_quartic_matrix (F : Finset (Fin 5 × Fin 6))
    (hne : F.Nonempty) (hsub : ∀ x ∈ F, seedAdj x.1 x.2)
    (hrow : ∀ i, matrixRowDegree F i = 0 ∨ matrixRowDegree F i = 4)
    (hcol : ∀ j, matrixColumnDegree F j = 0 ∨ matrixColumnDegree F j = 4) : False := by
  let P := univ.filter fun i => 0 < matrixRowDegree F i
  let Q := univ.filter fun j => 0 < matrixColumnDegree F j
  have hP (i : Fin 5) : i ∈ P ↔ 0 < matrixRowDegree F i := by simp [P]
  have hQ (j : Fin 6) : j ∈ Q ↔ 0 < matrixColumnDegree F j := by simp [Q]
  have hP4 (i : Fin 5) (hi : i ∈ P) : matrixRowDegree F i = 4 :=
    (hrow i).resolve_left (Nat.ne_of_gt ((hP i).mp hi))
  have hQ4 (j : Fin 6) (hj : j ∈ Q) : matrixColumnDegree F j = 4 :=
    (hcol j).resolve_left (Nat.ne_of_gt ((hQ j).mp hj))
  have hFrow : F.card = ∑ i : Fin 5, matrixRowDegree F i :=
    card_eq_sum_card_fiberwise (f := Prod.fst) (s := F) (t := univ) (by simp)
  have hFcol : F.card = ∑ j : Fin 6, matrixColumnDegree F j :=
    card_eq_sum_card_fiberwise (f := Prod.snd) (s := F) (t := univ) (by simp)
  have hsumP : (∑ i : Fin 5, matrixRowDegree F i) = 4 * P.card := by
    calc
      _ = ∑ i : Fin 5, if i ∈ P then 4 else 0 := by
        apply sum_congr rfl
        intro i _
        by_cases hi : i ∈ P
        · simp [hi, hP4 i hi]
        · have hz : matrixRowDegree F i = 0 := by
            have hn := mt (hP i).mpr hi
            omega
          simp [hi, hz]
      _ = 4 * P.card := by simp [mul_comm]
  have hsumQ : (∑ j : Fin 6, matrixColumnDegree F j) = 4 * Q.card := by
    calc
      _ = ∑ j : Fin 6, if j ∈ Q then 4 else 0 := by
        apply sum_congr rfl
        intro j _
        by_cases hj : j ∈ Q
        · simp [hj, hQ4 j hj]
        · have hz : matrixColumnDegree F j = 0 := by
            have hn := mt (hQ j).mpr hj
            omega
          simp [hj, hz]
      _ = 4 * Q.card := by simp [mul_comm]
  have hbalance : P.card = Q.card := by omega
  have hPne : P.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨x.1, (hP x.1).mpr ?_⟩
    exact card_pos.mpr ⟨x, mem_filter.mpr ⟨hx, rfl⟩⟩
  have hrowlower (i : Fin 5) (hi : i ∈ P) : 4 ≤ seedRowDegree Q i := by
    let T := F.filter fun x => x.1 = i
    have hcard : (T.image Prod.snd).card = T.card := by
      apply card_image_of_injOn
      intro x hx y hy hxy
      have hxi := (mem_filter.mp hx).2
      have hyi := (mem_filter.mp hy).2
      exact Prod.ext (hxi.trans hyi.symm) hxy
    have hsubset : T.image Prod.snd ⊆ Q.filter fun j => seedAdj i j := by
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
  have hcollower (j : Fin 6) (hj : j ∈ Q) : 4 ≤ seedColumnDegree P j := by
    let T := F.filter fun x => x.2 = j
    have hcard : (T.image Prod.fst).card = T.card := by
      apply card_image_of_injOn
      intro x hx y hy hxy
      have hxj := (mem_filter.mp hx).2
      have hyj := (mem_filter.mp hy).2
      exact Prod.ext hxy (hxj.trans hyj.symm)
    have hsubset : T.image Prod.fst ⊆ P.filter fun i => seedAdj i j := by
      intro i hi
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hi
      obtain ⟨hxF, hxj⟩ := mem_filter.mp hx
      refine mem_filter.mpr ⟨(hP x.1).mpr ?_, ?_⟩
      · exact card_pos.mpr ⟨x, mem_filter.mpr ⟨hxF, rfl⟩⟩
      · exact hxj ▸ hsub x hxF
    have hle := card_le_card hsubset
    rw [hcard] at hle
    change matrixColumnDegree F j ≤ seedColumnDegree P j at hle
    rwa [hQ4 j hj] at hle
  exact seed_no_balanced_support P Q hPne hbalance hrowlower hcollower

/-- Actual natural degree capacity8 forces three distinct eligible attachment vertices. -/
theorem capacity_ge_eight {V : Type*} [DecidableEq V] (S : Finset V) (g : V → ℕ)
    (hdegree : ∀ v ∈ S, 3 ≤ g v ∧ g v ≤ 6)
    (hcapacity : 8 ≤ ∑ v ∈ S, (6 - g v)) :
    3 ≤ (S.filter fun v => g v ≤ 5).card := by
  have hle : (∑ v ∈ S, (6 - g v)) ≤ ∑ v ∈ S, if g v ≤ 5 then 3 else 0 := by
    apply sum_le_sum
    intro v hv
    have hd := hdegree v hv
    split_ifs <;> omega
  have hright : (∑ v ∈ S, if g v ≤ 5 then 3 else 0) =
      3 * (S.filter fun v => g v ≤ 5).card := by
    rw [← sum_filter]
    simp [mul_comm]
  rw [hright] at hle
  omega

/-- The larger or equal opposite shore has exactly capacity8 or11. -/
theorem opposite_capacity (a b e : ℕ) (hab : a ≤ b) (hba : b ≤ a + 1)
    (hedges : e + 8 = 3 * (a + b)) :
    (6 * b - e = 8 ∨ 6 * b - e = 11) ∧ 8 ≤ 6 * b - e := by omega

/- -/
def seedGraph : SimpleGraph (Fin 5 ⊕ Fin 6) where
  Adj v w := match v, w with
    | Sum.inl i, Sum.inr j => seedAdj i j
    | Sum.inr j, Sum.inl i => seedAdj i j
    | _, _ => False
  symm := ⟨by intro v w; cases v <;> cases w <;> simp⟩
  loopless := ⟨by intro v; cases v <;> simp⟩

instance seedGraphDecidable : DecidableRel seedGraph.Adj := fun v w => by
  cases v <;> cases w <;> unfold seedGraph <;> infer_instance

theorem seed_graph_edges : seedGraph.edgeFinset.card = 25 := by decide

theorem seed_graph_max_degree : seedGraph.maxDegree ≤ 6 := by decide

theorem seed_graph_bipartite : seedGraph.IsBipartite := by
  apply SimpleGraph.IsBipartiteWith.isBipartite (s := Set.range Sum.inl) (t := Set.range Sum.inr)
  refine ⟨?_, ?_⟩
  · simp [Set.disjoint_left]
  · intro v w hvw
    cases v <;> cases w <;> simp_all [seedGraph]

private theorem row_card_matrix (r : Fin 5 → Fin 6 → Prop) [∀ i j, Decidable (r i j)]
    (i : Fin 5) :
    matrixRowDegree (univ.filter fun x : Fin 5 × Fin 6 => r x.1 x.2) i =
      (univ.filter fun j => r i j).card := by
  unfold matrixRowDegree
  rw [filter_filter]
  have heq : (univ.filter fun x : Fin 5 × Fin 6 => r x.1 x.2 ∧ x.1 = i) =
      ({i} ×ˢ (univ.filter fun j => r i j)) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton]
    constructor
    · rintro ⟨hr, hi⟩
      exact ⟨hi, hi ▸ hr⟩
    · rintro ⟨hi, hr⟩
      exact ⟨hi ▸ hr, hi⟩
  rw [heq, card_product, card_singleton, one_mul]

private theorem column_card_matrix (r : Fin 5 → Fin 6 → Prop) [∀ i j, Decidable (r i j)]
    (j : Fin 6) :
    matrixColumnDegree (univ.filter fun x : Fin 5 × Fin 6 => r x.1 x.2) j =
      (univ.filter fun i => r i j).card := by
  unfold matrixColumnDegree
  rw [filter_filter]
  have heq : (univ.filter fun x : Fin 5 × Fin 6 => r x.1 x.2 ∧ x.2 = j) =
      ((univ.filter fun i => r i j) ×ˢ {j}) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton]
    constructor
    · rintro ⟨hr, hj⟩
      exact ⟨hj ▸ hr, hj⟩
    · rintro ⟨hr, hj⟩
      exact ⟨hj ▸ hr, hj⟩
  rw [heq, card_product, card_singleton, mul_one]

private theorem degree_left_matrix (K : SimpleGraph (Fin 5 ⊕ Fin 6)) [DecidableRel K.Adj]
    (hK : K ≤ seedGraph) (i : Fin 5) :
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

private theorem degree_right_matrix (K : SimpleGraph (Fin 5 ⊕ Fin 6)) [DecidableRel K.Adj]
    (hK : K ≤ seedGraph) (j : Fin 6) :
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

noncomputable instance seedSubgraphCoeLocallyFinite (H : seedGraph.Subgraph) :
    H.coe.LocallyFinite := fun _ => Fintype.ofFinite _

/-- Literal arbitrary subgraph quartic absence for the actual eleven-vertex graph. -/
theorem seed_no_quartic_subgraph :
    ¬ ∃ H : seedGraph.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 4 := by
  classical
  rintro ⟨H, hne, hregular⟩
  let F := univ.filter fun x : Fin 5 × Fin 6 => H.Adj (Sum.inl x.1) (Sum.inr x.2)
  have hleft (i : Fin 5) : matrixRowDegree F i = H.degree (Sum.inl i) := by
    dsimp [F]
    rw [row_card_matrix (fun i j => H.Adj (Sum.inl i) (Sum.inr j)) i]
    exact (degree_left_matrix H.spanningCoe H.spanningCoe_le i).symm.trans
      (SimpleGraph.Subgraph.degree_spanningCoe _)
  have hright (j : Fin 6) : matrixColumnDegree F j = H.degree (Sum.inr j) := by
    dsimp [F]
    rw [column_card_matrix (fun i j => H.Adj (Sum.inl i) (Sum.inr j)) j]
    exact (degree_right_matrix H.spanningCoe H.spanningCoe_le j).symm.trans
      (SimpleGraph.Subgraph.degree_spanningCoe _)
  have hdegrees (v : Fin 5 ⊕ Fin 6) : H.degree v = 0 ∨ H.degree v = 4 := by
    by_cases hv : v ∈ H.verts
    · right
      exact (SimpleGraph.Subgraph.coe_degree H ⟨v, hv⟩).symm.trans (hregular.degree_eq _)
    · left
      exact SimpleGraph.Subgraph.degree_of_notMem_verts hv
  have hFne : F.Nonempty := by
    obtain ⟨v, hv⟩ := hne
    have hd : H.degree v = 4 :=
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
  apply seed_no_quartic_matrix F hFne
  · intro x hx
    exact H.adj_sub (mem_filter.mp hx).2
  · intro i
    rw [hleft]
    exact hdegrees _
  · intro j
    rw [hright]
    exact hdegrees _

end Erdos585.QBSharpness

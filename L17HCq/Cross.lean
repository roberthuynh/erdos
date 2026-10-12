import BqLowerFamilyDirect

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open Finset SimpleGraph
namespace Erdos585.L17HCq

theorem capacity_slots_plus_one {X : Type*} [DecidableEq X] (r : ℕ) (hr : 1 ≤ r)
    (S : Finset X) (g : X → ℕ)
    (hd : ∀ v ∈ S, r ≤ g v ∧ g v ≤ 2*r)
    (hc : r*(r-1)+1 ≤ ∑ v ∈ S, (2*r-g v)) :
    r ≤ (S.filter fun v => g v ≤ 2*r-1).card := by
  have hle : (∑ v ∈ S, (2*r-g v)) ≤
      ∑ v ∈ S, if g v ≤ 2*r-1 then r else 0 := by
    apply sum_le_sum
    intro v hv
    have hvd := hd v hv
    split_ifs <;> omega
  have heq : (∑ v ∈ S, if g v ≤ 2*r-1 then r else 0) =
      r * (S.filter fun v => g v ≤ 2*r-1).card := by
    rw [← sum_filter]
    simp [mul_comm]
  rw [heq] at hle
  by_contra hnot
  have hn : (S.filter fun v => g v ≤ 2*r-1).card ≤ r-1 := by omega
  have hmul := Nat.mul_le_mul_left r hn
  omega

section Cross
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def crossGraph (R : A → B → Prop) : SimpleGraph (A ⊕ B) where
  Adj v w := match v,w with
    | .inl i,.inr j => R i j
    | .inr j,.inl i => R i j
    | _,_ => False
  symm := ⟨by intro v w; cases v <;> cases w <;> simp⟩
  loopless := ⟨by intro v; cases v <;> simp⟩

instance crossGraphDecidable (R : A → B → Prop) [∀ i j, Decidable (R i j)] :
    DecidableRel (crossGraph R).Adj := fun v w => by
  cases v <;> cases w <;> unfold crossGraph <;> infer_instance

def rowDegree (R : A → B → Prop) [∀ i j, Decidable (R i j)]
    (Q : Finset B) (i : A) : ℕ := (Q.filter (R i)).card

def columnDegree (R : A → B → Prop) [∀ i j, Decidable (R i j)]
    (P : Finset A) (j : B) : ℕ := (P.filter fun i => R i j).card

theorem cross_degree_left (R : A → B → Prop) [∀ i j, Decidable (R i j)]
    (K : SimpleGraph (A ⊕ B)) [DecidableRel K.Adj]
    (hK : K ≤ crossGraph R) (i : A) :
    K.degree (.inl i) = (univ.filter fun j => K.Adj (.inl i) (.inr j)).card := by
  have hn : K.neighborFinset (.inl i) =
      (univ.filter fun j => K.Adj (.inl i) (.inr j)).image Sum.inr := by
    ext v
    cases v with
    | inl i' =>
      have hnot : ¬ K.Adj (.inl i) (.inl i') := fun h => hK h
      simp [hnot]
    | inr j => simp
  rw [← card_neighborFinset_eq_degree, hn, card_image_of_injective _ Sum.inr_injective]

theorem cross_degree_right (R : A → B → Prop) [∀ i j, Decidable (R i j)]
    (K : SimpleGraph (A ⊕ B)) [DecidableRel K.Adj]
    (hK : K ≤ crossGraph R) (j : B) :
    K.degree (.inr j) = (univ.filter fun i => K.Adj (.inl i) (.inr j)).card := by
  have hn : K.neighborFinset (.inr j) =
      (univ.filter fun i => K.Adj (.inl i) (.inr j)).image Sum.inl := by
    ext v
    cases v with
    | inl i => simp [K.adj_comm]
    | inr j' =>
      have hnot : ¬ K.Adj (.inr j) (.inr j') := fun h => hK h
      simp [hnot]
  rw [← card_neighborFinset_eq_degree, hn, card_image_of_injective _ Sum.inl_injective]

theorem cross_bipartite (R : A → B → Prop) :
    (crossGraph R).IsBipartiteWith ↑(univ.image Sum.inl : Finset (A ⊕ B))
      ↑(univ.image Sum.inr : Finset (A ⊕ B)) := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_coe]
    apply Finset.disjoint_left.mpr
    intro v hvl hvr
    rcases mem_image.mp hvl with ⟨a,_,rfl⟩
    rcases mem_image.mp hvr with ⟨b,_,hb⟩
    cases hb
  · intro v w hvw
    cases v <;> cases w <;> simp [crossGraph] at hvw ⊢

theorem required_neighbors {X Y : Type*} [DecidableEq Y]
    (R : X → Y → Prop) [∀ x y, Decidable (R x y)]
    (S T : Finset Y) (x : X) (hST : S ⊆ T)
    (q : ℕ) (hfull : (T.filter (R x)).card = q)
    (hlower : q ≤ (S.filter (R x)).card) :
    ∀ y ∈ T, R x y → y ∈ S := by
  have hsub := filter_subset_filter (R x) hST
  have heq := eq_of_subset_of_card_le hsub (by omega)
  intro y hy hr
  have hm : y ∈ T.filter (R x) := mem_filter.mpr ⟨hy,hr⟩
  rw [← heq] at hm
  exact (mem_filter.mp hm).1

theorem noRegular_crossGraph (R : A → B → Prop) [∀ i j, Decidable (R i j)]
    (q : ℕ) (hq : 0 < q)
    (hbad : ∀ (P : Finset A) (Q : Finset B), P.Nonempty → P.card = Q.card →
      (∀ i ∈ P, q ≤ rowDegree R Q i) →
      (∀ j ∈ Q, q ≤ columnDegree R P j) → False) :
    BqLowerFamily.NoRegular q (crossGraph R) := by
  classical
  rintro ⟨H,hne,hreg⟩
  let F := univ.filter fun x : A × B => H.Adj (.inl x.1) (.inr x.2)
  let rd := fun i : A => (F.filter fun x => x.1 = i).card
  let cd := fun j : B => (F.filter fun x => x.2 = j).card
  have hleft (i : A) : rd i = H.degree (.inl i) := by
    have heq : (F.filter fun x => x.1 = i) =
        {i} ×ˢ (univ.filter fun j => H.Adj (.inl i) (.inr j)) := by
      ext x
      simp only [F, mem_filter, mem_univ, true_and, mem_product, mem_singleton]
      constructor <;> rintro ⟨h1,h2⟩
      · exact ⟨h2,h2 ▸ h1⟩
      · exact ⟨h1 ▸ h2,h1⟩
    change (F.filter fun x => x.1 = i).card = _
    rw [heq, card_product, card_singleton, one_mul]
    exact (cross_degree_left R H.spanningCoe H.spanningCoe_le i).symm.trans
      (Subgraph.degree_spanningCoe _)
  have hright (j : B) : cd j = H.degree (.inr j) := by
    have heq : (F.filter fun x => x.2 = j) =
        (univ.filter fun i => H.Adj (.inl i) (.inr j)) ×ˢ {j} := by
      ext x
      simp only [F, mem_filter, mem_univ, true_and, mem_product, mem_singleton]
      constructor <;> rintro ⟨h1,h2⟩
      · exact ⟨h2 ▸ h1,h2⟩
      · exact ⟨h2 ▸ h1,h2⟩
    change (F.filter fun x => x.2 = j).card = _
    rw [heq, card_product, card_singleton, mul_one]
    exact (cross_degree_right R H.spanningCoe H.spanningCoe_le j).symm.trans
      (Subgraph.degree_spanningCoe _)
  have hdegrees (v : A ⊕ B) : H.degree v = 0 ∨ H.degree v = q := by
    by_cases hv : v ∈ H.verts
    · exact Or.inr ((Subgraph.coe_degree H ⟨v,hv⟩).symm.trans (hreg.degree_eq _))
    · exact Or.inl (Subgraph.degree_of_notMem_verts hv)
  let P := univ.filter fun i => 0 < rd i
  let Q := univ.filter fun j => 0 < cd j
  have hP (i : A) : i ∈ P ↔ 0 < rd i := by simp [P]
  have hQ (j : B) : j ∈ Q ↔ 0 < cd j := by simp [Q]
  have hPq (i : A) (hi : i ∈ P) : rd i = q := by
    have := hdegrees (.inl i)
    rw [← hleft] at this
    exact this.resolve_left (Nat.ne_of_gt ((hP i).mp hi))
  have hQq (j : B) (hj : j ∈ Q) : cd j = q := by
    have := hdegrees (.inr j)
    rw [← hright] at this
    exact this.resolve_left (Nat.ne_of_gt ((hQ j).mp hj))
  have hFr : F.card = ∑ i : A, rd i :=
    card_eq_sum_card_fiberwise (f := Prod.fst) (s := F) (t := univ) (by simp)
  have hFc : F.card = ∑ j : B, cd j :=
    card_eq_sum_card_fiberwise (f := Prod.snd) (s := F) (t := univ) (by simp)
  have hsumP : (∑ i : A, rd i) = q * P.card := by
    calc
      _ = ∑ i : A, if i ∈ P then q else 0 := by
        apply sum_congr rfl
        intro i _
        by_cases hi : i ∈ P
        · simp [hi,hPq i hi]
        · have hz : rd i = 0 := by have := mt (hP i).mpr hi; omega
          simp [hi,hz]
      _ = _ := by simp [mul_comm]
  have hsumQ : (∑ j : B, cd j) = q * Q.card := by
    calc
      _ = ∑ j : B, if j ∈ Q then q else 0 := by
        apply sum_congr rfl
        intro j _
        by_cases hj : j ∈ Q
        · simp [hj,hQq j hj]
        · have hz : cd j = 0 := by have := mt (hQ j).mpr hj; omega
          simp [hj,hz]
      _ = _ := by simp [mul_comm]
  have hbal : P.card = Q.card := by nlinarith
  have hPne : P.Nonempty := by
    obtain ⟨v,hv⟩ := hne
    have hd : H.degree v = q := (Subgraph.coe_degree H ⟨v,hv⟩).symm.trans (hreg.degree_eq _)
    obtain ⟨w,hvw⟩ := Subgraph.degree_pos_iff_exists_adj.mp (by omega : 0 < H.degree v)
    have hg := H.adj_sub hvw
    cases v with
    | inl i =>
      cases w with
      | inl i' => exact hg.elim
      | inr j =>
        refine ⟨i,(hP i).mpr (card_pos.mpr ?_)⟩
        exact ⟨(i,j),mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hvw⟩,rfl⟩⟩
    | inr j =>
      cases w with
      | inl i =>
        refine ⟨i,(hP i).mpr (card_pos.mpr ?_)⟩
        exact ⟨(i,j),mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hvw.symm⟩,rfl⟩⟩
      | inr j' => exact hg.elim
  apply hbad P Q hPne hbal
  · intro i hi
    let T := F.filter fun x => x.1 = i
    have hinj : Set.InjOn Prod.snd (T : Set (A × B)) := by
      intro x hx y hy hxy
      exact Prod.ext ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) hxy
    have hsub : T.image Prod.snd ⊆ Q.filter (R i) := by
      intro j hj
      rcases mem_image.mp hj with ⟨x,hx,rfl⟩
      obtain ⟨hxF,hxi⟩ := mem_filter.mp hx
      refine mem_filter.mpr ⟨(hQ x.2).mpr (card_pos.mpr ?_), ?_⟩
      · exact ⟨x,mem_filter.mpr ⟨hxF,rfl⟩⟩
      · exact hxi ▸ H.adj_sub (mem_filter.mp hxF).2
    have hle := card_le_card hsub
    rw [card_image_of_injOn hinj] at hle
    change rd i ≤ rowDegree R Q i at hle
    rwa [hPq i hi] at hle
  · intro j hj
    let T := F.filter fun x => x.2 = j
    have hinj : Set.InjOn Prod.fst (T : Set (A × B)) := by
      intro x hx y hy hxy
      exact Prod.ext hxy ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)
    have hsub : T.image Prod.fst ⊆ P.filter fun i => R i j := by
      intro i hi
      rcases mem_image.mp hi with ⟨x,hx,rfl⟩
      obtain ⟨hxF,hxj⟩ := mem_filter.mp hx
      refine mem_filter.mpr ⟨(hP x.1).mpr (card_pos.mpr ?_), ?_⟩
      · exact ⟨x,mem_filter.mpr ⟨hxF,rfl⟩⟩
      · exact hxj ▸ H.adj_sub (mem_filter.mp hxF).2
    have hle := card_le_card hsub
    rw [card_image_of_injOn hinj] at hle
    change cd j ≤ columnDegree R P j at hle
    rwa [hQq j hj] at hle
end Cross

end Erdos585.L17HCq

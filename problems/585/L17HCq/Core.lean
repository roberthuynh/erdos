import L17HCq.Cross
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
open Finset SimpleGraph
namespace Erdos585.L17HCq

def coreAdj (q : ℕ) (i : Fin (q+1)) (j : Fin (q+3)) : Prop :=
  ¬ ((i.val=0 ∧ (j.val=0 ∨ j.val=1)) ∨
     (i.val=1 ∧ (j.val=2 ∨ j.val=3)) ∨
     (i.val=2 ∧ (j.val=4 ∨ j.val=5)))
instance coreAdjDecidable (q : ℕ) : DecidableRel (coreAdj q) := fun _ _ => by
  unfold coreAdj; infer_instance

def coreMissing (q : ℕ) (hq : 5 ≤ q) : Finset (Fin (q+1) × Fin (q+3)) :=
  {(⟨0,by omega⟩,⟨0,by omega⟩),(⟨0,by omega⟩,⟨1,by omega⟩),
   (⟨1,by omega⟩,⟨2,by omega⟩),(⟨1,by omega⟩,⟨3,by omega⟩),
   (⟨2,by omega⟩,⟨4,by omega⟩),(⟨2,by omega⟩,⟨5,by omega⟩)}
theorem coreMissing_card (q : ℕ) (hq : 5 ≤ q) : (coreMissing q hq).card=6 := by
  simp [coreMissing,Fin.ext_iff]
theorem coreMissing_iff (q : ℕ) (hq : 5 ≤ q) (i : Fin (q+1)) (j : Fin (q+3)) :
    (i,j) ∈ coreMissing q hq ↔ ¬ coreAdj q i j := by
  simp only [coreMissing,mem_insert,mem_singleton,Prod.mk.injEq,Fin.ext_iff,coreAdj,not_not]
  tauto

theorem coreMissing_row_cap (q : ℕ) (hq : 5 ≤ q) (i : Fin (q+1)) :
    ((coreMissing q hq).filter fun x => x.1=i).card ≤ 2 := by
  by_cases h0 : i.val=0
  · simp [coreMissing,filter_insert,filter_singleton,Fin.ext_iff,-Fin.val_eq_zero_iff,h0]
  by_cases h1 : i.val=1
  · simp [coreMissing,filter_insert,filter_singleton,Fin.ext_iff,-Fin.val_eq_zero_iff,h1]
  by_cases h2 : i.val=2
  · simp [coreMissing,filter_insert,filter_singleton,Fin.ext_iff,-Fin.val_eq_zero_iff,h2]
  · have hn0 := Ne.symm h0; have hn1 := Ne.symm h1; have hn2 := Ne.symm h2
    simp [coreMissing,filter_insert,filter_singleton,Fin.ext_iff,-Fin.val_eq_zero_iff,hn0,hn1,hn2]

theorem coreMissing_column_cap (q : ℕ) (hq : 5 ≤ q) (j : Fin (q+3)) :
    ((coreMissing q hq).filter fun x => x.2=j).card ≤ 1 := by
  by_cases h0 : j.val=0
  · simp [coreMissing,filter_insert,filter_singleton,Fin.ext_iff,-Fin.val_eq_zero_iff,h0]
  by_cases h1 : j.val=1
  · simp [coreMissing,filter_insert,filter_singleton,Fin.ext_iff,-Fin.val_eq_zero_iff,h1]
  by_cases h2 : j.val=2
  · simp [coreMissing,filter_insert,filter_singleton,Fin.ext_iff,-Fin.val_eq_zero_iff,h2]
  by_cases h3 : j.val=3
  · simp [coreMissing,filter_insert,filter_singleton,Fin.ext_iff,-Fin.val_eq_zero_iff,h3]
  by_cases h4 : j.val=4
  · simp [coreMissing,filter_insert,filter_singleton,Fin.ext_iff,-Fin.val_eq_zero_iff,h4]
  by_cases h5 : j.val=5
  · simp [coreMissing,filter_insert,filter_singleton,Fin.ext_iff,-Fin.val_eq_zero_iff,h5]
  · have hn0 := Ne.symm h0; have hn1 := Ne.symm h1; have hn2 := Ne.symm h2
    have hn3 := Ne.symm h3; have hn4 := Ne.symm h4; have hn5 := Ne.symm h5
    simp [coreMissing,filter_insert,filter_singleton,Fin.ext_iff,-Fin.val_eq_zero_iff,hn0,hn1,hn2,hn3,hn4,hn5]

theorem core_no_complete (q : ℕ) (hq : 5 ≤ q)
    (P : Finset (Fin (q+1))) (Q : Finset (Fin (q+3)))
    (hp : P.card=q) (hqc : Q.card=q)
    (hcomplete : ∀ i ∈ P, ∀ j ∈ Q, coreAdj q i j) : False := by
  have hpcomp : (univ \ P).card=1 := by
    rw [card_sdiff_of_subset (subset_univ P),card_univ,Fintype.card_fin,hp];omega
  have hqcomp : (univ \ Q).card=3 := by
    rw [card_sdiff_of_subset (subset_univ Q),card_univ,Fintype.card_fin,hqc];omega
  obtain ⟨a,ha⟩ := card_eq_one.mp hpcomp
  let R := (coreMissing q hq).filter fun x => x.1=a
  let C := (coreMissing q hq).filter fun x => x.2 ∈ univ \ Q
  have hsub : coreMissing q hq ⊆ R ∪ C := by
    intro x hx
    by_cases hi : x.1 ∈ P
    · by_cases hj : x.2 ∈ Q
      · exact ((coreMissing_iff q hq x.1 x.2).mp hx (hcomplete _ hi _ hj)).elim
      · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hx,by simp [hj]⟩))
    · have hn : x.1 ∈ univ \ P := by simp [hi]
      have heq : x.1=a := by simpa [ha] using hn
      exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hx,heq⟩))
  have hC : C.card ≤ (univ \ Q).card := by
    have hinj : Set.InjOn Prod.snd (C : Set (Fin (q+1) × Fin (q+3))) := by
      intro x hx y hy hxy
      have hxm := (mem_filter.mp hx).1
      have hym := (mem_filter.mp hy).1
      have hm := coreMissing_column_cap q hq x.2
      have hs : {x,y} ⊆ (coreMissing q hq).filter fun z => z.2=x.2 := by
        intro z hz
        rcases mem_insert.mp hz with rfl | hz
        · simp [hxm]
        · have hz' : z=y := mem_singleton.mp hz
          subst z; simp [hym,hxy]
      have hle := card_le_card hs
      by_contra hne
      have hcxy : ({x,y} : Finset (Fin (q+1) × Fin (q+3))).card=2 := by simp [hne]
      omega
    have hle : C.image Prod.snd ⊆ univ \ Q := by
      intro j hj
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hj
      exact (mem_filter.mp hx).2
    have hc := card_le_card hle
    rw [card_image_of_injOn hinj] at hc
    exact hc
  have hm := card_le_card hsub
  have hu := card_union_le R C
  have hr := coreMissing_row_cap q hq a
  rw [coreMissing_card] at hm
  change R.card ≤ 2 at hr
  omega

theorem two_missing_omission {A B : Type*} [DecidableEq B]
    (R : A → B → Prop) [∀ a b,Decidable (R a b)]
    (q : ℕ) (hq : 1 ≤ q) (Q : Finset B) (i : A) (a b : B) (hab : a ≠ b)
    (ha : ¬ R i a) (hb : ¬ R i b) (hcard : Q.card=q+1)
    (hlow : q ≤ rowDegree R Q i) : a ∉ Q ∨ b ∉ Q := by
  by_contra hn
  have hQa : a ∈ Q := by tauto
  have hQb : b ∈ Q := by tauto
  have hsub : Q.filter (R i) ⊆ (Q.erase a).erase b := by
    intro j hj
    obtain ⟨hjQ,hR⟩ := mem_filter.mp hj
    simp only [mem_erase]
    exact ⟨by intro he; subst j; exact hb hR,by intro he; subst j; exact ha hR,hjQ⟩
  have hle := card_le_card hsub
  rw [card_erase_of_mem (by simp [hQb,hab.symm]),card_erase_of_mem hQa,hcard] at hle
  change q ≤ (Q.filter (R i)).card at hlow
  omega

theorem three_omitted {B : Type*} [Fintype B] [DecidableEq B]
    (Q : Finset B) (a b c : B) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∉ Q) (hb : b ∉ Q) (hc : c ∉ Q)
    (hcomp : (univ \ Q).card=2) : False := by
  have hs : {a,b,c} ⊆ univ \ Q := by
    intro j hj
    simp only [mem_insert,mem_singleton] at hj
    rcases hj with rfl | rfl | rfl <;> simp_all
  have hle := card_le_card hs
  have hcard : ({a,b,c} : Finset B).card=3 := by simp [hab,hac,hbc]
  omega

theorem core_no_balanced_support (q : ℕ) (hq : 5 ≤ q)
    (P : Finset (Fin (q+1))) (Q : Finset (Fin (q+3)))
    (hne : P.Nonempty) (hbal : P.card=Q.card)
    (hrow : ∀ i ∈ P, q ≤ rowDegree (coreAdj q) Q i) : False := by
  have hlo : q ≤ P.card := by
    obtain ⟨i,hi⟩ := hne
    have hr := hrow i hi
    have hc := card_filter_le Q (coreAdj q i)
    change rowDegree (coreAdj q) Q i ≤ Q.card at hc
    omega
  have hhi : P.card ≤ q+1 := by simpa using card_le_card (subset_univ P)
  by_cases hk : P.card=q
  · apply core_no_complete q hq P Q hk (by omega)
    intro i hi j hj
    have heq : Q.filter (coreAdj q i)=Q :=
      eq_of_subset_of_card_le (filter_subset _ Q) (by
        have := hrow i hi
        change Q.card ≤ rowDegree (coreAdj q) Q i
        omega)
    exact (mem_filter.mp (show j ∈ Q.filter (coreAdj q i) by rwa [heq])).2
  · have hk' : P.card=q+1 := by omega
    have hP : P=univ := eq_of_subset_of_card_le (subset_univ P) (by simpa using hk'.ge)
    have hQc : Q.card=q+1 := by omega
    have hcomp : (univ \ Q).card=2 := by
      rw [card_sdiff_of_subset (subset_univ Q),card_univ,Fintype.card_fin,hQc];omega
    have h0 := two_missing_omission (coreAdj q) q (by omega) Q (⟨0,by omega⟩:Fin (q+1))
      (⟨0,by omega⟩:Fin (q+3)) (⟨1,by omega⟩:Fin (q+3))
      (by simp [Fin.ext_iff]) (by simp [coreAdj]) (by simp [coreAdj]) hQc
      (hrow _ (by simp [hP]))
    have h1 := two_missing_omission (coreAdj q) q (by omega) Q (⟨1,by omega⟩:Fin (q+1))
      (⟨2,by omega⟩:Fin (q+3)) (⟨3,by omega⟩:Fin (q+3))
      (by simp [Fin.ext_iff]) (by simp [coreAdj]) (by simp [coreAdj]) hQc
      (hrow _ (by simp [hP]))
    have h2 := two_missing_omission (coreAdj q) q (by omega) Q (⟨2,by omega⟩:Fin (q+1))
      (⟨4,by omega⟩:Fin (q+3)) (⟨5,by omega⟩:Fin (q+3))
      (by simp [Fin.ext_iff]) (by simp [coreAdj]) (by simp [coreAdj]) hQc
      (hrow _ (by simp [hP]))
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    all_goals refine three_omitted Q _ _ _ ?_ ?_ ?_ h0 h1 h2 hcomp <;> simp [Fin.ext_iff]
end Erdos585.L17HCq

import L17HCq.Core
import L17HCq.Birth
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
open Finset SimpleGraph BqLowerFamily
namespace Erdos585.L17HCq
abbrev SeedLeft (q : ℕ) := Fin (q+1) ⊕ Fin 2
abbrev SeedRight (q : ℕ) := Fin (q+3) ⊕ Unit
abbrev SeedVertex (q : ℕ) := SeedLeft q ⊕ SeedRight q

def seedRel (q : ℕ) : SeedLeft q → SeedRight q → Prop
  | .inl i,.inl j => coreAdj q i j
  | .inl i,.inr _ => i.val < q-2
  | .inr a,.inl j => if a.val=0 then j.val < q-1 else 4 ≤ j.val
  | .inr _,.inr _ => True
instance seedRelDecidable (q : ℕ) : DecidableRel (seedRel q) := fun i j => by
  cases i <;> cases j <;> unfold seedRel <;> infer_instance

def hcqSeedGraph (q : ℕ) : SimpleGraph (SeedVertex q) := crossGraph (seedRel q)
instance hcqSeedDecidable (q : ℕ) : DecidableRel (hcqSeedGraph q).Adj := by unfold hcqSeedGraph; infer_instance

def hcqSeedA (q : ℕ) : Finset (SeedVertex q) := univ.image Sum.inl
def hcqSeedB (q : ℕ) : Finset (SeedVertex q) := univ.image Sum.inr

theorem card_filter_sum {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (p : A ⊕ B → Prop) [DecidablePred p] :
    (univ.filter p).card=(univ.filter fun a => p (.inl a)).card+
      (univ.filter fun b => p (.inr b)).card := by
  have heq : univ.filter p =
      (univ.filter fun a => p (.inl a)).image Sum.inl ∪
      (univ.filter fun b => p (.inr b)).image Sum.inr := by
    ext x;cases x <;> simp
  have hd : Disjoint ((univ.filter fun a => p (.inl a)).image Sum.inl)
      ((univ.filter fun b => p (.inr b)).image Sum.inr) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a,_,rfl⟩ := mem_image.mp hx
    obtain ⟨b,_,hb⟩ := mem_image.mp hy
    cases hb
  rw [heq,card_union_of_disjoint hd,card_image_of_injective _ Sum.inl_injective,
    card_image_of_injective _ Sum.inr_injective]

theorem fin_lt_card (n m : ℕ) :
    (univ.filter fun i : Fin n => i.val < m).card= min n m := Fin.card_filter_val_lt

theorem fin_ge_card (n m : ℕ) :
    (univ.filter fun i : Fin n => m ≤ i.val).card=n-min n m := by
  have heq : (univ.filter fun i : Fin n => m ≤ i.val)=
      univ \ (univ.filter fun i : Fin n => i.val < m) := by
    ext i;simp only [mem_filter,mem_univ,true_and,mem_sdiff];omega
  rw [heq,card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin,fin_lt_card]

theorem seed_row_f (q : ℕ) (hq : 5 ≤ q) :
    rowDegree (seedRel q) univ (.inr (0:Fin 2))=q := by
  unfold rowDegree
  rw [card_filter_sum]
  simp only [seedRel,Fin.val_zero,ite_true]
  rw [fin_lt_card]
  simp only [filter_true_of_mem (fun _ _ => trivial),card_univ,Fintype.card_unique]
  rw [Nat.min_eq_right (by omega)]
  omega

theorem seed_row_g (q : ℕ) (hq : 5 ≤ q) :
    rowDegree (seedRel q) univ (.inr (1:Fin 2))=q := by
  unfold rowDegree
  rw [card_filter_sum]
  simp only [seedRel,Fin.val_one,one_ne_zero,ite_false]
  rw [fin_ge_card]
  simp only [filter_true_of_mem (fun _ _ => trivial),card_univ,Fintype.card_unique]
  rw [Nat.min_eq_right (by omega)]
  omega

theorem seed_column_h (q : ℕ) (hq : 5 ≤ q) :
    columnDegree (seedRel q) univ (.inr ())=q := by
  unfold columnDegree
  rw [card_filter_sum]
  simp only [seedRel]
  rw [fin_lt_card]
  simp only [filter_true_of_mem (fun _ _ => trivial),card_univ,Fintype.card_fin]
  rw [Nat.min_eq_right (by omega)]
  omega

theorem core_row_card (q : ℕ) (hq : 5 ≤ q) (i : Fin (q+1)) :
    rowDegree (coreAdj q) univ i = if i.val < 3 then q+1 else q+3 := by
  by_cases h0 : i.val=0
  · have hs : univ.filter (coreAdj q i)=
        (univ.erase (⟨0,by omega⟩:Fin (q+3))).erase ⟨1,by omega⟩ := by
      ext j;simp [coreAdj,Fin.ext_iff,-Fin.val_eq_zero_iff,h0];tauto
    unfold rowDegree
    rw [hs,card_erase_of_mem (by simp),card_erase_of_mem (by simp),card_univ,Fintype.card_fin]
    simp [h0]
  by_cases h1 : i.val=1
  · have hs : univ.filter (coreAdj q i)=
        (univ.erase (⟨2,by omega⟩:Fin (q+3))).erase ⟨3,by omega⟩ := by
      ext j;simp [coreAdj,Fin.ext_iff,-Fin.val_eq_zero_iff,h1];tauto
    unfold rowDegree
    rw [hs,card_erase_of_mem (by simp),card_erase_of_mem (by simp),card_univ,Fintype.card_fin]
    simp [h1]
  by_cases h2 : i.val=2
  · have hs : univ.filter (coreAdj q i)=
        (univ.erase (⟨4,by omega⟩:Fin (q+3))).erase ⟨5,by omega⟩ := by
      ext j;simp [coreAdj,Fin.ext_iff,-Fin.val_eq_zero_iff,h2];tauto
    unfold rowDegree
    rw [hs,card_erase_of_mem (by simp),card_erase_of_mem (by simp),card_univ,Fintype.card_fin]
    simp [h2]
  · have hs : univ.filter (coreAdj q i)=univ := by
      ext j;simp [coreAdj,h0,h1,h2]
    have hi : ¬ i.val < 3 := by omega
    simp [rowDegree,hs,hi]

/-- Trap exclusion uses both physical row and physical column lower bounds. -/
theorem seed_no_balanced_support (q : ℕ) (hq : 5 ≤ q)
    (P : Finset (SeedLeft q)) (Q : Finset (SeedRight q))
    (hne : P.Nonempty) (hbal : P.card=Q.card)
    (hrow : ∀ i ∈ P,q ≤ rowDegree (seedRel q) Q i)
    (hcol : ∀ j ∈ Q,q ≤ columnDegree (seedRel q) P j) : False := by
  have hf (hi : (.inr (0:Fin 2):SeedLeft q) ∈ P) : (.inr ():SeedRight q) ∈ Q := by
    exact required_neighbors (seedRel q) Q univ (.inr 0) (subset_univ _) q
      (seed_row_f q hq) (hrow _ hi) (.inr ()) (mem_univ _) trivial
  have hg (hi : (.inr (1:Fin 2):SeedLeft q) ∈ P) : (.inr ():SeedRight q) ∈ Q := by
    exact required_neighbors (seedRel q) Q univ (.inr 1) (subset_univ _) q
      (seed_row_g q hq) (hrow _ hi) (.inr ()) (mem_univ _) trivial
  have hh (hj : (.inr ():SeedRight q) ∈ Q) :
      (.inr (0:Fin 2):SeedLeft q) ∈ P ∧ (.inr (1:Fin 2):SeedLeft q) ∈ P := by
    have hreq := required_neighbors (fun j i => seedRel q i j) P univ (.inr ())
      (subset_univ _) q (seed_column_h q hq) (hcol _ hj)
    exact ⟨hreq (.inr 0) (mem_univ _) trivial,hreq (.inr 1) (mem_univ _) trivial⟩
  have hnH : (.inr ():SeedRight q) ∉ Q := by
    intro hhQ
    obtain ⟨hfP,hgP⟩ := hh hhQ
    have hQall : Q=univ := by
      ext j;simp only [mem_univ,iff_true]
      cases j with
      | inr u => cases u;exact hhQ
      | inl j =>
        have hcover : seedRel q (.inr (0:Fin 2)) (.inl j) ∨
            seedRel q (.inr (1:Fin 2)) (.inl j) := by
          dsimp [seedRel];omega
        rcases hcover with h0 | h1
        · exact required_neighbors (seedRel q) Q univ (.inr 0) (subset_univ _) q
            (seed_row_f q hq) (hrow _ hfP) _ (mem_univ _) h0
        · exact required_neighbors (seedRel q) Q univ (.inr 1) (subset_univ _) q
            (seed_row_g q hq) (hrow _ hgP) _ (mem_univ _) h1
    have hPcard : P.card ≤ q+3 := by
      have := card_le_card (subset_univ P)
      simpa only [card_univ,Fintype.card_sum,Fintype.card_fin] using this
    have hQcard : Q.card=q+4 := by simp [hQall,SeedRight,Fintype.card_sum]
    omega
  have hnF : (.inr (0:Fin 2):SeedLeft q) ∉ P := fun h => hnH (hf h)
  have hnG : (.inr (1:Fin 2):SeedLeft q) ∉ P := fun h => hnH (hg h)
  let P0 := univ.filter fun i : Fin (q+1) => (.inl i:SeedLeft q) ∈ P
  let Q0 := univ.filter fun j : Fin (q+3) => (.inl j:SeedRight q) ∈ Q
  have hP : P=P0.image Sum.inl := by
    ext i
    cases i with
    | inl i => simp [P0]
    | inr a => fin_cases a <;> simp [hnF,hnG]
  have hQ : Q=Q0.image Sum.inl := by
    ext j
    cases j with
    | inl j => simp [Q0]
    | inr u => cases u;simp [hnH]
  have hP0 : P0.Nonempty := by
    rw [hP] at hne
    exact (image_nonempty).mp hne
  have hbal0 : P0.card=Q0.card := by
    rw [hP,hQ,card_image_of_injective _ Sum.inl_injective,
      card_image_of_injective _ Sum.inl_injective] at hbal
    exact hbal
  apply core_no_balanced_support q hq P0 Q0 hP0 hbal0
  intro i hi
  have h := hrow (.inl i) (by rw [hP];simp [hi])
  have heq : rowDegree (seedRel q) Q (.inl i)=rowDegree (coreAdj q) Q0 i := by
    unfold rowDegree
    rw [hQ,filter_image]
    simp only [seedRel]
    rw [card_image_of_injective _ Sum.inl_injective]
  rwa [heq] at h

theorem hcq_seed_no_regular (q : ℕ) (hq : 5 ≤ q) :
    BqLowerFamily.NoRegular q (hcqSeedGraph q) :=
  noRegular_crossGraph (seedRel q) q (by omega) (seed_no_balanced_support q hq)
end Erdos585.L17HCq

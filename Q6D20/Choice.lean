import Q6D20.Base
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
open Finset SimpleGraph
namespace Erdos585.Q6D20R31

def orderedFin {n : ℕ} (S : Finset (Fin n)) : List (Fin n) :=
  (List.finRange n).filter fun v => decide (v ∈ S)

@[simp] theorem orderedFin_toFinset {n : ℕ} (S : Finset (Fin n)) :
    (orderedFin S).toFinset = S := by
  ext v
  simp [orderedFin]

theorem orderedFin_nodup {n : ℕ} (S : Finset (Fin n)) : (orderedFin S).Nodup :=
  (List.nodup_finRange n).filter _

theorem orderedFin_length {n : ℕ} (S : Finset (Fin n)) : (orderedFin S).length = S.card := by
  calc
    _ = (orderedFin S).toFinset.card := (List.toFinset_card_of_nodup (orderedFin_nodup S)).symm
    _ = S.card := congrArg Finset.card (orderedFin_toFinset S)

def priorityList {n : ℕ} (E L : Finset (Fin n)) : List (Fin n) :=
  orderedFin L ++ orderedFin (E \ L)

def priorityFive {n : ℕ} (E L : Finset (Fin n)) : Finset (Fin n) :=
  ((priorityList E L).take 5).toFinset

theorem priorityList_nodup {n : ℕ} (E L : Finset (Fin n)) :
    (priorityList E L).Nodup := by
  apply (orderedFin_nodup L).append (orderedFin_nodup (E \ L))
  apply List.disjoint_left.mpr
  intro v hv hw
  have hl : v ∈ L := by simpa [orderedFin] using hv
  have he : v ∈ E \ L := by simpa [orderedFin] using hw
  exact (mem_sdiff.mp he).2 hl

theorem priorityList_toFinset {n : ℕ} (E L : Finset (Fin n)) (hL : L ⊆ E) :
    (priorityList E L).toFinset = E := by
  ext v
  simp only [priorityList, List.toFinset_append, orderedFin_toFinset, mem_union, mem_sdiff]
  constructor
  · rintro (hl | ⟨he, _⟩)
    · exact hL hl
    · exact he
  · intro he
    by_cases hl : v ∈ L
    · exact Or.inl hl
    · exact Or.inr ⟨he, hl⟩

theorem priorityList_length {n : ℕ} (E L : Finset (Fin n)) (hL : L ⊆ E) :
    (priorityList E L).length = E.card := by
  rw [← List.toFinset_card_of_nodup (priorityList_nodup E L), priorityList_toFinset E L hL]

theorem priorityFive_subset {n : ℕ} (E L : Finset (Fin n)) (hL : L ⊆ E) :
    priorityFive E L ⊆ E := by
  intro v hv
  have hl := List.mem_of_mem_take (List.mem_toFinset.mp hv)
  rw [← priorityList_toFinset E L hL]
  exact List.mem_toFinset.mpr hl

theorem priorityFive_card {n : ℕ} (E L : Finset (Fin n)) (hL : L ⊆ E) (hE : 5 ≤ E.card) :
    (priorityFive E L).card = 5 := by
  unfold priorityFive
  rw [List.toFinset_card_of_nodup ((priorityList_nodup E L).take), List.length_take,
    priorityList_length E L hL, Nat.min_eq_left hE]

theorem priorityFive_mandatory {n : ℕ} (E L : Finset (Fin n)) (hL : L.card ≤ 5) :
    L ⊆ priorityFive E L := by
  intro v hv
  apply List.mem_toFinset.mpr
  change v ∈ (orderedFin L ++ orderedFin (E \ L)).take 5
  rw [List.take_append, List.take_of_length_le (by rw [orderedFin_length]; exact hL)]
  apply List.mem_append_left
  simpa [orderedFin] using hv

/-- Twenty actual slots with at most two degree-five endpoints force five distinct parents. -/
theorem capacity20 {V : Type*} [DecidableEq V] (S : Finset V) (g : V → ℕ)
    (hd : ∀ v ∈ S, 5 ≤ g v ∧ g v ≤ 10)
    (hL : (S.filter fun v => g v = 5).card ≤ 2)
    (hc : 20 ≤ ∑ v ∈ S, (10-g v)) :
    5 ≤ (S.filter fun v => g v ≤ 9).card := by
  have hle : (∑ v ∈ S, (10-g v)) ≤
      ∑ v ∈ S, ((if g v ≤ 9 then 4 else 0) + (if g v = 5 then 1 else 0)) := by
    apply sum_le_sum
    intro v hv
    have hvd := hd v hv
    split_ifs <;> omega
  have heq : (∑ v ∈ S, ((if g v ≤ 9 then 4 else 0) + (if g v = 5 then 1 else 0))) =
      4 * (S.filter fun v => g v ≤ 9).card + (S.filter fun v => g v = 5).card := by
    rw [sum_add_distrib]
    congr 1
    · rw [← sum_filter]
      simp [mul_comm]
    · rw [← sum_filter]
      simp
  rw [heq] at hle
  omega

variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem Good20.eligible {A B : Finset V} (h : Good20 G A B) (hsmall : A.card ≤ B.card)
    (hL : (B.filter fun v => G.degree v = 5).card ≤ 2) :
    5 ≤ (B.filter fun v => G.degree v ≤ 9).card := by
  have hcard : A.card+B.card = Fintype.card V := by
    rw [← card_union_of_disjoint h.disjoint, h.cover, card_univ]
  have hdensity : G.edgeFinset.card+20 = 5*(A.card+B.card) := by
    rw [hcard]
    exact h.density
  have hcapacity : (∑ v ∈ B, (10-G.degree v))+G.edgeFinset.card = 10*B.card := by
    calc
      _ = (∑ v ∈ B, (10-G.degree v)) + ∑ v ∈ B, G.degree v := by
        rw [SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' h.bipartite]
      _ = ∑ _v ∈ B, 10 := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro v _
        exact Nat.sub_add_cancel (h.degrees v).2
      _ = 10*B.card := by simp [mul_comm]
  exact capacity20 B (fun v => G.degree v) (fun v _ => h.degrees v) hL
    (BqLowerFamily.opposite_slots 5 A.card B.card G.edgeFinset.card 20
      (∑ v ∈ B, (10-G.degree v)) hsmall hdensity hcapacity)

end Erdos585.Q6D20R31

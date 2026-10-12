import Q6D20.Choice
import Openmath.Proofs.PaperSupport.Counter90.Main
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
open Finset SimpleGraph
namespace Erdos585.Q6D20R31

structure Data (n : ℕ) where
  graph : SimpleGraph (Fin n)
  decAdj : DecidableRel graph.Adj
  A : Finset (Fin n)
  B : Finset (Fin n)

instance Data.decidable {n : ℕ} (d : Data n) : DecidableRel d.graph.Adj := d.decAdj
def Data.Good {n : ℕ} (d : Data n) : Prop := Good20 d.graph d.A d.B

def seedData : Data 22 where
  graph := Counter90.graph
  decAdj := Counter90.graphDecidable
  A := univ.filter fun v => v.val < 10
  B := univ.filter fun v => 10 ≤ v.val

theorem seedData_good : seedData.Good := by
  refine ⟨?_, ?_, ?_, ?_, ?_, Counter90.seed_no_regular_subgraph⟩
  · apply Finset.disjoint_left.mpr
    intro v ha hb
    simp only [seedData, mem_filter, mem_univ, true_and] at ha hb
    omega
  · ext v
    simp only [seedData, mem_union, mem_filter, mem_univ, true_and]
    exact iff_true_intro (lt_or_ge _ _)
  · convert Counter90.original_bipartite using 1 <;>
      ext v <;> simp [seedData, Counter90.leftShore, Counter90.rightShore]
  · intro v
    change 5 ≤ Counter90.graph.degree v ∧ Counter90.graph.degree v ≤ 10
    have h := Counter90.original_degrees v
    exact ⟨by omega, h.2⟩
  · change Counter90.graph.edgeFinset.card + 20 = 5 * Fintype.card (Fin 22)
    rw [Counter90.original_edge_count]
    decide

/-- B enters on a tie. All old named shores remain original. -/
def opposite {n : ℕ} (d : Data n) : Finset (Fin n) :=
  if d.A.card < d.B.card then d.B else d.A
def selectedEligible {n : ℕ} (d : Data n) : Finset (Fin n) :=
  (opposite d).filter fun v => d.graph.degree v ≤ 9
def selectedLow {n : ℕ} (d : Data n) : Finset (Fin n) :=
  (opposite d).filter fun v => d.graph.degree v = 5
def selectedNeighbors {n : ℕ} (d : Data n) : Finset (Fin n) :=
  priorityFive (selectedEligible d) (selectedLow d)

theorem selectedLow_subset {n : ℕ} (d : Data n) : selectedLow d ⊆ selectedEligible d := by
  intro v hv
  rcases mem_filter.mp hv with ⟨ho, hd⟩
  exact mem_filter.mpr ⟨ho, by omega⟩

theorem selectedNeighbors_subset {n : ℕ} (d : Data n) :
    selectedNeighbors d ⊆ selectedEligible d :=
  priorityFive_subset _ _ (selectedLow_subset d)

theorem selectedNeighbors_card {n : ℕ} (d : Data n) (h : d.Good)
    (hL : (selectedLow d).card ≤ 2) : (selectedNeighbors d).card = 5 := by
  apply priorityFive_card _ _ (selectedLow_subset d)
  by_cases hs : d.A.card < d.B.card
  · simpa [selectedEligible, selectedLow, opposite, hs] using
      Good20.eligible d.graph h (by omega : d.A.card ≤ d.B.card)
        (by simpa [selectedLow, opposite, hs] using hL)
  · simpa [selectedEligible, selectedLow, opposite, hs] using
      Good20.eligible d.graph h.swap (by omega : d.B.card ≤ d.A.card)
        (by simpa [selectedLow, opposite, hs] using hL)

theorem selectedNeighbors_mandatory {n : ℕ} (d : Data n)
    (hL : (selectedLow d).card ≤ 2) : selectedLow d ⊆ selectedNeighbors d :=
  priorityFive_mandatory _ _ (by omega)

def nextA {n : ℕ} (d : Data n) : Finset (Option (Fin n)) :=
  if d.A.card < d.B.card then insert none (d.A.image some) else d.A.image some
def nextB {n : ℕ} (d : Data n) : Finset (Option (Fin n)) :=
  if d.A.card < d.B.card then d.B.image some else insert none (d.B.image some)

def step {n : ℕ} (d : Data n) : Data (n+1) where
  graph := (BqLowerFamily.extendGraph d.graph (selectedNeighbors d)).comap finSuccEquivLast
  decAdj := inferInstance
  A := relabelShore finSuccEquivLast (nextA d)
  B := relabelShore finSuccEquivLast (nextB d)

theorem step_good {n : ℕ} (d : Data n) (h : d.Good)
    (hL : (selectedLow d).card ≤ 2) : (step d).Good := by
  have hext : Good20 (BqLowerFamily.extendGraph d.graph (selectedNeighbors d))
      (nextA d) (nextB d) := by
    by_cases hs : d.A.card < d.B.card
    · have hNS : selectedNeighbors d ⊆ d.B.filter (fun v => d.graph.degree v ≤ 9) := by
        simpa [selectedEligible, opposite, hs] using selectedNeighbors_subset d
      have hh := Good20.extend d.graph h (selectedNeighbors d)
        (fun _ hv => (mem_filter.mp (hNS hv)).1) (selectedNeighbors_card d h hL)
        (fun _ hv => (mem_filter.mp (hNS hv)).2)
      simpa [nextA, nextB, hs] using hh
    · have hNS : selectedNeighbors d ⊆ d.A.filter (fun v => d.graph.degree v ≤ 9) := by
        simpa [selectedEligible, opposite, hs] using selectedNeighbors_subset d
      have hh := Good20.extend d.graph h.swap (selectedNeighbors d)
        (fun _ hv => (mem_filter.mp (hNS hv)).1) (selectedNeighbors_card d h hL)
        (fun _ hv => (mem_filter.mp (hNS hv)).2)
      simpa [nextA, nextB, hs] using hh.swap
  exact Good20.comap _ finSuccEquivLast hext

theorem step_degree_old {n : ℕ} (d : Data n) (v : Fin n) :
    (step d).graph.degree (Fin.castSucc v) =
      d.graph.degree v + if v ∈ selectedNeighbors d then 1 else 0 := by
  change ((BqLowerFamily.extendGraph d.graph (selectedNeighbors d)).comap
    finSuccEquivLast).degree (Fin.castSucc v) = _
  rw [← (SimpleGraph.Iso.comap finSuccEquivLast
    (BqLowerFamily.extendGraph d.graph (selectedNeighbors d))).degree_eq (Fin.castSucc v)]
  change (BqLowerFamily.extendGraph d.graph (selectedNeighbors d)).degree
    (finSuccEquivLast (Fin.castSucc v)) = _
  rw [finSuccEquivLast_castSucc, BqLowerFamily.degree_some]

theorem step_degree_new {n : ℕ} (d : Data n) :
    (step d).graph.degree (Fin.last n) = (selectedNeighbors d).card := by
  change ((BqLowerFamily.extendGraph d.graph (selectedNeighbors d)).comap
    finSuccEquivLast).degree (Fin.last n) = _
  rw [← (SimpleGraph.Iso.comap finSuccEquivLast
    (BqLowerFamily.extendGraph d.graph (selectedNeighbors d))).degree_eq (Fin.last n)]
  change (BqLowerFamily.extendGraph d.graph (selectedNeighbors d)).degree
    (finSuccEquivLast (Fin.last n)) = _
  rw [finSuccEquivLast_last, BqLowerFamily.degree_none]

theorem step_A_card {n : ℕ} (d : Data n) :
    (step d).A.card = d.A.card + if d.A.card < d.B.card then 1 else 0 := by
  unfold step relabelShore
  rw [card_image_of_injective _ finSuccEquivLast.symm.injective]
  by_cases hs : d.A.card < d.B.card <;>
    simp [nextA, hs, card_image_of_injective _ (Option.some_injective (Fin n))]

theorem step_B_card {n : ℕ} (d : Data n) :
    (step d).B.card = d.B.card + if d.A.card < d.B.card then 0 else 1 := by
  unfold step relabelShore
  rw [card_image_of_injective _ finSuccEquivLast.symm.injective]
  by_cases hs : d.A.card < d.B.card <;>
    simp [nextB, hs, card_image_of_injective _ (Option.some_injective (Fin n))]

def lowAll {n : ℕ} (d : Data n) : Finset (Fin n) := univ.filter fun v => d.graph.degree v = 5

/-- Literal steady state, starting only after the two low rows have been cleared. -/
structure Tail {n : ℕ} (d : Data n) : Prop where
  good : d.Good
  balance : d.A.card ≤ d.B.card ∧ d.B.card ≤ d.A.card+1
  low_opposite : ∀ v, d.graph.degree v = 5 → v ∈ opposite d
  low_card : (lowAll d).card ≤ 1

theorem Tail.low_le_two {n : ℕ} {d : Data n} (h : Tail d) : (selectedLow d).card ≤ 2 := by
  have hs : selectedLow d ⊆ lowAll d := by
    intro v hv
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hv).2⟩
  have hc := card_le_card hs
  have := h.low_card
  omega

theorem Tail.old_at_least_six {n : ℕ} {d : Data n} (h : Tail d) (v : Fin n) :
    6 ≤ (step d).graph.degree (Fin.castSucc v) := by
  rw [step_degree_old]
  have hd := (h.good.degrees v).1
  by_cases hv : d.graph.degree v = 5
  · have hl : v ∈ selectedLow d := mem_filter.mpr ⟨h.low_opposite v hv, hv⟩
    have hN := selectedNeighbors_mandatory d h.low_le_two hl
    simp [hN, hv]
  · split_ifs <;> omega

theorem Tail.new_opposite {n : ℕ} {d : Data n} (h : Tail d) :
    Fin.last n ∈ opposite (step d) := by
  have ha := step_A_card d
  have hb := step_B_card d
  by_cases hs : d.A.card < d.B.card
  · have hn : ¬ (step d).A.card < (step d).B.card := by
      simp only [hs, if_true] at ha hb
      have hbal := h.balance
      omega
    unfold opposite
    rw [if_neg hn]
    simp [step, nextA, hs, finSuccEquivLast]
  · have hn : (step d).A.card < (step d).B.card := by
      simp only [hs, if_false] at ha hb
      have hbal := h.balance
      omega
    unfold opposite
    rw [if_pos hn]
    simp [step, nextB, hs, finSuccEquivLast]

theorem Tail.advance {n : ℕ} {d : Data n} (h : Tail d) : Tail (step d) := by
  have hcard := selectedNeighbors_card d h.good h.low_le_two
  have hnew : (step d).graph.degree (Fin.last n) = 5 := by rw [step_degree_new, hcard]
  have honly (v : Fin (n+1)) : (step d).graph.degree v = 5 → v = Fin.last n := by
    refine Fin.lastCases (fun _ => rfl) (fun w hw => ?_) v
    have hd := h.old_at_least_six w
    omega
  refine ⟨step_good d h.good h.low_le_two, ?_, ?_, ?_⟩
  · rw [step_A_card, step_B_card]
    have hbal := h.balance
    split_ifs <;> omega
  · intro v hv
    rw [honly v hv]
    exact h.new_opposite
  · have hs : lowAll (step d) ⊆ {Fin.last n} := by
      intro v hv
      exact mem_singleton.mpr (honly v (mem_filter.mp hv).2)
    have hc := card_le_card hs
    simpa using hc

def start23 : Data 23 := step seedData
def start24 : Data 24 := step start23
def start25 : Data 25 := step start24

theorem start23_good : start23.Good := step_good seedData seedData_good (by decide)
theorem start24_good : start24.Good := step_good start23 start23_good (by decide)
theorem start25_good : start25.Good := step_good start24 start24_good (by decide)
theorem start25_tail : Tail start25 :=
  ⟨start25_good, by decide, by decide, by decide⟩

def emptyData (n : ℕ) : Data n where
  graph := ⊥
  decAdj := inferInstance
  A := ∅
  B := univ

def familyData : (n : ℕ) → Data n
  | 0 => emptyData 0
  | n+1 => if heq : n+1 = 22 then heq.symm ▸ seedData else
      if 22 ≤ n then step (familyData n) else emptyData (n+1)

@[simp] theorem familyData_twenty_two : familyData 22 = seedData := by rfl
@[simp] theorem familyData_twenty_three : familyData 23 = start23 := by rfl
@[simp] theorem familyData_twenty_four : familyData 24 = start24 := by rfl
@[simp] theorem familyData_twenty_five : familyData 25 = start25 := by rfl

theorem familyData_succ (n : ℕ) (hn : 22 ≤ n) :
    familyData (n+1) = step (familyData n) := by
  have hne : n+1 ≠ 22 := by omega
  rw [familyData]
  simp only [dif_neg hne, if_pos hn]

theorem familyData_tail (n : ℕ) (hn : 25 ≤ n) : Tail (familyData n) := by
  induction n, hn using Nat.le_induction with
  | base => exact start25_tail
  | succ n hn ih =>
    rw [familyData_succ n (by omega)]
    exact ih.advance

theorem familyData_good (n : ℕ) (hn : 22 ≤ n) : (familyData n).Good := by
  by_cases ht : 25 ≤ n
  · exact (familyData_tail n ht).good
  · have hs : n = 22 ∨ n = 23 ∨ n = 24 := by omega
    rcases hs with h | h | h <;> subst n
    · exact seedData_good
    · exact start23_good
    · exact start24_good

theorem familyData_low_le_two (n : ℕ) (hn : 22 ≤ n) :
    (selectedLow (familyData n)).card ≤ 2 := by
  by_cases ht : 25 ≤ n
  · exact (familyData_tail n ht).low_le_two
  · have hs : n = 22 ∨ n = 23 ∨ n = 24 := by omega
    rcases hs with h | h | h <;> subst n <;> decide

end Erdos585.Q6D20R31

import Mathlib

/-! Finite maximal families of actual disjoint b-leaf stars. -/
namespace Erdos642.CampaignFe72210b

variable {V : Type*} [DecidableEq V]

/-- Selected stars have distinct roots and pairwise disjoint leaves in disjoint shores. -/
structure PartialStarForest (G : SimpleGraph V) (A B : Finset V) (b : ℕ) where
  roots : Finset V
  leaves : V → Finset V
  roots_subset : roots ⊆ A
  leaves_subset : ∀ r ∈ roots, leaves r ⊆ B
  leaves_card : ∀ r ∈ roots, (leaves r).card = b
  adjacent : ∀ r ∈ roots, ∀ v ∈ leaves r, G.Adj r v
  leaves_disjoint : ∀ r ∈ roots, ∀ s ∈ roots, r ≠ s → Disjoint (leaves r) (leaves s)
  shores_disjoint : Disjoint A B

namespace PartialStarForest
variable {G : SimpleGraph V} {A B : Finset V} {b : ℕ}

def empty (hAB : Disjoint A B) : PartialStarForest G A B b where
  roots := ∅
  leaves := fun _ => ∅
  roots_subset := by simp
  leaves_subset := by simp
  leaves_card := by simp
  adjacent := by simp
  leaves_disjoint := by simp
  shores_disjoint := hAB

variable (F : PartialStarForest G A B b)

/-- The literal union of all selected leaves, with no multiplicity. -/
def usedLeaves : Finset V := F.roots.biUnion F.leaves

theorem leaf_subset_used (r : V) (hr : r ∈ F.roots) : F.leaves r ⊆ F.usedLeaves := by
  intro v hv
  exact Finset.mem_biUnion.mpr ⟨r, hr, hv⟩

theorem usedLeaves_subset : F.usedLeaves ⊆ B := by
  intro v hv
  obtain ⟨r, hr, hv⟩ := Finset.mem_biUnion.mp hv
  exact F.leaves_subset r hr hv

theorem usedLeaves_card : F.usedLeaves.card = F.roots.card * b := by
  have hd : (F.roots : Set V).PairwiseDisjoint F.leaves := by
    intro r hr s hs hne
    exact F.leaves_disjoint r hr s hs hne
  unfold usedLeaves
  rw [Finset.card_biUnion hd]
  calc
    _ = ∑ _r ∈ F.roots, b := by
      apply Finset.sum_congr rfl
      intro r hr
      exact F.leaves_card r hr
    _ = _ := by simp

variable [Fintype V] [DecidableRel G.Adj]

/-- Actual available neighbors in B, excluding every previously used leaf. -/
def freshNeighbors (r : V) : Finset V := (G.neighborFinset r ∩ B) \ F.usedLeaves

/-- A new actual b-leaf star can be added whenever its leaves are fresh. -/
def extend (r : V) (hrA : r ∈ A) (_hr : r ∉ F.roots) (T : Finset V)
    (hT : T ⊆ F.freshNeighbors r) (hcard : T.card = b) : PartialStarForest G A B b := by
  have hTB : T ⊆ B := by
    intro v hv
    exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp (hT hv)).1).2
  have hAdj : ∀ v ∈ T, G.Adj r v := by
    intro v hv
    exact (G.mem_neighborFinset r v).mp
      (Finset.mem_inter.mp (Finset.mem_sdiff.mp (hT hv)).1).1
  have hdis : ∀ s ∈ F.roots, Disjoint T (F.leaves s) := by
    intro s hs
    apply Finset.disjoint_left.mpr
    intro v hvT hvL
    exact (Finset.mem_sdiff.mp (hT hvT)).2 (F.leaf_subset_used s hs hvL)
  refine {
    roots := insert r F.roots
    leaves := Function.update F.leaves r T
    roots_subset := ?_
    leaves_subset := ?_
    leaves_card := ?_
    adjacent := ?_
    leaves_disjoint := ?_
    shores_disjoint := F.shores_disjoint }
  · intro s hs
    rcases Finset.mem_insert.mp hs with h | h
    · simpa [h] using hrA
    · exact F.roots_subset h
  · intro s hs
    by_cases h : s = r
    · subst s
      simpa using hTB
    · have hs' : s ∈ F.roots := (Finset.mem_insert.mp hs).resolve_left h
      simpa [Function.update_of_ne h] using F.leaves_subset s hs'
  · intro s hs
    by_cases h : s = r
    · subst s
      simpa using hcard
    · have hs' : s ∈ F.roots := (Finset.mem_insert.mp hs).resolve_left h
      simpa [Function.update_of_ne h] using F.leaves_card s hs'
  · intro s hs v hv
    by_cases h : s = r
    · subst s
      exact hAdj v (by simpa using hv)
    · have hs' : s ∈ F.roots := (Finset.mem_insert.mp hs).resolve_left h
      exact F.adjacent s hs' v (by simpa [Function.update_of_ne h] using hv)
  · intro s hs t ht hst
    by_cases hs' : s = r
    · subst s
      have ht' : t ≠ r := Ne.symm hst
      have htold : t ∈ F.roots := (Finset.mem_insert.mp ht).resolve_left ht'
      simpa [Function.update_of_ne ht'] using hdis t htold
    · by_cases ht' : t = r
      · subst t
        have hsold : s ∈ F.roots := (Finset.mem_insert.mp hs).resolve_left hs'
        simpa [Function.update_of_ne hs'] using (hdis s hsold).symm
      · have hsold : s ∈ F.roots := (Finset.mem_insert.mp hs).resolve_left hs'
        have htold : t ∈ F.roots := (Finset.mem_insert.mp ht).resolve_left ht'
        simpa [Function.update_of_ne hs', Function.update_of_ne ht'] using
          F.leaves_disjoint s hsold t htold hst

theorem extend_roots_card (r : V) (hrA : r ∈ A) (hr : r ∉ F.roots) (T : Finset V)
    (hT : T ⊆ F.freshNeighbors r) (hcard : T.card = b) :
    (F.extend r hrA hr T hT hcard).roots.card = F.roots.card + 1 := by
  change (insert r F.roots).card = _
  exact Finset.card_insert_of_notMem hr

/-- An unused root in a maximal actual forest has fewer than b fresh neighbors. -/
theorem freshNeighbors_card_lt_of_maximal
    (hmax : ∀ F' : PartialStarForest G A B b, F'.roots.card ≤ F.roots.card)
    (r : V) (hrA : r ∈ A) (hr : r ∉ F.roots) : (F.freshNeighbors r).card < b := by
  by_contra h
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt h)
  have hbound := hmax (F.extend r hrA hr T hT hcard)
  rw [F.extend_roots_card] at hbound
  omega

end PartialStarForest

variable [Fintype V]

/-- Maximality comes from a finite maximum over genuine root-and-leaf data. -/
theorem exists_maximal_partial_star_forest (G : SimpleGraph V) (A B : Finset V) (b : ℕ)
    (hAB : Disjoint A B) :
    ∃ F : PartialStarForest G A B b,
      ∀ F' : PartialStarForest G A B b, F'.roots.card ≤ F.roots.card := by
  classical
  let candidates : Finset (Finset V × (V → Finset V)) :=
    Finset.univ.filter fun d => ∃ F : PartialStarForest G A B b, (F.roots, F.leaves) = d
  have hne : candidates.Nonempty := by
    refine ⟨(∅, fun _ => ∅), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨PartialStarForest.empty hAB, rfl⟩
  obtain ⟨data, hdata, hmax⟩ := Finset.exists_max_image candidates
    (fun d => d.1.card) hne
  obtain ⟨F, rfl⟩ := (Finset.mem_filter.mp hdata).2
  refine ⟨F, ?_⟩
  intro F'
  have hmem : (F'.roots, F'.leaves) ∈ candidates := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, F', rfl⟩
  exact hmax (F'.roots, F'.leaves) hmem

/-- A literal maximal forest and its exact used-leaf count and extension obstruction. -/
theorem exists_partial_star_forest_fresh_obstruction (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (b : ℕ) (hAB : Disjoint A B) :
    ∃ F : PartialStarForest G A B b,
      (∀ F' : PartialStarForest G A B b, F'.roots.card ≤ F.roots.card) ∧
      F.usedLeaves.card = F.roots.card * b ∧
      ∀ r ∈ A, r ∉ F.roots → (F.freshNeighbors r).card < b := by
  obtain ⟨F, hmax⟩ := exists_maximal_partial_star_forest G A B b hAB
  exact ⟨F, hmax, F.usedLeaves_card, F.freshNeighbors_card_lt_of_maximal hmax⟩

end Erdos642.CampaignFe72210b

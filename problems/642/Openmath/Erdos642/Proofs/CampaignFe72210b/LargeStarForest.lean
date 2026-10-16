import Openmath.Erdos642.Proofs.CampaignFe72210b.MaximalStarForest
import Openmath.Erdos642.Proofs.CampaignFe72210b.IncidenceCounts

/-! Actual degree and incidence counts force many disjoint selected stars. -/
namespace Erdos642.CampaignFe72210b

variable {V : Type*} [DecidableEq V]
namespace PartialStarForest
variable {G : SimpleGraph V} {A B : Finset V} {b : ℕ}
variable (F : PartialStarForest G A B b)

/-- Restricting selected roots preserves the same actual leaf stars. -/
def restrictRoots (R : Finset V) (hR : R ⊆ F.roots) : PartialStarForest G A B b where
  roots := R
  leaves := F.leaves
  roots_subset := hR.trans F.roots_subset
  leaves_subset := fun r hr => F.leaves_subset r (hR hr)
  leaves_card := fun r hr => F.leaves_card r (hR hr)
  adjacent := fun r hr => F.adjacent r (hR hr)
  leaves_disjoint := fun r hr s hs => F.leaves_disjoint r (hR hr) s (hR hs)
  shores_disjoint := F.shores_disjoint

omit [DecidableEq V] in
/-- Exact selected-root size gives literal indexed root/leaf data. -/
theorem indexed_of_roots_card_eq (m : ℕ) (hm : F.roots.card = m) :
    ∃ root : Fin m → V, ∃ leaves : Fin m → Finset V,
      Function.Injective root ∧
      (∀ j, root j ∈ A) ∧
      (∀ j, leaves j ⊆ B) ∧
      (∀ j, (leaves j).card = b) ∧
      (∀ j v, v ∈ leaves j → G.Adj (root j) v) ∧
      (∀ j k, j ≠ k → Disjoint (leaves j) (leaves k)) := by
  classical
  let e := F.roots.equivFinOfCardEq hm
  have hinj : Function.Injective (fun j : Fin m => (e.symm j).val) := by
    intro j k h
    exact e.symm.injective (Subtype.ext h)
  refine ⟨fun j => (e.symm j).val, fun j => F.leaves (e.symm j).val,
    hinj, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact F.roots_subset (e.symm j).property
  · intro j
    exact F.leaves_subset _ (e.symm j).property
  · intro j
    exact F.leaves_card _ (e.symm j).property
  · intro j v hv
    exact F.adjacent _ (e.symm j).property v hv
  · intro j k hne
    exact F.leaves_disjoint _ (e.symm j).property _ (e.symm k).property
      (fun h => hne (hinj h))

variable [Fintype V] [DecidableRel G.Adj]

/-- Actual neighbors split exactly into fresh neighbors and already used leaves. -/
theorem degree_eq_fresh_add_used (r : V)
    (hcover : G.neighborFinset r ⊆ B) :
    G.degree r = (F.freshNeighbors r).card + (F.usedLeaves.filter (G.Adj r)).card := by
  have hn : G.neighborFinset r ∩ B = G.neighborFinset r := Finset.inter_eq_left.mpr hcover
  have hu : F.usedLeaves.filter (G.Adj r) = G.neighborFinset r ∩ F.usedLeaves := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_inter, G.mem_neighborFinset]
    tauto
  rw [← G.card_neighborFinset_eq_degree, freshNeighbors, hn, hu]
  exact (Finset.card_sdiff_add_card_inter _ _).symm

/-- Maximality and literal degree bounds force a large selected-root set. -/
theorem roots_card_ge_of_degree_criterion
    (hmax : ∀ F' : PartialStarForest G A B b, F'.roots.card ≤ F.roots.card)
    (m D : ℕ) (δ : ℝ)
    (hcover : ∀ r ∈ A, G.neighborFinset r ⊆ B)
    (hδ : ∀ r ∈ A, δ ≤ (G.degree r : ℝ))
    (hD : ∀ v ∈ B, G.degree v ≤ D)
    (hnum : ∀ f : ℕ, f < m → f ≤ A.card →
      (D : ℝ) * (f : ℝ) * (b : ℝ) <
        ((A.card : ℝ) - (f : ℝ)) * (δ - (b : ℝ))) :
    m ≤ F.roots.card := by
  have hlocal : ∀ r ∈ A \ F.roots,
      δ - (b : ℝ) ≤ ((F.usedLeaves.filter (G.Adj r)).card : ℝ) := by
    intro r hr
    obtain ⟨hrA, hrnot⟩ := Finset.mem_sdiff.mp hr
    have hsplit := F.degree_eq_fresh_add_used r (hcover r hrA)
    have hsplit' : (G.degree r : ℝ) = ((F.freshNeighbors r).card : ℝ) +
        ((F.usedLeaves.filter (G.Adj r)).card : ℝ) := by exact_mod_cast hsplit
    have hfresh := F.freshNeighbors_card_lt_of_maximal hmax r hrA hrnot
    have hfresh' : ((F.freshNeighbors r).card : ℝ) < (b : ℝ) := by exact_mod_cast hfresh
    have hdegree := hδ r hrA
    linarith
  have hlower : ((A \ F.roots).card : ℝ) * (δ - (b : ℝ)) ≤
      (IncidenceCounts.count G (A \ F.roots) F.usedLeaves : ℝ) := by
    unfold IncidenceCounts.count
    rw [Nat.cast_sum]
    calc
      _ = ∑ _r ∈ A \ F.roots, (δ - (b : ℝ)) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum hlocal
  have hupperNat := IncidenceCounts.count_le_card_mul G (A \ F.roots) F.usedLeaves D
    (fun v hv => hD v (F.usedLeaves_subset hv))
  rw [F.usedLeaves_card] at hupperNat
  have hupper : (IncidenceCounts.count G (A \ F.roots) F.usedLeaves : ℝ) ≤
      (F.roots.card : ℝ) * (b : ℝ) * (D : ℝ) := by exact_mod_cast hupperNat
  have hcardNat : (A \ F.roots).card + F.roots.card = A.card := by
    simpa only [Finset.union_eq_left.mpr F.roots_subset] using
      Finset.card_sdiff_add_card A F.roots
  have hcard : ((A \ F.roots).card : ℝ) = (A.card : ℝ) - (F.roots.card : ℝ) := by
    have h' : ((A \ F.roots).card : ℝ) + (F.roots.card : ℝ) = (A.card : ℝ) := by
      exact_mod_cast hcardNat
    linarith
  rw [hcard] at hlower
  have hbound : ((A.card : ℝ) - (F.roots.card : ℝ)) * (δ - (b : ℝ)) ≤
      (D : ℝ) * (F.roots.card : ℝ) * (b : ℝ) := by
    calc
      _ ≤ _ := hlower.trans hupper
      _ = _ := by ring
  by_contra h
  have hsmall : F.roots.card < m := Nat.lt_of_not_ge h
  have hsize : F.roots.card ≤ A.card := Finset.card_le_card F.roots_subset
  exact (not_lt_of_ge hbound) (hnum F.roots.card hsmall hsize)

end PartialStarForest

variable [Fintype V]

/-- The degree and scalar premises produce actual stars, without an incidence premise. -/
theorem exists_large_partial_star_forest (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (b m D : ℕ) (δ : ℝ) (hAB : Disjoint A B)
    (hcover : ∀ r ∈ A, G.neighborFinset r ⊆ B)
    (hδ : ∀ r ∈ A, δ ≤ (G.degree r : ℝ))
    (hD : ∀ v ∈ B, G.degree v ≤ D)
    (hnum : ∀ f : ℕ, f < m → f ≤ A.card →
      (D : ℝ) * (f : ℝ) * (b : ℝ) <
        ((A.card : ℝ) - (f : ℝ)) * (δ - (b : ℝ))) :
    ∃ F : PartialStarForest G A B b, m ≤ F.roots.card := by
  obtain ⟨F, hmax⟩ := exists_maximal_partial_star_forest G A B b hAB
  exact ⟨F, F.roots_card_ge_of_degree_criterion hmax m D δ hcover hδ hD hnum⟩

/-- Selecting an exact root subset retains actual disjoint b-leaf stars. -/
theorem exists_exact_partial_star_forest (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (b m D : ℕ) (δ : ℝ) (hAB : Disjoint A B)
    (hcover : ∀ r ∈ A, G.neighborFinset r ⊆ B)
    (hδ : ∀ r ∈ A, δ ≤ (G.degree r : ℝ))
    (hD : ∀ v ∈ B, G.degree v ≤ D)
    (hnum : ∀ f : ℕ, f < m → f ≤ A.card →
      (D : ℝ) * (f : ℝ) * (b : ℝ) <
        ((A.card : ℝ) - (f : ℝ)) * (δ - (b : ℝ))) :
    ∃ F : PartialStarForest G A B b, F.roots.card = m := by
  obtain ⟨F, hlarge⟩ := exists_large_partial_star_forest G A B b m D δ hAB hcover hδ hD hnum
  obtain ⟨R, hR, hcard⟩ := Finset.exists_subset_card_eq hlarge
  exact ⟨F.restrictRoots R hR, hcard⟩

end Erdos642.CampaignFe72210b

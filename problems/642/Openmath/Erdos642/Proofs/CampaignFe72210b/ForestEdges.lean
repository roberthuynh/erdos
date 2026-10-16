import Openmath.Erdos642.Proofs.CampaignFe72210b.ForestBundle
import Openmath.Erdos642.Proofs.CampaignFe72210b.CycleSupport

/-! Distinct literal host edges selected from a star-forest bundle. -/
namespace Erdos642.CampaignFe72210b.ForestBundle
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {A B : Finset V} {q m b : ℕ}
variable (F : ForestBundle G A B q m b)

def selectedPairs (L R : Finset V) : Finset (Σ _i : Fin q × Fin m, V) :=
  Finset.univ.sigma fun i => (F.leaves i).filter fun v => F.root i ∈ R ∧ v ∈ L

def selectedEdges (L R : Finset V) : Finset (Sym2 V) :=
  (F.selectedPairs L R).image fun z => s(F.root z.1, z.2)

theorem selected_edge_injective (L R : Finset V) :
    Set.InjOn (fun z : (Σ _i : Fin q × Fin m, V) => s(F.root z.1, z.2))
      (F.selectedPairs L R : Set _) := by
  intro z hz w hw he
  have hzleaf : z.2 ∈ F.leaves z.1 := (Finset.mem_filter.mp (Finset.mem_sigma.mp hz).2).1
  have hwleaf : w.2 ∈ F.leaves w.1 := (Finset.mem_filter.mp (Finset.mem_sigma.mp hw).2).1
  rcases Sym2.eq_iff.mp he with h | h
  · have hi := F.root_injective h.1
    cases z with
    | mk i v =>
      cases w with
      | mk j u =>
        dsimp at hi h
        subst j
        simp_all
  · have hrA := F.root_mem z.1
    have hwB := F.leaves_subset w.1 hwleaf
    rw [← h.1] at hwB
    exact False.elim (Finset.disjoint_left.mp F.shores_disjoint hrA hwB)

theorem selectedEdges_card (L R : Finset V) :
    (F.selectedEdges L R).card = (F.selectedPairs L R).card := by
  exact Finset.card_image_iff.mpr (F.selected_edge_injective L R)

theorem selectedEdges_subset_support {u v : V} (p : G.Walk u v)
    (L R : Finset V) (hL : ∀ x ∈ L, x ∈ p.support) (hR : ∀ x ∈ R, x ∈ p.support) :
    F.selectedEdges L R ⊆ supportEdges p := by
  intro e he
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
  have hz' := Finset.mem_filter.mp (Finset.mem_sigma.mp hz).2
  exact (mem_supportEdges p _ _).mpr
    ⟨F.adjacent z.1 z.2 hz'.1, hR _ hz'.2.1, hL _ hz'.2.2⟩

theorem indicator_weightedCount_eq_card (L R : Finset V) :
    F.weightedCount (fun v => if v ∈ L then 1 else 0)
      (fun v => if v ∈ R then 1 else 0) = ((F.selectedEdges L R).card : ℝ) := by
  rw [F.selectedEdges_card]
  unfold weightedCount selectedPairs
  rw [Finset.card_sigma, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hr : F.root i ∈ R
  · simp [hr, Finset.card_filter, Nat.cast_sum]
  · simp [hr]

end Erdos642.CampaignFe72210b.ForestBundle

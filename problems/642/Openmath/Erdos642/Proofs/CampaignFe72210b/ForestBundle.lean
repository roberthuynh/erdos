import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Tactic

/-! Literal finite star-forest data. Existence is a separate obligation. -/
namespace Erdos642.CampaignFe72210b

variable {V : Type*} [DecidableEq V]

/-- Roots are globally distinct; leaves need only be disjoint within each forest. -/
structure ForestBundle (G : SimpleGraph V) (A B : Finset V) (q m b : ℕ) where
  root : Fin q × Fin m → V
  leaves : Fin q × Fin m → Finset V
  root_mem : ∀ i, root i ∈ A
  leaves_subset : ∀ i, leaves i ⊆ B
  leaves_card : ∀ i, (leaves i).card = b
  adjacent : ∀ i v, v ∈ leaves i → G.Adj (root i) v
  root_injective : Function.Injective root
  leaves_disjoint : ∀ f j k, j ≠ k → Disjoint (leaves (f,j)) (leaves (f,k))
  shores_disjoint : Disjoint A B

namespace ForestBundle
variable {G : SimpleGraph V} {A B : Finset V} {q m b : ℕ}
variable (F : ForestBundle G A B q m b)

def roots (J : Finset (Fin q × Fin m)) : Finset V := J.image F.root

theorem roots_card (J : Finset (Fin q × Fin m)) : (F.roots J).card = J.card := by
  exact Finset.card_image_of_injective _ F.root_injective

theorem roots_subset (J : Finset (Fin q × Fin m)) : F.roots J ⊆ A := by
  intro v hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
  exact F.root_mem i

theorem sum_roots (J : Finset (Fin q × Fin m)) (w : V → ℝ) :
    (∑ v ∈ F.roots J, w v) = ∑ i ∈ J, w (F.root i) := by
  exact Finset.sum_image (fun i _ j _ h => F.root_injective h)

/-- Counts may have multiplicity. No self-avoidance or probability premise is used. -/
def weightedCount (L R : V → ℝ) : ℝ :=
  ∑ i, R (F.root i) * ∑ v ∈ F.leaves i, L v

/-- Good stars give a literal weighted lower bound through their distinct roots. -/
theorem weightedCount_lower (L R : V → ℝ) (hL : ∀ v, 0 ≤ L v)
    (hR : ∀ v, 0 ≤ R v) (a : ℝ) (J : Finset (Fin q × Fin m))
    (hgood : ∀ i ∈ J, a ≤ ∑ v ∈ F.leaves i, L v) :
    a * (∑ v ∈ F.roots J, R v) ≤ F.weightedCount L R := by
  rw [F.sum_roots, Finset.mul_sum]
  calc
    (∑ i ∈ J, a * R (F.root i)) ≤
        ∑ i ∈ J, R (F.root i) * ∑ v ∈ F.leaves i, L v := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hgood i hi) (hR _)
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
      intro i _ _
      exact mul_nonneg (hR _) (Finset.sum_nonneg fun v _ => hL v)

end ForestBundle
end Erdos642.CampaignFe72210b

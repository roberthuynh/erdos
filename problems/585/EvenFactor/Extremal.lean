import EvenFactor.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Finset SimpleGraph
namespace Erdos585.EvenFactorCriterion
universe u
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def oddRemaining (X : Finset V) : ℕ :=
  ((⊤ : G.Subgraph).deleteVerts (X : Set V)).coe.oddComponents.ncard

def gadgetDeficiency (X : Finset V) : ℤ :=
  (oddRemaining G X : ℤ) - #X

def ExtremalDeletion (X : Finset V) : Prop :=
  (∀ Y : Finset V, gadgetDeficiency G Y ≤ gadgetDeficiency G X) ∧
  (∀ Y : Finset V, gadgetDeficiency G Y = gadgetDeficiency G X → #X ≤ #Y)

/-- Both optimizations use actual finite vertex deletion sets. -/
theorem exists_extremal_deletion : ∃ X : Finset V, ExtremalDeletion G X := by
  classical
  obtain ⟨X, _, hmax⟩ := exists_max_image (univ : Finset (Finset V))
    (gadgetDeficiency G) univ_nonempty
  let candidates : Finset (Finset V) :=
    univ.filter (fun Y => gadgetDeficiency G Y = gadgetDeficiency G X)
  have hX : X ∈ candidates := by simp [candidates]
  obtain ⟨Y, hY, hmin⟩ := exists_min_image candidates Finset.card ⟨X, hX⟩
  have he : gadgetDeficiency G Y = gadgetDeficiency G X := (mem_filter.mp hY).2
  refine ⟨Y, ?_, ?_⟩
  · intro Z
    rw [he]
    exact hmax Z (mem_univ Z)
  · intro Z hZ
    exact hmin Z (by simp [candidates, hZ, he])

lemma positive_deficiency_iff (X : Finset V) :
    0 < gadgetDeficiency G X ↔ G.IsTutteViolator (X : Set V) := by
  unfold gadgetDeficiency oddRemaining SimpleGraph.IsTutteViolator
  rw [Set.ncard_coe_finset]
  omega

/-- Mathlib's proven matching criterion produces an actual deletion set. -/
theorem exists_positive_extremal
    (hno : ¬ ∃ M : G.Subgraph, M.IsPerfectMatching) :
    ∃ X : Finset V, ExtremalDeletion G X ∧ 0 < gadgetDeficiency G X := by
  classical
  have hh : ¬ ∀ s : Set V, ¬ G.IsTutteViolator s := by
    intro hs
    exact hno ((SimpleGraph.tutte (G := G)).mpr hs)
  push_neg at hh
  obtain ⟨s, hs⟩ := hh
  obtain ⟨X, hX⟩ := exists_extremal_deletion G
  refine ⟨X, hX, ?_⟩
  have hp : 0 < gadgetDeficiency G s.toFinset :=
    (positive_deficiency_iff G s.toFinset).mpr (by simpa using hs)
  exact lt_of_lt_of_le hp (hX.1 _)

/-- A smaller deletion cannot preserve the maximizing signed deficiency. -/
theorem extremal_erase_strict (X : Finset V) (hX : ExtremalDeletion G X)
    (v : V) (hv : v ∈ X) :
    gadgetDeficiency G (X.erase v) < gadgetDeficiency G X := by
  have hle := hX.1 (X.erase v)
  apply lt_of_le_of_ne hle
  intro he
  have hm := hX.2 (X.erase v) he
  exact (not_le.mpr (card_erase_lt_of_mem hv)) hm

end Erdos585.EvenFactorCriterion

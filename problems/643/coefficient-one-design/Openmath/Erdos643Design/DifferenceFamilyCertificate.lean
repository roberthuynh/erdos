import Openmath.Erdos643Design.DifferenceFamilyDesign

/-! Efficient exact finite certificates for supplied difference families. -/
set_option autoImplicit false

namespace Erdos643Design.DifferenceFamily
open Finset
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Enumerate only ordered pairs of actual points inside actual base blocks. -/
def smallWitnesses (base : Finset (Finset G)) (d : G) :
    Finset (Finset G × G × G) :=
  (base.biUnion (fun B => (B ×ˢ B).image (fun xy => (B,xy)))).filter
    (fun w => w.2.1 - w.2.2 = d)

omit [Fintype G] in
@[simp] theorem mem_smallWitnesses (base : Finset (Finset G)) (d : G)
    (B : Finset G) (x y : G) :
    (B,x,y) ∈ smallWitnesses base d ↔ B ∈ base ∧ x ∈ B ∧ y ∈ B ∧ x-y = d := by
  simp [smallWitnesses, and_assoc]

/-- The smaller enumeration has exactly the same witness triples. -/
theorem smallWitnesses_eq (base : Finset (Finset G)) (d : G) :
    smallWitnesses base d = witnesses base d := by
  ext ⟨B,x,y⟩
  rw [mem_smallWitnesses, mem_witnesses]

/-- Exact finite cardinal certificates supply the unique-difference property. -/
def Supplied.of_small_counts {k : ℕ} (base : Finset (Finset G))
    (uniform : base.IsUniform k)
    (counts : ∀ d : G, d ≠ 0 → (smallWitnesses base d).card = 1) :
    Supplied G k where
  base := base
  uniform := uniform
  unique_difference := by
    intro d hd
    have hc : (witnesses base d).card = 1 := by
      rw [← smallWitnesses_eq]
      exact counts d hd
    obtain ⟨w,hw⟩ := card_eq_one.mp hc
    refine ⟨w, ?_, ?_⟩
    · rw [hw]
      exact mem_singleton_self w
    · intro z hz
      rw [hw] at hz
      exact mem_singleton.mp hz

end Erdos643Design.DifferenceFamily

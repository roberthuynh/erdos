import GadgetNormalization.Local

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open SimpleGraph Finset Set
namespace Erdos585.GadgetNormalization
open EvenFactorCriterion FactorMatching
universe u
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]

def saturatedSlots (X : Finset (Vertex q G)) : Finset V :=
  univ.filter (fun v => ∀ i : Fin q, Sum.inl (v,i) ∈ X)

def saturatedStubs (X : Finset (Vertex q G)) : Finset V :=
  univ.filter (fun v => ∀ d : G.Dart, d.fst = v → Sum.inr d ∈ X)

/-- The returned sets are selectors on the original carrier, not supplied masks. -/
theorem extremal_canonical (hq : 0 < q) (hdeg : ∀ v : V, q ≤ G.degree v)
    (X : Finset (Vertex q G)) (hX : ExtremalDeletion (gadget q G) X) :
    ∃ S T : Finset V, Disjoint S T ∧
      (∀ (v : V) (i : Fin q), Sum.inl (v,i) ∈ X ↔ v ∈ S) ∧
      (∀ d : G.Dart, Sum.inr d ∈ X ↔ d.fst ∈ T) := by
  let S := saturatedSlots q G X
  let T := saturatedStubs q G X
  have hS (v : V) : v ∈ S ↔ ∀ i : Fin q, Sum.inl (v,i) ∈ X := by
    simp [S,saturatedSlots]
  have hT (v : V) : v ∈ T ↔ ∀ d : G.Dart, d.fst = v → Sum.inr d ∈ X := by
    simp [T,saturatedStubs]
  refine ⟨S,T, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hvS hvT
    obtain ⟨w,hvw⟩ := (G.degree_pos_iff_exists_adj v).mp (lt_of_lt_of_le hq (hdeg v))
    let d : G.Dart := ⟨(v,w),hvw⟩
    have hdT : Sum.inr d ∈ X := (hT v).mp hvT d rfl
    have hdS : Sum.inr d ∉ X := stub_not_deleted_of_slots_deleted q G X hX d
      (by simpa [d] using (hS v).mp hvS)
    exact hdS hdT
  · intro v i
    rw [hS v]
    constructor
    · intro hi j
      exact (slot_uniform q G X hX v i j).mp hi
    · intro hall
      exact hall i
  · intro d
    rw [hT d.fst]
    constructor
    · intro hd e he
      exact (stub_uniform q G hq X hX d e he).mp hd
    · intro hall
      exact hall d rfl

/-- A version returning the explicit internally derived original selectors. -/
theorem extremal_saturated (hq : 0 < q) (hdeg : ∀ v : V, q ≤ G.degree v)
    (X : Finset (Vertex q G)) (hX : ExtremalDeletion (gadget q G) X) :
    Disjoint (saturatedSlots q G X) (saturatedStubs q G X) ∧
      (∀ (v : V) (i : Fin q), Sum.inl (v,i) ∈ X ↔ v ∈ saturatedSlots q G X) ∧
      (∀ d : G.Dart, Sum.inr d ∈ X ↔ d.fst ∈ saturatedStubs q G X) := by
  obtain ⟨S,T,hdis,hS,hT⟩ := extremal_canonical q G hq hdeg X hX
  have hSE : S = saturatedSlots q G X := by
    ext v
    simp only [saturatedSlots, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hv i
      exact (hS v i).mpr hv
    · intro hi
      exact (hS v ⟨0,hq⟩).mp (hi ⟨0,hq⟩)
  have hTE : T = saturatedStubs q G X := by
    ext v
    simp only [saturatedStubs, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hv d hd
      exact (hT d).mpr (hd ▸ hv)
    · intro hall
      obtain ⟨w,hvw⟩ := (G.degree_pos_iff_exists_adj v).mp (lt_of_lt_of_le hq (hdeg v))
      let d : G.Dart := ⟨(v,w),hvw⟩
      exact (hT d).mp (hall d rfl)
  simpa [hSE,hTE] using And.intro hdis (And.intro hS hT)

end Erdos585.GadgetNormalization

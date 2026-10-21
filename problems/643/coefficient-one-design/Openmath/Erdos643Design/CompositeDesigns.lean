import Openmath.Erdos643Design.CompositeRows
import Openmath.Erdos643Design.SharedPointFill
import Openmath.Erdos643Design.WeightedPairwiseConstruction
import Openmath.Erdos643Design.DesignTransport
import Openmath.Erdos643Design.TDCompositeSeeds

/-! Exact design existence preserved through composite finite constructions. -/
set_option autoImplicit false
namespace Erdos643Design.CompositeSeeds
open Foundation
noncomputable section

/-- Fill each group and a common new point using an actual design of order `m+1`. -/
theorem sharedPoint {m : ℕ} (T : TransversalRows (Fin 5) (Fin m))
    (h : ∃ B : Finset (Finset (Fin (m+1))), B.IsBlockDesign 2 5) :
    ∃ B : Finset (Finset (Fin (5*m+1))), B.IsBlockDesign 2 5 := by
  obtain ⟨B,hB⟩ := h
  let e : Fin (m+1) ≃ Option (Fin m) :=
    (Fintype.equivFinOfCardEq (by simp)).symm
  let C := DesignTransport.relabel e B
  have hC : C.IsBlockDesign 2 (Fintype.card (Fin 5)) :=
    DesignTransport.isBlockDesign_relabel e B 2 5 hB
  let g : Option (Fin 5 × Fin m) ≃ Fin (5*m+1) :=
    Fintype.equivFinOfCardEq (by simp)
  exact ⟨DesignTransport.relabel g (SharedPoint.blocks T C),
    DesignTransport.isBlockDesign_relabel g _ 2 5 (SharedPoint.isBlockDesign T C hC)⟩

/-- Fill all five groups of an actual transversal using the same actual local design. -/
theorem groupFill {m : ℕ} (T : TransversalRows (Fin 5) (Fin m))
    (h : ∃ B : Finset (Finset (Fin m)), B.IsBlockDesign 2 5) :
    ∃ B : Finset (Finset (Fin (5*m))), B.IsBlockDesign 2 5 := by
  obtain ⟨B,hB⟩ := h
  let C := (fromTransversal T (fillFromDesigns (fun _ => B) (fun _ => hB))).completed
  have hC : C.IsBlockDesign 2 5 := transversal_and_block_designs T (fun _ => B) (fun _ => hB)
  let e : Fin 5 × Fin m ≃ Fin (5*m) := Fintype.equivFinOfCardEq (by simp)
  exact ⟨DesignTransport.relabel e C,DesignTransport.isBlockDesign_relabel e C 2 5 hC⟩

/-- A five-uniform actual design is a PBD whose weight-four local ingredient has order21. -/
theorem weighted {v : ℕ}
    (h : ∃ B : Finset (Finset (Fin v)), B.IsBlockDesign 2 5)
    (h21 : ∃ B : Finset (Finset (Fin 21)), B.IsBlockDesign 2 5) :
    ∃ B : Finset (Finset (Fin (4*v+1))), B.IsBlockDesign 2 5 := by
  obtain ⟨B,hB⟩ := h
  have hp : B.IsPairwiseBalancedDesign := ⟨by intro b hb; rw [hB.1 b hb]; decide,hB.2⟩
  have hl : ∀ b ∈ B, ∃ D : Finset (Finset (Fin (4*b.card+1))), D.IsBlockDesign 2 5 := by
    intro b hb
    rw [hB.1 b hb]
    exact h21
  have hh := WeightedPairwiseConstruction.exists_design_fin B hp hl
  have hc : Fintype.card (Fin v) = v := Fintype.card_fin v
  rw [hc] at hh
  exact hh

theorem design165_of_41_21
    (h41 : ∃ B : Finset (Finset (Fin 41)), B.IsBlockDesign 2 5)
    (h21 : ∃ B : Finset (Finset (Fin 21)), B.IsBlockDesign 2 5) :
    ∃ B : Finset (Finset (Fin 165)), B.IsBlockDesign 2 5 := weighted h41 h21

theorem design181_of_45_21
    (h45 : ∃ B : Finset (Finset (Fin 45)), B.IsBlockDesign 2 5)
    (h21 : ∃ B : Finset (Finset (Fin 21)), B.IsBlockDesign 2 5) :
    ∃ B : Finset (Finset (Fin 181)), B.IsBlockDesign 2 5 := weighted h45 h21

theorem design201_of_41 (h41 : ∃ B : Finset (Finset (Fin 41)), B.IsBlockDesign 2 5) :
    ∃ B : Finset (Finset (Fin 201)), B.IsBlockDesign 2 5 := sharedPoint td5_40 h41

theorem design301_of_61 (h61 : ∃ B : Finset (Finset (Fin 61)), B.IsBlockDesign 2 5) :
    ∃ B : Finset (Finset (Fin 301)), B.IsBlockDesign 2 5 :=
  sharedPoint TDCompositeSeeds.rows60 h61

theorem design421_of_85 (h85 : ∃ B : Finset (Finset (Fin 85)), B.IsBlockDesign 2 5) :
    ∃ B : Finset (Finset (Fin 421)), B.IsBlockDesign 2 5 := by
  obtain ⟨T⟩ := TDCompositeSeeds.exists_rows84
  exact sharedPoint T h85

theorem design401_of_81 (h81 : ∃ B : Finset (Finset (Fin 81)), B.IsBlockDesign 2 5) :
    ∃ B : Finset (Finset (Fin 401)), B.IsBlockDesign 2 5 := sharedPoint td5_80 h81

theorem design425_of_85 (h85 : ∃ B : Finset (Finset (Fin 85)), B.IsBlockDesign 2 5) :
    ∃ B : Finset (Finset (Fin 425)), B.IsBlockDesign 2 5 := groupFill td5_85 h85
end
end Erdos643Design.CompositeSeeds

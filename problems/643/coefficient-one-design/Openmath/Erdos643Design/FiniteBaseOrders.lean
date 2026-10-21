import Openmath.Erdos643Design.HananiAssembly
import Openmath.Erdos643Design.DesignSeed21
import Openmath.Erdos643Design.DesignPrime41
import Openmath.Erdos643Design.DesignPrime61
import Openmath.Erdos643Design.DesignPrime281
import Openmath.Erdos643Design.CyclicSeed81
import Openmath.Erdos643Design.CyclicSeed141
import Openmath.Erdos643Design.CompositeRows
import Openmath.Erdos643Design.CompositeSeedOrders
import Openmath.Erdos643Design.CompositeSeed401
import Openmath.Erdos643Design.FieldFamily5
import Openmath.Erdos643Design.FieldFamily9
import Openmath.Erdos643Design.FieldFamily13
import Openmath.Erdos643Design.FieldFamily17
import Openmath.Erdos643Design.FieldFamily25
import Openmath.Erdos643Design.FieldFamily29
import Openmath.Erdos643Design.FieldFamily37
import Openmath.Erdos643Design.FieldFamily41
import Openmath.Erdos643Design.FieldFamily61
import Openmath.Erdos643Design.FieldFamily81
import Openmath.Erdos643Design.FieldFamily121

/-! Assembly of the exact finite replication-base list from concrete design witnesses.
The conditional assembly uses the two displayed design-existence hypotheses. -/
set_option autoImplicit false
namespace Erdos643Design.FiniteBaseOrders
open HananiAssembly HananiArithmetic

/-- Actual degenerate one-point design, local to this assembly namespace. -/
theorem design_one : DesignExists 1 := by
  refine ⟨∅, ⟨by simp [Finset.IsUniform], ?_⟩⟩
  intro S hS
  have hc := Finset.card_le_card (Finset.subset_univ S)
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  omega

/-- Actual complete five-point design, local to this assembly namespace. -/
theorem design_five : DesignExists 5 := by
  refine ⟨{Finset.univ}, ⟨?_, ?_⟩⟩
  · intro e he
    have heq : e = Finset.univ := Finset.mem_singleton.mp he
    simp [heq]
  · intro S _
    refine ⟨Finset.univ, ⟨by simp, Finset.subset_univ S⟩, ?_⟩
    intro e he
    exact Finset.mem_singleton.mp he.1

theorem base_orders
    (h161 : DesignExists 161) (h285 : DesignExists 285) :
    ∀ r ∈ baseOrders, ReplicationExists r := by
  intro r hr
  simp only [baseOrders, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact Seed21.exists_design
  · exact FieldFamily5.exists_design
  · exact Seed41.exists_design
  · exact FieldFamily9.exists_design
  · exact Seed61.exists_design
  · exact FieldFamily13.exists_design
  · exact CyclicSeed81.exists_design
  · exact FieldFamily17.exists_design
  · exact FieldFamily25.exists_design
  · exact CyclicSeed141.exists_design
  · exact FieldFamily29.exists_design
  · exact h161
  · exact CompositeSeeds.exists_design165
  · exact CompositeSeeds.exists_design181
  · exact FieldFamily37.exists_design
  · exact CompositeSeeds.exists_design201
  · exact FieldFamily41.exists_design
  · exact Seed281.exists_design
  · exact h285
  · exact CompositeSeeds.exists_design301
  · exact FieldFamily61.exists_design
  · exact CompositeSeeds.exists_design401
  · exact FieldFamily81.exists_design
  · exact CompositeSeeds.exists_design421
  · exact CompositeSeeds.exists_design425
  · exact FieldFamily121.exists_design

/-- Only two concrete finite endpoints remain explicit at this assembly stage. -/
theorem residue_designs_of_two_seeds (h161 : DesignExists 161) (h285 : DesignExists 285) :
    ∀ n : ℕ, (n % 20 = 1 ∨ n % 20 = 5) →
      ∃ D : Finset (Finset (Fin n)), D.IsBlockDesign 2 5 :=
  residue_designs_of_finite_ingredients design_one design_five
    (base_orders h161 h285) ⟨CompositeSeeds.td6_16⟩
    ⟨CompositeSeeds.td11_11⟩ ⟨CompositeSeeds.td11_25⟩

end Erdos643Design.FiniteBaseOrders

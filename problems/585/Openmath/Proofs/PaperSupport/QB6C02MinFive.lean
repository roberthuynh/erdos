import Openmath.Proofs.PaperSupport.QB6C02MinFiveResidual
import Openmath.Proofs.PaperSupport.QB6C02OrdinaryFive

/-! Literal minimum-five endpoint assembly. Actual residual and ordinary
original degree-five graph producers form an exhaustive branch split.
Every high/core/family/cut/resource input is produced internally in them.
No assumed successful repair contract occurs at the public endpoints. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
open Erdos585.QB4 Erdos585.QB5 Erdos585.QB6Assembly
open Erdos585.QB6C02PartialFactor Erdos585.QB6C02NonlinearCore
open Erdos585.QB6C02NoTheta3
namespace Erdos585.QB6C02MinFive
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma residual_of_no_ordinary {A C : Finset V}
    (hno : ¬ ∃ p ∈ A, dg G C p = 5 ∧ Ordinary G A C p) :
    PositiveCoreResidual G A C := by
  classical
  intro p hp hp5
  by_contra hn
  have ho : Ordinary G A C p := by
    intro K hK hpK
    exact hn ⟨K, hK, hpK⟩
  exact hno ⟨p, hp, hp5, ho⟩

theorem minfive_good_pair : MinFiveGoodPair.{u} := by
  classical
  intro V _ G _ A C h hm
  by_cases ho : ∃ p ∈ A, dg G C p = 5 ∧ Ordinary G A C p
  · exact QB6C02OrdinaryFive.ordinary5_good_pair G A C h hm ho
  · exact residual_good_pair G A C h hm (residual_of_no_ordinary ho)

theorem minfive_repair : MinFiveRepair.{u} := by
  intro V _ G _ A C h hm
  obtain ⟨D, hD⟩ := minfive_good_pair G A C h hm
  exact goodPair_quartic h hD

end Erdos585.QB6C02MinFive

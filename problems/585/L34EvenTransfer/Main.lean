import L34EvenTransfer.Minimal
import L34EvenTransfer.Barrier
import EvenFactor.Main
import NEQAssembly.CriterionAdapter

/- 

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
namespace Erdos585.L34EvenTransfer
open QB4 B5 NEQ NEQAssembly
universe u

theorem l34_even (q : ℕ) (hq : 6 ≤ q) (heven : Even q)
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hn : 2 ≤ Fintype.card V) (hcap : G.maxDegree ≤ 2 * q - 2)
    (he : (q - 1) * Fintype.card V ≤ G.edgeSet.ncard + (q - 2)) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  classical
  by_contra havoid
  obtain ⟨U, K, hnK, hsub, hcapK, hexact, hfloor⟩ :=
    critical_extraction q hq G hn hcap he
  have havoidK : ¬∃ H : K.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q :=
    extraction_preserves_avoidance q G U K hsub havoid
  have hnospan := no_spanning_of_no_original_support q K hnK havoidK
  obtain ⟨S, T, hST, hnegative⟩ :=
    EvenFactorCriterion.even_no_spanning_factor_barrier q K hq heven hcapK hnospan
  have hnegativeNEQ : NEQ.delta q K univ T S < 0 := by
    rw [← criterion_original_delta_alignment q K S T]
    exact hnegative
  have hregular := regular_of_critical_barrier q hq heven K hnK hcapK hexact hfloor
    T S hST.symm hnegativeNEQ
  exact havoid (original_thinned_induced_regular_transport G U K hsub hregular)

end Erdos585.L34EvenTransfer

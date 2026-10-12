import AllHNextNonstrict.Original
import AllHNextNonstrict.Selection
import AllHNextNonstrict.PetalEscape
import AllHNextNonstrict.TopEscape

/-! R133: faithful nonstrict next-surplus original-host formalization.
The same original omission pays every cut and determines the exact support of
the returned original capacity-one regular subgraph. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.AllHNextNonstrict
open QB4 B5 L34 H3Unequal
universe u

/-- Every allowed variable offset and every original finite carrier are included.
Only the literal original Host is supplied; all cut selection is internal. -/
theorem allh_next_nonstrict (h q a j : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) (host : Host h q a j G A B) :
    ∃ O : Finset V, O ⊆ B ∧ #O = j ∧
      (∀ T ⊆ B, O ⊆ T → thetaJ q j G A B T ≤ 0) ∧
      ∃ H : G.Subgraph, H.verts = (↑(A ∪ (B \ O)) : Set V) ∧
        H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  classical
  have d := host.to_data
  obtain ⟨O, hOB, hOj, hcuts⟩ := d.common_omission (petal_escape (G := G)) (top_escape (G := G))
  have hfactor := factor_of_common_omission q j host.card hOB hOj hcuts
  have hq := host.parameters.q_pos
  have hA : A.Nonempty := card_pos.mp (by have hh := d.shores_large.1; omega)
  obtain ⟨H, hverts, hnonempty, hregular⟩ :=
    factor_exact_subgraph hq hA (host.disjoint.mono_right sdiff_subset) hfactor
  exact ⟨O, hOB, hOj, hcuts, H, hverts, hnonempty, hregular⟩

end Erdos585.AllHNextNonstrict

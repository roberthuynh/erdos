import R643
import Openmath.Proofs.PaperSupport.QB7Conditional
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.QB7SmallLobeR643
open QB4
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem U2Input.of_original {U W : Finset V} (h : QB7Conditional.U2Input G U W) :
    U2Input G U W := by
  refine {
    disjoint := h.disjoint
    independentU := h.independentU
    independentW := h.independentW
    card := h.card
    minU := h.minU
    capU := h.capU
    minW := h.minW
    capW := h.capW
    defU := h.defU
    sparse := by simpa [Sparse7,QB7Conditional.Sparse7,QB7Reduction.SparseBound] using h.sparse
  }

/-- Literal imported original U2Input, with no strengthened floor or supplied
all-cut/factor premise. The two original omissions are fixed arbitrary inputs. -/
theorem original_small_lobe_fixed_omissions {U W S U₁ U₂ W₁ W₂ : Finset V}
    (hi : QB7Conditional.U2Input G U W) (h : Split G U W S U₁ U₂ W₁ W₂)
    (hsmall : #U₁ = 4) {z₁ z₂ : V} (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ < 6) (hd₂ : dg G U z₂ < 6) :
    FixedOmissionFactor G U W z₁ z₂ :=
  small_lobe_fixed_omissions (U2Input.of_original hi) h hsmall hz₁ hz₂ hd₁ hd₂

#print axioms original_small_lobe_fixed_omissions
#print original_small_lobe_fixed_omissions
end Erdos585.QB7SmallLobeR643

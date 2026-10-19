import Openmath.Erdos643R3.AnchorMargin
import Openmath.Erdos643R3.AnchorHostAdapter

set_option autoImplicit false
namespace Erdos643R3.AnchorShare
open Finset
open Erdos643R3.Identity Erdos643R3.SlotModel Erdos643R3.AnchorCaps Erdos643R3.AnchorMargin
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}
variable {x y u v w : V}

/-- The proved strict host margin divided by its genuine positive act count. -/
theorem share_host (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2)
    (hu : 3 ≤ codeg H {x,u}) (hw : 3 ≤ codeg H {x,w})
    (hd : L1Top.Deficient H {x,u,v} ∨ L1Top.Deficient H {x,v,w})
    (hactive : L1Top.Active H {x,y}) :
    ((if L1Top.Deficient H {x,u,v} then L1Top.deficit H {x,u,v} else 0) +
       (if L1Top.Deficient H {x,v,w} then L1Top.deficit H {x,v,w} else 0)) <
      L1Top.charge H {x,u,w} / (L1Top.act H {x,u,w} : ℚ) := by
  classical
  have hm := full_margin_host h hcard hu hw hd
  have hmem : ({x,u,w} : Finset V) ∈ L1Top.bicone H {x,y} := by
    apply L1Top.mem_bicone.mpr
    refine ⟨{u,w},?_,x,by simp,rfl⟩
    rw [h.CN_xy]
    simp
  have ha := G1Bicone.act_pos_of_active_member hactive hmem
  have haq : (0 : ℚ) < L1Top.act H {x,u,w} := by exact_mod_cast ha
  have hs : (0 : ℚ) < groupSigma H x u w := by unfold groupSigma; positivity
  apply (lt_div_iff₀ haq).2
  nlinarith

end Erdos643R3.AnchorShare

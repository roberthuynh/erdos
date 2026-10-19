import Openmath.Erdos643R3.CPrime

set_option autoImplicit false
namespace Erdos643R3.G3Interface
open Finset hiding shadow
open Erdos643R3.Identity Erdos643R3.Weighting Erdos643R3.SlotModel
  Erdos643R3.RedistArith Erdos643R3.CPrime
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}

/-- Every apex-base pair in a bicone has codegree at least two. -/
theorem two_le_codeg {x y u v w : V} (hH : Uniform H)
    (hCN : CN H {x,y} = ({{u,v},{v,w},{u,w}} : Finset (Finset V))) :
    2 ≤ codeg H {x,u} := by
  obtain ⟨hT, _, hA⟩ := bicone_edges hCN
  have hxu := card_pair (triple_ne (hH _ hT)).1
  have hvw : ({v,w} : Finset V).card = 2 :=
    (mem_CN.mp (show ({v,w} : Finset V) ∈ CN H {x,y} by rw [hCN]; simp)).1
  have hs : ({v,w} : Finset V) ⊆ link H {x,u} := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rw [mem_link_iff_of_uniform hH hxu]
    rcases hz with hz | hz
    · subst z
      rwa [show insert v ({x,u} : Finset V) = {x,u,v} from triple_perm (fun t => by tauto)]
    · subst z
      rwa [show insert w ({x,u} : Finset V) = {x,u,w} from triple_perm (fun t => by tauto)]
  have hh := card_le_card hs
  rwa [hvw, ← codeg_eq_card_link hH hxu] at hh

/-- Thus the nonlight outer pairs in `CPrime.G3hPrime` are exactly heavy pairs,
with codegree at least three, on its actual bicone support. -/
theorem three_le_codeg_of_not_light {x y u v w : V} (hH : Uniform H)
    (hCN : CN H {x,y} = ({{u,v},{v,w},{u,w}} : Finset (Finset V)))
    (hn : ¬ Light H x u) : 3 ≤ codeg H {x,u} := by
  have hh := two_le_codeg hH hCN
  unfold Light at hn
  omega

end Erdos643R3.G3Interface

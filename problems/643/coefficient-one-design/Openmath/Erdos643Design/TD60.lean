import Openmath.Erdos643Design.DifferenceMatrixField
import Openmath.Erdos643Design.TransversalProducts
import Openmath.Erdos643Design.TransversalSymbols
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option

/-! GPLv3 finite-table adaptation from SageMath DM_60_6_1, revision
adff41bc98ebbe47fc5c4dc7d794bfc1957d6365, crediting R. Julian R. Abel,
Existence of Five MOLS of Orders 18 and 60, DOI 10.1002/jcd.21384.
See NOTICE-DESIGN.md, COPYING and licenses/Sage-COPYING.txt. -/

set_option autoImplicit false
namespace Erdos643Design.TD60
open Foundation
abbrev G := ZMod 2 × ZMod 30
def table : Fin 60 → Fin 4 → G := ![
  ![(0,0),(1,10),(1,22),(1,24)],
  ![(1,22),(0,0),(1,10),(0,17)],
  ![(1,10),(1,22),(0,0),(1,14)],
  ![(1,6),(0,13),(1,16),(1,0)],
  ![(0,13),(1,16),(1,6),(0,8)],
  ![(1,16),(1,6),(0,13),(0,20)],
  ![(0,0),(1,6),(1,1),(1,1)],
  ![(1,1),(0,0),(1,6),(0,7)],
  ![(1,6),(1,1),(0,0),(1,9)],
  ![(1,29),(0,23),(1,21),(1,0)],
  ![(0,23),(1,21),(1,29),(0,29)],
  ![(1,21),(1,29),(0,23),(0,24)],
  ![(0,0),(0,17),(1,8),(0,14)],
  ![(1,8),(0,0),(0,17),(0,20)],
  ![(0,17),(1,8),(0,0),(0,10)],
  ![(0,16),(0,10),(0,20),(1,0)],
  ![(0,10),(0,20),(0,16),(0,22)],
  ![(0,20),(0,16),(0,10),(1,13)],
  ![(0,0),(0,7),(0,9),(0,0)],
  ![(0,9),(0,0),(0,7),(0,1)],
  ![(0,7),(0,9),(0,0),(0,27)],
  ![(0,0),(0,29),(0,3),(1,0)],
  ![(0,29),(0,3),(0,0),(1,21)],
  ![(0,3),(0,0),(0,29),(1,23)],
  ![(0,0),(1,5),(1,21),(0,16)],
  ![(1,21),(0,0),(1,5),(1,4)],
  ![(1,5),(1,21),(0,0),(1,20)],
  ![(0,14),(1,26),(1,10),(1,0)],
  ![(1,26),(1,10),(0,14),(0,9)],
  ![(1,10),(0,14),(1,26),(0,25)],
  ![(0,0),(0,9),(1,29),(0,18)],
  ![(1,29),(0,0),(0,9),(0,26)],
  ![(0,9),(1,29),(0,0),(0,11)],
  ![(0,12),(0,4),(0,19),(1,0)],
  ![(0,4),(0,19),(0,12),(0,1)],
  ![(0,19),(0,12),(0,4),(1,21)],
  ![(0,0),(0,3),(1,0),(0,8)],
  ![(1,0),(0,0),(0,3),(0,19)],
  ![(0,3),(1,0),(0,0),(0,13)],
  ![(0,22),(0,11),(0,17),(1,0)],
  ![(0,11),(0,17),(0,22),(0,0)],
  ![(0,17),(0,22),(0,11),(1,27)],
  ![(0,0),(1,13),(0,2),(0,28)],
  ![(0,2),(0,0),(1,13),(0,28)],
  ![(1,13),(0,2),(0,0),(1,12)],
  ![(0,2),(0,2),(1,18),(1,0)],
  ![(0,2),(1,18),(0,2),(1,28)],
  ![(1,18),(0,2),(0,2),(0,17)],
  ![(0,0),(1,17),(0,12),(0,17)],
  ![(0,12),(0,0),(1,17),(1,21)],
  ![(1,17),(0,12),(0,0),(0,28)],
  ![(0,13),(1,9),(0,2),(1,0)],
  ![(1,9),(0,2),(0,13),(1,18)],
  ![(0,2),(0,13),(1,9),(0,13)],
  ![(0,0),(0,13),(1,15),(0,7)],
  ![(1,15),(0,0),(0,13),(0,6)],
  ![(0,13),(1,15),(0,0),(1,18)],
  ![(0,23),(0,24),(1,12),(1,0)],
  ![(0,24),(1,12),(0,23),(0,15)],
  ![(1,12),(0,23),(0,24),(1,17)]]
def index (r : G) : Fin 60 := ⟨r.1.val * 30 + r.2.val, by have h := ZMod.val_lt r.1; have h2 := ZMod.val_lt r.2; omega⟩
def matrix (r : G) (i : Fin 4) : G := table (index r) i

theorem difference_cover (i j : Fin 4) (hij : i ≠ j) :
    (Finset.univ.image (fun r : G => matrix r i - matrix r j)) = Finset.univ := by
  fin_cases i <;> fin_cases j <;> first | exact False.elim (hij rfl) | decide

def supplied : DifferenceMatrix (Fin 4) G where
  matrix := matrix
  difference_bijective := by
    intro i j hij
    apply (Fintype.bijective_iff_surjective_and_card _).mpr
    refine ⟨?_, rfl⟩
    intro z
    have hz : z ∈ Finset.univ.image (fun r : G => matrix r i - matrix r j) := by
      rw [difference_cover i j hij]
      exact Finset.mem_univ _
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hz
    exact ⟨r,hr⟩
end Erdos643Design.TD60

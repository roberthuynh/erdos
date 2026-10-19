import Openmath.Erdos643Design.DifferenceMatrixField
import Openmath.Erdos643Design.TransversalProducts
import Openmath.Erdos643Design.TransversalSymbols
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option

/-! GPLv3 finite-table adaptation from SageMath DM_21_6_1, revision
adff41bc98ebbe47fc5c4dc7d794bfc1957d6365, crediting Handbook of Combinatorial
Designs III.3.50. See NOTICE-DESIGN.md, COPYING and licenses/Sage-COPYING.txt. -/

set_option autoImplicit false
namespace Erdos643Design.TD21
open Foundation
abbrev G := ZMod 21
def table : Fin 21 → Fin 4 → G := ![
  ![0,0,0,0],
  ![8,9,11,14],
  ![9,11,14,18],
  ![11,14,18,8],
  ![14,18,8,9],
  ![18,8,9,11],
  ![17,16,5,1],
  ![16,5,1,19],
  ![5,1,19,17],
  ![1,19,17,16],
  ![19,17,16,5],
  ![20,4,10,3],
  ![4,10,3,12],
  ![10,3,12,20],
  ![3,12,20,4],
  ![12,20,4,10],
  ![2,15,6,13],
  ![15,6,13,7],
  ![6,13,7,2],
  ![13,7,2,15],
  ![7,2,15,6]]
def index (r : G) : Fin 21 := ⟨r.val, by exact ZMod.val_lt r⟩
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
end Erdos643Design.TD21

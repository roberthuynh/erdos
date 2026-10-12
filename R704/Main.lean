import R704.Base
import R704.Selection
import R704.Tiny
import R716.Main
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.Omit1UniqueR704
open QB4 B5 H3Unequal Omit1PrefixR691 Omit1KillersR716
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V} {q : ℕ} {A B M : Finset V}

/-- The actual unique-negative branch manufactures one pair paying every original unit cut. -/
theorem unique_pair_paid (host : Omit1Q0CutChainR699.Host q G A B)
    (unique : UniqueCut q G A B M) :
    ∃ a ∈ A∩M, ∃ b ∈ B\M, ∀ S : Finset V,
      (q : ℤ)*((if b∈S then 1 else 0)-(if a∈S then 1 else 0)) ≤ g q G A B S := by
  have d := Omit1Q0CutChainR699.all_negative host M (by rw [unique.negative]; omega)
  obtain ⟨a,ha,b,hb,cases⟩ := selector_alternatives host unique d
  refine ⟨a,ha,b,hb,?_⟩
  rcases cases with zz | oo | zo | oz
  · exact zero_zero_paid host d unique ha hb zz.1 zz.2
  · exact one_one_edge_paid host d unique ha hb oo.1 oo.2.1 oo.2.2
  · exact zero_one_nohazard_paid host d unique ha hb zo.1 zo.2.1 zo.2.2.2 zo.2.2.1
  · have sh := swapped_q0_host host
    have su := swapped_unique host.toHost unique
    have sd := Omit1Q0CutChainR699.all_negative sh (univ\M)
      (by rw [g_swap_complement host.toHost]; rw [unique.negative]; omega)
    have bx : B∩(univ\M)=B\M := by ext v; simp
    have ay : A\(univ\M)=A∩M := by ext v; simp
    have ha' : a∈A\(univ\M) := by simpa only [ay] using ha
    have hb' : b∈B∩(univ\M) := by simpa only [bx] using hb
    have db' : dg G (A\(univ\M)) b=0 := by simpa only [ay] using oz.2.1
    have da' : dg G (B∩(univ\M)) a=1 := by simpa only [bx] using oz.1
    have ns : ∀ x ∈ B∩(univ\M), ∀ y ∈ A\(univ\M), G.Adj x y →
        ¬(dg G (A\(univ\M)) x=1 ∧ dg G (B∩(univ\M)) y=1) := by
      rw [bx,ay]
      intro x hx y hy hxy hh
      exact oz.2.2.2 y hy x hx hxy.symm ⟨hh.2,hh.1⟩
    have paid := zero_one_nohazard_paid sh sd su hb' ha' db' da' ns oz.2.2.1
    intro S
    have pc := paid (univ\S)
    rw [g_swap_complement host.toHost S] at pc
    by_cases aa : a∈S <;> by_cases bb : b∈S <;> simpa [aa,bb] using pc

/-- Unique negativity, with its value and all other cut signs derived from the original host. -/
theorem unique_pair_paid_of_unique_negative (host : Omit1Q0CutChainR699.Host q G A B)
    (negative : g q G A B M < 0)
    (unique : ∀ S : Finset V, g q G A B S < 0 → S=M) :
    ∃ a ∈ A∩M, ∃ b ∈ B\M, ∀ S : Finset V,
      (q : ℤ)*((if b∈S then 1 else 0)-(if a∈S then 1 else 0)) ≤ g q G A B S := by
  apply unique_pair_paid host
  refine ⟨(Omit1Q0CutChainR699.all_negative host M negative).value,?_⟩
  intro S hn
  by_contra! bad
  exact hn (unique S bad)

#check @unique_pair_paid
#print axioms unique_pair_paid
#check @unique_pair_paid_of_unique_negative
#print axioms unique_pair_paid_of_unique_negative
end Erdos585.Omit1UniqueR704

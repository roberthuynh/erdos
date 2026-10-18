import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Erdos85.IncidenceRepair

/-- A proper additive subgroup occupies at most half a finite group. -/
theorem twice_card_addSubgroup_le {G : Type*} [AddGroup G] [Finite G]
    (S : AddSubgroup G) (hS : S ≠ ⊤) : 2 * Nat.card S ≤ Nat.card G := by
  have hi : 2 ≤ S.index := S.one_lt_index_of_ne_top hS
  calc
    2 * Nat.card S ≤ S.index * Nat.card S := Nat.mul_le_mul_right _ hi
    _ = Nat.card G := S.index_mul_card

/-- More-than-half agreement forces two additive homomorphisms to be equal. -/
theorem additive_eq_of_twice_card_agreement_gt {G H : Type*}
    [AddGroup G] [AddGroup H] [Finite G] (f g : G →+ H)
    (h : Nat.card G < 2 * Nat.card {x : G // f x = g x}) : f = g := by
  have he : f.eqLocus g = ⊤ := by
    by_contra hn
    have hc := twice_card_addSubgroup_le (f.eqLocus g) hn
    exact (not_lt_of_ge hc) h
  ext x
  have hx : x ∈ f.eqLocus g := by rw [he]; trivial
  exact hx

/-- The agreement bound in a cardinality-only form, including characteristic two. -/
theorem twice_card_agreement_le {G H : Type*}
    [AddGroup G] [AddGroup H] [Finite G] (f g : G →+ H) (hne : f ≠ g) :
    2 * Nat.card {x : G // f x = g x} ≤ Nat.card G := by
  by_contra h
  exact hne (additive_eq_of_twice_card_agreement_gt f g (Nat.lt_of_not_ge h))

/-- Translating a nonempty fiber identifies it with the kernel. -/
def additiveFiberEquivKer {G H : Type*} [AddGroup G] [AddGroup H]
    (f : G →+ H) (y : H) (x₀ : G) (hx₀ : f x₀ = y) :
    {x : G // f x = y} ≃ f.ker where
  toFun x := ⟨x.val - x₀, by simp [AddMonoidHom.mem_ker, map_sub, x.property, hx₀]⟩
  invFun x := ⟨x.val + x₀, by simp [map_add, (show f x.val = 0 from x.property), hx₀]⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

/-- Every fiber of a nonzero additive homomorphism occupies at most half the domain. -/
theorem twice_card_additive_fiber_le {G H : Type*} [AddGroup G] [AddGroup H]
    [Finite G] (f : G →+ H) (hne : f ≠ 0) (y : H) :
    2 * Nat.card {x : G // f x = y} ≤ Nat.card G := by
  by_cases hx : ∃ x, f x = y
  · obtain ⟨x₀, hx₀⟩ := hx
    rw [Nat.card_congr (additiveFiberEquivKer f y x₀ hx₀)]
    exact twice_card_addSubgroup_le f.ker (mt AddMonoidHom.ker_eq_top_iff.mp hne)
  · have : IsEmpty {x : G // f x = y} := ⟨fun x => hx ⟨x.val, x.property⟩⟩
    simp

/-- Two additive maps approximating the same function must agree when their
combined disagreement count is strictly less than half the domain. -/
theorem additive_eq_of_common_approximation {G H : Type*}
    [AddGroup G] [AddGroup H] [Fintype G]
    (f g : G →+ H) (c : G → H) [DecidableEq H]
    (hsmall : 2 * ((Finset.univ.filter fun x => f x ≠ c x).card +
      (Finset.univ.filter fun x => g x ≠ c x).card) < Fintype.card G) : f = g := by
  classical
  by_contra hne
  have hc := twice_card_agreement_le f g hne
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
  have hsub : (Finset.univ.filter fun x => f x ≠ g x) ⊆
      (Finset.univ.filter fun x => f x ≠ c x) ∪
        (Finset.univ.filter fun x => g x ≠ c x) := by
    intro x hx
    have hfg := (Finset.mem_filter.mp hx).2
    by_cases hf : f x = c x
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, fun hg => hfg (hf.trans hg.symm)⟩
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hf⟩
  have hb := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hp := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset G)) (fun x => f x = g x)
  simp only [Finset.card_univ] at hp
  simp only [ne_eq] at hb hsmall
  have heq : (Finset.univ.filter fun x => ¬ f x = g x).card =
      (Finset.univ.filter fun x => f x ≠ g x).card := by congr
  rw [heq] at hp
  omega

end Erdos85.IncidenceRepair

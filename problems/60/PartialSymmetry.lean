import Mathlib.Combinatorics.Configuration

/-! Prerequisites only for HMY (2023), Lemma 2.1. No numerical extension
claim is made. `good` means symmetry against every index, not just its block. -/
namespace Erdos60.PartialSymmetry

variable {P L : Type*} [Membership P L]

def SymmetricAt (line : P ≃ L) (good : Set P) : Prop :=
  ∀ a ∈ good, ∀ x : P, a ∈ line x ↔ x ∈ line a

/-- Cross-block symmetry transports two good points on an assigned line
into two assigned lines through the corresponding point. -/
theorem transport_pair (line : P ≃ L) (good : Set P)
    (h : SymmetricAt line good) {a b x : P}
    (ha : a ∈ good) (hb : b ∈ good)
    (hax : a ∈ line x) (hbx : b ∈ line x) :
    x ∈ line a ∧ x ∈ line b :=
  ⟨(h a ha x).mp hax, (h b hb x).mp hbx⟩

/-- Two distinct symmetric indices determine the point corresponding to
any line through those two indices. This uses actual incidence uniqueness. -/
theorem determine_point [Configuration.Nondegenerate P L]
    (line : P ≃ L) (good : Set P) (h : SymmetricAt line good)
    {a b x y : P} (hab : a ≠ b) (ha : a ∈ good) (hb : b ∈ good)
    (hax : a ∈ line x) (hbx : b ∈ line x)
    (hya : y ∈ line a) (hyb : y ∈ line b) : x = y := by
  have hx := transport_pair line good h ha hb hax hbx
  exact (Configuration.Nondegenerate.eq_or_eq hx.1 hya hx.2 hyb).resolve_right
    (fun he => hab (line.injective he))

/-- If two assigned lines differ but their profiles on the good set agree,
there cannot be two distinct good points on the first line. This is a direct
restriction on any prospective completion; it is not the threshold theorem. -/
theorem indistinguishable_lines_have_at_most_one_good_point
    [Configuration.Nondegenerate P L] (line : P ≃ L) (good : Set P)
    {x y : P} (hxy : x ≠ y)
    (profile : ∀ a ∈ good, a ∈ line x ↔ a ∈ line y)
    {a b : P} (ha : a ∈ good) (hb : b ∈ good)
    (hax : a ∈ line x) (hbx : b ∈ line x) : a = b := by
  exact (Configuration.Nondegenerate.eq_or_eq hax hbx
    ((profile a ha).mp hax) ((profile b hb).mp hbx)).resolve_right
      (fun he => hxy (line.injective he))

/-- The final possible exceptional row is fixed once a permutation fixes
all other rows. Used in the final sentence of Füredi (1988), Lemma 3.7. -/
theorem Equiv.fixed_at_exception (e : P ≃ P) (exception : P)
    (fixed : ∀ x, x ≠ exception → e x = x) : e exception = exception := by
  by_contra h
  have hh : e (e exception) = e exception := fixed (e exception) h
  exact h (e.injective hh)

#print axioms Equiv.fixed_at_exception
#print axioms transport_pair
#print axioms determine_point
#print axioms indistinguishable_lines_have_at_most_one_good_point
end Erdos60.PartialSymmetry

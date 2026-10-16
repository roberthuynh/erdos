import PolarityDegree
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

namespace Erdos60.Geometry
open scoped Classical

/-- An involution on an odd finite set has a fixed point. The proof uses an
actual degree-one graph and handshaking, avoiding any geometric source axiom. -/
theorem involution_fixedpoint_of_odd {S : Type*} [Fintype S]
    (f : S → S) (hinv : Function.Involutive f) (hodd : Odd (Fintype.card S)) :
    ∃ a, f a = a := by
  classical
  by_contra h
  have hfree : ∀ a, f a ≠ a := by simpa using h
  let H : SimpleGraph S := {
    Adj := fun a b => f a = b
    symm := ⟨fun a b hab => by rw [← hab]; exact hinv a⟩
    loopless := ⟨hfree⟩ }
  have hd : ∀ a, H.degree a = 1 := by
    intro a
    have he : H.neighborFinset a = {f a} := by ext b; simp [H, eq_comm]
    rw [← SimpleGraph.card_neighborFinset_eq_degree, he]
    simp
  have hs := H.sum_degrees_eq_twice_card_edges
  simp only [hd, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hs
  obtain ⟨k,hk⟩ := hodd
  omega

variable {P L : Type*} [Membership P L]

theorem Polarity.absolute_meets_polar_line [Configuration.ProjectivePlane P L]
    [Fintype P] [Finite L] (π : Polarity (P := P) (L := L))
    (heven : Even (Configuration.ProjectivePlane.order P L)) (x : P) :
    ∃ a : P, π.Absolute a ∧ a ∈ π.line x := by
  classical
  by_cases hx : π.Absolute x
  · exact ⟨x,hx,hx⟩
  let S := { a : P // a ∈ π.line x }
  have hline : ∀ a : S, π.line a.val ≠ π.line x := by
    intro a ha
    have hax := π.line.injective ha
    have hap := a.property
    rw [hax] at hap
    exact hx hap
  have hex : ∀ a : S, ∃ b : S, b.val ∈ π.line a.val := by
    intro a
    obtain ⟨b,hb,_⟩ := Configuration.HasPoints.existsUnique_point P L
      (π.line a.val) (π.line x) (hline a)
    exact ⟨⟨b,hb.2⟩,hb.1⟩
  choose f hf using hex
  have hinv : Function.Involutive f := by
    intro a
    apply Subtype.ext
    have ha : a.val ∈ π.line (f a).val := (π.reciprocal _ _).mp (hf a)
    rcases Configuration.Nondegenerate.eq_or_eq (hf (f a)) ha
      (f (f a)).property a.property with h | h
    · exact h
    · exact False.elim (hline (f a) h)
  have hcard : Fintype.card S = Configuration.ProjectivePlane.order P L + 1 := by
    simpa only [Configuration.pointCount, Nat.card_eq_fintype_card] using
      (Configuration.ProjectivePlane.pointCount_eq (P := P) (π.line x))
  have hodd : Odd (Fintype.card S) := by
    rw [hcard]
    obtain ⟨k,hk⟩ := heven
    exact ⟨k,by omega⟩
  obtain ⟨a,ha⟩ := involution_fixedpoint_of_odd f hinv hodd
  refine ⟨a.val,?_,a.property⟩
  have hh := hf a
  rw [ha] at hh
  exact hh

theorem Polarity.absolute_meets_line [Configuration.ProjectivePlane P L]
    [Fintype P] [Finite L] (π : Polarity (P := P) (L := L))
    (heven : Even (Configuration.ProjectivePlane.order P L)) (ℓ : L) :
    ∃ a : P, π.Absolute a ∧ a ∈ ℓ := by
  obtain ⟨x,rfl⟩ := π.line.surjective ℓ
  exact π.absolute_meets_polar_line heven x

/-- The even-order absolute-point lower bound, proved by incidence counting. -/
theorem Polarity.absolute_count_lower [Configuration.ProjectivePlane P L]
    [Fintype P] [Finite L] (π : Polarity (P := P) (L := L))
    (heven : Even (Configuration.ProjectivePlane.order P L)) :
    Configuration.ProjectivePlane.order P L + 1 ≤ Nat.card {a : P // π.Absolute a} := by
  classical
  let A := {a : P // π.Absolute a}
  have hex : ∀ x : P, ∃ a : A, x ∈ π.line a.val := by
    intro x
    obtain ⟨a,ha,hax⟩ := π.absolute_meets_polar_line heven x
    exact ⟨⟨a,ha⟩,(π.reciprocal a x).mp hax⟩
  choose f hf using hex
  let g : P → Σ a : A, {x : P // x ∈ π.line a.val} :=
    fun x => ⟨f x,⟨x,hf x⟩⟩
  have hg : Function.Injective g := by
    intro x y h
    exact congrArg (fun z : Σ a : A, {x : P // x ∈ π.line a.val} => z.2.val) h
  have hcard : ∀ a : A, Fintype.card {x : P // x ∈ π.line a.val} =
      Configuration.ProjectivePlane.order P L + 1 := by
    intro a
    simpa only [Configuration.pointCount, Nat.card_eq_fintype_card] using
      (Configuration.ProjectivePlane.pointCount_eq (P := P) (π.line a.val))
  have hcount := Fintype.card_le_of_injective g hg
  rw [Fintype.card_sigma] at hcount
  simp only [hcard, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hcount
  rw [Configuration.ProjectivePlane.card_points P L] at hcount
  have ha : Configuration.ProjectivePlane.order P L + 1 ≤ Fintype.card A := by
    by_contra hn
    have hle : Fintype.card A ≤ Configuration.ProjectivePlane.order P L := by omega
    have hmul := Nat.mul_le_mul_right (Configuration.ProjectivePlane.order P L + 1) hle
    nlinarith
  simpa only [Nat.card_eq_fintype_card] using ha

/-- Exact degree sum with the removed absolute diagonals retained. -/
theorem Polarity.twice_edges_add_absolute [Configuration.ProjectivePlane P L]
    [Fintype P] [Finite L] (π : Polarity (P := P) (L := L)) :
    2 * π.graph.edgeFinset.card + Nat.card {a : P // π.Absolute a} =
      (Configuration.ProjectivePlane.order P L + 1) *
      (Configuration.ProjectivePlane.order P L ^ 2 +
        Configuration.ProjectivePlane.order P L + 1) := by
  classical
  have hsum : ∑ x : P, (π.graph.degree x + if π.Absolute x then 1 else 0) =
      ∑ _x : P, (Configuration.ProjectivePlane.order P L + 1) := by
    apply Finset.sum_congr rfl
    intro x _
    exact (π.degree_add_diagonal x).trans
      (Configuration.ProjectivePlane.pointCount_eq (P := P) (π.line x))
  have hdiag : (∑ x : P, if π.Absolute x then 1 else 0) =
      Nat.card {a : P // π.Absolute a} := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.sum_add_distrib, π.graph.sum_degrees_eq_twice_card_edges, hdiag] at hsum
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Configuration.ProjectivePlane.card_points P L, Nat.mul_comm] using hsum

theorem Polarity.edge_count_upper [Configuration.ProjectivePlane P L]
    [Fintype P] [Finite L] (π : Polarity (P := P) (L := L))
    (heven : Even (Configuration.ProjectivePlane.order P L)) :
    π.graph.edgeFinset.card ≤ Configuration.ProjectivePlane.order P L *
      (Configuration.ProjectivePlane.order P L + 1)^2 / 2 := by
  have hsum := π.twice_edges_add_absolute
  have ha := π.absolute_count_lower heven
  have h2 : 2 * π.graph.edgeFinset.card ≤ Configuration.ProjectivePlane.order P L *
      (Configuration.ProjectivePlane.order P L + 1)^2 := by nlinarith
  omega

theorem Polarity.edge_count_eq_iff_absolute_count [Configuration.ProjectivePlane P L]
    [Fintype P] [Finite L] (π : Polarity (P := P) (L := L))
    (heven : Even (Configuration.ProjectivePlane.order P L)) :
    π.graph.edgeFinset.card = Configuration.ProjectivePlane.order P L *
      (Configuration.ProjectivePlane.order P L + 1)^2 / 2 ↔
    Nat.card {a : P // π.Absolute a} = Configuration.ProjectivePlane.order P L + 1 := by
  have hsum := π.twice_edges_add_absolute
  have he : 2 ∣ Configuration.ProjectivePlane.order P L *
      (Configuration.ProjectivePlane.order P L + 1)^2 := by
    exact dvd_mul_of_dvd_left (even_iff_two_dvd.mp heven) _
  have hm := Nat.mul_div_cancel' he
  constructor <;> intro h <;> nlinarith

#print axioms involution_fixedpoint_of_odd
#print axioms Polarity.absolute_meets_line
#print axioms Polarity.absolute_count_lower
#print axioms Polarity.twice_edges_add_absolute
#print axioms Polarity.edge_count_upper
#print axioms Polarity.edge_count_eq_iff_absolute_count
end Erdos60.Geometry

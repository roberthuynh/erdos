import Mathlib.Combinatorics.Configuration
import Mathlib.Combinatorics.SimpleGraph.Basic

/-! A genuine, limited geometry ingredient for #60. This does not supply the
Metsch embedding, partial-symmetry extension, or headline supersaturation theorem. -/
namespace Erdos60.Geometry

variable {P L : Type*} [Membership P L]

/-- A point-to-line equivalence with symmetric incidence is precisely the
point-to-line part of a polarity. Its inverse specifies the line-to-point part. -/
structure Polarity where
  line : P ≃ L
  reciprocal : ∀ x y : P, x ∈ line y ↔ y ∈ line x

def Polarity.graph (π : Polarity (P := P) (L := L)) : SimpleGraph P where
  Adj x y := x ≠ y ∧ x ∈ π.line y
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, (π.reciprocal x y).mp h.2⟩
  loopless := ⟨fun x h => h.1 rfl⟩

theorem Polarity.adj_iff (π : Polarity (P := P) (L := L)) (x y : P) :
    π.graph.Adj x y ↔ x ≠ y ∧ x ∈ π.line y := Iff.rfl

/-- The incidence uniqueness axiom proves the actual graph has at most one
common neighbor for distinct vertices. No completion theorem is assumed. -/
theorem Polarity.common_neighbor_unique [Configuration.Nondegenerate P L]
    (π : Polarity (P := P) (L := L)) {x y u v : P} (hxy : x ≠ y)
    (hxu : π.graph.Adj x u) (hyu : π.graph.Adj y u)
    (hxv : π.graph.Adj x v) (hyv : π.graph.Adj y v) : u = v := by
  have hu := (π.reciprocal x u).mp hxu.2
  have hu' := (π.reciprocal y u).mp hyu.2
  have hv := (π.reciprocal x v).mp hxv.2
  have hv' := (π.reciprocal y v).mp hyv.2
  rcases Configuration.Nondegenerate.eq_or_eq hu hv hu' hv' with h | h
  · exact h
  · exact False.elim (hxy (π.line.injective h))

/-- No ordinary four-cycle, expressed directly with its four edges. This
form avoids any induced-cycle convention or labelled-copy normalization. -/
theorem Polarity.no_four_cycle [Configuration.Nondegenerate P L]
    (π : Polarity (P := P) (L := L)) {a b c d : P}
    (hac : a ≠ c) (hbd : b ≠ d)
    (hab : π.graph.Adj a b) (hbc : π.graph.Adj b c)
    (hcd : π.graph.Adj c d) (hda : π.graph.Adj d a) : False := by
  exact hbd (π.common_neighbor_unique hac hab hbc.symm hda.symm hcd)

theorem Polarity.card_vertices [Configuration.ProjectivePlane P L]
    [Fintype P] [Finite L] (_π : Polarity (P := P) (L := L)) :
    Fintype.card P = Configuration.ProjectivePlane.order P L ^ 2 +
      Configuration.ProjectivePlane.order P L + 1 :=
  Configuration.ProjectivePlane.card_points P L

#print axioms Polarity.common_neighbor_unique
#print axioms Polarity.no_four_cycle
#print axioms Polarity.card_vertices

end Erdos60.Geometry

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-! Exact combinatorial support step of the accepted localization proof, §7.
No quantitative smallness of the exceptional set or residual set is asserted. -/
namespace Erdos60.Localization
variable {V : Type*}

/-- Opposite vertices have two distinct actual common neighbors in the host graph. -/
def Opposite (G : SimpleGraph V) (u v : V) : Prop :=
  u ≠ v ∧ ∃ x y, x ≠ y ∧ G.Adj u x ∧ G.Adj v x ∧ G.Adj u y ∧ G.Adj v y

/-- The actual residual set from §7, using one fixed exceptional set X. -/
def residual (G : SimpleGraph V) (X : Set V) : Set V :=
  {v | v ∉ X ∧ ∃ u, u ∉ X ∧ Opposite G v u}

def support (G : SimpleGraph V) (X : Set V) : Set V := X ∪ residual G X

/-- Every actual ordinary four-cycle has an actual edge inside X ∪ R.
The four vertices need only be pairwise distinct as opposite pairs: adjacency
in a simple graph supplies the remaining four inequalities automatically.
Additional diagonals are allowed, so the assertion is about ordinary C4s. -/
theorem cycle_has_support_edge (G : SimpleGraph V) (X : Set V)
    {a b c d : V} (hac : a ≠ c) (hbd : b ≠ d)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a) :
    (a ∈ support G X ∧ b ∈ support G X) ∨
    (b ∈ support G X ∧ c ∈ support G X) ∨
    (c ∈ support G X ∧ d ∈ support G X) ∨
    (d ∈ support G X ∧ a ∈ support G X) := by
  classical
  have hopac : Opposite G a c :=
    ⟨hac, b, d, hbd, hab, hbc.symm, hda.symm, hcd⟩
  have hopca : Opposite G c a :=
    ⟨hac.symm, b, d, hbd, hbc.symm, hab, hcd, hda.symm⟩
  have hopbd : Opposite G b d :=
    ⟨hbd, a, c, hac, hab.symm, hda, hbc, hcd.symm⟩
  have hopdb : Opposite G d b :=
    ⟨hbd.symm, a, c, hac, hda, hab.symm, hcd.symm, hbc⟩
  have ha : a ∉ X → c ∉ X → a ∈ support G X :=
    fun ha hc => Or.inr ⟨ha, c, hc, hopac⟩
  have hc : c ∉ X → a ∉ X → c ∈ support G X :=
    fun hc ha => Or.inr ⟨hc, a, ha, hopca⟩
  have hb : b ∉ X → d ∉ X → b ∈ support G X :=
    fun hb hd => Or.inr ⟨hb, d, hd, hopbd⟩
  have hd : d ∉ X → b ∉ X → d ∈ support G X :=
    fun hd hb => Or.inr ⟨hd, b, hb, hopdb⟩
  by_cases hax : a ∈ X <;> by_cases hbx : b ∈ X <;>
    by_cases hcx : c ∈ X <;> by_cases hdx : d ∈ X <;>
    simp_all only [support, Set.mem_union] <;> aesop

/-- The spanning graph formed by deleting all actual edges internal to support. -/
def deleteSupportEdges (G : SimpleGraph V) (X : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ¬ (u ∈ support G X ∧ v ∈ support G X)
  symm := ⟨fun _u _v h => ⟨h.1.symm, fun h' => h.2 ⟨h'.2, h'.1⟩⟩⟩
  loopless := ⟨fun _u h => G.ne_of_adj h.1 rfl⟩

/-- Deleting the selected actual edges eliminates every ordinary C4,
including cycles that leave the support. -/
theorem deleteSupportEdges_no_four_cycle (G : SimpleGraph V) (X : Set V)
    {a b c d : V} (hac : a ≠ c) (hbd : b ≠ d)
    (hab : (deleteSupportEdges G X).Adj a b)
    (hbc : (deleteSupportEdges G X).Adj b c)
    (hcd : (deleteSupportEdges G X).Adj c d)
    (hda : (deleteSupportEdges G X).Adj d a) : False := by
  rcases cycle_has_support_edge G X hac hbd hab.1 hbc.1 hcd.1 hda.1 with h | h | h | h
  · exact hab.2 h
  · exact hbc.2 h
  · exact hcd.2 h
  · exact hda.2 h

#print axioms cycle_has_support_edge
#print axioms deleteSupportEdges_no_four_cycle
end Erdos60.Localization

import PolarityDegree
import Mathlib.Tactic

namespace Erdos60.Geometry
variable {P L : Type*} [Membership P L]

/-- The two internal vertices of an oriented simple three-edge path. For
distinct nonadjacent endpoints, the edge hypotheses already force simplicity. -/
def Polarity.ThreePath (π : Polarity (P := P) (L := L)) (u v : P) :=
  { ab : P × P // π.graph.Adj u ab.1 ∧ π.graph.Adj ab.1 ab.2 ∧ π.graph.Adj ab.2 v }

noncomputable def Polarity.ThreePath.edges (π : Polarity (P := P) (L := L))
    {u v : P} (p : π.ThreePath u v) : Finset (Sym2 P) := by
  classical
  exact {s(u, p.val.1), s(p.val.1, p.val.2), s(p.val.2, v)}

theorem Polarity.ThreePath.edge_disjoint [Configuration.Nondegenerate P L]
    (π : Polarity (P := P) (L := L)) {u v : P} (hne : u ≠ v)
    (hnadj : ¬π.graph.Adj u v) (p r : π.ThreePath u v) (hpr : p ≠ r) :
    Disjoint (p.edges π) (r.edges π) := by
  classical
  obtain ⟨⟨a,b⟩, ha, hab, hb⟩ := p
  obtain ⟨⟨c,d⟩, hc, hcd, hd⟩ := r
  have hleft : a = c → b = d := fun h =>
    π.three_path_right_unique hnadj ha hab hb (h ▸ hcd) hd
  have hright : b = d → a = c := fun h =>
    π.three_path_left_unique hnadj ha hab hb hc (h.symm ▸ hcd)
  have hrev : ¬(a = d ∧ b = c) := by
    rintro ⟨rfl, rfl⟩
    exact π.three_path_no_reversed_middle hne ha hab hb hc hd
  have habne := hab.ne
  have hcdne := hcd.ne
  have huane := ha.ne
  have hcvne := hd.ne
  have hucne := hc.ne
  have hbvne := hb.ne
  have hav : a ≠ v := by intro h; exact hnadj (h ▸ ha)
  have hcv : c ≠ v := by intro h; exact hnadj (h ▸ hc)
  have hub : u ≠ b := by intro h; exact hnadj (h ▸ hb)
  have hud : u ≠ d := by intro h; exact hnadj (h ▸ hd)
  have hpair : ¬(a = c ∧ b = d) := by
    rintro ⟨rfl, rfl⟩
    exact hpr rfl
  apply Finset.disjoint_left.mpr
  intro e hp he
  simp only [ThreePath.edges, Finset.mem_insert, Finset.mem_singleton] at hp he
  rcases hp with hp | hp | hp <;> rcases he with he | he | he
  all_goals have heq := hp.symm.trans he
  all_goals simp only [Sym2.eq_iff] at heq
  all_goals grind

#print axioms Polarity.ThreePath.edge_disjoint
end Erdos60.Geometry

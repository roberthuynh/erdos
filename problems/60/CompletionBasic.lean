import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

namespace Erdos60.Completion
variable {V : Type*}

/-- Explicit ordinary four-cycle exclusion; diagonals are permitted. -/
def NoFourCycle (G : SimpleGraph V) : Prop :=
  ∀ ⦃a b c d : V⦄, a ≠ c → b ≠ d →
    G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → False

theorem common_neighbor_unique {G : SimpleGraph V} (hG : NoFourCycle G)
    {x y a b : V} (hxy : x ≠ y) (hxa : G.Adj x a) (hya : G.Adj y a)
    (hxb : G.Adj x b) (hyb : G.Adj y b) : a = b := by
  by_contra hab
  exact hG hxy hab hxa hya.symm hyb hxb.symm

/-- The local graph at any vertex has at most one neighbor at each vertex. -/
theorem neighborhood_neighbor_unique {G : SimpleGraph V} (hG : NoFourCycle G)
    {v a b c : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (hvc : G.Adj v c) (hab : G.Adj a b) (hac : G.Adj a c) : b = c :=
  common_neighbor_unique hG hva.ne hvb hab hvc hac

/-- Open two-step cell outside the center's closed neighborhood. -/
def cell (G : SimpleGraph V) (v a : V) : Set V :=
  {x | G.Adj a x ∧ x ≠ v ∧ ¬G.Adj v x}

def bundle (G : SimpleGraph V) (v a : V) : Set V := cell G v a ∪ {a}

theorem cells_disjoint {G : SimpleGraph V} (hG : NoFourCycle G)
    {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b) (hab : a ≠ b) :
    Disjoint (cell G v a) (cell G v b) := by
  apply Set.disjoint_left.mpr
  intro x ha hb
  have h := common_neighbor_unique hG ha.2.1 ha.1.symm hva hb.1.symm hvb
  exact hab h

theorem bundles_disjoint {G : SimpleGraph V} (hG : NoFourCycle G)
    {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b) (hab : a ≠ b) :
    Disjoint (bundle G v a) (bundle G v b) := by
  apply Set.disjoint_left.mpr
  intro x ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact Set.disjoint_left.mp (cells_disjoint hG hva hvb hab) ha hb
  · exact ha.2.2 ((Set.mem_singleton_iff.mp hb).symm ▸ hvb)
  · exact hb.2.2 ((Set.mem_singleton_iff.mp ha).symm ▸ hva)
  · exact hab ((Set.mem_singleton_iff.mp ha).symm.trans (Set.mem_singleton_iff.mp hb))

/-- A full vertex cannot have only full neighbors when q is even.
The proof counts genuine two-step paths and uses parity in the induced neighborhood. -/
theorem full_vertex_has_deficient_neighbor [Fintype V]
    (G : SimpleGraph V) (hG : NoFourCycle G) (q : ℕ) (hq : Even q)
    (hN : Fintype.card V = q^2+q+1)
    (hcap : ∀ x, letI := Classical.decRel G.Adj; G.degree x ≤ q+1)
    (v : V) (hv : letI := Classical.decRel G.Adj; G.degree v = q+1) :
    ∃ a : V, G.Adj v a ∧ (letI := Classical.decRel G.Adj; G.degree a ≤ q) := by
  classical
  by_contra hnone
  have hfull : ∀ a, G.Adj v a → G.degree a = q+1 := by
    intro a ha
    have hn : ¬G.degree a ≤ q := fun h => hnone ⟨a,ha,h⟩
    have hc := hcap a
    omega
  let A := {a : V // G.Adj v a}
  let T := (a : A) × {b : V // G.Adj a.val b ∧ b ≠ v}
  let f : T → {b : V // b ≠ v} := fun p => ⟨p.2.val,p.2.property.2⟩
  have hi : Function.Injective f := by
    intro p r h
    have he : p.2.val = r.2.val := congrArg Subtype.val h
    have ha : p.1.val = r.1.val := common_neighbor_unique hG p.2.property.2
      p.2.property.1.symm p.1.property (he ▸ r.2.property.1.symm) r.1.property
    cases p with | mk a b =>
      cases r with | mk c d =>
        have hac : a = c := Subtype.ext ha
        subst c
        have hbd : b = d := Subtype.ext he
        subst d
        rfl
  have hTc : Fintype.card T = q*(q+1) := by
    have hb : ∀ a : A, Fintype.card {b : V // G.Adj a.val b ∧ b ≠ v} = q := by
      intro a
      have he : Finset.univ.filter (fun b => G.Adj a.val b ∧ b ≠ v) =
          (G.neighborFinset a.val).erase v := by ext b; simp [and_comm]
      rw [Fintype.card_subtype,he,Finset.card_erase_of_mem
        (show v ∈ G.neighborFinset a.val by simpa using a.property.symm)]
      rw [SimpleGraph.card_neighborFinset_eq_degree,hfull a.val a.property]
      omega
    have hA : Fintype.card A = q+1 := by
      change Fintype.card (G.neighborSet v) = q+1
      rw [SimpleGraph.card_neighborSet_eq_degree,hv]
    simp only [T,Fintype.card_sigma,hb,Finset.sum_const,Finset.card_univ,smul_eq_mul]
    rw [hA]
    ring
  have hc : Fintype.card T = Fintype.card {b : V // b ≠ v} := by
    rw [hTc,Fintype.card_subtype_compl,Fintype.card_subtype_eq,hN]
    simp only [Nat.add_sub_cancel]
    ring
  have hs := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hi,hc⟩).2
  let H : SimpleGraph A := G.comap Subtype.val
  have hdeg : ∀ a : A, H.degree a = 1 := by
    intro a
    obtain ⟨p,hp⟩ := hs ⟨a.val,a.property.ne.symm⟩
    have hpa : p.2.val = a.val := congrArg Subtype.val hp
    let b : A := p.1
    have hab : H.Adj a b := by
      change G.Adj a.val p.1.val
      exact hpa ▸ p.2.property.1.symm
    have hn : H.neighborFinset a = {b} := by
      ext c
      simp only [SimpleGraph.mem_neighborFinset,Finset.mem_singleton]
      constructor
      · intro hac
        apply Subtype.ext
        exact neighborhood_neighbor_unique hG a.property c.property b.property hac hab
      · intro h
        exact h ▸ hab
    rw [← SimpleGraph.card_neighborFinset_eq_degree,hn]
    simp
  have hp := H.sum_degrees_eq_twice_card_edges
  simp only [hdeg,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] at hp
  have hA : Fintype.card A = q+1 := by
    change Fintype.card (G.neighborSet v) = q+1
    rw [SimpleGraph.card_neighborSet_eq_degree,hv]
  obtain ⟨k,hk⟩ := hq
  omega

#print axioms full_vertex_has_deficient_neighbor
#print axioms common_neighbor_unique
#print axioms cells_disjoint
#print axioms bundles_disjoint
end Erdos60.Completion

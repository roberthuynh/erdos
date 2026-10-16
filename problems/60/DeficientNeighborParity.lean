import GraphStatistics
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace Erdos60.Statistics
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Zero local cycle statistic gives common-neighbor uniqueness only for
opposite pairs containing this fixed vertex. No global C4-free premise. -/
theorem common_neighbor_unique_of_cycle_statistic_zero
    (G : SimpleGraph V) {x : V} (hz : vertexCycleStatistic G x = 0)
    {y a b : V} (hxy : x ≠ y)
    (hxa : G.Adj x a) (hya : G.Adj y a)
    (hxb : G.Adj x b) (hyb : G.Adj y b) : a = b := by
  classical
  have hy : y ∈ Finset.univ.erase x := by simp [hxy.symm]
  have hl := Finset.single_le_sum (f := fun y => (codegree G x y).choose 2)
    (fun y _ => Nat.zero_le _) hy
  change (codegree G x y).choose 2 ≤ vertexCycleStatistic G x at hl
  have hc : (codegree G x y).choose 2 = 0 := by omega
  have hn := Nat.choose_eq_zero_iff.mp hc
  have hcard : (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 1 := by
    change codegree G x y ≤ 1
    omega
  apply Finset.card_le_one.mp hcard a ?_ b ?_
  · simpa only [Finset.mem_inter,SimpleGraph.mem_neighborFinset] using And.intro hxa hya
  · simpa only [Finset.mem_inter,SimpleGraph.mem_neighborFinset] using And.intro hxb hyb

/-- Actual §1 local parity lemma: a high/full vertex with no deficient
neighbor belongs to at least one ordinary C4, even without global C4-freeness. -/
theorem cycle_statistic_pos_of_no_deficient_neighbor
    (G : SimpleGraph V) (q : ℕ) (hq : Even q)
    (hN : Fintype.card V = q^2+q+1) (x : V)
    (hx : q+1 ≤ G.degree x)
    (hneighbor : ∀ a, G.Adj x a → q+1 ≤ G.degree a) :
    1 ≤ vertexCycleStatistic G x := by
  classical
  by_contra hn
  have hz : vertexCycleStatistic G x = 0 := by omega
  have hqpos : 0 < q := by
    by_contra h
    have hq0 : q = 0 := by omega
    have hd := G.degree_lt_card_verts x
    rw [hN,hq0] at hd
    norm_num at hd hx
    omega
  let A := {a : V // G.Adj x a}
  let T := (a : A) × {b : V // G.Adj a.val b ∧ b ≠ x}
  let f : T → {b : V // b ≠ x} := fun p => ⟨p.2.val,p.2.property.2⟩
  have hi : Function.Injective f := by
    intro p r h
    have he : p.2.val = r.2.val := congrArg Subtype.val h
    have ha : p.1.val = r.1.val := common_neighbor_unique_of_cycle_statistic_zero G hz
      p.2.property.2.symm p.1.property p.2.property.1.symm r.1.property
      (he ▸ r.2.property.1.symm)
    cases p with | mk a b =>
      cases r with | mk c d =>
        have hac : a = c := Subtype.ext ha
        subst c
        have hbd : b = d := Subtype.ext he
        subst d
        rfl
  have hA : Fintype.card A = G.degree x := by
    change Fintype.card (G.neighborSet x) = G.degree x
    exact G.card_neighborSet_eq_degree x
  have hfiber : ∀ a : A, Fintype.card {b : V // G.Adj a.val b ∧ b ≠ x} = G.degree a.val - 1 := by
    intro a
    have he : Finset.univ.filter (fun b => G.Adj a.val b ∧ b ≠ x) =
        (G.neighborFinset a.val).erase x := by ext b; simp [and_comm]
    rw [Fintype.card_subtype,he,Finset.card_erase_of_mem
      (show x ∈ G.neighborFinset a.val by simpa using a.property.symm)]
    rw [SimpleGraph.card_neighborFinset_eq_degree]
  have hTl : G.degree x * q ≤ Fintype.card T := by
    rw [show Fintype.card T = ∑ a : A, (G.degree a.val - 1) from by
      simp only [T,Fintype.card_sigma,hfiber]]
    calc
      G.degree x * q = ∑ _a : A, q := by simp [hA]
      _ ≤ _ := Finset.sum_le_sum (fun a _ => by have hh := hneighbor a.val a.property; omega)
  have hTu := Fintype.card_le_of_injective f hi
  have htarget : Fintype.card {b : V // b ≠ x} = q^2+q := by
    rw [Fintype.card_subtype_compl,Fintype.card_subtype_eq,hN]
    omega
  rw [htarget] at hTu
  have hdx : G.degree x = q+1 := by nlinarith
  have hc : Fintype.card T = Fintype.card {b : V // b ≠ x} := by
    rw [htarget]
    rw [hdx] at hTl
    nlinarith
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
    have he : H.neighborFinset a = {b} := by
      ext c
      simp only [SimpleGraph.mem_neighborFinset,Finset.mem_singleton]
      constructor
      · intro hac
        apply Subtype.ext
        exact common_neighbor_unique_of_cycle_statistic_zero G hz a.property.ne
          c.property hac b.property hab
      · intro h
        exact h ▸ hab
    rw [← SimpleGraph.card_neighborFinset_eq_degree,he]
    simp
  have hp := H.sum_degrees_eq_twice_card_edges
  simp only [hdeg,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] at hp
  rw [hA,hdx] at hp
  obtain ⟨k,hk⟩ := hq
  omega

#print axioms common_neighbor_unique_of_cycle_statistic_zero
#print axioms cycle_statistic_pos_of_no_deficient_neighbor
end Erdos60.Statistics

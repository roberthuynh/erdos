import Erdos1017.BinomialLower

namespace Erdos1017.Binomial
open scoped BigOperators

noncomputable def independentVertices (a b : ℕ) : Finset (Fin a ⊕ Fin b) :=
  Finset.univ.map Function.Embedding.inl

noncomputable def coreVertices (a b : ℕ) : Finset (Fin a ⊕ Fin b) :=
  Finset.univ.map Function.Embedding.inr

noncomputable def splitGraph (a b : ℕ) : SimpleGraph (Fin a ⊕ Fin b) where
  Adj x y := x ≠ y ∧ ¬ (x ∈ independentVertices a b ∧ y ∈ independentVertices a b)
  symm := ⟨fun x y h => ⟨h.1.symm,fun hn => h.2 hn.symm⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

theorem split_cover_lower (a b t : ℕ) (ht : 2 ≤ t) (P : Cover (splitGraph a b) t) :
    (a*b.choose (t-1) : ℕ) ≤ P.cost := by
  classical
  let I := independentVertices a b
  let C := coreVertices a b
  have hdis : Disjoint I C := by
    apply Finset.disjoint_left.mpr
    intro x hxI hxC
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hxI
    simpa [C,coreVertices] using hxC
  have hind : ∀ u ∈ I,∀ v ∈ I,¬ (splitGraph a b).Adj u v := by
    intro u hu v hv h
    exact h.2 ⟨hu,hv⟩
  have hcl : ∀ r ∈ I,∀ B ∈ C.powersetCard (t-1),
      (splitGraph a b).IsClique ((insert r B : Finset (Fin a ⊕ Fin b)) : Set (Fin a ⊕ Fin b)) := by
    intro r hr B hB x hx y hy hxy
    refine ⟨hxy,?_⟩
    intro hboth
    have hnot (z : Fin a ⊕ Fin b) (hz : z ∈ B) : z ∉ I := by
      intro hzI
      exact Finset.disjoint_left.mp hdis hzI ((Finset.mem_powersetCard.mp hB).1 hz)
    have hxr : x=r := (Finset.mem_insert.mp hx).resolve_right (fun h => hnot x h hboth.1)
    have hyr : y=r := (Finset.mem_insert.mp hy).resolve_right (fun h => hnot y h hboth.2)
    exact hxy (hxr.trans hyr.symm)
  have h := star_cover_lower (splitGraph a b) I C t ht hdis hind hcl P
  simpa [I,C,independentVertices,coreVertices] using h

theorem maximizing_parameter (n t : ℕ) :
    ∃ a,a ≤ n ∧ maximumCost n t=a*(n-a).choose (t-1) := by
  obtain ⟨a,ha,he⟩ := Finset.exists_mem_eq_sup (Finset.range (n+1))
    (Finset.nonempty_range_iff.mpr (by omega)) (fun a => a*(n-a).choose (t-1))
  exact ⟨a,by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp ha),he⟩

theorem maximizing_positive_parameter (n t : ℕ) (hn : 0 < n) :
    ∃ a,1 ≤ a ∧ a ≤ n ∧ maximumCost n t=a*(n-a).choose (t-1) := by
  obtain ⟨a,ha,he⟩ := maximizing_parameter n t
  by_cases hp : 0 < a
  · exact ⟨a,hp,ha,he⟩
  · have hz : a=0 := by omega
    have hm : maximumCost n t=0 := by simpa [hz] using he
    have hle := le_maximumCost n t 1 hn
    rw [hm] at hle
    exact ⟨1,le_rfl,hn,hm.trans (Nat.eq_zero_of_le_zero hle).symm⟩

/-- Exact finite fractional extremal statement: every graph has an exact
partition below the maximum, and an explicitly sized split graph forces that
same cost for every cover. Covers and decompositions thus share the extremum. -/
theorem exact_fractional_extremum (n t : ℕ) (ht : 2 ≤ t) :
    (∀ G : SimpleGraph (Fin n),∃ P : Partition G (fun _ => 1) t,
      P.cost ≤ maximumCost n t) ∧
    (∃ a b : ℕ,a+b=n ∧
      (∃ P : Partition (splitGraph a b) (fun _ => 1) t,P.cost=maximumCost n t) ∧
      (∀ Q : Cover (splitGraph a b) t,(maximumCost n t : ℝ) ≤ Q.cost)) := by
  refine ⟨?_,?_⟩
  · intro G
    simpa using graph_upper G t ht
  · obtain ⟨a,ha,hmax⟩ := maximizing_parameter n t
    have hsum : a+(n-a)=n := Nat.add_sub_of_le ha
    obtain ⟨P,hP⟩ := graph_upper (splitGraph a (n-a)) t ht
    have hc : Fintype.card (Fin a ⊕ Fin (n-a))=n := by simp [hsum]
    rw [hc] at hP
    have hl : ∀ Q : Cover (splitGraph a (n-a)) t,(maximumCost n t : ℝ) ≤ Q.cost := by
      intro Q
      rw [hmax]
      exact split_cover_lower a (n-a) t ht Q
    refine ⟨a,n-a,hsum,⟨P,?_⟩,hl⟩
    exact le_antisymm hP (hl P.toCover)

end Erdos1017.Binomial

import GraphStatistics

/-! Source §5 equation (14), actual neighborhood unions. Repeated membership
is charged to actual common-neighbor pairs and therefore actual cycles through v.
No inclusion-exclusion/cycle-cost inequality is assumed. -/
namespace Erdos60.Statistics
open Finset
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def puncturedNeighborUnion (G : SimpleGraph V) (v : V) (I : Finset V) : Finset V :=
  I.biUnion fun i => (G.neighborFinset i).erase v
noncomputable def unionMultiplicity (G : SimpleGraph V) (v : V) (I : Finset V) (r : V) : ℕ :=
  (I.filter fun i => r ∈ (G.neighborFinset i).erase v).card

theorem unionMultiplicity_sum (G : SimpleGraph V) (v : V) (I : Finset V) :
    (∑ i ∈ I, ((G.neighborFinset i).erase v).card) =
      ∑ r ∈ Finset.univ.erase v, unionMultiplicity G v I r := by
  classical
  have hall : (∑ i ∈ I, ((G.neighborFinset i).erase v).card) =
      ∑ r : V, unionMultiplicity G v I r := by
    unfold unionMultiplicity
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_boole]
    congr 1
    ext x
    simp
  rw [hall]
  have he := Finset.sum_erase_add Finset.univ (unionMultiplicity G v I) (by simp : v ∈ Finset.univ)
  simpa [unionMultiplicity] using he.symm

theorem unionMultiplicity_le_codegree (G : SimpleGraph V) (v : V) (I : Finset V)
    (hI : I ⊆ G.neighborFinset v) (r : V) :
    unionMultiplicity G v I r ≤ codegree G v r := by
  classical
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hiI,hir⟩ := Finset.mem_filter.mp hi
  apply Finset.mem_inter.mpr
  refine ⟨hI hiI,?_⟩
  have hri := (Finset.mem_erase.mp hir).2
  simpa only [SimpleGraph.mem_neighborFinset,SimpleGraph.adj_comm] using hri

/-- Repetition cost is bounded by the exact actual cycle count through v. -/
theorem punctured_union_overlap_bound (G : SimpleGraph V) (v : V) (I : Finset V)
    (hI : I ⊆ G.neighborFinset v) :
    (∑ i ∈ I, ((G.neighborFinset i).erase v).card) ≤
      (puncturedNeighborUnion G v I).card + vertexCycleStatistic G v := by
  classical
  let U := puncturedNeighborUnion G v I
  have hscalar : ∀ r, unionMultiplicity G v I r ≤
      (if r ∈ U then 1 else 0) + (codegree G v r).choose 2 := by
    intro r
    by_cases hr : r ∈ U
    · have hl := choose_two_lower (unionMultiplicity G v I r)
      have hm := Nat.choose_le_choose 2 (unionMultiplicity_le_codegree G v I hI r)
      simp only [hr,ite_true]
      omega
    · have hz : unionMultiplicity G v I r = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨i,hi⟩
        obtain ⟨hiI,hir⟩ := Finset.mem_filter.mp hi
        exact hr (Finset.mem_biUnion.mpr ⟨i,hiI,hir⟩)
      simp [hr,hz]
  rw [unionMultiplicity_sum]
  have hs := Finset.sum_le_sum (s := Finset.univ.erase v) (fun r hr => hscalar r)
  rw [Finset.sum_add_distrib,Finset.sum_boole] at hs
  have hfilter : {r ∈ Finset.univ.erase v | r ∈ U} = U := by
    ext r
    have hvU : v ∉ U := by
      intro hv
      obtain ⟨i,hi,hv⟩ := Finset.mem_biUnion.mp hv
      exact (Finset.mem_erase.mp hv).1 rfl
    simp only [Finset.mem_filter,Finset.mem_erase,Finset.mem_univ,and_true]
    constructor
    · exact fun h => h.2
    · intro hr
      exact ⟨fun he => hvU (he ▸ hr),hr⟩
  rw [hfilter] at hs
  exact hs

/-- Source equation (14): q|I| ≤ |⋃i∈I(N(i)\{v})|+c(v), for actual
nondeficient neighbors of v. Here c(v) is the exact ordinary cycle statistic. -/
theorem nondeficient_neighbor_union (G : SimpleGraph V) (q : ℕ) (v : V)
    (I : Finset V) (hI : I ⊆ G.neighborFinset v)
    (hdeg : ∀ i ∈ I, q+1 ≤ G.degree i) :
    q * I.card ≤ (puncturedNeighborUnion G v I).card + vertexCycleStatistic G v := by
  have hlow : q * I.card ≤ ∑ i ∈ I, ((G.neighborFinset i).erase v).card := by
    calc
      _ = ∑ i ∈ I, q := by simp [Nat.mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have hvi : v ∈ G.neighborFinset i := by
          have h := hI hi
          simpa only [SimpleGraph.mem_neighborFinset,SimpleGraph.adj_comm] using h
        rw [Finset.card_erase_of_mem hvi,G.card_neighborFinset_eq_degree]
        have hd := hdeg i hi
        omega
  exact hlow.trans (punctured_union_overlap_bound G v I hI)

end Erdos60.Statistics

import C4Counting
import Mathlib.Data.Finset.Prod

set_option linter.unusedSimpArgs false
namespace Erdos60.Counting
open Finset
open scoped Classical
variable {V : Type*} [DecidableEq V]

/-- Vertex support of an ordinary edge-set cycle. -/
def cycleVertices (C : Finset (Sym2 V)) : Finset V := C.biUnion Sym2.toFinset

theorem fourEdges_vertices (a b c d : V) :
    cycleVertices (fourEdges a b c d) = {a,b,c,d} := by
  ext x
  simp [cycleVertices,fourEdges,Sym2.toFinset_mk_eq,or_comm,or_left_comm]

theorem fourEdges_vertices_card (a b c d : V) (hd : [a,b,c,d].Nodup) :
    (cycleVertices (fourEdges a b c d)).card = 4 := by
  have hne : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
    simpa only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true,and_assoc] using hd
  obtain ⟨hab,hac,had,hbc,hbd,hcd⟩ := hne
  rw [fourEdges_vertices]
  simp [hab,hac,had,hbc,hbd,hcd]

theorem IsFourCycle.vertices_card {C : Finset (Sym2 V)} (hC : IsFourCycle C) :
    (cycleVertices C).card = 4 := by
  obtain ⟨a,b,c,d,hd,rfl⟩ := hC
  exact fourEdges_vertices_card a b c d hd

/-- Unordered distinct-vertex pairs in a finite vertex set. -/
def vertexPairs (S : Finset V) : Finset (Sym2 V) :=
  S.offDiag.image (fun ab => s(ab.1,ab.2))

/-- Opposite pairs of the cycle edge-set, independent of ambient diagonals. -/
def cycleOppositePairs (C : Finset (Sym2 V)) : Finset (Sym2 V) :=
  vertexPairs (cycleVertices C) \ C

@[simp] theorem mem_vertexPairs (S : Finset V) (a b : V) :
    s(a,b) ∈ vertexPairs S ↔ a ∈ S ∧ b ∈ S ∧ a ≠ b := by
  simp only [vertexPairs,Finset.mem_image,Finset.mem_offDiag]
  constructor
  · rintro ⟨⟨x,y⟩,⟨hx,hy,hxy⟩,he⟩
    simp only [Sym2.eq_iff] at he
    rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨hx,hy,hxy⟩
    · exact ⟨hy,hx,hxy.symm⟩
  · rintro ⟨ha,hb,hab⟩
    exact ⟨(a,b),⟨ha,hb,hab⟩,rfl⟩

theorem fourEdges_oppositePairs (a b c d : V) (hd : [a,b,c,d].Nodup) :
    cycleOppositePairs (fourEdges a b c d) = {s(a,c),s(b,d)} := by
  have hne : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
    simpa only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true,and_assoc] using hd
  obtain ⟨hab,hac,had,hbc,hbd,hcd⟩ := hne
  apply Finset.Subset.antisymm
  · intro e he
    have hp := (Finset.mem_sdiff.mp he).1
    have hn := (Finset.mem_sdiff.mp he).2
    change e ∈ vertexPairs (cycleVertices (fourEdges a b c d)) at hp
    revert hp hn
    refine Sym2.inductionOn e (fun x y => ?_)
    intro hn hp
    rw [fourEdges_vertices,mem_vertexPairs] at hp
    obtain ⟨hx,hy,hxy⟩ := hp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl <;>
      simp_all [fourEdges,Sym2.eq_iff]
  · intro e he
    simp only [Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · apply Finset.mem_sdiff.mpr
      constructor
      · rw [fourEdges_vertices,mem_vertexPairs]
        simp [hac]
      · simp [fourEdges,Sym2.eq_iff,hab,hac,had,hbc,hbd,hcd,
          Ne.symm hab,Ne.symm hac,Ne.symm had,Ne.symm hbc,Ne.symm hbd,Ne.symm hcd]
    · apply Finset.mem_sdiff.mpr
      constructor
      · rw [fourEdges_vertices,mem_vertexPairs]
        simp [hbd]
      · simp [fourEdges,Sym2.eq_iff,hab,hac,had,hbc,hbd,hcd,
          Ne.symm hab,Ne.symm hac,Ne.symm had,Ne.symm hbc,Ne.symm hbd,Ne.symm hcd]

theorem IsFourCycle.oppositePairs_card {C : Finset (Sym2 V)} (hC : IsFourCycle C) :
    (cycleOppositePairs C).card = 2 := by
  obtain ⟨a,b,c,d,hd,rfl⟩ := hC
  rw [fourEdges_oppositePairs a b c d hd]
  have hab : a ≠ b := by
    intro h
    exact (List.nodup_cons.mp hd).1 (by simp [h])
  have had : a ≠ d := by
    intro h
    exact (List.nodup_cons.mp hd).1 (by simp [h])
  have hne : s(a,c) ≠ s(b,d) := by
    simp [Sym2.eq_iff,hab,had]
  simp [hne]

end Erdos60.Counting

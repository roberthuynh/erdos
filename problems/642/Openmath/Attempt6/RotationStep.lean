import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# One actual Pósa rotation in the original graph

Split the original path as `p ++ (w,u) ++ q`, with `p : x ⟶ w`
and `q : u ⟶ y`. A chord `(x,u)` replaces `(w,u)`, and the new
path is `reverse p ++ (x,u) ++ q : w ⟶ y`.
This is the same-path case of Definition 2.1 in arXiv:2507.20500v1.
The caller supplies an actual path decomposition, not rotation conclusions.
This file does not construct the forest rotation family or a sampler.
-/

namespace Erdos585.Attempt6

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {x w u y : V}

/-- The original path with its pivot-predecessor edge displayed. -/
def rotationOriginal (p : G.Walk x w) (q : G.Walk u y) (hwu : G.Adj w u) :
    G.Walk x y := p.append (.cons hwu q)

/-- The rotated path uses only edges of `G`, including its supplied chord. -/
def rotatePathStep (p : G.Walk x w) (q : G.Walk u y) (hxu : G.Adj x u) :
    G.Walk w y := p.reverse.append (.cons hxu q)

theorem rotationOriginal_support (p : G.Walk x w) (q : G.Walk u y)
    (hwu : G.Adj w u) :
    (rotationOriginal p q hwu).support = p.support ++ q.support := by
  simp [rotationOriginal, Walk.support_append]

theorem rotatePathStep_support (p : G.Walk x w) (q : G.Walk u y)
    (hxu : G.Adj x u) :
    (rotatePathStep p q hxu).support = p.support.reverse ++ q.support := by
  simp [rotatePathStep, Walk.support_append, Walk.support_reverse]

/-- Reversing the prefix preserves simplicity because the two displayed
segments have disjoint vertex supports in the original simple path. -/
theorem rotatePathStep_isPath (p : G.Walk x w) (q : G.Walk u y)
    (hwu : G.Adj w u) (hxu : G.Adj x u)
    (hp : (rotationOriginal p q hwu).IsPath) :
    (rotatePathStep p q hxu).IsPath := by
  rw [Walk.isPath_def, rotatePathStep_support, List.nodup_append']
  have h := hp.support_nodup
  rw [rotationOriginal_support, List.nodup_append'] at h
  exact ⟨List.nodup_reverse.mpr h.1, h.2.1, by simpa using h.2.2⟩

/-- The operation retains exactly the original vertices. -/
theorem rotatePathStep_sameSupport (p : G.Walk x w) (q : G.Walk u y)
    (hwu : G.Adj w u) (hxu : G.Adj x u) :
    {z | z ∈ (rotatePathStep p q hxu).support} =
      {z | z ∈ (rotationOriginal p q hwu).support} := by
  ext z
  simp [rotatePathStep_support, rotationOriginal_support]

/-- Ordered edge lists display the exact local replacement and reversal. -/
theorem rotatePathStep_edges (p : G.Walk x w) (q : G.Walk u y)
    (hxu : G.Adj x u) :
    (rotatePathStep p q hxu).edges = p.edges.reverse ++ s(x, u) :: q.edges := by
  simp [rotatePathStep, Walk.edges_append, Walk.edges_reverse]

theorem rotationOriginal_edges (p : G.Walk x w) (q : G.Walk u y)
    (hwu : G.Adj w u) :
    (rotationOriginal p q hwu).edges = p.edges ++ s(w, u) :: q.edges := by
  simp [rotationOriginal, Walk.edges_append]

/-- The deleted edge occurs in neither retained segment. -/
theorem rotationOriginal_deleted_not_retained (p : G.Walk x w) (q : G.Walk u y)
    (hwu : G.Adj w u) (hp : (rotationOriginal p q hwu).IsPath) :
    s(w, u) ∉ p.edges ∧ s(w, u) ∉ q.edges := by
  have h := hp.support_nodup
  rw [rotationOriginal_support, List.nodup_append'] at h
  constructor
  · intro he
    exact List.disjoint_left.mp h.2.2 (p.snd_mem_support_of_mem_edges he) q.start_mem_support
  · intro he
    exact List.disjoint_left.mp h.2.2 p.end_mem_support (q.fst_mem_support_of_mem_edges he)

/-- A genuine chord is absent from the original path. The explicit `x ≠ w`
hypothesis excludes the degenerate move replacing the same edge. -/
theorem rotatePathStep_chord_not_original (p : G.Walk x w) (q : G.Walk u y)
    (hwu : G.Adj w u) (hxu : G.Adj x u) (hxw : x ≠ w)
    (hp : (rotationOriginal p q hwu).IsPath) :
    s(x, u) ∉ (rotationOriginal p q hwu).edges := by
  have h := hp.support_nodup
  rw [rotationOriginal_support, List.nodup_append'] at h
  have hn₁ : s(x, u) ∉ p.edges := by
    intro he
    exact List.disjoint_left.mp h.2.2 (p.snd_mem_support_of_mem_edges he) q.start_mem_support
  have hn₂ : s(x, u) ∉ q.edges := by
    intro he
    exact List.disjoint_left.mp h.2.2 p.start_mem_support (q.fst_mem_support_of_mem_edges he)
  have hne : s(x, u) ≠ s(w, u) := by
    intro he
    rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨h, _⟩
    · exact hxw h
    · exact hxu.ne h
  simpa [rotationOriginal_edges] using And.intro hn₁ (And.intro hne hn₂)

/-- Exact undirected edge exchange, derived from simplicity of the original
path. No disjointness or exchange fact is assumed. This equality also covers
the degenerate `x = w` case, which reinserts the deleted edge. -/
theorem rotatePathStep_edgeSet (p : G.Walk x w) (q : G.Walk u y)
    (hwu : G.Adj w u) (hxu : G.Adj x u)
    (hp : (rotationOriginal p q hwu).IsPath) :
    (rotatePathStep p q hxu).edgeSet =
      insert s(x, u) ((rotationOriginal p q hwu).edgeSet \ {s(w, u)}) := by
  obtain ⟨hn₁, hn₂⟩ := rotationOriginal_deleted_not_retained p q hwu hp
  ext e
  simp only [Walk.mem_edgeSet, rotatePathStep_edges, rotationOriginal_edges,
    List.mem_append, List.mem_reverse, List.mem_cons, Set.mem_insert_iff,
    Set.mem_sdiff, Set.mem_singleton_iff]
  by_cases he : e = s(w, u)
  · subst e
    simp [hn₁, hn₂, eq_comm]
  · simp only [he, false_or]
    tauto

/-- A nontrivial rotation deletes the displayed old edge completely. -/
theorem rotatePathStep_deleted_absent (p : G.Walk x w) (q : G.Walk u y)
    (hwu : G.Adj w u) (hxu : G.Adj x u) (hxw : x ≠ w)
    (hp : (rotationOriginal p q hwu).IsPath) :
    s(w, u) ∉ (rotatePathStep p q hxu).edgeSet := by
  rw [rotatePathStep_edgeSet p q hwu hxu hp]
  simp only [Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff,
    not_true_eq_false, and_false, or_false]
  rw [Sym2.eq_iff]
  rintro (⟨h, _⟩ | ⟨_, h⟩)
  · exact hxw h.symm
  · exact hxu.ne h.symm

/-- The number of edges is preserved, including degenerate moves. -/
theorem rotatePathStep_length (p : G.Walk x w) (q : G.Walk u y)
    (hwu : G.Adj w u) (hxu : G.Adj x u) :
    (rotatePathStep p q hxu).length = (rotationOriginal p q hwu).length := by
  simp [rotatePathStep, rotationOriginal]

                                                                        
                                                                             
                                                                            
theorem rotatePathStep_verified (p : G.Walk x w) (q : G.Walk u y)
    (hwu : G.Adj w u) (hxu : G.Adj x u) (hxw : x ≠ w) (huy : u ≠ y)
    (hp : (rotationOriginal p q hwu).IsPath) :
    (rotatePathStep p q hxu).IsPath ∧
    {z | z ∈ (rotatePathStep p q hxu).support} =
      {z | z ∈ (rotationOriginal p q hwu).support} ∧
    (rotatePathStep p q hxu).edgeSet =
      insert s(x, u) ((rotationOriginal p q hwu).edgeSet \ {s(w, u)}) ∧
    s(x, u) ∉ (rotationOriginal p q hwu).edgeSet ∧
    s(w, u) ∉ (rotatePathStep p q hxu).edgeSet ∧
    (rotatePathStep p q hxu).length = (rotationOriginal p q hwu).length ∧
    ¬ q.Nil := by
  exact ⟨rotatePathStep_isPath p q hwu hxu hp,
    rotatePathStep_sameSupport p q hwu hxu,
    rotatePathStep_edgeSet p q hwu hxu hp,
    rotatePathStep_chord_not_original p q hwu hxu hxw hp,
    rotatePathStep_deleted_absent p q hwu hxu hxw hp,
    rotatePathStep_length p q hwu hxu, Walk.not_nil_of_ne huy⟩

end Erdos585.Attempt6

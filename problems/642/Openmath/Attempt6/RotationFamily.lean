import Openmath.Attempt6.RotationStep
import Openmath.Attempt6.MinimumForest
import Mathlib.Combinatorics.SimpleGraph.Bipartite

   
                                          

                                                                            
                                                                              
                                                                              
                                                                           

                                                                              
                                                                            
                                                                              
                                                                              
                                                                              
                                                                     
                                                                                
  

namespace Erdos585.Attempt6

open SimpleGraph

universe u v

variable {V : Type u} {G : SimpleGraph V}

/-- A walk with its actual endpoints retained in the state. -/
structure RotationPath (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish

namespace RotationPath

def vertexSet (a : RotationPath G) : Set V := {z | z ∈ a.walk.support}

def edgeSet (a : RotationPath G) : Set (Sym2 V) := a.walk.edgeSet

theorem edges_original (a : RotationPath G) : a.edgeSet ⊆ G.edgeSet :=
  fun _ h => a.walk.edges_subset_edgeSet h

end RotationPath

                                                                           
                                                                                  
inductive PathRotation : RotationPath G → RotationPath G → Prop
  | step {x w u y : V} (p : G.Walk x w) (q : G.Walk u y)
      (hwu : G.Adj w u) (hxu : G.Adj x u) :
      PathRotation ⟨x, y, rotationOriginal p q hwu⟩
        ⟨w, y, rotatePathStep p q hxu⟩

namespace PathRotation

variable {a b : RotationPath G}

theorem sameSupport (h : PathRotation a b) : b.vertexSet = a.vertexSet := by
  cases h with
  | step p q hwu hxu => exact rotatePathStep_sameSupport p q hwu hxu

theorem isPath (h : PathRotation a b) (ha : a.walk.IsPath) : b.walk.IsPath := by
  cases h with
  | step p q hwu hxu => exact rotatePathStep_isPath p q hwu hxu ha

theorem length (h : PathRotation a b) : b.walk.length = a.walk.length := by
  cases h with
  | step p q hwu hxu => exact rotatePathStep_length p q hwu hxu

theorem finish (h : PathRotation a b) : b.finish = a.finish := by
  cases h
  rfl

/-- Both old and new moving endpoints are neighbors of the same pivot. -/
theorem start_shore {S T : Set V} (h : PathRotation a b)
    (hG : G.IsBipartiteWith S T) (ha : a.start ∈ S) : b.start ∈ S := by
  cases h with
  | step p q hwu hxu => exact hG.mem_of_mem_adj' (hG.mem_of_mem_adj ha hxu) hwu

end PathRotation

/-- Any finite sequence of concrete same-path rotations, including no moves. -/
abbrev PathRotationReachable := Relation.ReflTransGen (@PathRotation V G)

namespace PathRotationReachable

variable {a b : RotationPath G}

theorem sameSupport (h : PathRotationReachable a b) : b.vertexSet = a.vertexSet := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact hstep.sameSupport.trans ih

theorem isPath (h : PathRotationReachable a b) (ha : a.walk.IsPath) : b.walk.IsPath := by
  induction h with
  | refl => exact ha
  | tail _ hstep ih => exact hstep.isPath ih

theorem length (h : PathRotationReachable a b) : b.walk.length = a.walk.length := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact hstep.length.trans ih

theorem finish (h : PathRotationReachable a b) : b.finish = a.finish := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact hstep.finish.trans ih

theorem start_shore {S T : Set V} (h : PathRotationReachable a b)
    (hG : G.IsBipartiteWith S T) (ha : a.start ∈ S) : b.start ∈ S := by
  induction h with
  | refl => exact ha
  | tail _ hstep ih => exact hstep.start_shore hG ih

/-- The full invariant bundle for a finite sequence. Exact support is a vertex
statement; the edge set can change, but it always stays in the original graph. -/
theorem verified {S T : Set V} (h : PathRotationReachable a b)
    (ha : a.walk.IsPath) (hG : G.IsBipartiteWith S T) (hS : a.start ∈ S) :
    b.walk.IsPath ∧ b.vertexSet = a.vertexSet ∧ b.edgeSet ⊆ G.edgeSet ∧
      b.walk.length = a.walk.length ∧ b.finish = a.finish ∧ b.start ∈ S :=
  ⟨h.isPath ha, h.sameSupport, b.edges_original, h.length, h.finish, h.start_shore hG hS⟩

end PathRotationReachable

/-- A spanning partition of the vertices into actual simple paths. An isolate
is represented by a nil walk and still occupies one component index. -/
structure IndexedPathPartition (G : SimpleGraph V) (ι : Type v) where
  path : ι → RotationPath G
  simple : ∀ i, (path i).walk.IsPath
  disjoint : ∀ i j, i ≠ j → Disjoint (path i).vertexSet (path j).vertexSet
  spanning : ∀ z, ∃ i, z ∈ (path i).vertexSet

/-- Each component undergoes a finite sequence of actual same-path rotations. -/
def ComponentwiseRotation {ι : Type v} (a b : ι → RotationPath G) : Prop :=
  ∀ i, PathRotationReachable (a i) (b i)

namespace ComponentwiseRotation

variable {ι : Type v} {a b : ι → RotationPath G}

theorem simple (h : ComponentwiseRotation a b) (ha : ∀ i, (a i).walk.IsPath) :
    ∀ i, (b i).walk.IsPath := fun i => (h i).isPath (ha i)

theorem disjoint (h : ComponentwiseRotation a b)
    (ha : ∀ i j, i ≠ j → Disjoint (a i).vertexSet (a j).vertexSet) :
    ∀ i j, i ≠ j → Disjoint (b i).vertexSet (b j).vertexSet := by
  intro i j hij
  rw [(h i).sameSupport, (h j).sameSupport]
  exact ha i j hij

theorem spanning (h : ComponentwiseRotation a b)
    (ha : ∀ z, ∃ i, z ∈ (a i).vertexSet) : ∀ z, ∃ i, z ∈ (b i).vertexSet := by
  intro z
  obtain ⟨i, hi⟩ := ha z
  exact ⟨i, (h i).sameSupport.symm ▸ hi⟩

/-- Reconstruct the spanning simple-path partition from the derived invariants. -/
def partition (a : IndexedPathPartition G ι) (b : ι → RotationPath G)
    (h : ComponentwiseRotation a.path b) : IndexedPathPartition G ι where
  path := b
  simple := h.simple a.simple
  disjoint := h.disjoint a.disjoint
  spanning := h.spanning a.spanning

theorem endpoint_shore {S T : Set V} (h : ComponentwiseRotation a b)
    (hG : G.IsBipartiteWith S T) (ha : ∀ i, (a i).start ∈ S) :
    ∀ i, (b i).start ∈ S := fun i => (h i).start_shore hG (ha i)

/-- Every component remains nonempty as a vertex set, including an isolate. -/
theorem component_nonempty (_h : ComponentwiseRotation a b) (i : ι) :
    (b i).vertexSet.Nonempty := ⟨(b i).start, (b i).walk.start_mem_support⟩

end ComponentwiseRotation

namespace SpanningLinearForest

variable [Fintype V]

/-- The actual forest components supply the concrete initial path partition. -/
noncomputable def pathPartition (F : SpanningLinearForest G) :
    IndexedPathPartition G F.graph.ConnectedComponent where
  path := fun C => ⟨(F.componentPath C).start, (F.componentPath C).finish,
    (F.componentPath C).walk⟩
  simple := fun C => (F.componentPath C).simple
  disjoint := by
    intro C D hCD
    rw [Set.disjoint_left]
    intro z hzC hzD
    exact F.component_disjoint hCD |>.le_bot ⟨
      ((F.componentPath C).support_exact z).mp hzC,
      ((F.componentPath D).support_exact z).mp hzD⟩
  spanning := by
    intro z
    obtain ⟨C, hC, _⟩ := F.componentPath_unique_cover z
    exact ⟨C, hC⟩

/-- Rotating each actual component produces a spanning partition with precisely
the same component index type, hence the original component count. -/
noncomputable def rotatedPathPartition (F : SpanningLinearForest G)
    (b : F.graph.ConnectedComponent → RotationPath G)
    (h : ComponentwiseRotation F.pathPartition.path b) :
    IndexedPathPartition G F.graph.ConnectedComponent := h.partition F.pathPartition b

theorem rotatedPathPartition_indexCount (F : SpanningLinearForest G)
    (b : F.graph.ConnectedComponent → RotationPath G)
    (_h : ComponentwiseRotation F.pathPartition.path b) :
    Nat.card F.graph.ConnectedComponent = F.componentCount := rfl

/-- Numeric minimality is preserved by retaining the actual component index
type. This does not rebuild a graph from the rotated path partition. -/
theorem rotatedPathPartition_minimumCount (F : SpanningLinearForest G)
    (hF : F.IsMinimum) (b : F.graph.ConnectedComponent → RotationPath G)
    (_h : ComponentwiseRotation F.pathPartition.path b) (F' : SpanningLinearForest G) :
    Nat.card F.graph.ConnectedComponent ≤ F'.componentCount := hF F'

end SpanningLinearForest

/-- Concatenating vertex supports records every occurrence, so `Nodup` means
both simple component paths and disjoint supports between components. -/
def rotationForestVertices (F : List (RotationPath G)) : List V :=
  F.flatMap fun p => p.walk.support

def IsPathForest (F : List (RotationPath G)) : Prop := (rotationForestVertices F).Nodup

def IsSpanningPathForest (F : List (RotationPath G)) : Prop :=
  IsPathForest F ∧ ∀ z, z ∈ rotationForestVertices F

namespace IndexedPathPartition

variable {ι : Type v}

/-- Enumerating every component once gives the list representation used by the
full forest rotation relation. Simplicity and disjointness are derived. -/
theorem enumerate_spanning (a : IndexedPathPartition G ι) (l : List ι)
    (hl : l.Nodup) (hcover : ∀ i, i ∈ l) : IsSpanningPathForest (l.map a.path) := by
  constructor
  · change (List.flatMap (fun p : RotationPath G => p.walk.support) (l.map a.path)).Nodup
    rw [List.flatMap_map, List.nodup_flatMap]
    constructor
    · intro i hi
      exact (a.simple i).support_nodup
    · exact hl.imp fun {i j} hij => List.disjoint_left.mpr
        (fun z hzi hzj => Set.disjoint_left.mp (a.disjoint i j hij) hzi hzj)
  · intro z
    obtain ⟨i, hi⟩ := a.spanning z
    change z ∈ List.flatMap (fun p : RotationPath G => p.walk.support) (l.map a.path)
    rw [List.flatMap_map, List.mem_flatMap]
    exact ⟨i, hcover i, hi⟩

end IndexedPathPartition

namespace SpanningLinearForest

variable [Fintype V]

/-- Enumerate the genuine chosen component paths of an actual forest. -/
noncomputable def pathList (F : SpanningLinearForest G) : List (RotationPath G) := by
  classical
  letI : Fintype F.graph.ConnectedComponent := Fintype.ofFinite _
  exact Finset.univ.toList.map F.pathPartition.path

theorem pathList_spanning (F : SpanningLinearForest G) : IsSpanningPathForest F.pathList := by
  classical
  let : Fintype F.graph.ConnectedComponent := Fintype.ofFinite _
  exact F.pathPartition.enumerate_spanning Finset.univ.toList (Finset.nodup_toList _)
    (fun i => by simp)

theorem pathList_length (F : SpanningLinearForest G) : F.pathList.length = F.componentCount := by
  classical
  let : Fintype F.graph.ConnectedComponent := Fintype.ofFinite _
  simp [pathList, componentCount, Nat.card_eq_fintype_card]

end SpanningLinearForest

/-- Each component contributes two endpoint tokens, also when its walk is nil. -/
def rotationForestEndpoints : List (RotationPath G) → Multiset V
  | [] => 0
  | p :: F => {p.start} + {p.finish} + rotationForestEndpoints F

/-- Every path contributes exactly two tokens, including an isolate. -/
theorem rotationForestEndpoints_card (F : List (RotationPath G)) :
    (rotationForestEndpoints F).card = 2 * F.length := by
  induction F with
  | nil => simp [rotationForestEndpoints]
  | cons p F ih => simp [rotationForestEndpoints, ih]; omega

theorem rotationForestEndpoints_append (F F' : List (RotationPath G)) :
    rotationForestEndpoints (F ++ F') = rotationForestEndpoints F + rotationForestEndpoints F' := by
  induction F with
  | nil => simp [rotationForestEndpoints]
  | cons p F ih => simp [rotationForestEndpoints, ih]

theorem rotationForestEndpoints_perm {F F' : List (RotationPath G)} (h : F.Perm F') :
    rotationForestEndpoints F = rotationForestEndpoints F' := by
  induction h with
  | nil => rfl
  | cons p h ih => simp [rotationForestEndpoints, ih]
  | swap p q F => simp only [rotationForestEndpoints]; ac_rfl
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Concrete same-path and different-path forest rotations, with list reordering
and path reversal as bookkeeping changes to the same represented forest. -/
inductive ForestRotation : List (RotationPath G) → List (RotationPath G) → Prop
  | reorder {F F' : List (RotationPath G)} (h : F.Perm F') : ForestRotation F F'
  | reverse (pre post : List (RotationPath G)) {x y : V} (p : G.Walk x y) :
      ForestRotation (pre ++ ⟨x, y, p⟩ :: post) (pre ++ ⟨y, x, p.reverse⟩ :: post)
  | within (pre post : List (RotationPath G)) {x w u y : V}
      (p : G.Walk x w) (q : G.Walk u y) (hwu : G.Adj w u) (hxu : G.Adj x u) :
      ForestRotation (pre ++ ⟨x, y, rotationOriginal p q hwu⟩ :: post)
        (pre ++ ⟨w, y, rotatePathStep p q hxu⟩ :: post)
  | between (pre post : List (RotationPath G)) {x y z w u t : V}
      (r : G.Walk x y) (p : G.Walk z w) (q : G.Walk u t)
      (hwu : G.Adj w u) (hxu : G.Adj x u) :
      ForestRotation (pre ++ ⟨x, y, r⟩ :: ⟨z, t, rotationOriginal p q hwu⟩ :: post)
        (pre ++ ⟨y, t, r.reverse.append (.cons hxu q)⟩ :: ⟨z, w, p⟩ :: post)

namespace ForestRotation

variable {F F' : List (RotationPath G)}

/-- Exact token exchange for the same-path move. -/
theorem within_endpoints (pre post : List (RotationPath G)) {x w u y : V}
    (p : G.Walk x w) (q : G.Walk u y) (hwu : G.Adj w u) (hxu : G.Adj x u) :
    rotationForestEndpoints (pre ++ ⟨w, y, rotatePathStep p q hxu⟩ :: post) + {x} =
      rotationForestEndpoints (pre ++ ⟨x, y, rotationOriginal p q hwu⟩ :: post) + {w} := by
  simp only [rotationForestEndpoints_append, rotationForestEndpoints]
  ac_rfl

/-- Exact token exchange for the different-path move, including isolates. -/
theorem between_endpoints (pre post : List (RotationPath G)) {x y z w u t : V}
    (r : G.Walk x y) (p : G.Walk z w) (q : G.Walk u t)
    (hwu : G.Adj w u) (hxu : G.Adj x u) :
    rotationForestEndpoints
      (pre ++ ⟨y, t, r.reverse.append (.cons hxu q)⟩ :: ⟨z, w, p⟩ :: post) + {x} =
      rotationForestEndpoints
        (pre ++ ⟨x, y, r⟩ :: ⟨z, t, rotationOriginal p q hwu⟩ :: post) + {w} := by
  simp only [rotationForestEndpoints_append, rotationForestEndpoints]
  ac_rfl

/-- The different-path move redistributes the two supports rather than
preserving each one individually. Their disjoint union is exactly preserved. -/
theorem vertices_perm (h : ForestRotation F F') :
    (rotationForestVertices F').Perm (rotationForestVertices F) := by
  cases h with
  | reorder h => exact h.symm.flatMap fun _ _ => List.Perm.refl _
  | reverse pre post p =>
    simpa [rotationForestVertices, Walk.support_reverse, List.append_assoc] using
      ((List.reverse_perm p.support).append_right (rotationForestVertices post)).append_left
        (rotationForestVertices pre)
  | within pre post p q hwu hxu =>
    simpa [rotationForestVertices, rotatePathStep_support, rotationOriginal_support,
      List.append_assoc] using
      (((List.reverse_perm p.support).append_right q.support).append_right
        (rotationForestVertices post)).append_left (rotationForestVertices pre)
  | between pre post r p q hwu hxu =>
    have hlocal : (r.support.reverse ++ q.support ++ p.support).Perm
        (r.support ++ p.support ++ q.support) := by
      have h₁ := (List.reverse_perm r.support).append
        (List.perm_append_comm (l₁ := q.support) (l₂ := p.support))
      simpa only [List.append_assoc] using h₁
    simpa [rotationForestVertices, rotationOriginal_support, Walk.support_append,
      Walk.support_reverse, List.append_assoc] using
      (hlocal.append_right (rotationForestVertices post)).append_left (rotationForestVertices pre)

theorem pathForest (h : ForestRotation F F') (hF : IsPathForest F) : IsPathForest F' :=
  h.vertices_perm.symm.nodup hF

theorem spanning (h : ForestRotation F F') (hF : IsSpanningPathForest F) :
    IsSpanningPathForest F' :=
  ⟨h.pathForest hF.1, fun z => h.vertices_perm.mem_iff.mpr (hF.2 z)⟩

theorem componentCount (h : ForestRotation F F') : F'.length = F.length := by
  cases h with
  | reorder h => exact h.length_eq.symm
  | reverse pre post p => simp
  | within pre post p q hwu hxu => simp
  | between pre post r p q hwu hxu => simp

end ForestRotation

/-- Full finite sequences of the actual forest moves above. -/
abbrev ForestRotationReachable := Relation.ReflTransGen (@ForestRotation V G)

namespace ForestRotationReachable

variable {F F' : List (RotationPath G)}

theorem vertices_perm (h : ForestRotationReachable F F') :
    (rotationForestVertices F').Perm (rotationForestVertices F) := by
  induction h with
  | refl => exact List.Perm.refl _
  | tail _ hstep ih => exact hstep.vertices_perm.trans ih

theorem spanning (h : ForestRotationReachable F F') (hF : IsSpanningPathForest F) :
    IsSpanningPathForest F' :=
  ⟨h.vertices_perm.symm.nodup hF.1, fun z => h.vertices_perm.mem_iff.mpr (hF.2 z)⟩

theorem componentCount (h : ForestRotationReachable F F') : F'.length = F.length := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact hstep.componentCount.trans ih

/-- Every resulting component is simple, derived from the original disjoint
simple-path representation and the explicit concrete rotation moves. -/
theorem simple (h : ForestRotationReachable F F') (hF : IsPathForest F)
    (p : RotationPath G) (hp : p ∈ F') : p.walk.IsPath := by
  have hnew : IsPathForest F' := h.vertices_perm.symm.nodup hF
  rw [Walk.isPath_def]
  exact (List.nodup_flatMap.mp hnew).1 p hp

/-- Exact full support and component count, with original-graph edges and
simple disjoint paths, for both cases of the forest rotation operation. -/
theorem verified (h : ForestRotationReachable F F') (hF : IsSpanningPathForest F) :
    IsSpanningPathForest F' ∧ F'.length = F.length ∧
      {z | z ∈ rotationForestVertices F'} = {z | z ∈ rotationForestVertices F} ∧
      (∀ p ∈ F', p.walk.IsPath ∧ p.edgeSet ⊆ G.edgeSet) := by
  refine ⟨h.spanning hF, h.componentCount, ?_, ?_⟩
  · ext z
    exact h.vertices_perm.mem_iff
  · intro p hp
    exact ⟨h.simple hF.1 p hp, p.edges_original⟩

end ForestRotationReachable

/-- A sequence from an actual minimum forest retains its exact minimum number
of component paths. The output is a spanning disjoint simple-path list. -/
theorem minimum_forest_rotation_count [Fintype V] (F : SpanningLinearForest G)
    (hF : F.IsMinimum) (Fn : List (RotationPath G))
    (h : ForestRotationReachable F.pathList Fn) :
    IsSpanningPathForest Fn ∧ Fn.length = F.componentCount ∧
      ∀ H : SpanningLinearForest G, Fn.length ≤ H.componentCount := by
  have hcount := h.componentCount.trans F.pathList_length
  exact ⟨h.spanning F.pathList_spanning, hcount, fun H => hcount ▸ hF H⟩

/-- A token move retains all fixed occurrences and retains a prescribed shore
for every free occurrence. The count proof distinguishes occurrences at isolates. -/
theorem endpoint_exchange_fixed_shore [DecidableEq V] {A B X : Multiset V} {x w : V}
    {S : Set V} (hex : B + {x} = A + {w}) (hfree : x ∈ A - X) (hfixed : X ≤ A)
    (hshore : ∀ z ∈ A - X, z ∈ S) (hw : w ∈ S) :
    X ≤ B ∧ ∀ z ∈ B - X, z ∈ S := by
  have hfreecount := Multiset.mem_sub.mp hfree
  constructor
  · rw [Multiset.le_iff_count]
    intro z
    have hbefore := Multiset.le_iff_count.mp hfixed z
    have he := congrArg (Multiset.count z) hex
    simp only [Multiset.count_add, Multiset.count_singleton] at he
    by_cases hzx : z = x
    · subst z
      split_ifs at he <;> omega
    · simp only [hzx, if_false] at he
      split_ifs at he <;> omega
  · intro z hz
    by_cases hzw : z = w
    · simpa [hzw] using hw
    · apply hshore z
      rw [Multiset.mem_sub] at hz ⊢
      have he := congrArg (Multiset.count z) hex
      simp only [Multiset.count_add, Multiset.count_singleton, hzw, if_false] at he
      split_ifs at he <;> omega

/-- A legal endpoint exchange leaves the new endpoint occurrence free. -/
theorem endpoint_exchange_new_free [DecidableEq V] {A B X : Multiset V} {x w : V}
    (hex : B + {x} = A + {w}) (hfree : x ∈ A - X) (hfixed : X ≤ A) :
    w ∈ B - X := by
  rw [Multiset.mem_sub]
  have hbefore := Multiset.le_iff_count.mp hfixed w
  have hfreecount := Multiset.mem_sub.mp hfree
  have he := congrArg (Multiset.count w) hex
  simp only [Multiset.count_add, Multiset.count_singleton] at he
  by_cases hwx : w = x
  · subst w
    simp only [ite_true] at he
    omega
  · simp only [hwx, if_false, ite_true] at he
    omega

/-- Concrete rotations which move only endpoint occurrences outside `X`.
Reordering components and reversing their orientation leave every token fixed. -/
inductive FixedForestRotation [DecidableEq V] (X : Multiset V) :
    List (RotationPath G) → List (RotationPath G) → Prop
  | reorder {F F' : List (RotationPath G)} (h : F.Perm F') : FixedForestRotation X F F'
  | reverse (pre post : List (RotationPath G)) {x y : V} (p : G.Walk x y) :
      FixedForestRotation X (pre ++ ⟨x, y, p⟩ :: post)
        (pre ++ ⟨y, x, p.reverse⟩ :: post)
  | within (pre post : List (RotationPath G)) {x w u y : V}
      (p : G.Walk x w) (q : G.Walk u y) (hwu : G.Adj w u) (hxu : G.Adj x u)
      (hfree : x ∈ rotationForestEndpoints
        (pre ++ ⟨x, y, rotationOriginal p q hwu⟩ :: post) - X) :
      FixedForestRotation X (pre ++ ⟨x, y, rotationOriginal p q hwu⟩ :: post)
        (pre ++ ⟨w, y, rotatePathStep p q hxu⟩ :: post)
  | between (pre post : List (RotationPath G)) {x y z w u t : V}
      (r : G.Walk x y) (p : G.Walk z w) (q : G.Walk u t)
      (hwu : G.Adj w u) (hxu : G.Adj x u)
      (hfree : x ∈ rotationForestEndpoints
        (pre ++ ⟨x, y, r⟩ :: ⟨z, t, rotationOriginal p q hwu⟩ :: post) - X) :
      FixedForestRotation X
        (pre ++ ⟨x, y, r⟩ :: ⟨z, t, rotationOriginal p q hwu⟩ :: post)
        (pre ++ ⟨y, t, r.reverse.append (.cons hxu q)⟩ :: ⟨z, w, p⟩ :: post)

namespace FixedForestRotation

variable [DecidableEq V] {X : Multiset V} {F F' : List (RotationPath G)}

theorem toForestRotation (h : FixedForestRotation X F F') : ForestRotation F F' := by
  cases h with
  | reorder h => exact .reorder h
  | reverse pre post p => exact .reverse pre post p
  | within pre post p q hwu hxu hfree => exact .within pre post p q hwu hxu
  | between pre post r p q hwu hxu hfree => exact .between pre post r p q hwu hxu

theorem fixed (h : FixedForestRotation X F F') (hfixed : X ≤ rotationForestEndpoints F) :
    X ≤ rotationForestEndpoints F' := by
  cases h with
  | reorder h => simpa only [← rotationForestEndpoints_perm h] using hfixed
  | reverse pre post p =>
    have he : rotationForestEndpoints (pre ++ ⟨_, _, p.reverse⟩ :: post) =
        rotationForestEndpoints (pre ++ ⟨_, _, p⟩ :: post) := by
      simp only [rotationForestEndpoints_append, rotationForestEndpoints]
      ac_rfl
    simpa only [he] using hfixed
  | within pre post p q hwu hxu hfree =>
    exact (endpoint_exchange_fixed_shore (S := Set.univ)
      (ForestRotation.within_endpoints pre post p q hwu hxu) hfree hfixed
      (fun _ _ => Set.mem_univ _) (Set.mem_univ _)).1
  | between pre post r p q hwu hxu hfree =>
    exact (endpoint_exchange_fixed_shore (S := Set.univ)
      (ForestRotation.between_endpoints pre post r p q hwu hxu) hfree hfixed
      (fun _ _ => Set.mem_univ _) (Set.mem_univ _)).1

/-- Fixing more tokens only removes legal moves. -/
theorem mono {Y : Multiset V} (hXY : X ≤ Y) (h : FixedForestRotation Y F F') :
    FixedForestRotation X F F' := by
  have hfree : ∀ z, ∀ A : Multiset V, z ∈ A - Y → z ∈ A - X := by
    intro z A hz
    rw [Multiset.mem_sub] at hz ⊢
    exact lt_of_le_of_lt (Multiset.le_iff_count.mp hXY z) hz
  cases h with
  | reorder h => exact .reorder h
  | reverse pre post p => exact .reverse pre post p
  | within pre post p q hwu hxu hf => exact .within pre post p q hwu hxu (hfree _ _ hf)
  | between pre post r p q hwu hxu hf =>
    exact .between pre post r p q hwu hxu (hfree _ _ hf)

/-- The fixed multiset and the one-shore condition are conclusions of legal
rotation, rather than conditions assumed about the resulting forest. -/
theorem fixed_shore {S T : Set V} (h : FixedForestRotation X F F')
    (hG : G.IsBipartiteWith S T) (hfixed : X ≤ rotationForestEndpoints F)
    (hshore : ∀ z ∈ rotationForestEndpoints F - X, z ∈ S) :
    X ≤ rotationForestEndpoints F' ∧
      ∀ z ∈ rotationForestEndpoints F' - X, z ∈ S := by
  cases h with
  | reorder h => simpa only [← rotationForestEndpoints_perm h] using And.intro hfixed hshore
  | reverse pre post p =>
    have he : rotationForestEndpoints (pre ++ ⟨_, _, p.reverse⟩ :: post) =
        rotationForestEndpoints (pre ++ ⟨_, _, p⟩ :: post) := by
      simp only [rotationForestEndpoints_append, rotationForestEndpoints]
      ac_rfl
    simpa only [he] using And.intro hfixed hshore
  | within pre post p q hwu hxu hfree =>
    exact endpoint_exchange_fixed_shore
      (ForestRotation.within_endpoints pre post p q hwu hxu) hfree hfixed hshore
      (hG.mem_of_mem_adj' (hG.mem_of_mem_adj (hshore _ hfree) hxu) hwu)
  | between pre post r p q hwu hxu hfree =>
    exact endpoint_exchange_fixed_shore
      (ForestRotation.between_endpoints pre post r p q hwu hxu) hfree hfixed hshore
      (hG.mem_of_mem_adj' (hG.mem_of_mem_adj (hshore _ hfree) hxu) hwu)

end FixedForestRotation

/-- The source's finite rotation-family relation with a fixed endpoint multiset. -/
abbrev FixedForestRotationReachable [DecidableEq V] (X : Multiset V) :=
  Relation.ReflTransGen (@FixedForestRotation V G _ X)

namespace FixedForestRotationReachable

variable [DecidableEq V] {X : Multiset V} {F F' : List (RotationPath G)}

theorem toForestRotationReachable (h : FixedForestRotationReachable X F F') :
    ForestRotationReachable F F' := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail hstep.toForestRotation

theorem fixed (h : FixedForestRotationReachable X F F')
    (hfixed : X ≤ rotationForestEndpoints F) : X ≤ rotationForestEndpoints F' := by
  induction h with
  | refl => exact hfixed
  | tail _ hstep ih => exact hstep.fixed ih

theorem mono {Y : Multiset V} (hXY : X ≤ Y)
    (h : FixedForestRotationReachable Y F F') : FixedForestRotationReachable X F F' := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (hstep.mono hXY)

theorem fixed_shore {S T : Set V} (h : FixedForestRotationReachable X F F')
    (hG : G.IsBipartiteWith S T) (hfixed : X ≤ rotationForestEndpoints F)
    (hshore : ∀ z ∈ rotationForestEndpoints F - X, z ∈ S) :
    X ≤ rotationForestEndpoints F' ∧
      ∀ z ∈ rotationForestEndpoints F' - X, z ∈ S := by
  induction h with
  | refl => exact ⟨hfixed, hshore⟩
  | tail _ hstep ih => exact hstep.fixed_shore hG ih.1 ih.2

/-- Concrete full-family invariant bundle, with isolate endpoint multiplicity. -/
theorem verified {S T : Set V} (h : FixedForestRotationReachable X F F')
    (hF : IsSpanningPathForest F) (hG : G.IsBipartiteWith S T)
    (hfixed : X ≤ rotationForestEndpoints F)
    (hshore : ∀ z ∈ rotationForestEndpoints F - X, z ∈ S) :
    IsSpanningPathForest F' ∧ F'.length = F.length ∧
      X ≤ rotationForestEndpoints F' ∧
      (∀ z ∈ rotationForestEndpoints F' - X, z ∈ S) ∧
      (∀ p ∈ F', p.walk.IsPath ∧ p.edgeSet ⊆ G.edgeSet) := by
  obtain ⟨hspan, hcount, _, hpaths⟩ := h.toForestRotationReachable.verified hF
  obtain ⟨hfixed', hshore'⟩ := h.fixed_shore hG hfixed hshore
  exact ⟨hspan, hcount, hfixed', hshore', hpaths⟩

end FixedForestRotationReachable

namespace FixedForestRotation

variable [DecidableEq V] {X : Multiset V} {F Fn : List (RotationPath G)}

/-- Every legal concrete move is reversible within the fixed-token family.
The cross-path inverse uses only orientation and ordering bookkeeping. -/
theorem reverseReachable (h : FixedForestRotation X F Fn)
    (hfixed : X ≤ rotationForestEndpoints F) : FixedForestRotationReachable X Fn F := by
  cases h with
  | reorder h => exact .single (.reorder h.symm)
  | reverse pre post p =>
    simpa using (Relation.ReflTransGen.single
      (FixedForestRotation.reverse (X := X) pre post p.reverse))
  | within pre post p q hwu hxu hfree =>
    have hw := endpoint_exchange_new_free
      (ForestRotation.within_endpoints pre post p q hwu hxu) hfree hfixed
    simpa [rotationOriginal, rotatePathStep] using
      (Relation.ReflTransGen.single (FixedForestRotation.within pre post p.reverse q hxu hwu hw))
  | @between pre post x y z w u t r p q hwu hxu hfree =>
    let a : RotationPath G := ⟨y, t, r.reverse.append (.cons hxu q)⟩
    let b : RotationPath G := ⟨z, w, p⟩
    let c : RotationPath G := ⟨z, t, rotationOriginal p q hwu⟩
    let d : RotationPath G := ⟨x, y, r⟩
    have hw := endpoint_exchange_new_free
      (ForestRotation.between_endpoints pre post r p q hwu hxu) hfree hfixed
    have hwnew : w ∈ rotationForestEndpoints
        (pre ++ ⟨w, z, p.reverse⟩ :: ⟨y, t, rotationOriginal r.reverse q hxu⟩ :: post) - X := by
      have he : rotationForestEndpoints
          (pre ++ ⟨w, z, p.reverse⟩ :: ⟨y, t, rotationOriginal r.reverse q hxu⟩ :: post) =
          rotationForestEndpoints (pre ++ a :: b :: post) := by
        simp only [a, b, rotationForestEndpoints_append, rotationForestEndpoints]
        ac_rfl
      exact he ▸ hw
    have h₁ : FixedForestRotationReachable X (pre ++ a :: b :: post)
        (pre ++ b :: a :: post) :=
      .single (.reorder ((List.Perm.swap b a post).append_left pre))
    have h₂ : FixedForestRotationReachable X (pre ++ b :: a :: post)
        (pre ++ ⟨w, z, p.reverse⟩ :: a :: post) := .single (.reverse pre (a :: post) p)
    have h₃ : FixedForestRotationReachable X
        (pre ++ ⟨w, z, p.reverse⟩ :: a :: post)
        (pre ++ c :: ⟨y, x, r.reverse⟩ :: post) := by
      simpa [a, c, rotationOriginal] using
        (Relation.ReflTransGen.single
          (FixedForestRotation.between pre post p.reverse r.reverse q hxu hwu hwnew))
    have h₄ : FixedForestRotationReachable X (pre ++ c :: ⟨y, x, r.reverse⟩ :: post)
        (pre ++ c :: d :: post) := by
      simpa [d, List.append_assoc] using
        (Relation.ReflTransGen.single
          (FixedForestRotation.reverse (X := X) (pre ++ [c]) post r.reverse))
    have h₅ : FixedForestRotationReachable X (pre ++ c :: d :: post)
        (pre ++ d :: c :: post) :=
      .single (.reorder ((List.Perm.swap d c post).append_left pre))
    exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

end FixedForestRotation

namespace FixedForestRotationReachable

variable [DecidableEq V] {X : Multiset V} {F Fn : List (RotationPath G)}

theorem symm (h : FixedForestRotationReachable X F Fn)
    (hfixed : X ≤ rotationForestEndpoints F) : FixedForestRotationReachable X Fn F := by
  induction h with
  | refl => exact .refl
  | tail hprefix hstep ih =>
    exact (hstep.reverseReachable (FixedForestRotationReachable.fixed hprefix hfixed)).trans ih

end FixedForestRotationReachable

/-- Reachable free endpoints belong to this particular starting forest's actual
fixed-token rotation family, rather than to a family indexed only by `X`. -/
def rotationComponent [DecidableEq V] (F : List (RotationPath G)) (X : Multiset V) : Set V :=
  {z | ∃ F', FixedForestRotationReachable X F F' ∧ z ∈ rotationForestEndpoints F' - X}

theorem freeEndpoints_subset_rotationComponent [DecidableEq V]
    (F : List (RotationPath G)) (X : Multiset V) :
    {z | z ∈ rotationForestEndpoints F - X} ⊆ rotationComponent F X :=
  fun _ hz => ⟨F, .refl, hz⟩

theorem rotationComponent_shore [DecidableEq V] {F : List (RotationPath G)} {X : Multiset V}
    {S T : Set V} (hG : G.IsBipartiteWith S T) (hfixed : X ≤ rotationForestEndpoints F)
    (hshore : ∀ z ∈ rotationForestEndpoints F - X, z ∈ S) :
    rotationComponent F X ⊆ S := by
  rintro z ⟨F', h, hz⟩
  exact (h.fixed_shore hG hfixed hshore).2 z hz

theorem rotationComponent_mono [DecidableEq V] {F : List (RotationPath G)}
    {X Y : Multiset V} (hXY : X ≤ Y) : rotationComponent F Y ⊆ rotationComponent F X := by
  rintro z ⟨F', h, hz⟩
  refine ⟨F', h.mono hXY, ?_⟩
  rw [Multiset.mem_sub] at hz ⊢
  exact lt_of_le_of_lt (Multiset.le_iff_count.mp hXY z) hz

/-- A starting forest in the same fixed-token family gives the same reachable
endpoint set. The family remains indexed by its actual starting forest. -/
theorem rotationComponent_eq [DecidableEq V] {F Fn : List (RotationPath G)} {X : Multiset V}
    (h : FixedForestRotationReachable X F Fn) (hfixed : X ≤ rotationForestEndpoints F) :
    rotationComponent Fn X = rotationComponent F X := by
  ext z
  constructor
  · rintro ⟨Fend, hnext, hz⟩
    exact ⟨Fend, h.trans hnext, hz⟩
  · rintro ⟨Fend, hnext, hz⟩
    exact ⟨Fend, (h.symm hfixed).trans hnext, hz⟩

/-- The number of free occurrences is invariant throughout the fixed family. -/
theorem fixed_rotation_free_card [DecidableEq V] {F Fn : List (RotationPath G)}
    {X : Multiset V} (h : FixedForestRotationReachable X F Fn)
    (hfixed : X ≤ rotationForestEndpoints F) :
    (rotationForestEndpoints Fn - X).card = (rotationForestEndpoints F - X).card := by
  rw [Multiset.card_sub (h.fixed hfixed), Multiset.card_sub hfixed,
    rotationForestEndpoints_card, rotationForestEndpoints_card,
    h.toForestRotationReachable.componentCount]

/-- Starting with an actual minimum forest, all concrete finite rotations keep
the minimum number of disjoint spanning simple paths, original edges, exact
vertex support, fixed token occurrences and one-shore free endpoints. The
rotation component is tied to this particular starting forest throughout. -/
theorem minimum_forest_rotation_family_verified [Fintype V] [DecidableEq V]
    (F : SpanningLinearForest G) (hF : F.IsMinimum) (Fn : List (RotationPath G))
    (X : Multiset V) {S T : Set V} (hG : G.IsBipartiteWith S T)
    (hfixed : X ≤ rotationForestEndpoints F.pathList)
    (hshore : ∀ z ∈ rotationForestEndpoints F.pathList - X, z ∈ S)
    (h : FixedForestRotationReachable X F.pathList Fn) :
    IsSpanningPathForest Fn ∧ Fn.length = F.componentCount ∧
      X ≤ rotationForestEndpoints Fn ∧
      (∀ z ∈ rotationForestEndpoints Fn - X, z ∈ S) ∧
      (∀ p ∈ Fn, p.walk.IsPath ∧ p.edgeSet ⊆ G.edgeSet) ∧
      (rotationForestEndpoints Fn - X).card = (rotationForestEndpoints F.pathList - X).card ∧
      rotationComponent Fn X = rotationComponent F.pathList X ∧
      (∀ H : SpanningLinearForest G, Fn.length ≤ H.componentCount) := by
  obtain ⟨hspan, _, hfix, hsh, hpaths⟩ := h.verified F.pathList_spanning hG hfixed hshore
  obtain ⟨_, hcount, hmin⟩ := minimum_forest_rotation_count F hF Fn h.toForestRotationReachable
  exact ⟨hspan, hcount, hfix, hsh, hpaths, fixed_rotation_free_card h hfixed,
    rotationComponent_eq h hfixed, hmin⟩

end Erdos585.Attempt6

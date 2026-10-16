import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Tactic
import Openmath.Proofs.PaperSupport.QBSharpness

/- -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

open Finset SimpleGraph

namespace Erdos585.QBSharpnessFamily

variable {V : Type*} [DecidableEq V]

/-- Actual graph extension with one new vertex and precisely the selected old neighbors. -/
def extendGraph (G : SimpleGraph V) (N : Finset V) : SimpleGraph (Option V) where
  Adj x y := match x, y with
    | some v, some w => G.Adj v w
    | none, some v => v ∈ N
    | some v, none => v ∈ N
    | none, none => False
  symm := ⟨by
    intro x y
    cases x <;> cases y <;> simp [G.adj_comm]⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

instance extendGraphDecidable (G : SimpleGraph V) [DecidableRel G.Adj] (N : Finset V) :
    DecidableRel (extendGraph G N).Adj := fun x y => by
  cases x <;> cases y <;> unfold extendGraph <;> infer_instance

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (N : Finset V)

@[simp] theorem degree_none : (extendGraph G N).degree none = N.card := by
  have hn : (extendGraph G N).neighborFinset none = N.image some := by
    ext x
    rw [SimpleGraph.mem_neighborFinset]
    cases x <;> simp [extendGraph]
  rw [← card_neighborFinset_eq_degree, hn, card_image_of_injective _ (Option.some_injective V)]

@[simp] theorem degree_some (v : V) :
    (extendGraph G N).degree (some v) = G.degree v + if v ∈ N then 1 else 0 := by
  have hn : (extendGraph G N).neighborFinset (some v) =
      (G.neighborFinset v).image some ∪ if v ∈ N then {none} else ∅ := by
    ext x
    rw [SimpleGraph.mem_neighborFinset]
    cases x <;> by_cases hv : v ∈ N <;> simp [extendGraph, hv]
  have hd : Disjoint ((G.neighborFinset v).image some)
      (if v ∈ N then {none} else ∅) := by
    split_ifs <;> simp
  rw [← card_neighborFinset_eq_degree, hn, card_union_of_disjoint hd,
    card_image_of_injective _ (Option.some_injective V), card_neighborFinset_eq_degree]
  split_ifs <;> simp

theorem edges_extend : (extendGraph G N).edgeFinset.card = G.edgeFinset.card + N.card := by
  have hs : (∑ x : Option V, (extendGraph G N).degree x) =
      (∑ v : V, G.degree v) + 2 * N.card := by
    rw [Fintype.sum_option]
    simp only [degree_none, degree_some, sum_add_distrib]
    have hind : (∑ v : V, if v ∈ N then 1 else 0) = N.card := by simp
    rw [hind]
    omega
  have h0 := SimpleGraph.sum_degrees_eq_twice_card_edges G
  have h1 := SimpleGraph.sum_degrees_eq_twice_card_edges (extendGraph G N)
  omega

noncomputable instance finiteSubgraphLocallyFinite {W : Type*} [Finite W]
    (K : SimpleGraph W) (H : K.Subgraph) : H.coe.LocallyFinite := fun _ => Fintype.ofFinite _

/-- The literal absence of arbitrary nonempty four-regular edge-subgraphs. -/
def NoQuartic {W : Type*} [Finite W] (K : SimpleGraph W) : Prop :=
  ¬ ∃ H : K.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree 4

/-- Actual degree-three extension preserves quartic absence. -/
theorem noQuartic_extend (hN : N.card = 3) (hG : NoQuartic G) :
    NoQuartic (extendGraph G N) := by
  classical
  rintro ⟨H, hne, hreg⟩
  have hnone : none ∉ H.verts := by
    intro hn
    have h4 : H.degree none = 4 :=
      (Subgraph.coe_degree H ⟨none, hn⟩).symm.trans (hreg.degree_eq _)
    have hle := H.degree_le none
    rw [degree_none, hN] at hle
    omega
  let H0 : G.Subgraph := {
    verts := {v | some v ∈ H.verts}
    Adj := fun v w => H.Adj (some v) (some w)
    adj_sub := fun h => H.adj_sub h
    edge_vert := fun h => H.edge_vert h
    symm := ⟨by intro v w h; exact h.symm⟩ }
  let : ∀ v : V, Fintype (H0.neighborSet v) := fun _ => Fintype.ofFinite _
  have h0ne : H0.verts.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    cases x with
    | none => exact (hnone hx).elim
    | some v => exact ⟨v, hx⟩
  have hdeg (v : V) : H0.degree v = H.degree (some v) := by
    let f : H0.neighborSet v → H.neighborSet (some v) := fun w => ⟨some w.val, w.property⟩
    have hinj : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact Option.some_injective V (congrArg Subtype.val hxy)
    have hsurj : Function.Surjective f := by
      intro w
      rcases w with ⟨x, hx⟩
      cases x with
      | none => exact (hnone hx.snd_mem).elim
      | some u => exact ⟨⟨u, hx⟩, rfl⟩
    exact Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  apply hG
  refine ⟨H0, h0ne, ?_⟩
  intro v
  rw [Subgraph.coe_degree]
  rw [hdeg v.val]
  exact (Subgraph.coe_degree H ⟨some v.val, v.property⟩).symm.trans (hreg.degree_eq _)

/-- Strong actual-graph induction data; no extension-success assumption is present. -/
structure Good (A B : Finset V) : Prop where
  disjoint : Disjoint A B
  cover : A ∪ B = univ
  bipartite : G.IsBipartiteWith ↑A ↑B
  balance_left : A.card ≤ B.card + 1
  balance_right : B.card ≤ A.card + 1
  degree_bounds : ∀ v, 3 ≤ G.degree v ∧ G.degree v ≤ 6
  edge_density : G.edgeFinset.card + 8 = 3 * Fintype.card V
  no_quartic : NoQuartic G

theorem Good.swap {A B : Finset V} (h : Good G A B) : Good G B A where
  disjoint := h.disjoint.symm
  cover := by rw [union_comm, h.cover]
  bipartite := h.bipartite.symm
  balance_left := h.balance_right
  balance_right := h.balance_left
  degree_bounds := h.degree_bounds
  edge_density := h.edge_density
  no_quartic := h.no_quartic

/-- Once the actual selected neighbors are supplied, every graph invariant is preserved. -/
theorem extend_good_selected {A B : Finset V} (h : Good G A B)
    (hsmall : A.card ≤ B.card) (hNB : N ⊆ B) (hN : N.card = 3)
    (hload : ∀ v ∈ N, G.degree v ≤ 5) :
    Good (extendGraph G N) (insert none (A.image some)) (B.image some) := by
  have hAc : (insert none (A.image some)).card = A.card + 1 := by
    rw [card_insert_of_notMem (by simp), card_image_of_injective _ (Option.some_injective V)]
  have hBc : (B.image some).card = B.card :=
    card_image_of_injective _ (Option.some_injective V)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro x hxA hxB
    cases x with
    | none => simp at hxB
    | some v =>
      exact Finset.disjoint_left.mp h.disjoint (by simpa using hxA) (by simpa using hxB)
  · ext x
    cases x with
    | none => simp
    | some v =>
      have hv : v ∈ A ∪ B := by rw [h.cover]; exact mem_univ _
      simpa using hv
  · refine ⟨?_, ?_⟩
    · rw [disjoint_coe]
      apply Finset.disjoint_left.mpr
      intro x hxA hxB
      cases x with
      | none => simp at hxB
      | some v => exact Finset.disjoint_left.mp h.disjoint (by simpa using hxA) (by simpa using hxB)
    · intro x y hxy
      cases x with
      | none =>
        cases y with
        | none => exact hxy.elim
        | some v => exact Or.inl ⟨by simp, by simpa using hNB hxy⟩
      | some v =>
        cases y with
        | none => exact Or.inr ⟨by simpa using hNB hxy, by simp⟩
        | some w => simpa using h.bipartite.mem_of_adj hxy
  · rw [hAc, hBc]
    omega
  · rw [hAc, hBc]
    have := h.balance_right
    omega
  · intro x
    cases x with
    | none => simp [hN]
    | some v =>
      rw [degree_some]
      have hd := h.degree_bounds v
      by_cases hv : v ∈ N
      · have hl := hload v hv
        simp [hv]
        omega
      · simp [hv]
        exact hd
  · rw [edges_extend, hN, Fintype.card_option]
    have := h.edge_density
    omega
  · exact noQuartic_extend G N hN h.no_quartic

/-- Actual shore sums and balance derive the legal three-element neighbor set. -/
theorem select_neighbors {A B : Finset V} (h : Good G A B) (hsmall : A.card ≤ B.card) :
    ∃ N : Finset V, N ⊆ B ∧ N.card = 3 ∧ ∀ v ∈ N, G.degree v ≤ 5 := by
  have hcard : A.card + B.card = Fintype.card V := by
    rw [← card_union_of_disjoint h.disjoint, h.cover, card_univ]
  have hdensity : G.edgeFinset.card + 8 = 3 * (A.card + B.card) := by
    rw [hcard]
    exact h.edge_density
  have hcapacity : (∑ v ∈ B, (6 - G.degree v)) + G.edgeFinset.card = 6 * B.card := by
    calc
      _ = (∑ v ∈ B, (6 - G.degree v)) + ∑ v ∈ B, G.degree v := by
        rw [SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' h.bipartite]
      _ = ∑ _v ∈ B, 6 := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro v _
        exact Nat.sub_add_cancel (h.degree_bounds v).2
      _ = 6 * B.card := by simp [mul_comm]
  have hopposite := QBSharpness.opposite_capacity A.card B.card G.edgeFinset.card
    hsmall h.balance_right hdensity
  have hcap : 8 ≤ ∑ v ∈ B, (6 - G.degree v) := by omega
  have hthree := QBSharpness.capacity_ge_eight B (fun v => G.degree v)
    (fun v _ => h.degree_bounds v) hcap
  obtain ⟨N, hNsub, hNc⟩ := Finset.exists_subset_card_eq hthree
  refine ⟨N, fun v hv => (mem_filter.mp (hNsub hv)).1, hNc, ?_⟩
  intro v hv
  exact (mem_filter.mp (hNsub hv)).2

/-- The next actual graph and its shore data exist without an assumed step contract. -/
theorem exists_good_extension {A B : Finset V} (h : Good G A B) :
    ∃ (N : Finset V) (A' B' : Finset (Option V)), Good (extendGraph G N) A' B' := by
  by_cases hsmall : A.card ≤ B.card
  · obtain ⟨N, hNB, hNc, hload⟩ := select_neighbors G h hsmall
    exact ⟨N, insert none (A.image some), B.image some,
      extend_good_selected G N h hsmall hNB hNc hload⟩
  · have hswap := h.swap
    have hrev : B.card ≤ A.card := by omega
    obtain ⟨N, hNA, hNc, hload⟩ := select_neighbors G hswap hrev
    exact ⟨N, insert none (B.image some), A.image some,
      extend_good_selected G N hswap hrev hNA hNc hload⟩

def seedLeft : Finset (Fin 5 ⊕ Fin 6) := (univ : Finset (Fin 5)).image Sum.inl

def seedRight : Finset (Fin 5 ⊕ Fin 6) := (univ : Finset (Fin 6)).image Sum.inr

/-- The actual seed supplies every induction invariant. -/
theorem seed_good : Good QBSharpness.seedGraph seedLeft seedRight := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, by decide, by decide, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [disjoint_coe]
      decide
    · intro v w hvw
      cases v <;> cases w <;> simp_all [QBSharpness.seedGraph, seedLeft, seedRight]
  · exact QBSharpness.seed_no_quartic_subgraph

/-- Actual finite graph witness with all stronger induction invariants. -/
def HasGood (n : ℕ) : Prop :=
  ∃ (W : Type) (wf : Fintype W) (wd : DecidableEq W),
    letI := wf
    letI := wd
    ∃ (K : SimpleGraph W) (kd : DecidableRel K.Adj),
      letI := kd
      Fintype.card W = n ∧ ∃ A B : Finset W, Good K A B

theorem hasGood_eleven : HasGood 11 := by
  refine ⟨Fin 5 ⊕ Fin 6, inferInstance, inferInstance, QBSharpness.seedGraph,
    inferInstance, by decide, seedLeft, seedRight, seed_good⟩

theorem hasGood_succ (n : ℕ) (h : HasGood n) : HasGood (n + 1) := by
  rcases h with ⟨W, wf, wd, h⟩
  let : Fintype W := wf
  let : DecidableEq W := wd
  rcases h with ⟨K, kd, hcard, A, B, hgood⟩
  let : DecidableRel K.Adj := kd
  obtain ⟨N, A', B', hnext⟩ := exists_good_extension K hgood
  refine ⟨Option W, inferInstance, inferInstance, extendGraph K N, inferInstance, ?_,
    A', B', hnext⟩
  rw [Fintype.card_option, hcard]

theorem hasGood_all_orders (n : ℕ) (hn : 11 ≤ n) : HasGood n := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction t with
  | zero => simpa using hasGood_eleven
  | succ t ih =>
    have hs := hasGood_succ (11 + t) ih
    simpa [Nat.add_assoc] using hs

/-- The full endpoint: an actual finite n-vertex graph, not an assumed family contract. -/
theorem all_orders (n : ℕ) (hn : 11 ≤ n) :
    ∃ (W : Type) (wf : Fintype W) (wd : DecidableEq W),
      letI := wf
      letI := wd
      ∃ (K : SimpleGraph W) (kd : DecidableRel K.Adj),
        letI := kd
        Fintype.card W = n ∧ K.IsBipartite ∧ K.edgeFinset.card + 8 = 3 * n ∧
          K.maxDegree ≤ 6 ∧ NoQuartic K := by
  rcases hasGood_all_orders n hn with ⟨W, wf, wd, h⟩
  let : Fintype W := wf
  let : DecidableEq W := wd
  rcases h with ⟨K, kd, hcard, A, B, hgood⟩
  let : DecidableRel K.Adj := kd
  refine ⟨W, wf, wd, K, kd, hcard, hgood.bipartite.isBipartite, ?_, ?_, hgood.no_quartic⟩
  · rw [← hcard]
    exact hgood.edge_density
  · exact K.maxDegree_le_of_forall_degree_le 6 (fun v => (hgood.degree_bounds v).2)

end Erdos585.QBSharpnessFamily

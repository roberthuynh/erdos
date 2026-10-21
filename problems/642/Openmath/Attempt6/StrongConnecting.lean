import Openmath.Attempt6.LocalRouting
import Openmath.Attempt6.PrivateLeafPaths

/-! Actual original-terminal routing from verified local reservoir inputs.
The random-reservoir supplier remains an explicit, separate obligation. -/
namespace Erdos585.Attempt6.StrongConnecting
open SimpleGraph Reachability LocalRouting
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All requested original terminal pairs have actual simple paths, with
pairwise disjoint nonempty exact interiors in Q union W. Terminal occurrences
may repeat across requests. -/
theorem local_routing {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (terminal : I × Bool → V)
    (Q W : Finset V) (hQW : Disjoint Q W) (hWQ : W.card ≤ Q.card) (hQ : 3 ≤ Q.card)
    (ell rank n : ℕ) (M L lambda delta D : ℝ)
    (hlambda : 0 < lambda) (hL : 1 ≤ L)
    (hdelta : 0 < delta) (hD : 0 ≤ D) (horder : Fintype.card V ≤ n)
    (hreach : ReservoirReachableAt G Q ell lambda)
    (hM : ∀ v ∈ Q, (((Q ∪ W).filter (G.Adj v)).card : ℝ) ≤ M)
    (hrank : (rank : ℝ) ≤ L ^ 6) (hpath : 4 * ell * logTwo (n : ℝ) ≤ rank)
    (hleft : ∀ i, delta ≤ ((W.filter (G.Adj (terminal i))).card : ℝ))
    (hright : ∀ v ∈ W, ((Finset.univ.filter (fun i => G.Adj (terminal i) v)).card : ℝ) ≤ D)
    (hload : D ≤ lambda * delta / (16 * M * L ^ 12))
    (houtside : ∀ i, terminal i ∉ Q ∪ W)
    (hdistinct : ∀ i, terminal (i, false) ≠ terminal (i, true)) :
    ∃ S : I → Finset V,
      (∀ i, SupportsRoute G (Q ∪ W) (rank + 2) (terminal (i, false)) (terminal (i, true)) (S i)) ∧
      Pairwise (fun i j => Disjoint (S i) (S j)) := by
  obtain ⟨f, hf, hfadj, copy, T, hT, hdis⟩ :=
    local_routing_central_of_large_reservoir G terminal Q W hQW hWQ hQ
      ell rank n M L lambda delta D hlambda hL hdelta hD horder hreach hM
      hrank hpath hleft hright hload
  have hleaf : Function.Injective (fun z : I × Bool =>
      if z.2 then f ((z.1, true), copy z.1) else f ((z.1, false), copy z.1)) := by
    have he : (fun z : I × Bool =>
        if z.2 then f ((z.1, true), copy z.1) else f ((z.1, false), copy z.1)) =
        (fun z : I × Bool => f (z, copy z.1)) := by
      funext z
      rcases z with ⟨i, b⟩
      cases b <;> rfl
    rw [he]
    exact selected_private_leaves_injective f hf copy
  exact append_private_leaf_route_family Q W hQW rank
    (fun i => terminal (i, false)) (fun i => terminal (i, true))
    (fun i => f ((i, false), copy i)) (fun i => f ((i, true), copy i)) T
    (fun i => (hfadj ((i, false), copy i)).2) (fun i => (hfadj ((i, true), copy i)).2.symm) hdistinct
    (fun i => houtside _) (fun i => houtside _)
    (fun i => (hfadj ((i, false), copy i)).1) (fun i => (hfadj ((i, true), copy i)).1) hT hleaf hdis

/-- Every edge of a simple route with a nonempty exact interior meets that
interior. In particular such a route cannot use the direct terminal edge. -/
theorem edge_meets_interior (G : SimpleGraph V) {x y : V} (T : Finset V)
    (p : G.Walk x y) (hp : p.IsPath) (hne : T.Nonempty) (hxT : x ∉ T) (hyT : y ∉ T)
    (hs : p.support.toFinset = insert x (insert y T)) :
    ∀ e ∈ p.edges, ∃ v ∈ T, v ∈ e := by
  classical
  have hxy : s(x, y) ∉ p.edges := by
    intro hedge
    obtain ⟨v, hv⟩ := hne
    have hvp : v ∈ p.support := by
      apply List.mem_toFinset.mp
      rw [hs]
      simp [hv]
    have heq := hp.eq_adj_toWalk_of_mem_edges hedge
    rw [heq] at hvp
    have hvxy : v = x ∨ v = y := by simpa using hvp
    rcases hvxy with rfl | rfl
    · exact hxT hv
    · exact hyT hv
  intro e he
  induction e using Sym2.inductionOn with
  | hf a b =>
    have ha : a = x ∨ a = y ∨ a ∈ T := by
      have hh := List.mem_toFinset.mpr (p.fst_mem_support_of_mem_edges he)
      rw [hs] at hh
      simpa using hh
    have hb : b = x ∨ b = y ∨ b ∈ T := by
      have hh := List.mem_toFinset.mpr (p.snd_mem_support_of_mem_edges he)
      rw [hs] at hh
      simpa using hh
    by_cases haT : a ∈ T
    · exact ⟨a, haT, by simp⟩
    by_cases hbT : b ∈ T
    · exact ⟨b, hbT, by simp⟩
    have hab := (p.adj_of_mem_edges he).ne
    rcases ha with rfl | rfl | ha
    · rcases hb with rfl | rfl | hb
      · exact False.elim (hab rfl)
      · exact False.elim (hxy he)
      · exact False.elim (hbT hb)
    · rcases hb with rfl | rfl | hb
      · exact False.elim (hxy (by simpa only [Sym2.eq_swap] using he))
      · exact False.elim (hab rfl)
      · exact False.elim (hbT hb)
    · exact False.elim (haT ha)

/-- Disjoint interiors give disjoint actual edges even when terminal
occurrences repeat across requests, provided all terminals lie outside U. -/
theorem route_edges_disjoint (G : SimpleGraph V) (U T S : Finset V)
    {x y a b : V} (p : G.Walk x y) (q : G.Walk a b)
    (hp : p.IsPath) (hTne : T.Nonempty) (hxT : x ∉ T) (hyT : y ∉ T)
    (hps : p.support.toFinset = insert x (insert y T))
    (hqs : q.support.toFinset = insert a (insert b S))
    (hTU : T ⊆ U) (haU : a ∉ U) (hbU : b ∉ U) (hTS : Disjoint T S) :
    p.edges.Disjoint q.edges := by
  classical
  apply List.disjoint_left.mpr
  intro e hep heq
  obtain ⟨v, hvT, hve⟩ := edge_meets_interior G T p hp hTne hxT hyT hps e hep
  have hvq : v ∈ q.support := (Walk.mem_support_iff_exists_mem_edges).mpr
    (Or.inr ⟨e, heq, hve⟩)
  have hv : v = a ∨ v = b ∨ v ∈ S := by
    have hh := List.mem_toFinset.mpr hvq
    rw [hqs] at hh
    simpa using hh
  rcases hv with rfl | rfl | hvS
  · exact haU (hTU hvT)
  · exact hbU (hTU hvT)
  · exact Finset.disjoint_left.mp hTS hvT hvS

/-- Realize selected exact interiors by an actual path family, retaining
pairwise edge disjointness and allowing repeated outside terminals. -/
theorem realize_route_family {I : Type*} (G : SimpleGraph V) (U : Finset V)
    (r : ℕ) (x y : I → V) (T : I → Finset V)
    (hx : ∀ i, x i ∉ U) (hy : ∀ i, y i ∉ U)
    (hT : ∀ i, SupportsRoute G U r (x i) (y i) (T i))
    (hpair : Pairwise (fun i j => Disjoint (T i) (T j))) :
    ∃ p : (i : I) → G.Walk (x i) (y i),
      (∀ i, (p i).IsPath ∧ (p i).length ≤ r ∧
        (p i).support.toFinset = insert (x i) (insert (y i) (T i))) ∧
      Pairwise (fun i j => (p i).edges.Disjoint (p j).edges) := by
  classical
  have hex : ∀ i, ∃ p : G.Walk (x i) (y i), p.IsPath ∧ p.length ≤ r ∧
      p.support.toFinset = insert (x i) (insert (y i) (T i)) :=
    fun i => (hT i).2.2.2.2.2
  choose p hp using hex
  refine ⟨p, hp, ?_⟩
  intro i j hij
  exact route_edges_disjoint G U (T i) (T j) (p i) (p j) (hp i).1
    (hT i).1 (hT i).2.2.1 (hT i).2.2.2.1 (hp i).2.2 (hp j).2.2
    (hT i).2.1 (hx j) (hy j) (hpair hij)

/-- Final deterministic local routing export: original graph paths between
original requested terminals, with exact nonempty disjoint interiors and
pairwise disjoint actual edge lists. -/
theorem local_routing_paths {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (terminal : I × Bool → V)
    (Q W : Finset V) (hQW : Disjoint Q W) (hWQ : W.card ≤ Q.card) (hQ : 3 ≤ Q.card)
    (ell rank n : ℕ) (M L lambda delta D : ℝ)
    (hlambda : 0 < lambda) (hL : 1 ≤ L)
    (hdelta : 0 < delta) (hD : 0 ≤ D) (horder : Fintype.card V ≤ n)
    (hreach : ReservoirReachableAt G Q ell lambda)
    (hM : ∀ v ∈ Q, (((Q ∪ W).filter (G.Adj v)).card : ℝ) ≤ M)
    (hrank : (rank : ℝ) ≤ L ^ 6) (hpath : 4 * ell * logTwo (n : ℝ) ≤ rank)
    (hleft : ∀ i, delta ≤ ((W.filter (G.Adj (terminal i))).card : ℝ))
    (hright : ∀ v ∈ W, ((Finset.univ.filter (fun i => G.Adj (terminal i) v)).card : ℝ) ≤ D)
    (hload : D ≤ lambda * delta / (16 * M * L ^ 12))
    (houtside : ∀ i, terminal i ∉ Q ∪ W)
    (hdistinct : ∀ i, terminal (i, false) ≠ terminal (i, true)) :
    ∃ S : I → Finset V, ∃ p : (i : I) → G.Walk (terminal (i, false)) (terminal (i, true)),
      (∀ i, (S i).Nonempty ∧ S i ⊆ Q ∪ W ∧
        terminal (i, false) ∉ S i ∧ terminal (i, true) ∉ S i ∧
        (p i).IsPath ∧ (p i).length ≤ rank + 2 ∧
        (p i).support.toFinset = insert (terminal (i, false)) (insert (terminal (i, true)) (S i))) ∧
      Pairwise (fun i j => Disjoint (S i) (S j)) ∧
      Pairwise (fun i j => (p i).edges.Disjoint (p j).edges) := by
  obtain ⟨S, hS, hpair⟩ := local_routing G terminal Q W hQW hWQ hQ ell rank n M L lambda delta D
    hlambda hL hdelta hD horder hreach hM hrank hpath hleft hright hload houtside hdistinct
  obtain ⟨p, hp, he⟩ := realize_route_family G (Q ∪ W) (rank + 2)
    (fun i => terminal (i, false)) (fun i => terminal (i, true)) S
    (fun i => houtside _) (fun i => houtside _) hS hpair
  exact ⟨S, p, (fun i => ⟨(hS i).1, (hS i).2.1, (hS i).2.2.1,
    (hS i).2.2.2.1, hp i⟩), hpair, he⟩

/-- A concrete integer central-path budget at large L. The ambient logarithm
is bounded explicitly by L rather than identified with any smaller order. -/
theorem half_power_rank_budget (ell n : ℕ) (L : ℝ) (hL : 16 ≤ L)
    (hell : (ell : ℝ) ≤ L ^ 4) (hlog : logTwo (n : ℝ) ≤ L) :
    ((Nat.floor (L ^ 6 / 2) : ℕ) : ℝ) ≤ L ^ 6 ∧
    4 * ell * logTwo (n : ℝ) ≤ (Nat.floor (L ^ 6 / 2) : ℕ) ∧
    Nat.floor (L ^ 6 / 2) + 2 ≤ Nat.floor (L ^ 6) := by
  have hLpos : 0 ≤ L := by linarith
  have hLone : 1 ≤ L := by linarith
  have h5 : 1 ≤ L ^ 5 := one_le_pow₀ hLone
  have h6 : L ^ 6 = L ^ 5 * L := by ring
  have hhalf : 0 ≤ L ^ 6 / 2 := by positivity
  have hf := Nat.floor_le hhalf
  have hfnext := Nat.lt_floor_add_one (L ^ 6 / 2)
  have hmul := mul_le_mul_of_nonneg_right hL (by positivity : 0 ≤ L ^ 5)
  have hroom : 4 * L ^ 5 + 1 ≤ L ^ 6 / 2 := by rw [h6]; nlinarith
  have hlen : 4 * ell * logTwo (n : ℝ) ≤ 4 * L ^ 5 := by
    have h1 := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ 4 * ell)
    have h2 := mul_le_mul_of_nonneg_right hell (by positivity : 0 ≤ 4 * L)
    nlinarith [show L ^ 4 * L = L ^ 5 by ring]
  refine ⟨by nlinarith [sq_nonneg (L ^ 3)], ?_, ?_⟩
  · linarith
  · apply Nat.le_floor
    have hbig : 4 ≤ L ^ 6 := by rw [h6]; nlinarith
    push_cast
    linarith

/-- Concrete local routing with the full original-terminal path length at
most floor(L^6), using reservoir radius at most L^4 and L at least sixteen. -/
theorem local_routing_power_six {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (terminal : I × Bool → V)
    (Q W : Finset V) (hQW : Disjoint Q W) (hWQ : W.card ≤ Q.card) (hQ : 3 ≤ Q.card)
    (ell n : ℕ) (M L lambda delta D : ℝ)
    (hlambda : 0 < lambda) (hL : 16 ≤ L)
    (hdelta : 0 < delta) (hD : 0 ≤ D) (horder : Fintype.card V ≤ n)
    (hreach : ReservoirReachableAt G Q ell lambda)
    (hM : ∀ v ∈ Q, (((Q ∪ W).filter (G.Adj v)).card : ℝ) ≤ M)
    (hell : (ell : ℝ) ≤ L ^ 4) (hlog : logTwo (n : ℝ) ≤ L)
    (hleft : ∀ i, delta ≤ ((W.filter (G.Adj (terminal i))).card : ℝ))
    (hright : ∀ v ∈ W, ((Finset.univ.filter (fun i => G.Adj (terminal i) v)).card : ℝ) ≤ D)
    (hload : D ≤ lambda * delta / (16 * M * L ^ 12))
    (houtside : ∀ i, terminal i ∉ Q ∪ W)
    (hdistinct : ∀ i, terminal (i, false) ≠ terminal (i, true)) :
    ∃ S : I → Finset V, ∃ p : (i : I) → G.Walk (terminal (i, false)) (terminal (i, true)),
      (∀ i, (S i).Nonempty ∧ S i ⊆ Q ∪ W ∧
        terminal (i, false) ∉ S i ∧ terminal (i, true) ∉ S i ∧
        (p i).IsPath ∧ (p i).length ≤ Nat.floor (L ^ 6) ∧
        (p i).support.toFinset = insert (terminal (i, false)) (insert (terminal (i, true)) (S i))) ∧
      Pairwise (fun i j => Disjoint (S i) (S j)) ∧
      Pairwise (fun i j => (p i).edges.Disjoint (p j).edges) := by
  obtain ⟨hrank, hpath, hlen⟩ := half_power_rank_budget ell n L hL hell hlog
  obtain ⟨S, p, hp, hdis, he⟩ := local_routing_paths G terminal Q W hQW hWQ hQ
    ell (Nat.floor (L ^ 6 / 2)) n M L lambda delta D hlambda (by linarith) hdelta hD
    horder hreach hM hrank hpath hleft hright hload houtside hdistinct
  refine ⟨S, p, ?_, hdis, he⟩
  intro i
  obtain ⟨hne, hsub, hx, hy, hsimple, hplen, hs⟩ := hp i
  exact ⟨hne, hsub, hx, hy, hsimple, hplen.trans hlen, hs⟩

end Erdos585.Attempt6.StrongConnecting

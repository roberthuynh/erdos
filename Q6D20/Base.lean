import BqLowerFamilyDirect
import Mathlib.Logic.Equiv.Fin.Basic
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open Finset SimpleGraph
namespace Erdos585.Q6D20R31
variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Actual original induction facts. No balanced-shore or successful-birth premise. -/
structure Good20 (A B : Finset V) : Prop where
  disjoint : Disjoint A B
  cover : A ∪ B = univ
  bipartite : G.IsBipartiteWith ↑A ↑B
  degrees : ∀ v, 5 ≤ G.degree v ∧ G.degree v ≤ 10
  density : G.edgeFinset.card + 20 = 5 * Fintype.card V
  no_regular : BqLowerFamily.NoRegular 6 G

theorem Good20.swap {A B : Finset V} (h : Good20 G A B) : Good20 G B A where
  disjoint := h.disjoint.symm
  cover := by rw [union_comm, h.cover]
  bipartite := h.bipartite.symm
  degrees := h.degrees
  density := h.density
  no_regular := h.no_regular

theorem Good20.extend {A B : Finset V} (h : Good20 G A B) (N : Finset V)
    (hNB : N ⊆ B) (hN : N.card = 5) (hload : ∀ v ∈ N, G.degree v ≤ 9) :
    Good20 (BqLowerFamily.extendGraph G N) (insert none (A.image some)) (B.image some) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro x
    cases x with
    | none => simp [hN]
    | some v =>
      rw [BqLowerFamily.degree_some]
      have hd := h.degrees v
      by_cases hv : v ∈ N
      · have hl := hload v hv
        simp [hv]
        omega
      · simp [hv]
        omega
  · rw [BqLowerFamily.edges_extend, hN, Fintype.card_option]
    have := h.density
    omega
  · exact BqLowerFamily.noRegular_extend G N 6 (by decide) hN h.no_regular

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Arbitrary original subgraphs are transported through an actual bijection. -/
theorem noRegular_comap {W : Type*} [Fintype W] (e : W ≃ V)
    (hG : BqLowerFamily.NoRegular 6 G) : BqLowerFamily.NoRegular 6 (G.comap e) := by
  classical
  rintro ⟨H, hne, hreg⟩
  let H0 : G.Subgraph := {
    verts := {v | e.symm v ∈ H.verts}
    Adj := fun v w => H.Adj (e.symm v) (e.symm w)
    adj_sub := by
      intro v w h
      simpa using H.adj_sub h
    edge_vert := fun h => H.edge_vert h
    symm := ⟨by intro v w h; exact h.symm⟩ }
  let : ∀ v : V, Fintype (H0.neighborSet v) := fun _ => Fintype.ofFinite _
  have h0ne : H0.verts.Nonempty := by
    obtain ⟨v, hv⟩ := hne
    exact ⟨e v, by simpa [H0] using hv⟩
  have hdeg (v : V) : H0.degree v = H.degree (e.symm v) := by
    let f : H0.neighborSet v → H.neighborSet (e.symm v) :=
      fun w => ⟨e.symm w.val, w.property⟩
    have hinj : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact e.symm.injective (congrArg Subtype.val hxy)
    have hsurj : Function.Surjective f := by
      intro w
      refine ⟨⟨e w.val, ?_⟩, ?_⟩
      · change H.Adj (e.symm v) (e.symm (e w.val))
        rw [e.symm_apply_apply]
        exact w.property
      · apply Subtype.ext
        simp [f]
    exact Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  apply hG
  refine ⟨H0, h0ne, ?_⟩
  intro v
  rw [Subgraph.coe_degree, hdeg v.val]
  exact (Subgraph.coe_degree H ⟨e.symm v.val, v.property⟩).symm.trans (hreg.degree_eq _)

/-- Relabel the named shores along the same original graph bijection. -/
def relabelShore {W : Type*} [DecidableEq W] (e : W ≃ V) (A : Finset V) : Finset W :=
  A.image e.symm

omit [DecidableEq V] [Fintype V] in
@[simp] theorem mem_relabelShore {W : Type*} [DecidableEq W] (e : W ≃ V)
    (A : Finset V) (w : W) : w ∈ relabelShore e A ↔ e w ∈ A := by
  constructor
  · intro hw
    obtain ⟨a, ha, heq⟩ := mem_image.mp hw
    have he : a = e w := by simpa using congrArg e heq
    exact he ▸ ha
  · intro hw
    exact mem_image.mpr ⟨e w, hw, e.symm_apply_apply w⟩

theorem Good20.comap {W : Type*} [DecidableEq W] [Fintype W] (e : W ≃ V)
    {A B : Finset V} (h : Good20 G A B) :
    Good20 (G.comap e) (relabelShore e A) (relabelShore e B) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro w ha hb
    exact Finset.disjoint_left.mp h.disjoint (mem_relabelShore e A w |>.mp ha)
      (mem_relabelShore e B w |>.mp hb)
  · ext w
    have hc : e w ∈ A ∪ B := by rw [h.cover]; exact mem_univ _
    simpa using hc
  · refine ⟨?_, ?_⟩
    · rw [disjoint_coe]
      apply Finset.disjoint_left.mpr
      intro w ha hb
      exact Finset.disjoint_left.mp h.disjoint (mem_relabelShore e A w |>.mp ha)
        (mem_relabelShore e B w |>.mp hb)
    · intro x y hxy
      simpa using h.bipartite.mem_of_adj hxy
  · intro w
    rw [← (SimpleGraph.Iso.comap e G).degree_eq w]
    exact h.degrees (e w)
  · rw [(SimpleGraph.Iso.comap e G).card_edgeFinset_eq]
    rw [Fintype.card_congr e]
    exact h.density
  · exact noRegular_comap G e h.no_regular

end Erdos585.Q6D20R31

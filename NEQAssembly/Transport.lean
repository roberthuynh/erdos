import NEQAssembly.Components

/-! Actual original induced-carrier transport.
Selected vertices and edges are transported by an injective original hom;
every degree is paid by an actual graph isomorphism. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open SimpleGraph Finset
open scoped Classical
namespace Erdos585.NEQAssembly
open NEQ
universe u v

noncomputable def subgraphMapIso {A : Type u} {B : Type v}
    {K : SimpleGraph A} {G : SimpleGraph B} (f : K →g G)
    (hf : Function.Injective f) (H : K.Subgraph) : H.coe ≃g (H.map f).coe where
  toEquiv := Equiv.Set.image f H.verts hf
  map_rel_iff' := by
    intro x y
    change (H.map f).Adj (f (x : A)) (f (y : A)) ↔ H.Adj (x : A) (y : A)
    constructor
    · rintro ⟨a, b, hab, hax, hby⟩
      have ha := hf hax
      have hb := hf hby
      simpa only [ha, hb] using hab
    · intro h
      exact ⟨x, y, h, rfl, rfl⟩

theorem regular_map_transport {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {K : SimpleGraph A} {G : SimpleGraph B} {q : ℕ}
    (f : K →g G) (hf : Function.Injective f)
    (h : ∃ H : K.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  obtain ⟨H, hnonempty, hregular⟩ := h
  refine ⟨H.map f, hnonempty.image f, ?_⟩
  let e := subgraphMapIso f hf H
  intro x
  exact (e.symm.degree_eq x).symm.trans (hregular (e.symm x))

theorem original_induced_regular_transport {V : Type u} [Fintype V]
    (G : SimpleGraph V) (U : Finset V) {q : ℕ}
    (h : ∃ H : (G.induce (U : Set V)).Subgraph,
      H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  let f : G.induce (U : Set V) →g G := (SimpleGraph.Embedding.induce (G := G) (U : Set V)).toHom
  exact regular_map_transport f (fun _ _ h => Subtype.ext h) h

theorem original_thinned_induced_regular_transport {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (K : SimpleGraph (U : Set V)) {q : ℕ}
    (hsub : K ≤ G.induce (U : Set V))
    (h : ∃ H : K.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  apply original_induced_regular_transport G U
  exact original_regular_transport hsub h

#print axioms subgraphMapIso
#print axioms regular_map_transport
#print axioms original_induced_regular_transport
#print axioms original_thinned_induced_regular_transport
end Erdos585.NEQAssembly

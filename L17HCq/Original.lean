import L17HCq.Counts
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
open Finset SimpleGraph BqLowerFamily
namespace Erdos585.L17HCq

/-- Exactly the55 original unit pairs in the bound pure raw source. -/
def l17RawEdges : Finset (Fin 17 × Fin 17) :=
  {(0,10),(0,11),(0,12),(0,14),(0,16),(1,8),(1,9),(1,13),(1,15),(1,16),(2,8),(2,9),(2,11),(2,13),(2,14),(2,15),(2,16),(3,8),(3,9),(3,10),(3,12),(3,13),(3,15),(3,16),(4,8),(4,9),(4,10),(4,11),(4,12),(4,14),(4,16),(5,8),(5,9),(5,10),(5,11),(5,12),(5,13),(5,14),(5,15),(6,8),(6,9),(6,10),(6,11),(6,12),(6,13),(6,14),(6,15),(7,8),(7,9),(7,10),(7,11),(7,12),(7,13),(7,14),(7,15)}

def l17SeedGraph : SimpleGraph (Fin 17) where
  Adj x y := (x,y) ∈ l17RawEdges ∨ (y,x) ∈ l17RawEdges
  symm := ⟨by intro x y h;exact Or.symm h⟩
  loopless := ⟨by intro x;fin_cases x <;> decide⟩
instance l17SeedDecidable : DecidableRel l17SeedGraph.Adj := fun _ _ => by
  unfold l17SeedGraph;infer_instance

def l17SeedA : Finset (Fin 17) := univ.filter fun v => v.val<8
def l17SeedB : Finset (Fin 17) := univ.filter fun v => 8 ≤ v.val

def q5Relabel : SeedVertex 5 → Fin 17
  | .inl (.inl i) => ⟨i.val+2,by omega⟩
  | .inl (.inr a) => ⟨a.val,by omega⟩
  | .inr (.inl j) => ![10,12,11,14,13,15,8,9] j
  | .inr (.inr _) => 16

theorem q5Relabel_bijective : Function.Bijective q5Relabel := by decide
noncomputable def q5SeedEquiv : SeedVertex 5 ≃ Fin 17 :=
  Equiv.ofBijective q5Relabel q5Relabel_bijective

theorem q5Relabel_adj : ∀ x y : SeedVertex 5,
    l17SeedGraph.Adj (q5Relabel x) (q5Relabel y) ↔ (hcqSeedGraph 5).Adj x y := by decide

noncomputable def q5SeedIso : hcqSeedGraph 5 ≃g l17SeedGraph where
  toEquiv := q5SeedEquiv
  map_rel_iff' := by intro x y;exact q5Relabel_adj x y

/-- Pull a real arbitrary-support factor back through an actual vertex/edge bijection. -/
theorem noRegular_equiv {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (K : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel K.Adj] (q : ℕ) (e : V ≃ W)
    (hadj : ∀ v w,K.Adj (e v) (e w) ↔ G.Adj v w)
    (hno : NoRegular q G) : NoRegular q K := by
  classical
  rintro ⟨H,hne,hreg⟩
  let H0 : G.Subgraph := {
    verts := {v | e v ∈ H.verts}
    Adj := fun v w => H.Adj (e v) (e w)
    adj_sub := fun h => (hadj _ _).mp (H.adj_sub h)
    edge_vert := fun h => H.edge_vert h
    symm := ⟨by intro v w h;exact h.symm⟩ }
  let : ∀ v : V,Fintype (H0.neighborSet v) := fun _ => Fintype.ofFinite _
  have hdeg (v : V) : H0.degree v=H.degree (e v) := by
    let f : H0.neighborSet v → H.neighborSet (e v) := fun w => ⟨e w.val,w.property⟩
    have hi : Function.Injective f := by
      intro x y hxy;apply Subtype.ext;exact e.injective (congrArg Subtype.val hxy)
    have hs : Function.Surjective f := by
      intro w
      refine ⟨⟨e.symm w.val,?_⟩,?_⟩
      · change H.Adj (e v) (e (e.symm w.val))
        rw [e.apply_symm_apply]
        exact w.property
      · apply Subtype.ext;simp [f]
    exact Fintype.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)
  apply hno
  refine ⟨H0,?_,?_⟩
  · obtain ⟨w,hw⟩ := hne
    exact ⟨e.symm w,by change e (e.symm w) ∈ H.verts;simpa using hw⟩
  · intro v
    rw [Subgraph.coe_degree,hdeg]
    exact (Subgraph.coe_degree H ⟨e v.val,v.property⟩).symm.trans (hreg.degree_eq _)

theorem l17_seed_no_regular : NoRegular 5 l17SeedGraph :=
  noRegular_equiv (hcqSeedGraph 5) l17SeedGraph 5 q5SeedEquiv q5Relabel_adj
    (hcq_seed_no_regular 5 (by decide))

def l17SeedLabeling : Labeling (Fin 17) where
  label := Fin.val
  injective := Fin.val_injective
  bounded := by intro v;simpa using v.isLt

theorem l17_seed_good : Good 5 13 l17SeedGraph l17SeedA l17SeedB := by
  refine ⟨by decide,by decide,?_,by decide,by decide,by decide,by decide,l17_seed_no_regular⟩
  refine ⟨?_,?_⟩
  · rw [disjoint_coe];decide
  · decide

theorem l17_raw_card : l17RawEdges.card=55 := by decide
theorem l17_raw_crossing : ∀ e ∈ l17RawEdges,e.1.val<8 ∧ 8 ≤ e.2.val := by decide
end Erdos585.L17HCq

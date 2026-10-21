import Openmath.Erdos642.Proofs.DenseMask20261019.IncidenceHall
import Openmath.Erdos642.Proofs.DenseMask20261019.ToughLayersV2
import Openmath.Erdos642.Proofs.Log3V1_20261024.Interface

   
                                                                                            

                                                                                                
                                                                                           
                                      

                                                                                         
                                                                                  
                                                                                                 
                                                                                           
                                                                                    
                                                
                                                                                              
                                                                                          

         
                                                                                      
                                                                               
                                                                                               
                                                                                         
                                                                                          
                                                                                       
                                                                                           
                              

                                                                                            
                                                                                              
                                                                                    
  

namespace Erdos642.Log3V1_20261024

open Finset SimpleGraph

variable {W : Type*}

/-! ### 1. Query family -/

section Card

/-- `Fintype.card ↥(S : Set W) = S.card` for any `Fintype` instance on the subtype. -/
theorem card_elem_eq (S : Finset W) [Fintype ↥(S : Set W)] :
    Fintype.card ↥(S : Set W) = S.card :=
  (Fintype.card_congr (Equiv.refl _ : ↥(S : Set W) ≃ {x // x ∈ S})).trans (Fintype.card_coe S)

/-- The query-index bound `Fintype.card I ≤ 2·Fintype.card V` of `exists_tough_layers`, from
MaskCore's `|W| ≤ 2|R|`. -/
theorem card_Q_le_two_card_R [Fintype W] (Q R : Finset W) [Fintype ↥(Q : Set W)]
    [Fintype ↥(R : Set W)] (hWR : Fintype.card W ≤ 2*R.card) :
    Fintype.card ↥(Q : Set W) ≤ 2*Fintype.card ↥(R : Set W) := by
  rw [card_elem_eq Q, card_elem_eq R]
  exact (Finset.card_le_univ Q).trans hWR

end Card

section Query

variable [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj] (Q R : Finset W)

/-- The query set of an occurrence `x ∈ Q`: the neighbours of `x` lying in `R`, viewed inside
the vertex type `↥(R : Set W)` of `H.induce (R : Set W)`. -/
def querySet (x : ↥(Q : Set W)) : Finset ↥(R : Set W) :=
  (H.neighborFinset x.1).subtype (fun y => y ∈ (R : Set W))

variable {H Q R}

@[simp] theorem mem_querySet {x : ↥(Q : Set W)} {y : ↥(R : Set W)} :
    y ∈ querySet H Q R x ↔ H.Adj x.1 y.1 := by
  unfold querySet
  rw [Finset.mem_subtype, SimpleGraph.mem_neighborFinset]

/-- Pushing the query set back to `W` gives exactly `N_H(x) ∩ R`. -/
theorem querySet_map (x : ↥(Q : Set W)) :
    (querySet H Q R x).map (Function.Embedding.subtype _) = H.neighborFinset x.1 ∩ R := by
  unfold querySet
  rw [Finset.subtype_map]
  ext y
  simp [Finset.mem_filter, Finset.mem_inter]

/-- `|querySet x| = |N_H(x) ∩ R|`; with MaskCore's `3d/4 ≤ |N_H(v) ∩ R|` this is the tough-layer
hypothesis `∀ i, d₀ ≤ |S i|` for `d₀ = 3d/4`. -/
theorem card_querySet (x : ↥(Q : Set W)) :
    (querySet H Q R x).card = (H.neighborFinset x.1 ∩ R).card := by
  rw [← querySet_map x, Finset.card_map]

theorem querySet_card_ge (d : ℝ)
    (hres : ∀ v, 3*d/4 ≤ ((H.neighborFinset v ∩ R).card : ℝ)) (x : ↥(Q : Set W)) :
    3*d/4 ≤ ((querySet H Q R x).card : ℝ) := by
  rw [card_querySet]
  exact hres x.1

end Query

/-! ### 2. Image layers in `W` -/

section Lift

variable {R : Finset W}

/-- The image in `W` of a layer `A' ⊆ ↥(R : Set W)`. -/
def liftLayer (A' : Finset ↥(R : Set W)) : Finset W :=
  A'.map (Function.Embedding.subtype _)

theorem mem_liftLayer {A' : Finset ↥(R : Set W)} {x : W} :
    x ∈ liftLayer A' ↔ ∃ y ∈ A', y.1 = x :=
  Finset.mem_map

theorem mem_liftLayer_of_mem {A' : Finset ↥(R : Set W)} {y : ↥(R : Set W)} (hy : y ∈ A') :
    y.1 ∈ liftLayer A' :=
  mem_liftLayer.mpr ⟨y, hy, rfl⟩

theorem mem_of_mem_liftLayer {A' : Finset ↥(R : Set W)} {y : ↥(R : Set W)}
    (hy : y.1 ∈ liftLayer A') : y ∈ A' := by
  obtain ⟨z, hz, hzy⟩ := mem_liftLayer.mp hy
  rwa [Subtype.ext hzy] at hz

theorem liftLayer_subset (A' : Finset ↥(R : Set W)) : liftLayer A' ⊆ R := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := mem_liftLayer.mp hx
  exact y.2

theorem card_liftLayer (A' : Finset ↥(R : Set W)) : (liftLayer A').card = A'.card := by
  unfold liftLayer
  exact Finset.card_map _

theorem disjoint_liftLayer_of_compl [Fintype W] [DecidableEq W] {Q : Finset W} (hR : R = Qᶜ)
    (A' : Finset ↥(R : Set W)) :
    Disjoint Q (liftLayer A') := by
  refine Finset.disjoint_left.mpr fun x hxQ hxA => ?_
  have hxR := liftLayer_subset A' hxA
  rw [hR, Finset.mem_compl] at hxR
  exact hxR hxQ

theorem disjoint_liftLayer {A' B' : Finset ↥(R : Set W)} (h : Disjoint A' B') :
    Disjoint (liftLayer A') (liftLayer B') := by
  unfold liftLayer
  exact (Finset.disjoint_map _).mpr h

/-- Pairwise disjointness of the layers transfers to their images. -/
theorem pairwise_disjoint_liftLayer {ι : Type*} {A' : ι → Finset ↥(R : Set W)}
    (h : Pairwise fun i j => Disjoint (A' i) (A' j)) :
    Pairwise fun i j => Disjoint (liftLayer (A' i)) (liftLayer (A' j)) :=
  fun _ _ hij => disjoint_liftLayer (h hij)

/-- The query conjunct of `LayerGood` counts exactly the neighbours of `x` in the image layer. -/
theorem card_querySet_inter [Fintype W] [DecidableEq W] {Q : Finset W} (H : SimpleGraph W)
    [DecidableRel H.Adj] (x : ↥(Q : Set W)) (A' : Finset ↥(R : Set W)) :
    (querySet H Q R x ∩ A').card = (H.neighborFinset x.1 ∩ liftLayer A').card := by
  have hmap : (querySet H Q R x ∩ A').map (Function.Embedding.subtype _)
      = H.neighborFinset x.1 ∩ liftLayer A' := by
    rw [Finset.map_inter, querySet_map]
    ext y
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨⟨hy, _⟩, hyA⟩
      exact ⟨hy, hyA⟩
    · rintro ⟨hy, hyA⟩
      exact ⟨⟨hy, liftLayer_subset A' hyA⟩, hyA⟩
  rw [← hmap, Finset.card_map]

end Lift

/-! ### 3. Hall for the endpoint occurrences of one layer -/

section Hall

variable [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- `Q.filter (H.Adj · v)`, the load counted by `isolate_tokens_match_layer`, is `N_H(v) ∩ Q`. -/
theorem filter_adj_right_eq (Q : Finset W) (v : W) :
    (Q.filter fun x => H.Adj x v) = H.neighborFinset v ∩ Q := by
  ext y
  rw [Finset.mem_filter, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
  exact ⟨fun h => ⟨h.2.symm, h.1⟩, fun h => ⟨h.2, h.1.symm⟩⟩

                                                                                           
                                                                                  
                                                                                           
                                                                                  
theorem exists_token_injection (Q A : Finset W) (h : ℝ) (hh : 0 < h)
    (hleft : ∀ x ∈ Q, h ≤ ((H.neighborFinset x ∩ A).card : ℝ))
    (hload : ∀ v, 2 * ((H.neighborFinset v ∩ Q).card : ℝ) ≤ h) :
    ∃ f : (↥(Q : Set W) × Bool) → W, Function.Injective f ∧
      ∀ z, f z ∈ A ∧ H.Adj z.1.val (f z) := by
  refine Erdos642.DenseMask20261019.IncidenceHall.isolate_tokens_match_layer H Q A h hh hleft ?_
  intro v
  rw [filter_adj_right_eq H Q v]
  exact hload v

/-- Hall for one layer from MaskCore's load bound `|N_H(v) ∩ Q| ≤ 2p·deg v` and `deg ≤ 100d`
(§4, (2)): `load(v) ≤ 400·p·d`. A layer in which every occurrence has at least `rho/2`
neighbours receives a token injection as soon as `800·p·d ≤ rho` (that is `h = rho/2 ≥ 400·p·d`,
the written inequality (3)). -/
theorem exists_token_injection_of_mask (Q A : Finset W) (p d rho : ℝ) (hp : 0 ≤ p)
    (hrho : 0 < rho)
    (hQ : ∀ v, ((H.neighborFinset v ∩ Q).card : ℝ) ≤ 2*p*(H.degree v : ℝ))
    (hhi : ∀ v, (H.degree v : ℝ) ≤ 100*d) (hpd : 800*p*d ≤ rho)
    (hleft : ∀ x ∈ Q, rho/2 ≤ ((H.neighborFinset x ∩ A).card : ℝ)) :
    ∃ f : (↥(Q : Set W) × Bool) → W, Function.Injective f ∧
      ∀ z, f z ∈ A ∧ H.Adj z.1.val (f z) := by
  refine exists_token_injection H Q A (rho/2) (by linarith) hleft ?_
  intro v
  have h1 := hQ v
  have h2 : 2*p*(H.degree v : ℝ) ≤ 2*p*(100*d) :=
    mul_le_mul_of_nonneg_left (hhi v) (by linarith)
  linarith

/-- Hall for one tough layer `A' ⊆ ↥(R : Set W)`: the query conjunct of `LayerGood` for the
family `querySet H Q R` (`rho/2 ≤ |querySet x ∩ A'|`), transferred to `W`, is the per-occurrence
lower bound, and the injection lands in `liftLayer A'`. -/
theorem exists_token_injection_of_layerGood (Q R : Finset W) (A' : Finset ↥(R : Set W))
    (p d rho : ℝ) (hp : 0 ≤ p) (hrho : 0 < rho)
    (hQ : ∀ v, ((H.neighborFinset v ∩ Q).card : ℝ) ≤ 2*p*(H.degree v : ℝ))
    (hhi : ∀ v, (H.degree v : ℝ) ≤ 100*d) (hpd : 800*p*d ≤ rho)
    (hS : ∀ x : ↥(Q : Set W), rho/2 ≤ ((querySet H Q R x ∩ A').card : ℝ)) :
    ∃ f : (↥(Q : Set W) × Bool) → W, Function.Injective f ∧
      ∀ z, f z ∈ liftLayer A' ∧ H.Adj z.1.val (f z) := by
  refine exists_token_injection_of_mask H Q (liftLayer A') p d rho hp hrho hQ hhi hpd ?_
  intro x hx
  have h := hS ⟨x, hx⟩
  rwa [card_querySet_inter H ⟨x, hx⟩ A'] at h

/-- The query conjunct of `LayerGood`, extracted for the family `querySet H Q R`. -/
theorem query_bound_of_layerGood (Q R : Finset W) [Fintype ↥(Q : Set W)]
    [Fintype ↥(R : Set W)] (G' : SimpleGraph ↥(R : Set W)) [DecidableRel G'.Adj]
    (rho D : ℝ) (A' : Finset ↥(R : Set W))
    (hgood : Erdos642.DenseMask20261019.ToughLayersV2.LayerGood G' rho D (querySet H Q R) A') :
    ∀ x : ↥(Q : Set W), rho/2 ≤ ((querySet H Q R x ∩ A').card : ℝ) :=
  hgood.2.2.2.2

end Hall

/-! ### 5. Degrees of `H.induce (R : Set W)` (hypotheses of `exists_tough_layers`) -/

section InducedDegree

variable [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj] (R : Finset W)

/-- The degree of `v` in `H.induce (R : Set W)` is `|N_H(v) ∩ R|`, for any instances. -/
theorem degree_induce_eq [Fintype ↥(R : Set W)] [DecidableRel (H.induce (R : Set W)).Adj]
    (v : ↥(R : Set W)) :
    (H.induce (R : Set W)).degree v = (H.neighborFinset v.1 ∩ R).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  have hmap : (Finset.univ.filter fun y : ↥(R : Set W) => (H.induce (R : Set W)).Adj v y).map
      (Function.Embedding.subtype _) = H.neighborFinset v.1 ∩ R := by
    ext y
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
      SimpleGraph.mem_neighborFinset, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz, z.2⟩
    · rintro ⟨hy, hyR⟩
      exact ⟨⟨y, hyR⟩, hy, rfl⟩
  rw [← hmap, Finset.card_map]

/-- Lower degree in the induced graph: `d₀ = 3d/4` from MaskCore's residual bound. -/
theorem degree_induce_ge [Fintype ↥(R : Set W)] [DecidableRel (H.induce (R : Set W)).Adj]
    (d : ℝ) (hres : ∀ v, 3*d/4 ≤ ((H.neighborFinset v ∩ R).card : ℝ)) (v : ↥(R : Set W)) :
    3*d/4 ≤ ((H.induce (R : Set W)).degree v : ℝ) := by
  rw [degree_induce_eq]
  exact hres v.1

/-- Upper degree in the induced graph: `deg_{G'} v ≤ deg_H v ≤ 100d`; with `d₀ = 3d/4` this is
`D·d₀` for any `D ≥ 400/3`, in particular `D₀ = 534`. -/
theorem degree_induce_le [Fintype ↥(R : Set W)] [DecidableRel (H.induce (R : Set W)).Adj]
    (d : ℝ) (hhi : ∀ v, (H.degree v : ℝ) ≤ 100*d) (v : ↥(R : Set W)) :
    ((H.induce (R : Set W)).degree v : ℝ) ≤ 100*d := by
  rw [degree_induce_eq]
  have h1 : (H.neighborFinset v.1 ∩ R).card ≤ H.degree v.1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_le_card Finset.inter_subset_left
  have h2 : ((H.neighborFinset v.1 ∩ R).card : ℝ) ≤ (H.degree v.1 : ℝ) := by exact_mod_cast h1
  exact h2.trans (hhi v.1)

end InducedDegree

/-! ### 4. Transport of `Linked` and `InsideConnected` along the induced-subgraph embedding -/

section Transport

variable (H : SimpleGraph W) (R : Finset W)

/-- The induced-subgraph homomorphism `H.induce (R : Set W) →g H`, i.e. `Subtype.val`. -/
def liftHom : H.induce (R : Set W) →g H where
  toFun := Subtype.val
  map_rel' := fun h => h

@[simp] theorem liftHom_apply (v : ↥(R : Set W)) : liftHom H R v = v.1 := rfl

theorem liftHom_injective : Function.Injective (liftHom H R) :=
  Subtype.val_injective

variable {H R}

theorem mem_support_map_of_mem {a b : ↥(R : Set W)} (w : (H.induce (R : Set W)).Walk a b)
    {y : ↥(R : Set W)} (hy : y ∈ w.support) : y.1 ∈ (w.map (liftHom H R)).support := by
  rw [SimpleGraph.Walk.support_map]
  exact List.mem_map.mpr ⟨y, hy, rfl⟩

theorem exists_of_mem_support_map {a b : ↥(R : Set W)} (w : (H.induce (R : Set W)).Walk a b)
    {x : W} (hx : x ∈ (w.map (liftHom H R)).support) : ∃ y ∈ w.support, y.1 = x := by
  rw [SimpleGraph.Walk.support_map] at hx
  exact List.mem_map.mp hx

theorem isPath_map {a b : ↥(R : Set W)} {w : (H.induce (R : Set W)).Walk a b} (hw : w.IsPath) :
    (w.map (liftHom H R)).IsPath :=
  (SimpleGraph.Walk.isPath_map_iff_of_injective (liftHom_injective H R)).mpr hw

variable [DecidableEq W]

/-- A port set `P ⊆ R` of `H`, pulled back to `↥(R : Set W)`. -/
def pullPorts (P : Finset W) : Finset ↥(R : Set W) :=
  P.subtype (fun y => y ∈ (R : Set W))

theorem mem_pullPorts {P : Finset W} {y : ↥(R : Set W)} :
    y ∈ pullPorts (R := R) P ↔ y.1 ∈ P :=
  Finset.mem_subtype

theorem pullPorts_map {P : Finset W} (hP : P ⊆ R) :
    (pullPorts (R := R) P).map (Function.Embedding.subtype _) = P := by
  unfold pullPorts
  exact Finset.subtype_map_of_mem (fun x hx => hP hx)

theorem card_pullPorts {P : Finset W} (hP : P ⊆ R) : (pullPorts (R := R) P).card = P.card := by
  have h := Finset.card_map (s := pullPorts (R := R) P)
    (Function.Embedding.subtype (fun y => y ∈ (R : Set W)))
  rw [pullPorts_map hP] at h
  exact h.symm

theorem pullPorts_subset {A' : Finset ↥(R : Set W)} {P : Finset W} (hP : P ⊆ liftLayer A') :
    pullPorts (R := R) P ⊆ A' := fun _ hy =>
  mem_of_mem_liftLayer (hP (mem_pullPorts.mp hy))

/-- Push a port path of `H.induce (R : Set W)` inside `A'` with ports in `pullPorts P` to a port
path of `H` inside `liftLayer A'` with ports in `P`. -/
def liftPortPath {A' : Finset ↥(R : Set W)} {P : Finset W}
    (q : PortPath (H.induce (R : Set W)) A' (pullPorts (R := R) P)) :
    PortPath H (liftLayer A') P where
  first := q.first.1
  last := q.last.1
  walk := q.walk.map (liftHom H R)
  distinct := fun h => q.distinct (Subtype.ext h)
  first_mem := mem_pullPorts.mp q.first_mem
  last_mem := mem_pullPorts.mp q.last_mem
  isPath := isPath_map q.isPath
  inside := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := exists_of_mem_support_map q.walk hx
    exact mem_liftLayer_of_mem (q.inside y hy)
  internal := by
    intro x hx hxf hxl hxP
    obtain ⟨y, hy, rfl⟩ := exists_of_mem_support_map q.walk hx
    exact q.internal y hy (fun h => hxf (congrArg Subtype.val h))
      (fun h => hxl (congrArg Subtype.val h)) (mem_pullPorts.mpr hxP)

/-- `Linked` transports from the induced graph on `R` to the host. -/
theorem linked_liftLayer (A' : Finset ↥(R : Set W)) (γ : ℝ)
    (hL : Linked (H.induce (R : Set W)) A' γ) : Linked H (liftLayer A') γ := by
  intro P hPA hP2
  have hPR : P ⊆ R := hPA.trans (liftLayer_subset A')
  have hcard : (pullPorts (R := R) P).card = P.card := card_pullPorts hPR
  obtain ⟨k, hk1, hkγ, paths, hdisj⟩ :=
    hL (pullPorts (R := R) P) (pullPorts_subset hPA) (by rwa [hcard])
  rw [hcard] at hkγ
  refine ⟨k, hk1, hkγ, fun i => liftPortPath (paths i), ?_⟩
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  obtain ⟨y, hy, rfl⟩ := exists_of_mem_support_map (paths i).walk hxi
  obtain ⟨z, hz, hzy⟩ := exists_of_mem_support_map (paths j).walk hxj
  have hzy' : z = y := Subtype.ext hzy
  subst hzy'
  exact Set.disjoint_left.mp (hdisj hij) hy hz

omit [DecidableEq W] in
/-- `InsideConnected` transports from the induced graph on `R` to the host. -/
theorem insideConnected_liftLayer (A' : Finset ↥(R : Set W))
    (hC : InsideConnected (H.induce (R : Set W)) A') : InsideConnected H (liftLayer A') := by
  intro x hx y hy hxy
  obtain ⟨x', hx', rfl⟩ := mem_liftLayer.mp hx
  obtain ⟨y', hy', rfl⟩ := mem_liftLayer.mp hy
  obtain ⟨w, hwp, hwA⟩ := hC x' hx' y' hy' (fun h => hxy (congrArg Subtype.val h))
  refine ⟨w.map (liftHom H R), isPath_map hwp, ?_⟩
  intro z hz
  obtain ⟨u, hu, rfl⟩ := exists_of_mem_support_map w hz
  exact mem_liftLayer_of_mem (hwA u hu)

end Transport

/-! ### 6. Stage-7 entry point -/

section Package

/-- Everything the merger stage needs about one family of layers, stated in `W`. Inputs: MaskCore's
`R = Qᶜ`, `|N_H(v) ∩ Q| ≤ 2p·deg v`, `deg ≤ 100d`; the load inequality `800·p·d ≤ rho`
(written (3)); for each layer `A' i ⊆ ↥(R : Set W)` the `LayerGood` query conjunct
(`query_bound_of_layerGood`), and stage 5's `Linked`/`InsideConnected` for `H.induce (R : Set W)`;
pairwise disjointness from `exists_tough_layers`. Output: layers `A i = liftLayer (A' i)` in `W`
with `A i ⊆ R`, `Disjoint Q (A i)`, pairwise disjoint, a token injection of `↥(Q : Set W) × Bool`
into each, `Linked H (A i) γ`, `InsideConnected H (A i)`, and `|A i| = |A' i|`. -/
theorem layers_package [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (Q R : Finset W) (hR : R = Qᶜ) (p d rho γ : ℝ) (hp : 0 ≤ p) (hrho : 0 < rho)
    (hQ : ∀ v, ((H.neighborFinset v ∩ Q).card : ℝ) ≤ 2*p*(H.degree v : ℝ))
    (hhi : ∀ v, (H.degree v : ℝ) ≤ 100*d) (hpd : 800*p*d ≤ rho)
    {ι : Type*} (A' : ι → Finset ↥(R : Set W))
    (hS : ∀ i (x : ↥(Q : Set W)), rho/2 ≤ ((querySet H Q R x ∩ A' i).card : ℝ))
    (hdisj : Pairwise fun i j => Disjoint (A' i) (A' j))
    (hL : ∀ i, Linked (H.induce (R : Set W)) (A' i) γ)
    (hC : ∀ i, InsideConnected (H.induce (R : Set W)) (A' i)) :
    ∃ A : ι → Finset W,
      (∀ i, A i ⊆ R) ∧ (∀ i, Disjoint Q (A i)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      (∀ i, ∃ f : (↥(Q : Set W) × Bool) → W, Function.Injective f ∧
        ∀ z, f z ∈ A i ∧ H.Adj z.1.val (f z)) ∧
      (∀ i, Linked H (A i) γ) ∧ (∀ i, InsideConnected H (A i)) ∧
      (∀ i, (A i).card = (A' i).card) :=
  ⟨fun i => liftLayer (A' i), fun _ => liftLayer_subset _,
    fun _ => disjoint_liftLayer_of_compl hR _, pairwise_disjoint_liftLayer hdisj,
    fun i => exists_token_injection_of_layerGood H Q R (A' i) p d rho hp hrho hQ hhi hpd (hS i),
    fun i => linked_liftLayer (A' i) γ (hL i), fun i => insideConnected_liftLayer (A' i) (hC i),
    fun _ => card_liftLayer _⟩

end Package

end Erdos642.Log3V1_20261024

import Openmath.Erdos642.Proofs.DenseMask20261019.GallaiHitting
import Openmath.Erdos642.Proofs.DenseMask20261019.DeletionComponents
import Openmath.Erdos642.Proofs.Log3V1_20261024.Interface

   
                                                                                      
                                                                                       
                               

                                                        

                                                                                        
                                                                                 
                                                                                
                                       

                                                                                            
                                                                                           
                                                                                        
                                                                                            
                                     
  

namespace Erdos642.Log3V1_20261024

open SimpleGraph
open Erdos642.DenseMask20261019

section Inclusion

variable {W : Type*}

/-- The inclusion homomorphism of an induced subgraph into the ambient graph. -/
def inducedInclusion (H : SimpleGraph W) (s : Set W) : H.induce s →g H where
  toFun := Subtype.val
  map_rel' := fun h => h

@[simp] theorem inducedInclusion_apply (H : SimpleGraph W) (s : Set W) (x : ↥s) :
    inducedInclusion H s x = x.val := rfl

theorem inducedInclusion_injective (H : SimpleGraph W) (s : Set W) :
    Function.Injective (inducedInclusion H s) :=
  fun _ _ h => Subtype.ext h

theorem mem_support_map_inclusion (H : SimpleGraph W) (s : Set W) {u v : ↥s}
    (w : (H.induce s).Walk u v) (x : W) :
    x ∈ (w.map (inducedInclusion H s)).support ↔ ∃ a ∈ w.support, a.val = x := by
  rw [Walk.support_map, List.mem_map]
  simp only [inducedInclusion_apply]

/-- Two unreachable vertices give at least two components after deleting nothing. -/
theorem two_le_card_components_of_not_reachable [Finite W] (H : SimpleGraph W) {u v : W}
    (h : ¬ H.Reachable u v) :
    2 ≤ Nat.card (H.induce (∅ : Set W)ᶜ).ConnectedComponent := by
  have hu : u ∈ (∅ : Set W)ᶜ := Set.notMem_empty u
  have hv : v ∈ (∅ : Set W)ᶜ := Set.notMem_empty v
  have hne : (H.induce (∅ : Set W)ᶜ).connectedComponentMk ⟨u, hu⟩ ≠
      (H.induce (∅ : Set W)ᶜ).connectedComponentMk ⟨v, hv⟩ := fun heq =>
    h ((ConnectedComponent.exact heq).map (inducedInclusion H (∅ : Set W)ᶜ))
  exact (Finite.one_lt_card_iff_nontrivial).mpr (nontrivial_of_ne _ _ hne)

/-- Pairwise separated ports outside `X` lie in distinct components of `H - X`. -/
theorem ncard_diff_le_card_components [Finite W] (H : SimpleGraph W) (Q X : Set W)
    (hsep : ∀ x y : ↥(Xᶜ), x.val ∈ Q → y.val ∈ Q → (H.induce Xᶜ).Reachable x y → x = y) :
    (Q \ X).ncard ≤ Nat.card (H.induce Xᶜ).ConnectedComponent := by
  let f : ↥(Q \ X) → (H.induce Xᶜ).ConnectedComponent := fun z =>
    (H.induce Xᶜ).connectedComponentMk ⟨z.val, z.property.2⟩
  have hf : Function.Injective f := by
    intro z w hzw
    have h := hsep ⟨z.val, z.property.2⟩ ⟨w.val, w.property.2⟩ z.property.1 w.property.1
      (ConnectedComponent.exact hzw)
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective f hf

/-- A positively tough graph is connected. -/
theorem reachable_of_ordinaryTough [Finite W] (H : SimpleGraph W) {η : ℝ}
    (hη0 : 0 < η) (htough : DeletionComponents.OrdinaryTough H η) (u v : W) :
    H.Reachable u v := by
  by_contra hnr
  have h2 := two_le_card_components_of_not_reachable H hnr
  have ht := htough ∅ h2
  rw [Set.ncard_empty, Nat.cast_zero] at ht
  have h2' : (2 : ℝ) ≤ (Nat.card (H.induce (∅ : Set W)ᶜ).ConnectedComponent : ℝ) := by
    exact_mod_cast h2
  linarith [mul_le_mul_of_nonneg_left h2' hη0.le]

end Inclusion

/-- The counting contradiction behind the Gallai separation branch: `n` ports, `m` deleted
vertices, `c` surviving components with `n ≤ c + m`, `m ≤ 2⌈ηn/4⌉ - 2`, and toughness. -/
theorem no_small_separator {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (n m c : ℕ) (hn : 2 ≤ n)
    (hcount : n ≤ c + m) (hX : m ≤ 2 * ⌈η * (n : ℝ) / 4⌉₊ - 2)
    (htough : 2 ≤ c → η * (c : ℝ) ≤ (m : ℝ)) : False := by
  set k := ⌈η * (n : ℝ) / 4⌉₊ with hk
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx0 : 0 < η * (n : ℝ) / 4 := div_pos (mul_pos hη0 (by linarith)) (by norm_num)
  have hkpos : 0 < k := Nat.ceil_pos.mpr hx0
  have hklt : (k : ℝ) < η * (n : ℝ) / 4 + 1 := Nat.ceil_lt_add_one hx0.le
  have hm2 : m + 2 ≤ 2 * k := by omega
  have hm2' : (m : ℝ) + 2 ≤ 2 * (k : ℝ) := by exact_mod_cast hm2
  have hcount' : (n : ℝ) ≤ (c : ℝ) + (m : ℝ) := by exact_mod_cast hcount
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  by_cases hc : 2 ≤ c
  · have h1 := htough hc
    -- η n ≤ η c + η m ≤ m + m, while m + 2 ≤ 2k < η n / 2 + 2.
    have hA : η * (n : ℝ) ≤ η * ((c : ℝ) + (m : ℝ)) := mul_le_mul_of_nonneg_left hcount' hη0.le
    have hB : η * (m : ℝ) ≤ (m : ℝ) := mul_le_of_le_one_left hm0 hη1
    nlinarith
  · have hc1 : c ≤ 1 := by omega
    have hc1' : (c : ℝ) ≤ 1 := by exact_mod_cast hc1
    -- n ≤ 1 + m, m + 2 ≤ 2k < η n / 2 + 2 ≤ n / 2 + 2, forcing n < 2.
    have hC : η * (n : ℝ) ≤ (n : ℝ) := mul_le_of_le_one_left (by linarith) hη1
    nlinarith

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The port set `P` viewed inside the vertex type of `G[A]`. -/
def innerPorts (A P : Finset V) : Set ↥(A : Set V) := {x | x.val ∈ P}

omit [Fintype V] [DecidableEq V] in
theorem ncard_innerPorts (A P : Finset V) (hPA : P ⊆ A) :
    (innerPorts A P).ncard = P.card := by
  have himg : Subtype.val '' innerPorts A P = (P : Set V) := by
    ext v
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact Finset.mem_coe.mpr ha
    · intro hv
      exact ⟨⟨v, Finset.mem_coe.mpr (hPA (Finset.mem_coe.mp hv))⟩, Finset.mem_coe.mp hv, rfl⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg, Set.ncard_coe_finset]

/-- A Gallai `A`-path of `G[A]` with terminals in the inner ports is a port path of `G`. -/
def portPathOfAPath (G : SimpleGraph V) (A P : Finset V)
    (q : GallaiPaths.APath (G.induce (A : Set V)) (innerPorts A P)) : PortPath G A P where
  first := q.first.val
  last := q.last.val
  walk := q.walk.map (inducedInclusion G (A : Set V))
  distinct := fun h => q.distinct (Subtype.ext h)
  first_mem := q.first_mem
  last_mem := q.last_mem
  isPath := q.simple.map (inducedInclusion_injective G (A : Set V))
  inside := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := (mem_support_map_inclusion G (A : Set V) q.walk x).mp hx
    exact Finset.mem_coe.mp a.property
  internal := by
    intro x hx hf hl hP
    obtain ⟨a, ha, rfl⟩ := (mem_support_map_inclusion G (A : Set V) q.walk x).mp hx
    exact q.internal a ha (fun h => hf (congrArg Subtype.val h))
      (fun h => hl (congrArg Subtype.val h)) hP

omit [Fintype V] [DecidableEq V] in
theorem portPathOfAPath_support (G : SimpleGraph V) (A P : Finset V)
    (q : GallaiPaths.APath (G.induce (A : Set V)) (innerPorts A P)) (x : V) :
    x ∈ (portPathOfAPath G A P q).walk.support ↔ ∃ a ∈ q.walk.support, a.val = x :=
  mem_support_map_inclusion G (A : Set V) q.walk x

omit [Fintype V] [DecidableEq V] in
/-- Vertex-disjointness of Gallai paths survives the inclusion into `G`. -/
theorem pairwise_disjoint_portPathOfAPath (G : SimpleGraph V) (A P : Finset V) {k : ℕ}
    (p : Fin k → GallaiPaths.APath (G.induce (A : Set V)) (innerPorts A P))
    (hp : Pairwise fun i j =>
      Disjoint {x | x ∈ (p i).walk.support} {x | x ∈ (p j).walk.support}) :
    Pairwise fun i j => Disjoint {x | x ∈ (portPathOfAPath G A P (p i)).walk.support}
      {x | x ∈ (portPathOfAPath G A P (p j)).walk.support} := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  obtain ⟨a, ha, hax⟩ := (portPathOfAPath_support G A P (p i) x).mp hxi
  obtain ⟨b, hb, hbx⟩ := (portPathOfAPath_support G A P (p j) x).mp hxj
  have hba : b = a := Subtype.ext (hbx.trans hax.symm)
  subst hba
  exact Set.disjoint_left.mp (hp hij) ha hb

omit [DecidableEq V] in
/-- Stage 5, part 1: ordinary `η`-toughness of `G[A]` supplies `η/4 · |P|` disjoint port paths. -/
theorem linked_of_ordinaryTough (G : SimpleGraph V) (A : Finset V)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (htough : DeletionComponents.OrdinaryTough (G.induce (A : Set V)) η) :
    Linked G A (η / 4) := by
  classical
  intro P hPA hP2
  have hn' : (2 : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hP2
  have hx0 : 0 < η * (P.card : ℝ) / 4 := div_pos (mul_pos hη0 (by linarith)) (by norm_num)
  set k := ⌈η * (P.card : ℝ) / 4⌉₊ with hk
  have hkpos : 0 < k := Nat.ceil_pos.mpr hx0
  have hkge : η / 4 * (P.card : ℝ) ≤ (k : ℝ) := by
    rw [hk]
    have := Nat.le_ceil (η * (P.card : ℝ) / 4)
    linarith
  refine ⟨k, hkpos, hkge, ?_⟩
  rcases GallaiHitting.gallai_alternative (G.induce (A : Set V)) (innerPorts A P) k with
    ⟨p, hp⟩ | ⟨X, hX, hsep⟩
  · exact ⟨fun i => portPathOfAPath G A P (p i), pairwise_disjoint_portPathOfAPath G A P p hp⟩
  · exfalso
    have h1 := ncard_diff_le_card_components (G.induce (A : Set V)) (innerPorts A P) X hsep
    have h2 := Set.ncard_le_ncard_sdiff_add_ncard (innerPorts A P) X
    rw [ncard_innerPorts A P hPA] at h2
    exact no_small_separator hη0 hη1 P.card X.ncard
      (Nat.card ((G.induce (A : Set V)).induce Xᶜ).ConnectedComponent) hP2
      (le_trans h2 (Nat.add_le_add_right h1 _)) hX (fun hc => htough X hc)

omit [DecidableEq V] in
/-- Stage 5, part 2: ordinary `η`-toughness of `G[A]` with `η > 0` connects `A` inside itself. -/
theorem insideConnected_of_ordinaryTough (G : SimpleGraph V) (A : Finset V)
    {η : ℝ} (hη0 : 0 < η)
    (htough : DeletionComponents.OrdinaryTough (G.induce (A : Set V)) η) :
    InsideConnected G A := by
  intro x hx y hy _hxy
  obtain ⟨w, hw⟩ := (reachable_of_ordinaryTough (G.induce (A : Set V)) hη0 htough
    ⟨x, Finset.mem_coe.mpr hx⟩ ⟨y, Finset.mem_coe.mpr hy⟩).exists_isPath
  refine ⟨w.map (inducedInclusion G (A : Set V)),
    hw.map (inducedInclusion_injective G (A : Set V)), ?_⟩
  intro z hz
  obtain ⟨a, _, rfl⟩ := (mem_support_map_inclusion G (A : Set V) w z).mp hz
  exact Finset.mem_coe.mp a.property

end Erdos642.Log3V1_20261024

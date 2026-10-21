import Openmath.Erdos642.Proofs.DenseMask20261019.SamplingObstruction

/-! Actual component unions in the nested-mask sampling obstruction. -/
namespace Erdos642.DenseMask20261019.ComponentObstruction

open SimpleGraph Finset
open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3.CutExtraction

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- All vertices in S whose actual induced component meets S intersect T. -/
noncomputable def componentUnion (S T : Finset V) : Finset V := by
  classical
  exact S.filter fun v => ∃ u ∈ S ∩ T,
    (mask G S).connectedComponentMk u = (mask G S).connectedComponentMk v

/-- Original vertices of a component of the graph induced on S. -/
noncomputable def componentVertices (S : Finset V)
    (c : (mask G S).ConnectedComponent) : Finset V := by
  classical
  exact S.filter fun v => v ∈ c.supp

/-- Literal original closed neighborhood. -/
def closedNeighborhood (S : Finset V) : Finset V :=
  S ∪ S.biUnion (fun v => G.neighborFinset v)

@[simp] theorem mem_componentUnion (S T : Finset V) (v : V) :
    v ∈ componentUnion G S T ↔ v ∈ S ∧ ∃ u ∈ S ∩ T,
      (mask G S).Reachable u v := by
  classical
  simp [componentUnion, ConnectedComponent.eq]

@[simp] theorem mem_componentVertices (S : Finset V)
    (c : (mask G S).ConnectedComponent) (v : V) :
    v ∈ componentVertices G S c ↔ v ∈ S ∧ v ∈ c.supp := by
  classical
  simp [componentVertices]

/-- Original-edge closure propagates along every induced walk. -/
theorem reachable_mem_closed (S U W : Finset V) (hSW : S ⊆ W)
    (hclosed : ∀ x ∈ U, ∀ y ∈ W, G.Adj x y → y ∈ U)
    {x y : V} (hx : x ∈ U) (hxy : (mask G S).Reachable x y) : y ∈ U := by
  have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hxy
  clear hxy
  induction hr with
  | refl => exact hx
  | tail _ hadj ih => exact hclosed _ ih _ (hSW hadj.2.2) hadj.1

/-- A closed bad region is a union of all the components it meets. -/
theorem componentUnion_eq_inter (S U W : Finset V) (hSW : S ⊆ W)
    (hclosed : ∀ x ∈ U, ∀ y ∈ W, G.Adj x y → y ∈ U) :
    componentUnion G S U = S ∩ U := by
  classical
  ext v
  rw [mem_componentUnion, Finset.mem_inter]
  constructor
  · rintro ⟨hv, u, hu, hreach⟩
    exact ⟨hv, reachable_mem_closed G S U W hSW hclosed
      (Finset.mem_inter.mp hu).2 hreach⟩
  · rintro ⟨hv, hu⟩
    exact ⟨hv, v, Finset.mem_inter.mpr ⟨hv, hu⟩, Reachable.rfl⟩

/-- Every half-mask center has an actual quarter-mask neighbor. -/
theorem nested_componentUnion_eq (Q M U W : Finset V)
    (hQM : Q ⊆ M) (hMW : M ⊆ W)
    (hclosed : ∀ x ∈ U, ∀ y ∈ W, G.Adj x y → y ∈ U)
    (hneighbor : ∀ v ∈ M, ∃ w ∈ Q, G.Adj v w) :
    componentUnion G M (componentUnion G Q U) = M ∩ U := by
  classical
  have hseed := componentUnion_eq_inter G Q U W (hQM.trans hMW) hclosed
  ext v
  rw [mem_componentUnion, Finset.mem_inter]
  constructor
  · rintro ⟨hv, u, hu, hreach⟩
    have huU : u ∈ U := by
      rw [hseed] at hu
      exact (Finset.mem_inter.mp (Finset.mem_inter.mp hu).2).2
    exact ⟨hv, reachable_mem_closed G M U W hMW hclosed huU hreach⟩
  · rintro ⟨hvM, hvU⟩
    obtain ⟨w, hwQ, hvw⟩ := hneighbor v hvM
    have hwU := hclosed v hvU w (hMW (hQM hwQ)) hvw
    have hwseed : w ∈ componentUnion G Q U := by
      rw [hseed]
      exact Finset.mem_inter.mpr ⟨hwQ, hwU⟩
    exact ⟨hvM, w, Finset.mem_inter.mpr ⟨hQM hwQ, hwseed⟩,
      (show (mask G M).Adj w v from ⟨hvw.symm, hQM hwQ, hvM⟩).reachable⟩

/-- Reached half-mask components stay in the original closed neighborhood. -/
theorem nested_componentUnion_subset_neighborhood (Q M U W : Finset V)
    (hQM : Q ⊆ M) (hMW : M ⊆ W)
    (hclosed : ∀ x ∈ U, ∀ y ∈ W, G.Adj x y → y ∈ U)
    (hneighbor : ∀ v ∈ M, ∃ w ∈ Q, G.Adj v w) :
    componentUnion G M (componentUnion G Q U) ⊆
      closedNeighborhood G (componentUnion G Q U) := by
  classical
  rw [nested_componentUnion_eq G Q M U W hQM hMW hclosed hneighbor]
  intro v hv
  obtain ⟨w, hwQ, hvw⟩ := hneighbor v (Finset.mem_inter.mp hv).1
  have hwU := hclosed v (Finset.mem_inter.mp hv).2 w (hMW (hQM hwQ)) hvw
  have hwseed : w ∈ componentUnion G Q U := by
    rw [componentUnion_eq_inter G Q U W (hQM.trans hMW) hclosed]
    exact Finset.mem_inter.mpr ⟨hwQ, hwU⟩
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨w, hwseed,
    (G.mem_neighborFinset w v).mpr hvw.symm⟩

/-- An actual component retains every original neighbor inside Q. -/
theorem component_restrictedDegree (Q : Finset V)
    (c : (mask G Q).ConnectedComponent) {x : V}
    (hx : x ∈ componentVertices G Q c) :
    restrictedDegree G (componentVertices G Q c) x = restrictedDegree G Q x := by
  classical
  obtain ⟨hxQ, hxc⟩ := (mem_componentVertices G Q c x).mp hx
  unfold restrictedDegree
  apply congrArg Finset.card
  ext y
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hy, hadj⟩
    exact ⟨((mem_componentVertices G Q c y).mp hy).1, hadj⟩
  · rintro ⟨hyQ, hadj⟩
    exact ⟨(mem_componentVertices G Q c y).mpr ⟨hyQ,
      c.mem_supp_of_adj_mem_supp hxc ⟨hadj, hxQ, hyQ⟩⟩, hadj⟩

/-- Apply a degree-to-order supplier to literal original component vertices. -/
theorem component_order_lower (Q : Finset V) (q m : ℝ)
    (hdegree : ∀ x ∈ Q, q ≤ (restrictedDegree G Q x : ℝ))
    (horder : ∀ S : Finset V, S.Nonempty →
      (∀ x ∈ S, q ≤ (restrictedDegree G S x : ℝ)) → m ≤ (S.card : ℝ))
    (c : (mask G Q).ConnectedComponent)
    (hmeet : ∃ x ∈ Q, x ∈ c.supp) :
    m ≤ ((componentVertices G Q c).card : ℝ) := by
  obtain ⟨x, hxQ, hxc⟩ := hmeet
  apply horder _ ⟨x, (mem_componentVertices G Q c x).mpr ⟨hxQ, hxc⟩⟩
  intro y hy
  rw [component_restrictedDegree G Q c hy]
  exact hdegree y ((mem_componentVertices G Q c y).mp hy).1

/-- Complete deterministic component witness for the measured obstruction.
Both unions range over all actual induced components meeting their seeds. -/
theorem exists_component_obstruction (Q M U W : Finset V)
    (hQM : Q ⊆ M) (hMW : M ⊆ W)
    (hclosed : ∀ x ∈ U, ∀ y ∈ W, G.Adj x y → y ∈ U)
    (hneighbor : ∀ v ∈ M, ∃ w ∈ Q, G.Adj v w)
    (q m lo hi : ℝ)
    (hdegree : ∀ x ∈ Q, q ≤ (restrictedDegree G Q x : ℝ))
    (horder : ∀ S : Finset V, S.Nonempty →
      (∀ x ∈ S, q ≤ (restrictedDegree G S x : ℝ)) → m ≤ (S.card : ℝ))
    (hlo : lo ≤ ((Q ∩ U).card : ℝ)) (hhi : ((M ∩ U).card : ℝ) ≤ hi) :
    ∃ A A' : Finset V,
      A = componentUnion G Q U ∧ A' = componentUnion G M A ∧
      A = Q ∩ U ∧ A' = M ∩ U ∧
      lo ≤ (A.card : ℝ) ∧ (A'.card : ℝ) ≤ hi ∧
      A' ⊆ closedNeighborhood G A ∧
      (∀ c : (mask G Q).ConnectedComponent,
        (∃ x ∈ Q ∩ U, x ∈ c.supp) →
        m ≤ ((componentVertices G Q c).card : ℝ)) := by
  refine ⟨componentUnion G Q U, componentUnion G M (componentUnion G Q U),
    rfl, rfl, componentUnion_eq_inter G Q U W (hQM.trans hMW) hclosed,
    nested_componentUnion_eq G Q M U W hQM hMW hclosed hneighbor, ?_, ?_,
    nested_componentUnion_subset_neighborhood G Q M U W hQM hMW hclosed hneighbor, ?_⟩
  · simpa only [componentUnion_eq_inter G Q U W (hQM.trans hMW) hclosed] using hlo
  · simpa only [nested_componentUnion_eq G Q M U W hQM hMW hclosed hneighbor] using hhi
  · intro c hc
    obtain ⟨x, hx, hxc⟩ := hc
    exact component_order_lower G Q q m hdegree horder c
      ⟨x, (Finset.mem_inter.mp hx).1, hxc⟩

end Erdos642.DenseMask20261019.ComponentObstruction

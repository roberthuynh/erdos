import EvenFactor.ComponentGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Finset SimpleGraph
namespace Erdos585.EvenFactorCriterion
open FactorMatching
universe u
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type u} [Fintype V] [DecidableEq V]

lemma component_pair (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V)
    (hne : x ≠ y) (hxy : G.Adj x y)
    (hx : ∀ z, G.Adj x z → z = y) (hy : ∀ z, G.Adj y z → z = x) :
    (G.connectedComponentMk x).supp.ncard = 2 := by
  have hclosed : ∀ v ∈ ({x,y} : Finset V), ∀ w, G.Adj v w → w ∈ ({x,y} : Finset V) := by
    intro v hv w hvw
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl
    · simp [hx w hvw]
    · simp [hy w hvw]
  have hsupp : (G.connectedComponentMk x).supp = ({x,y} : Finset V) := by
    ext z
    constructor
    · intro hz
      exact closed_mem_of_reachable G _ hclosed x z (by simp)
        (ConnectedComponent.exact hz).symm
    · intro hz
      simp only [Finset.mem_coe, mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact (ConnectedComponent.mem_supp_iff _ _).mpr rfl
      · exact ConnectedComponent.sound hxy.reachable.symm
  rw [hsupp, Set.ncard_coe_finset, card_pair hne]

variable (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]

def keptSlot (S T : Finset V) (v : V) (i : Fin q) (hv : v ∉ S) :
    RemainingVertex q G S T := ⟨Sum.inl (v,i),by simpa using hv⟩

def keptStub (S T : Finset V) (d : G.Dart) (hd : d.fst ∉ T) :
    RemainingVertex q G S T := ⟨Sum.inr d,by simpa using hd⟩

lemma stubS_neighbors (S T : Finset V) (d : G.Dart) (hdT : d.fst ∉ T)
    (heT : d.snd ∉ T) (hdS : d.fst ∈ S) (y : RemainingVertex q G S T)
    (h : (remainingGraph q G S T).Adj (keptStub q G S T d hdT) y) :
    y = keptStub q G S T d.symm heT := by
  rcases y with ⟨y,hy⟩
  cases y with
  | inl s =>
    change d.fst = s.1 at h
    exact False.elim (hy ((mem_canonical_slot q G S T s.1 s.2).mpr (h ▸ hdS)))
  | inr e =>
    change e = d.symm at h
    apply Subtype.ext
    exact congrArg Sum.inr h

/-- An S--S original edge leaves an actual even two-stub component. -/
theorem stubSS_even_component (S T : Finset V) (hST : Disjoint S T)
    (d : G.Dart) (hdS : d.fst ∈ S) (heS : d.snd ∈ S) :
    ¬ Odd ((remainingGraph q G S T).connectedComponentMk
      (keptStub q G S T d (fun ht => Finset.disjoint_left.mp hST hdS ht))).supp.ncard := by
  have hdT : d.fst ∉ T := fun ht => Finset.disjoint_left.mp hST hdS ht
  have heT : d.snd ∉ T := fun ht => Finset.disjoint_left.mp hST heS ht
  have hne : keptStub q G S T d hdT ≠ keptStub q G S T d.symm heT := by
    intro h
    have hd : d = d.symm := Sum.inr.inj (congrArg Subtype.val h)
    exact d.symm_ne hd.symm
  have hxy : (remainingGraph q G S T).Adj (keptStub q G S T d hdT)
      (keptStub q G S T d.symm heT) := rfl
  have hcard := component_pair (remainingGraph q G S T) _ _ hne hxy
    (fun y h => stubS_neighbors q G S T d hdT heT hdS y h)
    (fun y h => by simpa using stubS_neighbors q G S T d.symm heT hdT heS y h)
  rw [hcard]
  decide

end Erdos585.EvenFactorCriterion

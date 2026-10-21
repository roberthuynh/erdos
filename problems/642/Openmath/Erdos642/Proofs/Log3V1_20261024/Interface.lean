import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Real.Basic

   
                                                                                                
                                                                             
                                                                                             
                                                                               
  

namespace Erdos642.Log3V1_20261024

open SimpleGraph

variable {W : Type*} [DecidableEq W]

                                                                                             
                                   
structure PortPath (H : SimpleGraph W) (A P : Finset W) where
  first : W
  last : W
  walk : H.Walk first last
  distinct : first ≠ last
  first_mem : first ∈ P
  last_mem : last ∈ P
  isPath : walk.IsPath
  inside : ∀ x ∈ walk.support, x ∈ A
  internal : ∀ x ∈ walk.support, x ≠ first → x ≠ last → x ∉ P

/-- Every port set `P ⊆ A` with at least two ports carries at least `max 1 (γ·|P|)`
pairwise vertex-disjoint port paths inside `A`. -/
def Linked (H : SimpleGraph W) (A : Finset W) (γ : ℝ) : Prop :=
  ∀ P : Finset W, P ⊆ A → 2 ≤ P.card →
    ∃ k : ℕ, 1 ≤ k ∧ γ * (P.card : ℝ) ≤ (k : ℝ) ∧
      ∃ p : Fin k → PortPath H A P,
        Pairwise fun i j => Disjoint {x | x ∈ (p i).walk.support} {x | x ∈ (p j).walk.support}

/-- Any two distinct vertices of `A` are joined by a path of `H` that stays inside `A`. -/
def InsideConnected (H : SimpleGraph W) (A : Finset W) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ∃ w : H.Walk x y, w.IsPath ∧ ∀ z ∈ w.support, z ∈ A

end Erdos642.Log3V1_20261024

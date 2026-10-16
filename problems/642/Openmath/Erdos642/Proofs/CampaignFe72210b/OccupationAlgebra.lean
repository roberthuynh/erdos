import Openmath.Erdos642.Proofs.CampaignFe72210b.OccupationTail
import Openmath.Erdos642.Proofs.CampaignFe72210b.PathAvoidance
import Openmath.Erdos642.Proofs.CampaignFe72210b.ForestBundle

/-! Additive occupation identities for literal finite observation lists. -/
namespace Erdos642.OccupationAlgebra
open Erdos642.FiniteMarkov Erdos642.OccupationTail
variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem vertexSum_mono (f g : V → ℝ) (h : ∀ v, f v ≤ g v)
    {n : ℕ} (x : V) (p : Path V n) :
    Chain.vertexSum f x p ≤ Chain.vertexSum g x p := by
  induction n generalizing x with
  | zero => exact h x
  | succ n ih => exact add_le_add (h x) (ih p.1 p.2)

omit [DecidableEq V] in
theorem vertexSum_sum {I : Type*} (J : Finset I) (f : I → V → ℝ)
    {n : ℕ} (x : V) (p : Path V n) :
    Chain.vertexSum (fun v => ∑ i ∈ J, f i v) x p =
      ∑ i ∈ J, Chain.vertexSum (f i) x p := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change (∑ i ∈ J, f i x) + Chain.vertexSum (fun v => ∑ i ∈ J, f i v) p.1 p.2 =
      ∑ i ∈ J, (f i x + Chain.vertexSum (f i) p.1 p.2)
    rw [ih, Finset.sum_add_distrib]

theorem occupation_mono [Fintype V] {S T : Finset V} (h : S ⊆ T)
    {n : ℕ} (x : V) (p : Path V n) : occupation S x p ≤ occupation T x p := by
  apply vertexSum_mono
  intro v
  by_cases hs : v ∈ S
  · simp [hs, h hs]
  · simp only [hs, if_false]
    split_ifs <;> norm_num

theorem occupation_eq_sum_singletons [Fintype V] (S : Finset V)
    {n : ℕ} (x : V) (p : Path V n) :
    occupation S x p = ∑ v ∈ S, occupation {v} x p := by
  have hf : (fun y : V => if y ∈ S then (1 : ℝ) else 0) =
      (fun y => ∑ v ∈ S, if y = v then (1 : ℝ) else 0) := by
    funext y
    simp
  unfold occupation
  rw [hf, vertexSum_sum]
  simp only [Finset.mem_singleton]

theorem occupation_singleton_eq_count [Fintype V] (v x : V)
    {n : ℕ} (p : Path V n) :
    occupation {v} x p = ((x :: PathCoordinates.future p).count v : ℝ) := by
  induction n generalizing x with
  | zero =>
    by_cases hx : x = v
    · subst v; simp [occupation, Chain.vertexSum, PathCoordinates.future]
    · simp [occupation, Chain.vertexSum, PathCoordinates.future, hx]
  | succ n ih =>
    rcases p with ⟨y, p⟩
    change (if x ∈ ({v} : Finset V) then (1 : ℝ) else 0) +
      occupation {v} y p = _
    rw [ih]
    by_cases hx : x = v
    · subst v; simp [PathCoordinates.future, List.count_cons, add_comm]
    · simp [PathCoordinates.future, List.count_cons, hx]

end Erdos642.OccupationAlgebra

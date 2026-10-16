import Openmath.Erdos642.Proofs.CampaignFe72210b.CycleSupport

namespace Erdos642.CampaignFe72210b
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {u v : V}

/-- The actual walk segment from index i through index j. -/
def intervalPath (p : G.Walk u v) (i j : ℕ) (hij : i ≤ j) :
    G.Walk (p.getVert i) (p.getVert j) :=
  ((p.drop i).take (j-i)).copy rfl (by simp [Nat.add_sub_of_le hij])

theorem intervalPath_length (p : G.Walk u v) (i j : ℕ) (hij : i ≤ j)
    (hj : j ≤ p.length) : (intervalPath p i j hij).length = j-i := by
  simp [intervalPath, Nat.min_eq_left (show j-i ≤ p.length-i by omega)]

theorem intervalPath_isPath (p : G.Walk u v) (hp : p.IsPath)
    (i j : ℕ) (hij : i ≤ j) : (intervalPath p i j hij).IsPath := by
  simpa [intervalPath] using (hp.drop i).take (j-i)

theorem intervalPath_support (p : G.Walk u v) (i j : ℕ) (hij : i ≤ j)
    (hj : j ≤ p.length) :
    (intervalPath p i j hij).support = (p.support.drop i).take (j-i+1) := by
  simp [intervalPath, Walk.support_take, Walk.drop_support_eq_support_drop_min,
    Nat.min_eq_left (show i ≤ p.length by omega)]

theorem intervalPath_retains (p : G.Walk u v) (i j : ℕ) (hij : i ≤ j)
    (k : ℕ) (hik : i ≤ k) (hkj : k ≤ j) :
    p.getVert k ∈ (intervalPath p i j hij).support := by
  have h := (intervalPath p i j hij).getVert_mem_support (k-i)
  simpa [intervalPath, Nat.min_eq_right (show k-i ≤ j-i by omega),
    Nat.add_sub_of_le hik] using h

/-- Close the retained interval with the actual host edge. -/
theorem interval_cycle (p : G.Walk u v) (hp : p.IsPath)
    (i j : ℕ) (hsep : i+2 ≤ j) (hj : j ≤ p.length)
    (h : G.Adj (p.getVert i) (p.getVert j)) :
    ∃ c : G.Walk (p.getVert j) (p.getVert j), c.IsCycle ∧
      c.length = j-i+1 ∧
      (∀ x, x ∈ c.support ↔ x ∈ (p.support.drop i).take (j-i+1)) ∧
      (∀ k, i ≤ k → k ≤ j → p.getVert k ∈ c.support) := by
  have hij : i ≤ j := by omega
  let q := intervalPath p i j hij
  refine ⟨Walk.cons h.symm q, ?_, ?_, ?_, ?_⟩
  · apply close_path_isCycle q (intervalPath_isPath p hp i j hij)
    rw [intervalPath_length p i j hij hj]
    omega
  · rw [close_path_length, intervalPath_length p i j hij hj]
  · intro x
    rw [close_path_support, intervalPath_support p i j hij hj]
  · intro k hik hkj
    rw [close_path_support]
    exact intervalPath_retains p i j hij k hik hkj
end Erdos642.CampaignFe72210b

import Openmath.Erdos642.Proofs.CampaignFe72210b.PathAvoidance
import Openmath.Erdos642.Proofs.CampaignFe72210b.GraphPath
import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal

/-! Literal coordinates, self-avoidance, and visited vertices of actual path windows. -/
namespace Erdos642.FiniteMarkov
open PathCoordinates PathAvoidance
variable {V : Type*}

 theorem mem_visited_iff_coordinate [DecidableEq V] {n : ℕ} (x v : V) (p : Path V n) :
    v ∈ visited x p ↔ ∃ j : ℕ, j ≤ n ∧ coordinate x p j = v := by
  rw [mem_visited, List.mem_cons]
  constructor
  · intro h
    rcases h with h | h
    · exact ⟨0, Nat.zero_le _, by simpa only [coordinate_zero] using h.symm⟩
    · obtain ⟨j, _, hj, he⟩ := (mem_future_iff x v p).mp h
      exact ⟨j, hj, he⟩
  · rintro ⟨j, hj, he⟩
    cases j with
    | zero => exact Or.inl (by simpa only [coordinate_zero] using he.symm)
    | succ j => exact Or.inr ((mem_future_iff x v p).mpr ⟨j + 1, by omega, hj, he⟩)

namespace Chain
variable [Fintype V] (C : Chain V)

 theorem coordinate_append_suffix {m n : ℕ} (x : V) (p : Path V m) (q : Path V n) (j : ℕ) :
    coordinate x (C.append p q) (m + j) = coordinate (C.endpoint x p) q j := by
  induction m generalizing x with
  | zero => simp only [Nat.zero_add, append, endpoint]
  | succ m ih =>
    rw [Nat.succ_add]
    exact ih p.1 p.2

 theorem coordinate_append_prefix {m n : ℕ} (x : V) (p : Path V m) (q : Path V n)
    (j : ℕ) (hj : j ≤ m) : coordinate x (C.append p q) j = coordinate x p j := by
  induction m generalizing x j with
  | zero =>
    have hz : j = 0 := by omega
    subst j
    simp
  | succ m ih =>
    cases j with
    | zero => simp
    | succ j => exact ih p.1 p.2 j (by omega)

variable [DecidableEq V]

include C in
 theorem actualSA_split_prefix (a n : ℕ) (x : V) (p : Path V (n + a))
    (h : actualSA x p) : actualSA x (PathSplit.split a n p).1 := by
  have hh := C.actualSA_append_iff x (PathSplit.split a n p).1 (PathSplit.split a n p).2
  rw [C.append_split] at hh
  exact (hh.mp h).1

 theorem actualSA_split_suffix (a n : ℕ) (x : V) (p : Path V (n + a))
    (h : actualSA x p) : actualSA (C.endpoint x (PathSplit.split a n p).1)
      (PathSplit.split a n p).2 := by
  have hh := C.actualSA_append_iff x (PathSplit.split a n p).1 (PathSplit.split a n p).2
  rw [C.append_split] at hh
  exact (hh.mp h).2.1

/-- The literal window path; the prefix and suffix are actual split components. -/
def windowPath (a n r : ℕ) (p : Path V ((r + n) + a)) : Path V n :=
  (PathSplit.split n r (PathSplit.split a (r + n) p).2).1

def windowStart (a n r : ℕ) (x : V) (p : Path V ((r + n) + a)) : V :=
  C.endpoint x (PathSplit.split a (r + n) p).1

omit [DecidableEq V] in
 theorem coordinate_window (a n r : ℕ) (x : V) (p : Path V ((r + n) + a))
    (j : ℕ) (hj : j ≤ n) :
    coordinate x p (a + j) = coordinate (C.windowStart a n r x p) (windowPath a n r p) j := by
  have h1 := C.coordinate_append_suffix x (PathSplit.split a (r + n) p).1
    (PathSplit.split a (r + n) p).2 j
  rw [C.append_split] at h1
  have h2 := C.coordinate_append_prefix (C.windowStart a n r x p)
    (PathSplit.split n r (PathSplit.split a (r + n) p).2).1
    (PathSplit.split n r (PathSplit.split a (r + n) p).2).2 j hj
  rw [C.append_split] at h2
  exact h1.trans h2

 theorem actualSA_window (a n r : ℕ) (x : V) (p : Path V ((r + n) + a))
    (h : actualSA x p) : actualSA (C.windowStart a n r x p) (windowPath a n r p) := by
  have hs := C.actualSA_split_suffix a (r + n) x p h
  exact C.actualSA_split_prefix n r (C.windowStart a n r x p)
    (PathSplit.split a (r + n) p).2 hs

 theorem visited_window_coordinate (a n r : ℕ) (x v : V) (p : Path V ((r + n) + a))
    (hv : v ∈ visited (C.windowStart a n r x p) (windowPath a n r p)) :
    ∃ i : ℕ, a ≤ i ∧ i ≤ a + n ∧ coordinate x p i = v := by
  obtain ⟨j, hj, he⟩ := (mem_visited_iff_coordinate _ v _).mp hv
  refine ⟨a + j, by omega, by omega, ?_⟩
  exact (C.coordinate_window a n r x p j hj).trans he

end Chain
end Erdos642.FiniteMarkov

namespace Erdos642.CampaignFe72210b
open Erdos642.FiniteMarkov Erdos642.FiniteMarkov.PathCoordinates
variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg : ∀ x : V, 0 < G.degree x)

/-- The actual reconstructed graph walk has exactly the original finite-path coordinates. -/
theorem positiveWalk_getVert {n : ℕ} (x : V) (p : Path V n)
    (h : 0 < (graphChain G hdeg).weight x p) (j : ℕ) :
    (positiveWalk G hdeg x p h).getVert j = coordinate x p j := by
  induction n generalizing x j with
  | zero => cases j <;> rfl
  | succ n ih =>
    cases j with
    | zero => rfl
    | succ j => apply ih

end Erdos642.CampaignFe72210b

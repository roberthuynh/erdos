import Openmath.Erdos642.Proofs.CampaignFe72210b.PathCoordinates

namespace Erdos642.FiniteMarkov
open PathCoordinates
variable {V : Type*}
namespace PathAvoidance

def actualSA {n : ℕ} (x : V) (p : Path V n) : Prop := (x :: future p).Nodup

def visited [DecidableEq V] {n : ℕ} (x : V) (p : Path V n) : Finset V :=
  (x :: future p).toFinset

theorem mem_visited [DecidableEq V] {n : ℕ} (x a : V) (p : Path V n) :
    a ∈ visited x p ↔ a ∈ x :: future p := by simp [visited]

theorem visited_card_le [DecidableEq V] {n : ℕ} (x : V) (p : Path V n) :
    (visited x p).card ≤ n+1 := by
  have h := List.toFinset_card_le (x :: future p)
  simpa [visited] using h
end PathAvoidance
namespace Chain
variable [Fintype V] (C : Chain V)
open PathAvoidance

theorem future_append {m n : ℕ} (p : Path V m) (q : Path V n) :
    future (C.append p q) = future p ++ future q := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rcases p with ⟨y,p⟩
    simp only [append, future, List.cons_append, ih]

theorem endpoint_mem_vertices {n : ℕ} (x : V) (p : Path V n) :
    C.endpoint x p ∈ x :: future p := by
  induction n generalizing x with
  | zero => simp [endpoint]
  | succ n ih =>
    exact List.mem_cons_of_mem x (ih p.1 p.2)

variable [DecidableEq V]

theorem visited_prefix_subset {m n : ℕ} (x : V) (p : Path V m) (q : Path V n) :
    visited x p ⊆ visited x (C.append p q) := by
  intro a ha
  simp only [mem_visited, C.future_append, List.mem_cons, List.mem_append] at ha ⊢
  tauto

theorem actualSA_append_iff {m n : ℕ} (x : V) (p : Path V m) (q : Path V n) :
    actualSA x (C.append p q) ↔ actualSA x p ∧
      actualSA (C.endpoint x p) q ∧
      ¬ actualHit (visited x p) (C.endpoint x p) q := by
  rw [actualSA, C.future_append, ← List.cons_append, List.nodup_append']
  constructor
  · rintro ⟨hp, hq, hd⟩
    have hav : ¬ actualHit (visited x p) (C.endpoint x p) q := by
      rintro ⟨a, haq, hap⟩
      exact List.disjoint_left.mp hd ((mem_visited x a p).mp hap) haq
    refine ⟨hp, ?_, hav⟩
    apply List.nodup_cons.mpr
    refine ⟨?_, hq⟩
    intro hend
    exact List.disjoint_left.mp hd (C.endpoint_mem_vertices x p) hend
  · rintro ⟨hp, hq, hav⟩
    refine ⟨hp, (List.nodup_cons.mp hq).2, ?_⟩
    apply List.disjoint_left.mpr
    intro a hap haq
    exact hav ⟨a, haq, (mem_visited x a p).mpr hap⟩
end Chain
end Erdos642.FiniteMarkov

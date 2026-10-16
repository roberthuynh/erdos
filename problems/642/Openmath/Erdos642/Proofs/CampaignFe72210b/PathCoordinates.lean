import Openmath.Erdos642.Proofs.CampaignFe72210b.PathSplit
import Openmath.Erdos642.Proofs.CampaignFe72210b.PathEvents

namespace Erdos642.FiniteMarkov
variable {V : Type*}
namespace PathCoordinates

def future : {n : ℕ} → Path V n → List V
  | 0, _ => []
  | _+1, (y,p) => y :: future p

@[simp] theorem future_length {n : ℕ} (p : Path V n) : (future p).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ (ih p.2)

def coordinate : {n : ℕ} → V → Path V n → ℕ → V
  | _, x, _, 0 => x
  | 0, x, _, _+1 => x
  | _+1, _, (y,p), t+1 => coordinate y p t

@[simp] theorem coordinate_zero {n : ℕ} (x : V) (p : Path V n) :
    coordinate x p 0 = x := by cases n <;> rfl

theorem mem_future_iff {n : ℕ} (x a : V) (p : Path V n) :
    a ∈ future p ↔ ∃ t, 1 ≤ t ∧ t ≤ n ∧ coordinate x p t = a := by
  induction n generalizing x with
  | zero => simp only [future, List.not_mem_nil, false_iff, not_exists, not_and]
            intro t ht htn
            omega
  | succ n ih =>
    rcases p with ⟨y,p⟩
    constructor
    · intro h
      rcases List.mem_cons.mp h with h | h
      · exact ⟨1, by omega, by omega, by simpa [coordinate] using h.symm⟩
      · obtain ⟨t, ht, htn, he⟩ := (ih y p).mp h
        exact ⟨t+1, by omega, by omega, he⟩
    · rintro ⟨t, ht, htn, he⟩
      cases t with
      | zero => omega
      | succ t =>
        cases t with
        | zero => exact List.mem_cons.mpr (Or.inl (by simpa [coordinate] using he.symm))
        | succ t =>
          apply List.mem_cons.mpr
          apply Or.inr
          exact (ih y p).mpr ⟨t+1, by omega, by omega, he⟩

def actualHit (A : Finset V) {n : ℕ} (_x : V) (p : Path V n) : Prop :=
  ∃ a ∈ future p, a ∈ A

theorem actualHit_iff {n : ℕ} (A : Finset V) (x : V) (p : Path V n) :
    actualHit A x p ↔ ∃ t ∈ Finset.Icc 1 n, coordinate x p t ∈ A := by
  constructor
  · rintro ⟨a, ha, hA⟩
    obtain ⟨t, ht, htn, he⟩ := (mem_future_iff x a p).mp ha
    exact ⟨t, Finset.mem_Icc.mpr ⟨ht,htn⟩, he.symm ▸ hA⟩
  · rintro ⟨t, ht, hA⟩
    exact ⟨coordinate x p t, (mem_future_iff x _ p).mpr
      ⟨t, (Finset.mem_Icc.mp ht).1, (Finset.mem_Icc.mp ht).2, rfl⟩, hA⟩
end PathCoordinates
namespace Chain
variable [Fintype V]
variable (C : Chain V)
open PathCoordinates

theorem coordinate_split (m n : ℕ) (x : V) (p : Path V (n+m)) :
    coordinate x p m = C.endpoint x (PathSplit.split m n p).1 := by
  induction m generalizing x with
  | zero => simp [coordinate_zero, endpoint]
  | succ m ih => exact ih p.1 p.2

theorem coordinate_marginal_add [DecidableEq V] (m n : ℕ) (x y : V) :
    C.eventMass (n+m) (fun z p => coordinate z p m = y) x =
      (C.transition^m) x y := by
  classical
  have h := C.eventMass_prefix m n (fun z p => C.endpoint z p = y) x
  simp_rw [← C.coordinate_split] at h
  rw [h]
  rw [← C.endpoint_marginal m x y]
  unfold eventMass
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> rfl

theorem coordinate_marginal [DecidableEq V] (n t : ℕ) (ht : t ≤ n) (x y : V) :
    C.eventMass n (fun z p => coordinate z p t = y) x =
      (C.transition^t) x y := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [Nat.add_comm t r]
  exact C.coordinate_marginal_add t r x y

theorem actualHit_mass_le [DecidableEq V] (n : ℕ) (A : Finset V) (x : V) :
    C.eventMass n (actualHit A) x ≤ ∑ t ∈ Finset.Icc 1 n,
      ∑ a ∈ A, (C.transition^t) x a := by
  classical
  have hmono := C.eventMass_mono (actualHit A)
    (fun z p => ∃ t ∈ Finset.Icc 1 n, ∃ a ∈ A, coordinate z p t = a)
    (by
      intro z p hp
      obtain ⟨t, ht, hA⟩ := (actualHit_iff A z p).mp hp
      exact ⟨t, ht, coordinate z p t, hA, rfl⟩) x
  apply hmono.trans
  apply (C.eventMass_biUnion_le (Finset.Icc 1 n)
    (fun t z p => ∃ a ∈ A, coordinate z p t = a) x).trans
  apply Finset.sum_le_sum
  intro t ht
  have h := C.eventMass_biUnion_le (n := n) A (fun a z p => coordinate z p t = a) x
  simp_rw [C.coordinate_marginal n t (Finset.mem_Icc.mp ht).2 x] at h
  exact h
end Chain
end Erdos642.FiniteMarkov

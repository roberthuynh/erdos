import Openmath.Erdos642.Proofs.CampaignFe72210b.FiniteMarkov

namespace Erdos642.FiniteMarkov
variable {V : Type*} [Fintype V]
namespace PathSplit

def split : (m n : ℕ) → Path V (n+m) → Path V m × Path V n
  | 0, _, p => (PUnit.unit, p)
  | m+1, n, (y,p) => let r := split m n p; ((y,r.1),r.2)

end PathSplit
namespace Chain
variable (C : Chain V)

theorem split_append {m n : ℕ} (p : Path V m) (q : Path V n) :
    PathSplit.split m n (C.append p q) = (p,q) := by
  induction m with
  | zero => cases p; rfl
  | succ m ih =>
    rcases p with ⟨y,p⟩
    simp only [append, PathSplit.split, ih]

theorem append_split (m n : ℕ) (p : Path V (n+m)) :
    C.append (PathSplit.split m n p).1 (PathSplit.split m n p).2 = p := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rcases p with ⟨y,p⟩
    simp only [PathSplit.split, append, ih]
    rfl

def pathSplitEquiv (m n : ℕ) : Path V (n+m) ≃ Path V m × Path V n where
  toFun := PathSplit.split m n
  invFun := fun pq => C.append pq.1 pq.2
  left_inv := C.append_split m n
  right_inv := fun pq => C.split_append pq.1 pq.2

theorem eventMass_append_fubini (m n : ℕ) (E : V → Path V (n+m) → Prop) (x : V) :
    C.eventMass (n+m) E x = ∑ p : Path V m, C.weight x p *
      C.eventMass n (fun _ q => E x (C.append p q)) (C.endpoint x p) := by
  classical
  unfold eventMass
  rw [← (C.pathSplitEquiv m n).symm.sum_comp
    (fun r => if E x r then C.weight x r else 0), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  change (if E x (C.append p q) then C.weight x (C.append p q) else 0) = _
  rw [C.weight_append]
  split_ifs <;> simp

theorem eventMass_prefix (m n : ℕ) (E : V → Path V m → Prop) (x : V) :
    C.eventMass (n+m) (fun y r => E y (PathSplit.split m n r).1) x =
      C.eventMass m E x := by
  classical
  rw [C.eventMass_append_fubini]
  unfold eventMass
  apply Finset.sum_congr rfl
  intro p _
  simp only [C.split_append]
  by_cases h : E x p
  · simp only [h, if_true, C.total_weight, mul_one]
  · simp [h]
end Chain
end Erdos642.FiniteMarkov

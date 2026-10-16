import Openmath.Erdos642.Proofs.CampaignFe72210b.FiniteMarkov

/-! Actual path laws on closed finite subsets, obtained by summing one state at a time. -/
namespace Erdos642.FiniteMarkov

universe u v
variable {V : Type u} {W : Type v}

/-- Apply a vertex map to every future state, retaining chronological order. -/
def mapPath (f : V → W) : {n : ℕ} → Path V n → Path W n
  | 0, _ => PUnit.unit
  | _n + 1, p => (f p.1, mapPath f p.2)

namespace Chain
variable [Fintype V] (C : Chain V) (S : Set V) [DecidablePred (· ∈ S)]

/-- The literal restriction of a stochastic kernel to a subset it cannot leave. -/
noncomputable def restrict
    (hclosed : ∀ x : S, ∀ y : V, y ∉ S → C.transition x.val y = 0) : Chain S where
  transition := fun x y => C.transition x.val y.val
  nonneg := fun x y => C.nonneg x.val y.val
  row_sum := by
    intro x
    rw [← C.row_sum x.val]
    exact (Finset.sum_congr_set S (fun y => C.transition x.val y)
      (fun y : S => C.transition x.val y.val) (fun _ _ => rfl) (hclosed x)).symm

variable (D : Chain S)

/-- Entry equality alone identifies the weights of mapped subtype paths. -/
theorem mapped_weight
    (hentries : ∀ x y : S, D.transition x y = C.transition x.val y.val)
    (n : ℕ) (x : S) (p : Path S n) :
    C.weight x.val (mapPath Subtype.val p) = D.weight x p := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change C.transition x.val p.1.val * C.weight p.1.val (mapPath Subtype.val p.2) =
      D.transition x p.1 * D.weight p.1 p.2
    rw [hentries, ih]

/-- The full actual path expectation equals the expectation on the closed subtype. -/
theorem restriction_expectation
    (hentries : ∀ x y : S, D.transition x y = C.transition x.val y.val)
    (hclosed : ∀ x : S, ∀ y : V, y ∉ S → C.transition x.val y = 0)
    (n : ℕ) (x : S) (F : Path V n → ℝ) :
    (∑ p : Path V n, C.weight x.val p * F p) =
      ∑ q : Path S n, D.weight x q * F (mapPath Subtype.val q) := by
  induction n generalizing x with
  | zero =>
    rw [Fintype.sum_unique, Fintype.sum_unique]
    rfl
  | succ n ih =>
    change (∑ p : V × Path V n,
      (C.transition x.val p.1 * C.weight p.1 p.2) * F p) =
      ∑ q : S × Path S n,
        (D.transition x q.1 * D.weight q.1 q.2) *
          F (q.1.val, mapPath Subtype.val q.2)
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    calc
      _ = ∑ y : S, ∑ p : Path V n,
          (C.transition x.val y.val * C.weight y.val p) * F (y.val, p) := by
        apply Finset.sum_congr_set S
        · intro y hy
          rfl
        · intro y hy
          simp [hclosed x y hy]
      _ = ∑ y : S, ∑ q : Path S n,
          (D.transition x y * D.weight y q) * F (y.val, mapPath Subtype.val q) := by
        apply Finset.sum_congr rfl
        intro y _
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum, ← Finset.mul_sum, ih y (fun p => F (y.val, p)), hentries]

/-- Restriction preserves every event of the actual full-vertex path. -/
theorem restriction_eventMass
    (hentries : ∀ x y : S, D.transition x y = C.transition x.val y.val)
    (hclosed : ∀ x : S, ∀ y : V, y ∉ S → C.transition x.val y = 0)
    (n : ℕ) (E : V → Path V n → Prop) (x : S) :
    C.eventMass n E x.val =
      D.eventMass n (fun y q => E y.val (mapPath Subtype.val q)) x := by
  classical
  have h := C.restriction_expectation S D hentries hclosed n x
    (fun p => if E x.val p then 1 else 0)
  simpa only [eventMass, mul_ite, mul_one, mul_zero] using h

end Chain
end Erdos642.FiniteMarkov

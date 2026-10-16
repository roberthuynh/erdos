import Openmath.Erdos642.Proofs.CampaignFe72210b.PathSplit

/-! Genuine finite path windows and integration of events selected from completed history. -/
namespace Erdos642.FiniteMarkov.Chain
universe u
variable {V : Type u} [Fintype V]
variable (C : Erdos642.FiniteMarkov.Chain V)

/-- The actual n-transition window after a-prefix and before r-suffix transitions. -/
def windowEvent (a n r : ℕ) (E : V → Path V n → Prop)
    (x : V) (p : Path V ((r + n) + a)) : Prop :=
  let pq := PathSplit.split a (r + n) p
  E (C.endpoint x pq.1) (PathSplit.split n r pq.2).1

/-- Exact window law, with actual prefix endpoint as the initial window state. -/
theorem window_eventMass (a n r : ℕ) (E : V → Path V n → Prop) (x : V) :
    C.eventMass ((r + n) + a) (C.windowEvent a n r E) x =
      ∑ p : Path V a, C.weight x p * C.eventMass n E (C.endpoint x p) := by
  classical
  rw [C.eventMass_append_fubini]
  apply Finset.sum_congr rfl
  intro p _
  simp only [windowEvent, C.split_append]
  rw [C.eventMass_prefix]
  rfl

/-- Any uniform starting-state event bound survives actual prefix/suffix integration. -/
theorem window_eventMass_le (a n r : ℕ) (E : V → Path V n → Prop)
    (epsilon : ℝ) (hbound : ∀ y : V, C.eventMass n E y ≤ epsilon) (x : V) :
    C.eventMass ((r + n) + a) (C.windowEvent a n r E) x ≤ epsilon := by
  rw [C.window_eventMass]
  calc
    _ ≤ ∑ p : Path V a, C.weight x p * epsilon :=
      Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hbound _) (C.weight_nonneg x p)
    _ = epsilon := by rw [← Finset.sum_mul, C.total_weight, one_mul]

/-- The future segment after an actual prefix, with no suffix-index transport. -/
def futureEvent (a n : ℕ) (E : V → Path V n → Prop)
    (x : V) (p : Path V (n + a)) : Prop :=
  let pq := PathSplit.split a n p
  E (C.endpoint x pq.1) pq.2

theorem future_eventMass (a n : ℕ) (E : V → Path V n → Prop) (x : V) :
    C.eventMass (n + a) (C.futureEvent a n E) x =
      ∑ p : Path V a, C.weight x p * C.eventMass n E (C.endpoint x p) := by
  rw [C.eventMass_append_fubini]
  apply Finset.sum_congr rfl
  intro p _
  simp only [futureEvent, C.split_append]
  rfl

theorem future_eventMass_le (a n : ℕ) (E : V → Path V n → Prop)
    (epsilon : ℝ) (hbound : ∀ y : V, C.eventMass n E y ≤ epsilon) (x : V) :
    C.eventMass (n + a) (C.futureEvent a n E) x ≤ epsilon := by
  rw [C.future_eventMass]
  calc
    _ ≤ ∑ p : Path V a, C.weight x p * epsilon :=
      Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hbound _) (C.weight_nonneg x p)
    _ = epsilon := by rw [← Finset.sum_mul, C.total_weight, one_mul]

/-- A good completed prefix and a future bad event, after a fixed gap. -/
def historyWindowEvent (a g n : ℕ) (A : Path V a → Prop)
    (B : Path V a → V → Path V n → Prop)
    (x : V) (p : Path V ((n + g) + a)) : Prop :=
  let pq := PathSplit.split a (n + g) p
  let qr := PathSplit.split g n pq.2
  A pq.1 ∧ B pq.1 (C.endpoint (C.endpoint x pq.1) qr.1) qr.2

/-- Exact genuine Fubini for history-selected events and a fixed intervening gap. -/
theorem history_window_eventMass (a g n : ℕ) (A : Path V a → Prop) [DecidablePred A]
    (B : Path V a → V → Path V n → Prop) (x : V) :
    C.eventMass ((n + g) + a) (C.historyWindowEvent a g n A B) x =
      ∑ p : Path V a, C.weight x p *
        (if A p then C.eventMass (n + g) (C.futureEvent g n (B p)) (C.endpoint x p) else 0) := by
  classical
  rw [C.eventMass_append_fubini]
  apply Finset.sum_congr rfl
  intro p _
  simp only [historyWindowEvent, C.split_append]
  by_cases hp : A p
  · simp only [hp, true_and, if_true]
    rfl
  · simp only [hp, false_and, if_false]
    simp [eventMass]

/-- Uniform future bounds integrate over a good history and every actual gap state. -/
theorem history_window_eventMass_le (a g n : ℕ) (A : Path V a → Prop)
    (B : Path V a → V → Path V n → Prop) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hbound : ∀ p : Path V a, A p → ∀ y : V, C.eventMass n (B p) y ≤ epsilon)
    (x : V) :
    C.eventMass ((n + g) + a) (C.historyWindowEvent a g n A B) x ≤ epsilon := by
  classical
  rw [C.history_window_eventMass]
  calc
    _ ≤ ∑ p : Path V a, C.weight x p * epsilon := by
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_left _ (C.weight_nonneg x p)
      by_cases hp : A p
      · simp only [hp, if_true]
        exact C.future_eventMass_le g n (B p) epsilon (hbound p hp) (C.endpoint x p)
      · simpa only [hp, if_false] using hepsilon
    _ = epsilon := by rw [← Finset.sum_mul, C.total_weight, one_mul]

end Erdos642.FiniteMarkov.Chain

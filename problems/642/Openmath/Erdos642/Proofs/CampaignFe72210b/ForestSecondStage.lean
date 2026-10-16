import Openmath.Erdos642.Proofs.CampaignFe72210b.ForestOccupationAlgebra
import Openmath.Erdos642.Proofs.CampaignFe72210b.PathIntervals
import Openmath.Erdos642.Proofs.CampaignFe72210b.PathEvents

/-! Actual chronological second-stage occupation and weighted-count containment. -/
namespace Erdos642.CampaignFe72210b.ForestBundle
open Erdos642.FiniteMarkov Erdos642.OccupationTail
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {A B : Finset V} {q m b : ℕ}
variable (F : Erdos642.CampaignFe72210b.ForestBundle G A B q m b)

/-- Uniform fixed-set tails integrate after a successful completed first history. -/
theorem second_stage_eventMass_le (C : Chain V) (a g t : ℕ)
    (leafcut N delta : ℝ) (u : ℕ) (success : Path V a → Prop) (x : V)
    (hdelta : 0 ≤ delta)
    (hcard : ∀ p, success p → u ≤ (F.goodRootSet leafcut x p).card)
    (hfixed : ∀ U : Finset V, U ⊆ A → u ≤ U.card → ∀ y : V,
      C.eventMass (t - 1) (fun z r => occupation U z r <
        (t : ℝ) * (U.card : ℝ) / (300 * N)) y ≤ delta) :
    C.eventMass (((t - 1) + g) + a)
      (C.historyWindowEvent a g (t - 1) success (fun p z r =>
        occupation (F.goodRootSet leafcut x p) z r <
          (t : ℝ) * ((F.goodRootSet leafcut x p).card : ℝ) / (300 * N))) x ≤ delta := by
  apply C.history_window_eventMass_le a g (t - 1) success _ delta hdelta
  intro p hp y
  exact hfixed _ (F.goodRootSet_subset leafcut x p) (hcard p hp) y

/-- Deterministic low weighted count forces first failure or second failure. -/
theorem low_weightedCount_imp (leafcut N : ℝ) (hleafcut : 0 ≤ leafcut)
    (hN : 0 < N) (u t : ℕ) {a : ℕ} (success : Path V a → Prop)
    (x : V) (p : Path V a) (y : V) (r : Path V (t - 1))
    (hcard : success p → u ≤ (F.goodRootSet leafcut x p).card)
    (hlow : F.occupationWeightedCount x p y r <
      leafcut * ((t : ℝ) * (u : ℝ) / (300 * N))) :
    ¬ success p ∨ (success p ∧
      occupation (F.goodRootSet leafcut x p) y r <
        (t : ℝ) * ((F.goodRootSet leafcut x p).card : ℝ) / (300 * N)) := by
  classical
  by_cases hp : success p
  · right
    refine ⟨hp, ?_⟩
    by_contra hn
    have hocc := le_of_not_gt hn
    have hc : (u : ℝ) ≤ ((F.goodRootSet leafcut x p).card : ℝ) := by
      exact_mod_cast hcard hp
    have hthreshold : (t : ℝ) * (u : ℝ) / (300 * N) ≤
        (t : ℝ) * ((F.goodRootSet leafcut x p).card : ℝ) / (300 * N) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg t))
        (by positivity)
    have hlower := F.occupationWeightedCount_good_lower leafcut x p y r
    have hh := mul_le_mul_of_nonneg_left (hthreshold.trans hocc) hleafcut
    linarith
  · exact Or.inl hp

/-- The literal weighted count on two windows separated by a fixed gap. -/
noncomputable def windowWeightedCount (C : Chain V) (a g n : ℕ)
    (x : V) (w : Path V ((n + g) + a)) : ℝ :=
  let pq := PathSplit.split a (n + g) w
  let zr := PathSplit.split g n pq.2
  F.occupationWeightedCount x pq.1 (C.endpoint (C.endpoint x pq.1) zr.1) zr.2

/-- Actual low-window-count mass is bounded by the two unconditional failure inputs. -/
theorem low_windowWeightedCount_eventMass_le (C : Chain V) (a g t : ℕ)
    (leafcut N delta epsilon : ℝ) (hleafcut : 0 ≤ leafcut) (hN : 0 < N)
    (u : ℕ) (success : Path V a → Prop) (x : V) (hdelta : 0 ≤ delta)
    (hcard : ∀ p, success p → u ≤ (F.goodRootSet leafcut x p).card)
    (hfirst : C.eventMass a (fun _ p => ¬ success p) x ≤ epsilon)
    (hfixed : ∀ U : Finset V, U ⊆ A → u ≤ U.card → ∀ y : V,
      C.eventMass (t - 1) (fun z r => occupation U z r <
        (t : ℝ) * (U.card : ℝ) / (300 * N)) y ≤ delta) :
    C.eventMass (((t - 1) + g) + a)
      (fun _ w => F.windowWeightedCount C a g (t - 1) x w <
        leafcut * ((t : ℝ) * (u : ℝ) / (300 * N))) x ≤ epsilon + delta := by
  let E : V → Path V (((t - 1) + g) + a) → Prop :=
    fun _ w => ¬ success (PathSplit.split a ((t - 1) + g) w).1
  let H := C.historyWindowEvent a g (t - 1) success (fun p z r =>
    occupation (F.goodRootSet leafcut x p) z r <
      (t : ℝ) * ((F.goodRootSet leafcut x p).card : ℝ) / (300 * N))
  have hcontain : ∀ y w,
      F.windowWeightedCount C a g (t - 1) x w <
        leafcut * ((t : ℝ) * (u : ℝ) / (300 * N)) → E y w ∨ H x w := by
    intro y w hw
    exact F.low_weightedCount_imp leafcut N hleafcut hN u t success x _ _ _
      (hcard _) hw
  have hm := C.eventMass_mono
    (fun _ w => F.windowWeightedCount C a g (t - 1) x w <
      leafcut * ((t : ℝ) * (u : ℝ) / (300 * N)))
    (fun y w => E y w ∨ H x w) hcontain x
  have hu := C.eventMass_union_le E (fun _ w => H x w) x
  have hE : C.eventMass (((t - 1) + g) + a) E x ≤ epsilon := by
    exact (C.eventMass_prefix a ((t - 1) + g) (fun _ p => ¬ success p) x).le.trans hfirst
  have hH : C.eventMass (((t - 1) + g) + a) (fun _ w => H x w) x ≤ delta := by
    have hh := F.second_stage_eventMass_le C a g t leafcut N delta u success x hdelta hcard hfixed
    exact hh
  exact hm.trans (hu.trans (add_le_add hE hH))

end Erdos642.CampaignFe72210b.ForestBundle

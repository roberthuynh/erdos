import Openmath.IncidenceRepair.PlaneCost

noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair.Plane

/-- Exact finite cardinality is bounded by any nonnegative majorant that is at
least one at each marked element. No probabilistic approximation is used. -/
theorem card_filter_le_sum_majorant {A : Type*} (s : Finset A)
    (p : A → Prop) [DecidablePred p] (f : A → ℝ)
    (hn : ∀ x ∈ s, 0 ≤ f x) (hp : ∀ x ∈ s, p x → 1 ≤ f x) :
    ((s.filter p).card : ℝ) ≤ ∑ x ∈ s, f x := by
  calc
    ((s.filter p).card : ℝ) = ∑ x ∈ s.filter p, (1 : ℝ) := by simp
    _ ≤ ∑ x ∈ s.filter p, f x := Finset.sum_le_sum (fun x hx =>
      hp x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2)
    _ ≤ ∑ x ∈ s, f x := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset p s) (fun x hx _ => hn x hx)

/-- A union of marked families is charged to the sum of their majorants. -/
theorem card_filter_exists_le_sum_majorants {A I : Type*} [Fintype I]
    (s : Finset A) (p : I → A → Prop) [DecidablePred (fun x => ∃ i, p i x)]
    (f : I → A → ℝ)
    (hn : ∀ i x, x ∈ s → 0 ≤ f i x)
    (hp : ∀ i x, x ∈ s → p i x → 1 ≤ f i x) :
    ((s.filter (fun x => ∃ i, p i x)).card : ℝ) ≤ ∑ i, ∑ x ∈ s, f i x := by
  rw [Finset.sum_comm]
  apply card_filter_le_sum_majorant
  · intro x hx
    exact Finset.sum_nonneg (fun i _ => hn i x hx)
  · intro x hx hex
    obtain ⟨i, hi⟩ := hex
    exact (hp i x hx hi).trans
      (Finset.single_le_sum (fun j _ => hn j x hx) (Finset.mem_univ i))

variable {K : Type*} [Field K] [Fintype K]

theorem avg1_add (f g : K → ℝ) : avg1 (fun x => f x + g x) = avg1 f + avg1 g := by
  simp [avg1, Finset.sum_add_distrib, add_div]

theorem avg2_add (f g : K → K → ℝ) :
    avg2 (fun x y => f x y + g x y) = avg2 f + avg2 g := by
  simp [avg2, Finset.sum_add_distrib, add_div]

theorem sum_le_of_avg1_le {f : K → ℝ} {e : ℝ} (h : avg1 f ≤ e) :
    ∑ x, f x ≤ e * Fintype.card K := by
  exact (div_le_iff₀ (by exact_mod_cast Fintype.card_pos : (0:ℝ) < Fintype.card K)).1 h

theorem sum_le_of_avg2_le {f : K → K → ℝ} {e : ℝ} (h : avg2 f ≤ e) :
    ∑ x, ∑ y, f x y ≤ e * (Fintype.card K : ℝ)^2 := by
  have hc : (0:ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  exact (div_le_iff₀ (by positivity)).1 h

theorem sum_le_of_avg3_le {f : K → K → K → ℝ} {e : ℝ} (h : avg3 f ≤ e) :
    ∑ x, ∑ y, ∑ z, f x y z ≤ e * (Fintype.card K : ℝ)^3 := by
  have hc : (0:ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  exact (div_le_iff₀ (by positivity)).1 h

theorem close_budget {b : Point K 2 → Hyperplane K 2 → ℝ}
    (hb : ∀ p H, 0 ≤ b p H) :
    avg1 (fun t => b V (vertical t) + b U (horizontal t) +
      b (affine t t) (vertical t) + b (affine t t) (horizontal t) +
      b (affine t t) (slope 1 0)) ≤ cost b := by
  have h := subfamily_le_cost hb ({0, 1, 4, 5, 6} : Finset (Fin 24))
  simpa [costTerm, Finset.sum_insert, Finset.sum_singleton, avg1_add, add_assoc] using h

theorem badanchors_budget {b : Point K 2 → Hyperplane K 2 → ℝ}
    (hb : ∀ p H, 0 ≤ b p H) :
    avg1 (fun t => b V (vertical t) + b U (horizontal t)) ≤ cost b := by
  have h := subfamily_le_cost hb ({0, 1} : Finset (Fin 24))
  simpa [costTerm, Finset.sum_insert, Finset.sum_singleton, avg1_add] using h

theorem pencil_budget {b : Point K 2 → Hyperplane K 2 → ℝ}
    (hb : ∀ p H, 0 ≤ b p H) :
    avg2 (fun x y => b (affine x y) (vertical x) + b (affine x y) (horizontal y)) +
    avg1 (fun a => @ite ℝ (a ≠ 0) (Classical.propDecidable _) (b (affine 0 0) (slope a 0)) 0) +
    avg2 (fun a t => @ite ℝ (a ≠ 0) (Classical.propDecidable _) (b (affine t (a*t)) (slope a 0)) 0)
      ≤ cost b := by
  classical
  have h := subfamily_le_cost hb ({2, 3, 7, 8} : Finset (Fin 24))
  have h7 : costTerm b 7 = avg1 (fun a => @ite ℝ (a ≠ 0)
      (Classical.propDecidable _) (b (affine 0 0) (slope a 0)) 0) := by
    apply congrArg avg1
    funext a
    split_ifs <;> rfl
  have h8 : costTerm b 8 = avg2 (fun a t => @ite ℝ (a ≠ 0)
      (Classical.propDecidable _) (b (affine t (a*t)) (slope a 0)) 0) := by
    apply congrArg avg2
    funext a t
    split_ifs <;> rfl
  have hh : costTerm b 2 + costTerm b 3 + costTerm b 7 + costTerm b 8 ≤ cost b := by
    simpa [add_assoc] using h
  rw [h7, h8] at hh
  change avg2 (fun x y => b (affine x y) (vertical x)) +
    avg2 (fun x y => b (affine x y) (horizontal y)) + _ + _ ≤ cost b at hh
  rwa [← avg2_add] at hh

theorem close_raw_budget {b : Point K 2 → Hyperplane K 2 → ℝ}
    (hb : ∀ p H, 0 ≤ b p H) :
    (∑ t, (b V (vertical t) + b U (horizontal t) +
      b (affine t t) (vertical t) + b (affine t t) (horizontal t) +
      b (affine t t) (slope 1 0))) ≤ cost b * Fintype.card K :=
  sum_le_of_avg1_le (close_budget hb)

theorem badanchors_raw_budget {b : Point K 2 → Hyperplane K 2 → ℝ}
    (hb : ∀ p H, 0 ≤ b p H) :
    (∑ t, (b V (vertical t) + b U (horizontal t))) ≤ cost b * Fintype.card K :=
  sum_le_of_avg1_le (badanchors_budget hb)

theorem pencil_raw_budget {b : Point K 2 → Hyperplane K 2 → ℝ}
    (hb : ∀ p H, 0 ≤ b p H) :
    (∑ x, ∑ y, (b (affine x y) (vertical x) + b (affine x y) (horizontal y))) +
    (Fintype.card K : ℝ) * (∑ a, @ite ℝ (a ≠ 0) (Classical.propDecidable _) (b (affine 0 0) (slope a 0)) 0) +
    (∑ a, ∑ t, @ite ℝ (a ≠ 0) (Classical.propDecidable _) (b (affine t (a*t)) (slope a 0)) 0)
      ≤ cost b * (Fintype.card K : ℝ)^2 := by
  have h := pencil_budget hb
  have hq : (Fintype.card K : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hm := mul_le_mul_of_nonneg_right h (sq_nonneg (Fintype.card K : ℝ))
  unfold avg1 avg2 at hm
  convert hm using 1 <;> (try field_simp) <;> (try ring)
  all_goals rfl

end Erdos85.IncidenceRepair.Plane

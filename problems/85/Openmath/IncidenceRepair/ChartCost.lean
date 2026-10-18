import Openmath.IncidenceRepair.PlaneCost
import Openmath.IncidenceRepair.EquivariantAverage

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1200000
namespace Erdos85.IncidenceRepair.Plane

variable {K : Type*} [Field K] [Fintype K]

private theorem avg1_const (c : ℝ) : avg1 (fun _ : K => c) = c := by
  have h : (Fintype.card K : ℝ) ≠ 0 := by positivity
  simp [avg1, h]

private theorem avg2_const (c : ℝ) : avg2 (fun _ _ : K => c) = c := by
  have h : (Fintype.card K : ℝ) ≠ 0 := by positivity
  simp only [avg2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  <;> ring

private theorem avg3_const (c : ℝ) : avg3 (fun _ _ _ : K => c) = c := by
  have h : (Fintype.card K : ℝ) ≠ 0 := by positivity
  simp only [avg3, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  <;> ring

/-- Every one of the concrete twenty-four table distributions has mass at most one.
The eight restricted nonzero-slope terms retain the original q or q² denominator. -/
theorem costTerm_const_le {c : ℝ} (hc : 0 ≤ c) (i : Fin 24) :
    costTerm (fun (_ : Point K 2) (_ : Hyperplane K 2) => c) i ≤ c := by
  classical
  fin_cases i <;> dsimp only [costTerm]
  all_goals first
    | exact le_of_eq (avg1_const c)
    | exact le_of_eq (avg2_const c)
    | exact le_of_eq (avg3_const c)
    | apply (avg1_mono (g := fun _ => c) ?_).trans (le_of_eq (avg1_const c))
      intro x; split_ifs <;> simp_all
    | apply (avg2_mono (g := fun _ _ => c) ?_).trans (le_of_eq (avg2_const c))
      intro x y; split_ifs <;> simp_all

theorem cost_const_le {c : ℝ} (hc : 0 ≤ c) :
    cost (fun (_ : Point K 2) (_ : Hyperplane K 2) => c) ≤ 24 * c := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => costTerm_const_le (K := K) hc i)
  simpa [cost] using h

private theorem avg1_add' (f g : K → ℝ) :
    avg1 (fun x => f x + g x) = avg1 f + avg1 g := by
  simp [avg1, Finset.sum_add_distrib, add_div]
private theorem avg2_add' (f g : K → K → ℝ) :
    avg2 (fun x y => f x y + g x y) = avg2 f + avg2 g := by
  simp [avg2, Finset.sum_add_distrib, add_div]
private theorem avg3_add' (f g : K → K → K → ℝ) :
    avg3 (fun x y z => f x y z + g x y z) = avg3 f + avg3 g := by
  simp [avg3, Finset.sum_add_distrib, add_div]

theorem costTerm_add (b c : Point K 2 → Hyperplane K 2 → ℝ) (i : Fin 24) :
    costTerm (fun p H => b p H + c p H) i = costTerm b i + costTerm c i := by
  classical
  fin_cases i <;> dsimp only [costTerm]
  all_goals simp_rw [show ∀ (p : Prop) [Decidable p] (a b : ℝ),
    (if p then a + b else 0) = (if p then a else 0) + (if p then b else 0) by
      intros; split_ifs <;> simp]
  all_goals first | exact avg1_add' _ _ | exact avg2_add' _ _ | exact avg3_add' _ _

private theorem avg1_mul (r : ℝ) (f : K → ℝ) :
    avg1 (fun x => r * f x) = r * avg1 f := by
  simp only [avg1, ← Finset.mul_sum, mul_div_assoc]
private theorem avg2_mul (r : ℝ) (f : K → K → ℝ) :
    avg2 (fun x y => r * f x y) = r * avg2 f := by
  simp only [avg2, ← Finset.mul_sum, mul_div_assoc]
private theorem avg3_mul (r : ℝ) (f : K → K → K → ℝ) :
    avg3 (fun x y z => r * f x y z) = r * avg3 f := by
  simp only [avg3, ← Finset.mul_sum, mul_div_assoc]

theorem costTerm_mul (r : ℝ) (b : Point K 2 → Hyperplane K 2 → ℝ) (i : Fin 24) :
    costTerm (fun p H => r * b p H) i = r * costTerm b i := by
  classical
  fin_cases i <;> dsimp only [costTerm]
  all_goals simp_rw [show ∀ (p : Prop) [Decidable p] (a : ℝ),
    (if p then r * a else 0) = r * (if p then a else 0) by
      intros; split_ifs <;> simp]
  all_goals first | exact avg1_mul _ _ | exact avg2_mul _ _ | exact avg3_mul _ _

theorem cost_add (b c : Point K 2 → Hyperplane K 2 → ℝ) :
    cost (fun p H => b p H + c p H) = cost b + cost c := by
  simp [cost, costTerm_add, Finset.sum_add_distrib]

theorem cost_mul (r : ℝ) (b : Point K 2 → Hyperplane K 2 → ℝ) :
    cost (fun p H => r * b p H) = r * cost b := by
  simp [cost, costTerm_mul, Finset.mul_sum]

theorem cost_zero : cost (fun (_ : Point K 2) (_ : Hyperplane K 2) => (0 : ℝ)) = 0 := by
  exact cost_zero_of_zero_on_flags (fun _ _ _ => rfl)

theorem cost_sum {F : Type*} (s : Finset F)
    (b : F → Point K 2 → Hyperplane K 2 → ℝ) :
    cost (fun p H => ∑ f ∈ s, b f p H) = ∑ f ∈ s, cost (b f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cost_zero (K := K)
  | @insert f s hf ih => simp only [Finset.sum_insert hf, cost_add, ih]

/-- The published cost commutes with averaging over all source frames. -/
theorem average_cost {F : Type*} [Fintype F]
    (b : F → Point K 2 → Hyperplane K 2 → ℝ) :
    (∑ f, cost (b f)) / (Fintype.card F : ℝ) =
      cost (fun p H => (∑ f, b f p H) / (Fintype.card F : ℝ)) := by
  simp_rw [div_eq_mul_inv, mul_comm _ ((Fintype.card F : ℝ)⁻¹)]
  rw [cost_mul, cost_sum]

end Erdos85.IncidenceRepair.Plane

namespace Erdos85.IncidenceRepair

variable {K G F I : Type*} [Field K] [Fintype K] [Group G]
  [Fintype F] [Fintype I] [DecidableEq I] [Nonempty F] [Nonempty I]
  [MulAction G F] [MulAction G I] [MulAction.IsPretransitive G I]

/-- Actual incident plane flags, before any survival or certificate conditioning. -/
abbrev PlaneFlag (K : Type*) [Field K] :=
  { ph : Point K 2 × Hyperplane K 2 // Incident ph.1 ph.2 }

/-- Each induced plane flag is majorized by m original flags, with multiplicity.
Nonincident plane pairs are assigned zero because no table entry uses them. -/
def rawChartMajorant {m : ℕ} (slot : PlaneFlag K → Fin m → F → I)
    (error : I → ℝ) (f : F) (p : Point K 2) (H : Hyperplane K 2) : ℝ := by
  classical
  exact if h : Incident p H then ∑ s, error (slot ⟨(p,H), h⟩ s f) else 0

theorem rawChartMajorant_nonneg {m : ℕ} (slot : PlaneFlag K → Fin m → F → I)
    (error : I → ℝ) (herror : ∀ i, 0 ≤ error i) (f : F) (p : Point K 2)
    (H : Hyperplane K 2) : 0 ≤ rawChartMajorant slot error f p H := by
  classical
  unfold rawChartMajorant
  split_ifs
  · exact Finset.sum_nonneg (fun s _ => herror _)
  · exact le_refl 0

/-- Unconditioned original-slot averaging pays every term in the majorant. -/
theorem average_rawChartMajorant_le {m : ℕ}
    (slot : PlaneFlag K → Fin m → F → I)
    (hequiv : ∀ (ph : PlaneFlag K) (s : Fin m) (g : G) (f : F),
      slot ph s (g • f) = g • slot ph s f)
    (error : I → ℝ) (herror : ∀ i, 0 ≤ error i)
    (p : Point K 2) (H : Hyperplane K 2) :
    (∑ f, rawChartMajorant slot error f p H) / (Fintype.card F : ℝ) ≤
      (m : ℝ) * ((∑ i, error i) / (Fintype.card I : ℝ)) := by
  classical
  by_cases hp : Incident p H
  · have h := average_weighted_equivariant_slots (slot ⟨(p,H),hp⟩)
      (hequiv ⟨(p,H),hp⟩) (fun _ => (1 : ℝ)) error
    simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at h
    simpa [rawChartMajorant, hp] using le_of_eq h
  · simp only [rawChartMajorant, dif_neg hp, Finset.sum_const_zero, zero_div]
    exact mul_nonneg (by positivity)
      (div_nonneg (Finset.sum_nonneg (fun i _ => herror i)) (by positivity))

/-- The actual twenty-four normalized table sums cost at most 24m times the
original error density. No table average is assumed as a hypothesis. -/
theorem average_chart_cost_le {m : ℕ}
    (slot : PlaneFlag K → Fin m → F → I)
    (hequiv : ∀ (ph : PlaneFlag K) (s : Fin m) (g : G) (f : F),
      slot ph s (g • f) = g • slot ph s f)
    (error : I → ℝ) (herror : ∀ i, 0 ≤ error i) :
    (∑ f, Plane.cost (rawChartMajorant slot error f)) / (Fintype.card F : ℝ) ≤
      24 * (m : ℝ) * ((∑ i, error i) / (Fintype.card I : ℝ)) := by
  rw [Plane.average_cost]
  have hm := Plane.cost_mono (average_rawChartMajorant_le slot hequiv error herror)
  have hn : 0 ≤ (m : ℝ) * ((∑ i, error i) / (Fintype.card I : ℝ)) :=
    mul_nonneg (by positivity)
      (div_nonneg (Finset.sum_nonneg (fun i _ => herror i)) (by positivity))
  exact hm.trans (by simpa [mul_assoc] using Plane.cost_const_le (K := K) hn)

/-- Coordinate reconstruction samples q^n points and n original flags per point. -/
def rawGamma {n : ℕ} (slot : Fin n → (Fin n → K) → F → I)
    (error : I → ℝ) (f : F) : ℝ :=
  (∑ x, ∑ i, error (slot i x f)) / (Fintype.card K : ℝ)^n

theorem rawGamma_nonneg {n : ℕ} (slot : Fin n → (Fin n → K) → F → I)
    (error : I → ℝ) (herror : ∀ i, 0 ≤ error i) (f : F) :
    0 ≤ rawGamma slot error f := by
  apply div_nonneg
  · exact Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun i _ => herror _))
  · positivity

theorem average_gamma {n : ℕ} (slot : Fin n → (Fin n → K) → F → I)
    (hequiv : ∀ (i : Fin n) (x : Fin n → K) (g : G) (f : F),
      slot i x (g • f) = g • slot i x f) (error : I → ℝ) :
    (∑ f, rawGamma slot error f) / (Fintype.card F : ℝ) =
      (n : ℝ) * ((∑ i, error i) / (Fintype.card I : ℝ)) := by
  have hq : (Fintype.card K : ℝ) ≠ 0 := by positivity
  calc
    _ = ∑ x : Fin n → K, ∑ i : Fin n,
        ((∑ f, error (slot i x f)) / (Fintype.card F : ℝ)) /
          (Fintype.card K : ℝ)^n := by
      simp only [rawGamma, Finset.sum_div]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro f _
      ring
    _ = (n : ℝ) * ((∑ i, error i) / (Fintype.card I : ℝ)) := by
      simp_rw [average_equivariant_slot (slot _ _) (hequiv _ _) error]
      simp [Fintype.card_fun, Fintype.card_fin, hq, mul_div_assoc, mul_assoc]
      field_simp
      <;> ring

/-- The raw chart costs and coordinate cost are formed on every source frame. -/
def rawTotalCost {n : ℕ}
    (chartSlot : Fin (n-1) → PlaneFlag K → Fin (2*n-3) → F → I)
    (gammaSlot : Fin n → (Fin n → K) → F → I) (error : I → ℝ) (f : F) : ℝ :=
  rawGamma gammaSlot error f +
    ∑ j, Plane.cost (rawChartMajorant (chartSlot j) error f)

theorem rawTotalCost_nonneg {n : ℕ}
    (chartSlot : Fin (n-1) → PlaneFlag K → Fin (2*n-3) → F → I)
    (gammaSlot : Fin n → (Fin n → K) → F → I)
    (error : I → ℝ) (herror : ∀ i, 0 ≤ error i) (f : F) :
    0 ≤ rawTotalCost chartSlot gammaSlot error f := by
  apply add_nonneg (rawGamma_nonneg gammaSlot error herror f)
  exact Finset.sum_nonneg (fun j _ => Plane.cost_nonneg
    (rawChartMajorant_nonneg (chartSlot j) error herror f))

theorem average_total_cost_le {n : ℕ} (hn : 2 ≤ n)
    (chartSlot : Fin (n-1) → PlaneFlag K → Fin (2*n-3) → F → I)
    (gammaSlot : Fin n → (Fin n → K) → F → I)
    (hchart : ∀ j (ph : PlaneFlag K) s (g : G) f,
      chartSlot j ph s (g • f) = g • chartSlot j ph s f)
    (hgamma : ∀ i x (g : G) f, gammaSlot i x (g • f) = g • gammaSlot i x f)
    (error : I → ℝ) (herror : ∀ i, 0 ≤ error i) :
    (∑ f, rawTotalCost chartSlot gammaSlot error f) / (Fintype.card F : ℝ) ≤
      48 * (n : ℝ)^2 * ((∑ i, error i) / (Fintype.card I : ℝ)) := by
  let delta : ℝ := (∑ i, error i) / (Fintype.card I : ℝ)
  have hd : 0 ≤ delta := div_nonneg
    (Finset.sum_nonneg (fun i _ => herror i)) (by positivity)
  have hc := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    average_chart_cost_le (chartSlot j) (hchart j) error herror)
  have hg := average_gamma gammaSlot hgamma error
  have heq : (∑ f, rawTotalCost chartSlot gammaSlot error f) / (Fintype.card F : ℝ) =
      (n : ℝ) * delta +
        ∑ j, (∑ f, Plane.cost (rawChartMajorant (chartSlot j) error f)) /
          (Fintype.card F : ℝ) := by
    simp only [rawTotalCost, Finset.sum_add_distrib, add_div]
    rw [hg, Finset.sum_comm, Finset.sum_div]
    simp only [delta, Finset.sum_div, mul_div_assoc]
  rw [heq]
  have hcoeff : (n : ℝ) + (n-1 : ℕ) * (24 * (2*n-3 : ℕ)) ≤ 48 * (n : ℝ)^2 := by
    have h1 : 1 ≤ n := by omega
    have h3 : 3 ≤ 2*n := by omega
    push_cast [Nat.cast_sub h1, Nat.cast_sub h3]
    have hn0 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hbound := mul_le_mul_of_nonneg_right hcoeff hd
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hc
  dsimp only [delta] at *
  nlinarith

/-- Protected-frame certificate slots: base hyperplanes, then five n-slot
constructions for each of the n-1 coordinate planes. Repeats remain separate. -/
abbrev CertificateSlots (n : ℕ) := Fin (2*n*n+n) ⊕ (Fin (n-1) × Fin (5*n))

theorem certificate_slots_card {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card (CertificateSlots n) = 7*n*n - 4*n := by
  have h : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have heq : Fintype.card (CertificateSlots n) + 4*n = 7*n*n := by
    simp only [CertificateSlots, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    nlinarith
  omega

theorem certificate_slots_card_le {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card (CertificateSlots n) ≤ 7*n*n := by
  simp only [CertificateSlots, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  have h : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  nlinarith

theorem certificate_failure_bound {n : ℕ} (hn : 2 ≤ n)
    (slot : CertificateSlots n → F → I)
    (hequiv : ∀ s (g : G) f, slot s (g • f) = g • slot s f)
    (bad : I → Prop) [DecidablePred bad] :
    ((Finset.univ.filter (fun f => ∃ s, bad (slot s f))).card : ℝ) /
        (Fintype.card F : ℝ) ≤
      7 * (n : ℝ)^2 *
        (((Finset.univ.filter bad).card : ℝ) / (Fintype.card I : ℝ)) := by
  have h := certificate_failure_fraction_le slot hequiv bad
  have hc : (Fintype.card (CertificateSlots n) : ℝ) ≤ 7 * (n : ℝ)^2 := by
    exact_mod_cast (by simpa [pow_two, mul_assoc] using certificate_slots_card_le hn)
  exact h.trans (mul_le_mul_of_nonneg_right hc (by positivity))

end Erdos85.IncidenceRepair

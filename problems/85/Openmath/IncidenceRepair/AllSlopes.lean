import Openmath.IncidenceRepair.FieldCoherence
import Mathlib.Algebra.Field.Subfield.Basic

namespace Erdos85.IncidenceRepair

variable {K L : Type*} [Field K] [Field L]

/-- The scalars on which an additive map intertwines multiplication. The normalizing
condition at one makes the intertwining scalar uniquely equal to `H a`. -/
def scalarStabilizer (H : K →+ L) (h1 : H 1 = 1) : Subfield K where
  carrier := {a | ∀ x, H (a * x) = H a * H x}
  zero_mem' := by intro x; simp
  one_mem' := by intro x; simp [h1]
  add_mem' := by
    intro a b ha hb x
    simp only [add_mul, map_add]
    rw [ha x, hb x]
  neg_mem' := by
    intro a ha x
    simp only [neg_mul, map_neg]
    rw [ha x]
  mul_mem' := by
    intro a b ha hb x
    rw [mul_assoc, ha, hb, ha, mul_assoc]
  inv_mem' := by
    intro a ha
    by_cases ha0 : a = 0
    · subst a
      intro x
      simp
    · intro x
      have he : H a * H a⁻¹ = 1 := by
        rw [← ha, mul_inv_cancel₀ ha0, h1]
      have hHa : H a ≠ 0 := by
        intro hz
        rw [hz, zero_mul] at he
        exact zero_ne_one he
      apply mul_left_cancel₀ hHa
      rw [← ha, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul,
        ← mul_assoc, he, one_mul]

@[simp]
theorem mem_scalarStabilizer (H : K →+ L) (h1 : H 1 = 1) (a : K) :
    a ∈ scalarStabilizer H h1 ↔ ∀ x, H (a * x) = H a * H x := Iff.rfl

/-- This is exactly the existential scalar condition in the written proof. -/
theorem mem_scalarStabilizer_iff_exists (H : K →+ L) (h1 : H 1 = 1) (a : K) :
    a ∈ scalarStabilizer H h1 ↔ ∃ s : L, ∀ x, H (a * x) = s * H x := by
  constructor
  · intro ha
    exact ⟨H a, ha⟩
  · rintro ⟨s, hs⟩
    have he : H a = s := by simpa [h1] using hs 1
    intro x
    simpa [he] using hs x

/-- More than half the scalars intertwining multiplication forces all scalars to do so. -/
theorem scalarStabilizer_eq_top_of_twice_card_gt [Finite K]
    (H : K →+ L) (h1 : H 1 = 1)
    (hcard : Nat.card K < 2 * Nat.card (scalarStabilizer H h1)) :
    scalarStabilizer H h1 = ⊤ := by
  have ht : (scalarStabilizer H h1).toAddSubgroup = ⊤ := by
    by_contra hn
    exact (not_lt_of_ge (twice_card_addSubgroup_le _ hn)) hcard
  ext a
  simp only [Subfield.mem_top, iff_true]
  have ha : a ∈ (scalarStabilizer H h1).toAddSubgroup := by rw [ht]; trivial
  exact ha

/-- The ring embedding is constructed from the additive map; multiplication is a conclusion. -/
def ringHomOfManySlopes [Finite K] (H : K →+ L) (h1 : H 1 = 1)
    (hcard : Nat.card K < 2 * Nat.card (scalarStabilizer H h1)) : K →+* L where
  toFun := H
  map_zero' := H.map_zero
  map_add' := H.map_add
  map_one' := h1
  map_mul' := by
    intro a b
    have ha : a ∈ scalarStabilizer H h1 := by
      rw [scalarStabilizer_eq_top_of_twice_card_gt H h1 hcard]
      trivial
    exact ha b

@[simp]
theorem ringHomOfManySlopes_apply [Finite K] (H : K →+ L) (h1 : H 1 = 1)
    (hcard : Nat.card K < 2 * Nat.card (scalarStabilizer H h1)) (a : K) :
    ringHomOfManySlopes H h1 hcard a = H a := rfl

/-- Additive pullback of a target affine line along a slope graph. -/
def linePullback (H : K →+ L) (a : K) (u v : L) : K →+ L where
  toFun x := u * H x + v * H (a * x)
  map_zero' := by simp
  map_add' := by intro x y; simp only [mul_add, map_add]; ring

/-- A non-stabilizing slope cannot map entirely into any target affine direction. -/
theorem linePullback_ne_zero (H : K →+ L) (h1 : H 1 = 1)
    (a : K) (ha : a ∉ scalarStabilizer H h1) (u v : L)
    (huv : u ≠ 0 ∨ v ≠ 0) : linePullback H a u v ≠ 0 := by
  intro hz
  have hz' (x : K) : u * H x + v * H (a * x) = 0 := by
    exact DFunLike.congr_fun hz x
  by_cases hv : v = 0
  · have hu : u ≠ 0 := huv.resolve_right (not_not_intro hv)
    have he := hz' 1
    simp [hv, h1] at he
    exact hu he
  · apply ha
    apply (mem_scalarStabilizer_iff_exists H h1 a).mpr
    refine ⟨-u / v, ?_⟩
    intro x
    have he := hz' x
    apply (mul_left_cancel₀ hv)
    field_simp
    linear_combination he

/-- For a non-stabilizing slope, at most half the parameter values lie on any
nontrivial target affine line. This counts parameter values, including repeats. -/
theorem twice_card_line_parameters_le [Finite K] (H : K →+ L) (h1 : H 1 = 1)
    (a b : K) (ha : a ∉ scalarStabilizer H h1) (u v w : L)
    (huv : u ≠ 0 ∨ v ≠ 0) :
    2 * Nat.card {x : K // u * H x + v * H (a * x + b) = w} ≤ Nat.card K := by
  have he (x : K) :
      (u * H x + v * H (a * x + b) = w) ↔
      (linePullback H a u v x = w - v * H b) := by
    simp only [map_add, mul_add, linePullback, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    constructor <;> intro h <;> linear_combination h
  rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
  exact twice_card_additive_fiber_le _ (linePullback_ne_zero H h1 a ha u v huv) _

/-- The same parameter bound also allows the projective line at infinity. -/
theorem twice_card_projective_line_parameters_le [Finite K]
    (H : K →+ L) (h1 : H 1 = 1) (a b : K)
    (ha : a ∉ scalarStabilizer H h1) (u v w : L)
    (huvw : u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) :
    2 * Nat.card {x : K // u * H x + v * H (a * x + b) = w} ≤ Nat.card K := by
  by_cases hu : u = 0
  · by_cases hv : v = 0
    · have hw : w ≠ 0 := huvw.resolve_left (not_not_intro hu) |>.resolve_left
        (not_not_intro hv)
      have : IsEmpty {x : K // u * H x + v * H (a * x + b) = w} := by
        refine ⟨fun x => hw ?_⟩
        simpa [hu, hv] using x.property.symm
      rw [Nat.card_of_isEmpty]
      exact Nat.zero_le _
    · exact twice_card_line_parameters_le H h1 a b ha u v w (Or.inr hv)
  · exact twice_card_line_parameters_le H h1 a b ha u v w (Or.inl hu)

/-- A finite counting bridge from a marked-triple bound to a majority of good slopes. -/
theorem majority_slopes_of_few_marks {A : Type*} [Fintype A] [Nonempty A]
    (good : A → Prop) (marked : A → A → A → Prop)
    [DecidablePred good] [∀ a b, DecidablePred (marked a b)]
    (row_bound : ∀ a, ¬ good a → ∀ b,
      Fintype.card A ≤ 2 * (Finset.univ.filter (marked a b)).card)
    (few : 4 * (∑ a : A, ∑ b : A, (Finset.univ.filter (marked a b)).card)
      < Fintype.card A ^ 3) :
    Fintype.card A < 2 * (Finset.univ.filter good).card := by
  classical
  let bad := Finset.univ.filter (fun a => ¬ good a)
  let M := ∑ a : A, ∑ b : A, (Finset.univ.filter (marked a b)).card
  have hrow (a : A) (ha : a ∈ bad) :
      Fintype.card A ^ 2 ≤ 2 * ∑ b : A, (Finset.univ.filter (marked a b)).card := by
    have hb := Finset.sum_le_sum (s := (Finset.univ : Finset A))
      (fun b _ => row_bound a (Finset.mem_filter.mp ha).2 b)
    simpa [Finset.mul_sum, pow_two] using hb
  have hbad : bad.card * Fintype.card A ^ 2 ≤ 2 * M := by
    calc
      bad.card * Fintype.card A ^ 2 = ∑ _a ∈ bad, Fintype.card A ^ 2 := by simp
      _ ≤ ∑ a ∈ bad, 2 * ∑ b : A, (Finset.univ.filter (marked a b)).card :=
        Finset.sum_le_sum hrow
      _ ≤ ∑ a : A, 2 * ∑ b : A, (Finset.univ.filter (marked a b)).card :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ bad)
      _ = 2 * M := by simp [M, Finset.mul_sum]
  have hpos : 0 < Fintype.card A := Fintype.card_pos
  have hhalf : 2 * bad.card < Fintype.card A := by
    by_contra hn
    have hh : Fintype.card A ≤ 2 * bad.card := Nat.le_of_not_gt hn
    have hh' := Nat.mul_le_mul_right (Fintype.card A ^ 2) hh
    dsimp [M] at hbad
    nlinarith
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset A)) good
  change (Finset.univ.filter good).card + bad.card = Fintype.card A at hpartition
  omega

/-- Full scalar-field conclusion of the all-slopes argument, from actual marked
parameter triples and actual nonzero target-line equations. -/
theorem exists_ringHom_of_few_line_exceptions [Fintype K]
    (H : K →+ L) (h1 : H 1 = 1)
    (marked : K → K → K → Prop) [∀ a b, DecidablePred (marked a b)]
    (u v w : K → K → L)
    (hnondegenerate : ∀ a b, u a b ≠ 0 ∨ v a b ≠ 0 ∨ w a b ≠ 0)
    (hline : ∀ a b x, ¬ marked a b x →
      u a b * H x + v a b * H (a * x + b) = w a b)
    (few : 4 * (∑ a : K, ∑ b : K, (Finset.univ.filter (marked a b)).card)
      < Fintype.card K ^ 3) :
    ∃ σ : K →+* L, ∀ x, σ x = H x := by
  classical
  have hrow (a : K) (ha : a ∉ scalarStabilizer H h1) (b : K) :
      Fintype.card K ≤ 2 * (Finset.univ.filter (marked a b)).card := by
    have hc := twice_card_projective_line_parameters_le H h1 a b ha
      (u a b) (v a b) (w a b) (hnondegenerate a b)
    have hsub : (Finset.univ.filter fun x => ¬ marked a b x) ⊆
        Finset.univ.filter fun x => u a b * H x + v a b * H (a * x + b) = w a b := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hline a b x (Finset.mem_filter.mp hx).2⟩
    have hcount := Finset.card_le_card hsub
    have hp := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset K)) (marked a b)
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
    simp only [Finset.card_univ] at hp
    omega
  have hmajor := majority_slopes_of_few_marks
    (fun a => a ∈ scalarStabilizer H h1) marked hrow few
  have hc : Nat.card K < 2 * Nat.card (scalarStabilizer H h1) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hmajor
  exact ⟨ringHomOfManySlopes H h1 hc, fun _ => rfl⟩

end Erdos85.IncidenceRepair

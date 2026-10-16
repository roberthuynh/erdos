import Openmath.Erdos642.Proofs.CampaignFe72210b.SpectralOccupation
import Openmath.Erdos642.Proofs.CampaignFe72210b.PathEvents
import Openmath.Erdos642.Proofs.CampaignFe72210b.OccupationAlgebra

/-! Finite level counting and actual retained-level event union reduction.
No signed-observable tail is assumed. This is not a graph theorem. -/
namespace Erdos642.Continuation3.LevelSetOccupation
open Erdos642.FiniteMarkov Erdos642.OccupationTail Erdos642.OccupationAlgebra Matrix

theorem floor_eq_level_count (w η : ℝ) (hη : 0 < η) (hw : 0 ≤ w)
    (J : ℕ) (hf : ⌊w / η⌋₊ ≤ J) :
    (⌊w / η⌋₊ : ℝ) =
      ∑ j ∈ Finset.Icc 1 J, if (j : ℝ) * η ≤ w then (1 : ℝ) else 0 := by
  classical
  have hq : 0 ≤ w / η := div_nonneg hw hη.le
  have he : (Finset.Icc (1 : ℕ) J).filter (fun (j : ℕ) => (j : ℝ) * η ≤ w) =
      Finset.Icc (1 : ℕ) ⌊w / η⌋₊ := by
    ext (j : ℕ)
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have hj : (j : ℝ) * η ≤ w ↔ j ≤ ⌊w / η⌋₊ := by
      rw [← le_div_iff₀ hη, Nat.le_floor_iff hq]
    rw [hj]
    omega
  rw [← Finset.sum_filter, he]
  simp

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
private theorem vertexSum_affine (f : V → ℝ) (a b : ℝ)
    {n : ℕ} (x : V) (p : Path V n) :
    Chain.vertexSum (fun y => a * f y + b) x p =
      a * Chain.vertexSum f x p + (n + 1 : ℕ) * b := by
  induction n generalizing x with
  | zero => simp [Chain.vertexSum]
  | succ n ih =>
    rcases p with ⟨y, p⟩
    simp only [Chain.vertexSum, ih, Nat.cast_add, Nat.cast_one]
    ring

omit [Fintype V] in
/-- All approximation premises are deterministic finite sums. -/
theorem retained_level_event_containment {I : Type*} (R : Finset I)
    (S : I → Finset V) (v : V → ℝ) (mass : I → ℝ) (η δ μ : ℝ)
    (hη : 0 ≤ η)
    (hpoint : ∀ y, η * (∑ j ∈ R, if y ∈ S j then (1 : ℝ) else 0) - δ ≤ v y)
    (hmean : μ ≤ η * ∑ j ∈ R, mass j)
    {n : ℕ} (x : V) (p : Path V n)
    (hbad : Chain.vertexSum v x p < (μ / 2 - δ) * (n + 1 : ℕ)) :
    ∃ j ∈ R, occupation (S j) x p ≤ (n + 1 : ℕ) * mass j / 2 := by
  classical
  by_contra! hg
  have hlo := vertexSum_mono _ v hpoint x p
  rw [show (fun y => η * (∑ j ∈ R, if y ∈ S j then (1 : ℝ) else 0) - δ) =
    (fun y => η * (∑ j ∈ R, if y ∈ S j then (1 : ℝ) else 0) + -δ) by rfl,
    vertexSum_affine, vertexSum_sum] at hlo
  have hh : (n + 1 : ℕ) * (∑ j ∈ R, mass j) / 2 ≤
      ∑ j ∈ R, occupation (S j) x p := by
    calc
      _ = ∑ j ∈ R, (n + 1 : ℕ) * mass j / 2 := by
        rw [Finset.mul_sum, Finset.sum_div]
      _ ≤ _ := Finset.sum_le_sum (fun j hj => (hg j hj).le)
  have hmul := mul_le_mul_of_nonneg_left hh hη
  have hm := mul_le_mul_of_nonneg_left hmean
    (show 0 ≤ ((n + 1 : ℕ) : ℝ) / 2 by positivity)
  change η * (∑ i ∈ R, occupation (S i) x p) + (n + 1 : ℕ) * -δ ≤ _ at hlo
  nlinarith

theorem retained_level_tail (C : Chain V) (u : V → ℝ)
    (huPos : ∀ x, 0 < u x) (hu : (∑ x, u x ^ 2) = 1)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hA : (C.similarTransition u).IsHermitian)
    (hAu : C.similarTransition u *ᵥ u = u)
    (hpos : ∀ f : V → ℝ, 0 ≤ dotProduct f (C.similarTransition u *ᵥ f))
    (hgap : ∀ h : V → ℝ, dotProduct h u = 0 →
      dotProduct h (C.similarTransition u *ᵥ h) ≤ (1 - γ) * ∑ y, h y ^ 2)
    {I : Type*} (R : Finset I) (S : I → Finset V) (v : V → ℝ)
    (η δ μ ν : ℝ) (hη : 0 ≤ η)
    (hpoint : ∀ y, η * (∑ j ∈ R, if y ∈ S j then (1 : ℝ) else 0) - δ ≤ v y)
    (hmean : μ ≤ η * ∑ j ∈ R, Erdos642.TiltedOperator.mass (S j) u)
    (hretain : ∀ j ∈ R, ν ≤ Erdos642.TiltedOperator.mass (S j) u)
    (n : ℕ) (hn : 1 ≤ n) (x : V) :
    C.eventMass (n - 1)
      (fun y p => Chain.vertexSum v y p < (μ / 2 - δ) * (n : ℝ)) x ≤
      (R.card : ℝ) * (2 / u x ^ 2) * Real.exp (-γ * ν * (n : ℝ) / 64) := by
  classical
  have hncast : ((n - 1 + 1 : ℕ) : ℝ) = (n : ℝ) := by congr 1; omega
  have hcontain := C.eventMass_mono
    (fun y p => Chain.vertexSum v y p < (μ / 2 - δ) * (n : ℝ))
    (fun y p => ∃ j ∈ R, occupation (S j) y p ≤
      (n : ℝ) * Erdos642.TiltedOperator.mass (S j) u / 2)
    (fun y p hp => by
      simpa only [hncast] using retained_level_event_containment R S v
        (fun j => Erdos642.TiltedOperator.mass (S j) u) η δ μ hη hpoint hmean (n := n - 1) y p
        (by simpa only [hncast] using hp)) x
  apply hcontain.trans
  apply (C.eventMass_biUnion_le R _ x).trans
  calc
    _ ≤ ∑ j ∈ R, (2 / u x ^ 2) * Real.exp (-γ * ν * (n : ℝ) / 64) := by
      apply Finset.sum_le_sum
      intro j hj
      apply (C.point_mass_occupation_tail u huPos hu γ hγ hγ1 hA hAu hpos hgap
        (S j) n hn x).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (hretain j hj) hγ.le
      have h' := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
      linarith
    _ = _ := by simp; ring

/-- The literal floor levels satisfy the retained approximation and mean bounds.
The endpoint floor, rather than the ceiling, pays the rare-level mean loss. -/
theorem literal_level_approximation (u v : V → ℝ) (η δ μ : ℝ)
    (hη : 0 < η) (_hδ : 0 ≤ δ) (hδ1 : δ ≤ η)
    (hv : ∀ y, -δ ≤ v y ∧ v y ≤ 1 + δ) (hη1 : η ≤ 1 / 2)
    (hu : (∑ y, u y ^ 2) = 1) (hμ : μ ≤ ∑ y, u y ^ 2 * v y) :
    let J := ⌊2 / η⌋₊
    let S := fun j : ℕ => Finset.univ.filter (fun y => (j : ℝ) * η ≤ v y + δ)
    let R := (Finset.Icc 1 J).filter (fun j => η ≤ Erdos642.TiltedOperator.mass (S j) u)
    (∀ y, η * (∑ j ∈ R, if y ∈ S j then (1 : ℝ) else 0) - δ ≤ v y) ∧
    μ + δ - 3 * η ≤ η * ∑ j ∈ R, Erdos642.TiltedOperator.mass (S j) u := by
  classical
  dsimp only
  let J := ⌊2 / η⌋₊
  let S := fun j : ℕ => Finset.univ.filter (fun y => (j : ℝ) * η ≤ v y + δ)
  let L := Finset.Icc 1 J
  let R := L.filter (fun j => η ≤ Erdos642.TiltedOperator.mass (S j) u)
  change (∀ y, η * (∑ j ∈ R, if y ∈ S j then (1 : ℝ) else 0) - δ ≤ v y) ∧ _
  have hw (y : V) : 0 ≤ v y + δ := by linarith [(hv y).1]
  have hw2 (y : V) : v y + δ ≤ 2 := by linarith [(hv y).2]
  have hcount (y : V) : (∑ j ∈ L, if y ∈ S j then (1 : ℝ) else 0) =
      (⌊(v y + δ) / η⌋₊ : ℝ) := by
    have hf : ⌊(v y + δ) / η⌋₊ ≤ J := Nat.floor_mono
      ((div_le_div_iff_of_pos_right hη).2 (hw2 y))
    simpa [L, S] using (floor_eq_level_count (v y + δ) η hη (hw y) J hf).symm
  have hstep (y : V) :
      v y + δ - η ≤ η * (∑ j ∈ L, if y ∈ S j then (1 : ℝ) else 0) ∧
      η * (∑ j ∈ L, if y ∈ S j then (1 : ℝ) else 0) ≤ v y + δ := by
    rw [hcount]
    have hf := Nat.floor_le (div_nonneg (hw y) hη.le)
    have hg := Nat.lt_floor_add_one ((v y + δ) / η)
    have hf' := (le_div_iff₀ hη).mp hf
    have hg' := (div_lt_iff₀ hη).mp hg
    constructor <;> nlinarith
  constructor
  · intro y
    have hs : (∑ j ∈ R, if y ∈ S j then (1 : ℝ) else 0) ≤
        ∑ j ∈ L, if y ∈ S j then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) 
      intro j _ _
      positivity
    have hs' := mul_le_mul_of_nonneg_left hs hη.le
    linarith [(hstep y).2]
  · have hid : (∑ j ∈ L, Erdos642.TiltedOperator.mass (S j) u) =
        ∑ y, u y ^ 2 * (∑ j ∈ L, if y ∈ S j then (1 : ℝ) else 0) := by
      unfold Erdos642.TiltedOperator.mass
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    have hall : μ + δ - η ≤ η * ∑ j ∈ L, Erdos642.TiltedOperator.mass (S j) u := by
      have hs := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset V)) =>
        mul_le_mul_of_nonneg_left (hstep y).1 (sq_nonneg (u y)))
      rw [hid, Finset.mul_sum]
      have he : (∑ y, u y ^ 2 * (v y + δ - η)) =
          (∑ y, u y ^ 2 * v y) + δ - η := by
        simp_rw [mul_sub, mul_add]
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          ← Finset.sum_mul, ← Finset.sum_mul, hu]
        ring
      rw [he] at hs
      have he2 : (∑ y, u y ^ 2 * (η * (∑ j ∈ L, if y ∈ S j then (1 : ℝ) else 0))) =
          ∑ y, η * (u y ^ 2 * (∑ j ∈ L, if y ∈ S j then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl; intros; ring
      rw [he2] at hs
      linarith
    have hrare : (∑ j ∈ L, Erdos642.TiltedOperator.mass (S j) u) ≤
        (∑ j ∈ R, Erdos642.TiltedOperator.mass (S j) u) + (J : ℝ) * η := by
      have hs := Finset.sum_le_sum (fun j (_ : j ∈ L) => show
        Erdos642.TiltedOperator.mass (S j) u ≤
          (if η ≤ Erdos642.TiltedOperator.mass (S j) u then
             Erdos642.TiltedOperator.mass (S j) u else 0) + η by
          split_ifs <;> linarith)
      rw [Finset.sum_add_distrib, ← Finset.sum_filter] at hs
      simpa [R, L] using hs
    have hJ : η * (J : ℝ) ≤ 2 := by
      have hf := Nat.floor_le (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hη.le)
      have hf' := (le_div_iff₀ hη).mp hf
      simpa [J, mul_comm] using hf'
    have hh := mul_le_mul_of_nonneg_left hrare hη.le
    have hhh := mul_le_mul_of_nonneg_right hJ hη.le
    nlinarith
/-- Literal signed-center tail. This uses only proved indicator concentration;
the mean, floor error, and discarded-level losses are discharged internally. -/
theorem signed_center_tail (C : Chain V) (u : V → ℝ)
    (huPos : ∀ x, 0 < u x) (hu : (∑ x, u x ^ 2) = 1)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hA : (C.similarTransition u).IsHermitian)
    (hAu : C.similarTransition u *ᵥ u = u)
    (hpos : ∀ f : V → ℝ, 0 ≤ dotProduct f (C.similarTransition u *ᵥ f))
    (hgap : ∀ h : V → ℝ, dotProduct h u = 0 →
      dotProduct h (C.similarTransition u *ᵥ h) ≤ (1 - γ) * ∑ y, h y ^ 2)
    (v : V → ℝ) (μ δ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ μ / 1024)
    (hv : ∀ y, -δ ≤ v y ∧ v y ≤ 1 + δ)
    (hmean : μ ≤ ∑ y, u y ^ 2 * v y)
    (n : ℕ) (hn : 1 ≤ n) (x : V) :
    C.eventMass (n - 1)
      (fun y p => Chain.vertexSum v y p < 255 * μ * (n : ℝ) / 512) x ≤
      (⌈2 / (μ / 1024)⌉₊ : ℝ) * (2 / u x ^ 2) *
        Real.exp (-γ * μ * (n : ℝ) / 65536) := by
  classical
  let η := μ / 1024
  let J := ⌊2 / η⌋₊
  let S := fun j : ℕ => Finset.univ.filter (fun y => (j : ℝ) * η ≤ v y + δ)
  let R := (Finset.Icc 1 J).filter (fun j => η ≤ Erdos642.TiltedOperator.mass (S j) u)
  have hη : 0 < η := by dsimp [η]; positivity
  have ha := literal_level_approximation u v η δ μ hη hδ hδ1 hv
    (by dsimp [η]; linarith) hu hmean
  change (∀ y, η * (∑ j ∈ R, if y ∈ S j then (1 : ℝ) else 0) - δ ≤ v y) ∧
    μ + δ - 3 * η ≤ η * ∑ j ∈ R, Erdos642.TiltedOperator.mass (S j) u at ha
  have ht := retained_level_tail C u huPos hu γ hγ hγ1 hA hAu hpos hgap
    R S v η δ (μ + δ - 3 * η) η hη.le ha.1 ha.2
    (fun j hj => (Finset.mem_filter.mp hj).2) n hn x
  have hc := C.eventMass_mono (n := n - 1)
    (fun y p => Chain.vertexSum v y p < 255 * μ * (n : ℝ) / 512)
    (fun y p => Chain.vertexSum v y p < ((μ + δ - 3 * η) / 2 - δ) * (n : ℝ))
    (fun y p hp => by
      have hh : 255 * μ / 512 ≤ (μ + δ - 3 * η) / 2 - δ := by
        dsimp [η]; linarith
      have hh' := mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
      apply hp.trans_le
      convert hh' using 1; ring) x
  apply hc.trans (ht.trans _)
  have hcard : (R.card : ℝ) ≤ (⌈2 / η⌉₊ : ℝ) := by
    have hR : R.card ≤ J := by
      have hh := Finset.card_le_card (Finset.filter_subset
        (fun j => η ≤ Erdos642.TiltedOperator.mass (S j) u) (Finset.Icc 1 J))
      simpa [R] using hh
    have hJ : J ≤ ⌈2 / η⌉₊ := Nat.floor_le_ceil _
    exact_mod_cast hR.trans hJ
  have he : -γ * η * (n : ℝ) / 64 = -γ * μ * (n : ℝ) / 65536 := by
    dsimp [η]; ring
  rw [he]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcard (by positivity)) (Real.exp_nonneg _)
end Erdos642.Continuation3.LevelSetOccupation

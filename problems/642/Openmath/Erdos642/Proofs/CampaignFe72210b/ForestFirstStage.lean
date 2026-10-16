import Openmath.Erdos642.Proofs.CampaignFe72210b.ForestOccupationAlgebra
import Openmath.Erdos642.Proofs.CampaignFe72210b.PathEvents

/-! Actual bad-star subset selection and the finite first-stage forest union bound. -/
namespace Erdos642.CampaignFe72210b.ForestBundle
open Erdos642.FiniteMarkov Erdos642.OccupationTail
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {A B : Finset V} {q m b : ℕ}
variable (F : Erdos642.CampaignFe72210b.ForestBundle G A B q m b)

noncomputable def badInForest (f : Fin q) (a : ℝ) {n : ℕ}
    (x : V) (p : Path V n) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun j => occupation (F.leaves (f, j)) x p < a)

omit [Fintype V] in
@[simp] theorem mem_badInForest (f : Fin q) (a : ℝ) {n : ℕ}
    (x : V) (p : Path V n) (j : Fin m) :
    j ∈ F.badInForest f a x p ↔ occupation (F.leaves (f, j)) x p < a := by
  classical
  simp [badInForest]

omit [Fintype V] in
/-- Actual large bad sets contain an actual prescribed-size set of bad stars. -/
theorem bad_subset_exists (f : Fin q) (a : ℝ) {n : ℕ} (x : V) (p : Path V n)
    (h : ℕ) (hbad : h ≤ (F.badInForest f a x p).card) :
    ∃ J : Finset (Fin m), J.card = h ∧
      ∀ j ∈ J, occupation (F.leaves (f, j)) x p < a := by
  obtain ⟨J, hJ, hcard⟩ := Finset.exists_subset_card_eq hbad
  exact ⟨J, hcard, fun j hj => (F.mem_badInForest f a x p j).mp (hJ hj)⟩

/-- The exact leaf-union event forced by h individually bad stars. -/
theorem bad_subset_low_union (f : Fin q) (t : ℕ) (ht : 1 ≤ t)
    (N : ℝ) (hN : 0 < N) (hb : 1 ≤ b) (h : ℕ) (hh : 1 ≤ h)
    {n : ℕ} (x : V) (p : Path V n)
    (hbad : h ≤ (F.badInForest f ((t : ℝ) * (b : ℝ) / (600 * N)) x p).card) :
    ∃ J ∈ (Finset.univ : Finset (Fin m)).powersetCard h,
      occupation (F.leafUnion f J) x p <
        (t : ℝ) * ((F.leafUnion f J).card : ℝ) / (300 * N) := by
  obtain ⟨J, hcard, hJbad⟩ := F.bad_subset_exists f _ x p h hbad
  have hJ : J.Nonempty := Finset.card_pos.mp (by omega)
  have hu := F.bad_leafUnion_occupation_lt f J hJ _ x p hJbad
  refine ⟨J, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩, ?_⟩
  apply lt_of_lt_of_le hu
  rw [F.leafUnion_card, Nat.cast_mul]
  have hnonneg : 0 ≤ (J.card : ℝ) * ((t : ℝ) * (b : ℝ) / (600 * N)) := by positivity
  have heq : (t : ℝ) * ((J.card : ℝ) * (b : ℝ)) / (300 * N) =
      2 * ((J.card : ℝ) * ((t : ℝ) * (b : ℝ) / (600 * N))) := by ring
  rw [heq]
  linarith

/-- Exact finite subset-sum bound; its fixed-union suppliers are still explicit. -/
theorem bad_forest_eventMass_le_subset_sum (C : Chain V) (f : Fin q)
    (t : ℕ) (ht : 1 ≤ t) (N : ℝ) (hN : 0 < N) (hb : 1 ≤ b)
    (h : ℕ) (hh : 1 ≤ h) (x : V) :
    C.eventMass (t - 1)
      (fun y p => h ≤ (F.badInForest f ((t : ℝ) * (b : ℝ) / (600 * N)) y p).card) x ≤
      ∑ J ∈ (Finset.univ : Finset (Fin m)).powersetCard h,
        C.eventMass (t - 1) (fun y p => occupation (F.leafUnion f J) y p <
          (t : ℝ) * ((F.leafUnion f J).card : ℝ) / (300 * N)) x := by
  have hm := C.eventMass_mono (n := t - 1)
    (fun y p => h ≤ (F.badInForest f ((t : ℝ) * (b : ℝ) / (600 * N)) y p).card)
    (fun y p => ∃ J ∈ (Finset.univ : Finset (Fin m)).powersetCard h,
      occupation (F.leafUnion f J) y p < (t : ℝ) * ((F.leafUnion f J).card : ℝ) / (300 * N))
    (fun y p hp => F.bad_subset_low_union f t ht N hN hb h hh y p hp) x
  exact hm.trans (C.eventMass_biUnion_le _ _ x)

/-- A literal per-forest finite union bound, with explicit fixed-leaf-union input. -/
theorem bad_forest_eventMass_le (C : Chain V) (f : Fin q)
    (t : ℕ) (ht : 1 ≤ t) (N : ℝ) (hN : 0 < N) (hb : 1 ≤ b)
    (h : ℕ) (hh : 1 ≤ h) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hfixed : ∀ J : Finset (Fin m), J.card = h → ∀ y : V,
      C.eventMass (t - 1) (fun z p => occupation (F.leafUnion f J) z p <
        (t : ℝ) * ((F.leafUnion f J).card : ℝ) / (300 * N)) y ≤ delta)
    (x : V) :
    C.eventMass (t - 1)
      (fun y p => h ≤ (F.badInForest f ((t : ℝ) * (b : ℝ) / (600 * N)) y p).card) x ≤
      (2 : ℝ) ^ m * delta := by
  have hcap : ((Finset.univ : Finset (Fin m)).powersetCard h).card ≤ 2 ^ m := by
    calc
      _ ≤ ((Finset.univ : Finset (Fin m)).powerset).card := Finset.card_le_card (by
        intro J hJ
        exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hJ).1)
      _ = _ := by simp
  calc
    _ ≤ ∑ J ∈ (Finset.univ : Finset (Fin m)).powersetCard h,
        C.eventMass (t - 1) (fun y p => occupation (F.leafUnion f J) y p <
          (t : ℝ) * ((F.leafUnion f J).card : ℝ) / (300 * N)) x :=
      F.bad_forest_eventMass_le_subset_sum C f t ht N hN hb h hh x
    _ ≤ ∑ _J ∈ (Finset.univ : Finset (Fin m)).powersetCard h, delta := by
      apply Finset.sum_le_sum
      intro J hJ
      exact hfixed J (Finset.mem_powersetCard.mp hJ).2 x
    _ = (((Finset.univ : Finset (Fin m)).powersetCard h).card : ℝ) * delta := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcap) hdelta

/-- The reviewed ceiling-half integer threshold, including odd m and m=1. -/
theorem bad_forest_half_eventMass_le (C : Chain V) (f : Fin q)
    (t : ℕ) (ht : 1 ≤ t) (N : ℝ) (hN : 0 < N) (hb : 1 ≤ b) (hm : 1 ≤ m)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hfixed : ∀ J : Finset (Fin m), J.card = (m + 1) / 2 → ∀ y : V,
      C.eventMass (t - 1) (fun z p => occupation (F.leafUnion f J) z p <
        (t : ℝ) * ((F.leafUnion f J).card : ℝ) / (300 * N)) y ≤ delta)
    (x : V) :
    C.eventMass (t - 1)
      (fun y p => (m + 1) / 2 ≤ (F.badInForest f ((t : ℝ) * (b : ℝ) / (600 * N)) y p).card) x ≤
      (2 : ℝ) ^ m * delta := by
  exact F.bad_forest_eventMass_le C f t ht N hN hb ((m + 1) / 2) (by omega) delta hdelta hfixed x

end Erdos642.CampaignFe72210b.ForestBundle

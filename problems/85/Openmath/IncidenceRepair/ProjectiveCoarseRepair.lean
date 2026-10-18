import Openmath.IncidenceRepair.AffineGeometry
import Openmath.IncidenceRepair.GeometryDesign
import Openmath.IncidenceRepair.CoarseCounting
import Openmath.IncidenceRepair.Target
import Openmath.IncidenceRepair.NumericBounds
import Openmath.IncidenceRepair.DensityBounds

noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair

lemma filtered_incidence_sum {P H : Type*} [Fintype P]
    (U : P → Prop) [DecidablePred U] (R : P → H → Prop) (h : H) :
    (∑ p ∈ Finset.univ.filter U, incidence R p h) =
      (Nat.card {p : P // U p ∧ R p h} : ℝ) := by
  classical
  rw [Finset.sum_filter]
  convert sum_indicator_eq_natCard (fun p : P => U p ∧ R p h) using 1
  apply Finset.sum_congr rfl
  intro p _
  unfold incidence
  split_ifs <;> simp_all

variable {K L : Type*} [Field K] [Field L] [Finite K] [Finite L] {n : ℕ}

lemma affine_restriction_card (R : Point K n → Prop) :
    Nat.card {p : Point K n // ¬ Incident p infinityHyperplane ∧ R p} =
      Nat.card {x : Fin n → K // R (affinePoint x)} := by
  let e : {x : Fin n → K // R (affinePoint x)} ≃
      {p : Point K n // ¬ Incident p infinityHyperplane ∧ R p} :=
    { toFun := fun x => ⟨affinePoint x.val, affinePoint_not_infinity x.val, x.property⟩
      invFun := fun p => ⟨affinePointEquiv.symm ⟨p.val, p.property.1⟩, by
        have h := congrArg Subtype.val (affinePointEquiv.apply_symm_apply ⟨p.val, p.property.1⟩)
        change affinePoint (affinePointEquiv.symm ⟨p.val, p.property.1⟩) = p.val at h
        change R (affinePoint (affinePointEquiv.symm ⟨p.val, p.property.1⟩))
        rw [h]
        exact p.property.2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact affinePointEquiv.symm_apply_apply x.val
      right_inv := by
        intro p
        apply Subtype.ext
        have h := congrArg Subtype.val (affinePointEquiv.apply_symm_apply ⟨p.val, p.property.1⟩)
        change affinePoint (affinePointEquiv.symm ⟨p.val, p.property.1⟩) = p.val at h
        exact h }
  exact (Nat.card_congr e).symm

/-- Actual affine mismatch count, on source points rather than a supplied budget. -/
def affineErrors (φ : Point K n → Point L n) (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n) : ℕ :=
  Nat.card {p : Point K n // ¬ Incident p infinityHyperplane ∧ φ p ≠ pointEmbedding σ A p}

/-- Actual wrong non-infinity hyperplanes. -/
def affineHyperplaneErrors (ψ : Hyperplane K n → Hyperplane L n) (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n) : ℕ :=
  Nat.card {H : Hyperplane K n // H ≠ infinityHyperplane ∧ ψ H ≠ hyperplaneEmbedding σ A H}

/-- Actual wrong points at source infinity. -/
def infinityErrors (φ : Point K n → Point L n) (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n) : ℕ :=
  Nat.card {p : Point K n // Incident p infinityHyperplane ∧ φ p ≠ pointEmbedding σ A p}

/-- Section 7.1 from actual affine incidence counts and the proper-subfield cap. -/
theorem projective_affine_error_inequality (hn : 2 ≤ n) (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n)
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n) :
    ((Nat.card K : ℝ)^(n-1) - (Nat.card K : ℝ)^(n-1)/(Nat.card K : ℝ)) *
      (affineHyperplaneErrors ψ σ A : ℝ) ≤
      (brokenFlags φ ψ : ℝ) + (flagDegree K n : ℝ) * affineErrors φ σ A := by
  classical
  letI : Fintype (Point K n) := Fintype.ofFinite _
  let U := Finset.univ.filter (fun p : Point K n => ¬ Incident p infinityHyperplane)
  let S := U.filter (fun p => φ p ≠ pointEmbedding σ A p)
  let C := Finset.univ.filter (fun H : Hyperplane K n =>
    H ≠ infinityHyperplane ∧ ψ H ≠ hyperplaneEmbedding σ A H)
  have hU : ∀ p, p ∈ U ↔ ¬ Incident p infinityHyperplane := by simp [U]
  have hC : ∀ H, H ∈ C ↔ H ≠ infinityHyperplane ∧ ψ H ≠ hyperplaneEmbedding σ A H := by simp [C]
  have hp : (Nat.card K : ℝ)^(n-2) = (Nat.card K : ℝ)^(n-1)/(Nat.card K : ℝ) := by
    have hq : (Nat.card K : ℝ) ≠ 0 := by exact_mod_cast (show Nat.card K ≠ 0 by have := Finite.one_lt_card (α := K); omega)
    apply (eq_div_iff hq).mpr
    rw [← pow_succ]
    congr 1
    omega
  have hdegree : ∀ H ∈ C, ∑ p ∈ U, incidence Incident p H = (Nat.card K : ℝ)^(n-1) := by
    intro H hH
    rw [filtered_incidence_sum, affine_restriction_card, affine_hyperplane_points_card H ((hC H).mp hH).1]
    norm_cast
  have hrow : ∀ p ∈ S, ∑ H ∈ C, incidence Incident p H ≤ (flagDegree K n : ℝ) := by
    intro p _
    calc
      _ ≤ ∑ H, incidence Incident p H := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ C) (fun H _ _ => by unfold incidence; split_ifs <;> positivity)
      _ = _ := projective_degree p
  have hsurvive : ∀ H ∈ C,
      ∑ p ∈ U, incidence (fun p H => Incident p H ∧ Incident (pointEmbedding σ A p) (ψ H)) p H ≤
        (Nat.card K : ℝ)^(n-1)/(Nat.card K : ℝ) := by
    intro H hH
    rw [filtered_incidence_sum, affine_restriction_card, ← hp]
    exact_mod_cast wrong_affine_hyperplane_intersection_card hn σ A H (ψ H) ((hC H).mp hH).2
  have h := coarse_affine_count Incident Incident φ (pointEmbedding σ A) ψ U S C
    ((Nat.card K : ℝ)^(n-1)) (Nat.card K : ℝ) (flagDegree K n : ℝ)
    (Finset.filter_subset _ _) (by intro p hp; simp [S, hp]) hdegree hrow hsurvive
  rw [brokenFlagSum_eq_card] at h
  have hScard : S.card = affineErrors φ σ A := by
    simp [S, U, affineErrors, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter]
  have hCcard : C.card = affineHyperplaneErrors ψ σ A := by
    simp [C, affineHyperplaneErrors, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa only [hScard, hCcard, brokenFlags] using h

/-- Section 7.2 from actual infinity points and non-infinity hyperplanes. -/
theorem projective_infinity_error_inequality (hn : 2 ≤ n) (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n)
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n) :
    ((Nat.card K : ℝ)^(n-1) - 1) * (infinityErrors φ σ A : ℝ) ≤
      (brokenFlags φ ψ : ℝ) +
        (((Nat.card K^(n-1)-1)/(Nat.card K-1) : ℕ) : ℝ) * affineHyperplaneErrors ψ σ A := by
  classical
  letI : Fintype (Point K n) := Fintype.ofFinite _
  let U := Finset.univ.filter (fun H : Hyperplane K n => H ≠ infinityHyperplane)
  let B := U.filter (fun H => ψ H ≠ hyperplaneEmbedding σ A H)
  let S := Finset.univ.filter (fun p : Point K n =>
    Incident p infinityHyperplane ∧ φ p ≠ pointEmbedding σ A p)
  let lam : ℝ := ((Nat.card K^(n-1)-1)/(Nat.card K-1) : ℕ)
  have hS : ∀ p, p ∈ S ↔ Incident p infinityHyperplane ∧ φ p ≠ pointEmbedding σ A p := by simp [S]
  have hdegree : ∀ p ∈ S, ∑ H ∈ U, incidence Incident p H = (flagDegree K n : ℝ)-1 := by
    intro p hp
    change (∑ H ∈ Finset.univ.filter (fun H : Hyperplane K n => H ≠ infinityHyperplane),
      incidence (fun H p => Incident p H) H p) = _
    rw [filtered_incidence_sum]
    have he : Nat.card {H : Hyperplane K n // H ≠ infinityHyperplane ∧ Incident p H} =
        Nat.card {H : Hyperplane K n // Incident p H ∧ H ≠ infinityHyperplane} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun H => and_comm))
    rw [he, affine_hyperplanes_through_infinity_card p ((hS p).mp hp).1]
    change ((flagDegree K n - 1 : ℕ) : ℝ) = _
    rw [Nat.cast_sub (flagDegree_pos (K := K) hn)]
    norm_num
  have hrow : ∀ H ∈ B, ∑ p ∈ S, incidence Incident p H ≤ lam := by
    intro H hH
    have hH0 : H ≠ infinityHyperplane := by simpa [B, U] using (Finset.mem_filter.mp hH).1
    calc
      _ ≤ ∑ p ∈ Finset.univ.filter (fun p : Point K n => Incident p infinityHyperplane),
          incidence Incident p H := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ((hS p).mp hp).1
        · intro p _ _
          unfold incidence
          split_ifs <;> positivity
      _ = lam := by
        rw [filtered_incidence_sum]
        have he : Nat.card {p : Point K n // Incident p infinityHyperplane ∧ Incident p H} =
            Nat.card {p : Point K n // Incident p H ∧ Incident p infinityHyperplane} :=
          Nat.card_congr (Equiv.subtypeEquivRight (fun p => and_comm))
        rw [he, affine_hyperplane_infinity_points_card H hH0]
  have hsurvive : ∀ p ∈ S,
      ∑ H ∈ U, incidence (fun p H => Incident p H ∧ Incident (φ p) (hyperplaneEmbedding σ A H)) p H ≤ lam := by
    intro p hp
    calc
      _ ≤ ∑ H, incidence (fun p H => Incident p H ∧ Incident (φ p) (hyperplaneEmbedding σ A H)) p H := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
        intro H _ _
        unfold incidence
        split_ifs <;> positivity
      _ ≤ lam := by
        have he := sum_indicator_eq_natCard (fun H : Hyperplane K n =>
          Incident p H ∧ Incident (φ p) (hyperplaneEmbedding σ A H))
        have hs : (∑ H, incidence (fun p H => Incident p H ∧
            Incident (φ p) (hyperplaneEmbedding σ A H)) p H) =
            (Nat.card {H : Hyperplane K n // Incident p H ∧
              Incident (φ p) (hyperplaneEmbedding σ A H)} : ℝ) := by
          convert he using 1
          apply Finset.sum_congr rfl
          intro H _
          dsimp [incidence]
          split_ifs <;> rfl
        rw [hs]
        dsimp [lam]
        exact_mod_cast wrong_point_intersection_card σ A p (φ p) ((hS p).mp hp).2
  have hsplit : (Nat.card K : ℝ)^(n-1) = (flagDegree K n : ℝ)-lam := by
    have hs := source_degree_split (Nat.card K) n (Finite.one_lt_card (α := K)) (show 1 ≤ n by omega)
    have hs' : (flagDegree K n : ℝ) = (Nat.card K : ℝ)^(n-1)+lam := by
      dsimp [flagDegree, lam]
      exact_mod_cast hs
    linarith
  have h := coarse_infinity_count Incident Incident φ ψ (hyperplaneEmbedding σ A) U B S
    ((Nat.card K : ℝ)^(n-1)) (flagDegree K n : ℝ) lam (Finset.filter_subset _ _)
    (by intro H hH; simp [B, hH]) hsplit hdegree hrow hsurvive
  rw [brokenFlagSum_eq_card] at h
  have hScard : S.card = infinityErrors φ σ A := by
    simp [S, infinityErrors, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hBcard : B.card = affineHyperplaneErrors ψ σ A := by
    simp [B, U, affineHyperplaneErrors, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter]
  simpa only [hScard, hBcard, brokenFlags, lam] using h

/-- Actual paired distance splits into the affine point, affine hyperplane,
and infinity point errors when the infinity hyperplane is already correct. -/
theorem repairDistance_affine_split (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n)
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (hInfinity : ψ infinityHyperplane = hyperplaneEmbedding σ A infinityHyperplane) :
    repairDistance φ (pointEmbedding σ A) ψ (hyperplaneEmbedding σ A) =
      affineErrors φ σ A + affineHyperplaneErrors ψ σ A + infinityErrors φ σ A := by
  classical
  letI : Fintype (Point K n) := Fintype.ofFinite _
  have hpoints : Nat.card {p : Point K n // φ p ≠ pointEmbedding σ A p} =
      affineErrors φ σ A + infinityErrors φ σ A := by
    simp only [affineErrors, infinityErrors, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have h := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun p : Point K n => φ p ≠ pointEmbedding σ A p))
      (fun p => Incident p infinityHyperplane)
    simpa only [Finset.filter_filter, and_comm, Nat.add_comm] using h.symm
  have hhyper : Nat.card {H : Hyperplane K n // ψ H ≠ hyperplaneEmbedding σ A H} =
      affineHyperplaneErrors ψ σ A := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro H
    constructor
    · intro h
      refine ⟨?_, h⟩
      intro he
      subst H
      exact h hInfinity
    · exact And.right
  unfold repairDistance
  rw [hpoints, hhyper]
  omega

/-- Section 7 for actual canonical projective spaces and arbitrary maps.
Both coarse inequalities are derived from original flags, not assumed. -/
theorem projective_coarse_repair (hn : 2 ≤ n) (σ : K →+* L)
    (A : Coordinates L n ≃ₗ[L] Coordinates L n)
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (hInfinity : ψ infinityHyperplane = hyperplaneEmbedding σ A infinityHyperplane)
    (hZ : (affineErrors φ σ A : ℝ) ≤ 971 / 10000000 * (pointCount K n : ℝ))
    (hδ : errorDensity φ ψ ≤ 1 / 4000000000) :
    (repairDistance φ (pointEmbedding σ A) ψ (hyperplaneEmbedding σ A) : ℝ) <
        (pointCount K n : ℝ) / 1000 ∧
    (repairDistance φ (pointEmbedding σ A) ψ (hyperplaneEmbedding σ A) : ℝ) ≤
        (pointCount K n : ℝ) / 20 := by
  let a : ℝ := (Nat.card K : ℝ)^(n-1)
  let d : ℝ := flagDegree K n
  let lam : ℝ := ((Nat.card K^(n-1)-1)/(Nat.card K-1) : ℕ)
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have ha : 2 ≤ a := by
    dsimp [a]
    exact_mod_cast source_gap_ge_two (Nat.card K) n hq hn
  have hqreal : (2 : ℝ) ≤ Nat.card K := by exact_mod_cast hq
  have hd : d ≤ 2 * a := by
    dsimp [d, a, flagDegree]
    exact_mod_cast source_degree_le_twice_gap (Nat.card K) n hq (by omega)
  have hlam : lam ≤ a-1 := by
    have hp : 1 ≤ Nat.card K^(n-1) := by
      have := source_gap_ge_two (Nat.card K) n hq hn
      omega
    have h := source_codegree_le_gap_sub_one (Nat.card K) n
    have h' : lam ≤ ((Nat.card K^(n-1)-1 : ℕ) : ℝ) := by
      dsimp [lam]
      exact_mod_cast h
    rw [Nat.cast_sub hp, Nat.cast_one, Nat.cast_pow] at h'
    exact h'
  have hsplit :
      (repairDistance φ (pointEmbedding σ A) ψ (hyperplaneEmbedding σ A) : ℝ) =
        (affineErrors φ σ A : ℝ) + (affineHyperplaneErrors ψ σ A : ℝ) +
          (infinityErrors φ σ A : ℝ) := by
    exact_mod_cast repairDistance_affine_split σ A φ ψ hInfinity
  have hc := coarse_paired_bound ha hqreal hd
    (show (0 : ℝ) ≤ affineHyperplaneErrors ψ σ A by positivity)
    (show (0 : ℝ) ≤ affineErrors φ σ A by positivity)
    (show (0 : ℝ) ≤ brokenFlags φ ψ by positivity) hlam
    (projective_affine_error_inequality hn σ A φ ψ)
    (projective_infinity_error_inequality hn σ A φ ψ) hsplit
  have hN : (0 : ℝ) < pointCount K n := by exact_mod_cast pointCount_pos (K := K) hn
  have hclose := coarse_proximity hN hZ (error_over_gap_bound hn φ ψ) hδ hc
  exact ⟨hclose, by linarith⟩

end Erdos85.IncidenceRepair

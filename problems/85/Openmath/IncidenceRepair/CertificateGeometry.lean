import Openmath.IncidenceRepair.FrameGeometry

noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair

variable {K : Type*} [Field K] {n : ℕ}

def coordinatePoint (i : Fin (n + 1)) : Point K n :=
  Projectivization.mk K (Pi.single i 1) (by
    classical
    intro h
    have := congr_fun h i
    simp at this)

def coordinateHyperplane (i : Fin (n + 1)) : Hyperplane K n := coordinatePoint i

def onesPoint : Point K n :=
  Projectivization.mk K (fun _ => 1) (by
    intro h
    have := congr_fun h 0
    simp at this)

lemma coordinatePoint_incident (i : Fin (n + 1)) (H : Hyperplane K n) :
    Incident (coordinatePoint i) H ↔ H.rep i = 0 := by
  classical
  unfold Incident coordinatePoint
  conv_lhs => rw [← Projectivization.mk_rep H]
  rw [Projectivization.orthogonal_mk]
  simp [dotProduct, Pi.single_apply]

lemma coordinateHyperplane_incident (p : Point K n) (i : Fin (n + 1)) :
    Incident p (coordinateHyperplane i) ↔ p.rep i = 0 := by
  classical
  unfold Incident coordinateHyperplane coordinatePoint
  conv_lhs => rw [← Projectivization.mk_rep p]
  rw [Projectivization.orthogonal_mk]
  simp [dotProduct, Pi.single_apply]

/-- The n coordinate points lying on a coordinate hyperplane determine it uniquely. -/
theorem hyperplane_forced_by_basis (H : Hyperplane K n) (i : Fin (n + 1))
    (h : ∀ j, j ≠ i → Incident (coordinatePoint j) H) :
    H = coordinateHyperplane i := by
  classical
  have hzero : ∀ j, j ≠ i → H.rep j = 0 := fun j hj =>
    (coordinatePoint_incident j H).mp (h j hj)
  have hi : H.rep i ≠ 0 := by
    intro hiz
    apply H.rep_nonzero
    funext j
    by_cases hj : j = i
    · simpa [hj] using hiz
    · exact hzero j hj
  rw [← Projectivization.mk_rep H]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
  refine ⟨H.rep i, ?_⟩
  funext j
  by_cases hj : j = i
  · simp [hj]
  · simp [Pi.single_apply, hj, hzero j hj]

/-- A coordinate pencil hyperplane X_i = t X_0, with i different from 0. -/
def pencilHyperplane (i : Fin (n + 1)) (hi : i ≠ 0) (t : K) : Hyperplane K n :=
  Projectivization.mk K (Pi.single i 1 - t • Pi.single 0 1) (by
    classical
    intro h
    have := congr_fun h i
    simp [hi] at this)

lemma pencilHyperplane_incident (p : Point K n) (i : Fin (n + 1)) (hi : i ≠ 0)
    (t : K) : Incident p (pencilHyperplane i hi t) ↔ p.rep i = t * p.rep 0 := by
  classical
  unfold Incident pencilHyperplane
  conv_lhs => rw [← Projectivization.mk_rep p]
  rw [Projectivization.orthogonal_mk]
  simp [dotProduct, Pi.single_apply, mul_sub, sub_mul, Finset.sum_sub_distrib,
    Pi.sub_apply, Pi.smul_apply, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, sub_eq_zero, mul_comm]

lemma onesPoint_incident (H : Hyperplane K n) :
    Incident (onesPoint (K := K) (n := n)) H ↔ ∑ i, H.rep i = 0 := by
  unfold Incident onesPoint
  conv_lhs => rw [← Projectivization.mk_rep H]
  rw [Projectivization.orthogonal_mk]
  simp [dotProduct, Pi.single_apply]

/-- The all-ones point and the n-1 complementary coordinate points force X_i=X_0. -/
theorem hyperplane_forced_by_ones (H : Hyperplane K n) (i : Fin (n + 1)) (hi : i ≠ 0)
    (hb : ∀ j, j ≠ 0 → j ≠ i → Incident (coordinatePoint j) H)
    (hI : Incident (onesPoint (K := K) (n := n)) H) :
    H = pencilHyperplane i hi 1 := by
  classical
  have hz : ∀ j, j ≠ 0 → j ≠ i → H.rep j = 0 := fun j h0 hi =>
    (coordinatePoint_incident j H).mp (hb j h0 hi)
  have hsum : H.rep 0 + H.rep i = 0 := by
    have hs := (onesPoint_incident H).mp hI
    have he : ∑ j, H.rep j = H.rep 0 + H.rep i := by
      calc
        ∑ j, H.rep j = ∑ j ∈ ({0, i} : Finset (Fin (n + 1))), H.rep j := by
          symm
          apply Finset.sum_subset (by simp)
          intro j hj hnot
          have hn : j ≠ 0 ∧ j ≠ i := by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hnot
          have hj0 := hn.1
          have hji := hn.2
          exact hz j hj0 hji
        _ = H.rep 0 + H.rep i := by simp [hi, Ne.symm hi]
    rwa [he] at hs
  rw [← Projectivization.mk_rep H]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
  refine ⟨H.rep i, ?_⟩
  funext j
  by_cases h0 : j = 0
  · subst j
    simp [hi, Ne.symm hi]
    linear_combination -hsum
  · by_cases hji : j = i
    · subst j
      simp [hi]
    · simp [Pi.single_apply, h0, hji, hz j h0 hji]

/-- The n coordinate-pencil hyperplanes have exactly their expected affine point
as common intersection. This gives the global reconstruction, not just a plane restriction. -/
theorem point_forced_by_pencils (p : Point K n) (t : Coordinates K n) (ht : t 0 = 1)
    (h : ∀ (i : Fin (n + 1)) (hi : i ≠ 0), Incident p (pencilHyperplane i hi (t i))) :
    p = Projectivization.mk K t (by
      intro hz
      have := congr_fun hz 0
      simp [ht] at this) := by
  have heq : ∀ i, p.rep i = t i * p.rep 0 := by
    intro i
    by_cases hi : i = 0
    · simp [hi, ht]
    · exact (pencilHyperplane_incident p i hi (t i)).mp (h i hi)
  rw [← Projectivization.mk_rep p]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
  refine ⟨p.rep 0, ?_⟩
  funext i
  simpa [mul_comm] using (heq i).symm

end Erdos85.IncidenceRepair

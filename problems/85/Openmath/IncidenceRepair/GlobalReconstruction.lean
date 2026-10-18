import Openmath.IncidenceRepair.ChartCoherence
import Openmath.IncidenceRepair.SharedPencil
import Openmath.IncidenceRepair.AffineGeometry
import Openmath.IncidenceRepair.CoordinateReconstruction
import Openmath.IncidenceRepair.CanonicalCharts
import Openmath.IncidenceRepair.WeightedPlaneTheorem
import Openmath.IncidenceRepair.ProjectiveCoarseRepair

/-! Actual global reconstruction from the n coordinate pencils. -/
noncomputable section
open scoped BigOperators
namespace Erdos85.IncidenceRepair
attribute [local instance] Classical.propDecidable
variable {K L : Type*} [Field K] [Fintype K] [Field L] {n : ℕ}

def pencilProperSet (ψ : Hyperplane K n → Hyperplane L n) (i : Fin n) : Finset K :=
  Finset.univ.filter (globalProper ψ i.succ (Fin.succ_ne_zero i))

def pencilCoordinate (ψ : Hyperplane K n → Hyperplane L n) (i : Fin n) : K → L :=
  globalCoordinate ψ i.succ (Fin.succ_ne_zero i)

def badPencilFlags (φ : Point K n → Point L n)
    (ψ : Hyperplane K n → Hyperplane L n) : Finset (Fin n → K) :=
  Finset.univ.filter fun x => ∃ i : Fin n,
    ¬ Incident (φ (affinePoint x)) (ψ (pencilHyperplane i.succ (Fin.succ_ne_zero i) (x i)))

def pencilFlagSum (φ : Point K n → Point L n)
    (ψ : Hyperplane K n → Hyperplane L n) : ℝ :=
  ∑ x : Fin n → K, ∑ i : Fin n,
    if Incident (φ (affinePoint x)) (ψ (pencilHyperplane i.succ (Fin.succ_ne_zero i) (x i)))
    then 0 else 1

def pencilGamma (φ : Point K n → Point L n)
    (ψ : Hyperplane K n → Hyperplane L n) : ℝ :=
  pencilFlagSum φ ψ / (Fintype.card K : ℝ)^n

lemma pencilFlagSum_nonneg (φ : Point K n → Point L n)
    (ψ : Hyperplane K n → Hyperplane L n) : 0 ≤ pencilFlagSum φ ψ := by
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> norm_num

lemma pencilGamma_nonneg (φ : Point K n → Point L n)
    (ψ : Hyperplane K n → Hyperplane L n) : 0 ≤ pencilGamma φ ψ :=
  div_nonneg (pencilFlagSum_nonneg φ ψ) (by positivity)

lemma badPencilFlags_card_le (φ : Point K n → Point L n)
    (ψ : Hyperplane K n → Hyperplane L n) :
    ((badPencilFlags φ ψ).card : ℝ) ≤ pencilGamma φ ψ*(Fintype.card K : ℝ)^n := by
  have hq : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  rw [pencilGamma, div_mul_cancel₀ _ (ne_of_gt (pow_pos hq n))]
  unfold badPencilFlags pencilFlagSum
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_le_sum
  intro x _
  split_ifs with hx
  · obtain ⟨i, hi⟩ := hx
    calc
      (1 : ℝ) = if Incident (φ (affinePoint x))
          (ψ (pencilHyperplane i.succ (Fin.succ_ne_zero i) (x i))) then 0 else 1 := by
        rw [if_neg hi]
      _ ≤ _ := Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin n => if Incident (φ (affinePoint x))
          (ψ (pencilHyperplane j.succ (Fin.succ_ne_zero j) (x j))) then (0 : ℝ) else 1)
        (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
  · exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

/-- Actual geometry supplies reconstruction from preserved proper coordinate pencils. -/
theorem reconstruct_of_good_pencils (φ : Point K n → Point L n)
    (ψ : Hyperplane K n → Hyperplane L n) (x : Fin n → K)
    (hflags : x ∉ badPencilFlags φ ψ)
    (hproper : ∀ i, x i ∈ pencilProperSet ψ i) :
    φ (affinePoint x) = affinePoint (fun i => pencilCoordinate ψ i (x i)) := by
  have hgood (i : Fin n) : Incident (φ (affinePoint x))
      (ψ (pencilHyperplane i.succ (Fin.succ_ne_zero i) (x i))) := by
    by_contra hi
    exact hflags (Finset.mem_filter.mpr ⟨Finset.mem_univ x, ⟨i, hi⟩⟩)
  have hp (i : Fin n) : globalProper ψ i.succ (Fin.succ_ne_zero i) (x i) :=
    (Finset.mem_filter.mp (hproper i)).2
  apply point_forced_by_pencils (φ (affinePoint x))
    (affineVector (fun i => pencilCoordinate ψ i (x i))) (by simp [affineVector])
  intro i hi
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi
  have hg := hgood j
  rw [globalCoordinate_image ψ _ _ (x j) (hp j)] at hg
  simpa only [affineVector, Fin.cons_succ, pencilCoordinate] using hg

/-- All geometric reconstruction assumptions are discharged here; only the
coordinate deficit budgets remain as explicit inputs. -/
theorem global_affine_reconstruction (hn : 0 < n)
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (σ : K →+* L) (η E : ℝ) (hη : 0 ≤ η)
    (hE : pencilGamma φ ψ + η ≤ E)
    (hproper : (∑ i : Fin n, ((Finset.univ \ pencilProperSet ψ i).card : ℝ)) ≤
      34*η*Fintype.card K)
    (hscalar : (∑ i : Fin n, ((Finset.univ.filter
      (fun a => pencilCoordinate ψ i a ≠ σ a)).card : ℝ)) ≤
      936*η*Fintype.card K) :
    ((Finset.univ.filter (fun x : Fin n → K =>
      φ (affinePoint x) ≠ affinePoint (fun i => σ (x i)))).card : ℝ) ≤
      971*E*(Fintype.card K : ℝ)^n := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hh := coordinate_reconstruction_numeric_bound
    (fun x => φ (affinePoint x)) (affinePoint (K := L))
    (pencilCoordinate ψ) (fun x => σ x) (pencilProperSet ψ) (badPencilFlags φ ψ)
    (reconstruct_of_good_pencils φ ψ)
    (pencilGamma φ ψ) η E (pencilGamma_nonneg φ ψ) hη hE
    (by simpa using badPencilFlags_card_le φ ψ) hproper hscalar
  simpa using hh.1.trans hh.2

/-- Coordinate enumeration: the common first coordinate, then n−1 chart coordinates. -/
def chartCoordinateIndex (hn : 2 ≤ n) : Option (Fin (n-1)) ≃ Fin n :=
  (finSuccEquiv (n-1)).symm.trans (finCongr (by omega))

lemma chartCoordinateIndex_first (hn : 2 ≤ n) (j : Fin (n-1)) :
    (chartCoordinateIndex hn none).succ = canonicalChart n hn j 0 := by
  apply Fin.ext
  rfl

lemma chartCoordinateIndex_other (hn : 2 ≤ n) (j : Fin (n-1)) :
    (chartCoordinateIndex hn (some j)).succ = canonicalChart n hn j 1 := by
  apply Fin.ext
  rfl

omit [Fintype K] in
lemma canonical_coordX (hn : 2 ≤ n) (ψ : Hyperplane K n → Hyperplane L n)
    (j : Fin (n-1)) (x : K) :
    Plane.coordX (inducedHyperplanes (canonicalChart n hn j) ψ) x =
      pencilCoordinate ψ (chartCoordinateIndex hn none) x := by
  rw [coordX_shared _ (canonicalChart_two n hn j)]
  unfold pencilCoordinate
  simp only [chartCoordinateIndex_first hn j]

omit [Fintype K] in
lemma canonical_coordY (hn : 2 ≤ n) (ψ : Hyperplane K n → Hyperplane L n)
    (j : Fin (n-1)) (x : K) :
    Plane.coordY (inducedHyperplanes (canonicalChart n hn j) ψ) x =
      pencilCoordinate ψ (chartCoordinateIndex hn (some j)) x := by
  rw [coordY_shared _ (canonicalChart_two n hn j)]
  unfold pencilCoordinate
  simp only [chartCoordinateIndex_other hn j]

lemma canonical_properX (hn : 2 ≤ n) (ψ : Hyperplane K n → Hyperplane L n)
    (j : Fin (n-1)) (x : K) :
    Plane.ProperX (inducedHyperplanes (canonicalChart n hn j) ψ) x ↔
      x ∈ pencilProperSet ψ (chartCoordinateIndex hn none) := by
  rw [properX_shared _ (canonicalChart_two n hn j)]
  simp only [pencilProperSet, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [chartCoordinateIndex_first hn j]

lemma canonical_properY (hn : 2 ≤ n) (ψ : Hyperplane K n → Hyperplane L n)
    (j : Fin (n-1)) (x : K) :
    Plane.ProperY (inducedHyperplanes (canonicalChart n hn j) ψ) x ↔
      x ∈ pencilProperSet ψ (chartCoordinateIndex hn (some j)) := by
  rw [properY_shared _ (canonicalChart_two n hn j)]
  simp only [pencilProperSet, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [chartCoordinateIndex_other hn j]

omit [Field K] in
lemma properSet_deficit (p : Finset K) :
    ((Finset.univ \ p).card : ℝ) = count (fun x => x ∉ p) := by
  rw [Chart.count_eq_card]
  congr 2
  ext x
  simp

/-- For the identity target normalization, vector-chart errors equal the actual
non-infinity projective-point mismatch count used by the coarse repair theorem. -/
lemma affineErrors_eq_vector_count [Finite L]
    (φ : Point K n → Point L n) (σ : K →+* L) :
    affineErrors φ σ (LinearEquiv.refl L (Coordinates L n)) =
      (Finset.univ.filter (fun x : Fin n → K =>
        φ (affinePoint x) ≠ affinePoint (fun i => σ (x i)))).card := by
  rw [affineErrors, affine_restriction_card]
  simp only [pointEmbedding_affine, Nat.card_eq_fintype_card, Fintype.card_subtype]

def normalizedChartPoints (hn : 2 ≤ n) (φ : Point K n → Point L n)
    (j : Fin (n-1)) : Point K 2 → Point L 2 :=
  fun p => chartRestrictPoint (canonicalChart n hn j) (φ (chartPoint (canonicalChart n hn j) p))

/-- Full normalized reconstruction from the actual protected chart maps and their
weighted original-flag majorants. The field embedding is constructed here. -/
theorem normalized_weighted_reconstruction [Finite L] (hn : 2 ≤ n)
    (φ : Point K n → Point L n) (ψ : Hyperplane K n → Hyperplane L n)
    (b : Fin (n-1) → Point K 2 → Hyperplane K 2 → ℝ)
    (hprotected : ∀ j, Plane.Protected (normalizedChartPoints hn φ j)
      (inducedHyperplanes (canonicalChart n hn j) ψ))
    (hb : ∀ j p H, 0 ≤ b j p H)
    (hbad : ∀ j p H, Incident p H →
      ¬ Incident (normalizedChartPoints hn φ j p)
        (inducedHyperplanes (canonicalChart n hn j) ψ H) → 1 ≤ b j p H)
    (hsmall : (∑ j, Plane.cost (b j)) ≤ 1/10000000)
    (E : ℝ) (hE : pencilGamma φ ψ + (∑ j, Plane.cost (b j)) ≤ E) :
    ∃ σ : K →+* L,
      (affineErrors φ σ (LinearEquiv.refl L (Coordinates L n)) : ℝ) ≤
        971*E*(Fintype.card K : ℝ)^n := by
  classical
  let j₀ : Fin (n-1) := ⟨0, by omega⟩
  let η : Fin (n-1) → ℝ := fun j => Plane.cost (b j)
  have hη (j : Fin (n-1)) : 0 ≤ η j := Plane.cost_nonneg (hb j)
  have hj (j : Fin (n-1)) : η j ≤ ∑ k, η k :=
    Finset.single_le_sum (fun k _ => hη k) (Finset.mem_univ j)
  have hplane (j : Fin (n-1)) := Plane.weighted_plane
    (normalizedChartPoints hn φ j) (inducedHyperplanes (canonicalChart n hn j) ψ)
    (hprotected j) (b j) (hb j) (hbad j) ((hj j).trans hsmall)
  choose σ hσ using fun j => (hplane j).2.2
  let e := chartCoordinateIndex hn
  let f₁ := pencilCoordinate ψ (e none)
  let f := fun j => pencilCoordinate ψ (e (some j))
  let p₁ := pencilProperSet ψ (e none)
  let p := fun j => pencilProperSet ψ (e (some j))
  have hf₁ (j : Fin (n-1)) : count (fun x => f₁ x ≠ σ j x) ≤
      288*η j*Fintype.card K := by
    simpa only [canonical_coordX] using (hσ j).1
  have hf (j : Fin (n-1)) : count (fun x => f j x ≠ σ j x) ≤
      648*η j*Fintype.card K := by
    simpa only [canonical_coordY] using (hσ j).2.1
  have hp₁ : ((Finset.univ \ p₁).card : ℝ) ≤ 17*η j₀*Fintype.card K := by
    rw [properSet_deficit]
    simpa only [canonical_properX] using (hplane j₀).1
  have hp (j : Fin (n-1)) : ((Finset.univ \ p j).card : ℝ) ≤
      17*η j*Fintype.card K := by
    rw [properSet_deficit]
    simpa only [canonical_properY] using (hplane j).2.1
  have hbud := Chart.coherent_coordinate_budget j₀ σ f₁ f p₁ p η hη hsmall hf₁ hp₁ hp hf
  have hpfunc : Chart.properCoordinates p₁ p = fun i => pencilProperSet ψ (e i) := by
    funext i
    cases i <;> rfl
  have hffunc : Chart.coordinates f₁ f = fun i => pencilCoordinate ψ (e i) := by
    funext i
    cases i <;> rfl
  have hproper : (∑ i : Fin n, ((Finset.univ \ pencilProperSet ψ i).card : ℝ)) ≤
      34*(∑ j, η j)*Fintype.card K := by
    have h := hbud.2.1
    rw [hpfunc] at h
    rw [Equiv.sum_comp e (fun i : Fin n => ((Finset.univ \ pencilProperSet ψ i).card : ℝ))] at h
    exact h
  have hscalar : (∑ i : Fin n, ((Finset.univ.filter
      (fun a => pencilCoordinate ψ i a ≠ σ j₀ a)).card : ℝ)) ≤
      936*(∑ j, η j)*Fintype.card K := by
    have h := hbud.2.2
    rw [hffunc] at h
    rw [Equiv.sum_comp e (fun i : Fin n => ((Finset.univ.filter
      (fun a => pencilCoordinate ψ i a ≠ σ j₀ a)).card : ℝ))] at h
    exact h
  refine ⟨σ j₀, ?_⟩
  rw [affineErrors_eq_vector_count]
  exact global_affine_reconstruction (by omega) φ ψ (σ j₀) (∑ j, η j) E
    (Finset.sum_nonneg (fun j _ => hη j)) hE hproper hscalar

end Erdos85.IncidenceRepair

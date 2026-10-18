import Openmath.IncidenceRepair.WeightedPlane
import Openmath.IncidenceRepair.PlaneCostCounting
import Openmath.IncidenceRepair.PlaneReciprocalBudget
import Openmath.IncidenceRepair.PlaneSupportBounds

noncomputable section
namespace Erdos85.IncidenceRepair.Plane
open Finset
variable {K L : Type*} [Field K] [Field L] [Fintype K] [DecidableEq K]

 def goodX (ψ : Hyperplane K 2 → Hyperplane L 2) : Finset K := by
  classical
  exact univ.filter (ProperX ψ)
 def goodY (ψ : Hyperplane K 2 → Hyperplane L 2) : Finset K := by
  classical
  exact univ.filter (ProperY ψ)
 def badX (φ : Point K 2 → Point L 2) (ψ : Hyperplane K 2 → Hyperplane L 2) : Finset K := by
  classical
  exact univ.filter fun t => ¬ Incident (φ V) (ψ (vertical t))
 def badY (φ : Point K 2 → Point L 2) (ψ : Hyperplane K 2 → Hyperplane L 2) : Finset K := by
  classical
  exact univ.filter fun t => ¬ Incident (φ U) (ψ (horizontal t))
 def badOrigin (φ : Point K 2 → Point L 2) (ψ : Hyperplane K 2 → Hyperplane L 2) : Finset K := by
  classical
  exact univ.filter fun a => a ≠ 0 ∧ ¬ Incident (φ (affine 0 0)) (ψ (slope a 0))
 def badCoordinates (φ : Point K 2 → Point L 2) (ψ : Hyperplane K 2 → Hyperplane L 2) : Finset (K × K) := by
  classical
  exact univ.filter fun p => ¬ Incident (φ (affine p.1 p.2)) (ψ (vertical p.1)) ∨
    ¬ Incident (φ (affine p.1 p.2)) (ψ (horizontal p.2))
 def badPencil (φ : Point K 2 → Point L 2) (ψ : Hyperplane K 2 → Hyperplane L 2) : Finset (K × K) := by
  classical
  exact univ.filter fun p => p.1 ≠ 0 ∧
    ¬ Incident (φ (affine p.2 (p.1*p.2))) (ψ (slope p.1 0))
 def markedPoints (φ : Point K 2 → Point L 2) (ψ : Hyperplane K 2 → Hyperplane L 2) : Finset (K × K) := by
  classical
  exact badCoordinates φ ψ ∪ (badPencil φ ψ).image fun p => (p.2, p.1*p.2)

 theorem collapseX_iff (φ : Point K 2 → Point L 2) (ψ : Hyperplane K 2 → Hyperplane L 2)
    (hp : Protected φ ψ) (t : K) :
    t ∈ univ \ (goodX ψ ∪ badX φ ψ) ↔ ψ (vertical t) = infinity := by
  classical
  simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or, goodX, badX,
    mem_filter, mem_univ, true_and, not_not]
  rw [hp.point_V, properX_iff]
  constructor
  · rintro ⟨hn, hg⟩
    by_contra hi
    exact hn ⟨hg, hi⟩
  · intro hi
    simp [hi, Incident, V, horizontal, infinity, Projectivization.orthogonal_mk, dotProduct, Fin.sum_univ_succ]

 theorem collapseY_iff (φ : Point K 2 → Point L 2) (ψ : Hyperplane K 2 → Hyperplane L 2)
    (hp : Protected φ ψ) (t : K) :
    t ∈ univ \ (goodY ψ ∪ badY φ ψ) ↔ ψ (horizontal t) = infinity := by
  classical
  simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or, goodY, badY,
    mem_filter, mem_univ, true_and, not_not]
  rw [hp.point_U, properY_iff]
  constructor
  · rintro ⟨hn, hg⟩
    by_contra hi
    exact hn ⟨hg, hi⟩
  · intro hi
    simp [hi, Incident, U, vertical, infinity, Projectivization.orthogonal_mk, dotProduct, Fin.sum_univ_succ]

 theorem unmarked_good (φ : Point K 2 → Point L 2) (ψ : Hyperplane K 2 → Hyperplane L 2)
    (a t : K) (ha : a ≠ 0) (hm : (t, a*t) ∉ markedPoints φ ψ) :
    Incident (φ (affine t (a*t))) (ψ (vertical t)) ∧
    Incident (φ (affine t (a*t))) (ψ (horizontal (a*t))) ∧
    Incident (φ (affine t (a*t))) (ψ (slope a 0)) := by
  classical
  have hc : (t, a*t) ∉ badCoordinates φ ψ := fun hh => hm (mem_union_left _ hh)
  have hvh : Incident (φ (affine t (a*t))) (ψ (vertical t)) ∧
      Incident (φ (affine t (a*t))) (ψ (horizontal (a*t))) := by
    simpa [badCoordinates] using hc
  refine ⟨hvh.1, hvh.2, ?_⟩
  by_contra hl
  apply hm
  apply mem_union_right
  exact mem_image.mpr ⟨(a,t), by simpa [badPencil] using And.intro ha hl, rfl⟩

theorem protected_zero_mem (φ : Point K 2 → Point L 2) (ψ : Hyperplane K 2 → Hyperplane L 2)
    (hp : Protected φ ψ) : (0 : K) ∈ goodX ψ ∧ (0 : K) ∈ goodY ψ := by
  classical
  obtain ⟨hx, _, hy, _⟩ := protected_values φ ψ hp
  exact ⟨by simpa [goodX] using hx, by simpa [goodY] using hy⟩

theorem pencil_marked_inclusions (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) (hp : Protected φ ψ)
    (a : K) (ha : a ≠ 0) (hbad : a ∉ badOrigin φ ψ) :
    ((goodX ψ).filter fun t => a * t ∈ univ \ (goodY ψ ∪ badY φ ψ)) ⊆
        slopeErrors (markedPoints φ ψ) a ∨
    ((univ \ (goodX ψ ∪ badX φ ψ)).filter fun t => a * t ∈ goodY ψ) ⊆
        slopeErrors (markedPoints φ ψ) a := by
  classical
  have hO : Incident (φ (affine 0 0)) (ψ (slope a 0)) := by
    simpa [badOrigin, ha] using hbad
  have hz := protected_zero_mem φ ψ hp
  by_cases hR : ((goodX ψ).filter fun t => a * t ∈ univ \ (goodY ψ ∪ badY φ ψ)) ⊆
      slopeErrors (markedPoints φ ψ) a
  · exact Or.inl hR
  · right
    obtain ⟨t, htR, htE⟩ := not_subset.mp hR
    obtain ⟨htX, htY⟩ := mem_filter.mp htR
    have htX' : ProperX ψ t := by simpa [goodX] using htX
    have htY' := (collapseY_iff φ ψ hp (a*t)).mp htY
    have ht0 : t ≠ 0 := by
      intro he
      subst t
      have h := (mem_sdiff.mp htY).2
      exact h (mem_union_left _ (by simpa using hz.2))
    have htn : (t,a*t) ∉ markedPoints φ ψ := by
      simpa [slopeErrors, ht0] using htE
    obtain ⟨htv, hth, htl⟩ := unmarked_good φ ψ a t ha htn
    intro u huS
    obtain ⟨huX, huY⟩ := mem_filter.mp huS
    have huX' := (collapseX_iff φ ψ hp u).mp huX
    have huY' : ProperY ψ (a*u) := by simpa [goodY] using huY
    have hu0 : u ≠ 0 := by
      intro he
      subst u
      exact (mem_sdiff.mp huX).2 (mem_union_left _ hz.1)
    have hum : (u,a*u) ∈ markedPoints φ ψ := by
      by_contra hun
      obtain ⟨huv, huh, hul⟩ := unmarked_good φ ψ a u ha hun
      exact pencil_mixed_obstruction φ ψ hp a t u htX' htY' huX' huY'
        htv hth huv huh htl hul hO
    simpa [slopeErrors] using And.intro hu0 hum

/-- A pointwise majorant is required only on actual original flags. -/
def FlagMajorant (φ : Point K 2 → Point L 2) (ψ : Hyperplane K 2 → Hyperplane L 2)
    (b : Point K 2 → Hyperplane K 2 → ℝ) : Prop :=
  ∀ p H, Incident p H → ¬ Incident (φ p) (ψ H) → 1 ≤ b p H

theorem badX_bound (φ : Point K 2 → Point L 2) (ψ : Hyperplane K 2 → Hyperplane L 2)
    (b : Point K 2 → Hyperplane K 2 → ℝ) (hb : ∀ p H, 0 ≤ b p H)
    (hm : FlagMajorant φ ψ b) :
    ((badX φ ψ).card : ℝ) ≤ ∑ t, b V (vertical t) := by
  classical
  apply card_filter_le_sum_majorant
  · intro t _; exact hb _ _
  · intro t _ ht; exact hm _ _ (V_on_vertical t) ht

theorem badY_bound (φ : Point K 2 → Point L 2) (ψ : Hyperplane K 2 → Hyperplane L 2)
    (b : Point K 2 → Hyperplane K 2 → ℝ) (hb : ∀ p H, 0 ≤ b p H)
    (hm : FlagMajorant φ ψ b) :
    ((badY φ ψ).card : ℝ) ≤ ∑ t, b U (horizontal t) := by
  classical
  apply card_filter_le_sum_majorant
  · intro t _; exact hb _ _
  · intro t _ ht; exact hm _ _ (U_on_horizontal t) ht

theorem proper_card_close (φ : Point K 2 → Point L 2) (ψ : Hyperplane K 2 → Hyperplane L 2)
    (hp : Protected φ ψ) (b : Point K 2 → Hyperplane K 2 → ℝ)
    (hb : ∀ p H, 0 ≤ b p H) (hm : FlagMajorant φ ψ b) :
    |((goodX ψ).card : ℝ) - (goodY ψ).card| ≤ cost b * Fintype.card K := by
  classical
  let M := univ.filter fun t => ¬ (ProperX ψ t ↔ ProperY ψ t)
  have hM : (M.card : ℝ) ≤ ∑ t, (b V (vertical t) + b U (horizontal t) +
      b (affine t t) (vertical t) + b (affine t t) (horizontal t) +
      b (affine t t) (slope 1 0)) := by
    apply card_filter_le_sum_majorant
    · intro t _; exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (hb _ _) (hb _ _)) (hb _ _)) (hb _ _)) (hb _ _)
    · intro t _ ht
      have h0 := hb V (vertical t)
      have h1 := hb U (horizontal t)
      have h2 := hb (affine t t) (vertical t)
      have h3 := hb (affine t t) (horizontal t)
      have h4 := hb (affine t t) (slope 1 0)
      by_contra! hsum
      have hv : Incident (φ V) (ψ (vertical t)) := by
        by_contra hn
        have hh := hm _ _ (V_on_vertical t) hn
        linarith
      have hu : Incident (φ U) (ψ (horizontal t)) := by
        by_contra hn
        have hh := hm _ _ (U_on_horizontal t) hn
        linarith
      have hcv : Incident (φ (affine t t)) (ψ (vertical t)) := by
        by_contra hn
        have hh := hm _ _ (by simp) hn
        linarith
      have hch : Incident (φ (affine t t)) (ψ (horizontal t)) := by
        by_contra hn
        have hh := hm _ _ (by simp) hn
        linarith
      have hcd : Incident (φ (affine t t)) (ψ (slope 1 0)) := by
        by_contra hn
        have hh := hm _ _ (by simp) hn
        linarith
      exact ht (proper_agree_of_diagonal_good φ ψ hp t hv hu hcv hch hcd)
  have hx : goodX ψ ⊆ goodY ψ ∪ M := by
    intro t ht
    simp only [goodX, goodY, mem_filter, mem_univ, true_and, mem_union, M] at *
    tauto
  have hy : goodY ψ ⊆ goodX ψ ∪ M := by
    intro t ht
    simp only [goodX, goodY, mem_filter, mem_univ, true_and, mem_union, M] at *
    tauto
  have hxc := (card_le_card hx).trans (card_union_le _ _)
  have hyc := (card_le_card hy).trans (card_union_le _ _)
  have hxr : ((goodX ψ).card : ℝ) ≤ (goodY ψ).card + M.card := by exact_mod_cast hxc
  have hyr : ((goodY ψ).card : ℝ) ≤ (goodX ψ).card + M.card := by exact_mod_cast hyc
  have hbudget := sum_le_of_avg1_le (close_budget hb)
  rw [abs_le]
  constructor <;> linarith

theorem origin_bound (φ : Point K 2 → Point L 2) (ψ : Hyperplane K 2 → Hyperplane L 2)
    (b : Point K 2 → Hyperplane K 2 → ℝ) (hb : ∀ p H, 0 ≤ b p H)
    (hm : FlagMajorant φ ψ b) :
    ((badOrigin φ ψ).card : ℝ) ≤ ∑ a, if a ≠ 0 then b (affine 0 0) (slope a 0) else 0 := by
  classical
  apply card_filter_le_sum_majorant
  · intro a _; split_ifs <;> first | exact hb _ _ | exact le_refl 0
  · intro a _ ha
    rw [if_pos ha.1]
    exact hm _ _ (by simp) ha.2

theorem coordinates_bound (φ : Point K 2 → Point L 2) (ψ : Hyperplane K 2 → Hyperplane L 2)
    (b : Point K 2 → Hyperplane K 2 → ℝ) (hb : ∀ p H, 0 ≤ b p H)
    (hm : FlagMajorant φ ψ b) :
    ((badCoordinates φ ψ).card : ℝ) ≤ ∑ x, ∑ y,
      (b (affine x y) (vertical x) + b (affine x y) (horizontal y)) := by
  classical
  rw [← Fintype.sum_prod_type (fun p : K × K => b (affine p.1 p.2) (vertical p.1) + b (affine p.1 p.2) (horizontal p.2))]
  apply card_filter_le_sum_majorant
  · intro p _; exact add_nonneg (hb _ _) (hb _ _)
  · intro p _ hp
    rcases hp with hv | hh
    · have h := hm _ _ (by simp) hv
      linarith [hb (affine p.1 p.2) (horizontal p.2)]
    · have h := hm _ _ (by simp) hh
      linarith [hb (affine p.1 p.2) (vertical p.1)]

theorem pencil_bound (φ : Point K 2 → Point L 2) (ψ : Hyperplane K 2 → Hyperplane L 2)
    (b : Point K 2 → Hyperplane K 2 → ℝ) (hb : ∀ p H, 0 ≤ b p H)
    (hm : FlagMajorant φ ψ b) :
    ((badPencil φ ψ).card : ℝ) ≤ ∑ a, ∑ t,
      if a ≠ 0 then b (affine t (a*t)) (slope a 0) else 0 := by
  classical
  rw [← Fintype.sum_prod_type (fun p : K × K => if p.1 ≠ 0 then b (affine p.2 (p.1*p.2)) (slope p.1 0) else 0)]
  apply card_filter_le_sum_majorant
  · intro p _; split_ifs <;> first | exact hb _ _ | exact le_refl 0
  · intro p _ hp
    rw [if_pos hp.1]
    exact hm _ _ (by simp) hp.2

theorem marked_card_bound (φ : Point K 2 → Point L 2) (ψ : Hyperplane K 2 → Hyperplane L 2) :
    (markedPoints φ ψ).card ≤ (badCoordinates φ ψ).card + (badPencil φ ψ).card := by
  classical
  exact (card_union_le _ _).trans (Nat.add_le_add_left card_image_le _)

def reciprocalBad (ψ : Hyperplane K 2 → Hyperplane L 2) : Finset K := by
  classical
  exact univ.filter fun a => a ≠ 0 ∧ ψ (horizontal a) = infinity ∧ ψ (vertical a⁻¹) = infinity

theorem reciprocal_cover_actual (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) (hp : Protected φ ψ) :
    Fintype.card K + 1 ≤ (goodX ψ).card + (goodY ψ).card +
      (badX φ ψ).card + (badY φ ψ).card + (reciprocalBad ψ).card := by
  classical
  obtain ⟨hx, hy⟩ := protected_zero_mem φ ψ hp
  apply reciprocal_coverage (goodX ψ) (goodY ψ) (badX φ ψ) (badY φ ψ)
    (reciprocalBad ψ) hx hy
  intro a ha
  by_cases hY : a ∈ goodY ψ
  · exact Or.inl hY
  by_cases hBY : a ∈ badY φ ψ
  · exact Or.inr (Or.inl hBY)
  by_cases hX : a⁻¹ ∈ goodX ψ
  · exact Or.inr (Or.inr (Or.inl hX))
  by_cases hBX : a⁻¹ ∈ badX φ ψ
  · exact Or.inr (Or.inr (Or.inr (Or.inl hBX)))
  right; right; right; right
  have hy' := (collapseY_iff φ ψ hp a).mp (by simp [hY,hBY])
  have hx' := (collapseX_iff φ ψ hp a⁻¹).mp (by simp [hX,hBX])
  simpa [reciprocalBad] using And.intro ha (And.intro hy' hx')

theorem reciprocal_bad_bound (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) (hp : Protected φ ψ)
    (b : Point K 2 → Hyperplane K 2 → ℝ) (hb : ∀ p H, 0 ≤ b p H)
    (hm : FlagMajorant φ ψ b) :
    ((reciprocalBad ψ).card : ℝ) ≤ ∑ a, if a ≠ 0 then
      b (affine 0 0) (slope a 0) + b (affine 1 a) (vertical 1) +
      b (affine 1 a) (horizontal a) + b (affine a⁻¹ 1) (vertical a⁻¹) +
      b (affine a⁻¹ 1) (horizontal 1) + b (affine 1 a) (slope a 0) +
      b (affine a⁻¹ 1) (slope a 0) else 0 := by
  classical
  apply card_filter_le_sum_majorant
  · intro a _
    split_ifs
    · exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
        (hb _ _) (hb _ _)) (hb _ _)) (hb _ _)) (hb _ _)) (hb _ _)) (hb _ _)
    · exact le_refl 0
  · intro a _ ha
    rw [if_pos ha.1]
    have h0 := hb (affine 0 0) (slope a 0)
    have h1 := hb (affine 1 a) (vertical 1)
    have h2 := hb (affine 1 a) (horizontal a)
    have h3 := hb (affine a⁻¹ 1) (vertical a⁻¹)
    have h4 := hb (affine a⁻¹ 1) (horizontal 1)
    have h5 := hb (affine 1 a) (slope a 0)
    have h6 := hb (affine a⁻¹ 1) (slope a 0)
    by_contra! hs
    have hO : Incident (φ (affine 0 0)) (ψ (slope a 0)) := by
      by_contra hn
      have hh := hm _ _ (by simp) hn
      linarith
    have hpv : Incident (φ (affine 1 a)) (ψ (vertical 1)) := by
      by_contra hn
      have hh := hm _ _ (by simp) hn
      linarith
    have hph : Incident (φ (affine 1 a)) (ψ (horizontal a)) := by
      by_contra hn
      have hh := hm _ _ (by simp) hn
      linarith
    have hqv : Incident (φ (affine a⁻¹ 1)) (ψ (vertical a⁻¹)) := by
      by_contra hn
      have hh := hm _ _ (by simp) hn
      linarith
    have hqh : Incident (φ (affine a⁻¹ 1)) (ψ (horizontal 1)) := by
      by_contra hn
      have hh := hm _ _ (by simp) hn
      linarith
    have hpl : Incident (φ (affine 1 a)) (ψ (slope a 0)) := by
      by_contra hn
      have hh := hm _ _ (by simp) hn
      linarith
    have hql : Incident (φ (affine a⁻¹ 1)) (ψ (slope a 0)) := by
      by_contra hn
      have hh := hm _ _ (by simp [ha.1]) hn
      linarith
    exact reciprocal_obstruction φ ψ hp a ha.2.1 ha.2.2 hpv hph hqv hqh hpl hql hO

/-- The support estimates of the weighted protected-plane lemma, derived from
actual projective incidences and the exact twenty-four-family majorant cost. -/
theorem protected_support_bounds (φ : Point K 2 → Point L 2)
    (ψ : Hyperplane K 2 → Hyperplane L 2) (hp : Protected φ ψ)
    (b : Point K 2 → Hyperplane K 2 → ℝ) (hb : ∀ p H, 0 ≤ b p H)
    (hm : FlagMajorant φ ψ b) (hsmall : cost b ≤ 1 / 12) :
    (Fintype.card K : ℝ) - (goodX ψ).card ≤ 17 * cost b * Fintype.card K ∧
    (Fintype.card K : ℝ) - (goodY ψ).card ≤ 16 * cost b * Fintype.card K := by
  classical
  obtain ⟨hx0, hx1, hy0, hy1, _⟩ := protected_values φ ψ hp
  have hX0 : (0 : K) ∈ goodX ψ := by simpa [goodX] using hx0
  have hY0 : (0 : K) ∈ goodY ψ := by simpa [goodY] using hy0
  have hX2 : 2 ≤ (goodX ψ).card := by
    have hs : ({0,1} : Finset K) ⊆ goodX ψ := by
      intro t ht
      rcases (by simpa only [mem_insert, mem_singleton] using ht : t = 0 ∨ t = 1) with ht | ht <;> subst t
      · exact hX0
      · simpa [goodX] using hx1
    simpa using card_le_card hs
  have hY2 : 2 ≤ (goodY ψ).card := by
    have hs : ({0,1} : Finset K) ⊆ goodY ψ := by
      intro t ht
      rcases (by simpa only [mem_insert, mem_singleton] using ht : t = 0 ∨ t = 1) with ht | ht <;> subst t
      · exact hY0
      · simpa [goodY] using hy1
    simpa using card_le_card hs
  have hq : 2 ≤ Fintype.card K := hX2.trans (card_le_univ _)
  have hq0 : (0 : ℝ) ≤ Fintype.card K := by positivity
  have hdis : Disjoint (goodY ψ) (badY φ ψ) := by
    apply disjoint_left.mpr
    intro t hyt hbt
    have hy : ProperY ψ t := by simpa [goodY] using hyt
    have hb' : ¬ Incident (φ U) (ψ (horizontal t)) := by simpa [badY] using hbt
    apply hb'
    rw [hp.point_U]
    exact ((properY_iff ψ t).mp hy).1
  have hBX := badX_bound φ ψ b hb hm
  have hBY := badY_bound φ ψ b hb hm
  have hanchor := badanchors_raw_budget hb
  simp only [sum_add_distrib] at hanchor
  have hanchors : ((badX φ ψ).card : ℝ) + (badY φ ψ).card ≤ cost b * Fintype.card K := by
    linarith
  have hcl := proper_card_close φ ψ hp b hb hm
  have him : |((goodX ψ).card : ℝ) - (goodY ψ).card| +
      (badX φ ψ).card + (badY φ ψ).card ≤ 2 * cost b * Fintype.card K := by linarith
  have hBY' : ((badY φ ψ).card : ℝ) ≤ cost b * Fintype.card K := by
    have hh : (0 : ℝ) ≤ (badX φ ψ).card := by positivity
    linarith
  have hO := origin_bound φ ψ b hb hm
  have hQ := coordinates_bound φ ψ b hb hm
  have hP := pencil_bound φ ψ b hb hm
  have hM : ((markedPoints φ ψ).card : ℝ) ≤ (badCoordinates φ ψ).card + (badPencil φ ψ).card := by
    exact_mod_cast marked_card_bound φ ψ
  have hOb := mul_le_mul_of_nonneg_left hO hq0
  have hpb : (∑ x, ∑ y, (b (affine x y) (vertical x) + b (affine x y) (horizontal y))) +
      (Fintype.card K : ℝ) * (∑ a, if a ≠ 0 then b (affine 0 0) (slope a 0) else 0) +
      (∑ a, ∑ t, if a ≠ 0 then b (affine t (a*t)) (slope a 0) else 0) ≤
      cost b * (Fintype.card K : ℝ)^2 := by
    have ho : (∑ a, if a ≠ 0 then b (affine 0 0) (slope a 0) else 0) =
        ∑ a, @ite ℝ (a ≠ 0) (Classical.propDecidable _) (b (affine 0 0) (slope a 0)) 0 := by
      apply sum_congr rfl
      intro a _
      by_cases ha : a = 0 <;> simp [ha]
    have hp' : (∑ a, ∑ t, if a ≠ 0 then b (affine t (a*t)) (slope a 0) else 0) =
        ∑ a, ∑ t, @ite ℝ (a ≠ 0) (Classical.propDecidable _) (b (affine t (a*t)) (slope a 0)) 0 := by
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro t _
      by_cases ha : a = 0 <;> simp [ha]
    rw [ho, hp']
    exact pencil_raw_budget hb
  have hcost : (Fintype.card K : ℝ) * (badOrigin φ ψ).card + (markedPoints φ ψ).card ≤
      cost b * (Fintype.card K : ℝ)^2 := by linarith
  have hR := reciprocal_bad_bound φ ψ hp b hb hm
  have hrb : (∑ a, b V (vertical a)) + (∑ a, b U (horizontal a)) +
      (∑ a, if a ≠ 0 then b (affine 0 0) (slope a 0) + b (affine 1 a) (vertical 1) +
        b (affine 1 a) (horizontal a) + b (affine a⁻¹ 1) (vertical a⁻¹) +
        b (affine a⁻¹ 1) (horizontal 1) + b (affine 1 a) (slope a 0) +
        b (affine a⁻¹ 1) (slope a 0) else 0) ≤ cost b * Fintype.card K := by
    have hr := reciprocal_raw_budget hb
    have he : (∑ a, reciprocalMajorant b a) = (∑ a, b V (vertical a)) + (∑ a, b U (horizontal a)) +
        (∑ a, if a ≠ 0 then b (affine 0 0) (slope a 0) + b (affine 1 a) (vertical 1) +
          b (affine 1 a) (horizontal a) + b (affine a⁻¹ 1) (vertical a⁻¹) +
          b (affine a⁻¹ 1) (horizontal 1) + b (affine 1 a) (slope a 0) +
          b (affine a⁻¹ 1) (slope a 0) else 0) := by
      rw [← sum_add_distrib, ← sum_add_distrib]
      apply sum_congr rfl
      intro a _
      by_cases ha : a = 0 <;> simp [reciprocalMajorant, ha]
    rwa [he] at hr
  have hcoverN := reciprocal_cover_actual φ ψ hp
  have hcoverR : (Fintype.card K : ℝ) + 1 ≤ (goodX ψ).card + (goodY ψ).card +
      (badX φ ψ).card + (badY φ ψ).card + (reciprocalBad ψ).card := by exact_mod_cast hcoverN
  have hcover : (Fintype.card K : ℝ) + 1 - cost b * Fintype.card K ≤
      (goodX ψ).card + (goodY ψ).card := by linarith
  exact finite_support_bounds (goodX ψ) (goodY ψ) (badX φ ψ) (badY φ ψ)
    (badOrigin φ ψ) (markedPoints φ ψ) (cost b) hq (cost_nonneg hb) hsmall
    hX0 hY0 hX2 hY2 hdis (pencil_marked_inclusions φ ψ hp) hcost him hBY' hcl hcover

end Erdos85.IncidenceRepair.Plane

import GeneralStar.Incidence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

open Finset SimpleGraph
namespace Erdos585.GeneralStar

def originalDegree (D : GraphData) (z : ℕ) : ℕ :=
  ∑ v, if D.label v=z then D.graph.degree v else 0

theorem originalDegree_label (D : GraphData) (v : D.Carrier) :
    originalDegree D (D.label v)=D.graph.degree v := by
  unfold originalDegree
  rw [sum_eq_single v]
  · simp
  · intro w _ hwv
    have hn : D.label w ≠ D.label v := fun h => hwv (D.labels.injective h)
    simp [hn]
  · simp

theorem seedSlot_outside (q : ℕ) (D : GraphData) (v : D.Carrier) (hv : v ∉ D.B) :
    seedSlot q D (D.label v)=0 := by
  apply sum_eq_zero
  intro w hw
  have hn : D.label w ≠ D.label v := by
    intro he
    exact hv (D.labels.injective he ▸ hw)
  simp [hn]

theorem original_plus_slot (q : ℕ) (D : GraphData) (hs : SeedHyp q D) (v : D.Carrier) :
    originalDegree D (D.label v)+seedSlot q D (D.label v) ≤ 2*(q-1) := by
  rw [originalDegree_label]
  by_cases hv : v ∈ D.B
  · rw [seedSlot_of_mem q D v hv]
    have hd := (hs.2.2.2.1 v).2
    omega
  · rw [seedSlot_outside q D v hv,Nat.add_zero]
    exact (hs.2.2.2.1 v).2

/-- Exact original degree including all future newborn incidences on the same label. -/
theorem transfer_degree (q : ℕ) (D : GraphData) (hq : 5 ≤ q) (hs : SeedHyp q D)
    (t : ℕ) (v : (transferState q D t).Carrier) :
    (transferState q D t).graph.degree v =
      (if (transferState q D t).label v < D.order then
        originalDegree D ((transferState q D t).label v) else q-1) +
        useCount q D t ((transferState q D t).label v) := by
  revert v
  induction t with
  | zero =>
    intro v
    change D.Carrier at v
    change D.graph.degree v = (if D.label v < D.order then originalDegree D (D.label v) else q-1)+useCount q D 0 (D.label v)
    have hb := D.labels.bounded v
    change D.label v < D.order at hb
    simp only [useCount,useSet,range_zero,filter_empty,card_empty,Nat.add_zero]
    rw [if_pos hb,originalDegree_label]
  | succ t ih =>
    change ∀ v : Option (transferState q D t).Carrier,
      (BqLowerFamily.extendGraph (transferState q D t).graph
        (transferNeighbors q D (transferState q D t) t)).degree v =
        (if ((transferState q D t).add (receivingA q t)
          (transferNeighbors q D (transferState q D t) t)).label v < D.order then
          originalDegree D (((transferState q D t).add (receivingA q t)
            (transferNeighbors q D (transferState q D t) t)).label v) else q-1) +
          useCount q D (t+1) (((transferState q D t).add (receivingA q t)
            (transferNeighbors q D (transferState q D t) t)).label v)
    intro w
    cases w with
    | none =>
      change _ = (if (transferState q D t).order < D.order then _ else q-1) +
        useCount q D (t+1) (transferState q D t).order
      have ho := transfer_order q D t
      rw [if_neg (by omega),BqLowerFamily.degree_none,transferNeighbors_card q D hq hs t,
        useCount_succ,useCount_before_label q D hq hs t _ (by omega)]
      have hn : (transferState q D t).order ∉ prescribedLabels q D t := by
        intro hp
        have := mem_range.mp (prescribedLabels_range q D hq hs t hp)
        omega
      simp [hn]
    | some w =>
      change _ = (if (transferState q D t).label w < D.order then _ else q-1)+
        useCount q D (t+1) ((transferState q D t).label w)
      rw [BqLowerFamily.degree_some,ih w,useCount_succ]
      have he : w ∈ transferNeighbors q D (transferState q D t) t ↔
          (transferState q D t).label w ∈ prescribedLabels q D t := by
        simp [transferNeighbors]
      change ((if (transferState q D t).label w < D.order then originalDegree D ((transferState q D t).label w) else q-1)+useCount q D t ((transferState q D t).label w) + if w ∈ transferNeighbors q D (transferState q D t) t then 1 else 0) = (if (transferState q D t).label w < D.order then originalDegree D ((transferState q D t).label w) else q-1)+(useCount q D t ((transferState q D t).label w)+if (transferState q D t).label w ∈ prescribedLabels q D t then 1 else 0)
      simp only [he]
      omega

theorem transfer_max (q : ℕ) (D : GraphData) (hq : 5 ≤ q) (hs : SeedHyp q D)
    (t : ℕ) : ∀ v, (transferState q D t).graph.degree v ≤ 2*(q-1) := by
  intro v
  rw [transfer_degree q D hq hs t v]
  by_cases hv : (transferState q D t).label v < D.order
  · rw [if_pos hv]
    have hm : (transferState q D t).label v ∈ range D.order := mem_range.mpr hv
    rw [← D.label_range] at hm
    obtain ⟨w,_,hwe⟩ := mem_image.mp hm
    have hu := startup_use_bound q D hq hs t ((transferState q D t).label v) hv
    have hd := original_plus_slot q D hs w
    rw [hwe] at hd
    omega
  · rw [if_neg hv]
    have hu := tail_use_bound q D hq hs t ((transferState q D t).label v) (by omega)
    omega

end Erdos585.GeneralStar

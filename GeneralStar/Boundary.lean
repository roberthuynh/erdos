import GeneralStar.Word

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

open Finset SimpleGraph
namespace Erdos585.GeneralStar

theorem seedSlot_of_mem (q : ℕ) (D : GraphData) (v : D.Carrier) (hv : v ∈ D.B) :
    seedSlot q D (D.label v)=2*(q-1)-D.graph.degree v := by
  unfold seedSlot
  rw [sum_eq_single v]
  · simp
  · intro w _ hwv
    have hn : D.label w ≠ D.label v := fun h => hwv (D.labels.injective h)
    simp [hn]
  · intro hn
    exact (hn hv).elim

theorem ordered_slots_sum (q : ℕ) (D : GraphData) :
    (((D.B.image D.label).sort (· ≤ ·)).map (seedSlot q D)).sum =
      ∑ v ∈ D.B, (2*(q-1)-D.graph.degree v) := by
  rw [← List.sum_toFinset (seedSlot q D) ((D.B.image D.label).sort_nodup (· ≤ ·)),sort_toFinset]
  rw [sum_image (g := D.label) (fun _ _ _ _ h => D.labels.injective h)]
  apply sum_congr rfl
  intro v hv
  exact seedSlot_of_mem q D v hv

theorem ordered_slot_bound (q : ℕ) (D : GraphData) (hs : SeedHyp q D)
    (z : ℕ) (hz : z ∈ (D.B.image D.label).sort (· ≤ ·)) : seedSlot q D z ≤ q-1 := by
  have hz' : z ∈ D.B.image D.label := by simpa using hz
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hz'
  rw [seedSlot_of_mem q D v hv]
  have hd := hs.2.2.2.1 v
  omega

theorem startupWord_length (q : ℕ) (D : GraphData) (hs : SeedHyp q D) :
    (startupWord q D).length=(q-1)*(q-1) := by
  unfold startupWord
  apply allocateWord_length
  rw [ordered_slots_sum]
  simpa [pow_two] using hs.2.2.2.2.2

theorem startupLabels_card (q : ℕ) (D : GraphData) (_hq : 5 ≤ q)
    (hs : SeedHyp q D) (t : ℕ) (ht : t < q-1) : (startupLabels q D t).card=q-1 := by
  unfold startupLabels startupWord
  rw [card_image_of_injOn]
  · exact card_range (q-1)
  · apply allocateWord_residue_injective
    · omega
    · exact ht
    · exact sort_nodup _ _
    · exact ordered_slot_bound q D hs
    · rw [ordered_slots_sum]
      simpa [pow_two] using hs.2.2.2.2.2

theorem startupLabels_subset (q : ℕ) (D : GraphData) (_hq : 5 ≤ q)
    (hs : SeedHyp q D) (t : ℕ) (ht : t < q-1) :
    startupLabels q D t ⊆ D.B.image D.label := by
  intro z hz
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hz
  have hj' : j < q-1 := mem_range.mp hj
  have hip : t+j*(q-1) < (q-1)*(q-1) := by nlinarith
  have hl := startupWord_length q D hs
  have hm := getD_mem_of_lt (startupWord q D) (t+j*(q-1)) (by omega)
  unfold startupWord at hm
  rw [allocateWord_eq_take] at hm
  have hr := rawWord_mem (seedSlot q D) ((D.B.image D.label).sort (· ≤ ·)) _
    (List.mem_of_mem_take hm)
  simpa [startupWord,allocateWord_eq_take] using hr

theorem GraphData.label_range (D : GraphData) : univ.image D.label=range D.order :=
  D.labels.image_range

theorem GraphData.add_order (D : GraphData) (b : Bool) (N : Finset D.Carrier) :
    (D.add b N).order=D.order+1 := by
  change Fintype.card (Option D.Carrier)=Fintype.card D.Carrier+1
  exact Fintype.card_option

theorem transfer_order (q : ℕ) (D : GraphData) (t : ℕ) :
    (transferState q D t).order=D.order+t := by
  induction t with
  | zero => simp [transferState]
  | succ t ih => rw [transferState,GraphData.add_order,ih];omega

theorem prescribedLabels_card (q : ℕ) (D : GraphData) (hq : 5 ≤ q)
    (hs : SeedHyp q D) (t : ℕ) : (prescribedLabels q D t).card=q-1 := by
  by_cases ht : t < q-1
  · simp only [prescribedLabels,if_pos ht]
    exact startupLabels_card q D hq hs t ht
  · simp only [prescribedLabels,if_neg ht]
    rw [card_image_of_injective _ (by intro x y h; dsimp at h; omega)]
    exact card_range _

theorem prescribedLabels_range (q : ℕ) (D : GraphData) (hq : 5 ≤ q)
    (hs : SeedHyp q D) (t : ℕ) : prescribedLabels q D t ⊆ range (D.order+t) := by
  by_cases ht : t < q-1
  · simp only [prescribedLabels,if_pos ht]
    intro z hz
    obtain ⟨v,_,rfl⟩ := mem_image.mp (startupLabels_subset q D hq hs t ht hz)
    have hb := D.labels.bounded v
    change D.label v < D.order at hb
    exact mem_range.mpr (by omega)
  · simp only [prescribedLabels,if_neg ht]
    intro z hz
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hz
    have hj' := mem_range.mp hj
    have hr : 0 < q-1 := by omega
    have hk : 1 ≤ t/(q-1) := (Nat.le_div_iff_mul_le hr).mpr (by omega)
    have hsub : t/(q-1)-1+1=t/(q-1) := by omega
    have hprod := Nat.div_mul_le_self t (q-1)
    apply mem_range.mpr
    nlinarith

theorem transferNeighbors_image (q : ℕ) (seed D : GraphData) (t : ℕ)
    (hb : prescribedLabels q seed t ⊆ range D.order) :
    (transferNeighbors q seed D t).image D.label=prescribedLabels q seed t := by
  ext z
  constructor
  · intro hz
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hz
    exact (mem_filter.mp hv).2
  · intro hz
    have hr := hb hz
    rw [← D.label_range] at hr
    obtain ⟨v,_,rfl⟩ := mem_image.mp hr
    exact mem_image.mpr ⟨v,mem_filter.mpr ⟨mem_univ _,hz⟩,rfl⟩

theorem transferNeighbors_card (q : ℕ) (D : GraphData) (hq : 5 ≤ q)
    (hs : SeedHyp q D) (t : ℕ) :
    (transferNeighbors q D (transferState q D t) t).card=q-1 := by
  have hr : prescribedLabels q D t ⊆ range (transferState q D t).order := by
    rw [transfer_order]
    exact prescribedLabels_range q D hq hs t
  have he := congrArg Finset.card (transferNeighbors_image q D (transferState q D t) t hr)
  rw [card_image_of_injective _ (show Function.Injective (transferState q D t).label from
      (transferState q D t).labels.injective)] at he
  exact he.trans (prescribedLabels_card q D hq hs t)

theorem transfer_noRegular (q : ℕ) (D : GraphData) (hq : 5 ≤ q)
    (hs : SeedHyp q D) (t : ℕ) :
    BqLowerFamily.NoRegular q (transferState q D t).graph := by
  induction t with
  | zero => exact hs.2.2.2.2.1
  | succ t ih =>
    exact BqLowerFamily.noRegular_extend (transferState q D t).graph
      (transferNeighbors q D (transferState q D t) t) q (by omega)
      (transferNeighbors_card q D hq hs t) ih

theorem transfer_edges (q : ℕ) (D : GraphData) (hq : 5 ≤ q)
    (hs : SeedHyp q D) (t : ℕ) :
    (transferState q D t).graph.edgeFinset.card=D.graph.edgeFinset.card+(q-1)*t := by
  induction t with
  | zero => simp only [transferState,Nat.mul_zero,Nat.add_zero]; rfl
  | succ t ih =>
    change (BqLowerFamily.extendGraph (transferState q D t).graph
      (transferNeighbors q D (transferState q D t) t)).edgeFinset.card=_
    rw [BqLowerFamily.edges_extend,transferNeighbors_card q D hq hs t,ih]
    ring

theorem transfer_min (q : ℕ) (D : GraphData) (hq : 5 ≤ q)
    (hs : SeedHyp q D) (t : ℕ) :
    ∀ v, q-1 ≤ (transferState q D t).graph.degree v := by
  induction t with
  | zero => exact fun v => (hs.2.2.2.1 v).1
  | succ t ih =>
    change ∀ v : Option (transferState q D t).Carrier,
      q-1 ≤ (BqLowerFamily.extendGraph (transferState q D t).graph
        (transferNeighbors q D (transferState q D t) t)).degree v
    intro v
    cases v with
    | none => rw [BqLowerFamily.degree_none,transferNeighbors_card q D hq hs t]
    | some v => rw [BqLowerFamily.degree_some];exact le_trans (ih v) (Nat.le_add_right _ _)

end Erdos585.GeneralStar

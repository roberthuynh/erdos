import GeneralStar.Degree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

open Finset SimpleGraph
namespace Erdos585.GeneralStar

def leftLabel (q : ℕ) (D : GraphData) (z : ℕ) : Prop :=
  if z < D.order then z ∈ D.A.image D.label else receivingA q (z-D.order)=true
instance leftLabelDecidable (q : ℕ) (D : GraphData) (z : ℕ) : Decidable (leftLabel q D z) := by
  unfold leftLabel; infer_instance

theorem transfer_left (q : ℕ) (D : GraphData) (t : ℕ) (v : (transferState q D t).Carrier) :
    v ∈ (transferState q D t).A ↔ leftLabel q D ((transferState q D t).label v) := by
  revert v
  induction t with
  | zero =>
    intro v
    change D.Carrier at v
    change v ∈ D.A ↔ leftLabel q D (D.label v)
    have hb := D.labels.bounded v
    change D.label v < D.order at hb
    simp only [leftLabel,if_pos hb]
    constructor
    · intro hv;exact mem_image.mpr ⟨v,hv,rfl⟩
    · intro hv
      obtain ⟨w,hw,hwe⟩ := mem_image.mp hv
      exact D.labels.injective hwe ▸ hw
  | succ t ih =>
    intro v
    change Option (transferState q D t).Carrier at v
    cases v with
    | none =>
      have ho := transfer_order q D t
      change none ∈ (if receivingA q t then insert none ((transferState q D t).A.image some)
        else (transferState q D t).A.image some) ↔ leftLabel q D (transferState q D t).order
      rw [ho]
      cases hb : receivingA q t <;> simp [leftLabel,hb]
    | some v =>
      change some v ∈ (if receivingA q t then insert none ((transferState q D t).A.image some)
        else (transferState q D t).A.image some) ↔ leftLabel q D ((transferState q D t).label v)
      cases hb : receivingA q t <;> simpa [hb] using ih v

theorem transfer_shore_sets (q : ℕ) (D : GraphData) (hs : SeedHyp q D) (t : ℕ) :
    Disjoint (transferState q D t).A (transferState q D t).B ∧
    (transferState q D t).A ∪ (transferState q D t).B=univ := by
  induction t with
  | zero => exact ⟨hs.1,hs.2.1⟩
  | succ t ih =>
    change Disjoint
      (if receivingA q t then insert none ((transferState q D t).A.image some) else (transferState q D t).A.image some)
      (if receivingA q t then (transferState q D t).B.image some else insert none ((transferState q D t).B.image some)) ∧
      (if receivingA q t then insert none ((transferState q D t).A.image some) else (transferState q D t).A.image some) ∪
      (if receivingA q t then (transferState q D t).B.image some else insert none ((transferState q D t).B.image some))=univ
    cases receivingA q t
    all_goals simp only [Bool.false_eq_true,if_false,if_true]
    all_goals refine ⟨?_,?_⟩
    · apply Finset.disjoint_left.mpr
      intro v hva hvb
      cases v with
      | none => simp at hva
      | some v => exact Finset.disjoint_left.mp ih.1 (by simpa using hva) (by simpa using hvb)
    · ext v
      cases v with
      | none => simp
      | some v =>
        have hv : v ∈ (transferState q D t).A ∪ (transferState q D t).B := by rw [ih.2];simp
        simpa using hv
    · apply Finset.disjoint_left.mpr
      intro v hva hvb
      cases v with
      | none => simp at hvb
      | some v => exact Finset.disjoint_left.mp ih.1 (by simpa using hva) (by simpa using hvb)
    · ext v
      cases v with
      | none => simp
      | some v =>
        have hv : v ∈ (transferState q D t).A ∪ (transferState q D t).B := by rw [ih.2];simp
        simpa using hv

theorem transfer_right (q : ℕ) (D : GraphData) (hs : SeedHyp q D) (t : ℕ)
    (v : (transferState q D t).Carrier) :
    v ∈ (transferState q D t).B ↔ ¬leftLabel q D ((transferState q D t).label v) := by
  have hsets := transfer_shore_sets q D hs t
  rw [← transfer_left]
  have hc : v ∈ (transferState q D t).A ∪ (transferState q D t).B := by rw [hsets.2];simp
  constructor
  · exact fun hv ha => Finset.disjoint_left.mp hsets.1 ha hv
  · intro hn
    exact (mem_union.mp hc).resolve_left hn

theorem parent_receiving (q : ℕ) (_hq : 5 ≤ q) (t j : ℕ) (ht : q-1 ≤ t) (hj : j < q-1) :
    receivingA q ((t/(q-1)-1)*(q-1)+j)= !(receivingA q t) := by
  have hr : 0 < q-1 := by omega
  have hk : 1 ≤ t/(q-1) := (Nat.le_div_iff_mul_le hr).mpr (by omega)
  have hd : ((t/(q-1)-1)*(q-1)+j)/(q-1)=t/(q-1)-1 := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hr,Nat.div_eq_of_lt hj,Nat.zero_add]
  have hs : ((t/(q-1)-1)*(q-1)+j)<q-1 ↔ t/(q-1)=1 := by
    constructor
    · intro h
      by_contra hn
      have hsub : 1 ≤ t/(q-1)-1 := by omega
      have hm : q-1 ≤ (t/(q-1)-1)*(q-1) := by nlinarith
      omega
    · intro h; simp [h];exact hj
  simp only [receivingA,hd,hs]
  rw [← decide_not]
  congr 1
  apply propext
  omega

theorem prescribed_opposite (q : ℕ) (D : GraphData) (hq : 5 ≤ q) (hs : SeedHyp q D)
    (t : ℕ) (v : (transferState q D t).Carrier)
    (hv : v ∈ transferNeighbors q D (transferState q D t) t) :
    if receivingA q t then v ∈ (transferState q D t).B else v ∈ (transferState q D t).A := by
  have hz := (mem_filter.mp hv).2
  by_cases ht : t < q-1
  · have hb : receivingA q t=true := by simp [receivingA,ht]
    simp only [hb,if_true]
    rw [transfer_right q D hs t v]
    simp only [prescribedLabels,if_pos ht] at hz
    obtain ⟨w,hw,hwe⟩ := mem_image.mp (startupLabels_subset q D hq hs t ht hz)
    have hwb := D.labels.bounded w
    change D.label w < D.order at hwb
    rw [← hwe]
    simp only [leftLabel,if_pos hwb]
    intro ha
    obtain ⟨u,hu,hue⟩ := mem_image.mp ha
    have he := D.labels.injective hue
    exact Finset.disjoint_left.mp hs.1 hu (he.symm ▸ hw)
  · simp only [prescribedLabels,if_neg ht] at hz
    obtain ⟨j,hj,hje⟩ := mem_image.mp hz
    have hje' : (transferState q D t).label v-D.order=(t/(q-1)-1)*(q-1)+j := by omega
    have hlow : D.order ≤ (transferState q D t).label v := by omega
    have hp := parent_receiving q hq t j (by omega) (mem_range.mp hj)
    cases hb : receivingA q t
    · simp only [Bool.false_eq_true,if_false]
      rw [transfer_left]
      simp [leftLabel,not_lt_of_ge hlow,hje',hp,hb]
    · simp only [if_true]
      rw [transfer_right q D hs t v]
      simp [leftLabel,not_lt_of_ge hlow,hje',hp,hb]

theorem add_bipartite (D : GraphData) (b : Bool) (N : Finset D.Carrier)
    (hd : Disjoint D.A D.B)
    (hb : D.graph.IsBipartiteWith (D.A : Set D.Carrier) (D.B : Set D.Carrier))
    (hN : if b then N ⊆ D.B else N ⊆ D.A) :
    (D.add b N).graph.IsBipartiteWith ((D.add b N).A : Set (D.add b N).Carrier)
      ((D.add b N).B : Set (D.add b N).Carrier) := by
  change (BqLowerFamily.extendGraph D.graph N).IsBipartiteWith
    (((if b then insert none (D.A.image some) else D.A.image some) : Finset (Option D.Carrier)) : Set (Option D.Carrier))
    (((if b then D.B.image some else insert none (D.B.image some)) : Finset (Option D.Carrier)) : Set (Option D.Carrier))
  cases b
  all_goals simp only [Bool.false_eq_true,if_false,if_true] at hN ⊢
  all_goals refine ⟨?_,?_⟩
  · rw [disjoint_coe]
    apply Finset.disjoint_left.mpr
    intro v hva hvb
    cases v with
    | none => simp at hva
    | some v => exact Finset.disjoint_left.mp hd (by simpa using hva) (by simpa using hvb)
  · intro v w hvw
    cases v with
    | none =>
      cases w with
      | none => exact hvw.elim
      | some w => exact Or.inr ⟨by simp,by simpa using hN hvw⟩
    | some v =>
      cases w with
      | none => exact Or.inl ⟨by simpa using hN hvw,by simp⟩
      | some w => simpa using hb.mem_of_adj hvw
  · rw [disjoint_coe]
    apply Finset.disjoint_left.mpr
    intro v hva hvb
    cases v with
    | none => simp at hvb
    | some v => exact Finset.disjoint_left.mp hd (by simpa using hva) (by simpa using hvb)
  · intro v w hvw
    cases v with
    | none =>
      cases w with
      | none => exact hvw.elim
      | some w => exact Or.inl ⟨by simp,by simpa using hN hvw⟩
    | some v =>
      cases w with
      | none => exact Or.inr ⟨by simpa using hN hvw,by simp⟩
      | some w => simpa using hb.mem_of_adj hvw

theorem transfer_bipartiteWith (q : ℕ) (D : GraphData) (hq : 5 ≤ q) (hs : SeedHyp q D)
    (t : ℕ) : (transferState q D t).graph.IsBipartiteWith
      ((transferState q D t).A : Set (transferState q D t).Carrier)
      ((transferState q D t).B : Set (transferState q D t).Carrier) := by
  induction t with
  | zero => exact hs.2.2.1
  | succ t ih =>
    apply add_bipartite _ _ _ (transfer_shore_sets q D hs t).1 ih
    cases hb : receivingA q t
    all_goals simp only [Bool.false_eq_true,if_false,if_true]
    all_goals intro v hv
    all_goals simpa [hb] using prescribed_opposite q D hq hs t v hv

end Erdos585.GeneralStar

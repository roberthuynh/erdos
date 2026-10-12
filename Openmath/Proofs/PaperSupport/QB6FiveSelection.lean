import Openmath.Proofs.PaperSupport.QB6E6Lean

/- 


-/

open Finset
namespace Erdos585.QB6FiveSelection
open QB4 QB5 QB6Assembly QB6E6Lean
universe u
set_option maxHeartbeats 1500000
variable {V : Type u} [DecidableEq V]

/-- Actual per-shore marked cost. -/
def markedCost (F : Finset (V × V)) (r : V × V → V) (L : Finset V) : ℤ :=
  ∑ v ∈ L, (3 - (mult F r v : ℤ))

/-- Conservative positive weight for an actual subset of the pair set. -/
def pointWeight (F M : Finset (V × V)) (r : V × V → V) (L : Finset V) (v : V) : ℤ :=
  max 0 (3 * (mult M r v : ℤ) - if v ∈ L then 3 else (mult F r v : ℤ))

def weightBudget (F M : Finset (V × V)) (r : V × V → V) (X L : Finset V) : ℤ :=
  ∑ v ∈ X, pointWeight F M r L v

/-- All inputs are actual endpoint counts and marks. -/
structure SideData (F : Finset (V × V)) (r : V × V → V) (X L : Finset V) : Prop where
  ends : ∀ e ∈ F, r e ∈ X
  subset : L ⊆ X
  cap : ∀ v ∈ X, mult F r v ≤ 3
  positive : ∀ v ∈ L, 0 < mult F r v
  triples : ∀ v ∈ X, mult F r v = 3 → v ∈ L
  cost : markedCost F r L ≤ 6

/-- Actual coverage, or exactly one actual uncovered mark with budget. -/
def GoodSide (F M : Finset (V × V)) (r : V × V → V) (X L : Finset V) : Prop :=
  (∀ v ∈ L, 0 < mult M r v) ∨
    ∃ p ∈ L, mult M r p = 0 ∧
      (∀ v ∈ L, mult M r v = 0 → v = p) ∧ weightBudget F M r X L ≤ 7

/-- Eligible actual edges meet no marked degree-one endpoint. -/
def eligible (F : Finset (V × V)) (L R : Finset V) : Finset (V × V) :=
  {e ∈ F | ¬ (e.1 ∈ L ∧ mult F Prod.fst e.1 = 1) ∧
    ¬ (e.2 ∈ R ∧ mult F Prod.snd e.2 = 1)}

def badLeft (F : Finset (V × V)) (L : Finset V) (e f : V × V) : Prop :=
  e.1 = f.1 ∧ e.1 ∈ L ∧ mult F Prod.fst e.1 = 2

def badRight (F : Finset (V × V)) (R : Finset V) (e f : V × V) : Prop :=
  e.2 = f.2 ∧ e.2 ∈ R ∧ mult F Prod.snd e.2 = 2

/- -/
def GenericSelectionStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (F : Finset (V × V)) (X Y L R : Finset V),
    #F = 7 → SideData F Prod.fst X L → SideData F Prod.snd Y R →
      ∃ M ⊆ F, #M = 5 ∧ GoodSide F M Prod.fst X L ∧ GoodSide F M Prod.snd Y R

theorem mult_mono {F M : Finset (V × V)} (hM : M ⊆ F) (r : V × V → V) (v : V) :
    mult M r v ≤ mult F r v := card_le_card (filter_subset_filter _ hM)

theorem mult_sdiff_add {F N : Finset (V × V)} (hN : N ⊆ F) (r : V × V → V) (v : V) :
    mult (F \ N) r v + mult N r v = mult F r v := by
  unfold mult
  have he : {e ∈ F \ N | r e = v} = {e ∈ F | r e = v} \ {e ∈ N | r e = v} := by
    ext e
    simp only [mem_filter, mem_sdiff]
    tauto
  rw [he]
  exact card_sdiff_add_card_eq_card (filter_subset_filter _ hN)

theorem mult_pair {e f : V × V} (hne : e ≠ f) (r : V × V → V) (v : V) :
    mult {e, f} r v = (if r e = v then 1 else 0) + (if r f = v then 1 else 0) := by
  unfold mult
  rw [filter_insert, filter_singleton]
  by_cases he : r e = v <;> by_cases hf : r f = v <;>
    simp [he, hf, hne]

theorem mult_delete_pair {F : Finset (V × V)} {e f : V × V}
    (he : e ∈ F) (hf : f ∈ F) (hne : e ≠ f) (r : V × V → V) (v : V) :
    mult (F \ {e, f}) r v + (if r e = v then 1 else 0) + (if r f = v then 1 else 0) =
      mult F r v := by
  have hN : ({e, f} : Finset (V × V)) ⊆ F := by
    intro x hx
    rcases (by simpa only [mem_insert, mem_singleton] using hx) with rfl | rfl
    · exact he
    · exact hf
  have hs := mult_sdiff_add hN r v
  rw [mult_pair hne] at hs
  omega

theorem pointWeight_mono {F M : Finset (V × V)} (hM : M ⊆ F)
    (r : V × V → V) (L : Finset V) (v : V) : pointWeight F M r L v ≤ pointWeight F F r L v := by
  apply max_le_max le_rfl
  have hm := mult_mono hM r v
  omega

theorem budget_drop {F M : Finset (V × V)} (hM : M ⊆ F)
    (r : V × V → V) (X L : Finset V) {v : V} (hv : v ∈ X) {b : ℤ}
    (hdrop : pointWeight F M r L v + b ≤ pointWeight F F r L v) :
    weightBudget F M r X L + b ≤ weightBudget F F r X L := by
  have hsM := sum_erase_add X (pointWeight F M r L) hv
  have hsF := sum_erase_add X (pointWeight F F r L) hv
  have he : (∑ w ∈ X.erase v, pointWeight F M r L w) ≤
      ∑ w ∈ X.erase v, pointWeight F F r L w :=
    sum_le_sum fun w _ => pointWeight_mono hM r L w
  unfold weightBudget
  linarith

theorem initial_budget {F : Finset (V × V)} {r : V × V → V} {X L : Finset V}
    (h : SideData F r X L) (hF : #F = 7) : weightBudget F F r X L = 14 - markedCost F r L := by
  have hp : ∀ v ∈ X, pointWeight F F r L v =
      2 * (mult F r v : ℤ) - if v ∈ L then (3 - (mult F r v : ℤ)) else 0 := by
    intro v hv
    by_cases hvL : v ∈ L
    · have hn := h.positive v hvL
      simp only [pointWeight, if_pos hvL]
      omega
    · have hc := h.cap v hv
      have hn : mult F r v ≤ 2 := by
        by_contra! hn
        exact hvL (h.triples v hv (by omega))
      simp only [pointWeight, if_neg hvL]
      omega
  have hs : (∑ v ∈ X, (mult F r v : ℤ)) = 7 := by
    have ht := sum_mult_eq F r X
    have hf : {e ∈ F | r e ∈ X} = F := filter_eq_self.mpr h.ends
    rw [hf, hF] at ht
    exact_mod_cast ht
  have hfilter : {v ∈ X | v ∈ L} = L := by
    ext v
    simp only [mem_filter]
    exact ⟨fun hv => hv.2, fun hv => ⟨h.subset hv, hv⟩⟩
  have hz : (∑ v ∈ X, if v ∈ L then (3 - (mult F r v : ℤ)) else 0) = markedCost F r L := by
    rw [← sum_filter, hfilter]
    rfl
  unfold weightBudget
  rw [sum_congr rfl hp, sum_sub_distrib, ← mul_sum, hs, hz]
  ring

def leaves (F : Finset (V × V)) (r : V × V → V) (L : Finset V) : Finset V :=
  {v ∈ L | mult F r v = 1}

def leafEdges (F : Finset (V × V)) (r : V × V → V) (L : Finset V) : Finset (V × V) :=
  {e ∈ F | r e ∈ leaves F r L}

theorem leafEdges_card (F : Finset (V × V)) (r : V × V → V) (L : Finset V) :
    #(leafEdges F r L) = #(leaves F r L) := by
  have ht := sum_mult_eq F r (leaves F r L)
  have hp : ∀ v ∈ leaves F r L, mult F r v = 1 := fun v hv => (mem_filter.mp hv).2
  rw [sum_congr rfl hp, sum_const, smul_eq_mul, mul_one] at ht
  exact ht.symm

theorem leaves_cost {F : Finset (V × V)} {r : V × V → V} {X L : Finset V}
    (h : SideData F r X L) : 2 * (#(leaves F r L) : ℤ) ≤ markedCost F r L := by
  have hs : (∑ v ∈ leaves F r L, (3 - (mult F r v : ℤ))) = 2 * #(leaves F r L) := by
    have hp : ∀ v ∈ leaves F r L, (3 - (mult F r v : ℤ)) = 2 := by
      intro v hv
      have hc := (mem_filter.mp hv).2
      rw [hc]
      norm_num
    rw [sum_congr rfl hp, sum_const, nsmul_eq_mul]
    ring
  rw [← hs]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun v hv _ => by
    have hc := h.cap v (h.subset hv)
    omega

theorem ineligible_union (F : Finset (V × V)) (L R : Finset V) :
    F \ eligible F L R = leafEdges F Prod.fst L ∪ leafEdges F Prod.snd R := by
  ext e
  simp only [eligible, leafEdges, leaves, mem_sdiff, mem_filter, mem_union]
  tauto

theorem ineligible_bound {F : Finset (V × V)} {X Y L R : Finset V}
    (hL : SideData F Prod.fst X L) (hR : SideData F Prod.snd Y R) :
    2 * (#(F \ eligible F L R) : ℤ) ≤ markedCost F Prod.fst L + markedCost F Prod.snd R := by
  have hc : #(F \ eligible F L R) ≤ #(leaves F Prod.fst L) + #(leaves F Prod.snd R) := by
    rw [ineligible_union]
    have hu := card_union_le (leafEdges F Prod.fst L) (leafEdges F Prod.snd R)
    rwa [leafEdges_card, leafEdges_card] at hu
  have hzL := leaves_cost hL
  have hzR := leaves_cost hR
  omega

theorem lost_eligible {F : Finset (V × V)} {r : V × V → V} {X L : Finset V}
    (h : SideData F r X L) {e f : V × V} (he : e ∈ F) (hf : f ∈ F) (hne : e ≠ f)
    (heL : ¬ (r e ∈ L ∧ mult F r (r e) = 1))
    (hfL : ¬ (r f ∈ L ∧ mult F r (r f) = 1)) {v : V} (hv : v ∈ L)
    (hz : mult (F \ {e, f}) r v = 0) : r e = v ∧ r f = v ∧ mult F r v = 2 := by
  have hd := mult_delete_pair he hf hne r v
  have hp := h.positive v hv
  by_cases hev : r e = v
  · by_cases hfv : r f = v
    · simp only [if_pos hev, if_pos hfv, hz] at hd
      exact ⟨hev, hfv, by omega⟩
    · have hc : mult F r v = 1 := by simp only [if_pos hev, if_neg hfv, hz] at hd; omega
      exact False.elim (heL ⟨hev ▸ hv, hev ▸ hc⟩)
  · by_cases hfv : r f = v
    · have hc : mult F r v = 1 := by simp only [if_neg hev, if_pos hfv, hz] at hd; omega
      exact False.elim (hfL ⟨hfv ▸ hv, hfv ▸ hc⟩)
    · simp only [if_neg hev, if_neg hfv, hz] at hd
      omega

theorem pair_covered {F : Finset (V × V)} {r : V × V → V} {X L : Finset V}
    (h : SideData F r X L) {e f : V × V} (he : e ∈ F) (hf : f ∈ F) (hne : e ≠ f)
    (heL : ¬ (r e ∈ L ∧ mult F r (r e) = 1))
    (hfL : ¬ (r f ∈ L ∧ mult F r (r f) = 1))
    (hbad : ¬ (r e = r f ∧ r e ∈ L ∧ mult F r (r e) = 2)) :
    ∀ v ∈ L, 0 < mult (F \ {e, f}) r v := by
  intro v hv
  by_contra! hz
  have ht := lost_eligible h he hf hne heL hfL hv (by omega)
  apply hbad
  rcases ht with ⟨hev, hfv, hc⟩
  exact ⟨hev.trans hfv.symm, hev ▸ hv, hev ▸ hc⟩

theorem pair_good_side {F : Finset (V × V)} {r : V × V → V} {X L : Finset V}
    (h : SideData F r X L) (hF : #F = 7) {e f : V × V}
    (he : e ∈ F) (hf : f ∈ F) (hne : e ≠ f)
    (heL : ¬ (r e ∈ L ∧ mult F r (r e) = 1))
    (hfL : ¬ (r f ∈ L ∧ mult F r (r f) = 1))
    (hc : 4 ≤ markedCost F r L) : GoodSide F (F \ {e, f}) r X L := by
  by_cases hbad : r e = r f ∧ r e ∈ L ∧ mult F r (r e) = 2
  · right
    refine ⟨r e, hbad.2.1, ?_, ?_, ?_⟩
    · have hd := mult_delete_pair he hf hne r (r e)
      simp only [if_pos hbad.1.symm, hbad.2.2, ite_true] at hd
      omega
    · intro v hv hz
      exact (lost_eligible h he hf hne heL hfL hv hz).1.symm
    · have hv := h.subset hbad.2.1
      have hd := mult_delete_pair he hf hne r (r e)
      have hz : mult (F \ {e, f}) r (r e) = 0 := by
        simp only [if_pos hbad.1.symm, hbad.2.2, ite_true] at hd
        omega
      have hdrop : pointWeight F (F \ {e, f}) r L (r e) + 3 ≤ pointWeight F F r L (r e) := by
        simp [pointWeight, hz, hbad.2.1, hbad.2.2]
      have hb := budget_drop sdiff_subset r X L hv hdrop
      rw [initial_budget h hF] at hb
      omega
  · exact Or.inl (pair_covered h he hf hne heL hfL hbad)

theorem no_marked_two {F : Finset (V × V)} {r : V × V → V} {X L : Finset V}
    (h : SideData F r X L) (hz : markedCost F r L = 6)
    (hl : #(leaves F r L) = 3) : ∀ v ∈ L, mult F r v ≠ 2 := by
  have hs : (∑ v ∈ leaves F r L, (3 - (mult F r v : ℤ))) = 6 := by
    have hp : ∀ v ∈ leaves F r L, (3 - (mult F r v : ℤ)) = 2 := by
      intro v hv
      rw [(mem_filter.mp hv).2]
      norm_num
    rw [sum_congr rfl hp, sum_const, hl]
    norm_num
  have ht := sum_sdiff (filter_subset (fun v => mult F r v = 1) L)
    (f := fun v => (3 - (mult F r v : ℤ)))
  change (∑ v ∈ L \ leaves F r L, (3 - (mult F r v : ℤ))) +
    (∑ v ∈ leaves F r L, (3 - (mult F r v : ℤ))) = markedCost F r L at ht
  rw [hz, hs] at ht
  have ht0 : (∑ v ∈ L \ leaves F r L, (3 - (mult F r v : ℤ))) = 0 := by omega
  intro v hv hc
  have hvn : v ∈ L \ leaves F r L := by
    simp [leaves, hv, hc]
  have hle := single_le_sum (f := fun v => (3 - (mult F r v : ℤ)))
    (s := L \ leaves F r L) (fun w hw => by
      have hc' := h.cap w (h.subset (mem_sdiff.mp hw).1)
      omega) hvn
  rw [hc, ht0] at hle
  norm_num at hle

theorem one_eligible_lost {F : Finset (V × V)} {r : V × V → V} {X L : Finset V}
    (h : SideData F r X L) {e f : V × V} (he : e ∈ F) (hf : f ∈ F) (hne : e ≠ f)
    (heL : ¬ (r e ∈ L ∧ mult F r (r e) = 1))
    (h2 : ∀ v ∈ L, mult F r v ≠ 2) {v : V} (hv : v ∈ L)
    (hz : mult (F \ {e, f}) r v = 0) : r f = v ∧ mult F r v = 1 ∧ r e ≠ v := by
  have hd := mult_delete_pair he hf hne r v
  have hp := h.positive v hv
  have hn := h2 v hv
  by_cases hev : r e = v
  · by_cases hfv : r f = v
    · simp only [if_pos hev, if_pos hfv, hz] at hd
      omega
    · have hc : mult F r v = 1 := by simp only [if_pos hev, if_neg hfv, hz] at hd; omega
      exact False.elim (heL ⟨hev ▸ hv, hev ▸ hc⟩)
  · by_cases hfv : r f = v
    · simp only [if_neg hev, if_pos hfv, hz] at hd
      exact ⟨hfv, by omega, hev⟩
    · simp only [if_neg hev, if_neg hfv, hz] at hd
      omega

theorem one_eligible_drop {F : Finset (V × V)} {r : V × V → V} {X L : Finset V}
    (h : SideData F r X L) {e f : V × V} (he : e ∈ F) (hf : f ∈ F) (hne : e ≠ f)
    (heL : ¬ (r e ∈ L ∧ mult F r (r e) = 1))
    (h2 : ∀ v ∈ L, mult F r v ≠ 2) :
    pointWeight F (F \ {e, f}) r L (r e) + 2 ≤ pointWeight F F r L (r e) := by
  have hd := mult_delete_pair he hf hne r (r e)
  have hv := h.ends e he
  have hc := h.cap (r e) hv
  have hp : 0 < mult F r (r e) := by
    unfold mult
    exact card_pos.mpr ⟨e, mem_filter.mpr ⟨he, rfl⟩⟩
  by_cases hm : r e ∈ L
  · have hn := h2 (r e) hm
    have h1 : mult F r (r e) ≠ 1 := fun hh => heL ⟨hm, hh⟩
    have hc3 : mult F r (r e) = 3 := by omega
    simp only [ite_true] at hd
    simp only [pointWeight, if_pos hm, hc3]
    omega
  · have hc2 : mult F r (r e) ≤ 2 := by
      by_contra! hn
      exact hm (h.triples (r e) hv (by omega))
    simp only [ite_true] at hd
    simp only [pointWeight, if_neg hm]
    omega

theorem one_eligible_good_side {F : Finset (V × V)} {r : V × V → V} {X L : Finset V}
    (h : SideData F r X L) (hF : #F = 7) {e f : V × V}
    (he : e ∈ F) (hf : f ∈ F) (hne : e ≠ f)
    (heL : ¬ (r e ∈ L ∧ mult F r (r e) = 1))
    (h2 : ∀ v ∈ L, mult F r v ≠ 2) (hz : markedCost F r L = 6) :
    GoodSide F (F \ {e, f}) r X L := by
  by_cases hleaf : r f ∈ L ∧ mult F r (r f) = 1
  · right
    refine ⟨r f, hleaf.1, ?_, ?_, ?_⟩
    · have hneR : r e ≠ r f := fun hh => heL ⟨hh ▸ hleaf.1, hh ▸ hleaf.2⟩
      have hd := mult_delete_pair he hf hne r (r f)
      simp only [if_neg hneR, ite_true, hleaf.2] at hd
      omega
    · intro v hv hvz
      exact (one_eligible_lost h he hf hne heL h2 hv hvz).1.symm
    · have hdrop := one_eligible_drop h he hf hne heL h2
      have hb := budget_drop sdiff_subset r X L (h.ends e he) hdrop
      rw [initial_budget h hF, hz] at hb
      omega
  · left
    intro v hv
    by_contra! hvz
    have ht := one_eligible_lost h he hf hne heL h2 hv (by omega)
    exact hleaf ⟨ht.1 ▸ hv, ht.1 ▸ ht.2.1⟩

theorem three_le_mult {F : Finset (V × V)} {e f g : V × V}
    (he : e ∈ F) (hf : f ∈ F) (hg : g ∈ F)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (r : V × V → V) (hefR : r e = r f) (hegR : r e = r g) :
    3 ≤ mult F r (r e) := by
  have hs : ({e, f, g} : Finset (V × V)) ⊆ {x ∈ F | r x = r e} := by
    intro x hx
    rcases (by simpa only [mem_insert, mem_singleton] using hx) with rfl | rfl | rfl
    · exact mem_filter.mpr ⟨he, rfl⟩
    · exact mem_filter.mpr ⟨hf, hefR.symm⟩
    · exact mem_filter.mpr ⟨hg, hegR.symm⟩
  have hc : #({e, f, g} : Finset (V × V)) = 3 := by simp [hef, heg, hfg]
  have ht := card_le_card hs
  rwa [hc] at ht

theorem three_good_pair {F : Finset (V × V)} {L R : Finset V} {e f g : V × V}
    (he : e ∈ F) (hf : f ∈ F) (hg : g ∈ F)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    (¬ badLeft F L e f ∧ ¬ badRight F R e f) ∨
    (¬ badLeft F L e g ∧ ¬ badRight F R e g) ∨
    (¬ badLeft F L f g ∧ ¬ badRight F R f g) := by
  by_contra! hn
  have hEF : badLeft F L e f ∨ badRight F R e f := by tauto
  have hEG : badLeft F L e g ∨ badRight F R e g := by tauto
  have hFG : badLeft F L f g ∨ badRight F R f g := by tauto
  have hcontra (r : V × V → V) (h1 : r e = r f) (h2 : r e = r g)
      (hc : mult F r (r e) = 2) : False := by
    have ht := three_le_mult he hf hg hef heg hfg r h1 h2
    omega
  rcases hEF with hEF | hEF <;> rcases hEG with hEG | hEG
  · exact hcontra Prod.fst hEF.1 hEG.1 hEF.2.2
  · rcases hFG with hFG | hFG
    · exact hcontra Prod.fst hEF.1 (hEF.1.trans hFG.1) hEF.2.2
    · exact hcontra Prod.snd (hEG.1.trans hFG.1.symm) hEG.1 hEG.2.2
  · rcases hFG with hFG | hFG
    · exact hcontra Prod.fst (hEG.1.trans hFG.1.symm) hEG.1 hEG.2.2
    · exact hcontra Prod.snd hEF.1 (hEF.1.trans hFG.1) hEF.2.2
  · exact hcontra Prod.snd hEF.1 hEG.1 hEF.2.2

theorem delete_pair_five {F : Finset (V × V)} {e f : V × V}
    (hF : #F = 7) (he : e ∈ F) (hf : f ∈ F) (hne : e ≠ f) : #(F \ {e, f}) = 5 := by
  have hN : ({e, f} : Finset (V × V)) ⊆ F := by
    intro x hx
    rcases (by simpa only [mem_insert, mem_singleton] using hx) with rfl | rfl
    · exact he
    · exact hf
  have hs := card_sdiff_add_card_eq_card hN
  have hc : #({e, f} : Finset (V × V)) = 2 := by simp [hne]
  rw [hc, hF] at hs
  omega

theorem generic_selection : GenericSelectionStatement.{u} := by
  intro V _ F X Y L R hF hL hR
  let K := eligible F L R
  have hKF : K ⊆ F := filter_subset _ _
  have hs : #(F \ K) + #K = 7 := by
    rw [card_sdiff_add_card_eq_card hKF, hF]
  have hz := ineligible_bound hL hR
  have hzL := hL.cost
  have hzR := hR.cost
  have hpos : 0 < #K := by change 2 * (#(F \ K) : ℤ) ≤ _ at hz; omega
  have hdata : ∀ e ∈ K, e ∈ F ∧
      ¬ (e.1 ∈ L ∧ mult F Prod.fst e.1 = 1) ∧
      ¬ (e.2 ∈ R ∧ mult F Prod.snd e.2 = 1) := fun e he => mem_filter.mp he
  by_cases h3 : 3 ≤ #K
  · obtain ⟨e, he⟩ := card_pos.mp hpos
    have hposE : 0 < #(K.erase e) := by rw [card_erase_of_mem he]; omega
    obtain ⟨f, hf⟩ := card_pos.mp hposE
    have hfK := (mem_erase.mp hf).2
    have hef : e ≠ f := ((mem_erase.mp hf).1).symm
    have hposF : 0 < #((K.erase e).erase f) := by
      rw [card_erase_of_mem hf, card_erase_of_mem he]
      omega
    obtain ⟨g, hg⟩ := card_pos.mp hposF
    have hgE := (mem_erase.mp hg).2
    have hgK := (mem_erase.mp hgE).2
    have heg : e ≠ g := ((mem_erase.mp hgE).1).symm
    have hfg : f ≠ g := ((mem_erase.mp hg).1).symm
    have de := hdata e he
    have df := hdata f hfK
    have dg := hdata g hgK
    have hpair (a b : V × V) (da : a ∈ F ∧
        ¬ (a.1 ∈ L ∧ mult F Prod.fst a.1 = 1) ∧ ¬ (a.2 ∈ R ∧ mult F Prod.snd a.2 = 1))
        (db : b ∈ F ∧ ¬ (b.1 ∈ L ∧ mult F Prod.fst b.1 = 1) ∧
          ¬ (b.2 ∈ R ∧ mult F Prod.snd b.2 = 1)) (hab : a ≠ b)
        (hl : ¬ badLeft F L a b) (hr : ¬ badRight F R a b) :
        ∃ M ⊆ F, #M = 5 ∧ GoodSide F M Prod.fst X L ∧ GoodSide F M Prod.snd Y R := by
      refine ⟨F \ {a, b}, sdiff_subset, delete_pair_five hF da.1 db.1 hab, ?_, ?_⟩
      · exact Or.inl (pair_covered hL da.1 db.1 hab da.2.1 db.2.1 hl)
      · exact Or.inl (pair_covered hR da.1 db.1 hab da.2.2 db.2.2 hr)
    rcases three_good_pair de.1 df.1 dg.1 hef heg hfg with hp | hp | hp
    · exact hpair e f de df hef hp.1 hp.2
    · exact hpair e g de dg heg hp.1 hp.2
    · exact hpair f g df dg hfg hp.1 hp.2
  · by_cases htwo : #K = 2
    · obtain ⟨e, he⟩ := card_pos.mp hpos
      have hposE : 0 < #(K.erase e) := by rw [card_erase_of_mem he, htwo]; norm_num
      obtain ⟨f, hf⟩ := card_pos.mp hposE
      have hfK := (mem_erase.mp hf).2
      have hef : e ≠ f := ((mem_erase.mp hf).1).symm
      have de := hdata e he
      have df := hdata f hfK
      have hleft : 4 ≤ markedCost F Prod.fst L := by
        change 2 * (#(F \ K) : ℤ) ≤ _ at hz
        omega
      have hright : 4 ≤ markedCost F Prod.snd R := by
        change 2 * (#(F \ K) : ℤ) ≤ _ at hz
        omega
      exact ⟨F \ {e, f}, sdiff_subset, delete_pair_five hF de.1 df.1 hef,
        pair_good_side hL hF de.1 df.1 hef de.2.1 df.2.1 hleft,
        pair_good_side hR hF de.1 df.1 hef de.2.2 df.2.2 hright⟩
    · have hone : #K = 1 := by omega
      have hleft : markedCost F Prod.fst L = 6 := by
        change 2 * (#(F \ K) : ℤ) ≤ _ at hz
        omega
      have hright : markedCost F Prod.snd R = 6 := by
        change 2 * (#(F \ K) : ℤ) ≤ _ at hz
        omega
      have hleaves : #(leaves F Prod.fst L) = 3 ∧ #(leaves F Prod.snd R) = 3 := by
        have hcl := leaves_cost hL
        have hcr := leaves_cost hR
        have hc : #(F \ K) ≤ #(leaves F Prod.fst L) + #(leaves F Prod.snd R) := by
          change #(F \ eligible F L R) ≤ _
          rw [ineligible_union]
          have hu := card_union_le (leafEdges F Prod.fst L) (leafEdges F Prod.snd R)
          rwa [leafEdges_card, leafEdges_card] at hu
        omega
      have h2L := no_marked_two hL hleft hleaves.1
      have h2R := no_marked_two hR hright hleaves.2
      obtain ⟨e, he⟩ := card_pos.mp hpos
      have hbadpos : 0 < #(F \ K) := by omega
      obtain ⟨f, hf⟩ := card_pos.mp hbadpos
      have hfF := (mem_sdiff.mp hf).1
      have hef : e ≠ f := fun heq => (mem_sdiff.mp hf).2 (heq ▸ he)
      have de := hdata e he
      exact ⟨F \ {e, f}, sdiff_subset, delete_pair_five hF de.1 hfF hef,
        one_eligible_good_side hL hF de.1 hfF hef de.2.1 h2L hleft,
        one_eligible_good_side hR hF de.1 hfF hef de.2.2 h2R hright⟩

variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem mult_adj_fst {A D : Finset V} {a : V} (ha : a ∈ A) :
    mult (adjPairs G A D) Prod.fst a = dg G D a := card_adjPairs_filter_fst ha

theorem mult_adj_snd {A D : Finset V} {d : V} (hd : d ∈ D) :
    mult (adjPairs G A D) Prod.snd d = dg G A d := card_adjPairs_filter_snd hd

theorem actual_side_left {P Q A C : Finset V} (h : E6Input G P Q A C) :
    SideData (adjPairs G A (Q \ C)) Prod.fst A {a ∈ A | dg G C a = 3} := by
  refine ⟨?_, filter_subset _ _, ?_, ?_, ?_, ?_⟩
  · intro e he
    exact (mem_product.mp (mem_filter.mp he).1).1
  · intro a ha
    rw [mult_adj_fst ha]
    exact (forward_degrees_left h a ha).1
  · intro a ha
    rw [mult_adj_fst (mem_filter.mp ha).1]
    exact (forward_degrees_left h a (mem_filter.mp ha).1).2.1 (mem_filter.mp ha).2
  · intro a ha hc
    refine mem_filter.mpr ⟨ha, ?_⟩
    rw [mult_adj_fst ha] at hc
    exact (forward_degrees_left h a ha).2.2 hc
  · unfold markedCost
    have heq : (∑ a ∈ {a ∈ A | dg G C a = 3},
        (3 - (mult (adjPairs G A (Q \ C)) Prod.fst a : ℤ))) =
        ∑ a ∈ {a ∈ A | dg G C a = 3}, (3 - (dg G (Q \ C) a : ℤ)) := by
      refine sum_congr rfl fun a ha => ?_
      rw [mult_adj_fst (mem_filter.mp ha).1]
    rw [heq]
    exact marked_cost_left h

theorem actual_side_right {P Q A C : Finset V} (h : E6Input G P Q A C) :
    SideData (adjPairs G A (Q \ C)) Prod.snd (Q \ C) {d ∈ Q \ C | dg G (P \ A) d = 3} := by
  refine ⟨?_, filter_subset _ _, ?_, ?_, ?_, ?_⟩
  · intro e he
    exact (mem_product.mp (mem_filter.mp he).1).2
  · intro d hd
    rw [mult_adj_snd hd]
    exact (forward_degrees_right h d hd).1
  · intro d hd
    rw [mult_adj_snd (mem_filter.mp hd).1]
    exact (forward_degrees_right h d (mem_filter.mp hd).1).2.1 (mem_filter.mp hd).2
  · intro d hd hc
    refine mem_filter.mpr ⟨hd, ?_⟩
    rw [mult_adj_snd hd] at hc
    exact (forward_degrees_right h d hd).2.2 hc
  · unfold markedCost
    have heq : (∑ d ∈ {d ∈ Q \ C | dg G (P \ A) d = 3},
        (3 - (mult (adjPairs G A (Q \ C)) Prod.snd d : ℤ))) =
        ∑ d ∈ {d ∈ Q \ C | dg G (P \ A) d = 3}, (3 - (dg G A d : ℤ)) := by
      refine sum_congr rfl fun d hd => ?_
      rw [mult_adj_snd (mem_filter.mp hd).1]
    rw [heq]
    exact marked_cost_right h

theorem goodSide_usable {F M : Finset (V × V)} {r : V × V → V} {A C : Finset V}
    (hcap : ∀ a ∈ A, mult F r a + dg G C a ≤ 6)
    (hgood : GoodSide F M r A {a ∈ A | dg G C a = 3}) :
    UsableFive G A C (mult M r) := by
  rcases hgood with hc | ⟨p, hp, hp0, hu, hb⟩
  · left
    intro a ha hd
    exact hc a (mem_filter.mpr ⟨ha, hd⟩)
  · right
    refine ⟨p, (mem_filter.mp hp).1, (mem_filter.mp hp).2, hp0, ?_, ?_⟩
    · intro a ha hd hz
      exact hu a (mem_filter.mpr ⟨ha, hd⟩) hz
    · have hpoint : ∀ a ∈ A, max 0 (QB6E6.rowWeight G (mult M r) C a) ≤
          pointWeight F M r {a ∈ A | dg G C a = 3} a := by
        intro a ha
        apply max_le_max le_rfl
        by_cases hm : a ∈ {a ∈ A | dg G C a = 3}
        · have hd := (mem_filter.mp hm).2
          simp only [if_pos hm, QB6E6.rowWeight, hd]
          omega
        · simp only [if_neg hm, QB6E6.rowWeight]
          have hc := hcap a ha
          omega
      have he : (∑ a ∈ A.erase p, max 0 (QB6E6.rowWeight G (mult M r) C a)) ≤
          ∑ a ∈ A.erase p, pointWeight F M r {a ∈ A | dg G C a = 3} a :=
        sum_le_sum fun a ha => hpoint a (erase_subset _ _ ha)
      have hsum : (∑ a ∈ A.erase p, pointWeight F M r {a ∈ A | dg G C a = 3} a) ≤
          weightBudget F M r A {a ∈ A | dg G C a = 3} := by
        apply sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
        intro a _ _
        exact le_max_left _ _
      exact (he.trans hsum).trans hb

/-- The full literal physical producer, with no producer premise. -/
theorem actual_five_selection : ActualFiveSelection.{u} := by
  intro V _ G _ P Q A C h
  have hF : #(adjPairs G A (Q \ C)) = 7 := by
    rw [card_adjPairs]
    exact h.forward
  obtain ⟨M, hM, hc, hL, hR⟩ := generic_selection (adjPairs G A (Q \ C)) A (Q \ C)
    {a ∈ A | dg G C a = 3} {d ∈ Q \ C | dg G (P \ A) d = 3}
    hF (actual_side_left h) (actual_side_right h)
  refine ⟨M, hM, hc, goodSide_usable ?_ hL, goodSide_usable ?_ hR⟩
  · intro a ha
    rw [mult_adj_fst ha]
    have hs := dg_sdiff_add (G := G) h.subsetC a
    have hc := h.capP a (h.subsetA ha)
    omega
  · intro d hd
    rw [mult_adj_snd hd]
    have hs := dg_sdiff_add (G := G) h.subsetA d
    have hc := h.capQ d (sdiff_subset hd)
    omega

#print axioms Erdos585.QB6FiveSelection.generic_selection
#print axioms Erdos585.QB6FiveSelection.actual_five_selection
#check Erdos585.QB6FiveSelection.actual_five_selection
example : ActualFiveSelection.{u} := actual_five_selection

end Erdos585.QB6FiveSelection

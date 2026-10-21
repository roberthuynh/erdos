/-
Literal formalization of the reverse-two/forward-seven critical class.
Graph/theta machinery is credited to Openmath.Proofs.QB4 and QB5 and
QB6CoveredFive (Apache-2.0, Robert Huynh, 2026).
-/
import Openmath.Proofs.PaperSupport.QB6CoveredFive
import Openmath.Proofs.PaperSupport.QB6FiveSelection

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
namespace Erdos585.QB7TwoReverse
open QB4 QB5

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every field is literal finite-graph data, not a factor or supplier premise. -/
structure CriticalClass (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D : Finset V) : Prop where
  disjAB : Disjoint A B
  disjCD : Disjoint C D
  disjPQ : Disjoint (A ∪ B) (C ∪ D)
  independentP : ∀ x ∈ A ∪ B, ∀ y ∈ A ∪ B, ¬ G.Adj x y
  independentQ : ∀ x ∈ C ∪ D, ∀ y ∈ C ∪ D, ¬ G.Adj x y
  balanced : #(A ∪ B) = #(C ∪ D)
  minP : ∀ x ∈ A ∪ B, 4 ≤ dg G (C ∪ D) x
  capP : ∀ x ∈ A ∪ B, dg G (C ∪ D) x ≤ 6
  minQ : ∀ x ∈ C ∪ D, 4 ≤ dg G (A ∪ B) x
  capQ : ∀ x ∈ C ∪ D, dg G (A ∪ B) x ≤ 6
  sparse4 : ∀ X ⊆ A ∪ B, ∀ Y ⊆ C ∪ D,
    4 ≤ #X + #Y → #X + #Y < #(A ∪ B) + #(C ∪ D) → 16 ≤ gv G X Y
  sparse3 : ∀ X ⊆ A ∪ B, ∀ Y ⊆ C ∪ D,
    #X + #Y = 3 → 14 ≤ gv G X Y
  imbalanceAC : #A = #C + 2
  imbalanceDB : #D = #B + 2
  saturatedB : ∀ b ∈ B, dg G (C ∪ D) b = 6
  saturatedC : ∀ c ∈ C, dg G (A ∪ B) c = 6
  forward7 : ec G A D = 7
  reverse2 : ec G B C = 2
  potentialAC : gv G A C = 16
  potentialDB : gv G D B = 16
  minA : ∀ a ∈ A, 3 ≤ dg G C a
  minD : ∀ d ∈ D, 3 ≤ dg G B d

/-- Desired public class result: no supplied blocks, omissions, labels or Hall premises. -/
def PhysicalRepair : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D : Finset V), CriticalClass G A B C D → Quartic G (A ∪ B) (C ∪ D)

/-- Literal actual four-by-four adjacency, rather than an abstract success certificate. -/
def HasInternal44 (G : SimpleGraph V) (A C : Finset V) : Prop :=
  ∃ X ⊆ A, ∃ Y ⊆ C, #X = 4 ∧ #Y = 4 ∧ ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y

/-- Actual block inputs of the six-supply argument; size floors are outputs. -/
structure DoubleScarBlock (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V) : Prop where
  disjoint : Disjoint A C
  card : #A = #C + 2
  small : ∀ c ∈ C, 4 ≤ dg G A c ∧ dg G A c ≤ 6
  edges : (ec G A C : ℤ) = 6 * #C - 2
  minA : ∀ a ∈ A, 3 ≤ dg G C a
  capA : ∀ a ∈ A, dg G C a ≤ 6
  sparse4 : ∀ T ⊆ A, ∀ J ⊆ C, 4 ≤ #T + #J → 16 ≤ gv G T J
  sparse3 : ∀ T ⊆ A, ∀ J ⊆ C, #T + #J = 3 → 14 ≤ gv G T J

structure SixData (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V) (m : V → ℕ) : Prop where
  block : DoubleScarBlock G A C
  msum_eq : msum m A = 6
  le_delta : ∀ a ∈ A, m a + dg G C a ≤ 6

/-- The actual small-shore residual degree demand, with the literal column degree. -/
def demand (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C T : Finset V) : ℤ :=
  4 * #T - ∑ c ∈ C, min ((dg G A c : ℤ) - 2) (dg G T c : ℤ)

/-- Complete variable-support omission certificate; this is an output of classification. -/
def GoodOmission (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V) (m : V → ℕ) (p : V) : Prop :=
  p ∈ A ∧ m p = 0 ∧ ∀ T ⊆ A.erase p, demand G A C T ≤ msum m T

/-- Literal equality signature of failure in the no-K4,4 branch. -/
def BetaSignature (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V) (m : V → ℕ) : Prop :=
  ∃ K R J : Finset V, ∃ z : V,
    Disjoint K R ∧ K ∪ R = A ∧ Disjoint J {z} ∧ J ∪ {z} = C ∧
    #R = 4 ∧ #J = #K + 1 ∧ dg G A z = 4 ∧
    (∀ c ∈ J, dg G A c = 6) ∧ (∀ k ∈ K, ¬ G.Adj k z) ∧
    (∀ r ∈ R, G.Adj r z) ∧
    (∀ k ∈ K, 6 - (dg G C k : ℤ) - m k = 0) ∧
    (∀ r ∈ R, 6 - (dg G C r : ℤ) - m r = 2) ∧
    (msum m K = 5 ∨ msum m K = 6) ∧
    msum m R = 6 - msum m K ∧
    (∀ r ∈ R, (dg G J r : ℤ) = 3 - m r)

/-- Exact missing classification; this predicate is not an assumed public input. -/
def SixClassification : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V) (m : V → ℕ), SixData G A C m →
    (∀ a ∈ A, 4 ≤ dg G C a + m a) →
      (¬ ∃ p, GoodOmission G A C m p) →
        HasInternal44 G A C ∨ BetaSignature G A C m


set_option maxHeartbeats 2000000

variable {A B C D T J : Finset V} {m : V → ℕ}

omit [DecidableRel G.Adj] in
lemma quartic_mono {U W U' W' : Finset V} (h : Quartic G U W)
    (hU : U ⊆ U') (hW : W ⊆ W') : Quartic G U' W' := by
  obtain ⟨F, hn, hf, ha, hp, hq⟩ := h
  exact ⟨F, hn, hf.trans (fun x hx => mem_product.mpr ⟨hU (mem_product.mp hx).1, hW (mem_product.mp hx).2⟩), ha, hp, hq⟩

omit [DecidableRel G.Adj] in
lemma quartic_of_internal44 (h : HasInternal44 G A C) : Quartic G A C := by
  obtain ⟨X, hXA, Y, hYC, hX, hY, ha⟩ := h
  obtain ⟨x, hx⟩ : X.Nonempty := card_pos.mp (by omega)
  obtain ⟨y, hy⟩ : Y.Nonempty := card_pos.mp (by omega)
  refine ⟨X ×ˢ Y, ⟨(x,y), mem_product.mpr ⟨hx,hy⟩⟩,
    (fun z hz => mem_product.mpr ⟨hXA (mem_product.mp hz).1, hYC (mem_product.mp hz).2⟩),
    ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxX, hxY⟩ := mem_product.mp hx
    exact ha x.1 hxX x.2 hxY
  · intro u
    by_cases hu : u ∈ X
    · right
      have he : ((X ×ˢ Y).filter fun x => x.1 = u) = {u} ×ˢ Y := by
        ext x
        simp only [mem_filter, mem_product, mem_singleton]
        constructor
        · rintro ⟨⟨_, hy⟩, he⟩
          exact ⟨he, hy⟩
        · rintro ⟨he, hy⟩
          exact ⟨⟨he ▸ hu, hy⟩, he⟩
      rw [he, card_product, card_singleton, one_mul, hY]
    · left
      apply card_eq_zero.mpr
      apply filter_eq_empty_iff.mpr
      intro x hx he
      exact hu (he ▸ (mem_product.mp hx).1)
  · intro v
    by_cases hv : v ∈ Y
    · right
      have he : ((X ×ˢ Y).filter fun x => x.2 = v) = X ×ˢ {v} := by
        ext x
        simp only [mem_filter, mem_product, mem_singleton]
        constructor
        · rintro ⟨⟨hx, _⟩, he⟩
          exact ⟨hx, he⟩
        · rintro ⟨hx, he⟩
          exact ⟨⟨hx, he ▸ hv⟩, he⟩
      rw [he, card_product, card_singleton, mul_one, hX]
    · left
      apply card_eq_zero.mpr
      apply filter_eq_empty_iff.mpr
      intro x hx he
      exact hv (he ▸ (mem_product.mp hx).2)

omit [DecidableEq V] in
lemma DoubleScarBlock.four_le (h : DoubleScarBlock G A C) : 4 ≤ #C := by
  have he : (ec G A C : ℤ) ≤ (#A : ℤ) * #C := by
    exact_mod_cast ec_le_card_mul (G := G) A C
  rw [h.edges] at he
  have hnon : (0 : ℤ) ≤ ec G A C := Nat.cast_nonneg _
  rw [h.edges] at hnon
  have hc : (#A : ℤ) = (#C : ℤ) + 2 := by exact_mod_cast h.card
  rw [hc] at he
  by_contra hn
  have hc3 : #C ≤ 3 := by omega
  interval_cases ht : #C
  all_goals omega

omit [DecidableEq V] in
lemma DoubleScarBlock.six_le (h : DoubleScarBlock G A C) : 6 ≤ #A := by
  have := h.four_le
  have := h.card
  omega

namespace SixData

omit [DecidableEq V] in
lemma msum_le (h : SixData G A C m) (hT : T ⊆ A) : msum m T ≤ 6 :=
  h.msum_eq ▸ msum_mono m hT

omit [DecidableEq V] in
lemma m_le_three (h : SixData G A C m) {a : V} (ha : a ∈ A) : m a ≤ 3 := by
  have := h.le_delta a ha
  have := h.block.minA a ha
  omega

omit [DecidableEq V] in
lemma wsum_eq_eight (h : SixData G A C m) : wsum G m C A = 8 := by
  rw [wsum_eq, h.block.edges, h.msum_eq, h.block.card]
  push_cast
  ring

omit [DecidableEq V] in
lemma row_weight_eq_four (h : SixData G A C m) :
    ∑ a ∈ A, QB6E6.rowWeight G m C a = 4 := by
  rw [← QB6E6.row_weight_sum, h.msum_eq, h.wsum_eq_eight]
  norm_num

omit [DecidableEq V] in
lemma wsum_nonneg' (h : SixData G A C m) (hT : T ⊆ A) : 0 ≤ wsum G m C T :=
  wsum_nonneg h.le_delta hT

end SixData

lemma complement_demand (h : SixData G A C m) (hT : T ⊆ A) :
    demand G A C (A \ T) - msum m (A \ T) = thetaStar G m C T := by
  have hpoint : ∀ c ∈ C,
      min ((dg G A c : ℤ) - 2) (dg G (A \ T) c : ℤ) +
        max 0 ((dg G T c : ℤ) - 2) = (dg G A c : ℤ) - 2 := by
    intro c _
    have hs := dg_sdiff_add (G := G) hT c
    zify at hs
    rcases le_total (dg G T c : ℤ) 2 with hl | hr
    · rw [max_eq_left (by omega), min_eq_left (by omega)]
      omega
    · rw [max_eq_right (by omega), min_eq_right (by omega)]
      omega
  have hsum := sum_congr rfl hpoint
  rw [sum_add_distrib] at hsum
  have hdeg : (∑ c ∈ C, (dg G A c : ℤ)) = (ec G A C : ℤ) := by
    rw [ec_comm]
    simp [ec]
  have hcap : (∑ c ∈ C, ((dg G A c : ℤ) - 2)) = 4 * #C - 2 := by
    rw [sum_sub_distrib, hdeg, h.block.edges, sum_const, nsmul_eq_mul]
    ring
  have hms := msum_sdiff_add m hT
  have hcs := card_sdiff_add_card_eq_card hT
  have hc := h.block.card
  have hm := h.msum_eq
  zify at hc hcs
  unfold demand thetaStar
  linarith

omit [DecidableEq V] in
lemma theta_le_large (h : DoubleScarBlock G A C) (m : V → ℕ)
    (hT : T ⊆ A) (hJ : J ⊆ C) (h4 : 4 ≤ #T + #J) :
    theta G m T J ≤ msum m T - 4 - ((#T : ℤ) - #J) := by
  have hg := h.sparse4 T hT J hJ h4
  have ht := two_mul_theta (G := G) m T J
  linarith

lemma critical_theta_bound (h : DoubleScarBlock G A C) (m : V → ℕ)
    (hT : T ⊆ A) (hJ : J ⊆ C) (h4 : 4 ≤ #T + #J) :
    3 * theta G m T J ≤
      2 * msum m T - wsum G m C T - (ec G T (C \ J) : ℤ) - 4 := by
  have hg := h.sparse4 T hT J hJ h4
  have ht := two_mul_theta (G := G) m T J
  have hb := theta_eq_four_add (G := G) m hJ T
  linarith

omit [DecidableEq V] in
lemma cpr_nonempty (hm : msum m T ≤ 6) (h3 : 3 ≤ #T)
    (hpos : 1 ≤ thetaStar G m C T) : (cpr G C T).Nonempty := by
  rw [nonempty_iff_ne_empty]
  intro he
  rw [← theta_cpr, he] at hpos
  have hz : ec G T ∅ = 0 := by simp [ec, dg]
  simp only [theta, card_empty, hz, CharP.cast_eq_zero, add_zero] at hpos
  omega

lemma kappa_bounds (h : SixData G A C m) (hT : T ⊆ A) (hJ : J ⊆ C)
    (h4 : 4 ≤ #T + #J) (hpos : 1 ≤ theta G m T J) :
    -1 ≤ (#T : ℤ) - #J ∧ (#T : ℤ) - #J ≤ msum m T - 5 := by
  have hb := theta_le_large h.block m hT hJ h4
  have ht := theta_eq_four_add (G := G) m hJ T
  have hw := h.wsum_nonneg' hT
  have he : (0 : ℤ) ≤ ec G T (C \ J) := Nat.cast_nonneg _
  omega

lemma thetaStar_le_two (h : SixData G A C m) (hT : T ⊆ A) (h3 : 3 ≤ #T) :
    thetaStar G m C T ≤ 2 := by
  by_cases hp : 1 ≤ thetaStar G m C T
  · have hne := cpr_nonempty (h.msum_le hT) h3 hp
    have h4 : 4 ≤ #T + #(cpr G C T) := by have := hne.card_pos; omega
    have hb := theta_le_large h.block m hT (cpr_subset C T) h4
    have hk := kappa_bounds h hT (cpr_subset C T) h4 (by rwa [theta_cpr])
    have ht := theta_eq_four_add (G := G) m (cpr_subset (G := G) C T) T
    rw [theta_cpr] at hb ht
    have hw := h.wsum_nonneg' hT
    have he : (0 : ℤ) ≤ ec G T (C \ cpr G C T) := Nat.cast_nonneg _
    have hm := h.msum_le hT
    omega
  · omega

lemma big_supply (h : SixData G A C m) (hT : T ⊆ A) (h3 : 3 ≤ #T)
    (hpos : 1 ≤ thetaStar G m C T) :
    4 ≤ msum m T ∧ -1 ≤ (#T : ℤ) - #(cpr G C T) ∧
      (#T : ℤ) - #(cpr G C T) ≤ msum m T - 5 := by
  have hne := cpr_nonempty (h.msum_le hT) h3 hpos
  have h4 : 4 ≤ #T + #(cpr G C T) := by have := hne.card_pos; omega
  have hk := kappa_bounds h hT (cpr_subset C T) h4 (by rwa [theta_cpr])
  exact ⟨by omega, hk⟩

lemma big_boundary_weight (h : SixData G A C m) (hT : T ⊆ A) (h3 : 3 ≤ #T)
    (hpos : 1 ≤ thetaStar G m C T) :
    7 + (ec G T (C \ cpr G C T) : ℤ) ≤ 2 * msum m T - wsum G m C T := by
  have hne := cpr_nonempty (h.msum_le hT) h3 hpos
  have h4 : 4 ≤ #T + #(cpr G C T) := by have := hne.card_pos; omega
  have hb := critical_theta_bound h.block m hT (cpr_subset C T) h4
  rw [theta_cpr] at hb
  omega


namespace CriticalClass

lemma swap (h : CriticalClass G A B C D) : CriticalClass G D C B A := by
  refine ⟨h.disjCD.symm, h.disjAB.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h.imbalanceDB, h.imbalanceAC, ?_, ?_, ?_, ?_, h.potentialDB,
    h.potentialAC, h.minD, h.minA⟩
  · simpa [union_comm] using h.disjPQ.symm
  · simpa [union_comm] using h.independentQ
  · simpa [union_comm] using h.independentP
  · simpa [union_comm] using h.balanced.symm
  · simpa [union_comm] using h.minQ
  · simpa [union_comm] using h.capQ
  · simpa [union_comm] using h.minP
  · simpa [union_comm] using h.capP
  · intro X hX Y hY h4 hp
    have hx : X ⊆ C ∪ D := by simpa [union_comm] using hX
    have hy : Y ⊆ A ∪ B := by simpa [union_comm] using hY
    have hproper : #Y + #X < #(A ∪ B) + #(C ∪ D) := by
      simpa [union_comm, Nat.add_comm] using hp
    have hh := h.sparse4 Y hy X hx (by omega) hproper
    simpa [gv_comm] using hh
  · intro X hX Y hY h3
    have hx : X ⊆ C ∪ D := by simpa [union_comm] using hX
    have hy : Y ⊆ A ∪ B := by simpa [union_comm] using hY
    have hh := h.sparse3 Y hy X hx (by omega)
    simpa [gv_comm] using hh
  · simpa [union_comm] using h.saturatedC
  · simpa [union_comm] using h.saturatedB
  · simpa [ec_comm] using h.forward7
  · simpa [ec_comm] using h.reverse2

lemma blockAC (h : CriticalClass G A B C D) : DoubleScarBlock G A C := by
  have ha : #A = #C + 2 := h.imbalanceAC
  have he : (ec G A C : ℤ) = 6 * #C - 2 := by
    have hp := h.potentialAC
    have ha' : (#A : ℤ) = (#C : ℤ) + 2 := by exact_mod_cast ha
    unfold gv at hp
    rw [ha'] at hp
    linarith
  refine ⟨h.disjPQ.mono subset_union_left subset_union_left, ha, ?_, he,
    h.minA, ?_, ?_, ?_⟩
  · intro c hc
    have hs := h.saturatedC c hc
    have hd := dg_union_of_disjoint (G := G) h.disjAB c
    have hr : dg G B c ≤ ec G C B := by
      unfold ec
      exact single_le_sum (fun _ _ => Nat.zero_le _) hc
    rw [ec_comm C B, h.reverse2] at hr
    omega
  · intro a ha
    exact (dg_mono (G := G) subset_union_left a).trans (h.capP a (mem_union_left B ha))
  · intro T hT J hJ h4
    have hta := card_le_card hT
    have hjc := card_le_card hJ
    have hcd := h.imbalanceDB
    have hab : #(A ∪ B) = #A + #B := card_union_of_disjoint h.disjAB
    have hcd' : #(C ∪ D) = #C + #D := card_union_of_disjoint h.disjCD
    exact h.sparse4 T (hT.trans subset_union_left) J (hJ.trans subset_union_left)
      h4 (by rw [hab, hcd']; omega)
  · intro T hT J hJ h3
    exact h.sparse3 T (hT.trans subset_union_left) J (hJ.trans subset_union_left) h3

lemma blockDB (h : CriticalClass G A B C D) : DoubleScarBlock G D B := h.swap.blockAC

lemma forward_degreeA (h : CriticalClass G A B C D) {a : V} (ha : a ∈ A) :
    dg G D a ≤ 3 := by
  have hd := dg_union_of_disjoint (G := G) h.disjCD a
  have hmin := h.minA a ha
  have hcap := h.capP a (mem_union_left B ha)
  omega

lemma forward_degreeD (h : CriticalClass G A B C D) {d : V} (hd : d ∈ D) :
    dg G A d ≤ 3 := h.swap.forward_degreeA hd

lemma deficiencyA (h : CriticalClass G A B C D) : df G (C ∪ D) A = 7 := by
  have he : ec G A (C ∪ D) = ec G A C + ec G A D := by
    unfold ec
    simp_rw [dg_union_of_disjoint (G := G) h.disjCD]
    rw [sum_add_distrib]
  rw [df_eq, he, Nat.cast_add, h.blockAC.edges, h.forward7, h.imbalanceAC]
  push_cast
  ring

lemma deficiencyD (h : CriticalClass G A B C D) : df G (A ∪ B) D = 7 := by
  simpa [union_comm] using h.swap.deficiencyA

lemma direct_internal44 (_h : CriticalClass G A B C D)
    (hi : HasInternal44 G A C ∨ HasInternal44 G D B) : Quartic G (A ∪ B) (C ∪ D) := by
  rcases hi with hi | hi
  · exact quartic_mono (quartic_of_internal44 hi) subset_union_left subset_union_left
  · obtain ⟨X, hXD, Y, hYB, hX, hY, hadj⟩ := hi
    have hr : HasInternal44 G B D :=
      ⟨Y, hYB, X, hXD, hY, hX, fun y hy x hx => (hadj x hx y hy).symm⟩
    exact quartic_mono (quartic_of_internal44 hr) subset_union_right subset_union_right

end CriticalClass


lemma DoubleScarBlock.has44_of_card_four (h : DoubleScarBlock G A C) (hc : #C = 4) :
    HasInternal44 G A C := by
  have hac : #A = 6 := by have := h.card; omega
  have hec : ec G A C = 22 := by have := h.edges; omega
  set X : Finset V := A.filter (fun a => dg G C a = 4) with hX
  have hXA : X ⊆ A := filter_subset _ _
  have hdeg4 : ∀ a ∈ X, dg G C a = 4 := fun a ha => (mem_filter.mp ha).2
  have hxsum : ec G X C = 4 * #X := by
    unfold ec
    have hh := sum_congr rfl hdeg4
    simpa [sum_const, smul_eq_mul, Nat.mul_comm] using hh
  have hothers : ∀ a ∈ A \ X, dg G C a ≤ 3 := by
    intro a ha
    have hd := dg_le_card (G := G) C a
    have hn : dg G C a ≠ 4 := by
      intro he
      exact (mem_sdiff.mp ha).2 (mem_filter.mpr ⟨(mem_sdiff.mp ha).1,he⟩)
    omega
  have hysum : ec G (A \ X) C ≤ 3 * #(A \ X) := by
    unfold ec
    have hh := sum_le_sum hothers
    simpa [sum_const, smul_eq_mul, Nat.mul_comm] using hh
  have he := ec_sdiff_add_left (G := G) hXA C
  have hcard := card_sdiff_add_card_eq_card hXA
  rw [hec, hxsum] at he
  have hx4 : 4 ≤ #X := by omega
  obtain ⟨Z, hZX, hZ4⟩ := exists_subset_card_eq hx4
  refine ⟨Z, hZX.trans hXA, C, Subset.rfl, hZ4, hc, ?_⟩
  intro z hz c hcc
  have hd : dg G C z = #C := by rw [hdeg4 z (hZX hz),hc]
  have hall : C.filter (G.Adj z) = C :=
    eq_of_subset_of_card_le (filter_subset _ _) (by change #C ≤ dg G C z; exact hd.ge)
  have hm : c ∈ C.filter (G.Adj z) := hall.symm ▸ hcc
  exact (mem_filter.mp hm).2

lemma SixData.has44_of_all_positive (h : SixData G A C m) (hm : ∀ a ∈ A, 0 < m a) :
    HasInternal44 G A C := by
  have hsum : (#A : ℤ) ≤ msum m A := by
    have hh : (∑ _a ∈ A, (1 : ℤ)) ≤ ∑ a ∈ A, (m a : ℤ) :=
      sum_le_sum fun a ha => by exact_mod_cast hm a ha
    simpa [msum, sum_const, nsmul_eq_mul] using hh
  have ha6 := h.block.six_le
  have hc := h.block.card
  have hms := h.msum_eq
  have hc4 : #C = 4 := by omega
  exact h.block.has44_of_card_four hc4

lemma good_iff_theta (h : SixData G A C m) (p : V) :
    GoodOmission G A C m p ↔
      p ∈ A ∧ ∀ T ⊆ A, p ∈ T → thetaStar G m C T ≤ 0 := by
  constructor
  · rintro ⟨hp,_,hgood⟩
    refine ⟨hp,fun T hT hpT => ?_⟩
    have ht : A \ T ⊆ A.erase p := by
      intro a ha
      refine mem_erase.mpr ⟨?_,(mem_sdiff.mp ha).1⟩
      intro he
      exact (mem_sdiff.mp ha).2 (he ▸ hpT)
    have hg := hgood (A \ T) ht
    have hi := complement_demand h hT
    omega
  · rintro ⟨hp,htheta⟩
    have hpzero : m p = 0 := by
      have hh := htheta {p} (singleton_subset_iff.mpr hp) (mem_singleton_self p)
      rw [thetaStar_singleton] at hh
      omega
    refine ⟨hp,hpzero,fun T hT => ?_⟩
    have hTA := hT.trans (erase_subset p A)
    have hpnot : p ∉ T := fun hh => (mem_erase.mp (hT hh)).1 rfl
    have hpT : p ∈ A \ T := mem_sdiff.mpr ⟨hp,hpnot⟩
    have hh := htheta (A \ T) sdiff_subset hpT
    have hi := complement_demand h (sdiff_subset (s := A) (t := T))
    rw [sdiff_sdiff_right_self, inf_eq_right.mpr hTA] at hi
    omega

lemma failed_cover (h : SixData G A C m) (hbad : ¬ ∃ p, GoodOmission G A C m p) :
    QB6CoveredFive.CoveredByOverloads G A C m := by
  intro p hp
  by_contra! hn
  apply hbad
  refine ⟨p,(good_iff_theta h p).mpr ⟨hp,fun T hT hpT => ?_⟩⟩
  have hh := hn T hT hpT
  omega


lemma thetaStar_le_two_of_two_le (h : SixData G A C m) (hT : T ⊆ A) (h2 : 2 ≤ #T) :
    thetaStar G m C T ≤ 2 := by
  by_cases h3 : 3 ≤ #T
  · exact thetaStar_le_two h hT h3
  · have he : #T = 2 := by omega
    rw [thetaStar_of_card_eq_two m C he]
    have := h.msum_le hT
    omega

lemma merge_two_rows (h : SixData G A C m) {T T' : Finset V}
    (hT : T ⊆ A) (hp : 1 ≤ thetaStar G m C T) (hp' : 1 ≤ thetaStar G m C T')
    (hU : thetaStar G m C (T ∪ T') ≤ 0) (h2 : 2 ≤ #(T ∩ T')) :
    thetaStar G m C (T ∩ T') = 2 ∧ thetaStar G m C T = 1 ∧ thetaStar G m C T' = 1 := by
  have hi := merge_thetaStar_inter hU
  have hb := thetaStar_le_two_of_two_le h (inter_subset_left.trans hT) h2
  omega

lemma zero_row_in_max_big (h : SixData G A C m)
    (hall : QB6CoveredFive.CoveredByOverloads G A C m) {x : V} (hx : x ∈ A) (hmx : m x = 0) :
    ∃ S, IsMaxOver G m A C S ∧ 3 ≤ #S ∧ x ∈ S := by
  obtain ⟨S,hSA,hxS,hpos⟩ := hall x hx
  obtain ⟨T,hST,hT⟩ := exists_isMaxOver hSA hpos
  have hxT := hST hxS
  have ht3 : 3 ≤ #T := by
    by_contra hc
    interval_cases ht : #T
    · have he := card_eq_zero.mp ht
      rw [he] at hxT
      simp at hxT
    · have he : T = {x} := (eq_of_subset_of_card_le
        (singleton_subset_iff.mpr hxT) (by simp [ht])).symm
      have hp := hT.2.1
      rw [he,thetaStar_singleton,hmx] at hp
      norm_num at hp
    · have hp := hT.2.1
      rw [thetaStar_of_card_eq_two m C ht] at hp
      have hs := sum_erase_add T (fun a => (m a : ℤ)) hxT
      change msum m (T.erase x) + (m x : ℤ) = msum m T at hs
      rw [hmx] at hs
      have hce : #(T.erase x) = 1 := by rw [card_erase_of_mem hxT,ht]
      obtain ⟨y,hy⟩ := card_eq_one.mp hce
      rw [hy,msum_singleton] at hs
      have hyA : y ∈ A := hT.1 (erase_subset x T (hy ▸ mem_singleton_self y))
      have := h.m_le_three hyA
      omega
  exact ⟨T,hT,ht3,hxT⟩

lemma no_max_pair (h : SixData G A C m)
    (hall : QB6CoveredFive.CoveredByOverloads G A C m) (hT : IsMaxOver G m A C T) :
    #T ≠ 2 := by
  classical
  intro hT2
  have hmT : msum m T = 5 ∨ msum m T = 6 := by
    have hp := hT.2.1
    rw [thetaStar_of_card_eq_two m C hT2] at hp
    have hb := h.msum_le hT.1
    omega
  obtain ⟨a,b,hab,hTab,hma,hmb⟩ :
      ∃ a b, a ≠ b ∧ T = {a,b} ∧ m a = 3 ∧ (m b = 2 ∨ m b = 3) := by
    obtain ⟨a,b,hab,hTab⟩ := card_eq_two.mp hT2
    have haA := hT.1 (hTab ▸ mem_insert_self a {b})
    have hbA := hT.1 (hTab ▸ mem_insert_of_mem (mem_singleton_self b))
    have hma := h.m_le_three haA
    have hmb := h.m_le_three hbA
    rw [hTab,msum,sum_pair hab] at hmT
    rcases (by omega : m a = 3 ∧ (m b = 2 ∨ m b = 3) ∨
        m b = 3 ∧ (m a = 2 ∨ m a = 3)) with hs | hs
    · exact ⟨a,b,hab,hTab,hs⟩
    · exact ⟨b,a,hab.symm,hTab.trans (pair_comm a b),hs⟩
  have haT : a ∈ T := hTab ▸ mem_insert_self a {b}
  have hbT : b ∈ T := hTab ▸ mem_insert_of_mem (mem_singleton_self b)
  have haA := hT.1 haT
  have hbA := hT.1 hbT
  have hera : msum m (A.erase a) = 3 := by
    have hs := sum_erase_add A (fun x => (m x : ℤ)) haA
    change msum m (A.erase a) + (m a : ℤ) = msum m A at hs
    rw [h.msum_eq,hma] at hs
    omega
  rcases hmb with hmb | hmb
  · have hmt5 : msum m T = 5 := by rw [hTab,msum,sum_pair hab,hma,hmb]; norm_num
    have herb : msum m (A.erase b) = 4 := by
      have hs := sum_erase_add A (fun x => (m x : ℤ)) hbA
      change msum m (A.erase b) + (m b : ℤ) = msum m A at hs
      rw [h.msum_eq,hmb] at hs
      omega
    have bigfacts : ∀ S, IsMaxOver G m A C S → 3 ≤ #S →
        a ∈ S ∧ b ∉ S ∧ msum m S = 4 ∧
        (#S : ℤ) - #(cpr G C S) ≤ -1 := by
      intro S hS hS3
      have hb := big_supply h hS.1 hS3 hS.2.1
      have haS : a ∈ S := by
        by_contra hn
        have hs : S ⊆ A.erase a := fun x hx =>
          mem_erase.mpr ⟨fun he => hn (he ▸ hx),hS.1 hx⟩
        have hm := msum_mono m hs
        omega
      have hbS : b ∉ S := by
        intro hbS
        have ht : T ⊆ S := by rw [hTab]; exact insert_subset haS (singleton_subset_iff.mpr hbS)
        have he := hT.2.2 S hS.1 ht hS.2.1
        rw [he] at hS3
        omega
      have hs : S ⊆ A.erase b := fun x hx =>
        mem_erase.mpr ⟨fun he => hbS (he ▸ hx),hS.1 hx⟩
      have hm := msum_mono m hs
      exact ⟨haS,hbS,by omega,by omega⟩
    have unique_big : ∀ S S', IsMaxOver G m A C S → 3 ≤ #S →
        IsMaxOver G m A C S' → 3 ≤ #S' → S = S' := by
      intro S S' hS hS3 hS' hS3'
      by_contra hne
      obtain ⟨_,hbS,hmS,_⟩ := bigfacts S hS hS3
      obtain ⟨_,hbS',hmS',_⟩ := bigfacts S' hS' hS3'
      have hum : msum m (S ∪ S') ≤ 4 := by
        have hs : S ∪ S' ⊆ A.erase b := fun x hx =>
          mem_erase.mpr ⟨fun he => by
            subst x
            rcases mem_union.mp hx with hx | hx
            · exact hbS hx
            · exact hbS' hx,
            union_subset hS.1 hS'.1 hx⟩
        exact (msum_mono m hs).trans herb.le
      have hms := msum_union_add_inter m S S'
      have him : msum m (S ∩ S') = 4 := by
        have hm : msum m (S ∩ S') ≤ 4 := (msum_mono m inter_subset_left).trans hmS.le
        omega
      have hi2 : 2 ≤ #(S ∩ S') := by
        by_contra hn
        interval_cases hc : #(S ∩ S')
        · rw [card_eq_zero.mp hc,msum_empty] at him
          norm_num at him
        · obtain ⟨v,hv⟩ := card_eq_one.mp hc
          have hvA := hS.1 (inter_subset_left (hv ▸ mem_singleton_self v))
          rw [hv,msum_singleton] at him
          have := h.m_le_three hvA
          omega
      have hu := hS.union_le hS' hne
      have hi : 2 ≤ thetaStar G m C (S ∩ S') := by
        have hh := merge_thetaStar_inter hu
        have h1 := hS.2.1
        have h2 := hS'.2.1
        omega
      by_cases hic : #(S ∩ S') = 2
      · rw [thetaStar_of_card_eq_two m C hic,him] at hi
        norm_num at hi
      · have hi3 : 3 ≤ #(S ∩ S') := by omega
        have hn := cpr_nonempty (G := G) (C := C) (h.msum_le (inter_subset_left.trans hS.1)) hi3 (by omega)
        have h4 : 4 ≤ #(S ∩ S') + #(cpr G C (S ∩ S')) := by have := hn.card_pos; omega
        have hk := kappa_bounds h (inter_subset_left.trans hS.1) (cpr_subset C (S ∩ S'))
          h4 (by rw [theta_cpr]; omega)
        have hh := theta_le_large h.block m (inter_subset_left.trans hS.1)
          (cpr_subset C (S ∩ S')) h4
        rw [theta_cpr,him] at hh
        omega
    by_cases hex : ∃ S, IsMaxOver G m A C S ∧ 3 ≤ #S
    · obtain ⟨S,hS,hS3⟩ := hex
      obtain ⟨_,hbS,hmS,hkap⟩ := bigfacts S hS hS3
      have hcover : A.erase b ⊆ S := by
        intro x hx
        obtain ⟨hxb,hxA⟩ := mem_erase.mp hx
        by_cases hmx : m x = 0
        · obtain ⟨S',hS',hS3',hxS'⟩ := zero_row_in_max_big h hall hxA hmx
          rw [unique_big S' S hS' hS3' hS hS3] at hxS'
          exact hxS'
        · by_contra hxS
          have hs : insert x S ⊆ A.erase b :=
            insert_subset hx (fun y hy => mem_erase.mpr ⟨fun he => hbS (he ▸ hy),hS.1 hy⟩)
          have hh := msum_mono m hs
          rw [msum,sum_insert hxS] at hh
          change (m x : ℤ) + msum m S ≤ msum m (A.erase b) at hh
          omega
      have hsz := card_le_card hcover
      rw [card_erase_of_mem hbA] at hsz
      have hc := card_le_card (cpr_subset (G := G) C S)
      have ha := h.block.card
      omega
    · have hout : ∀ x ∈ A \ T, 0 < m x := by
        intro x hx
        by_contra hn
        have hm0 : m x = 0 := by omega
        obtain ⟨S,hS,hS3,_⟩ := zero_row_in_max_big h hall (mem_sdiff.mp hx).1 hm0
        exact hex ⟨S,hS,hS3⟩
      have hsum : (#(A \ T) : ℤ) ≤ msum m (A \ T) := by
        have hh : (∑ _x ∈ A \ T, (1 : ℤ)) ≤ ∑ x ∈ A \ T, (m x : ℤ) :=
          sum_le_sum fun x hx => by exact_mod_cast hout x hx
        simpa [msum,sum_const,nsmul_eq_mul] using hh
      have hms := msum_sdiff_add m hT.1
      have hcs := card_sdiff_add_card_eq_card hT.1
      have hsix := h.block.six_le
      have hm := h.msum_eq
      omega
  · have herb : msum m (A.erase b) = 3 := by
      have hs := sum_erase_add A (fun x => (m x : ℤ)) hbA
      change msum m (A.erase b) + (m b : ℤ) = msum m A at hs
      rw [h.msum_eq,hmb] at hs
      omega
    have hmt6 : msum m T = 6 := by rw [hTab,msum,sum_pair hab,hma,hmb]; norm_num
    have hmo : msum m (A \ T) = 0 := by
      have hh := msum_sdiff_add m hT.1
      have hm := h.msum_eq
      omega
    have hex : (A \ T).Nonempty := by
      have hc := card_sdiff_add_card_eq_card hT.1
      have hsix := h.block.six_le
      exact card_pos.mp (by omega)
    obtain ⟨x,hx⟩ := hex
    have hmx : m x = 0 := by have hh := le_msum m hx; omega
    obtain ⟨S,hS,hS3,hxS⟩ := zero_row_in_max_big h hall (mem_sdiff.mp hx).1 hmx
    have hb := big_supply h hS.1 hS3 hS.2.1
    have haS : a ∈ S := by
      by_contra hn
      have hs : S ⊆ A.erase a := fun y hy => mem_erase.mpr ⟨fun he => hn (he ▸ hy),hS.1 hy⟩
      have hh := msum_mono m hs
      omega
    have hbS : b ∈ S := by
      by_contra hn
      have hs : S ⊆ A.erase b := fun y hy => mem_erase.mpr ⟨fun he => hn (he ▸ hy),hS.1 hy⟩
      have hh := msum_mono m hs
      omega
    have ht : T ⊆ S := by rw [hTab]; exact insert_subset haS (singleton_subset_iff.mpr hbS)
    have hh := hT.2.2 S hS.1 ht hS.2.1
    exact (mem_sdiff.mp hx).2 (hh ▸ hxS)

lemma max_cases (h : SixData G A C m) (hall : QB6CoveredFive.CoveredByOverloads G A C m)
    (hT : IsMaxOver G m A C T) :
    T = ∅ ∨ (∃ u, T = {u} ∧ 1 ≤ m u) ∨ 3 ≤ #T := by
  rcases lt_or_ge #T 3 with hc | hc
  · have hn2 := no_max_pair h hall hT
    have h1 := hT.2.1
    interval_cases he : #T
    · exact Or.inl (card_eq_zero.1 he)
    · obtain ⟨u, rfl⟩ := card_eq_one.1 he
      rw [thetaStar_singleton] at h1
      exact Or.inr (Or.inl ⟨u, rfl, by exact_mod_cast h1⟩)
    · exact absurd rfl hn2
  · exact Or.inr (Or.inr hc)

lemma inter_of_lt {T' : Finset V} (hT : IsMaxOver G m A C T)
    (hT' : IsMaxOver G m A C T') (hne : T ≠ T') (h2 : #(T ∩ T') < 2) :
    T ∩ T' = ∅ ∨ ∃ v, T ∩ T' = {v} ∧
      thetaStar G m C T + thetaStar G m C T' + #(cpr G C T ∩ cpr G C T') ≤ m v := by
  have hU := hT.union_le hT' hne
  interval_cases hc : #(T ∩ T')
  · exact Or.inl (card_eq_zero.mp hc)
  · obtain ⟨v,hv⟩ := card_eq_one.mp hc
    exact Or.inr ⟨v,hv,merge_N1 hU hv⟩

lemma three_cpr_false (hX : DoubleScarBlock G A C) {T₁ T₂ T₃ : Finset V} (h₁ : T₁ ⊆ A)
    (h₂ : T₂ ⊆ A) (h₃ : T₃ ⊆ A) {v c : V} (h12 : T₁ ∩ T₂ = {v}) (h13 : T₁ ∩ T₃ = {v})
    (h23 : T₂ ∩ T₃ = {v}) (hc : c ∈ C) (hc₁ : 3 ≤ dg G T₁ c) (hc₂ : 3 ≤ dg G T₂ c)
    (hc₃ : 3 ≤ dg G T₃ c) : False := by
  have e1 := dg_union_add_dg_inter (G := G) T₁ T₂ c
  have e2 := dg_union_add_dg_inter (G := G) (T₁ ∪ T₂) T₃ c
  have hi : (T₁ ∪ T₂) ∩ T₃ = {v} := by rw [union_inter_distrib_right, h13, h23, union_self]
  rw [h12] at e1
  rw [hi] at e2
  have hv := dg_le_card (G := G) ({v} : Finset V) c
  rw [card_singleton] at hv
  have hA := dg_mono (G := G) (union_subset (union_subset h₁ h₂) h₃) c
  have hcap := (hX.small c hc).2
  omega

/-- Double counting over a family of subsets of `A`. -/
lemma sum_sum_eq_sum_filter {ℱ : Finset (Finset V)} (hℱ : ∀ T ∈ ℱ, T ⊆ A)
    (F : V → Finset V → ℤ) :
    ∑ T ∈ ℱ, ∑ v ∈ T, F v T = ∑ v ∈ A, ∑ T ∈ ℱ.filter (fun T => v ∈ T), F v T := by
  have h : ∀ T ∈ ℱ, ∑ v ∈ T, F v T = ∑ v ∈ A, if v ∈ T then F v T else 0 := by
    intro T hT
    rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.2 (hℱ T hT)]
  rw [sum_congr rfl h, sum_comm]
  exact sum_congr rfl fun v _ => (sum_filter _ _).symm

/-- If every `c ∈ C` lies in at most `b` of the sets `t T ⊆ C`, then `Σ_T e(v, t T) ≤ b d_v`. -/
lemma sum_dg_le_mul {ℱ : Finset (Finset V)} (t : Finset V → Finset V)
    (ht : ∀ T ∈ ℱ, t T ⊆ C) (b : ℕ) (hb : ∀ c ∈ C, #(ℱ.filter (fun T => c ∈ t T)) ≤ b)
    (v : V) : ∑ T ∈ ℱ, dg G (t T) v ≤ b * dg G C v := by
  have e1 : ∀ T ∈ ℱ, dg G (t T) v = ∑ c ∈ C.filter (G.Adj v), if c ∈ t T then 1 else 0 := by
    intro T hT
    unfold dg
    rw [← card_filter]
    congr 1
    ext c
    simp only [mem_filter]
    constructor
    · rintro ⟨hc, hadj⟩
      exact ⟨⟨ht T hT hc, hadj⟩, hc⟩
    · rintro ⟨⟨_, hadj⟩, hc⟩
      exact ⟨hc, hadj⟩
  calc ∑ T ∈ ℱ, dg G (t T) v
      = ∑ T ∈ ℱ, ∑ c ∈ C.filter (G.Adj v), if c ∈ t T then 1 else 0 := sum_congr rfl e1
    _ = ∑ c ∈ C.filter (G.Adj v), ∑ T ∈ ℱ, if c ∈ t T then 1 else 0 := sum_comm
    _ = ∑ c ∈ C.filter (G.Adj v), #(ℱ.filter (fun T => c ∈ t T)) :=
        sum_congr rfl fun c _ => (card_filter _ _).symm
    _ ≤ ∑ _c ∈ C.filter (G.Adj v), b := sum_le_sum fun c hc => hb c (mem_filter.1 hc).1
    _ = b * dg G C v := by
        rw [sum_const, smul_eq_mul, mul_comm]
        rfl

omit [DecidableEq V] in
/-- `Σ_{v ∈ T} (3m(v) - 6 + e(v, C'(T))) = 3θ*(T) + g(X'(T)) - 12`: the per-member term of
PAPER4 (3.1), `2m(T) - w(T) - ∂_A(X'(T))`. -/
lemma sum_F_eq (m : V → ℕ) (C T : Finset V) :
    ∑ v ∈ T, (3 * (m v : ℤ) - 6 + dg G (cpr G C T) v) =
      3 * thetaStar G m C T + gv G T (cpr G C T) - 12 := by
  have e1 : (ec G T (cpr G C T) : ℤ) = ∑ v ∈ T, (dg G (cpr G C T) v : ℤ) := by
    unfold ec
    push_cast
    rfl
  have e2 : ∑ v ∈ T, (3 * (m v : ℤ) - 6 + dg G (cpr G C T) v) =
      3 * msum m T - 6 * #T + ∑ v ∈ T, (dg G (cpr G C T) v : ℤ) := by
    unfold msum
    rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
    ring
  rw [e2, ← theta_cpr]
  unfold theta gv
  rw [e1]
  ring

/-- Under "no two maximal overloaded sets share two vertices", two of them containing `v` meet
exactly in `{v}`, and Lemma 3.2 (N1) applies at `v`. -/
lemma inter_eq_singleton (_hK : SixData G A C m)
    (hno : ∀ T₁ T₂, IsMaxOver G m A C T₁ → IsMaxOver G m A C T₂ → T₁ ≠ T₂ → #(T₁ ∩ T₂) < 2)
    {T T' : Finset V} (hT : IsMaxOver G m A C T) (hT' : IsMaxOver G m A C T') (hne : T ≠ T')
    {v : V} (hv : v ∈ T) (hv' : v ∈ T') :
    T ∩ T' = {v} ∧
      thetaStar G m C T + thetaStar G m C T' + #(cpr G C T ∩ cpr G C T') ≤ m v := by
  have hvi : v ∈ T ∩ T' := mem_inter.2 ⟨hv, hv'⟩
  rcases inter_of_lt hT hT' hne (hno T T' hT hT' hne) with h | ⟨w, hw, hle⟩
  · rw [h] at hvi
    simp at hvi
  · rw [hw, mem_singleton] at hvi
    subst hvi
    exact ⟨hw, hle⟩

/-- If every vertex of `A` lies in an overloaded set, a vertex in no maximal overloaded set with at
least three elements lies in a singleton member, so `m(v) ≥ 1`. -/
lemma one_le_m_of_not_big (hK : SixData G A C m)
    (hall : QB6CoveredFive.CoveredByOverloads G A C m) {v : V} (hv : v ∈ A)
    (hnb : ∀ T, IsMaxOver G m A C T → 3 ≤ #T → v ∉ T) : 1 ≤ m v := by
  obtain ⟨T, hTA, hvT, h1⟩ := hall v hv
  obtain ⟨T', hsub, hT'⟩ := exists_isMaxOver hTA h1
  have hvT' := hsub hvT
  rcases max_cases hK hall hT' with h | ⟨u, hu, hmu⟩ | h
  · rw [h] at hvT'
    simp at hvT'
  · rw [hu, mem_singleton] at hvT'
    subst hvT'
    exact hmu
  · exact absurd hvT' (hnb T' hT' h)

theorem exists_hub_pair_or_internal44 (hK : SixData G A C m)
    (hall : QB6CoveredFive.CoveredByOverloads G A C m) :
    HasInternal44 G A C ∨
    ∃ T₁ T₂, IsMaxOver G m A C T₁ ∧ IsMaxOver G m A C T₂ ∧ T₁ ≠ T₂ ∧ 2 ≤ #(T₁ ∩ T₂) := by
  classical
  by_cases h44 : HasInternal44 G A C
  · exact Or.inl h44
  right
  by_contra! hno
  -- the big members of the family
  set ℬ : Finset (Finset V) := A.powerset.filter (fun T => IsMaxOver G m A C T ∧ 3 ≤ #T)
    with hℬ
  have memℬ : ∀ T, T ∈ ℬ ↔ IsMaxOver G m A C T ∧ 3 ≤ #T := fun T => by
    rw [hℬ, mem_filter, mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.1.1, h⟩⟩
  have hℬA : ∀ T ∈ ℬ, T ⊆ A := fun T hT => ((memℬ T).1 hT).1.1
  -- the weight identity (3.1)
  have hid := sum_sum_eq_sum_filter hℬA
    (fun v T => 3 * (m v : ℤ) - 6 + dg G (cpr G C T) v)
  have hf0 := hK.row_weight_eq_four
  change (∑ a ∈ A, (3 * (m a : ℤ) - 6 + dg G C a)) = 4 at hf0
  -- lower bound for each big member: 2m(T) - w(T) - ∂_A(X'(T)) ≥ 3 + (g(X'(T)) - 12)
  have hlow : ∀ T ∈ ℬ, 3 + (gv G T (cpr G C T) - 12) ≤
      ∑ v ∈ T, (3 * (m v : ℤ) - 6 + dg G (cpr G C T) v) := by
    intro T hT
    obtain ⟨hTm, hT3⟩ := (memℬ T).1 hT
    have e := sum_F_eq (G := G) m C T
    have h1 := hTm.2.1
    linarith
  have hgnn : ∀ T ∈ ℬ, 4 ≤ gv G T (cpr G C T) - 12 := fun T hT => by
    obtain ⟨hTm, hT3⟩ := (memℬ T).1 hT
    have hn := cpr_nonempty (hK.msum_le hTm.1) hT3 hTm.2.1
    have h4 : 4 ≤ #T + #(cpr G C T) := by have := hn.card_pos; omega
    have := hK.block.sparse4 T hTm.1 (cpr G C T) (cpr_subset C T) h4
    linarith
  -- the bound at a vertex that is not shared by two big members with `m = 3`
  have hvert : ∀ v ∈ A, ¬ (2 ≤ #(ℬ.filter (fun T => v ∈ T)) ∧ m v = 3) →
      ∑ T ∈ ℬ.filter (fun T => v ∈ T), (3 * (m v : ℤ) - 6 + dg G (cpr G C T) v) ≤
        3 * (m v : ℤ) - 6 + dg G C v := by
    intro v hv hnb
    have hd3 := hK.block.minA v hv
    have hm3 := hK.m_le_three hv
    have hsplit : ∑ T ∈ ℬ.filter (fun T => v ∈ T), (3 * (m v : ℤ) - 6 + dg G (cpr G C T) v) =
        (#(ℬ.filter (fun T => v ∈ T)) : ℤ) * (3 * (m v : ℤ) - 6) +
          ∑ T ∈ ℬ.filter (fun T => v ∈ T), (dg G (cpr G C T) v : ℤ) := by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul]
    rw [hsplit]
    rcases Nat.lt_or_ge #(ℬ.filter (fun T => v ∈ T)) 1 with hk | hk
    · -- `v` lies in no big member: it is a singleton member, `m(v) ≥ 1`
      have hk0 : ℬ.filter (fun T => v ∈ T) = ∅ := card_eq_zero.1 (by omega)
      rw [hk0, sum_empty, card_empty]
      have h1 : 1 ≤ m v := one_le_m_of_not_big hK hall hv fun T hT hT3 hvT => by
        have : T ∈ ℬ.filter (fun T => v ∈ T) := mem_filter.2 ⟨(memℬ T).2 ⟨hT, hT3⟩, hvT⟩
        rw [hk0] at this
        simp at this
      push_cast
      omega
    · -- the sets `C'(T)`, `v ∈ T`, are pairwise disjoint (or there is only one)
      have hdisj : ∑ T ∈ ℬ.filter (fun T => v ∈ T), dg G (cpr G C T) v ≤ 1 * dg G C v := by
        refine sum_dg_le_mul (fun T => cpr G C T) (fun T _ => cpr_subset C T) 1
          (fun c _ => ?_) v
        rw [card_le_one]
        intro T₁ h₁ T₂ h₂
        by_contra hne
        rw [mem_filter, mem_filter] at h₁ h₂
        obtain ⟨⟨hT₁ℬ, hvT₁⟩, hc₁⟩ := h₁
        obtain ⟨⟨hT₂ℬ, hvT₂⟩, hc₂⟩ := h₂
        have hT₁m := ((memℬ _).1 hT₁ℬ).1
        have hT₂m := ((memℬ _).1 hT₂ℬ).1
        obtain ⟨-, hle⟩ := inter_eq_singleton hK hno hT₁m hT₂m hne hvT₁ hvT₂
        have hcc : 0 < #(cpr G C T₁ ∩ cpr G C T₂) := card_pos.2 ⟨c, mem_inter.2 ⟨hc₁, hc₂⟩⟩
        have h2 : 1 < #(ℬ.filter (fun T => v ∈ T)) :=
          one_lt_card.2 ⟨T₁, mem_filter.2 ⟨hT₁ℬ, hvT₁⟩, T₂, mem_filter.2 ⟨hT₂ℬ, hvT₂⟩, hne⟩
        have hm2 : m v ≠ 3 := fun h => hnb ⟨h2, h⟩
        have h1 := hT₁m.2.1
        have h1' := hT₂m.2.1
        omega
      have hdisj' : ∑ T ∈ ℬ.filter (fun T => v ∈ T), (dg G (cpr G C T) v : ℤ) ≤ dg G C v := by
        rw [one_mul] at hdisj
        exact_mod_cast hdisj
      have hkm : (#(ℬ.filter (fun T => v ∈ T)) : ℤ) * (3 * (m v : ℤ) - 6) ≤ 3 * (m v : ℤ) - 6 := by
        by_cases hmv : m v = 3
        · have : #(ℬ.filter (fun T => v ∈ T)) = 1 := by
            by_contra h
            exact hnb ⟨by omega, hmv⟩
          rw [this]
          simp
        · have hx : 3 * (m v : ℤ) - 6 ≤ 0 := by omega
          have hk1 : (1 : ℤ) ≤ #(ℬ.filter (fun T => v ∈ T)) := by exact_mod_cast hk
          have := mul_le_mul_of_nonpos_right hk1 hx
          linarith
      linarith
  by_cases hbad : ∃ v₀ ∈ A, 2 ≤ #(ℬ.filter (fun T => v₀ ∈ T)) ∧ m v₀ = 3
  · -- a vertex `v₀` with `m(v₀) = 3` shared by two big members
    obtain ⟨v₀, hv₀, hk₀, hm₀⟩ := hbad
    have hd₀ : dg G C v₀ = 3 := by
      have := hK.le_delta v₀ hv₀
      have := hK.block.minA v₀ hv₀
      omega
    -- every big member contains `v₀`, since it has `m(T) ≥ 4`
    have hall₀ : ∀ T ∈ ℬ, v₀ ∈ T := by
      intro T hT
      obtain ⟨hTm, hT3⟩ := (memℬ T).1 hT
      by_contra hv₀T
      have h2 := (big_supply hK hTm.1 hT3 hTm.2.1).1
      have h3 : msum m T ≤ msum m (A.erase v₀) :=
        msum_mono m fun x hx => mem_erase.2 ⟨fun h => hv₀T (h ▸ hx), hTm.1 hx⟩
      have h4 : msum m (A.erase v₀) + m v₀ = msum m A := by
        unfold msum
        exact sum_erase_add A _ hv₀
      have h5 := hK.msum_eq
      rw [hm₀] at h4
      push_cast at h4
      omega
    -- A second shared row would create a literal two-row intersection.
    have hother : ∀ v ∈ A.erase v₀,
        ∑ T ∈ ℬ.filter (fun T => v ∈ T), (3 * (m v : ℤ) - 6 + dg G (cpr G C T) v) ≤
          3 * (m v : ℤ) - 6 + dg G C v := by
      intro v hv
      obtain ⟨hne,hvA⟩ := mem_erase.mp hv
      refine hvert v hvA fun ⟨hk,_hm⟩ => ?_
      obtain ⟨T₁,h₁,T₂,h₂,h12⟩ := one_lt_card.mp (by omega : 1 < #(ℬ.filter (fun T => v ∈ T)))
      have ht₁ := ((memℬ _).mp (mem_filter.mp h₁).1).1
      have ht₂ := ((memℬ _).mp (mem_filter.mp h₂).1).1
      have hsub : ({v,v₀} : Finset V) ⊆ T₁ ∩ T₂ := by
        apply insert_subset
        · exact mem_inter.mpr ⟨(mem_filter.mp h₁).2,(mem_filter.mp h₂).2⟩
        · exact singleton_subset_iff.mpr (mem_inter.mpr
            ⟨hall₀ _ (mem_filter.mp h₁).1,hall₀ _ (mem_filter.mp h₂).1⟩)
      have hcard := card_le_card hsub
      rw [card_pair hne] at hcard
      have hh := hno T₁ T₂ ht₁ ht₂ h12
      omega
    have hℬv₀ : ℬ.filter (fun T => v₀ ∈ T) = ℬ := filter_true_of_mem hall₀
    rw [hℬv₀] at hk₀
    -- the identity and the bounds at the vertices
    have hsum : ∑ v ∈ A, ∑ T ∈ ℬ.filter (fun T => v ∈ T),
        (3 * (m v : ℤ) - 6 + dg G (cpr G C T) v) ≤
          ∑ T ∈ ℬ, (3 * (m v₀ : ℤ) - 6 + dg G (cpr G C T) v₀) -
            (3 * (m v₀ : ℤ) - 6 + dg G C v₀) + 4 := by
      rw [← add_sum_erase A _ hv₀, hℬv₀]
      have h1 := sum_le_sum hother
      have h2 : ∑ v ∈ A.erase v₀, (3 * (m v : ℤ) - 6 + dg G C v) +
          (3 * (m v₀ : ℤ) - 6 + dg G C v₀) = 4 := by
        rw [sum_erase_add A _ hv₀]
        exact hf0
      linarith
    have hF₀ : ∑ T ∈ ℬ, (3 * (m v₀ : ℤ) - 6 + dg G (cpr G C T) v₀) =
        3 * #ℬ + ∑ T ∈ ℬ, (dg G (cpr G C T) v₀ : ℤ) := by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul, hm₀]
      push_cast
      ring
    have hlowsum : ∑ T ∈ ℬ, (3 + (gv G T (cpr G C T) - 12)) =
        3 * #ℬ + ∑ T ∈ ℬ, (gv G T (cpr G C T) - 12) := by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul]
      ring
    -- a neighbor of `v₀` lies in at most two of the sets `C'(T)`
    have hdg2 : ∑ T ∈ ℬ, dg G (cpr G C T) v₀ ≤ 2 * dg G C v₀ := by
      refine sum_dg_le_mul (fun T => cpr G C T) (fun T _ => cpr_subset C T) 2
        (fun c hc => ?_) v₀
      by_contra! h3
      obtain ⟨T₁, h₁, T₂, h₂, T₃, h₃, h12, h13, h23⟩ := two_lt_card.1 h3
      rw [mem_filter] at h₁ h₂ h₃
      have hT₁m := ((memℬ _).1 h₁.1).1
      have hT₂m := ((memℬ _).1 h₂.1).1
      have hT₃m := ((memℬ _).1 h₃.1).1
      exact three_cpr_false hK.block hT₁m.1 hT₂m.1 hT₃m.1
        (inter_eq_singleton hK hno hT₁m hT₂m h12 (hall₀ _ h₁.1) (hall₀ _ h₂.1)).1
        (inter_eq_singleton hK hno hT₁m hT₃m h13 (hall₀ _ h₁.1) (hall₀ _ h₃.1)).1
        (inter_eq_singleton hK hno hT₂m hT₃m h23 (hall₀ _ h₂.1) (hall₀ _ h₃.1)).1
        hc (mem_cpr.1 h₁.2).2 (mem_cpr.1 h₂.2).2 (mem_cpr.1 h₃.2).2
    have hdg2' : ∑ T ∈ ℬ, (dg G (cpr G C T) v₀ : ℤ) ≤ 6 := by
      rw [hd₀] at hdg2
      exact_mod_cast hdg2
    have hlow' := sum_le_sum hlow
    have hglow : 4 * (#ℬ : ℤ) ≤ ∑ T ∈ ℬ, (gv G T (cpr G C T) - 12) := by
      have hs := sum_le_sum hgnn
      simpa only [sum_const, nsmul_eq_mul, mul_comm] using hs
    rw [hd₀] at hsum
    push_cast at hsum
    linarith
  · have hall' : ∀ v ∈ A,
        ∑ T ∈ ℬ.filter (fun T => v ∈ T), (3 * (m v : ℤ) - 6 + dg G (cpr G C T) v) ≤
          3 * (m v : ℤ) - 6 + dg G C v :=
      fun v hv => hvert v hv fun h => hbad ⟨v, hv, h⟩
    have h1 := sum_le_sum hall'
    have h2 := sum_le_sum hlow
    have h3 : ∑ T ∈ ℬ, (3 + (gv G T (cpr G C T) - 12)) =
        3 * #ℬ + ∑ T ∈ ℬ, (gv G T (cpr G C T) - 12) := by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul]
      ring
    have h4 : 4 * (#ℬ : ℤ) ≤ ∑ T ∈ ℬ, (gv G T (cpr G C T) - 12) := by
      have hs := sum_le_sum hgnn
      simpa only [sum_const, nsmul_eq_mul, mul_comm] using hs
    have hℬ0 : ℬ = ∅ := by
      apply card_eq_zero.1
      have : (#ℬ : ℤ) ≤ 0 := by linarith
      omega
    have hm1 : ∀ v ∈ A, (1 : ℤ) ≤ m v := fun v hv => by
      have := one_le_m_of_not_big hK hall hv fun T hT hT3 hvT => by
        have : T ∈ ℬ := (memℬ T).2 ⟨hT, hT3⟩
        rw [hℬ0] at this
        simp at this
      exact_mod_cast this
    have h5 : ∑ _v ∈ A, (1 : ℤ) ≤ msum m A := sum_le_sum hm1
    rw [sum_const, nsmul_eq_mul, mul_one, hK.msum_eq] at h5
    exact h44 (hK.has44_of_all_positive (fun v hv => by have := hm1 v hv; omega))


variable {K : Finset V}

def columnLoss (G : SimpleGraph V) [DecidableRel G.Adj] (A J : Finset V) : ℤ :=
  6 * #J - ec G A J

omit [DecidableEq V] in
lemma loss_nonneg (h : DoubleScarBlock G A C) (hJ : J ⊆ C) : 0 ≤ columnLoss G A J := by
  have hb : ec G J A ≤ 6 * #J := by
    calc
      ec G J A ≤ ∑ _c ∈ J, 6 := sum_le_sum fun c hc => (h.small c (hJ hc)).2
      _ = 6 * #J := by simp [mul_comm]
  rw [ec_comm] at hb
  unfold columnLoss
  omega

lemma loss_le_two (h : DoubleScarBlock G A C) (hJ : J ⊆ C) : columnLoss G A J ≤ 2 := by
  have hn := loss_nonneg h (sdiff_subset (s := C) (t := J))
  have he := ec_sdiff_add_right (G := G) hJ A
  have hc := card_sdiff_add_card_eq_card hJ
  have hfull := h.edges
  unfold columnLoss at *
  omega

lemma theta_boundary (h : DoubleScarBlock G A C) (m : V → ℕ)
    (hT : T ⊆ A) (hJ : J ⊆ C) :
    theta G m T J = msum m T + 4 - 4 * ((#T : ℤ) - #J) -
      columnLoss G A J - ec G J (A \ T) := by
  have he := ec_sdiff_add_right (G := G) hT J
  have ht := ec_comm (G := G) T J
  have ha := ec_comm (G := G) A J
  have hn := loss_nonneg h hJ
  unfold theta columnLoss at *
  omega

def kpC (G : SimpleGraph V) [DecidableRel G.Adj] (C K : Finset V) : Finset V :=
  {c ∈ C | 2 ≤ dg G K c}

omit [DecidableEq V] in
lemma kpC_subset (C K : Finset V) : kpC G C K ⊆ C := filter_subset _ _

omit [DecidableEq V] in
lemma theta_kpC (m : V → ℕ) (C K : Finset V) :
    theta G m K (kpC G C K) = thetaStar G m C K :=
  theta_eq_thetaStar m (kpC_subset C K) (fun c hc h3 => mem_filter.mpr ⟨hc,by omega⟩)
    (fun c hc => (mem_filter.mp hc).2)

lemma kplus_facts (h : SixData G A C m) (hKA : K ⊆ A) (hK3 : 3 ≤ #K)
    (hKtheta : thetaStar G m C K = 2) :
    wsum G m C K + ec G K (C \ kpC G C K) = 2 + 2 * ((#K : ℤ) - #(kpC G C K)) ∧
    (#K : ℤ) - #(kpC G C K) ≤ msum m K - 6 ∧
    (ec G (kpC G C K) (A \ K) : ℤ) + columnLoss G A (kpC G C K) =
      msum m K + 2 - 4 * ((#K : ℤ) - #(kpC G C K)) ∧
    gv G K (kpC G C K) = 2 * msum m K + 4 - 2 * ((#K : ℤ) - #(kpC G C K)) := by
  have hcp := cpr_nonempty (G := G) (C := C) (h.msum_le hKA) hK3 (by omega)
  have hsub : cpr G C K ⊆ kpC G C K := fun c hc =>
    mem_filter.mpr ⟨(mem_cpr.mp hc).1,by have := (mem_cpr.mp hc).2; omega⟩
  have h4 : 4 ≤ #K + #(kpC G C K) := by
    have hp := hcp.card_pos
    have hl := card_le_card hsub
    omega
  have htheta : theta G m K (kpC G C K) = 2 := (theta_kpC m C K).trans hKtheta
  have h1 := theta_eq_four_add (G := G) m (kpC_subset (G := G) C K) K
  have h2 := theta_le_large h.block m hKA (kpC_subset (G := G) C K) h4
  have h3 := theta_boundary h.block m hKA (kpC_subset (G := G) C K)
  have h4' := two_mul_theta (G := G) m K (kpC G C K)
  rw [htheta] at h1 h2 h3 h4'
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma core_mass (h : SixData G A C m) (hKA : K ⊆ A) (hK2 : 2 ≤ #K)
    (hKtheta : thetaStar G m C K = 2) : 5 ≤ msum m K := by
  by_cases hK3 : 3 ≤ #K
  · obtain ⟨hk1,hk2,_,_⟩ := kplus_facts h hKA hK3 hKtheta
    have hw := h.wsum_nonneg' hKA
    have he : (0 : ℤ) ≤ ec G K (C \ kpC G C K) := Nat.cast_nonneg _
    omega
  · have hc : #K = 2 := by omega
    rw [thetaStar_of_card_eq_two m C hc] at hKtheta
    omega

structure IsHub (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V) (m : V → ℕ) (K : Finset V) : Prop where
  subset : K ⊆ A
  two_le : 2 ≤ #K
  thetaStar_eq : thetaStar G m C K = 2
  maximal : ∀ K' ⊆ A, K ⊆ K' → 2 ≤ thetaStar G m C K' → K' = K
  msum_ge : 5 ≤ msum m K
  big : ∀ T, IsMaxOver G m A C T → 3 ≤ #T →
    K ⊆ T ∧ thetaStar G m C T = 1 ∧ T ≠ K
  inter : ∀ T T', IsMaxOver G m A C T → 3 ≤ #T → IsMaxOver G m A C T' →
    3 ≤ #T' → T ≠ T' → T ∩ T' = K
  exists_big : ∃ T, IsMaxOver G m A C T ∧ 3 ≤ #T
  exists_pair : ∃ T₁ T₂, IsMaxOver G m A C T₁ ∧ 3 ≤ #T₁ ∧
    IsMaxOver G m A C T₂ ∧ 3 ≤ #T₂ ∧ T₁ ≠ T₂

lemma hub_meet_one_false (h : SixData G A C m) (hKA : K ⊆ A)
    (hK2 : 2 ≤ #K) (hKtheta : thetaStar G m C K = 2)
    (hT : IsMaxOver G m A C T) (hT3 : 3 ≤ #T) {a : V} (ha : T ∩ K = {a}) : False := by
  have haT : a ∈ T := (mem_inter.mp (ha ▸ mem_singleton_self a)).1
  have haK : a ∈ K := (mem_inter.mp (ha ▸ mem_singleton_self a)).2
  have haA := hKA haK
  have hKT : ¬ K ⊆ T := fun hh => by
    rw [inter_eq_right.mpr hh] at ha
    rw [ha,card_singleton] at hK2
    omega
  have hU : thetaStar G m C (T ∪ K) ≤ 0 := by
    by_contra hn
    have hh := hT.2.2 (T ∪ K) (union_subset hT.1 hKA) subset_union_left (by omega)
    exact hKT (hh ▸ subset_union_right)
  have h21 := thetaStar_add_le (G := G) m C T K
  rw [ha,thetaStar_singleton] at h21
  have hp := hT.2.1
  have hm3 := h.m_le_three haA
  have hma : m a = 3 := by omega
  have hda : dg G C a = 3 := by
    have := h.le_delta a haA
    have := h.block.minA a haA
    omega
  have hmass := core_mass h hKA hK2 hKtheta
  have hbig := big_supply h hT.1 hT3 hT.2.1
  have hsum := msum_union_add_inter m T K
  rw [ha,msum_singleton,hma] at hsum
  have hcap := h.msum_le (union_subset hT.1 hKA)
  have hmk5 : msum m K = 5 := by omega
  have hmt4 : msum m T = 4 := by omega
  have hK3 : 3 ≤ #K := by
    by_contra hn
    have hc : #K = 2 := by omega
    rw [thetaStar_of_card_eq_two m C hc,hmk5] at hKtheta
    norm_num at hKtheta
  obtain ⟨hk1,hk2,_,hk4⟩ := kplus_facts h hKA hK3 hKtheta
  have hw := h.wsum_nonneg' hKA
  have he : (0 : ℤ) ≤ ec G K (C \ kpC G C K) := Nat.cast_nonneg _
  have hkap : (#K : ℤ) - #(kpC G C K) = -1 := by omega
  have hb0 : ec G K (C \ kpC G C K) = 0 := by omega
  have hdL : dg G (kpC G C K) a = 3 := by
    have hs := dg_sdiff_add (G := G) (kpC_subset (G := G) C K) a
    have hl : dg G (C \ kpC G C K) a ≤ ec G K (C \ kpC G C K) :=
      single_le_sum (f := fun x => dg G (C \ kpC G C K) x) (fun _ _ => Nat.zero_le _) haK
    omega
  have hun := theta_union_add_theta_inter (G := G) m T K (cpr G C T) (kpC G C K)
  rw [theta_cpr,theta_kpC,ha,hKtheta] at hun
  have hle := theta_le_thetaStar (G := G) m
    (union_subset (cpr_subset (G := G) C T) (kpC_subset (G := G) C K)) (T ∪ K)
  have hsing := (theta_singleton (G := G) m a (cpr G C T ∩ kpC G C K)).2
  have hcross : (0 : ℤ) ≤ (ec G (T \ K) (kpC G C K \ cpr G C T) : ℤ) +
      (ec G (K \ T) (cpr G C T \ kpC G C K) : ℤ) := by positivity
  have hJ0 : #(cpr G C T ∩ kpC G C K) = 0 := by
    rw [hma] at hsing
    push_cast at hsing
    have hh : (#(cpr G C T ∩ kpC G C K) : ℤ) ≤ 0 := by linarith
    omega
  have hsub : cpr G C T ⊆ C \ kpC G C K := fun c hc => by
    refine mem_sdiff.mpr ⟨cpr_subset C T hc,fun hck => ?_⟩
    have hh : c ∈ cpr G C T ∩ kpC G C K := mem_inter.mpr ⟨hc,hck⟩
    rw [card_eq_zero.mp hJ0] at hh
    simp at hh
  have hda0 : dg G (cpr G C T) a = 0 := by
    have h1 := dg_mono (G := G) hsub a
    have h2 := dg_sdiff_add (G := G) (kpC_subset (G := G) C K) a
    omega
  have hkapT : (#T : ℤ) - #(cpr G C T) = -1 := by omega
  have h4 : 4 ≤ #(T.erase a) + #(cpr G C T) := by
    rw [card_erase_of_mem haT]
    omega
  have hsp := h.block.sparse4 (T.erase a) ((erase_subset a T).trans hT.1)
    (cpr G C T) (cpr_subset C T) h4
  rw [gv_erase_left haT,hda0] at hsp
  have ht := two_mul_theta (G := G) m T (cpr G C T)
  rw [theta_cpr,hmt4] at ht
  push_cast at hsp
  linarith

theorem isHub_of_pair (hK : SixData G A C m) (hall : QB6CoveredFive.CoveredByOverloads G A C m) {T₁ T₂ : Finset V} (h₁ : IsMaxOver G m A C T₁)
    (h₂ : IsMaxOver G m A C T₂) (hne : T₁ ≠ T₂) (h2 : 2 ≤ #(T₁ ∩ T₂)) :
    IsHub G A C m (T₁ ∩ T₂) := by
  have hU := h₁.union_le h₂ hne
  obtain ⟨hKθ, hθ₁, hθ₂⟩ := merge_two_rows hK h₁.1 h₁.2.1 h₂.2.1 hU h2
  have hKA : T₁ ∩ T₂ ⊆ A := inter_subset_left.trans h₁.1
  -- (a): no set strictly containing `K` has `θ* ≥ 2`
  have hmax : ∀ K' ⊆ A, T₁ ∩ T₂ ⊆ K' → 2 ≤ thetaStar G m C K' → K' = T₁ ∩ T₂ := by
    intro K' hK'A hsub htheta2
    have key : ∀ T, IsMaxOver G m A C T → T₁ ∩ T₂ ⊆ T → thetaStar G m C T = 1 → K' ⊆ T := by
      intro T hT hKT hθT
      have hle := thetaStar_add_le (G := G) m C T K'
      have hi3 : 2 ≤ #(T ∩ K') := h2.trans (card_le_card (subset_inter hKT hsub))
      have hi2 := thetaStar_le_two_of_two_le hK
        ((inter_subset_left (s₂ := K')).trans hT.1) hi3
      have hu1 : 1 ≤ thetaStar G m C (T ∪ K') := by linarith
      have := hT.2.2 (T ∪ K') (union_subset hT.1 hK'A) subset_union_left hu1
      rw [← this]
      exact subset_union_right
    exact Subset.antisymm
      (subset_inter (key T₁ h₁ inter_subset_left hθ₁) (key T₂ h₂ inter_subset_right hθ₂)) hsub
  have hmK : 5 ≤ msum m (T₁ ∩ T₂) := core_mass hK hKA h2 hKθ
  -- (c): every big maximal overloaded set contains `K` and has `θ* = 1`
  have hbig : ∀ T, IsMaxOver G m A C T → 3 ≤ #T →
      T₁ ∩ T₂ ⊆ T ∧ thetaStar G m C T = 1 ∧ T ≠ T₁ ∩ T₂ := by
    intro T hT hT3
    have hsub : T₁ ∩ T₂ ⊆ T := by
      have h2m := (big_supply hK hT.1 hT3 hT.2.1).1
      rcases lt_or_ge #(T ∩ (T₁ ∩ T₂)) 2 with hlt | hge
      · exfalso
        interval_cases hc : #(T ∩ (T₁ ∩ T₂))
        · -- `T` misses `K`: then `m(T) ≤ 5 - m(K) ≤ 1`
          have hdisj : Disjoint T (T₁ ∩ T₂) := disjoint_iff_inter_eq_empty.2 (card_eq_zero.1 hc)
          have e := msum_union_of_disjoint m hdisj
          have := hK.msum_le (union_subset hT.1 hKA)
          omega
        · obtain ⟨a, ha⟩ := card_eq_one.1 hc
          exact hub_meet_one_false hK hKA h2 hKθ hT hT3 ha
      · -- `T` shares at least two vertices with `K`: `T ∪ K` is overloaded
        have hle := thetaStar_add_le (G := G) m C T (T₁ ∩ T₂)
        have hi2 : thetaStar G m C (T ∩ (T₁ ∩ T₂)) ≤ 2 := by
          rcases eq_or_lt_of_le hge with h2 | h2'
          · rw [thetaStar_of_card_eq_two m C h2.symm]
            have := hK.msum_le ((inter_subset_left (s₂ := T₁ ∩ T₂)).trans hT.1)
            linarith
          · exact thetaStar_le_two_of_two_le hK
              ((inter_subset_left (s₂ := T₁ ∩ T₂)).trans hT.1) h2'.le
        have hu1 : 1 ≤ thetaStar G m C (T ∪ (T₁ ∩ T₂)) := by linarith [hT.2.1]
        have := hT.2.2 _ (union_subset hT.1 hKA) subset_union_left hu1
        rw [← this]
        exact subset_union_right
    refine ⟨hsub, ?_, ?_⟩
    · by_cases hT1 : T = T₁
      · rw [hT1]
        exact hθ₁
      · have hU' := hT.union_le h₁ hT1
        have h2' : 2 ≤ #(T ∩ T₁) := h2.trans (card_le_card (subset_inter hsub inter_subset_left))
        exact (merge_two_rows hK hT.1 hT.2.1 h₁.2.1 hU' h2').2.1
    · intro hTK
      have e1 := hT.2.2 T₁ h₁.1 (hTK ▸ inter_subset_left) h₁.2.1
      have e2 := hT.2.2 T₂ h₂.1 (hTK ▸ inter_subset_right) h₂.2.1
      exact hne (e1.trans e2.symm)
  -- (c): two big members meet exactly in `K`
  have hinter : ∀ T T', IsMaxOver G m A C T → 3 ≤ #T → IsMaxOver G m A C T' → 3 ≤ #T' →
      T ≠ T' → T ∩ T' = T₁ ∩ T₂ := by
    intro T T' hT hT3 hT' hT3' hTT'
    obtain ⟨hs, -, -⟩ := hbig T hT hT3
    obtain ⟨hs', -, -⟩ := hbig T' hT' hT3'
    have h2' : 2 ≤ #(T ∩ T') := h2.trans (card_le_card (subset_inter hs hs'))
    have hU' := hT.union_le hT' hTT'
    have hθ := (merge_two_rows hK hT.1 hT.2.1 hT'.2.1 hU' h2').1
    exact hmax (T ∩ T') ((inter_subset_left (s₂ := T')).trans hT.1) (subset_inter hs hs')
      hθ.ge
  have hT₁3 : 3 ≤ #T₁ := by
    have hh := h2.trans (card_le_card (inter_subset_left (s₂ := T₂)))
    have hn := no_max_pair hK hall h₁
    omega
  have hT₂3 : 3 ≤ #T₂ := by
    have hh := h2.trans (card_le_card (inter_subset_right (s₁ := T₁)))
    have hn := no_max_pair hK hall h₂
    omega
  exact ⟨hKA, h2, hKθ, hmax, hmK, hbig, hinter, ⟨T₁, h₁, hT₁3⟩,
    ⟨T₁, T₂, h₁, hT₁3, h₂, hT₂3, hne⟩⟩


lemma theta_S (hub : IsHub G A C m K) {T : Finset V} (hT : IsMaxOver G m A C T)
    (hT3 : 3 ≤ #T) : theta G m T (cpr G C T ∪ kpC G C K) = 1 := by
  obtain ⟨hKT, hθT, -⟩ := hub.big T hT hT3
  rw [← hθT]
  refine theta_eq_thetaStar m (union_subset (cpr_subset C T) (kpC_subset C K))
    (fun c hc h3 => mem_union_left _ (mem_cpr.2 ⟨hc, h3⟩)) fun c hc => ?_
  rcases mem_union.1 hc with h | h
  · have := (mem_cpr.1 h).2
    omega
  · exact (mem_filter.1 h).2.trans (dg_mono hKT c)

/-- **PAPER4 Lemma 3.5 (a) to (c)** for one big member `T` and its petal
`P_T = (T - K, C'(T) - K⁺_C)`: `θ(P_T) = 3 - E_T` with `E_T = e(K, C'(T) - K⁺_C) + e(T - K, K⁺_C)`,
`w(K) + w(T - K) ≤ 3 + 2κ(S_T)` and `κ(S_T) ≤ m(T) - 5`, where
`κ(S_T) = κ(K⁺) + κ(P_T)`, and `T - K ≠ ∅`. -/
lemma petal_facts (hK : SixData G A C m) (hub : IsHub G A C m K) {T : Finset V}
    (hT : IsMaxOver G m A C T) (hT3 : 3 ≤ #T) :
    theta G m (T \ K) (cpr G C T \ kpC G C K) =
        3 - ((ec G K (cpr G C T \ kpC G C K) : ℤ) + ec G (T \ K) (kpC G C K)) ∧
      wsum G m C K + wsum G m C (T \ K) ≤
        3 + 2 * (((#K : ℤ) - #(kpC G C K)) + ((#(T \ K) : ℤ) - #(cpr G C T \ kpC G C K))) ∧
      ((#K : ℤ) - #(kpC G C K)) + ((#(T \ K) : ℤ) - #(cpr G C T \ kpC G C K)) ≤
        msum m K + msum m (T \ K) - 5 ∧
      1 ≤ #(T \ K) ∧
      -1 ≤ ((#K : ℤ) - #(kpC G C K)) + ((#(T \ K) : ℤ) - #(cpr G C T \ kpC G C K)) := by
  obtain ⟨hKT, hθT, hTK⟩ := hub.big T hT hT3
  have hS := theta_S hub hT hT3
  have hJ'C : cpr G C T ∪ kpC G C K ⊆ C := union_subset (cpr_subset C T) (kpC_subset C K)
  -- θ(P_T) = 3 - E_T, from Lemma 2.1(c) for the disjoint `K⁺` and `P_T`
  have hun := theta_union_add_theta_inter (G := G) m K (T \ K) (kpC G C K)
    (cpr G C T \ kpC G C K)
  have e1 : K ∪ (T \ K) = T := union_sdiff_of_subset hKT
  have e2 : kpC G C K ∪ (cpr G C T \ kpC G C K) = cpr G C T ∪ kpC G C K := by
    rw [union_sdiff_self_eq_union, union_comm]
  have e3 : K ∩ (T \ K) = ∅ := inter_sdiff_self K T
  have e4 : kpC G C K ∩ (cpr G C T \ kpC G C K) = ∅ := inter_sdiff_self _ _
  have e5 : K \ (T \ K) = K := by
    ext x
    simp only [mem_sdiff]
    tauto
  have e6 : (cpr G C T \ kpC G C K) \ kpC G C K = cpr G C T \ kpC G C K := by
    ext x
    simp only [mem_sdiff]
    tauto
  have e7 : (T \ K) \ K = T \ K := by
    ext x
    simp only [mem_sdiff]
    tauto
  have e8 : kpC G C K \ (cpr G C T \ kpC G C K) = kpC G C K := by
    ext x
    simp only [mem_sdiff]
    tauto
  rw [e1, e2, e3, e4, e5, e6, e7, e8, hS, theta_empty, theta_kpC, hub.thetaStar_eq] at hun
  -- `h(S_T) = 3 + 2κ(S_T) ≥ w(T)` and `κ(S_T) ≤ m(T) - 5`
  have h4 := theta_eq_four_add (G := G) m hJ'C T
  rw [hS] at h4
  have hw := wsum_sdiff_add (G := G) m C hKT
  have hcT := card_sdiff_add_card_eq_card hKT
  have hcJ : #(cpr G C T \ kpC G C K) + #(kpC G C K) = #(cpr G C T ∪ kpC G C K) :=
    card_sdiff_add_card _ _
  have hec : (0 : ℤ) ≤ ec G T (C \ (cpr G C T ∪ kpC G C K)) := Nat.cast_nonneg _
  have hcp := cpr_nonempty (hK.msum_le hT.1) hT3 hT.2.1
  have hJ1 : 1 ≤ #(cpr G C T ∪ kpC G C K) := by
    have hp := hcp.card_pos
    have hc : #(cpr G C T) ≤ #(cpr G C T ∪ kpC G C K) := card_le_card subset_union_left
    omega
  have hk := kappa_bounds hK hT.1 hJ'C (by omega) (by rw [hS])
  have hmT := msum_sdiff_add m hKT
  have hQ : 1 ≤ #(T \ K) := by
    have : (T \ K).Nonempty := by
      rw [nonempty_iff_ne_empty, Ne, sdiff_eq_empty_iff_subset]
      exact fun h => hTK (Subset.antisymm h hKT)
    exact this.card_pos
  refine ⟨by linarith, ?_, ?_, hQ, ?_⟩
  · have : (#T : ℤ) - #(cpr G C T ∪ kpC G C K) =
        ((#K : ℤ) - #(kpC G C K)) + ((#(T \ K) : ℤ) - #(cpr G C T \ kpC G C K)) := by
      push_cast [← hcT, ← hcJ]
      ring
    linarith
  · have : (#T : ℤ) - #(cpr G C T ∪ kpC G C K) =
        ((#K : ℤ) - #(kpC G C K)) + ((#(T \ K) : ℤ) - #(cpr G C T \ kpC G C K)) := by
      push_cast [← hcT, ← hcJ]
      ring
    linarith [hk.2]
  · have : (#T : ℤ) - #(cpr G C T ∪ kpC G C K) =
        ((#K : ℤ) - #(kpC G C K)) + ((#(T \ K) : ℤ) - #(cpr G C T \ kpC G C K)) := by
      push_cast [← hcT, ← hcJ]
      ring
    linarith [hk.1]

/-- **PAPER4 Lemma 3.5(a)**: the `C`-parts of the petals of two distinct big members are
disjoint, since `θ(S_T ∩ S_T') ≥ 2` and a `C`-vertex outside `K⁺_C` lowers `θ(K⁺)` by at least 1.
-/
lemma petal_J_disjoint (hub : IsHub G A C m K) {T T' : Finset V}
    (hT : IsMaxOver G m A C T) (hT3 : 3 ≤ #T) (hT' : IsMaxOver G m A C T') (hT3' : 3 ≤ #T')
    (hne : T ≠ T') : Disjoint (cpr G C T \ kpC G C K) (cpr G C T' \ kpC G C K) := by
  have hS := theta_S hub hT hT3
  have hS' := theta_S hub hT' hT3'
  have hun := theta_union_add_theta_inter (G := G) m T T' (cpr G C T ∪ kpC G C K)
    (cpr G C T' ∪ kpC G C K)
  have hU := hT.union_le hT' hne
  have hle := theta_le_thetaStar (G := G) m
    (union_subset (union_subset (cpr_subset (G := G) C T) (kpC_subset (G := G) C K))
      (union_subset (cpr_subset (G := G) C T') (kpC_subset (G := G) C K))) (T ∪ T')
  have eZ : (cpr G C T ∪ kpC G C K) ∩ (cpr G C T' ∪ kpC G C K) =
      kpC G C K ∪ ((cpr G C T \ kpC G C K) ∩ (cpr G C T' \ kpC G C K)) := by
    ext x
    simp only [mem_union, mem_inter, mem_sdiff]
    tauto
  have hdisj : Disjoint (kpC G C K) ((cpr G C T \ kpC G C K) ∩ (cpr G C T' \ kpC G C K)) :=
    disjoint_sdiff.mono_right inter_subset_left
  rw [hub.inter T T' hT hT3 hT' hT3' hne, eZ, theta_union_right m K hdisj, theta_kpC,
    hub.thetaStar_eq, hS, hS'] at hun
  -- every `c` in both petals has `e(c, K) ≤ 1`
  have hZ : ∑ c ∈ (cpr G C T \ kpC G C K) ∩ (cpr G C T' \ kpC G C K), ((dg G K c : ℤ) - 2) ≤
      ∑ _c ∈ (cpr G C T \ kpC G C K) ∩ (cpr G C T' \ kpC G C K), (-1 : ℤ) := by
    refine sum_le_sum fun c hc => ?_
    obtain ⟨hcT, hcL⟩ := mem_sdiff.1 (mem_inter.1 hc).1
    have hcC := cpr_subset C T hcT
    have : dg G K c < 2 := by
      by_contra h
      exact hcL (mem_filter.2 ⟨hcC, by omega⟩)
    have : (dg G K c : ℤ) ≤ 1 := by exact_mod_cast (by omega : dg G K c ≤ 1)
    linarith
  rw [sum_const, nsmul_eq_mul, mul_neg_one] at hZ
  have hcross : (0 : ℤ) ≤ (ec G (T \ T') ((cpr G C T' ∪ kpC G C K) \ (cpr G C T ∪ kpC G C K)) :
      ℤ) + (ec G (T' \ T) ((cpr G C T ∪ kpC G C K) \ (cpr G C T' ∪ kpC G C K)) : ℤ) := by
    positivity
  rw [disjoint_iff_inter_eq_empty]
  apply card_eq_zero.1
  have : (#((cpr G C T \ kpC G C K) ∩ (cpr G C T' \ kpC G C K)) : ℤ) ≤ 0 := by linarith
  omega

/-- Scalar images of actual petal data, never a supplied public success premise. -/
structure PetalBudget (q j e m w E kc mc wk : ℤ) : Prop where
  q_pos : 1 ≤ q
  j_nonneg : 0 ≤ j
  e_nonneg : 0 ≤ e
  e_cap : e ≤ q * j
  m_nonneg : 0 ≤ m
  w_nonneg : 0 ≤ w
  w_cap : w ≤ 2 * q
  E_nonneg : 0 ≤ E
  theta : m + 4 - 4*q - 2*j + e = 3-E
  weight : wk+w ≤ 3+2*(kc+(q-j))
  k_lower : -1 ≤ kc+(q-j)
  k_upper : kc+(q-j) ≤ mc+m-5
  m_cap : mc+m ≤ 6
  large : 4 ≤ q+j → 7+(q-j) ≤ E+m
  triple : q+j=3 → 6+(q-j) ≤ E+m

lemma beta_budget {q j e m w E mc : ℤ} (h : PetalBudget q j e m w E (-1) mc 0) :
    0 ≤ 2*(E+m)-3*w ∧
    (2 ≤ q+j → 2 ≤ 2*(E+m)-3*w) ∧
    (2*(E+m)-3*w=0 → q=1 ∧ j=0 ∧ w=2 ∧ E+m=3) := by
  obtain ⟨hq,hj,he,hec,hm,hw,hwc,hE,ht,hW,hkl,hku,hmc,hlarge,hthree⟩ := h
  have hk : 0 ≤ q-j ∧ q-j ≤ 2 := by omega
  by_cases h4 : 4 ≤ q+j
  · have hb := hlarge h4
    have hs : 3 ≤ 2*(E+m)-3*w := by omega
    exact ⟨by omega,fun _ => by omega,fun hz => by omega⟩
  · have hq3 : q ≤ 3 := by omega
    have hj2 : j ≤ 2 := by omega
    interval_cases q <;> interval_cases j <;> norm_num at hec <;> omega

lemma beta_zero_nonsingle {q j e w E : ℤ}
    (h : PetalBudget q j e 0 w E (-1) 5 0) (h2 : 2 ≤ q+j) :
    5 ≤ 2*E-3*w := by
  obtain ⟨hq,hj,he,hec,hm,hw,hwc,hE,ht,hW,hkl,hku,hmc,hlarge,hthree⟩ := h
  have hk : 0 ≤ q-j ∧ q-j ≤ 1 := by omega
  by_cases h4 : 4 ≤ q+j
  · have hb := hlarge h4
    omega
  · have hq3 : q ≤ 3 := by omega
    have hj2 : j ≤ 2 := by omega
    interval_cases q <;> interval_cases j <;> norm_num at hec <;> omega

lemma delta_budget {q j e w E wk : ℤ} (h : PetalBudget q j e 0 w E 0 6 wk)
    (hwk : 0 ≤ wk) :
    w+1 ≤ E ∧ (2 ≤ q+j → w+2 ≤ E) ∧
      (E-w=1 → q=1 ∧ j=0 ∧ w=2 ∧ E=3) := by
  obtain ⟨hq,hj,he,hec,hm,hw,hwc,hE,ht,hW,hkl,hku,hmc,hlarge,hthree⟩ := h
  have hk : -1 ≤ q-j ∧ q-j ≤ 1 := by omega
  by_cases h4 : 4 ≤ q+j
  · have hb := hlarge h4
    have hs : w+3 ≤ E := by omega
    exact ⟨by omega,fun _ => by omega,fun hz => by omega⟩
  · have hq3 : q ≤ 3 := by omega
    have hj2 : j ≤ 2 := by omega
    interval_cases q <;> interval_cases j <;> norm_num at hec <;> omega

lemma gamma_budget {q j e w E : ℤ} (h : PetalBudget q j e 0 w E 1 6 0) : w+2 ≤ E := by
  obtain ⟨hq,hj,he,hec,hm,hw,hwc,hE,ht,hW,hkl,hku,hmc,hlarge,hthree⟩ := h
  have hk : -2 ≤ q-j ∧ q-j ≤ 0 := by omega
  by_cases h4 : 4 ≤ q+j
  · have hb := hlarge h4
    omega
  · have hq3 : q ≤ 3 := by omega
    have hj2 : j ≤ 2 := by omega
    interval_cases q <;> interval_cases j <;> norm_num at hec <;> omega

lemma alpha_budget {q j e w E : ℤ} (h : PetalBudget q j e 0 w E 2 6 0) : w+1 ≤ E := by
  obtain ⟨hq,hj,he,hec,hm,hw,hwc,hE,ht,hW,hkl,hku,hmc,hlarge,hthree⟩ := h
  have hk : -3 ≤ q-j ∧ q-j ≤ -1 := by omega
  by_cases h4 : 4 ≤ q+j
  · have hb := hlarge h4
    omega
  · have hq3 : q ≤ 3 := by omega
    have hj2 : j ≤ 2 := by omega
    interval_cases q <;> interval_cases j <;> norm_num at hec <;> omega

lemma core_tags (h : SixData G A C m) (hub : IsHub G A C m K) :
    let L := kpC G C K
    let k := (#K : ℤ)-#L
    wsum G m C K + ec G K (C \ L) = 2+2*k ∧
    (ec G L (A \ K) : ℤ)+columnLoss G A L = msum m K+2-4*k ∧
    -1 ≤ k ∧ k ≤ 2 ∧
    (0 ≤ k → msum m K=6) ∧
    (1 ≤ k → wsum G m C K=0) ∧
    (k=0 → wsum G m C K ≤ 2) ∧
    (k = -1 → wsum G m C K=0 ∧ ec G K (C \ L)=0) := by
  dsimp only
  have ht : theta G m K (kpC G C K)=2 := (theta_kpC m C K).trans hub.thetaStar_eq
  have h1 := theta_eq_four_add (G := G) m (kpC_subset (G := G) C K) K
  have h2 := theta_boundary h.block m hub.subset (kpC_subset (G := G) C K)
  rw [ht] at h1 h2
  have hw := h.wsum_nonneg' hub.subset
  have hb : (0 : ℤ) ≤ ec G K (C \ kpC G C K) := Nat.cast_nonneg _
  have hm := h.msum_le hub.subset
  have htag : ((#K : ℤ)-#(kpC G C K) ≤ 0) ∨
      (msum m K=6 ∧ wsum G m C K=0 ∧ (#K : ℤ)-#(kpC G C K) ≤ 2) := by
    by_cases h3 : 3 ≤ #K
    · have hk := (kplus_facts h hub.subset h3 hub.thetaStar_eq).2.1
      exact Or.inl (by omega)
    · have hc : #K=2 := by have h2 := hub.two_le; omega
      have ht2 := hub.thetaStar_eq
      rw [thetaStar_of_card_eq_two m C hc] at ht2
      have he : (6 : ℤ) ≤ ec G K C := by
        have hh := sum_le_sum (fun x hx => h.block.minA x (hub.subset hx))
        rw [sum_const,nsmul_eq_mul,hc] at hh
        exact_mod_cast hh
      have hwf := wsum_eq (G := G) m C K
      rw [hc] at hwf
      refine Or.inr ⟨by omega,by omega,?_⟩
      have hj : (0 : ℤ) ≤ #(kpC G C K) := Nat.cast_nonneg _
      omega
  refine ⟨by omega,by omega,by omega,by rcases htag with ht | ⟨_,_,ht⟩ <;> omega,
    ?_,?_,by omega,by omega⟩
  · intro hk
    rcases htag with htag | ⟨ht,_,_⟩
    · by_cases h3 : 3 ≤ #K
      · have hh := (kplus_facts h hub.subset h3 hub.thetaStar_eq).2.1
        omega
      · have h2 := hub.two_le
        have hc : #K=2 := by omega
        have hthe := hub.thetaStar_eq
        rw [thetaStar_of_card_eq_two m C hc] at hthe
        omega
    · exact ht
  · intro hk
    rcases htag with ht | ⟨_,hw,_⟩
    · omega
    · exact hw

noncomputable def overloadFamily (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V) (m : V → ℕ) : Finset (Finset V) := by
  classical
  exact A.powerset.filter (fun T => IsMaxOver G m A C T ∧ 3 ≤ #T)

structure HubAccounts (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V) (m : V → ℕ) (K : Finset V)
    (ℬ : Finset (Finset V)) (U R : Finset V) : Prop where
  family : ℬ=overloadFamily G A C m
  rowUnion : U=ℬ.biUnion (fun T => T \ K)
  leftover : R=A \ (K ∪ U)
  mem_family : ∀ T, T∈ℬ ↔ IsMaxOver G m A C T ∧ 3 ≤ #T
  two_family : 2 ≤ #ℬ
  subset_U : U ⊆ A \ K
  rows_disjoint : (ℬ : Set (Finset V)).PairwiseDisjoint (fun T => T \ K)
  columns_disjoint : (ℬ : Set (Finset V)).PairwiseDisjoint (fun T => cpr G C T \ kpC G C K)
  sum_W : wsum G m C U=∑ T∈ℬ, wsum G m C (T \ K)
  sum_M : msum m U=∑ T∈ℬ, msum m (T \ K)
  sum_C : #U=∑ T∈ℬ, #(T \ K)
  sum_E : (∑ T∈ℬ, ((ec G K (cpr G C T \ kpC G C K) : ℤ)+ec G (T \ K) (kpC G C K)))
    ≤ ec G K (C \ kpC G C K)+ec G (kpC G C K) (A \ K)
  partition_W : wsum G m C R+wsum G m C K+wsum G m C U=8
  partition_M : msum m R+msum m K+msum m U=6
  partition_C : #R+#K+#U=#A
  leftover_mass : (#R : ℤ) ≤ msum m R
  leftover_weight : wsum G m C R ≤ 2*#R
  per_petal : ∀ T∈ℬ,
    PetalBudget (#(T \ K)) (#(cpr G C T \ kpC G C K))
      (ec G (T \ K) (cpr G C T \ kpC G C K)) (msum m (T \ K))
      (wsum G m C (T \ K))
      ((ec G K (cpr G C T \ kpC G C K) : ℤ)+ec G (T \ K) (kpC G C K))
      ((#K : ℤ)-#(kpC G C K)) (msum m K) (wsum G m C K)

lemma hub_accounts (hK : SixData G A C m) (hcov : ∀ a∈A, 4 ≤ dg G C a+m a)
    (hall : QB6CoveredFive.CoveredByOverloads G A C m) (hub : IsHub G A C m K) :
    ∃ ℬ U R, HubAccounts G A C m K ℬ U R := by
  classical
  set L := kpC G C K with hL
  set ℬ : Finset (Finset V) := A.powerset.filter (fun T => IsMaxOver G m A C T ∧ 3 ≤ #T)
    with hℬ
  have memℬ : ∀ T, T ∈ ℬ ↔ IsMaxOver G m A C T ∧ 3 ≤ #T := fun T => by
    rw [hℬ, mem_filter, mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.1.1, h⟩⟩
  have hdQ : (ℬ : Set (Finset V)).PairwiseDisjoint (fun T => T \ K) := by
    intro T hT T' hT' hne
    obtain ⟨hTm, hT3⟩ := (memℬ T).1 (mem_coe.1 hT)
    obtain ⟨hT'm, hT3'⟩ := (memℬ T').1 (mem_coe.1 hT')
    have hi := hub.inter T T' hTm hT3 hT'm hT3' hne
    show Disjoint (T \ K) (T' \ K)
    rw [disjoint_left]
    intro x hx hx'
    rw [mem_sdiff] at hx hx'
    exact hx.2 (hi ▸ mem_inter.2 ⟨hx.1, hx'.1⟩)
  have hdJ : (ℬ : Set (Finset V)).PairwiseDisjoint (fun T => cpr G C T \ L) := by
    intro T hT T' hT' hne
    obtain ⟨hTm, hT3⟩ := (memℬ T).1 (mem_coe.1 hT)
    obtain ⟨hT'm, hT3'⟩ := (memℬ T').1 (mem_coe.1 hT')
    exact petal_J_disjoint hub hTm hT3 hT'm hT3' hne
  set U := ℬ.biUnion (fun T => T \ K) with hU
  set Jall := ℬ.biUnion (fun T => cpr G C T \ L) with hJall
  have hUA : U ⊆ A \ K := fun x hx => by
    obtain ⟨T, hT, hxT⟩ := mem_biUnion.1 hx
    obtain ⟨hxT, hxK⟩ := mem_sdiff.1 hxT
    exact mem_sdiff.2 ⟨((memℬ T).1 hT).1.1 hxT, hxK⟩
  have hJC : Jall ⊆ C \ L := fun x hx => by
    obtain ⟨T, -, hxT⟩ := mem_biUnion.1 hx
    obtain ⟨hxT, hxL⟩ := mem_sdiff.1 hxT
    exact mem_sdiff.2 ⟨cpr_subset C T hxT, hxL⟩
  have sW : wsum G m C U = ∑ T ∈ ℬ, wsum G m C (T \ K) := sum_biUnion hdQ
  have sM : msum m U = ∑ T ∈ ℬ, msum m (T \ K) := sum_biUnion hdQ
  have sC : #U = ∑ T ∈ ℬ, #(T \ K) := card_biUnion hdQ
  have sE1 : ∑ T ∈ ℬ, (ec G K (cpr G C T \ L) : ℤ) ≤ ec G K (C \ L) := by
    have h1 : ∑ T ∈ ℬ, ec G K (cpr G C T \ L) = ec G Jall K := by
      rw [show ec G Jall K = ∑ c ∈ Jall, dg G K c from rfl, sum_biUnion hdJ]
      exact sum_congr rfl fun T _ => ec_comm _ _
    have h2 : ec G Jall K ≤ ec G K (C \ L) := by
      rw [ec_comm K]
      exact ec_mono_left hJC K
    exact_mod_cast h1 ▸ h2
  have sE2 : ∑ T ∈ ℬ, (ec G (T \ K) L : ℤ) ≤ ec G L (A \ K) := by
    have h1 : ∑ T ∈ ℬ, ec G (T \ K) L = ec G U L := by
      rw [show ec G U L = ∑ x ∈ U, dg G L x from rfl, sum_biUnion hdQ]
      rfl
    have h2 : ec G U L ≤ ec G L (A \ K) := by
      rw [ec_comm L]
      exact ec_mono_left hUA L
    exact_mod_cast h1 ▸ h2
  have hKU : Disjoint K U := disjoint_left.2 fun x hxK hxU => (mem_sdiff.1 (hUA hxU)).2 hxK
  have hKUA : K ∪ U ⊆ A := union_subset hub.subset (hUA.trans sdiff_subset)
  have pW := wsum_sdiff_add (G := G) m C hKUA
  rw [wsum_union_of_disjoint m C hKU,hK.wsum_eq_eight] at pW
  have pM := msum_sdiff_add m hKUA
  rw [msum_union_of_disjoint m hKU,hK.msum_eq] at pM
  have pC := card_sdiff_add_card_eq_card hKUA
  rw [card_union_of_disjoint hKU] at pC
  set R := A \ (K ∪ U) with hR
  have hRm : (#R : ℤ) ≤ msum m R := by
    have h1 : ∀ v ∈ R, (1 : ℤ) ≤ m v := by
      intro v hv
      obtain ⟨hvA, hvKU⟩ := mem_sdiff.1 hv
      have : 1 ≤ m v := one_le_m_of_not_big hK hall hvA fun T hT hT3 hvT => by
        apply hvKU
        by_cases hvK : v ∈ K
        · exact mem_union_left _ hvK
        · exact mem_union_right _
            (mem_biUnion.2 ⟨T, (memℬ T).2 ⟨hT, hT3⟩, mem_sdiff.2 ⟨hvT, hvK⟩⟩)
      exact_mod_cast this
    have h2 := sum_le_sum h1
    rw [sum_const, nsmul_eq_mul, mul_one] at h2
    exact h2
  have hRw : wsum G m C R ≤ 2 * #R := wsum_le_two_mul hcov sdiff_subset
  have hB2 : 2 ≤ #ℬ := by
    obtain ⟨T₁,T₂,h₁,h₁3,h₂,h₂3,hne⟩ := hub.exists_pair
    exact Nat.succ_le_of_lt (one_lt_card.2
      ⟨T₁,(memℬ T₁).2 ⟨h₁,h₁3⟩,T₂,(memℬ T₂).2 ⟨h₂,h₂3⟩,hne⟩)
  refine ⟨ℬ,U,R,(by unfold overloadFamily; exact hℬ),hU,hR,memℬ,hB2,hUA,hdQ,hdJ,sW,sM,sC,?_,
    by linarith,by linarith,by omega,hRm,hRw,?_⟩
  · rw [sum_add_distrib]
    linarith
  · intro T hT
    obtain ⟨hTm,hT3⟩ := (memℬ T).1 hT
    obtain ⟨hθ,hw,hκ,hq,hlo⟩ := petal_facts hK hub hTm hT3
    have hKT := (hub.big T hTm hT3).1
    have hQA : T \ K ⊆ A := sdiff_subset.trans hTm.1
    have hHC : cpr G C T \ L ⊆ C := sdiff_subset.trans (cpr_subset C T)
    have hmT := hK.msum_le hTm.1
    have hmTs := msum_sdiff_add m hKT
    have he := ec_le_card_mul (G := G) (T \ K) (cpr G C T \ L)
    dsimp only [L] at he hHC
    refine ⟨by exact_mod_cast hq,by positivity,by positivity,by exact_mod_cast he,
      msum_nonneg m _,hK.wsum_nonneg' hQA,wsum_le_two_mul hcov hQA,by positivity,
      hθ,hw,hlo,hκ,by linarith,?_,?_⟩
    · intro h4
      have hh := theta_le_large hK.block m hQA hHC (by omega)
      unfold theta at hh hθ
      linarith
    · intro h3
      have hg := hK.block.sparse3 (T \ K) hQA (cpr G C T \ kpC G C K) hHC (by omega)
      have hh := two_mul_theta (G := G) m (T \ K) (cpr G C T \ kpC G C K)
      rw [hθ] at hh
      linarith

lemma hub_is_beta (h : SixData G A C m) (hcov : ∀ a∈A,4 ≤ dg G C a+m a)
    (hall : QB6CoveredFive.CoveredByOverloads G A C m) (hub : IsHub G A C m K) :
    (#K : ℤ)-#(kpC G C K) = -1 := by
  classical
  obtain ⟨ℬ,U,R,ac⟩ := hub_accounts h hcov hall hub
  obtain ⟨hk1,hk2,hkl,hku,hm6,hw0,hw2,hwβ⟩ := core_tags h hub
  have hmnR : 0 ≤ msum m R := msum_nonneg m R
  have hmnU : 0 ≤ msum m U := msum_nonneg m U
  have hmK := h.msum_le hub.subset
  have hwr0 : 0 ≤ wsum G m C R := h.wsum_nonneg' (by rw [ac.leftover]; exact sdiff_subset)
  have hn0 := loss_nonneg h.block (kpC_subset (G := G) C K)
  have hB2 : (2 : ℤ) ≤ #ℬ := by exact_mod_cast ac.two_family
  by_contra hn
  have hk0 : 0 ≤ (#K : ℤ)-#(kpC G C K) := by omega
  have hmK6 := hm6 hk0
  have hMR : msum m R=0 := by linarith [ac.partition_M]
  have hMU : msum m U=0 := by linarith [ac.partition_M]
  have hcardR : #R=0 := by have hr := ac.leftover_mass; omega
  have hWR : wsum G m C R=0 := by
    have hr := ac.leftover_weight
    rw [hcardR] at hr
    norm_num at hr
    linarith
  have hmQ0 : ∀ T∈ℬ,msum m (T \ K)=0 :=
    (sum_eq_zero_iff_of_nonneg (fun T _ => msum_nonneg m (T \ K))).mp
      (ac.sum_M ▸ hMU)
  have hW : wsum G m C U+wsum G m C K=8 := by linarith [ac.partition_W]
  have hbound : (∑ T∈ℬ, ((ec G K (cpr G C T \ kpC G C K) : ℤ)+ec G (T \ K) (kpC G C K)))
      ≤ 10-2*((#K : ℤ)-#(kpC G C K))-wsum G m C K-columnLoss G A (kpC G C K) := by
    linarith [ac.sum_E]
  have sumCost : ∀ (c : ℤ),
      (∀ T∈ℬ,wsum G m C (T \ K)+c ≤
        (ec G K (cpr G C T \ kpC G C K) : ℤ)+ec G (T \ K) (kpC G C K)) →
      wsum G m C U+c*#ℬ ≤
        ∑ T∈ℬ, ((ec G K (cpr G C T \ kpC G C K) : ℤ)+ec G (T \ K) (kpC G C K)) := by
    intro c hh
    have hs := sum_le_sum hh
    rw [sum_add_distrib,← ac.sum_W,sum_const,nsmul_eq_mul] at hs
    linarith
  interval_cases hkc : (#K : ℤ)-#(kpC G C K)
  · have hpCost : ∀ T∈ℬ,wsum G m C (T \ K)+1 ≤
        (ec G K (cpr G C T \ kpC G C K) : ℤ)+ec G (T \ K) (kpC G C K) := by
      intro T hT
      have hp := ac.per_petal T hT
      rw [hmQ0 T hT,hmK6,hkc] at hp
      exact (delta_budget hp (h.wsum_nonneg' hub.subset)).1
    have hsc := sumCost 1 hpCost
    have hss : (∑ T∈ℬ, ((ec G K (cpr G C T \ kpC G C K) : ℤ)+
        ec G (T \ K) (kpC G C K)-wsum G m C (T \ K)-1)) ≤ 0 := by
      rw [sum_sub_distrib,sum_sub_distrib,← ac.sum_W,sum_const,nsmul_eq_mul,mul_one]
      linarith
    have hwT : ∀ T∈ℬ,wsum G m C (T \ K)=2 := by
      intro T hT
      have hz : 0 ≤ (ec G K (cpr G C T \ kpC G C K) : ℤ)+
        ec G (T \ K) (kpC G C K)-wsum G m C (T \ K)-1 := by linarith [hpCost T hT]
      have hs := single_le_sum
        (f := fun S => (ec G K (cpr G C S \ kpC G C K) : ℤ)+
          ec G (S \ K) (kpC G C K)-wsum G m C (S \ K)-1)
        (fun S hS => by linarith [hpCost S hS]) hT
      have heq : (ec G K (cpr G C T \ kpC G C K) : ℤ)+
        ec G (T \ K) (kpC G C K)-wsum G m C (T \ K)=1 := by linarith
      have hp := ac.per_petal T hT
      rw [hmQ0 T hT,hmK6,hkc] at hp
      exact ((delta_budget hp (h.wsum_nonneg' hub.subset)).2.2 heq).2.2.1
    have hsW : wsum G m C U=2*#ℬ := by
      rw [ac.sum_W,sum_congr rfl hwT,sum_const,nsmul_eq_mul]
      ring
    have htwo := hw2 rfl
    linarith
  · have hwK0 := hw0 (by omega)
    have hc := sumCost 2 (fun T hT => by
      have hp := ac.per_petal T hT
      rw [hmQ0 T hT,hmK6,hwK0,hkc] at hp
      exact gamma_budget hp)
    linarith
  · have hwK0 := hw0 (by omega)
    have hc := sumCost 1 (fun T hT => by
      have hp := ac.per_petal T hT
      rw [hmQ0 T hT,hmK6,hwK0,hkc] at hp
      exact alpha_budget hp)
    linarith

omit [DecidableEq V] in
lemma row_weight_zero (h : SixData G A C m) (hT : T ⊆ A)
    (hz : wsum G m C T=0) : ∀ a∈T,6-(dg G C a : ℤ)-m a=0 := by
  have hn : ∀ a∈T,0 ≤ 6-(dg G C a : ℤ)-m a := by
    intro a ha
    have hd := h.le_delta a (hT ha)
    omega
  exact (sum_eq_zero_iff_of_nonneg hn).mp hz

omit [DecidableEq V] in
lemma row_weight_two (hcov : ∀ a∈A,4 ≤ dg G C a+m a) (hT : T ⊆ A)
    (hz : wsum G m C T=2*#T) : ∀ a∈T,6-(dg G C a : ℤ)-m a=2 := by
  have hn : ∀ a∈T,0 ≤ 2-(6-(dg G C a : ℤ)-m a) := by
    intro a ha
    have hd := hcov a (hT ha)
    omega
  have hs : (∑ a∈T,(2-(6-(dg G C a : ℤ)-m a)))=0 := by
    rw [sum_sub_distrib,sum_const,nsmul_eq_mul]
    change (#T : ℤ)*2-wsum G m C T=0
    linarith
  intro a ha
  have hzero := (sum_eq_zero_iff_of_nonneg hn).mp hs a ha
  omega

lemma beta_column_of_four (h : DoubleScarBlock G A C) (hKA : K ⊆ A)
    (hk : (#K : ℤ)-#(kpC G C K) = -1) (hR4 : #(A \ K)=4)
    (hb0 : ec G K (C \ kpC G C K)=0) :
    ∃ z, C \ kpC G C K={z} ∧ dg G A z=4 ∧
      (∀ k∈K,¬G.Adj k z) ∧ (∀ r∈A \ K,G.Adj r z) ∧
      columnLoss G A (kpC G C K)=0 := by
  let L := kpC G C K
  have hLC : L ⊆ C := kpC_subset C K
  have hAK := card_sdiff_add_card_eq_card hKA
  have hCL := card_sdiff_add_card_eq_card hLC
  have hC := h.card
  have hCL1 : #(C \ L)=1 := by
    dsimp only [L] at hCL ⊢
    omega
  obtain ⟨z,hz⟩ := card_eq_one.mp hCL1
  have hzC : z∈C := (mem_sdiff.mp (hz ▸ mem_singleton_self z)).1
  have hdK : dg G K z=0 := by
    have he0 : ec G (C \ L) K=0 := by rw [ec_comm]; exact hb0
    rw [hz] at he0
    simpa [ec] using he0
  have hd := (h.small z hzC).1
  have hsplit := dg_sdiff_add (G := G) hKA z
  have hle := dg_le_card (G := G) (A \ K) z
  have hdA : dg G A z=4 := by omega
  have hdR : dg G (A \ K) z=4 := by omega
  have haK : ∀ k∈K,¬G.Adj k z := by
    intro k hkK ha
    have hf : k∈K.filter (G.Adj z) := mem_filter.mpr ⟨hkK,ha.symm⟩
    have hc : #(K.filter (G.Adj z))=0 := hdK
    rw [card_eq_zero.mp hc] at hf
    simp at hf
  have haR : ∀ r∈A \ K,G.Adj r z := by
    have he : (A \ K).filter (G.Adj z)=A \ K :=
      eq_of_subset_of_card_le (filter_subset _ _) (by change #(A \ K) ≤ dg G (A \ K) z; omega)
    intro r hr
    exact (mem_filter.mp (he.symm ▸ hr)).2.symm
  have hLoss : columnLoss G A L=0 := by
    have he := ec_sdiff_add_right (G := G) hLC A
    have hdeg : ec G A (C \ L)=4 := by rw [ec_comm,hz]; simpa [ec] using hdA
    have hefull := h.edges
    unfold columnLoss
    omega
  exact ⟨z,hz,hdA,haK,haR,hLoss⟩

lemma beta_extract (h : SixData G A C m) (hcov : ∀ a∈A,4 ≤ dg G C a+m a)
    (hKA : K ⊆ A) (hk : (#K : ℤ)-#(kpC G C K) = -1)
    (hwK : wsum G m C K=0) (hb0 : ec G K (C \ kpC G C K)=0)
    (hR4 : #(A \ K)=4) (hWR : wsum G m C (A \ K)=8)
    (hmK : 5 ≤ msum m K) : BetaSignature G A C m := by
  let L := kpC G C K
  obtain ⟨z,hz,hdz,haK,haR,hn0⟩ := beta_column_of_four h.block hKA hk hR4 hb0
  have hLC : L ⊆ C := kpC_subset C K
  have hJz : Disjoint L {z} := by rw [← hz]; exact disjoint_sdiff
  have hC : L ∪ {z}=C := by rw [← hz]; exact union_sdiff_of_subset hLC
  have hJ6 : ∀ c∈L,dg G A c=6 := by
    have hs : (∑ c∈L,(6-(dg G A c : ℤ)))=0 := by
      change columnLoss G A L=0 at hn0
      rw [sum_sub_distrib,sum_const,nsmul_eq_mul]
      have he := ec_comm (G := G) A L
      unfold columnLoss at hn0
      rw [← Nat.cast_sum]
      change (#L : ℤ)*6-(ec G L A : ℤ)=0
      omega
    have hn : ∀ c∈L,0 ≤ 6-(dg G A c : ℤ) := by
      intro c hc
      have := (h.block.small c (hLC hc)).2
      omega
    intro c hc
    have hh := (sum_eq_zero_iff_of_nonneg hn).mp hs c hc
    omega
  have hRw : ∀ r∈A \ K,6-(dg G C r : ℤ)-m r=2 :=
    row_weight_two hcov sdiff_subset (by rw [hR4]; norm_num; exact hWR)
  have hKw := row_weight_zero h hKA hwK
  have hms := msum_sdiff_add m hKA
  have hm6 := h.msum_le hKA
  have hJL : #L=#K+1 := by change #(kpC G C K)=#K+1; omega
  refine ⟨K,A \ K,L,z,disjoint_sdiff,union_sdiff_of_subset hKA,hJz,hC,hR4,hJL,
    hdz,hJ6,haK,haR,hKw,hRw,by omega,by linarith [h.msum_eq],?_⟩
  intro r hr
  have hs := dg_sdiff_add (G := G) hLC r
  have hdzr : dg G (C \ L) r=1 := by
    rw [hz]
    change #(({z} : Finset V).filter (G.Adj r))=1
    rw [filter_singleton]
    simp only [haR r hr,if_pos,card_singleton]
  have hw := hRw r hr
  omega

lemma leftover_singleton {ℬ : Finset (Finset V)} {U R : Finset V}
    (h : SixData G A C m) (hall : QB6CoveredFive.CoveredByOverloads G A C m)
    (ac : HubAccounts G A C m K ℬ U R) {v : V} (hv : v∈R) :
    IsMaxOver G m A C {v} := by
  have hR := hv
  rw [ac.leftover] at hR
  obtain ⟨hvA,hvKU⟩ := mem_sdiff.mp hR
  obtain ⟨T,hTA,hvT,hpos⟩ := hall v hvA
  obtain ⟨T',hTT',hT'⟩ := exists_isMaxOver hTA hpos
  have hvT' := hTT' hvT
  rcases max_cases h hall hT' with h0 | ⟨u,hu,_⟩ | h3
  · rw [h0] at hvT'
    simp at hvT'
  · rw [hu,mem_singleton] at hvT'
    subst u
    rwa [hu] at hT'
  · exfalso
    apply hvKU
    by_cases hvK : v∈K
    · exact mem_union_left _ hvK
    · apply mem_union_right
      rw [ac.rowUnion]
      exact mem_biUnion.mpr ⟨T',(ac.mem_family T').mpr ⟨hT',h3⟩,mem_sdiff.mpr ⟨hvT',hvK⟩⟩

lemma hub_beta_signature (h : SixData G A C m) (hcov : ∀ a∈A,4 ≤ dg G C a+m a)
    (hall : QB6CoveredFive.CoveredByOverloads G A C m) (hub : IsHub G A C m K) :
    BetaSignature G A C m := by
  classical
  obtain ⟨ℬ,U,R,ac⟩ := hub_accounts h hcov hall hub
  have hk := hub_is_beta h hcov hall hub
  obtain ⟨hk1,hk2,_,_,_,_,_,hwb⟩ := core_tags h hub
  obtain ⟨hwK,hb0⟩ := hwb hk
  have hmK := h.msum_le hub.subset
  have hmr0 := msum_nonneg m R
  have hmu0 := msum_nonneg m U
  have hn0 := loss_nonneg h.block (kpC_subset (G := G) C K)
  have hRsub : R ⊆ A := by rw [ac.leftover]; exact sdiff_subset
  have hwr0 := h.wsum_nonneg' hRsub
  have hmR1 : msum m R ≤ 1 := by linarith [ac.partition_M,hub.msum_ge]
  have hCR1 : #R ≤ 1 := by have hh:=ac.leftover_mass; omega
  have hWR2 : wsum G m C R ≤ 2 := by have hh:=ac.leftover_weight; omega
  let EP : Finset V → ℤ := fun T => (ec G K (cpr G C T \ kpC G C K) : ℤ)+
    ec G (T \ K) (kpC G C K)
  have hEP : ∑ T∈ℬ,EP T ≤ msum m K+6-columnLoss G A (kpC G C K) := by
    have hh := ac.sum_E
    change ∑ T∈ℬ,EP T ≤ _ at hh
    rw [hk] at hk2
    omega
  have hbudget : ∀ T∈ℬ,0 ≤ 2*(EP T+msum m (T \ K))-3*wsum G m C (T \ K) := by
    intro T hT
    have hp := ac.per_petal T hT
    rw [hk,hwK] at hp
    exact (beta_budget hp).1
  have hslack : ∑ T∈ℬ,(2*(EP T+msum m (T \ K))-3*wsum G m C (T \ K)) ≤
      3*wsum G m C R-2*msum m R-2*columnLoss G A (kpC G C K) := by
    simp_rw [mul_add]
    rw [sum_sub_distrib,sum_add_distrib,← mul_sum,← mul_sum,← mul_sum,
      ← ac.sum_M,← ac.sum_W]
    linarith [ac.partition_M,ac.partition_W]
  have hWout : wsum G m C (A \ K)=8 := by
    have hh := wsum_sdiff_add (G := G) m C hub.subset
    rw [hwK,h.wsum_eq_eight] at hh
    linarith
  by_cases hmR0 : msum m R=0
  · have hCR0 : #R=0 := by have hh:=ac.leftover_mass; omega
    have hWR0 : wsum G m C R=0 := by
      have hh := ac.leftover_weight
      rw [hCR0] at hh
      norm_num at hh
      linarith
    have hs0 : ∑ T∈ℬ,(2*(EP T+msum m (T \ K))-3*wsum G m C (T \ K)) ≤ 0 := by linarith
    have hone : ∀ T∈ℬ,#(T \ K)=1 ∧ #(cpr G C T \ kpC G C K)=0 ∧
        wsum G m C (T \ K)=2 := by
      intro T hT
      have hi := single_le_sum
        (f := fun S => 2*(EP S+msum m (S \ K))-3*wsum G m C (S \ K)) hbudget hT
      have hzero : 2*(EP T+msum m (T \ K))-3*wsum G m C (T \ K)=0 := by linarith [hbudget T hT]
      have hp := ac.per_petal T hT
      rw [hk,hwK] at hp
      obtain ⟨hq,hj,hw,_⟩ := (beta_budget hp).2.2 hzero
      exact ⟨by omega,by omega,hw⟩
    have hsW : wsum G m C U=2*#ℬ := by
      rw [ac.sum_W,sum_congr rfl (fun T hT => (hone T hT).2.2),sum_const,nsmul_eq_mul]
      ring
    have hB4 : #ℬ=4 := by linarith [ac.partition_W]
    have hU4 : #U=4 := by
      rw [ac.sum_C,sum_congr rfl (fun T hT => (hone T hT).1),sum_const,nsmul_eq_mul,mul_one,hB4]
      norm_num
    have hR4 : #(A \ K)=4 := by
      have hh := card_sdiff_add_card_eq_card hub.subset
      have hh' := ac.partition_C
      omega
    exact beta_extract h hcov hub.subset hk hwK hb0 hR4 hWout hub.msum_ge
  · have hmR : msum m R=1 := by omega
    have hmK5 : msum m K=5 := by linarith [hub.msum_ge,ac.partition_M]
    have hmU0 : msum m U=0 := by linarith [ac.partition_M]
    have hCR : #R=1 := by
      by_contra hn
      have hzero : #R=0 := by omega
      have he : R=∅ := card_eq_zero.mp hzero
      rw [he,msum_empty] at hmR
      omega
    have hmQ0 : ∀ T∈ℬ,msum m (T \ K)=0 :=
      (sum_eq_zero_iff_of_nonneg (fun T _ => msum_nonneg m (T \ K))).mp (ac.sum_M ▸ hmU0)
    have hs4 : ∑ T∈ℬ,(2*(EP T+msum m (T \ K))-3*wsum G m C (T \ K)) ≤ 4 := by linarith
    have hone : ∀ T∈ℬ,#(T \ K)=1 ∧ #(cpr G C T \ kpC G C K)=0 := by
      intro T hT
      have hi := single_le_sum
        (f := fun S => 2*(EP S+msum m (S \ K))-3*wsum G m C (S \ K)) hbudget hT
      have hp := ac.per_petal T hT
      rw [hk,hwK,hmK5,hmQ0 T hT] at hp
      have hlt : (#(T \ K) : ℤ)+#(cpr G C T \ kpC G C K)<2 := by
        by_contra hn
        have hh := beta_zero_nonsingle hp (by omega)
        rw [hmQ0 T hT] at hi
        linarith
      have hq := hp.q_pos
      have hj := hp.j_nonneg
      constructor <;> omega
    have hE3 : ∀ T∈ℬ,EP T=3 := by
      intro T hT
      have hp := ac.per_petal T hT
      have ht := hp.theta
      have he := hp.e_cap
      have he0 := hp.e_nonneg
      obtain ⟨hq,hj⟩ := hone T hT
      rw [hq,hj,hmQ0 T hT] at ht
      rw [hq,hj] at he
      norm_num at ht he
      dsimp only [EP]
      omega
    have hsE : ∑ T∈ℬ,EP T=3*#ℬ := by
      rw [sum_congr rfl hE3,sum_const,nsmul_eq_mul]
      ring
    have hUC : #U=#ℬ := by
      rw [ac.sum_C,sum_congr rfl (fun T hT => (hone T hT).1),sum_const,nsmul_eq_mul,mul_one]
      norm_num
    have hWU := wsum_le_two_mul hcov (ac.subset_U.trans sdiff_subset)
    have hB3 : #ℬ=3 := by have hpart := ac.partition_W; omega
    have hU3 : #U=3 := by omega
    have hWU6 : wsum G m C U=6 := by linarith [ac.partition_W]
    have hWR2 : wsum G m C R=2 := by linarith [ac.partition_W]
    have hOut4 : #(A \ K)=4 := by
      have hh := card_sdiff_add_card_eq_card hub.subset
      have hh' := ac.partition_C
      omega
    obtain ⟨z,hz,hdz,_,_,hnJ⟩ := beta_column_of_four h.block hub.subset hk hOut4 hb0
    have hbd11 : ec G (kpC G C K) (A \ K)=11 := by omega
    obtain ⟨u,hu⟩ := card_eq_one.mp hCR
    have huR : u∈R := hu ▸ mem_singleton_self u
    have huA := hRsub huR
    have hUdisR : Disjoint U R := by
      rw [disjoint_left]
      intro x hxU hxR
      rw [ac.leftover] at hxR
      exact (mem_sdiff.mp hxR).2 (mem_union_right K hxU)
    have hUR : U ∪ R=A \ K := by
      ext x
      constructor
      · intro hx
        rcases mem_union.mp hx with hxU | hxR
        · exact ac.subset_U hxU
        · rw [ac.leftover] at hxR
          obtain ⟨hxA,hxn⟩ := mem_sdiff.mp hxR
          exact mem_sdiff.mpr ⟨hxA,fun hxK => hxn (mem_union_left U hxK)⟩
      · intro hx
        obtain ⟨hxA,hxK⟩ := mem_sdiff.mp hx
        by_cases hxU : x∈U
        · exact mem_union_left R hxU
        · apply mem_union_right
          rw [ac.leftover]
          exact mem_sdiff.mpr ⟨hxA,fun hxu => (mem_union.mp hxu).elim hxK hxU⟩
    have hsumEP : (∑ T∈ℬ,EP T)=(ec G U (kpC G C K) : ℤ) := by
      have he0 : ∀ T∈ℬ,ec G K (cpr G C T \ kpC G C K)=0 := by
        intro T hT
        rw [card_eq_zero.mp (hone T hT).2]
        simp [ec,dg]
      have heq : ec G U (kpC G C K)=∑ T∈ℬ,ec G (T \ K) (kpC G C K) := by
        rw [ac.rowUnion]
        exact sum_biUnion ac.rows_disjoint
      have heach : ∀ T∈ℬ,EP T=(ec G (T \ K) (kpC G C K) : ℤ) := by
        intro T hT
        dsimp only [EP]
        rw [he0 T hT]
        norm_num
      rw [sum_congr rfl heach,← Nat.cast_sum,← heq]
    have hUL9 : ec G U (kpC G C K)=9 := by omega
    have hdu2 : dg G (kpC G C K) u=2 := by
      have heq : ec G (U ∪ R) (kpC G C K)=
          ec G U (kpC G C K)+ec G R (kpC G C K) := by
        unfold ec
        rw [sum_union hUdisR]
      rw [hUR,ec_comm (A \ K),hbd11,hUL9,hu] at heq
      simpa [ec] using (by omega : ec G {u} (kpC G C K)=2)
    have hmu1 : m u=1 := by rw [hu] at hmR; simpa [msum] using hmR
    have huK : u∉K := by
      rw [ac.leftover] at huR
      exact fun hh => (mem_sdiff.mp huR).2 (mem_union_left U hh)
    have hKdis : Disjoint K {u} := disjoint_singleton_right.mpr huK
    have hpos : 1 ≤ thetaStar G m C (K ∪ {u}) := by
      have hs : theta G m (K ∪ {u}) (kpC G C K)=1 := by
        have heq : ec G (K ∪ {u}) (kpC G C K)=
            ec G K (kpC G C K)+dg G (kpC G C K) u := by
          unfold ec
          rw [sum_union hKdis,sum_singleton]
        have ht := (theta_kpC m C K).trans hub.thetaStar_eq
        unfold theta at ht ⊢
        rw [msum_union_of_disjoint m hKdis,card_union_of_disjoint hKdis,heq,msum_singleton,card_singleton,hmu1,hdu2]
        push_cast
        linarith
      have hle := theta_le_thetaStar (G := G) m (kpC_subset (G := G) C K) (K ∪ {u})
      omega
    have hmax := leftover_singleton h hall ac (hu ▸ mem_singleton_self u)
    have heq := hmax.2.2 (K ∪ {u}) (union_subset hub.subset (singleton_subset_iff.mpr huA))
      subset_union_right hpos
    have hc := card_union_of_disjoint hKdis
    rw [heq,card_singleton] at hc
    have h2 := hub.two_le
    omega

/-- Unconditional actual six-supply classification, with the direct extraction branch paid. -/
theorem six_classification : SixClassification.{u} := by
  intro V _ G _ A C m h hcov hbad
  have hall := failed_cover h hbad
  rcases exists_hub_pair_or_internal44 h hall with h44 | ⟨T₁,T₂,h₁,h₂,hne,h2⟩
  · exact Or.inl h44
  · exact Or.inr (hub_beta_signature h hcov hall (isHub_of_pair h hall h₁ h₂ hne h2))

open QB6E6Lean

theorem card_supply_six (M : Finset (V × V))
    (hMadj : ∀ e ∈ M, G.Adj e.1 e.2) (hM6 : #M ≤ 6) (T S : Finset V) :
    #{e ∈ M | e.1 ∈ T} + #{e ∈ M | e.2 ∈ S} ≤ 6 + ec G T S := by
  have hu : #({e ∈ M | e.1 ∈ T} ∪ {e ∈ M | e.2 ∈ S}) ≤ 6 :=
    (card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))).trans hM6
  have hi : #({e ∈ M | e.1 ∈ T} ∩ {e ∈ M | e.2 ∈ S}) ≤ ec G T S := by
    rw [← card_adjPairs]
    refine card_le_card fun e he => ?_
    obtain ⟨he1, he2⟩ := mem_inter.1 he
    obtain ⟨heM, heT⟩ := mem_filter.1 he1
    obtain ⟨_, heS⟩ := mem_filter.1 he2
    exact mem_filter.2 ⟨mem_product.2 ⟨heT, heS⟩, hMadj e heM⟩
  have := card_union_add_card_inter {e ∈ M | e.1 ∈ T} {e ∈ M | e.2 ∈ S}
  omega

private lemma ec_union_right (X : Finset V) {S T : Finset V} (h : Disjoint S T) :
    ec G X (S ∪ T) = ec G X S + ec G X T := by
  unfold ec
  rw [← sum_add_distrib]
  exact sum_congr rfl fun x _ => dg_union_of_disjoint h x

private lemma ec_filter_split (X A S : Finset V) :
    ec G {x ∈ X | x ∈ A} S + ec G {x ∈ X | x ∉ A} S = ec G X S :=
  sum_filter_add_sum_filter_not X (· ∈ A) (dg G S)


theorem cut_condition_of_six_pair {P Q A C : Finset V} (hA : A ⊆ P) (hC : C ⊆ Q)
    (hcardB : #(Q \ C) = #(P \ A) + 2)
    (hsatC : ∀ c ∈ C, dg G P c = 6) (hsatB : ∀ b ∈ P \ A, dg G Q b = 6)
    (hreverse : ec G (P \ A) C = 2)
    (M : Finset (V × V)) (hMadj : ∀ e ∈ M, G.Adj e.1 e.2) (hM6 : #M ≤ 6)
    {p q : V} (hq : q ∈ Q \ C)
    (hX : ∀ T ⊆ A.erase p, demand G A C T ≤ (#{e ∈ M | e.1 ∈ T} : ℤ))
    (hY : ∀ S ⊆ (Q \ C).erase q,
      demand G (Q \ C) (P \ A) S ≤ (#{e ∈ M | e.2 ∈ S} : ℤ)) :
    ∀ X ⊆ P.erase p, ∀ Z ⊆ Q.erase q, 4 * #X ≤ ec G X (Q.erase q \ Z) + 4 * #Z := by
  intro X hXsub Z hZsub
  have hqC : q ∉ C := (mem_sdiff.1 hq).2
  set A1 := {x ∈ X | x ∈ A} with hA1def
  set B1 := {x ∈ X | x ∉ A} with hB1def
  set D1 := ((Q \ C).erase q) \ (Z \ C) with hD1def
  have hA1 : A1 ⊆ A.erase p := fun x hx => by
    obtain ⟨hxX, hxA⟩ := mem_filter.1 hx
    exact mem_erase.2 ⟨(mem_erase.1 (hXsub hxX)).1, hxA⟩
  have hB1 : B1 ⊆ P \ A := fun x hx => by
    obtain ⟨hxX, hxA⟩ := mem_filter.1 hx
    exact mem_sdiff.2 ⟨(mem_erase.1 (hXsub hxX)).2, hxA⟩
  have hD1 : D1 ⊆ (Q \ C).erase q := sdiff_subset
  have hZC : Z \ C ⊆ (Q \ C).erase q := fun x hx => by
    obtain ⟨hxZ, hxC⟩ := mem_sdiff.1 hx
    obtain ⟨hxq, hxQ⟩ := mem_erase.1 (hZsub hxZ)
    exact mem_erase.2 ⟨hxq, mem_sdiff.2 ⟨hxQ, hxC⟩⟩
  have hR : Q.erase q \ Z = (C \ Z) ∪ D1 := by
    ext x
    simp only [hD1def, mem_sdiff, mem_erase, mem_union]
    constructor
    · rintro ⟨⟨hxq, hxQ⟩, hxZ⟩
      by_cases hxC : x ∈ C
      · exact Or.inl ⟨hxC, hxZ⟩
      · exact Or.inr ⟨⟨hxq, hxQ, hxC⟩, fun h => hxZ h.1⟩
    · rintro (⟨hxC, hxZ⟩ | ⟨⟨hxq, hxQ, hxC⟩, hx⟩)
      · exact ⟨⟨fun h => hqC (h ▸ hxC), hC hxC⟩, hxZ⟩
      · exact ⟨⟨hxq, hxQ⟩, fun h => hx ⟨h, hxC⟩⟩
  have hdisj : Disjoint (C \ Z) D1 := by
    rw [disjoint_left]
    intro x hx hxD
    exact (mem_sdiff.1 (mem_erase.1 (sdiff_subset hxD)).2).2 (mem_sdiff.1 hx).1
  have hec : ec G X (Q.erase q \ Z) =
      ec G A1 (C \ Z) + ec G A1 D1 + (ec G B1 (C \ Z) + ec G B1 D1) := by
    rw [hR, ← ec_filter_split X A, ec_union_right _ hdisj, ec_union_right _ hdisj]
  have hcX : #A1 + #B1 = #X := card_filter_add_card_filter_not (s := X) (· ∈ A)
  have hcZ : #(Z ∩ C) + #(Z \ C) = #Z := by
    have := card_sdiff_add_card_eq_card (inter_subset_left : Z ∩ C ⊆ Z)
    rw [sdiff_inter_self_left] at this
    omega
  have hcD : #D1 + #(Z \ C) + 1 = #(Q \ C) := by
    have h1 := card_sdiff_add_card_eq_card hZC
    have h2 := card_erase_add_one hq
    rw [← hD1def] at h1
    omega
  have hcapB : ∀ K ⊆ P \ A,
      (∑ b ∈ K, ((dg G (Q \ C) b : ℤ) - 2)) = 4 * #K - ec G K C := by
    intro K hK
    have hp : ∀ b ∈ K, (dg G (Q \ C) b : ℤ) - 2 = 4 - (dg G C b : ℤ) := by
      intro b hb
      have hs := dg_sdiff_add (G := G) hC b
      have h6 := hsatB b (hK hb)
      omega
    rw [sum_congr rfl hp, sum_sub_distrib, sum_const, nsmul_eq_mul]
    simp [ec, mul_comm]
  have hcap1 := sum_min_scar_left hA hsatC A1 Z
  have hcap2 := sum_min_scar_right (G := G) (D := Q \ C) hB1 D1
  rw [hcapB _ Subset.rfl, hcapB _ hB1, hreverse] at hcap2
  norm_num only [Nat.cast_ofNat] at hcap2
  have hsup := card_supply_six M hMadj hM6 A1 D1
  have hrev := reverse_set_payment (G := G) (C := C) hB1 Z
  have hdX := hX A1 hA1
  have hdY := hY D1 hD1
  rw [inter_comm] at hcap1 hrev
  unfold demand at hdX hdY
  zify at hec hcX hcZ hcD hcardB hsup hrev ⊢
  linarith


def markedLeaves (G : SimpleGraph V) [DecidableRel G.Adj] (A C D : Finset V) : Finset V :=
  {a∈A | dg G C a=3 ∧ dg G D a=1}

def eligibleLabels (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C D : Finset V) : Finset (V × V) :=
  {e∈adjPairs G A D | e.1∉markedLeaves G A C D ∧ e.2∉markedLeaves G D B A}

def GoodLabel (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C D : Finset V) (e : V × V) : Prop :=
  ∃ p,GoodOmission G A C (mult ((adjPairs G A D).erase e) Prod.fst) p

lemma mult_erase {F : Finset (V × V)} {e : V × V} (he : e∈F)
    (r : V × V → V) (a : V) :
    mult (F.erase e) r a+(if r e=a then 1 else 0)=mult F r a := by
  unfold mult
  rw [filter_erase]
  by_cases h : r e=a
  · rw [if_pos h]
    exact card_erase_add_one (mem_filter.mpr ⟨he,h⟩)
  · rw [if_neg h,add_zero,erase_eq_self.mpr (by intro hh; exact h (mem_filter.mp hh).2)]

lemma mult_forward {a : V} (ha : a∈A) : mult (adjPairs G A D) Prod.fst a=dg G D a := by
  have heq : (adjPairs G A D).filter (fun e => e.1=a)=adjPairs G {a} D := by
    ext e
    simp only [adjPairs,mem_filter,mem_product,mem_singleton]
    constructor
    · rintro ⟨⟨⟨_,heD⟩,hadj⟩,he⟩
      exact ⟨⟨he,heD⟩,hadj⟩
    · rintro ⟨⟨he,heD⟩,hadj⟩
      exact ⟨⟨⟨he ▸ ha,heD⟩,hadj⟩,he⟩
  unfold mult
  rw [heq,card_adjPairs]
  simp [ec]

lemma deleted_row_weight {a : V} (hc : CriticalClass G A B C D) {e : V × V}
    (he : e∈adjPairs G A D) (ha : a∈A) :
    6-(dg G C a : ℤ)-mult ((adjPairs G A D).erase e) Prod.fst a =
      6-(dg G (C ∪ D) a : ℤ)+(if e.1=a then 1 else 0) := by
  have hs := dg_union_of_disjoint (G := G) hc.disjCD a
  have hd := mult_erase he Prod.fst a
  rw [mult_forward ha] at hd
  by_cases haE : e.1=a <;> simp only [haE,if_true,if_false] at * <;> omega

lemma selected_six_data (hc : CriticalClass G A B C D) {e : V × V}
    (he : e∈adjPairs G A D) (hel : e.1∉markedLeaves G A C D) :
    SixData G A C (mult ((adjPairs G A D).erase e) Prod.fst) ∧
      (∀ a∈A,4 ≤ dg G C a+mult ((adjPairs G A D).erase e) Prod.fst a) := by
  have h6 : #((adjPairs G A D).erase e)=6 := by
    rw [card_erase_of_mem he,card_adjPairs,hc.forward7]
  have hends : ∀ x∈(adjPairs G A D).erase e,x.1∈A := by
    intro x hx
    exact (mem_product.mp (mem_filter.mp ((erase_subset e _) hx)).1).1
  have hm6 : msum (mult ((adjPairs G A D).erase e) Prod.fst) A=6 := by
    rw [msum_mult_eq,filter_eq_self.mpr hends,h6]
    norm_num
  have hcap : ∀ a∈A,mult ((adjPairs G A D).erase e) Prod.fst a+dg G C a ≤ 6 := by
    intro a ha
    have hm := mult_fst_le_degree (G := G) (erase_subset e (adjPairs G A D)) a
    have hs := dg_union_of_disjoint (G := G) hc.disjCD a
    have hb := hc.capP a (mem_union_left B ha)
    omega
  refine ⟨⟨hc.blockAC,hm6,hcap⟩,?_⟩
  intro a ha
  have hmin := hc.minA a ha
  have hma := hc.minP a (mem_union_left B ha)
  have hs := dg_union_of_disjoint (G := G) hc.disjCD a
  have hd := mult_erase he Prod.fst a
  rw [mult_forward ha] at hd
  by_cases haE : e.1=a
  · rw [if_pos haE] at hd
    by_contra hn
    have hdC : dg G C a=3 := by omega
    have hdD : dg G D a=1 := by omega
    exact hel (haE.symm ▸ mem_filter.mpr ⟨ha,hdC,hdD⟩)
  · rw [if_neg haE] at hd
    omega

lemma bad_label_beta (hc : CriticalClass G A B C D) (h44 : ¬HasInternal44 G A C)
    {e : V × V} (he : e∈adjPairs G A D) (hel : e.1∉markedLeaves G A C D)
    (hbad : ¬GoodLabel G A C D e) :
    BetaSignature G A C (mult ((adjPairs G A D).erase e) Prod.fst) := by
  obtain ⟨h,hcov⟩ := selected_six_data hc he hel
  rcases six_classification G A C _ h hcov hbad with ha | hb
  · exact False.elim (h44 ha)
  · exact hb

lemma bad_label_witness (hc : CriticalClass G A B C D) (h44 : ¬HasInternal44 G A C)
    {e : V × V} (he : e∈adjPairs G A D) (hel : e.1∉markedLeaves G A C D)
    (hbad : ¬GoodLabel G A C D e) :
    (6-(dg G (C ∪ D) e.1 : ℤ)=1) ∧ dg G D e.1 ≤ 2 ∧
    (∀ a∈A,6-(dg G (C ∪ D) a : ℤ)=1 → a=e.1) ∧
    #(markedLeaves G A C D) ≤ 1 ∧ ∃ z∈C,dg G B z=2 := by
  let m := mult ((adjPairs G A D).erase e) Prod.fst
  obtain ⟨K,R,J,z,hKR,hKA,hJz,hJC,hR4,hJK,hdz,hJ6,hKz,hRz,hwK,hwR,hmK,_,_⟩ :=
    bad_label_beta hc h44 he hel hbad
  have hKsub : K ⊆ A := by rw [← hKA]; exact subset_union_left
  have hRsub : R ⊆ A := by rw [← hKA]; exact subset_union_right
  have heA : e.1∈A := (mem_product.mp (mem_filter.mp he).1).1
  have heD : e.2∈D := (mem_product.mp (mem_filter.mp he).1).2
  have heAdj := (mem_filter.mp he).2
  have hdK : ∀ k∈K,6-(dg G (C ∪ D) k : ℤ)=0 := by
    intro k hk
    have hs := deleted_row_weight hc he (hKsub hk)
    have hzero := hwK k hk
    have hcap := hc.capP k (mem_union_left B (hKsub hk))
    by_cases hek : e.1=k
    · rw [if_pos hek] at hs
      omega
    · rw [if_neg hek] at hs
      omega
  have heK : e.1∉K := by
    intro hek
    have hs := deleted_row_weight hc he heA
    have hzero := hwK e.1 hek
    have hcap := hc.capP e.1 (mem_union_left B heA)
    rw [if_pos rfl] at hs
    omega
  have heR : e.1∈R := by
    have hmem : e.1∈K ∪ R := hKA ▸ heA
    exact (mem_union.mp hmem).resolve_left heK
  have hdelta : 6-(dg G (C ∪ D) e.1 : ℤ)=1 := by
    have hs := deleted_row_weight hc he heA
    have htwo := hwR e.1 heR
    rw [if_pos rfl] at hs
    omega
  have hfd2 : dg G D e.1 ≤ 2 := by
    have hs := dg_union_of_disjoint (G := G) hc.disjCD e.1
    have hmin := hc.minA e.1 heA
    omega
  have hunique : ∀ a∈A,6-(dg G (C ∪ D) a : ℤ)=1 → a=e.1 := by
    intro a ha hda
    have hs := deleted_row_weight hc he ha
    have hamem : a∈K ∪ R := hKA ▸ ha
    rcases mem_union.mp hamem with haK | haR
    · have hzero := hdK a haK
      omega
    · have htwo := hwR a haR
      by_cases hea : e.1=a
      · exact hea.symm
      · rw [if_neg hea] at hs
        omega
  have hleafsub : markedLeaves G A C D ⊆ R.erase e.1 := by
    intro a ha
    obtain ⟨haA,hadC,hadD⟩ := mem_filter.mp ha
    have hdeltaA : 6-(dg G (C ∪ D) a : ℤ)=2 := by
      have hs := dg_union_of_disjoint (G := G) hc.disjCD a
      omega
    have haR : a∈R := by
      have hm : a∈K ∪ R := hKA ▸ haA
      rcases mem_union.mp hm with haK | haR
      · have hz := hdK a haK
        omega
      · exact haR
    exact mem_erase.mpr ⟨fun heq => by subst a; omega,haR⟩
  have hmcK : msum m K=(ec G K D : ℤ) := by
    have hpt : ∀ k∈K,(m k : ℤ)=(dg G D k : ℤ) := by
      intro k hk
      have hs := mult_erase he Prod.fst k
      have hne : e.1 ≠ k := fun hh => heK (hh ▸ hk)
      rw [mult_forward (hKsub hk),if_neg hne,add_zero] at hs
      exact_mod_cast hs
    unfold msum
    rw [sum_congr rfl hpt,← Nat.cast_sum]
    rfl
  have hK5 : 5 ≤ ec G K D := by
    change msum m K=ec G K D at hmcK
    change msum m K=5 ∨ msum m K=6 at hmK
    rw [hmcK] at hmK
    omega
  have hsplit : ec G K D+ec G R D=7 := by
    have hh : ec G (K ∪ R) D=ec G K D+ec G R D := by unfold ec; rw [sum_union hKR]
    rw [hKA,hc.forward7] at hh
    omega
  have hpos : 1 ≤ dg G D e.1 := by
    exact card_pos.mpr ⟨e.2,mem_filter.mpr ⟨heD,heAdj⟩⟩
  have hRe := sum_erase_add R (dg G D) heR
  have hmono := ec_mono_left (G := G) hleafsub D
  have hleafE : ec G (markedLeaves G A C D) D=#(markedLeaves G A C D) := by
    unfold ec
    rw [sum_congr rfl (fun a ha => (mem_filter.mp ha).2.2),sum_const,nsmul_eq_mul,mul_one]
    norm_num
  have hleaf1 : #(markedLeaves G A C D) ≤ 1 := by
    change ec G (R.erase e.1) D+dg G D e.1=ec G R D at hRe
    omega
  have hzC : z∈C := hJC ▸ mem_union_right J (mem_singleton_self z)
  have hdzB : dg G B z=2 := by
    have hs := dg_union_of_disjoint (G := G) hc.disjAB z
    have hd := hc.saturatedC z hzC
    omega
  exact ⟨hdelta,hfd2,hunique,hleaf1,z,hzC,hdzB⟩

lemma reverse_two_witness_false (he : ec G B C=2) {b c : V}
    (hb : b∈B) (hc : c∈C) (hb2 : dg G C b=2) (hc2 : dg G B c=2) : False := by
  have hsum := sum_erase_add B (dg G C) hb
  change ec G (B.erase b) C+dg G C b=ec G B C at hsum
  have hzero : ec G (B.erase b) C=0 := by omega
  have hsub : B.filter (G.Adj c) ⊆ {b} := by
    intro x hx
    obtain ⟨hxB,hcx⟩ := mem_filter.mp hx
    by_cases hxb : x=b
    · exact mem_singleton.mpr hxb
    · have hxE : x∈B.erase b := mem_erase.mpr ⟨hxb,hxB⟩
      have hd : dg G C x ≤ ec G (B.erase b) C :=
        single_le_sum (fun _ _ => Nat.zero_le _) hxE
      have hp : 1 ≤ dg G C x := card_pos.mpr ⟨c,mem_filter.mpr ⟨hc,hcx.symm⟩⟩
      omega
  have hd := card_le_card hsub
  change dg G B c ≤ #{b} at hd
  rw [card_singleton] at hd
  omega

lemma mult_forward_snd {d : V} (hd : d∈D) : mult (adjPairs G A D) Prod.snd d=dg G A d := by
  have heq : (adjPairs G A D).filter (fun e => e.2=d)=adjPairs G A {d} := by
    ext e
    simp only [adjPairs,mem_filter,mem_product,mem_singleton]
    constructor
    · rintro ⟨⟨⟨heA,_⟩,hadj⟩,he⟩
      exact ⟨⟨heA,he⟩,hadj⟩
    · rintro ⟨⟨heA,he⟩,hadj⟩
      exact ⟨⟨⟨heA,he ▸ hd⟩,hadj⟩,he⟩
  unfold mult
  rw [heq,card_adjPairs,ec_comm]
  simp [ec]

lemma marked_leaves_three (hc : CriticalClass G A B C D) : #(markedLeaves G A C D) ≤ 3 := by
  have hsub : markedLeaves G A C D ⊆ A := filter_subset _ _
  have hpoint : ∀ a∈markedLeaves G A C D,6-(dg G (C ∪ D) a : ℤ)=2 := by
    intro a ha
    obtain ⟨_,hdC,hdD⟩ := mem_filter.mp ha
    have hs := dg_union_of_disjoint (G := G) hc.disjCD a
    omega
  have hs : (∑ a∈markedLeaves G A C D,(6-(dg G (C ∪ D) a : ℤ))) ≤ df G (C ∪ D) A := by
    exact sum_le_sum_of_subset_of_nonneg hsub (fun a ha _ => by
      have hd := hc.capP a (mem_union_left B ha)
      omega)
  rw [hc.deficiencyA,sum_congr rfl hpoint,sum_const,nsmul_eq_mul] at hs
  omega

lemma eligible_card_bound (hc : CriticalClass G A B C D) :
    7 ≤ #(eligibleLabels G A B C D)+#(markedLeaves G A C D)+#(markedLeaves G D B A) := by
  let F := adjPairs G A D
  let X := markedLeaves G A C D
  let Y := markedLeaves G D B A
  have hXF : #{e∈F | e.1∈X}=#X := by
    have hs := sum_mult_eq F Prod.fst X
    have hp : ∀ x∈X,mult F Prod.fst x=1 := by
      intro x hx
      have hd := (mem_filter.mp hx).2.2
      rw [mult_forward (mem_filter.mp hx).1,hd]
    rw [sum_congr rfl hp,sum_const,nsmul_eq_mul,mul_one] at hs
    exact hs.symm
  have hYF : #{e∈F | e.2∈Y}=#Y := by
    have hs := sum_mult_eq F Prod.snd Y
    have hp : ∀ y∈Y,mult F Prod.snd y=1 := by
      intro y hy
      have hd := (mem_filter.mp hy).2.2
      rw [mult_forward_snd (mem_filter.mp hy).1,hd]
    rw [sum_congr rfl hp,sum_const,nsmul_eq_mul,mul_one] at hs
    exact hs.symm
  have heq : F \ eligibleLabels G A B C D={e∈F | e.1∈X} ∪ {e∈F | e.2∈Y} := by
    ext e
    simp only [eligibleLabels,mem_sdiff,mem_filter,mem_union,F,X,Y]
    tauto
  have hbad : #(F \ eligibleLabels G A B C D) ≤ #X+#Y := by
    rw [heq]
    have hh := card_union_le {e∈F | e.1∈X} {e∈F | e.2∈Y}
    rwa [hXF,hYF] at hh
  dsimp only [X,Y] at hbad
  have hEsub : eligibleLabels G A B C D ⊆ F := filter_subset _ _
  have hcard := card_sdiff_add_card_eq_card hEsub
  have hF : #F=7 := by rw [card_adjPairs,hc.forward7]
  omega

lemma eligible_nonempty (hc : CriticalClass G A B C D) : (eligibleLabels G A B C D).Nonempty := by
  have hcL := marked_leaves_three hc
  have hcR := marked_leaves_three hc.swap
  have hb := eligible_card_bound hc
  exact card_pos.mp (by omega)

omit [DecidableEq V] in
lemma pair_swap_mem {e : V × V} : e.swap∈adjPairs G D A ↔ e∈adjPairs G A D := by
  simp only [adjPairs,mem_filter,mem_product,Prod.fst_swap,Prod.snd_swap,G.adj_comm]
  tauto

lemma eligible_swap {e : V × V} :
    e.swap∈eligibleLabels G D C B A ↔ e∈eligibleLabels G A B C D := by
  simp only [eligibleLabels,mem_filter,pair_swap_mem,Prod.fst_swap,Prod.snd_swap]
  tauto

lemma simultaneous_bad_false (hc : CriticalClass G A B C D)
    (h44A : ¬HasInternal44 G A C) (h44D : ¬HasInternal44 G D B)
    {e f : V × V} (he : e∈eligibleLabels G A B C D)
    (hf : f∈eligibleLabels G A B C D) (hbadA : ¬GoodLabel G A C D e)
    (hbadD : ¬GoodLabel G D B A f.swap) : False := by
  obtain ⟨_,_,_,_,z,hz,hz2⟩ := bad_label_witness hc h44A (mem_filter.mp he).1 (mem_filter.mp he).2.1 hbadA
  have hfs := eligible_swap.mpr hf
  obtain ⟨_,_,_,_,b,hb,hb2⟩ := bad_label_witness hc.swap h44D (mem_filter.mp hfs).1 (mem_filter.mp hfs).2.1 hbadD
  exact reverse_two_witness_false hc.reverse2 hb hz hb2 hz2

lemma common_label_of_left_bad (hc : CriticalClass G A B C D)
    (h44A : ¬HasInternal44 G A C) (h44D : ¬HasInternal44 G D B)
    {e : V × V} (he : e∈eligibleLabels G A B C D) (hbad : ¬GoodLabel G A C D e) :
    ∃ f∈eligibleLabels G A B C D,GoodLabel G A C D f ∧ GoodLabel G D B A f.swap := by
  obtain ⟨hde,hf2,huniq,hleaf1,_⟩ := bad_label_witness hc h44A (mem_filter.mp he).1 (mem_filter.mp he).2.1 hbad
  have hleaf3 := marked_leaves_three hc.swap
  have hcard := eligible_card_bound hc
  have hE3 : 3 ≤ #(eligibleLabels G A B C D) := by omega
  have hmult : #{f∈eligibleLabels G A B C D | f.1=e.1} ≤ 2 := by
    have hm := mult_fst_le_degree (G := G) (A := A) (D := D)
      (M := eligibleLabels G A B C D) (filter_subset _ _) e.1
    exact hm.trans hf2
  have hne : ∃ f∈eligibleLabels G A B C D,f.1≠e.1 := by
    by_contra! hn
    have heq : (eligibleLabels G A B C D).filter (fun f => f.1=e.1)=eligibleLabels G A B C D := filter_eq_self.mpr hn
    rw [heq] at hmult
    omega
  obtain ⟨f,hf,hef⟩ := hne
  refine ⟨f,hf,?_,?_⟩
  · by_contra hb
    have hdf := (bad_label_witness hc h44A (mem_filter.mp hf).1 (mem_filter.mp hf).2.1 hb).1
    have hfA := (mem_product.mp (mem_filter.mp (mem_filter.mp hf).1).1).1
    exact hef (huniq f.1 hfA hdf)
  · by_contra hb
    exact simultaneous_bad_false hc h44A h44D he hf hbad hb

lemma common_good_label (hc : CriticalClass G A B C D)
    (h44A : ¬HasInternal44 G A C) (h44D : ¬HasInternal44 G D B) :
    ∃ e∈eligibleLabels G A B C D,GoodLabel G A C D e ∧ GoodLabel G D B A e.swap := by
  by_cases hbadA : ∃ e∈eligibleLabels G A B C D,¬GoodLabel G A C D e
  · obtain ⟨e,he,hbad⟩ := hbadA
    exact common_label_of_left_bad hc h44A h44D he hbad
  · by_cases hbadD : ∃ e∈eligibleLabels G A B C D,¬GoodLabel G D B A e.swap
    · obtain ⟨e,he,hbad⟩ := hbadD
      obtain ⟨f,hf,hfD,hfA⟩ := common_label_of_left_bad hc.swap h44D h44A (eligible_swap.mpr he) hbad
      refine ⟨f.swap,eligible_swap.mp hf,hfA,?_⟩
      simpa only [Prod.swap_swap] using hfD
    · obtain ⟨e,he⟩ := eligible_nonempty hc
      exact ⟨e,he,by by_contra hb; exact hbadA ⟨e,he,hb⟩,
        by by_contra hb; exact hbadD ⟨e,he,hb⟩⟩

omit [DecidableEq V] in
lemma adjPairs_swap_map (A D : Finset V) :
    (adjPairs G A D).map ⟨Prod.swap,Prod.swap_injective⟩=adjPairs G D A := by
  ext e
  constructor
  · intro he
    obtain ⟨f,hf,rfl⟩ := mem_map.mp he
    exact pair_swap_mem.mpr hf
  · intro he
    exact mem_map.mpr ⟨e.swap,pair_swap_mem.mp (by simpa only [Prod.swap_swap] using he),by simp⟩

lemma selected_transpose (e : V × V) :
    mult ((adjPairs G D A).erase e.swap) Prod.fst =
      mult ((adjPairs G A D).erase e) Prod.snd := by
  have hs : ((adjPairs G A D).erase e).map ⟨Prod.swap,Prod.swap_injective⟩=
      (adjPairs G D A).erase e.swap := by
    rw [map_erase,adjPairs_swap_map]
    rfl
  funext d
  rw [← hs]
  unfold mult
  rw [filter_map,card_map]
  rfl

lemma actual_common_support (hc : CriticalClass G A B C D)
    (h44A : ¬HasInternal44 G A C) (h44D : ¬HasInternal44 G D B) :
    ∃ M ⊆ adjPairs G A D,#M=6 ∧
      (∃ p,GoodOmission G A C (mult M Prod.fst) p) ∧
      (∃ q,GoodOmission G D B (mult M Prod.snd) q) := by
  obtain ⟨e,he,hgoodA,hgoodD⟩ := common_good_label hc h44A h44D
  have heF := (mem_filter.mp he).1
  have h6 : #((adjPairs G A D).erase e)=6 := by rw [card_erase_of_mem heF,card_adjPairs,hc.forward7]
  refine ⟨(adjPairs G A D).erase e,erase_subset e _,h6,hgoodA,?_⟩
  change ∃ q,GoodOmission G D B (mult ((adjPairs G D A).erase e.swap) Prod.fst) q at hgoodD
  rw [selected_transpose] at hgoodD
  exact hgoodD

lemma physical_quartic_of_six (hc : CriticalClass G A B C D)
    (M : Finset (V × V)) (hM : M ⊆ adjPairs G A D) (hM6 : #M=6)
    {p q : V} (hgoodA : GoodOmission G A C (mult M Prod.fst) p)
    (hgoodD : GoodOmission G D B (mult M Prod.snd) q) :
    Quartic G (A ∪ B) (C ∪ D) := by
  have hPA : (A ∪ B) \ A=B := by
    ext x
    simp only [mem_sdiff,mem_union]
    constructor
    · rintro ⟨hx,hxn⟩
      exact hx.resolve_left hxn
    · intro hx
      exact ⟨Or.inr hx,fun ha => disjoint_left.mp hc.disjAB ha hx⟩
  have hQC : (C ∪ D) \ C=D := by
    ext x
    simp only [mem_sdiff,mem_union]
    constructor
    · rintro ⟨hx,hxn⟩
      exact hx.resolve_left hxn
    · intro hx
      exact ⟨Or.inr hx,fun hc' => disjoint_left.mp hc.disjCD hc' hx⟩
  have hMadj : ∀ e∈M,G.Adj e.1 e.2 := fun e he => (mem_filter.mp (hM he)).2
  have hX : ∀ T ⊆ A.erase p,demand G A C T ≤ (#{e∈M | e.1∈T} : ℤ) := by
    intro T hT
    have hh := hgoodA.2.2 T hT
    rwa [msum_mult_eq] at hh
  have hY : ∀ S ⊆ ((C ∪ D) \ C).erase q,
      demand G ((C ∪ D) \ C) ((A ∪ B) \ A) S ≤ (#{e∈M | e.2∈S} : ℤ) := by
    rw [hPA,hQC]
    intro S hS
    have hh := hgoodD.2.2 S hS
    rwa [msum_mult_eq] at hh
  have hcut := cut_condition_of_six_pair (G := G)
    (P := A ∪ B) (Q := C ∪ D) (A := A) (C := C) subset_union_left subset_union_left
    (by rw [hQC,hPA]; exact hc.imbalanceDB) hc.saturatedC
    (by rw [hPA]; exact hc.saturatedB) (by rw [hPA]; exact hc.reverse2)
    M hMadj (by omega) (by rw [hQC]; exact hgoodD.1) hX hY
  have hpP : p∈A ∪ B := mem_union_left B hgoodA.1
  have hqQ : q∈C ∪ D := mem_union_right C hgoodD.1
  have hcard : #((A ∪ B).erase p)=#((C ∪ D).erase q) := by
    have hp := card_erase_add_one hpP
    have hq := card_erase_add_one hqQ
    have hb := hc.balanced
    omega
  obtain ⟨F,hF,hadj,hFP,hFQ⟩ := exists_four_factor _ _ hcard hcut
  have hPne : ((A ∪ B).erase p).Nonempty := by
    have hA6 := hc.blockAC.six_le
    have ha := card_le_card (subset_union_left : A ⊆ A ∪ B)
    have hp := card_erase_add_one hpP
    exact card_pos.mp (by omega)
  have hQne : ((C ∪ D).erase q).Nonempty := card_pos.mp (by rw [← hcard]; exact card_pos.mpr hPne)
  have hquartic := (quartic_of_four_factor (G := G) Subset.rfl hQne hF hadj hFP hFQ).swap
  exact quartic_mono hquartic (erase_subset _ _) (erase_subset _ _)

/-- Actual original-edge class repair, with every supply/omission/Hall premise produced. -/
theorem physical_repair : PhysicalRepair.{u} := by
  intro V _ G _ A B C D hc
  by_cases h44A : HasInternal44 G A C
  · exact hc.direct_internal44 (Or.inl h44A)
  by_cases h44D : HasInternal44 G D B
  · exact hc.direct_internal44 (Or.inr h44D)
  obtain ⟨M,hM,h6,⟨p,hp⟩,⟨q,hq⟩⟩ := actual_common_support hc h44A h44D
  exact physical_quartic_of_six hc M hM h6 hp hq

end Erdos585.QB7TwoReverse

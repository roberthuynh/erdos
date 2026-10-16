import Openmath.Proofs.PaperSupport.QB6C02NonlinearCore
import Openmath.Proofs.PaperSupport.QB6C02LinearCover
import Openmath.Proofs.PaperSupport.QB6C02SixNeighbor

/- 


-/
open Finset
open Erdos585.QB4 Erdos585.QB5 Erdos585.QB6Assembly
open Erdos585.QB6C02PartialFactor Erdos585.QB6C02NonlinearCore
namespace Erdos585.QB6C02NoTheta3
universe u
variable {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
set_option maxHeartbeats 2200000

/-- Actual theta bound on every physical A subset of order at least three. -/
def NoTheta3 (A C : Finset V) : Prop :=
  ∀ Z ⊆ A, 3 ≤ #Z → thetaC02 G C Z ≤ 2

/-- A literal original-edge spanning four-factor after exactly two A omissions. -/
def GoodPair (A C D : Finset V) : Prop :=
  D ⊆ A ∧ #D = 2 ∧ ∃ F : Finset (V × V), F.Nonempty ∧
    F ⊆ adjPairs G (A \ D) C ∧
    (∀ a ∈ A \ D, edgeDegree F Prod.fst a = 4) ∧
    (∀ c ∈ C, edgeDegree F Prod.snd c = 4)

/-- Physical pair coverage by the actual maximal-positive powerset family. -/
def APF (A C : Finset V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
    ∃ T ∈ maxPositiveFamily G A C, a ∈ T ∧ b ∈ T

/-- The actual eligible high sets; singleton theta values are excluded. -/
def highSets (A C : Finset V) : Finset (Finset V) := by
  classical
  exact A.powerset.filter fun K => 3 ≤ #K ∧ 2 ≤ thetaC02 G C K

def maxHighFamily (A C : Finset V) : Finset (Finset V) :=
  maximalMembers (highSets G A C)

/-- Count-two columns are included physically, without a supplied shore. -/
def corePlus (C K : Finset V) : Finset V :=
  C.filter fun c => 2 ≤ dg G K c

def highLoss (C K : Finset V) : ℤ :=
  6 * (#K : ℤ) - ec G K (corePlus G C K)

def NoTheta3GoodPair : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V), C02Input G A C → NoTheta3 G A C →
      ∃ D, GoodPair G A C D

def NoTheta3Repair : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V), C02Input G A C → NoTheta3 G A C → Quartic G A C

variable {G}

/-- Every actual opposite-shore Hall cut is paid, including empty/full cuts. -/
theorem pair_cut_of_theta {A C D : Finset V} (h : C02Input G A C)
    (hD : D ⊆ A)
    (htheta : ∀ Z ⊆ A, D ⊆ Z → thetaC02 G C Z ≤ 0) :
    ∀ S ⊆ A \ D, ∀ T ⊆ C,
      4 * #S ≤ ec G S (C \ T) + 4 * #T := by
  intro S hS T hT
  have hSA : S ⊆ A := hS.trans sdiff_subset
  have hDZ : D ⊆ A \ S := by
    intro a ha
    refine mem_sdiff.mpr ⟨hD ha, ?_⟩
    intro has
    exact (mem_sdiff.mp (hS has)).2 ha
  have hd : demandC02 G C S ≤ 0 := by
    rw [complement_demand h hSA]
    exact htheta (A \ S) sdiff_subset hDZ
  have hs := sum_sdiff hT (f := fun c => min 4 (dg G S c : ℤ))
  have h1 : (∑ c ∈ C \ T, min 4 (dg G S c : ℤ)) ≤ (ec G S (C \ T) : ℤ) := by
    rw [ec_comm]
    change (∑ c ∈ C \ T, min 4 (dg G S c : ℤ)) ≤
      ((∑ c ∈ C \ T, dg G S c : ℕ) : ℤ)
    rw [Nat.cast_sum]
    exact sum_le_sum fun c _ => min_le_right _ _
  have h2 : (∑ c ∈ T, min 4 (dg G S c : ℤ)) ≤ 4 * (#T : ℤ) := by
    calc
      _ ≤ ∑ _c ∈ T, (4 : ℤ) := sum_le_sum fun c _ => min_le_left _ _
      _ = _ := by rw [sum_const, nsmul_eq_mul]; ring
  have hcut : 4 * (#S : ℤ) ≤ (ec G S (C \ T) : ℤ) + 4 * #T := by
    unfold demandC02 at hd
    linarith
  exact_mod_cast hcut

/-- Integral QB4 Hall produces the nonempty original-edge factor. -/
theorem goodPair_of_theta {A C D : Finset V} (h : C02Input G A C)
    (hD : D ⊆ A) (hD2 : #D = 2)
    (htheta : ∀ Z ⊆ A, D ⊆ Z → thetaC02 G C Z ≤ 0) :
    GoodPair G A C D := by
  have hc : #(A \ D) = #C := by
    have hd := card_sdiff_add_card_eq_card hD
    have ha := h.card
    omega
  obtain ⟨F, hF, hadj, hFA, hFC⟩ :=
    exists_four_factor (G := G) (A \ D) C hc (pair_cut_of_theta h hD htheta)
  have hFadj : F ⊆ adjPairs G (A \ D) C := by
    intro e he
    exact mem_filter.mpr ⟨hF he, hadj e he⟩
  have hne : F.Nonempty := by
    have hC : C.Nonempty := card_pos.mp (by have hh := c02_cardC h; omega)
    obtain ⟨c, hc⟩ := hC
    obtain ⟨e, he⟩ := card_pos.mp (show 0 < #{e ∈ F | e.2 = c} from by
      rw [hFC c hc]; norm_num)
    exact ⟨e, (mem_filter.mp he).1⟩
  exact ⟨hD, hD2, F, hne, hFadj, hFA, hFC⟩

theorem goodPair_quartic {A C D : Finset V} (h : C02Input G A C)
    (hgood : GoodPair G A C D) : Quartic G A C := by
  obtain ⟨_, _, F, _, hF, hFA, hFC⟩ := hgood
  have hC : C.Nonempty := card_pos.mp (by have hh := c02_cardC h; omega)
  have hprod : F ⊆ (A \ D) ×ˢ C := hF.trans (filter_subset _ _)
  have hadj : ∀ e ∈ F, G.Adj e.1 e.2 := fun e he => (mem_filter.mp (hF he)).2
  exact (quartic_of_four_factor (G := G) sdiff_subset hC hprod hadj hFA hFC).swap

/-- Failed physical good pairs produce the cover, not a supplied APF assumption. -/
theorem apf_of_no_good_pair {A C : Finset V} (h : C02Input G A C)
    (hn : ∀ D ⊆ A, #D = 2 → ¬ GoodPair G A C D) : APF G A C := by
  classical
  intro a ha b hb hab
  by_contra hcover
  let D : Finset V := {a, b}
  have hD : D ⊆ A := by
    intro x hx
    simp only [D, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have hD2 : #D = 2 := by simp [D, hab]
  have htheta : ∀ Z ⊆ A, D ⊆ Z → thetaC02 G C Z ≤ 0 := by
    intro Z hZ hDZ
    by_contra hpositive
    have h2 : 2 ≤ #Z := by have hc := card_le_card hDZ; omega
    obtain ⟨T, hT, hZT⟩ := positive_extension (G := G) (C := C) hZ h2 (by omega)
    apply hcover
    refine ⟨T, hT, hZT (hDZ ?_), hZT (hDZ ?_)⟩ <;> simp [D]
  exact hn D hD hD2 (goodPair_of_theta h hD hD2 htheta)

theorem apf_of_no_quartic {A C : Finset V} (h : C02Input G A C)
    (hn : ¬ Quartic G A C) : APF G A C :=
  apf_of_no_good_pair h fun _ _ _ hgood => hn (goodPair_quartic h hgood)

omit [DecidableEq V] in
lemma mem_highSets {A C K : Finset V} :
    K ∈ highSets G A C ↔ K ⊆ A ∧ 3 ≤ #K ∧ 2 ≤ thetaC02 G C K := by
  classical
  simp [highSets]

omit [DecidableEq V] in
theorem theta_nontrivial {A C Z : Finset V} (hn : NoTheta3 G A C)
    (hZ : Z ⊆ A) (h2 : 2 ≤ #Z) : thetaC02 G C Z ≤ 2 := by
  by_cases h3 : 3 ≤ #Z
  · exact hn Z hZ h3
  · have hs := theta_small (G := G) C (Z := Z) (by omega)
    omega

theorem maxHigh_data {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hK : K ∈ maxHighFamily G A C) :
    K ⊆ A ∧ 3 ≤ #K ∧ thetaC02 G C K = 2 ∧ K ≠ A ∧
      ∀ U, U ⊆ A → K ⊆ U → U ≠ K → thetaC02 G C U ≤ 1 := by
  obtain ⟨hp, hm⟩ := mem_maximalMembers.mp hK
  obtain ⟨hKA, h3, ht⟩ := mem_highSets.mp hp
  have heq : thetaC02 G C K = 2 := by have hh := hn K hKA h3; omega
  have hne : K ≠ A := by
    intro he
    have hw := theta_whole h
    rw [he] at heq
    omega
  refine ⟨hKA, h3, heq, hne, ?_⟩
  intro U hU hKU hneq
  by_contra hu
  have h3U : 3 ≤ #U := h3.trans (card_le_card hKU)
  exact hneq (hm U (mem_highSets.mpr ⟨hU, h3U, by omega⟩) hKU)

theorem high_extension {A C Z : Finset V} (hZ : Z ⊆ A)
    (h3 : 3 ≤ #Z) (ht : 2 ≤ thetaC02 G C Z) :
    ∃ K ∈ maxHighFamily G A C, Z ⊆ K :=
  exists_maximal_extension (mem_highSets.mpr ⟨hZ, h3, ht⟩)

/-- No-theta-three containment uses actual finite intersection theta. -/
theorem high_F_containment {A C K T : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hK : K ∈ maxHighFamily G A C)
    (hT : T ∈ maxPositiveFamily G A C) (hI : 2 ≤ #(K ∩ T)) : K ⊆ T := by
  obtain ⟨hKA, _, htK, _, _⟩ := maxHigh_data h hn hK
  obtain ⟨hTA, _, htT, hmT⟩ := maxPositive_data h hT
  by_contra hnot
  have hUne : K ∪ T ≠ T := by
    intro he
    exact hnot (he ▸ subset_union_left)
  have hU := hmT (K ∪ T) (union_subset hKA hTA) subset_union_right hUne
  have hIt := theta_nontrivial hn (inter_subset_left.trans hKA) hI
  have hs := theta_supermodular (G := G) C K T
  linarith

/-- Distinct actual high maxima meet in at most one original point. -/
theorem high_inter_card_le_one {A C K L : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hK : K ∈ maxHighFamily G A C)
    (hL : L ∈ maxHighFamily G A C) (hne : K ≠ L) : #(K ∩ L) ≤ 1 := by
  obtain ⟨hKA, _, htK, _, hmK⟩ := maxHigh_data h hn hK
  obtain ⟨hLA, _, htL, _, hmL⟩ := maxHigh_data h hn hL
  have hUne : K ∪ L ≠ K := by
    intro he
    have hLK : L ⊆ K := he ▸ subset_union_right
    have hx := hmL K hKA hLK hne
    omega
  have hU := hmK (K ∪ L) (union_subset hKA hLA) subset_union_left hUne
  by_contra hi
  have hIt := theta_nontrivial (Z := K ∩ L) hn (inter_subset_left.trans hKA) (by omega)
  have hs := theta_supermodular (G := G) C K L
  linarith

/-- Every nonlinear F intersection is exactly one actual high maximum. -/
theorem nonlinear_F_intersection {A C T T' : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hT : T ∈ maxPositiveFamily G A C)
    (hT' : T' ∈ maxPositiveFamily G A C) (hne : T ≠ T')
    (hI : 2 ≤ #(T ∩ T')) :
    thetaC02 G C T = 1 ∧ thetaC02 G C T' = 1 ∧
    thetaC02 G C (T ∪ T') = 0 ∧ thetaC02 G C (T ∩ T') = 2 ∧
    T ∩ T' ∈ maxHighFamily G A C := by
  obtain ⟨hTA, h3T, htT, hmT⟩ := maxPositive_data h hT
  obtain ⟨hT'A, _, htT', _⟩ := maxPositive_data h hT'
  have hUne : T ∪ T' ≠ T := by
    intro he
    obtain ⟨hpT, _⟩ := mem_maximalMembers.mp hT
    obtain ⟨_, hmT'⟩ := mem_maximalMembers.mp hT'
    exact hne (hmT' T hpT (he ▸ subset_union_right))
  have hU := hmT (T ∪ T') (union_subset hTA hT'A) subset_union_left hUne
  have hIA : T ∩ T' ⊆ A := inter_subset_left.trans hTA
  have hIt := theta_nontrivial hn hIA hI
  have hs := theta_supermodular (G := G) C T T'
  have heqs : thetaC02 G C T = 1 ∧ thetaC02 G C T' = 1 ∧
      thetaC02 G C (T ∪ T') = 0 ∧ thetaC02 G C (T ∩ T') = 2 := by omega
  have h3I : 3 ≤ #(T ∩ T') := by
    by_contra hh
    have hx := theta_small (G := G) C (Z := T ∩ T') (by omega)
    omega
  obtain ⟨K, hK, hIK⟩ := high_extension (G := G) (C := C) hIA h3I (by omega)
  have hIKT : T ∩ T' ⊆ K ∩ T := subset_inter hIK inter_subset_left
  have hIKT' : T ∩ T' ⊆ K ∩ T' := subset_inter hIK inter_subset_right
  have hKT := high_F_containment h hn hK hT (hI.trans (card_le_card hIKT))
  have hKT' := high_F_containment h hn hK hT' (hI.trans (card_le_card hIKT'))
  have heq : T ∩ T' = K := subset_antisymm hIK (subset_inter hKT hKT')
  exact ⟨heqs.1, heqs.2.1, heqs.2.2.1, heqs.2.2.2, heq.symm ▸ hK⟩

omit [DecidableEq V] in
lemma corePlus_subset (C K : Finset V) : corePlus G C K ⊆ C := filter_subset _ _

omit [DecidableEq V] in
/-- The exact theta identity includes actual count-two columns. -/
theorem theta_corePlus (C K : Finset V) :
    thetaC02 G C K = 8 - 4 * #K - 2 * #(corePlus G C K) +
      ec G K (corePlus G C K) := by
  have hs : (∑ c ∈ C, max 0 ((dg G K c : ℤ) - 2)) =
      ∑ c ∈ corePlus G C K, ((dg G K c : ℤ) - 2) := by
    rw [corePlus, sum_filter]
    apply sum_congr rfl
    intro c _
    by_cases hh : 2 ≤ dg G K c <;> simp only [hh, if_true, if_false] <;> omega
  have he : (ec G K (corePlus G C K) : ℤ) =
      ∑ c ∈ corePlus G C K, (dg G K c : ℤ) := by
    rw [ec_comm]
    unfold ec
    rw [Nat.cast_sum]
  rw [sum_sub_distrib, ← he, sum_const, nsmul_eq_mul] at hs
  unfold thetaC02
  rw [hs]
  ring

/-- All three absorbed loss signatures and the actual proper g domain. -/
theorem highPlus_geometry {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hK : K ∈ maxHighFamily G A C) :
    (highLoss G C K = 0 ∨ highLoss G C K = 2 ∨ highLoss G C K = 4) ∧
    highLoss G C K = 6 + 2 * ((#K : ℤ) - #(corePlus G C K)) ∧
    14 ≤ gv G K (corePlus G C K) := by
  obtain ⟨hKA, h3K, htK, hneK, _⟩ := maxHigh_data h hn hK
  have hY := corePlus_subset (G := G) C K
  have hcK : #K < #A := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hKA, hneK⟩)
  have hcY := card_le_card hY
  have hg := h.sparse K hKA (corePlus G C K) hY (by omega) (by omega)
  have hcap : ec G K (corePlus G C K) ≤ 6 * #K :=
    ec_le_six_mul fun a ha => (dg_mono hY a).trans (h.capA a (hKA ha))
  have hcapz : (ec G K (corePlus G C K) : ℤ) ≤ 6 * (#K : ℤ) := by exact_mod_cast hcap
  have ht := theta_corePlus (G := G) C K
  have hl : highLoss G C K = 6 + 2 * ((#K : ℤ) - #(corePlus G C K)) := by
    unfold highLoss
    linarith
  have hh : 0 ≤ highLoss G C K := by unfold highLoss; omega
  have hk : (#K : ℤ) - #(corePlus G C K) ≤ -1 := by
    unfold gv at hg
    omega
  refine ⟨?_, hl, hg⟩
  omega

/-- Boundary and complementary cardinality are literal original counts. -/
theorem highPlus_boundary {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hK : K ∈ maxHighFamily G A C) :
    (ec G (A \ K) (corePlus G C K) : ℤ) = 18 - 2 * highLoss G C K ∧
    2 * (#(A \ K) : ℤ) = 2 * #(C \ corePlus G C K) + 10 - highLoss G C K := by
  obtain ⟨hKA, _, _, _, _⟩ := maxHigh_data h hn hK
  obtain ⟨_, hl, _⟩ := highPlus_geometry h hn hK
  have hY := corePlus_subset (G := G) C K
  have he : ec G A (corePlus G C K) = 6 * #(corePlus G C K) := by
    rw [ec_comm]
    unfold ec
    rw [sum_congr rfl (fun c hc => h.satC c (hY hc)), sum_const, smul_eq_mul, mul_comm]
  have hs := ec_sdiff_add_left (G := G) hKA (corePlus G C K)
  have hsZ : (ec G (A \ K) (corePlus G C K) : ℤ) + ec G K (corePlus G C K) =
      6 * (#(corePlus G C K) : ℤ) := by exact_mod_cast (he ▸ hs)
  have hcK : (#(A \ K) : ℤ) + #K = #A := by exact_mod_cast card_sdiff_add_card_eq_card hKA
  have hcY : (#(C \ corePlus G C K) : ℤ) + #(corePlus G C K) = #C := by
    exact_mod_cast card_sdiff_add_card_eq_card hY
  have hcA : (#A : ℤ) = #C + 2 := by exact_mod_cast h.card
  have hd : highLoss G C K = 6 * (#K : ℤ) - ec G K (corePlus G C K) := rfl
  constructor <;> linarith

theorem highPlus_individual_loss {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hK : K ∈ maxHighFamily G A C) {a : V} (ha : a ∈ K) :
    0 ≤ 6 - (dg G (corePlus G C K) a : ℤ) ∧
    6 - (dg G (corePlus G C K) a : ℤ) ≤ highLoss G C K := by
  obtain ⟨hKA, _, _, _, _⟩ := maxHigh_data h hn hK
  have hcap : ∀ b ∈ K, dg G (corePlus G C K) b ≤ 6 := fun b hb =>
    (dg_mono (corePlus_subset (G := G) C K) b).trans (h.capA b (hKA hb))
  have hdf : df G (corePlus G C K) K = highLoss G C K := df_eq _ _
  have hsingle : 6 - (dg G (corePlus G C K) a : ℤ) ≤ df G (corePlus G C K) K :=
    single_le_sum (f := fun b => (6 : ℤ) - (dg G (corePlus G C K) b : ℤ))
      (fun b hb => by have hx := hcap b hb; omega) ha
  rw [hdf] at hsingle
  exact ⟨by have hh := hcap a ha; omega, hsingle⟩

/-- Count-two columns already give the unit singleton gap. -/
lemma singleton_gap_one_plus {K T : Finset V} {a c : V}
    (hi : K ∩ T = {a}) (hx : 2 ≤ dg G K c) (hy : 3 ≤ dg G T c)
    (hadj : G.Adj a c) : columnGap (G := G) K T c = 1 := by
  have hd := dg_union_add_dg_inter (G := G) K T c
  have hz : dg G ({a} : Finset V) c = 1 := by
    simp only [dg, filter_singleton, if_pos (G.adj_symm hadj), card_singleton]
  unfold columnGap
  rw [hi, hz] at hd ⊢
  omega

/-- Every partial member pays actual outside incidences and individual loss. -/
theorem partial_absorbed_loss {A C K T : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hK : K ∈ maxHighFamily G A C)
    (hT : T ∈ maxPositiveFamily G A C) (hnot : ¬ K ⊆ T)
    {a : V} (hi : K ∩ T = {a}) :
    2 * thetaC02 G C T ≤ (dg G (C \ corePlus G C K) a : ℤ) ∧
    2 * thetaC02 G C T ≤ 6 - (dg G (corePlus G C K) a : ℤ) := by
  classical
  obtain ⟨hKA, _, htK, _, _⟩ := maxHigh_data h hn hK
  obtain ⟨hTA, h3T, htT, hmT⟩ := maxPositive_data h hT
  have hai : a ∈ K ∩ T := by rw [hi]; simp
  obtain ⟨haK, haT⟩ := mem_inter.mp hai
  have hUne : K ∪ T ≠ T := by intro he; exact hnot (he ▸ subset_union_left)
  have hU := hmT (K ∪ T) (union_subset hKA hTA) subset_union_right hUne
  have hsingle : thetaC02 G C ({a} : Finset V) = 4 := by
    simpa using (theta_small (G := G) C (Z := {a}) (by simp))
  have hg := theta_gap_sum (G := G) C K T
  rw [hi, hsingle, htK] at hg
  have hgap : (∑ c ∈ C, columnGap (G := G) K T c) ≤ 2 - thetaC02 G C T := by
    linarith
  let S := (corePlus G C K ∩ cpr G C T).filter fun c => G.Adj a c
  have hSC : S ⊆ C := by
    intro c hc
    exact (mem_filter.mp (mem_inter.mp (mem_filter.mp hc).1).1).1
  have hunit : ∀ c ∈ S, columnGap (G := G) K T c = 1 := by
    intro c hc
    obtain ⟨hci, hac⟩ := mem_filter.mp hc
    obtain ⟨hcK, hcT⟩ := mem_inter.mp hci
    exact singleton_gap_one_plus hi (mem_filter.mp hcK).2 (mem_cpr.mp hcT).2 hac
  have hsum := sum_le_sum_of_subset_of_nonneg hSC
    (fun c _ _ => columnGap_nonneg (G := G) K T c)
  have hsumeq : (∑ c ∈ S, columnGap (G := G) K T c) = (#S : ℤ) := by
    rw [sum_congr rfl hunit]
    simp
  rw [hsumeq] at hsum
  have hcommon : (dg G (corePlus G C K ∩ cpr G C T) a : ℤ) ≤
      ∑ c ∈ C, columnGap (G := G) K T c := hsum
  have hdu := dg_union_add_dg_inter (G := G) (corePlus G C K) (cpr G C T) a
  have hduc : dg G (corePlus G C K ∪ cpr G C T) a ≤ dg G C a :=
    dg_mono (union_subset (corePlus_subset (G := G) C K) (cpr_subset (G := G) C T)) a
  have hds := dg_sdiff_add (G := G) (corePlus_subset (G := G) C K) a
  have h3erase : 2 ≤ #(T.erase a) := by
    have hc := card_erase_add_one haT
    omega
  have htErase := theta_nontrivial (Z := T.erase a) hn ((erase_subset _ _).trans hTA) h3erase
  have hErase := theta_erase (G := G) (C := C) haT
  have hcap := h.capA a (hKA haK)
  constructor <;> omega

/-- An actual high maximum has a row of absorbed degree at least five. -/
theorem high_clean_vertex {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hK : K ∈ maxHighFamily G A C) :
    ∃ a ∈ K, 5 ≤ dg G (corePlus G C K) a := by
  obtain ⟨_, h3K, _, _, _⟩ := maxHigh_data h hn hK
  obtain ⟨hsig, _, _⟩ := highPlus_geometry h hn hK
  by_contra hnone
  push Not at hnone
  have hsum : 2 * (#K : ℤ) ≤ highLoss G C K := by
    calc
      _ = ∑ _a ∈ K, (2 : ℤ) := by simp only [sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ a ∈ K, (6 - (dg G (corePlus G C K) a : ℤ)) :=
        sum_le_sum fun a ha => by have hh := hnone a ha; omega
      _ = _ := df_eq _ _
  omega

/-- APF pays every actual K-containing cover member from a clean row. -/
theorem high_cover {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C)
    {r : V} (hr : r ∈ A \ K) :
    ∃ T ∈ maxPositiveFamily G A C, K ⊆ T ∧ r ∈ T := by
  obtain ⟨hKA, _, _, _, _⟩ := maxHigh_data h hn hK
  obtain ⟨a, haK, ha5⟩ := high_clean_vertex h hn hK
  obtain ⟨hrA, hrK⟩ := mem_sdiff.mp hr
  have har : a ≠ r := by intro he; exact hrK (he ▸ haK)
  obtain ⟨T, hT, haT, hrT⟩ := hp a (hKA haK) r hrA har
  refine ⟨T, hT, ?_, hrT⟩
  by_contra hnot
  have hI : #(K ∩ T) ≤ 1 := by
    by_contra hi
    exact hnot (high_F_containment h hn hK hT (by omega))
  have hai : a ∈ K ∩ T := mem_inter.mpr ⟨haK, haT⟩
  have hsub : {a} ⊆ K ∩ T := singleton_subset_iff.mpr hai
  have heq : K ∩ T = {a} := (eq_of_subset_of_card_le hsub (by simpa using hI)).symm
  obtain ⟨hout, _⟩ := partial_absorbed_loss h hn hK hT hnot heq
  have hd := dg_sdiff_add (G := G) (corePlus_subset (G := G) C K) a
  have hcap := h.capA a (hKA haK)
  have hpositive := (maxPositive_data h hT).2.2.1
  omega

theorem high_not_F {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C) :
    K ∉ maxPositiveFamily G A C := by
  obtain ⟨hKA, _, _, hneK, _⟩ := maxHigh_data h hn hK
  have hR : (A \ K).Nonempty := by
    by_contra hh
    have he := not_nonempty_iff_eq_empty.mp hh
    exact hneK (subset_antisymm hKA (sdiff_eq_empty_iff_subset.mp he))
  obtain ⟨r, hr⟩ := hR
  obtain ⟨T, hT, hKT, hrT⟩ := high_cover h hn hp hK hr
  intro hKF
  have hTK : T ≠ K := by intro he; exact (mem_sdiff.mp hr).2 (he ▸ hrT)
  have ht := (maxPositive_data h hKF).2.2.2 T (maxPositive_data h hT).1 hKT hTK
  have hpositive := (maxPositive_data h hT).2.2.1
  omega

variable (G) in
def containingFamily (A C K : Finset V) : Finset (Finset V) :=
  (maxPositiveFamily G A C).filter fun T => K ⊆ T

lemma mem_containingFamily {A C K T : Finset V} :
    T ∈ containingFamily G A C K ↔ T ∈ maxPositiveFamily G A C ∧ K ⊆ T := by
  simp [containingFamily]

theorem containing_theta_one {A C K T : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C)
    (hT : T ∈ containingFamily G A C K) : thetaC02 G C T = 1 ∧ T ≠ K := by
  obtain ⟨hTF, hKT⟩ := mem_containingFamily.mp hT
  have hTK : T ≠ K := by intro he; exact high_not_F h hn hp hK (he ▸ hTF)
  have ht := (maxHigh_data h hn hK).2.2.2.2 T (maxPositive_data h hTF).1 hKT hTK
  have hpositive := (maxPositive_data h hTF).2.2.1
  exact ⟨by omega, hTK⟩

theorem containing_intersection {A C K T T' : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C)
    (hT : T ∈ containingFamily G A C K) (hT' : T' ∈ containingFamily G A C K)
    (hne : T ≠ T') : T ∩ T' = K ∧ thetaC02 G C (T ∪ T') = 0 ∧
      ∀ c ∈ C, columnGap (G := G) T T' c = 0 := by
  obtain ⟨hTF, hKT⟩ := mem_containingFamily.mp hT
  obtain ⟨hT'F, hKT'⟩ := mem_containingFamily.mp hT'
  have h3K := (maxHigh_data h hn hK).2.1
  have hKI : K ⊆ T ∩ T' := subset_inter hKT hKT'
  have h2I : 2 ≤ #(T ∩ T') := by have hc := card_le_card hKI; omega
  obtain ⟨_, _, htU, htI, hIH⟩ := nonlinear_F_intersection h hn hTF hT'F hne h2I
  obtain ⟨_, hmK⟩ := mem_maximalMembers.mp hK
  obtain ⟨hIh, _⟩ := mem_maximalMembers.mp hIH
  have hIK : T ∩ T' = K := hmK (T ∩ T') hIh hKI
  have hg := theta_gap_sum (G := G) C T T'
  have htT := (containing_theta_one h hn hp hK hT).1
  have htT' := (containing_theta_one h hn hp hK hT').1
  have hs : (∑ c ∈ C, columnGap (G := G) T T' c) = 0 := by omega
  refine ⟨hIK, htU, ?_⟩
  intro c hc
  have hle : columnGap (G := G) T T' c ≤ ∑ c ∈ C, columnGap (G := G) T T' c :=
    single_le_sum (fun c _ => columnGap_nonneg (G := G) T T' c) hc
  have hnon := columnGap_nonneg (G := G) T T' c
  omega

theorem containing_cover {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C) :
    (containingFamily G A C K).biUnion (fun T => T \ K) = A \ K := by
  ext r
  constructor
  · intro hr
    obtain ⟨T, hT, hrT⟩ := mem_biUnion.mp hr
    obtain ⟨hrT, hrK⟩ := mem_sdiff.mp hrT
    have hTA := (maxPositive_data h (mem_containingFamily.mp hT).1).1
    exact mem_sdiff.mpr ⟨hTA hrT, hrK⟩
  · intro hr
    obtain ⟨T, hT, hKT, hrT⟩ := high_cover h hn hp hK hr
    exact mem_biUnion.mpr ⟨T, mem_containingFamily.mpr ⟨hT, hKT⟩,
      mem_sdiff.mpr ⟨hrT, (mem_sdiff.mp hr).2⟩⟩

theorem containing_petals_disjoint {A C K T T' : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C)
    (hT : T ∈ containingFamily G A C K) (hT' : T' ∈ containingFamily G A C K)
    (hne : T ≠ T') : Disjoint (T \ K) (T' \ K) := by
  have heq := (containing_intersection h hn hp hK hT hT' hne).1
  apply disjoint_left.mpr
  intro r hr hr'
  have hi : r ∈ T ∩ T' := mem_inter.mpr ⟨(mem_sdiff.mp hr).1, (mem_sdiff.mp hr').1⟩
  rw [heq] at hi
  exact (mem_sdiff.mp hr).2 hi

/-- Exact theta on an actual threshold-valid selected column shore. -/
theorem theta_selected {C Z Y : Finset V} (hY : Y ⊆ C)
    (hin : ∀ c ∈ Y, 2 ≤ dg G Z c) (hout : ∀ c ∈ C \ Y, dg G Z c ≤ 2) :
    thetaC02 G C Z = 8 - 4 * #Z - 2 * #Y + ec G Z Y := by
  have hs : (∑ c ∈ Y, max 0 ((dg G Z c : ℤ) - 2)) =
      ∑ c ∈ C, max 0 ((dg G Z c : ℤ) - 2) :=
    sum_subset hY fun c hc hn => by
      have hh := hout c (mem_sdiff.mpr ⟨hc, hn⟩)
      omega
  have hf : (∑ c ∈ C, max 0 ((dg G Z c : ℤ) - 2)) =
      ∑ c ∈ Y, ((dg G Z c : ℤ) - 2) := by
    rw [← hs]
    exact sum_congr rfl fun c hc => by have hh := hin c hc; omega
  have he : (ec G Z Y : ℤ) = ∑ c ∈ Y, (dg G Z c : ℤ) := by
    rw [ec_comm]; unfold ec; rw [Nat.cast_sum]
  rw [sum_sub_distrib, ← he, sum_const, nsmul_eq_mul] at hf
  unfold thetaC02
  rw [hf]
  ring

lemma column_gap_zero_low {T T' : Finset V} {c : V}
    (hx : 3 ≤ dg G T c) (hz : dg G (T ∩ T') c ≤ 1)
    (hg : columnGap (G := G) T T' c = 0) : dg G T' c = dg G (T ∩ T') c := by
  have hd := dg_union_add_dg_inter (G := G) T T' c
  have hm := dg_mono (G := G) (inter_subset_right (s₁ := T) (s₂ := T')) c
  unfold columnGap at hg
  omega

variable (G) in
def petalJ (C K T : Finset V) : Finset V :=
  (C \ corePlus G C K).filter fun c => 3 ≤ dg G T c

variable (G) in
def petalD (C K T : Finset V) : ℤ :=
  (#(T \ K) : ℤ) - #(petalJ G C K T)

lemma petalJ_subset (C K T : Finset V) : petalJ G C K T ⊆ C \ corePlus G C K :=
  filter_subset _ _

lemma petalJ_low {C K T : Finset V} {c : V} (hc : c ∈ petalJ G C K T) :
    dg G K c ≤ 1 := by
  obtain ⟨hcO, _⟩ := mem_filter.mp hc
  obtain ⟨hcC, hcN⟩ := mem_sdiff.mp hcO
  by_contra hh
  exact hcN (mem_filter.mpr ⟨hcC, by omega⟩)

/-- Actual zero gaps remove every other petal's original neighbors. -/
theorem petalJ_owner {A C K T T' : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C)
    (hT : T ∈ containingFamily G A C K) (hT' : T' ∈ containingFamily G A C K)
    (hne : T ≠ T') {c : V} (hc : c ∈ petalJ G C K T) : dg G (T' \ K) c = 0 := by
  obtain ⟨hi, _, hg⟩ := containing_intersection h hn hp hK hT hT' hne
  have hcC : c ∈ C := (mem_sdiff.mp (petalJ_subset (G := G) C K T hc)).1
  have hx := (mem_filter.mp hc).2
  have hz : dg G (T ∩ T') c ≤ 1 := by rw [hi]; exact petalJ_low hc
  have he := column_gap_zero_low hx hz (hg c hcC)
  have hd := dg_sdiff_add (G := G) (mem_containingFamily.mp hT').2 c
  rw [hi] at he
  omega

/-- Physical coverage plus C saturation pays every canonical petal column. -/
theorem petalJ_saturated {A C K T : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C)
    (hT : T ∈ containingFamily G A C K) {c : V} (hc : c ∈ petalJ G C K T) :
    dg G T c = 6 := by
  have hTA := (maxPositive_data h (mem_containingFamily.mp hT).1).1
  have hKT := (mem_containingFamily.mp hT).2
  have hcC : c ∈ C := (mem_sdiff.mp (petalJ_subset (G := G) C K T hc)).1
  have hz : dg G (A \ T) c = 0 := by
    apply card_eq_zero.mpr
    apply filter_eq_empty_iff.mpr
    intro r hr hadj
    obtain ⟨hrA, hrT⟩ := mem_sdiff.mp hr
    have hrK : r ∉ K := fun hh => hrT (hKT hh)
    obtain ⟨T', hTF', hKT', hrT'⟩ := high_cover h hn hp hK (mem_sdiff.mpr ⟨hrA, hrK⟩)
    have hT' : T' ∈ containingFamily G A C K := mem_containingFamily.mpr ⟨hTF', hKT'⟩
    have hne : T ≠ T' := by intro he; exact hrT (he.symm ▸ hrT')
    have hzero := petalJ_owner h hn hp hK hT hT' hne hc
    have hpositive : 0 < dg G (T' \ K) c :=
      card_pos.mpr ⟨r, mem_filter.mpr ⟨mem_sdiff.mpr ⟨hrT', hrK⟩, hadj⟩⟩
    omega
  have hd := dg_sdiff_add (G := G) hTA c
  rw [h.satC c hcC, hz] at hd
  omega

theorem petalJ_disjoint {A C K T T' : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C)
    (hT : T ∈ containingFamily G A C K) (hT' : T' ∈ containingFamily G A C K)
    (hne : T ≠ T') : Disjoint (petalJ G C K T) (petalJ G C K T') := by
  apply disjoint_left.mpr
  intro c hc hc'
  have hz := petalJ_owner h hn hp hK hT hT' hne hc
  have hsat := petalJ_saturated h hn hp hK hT' hc'
  have hlow := petalJ_low hc
  have hd := dg_sdiff_add (G := G) (mem_containingFamily.mp hT').2 c
  omega

theorem petal_selected {A C K T : Finset V} (_h : C02Input G A C)
    (_hn : NoTheta3 G A C) (_hp : APF G A C) (_hK : K ∈ maxHighFamily G A C)
    (hT : T ∈ containingFamily G A C K) :
    thetaC02 G C T = 8 - 4 * #T - 2 * #(corePlus G C K ∪ petalJ G C K T) +
      ec G T (corePlus G C K ∪ petalJ G C K T) := by
  have hY : corePlus G C K ∪ petalJ G C K T ⊆ C :=
    union_subset (corePlus_subset (G := G) C K)
      ((petalJ_subset (G := G) C K T).trans sdiff_subset)
  apply theta_selected hY
  · intro c hc
    rcases mem_union.mp hc with hc | hc
    · exact (mem_filter.mp hc).2.trans (dg_mono (mem_containingFamily.mp hT).2 c)
    · exact (show 2 ≤ 3 from by omega).trans (mem_filter.mp hc).2
  · intro c hc
    obtain ⟨hcC, hcN⟩ := mem_sdiff.mp hc
    have hcY : c ∉ corePlus G C K := fun hh => hcN (mem_union_left _ hh)
    by_contra hh
    have hcJ : c ∈ petalJ G C K T := mem_filter.mpr ⟨mem_sdiff.mpr ⟨hcC, hcY⟩, by omega⟩
    exact hcN (mem_union_right _ hcJ)

theorem petal_exact {A C K T : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C)
    (hT : T ∈ containingFamily G A C K) :
    (ec G (T \ K) (corePlus G C K) : ℤ) = 4 * petalD G C K T - 1 ∧
    (ec G (T \ K) (petalJ G C K T) : ℤ) + ec G K (petalJ G C K T) =
      6 * (#(petalJ G C K T) : ℤ) ∧
    gv G (T \ K) (petalJ G C K T) =
      2 * (3 * petalD G C K T + ec G K (petalJ G C K T)) ∧
    df G C (T \ K) = 1 + 2 * petalD G C K T + ec G K (petalJ G C K T) -
      ec G (T \ K) (C \ (corePlus G C K ∪ petalJ G C K T)) := by
  have hKT := (mem_containingFamily.mp hT).2
  have hY := corePlus_subset (G := G) C K
  have hJ := petalJ_subset (G := G) C K T
  have hYJ : Disjoint (corePlus G C K) (petalJ G C K T) := by
    apply disjoint_left.mpr
    intro c hcY hcJ
    exact (mem_sdiff.mp (hJ hcJ)).2 hcY
  have hJU : corePlus G C K ∪ petalJ G C K T ⊆ C := union_subset hY (hJ.trans sdiff_subset)
  have hcTK : (#(T \ K) : ℤ) + #K = #T := by exact_mod_cast card_sdiff_add_card_eq_card hKT
  have hcYJ : (#(corePlus G C K ∪ petalJ G C K T) : ℤ) =
      #(corePlus G C K) + #(petalJ G C K T) := by exact_mod_cast card_union_of_disjoint hYJ
  have heTYJ : ec G T (corePlus G C K ∪ petalJ G C K T) =
      ec G T (corePlus G C K) + ec G T (petalJ G C K T) := by
    unfold ec
    rw [← sum_add_distrib]
    exact sum_congr rfl fun r _ => dg_union_of_disjoint hYJ r
  have heTJ : ec G T (petalJ G C K T) = 6 * #(petalJ G C K T) := by
    rw [ec_comm]
    unfold ec
    rw [sum_congr rfl (fun c hc => petalJ_saturated h hn hp hK hT hc),
      sum_const, smul_eq_mul, mul_comm]
  have hePY := ec_sdiff_add_left (G := G) hKT (corePlus G C K)
  have hePJ := ec_sdiff_add_left (G := G) hKT (petalJ G C K T)
  have heTJZ : (ec G T (petalJ G C K T) : ℤ) = 6 * (#(petalJ G C K T) : ℤ) := by
    exact_mod_cast heTJ
  have heTYJZ : (ec G T (corePlus G C K ∪ petalJ G C K T) : ℤ) =
      ec G T (corePlus G C K) + ec G T (petalJ G C K T) := by exact_mod_cast heTYJ
  have hePYZ : (ec G (T \ K) (corePlus G C K) : ℤ) + ec G K (corePlus G C K) =
      ec G T (corePlus G C K) := by exact_mod_cast hePY
  have hePJZ : (ec G (T \ K) (petalJ G C K T) : ℤ) + ec G K (petalJ G C K T) =
      6 * (#(petalJ G C K T) : ℤ) := by exact_mod_cast (heTJ ▸ hePJ)
  have htT := (containing_theta_one h hn hp hK hT).1
  have htK := (maxHigh_data h hn hK).2.2.1
  have htTS := petal_selected h hn hp hK hT
  have htKS := theta_corePlus (G := G) C K
  have hE : (ec G (T \ K) (corePlus G C K) : ℤ) = 4 * petalD G C K T - 1 := by
    unfold petalD
    linarith
  have hgv : gv G (T \ K) (petalJ G C K T) =
      2 * (3 * petalD G C K T + ec G K (petalJ G C K T)) := by
    unfold gv petalD
    linarith
  have hePUnion : ec G (T \ K) (corePlus G C K ∪ petalJ G C K T) =
      ec G (T \ K) (corePlus G C K) + ec G (T \ K) (petalJ G C K T) := by
    unfold ec
    rw [← sum_add_distrib]
    exact sum_congr rfl fun r _ => dg_union_of_disjoint hYJ r
  have hePCR := ec_sdiff_add_right (G := G) hJU (T \ K)
  have hePCZ : (ec G (T \ K) (C \ (corePlus G C K ∪ petalJ G C K T)) : ℤ) +
      ec G (T \ K) (corePlus G C K) + ec G (T \ K) (petalJ G C K T) = ec G (T \ K) C := by
    rw [hePUnion] at hePCR
    rw [← add_assoc] at hePCR
    exact_mod_cast hePCR
  have hdef : df G C (T \ K) = 1 + 2 * petalD G C K T + ec G K (petalJ G C K T) -
      ec G (T \ K) (C \ (corePlus G C K ∪ petalJ G C K T)) := by
    rw [df_eq]
    unfold petalD at hE ⊢
    linarith
  exact ⟨hE, hePJZ, hgv, hdef⟩

theorem petal_d_bounds {A C K T : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C)
    (hT : T ∈ containingFamily G A C K) :
    1 ≤ petalD G C K T ∧ 2 * petalD G C K T ≤ 6 - highLoss G C K := by
  have hE := (petal_exact h hn hp hK hT).1
  have hE0 : (0 : ℤ) ≤ ec G (T \ K) (corePlus G C K) := by positivity
  have hTA := (maxPositive_data h (mem_containingFamily.mp hT).1).1
  have h3T := (maxPositive_data h (mem_containingFamily.mp hT).1).2.1
  have htT := (containing_theta_one h hn hp hK hT).1
  have hproper : T ≠ A := by
    intro he
    have hw := theta_whole h
    rw [he] at htT
    omega
  have hKT := (mem_containingFamily.mp hT).2
  have hY := corePlus_subset (G := G) C K
  have hJ := petalJ_subset (G := G) C K T
  have hYJ : Disjoint (corePlus G C K) (petalJ G C K T) :=
    disjoint_left.mpr fun c hcY hcJ => (mem_sdiff.mp (hJ hcJ)).2 hcY
  have hUC : corePlus G C K ∪ petalJ G C K T ⊆ C := union_subset hY (hJ.trans sdiff_subset)
  have htc : #T < #A := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hTA, hproper⟩)
  have huc := card_le_card hUC
  have hg := h.sparse T hTA (corePlus G C K ∪ petalJ G C K T) hUC (by omega) (by omega)
  have ht := petal_selected h hn hp hK hT
  have hcardP : (#(T \ K) : ℤ) + #K = #T := by exact_mod_cast card_sdiff_add_card_eq_card hKT
  have hcardY : (#(corePlus G C K ∪ petalJ G C K T) : ℤ) =
      #(corePlus G C K) + #(petalJ G C K T) := by exact_mod_cast card_union_of_disjoint hYJ
  have hLoss := (highPlus_geometry h hn hK).2.1
  unfold gv at hg
  unfold petalD
  constructor
  · unfold petalD at hE
    omega
  · linarith

/-- One-row maximality pays the actual boundary degree at every outside row. -/
theorem outside_row_degree {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hK : K ∈ maxHighFamily G A C) {r : V}
    (hr : r ∈ A \ K) : dg G (corePlus G C K) r ≤ 3 := by
  obtain ⟨hKA, _, htK, _, hmK⟩ := maxHigh_data h hn hK
  obtain ⟨hrA, hrK⟩ := mem_sdiff.mp hr
  have hsub : insert r K ⊆ A := insert_subset_iff.mpr ⟨hrA, hKA⟩
  have hne : insert r K ≠ K := by intro he; exact hrK (he ▸ mem_insert_self r K)
  have hmax := hmK (insert r K) hsub (subset_insert r K) hne
  have hY := corePlus_subset (G := G) C K
  have htheta : thetaC02 G C (insert r K) =
      8 - 4 * #(insert r K) - 2 * #(corePlus G C K) + ec G (insert r K) (corePlus G C K) := by
    apply theta_selected hY
    · intro c hc
      exact (mem_filter.mp hc).2.trans (dg_mono (subset_insert r K) c)
    · intro c hc
      obtain ⟨hcC, hcY⟩ := mem_sdiff.mp hc
      have hlo : dg G K c ≤ 1 := by
        by_contra hh
        exact hcY (mem_filter.mpr ⟨hcC, by omega⟩)
      have hd := dg_union_of_disjoint (G := G) (disjoint_singleton_left.mpr hrK) c
      simp only [singleton_union] at hd
      have hsingle := dg_le_card (G := G) ({r} : Finset V) c
      simp only [card_singleton] at hsingle
      omega
  have hcard : (#(insert r K) : ℤ) = #K + 1 := by exact_mod_cast card_insert_of_notMem hrK
  have he : ec G (insert r K) (corePlus G C K) =
      dg G (corePlus G C K) r + ec G K (corePlus G C K) := by
    unfold ec
    rw [sum_insert hrK]
  have hez : (ec G (insert r K) (corePlus G C K) : ℤ) =
      dg G (corePlus G C K) r + ec G K (corePlus G C K) := by exact_mod_cast he
  have ht := theta_corePlus (G := G) C K
  omega

theorem petals_pairwise {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C) :
    (containingFamily G A C K : Set (Finset V)).PairwiseDisjoint (fun T => T \ K) := by
  intro T hT T' hT' hne
  exact containing_petals_disjoint h hn hp hK hT hT' hne

theorem Jparts_pairwise {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C) :
    (containingFamily G A C K : Set (Finset V)).PairwiseDisjoint (petalJ G C K) := by
  intro T hT T' hT' hne
  exact petalJ_disjoint h hn hp hK hT hT' hne

theorem containing_card_sum {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C) :
    (∑ T ∈ containingFamily G A C K, (#(T \ K) : ℤ)) = #(A \ K) := by
  have hc := card_biUnion (petals_pairwise h hn hp hK)
  rw [containing_cover h hn hp hK] at hc
  exact_mod_cast hc.symm

theorem containing_edge_sum {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C)
    (Y : Finset V) :
    (∑ T ∈ containingFamily G A C K, (ec G (T \ K) Y : ℤ)) = ec G (A \ K) Y := by
  have hs := sum_biUnion (f := fun a => dg G Y a) (petals_pairwise h hn hp hK)
  rw [containing_cover h hn hp hK] at hs
  exact_mod_cast hs.symm

theorem containing_deficit_sum {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C) :
    (∑ T ∈ containingFamily G A C K, df G C (T \ K)) = df G C (A \ K) := by
  have hs := sum_biUnion (f := fun a => (6 : ℤ) - (dg G C a : ℤ))
    (petals_pairwise h hn hp hK)
  rw [containing_cover h hn hp hK] at hs
  exact hs.symm

theorem containing_Jcard_sum {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C) :
    (∑ T ∈ containingFamily G A C K, (#(petalJ G C K T) : ℤ)) =
      #((containingFamily G A C K).biUnion (petalJ G C K)) := by
  exact_mod_cast (card_biUnion (Jparts_pairwise h hn hp hK)).symm

theorem containing_Junion_subset (A C K : Finset V) :
    (containingFamily G A C K).biUnion (petalJ G C K) ⊆ C \ corePlus G C K := by
  intro c hc
  obtain ⟨T, _, hcT⟩ := mem_biUnion.mp hc
  exact petalJ_subset (G := G) C K T hcT

theorem containing_alpha_sum {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C) :
    (∑ T ∈ containingFamily G A C K, (ec G K (petalJ G C K T) : ℤ)) =
      ec G K ((containingFamily G A C K).biUnion (petalJ G C K)) := by
  have hs := sum_biUnion (f := fun c => dg G K c) (Jparts_pairwise h hn hp hK)
  have hnat : (∑ T ∈ containingFamily G A C K, ec G K (petalJ G C K T)) =
      ec G K ((containingFamily G A C K).biUnion (petalJ G C K)) := by
    calc
      _ = ∑ T ∈ containingFamily G A C K, ec G (petalJ G C K T) K :=
        sum_congr rfl fun T _ => ec_comm _ _
      _ = ec G ((containingFamily G A C K).biUnion (petalJ G C K)) K := hs.symm
      _ = _ := ec_comm _ _
  exact_mod_cast hnat

theorem outside_alpha_budget {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hK : K ∈ maxHighFamily G A C) :
    (ec G K (C \ corePlus G C K) : ℤ) ≤ highLoss G C K := by
  have hKA := (maxHigh_data h hn hK).1
  have hY := corePlus_subset (G := G) C K
  have hd := df_eq_df_add_ec (G := G) hY K
  have hdf : 0 ≤ df G C K :=
    sum_nonneg fun a ha => by have hh := h.capA a (hKA ha); omega
  have hl : df G (corePlus G C K) K = highLoss G C K := df_eq _ _
  rw [hl] at hd
  linarith

theorem containing_alpha_budget {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C) :
    (∑ T ∈ containingFamily G A C K, (ec G K (petalJ G C K T) : ℤ)) ≤ highLoss G C K := by
  rw [containing_alpha_sum h hn hp hK]
  have he := ec_mono_right (G := G) K (containing_Junion_subset (G := G) A C K)
  have hez : (ec G K ((containingFamily G A C K).biUnion (petalJ G C K)) : ℤ) ≤
      ec G K (C \ corePlus G C K) := by exact_mod_cast he
  exact hez.trans (outside_alpha_budget h hn hK)

omit [DecidableEq V] in
theorem c02_total_deficit {A C : Finset V} (h : C02Input G A C) : df G C A = 12 := by
  have he : ec G A C = 6 * #C := by
    rw [ec_comm]
    unfold ec
    rw [sum_congr rfl h.satC, sum_const, smul_eq_mul, mul_comm]
  have hez : (ec G A C : ℤ) = 6 * (#C : ℤ) := by exact_mod_cast he
  have hc : (#A : ℤ) = #C + 2 := by exact_mod_cast h.card
  rw [df_eq]
  linarith

omit [DecidableEq V] in
theorem c02_deficit_bounds {A C Z : Finset V} (h : C02Input G A C)
    (hZ : Z ⊆ A) : 0 ≤ df G C Z ∧ df G C Z ≤ 2 * (#Z : ℤ) := by
  constructor
  · exact sum_nonneg fun a ha => by have hc := h.capA a (hZ ha); omega
  · calc
      _ ≤ ∑ _a ∈ Z, (2 : ℤ) := sum_le_sum fun a ha => by
        have hm := h.minA a (hZ ha)
        omega
      _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

theorem petal_alpha_bound {A C K T : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hK : K ∈ maxHighFamily G A C) :
    (ec G K (petalJ G C K T) : ℤ) ≤ highLoss G C K := by
  have hm := ec_mono_right (G := G) K (petalJ_subset (G := G) C K T)
  have hmz : (ec G K (petalJ G C K T) : ℤ) ≤ ec G K (C \ corePlus G C K) :=
    by exact_mod_cast hm
  exact hmz.trans (outside_alpha_budget h hn hK)

/-- The small support case uses literal C saturation, not a sparsity extrapolation. -/
theorem petal_small {A C K T : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C)
    (hT : T ∈ containingFamily G A C K)
    (hsmall : #(T \ K) + #(petalJ G C K T) ≤ 2) :
    #(T \ K) = 1 ∧ #(petalJ G C K T) = 0 ∧ petalD G C K T = 1 ∧
      ec G (T \ K) (corePlus G C K) = 3 ∧ df G C (T \ K) ≤ 2 := by
  have hKT := (mem_containingFamily.mp hT).2
  have hj : #(petalJ G C K T) = 0 := by
    by_contra hne
    obtain ⟨c, hc⟩ := card_pos.mp (show 0 < #(petalJ G C K T) by omega)
    have hsat := petalJ_saturated h hn hp hK hT hc
    have hlo := petalJ_low (G := G) hc
    have hd := dg_sdiff_add (G := G) hKT c
    have hdc := dg_le_card (G := G) (T \ K) c
    omega
  have he := (petal_exact h hn hp hK hT).1
  have hd := (petal_d_bounds h hn hp hK hT).1
  have hrows : ec G (T \ K) (corePlus G C K) ≤ 3 * #(T \ K) := by
    unfold ec
    calc
      _ ≤ ∑ _r ∈ T \ K, 3 := sum_le_sum fun r hr => by
        have hTA := (maxPositive_data h (mem_containingFamily.mp hT).1).1
        exact outside_row_degree h hn hK (mem_sdiff.mpr ⟨hTA (mem_sdiff.mp hr).1,
          (mem_sdiff.mp hr).2⟩)
      _ = _ := by simp only [sum_const, smul_eq_mul]; omega
  have hz : (ec G (T \ K) (corePlus G C K) : ℤ) ≤ 3 * (#(T \ K) : ℤ) :=
    by exact_mod_cast hrows
  have hp1 : #(T \ K) = 1 := by unfold petalD at he hd; omega
  have hd1 : petalD G C K T = 1 := by unfold petalD; omega
  have he3 : ec G (T \ K) (corePlus G C K) = 3 := by omega
  have hTA := (maxPositive_data h (mem_containingFamily.mp hT).1).1
  have hdef := (c02_deficit_bounds h (sdiff_subset (s := T) (t := K) |>.trans hTA)).2
  exact ⟨hp1, hj, hd1, he3, by omega⟩

theorem petal_large_g {A C K T : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C)
    (hT : T ∈ containingFamily G A C K)
    (hlarge : 3 ≤ #(T \ K) + #(petalJ G C K T)) :
    7 ≤ 3 * petalD G C K T + ec G K (petalJ G C K T) := by
  have hTA := (maxPositive_data h (mem_containingFamily.mp hT).1).1
  have ht := (containing_theta_one h hn hp hK hT).1
  have hne : T ≠ A := by intro he; rw [he, theta_whole h] at ht; omega
  have htc := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hTA, hne⟩)
  have hpc := card_le_card (sdiff_subset (s := T) (t := K))
  have hJA := (petalJ_subset (G := G) C K T).trans sdiff_subset
  have hjc := card_le_card hJA
  have hg := h.sparse (T \ K) (sdiff_subset.trans hTA)
    (petalJ G C K T) hJA hlarge (by omega)
  have he := (petal_exact h hn hp hK hT).2.2.1
  linarith

theorem no_loss_four {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C) :
    highLoss G C K ≠ 4 := by
  intro h4
  have hE : ∀ T ∈ containingFamily G A C K,
      (ec G (T \ K) (corePlus G C K) : ℤ) = 3 := by
    intro T hT
    have hd := petal_d_bounds h hn hp hK hT
    have he := (petal_exact h hn hp hK hT).1
    omega
  have hs := containing_edge_sum h hn hp hK (corePlus G C K)
  have hb := (highPlus_boundary h hn hK).1
  rw [sum_congr rfl hE, sum_const, nsmul_eq_mul] at hs
  omega

theorem loss_zero_original_deficit {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hK : K ∈ maxHighFamily G A C)
    (h0 : highLoss G C K = 0) : df G C K = 0 := by
  have hY := corePlus_subset (G := G) C K
  have hd := df_eq_df_add_ec (G := G) hY K
  have hdf := (c02_deficit_bounds h (maxHigh_data h hn hK).1).1
  have hl : df G (corePlus G C K) K = highLoss G C K := df_eq _ _
  rw [hl, h0] at hd
  have he : (0 : ℤ) ≤ ec G K (C \ corePlus G C K) := by positivity
  omega

theorem loss_zero_petal_charge {A C K T : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C)
    (h0 : highLoss G C K = 0) (hT : T ∈ containingFamily G A C K) :
    3 * df G C (T \ K) ≤ 2 * (ec G (T \ K) (corePlus G C K) : ℤ) ∧
      (3 ≤ #(T \ K) + #(petalJ G C K T) →
       3 * df G C (T \ K) < 2 * (ec G (T \ K) (corePlus G C K) : ℤ)) := by
  have ha := petal_alpha_bound h hn (T := T) hK
  have ha0 : ec G K (petalJ G C K T) = 0 := by omega
  have hd := petal_d_bounds h hn hp hK hT
  have he := petal_exact h hn hp hK hT
  have ho : (0 : ℤ) ≤ ec G (T \ K) (C \ (corePlus G C K ∪ petalJ G C K T)) :=
    by positivity
  by_cases hl : 3 ≤ #(T \ K) + #(petalJ G C K T)
  · have hg := petal_large_g h hn hp hK hT hl
    constructor <;> omega
  · have hs := petal_small h hn hp hK hT (by omega)
    exact ⟨by omega, by omega⟩

/-- Equality of actual global charges forces all six loss-zero petals to be singletons. -/
theorem loss_zero_shape {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C)
    (h0 : highLoss G C K = 0) :
    (∀ T ∈ containingFamily G A C K, #(T \ K) = 1 ∧
      #(petalJ G C K T) = 0 ∧ ec G (T \ K) (corePlus G C K) = 3 ∧
        df G C (T \ K) = 2) ∧ #(A \ K) = 6 ∧ #(C \ corePlus G C K) = 1 := by
  have hK0 := loss_zero_original_deficit h hn hK h0
  have htotal := c02_total_deficit h
  have hpart := df_sdiff_add (G := G) (S := C) (maxHigh_data h hn hK).1
  have hR : df G C (A \ K) = 12 := by omega
  have hb := (highPlus_boundary h hn hK).1
  have hds := containing_deficit_sum h hn hp hK
  have hes := containing_edge_sum h hn hp hK (corePlus G C K)
  have heq : (∑ T ∈ containingFamily G A C K, 3 * df G C (T \ K)) =
      ∑ T ∈ containingFamily G A C K,
        2 * (ec G (T \ K) (corePlus G C K) : ℤ) := by
    rw [← mul_sum, ← mul_sum, hds, hes]
    omega
  have hpoint := (sum_eq_sum_iff_of_le fun T hT =>
    (loss_zero_petal_charge h hn hp hK h0 hT).1).mp heq
  have hshape : ∀ T ∈ containingFamily G A C K, #(T \ K) = 1 ∧
      #(petalJ G C K T) = 0 ∧ ec G (T \ K) (corePlus G C K) = 3 ∧
        df G C (T \ K) = 2 := by
    intro T hT
    have heqT := hpoint T hT
    have hsmall : #(T \ K) + #(petalJ G C K T) ≤ 2 := by
      have hh := (loss_zero_petal_charge h hn hp hK h0 hT).2
      omega
    obtain ⟨hp1, hj0, _, he3, _⟩ := petal_small h hn hp hK hT hsmall
    exact ⟨hp1, hj0, he3, by omega⟩
  have hE : ∀ T ∈ containingFamily G A C K,
      (ec G (T \ K) (corePlus G C K) : ℤ) = 3 := by
    intro T hT; exact_mod_cast (hshape T hT).2.2.1
  have hcard : #(containingFamily G A C K) = 6 := by
    rw [sum_congr rfl hE, sum_const, nsmul_eq_mul] at hes
    omega
  have hcs := containing_card_sum h hn hp hK
  have hp1 : ∀ T ∈ containingFamily G A C K, (#(T \ K) : ℤ) = 1 := by
    intro T hT; exact_mod_cast (hshape T hT).1
  rw [sum_congr rfl hp1, sum_const, nsmul_eq_mul] at hcs
  have hR6 : #(A \ K) = 6 := by omega
  have hbound := (highPlus_boundary h hn hK).2
  exact ⟨hshape, hR6, by omega⟩

theorem loss_zero_rows {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C)
    (h0 : highLoss G C K = 0) {r : V} (hr : r ∈ A \ K) :
    dg G (corePlus G C K) r = 3 ∧ dg G C r = 4 := by
  have hcov := containing_cover h hn hp hK
  rw [← hcov] at hr
  obtain ⟨T, hT, hrP⟩ := mem_biUnion.mp hr
  obtain ⟨hp1, _, hE, hd⟩ := (loss_zero_shape h hn hp hK h0).1 T hT
  obtain ⟨a, hPa⟩ := card_eq_one.mp hp1
  have har : r = a := by rw [hPa] at hrP; simpa using hrP
  have hP : T \ K = {r} := by simpa [har] using hPa
  rw [hP] at hE hd
  simp only [ec, sum_singleton] at hE
  simp only [df, sum_singleton] at hd
  exact ⟨hE, by omega⟩

/-- Every actual outside support of order at least two has nonpositive theta in loss zero. -/
theorem loss_zero_outside_theta {A C K B : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C)
    (h0 : highLoss G C K = 0) (hB : B ⊆ A \ K) (h2 : 2 ≤ #B) :
    thetaC02 G C B ≤ 0 := by
  by_cases hb2 : #B = 2
  · have ht := theta_small (G := G) C (Z := B) (by omega)
    omega
  have h3 : 3 ≤ #B := by omega
  have hY := corePlus_subset (G := G) C K
  have hKA := (maxHigh_data h hn hK).1
  have hRcol : ∀ c ∈ corePlus G C K, dg G B c ≤ 4 := by
    intro c hc
    have hcC := hY hc
    have hkc := (mem_filter.mp hc).2
    have hsat := h.satC c hcC
    have hsplit := dg_sdiff_add (G := G) hKA c
    have hm := dg_mono (G := G) hB c
    omega
  have hE : (ec G B (corePlus G C K) : ℤ) = 3 * (#B : ℤ) := by
    unfold ec
    rw [sum_congr rfl (fun r hr => (loss_zero_rows h hn hp hK h0 (hB hr)).1),
      sum_const, smul_eq_mul]
    push_cast
    ring
  obtain ⟨c, hC⟩ := card_eq_one.mp (loss_zero_shape h hn hp hK h0).2.2
  have hout : (∑ c ∈ C \ corePlus G C K, max 0 ((dg G B c : ℤ) - 2)) ≤ (#B : ℤ) - 2 := by
    rw [hC, sum_singleton]
    have hdeg := dg_le_card (G := G) B c
    omega
  have hsplit := sum_sdiff hY (f := fun c => max 0 ((dg G B c : ℤ) - 2))
  have hec : (∑ c ∈ corePlus G C K, (dg G B c : ℤ)) = ec G B (corePlus G C K) := by
    rw [ec_comm]; unfold ec; rw [Nat.cast_sum]
  by_cases hb3 : #B = 3
  · have hin : 3 * (∑ c ∈ corePlus G C K, max 0 ((dg G B c : ℤ) - 2)) ≤
        (ec G B (corePlus G C K) : ℤ) := by
      rw [mul_sum, ← hec]
      exact sum_le_sum fun c _ => by have hc := dg_le_card (G := G) B c; omega
    unfold thetaC02
    omega
  · have hin : 2 * (∑ c ∈ corePlus G C K, max 0 ((dg G B c : ℤ) - 2)) ≤
        (ec G B (corePlus G C K) : ℤ) := by
      rw [mul_sum, ← hec]
      exact sum_le_sum fun c hc => by have hh := hRcol c hc; omega
    unfold thetaC02
    omega

theorem loss_zero_module {A C K T : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hK : K ∈ maxHighFamily G A C)
    (h0 : highLoss G C K = 0) (hT : T ∈ maxPositiveFamily G A C) :
    K ⊆ T ∨ Disjoint K T := by
  by_cases hKT : K ⊆ T
  · exact Or.inl hKT
  · right
    have hI : #(K ∩ T) ≤ 1 := by
      by_contra hh
      exact hKT (high_F_containment h hn hK hT (by omega))
    by_contra hdis
    have hne : (K ∩ T).Nonempty := by
      by_contra hnI
      have he := not_nonempty_iff_eq_empty.mp hnI
      exact hdis (disjoint_iff_inter_eq_empty.mpr he)
    have h1 : #(K ∩ T) = 1 := by have hc := card_pos.mpr hne; omega
    obtain ⟨a, hi⟩ := card_eq_one.mp h1
    have ha : a ∈ K := mem_inter.mp (show a ∈ K ∩ T by rw [hi]; simp) |>.1
    have hl := (partial_absorbed_loss h hn hK hT hKT hi).2
    have hiL := highPlus_individual_loss h hn hK ha
    have ht := (maxPositive_data h hT).2.2.1
    omega

theorem no_loss_zero {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C) :
    highLoss G C K ≠ 0 := by
  intro h0
  have hR6 := (loss_zero_shape h hn hp hK h0).2.1
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (show 1 < #(A \ K) by omega)
  obtain ⟨T, hT, haT, hbT⟩ := hp a (mem_sdiff.mp ha).1 b (mem_sdiff.mp hb).1 hab
  rcases loss_zero_module h hn hK h0 hT with hKT | hdis
  · have hTF := mem_containingFamily.mpr ⟨hT, hKT⟩
    have hp1 := ((loss_zero_shape h hn hp hK h0).1 T hTF).1
    obtain ⟨r, hP⟩ := card_eq_one.mp hp1
    have haP : a ∈ T \ K := mem_sdiff.mpr ⟨haT, (mem_sdiff.mp ha).2⟩
    have hbP : b ∈ T \ K := mem_sdiff.mpr ⟨hbT, (mem_sdiff.mp hb).2⟩
    rw [hP] at haP hbP
    simp only [mem_singleton] at haP hbP
    exact hab (haP.trans hbP.symm)
  · have hTA := (maxPositive_data h hT).1
    have hsub : T ⊆ A \ K := by
      intro r hr
      refine mem_sdiff.mpr ⟨hTA hr, ?_⟩
      intro hrK
      exact disjoint_left.mp hdis hrK hr
    have ht := (maxPositive_data h hT).2.2.1
    have hlo := loss_zero_outside_theta h hn hp hK h0 hsub
      (by have hc := (maxPositive_data h hT).2.1; omega)
    omega

theorem loss_two_petal_cases {A C K T : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C)
    (h2 : highLoss G C K = 2) (hT : T ∈ containingFamily G A C K) :
    (petalD G C K T = 1 ∨ petalD G C K T = 2) ∧
      (petalD G C K T = 2 → 1 ≤ ec G K (petalJ G C K T)) := by
  have hd := petal_d_bounds h hn hp hK hT
  have ha := petal_alpha_bound h hn (T := T) hK
  constructor
  · omega
  · intro hd2
    have hl : 3 ≤ #(T \ K) + #(petalJ G C K T) := by
      by_contra hh
      have hs := petal_small h hn hp hK hT (by omega)
      omega
    have hg := petal_large_g h hn hp hK hT hl
    omega

/-- The actual two-petal family is forced by its integral edge and incidence charges. -/
theorem loss_two_counts {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C)
    (h2 : highLoss G C K = 2) :
    #(containingFamily G A C K) = 2 ∧
      (∀ T ∈ containingFamily G A C K, petalD G C K T = 2 ∧
        ec G (T \ K) (corePlus G C K) = 7 ∧ ec G K (petalJ G C K T) = 1) ∧
      df G C K = 0 ∧
      (containingFamily G A C K).biUnion (petalJ G C K) = C \ corePlus G C K := by
  classical
  let F := containingFamily G A C K
  let F2 := F.filter fun T => petalD G C K T = 2
  have hF2 : F2 ⊆ F := filter_subset _ _
  have hα : ∀ T ∈ F2, (1 : ℤ) ≤ ec G K (petalJ G C K T) := by
    intro T hT
    obtain ⟨hTF, hd⟩ := mem_filter.mp hT
    exact_mod_cast (loss_two_petal_cases h hn hp hK h2 hTF).2 hd
  have hαsum := containing_alpha_budget h hn hp hK
  have hcount2 : (#F2 : ℤ) ≤ 2 := by
    calc
      _ = ∑ _T ∈ F2, (1 : ℤ) := by simp
      _ ≤ ∑ T ∈ F2, (ec G K (petalJ G C K T) : ℤ) := sum_le_sum hα
      _ ≤ ∑ T ∈ F, (ec G K (petalJ G C K T) : ℤ) :=
        sum_le_sum_of_subset_of_nonneg hF2 (fun _ _ _ => by positivity)
      _ ≤ 2 := by simpa [F, h2] using hαsum
  have hE : ∀ T ∈ F, (ec G (T \ K) (corePlus G C K) : ℤ) =
      3 + if petalD G C K T = 2 then 4 else 0 := by
    intro T hT
    have hd := (loss_two_petal_cases h hn hp hK h2 hT).1
    have he := (petal_exact h hn hp hK hT).1
    split_ifs <;> omega
  have hsumE := containing_edge_sum h hn hp hK (corePlus G C K)
  have hboundary := (highPlus_boundary h hn hK).1
  have hboole : (∑ T ∈ F, if petalD G C K T = 2 then (4 : ℤ) else 0) =
      4 * (#F2 : ℤ) := by
    rw [← sum_filter]
    simp only [F2, sum_const, nsmul_eq_mul]
    ring
  have hEtotal : (ec G (A \ K) (corePlus G C K) : ℤ) = 3 * (#F : ℤ) + 4 * #F2 := by
    rw [← hsumE]
    change (∑ T ∈ F, (ec G (T \ K) (corePlus G C K) : ℤ)) = _
    rw [sum_congr rfl hE, sum_add_distrib, hboole, sum_const, nsmul_eq_mul]
    ring
  have hcard2 : #F2 = 2 := by omega
  have hcard : #F = 2 := by omega
  have hsame : F2 = F := eq_of_subset_of_card_le hF2 (by omega)
  have hd2 : ∀ T ∈ F, petalD G C K T = 2 := by
    intro T hT
    rw [← hsame] at hT
    exact (mem_filter.mp hT).2
  have hαF : ∀ T ∈ F, (1 : ℤ) ≤ ec G K (petalJ G C K T) := by
    intro T hT
    exact_mod_cast (loss_two_petal_cases h hn hp hK h2 hT).2 (hd2 T hT)
  have hαtotal : (∑ T ∈ F, (ec G K (petalJ G C K T) : ℤ)) = 2 := by
    have hle := sum_le_sum hαF
    have hsz : (∑ _T ∈ F, (1 : ℤ)) = 2 := by simp [hcard]
    change (∑ T ∈ F, (ec G K (petalJ G C K T) : ℤ)) ≤ _ at hαsum
    rw [h2] at hαsum
    omega
  have hαpoint := (sum_eq_sum_iff_of_le hαF).mp
    (show (∑ _T ∈ F, (1 : ℤ)) = ∑ T ∈ F, (ec G K (petalJ G C K T) : ℤ) by
      rw [hαtotal]; simp [hcard])
  have hα1 : ∀ T ∈ F, ec G K (petalJ G C K T) = 1 := by
    intro T hT
    have heq := hαpoint T hT
    omega
  have hKα := outside_alpha_budget h hn hK
  have hJsub := containing_Junion_subset (G := G) A C K
  have hJec := ec_mono_right (G := G) K hJsub
  have hαexact := containing_alpha_sum h hn hp hK
  have hKout : (ec G K (C \ corePlus G C K) : ℤ) = 2 := by
    change (∑ T ∈ F, (ec G K (petalJ G C K T) : ℤ)) = _ at hαexact
    rw [hαtotal] at hαexact
    omega
  have hdfK : df G C K = 0 := by
    have heq := df_eq_df_add_ec (G := G) (corePlus_subset (G := G) C K) K
    have hl : df G (corePlus G C K) K = highLoss G C K := df_eq _ _
    rw [hl, h2] at heq
    omega
  have hdsum : (∑ T ∈ F, petalD G C K T) = 4 := by
    rw [sum_congr rfl hd2, sum_const, nsmul_eq_mul]
    omega
  have hps := containing_card_sum h hn hp hK
  have hjs := containing_Jcard_sum h hn hp hK
  have hsd : (∑ T ∈ F, petalD G C K T) =
      (#(A \ K) : ℤ) - #((containingFamily G A C K).biUnion (petalJ G C K)) := by
    unfold petalD
    rw [sum_sub_distrib]
    exact congrArg₂ (fun x y : ℤ => x - y) hps hjs
  have hRb := (highPlus_boundary h hn hK).2
  have hJcard : #((containingFamily G A C K).biUnion (petalJ G C K)) =
      #(C \ corePlus G C K) := by omega
  have hJfull := eq_of_subset_of_card_le hJsub hJcard.ge
  refine ⟨hcard, ?_, hdfK, hJfull⟩
  intro T hT
  have he := (petal_exact h hn hp hK hT).1
  exact ⟨hd2 T hT, by have hd := hd2 T hT; omega, hα1 T hT⟩

/-- No outside column leaks from its actual owning petal once all J columns are used. -/
theorem loss_two_out_zero {A C K T : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C)
    (h2 : highLoss G C K = 2) (hT : T ∈ containingFamily G A C K) :
    ec G (T \ K) (C \ (corePlus G C K ∪ petalJ G C K T)) = 0 := by
  have hJfull := (loss_two_counts h hn hp hK h2).2.2.2
  have hdeg : ∀ c ∈ C \ (corePlus G C K ∪ petalJ G C K T), dg G (T \ K) c = 0 := by
    intro c hc
    obtain ⟨hcC, hcnot⟩ := mem_sdiff.mp hc
    have hcY : c ∉ corePlus G C K := fun hh => hcnot (mem_union_left _ hh)
    have hcJ : c ∉ petalJ G C K T := fun hh => hcnot (mem_union_right _ hh)
    have hcU : c ∈ (containingFamily G A C K).biUnion (petalJ G C K) := by
      rw [hJfull]; exact mem_sdiff.mpr ⟨hcC, hcY⟩
    obtain ⟨T', hT', hcT'⟩ := mem_biUnion.mp hcU
    have hne : T' ≠ T := by intro he; exact hcJ (he ▸ hcT')
    exact petalJ_owner h hn hp hK hT' hT hne hcT'
  rw [ec_comm]
  unfold ec
  rw [sum_congr rfl hdeg]
  simp

theorem loss_two_shape {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C)
    (h2 : highLoss G C K = 2) :
    #(containingFamily G A C K) = 2 ∧
      (∀ T ∈ containingFamily G A C K, petalD G C K T = 2 ∧
        ec G (T \ K) (corePlus G C K) = 7 ∧ ec G K (petalJ G C K T) = 1 ∧
          df G C (T \ K) = 6) ∧ (∀ a ∈ K, dg G C a = 6) := by
  obtain ⟨hcard, hcounts, hdfK, _⟩ := loss_two_counts h hn hp hK h2
  refine ⟨hcard, ?_, ?_⟩
  · intro T hT
    obtain ⟨hd, he, hα⟩ := hcounts T hT
    have hout := loss_two_out_zero h hn hp hK h2 hT
    have hdef := (petal_exact h hn hp hK hT).2.2.2
    exact ⟨hd, he, hα, by omega⟩
  · intro a ha
    exact dg_eq_six_of_df_eq_zero (fun a ha => h.capA a ((maxHigh_data h hn hK).1 ha)) hdfK ha

theorem high_loss_two {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C) :
    highLoss G C K = 2 := by
  have hg := (highPlus_geometry h hn hK).1
  have h0 := no_loss_zero h hn hp hK
  have h4 := no_loss_four h hn hp hK
  omega

lemma singleton_gap_both_plus {K L : Finset V} {a c : V}
    (hi : K ∩ L = {a}) (hx : 2 ≤ dg G K c) (hy : 2 ≤ dg G L c)
    (hadj : G.Adj a c) : columnGap (G := G) K L c = 1 := by
  have hd := dg_union_add_dg_inter (G := G) K L c
  have hz : dg G ({a} : Finset V) c = 1 := by
    simp only [dg, filter_singleton, if_pos (G.adj_symm hadj), card_singleton]
  unfold columnGap
  rw [hi, hz] at hd ⊢
  omega

/-- The singleton intersection is excluded by the two actual shared absorbed neighbors. -/
theorem high_disjoint {A C K L : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C)
    (hL : L ∈ maxHighFamily G A C) (hne : K ≠ L) : Disjoint K L := by
  classical
  have hi1 := high_inter_card_le_one h hn hK hL hne
  by_contra hdis
  have hi0 : 0 < #(K ∩ L) := by
    by_contra hh
    have he : K ∩ L = ∅ := card_eq_zero.mp (by omega)
    exact hdis (disjoint_iff_inter_eq_empty.mpr he)
  obtain ⟨a, hi⟩ := card_eq_one.mp (show #(K ∩ L) = 1 by omega)
  have ha := mem_inter.mp (show a ∈ K ∩ L by rw [hi]; simp)
  obtain ⟨hKA, _, htK, _, hmK⟩ := maxHigh_data h hn hK
  obtain ⟨hLA, _, htL, _, _⟩ := maxHigh_data h hn hL
  have hUne : K ∪ L ≠ K := by
    intro he
    have hLK : L ⊆ K := he ▸ subset_union_right
    obtain ⟨_, hmL⟩ := mem_maximalMembers.mp hL
    obtain ⟨hKset, _⟩ := mem_maximalMembers.mp hK
    exact hne (hmL K hKset hLK)
  have hU := hmK (K ∪ L) (union_subset hKA hLA) subset_union_left hUne
  have hsingle : thetaC02 G C ({a} : Finset V) = 4 := by
    simpa using (theta_small (G := G) C (Z := {a}) (by simp))
  have hg := theta_gap_sum (G := G) C K L
  rw [hi, hsingle, htK, htL] at hg
  have hgap : (∑ c ∈ C, columnGap (G := G) K L c) ≤ 1 := by omega
  have hKloss := highPlus_individual_loss h hn hK ha.1
  have hLloss := highPlus_individual_loss h hn hL ha.2
  rw [high_loss_two h hn hp hK] at hKloss
  rw [high_loss_two h hn hp hL] at hLloss
  have hd := dg_union_add_dg_inter (G := G) (corePlus G C K) (corePlus G C L) a
  have hdu := dg_mono (G := G) (union_subset (corePlus_subset (G := G) C K)
    (corePlus_subset (G := G) C L)) a
  have hcap := h.capA a (hKA ha.1)
  have hcommon : 2 ≤ dg G (corePlus G C K ∩ corePlus G C L) a := by omega
  let S := (corePlus G C K ∩ corePlus G C L).filter fun c => G.Adj a c
  have hSC : S ⊆ C := by
    intro c hc
    exact (corePlus_subset (G := G) C K) (mem_inter.mp (mem_filter.mp hc).1).1
  have hunit : ∀ c ∈ S, columnGap (G := G) K L c = 1 := by
    intro c hc
    obtain ⟨hci, hac⟩ := mem_filter.mp hc
    obtain ⟨hcK, hcL⟩ := mem_inter.mp hci
    exact singleton_gap_both_plus hi (mem_filter.mp hcK).2 (mem_filter.mp hcL).2 hac
  have hsum := sum_le_sum_of_subset_of_nonneg hSC
    (fun c _ _ => columnGap_nonneg (G := G) K L c)
  have hs : (∑ c ∈ S, columnGap (G := G) K L c) =
      (dg G (corePlus G C K ∩ corePlus G C L) a : ℤ) := by
    rw [sum_congr rfl hunit]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    rfl
  rw [hs] at hsum
  omega

theorem partial_canonical_degree {A C K T : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C)
    (hT : T ∈ maxPositiveFamily G A C) (hnot : ¬ K ⊆ T)
    {a : V} (hi : K ∩ T = {a}) :
    thetaC02 G C T = 1 ∧ dg G (cpr G C T) a = 3 ∧ thetaC02 G C (T.erase a) = 2 := by
  classical
  obtain ⟨hKA, _, htK, _, _⟩ := maxHigh_data h hn hK
  obtain ⟨hTA, h3T, htT, hmT⟩ := maxPositive_data h hT
  obtain ⟨haK, haT⟩ := mem_inter.mp (show a ∈ K ∩ T by rw [hi]; simp)
  have hloss := highPlus_individual_loss h hn hK haK
  rw [high_loss_two h hn hp hK] at hloss
  have hpartial := (partial_absorbed_loss h hn hK hT hnot hi).2
  have ht1 : thetaC02 G C T = 1 := by omega
  have hplus : dg G (corePlus G C K) a = 4 := by omega
  have hUne : K ∪ T ≠ T := by intro he; exact hnot (he ▸ subset_union_left)
  have hU := hmT (K ∪ T) (union_subset hKA hTA) subset_union_right hUne
  have hsingle : thetaC02 G C ({a} : Finset V) = 4 := by
    simpa using (theta_small (G := G) C (Z := {a}) (by simp))
  have hg := theta_gap_sum (G := G) C K T
  rw [hi, hsingle, htK, ht1] at hg
  have hgap : (∑ c ∈ C, columnGap (G := G) K T c) ≤ 1 := by omega
  let S := (corePlus G C K ∩ cpr G C T).filter fun c => G.Adj a c
  have hSC : S ⊆ C := by
    intro c hc
    exact (mem_filter.mp (mem_inter.mp (mem_filter.mp hc).1).1).1
  have hunit : ∀ c ∈ S, columnGap (G := G) K T c = 1 := by
    intro c hc
    obtain ⟨hci, hac⟩ := mem_filter.mp hc
    obtain ⟨hcK, hcT⟩ := mem_inter.mp hci
    exact singleton_gap_one_plus hi (mem_filter.mp hcK).2 (mem_cpr.mp hcT).2 hac
  have hsum := sum_le_sum_of_subset_of_nonneg hSC
    (fun c _ _ => columnGap_nonneg (G := G) K T c)
  have hs : (∑ c ∈ S, columnGap (G := G) K T c) =
      (dg G (corePlus G C K ∩ cpr G C T) a : ℤ) := by
    rw [sum_congr rfl hunit]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    rfl
  rw [hs] at hsum
  have hd := dg_union_add_dg_inter (G := G) (corePlus G C K) (cpr G C T) a
  have hdu := dg_mono (G := G) (union_subset (corePlus_subset (G := G) C K)
    (cpr_subset (G := G) C T)) a
  have hcap := h.capA a (hKA haK)
  have hdeg3 : dg G (cpr G C T) a ≤ 3 := by omega
  have hEr := theta_erase (G := G) (C := C) haT
  have hcard : 2 ≤ #(T.erase a) := by have hc := card_erase_add_one haT; omega
  have htheta := theta_nontrivial (Z := T.erase a) hn ((erase_subset _ _).trans hTA) hcard
  exact ⟨ht1, by omega, by omega⟩

/-- The deletion produces another actual high core and rules out partial intersection. -/
theorem high_module {A C K T : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C)
    (hT : T ∈ maxPositiveFamily G A C) : K ⊆ T ∨ Disjoint K T := by
  classical
  by_cases hKT : K ⊆ T
  · exact Or.inl hKT
  · right
    have hI : #(K ∩ T) ≤ 1 := by
      by_contra hh
      exact hKT (high_F_containment h hn hK hT (by omega))
    by_contra hdis
    have hI0 : 0 < #(K ∩ T) := by
      by_contra hh
      exact hdis (disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp (by omega)))
    obtain ⟨a, hi⟩ := card_eq_one.mp (show #(K ∩ T) = 1 by omega)
    obtain ⟨haK, haT⟩ := mem_inter.mp (show a ∈ K ∩ T by rw [hi]; simp)
    obtain ⟨_, _, hθerase⟩ := partial_canonical_degree h hn hp hK hT hKT hi
    have hTA := (maxPositive_data h hT).1
    have hEA : T.erase a ⊆ A := (erase_subset _ _).trans hTA
    have h3E : 3 ≤ #(T.erase a) := by
      by_contra hh
      have hs := theta_small (G := G) C (Z := T.erase a) (by omega)
      omega
    obtain ⟨L, hL, hEL⟩ := high_extension (G := G) (C := C) hEA h3E (by omega)
    have hLT : L ⊆ T := by
      have hsub : T.erase a ⊆ L ∩ T := subset_inter hEL (erase_subset _ _)
      have hci := card_le_card hsub
      exact high_F_containment h hn hL hT (by omega)
    have hLK : L ≠ K := by
      intro he
      have hsub : T.erase a ⊆ K ∩ T := subset_inter (he ▸ hEL) (erase_subset _ _)
      have hc := card_le_card hsub
      omega
    have hLKdis := high_disjoint h hn hp hL hK hLK
    have haL : a ∉ L := fun hh => disjoint_left.mp hLKdis hh haK
    have heq : L = T.erase a := by
      apply Subset.antisymm _ hEL
      intro r hr
      exact mem_erase.mpr ⟨fun he => haL (he ▸ hr), hLT hr⟩
    have hTL := mem_containingFamily.mpr ⟨hT, hLT⟩
    have hdef := ((loss_two_shape h hn hp hL (high_loss_two h hn hp hL)).2.1 T hTL).2.2.2
    have hsingle : T \ L = {a} := by
      rw [heq]
      ext r
      simp only [mem_sdiff, mem_erase, mem_singleton]
      constructor
      · intro hr
        by_contra hne
        exact hr.2 ⟨hne, hr.1⟩
      · intro he
        subst r
        exact ⟨haT, by simp⟩
    rw [hsingle] at hdef
    simp only [df, sum_singleton] at hdef
    have hmin := h.minA a (hTA haT)
    omega

omit [DecidableEq V] in
theorem c02_deficient_vertex {A C : Finset V} (h : C02Input G A C) :
    ∃ a ∈ A, dg G C a ≤ 5 := by
  classical
  by_contra hnone
  push Not at hnone
  have hdf : df G C A = 0 := by
    apply sum_eq_zero
    intro a ha
    have hca := h.capA a ha
    have hhi := hnone a ha
    omega
  have ht := c02_total_deficit h
  omega

/-- An actual high core is incompatible with the actual pair cover. -/
theorem high_branch_contradiction {A C K : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) (hK : K ∈ maxHighFamily G A C) : False := by
  classical
  obtain ⟨a, haA, ha5⟩ := c02_deficient_vertex h
  have haAll : ∀ L ∈ maxHighFamily G A C, a ∉ L := by
    intro L hL haL
    have hd := (loss_two_shape h hn hp hL (high_loss_two h hn hp hL)).2.2 a haL
    omega
  have haK := haAll K hK
  obtain ⟨T1, hT1, hKT1, ha1⟩ := high_cover h hn hp hK (mem_sdiff.mpr ⟨haA, haK⟩)
  have hT1F := mem_containingFamily.mpr ⟨hT1, hKT1⟩
  have hcard := (loss_two_shape h hn hp hK (high_loss_two h hn hp hK)).1
  have hcErase : #((containingFamily G A C K).erase T1) = 1 := by
    have hh := card_erase_add_one hT1F
    omega
  obtain ⟨T2, hErase⟩ := card_eq_one.mp hcErase
  have hT2E : T2 ∈ (containingFamily G A C K).erase T1 := by rw [hErase]; simp
  obtain ⟨hne21, hT2F⟩ := mem_erase.mp hT2E
  obtain ⟨hT2, hKT2⟩ := mem_containingFamily.mp hT2F
  have hfamily : containingFamily G A C K = {T1, T2} := by
    ext T
    constructor
    · intro hTF
      by_cases he : T = T1
      · simp [he]
      · have hh : T ∈ (containingFamily G A C K).erase T1 := mem_erase.mpr ⟨he, hTF⟩
        rw [hErase] at hh
        simp only [mem_singleton] at hh
        simp [hh]
    · intro hTF
      simp only [mem_insert, mem_singleton] at hTF
      rcases hTF with rfl | rfl
      · exact hT1F
      · exact hT2F
  have hI12 := (containing_intersection h hn hp hK hT1F hT2F hne21.symm).1
  have hcover : T1 ∪ T2 = A := by
    apply Subset.antisymm (union_subset (maxPositive_data h hT1).1 (maxPositive_data h hT2).1)
    intro r hr
    by_cases hrK : r ∈ K
    · exact mem_union_left _ (hKT1 hrK)
    · have hrR : r ∈ A \ K := mem_sdiff.mpr ⟨hr, hrK⟩
      rw [← containing_cover h hn hp hK, hfamily] at hrR
      obtain ⟨T, hTF, hrT⟩ := mem_biUnion.mp hrR
      simp only [mem_insert, mem_singleton] at hTF
      rcases hTF with rfl | rfl
      · exact mem_union_left _ (mem_sdiff.mp hrT).1
      · exact mem_union_right _ (mem_sdiff.mp hrT).1
  have ha2 : a ∉ T2 := by
    intro hh
    have hi : a ∈ T1 ∩ T2 := mem_inter.mpr ⟨ha1, hh⟩
    rw [hI12] at hi
    exact haK hi
  have hP2ne : (T2 \ K).Nonempty := by
    by_contra hnP
    have he : T2 \ K = ∅ := not_nonempty_iff_eq_empty.mp hnP
    have hs : T2 ⊆ K := sdiff_eq_empty_iff_subset.mp he
    have heq : T2 = K := Subset.antisymm hs hKT2
    exact (containing_theta_one h hn hp hK hT2F).2 heq
  obtain ⟨b, hbP⟩ := hP2ne
  obtain ⟨hb2, hbK⟩ := mem_sdiff.mp hbP
  have hb1 : b ∉ T1 := by
    intro hh
    have hi : b ∈ T1 ∩ T2 := mem_inter.mpr ⟨hh, hb2⟩
    rw [hI12] at hi
    exact hbK hi
  have hab : a ≠ b := fun he => hb1 (he ▸ ha1)
  obtain ⟨T3, hT3, ha3, hb3⟩ := hp a haA b ((maxPositive_data h hT2).1 hb2) hab
  have hne31 : T3 ≠ T1 := fun he => hb1 (he ▸ hb3)
  have hne32 : T3 ≠ T2 := fun he => ha2 (he ▸ ha3)
  have hK3 : ¬ K ⊆ T3 := by
    intro hKT3
    have hT3F := mem_containingFamily.mpr ⟨hT3, hKT3⟩
    rw [hfamily] at hT3F
    simp only [mem_insert, mem_singleton] at hT3F
    exact hT3F.elim hne31 hne32
  have hdisK3 := (high_module h hn hp hK hT3).resolve_left hK3
  have hI13le : #(T3 ∩ T1) ≤ 1 := by
    by_contra hh
    have hL := (nonlinear_F_intersection h hn hT3 hT1 hne31 (by omega)).2.2.2.2
    exact haAll (T3 ∩ T1) hL (mem_inter.mpr ⟨ha3, ha1⟩)
  have hI13 : T3 ∩ T1 = {a} := by
    have haI : a ∈ T3 ∩ T1 := mem_inter.mpr ⟨ha3, ha1⟩
    have hsub : ({a} : Finset V) ⊆ T3 ∩ T1 := singleton_subset_iff.mpr haI
    apply (eq_of_subset_of_card_le hsub (by simpa using hI13le)).symm
  have hI23 : 2 ≤ #(T3 ∩ T2) := by
    have hT3sub : T3 ⊆ (T3 ∩ T1) ∪ (T3 ∩ T2) := by
      intro r hr
      have hrA := (maxPositive_data h hT3).1 hr
      rw [← hcover] at hrA
      rcases mem_union.mp hrA with hr1 | hr2
      · exact mem_union_left _ (mem_inter.mpr ⟨hr, hr1⟩)
      · exact mem_union_right _ (mem_inter.mpr ⟨hr, hr2⟩)
    have hcsub := card_le_card hT3sub
    have hcu := card_union_le (T3 ∩ T1) (T3 ∩ T2)
    rw [hI13] at hcsub
    rw [hI13, card_singleton] at hcu
    have h3T3 := (maxPositive_data h hT3).2.1
    omega
  have hL := (nonlinear_F_intersection h hn hT3 hT2 hne32 hI23).2.2.2.2
  have hL3 : T3 ∩ T2 ⊆ T3 := inter_subset_left
  have hLTF := mem_containingFamily.mpr ⟨hT3, hL3⟩
  have hdef := ((loss_two_shape h hn hp hL (high_loss_two h hn hp hL)).2.1 T3 hLTF).2.2.2
  have hsingle : T3 \ (T3 ∩ T2) = {a} := by
    ext r
    constructor
    · intro hr
      obtain ⟨hr3, hrnot⟩ := mem_sdiff.mp hr
      have hrA := (maxPositive_data h hT3).1 hr3
      rw [← hcover] at hrA
      rcases mem_union.mp hrA with hr1 | hr2
      · have hi : r ∈ T3 ∩ T1 := mem_inter.mpr ⟨hr3, hr1⟩
        rw [hI13] at hi
        exact hi
      · exact False.elim (hrnot (mem_inter.mpr ⟨hr3, hr2⟩))
    · intro hr
      have he : r = a := mem_singleton.mp hr
      subst r
      exact mem_sdiff.mpr ⟨ha3, fun hh => ha2 (mem_inter.mp hh).2⟩
  rw [hsingle] at hdef
  simp only [df, sum_singleton] at hdef
  have hmin := h.minA a haA
  omega

variable (G) in
def columnNeighbors (A : Finset V) (c : V) : Finset V := A.filter (G.Adj c)

variable (G) in
def columnContributors (A C : Finset V) (c : V) : Finset (Finset V) :=
  (maxPositiveFamily G A C).filter fun T => 3 ≤ dg G T c

variable (G) in
def columnTraces (A C : Finset V) (c : V) : Finset (Finset V) :=
  (columnContributors G A C c).image fun T => T ∩ columnNeighbors G A c

theorem column_trace_degree {A C T : Finset V} (h : C02Input G A C)
    (hT : T ∈ maxPositiveFamily G A C) (c : V) :
    #(T ∩ columnNeighbors G A c) = dg G T c := by
  have hTA := (maxPositive_data h hT).1
  have he : T ∩ columnNeighbors G A c = T.filter (G.Adj c) := by
    ext a
    simp only [mem_inter, columnNeighbors, mem_filter]
    exact ⟨fun ha => ⟨ha.1, ha.2.2⟩, fun ha => ⟨ha.1, hTA ha.1, ha.2⟩⟩
  rw [he]
  rfl

/-- The exact column family is derived from the actual global maxima. -/
theorem column_trace_data {A C : Finset V} (h : C02Input G A C) {c : V} (hc : c ∈ C)
    (hlin : ∀ T ∈ maxPositiveFamily G A C, ∀ U ∈ maxPositiveFamily G A C,
      T ≠ U → #(T ∩ U) ≤ 1) :
    #(columnNeighbors G A c) = 6 ∧
      (∀ S ∈ columnTraces G A C c, S ⊆ columnNeighbors G A c ∧ 3 ≤ #S) ∧
      (∀ S ∈ columnTraces G A C c, ∀ R ∈ columnTraces G A C c,
        S ≠ R → #(S ∩ R) ≤ 1) ∧
      (∑ T ∈ maxPositiveFamily G A C, max 0 ((dg G T c : ℤ) - 2)) =
        ∑ S ∈ columnTraces G A C c, ((#S : ℤ) - 2) := by
  classical
  have hn6 : #(columnNeighbors G A c) = 6 := h.satC c hc
  have hblocks : ∀ S ∈ columnTraces G A C c, S ⊆ columnNeighbors G A c ∧ 3 ≤ #S := by
    intro S hS
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hS
    obtain ⟨hTF, hd⟩ := mem_filter.mp hT
    exact ⟨inter_subset_right, by rw [column_trace_degree h hTF]; exact hd⟩
  have hlinear : ∀ S ∈ columnTraces G A C c, ∀ R ∈ columnTraces G A C c,
      S ≠ R → #(S ∩ R) ≤ 1 := by
    intro S hS R hR hne
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hS
    obtain ⟨U, hU, rfl⟩ := mem_image.mp hR
    have hTU : T ≠ U := fun he => hne (congrArg (fun X => X ∩ columnNeighbors G A c) he)
    have hsub : (T ∩ columnNeighbors G A c) ∩ (U ∩ columnNeighbors G A c) ⊆ T ∩ U :=
      fun a ha => mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp ha).1).1,
        (mem_inter.mp (mem_inter.mp ha).2).1⟩
    exact (card_le_card hsub).trans (hlin T (mem_filter.mp hT).1 U (mem_filter.mp hU).1 hTU)
  have hinj : ∀ T ∈ columnContributors G A C c, ∀ U ∈ columnContributors G A C c,
      T ∩ columnNeighbors G A c = U ∩ columnNeighbors G A c → T = U := by
    intro T hT U hU he
    obtain ⟨hTF, hd⟩ := mem_filter.mp hT
    have hUF := (mem_filter.mp hU).1
    by_contra hne
    have hsub : T ∩ columnNeighbors G A c ⊆ T ∩ U := by
      intro a ha
      have haU : a ∈ U ∩ columnNeighbors G A c := he ▸ ha
      exact mem_inter.mpr ⟨(mem_inter.mp ha).1, (mem_inter.mp haU).1⟩
    have hcard := card_le_card hsub
    rw [column_trace_degree h hTF] at hcard
    have hlo := hlin T hTF U hUF hne
    omega
  have hsum : (∑ T ∈ maxPositiveFamily G A C, max 0 ((dg G T c : ℤ) - 2)) =
      ∑ T ∈ columnContributors G A C c,
        ((#(T ∩ columnNeighbors G A c) : ℤ) - 2) := by
    calc
      _ = ∑ T ∈ columnContributors G A C c, max 0 ((dg G T c : ℤ) - 2) := by
        symm
        apply sum_subset (filter_subset _ _)
        intro T hT hnot
        have hd : dg G T c ≤ 2 := by
          by_contra hh
          exact hnot (mem_filter.mpr ⟨hT, by omega⟩)
        omega
      _ = _ := sum_congr rfl fun T hT => by
        obtain ⟨hTF, hd⟩ := mem_filter.mp hT
        rw [column_trace_degree h hTF]
        omega
  have himg : (∑ S ∈ columnTraces G A C c, ((#S : ℤ) - 2)) =
      ∑ T ∈ columnContributors G A C c,
        ((#(T ∩ columnNeighbors G A c) : ℤ) - 2) := sum_image hinj
  exact ⟨hn6, hblocks, hlinear, hsum.trans himg.symm⟩

theorem low_F_linear {A C : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C)
    (hlow : ∀ Z ⊆ A, 3 ≤ #Z → thetaC02 G C Z ≤ 1) :
    ∀ T ∈ maxPositiveFamily G A C, ∀ U ∈ maxPositiveFamily G A C,
      T ≠ U → #(T ∩ U) ≤ 1 := by
  intro T hT U hU hne
  by_contra hh
  have hhigh := (nonlinear_F_intersection h hn hT hU hne (by omega)).2.2.2.2
  obtain ⟨hIA, h3I, htI, _, _⟩ := maxHigh_data h hn hhigh
  have ht := hlow (T ∩ U) hIA h3I
  omega

theorem low_F_card {A C : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C)
    (hlow : ∀ Z ⊆ A, 3 ≤ #Z → thetaC02 G C Z ≤ 1) :
    #A ≤ #(maxPositiveFamily G A C) := by
  have hA : 3 ≤ #A := by have hc := c02_cardC h; have hh := h.card; omega
  apply Erdos585.QB6C02LinearCover.fisher_linear_pair_cover A (maxPositiveFamily G A C) hA
  · intro T hT
    obtain ⟨hTA, h3T, htT, _⟩ := maxPositive_data h hT
    refine ⟨hTA, by omega, ?_⟩
    intro he
    rw [he, theta_whole h] at htT
    omega
  · exact hp
  · exact low_F_linear h hn hlow

theorem positive_charge_five {A C T : Finset V} (h : C02Input G A C)
    (hT : T ∈ maxPositiveFamily G A C) :
    5 ≤ ∑ c ∈ C, max 0 ((dg G T c : ℤ) - 2) := by
  obtain ⟨_, h3, ht, _⟩ := maxPositive_data h hT
  unfold thetaC02 at ht
  omega

/-- This is the explicit aggregate step; its column bound is supplied by actual traces. -/
theorem low_aggregate_contradiction {A C : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C)
    (hlow : ∀ Z ⊆ A, 3 ≤ #Z → thetaC02 G C Z ≤ 1)
    (hcolumn : ∀ c ∈ C,
      (∑ T ∈ maxPositiveFamily G A C, max 0 ((dg G T c : ℤ) - 2)) ≤ 4) : False := by
  have hF := low_F_card h hn hp hlow
  have hrow : 5 * (#(maxPositiveFamily G A C) : ℤ) ≤
      ∑ T ∈ maxPositiveFamily G A C, ∑ c ∈ C, max 0 ((dg G T c : ℤ) - 2) := by
    calc
      _ = ∑ _T ∈ maxPositiveFamily G A C, (5 : ℤ) := by
        rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := sum_le_sum fun T hT => positive_charge_five h hT
  have hcol : (∑ T ∈ maxPositiveFamily G A C, ∑ c ∈ C,
      max 0 ((dg G T c : ℤ) - 2)) ≤ 4 * (#C : ℤ) := by
    rw [sum_comm]
    calc
      _ ≤ ∑ _c ∈ C, (4 : ℤ) := sum_le_sum hcolumn
      _ = _ := by rw [sum_const, nsmul_eq_mul]; ring
  have hc := h.card
  omega

/-- The physical column bound comes from the proved actual trace family. -/
theorem actual_column_budget {A C : Finset V} (h : C02Input G A C) {c : V} (hc : c ∈ C)
    (hlin : ∀ T ∈ maxPositiveFamily G A C, ∀ U ∈ maxPositiveFamily G A C,
      T ≠ U → #(T ∩ U) ≤ 1) :
    (∑ T ∈ maxPositiveFamily G A C, max 0 ((dg G T c : ℤ) - 2)) ≤ 4 := by
  obtain ⟨hN, hblocks, hlinear, hcharge⟩ := column_trace_data h hc hlin
  rw [hcharge]
  exact Erdos585.QB6C02SixNeighbor.six_neighbor_int
    (columnNeighbors G A c) (columnTraces G A C c) hN
    (fun S hS => (hblocks S hS).1) (fun S hS => (hblocks S hS).2) hlinear

theorem low_branch_contradiction {A C : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C)
    (hlow : ∀ Z ⊆ A, 3 ≤ #Z → thetaC02 G C Z ≤ 1) : False :=
  low_aggregate_contradiction h hn hp hlow
    fun _c hc => actual_column_budget h hc (low_F_linear h hn hlow)

/-- Both actual high and low families are produced from the physical graph. -/
theorem no_theta3_apf_impossible {A C : Finset V} (h : C02Input G A C)
    (hn : NoTheta3 G A C) (hp : APF G A C) : False := by
  classical
  by_cases hH : (maxHighFamily G A C).Nonempty
  · obtain ⟨K, hK⟩ := hH
    exact high_branch_contradiction h hn hp hK
  · have hlow : ∀ Z ⊆ A, 3 ≤ #Z → thetaC02 G C Z ≤ 1 := by
      intro Z hZ h3
      by_contra hh
      obtain ⟨K, hK, _⟩ := high_extension (G := G) (C := C) hZ h3 (by omega)
      exact hH ⟨K, hK⟩
    exact low_branch_contradiction h hn hp hlow

/-- Literal arbitrary-Type C02+NoTheta3 omission-pair producer; APF is derived inside. -/
theorem no_theta3_good_pair : NoTheta3GoodPair.{u} := by
  intro V inst G instAdj A C h hn
  classical
  by_contra hnone
  have hp : APF G A C := apf_of_no_good_pair h fun D _ _ hgood => hnone ⟨D, hgood⟩
  exact no_theta3_apf_impossible h hn hp

/-- Literal original-edge nonempty Quartic consequence at every finite order. -/
theorem no_theta3_repair : NoTheta3Repair.{u} := by
  intro V inst G instAdj A C h hn
  obtain ⟨D, hD⟩ := no_theta3_good_pair G A C h hn
  exact goodPair_quartic h hD

#print axioms pair_cut_of_theta
#print axioms goodPair_of_theta
#print axioms goodPair_quartic
#print axioms apf_of_no_good_pair
#print axioms apf_of_no_quartic
#print axioms maxHigh_data
#print axioms high_F_containment
#print axioms nonlinear_F_intersection
#print axioms theta_corePlus
#print axioms highPlus_geometry
#print axioms highPlus_boundary
#print axioms highPlus_individual_loss
#print axioms partial_absorbed_loss
#print axioms high_cover
#print axioms containing_intersection
#print axioms containing_cover
#print axioms petalJ_owner
#print axioms petalJ_saturated
#print axioms petalJ_disjoint
#print axioms petal_exact
#print axioms petal_d_bounds
#print axioms outside_row_degree
#print axioms containing_edge_sum
#print axioms containing_alpha_budget
#print axioms no_theta3_good_pair
#print axioms no_theta3_repair
#print NoTheta3
#print GoodPair
#print APF
#print NoTheta3GoodPair
#print NoTheta3Repair
end Erdos585.QB6C02NoTheta3

import Openmath.Proofs.PaperSupport.QB6C02PartialFactorLean

/- 


-/
open Finset
open Erdos585.QB4 Erdos585.QB5 Erdos585.QB6Assembly Erdos585.QB6C02PartialFactor
namespace Erdos585.QB6C02NonlinearCore
universe u
variable {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
set_option maxHeartbeats 1800000

/-- The actual positive theta subsets of the finite physical shore. -/
def positiveSets (A C : Finset V) : Finset (Finset V) := by
  classical
  exact A.powerset.filter fun T => 2 ≤ #T ∧ 0 < thetaC02 G C T

/-- Inclusion-maximal members of an actual finite family. -/
def maximalMembers (H : Finset (Finset V)) : Finset (Finset V) := by
  classical
  exact H.filter fun T => ∀ U ∈ H, T ⊆ U → U = T

/-- No producer or desired nesting is part of this definition. -/
def maxPositiveFamily (A C : Finset V) : Finset (Finset V) :=
  maximalMembers (positiveSets G A C)

/-- The actual theta-three subsets. -/
def thetaThreeSets (A C : Finset V) : Finset (Finset V) := by
  classical
  exact A.powerset.filter fun T => thetaC02 G C T = 3

def maxThetaThreeFamily (A C : Finset V) : Finset (Finset V) :=
  maximalMembers (thetaThreeSets G A C)

variable {G}

omit [DecidableEq V] in
lemma mem_positiveSets {A C T : Finset V} :
    T ∈ positiveSets G A C ↔ T ⊆ A ∧ 2 ≤ #T ∧ 0 < thetaC02 G C T := by
  classical
  simp [positiveSets]

lemma mem_maximalMembers {H : Finset (Finset V)} {T : Finset V} :
    T ∈ maximalMembers H ↔ T ∈ H ∧ ∀ U ∈ H, T ⊆ U → U = T := by
  classical
  simp [maximalMembers]

omit [DecidableEq V] in
lemma mem_thetaThreeSets {A C T : Finset V} :
    T ∈ thetaThreeSets G A C ↔ T ⊆ A ∧ thetaC02 G C T = 3 := by
  classical
  simp [thetaThreeSets]

omit [DecidableEq V] in
/-- Small-cardinality and full-shore cases are excluded by literal theta values. -/
theorem theta3_large_proper {A C K : Finset V} (h : C02Input G A C)
    (_hK : K ⊆ A) (ht : thetaC02 G C K = 3) : 3 ≤ #K ∧ K ≠ A := by
  constructor
  · by_contra hn
    have hs := theta_small (G := G) C (Z := K) (by omega)
    omega
  · intro he
    have hw := theta_whole h
    rw [he] at ht
    omega

omit [DecidableEq V] in
/-- Actual canonical theta-three geometry, before any family/nesting conclusion. -/
theorem theta3_geometry {A C K : Finset V} (h : C02Input G A C)
    (hK : K ⊆ A) (ht : thetaC02 G C K = 3) :
    3 ≤ #K ∧ K ≠ A ∧ #(cpr G C K) = #K + 2 ∧
    (ec G K (cpr G C K) : ℤ) = 6 * (#K : ℤ) - 1 ∧
    gv G K (cpr G C K) = 14 ∧
    ∀ a ∈ K, 5 ≤ dg G (cpr G C K) a := by
  obtain ⟨hl, hp⟩ := theta3_large_proper h hK ht
  obtain ⟨hb1, hb2⟩ := theta_proper_bounds h hK hp hl
  have hc := theta_canonical (G := G) C K
  have hy : #(cpr G C K) = #K + 2 := by omega
  have hyz : (#(cpr G C K) : ℤ) = #K + 2 := by exact_mod_cast hy
  have he : (ec G K (cpr G C K) : ℤ) = 6 * (#K : ℤ) - 1 := by omega
  have hg : gv G K (cpr G C K) = 14 := by unfold gv; omega
  have hcap : ∀ a ∈ K, dg G (cpr G C K) a ≤ 6 := by
    intro a ha
    exact (dg_mono (cpr_subset (G := G) C K) a).trans (h.capA a (hK ha))
  have hd : df G (cpr G C K) K = 1 := by rw [df_eq, he]; ring
  have hr : ∀ a ∈ K, 5 ≤ dg G (cpr G C K) a := by
    intro a ha
    have hs : 6 - (dg G (cpr G C K) a : ℤ) ≤ df G (cpr G C K) K :=
      single_le_sum (f := fun b => (6 : ℤ) - (dg G (cpr G C K) b : ℤ))
        (fun b hb => by have := hcap b hb; omega) ha
    rw [hd] at hs
    omega
  exact ⟨hl, hp, hy, he, hg, hr⟩

/-- Finite maximality is produced from the actual family, never supplied. -/
theorem exists_maximal_extension {H : Finset (Finset V)} {T : Finset V}
    (hT : T ∈ H) : ∃ U ∈ maximalMembers H, T ⊆ U := by
  classical
  let S := H.filter fun U => T ⊆ U
  have hs : S.Nonempty := ⟨T, mem_filter.mpr ⟨hT, subset_rfl⟩⟩
  obtain ⟨U, hU, hm⟩ := exists_max_image S Finset.card hs
  obtain ⟨hu, ht⟩ := mem_filter.mp hU
  refine ⟨U, mem_maximalMembers.mpr ⟨hu, ?_⟩, ht⟩
  intro W hw huw
  have hc := hm W (mem_filter.mpr ⟨hw, ht.trans huw⟩)
  exact (eq_of_subset_of_card_le huw hc).symm

theorem positive_extension {A C T : Finset V} (hT : T ⊆ A)
    (h2 : 2 ≤ #T) (hp : 0 < thetaC02 G C T) :
    ∃ U ∈ maxPositiveFamily G A C, T ⊆ U :=
  exists_maximal_extension (mem_positiveSets.mpr ⟨hT, h2, hp⟩)

/-- The literal actual column gap. -/
def columnGap (K T : Finset V) (c : V) : ℤ :=
  max 0 ((dg G (K ∪ T) c : ℤ) - 2) +
  max 0 ((dg G (K ∩ T) c : ℤ) - 2) -
  max 0 ((dg G K c : ℤ) - 2) - max 0 ((dg G T c : ℤ) - 2)

lemma columnGap_nonneg (K T : Finset V) (c : V) :
    0 ≤ columnGap (G := G) K T c := by
  have hd := dg_union_add_dg_inter (G := G) K T c
  have h1 := dg_mono (G := G) (inter_subset_left (s₁ := K) (s₂ := T)) c
  have h2 := dg_mono (G := G) (inter_subset_right (s₁ := K) (s₂ := T)) c
  unfold columnGap
  omega

/-- Exact modular card cancellation leaves exactly the actual column gaps. -/
theorem theta_gap_sum (C K T : Finset V) :
    thetaC02 G C (K ∪ T) + thetaC02 G C (K ∩ T) -
      thetaC02 G C K - thetaC02 G C T =
    ∑ c ∈ C, columnGap (G := G) K T c := by
  have hc : (#(K ∪ T) : ℤ) + #(K ∩ T) = #K + #T := by
    exact_mod_cast card_union_add_card_inter K T
  simp only [thetaC02, columnGap, sum_sub_distrib, sum_add_distrib]
  linarith

theorem theta_supermodular (C K T : Finset V) :
    thetaC02 G C K + thetaC02 G C T ≤
      thetaC02 G C (K ∪ T) + thetaC02 G C (K ∩ T) := by
  have hs := theta_gap_sum (G := G) C K T
  have hn : 0 ≤ ∑ c ∈ C, columnGap (G := G) K T c :=
    sum_nonneg fun c _ => columnGap_nonneg (G := G) K T c
  linarith

/-- When the intersection is one row, a zero gap forces no other T-neighbor. -/
lemma singleton_gap_zero {K T : Finset V} {a c : V}
    (hi : K ∩ T = {a}) (hx : 3 ≤ dg G K c)
    (hg : columnGap (G := G) K T c = 0) :
    dg G T c = dg G {a} c := by
  have hd := dg_union_add_dg_inter (G := G) K T c
  have hz := dg_le_card (G := G) ({a} : Finset V) c
  have hm := dg_mono (G := G) (inter_subset_right (s₁ := K) (s₂ := T)) c
  unfold columnGap at hg
  rw [hi] at hd hm hg
  simp only [card_singleton] at hz
  omega

lemma singleton_gap_one {K T : Finset V} {a c : V}
    (hi : K ∩ T = {a}) (hx : 3 ≤ dg G K c) (hy : 3 ≤ dg G T c)
    (hadj : G.Adj a c) : columnGap (G := G) K T c = 1 := by
  have hd := dg_union_add_dg_inter (G := G) K T c
  have hz : dg G ({a} : Finset V) c = 1 := by simp only [dg, filter_singleton, if_pos (G.adj_symm hadj), card_singleton]
  unfold columnGap
  rw [hi, hz] at hd ⊢
  omega

/-- Erasing a nonneighbor preserves the actual column degree. -/
lemma dg_erase_of_not_adj {T : Finset V} {a c : V} (hn : ¬ G.Adj c a) :
    dg G (T.erase a) c = dg G T c := by
  unfold dg
  rw [filter_erase, erase_eq_of_notMem]
  simp [hn]

/-- Exact canonical deletion identity, including the degree-three boundary. -/
theorem theta_erase {C T : Finset V} {a : V} (ha : a ∈ T) :
    thetaC02 G C (T.erase a) = thetaC02 G C T + 4 - dg G (cpr G C T) a := by
  have hp : ∀ c ∈ C,
      max 0 ((dg G (T.erase a) c : ℤ) - 2) =
      max 0 ((dg G T c : ℤ) - 2) -
        (if G.Adj a c ∧ 3 ≤ dg G T c then (1 : ℤ) else 0) := by
    intro c _
    by_cases hn : G.Adj a c
    · have hd := dg_erase_add (G := G) ha c (G.adj_symm hn)
      by_cases hh : 3 ≤ dg G T c
      · simp only [hn, hh, and_self, if_true]
        omega
      · simp only [hn, hh, and_false, if_false]
        omega
    · have hd := dg_erase_of_not_adj (G := G) (T := T) (a := a) (c := c)
        (fun hc => hn (G.adj_symm hc))
      rw [hd]
      simp [hn]
  have hd : (dg G (cpr G C T) a : ℤ) =
      ∑ c ∈ C, if G.Adj a c ∧ 3 ≤ dg G T c then (1 : ℤ) else 0 := by
    change ((#((C.filter fun c => 3 ≤ dg G T c).filter fun c => G.Adj a c) : ℕ) : ℤ) = _
    rw [filter_filter, card_filter, Nat.cast_sum]
    refine sum_congr rfl fun c _ => ?_
    by_cases h1 : G.Adj a c <;> by_cases h2 : 3 ≤ dg G T c <;> simp [h1, h2]
  have hc : (#(T.erase a) : ℤ) + 1 = #T := by
    exact_mod_cast card_erase_add_one ha
  have hs := sum_congr rfl hp
  rw [sum_sub_distrib, ← hd] at hs
  unfold thetaC02
  rw [hs]
  linarith

/-- The actual maximal-positive family has no members of order two. -/
lemma maxPositive_data {A C T : Finset V} (_h : C02Input G A C)
    (hT : T ∈ maxPositiveFamily G A C) :
    T ⊆ A ∧ 3 ≤ #T ∧ 0 < thetaC02 G C T ∧
    ∀ U, U ⊆ A → T ⊆ U → U ≠ T → thetaC02 G C U ≤ 0 := by
  classical
  obtain ⟨hp, hm⟩ := mem_maximalMembers.mp hT
  obtain ⟨ht, h2, hpos⟩ := mem_positiveSets.mp hp
  have h3 : 3 ≤ #T := by
    by_contra hn
    have hs := theta_small (G := G) C (Z := T) (by omega)
    omega
  refine ⟨ht, h3, hpos, ?_⟩
  intro U hu htu hne
  by_contra hn
  have h2u : 2 ≤ #U := by have hc := card_le_card htu; omega
  exact hne (hm U (mem_positiveSets.mpr ⟨hu, h2u, by omega⟩) htu)

/-- Literal N1: arbitrary theta-three sets nest in any maximal-positive set they meet. -/
theorem n1_nesting {A C K T : Finset V} (h : C02Input G A C)
    (hK : K ⊆ A) (htK : thetaC02 G C K = 3)
    (hT : T ∈ maxPositiveFamily G A C) : Disjoint K T ∨ K ⊆ T := by
  classical
  by_cases hdis : Disjoint K T
  · exact Or.inl hdis
  by_cases hsub : K ⊆ T
  · exact Or.inr hsub
  obtain ⟨hta, ht3, htpos, hmax⟩ := maxPositive_data h hT
  have hwa : K ∪ T ⊆ A := union_subset hK hta
  have hwt : K ∪ T ≠ T := by
    intro he
    exact hsub (he ▸ subset_union_left)
  have hwt0 := hmax (K ∪ T) hwa subset_union_right hwt
  have hi : (K ∩ T).Nonempty := not_disjoint_iff_nonempty_inter.mp hdis
  have hia : K ∩ T ⊆ A := inter_subset_left.trans hK
  have hsup := theta_supermodular (G := G) C K T
  have hit4 : 4 ≤ thetaC02 G C (K ∩ T) := by omega
  have hic : #(K ∩ T) = 1 := by
    have hpos := card_pos.mpr hi
    by_cases h3 : 3 ≤ #(K ∩ T)
    · have hb := theta_three h hia h3
      omega
    · have hs := theta_small (G := G) C (Z := K ∩ T) (by omega)
      omega
  obtain ⟨a, hia1⟩ := card_eq_one.mp hic
  have hai : a ∈ K ∩ T := by rw [hia1]; simp
  obtain ⟨hak, hat⟩ := mem_inter.mp hai
  have htI : thetaC02 G C (K ∩ T) = 4 := by
    rw [theta_small (G := G) C (by omega)]
    omega
  have htT : thetaC02 G C T = 1 := by omega
  have htW : thetaC02 G C (K ∪ T) = 0 := by omega
  have hgs := theta_gap_sum (G := G) C K T
  have hgs0 : (∑ c ∈ C, columnGap (G := G) K T c) = 0 := by omega
  have hg0 : ∀ c ∈ C, columnGap (G := G) K T c = 0 :=
    (sum_eq_zero_iff_of_nonneg (fun c _ => columnGap_nonneg (G := G) K T c)).mp hgs0
  have hyinter : dg G (cpr G C K ∩ cpr G C T) a = 0 := by
    unfold dg
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro c hc
    obtain ⟨hci, _hadj⟩ := mem_filter.mp hc
    obtain ⟨hck, hct⟩ := mem_inter.mp hci
    obtain ⟨hcc, hx⟩ := mem_cpr.mp hck
    have hy := (mem_cpr.mp hct).2
    have hs := singleton_gap_zero hia1 hx (hg0 c hcc)
    have hz := dg_le_card (G := G) ({a} : Finset V) c
    simp only [card_singleton] at hz
    omega
  have hdu := dg_union_add_dg_inter (G := G) (cpr G C K) (cpr G C T) a
  have hduc : dg G (cpr G C K ∪ cpr G C T) a ≤ 6 :=
    (dg_mono (union_subset (cpr_subset (G := G) C K) (cpr_subset (G := G) C T)) a).trans
      (h.capA a (hK hak))
  have hrow := (theta3_geometry h hK htK).2.2.2.2.2 a hak
  have hyt : dg G (cpr G C T) a ≤ 1 := by omega
  have he := theta_erase (G := G) (C := C) hat
  have he4 : 4 ≤ thetaC02 G C (T.erase a) := by omega
  have htea : T.erase a ⊆ A := erase_subset a T |>.trans hta
  have hec := card_erase_add_one hat
  by_cases he3 : 3 ≤ #(T.erase a)
  · have hb := theta_three h htea he3
    omega
  · have hs := theta_small (G := G) C (Z := T.erase a) (by omega)
    omega

/-- Actual singleton-intersection geometry forces at least four unit column gaps. -/
lemma singleton_gap_sum_four {A C K L : Finset V} (h : C02Input G A C)
    (hK : K ⊆ A) (hL : L ⊆ A) (htK : thetaC02 G C K = 3)
    (htL : thetaC02 G C L = 3) {a : V} (hi : K ∩ L = {a}) :
    4 ≤ ∑ c ∈ C, columnGap (G := G) K L c := by
  classical
  have hai : a ∈ K ∩ L := by rw [hi]; simp
  obtain ⟨hak, hal⟩ := mem_inter.mp hai
  have hk5 := (theta3_geometry h hK htK).2.2.2.2.2 a hak
  have hl5 := (theta3_geometry h hL htL).2.2.2.2.2 a hal
  have hd := dg_union_add_dg_inter (G := G) (cpr G C K) (cpr G C L) a
  have hcap : dg G (cpr G C K ∪ cpr G C L) a ≤ 6 :=
    (dg_mono (union_subset (cpr_subset (G := G) C K) (cpr_subset (G := G) C L)) a).trans
      (h.capA a (hK hak))
  let S := (cpr G C K ∩ cpr G C L).filter fun c => G.Adj a c
  have hsc : S ⊆ C := by
    intro c hc
    exact (mem_cpr.mp (mem_inter.mp (mem_filter.mp hc).1).1).1
  have hs4 : 4 ≤ #S := by
    change 4 ≤ dg G (cpr G C K ∩ cpr G C L) a
    omega
  have hunit : ∀ c ∈ S, columnGap (G := G) K L c = 1 := by
    intro c hc
    obtain ⟨hci, hac⟩ := mem_filter.mp hc
    obtain ⟨hck, hcl⟩ := mem_inter.mp hci
    exact singleton_gap_one hi (mem_cpr.mp hck).2 (mem_cpr.mp hcl).2 hac
  have hs := sum_le_sum_of_subset_of_nonneg hsc
    (fun c _ _ => columnGap_nonneg (G := G) K L c)
  have he : (∑ c ∈ S, columnGap (G := G) K L c) = (#S : ℤ) := by
    rw [sum_congr rfl hunit]
    simp
  rw [he] at hs
  have hs4z : (4 : ℤ) ≤ #S := by exact_mod_cast hs4
  exact hs4z.trans hs

/-- Literal N2: intersecting actual theta-three sets have theta-three union. -/
theorem n2_union {A C K L : Finset V} (h : C02Input G A C)
    (hK : K ⊆ A) (hL : L ⊆ A) (htK : thetaC02 G C K = 3)
    (htL : thetaC02 G C L = 3) (hi : (K ∩ L).Nonempty) :
    thetaC02 G C (K ∪ L) = 3 := by
  classical
  have hk3 := (theta3_large_proper h hK htK).1
  have hwa : K ∪ L ⊆ A := union_subset hK hL
  have hw3 : 3 ≤ #(K ∪ L) := hk3.trans (card_le_card subset_union_left)
  have hwt := theta_three h hwa hw3
  have hia : K ∩ L ⊆ A := inter_subset_left.trans hK
  have hsup := theta_supermodular (G := G) C K L
  by_cases hi3 : 3 ≤ #(K ∩ L)
  · have hit := theta_three h hia hi3
    omega
  · have his := theta_small (G := G) C (Z := K ∩ L) (by omega)
    have hicp := card_pos.mpr hi
    have hic1 : #(K ∩ L) = 1 := by omega
    obtain ⟨a, hia1⟩ := card_eq_one.mp hic1
    have hgf := singleton_gap_sum_four h hK hL htK htL hia1
    have hgs := theta_gap_sum (G := G) C K L
    omega

/-- Distinct actual inclusion-maximal theta-three sets are disjoint on A. -/
theorem maximal_theta3_disjoint {A C K L : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxThetaThreeFamily G A C)
    (hL : L ∈ maxThetaThreeFamily G A C) (hne : K ≠ L) : Disjoint K L := by
  classical
  by_contra hd
  obtain ⟨hks, hkm⟩ := mem_maximalMembers.mp hK
  obtain ⟨hls, hlm⟩ := mem_maximalMembers.mp hL
  obtain ⟨hka, hkt⟩ := mem_thetaThreeSets.mp hks
  obtain ⟨hla, hlt⟩ := mem_thetaThreeSets.mp hls
  have hi := not_disjoint_iff_nonempty_inter.mp hd
  have hu := n2_union h hka hla hkt hlt hi
  have hum : K ∪ L ∈ thetaThreeSets G A C :=
    mem_thetaThreeSets.mpr ⟨union_subset hka hla, hu⟩
  have heK := hkm (K ∪ L) hum subset_union_left
  have heL := hlm (K ∪ L) hum subset_union_right
  exact hne (heK.symm.trans heL)

end Erdos585.QB6C02NonlinearCore

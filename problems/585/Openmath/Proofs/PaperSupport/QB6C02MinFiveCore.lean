import Openmath.Proofs.PaperSupport.QB6C02Five4

/- 


-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
open Finset
open Erdos585.QB4 Erdos585.QB5 Erdos585.QB6Assembly
open Erdos585.QB6C02PartialFactor Erdos585.QB6C02NonlinearCore
open Erdos585.QB6C02NoTheta3 Erdos585.QB6C02Five4
namespace Erdos585.QB6C02MinFive
universe u
variable {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def MinFive (A C : Finset V) : Prop := ∀ a ∈ A, 5 ≤ dg G C a

def Ordinary (A C : Finset V) (p : V) : Prop :=
  ∀ K ∈ maxThetaThreeFamily G A C, p ∉ K

def MinFiveGoodPair : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V), C02Input G A C → MinFive G A C → ∃ D, GoodPair G A C D

def MinFiveRepair : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V), C02Input G A C → MinFive G A C → Quartic G A C

variable {G}

lemma minfive_deficit {A C Z : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hZ : Z ⊆ A) : 0 ≤ df G C Z ∧ df G C Z ≤ (#Z : ℤ) := by
  refine ⟨(c02_deficit_bounds h hZ).1, ?_⟩
  unfold df
  calc
    _ ≤ ∑ _a ∈ Z, (1 : ℤ) := sum_le_sum fun a ha => by
      have hh := hm a (hZ ha)
      omega
    _ = _ := by simp

lemma ordinary_theta_le_two {A C Z : Finset V} (h : C02Input G A C)
    (hZ : Z ⊆ A) (h2 : 2 ≤ #Z) {p : V} (hp : p ∈ Z)
    (ho : Ordinary G A C p) : thetaC02 G C Z ≤ 2 := by
  have hb := theta_order_two_le_three h hZ h2
  by_contra hh
  have ht : thetaC02 G C Z = 3 := by omega
  obtain ⟨K, hK, hZK⟩ := exists_maximal_extension (mem_thetaThreeSets.mpr ⟨hZ, ht⟩)
  exact ho K hK (hZK hp)

def partialPotential2 (B s : ℤ) : ℤ :=
  if s ≤ 0 then (if 14 ≤ B then 7 else if 11 ≤ B then 6 else if 8 ≤ B then 5 else if 7 ≤ B then 3 else if 6 ≤ B then 2 else if 3 ≤ B then 1 else 0) else (if 14 ≤ B then 9 else if 13 ≤ B then 8 else if 10 ≤ B then 7 else if 7 ≤ B then 6 else if 6 ≤ B then 4 else if 5 ≤ B then 2 else if 3 ≤ B then 1 else 0)

lemma partialPotential2_nonneg (B s : ℤ) : 0 ≤ partialPotential2 B s := by
  unfold partialPotential2
  repeat' first | omega | split

lemma partialPotential2_step (B s b a delta d : ℤ)
    (hB0 : 0 ≤ B) (hB : B ≤ 14) (hs0 : 0 ≤ s) (hs : s ≤ 1)
    (hb0 : 0 ≤ b) (hb : b ≤ B) (ha0 : 0 ≤ a) (ha : a ≤ s) (hdpos : 0 < delta)
    (hc : (b = 3 ∧ a = 0 ∧ delta ≤ 1) ∨
      (-1 ≤ d ∧ d ≤ 2 ∧ 6 + d - a ≤ b ∧ delta ≤ 1 + 2 * d + a)) :
    delta + partialPotential2 (B - b) (s - a) ≤ partialPotential2 B s := by
  rcases hc with hsmall | hlarge
  · obtain ⟨hb3, ha0', hdel⟩ := hsmall
    subst b
    subst a
    unfold partialPotential2
    repeat' first | omega | split
  · obtain ⟨hdlo, hdhi, hcost, hdel⟩ := hlarge
    unfold partialPotential2
    repeat' first | omega | split

def partialPotential4 (B s : ℤ) : ℤ :=
  if s ≤ 0 then (if 10 ≤ B then 4 else if 7 ≤ B then 3 else if 6 ≤ B then 2 else if 3 ≤ B then 1 else 0) else (if s ≤ 1 then (if 9 ≤ B then 5 else if 6 ≤ B then 4 else if 5 ≤ B then 2 else if 3 ≤ B then 1 else 0) else (if s ≤ 2 then (if 8 ≤ B then 6 else if 5 ≤ B then 5 else if 4 ≤ B then 3 else if 3 ≤ B then 1 else 0) else (if 10 ≤ B then 8 else if 7 ≤ B then 7 else if 4 ≤ B then 6 else if 3 ≤ B then 4 else if 2 ≤ B then 2 else 0)))

lemma partialPotential4_nonneg (B s : ℤ) : 0 ≤ partialPotential4 B s := by
  unfold partialPotential4
  repeat' first | omega | split

lemma partialPotential4_step (B s b a delta d : ℤ)
    (hB0 : 0 ≤ B) (hB : B ≤ 10) (hs0 : 0 ≤ s) (hs : s ≤ 3)
    (hb0 : 0 ≤ b) (hb : b ≤ B) (ha0 : 0 ≤ a) (ha : a ≤ s) (hdpos : 0 < delta)
    (hc : (b = 3 ∧ a = 0 ∧ delta ≤ 1) ∨
      (-2 ≤ d ∧ d ≤ 1 ∧ 6 + d - a ≤ b ∧ delta ≤ 1 + 2 * d + a)) :
    delta + partialPotential4 (B - b) (s - a) ≤ partialPotential4 B s := by
  rcases hc with hsmall | hlarge
  · obtain ⟨hb3, ha0', hdel⟩ := hsmall
    subst b
    subst a
    unfold partialPotential4
    repeat' first | omega | split
  · obtain ⟨hdlo, hdhi, hcost, hdel⟩ := hlarge
    unfold partialPotential4
    repeat' first | omega | split

lemma partial_family2 {I : Type u} [DecidableEq I] (F : Finset I)
    (b a delta d : I → ℤ) (B s : ℤ)
    (hB0 : 0 ≤ B) (hB : B ≤ 14) (hs0 : 0 ≤ s) (hs : s ≤ 1)
    (hb0 : ∀ i ∈ F, 0 ≤ b i) (ha0 : ∀ i ∈ F, 0 ≤ a i)
    (hd0 : ∀ i ∈ F, 0 ≤ delta i)
    (hcost : ∑ i ∈ F, b i ≤ B) (hscar : ∑ i ∈ F, a i ≤ s)
    (hc : ∀ i ∈ F, (b i = 3 ∧ a i = 0 ∧ delta i ≤ 1) ∨
      (-1 ≤ d i ∧ d i ≤ 2 ∧ 6 + d i - a i ≤ b i ∧
        delta i ≤ 1 + 2 * d i + a i)) :
    (∑ i ∈ F, delta i) ≤ partialPotential2 B s := by
  induction F using Finset.induction_on generalizing B s with
  | empty => simpa using partialPotential2_nonneg B s
  | @insert i F hi ih =>
    have hbFi := hb0 i (mem_insert_self i F)
    have haFi := ha0 i (mem_insert_self i F)
    have hdFi := hd0 i (mem_insert_self i F)
    have hbF : ∀ j ∈ F, 0 ≤ b j := fun j hj => hb0 j (mem_insert_of_mem hj)
    have haF : ∀ j ∈ F, 0 ≤ a j := fun j hj => ha0 j (mem_insert_of_mem hj)
    have hdF : ∀ j ∈ F, 0 ≤ delta j := fun j hj => hd0 j (mem_insert_of_mem hj)
    have hcF : ∀ j ∈ F, (b j = 3 ∧ a j = 0 ∧ delta j ≤ 1) ∨
      (-1 ≤ d j ∧ d j ≤ 2 ∧ 6 + d j - a j ≤ b j ∧
        delta j ≤ 1 + 2 * d j + a j) :=
      fun j hj => hc j (mem_insert_of_mem hj)
    rw [sum_insert hi] at hcost hscar ⊢
    have hbSum : (0 : ℤ) ≤ ∑ j ∈ F, b j := sum_nonneg hbF
    have haSum : (0 : ℤ) ≤ ∑ j ∈ F, a j := sum_nonneg haF
    by_cases hdz : delta i = 0
    · have hh := ih B s hB0 hB hs0 hs hbF haF hdF (by omega) (by omega) hcF
      omega
    · have hh := ih (B - b i) (s - a i) (by omega) (by omega) (by omega) (by omega)
        hbF haF hdF (by omega) (by omega) hcF
      have hstep := partialPotential2_step B s (b i) (a i) (delta i) (d i)
        hB0 hB hs0 hs hbFi (by omega) haFi (by omega) (by omega) (hc i (mem_insert_self i F))
      omega

lemma partial_family4 {I : Type u} [DecidableEq I] (F : Finset I)
    (b a delta d : I → ℤ) (B s : ℤ)
    (hB0 : 0 ≤ B) (hB : B ≤ 10) (hs0 : 0 ≤ s) (hs : s ≤ 3)
    (hb0 : ∀ i ∈ F, 0 ≤ b i) (ha0 : ∀ i ∈ F, 0 ≤ a i)
    (hd0 : ∀ i ∈ F, 0 ≤ delta i)
    (hcost : ∑ i ∈ F, b i ≤ B) (hscar : ∑ i ∈ F, a i ≤ s)
    (hc : ∀ i ∈ F, (b i = 3 ∧ a i = 0 ∧ delta i ≤ 1) ∨
      (-2 ≤ d i ∧ d i ≤ 1 ∧ 6 + d i - a i ≤ b i ∧
        delta i ≤ 1 + 2 * d i + a i)) :
    (∑ i ∈ F, delta i) ≤ partialPotential4 B s := by
  induction F using Finset.induction_on generalizing B s with
  | empty => simpa using partialPotential4_nonneg B s
  | @insert i F hi ih =>
    have hbFi := hb0 i (mem_insert_self i F)
    have haFi := ha0 i (mem_insert_self i F)
    have hdFi := hd0 i (mem_insert_self i F)
    have hbF : ∀ j ∈ F, 0 ≤ b j := fun j hj => hb0 j (mem_insert_of_mem hj)
    have haF : ∀ j ∈ F, 0 ≤ a j := fun j hj => ha0 j (mem_insert_of_mem hj)
    have hdF : ∀ j ∈ F, 0 ≤ delta j := fun j hj => hd0 j (mem_insert_of_mem hj)
    have hcF : ∀ j ∈ F, (b j = 3 ∧ a j = 0 ∧ delta j ≤ 1) ∨
      (-2 ≤ d j ∧ d j ≤ 1 ∧ 6 + d j - a j ≤ b j ∧
        delta j ≤ 1 + 2 * d j + a j) :=
      fun j hj => hc j (mem_insert_of_mem hj)
    rw [sum_insert hi] at hcost hscar ⊢
    have hbSum : (0 : ℤ) ≤ ∑ j ∈ F, b j := sum_nonneg hbF
    have haSum : (0 : ℤ) ≤ ∑ j ∈ F, a j := sum_nonneg haF
    by_cases hdz : delta i = 0
    · have hh := ih B s hB0 hB hs0 hs hbF haF hdF (by omega) (by omega) hcF
      omega
    · have hh := ih (B - b i) (s - a i) (by omega) (by omega) (by omega) (by omega)
        hbF haF hdF (by omega) (by omega) hcF
      have hstep := partialPotential4_step B s (b i) (a i) (delta i) (d i)
        hB0 hB hs0 hs hbFi (by omega) haFi (by omega) (by omega) (hc i (mem_insert_self i F))
      omega

lemma high_data_all {A C H : Finset V} (h : C02Input G A C)
    (hH : H ∈ maxHighFamily G A C) :
    H ⊆ A ∧ 3 ≤ #H ∧ 2 ≤ thetaC02 G C H ∧ H ≠ A ∧
      ∀ U, U ⊆ A → H ⊆ U → U ≠ H → thetaC02 G C U ≤ 1 := by
  obtain ⟨hs, hm⟩ := mem_maximalMembers.mp hH
  obtain ⟨hHA, h3, ht⟩ := mem_highSets.mp hs
  have hne : H ≠ A := by intro he; rw [he, theta_whole h] at ht; omega
  refine ⟨hHA, h3, ht, hne, ?_⟩
  intro U hUA hHU hUH
  by_contra hh
  have hc := card_le_card hHU
  exact hUH (hm U (mem_highSets.mpr ⟨hUA, by omega, by omega⟩) hHU)

lemma core_high_module {A C K H : Finset V} (h : C02Input G A C)
    (hK : K ⊆ A) (htK : thetaC02 G C K = 3)
    (hH : H ∈ maxHighFamily G A C) : Disjoint K H ∨ K ⊆ H := by
  classical
  by_cases hdis : Disjoint K H
  · exact Or.inl hdis
  by_cases hsub : K ⊆ H
  · exact Or.inr hsub
  obtain ⟨hHA, hH3, htH, _, hmax⟩ := high_data_all h hH
  have hwa : K ∪ H ⊆ A := union_subset hK hHA
  have hwt : K ∪ H ≠ H := by intro he; exact hsub (he ▸ subset_union_left)
  have hwt1 := hmax (K ∪ H) hwa subset_union_right hwt
  have hi : (K ∩ H).Nonempty := not_disjoint_iff_nonempty_inter.mp hdis
  have hia : K ∩ H ⊆ A := inter_subset_left.trans hK
  have hsup := theta_supermodular (G := G) C K H
  have hit4 : 4 ≤ thetaC02 G C (K ∩ H) := by omega
  have hic : #(K ∩ H) = 1 := by
    have hpos := card_pos.mpr hi
    by_cases h3 : 3 ≤ #(K ∩ H)
    · have hb := theta_three h hia h3
      omega
    · have hs := theta_small (G := G) C (Z := K ∩ H) (by omega)
      omega
  obtain ⟨p, hia1⟩ := card_eq_one.mp hic
  have hpi : p ∈ K ∩ H := by rw [hia1]; simp
  obtain ⟨hpk, hph⟩ := mem_inter.mp hpi
  have htI : thetaC02 G C (K ∩ H) = 4 := by
    rw [theta_small (G := G) C (by omega)]
    omega
  have htH2 : thetaC02 G C H = 2 := by omega
  have hgs := theta_gap_sum (G := G) C K H
  have hgs0 : (∑ c ∈ C, columnGap (G := G) K H c) = 0 := by
    have hnon : 0 ≤ ∑ c ∈ C, columnGap (G := G) K H c :=
      sum_nonneg fun c _ => columnGap_nonneg (G := G) K H c
    omega
  have hg0 : ∀ c ∈ C, columnGap (G := G) K H c = 0 :=
    (sum_eq_zero_iff_of_nonneg (fun c _ => columnGap_nonneg (G := G) K H c)).mp hgs0
  have hyinter : dg G (cpr G C K ∩ cpr G C H) p = 0 := by
    unfold dg
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro c hc
    obtain ⟨hci, _hadj⟩ := mem_filter.mp hc
    obtain ⟨hck, hch⟩ := mem_inter.mp hci
    obtain ⟨hcc, hx⟩ := mem_cpr.mp hck
    have hy := (mem_cpr.mp hch).2
    have hs := singleton_gap_zero hia1 hx (hg0 c hcc)
    have hz := dg_le_card (G := G) ({p} : Finset V) c
    simp only [card_singleton] at hz
    omega
  have hdu := dg_union_add_dg_inter (G := G) (cpr G C K) (cpr G C H) p
  have hcap : dg G (cpr G C K ∪ cpr G C H) p ≤ 6 :=
    (dg_mono (union_subset (cpr_subset (G := G) C K) (cpr_subset (G := G) C H)) p).trans
      (h.capA p (hK hpk))
  have hrow := (theta3_geometry h hK htK).2.2.2.2.2 p hpk
  have hdH : dg G (cpr G C H) p ≤ 1 := by omega
  have he := theta_erase (G := G) (C := C) hph
  have hec := card_erase_add_one hph
  have he2 : 2 ≤ #(H.erase p) := by omega
  have hb := theta_order_two_le_three h ((erase_subset _ _).trans hHA) he2
  omega

lemma strict_min_small {A C H T : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hH : H ∈ maxHighFamily G A C)
    (htH : thetaC02 G C H = 2) (hT : T ∈ strictContainingFamily G A C H)
    (hs : #(T \ H) + #(petalJ G C H T) ≤ 2) :
    ec G (T \ H) (corePlus G C H) = 3 ∧ ec G H (petalJ G C H T) = 0 ∧
      df G C (T \ H) ≤ 1 := by
  have hsmall := strict_small h hH htH hT hs
  have hsub : T \ H ⊆ A := sdiff_subset.trans (maxPositive_data h (mem_strictContainingFamily.mp hT).1).1
  have hd := (minfive_deficit h hm hsub).2
  exact ⟨hsmall.2.2.2.2.1, hsmall.2.2.2.1, by omega⟩

lemma strict_min_items2 {A C H : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hH : H ∈ maxHighFamily G A C)
    (htH : thetaC02 G C H = 2) (hl : highLoss G C H = 2) :
    ∀ T ∈ strictContainingFamily G A C H,
      ((ec G (T \ H) (corePlus G C H) : ℤ) = 3 ∧
        (ec G H (petalJ G C H T) : ℤ) = 0 ∧ df G C (T \ H) ≤ 1) ∨
      (-1 ≤ petalD G C H T ∧ petalD G C H T ≤ 2 ∧
        6 + petalD G C H T - ec G H (petalJ G C H T) ≤ ec G (T \ H) (corePlus G C H) ∧
        df G C (T \ H) ≤ 1 + 2 * petalD G C H T + ec G H (petalJ G C H T)) := by
  intro T hT
  by_cases hs : #(T \ H) + #(petalJ G C H T) ≤ 2
  · obtain ⟨hb, ha, hd⟩ := strict_min_small h hm hH htH hT hs
    exact Or.inl ⟨by exact_mod_cast hb, by exact_mod_cast ha, hd⟩
  · have hb := strict_d_bounds h hH htH hT
    have hh := (high_geometry h hH htH).2.1
    have hc := strict_large h hH htH hT (by omega)
    have he := (strict_petal_exact h hH htH hT).1
    have ho : (0 : ℤ) ≤ ec G (T \ H) (C \ (corePlus G C H ∪ petalJ G C H T)) := by positivity
    refine Or.inr ⟨by omega, by omega, hc, by omega⟩

lemma strict_min_items4 {A C H : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hH : H ∈ maxHighFamily G A C)
    (htH : thetaC02 G C H = 2) (hl : highLoss G C H = 4) :
    ∀ T ∈ strictContainingFamily G A C H,
      ((ec G (T \ H) (corePlus G C H) : ℤ) = 3 ∧
        (ec G H (petalJ G C H T) : ℤ) = 0 ∧ df G C (T \ H) ≤ 1) ∨
      (-2 ≤ petalD G C H T ∧ petalD G C H T ≤ 1 ∧
        6 + petalD G C H T - ec G H (petalJ G C H T) ≤ ec G (T \ H) (corePlus G C H) ∧
        df G C (T \ H) ≤ 1 + 2 * petalD G C H T + ec G H (petalJ G C H T)) := by
  intro T hT
  by_cases hs : #(T \ H) + #(petalJ G C H T) ≤ 2
  · obtain ⟨hb, ha, hd⟩ := strict_min_small h hm hH htH hT hs
    exact Or.inl ⟨by exact_mod_cast hb, by exact_mod_cast ha, hd⟩
  · have hb := strict_d_bounds h hH htH hT
    have hh := (high_geometry h hH htH).2.1
    have hc := strict_large h hH htH hT (by omega)
    have he := (strict_petal_exact h hH htH hT).1
    have ho : (0 : ℤ) ≤ ec G (T \ H) (C \ (corePlus G C H ∪ petalJ G C H T)) := by positivity
    refine Or.inr ⟨by omega, by omega, hc, by omega⟩

lemma minfive_strict_budget {A C H : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hH : H ∈ maxHighFamily G A C)
    (htH : thetaC02 G C H = 2) (hdH : 0 < df G C H) :
    (∑ T ∈ strictContainingFamily G A C H, df G C (T \ H)) ≤
      10 - df G C H ∧
    (highLoss G C H = 4 → df G C H ≤ 2 →
      (∑ T ∈ strictContainingFamily G A C H, df G C (T \ H)) ≤ 9 - df G C H) := by
  have hKA := (high_data h hH htH).1
  have hgeom := (high_geometry h hH htH).1
  have hb := strict_boundary_budget h hH htH
  have ha := strict_scar_budget h hH htH
  have hscar0 : 0 ≤ highLoss G C H - df G C H := by
    rw [← high_outside_alpha]
    positivity
  have hdel : ∀ T ∈ strictContainingFamily G A C H, 0 ≤ df G C (T \ H) :=
    fun T hT => (c02_deficit_bounds h (sdiff_subset.trans (maxPositive_data h (mem_strictContainingFamily.mp hT).1).1)).1
  rcases hgeom with h0 | h2 | h4
  · omega
  · have hh := partial_family2 (strictContainingFamily G A C H)
      (fun T => (ec G (T \ H) (corePlus G C H) : ℤ))
      (fun T => (ec G H (petalJ G C H T) : ℤ))
      (fun T => df G C (T \ H)) (petalD G C H) 14 (2 - df G C H)
      (by omega) (by omega) (by omega) (by omega)
      (fun _ _ => by positivity) (fun _ _ => by positivity) hdel
      (by omega) (by omega) (strict_min_items2 h hm hH htH h2)
    norm_num [partialPotential2] at hh
    constructor
    · split_ifs at hh <;> omega
    · intro hh4
      omega
  · have hh := partial_family4 (strictContainingFamily G A C H)
      (fun T => (ec G (T \ H) (corePlus G C H) : ℤ))
      (fun T => (ec G H (petalJ G C H T) : ℤ))
      (fun T => df G C (T \ H)) (petalD G C H) 10 (4 - df G C H)
      (by omega) (by omega) (by omega) (by omega)
      (fun _ _ => by positivity) (fun _ _ => by positivity) hdel
      (by omega) (by omega) (strict_min_items4 h hm hH htH h4)
    norm_num [partialPotential4] at hh
    constructor
    · split_ifs at hh <;> omega
    · intro _ hd2
      split_ifs at hh <;> omega

variable (G) in
 def privateRows (A C H : Finset V) : Finset V :=
   (A \ H) \ (strictContainingFamily G A C H).biUnion (fun T => T \ H)

lemma minfive_private_deficit {A C H : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hH : H ∈ maxHighFamily G A C)
    (htH : thetaC02 G C H = 2) (hdH : 0 < df G C H) :
    2 ≤ df G C (privateRows G A C H) ∧
      (highLoss G C H = 4 → df G C H ≤ 2 → 3 ≤ df G C (privateRows G A C H)) := by
  have hsub := strict_union_subset (K := H) h
  have hs := df_sdiff_add (G := G) (S := C) hsub
  have ht := df_sdiff_add (G := G) (S := C) (high_data h hH htH).1
  have hb := minfive_strict_budget h hm hH htH hdH
  have hd := strict_deficit_union h hH htH
  have htot := c02_total_deficit h
  change df G C (privateRows G A C H) +
    df G C ((strictContainingFamily G A C H).biUnion (fun T => T \ H)) = df G C (A \ H) at hs
  constructor
  · omega
  · intro hl hde
    have hc := hb.2 hl hde
    omega

lemma minfive_private_row {A C H : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hH : H ∈ maxHighFamily G A C)
    (htH : thetaC02 G C H = 2) (hdH : 0 < df G C H) :
    ∃ r ∈ privateRows G A C H, dg G C r = 5 := by
  have hd := (minfive_private_deficit h hm hH htH hdH).1
  by_contra hn
  have hsub : privateRows G A C H ⊆ A := sdiff_subset.trans sdiff_subset
  have hz : df G C (privateRows G A C H) = 0 := by
    unfold df
    apply sum_eq_zero
    intro r hr
    have h5 := hm r (hsub hr)
    have h6 := h.capA r (hsub hr)
    have hne : dg G C r ≠ 5 := fun he => hn ⟨r, hr, he⟩
    omega
  omega

lemma core_data {A C K : Finset V} (hK : K ∈ maxThetaThreeFamily G A C) :
    K ⊆ A ∧ thetaC02 G C K = 3 ∧
      ∀ U ⊆ A, thetaC02 G C U = 3 → K ⊆ U → U = K := by
  obtain ⟨hs, hm⟩ := mem_maximalMembers.mp hK
  obtain ⟨hKA, ht⟩ := mem_thetaThreeSets.mp hs
  refine ⟨hKA, ht, ?_⟩
  intro U hU htU hKU
  exact hm U (mem_thetaThreeSets.mpr ⟨hU, htU⟩) hKU

variable (G) in
 def PositiveCoreResidual (A C : Finset V) : Prop :=
   ∀ a ∈ A, dg G C a = 5 → ∃ K ∈ maxThetaThreeFamily G A C, a ∈ K

lemma core_loss_bound {A C K : Finset V} (h : C02Input G A C)
    (hK : K ∈ maxThetaThreeFamily G A C) : 0 ≤ df G C K ∧ df G C K ≤ 1 := by
  have hd := theta3_original_loss h (core_data hK).1 (core_data hK).2.1
  have h0 := (c02_deficit_bounds h (core_data hK).1).1
  have he : (0 : ℤ) ≤ ec G K (C \ cpr G C K) := by positivity
  omega

lemma residual_ordinary_six {A C : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C)
    {p : V} (hp : p ∈ A) (ho : Ordinary G A C p) : dg G C p = 6 := by
  have h5 := hm p hp
  have h6 := h.capA p hp
  by_contra hn
  have he : dg G C p = 5 := by omega
  obtain ⟨K, hK, hpK⟩ := hr p hp he
  exact ho K hK hpK

lemma private_not_H {A C H : Finset V} {r : V} (hr : r ∈ privateRows G A C H) :
    r ∈ A ∧ r ∉ H := by
  exact mem_sdiff.mp (mem_sdiff.mp hr).1

lemma private_not_strict {A C H T : Finset V} {r : V}
    (hr : r ∈ privateRows G A C H) (hT : T ∈ strictContainingFamily G A C H) : r ∉ T := by
  intro hrT
  have hrH := (private_not_H hr).2
  exact (mem_sdiff.mp hr).2 (mem_biUnion.mpr ⟨T, hT, mem_sdiff.mpr ⟨hrT, hrH⟩⟩)

lemma private_core {A C H : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C)
    (hH : H ∈ maxHighFamily G A C) (htH : thetaC02 G C H = 2)
    (hdH : 0 < df G C H) :
    ∃ K ∈ maxThetaThreeFamily G A C, df G C K = 1 ∧ Disjoint K H ∧
      ∀ T ∈ strictContainingFamily G A C H, Disjoint K T := by
  obtain ⟨r, hrP, hr5⟩ := minfive_private_row h hm hH htH hdH
  obtain ⟨K, hK, hrK⟩ := hr r (private_not_H hrP).1 hr5
  have hKA := (core_data hK).1
  have htK := (core_data hK).2.1
  have hdis : Disjoint K H := by
    rcases core_high_module h hKA htK hH with hd | hs
    · exact hd
    · exact False.elim ((private_not_H hrP).2 (hs hrK))
  have hdf : df G C K = 1 := by
    have hbound := core_loss_bound h hK
    have hsingle : (6 : ℤ) - (dg G C r : ℤ) ≤ df G C K :=
      single_le_sum (f := fun a => (6 : ℤ) - (dg G C a : ℤ))
        (fun a ha => by have hh := h.capA a (hKA ha); omega) hrK
    omega
  refine ⟨K, hK, hdf, hdis, ?_⟩
  intro T hT
  rcases n1_nesting h hKA htK (mem_strictContainingFamily.mp hT).1 with hd | hs
  · exact hd
  · exact False.elim (private_not_strict hrP hT (hs hrK))

lemma apf_core_member {A C K L : Finset V} (h : C02Input G A C)
    (hapf : APF G A C) (hK : K ∈ maxThetaThreeFamily G A C)
    (hL : L ∈ maxThetaThreeFamily G A C) (hne : K ≠ L) :
    ∃ T ∈ maxPositiveFamily G A C, K ⊆ T ∧ L ⊆ T := by
  have hd := maximal_theta3_disjoint h hK hL hne
  obtain ⟨p, hp⟩ := card_pos.mp (show 0 < #K by
    have hh := (theta3_large_proper h (core_data hK).1 (core_data hK).2.1).1
    omega)
  obtain ⟨q, hq⟩ := card_pos.mp (show 0 < #L by
    have hh := (theta3_large_proper h (core_data hL).1 (core_data hL).2.1).1
    omega)
  have hpq : p ≠ q := fun he => disjoint_left.mp hd hp (he ▸ hq)
  obtain ⟨T, hT, hpT, hqT⟩ := hapf p ((core_data hK).1 hp) q ((core_data hL).1 hq) hpq
  have hKT : K ⊆ T := by
    rcases n1_nesting h (core_data hK).1 (core_data hK).2.1 hT with hdis | hs
    · exact False.elim (disjoint_left.mp hdis hp hpT)
    · exact hs
  have hLT : L ⊆ T := by
    rcases n1_nesting h (core_data hL).1 (core_data hL).2.1 hT with hdis | hs
    · exact False.elim (disjoint_left.mp hdis hq hqT)
    · exact hs
  exact ⟨T, hT, hKT, hLT⟩

lemma high_partial_core {A C H K L : Finset V} (h : C02Input G A C)
    (hapf : APF G A C) (hH : H ∈ maxHighFamily G A C)
    (htH : thetaC02 G C H = 2) (hK : K ∈ maxThetaThreeFamily G A C)
    (hKH : K ⊆ H) (hL : L ∈ maxThetaThreeFamily G A C)
    (hLH : Disjoint L H)
    (hLS : ∀ T ∈ strictContainingFamily G A C H, Disjoint L T) :
    ∃ T ∈ maxPositiveFamily G A C, K ⊆ T ∧ L ⊆ T ∧
      H ∩ T = K ∧ thetaC02 G C T = 1 ∧ thetaC02 G C (H ∪ T) = 0 ∧
      ∀ c ∈ C, columnGap (G := G) H T c = 0 := by
  have hne : K ≠ L := by
    intro he
    obtain ⟨p, hp⟩ := card_pos.mp (show 0 < #L by
      have hh := (theta3_large_proper h (core_data hL).1 (core_data hL).2.1).1
      omega)
    exact disjoint_left.mp hLH hp (hKH (he ▸ hp))
  obtain ⟨T, hT, hKT, hLT⟩ := apf_core_member h hapf hK hL hne
  obtain ⟨hHA, _, _, _⟩ := high_data h hH htH
  obtain ⟨hTA, _, htpos, hmT⟩ := maxPositive_data h hT
  have hnot : ¬ H ⊆ T := by
    intro hs
    have hTN : T ≠ H := by
      intro he
      obtain ⟨p, hp⟩ := card_pos.mp (show 0 < #L by
        have hh := (theta3_large_proper h (core_data hL).1 (core_data hL).2.1).1
        omega)
      exact disjoint_left.mp hLH hp (he ▸ hLT hp)
    have hTs := mem_strictContainingFamily.mpr ⟨hT, hs, hTN⟩
    obtain ⟨p, hp⟩ := card_pos.mp (show 0 < #L by
      have hh := (theta3_large_proper h (core_data hL).1 (core_data hL).2.1).1
      omega)
    exact disjoint_left.mp (hLS T hTs) hp (hLT hp)
  have hUn : H ∪ T ≠ T := by intro he; exact hnot (he ▸ subset_union_left)
  have hUb := hmT (H ∪ T) (union_subset hHA hTA) subset_union_right hUn
  have hKI : K ⊆ H ∩ T := subset_inter hKH hKT
  have hI3 : 3 ≤ #(H ∩ T) :=
    ((theta3_large_proper h (core_data hK).1 (core_data hK).2.1).1).trans (card_le_card hKI)
  have hbI := theta_three h (inter_subset_left.trans hHA) hI3
  have hs := theta_supermodular (G := G) C H T
  have htI : thetaC02 G C (H ∩ T) = 3 := by omega
  have hIe : H ∩ T = K := (core_data hK).2.2 _ (inter_subset_left.trans hHA) htI hKI
  have hgap := theta_gap_sum (G := G) C H T
  have hnon : 0 ≤ ∑ c ∈ C, columnGap (G := G) H T c :=
    sum_nonneg fun c _ => columnGap_nonneg (G := G) H T c
  have hsum0 : (∑ c ∈ C, columnGap (G := G) H T c) = 0 := by omega
  refine ⟨T, hT, hKT, hLT, hIe, by omega, by omega, ?_⟩
  intro c hc
  have hh := single_le_sum (fun c _ => columnGap_nonneg (G := G) H T c) hc
  have hh0 := columnGap_nonneg (G := G) H T c
  omega

lemma high_private_shield_columns {A C H K L : Finset V} (h : C02Input G A C)
    (hapf : APF G A C) (hH : H ∈ maxHighFamily G A C)
    (htH : thetaC02 G C H = 2) (hK : K ∈ maxThetaThreeFamily G A C)
    (hKH : K ⊆ H) (hL : L ∈ maxThetaThreeFamily G A C)
    (hLH : Disjoint L H)
    (hLS : ∀ T ∈ strictContainingFamily G A C H, Disjoint L T) :
    ∀ c ∈ cpr G C L, dg G (H \ K) c = 0 := by
  obtain ⟨T, hT, hKT, hLT, hi, _, _, hg⟩ :=
    high_partial_core h hapf hH htH hK hKH hL hLH hLS
  have hHA := (high_data h hH htH).1
  intro c hc
  obtain ⟨hcC, hcL⟩ := mem_cpr.mp hc
  have hHL : Disjoint H L := hLH.symm
  have hLunion := dg_union_of_disjoint (G := G) hHL c
  have hLcap : dg G (H ∪ L) c ≤ 6 := by
    have hh := dg_mono (G := G) (union_subset hHA (core_data hL).1) c
    rw [h.satC c hcC] at hh
    exact hh
  have hd := dg_sdiff_add (G := G) hKH c
  have hz := dg_mono (G := G) hKH c
  by_cases hcK : c ∈ cpr G C K
  · have hc3 := (mem_cpr.mp hcK).2
    omega
  · have hlo := theta3_outside_low h (core_data hK).1 (core_data hK).2.1
      (mem_sdiff.mpr ⟨hcC, hcK⟩)
    have hKL : Disjoint K L := hHL.mono_left hKH
    have hsum := dg_union_of_disjoint (G := G) hKL c
    have hym := dg_mono (G := G) (union_subset hKT hLT) c
    have hdu := dg_union_add_dg_inter (G := G) H T c
    have hhg := hg c hcC
    unfold columnGap at hhg
    rw [hi] at hhg hdu
    omega

lemma high_private_shield {A C H K L : Finset V} (h : C02Input G A C)
    (hapf : APF G A C) (hH : H ∈ maxHighFamily G A C)
    (htH : thetaC02 G C H = 2) (hK : K ∈ maxThetaThreeFamily G A C)
    (hKH : K ⊆ H) (hL : L ∈ maxThetaThreeFamily G A C)
    (hLH : Disjoint L H)
    (hLS : ∀ T ∈ strictContainingFamily G A C H, Disjoint L T)
    {p : V} (hp : p ∈ H \ K) : dg G (cpr G C L) p = 0 := by
  classical
  have hh := high_private_shield_columns h hapf hH htH hK hKH hL hLH hLS
  unfold dg
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨hcL, hpc⟩ := mem_filter.mp hc
  have hp1 : 0 < dg G (H \ K) c :=
    card_pos.mpr ⟨p, mem_filter.mpr ⟨hp, G.adj_symm hpc⟩⟩
  rw [hh c hcL] at hp1
  omega

lemma positive_deficit_row {A C Z : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hZ : Z ⊆ A) (hd : 0 < df G C Z) :
    ∃ p ∈ Z, dg G C p = 5 := by
  by_contra hn
  have hz : df G C Z = 0 := by
    unfold df
    apply sum_eq_zero
    intro p hp
    have h5 := hm p (hZ hp)
    have h6 := h.capA p (hZ hp)
    have hne : dg G C p ≠ 5 := fun he => hn ⟨p, hp, he⟩
    omega
  omega

lemma high_contains_positive_core {A C H : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C)
    (hH : H ∈ maxHighFamily G A C) (hd : 0 < df G C H) :
    ∃ K ∈ maxThetaThreeFamily G A C, K ⊆ H ∧ df G C K = 1 := by
  have hHA := (high_data_all h hH).1
  obtain ⟨p, hp, hp5⟩ := positive_deficit_row h hm hHA hd
  obtain ⟨K, hK, hpK⟩ := hr p (hHA hp) hp5
  have hKH : K ⊆ H := by
    rcases core_high_module h (core_data hK).1 (core_data hK).2.1 hH with hdis | hs
    · exact False.elim (disjoint_left.mp hdis hpK hp)
    · exact hs
  have hdf := core_loss_bound h hK
  have hsingle : (6 : ℤ) - (dg G C p : ℤ) ≤ df G C K :=
    single_le_sum (f := fun a => (6 : ℤ) - (dg G C a : ℤ))
      (fun a ha => by have hh := h.capA a ((core_data hK).1 ha); omega) hpK
  exact ⟨K, hK, hKH, by omega⟩

lemma cores_inside_high_canonical_disjoint {A C H K L : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hH : H ∈ maxHighFamily G A C) (htH : thetaC02 G C H = 2) (hdH : 0 < df G C H)
    (hK : K ∈ maxThetaThreeFamily G A C) (hKH : K ⊆ H)
    (hL : L ∈ maxThetaThreeFamily G A C) (hLH : L ⊆ H) (hne : K ≠ L) :
    Disjoint (cpr G C K) (cpr G C L) := by
  classical
  obtain ⟨M, hM, _, hMH, hMS⟩ := private_core h hm hr hH htH hdH
  obtain ⟨T, hT, hKT, hMT, hiT, htT, _, _⟩ :=
    high_partial_core h hapf hH htH hK hKH hM hMH hMS
  obtain ⟨U, hU, hLU, hMU, hiU, htU, _, _⟩ :=
    high_partial_core h hapf hH htH hL hLH hM hMH hMS
  have hTU : T ≠ U := by intro he; rw [he, hiU] at hiT; exact hne hiT.symm
  obtain ⟨hTA, _, _, hmT⟩ := maxPositive_data h hT
  obtain ⟨hUA, _, _, _⟩ := maxPositive_data h hU
  have hnot : ¬ U ⊆ T := by
    intro hs
    obtain ⟨hTS, _⟩ := mem_maximalMembers.mp hT
    obtain ⟨_, hmU⟩ := mem_maximalMembers.mp hU
    exact hTU (hmU T hTS hs)
  have hUn : T ∪ U ≠ T := by intro he; exact hnot (he ▸ subset_union_right)
  have hUb := hmT (T ∪ U) (union_subset hTA hUA) subset_union_left hUn
  have hMI := subset_inter hMT hMU
  have hM3 := (theta3_large_proper h (core_data hM).1 (core_data hM).2.1).1
  have hIb := theta_three h (inter_subset_left.trans hTA) (hM3.trans (card_le_card hMI))
  have hgap := theta_gap_sum (G := G) C T U
  have hsum : (∑ c ∈ C, columnGap (G := G) T U c) ≤ 1 := by omega
  apply disjoint_left.mpr
  intro c hcK hcL
  obtain ⟨hcC, hk3⟩ := mem_cpr.mp hcK
  have hl3 := (mem_cpr.mp hcL).2
  have hKL := maximal_theta3_disjoint h hK hL hne
  have hrow : dg G (K ∪ L) c = 6 := by
    have hd := dg_union_of_disjoint (G := G) hKL c
    have hm := dg_mono (G := G) (union_subset (core_data hK).1 (core_data hL).1) c
    rw [h.satC c hcC] at hm
    omega
  have hcoreSum := dg_union_of_disjoint (G := G) hKL c
  have hKc : dg G K c = 3 := by omega
  have hLc : dg G L c = 3 := by omega
  have hTminus : dg G (A \ (K ∪ L)) c = 0 := by
    have hd := dg_sdiff_add (G := G) (union_subset (core_data hK).1 (core_data hL).1) c
    rw [h.satC c hcC, hrow] at hd
    omega
  have hIn : dg G (T ∩ U) c = 0 := by
    have hIoutside : T ∩ U ⊆ A \ (K ∪ L) := by
      intro a ha
      have haA := hTA (mem_inter.mp ha).1
      refine mem_sdiff.mpr ⟨haA, ?_⟩
      intro hkL
      rcases mem_union.mp hkL with haK | haL
      · have haH := hKH haK
        have haL' : a ∈ L := hiU ▸ mem_inter.mpr ⟨haH, (mem_inter.mp ha).2⟩
        exact disjoint_left.mp hKL haK haL'
      · have haH := hLH haL
        have haK' : a ∈ K := hiT ▸ mem_inter.mpr ⟨haH, (mem_inter.mp ha).1⟩
        exact disjoint_left.mp hKL haK' haL
    have hh := dg_mono (G := G) hIoutside c
    omega
  have hTc : dg G T c = 3 := by
    have hlo := dg_mono (G := G) hKT c
    have hdc := dg_union_add_dg_inter (G := G) H T c
    have hHlo := dg_mono (G := G) (union_subset hKH hLH) c
    have hHhi := dg_mono (G := G) (high_data h hH htH).1 c
    have hUhi := dg_mono (G := G) (union_subset (high_data h hH htH).1 hTA) c
    rw [h.satC c hcC] at hHhi hUhi
    rw [hiT] at hdc
    omega
  have hUc : dg G U c = 3 := by
    have hlo := dg_mono (G := G) hLU c
    have hdc := dg_union_add_dg_inter (G := G) H U c
    have hHlo := dg_mono (G := G) (union_subset hKH hLH) c
    have hHhi := dg_mono (G := G) (high_data h hH htH).1 c
    have hUhi := dg_mono (G := G) (union_subset (high_data h hH htH).1 hUA) c
    rw [h.satC c hcC] at hHhi hUhi
    rw [hiU] at hdc
    omega
  have hdu := dg_union_add_dg_inter (G := G) T U c
  have hgg : columnGap (G := G) T U c = 2 := by
    unfold columnGap
    omega
  have hs := single_le_sum (fun c _ => columnGap_nonneg (G := G) T U c) hcC
  omega

lemma high_partial_ordinary {A C H T : Finset V} (h : C02Input G A C)
    (hH : H ∈ maxHighFamily G A C) (htH : thetaC02 G C H = 2)
    (hT : T ∈ maxPositiveFamily G A C) (hnot : ¬ H ⊆ T)
    {p : V} (hpH : p ∈ H) (hpT : p ∈ T) (ho : Ordinary G A C p) : H ∩ T = {p} := by
  obtain ⟨hHA, _, _, _⟩ := high_data h hH htH
  obtain ⟨hTA, _, htT, hmT⟩ := maxPositive_data h hT
  have hUne : H ∪ T ≠ T := by intro he; exact hnot (he ▸ subset_union_left)
  have hU := hmT (H ∪ T) (union_subset hHA hTA) subset_union_right hUne
  have hs := theta_supermodular (G := G) C H T
  have hpI : p ∈ H ∩ T := mem_inter.mpr ⟨hpH, hpT⟩
  have hI2 : #(H ∩ T) < 2 := by
    by_contra hh
    have hb := ordinary_theta_le_two h (inter_subset_left.trans hHA) (by omega) hpI ho
    omega
  have hI0 : 0 < #(H ∩ T) := card_pos.mpr ⟨p, hpI⟩
  obtain ⟨a, ha⟩ := card_eq_one.mp (show #(H ∩ T) = 1 by omega)
  have he : p = a := mem_singleton.mp (ha ▸ hpI)
  simpa [he] using ha

lemma core_insert_cpr {A C K : Finset V} (h : C02Input G A C)
    (hKA : K ⊆ A) (htK : thetaC02 G C K = 3) {p : V} (hpK : p ∉ K) :
    cpr G C (insert p K) = cpr G C K := by
  apply Subset.antisymm
  · intro c hc
    obtain ⟨hcC, hd⟩ := mem_cpr.mp hc
    by_contra hh
    have hlo := theta3_outside_low h hKA htK (mem_sdiff.mpr ⟨hcC, hh⟩)
    have hdu := dg_union_of_disjoint (G := G) (disjoint_singleton_left.mpr hpK) c
    simp only [singleton_union] at hdu
    have h1 := dg_le_card (G := G) ({p} : Finset V) c
    simp only [card_singleton] at h1
    omega
  · intro c hc
    obtain ⟨hcC, hd⟩ := mem_cpr.mp hc
    exact mem_cpr.mpr ⟨hcC, hd.trans (dg_mono (G := G) (subset_insert _ _) c)⟩

lemma residual_ordinary_high_out {A C H : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hH : H ∈ maxHighFamily G A C) (htH : thetaC02 G C H = 2) (hdH : 0 < df G C H)
    {p : V} (hpH : p ∈ H) (ho : Ordinary G A C p) :
    2 ≤ dg G (C \ corePlus G C H) p := by
  classical
  have hHA := (high_data h hH htH).1
  have hpA := hHA hpH
  have hp6 := residual_ordinary_six h hm hr hpA ho
  obtain ⟨K, hK, hKH, _⟩ := high_contains_positive_core h hm hr hH hdH
  obtain ⟨r, hrP, hr5⟩ := minfive_private_row h hm hH htH hdH
  obtain ⟨L, hL, hrL⟩ := hr r (private_not_H hrP).1 hr5
  have hLH : Disjoint L H := by
    rcases core_high_module h (core_data hL).1 (core_data hL).2.1 hH with hd | hs
    · exact hd
    · exact False.elim ((private_not_H hrP).2 (hs hrL))
  have hLS : ∀ T ∈ strictContainingFamily G A C H, Disjoint L T := by
    intro T hT
    rcases n1_nesting h (core_data hL).1 (core_data hL).2.1 (mem_strictContainingFamily.mp hT).1 with hd | hs
    · exact hd
    · exact False.elim (private_not_strict hrP hT (hs hrL))
  have hpr : p ≠ r := fun he => (private_not_H hrP).2 (he ▸ hpH)
  obtain ⟨T, hT, hpT, hrT⟩ := hapf p hpA r (private_not_H hrP).1 hpr
  have hLT : L ⊆ T := by
    rcases n1_nesting h (core_data hL).1 (core_data hL).2.1 hT with hd | hs
    · exact False.elim (disjoint_left.mp hd hrL hrT)
    · exact hs
  have hnot : ¬ H ⊆ T := by
    intro hs
    have hne : T ≠ H := fun he => (private_not_H hrP).2 (he ▸ hrT)
    exact private_not_strict hrP (mem_strictContainingFamily.mpr ⟨hT, hs, hne⟩) hrT
  have hi := high_partial_ordinary h hH htH hT hnot hpH hpT ho
  have hb := singleton_gap_budget h hH htH hT hnot hi
  obtain ⟨hTA, hT3, htpos, _⟩ := maxPositive_data h hT
  have htT := ordinary_theta_le_two h hTA (by omega) hpT ho
  have h2 : 2 ≤ #(T.erase p) := by have hh := card_erase_add_one hpT; omega
  have heθ := theta_erase (G := G) (C := C) hpT
  have heB := theta_order_two_le_three h ((erase_subset _ _).trans hTA) h2
  have hsubC : cpr G C T ⊆ C := cpr_subset (G := G) C T
  have hsplit := dg_sdiff_add (G := G) (inter_subset_right (s₁ := corePlus G C H) (s₂ := cpr G C T)) p
  have hsub : cpr G C T \ (corePlus G C H ∩ cpr G C T) ⊆ C \ corePlus G C H := by
    intro c hc
    obtain ⟨hcT, hcN⟩ := mem_sdiff.mp hc
    exact mem_sdiff.mpr ⟨hsubC hcT, fun hcH => hcN (mem_inter.mpr ⟨hcH, hcT⟩)⟩
  have hmono := dg_mono (G := G) hsub p
  by_contra hout
  have ht1 : thetaC02 G C T = 1 := by omega
  have hdT : dg G (cpr G C T) p = 2 := by omega
  have he3 : thetaC02 G C (T.erase p) = 3 := by omega
  have hLer : L ⊆ T.erase p := by
    intro a ha
    refine mem_erase.mpr ⟨?_, hLT ha⟩
    intro he
    exact ho L hL (he ▸ ha)
  have herL : T.erase p = L :=
    (core_data hL).2.2 _ ((erase_subset _ _).trans hTA) he3 hLer
  have hpL : p ∉ L := ho L hL
  have hTL : T = insert p L := by
    rw [← herL]
    exact (insert_erase hpT).symm
  have hcan := core_insert_cpr h (core_data hL).1 (core_data hL).2.1 hpL
  have hshield := high_private_shield h hapf hH htH hK hKH hL hLH hLS
    (mem_sdiff.mpr ⟨hpH, ho K hK⟩)
  rw [hTL, hcan] at hdT
  omega

lemma theta_selected_upper (C B Y : Finset V) (hY : Y ⊆ C)
    (hy : ∀ c ∈ Y, 2 ≤ dg G B c) :
    thetaC02 G C B ≤ 8 - 4 * (#B : ℤ) + ec G B C - 2 * #Y := by
  have hf : (∑ c ∈ Y, max 0 ((dg G B c : ℤ) - 2)) =
      (ec G B Y : ℤ) - 2 * #Y := by
    have hh : ∀ c ∈ Y, max 0 ((dg G B c : ℤ) - 2) = (dg G B c : ℤ) - 2 := by
      intro c hc
      have hd := hy c hc
      omega
    rw [sum_congr rfl hh, sum_sub_distrib, sum_const, nsmul_eq_mul, ec_comm]
    simp only [ec, Nat.cast_sum]
    ring
  have ho : (∑ c ∈ C \ Y, max 0 ((dg G B c : ℤ) - 2)) ≤ ec G B (C \ Y) := by
    rw [ec_comm]
    change _ ≤ ((∑ c ∈ C \ Y, dg G B c : ℕ) : ℤ)
    rw [Nat.cast_sum]
    exact sum_le_sum fun c _ => by omega
  have hs := sum_sdiff hY (f := fun c => max 0 ((dg G B c : ℤ) - 2))
  have he : (ec G B (C \ Y) : ℤ) + ec G B Y = ec G B C := by
    exact_mod_cast ec_sdiff_add_right (G := G) hY B
  unfold thetaC02
  linarith

variable (G) in
 def coresIn (A C H : Finset V) : Finset (Finset V) :=
   (maxThetaThreeFamily G A C).filter fun K => K ⊆ H

lemma mem_coresIn {A C H K : Finset V} :
    K ∈ coresIn G A C H ↔ K ∈ maxThetaThreeFamily G A C ∧ K ⊆ H := mem_filter

lemma coresIn_pairwise {A C H : Finset V} (h : C02Input G A C) :
    (coresIn G A C H : Set (Finset V)).PairwiseDisjoint id := by
  intro K hK L hL hne
  exact maximal_theta3_disjoint h (mem_coresIn.mp hK).1 (mem_coresIn.mp hL).1 hne

lemma core_union_subset {A C H : Finset V} :
    (coresIn G A C H).biUnion id ⊆ H := by
  intro p hp
  obtain ⟨K, hK, hpK⟩ := mem_biUnion.mp hp
  exact (mem_coresIn.mp hK).2 hpK

lemma coresIn_cpr_pairwise {A C H : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hH : H ∈ maxHighFamily G A C) (htH : thetaC02 G C H = 2) (hdH : 0 < df G C H) :
    (coresIn G A C H : Set (Finset V)).PairwiseDisjoint (cpr G C) := by
  intro K hK L hL hne
  obtain ⟨hKF, hKH⟩ := mem_coresIn.mp hK
  obtain ⟨hLF, hLH⟩ := mem_coresIn.mp hL
  exact cores_inside_high_canonical_disjoint h hm hr hapf hH htH hdH hKF hKH hLF hLH hne

lemma core_union_theta_bound {A C H : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hH : H ∈ maxHighFamily G A C) (htH : thetaC02 G C H = 2) (hdH : 0 < df G C H) :
    thetaC02 G C ((coresIn G A C H).biUnion id) ≤
      8 - 4 * (#(coresIn G A C H) : ℤ) - df G C ((coresIn G A C H).biUnion id) := by
  let F := coresIn G A C H
  let B := F.biUnion id
  let Y := F.biUnion (cpr G C)
  have hYC : Y ⊆ C := by
    intro c hc
    obtain ⟨K, _, hcK⟩ := mem_biUnion.mp hc
    exact cpr_subset (G := G) C K hcK
  have hy : ∀ c ∈ Y, 2 ≤ dg G B c := by
    intro c hc
    obtain ⟨K, hK, hcK⟩ := mem_biUnion.mp hc
    have hKB : K ⊆ B := fun p hp => mem_biUnion.mpr ⟨K, hK, hp⟩
    have h3 := (mem_cpr.mp hcK).2
    exact (show 2 ≤ 3 by omega).trans (h3.trans (dg_mono (G := G) hKB c))
  have hcardB : (#B : ℤ) = ∑ K ∈ F, (#K : ℤ) := by
    exact_mod_cast card_biUnion (coresIn_pairwise (H := H) h)
  have hcardY : (#Y : ℤ) = ∑ K ∈ F, (#(cpr G C K) : ℤ) := by
    exact_mod_cast card_biUnion (coresIn_cpr_pairwise h hm hr hapf hH htH hdH)
  have hcy : (#Y : ℤ) = #B + 2 * #F := by
    have hc : ∀ K ∈ F, (#(cpr G C K) : ℤ) = #K + 2 := by
      intro K hK
      have hKF := (mem_coresIn.mp hK).1
      have hh := (theta3_geometry h (core_data hKF).1 (core_data hKF).2.1).2.2.1
      exact_mod_cast hh
    rw [hcardY, sum_congr rfl hc, sum_add_distrib, ← hcardB]
    simp only [sum_const, nsmul_eq_mul]
    ring
  have ht := theta_selected_upper (G := G) C B Y hYC hy
  have hd := df_eq (G := G) C B
  change thetaC02 G C B ≤ 8 - 4 * (#F : ℤ) - df G C B
  linarith

lemma high_outside_core_ordinary {A C H : Finset V} (h : C02Input G A C)
    (hH : H ∈ maxHighFamily G A C) {p : V}
    (hp : p ∈ H \ (coresIn G A C H).biUnion id) : Ordinary G A C p := by
  obtain ⟨hpH, hpN⟩ := mem_sdiff.mp hp
  intro K hK hpK
  have hKH : K ⊆ H := by
    rcases core_high_module h (core_data hK).1 (core_data hK).2.1 hH with hd | hs
    · exact False.elim (disjoint_left.mp hd hpK hpH)
    · exact hs
  exact hpN (mem_biUnion.mpr ⟨K, mem_coresIn.mpr ⟨hK, hKH⟩, hpK⟩)

lemma high_neutral_card {A C H : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hH : H ∈ maxHighFamily G A C) (htH : thetaC02 G C H = 2) (hdH : 0 < df G C H) :
    #(H \ (coresIn G A C H).biUnion id) ≤ 1 := by
  let O := H \ (coresIn G A C H).biUnion id
  have hout : 2 * #O ≤ ec G O (C \ corePlus G C H) := by
    unfold ec
    calc
      _ = ∑ _p ∈ O, 2 := by simp [mul_comm]
      _ ≤ _ := sum_le_sum fun p hp => residual_ordinary_high_out h hm hr hapf hH htH hdH
        (mem_sdiff.mp hp).1 (high_outside_core_ordinary h hH hp)
  have he := ec_mono_left (G := G) (show O ⊆ H from sdiff_subset) (C \ corePlus G C H)
  have hh := high_outside_alpha (G := G) (C := C) (K := H)
  have hl := (high_geometry h hH htH).1
  have houtz : 2 * (#O : ℤ) ≤ ec G O (C \ corePlus G C H) := by exact_mod_cast hout
  have hez : (ec G O (C \ corePlus G C H) : ℤ) ≤ ec G H (C \ corePlus G C H) := by exact_mod_cast he
  change #O ≤ 1
  omega

lemma high_core_union_deficit {A C H : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hH : H ∈ maxHighFamily G A C) :
    df G C ((coresIn G A C H).biUnion id) = df G C H := by
  have hsub := core_union_subset (G := G) (A := A) (C := C) (H := H)
  have hz : df G C (H \ (coresIn G A C H).biUnion id) = 0 := by
    unfold df
    apply sum_eq_zero
    intro p hp
    have h6 := residual_ordinary_six h hm hr ((high_data_all h hH).1 (mem_sdiff.mp hp).1)
      (high_outside_core_ordinary h hH hp)
    omega
  have hs := df_sdiff_add (G := G) (S := C) hsub
  omega

lemma theta_insert_upper {C B : Finset V} {p : V} (hp : p ∉ B) :
    thetaC02 G C (insert p B) ≤ thetaC02 G C B + (dg G C p : ℤ) - 4 := by
  have hca : (#(insert p B) : ℤ) = #B + 1 := by exact_mod_cast card_insert_of_notMem hp
  have hscalar : ∀ c ∈ C, max 0 ((dg G (insert p B) c : ℤ) - 2) ≤
      max 0 ((dg G B c : ℤ) - 2) + (dg G ({p} : Finset V) c : ℤ) := by
    intro c hc
    have hd := dg_union_of_disjoint (G := G) (disjoint_singleton_left.mpr hp) c
    simp only [singleton_union] at hd
    have h1 := dg_le_card (G := G) ({p} : Finset V) c
    simp only [card_singleton] at h1
    omega
  have hs := sum_le_sum hscalar
  rw [sum_add_distrib] at hs
  have he : (∑ c ∈ C, (dg G ({p} : Finset V) c : ℤ)) = dg G C p := by
    rw [← Nat.cast_sum]
    change (ec G C {p} : ℤ) = dg G C p
    rw [ec_comm]
    simp [ec]
  unfold thetaC02
  linarith

lemma residual_high_shape {A C H : Finset V} (h : C02Input G A C)
    (hm : MinFive G A C) (hr : PositiveCoreResidual G A C) (hapf : APF G A C)
    (hH : H ∈ maxHighFamily G A C) (htH : thetaC02 G C H = 2) (hdH : 0 < df G C H) :
    ∃ K ∈ maxThetaThreeFamily G A C, ∃ p,
      df G C K = 1 ∧ Ordinary G A C p ∧ p ∉ K ∧ H = insert p K ∧
      dg G C p = 6 ∧ dg G (cpr G C K) p = 3 := by
  classical
  let F := coresIn G A C H
  let B := F.biUnion id
  let O := H \ B
  have hBsub : B ⊆ H := core_union_subset (G := G)
  have hBdef := high_core_union_deficit h hm hr hH
  have htheta := core_union_theta_bound h hm hr hapf hH htH hdH
  have hOcard := high_neutral_card h hm hr hapf hH htH hdH
  change #O ≤ 1 at hOcard
  change df G C B = df G C H at hBdef
  change thetaC02 G C B ≤ 8 - 4 * (#F : ℤ) - df G C B at htheta
  have hFpos : 0 < #F := by
    obtain ⟨K, hK, hKH, _⟩ := high_contains_positive_core h hm hr hH hdH
    exact card_pos.mpr ⟨K, mem_coresIn.mpr ⟨hK, hKH⟩⟩
  have hO1 : #O = 1 := by
    by_contra hn
    have hO0 : #O = 0 := by omega
    have hBH : B = H := Subset.antisymm hBsub (sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp hO0))
    by_cases hF1 : #F = 1
    · obtain ⟨K, hFK⟩ := card_eq_one.mp hF1
      have hBF : B = K := by simp [B, hFK]
      have hKF : K ∈ F := hFK ▸ mem_singleton_self K
      have htK := (core_data (mem_coresIn.mp hKF).1).2.1
      rw [← hBH, hBF] at htH
      omega
    · change thetaC02 G C B ≤ 8 - 4 * (#F : ℤ) - df G C B at htheta
      change df G C B = df G C H at hBdef
      rw [hBH] at htheta
      omega
  obtain ⟨p, hOp⟩ := card_eq_one.mp hO1
  have hpO : p ∈ O := hOp ▸ mem_singleton_self p
  have hpH := (mem_sdiff.mp hpO).1
  have hpB := (mem_sdiff.mp hpO).2
  have hpord := high_outside_core_ordinary h hH hpO
  have hp6 := residual_ordinary_six h hm hr ((high_data h hH htH).1 hpH) hpord
  have hHB : H = insert p B := by
    have he := sdiff_union_of_subset hBsub
    change O ∪ B = H at he
    rw [hOp, singleton_union] at he
    exact he.symm
  have hF1 : #F = 1 := by
    have hi := theta_insert_upper (G := G) (C := C) hpB
    change thetaC02 G C B ≤ 8 - 4 * (#F : ℤ) - df G C B at htheta
    change df G C B = df G C H at hBdef
    rw [← hHB] at hi
    omega
  obtain ⟨K, hFK⟩ := card_eq_one.mp hF1
  have hBF : B = K := by simp [B, hFK]
  have hKF : K ∈ F := hFK ▸ mem_singleton_self K
  have hK := (mem_coresIn.mp hKF).1
  have hdf : df G C K = 1 := by
    have hd := core_loss_bound h hK
    change df G C B = df G C H at hBdef
    rw [hBF] at hBdef
    omega
  have hpK : p ∉ K := by rwa [hBF] at hpB
  have hHK : H = insert p K := by simpa [hBF] using hHB
  have hcan := core_insert_cpr h (core_data hK).1 (core_data hK).2.1 hpK
  have her : H.erase p = K := by rw [hHK]; exact erase_insert hpK
  have he := theta_erase (G := G) (C := C) hpH
  rw [her, hHK, hcan] at he
  rw [← hHK] at he
  have htK := (core_data hK).2.1
  exact ⟨K, hK, p, hdf, hpord, hpK, hHK, hp6, by omega⟩

end Erdos585.QB6C02MinFive

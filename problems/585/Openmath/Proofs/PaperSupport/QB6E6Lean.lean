import Openmath.Proofs.PaperSupport.QB6Assembly
import Openmath.Proofs.QB5.Block

/- 



-/

open Finset
namespace Erdos585.QB6E6
open QB4 QB5

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def scarDemand (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C T : Finset V) : ℤ :=
  4 * #T - ∑ c ∈ C, min ((dg G A c : ℤ) - 2) (dg G T c : ℤ)

def rowWeight (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : V → ℕ) (C : Finset V) (a : V) : ℤ :=
  3 * m a - 6 + dg G C a

theorem complement_scar_demand {A C T : Finset V} {m : V → ℕ}
    (hT : T ⊆ A) (hcard : #A = #C + 2)
    (hec : (ec G A C : ℤ) = 6 * #C - 1)
    (hm : msum m A = 5) :
    scarDemand G A C (A \ T) - msum m (A \ T) = thetaStar G m C T := by
  have hpoint : ∀ c ∈ C,
      min ((dg G A c : ℤ) - 2) (dg G (A \ T) c : ℤ) +
        max 0 ((dg G T c : ℤ) - 2) = (dg G A c : ℤ) - 2 := by
    intro c _
    have hsplit := dg_sdiff_add (G := G) hT c
    zify at hsplit
    rcases le_total (dg G T c : ℤ) 2 with h | h
    · rw [max_eq_left (by omega), min_eq_left (by omega)]
      omega
    · rw [max_eq_right (by omega), min_eq_right (by omega)]
      omega
  have hsum := sum_congr rfl hpoint
  rw [sum_add_distrib] at hsum
  have hdeg : (∑ c ∈ C, (dg G A c : ℤ)) = (ec G A C : ℤ) := by
    rw [ec_comm]
    simp [ec]
  have hcap : (∑ c ∈ C, ((dg G A c : ℤ) - 2)) = 4 * #C - 1 := by
    rw [sum_sub_distrib, hdeg, hec, sum_const, nsmul_eq_mul]
    ring
  have hms := msum_sdiff_add m hT
  have hcs := card_sdiff_add_card_eq_card hT
  zify at hcard hcs
  unfold scarDemand thetaStar
  linarith

theorem shifted_theta_bound {A C T J : Finset V} {m : V → ℕ}
    (hsp : ∀ S ⊆ A, ∀ K ⊆ C, 3 ≤ #S + #K → 14 ≤ gv G S K)
    (hT : T ⊆ A) (hJ : J ⊆ C) (h3 : 3 ≤ #T + #J) :
    3 * theta G m T J ≤
      2 * msum m T - wsum G m C T - (ec G T (C \ J) : ℤ) - 2 := by
  have hg := hsp T hT J hJ h3
  have h1 := two_mul_theta (G := G) m T J
  have h2 := theta_eq_four_add (G := G) m hJ T
  linarith

omit [DecidableEq V] in
theorem row_weight_sum (m : V → ℕ) (C T : Finset V) :
    2 * msum m T - wsum G m C T = ∑ a ∈ T, rowWeight G m C a := by
  calc
    2 * msum m T - wsum G m C T =
        ∑ a ∈ T, (2 * (m a : ℤ) - (6 - (dg G C a : ℤ) - m a)) := by
      simp [msum, wsum, mul_sum, sum_sub_distrib]
    _ = _ := sum_congr rfl fun a _ => by unfold rowWeight; ring

theorem forced_theta_nonpositive {A C : Finset V} {m : V → ℕ} {p : V}
    (hsp : ∀ S ⊆ A, ∀ K ⊆ C, 3 ≤ #S + #K → 14 ≤ gv G S K)
    (hmin : ∀ a ∈ A, 3 ≤ dg G C a)
    (hcap : ∀ a ∈ A, m a + dg G C a ≤ 6)
    (_hp : p ∈ A) (hdp : dg G C p = 3) (hmp : m p = 0)
    (hbudget : (∑ a ∈ A.erase p, max 0 (rowWeight G m C a)) ≤ 7)
    {T : Finset V} (hT : T ⊆ A) (hpT : p ∈ T) :
    thetaStar G m C T ≤ 0 := by
  have hweight : 2 * msum m T - wsum G m C T ≤ 4 := by
    rw [row_weight_sum]
    have hs := sum_erase_add T (rowWeight G m C) hpT
    have hpw : rowWeight G m C p = -3 := by simp [rowWeight, hmp, hdp]
    rw [hpw] at hs
    have hsub : T.erase p ⊆ A.erase p := fun a ha => by
      exact mem_erase.2 ⟨(mem_erase.1 ha).1, hT (mem_erase.1 ha).2⟩
    have hle : (∑ a ∈ T.erase p, rowWeight G m C a) ≤
        ∑ a ∈ A.erase p, max 0 (rowWeight G m C a) := by
      calc
        _ ≤ ∑ a ∈ T.erase p, max 0 (rowWeight G m C a) :=
          sum_le_sum fun a _ => le_max_right _ _
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun a _ _ => le_max_left _ _
    linarith
  by_cases h3 : 3 ≤ #T
  · have hb := shifted_theta_bound (m := m) hsp hT (cpr_subset (G := G) C T) (by omega)
    rw [theta_cpr] at hb
    have hn : (0 : ℤ) ≤ ec G T (C \ cpr G C T) := Nat.cast_nonneg _
    omega
  · have hpos : 1 ≤ #T := card_pos.2 ⟨p, hpT⟩
    rcases (by omega : #T = 1 ∨ #T = 2) with hc | hc
    · have heq : T = {p} := (eq_of_subset_of_card_le
        (singleton_subset_iff.2 hpT) (by simp [hc])).symm
      rw [heq, thetaStar_singleton, hmp]
      norm_num
    · rw [thetaStar_of_card_eq_two m C hc]
      have hms := sum_erase_add T (fun a => (m a : ℤ)) hpT
      have herase : #(T.erase p) = 1 := by rw [card_erase_of_mem hpT, hc]
      have hm3 : msum m (T.erase p) ≤ 3 := by
        calc
          _ ≤ ∑ _a ∈ T.erase p, (3 : ℤ) := sum_le_sum fun a ha => by
            have hmi := hmin a (hT (erase_subset p T ha))
            have hca := hcap a (hT (erase_subset p T ha))
            exact_mod_cast (by omega : m a ≤ 3)
          _ = 3 := by simp [herase]
      change msum m (T.erase p) + (m p : ℤ) = msum m T at hms
      rw [hmp] at hms
      omega

theorem forced_scar_supply {A C : Finset V} {m : V → ℕ} {p : V}
    (hcard : #A = #C + 2) (hec : (ec G A C : ℤ) = 6 * #C - 1)
    (hm : msum m A = 5)
    (hsp : ∀ S ⊆ A, ∀ K ⊆ C, 3 ≤ #S + #K → 14 ≤ gv G S K)
    (hmin : ∀ a ∈ A, 3 ≤ dg G C a)
    (hcap : ∀ a ∈ A, m a + dg G C a ≤ 6)
    (hp : p ∈ A) (hdp : dg G C p = 3) (hmp : m p = 0)
    (hbudget : (∑ a ∈ A.erase p, max 0 (rowWeight G m C a)) ≤ 7)
    {T : Finset V} (hT : T ⊆ A.erase p) :
    scarDemand G A C T ≤ msum m T := by
  have hTA : T ⊆ A := hT.trans (erase_subset p A)
  have hpnot : p ∉ T := fun h => (mem_erase.1 (hT h)).1 rfl
  have hpc : p ∈ A \ T := mem_sdiff.2 ⟨hp, hpnot⟩
  have htheta := forced_theta_nonpositive hsp hmin hcap hp hdp hmp hbudget
    (sdiff_subset (s := A) (t := T)) hpc
  have hid := complement_scar_demand (G := G) (sdiff_subset (s := A) (t := T))
    hcard hec hm
  rw [sdiff_sdiff_right_self, inf_eq_right.mpr hTA] at hid
  linarith

omit [DecidableEq V] in
theorem scar_demand_nat {A C T : Finset V}
    (hcol : ∀ c ∈ C, 2 ≤ dg G A c) :
    scarDemand G A C T =
      4 * (#T : ℤ) - ∑ c ∈ C, ((min (dg G A c - 2) (dg G T c) : ℕ) : ℤ) := by
  unfold scarDemand
  congr 1
  refine sum_congr rfl fun c hc => ?_
  have hd := hcol c hc
  have hcast : ((dg G A c - 2 : ℕ) : ℤ) = (dg G A c : ℤ) - 2 := by omega
  rw [← hcast, Nat.cast_min]

theorem forced_scar_supply_nat {A C : Finset V} {m : V → ℕ} {p : V}
    (hcard : #A = #C + 2) (hec : (ec G A C : ℤ) = 6 * #C - 1)
    (hscar : ∀ c ∈ C, 5 ≤ dg G A c ∧ dg G A c ≤ 6)
    (hm : msum m A = 5)
    (hsp : ∀ S ⊆ A, ∀ K ⊆ C, 3 ≤ #S + #K → 14 ≤ gv G S K)
    (hmin : ∀ a ∈ A, 3 ≤ dg G C a)
    (hcap : ∀ a ∈ A, m a + dg G C a ≤ 6)
    (hp : p ∈ A) (hdp : dg G C p = 3) (hmp : m p = 0)
    (hbudget : (∑ a ∈ A.erase p, max 0 (rowWeight G m C a)) ≤ 7)
    {T : Finset V} (hT : T ⊆ A.erase p) :
    4 * (#T : ℤ) - ∑ c ∈ C, ((min (dg G A c - 2) (dg G T c) : ℕ) : ℤ) ≤ msum m T := by
  rw [← scar_demand_nat (G := G) (fun c hc => (hscar c hc).1.trans' (by norm_num))]
  exact forced_scar_supply hcard hec hm hsp hmin hcap hp hdp hmp hbudget hT

theorem reverse_indicator_payment (b c : Bool) :
    (if c then (1 : ℤ) else 0) - (if b then 1 else 0) +
      (if b && !c then 1 else 0) ≥ 0 := by
  cases b <;> cases c <;> decide

theorem beta_petal_cost {q j e E m w : ℤ}
    (hq : 1 ≤ q) (hj : 0 ≤ j) (he0 : 0 ≤ e) (he : e ≤ q * j)
    (hw0 : 0 ≤ w) (hwq : w ≤ 2 * q)
    (hk0 : 0 ≤ q - j) (hk2 : q - j ≤ 2) (hwk : w ≤ 1 + 2 * (q - j))
    (htheta : m + 4 - 4 * q - 2 * j + e = 3 - E)
    (hsp : 3 ≤ q + j → 6 + (q - j) ≤ E + m) :
    3 * w ≤ 2 * (E + m) := by
  by_cases h3 : 3 ≤ q + j
  · have := hsp h3
    omega
  · have hq2 : q ≤ 2 := by omega
    have hj1 : j ≤ 1 := by omega
    interval_cases q <;> interval_cases j <;> omega

theorem beta_zero_nonsingle_slack {q j e E w : ℤ}
    (hq : 1 ≤ q) (hj : 0 ≤ j) (h2 : 2 ≤ q + j)
    (he0 : 0 ≤ e) (he : e ≤ q * j) (hw0 : 0 ≤ w) (hwq : w ≤ 2 * q)
    (hk0 : 0 ≤ q - j) (hk1 : q - j ≤ 1) (hwk : w ≤ 1 + 2 * (q - j))
    (htheta : 4 - 4 * q - 2 * j + e = 3 - E)
    (hsp : 3 ≤ q + j → 6 + (q - j) ≤ E) :
    3 * w + 5 ≤ 2 * E := by
  by_cases h3 : 3 ≤ q + j
  · have := hsp h3
    omega
  · have hq2 : q ≤ 2 := by omega
    have hj1 : j ≤ 1 := by omega
    interval_cases q <;> interval_cases j <;> omega

theorem delta_petal_cost {q j e E w wK : ℤ}
    (hq : 1 ≤ q) (hj : 0 ≤ j) (he0 : 0 ≤ e) (he : e ≤ q * j)
    (hw0 : 0 ≤ w) (hwK : 0 ≤ wK) (hwq : w ≤ 2 * q)
    (hkm : -1 ≤ q - j) (hkp : q - j ≤ 1) (hwk : w ≤ 3 + 2 * (q - j) - wK)
    (htheta : 4 - 4 * q - 2 * j + e = 3 - E)
    (hsp : 3 ≤ q + j → 6 + (q - j) ≤ E) : w + 1 ≤ E := by
  by_cases h3 : 3 ≤ q + j
  · have := hsp h3
    omega
  · have hq2 : q ≤ 2 := by omega
    have hj1 : j ≤ 1 := by omega
    interval_cases q <;> interval_cases j <;> omega

theorem delta_budget_false {wK wPet E r n : ℤ}
    (hr : 2 ≤ r) (hn : 0 ≤ n) (hwhole : wK + wPet = 8)
    (hcost : wPet + r ≤ E) (hboundary : E ≤ 9 - wK - n) : False := by omega

end Erdos585.QB6E6

/- 

-/

open Finset
namespace Erdos585.QB6E6Lean
open QB4 QB5 QB6Assembly QB6E6
universe u
set_option maxHeartbeats 1000000
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The physical five-edge supply inequality, with no graph selection assumed. -/
theorem card_supply_five (M : Finset (V × V))
    (hMadj : ∀ e ∈ M, G.Adj e.1 e.2) (hM5 : #M ≤ 5) (T S : Finset V) :
    #{e ∈ M | e.1 ∈ T} + #{e ∈ M | e.2 ∈ S} ≤ 5 + ec G T S := by
  have hu : #({e ∈ M | e.1 ∈ T} ∪ {e ∈ M | e.2 ∈ S}) ≤ 5 :=
    (card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))).trans hM5
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

/-- Scar capacity is exactly four minus the actual reverse degree. -/
theorem scar_capacity_eq {P A C K : Finset V} (hA : A ⊆ P)
    (hsat : ∀ c ∈ C, dg G P c = 6) (hK : K ⊆ C) :
    (∑ c ∈ K, ((dg G A c : ℤ) - 2)) = 4 * #K - ec G (P \ A) K := by
  have hp : ∀ c ∈ K,
      (dg G A c : ℤ) - 2 = 4 - (dg G (P \ A) c : ℤ) := by
    intro c hc
    have hsplit := dg_sdiff_add (G := G) hA c
    have h6 := hsat c (hK hc)
    omega
  rw [sum_congr rfl hp, sum_sub_distrib, sum_const, nsmul_eq_mul, ec_comm]
  simp [ec, mul_comm]

/-- The first Hall bracket retains the actual reverse loss on its small shore. -/
theorem sum_min_scar_left {P A C : Finset V} (hA : A ⊆ P)
    (hsat : ∀ c ∈ C, dg G P c = 6) (T Z : Finset V) :
    (∑ c ∈ C, min ((dg G A c : ℤ) - 2) (dg G T c : ℤ)) ≤
      (ec G T (C \ Z) : ℤ) + 4 * #(C ∩ Z) - ec G (P \ A) (C ∩ Z) := by
  rw [← sum_inter_add_sum_sdiff C Z]
  have h1 : (∑ c ∈ C ∩ Z, min ((dg G A c : ℤ) - 2) (dg G T c : ℤ)) ≤
      ∑ c ∈ C ∩ Z, ((dg G A c : ℤ) - 2) :=
    sum_le_sum fun _ _ => min_le_left _ _
  rw [scar_capacity_eq hA hsat inter_subset_left] at h1
  have h2 : (∑ c ∈ C \ Z, min ((dg G A c : ℤ) - 2) (dg G T c : ℤ)) ≤
      ∑ c ∈ C \ Z, (dg G T c : ℤ) := sum_le_sum fun _ _ => min_le_right _ _
  have he : (∑ c ∈ C \ Z, (dg G T c : ℤ)) = (ec G T (C \ Z) : ℤ) := by
    rw [ec_comm]
    simp [ec]
  rw [he] at h2
  linarith

/-- The second bracket is valid for literal internal degree-minus-two capacities. -/
theorem sum_min_scar_right {D B B1 : Finset V} (hB1 : B1 ⊆ B) (S : Finset V) :
    (∑ b ∈ B, min ((dg G D b : ℤ) - 2) (dg G S b : ℤ)) -
        (∑ b ∈ B, ((dg G D b : ℤ) - 2)) ≤
      (ec G B1 S : ℤ) - (∑ b ∈ B1, ((dg G D b : ℤ) - 2)) := by
  have hsplit := sum_sdiff
    (f := fun b => min ((dg G D b : ℤ) - 2) (dg G S b : ℤ) - ((dg G D b : ℤ) - 2)) hB1
  have h1 : (∑ b ∈ B \ B1,
      (min ((dg G D b : ℤ) - 2) (dg G S b : ℤ) - ((dg G D b : ℤ) - 2))) ≤ 0 :=
    sum_nonpos fun _ _ => sub_nonpos.mpr (min_le_left _ _)
  have h2 : (∑ b ∈ B1,
      (min ((dg G D b : ℤ) - 2) (dg G S b : ℤ) - ((dg G D b : ℤ) - 2))) ≤
      (∑ b ∈ B1, ((dg G S b : ℤ) - ((dg G D b : ℤ) - 2))) :=
    sum_le_sum fun _ _ => sub_le_sub_right (min_le_right _ _) _
  have he : (∑ b ∈ B1, (dg G S b : ℤ)) = (ec G B1 S : ℤ) := by simp [ec]
  simp only [sum_sub_distrib] at hsplit h1 h2 ⊢
  rw [he] at h2
  linarith

/-- Actual reverse edges pay the loss across every physical cut. -/
theorem reverse_set_payment {B B1 C : Finset V} (hB1 : B1 ⊆ B) (Z : Finset V) :
    ec G B1 C ≤ ec G B (C ∩ Z) + ec G B1 (C \ Z) := by
  have hs := ec_sdiff_add_right (G := G) (inter_subset_left : C ∩ Z ⊆ C) B1
  rw [sdiff_inter_self_left] at hs
  have hm := ec_mono_left (G := G) hB1 (C ∩ Z)
  omega

/-- Full physical Hall coupling with five forward supply edges and one reverse edge. -/
theorem cut_condition_of_scar_pair {P Q A C : Finset V} (hA : A ⊆ P) (hC : C ⊆ Q)
    (hcardB : #(Q \ C) = #(P \ A) + 2)
    (hsatC : ∀ c ∈ C, dg G P c = 6) (hsatB : ∀ b ∈ P \ A, dg G Q b = 6)
    (hreverse : ec G (P \ A) C = 1)
    (M : Finset (V × V)) (hMadj : ∀ e ∈ M, G.Adj e.1 e.2) (hM5 : #M ≤ 5)
    {p q : V} (hq : q ∈ Q \ C)
    (hX : ∀ T ⊆ A.erase p, scarDemand G A C T ≤ (#{e ∈ M | e.1 ∈ T} : ℤ))
    (hY : ∀ S ⊆ (Q \ C).erase q,
      scarDemand G (Q \ C) (P \ A) S ≤ (#{e ∈ M | e.2 ∈ S} : ℤ)) :
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
  norm_num only [Nat.cast_one] at hcap2
  have hsup := card_supply_five M hMadj hM5 A1 D1
  have hrev := reverse_set_payment (G := G) (C := C) hB1 Z
  have hdX := hX A1 hA1
  have hdY := hY D1 hD1
  rw [inter_comm] at hcap1 hrev
  unfold scarDemand at hdX hdY
  zify at hec hcX hcZ hcD hcardB hsup hrev ⊢
  linarith

/-- The paid coupling produces an actual quartic once the two literal supplies exist. -/
theorem quartic_of_scar_supplies {P Q A C : Finset V} (h : E6Input G P Q A C)
    (M : Finset (V × V)) (hMadj : ∀ e ∈ M, G.Adj e.1 e.2) (hM5 : #M ≤ 5)
    {p q : V} (hp : p ∈ A) (hq : q ∈ Q \ C)
    (hX : ∀ T ⊆ A.erase p, scarDemand G A C T ≤ (#{e ∈ M | e.1 ∈ T} : ℤ))
    (hY : ∀ S ⊆ (Q \ C).erase q,
      scarDemand G (Q \ C) (P \ A) S ≤ (#{e ∈ M | e.2 ∈ S} : ℤ)) :
    Quartic G P Q := by
  have hpP := h.subsetA hp
  have hqQ := sdiff_subset hq
  have hcard : #(P.erase p) = #(Q.erase q) := by
    have hcP := card_erase_add_one hpP
    have hcQ := card_erase_add_one hqQ
    have := h.balanced
    omega
  have hcut := cut_condition_of_scar_pair h.subsetA h.subsetC h.cardRight h.satC h.satB
    h.reverse M hMadj hM5 hq hX hY
  obtain ⟨F, hF, hadj, hFP, hFQ⟩ := exists_four_factor _ _ hcard hcut
  have hPne : (P.erase p).Nonempty := by
    have hs := h.six_le_A
    have hA := card_le_card h.subsetA
    have hc := card_erase_add_one hpP
    exact card_pos.mp (by omega)
  have hQne : (Q.erase q).Nonempty := card_pos.mp (by rw [← hcard]; exact card_pos.mpr hPne)
  exact (quartic_of_four_factor (G := G) Subset.rfl hQne hF hadj hFP hFQ).swap.mono
    (erase_subset _ _) (erase_subset _ _)

/-- Literal scarred block data; every field is physical. -/
structure ScarBlock (G : SimpleGraph V) [DecidableRel G.Adj] (A C : Finset V) : Prop where
  disjoint : Disjoint A C
  card : #A = #C + 2
  six : 6 ≤ #A
  scar : ∀ c ∈ C, 5 ≤ dg G A c ∧ dg G A c ≤ 6
  edges : (ec G A C : ℤ) = 6 * #C - 1
  minA : ∀ a ∈ A, 3 ≤ dg G C a
  capA : ∀ a ∈ A, dg G C a ≤ 6
  sparse : ∀ T ⊆ A, ∀ J ⊆ C, 3 ≤ #T + #J → 14 ≤ gv G T J

/-- Assumed covered KL5 producer. It contains no factor or deletion input. -/
def CoveredFiveSupply : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V), ScarBlock G A C → ∀ m : V → ℕ, msum m A = 5 →
      (∀ a ∈ A, m a + dg G C a ≤ 6) → (∀ a ∈ A, 4 ≤ dg G C a + m a) →
        ∃ p ∈ A, m p = 0 ∧ ∀ T ⊆ A.erase p, scarDemand G A C T ≤ msum m T

/-- Physical usability is coverage or one literal low row with a weight budget. -/
def UsableFive (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V) (m : V → ℕ) : Prop :=
  (∀ a ∈ A, dg G C a = 3 → 0 < m a) ∨
    ∃ p ∈ A, dg G C p = 3 ∧ m p = 0 ∧
      (∀ a ∈ A, dg G C a = 3 → m a = 0 → a = p) ∧
        (∑ a ∈ A.erase p, max 0 (rowWeight G m C a)) ≤ 7

/-- Multiplicity counts the literal members of an actual finite pair set. -/
def mult (M : Finset (V × V)) (r : V × V → V) (v : V) : ℕ := #{e ∈ M | r e = v}

/-- Assumed actual seven-to-five support choice; no desired demand is supplied. -/
def ActualFiveSelection : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P Q A C : Finset V), E6Input G P Q A C →
      ∃ M : Finset (V × V), M ⊆ adjPairs G A (Q \ C) ∧ #M = 5 ∧
        UsableFive G A C (mult M Prod.fst) ∧
        UsableFive G (Q \ C) (P \ A) (mult M Prod.snd)

/-- The credited QB5 finite-fiber count for actual endpoint multiplicities. -/
theorem sum_mult_eq (M : Finset (V × V)) (r : V × V → V) (T : Finset V) :
    (∑ v ∈ T, mult M r v) = #{e ∈ M | r e ∈ T} := by
  have h := card_eq_sum_card_fiberwise (s := {e ∈ M | r e ∈ T}) (t := T) (f := r)
    (fun e he => (mem_filter.1 he).2)
  rw [h]
  refine sum_congr rfl fun v hv => ?_
  unfold mult
  rw [filter_filter]
  refine congrArg card (filter_congr fun e _ => ?_)
  constructor
  · intro h
    exact ⟨h ▸ hv, h⟩
  · exact fun h => h.2

theorem msum_mult_eq (M : Finset (V × V)) (r : V × V → V) (T : Finset V) :
    msum (mult M r) T = (#{e ∈ M | r e ∈ T} : ℤ) := by
  unfold msum
  exact_mod_cast sum_mult_eq M r T

theorem mult_fst_le_degree {A D : Finset V} {M : Finset (V × V)}
    (hM : M ⊆ adjPairs G A D) (a : V) : mult M Prod.fst a ≤ dg G D a := by
  calc
    _ ≤ #(adjPairs G {a} D) := by
      apply card_le_card
      intro e he
      obtain ⟨heM, hea⟩ := mem_filter.1 he
      obtain ⟨heAD, hadj⟩ := mem_filter.1 (hM heM)
      exact mem_filter.2 ⟨mem_product.2 ⟨mem_singleton.2 hea, (mem_product.1 heAD).2⟩, hadj⟩
    _ = dg G D a := by rw [card_adjPairs]; simp [ec]

theorem mult_snd_le_degree {A D : Finset V} {M : Finset (V × V)}
    (hM : M ⊆ adjPairs G A D) (d : V) : mult M Prod.snd d ≤ dg G A d := by
  calc
    _ ≤ #(adjPairs G A {d}) := by
      apply card_le_card
      intro e he
      obtain ⟨heM, hed⟩ := mem_filter.1 he
      obtain ⟨heAD, hadj⟩ := mem_filter.1 (hM heM)
      exact mem_filter.2 ⟨mem_product.2 ⟨(mem_product.1 heAD).1, mem_singleton.2 hed⟩, hadj⟩
    _ = dg G A d := by rw [card_adjPairs, ec_comm]; simp [ec]

theorem scarBlock_left {P Q A C : Finset V} (h : E6Input G P Q A C) : ScarBlock G A C := by
  refine ⟨disjoint_of_subset_left h.subsetA (disjoint_of_subset_right h.subsetC h.disjoint),
    h.cardLeft, h.six_le_A, ?_, ?_, h.internalMinA, h.capInternalA, h.sparseLeft⟩
  · intro c hc
    have hd := h.smallDegreeLeft c hc
    constructor <;> omega
  · have hz := h.smallDefLeft
    have he := df_eq (G := G) A C
    have hc := ec_comm (G := G) C A
    omega

theorem scarBlock_right {P Q A C : Finset V} (h : E6Input G P Q A C) :
    ScarBlock G (Q \ C) (P \ A) := by
  refine ⟨disjoint_of_subset_left sdiff_subset
    (disjoint_of_subset_right sdiff_subset h.disjoint.symm),
    h.cardRight, h.six_le_D, ?_, ?_, h.internalMinD, h.capInternalD, h.sparseRight⟩
  · intro b hb
    have hd := h.smallDegreeRight b hb
    constructor <;> omega
  · have hz := h.smallDefRight
    have he := df_eq (G := G) (Q \ C) (P \ A)
    have hc := ec_comm (G := G) (P \ A) (Q \ C)
    omega

/-- Usability supplies demands through covered KL5 or the already paid forced branch. -/
theorem supply_of_usable (cover : CoveredFiveSupply.{u})
    {A C : Finset V} (h : ScarBlock G A C) {m : V → ℕ} (hm : msum m A = 5)
    (hcap : ∀ a ∈ A, m a + dg G C a ≤ 6) (hu : UsableFive G A C m) :
    ∃ p ∈ A, m p = 0 ∧ ∀ T ⊆ A.erase p, scarDemand G A C T ≤ msum m T := by
  rcases hu with hc | ⟨p, hp, hd, hmp, _, hb⟩
  · apply cover G A C h m hm hcap
    intro a ha
    have hmin := h.minA a ha
    by_cases hd : dg G C a = 3
    · have hp := hc a ha hd
      omega
    · omega
  · exact ⟨p, hp, hmp, fun T hT =>
      forced_scar_supply h.card h.edges hm h.sparse h.minA hcap hp hd hmp hb hT⟩

/-- Exact conditional endpoint. Its two physical producers remain explicit assumptions. -/
theorem e6_of_physical_producers (cover : CoveredFiveSupply.{u})
    (choose : ActualFiveSelection.{u}) : E6Repair.{u} := by
  intro V _ G _ P Q A C h
  obtain ⟨M, hM, hM5, hL, hR⟩ := choose G P Q A C h
  have hMadj : ∀ e ∈ M, G.Adj e.1 e.2 := fun e he => (mem_filter.1 (hM he)).2
  have hmL : msum (mult M Prod.fst) A = 5 := by
    rw [msum_mult_eq]
    have hf : {e ∈ M | e.1 ∈ A} = M := filter_eq_self.mpr fun e he =>
      (mem_product.1 (mem_filter.1 (hM he)).1).1
    rw [hf, hM5]
    norm_num
  have hmR : msum (mult M Prod.snd) (Q \ C) = 5 := by
    rw [msum_mult_eq]
    have hf : {e ∈ M | e.2 ∈ Q \ C} = M := filter_eq_self.mpr fun e he =>
      (mem_product.1 (mem_filter.1 (hM he)).1).2
    rw [hf, hM5]
    norm_num
  have hcapL : ∀ a ∈ A, mult M Prod.fst a + dg G C a ≤ 6 := by
    intro a ha
    have hm := mult_fst_le_degree hM a
    have hs := dg_sdiff_add (G := G) h.subsetC a
    have hd := h.capP a (h.subsetA ha)
    omega
  have hcapR : ∀ d ∈ Q \ C, mult M Prod.snd d + dg G (P \ A) d ≤ 6 := by
    intro d hd
    have hm := mult_snd_le_degree hM d
    have hs := dg_sdiff_add (G := G) h.subsetA d
    have hb := h.capQ d (sdiff_subset hd)
    omega
  obtain ⟨p, hp, _, hX⟩ := supply_of_usable cover (scarBlock_left h) hmL hcapL hL
  obtain ⟨q, hq, _, hY⟩ := supply_of_usable cover (scarBlock_right h) hmR hcapR hR
  apply quartic_of_scar_supplies h M hMadj (by omega) hp hq
  · intro T hT
    simpa only [msum_mult_eq] using hX T hT
  · intro S hS
    simpa only [msum_mult_eq] using hY S hS

/-- Actual forward endpoints meet the degree and mark requirements on the left. -/
theorem forward_degrees_left {P Q A C : Finset V} (h : E6Input G P Q A C) :
    ∀ a ∈ A, dg G (Q \ C) a ≤ 3 ∧
      (dg G C a = 3 → 0 < dg G (Q \ C) a) ∧
      (dg G (Q \ C) a = 3 → dg G C a = 3) := by
  intro a ha
  have hs := dg_sdiff_add (G := G) h.subsetC a
  have hi := h.internalMinA a ha
  have hlo := h.minP a (h.subsetA ha)
  have hhi := h.capP a (h.subsetA ha)
  omega

theorem forward_degrees_right {P Q A C : Finset V} (h : E6Input G P Q A C) :
    ∀ d ∈ Q \ C, dg G A d ≤ 3 ∧
      (dg G (P \ A) d = 3 → 0 < dg G A d) ∧
      (dg G A d = 3 → dg G (P \ A) d = 3) := by
  intro d hd
  have hs := dg_sdiff_add (G := G) h.subsetA d
  have hi := h.internalMinD d hd
  have hlo := h.minQ d (sdiff_subset hd)
  have hhi := h.capQ d (sdiff_subset hd)
  omega

/-- The actual marked leaf/degree-two cost is paid by ambient deficiency six. -/
theorem marked_cost_left {P Q A C : Finset V} (h : E6Input G P Q A C) :
    (∑ a ∈ {a ∈ A | dg G C a = 3}, (3 - (dg G (Q \ C) a : ℤ))) ≤ 6 := by
  let L := {a ∈ A | dg G C a = 3}
  have hLA : L ⊆ A := filter_subset _ _
  have hid : (∑ a ∈ L, (3 - (dg G (Q \ C) a : ℤ))) = df G Q L := by
    unfold df
    refine sum_congr rfl fun a ha => ?_
    have hs := dg_sdiff_add (G := G) h.subsetC a
    have hi := (mem_filter.mp ha).2
    omega
  change (∑ a ∈ L, (3 - (dg G (Q \ C) a : ℤ))) ≤ 6
  rw [hid]
  have hb := df_le_of_subset (G := G) (S := Q) (hLA.trans h.subsetA) h.capP
  rw [h.defP] at hb
  exact hb

theorem marked_cost_right {P Q A C : Finset V} (h : E6Input G P Q A C) :
    (∑ d ∈ {d ∈ Q \ C | dg G (P \ A) d = 3}, (3 - (dg G A d : ℤ))) ≤ 6 := by
  let L := {d ∈ Q \ C | dg G (P \ A) d = 3}
  have hLD : L ⊆ Q \ C := filter_subset _ _
  have hid : (∑ d ∈ L, (3 - (dg G A d : ℤ))) = df G P L := by
    unfold df
    refine sum_congr rfl fun d hd => ?_
    have hs := dg_sdiff_add (G := G) h.subsetA d
    have hi := (mem_filter.mp hd).2
    omega
  change (∑ d ∈ L, (3 - (dg G A d : ℤ))) ≤ 6
  rw [hid]
  have hb := df_le_of_subset (G := G) (S := P) (hLD.trans sdiff_subset) h.capQ
  rw [h.defQ] at hb
  exact hb

#print axioms Erdos585.QB6E6.complement_scar_demand
#print axioms Erdos585.QB6E6.shifted_theta_bound
#print axioms Erdos585.QB6E6.row_weight_sum
#print axioms Erdos585.QB6E6.forced_theta_nonpositive
#print axioms Erdos585.QB6E6.forced_scar_supply
#print axioms Erdos585.QB6E6.scar_demand_nat
#print axioms Erdos585.QB6E6.forced_scar_supply_nat
#print axioms Erdos585.QB6E6.reverse_indicator_payment
#print axioms Erdos585.QB6E6.beta_petal_cost
#print axioms Erdos585.QB6E6.beta_zero_nonsingle_slack
#print axioms Erdos585.QB6E6.delta_petal_cost
#print axioms Erdos585.QB6E6.delta_budget_false
#print axioms card_supply_five
#print axioms scar_capacity_eq
#print axioms sum_min_scar_left
#print axioms sum_min_scar_right
#print axioms reverse_set_payment
#print axioms cut_condition_of_scar_pair
#print axioms quartic_of_scar_supplies
#print axioms sum_mult_eq
#print axioms msum_mult_eq
#print axioms mult_fst_le_degree
#print axioms mult_snd_le_degree
#print axioms scarBlock_left
#print axioms scarBlock_right
#print axioms supply_of_usable
#print axioms e6_of_physical_producers
#print axioms forward_degrees_left
#print axioms forward_degrees_right
#print axioms marked_cost_left
#print axioms marked_cost_right
#check quartic_of_scar_supplies
#check e6_of_physical_producers
#print CoveredFiveSupply
#print ScarBlock
#print ActualFiveSelection
#print UsableFive
#print mult
#print E6Repair
#print E6Input
#print Sparse6
#print scarDemand
#print rowWeight
#print Erdos585.QB4.adjPairs
#print Erdos585.QB4.Quartic
#print Erdos585.QB4.dg
#print Erdos585.QB4.ec
#print Erdos585.QB4.gv
#print Erdos585.QB4.df
#print Erdos585.QB5.msum

end Erdos585.QB6E6Lean

import Erdos1017.BinomialSelector

namespace Erdos1017.Binomial
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem clique_support_partition (G : SimpleGraph V) (w : V → ℕ) (t : ℕ)
    (ht : 2 ≤ t) (hc : G.IsClique (support w : Set V)) :
    ∃ P : Partition G w t, P.cost ≤ maximumCost (∑ i,w i) t := by
  classical
  by_cases hz : ∀ i,w i=0
  · let P : Partition G w t := {
      mass := fun _ => 0
      nonneg := fun _ => le_rfl
      supported := fun _ h => (h rfl).elim
      load := fun B _ hB => by simp [subsetMoment,hz,hB,show t ≠ 0 by omega] }
    refine ⟨P,?_⟩
    simp [Partition.cost,P,hz,maximumCost_zero]
  · obtain ⟨v,hv⟩ := not_forall.mp hz
    obtain ⟨r,_,hr⟩ := Finset.exists_max_image Finset.univ w ⟨v,Finset.mem_univ v⟩
    have haN : 0 < w r := lt_of_lt_of_le (Nat.pos_of_ne_zero hv) (hr v (Finset.mem_univ v))
    let a : ℝ := w r
    have ha : 0 < a := by dsimp [a]; exact_mod_cast haN
    let p : V → ℝ := fun i => w i/a
    let m : (V → Bool) → ℝ := fun b => a^t*selectorMass p b
    have hp0 (i : V) : 0 ≤ p i := div_nonneg (Nat.cast_nonneg _) ha.le
    have hp1 (i : V) : p i ≤ 1 := (div_le_one ha).mpr (by dsimp [a]; exact_mod_cast hr i (Finset.mem_univ i))
    have hm (b : V → Bool) : 0 ≤ m b := mul_nonneg (pow_nonneg ha.le _) (selectorMass_nonneg p hp0 hp1 b)
    have hselected (b : V → Bool) (hb : m b ≠ 0) : selected b ⊆ support w := by
      intro i hi
      have hi' : b i=true := by simpa [selected] using hi
      have hw : w i ≠ 0 := by
        intro hzero
        have hpz : selectorMass p b=0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ i)
          simp [p,hzero,hi']
        exact hb (by simp [m,hpz])
      simp [support,Nat.pos_of_ne_zero hw]
    have hroot (b : V → Bool) (hb : m b ≠ 0) : r ∈ selected b := by
      have hpone : p r=1 := by dsimp [p,a]; exact div_self (ne_of_gt ha)
      by_contra hn
      have hrb : b r=false := by simpa [selected] using hn
      have hpz : selectorMass p b=0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ r)
        simp [hrb,hpone]
      exact hb (by simp [m,hpz])
    let P : Partition G w t := {
      mass := aggregateMass selected m
      nonneg := aggregateMass_nonneg selected m hm
      supported := fun S h => by
        obtain ⟨b,_,hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
        by_cases he : selected b=S
        · have hb' : m b ≠ 0 := by simpa [he] using hb
          rw [← he]
          exact fun i hi j hj hij => hc (hselected b hb' hi) (hselected b hb' hj) hij
        · simp [he] at hb
      load := fun B _ hB => by
        have h := aggregate_observable selected m (fun S => if B ⊆ S then (1:ℝ) else 0)
        simp only [mul_ite,mul_one,mul_zero] at h
        change subsetMoment (aggregateMass selected m) B=_
        unfold subsetMoment
        rw [h]
        change (∑ b : V → Bool,if B ⊆ selected b then a^t*selectorMass (fun i => w i/a) b else 0)=_
        rw [scaled_selector_moment w a (ne_of_gt ha),hB]
        field_simp }
    have hcost : P.cost=a*(elementary w (Finset.univ.erase r) (t-1) : ℝ) := by
      have hp := aggregate_observable selected m (cliqueCost t)
      change (∑ S,aggregateMass selected m S*cliqueCost t S)=_
      rw [hp]
      have he (b : V → Bool) : m b*cliqueCost t (selected b)=
          ∑ B ∈ (Finset.univ.erase r).powersetCard (t-1),if B ⊆ selected b then m b else 0 := by
        by_cases hb : m b=0
        · simp [hb]
        · have hrb := hroot b hb
          have hcard := Finset.card_erase_of_mem hrb
          unfold cliqueCost
          rw [← hcard,count_subsets_erase,Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro B _
          split_ifs <;> simp
      simp_rw [he]
      rw [Finset.sum_comm]
      have hmoment (B : Finset V) (hB : B ∈ (Finset.univ.erase r).powersetCard (t-1)) :
          (∑ b : V → Bool,if B ⊆ selected b then m b else 0)=a*(∏ i ∈ B,(w i : ℝ)) := by
        have hcard := (Finset.mem_powersetCard.mp hB).2
        change (∑ b : V → Bool,if B ⊆ selected b then a^t*selectorMass (fun i => w i/a) b else 0)=_
        rw [scaled_selector_moment w a (ne_of_gt ha),hcard]
        have ht' : t=(t-1)+1 := by omega
        rw [show a^t=a^(t-1)*a by rw [← pow_succ,← ht']]
        field_simp
        <;> ring
      simp only [elementary,Nat.cast_sum,Nat.cast_prod]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hmoment
    refine ⟨P,?_⟩
    rw [hcost]
    have hs : (∑ i ∈ Finset.univ.erase r,w i)=(∑ i,w i)-w r := by
      have he := Finset.sum_erase_add Finset.univ w (Finset.mem_univ r)
      omega
    have hle : w r ≤ ∑ i,w i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
    have hb := Nat.mul_le_mul_left (w r) (elementary_le_choose w (Finset.univ.erase r) (t-1))
    rw [hs] at hb
    have hfinal := hb.trans (le_maximumCost (∑ i,w i) t (w r) hle)
    dsimp [a]
    exact_mod_cast hfinal

/-- Full all-graph upper bound with exact load on every original t-clique. -/
theorem graph_upper (G : SimpleGraph V) (t : ℕ) (ht : 2 ≤ t) :
    ∃ P : Partition G (fun _ => 1) t, P.cost ≤ maximumCost (Fintype.card V) t := by
  have h := reduce_to_clique_support G t (fun n => (maximumCost n t : ℝ))
    (fun w hc => clique_support_partition G w t ht hc) (fun _ => 1)
  simpa using h

end Erdos1017.Binomial

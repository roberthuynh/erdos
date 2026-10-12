import L17HCq.Seed
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
open Finset SimpleGraph BqLowerFamily
namespace Erdos585.L17HCq

theorem core_column_card (q : ℕ) (hq : 5 ≤ q) (j : Fin (q+3)) :
    columnDegree (coreAdj q) univ j = q+1-(if j.val<6 then 1 else 0) := by
  by_cases h0 : j.val=0
  · have hs : univ.filter (fun i => coreAdj q i j)=
        univ.erase (⟨0,by omega⟩:Fin (q+1)) := by
      ext i;simp [coreAdj,Fin.ext_iff,-Fin.val_eq_zero_iff,h0]
    unfold columnDegree
    rw [hs,card_erase_of_mem (by simp),card_univ,Fintype.card_fin]
    simp [h0]
  by_cases h1 : j.val=1
  · have hs : univ.filter (fun i => coreAdj q i j)=
        univ.erase (⟨0,by omega⟩:Fin (q+1)) := by
      ext i;simp [coreAdj,Fin.ext_iff,-Fin.val_eq_zero_iff,h1]
    unfold columnDegree
    rw [hs,card_erase_of_mem (by simp),card_univ,Fintype.card_fin]
    simp [h1]
  by_cases h2 : j.val=2
  · have hs : univ.filter (fun i => coreAdj q i j)=
        univ.erase (⟨1,by omega⟩:Fin (q+1)) := by
      ext i;simp [coreAdj,Fin.ext_iff,-Fin.val_eq_zero_iff,h2]
    unfold columnDegree
    rw [hs,card_erase_of_mem (by simp),card_univ,Fintype.card_fin]
    simp [h2]
  by_cases h3 : j.val=3
  · have hs : univ.filter (fun i => coreAdj q i j)=
        univ.erase (⟨1,by omega⟩:Fin (q+1)) := by
      ext i;simp [coreAdj,Fin.ext_iff,-Fin.val_eq_zero_iff,h3]
    unfold columnDegree
    rw [hs,card_erase_of_mem (by simp),card_univ,Fintype.card_fin]
    simp [h3]
  by_cases h4 : j.val=4
  · have hs : univ.filter (fun i => coreAdj q i j)=
        univ.erase (⟨2,by omega⟩:Fin (q+1)) := by
      ext i;simp [coreAdj,Fin.ext_iff,-Fin.val_eq_zero_iff,h4]
    unfold columnDegree
    rw [hs,card_erase_of_mem (by simp),card_univ,Fintype.card_fin]
    simp [h4]
  by_cases h5 : j.val=5
  · have hs : univ.filter (fun i => coreAdj q i j)=
        univ.erase (⟨2,by omega⟩:Fin (q+1)) := by
      ext i;simp [coreAdj,Fin.ext_iff,-Fin.val_eq_zero_iff,h5]
    unfold columnDegree
    rw [hs,card_erase_of_mem (by simp),card_univ,Fintype.card_fin]
    simp [h5]
  · have hs : univ.filter (fun i => coreAdj q i j)=univ := by
      ext i;simp [coreAdj,h0,h1,h2,h3,h4,h5]
    have hi : ¬ j.val<6 := by omega
    simp [columnDegree,hs,hi]

theorem seed_row_base (q : ℕ) (i : Fin (q+1)) :
    rowDegree (seedRel q) univ (.inl i)=rowDegree (coreAdj q) univ i+
      (if i.val<q-2 then 1 else 0) := by
  unfold rowDegree
  rw [card_filter_sum]
  by_cases hi : i.val<q-2 <;> simp [seedRel,hi]

theorem seed_column_ordinary (q : ℕ) (j : Fin (q+3)) :
    columnDegree (seedRel q) univ (.inl j)=columnDegree (coreAdj q) univ j+
      (univ.filter fun a : Fin 2 => seedRel q (.inr a) (.inl j)).card := by
  unfold columnDegree
  rw [card_filter_sum]
  rfl

theorem sum_core_rows (q : ℕ) (hq : 5 ≤ q) :
    (∑ i : Fin (q+1),rowDegree (coreAdj q) univ i)+6=(q+1)*(q+3) := by
  have hlt : (univ.filter fun i : Fin (q+1) => i.val<3).card=3 := by
    rw [fin_lt_card,Nat.min_eq_right (by omega)]
  have hge : (univ.filter fun i : Fin (q+1) => 3 ≤ i.val).card=q-2 := by
    rw [fin_ge_card,Nat.min_eq_right (by omega)];omega
  have hs : (∑ i : Fin (q+1),rowDegree (coreAdj q) univ i)=
      (q+1)*3+(q+3)*(q-2) := by
    simp_rw [core_row_card q hq]
    rw [sum_ite]
    simp [hlt,hge,mul_comm]
  rw [hs]
  have hp : q-2+2=q := by omega
  nlinarith

theorem sum_seed_rows (q : ℕ) (hq : 5 ≤ q) :
    (∑ i : SeedLeft q,rowDegree (seedRel q) univ i)+5=q*q+7*q := by
  rw [Fintype.sum_sum_type,Fin.sum_univ_two,seed_row_f q hq,seed_row_g q hq]
  simp_rw [seed_row_base]
  rw [sum_add_distrib]
  have hind : (∑ i : Fin (q+1),if i.val<q-2 then 1 else 0)=q-2 := by
    rw [← card_filter]
    rw [fin_lt_card,Nat.min_eq_right (by omega)]
  rw [hind]
  have hs := sum_core_rows q hq
  have hp : q-2+2=q := by omega
  nlinarith

theorem cross_edge_count {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (R : A → B → Prop) [∀ i j,Decidable (R i j)] :
    (crossGraph R).edgeFinset.card=∑ i : A,rowDegree R univ i := by
  have h := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges (cross_bipartite R)
  rw [sum_image (fun _ _ _ _ hh => Sum.inl_injective hh)] at h
  simp_rw [cross_degree_left R (crossGraph R) le_rfl] at h
  exact h.symm

theorem hcq_seed_edge_count (q : ℕ) (hq : 5 ≤ q) :
    (hcqSeedGraph q).edgeFinset.card+5=q*q+7*q := by
  change (crossGraph (seedRel q)).edgeFinset.card+5=_
  rw [cross_edge_count]
  exact sum_seed_rows q hq

theorem hcq_seed_degree_bounds (q : ℕ) (hq : 5 ≤ q) (v : SeedVertex q) :
    q-1 ≤ (hcqSeedGraph q).degree v ∧ (hcqSeedGraph q).degree v ≤ 2*(q-1) := by
  cases v with
  | inl i =>
    rw [cross_degree_left (seedRel q) (hcqSeedGraph q) le_rfl]
    change q-1 ≤ rowDegree (seedRel q) univ i ∧ rowDegree (seedRel q) univ i ≤ 2*(q-1)
    cases i with
    | inl i =>
      rw [seed_row_base,core_row_card q hq]
      by_cases hsmall : i.val<3 <;> by_cases hh : i.val<q-2
      all_goals simp only [hsmall,hh,ite_true,ite_false]
      all_goals omega
    | inr a =>
      have ha : a=0 ∨ a=1 := by fin_cases a <;> simp
      have hd : rowDegree (seedRel q) univ (.inr a)=q := by
        rcases ha with rfl | rfl
        · exact seed_row_f q hq
        · exact seed_row_g q hq
      rw [hd];omega
  | inr j =>
    rw [cross_degree_right (seedRel q) (hcqSeedGraph q) le_rfl]
    change q-1 ≤ columnDegree (seedRel q) univ j ∧ columnDegree (seedRel q) univ j ≤ 2*(q-1)
    cases j with
    | inl j =>
      rw [seed_column_ordinary,core_column_card q hq]
      have hc : (univ.filter fun a : Fin 2 => seedRel q (.inr a) (.inl j)).card ≤ 2 :=
        by simpa using card_filter_le univ (fun a : Fin 2 => seedRel q (.inr a) (.inl j))
      split_ifs <;> omega
    | inr u => cases u;rw [seed_column_h q hq];omega

def hcqDeficit (q : ℕ) : ℕ := q^2-2*q-2

theorem hcq_deficit_guard (q : ℕ) (hq : 5 ≤ q) :
    (q-1)*(q-2)+1 ≤ hcqDeficit q := by
  unfold hcqDeficit
  have h1 : q-1+1=q := by omega
  have h2 : q-2+2=q := by omega
  have hs : 2*q+2 ≤ q^2 := by nlinarith
  have hd : q^2-2*q-2+2*q+2=q^2 := by omega
  nlinarith

theorem hcq_seed_good (q : ℕ) (hq : 5 ≤ q) :
    Good q (hcqDeficit q) (hcqSeedGraph q) (hcqSeedA q) (hcqSeedB q) := by
  have ha : (hcqSeedA q).card=q+3 := by
    simp [hcqSeedA,card_image_of_injective _ Sum.inl_injective,SeedLeft,Fintype.card_sum]
  have hb : (hcqSeedB q).card=q+4 := by
    simp [hcqSeedB,card_image_of_injective _ Sum.inr_injective,SeedRight,Fintype.card_sum]
  have hv : Fintype.card (SeedVertex q)=2*q+7 := by
    simp [SeedVertex,SeedLeft,SeedRight,Fintype.card_sum];omega
  refine ⟨?_,?_,cross_bipartite (seedRel q),by omega,by omega,
    hcq_seed_degree_bounds q hq,?_,hcq_seed_no_regular q hq⟩
  · apply Finset.disjoint_left.mpr
    intro v hva hvb
    obtain ⟨a,_,rfl⟩ := mem_image.mp hva
    obtain ⟨b,_,hb⟩ := mem_image.mp hvb
    cases hb
  · ext v;cases v <;> simp [hcqSeedA,hcqSeedB]
  · rw [hv]
    have he := hcq_seed_edge_count q hq
    unfold hcqDeficit
    have hs : 2*q+2 ≤ q^2 := by nlinarith
    have hd : q^2-2*q-2+2*q+2=q^2 := by omega
    have hr : q-1+1=q := by omega
    nlinarith
end Erdos585.L17HCq

import GeneralStar.Uniform

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

open Finset SimpleGraph
namespace Erdos585.GeneralStar

theorem uniform_order (q s p h b : ℕ) : (uniformSeed q s p h b).order=q+s+b := by
  change Fintype.card (Fin (q+s) ⊕ Fin b)=q+s+b
  simp

theorem uniform_bounds (q s p h b : ℕ) (hq : 5 ≤ q) (hp : UParams q s p h b)
    (v : (uniformSeed q s p h b).Carrier) :
    q-1 ≤ (uniformSeed q s p h b).graph.degree v ∧
    (uniformSeed q s p h b).graph.degree v ≤ 2*(q-1) := by
  rcases hp with ⟨hs,hps,_hhs,_hpa,hab,hbr,hph,hrh,_hend0,_hends⟩
  change Fin (q+s) ⊕ Fin b at v
  cases v with
  | inl i =>
    change q-1 ≤ (L17HCq.crossGraph (uniformRel q s p h b)).degree (.inl i) ∧
      (L17HCq.crossGraph (uniformRel q s p h b)).degree (.inl i) ≤ 2*(q-1)
    rw [L17HCq.cross_degree_left _ _ le_rfl]
    change q-1 ≤ L17HCq.rowDegree (uniformRel q s p h b) univ i ∧ L17HCq.rowDegree (uniformRel q s p h b) univ i ≤ 2*(q-1)
    rw [uniform_row q s p h b hph i]
    split_ifs <;> omega
  | inr j =>
    change q-1 ≤ (L17HCq.crossGraph (uniformRel q s p h b)).degree (.inr j) ∧
      (L17HCq.crossGraph (uniformRel q s p h b)).degree (.inr j) ≤ 2*(q-1)
    rw [L17HCq.cross_degree_right _ _ le_rfl]
    change q-1 ≤ L17HCq.columnDegree (uniformRel q s p h b) univ j ∧ L17HCq.columnDegree (uniformRel q s p h b) univ j ≤ 2*(q-1)
    have hd := uniform_column_bounds q s p h b j
    omega

theorem uniform_edges (q s p h b : ℕ) (hp : UParams q s p h b) :
    (uniformSeed q s p h b).graph.edgeFinset.card+p*h=(q+s)*b := by
  rcases hp with ⟨_hs,hps,_hhs,hpa,_hab,_hbr,hph,_hrh,_hend0,_hends⟩
  have hh : h ≤ b := by nlinarith
  change (L17HCq.crossGraph (uniformRel q s p h b)).edgeFinset.card+p*h=(q+s)*b
  rw [L17HCq.cross_edge_count]
  have hsum : (∑ i : Fin (q+s),L17HCq.rowDegree (uniformRel q s p h b) univ i)+
      (∑ i : Fin (q+s),if i.val<p then h else 0)=(q+s)*b := by
    rw [← sum_add_distrib]
    have he : (∑ i : Fin (q+s),(L17HCq.rowDegree (uniformRel q s p h b) univ i+
        if i.val<p then h else 0))=∑ _i : Fin (q+s), b := by
      apply sum_congr rfl
      intro i _
      rw [uniform_row q s p h b hph i]
      split_ifs <;> omega
    rw [he]
    simp
  have hind : (∑ i : Fin (q+s),if i.val<p then h else 0)=p*h := by
    rw [← sum_filter]
    simp only [sum_const,nsmul_eq_mul,L17HCq.fin_lt_card,Nat.min_eq_right hpa,Nat.cast_id]
  rwa [hind] at hsum

theorem uniform_bipartiteWith (q s p h b : ℕ) :
    (uniformSeed q s p h b).graph.IsBipartiteWith
      ((uniformSeed q s p h b).A : Set (uniformSeed q s p h b).Carrier)
      ((uniformSeed q s p h b).B : Set (uniformSeed q s p h b).Carrier) :=
  L17HCq.cross_bipartite (uniformRel q s p h b)

theorem uniform_slots (q s p h b : ℕ) (hq : 5 ≤ q) (hp : UParams q s p h b) :
    (q-1)^2 ≤ ∑ v ∈ (uniformSeed q s p h b).B,
      (2*(q-1)-(uniformSeed q s p h b).graph.degree v) := by
  let D := uniformSeed q s p h b
  have hdegree := uniform_bounds q s p h b hq hp
  have hcapacity : (∑ v ∈ D.B, (2*(q-1)-D.graph.degree v))+
      D.graph.edgeFinset.card=2*(q-1)*b := by
    calc
      _ = (∑ v ∈ D.B, (2*(q-1)-D.graph.degree v))+∑ v ∈ D.B,D.graph.degree v := by
        rw [SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' (uniform_bipartiteWith q s p h b)]
      _ = ∑ _v ∈ D.B,2*(q-1) := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro v _
        exact Nat.sub_add_cancel (hdegree v).2
      _ = _ := by
        have hc : D.B.card=b := by
          change (univ.image Sum.inr : Finset (Fin (q+s) ⊕ Fin b)).card=b
          rw [card_image_of_injective _ Sum.inr_injective,card_univ,Fintype.card_fin]
        simp [hc,mul_comm]
  rcases hp with ⟨_hs,hps,hhs,hpa,hab,hbr,hph,_hrh,_hend0,_hends⟩
  have he := uniform_edges q s p h b ⟨by omega,hps,hhs,hpa,hab,hbr,hph,by omega,by omega,by omega⟩
  have hr : q-1+1=q := by omega
  have hat : q+s ≤ 2*(q-1) := by omega
  have hguard : s+1 ≤ q-1 := by omega
  have hsquare : (s+1)^2 ≤ p*h := by nlinarith
  have hm := Nat.mul_le_mul_right (2*(q-1)-(q+s)) hab
  have hsub : 2*(q-1)-(q+s)+(q+s)=2*(q-1) := by omega
  change (∑ v ∈ D.B, (2*(q-1)-D.graph.degree v))+D.graph.edgeFinset.card=2*(q-1)*b at hcapacity
  change D.graph.edgeFinset.card+p*h=(q+s)*b at he
  nlinarith

theorem uniform_seedHyp (q s p h b : ℕ) (hq : 5 ≤ q) (hp : UParams q s p h b) :
    SeedHyp q (uniformSeed q s p h b) := by
  refine ⟨?_,?_,uniform_bipartiteWith q s p h b,uniform_bounds q s p h b hq hp,
    uniform_noRegular q s p h b hq hp,uniform_slots q s p h b hq hp⟩
  · change Disjoint (univ.image Sum.inl : Finset (Fin (q+s) ⊕ Fin b)) (univ.image Sum.inr)
    apply Finset.disjoint_left.mpr
    intro v hva hvb
    obtain ⟨a,_,rfl⟩ := mem_image.mp hva
    obtain ⟨z,_,he⟩ := mem_image.mp hvb
    cases he
  · change (univ.image Sum.inl : Finset (Fin (q+s) ⊕ Fin b)) ∪ (univ.image Sum.inr)=univ
    ext v;cases v <;> simp

theorem uniform_deficit (q s p h b : ℕ) (hq : 5 ≤ q) (hp : UParams q s p h b) :
    (q-1)*(uniformSeed q s p h b).order-(uniformSeed q s p h b).graph.edgeFinset.card =
      uniformDeficit q s p h b := by
  have he := uniform_edges q s p h b hp
  rcases hp with ⟨_hs,_hps,_hhs,_hpa,hab,hbr,_hph,_hrh,_hend0,_hends⟩
  have hqr : q-1+1=q := by omega
  have ha : q+s ≤ 2*(q-1) := by omega
  have h1 := Nat.mul_le_mul_right b ha
  have h2 := Nat.mul_le_mul_right (q+s) hbr
  have habound : (q+s)*b ≤ (q-1)*(q+s+b) := by nlinarith
  rw [uniform_order]
  unfold uniformDeficit
  omega

/-- U24 has no seed, selection, slot, or factor hypothesis. -/
theorem U24 (q s p h b n : ℕ) (hq : 5 ≤ q) (hp : UParams q s p h b)
    (hn : uniformStart q s b ≤ n) :
    FamilyConclusion q n (uniformDeficit q s p h b) (uniformFamily q s p h b n) := by
  have hs := uniform_seedHyp q s p h b hq hp
  have ho : (uniformSeed q s p h b).order=uniformStart q s b := uniform_order q s p h b
  have ht := T24_order q (uniformSeed q s p h b) hq hs n (by omega)
  rw [uniform_deficit q s p h b hq hp] at ht
  simpa only [uniformFamily,ho] using ht

end Erdos585.GeneralStar

import R863.Selection
import R863.Rank
import R863.Resources
import R863.UniformEscape

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
open Finset SimpleGraph
noncomputable section
namespace Erdos585.R863
open QB4 B5 L34 H3Unequal
open AllHNextNonstrict.TopEscape
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace ActualSelection

lemma upward_strict {q j : ℕ} {A B K S P : Finset V}
    (_hK : K⊆B) (hp : Rank.UpwardMin q j G A B K S P) :
    ∀ T⊆B, K∪P⊆T → K∪P≠T →
      thetaJ q j G A B T≤thetaJ q j G A B (K∪P)-1 := by
  classical
  intro T hT hKT hne
  have hPT : P⊆T\K := by
    classical
    intro v hv
    exact mem_sdiff.mpr ⟨hKT (mem_union_right _ hv),(mem_sdiff.mp (hp.subset hv)).2⟩
  have hKsub : K⊆T := subset_union_left.trans hKT
  have hneP : P≠T\K := by
    classical
    intro he
    exact hne (by rw [he,union_sdiff_of_subset hKsub])
  have hc := hp.strict (T\K) (sdiff_subset_sdiff_left K hT) hPT hneP
  unfold extensionCost at hc
  rw [union_sdiff_of_subset hKsub] at hc
  omega

/-- Actual upward-minimum descent in one fixed original residual carrier. -/
lemma rank_select {h q j e : ℕ} {A B K : Finset V}
    (d : Data h q j e G A B) (hK : K⊆B) (hl : q-1≤#K) :
    ∀ (n : ℕ) (S : Finset V), S⊆B\K →
      (∀ Q⊆B\K, S⊆Q → thetaJ q j G A B K-2*(n : ℤ)≤extensionCost q j G A B K Q) →
      ∃ Y⊆B\K, S⊆Y ∧ #Y≤#S+n ∧
        ∀ Q⊆B\K, Y⊆Q → thetaJ q j G A B K≤extensionCost q j G A B K Q := by
  classical
  intro n
  induction n with
  | zero =>
      intro S hS hLower
      exact ⟨S,hS,Subset.rfl,by omega,by simpa using hLower⟩
  | succ n ih =>
      intro S hS hLower
      obtain ⟨P,hp⟩ := Rank.exists_upward_min (G:=G) q j A B K S hS
      have hbound := hLower P hp.subset hp.contains
      by_cases hdone : thetaJ q j G A B K≤extensionCost q j G A B K P
      · refine ⟨S,hS,Subset.rfl,by omega,?_⟩
        intro Q hQ hSQ
        exact hdone.trans (hp.minimal Q hQ hSQ)
      · have hpos : 0<thetaJ q j G A B (K∪P) := by
          classical
          unfold extensionCost at hdone
          omega
        have hT : K∪P⊆B := union_subset hK (hp.subset.trans sdiff_subset)
        have hlT : q-1≤#(K∪P) := hl.trans (card_le_card subset_union_left)
        have hsT := upward_strict hK hp
        have hstep : ∃ z∈B\(K∪P), ∀ Q⊆B\K, insert z S⊆Q →
            thetaJ q j G A B K-2*(n : ℤ)≤extensionCost q j G A B K Q := by
          classical
          by_cases htwo : 2≤thetaJ q j G A B (K∪P)
          · obtain ⟨z,hz,_,hcost⟩ := petal_escape (G:=G) h q j e A B (K∪P) ∅ d
              hT hlT htwo hsT (empty_subset _) (by simp)
            refine ⟨z,hz,?_⟩
            intro Q hQ hSQ
            have hzQ := hSQ (mem_insert_self _ _)
            have hzP : z∉P := fun hzP => (mem_sdiff.mp hz).2 (mem_union_right _ hzP)
            have hQP : Q\P⊆B\(K∪P) := by
              classical
              intro v hv
              have hvR := mem_sdiff.mp (hQ (mem_sdiff.mp hv).1)
              exact mem_sdiff.mpr ⟨hvR.1,fun hu => (mem_union.mp hu).elim hvR.2 (mem_sdiff.mp hv).2⟩
            have hc := hcost (Q\P) hQP (mem_sdiff.mpr ⟨hzQ,hzP⟩)
            have he := cost_contract (G:=G) (q:=q) (j:=j) (A:=A) (B:=B) (K:=K) (H:=P) (P:=Q\P)
            have hset : P∪(Q\P)=P∪Q := by ext v; simp only [mem_union,mem_sdiff]; tauto
            rw [hset] at he
            have hgain := Rank.gain_transfer hp hQ ((subset_insert z S).trans hSQ)
            push_cast at hbound
            omega
          · have hR := d.positive_complement hT hpos
            obtain ⟨z,hz⟩ := card_pos.mp (show 0<#(B\(K∪P)) by omega)
            refine ⟨z,hz,?_⟩
            intro Q hQ hSQ
            have hzQ := hSQ (mem_insert_self _ _)
            have hzP : z∉P := fun hzP => (mem_sdiff.mp hz).2 (mem_union_right _ hzP)
            have hQP : Q\P⊆B\(K∪P) := by
              classical
              intro v hv
              have hvR := mem_sdiff.mp (hQ (mem_sdiff.mp hv).1)
              exact mem_sdiff.mpr ⟨hvR.1,fun hu => (mem_union.mp hu).elim hvR.2 (mem_sdiff.mp hv).2⟩
            have hc := strict_extension_cost_min hT hsT (Q\P) hQP ⟨z,mem_sdiff.mpr ⟨hzQ,hzP⟩⟩
            have he := cost_contract (G:=G) (q:=q) (j:=j) (A:=A) (B:=B) (K:=K) (H:=P) (P:=Q\P)
            have hset : P∪(Q\P)=P∪Q := by ext v; simp only [mem_union,mem_sdiff]; tauto
            rw [hset] at he
            have hgain := Rank.gain_transfer hp hQ ((subset_insert z S).trans hSQ)
            have hone : extensionCost q j G A B K P=thetaJ q j G A B K-1 := by
              classical
              unfold extensionCost
              omega
            omega
        obtain ⟨z,hz,hnew⟩ := hstep
        have hnewS : insert z S⊆B\K := by
          classical
          apply insert_subset_iff.mpr
          exact ⟨mem_sdiff.mpr ⟨(mem_sdiff.mp hz).1,fun hh => (mem_sdiff.mp hz).2 (mem_union_left _ hh)⟩,hS⟩
        obtain ⟨Y,hY,hSY,hcard,hgood⟩ := ih (insert z S) hnewS hnew
        refine ⟨Y,hY,(subset_insert z S).trans hSY,?_,hgood⟩
        have hc := card_insert_le z S
        omega

/-- One actual upward selection, padded inside its original residual carrier, pays every original cut. -/
theorem common_omission {h q j e : ℕ} {A B : Finset V} (d : Data h q j e G A B) :
    ∃ O : Finset V, O⊆B ∧ #O=j ∧ ∀ T⊆B, O⊆T → thetaJ q j G A B T≤0 := by
  classical
  by_cases hex : ∃ T, LargePositive q j G A B T
  · obtain ⟨K,hk⟩ := AllHTopTwo.exists_high_above (G:=G) q j
      (show ∃ T, LargePositive q j G A B T ∧ (∅ : Finset V)⊆T from
        by obtain ⟨T,hT⟩ := hex; exact ⟨T,hT,empty_subset _⟩)
    have hK := hk.positive.1
    have hl := hk.positive.2.1
    have hR := d.positive_complement hK hk.positive.2.2
    have hbound := d.theta_large_le hK hl
    have hj := d.parameters.j_bounds
    have hjpos := d.parameters.j_pos
    have hbase : ∀ Q⊆B\K, (0 : ℤ)≤extensionCost q j G A B K Q := by
      classical
      intro Q hQ
      by_cases he : Q=∅
      · simp [he,extensionCost]
      · have hm := strict_extension_cost_min hK hk.strict Q hQ (nonempty_iff_ne_empty.mpr he)
        omega
    have hexY : ∃ Y⊆B\K, #Y≤j ∧
        ∀ Q⊆B\K, Y⊆Q → thetaJ q j G A B K≤extensionCost q j G A B K Q := by
      classical
      by_cases hlo : thetaJ q j G A B K≤2*(j : ℤ)
      · have hb : ∀ Q⊆B\K, (∅ : Finset V)⊆Q →
            thetaJ q j G A B K-2*(j : ℤ)≤extensionCost q j G A B K Q := by
          classical
          intro Q hQ _
          have hh := hbase Q hQ
          omega
        obtain ⟨Y,hY,_,hc,hgood⟩ := rank_select d hK hl j ∅ (empty_subset _) hb
        exact ⟨Y,hY,by simpa using hc,hgood⟩
      · have hstep : ∃ z∈B\K, ∀ Q⊆B\K, z∈Q →
            thetaJ q j G A B K-2*((j-1 : ℕ) : ℤ)≤extensionCost q j G A B K Q := by
          classical
          let s := (thetaJ q j G A B K-2*(j : ℤ)+1).toNat
          have hs : (s : ℤ)=thetaJ q j G A B K-2*(j : ℤ)+1 :=
            Int.toNat_of_nonneg (by omega)
          obtain ⟨z,hz,_hlight,hc⟩ := UniformEscape.escape d s K hK hl (by omega) hk.strict
          refine ⟨z,hz,?_⟩
          intro Q hQ hzQ
          have hh := hc Q hQ hzQ
          omega
        obtain ⟨z,hz,hstep⟩ := hstep
        obtain ⟨Y,hY,_,hc,hgood⟩ := rank_select d hK hl (j-1) {z} (singleton_subset_iff.mpr hz)
          (fun Q hQ hZQ => hstep Q hQ (hZQ (mem_singleton_self z)))
        exact ⟨Y,hY,by simp only [card_singleton] at hc; omega,hgood⟩
    obtain ⟨Y,hY,hYj,hgood⟩ := hexY
    have hRj : j≤#(B\K) := by have hq := d.parameters.q_ge_height; omega
    have hav : j-#Y≤#((B\K)\Y) := by
      classical
      have hh := card_sdiff_add_card_eq_card hY
      omega
    obtain ⟨U,hU,hUc⟩ := exists_subset_card_eq hav
    have hdis : Disjoint Y U := Finset.disjoint_left.mpr fun v hv hu => (mem_sdiff.mp (hU hu)).2 hv
    let O := Y∪U
    have hOR : O⊆B\K := union_subset hY (hU.trans sdiff_subset)
    have hOj : #O=j := by rw [card_union_of_disjoint hdis]; omega
    refine ⟨O,hOR.trans sdiff_subset,hOj,?_⟩
    intro T hT hOT
    by_cases hlarge : q-1≤#T
    · by_contra! hp
      have hcomp := d.high_compare_union hk ⟨hT,hlarge,hp⟩ (empty_subset _)
      have hYQ : Y⊆T\K := by
        classical
        intro v hv
        have hvO : v∈O := mem_union_left _ hv
        exact mem_sdiff.mpr ⟨hOT hvO,(mem_sdiff.mp (hOR hvO)).2⟩
      have hh := hgood (T\K) (sdiff_subset_sdiff_left K hT) hYQ
      have he : K∪(T\K)=K∪T := by ext v; simp only [mem_union,mem_sdiff]; tauto
      rw [extensionCost,he] at hh
      omega
    · exact d.small_good hOj hOT (by have hq := d.parameters.q_pos; omega)
  · have hB : j≤#B := by have hh := d.shores_large.2; omega
    obtain ⟨O,hO,hOj⟩ := exists_subset_card_eq hB
    refine ⟨O,hO,hOj,?_⟩
    intro T hT hOT
    by_cases hl : q-1≤#T
    · by_contra! hp
      exact hex ⟨T,hT,hl,hp⟩
    · exact d.small_good hOj hOT (by have hq := d.parameters.q_pos; omega)

end ActualSelection
end Erdos585.R863

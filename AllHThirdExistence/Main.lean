import AllHThirdTwoQuota.Main
import AllHThirdQuotaFailure.Main

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.AllHThirdExistence
open AllHThirdFragileFree (Host)
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {h q j : ℕ} {A B S O : Finset V}

/-- The actual omission identities pay equal retained shores. -/
lemma balance_of_omissions (host : Host h q j G A B)
    (hSA : S⊆A) (hOB : O⊆B) (hO : #O=j+#S) : #(A\S)=#(B\O) := by
  classical
  have ha := card_sdiff_add_card_eq_card hSA
  have hb := card_sdiff_add_card_eq_card hOB
  have hc := host.card
  omega

/-- An actual omitted original vertex makes the exact original support proper. -/
lemma proper_of_omission (host : Host h q j G A B)
    (hSA : S⊆A) (hOB : O⊆B) (hne : S.Nonempty ∨ O.Nonempty)
    (H : G.Subgraph) (hverts : H.verts=(↑((A\S)∪(B\O)):Set V)) :
    H.verts⊂(Set.univ : Set V) := by
  classical
  apply Set.ssubset_univ_iff.mpr
  intro he
  rcases hne with hs|ho
  · obtain ⟨x,hx⟩ := hs
    have hv : x∈H.verts := by rw [he]; trivial
    rw [hverts] at hv
    rcases mem_union.mp hv with ha|hb
    · exact (mem_sdiff.mp ha).2 hx
    · exact disjoint_left.mp host.disjoint (hSA hx) (mem_sdiff.mp hb).1
  · obtain ⟨x,hx⟩ := ho
    have hv : x∈H.verts := by rw [he]; trivial
    rw [hverts] at hv
    rcases mem_union.mp hv with ha|hb
    · exact disjoint_left.mp host.disjoint (mem_sdiff.mp ha).1 (hOB hx)
    · exact (mem_sdiff.mp hb).2 hx

/-- Negating the literal pair scalar produces actual distinct fragile roots. -/
lemma failed_pair (hn : ¬AllHThirdTwoQuota.OriginalPairCondition h q j G A B) :
    ∃ x∈A, G.degree x≤q+2*h-5 ∧ ∃ y∈A, G.degree y≤q+2*h-5 ∧ x≠y ∧
      AllHThirdQuotaFailure.QuotaFailure G q j B x y := by
  classical
  unfold AllHThirdTwoQuota.OriginalPairCondition at hn
  push Not at hn
  obtain ⟨x,hx,hxd,y,hy,hyd,hxy,hfail⟩ := hn
  refine ⟨x,hx,hxd,y,hy,hyd,hxy,?_⟩
  unfold AllHThirdQuotaFailure.QuotaFailure
  rw [AllHThirdTwoQuota.Original.outside_card x y]
  exact hfail

/-- Every exact strict third-surplus original host has a proper original q-factor.
The omission counts and retained shores refer to the same original support. -/
theorem third_surplus (h q j : ℕ) (G : SimpleGraph V) (A B : Finset V)
    (host : Host h q j G A B) :
    ∃ S O : Finset V, S⊆A ∧ O⊆B ∧ #S≤8*h-1 ∧
      #O=j+#S ∧ #O≤8*h+j-1 ∧ #O<9*h ∧
      q≤#(A\S) ∧ #(A\S)=#(B\O) ∧
      ∃ H : G.Subgraph, H.verts=(↑((A\S)∪(B\O)):Set V) ∧
        H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q ∧ H.verts⊂(Set.univ : Set V) := by
  classical
  have hn := AllHThirdQuotaFailure.Host.numeric host
  by_cases hp : AllHThirdTwoQuota.OriginalPairCondition h q j G A B
  · obtain ⟨O,hOB,hOj,_hcuts,H,hverts,hnonempty,hregular⟩ :=
      (AllHThirdTwoQuota.whole_A_iff h q j G A B host).mpr hp
    have hSA : (∅ : Finset V)⊆A := empty_subset A
    have hO : #O=j+#(∅ : Finset V) := by simpa using hOj
    have hbalance := balance_of_omissions host hSA hOB hO
    have hretained : q≤#(A\(∅ : Finset V)) := by
      simpa using (AllHThirdTwoQuota.Original.to_data host).shores_large.1
    have hverts' : H.verts=(↑((A\(∅ : Finset V))∪(B\O)):Set V) := by
      simpa using hverts
    have hproper := proper_of_omission host hSA hOB
      (Or.inr (card_pos.mp (show 0<#O by omega))) H hverts'
    refine ⟨∅,O,hSA,hOB,?_,hO,?_,?_,hretained,hbalance,H,hverts',hnonempty,hregular,hproper⟩
    · simp
    · simp only [card_empty] at hO
      omega
    · omega
  · obtain ⟨x,hx,_hxd,y,hy,_hyd,hxy,hfail⟩ := failed_pair hp
    obtain ⟨S,O,hSA,hOB,_hxS,_hyS,hSlo,hShi,hO,hOhi,hOlt,hmlo,_hmhi,_hfactor,
      H,hverts,hnonempty,hregular⟩ := AllHThirdQuotaFailure.qfail host hx hy hxy hfail
    have hbalance := balance_of_omissions host hSA hOB hO
    have hproper := proper_of_omission host hSA hOB
      (Or.inl (card_pos.mp (show 0<#S by omega))) H hverts
    exact ⟨S,O,hSA,hOB,hShi,hO,hOhi,hOlt,hmlo,hbalance,H,hverts,hnonempty,hregular,hproper⟩

/-- Forgetting the paid support bounds leaves unconditional proper-factor existence. -/
theorem proper_factor_exists (h q j : ℕ) (G : SimpleGraph V) (A B : Finset V)
    (host : Host h q j G A B) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q ∧
      H.verts⊂(Set.univ : Set V) := by
  obtain ⟨S,O,_hSA,_hOB,_hS,_hO,_hOhi,_hOlt,_hm,_hbal,H,_hverts,hn,hreg,hproper⟩ :=
    third_surplus h q j G A B host
  exact ⟨H,hn,hreg,hproper⟩

end Erdos585.AllHThirdExistence

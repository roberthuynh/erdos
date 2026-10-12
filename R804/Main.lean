import R804.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
noncomputable section

namespace Erdos585.R804
open QB4 B5 L34 H3Unequal

universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {h q j ξ : ℕ} {A B S O : Finset V}

open Classical in
/-- The same actual original omissions balance the two retained shores. -/
lemma balance_of_omissions (host : Host h q j ξ G A B)
    (hSA : S⊆A) (hOB : O⊆B) (hO : #O=j+#S) : #(A\S)=#(B\O) := by
  have ha := card_sdiff_add_card_eq_card hSA
  have hb := card_sdiff_add_card_eq_card hOB
  have hc := host.card
  omega

open Classical in
/-- Any actual omission makes this exact original support proper. -/
lemma proper_of_omission (host : Host h q j ξ G A B)
    (hSA : S⊆A) (hOB : O⊆B) (hne : S.Nonempty ∨ O.Nonempty)
    (H : G.Subgraph) (hverts : H.verts=(↑((A\S)∪(B\O)):Set V)) :
    H.verts⊂(Set.univ : Set V) := by
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

open Classical in
/-- Every literal strict fourth-surplus host produces a proper original q-subgraph.
The omission counts, retained shores, and returned graph all use the SAME support. -/
theorem variable_offset_surplus (h q j ξ : ℕ) (G : SimpleGraph V) (A B : Finset V)
    (host : Host h q j ξ G A B) :
    ∃ S O : Finset V, S⊆A ∧ O⊆B ∧ #S≤8*h-1 ∧
      #O=j+#S ∧ #O≤8*h+j-1 ∧ #O<9*h ∧
      q≤#(A\S) ∧ #(A\S)=#(B\O) ∧
      ((S=∅ ∧ #O=j) ∨ (1≤#S ∧ #(A\S)<#A ∧ #(B\O)<#B)) ∧
      ∃ H : G.Subgraph, H.verts=(↑((A\S)∪(B\O)):Set V) ∧
        H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q ∧ H.verts⊂(Set.univ : Set V) := by
  have hn := Host.numeric host
  by_cases hp : ∃ O0 : Finset V, O0⊆B ∧ #O0=j ∧ ∀ x∈A,
      G.degree x≤q+2*h-5 → dg G O0 x≤G.degree x-q
  · obtain ⟨O,hOB,hOj,_hcuts,H,hverts,hnonempty,hregular⟩ :=
      AllHQuotaNonstrict.uniform_quota_nonstrict h q j ξ G A B (quota_host host) hp
    have hSA : (∅ : Finset V)⊆A := empty_subset A
    have hO : #O=j+#(∅ : Finset V) := by simpa using hOj
    have hbalance := balance_of_omissions host hSA hOB hO
    have hretained : q≤#(A\(∅ : Finset V)) := by
      simpa using ((quota_host host).to_data).shores_large.1
    have hverts' : H.verts=(↑((A\(∅ : Finset V))∪(B\O)):Set V) := by
      simpa using hverts
    have hproper := proper_of_omission host hSA hOB
      (Or.inr (card_pos.mp (show 0<#O by omega))) H hverts'
    refine ⟨∅,O,hSA,hOB,?_,hO,?_,?_,hretained,hbalance,
      Or.inl ⟨rfl,hOj⟩,H,hverts',hnonempty,hregular,hproper⟩
    · simp
    · simp only [card_empty] at hO
      omega
    · omega
  · let W := A.filter (fun x => G.degree x≤q+2*h-5)
    have hf : Failed G q j B W := by
      intro hgood
      obtain ⟨O,hOB,hOj,hpay⟩ := hgood
      apply hp
      refine ⟨O,hOB,hOj,?_⟩
      intro x hx hlow
      exact hpay x (mem_filter.mpr ⟨hx,hlow⟩)
    obtain ⟨x,hx,y,hy,z,hz,hxy,hxz,hyz,hthree⟩ :=
      failed_three host hf (filter_subset _ _)
    obtain ⟨S,O,hSA,hOB,_hd,hc⟩ :=
      three_quota host hx hy hz hxy hxz hyz hthree
    have hAS := retained_sdiff hSA
    have hBO := retained_sdiff hOB
    have hS : #S≤8*h-1 := by simpa only [hAS] using hc.omitted_bound
    have hSpos : 1≤#S := by simpa only [hAS] using hc.omitted_positive
    have hO : #O=j+#S := by simpa only [hAS,hBO] using hc.omitted_equal
    have hOhi : #O≤8*h+j-1 := by simpa only [hBO] using hc.omitted_right_bound
    have hOlt : #O<9*h := by simpa only [hBO] using hc.omitted_right_small
    have hbalance := balance_of_omissions host hSA hOB hO
    obtain ⟨H,hverts,hnonempty,hregular⟩ := hc.subgraph
    have hproper := proper_of_omission host hSA hOB
      (Or.inl (card_pos.mp (show 0<#S by omega))) H hverts
    exact ⟨S,O,hSA,hOB,hS,hO,hOhi,hOlt,hc.size_lower,hbalance,
      Or.inr ⟨hSpos,hc.strict_left,hc.strict_right⟩,
      H,hverts,hnonempty,hregular,hproper⟩

open Classical in
/-- Forgetting the quantitative omissions leaves unconditional proper-factor existence. -/
theorem proper_factor_exists (h q j ξ : ℕ) (G : SimpleGraph V) (A B : Finset V)
    (host : Host h q j ξ G A B) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q ∧
      H.verts⊂(Set.univ : Set V) := by
  obtain ⟨S,O,_hSA,_hOB,_hS,_hO,_hOhi,_hOlt,_hm,_hbal,_hbranch,
    H,_hverts,hn,hreg,hproper⟩ := variable_offset_surplus h q j ξ G A B host
  exact ⟨H,hn,hreg,hproper⟩

end Erdos585.R804

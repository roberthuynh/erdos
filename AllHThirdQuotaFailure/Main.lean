import AllHThirdQuotaFailure.Dense
import AllHThirdQuotaFailure.Trim

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.AllHThirdQuotaFailure
open QB4 B5 L34 H3Unequal
open AllHThirdFragileFree (Host offset constant)
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {h q j : ℕ} {A B AH BH : Finset V} {x y : V}

/-- QFAIL213 for EVERY prescribed original balancing choice. -/
theorem qfail_cleanup (host : Host h q j G A B)
    (hx : x∈A) (hy : y∈A) (hne : x≠y)
    (hf : QuotaFailure G q j B x y) (d : Cleanup G q A B AH BH) :
    Conclusion G h q j A B AH BH x y := by
  classical
  have hs := d.shore_bounds host hx hy hf
  have hr := d.roots_deleted host hx hy hne hf
  have ho := d.omission_bounds host
  have hnon := d.nonempty host hx
  have hl : ∀ v∈AH,#AH+q≤2*dg G BH v := by
    intro v hv
    have hd := d.retained_left host hv
    omega
  have hb : ∀ v∈BH,#AH+q≤2*dg G AH v := by
    intro v hv
    have hd := d.retained_right host hv
    omega
  have hfactor := dense_factor q d.balanced hs.1 hl hb
  have hdis := host.disjoint.mono d.left_original d.right_original
  have hsub := factor_exact_subgraph (Host.numeric host).1 hnon hdis hfactor
  exact ⟨hs.1,hs.2,hr.1,hr.2.1,hr.2.2,ho.1,ho.2.1,ho.2.2.1,ho.2.2.2,hfactor,hsub⟩

omit [Fintype V] in
lemma retained_sdiff {P T : Finset V} (hT : T⊆P) : P\(P\T)=T := by
  classical
  ext v
  simp only [mem_sdiff]
  constructor
  · rintro ⟨hv,hn⟩
    by_contra hh
    exact hn ⟨hv,hh⟩
  · intro hv
    exact ⟨hT hv,fun hh => hh.2 hv⟩

/-- Bare supporting theorem: roots, omissions and original q-factor all produced. -/
theorem qfail (host : Host h q j G A B)
    (hx : x∈A) (hy : y∈A) (hne : x≠y) (hf : QuotaFailure G q j B x y) :
    ∃ S O : Finset V, S⊆A ∧ O⊆B ∧ x∈S ∧ y∈S ∧
      2≤#S ∧ #S≤8*h-1 ∧ #O=j+#S ∧ #O≤8*h+j-1 ∧ #O<9*h ∧
      q≤#(A\S) ∧ #(A\S)<2*q ∧ FactorOn q G (A\S) (B\O) ∧
      ∃ H : G.Subgraph, H.verts=(↑((A\S)∪(B\O)):Set V) ∧
        H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  classical
  obtain ⟨AH,BH,d⟩ := exists_cleanup (G:=G) q A B
  have hc := qfail_cleanup host hx hy hne hf d
  change q≤#AH ∧ #AH<2*q ∧ x∈A\AH ∧ y∈A\AH ∧
    2≤#(A\AH) ∧ #(A\AH)≤8*h-1 ∧ #(B\BH)=j+#(A\AH) ∧
    #(B\BH)≤8*h+j-1 ∧ #(B\BH)<9*h ∧ FactorOn q G AH BH ∧
    ∃ H:G.Subgraph,H.verts=(↑(AH∪BH):Set V) ∧ H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q at hc
  have ha := retained_sdiff d.left_original
  have hb := retained_sdiff d.right_original
  refine ⟨A\AH,B\BH,sdiff_subset,sdiff_subset,hc.2.2.1,hc.2.2.2.1,
    hc.2.2.2.2.1,hc.2.2.2.2.2.1,hc.2.2.2.2.2.2.1,
    hc.2.2.2.2.2.2.2.1,hc.2.2.2.2.2.2.2.2.1,?_,?_,?_,?_⟩
  · simpa only [ha] using hc.1
  · simpa only [ha] using hc.2.1
  · simpa only [ha,hb] using hc.2.2.2.2.2.2.2.2.2.1
  · simpa only [ha,hb] using hc.2.2.2.2.2.2.2.2.2.2

end Erdos585.AllHThirdQuotaFailure

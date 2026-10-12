import AllHFourthQuotaFailure.Dense
import AllHFourthQuotaFailure.Trim

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] r248InterfaceDecidableEq
namespace Erdos585.AllHFourthQuotaFailure
open QB4 B5 L34 H3Unequal
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {h q j : ℕ} {A B AH BH : Finset V} {x y z : V}

/-- The failed-three-quota branch, for EVERY prescribed mark-and-balance choice. -/
theorem three_quota_cleanup (host : Host h q j G A B)
    (hx : x∈A) (hy : y∈A) (hz : z∈A) (hxy : x≠y) (hxz : x≠z) (hyz : y≠z)
    (hf : ThreeFailure G q j B x y z) (d : Cleanup G q A B AH BH) :
    Conclusion G h q j A B AH BH {x,y,z} := by
  have hT : ({x,y,z}:Finset V)⊆A := by
    simp only [insert_subset_iff,singleton_subset_iff]
    exact ⟨hx,hy,hz⟩
  have hTc : #({x,y,z}:Finset V)=3 := by simp [hxy,hxz,hyz]
  obtain ⟨I,hi⟩ := exists_minimal_failed hf
  have hn := Host.numeric host
  have hs := Host.shores_large host hx
  have hI := hi.nonempty (show j≤#B by omega)
  have hIc : #I≤3 := (card_le_card hi.subset).trans (by omega)
  have hdel := d.essential_deleted host hi hT
  have hpos : 1≤#(A\AH) := by
    obtain ⟨v,hv⟩ := hI
    have hp : 0<#(A\AH) := card_pos.mpr ⟨v,hdel hv⟩
    omega
  have hbounds := d.shore_bounds host hx hi hT (by omega)
  have homit := d.omission_bounds host
  have hnon := d.nonempty host hx
  have hfactor := dense_factor q d.balanced (by omega) hnon hbounds.2
    (fun _ hv => d.retained_left host hv) (fun _ hv => d.retained_right host hv)
  have hupperA : ∀ v∈AH,dg G BH v<2*q := by
    intro v hv
    have hs := dg_sdiff_add (G:=G) d.right_original v
    have he := dg_eq_degree host.bipartite (d.left_original hv)
    have hc := host.cap_degree v
    omega
  have hupperB : ∀ v∈BH,dg G AH v<2*q := by
    intro v hv
    have hs := dg_sdiff_add (G:=G) d.left_original v
    have he := dg_eq_degree host.bipartite.symm (d.right_original hv)
    have hc := host.cap_degree v
    omega
  have hmargin := actual_minimum_margin q d.balanced hnon hbounds.2
    (fun _ hv => d.retained_left host hv) (fun _ hv => d.retained_right host hv) hupperA hupperB
  have hshrinkA : #AH<#A := by
    have he := card_sdiff_add_card_eq_card d.left_original
    omega
  have hshrinkB : #BH<#B := by
    have he := card_sdiff_add_card_eq_card d.right_original
    have heq := homit.2.1
    omega
  exact ⟨hbounds.1,hbounds.2,(fun _ hv => d.retained_left host hv),(fun _ hv => d.retained_right host hv),hpos,
    homit.1,homit.2.1,homit.2.2.1,homit.2.2.2,hi.shore_bound host hT (by omega),
    ⟨I,hi,hI,hIc,(fun _ hv => hi.quota_lt hv),hdel⟩,hmargin,hshrinkA,hshrinkB,hfactor,
    factor_exact_subgraph hn.1 hnon
      (host.disjoint.mono d.left_original d.right_original) hfactor⟩

omit [Fintype V] in
lemma retained_sdiff {P T : Finset V} (hT : T⊆P) : P\(P\T)=T := by
  ext v
  simp only [mem_sdiff]
  constructor
  · rintro ⟨hv,hn⟩
    by_contra hh
    exact hn ⟨hv,hh⟩
  · intro hv
    exact ⟨hT hv,fun hh => hh.2 hv⟩

/-- All original omissions, the carrier and the factor are internally produced. -/
theorem three_quota (host : Host h q j G A B)
    (hx : x∈A) (hy : y∈A) (hz : z∈A) (hxy : x≠y) (hxz : x≠z) (hyz : y≠z)
    (hf : ThreeFailure G q j B x y z) :
    ∃ S O : Finset V, S⊆A ∧ O⊆B ∧
      Cleanup G q A B (A\S) (B\O) ∧
      Conclusion G h q j A B (A\S) (B\O) {x,y,z} := by
  obtain ⟨AH,BH,d⟩ := exists_cleanup (G:=G) q A B
  have hc := three_quota_cleanup host hx hy hz hxy hxz hyz hf d
  have ha := retained_sdiff d.left_original
  have hb := retained_sdiff d.right_original
  refine ⟨A\AH,B\BH,sdiff_subset,sdiff_subset,?_,?_⟩
  · simpa only [ha,hb] using d
  · simpa only [ha,hb] using hc

end Erdos585.AllHFourthQuotaFailure

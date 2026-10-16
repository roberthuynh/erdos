import AllHThirdTwoQuota.Original
import AllHThirdTwoQuota.Quota
import AllHThirdTwoQuota.Selection
import AllHThirdTwoQuota.PetalEscape
import AllHThirdTwoQuota.TopEscape

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section

namespace Erdos585.AllHThirdTwoQuota
open QB4 B5 L34 H3Unequal
open AllHThirdFragileFree (Host offset constant)
universe u

/-- ONE omission pays ALL original cuts and supports an actual exact-support factor. -/
def WholeASelection (q j : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) : Prop := by
  classical
  exact ∃ O : Finset V, O⊆B ∧ #O=j ∧
    (∀ T⊆B, O⊆T → thetaJ q j G A B T≤0) ∧
    ∃ H : G.Subgraph, H.verts=(↑(A∪(B\O)) : Set V) ∧
      H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q

/-- Factor-only existence uses the same literal original support. -/
def OriginalWholeAFactor (q j : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) : Prop := by
  classical
  exact ∃ O : Finset V, O⊆B ∧ #O=j ∧
    ∃ H : G.Subgraph, H.verts=(↑(A∪(B\O)) : Set V) ∧
      H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q

/-- Literal original degrees and neighborhoods, with no supplied fragile family.
The right side is vacuous for zero or one actual fragile row. -/
def OriginalPairCondition (h q j : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) : Prop :=
  ∀ x∈A, G.degree x≤q+2*h-5 → ∀ y∈A, G.degree y≤q+2*h-5 → x≠y →
    j≤({z : V | z∈B ∧ ¬G.Adj x z ∧ ¬G.Adj y z} : Set V).ncard+
      (G.degree x-q)+(G.degree y-q)

namespace Original
variable {V : Type u} [Fintype V] {G : SimpleGraph V} {A B : Finset V}
variable {h q j : ℕ}

omit [Fintype V] in
lemma outside_card [DecidableEq V] [DecidableRel G.Adj] (x y : V) :
    #(B.filter (fun z => ¬G.Adj x z ∧ ¬G.Adj y z))=
      ({z : V | z∈B ∧ ¬G.Adj x z ∧ ¬G.Adj y z} : Set V).ncard := by
  have he : ({z : V | z∈B ∧ ¬G.Adj x z ∧ ¬G.Adj y z} : Set V)=
      ↑(B.filter (fun z => ¬G.Adj x z ∧ ¬G.Adj y z)) := by
    ext z
    simp only [Set.mem_ofPred_eq,mem_coe,mem_filter]
  rw [he,Set.ncard_coe_finset]

/-- Actual paired degrees are whole original degrees on the covering shore. -/
lemma pair_condition_iff (host : Host h q j G A B) :
    letI : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
    (to_data host).PairCondition↔OriginalPairCondition h q j G A B := by
  classical
  let d := to_data host
  change d.PairCondition↔OriginalPairCondition h q j G A B
  constructor
  · intro hp x hx hxd y hy hyd hxy
    have hxf : x∈d.fragileRows := d.mem_fragile.mpr
      ⟨hx,by rw [dg_eq_degree host.bipartite hx]; exact hxd⟩
    have hyf : y∈d.fragileRows := d.mem_fragile.mpr
      ⟨hy,by rw [dg_eq_degree host.bipartite hy]; exact hyd⟩
    have hs := hp x hxf y hyf hxy
    rw [outside_card x y,dg_eq_degree host.bipartite hx,
      dg_eq_degree host.bipartite hy] at hs
    exact hs

  · intro hp x hx y hy hxy
    obtain ⟨hxA,hxd⟩ := d.mem_fragile.mp hx
    obtain ⟨hyA,hyd⟩ := d.mem_fragile.mp hy
    rw [dg_eq_degree host.bipartite hxA] at hxd
    rw [dg_eq_degree host.bipartite hyA] at hyd
    have hs := hp x hxA hxd y hyA hyd hxy
    rw [outside_card x y,dg_eq_degree host.bipartite hxA,
      dg_eq_degree host.bipartite hyA]
    exact hs

/-- Necessity is paid by actual original subgraph neighbors, not supplied cuts. -/
lemma quota_of_factor (host : Host h q j G A B) {O : Finset V}
    (hOB : O⊆B) (hOj : #O=j) (H : G.Subgraph)
    (hverts : H.verts=(↑(A∪(B\O)) : Set V))
    (hregular : H.coe.IsRegularOfDegree q) :
    letI : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
    (to_data host).QuotaFeasible O := by
  classical
  let d := to_data host
  refine ⟨hOB,hOj,?_⟩
  intro x hx
  have hxA := d.fragile_subset hx
  have hxV : x∈H.verts := by
    rw [hverts]
    exact mem_union_left _ hxA
  have hsub : (H.neighborSet x).toFinset⊆(B\O).filter (fun z => G.Adj x z) := by
    intro z hz
    have hadj : H.Adj x z := by
      simpa only [Set.mem_toFinset,SimpleGraph.Subgraph.mem_neighborSet] using hz
    have hG := H.adj_sub hadj
    have hzB : z∈B := host.bipartite.mem_of_mem_adj hxA hG
    have hzV := H.edge_vert hadj.symm
    rw [hverts] at hzV
    have hzR : z∈B\O := by
      change z∈A∪(B\O) at hzV
      rcases mem_union.mp hzV with hzA|hzR
      · exact False.elim ((disjoint_left.mp host.disjoint hzA) hzB)
      · exact hzR
    exact mem_filter.mpr ⟨hzR,hG⟩
  have hd : H.degree x=q := by
    have hr := hregular ⟨x,hxV⟩
    rw [SimpleGraph.Subgraph.coe_degree] at hr
    exact hr
  have hle := card_le_card hsub
  rw [SimpleGraph.Subgraph.finset_card_neighborSet_eq_degree,hd] at hle
  change q≤dg G (B\O) x at hle
  have hs := dg_sdiff_add (G:=G) hOB x
  omega

end Original

/-- Exact R204 whole-A iff. The same existential omission pays every cut and
supports the actual original factor; no quota-feasible omission is supplied. -/
theorem whole_A_iff (h q j : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) (host : Host h q j G A B) :
    WholeASelection q j G A B↔OriginalPairCondition h q j G A B := by
  classical
  have d := Original.to_data host
  have hpiff := Original.pair_condition_iff host
  constructor
  · rintro ⟨O,hOB,hOj,hcuts,_⟩
    exact hpiff.mp (d.pair_of_quota (d.quota_of_cuts hOB hOj hcuts))
  · intro hp
    have hquota := d.quota_exists (hpiff.mpr hp)
    obtain ⟨O,hOB,hOj,hcuts⟩ :=
      d.common_omission (petal_escape (G:=G)) (top_escape (G:=G)) hquota
    have hfactor := factor_of_common_omission q j host.card hOB hOj hcuts
    have hq := host.parameters.to_parameters.q_pos
    have hA : A.Nonempty := card_pos.mp (by have hs:=d.shores_large.1; omega)
    obtain ⟨H,hverts,hnonempty,hregular⟩ :=
      factor_exact_subgraph hq hA (host.disjoint.mono_right sdiff_subset) hfactor
    exact ⟨O,hOB,hOj,hcuts,H,hverts,hnonempty,hregular⟩

/-- The literal natural ceiling of j/2 suffices, for ALL integer/composite q. -/
theorem minA_half_surplus (h q j : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) (host : Host h q j G A B)
    (hmin : ∀ x∈A, q+(j+1)/2≤G.degree x) : WholeASelection q j G A B := by
  apply (whole_A_iff h q j G A B host).mpr
  intro x hx _ y hy _ _
  have hdx := hmin x hx
  have hdy := hmin y hy
  omega

/-- Literal actual-factor iff, with necessity derived from original neighbor units. -/
theorem original_factor_iff (h q j : ℕ) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) (host : Host h q j G A B) :
    OriginalWholeAFactor q j G A B↔OriginalPairCondition h q j G A B := by
  classical
  constructor
  · rintro ⟨O,hOB,hOj,H,hverts,_,hregular⟩
    have d := Original.to_data host
    have hquota := Original.quota_of_factor host hOB hOj H hverts hregular
    exact (Original.pair_condition_iff host).mp (d.pair_of_quota hquota)
  · intro hp
    obtain ⟨O,hOB,hOj,_,H,hverts,hnonempty,hregular⟩ :=
      (whole_A_iff h q j G A B host).mpr hp
    exact ⟨O,hOB,hOj,H,hverts,hnonempty,hregular⟩

end Erdos585.AllHThirdTwoQuota

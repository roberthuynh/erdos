import Openmath.Erdos642.Proofs.DenseMask20261019.SprinklingProbability
import Openmath.Erdos642.Proofs.DenseMask20261019.InitialMass
import Openmath.Erdos642.Proofs.DenseMask20261019.GallaiDeficiency

/-! Actual cut matchings and escape of a fixed original component union. -/
noncomputable section
namespace Erdos642.DenseMask20261019.CutEscape
open Finset SimpleGraph MeasureTheory ProbabilityTheory Real
open OAI.ErdosGallai.Sampling
open Erdos642.CampaignFe72210b
open Erdos642.CampaignFe72210bContinuation3.CutExtraction
open Erdos642.DenseMask20261019
open ComponentObstruction NestedSampling
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def Expands (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) : Prop :=
  ∀ U : Finset V, 2*U.card ≤ Fintype.card V →
    lam*(U.card : ℝ) ≤ ((closedNeighborhood G U \ U).card : ℝ)

def cutGraph (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ((x ∈ S ∧ y ∉ S) ∨ (y ∈ S ∧ x ∉ S))
  symm := ⟨by intro x y h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro x h; exact G.loopless.irrefl x h.1⟩

theorem exists_maximal_matching (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∃ M : H.Subgraph, M.IsMatching ∧
      ∀ x y, H.Adj x y → x ∈ M.verts ∨ y ∈ M.verts := by
  classical
  let F := (Finset.univ : Finset H.Subgraph).filter (fun M => M.IsMatching)
  have hb : (⊥ : H.Subgraph).IsMatching := by intro v hv; simpa using hv
  obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image F (fun M => M.edgeSet.ncard)
    ⟨⊥, by simp [F, hb]⟩
  have hm := (Finset.mem_filter.mp hM).2
  refine ⟨M, hm, ?_⟩
  intro x y hxy
  by_contra hc
  have hx : x ∉ M.verts := fun h => hc (Or.inl h)
  have hy : y ∉ M.verts := fun h => hc (Or.inr h)
  let E := H.subgraphOfAdj hxy
  have he : E.IsMatching := Subgraph.IsMatching.subgraphOfAdj hxy
  have hd : Disjoint M.support E.support := by
    rw [hm.support_eq_verts, he.support_eq_verts]
    change Disjoint M.verts {x,y}
    rw [Set.disjoint_left]
    intro z hz hzE
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzE
    exact hzE.elim (fun h => hx (h ▸ hz)) (fun h => hy (h ▸ hz))
  have hnew := hm.sup he hd
  have hnewF : M ⊔ E ∈ F := by simp [F, hnew]
  have hmax' := hmax (M ⊔ E) hnewF
  have hnot : s(x,y) ∉ M.edgeSet := fun h => hx ((show M.Adj x y from h).fst_mem)
  have hcard : (M ⊔ E).edgeSet.ncard = M.edgeSet.ncard+1 := by
    rw [Subgraph.edgeSet_sup, SimpleGraph.edgeSet_subgraphOfAdj]
    have heq : M.edgeSet ∪ {s(x,y)} = insert s(x,y) M.edgeSet := by ext z; simp [or_comm]
    rw [heq, Set.ncard_insert_of_notMem hnot]
  omega

/-- An actual matching across an original cut; no regularity hypothesis. -/
theorem cut_matching (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (lam : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hexp : Expands G lam)
    (hS : (S.card : ℝ) ≤ 99*(Fintype.card V : ℝ)/100) :
    ∃ M : (cutGraph G S).Subgraph, M.IsMatching ∧
      lam*(S.card : ℝ)/400 ≤ (M.edgeSet.ncard : ℝ) := by
  classical
  obtain ⟨M, hm, hcover⟩ := exists_maximal_matching (cutGraph G S)
  obtain ⟨X, hXsmall, hSX, hcross⟩ : ∃ X : Finset V,
      2*X.card ≤ Fintype.card V ∧ (S.card : ℝ) ≤ 100*(X.card : ℝ) ∧
      (∀ x ∈ X, ∀ y, y ∉ X → G.Adj x y → (cutGraph G S).Adj x y) := by
    by_cases hs : 2*S.card ≤ Fintype.card V
    · refine ⟨S, hs, ?_, ?_⟩
      · nlinarith [show (0 : ℝ) ≤ S.card by positivity]
      · intro x hx y hy hxy; exact ⟨hxy, Or.inl ⟨hx, hy⟩⟩
    · let X := Finset.univ \ S
      have hc : X.card+S.card = Fintype.card V := by
        simpa [X] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
      have hcR : (X.card : ℝ)+(S.card : ℝ) = Fintype.card V := by exact_mod_cast hc
      refine ⟨X, by omega, by nlinarith, ?_⟩
      intro x hx y hy hxy
      have hxS : x ∉ S := (Finset.mem_sdiff.mp hx).2
      have hyS : y ∈ S := by simpa [X] using hy
      exact ⟨hxy, Or.inr ⟨hyS, hxS⟩⟩
  let R := M.verts.toFinset
  let U := X \ R
  have hr : R.card = 2*M.edgeSet.ncard := by
    change M.verts.toFinset.card = _
    rw [← Set.ncard_eq_toFinset_card']
    exact GallaiDeficiency.matching_card hm
  have hUX : U ⊆ X := Finset.sdiff_subset
  have hUsmall : 2*U.card ≤ Fintype.card V := by
    have hc := Finset.card_le_card hUX
    omega
  have hb : closedNeighborhood G U \ U ⊆ R := by
    intro z hz
    obtain ⟨hzPhi, hzU⟩ := Finset.mem_sdiff.mp hz
    have hn : ∃ x ∈ U, G.Adj x z := by
      rcases Finset.mem_union.mp hzPhi with h | h
      · exact False.elim (hzU h)
      · obtain ⟨x, hx, hz⟩ := Finset.mem_biUnion.mp h
        exact ⟨x, hx, (G.mem_neighborFinset x z).mp hz⟩
    obtain ⟨x, hx, hxy⟩ := hn
    by_contra hzR
    have hxX : x ∈ X := hUX hx
    have hxM : x ∉ M.verts := by
      have hxR := (Finset.mem_sdiff.mp hx).2
      simpa [R] using hxR
    have hzM : z ∉ M.verts := by simpa [R] using hzR
    have hzX : z ∈ X := by
      by_contra hzX
      exact (hcover x z (hcross x hxX z hzX hxy)).elim hxM hzM
    exact hzU (Finset.mem_sdiff.mpr ⟨hzX, hzR⟩)
  have hbd : ((closedNeighborhood G U \ U).card : ℝ) ≤ 2*(M.edgeSet.ncard : ℝ) := by
    exact_mod_cast (Finset.card_le_card hb).trans_eq hr
  have hXsub : X ⊆ U ∪ R := by
    intro x hx
    by_cases hxR : x ∈ R
    · exact Finset.mem_union_right _ hxR
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxR⟩)
  have hxc : (X.card : ℝ) ≤ (U.card : ℝ)+2*(M.edgeSet.ncard : ℝ) := by
    have hc := (Finset.card_le_card hXsub).trans (Finset.card_union_le U R)
    rw [hr] at hc
    exact_mod_cast hc
  have he := hexp U hUsmall
  have hxmul := mul_le_mul_of_nonneg_left hxc hlam
  have hml := mul_le_mul_of_nonneg_right hlam1 (by positivity : 0 ≤ 2*(M.edgeSet.ncard : ℝ))
  have hx : lam*(X.card : ℝ) ≤ 4*(M.edgeSet.ncard : ℝ) := by nlinarith
  have hsx := mul_le_mul_of_nonneg_left hSX hlam
  refine ⟨M, hm, ?_⟩
  linarith

private theorem degree_univ (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    restrictedDegree G Finset.univ v = G.degree v := by
  unfold restrictedDegree
  congr 1
  ext w
  simp

/-- Incidences use the degree cap at EVERY original center. -/
theorem phi_order (G : SimpleGraph V) [DecidableRel G.Adj] (Q B : Finset V)
    (p d D k : ℝ) (hd : 0 < d) (hBQ : B ⊆ Q)
    (hdeg : ∀ v, d ≤ (G.degree v : ℝ))
    (hcap : ∀ v, (restrictedDegree G Q v : ℝ) ≤ 2*D*p*d)
    (hB : k/5 ≤ (B.card : ℝ)) :
    k ≤ 10*D*p*((closedNeighborhood G B).card : ℝ) := by
  let P := closedNeighborhood G B
  have hc (v : V) : (restrictedDegree G B v : ℝ) ≤ 2*D*p*d := by
    exact (show (restrictedDegree G B v : ℝ) ≤ restrictedDegree G Q v from by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hBQ)).trans (hcap v)
  have hrestrict : IncidenceCounts.count G B Finset.univ = IncidenceCounts.count G B P := by
    unfold IncidenceCounts.count
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hxy
      exact ⟨Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨x, hx, (G.mem_neighborFinset x y).mpr hxy⟩), hxy⟩
    · exact fun h => h.2
  have hlo : d*(B.card : ℝ) ≤ (IncidenceCounts.count G B Finset.univ : ℝ) := by
    calc
      _ = ∑ v ∈ B, d := by simp [mul_comm]
      _ ≤ ∑ v ∈ B, (restrictedDegree G Finset.univ v : ℝ) :=
        Finset.sum_le_sum (fun v _ => by simpa [degree_univ] using hdeg v)
      _ = _ := by simp [restrictedDegree, IncidenceCounts.count]
  have hhi : (IncidenceCounts.count G P B : ℝ) ≤ (P.card : ℝ)*(2*D*p*d) := by
    calc
      _ = ∑ v ∈ P, (restrictedDegree G B v : ℝ) := by simp [restrictedDegree, IncidenceCounts.count]
      _ ≤ ∑ _v ∈ P, 2*D*p*d := Finset.sum_le_sum (fun v _ => hc v)
      _ = _ := by simp [mul_comm]
  rw [hrestrict, IncidenceCounts.count_swap] at hlo
  have hprod : d*(B.card : ℝ) ≤ d*(2*D*p*(P.card : ℝ)) := by nlinarith
  have hh := (mul_le_mul_iff_right₀ hd).mp hprod
  nlinarith

private theorem subset_reached (G : SimpleGraph V) [DecidableRel G.Adj]
    (M B : Finset V) (hBM : B ⊆ M) : B ⊆ componentUnion G M B := by
  intro b hb
  apply (mem_componentUnion G M B b).mpr
  exact ⟨hBM hb, b, Finset.mem_inter.mpr ⟨hBM hb, hb⟩, Reachable.rfl⟩

private theorem phi_neighbor (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) {u : V} (hu : u ∈ closedNeighborhood G B \ B) :
    ∃ b ∈ B, G.Adj b u := by
  obtain ⟨hphi, hnb⟩ := Finset.mem_sdiff.mp hu
  rcases Finset.mem_union.mp hphi with h | h
  · exact False.elim (hnb h)
  · obtain ⟨b, hb, hbu⟩ := Finset.mem_biUnion.mp h
    exact ⟨b, hb, (G.mem_neighborFinset b u).mp hbu⟩

private theorem neighbor_reached (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q B Z : Finset V) (hBQ : B ⊆ Q) :
    (closedNeighborhood G B \ B) ∩ Z ⊆ componentUnion G (Q ∪ Z) B := by
  intro u hu
  obtain ⟨huS, huZ⟩ := Finset.mem_inter.mp hu
  obtain ⟨b, hb, hbu⟩ := phi_neighbor G B huS
  have hbM : b ∈ Q ∪ Z := Finset.mem_union_left _ (hBQ hb)
  have huM : u ∈ Q ∪ Z := Finset.mem_union_right _ huZ
  exact (mem_componentUnion G (Q ∪ Z) B u).mpr ⟨huM, b, Finset.mem_inter.mpr ⟨hbM, hb⟩,
    (show (mask G (Q ∪ Z)).Adj b u from ⟨hbu, hbM, huM⟩).reachable⟩

/-- A fixed original seed union escapes its original neighborhood after exact sprinkling.
The conclusion uses ALL reached components in the enlarged original mask. -/
theorem fixed_union_escape (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q B : Finset V) (p : unitInterval) (d D lam k : ℝ)
    (hp : 0 < (p : ℝ)) (hd : 0 < d) (hD : 1 ≤ D)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hexp : Expands G lam)
    (hk : 0 < k) (hkN : k ≤ 3*(p : ℝ)*(Fintype.card V : ℝ)/5)
    (hBQ : B ⊆ Q) (hdeg : ∀ v, d ≤ (G.degree v : ℝ))
    (hcap : ∀ v, (restrictedDegree G Q v : ℝ) ≤ 2*D*(p : ℝ)*d)
    (hBlo : k/5 ≤ (B.card : ℝ)) (hBhi : (B.card : ℝ) ≤ 9*k/17) :
    (sampleMeasure V (sprinkle p)).real {z |
      ((componentUnion G (Q ∪ sampleVertices z) B).card : ℝ) ≤ 9*k/17 ∧
      componentUnion G (Q ∪ sampleVertices z) B ⊆ closedNeighborhood G B} ≤
        exp (-(p : ℝ)*lam*k/(128000*D)) := by
  let n : ℝ := Fintype.card V
  let P := closedNeighborhood G B
  let S := P \ B
  let r := sprinkle p
  have hp0 := p.property.1
  have hp1 := p.property.2
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hD0 : 0 < D := by linarith
  have hden : 0 < 4-(p : ℝ) := by linarith
  have hr : (r : ℝ) = (p : ℝ)/(4-(p : ℝ)) := rfl
  have hrlo : (p : ℝ)/4 ≤ (r : ℝ) := by
    rw [hr, le_div_iff₀ hden]
    nlinarith
  have hBP : B ⊆ P := Finset.subset_union_left
  have hcard : (S.card : ℝ)+(B.card : ℝ) = P.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hBP
  by_cases hlarge : 99*n/100 ≤ (P.card : ℝ)
  · have hpN : 0 ≤ (p : ℝ)*n := mul_nonneg hp0 hn
    have hpNle : (p : ℝ)*n ≤ n := by nlinarith
    have hBpn : (B.card : ℝ) ≤ 27*(p : ℝ)*n/85 := by linarith
    have hsize : 11*n*(4-(p : ℝ))/50 ≤ (S.card : ℝ) := by nlinarith
    have hmean : 11*((p : ℝ)*n)/50 ≤ (r : ℝ)*(S.card : ℝ) := by
      rw [hr, div_mul_eq_mul_div, le_div_iff₀ hden]
      nlinarith [mul_le_mul_of_nonneg_left hsize hp0]
    have hsub : {z | ((componentUnion G (Q ∪ sampleVertices z) B).card : ℝ) ≤ 9*k/17 ∧
        componentUnion G (Q ∪ sampleVertices z) B ⊆ P} ⊆
        {z | ((S ∩ sampleVertices z).card : ℝ) ≤ ((p : ℝ)*n)/5} := by
      intro z hz
      have hBS : Disjoint B (S ∩ sampleVertices z) := by
        apply Finset.disjoint_left.mpr
        intro b hb hbs
        exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hbs).1).2 hb
      have hBreach := subset_reached G (Q ∪ sampleVertices z) B
        (fun b hb => Finset.mem_union_left _ (hBQ hb))
      have hSreach := neighbor_reached G Q B (sampleVertices z) hBQ
      have hc := Finset.card_le_card (Finset.union_subset hBreach hSreach)
      rw [Finset.card_union_of_disjoint hBS] at hc
      have hcR : (B.card : ℝ)+((S ∩ sampleVertices z).card : ℝ) ≤
          (componentUnion G (Q ∪ sampleVertices z) B).card := by exact_mod_cast hc
      change ((S ∩ sampleVertices z).card : ℝ) ≤ ((p : ℝ)*n)/5
      have hbad := hz.1
      linarith
    calc
      _ ≤ (sampleMeasure V r).real {z | ((S ∩ sampleVertices z).card : ℝ) ≤ ((p : ℝ)*n)/5} :=
        measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ exp (-((p : ℝ)*n)/2000) :=
        SprinklingProbability.count_lower_tail r S ((p : ℝ)*n) hpN hmean
      _ ≤ _ := by
        apply exp_le_exp.mpr
        have hlamk : lam*k ≤ k := by nlinarith
        have hpnk : (p : ℝ)*lam*k ≤ (p : ℝ)*k := by nlinarith
        have hpk : (p : ℝ)*k ≤ k := by nlinarith
        apply (le_div_iff₀ (by positivity : 0 < 128000*D)).mpr
        nlinarith [mul_le_mul_of_nonneg_left hD hpN]
  · have hsmall : (P.card : ℝ) ≤ 99*n/100 := (lt_of_not_ge hlarge).le
    obtain ⟨M, hM, hMc⟩ := cut_matching G P lam hlam.le hlam1 hexp hsmall
    have hphi := phi_order G Q B (p : ℝ) d D k hd hBQ hdeg hcap hBlo
    have hbound : lam*k ≤ 4000*D*(p : ℝ)*(M.edgeSet.ncard : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_left hphi hlam.le
      have h2 := mul_le_mul_of_nonneg_left hMc (by positivity : 0 ≤ 10*D*(p : ℝ))
      nlinarith
    have hsub : {z | ((componentUnion G (Q ∪ sampleVertices z) B).card : ℝ) ≤ 9*k/17 ∧
        componentUnion G (Q ∪ sampleVertices z) B ⊆ P} ⊆
        {z | ∀ u v, M.Adj u v → ¬ (u ∈ sampleVertices z ∧ v ∈ sampleVertices z)} := by
      intro z hz u v huv huvZ
      have he := M.adj_sub huv
      have hescape (x y : V) (hxy : G.Adj x y) (hxP : x ∈ P) (hyP : y ∉ P)
          (hxZ : x ∈ sampleVertices z) (hyZ : y ∈ sampleVertices z) : False := by
        have hxB : x ∉ B := by
          intro hxB
          apply hyP
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨x, hxB, (G.mem_neighborFinset x y).mpr hxy⟩)
        obtain ⟨b, hb, hbx⟩ := phi_neighbor G B (Finset.mem_sdiff.mpr ⟨hxP, hxB⟩)
        have hbM : b ∈ Q ∪ sampleVertices z := Finset.mem_union_left _ (hBQ hb)
        have hxM : x ∈ Q ∪ sampleVertices z := Finset.mem_union_right _ hxZ
        have hyM : y ∈ Q ∪ sampleVertices z := Finset.mem_union_right _ hyZ
        have hbxM : (mask G (Q ∪ sampleVertices z)).Adj b x := ⟨hbx, hbM, hxM⟩
        have hxyM : (mask G (Q ∪ sampleVertices z)).Adj x y := ⟨hxy, hxM, hyM⟩
        have hyreach : y ∈ componentUnion G (Q ∪ sampleVertices z) B :=
          (mem_componentUnion G (Q ∪ sampleVertices z) B y).mpr ⟨hyM, b, Finset.mem_inter.mpr ⟨hbM, hb⟩,
            hbxM.reachable.trans hxyM.reachable⟩
        exact hyP (hz.2 hyreach)
      rcases he.2 with h | h
      · exact hescape u v he.1 h.1 h.2 huvZ.1 huvZ.2
      · exact hescape v u he.1.symm h.1 h.2 huvZ.2 huvZ.1
    calc
      _ ≤ (sampleMeasure V r).real {z | ∀ u v, M.Adj u v →
          ¬ (u ∈ sampleVertices z ∧ v ∈ sampleVertices z)} :=
        measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ exp (-(r : ℝ)^2*(M.edgeSet.ncard : ℝ)/2) :=
        SprinklingProbability.matching_no_hit_adj (cutGraph G P) M hM r
      _ ≤ _ := by
        apply exp_le_exp.mpr
        apply (le_div_iff₀ (by positivity : 0 < 128000*D)).mpr
        have hr0 := r.property.1
        have hrsq : (p : ℝ)^2 ≤ 16*(r : ℝ)^2 := by nlinarith
        have h1 := mul_le_mul_of_nonneg_left hbound hp0
        have h2 := mul_le_mul_of_nonneg_left hrsq
          (by positivity : 0 ≤ 4000*D*(M.edgeSet.ncard : ℝ))
        nlinarith

end Erdos642.DenseMask20261019.CutEscape

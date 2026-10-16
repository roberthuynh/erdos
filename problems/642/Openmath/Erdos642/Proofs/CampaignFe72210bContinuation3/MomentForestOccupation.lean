import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.GraphSmoothingOccupation
import Openmath.Erdos642.Proofs.CampaignFe72210b.GraphForestFirstStage

/-! Joint parity transfer and the actual fixed leaf-union first-stage event. -/
namespace Erdos642.CampaignFe72210bContinuation3.MomentForestOccupation
open SimpleGraph Matrix Erdos642.FiniteMarkov Erdos642.OccupationTail
open Erdos642.CampaignFe72210b
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A joint family event loses no extra family factor when an unused suffix is integrated out. -/
theorem family_prefix_le (C : Chain V) (s : Set V) [DecidablePred (· ∈ s)]
    (S : Finset (Finset s)) (L l : ℕ) (hl : l ≤ L) (a : ℝ) (x : V) :
    C.eventMass L (fun y p => ∃ T ∈ S, occupation (ambientShoreSet s T) y p < a) x ≤
    C.eventMass l (fun y p => ∃ T ∈ S, occupation (ambientShoreSet s T) y p < a) x := by
  have hm := C.eventMass_mono
    (fun y p => ∃ T ∈ S, occupation (ambientShoreSet s T) y p < a)
    (fun y p => ∃ T ∈ S, occupation (ambientShoreSet s T) y (PathSplit.split l (L-l) p).1 < a)
    (by intro y p hp; obtain ⟨T,hT,hp⟩ := hp; exact ⟨T,hT,
      lt_of_le_of_lt (occupation_prefix_le C (ambientShoreSet s T) l (L-l) y p) hp⟩) x
  have he : L-l+l=L := Nat.sub_add_cancel hl
  have ht := hm.trans_eq (C.eventMass_prefix l (L-l) (fun y p => ∃ T ∈ S, occupation (ambientShoreSet s T) y p < a) x)
  rw [he] at ht
  exact ht

variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (s : Set V) [DecidablePred (· ∈ s)] [Nonempty s]

omit [Nonempty s] in
/-- Joint even-sample transfer for an entire fixed family, without a second union. -/
theorem same_shore_family_sample_bound (t : Set V) (hbi : G.IsBipartiteWith s t)
    (hdeg : ∀ x : V, 0 < G.degree x) (S : Finset (Finset s))
    (n L : ℕ) (hfit : 2*n ≤ L) (a c B : ℝ) (hac : a ≤ c)
    (hshore : ∀ x : s, (shoreChain G s t hbi hdeg).eventMass n
      (fun y p => ∃ T ∈ S, occupation T y p ≤ c) x ≤ B) (x : s) :
    (graphChain G hdeg).eventMass L
      (fun y p => ∃ T ∈ S, occupation (ambientShoreSet s T) y p < a) x.val ≤ B := by
  apply (family_prefix_le (graphChain G hdeg) s S L (2*n) hfit a x.val).trans
  have hm := (graphChain G hdeg).eventMass_mono
    (fun y p => ∃ T ∈ S, occupation (ambientShoreSet s T) y p < a)
    (fun y p => ∃ T ∈ S, occupation (ambientShoreSet s T) y (sampleEvenTwoMul n p) ≤ c)
    (by
      intro y p hp
      obtain ⟨T,hT,hp⟩ := hp
      exact ⟨T,hT,(occupation_even_sample_le (ambientShoreSet s T) n y p).trans (hp.le.trans hac)⟩) x.val
  apply hm.trans
  have he := graph_even_shore_eventMass s G t hbi hdeg n
    (fun y p => ∃ T ∈ S, occupation (ambientShoreSet s T) y p ≤ c) x
  rw [he]
  simpa only [occupation_map_shore] using hshore x

theorem family_succ_le (C : Chain V) (s : Set V) [DecidablePred (· ∈ s)]
    (S : Finset (Finset s)) (n : ℕ) (a : ℝ) (x : V) :
    C.eventMass (n+1) (fun y p => ∃ T ∈ S, occupation (ambientShoreSet s T) y p < a) x ≤
      ∑ y, C.transition x y * C.eventMass n
        (fun z p => ∃ T ∈ S, occupation (ambientShoreSet s T) z p < a) y := by
  have hm := C.eventMass_mono (n := n+1)
    (fun y p => ∃ T ∈ S, occupation (ambientShoreSet s T) y p < a)
    (fun _ p => ∃ T ∈ S, occupation (ambientShoreSet s T) p.1 p.2 < a) (by
      intro y p hp
      obtain ⟨T,hT,hp⟩ := hp
      refine ⟨T,hT,?_⟩
      change (if y ∈ ambientShoreSet s T then 1 else 0) + occupation (ambientShoreSet s T) p.1 p.2 < a at hp
      split_ifs at hp <;> linarith) x
  exact hm.trans_eq (by rw [eventMass_succ]; rfl)

omit [Nonempty s] in
/-- Actual first-step averaging for starts outside the sampled shore, jointly for the fixed family. -/
theorem graph_family_sample_bound (t : Set V) (hbi : G.IsBipartiteWith s t)
    (hdeg : ∀ x : V, 0 < G.degree x) (S : Finset (Finset s))
    (n L : ℕ) (hfit : 2*n+1 ≤ L) (a c B : ℝ) (hac : a ≤ c) (_hB : 0 ≤ B)
    (hshore : ∀ x : s, (shoreChain G s t hbi hdeg).eventMass n
      (fun y p => ∃ T ∈ S, occupation T y p ≤ c) x ≤ B) (x : V) :
    (graphChain G hdeg).eventMass L
      (fun y p => ∃ T ∈ S, occupation (ambientShoreSet s T) y p < a) x ≤ B := by
  by_cases hx : x ∈ s
  · exact same_shore_family_sample_bound G s t hbi hdeg S n L (by omega) a c B hac hshore ⟨x,hx⟩
  · have hL : L-1+1=L := by omega
    have hm := family_succ_le (graphChain G hdeg) s S (L-1) a x
    rw [hL] at hm
    apply hm.trans
    calc
      _ ≤ ∑ y, (graphChain G hdeg).transition x y * B := by
        apply Finset.sum_le_sum
        intro y _
        by_cases hy : y ∈ s
        · exact mul_le_mul_of_nonneg_left
            (same_shore_family_sample_bound G s t hbi hdeg S n (L-1) (by omega)
              a c B hac hshore ⟨y,hy⟩) ((graphChain G hdeg).nonneg x y)
        · have hxy : ¬ G.Adj x y := by
            intro hadj
            rcases hbi.mem_of_adj hadj with hh | hh
            · exact hx hh.1
            · exact hy hh.2
          have hz : (graphChain G hdeg).transition x y = 0 := by
            simp [graphChain, graphTransition, SimpleGraph.adjMatrix_apply, hxy]
          simp [hz]
      _ = B := by rw [← Finset.sum_mul, (graphChain G hdeg).row_sum, one_mul]

section Forest
variable {G} {A B : Finset V} {q m b : ℕ}
variable (F : ForestBundle G A B q m b)

noncomputable def shoreLeafUnion (f : Fin q) (J : Finset (Fin m)) : Finset (B:Set V) :=
  (F.leafUnion f J).subtype (fun v => v ∈ B)

omit [Fintype V] [DecidableRel G.Adj] in
@[simp] theorem ambient_shoreLeafUnion (f : Fin q) (J : Finset (Fin m)) :
    ambientShoreSet (B:Set V) (shoreLeafUnion F f J) = F.leafUnion f J := by
  exact Finset.subtype_map_of_mem (F.leafUnion_subset f J)

omit [Fintype V] [DecidableRel G.Adj] in
theorem shoreLeafUnion_card (f : Fin q) (J : Finset (Fin m)) :
    (shoreLeafUnion F f J).card = J.card*b := by
  have hh := congrArg Finset.card (ambient_shoreLeafUnion F f J)
  simpa only [ambientShoreSet, Finset.card_map, F.leafUnion_card] using hh

noncomputable def leafFamily (h : ℕ) : Finset (Finset (B:Set V)) := by
  classical
  exact ((Finset.univ : Finset (Fin q)).product
    ((Finset.univ : Finset (Fin m)).powersetCard h)).image
      (fun i => shoreLeafUnion F i.1 i.2)

noncomputable def indicatorFamily (h : ℕ) : Finset ({v : V // v ∈ B} → ℝ) := by
  classical
  exact (leafFamily F h).image (fun (T : Finset {v : V // v ∈ B}) (y : {v : V // v ∈ B}) => if y ∈ T then (1:ℝ) else 0)

omit [Fintype V] [DecidableRel G.Adj] in
theorem leafFamily_card_le (h : ℕ) : (leafFamily F h).card ≤ q*2^m := by
  classical
  unfold leafFamily
  apply Finset.card_image_le.trans
  change (Finset.univ ×ˢ (Finset.univ : Finset (Fin m)).powersetCard h).card ≤ q*2^m
  rw [Finset.card_product]
  have hh : ((Finset.univ : Finset (Fin m)).powersetCard h).card ≤ 2^m := by
    calc
      _ ≤ ((Finset.univ : Finset (Fin m)).powerset).card := Finset.card_le_card (by
        intro J hJ
        exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hJ).1)
      _ = _ := by simp
  simpa using Nat.mul_le_mul_left q hh

omit [Fintype V] [DecidableRel G.Adj] in
theorem indicatorFamily_card_le (h : ℕ) : (indicatorFamily F h).card ≤ q*2^m := by
  classical
  exact Finset.card_image_le.trans (leafFamily_card_le F h)

omit [Fintype V] [DecidableRel G.Adj] in
theorem leafFamily_member_card (h : ℕ) (T : Finset (B:Set V)) (hT : T ∈ leafFamily F h) :
    T.card = h*b := by
  classical
  obtain ⟨⟨f,J⟩,hi,rfl⟩ := Finset.mem_image.mp hT
  have hj := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hi).2).2
  rw [shoreLeafUnion_card, hj]

omit [DecidableRel G.Adj] in
/-- Strict bad-star union containment uses the actual 600 denominator, not an old half-mean bound. -/
theorem bad_half_subset_family (L : ℕ) (_hL : 1 ≤ L) (_hN : 0 < (Fintype.card V:ℝ))
    (hm : 1 ≤ m) (x : V) (p : Path V (L-1))
    (hbad : ∃ f : Fin q, (m+1)/2 ≤
      (F.badInForest f ((L:ℝ)*(b:ℝ)/(600*(Fintype.card V:ℝ))) x p).card) :
    ∃ T ∈ leafFamily F ((m+1)/2), occupation (ambientShoreSet (B:Set V) T) x p <
      (L:ℝ)*(((m+1)/2*b:ℕ):ℝ)/(600*(Fintype.card V:ℝ)) := by
  classical
  obtain ⟨f,hbad⟩ := hbad
  obtain ⟨J,hJ,hbadJ⟩ := F.bad_subset_exists f _ x p ((m+1)/2) hbad
  have hJnonempty : J.Nonempty := Finset.card_pos.mp (by omega)
  have hh := F.bad_leafUnion_occupation_lt f J hJnonempty _ x p hbadJ
  refine ⟨shoreLeafUnion F f J, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨(f,J), Finset.mem_product.mpr
      ⟨Finset.mem_univ _, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hJ⟩⟩,rfl⟩
  · rw [ambient_shoreLeafUnion]
    convert hh using 1; rw [hJ]; push_cast; ring

variable (G)
variable [Nonempty (B:Set V)]

attribute [-instance] FinsetCoe.fintype in
/-- Raw actual ordinary first-stage bound. The only smoothing input is a scalar condition on r;
all graph rank/tail/family/mean/parity and bad-half containment are derived. -/
theorem graph_bad_half_raw (hbi : G.IsBipartiteWith (B:Set V) (A:Set V))
    (hdeg : ∀ x : V, 0 < G.degree x) (γ d Λ : ℝ)
    (hgap : HasBipartiteSpectralGap G γ) (hd : 0 < d) (hΛ : 1 ≤ Λ)
    (hmin : ∀ x : V, d ≤ (G.degree x:ℝ)) (hmax : ∀ x : V, (G.degree x:ℝ) ≤ 100*d)
    (hmoment : ∀ x : V, (graphTransition G^4) x x ≤ Λ/d^2)
    (hq : 1 ≤ q) (hm : 1 ≤ m) (hb : 1 ≤ b)
    (r : ℕ) (hr : 1 ≤ r)
    (hrsmall : Real.sqrt (50*Λ*(Fintype.card V:ℝ))/d*(1/4:ℝ)^(r-1) ≤
      ((((m+1)/2*b:ℕ):ℝ)/(50*(Fintype.card V:ℝ)))/1024)
    (L : ℕ) (hL : 2 ≤ L) :
    ∃ D : ℕ, 1 ≤ D ∧ D ≤ Fintype.card V ∧ (D:ℝ) ≤ 16*Λ*(Fintype.card V:ℝ)/d^2 ∧
      ∀ x : V, (graphChain G hdeg).eventMass (L-1)
        (fun y p => ∃ f : Fin q, (m+1)/2 ≤
          (F.badInForest f ((L:ℝ)*(b:ℝ)/(600*(Fintype.card V:ℝ))) y p).card) x ≤
      ((q:ℝ)*2^m)*(1+((((m+1)/2*b:ℕ):ℝ)/(50*(Fintype.card V:ℝ)))/16)*
        Real.exp (-((((m+1)/2*b:ℕ):ℝ)/(50*(Fintype.card V:ℝ)))^2*(L/2:ℕ)/(256*(r:ℝ))) +
      (CoordinateGrid.alphabet (Fintype.card V) ((((m+1)/2*b:ℕ):ℝ)/(50*(Fintype.card V:ℝ)))^D:ℕ)*
        (⌈2/(((((m+1)/2*b:ℕ):ℝ)/(50*(Fintype.card V:ℝ)))/1024)⌉₊:ℝ)*
        (100*(Fintype.card V:ℝ))*Real.exp
          (-γ*((((m+1)/2*b:ℕ):ℝ)/(50*(Fintype.card V:ℝ)))*(L/2:ℕ)/65536) := by
  classical
  let h := (m+1)/2
  let n := L/2
  let μ : ℝ := ((h*b:ℕ):ℝ)/(50*(Fintype.card V:ℝ))
  have hhh : 1 ≤ h := by dsimp [h]; omega
  have hhm : h ≤ m := by dsimp [h]; omega
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hfit : 2*(n-1)+1 ≤ L-1 := by dsimp [n]; omega
  have hcount : (L:ℝ) ≤ 3*(n:ℝ) := by exact_mod_cast (show L ≤ 3*n by dsimp [n]; omega)
  have hNV : 0 < Fintype.card V := by
    let z : (B:Set V) := Classical.choice inferInstance
    have : Nonempty V := ⟨z.val⟩
    exact Fintype.card_pos
  have hN : 0 < (Fintype.card V:ℝ) := by exact_mod_cast hNV
  have hμ : 0 < μ := by dsimp [μ]; positivity
  obtain ⟨J,_,hJ⟩ := Finset.exists_subset_card_eq
    (show h ≤ (Finset.univ : Finset (Fin m)).card by simpa using hhm)
  let f0 : Fin q := ⟨0,by omega⟩
  have hsize : h*b ≤ Fintype.card V := by
    have hh := (F.leafUnion f0 J).card_le_univ
    simpa only [F.leafUnion_card, hJ] using hh
  have hμ1 : μ ≤ 1 := by
    dsimp [μ]
    apply (div_le_iff₀ (by positivity : 0 < 50*(Fintype.card V:ℝ))).mpr
    have hh : ((h*b:ℕ):ℝ) ≤ (Fintype.card V:ℝ) := by exact_mod_cast hsize
    nlinarith
  have hfunctions : ∀ f ∈ indicatorFamily F h, ∀ y, 0 ≤ f y ∧ f y ≤ 1 := by
    intro f hff y
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hff
    dsimp only
    split_ifs <;> norm_num
  have hmean : ∀ f ∈ indicatorFamily F h, μ ≤ ∑ y, shoreRoot G (B:Set V) y^2*f y := by
    intro f hff
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hff
    have hh := shore_mass_lower G (B:Set V) (A:Set V) hbi hdeg d hd hmin hmax T
    rw [leafFamily_member_card F h T hT] at hh
    simpa only [Erdos642.TiltedOperator.mass, mul_ite, mul_one, mul_zero] using hh
  obtain ⟨D,hD,hDN,hRank,hprob⟩ := GraphSmoothingOccupation.graph_shore_family_tail G
    (B:Set V) (A:Set V) hbi hdeg γ d Λ hgap hd hΛ hmin hmax hmoment
    (indicatorFamily F h) hfunctions μ hμ hμ1 hmean r hr hrsmall
  let C0 : ℝ := ((q:ℝ)*2^m)*(1+μ/16)*Real.exp (-μ^2*(n:ℝ)/(256*(r:ℝ))) +
    (CoordinateGrid.alphabet (Fintype.card V) μ^D:ℕ)*(⌈2/(μ/1024)⌉₊:ℝ)*
      (100*(Fintype.card V:ℝ))*Real.exp (-γ*μ*(n:ℝ)/65536)
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hshore : ∀ y : (B:Set V), (shoreChain G (B:Set V) (A:Set V) hbi hdeg).eventMass (n-1)
      (fun z p => ∃ T ∈ leafFamily F h, occupation T z p ≤ μ*(n:ℝ)/4) y ≤ C0 := by
    intro y
    have he : (fun (z : (B:Set V)) (p : Path (B:Set V) (n-1)) => ∃ T ∈ leafFamily F h, occupation T z p ≤ μ*(n:ℝ)/4) =
      (fun (z : (B:Set V)) (p : Path (B:Set V) (n-1)) => ∃ f ∈ indicatorFamily F h, Chain.vertexSum f z p ≤ μ*(n:ℝ)/4) := by
      funext z p
      apply propext
      constructor
      · rintro ⟨T,hT,hp⟩
        exact ⟨(fun v => if v ∈ T then (1:ℝ) else 0), Finset.mem_image.mpr ⟨T,hT,rfl⟩,hp⟩
      · rintro ⟨f,hff,hp⟩
        obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hff
        exact ⟨T,hT,hp⟩
    rw [he]
    apply (hprob n hn y).trans
    dsimp only [C0]
    apply add_le_add ?_ le_rfl
    have hc : ((indicatorFamily F h).card:ℝ) ≤ (q:ℝ)*2^m := by
      exact_mod_cast indicatorFamily_card_le F h
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (Real.exp_nonneg _)
  have ha : (L:ℝ)*((h*b:ℕ):ℝ)/(600*(Fintype.card V:ℝ)) ≤ μ*(n:ℝ)/4 := by
    have hh := mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg (h*b):0≤((h*b:ℕ):ℝ))
    calc
      _ ≤ (3*(n:ℝ))*((h*b:ℕ):ℝ)/(600*(Fintype.card V:ℝ)) :=
        div_le_div_of_nonneg_right hh (by positivity)
      _ = _ := by dsimp [μ]; ring
  refine ⟨D,hD,hDN,hRank,?_⟩
  intro x
  have hc := (graphChain G hdeg).eventMass_mono
    (fun y p => ∃ f : Fin q, h ≤ (F.badInForest f ((L:ℝ)*(b:ℝ)/(600*(Fintype.card V:ℝ))) y p).card)
    (fun y p => ∃ T ∈ leafFamily F h, occupation (ambientShoreSet (B:Set V) T) y p <
      (L:ℝ)*((h*b:ℕ):ℝ)/(600*(Fintype.card V:ℝ)))
    (fun y p hp => bad_half_subset_family F L (by omega) hN hm y p hp) x
  have ht := graph_family_sample_bound G (B:Set V) (A:Set V) hbi hdeg (leafFamily F h)
    (n-1) (L-1) hfit ((L:ℝ)*((h*b:ℕ):ℝ)/(600*(Fintype.card V:ℝ)))
    (μ*(n:ℝ)/4) C0 ha hC0 (by simpa only [Nat.sub_add_cancel hn] using hshore) x
  exact hc.trans ht

end Forest
end Erdos642.CampaignFe72210bContinuation3.MomentForestOccupation

import R837.Budget
import NEQAssembly.Counts
import Openmath.Proofs.PaperSupport.BqMain
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.R882.Normalization
open QB4 R837 B5 NEQAssembly
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}
def F (h q : ℕ) : ℕ := h*q-16*h^2
lemma cutoff (h q : ℕ) (_hh : 6 ≤ h) (hq : 4096*(h+1)^2 ≤ q) : 32*h ≤ q := by
  nlinarith [sq_nonneg (h+1)]
lemma F_cast {h q : ℕ} (hq : 32*h ≤ q) : (F h q : ℤ) = (h:ℤ)*q-16*h^2 := by
  have hm := Nat.mul_le_mul_left h hq
  have hc : 16*h^2 ≤ h*q := by nlinarith
  unfold F
  rw [Nat.cast_sub hc]
  push_cast
  ring
omit [Fintype V] [DecidableEq V] in
lemma small_floor {h q : ℕ} (hh : 6 ≤ h) (hq : 32*h ≤ q)
    (X Y : Finset V) (hl : h ≤ #X+#Y) (hs : #X+#Y ≤ 2*q) :
    (h:ℤ)*q-16*h^2+1 ≤ deficit G (q-1) (X,Y) := by
  have hp := R837.edge_bound (G := G) X Y
  have sq := sq_nonneg ((#X:ℤ)-#Y)
  have p := mul_nonneg (show 0 ≤ (#X:ℤ)+#Y-h by omega)
    (show 0 ≤ 2*(q:ℤ)-((#X:ℤ)+#Y) by omega)
  have t := mul_nonneg (show 0 ≤ 2*(q:ℤ)-h-4 by omega)
    (show 0 ≤ (#X:ℤ)+#Y-h by omega)
  have pred : ((q-1:ℕ):ℤ)=(q:ℤ)-1 := by omega
  unfold deficit order
  dsimp
  rw [pred]
  zify at hp
  nlinarith
def Dense (h q : ℕ) (G : SimpleGraph V) (A B : Finset V) (S : Support V) : Prop :=
  Included S (A,B) ∧ 2*q ≤ order S ∧ deficit G (q-1) S ≤ F h q
omit [Fintype V] [DecidableEq V] in
lemma minimal_dense {h q : ℕ} {A B : Finset V}
    (hn : 2*q ≤ order (A,B)) (he : deficit G (q-1) (A,B) ≤ F h q) :
    ∃ S, Dense h q G A B S ∧
      ∀ T, Dense h q G A B T → order S ≤ order T := by
  let fam := (A.powerset ×ˢ B.powerset).filter (Dense h q G A B)
  have hseed : (A,B) ∈ fam := by
    apply mem_filter.mpr
    exact ⟨mem_product.mpr ⟨mem_powerset.mpr Subset.rfl,mem_powerset.mpr Subset.rfl⟩,
      ⟨⟨Subset.rfl,Subset.rfl⟩,hn,he⟩⟩
  obtain ⟨S,hS,hmin⟩ := exists_min_image fam order ⟨(A,B),hseed⟩
  refine ⟨S,(mem_filter.mp hS).2,?_⟩
  intro T hT
  exact hmin T (mem_filter.mpr ⟨mem_product.mpr
    ⟨mem_powerset.mpr hT.1.1,mem_powerset.mpr hT.1.2⟩,hT⟩)
omit [Fintype V] [DecidableEq V] in
lemma hasFactor_mono_graph {K : SimpleGraph V} [DecidableRel K.Adj]
    {q : ℕ} {S T : Support V} (hKG : K ≤ G) (hTS : Included T S)
    (hf : HasFactor K q T) : HasFactor G q S := by
  obtain ⟨J,hJ,X,Y,hX,hY,hn,hminX,hminY⟩ := hf
  exact ⟨J,hJ.trans hKG,X,Y,hX.trans hTS.1,hY.trans hTS.2,hn,hminX,hminY⟩
/-- Actual original-support extraction. No selector or arbitrary-graph caller assumed. -/
theorem critical_normalization (h q : ℕ) (hh : 6 ≤ h)
    (hq : 4096*(h+1)^2 ≤ q) (A B : Finset V)
    (hbip : InducedBipartite G (A,B))
    (hn : 2*q ≤ order (A,B)) (hcap : Capped G (2*q-2) (A,B))
    (he : deficit G (q-1) (A,B) ≤ F h q) (hno : Noq G q (A,B)) :
    ∃ (S : Support V) (K : SimpleGraph V),
      Included S (A,B) ∧ K ≤ G ∧ InducedBipartite K S ∧
      2*q ≤ order S ∧ Capped K (2*q-2) S ∧ MinCore K q S ∧
      deficit K (q-1) S = (F h q : ℤ) ∧ Noq K q S ∧
      (∀ T, Included T S → h ≤ order T → order T < order S →
        (F h q : ℤ)+1 ≤ deficit K (q-1) T) := by
  have hq32 := cutoff h q hh hq
  have hF := F_cast hq32
  obtain ⟨S,hS,hminimal⟩ := minimal_dense hn he
  have hdis : Disjoint S.1 S.2 := hbip.1.mono hS.1.1 hS.1.2
  have hnontrunc : F h q ≤ (q-1)*order S := by
    have hs := hS.2.1
    have hm := Nat.mul_le_mul_left (q-1) hs
    have hf : F h q ≤ h*q := Nat.sub_le _ _
    have ht := Nat.mul_le_mul_right q (show h ≤ q-1 by omega)
    nlinarith
  have hm : (q-1)*order S-F h q ≤ ec G S.1 S.2 := by
    have hd := hS.2.2
    unfold deficit at hd
    have hdense : (q-1)*order S ≤ ec G S.1 S.2+F h q := by
      exact_mod_cast (show ((q-1:ℕ):ℤ)*order S ≤ (ec G S.1 S.2:ℤ)+(F h q:ℤ) by linarith)
    omega
  obtain ⟨K,hKG,heK⟩ := thin_pair (G := G) hdis ((q-1)*order S-F h q) hm
  let _ : DecidableRel K.Adj := Classical.decRel _
  have hexact : deficit K (q-1) S = (F h q : ℤ) := by
    unfold deficit
    rw [heK,Nat.cast_sub hnontrunc]
    push_cast
    ring
  have hfloor : ∀ T, Included T S → h ≤ order T → order T < order S →
      (F h q : ℤ)+1 ≤ deficit K (q-1) T := by
    intro T hTS hht hlt
    by_cases hel : 2*q ≤ order T
    · have hfail : ¬ deficit G (q-1) T ≤ (F h q : ℤ) := by
        intro hd
        have hmin := hminimal T ⟨⟨hTS.1.trans hS.1.1,hTS.2.trans hS.1.2⟩,hel,hd⟩
        omega
      have hmono := ec_mono_original K G hKG T.1 T.2
      unfold deficit
      unfold deficit at hfail
      have hc : (ec K T.1 T.2:ℤ) ≤ ec G T.1 T.2 := by exact_mod_cast hmono
      omega
    · rw [hF]
      exact small_floor hh hq32 T.1 T.2 hht (by simpa [order] using (show order T ≤ 2*q by omega))
  have hlarge : 2*q+1 ≤ order S := by
    by_contra! hnlarge
    have hs : order S=2*q := by have ht:=hS.2.1; omega
    have hf := small_floor (G := K) hh hq32 S.1 S.2
      (by simpa [order] using (show h ≤ order S by omega))
      (by simpa [order] using (show order S ≤ 2*q by omega))
    rw [hexact,hF] at hf
    omega
  have hmin : MinCore K q S := by
    constructor
    · intro v hv
      by_contra! hd
      have hc := card_erase_add_one hv
      have hi : Included (S.1.erase v,S.2) S := ⟨erase_subset _ _,Subset.rfl⟩
      have ho : order (S.1.erase v,S.2)+1=order S := by
        simp only [order]; omega
      have hl : h ≤ order (S.1.erase v,S.2) := by omega
      have ht : order (S.1.erase v,S.2) < order S := by omega
      have hf := hfloor _ hi hl ht
      rw [erase_left (G := K) hv (q-1),hexact] at hf
      have hpred : ((q-1:ℕ):ℤ)=(q:ℤ)-1 := by omega
      rw [hpred] at hf
      omega
    · intro v hv
      by_contra! hd
      have hc := card_erase_add_one hv
      have hi : Included (S.1,S.2.erase v) S := ⟨Subset.rfl,erase_subset _ _⟩
      have ho : order (S.1,S.2.erase v)+1=order S := by
        simp only [order]; omega
      have hl : h ≤ order (S.1,S.2.erase v) := by omega
      have ht : order (S.1,S.2.erase v) < order S := by omega
      have hf := hfloor _ hi hl ht
      rw [erase_right (G := K) hv (q-1),hexact] at hf
      have hpred : ((q-1:ℕ):ℤ)=(q:ℤ)-1 := by omega
      rw [hpred] at hf
      omega
  refine ⟨S,K,hS.1,hKG,?_,hS.2.1,?_,hmin,hexact,?_,hfloor⟩
  · exact ⟨hdis,fun v hv w hw he => hbip.2.1 v (hS.1.1 hv) w (hS.1.1 hw) (hKG he),
      fun v hv w hw he => hbip.2.2 v (hS.1.2 hv) w (hS.1.2 hw) (hKG he)⟩
  · constructor
    · intro v hv
      exact (dg_mono_original K G hKG S.2 v).trans
        ((dg_mono (G := G) hS.1.2 v).trans (hcap.1 v (hS.1.1 hv)))
    · intro v hv
      exact (dg_mono_original K G hKG S.1 v).trans
        ((dg_mono (G := G) hS.1.1 v).trans (hcap.2 v (hS.1.2 hv)))
  · intro hf
    exact hno (hasFactor_mono_graph hKG hS.1 hf)

/-- The support predicate selects genuine original edges and gives a genuine subgraph. -/
lemma hasFactor_original_subgraph {q : ℕ} (hq : 0 < q) {A B : Finset V}
    (hdis : Disjoint A B) (hf : HasFactor G q (A,B)) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  obtain ⟨J,hJG,X,Y,hX,hY,hn,hdegX,hdegY⟩ := hf
  have hXne : X.Nonempty := by
    by_contra! hx
    have he : X=∅ := hx
    have hYpos : 0 < Y.card := by simpa [he] using hn
    obtain ⟨y,hy⟩ := card_pos.mp hYpos
    have hd := hdegY y hy
    simp [he] at hd
    omega
  have hfactor : FactorOn q J X Y := by
    refine ⟨adjPairs J X Y,filter_subset _ _,?_,?_,?_⟩
    · intro x hx
      exact (mem_filter.mp hx).2
    · intro x hx
      rw [card_adjPairs_filter_fst hx]
      exact hdegX x hx
    · intro y hy
      rw [card_adjPairs_filter_snd hy]
      change (X.filter (J.Adj y)).card=q
      exact hdegY y hy
  have hpair := FactorOn.regular_pairs hq hXne hfactor
  exact B5.exists_subgraph_of_regularPairs (hdis.mono hX hY)
    (RegularPairs.mono_graph hJG hpair)

/-- Literal finite simple bipartite graph caller. All physical critical inputs
are derived internally; the conclusion is normalization, not factor existence. -/
theorem original_graph_normalization (h q : ℕ) (hh : 6 ≤ h)
    (hq : 4096*(h+1)^2 ≤ q) (G : SimpleGraph V)
    (hbip : G.IsBipartite) (hn : 2*q ≤ Fintype.card V)
    (hcap : G.maxDegree ≤ 2*q-2)
    (he : ((q:ℤ)-1)*Fintype.card V-(G.edgeSet.ncard:ℤ) ≤ (h:ℤ)*q-16*h^2)
    (hno : ¬∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q) :
    ∃ (A B : Finset V) (S : Support V) (K : SimpleGraph V),
      Disjoint A B ∧ A∪B=univ ∧ Included S (A,B) ∧ K ≤ G ∧
      InducedBipartite K S ∧ 2*q ≤ order S ∧ Capped K (2*q-2) S ∧
      MinCore K q S ∧ deficit K (q-1) S=(F h q:ℤ) ∧ Noq K q S ∧
      (∀ T, Included T S → h ≤ order T → order T < order S →
        (F h q:ℤ)+1 ≤ deficit K (q-1) T) := by
  have hq32 := cutoff h q hh hq
  have hqpos : 0<q := by omega
  obtain ⟨o⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨A,B,_,hdis,hcov,hbw⟩ := QB4.exists_sides hbip o
  have hc : order (A,B)=Fintype.card V := by
    unfold order
    dsimp
    rw [← card_union_of_disjoint hdis,hcov,card_univ]
  have hb : InducedBipartite G (A,B) := by
    refine ⟨hdis,?_,?_⟩
    · intro v hv w hw hadj
      rcases hbw.mem_of_adj hadj with h | h
      · exact disjoint_left.mp hdis hw h.2
      · exact disjoint_left.mp hdis hv h.1
    · intro v hv w hw hadj
      rcases hbw.mem_of_adj hadj with h | h
      · exact disjoint_left.mp hdis h.1 hv
      · exact disjoint_left.mp hdis h.2 hw
  have hcp : Capped G (2*q-2) (A,B) := by
    constructor
    · intro v hv
      exact (dg_le_maxDegree B v).trans hcap
    · intro v hv
      exact (dg_le_maxDegree A v).trans hcap
  have hed : deficit G (q-1) (A,B) ≤ (F h q:ℤ) := by
    unfold deficit
    rw [hc,QB4.ec_eq_ncard hbw,F_cast hq32]
    have pred : ((q-1:ℕ):ℤ)=(q:ℤ)-1 := by omega
    rwa [pred]
  have hnos : Noq G q (A,B) := fun hf => hno (hasFactor_original_subgraph hqpos hdis hf)
  obtain ⟨S,K,hS,hKG,hbS,hnS,hcapS,hminS,heS,hnoS,hfloor⟩ :=
    critical_normalization h q hh hq A B hb (by rwa [hc]) hcp hed hnos
  exact ⟨A,B,S,K,hdis,hcov,hS,hKG,hbS,hnS,hcapS,hminS,heS,hnoS,hfloor⟩

#print axioms critical_normalization
#print axioms hasFactor_original_subgraph
#print axioms original_graph_normalization
end Erdos585.R882.Normalization

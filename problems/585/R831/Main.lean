import Openmath.AllHTopCritical.Interface
import NEQAssembly.Counts
import AllHThirdExistence.Caller
import R753.Main
import AllHFourthExistence.Main
import R773.Main
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.H5BareR831
open QB4 B5 L34 H3Unequal AllHTopCritical NEQAssembly
universe u
/-- Sole downstream proposition: no literal original balanced host exists. -/
def BalancedImpossible (q : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (A B : Finset V), Host 5 q G A B → False
variable {V : Type u} [Fintype V] {G : SimpleGraph V} {q : ℕ}
omit [Fintype V] in
lemma boundary_order {U W : Finset V} (hq : 36864 ≤ q)
    (hn : 2*q ≤ #U+#W)
    (he : (q-1)*(#U+#W) ≤ ec G U W+(5*q-58)) : 2*q+1 ≤ #U+#W := by
  by_contra! hs
  have hm : #U+#W = 2*q := by omega
  have hp := B5.ec_le_product (G := G) U W
  have sq := sq_nonneg ((#U : ℤ)-#W)
  have sq2 := sq_nonneg ((q : ℤ)-3)
  zify at hm hp he
  rw [Bq.pred_cast (by omega)] at he
  have hc : ((5*q-58 : ℕ) : ℤ) = 5*(q : ℤ)-58 := by omega
  rw [hc] at he
  nlinarith
omit [Fintype V] in
lemma small_floor {X Y : Finset V} (hq : 36864 ≤ q)
    (hl : 5 ≤ #X+#Y) (hs : #X+#Y ≤ 2*q-1) :
    5*(q : ℤ)-57 ≤ coreDefect q G X Y := by
  have hp := B5.ec_le_product (G := G) X Y
  have sq := sq_nonneg ((#X : ℤ)-#Y)
  have poly := mul_nonneg (show 0 ≤ (#X : ℤ)+#Y-5 by omega)
    (show 0 ≤ 2*(q : ℤ)-1-(#X+#Y) by omega)
  zify at hp
  unfold coreDefect
  nlinarith
lemma split_support {A B : Finset V} (hcov : A∪B=univ) (S : Finset V) :
    (S∩A)∪(S∩B)=S := by
  rw [← inter_union_distrib_left, hcov, inter_univ]
omit [Fintype V] in
lemma induce_bipartite (hbip : G.IsBipartite) (S : Finset V) :
    (G.induce (S : Set V)).IsBipartite := by
  obtain ⟨A,B,h⟩ := hbip.exists_isBipartiteWith
  apply isBipartite_iff_exists_isBipartiteWith.mpr
  refine ⟨Subtype.val ⁻¹' A, Subtype.val ⁻¹' B, ?_, ?_⟩
  · exact h.disjoint.preimage _
  · intro x y hxy
    exact h.mem_of_adj hxy
omit [Fintype V] in
/-- Cap plus exact density forces sorted imbalance at most four. -/
lemma imbalance_le_four {A B : Finset V} (hq : 36864 ≤ q)
    (hab : #A ≤ #B) (hcap : ∀ a∈A, dg G B a ≤ 2*q-2)
    (he : ec G A B+(5*q-58)=(q-1)*(#A+#B)) : #B-#A ≤ 4 := by
  have hd := deficiency_nonneg (G := G) (2*(q : ℤ)-2)
    (show ∀ a∈A, (dg G B a : ℤ) ≤ 2*(q : ℤ)-2 by
      intro a ha; have hh := hcap a ha; omega)
  rw [deficiency_eq] at hd
  have hc : ((5*q-58 : ℕ) : ℤ)=5*(q : ℤ)-58 := by omega
  zify at he hab
  rw [Bq.pred_cast (by omega), hc] at he
  by_contra! hbad
  have hdiff : 5 ≤ (#B : ℤ)-#A := by omega
  have hm := mul_nonneg (show 0 ≤ (q : ℤ)-1 by omega)
    (show 0 ≤ (#B : ℤ)-#A-5 by omega)
  nlinarith
lemma critical_sorted (balanced : BalancedImpossible.{u} q) (hq : 36864 ≤ q)
    {A B : Finset V} (hdis : Disjoint A B) (hcov : A∪B=univ)
    (hbip : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hab : #A ≤ #B) (hn : 2*q ≤ Fintype.card V)
    (hmin : ∀ v, q ≤ G.degree v) (hcap : ∀ v, G.degree v ≤ 2*q-2)
    (he : G.edgeSet.ncard+(5*q-58)=(q-1)*Fintype.card V)
    (hno : Noq q G)
    (hfloor : ∀ S : Finset V, 5 ≤ #S → #S < Fintype.card V →
      5*(q : ℤ)-57 ≤ ((q : ℤ)-1)*#S-((G.induce (S : Set V)).edgeSet.ncard : ℤ)) : False := by
  have hc : #A+#B=Fintype.card V := by
    rw [← card_union_of_disjoint hdis, hcov, card_univ]
  have hj := imbalance_le_four hq hab
    (show ∀ a∈A, dg G B a ≤ 2*q-2 by
      intro a ha; rw [dg_eq_degree hbip ha]; exact hcap a)
    (by rw [ec_eq_ncard hbip, hc]; exact he)
  by_cases hbal : #A=#B
  · apply balanced G A B
    refine ⟨⟨by omega, by simpa using hq⟩,hdis,hcov,hbal,hbip,hn,hmin,hcap,?_,hno,?_⟩
    · simpa [constant,offset] using he
    · intro S hs hp
      have hh := hfloor S (by omega) hp
      have hconst : ((constant 5 q : ℕ) : ℤ)+1=5*(q : ℤ)-57 := by
        norm_num [constant,offset]
        omega
      rwa [hconst]
  · have hbranch : #B-#A=1 ∨ #B-#A=2 ∨ #B-#A=3 ∨ #B-#A=4 := by omega
    have card : #B=#A+(#B-#A) := by omega
    have edges : (G.edgeSet.ncard:ℤ)=((q:ℤ)-1)*Fintype.card V-(5*(q:ℤ)-58) := by
      have hm : ((q-1:ℕ):ℤ)=(q:ℤ)-1 := by omega
      have hc : ((5*q-58:ℕ):ℤ)=5*(q:ℤ)-58 := by omega
      zify at he
      rw [hm,hc] at he
      linarith
    rcases hbranch with hj | hj | hj | hj
    · rw [hj] at card
      obtain ⟨S,O,_,_,_,_,_,_,_,_,_,H,_,hne,hreg,_⟩ :=
        AllHFourthExistence.fourth_surplus 5 q 1 G A B
          ⟨by decide, (by norm_num; exact hq), by decide, hdis, hcov, hbip, card, hn, hmin, hcap,
          (by norm_num; exact he), (by
            intro X hl hp
            norm_num [AllHFourthQuotaFailure.constant,AllHFourthQuotaFailure.offset]
            have hh := hfloor X hl hp
            have hc : ((5*q-58:ℕ):ℤ)=5*(q:ℤ)-58 := by omega
            rw [hc]
            omega)⟩
      exact hno ⟨H,hne,hreg⟩
    · rw [hj] at card
      obtain ⟨S,O,_,_,_,_,_,_,_,_,H,_,hne,hreg,_⟩ :=
        AllHThirdExistence.literal_host_caller 5 q 2 G A B (by decide)
          (by norm_num; exact hq) (by decide) hdis hcov hbip card hn hmin hcap
          (by norm_num; exact he) (by
            intro X hl hp
            norm_num
            have hh := hfloor X hl hp
            have hc : ((5*q-58:ℕ):ℤ)=5*(q:ℤ)-58 := by omega
            rw [hc]
            omega)
      exact hno ⟨H,hne,hreg⟩
    · have p : AllHNextNonstrict.Parameters 5 q 58 3 :=
        ⟨by decide,by norm_num; exact hq,by decide,by decide,rfl⟩
      have host : AllHNextNonstrict.Host 5 q 58 3 G A B :=
        ⟨p,hdis,hcov,hbip,by omega,hn,hmin,hcap,by simpa [AllHNextNonstrict.constant] using he,by
          intro X hl hp
          have hh := hfloor X hl hp
          have hc : ((AllHNextNonstrict.constant 5 q 58:ℕ):ℤ)=5*(q:ℤ)-58 := by
            unfold AllHNextNonstrict.constant; omega
          rw [hc]
          omega⟩
      obtain ⟨O,_,_,_,H,_,hne,hreg⟩ := AllHNextNonstrict.allh_next_nonstrict 5 q 58 3 G A B host
      exact hno ⟨H,hne,hreg⟩
    · have p : AllHLargestNonstrict.Parameters 5 q 58 4 :=
        ⟨by decide,by norm_num; exact hq,by decide,by decide,rfl⟩
      have host : AllHLargestNonstrict.Host 5 q 58 4 G A B :=
        ⟨p,hdis,hcov,hbip,by omega,hn,hmin,hcap,by simpa [AllHLargestNonstrict.constant] using he,by
          intro X hl hp
          have hh := hfloor X hl hp
          have hc : ((AllHLargestNonstrict.constant 5 q 58:ℕ):ℤ)=5*(q:ℤ)-58 := by
            unfold AllHLargestNonstrict.constant; omega
          rw [hc]
          omega⟩
      obtain ⟨O,_,_,_,H,_,hne,hreg⟩ := AllHLargestNonstrict.allh_largest_nonstrict 5 q 58 4 G A B host
      exact hno ⟨H,hne,hreg⟩

lemma critical_impossible (balanced : BalancedImpossible.{u} q) (hq : 36864 ≤ q)
    {A B : Finset V} (hdis : Disjoint A B) (hcov : A∪B=univ)
    (hbip : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hn : 2*q ≤ Fintype.card V)
    (hmin : ∀ v, q ≤ G.degree v) (hcap : ∀ v, G.degree v ≤ 2*q-2)
    (he : G.edgeSet.ncard+(5*q-58)=(q-1)*Fintype.card V)
    (hno : Noq q G)
    (hfloor : ∀ S : Finset V, 5 ≤ #S → #S < Fintype.card V →
      5*(q : ℤ)-57 ≤ ((q : ℤ)-1)*#S-((G.induce (S : Set V)).edgeSet.ncard : ℤ)) : False := by
  by_cases hab : #A ≤ #B
  · exact critical_sorted balanced hq hdis hcov hbip hab hn hmin hcap he hno hfloor
  · exact critical_sorted balanced hq hdis.symm (by rwa [union_comm]) hbip.symm
      (by omega) hn hmin hcap he hno hfloor

/-- Strong induction ranges over all smaller finite bipartite cap-D graphs. -/
theorem dense_aux (q : ℕ) (hq : 36864 ≤ q) (balanced : BalancedImpossible.{u} q)
    (n : ℕ) : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
    Fintype.card V=n → G.IsBipartite → G.maxDegree ≤ 2*q-2 →
    2*q ≤ Fintype.card V →
    (q-1)*Fintype.card V ≤ G.edgeSet.ncard+(5*q-58) →
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ G hnum hbip hcap hn he
    classical
    by_contra hno
    obtain ⟨o⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨A,B,_,hdis,hcov,hbw⟩ := exists_sides hbip o
    have hc : #A+#B=Fintype.card V := by
      rw [← card_union_of_disjoint hdis,hcov,card_univ]
    have hlarge : 2*q+1 ≤ Fintype.card V := by
      rw [← hc]
      exact boundary_order hq (by omega) (by rw [hc,ec_eq_ncard hbw]; exact he)
    have hnontrunc : 5*q-58 ≤ (q-1)*Fintype.card V := by
      have hm := Nat.mul_le_mul_right (Fintype.card V) (by omega : 3 ≤ q-1)
      omega
    let m := (q-1)*Fintype.card V-(5*q-58)
    obtain ⟨K,hKG,hmK⟩ := thin_pair (G := G) hdis m
      (by rw [ec_eq_ncard hbw]; dsimp [m]; omega)
    let _ : DecidableRel K.Adj := Classical.decRel _
    have hbwK : K.IsBipartiteWith (A : Set V) (B : Set V) :=
      ⟨hbw.disjoint,fun _ _ h => hbw.mem_of_adj (hKG h)⟩
    have heK : K.edgeSet.ncard+(5*q-58)=(q-1)*Fintype.card V := by
      rw [← ec_eq_ncard hbwK,hmK]
      dsimp [m]
      omega
    have hnoK : Noq q K := fun hf => hno (NEQ.original_regular_transport hKG hf)
    have hcapK : K.maxDegree ≤ 2*q-2 := thinned_cap K G _ hKG hcap
    have hproper : ∀ S : Finset V, 2*q ≤ #S → #S < Fintype.card V →
        5*(q : ℤ)-57 ≤ ((q : ℤ)-1)*#S-
          ((K.induce (S : Set V)).edgeSet.ncard : ℤ) := by
      intro S hs hlt
      by_contra! hbad
      have hdense : (q-1)*#S ≤ (K.induce (S : Set V)).edgeSet.ncard+(5*q-58) := by
        have hpred : ((q-1 : ℕ) : ℤ)=(q : ℤ)-1 := by omega
        have hconstant : ((5*q-58 : ℕ) : ℤ)=5*(q : ℤ)-58 := by omega
        zify
        rw [hpred,hconstant]
        omega
      have hf := ih #S (by omega) (K.induce (S : Set V))
        (by simp) (induce_bipartite hbwK.isBipartite S)
        (induced_cap K S _ hcapK) (by simpa using hs) (by simpa using hdense)
      exact hnoK (original_induced_regular_transport K S hf)
    have hsmaller : ∀ X ⊆ A, ∀ Y ⊆ B, 2*q ≤ #X+#Y → #X+#Y < #A+#B →
        (q-1)*(#X+#Y) ≤ ec K X Y+(5*q-58) → False := by
      intro X hX Y hY hs hlt hdense
      have hf := hproper (X∪Y) (by rwa [card_union_of_disjoint (hdis.mono hX hY)])
        (by rw [card_union_of_disjoint (hdis.mono hX hY)]; omega)
      rw [induced_edges_eq_ec hdis hbwK hX hY,
        card_union_of_disjoint (hdis.mono hX hY)] at hf
      have hpred : ((q-1 : ℕ) : ℤ)=(q : ℤ)-1 := by omega
      have hconstant : ((5*q-58 : ℕ) : ℤ)=5*(q : ℤ)-58 := by omega
      zify at hdense
      rw [hpred,hconstant] at hdense
      push_cast at hdense hf
      omega
    have hminA : ∀ a∈A, q ≤ dg K B a := by
      intro a ha
      by_contra! hlow
      have hcard := card_erase_add_one ha
      have hec := Bq.ec_erase_add (G := K) (W := B) ha
      have hpair : ec K A B+(5*q-58)=(q-1)*(#A+#B) := by
        rw [ec_eq_ncard hbwK,hc]; exact heK
      have hprod : (q-1)*(#(A.erase a)+#B)+(q-1)=(q-1)*(#A+#B) := by
        calc _ = (q-1)*((#(A.erase a)+#B)+1) := by ring
          _ = _ := by congr 1; omega
      exact hsmaller (A.erase a) (erase_subset a A) B (Subset.refl B)
        (by omega) (by omega) (by omega)
    have hminB : ∀ b∈B, q ≤ dg K A b := by
      intro b hb
      by_contra! hlow
      have hcard := card_erase_add_one hb
      have hec := Bq.ec_erase_add (G := K) (W := A) hb
      rw [ec_comm (G := K) (B.erase b) A,ec_comm (G := K) B A] at hec
      have hpair : ec K A B+(5*q-58)=(q-1)*(#A+#B) := by
        rw [ec_eq_ncard hbwK,hc]; exact heK
      have hprod : (q-1)*(#A+#(B.erase b))+(q-1)=(q-1)*(#A+#B) := by
        calc _ = (q-1)*((#A+#(B.erase b))+1) := by ring
          _ = _ := by congr 1; omega
      exact hsmaller A (Subset.refl A) (B.erase b) (erase_subset b B)
        (by omega) (by omega) (by omega)
    have hminK : ∀ v, q ≤ K.degree v := by
      intro v
      have hv : v∈A∪B := by rw [hcov]; exact mem_univ v
      rcases mem_union.mp hv with ha | hb
      · rw [← dg_eq_degree hbwK ha]; exact hminA v ha
      · rw [← dg_eq_degree hbwK.symm hb]; exact hminB v hb
    have hfloor : ∀ S : Finset V, 5 ≤ #S → #S < Fintype.card V →
        5*(q : ℤ)-57 ≤ ((q : ℤ)-1)*#S-
          ((K.induce (S : Set V)).edgeSet.ncard : ℤ) := by
      intro S hs hp
      by_cases hel : 2*q ≤ #S
      · exact hproper S hel hp
      · have hsplit := split_support hcov S
        have hd := hdis.mono (inter_subset_right : S∩A ⊆ A) (inter_subset_right : S∩B ⊆ B)
        have hcard : #(S∩A)+#(S∩B)=#S := by rw [← card_union_of_disjoint hd,hsplit]
        have hf := small_floor (G := K) hq (by omega : 5 ≤ #(S∩A)+#(S∩B))
          (by omega : #(S∩A)+#(S∩B) ≤ 2*q-1)
        unfold coreDefect at hf
        have hcardZ : (#(S∩A) : ℤ)+#(S∩B)=(#S : ℤ) := by exact_mod_cast hcard
        rw [hcardZ] at hf
        have hec := induced_edges_eq_ec hdis hbwK
          (inter_subset_right : S∩A ⊆ A) (inter_subset_right : S∩B ⊆ B)
        rw [hsplit] at hec
        rwa [hec]
    exact critical_impossible balanced hq hdis hcov hbwK hn hminK
      (fun v => (K.degree_le_maxDegree v).trans hcapK) heK hnoK hfloor

/-- Literal bare endpoint, conditional only on absence of balanced Host 5. -/
theorem bare_h5_of_balanced_impossible (q : ℕ) (hq : 36864 ≤ q)
    (balanced : BalancedImpossible.{u} q) {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hbip : G.IsBipartite) (hcap : G.maxDegree ≤ 2*q-2)
    (hn : 2*q ≤ Fintype.card V)
    (he : (q-1)*Fintype.card V-(5*q-58) ≤ G.edgeSet.ncard) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  exact dense_aux q hq balanced (Fintype.card V) G rfl hbip hcap hn (by omega)
#print axioms bare_h5_of_balanced_impossible
end Erdos585.H5BareR831

import R783.Coverage
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.GeneralSelectorR783
open QB4 B5 H3Unequal Omit1PrefixR691 Omit1UnitCutAdapterR707
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V} {h q : ℕ} {F : ℤ}
  {A B M P S T : Finset V}
variable (host : OriginalHost h q F G A B)

omit [Fintype V] in
/-- Row and column exclusions leave a single actual pair. -/
lemma select_avoiding (LA LB : Finset V) (H K : V → V → Prop) (d : ℕ)
    (row : ∀ a ∈ LA, #(LB.filter (H a)) ≤ d)
    (col : ∀ b ∈ LB, #(LA.filter (fun a => K a b)) ≤ d)
    (largeA : 2*d < #LA) (largeB : 2*d < #LB) :
    ∃ a ∈ LA, ∃ b ∈ LB, ¬H a b ∧ ¬K a b := by
  by_contra no
  have all : ∀ a ∈ LA, ∀ b ∈ LB, H a b ∨ K a b := by
    intro a ha b hb
    by_cases hh : H a b
    · exact Or.inl hh
    · exact Or.inr (by by_contra hk; exact no ⟨a,ha,b,hb,hh,hk⟩)
  have rows : ∀ a ∈ LA, #LB ≤ d+#(LB.filter (K a)) := by
    intro a ha
    have cover : LB ⊆ LB.filter (H a) ∪ LB.filter (K a) := by
      intro b hb
      exact (all a ha b hb).elim (fun hh => mem_union_left _ (mem_filter.mpr ⟨hb,hh⟩))
        (fun hk => mem_union_right _ (mem_filter.mpr ⟨hb,hk⟩))
    have bound := (card_le_card cover).trans (card_union_le _ _)
    have hh := row a ha
    omega
  have count : #LA*#LB ≤ #LA*d+∑ a ∈ LA, #(LB.filter (K a)) := by
    have hh := sum_le_sum rows
    simp only [sum_const,nsmul_eq_mul,sum_add_distrib] at hh
    omega
  have swap : (∑ a ∈ LA, #(LB.filter (K a))) = ∑ b ∈ LB, #(LA.filter (fun a => K a b)) := by
    simp only [card_filter]
    exact sum_comm
  rw [swap] at count
  have colsum := sum_le_sum col
  simp only [sum_const,nsmul_eq_mul] at colsum
  have p1 := Nat.mul_lt_mul_of_pos_left largeB (show 0<#LA by omega)
  have p2 := Nat.mul_lt_mul_of_pos_left largeA (show 0<#LB by omega)
  nlinarith

include host
lemma pool_numeric : 4*(2*h-3) < q := by
  have hh := host.height
  have hq := host.large
  have sub : 2*h-3+3=2*h := by omega
  nlinarith

omit host in
lemma complement_complement (S : Finset V) : univ\(univ\S)=S := by ext v; simp

/-- The mirror of the least original minimizer is the greatest swapped minimizer. -/
lemma mirror_greatest
    (lower : ∀ S : Finset V, g q G A B M ≤ g q G A B S)
    (least : ∀ S : Finset V, g q G A B S=g q G A B M → M ⊆ S) :
    (∀ S : Finset V, g q G B A (univ\M) ≤ g q G B A S) ∧
    (∀ S : Finset V, g q G B A S=g q G B A (univ\M) → S ⊆ univ\M) := by
  have mirror : ∀ S : Finset V, g q G B A S=g q G A B (univ\S) := by
    intro S
    simpa only [complement_complement] using AllHCommonPinsR773.swapped_complement host (univ\S)
  constructor
  · intro S
    rw [mirror,complement_complement,mirror]
    exact lower _
  · intro S hs
    rw [mirror,mirror,complement_complement] at hs
    have sub := least (univ\S) hs
    intro v hv
    refine mem_sdiff.mpr ⟨mem_univ v,?_⟩
    intro hm
    exact (mem_sdiff.mp (sub hm)).2 hv

/-- The same common pin sets serve both internally chosen anchors. -/
theorem selector_from_common_pins (small_height : h=3 ∨ h=4)
    (exists_negative : ∃ M : Finset V, g q G A B M < 0)
    (LA LB : Finset V) (ha : LA ⊆ A) (hb : LB ⊆ B)
    (ca : q < 2*#LA) (cb : q < 2*#LB)
    (pins : ∀ M : Finset V, g q G A B M < 0 →
      LA ⊆ M ∧ Disjoint LB M ∧
      (∀ v ∈ LA, dg G (B\M) v ≤ 3*h-4) ∧
      (∀ v ∈ LB, dg G (A∩M) v ≤ 3*h-4)) :
    ∃ a ∈ A, ∃ b ∈ B, UnitCuts q G A B a b := by
  obtain ⟨Mlo,Mhi,nested,neglo,neghi,lower,values,greatest,least⟩ := global_extrema exists_negative
  have lowerhi : ∀ S : Finset V, g q G A B Mhi ≤ g q G A B S := by
    intro S
    rw [← values]
    exact lower S
  have plo := pins Mlo neglo
  have phi := pins Mhi neghi
  have common : ∀ a ∈ LA, CommonLeft q G A B a := by
    intro a ha' S negS
    exact (pins S negS).1 ha'
  have commonSwap : ∀ b ∈ LB, CommonLeft q G B A b := by
    intro b hb' S negS
    have neg : g q G A B (univ\S)<0 := by
      rw [AllHCommonPinsR773.swapped_complement (AllHCommonPinsR773.swap host) S]
      exact negS
    have disj := (pins (univ\S) neg).2.1
    by_contra! outside
    exact disjoint_left.mp disj hb' (by simp [outside])
  have Nneg : g q G B A (univ\Mlo)<0 := by
    rw [AllHCommonPinsR773.swapped_complement host]
    exact neglo
  have swapExt := mirror_greatest host lower least
  have LAheads : LA ⊆ A\(univ\Mlo) := by
    intro a ha'
    have hm := plo.1 ha'
    simp only [mem_sdiff,mem_univ]
    exact ⟨ha ha',by simpa using hm⟩
  have LBheads : LB ⊆ B\Mhi := by
    intro b hb'
    exact mem_sdiff.mpr ⟨hb hb',fun hm => disjoint_left.mp phi.2.1 hb' hm⟩
  let H : V → V → Prop := fun a b => Hazard q G A B Mhi a b
  let K : V → V → Prop := fun a b => Hazard q G B A (univ\Mlo) b a
  have row : ∀ a ∈ LA, #(LB.filter (H a)) ≤ 2*h-3 := by
    intro a ha'
    exact exact_hazard_card host neghi (mem_inter.mpr ⟨ha ha',phi.1 ha'⟩)
      (common a ha') (phi.2.2.1 a ha') LB LBheads phi.2.2.2
  have col : ∀ b ∈ LB, #(LA.filter (fun a => K a b)) ≤ 2*h-3 := by
    intro b hb'
    have bN : b ∈ B∩(univ\Mlo) := by
      refine mem_inter.mpr ⟨hb hb',mem_sdiff.mpr ⟨mem_univ b,?_⟩⟩
      exact fun hm => disjoint_left.mp plo.2.1 hb' hm
    have bLight : dg G (A\(univ\Mlo)) b ≤ 3*h-4 := by
      have eq : A\(univ\Mlo)=A∩Mlo := by ext v; simp
      rw [eq]
      exact plo.2.2.2 b hb'
    have aLight : ∀ a ∈ LA, dg G (B∩(univ\Mlo)) a ≤ 3*h-4 := by
      have eq : B∩(univ\Mlo)=B\Mlo := by ext v; simp
      rw [eq]
      exact plo.2.2.1
    exact exact_hazard_card (AllHCommonPinsR773.swap host) Nneg bN
      (commonSwap b hb') bLight LA LAheads aLight
  have num := pool_numeric host
  obtain ⟨a,ha',b,hb',notH,notK⟩ := select_avoiding LA LB H K (2*h-3) row col
    (by omega) (by omega)
  refine ⟨a,ha ha',b,hb hb',?_⟩
  intro W
  have killer_paid : a ∉ W → b ∈ W → (q : ℤ) ≤ g q G A B W := by
    intro aout bin
    by_contra! unpaid
    have band : g q G A B W ≤ (q : ℤ)-1 := by omega
    have loc := band_localization host neghi band
    rcases loc with remove|add
    · have sub : Mlo\W ⊆ Mhi\W := sdiff_subset_sdiff_left W nested
      have tiny : #(Mlo\W)<h := (card_le_card sub).trans_lt remove
      have eq : (univ\W)\(univ\Mlo)=Mlo\W := by ext v; simp only [mem_sdiff,mem_univ]; tauto
      have bOut : b ∉ univ\W := by simp [bin]
      have aIn : a ∈ univ\W := by simp [aout]
      have aOutside : a ∉ univ\Mlo := by simp [plo.1 ha']
      have bandSwap : g q G B A (univ\W) ≤ (q : ℤ)-1 := by
        rw [AllHCommonPinsR773.swapped_complement host]
        exact band
      have hazard := tiny_killer_hazard (AllHCommonPinsR773.swap host) small_height
        (ha ha') aOutside bOut aIn swapExt.1 swapExt.2 (by rwa [eq]) bandSwap
      exact notK hazard
    · have bOutside : b ∉ Mhi := fun hm => disjoint_left.mp phi.2.1 hb' hm
      exact notH (tiny_killer_hazard host small_height (hb hb') bOutside aout bin
        lowerhi greatest add band)
  have global_lower : (2 : ℤ)-(h : ℤ) ≤ g q G A B W := by
    by_cases neg : g q G A B W<0
    · have bd := AllHCommonPinsR773.negative_bounds host neg
      omega
    · have hh := host.height
      omega
  have qh := AllHCommonPinsR773.numeric host
  by_cases ai : a ∈ W <;> by_cases bi : b ∈ W
  · have nn : 0 ≤ g q G A B W := by
      by_contra! neg
      exact disjoint_left.mp (pins W neg).2.1 hb' bi
    simpa [ai,bi] using nn
  · simp only [ai,bi,if_true,if_false,zero_sub,mul_neg,mul_one]
    omega
  · simpa [ai,bi] using killer_paid ai bi
  · have nn := avoiding_nonnegative (common a ha') ai
    simpa [ai,bi] using nn

/-- The full h=3,4 original-host endpoint supplies its pins and omission pair internally. -/
theorem original_factor (small_height : h=3 ∨ h=4)
    (exists_negative : ∃ M : Finset V, g q G A B M < 0) :
    ∃ a ∈ A, ∃ b ∈ B, UnitCuts q G A B a b ∧
      FactorOn q G (A\{a}) (B\{b}) ∧
      ∃ H : G.Subgraph, H.verts=(↑(univ\{a,b}) : Set V) ∧
        H.verts.Nonempty ∧ H.verts ≠ Set.univ ∧ H.coe.IsRegularOfDegree q := by
  obtain ⟨_,LA,LB,ha,hb,ca,cb,pins⟩ := AllHCommonPinsR773.full_common_pins host exists_negative
  obtain ⟨a,ha',b,hb',uc⟩ := selector_from_common_pins host small_height exists_negative
    LA LB ha hb ca cb pins
  have order : q ≤ #A-1 := by
    obtain ⟨M,neg⟩ := exists_negative
    have ep := (AllHCommonPinsR773.endpoint_order host neg).1
    have bound := card_le_card (inter_subset_left : A∩M ⊆ A)
    omega
  have positive : 0<q := by have qq := AllHCommonPinsR773.q_large host; omega
  obtain ⟨factor,H,verts,nonempty,regular⟩ := exact_original_factor
    host.disjoint host.balanced ha' hb' positive order uc
  have support : (A\{a})∪(B\{b})=univ\{a,b} := by
    rw [support_eq host.disjoint ha' hb',host.cover]
  rw [support] at verts
  refine ⟨a,ha',b,hb',uc,factor,H,verts,nonempty,?_,regular⟩
  intro full
  have ain : a ∈ H.verts := by rw [full]; trivial
  rw [verts] at ain
  simpa using ain

omit host in
/-- Literal original caller: no pins, anchors, successful pair, chain, saturation,
uniqueness, or Noq premise is supplied. The factor uses actual original edges. -/
theorem original_host_caller
    (small_height : h=3 ∨ h=4)
    (height : 3 ≤ h) (large : 1024*(h+1)^2 ≤ q)
    (disjoint : Disjoint A B) (cover : A∪B=univ) (balanced : #A=#B)
    (bipartite : G.IsBipartiteWith (A : Set V) (B : Set V))
    (order : 2*q ≤ Fintype.card V)
    (minimum : ∀ v : V, q ≤ G.degree v)
    (cap : ∀ v : V, G.degree v ≤ 2*q-2)
    (exact_deficit : ((q : ℤ)-1)*Fintype.card V-(G.edgeSet.ncard : ℤ)=F)
    (range : (h : ℤ)*q-((h : ℤ)^2+5*h+8)+1 ≤ F ∧
      F ≤ (h : ℤ)*q-((h : ℤ)^2+5*h+8)+(h : ℤ)-2)
    (proper : ∀ D : Finset V, h ≤ #D → #D < Fintype.card V →
      F+1 ≤ ((q : ℤ)-1)*#D-((G.induce (D : Set V)).edgeSet.ncard : ℤ))
    (negative_exists : ∃ M : Finset V,
      (ec G (A∩M) (B\M) : ℤ) < (q : ℤ)*((#(A∩M) : ℤ)-#(B∩M))) :
    ∃ a ∈ A, ∃ b ∈ B,
      (∀ W : Finset V,
        (q : ℤ)*((if b ∈ W then 1 else 0)-(if a ∈ W then 1 else 0)) ≤
          (ec G (A∩W) (B\W) : ℤ)-(q : ℤ)*((#(A∩W) : ℤ)-#(B∩W))) ∧
      FactorOn q G (A\{a}) (B\{b}) ∧
      ∃ H : G.Subgraph, H.verts=(↑(univ\{a,b}) : Set V) ∧
        H.verts.Nonempty ∧ H.verts ≠ Set.univ ∧ H.coe.IsRegularOfDegree q := by
  have cards := card_union_of_disjoint disjoint
  rw [cover,card_univ] at cards
  have host : OriginalHost h q F G A B := {
    height := height,large := large,disjoint := disjoint,cover := cover,
    balanced := balanced,bipartite := bipartite,order := order,
    min_degree := minimum,cap := cap,
    total := by
      unfold coreDefect
      rw [ec_eq_ncard bipartite]
      zify at cards
      nlinarith,
    range := range,proper := proper }
  have ex : ∃ M : Finset V, g q G A B M<0 := by
    obtain ⟨M,hm⟩ := negative_exists
    exact ⟨M,by unfold g k; omega⟩
  exact original_factor host small_height ex

/-- If every original slack is nonnegative, the whole original graph supplies a factor. -/
theorem nonnegative_factor (nonnegative : ∀ S : Finset V, 0 ≤ g q G A B S) :
    ∃ H : G.Subgraph, H.verts=Set.univ ∧ H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  have cuts : ∀ X ⊆ A, ∀ Y ⊆ B, q*#X ≤ ec G X (B\Y)+q*#Y := by
    intro X hX Y hY
    have hAX : A∩(X∪Y)=X := by
      ext v
      simp only [mem_inter,mem_union]
      constructor
      · rintro ⟨av,xv|yv⟩
        · exact xv
        · exact False.elim (disjoint_left.mp host.disjoint av (hY yv))
      · intro xv
        exact ⟨hX xv,Or.inl xv⟩
    have hBY : B∩(X∪Y)=Y := by
      ext v
      simp only [mem_inter,mem_union]
      constructor
      · rintro ⟨bv,xv|yv⟩
        · exact False.elim (disjoint_left.mp host.disjoint (hX xv) bv)
        · exact yv
      · intro yv
        exact ⟨hY yv,Or.inr yv⟩
    have hBout : B\(X∪Y)=B\Y := by
      ext v
      simp only [mem_sdiff,mem_union]
      constructor
      · tauto
      · rintro ⟨bv,ny⟩
        exact ⟨bv,fun hv => hv.elim (fun xv => disjoint_left.mp host.disjoint (hX xv) bv) ny⟩
    have nn := nonnegative (X∪Y)
    unfold g k at nn
    rw [hAX,hBY,hBout] at nn
    have paid : (q : ℤ)*#X ≤ (ec G X (B\Y) : ℤ)+(q : ℤ)*#Y := by nlinarith
    exact_mod_cast paid
  have factor := B5Factor.exists_target_factor A B host.balanced cuts
  have positive : 0<q := by have qq := AllHCommonPinsR773.q_large host; omega
  have cards := card_union_of_disjoint host.disjoint
  rw [host.cover,card_univ] at cards
  have hA : A.Nonempty := by
    apply card_pos.mp
    have order := host.order
    have bal := host.balanced
    omega
  obtain ⟨H,verts,nonempty,regular⟩ := H3Unequal.factor_exact_subgraph positive hA host.disjoint factor
  have support : (↑(A∪B) : Set V)=Set.univ := by rw [host.cover]; simp
  rw [support] at verts
  exact ⟨H,verts,nonempty,regular⟩

/-- Required balanced-core supplier, with the negative and no-negative cases both internal. -/
theorem balanced_core_factor (small_height : h=3 ∨ h=4) :
    ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  by_cases neg : ∃ M : Finset V, g q G A B M<0
  · obtain ⟨a,ha,b,hb,uc,fac,H,verts,hn,proper,regular⟩ := original_factor host small_height neg
    exact ⟨H,hn,regular⟩
  · have nonnegative : ∀ M : Finset V, 0 ≤ g q G A B M := by
      intro M
      by_contra! hm
      exact neg ⟨M,hm⟩
    obtain ⟨H,_,hn,regular⟩ := nonnegative_factor host nonnegative
    exact ⟨H,hn,regular⟩

#print axioms select_avoiding
#print axioms selector_from_common_pins
#print axioms original_factor
#print axioms original_host_caller
#print axioms nonnegative_factor
#print axioms balanced_core_factor
end Erdos585.GeneralSelectorR783

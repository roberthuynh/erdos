import R704.Base
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.Omit1UniqueR704
open QB4 B5 H3Unequal Omit1PrefixR691
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V} {q : ℕ}
  {A B M P S T : Finset V} {L : ℤ}
variable (host : Omit1PrefixR691.Host q L G A B)
include host
/-- A diagonal size consequence of actual saturation, reverse count and order. -/
lemma large_shores (d : Omit1Q0CutChainR699.CutData q G A B M) :
    2*q-2 ≤ #(A∩M) ∧ 2*q-2 ≤ #(B\M) := by
  have hq := host.large
  have cs := support_card host M
  have ki := d.imbalance
  have ord := d.order
  have cardT : q-1 ≤ #(B∩M) := by unfold k at ki; omega
  have eh : ec G (B∩M) A = (2*q-2)*#(B∩M) := by
    unfold ec
    calc
      _ = ∑ _t ∈ B∩M, (2*q-2) := sum_congr rfl (fun t ht => by
        rw [dg_eq_degree host.bipartite.symm (mem_inter.mp ht).1,d.saturated_B t ht])
      _ = _ := by simp only [sum_const,smul_eq_mul]; exact Nat.mul_comm _ _
  have split := ec_sdiff_add_right (G := G) (inter_subset_left : A∩M ⊆ A) (B∩M)
  have ax : A\(A∩M)=A\M := by ext v; simp
  rw [ax,ec_comm (G := G) (B∩M) (A\M)] at split
  have simple := AllHTopCritical.ec_le_product (G := G) (B∩M) (A∩M)
  have hr := d.reverse
  have xl : 2*q-2 ≤ #(A∩M) := by
    by_contra! hn
    zify at eh split simple cardT hn
    unfold k at ki
    have cz : (#(A∩M) : ℤ) = #(B∩M)+2 := by omega
    have dc : ((2*q-2 : ℕ) : ℤ) = 2*(q : ℤ)-2 := by omega
    rw [dc] at eh
    have prod := mul_nonneg (show (0 : ℤ) ≤ 2*(q : ℤ)-3-#(A∩M) by omega)
      (show (0 : ℤ) ≤ #(B∩M) by positivity)
    have cardTi : (q : ℤ)-1 ≤ #(B∩M) := by omega
    nlinarith only [eh,split,simple,hr,cardTi,prod]
  have ordc := d.complement_order
  have cc := card_sdiff_add_card_eq_card (show A∩M ⊆ A from inter_subset_left)
  have cb := card_sdiff_add_card_eq_card (show B∩M ⊆ B from inter_subset_left)
  have bs : B\(B∩M)=B\M := by ext v; simp
  rw [ax] at cc
  rw [bs] at cb
  have cs' := support_card host (univ\M)
  have ai : A∩(univ\M)=A\M := by ext v; simp
  have bi : B∩(univ\M)=B\M := by ext v; simp
  rw [ai,bi] at cs'
  have bal := host.balanced
  have cardV : q-1 ≤ #(A\M) := by unfold k at ki; omega
  have eh' : ec G (A\M) B = (2*q-2)*#(A\M) := by
    unfold ec
    calc
      _ = ∑ _t ∈ A\M, (2*q-2) := sum_congr rfl (fun t ht => by
        rw [dg_eq_degree host.bipartite (sdiff_subset ht),d.saturated_A t ht])
      _ = _ := by simp only [sum_const,smul_eq_mul]; exact Nat.mul_comm _ _
  have split' := ec_sdiff_add_right (G := G) (inter_subset_left : B∩M ⊆ B) (A\M)
  rw [bs] at split'
  have simple' := AllHTopCritical.ec_le_product (G := G) (A\M) (B\M)
  refine ⟨xl,?_⟩
  by_contra! hn
  zify at eh' split' simple' cardV hn
  have dc : ((2*q-2 : ℕ) : ℤ) = 2*(q : ℤ)-2 := by omega
  rw [dc] at eh'
  have prod := mul_nonneg (show (0 : ℤ) ≤ 2*(q : ℤ)-3-#(B\M) by omega)
    (show (0 : ℤ) ≤ #(A\M) by positivity)
  have cardVi : (q : ℤ)-1 ≤ #(A\M) := by omega
  nlinarith only [eh',split',simple',hr,cardVi,prod]

omit host [Fintype V] in
lemma ec_left_zero {X Y : Finset V} (hz : ∀ x ∈ X, dg G Y x = 0) : ec G X Y = 0 := by
  exact sum_eq_zero hz

omit host [Fintype V] in
/-- One positive shore of a nearly matching forward graph supplies almost all degree-one heads. -/
lemma many_one_heads {X Y : Finset V} (hlarge : 2*q-2 ≤ #Y)
    (hq : 2 ≤ q) (total : ec G X Y = 2*q-1)
    (positive : ∀ y ∈ Y, 0 < dg G X y) :
    2*q-3 ≤ #(Y.filter (fun y => dg G X y=1)) := by
  let Y1 := Y.filter (fun y => dg G X y=1)
  have hh : ∀ y ∈ Y\Y1, 2 ≤ dg G X y := by
    intro y hy
    have hym := (mem_sdiff.mp hy).1
    have hyn := (mem_sdiff.mp hy).2
    have hp := positive y hym
    have hn : dg G X y ≠ 1 := by intro he; exact hyn (mem_filter.mpr ⟨hym,he⟩)
    omega
  have ep : ec G Y1 X = #Y1 := by
    unfold ec
    calc
      _ = ∑ _y ∈ Y1, 1 := sum_congr rfl (fun y hy => (mem_filter.mp hy).2)
      _ = _ := by simp
  have el : 2*#(Y\Y1) ≤ ec G (Y\Y1) X := by
    calc
      _ = ∑ _y ∈ Y\Y1, 2 := by simp; omega
      _ ≤ _ := sum_le_sum hh
  have es := ec_sdiff_add_left (G := G) (filter_subset (fun y => dg G X y=1) Y) X
  have cs := card_sdiff_add_card_eq_card (filter_subset (fun y => dg G X y=1) Y)
  rw [ec_comm (G := G) Y X,total] at es
  change ec G (Y\Y1) X + ec G Y1 X = 2*q-1 at es
  change #(Y\Y1)+#Y1=#Y at cs
  change 2*q-3 ≤ #Y1
  omega


omit host [Fintype V] in
/-- Actual forward edges force a zero vertex when a positive opposite shore has no S1 edge. -/
lemma zero_vertex_of_no_s1 {X Y : Finset V} (hq : 4 ≤ q)
    (lx : 2*q-2 ≤ #X) (ly : 2*q-2 ≤ #Y) (total : ec G X Y = 2*q-1)
    (positive : ∀ y ∈ Y, 0 < dg G X y)
    (noS1 : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y → ¬(dg G Y x=1 ∧ dg G X y=1)) :
    ∃ a ∈ X, dg G Y a=0 := by
  let X0 := X.filter (fun x => dg G Y x=0)
  let X1 := X.filter (fun x => dg G Y x=1)
  let Xh := X.filter (fun x => 2 ≤ dg G Y x)
  let Y1 := Y.filter (fun y => dg G X y=1)
  have many : 2*q-3 ≤ #Y1 := many_one_heads ly (by omega) total positive
  have oneX : ec G X1 Y = #X1 := by
    unfold ec
    calc
      _ = ∑ _x ∈ X1, 1 := sum_congr rfl (fun x hx => (mem_filter.mp hx).2)
      _ = _ := by simp
  have oneY : ec G X Y1 = #Y1 := by
    rw [ec_comm]
    unfold ec
    calc
      _ = ∑ _y ∈ Y1, 1 := sum_congr rfl (fun y hy => (mem_filter.mp hy).2)
      _ = _ := by simp
  have noedge : ec G X1 Y1 = 0 := by
    apply ec_left_zero
    intro x hx
    unfold dg
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    have xm := mem_filter.mp hx
    have ym := mem_filter.mp (mem_filter.mp hy).1
    exact noS1 x xm.1 y ym.1 (mem_filter.mp hy).2 ⟨xm.2,ym.2⟩
  have split := ec_sdiff_add_left (G := G) (filter_subset (fun x => dg G Y x=1) X) Y
  have splitY := ec_sdiff_add_left (G := G) (filter_subset (fun x => dg G Y x=1) X) Y1
  change ec G (X\X1) Y + ec G X1 Y = ec G X Y at split
  change ec G (X\X1) Y1 + ec G X1 Y1 = ec G X Y1 at splitY
  have mono := ec_mono_right (G := G) (X\X1) (filter_subset (fun y => dg G X y=1) Y)
  change ec G (X\X1) Y1 ≤ ec G (X\X1) Y at mono
  have smallone : #X1 ≤ 2 := by omega
  have high : 2*#Xh ≤ ec G Xh Y := by
    calc
      _ = ∑ _x ∈ Xh, 2 := by simp; omega
      _ ≤ _ := sum_le_sum (fun x hx => (mem_filter.mp hx).2)
  have highle := ec_mono_left (G := G) (filter_subset (fun x => 2 ≤ dg G Y x) X) Y
  change ec G Xh Y ≤ ec G X Y at highle
  have highcount : #Xh ≤ q-1 := by omega
  have partition : X\X0 = X1∪Xh := by
    ext x
    by_cases hx : x ∈ X
    · simp [X0,X1,Xh,hx]; omega
    · simp [X0,X1,Xh,hx]
  have disj : Disjoint X1 Xh := by
    apply Finset.disjoint_left.mpr
    intro x hx hh
    have one := (mem_filter.mp hx).2
    have two := (mem_filter.mp hh).2
    omega
  have cardpart := card_sdiff_add_card_eq_card (filter_subset (fun x => dg G Y x=0) X)
  change #(X\X0)+#X0=#X at cardpart
  rw [partition,card_union_of_disjoint disj] at cardpart
  have nonempty : X0.Nonempty := card_pos.mp (by omega)
  obtain ⟨a,ha⟩ := nonempty
  exact ⟨a,(mem_filter.mp ha).1,(mem_filter.mp ha).2⟩

omit host in
/-- In the original positive-Y/no-S1 Case B, a zero vertex and a nonhazardous degree-one head are derived. -/
theorem caseB_selector (host0 : Omit1PrefixR691.Host q 0 G A B)
    (unique : UniqueCut q G A B M) (d : Omit1Q0CutChainR699.CutData q G A B M)
    (positive : ∀ y ∈ B\M, 0 < dg G (A∩M) y)
    (noS1 : ∀ x ∈ A∩M, ∀ y ∈ B\M, G.Adj x y →
      ¬(dg G (B\M) x=1 ∧ dg G (A∩M) y=1)) :
    ∃ a ∈ A∩M, ∃ b ∈ B\M, dg G (B\M) a=0 ∧
      dg G (A∩M) b=1 ∧ ¬ Hazardous q G A B M a b := by
  have sizes := large_shores host0 d
  have hq := host0.large
  have et : ec G (A∩M) (B\M) = 2*q-1 := by have hh:=d.forward; omega
  obtain ⟨a,ha,da⟩ := zero_vertex_of_no_s1 (by omega) sizes.1 sizes.2 et positive noS1
  have many := many_one_heads sizes.2 (by omega) et positive
  let heads := (B\M).filter (fun y => dg G (A∩M) y=1)
  obtain ⟨b,hb,nb⟩ := exists_nonhazardous_head host0 unique d ha da heads
    (filter_subset _ _) (by change 2*q-3 ≤ #heads at many; omega)
  exact ⟨a,ha,b,(mem_filter.mp hb).1,da,(mem_filter.mp hb).2,nb⟩

lemma swapped_host : Omit1PrefixR691.Host q L G B A := by
  refine ⟨host.large,host.loss,host.disjoint.symm,?_,host.balanced.symm,
    host.bipartite.symm,host.cap,?_,host.proper⟩
  · rw [union_comm]; exact host.cover
  · rw [← AllHTopCritical.coreDefect_symm]; exact host.total

lemma g_swap_complement (S : Finset V) :
    g q G B A (univ\S) = g q G A B S := by
  have bi : B∩(univ\S)=B\S := by ext v; simp
  have ac : A\(univ\S)=A∩S := by ext v; simp
  have ai : A∩(univ\S)=A\S := by ext v; simp
  have ca := card_sdiff_add_card_eq_card (inter_subset_left : A∩S ⊆ A)
  have cb := card_sdiff_add_card_eq_card (inter_subset_left : B∩S ⊆ B)
  have as' : A\(A∩S)=A\S := by ext v; simp
  have bs' : B\(B∩S)=B\S := by ext v; simp
  rw [as'] at ca
  rw [bs'] at cb
  have bal := host.balanced
  unfold g k
  rw [bi,ac,ai,ec_comm (G := G) (B\S) (A∩S)]
  zify at ca cb bal
  nlinarith

lemma swapped_unique (unique : UniqueCut q G A B M) :
    UniqueCut q G B A (univ\M) := by
  refine ⟨by rw [g_swap_complement host]; exact unique.negative,?_⟩
  intro S hn
  have cS : univ\(univ\S)=S := by ext v; simp
  have ns : univ\S ≠ M := by
    intro he
    have hh := congrArg (fun T : Finset V => univ\T) he
    rw [cS] at hh
    exact hn hh
  have hi := g_swap_complement host (univ\S)
  rw [cS] at hi
  rw [hi]
  exact unique.others (univ\S) ns

omit host in
lemma swapped_q0_host (host0 : Omit1Q0CutChainR699.Host q G A B) :
    Omit1Q0CutChainR699.Host q G B A :=
  ⟨swapped_host host0.toHost,host0.min_degree,host0.no_regular⟩

omit host in
/-- The selector is manufactured from all original forward edges and all original zero cuts. -/
theorem selector_alternatives (host0 : Omit1Q0CutChainR699.Host q G A B)
    (unique : UniqueCut q G A B M) (d : Omit1Q0CutChainR699.CutData q G A B M) :
    ∃ a ∈ A∩M, ∃ b ∈ B\M,
      (dg G (B\M) a=0 ∧ dg G (A∩M) b=0) ∨
      (G.Adj a b ∧ dg G (B\M) a=1 ∧ dg G (A∩M) b=1) ∨
      (dg G (B\M) a=0 ∧ dg G (A∩M) b=1 ∧ ¬ Hazardous q G A B M a b ∧
        (∀ x ∈ A∩M, ∀ y ∈ B\M, G.Adj x y → ¬(dg G (B\M) x=1 ∧ dg G (A∩M) y=1))) ∨
      (dg G (B\M) a=1 ∧ dg G (A∩M) b=0 ∧
        ¬ Hazardous q G B A (univ\M) b a ∧
        (∀ x ∈ A∩M, ∀ y ∈ B\M, G.Adj x y → ¬(dg G (B\M) x=1 ∧ dg G (A∩M) y=1))) := by
  by_cases hs1 : ∃ a ∈ A∩M, ∃ b ∈ B\M,
      G.Adj a b ∧ dg G (B\M) a=1 ∧ dg G (A∩M) b=1
  · obtain ⟨a,ha,b,hb,hab,da,db⟩ := hs1
    exact ⟨a,ha,b,hb,Or.inr (Or.inl ⟨hab,da,db⟩)⟩
  have noS1 : ∀ a ∈ A∩M, ∀ b ∈ B\M, G.Adj a b →
      ¬(dg G (B\M) a=1 ∧ dg G (A∩M) b=1) := by
    intro a ha b hb hab hh
    exact hs1 ⟨a,ha,b,hb,hab,hh.1,hh.2⟩
  by_cases hy : ∃ b ∈ B\M, dg G (A∩M) b=0
  · obtain ⟨b,hb,db⟩ := hy
    by_cases hx : ∃ a ∈ A∩M, dg G (B\M) a=0
    · obtain ⟨a,ha,da⟩ := hx
      exact ⟨a,ha,b,hb,Or.inl ⟨da,db⟩⟩
    · have sh := swapped_q0_host host0
      have su := swapped_unique host0.toHost unique
      have sd := Omit1Q0CutChainR699.all_negative sh (univ\M)
        (by rw [g_swap_complement host0.toHost]; have hh:=unique.negative; omega)
      have bx : B∩(univ\M)=B\M := by ext v; simp
      have ay : A\(univ\M)=A∩M := by ext v; simp
      have pos : ∀ a ∈ A\(univ\M), 0 < dg G (B∩(univ\M)) a := by
        rw [bx,ay]
        intro a ha
        by_contra! hn
        exact hx ⟨a,ha,by omega⟩
      have ns : ∀ b ∈ B∩(univ\M), ∀ a ∈ A\(univ\M), G.Adj b a →
          ¬(dg G (A\(univ\M)) b=1 ∧ dg G (B∩(univ\M)) a=1) := by
        rw [bx,ay]
        intro b hb a ha hab hh
        exact noS1 a ha b hb hab.symm ⟨hh.2,hh.1⟩
      obtain ⟨b',hb',a',ha',db',da',nh⟩ := caseB_selector sh.toHost su sd pos ns
      simp only [bx,ay] at hb' ha' db' da'
      exact ⟨a',ha',b',hb',Or.inr (Or.inr (Or.inr ⟨da',db',nh,noS1⟩))⟩
  · have pos : ∀ b ∈ B\M, 0 < dg G (A∩M) b := by
      intro b hb
      by_contra! hn
      exact hy ⟨b,hb,by omega⟩
    obtain ⟨a,ha,b,hb,da,db,nh⟩ := caseB_selector host0.toHost unique d pos noS1
    exact ⟨a,ha,b,hb,Or.inr (Or.inr (Or.inl ⟨da,db,nh,noS1⟩))⟩

#print axioms large_shores
#print axioms many_one_heads
#print axioms zero_vertex_of_no_s1
#print axioms caseB_selector
#print axioms selector_alternatives
end Erdos585.Omit1UniqueR704

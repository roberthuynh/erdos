import R699.Main
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.Omit1ChainBranchR703
open QB4 B5 H3Unequal AllHTopCritical Omit1PrefixR691 Omit1Q0CutChainR699
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V} {q : ℕ} {A B : Finset V}
variable (host : Omit1Q0CutChainR699.Host q G A B)
include host

/-- Every nonempty actual negative-cut difference has its order-26 guard before floor use. -/
lemma difference_order_26 (S T : Finset V) (hs : g q G A B S < 0)
    (ht : g q G A B T < 0) (hne : (S \ T).Nonempty) : 26 ≤ #(S \ T) := by
  by_contra! hn
  obtain ⟨v, hv⟩ := hne
  have hvS := (mem_sdiff.mp hv).1
  have hvT := (mem_sdiff.mp hv).2
  have hq := host.large
  have rs := all_negative host S hs
  have rt := all_negative host T ht
  have hab : v ∈ A ∨ v ∈ B := by
    have hu : v ∈ A ∪ B := by rw [host.cover]; exact mem_univ v
    exact mem_union.mp hu
  rcases hab with ha | hb
  · have lower := diagonal_degree_A host S hs (mem_inter.mpr ⟨ha,hvS⟩)
    have upper := dg_difference_bound (G := G) (B ∩ S) (B ∩ T) v
    have hm := dg_le_ec (G := G) (Y := B ∩ T) (mem_sdiff.mpr ⟨ha,hvT⟩)
    have hc : #((B ∩ S) \ (B ∩ T)) ≤ #(S \ T) := by
      apply card_le_card
      intro x hx
      simp only [mem_sdiff, mem_inter] at hx ⊢
      tauto
    have hr := rt.reverse
    zify at lower upper hm hc hn
    have hqm : ((q-1 : ℕ) : ℤ) = (q : ℤ)-1 := by omega
    rw [hqm] at lower
    omega
  · have lower := diagonal_degree_B_complement host T ht (mem_sdiff.mpr ⟨hb,hvT⟩)
    have upper := dg_difference_bound (G := G) (A \ T) (A \ S) v
    have hm := dg_le_ec (G := G) (Y := A \ S) (mem_inter.mpr ⟨hb,hvS⟩)
    rw [ec_comm (G := G) (B ∩ S) (A \ S)] at hm
    have hc : #((A \ T) \ (A \ S)) ≤ #(S \ T) := by
      apply card_le_card
      intro x hx
      simp only [mem_sdiff] at hx ⊢
      tauto
    have hr := rs.reverse
    zify at lower upper hm hc hn
    have hqm : ((q-1 : ℕ) : ℤ) = (q : ℤ)-1 := by omega
    rw [hqm] at lower
    omega


/-- The entire original edge bypass of two distinct nested negative cuts is at most one. -/
theorem extreme_bypass (S T : Finset V) (hs : g q G A B S < 0)
    (ht : g q G A B T < 0) (hst : S ⊆ T) (hne : S ≠ T) :
    ec G S (univ \ T) ≤ 1 := by
  have rs := all_negative host S hs
  have rt := all_negative host T ht
  have hi : (T \ S).Nonempty := sdiff_nonempty.mpr (by
    intro h; exact hne (Subset.antisymm hst h))
  have h26 := difference_order_26 host T S ht hs hi
  have hord : 3 ≤ #(T \ S) := by omega
  have hd1 : Disjoint S (T \ S) := disjoint_sdiff_self_right
  have hd2 : Disjoint (T \ S) (univ \ T) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (mem_sdiff.mp hw).2 (mem_sdiff.mp hv).1
  have hu : S ∪ (T \ S) = T := union_sdiff_of_subset hst
  have ho : (T \ S) ∪ (univ \ T) = univ \ S := by
    ext v
    simp only [mem_union, mem_sdiff, mem_univ]
    have hv : v ∈ S → v ∈ T := fun h => hst h
    tauto
  have fs := f_disjoint host.toHost hd1
  rw [hu] at fs
  have fo := f_disjoint host.toHost hd2
  rw [ho] at fo
  have bs := complementary host.toHost S
  have bt := complementary host.toHost T
  have ep := ec_sdiff_add_right (G := G) (show T \ S ⊆ univ \ S by
    intro v hv; exact mem_sdiff.mpr ⟨mem_univ v,(mem_sdiff.mp hv).2⟩) S
  have ee : (univ \ S) \ (T \ S) = univ \ T := by
    ext v
    simp only [mem_sdiff, mem_univ]
    have hv : v ∈ S → v ∈ T := fun h => hst h
    tauto
  rw [ee] at ep
  have hp : #(T \ S) < Fintype.card V := by
    have hc := card_sdiff_add_card_eq_card hst
    have hS := rs.order
    have hT := card_le_univ T
    have hq := host.large
    omega
  have floorI := floor host.toHost (T \ S) hord hp
  have eqI : f q G A B (T \ S) + (ec G S (univ \ T) : ℤ) =
      3*(q : ℤ)-29 := by
    have a := rs.tight
    have b := rs.tight_complement
    have c := rt.tight
    have d := rt.tight_complement
    zify at ep
    omega
  omega

omit host [Fintype V] in
/-- Every negative cut contains the least pin and omits the greatest pin. -/
theorem negative_pins (Smin Smax : Finset V)
    (extrema : ∀ S : Finset V, g q G A B S < 0 → Smin ⊆ S ∧ S ⊆ Smax)
    {a b : V} (ha : a ∈ Smin) (hb : b ∉ Smax) (W : Finset V) :
    (a ∉ W → 0 ≤ g q G A B W) ∧ (b ∈ W → 0 ≤ g q G A B W) := by
  constructor
  · intro han
    by_contra! hh
    exact han ((extrema W hh).1 ha)
  · intro hbi
    by_contra! hh
    exact hb ((extrema W hh).2 hbi)

/-- The diagonal minimum and ambient cap bound every individual full-forward degree. -/
theorem forward_degree_bound (S : Finset V) (hs : g q G A B S < 0)
    {a : V} (ha : a ∈ A ∩ S) : dg G (B \ S) a ≤ q-1 := by
  have lo := diagonal_degree_A host S hs ha
  have hi := host.capA a (mem_inter.mp ha).1
  have he := dg_sdiff_add (G := G) (inter_subset_left : B ∩ S ⊆ B) a
  have hh : B \ (B ∩ S) = B \ S := by ext v; simp
  rw [hh] at he
  have hq := host.large
  omega

/-- The right extreme uses its own full forward rectangle, not the bypass. -/
theorem backward_degree_bound (T : Finset V) (ht : g q G A B T < 0)
    {b : V} (hb : b ∈ B \ T) : dg G (A ∩ T) b ≤ q-1 := by
  have lo := diagonal_degree_B_complement host T ht hb
  have hi := host.capB b (mem_sdiff.mp hb).1
  have he := dg_sdiff_add (G := G) (inter_subset_left : A ∩ T ⊆ A) b
  have hh : A \ (A ∩ T) = A \ T := by ext v; simp
  rw [hh] at he
  have hq := host.large
  omega

lemma swap_host : Omit1Q0CutChainR699.Host q G B A := by
  refine ⟨?_, host.min_degree, host.no_regular⟩
  refine ⟨host.large, host.loss, host.disjoint.symm, ?_, host.balanced.symm,
    host.bipartite.symm, host.cap, ?_, host.proper⟩
  · rw [union_comm]; exact host.cover
  · rw [← coreDefect_symm]; exact host.total

omit host [Fintype V] in
lemma zero_degree_exists (X Y : Finset V) (he : ec G X Y < #X) :
    ∃ v ∈ X, dg G Y v = 0 := by
  by_contra! hn
  have hl : #X ≤ ec G X Y := by
    calc
      #X = ∑ _v ∈ X, (1 : ℕ) := by simp
      _ ≤ ∑ v ∈ X, dg G Y v := sum_le_sum (fun v hv => by have hh := hn v hv; omega)
      _ = _ := rfl
  omega

/-- Saturation and the actual small reverse rectangle force a large diagonal shore. -/
lemma large_diagonal (X Y : Finset V) (hX : X ⊆ A) (hY : Y ⊆ B)
    (hy : Y.Nonempty) (hs : #X = #Y+2)
    (sat : ∀ v ∈ Y, G.degree v = 2*q-2)
    (rev : (ec G Y (A \ X) : ℤ) = (q : ℤ)-28) : 2*q-2 ≤ #X := by
  obtain ⟨v,hv⟩ := hy
  have hd := dg_sdiff_add (G := G) hX v
  rw [dg_eq_degree host.bipartite.symm (hY hv), sat v hv] at hd
  have hc := dg_le_card (G := G) X v
  have he := dg_le_ec (G := G) (Y := A \ X) hv
  have hq := host.large
  have yl : q+24 ≤ #Y := by omega
  have er : ec G Y (A \ X) < #Y := by omega
  obtain ⟨w,hw,hz⟩ := zero_degree_exists Y (A \ X) er
  have hdw := dg_sdiff_add (G := G) hX w
  rw [dg_eq_degree host.bipartite.symm (hY hw), sat w hw, hz] at hdw
  have hcw := dg_le_card (G := G) X w
  omega

theorem extreme_shore_sizes (S : Finset V) (hs : g q G A B S < 0) :
    2*q-2 ≤ #(A ∩ S) ∧ 2*q-2 ≤ #(B \ S) := by
  have rs := all_negative host S hs
  have cc := support_card host.toHost S
  have co := support_card host.toHost (univ \ S)
  have ki := rs.imbalance
  have hq := host.large
  have ho := rs.order
  have hco := rs.complement_order
  have ca := card_sdiff_add_card_eq_card (inter_subset_left : A ∩ S ⊆ A)
  have cb := card_sdiff_add_card_eq_card (inter_subset_left : B ∩ S ⊆ B)
  have ac : A ∩ (univ \ S) = A \ S := by ext v; simp
  have bc : B ∩ (univ \ S) = B \ S := by ext v; simp
  have ad : A \ (A ∩ S) = A \ S := by ext v; simp
  have bd : B \ (B \ S) = B ∩ S := by ext v; simp
  have asd : A \ (A ∩ S) = A \ S := by ext v; simp
  have bs2 : B \ (B ∩ S) = B \ S := by ext v; simp
  rw [ad] at ca
  rw [bs2] at cb
  rw [ac,bc] at co
  unfold k at ki
  constructor
  · apply large_diagonal host (A ∩ S) (B ∩ S) inter_subset_left inter_subset_left
      (card_pos.mp (by omega)) (by omega) rs.saturated_B
    rw [ad,ec_comm]
    exact rs.reverse
  · apply large_diagonal (swap_host host) (B \ S) (A \ S) sdiff_subset sdiff_subset
      (card_pos.mp (by have bal := host.balanced; omega))
      (by have bal := host.balanced; omega) rs.saturated_A
    rw [bd]
    exact rs.reverse

omit host [Fintype V] in
/-- A full-forward sum supplies a low-degree vertex avoiding the at-most-one bypass. -/
lemma low_choice (X Y Z : Finset V) (hq : 4 ≤ q) (hx : 2*q-2 ≤ #X)
    (hy : ec G X Y = 2*q-1) (hz : ec G X Z ≤ 1) :
    ∃ v ∈ X, dg G Y v ≤ 1 ∧ dg G Z v = 0 := by
  by_contra! hn
  have hp : ∀ v ∈ X, 2 ≤ dg G Y v + 2*dg G Z v := by
    intro v hv
    by_cases h : dg G Y v ≤ 1
    · have hh := hn v hv h; omega
    · omega
  have hh : 2*#X ≤ ec G X Y + 2*ec G X Z := by
    calc
      2*#X = ∑ _v ∈ X, (2 : ℕ) := by simp; omega
      _ ≤ ∑ v ∈ X, (dg G Y v + 2*dg G Z v) := sum_le_sum hp
      _ = ec G X Y + 2*ec G X Z := by rw [sum_add_distrib, ← mul_sum]; rfl
  omega

/-- Construct one original pair using the two separate full-forward extreme sums. -/
theorem extreme_low_pair (S T : Finset V) (hs : g q G A B S < 0)
    (ht : g q G A B T < 0) (hst : S ⊆ T) (hne : S ≠ T) :
    ∃ a ∈ A ∩ S, ∃ b ∈ B \ T,
      dg G (B \ S) a ≤ 1 ∧ dg G (A ∩ T) b ≤ 1 ∧
      dg G (B \ T) a = 0 ∧ dg G (A ∩ S) b = 0 := by
  have bypass := extreme_bypass host S T hs ht hst hne
  have rs := all_negative host S hs
  have rt := all_negative host T ht
  have szS := extreme_shore_sizes host S hs
  have szT := extreme_shore_sizes host T ht
  have hyS : ec G (A ∩ S) (B \ S) = 2*q-1 := by have hq := host.large; have hf := rs.forward; omega
  have hyT : ec G (B \ T) (A ∩ T) = 2*q-1 := by
    rw [ec_comm]; have hq := host.large; have hf := rt.forward; omega
  have hz : ec G (A ∩ S) (B \ T) ≤ 1 := by
    have hm := ec_mono_left (G := G) (inter_subset_right : A ∩ S ⊆ S) (B \ T)
    have hm2 := ec_mono_right (G := G) S (show B \ T ⊆ univ \ T by
      intro v hv; exact mem_sdiff.mpr ⟨mem_univ v,(mem_sdiff.mp hv).2⟩)
    omega
  obtain ⟨a,ha,hla,hza⟩ := low_choice (A ∩ S) (B \ S) (B \ T)
    (by have hq := host.large; omega) szS.1 hyS hz
  rw [ec_comm] at hz
  obtain ⟨b,hb,hlb,hzb⟩ := low_choice (B \ T) (A ∩ T) (A ∩ S)
    (by have hq := host.large; omega) szT.2 hyT hz
  exact ⟨a,ha,b,hb,hla,hlb,hza,hzb⟩

omit host [Fintype V] in
lemma k_disjoint {X Y : Finset V} (hd : Disjoint X Y) :
    k A B (X ∪ Y) = k A B X + k A B Y := by
  have ha := card_union_of_disjoint (hd.mono inter_subset_right inter_subset_right :
    Disjoint (A ∩ X) (A ∩ Y))
  have hb := card_union_of_disjoint (hd.mono inter_subset_right inter_subset_right :
    Disjoint (B ∩ X) (B ∩ Y))
  rw [← inter_union_distrib_left] at ha hb
  unfold k
  omega

omit host [Fintype V] in
lemma sA_disjoint {X Y : Finset V} (hd : Disjoint X Y) :
    sA q G A B (X ∪ Y) = sA q G A B X + sA q G A B Y := by
  unfold sA deficiency
  rw [inter_union_distrib_left, sum_union (hd.mono inter_subset_right inter_subset_right)]

/-- Exact potential uncrossing on actual disjoint original edge units. -/
lemma f_uncross (N W : Finset V) :
    f q G A B N + f q G A B W = f q G A B (N ∩ W) +
      f q G A B (N ∪ W) + (ec G (N \ W) (W \ N) : ℤ) := by
  have dpx : Disjoint (N ∩ W) (N \ W) := by
    apply Finset.disjoint_left.mpr; intro v hv hw
    exact (mem_sdiff.mp hw).2 (mem_inter.mp hv).2
  have dpy : Disjoint (N ∩ W) (W \ N) := by
    apply Finset.disjoint_left.mpr; intro v hv hw
    exact (mem_sdiff.mp hw).2 (mem_inter.mp hv).1
  have dny : Disjoint N (W \ N) := disjoint_sdiff_self_right
  have upx : (N ∩ W) ∪ (N \ W) = N := by ext v; simp; tauto
  have upy : (N ∩ W) ∪ (W \ N) = W := by ext v; simp; tauto
  have uny : N ∪ (W \ N) = N ∪ W := union_sdiff_self_eq_union
  have a := f_disjoint host.toHost dpx
  have b := f_disjoint host.toHost dpy
  have c := f_disjoint host.toHost dny
  rw [upx] at a
  rw [upy] at b
  rw [uny] at c
  have he := ec_union_left (G := G) dpx (W \ N)
  rw [upx] at he
  zify at he
  omega

/-- The original cut function has the exact unit-edge uncrossing identity. -/
lemma g_uncross (N W : Finset V) :
    g q G A B N + g q G A B W = g q G A B (N ∩ W) +
      g q G A B (N ∪ W) + (ec G (N \ W) (W \ N) : ℤ) := by
  have hf := f_uncross host N W
  have ha : sA q G A B N + sA q G A B W =
      sA q G A B (N ∩ W) + sA q G A B (N ∪ W) := by
    unfold sA deficiency
    have h := sum_union_inter (s₁ := A ∩ N) (s₂ := A ∩ W)
      (f := fun v => 2*(q : ℤ)-2-(dg G B v : ℤ))
    have hi : (A ∩ N) ∩ (A ∩ W) = A ∩ (N ∩ W) := by ext v; simp; tauto
    have hu : (A ∩ N) ∪ (A ∩ W) = A ∩ (N ∪ W) := by ext v; simp; tauto
    rw [hi,hu] at h
    omega
  have hk : k A B N + k A B W = k A B (N ∩ W) + k A B (N ∪ W) := by
    have ca := card_union_add_card_inter (A ∩ N) (A ∩ W)
    have cb := card_union_add_card_inter (B ∩ N) (B ∩ W)
    have hiA : (A ∩ N) ∩ (A ∩ W) = A ∩ (N ∩ W) := by ext v; simp; tauto
    have huA : (A ∩ N) ∪ (A ∩ W) = A ∩ (N ∪ W) := by ext v; simp; tauto
    have hiB : (B ∩ N) ∩ (B ∩ W) = B ∩ (N ∩ W) := by ext v; simp; tauto
    have huB : (B ∩ N) ∪ (B ∩ W) = B ∩ (N ∪ W) := by ext v; simp; tauto
    rw [hiA,huA] at ca
    rw [hiB,huB] at cb
    unfold k
    omega
  have cN := cut_identity (q := q) (G := G) (A := A) (B := B) N
  have cW := cut_identity (q := q) (G := G) (A := A) (B := B) W
  have cP := cut_identity (q := q) (G := G) (A := A) (B := B) (N ∩ W)
  have cU := cut_identity (q := q) (G := G) (A := A) (B := B) (N ∪ W)
  omega

/-- The tiny removed-cell equation uses saturation inside the actual negative cut. -/
lemma removed_identity (N W : Finset V) (hn : g q G A B N < 0) :
    g q G A B (N ∩ W) = f q G A B (N \ W) + k A B (N \ W) - 1 -
      (ec G (N \ W) (univ \ N) : ℤ) := by
  have rn := all_negative host N hn
  have dpx : Disjoint (N ∩ W) (N \ W) := by
    apply Finset.disjoint_left.mpr; intro v hv hw
    exact (mem_sdiff.mp hw).2 (mem_inter.mp hv).2
  have upx : (N ∩ W) ∪ (N \ W) = N := by ext v; simp; tauto
  have fp := f_disjoint host.toHost dpx
  have ap := sA_disjoint (q := q) (G := G) (A := A) (B := B) dpx
  have kp := k_disjoint (A := A) (B := B) dpx
  rw [upx] at fp ap kp
  have cN := cut_identity (q := q) (G := G) (A := A) (B := B) N
  have cP := cut_identity (q := q) (G := G) (A := A) (B := B) (N ∩ W)
  have bx : sB q G A B (N \ W) = 0 := by
    unfold sB deficiency
    apply sum_eq_zero
    intro v hv
    have hvB := (mem_inter.mp hv).1
    have hvN := (mem_sdiff.mp (mem_inter.mp hv).2).1
    rw [dg_eq_degree host.bipartite.symm hvB,
      rn.saturated_B v (mem_inter.mpr ⟨hvB,hvN⟩)]
    have hq := host.large
    omega
  have bi := boundary_identity host.toHost (N \ W)
  rw [bx] at bi
  have dd : Disjoint (N ∩ W) (univ \ N) := by
    apply Finset.disjoint_left.mpr; intro v hv hw
    exact (mem_sdiff.mp hw).2 (mem_inter.mp hv).1
  have uu : (N ∩ W) ∪ (univ \ N) = univ \ (N \ W) := by ext v; simp; tauto
  have ee := ec_union_right (G := G) dd (N \ W)
  rw [uu, ec_comm (G := G) (N \ W) (N ∩ W)] at ee
  have va := rn.value
  zify at ee
  omega

/-- The tiny added-cell equation uses actual saturation outside the negative cut. -/
lemma added_identity (N W : Finset V) (hn : g q G A B N < 0) :
    g q G A B (N ∪ W) = f q G A B (W \ N) - k A B (W \ N) - 1 -
      (ec G N (W \ N) : ℤ) := by
  have rn := all_negative host N hn
  have dd : Disjoint N (W \ N) := disjoint_sdiff_self_right
  have uu : N ∪ (W \ N) = N ∪ W := union_sdiff_self_eq_union
  have ff := f_disjoint host.toHost dd
  have aa := sA_disjoint (q := q) (G := G) (A := A) (B := B) dd
  have kk := k_disjoint (A := A) (B := B) dd
  rw [uu] at ff aa kk
  have az : sA q G A B (W \ N) = 0 := by
    unfold sA deficiency
    apply sum_eq_zero
    intro v hv
    have hvA := (mem_inter.mp hv).1
    have hvN := (mem_sdiff.mp (mem_inter.mp hv).2).2
    rw [dg_eq_degree host.bipartite hvA,
      rn.saturated_A v (mem_sdiff.mpr ⟨hvA,hvN⟩)]
    have hq := host.large
    omega
  have cN := cut_identity (q := q) (G := G) (A := A) (B := B) N
  have cU := cut_identity (q := q) (G := G) (A := A) (B := B) (N ∪ W)
  have va := rn.value
  omega

/-- The stronger cross-cell identity retained in the independent accepted proof. -/
lemma cross_cell_identity (N W : Finset V) (hn : g q G A B N < 0) :
    f q G A B (N \ W) + f q G A B (W \ N) +
      (ec G (N ∩ W) (univ \ (N ∪ W)) : ℤ) =
      3*(q : ℤ)-30 + g q G A B W + k A B W := by
  have rn := all_negative host N hn
  have dpx : Disjoint (N ∩ W) (N \ W) := by
    apply Finset.disjoint_left.mpr; intro v hv hw
    exact (mem_sdiff.mp hw).2 (mem_inter.mp hv).2
  have dpy : Disjoint (N ∩ W) (W \ N) := by
    apply Finset.disjoint_left.mpr; intro v hv hw
    exact (mem_sdiff.mp hw).2 (mem_inter.mp hv).1
  have dyz : Disjoint (W \ N) (univ \ (N ∪ W)) := by
    apply Finset.disjoint_left.mpr; intro v hv hw
    exact (mem_sdiff.mp hw).2 (mem_union.mpr (Or.inr (mem_sdiff.mp hv).1))
  have upx : (N ∩ W) ∪ (N \ W) = N := by ext v; simp; tauto
  have upy : (N ∩ W) ∪ (W \ N) = W := by ext v; simp; tauto
  have uyz : (W \ N) ∪ (univ \ (N ∪ W)) = univ \ N := by ext v; simp; tauto
  have ep := ec_union_left (G := G) dpx (univ \ N)
  have ex := ec_union_right (G := G) dyz (N \ W)
  have ey := ec_union_left (G := G) dpx (W \ N)
  have epp := ec_union_right (G := G) dyz (N ∩ W)
  rw [upx] at ep ey
  rw [uyz] at ex epp
  have kp := k_disjoint (A := A) (B := B) dpx
  have kw := k_disjoint (A := A) (B := B) dpy
  rw [upx] at kp
  rw [upy] at kw
  have bn := complementary host.toHost N
  have a := removed_identity host N W hn
  have b := added_identity host N W hn
  have c := g_uncross host N W
  have val := rn.value
  have bal := rn.imbalance
  have tn := rn.tight
  have tc := rn.tight_complement
  zify at ep ex ey epp
  omega

/-- An actual band cut differs from a negative cut by a tiny cell in one direction. -/
theorem cross_localization (N W : Finset V) (hn : g q G A B N < 0)
    (band : g q G A B W ≤ (q : ℤ)-1) :
    #(N \ W) ≤ 2 ∨ #(W \ N) ≤ 2 := by
  by_contra! hh
  have rn := all_negative host N hn
  have hx : #(N \ W) < Fintype.card V :=
    (card_le_card (sdiff_subset : N \ W ⊆ N)).trans_lt rn.proper
  have hy : #(W \ N) < Fintype.card V := by
    have sub : W \ N ⊆ univ \ N := by
      intro v hv; exact mem_sdiff.mpr ⟨mem_univ v,(mem_sdiff.mp hv).2⟩
    exact (card_le_card sub).trans_lt rn.complement_proper
  have fx := floor host.toHost (N \ W) (by omega) hx
  have fy := floor host.toHost (W \ N) (by omega) hy
  have ci := cross_cell_identity host N W hn
  have ck := counting host.toHost W band
  have en : 0 ≤ (ec G (N ∩ W) (univ \ (N ∪ W)) : ℤ) := Nat.cast_nonneg _
  have hq : (16384 : ℤ) ≤ q := by exact_mod_cast host.large
  omega

lemma dg_left (a : V) (ha : a ∈ A) (X : Finset V) :
    dg G X a = dg G (B ∩ X) a := by
  have p := support_partition host.toHost X
  have e := dg_union_of_disjoint (G := G)
    (host.disjoint.mono inter_subset_left inter_subset_left : Disjoint (A ∩ X) (B ∩ X)) a
  rw [p] at e
  have z := ec_internal_zero host.disjoint host.bipartite (Subset.refl A)
  have h := dg_le_ec (G := G) (Y := A) ha
  have m := dg_mono (G := G) (inter_subset_left : A ∩ X ⊆ A) a
  omega

lemma dg_right (b : V) (hb : b ∈ B) (X : Finset V) :
    dg G X b = dg G (A ∩ X) b := dg_left (swap_host host) b hb X

lemma f_singleton (a : V) : f q G A B {a} = (q : ℤ)-1 := by
  have h := f_twice host.toHost {a}
  have hz : ({w ∈ ({a} : Finset V) | G.Adj a w} : Finset V) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro w hw
    have e : w = a := mem_singleton.mp hw
    subst w
    exact G.loopless.irrefl a
  simp only [ec,sum_singleton,dg,hz,card_empty,Nat.cast_zero,sub_zero,card_singleton,
    Nat.cast_one,mul_one] at h
  omega

omit host [Fintype V] in
lemma k_singleton_A {a : V} (ha : a ∈ A) (hb : a ∉ B) : k A B {a} = 1 := by
  simp [k,ha,hb]
omit host [Fintype V] in
lemma k_singleton_B {b : V} (hb : b ∈ B) (ha : b ∉ A) : k A B {b} = -1 := by
  simp [k,ha,hb]

lemma pair_potential {a x : V} (hx : a ≠ x) :
    2*((q : ℤ)-1)-1 ≤ f q G A B {a,x} := by
  have hd : Disjoint ({a} : Finset V) {x} := by simpa using hx
  have h := f_disjoint host.toHost hd
  have ee := AllHTopCritical.ec_le_product (G := G) ({a} : Finset V) {x}
  rw [f_singleton host a, f_singleton host x] at h
  simp only [singleton_union, card_singleton, mul_one] at h ee
  omega

lemma pair_same_A {a x : V} (ha : a ∈ A) (hxa : x ∈ A) (hx : a ≠ x) :
    f q G A B {a,x} = 2*((q : ℤ)-1) := by
  have hd : Disjoint ({a} : Finset V) {x} := by simpa using hx
  have h := f_disjoint host.toHost hd
  have ee := ec_mono (G := G) (singleton_subset_iff.mpr ha) (singleton_subset_iff.mpr hxa)
  have zz := ec_internal_zero host.disjoint host.bipartite (Subset.refl A)
  rw [f_singleton host a, f_singleton host x] at h
  simp only [singleton_union] at h
  omega

lemma pair_same_B {b x : V} (hb : b ∈ B) (hxb : x ∈ B) (hx : b ≠ x) :
    f q G A B {b,x} = 2*((q : ℤ)-1) := by
  have h := pair_same_A (swap_host host) hb hxb hx
  have sw : ∀ Z : Finset V, f q G B A Z = f q G A B Z := by
    intro Z; unfold f; rw [coreDefect_symm]
  rwa [sw] at h

omit host [Fintype V] in
lemma tiny_cases {X : Finset V} {a : V} (ha : a ∈ X) (hc : #X ≤ 2) :
    X = {a} ∨ ∃ x, x ≠ a ∧ X = {a,x} := by
  have he := card_erase_add_one ha
  by_cases hz : X.erase a = ∅
  · left
    have h := insert_erase ha
    rw [hz] at h
    exact h.symm
  · obtain ⟨x,hx⟩ := nonempty_iff_ne_empty.mpr hz
    have hxne := (mem_erase.mp hx).1
    have eq : X.erase a = {x} := eq_singleton_iff_unique_mem.mpr ⟨hx,by
      intro y hy
      exact card_le_one.mp (by omega) y hy x hx⟩
    have h := insert_erase ha
    rw [eq] at h
    exact Or.inr ⟨x,hxne,h.symm⟩

/-- All singleton/doubleton removed cells, with their original degree guard. -/
lemma tiny_removed (N W : Finset V) (hn : g q G A B N < 0) {a : V}
    (ha : a ∈ A ∩ (N \ W)) {lam : ℕ} (_hlam : lam ≤ 1)
    (low : dg G (B \ N) a ≤ lam) (tiny : #(N \ W) ≤ 2) :
    (q : ℤ)-1-lam ≤ g q G A B (N ∩ W) ∧
    (g q G A B (N ∩ W) ≤ (q : ℤ)-1-lam →
      N \ W = {a} ∧ dg G (univ \ N) a = lam) := by
  have rn := all_negative host N hn
  have eq := removed_identity host N W hn
  have haA := (mem_inter.mp ha).1
  have haX := (mem_inter.mp ha).2
  have haB : a ∉ B := fun hb => Finset.disjoint_left.mp host.disjoint haA hb
  have da : dg G (univ \ N) a ≤ lam := by
    rw [dg_left host a haA]
    have ee : B ∩ (univ \ N) = B \ N := by ext v; simp
    rwa [ee]
  rcases tiny_cases haX tiny with hsingle | ⟨x,hxa,hpair⟩
  · rw [hsingle, f_singleton host a, k_singleton_A haA haB] at eq
    simp only [ec,sum_singleton] at eq
    constructor
    · omega
    · intro hh; exact ⟨hsingle,by omega⟩
  · have hx : a ≠ x := Ne.symm hxa
    have hxN : x ∈ N := by
      have hi : x ∈ N \ W := by rw [hpair]; simp
      exact (mem_sdiff.mp hi).1
    have dh : Disjoint ({a} : Finset V) {x} := by simpa using hx
    have kk := k_disjoint (A := A) (B := B) dh
    simp only [singleton_union] at kk
    have ee : ec G {a,x} (univ \ N) = dg G (univ \ N) a + dg G (univ \ N) x := by
      simp [ec,hx]
    have hab : x ∈ A ∨ x ∈ B := by
      have hu : x ∈ A ∪ B := by rw [host.cover]; exact mem_univ x
      exact mem_union.mp hu
    rcases hab with hxA | hxB
    · have hxNB : x ∉ B := fun hb => Finset.disjoint_left.mp host.disjoint hxA hb
      have dx := forward_degree_bound host N hn (mem_inter.mpr ⟨hxA,hxN⟩)
      have dx' : dg G (univ \ N) x ≤ q-1 := by
        rw [dg_left host x hxA]
        have e : B ∩ (univ \ N) = B \ N := by ext v; simp
        rwa [e]
      rw [k_singleton_A haA haB,k_singleton_A hxA hxNB] at kk
      rw [hpair,pair_same_A host haA hxA hx,kk,ee] at eq
      have hq := host.large
      constructor
      · omega
      · intro hh; exfalso; omega
    · have hxNA : x ∉ A := fun ha => Finset.disjoint_left.mp host.disjoint ha hxB
      have dx : (dg G (univ \ N) x : ℤ) ≤ (q : ℤ)-28 := by
        rw [dg_right host x hxB]
        have e : A ∩ (univ \ N) = A \ N := by ext v; simp
        rw [e]
        have h := dg_le_ec (G := G) (Y := A \ N) (mem_inter.mpr ⟨hxB,hxN⟩)
        rw [ec_comm] at h
        have hr := rn.reverse
        omega
      rw [k_singleton_A haA haB,k_singleton_B hxB hxNA] at kk
      have fp := pair_potential host hx
      rw [hpair,kk,ee] at eq
      have hq := host.large
      constructor
      · omega
      · intro hh; exfalso; omega

/-- Swapping original shores and complementing the source set preserves g exactly. -/
lemma g_swap_complement (S : Finset V) :
    g q G B A (univ \ S) = g q G A B S := by
  have ca := card_sdiff_add_card_eq_card (inter_subset_left : A ∩ S ⊆ A)
  have cb := card_sdiff_add_card_eq_card (inter_subset_left : B ∩ S ⊆ B)
  have ea : A \ (A ∩ S) = A \ S := by ext v; simp
  have eb : B \ (B ∩ S) = B \ S := by ext v; simp
  rw [ea] at ca
  rw [eb] at cb
  have ac : A ∩ (univ \ S) = A \ S := by ext v; simp
  have bc : B ∩ (univ \ S) = B \ S := by ext v; simp
  have ab : A \ (univ \ S) = A ∩ S := by ext v; simp
  have hk : k B A (univ \ S) = k A B S := by
    unfold k
    rw [ac,bc]
    have bal := host.balanced
    omega
  unfold g
  rw [bc,ab,hk,ec_comm]

lemma tiny_added (N W : Finset V) (hn : g q G A B N < 0) {b : V}
    (hb : b ∈ B ∩ (W \ N)) (low : dg G (A ∩ N) b ≤ 1)
    (tiny : #(W \ N) ≤ 2) :
    (q : ℤ)-2 ≤ g q G A B (N ∪ W) ∧
    (g q G A B (N ∪ W) ≤ (q : ℤ)-2 →
      W \ N = {b} ∧ dg G N b = 1) := by
  have hn' : g q G B A (univ \ N) < 0 := by rwa [g_swap_complement host N]
  have ec : (univ \ N) \ (univ \ W) = W \ N := by ext v; simp; tauto
  have ep : (univ \ N) ∩ (univ \ W) = univ \ (N ∪ W) := by ext v; simp
  have ea : A \ (univ \ N) = A ∩ N := by ext v; simp
  have ed : univ \ (univ \ N) = N := by ext v; simp
  have h := tiny_removed (swap_host host) (univ \ N) (univ \ W) hn'
    (a := b) (by rwa [ec]) (lam := 1) (by decide) (by rwa [ea]) (by rwa [ec])
  rw [ec,ep,g_swap_complement host (N ∪ W),ed] at h
  norm_num only [Nat.cast_one, sub_sub] at h
  exact h

/-- A tiny added cell containing any A vertex forces a positive union cut. -/
lemma tiny_added_A (N W : Finset V) (hn : g q G A B N < 0) {a : V}
    (ha : a ∈ A ∩ (W \ N)) (tiny : #(W \ N) ≤ 2) :
    0 < g q G A B (N ∪ W) := by
  have rn := all_negative host N hn
  have eq := added_identity host N W hn
  have haA := (mem_inter.mp ha).1
  have haX := (mem_inter.mp ha).2
  have haN := (mem_sdiff.mp haX).2
  have haB : a ∉ B := fun hb => Finset.disjoint_left.mp host.disjoint haA hb
  have reverse_bound : ∀ v ∈ A \ N, (dg G N v : ℤ) ≤ (q : ℤ)-28 := by
    intro v hv
    rw [dg_left host v (mem_sdiff.mp hv).1]
    have he := dg_le_ec (G := G) (Y := B ∩ N) hv
    have hr := rn.reverse
    omega
  have da := reverse_bound a (mem_sdiff.mpr ⟨haA,haN⟩)
  rcases tiny_cases haX tiny with hsingle | ⟨x,hxa,hpair⟩
  · rw [hsingle, f_singleton host a, k_singleton_A haA haB] at eq
    rw [ec_comm] at eq
    simp only [ec,sum_singleton] at eq
    omega
  · have hx : a ≠ x := Ne.symm hxa
    have hxN : x ∉ N := by
      have hi : x ∈ W \ N := by rw [hpair]; simp
      exact (mem_sdiff.mp hi).2
    have dh : Disjoint ({a} : Finset V) {x} := by simpa using hx
    have kk := k_disjoint (A := A) (B := B) dh
    simp only [singleton_union] at kk
    have ee : ec G N {a,x} = dg G N a + dg G N x := by
      rw [ec_comm]; simp [ec,hx]
    have hab : x ∈ A ∨ x ∈ B := by
      have hu : x ∈ A ∪ B := by rw [host.cover]; exact mem_univ x
      exact mem_union.mp hu
    rcases hab with hxA | hxB
    · have hxNB : x ∉ B := fun hb => Finset.disjoint_left.mp host.disjoint hxA hb
      have dx := reverse_bound x (mem_sdiff.mpr ⟨hxA,hxN⟩)
      rw [k_singleton_A haA haB,k_singleton_A hxA hxNB] at kk
      rw [hpair,pair_same_A host haA hxA hx,kk,ee] at eq
      omega
    · have hxNA : x ∉ A := fun ha => Finset.disjoint_left.mp host.disjoint ha hxB
      have dx : dg G N x ≤ q-1 := by
        rw [dg_right host x hxB]
        exact backward_degree_bound host N hn (mem_sdiff.mpr ⟨hxB,hxN⟩)
      rw [k_singleton_A haA haB,k_singleton_B hxB hxNA] at kk
      have fp := pair_potential host hx
      rw [hpair,kk,ee] at eq
      have hq := host.large
      omega

/-- A zero cut missing a low-forward A pin cannot extend beyond the negative cut in A. -/
theorem zero_pin (N J : Finset V) (hn : g q G A B N < 0) {a : V}
    (ha : a ∈ A ∩ N) (low : dg G (B \ N) a ≤ 1)
    (zero : g q G A B J = 0) (missing : a ∉ J) : A ∩ (J \ N) = ∅ := by
  have loc := cross_localization host N J hn (by have hq := host.large; omega)
  have unc := g_uncross host N J
  have vn := (all_negative host N hn).value
  have lp := all_cut_lower host (N ∩ J)
  have lu := all_cut_lower host (N ∪ J)
  have en : 0 ≤ (ec G (N \ J) (J \ N) : ℤ) := Nat.cast_nonneg _
  have hq : (16384 : ℤ) ≤ q := by exact_mod_cast host.large
  rcases loc with ht | ht
  · have tr := tiny_removed host N J hn
      (a := a) (by exact mem_inter.mpr ⟨(mem_inter.mp ha).1,
        mem_sdiff.mpr ⟨(mem_inter.mp ha).2,missing⟩⟩)
      (lam := 1) (by decide) low ht
    exfalso
    omega
  · apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have ta := tiny_added_A host N J hn hx ht
    omega

/-- The mirrored zero pin is derived on the same actual original graph. -/
theorem mirrored_zero_pin (N J : Finset V) (hn : g q G A B N < 0) {b : V}
    (hb : b ∈ B \ N) (low : dg G (A ∩ N) b ≤ 1)
    (zero : g q G A B J = 0) (present : b ∈ J) : B ∩ (N \ J) = ∅ := by
  have hn' : g q G B A (univ \ N) < 0 := by rwa [g_swap_complement host N]
  have hz : g q G B A (univ \ J) = 0 := by rwa [g_swap_complement host J]
  have eh : B ∩ (univ \ N) = B \ N := by ext v; simp
  have el : A \ (univ \ N) = A ∩ N := by ext v; simp
  have h := zero_pin (swap_host host) (univ \ N) (univ \ J) hn'
    (a := b) (by rwa [eh]) (by rwa [el]) hz (by simp [present])
  have ec : (univ \ J) \ (univ \ N) = N \ J := by ext v; simp; tauto
  rwa [ec] at h

/-- A low extreme pair pays every original cut containing only its B pin. -/
lemma low_pair_pays_band (S T : Finset V) (hs : g q G A B S < 0)
    (ht : g q G A B T < 0)
    (extrema : ∀ N : Finset V, g q G A B N < 0 → S ⊆ N ∧ N ⊆ T)
    {a b : V} (ha : a ∈ A ∩ S) (hb : b ∈ B \ T)
    (lowA : dg G (B \ S) a ≤ 1) (lowB : dg G (A ∩ T) b ≤ 1)
    (zeroA : dg G (B \ T) a = 0) (zeroB : dg G (A ∩ S) b = 0)
    (W : Finset V) (amissing : a ∉ W) (bpresent : b ∈ W) :
    (q : ℤ) ≤ g q G A B W := by
  by_contra! band
  have bs : g q G A B W ≤ (q : ℤ)-1 := by omega
  have hst := (extrema T ht).1
  have haT : a ∈ T := hst (mem_inter.mp ha).2
  have hbT : b ∉ T := (mem_sdiff.mp hb).2
  have loc := cross_localization host T W ht bs
  have unc := g_uncross host T W
  have val := (all_negative host T ht).value
  have en : 0 ≤ (ec G (T \ W) (W \ T) : ℤ) := Nat.cast_nonneg _
  have pinP := (negative_pins S T extrema (mem_inter.mp ha).2 hbT (T ∩ W)).1
    (by intro h; exact amissing (mem_inter.mp h).2)
  have pinU := (negative_pins S T extrema (mem_inter.mp ha).2 hbT (T ∪ W)).2
    (mem_union.mpr (Or.inr bpresent))
  rcases loc with tx | ty
  · have tr := tiny_removed host T W ht (a := a)
      (mem_inter.mpr ⟨(mem_inter.mp ha).1,mem_sdiff.mpr ⟨haT,amissing⟩⟩)
      (lam := 0) (by decide) (by omega) tx
    omega
  · have ta := tiny_added host T W ht (b := b)
      (mem_inter.mpr ⟨(mem_sdiff.mp hb).1,mem_sdiff.mpr ⟨bpresent,hbT⟩⟩)
      lowB ty
    have upper : g q G A B (T ∪ W) ≤ (q : ℤ)-2 := by omega
    obtain ⟨single,db⟩ := ta.2 upper
    have zp : g q G A B (T ∩ W) = 0 := by omega
    have ez : ec G (T \ W) (W \ T) = 0 := by omega
    rw [single,ec_comm] at ez
    simp only [ec,sum_singleton] at ez
    have de := dg_sdiff_add (G := G) (inter_subset_left : T ∩ W ⊆ T) b
    have ee : T \ (T ∩ W) = T \ W := by ext v; simp
    rw [ee] at de
    have dp : dg G (T ∩ W) b = 1 := by omega
    have pin := zero_pin host S (T ∩ W) hs ha lowA zp
      (by intro h; exact amissing (mem_inter.mp h).2)
    have sub : A ∩ (T ∩ W) ⊆ A ∩ S := by
      intro v hv
      refine mem_inter.mpr ⟨(mem_inter.mp hv).1,?_⟩
      by_contra hn
      have hi : v ∈ A ∩ ((T ∩ W) \ S) :=
        mem_inter.mpr ⟨(mem_inter.mp hv).1,mem_sdiff.mpr ⟨(mem_inter.mp hv).2,hn⟩⟩
      rw [pin] at hi
      exact notMem_empty v hi
    rw [dg_right host b (mem_sdiff.mp hb).1] at dp
    have dm := dg_mono (G := G) sub b
    omega

/-- Strict-chain existence with one pair paying all original unit cuts simultaneously. -/
theorem strict_chain_unit_cuts (S T : Finset V) (hs : g q G A B S < 0)
    (ht : g q G A B T < 0) (hne : S ≠ T)
    (extrema : ∀ N : Finset V, g q G A B N < 0 → S ⊆ N ∧ N ⊆ T) :
    ∃ a ∈ A ∩ S, ∃ b ∈ B \ T, ∀ W : Finset V,
      (q : ℤ)*((if b ∈ W then 1 else 0)-(if a ∈ W then 1 else 0)) ≤
        g q G A B W := by
  have hst := (extrema T ht).1
  obtain ⟨a,ha,b,hb,lowA,lowB,zeroA,zeroB⟩ :=
    extreme_low_pair host S T hs ht hst hne
  refine ⟨a,ha,b,hb,?_⟩
  intro W
  have pins := negative_pins S T extrema (mem_inter.mp ha).2 (mem_sdiff.mp hb).2 W
  by_cases am : a ∈ W <;> by_cases bm : b ∈ W
  · simp only [if_pos am,if_pos bm,sub_self,mul_zero]
    exact pins.2 bm
  · simp only [if_pos am,if_neg bm]
    have lo := all_cut_lower host W
    have hq := host.large
    omega
  · simp only [if_neg am,if_pos bm,sub_zero,mul_one]
    exact low_pair_pays_band host S T hs ht extrema ha hb lowA lowB zeroA zeroB W am bm
  · simp only [if_neg am,if_neg bm,sub_self,mul_zero]
    exact pins.1 am

/-- No selected cuts or endpoints are inputs: two distinct negatives suffice. -/
theorem q0_multi_negative_unit_cuts
    (multiple : ∃ X Y : Finset V, g q G A B X < 0 ∧ g q G A B Y < 0 ∧ X ≠ Y) :
    ∃ S T : Finset V, g q G A B S < 0 ∧ g q G A B T < 0 ∧ S ≠ T ∧
      (∀ N : Finset V, g q G A B N < 0 → S ⊆ N ∧ N ⊆ T) ∧
      26 ≤ #(T \ S) ∧
      ∃ a ∈ A ∩ S, ∃ b ∈ B \ T, ∀ W : Finset V,
        (q : ℤ)*((if b ∈ W then 1 else 0)-(if a ∈ W then 1 else 0)) ≤
          g q G A B W := by
  obtain ⟨S,T,hs,ht,_,_,extrema⟩ := negative_extrema host
  have hne : S ≠ T := by
    intro eq
    obtain ⟨X,Y,hX,hY,hXY⟩ := multiple
    have ex := extrema X hX
    have ey := extrema Y hY
    rw [← eq] at ex ey
    have eX : S = X := Subset.antisymm ex.1 ex.2
    have eY : S = Y := Subset.antisymm ey.1 ey.2
    exact hXY (eX.symm.trans eY)
  have hst := (extrema T ht).1
  have hi : (T \ S).Nonempty := sdiff_nonempty.mpr (by
    intro h; exact hne (Subset.antisymm hst h))
  exact ⟨S,T,hs,ht,hne,extrema,difference_order_26 host T S ht hs hi,
    strict_chain_unit_cuts host S T hs ht hne extrema⟩

#check @strict_chain_unit_cuts
#check @q0_multi_negative_unit_cuts
#print axioms difference_order_26
#print axioms extreme_low_pair
#print axioms cross_localization
#print axioms zero_pin
#print axioms mirrored_zero_pin
#print axioms low_pair_pays_band
#print axioms strict_chain_unit_cuts
#print axioms q0_multi_negative_unit_cuts
end Erdos585.Omit1ChainBranchR703

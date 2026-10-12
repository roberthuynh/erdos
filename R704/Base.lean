import R691.Main
import R699.Main
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

/-- Literal uniqueness on every original vertex support. -/
structure UniqueCut (q : ℕ) (G : SimpleGraph V) (A B M : Finset V) : Prop where
  negative : g q G A B M = -1
  others : ∀ S : Finset V, S ≠ M → 0 ≤ g q G A B S

omit [Fintype V] in
lemma g_submodular (S T : Finset V) :
    g q G A B (S ∪ T) + g q G A B (S ∩ T) ≤
      g q G A B S + g q G A B T := by
  have e := QB4.ec_add_ec_le (G := G) (A∩S) (A∩T) (B∩S) (B∩T)
  have cA := card_union_add_card_inter (A∩S) (A∩T)
  have cB := card_union_add_card_inter (B∩S) (B∩T)
  have sA := sum_union_inter (s₁ := A∩S) (s₂ := A∩T) (f := fun v => (dg G B v : ℤ))
  have iS := ec_sdiff_add_right (G := G) (inter_subset_left : B∩S ⊆ B) (A∩S)
  have iT := ec_sdiff_add_right (G := G) (inter_subset_left : B∩T ⊆ B) (A∩T)
  have iU := ec_sdiff_add_right (G := G) (inter_subset_left : B∩(S∪T) ⊆ B) (A∩(S∪T))
  have iI := ec_sdiff_add_right (G := G) (inter_subset_left : B∩(S∩T) ⊆ B) (A∩(S∩T))
  have dS : B \ (B∩S) = B\S := by ext v; simp
  have dT : B \ (B∩T) = B\T := by ext v; simp
  have dU : B \ (B∩(S∪T)) = B\(S∪T) := by ext v; simp
  have dI : B \ (B∩(S∩T)) = B\(S∩T) := by ext v; simp
  rw [dS] at iS
  rw [dT] at iT
  rw [dU] at iU
  rw [dI] at iI
  have aI : (A∩S)∩(A∩T) = A∩(S∩T) := by ext v; simp only [mem_inter]; tauto
  have bI : (B∩S)∩(B∩T) = B∩(S∩T) := by ext v; simp only [mem_inter]; tauto
  rw [← inter_union_distrib_left, ← inter_union_distrib_left, aI, bI] at e
  rw [← inter_union_distrib_left, aI] at cA sA
  rw [← inter_union_distrib_left, bI] at cB
  have sA' : (ec G (A∩(S∪T)) B : ℤ) + ec G (A∩(S∩T)) B =
    (ec G (A∩S) B : ℤ) + ec G (A∩T) B := by simpa only [ec, Nat.cast_sum] using sA
  zify at e cA cB iS iT iU iI
  unfold g k
  nlinarith only [e,cA,cB,sA',iS,iT,iU,iI]

omit [Fintype V] in
lemma nonnegative_avoiding (unique : UniqueCut q G A B M) {a : V}
    (ha : a ∈ M) (havoid : a ∉ S) : 0 ≤ g q G A B S := by
  apply unique.others
  intro he
  subst S
  exact havoid ha

omit [Fintype V] in
/-- No floor is used on the possibly empty intersection. -/
theorem zero_union (unique : UniqueCut q G A B M) {a : V}
    (ha : a ∈ M) (hS : a ∉ S) (hT : a ∉ T)
    (zS : g q G A B S = 0) (zT : g q G A B T = 0) :
    g q G A B (S∪T) = 0 ∧ g q G A B (S∩T) = 0 := by
  have nU := nonnegative_avoiding unique ha (show a ∉ S∪T by simp [hS,hT])
  have nI := nonnegative_avoiding unique ha (show a ∉ S∩T by simp [hS])
  have sm := g_submodular (q := q) (G := G) (A := A) (B := B) S T
  omega

variable (host : Omit1PrefixR691.Host q L G A B)
include host
lemma zero_imbalance (zP : g q G A B P = 0) (hl : 3 ≤ #P)
    (hp : #P < Fintype.card V) : k A B P = 1 ∨ k A B P = 2 := by
  have hq := host.large
  have hb := counting host P (by omega)
  have sc := scar_bounds host P
  have ff := floor host P hl hp
  have id := cut_identity (q := q) (G := G) (A := A) (B := B) P
  have cp := cap_potential host P
  have hk : k A B P ≤ 2 := by
    by_contra! hn
    have hm := mul_nonneg (show (0 : ℤ) ≤ (q : ℤ)-2 by omega)
      (show 0 ≤ k A B P-3 by omega)
    have hL := host.loss
    nlinarith only [hm,cp,id,zP,sc.2.1,hL.2]
  omega

/-- The corrected classification retains the F+2 possibility explicitly. -/
theorem zero_potential_classification (zP : g q G A B P = 0)
    (hl : 3 ≤ #P) (hp : #P < Fintype.card V) :
    (k A B P = 1 ∧ sA q G A B P = 3*(q : ℤ)-31+L ∧
      f q G A B P = 3*(q : ℤ)-30+L) ∨
    (k A B P = 2 ∧ sA q G A B P = 3*(q : ℤ)-32+L ∧
      f q G A B P = 3*(q : ℤ)-30+L) ∨
    (k A B P = 2 ∧ sA q G A B P = 3*(q : ℤ)-31+L ∧
      f q G A B P = 3*(q : ℤ)-29+L) := by
  have hk := zero_imbalance host zP hl hp
  have sc := scar_bounds host P
  have ff := floor host P hl hp
  have id := cut_identity (q := q) (G := G) (A := A) (B := B) P
  omega

lemma sB_subcut_zero (hP : P ⊆ M) (hm : sB q G A B M = 0) :
    sB q G A B P = 0 := by
  have hn := (scar_bounds host P).2.2.1
  have hs : B∩P ⊆ B∩M := inter_subset_inter_left hP
  have hd := deficiency_le_subset (G := G) (2*(q : ℤ)-2) hs
    (fun v hv => capB host (inter_subset_left hv))
  change sB q G A B P ≤ sB q G A B M at hd
  omega

/-- Actual boundary cancellation; f(P) is never replaced by F+1. -/
theorem zero_outer_boundary_identity (hP : P ⊆ M)
    (zm : sB q G A B M = 0) (tm : f q G A B M = 3*(q : ℤ)-30+L)
    (zP : g q G A B P = 0) :
    (ec G P (univ\M) : ℤ) = k A B P + 3*(q : ℤ)-30+L - f q G A B (M\P) := by
  have sb := sB_subcut_zero host hP zm
  have fp := f_disjoint host (disjoint_sdiff_self_right : Disjoint P (M\P))
  rw [union_sdiff_of_subset hP] at fp
  have bi := boundary_identity host P
  have ci := cut_identity (q := q) (G := G) (A := A) (B := B) P
  have e1 := ec_sdiff_add_right (G := G) hP P
  have e2 := ec_sdiff_add_right (G := G) (subset_univ M) P
  have e3 := ec_sdiff_add_right (G := G) (subset_univ P) P
  zify at e1 e2 e3
  omega

/-- The guarded two-edge bound, valid also for potential F+2. -/
theorem zero_outer_boundary_bound (hP : P ⊆ M)
    (zm : sB q G A B M = 0) (tm : f q G A B M = 3*(q : ℤ)-30+L)
    (zP : g q G A B P = 0) (hl : 3 ≤ #P) (hp : #P < Fintype.card V)
    (hc : 3 ≤ #(M\P)) (hpc : #(M\P) < Fintype.card V) :
    (ec G P (univ\M) : ℤ) ≤ k A B P ∧ (ec G P (univ\M) : ℤ) ≤ 2 := by
  have id := zero_outer_boundary_identity host hP zm tm zP
  have fl := floor host (M\P) hc hpc
  have hk := zero_imbalance host zP hl hp
  omega

omit host [Fintype V] in
lemma g_erase_A {a : V} (ha : a ∈ A∩S) (hn : a ∉ B) :
    g q G A B (S.erase a) = g q G A B S + (q : ℤ) - dg G (B\S) a := by
  have ax : A∩(S.erase a) = (A∩S).erase a := by ext v; simp [and_left_comm]
  have bx : B∩(S.erase a) = B∩S := by
    ext v
    simp only [mem_inter, mem_erase]
    constructor
    · tauto
    · rintro ⟨hb,hs⟩; exact ⟨hb,ne_of_mem_of_not_mem hb hn,hs⟩
  have by' : B\(S.erase a) = B\S := by
    ext v
    simp only [mem_sdiff, mem_erase]
    constructor
    · rintro ⟨hb,hs⟩; exact ⟨hb,fun hv => hs ⟨ne_of_mem_of_not_mem hb hn,hv⟩⟩
    · tauto
  have ee : ec G ((A∩S).erase a) (B\S) + dg G (B\S) a = ec G (A∩S) (B\S) :=
    sum_erase_add _ _ ha
  have cc := card_erase_add_one ha
  unfold g k
  rw [ax,bx,by']
  zify at ee cc
  nlinarith

omit host [Fintype V] in
lemma g_erase_B {b : V} (hb : b ∈ B∩S) (hn : b ∉ A) :
    g q G A B (S.erase b) = g q G A B S - (q : ℤ) + dg G (A∩S) b := by
  have ax : A∩(S.erase b) = A∩S := by
    ext v
    simp only [mem_inter, mem_erase]
    constructor
    · tauto
    · rintro ⟨ha,hs⟩; exact ⟨ha,ne_of_mem_of_not_mem ha hn,hs⟩
  have bx : B∩(S.erase b) = (B∩S).erase b := by ext v; simp [and_left_comm]
  have by' : B\(S.erase b) = insert b (B\S) := by
    ext v
    have hbB := (mem_inter.mp hb).1
    have hbS := (mem_inter.mp hb).2
    simp only [mem_sdiff,mem_erase,mem_insert]
    by_cases he : v=b
    · subst v; simp [hbB]
    · simp [he]
  have nb : b ∉ B\S := by simp [(mem_inter.mp hb).2]
  have ee : ec G (A∩S) (insert b (B\S)) = ec G (A∩S) {b} + ec G (A∩S) (B\S) := by
    rw [← singleton_union, ec_union_right (disjoint_singleton_left.mpr nb)]
  have sing : ec G (A∩S) {b} = dg G (A∩S) b := by rw [ec_comm]; simp [ec]
  rw [sing] at ee
  have cc := card_erase_add_one hb
  unfold g k
  rw [ax,bx,by']
  zify at ee cc
  nlinarith

omit host [Fintype V] in
/-- Finite union closure includes the empty family, whose union is empty. -/
theorem zero_biUnion (unique : UniqueCut q G A B M) {a : V}
    (ha : a ∈ M) (family : Finset (Finset V))
    (hf : ∀ P ∈ family, a ∉ P ∧ g q G A B P = 0) :
    a ∉ family.biUnion id ∧ g q G A B (family.biUnion id) = 0 := by
  induction family using Finset.induction_on with
  | empty => simp [g,k,ec,dg]
  | @insert P family hn ih =>
    have hp := hf P (mem_insert_self _ _)
    have hi := ih (fun T ht => hf T (mem_insert_of_mem ht))
    rw [biUnion_insert]
    exact ⟨by simp [hp.1,hi.1], (zero_union unique ha hp.1 hi.1 hp.2 hi.2).1⟩

/-- Saturated original T vertices have large internal degree, using the actual reverse count. -/
lemma internal_T (d : Omit1Q0CutChainR699.CutData q G A B M) {t : V} (ht : t ∈ B∩M) :
    q+26 ≤ dg G (A∩M) t := by
  have hd := dg_sdiff_add (G := G) (inter_subset_left : A∩M ⊆ A) t
  have ax : A\(A∩M) = A\M := by ext v; simp
  rw [ax, dg_eq_degree host.bipartite.symm (mem_inter.mp ht).1, d.saturated_B t ht] at hd
  have he := Omit1Q0CutChainR699.dg_le_ec (G := G) (Y := A\M) ht
  rw [ec_comm (G := G) (B∩M) (A\M)] at he
  have hr := d.reverse
  have hq := host.large
  omega

/-- Every tiny complement is rejected before a floor is used on that complement. -/
theorem zero_complement_order (d : Omit1Q0CutChainR699.CutData q G A B M)
    {a : V} (ha : a ∈ A∩M) (da : dg G (B\M) a = 0)
    (hP : P ⊆ M) (avoid : a ∉ P) (zP : g q G A B P = 0)
    (hl : 3 ≤ #P) : 3 ≤ #(M\P) := by
  let C := M\P
  have ac : a ∈ C := mem_sdiff.mpr ⟨(mem_inter.mp ha).2,avoid⟩
  have ca := card_sdiff_add_card_eq_card (show A∩P ⊆ A∩M from inter_subset_inter_left hP)
  have cb := card_sdiff_add_card_eq_card (show B∩P ⊆ B∩M from inter_subset_inter_left hP)
  have ea : (A∩M)\(A∩P) = A∩C := by ext v; simp only [C,mem_sdiff,mem_inter]; tauto
  have eb : (B∩M)\(B∩P) = B∩C := by ext v; simp only [C,mem_sdiff,mem_inter]; tauto
  rw [ea] at ca
  rw [eb] at cb
  have cp := support_card host C
  have km := d.imbalance
  have kp := zero_imbalance host zP hl ((card_le_card hP).trans_lt d.proper)
  have pa := card_pos.mpr (show (A∩C).Nonempty from ⟨a,mem_inter.mpr ⟨(mem_inter.mp ha).1,ac⟩⟩)
  change 3 ≤ #C
  by_contra! hc
  have kc : k A B C = 0 ∨ k A B C = 1 := by unfold k at *; omega
  have nac : #(A∩C) = 1 := by unfold k at kc; omega
  have ae : A∩C = {a} := by
    exact (eq_of_subset_of_card_le (singleton_subset_iff.mpr (mem_inter.mpr ⟨(mem_inter.mp ha).1,ac⟩)) (by simp [nac])).symm
  have nbc : #(B∩C) ≤ 1 := by omega
  have hnB : a ∉ B := fun hh => Finset.disjoint_left.mp host.disjoint (mem_inter.mp ha).1 hh
  rcases (show #(B∩C)=0 ∨ #(B∩C)=1 by omega) with hz | hz
  · have be : B∩C=∅ := card_eq_zero.mp hz
    have ce : C={a} := by rw [← support_partition host C,ae,be,union_empty]
    have pe : P=M.erase a := by
      have sub := Finset.sdiff_sdiff_eq_self hP
      change M\C=P at sub
      rw [ce,sdiff_singleton_eq_erase] at sub
      exact sub.symm
    have ge := g_erase_A (q := q) (G := G) ha hnB
    rw [← pe,zP,d.value,da] at ge
    have hq := host.large
    omega
  · obtain ⟨t,te⟩ := card_eq_one.mp hz
    have ht : t ∈ B∩M := by
      have hh : t ∈ B∩C := by rw [te]; simp
      exact mem_inter.mpr ⟨(mem_inter.mp hh).1,(mem_sdiff.mp (mem_inter.mp hh).2).1⟩
    have ce : C={a,t} := by rw [← support_partition host C,ae,te]; rfl
    have nat : a ≠ t := fun he => hnB (he ▸ (mem_inter.mp ht).1)
    have pe : P=(M.erase a).erase t := by
      have sub := Finset.sdiff_sdiff_eq_self hP
      change M\C=P at sub
      rw [ce] at sub
      ext v
      have hsub := Finset.ext_iff.mp sub v
      simp only [mem_erase,mem_sdiff,mem_insert,mem_singleton] at hsub ⊢
      tauto
    have ga := g_erase_A (q := q) (G := G) ha hnB
    have hnA : t ∉ A := fun hh => Finset.disjoint_left.mp host.disjoint hh (mem_inter.mp ht).1
    have ht' : t ∈ B∩(M.erase a) := mem_inter.mpr ⟨(mem_inter.mp ht).1,mem_erase.mpr ⟨nat.symm,(mem_inter.mp ht).2⟩⟩
    have gt := g_erase_B (q := q) (G := G) ht' hnA
    have ax : A∩(M.erase a) = (A∩M).erase a := by ext v; simp [and_left_comm]
    rw [ax,← pe,zP,ga,d.value,da] at gt
    have lower := internal_T host d ht
    have diff := Omit1Q0CutChainR699.dg_difference_bound (G := G) (A∩M) ((A∩M).erase a) t
    have dd : (A∩M)\((A∩M).erase a) = {a} := by
      ext v
      simp only [mem_sdiff,mem_erase,mem_singleton,mem_inter]
      have am := ha
      simp only [mem_inter] at am
      constructor
      · tauto
      · rintro rfl; exact ⟨am,by tauto⟩
    rw [dd,card_singleton] at diff
    have hq := host.large
    omega

omit host in
/-- All original zero supports of guarded order avoiding the actual vertex. -/
def zeroFamily (q : ℕ) (G : SimpleGraph V) (A B M : Finset V) (a : V) : Finset (Finset V) :=
  univ.filter (fun P => P ⊆ M ∧ a ∉ P ∧ g q G A B P = 0 ∧ 3 ≤ #P)

omit host in
lemma mem_zeroFamily {a : V} : P ∈ zeroFamily q G A B M a ↔
    P ⊆ M ∧ a ∉ P ∧ g q G A B P = 0 ∧ 3 ≤ #P := by simp [zeroFamily]

omit host in
/-- Empty unions are zero; the order guard is asserted only for a nonempty family. -/
theorem zeroFamily_union (unique : UniqueCut q G A B M) {a : V} (ha : a ∈ M) :
    let U := (zeroFamily q G A B M a).biUnion id
    U ⊆ M ∧ a ∉ U ∧ g q G A B U = 0 ∧
      ((zeroFamily q G A B M a).Nonempty → 3 ≤ #U) := by
  let family := zeroFamily q G A B M a
  have hz := zero_biUnion unique ha family (fun P hP =>
    ⟨(mem_zeroFamily.mp hP).2.1,(mem_zeroFamily.mp hP).2.2.1⟩)
  refine ⟨?_,hz.1,hz.2,?_⟩
  · intro v hv
    obtain ⟨P,hP,hvP⟩ := mem_biUnion.mp hv
    exact (mem_zeroFamily.mp hP).1 hvP
  · intro hn
    obtain ⟨P,hP⟩ := hn
    have hs : P ⊆ family.biUnion id := subset_biUnion_of_mem id hP
    exact (mem_zeroFamily.mp hP).2.2.2.trans (card_le_card hs)

omit host [Fintype V] in
/-- Distinct original heads consume distinct original unit incidences. -/
lemma head_card_le_boundary {U H O : Finset V} (hH : H ⊆ O)
    (positive : ∀ b ∈ H, 0 < dg G U b) : #H ≤ ec G U O := by
  have hh : #H ≤ ec G H U := by
    calc
      #H = ∑ _b ∈ H, 1 := by simp
      _ ≤ ∑ b ∈ H, dg G U b := sum_le_sum (fun b hb => positive b hb)
  have hm := ec_mono_left (G := G) hH U
  rw [ec_comm (G := G) O U] at hm
  exact hh.trans hm

omit host in
/-- Actual original neighbor hazard, with no supplied successful head. -/
def Hazardous (q : ℕ) (G : SimpleGraph V) (A B M : Finset V) (a b : V) : Prop :=
  ∃ P : Finset V, P ⊆ M ∧ a ∉ P ∧ g q G A B P = 0 ∧ 3 ≤ #P ∧ 0 < dg G P b

omit host in
/-- Case B hazard bound, with empty and nonempty zero families separated. -/
theorem hazardous_card_le_two (host0 : Omit1PrefixR691.Host q 0 G A B)
    (unique : UniqueCut q G A B M) (d : Omit1Q0CutChainR699.CutData q G A B M)
    {a : V} (ha : a ∈ A∩M) (da : dg G (B\M) a = 0)
    (heads : Finset V) (hheads : heads ⊆ B\M) :
    #(heads.filter (Hazardous q G A B M a)) ≤ 2 := by
  let family := zeroFamily q G A B M a
  let U := family.biUnion id
  let H := heads.filter (Hazardous q G A B M a)
  by_cases hn : family.Nonempty
  · have zu := zeroFamily_union unique (mem_inter.mp ha).2
    change U ⊆ M ∧ a ∉ U ∧ g q G A B U = 0 ∧ (family.Nonempty → 3 ≤ #U) at zu
    have hu3 := zu.2.2.2 hn
    have hc3 := zero_complement_order host0 d ha da zu.1 zu.2.1 zu.2.2.1 hu3
    have hp := (card_le_card zu.1).trans_lt d.proper
    have hpc := (card_le_card (sdiff_subset : M\U ⊆ M)).trans_lt d.proper
    have bound := zero_outer_boundary_bound host0 zu.1 d.scar_B (by simpa using d.tight)
      zu.2.2.1 hu3 hp hc3 hpc
    have ho : H ⊆ univ\M := by
      intro b hb
      have hh := hheads (mem_filter.mp hb).1
      exact mem_sdiff.mpr ⟨mem_univ b,(mem_sdiff.mp hh).2⟩
    have positive : ∀ b ∈ H, 0 < dg G U b := by
      intro b hb
      obtain ⟨P,hPM,hPa,hPz,hP3,hPb⟩ := (mem_filter.mp hb).2
      have hPf : P ∈ family := mem_zeroFamily.mpr ⟨hPM,hPa,hPz,hP3⟩
      exact hPb.trans_le (dg_mono (G := G) (subset_biUnion_of_mem id hPf) b)
    have count := head_card_le_boundary ho positive
    change #H ≤ 2
    omega
  · have he : family=∅ := not_nonempty_iff_eq_empty.mp hn
    have hH : H=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro b hb
      obtain ⟨P,hPM,hPa,hPz,hP3,_⟩ := (mem_filter.mp hb).2
      have hPf : P ∈ family := mem_zeroFamily.mpr ⟨hPM,hPa,hPz,hP3⟩
      rw [he] at hPf
      simp at hPf
    change #H ≤ 2
    simp [hH]

omit host in
/-- The head is derived from the original cardinal bound, not supplied as a premise. -/
theorem exists_nonhazardous_head (host0 : Omit1PrefixR691.Host q 0 G A B)
    (unique : UniqueCut q G A B M) (d : Omit1Q0CutChainR699.CutData q G A B M)
    {a : V} (ha : a ∈ A∩M) (da : dg G (B\M) a = 0)
    (heads : Finset V) (hheads : heads ⊆ B\M) (many : 3 ≤ #heads) :
    ∃ b ∈ heads, ¬ Hazardous q G A B M a b := by
  have count := hazardous_card_le_two host0 unique d ha da heads hheads
  by_contra! hn
  have he : heads.filter (Hazardous q G A B M a) = heads := filter_eq_self.mpr hn
  rw [he] at count
  omega

#print axioms g_submodular
#print axioms zero_union
#print axioms zero_potential_classification
#print axioms zero_outer_boundary_identity
#print axioms zero_outer_boundary_bound
#print axioms zero_complement_order
#print axioms zeroFamily_union
#print axioms hazardous_card_le_two
#print axioms exists_nonhazardous_head
end Erdos585.Omit1UniqueR704

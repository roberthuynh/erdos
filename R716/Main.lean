import R704.Base
import R704.Tiny
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.Omit1KillersR716
open QB4 B5 L34 H3Unequal Omit1PrefixR691 Omit1UniqueR704
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V} {q : ℕ}
  {A B M S T P H : Finset V}

omit [Fintype V] in
lemma sA_disjoint (hd : Disjoint S T) :
    sA q G A B S + sA q G A B T = sA q G A B (S∪T) := by
  unfold sA deficiency
  rw [inter_union_distrib_left, sum_union (hd.mono inter_subset_right inter_subset_right)]
omit [Fintype V] in
lemma k_disjoint (hd : Disjoint S T) :
    k A B S + k A B T = k A B (S∪T) := by
  unfold k
  rw [inter_union_distrib_left, inter_union_distrib_left,
    card_union_of_disjoint (hd.mono inter_subset_right inter_subset_right),
    card_union_of_disjoint (hd.mono inter_subset_right inter_subset_right)]
  push_cast
  ring
lemma g_disjoint (host : Omit1PrefixR691.Host q 0 G A B) (hd : Disjoint S T) :
    g q G A B S + g q G A B T = g q G A B (S∪T) + (ec G S T : ℤ) := by
  have f := f_disjoint host hd
  have a := sA_disjoint (q := q) (G := G) (A := A) (B := B) hd
  have k := k_disjoint (A := A) (B := B) hd
  rw [cut_identity,cut_identity,cut_identity]
  omega

/-- The exact original crossing tax, not a scalar stand-in. -/
theorem four_cell_tax (host : Omit1PrefixR691.Host q 0 G A B) :
    g q G A B S = g q G A B (M∩S) + g q G A B (M∪S) -
      g q G A B M + (ec G (M\S) (S\M) : ℤ) := by
  have up : (M∩S)∪(M\S)=M := by ext x; simp only [mem_union,mem_inter,mem_sdiff]; tauto
  have uh : (M∩S)∪(S\M)=S := by ext x; simp only [mem_union,mem_inter,mem_sdiff]; tauto
  have mh : M∪(S\M)=M∪S := by ext x; simp only [mem_union,mem_sdiff]; tauto
  have du : Disjoint (M∩S) (M\S) := by apply Finset.disjoint_left.mpr; intro x hx hy; simp only [mem_inter,mem_sdiff] at hx hy; tauto
  have dh : Disjoint (M∩S) (S\M) := by apply Finset.disjoint_left.mpr; intro x hx hy; simp only [mem_inter,mem_sdiff] at hx hy; tauto
  have dm : Disjoint M (S\M) := disjoint_sdiff_self_right
  have gu := g_disjoint host du
  have gs := g_disjoint host dh
  have gm := g_disjoint host dm
  have ee := ec_union_left (G := G) du (S\M)
  rw [up] at gu ee
  rw [uh] at gs
  rw [mh] at gm
  zify at ee
  omega

lemma sA_outside_zero (host : Omit1PrefixR691.Host q 0 G A B)
    (d : Omit1Q0CutChainR699.CutData q G A B M) (hs : S ⊆ univ\M) :
    sA q G A B S=0 := by
  unfold sA deficiency
  apply sum_eq_zero
  intro v hv
  have hm : v ∈ A\M := mem_sdiff.mpr ⟨(mem_inter.mp hv).1,(mem_sdiff.mp (hs (mem_inter.mp hv).2)).2⟩
  rw [dg_eq_degree host.bipartite (mem_sdiff.mp hm).1,d.saturated_A v hm]
  have hq := host.large
  omega

lemma sB_inside_zero (host : Omit1PrefixR691.Host q 0 G A B)
    (d : Omit1Q0CutChainR699.CutData q G A B M) (hs : S ⊆ M) :
    sB q G A B S=0 := by
  unfold sB deficiency
  apply sum_eq_zero
  intro v hv
  have hm : v ∈ B∩M := mem_inter.mpr ⟨(mem_inter.mp hv).1,hs (mem_inter.mp hv).2⟩
  rw [dg_eq_degree host.bipartite.symm (mem_inter.mp hm).1,d.saturated_B v hm]
  have hq := host.large
  omega

/-- The R694 actual four-cell potential identity, with both bypass orientations. -/
theorem four_cell_potential (host : Omit1PrefixR691.Host q 0 G A B)
    (d : Omit1Q0CutChainR699.CutData q G A B M) :
    g q G A B S = f q G A B (M\S)+f q G A B (S\M) -
      (3*(q : ℤ)-31)-k A B S-1 +
      (ec G (M∩S) (univ\(M∪S)) : ℤ) := by
  let U := M∩S
  let P := M\S
  let H := S\M
  let Z := univ\(M∪S)
  have du : Disjoint U P := by apply Finset.disjoint_left.mpr; intro x hx hy; simp only [U,P,mem_inter,mem_sdiff] at hx hy; tauto
  have dh : Disjoint U H := by apply Finset.disjoint_left.mpr; intro x hx hy; simp only [U,H,mem_inter,mem_sdiff] at hx hy; tauto
  have up : U∪P=M := by ext x; simp only [U,P,mem_union,mem_inter,mem_sdiff]; tauto
  have uh : U∪H=S := by ext x; simp only [U,H,mem_union,mem_inter,mem_sdiff]; tauto
  have hz : H∪Z=univ\M := by ext x; simp only [H,Z,mem_union,mem_sdiff,mem_univ]; tauto
  have dz : Disjoint H Z := by apply Finset.disjoint_left.mpr; intro x hx hy; simp only [H,Z,mem_sdiff,mem_univ,mem_union] at hx hy; tauto
  have fp := f_disjoint host du
  have fh := f_disjoint host dh
  rw [up,d.tight] at fp
  rw [uh] at fh
  have sp := sA_disjoint (q := q) (G := G) (A := A) (B := B) du
  have sh := sA_disjoint (q := q) (G := G) (A := A) (B := B) dh
  rw [up,d.captured] at sp
  rw [uh,sA_outside_zero host d (show H ⊆ univ\M by intro x hx; simp [H] at hx; simp [hx.2])] at sh
  have bp := boundary_identity host P
  rw [sB_inside_zero host d (show P ⊆ M from sdiff_subset)] at bp
  have bm := complementary host M
  rw [d.tight,d.tight_complement] at bm
  have pm : univ\P=U∪(univ\M) := by ext x; simp only [U,P,mem_union,mem_inter,mem_sdiff,mem_univ]; tauto
  have dum : Disjoint U (univ\M) := disjoint_sdiff_self_right.mono inter_subset_left (Subset.refl _)
  have ep := ec_union_right (G := G) dum P
  rw [← pm] at ep
  have em := ec_union_left (G := G) du (univ\M)
  rw [up] at em
  have eup := ec_union_right (G := G) dz U
  have epp := ec_union_right (G := G) dz P
  rw [hz] at eup epp
  rw [ec_comm (G := G) P U] at ep
  have gs := cut_identity (q := q) (G := G) (A := A) (B := B) S
  zify at ep em eup epp
  change g q G A B S = f q G A B P + f q G A B H - (3*(q : ℤ)-31)-k A B S-1+(ec G U Z : ℤ)
  omega

/-- Every dangerous original cut has a tiny cell containing an omitted vertex. -/
theorem dangerous_tiny (host : Omit1PrefixR691.Host q 0 G A B)
    (d : Omit1Q0CutChainR699.CutData q G A B M)
    (bad : g q G A B S < q) : #(M\S)≤2 ∨ #(S\M)≤2 := by
  by_contra! hn
  have band : g q G A B S ≤ (q : ℤ)-1 := by omega
  have ck := counting host S band
  have p3 : 3 ≤ #(M\S) := by omega
  have h3 : 3 ≤ #(S\M) := by omega
  have dis : Disjoint (M\S) (S\M) := by apply Finset.disjoint_left.mpr; intro x hx hy; simp only [mem_sdiff] at hx hy; tauto
  have fp := floor host (M\S) p3 (proper_of_disjoint dis h3)
  have fh := floor host (S\M) h3 (proper_of_disjoint dis.symm p3)
  have id := four_cell_potential host d (S := S)
  have ez : 0 ≤ (ec G (M∩S) (univ\(M∪S)) : ℤ) := Nat.cast_nonneg _
  have hq := host.large
  omega

lemma swap_host (host : Omit1Q0CutChainR699.Host q G A B) :
    Omit1Q0CutChainR699.Host q G B A := by
  have hs : Omit1PrefixR691.Host q 0 G B A := {
    large := host.large
    loss := host.loss
    disjoint := host.disjoint.symm
    cover := by simpa [union_comm] using host.cover
    balanced := host.balanced.symm
    bipartite := host.bipartite.symm
    cap := host.cap
    total := by simpa only [AllHTopCritical.coreDefect_symm] using host.total
    proper := host.proper }
  exact ⟨hs,host.min_degree,host.no_regular⟩

lemma g_swap (host : Omit1PrefixR691.Host q 0 G A B) (S : Finset V) :
    g q G B A (univ\S)=g q G A B S := by
  have ca := card_sdiff_add_card_eq_card (inter_subset_left : A∩S ⊆ A)
  have cb := card_sdiff_add_card_eq_card (inter_subset_left : B∩S ⊆ B)
  have ax : A\(A∩S)=A\S := by ext v; simp
  have bx : B\(B∩S)=B\S := by ext v; simp
  rw [ax] at ca
  rw [bx] at cb
  have ae : A\(univ\S)=A∩S := by ext v; simp
  have be : B∩(univ\S)=B\S := by ext v; simp
  have aa : A∩(univ\S)=A\S := by ext v; simp
  have bal := host.balanced
  unfold g k
  rw [ae,be,aa,ec_comm (G := G) (B\S) (A∩S)]
  zify at ca cb bal
  nlinarith

lemma forward_cap_A (host : Omit1Q0CutChainR699.Host q G A B)
    (d : Omit1Q0CutChainR699.CutData q G A B M) {a : V} (ha : a∈A∩M) :
    dg G (B\M) a ≤ q-1 := by
  have hi := Omit1Q0CutChainR699.diagonal_degree_A host M (by rw [d.value]; omega) ha
  have hc := host.capA a (mem_inter.mp ha).1
  have hs := dg_sdiff_add (G := G) (inter_subset_left : B∩M ⊆ B) a
  have be : B\(B∩M)=B\M := by ext v; simp
  rw [be] at hs
  have hq := host.large
  omega

/-- Direct singleton/pair incidence table; no tiny-set floor is used. -/
theorem tiny_alpha (host : Omit1Q0CutChainR699.Host q G A B)
    (d : Omit1Q0CutChainR699.CutData q G A B M)
    {a : V} (ha : a∈A∩M) (hp : P⊆M) (ap : a∈P) (tiny : #P≤2)
    (da : dg G (B\M) a ≤ 1) :
    (q : ℤ)-dg G (B\M) a ≤ g q G A B (M\P)+1 ∧
    (P≠{a} → (q : ℤ) ≤ g q G A B (M\P)+1) := by
  have anB : a∉B := fun hb => Finset.disjoint_left.mp host.disjoint (mem_inter.mp ha).1 hb
  have ga := g_erase_A (q := q) (G := G) ha anB
  have hq := host.large
  by_cases pe : P={a}
  · rw [pe,sdiff_singleton_eq_erase,ga,d.value]
    exact ⟨by omega,by simp⟩
  · have nonempty : (P.erase a).Nonempty := by
      by_contra hn
      have he := not_nonempty_iff_eq_empty.mp hn
      have pp := insert_erase ap
      rw [he] at pp
      exact pe pp.symm
    obtain ⟨x,hx⟩ := nonempty
    have xp := (mem_erase.mp hx).2
    have xa := (mem_erase.mp hx).1
    have px : P={a,x} := by
      apply (eq_of_subset_of_card_le (show {a,x}⊆P by intro v hv; simp only [mem_insert,mem_singleton] at hv; rcases hv with rfl|rfl <;> assumption) _).symm
      simp [Ne.symm xa]
      exact tiny
    have xM := hp xp
    have sd : M\P=(M.erase a).erase x := by
      ext v
      simp only [px,mem_sdiff,mem_insert,mem_singleton,mem_erase]
      tauto
    have ax : A∩(M.erase a)=(A∩M).erase a := by ext v; simp [and_left_comm]
    have bx : B\(M.erase a)=B\M := by
      ext v
      simp only [mem_sdiff,mem_erase]
      constructor
      · rintro ⟨hb,hn⟩
        exact ⟨hb,fun hm => hn ⟨ne_of_mem_of_not_mem hb anB,hm⟩⟩
      · tauto
    have cover : x∈A ∨ x∈B := by
      have hh : x∈A∪B := by rw [host.cover]; exact mem_univ x
      exact mem_union.mp hh
    rcases cover with xA | xB
    · have xnB : x∉B := fun hb => Finset.disjoint_left.mp host.disjoint xA hb
      have gx := g_erase_A (q := q) (G := G)
        (mem_inter.mpr ⟨xA,mem_erase.mpr ⟨xa,xM⟩⟩) xnB
      have cap := forward_cap_A host d (mem_inter.mpr ⟨xA,xM⟩)
      rw [bx,ga,d.value] at gx
      rw [sd,gx]
      exact ⟨by omega,by intro _; omega⟩
    · have xnA : x∉A := fun hh => Finset.disjoint_left.mp host.disjoint hh xB
      have gx := g_erase_B (q := q) (G := G)
        (mem_inter.mpr ⟨xB,mem_erase.mpr ⟨xa,xM⟩⟩) xnA
      have lower := internal_T host.toHost d (mem_inter.mpr ⟨xB,xM⟩)
      have diff := Omit1Q0CutChainR699.dg_difference_bound (G := G) (A∩M) ((A∩M).erase a) x
      have ee : (A∩M)\((A∩M).erase a)={a} := by
        ext v
        simp only [mem_sdiff,mem_inter,mem_erase,mem_singleton]
        have aa := mem_inter.mp ha
        constructor
        · tauto
        · rintro rfl; tauto
      rw [ee,card_singleton] at diff
      rw [ax,ga,d.value] at gx
      rw [sd,gx]
      exact ⟨by omega,by intro _; omega⟩

/-- The mirrored tiny table is obtained by the actual shore/complement involution. -/
theorem tiny_beta (host : Omit1Q0CutChainR699.Host q G A B)
    (d : Omit1Q0CutChainR699.CutData q G A B M)
    {b : V} (hb : b∈B\M) (hp : H⊆univ\M) (bp : b∈H) (tiny : #H≤2)
    (db : dg G (A∩M) b ≤ 1) :
    (q : ℤ)-dg G (A∩M) b ≤ g q G A B (M∪H)+1 ∧
    (H≠{b} → (q : ℤ) ≤ g q G A B (M∪H)+1) := by
  have sw := swap_host host
  have gs := g_swap host.toHost M
  have ds := Omit1Q0CutChainR699.all_negative sw (univ\M) (by rw [gs,d.value]; omega)
  have bh : b∈B∩(univ\M) := by simpa using hb
  have am : A\(univ\M)=A∩M := by ext v; simp
  have comp : (univ\M)\H=univ\(M∪H) := by ext v; simp only [mem_sdiff,mem_univ,mem_union]; tauto
  have ta := tiny_alpha sw ds bh hp bp tiny (by simpa [am] using db)
  rw [am,comp,g_swap host.toHost] at ta
  exact ta

omit [Fintype V] in
lemma unique_lower (unique : UniqueCut q G A B M) (S : Finset V) :
    -1 ≤ g q G A B S := by
  by_cases he : S=M
  · rw [he,unique.negative]
  · have hn := unique.others S he; omega

omit [Fintype V] in
lemma cross_parameters (unique : UniqueCut q G A B M) {a b : V}
    (ha : a∈A∩M) (hb : b∈B\M) (avoid : a∉S) (inside : b∈S) :
    0 ≤ g q G A B (M∩S) ∧ 0 ≤ g q G A B (M∪S) := by
  constructor
  · apply unique.others
    intro he
    have aa : a∈M∩S := he.symm ▸ (mem_inter.mp ha).2
    exact avoid (mem_inter.mp aa).2
  · apply unique.others
    intro he
    have bb : b∈M∪S := mem_union.mpr (Or.inr inside)
    rw [he] at bb
    exact (mem_sdiff.mp hb).2 bb

/-- The only orientation that needs a q-sized payment is a outside, b inside. -/
theorem paid_of_cross (host : Omit1PrefixR691.Host q 0 G A B)
    (unique : UniqueCut q G A B M) {a b : V}
    (ha : a∈A∩M) (hb : b∈B\M)
    (pay : ∀ S : Finset V, a∉S → b∈S → (q : ℤ) ≤ g q G A B S) :
    ∀ S : Finset V,
      (q : ℤ)*((if b∈S then 1 else 0)-(if a∈S then 1 else 0)) ≤ g q G A B S := by
  intro S
  by_cases aa : a∈S <;> by_cases bb : b∈S
  · have hn := unique.others S (by intro he; rw [he] at bb; exact (mem_sdiff.mp hb).2 bb)
    simpa [aa,bb] using hn
  · have hn := unique_lower unique S
    have hq := host.large
    simp [aa,bb]
    omega
  · simpa [aa,bb] using pay S aa bb
  · have hn := unique.others S (by intro he; rw [he] at aa; exact aa (mem_inter.mp ha).2)
    simpa [aa,bb] using hn

/-- A zero-zero pair pays every original support. -/
theorem zero_zero_paid (host : Omit1Q0CutChainR699.Host q G A B)
    (d : Omit1Q0CutChainR699.CutData q G A B M) (unique : UniqueCut q G A B M)
    {a b : V} (ha : a∈A∩M) (hb : b∈B\M)
    (da : dg G (B\M) a=0) (db : dg G (A∩M) b=0) :
    ∀ S : Finset V,
      (q : ℤ)*((if b∈S then 1 else 0)-(if a∈S then 1 else 0)) ≤ g q G A B S := by
  apply paid_of_cross host.toHost unique ha hb
  intro S aa bb
  by_contra! bad
  have pars := cross_parameters unique ha hb aa bb
  have tax := four_cell_tax host.toHost (M := M) (S := S)
  rw [unique.negative] at tax
  have enn : 0 ≤ (ec G (M\S) (S\M) : ℤ) := Nat.cast_nonneg _
  rcases dangerous_tiny host.toHost d bad with pt | ht
  · have ap : a∈M\S := mem_sdiff.mpr ⟨(mem_inter.mp ha).2,aa⟩
    have al := (tiny_alpha host d ha sdiff_subset ap pt (by omega)).1
    have pe : M\(M\S)=M∩S := by ext v; simp only [mem_sdiff,mem_inter]; tauto
    rw [pe,da] at al
    omega
  · have bp : b∈S\M := mem_sdiff.mpr ⟨bb,(mem_sdiff.mp hb).2⟩
    have al := (tiny_beta host d hb (show S\M⊆univ\M by intro x hx; exact mem_sdiff.mpr ⟨mem_univ x,(mem_sdiff.mp hx).2⟩) bp ht (by omega)).1
    have pe : M∪(S\M)=M∪S := by ext v; simp only [mem_sdiff,mem_union]; tauto
    rw [pe,db] at al
    omega

/-- A literal original edge between two degree-one forward vertices pays all cuts. -/
theorem one_one_edge_paid (host : Omit1Q0CutChainR699.Host q G A B)
    (d : Omit1Q0CutChainR699.CutData q G A B M) (unique : UniqueCut q G A B M)
    {a b : V} (ha : a∈A∩M) (hb : b∈B\M) (ab : G.Adj a b)
    (da : dg G (B\M) a=1) (db : dg G (A∩M) b=1) :
    ∀ S : Finset V,
      (q : ℤ)*((if b∈S then 1 else 0)-(if a∈S then 1 else 0)) ≤ g q G A B S := by
  apply paid_of_cross host.toHost unique ha hb
  intro S aa bb
  by_contra! bad
  have pars := cross_parameters unique ha hb aa bb
  have tax := four_cell_tax host.toHost (M := M) (S := S)
  rw [unique.negative] at tax
  have enn : 0 ≤ (ec G (M\S) (S\M) : ℤ) := Nat.cast_nonneg _
  have ap : a∈M\S := mem_sdiff.mpr ⟨(mem_inter.mp ha).2,aa⟩
  have bp : b∈S\M := mem_sdiff.mpr ⟨bb,(mem_sdiff.mp hb).2⟩
  have ep : 1 ≤ ec G (M\S) (S\M) := by
    have hh : 1 ≤ dg G (S\M) a := by
      unfold dg
      exact card_pos.mpr ⟨b,mem_filter.mpr ⟨bp,ab⟩⟩
    exact hh.trans (Omit1Q0CutChainR699.dg_le_ec ap)
  rcases dangerous_tiny host.toHost d bad with pt | ht
  · have al := tiny_alpha host d ha sdiff_subset ap pt (by omega)
    have pe : M\(M\S)=M∩S := by ext v; simp only [mem_sdiff,mem_inter]; tauto
    rw [pe,da] at al
    by_cases sing : M\S={a}
    · have a1 := al.1
      omega
    · have a2 := al.2 sing
      omega
  · have al := tiny_beta host d hb (show S\M⊆univ\M by intro x hx; exact mem_sdiff.mpr ⟨mem_univ x,(mem_sdiff.mp hx).2⟩) bp ht (by omega)
    have pe : M∪(S\M)=M∪S := by ext v; simp only [mem_sdiff,mem_union]; tauto
    rw [pe,db] at al
    by_cases sing : S\M={b}
    · have a1 := al.1
      omega
    · have a2 := al.2 sing
      omega

lemma dg_other_shore (host : Omit1PrefixR691.Host q 0 G A B) {b : V}
    (hb : b∈B) (S : Finset V) : dg G S b=dg G (A∩S) b := by
  unfold dg
  congr 1
  ext x
  simp only [mem_filter,mem_inter]
  constructor
  · rintro ⟨hx,he⟩
    exact ⟨⟨host.bipartite.symm.mem_of_mem_adj hb he,hx⟩,he⟩
  · tauto

/-- Every bad cut for a zero/one pair is exactly a singleton-head zero-cut hazard.
The four cells and the neighbor degree are original graph data. -/
theorem zero_one_bad_data (host : Omit1Q0CutChainR699.Host q G A B)
    (d : Omit1Q0CutChainR699.CutData q G A B M) (unique : UniqueCut q G A B M)
    {a b : V} (ha : a∈A∩M) (hb : b∈B\M)
    (da : dg G (B\M) a=0) (db : dg G (A∩M) b=1)
    (aa : a∉S) (bb : b∈S) (bad : g q G A B S < q) :
    S\M={b} ∧ g q G A B (M∩S)=0 ∧ dg G (M∩S) b=1 := by
  have pars := cross_parameters unique ha hb aa bb
  have tax := four_cell_tax host.toHost (M := M) (S := S)
  rw [unique.negative] at tax
  have enn : 0 ≤ (ec G (M\S) (S\M) : ℤ) := Nat.cast_nonneg _
  have ap : a∈M\S := mem_sdiff.mpr ⟨(mem_inter.mp ha).2,aa⟩
  have bp : b∈S\M := mem_sdiff.mpr ⟨bb,(mem_sdiff.mp hb).2⟩
  have pe : M\(M\S)=M∩S := by ext v; simp only [mem_sdiff,mem_inter]; tauto
  have he : M∪(S\M)=M∪S := by ext v; simp only [mem_sdiff,mem_union]; tauto
  have ht : #(S\M)≤2 := by
    rcases dangerous_tiny host.toHost d bad with pt | ht
    · have al := (tiny_alpha host d ha sdiff_subset ap pt (by omega)).1
      rw [pe,da] at al
      omega
    · exact ht
  have be : S\M={b} := by
    by_contra hn
    have al := (tiny_beta host d hb (show S\M⊆univ\M by intro x hx; exact mem_sdiff.mpr ⟨mem_univ x,(mem_sdiff.mp hx).2⟩) bp ht (by omega)).2 hn
    rw [he] at al
    omega
  have bnA : b∉A := fun hh => Finset.disjoint_left.mp host.disjoint hh (mem_sdiff.mp hb).1
  have bim : b∈B∩(M∪{b}) := mem_inter.mpr ⟨(mem_sdiff.mp hb).1,by simp⟩
  have erase : (M∪{b}).erase b=M := by
    ext v
    by_cases ve : v=b
    · subst v; simp [(mem_sdiff.mp hb).2]
    · simp [ve]
  have ax : A∩(M∪{b})=A∩M := by
    ext v
    by_cases ve : v=b
    · subst v; simp [bnA]
    · simp [ve]
  have gb := g_erase_B (q := q) (G := G) bim bnA
  rw [erase,ax,unique.negative,db] at gb
  have mu : M∪S=M∪{b} := by rw [← he,be]
  rw [mu] at tax pars
  have gz : g q G A B (M∩S)=0 := by omega
  have ez : ec G (M\S) (S\M)=0 := by omega
  have dz : dg G (M\S) b=0 := by
    rw [be,ec_comm] at ez
    simpa [ec] using ez
  have dp : Disjoint (M∩S) (M\S) := by apply Finset.disjoint_left.mpr; intro x hx hy; simp only [mem_inter,mem_sdiff] at hx hy; tauto
  have up : (M∩S)∪(M\S)=M := by ext v; simp only [mem_inter,mem_sdiff,mem_union]; tauto
  have ds := dg_union_of_disjoint (G := G) dp b
  rw [up,dz,dg_other_shore host.toHost (mem_sdiff.mp hb).1 M,db] at ds
  exact ⟨be,gz,by omega⟩

/-- The hard zero/one selection pays every original cut. Tiny zero cuts are
excluded by the derived no-S1 alternative; larger zero cuts by the selected head. -/
theorem zero_one_nohazard_paid (host : Omit1Q0CutChainR699.Host q G A B)
    (d : Omit1Q0CutChainR699.CutData q G A B M) (unique : UniqueCut q G A B M)
    {a b : V} (ha : a∈A∩M) (hb : b∈B\M)
    (da : dg G (B\M) a=0) (db : dg G (A∩M) b=1)
    (nos1 : ∀ x∈A∩M, ∀ y∈B\M, G.Adj x y →
      ¬(dg G (B\M) x=1 ∧ dg G (A∩M) y=1))
    (safe : ¬Hazardous q G A B M a b) :
    ∀ S : Finset V,
      (q : ℤ)*((if b∈S then 1 else 0)-(if a∈S then 1 else 0)) ≤ g q G A B S := by
  apply paid_of_cross host.toHost unique ha hb
  intro S aa bb
  by_contra! bad
  obtain ⟨_,gz,du⟩ := zero_one_bad_data host d unique ha hb da db aa bb bad
  by_cases large : 3≤#(M∩S)
  · exact safe ⟨M∩S,inter_subset_left,by intro hh; exact aa (mem_inter.mp hh).2,gz,large,by omega⟩
  · have tiny : #(M∩S)≤2 := by omega
    have dne : ( (M∩S).filter (fun x => G.Adj b x)).Nonempty := by
      apply card_pos.mp
      change 0<dg G (M∩S) b
      omega
    obtain ⟨x,hx⟩ := dne
    obtain ⟨xm,adj⟩ := mem_filter.mp hx
    have xA : x∈A := host.bipartite.symm.mem_of_mem_adj (mem_sdiff.mp hb).1 adj
    have xu : x∈A∩(M∩S) := mem_inter.mpr ⟨xA,xm⟩
    have xM : x∈A∩M := mem_inter.mpr ⟨xA,(mem_inter.mp xm).1⟩
    have deg := tiny_zero_degree host gz tiny xu
    have internal := Omit1Q0CutChainR699.diagonal_degree_A host M (by rw [d.value]; omega) xM
    have split := dg_sdiff_add (G := G) (inter_subset_left : B∩M⊆B) x
    have be : B\(B∩M)=B\M := by ext v; simp
    rw [be,dg_eq_degree host.bipartite xA,deg] at split
    have pos : 0<dg G (B\M) x := by
      unfold dg
      exact card_pos.mpr ⟨b,mem_filter.mpr ⟨hb,adj.symm⟩⟩
    have phi : dg G (B\M) x=1 := by have hq := host.large; omega
    exact nos1 x xM b hb adj.symm ⟨phi,db⟩

#print axioms four_cell_tax
#print axioms four_cell_potential
#print axioms dangerous_tiny
#print axioms tiny_alpha
#print axioms tiny_beta
#print axioms zero_zero_paid
#print axioms one_one_edge_paid
#print axioms zero_one_bad_data
#print axioms zero_one_nohazard_paid
end Erdos585.Omit1KillersR716

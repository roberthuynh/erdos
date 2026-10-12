import R701.Main
import R744.Main
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.R753
open QB4 B5 L34 H3Unequal AllHTopCritical
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {q : ℕ} {A B : Finset V}
abbrev defect {W : Type u} (q : ℕ) (K : SimpleGraph W) (S : Finset W) : ℤ := H49Q0R701.defect q K S
lemma constant4 (host : Host 4 q G A B) :
    (constant 4 q : ℤ) = 4*(q:ℤ)-44 := by
  classical
  have hc := host.parameters.constant_cast
  norm_num [offset] at hc
  exact hc
lemma paired_defect (host : Host 4 q G A B) {P Q : Finset V}
    (hP : P ⊆ A) (hQ : Q ⊆ B) :
    defect q G (P∪Q) = coreDefect q G P Q := by
  classical
  unfold defect H49Q0R701.defect coreDefect
  rw [induced_edges_eq_ec host.disjoint host.bipartite hP hQ,
    card_union_of_disjoint (host.disjoint.mono hP hQ)]
  push_cast
  rfl
lemma whole_violation (host : Host 4 q G A B) :
    ∃ X ⊆ A, ∃ Y ⊆ B, (ec G X Y : ℤ) <
      (q : ℤ)*((#X : ℤ)+#Y-#B) := by
  classical
  by_contra! hn
  have hcuts : ∀ X ⊆ A, ∀ C ⊆ B,
      q*#X ≤ ec G X (B\C)+q*#C := by
    classical
    intro X hX C hC
    have hf := hn X hX (B\C) sdiff_subset
    have hc := card_sdiff_add_card_eq_card hC
    zify at hc ⊢
    nlinarith
  have hf : FactorOn q G A B :=
    B5Factor.exists_target_factor (k := q) A B host.balanced hcuts
  have hA : A.Nonempty := card_pos.mp (by
    have ho := host.shore_order
    have hb := host.balanced
    have hq := host.parameters.q_pos
    have he := host.order
    omega)
  obtain ⟨H, _, hne, hreg⟩ := factor_exact_subgraph host.parameters.q_pos hA host.disjoint hf
  exact host.no_regular ⟨H, hne, hreg⟩
lemma rectangle_lower {X Y : Finset V} (host : Host 4 q G A B) (hX : X ⊆ A) (hY : Y ⊆ B) :
    (q : ℤ) * #X ≤ (#X : ℤ) * #(B \ Y) + (ec G X Y : ℤ) := by
  classical
  have hm := Bq.ec_lower_of_min (G := G) hX host.minA
  have hs := ec_sdiff_add_right (G := G) hY X
  have hp := AllHTopCritical.ec_le_product (G := G) X (B \ Y)
  zify at hm hs hp
  nlinarith

lemma cut_seed (host : Host 4 q G A B) {X Y : Finset V}
    (hX : X ⊆ A) (hY : Y ⊆ B)
    (violation : (ec G X Y : ℤ) < (q:ℤ)*((#X:ℤ)+#Y-#B)) :
    ∃ P Q : Finset V, P⊆A ∧ Q⊆B ∧ 4≤#P+#Q ∧
      #P+#Q<Fintype.card V ∧ coreDefect q G P Q≤4*(q:ℤ)-42 := by
  classical
  let k : ℤ := (#X : ℤ) + #Y - #B
  let dA := deficiency (2 * (q : ℤ) - 2) G B (A \ X)
  let dB := deficiency (2 * (q : ℤ) - 2) G A (B \ Y)
  have hq : (25600 : ℤ) ≤ q := by
    classical
    have hp := host.parameters.large
    norm_num at hp
    exact_mod_cast hp
  have hc : (constant 4 q : ℤ) = 4 * (q : ℤ) - 44 := by
    classical
    have hh := host.parameters.constant_cast
    norm_num [offset] at hh
    exact hh
  have ca := card_sdiff_add_card_eq_card hX
  have cb := card_sdiff_add_card_eq_card hY
  have bal := host.balanced
  have ord := host.shore_order
  zify at ca cb bal ord
  have kX : (#X : ℤ) = #(B \ Y) + k := by dsimp [k]; omega
  have kY : (#Y : ℤ) = #(A \ X) + k := by dsimp [k]; omega
  have da0 : 0 ≤ dA := deficiency_nonneg _
    (fun v hv => host.capA_int v (sdiff_subset hv))
  have db0 : 0 ≤ dB := deficiency_nonneg _
    (fun v hv => host.capB_int v (sdiff_subset hv))
  have sx := ec_sdiff_add_right (G := G) hY X
  have sv := ec_sdiff_add_right (G := G) hY (A \ X)
  have sa := ec_sdiff_add_left (G := G) hX B
  have st := ec_sdiff_add_left (G := G) hX (B \ Y)
  have da := deficiency_eq (G := G) (2 * (q : ℤ) - 2) B (A \ X)
  have db := deficiency_eq (G := G) (2 * (q : ℤ) - 2) A (B \ Y)
  rw [ec_comm (G := G) (B \ Y) A] at db
  have whole := host.deficiency_A
  rw [deficiency_eq, hc] at whole
  zify at sx sv sa st
  change dA = _ at da
  change dB = _ at db
  have identity : 4 * (q : ℤ) - 44 =
      2 * ((q : ℤ) - 1) * k + (ec G (A \ X) (B \ Y) : ℤ) +
        dA + dB - (ec G X Y : ℤ) := by
    classical
    nlinarith
  have x0 : 0 ≤ (ec G X Y : ℤ) := Nat.cast_nonneg _
  have z0 : 0 ≤ (ec G (A \ X) (B \ Y) : ℤ) := Nat.cast_nonneg _
  change (ec G X Y : ℤ) < (q : ℤ) * k at violation
  have kp : 1 ≤ k := by
    classical
    by_contra! hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (show (0 : ℤ) ≤ q by omega)
      (show k ≤ 0 by omega)
    nlinarith only [hm, violation, x0]
  have kle : k ≤ 3 := by
    classical
    by_contra! hn
    have hm := mul_nonneg (show (0 : ℤ) ≤ (q : ℤ) - 2 by omega)
      (show 0 ≤ k - 4 by omega)
    nlinarith only [identity, violation, hm, da0, db0, z0, hq]
  have lowerX := rectangle_lower host hX hY
  have lowerY : (q : ℤ) * #Y ≤ (#Y : ℤ) * #(A \ X) + (ec G X Y : ℤ) := by
    classical
    have hm := Bq.ec_lower_of_min (G := G) hY host.minB
    have hs := ec_sdiff_add_right (G := G) hX Y
    have hp := AllHTopCritical.ec_le_product (G := G) Y (A \ X)
    rw [ec_comm (G := G) Y X] at hs
    zify at hm hs hp
    nlinarith
  have Xlarge : (q : ℤ) + 1 ≤ #X := by
    classical
    by_contra! hn
    have hm := mul_nonneg (show (0 : ℤ) ≤ (#X : ℤ) - k by omega)
      (show 0 ≤ (q : ℤ) - #X by omega)
    nlinarith only [lowerX, kX, violation, hm]
  have Ylarge : (q : ℤ) + 1 ≤ #Y := by
    classical
    by_contra! hn
    have hm := mul_nonneg (show (0 : ℤ) ≤ (#Y : ℤ) - k by omega)
      (show 0 ≤ (q : ℤ) - #Y by omega)
    nlinarith only [lowerY, kY, violation, hm]
  have eligible1 : 4 ≤ #X + #(B \ Y) := by omega
  have proper1 : #X + #(B \ Y) < Fintype.card V := by omega
  have diagonal1 : coreDefect q G X (B \ Y) =
      ((q : ℤ) - 1) * k + (ec G (A \ X) (B \ Y) : ℤ) + dB := by
    classical
    unfold coreDefect
    nlinarith only [kX, db, st]
  refine ⟨X,B\Y,hX,sdiff_subset,eligible1,proper1,?_⟩
  rw [diagonal1]
  nlinarith only [identity,violation,da0,kle]

def Piece (_q : ℕ) (_G : SimpleGraph V) (A B P Q : Finset V) : Prop :=
  P⊆A ∧ Q⊆B ∧ 4≤#P+#Q ∧ #P+#Q<Fintype.card V

lemma paired_floor (host : Host 4 q G A B) {P Q : Finset V}
    (piece : Piece q G A B P Q) : 4*(q:ℤ)-43 ≤ coreDefect q G P Q := by
  classical
  have hd := host.disjoint.mono piece.1 piece.2.1
  have hc := card_union_of_disjoint hd
  have hf := host.extended_floor (W:=P∪Q) (by have h:=piece.2.2.2; omega)
    (Subset.refl _) (by have h:=piece.2.2.1; omega)
  rw [constant4 host] at hf
  change _ ≤ defect q G (P∪Q) at hf
  rw [paired_defect host piece.1 piece.2.1] at hf
  omega

lemma minimum_exists (host : Host 4 q G A B) :
    ∃ P Q : Finset V, Piece q G A B P Q ∧ coreDefect q G P Q≤4*(q:ℤ)-42 ∧
      (∀ P' Q', Piece q G A B P' Q' → coreDefect q G P Q≤coreDefect q G P' Q') ∧
      (∀ P' Q', Piece q G A B P' Q' → coreDefect q G P' Q'=coreDefect q G P Q →
        #P+#Q≤#P'+#Q') := by
  classical
  obtain ⟨X,hX,Y,hY,hv⟩ := whole_violation host
  obtain ⟨P,Q,hP,hQ,hl,hp,hf⟩ := cut_seed host hX hY hv
  let candidates : Finset (Finset V × Finset V) :=
    (univ ×ˢ univ).filter fun t => Piece q G A B t.1 t.2
  have hn : candidates.Nonempty := ⟨(P,Q),by
    simp only [candidates,mem_filter,mem_product,mem_univ,true_and]
    exact ⟨hP,hQ,hl,hp⟩⟩
  obtain ⟨t,ht,hmin⟩ := candidates.exists_min_image
    (fun t => coreDefect q G t.1 t.2) hn
  let equal := candidates.filter fun z => coreDefect q G z.1 z.2=coreDefect q G t.1 t.2
  have he : equal.Nonempty := ⟨t,by simp [equal,ht]⟩
  obtain ⟨z,hz,horder⟩ := equal.exists_min_image (fun z => #z.1+#z.2) he
  have hz' := mem_filter.mp hz
  have zeq := hz'.2
  refine ⟨z.1,z.2,(mem_filter.mp hz'.1).2,?_,?_,?_⟩
  · rw [zeq]
    exact (hmin (P,Q) (by
    simp only [candidates,mem_filter,mem_product,mem_univ,true_and]
    exact ⟨hP,hQ,hl,hp⟩)).trans hf
  · intro P' Q' hh
    rw [zeq]
    exact hmin (P',Q') (by simp [candidates,hh])
  · intro P' Q' hh heq
    exact horder (P',Q') (by simp [equal,candidates,hh,heq,zeq])

lemma piece_order (host : Host 4 q G A B) {P Q : Finset V}
    (piece : Piece q G A B P Q) (hf : coreDefect q G P Q≤4*(q:ℤ)-42) :
    2*q≤#P+#Q := by
  classical
  have hp := AllHTopCritical.ec_le_product (G:=G) P Q
  have hq : 25600≤q := host.parameters.large
  by_contra! hn
  have hlo : (4:ℤ)≤(#P:ℤ)+#Q := by have h:=piece.2.2.1; omega
  have hhi : (#P:ℤ)+#Q≤2*(q:ℤ)-1 := by omega
  have sq := sq_nonneg ((#P:ℤ)-#Q)
  have poly := mul_nonneg (show 0≤(#P:ℤ)+#Q-4 by omega)
    (show 0≤2*(q:ℤ)-1-(#P+#Q) by omega)
  unfold coreDefect at hf
  zify at hp
  nlinarith
omit [Fintype V] in
lemma erase_defect {P Q : Finset V} {v : V} (hv : v ∈ P) :
    coreDefect q G (P.erase v) Q = coreDefect q G P Q - ((q : ℤ)-1) + dg G Q v := by
  classical
  have h := potential_erase_left (G := G) (2*(q : ℤ)-2) hv Q
  have h1 := twice_coreDefect (G := G) q P Q
  have h2 := twice_coreDefect (G := G) q (P.erase v) Q
  linarith

lemma minimum_minA (host : Host 4 q G A B) {P Q : Finset V}
    (piece : Piece q G A B P Q) (hf : coreDefect q G P Q≤4*(q:ℤ)-42)
    (hmin : ∀ P' Q', Piece q G A B P' Q' → coreDefect q G P Q≤coreDefect q G P' Q')
    (horder : ∀ P' Q', Piece q G A B P' Q' → coreDefect q G P' Q'=coreDefect q G P Q →
      #P+#Q≤#P'+#Q') : ∀ v∈P,q≤dg G Q v := by
  classical
  intro v hv
  have ho := piece_order host piece hf
  have hc := card_erase_add_one hv
  have hq : 25600≤q := host.parameters.large
  have lesser : Piece q G A B (P.erase v) Q :=
    ⟨(erase_subset v P).trans piece.1,piece.2.1,by omega,
      by have hh:=piece.2.2.2; omega⟩
  have he := erase_defect (q:=q) (G:=G) (Q:=Q) hv
  have hm := hmin (P.erase v) Q lesser
  by_contra! hn
  have eq : coreDefect q G (P.erase v) Q=coreDefect q G P Q := by omega
  have hh := horder (P.erase v) Q lesser eq
  omega

lemma split_support (host : Host 4 q G A B) (S : Finset V) :
    (S∩A)∪(S∩B)=S := by
  classical
  rw [← inter_union_distrib_left,host.cover,inter_univ]

lemma minimum_strict_floor (host : Host 4 q G A B) {P Q : Finset V}
    (piece : Piece q G A B P Q)
    (hmin : ∀ P' Q', Piece q G A B P' Q' → coreDefect q G P Q≤coreDefect q G P' Q')
    (horder : ∀ P' Q', Piece q G A B P' Q' → coreDefect q G P' Q'=coreDefect q G P Q →
      #P+#Q≤#P'+#Q') :
    ∀ S⊆P∪Q,4≤#S → #S<#(P∪Q) → coreDefect q G P Q+1≤defect q G S := by
  classical
  intro S hS hl hp
  have hd := host.disjoint.mono piece.1 piece.2.1
  have hc := card_union_of_disjoint hd
  have hsplit := split_support host S
  have hdis := host.disjoint.mono (inter_subset_right : S∩A⊆A) (inter_subset_right : S∩B⊆B)
  have hcard := card_union_of_disjoint hdis
  rw [hsplit] at hcard
  have hdef := paired_defect host (inter_subset_right : S∩A⊆A) (inter_subset_right : S∩B⊆B)
  rw [hsplit] at hdef
  have p : Piece q G A B (S∩A) (S∩B) :=
    ⟨inter_subset_right,inter_subset_right,by omega,by have hh:=piece.2.2.2; omega⟩
  have hm := hmin (S∩A) (S∩B) p
  by_contra! hn
  have eq : coreDefect q G (S∩A) (S∩B)=coreDefect q G P Q := by omega
  have hh := horder (S∩A) (S∩B) p eq
  omega

lemma swap_piece {P Q : Finset V} (piece : Piece q G A B P Q) : Piece q G B A Q P :=
  ⟨piece.2.1,piece.1,by have h:=piece.2.2.1; omega,by have h:=piece.2.2.2; omega⟩

lemma minimum_minB (host : Host 4 q G A B) {P Q : Finset V}
    (piece : Piece q G A B P Q) (hf : coreDefect q G P Q≤4*(q:ℤ)-42)
    (hmin : ∀ P' Q', Piece q G A B P' Q' → coreDefect q G P Q≤coreDefect q G P' Q')
    (horder : ∀ P' Q', Piece q G A B P' Q' → coreDefect q G P' Q'=coreDefect q G P Q →
      #P+#Q≤#P'+#Q') : ∀ v∈Q,q≤dg G P v := by
  classical
  apply minimum_minA host.swap (swap_piece piece)
  · rw [coreDefect_symm]; exact hf
  · intro Q' P' hh
    rw [coreDefect_symm,coreDefect_symm (G:=G) Q' P']
    exact hmin P' Q' (swap_piece hh)
  · intro Q' P' hh he
    rw [coreDefect_symm (G:=G) Q' P',coreDefect_symm (G:=G) Q P] at he
    have hm := horder P' Q' (swap_piece hh) he
    omega

lemma piece_imbalance (host : Host 4 q G A B) {P Q : Finset V}
    (hf : coreDefect q G P Q≤4*(q:ℤ)-42) : #Q≤#P+3 ∧ #P≤#Q+3 := by
  classical
  have hlarge : 25600≤q := host.parameters.large
  have ca := deficiency_nonneg (G:=G) (W:=Q) (X:=P) (2*(q:ℤ)-2)
    (fun v _ => show (dg G Q v:ℤ)≤2*q-2 by
      have h := (dg_le_ambient (G:=G) Q v).trans (host.cap_degree v); omega)
  have cb := deficiency_nonneg (G:=G) (W:=P) (X:=Q) (2*(q:ℤ)-2)
    (fun v _ => show (dg G P v:ℤ)≤2*q-2 by
      have h := (dg_le_ambient (G:=G) P v).trans (host.cap_degree v); omega)
  rw [deficiency_eq] at ca cb
  rw [ec_comm (G:=G) Q P] at cb
  unfold coreDefect at hf
  constructor
  · by_contra! hn
    have hm := mul_nonneg (show 0≤(q:ℤ)-1 by omega)
      (show 0≤(#Q:ℤ)-#P-4 by omega)
    nlinarith
  · by_contra! hn
    have hm := mul_nonneg (show 0≤(q:ℤ)-1 by omega)
      (show 0≤(#P:ℤ)-#Q-4 by omega)
    nlinarith

/-- Only actual original-host facts are supplied; every factor is internally selected. -/
lemma surplus_factor (q a j : ℕ) {W : Type u} [Fintype W]
    (K : SimpleGraph W) (L R : Finset W) (large : 25600≤q)
    (offset : a=42 ∨ a=43) (branch : j=1 ∨ j=2 ∨ j=3)
    (disjoint : Disjoint L R) (cover : L∪R=univ)
    (bipartite : K.IsBipartiteWith (L:Set W) (R:Set W))
    (card : #R=#L+j) (order : 2*q≤Fintype.card W)
    (minimum : ∀ v:W,q≤K.degree v) (cap : ∀ v:W,K.degree v≤2*q-2)
    (edges : (K.edgeSet.ncard:ℤ)=((q:ℤ)-1)*Fintype.card W-(4*(q:ℤ)-a))
    (proper : ∀ X:Finset W,4≤#X → #X<Fintype.card W →
      4*(q:ℤ)-a≤defect q K X) :
    ∃ H:K.Subgraph,H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  classical
  rcases branch with rfl | rfl | rfl
  · obtain ⟨P,Q,_,_,_,_,H,_,hne,hreg,_⟩ :=
      R744.original_factor q a K L R large offset disjoint cover bipartite card order
        minimum cap edges proper
    exact ⟨H,hne,hreg⟩
  · have p : AllHNextNonstrict.Parameters 4 q a 2 :=
      ⟨by decide,by norm_num; exact large,by rcases offset with rfl|rfl <;> decide,
        by rcases offset with rfl|rfl <;> decide,rfl⟩
    have hedge : K.edgeSet.ncard+AllHNextNonstrict.constant 4 q a=
        (q-1)*Fintype.card W := by
      classical
      have hc : (AllHNextNonstrict.constant 4 q a:ℤ)=4*(q:ℤ)-a := by
        classical
        unfold AllHNextNonstrict.constant
        rcases offset with rfl|rfl <;> omega
      have hqm : ((q-1:ℕ):ℤ)=(q:ℤ)-1 := by omega
      zify
      rw [hc,hqm]
      linarith
    have host : AllHNextNonstrict.Host 4 q a 2 K L R :=
      ⟨p,disjoint,cover,bipartite,card,order,minimum,cap,hedge,by
        intro X hl hp
        have hc : (AllHNextNonstrict.constant 4 q a:ℤ)=4*(q:ℤ)-a := by
          classical
          unfold AllHNextNonstrict.constant
          rcases offset with rfl|rfl <;> omega
        rw [hc]
        exact proper X hl hp⟩
    obtain ⟨O,_,_,_,H,_,hne,hreg⟩ := AllHNextNonstrict.allh_next_nonstrict 4 q a 2 K L R host
    exact ⟨H,hne,hreg⟩
  · have p : AllHLargestNonstrict.Parameters 4 q a 3 :=
      ⟨by decide,by norm_num; exact large,by rcases offset with rfl|rfl <;> decide,
        by rcases offset with rfl|rfl <;> decide,rfl⟩
    have hedge : K.edgeSet.ncard+AllHLargestNonstrict.constant 4 q a=
        (q-1)*Fintype.card W := by
      classical
      have hc : (AllHLargestNonstrict.constant 4 q a:ℤ)=4*(q:ℤ)-a := by
        classical
        unfold AllHLargestNonstrict.constant
        rcases offset with rfl|rfl <;> omega
      have hqm : ((q-1:ℕ):ℤ)=(q:ℤ)-1 := by omega
      zify
      rw [hc,hqm]
      linarith
    have host : AllHLargestNonstrict.Host 4 q a 3 K L R :=
      ⟨p,disjoint,cover,bipartite,card,order,minimum,cap,hedge,by
        intro X hl hp
        have hc : (AllHLargestNonstrict.constant 4 q a:ℤ)=4*(q:ℤ)-a := by
          classical
          unfold AllHLargestNonstrict.constant
          rcases offset with rfl|rfl <;> omega
        rw [hc]
        exact proper X hl hp⟩
    obtain ⟨O,_,_,_,H,_,hne,hreg⟩ := AllHLargestNonstrict.allh_largest_nonstrict 4 q a 3 K L R host
    exact ⟨H,hne,hreg⟩
variable {P Q : Finset V}
def shore (P Q R : Finset V) : Finset (↑(P∪Q) : Set V) :=
  univ.filter fun v => v.val ∈ R
omit [Fintype V] in
lemma mem_shore (R : Finset V) (v : (↑(P∪Q) : Set V)) :
    v ∈ shore P Q R ↔ v.val ∈ R := by simp [shore]
omit [Fintype V] in
lemma shore_image (R : Finset V) (hR : R ⊆ P∪Q) :
    (shore P Q R).image Subtype.val = R := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
    exact (mem_shore R w).mp hw
  · intro hv
    exact mem_image.mpr ⟨⟨v,hR hv⟩,(mem_shore R ⟨v,hR hv⟩).mpr hv,rfl⟩
omit [Fintype V] in
lemma shore_card (R : Finset V) (hR : R ⊆ P∪Q) : #(shore P Q R) = #R := by
  classical
  calc
    #(shore P Q R) = #((shore P Q R).image Subtype.val) :=
      (card_image_of_injective _ Subtype.val_injective).symm
    _ = #R := congrArg Finset.card (shore_image R hR)


lemma exclude_unequal (host : Host 4 q G A B) {P Q : Finset V} {j : ℕ}
    (piece : Piece q G A B P Q) (hf : coreDefect q G P Q≤4*(q:ℤ)-42)
    (hmin : ∀ P' Q', Piece q G A B P' Q' → coreDefect q G P Q≤coreDefect q G P' Q')
    (horder : ∀ P' Q', Piece q G A B P' Q' → coreDefect q G P' Q'=coreDefect q G P Q →
      #P+#Q≤#P'+#Q') (branch : j=1 ∨ j=2 ∨ j=3) (card : #Q=#P+j) : False := by
  classical
  let K := G.induce (↑(P∪Q):Set V)
  let PP := shore P Q P
  let QQ := shore P Q Q
  have hp : PP.image Subtype.val=P := shore_image P subset_union_left
  have hq : QQ.image Subtype.val=Q := shore_image Q subset_union_right
  have cp : #PP=#P := shore_card P subset_union_left
  have cq : #QQ=#Q := shore_card Q subset_union_right
  have hd0 := host.disjoint.mono piece.1 piece.2.1
  have hd : Disjoint PP QQ := by
    classical
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact Finset.disjoint_left.mp hd0 ((mem_shore P v).mp hv) ((mem_shore Q v).mp hw)
  have hc : PP∪QQ=univ := by
    classical
    ext v
    have hv := v.property
    simp only [mem_union,mem_univ,iff_true]
    exact (mem_union.mp hv).elim
      (fun h => Or.inl ((mem_shore P v).mpr h))
      (fun h => Or.inr ((mem_shore Q v).mpr h))
  have hb : K.IsBipartiteWith (PP:Set (↑(P∪Q):Set V)) (QQ:Set (↑(P∪Q):Set V)) := by
    classical
    constructor
    · exact Set.disjoint_left.mpr (fun v hv hw => Finset.disjoint_left.mp hd hv hw)
    · intro v w hadj
      have hv := v.property
      have hw := w.property
      rcases host.bipartite.mem_of_adj (show G.Adj v.val w.val from hadj) with h|h
      · have vp : v.val∈P := (mem_union.mp hv).resolve_right
          (fun ht => Set.disjoint_left.mp host.bipartite.disjoint h.1 (piece.2.1 ht))
        have wq : w.val∈Q := (mem_union.mp hw).resolve_left
          (fun ht => Set.disjoint_left.mp host.bipartite.disjoint (piece.1 ht) h.2)
        exact Or.inl ⟨(mem_shore P v).mpr vp,(mem_shore Q w).mpr wq⟩
      · have vq : v.val∈Q := (mem_union.mp hv).resolve_left
          (fun ht => Set.disjoint_left.mp host.bipartite.disjoint (piece.1 ht) h.1)
        have wp : w.val∈P := (mem_union.mp hw).resolve_right
          (fun ht => Set.disjoint_left.mp host.bipartite.disjoint h.2 (piece.2.1 ht))
        exact Or.inr ⟨(mem_shore Q v).mpr vq,(mem_shore P w).mpr wp⟩
  have he : ec K PP QQ=ec G P Q := by
    classical
    have hh := NEQAssembly.ec_embedding_image K G
      (SimpleGraph.Embedding.induce (G:=G) (↑(P∪Q):Set V)) PP QQ
    change ec G (PP.image Subtype.val) (QQ.image Subtype.val)=_ at hh
    rw [hp,hq] at hh
    exact hh.symm
  have csize : Fintype.card (↑(P∪Q):Set V)=#P+#Q := by
    classical
    exact (Fintype.card_of_finset' (P∪Q) (fun _ => Iff.rfl)).trans (card_union_of_disjoint hd0)
  have minimum : ∀ v:(↑(P∪Q):Set V),q≤K.degree v := by
    classical
    intro v
    rw [NEQAssembly.induced_degree_eq_dg]
    rcases mem_union.mp v.property with hv|hv
    · rw [host.dg_union_left piece.1 piece.2.1 (piece.1 hv)]
      exact minimum_minA host piece hf hmin horder v.val hv
    · rw [host.dg_union_right piece.1 piece.2.1 (piece.2.1 hv)]
      exact minimum_minB host piece hf hmin horder v.val hv
  have cap : ∀ v:(↑(P∪Q):Set V),K.degree v≤2*q-2 := by
    classical
    intro v
    rw [NEQAssembly.induced_degree_eq_dg]
    exact (dg_le_ambient (G:=G) (P∪Q) v.val).trans (host.cap_degree v.val)
  obtain ⟨a,ha,hfa⟩ : ∃ a:ℕ,(a=42 ∨ a=43) ∧ coreDefect q G P Q=4*(q:ℤ)-a := by
    classical
    have hl := paired_floor host piece
    by_cases he : coreDefect q G P Q=4*(q:ℤ)-42
    · exact ⟨42,Or.inl rfl,he⟩
    · exact ⟨43,Or.inr rfl,by omega⟩
  have edges : (K.edgeSet.ncard:ℤ)=((q:ℤ)-1)*Fintype.card (↑(P∪Q):Set V)-(4*(q:ℤ)-a) := by
    classical
    rw [← ec_eq_ncard hb,he,csize]
    unfold coreDefect at hfa
    push_cast
    linarith
  have proper : ∀ T:Finset (↑(P∪Q):Set V),4≤#T → #T<Fintype.card (↑(P∪Q):Set V) →
      4*(q:ℤ)-a≤defect q K T := by
    classical
    intro T hl ht
    have cs : Fintype.card (↑(P∪Q):Set V)=#(P∪Q) := Fintype.card_of_finset' (P∪Q) (fun _ => Iff.rfl)
    rw [cs] at ht
    change _≤H49Q0R701.defect q (G.induce (↑(P∪Q):Set V)) T
    rw [H49Q0R701.induced_defect]
    have hh := minimum_strict_floor host piece hmin horder (T.image Subtype.val)
      (by intro v hv; obtain ⟨w,_,rfl⟩:=mem_image.mp hv; exact w.property)
      (by simpa only [card_image_of_injective _ Subtype.val_injective] using hl)
      (by simpa only [card_image_of_injective _ Subtype.val_injective,Fintype.card_coe] using ht)
    change _≤H49Q0R701.defect q G (T.image Subtype.val) at hh
    rw [hfa] at hh
    linarith
  have factor := surplus_factor q a j K PP QQ host.parameters.large ha branch hd (by simpa only [Finset.ext_iff,Finset.mem_union] using hc) hb
    (by omega) (by rw [csize]; exact piece_order host piece hf) minimum cap edges proper
  exact host.no_regular (NEQAssembly.original_induced_regular_transport G (P∪Q) factor)

lemma minimum_balanced (host : Host 4 q G A B) {P Q : Finset V}
    (piece : Piece q G A B P Q) (hf : coreDefect q G P Q≤4*(q:ℤ)-42)
    (hmin : ∀ P' Q', Piece q G A B P' Q' → coreDefect q G P Q≤coreDefect q G P' Q')
    (horder : ∀ P' Q', Piece q G A B P' Q' → coreDefect q G P' Q'=coreDefect q G P Q →
      #P+#Q≤#P'+#Q') : #P=#Q := by
  classical
  have hi := piece_imbalance host hf
  by_contra hn
  by_cases hlt : #P<#Q
  · have cases : #Q=#P+1 ∨ #Q=#P+2 ∨ #Q=#P+3 := by omega
    rcases cases with h1|h2|h3
    · exact exclude_unequal host piece hf hmin horder (Or.inl rfl) h1
    · exact exclude_unequal host piece hf hmin horder (Or.inr (Or.inl rfl)) h2
    · exact exclude_unequal host piece hf hmin horder (Or.inr (Or.inr rfl)) h3
  · have sf : coreDefect q G Q P≤4*(q:ℤ)-42 := by rw [coreDefect_symm]; exact hf
    have sm : ∀ Q' P',Piece q G B A Q' P' → coreDefect q G Q P≤coreDefect q G Q' P' := by
      classical
      intro Q' P' hh
      rw [coreDefect_symm,coreDefect_symm (G:=G) Q' P']
      exact hmin P' Q' (swap_piece hh)
    have so : ∀ Q' P',Piece q G B A Q' P' → coreDefect q G Q' P'=coreDefect q G Q P →
        #Q+#P≤#Q'+#P' := by
      classical
      intro Q' P' hh he
      rw [coreDefect_symm (G:=G) Q' P',coreDefect_symm (G:=G) Q P] at he
      have hm := horder P' Q' (swap_piece hh) he
      omega
    have cases : #P=#Q+1 ∨ #P=#Q+2 ∨ #P=#Q+3 := by omega
    rcases cases with h1|h2|h3
    · exact exclude_unequal host.swap (swap_piece piece) sf sm so (Or.inl rfl) h1
    · exact exclude_unequal host.swap (swap_piece piece) sf sm so (Or.inr (Or.inl rfl)) h2
    · exact exclude_unequal host.swap (swap_piece piece) sf sm so (Or.inr (Or.inr rfl)) h3


/-- Actual original balanced core at one of two adjacent deficits. -/
structure TwoOffsetCore (q : ℕ) (G : SimpleGraph V) (A B P Q : Finset V) : Prop where
  left_subset : P⊆A
  right_subset : Q⊆B
  disjoint : Disjoint P Q
  balanced : #P=#Q
  shore_order : q≤#P
  nonempty : (P∪Q).Nonempty
  order : 2*q≤#(P∪Q)
  proper : #(P∪Q)<Fintype.card V
  exact_defect : defect q G (P∪Q)=4*(q:ℤ)-43 ∨ defect q G (P∪Q)=4*(q:ℤ)-42
  minimum : ∀ v:(↑(P∪Q):Set V),q≤(G.induce (↑(P∪Q):Set V)).degree v
  cap : ∀ v:(↑(P∪Q):Set V),(G.induce (↑(P∪Q):Set V)).degree v≤2*q-2
  strict_floor : ∀ T⊆P∪Q,4≤#T → #T<#(P∪Q) → defect q G (P∪Q)+1≤defect q G T
  global_minimum : ∀ T:Finset V,4≤#T → #T<Fintype.card V → defect q G (P∪Q)≤defect q G T
  minimum_order : ∀ T:Finset V,4≤#T → #T<Fintype.card V →
    defect q G T=defect q G (P∪Q) → #(P∪Q)≤#T
  no_regular : Noq q (G.induce (↑(P∪Q):Set V))
  original_adjacency : ∀ v w:(↑(P∪Q):Set V),
    (G.induce (↑(P∪Q):Set V)).Adj v w ↔ G.Adj v.val w.val

/-- Literal Host4 constructs its own cut, global minimum, balance, and every internal strict floor. -/
theorem construct_two_offset_core (host : Host 4 q G A B) :
    ∃ P Q:Finset V,TwoOffsetCore q G A B P Q := by
  classical
  obtain ⟨P,Q,piece,hf,hmin,horder⟩ := minimum_exists host
  have hd := host.disjoint.mono piece.1 piece.2.1
  have hc := card_union_of_disjoint hd
  have ho := piece_order host piece hf
  have hb := minimum_balanced host piece hf hmin horder
  have hq : 25600≤q := host.parameters.large
  have hminU : ∀ v∈P∪Q,q≤dg G (P∪Q) v := by
    classical
    intro v hv
    rcases mem_union.mp hv with hv|hv
    · rw [host.dg_union_left piece.1 piece.2.1 (piece.1 hv)]
      exact minimum_minA host piece hf hmin horder v hv
    · rw [host.dg_union_right piece.1 piece.2.1 (piece.2.1 hv)]
      exact minimum_minB host piece hf hmin horder v hv
  refine ⟨P,Q,piece.1,piece.2.1,hd,hb,by omega,?_,by omega,
    by have hp:=piece.2.2.2; omega,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact card_pos.mp (by omega)
  · rw [paired_defect host piece.1 piece.2.1]
    have hl := paired_floor host piece
    omega
  · intro v
    rw [NEQAssembly.induced_degree_eq_dg]
    exact hminU v.val v.property
  · intro v
    rw [NEQAssembly.induced_degree_eq_dg]
    exact (dg_le_ambient (G:=G) (P∪Q) v.val).trans (host.cap_degree v.val)
  · rw [paired_defect host piece.1 piece.2.1]
    exact minimum_strict_floor host piece hmin horder
  · intro T hl hp
    have hs := split_support host T
    have ht := card_union_of_disjoint
      (host.disjoint.mono (inter_subset_right: T∩A⊆A) (inter_subset_right:T∩B⊆B))
    rw [hs] at ht
    have tp : Piece q G A B (T∩A) (T∩B) :=
      ⟨inter_subset_right,inter_subset_right,by omega,by omega⟩
    have hm := hmin (T∩A) (T∩B) tp
    rw [paired_defect host piece.1 piece.2.1]
    have hh := paired_defect host (inter_subset_right:T∩A⊆A) (inter_subset_right:T∩B⊆B)
    rw [hs] at hh
    rw [hh]
    exact hm
  · intro T hl hp he
    have hs := split_support host T
    have ht := card_union_of_disjoint
      (host.disjoint.mono (inter_subset_right:T∩A⊆A) (inter_subset_right:T∩B⊆B))
    rw [hs] at ht
    have tp : Piece q G A B (T∩A) (T∩B) :=
      ⟨inter_subset_right,inter_subset_right,by omega,by omega⟩
    have hh := paired_defect host (inter_subset_right:T∩A⊆A) (inter_subset_right:T∩B⊆B)
    rw [hs] at hh
    rw [hh,paired_defect host piece.1 piece.2.1] at he
    have hm := horder (T∩A) (T∩B) tp he
    omega
  · intro h
    exact host.no_regular (NEQAssembly.original_induced_regular_transport G (P∪Q) h)
  · intro v w
    rfl

lemma TwoOffsetCore.induced_strict_floor {P Q:Finset V}
    (core : TwoOffsetCore q G A B P Q) :
    ∀ T:Finset (↑(P∪Q):Set V),4≤#T → #T<Fintype.card (↑(P∪Q):Set V) →
      defect q G (P∪Q)+1≤defect q (G.induce (↑(P∪Q):Set V)) T := by
  classical
  intro T hl hp
  have cs : Fintype.card (↑(P∪Q):Set V)=#(P∪Q) := Fintype.card_of_finset' (P∪Q) (fun _ => Iff.rfl)
  rw [cs] at hp
  change _≤H49Q0R701.defect q (G.induce (↑(P∪Q):Set V)) T
  rw [H49Q0R701.induced_defect]
  apply core.strict_floor (T.image Subtype.val)
  · intro v hv
    obtain ⟨w,_,rfl⟩:=mem_image.mp hv
    exact w.property
  · simpa only [card_image_of_injective _ Subtype.val_injective] using hl
  · simpa only [card_image_of_injective _ Subtype.val_injective,Fintype.card_coe] using hp

#print axioms construct_two_offset_core
#print axioms TwoOffsetCore.induced_strict_floor
end Erdos585.R753

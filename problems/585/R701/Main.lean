import R653.Main
import NEQAssembly.Transport
import NEQAssembly.Counts
import Openmath.AllHTopCritical.Selectors
import Openmath.Proofs.PaperSupport.H3RangeR400
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.H49Q0R701
open QB4 B5 L34 H3Unequal AllHTopCritical
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {q : ℕ} {A B : Finset V}
def defect (q : ℕ) (G : SimpleGraph V) (S : Finset V) : ℤ :=
  ((q : ℤ)-1)*#S - ((G.induce (S : Set V)).edgeSet.ncard : ℤ)
lemma constant3 (host : Host 3 q G A B) :
    (constant 3 q : ℤ)+1 = 3*(q : ℤ)-31 := by
  have hc := host.parameters.constant_cast
  norm_num [offset] at hc
  omega
lemma paired_defect (host : Host 3 q G A B) {P Q : Finset V}
    (hP : P ⊆ A) (hQ : Q ⊆ B) :
    defect q G (P∪Q) = coreDefect q G P Q := by
  unfold defect coreDefect
  rw [induced_edges_eq_ec host.disjoint host.bipartite hP hQ,
    card_union_of_disjoint (host.disjoint.mono hP hQ)]
  push_cast
  rfl
lemma whole_violation (host : Host 3 q G A B) :
    ∃ X ⊆ A, ∃ Y ⊆ B, (ec G X Y : ℤ) <
      (q : ℤ)*((#X : ℤ)+#Y-#B) := by
  by_contra! hn
  have hcuts : ∀ X ⊆ A, ∀ C ⊆ B,
      q*#X ≤ ec G X (B\C)+q*#C := by
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
/-- Every field comes from an actual violating original cut; no TopCore premise. -/
lemma diagonal_of_cut (host : Host 3 q G A B) {X Y : Finset V}
    (hX : X ⊆ A) (hY : Y ⊆ B)
    (hv : (ec G X Y : ℤ) < (q : ℤ)*((#X : ℤ)+#Y-#B)) :
    Diagonal 3 q G A B X (B\Y) := by
  have c := AllCutRigidityR653.all_violating_cuts host hX hY hv
  have cb := card_sdiff_add_card_eq_card hY
  have hi : #X = #(B\Y)+2 := by have hh := c.imbalance; omega
  have hf := c.first_deficit
  have hc := constant3 host
  have hp := AllHTopCritical.ec_le_product (G := G) X (B\Y)
  have eligible := c.first_eligible
  have hq := host.parameters.q_pos
  have hpos : 1 ≤ #(B\Y) := by omega
  have hbound : (#(B\Y) : ℤ)*(2*(q : ℤ)-3-1-#(B\Y)) ≤
      (q : ℤ)+3-offset 3 := by
    unfold coreDefect at hf
    norm_num [offset] at hf ⊢
    zify at hi hp
    nlinarith
  have ho := host.parameters.quadratic_order hpos hbound
  refine ⟨hX, sdiff_subset, by simpa using hi, ho, c.first_proper,
    c.first_deficit, c.saturated_B, ?_⟩
  rw [ec_comm]
  norm_num [offset]
  linarith [c.reverse]
/-- Actual balanced min-q equality seed derived by R653 and the R149 retained core. -/
theorem seed (host : Host 3 q G A B) :
    ∃ P ⊆ A, ∃ Q ⊆ B, #P = #Q ∧ 2*q ≤ #P+#Q ∧
      #P+#Q < Fintype.card V ∧ coreDefect q G P Q = 3*(q : ℤ)-31 ∧
      (∀ v ∈ P∪Q, q ≤ dg G (P∪Q) v) := by
  obtain ⟨X, hX, Y, hY, hv⟩ := whole_violation host
  have d := diagonal_of_cut host hX hY hv
  have out := d.conclusion host
  let P := X\lowRoots q G X (B\Y)
  let Q := B\Y
  have hd : Disjoint P Q := host.disjoint.mono (sdiff_subset.trans hX) (sdiff_subset : Q ⊆ B)
  have count : #(lowRoots q G X Q) = 2 := by
    dsimp [Q]
    have hh := out.deleted_count
    norm_num at hh
    omega
  have hc := card_sdiff_add_card_eq_card (lowRoots_subset (G := G) q X Q)
  have hi := d.surplus
  have hr : retained q G X Q = P∪Q := rfl
  refine ⟨P, sdiff_subset.trans hX, Q, sdiff_subset, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [P, Q] at *
    omega
  · rw [← card_union_of_disjoint hd, ← hr]
    exact out.retained_eligible
  · rw [← card_union_of_disjoint hd, ← hr]
    exact d.retained_proper host
  · rw [← constant3 host]
    exact out.retained_deficit
  · rw [← hr]
    exact out.retained_minimum
/-- Equality candidates include every original induced support, including unequal ones. -/
def EqualPiece (q : ℕ) (G : SimpleGraph V) (A B P Q : Finset V) : Prop :=
  P ⊆ A ∧ Q ⊆ B ∧ 3 ≤ #P+#Q ∧ #P+#Q < Fintype.card V ∧
    coreDefect q G P Q = 3*(q : ℤ)-31
lemma equality_minimum (host : Host 3 q G A B) :
    ∃ P Q : Finset V, EqualPiece q G A B P Q ∧
      ∀ P' Q', EqualPiece q G A B P' Q' → #P+#Q ≤ #P'+#Q' := by
  obtain ⟨P, hP, Q, hQ, _, ho, hp, hf, _⟩ := seed host
  let candidates : Finset (Finset V × Finset V) :=
    (univ ×ˢ univ).filter fun t => EqualPiece q G A B t.1 t.2
  have hn : candidates.Nonempty := ⟨(P,Q), by
    simp only [candidates, mem_filter, mem_product, mem_univ, true_and]
    exact ⟨hP, hQ, by have hq := host.parameters.large; norm_num at hq; omega, hp, hf⟩⟩
  obtain ⟨t, ht, hmin⟩ := candidates.exists_min_image (fun t => #t.1+#t.2) hn
  refine ⟨t.1, t.2, (mem_filter.mp ht).2, ?_⟩
  intro P' Q' hh
  exact hmin (P',Q') (by simp [candidates, hh])
lemma paired_floor (host : Host 3 q G A B) {P Q : Finset V}
    (hP : P ⊆ A) (hQ : Q ⊆ B) (hl : 3 ≤ #P+#Q)
    (hp : #P+#Q < Fintype.card V) :
    3*(q : ℤ)-31 ≤ coreDefect q G P Q := by
  have hd := host.disjoint.mono hP hQ
  have hc := card_union_of_disjoint hd
  have ff := host.extended_floor (W := P∪Q) (by omega) (Subset.rfl) (by omega)
  rw [constant3 host] at ff
  change _ ≤ defect q G (P∪Q) at ff
  rw [paired_defect host hP hQ] at ff
  exact ff
lemma equality_order (host : Host 3 q G A B) {P Q : Finset V}
    (piece : EqualPiece q G A B P Q) : 2*q ≤ #P+#Q := by
  obtain ⟨hP,hQ,hl,hproper,hf⟩ := piece
  have hp := AllHTopCritical.ec_le_product (G := G) P Q
  have hq : 16384 ≤ q := by simpa using host.parameters.large
  by_contra! hn
  have hlo : (3 : ℤ) ≤ (#P : ℤ)+#Q := by omega
  have hhi : (#P : ℤ)+#Q ≤ 2*(q : ℤ)-1 := by omega
  have sq := sq_nonneg ((#P : ℤ)-#Q)
  have poly := mul_nonneg (show 0 ≤ (#P : ℤ)+#Q-3 by omega)
    (show 0 ≤ 2*(q : ℤ)-1-(#P+#Q) by omega)
  unfold coreDefect at hf
  zify at hp
  nlinarith
omit [Fintype V] in
lemma erase_defect {P Q : Finset V} {v : V} (hv : v ∈ P) :
    coreDefect q G (P.erase v) Q = coreDefect q G P Q - ((q : ℤ)-1) + dg G Q v := by
  have h := potential_erase_left (G := G) (2*(q : ℤ)-2) hv Q
  have h1 := twice_coreDefect (G := G) q P Q
  have h2 := twice_coreDefect (G := G) q (P.erase v) Q
  linarith
/-- Finite peeling in minimum form: an r-degree deletion preserves equality and lowers order. -/
lemma minimum_minA (host : Host 3 q G A B) {P Q : Finset V}
    (piece : EqualPiece q G A B P Q)
    (minimal : ∀ P' Q', EqualPiece q G A B P' Q' → #P+#Q ≤ #P'+#Q') :
    ∀ v ∈ P, q ≤ dg G Q v := by
  intro v hv
  have ho := equality_order host piece
  have hc := card_erase_add_one hv
  have hlarge : 16384 ≤ q := by simpa using host.parameters.large
  have hfloor := paired_floor host ((erase_subset v P).trans piece.1) piece.2.1
    (by omega) (by have hp := piece.2.2.2.1; omega)
  have he := erase_defect (q := q) (G := G) (Q := Q) hv
  have hf := piece.2.2.2.2
  by_contra! hn
  have equal : coreDefect q G (P.erase v) Q = 3*(q : ℤ)-31 := by omega
  have lesser : EqualPiece q G A B (P.erase v) Q :=
    ⟨(erase_subset v P).trans piece.1, piece.2.1, by omega,
      by have hp := piece.2.2.2.1; omega, equal⟩
  have hh := minimal (P.erase v) Q lesser
  omega
lemma minimum_minB (host : Host 3 q G A B) {P Q : Finset V}
    (piece : EqualPiece q G A B P Q)
    (minimal : ∀ P' Q', EqualPiece q G A B P' Q' → #P+#Q ≤ #P'+#Q') :
    ∀ v ∈ Q, q ≤ dg G P v := by
  apply minimum_minA host.swap
  · refine ⟨piece.2.1, piece.1, by have h := piece.2.2.1; omega,
      by have h := piece.2.2.2.1; omega, ?_⟩
    rw [← coreDefect_symm]
    exact piece.2.2.2.2
  · intro Q' P' h
    have hswap : EqualPiece q G A B P' Q' := by
      refine ⟨h.2.1, h.1, by have hh := h.2.2.1; omega,
        by have hh := h.2.2.2.1; omega, ?_⟩
      rw [← coreDefect_symm]
      exact h.2.2.2.2
    have hh := minimal P' Q' hswap
    omega
lemma piece_imbalance (host : Host 3 q G A B) {P Q : Finset V}
    (piece : EqualPiece q G A B P Q) : #Q ≤ #P+2 ∧ #P ≤ #Q+2 := by
  have hlarge : 16384 ≤ q := by simpa using host.parameters.large
  have ca := deficiency_nonneg (G := G) (W := Q) (X := P) (2*(q : ℤ)-2)
    (fun v hv => show (dg G Q v : ℤ) ≤ 2*q-2 by
      have h := (dg_le_ambient (G := G) Q v).trans (host.cap_degree v); omega)
  have cb := deficiency_nonneg (G := G) (W := P) (X := Q) (2*(q : ℤ)-2)
    (fun v hv => show (dg G P v : ℤ) ≤ 2*q-2 by
      have h := (dg_le_ambient (G := G) P v).trans (host.cap_degree v); omega)
  rw [deficiency_eq] at ca cb
  rw [ec_comm (G := G) Q P] at cb
  have hf := piece.2.2.2.2
  unfold coreDefect at hf
  constructor
  · by_contra! hn
    have hm := mul_nonneg (show 0 ≤ (q : ℤ)-1 by omega)
      (show 0 ≤ (#Q : ℤ)-#P-3 by omega)
    nlinarith
  · by_contra! hn
    have hm := mul_nonneg (show 0 ≤ (q : ℤ)-1 by omega)
      (show 0 ≤ (#P : ℤ)-#Q-3 by omega)
    nlinarith
/-- R400 a=31 acts on original adjacent pairs; no induced relabeling is assumed. -/
lemma exclude_unequal (host : Host 3 q G A B) {P Q : Finset V} {j : ℕ}
    (piece : EqualPiece q G A B P Q)
    (minimal : ∀ P' Q', EqualPiece q G A B P' Q' → #P+#Q ≤ #P'+#Q')
    (branch : j = 1 ∨ j = 2) (card : #Q = #P+j) : False := by
  have hlarge : 16384 ≤ q := by simpa using host.parameters.large
  have hmA := minimum_minA host piece minimal
  have hmB := minimum_minB host piece minimal
  have hcapA : ∀ v ∈ P, dg G Q v ≤ 2*q-2 :=
    fun v _ => (dg_le_ambient (G := G) Q v).trans (host.cap_degree v)
  have hcapB : ∀ v ∈ Q, dg G P v ≤ 2*q-2 :=
    fun v _ => (dg_le_ambient (G := G) P v).trans (host.cap_degree v)
  have deficient : deficiency (2*(q : ℤ)-2) G Q P =
      3*(q : ℤ)-31-((q : ℤ)-1)*j := by
    rw [deficiency_eq]
    have hf := piece.2.2.2.2
    unfold coreDefect at hf
    zify at card
    nlinarith
  have sparse : ∀ X ⊆ P, ∀ Y ⊆ Q, 3 ≤ #X+#Y → #X+#Y < #P+#Q →
      2*(3*(q : ℤ)-31) ≤ potential (2*(q : ℤ)-2) G X Y := by
    intro X hX Y hY hl hp
    have hf := paired_floor host (hX.trans piece.1) (hY.trans piece.2.1) hl
      (lt_trans hp piece.2.2.2.1)
    rw [← twice_coreDefect]
    linarith
  have hd := host.disjoint.mono piece.1 piece.2.1
  have omitted : ∃ O : Finset V, O ⊆ Q ∧ #O = j ∧
      ∀ T ⊆ Q, O ⊆ T → thetaJ q j G P Q T ≤ 0 := by
    rcases branch with hj | hj
    · have d : AllHNextH3R400.Data 3 q 31 j G P Q := by
        refine ⟨⟨by decide, rfl, by simpa using hlarge, by decide, by decide,
          by simpa using hj⟩, hd, card, hmA, hcapA, hmB, hcapB, ?_, ?_⟩
        · simpa using deficient
        · simpa using sparse
      exact d.common_omission (AllHNextH3R400.petal_escape (G := G))
        (AllHNextH3R400.top_escape (G := G))
    · have d : AllHLargestH3R400.Data 3 q 31 j G P Q := by
        refine ⟨⟨by decide, rfl, by simpa using hlarge, by decide, by decide,
          by simpa using hj⟩, hd, card, hmA, hcapA, hmB, hcapB, ?_, ?_⟩
        · simpa using deficient
        · simpa using sparse
      exact d.common_omission (AllHLargestH3R400.petal_escape (G := G))
  obtain ⟨O,hO,hOj,hcuts⟩ := omitted
  have hf := factor_of_common_omission q j card hO hOj hcuts
  have hp : P.Nonempty := card_pos.mp (by
    have ho := equality_order host piece
    rcases branch with hj | hj <;> omega)
  obtain ⟨H,_,hne,hreg⟩ := factor_exact_subgraph host.parameters.q_pos hp
    (hd.mono_right sdiff_subset) hf
  exact host.no_regular ⟨H,hne,hreg⟩
lemma minimum_balanced (host : Host 3 q G A B) {P Q : Finset V}
    (piece : EqualPiece q G A B P Q)
    (minimal : ∀ P' Q', EqualPiece q G A B P' Q' → #P+#Q ≤ #P'+#Q') :
    #P = #Q := by
  have hi := piece_imbalance host piece
  by_contra hn
  by_cases hlt : #P < #Q
  · have hcases : #Q = #P+1 ∨ #Q = #P+2 := by omega
    rcases hcases with h1 | h2
    · exact exclude_unequal host piece minimal (Or.inl rfl) h1
    · exact exclude_unequal host piece minimal (Or.inr rfl) h2
  · have pswap : EqualPiece q G B A Q P := by
      refine ⟨piece.2.1,piece.1,by have h := piece.2.2.1; omega,
        by have h := piece.2.2.2.1; omega, ?_⟩
      rw [← coreDefect_symm]
      exact piece.2.2.2.2
    have mswap : ∀ Q' P', EqualPiece q G B A Q' P' → #Q+#P ≤ #Q'+#P' := by
      intro Q' P' hh
      have p : EqualPiece q G A B P' Q' := by
        refine ⟨hh.2.1,hh.1,by have h := hh.2.2.1; omega,
          by have h := hh.2.2.2.1; omega, ?_⟩
        rw [← coreDefect_symm]
        exact hh.2.2.2.2
      have h := minimal P' Q' p
      omega
    have hcases : #P = #Q+1 ∨ #P = #Q+2 := by omega
    rcases hcases with h1 | h2
    · exact exclude_unequal host.swap pswap mswap (Or.inl rfl) h1
    · exact exclude_unequal host.swap pswap mswap (Or.inr rfl) h2
lemma split_support (host : Host 3 q G A B) (S : Finset V) :
    (S∩A)∪(S∩B) = S := by
  rw [← inter_union_distrib_left, host.cover, inter_univ]
/-- Global finite minimum pays EVERY proper internal support, without a supplied strict floor. -/
lemma minimum_strict_floor (host : Host 3 q G A B) {P Q : Finset V}
    (piece : EqualPiece q G A B P Q)
    (minimal : ∀ P' Q', EqualPiece q G A B P' Q' → #P+#Q ≤ #P'+#Q') :
    ∀ S ⊆ P∪Q, 3 ≤ #S → #S < #(P∪Q) → 3*(q : ℤ)-30 ≤ defect q G S := by
  intro S hS hl hp
  have hd := host.disjoint.mono piece.1 piece.2.1
  have hc := card_union_of_disjoint hd
  have hf := host.extended_floor (W := P∪Q) (by have hh := piece.2.2.2.1; omega) hS hl
  rw [constant3 host] at hf
  change 3*(q : ℤ)-31 ≤ defect q G S at hf
  by_contra! hn
  have heq : defect q G S = 3*(q : ℤ)-31 := by omega
  have hsplit := split_support host S
  have hdis := host.disjoint.mono (inter_subset_right : S∩A ⊆ A) (inter_subset_right : S∩B ⊆ B)
  have hcard := card_union_of_disjoint hdis
  rw [hsplit] at hcard
  have hdef := paired_defect host (inter_subset_right : S∩A ⊆ A) (inter_subset_right : S∩B ⊆ B)
  rw [hsplit] at hdef
  have p : EqualPiece q G A B (S∩A) (S∩B) :=
    ⟨inter_subset_right,inter_subset_right,by omega,
      by have hh := piece.2.2.2.1; omega,by omega⟩
  have hm := minimal (S∩A) (S∩B) p
  omega
/-- The requested actual original Q0 package, with all floors derived internally. -/
structure Q0 (q : ℕ) (G : SimpleGraph V) (A B P Q : Finset V) : Prop where
  left_subset : P ⊆ A
  right_subset : Q ⊆ B
  disjoint : Disjoint P Q
  balanced : #P = #Q
  nonempty : (P∪Q).Nonempty
  order : 2*q ≤ #(P∪Q)
  proper : #(P∪Q) < Fintype.card V
  exact_defect : defect q G (P∪Q) = 3*(q : ℤ)-31
  minimum : ∀ v : (P∪Q : Finset V), q ≤ (G.induce (P∪Q : Finset V)).degree v
  cap : ∀ v : (P∪Q : Finset V), (G.induce (P∪Q : Finset V)).degree v ≤ 2*q-2
  strict_floor : ∀ S ⊆ P∪Q, 3 ≤ #S → #S < #(P∪Q) →
    3*(q : ℤ)-30 ≤ defect q G S
  minimum_equality_order : ∀ P' Q', EqualPiece q G A B P' Q' → #P+#Q ≤ #P'+#Q'
  no_regular : Noq q (G.induce (P∪Q : Finset V))
  original_adjacency : ∀ v w : (P∪Q : Finset V),
    (G.induce (P∪Q : Finset V)).Adj v w ↔ G.Adj v.val w.val

/-- Whole balanced critical Host3 to an actual minimum-order proper balanced min-q Q0. -/
theorem construct_q0 (host : Host 3 q G A B) :
    ∃ P Q : Finset V, Q0 q G A B P Q := by
  obtain ⟨P,Q,piece,hm⟩ := equality_minimum host
  have hd := host.disjoint.mono piece.1 piece.2.1
  have hc := card_union_of_disjoint hd
  have ho := equality_order host piece
  have hmin : ∀ v ∈ P∪Q, q ≤ dg G (P∪Q) v := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · rw [host.dg_union_left piece.1 piece.2.1 (piece.1 hv)]
      exact minimum_minA host piece hm v hv
    · rw [host.dg_union_right piece.1 piece.2.1 (piece.2.1 hv)]
      exact minimum_minB host piece hm v hv
  refine ⟨P,Q,piece.1,piece.2.1,hd,minimum_balanced host piece hm,?_,by omega,
    by have hp := piece.2.2.2.1; omega,?_,?_,?_,minimum_strict_floor host piece hm,hm,?_,?_⟩
  · exact card_pos.mp (by have hq := host.parameters.q_pos; omega)
  · rw [paired_defect host piece.1 piece.2.1]
    exact piece.2.2.2.2
  · intro v
    rw [NEQAssembly.induced_degree_eq_dg]
    exact hmin v.val v.property
  · intro v
    rw [NEQAssembly.induced_degree_eq_dg]
    exact (dg_le_ambient (G := G) (P∪Q) v.val).trans (host.cap_degree v.val)
  · intro h
    exact host.no_regular (NEQAssembly.original_induced_regular_transport G (P∪Q) h)
  · intro v w
    rfl

/-- Nested induced supports preserve cardinalities and actual original edge counts. -/
lemma induced_defect (S : Finset V) (T : Finset (S : Set V)) :
    defect q (G.induce (S : Set V)) T = defect q G (T.image Subtype.val) := by
  let f : G.induce (S : Set V) ↪g G := SimpleGraph.Embedding.induce (G := G) (S : Set V)
  have he := NEQAssembly.ec_embedding_image (G.induce (S : Set V)) G f T T
  rw [NEQAssembly.ec_self_eq_twice_induced_edges,
    NEQAssembly.ec_self_eq_twice_induced_edges] at he
  have hedges : ((G.induce (S : Set V)).induce (T : Set (S : Set V))).edgeSet.ncard =
      (G.induce (T.image Subtype.val : Set V)).edgeSet.ncard := by
    apply Nat.mul_left_cancel (show 0 < 2 by decide)
    exact he.symm
  unfold defect
  rw [hedges, card_image_of_injective _ Subtype.val_injective]
lemma Q0.induced_strict_floor {P Q : Finset V} (piece : Q0 q G A B P Q) :
    ∀ T : Finset (P∪Q : Finset V), 3 ≤ #T →
      #T < Fintype.card (P∪Q : Finset V) →
      3*(q : ℤ)-30 ≤ defect q (G.induce (P∪Q : Finset V)) T := by
  intro T hl hp
  rw [induced_defect]
  apply piece.strict_floor (T.image Subtype.val)
  · intro v hv
    obtain ⟨w,_,rfl⟩ := mem_image.mp hv
    exact w.property
  · simpa only [card_image_of_injective _ Subtype.val_injective] using hl
  · simpa only [card_image_of_injective _ Subtype.val_injective,
      Fintype.card_coe] using hp

#print axioms construct_q0
#print axioms Q0.induced_strict_floor
end Erdos585.H49Q0R701

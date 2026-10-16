import Openmath.Proofs.QB4.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 2048

open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace Erdos585.R837
open QB4
universe u
variable {V : Type u} [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Two finite sets of ORIGINAL vertices, representing the induced cross graph. -/
abbrev Support (V : Type u) := Finset V × Finset V

def order (S : Support V) : ℕ := S.1.card + S.2.card

def deficit (r : ℕ) (S : Support V) : ℤ :=
  (r : ℤ) * order S - ec G S.1 S.2

def Included (T S : Support V) : Prop := T.1 ⊆ S.1 ∧ T.2 ⊆ S.2

/-- Ensures cross-edge counts are the FULL actual original induced edge counts. -/
def InducedBipartite (S : Support V) : Prop :=
  Disjoint S.1 S.2 ∧
  (∀ v ∈ S.1, ∀ w ∈ S.1, ¬ G.Adj v w) ∧
  (∀ v ∈ S.2, ∀ w ∈ S.2, ¬ G.Adj v w)

/-- Sequential removal of actual original vertices at current crossdegree at most r. -/
inductive Peels (r : ℕ) : Support V → Support V → Prop
  | refl (S) : Peels r S S
  | left {A B T} (v : V) (hv : v ∈ A) (hd : dg G B v ≤ r)
      (tail : Peels r (A.erase v, B) T) : Peels r (A, B) T
  | right {A B T} (v : V) (hv : v ∈ B) (hd : dg G A v ≤ r)
      (tail : Peels r (A, B.erase v) T) : Peels r (A, B) T

def MinCore (q : ℕ) (S : Support V) : Prop :=
  (∀ v ∈ S.1, q ≤ dg G S.2 v) ∧ (∀ v ∈ S.2, q ≤ dg G S.1 v)

def Capped (D : ℕ) (S : Support V) : Prop :=
  (∀ v ∈ S.1, dg G S.2 v ≤ D) ∧ (∀ v ∈ S.2, dg G S.1 v ≤ D)

/-- Actual nonempty q-regular original edge selection; supports may be proper or disconnected. -/
def HasFactor (q : ℕ) (S : Support V) : Prop :=
  ∃ J : SimpleGraph V, J ≤ G ∧ ∃ X Y : Finset V,
    X ⊆ S.1 ∧ Y ⊆ S.2 ∧ 0 < X.card + Y.card ∧
    (∀ x ∈ X, (Y.filter (J.Adj x)).card = q) ∧
    (∀ y ∈ Y, (X.filter (J.Adj y)).card = q)

def Noq (q : ℕ) (S : Support V) : Prop := ¬ HasFactor G q S


variable {G}

omit [DecidableEq V] in
lemma edge_bound (A B : Finset V) : ec G A B ≤ A.card * B.card := by
  unfold ec
  calc ∑ a ∈ A, dg G B a ≤ ∑ _a ∈ A, B.card := sum_le_sum fun a _ => dg_le_card B a
    _ = A.card * B.card := by simp

lemma erase_left {A B : Finset V} {v : V} (hv : v ∈ A) (r : ℕ) :
    deficit G r (A.erase v, B) = deficit G r (A,B) + (dg G B v : ℤ) - r := by
  have h1 : ec G (A.erase v) B + dg G B v = ec G A B := sum_erase_add A _ hv
  have h2 := card_erase_add_one hv
  unfold deficit order
  dsimp
  nlinarith

lemma erase_right {A B : Finset V} {v : V} (hv : v ∈ B) (r : ℕ) :
    deficit G r (A, B.erase v) = deficit G r (A,B) + (dg G A v : ℤ) - r := by
  have h1 : ec G A (B.erase v) + dg G A v = ec G A B := by
    rw [ec_comm A (B.erase v), ec_comm A B]
    exact sum_erase_add B _ hv
  have h2 := card_erase_add_one hv
  unfold deficit order
  dsimp
  nlinarith

lemma Peels.included {r : ℕ} {H K : Support V} (p : Peels G r H K) : Included K H := by
  induction p with
  | refl => exact ⟨Subset.rfl, Subset.rfl⟩
  | left v hv hd tail ih => exact ⟨ih.1.trans (erase_subset v _), ih.2⟩
  | right v hv hd tail ih => exact ⟨ih.1, ih.2.trans (erase_subset v _)⟩


lemma exists_terminal (r : ℕ) (H : Support V) :
    ∃ K, Peels G r H K ∧ MinCore G (r+1) K := by
  have main : ∀ n : ℕ, ∀ S : Support V, order S = n →
      ∃ K, Peels G r S K ∧ MinCore G (r+1) K := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hn
      by_cases hm : MinCore G (r+1) S
      · exact ⟨S,Peels.refl _,hm⟩
      · obtain ⟨A,B⟩ := S
        simp only [MinCore, not_and_or, not_forall] at hm
        rcases hm with hm | hm
        · obtain ⟨v,hv,hd⟩ := hm
          have hd' : dg G B v ≤ r := by omega
          have hc := card_erase_add_one hv
          have hlt : order (A.erase v,B) < n := by simp only [order] at hn ⊢; omega
          obtain ⟨K,hp,hk⟩ := ih _ hlt (A.erase v,B) rfl
          exact ⟨K,Peels.left v hv hd' hp,hk⟩
        · obtain ⟨v,hv,hd⟩ := hm
          have hd' : dg G A v ≤ r := by omega
          have hc := card_erase_add_one hv
          have hlt : order (A,B.erase v) < n := by simp only [order] at hn ⊢; omega
          obtain ⟨K,hp,hk⟩ := ih _ hlt (A,B.erase v) rfl
          exact ⟨K,Peels.right v hv hd' hp,hk⟩
  exact main _ H rfl

omit [DecidableEq V] in
lemma core_order {r : ℕ} {K : Support V} (hk : MinCore G (r+1) K)
    (hne : 0 < order K) : 2*(r+1) ≤ order K := by
  have ha : r+1 ≤ K.1.card := by
    by_cases hb : K.2.Nonempty
    · obtain ⟨v,hv⟩ := hb
      exact (hk.2 v hv).trans (dg_le_card K.1 v)
    · have he := not_nonempty_iff_eq_empty.mp hb
      have hp : K.1.Nonempty := by simpa [order,he] using hne
      obtain ⟨v,hv⟩ := hp
      have := hk.1 v hv
      simp [he,dg] at this
  have hb : r+1 ≤ K.2.card := by
    obtain ⟨v,hv⟩ := card_pos.mp (show 0 < K.1.card by omega)
    exact (hk.1 v hv).trans (dg_le_card K.2 v)
  unfold order
  omega

-- Elementary support/process machinery above is adapted from R603.
-- All degrees and edge counts retain QB4's actual original graph semantics.

/-- Exact threshold ledger, including negative pruning charges. -/
lemma Peels.cost_le {T r : ℕ} {H K : Support V} (p : Peels G T H K) :
    deficit G r K ≤ deficit G r H +
      ((order H : ℤ) - order K) * ((T : ℤ) - r) := by
  induction p with
  | refl S => simp
  | @left A B K v hv hd tail ih =>
    have hc := card_erase_add_one hv
    have he := erase_left (G := G) (B := B) hv r
    have hd' : (dg G B v : ℤ) ≤ T := by exact_mod_cast hd
    have ho : (order (A.erase v,B) : ℤ) + 1 = order (A,B) := by
      simp only [order]; exact_mod_cast (by omega : (A.erase v).card + B.card + 1 = A.card+B.card)
    nlinarith
  | @right A B K v hv hd tail ih =>
    have hc := card_erase_add_one hv
    have he := erase_right (G := G) (A := A) hv r
    have hd' : (dg G A v : ℤ) ≤ T := by exact_mod_cast hd
    have ho : (order (A,B.erase v) : ℤ) + 1 = order (A,B) := by
      simp only [order]; exact_mod_cast (by omega : A.card + (B.erase v).card + 1 = A.card+B.card)
    nlinarith

/-- An exact sequential ledger of the ACTUAL current-degree-minus-r charges. -/
lemma Peels.ledger {T r : ℕ} {H K : Support V} (p : Peels G T H K) :
    ∃ charges : List ℤ, charges.length=order H-order K ∧
      charges.sum=deficit G r K-deficit G r H ∧
      ∀ charge ∈ charges, charge ≤ (T:ℤ)-r := by
  induction p with
  | refl S => exact ⟨[],by simp,by simp,by simp⟩
  | @left A B K v hv hd tail ih =>
    obtain ⟨charges,len,total,bound⟩ := ih
    have inc := tail.included
    have leord : order K ≤ order (A.erase v,B) :=
      Nat.add_le_add (card_le_card inc.1) (card_le_card inc.2)
    have hc := card_erase_add_one hv
    have eq := erase_left (G := G) (B := B) hv r
    refine ⟨((dg G B v:ℤ)-r)::charges,?_,?_,?_⟩
    · simp only [List.length_cons,len]
      dsimp [order] at *
      omega
    · simp only [List.sum_cons,total]
      linarith
    · intro z hz
      rcases List.mem_cons.mp hz with eq | hz
      · subst z
        exact sub_le_sub_right (Int.ofNat_le.mpr hd) _
      · exact bound z hz
  | @right A B K v hv hd tail ih =>
    obtain ⟨charges,len,total,bound⟩ := ih
    have inc := tail.included
    have leord : order K ≤ order (A,B.erase v) :=
      Nat.add_le_add (card_le_card inc.1) (card_le_card inc.2)
    have hc := card_erase_add_one hv
    have eq := erase_right (G := G) (A := A) hv r
    refine ⟨((dg G A v:ℤ)-r)::charges,?_,?_,?_⟩
    · simp only [List.length_cons,len]
      dsimp [order] at *
      omega
    · simp only [List.sum_cons,total]
      linarith
    · intro z hz
      rcases List.mem_cons.mp hz with eq | hz
      · subst z
        exact sub_le_sub_right (Int.ofNat_le.mpr hd) _
      · exact bound z hz

/-- A sufficiently long actual process has an actual prefix of k removals. -/
lemma Peels.prefix {T : ℕ} {H K : Support V} (p : Peels G T H K)
    (k : ℕ) (hk : order K + k ≤ order H) :
    ∃ M, Peels G T H M ∧ Peels G T M K ∧ order M + k = order H := by
  induction p generalizing k with
  | refl S =>
    have : k = 0 := by omega
    subst k
    exact ⟨S,Peels.refl _,Peels.refl _,by omega⟩
  | @left A B K v hv hd tail ih =>
    cases k with
    | zero => exact ⟨(A,B),Peels.refl _,Peels.left v hv hd tail,by omega⟩
    | succ k =>
      have hc := card_erase_add_one hv
      have ho : order (A.erase v,B)+1=order (A,B) := by simp only [order]; omega
      obtain ⟨M,hm,mt,he⟩ := ih k (by omega)
      exact ⟨M,Peels.left v hv hd hm,mt,by omega⟩
  | @right A B K v hv hd tail ih =>
    cases k with
    | zero => exact ⟨(A,B),Peels.refl _,Peels.right v hv hd tail,by omega⟩
    | succ k =>
      have hc := card_erase_add_one hv
      have ho : order (A,B.erase v)+1=order (A,B) := by simp only [order]; omega
      obtain ⟨M,hm,mt,he⟩ := ih k (by omega)
      exact ⟨M,Peels.right v hv hd hm,mt,by omega⟩



lemma original_cap_fringe {r : ℕ} {H K : Support V} (hsub : Included K H)
    (hcap : Capped G (2*r) H) :
    deficit G r (H.1 \ K.1,H.2 \ K.2) ≤ deficit G r H + deficit G r K := by
  have ea := ec_sdiff_add_left (G := G) hsub.1 H.2
  have eb := ec_sdiff_add_right (G := G) hsub.2 K.1
  have ex := ec_sdiff_add_right (G := G) hsub.2 (H.1 \ K.1)
  have ey := ec_sdiff_add_left (G := G) hsub.1 K.2
  have ha := card_sdiff_add_card_eq_card hsub.1
  have hb := card_sdiff_add_card_eq_card hsub.2
  have capA : ec G K.1 H.2 ≤ (2*r)*K.1.card := by
    unfold ec
    calc ∑ x ∈ K.1, dg G H.2 x ≤ ∑ _x ∈ K.1, 2*r :=
        sum_le_sum fun x hx => hcap.1 x (hsub.1 hx)
      _ = (2*r)*K.1.card := by simp [mul_comm]
  have capB : ec G H.1 K.2 ≤ (2*r)*K.2.card := by
    rw [ec_comm]
    unfold ec
    calc ∑ x ∈ K.2, dg G H.1 x ≤ ∑ _x ∈ K.2, 2*r :=
        sum_le_sum fun x hx => hcap.2 x (hsub.2 hx)
      _ = (2*r)*K.2.card := by simp [mul_comm]
  unfold deficit order at ⊢
  dsimp at ⊢
  have ea' := congrArg (fun n : ℕ => (n:ℤ)) ea
  have eb' := congrArg (fun n : ℕ => (n:ℤ)) eb
  have ex' := congrArg (fun n : ℕ => (n:ℤ)) ex
  have ey' := congrArg (fun n : ℕ => (n:ℤ)) ey
  have ha' := congrArg (fun n : ℕ => (n:ℤ)) ha
  have hb' := congrArg (fun n : ℕ => (n:ℤ)) hb
  have ca' := Int.ofNat_le.mpr capA
  have cb' := Int.ofNat_le.mpr capB
  push_cast at ea' eb' ex' ey' ha' hb' ca' cb' ⊢
  nlinarith


/-- Actual first-2h prefix contradiction from original cap and exact deficit. -/
theorem deletion_count {h q : ℕ} {H K : Support V}
    (hh : 6 ≤ h) (hq : 4096*(h+1)^2 ≤ q)
    (hf : deficit G (q-1) H = (h:ℤ)*q-16*(h:ℤ)^2)
    (hc : Capped G (2*(q-1)) H)
    (p : Peels G (q+2*h-5) H K) : order H - order K ≤ 2*h-1 := by
  have hq1 : 1 ≤ q := by nlinarith
  have hr : ((q-1:ℕ):ℤ) = (q:ℤ)-1 := by omega
  have ht : ((q+2*h-5:ℕ):ℤ) = (q:ℤ)+2*h-5 := by omega
  have sub := p.included
  have leord : order K ≤ order H := Nat.add_le_add (card_le_card sub.1) (card_le_card sub.2)
  by_contra hnot
  obtain ⟨M,pm,_,hm⟩ := p.prefix (2*h) (by omega)
  have sm := pm.included
  let P : Support V := (H.1\M.1,H.2\M.2)
  have ha := card_sdiff_add_card_eq_card sm.1
  have hb := card_sdiff_add_card_eq_card sm.2
  have pn : order P = 2*h := by dsimp [P,order] at *; omega
  have cp := pm.cost_le (r := q-1)
  have fp := original_cap_fringe sm hc
  change deficit G (q-1) P ≤ deficit G (q-1) H + deficit G (q-1) M at fp
  have edge : (ec G P.1 P.2:ℤ) ≤ (h:ℤ)^2 := by
    have ee := edge_bound (G := G) P.1 P.2
    have en : (P.1.card:ℤ)+P.2.card=2*(h:ℤ) := by exact_mod_cast pn
    have ee' : (ec G P.1 P.2:ℤ) ≤ (P.1.card:ℤ)*P.2.card := by exact_mod_cast ee
    nlinarith [sq_nonneg ((P.1.card:ℤ)-P.2.card)]
  have low : (q:ℤ)*2*h-2*h-(h:ℤ)^2 ≤ deficit G (q-1) P := by
    unfold deficit
    rw [pn,hr]
    push_cast
    nlinarith
  have hm' : (order M:ℤ)+2*(h:ℤ)=order H := by exact_mod_cast hm
  rw [hf,hr,ht] at cp
  rw [hf] at fp
  have hh' : (6:ℤ) ≤ h := by exact_mod_cast hh
  nlinarith [sq_nonneg (h:ℤ)]


def diff (H K : Support V) : Support V := (H.1\K.1,H.2\K.2)
def join (H K : Support V) : Support V := (H.1∪K.1,H.2∪K.2)
def cut (G : SimpleGraph V) [DecidableRel G.Adj] (H K : Support V) : ℕ := ec G H.1 K.2 + ec G K.1 H.2

def StrictFloor (G : SimpleGraph V) [DecidableRel G.Adj] (h r : ℕ) (F : ℤ) (H : Support V) : Prop :=
  ∀ U, Included U H → h ≤ order U → order U < order H → F+1 ≤ deficit G r U

lemma order_diff {H K : Support V} (s : Included K H) :
    order (diff H K) + order K = order H := by
  have ha := card_sdiff_add_card_eq_card s.1
  have hb := card_sdiff_add_card_eq_card s.2
  dsimp [diff,order]; omega

lemma ec_union_left {A B C : Finset V} (hd : Disjoint A B) :
    ec G (A∪B) C = ec G A C + ec G B C := by
  exact sum_union hd

lemma ec_union_right {A B C : Finset V} (hd : Disjoint B C) :
    ec G A (B∪C) = ec G A B + ec G A C := by
  unfold ec
  simp_rw [dg_union_of_disjoint hd]
  exact sum_add_distrib

lemma deficit_join {H K : Support V}
    (ha : Disjoint H.1 K.1) (hb : Disjoint H.2 K.2) (r : ℕ) :
    deficit G r (join H K) = deficit G r H + deficit G r K - cut G H K := by
  have ea := ec_union_left (G := G) (C := H.2∪K.2) ha
  have eb := ec_union_right (G := G) (A := H.1) hb
  have ec' := ec_union_right (G := G) (A := K.1) hb
  have ca := card_union_of_disjoint ha
  have cb := card_union_of_disjoint hb
  unfold deficit order join cut
  dsimp at *
  rw [ea,eb,ec']
  push_cast
  rw [ca,cb]
  push_cast
  ring

lemma partition_deficit {H K : Support V} (s : Included K H) (r : ℕ) :
    deficit G r H = deficit G r K + deficit G r (diff H K) - cut G (diff H K) K := by
  have e : join (diff H K) K = H := by
    apply Prod.ext <;> simp only [join,diff,sdiff_union_of_subset,s.1,s.2]
  have id := deficit_join (G := G) (H := diff H K) (K := K) sdiff_disjoint sdiff_disjoint r
  rw [e] at id
  linarith

lemma cut_split {H K U : Support V} (s : Included U K) :
    cut G H (diff K U) + cut G H U = cut G H K := by
  have ea := ec_sdiff_add_right (G := G) s.2 H.1
  have eb := ec_sdiff_add_left (G := G) s.1 H.2
  dsimp [cut,diff]
  omega

/-- Exact identity on the SAME original U union the actual deleted support. -/
lemma inherited_identity {H K U : Support V}
    (s : Included K H) (u : Included U K) (r : ℕ) :
    deficit G r (join U (diff H K)) = deficit G r U +
      (cut G (diff H K) (diff K U):ℤ) - (deficit G r K-deficit G r H) := by
  have ha : Disjoint U.1 (H.1\K.1) := (sdiff_disjoint : Disjoint (H.1\K.1) K.1).symm.mono_left u.1
  have hb : Disjoint U.2 (H.2\K.2) := (sdiff_disjoint : Disjoint (H.2\K.2) K.2).symm.mono_left u.2
  have a := deficit_join (G := G) (H := U) (K := diff H K) ha hb r
  have b := partition_deficit (G := G) s r
  have c := cut_split (G := G) (H := diff H K) u
  have co : cut G U (diff H K) = cut G (diff H K) U := by
    dsimp [cut]; omega
  rw [co] at a
  have c' := congrArg (fun n : ℕ => (n:ℤ)) c
  push_cast at c'
  linarith

/-- The literal original strict floor gives exactly the cut-local inherited loss. -/
theorem inherited_floor {h r : ℕ} {F : ℤ} {H K : Support V}
    (s : Included K H) (hf : deficit G r H=F) (floor : StrictFloor G h r F H) :
    ∀ U, Included U K → h ≤ order U → order U < order K →
      deficit G r K + 1 - min (deficit G r K-F)
        (cut G (diff H K) (diff K U):ℤ) ≤ deficit G r U := by
  intro U u hu hp
  have sk : order K ≤ order H := Nat.add_le_add (card_le_card s.1) (card_le_card s.2)
  have f1 := floor U ⟨u.1.trans s.1,u.2.trans s.2⟩ hu (by omega)
  have js : Included (join U (diff H K)) H := by
    exact ⟨union_subset (u.1.trans s.1) sdiff_subset,union_subset (u.2.trans s.2) sdiff_subset⟩
  have ha : Disjoint U.1 (H.1\K.1) := (sdiff_disjoint : Disjoint (H.1\K.1) K.1).symm.mono_left u.1
  have hb : Disjoint U.2 (H.2\K.2) := (sdiff_disjoint : Disjoint (H.2\K.2) K.2).symm.mono_left u.2
  have jn : order (join U (diff H K))=order U+order (diff H K) := by
    dsimp [order,join,diff]
    rw [card_union_of_disjoint ha,card_union_of_disjoint hb]
    omega
  have dn := order_diff s
  have f2 := floor (join U (diff H K)) js (by omega) (by omega)
  have id := inherited_identity (G := G) s u r
  rw [hf] at id
  rw [id] at f2
  by_cases hc : deficit G r K-F ≤ (cut G (diff H K) (diff K U):ℤ)
  · rw [min_eq_left hc]; linarith
  · rw [min_eq_right (by omega)]; linarith


/-- Exact simultaneous original-degree cost, with internal deleted edges counted once. -/
lemma original_cost_identity {H K : Support V} (s : Included K H) (r : ℕ) :
    deficit G r K - deficit G r H =
      (ec G (diff H K).1 H.2 + ec G H.1 (diff H K).2:ℕ) -
        (r:ℤ)*order (diff H K) - ec G (diff H K).1 (diff H K).2 := by
  have part := partition_deficit (G := G) s r
  have ea := ec_sdiff_add_right (G := G) s.2 (H.1\K.1)
  have eb := ec_sdiff_add_left (G := G) s.1 (H.2\K.2)
  simp only [deficit,cut,diff] at part ⊢
  dsimp at *
  have ea' := congrArg (fun n : ℕ => (n:ℤ)) ea
  have eb' := congrArg (fun n : ℕ => (n:ℤ)) eb
  push_cast at ea' eb' ⊢
  linarith

omit [DecidableEq V] in
lemma Included.order_eq {H K : Support V} (s : Included K H) (hn : order K=order H) : K=H := by
  have ca := card_le_card s.1
  have cb := card_le_card s.2
  have ea : K.1=H.1 := eq_of_subset_of_card_le s.1 (by unfold order at hn; omega)
  have eb : K.2=H.2 := eq_of_subset_of_card_le s.2 (by unfold order at hn; omega)
  exact Prod.ext ea eb

structure Host (h q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] (H : Support V) : Prop where
  height : 6 ≤ h
  large : 4096*(h+1)^2 ≤ q
  induced : InducedBipartite G H
  order : 2*q ≤ R837.order H
  minimum : MinCore G q H
  cap : Capped G (2*(q-1)) H
  exact_deficit : deficit G (q-1) H=(h:ℤ)*q-16*(h:ℤ)^2
  proper : StrictFloor G h (q-1) ((h:ℤ)*q-16*(h:ℤ)^2) H

structure Reduction (h q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (H K : Support V) : Prop where
  process : Peels G (q+2*h-5) H K
  included : Included K H
  induced : InducedBipartite G K
  nonempty : 0 < order K
  order : 2*q ≤ R837.order K
  minimum : MinCore G (q+2*h-4) K
  cap : Capped G (2*(q-1)) K
  deleted : R837.order H-R837.order K ≤ 2*h-1
  cost_nonnegative : 0 ≤ deficit G (q-1) K-deficit G (q-1) H
  cost_upper : deficit G (q-1) K-deficit G (q-1) H ≤ 4*(h:ℤ)^2-10*h+4
  inherited : ∀ U, Included U K → h ≤ R837.order U → R837.order U < R837.order K →
    deficit G (q-1) K+1-min (deficit G (q-1) K-deficit G (q-1) H)
      (cut G (diff H K) (diff K U):ℤ) ≤ deficit G (q-1) U

/-- Complete generic actual-process theorem from the ORIGINAL host. -/
theorem threshold_reduction {h q : ℕ} {H K : Support V} (host : Host h q G H)
    (p : Peels G (q+2*h-5) H K) (terminal : MinCore G (q+2*h-4) K) :
    Reduction h q G H K := by
  have hh := host.height
  have hq := host.large
  have hqbig : 2*h+1 ≤ q := by nlinarith
  have sub := p.included
  have sle : order K ≤ order H := Nat.add_le_add (card_le_card sub.1) (card_le_card sub.2)
  have count := deletion_count hh hq host.exact_deficit host.cap p
  have hord := host.order
  have ne : 0 < order K := by omega
  have tmin : MinCore G ((q+2*h-5)+1) K := by
    convert terminal using 1; omega
  have ko := core_order tmin ne
  have elig : 2*q ≤ order K := by omega
  have kh : h ≤ order K := by omega
  have cp := p.cost_le (r := q-1)
  have hr : ((q-1:ℕ):ℤ) = (q:ℤ)-1 := by omega
  have ht : ((q+2*h-5:ℕ):ℤ) = (q:ℤ)+2*h-5 := by omega
  have diff_bound : (order H:ℤ)-order K ≤ 2*(h:ℤ)-1 := by omega
  have hh' : (6:ℤ) ≤ h := by exact_mod_cast hh
  have cost : deficit G (q-1) K-deficit G (q-1) H ≤ 4*(h:ℤ)^2-10*h+4 := by
    rw [hr,ht] at cp
    have mult := mul_le_mul_of_nonneg_right diff_bound (show 0 ≤ 2*(h:ℤ)-4 by omega)
    nlinarith
  have nonneg : 0 ≤ deficit G (q-1) K-deficit G (q-1) H := by
    by_cases he : order K=order H
    · have eq := sub.order_eq he
      rw [eq]; omega
    · have f := host.proper K sub kh (by omega)
      rw [host.exact_deficit]
      omega
  have cap : Capped G (2*(q-1)) K :=
    ⟨fun v hv => (dg_mono sub.2 v).trans (host.cap.1 v (sub.1 hv)),
     fun v hv => (dg_mono sub.1 v).trans (host.cap.2 v (sub.2 hv))⟩
  have bip : InducedBipartite G K :=
    ⟨host.induced.1.mono sub.1 sub.2,
     fun v hv w hw => host.induced.2.1 v (sub.1 hv) w (sub.1 hw),
     fun v hv w hw => host.induced.2.2 v (sub.2 hv) w (sub.2 hw)⟩
  refine ⟨p,sub,bip,ne,elig,terminal,cap,count,nonneg,cost,?_⟩
  have fl := inherited_floor (G := G) sub host.exact_deficit host.proper
  simpa only [host.exact_deficit] using fl

/-- Existence constructs the actual process; it assumes neither budget nor retained support. -/
theorem exists_threshold_reduction {h q : ℕ} {H : Support V} (host : Host h q G H) :
    ∃ K, Reduction h q G H K := by
  obtain ⟨K,p,hm⟩ := exists_terminal (G := G) (q+2*h-5) H
  have hh := host.height
  have min : MinCore G (q+2*h-4) K := by
    convert hm using 1; omega
  exact ⟨K,threshold_reduction host p min⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The identical selected original edges and selected vertices transport unchanged. -/
theorem original_factor_transport {q : ℕ} {H K : Support V}
    (s : Included K H) (factor : HasFactor G q K) : HasFactor G q H := by
  obtain ⟨J,j,X,Y,x,y,pos,dx,dy⟩ := factor
  exact ⟨J,j,X,Y,x.trans s.1,y.trans s.2,pos,dx,dy⟩


/-- Exact original-label signed gap, without any monotone-progress assertion. -/
lemma signed_gap_identity {H K : Support V} (sub : Included K H) :
    (K.2.card:ℤ)-K.1.card = (H.2.card:ℤ)-H.1.card+
      (diff H K).1.card-(diff H K).2.card := by
  have a := card_sdiff_add_card_eq_card sub.1
  have b := card_sdiff_add_card_eq_card sub.2
  dsimp [diff]
  omega

omit [DecidableEq V] in
lemma cut_simple_bound (P W : Support V) : cut G P W ≤ order P*order W := by
  have a := edge_bound (G := G) P.1 W.2
  have b := edge_bound (G := G) W.1 P.2
  dsimp [cut,order]
  nlinarith

/-- Exact retained offset; the cost is its ACTUAL deficit increment. -/
lemma retained_offset {h q : ℕ} {H K : Support V} (host : Host h q G H)
    (red : Reduction h q G H K) :
    (h:ℤ)*q-deficit G (q-1) K =
      16*(h:ℤ)^2-(deficit G (q-1) K-deficit G (q-1) H) ∧
    12*(h:ℤ)^2+10*h-4 ≤ (h:ℤ)*q-deficit G (q-1) K := by
  have e := host.exact_deficit
  have b := red.cost_upper
  constructor <;> linarith

/-- Both signs and zero are covered by the actual terminal shore bound. -/
theorem retained_imbalance {h q : ℕ} {H K : Support V} (host : Host h q G H)
    (red : Reduction h q G H K) : |(K.2.card:ℤ)-K.1.card| ≤ (h:ℤ)-1 := by
  have hh := host.height
  have hq := host.large
  have qbig : 2 ≤ q := by nlinarith
  have hr : ((q-1:ℕ):ℤ)=(q:ℤ)-1 := by omega
  have ea : ec G K.1 K.2 ≤ (2*(q-1))*K.1.card := by
    unfold ec
    calc ∑ v ∈ K.1, dg G K.2 v ≤ ∑ _v ∈ K.1, 2*(q-1) := sum_le_sum red.cap.1
      _ = (2*(q-1))*K.1.card := by simp [mul_comm]
  have eb : ec G K.1 K.2 ≤ (2*(q-1))*K.2.card := by
    rw [ec_comm]
    unfold ec
    calc ∑ v ∈ K.2, dg G K.1 v ≤ ∑ _v ∈ K.2, 2*(q-1) := sum_le_sum red.cap.2
      _ = (2*(q-1))*K.2.card := by simp [mul_comm]
  have ea' : (ec G K.1 K.2:ℤ) ≤ 2*((q-1:ℕ):ℤ)*K.1.card := by exact_mod_cast ea
  rw [hr] at ea'
  have eb' : (ec G K.1 K.2:ℤ) ≤ 2*((q-1:ℕ):ℤ)*K.2.card := by exact_mod_cast eb
  rw [hr] at eb'
  have b := red.cost_upper
  have f := host.exact_deficit
  have hh' : (6:ℤ) ≤ h := by exact_mod_cast hh
  have qb : (2:ℤ) ≤ q := by exact_mod_cast qbig
  have upper : deficit G (q-1) K < (h:ℤ)*((q:ℤ)-1) := by nlinarith
  unfold deficit order at upper
  rw [hr] at upper
  push_cast at upper
  apply abs_le.mpr
  constructor <;> nlinarith

-- Original induced-carrier transport is adapted from NEQAssembly.Transport.
noncomputable def originalMapIso {A : Type u} {B : Type u}
    {J : SimpleGraph A} {L : SimpleGraph B} (f : J →g L)
    (inj : Function.Injective f) (F : J.Subgraph) : F.coe ≃g (F.map f).coe where
  toEquiv := Equiv.Set.image f F.verts inj
  map_rel_iff' := by
    intro x y
    change (F.map f).Adj (f (x:A)) (f (y:A)) ↔ F.Adj (x:A) (y:A)
    constructor
    · rintro ⟨a,b,hab,hax,hby⟩
      have ha := inj hax
      have hb := inj hby
      simpa only [ha,hb] using hab
    · intro h
      exact ⟨x,y,h,rfl,rfl⟩

/-- Actual Mathlib subgraph factor on the terminal support transports on the identical units. -/
theorem original_induced_factor_transport [Fintype V] {q : ℕ} (K : Support V)
    (factor : ∃ F : (G.induce ((K.1∪K.2):Set V)).Subgraph,
      F.verts.Nonempty ∧ F.coe.IsRegularOfDegree q) :
    ∃ F : G.Subgraph, F.verts.Nonempty ∧ F.coe.IsRegularOfDegree q := by
  let f : G.induce ((K.1∪K.2):Set V) →g G :=
    (SimpleGraph.Embedding.induce (G := G) ((K.1∪K.2):Set V)).toHom
  obtain ⟨F,ne,reg⟩ := factor
  have inj : Function.Injective f := fun _ _ eq => Subtype.ext eq
  let e := originalMapIso f inj F
  refine ⟨F.map f,ne.image f,?_⟩
  intro v
  exact (e.symm.degree_eq v).symm.trans (reg (e.symm v))

#print axioms signed_gap_identity
#print axioms cut_simple_bound
#print axioms retained_offset
#print axioms retained_imbalance
#print axioms original_induced_factor_transport
#print axioms Peels.ledger
#print axioms deletion_count
#print axioms inherited_identity
#print axioms inherited_floor
#print axioms original_cost_identity
#print axioms threshold_reduction
#print axioms exists_threshold_reduction
#print axioms original_factor_transport
end Erdos585.R837

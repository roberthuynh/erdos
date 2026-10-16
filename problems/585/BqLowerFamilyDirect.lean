import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/- Source: BqBirthCore.lean; only its import lines removed. -/

/- 
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open Finset SimpleGraph
namespace BqLowerFamily
variable {V : Type*} [DecidableEq V]

/-- Actual graph extension with one new vertex and precisely the selected old neighbors. -/
def extendGraph (G : SimpleGraph V) (N : Finset V) : SimpleGraph (Option V) where
  Adj x y := match x, y with
    | some v, some w => G.Adj v w
    | none, some v => v ∈ N
    | some v, none => v ∈ N
    | none, none => False
  symm := ⟨by
    intro x y
    cases x <;> cases y <;> simp [G.adj_comm]⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

instance extendGraphDecidable (G : SimpleGraph V) [DecidableRel G.Adj] (N : Finset V) :
    DecidableRel (extendGraph G N).Adj := fun x y => by
  cases x <;> cases y <;> unfold extendGraph <;> infer_instance

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (N : Finset V)

@[simp] theorem degree_none : (extendGraph G N).degree none = N.card := by
  have hn : (extendGraph G N).neighborFinset none = N.image some := by
    ext x
    rw [SimpleGraph.mem_neighborFinset]
    cases x <;> simp [extendGraph]
  rw [← card_neighborFinset_eq_degree, hn, card_image_of_injective _ (Option.some_injective V)]

@[simp] theorem degree_some (v : V) :
    (extendGraph G N).degree (some v) = G.degree v + if v ∈ N then 1 else 0 := by
  have hn : (extendGraph G N).neighborFinset (some v) =
      (G.neighborFinset v).image some ∪ if v ∈ N then {none} else ∅ := by
    ext x
    rw [SimpleGraph.mem_neighborFinset]
    cases x <;> by_cases hv : v ∈ N <;> simp [extendGraph, hv]
  have hd : Disjoint ((G.neighborFinset v).image some)
      (if v ∈ N then {none} else ∅) := by
    split_ifs <;> simp
  rw [← card_neighborFinset_eq_degree, hn, card_union_of_disjoint hd,
    card_image_of_injective _ (Option.some_injective V), card_neighborFinset_eq_degree]
  split_ifs <;> simp

theorem edges_extend : (extendGraph G N).edgeFinset.card = G.edgeFinset.card + N.card := by
  have hs : (∑ x : Option V, (extendGraph G N).degree x) =
      (∑ v : V, G.degree v) + 2 * N.card := by
    rw [Fintype.sum_option]
    simp only [degree_none, degree_some, sum_add_distrib]
    have hind : (∑ v : V, if v ∈ N then 1 else 0) = N.card := by simp
    rw [hind]
    omega
  have h0 := SimpleGraph.sum_degrees_eq_twice_card_edges G
  have h1 := SimpleGraph.sum_degrees_eq_twice_card_edges (extendGraph G N)
  omega

noncomputable instance finiteSubgraphLocallyFinite {W : Type*} [Finite W]
    (K : SimpleGraph W) (H : K.Subgraph) : H.coe.LocallyFinite := fun _ => Fintype.ofFinite _

/-- Absence of arbitrary nonempty original q-regular Subgraphs. -/
def NoRegular (q : ℕ) {W : Type*} [Finite W] (K : SimpleGraph W) : Prop :=
  ¬ ∃ H : K.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q

/-- Actual degree-(q-1) birth preserves arbitrary original-support absence. -/
theorem noRegular_extend (q : ℕ) (hq : 1 ≤ q) (hN : N.card = q - 1) (hG : NoRegular q G) :
    NoRegular q (extendGraph G N) := by
  classical
  rintro ⟨H, hne, hreg⟩
  have hnone : none ∉ H.verts := by
    intro hn
    have h4 : H.degree none = q :=
      (Subgraph.coe_degree H ⟨none, hn⟩).symm.trans (hreg.degree_eq _)
    have hle := H.degree_le none
    rw [degree_none, hN] at hle
    omega
  let H0 : G.Subgraph := {
    verts := {v | some v ∈ H.verts}
    Adj := fun v w => H.Adj (some v) (some w)
    adj_sub := fun h => H.adj_sub h
    edge_vert := fun h => H.edge_vert h
    symm := ⟨by intro v w h; exact h.symm⟩ }
  let : ∀ v : V, Fintype (H0.neighborSet v) := fun _ => Fintype.ofFinite _
  have h0ne : H0.verts.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    cases x with
    | none => exact (hnone hx).elim
    | some v => exact ⟨v, hx⟩
  have hdeg (v : V) : H0.degree v = H.degree (some v) := by
    let f : H0.neighborSet v → H.neighborSet (some v) := fun w => ⟨some w.val, w.property⟩
    have hinj : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact Option.some_injective V (congrArg Subtype.val hxy)
    have hsurj : Function.Surjective f := by
      intro w
      rcases w with ⟨x, hx⟩
      cases x with
      | none => exact (hnone hx.snd_mem).elim
      | some u => exact ⟨⟨u, hx⟩, rfl⟩
    exact Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  apply hG
  refine ⟨H0, h0ne, ?_⟩
  intro v
  rw [Subgraph.coe_degree]
  rw [hdeg v.val]
  exact (Subgraph.coe_degree H ⟨some v.val, v.property⟩).symm.trans (hreg.degree_eq _)


/-- Finite actual slot units force r distinct unsaturated original vertices. -/
theorem capacity_slots {X : Type*} [DecidableEq X] (r : ℕ) (hr : 3 ≤ r)
    (S : Finset X) (g : X → ℕ)
    (hd : ∀ v ∈ S, r ≤ g v ∧ g v ≤ 2*r)
    (hc : r*r-1 ≤ ∑ v ∈ S, (2*r-g v)) :
    r ≤ (S.filter fun v => g v ≤ 2*r-1).card := by
  have hle : (∑ v ∈ S, (2*r-g v)) ≤
      ∑ v ∈ S, if g v ≤ 2*r-1 then r else 0 := by
    apply sum_le_sum
    intro v hv
    have hvd := hd v hv
    split_ifs <;> omega
  have heq : (∑ v ∈ S, if g v ≤ 2*r-1 then r else 0) =
      r * (S.filter fun v => g v ≤ 2*r-1).card := by
    rw [← sum_filter]
    simp [mul_comm]
  rw [heq] at hle
  by_contra hnot
  have hn : (S.filter fun v => g v ≤ 2*r-1).card ≤ r-1 := by omega
  have hmul := Nat.mul_le_mul_left r hn
  have hp : 1 ≤ r*r := by nlinarith
  have hp' := Nat.sub_add_cancel hp
  have hrp : 1 ≤ r := by omega
  have hrpred := Nat.sub_add_cancel hrp
  nlinarith

/-- Same actual edges and smaller-shore balance pay opposite capacity. -/
theorem opposite_slots (r a b m c C : ℕ) (hab : a ≤ b)
    (hm : m+c=r*(a+b))
    (hC : C+m=2*r*b) : c ≤ C := by
  have hmul := Nat.mul_le_mul_left r hab
  nlinarith

#print axioms degree_none
#print axioms degree_some
#print axioms edges_extend
#print axioms noRegular_extend
#print axioms capacity_slots
#print axioms opposite_slots
end BqLowerFamily

/- Source: BqSeedHelpers.lean; only its import lines removed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
open Finset SimpleGraph
namespace BqLowerFamily

def seedAdj (q : ℕ) (i : Fin (q+1)) (j : Fin (q+2)) : Prop :=
  ¬ ((i.val = 0 ∧ j.val = 0) ∨ (i.val = 0 ∧ j.val = 1) ∨
     (i.val = 1 ∧ j.val = 2) ∨ (i.val = 1 ∧ j.val = 3) ∨
     (i.val = 2 ∧ j.val = 4))

instance seedAdjDecidable (q : ℕ) : DecidableRel (seedAdj q) := fun _ _ => by
  unfold seedAdj
  infer_instance

def seedGraph (q : ℕ) : SimpleGraph (Fin (q+1) ⊕ Fin (q+2)) where
  Adj v w := match v,w with
    | .inl i,.inr j => seedAdj q i j
    | .inr j,.inl i => seedAdj q i j
    | _,_ => False
  symm := ⟨by intro v w; cases v <;> cases w <;> simp⟩
  loopless := ⟨by intro v; cases v <;> simp⟩

instance seedGraphDecidable (q : ℕ) : DecidableRel (seedGraph q).Adj := fun v w => by
  cases v <;> cases w <;> unfold seedGraph <;> infer_instance

def seedRowDegree (q : ℕ) (Q : Finset (Fin (q+2))) (i : Fin (q+1)) : ℕ :=
  (Q.filter fun j => seedAdj q i j).card

def seedColumnDegree (q : ℕ) (P : Finset (Fin (q+1))) (j : Fin (q+2)) : ℕ :=
  (P.filter fun i => seedAdj q i j).card

def missingPairs (q : ℕ) (hq : 4 ≤ q) : Finset (Fin (q+1) × Fin (q+2)) :=
  {(⟨0,by omega⟩,⟨0,by omega⟩), (⟨0,by omega⟩,⟨1,by omega⟩),
   (⟨1,by omega⟩,⟨2,by omega⟩), (⟨1,by omega⟩,⟨3,by omega⟩),
   (⟨2,by omega⟩,⟨4,by omega⟩)}

theorem missing_card (q : ℕ) (hq : 4 ≤ q) : (missingPairs q hq).card = 5 := by
  simp [missingPairs, Fin.ext_iff]

theorem missing_iff (q : ℕ) (hq : 4 ≤ q) (i : Fin (q+1)) (j : Fin (q+2)) :
    (i,j) ∈ missingPairs q hq ↔ ¬ seedAdj q i j := by
  simp only [missingPairs, mem_insert, mem_singleton, Prod.mk.injEq, Fin.ext_iff, seedAdj, not_not]

theorem missing_row_cap (q : ℕ) (hq : 4 ≤ q) (i : Fin (q+1)) :
    ((missingPairs q hq).filter fun x => x.1 = i).card ≤ 2 := by
  by_cases h0 : i.val = 0
  · simp [missingPairs, filter_insert, filter_singleton, Fin.ext_iff, -Fin.val_eq_zero_iff, h0]
  by_cases h1 : i.val = 1
  · simp [missingPairs, filter_insert, filter_singleton, Fin.ext_iff, -Fin.val_eq_zero_iff, h1]
  by_cases h2 : i.val = 2
  · simp [missingPairs, filter_insert, filter_singleton, Fin.ext_iff, -Fin.val_eq_zero_iff, h2]
  · have hn0 := Ne.symm h0
    have hn1 := Ne.symm h1
    have hn2 := Ne.symm h2
    simp [missingPairs, filter_insert, filter_singleton, Fin.ext_iff, -Fin.val_eq_zero_iff, hn0, hn1, hn2]

theorem missing_column_cap (q : ℕ) (hq : 4 ≤ q) (j : Fin (q+2)) :
    ((missingPairs q hq).filter fun x => x.2 = j).card ≤ 1 := by
  by_cases h0 : j.val = 0
  · simp [missingPairs, filter_insert, filter_singleton, Fin.ext_iff, -Fin.val_eq_zero_iff, h0]
  by_cases h1 : j.val = 1
  · simp [missingPairs, filter_insert, filter_singleton, Fin.ext_iff, -Fin.val_eq_zero_iff, h1]
  by_cases h2 : j.val = 2
  · simp [missingPairs, filter_insert, filter_singleton, Fin.ext_iff, -Fin.val_eq_zero_iff, h2]
  by_cases h3 : j.val = 3
  · simp [missingPairs, filter_insert, filter_singleton, Fin.ext_iff, -Fin.val_eq_zero_iff, h3]
  by_cases h4 : j.val = 4
  · simp [missingPairs, filter_insert, filter_singleton, Fin.ext_iff, -Fin.val_eq_zero_iff, h4]
  · have hn0 := Ne.symm h0
    have hn1 := Ne.symm h1
    have hn2 := Ne.symm h2
    have hn3 := Ne.symm h3
    have hn4 := Ne.symm h4
    simp [missingPairs, filter_insert, filter_singleton, Fin.ext_iff, -Fin.val_eq_zero_iff, hn0, hn1, hn2, hn3, hn4]

theorem row_degree_zero (q : ℕ) (hq : 4 ≤ q) :
    seedRowDegree q univ ⟨0,by omega⟩ = q := by
  have hset : (univ.filter fun j : Fin (q+2) => seedAdj q ⟨0,by omega⟩ j) =
      ((univ.erase ⟨0,by omega⟩).erase ⟨1,by omega⟩) := by
    ext j
    simp [seedAdj, Fin.ext_iff, -Fin.val_eq_zero_iff]; tauto
  unfold seedRowDegree
  rw [hset, card_erase_of_mem (by simp),
      card_erase_of_mem (by simp), card_univ, Fintype.card_fin]
  omega

theorem row_degree_one (q : ℕ) (hq : 4 ≤ q) :
    seedRowDegree q univ ⟨1,by omega⟩ = q := by
  have hset : (univ.filter fun j : Fin (q+2) => seedAdj q ⟨1,by omega⟩ j) =
      ((univ.erase ⟨2,by omega⟩).erase ⟨3,by omega⟩) := by
    ext j
    simp [seedAdj, Fin.ext_iff, -Fin.val_eq_zero_iff]; tauto
  unfold seedRowDegree
  rw [hset, card_erase_of_mem (by simp),
      card_erase_of_mem (by simp), card_univ, Fintype.card_fin]
  omega

#print axioms missing_card
#print axioms missing_row_cap
#print axioms missing_column_cap
#print axioms row_degree_zero
#print axioms row_degree_one
end BqLowerFamily

/- Source: BqSeedSupport-v1.lean; only its import lines removed. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
open Finset SimpleGraph
namespace BqLowerFamily

theorem no_complete_q_support (q : ℕ) (hq : 4 ≤ q)
    (P : Finset (Fin (q+1))) (Q : Finset (Fin (q+2)))
    (hp : P.card = q) (hqcard : Q.card = q)
    (hcomplete : ∀ i ∈ P, ∀ j ∈ Q, seedAdj q i j) : False := by
  have hpcomp : (univ \ P).card = 1 := by
    rw [card_sdiff_of_subset (subset_univ P), card_univ, Fintype.card_fin, hp]
    omega
  have hqcomp : (univ \ Q).card = 2 := by
    rw [card_sdiff_of_subset (subset_univ Q), card_univ, Fintype.card_fin, hqcard]
    omega
  obtain ⟨a, ha⟩ := card_eq_one.mp hpcomp
  obtain ⟨b,c,_hbc,hbc⟩ := card_eq_two.mp hqcomp
  let R := (missingPairs q hq).filter fun x => x.1 = a
  let Cb := (missingPairs q hq).filter fun x => x.2 = b
  let Cc := (missingPairs q hq).filter fun x => x.2 = c
  have hsub : missingPairs q hq ⊆ (R ∪ Cb) ∪ Cc := by
    intro x hx
    by_cases hxp : x.1 ∈ P
    · by_cases hxq : x.2 ∈ Q
      · exact ((missing_iff q hq x.1 x.2).mp hx
          (hcomplete x.1 hxp x.2 hxq)).elim
      · have hn : x.2 ∈ univ \ Q := mem_sdiff.mpr ⟨mem_univ _,hxq⟩
        have hbcx : x.2 = b ∨ x.2 = c := by simpa [hbc] using hn
        rcases hbcx with hb | hc
        · exact mem_union.mpr (Or.inl (mem_union.mpr
            (Or.inr (mem_filter.mpr ⟨hx,hb⟩))))
        · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hx,hc⟩))
    · have hn : x.1 ∈ univ \ P := mem_sdiff.mpr ⟨mem_univ _,hxp⟩
      have hax : x.1 = a := by simpa [ha] using hn
      exact mem_union.mpr (Or.inl (mem_union.mpr
        (Or.inl (mem_filter.mpr ⟨hx,hax⟩))))
  have hM := card_le_card hsub
  have hU1 := card_union_le R Cb
  have hU2 := card_union_le (R ∪ Cb) Cc
  have hR := missing_row_cap q hq a
  have hCb := missing_column_cap q hq b
  have hCc := missing_column_cap q hq c
  rw [missing_card] at hM
  change R.card ≤ 2 at hR
  change Cb.card ≤ 1 at hCb
  change Cc.card ≤ 1 at hCc
  omega

theorem required_row_neighbors (q : ℕ) (Q : Finset (Fin (q+2)))
    (i : Fin (q+1)) (hfull : seedRowDegree q univ i = q)
    (hlower : q ≤ seedRowDegree q Q i) :
    ∀ j, seedAdj q i j → j ∈ Q := by
  have hsub : Q.filter (seedAdj q i) ⊆ univ.filter (seedAdj q i) :=
    filter_subset_filter (seedAdj q i) (subset_univ Q)
  have hcard : (univ.filter (seedAdj q i)).card ≤
      (Q.filter (seedAdj q i)).card := by
    change seedRowDegree q univ i ≤ seedRowDegree q Q i
    rw [hfull]
    exact hlower
  have heq := eq_of_subset_of_card_le hsub hcard
  intro j hj
  have hmem : j ∈ univ.filter (seedAdj q i) :=
    mem_filter.mpr ⟨mem_univ _,hj⟩
  rw [← heq] at hmem
  exact (mem_filter.mp hmem).1

theorem seed_no_balanced_support (q : ℕ) (hq : 4 ≤ q)
    (P : Finset (Fin (q+1))) (Q : Finset (Fin (q+2)))
    (hne : P.Nonempty) (hbal : P.card = Q.card)
    (hrow : ∀ i ∈ P, q ≤ seedRowDegree q Q i) : False := by
  have hklo : q ≤ P.card := by
    obtain ⟨i,hi⟩ := hne
    have hr := hrow i hi
    have hc := card_filter_le Q (seedAdj q i)
    change seedRowDegree q Q i ≤ Q.card at hc
    omega
  have hkhi : P.card ≤ q+1 := by
    simpa using card_le_card (subset_univ P)
  by_cases hk : P.card = q
  · apply no_complete_q_support q hq P Q hk (by omega)
    intro i hi j hj
    have heq : Q.filter (seedAdj q i) = Q :=
      eq_of_subset_of_card_le (filter_subset _ Q) (by
        change Q.card ≤ seedRowDegree q Q i
        have hr := hrow i hi
        omega)
    have hmem : j ∈ Q.filter (seedAdj q i) := by rwa [heq]
    exact (mem_filter.mp hmem).2
  · have hk' : P.card = q+1 := by omega
    have hP : P = univ := eq_of_subset_of_card_le (subset_univ P) (by simpa using hk'.ge)
    have h0 : q ≤ seedRowDegree q Q ⟨0,by omega⟩ :=
      hrow ⟨0,by omega⟩ (by simp [hP])
    have h1 : q ≤ seedRowDegree q Q ⟨1,by omega⟩ :=
      hrow ⟨1,by omega⟩ (by simp [hP])
    have hQall : ∀ j : Fin (q+2), j ∈ Q := by
      intro j
      have hj : seedAdj q ⟨0,by omega⟩ j ∨ seedAdj q ⟨1,by omega⟩ j := by
        dsimp [seedAdj]
        omega
      rcases hj with hj0 | hj1
      · exact required_row_neighbors q Q ⟨0,by omega⟩ (row_degree_zero q hq) h0 j hj0
      · exact required_row_neighbors q Q ⟨1,by omega⟩ (row_degree_one q hq) h1 j hj1
    have hQ : Q = univ := by
      ext j
      simp only [mem_univ, iff_true]
      exact hQall j
    have hQc : Q.card = q+2 := by simp [hQ]
    omega

#print axioms no_complete_q_support
#print axioms required_row_neighbors
#print axioms seed_no_balanced_support
end BqLowerFamily

/- Source: BqSeedMatrix.lean; only its import lines removed. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
open Finset SimpleGraph
namespace BqLowerFamily
variable (q : ℕ)
def matrixRowDegree (F : Finset (Fin (q+1) × Fin (q+2))) (i : Fin (q+1)) : ℕ :=
  (F.filter fun x => x.1 = i).card

def matrixColumnDegree (F : Finset (Fin (q+1) × Fin (q+2))) (j : Fin (q+2)) : ℕ :=
  (F.filter fun x => x.2 = j).card

/-- Actual selected edges cannot have all nonzero row and column degrees equal to q. -/
theorem seed_no_regular_matrix (hq : 4 ≤ q) (F : Finset (Fin (q+1) × Fin (q+2)))
    (hne : F.Nonempty) (hsub : ∀ x ∈ F, seedAdj q x.1 x.2)
    (hrow : ∀ i, matrixRowDegree q F i = 0 ∨ matrixRowDegree q F i = q)
    (hcol : ∀ j, matrixColumnDegree q F j = 0 ∨ matrixColumnDegree q F j = q) : False := by
  let P := univ.filter fun i => 0 < matrixRowDegree q F i
  let Q := univ.filter fun j => 0 < matrixColumnDegree q F j
  have hP (i : Fin (q+1)) : i ∈ P ↔ 0 < matrixRowDegree q F i := by simp [P]
  have hQ (j : Fin (q+2)) : j ∈ Q ↔ 0 < matrixColumnDegree q F j := by simp [Q]
  have hP4 (i : Fin (q+1)) (hi : i ∈ P) : matrixRowDegree q F i = q :=
    (hrow i).resolve_left (Nat.ne_of_gt ((hP i).mp hi))
  have hQ4 (j : Fin (q+2)) (hj : j ∈ Q) : matrixColumnDegree q F j = q :=
    (hcol j).resolve_left (Nat.ne_of_gt ((hQ j).mp hj))
  have hFrow : F.card = ∑ i : Fin (q+1), matrixRowDegree q F i :=
    card_eq_sum_card_fiberwise (f := Prod.fst) (s := F) (t := univ) (by simp)
  have hFcol : F.card = ∑ j : Fin (q+2), matrixColumnDegree q F j :=
    card_eq_sum_card_fiberwise (f := Prod.snd) (s := F) (t := univ) (by simp)
  have hsumP : (∑ i : Fin (q+1), matrixRowDegree q F i) = q * P.card := by
    calc
      _ = ∑ i : Fin (q+1), if i ∈ P then q else 0 := by
        apply sum_congr rfl
        intro i _
        by_cases hi : i ∈ P
        · simp [hi, hP4 i hi]
        · have hz : matrixRowDegree q F i = 0 := by
            have hn := mt (hP i).mpr hi
            omega
          simp [hi, hz]
      _ = q * P.card := by simp [mul_comm]
  have hsumQ : (∑ j : Fin (q+2), matrixColumnDegree q F j) = q * Q.card := by
    calc
      _ = ∑ j : Fin (q+2), if j ∈ Q then q else 0 := by
        apply sum_congr rfl
        intro j _
        by_cases hj : j ∈ Q
        · simp [hj, hQ4 j hj]
        · have hz : matrixColumnDegree q F j = 0 := by
            have hn := mt (hQ j).mpr hj
            omega
          simp [hj, hz]
      _ = q * Q.card := by simp [mul_comm]
  have hbalance : P.card = Q.card := by nlinarith
  have hPne : P.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨x.1, (hP x.1).mpr ?_⟩
    exact card_pos.mpr ⟨x, mem_filter.mpr ⟨hx, rfl⟩⟩
  have hrowlower (i : Fin (q+1)) (hi : i ∈ P) : q ≤ seedRowDegree q Q i := by
    let T := F.filter fun x => x.1 = i
    have hcard : (T.image Prod.snd).card = T.card := by
      apply card_image_of_injOn
      intro x hx y hy hxy
      have hxi := (mem_filter.mp hx).2
      have hyi := (mem_filter.mp hy).2
      exact Prod.ext (hxi.trans hyi.symm) hxy
    have hsubset : T.image Prod.snd ⊆ Q.filter fun j => seedAdj q i j := by
      intro j hj
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hj
      obtain ⟨hxF, hxi⟩ := mem_filter.mp hx
      refine mem_filter.mpr ⟨(hQ x.2).mpr ?_, ?_⟩
      · exact card_pos.mpr ⟨x, mem_filter.mpr ⟨hxF, rfl⟩⟩
      · exact hxi ▸ hsub x hxF
    have hle := card_le_card hsubset
    rw [hcard] at hle
    change matrixRowDegree q F i ≤ seedRowDegree q Q i at hle
    rwa [hP4 i hi] at hle
  exact seed_no_balanced_support q hq P Q hPne hbalance hrowlower

theorem row_card_matrix (r : Fin (q+1) → Fin (q+2) → Prop) [∀ i j, Decidable (r i j)]
    (i : Fin (q+1)) :
    matrixRowDegree q (univ.filter fun x : Fin (q+1) × Fin (q+2) => r x.1 x.2) i =
      (univ.filter fun j => r i j).card := by
  unfold matrixRowDegree
  rw [filter_filter]
  have heq : (univ.filter fun x : Fin (q+1) × Fin (q+2) => r x.1 x.2 ∧ x.1 = i) =
      ({i} ×ˢ (univ.filter fun j => r i j)) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton]
    constructor
    · rintro ⟨hr, hi⟩
      exact ⟨hi, hi ▸ hr⟩
    · rintro ⟨hi, hr⟩
      exact ⟨hi ▸ hr, hi⟩
  rw [heq, card_product, card_singleton, one_mul]

theorem column_card_matrix (r : Fin (q+1) → Fin (q+2) → Prop) [∀ i j, Decidable (r i j)]
    (j : Fin (q+2)) :
    matrixColumnDegree q (univ.filter fun x : Fin (q+1) × Fin (q+2) => r x.1 x.2) j =
      (univ.filter fun i => r i j).card := by
  unfold matrixColumnDegree
  rw [filter_filter]
  have heq : (univ.filter fun x : Fin (q+1) × Fin (q+2) => r x.1 x.2 ∧ x.2 = j) =
      ((univ.filter fun i => r i j) ×ˢ {j}) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton]
    constructor
    · rintro ⟨hr, hj⟩
      exact ⟨hj ▸ hr, hj⟩
    · rintro ⟨hr, hj⟩
      exact ⟨hj ▸ hr, hj⟩
  rw [heq, card_product, card_singleton, mul_one]

theorem degree_left_matrix (K : SimpleGraph (Fin (q+1) ⊕ Fin (q+2))) [DecidableRel K.Adj]
    (hK : K ≤ seedGraph q) (i : Fin (q+1)) :
    K.degree (Sum.inl i) = (univ.filter fun j => K.Adj (Sum.inl i) (Sum.inr j)).card := by
  have hn : K.neighborFinset (Sum.inl i) =
      (univ.filter fun j => K.Adj (Sum.inl i) (Sum.inr j)).image Sum.inr := by
    ext v
    cases v with
    | inl i' =>
      have hnot : ¬ K.Adj (Sum.inl i) (Sum.inl i') := by
        intro h
        exact hK h
      simp [hnot]
    | inr j => simp
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hn,
    card_image_of_injective _ Sum.inr_injective]

theorem degree_right_matrix (K : SimpleGraph (Fin (q+1) ⊕ Fin (q+2))) [DecidableRel K.Adj]
    (hK : K ≤ seedGraph q) (j : Fin (q+2)) :
    K.degree (Sum.inr j) = (univ.filter fun i => K.Adj (Sum.inl i) (Sum.inr j)).card := by
  have hn : K.neighborFinset (Sum.inr j) =
      (univ.filter fun i => K.Adj (Sum.inl i) (Sum.inr j)).image Sum.inl := by
    ext v
    cases v with
    | inl i => simp [K.adj_comm]
    | inr j' =>
      have hnot : ¬ K.Adj (Sum.inr j) (Sum.inr j') := by
        intro h
        exact hK h
      simp [hnot]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hn,
    card_image_of_injective _ Sum.inl_injective]

/-- Literal arbitrary q-regular Subgraph absence for the actual all-q seed. -/
theorem seed_no_regular_subgraph (hq : 4 ≤ q) :
    ¬ ∃ H : (seedGraph q).Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q := by
  classical
  rintro ⟨H, hne, hregular⟩
  let F := univ.filter fun x : Fin (q+1) × Fin (q+2) => H.Adj (Sum.inl x.1) (Sum.inr x.2)
  have hleft (i : Fin (q+1)) : matrixRowDegree q F i = H.degree (Sum.inl i) := by
    dsimp [F]
    rw [row_card_matrix q (fun i j => H.Adj (Sum.inl i) (Sum.inr j)) i]
    exact (degree_left_matrix q H.spanningCoe H.spanningCoe_le i).symm.trans
      (SimpleGraph.Subgraph.degree_spanningCoe _)
  have hright (j : Fin (q+2)) : matrixColumnDegree q F j = H.degree (Sum.inr j) := by
    dsimp [F]
    rw [column_card_matrix q (fun i j => H.Adj (Sum.inl i) (Sum.inr j)) j]
    exact (degree_right_matrix q H.spanningCoe H.spanningCoe_le j).symm.trans
      (SimpleGraph.Subgraph.degree_spanningCoe _)
  have hdegrees (v : Fin (q+1) ⊕ Fin (q+2)) : H.degree v = 0 ∨ H.degree v = q := by
    by_cases hv : v ∈ H.verts
    · right
      exact (SimpleGraph.Subgraph.coe_degree H ⟨v, hv⟩).symm.trans (hregular.degree_eq _)
    · left
      exact SimpleGraph.Subgraph.degree_of_notMem_verts hv
  have hFne : F.Nonempty := by
    obtain ⟨v, hv⟩ := hne
    have hd : H.degree v = q :=
      (SimpleGraph.Subgraph.coe_degree H ⟨v, hv⟩).symm.trans (hregular.degree_eq _)
    obtain ⟨w, hvw⟩ := (SimpleGraph.Subgraph.degree_pos_iff_exists_adj).mp (by omega : 0 < H.degree v)
    have hg := H.adj_sub hvw
    cases v with
    | inl i =>
      cases w with
      | inl i' => exact hg.elim
      | inr j => exact ⟨(i, j), mem_filter.mpr ⟨mem_univ _, hvw⟩⟩
    | inr j =>
      cases w with
      | inl i => exact ⟨(i, j), mem_filter.mpr ⟨mem_univ _, hvw.symm⟩⟩
      | inr j' => exact hg.elim
  apply seed_no_regular_matrix q hq F hFne
  · intro x hx
    exact H.adj_sub (mem_filter.mp hx).2
  · intro i
    rw [hleft]
    exact hdegrees _
  · intro j
    rw [hright]
    exact hdegrees _


#print axioms seed_no_regular_matrix
#print axioms seed_no_regular_subgraph
end BqLowerFamily

/- Source: BqGood.lean; only its import lines removed. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open Finset SimpleGraph
namespace BqLowerFamily
variable {V : Type*} [DecidableEq V] [Fintype V]
variable (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] (N : Finset V)
/-- Strong actual-graph induction data; no extension-success assumption is present. -/
structure Good (A B : Finset V) : Prop where
  disjoint : Disjoint A B
  cover : A ∪ B = univ
  bipartite : G.IsBipartiteWith ↑A ↑B
  balance_left : A.card ≤ B.card + 1
  balance_right : B.card ≤ A.card + 1
  degree_bounds : ∀ v, q-1 ≤ G.degree v ∧ G.degree v ≤ 2*(q-1)
  edge_density : G.edgeFinset.card + ((q-1)^2-1) = (q-1) * Fintype.card V
  no_regular : NoRegular q G

theorem Good.swap {A B : Finset V} (h : Good q G A B) : Good q G B A where
  disjoint := h.disjoint.symm
  cover := by rw [union_comm, h.cover]
  bipartite := h.bipartite.symm
  balance_left := h.balance_right
  balance_right := h.balance_left
  degree_bounds := h.degree_bounds
  edge_density := h.edge_density
  no_regular := h.no_regular

/-- Once the actual selected neighbors are supplied, every graph invariant is preserved. -/
theorem extend_good_selected (hq : 4 ≤ q) {A B : Finset V} (h : Good q G A B)
    (hsmall : A.card ≤ B.card) (hNB : N ⊆ B) (hN : N.card = q-1)
    (hload : ∀ v ∈ N, G.degree v ≤ 2*(q-1)-1) :
    Good q (extendGraph G N) (insert none (A.image some)) (B.image some) := by
  have hAc : (insert none (A.image some)).card = A.card + 1 := by
    rw [card_insert_of_notMem (by simp), card_image_of_injective _ (Option.some_injective V)]
  have hBc : (B.image some).card = B.card :=
    card_image_of_injective _ (Option.some_injective V)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro x hxA hxB
    cases x with
    | none => simp at hxB
    | some v =>
      exact Finset.disjoint_left.mp h.disjoint (by simpa using hxA) (by simpa using hxB)
  · ext x
    cases x with
    | none => simp
    | some v =>
      have hv : v ∈ A ∪ B := by rw [h.cover]; exact mem_univ _
      simpa using hv
  · refine ⟨?_, ?_⟩
    · rw [disjoint_coe]
      apply Finset.disjoint_left.mpr
      intro x hxA hxB
      cases x with
      | none => simp at hxB
      | some v => exact Finset.disjoint_left.mp h.disjoint (by simpa using hxA) (by simpa using hxB)
    · intro x y hxy
      cases x with
      | none =>
        cases y with
        | none => exact hxy.elim
        | some v => exact Or.inl ⟨by simp, by simpa using hNB hxy⟩
      | some v =>
        cases y with
        | none => exact Or.inr ⟨by simpa using hNB hxy, by simp⟩
        | some w => simpa using h.bipartite.mem_of_adj hxy
  · rw [hAc, hBc]
    omega
  · rw [hAc, hBc]
    have := h.balance_right
    omega
  · intro x
    cases x with
    | none => simp [hN]; omega
    | some v =>
      rw [degree_some]
      have hd := h.degree_bounds v
      by_cases hv : v ∈ N
      · have hl := hload v hv
        simp [hv]
        omega
      · simp [hv]
        omega
  · rw [edges_extend, hN, Fintype.card_option]
    have := h.edge_density
    nlinarith
  · exact noRegular_extend G N q (by omega) hN h.no_regular


/-- The required neighbor CARDINALITY follows from actual shore degree sums. -/
theorem eligible_card (hq : 4 ≤ q) {A B : Finset V}
    (h : Good q G A B) (hsmall : A.card ≤ B.card) :
    q-1 ≤ (B.filter fun v => G.degree v ≤ 2*(q-1)-1).card := by
  have hcard : A.card+B.card = Fintype.card V := by
    rw [← card_union_of_disjoint h.disjoint, h.cover, card_univ]
  have hdensity : G.edgeFinset.card + ((q-1)^2-1) = (q-1)*(A.card+B.card) := by
    rw [hcard]
    exact h.edge_density
  have hcapacity : (∑ v ∈ B, (2*(q-1)-G.degree v))+G.edgeFinset.card =
      2*(q-1)*B.card := by
    calc
      _ = (∑ v ∈ B, (2*(q-1)-G.degree v)) + ∑ v ∈ B, G.degree v := by
        rw [SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' h.bipartite]
      _ = ∑ _v ∈ B, 2*(q-1) := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro v _
        exact Nat.sub_add_cancel (h.degree_bounds v).2
      _ = 2*(q-1)*B.card := by simp [mul_comm]
  have hcap := opposite_slots (q-1) A.card B.card G.edgeFinset.card
    ((q-1)^2-1) (∑ v ∈ B, (2*(q-1)-G.degree v)) hsmall hdensity hcapacity
  apply capacity_slots (q-1) (by omega) B (fun v => G.degree v)
    (fun v _ => h.degree_bounds v)
  simpa [pow_two] using hcap

#print axioms Good.swap
#print axioms extend_good_selected
#print axioms eligible_card
end BqLowerFamily

/- Source: BqLeastLabels.lean; only its import lines removed. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
open Finset SimpleGraph
namespace BqLowerFamily
variable {V : Type*}

def leastLabels (r : ℕ) (S : Finset V) (label : V → ℕ) : Finset ℕ :=
  (((S.image label).sort (· ≤ ·)).take r).toFinset

def leastNeighbors (r : ℕ) (S : Finset V) (label : V → ℕ) : Finset V :=
  S.filter fun v => label v ∈ leastLabels r S label

theorem leastLabels_subset (r : ℕ) (S : Finset V) (label : V → ℕ) :
    leastLabels r S label ⊆ S.image label := by
  intro x hx
  have ht : x ∈ ((S.image label).sort (· ≤ ·)).take r := by
    simpa [leastLabels] using hx
  have hsort := List.mem_of_mem_take ht
  exact (mem_sort (· ≤ ·)).mp hsort

theorem leastLabels_card (r : ℕ) (S : Finset V) (label : V → ℕ)
    (hinj : Function.Injective label) (hcard : r ≤ S.card) :
    (leastLabels r S label).card = r := by
  have hnodup := ((S.image label).sort_nodup (· ≤ ·)).take (i := r)
  unfold leastLabels
  rw [List.toFinset_card_of_nodup hnodup, List.length_take,
      length_sort, card_image_of_injective _ hinj, Nat.min_eq_left hcard]

theorem leastNeighbors_image (r : ℕ) (S : Finset V) (label : V → ℕ) :
    (leastNeighbors r S label).image label = leastLabels r S label := by
  ext x
  constructor
  · intro hx
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hx
    exact (mem_filter.mp hv).2
  · intro hx
    have hxs := leastLabels_subset r S label hx
    obtain ⟨v,hv,hvx⟩ := mem_image.mp hxs
    exact mem_image.mpr ⟨v,mem_filter.mpr ⟨hv,hvx ▸ hx⟩,hvx⟩

theorem leastNeighbors_card (r : ℕ) (S : Finset V) (label : V → ℕ)
    (hinj : Function.Injective label) (hcard : r ≤ S.card) :
    (leastNeighbors r S label).card = r := by
  rw [← card_image_of_injective _ hinj, leastNeighbors_image]
  exact leastLabels_card r S label hinj hcard

theorem leastNeighbors_le_omitted (r : ℕ) (S : Finset V) (label : V → ℕ)
    (v w : V) (hv : v ∈ leastNeighbors r S label) (hw : w ∈ S)
    (hwn : w ∉ leastNeighbors r S label) : label v ≤ label w := by
  let L := (S.image label).sort (· ≤ ·)
  have hvT : label v ∈ L.take r := by simpa [leastNeighbors,leastLabels,L] using (mem_filter.mp hv).2
  have hvL : label v ∈ L := List.mem_of_mem_take hvT
  have hwL : label w ∈ L := (mem_sort (· ≤ ·)).mpr (mem_image.mpr ⟨w,hw,rfl⟩)
  have hwT : label w ∉ L.take r := by
    intro ht
    apply hwn
    exact mem_filter.mpr ⟨hw,by simpa [leastLabels,L] using ht⟩
  have hvi := (List.mem_take_iff_idxOf_lt hvL).mp hvT
  have hwi : r ≤ L.idxOf (label w) := by
    have hn := mt (List.mem_take_iff_idxOf_lt hwL).mpr hwT
    omega
  have hiv := List.idxOf_lt_length_of_mem hvL
  have hiw := List.idxOf_lt_length_of_mem hwL
  have hsort : L.Pairwise (· ≤ ·) := (S.image label).pairwise_sort (· ≤ ·)
  have hle : L.get ⟨L.idxOf (label v),hiv⟩ ≤ L.get ⟨L.idxOf (label w),hiw⟩ :=
    hsort.rel_get_of_le (by change L.idxOf (label v) ≤ L.idxOf (label w); omega)
  simpa only [List.idxOf_get] using hle

#print axioms leastLabels_subset
#print axioms leastLabels_card
#print axioms leastNeighbors_card
#print axioms leastNeighbors_le_omitted
end BqLowerFamily

/- Source: BqLabel-v1.lean; only its import lines removed. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
open Finset SimpleGraph
namespace BqLowerFamily

structure Labeling (V : Type*) [Fintype V] where
  label : V → ℕ
  injective : Function.Injective label
  bounded : ∀ v, label v < Fintype.card V

def seedLabel (q : ℕ) : (Fin (q+1) ⊕ Fin (q+2)) → ℕ
  | .inl i => i.val
  | .inr j => q+1+j.val

def seedLabeling (q : ℕ) : Labeling (Fin (q+1) ⊕ Fin (q+2)) where
  label := seedLabel q
  injective := by
    intro x y hxy
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (Fin.ext hxy)
      | inr j =>
        dsimp [seedLabel] at hxy
        have hi := i.isLt
        omega
    | inr i =>
      cases y with
      | inl j =>
        dsimp [seedLabel] at hxy
        have hj := j.isLt
        omega
      | inr j =>
        dsimp [seedLabel] at hxy
        exact congrArg Sum.inr (Fin.ext (Nat.add_left_cancel hxy))
  bounded := by
    intro x
    simp only [Fintype.card_sum,Fintype.card_fin]
    cases x with
    | inl i =>
      dsimp [seedLabel]
      have hi := i.isLt
      omega
    | inr j =>
      dsimp [seedLabel]
      have hj := j.isLt
      omega

def Labeling.extend {V : Type*} [Fintype V] (L : Labeling V) : Labeling (Option V) where
  label := fun x => match x with
    | none => Fintype.card V
    | some v => L.label v
  injective := by
    intro x y hxy
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some v =>
        have hv := L.bounded v
        change Fintype.card V = L.label v at hxy
        omega
    | some v =>
      cases y with
      | none =>
        have hv := L.bounded v
        change L.label v = Fintype.card V at hxy
        omega
      | some w => exact congrArg some (L.injective hxy)
  bounded := by
    intro x
    rw [Fintype.card_option]
    cases x with
    | none => exact Nat.lt_succ_self _
    | some v => exact (L.bounded v).trans (Nat.lt_succ_self _)

theorem Labeling.image_range {V : Type*} [Fintype V] (L : Labeling V) :
    univ.image L.label = range (Fintype.card V) := by
  have hsub : univ.image L.label ⊆ range (Fintype.card V) := by
    intro k hk
    obtain ⟨v,_hv,rfl⟩ := mem_image.mp hk
    exact mem_range.mpr (L.bounded v)
  apply eq_of_subset_of_card_le hsub
  rw [card_range,card_image_of_injective _ L.injective,card_univ]

#print axioms seedLabeling
#print axioms Labeling.extend
#print axioms Labeling.image_range
end BqLowerFamily

/- Source: BqSeedInvariant.lean; only its import lines removed. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
open Finset SimpleGraph
namespace BqLowerFamily

def seedA (q : ℕ) : Finset (Fin (q+1) ⊕ Fin (q+2)) := univ.image Sum.inl
def seedB (q : ℕ) : Finset (Fin (q+1) ⊕ Fin (q+2)) := univ.image Sum.inr
def seedMatrix (q : ℕ) : Finset (Fin (q+1) × Fin (q+2)) :=
  univ.filter fun x => seedAdj q x.1 x.2

theorem seedA_card (q : ℕ) : (seedA q).card = q+1 := by
  rw [seedA,card_image_of_injective _ Sum.inl_injective,card_univ,Fintype.card_fin]
theorem seedB_card (q : ℕ) : (seedB q).card = q+2 := by
  rw [seedB,card_image_of_injective _ Sum.inr_injective,card_univ,Fintype.card_fin]

theorem seed_disjoint (q : ℕ) : Disjoint (seedA q) (seedB q) := by
  apply Finset.disjoint_left.mpr
  intro x hxA hxB
  cases x <;> simp_all [seedA,seedB]

theorem seed_cover (q : ℕ) : seedA q ∪ seedB q = univ := by
  ext x
  cases x <;> simp [seedA,seedB]

theorem seed_bipartite (q : ℕ) :
    (seedGraph q).IsBipartiteWith ↑(seedA q) ↑(seedB q) := by
  refine ⟨?_,?_⟩
  · rw [disjoint_coe]
    exact seed_disjoint q
  · intro x y hxy
    cases x <;> cases y <;> simp_all [seedGraph,seedA,seedB]

theorem missingPairs_filter (q : ℕ) (hq : 4 ≤ q) :
    missingPairs q hq = univ.filter fun x => ¬ seedAdj q x.1 x.2 := by
  ext x
  simp only [mem_filter,mem_univ,true_and]
  exact missing_iff q hq x.1 x.2

theorem seed_row_bounds (q : ℕ) (hq : 4 ≤ q) (i : Fin (q+1)) :
    q ≤ seedRowDegree q univ i ∧ seedRowDegree q univ i ≤ q+2 := by
  have hc : seedRowDegree q univ i + matrixRowDegree q (missingPairs q hq) i = q+2 := by
    rw [missingPairs_filter q hq,row_card_matrix q (fun a b => ¬ seedAdj q a b) i]
    change (univ.filter (seedAdj q i)).card + (univ.filter fun j => ¬ seedAdj q i j).card = q+2
    rw [card_filter_add_card_filter_not,card_univ,Fintype.card_fin]
  have hcap := missing_row_cap q hq i
  change matrixRowDegree q (missingPairs q hq) i ≤ 2 at hcap
  omega

theorem seed_column_bounds (q : ℕ) (hq : 4 ≤ q) (j : Fin (q+2)) :
    q ≤ seedColumnDegree q univ j ∧ seedColumnDegree q univ j ≤ q+1 := by
  have hc : seedColumnDegree q univ j + matrixColumnDegree q (missingPairs q hq) j = q+1 := by
    rw [missingPairs_filter q hq,column_card_matrix q (fun a b => ¬ seedAdj q a b) j]
    change (univ.filter fun i => seedAdj q i j).card + (univ.filter fun i => ¬ seedAdj q i j).card = q+1
    rw [card_filter_add_card_filter_not,card_univ,Fintype.card_fin]
  have hcap := missing_column_cap q hq j
  change matrixColumnDegree q (missingPairs q hq) j ≤ 1 at hcap
  omega

theorem seed_degree_bounds (q : ℕ) (hq : 4 ≤ q) :
    ∀ v, q-1 ≤ (seedGraph q).degree v ∧ (seedGraph q).degree v ≤ 2*(q-1) := by
  intro v
  cases v with
  | inl i =>
    have heq : (seedGraph q).degree (.inl i) = seedRowDegree q univ i :=
      degree_left_matrix q (seedGraph q) le_rfl i
    rw [heq]
    have hb := seed_row_bounds q hq i
    omega
  | inr j =>
    have heq : (seedGraph q).degree (.inr j) = seedColumnDegree q univ j :=
      degree_right_matrix q (seedGraph q) le_rfl j
    rw [heq]
    have hb := seed_column_bounds q hq j
    omega

theorem seed_graph_matrix_card (q : ℕ) :
    (seedGraph q).edgeFinset.card = (seedMatrix q).card := by
  have hFrow : (seedMatrix q).card = ∑ i : Fin (q+1), matrixRowDegree q (seedMatrix q) i :=
    card_eq_sum_card_fiberwise (f := Prod.fst) (s := seedMatrix q) (t := univ) (by simp)
  rw [← SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges (seed_bipartite q)]
  rw [seedA,sum_image (by intro x _ y _ h; exact Sum.inl_injective h)]
  rw [hFrow]
  apply sum_congr rfl
  intro i _
  rw [seedMatrix,row_card_matrix]
  exact degree_left_matrix q (seedGraph q) le_rfl i

theorem seed_edge_count (q : ℕ) (hq : 4 ≤ q) :
    (seedGraph q).edgeFinset.card + 5 = (q+1)*(q+2) := by
  rw [seed_graph_matrix_card,← missing_card q hq,missingPairs_filter q hq]
  unfold seedMatrix
  rw [card_filter_add_card_filter_not,card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_fin]

theorem seed_good (q : ℕ) (hq : 4 ≤ q) :
    Good q (seedGraph q) (seedA q) (seedB q) := by
  refine ⟨seed_disjoint q,seed_cover q,seed_bipartite q,?_,?_,
    seed_degree_bounds q hq,?_,seed_no_regular_subgraph q hq⟩
  · rw [seedA_card,seedB_card]
    omega
  · rw [seedA_card,seedB_card]
  · rw [Fintype.card_sum,Fintype.card_fin,Fintype.card_fin]
    have he := seed_edge_count q hq
    have hr : q-1+1=q := by omega
    have hs : 1 ≤ (q-1)^2 := by nlinarith
    have hc := Nat.sub_add_cancel hs
    nlinarith

#print axioms seed_degree_bounds
#print axioms seed_edge_count
#print axioms seed_good
end BqLowerFamily

/- Source: BqStep.lean; only its import lines removed. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 4000
open Finset SimpleGraph
namespace BqLowerFamily
variable {V : Type*} [Fintype V] [DecidableEq V]

def nextNeighbors (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (L : Labeling V) : Finset V :=
  let opposite := if A.card ≤ B.card then B else A
  leastNeighbors (q-1) (opposite.filter fun v => G.degree v ≤ 2*(q-1)-1) L.label

def nextA (A B : Finset V) : Finset (Option V) :=
  if A.card ≤ B.card then insert none (A.image some) else A.image some

def nextB (A B : Finset V) : Finset (Option V) :=
  if A.card ≤ B.card then B.image some else insert none (B.image some)

theorem literalNext_good (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (L : Labeling V) (hq : 4 ≤ q) (h : Good q G A B) :
    Good q (extendGraph G (nextNeighbors q G A B L)) (nextA A B) (nextB A B) := by
  by_cases hsmall : A.card ≤ B.card
  · let S := B.filter fun v => G.degree v ≤ 2*(q-1)-1
    have hN : nextNeighbors q G A B L = leastNeighbors (q-1) S L.label := by
      simp [nextNeighbors,hsmall,S]
    have hNS : nextNeighbors q G A B L ⊆ S := by
      rw [hN]
      exact filter_subset _ S
    have hNB : nextNeighbors q G A B L ⊆ B := by
      intro v hv
      exact (mem_filter.mp (hNS hv)).1
    have hNc : (nextNeighbors q G A B L).card = q-1 := by
      rw [hN]
      exact leastNeighbors_card (q-1) S L.label L.injective (eligible_card q G hq h hsmall)
    have hload : ∀ v ∈ nextNeighbors q G A B L, G.degree v ≤ 2*(q-1)-1 := by
      intro v hv
      exact (mem_filter.mp (hNS hv)).2
    have hn := extend_good_selected q G (nextNeighbors q G A B L) hq h hsmall hNB hNc hload
    simpa [nextA,nextB,hsmall] using hn
  · have hsmall' : B.card ≤ A.card := by omega
    let S := A.filter fun v => G.degree v ≤ 2*(q-1)-1
    have hN : nextNeighbors q G A B L = leastNeighbors (q-1) S L.label := by
      simp [nextNeighbors,hsmall,S]
    have hNS : nextNeighbors q G A B L ⊆ S := by
      rw [hN]
      exact filter_subset _ S
    have hNA : nextNeighbors q G A B L ⊆ A := by
      intro v hv
      exact (mem_filter.mp (hNS hv)).1
    have hNc : (nextNeighbors q G A B L).card = q-1 := by
      rw [hN]
      exact leastNeighbors_card (q-1) S L.label L.injective (eligible_card q G hq h.swap hsmall')
    have hload : ∀ v ∈ nextNeighbors q G A B L, G.degree v ≤ 2*(q-1)-1 := by
      intro v hv
      exact (mem_filter.mp (hNS hv)).2
    have hn := extend_good_selected q G (nextNeighbors q G A B L) hq h.swap hsmall' hNA hNc hload
    simpa [nextA,nextB,hsmall] using hn.swap

theorem nextNeighbors_card (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (L : Labeling V) (hq : 4 ≤ q) (h : Good q G A B) :
    (nextNeighbors q G A B L).card = q-1 := by
  by_cases hsmall : A.card ≤ B.card
  · simpa [nextNeighbors,hsmall] using
      leastNeighbors_card (q-1) (B.filter fun v => G.degree v ≤ 2*(q-1)-1)
        L.label L.injective (eligible_card q G hq h hsmall)
  · have hrev : B.card ≤ A.card := by omega
    simpa [nextNeighbors,hsmall] using
      leastNeighbors_card (q-1) (A.filter fun v => G.degree v ≤ 2*(q-1)-1)
        L.label L.injective (eligible_card q G hq h.swap hrev)

omit [DecidableEq V] in
theorem nextNeighbors_least (q : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (L : Labeling V) (v w : V)
    (hv : v ∈ nextNeighbors q G A B L)
    (hw : w ∈ (if A.card ≤ B.card then B else A).filter
      fun x => G.degree x ≤ 2*(q-1)-1)
    (hwn : w ∉ nextNeighbors q G A B L) : L.label v ≤ L.label w := by
  exact leastNeighbors_le_omitted (q-1)
    ((if A.card ≤ B.card then B else A).filter fun x => G.degree x ≤ 2*(q-1)-1)
    L.label v w hv hw hwn

omit [DecidableEq V] in
@[simp] theorem extend_label_old (L : Labeling V) (v : V) :
    L.extend.label (some v) = L.label v := rfl
omit [DecidableEq V] in
@[simp] theorem extend_label_new (L : Labeling V) :
    L.extend.label none = Fintype.card V := rfl

#print axioms literalNext_good
#print axioms nextNeighbors_card
#print axioms nextNeighbors_least
end BqLowerFamily

/- Source: BqLowerFamily.lean; only its import lines removed. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
open Finset SimpleGraph
namespace BqLowerFamily

def HasLabeledGood (q n : ℕ) : Prop :=
  ∃ (W : Type) (wf : Fintype W) (wd : DecidableEq W),
    letI := wf
    letI := wd
    ∃ (K : SimpleGraph W) (kd : DecidableRel K.Adj),
      letI := kd
      Fintype.card W = n ∧ ∃ (_L : Labeling W) (A B : Finset W), Good q K A B

theorem hasLabeledGood_seed (q : ℕ) (hq : 4 ≤ q) : HasLabeledGood q (2*q+3) := by
  refine ⟨Fin (q+1) ⊕ Fin (q+2),inferInstance,inferInstance,
    seedGraph q,inferInstance,?_,seedLabeling q,seedA q,seedB q,seed_good q hq⟩
  simp only [Fintype.card_sum,Fintype.card_fin]
  omega

theorem hasLabeledGood_succ (q : ℕ) (hq : 4 ≤ q) (n : ℕ)
    (h : HasLabeledGood q n) : HasLabeledGood q (n+1) := by
  rcases h with ⟨W,wf,wd,h⟩
  let : Fintype W := wf
  let : DecidableEq W := wd
  rcases h with ⟨K,kd,hcard,L,A,B,hgood⟩
  let : DecidableRel K.Adj := kd
  let N := nextNeighbors q K A B L
  have hnext := literalNext_good q K A B L hq hgood
  refine ⟨Option W,inferInstance,inferInstance,extendGraph K N,inferInstance,?_,
    L.extend,nextA A B,nextB A B,hnext⟩
  rw [Fintype.card_option,hcard]

theorem hasLabeledGood_all_orders (q : ℕ) (hq : 4 ≤ q) (n : ℕ)
    (hn : 2*q+3 ≤ n) : HasLabeledGood q n := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction t with
  | zero => simpa using hasLabeledGood_seed q hq
  | succ t ih =>
    have hs := hasLabeledGood_succ q hq (2*q+3+t) ih
    simpa [Nat.add_assoc] using hs

def LowerEndpoint : Prop :=
  ∀ (q : ℕ), 4 ≤ q → ∀ (n : ℕ), 2*q+3 ≤ n →
    ∃ (V : Type) (vf : Fintype V) (vd : DecidableEq V),
      letI := vf
      letI := vd
      ∃ (G : SimpleGraph V) (gd : DecidableRel G.Adj),
        letI := gd
        Fintype.card V = n ∧ G.IsBipartite ∧
          (∀ v, q-1 ≤ G.degree v) ∧ G.maxDegree ≤ 2*q-2 ∧
          G.edgeFinset.card + ((q-1)^2-1) = (q-1)*n ∧
          ¬ (∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q)

theorem all_orders (q : ℕ) (hq : 4 ≤ q) (n : ℕ) (hn : 2*q+3 ≤ n) :
    ∃ (V : Type) (vf : Fintype V) (vd : DecidableEq V),
      letI := vf
      letI := vd
      ∃ (G : SimpleGraph V) (gd : DecidableRel G.Adj),
        letI := gd
        Fintype.card V = n ∧ G.IsBipartite ∧
          (∀ v, q-1 ≤ G.degree v) ∧ G.maxDegree ≤ 2*q-2 ∧
          G.edgeFinset.card + ((q-1)^2-1) = (q-1)*n ∧
          ¬ (∃ H : G.Subgraph, H.verts.Nonempty ∧ H.coe.IsRegularOfDegree q) := by
  rcases hasLabeledGood_all_orders q hq n hn with ⟨W,wf,wd,h⟩
  let : Fintype W := wf
  let : DecidableEq W := wd
  rcases h with ⟨K,kd,hcard,_L,A,B,hgood⟩
  let : DecidableRel K.Adj := kd
  refine ⟨W,wf,wd,K,kd,hcard,hgood.bipartite.isBipartite,
    fun v => (hgood.degree_bounds v).1,?_,?_,hgood.no_regular⟩
  · have hmax := K.maxDegree_le_of_forall_degree_le (2*(q-1))
      (fun v => (hgood.degree_bounds v).2)
    have heq : 2*(q-1)=2*q-2 := by omega
    rwa [heq] at hmax
  · rw [← hcard]
    exact hgood.edge_density

theorem lowerEndpoint : LowerEndpoint := by
  intro q hq n hn
  exact all_orders q hq n hn

#print LowerEndpoint
#check all_orders
#print axioms hasLabeledGood_seed
#print axioms hasLabeledGood_succ
#print axioms hasLabeledGood_all_orders
#print axioms all_orders
#print axioms lowerEndpoint
end BqLowerFamily

/- Fresh complete declared-name type/axiom audit; no opaque foreign proof import. -/
#check BqLowerFamily.extendGraph
#print axioms BqLowerFamily.extendGraph
#check BqLowerFamily.extendGraphDecidable
#print axioms BqLowerFamily.extendGraphDecidable
#check BqLowerFamily.degree_none
#print axioms BqLowerFamily.degree_none
#check BqLowerFamily.degree_some
#print axioms BqLowerFamily.degree_some
#check BqLowerFamily.edges_extend
#print axioms BqLowerFamily.edges_extend
#check BqLowerFamily.finiteSubgraphLocallyFinite
#print axioms BqLowerFamily.finiteSubgraphLocallyFinite
#check BqLowerFamily.NoRegular
#print axioms BqLowerFamily.NoRegular
#check BqLowerFamily.noRegular_extend
#print axioms BqLowerFamily.noRegular_extend
#check BqLowerFamily.capacity_slots
#print axioms BqLowerFamily.capacity_slots
#check BqLowerFamily.opposite_slots
#print axioms BqLowerFamily.opposite_slots
#check BqLowerFamily.seedAdj
#print axioms BqLowerFamily.seedAdj
#check BqLowerFamily.seedAdjDecidable
#print axioms BqLowerFamily.seedAdjDecidable
#check BqLowerFamily.seedGraph
#print axioms BqLowerFamily.seedGraph
#check BqLowerFamily.seedGraphDecidable
#print axioms BqLowerFamily.seedGraphDecidable
#check BqLowerFamily.seedRowDegree
#print axioms BqLowerFamily.seedRowDegree
#check BqLowerFamily.seedColumnDegree
#print axioms BqLowerFamily.seedColumnDegree
#check BqLowerFamily.missingPairs
#print axioms BqLowerFamily.missingPairs
#check BqLowerFamily.missing_card
#print axioms BqLowerFamily.missing_card
#check BqLowerFamily.missing_iff
#print axioms BqLowerFamily.missing_iff
#check BqLowerFamily.missing_row_cap
#print axioms BqLowerFamily.missing_row_cap
#check BqLowerFamily.missing_column_cap
#print axioms BqLowerFamily.missing_column_cap
#check BqLowerFamily.row_degree_zero
#print axioms BqLowerFamily.row_degree_zero
#check BqLowerFamily.row_degree_one
#print axioms BqLowerFamily.row_degree_one
#check BqLowerFamily.no_complete_q_support
#print axioms BqLowerFamily.no_complete_q_support
#check BqLowerFamily.required_row_neighbors
#print axioms BqLowerFamily.required_row_neighbors
#check BqLowerFamily.seed_no_balanced_support
#print axioms BqLowerFamily.seed_no_balanced_support
#check BqLowerFamily.matrixRowDegree
#print axioms BqLowerFamily.matrixRowDegree
#check BqLowerFamily.matrixColumnDegree
#print axioms BqLowerFamily.matrixColumnDegree
#check BqLowerFamily.seed_no_regular_matrix
#print axioms BqLowerFamily.seed_no_regular_matrix
#check BqLowerFamily.row_card_matrix
#print axioms BqLowerFamily.row_card_matrix
#check BqLowerFamily.column_card_matrix
#print axioms BqLowerFamily.column_card_matrix
#check BqLowerFamily.degree_left_matrix
#print axioms BqLowerFamily.degree_left_matrix
#check BqLowerFamily.degree_right_matrix
#print axioms BqLowerFamily.degree_right_matrix
#check BqLowerFamily.seed_no_regular_subgraph
#print axioms BqLowerFamily.seed_no_regular_subgraph
#check BqLowerFamily.Good
#print axioms BqLowerFamily.Good
#check BqLowerFamily.Good.swap
#print axioms BqLowerFamily.Good.swap
#check BqLowerFamily.extend_good_selected
#print axioms BqLowerFamily.extend_good_selected
#check BqLowerFamily.eligible_card
#print axioms BqLowerFamily.eligible_card
#check BqLowerFamily.leastLabels
#print axioms BqLowerFamily.leastLabels
#check BqLowerFamily.leastNeighbors
#print axioms BqLowerFamily.leastNeighbors
#check BqLowerFamily.leastLabels_subset
#print axioms BqLowerFamily.leastLabels_subset
#check BqLowerFamily.leastLabels_card
#print axioms BqLowerFamily.leastLabels_card
#check BqLowerFamily.leastNeighbors_image
#print axioms BqLowerFamily.leastNeighbors_image
#check BqLowerFamily.leastNeighbors_card
#print axioms BqLowerFamily.leastNeighbors_card
#check BqLowerFamily.leastNeighbors_le_omitted
#print axioms BqLowerFamily.leastNeighbors_le_omitted
#check BqLowerFamily.Labeling
#print axioms BqLowerFamily.Labeling
#check BqLowerFamily.seedLabel
#print axioms BqLowerFamily.seedLabel
#check BqLowerFamily.seedLabeling
#print axioms BqLowerFamily.seedLabeling
#check BqLowerFamily.Labeling.extend
#print axioms BqLowerFamily.Labeling.extend
#check BqLowerFamily.Labeling.image_range
#print axioms BqLowerFamily.Labeling.image_range
#check BqLowerFamily.seedA
#print axioms BqLowerFamily.seedA
#check BqLowerFamily.seedB
#print axioms BqLowerFamily.seedB
#check BqLowerFamily.seedMatrix
#print axioms BqLowerFamily.seedMatrix
#check BqLowerFamily.seedA_card
#print axioms BqLowerFamily.seedA_card
#check BqLowerFamily.seedB_card
#print axioms BqLowerFamily.seedB_card
#check BqLowerFamily.seed_disjoint
#print axioms BqLowerFamily.seed_disjoint
#check BqLowerFamily.seed_cover
#print axioms BqLowerFamily.seed_cover
#check BqLowerFamily.seed_bipartite
#print axioms BqLowerFamily.seed_bipartite
#check BqLowerFamily.missingPairs_filter
#print axioms BqLowerFamily.missingPairs_filter
#check BqLowerFamily.seed_row_bounds
#print axioms BqLowerFamily.seed_row_bounds
#check BqLowerFamily.seed_column_bounds
#print axioms BqLowerFamily.seed_column_bounds
#check BqLowerFamily.seed_degree_bounds
#print axioms BqLowerFamily.seed_degree_bounds
#check BqLowerFamily.seed_graph_matrix_card
#print axioms BqLowerFamily.seed_graph_matrix_card
#check BqLowerFamily.seed_edge_count
#print axioms BqLowerFamily.seed_edge_count
#check BqLowerFamily.seed_good
#print axioms BqLowerFamily.seed_good
#check BqLowerFamily.nextNeighbors
#print axioms BqLowerFamily.nextNeighbors
#check BqLowerFamily.nextA
#print axioms BqLowerFamily.nextA
#check BqLowerFamily.nextB
#print axioms BqLowerFamily.nextB
#check BqLowerFamily.literalNext_good
#print axioms BqLowerFamily.literalNext_good
#check BqLowerFamily.nextNeighbors_card
#print axioms BqLowerFamily.nextNeighbors_card
#check BqLowerFamily.nextNeighbors_least
#print axioms BqLowerFamily.nextNeighbors_least
#check BqLowerFamily.extend_label_old
#print axioms BqLowerFamily.extend_label_old
#check BqLowerFamily.extend_label_new
#print axioms BqLowerFamily.extend_label_new
#check BqLowerFamily.HasLabeledGood
#print axioms BqLowerFamily.HasLabeledGood
#check BqLowerFamily.hasLabeledGood_seed
#print axioms BqLowerFamily.hasLabeledGood_seed
#check BqLowerFamily.hasLabeledGood_succ
#print axioms BqLowerFamily.hasLabeledGood_succ
#check BqLowerFamily.hasLabeledGood_all_orders
#print axioms BqLowerFamily.hasLabeledGood_all_orders
#check BqLowerFamily.LowerEndpoint
#print axioms BqLowerFamily.LowerEndpoint
#check BqLowerFamily.all_orders
#print axioms BqLowerFamily.all_orders
#check BqLowerFamily.lowerEndpoint
#print axioms BqLowerFamily.lowerEndpoint
#print BqLowerFamily.NoRegular
#print BqLowerFamily.Good
#print BqLowerFamily.Labeling
#print BqLowerFamily.HasLabeledGood
#print BqLowerFamily.LowerEndpoint
#print BqLowerFamily.seedAdj
#print BqLowerFamily.seedGraph
#print BqLowerFamily.leastLabels
#print BqLowerFamily.leastNeighbors
#print BqLowerFamily.Labeling.extend
#print BqLowerFamily.nextNeighbors
#print BqLowerFamily.nextA
#print BqLowerFamily.nextB
#print BqLowerFamily.extendGraph
set_option pp.explicit true in
#check BqLowerFamily.all_orders
set_option pp.explicit true in
#check BqLowerFamily.lowerEndpoint

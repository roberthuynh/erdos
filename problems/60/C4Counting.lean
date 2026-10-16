import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! Ordinary unlabelled C4s represented by their four unordered edges.
Extra ambient edges, including diagonals, are allowed. Rotations and reflections
have the same edge set; different cycles on the same four vertices remain distinct.
This module is a counting foundation, not the #60 headline theorem. -/
namespace Erdos60.Counting
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges traversed in order a,b,c,d,a. -/
def fourEdges (a b c d : V) : Finset (Sym2 V) :=
  {s(a,b), s(b,c), s(c,d), s(d,a)}

omit [Fintype V] in
theorem fourEdges_rotate (a b c d : V) :
    fourEdges b c d a = fourEdges a b c d := by
  ext e
  simp [fourEdges, or_comm, or_left_comm]

omit [Fintype V] in
theorem fourEdges_reverse (a b c d : V) :
    fourEdges a d c b = fourEdges a b c d := by
  ext e
  simp [fourEdges, Sym2.eq_swap, or_comm, or_left_comm, or_assoc]

omit [Fintype V] in
theorem fourEdges_card (a b c d : V) (hd : [a,b,c,d].Nodup) :
    (fourEdges a b c d).card = 4 := by
  simp only [List.nodup_cons, List.mem_cons,
    not_or, List.nodup_nil, List.not_mem_nil, not_false_eq_true, and_true] at hd
  simp [fourEdges, hd.1.1, hd.1.2.1, hd.1.2.2,
    hd.2.1.1, hd.2.1.2, hd.2.2, Ne.symm hd.1.1, Ne.symm hd.1.2.1,
    Ne.symm hd.1.2.2]

/-- Shape alone, independent of any ambient graph. -/
def IsFourCycle (C : Finset (Sym2 V)) : Prop :=
  ∃ a b c d : V, [a,b,c,d].Nodup ∧ C = fourEdges a b c d

omit [Fintype V] in
theorem IsFourCycle.card {C : Finset (Sym2 V)} (h : IsFourCycle C) : C.card = 4 := by
  obtain ⟨a,b,c,d,hd,rfl⟩ := h
  exact fourEdges_card a b c d hd

noncomputable def cycles (G : SimpleGraph V) : Finset (Finset (Sym2 V)) := by
  classical
  exact G.edgeFinset.powerset.filter IsFourCycle

noncomputable def cycleCount (G : SimpleGraph V) : ℕ := (cycles G).card

@[simp] theorem mem_cycles (G : SimpleGraph V) (C : Finset (Sym2 V)) :
    C ∈ cycles G ↔ C ⊆ G.edgeFinset ∧ IsFourCycle C := by
  classical
  simp [cycles]

theorem cycles_mono {G H : SimpleGraph V} (h : G ≤ H) : cycles G ⊆ cycles H := by
  classical
  intro C hC
  obtain ⟨hsub, hshape⟩ := (mem_cycles G C).mp hC
  exact (mem_cycles H C).mpr ⟨fun e he => by
    have heG := hsub he
    simp only [SimpleGraph.mem_edgeFinset] at heG ⊢
    exact SimpleGraph.edgeSet_mono h heG, hshape⟩

theorem cycleCount_mono {G H : SimpleGraph V} (h : G ≤ H) :
    cycleCount G ≤ cycleCount H := Finset.card_le_card (cycles_mono h)

/-- Abstract edge deletion bound: pairwise edge-disjoint members each destroyed
by some missing edge inject into the actual set of missing edges. -/
theorem destroyed_le_missing {E : Type*} [DecidableEq E]
    (P : Finset (Finset E)) (D : Finset E)
    (hdis : ∀ p ∈ P, ∀ r ∈ P, p ≠ r → Disjoint p r) :
    (P.filter fun p => ¬ Disjoint p D).card ≤ D.card := by
  classical
  let B := P.filter fun p => ¬ Disjoint p D
  have hw : ∀ p ∈ B, ∃ e, e ∈ p ∧ e ∈ D := by
    intro p hp
    have hn := (Finset.mem_filter.mp hp).2
    obtain ⟨e, hep, heD⟩ := by
      simpa only [Finset.disjoint_left, not_forall, not_not] using hn
    exact ⟨e, hep, heD⟩
  by_cases hB : B.Nonempty
  · let f : Finset E → E := fun p => if hp : p ∈ B then (hw p hp).choose
      else (hw hB.choose hB.choose_spec).choose
    apply Finset.card_le_card_of_injOn f
    · intro p hp
      change p ∈ B at hp
      dsimp [f]
      rw [dif_pos hp]
      exact (hw p hp).choose_spec.2
    · intro p hp r hr heq
      by_contra hne
      have hd := hdis p (Finset.mem_filter.mp hp).1 r (Finset.mem_filter.mp hr).1 hne
      have hfp : f p ∈ p := by
        change p ∈ B at hp
        dsimp [f]
        rw [dif_pos hp]
        exact (hw p hp).choose_spec.1
      have hfr : f r ∈ r := by
        change r ∈ B at hr
        dsimp [f]
        rw [dif_pos hr]
        exact (hw r hr).choose_spec.1
      exact Finset.disjoint_left.mp hd hfp (heq ▸ hfr)
  · have : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    change B.card ≤ D.card
    simp [this]

/-- At least |P|-|D| members survive deleting D. -/
theorem retained_ge_sub_missing {E : Type*} [DecidableEq E]
    (P : Finset (Finset E)) (D : Finset E)
    (hdis : ∀ p ∈ P, ∀ r ∈ P, p ≠ r → Disjoint p r) :
    P.card - D.card ≤ (P.filter fun p => Disjoint p D).card := by
  classical
  have hb := destroyed_le_missing P D hdis
  have hs := Finset.card_filter_add_card_filter_not (s := P) (p := fun p => Disjoint p D)
  omega

/-- An endpoint-marked simple three-path, represented only by its three edges. -/
def IsThreePath (e : Sym2 V) (p : Finset (Sym2 V)) : Prop :=
  ∃ a x y b : V, e = s(a,b) ∧ [a,x,y,b].Nodup ∧
    p = {s(a,x), s(x,y), s(y,b)}

omit [Fintype V] in
theorem threePath_closes {e : Sym2 V} {p : Finset (Sym2 V)}
    (hp : IsThreePath e p) : IsFourCycle (insert e p) := by
  obtain ⟨a,x,y,b,rfl,hd,rfl⟩ := hp
  refine ⟨a,x,y,b,hd,?_⟩
  simp [fourEdges, Sym2.eq_swap, Finset.ext_iff, or_comm, or_left_comm]

omit [Fintype V] in
/-- Edge sets avoid a distinguished added edge, so closing is injective. -/
theorem close_injective {e : Sym2 V} (P : Finset (Finset (Sym2 V)))
    (havoid : ∀ p ∈ P, e ∉ p) : Set.InjOn (fun p : Finset (Sym2 V) => insert e p) (P : Set _) := by
  intro p hp r hr h
  have hh := congrArg (fun C : Finset (Sym2 V) => C.erase e) h
  simpa [Finset.erase_insert, havoid p hp, havoid r hr] using hh

/-- Actual graph one-added-edge counting theorem. The path hypotheses are
finite families of actual simple Q-three-path edge sets, pairwise edge-disjoint
for each added edge. No cycle count inequality is assumed. -/
theorem retained_path_count (G Q : SimpleGraph V)
    (A : Finset (Sym2 V)) (P : Sym2 V → Finset (Finset (Sym2 V))) (k : ℕ)
    (hA : ∀ e ∈ A, e ∈ G.edgeFinset ∧ e ∉ Q.edgeFinset)
    (hpath : ∀ e ∈ A, ∀ p ∈ P e, IsThreePath e p ∧ p ⊆ Q.edgeFinset)
    (hdis : ∀ e ∈ A, ∀ p ∈ P e, ∀ r ∈ P e, p ≠ r → Disjoint p r)
    (hnum : ∀ e ∈ A, k ≤ (P e).card) :
    A.card * (k - (Q.edgeFinset \ G.edgeFinset).card) ≤ cycleCount G := by
  classical
  let D := Q.edgeFinset \ G.edgeFinset
  let R := fun e => (P e).filter fun p => Disjoint p D
  let F := fun e => (R e).image (insert e)
  have hR : ∀ e ∈ A, ∀ p ∈ R e, p ⊆ G.edgeFinset := by
    intro e he p hp a ha
    have hpP := (Finset.mem_filter.mp hp).1
    have hpD := (Finset.mem_filter.mp hp).2
    by_contra hn
    exact Finset.disjoint_left.mp hpD ha
      (Finset.mem_sdiff.mpr ⟨(hpath e he p hpP).2 ha, hn⟩)
  have havoid : ∀ e ∈ A, ∀ p ∈ P e, e ∉ p := by
    intro e he p hp hn
    exact (hA e he).2 ((hpath e he p hp).2 hn)
  have hFcount : ∀ e ∈ A, k - D.card ≤ (F e).card := by
    intro e he
    have hr := retained_ge_sub_missing (P e) D (hdis e he)
    have hi : Set.InjOn (fun p : Finset (Sym2 V) => insert e p) (R e : Set _) := close_injective (R e)
      (fun p hp => havoid e he p (Finset.mem_filter.mp hp).1)
    have hc : (F e).card = (R e).card := Finset.card_image_iff.mpr hi
    rw [hc]
    exact (Nat.sub_le_sub_right (hnum e he) D.card).trans hr
  have hFsub : ∀ e ∈ A, F e ⊆ cycles G := by
    intro e he C hC
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hC
    apply (mem_cycles G _).mpr
    exact ⟨Finset.insert_subset (hA e he).1 (hR e he p hp),
      threePath_closes (hpath e he p (Finset.mem_filter.mp hp).1).1⟩
  have hFdis : ∀ e ∈ A, ∀ f ∈ A, e ≠ f → Disjoint (F e) (F f) := by
    intro e he f hf hne
    apply Finset.disjoint_left.mpr
    intro C hCe hCf
    obtain ⟨p,hp,hCp⟩ := Finset.mem_image.mp hCe
    obtain ⟨r,hr,hCr⟩ := Finset.mem_image.mp hCf
    have heC : e ∈ insert f r := by rw [hCr, ← hCp]; simp
    rcases Finset.mem_insert.mp heC with hef | her
    · exact hne hef
    · exact (hA e he).2 ((hpath f hf r (Finset.mem_filter.mp hr).1).2 her)
  have hUnion : A.biUnion F ⊆ cycles G := by
    intro C hC
    obtain ⟨e,he,hCe⟩ := Finset.mem_biUnion.mp hC
    exact hFsub e he hCe
  calc
    A.card * (k - D.card) = ∑ e ∈ A, (k - D.card) := by simp
    _ ≤ ∑ e ∈ A, (F e).card := Finset.sum_le_sum hFcount
    _ = (A.biUnion F).card := (Finset.card_biUnion (by
      intro e he f hf hne
      exact hFdis e he f hf hne)).symm
    _ ≤ cycleCount G := Finset.card_le_card hUnion

end Erdos60.Counting

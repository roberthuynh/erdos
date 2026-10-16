import MatchingConverse

set_option linter.unusedSimpArgs false
namespace Erdos60.Counting
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem cycle_erase_threePath {C : Finset (Sym2 V)} {e : Sym2 V}
    (hC : IsFourCycle C) (he : e ∈ C) : IsThreePath e (C.erase e) := by
  obtain ⟨a,b,c,d,hd,rfl⟩ := hC
  have hne : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
    simpa only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, not_or, not_false_eq_true, and_true, and_assoc] using hd
  obtain ⟨hab,hac,had,hbc,hbd,hcd⟩ := hne
  simp only [fourEdges, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · refine ⟨a,d,c,b,rfl,?_,?_⟩
    · simp [List.nodup_cons, hab,hac,had,hbc,hbd,hcd, Ne.symm hab,
        Ne.symm hac,Ne.symm had,Ne.symm hbc,Ne.symm hbd,Ne.symm hcd]
    · simp [fourEdges, Finset.erase_insert_of_ne, Sym2.eq_iff, hab,hac,had,hbc,hbd,hcd,
        Ne.symm hab,Ne.symm hac,Ne.symm had,Ne.symm hbc,Ne.symm hbd,Ne.symm hcd]
      ext z
      simp [Sym2.eq_swap, or_comm,or_left_comm,or_assoc]
  · refine ⟨b,a,d,c,rfl,?_,?_⟩
    · simp [List.nodup_cons, hab,hac,had,hbc,hbd,hcd, Ne.symm hab,
        Ne.symm hac,Ne.symm had,Ne.symm hbc,Ne.symm hbd,Ne.symm hcd]
    · simp [fourEdges, Finset.erase_insert_of_ne, Sym2.eq_iff, hab,hac,had,hbc,hbd,hcd,
        Ne.symm hab,Ne.symm hac,Ne.symm had,Ne.symm hbc,Ne.symm hbd,Ne.symm hcd]
      ext z
      simp [Sym2.eq_swap, or_comm,or_left_comm,or_assoc]
  · refine ⟨c,b,a,d,rfl,?_,?_⟩
    · simp [List.nodup_cons, hab,hac,had,hbc,hbd,hcd, Ne.symm hab,
        Ne.symm hac,Ne.symm had,Ne.symm hbc,Ne.symm hbd,Ne.symm hcd]
    · simp [fourEdges, Finset.erase_insert_of_ne, Sym2.eq_iff, hab,hac,had,hbc,hbd,hcd,
        Ne.symm hab,Ne.symm hac,Ne.symm had,Ne.symm hbc,Ne.symm hbd,Ne.symm hcd]
      ext z
      simp [Sym2.eq_swap, or_comm,or_left_comm,or_assoc]
  · refine ⟨d,c,b,a,rfl,?_,?_⟩
    · simp [List.nodup_cons, hab,hac,had,hbc,hbd,hcd, Ne.symm hab,
        Ne.symm hac,Ne.symm had,Ne.symm hbc,Ne.symm hbd,Ne.symm hcd]
    · simp [fourEdges, Finset.erase_insert_of_ne, Sym2.eq_iff, hab,hac,had,hbc,hbd,hcd,
        Ne.symm hab,Ne.symm hac,Ne.symm had,Ne.symm hbc,Ne.symm hbd,Ne.symm hcd]
      ext z
      simp [Sym2.eq_swap, or_comm,or_left_comm,or_assoc]

/-- Closing and erasing give the cardinality correspondence, under an explicit
complete path-family membership contract and actual base-path containment. -/
theorem marked_card_eq_paths (G Q : SimpleGraph V) (e : Sym2 V)
    (P : Finset (Finset (Sym2 V)))
    (heG : e ∈ G.edgeFinset) (heQ : e ∉ Q.edgeFinset)
    (hQG : Q ≤ G)
    (hbase : ∀ C ∈ markedCycles G e, C.erase e ⊆ Q.edgeFinset)
    (hcomplete : ∀ p, p ∈ P ↔ IsThreePath e p ∧ p ⊆ Q.edgeFinset) :
    (markedCycles G e).card = P.card := by
  classical
  have hfamily : markedCycles G e = P.image (insert e) := by
    ext C
    constructor
    · intro hC
      obtain ⟨hcycle,heC⟩ := Finset.mem_filter.mp hC
      have hp : C.erase e ∈ P := (hcomplete _).mpr
        ⟨cycle_erase_threePath ((mem_cycles G C).mp hcycle).2 heC,hbase C hC⟩
      exact Finset.mem_image.mpr ⟨C.erase e,hp,Finset.insert_erase heC⟩
    · intro hC
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hC
      obtain ⟨hpath,hsub⟩ := (hcomplete p).mp hp
      apply Finset.mem_filter.mpr
      refine ⟨(mem_cycles G _).mpr ⟨?_,threePath_closes hpath⟩,by simp⟩
      apply Finset.insert_subset heG
      intro x hx
      have hQ := hsub hx
      simp only [SimpleGraph.mem_edgeFinset] at hQ ⊢
      exact SimpleGraph.edgeSet_mono hQG hQ
  rw [hfamily]
  apply Finset.card_image_iff.mpr
  apply close_injective P
  intro p hp he
  exact heQ (((hcomplete p).mp hp).2 he)

/-- Every marked matching cycle erases to an actual path in the base graph. -/
theorem matching_marked_erase_subset (Q K : SimpleGraph V) (S : Set V)
    (hm : IsMatchingGraph K)
    (hsupport : ∀ a b, K.Adj a b → a ∈ S ∧ b ∈ S)
    (hind : ∀ a ∈ S, ∀ b ∈ S, ¬ Q.Adj a b)
    (e : Sym2 V) (he : e ∈ K.edgeFinset)
    (C : Finset (Sym2 V)) (hC : C ∈ markedCycles (Q ⊔ K) e) :
    C.erase e ⊆ Q.edgeFinset := by
  obtain ⟨hcycle,heC⟩ := Finset.mem_filter.mp hC
  have hone := matching_cycle_at_most_one Q K S hm hsupport hind C hcycle
  have hsub := ((mem_cycles _ _).mp hcycle).1
  intro x hx
  obtain ⟨hne,hxC⟩ := Finset.mem_erase.mp hx
  have hG := hsub hxC
  simp only [SimpleGraph.mem_edgeFinset] at hG ⊢
  rw [SimpleGraph.edgeSet_sup, Set.mem_union] at hG
  rcases hG with hQ | hK
  · exact hQ
  · have hxK : x ∈ K.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hK
    exact False.elim (hne (Finset.card_le_one.mp hone x
      (Finset.mem_inter.mpr ⟨hxC,hxK⟩) e (Finset.mem_inter.mpr ⟨heC,he⟩)))

/-- The full matching converse counting bridge. Exact k is assumed only for
complete actual base-three-path families, never for cycle counts. -/
theorem matching_exact_cycle_count (Q K : SimpleGraph V) (S : Set V)
    (hfree : cycles Q = ∅)
    (hm : IsMatchingGraph K)
    (hsupport : ∀ a b, K.Adj a b → a ∈ S ∧ b ∈ S)
    (hind : ∀ a ∈ S, ∀ b ∈ S, ¬ Q.Adj a b)
    (P : Sym2 V → Finset (Finset (Sym2 V))) (k : ℕ)
    (hcomplete : ∀ e ∈ K.edgeFinset, ∀ p,
      p ∈ P e ↔ IsThreePath e p ∧ p ⊆ Q.edgeFinset)
    (hcount : ∀ e ∈ K.edgeFinset, (P e).card = k) :
    cycleCount (Q ⊔ K) = K.edgeFinset.card * k := by
  have hdis : Disjoint Q.edgeFinset K.edgeFinset := by
    apply Finset.disjoint_left.mpr
    intro e
    refine Sym2.inductionOn e (fun a b => ?_)
    intro heQ heK
    have hQ : Q.Adj a b := by simpa using heQ
    have hK : K.Adj a b := by simpa using heK
    exact hind a (hsupport a b hK).1 b (hsupport a b hK).2 hQ
  rw [matching_cycle_partition_count Q K S hfree hm hsupport hind]
  calc
    ∑ e ∈ K.edgeFinset, (markedCycles (Q ⊔ K) e).card =
        ∑ e ∈ K.edgeFinset, k := by
      apply Finset.sum_congr rfl
      intro e he
      rw [marked_card_eq_paths (Q ⊔ K) Q e (P e) ?_ ?_ le_sup_left
        (matching_marked_erase_subset Q K S hm hsupport hind e he) (hcomplete e he)]
      · exact hcount e he
      · simp only [SimpleGraph.mem_edgeFinset] at he ⊢
        exact SimpleGraph.edgeSet_mono le_sup_right he
      · exact fun heQ => Finset.disjoint_left.mp hdis heQ he
    _ = K.edgeFinset.card * k := by simp

/-- The complete finite family of base three-path edge sets for e. -/
noncomputable def baseThreePaths (Q : SimpleGraph V) (e : Sym2 V) :
    Finset (Finset (Sym2 V)) := Q.edgeFinset.powerset.filter (IsThreePath e)

@[simp] theorem mem_baseThreePaths (Q : SimpleGraph V) (e : Sym2 V)
    (p : Finset (Sym2 V)) :
    p ∈ baseThreePaths Q e ↔ IsThreePath e p ∧ p ⊆ Q.edgeFinset := by
  simp [baseThreePaths,and_comm]

/-- Canonical-family version: geometry only has to provide the exact number of
actual base three-path edge sets for each added matching edge. -/
theorem matching_exact_cycle_count_canonical (Q K : SimpleGraph V) (S : Set V)
    (hfree : cycles Q = ∅)
    (hm : IsMatchingGraph K)
    (hsupport : ∀ a b, K.Adj a b → a ∈ S ∧ b ∈ S)
    (hind : ∀ a ∈ S, ∀ b ∈ S, ¬ Q.Adj a b)
    (k : ℕ) (hcount : ∀ e ∈ K.edgeFinset, (baseThreePaths Q e).card = k) :
    cycleCount (Q ⊔ K) = K.edgeFinset.card * k := by
  apply matching_exact_cycle_count Q K S hfree hm hsupport hind (baseThreePaths Q) k
  · intro e he p
    exact mem_baseThreePaths Q e p
  · exact hcount

end Erdos60.Counting

import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.MinimalNeighborhoodHall

/-! Actual nested equal-shore matching layers, constructed by finite residual recursion. -/
namespace Erdos642.CampaignFe72210bContinuation3.NestedMatchingLayers

open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An adjacency equivalence gives exactly its actual matching edges. -/
def matchingGraph (C D : Finset V) (hCD : Disjoint C D)
    (e : ↥(C : Set V) ≃ ↥(D : Set V)) : SimpleGraph V where
  Adj x y := (∃ hx : x ∈ C, (e ⟨x, hx⟩).val = y) ∨
    (∃ hy : y ∈ C, (e ⟨y, hy⟩).val = x)
  symm := ⟨by intro x y h; exact h.elim Or.inr Or.inl⟩
  loopless := ⟨by
    intro x h
    rcases h with ⟨hx, he⟩ | ⟨hx, he⟩
    all_goals
      have hxD : x ∈ D := he ▸ (e ⟨x, hx⟩).property
      exact Finset.disjoint_left.mp hCD hx hxD⟩

omit [Fintype V] [DecidableEq V] in
/-- The selected graph really crosses precisely the selected shores. -/
theorem matchingGraph_cross (C D : Finset V) (hCD : Disjoint C D)
    (e : ↥(C : Set V) ≃ ↥(D : Set V)) :
    (matchingGraph C D hCD e).IsBipartiteWith (C : Set V) (D : Set V) := by
  refine ⟨by simpa using hCD, ?_⟩
  intro x y h
  rcases h with ⟨hx, he⟩ | ⟨hy, he⟩
  · exact Or.inl ⟨hx, he ▸ (e ⟨x, hx⟩).property⟩
  · exact Or.inr ⟨he ▸ (e ⟨y, hy⟩).property, hy⟩

omit [Fintype V] [DecidableEq V] in
/-- A genuine matching has at most one actual neighbor at every ambient vertex. -/
theorem matchingGraph_unique (C D : Finset V) (hCD : Disjoint C D)
    (e : ↥(C : Set V) ≃ ↥(D : Set V)) (x y z : V)
    (hxy : (matchingGraph C D hCD e).Adj x y)
    (hxz : (matchingGraph C D hCD e).Adj x z) : y = z := by
  rcases hxy with ⟨hx, hxy⟩ | ⟨hy, hyx⟩
  · rcases hxz with ⟨hx', hxz⟩ | ⟨hz, hzx⟩
    · have he : (e ⟨x, hx⟩).val = (e ⟨x, hx'⟩).val :=
        congrArg (fun a : (C : Set V) => (e a).val) (Subtype.ext rfl)
      exact hxy.symm.trans (he.trans hxz)
    · have hxD : x ∈ D := hzx ▸ (e ⟨z, hz⟩).property
      exact False.elim (Finset.disjoint_left.mp hCD hx hxD)
  · rcases hxz with ⟨hx, hxz⟩ | ⟨hz, hzx⟩
    · have hxD : x ∈ D := hyx ▸ (e ⟨y, hy⟩).property
      exact False.elim (Finset.disjoint_left.mp hCD hx hxD)
    · have he : e ⟨y, hy⟩ = e ⟨z, hz⟩ := Subtype.ext (hyx.trans hzx.symm)
      exact congrArg Subtype.val (e.injective he)

omit [Fintype V] [DecidableEq V] in
/-- Every actual bijection edge belongs to its selected matching graph. -/
theorem matchingGraph_map (C D : Finset V) (hCD : Disjoint C D)
    (e : ↥(C : Set V) ≃ ↥(D : Set V)) (x : (C : Set V)) :
    (matchingGraph C D hCD e).Adj x.val (e x).val :=
  Or.inl ⟨x.property, rfl⟩

omit [Fintype V] [DecidableEq V] in
/-- If the bijection follows residual adjacency, every selected edge is a residual edge. -/
theorem matchingGraph_le (R : SimpleGraph V) (C D : Finset V) (hCD : Disjoint C D)
    (e : ↥(C : Set V) ≃ ↥(D : Set V))
    (he : ∀ x : (C : Set V), R.Adj x.val (e x).val) :
    matchingGraph C D hCD e ≤ R := by
  intro x y h
  rcases h with ⟨hx, hxy⟩ | ⟨hy, hyx⟩
  · rw [← hxy]
    exact he ⟨x, hx⟩
  · rw [← hyx]
    exact (he ⟨y, hy⟩).symm

omit [DecidableEq V] in
/-- Literal neighbor cardinality avoids unspecified finite instances in stored graph fields. -/
theorem neighbor_ncard_eq_degree (R : SimpleGraph V) [DecidableRel R.Adj] (v : V) :
    (R.neighborSet v).ncard = R.degree v := by
  rw [Set.ncard_eq_toFinset_card', ← R.neighborFinset_def v]
  exact R.card_neighborFinset_eq_degree v

/-- Actual matching-edge deletion lowers an actual degree by at most one. -/
theorem matching_deletion_degree (R M : SimpleGraph V) (hMR : M ≤ R)
    (hunique : ∀ v w z, M.Adj v w → M.Adj v z → w = z) (v : V) :
    (R.neighborSet v).ncard ≤ ((R \ M).neighborSet v).ncard + 1 := by
  classical
  have hUnion : R.neighborFinset v = (R \ M).neighborFinset v ∪ M.neighborFinset v := by
    ext w
    simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset, SimpleGraph.sdiff_adj]
    constructor
    · intro h
      by_cases hM : M.Adj v w
      · exact Or.inr hM
      · exact Or.inl ⟨h, hM⟩
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact hMR h
  have hMcard : (M.neighborFinset v).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro w hw z hz
    exact hunique v w z (by simpa using hw) (by simpa using hz)
  have hcard := Finset.card_union_le ((R \ M).neighborFinset v) (M.neighborFinset v)
  rw [← hUnion] at hcard
  have h := hcard.trans (Nat.add_le_add_left hMcard _)
  simpa only [SimpleGraph.card_neighborFinset_eq_degree, neighbor_ncard_eq_degree] using h

/-- Actual finite layer data. Matchings i connect shores i+1; shores zero are the inputs. -/
structure Layers (G : SimpleGraph V) (A B : Finset V) (n : ℕ) where
  left : ℕ → Finset V
  right : ℕ → Finset V
  matching : ℕ → SimpleGraph V
  leftZero : left 0 = A
  rightZero : right 0 = B
  leftSubset : ∀ i, i ≤ n → left i ⊆ A
  rightSubset : ∀ i, i ≤ n → right i ⊆ B
  leftNonempty : ∀ i, i ≤ n → (left i).Nonempty
  rightNonempty : ∀ i, 1 ≤ i → i ≤ n → (right i).Nonempty
  leftNested : ∀ i, i < n → left (i + 1) ⊆ left i
  rightNested : ∀ i, i < n → right (i + 1) ⊆ right i
  equalCard : ∀ i, 1 ≤ i → i ≤ n → (left i).card = (right i).card
  matchingLe : ∀ i, i < n → matching i ≤ G
  matchingCross : ∀ i, i < n →
    (matching i).IsBipartiteWith (left (i + 1) : Set V) (right (i + 1) : Set V)
  matchingUnique : ∀ i, i < n → ∀ v w z,
    (matching i).Adj v w → (matching i).Adj v z → w = z
  bijection : ∀ i, i < n →
    ∃ e : ↥(left (i + 1) : Set V) ≃ ↥(right (i + 1) : Set V),
      (∀ x : (left (i + 1) : Set V), G.Adj x.val (e x).val) ∧
      (∀ x : (left (i + 1) : Set V), (matching i).Adj x.val (e x).val)
  separated : ∀ i, i < n → ∀ j, j < n → i ≠ j → ∀ v w,
    (matching i).Adj v w → ¬ (matching j).Adj v w

/-- Internal residual invariants, all derived along with the public actual family. -/
structure State (G : SimpleGraph V) (A B : Finset V) (δ n : ℕ) where
  layers : Layers G A B n
  residual : SimpleGraph V
  residualLe : residual ≤ G
  avoids : ∀ i, i < n → ∀ v w, residual.Adj v w → ¬ (layers.matching i).Adj v w
  budget : ∀ a ∈ A, δ ≤ (residual.neighborSet a).ncard + n
  containment : ∀ a ∈ layers.left n, residual.neighborSet a ⊆ (layers.right n : Set V)

private def initialState (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (δ : ℕ) (hA : A.Nonempty)
    (hcontain : ∀ a ∈ A, G.neighborFinset a ⊆ B)
    (hdegree : ∀ a ∈ A, δ ≤ G.degree a) : State G A B δ 0 := by
  classical
  let L : Layers G A B 0 := {
    left := fun _ => A
    right := fun _ => B
    matching := fun _ => ⊥
    leftZero := rfl
    rightZero := rfl
    leftSubset := by intro i hi; exact Finset.Subset.refl A
    rightSubset := by intro i hi; exact Finset.Subset.refl B
    leftNonempty := by intro i hi; exact hA
    rightNonempty := by intro i hi hle; omega
    leftNested := by intro i hi; omega
    rightNested := by intro i hi; omega
    equalCard := by intro i hi hle; omega
    matchingLe := by intro i hi; omega
    matchingCross := by intro i hi; omega
    matchingUnique := by intro i hi; omega
    bijection := by intro i hi; omega
    separated := by intro i hi; omega }
  refine {
    layers := L
    residual := G
    residualLe := le_rfl
    avoids := by intro i hi; omega
    budget := ?_
    containment := ?_ }
  · intro a ha
    simpa only [neighbor_ncard_eq_degree, Nat.add_zero] using hdegree a ha
  · intro a ha b hb
    exact hcontain a ha (by simpa using hb)

/-- One Hall step appends an actual matching and updates the actual residual graph. -/
theorem exists_next_state (G : SimpleGraph V) (A B : Finset V) (δ n : ℕ)
    (hAB : Disjoint A B) (hcard : B.card ≤ A.card)
    (S : State G A B δ n) (hn : n < δ) : Nonempty (State G A B δ (n + 1)) := by
  classical
  let L := S.layers
  have hcurrentDisjoint : Disjoint (L.left n) (L.right n) :=
    hAB.mono (L.leftSubset n le_rfl) (L.rightSubset n le_rfl)
  have hcurrentCard : (L.right n).card ≤ (L.left n).card := by
    by_cases hzero : n = 0
    · subst n
      simpa only [L.leftZero, L.rightZero] using hcard
    · exact (L.equalCard n (by omega) le_rfl).symm.le
  have hcurrentContain : ∀ a ∈ L.left n,
      S.residual.neighborFinset a ⊆ L.right n := by
    intro a ha b hb
    exact S.containment a ha (by simpa using hb)
  have hcurrentPositive : ∀ a ∈ L.left n, 0 < S.residual.degree a := by
    intro a ha
    have h := S.budget a (L.leftSubset n le_rfl ha)
    rw [neighbor_ncard_eq_degree] at h
    omega
  obtain ⟨C, hCsub, hCne, hDsub, hDne, hCD, hCequal, _, e, he⟩ :=
    MinimalNeighborhoodHall.exists_minimal_neighborhood_matching S.residual
      (L.left n) (L.right n) (L.leftNonempty n le_rfl) hcurrentDisjoint
      hcurrentCard hcurrentContain hcurrentPositive
  let D := MinimalNeighborhoodHall.neighbors S.residual C
  let M := matchingGraph C D hCD e
  have hMR : M ≤ S.residual := matchingGraph_le S.residual C D hCD e he
  have hMunique : ∀ v w z, M.Adj v w → M.Adj v z → w = z :=
    matchingGraph_unique C D hCD e
  let lf : ℕ → Finset V := fun i => if i = n + 1 then C else L.left i
  let rf : ℕ → Finset V := fun i => if i = n + 1 then D else L.right i
  let mf : ℕ → SimpleGraph V := fun i => if i = n then M else L.matching i
  have hlOld : ∀ i, i ≤ n → lf i = L.left i := by
    intro i hi
    simp only [lf, if_neg (show i ≠ n + 1 by omega)]
  have hrOld : ∀ i, i ≤ n → rf i = L.right i := by
    intro i hi
    simp only [rf, if_neg (show i ≠ n + 1 by omega)]
  have hmOld : ∀ i, i < n → mf i = L.matching i := by
    intro i hi
    simp only [mf, if_neg (show i ≠ n by omega)]
  have hlNew : lf (n + 1) = C := by simp only [lf, if_pos rfl]
  have hrNew : rf (n + 1) = D := by simp only [rf, if_pos rfl]
  have hmNew : mf n = M := by simp only [mf, if_pos rfl]
  let L' : Layers G A B (n + 1) := {
    left := lf
    right := rf
    matching := mf
    leftZero := by rw [hlOld 0 (by omega)]; exact L.leftZero
    rightZero := by rw [hrOld 0 (by omega)]; exact L.rightZero
    leftSubset := by
      intro i hi
      by_cases h : i = n + 1
      · subst i; rw [hlNew]; exact hCsub.trans (L.leftSubset n le_rfl)
      · rw [hlOld i (by omega)]; exact L.leftSubset i (by omega)
    rightSubset := by
      intro i hi
      by_cases h : i = n + 1
      · subst i; rw [hrNew]; exact hDsub.trans (L.rightSubset n le_rfl)
      · rw [hrOld i (by omega)]; exact L.rightSubset i (by omega)
    leftNonempty := by
      intro i hi
      by_cases h : i = n + 1
      · subst i; rw [hlNew]; exact hCne
      · rw [hlOld i (by omega)]; exact L.leftNonempty i (by omega)
    rightNonempty := by
      intro i hpos hi
      by_cases h : i = n + 1
      · subst i; rw [hrNew]; exact hDne
      · rw [hrOld i (by omega)]; exact L.rightNonempty i hpos (by omega)
    leftNested := by
      intro i hi
      by_cases h : i = n
      · subst i; rw [hlNew, hlOld n le_rfl]; exact hCsub
      · rw [hlOld (i + 1) (by omega), hlOld i (by omega)]
        exact L.leftNested i (by omega)
    rightNested := by
      intro i hi
      by_cases h : i = n
      · subst i; rw [hrNew, hrOld n le_rfl]; exact hDsub
      · rw [hrOld (i + 1) (by omega), hrOld i (by omega)]
        exact L.rightNested i (by omega)
    equalCard := by
      intro i hpos hi
      by_cases h : i = n + 1
      · subst i; rw [hlNew, hrNew]; exact hCequal
      · rw [hlOld i (by omega), hrOld i (by omega)]
        exact L.equalCard i hpos (by omega)
    matchingLe := by
      intro i hi
      by_cases h : i = n
      · subst i; rw [hmNew]; exact hMR.trans S.residualLe
      · rw [hmOld i (by omega)]; exact L.matchingLe i (by omega)
    matchingCross := by
      intro i hi
      by_cases h : i = n
      · subst i; rw [hmNew, hlNew, hrNew]
        exact matchingGraph_cross C D hCD e
      · rw [hmOld i (by omega), hlOld (i + 1) (by omega), hrOld (i + 1) (by omega)]
        exact L.matchingCross i (by omega)
    matchingUnique := by
      intro i hi
      by_cases h : i = n
      · subst i; rw [hmNew]; exact hMunique
      · rw [hmOld i (by omega)]; exact L.matchingUnique i (by omega)
    bijection := by
      intro i hi
      by_cases h : i = n
      · subst i; rw [hlNew, hrNew, hmNew]
        exact ⟨e, fun x => S.residualLe (he x), matchingGraph_map C D hCD e⟩
      · rw [hlOld (i + 1) (by omega), hrOld (i + 1) (by omega), hmOld i (by omega)]
        exact L.bijection i (by omega)
    separated := by
      intro i hi j hj hij v w
      by_cases hin : i = n
      · subst i
        have hjold : j < n := by omega
        rw [hmNew, hmOld j hjold]
        intro hnew
        exact S.avoids j hjold v w (hMR hnew)
      · have hiold : i < n := by omega
        by_cases hjn : j = n
        · subst j
          rw [hmOld i hiold, hmNew]
          intro hold hnew
          exact S.avoids i hiold v w (hMR hnew) hold
        · rw [hmOld i hiold, hmOld j (by omega)]
          exact L.separated i hiold j (by omega) hij v w }
  refine ⟨{
    layers := L'
    residual := S.residual \ M
    residualLe := (show S.residual \ M ≤ S.residual from sdiff_le).trans S.residualLe
    avoids := ?_
    budget := ?_
    containment := ?_ }⟩
  · intro i hi v w hnew
    have hparts := (SimpleGraph.sdiff_adj S.residual M v w).mp hnew
    change ¬ (mf i).Adj v w
    by_cases h : i = n
    · subst i; rw [hmNew]; exact hparts.2
    · rw [hmOld i (by omega)]
      exact S.avoids i (by omega) v w hparts.1
  · intro a ha
    have hbudget := S.budget a ha
    have hdrop := matching_deletion_degree S.residual M hMR hMunique a
    omega
  · intro a ha b hab
    change a ∈ lf (n + 1) at ha
    rw [hlNew] at ha
    change b ∈ (rf (n + 1) : Set V)
    rw [hrNew]
    have hactual : S.residual.Adj a b :=
      ((SimpleGraph.sdiff_adj S.residual M a b).mp hab).1
    exact (MinimalNeighborhoodHall.mem_neighbors S.residual C b).mpr ⟨a, ha, hactual⟩

/-- The full actual family is constructed; no desired sequence is a hypothesis. -/
theorem exists_nested_matching_layers (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (δ : ℕ) (hA : A.Nonempty) (hAB : Disjoint A B)
    (hcard : B.card ≤ A.card)
    (hcontain : ∀ a ∈ A, G.neighborFinset a ⊆ B)
    (hdegree : ∀ a ∈ A, δ ≤ G.degree a) : Nonempty (Layers G A B δ) := by
  have hstates : ∀ n, n ≤ δ → Nonempty (State G A B δ n) := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨initialState G A B δ hA hcontain hdegree⟩
    | succ n ih =>
      intro hn
      obtain ⟨S⟩ := ih (by omega)
      exact exists_next_state G A B δ n hAB hcard S (by omega)
  obtain ⟨S⟩ := hstates δ le_rfl
  exact ⟨S.layers⟩

end Erdos642.CampaignFe72210bContinuation3.NestedMatchingLayers

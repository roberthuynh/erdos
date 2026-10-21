import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic

namespace Erdos643
namespace GraphDeletion

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable local instance (G : SimpleGraph V) : Fintype G.edgeSet := Fintype.ofFinite _

/-- Two distinct common neighbors, with the endpoints themselves distinct. -/
def IsDiagonal (G : SimpleGraph V) (x y : V) : Prop :=
  x ≠ y ∧ ∃ a b, a ≠ b ∧ G.Adj x a ∧ G.Adj y a ∧ G.Adj x b ∧ G.Adj y b

lemma isDiagonal_symm {G : SimpleGraph V} {x y : V} :
    IsDiagonal G x y ↔ IsDiagonal G y x := by
  constructor <;> rintro ⟨hxy, a, b, hab, hxa, hya, hxb, hyb⟩
  · exact ⟨hxy.symm, a, b, hab, hya, hxa, hyb, hxb⟩
  · exact ⟨hxy.symm, a, b, hab, hya, hxa, hyb, hxb⟩

noncomputable def diagonalGraph (G : SimpleGraph V) : SimpleGraph V where
  Adj := IsDiagonal G
  symm := ⟨fun _ _ h => isDiagonal_symm.mp h⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable def diagonals (G : SimpleGraph V) : Finset (Sym2 V) := by
  classical
  exact (diagonalGraph G).edgeFinset

lemma mem_diagonals {G : SimpleGraph V} {x y : V} :
    s(x,y) ∈ diagonals G ↔ IsDiagonal G x y := by
  classical
  change s(x,y) ∈ (diagonalGraph G).edgeFinset ↔ _
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  rfl

lemma isDiagonal_mono {G H : SimpleGraph V} (h : H ≤ G) {x y : V}
    (hd : IsDiagonal H x y) : IsDiagonal G x y := by
  rcases hd with ⟨hxy, a, b, hab, hxa, hya, hxb, hyb⟩
  exact ⟨hxy, a, b, hab, h hxa, h hya, h hxb, h hyb⟩

lemma diagonals_mono {G H : SimpleGraph V} (h : H ≤ G) :
    diagonals H ⊆ diagonals G := by
  classical
  exact SimpleGraph.edgeFinset_mono (fun _ _ hd => isDiagonal_mono h hd)

/-- The PV wing X = D(u) ∩ N(v). -/
noncomputable def wing (G : SimpleGraph V) (u v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun x => IsDiagonal G u x ∧ G.Adj v x)

lemma mem_wing {G : SimpleGraph V} {u v x : V} :
    x ∈ wing G u v ↔ IsDiagonal G u x ∧ G.Adj v x := by
  classical
  simp [wing]

/-- Unordered edges all incident to a specified vertex. -/
def spokes (v : V) (X : Finset V) : Finset (Sym2 V) := X.image (fun x => s(v,x))

lemma spoke_injective (v : V) : Function.Injective (fun x : V => s(v,x)) := by
  intro x y h
  rcases Sym2.eq_iff.mp h with h | h
  · exact h.2
  · exact h.2.trans h.1

lemma card_spokes (v : V) (X : Finset V) : (spokes v X).card = X.card :=
  Finset.card_image_of_injective X (spoke_injective v)

lemma spokes_subset_edges (G : SimpleGraph V) (u v : V) :
    spokes v (wing G u v) ⊆ G.edgeFinset := by
  classical
  intro e he
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
  exact SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet G).mpr (mem_wing.mp hx).2)

lemma wing_excludes_left (G : SimpleGraph V) (u v : V) : u ∉ wing G u v := by
  intro h
  exact (mem_wing.mp h).1.1 rfl

lemma wing_excludes_right (G : SimpleGraph V) (u v : V) : v ∉ wing G u v := by
  intro h
  exact G.loopless.irrefl _ (mem_wing.mp h).2

/-- The elementary four-cycle inference underlying both cases of PV Claim 1. -/
lemma alternate_wing {G : SimpleGraph V} {u v y w : V}
    (huv : G.Adj u v) (hy : y ∈ wing G v u)
    (hvw : G.Adj v w) (hyw : G.Adj y w) (hwu : w ≠ u) :
    w ∈ wing G u v := by
  apply mem_wing.mpr
  refine ⟨⟨hwu.symm, v, y, (mem_wing.mp hy).1.1, huv, hvw.symm,
    (mem_wing.mp hy).2, hyw.symm⟩, hvw⟩

/-- Deleting the v-X spokes and uv kills every original v-Y diagonal completely. -/
lemma unbalanced_kills {G : SimpleGraph V} {u v : V} (huv : G.Adj u v)
    {y : V} (hy : y ∈ wing G v u) :
    ¬ ∃ w, (G.deleteEdges (↑(insert s(u,v) (spokes v (wing G u v))) : Set (Sym2 V))).Adj v w ∧
      (G.deleteEdges (↑(insert s(u,v) (spokes v (wing G u v))) : Set (Sym2 V))).Adj y w := by
  classical
  rintro ⟨w, hvw, hyw⟩
  obtain ⟨hvw, hn⟩ := SimpleGraph.deleteEdges_adj.mp hvw
  obtain ⟨hyw, _⟩ := SimpleGraph.deleteEdges_adj.mp hyw
  have hwu : w ≠ u := by
    rintro rfl
    exact hn (by simp [Sym2.eq_swap])
  have hw := alternate_wing huv hy hvw hyw hwu
  exact hn (by simp only [Finset.mem_coe, Finset.mem_insert]; right; exact Finset.mem_image.mpr ⟨w, hw, rfl⟩)

/-- Deleting both wing-spoke families kills the v-Y diagonals, including half remnants. -/
lemma balanced_kills_right {G : SimpleGraph V} {u v : V} (huv : G.Adj u v)
    {y : V} (hy : y ∈ wing G v u) :
    ¬ ∃ w, (G.deleteEdges (↑(spokes v (wing G u v) ∪ spokes u (wing G v u)) : Set (Sym2 V))).Adj v w ∧
      (G.deleteEdges (↑(spokes v (wing G u v) ∪ spokes u (wing G v u)) : Set (Sym2 V))).Adj y w := by
  classical
  rintro ⟨w, hvw, hyw⟩
  obtain ⟨hvw, hn⟩ := SimpleGraph.deleteEdges_adj.mp hvw
  obtain ⟨hyw, hn'⟩ := SimpleGraph.deleteEdges_adj.mp hyw
  have hwu : w ≠ u := by
    rintro rfl
    apply hn'
    simp only [Finset.mem_coe, Finset.mem_union]
    right
    exact Finset.mem_image.mpr ⟨y, hy, Sym2.eq_swap⟩
  have hw := alternate_wing huv hy hvw hyw hwu
  apply hn
  simp only [Finset.mem_coe, Finset.mem_union]
  left
  exact Finset.mem_image.mpr ⟨w, hw, rfl⟩

lemma balanced_kills_left {G : SimpleGraph V} {u v : V} (huv : G.Adj u v)
    {x : V} (hx : x ∈ wing G u v) :
    ¬ ∃ w, (G.deleteEdges (↑(spokes v (wing G u v) ∪ spokes u (wing G v u)) : Set (Sym2 V))).Adj u w ∧
      (G.deleteEdges (↑(spokes v (wing G u v) ∪ spokes u (wing G v u)) : Set (Sym2 V))).Adj x w := by
  simpa only [Finset.union_comm] using balanced_kills_right huv.symm hx

lemma diagonal_spokes_subset (G : SimpleGraph V) (u v : V) :
    spokes u (wing G u v) ⊆ diagonals G := by
  classical
  intro e he
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
  exact mem_diagonals.mpr (mem_wing.mp hx).1

lemma disjoint_diagonal_spokes {G : SimpleGraph V} {u v : V} (huv : G.Adj u v) :
    Disjoint (spokes u (wing G u v)) (spokes v (wing G v u)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hf
  rcases Sym2.eq_iff.mp hxy with h | h
  · exact huv.ne h.1.symm
  · exact wing_excludes_right G u v (h.1 ▸ hx)

/-- PV Claim 1 in an orientation where the first wing is no larger. -/
lemma local_deletion_oriented {G : SimpleGraph V} {u v : V}
    (huv : G.Adj u v) (hX : (wing G u v).Nonempty)
    (hXY : (wing G u v).card ≤ (wing G v u).card) :
    ∃ R T : Finset (Sym2 V), R.Nonempty ∧ R ⊆ G.edgeFinset ∧
      T ⊆ diagonals G ∧ R.card ≤ T.card ∧
      ∀ x y, s(x,y) ∈ T → ¬ ∃ z, (G.deleteEdges (↑R : Set (Sym2 V))).Adj x z ∧
        (G.deleteEdges (↑R : Set (Sym2 V))).Adj y z := by
  classical
  by_cases heq : (wing G u v).card = (wing G v u).card
  · let R := spokes v (wing G u v) ∪ spokes u (wing G v u)
    let T := spokes u (wing G u v) ∪ spokes v (wing G v u)
    refine ⟨R, T, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨x, hx⟩ := hX
      exact ⟨s(v,x), Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩
    · exact Finset.union_subset (spokes_subset_edges G u v) (spokes_subset_edges G v u)
    · exact Finset.union_subset (diagonal_spokes_subset G u v) (diagonal_spokes_subset G v u)
    · dsimp [R, T]
      rw [Finset.card_union_of_disjoint (disjoint_diagonal_spokes huv), card_spokes, card_spokes]
      calc
        _ ≤ (spokes v (wing G u v)).card + (spokes u (wing G v u)).card := Finset.card_union_le _ _
        _ = _ := by rw [card_spokes, card_spokes]
    · intro x y hxy
      rcases Finset.mem_union.mp hxy with hxy | hxy
      · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hxy
        rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact balanced_kills_left huv ha
        · 
          rintro ⟨z, hz, hz'⟩
          exact balanced_kills_left huv ha ⟨z, hz', hz⟩
      · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hxy
        rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact balanced_kills_right huv ha
        · 
          rintro ⟨z, hz, hz'⟩
          exact balanced_kills_right huv ha ⟨z, hz', hz⟩
  · let R := insert s(u,v) (spokes v (wing G u v))
    let T := spokes v (wing G v u)
    refine ⟨R, T, Finset.insert_nonempty _ _, ?_, diagonal_spokes_subset G v u, ?_, ?_⟩
    · apply Finset.insert_subset_iff.mpr
      exact ⟨SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet G).mpr huv), spokes_subset_edges G u v⟩
    · dsimp [R, T]
      rw [card_spokes]
      have hc := Finset.card_insert_le s(u,v) (spokes v (wing G u v))
      rw [card_spokes] at hc
      omega
    · intro x y hxy
      obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hxy
      rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact unbalanced_kills huv ha
      · 
        rintro ⟨z, hz, hz'⟩
        exact unbalanced_kills huv ha ⟨z, hz', hz⟩

/-- PV Claim 1: a graph with a diagonal admits a nonempty edge deletion charged
injectively (in cardinality) to original diagonals brought all the way to zero. -/
theorem local_deletion {G : SimpleGraph V} {x y : V} (hd : IsDiagonal G x y) :
    ∃ R T : Finset (Sym2 V), R.Nonempty ∧ R ⊆ G.edgeFinset ∧
      T ⊆ diagonals G ∧ R.card ≤ T.card ∧
      ∀ a b, s(a,b) ∈ T → ¬ ∃ z, (G.deleteEdges (↑R : Set (Sym2 V))).Adj a z ∧
        (G.deleteEdges (↑R : Set (Sym2 V))).Adj b z := by
  classical
  obtain ⟨hxy, a, b, hab, hxa, hya, hxb, hyb⟩ := hd
  have hX : (wing G x a).Nonempty := ⟨y, mem_wing.mpr ⟨⟨hxy, a, b, hab, hxa, hya, hxb, hyb⟩, hya.symm⟩⟩
  have hY : (wing G a x).Nonempty := by
    refine ⟨b, mem_wing.mpr ⟨?_, hxb⟩⟩
    exact ⟨hab, x, y, hxy, hxa.symm, hxb.symm, hya.symm, hyb.symm⟩
  rcases le_total (wing G x a).card (wing G a x).card with h | h
  · exact local_deletion_oriented hxa hX h
  · exact local_deletion_oriented hxa.symm hY h

/-- Residual half-diagonal cleanup. This is the last paragraph of PV Lemma 3. -/
lemma half_deletion {G : SimpleGraph V} {a b z : V} (hab : a ≠ b)
    (hnd : ¬ IsDiagonal G a b) (haz : G.Adj a z) (hbz : G.Adj b z) :
    ¬ ∃ w, (G.deleteEdges ({s(a,z)} : Set (Sym2 V))).Adj a w ∧
      (G.deleteEdges ({s(a,z)} : Set (Sym2 V))).Adj b w := by
  classical
  rintro ⟨w, haw, hbw⟩
  obtain ⟨haw, hn⟩ := SimpleGraph.deleteEdges_adj.mp haw
  obtain ⟨hbw, _⟩ := SimpleGraph.deleteEdges_adj.mp hbw
  have hwz : w ≠ z := by
    rintro rfl
    exact hn (Set.mem_singleton _)
  exact hnd ⟨hab, w, z, hwz, haw, hbw, haz, hbz⟩

/-- A charge-preserving step, allowing an arbitrary nonloop charge set containing
all current diagonals. Original charges can include current half-diagonals. -/
lemma charge_step (G : SimpleGraph V) (S : Finset (Sym2 V))
    (hS : ∀ a b, s(a,b) ∈ S → a ≠ b) (hD : diagonals G ⊆ S)
    (hactive : ∃ a b, s(a,b) ∈ S ∧ ∃ z, G.Adj a z ∧ G.Adj b z) :
    ∃ R T : Finset (Sym2 V), T.Nonempty ∧ R ⊆ G.edgeFinset ∧
      T ⊆ S ∧ R.card ≤ T.card ∧
      ∀ a b, s(a,b) ∈ T → ¬ ∃ z, (G.deleteEdges (↑R : Set (Sym2 V))).Adj a z ∧
        (G.deleteEdges (↑R : Set (Sym2 V))).Adj b z := by
  classical
  by_cases hd : ∃ a b, IsDiagonal G a b
  · obtain ⟨a, b, hd⟩ := hd
    obtain ⟨R, T, hR, hRG, hTD, hc, hk⟩ := local_deletion hd
    refine ⟨R, T, ?_, hRG, hTD.trans hD, hc, hk⟩
    have hpos := Finset.card_pos.mpr hR
    exact Finset.card_pos.mp (by omega)
  · obtain ⟨a, b, habS, z, haz, hbz⟩ := hactive
    refine ⟨{s(a,z)}, {s(a,b)}, Finset.singleton_nonempty _, ?_, ?_, ?_, ?_⟩
    · simpa using SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet G).mpr haz)
    · simpa using habS
    · simp
    · intro x y hxy
      have he : s(a,b) = s(x,y) := (Finset.mem_singleton.mp hxy).symm
      rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa using half_deletion (hS _ _ habS) (fun h => hd ⟨_, _, h⟩) haz hbz
      · rintro ⟨w, hbw, haw⟩
        apply half_deletion (hS _ _ habS) (fun h => hd ⟨_, _, h⟩) haz hbz
        simpa using (show ∃ w, (G.deleteEdges (↑({s(a,z)} : Finset (Sym2 V)) : Set (Sym2 V))).Adj a w ∧
          (G.deleteEdges (↑({s(a,z)} : Finset (Sym2 V)) : Set (Sym2 V))).Adj b w from ⟨w, haw, hbw⟩)

/-- Finite induction on the remaining charge set. All charge sets refer to pairs
of distinct original vertices, and each step deletes actual current edges. -/
theorem deletion_with_charges (G : SimpleGraph V) (S : Finset (Sym2 V))
    (hS : ∀ a b, s(a,b) ∈ S → a ≠ b) (hD : diagonals G ⊆ S) :
    ∃ R : Finset (Sym2 V), R ⊆ G.edgeFinset ∧ R.card ≤ S.card ∧
      ∀ a b, s(a,b) ∈ S → ¬ ∃ z, (G.deleteEdges (↑R : Set (Sym2 V))).Adj a z ∧
        (G.deleteEdges (↑R : Set (Sym2 V))).Adj b z := by
  classical
  suffices aux : ∀ n : ℕ, ∀ (G : SimpleGraph V) (S : Finset (Sym2 V)), S.card = n →
      (∀ a b, s(a,b) ∈ S → a ≠ b) → diagonals G ⊆ S →
      ∃ R : Finset (Sym2 V), R ⊆ G.edgeFinset ∧ R.card ≤ S.card ∧
        ∀ a b, s(a,b) ∈ S → ¬ ∃ z, (G.deleteEdges (↑R : Set (Sym2 V))).Adj a z ∧
          (G.deleteEdges (↑R : Set (Sym2 V))).Adj b z by
    exact aux S.card G S rfl hS hD
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G S hcard hS hD
    by_cases hactive : ∃ a b, s(a,b) ∈ S ∧ ∃ z, G.Adj a z ∧ G.Adj b z
    · obtain ⟨R, T, hT, hRG, hTS, hc, hk⟩ := charge_step G S hS hD hactive
      let H := G.deleteEdges (↑R : Set (Sym2 V))
      have hsub : diagonals H ⊆ S \ T := by
        intro e he
        apply Finset.mem_sdiff.mpr
        refine ⟨hD (diagonals_mono (G.deleteEdges_le _) he), ?_⟩
        induction e using Sym2.inductionOn with
        | _ a b =>
          intro hTmem
          obtain ⟨_, z, w, hzw, haz, hbz, haw, hbw⟩ := mem_diagonals.mp he
          exact hk a b hTmem ⟨z, haz, hbz⟩
      have hlt : (S \ T).card < n := by
        have heq := Finset.card_sdiff_add_card_eq_card hTS
        have hp := Finset.card_pos.mpr hT
        omega
      obtain ⟨Q, hQH, hQc, hQk⟩ := ih (S \ T).card hlt H (S \ T) rfl
        (fun a b hp => hS a b (Finset.mem_sdiff.mp hp).1) hsub
      refine ⟨R ∪ Q, Finset.union_subset hRG (hQH.trans (SimpleGraph.edgeFinset_mono (G.deleteEdges_le _))), ?_, ?_⟩
      · have heq := Finset.card_sdiff_add_card_eq_card hTS
        have hle := Finset.card_union_le R Q
        omega
      · intro a b hp
        have hrewrite : G.deleteEdges (↑(R ∪ Q) : Set (Sym2 V)) = H.deleteEdges (↑Q : Set (Sym2 V)) := by
          simp [H]
        rw [hrewrite]
        by_cases ht : s(a,b) ∈ T
        · rintro ⟨z, haz, hbz⟩
          exact hk a b ht ⟨z, (H.deleteEdges_le _ haz), (H.deleteEdges_le _ hbz)⟩
        · exact hQk a b (Finset.mem_sdiff.mpr ⟨hp, ht⟩)
    · refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
      intro a b hp hex
      apply hactive
      simpa using (show ∃ a b, s(a,b) ∈ S ∧ ∃ z,
        (G.deleteEdges (↑(∅ : Finset (Sym2 V)) : Set (Sym2 V))).Adj a z ∧
        (G.deleteEdges (↑(∅ : Finset (Sym2 V)) : Set (Sym2 V))).Adj b z from ⟨a,b,hp,hex⟩)

/-- Pikhurko--Verstraëte 2009 Lemma 3, with unordered diagonal charges and
complete elimination of common neighbors for every ORIGINAL diagonal. -/
theorem pv2009_lemma3 (G : SimpleGraph V) :
    ∃ R : Finset (Sym2 V), R ⊆ G.edgeFinset ∧ R.card ≤ (diagonals G).card ∧
      ∀ a b, IsDiagonal G a b → ¬ ∃ z,
        (G.deleteEdges (↑R : Set (Sym2 V))).Adj a z ∧
        (G.deleteEdges (↑R : Set (Sym2 V))).Adj b z := by
  classical
  obtain ⟨R, hRG, hc, hk⟩ := deletion_with_charges G (diagonals G)
    (fun a b hp => (mem_diagonals.mp hp).1) (Finset.Subset.refl _)
  exact ⟨R, hRG, hc, fun a b hd => hk a b (mem_diagonals.mpr hd)⟩

/-- The finite set of actual common neighbors; its cardinality is PV's μ. -/
noncomputable def commonNeighborFinset (G : SimpleGraph V) (a b : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun z => G.Adj a z ∧ G.Adj b z)

lemma mem_commonNeighborFinset {G : SimpleGraph V} {a b z : V} :
    z ∈ commonNeighborFinset G a b ↔ G.Adj a z ∧ G.Adj b z := by
  classical
  simp [commonNeighborFinset]

lemma coe_commonNeighborFinset (G : SimpleGraph V) (a b : V) :
    (↑(commonNeighborFinset G a b) : Set V) = G.commonNeighbors a b := by
  ext z
  simp [mem_commonNeighborFinset, SimpleGraph.mem_commonNeighbors]

/-- Exact bridge from the witness formulation to the source's μ ≥ 2. -/
lemma isDiagonal_iff_commonNeighbor_card (G : SimpleGraph V) (a b : V) :
    IsDiagonal G a b ↔ a ≠ b ∧ 2 ≤ (commonNeighborFinset G a b).card := by
  classical
  constructor
  · rintro ⟨hab, x, y, hxy, hax, hbx, hay, hby⟩
    refine ⟨hab, ?_⟩
    have hp : 1 < (commonNeighborFinset G a b).card := Finset.one_lt_card.mpr
      ⟨x, mem_commonNeighborFinset.mpr ⟨hax,hbx⟩, y, mem_commonNeighborFinset.mpr ⟨hay,hby⟩, hxy⟩
    omega
  · rintro ⟨hab, hc⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (show 1 < (commonNeighborFinset G a b).card by omega)
    obtain ⟨hax, hbx⟩ := mem_commonNeighborFinset.mp hx
    obtain ⟨hay, hby⟩ := mem_commonNeighborFinset.mp hy
    exact ⟨hab, x, y, hxy, hax, hbx, hay, hby⟩

/-- The supplier with μ expressed explicitly as a finite cardinality. -/
theorem pv2009_lemma3_card (G : SimpleGraph V) :
    ∃ R : Finset (Sym2 V), R ⊆ G.edgeFinset ∧ R.card ≤ (diagonals G).card ∧
      ∀ a b, a ≠ b → 2 ≤ (commonNeighborFinset G a b).card →
        commonNeighborFinset (G.deleteEdges (↑R : Set (Sym2 V))) a b = ∅ := by
  classical
  obtain ⟨R, hRG, hc, hk⟩ := pv2009_lemma3 G
  refine ⟨R, hRG, hc, ?_⟩
  intro a b hab hd
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  exact hk a b ((isDiagonal_iff_commonNeighbor_card G a b).mpr ⟨hab,hd⟩)
    ⟨z, (mem_commonNeighborFinset.mp hz).1, (mem_commonNeighborFinset.mp hz).2⟩

end GraphDeletion
end Erdos643

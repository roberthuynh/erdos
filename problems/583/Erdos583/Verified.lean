/- Complete standalone proof of the path-partition bounds.
The sections preserve the original modular proof structure.
See source-identity.json for source provenance. -/
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Fintype.Option
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Decomposition
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Rat.Cast.Order
import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/- BEGIN Erdos583.Parity; source SHA256 6bd3952638b3f7db53661df8c0081d529c7d74b68d552e8a50bd20cc713787da -/
section Source01_Erdos583_Parity




/-!+# Parity accounting for deletion of all even-neighbor edges at one center

The vertex type is kept fixed, so deleted centers are counted as isolates when
appropriate. This file contains graph accounting only, not a path-decomposition
bound or an assumed restoration theorem.
-/

noncomputable section

namespace Erdos583

open SimpleGraph
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

def oddVertices (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter fun v => Odd (G.degree v)

def nonisolatedEvenVertices (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter fun v => Even (G.degree v) ∧ G.degree v ≠ 0

def isolatedVertices (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter fun v => G.degree v = 0

def phi (G : SimpleGraph V) : ℚ :=
  (oddVertices G).card / 2 + 2 * (nonisolatedEvenVertices G).card / 3

def evenNeighbors (G : SimpleGraph V) (x : V) : Finset V :=
  (G.neighborFinset x).filter fun v => Even (G.degree v)

def evenNeighborCount (G : SimpleGraph V) (x : V) : ℕ :=
  (evenNeighbors G x).card

@[simp] theorem mem_oddVertices (G : SimpleGraph V) (v : V) :
    v ∈ oddVertices G ↔ Odd (G.degree v) := by simp [oddVertices]

@[simp] theorem mem_nonisolatedEvenVertices (G : SimpleGraph V) (v : V) :
    v ∈ nonisolatedEvenVertices G ↔ Even (G.degree v) ∧ G.degree v ≠ 0 := by
  simp [nonisolatedEvenVertices]

@[simp] theorem mem_isolatedVertices (G : SimpleGraph V) (v : V) :
    v ∈ isolatedVertices G ↔ G.degree v = 0 := by simp [isolatedVertices]

@[simp] theorem mem_evenNeighbors (G : SimpleGraph V) (x v : V) :
    v ∈ evenNeighbors G x ↔ G.Adj x v ∧ Even (G.degree v) := by
  simp [evenNeighbors, G.mem_neighborFinset]

theorem even_card_oddVertices (G : SimpleGraph V) : Even (oddVertices G).card :=
  G.even_card_odd_degree_vertices

theorem evenNeighbors_subset (G : SimpleGraph V) (x : V) :
    evenNeighbors G x ⊆ G.neighborFinset x := Finset.filter_subset _ _

theorem evenNeighborCount_le_degree (G : SimpleGraph V) (x : V) :
    evenNeighborCount G x ≤ G.degree x :=
  Finset.card_le_card (evenNeighbors_subset G x)

/-- Delete precisely the edges from `x` to its even-degree neighbors. The parity
of the center is unrestricted. -/
def starDeleteEven (G : SimpleGraph V) (x : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ ¬ (a = x ∧ Even (G.degree b)) ∧
    ¬ (b = x ∧ Even (G.degree a))
  symm := ⟨by intro a b h; exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by intro a h; exact h.1.ne rfl⟩

@[simp] theorem starDeleteEven_adj (G : SimpleGraph V) (x a b : V) :
    (starDeleteEven G x).Adj a b ↔ G.Adj a b ∧
      ¬ (a = x ∧ Even (G.degree b)) ∧ ¬ (b = x ∧ Even (G.degree a)) := Iff.rfl

theorem starDeleteEven_le (G : SimpleGraph V) (x : V) : starDeleteEven G x ≤ G :=
  fun _ _ h => h.1

theorem neighborFinset_starDeleteEven_center (G : SimpleGraph V) (x : V) :
    (starDeleteEven G x).neighborFinset x = G.neighborFinset x \ evenNeighbors G x := by
  ext v
  simp only [mem_neighborFinset, starDeleteEven_adj, Finset.mem_sdiff, mem_evenNeighbors]
  constructor
  · intro h; exact ⟨h.1, fun h' => h.2.1 ⟨by trivial, h'.2⟩⟩
  · rintro ⟨h, hn⟩
    exact ⟨h, fun he => hn ⟨h, he.2⟩, fun he => h.ne he.1.symm⟩

theorem degree_starDeleteEven_center (G : SimpleGraph V) (x : V) :
    (starDeleteEven G x).degree x = G.degree x - evenNeighborCount G x := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_starDeleteEven_center,
    Finset.card_sdiff_of_subset (evenNeighbors_subset G x)]
  rfl

theorem neighborFinset_starDeleteEven_selected (G : SimpleGraph V) (x v : V)
    (hv : v ∈ evenNeighbors G x) :
    (starDeleteEven G x).neighborFinset v = (G.neighborFinset v).erase x := by
  classical
  obtain ⟨h, he⟩ := (mem_evenNeighbors G x v).mp hv
  ext w
  simp only [mem_neighborFinset, starDeleteEven_adj, Finset.mem_erase]
  constructor
  · intro hw; exact ⟨fun hwx => hw.2.2 ⟨hwx, he⟩, hw.1⟩
  · rintro ⟨hwx, hw⟩
    exact ⟨hw, fun hvx => h.ne hvx.1.symm, fun hwe => hwx hwe.1⟩

theorem degree_starDeleteEven_selected (G : SimpleGraph V) (x v : V)
    (hv : v ∈ evenNeighbors G x) :
    (starDeleteEven G x).degree v = G.degree v - 1 := by
  classical
  rw [← card_neighborFinset_eq_degree, neighborFinset_starDeleteEven_selected G x v hv,
    Finset.card_erase_of_mem]
  · rfl
  · exact (G.mem_neighborFinset v x).mpr ((mem_evenNeighbors G x v).mp hv).1.symm

theorem neighborFinset_starDeleteEven_other (G : SimpleGraph V) (x v : V)
    (hvx : v ≠ x) (hv : v ∉ evenNeighbors G x) :
    (starDeleteEven G x).neighborFinset v = G.neighborFinset v := by
  ext w
  simp only [mem_neighborFinset, starDeleteEven_adj]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, fun he => hvx he.1, ?_⟩
    rintro ⟨hwx, he⟩
    exact hv ((mem_evenNeighbors G x v).mpr ⟨by simpa [hwx] using h.symm, he⟩)

theorem degree_starDeleteEven_other (G : SimpleGraph V) (x v : V)
    (hvx : v ≠ x) (hv : v ∉ evenNeighbors G x) :
    (starDeleteEven G x).degree v = G.degree v := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_starDeleteEven_other G x v hvx hv]
  rfl

theorem selected_degree_ge_two (G : SimpleGraph V) (x v : V)
    (hv : v ∈ evenNeighbors G x) : 2 ≤ G.degree v := by
  obtain ⟨h, he⟩ := (mem_evenNeighbors G x v).mp hv
  have hp := h.degree_pos_right
  obtain ⟨j, hj⟩ := he
  omega

theorem selected_becomes_odd (G : SimpleGraph V) (x v : V)
    (hv : v ∈ evenNeighbors G x) : Odd ((starDeleteEven G x).degree v) := by
  rw [degree_starDeleteEven_selected G x v hv]
  exact Nat.Even.sub_odd (by have := selected_degree_ge_two G x v hv; omega)
    ((mem_evenNeighbors G x v).mp hv).2 (by decide)

theorem selected_remains_nonisolated (G : SimpleGraph V) (x v : V)
    (hv : v ∈ evenNeighbors G x) : (starDeleteEven G x).degree v ≠ 0 := by
  rw [degree_starDeleteEven_selected G x v hv]
  have := selected_degree_ge_two G x v hv
  omega

theorem oddVertices_erase_starDeleteEven (G : SimpleGraph V) (x : V) :
    (oddVertices (starDeleteEven G x)).erase x =
      (oddVertices G).erase x ∪ evenNeighbors G x := by
  classical
  ext v
  by_cases hv : v ∈ evenNeighbors G x
  · have hne := ((mem_evenNeighbors G x v).mp hv).1.ne.symm
    have ho := selected_becomes_odd G x v hv
    simp [hv, hne, ho]
  · by_cases hne : v = x
    · subst v; simp [hv]
    · simp [hv, hne, degree_starDeleteEven_other G x v hne hv]

theorem nonisolatedEvenVertices_erase_starDeleteEven (G : SimpleGraph V) (x : V) :
    (nonisolatedEvenVertices (starDeleteEven G x)).erase x =
      (nonisolatedEvenVertices G).erase x \ evenNeighbors G x := by
  classical
  ext v
  by_cases hv : v ∈ evenNeighbors G x
  · have ho := selected_becomes_odd G x v hv
    have hn : ¬ Even ((starDeleteEven G x).degree v) := Nat.not_even_iff_odd.mpr ho
    simp [hv, hn]
  · by_cases hne : v = x
    · subst v; simp [hv]
    · simp [hv, hne, degree_starDeleteEven_other G x v hne hv]

theorem isolatedVertices_erase_starDeleteEven (G : SimpleGraph V) (x : V) :
    (isolatedVertices (starDeleteEven G x)).erase x = (isolatedVertices G).erase x := by
  classical
  ext v
  by_cases hv : v ∈ evenNeighbors G x
  · have hn := selected_remains_nonisolated G x v hv
    have hp := selected_degree_ge_two G x v hv
    have hg : G.degree v ≠ 0 := by omega
    simp [hn, hg]
  · by_cases hne : v = x
    · subst v; simp
    · simp [hne, degree_starDeleteEven_other G x v hne hv]

theorem evenNeighbors_subset_nonisolatedEven_erase (G : SimpleGraph V) (x : V) :
    evenNeighbors G x ⊆ (nonisolatedEvenVertices G).erase x := by
  classical
  intro v hv
  obtain ⟨h, he⟩ := (mem_evenNeighbors G x v).mp hv
  exact Finset.mem_erase.mpr ⟨h.ne.symm,
    (mem_nonisolatedEvenVertices G v).mpr ⟨he, Nat.ne_of_gt h.degree_pos_right⟩⟩

theorem disjoint_oddVertices_evenNeighbors (G : SimpleGraph V) (x : V) :
    Disjoint ((oddVertices G).erase x) (evenNeighbors G x) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v ho he
  have hodd := (mem_oddVertices G v).mp (Finset.mem_of_mem_erase ho)
  exact (Nat.not_even_iff_odd.mpr hodd) ((mem_evenNeighbors G x v).mp he).2

theorem card_oddVertices_erase_starDeleteEven (G : SimpleGraph V) (x : V) :
    ((oddVertices (starDeleteEven G x)).erase x).card =
      ((oddVertices G).erase x).card + evenNeighborCount G x := by
  rw [oddVertices_erase_starDeleteEven,
    Finset.card_union_of_disjoint (disjoint_oddVertices_evenNeighbors G x)]
  rfl

theorem card_nonisolatedEvenVertices_erase_starDeleteEven (G : SimpleGraph V) (x : V) :
    ((nonisolatedEvenVertices (starDeleteEven G x)).erase x).card +
      evenNeighborCount G x = ((nonisolatedEvenVertices G).erase x).card := by
  rw [nonisolatedEvenVertices_erase_starDeleteEven]
  exact Finset.card_sdiff_add_card_eq_card (evenNeighbors_subset_nonisolatedEven_erase G x)

/-- The exact contribution of one ordinary degree to the parity potential. -/
def parityWeight (d : ℕ) : ℚ :=
  (if Odd d then 1 / 2 else 0) + (if Even d ∧ d ≠ 0 then 2 / 3 else 0)

omit [Fintype V] in
private theorem card_erase_add_indicator (s : Finset V) (x : V) :
    (s.erase x).card + (if x ∈ s then 1 else 0) = s.card := by
  classical
  by_cases h : x ∈ s
  · simpa [h] using Finset.card_erase_add_one h
  · simp [h]

omit [Fintype V] in
private theorem rat_card_erase_add_indicator (s : Finset V) (x : V) :
    ((s.erase x).card : ℚ) + (if x ∈ s then 1 else 0) = (s.card : ℚ) := by
  classical
  exact_mod_cast card_erase_add_indicator s x

theorem phi_eq_erased (G : SimpleGraph V) (x : V) :
    phi G = ((oddVertices G).erase x).card / 2 +
      2 * (((nonisolatedEvenVertices G).erase x).card : ℚ) / 3 +
      parityWeight (G.degree x) := by
  have ho := rat_card_erase_add_indicator (oddVertices G) x
  have he := rat_card_erase_add_indicator (nonisolatedEvenVertices G) x
  simp only [mem_oddVertices] at ho
  simp only [mem_nonisolatedEvenVertices] at he
  unfold phi parityWeight
  split_ifs at * <;> linarith

theorem phi_starDeleteEven_exact (G : SimpleGraph V) (x : V) :
    phi G - phi (starDeleteEven G x) = (evenNeighborCount G x : ℚ) / 6 +
      parityWeight (G.degree x) - parityWeight ((starDeleteEven G x).degree x) := by
  have ho : (((oddVertices (starDeleteEven G x)).erase x).card : ℚ) =
      (((oddVertices G).erase x).card : ℚ) + evenNeighborCount G x := by
    exact_mod_cast card_oddVertices_erase_starDeleteEven G x
  have he : (((nonisolatedEvenVertices (starDeleteEven G x)).erase x).card : ℚ) +
      evenNeighborCount G x = (((nonisolatedEvenVertices G).erase x).card : ℚ) := by
    exact_mod_cast card_nonisolatedEvenVertices_erase_starDeleteEven G x
  rw [phi_eq_erased G x, phi_eq_erased (starDeleteEven G x) x]
  linarith

theorem parityWeight_zero : parityWeight 0 = 0 := by norm_num [parityWeight]

theorem parityWeight_le_two_thirds (d : ℕ) : parityWeight d ≤ 2 / 3 := by
  unfold parityWeight
  rcases Nat.even_or_odd d with he | ho
  · have hn := Nat.not_odd_iff_even.mpr he
    simp only [if_neg hn]
    split_ifs <;> norm_num
  · have hn := Nat.not_even_iff_odd.mpr ho
    simp [ho, hn]
    norm_num

theorem half_le_parityWeight {d : ℕ} (hd : d ≠ 0) : 1 / 2 ≤ parityWeight d := by
  unfold parityWeight
  rcases Nat.even_or_odd d with he | ho
  · have hn := Nat.not_odd_iff_even.mpr he
    norm_num [he, hn, hd]
  · have hn := Nat.not_even_iff_odd.mpr ho
    norm_num [ho, hn]

theorem parityWeight_drop_ge {d r : ℕ} (hr : r ≤ d) :
    -(1 / 6 : ℚ) ≤ parityWeight d - parityWeight r := by
  by_cases hd : d = 0
  · have hr0 : r = 0 := by omega
    simp [hd, hr0]
  · have hlow := half_le_parityWeight hd
    have hhigh := parityWeight_le_two_thirds r
    linarith

/-- Actual graph potential decrease; the center may have either parity. -/
theorem phi_starDeleteEven_drop (G : SimpleGraph V) (x : V) :
    ((evenNeighborCount G x : ℚ) - 1) / 6 ≤ phi G - phi (starDeleteEven G x) := by
  have hdeg : (starDeleteEven G x).degree x ≤ G.degree x := by
    rw [degree_starDeleteEven_center]
    exact Nat.sub_le _ _
  have hw := parityWeight_drop_ge hdeg
  rw [phi_starDeleteEven_exact]
  linarith

/-- This is the parity premise needed to expose endpoints in any residual
path partition: every original neighbor of the center has odd residual degree. -/
theorem original_neighbor_odd_after_starDeleteEven (G : SimpleGraph V) (x v : V)
    (hv : G.Adj x v) : Odd ((starDeleteEven G x).degree v) := by
  by_cases he : Even (G.degree v)
  · exact selected_becomes_odd G x v ((mem_evenNeighbors G x v).mpr ⟨hv, he⟩)
  · have hnot : v ∉ evenNeighbors G x := by simp [he]
    rw [degree_starDeleteEven_other G x v hv.ne.symm hnot]
    exact Nat.not_even_iff_odd.mp he

theorem odd_count_starDeleteEven (G : SimpleGraph V) (x : V) :
    (oddVertices (starDeleteEven G x)).card + (if Odd (G.degree x) then 1 else 0) =
      (oddVertices G).card + evenNeighborCount G x +
        (if Odd ((starDeleteEven G x).degree x) then 1 else 0) := by
  have hG := card_erase_add_indicator (oddVertices G) x
  have hH := card_erase_add_indicator (oddVertices (starDeleteEven G x)) x
  have hc := card_oddVertices_erase_starDeleteEven G x
  simp only [mem_oddVertices] at hG hH
  omega

theorem even_count_starDeleteEven (G : SimpleGraph V) (x : V) :
    (nonisolatedEvenVertices (starDeleteEven G x)).card + evenNeighborCount G x +
        (if Even (G.degree x) ∧ G.degree x ≠ 0 then 1 else 0) =
      (nonisolatedEvenVertices G).card +
        (if Even ((starDeleteEven G x).degree x) ∧
          (starDeleteEven G x).degree x ≠ 0 then 1 else 0) := by
  have hG := card_erase_add_indicator (nonisolatedEvenVertices G) x
  have hH := card_erase_add_indicator (nonisolatedEvenVertices (starDeleteEven G x)) x
  have hc := card_nonisolatedEvenVertices_erase_starDeleteEven G x
  simp only [mem_nonisolatedEvenVertices] at hG hH
  omega

theorem isolate_count_starDeleteEven (G : SimpleGraph V) (x : V) :
    (isolatedVertices (starDeleteEven G x)).card + (if G.degree x = 0 then 1 else 0) =
      (isolatedVertices G).card +
        (if (starDeleteEven G x).degree x = 0 then 1 else 0) := by
  have hG := card_erase_add_indicator (isolatedVertices G) x
  have hH := card_erase_add_indicator (isolatedVertices (starDeleteEven G x)) x
  have hc := congrArg Finset.card (isolatedVertices_erase_starDeleteEven G x)
  simp only [mem_isolatedVertices] at hG hH
  omega

theorem odd_count_starDeleteEven_bounds (G : SimpleGraph V) (x : V) :
    (oddVertices G).card + evenNeighborCount G x ≤
      (oddVertices (starDeleteEven G x)).card + 1 ∧
    (oddVertices (starDeleteEven G x)).card ≤
      (oddVertices G).card + evenNeighborCount G x + 1 := by
  have h := odd_count_starDeleteEven G x
  split_ifs at h <;> omega

theorem isolate_count_starDeleteEven_le (G : SimpleGraph V) (x : V) :
    (isolatedVertices (starDeleteEven G x)).card ≤ (isolatedVertices G).card + 1 := by
  have h := isolate_count_starDeleteEven G x
  split_ifs at h <;> omega

theorem degree_starDeleteEven_accounting (G : SimpleGraph V) (x v : V) :
    G.degree v = (starDeleteEven G x).degree v +
      (if v = x then evenNeighborCount G x else 0) +
      (if v ∈ evenNeighbors G x then 1 else 0) := by
  by_cases hcenter : v = x
  · subst v
    have hk := evenNeighborCount_le_degree G x
    have hx : x ∉ evenNeighbors G x := by simp
    simp only [degree_starDeleteEven_center, ite_true, if_neg hx]
    omega
  · by_cases hselected : v ∈ evenNeighbors G x
    · rw [degree_starDeleteEven_selected G x v hselected]
      have hd := selected_degree_ge_two G x v hselected
      simp only [if_neg hcenter, if_pos hselected]
      omega
    · rw [degree_starDeleteEven_other G x v hcenter hselected]
      simp [hcenter, hselected]

/-- Exactly `k` original edges are removed by the star operation. -/
theorem edge_count_starDeleteEven (G : SimpleGraph V) (x : V) :
    (starDeleteEven G x).edgeFinset.card + evenNeighborCount G x = G.edgeFinset.card := by
  classical
  have hd : (∑ v : V, G.degree v) = ∑ v : V, ((starDeleteEven G x).degree v +
      (if v = x then evenNeighborCount G x else 0) +
      (if v ∈ evenNeighbors G x then 1 else 0)) :=
    Finset.sum_congr rfl (fun v _ => degree_starDeleteEven_accounting G x v)
  simp only [Finset.sum_add_distrib] at hd
  have hs : (∑ v : V, if v ∈ evenNeighbors G x then 1 else 0) = evenNeighborCount G x := by
    simp only [Finset.sum_boole, evenNeighborCount]
    have hset : (Finset.univ.filter fun v => v ∈ evenNeighbors G x) = evenNeighbors G x := by
      ext v
      simp
    rw [hset]
    rfl
  rw [hs] at hd
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hd
  rw [G.sum_degrees_eq_twice_card_edges,
    (starDeleteEven G x).sum_degrees_eq_twice_card_edges] at hd
  omega

theorem edge_count_starDeleteEven_lt (G : SimpleGraph V) (x : V)
    (hk : 0 < evenNeighborCount G x) :
    (starDeleteEven G x).edgeFinset.card < G.edgeFinset.card := by
  have := edge_count_starDeleteEven G x
  omega

theorem odd_count_starDeleteEven_scaled (G : SimpleGraph V) (x : V)
    (hk : 24 ≤ evenNeighborCount G x) :
    24 * (oddVertices (starDeleteEven G x)).card ≤
      24 * (oddVertices G).card + 25 * evenNeighborCount G x := by
  have := (odd_count_starDeleteEven_bounds G x).2
  omega

theorem isolate_count_starDeleteEven_scaled (G : SimpleGraph V) (x : V)
    (hk : 24 ≤ evenNeighborCount G x) :
    24 * (isolatedVertices (starDeleteEven G x)).card ≤
      24 * (isolatedVertices G).card + evenNeighborCount G x := by
  have := isolate_count_starDeleteEven_le G x
  omega

theorem vertex_parity_count (G : SimpleGraph V) :
    (oddVertices G).card + (nonisolatedEvenVertices G).card +
      (isolatedVertices G).card = Fintype.card V := by
  classical
  have hd : Disjoint (oddVertices G) (nonisolatedEvenVertices G) := by
    apply Finset.disjoint_left.mpr
    intro v ho he
    exact (Nat.not_even_iff_odd.mpr ((mem_oddVertices G v).mp ho))
      ((mem_nonisolatedEvenVertices G v).mp he).1
  have hi : Disjoint (oddVertices G ∪ nonisolatedEvenVertices G) (isolatedVertices G) := by
    apply Finset.disjoint_left.mpr
    intro v hv hz
    have hzero := (mem_isolatedVertices G v).mp hz
    rcases Finset.mem_union.mp hv with ho | he
    · have := (mem_oddVertices G v).mp ho
      simp [hzero] at this
    · exact ((mem_nonisolatedEvenVertices G v).mp he).2 hzero
  have hu : oddVertices G ∪ nonisolatedEvenVertices G ∪ isolatedVertices G = Finset.univ := by
    ext v
    by_cases hz : G.degree v = 0
    · simp [hz]
    · rcases Nat.even_or_odd (G.degree v) with he | ho
      · simp [he, hz]
      · simp [ho]
  have hc := congrArg Finset.card hu
  rw [Finset.card_union_of_disjoint hi, Finset.card_union_of_disjoint hd,
    Finset.card_univ] at hc
  exact hc

/-- A single checked interface for the actual graph accounting used in peeling.
It makes no assertion about path partitions or their restoration. -/
theorem starDeleteEven_accounting (G : SimpleGraph V) (x : V) :
    let H := starDeleteEven G x
    let k := evenNeighborCount G x
    H ≤ G ∧
    H.edgeFinset.card + k = G.edgeFinset.card ∧
    H.degree x = G.degree x - k ∧
    (∀ v, G.Adj x v → Odd (H.degree v)) ∧
    ((k : ℚ) - 1) / 6 ≤ phi G - phi H ∧
    (oddVertices G).card + k ≤ (oddVertices H).card + 1 ∧
    (oddVertices H).card ≤ (oddVertices G).card + k + 1 ∧
    (isolatedVertices H).card ≤ (isolatedVertices G).card + 1 ∧
    (oddVertices H).card + (nonisolatedEvenVertices H).card +
      (isolatedVertices H).card = Fintype.card V := by
  exact ⟨starDeleteEven_le G x, edge_count_starDeleteEven G x,
    degree_starDeleteEven_center G x, original_neighbor_odd_after_starDeleteEven G x,
    phi_starDeleteEven_drop G x, (odd_count_starDeleteEven_bounds G x).1,
    (odd_count_starDeleteEven_bounds G x).2, isolate_count_starDeleteEven_le G x,
    vertex_parity_count (starDeleteEven G x)⟩

end Erdos583
end
end Source01_Erdos583_Parity
/- END Erdos583.Parity -/

/- BEGIN Erdos583.BridgeGraph; source SHA256 2b1dfc042623f325ef276834ca93694d8464ea006b7a2ad4a10cc276b467fb0a -/
section Source02_Erdos583_BridgeGraph




/-! The actual graph used for the Eulerian-to-general bridge: add one hub,
joined precisely to the vertices of odd original degree. No path bound is
assumed or asserted in this module. -/

noncomputable section

namespace Erdos583

open SimpleGraph
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

def parityCompletion (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj a b := match a, b with
    | some u, some v => G.Adj u v
    | none, some v => Odd (G.degree v)
    | some u, none => Odd (G.degree u)
    | none, none => False
  symm := ⟨by intro a b h; cases a <;> cases b <;> first | exact h | exact h.symm⟩
  loopless := ⟨by intro a h; cases a with
                 | none => exact h
                 | some v => exact G.loopless.irrefl v h⟩

@[simp] theorem parityCompletion_adj_some (G : SimpleGraph V) (u v : V) :
    (parityCompletion G).Adj (some u) (some v) ↔ G.Adj u v := Iff.rfl

@[simp] theorem parityCompletion_adj_hub (G : SimpleGraph V) (v : V) :
    (parityCompletion G).Adj none (some v) ↔ Odd (G.degree v) := Iff.rfl

def someEmbedding : V ↪ Option V := ⟨some, Option.some_injective V⟩

theorem parityCompletion_neighbors_hub (G : SimpleGraph V) :
    (parityCompletion G).neighborFinset none = (oddVertices G).map someEmbedding := by
  ext w
  simp only [mem_neighborFinset]
  cases w <;> simp [parityCompletion, someEmbedding]

theorem parityCompletion_neighbors_some (G : SimpleGraph V) (v : V) :
    (parityCompletion G).neighborFinset (some v) =
      if Odd (G.degree v) then insert none ((G.neighborFinset v).map someEmbedding)
      else (G.neighborFinset v).map someEmbedding := by
  ext w
  simp only [mem_neighborFinset]
  cases w <;> by_cases h : Odd (G.degree v) <;>
    simp [parityCompletion, someEmbedding, h]

theorem parityCompletion_degree_hub (G : SimpleGraph V) :
    (parityCompletion G).degree none = (oddVertices G).card := by
  rw [← card_neighborFinset_eq_degree, parityCompletion_neighbors_hub, Finset.card_map]

theorem parityCompletion_degree_some (G : SimpleGraph V) (v : V) :
    (parityCompletion G).degree (some v) = G.degree v +
      if Odd (G.degree v) then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree, parityCompletion_neighbors_some]
  by_cases h : Odd (G.degree v)
  · simp [h, someEmbedding, card_neighborFinset_eq_degree]
  · simp [h, card_neighborFinset_eq_degree]

theorem parityCompletion_even_degree (G : SimpleGraph V) (v : Option V) :
    Even ((parityCompletion G).degree v) := by
  cases v with
  | none => rw [parityCompletion_degree_hub]; exact even_card_oddVertices G
  | some v =>
    rw [parityCompletion_degree_some]
    rcases Nat.even_or_odd (G.degree v) with he | ho
    · simp [Nat.not_odd_iff_even.mpr he, he]
    · simp only [if_pos ho]
      exact ho.add_odd (by decide)

theorem parityCompletion_reachable_some (G : SimpleGraph V) {u v : V}
    (h : G.Reachable u v) : (parityCompletion G).Reachable (some u) (some v) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.rfl
  | @cons a b c hab p ih =>
    exact (show (parityCompletion G).Adj (some a) (some b) from hab).reachable.trans ih

theorem parityCompletion_connected (G : SimpleGraph V) (hG : G.Connected)
    (ho : (oddVertices G).Nonempty) : (parityCompletion G).Connected := by
  obtain ⟨w, hw⟩ := ho
  have hhub : (parityCompletion G).Adj none (some w) := (mem_oddVertices G w).mp hw
  constructor
  intro u v
  cases u with
  | none =>
    cases v with
    | none => exact Reachable.rfl
    | some v => exact hhub.reachable.trans (parityCompletion_reachable_some G (hG.preconnected w v))
  | some u =>
    cases v with
    | none => exact (parityCompletion_reachable_some G (hG.preconnected u w)).trans hhub.symm.reachable
    | some v => exact parityCompletion_reachable_some G (hG.preconnected u v)

/-- Actual parity-completion certificate. Connectivity needs at least one odd
vertex, because otherwise the newly added hub is an isolated vertex. -/
theorem parityCompletion_certificate (G : SimpleGraph V) (hG : G.Connected)
    (ho : (oddVertices G).Nonempty) :
    (parityCompletion G).Connected ∧
    (∀ v, Even ((parityCompletion G).degree v)) ∧
    (parityCompletion G).degree none = (oddVertices G).card ∧
    Fintype.card (Option V) = Fintype.card V + 1 ∧
    (∀ u v, (parityCompletion G).Adj (some u) (some v) ↔ G.Adj u v) := by
  exact ⟨parityCompletion_connected G hG ho, parityCompletion_even_degree G,
    parityCompletion_degree_hub G, Fintype.card_option, fun _ _ => Iff.rfl⟩

end Erdos583
end
end Source02_Erdos583_BridgeGraph
/- END Erdos583.BridgeGraph -/

/- BEGIN Erdos583.Subdivision; source SHA256 3442388a936d7653823f4d8f2130d3c555ede1c3cd4e7a728059b2970809ef0a -/
section Source03_Erdos583_Subdivision



/-! Actual edge subdivision and the one-edge-deleted residual used in the
all-odd branch of the classical mixed-partition induction. This module only
proves graph accounting; no path suppression or decomposition is assumed. -/

noncomputable section
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

/-- Replace xz by x-none-z, retaining all original vertices and isolates. -/
def edgeSubdivision (G : SimpleGraph V) (x z : V) : SimpleGraph (Option V) where
  Adj u v := match u, v with
    | some a, some b => (G.deleteEdges {s(x,z)}).Adj a b
    | none, some a => a = x ∨ a = z
    | some a, none => a = x ∨ a = z
    | none, none => False
  symm := ⟨by intro a b h; cases a <;> cases b <;> first | exact h | exact h.symm⟩
  loopless := ⟨by intro a h; cases a with
                 | none => exact h
                 | some a => exact (G.deleteEdges {s(x,z)}).loopless.irrefl a h⟩

/-- Delete exactly the new edge none--some x from the subdivision. -/
def subdivisionResidual (G : SimpleGraph V) (x z : V) : SimpleGraph (Option V) :=
  (edgeSubdivision G x z).deleteEdges {s(none, some x)}

omit [Fintype V] in
@[simp] theorem edgeSubdivision_adj_some (G : SimpleGraph V) (x z u v : V) :
    (edgeSubdivision G x z).Adj (some u) (some v) ↔
      (G.deleteEdges {s(x,z)}).Adj u v := Iff.rfl

omit [Fintype V] in
@[simp] theorem edgeSubdivision_adj_new (G : SimpleGraph V) (x z v : V) :
    (edgeSubdivision G x z).Adj none (some v) ↔ v = x ∨ v = z := Iff.rfl

omit [Fintype V] in
@[simp] theorem subdivisionResidual_adj_some (G : SimpleGraph V) (x z u v : V) :
    (subdivisionResidual G x z).Adj (some u) (some v) ↔
      (G.deleteEdges {s(x,z)}).Adj u v := by
  simp [subdivisionResidual, SimpleGraph.deleteEdges_adj]

omit [Fintype V] in
theorem subdivisionResidual_adj_new (G : SimpleGraph V) {x z : V} (hxz : x ≠ z) (v : V) :
    (subdivisionResidual G x z).Adj none (some v) ↔ v = z := by
  simp only [subdivisionResidual, SimpleGraph.deleteEdges_adj, edgeSubdivision_adj_new,
    Set.mem_singleton_iff, Sym2.eq_iff]
  simp only [Option.some.injEq, Option.some_ne_none, and_false, or_false, true_and]
  constructor
  · tauto
  · rintro rfl
    exact ⟨Or.inr rfl, hxz.symm⟩

theorem neighborFinset_delete_single_edge_left (G : SimpleGraph V) (x z : V) :
    (G.deleteEdges {s(x,z)}).neighborFinset x = (G.neighborFinset x).erase z := by
  ext v
  simp only [mem_neighborFinset, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff,
    Sym2.eq_iff, Finset.mem_erase]
  constructor
  · rintro ⟨h, hn⟩
    exact ⟨fun he => hn (Or.inl ⟨trivial, he⟩), h⟩
  · rintro ⟨hne, h⟩
    refine ⟨h, ?_⟩
    rintro (⟨_, hvz⟩ | ⟨hxz, hvx⟩)
    · exact hne hvz
    · exact h.ne hvx.symm

theorem neighborFinset_delete_single_edge_right (G : SimpleGraph V) (x z : V) :
    (G.deleteEdges {s(x,z)}).neighborFinset z = (G.neighborFinset z).erase x := by
  have he : s(x,z) = s(z,x) := Sym2.eq_swap
  rw [he]
  exact neighborFinset_delete_single_edge_left G z x

theorem neighborFinset_delete_single_edge_other (G : SimpleGraph V) {x z v : V}
    (hvx : v ≠ x) (hvz : v ≠ z) :
    (G.deleteEdges {s(x,z)}).neighborFinset v = G.neighborFinset v := by
  ext w
  simp [mem_neighborFinset, SimpleGraph.deleteEdges_adj, hvx, hvz]

theorem edgeSubdivision_neighbors_new (G : SimpleGraph V) (x z : V) :
    (edgeSubdivision G x z).neighborFinset none = {some x, some z} := by
  ext v
  simp only [mem_neighborFinset]
  cases v <;> simp [edgeSubdivision]

theorem edgeSubdivision_neighbors_some (G : SimpleGraph V) (x z v : V) :
    (edgeSubdivision G x z).neighborFinset (some v) =
      if v = x ∨ v = z then
        insert none (((G.deleteEdges {s(x,z)}).neighborFinset v).map someEmbedding)
      else ((G.deleteEdges {s(x,z)}).neighborFinset v).map someEmbedding := by
  ext w
  simp only [mem_neighborFinset]
  cases w <;> by_cases h : v = x ∨ v = z <;>
    simp [edgeSubdivision, someEmbedding, h]

theorem subdivisionResidual_neighbors_new (G : SimpleGraph V) {x z : V} (hxz : x ≠ z) :
    (subdivisionResidual G x z).neighborFinset none = {some z} := by
  ext v
  cases v with
  | none => simp
  | some v => simp [subdivisionResidual_adj_new G hxz]

theorem subdivisionResidual_neighbors_some (G : SimpleGraph V) {x z : V} (hxz : x ≠ z) (v : V) :
    (subdivisionResidual G x z).neighborFinset (some v) =
      if v = z then insert none (((G.deleteEdges {s(x,z)}).neighborFinset v).map someEmbedding)
      else ((G.deleteEdges {s(x,z)}).neighborFinset v).map someEmbedding := by
  ext w
  cases w with
  | none =>
    by_cases h : v = z <;> simp [mem_neighborFinset, SimpleGraph.adj_comm,
      subdivisionResidual_adj_new G hxz, someEmbedding, h]
  | some w =>
    by_cases h : v = z <;> simp [mem_neighborFinset, someEmbedding, h]

omit [Fintype V] in
theorem card_insert_none_map_some (S : Finset V) :
    (insert none (S.map someEmbedding)).card = S.card + 1 := by
  simp [someEmbedding]

theorem edgeSubdivision_degree_new (G : SimpleGraph V) {x z : V} (hxz : x ≠ z) :
    (edgeSubdivision G x z).degree none = 2 := by
  rw [← card_neighborFinset_eq_degree, edgeSubdivision_neighbors_new]
  simp [hxz]

theorem edgeSubdivision_degree_some (G : SimpleGraph V) {x z : V} (hxz : G.Adj x z) (v : V) :
    (edgeSubdivision G x z).degree (some v) = G.degree v := by
  rw [← card_neighborFinset_eq_degree, edgeSubdivision_neighbors_some]
  by_cases hvx : v = x
  · subst v
    simp only [true_or, if_pos, card_insert_none_map_some,
      neighborFinset_delete_single_edge_left]
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset x z).mpr hxz), card_neighborFinset_eq_degree]
    have := hxz.degree_pos_left
    omega
  · by_cases hvz : v = z
    · subst v
      simp only [or_true, if_pos, card_insert_none_map_some,
        neighborFinset_delete_single_edge_right]
      rw [Finset.card_erase_of_mem ((G.mem_neighborFinset z x).mpr hxz.symm), card_neighborFinset_eq_degree]
      have := hxz.degree_pos_right
      omega
    · simp [hvx, hvz, neighborFinset_delete_single_edge_other G hvx hvz,
        card_neighborFinset_eq_degree]

theorem subdivisionResidual_degree_new (G : SimpleGraph V) {x z : V} (hxz : x ≠ z) :
    (subdivisionResidual G x z).degree none = 1 := by
  rw [← card_neighborFinset_eq_degree, subdivisionResidual_neighbors_new G hxz]
  simp

theorem subdivisionResidual_degree_left (G : SimpleGraph V) {x z : V} (hxz : G.Adj x z) :
    (subdivisionResidual G x z).degree (some x) = G.degree x - 1 := by
  rw [← card_neighborFinset_eq_degree, subdivisionResidual_neighbors_some G hxz.ne]
  simp only [if_neg hxz.ne, Finset.card_map, neighborFinset_delete_single_edge_left]
  rw [Finset.card_erase_of_mem ((G.mem_neighborFinset x z).mpr hxz), card_neighborFinset_eq_degree]

theorem subdivisionResidual_degree_other (G : SimpleGraph V) {x z : V} (hxz : G.Adj x z)
    (v : V) (hvx : v ≠ x) :
    (subdivisionResidual G x z).degree (some v) = G.degree v := by
  rw [← card_neighborFinset_eq_degree, subdivisionResidual_neighbors_some G hxz.ne]
  by_cases hvz : v = z
  · subst v
    simp only [ite_true, card_insert_none_map_some,
      neighborFinset_delete_single_edge_right]
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset z x).mpr hxz.symm), card_neighborFinset_eq_degree]
    have := hxz.degree_pos_right
    omega
  · simp [hvz, neighborFinset_delete_single_edge_other G hvx hvz,
      card_neighborFinset_eq_degree]


omit [Fintype V] in
theorem edgeSubdivision_comap_some (G : SimpleGraph V) (x z : V) :
    (edgeSubdivision G x z).comap some = G.deleteEdges {s(x,z)} := by
  ext u v
  rfl

omit [Fintype V] in
theorem subdivisionResidual_comap_some (G : SimpleGraph V) (x z : V) :
    (subdivisionResidual G x z).comap some = G.deleteEdges {s(x,z)} := by
  ext u v
  exact subdivisionResidual_adj_some G x z u v

/-- The actual nonisolated vertices; ambient isolates are retained separately. -/
def activeVertices (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter fun v => G.degree v ≠ 0

@[simp] theorem mem_activeVertices (G : SimpleGraph V) (v : V) :
    v ∈ activeVertices G ↔ G.degree v ≠ 0 := by simp [activeVertices]

def edgeExcess (G : SimpleGraph V) : ℕ := 2 * G.edgeFinset.card - (activeVertices G).card

theorem activeVertices_card_le_twice_edges (G : SimpleGraph V) :
    (activeVertices G).card ≤ 2 * G.edgeFinset.card := by
  calc
    _ = ∑ v : V, if G.degree v ≠ 0 then 1 else 0 := by rw [activeVertices, Finset.card_eq_sum_ones, Finset.sum_filter]
    _ ≤ ∑ v : V, G.degree v := by
      apply Finset.sum_le_sum
      intro v _
      split_ifs <;> omega
    _ = _ := G.sum_degrees_eq_twice_card_edges

theorem subdivisionResidual_degree_some_add (G : SimpleGraph V) {x z : V}
    (hxz : G.Adj x z) (v : V) :
    (subdivisionResidual G x z).degree (some v) + (if v = x then 1 else 0) = G.degree v := by
  by_cases hvx : v = x
  · subst v
    rw [subdivisionResidual_degree_left G hxz]
    have := hxz.degree_pos_left
    simp only [ite_true]
    omega
  · rw [subdivisionResidual_degree_other G hxz v hvx, if_neg hvx, add_zero]

theorem edgeSubdivision_edge_count (G : SimpleGraph V) {x z : V} (hxz : G.Adj x z) :
    (edgeSubdivision G x z).edgeFinset.card = G.edgeFinset.card + 1 := by
  have hsum := (edgeSubdivision G x z).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_option, edgeSubdivision_degree_new G hxz.ne] at hsum
  simp only [edgeSubdivision_degree_some G hxz] at hsum
  rw [G.sum_degrees_eq_twice_card_edges] at hsum
  omega

theorem subdivisionResidual_edge_count (G : SimpleGraph V) {x z : V} (hxz : G.Adj x z) :
    (subdivisionResidual G x z).edgeFinset.card = G.edgeFinset.card := by
  have hold : (∑ v : V, (subdivisionResidual G x z).degree (some v)) + 1 =
      ∑ v : V, G.degree v := by
    calc
      _ = ∑ v : V, ((subdivisionResidual G x z).degree (some v) +
          (if v = x then 1 else 0)) := by simp [Finset.sum_add_distrib]
      _ = _ := Finset.sum_congr rfl (fun v _ => subdivisionResidual_degree_some_add G hxz v)
  have hsum := (subdivisionResidual G x z).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_option, subdivisionResidual_degree_new G hxz.ne] at hsum
  rw [G.sum_degrees_eq_twice_card_edges] at hold
  omega

theorem subdivisionResidual_old_nonisolated (G : SimpleGraph V) {x z : V}
    (hxz : G.Adj x z) (hx : 3 ≤ G.degree x) (v : V) :
    (subdivisionResidual G x z).degree (some v) ≠ 0 ↔ G.degree v ≠ 0 := by
  by_cases hvx : v = x
  · subst v
    rw [subdivisionResidual_degree_left G hxz]
    omega
  · rw [subdivisionResidual_degree_other G hxz v hvx]

theorem subdivisionResidual_old_support (G : SimpleGraph V) {x z : V}
    (hxz : G.Adj x z) (hx : 3 ≤ G.degree x) (v : V) :
    some v ∈ (subdivisionResidual G x z).support ↔ v ∈ G.support := by
  rw [← degree_pos_iff_mem_support, ← degree_pos_iff_mem_support,
    Nat.pos_iff_ne_zero, Nat.pos_iff_ne_zero]
  exact subdivisionResidual_old_nonisolated G hxz hx v

theorem subdivisionResidual_activeVertices (G : SimpleGraph V) {x z : V}
    (hxz : G.Adj x z) (hx : 3 ≤ G.degree x) :
    activeVertices (subdivisionResidual G x z) = insert none ((activeVertices G).map someEmbedding) := by
  ext v
  cases v with
  | none => simp [subdivisionResidual_degree_new G hxz.ne, someEmbedding]
  | some v => simp [someEmbedding, subdivisionResidual_old_nonisolated G hxz hx]

theorem subdivisionResidual_active_count (G : SimpleGraph V) {x z : V}
    (hxz : G.Adj x z) (hx : 3 ≤ G.degree x) :
    (activeVertices (subdivisionResidual G x z)).card = (activeVertices G).card + 1 := by
  rw [subdivisionResidual_activeVertices G hxz hx, card_insert_none_map_some]

theorem subdivisionResidual_edgeExcess (G : SimpleGraph V) {x z : V}
    (hxz : G.Adj x z) (hx : 3 ≤ G.degree x) :
    edgeExcess (subdivisionResidual G x z) + 1 = edgeExcess G := by
  have hbound := activeVertices_card_le_twice_edges (subdivisionResidual G x z)
  rw [subdivisionResidual_active_count G hxz hx, subdivisionResidual_edge_count G hxz] at hbound
  unfold edgeExcess
  rw [subdivisionResidual_active_count G hxz hx, subdivisionResidual_edge_count G hxz]
  omega

/-- Every original subdivision-neighbor of x is odd in the residual, including
its new neighbor none. No endpoint or path-partition condition is assumed. -/
theorem subdivisionResidual_original_neighbors_odd (G : SimpleGraph V) {x z : V}
    (hxz : G.Adj x z)
    (hodd : ∀ v, G.degree v ≠ 0 → Odd (G.degree v)) :
    ∀ w, (edgeSubdivision G x z).Adj (some x) w →
      Odd ((subdivisionResidual G x z).degree w) := by
  intro w hw
  cases w with
  | none => rw [subdivisionResidual_degree_new G hxz.ne]; decide
  | some v =>
    have hg : G.Adj x v := (SimpleGraph.deleteEdges_adj.mp hw).1
    rw [subdivisionResidual_degree_other G hxz v hg.ne.symm]
    exact hodd v (Nat.ne_of_gt hg.degree_pos_right)

/-- All ordinary-degree, original-support, edge-count and induction-measure
clauses for the actual subdivision residual. No decomposition conclusion. -/
theorem subdivision_residual_certificate (G : SimpleGraph V) {x z : V}
    (hxz : G.Adj x z) (hx : 3 ≤ G.degree x)
    (hodd : ∀ v, G.degree v ≠ 0 → Odd (G.degree v)) :
    (edgeSubdivision G x z).comap some = G.deleteEdges {s(x,z)} ∧
    (∀ v, (edgeSubdivision G x z).degree (some v) = G.degree v) ∧
    (edgeSubdivision G x z).degree none = 2 ∧
    (subdivisionResidual G x z).degree (some x) = G.degree x - 1 ∧
    (∀ v, v ≠ x → (subdivisionResidual G x z).degree (some v) = G.degree v) ∧
    (subdivisionResidual G x z).degree none = 1 ∧
    (∀ v, some v ∈ (subdivisionResidual G x z).support ↔ v ∈ G.support) ∧
    (activeVertices (subdivisionResidual G x z)).card = (activeVertices G).card + 1 ∧
    (subdivisionResidual G x z).edgeFinset.card = G.edgeFinset.card ∧
    edgeExcess (subdivisionResidual G x z) + 1 = edgeExcess G ∧
    (∀ w, (edgeSubdivision G x z).Adj (some x) w →
      Odd ((subdivisionResidual G x z).degree w)) :=
  ⟨edgeSubdivision_comap_some G x z, edgeSubdivision_degree_some G hxz,
    edgeSubdivision_degree_new G hxz.ne, subdivisionResidual_degree_left G hxz,
    subdivisionResidual_degree_other G hxz, subdivisionResidual_degree_new G hxz.ne,
    subdivisionResidual_old_support G hxz hx, subdivisionResidual_active_count G hxz hx,
    subdivisionResidual_edge_count G hxz, subdivisionResidual_edgeExcess G hxz hx,
    subdivisionResidual_original_neighbors_odd G hxz hodd⟩


theorem activeVertices_eq_oddVertices_of_all_odd (G : SimpleGraph V)
    (hodd : ∀ v, G.degree v ≠ 0 → Odd (G.degree v)) :
    activeVertices G = oddVertices G := by
  ext v
  simp only [mem_activeVertices, mem_oddVertices]
  refine ⟨hodd v, ?_⟩
  intro ho hz
  rw [hz] at ho
  norm_num at ho

theorem even_activeVertices_card_of_all_odd (G : SimpleGraph V)
    (hodd : ∀ v, G.degree v ≠ 0 → Odd (G.degree v)) : Even (activeVertices G).card := by
  rw [activeVertices_eq_oddVertices_of_all_odd G hodd]
  exact even_card_oddVertices G

theorem subdivisionResidual_active_half (G : SimpleGraph V) {x z : V}
    (hxz : G.Adj x z) (hx : 3 ≤ G.degree x)
    (hodd : ∀ v, G.degree v ≠ 0 → Odd (G.degree v)) :
    (activeVertices (subdivisionResidual G x z)).card / 2 = (activeVertices G).card / 2 := by
  rw [subdivisionResidual_active_count G hxz hx]
  obtain ⟨r, hr⟩ := even_activeVertices_card_of_all_odd G hodd
  omega

end Erdos583
end
end Source03_Erdos583_Subdivision
/- END Erdos583.Subdivision -/

/- BEGIN Erdos583.Basic; source SHA256 75536b1fd2aa51d71274693b1f50813221b8f3acb4035d96b5ba5b3131aae124 -/
section Source04_Erdos583_Basic




/-!
# Exact path-partition definitions for Erdős 583

These definitions use vertex-simple, nonempty walks and the existing edge-set
partition definition. They do not import the formal conjecture or any assumed
graph-decomposition bound.
-/

namespace Erdos583

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A subgraph consisting exactly of one nonempty vertex-simple path. -/
def IsNonemptyPathSubgraph (H : G.Subgraph) : Prop :=
  ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ ¬ p.Nil ∧ H = p.toSubgraph

/-- An edge partition into at most `q` nonempty vertex-simple paths. -/
def HasPathPartition (G : SimpleGraph V) (q : ℕ) : Prop :=
  ∃ D : Finset G.Subgraph,
    (∀ H ∈ D, IsNonemptyPathSubgraph H) ∧ IsDecomposition G D ∧ D.card ≤ q

/-- The same partition witness with its size bounded by a rational number. -/
def HasPathBound (G : SimpleGraph V) (b : ℚ) : Prop :=
  ∃ D : Finset G.Subgraph,
    (∀ H ∈ D, IsNonemptyPathSubgraph H) ∧ IsDecomposition G D ∧ (D.card : ℚ) ≤ b

theorem HasPathPartition.mono {q r : ℕ} (h : HasPathPartition G q) (hqr : q ≤ r) :
    HasPathPartition G r := by
  obtain ⟨D, hpath, hdec, hcard⟩ := h
  exact ⟨D, hpath, hdec, hcard.trans hqr⟩

theorem HasPathBound.mono {a b : ℚ} (h : HasPathBound G a) (hab : a ≤ b) :
    HasPathBound G b := by
  obtain ⟨D, hpath, hdec, hcard⟩ := h
  exact ⟨D, hpath, hdec, hcard.trans hab⟩

theorem hasPathPartition_bot : HasPathPartition (⊥ : SimpleGraph V) 0 := by
  refine ⟨∅, by simp, ?_, by simp⟩
  simp [SimpleGraph.IsDecomposition]

theorem isNonemptyPathSubgraph_subgraphOfAdj {u v : V} (h : G.Adj u v) :
    IsNonemptyPathSubgraph (G.subgraphOfAdj h) := by
  refine ⟨u, v, h.toWalk, h.isPath_toWalk, ?_, h.toSubgraph_toWalk.symm⟩
  simp [SimpleGraph.Adj.toWalk]

theorem exists_pathSubgraph_singleton_edge (e : Sym2 V) (he : e ∈ G.edgeSet) :
    ∃ H : G.Subgraph, IsNonemptyPathSubgraph H ∧ H.edgeSet = {e} := by
  induction e using Sym2.ind with
  | _ u v =>
    exact ⟨G.subgraphOfAdj he, isNonemptyPathSubgraph_subgraphOfAdj he,
      G.edgeSet_subgraphOfAdj he⟩

theorem hasPathPartition_of_edgeSet_singleton {u v : V} (h : G.Adj u v)
    (hE : G.edgeSet = {s(u, v)}) : HasPathPartition G 1 := by
  classical
  refine ⟨{G.subgraphOfAdj h}, ?_, ?_, by simp⟩
  · simpa using isNonemptyPathSubgraph_subgraphOfAdj h
  · simp [SimpleGraph.IsDecomposition, hE]

/-- Finite edge sets always admit a finite path partition, using each edge as a path. -/
theorem hasPathPartition_card_edgeSet [Fintype G.edgeSet] :
    HasPathPartition G (Fintype.card G.edgeSet) := by
  classical
  let f : G.edgeSet → G.Subgraph := fun e =>
    Classical.choose (exists_pathSubgraph_singleton_edge e.val e.property)
  have hf (e : G.edgeSet) : IsNonemptyPathSubgraph (f e) ∧ (f e).edgeSet = {e.val} :=
    Classical.choose_spec (exists_pathSubgraph_singleton_edge e.val e.property)
  refine ⟨Finset.univ.image f, ?_, ?_, ?_⟩
  · intro H hH
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hH
    exact (hf e).1
  · constructor
    · intro H hH J hJ hne
      obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hH
      obtain ⟨e', _, rfl⟩ := Finset.mem_image.mp hJ
      change Disjoint (f e).edgeSet (f e').edgeSet
      rw [(hf e).2, (hf e').2]
      apply Set.disjoint_left.mpr
      intro z hz hz'
      have hee : e = e' := Subtype.ext ((Set.mem_singleton_iff.mp hz).symm.trans
        (Set.mem_singleton_iff.mp hz'))
      exact hne (congrArg f hee)
    · ext z
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨H, _, hz⟩
        exact H.edgeSet_subset hz
      · intro hz
        refine ⟨f ⟨z, hz⟩, Finset.mem_image.mpr ⟨⟨z, hz⟩, Finset.mem_univ _, rfl⟩, ?_⟩
        rw [(hf ⟨z, hz⟩).2]
        exact Set.mem_singleton z
  · exact (Finset.card_image_le).trans_eq (Finset.card_univ)

theorem exists_hasPathPartition [Finite G.edgeSet] : ∃ q, HasPathPartition G q := by
  let := Fintype.ofFinite G.edgeSet
  exact ⟨Fintype.card G.edgeSet, hasPathPartition_card_edgeSet⟩

theorem IsNonemptyPathSubgraph.edgeSet_nonempty {H : G.Subgraph}
    (h : IsNonemptyPathSubgraph H) : H.edgeSet.Nonempty := by
  obtain ⟨u, v, p, _, hnil, rfl⟩ := h
  exact ⟨s(u, p.snd), p.toSubgraph_adj_snd hnil⟩

theorem hasPathPartition_zero_iff : HasPathPartition G 0 ↔ G = ⊥ := by
  classical
  constructor
  · rintro ⟨D, _, hdec, hcard⟩
    have hD : D = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
    have hE : G.edgeSet = ∅ := by
      simpa [hD] using hdec.2.symm
    exact SimpleGraph.edgeSet_eq_empty.mp hE
  · rintro rfl
    exact hasPathPartition_bot

theorem hasPathBound_iff_exists_partition {b : ℚ} :
    HasPathBound G b ↔ ∃ q : ℕ, HasPathPartition G q ∧ (q : ℚ) ≤ b := by
  constructor
  · rintro ⟨D, hp, hd, hc⟩
    exact ⟨D.card, ⟨D, hp, hd, le_rfl⟩, hc⟩
  · rintro ⟨q, ⟨D, hp, hd, hc⟩, hq⟩
    refine ⟨D, hp, hd, le_trans ?_ hq⟩
    exact_mod_cast hc

theorem hasPathBound_nat_iff {q : ℕ} :
    HasPathBound G (q : ℚ) ↔ HasPathPartition G q := by
  constructor
  · rintro ⟨D, hp, hd, hc⟩
    refine ⟨D, hp, hd, ?_⟩
    exact_mod_cast hc
  · intro h
    exact hasPathBound_iff_exists_partition.mpr ⟨q, h, le_rfl⟩

/-- The minimum path count exists because the graph has a finite edge set. -/
noncomputable def pn (G : SimpleGraph V) [Finite G.edgeSet] : ℕ := by
  classical
  exact Nat.find (exists_hasPathPartition (G := G))

theorem hasPathPartition_pn [Finite G.edgeSet] : HasPathPartition G (pn G) := by
  classical
  exact Nat.find_spec (exists_hasPathPartition (G := G))

theorem pn_le_iff [Finite G.edgeSet] {q : ℕ} : pn G ≤ q ↔ HasPathPartition G q := by
  classical
  constructor
  · exact HasPathPartition.mono hasPathPartition_pn
  · exact Nat.find_min' (exists_hasPathPartition (G := G))

theorem hasPathBound_iff_pn_le [Finite G.edgeSet] {b : ℚ} :
    HasPathBound G b ↔ (pn G : ℚ) ≤ b := by
  rw [hasPathBound_iff_exists_partition]
  constructor
  · rintro ⟨q, hq, hb⟩
    refine le_trans ?_ hb
    exact_mod_cast (pn_le_iff.mpr hq)
  · intro hb
    exact ⟨pn G, hasPathPartition_pn, hb⟩

theorem pn_eq_zero_iff [Finite G.edgeSet] : pn G = 0 ↔ G = ⊥ := by
  rw [← Nat.le_zero, pn_le_iff, hasPathPartition_zero_iff]

theorem pn_eq_one_of_edgeSet_singleton [Finite G.edgeSet] {u v : V}
    (h : G.Adj u v) (hE : G.edgeSet = {s(u, v)}) : pn G = 1 := by
  apply Nat.le_antisymm
  · exact pn_le_iff.mpr (hasPathPartition_of_edgeSet_singleton h hE)
  · apply Nat.one_le_iff_ne_zero.mpr
    intro hz
    have hG := pn_eq_zero_iff.mp hz
    simp [hG] at h

/-- The finite-vertex formulation follows from the more general finite-edge theorem. -/
theorem exists_hasPathPartition_of_finite_vertices [Finite V] :
    ∃ q, HasPathPartition G q :=
  exists_hasPathPartition

/-- A positive-length simple path has two distinct endpoints. -/
theorem IsNonemptyPathSubgraph.exists_distinct_endpoints {H : G.Subgraph}
    (h : IsNonemptyPathSubgraph H) :
    ∃ (u v : V) (p : G.Walk u v),
      u ≠ v ∧ p.IsPath ∧ ¬ p.Nil ∧ H = p.toSubgraph := by
  obtain ⟨u, v, p, hp, hnil, hH⟩ := h
  exact ⟨u, v, p, hp.nil_iff_eq.not.mp hnil, hp, hnil, hH⟩

end Erdos583
end Source04_Erdos583_Basic
/- END Erdos583.Basic -/

/- BEGIN Erdos583.Packing; source SHA256 77242eddede641d6d555df8a5ae7e4080a43586a4fbf192267ea03b5f225115d -/
section Source05_Erdos583_Packing


/-! Finite greedy packing for the graph reductions. -/

namespace Erdos583

/-- A family with at most `D` intersecting members at each index has a disjoint
subfamily of size at least the total number of indices divided by `D`. -/
theorem exists_disjoint_subfamily {ι V : Type*} [DecidableEq ι] [DecidableEq V]
    (S : Finset ι) (B : ι → Finset V) (D : ℕ)
    (hnonempty : ∀ i ∈ S, (B i).Nonempty)
    (hconflict : ∀ i ∈ S, (S.filter fun j => ¬ Disjoint (B i) (B j)).card ≤ D) :
    ∃ T ⊆ S, (T : Set ι).Pairwise (fun i j => Disjoint (B i) (B j)) ∧ S.card ≤ D * T.card := by
  classical
  revert hnonempty hconflict
  refine Finset.strongInductionOn S ?_
  intro S ih hn hc
  by_cases hs : S = ∅
  · subst S
    exact ⟨∅, by simp, by simp, by simp⟩
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
  let C := S.filter fun j => ¬ Disjoint (B i) (B j)
  have hCS : C ⊆ S := Finset.filter_subset _ _
  have hiC : i ∈ C := by
    obtain ⟨v, hv⟩ := hn i hi
    exact Finset.mem_filter.mpr ⟨hi, fun h => (Finset.disjoint_left.mp h) hv hv⟩
  have hsplit : (S \ C).card + C.card = S.card :=
    Finset.card_sdiff_add_card_eq_card hCS
  have hsub : S \ C ⊆ S := Finset.sdiff_subset
  have hstrict : S \ C ⊂ S := by
    refine ⟨hsub, ?_⟩
    intro hSS
    exact (Finset.mem_sdiff.mp (hSS hi)).2 hiC
  have hnew : ∀ j ∈ S \ C,
      ((S \ C).filter fun l => ¬ Disjoint (B j) (B l)).card ≤ D := by
    intro j hj
    apply le_trans (Finset.card_le_card ?_) (hc j (hsub hj))
    intro l hl
    obtain ⟨hlS, hld⟩ := Finset.mem_filter.mp hl
    exact Finset.mem_filter.mpr ⟨hsub hlS, hld⟩
  obtain ⟨T, hT, hp, hcard⟩ := ih (S \ C) hstrict (fun j hj => hn j (hsub hj)) hnew
  have hiT : i ∉ T := by
    intro hit
    exact (Finset.mem_sdiff.mp (hT hit)).2 hiC
  have hiDis (j : ι) (hj : j ∈ T) : Disjoint (B i) (B j) := by
    have hjs := hT hj
    by_contra hnd
    exact (Finset.mem_sdiff.mp hjs).2
      (Finset.mem_filter.mpr ⟨hsub hjs, hnd⟩)
  refine ⟨insert i T, ?_, ?_, ?_⟩
  · intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hi
    · exact hsub (hT hj)
  · intro j hj l hl hjl
    by_cases hji : j = i
    · subst j
      have hlT : l ∈ T := (Finset.mem_insert.mp hl).resolve_left (Ne.symm hjl)
      exact hiDis l hlT
    · have hjT : j ∈ T := (Finset.mem_insert.mp hj).resolve_left hji
      by_cases hli : l = i
      · subst l
        exact (hiDis j hjT).symm
      · have hlT : l ∈ T := (Finset.mem_insert.mp hl).resolve_left hli
        exact hp hjT hlT hjl
  · have hCbound : C.card ≤ D := hc i hi
    rw [Finset.card_insert_of_notMem hiT]
    nlinarith

/-- Bounded member size and bounded incidence imply the required conflict bound. -/
theorem exists_disjoint_subfamily_of_incidence {ι V : Type*}
    [DecidableEq ι] [DecidableEq V] (S : Finset ι) (B : ι → Finset V) (s d : ℕ)
    (hnonempty : ∀ i ∈ S, (B i).Nonempty)
    (hsize : ∀ i ∈ S, (B i).card ≤ s)
    (hincidence : ∀ v, (S.filter fun i => v ∈ B i).card ≤ d) :
    ∃ T ⊆ S, (T : Set ι).Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      S.card ≤ (s * d) * T.card := by
  classical
  apply exists_disjoint_subfamily S B (s * d) hnonempty
  intro i hi
  have heq : (S.filter fun j => ¬ Disjoint (B i) (B j)) =
      (B i).biUnion (fun v => S.filter fun j => v ∈ B j) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hj, hnd⟩
      rw [Finset.disjoint_left] at hnd
      push Not at hnd
      obtain ⟨v, hvi, hvj⟩ := hnd
      exact ⟨v, hvi, hj, hvj⟩
    · rintro ⟨v, hvi, hj, hvj⟩
      exact ⟨hj, fun h => (Finset.disjoint_left.mp h) hvi hvj⟩
  rw [heq]
  calc
    ((B i).biUnion fun v => S.filter fun j => v ∈ B j).card ≤
        (B i).card * d :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun v _ => hincidence v)
    _ ≤ s * d := Nat.mul_le_mul_right d (hsize i hi)

end Erdos583
end Source05_Erdos583_Packing
/- END Erdos583.Packing -/

/- BEGIN Erdos583.CorePacking; source SHA256 2e21c9e9a420a04ed050bab887de2d2d1e1c27cff7670e1e2621642bf050951a -/
section Source06_Erdos583_CorePacking



/-! Actual graph neighborhood packings for the bounded-even-neighbor core. -/

noncomputable section

namespace Erdos583

open SimpleGraph
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

def closedNeighborhood (G : SimpleGraph V) (x : V) : Finset V :=
  insert x (G.neighborFinset x)

@[simp] theorem mem_closedNeighborhood (G : SimpleGraph V) (x v : V) :
    v ∈ closedNeighborhood G x ↔ v = x ∨ G.Adj x v := by
  simp [closedNeighborhood]

/-- The full-star centers in the written core argument. -/
def highEvenCenters (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter fun x => Even (G.degree x) ∧ 4 ≤ G.degree x ∧
    ∀ v, G.Adj x v → Even (G.degree v)

@[simp] theorem mem_highEvenCenters (G : SimpleGraph V) (x : V) :
    x ∈ highEvenCenters G ↔ Even (G.degree x) ∧ 4 ≤ G.degree x ∧
      ∀ v, G.Adj x v → Even (G.degree v) := by
  simp [highEvenCenters]

theorem degree_eq_evenNeighborCount_of_clean (G : SimpleGraph V) (x : V)
    (hclean : ∀ v, G.Adj x v → Even (G.degree v)) :
    G.degree x = evenNeighborCount G x := by
  have hs : evenNeighbors G x = G.neighborFinset x := by
    ext v
    simp only [mem_evenNeighbors, mem_neighborFinset]
    exact ⟨And.left, fun h => ⟨h, hclean v h⟩⟩
  unfold evenNeighborCount
  rw [hs, card_neighborFinset_eq_degree]

/-- A conflicting even center is the center, a neighbor, or a two-step even
neighbor. The repeated center is erased from each two-step list. -/
theorem closedNeighborhood_conflicts_subset (G : SimpleGraph V) (A : Finset V) (x : V)
    (hEven : ∀ y ∈ A, Even (G.degree y)) :
    (A.filter fun y => ¬ Disjoint (closedNeighborhood G x) (closedNeighborhood G y)) ⊆
      insert x (G.neighborFinset x ∪ (G.neighborFinset x).biUnion
        (fun v => (evenNeighbors G v).erase x)) := by
  classical
  intro y hy
  obtain ⟨hyA, hconf⟩ := Finset.mem_filter.mp hy
  by_cases hyx : y = x
  · simp [hyx]
  obtain ⟨v, hvx, hvy⟩ := Finset.not_disjoint_iff.mp hconf
  apply Finset.mem_insert.mpr
  right
  rcases (mem_closedNeighborhood G x v).mp hvx with hvx | hvx
  · subst v
    rcases (mem_closedNeighborhood G y x).mp hvy with hxy | hxy
    · exact (hyx hxy.symm).elim
    · exact Finset.mem_union_left _ ((G.mem_neighborFinset x y).mpr hxy.symm)
  · rcases (mem_closedNeighborhood G y v).mp hvy with hvy | hvy
    · subst v
      exact Finset.mem_union_left _ ((G.mem_neighborFinset x y).mpr hvx)
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨v, (G.mem_neighborFinset x v).mpr hvx, ?_⟩
      exact Finset.mem_erase.mpr ⟨hyx,
        (mem_evenNeighbors G v y).mpr ⟨hvy.symm, hEven y hyA⟩⟩

theorem closedNeighborhood_conflict_bound (G : SimpleGraph V) (A : Finset V)
    (K : ℕ) (hcap : ∀ v, evenNeighborCount G v ≤ K)
    (hEven : ∀ y ∈ A, Even (G.degree y)) (x : V) (hx : x ∈ A)
    (hclean : ∀ v, G.Adj x v → Even (G.degree v)) :
    (A.filter fun y => ¬ Disjoint (closedNeighborhood G x) (closedNeighborhood G y)).card ≤
      K ^ 2 + 1 := by
  classical
  have hd : G.degree x ≤ K := by
    rw [degree_eq_evenNeighborCount_of_clean G x hclean]
    exact hcap x
  have hs : (∑ v ∈ G.neighborFinset x, ((evenNeighbors G v).erase x).card) +
      G.degree x ≤ G.degree x * K := by
    calc
      _ = ∑ v ∈ G.neighborFinset x, (((evenNeighbors G v).erase x).card + 1) := by
        simp [Finset.sum_add_distrib, card_neighborFinset_eq_degree]
      _ ≤ ∑ _v ∈ G.neighborFinset x, K := by
        apply Finset.sum_le_sum
        intro v hv
        have hmem : x ∈ evenNeighbors G v :=
          (mem_evenNeighbors G v x).mpr ⟨((G.mem_neighborFinset x v).mp hv).symm, hEven x hx⟩
        rw [Finset.card_erase_add_one hmem]
        exact hcap v
      _ = G.degree x * K := by simp [card_neighborFinset_eq_degree]
  have hbound := Finset.card_le_card (closedNeighborhood_conflicts_subset G A x hEven)
  have hi := Finset.card_insert_le x
    (G.neighborFinset x ∪ (G.neighborFinset x).biUnion (fun v => (evenNeighbors G v).erase x))
  have hu := Finset.card_union_le (G.neighborFinset x)
    ((G.neighborFinset x).biUnion (fun v => (evenNeighbors G v).erase x))
  have hb := Finset.card_biUnion_le (s := G.neighborFinset x)
    (t := fun v => (evenNeighbors G v).erase x)
  rw [card_neighborFinset_eq_degree] at hu
  have hm := Nat.mul_le_mul_right K hd
  rw [pow_two]
  omega

/-- An actual family of full-star centers with pairwise disjoint closed
neighborhoods, with the quantitative factor used in the core proof. -/
theorem exists_highEvenCenters_packing (G : SimpleGraph V) (K : ℕ)
    (hcap : ∀ v, evenNeighborCount G v ≤ K) :
    ∃ R ⊆ highEvenCenters G,
      (R : Set V).Pairwise (fun x y => Disjoint (closedNeighborhood G x) (closedNeighborhood G y)) ∧
      (highEvenCenters G).card ≤ (K ^ 2 + 1) * R.card := by
  classical
  apply exists_disjoint_subfamily (highEvenCenters G) (closedNeighborhood G) (K ^ 2 + 1)
  · intro x _
    exact ⟨x, by simp⟩
  · intro x hx
    apply closedNeighborhood_conflict_bound G (highEvenCenters G) K hcap
    · intro y hy
      exact ((mem_highEvenCenters G y).mp hy).1
    · exact hx
    · exact ((mem_highEvenCenters G x).mp hx).2.2

/-- Undirected original edges with both endpoints in a chosen degree-two set. -/
def degreeTwoPairs (G : SimpleGraph V) (B : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ B

@[simp] theorem mem_degreeTwoPairs (G : SimpleGraph V) (B : Finset V) (e : Sym2 V) :
    e ∈ degreeTwoPairs G B ↔ e ∈ G.edgeFinset ∧ ∀ v ∈ e, v ∈ B := by
  simp [degreeTwoPairs]

def pairClosedSet (G : SimpleGraph V) (e : Sym2 V) : Finset V :=
  e.toFinset.biUnion (closedNeighborhood G)

@[simp] theorem mem_pairClosedSet (G : SimpleGraph V) (e : Sym2 V) (v : V) :
    v ∈ pairClosedSet G e ↔ ∃ w ∈ e, v = w ∨ G.Adj w v := by
  simp [pairClosedSet, Sym2.mem_toFinset]

theorem pairClosedSet_nonempty (G : SimpleGraph V) (e : Sym2 V) :
    (pairClosedSet G e).Nonempty := by
  induction e using Sym2.inductionOn with
  | _ x y => exact ⟨x, (mem_pairClosedSet G s(x,y) x).mpr ⟨x, by simp, Or.inl rfl⟩⟩

theorem card_pairClosedSet_le (G : SimpleGraph V) (B : Finset V)
    (hB : ∀ v ∈ B, G.degree v = 2) (e : Sym2 V) (he : e ∈ degreeTwoPairs G B) :
    (pairClosedSet G e).card ≤ 4 := by
  classical
  induction e using Sym2.inductionOn with
  | _ x y =>
    obtain ⟨hedge, hend⟩ := (mem_degreeTwoPairs G B s(x,y)).mp he
    have hxy : G.Adj x y := by simpa using hedge
    have hx := hB x (hend x (by simp))
    have hy := hB y (hend y (by simp))
    have hcx : (closedNeighborhood G x).card = 3 := by
      simp [closedNeighborhood, card_neighborFinset_eq_degree, hx]
    have hcy : (closedNeighborhood G y).card = 3 := by
      simp [closedNeighborhood, card_neighborFinset_eq_degree, hy]
    have hsub : ({x,y} : Finset V) ⊆ closedNeighborhood G x ∩ closedNeighborhood G y := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · simp [hxy.symm]
      · simp [hxy]
    have hc := Finset.card_le_card hsub
    have hn : ({x,y} : Finset V).card = 2 := by simp [hxy.ne]
    rw [hn] at hc
    have hu := Finset.card_union_add_card_inter (closedNeighborhood G x) (closedNeighborhood G y)
    have hp : pairClosedSet G s(x,y) = closedNeighborhood G x ∪ closedNeighborhood G y := by
      simp [pairClosedSet, Sym2.toFinset_mk_eq]
    rw [hp]
    omega

private theorem incidenceFinset_membership (G : SimpleGraph V) (v : V) (e : Sym2 V) :
    e ∈ G.incidenceFinset v ↔ e ∈ G.edgeFinset ∧ v ∈ e := by
  classical
  rw [G.incidenceFinset_eq_filter]
  exact Finset.mem_filter

theorem degreeTwoPairs_incident_bound (G : SimpleGraph V) (B : Finset V)
    (hB : ∀ v ∈ B, G.degree v = 2) (v : V) :
    ((degreeTwoPairs G B).filter fun e => v ∈ e).card ≤ 2 := by
  classical
  by_cases hvB : v ∈ B
  · have hs : ((degreeTwoPairs G B).filter fun e => v ∈ e) ⊆ G.incidenceFinset v := by
      intro e he
      obtain ⟨he, hv⟩ := Finset.mem_filter.mp he
      exact (incidenceFinset_membership G v e).mpr
        ⟨((mem_degreeTwoPairs G B e).mp he).1, hv⟩
    have hc := Finset.card_le_card hs
    simpa [hB v hvB] using hc
  · have he : ((degreeTwoPairs G B).filter fun e => v ∈ e) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨he, hv⟩ := Finset.mem_filter.mp he
      exact hvB (((mem_degreeTwoPairs G B e).mp he).2 v hv)
    simp [he]

theorem degreeTwoPairs_closed_incidence_bound (G : SimpleGraph V) (B : Finset V)
    (hB : ∀ v ∈ B, G.degree v = 2) (K : ℕ)
    (hcap : ∀ v, evenNeighborCount G v ≤ K) (v : V) :
    ((degreeTwoPairs G B).filter fun e => v ∈ pairClosedSet G e).card ≤ K + 2 := by
  classical
  let D := (degreeTwoPairs G B).filter fun e => v ∈ e
  let R : V → Finset (Sym2 V) := fun w =>
    if w ∈ B then (G.incidenceFinset w).erase s(v,w) else ∅
  have hR : ∀ w ∈ evenNeighbors G v, (R w).card ≤ 1 := by
    intro w hw
    by_cases hwB : w ∈ B
    · have hvw := ((mem_evenNeighbors G v w).mp hw).1
      have hm : s(v,w) ∈ G.incidenceFinset w := by
        exact (G.mem_incidenceFinset w s(v,w)).mpr (G.mk'_mem_incidenceSet_right_iff.mpr hvw)
      simp only [R, if_pos hwB]
      rw [Finset.card_erase_of_mem hm, card_incidenceFinset_eq_degree, hB w hwB]
    · simp [R, hwB]
  have hsub : ((degreeTwoPairs G B).filter fun e => v ∈ pairClosedSet G e) ⊆
      D ∪ (evenNeighbors G v).biUnion R := by
    intro e he
    obtain ⟨he, hv⟩ := Finset.mem_filter.mp he
    obtain ⟨hedge, hend⟩ := (mem_degreeTwoPairs G B e).mp he
    by_cases hve : v ∈ e
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, hve⟩)
    · obtain ⟨w, hwe, hvw⟩ := (mem_pairClosedSet G e v).mp hv
      have hwB := hend w hwe
      have hvw' : G.Adj v w := by
        rcases hvw with rfl | hvw
        · exact (hve hwe).elim
        · exact hvw.symm
      have hwN : w ∈ evenNeighbors G v :=
        (mem_evenNeighbors G v w).mpr ⟨hvw', by rw [hB w hwB]; decide⟩
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨w, hwN, ?_⟩
      simp only [R, if_pos hwB]
      apply Finset.mem_erase.mpr
      refine ⟨?_, (incidenceFinset_membership G w e).mpr ⟨hedge, hwe⟩⟩
      intro heq
      apply hve
      rw [heq]
      simp
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le D ((evenNeighbors G v).biUnion R)
  have hb := Finset.card_biUnion_le_card_mul (evenNeighbors G v) R 1 hR
  have hd : D.card ≤ 2 := degreeTwoPairs_incident_bound G B hB v
  have hk := hcap v
  change (evenNeighbors G v).card ≤ K at hk
  omega

theorem exists_degreeTwoPairs_packing (G : SimpleGraph V) (B : Finset V)
    (hB : ∀ v ∈ B, G.degree v = 2) (K : ℕ)
    (hcap : ∀ v, evenNeighborCount G v ≤ K) :
    ∃ Q ⊆ degreeTwoPairs G B,
      (Q : Set (Sym2 V)).Pairwise (fun e f => Disjoint (pairClosedSet G e) (pairClosedSet G f)) ∧
      (degreeTwoPairs G B).card ≤ (4 * (K + 2)) * Q.card := by
  classical
  apply exists_disjoint_subfamily_of_incidence (degreeTwoPairs G B) (pairClosedSet G) 4 (K + 2)
  · intro e _; exact pairClosedSet_nonempty G e
  · exact card_pairClosedSet_le G B hB
  · exact degreeTwoPairs_closed_incidence_bound G B hB K hcap

/-- Both actual graph packings used by the core argument. This theorem only
selects disjoint reduction supports; it asserts no path restoration. -/
theorem bounded_even_core_packings (G : SimpleGraph V) (B : Finset V) (K : ℕ)
    (hB : ∀ v ∈ B, G.degree v = 2)
    (hcap : ∀ v, evenNeighborCount G v ≤ K) :
    (∃ R ⊆ highEvenCenters G,
      (R : Set V).Pairwise (fun x y => Disjoint (closedNeighborhood G x) (closedNeighborhood G y)) ∧
      (highEvenCenters G).card ≤ (K ^ 2 + 1) * R.card) ∧
    (∃ Q ⊆ degreeTwoPairs G B,
      (Q : Set (Sym2 V)).Pairwise (fun e f => Disjoint (pairClosedSet G e) (pairClosedSet G f)) ∧
      (degreeTwoPairs G B).card ≤ (4 * (K + 2)) * Q.card) :=
  ⟨exists_highEvenCenters_packing G K hcap, exists_degreeTwoPairs_packing G B hB K hcap⟩

end Erdos583
end
end Source06_Erdos583_CorePacking
/- END Erdos583.CorePacking -/

/- BEGIN Erdos583.CoreCounts; source SHA256 90b664543b2a5d1bed5f5c3e8f5f2a55c18ae0cffba7f4ca6b9f8ffedc77d705 -/
section Source07_Erdos583_CoreCounts



/-! Actual vertex, contact and degree-two edge counts for the bounded-even core. -/

noncomputable section

namespace Erdos583

open SimpleGraph
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

def badEvenVertices (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter fun v => Even (G.degree v) ∧ ∃ w, G.Adj v w ∧ Odd (G.degree w)

@[simp] theorem mem_badEvenVertices (G : SimpleGraph V) (v : V) :
    v ∈ badEvenVertices G ↔ Even (G.degree v) ∧ ∃ w, G.Adj v w ∧ Odd (G.degree w) := by
  simp [badEvenVertices]

theorem badEvenVertices_subset_contacts (G : SimpleGraph V) :
    badEvenVertices G ⊆ (oddVertices G).biUnion (evenNeighbors G) := by
  classical
  intro v hv
  obtain ⟨he, w, hadj, ho⟩ := (mem_badEvenVertices G v).mp hv
  exact Finset.mem_biUnion.mpr ⟨w, (mem_oddVertices G w).mpr ho,
    (mem_evenNeighbors G w v).mpr ⟨hadj.symm, he⟩⟩

theorem badEvenVertices_card_le (G : SimpleGraph V) (K : ℕ)
    (hcap : ∀ v, evenNeighborCount G v ≤ K) :
    (badEvenVertices G).card ≤ K * (oddVertices G).card := by
  have hs := Finset.card_le_card (badEvenVertices_subset_contacts G)
  have hb := Finset.card_biUnion_le_card_mul (oddVertices G) (evenNeighbors G) K
    (fun v _ => hcap v)
  exact hs.trans (by simpa [Nat.mul_comm] using hb)

def cleanDegreeTwoVertices (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter fun v => G.degree v = 2 ∧ ∀ w, G.Adj v w → Even (G.degree w)

@[simp] theorem mem_cleanDegreeTwoVertices (G : SimpleGraph V) (v : V) :
    v ∈ cleanDegreeTwoVertices G ↔ G.degree v = 2 ∧
      ∀ w, G.Adj v w → Even (G.degree w) := by
  simp [cleanDegreeTwoVertices]

def componentVertices (G : SimpleGraph V) (C : G.ConnectedComponent) : Finset V :=
  Finset.univ.filter fun v => G.connectedComponentMk v = C

@[simp] theorem mem_componentVertices (G : SimpleGraph V) (C : G.ConnectedComponent) (v : V) :
    v ∈ componentVertices G C ↔ G.connectedComponentMk v = C := by
  simp [componentVertices]

def triangleComponents (G : SimpleGraph V) : Finset G.ConnectedComponent :=
  Finset.univ.filter fun C => (componentVertices G C).card = 3 ∧
    ∀ v ∈ componentVertices G C, G.degree v = 2

def triangleVertices (G : SimpleGraph V) : Finset V :=
  (triangleComponents G).biUnion (componentVertices G)

@[simp] theorem mem_triangleComponents (G : SimpleGraph V) (C : G.ConnectedComponent) :
    C ∈ triangleComponents G ↔ (componentVertices G C).card = 3 ∧
      ∀ v ∈ componentVertices G C, G.degree v = 2 := by
  simp [triangleComponents]

theorem componentVertices_pairwiseDisjoint (G : SimpleGraph V) :
    (Set.univ : Set G.ConnectedComponent).PairwiseDisjoint (componentVertices G) := by
  classical
  intro C _ D _ hne
  apply Finset.disjoint_left.mpr
  intro v hvC hvD
  exact hne (((mem_componentVertices G C v).mp hvC).symm.trans
    ((mem_componentVertices G D v).mp hvD))

theorem triangleVertices_card (G : SimpleGraph V) :
    (triangleVertices G).card = 3 * (triangleComponents G).card := by
  classical
  unfold triangleVertices
  rw [Finset.card_biUnion]
  · rw [Finset.sum_const_nat (m := 3)]
    · omega
    · intro C hC
      exact ((mem_triangleComponents G C).mp hC).1
  · intro C hC D hD hne
    exact componentVertices_pairwiseDisjoint G (by simp) (by simp) hne

theorem triangleVertices_closed (G : SimpleGraph V) {v w : V}
    (hv : v ∈ triangleVertices G) (hvw : G.Adj v w) : w ∈ triangleVertices G := by
  classical
  obtain ⟨C, hC, hvC⟩ := Finset.mem_biUnion.mp hv
  apply Finset.mem_biUnion.mpr
  refine ⟨C, hC, (mem_componentVertices G C w).mpr ?_⟩
  exact (ConnectedComponent.sound hvw.reachable).symm.trans ((mem_componentVertices G C v).mp hvC)

theorem triangleVertices_no_crossing (G : SimpleGraph V) {v w : V}
    (hv : v ∉ triangleVertices G) (hw : w ∈ triangleVertices G) : ¬ G.Adj v w := by
  intro h
  exact hv (triangleVertices_closed G hw h.symm)

theorem triangleVertices_subset_cleanDegreeTwo (G : SimpleGraph V) :
    triangleVertices G ⊆ cleanDegreeTwoVertices G := by
  classical
  intro v hv
  obtain ⟨C, hC, hvC⟩ := Finset.mem_biUnion.mp hv
  have hdeg := ((mem_triangleComponents G C).mp hC).2
  apply (mem_cleanDegreeTwoVertices G v).mpr
  refine ⟨hdeg v hvC, ?_⟩
  intro w hw
  have hwC : w ∈ componentVertices G C :=
    (mem_componentVertices G C w).mpr
      ((ConnectedComponent.sound hw.reachable).symm.trans ((mem_componentVertices G C v).mp hvC))
  rw [hdeg w hwC]
  decide

/-- The support of a selected triangle component really is a clique. Together
with its cardinality three and component closure, this identifies isolated K3. -/
theorem triangleComponent_adj (G : SimpleGraph V) (C : G.ConnectedComponent)
    (hC : C ∈ triangleComponents G) {v w : V}
    (hv : v ∈ componentVertices G C) (hw : w ∈ componentVertices G C) (hne : v ≠ w) :
    G.Adj v w := by
  classical
  obtain ⟨hcard, hdeg⟩ := (mem_triangleComponents G C).mp hC
  have hs : G.neighborFinset v ⊆ (componentVertices G C).erase v := by
    intro z hz
    have hvz := (G.mem_neighborFinset v z).mp hz
    exact Finset.mem_erase.mpr ⟨hvz.ne.symm,
      (mem_componentVertices G C z).mpr
        ((ConnectedComponent.sound hvz.reachable).symm.trans ((mem_componentVertices G C v).mp hv))⟩
  have heq : G.neighborFinset v = (componentVertices G C).erase v := by
    apply Finset.eq_of_subset_of_card_le hs
    rw [Finset.card_erase_of_mem hv, hcard, card_neighborFinset_eq_degree, hdeg v hv]
  apply (G.mem_neighborFinset v w).mp
  rw [heq]
  exact Finset.mem_erase.mpr ⟨hne.symm, hw⟩

def noInternalNeighbors (G : SimpleGraph V) (B : Finset V) : Finset V :=
  B.filter fun v => ∀ w ∈ B, ¬ G.Adj v w

omit [Fintype V] in
private theorem adjacency_double_count (G : SimpleGraph V) (S C : Finset V) :
    (∑ v ∈ S, (C.filter (G.Adj v)).card) =
      ∑ w ∈ C, (S.filter fun v => G.Adj v w).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

/-- Degree-two vertices with no internal neighbor send both incident edges into
the permitted outside set. The contact cap counts them without choosing edges. -/
theorem noInternalNeighbors_card_bound (G : SimpleGraph V) (B C : Finset V) (K : ℕ)
    (hB : ∀ v ∈ B, G.degree v = 2)
    (hcap : ∀ v, evenNeighborCount G v ≤ K)
    (hneighbors : ∀ v ∈ B, ∀ w, G.Adj v w → w ∈ B ∪ C) :
    2 * (noInternalNeighbors G B).card ≤ K * C.card := by
  classical
  let S := noInternalNeighbors G B
  have hsB : S ⊆ B := Finset.filter_subset _ _
  have hn : ∀ v ∈ S, C.filter (G.Adj v) = G.neighborFinset v := by
    intro v hv
    have hvB := hsB hv
    have hvno := (Finset.mem_filter.mp hv).2
    ext w
    simp only [Finset.mem_filter, mem_neighborFinset]
    constructor
    · exact And.right
    · intro hadj
      have hw := hneighbors v hvB w hadj
      exact ⟨(Finset.mem_union.mp hw).resolve_left (fun hwB => hvno w hwB hadj), hadj⟩
  have hleft : (∑ v ∈ S, (C.filter (G.Adj v)).card) = 2 * S.card := by
    calc
      _ = ∑ v ∈ S, 2 := Finset.sum_congr rfl (fun v hv => by
        rw [hn v hv, card_neighborFinset_eq_degree, hB v (hsB hv)])
      _ = _ := by simp [Nat.mul_comm]
  have hright : (∑ w ∈ C, (S.filter fun v => G.Adj v w).card) ≤ K * C.card := by
    calc
      _ ≤ ∑ _w ∈ C, K := by
        apply Finset.sum_le_sum
        intro w _
        apply le_trans (Finset.card_le_card ?_) (hcap w)
        intro v hv
        obtain ⟨hvS, hvw⟩ := Finset.mem_filter.mp hv
        exact (mem_evenNeighbors G w v).mpr
          ⟨hvw.symm, by rw [hB v (hsB hvS)]; decide⟩
      _ = _ := by simp [Nat.mul_comm]
  rw [← hleft, adjacency_double_count]
  exact hright

theorem internallyAdjacent_vertices_covered (G : SimpleGraph V) (B : Finset V) :
    B \ noInternalNeighbors G B ⊆ (degreeTwoPairs G B).biUnion Sym2.toFinset := by
  classical
  intro v hv
  obtain ⟨hvB, hvS⟩ := Finset.mem_sdiff.mp hv
  have hex : ∃ w ∈ B, G.Adj v w := by
    by_contra h
    push Not at h
    exact hvS (Finset.mem_filter.mpr ⟨hvB, h⟩)
  obtain ⟨w, hwB, hvw⟩ := hex
  apply Finset.mem_biUnion.mpr
  refine ⟨s(v,w), ?_, by simp [Sym2.mem_toFinset]⟩
  apply (mem_degreeTwoPairs G B s(v,w)).mpr
  refine ⟨by simpa using hvw, ?_⟩
  intro z hz
  rcases Sym2.mem_iff.mp hz with rfl | rfl
  · exact hvB
  · exact hwB

/-- The candidate-edge lower bound in integral form, before classifying the
outside set as high-even or bad-even vertices. -/
theorem degreeTwoPairs_lower_bound (G : SimpleGraph V) (B C : Finset V) (K : ℕ)
    (hB : ∀ v ∈ B, G.degree v = 2)
    (hcap : ∀ v, evenNeighborCount G v ≤ K)
    (hneighbors : ∀ v ∈ B, ∀ w, G.Adj v w → w ∈ B ∪ C) :
    2 * B.card ≤ 4 * (degreeTwoPairs G B).card + K * C.card := by
  classical
  have hs := noInternalNeighbors_card_bound G B C K hB hcap hneighbors
  have hc := Finset.card_le_card (internallyAdjacent_vertices_covered G B)
  have hp := Finset.card_biUnion_le_card_mul (degreeTwoPairs G B) Sym2.toFinset 2
    (fun e he => le_of_eq (G.card_toFinset_mem_edgeFinset
      ⟨e, ((mem_degreeTwoPairs G B e).mp he).1⟩))
  have hsum := Finset.card_sdiff_add_card_eq_card
    (show noInternalNeighbors G B ⊆ B from Finset.filter_subset _ _)
  omega

theorem nonisolatedEvenVertices_partition (G : SimpleGraph V) :
    nonisolatedEvenVertices G =
      highEvenCenters G ∪ badEvenVertices G ∪ cleanDegreeTwoVertices G := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨he, hne⟩ := (mem_nonisolatedEvenVertices G v).mp hv
    by_cases hb : v ∈ badEvenVertices G
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hb)
    · have hclean : ∀ w, G.Adj v w → Even (G.degree w) := by
        intro w hw
        by_contra hn
        exact hb ((mem_badEvenVertices G v).mpr ⟨he, w, hw, Nat.not_even_iff_odd.mp hn⟩)
      by_cases hd : G.degree v = 2
      · exact Finset.mem_union_right _ ((mem_cleanDegreeTwoVertices G v).mpr ⟨hd, hclean⟩)
      · have hge : 4 ≤ G.degree v := by obtain ⟨j, hj⟩ := he; omega
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          ((mem_highEvenCenters G v).mpr ⟨he, hge, hclean⟩))
  · intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_union.mp hv with ha | hb
      · obtain ⟨he, hge, _⟩ := (mem_highEvenCenters G v).mp ha
        exact (mem_nonisolatedEvenVertices G v).mpr ⟨he, by omega⟩
      · obtain ⟨he, w, hadj, _⟩ := (mem_badEvenVertices G v).mp hb
        exact (mem_nonisolatedEvenVertices G v).mpr ⟨he, Nat.ne_of_gt hadj.degree_pos_left⟩
    · have hd := ((mem_cleanDegreeTwoVertices G v).mp hv).1
      apply (mem_nonisolatedEvenVertices G v).mpr
      rw [hd]
      decide

theorem disjoint_high_bad (G : SimpleGraph V) :
    Disjoint (highEvenCenters G) (badEvenVertices G) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v ha hb
  have hclean := ((mem_highEvenCenters G v).mp ha).2.2
  obtain ⟨_, w, hadj, ho⟩ := (mem_badEvenVertices G v).mp hb
  exact (Nat.not_even_iff_odd.mpr ho) (hclean w hadj)

theorem disjoint_high_bad_cleanDegreeTwo (G : SimpleGraph V) :
    Disjoint (highEvenCenters G ∪ badEvenVertices G) (cleanDegreeTwoVertices G) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hc
  obtain ⟨hd, hclean⟩ := (mem_cleanDegreeTwoVertices G v).mp hc
  rcases Finset.mem_union.mp hv with ha | hb
  · have hge := ((mem_highEvenCenters G v).mp ha).2.1
    omega
  · obtain ⟨_, w, hadj, ho⟩ := (mem_badEvenVertices G v).mp hb
    exact (Nat.not_even_iff_odd.mpr ho) (hclean w hadj)

def coreDegreeTwoVertices (G : SimpleGraph V) : Finset V :=
  cleanDegreeTwoVertices G \ triangleVertices G

theorem coreDegreeTwoVertices_degree (G : SimpleGraph V) (v : V)
    (hv : v ∈ coreDegreeTwoVertices G) : G.degree v = 2 :=
  ((mem_cleanDegreeTwoVertices G v).mp (Finset.mem_sdiff.mp hv).1).1

theorem even_core_class_count (G : SimpleGraph V) :
    (nonisolatedEvenVertices G).card = (highEvenCenters G).card +
      (badEvenVertices G).card + (coreDegreeTwoVertices G).card +
      3 * (triangleComponents G).card := by
  classical
  have hs := Finset.card_sdiff_add_card_eq_card (triangleVertices_subset_cleanDegreeTwo G)
  change (coreDegreeTwoVertices G).card + (triangleVertices G).card =
    (cleanDegreeTwoVertices G).card at hs
  rw [triangleVertices_card] at hs
  rw [nonisolatedEvenVertices_partition,
    Finset.card_union_of_disjoint (disjoint_high_bad_cleanDegreeTwo G),
    Finset.card_union_of_disjoint (disjoint_high_bad G)]
  omega

theorem coreDegreeTwoVertices_neighbors (G : SimpleGraph V) (v : V)
    (hv : v ∈ coreDegreeTwoVertices G) (w : V) (hvw : G.Adj v w) :
    w ∈ coreDegreeTwoVertices G ∪ (highEvenCenters G ∪ badEvenVertices G) := by
  classical
  obtain ⟨hvc, hvnot⟩ := Finset.mem_sdiff.mp hv
  have he := ((mem_cleanDegreeTwoVertices G v).mp hvc).2 w hvw
  have hwE : w ∈ nonisolatedEvenVertices G :=
    (mem_nonisolatedEvenVertices G w).mpr ⟨he, Nat.ne_of_gt hvw.degree_pos_right⟩
  rw [nonisolatedEvenVertices_partition] at hwE
  rcases Finset.mem_union.mp hwE with hwAB | hwC
  · exact Finset.mem_union_right _ hwAB
  · apply Finset.mem_union_left
    apply Finset.mem_sdiff.mpr
    refine ⟨hwC, ?_⟩
    intro hwZ
    exact hvnot (triangleVertices_closed G hwZ hvw.symm)

/-- The exact written candidate-edge lower bound, with all class/contact and
triangle-exclusion premises discharged for actual graph-defined sets. -/
theorem core_degreeTwoPairs_lower_bound_integral (G : SimpleGraph V) (K : ℕ)
    (hcap : ∀ v, evenNeighborCount G v ≤ K) :
    2 * (nonisolatedEvenVertices G).card ≤
      4 * (degreeTwoPairs G (coreDegreeTwoVertices G)).card +
      (K + 2) * ((highEvenCenters G).card + (badEvenVertices G).card) +
      6 * (triangleComponents G).card := by
  have hb := degreeTwoPairs_lower_bound G (coreDegreeTwoVertices G)
    (highEvenCenters G ∪ badEvenVertices G) K (coreDegreeTwoVertices_degree G) hcap
    (coreDegreeTwoVertices_neighbors G)
  rw [Finset.card_union_of_disjoint (disjoint_high_bad G)] at hb
  have he := even_core_class_count G
  nlinarith

theorem core_degreeTwoPairs_lower_bound (G : SimpleGraph V) (K : ℕ)
    (hcap : ∀ v, evenNeighborCount G v ≤ K) :
    ((nonisolatedEvenVertices G).card - 3 * (triangleComponents G).card -
      ((K : ℚ) + 2) * ((highEvenCenters G).card + (badEvenVertices G).card) / 2) / 2 ≤
      (degreeTwoPairs G (coreDegreeTwoVertices G)).card := by
  have hq : (2 : ℚ) * (nonisolatedEvenVertices G).card ≤
      4 * (degreeTwoPairs G (coreDegreeTwoVertices G)).card +
      ((K : ℚ) + 2) * ((highEvenCenters G).card + (badEvenVertices G).card) +
      6 * (triangleComponents G).card := by
    exact_mod_cast core_degreeTwoPairs_lower_bound_integral G K hcap
  linarith

theorem triangleComponents_card_le_components (G : SimpleGraph V) :
    (triangleComponents G).card ≤ Nat.card G.ConnectedComponent := by
  rw [Nat.card_eq_fintype_card]
  exact Finset.card_le_univ _

theorem componentVertices_subset_of_closed (G : SimpleGraph V) (S : Finset V) (x : V)
    (hx : x ∈ S) (hclosed : ∀ v ∈ S, ∀ w, G.Adj v w → w ∈ S) :
    componentVertices G (G.connectedComponentMk x) ⊆ S := by
  have hp : ∀ {v w : V}, G.Walk v w → v ∈ S → w ∈ S := by
    intro v w p
    induction p with
    | nil => exact id
    | @cons a b c hab p ih => exact fun ha => ih (hclosed a ha b hab)
  intro v hv
  have hr : G.Reachable x v := ConnectedComponent.exact
    (((mem_componentVertices G (G.connectedComponentMk x) v).mp hv).symm)
  obtain ⟨p⟩ := hr
  exact hp p hx

theorem neighborFinset_eq_pair_of_degree_two (G : SimpleGraph V) {v a b : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hab : a ≠ b) (hd : G.degree v = 2) :
    G.neighborFinset v = {a,b} := by
  classical
  have hs : ({a,b} : Finset V) ⊆ G.neighborFinset v := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hwa | hwb
    · subst w; exact (G.mem_neighborFinset v a).mpr ha
    · subst w; exact (G.mem_neighborFinset v b).mpr hb
  symm
  apply Finset.eq_of_subset_of_card_le hs
  simp [card_neighborFinset_eq_degree, hd, hab]

/-- A triangle all three of whose ordinary degrees are two is an entire
selected component, not merely a triangle subgraph inside a larger component. -/
theorem degree_two_triangle_is_component (G : SimpleGraph V) {x y z : V}
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hzx : G.Adj z x)
    (hx : G.degree x = 2) (hy : G.degree y = 2) (hz : G.degree z = 2) :
    G.connectedComponentMk x ∈ triangleComponents G := by
  classical
  let S : Finset V := {x,y,z}
  have hNx := neighborFinset_eq_pair_of_degree_two G hxy hzx.symm hyz.ne hx
  have hNy := neighborFinset_eq_pair_of_degree_two G hxy.symm hyz hzx.ne.symm hy
  have hNz := neighborFinset_eq_pair_of_degree_two G hzx hyz.symm hxy.ne hz
  have hclosed : ∀ v ∈ S, ∀ w, G.Adj v w → w ∈ S := by
    intro v hv w hvw
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
    rcases hv with hvx | hvy | hvz
    · subst v
      have hw := (G.mem_neighborFinset x w).mpr hvw
      rw [hNx] at hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      tauto
    · subst v
      have hw := (G.mem_neighborFinset y w).mpr hvw
      rw [hNy] at hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      tauto
    · subst v
      have hw := (G.mem_neighborFinset z w).mpr hvw
      rw [hNz] at hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      tauto
  have hcomp : componentVertices G (G.connectedComponentMk x) = S := by
    apply Finset.Subset.antisymm
    · exact componentVertices_subset_of_closed G S x (by simp [S]) hclosed
    · intro v hv
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with hvx | hvy | hvz
      · subst v; simp
      · subst v; exact (mem_componentVertices G (G.connectedComponentMk x) y).mpr
          (ConnectedComponent.sound hxy.symm.reachable)
      · subst v; exact (mem_componentVertices G (G.connectedComponentMk x) z).mpr
          (ConnectedComponent.sound hzx.reachable)
  apply (mem_triangleComponents G (G.connectedComponentMk x)).mpr
  rw [hcomp]
  constructor
  · simp [S, hxy.ne, hzx.ne.symm, hyz.ne]
  · intro v hv
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz

/-- Excluding triangle components pays the common-boundary condition needed
for pendant-triangle restoration: the common neighbor has degree at least four. -/
theorem coreDegreeTwo_common_neighbor_degree_ge_four (G : SimpleGraph V) {x y z : V}
    (hx : x ∈ coreDegreeTwoVertices G) (hy : y ∈ coreDegreeTwoVertices G)
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hzx : G.Adj z x) : 4 ≤ G.degree z := by
  have hx2 := coreDegreeTwoVertices_degree G x hx
  have hy2 := coreDegreeTwoVertices_degree G y hy
  have hze : Even (G.degree z) :=
    ((mem_cleanDegreeTwoVertices G x).mp (Finset.mem_sdiff.mp hx).1).2 z hzx.symm
  have hzp := hzx.degree_pos_left
  have hzne : G.degree z ≠ 2 := by
    intro hz2
    have hC := degree_two_triangle_is_component G hxy hyz hzx hx2 hy2 hz2
    have hxZ : x ∈ triangleVertices G := Finset.mem_biUnion.mpr
      ⟨G.connectedComponentMk x, hC, by simp⟩
    exact (Finset.mem_sdiff.mp hx).2 hxZ
  obtain ⟨j, hj⟩ := hze
  omega

/-- Checked graph-defined counts and the exact triangle exception used in the
core argument. Path partitions and restoration are deliberately absent. -/
theorem bounded_even_core_counts (G : SimpleGraph V) (K : ℕ)
    (hcap : ∀ v, evenNeighborCount G v ≤ K) :
    (badEvenVertices G).card ≤ K * (oddVertices G).card ∧
    (triangleVertices G).card = 3 * (triangleComponents G).card ∧
    (triangleComponents G).card ≤ Nat.card G.ConnectedComponent ∧
    (∀ v w, v ∉ triangleVertices G → w ∈ triangleVertices G → ¬ G.Adj v w) ∧
    (nonisolatedEvenVertices G).card = (highEvenCenters G).card +
      (badEvenVertices G).card + (coreDegreeTwoVertices G).card + 3 * (triangleComponents G).card ∧
    2 * (nonisolatedEvenVertices G).card ≤
      4 * (degreeTwoPairs G (coreDegreeTwoVertices G)).card +
      (K + 2) * ((highEvenCenters G).card + (badEvenVertices G).card) +
      6 * (triangleComponents G).card ∧
    (∀ x y z, x ∈ coreDegreeTwoVertices G → y ∈ coreDegreeTwoVertices G →
      G.Adj x y → G.Adj y z → G.Adj z x → 4 ≤ G.degree z) :=
  ⟨badEvenVertices_card_le G K hcap, triangleVertices_card G,
    triangleComponents_card_le_components G, fun _ _ => triangleVertices_no_crossing G,
    even_core_class_count G, core_degreeTwoPairs_lower_bound_integral G K hcap,
    fun _ _ _ => coreDegreeTwo_common_neighbor_degree_ge_four G⟩

end Erdos583
end
end Source07_Erdos583_CoreCounts
/- END Erdos583.CoreCounts -/

/- BEGIN Erdos583.PairLift; source SHA256 92d66fcb932af5f18a2482c3ae1dc9c7604abf4fb34b390ff71a81db45ed3e3e -/
section Source08_Erdos583_PairLift





/-! Concrete degree-two-pair path restoration. No decomposition bound is assumed. -/

noncomputable section

namespace Erdos583

open SimpleGraph
attribute [local instance] Classical.propDecidable

variable {V : Type*} {G : SimpleGraph V}

/-- Split an arbitrary root-containing path and absorb a private pendant
triangle into two nonempty paths. The root need not be an endpoint. -/
theorem pendant_triangle_split {a b z x y : V} (p : G.Walk a b)
    (hp : p.IsPath) (hz : z ∈ p.support)
    (hx : x ∉ p.support) (hy : y ∉ p.support)
    (hxz : G.Adj x z) (hxy : G.Adj x y) (hyz : G.Adj y z) :
    ∃ Q₁ Q₂ : G.Subgraph,
      IsNonemptyPathSubgraph Q₁ ∧ IsNonemptyPathSubgraph Q₂ ∧
      Disjoint Q₁.edgeSet Q₂.edgeSet ∧
      Q₁.edgeSet ∪ Q₂.edgeSet = p.edgeSet ∪ {s(x,z), s(x,y), s(y,z)} := by
  obtain ⟨q, r, hq, hr, hsplit⟩ := hp.mem_support_iff_exists_append.mp hz
  have hqsub : q.support ⊆ p.support := by
    rw [hsplit]
    exact q.support_subset_support_append_left r
  have hrsub : r.support ⊆ p.support := by
    rw [hsplit]
    exact q.support_subset_support_append_right r
  have hxq : x ∉ q.reverse.support := by simpa using fun h => hx (hqsub h)
  have hyq : y ∉ q.reverse.support := by simpa using fun h => hy (hqsub h)
  have hyr : y ∉ r.support := fun h => hy (hrsub h)
  let p₁ : G.Walk y a := .cons hxy.symm (.cons hxz q.reverse)
  let p₂ : G.Walk y b := .cons hyz r
  have hp₁ : p₁.IsPath := by
    apply (hq.reverse.cons hxq).cons
    simp only [Walk.support_cons, List.mem_cons]
    exact fun h => h.elim hxy.ne.symm hyq
  have hp₂ : p₂.IsPath := hr.cons hyr
  have hqr : Disjoint q.edgeSet r.edgeSet := by
    have hnod := hp.isTrail.edges_nodup
    rw [hsplit, Walk.edges_append] at hnod
    apply Set.disjoint_left.mpr
    exact fun _ heq her => List.disjoint_of_nodup_append hnod heq her
  have hxy_r : s(x,y) ∉ r.edgeSet := fun he => hx (hrsub (r.fst_mem_support_of_mem_edges he))
  have hxz_r : s(x,z) ∉ r.edgeSet := fun he => hx (hrsub (r.fst_mem_support_of_mem_edges he))
  have hyz_q : s(y,z) ∉ q.edgeSet := fun he => hy (hqsub (q.fst_mem_support_of_mem_edges he))
  have hswap : s(y,x) = s(x,y) := Sym2.eq_swap
  have he₁ : s(x,y) ≠ s(y,z) := by simp [hxy.ne, hyz.ne, hxz.ne]
  have he₂ : s(x,z) ≠ s(y,z) := by simp [hxy.ne, hxz.ne]
  refine ⟨p₁.toSubgraph, p₂.toSubgraph,
    ⟨y, a, p₁, hp₁, Walk.not_nil_cons, rfl⟩,
    ⟨y, b, p₂, hp₂, Walk.not_nil_cons, rfl⟩, ?_, ?_⟩
  · simp only [Walk.edgeSet_toSubgraph, p₁, p₂, Walk.edgeSet_cons, Walk.edgeSet_reverse, hswap]
    apply Set.disjoint_left.mpr
    intro e he₁' he₂'
    simp only [Set.mem_insert_iff] at he₁' he₂'
    rcases he₁' with heq | heq | heq
    · subst e
      exact he₂'.elim he₁ hxy_r
    · subst e
      exact he₂'.elim he₂ hxz_r
    · rcases he₂' with her | her
      · subst e; exact hyz_q heq
      · exact Set.disjoint_left.mp hqr heq her
  · simp only [Walk.edgeSet_toSubgraph, p₁, p₂, Walk.edgeSet_cons, Walk.edgeSet_reverse, hswap]
    rw [hsplit, Walk.edgeSet_append]
    ext e
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

/-- Add one concrete three-edge path with two private internal vertices. -/
theorem distinct_outer_pair_path {a x y b : V}
    (hax : G.Adj a x) (hxy : G.Adj x y) (hyb : G.Adj y b)
    (hab : a ≠ b) (hay : a ≠ y) (hxb : x ≠ b) :
    ∃ Q : G.Subgraph, IsNonemptyPathSubgraph Q ∧
      Q.edgeSet = {s(a,x), s(x,y), s(y,b)} := by
  let p : G.Walk a b := .cons hax (.cons hxy hyb.toWalk)
  have hp : p.IsPath := by
    simp [p, Walk.cons_isPath_iff, SimpleGraph.Adj.toWalk, hax.ne, hxy.ne, hyb.ne, hab, hay, hxb]
  refine ⟨p.toSubgraph, ⟨a, b, p, hp, Walk.not_nil_cons, rfl⟩, ?_⟩
  ext e
  simp only [Walk.edgeSet_toSubgraph, p, Walk.edgeSet_cons, Adj.toWalk,
    Walk.edgeSet_nil, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false]
  tauto

/-- Replace one member of an arbitrary partial path partition by two paths.
The extra edges must be fresh for the old family; no endpoint assumption occurs. -/
theorem replace_path_by_two (D : Finset G.Subgraph)
    (hall : ∀ P ∈ D, IsNonemptyPathSubgraph P)
    (hdisj : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun P => P.edgeSet))
    (P Q₁ Q₂ : G.Subgraph) (hP : P ∈ D)
    (hQ₁ : IsNonemptyPathSubgraph Q₁) (hQ₂ : IsNonemptyPathSubgraph Q₂)
    (hQQ : Disjoint Q₁.edgeSet Q₂.edgeSet) (T : Set (Sym2 V))
    (hfresh : ∀ R ∈ D, Disjoint T R.edgeSet)
    (hQcover : Q₁.edgeSet ∪ Q₂.edgeSet = P.edgeSet ∪ T)
    (hcover : (⋃ R ∈ D, R.edgeSet) ∪ T = G.edgeSet) :
    HasPathPartition G (D.card + 1) := by
  classical
  have hnew (Q : G.Subgraph) (hQ : Q = Q₁ ∨ Q = Q₂) (R : G.Subgraph)
      (hR : R ∈ D.erase P) : Disjoint Q.edgeSet R.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heQ heR
    have heU : e ∈ Q₁.edgeSet ∪ Q₂.edgeSet := by
      rcases hQ with rfl | rfl
      · exact Or.inl heQ
      · exact Or.inr heQ
    rw [hQcover] at heU
    rcases heU with heP | heT
    · exact Set.disjoint_left.mp
        (hdisj hP (Finset.mem_of_mem_erase hR) (Finset.mem_erase.mp hR).1.symm) heP heR
    · exact Set.disjoint_left.mp (hfresh R (Finset.mem_of_mem_erase hR)) heT heR
  refine ⟨insert Q₁ (insert Q₂ (D.erase P)), ?_, ?_, ?_⟩
  · intro R hR
    rcases Finset.mem_insert.mp hR with rfl | hR
    · exact hQ₁
    · rcases Finset.mem_insert.mp hR with rfl | hR
      · exact hQ₂
      · exact hall R (Finset.mem_of_mem_erase hR)
  · constructor
    · intro R hR S hS hne
      simp only [Finset.mem_coe, Finset.mem_insert] at hR hS
      rcases hR with hR | hR | hR <;> rcases hS with hS | hS | hS
      · subst R; subst S; exact (hne rfl).elim
      · subst R; subst S; exact hQQ
      · subst R; exact hnew Q₁ (Or.inl rfl) S hS
      · subst R; subst S; exact hQQ.symm
      · subst R; subst S; exact (hne rfl).elim
      · subst R; exact hnew Q₂ (Or.inr rfl) S hS
      · subst S; exact (hnew Q₁ (Or.inl rfl) R hR).symm
      · subst S; exact (hnew Q₂ (Or.inr rfl) R hR).symm
      · exact hdisj (Finset.mem_of_mem_erase hR) (Finset.mem_of_mem_erase hS) hne
    · rw [← hcover]
      ext e
      simp only [Set.mem_iUnion, exists_prop, Set.mem_union]
      constructor
      · rintro ⟨R, hR, heR⟩
        rcases Finset.mem_insert.mp hR with hRQ | hR
        · subst R
          have he := hQcover ▸ (show e ∈ Q₁.edgeSet ∪ Q₂.edgeSet from Or.inl heR)
          exact he.elim (fun heP => Or.inl ⟨P, hP, heP⟩) Or.inr
        · rcases Finset.mem_insert.mp hR with hRQ | hR
          · subst R
            have he := hQcover ▸ (show e ∈ Q₁.edgeSet ∪ Q₂.edgeSet from Or.inr heR)
            exact he.elim (fun heP => Or.inl ⟨P, hP, heP⟩) Or.inr
          · exact Or.inl ⟨R, Finset.mem_of_mem_erase hR, heR⟩
      · have hput : e ∈ P.edgeSet ∪ T →
            ∃ R ∈ insert Q₁ (insert Q₂ (D.erase P)), e ∈ R.edgeSet := by
          intro he
          rw [← hQcover] at he
          rcases he with he | he
          · exact ⟨Q₁, Finset.mem_insert_self _ _, he⟩
          · exact ⟨Q₂, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), he⟩
        rintro (⟨R, hR, heR⟩ | heT)
        · by_cases hRP : R = P
          · subst R; exact hput (Or.inl heR)
          · exact ⟨R, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_erase.mpr ⟨hRP, hR⟩)), heR⟩
        · exact hput (Or.inr heT)
  · have h₁ := Finset.card_insert_le Q₁ (insert Q₂ (D.erase P))
    have h₂ := Finset.card_insert_le Q₂ (D.erase P)
    have he := Finset.card_erase_add_one hP
    omega

/-- A fresh nonempty simple path can be added to any partial path partition. -/
theorem add_fresh_path (D : Finset G.Subgraph)
    (hall : ∀ P ∈ D, IsNonemptyPathSubgraph P)
    (hdisj : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun P => P.edgeSet))
    (Q : G.Subgraph) (hQ : IsNonemptyPathSubgraph Q)
    (hfresh : ∀ R ∈ D, Disjoint Q.edgeSet R.edgeSet)
    (hcover : (⋃ R ∈ D, R.edgeSet) ∪ Q.edgeSet = G.edgeSet) :
    HasPathPartition G (D.card + 1) := by
  classical
  refine ⟨insert Q D, ?_, ?_, Finset.card_insert_le _ _⟩
  · intro R hR
    rcases Finset.mem_insert.mp hR with rfl | hR
    · exact hQ
    · exact hall R hR
  · constructor
    · intro R hR S hS hne
      simp only [Finset.mem_coe, Finset.mem_insert] at hR hS
      rcases hR with rfl | hR <;> rcases hS with rfl | hS
      · exact (hne rfl).elim
      · exact hfresh S hS
      · exact (hfresh R hR).symm
      · exact hdisj hR hS hne
    · simpa [Set.union_comm] using hcover

/-- Promote a residual partition into the ambient graph while retaining exactly
its original edge sets. The finite family may only get smaller under `image`. -/
theorem promote_path_partition {H : SimpleGraph V} (hle : H ≤ G) {q : ℕ}
    (hq : HasPathPartition H q) :
    ∃ D : Finset G.Subgraph,
      (∀ P ∈ D, IsNonemptyPathSubgraph P) ∧
      Set.PairwiseDisjoint (D : Set G.Subgraph) (fun P => P.edgeSet) ∧
      (⋃ P ∈ D, P.edgeSet) = H.edgeSet ∧ D.card ≤ q := by
  classical
  obtain ⟨D, hpaths, hdec, hcard⟩ := hq
  let f : H.Subgraph → G.Subgraph := fun P => P.map (.ofLE hle)
  have hE (P : H.Subgraph) : (f P).edgeSet = P.edgeSet := by simp [f]
  have hpath (P : H.Subgraph) (hP : IsNonemptyPathSubgraph P) : IsNonemptyPathSubgraph (f P) := by
    obtain ⟨a, b, p, hp, hn, rfl⟩ := hP
    refine ⟨a, b, p.mapLe hle, hp.mapLe hle, ?_, ?_⟩
    · simpa [Walk.mapLe] using hn
    · simp [f, Walk.mapLe]
  refine ⟨D.image f, ?_, ?_, ?_, Finset.card_image_le.trans hcard⟩
  · intro P hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    exact hpath Q (hpaths Q hQ)
  · intro P hP Q hQ hne
    obtain ⟨P₀, hP₀, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨Q₀, hQ₀, rfl⟩ := Finset.mem_image.mp hQ
    change Disjoint (f P₀).edgeSet (f Q₀).edgeSet
    rw [hE, hE]
    exact hdec.1 hP₀ hQ₀ (fun h => hne (congrArg f h))
  · rw [← hdec.2]
    ext e
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨P, hP, he⟩
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
      exact ⟨Q, hQ, hE Q ▸ he⟩
    · rintro ⟨P, hP, he⟩
      exact ⟨f P, Finset.mem_image.mpr ⟨P, hP, rfl⟩, (hE P).symm ▸ he⟩

theorem isolated_not_in_edge {H : SimpleGraph V} {x : V} (hx : H.IsIsolated x)
    {e : Sym2 V} (he : e ∈ H.edgeSet) : x ∉ e := by
  induction e using Sym2.ind with
  | _ a b =>
    intro hxe
    have hab : H.Adj a b := he
    rcases Sym2.mem_iff.mp hxe with hxa | hxb
    · subst x; exact hx b hab
    · subst x; exact hx a hab.symm

theorem path_avoids_residual_isolate {H : SimpleGraph V} {a b x : V}
    (p : G.Walk a b) (hn : ¬p.Nil) (hE : p.edgeSet ⊆ H.edgeSet)
    (hx : H.IsIsolated x) : x ∉ p.support := by
  intro hxp
  obtain ⟨e, he, hxe⟩ := (Walk.mem_support_iff_exists_mem_edges_of_not_nil hn).mp hxp
  exact isolated_not_in_edge hx (hE he) hxe

/-- Any residual path partition absorbs a private pendant triangle at a
nonisolated root for cost at most one additional path. -/
theorem restore_pendant_triangle {H : SimpleGraph V} (hle : H ≤ G)
    {x y z : V} (hx : H.IsIsolated x) (hy : H.IsIsolated y) (hz : ¬H.IsIsolated z)
    (hxz : G.Adj x z) (hxy : G.Adj x y) (hyz : G.Adj y z)
    (hcover : H.edgeSet ∪ {s(x,z), s(x,y), s(y,z)} = G.edgeSet)
    {q : ℕ} (hq : HasPathPartition H q) : HasPathPartition G (q + 1) := by
  classical
  obtain ⟨D, hall, hdisj, hDcover, hcard⟩ := promote_path_partition hle hq
  have hsubset (P : G.Subgraph) (hP : P ∈ D) : P.edgeSet ⊆ H.edgeSet := by
    intro e he
    rw [← hDcover]
    exact Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨hP, he⟩⟩
  obtain ⟨w, hzw⟩ := H.exists_adj_iff_not_isIsolated.mpr hz
  have he : s(z,w) ∈ ⋃ P ∈ D, P.edgeSet := by rw [hDcover]; exact hzw
  obtain ⟨P, heP⟩ := Set.mem_iUnion.mp he
  obtain ⟨hP, heP⟩ := Set.mem_iUnion.mp heP
  obtain ⟨a, b, p, hp, hn, hpeq⟩ := hall P hP
  have hpE : p.edgeSet ⊆ H.edgeSet := by simpa [hpeq] using hsubset P hP
  have hzp : z ∈ p.support := by
    rw [hpeq, Walk.edgeSet_toSubgraph] at heP
    exact p.fst_mem_support_of_mem_edges heP
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, hQQ, hQcover⟩ := pendant_triangle_split p hp hzp
    (path_avoids_residual_isolate p hn hpE hx) (path_avoids_residual_isolate p hn hpE hy)
    hxz hxy hyz
  have hfresh (R : G.Subgraph) (hR : R ∈ D) :
      Disjoint ({s(x,z), s(x,y), s(y,z)} : Set (Sym2 V)) R.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he heR
    have heH := hsubset R hR heR
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with he | he | he
    · subst e; exact isolated_not_in_edge hx heH (by simp)
    · subst e; exact isolated_not_in_edge hx heH (by simp)
    · subst e; exact isolated_not_in_edge hy heH (by simp)
  have hres := replace_path_by_two D hall hdisj P Q₁ Q₂ hP hQ₁ hQ₂ hQQ
    {s(x,z), s(x,y), s(y,z)} hfresh
    (by simpa [hpeq] using hQcover) (by simpa [hDcover] using hcover)
  exact hres.mono (Nat.add_le_add_right hcard 1)

theorem restore_distinct_outer_pair {H : SimpleGraph V} (hle : H ≤ G)
    {a x y b : V} (hx : H.IsIsolated x) (hy : H.IsIsolated y)
    (hax : G.Adj a x) (hxy : G.Adj x y) (hyb : G.Adj y b)
    (hab : a ≠ b) (hay : a ≠ y) (hxb : x ≠ b)
    (hcover : H.edgeSet ∪ {s(a,x), s(x,y), s(y,b)} = G.edgeSet)
    {q : ℕ} (hq : HasPathPartition H q) : HasPathPartition G (q + 1) := by
  classical
  obtain ⟨D, hall, hdisj, hDcover, hcard⟩ := promote_path_partition hle hq
  obtain ⟨Q, hQ, hQE⟩ := distinct_outer_pair_path hax hxy hyb hab hay hxb
  have hfresh (R : G.Subgraph) (hR : R ∈ D) : Disjoint Q.edgeSet R.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he heR
    have heH : e ∈ H.edgeSet := by
      rw [← hDcover]
      exact Set.mem_iUnion.mpr ⟨R, Set.mem_iUnion.mpr ⟨hR, heR⟩⟩
    rw [hQE] at he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with he | he | he
    · subst e; exact isolated_not_in_edge hx heH (by simp)
    · subst e; exact isolated_not_in_edge hx heH (by simp)
    · subst e; exact isolated_not_in_edge hy heH (by simp)
  have hres := add_fresh_path D hall hdisj Q hQ hfresh
    (by simpa [hDcover, hQE] using hcover)
  exact hres.mono (Nat.add_le_add_right hcard 1)

/-- Isolate the two internal vertices while keeping the ambient vertex type. -/
def isolatePair (G : SimpleGraph V) (x y : V) : SimpleGraph V :=
  (G.deleteIncidenceSet x).deleteIncidenceSet y

theorem isolatePair_adj (G : SimpleGraph V) (x y u v : V) :
    (isolatePair G x y).Adj u v ↔
      G.Adj u v ∧ u ≠ x ∧ v ≠ x ∧ u ≠ y ∧ v ≠ y := by
  simp only [isolatePair, deleteIncidenceSet_adj]
  tauto

theorem isolatePair_le (G : SimpleGraph V) (x y : V) : isolatePair G x y ≤ G :=
  ((G.deleteIncidenceSet x).deleteIncidenceSet_le y).trans (G.deleteIncidenceSet_le x)

theorem isolatePair_left_isolated (G : SimpleGraph V) (x y : V) :
    (isolatePair G x y).IsIsolated x := by
  intro v hv
  exact ((isolatePair_adj G x y x v).mp hv).2.1 rfl

theorem isolatePair_right_isolated (G : SimpleGraph V) (x y : V) :
    (isolatePair G x y).IsIsolated y := by
  intro v hv
  exact ((isolatePair_adj G x y y v).mp hv).2.2.2.1 rfl

theorem isolatePair_edge_cover (G : SimpleGraph V) (a x y b : V)
    (hNx : ∀ v, G.Adj x v ↔ v = a ∨ v = y)
    (hNy : ∀ v, G.Adj y v ↔ v = x ∨ v = b) :
    (isolatePair G x y).edgeSet ∪ {s(a,x), s(x,y), s(y,b)} = G.edgeSet := by
  have hax : G.Adj a x := ((hNx a).mpr (Or.inl rfl)).symm
  have hxy : G.Adj x y := (hNx y).mpr (Or.inr rfl)
  have hyb : G.Adj y b := (hNy b).mpr (Or.inr rfl)
  ext e
  constructor
  · rintro (he | he)
    · exact SimpleGraph.edgeSet_mono (isolatePair_le G x y) he
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl | rfl
      · exact hax
      · exact hxy
      · exact hyb
  · intro he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := he
      by_cases hux : u = x
      · subst u
        rcases (hNx v).mp huv with hva | hvy
        · subst v; exact Or.inr (by simp [Sym2.eq_swap])
        · subst v; exact Or.inr (by simp)
      by_cases huy : u = y
      · subst u
        rcases (hNy v).mp huv with hvx | hvb
        · subst v; exact Or.inr (by simp [Sym2.eq_swap])
        · subst v; exact Or.inr (by simp)
      by_cases hvx : v = x
      · subst v
        rcases (hNx u).mp huv.symm with hua | huy'
        · subst u; exact Or.inr (by simp)
        · subst u; exact Or.inr (by simp [Sym2.eq_swap])
      by_cases hvy : v = y
      · subst v
        rcases (hNy u).mp huv.symm with hux' | hub
        · subst u; exact Or.inr (by simp)
        · subst u; exact Or.inr (by simp [Sym2.eq_swap])
      exact Or.inl ((isolatePair_adj G x y u v).mpr ⟨huv, hux, hvx, huy, hvy⟩)

section Finite

variable [Fintype V]

theorem neighborFinset_isolatePair_other (G : SimpleGraph V) (x y v : V)
    (hvx : v ≠ x) (hvy : v ≠ y) :
    (isolatePair G x y).neighborFinset v = ((G.neighborFinset v).erase x).erase y := by
  classical
  ext w
  simp only [mem_neighborFinset, isolatePair_adj, Finset.mem_erase]
  tauto

theorem degree_isolatePair_common_root (G : SimpleGraph V) {x y z : V}
    (hxz : G.Adj x z) (hyz : G.Adj y z) (hxy : x ≠ y) :
    (isolatePair G x y).degree z = G.degree z - 2 := by
  classical
  rw [← card_neighborFinset_eq_degree,
    neighborFinset_isolatePair_other G x y z hxz.ne.symm hyz.ne.symm]
  rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem]
  · rw [card_neighborFinset_eq_degree]
    omega
  · exact (G.mem_neighborFinset z x).mpr hxz.symm
  · exact Finset.mem_erase.mpr ⟨hxy.symm, (G.mem_neighborFinset z y).mpr hyz.symm⟩

/-- Actual degree-two pair restoration, including coincident outer neighbors.
The only common-root hypothesis is the original degree bound which guarantees
an arbitrary residual path is available for absorption. -/
theorem restore_degree_two_pair (G : SimpleGraph V) {a x y b : V}
    (hax : G.Adj a x) (hxy : G.Adj x y) (hyb : G.Adj y b)
    (hay : a ≠ y) (hxb : x ≠ b)
    (hx2 : G.degree x = 2) (hy2 : G.degree y = 2)
    (hroot : a = b → 4 ≤ G.degree a)
    {q : ℕ} (hq : HasPathPartition (isolatePair G x y) q) :
    HasPathPartition G (q + 1) := by
  have hNx : ∀ v, G.Adj x v ↔ v = a ∨ v = y := by
    intro v
    have hn := neighborFinset_eq_pair_of_degree_two G hax.symm hxy hay hx2
    rw [← G.mem_neighborFinset x v, hn]
    simp
  have hNy : ∀ v, G.Adj y v ↔ v = x ∨ v = b := by
    intro v
    have hn := neighborFinset_eq_pair_of_degree_two G hxy.symm hyb hxb hy2
    rw [← G.mem_neighborFinset y v, hn]
    simp
  have hcover := isolatePair_edge_cover G a x y b hNx hNy
  by_cases hab : a = b
  · subst b
    have hzdeg : (isolatePair G x y).degree a ≠ 0 := by
      rw [degree_isolatePair_common_root G hax.symm hyb hxy.ne]
      have := hroot rfl
      omega
    have hz : ¬(isolatePair G x y).IsIsolated a := by
      intro hi
      exact hzdeg hi.degree_eq_zero
    apply restore_pendant_triangle (isolatePair_le G x y)
      (isolatePair_left_isolated G x y) (isolatePair_right_isolated G x y) hz
      hax.symm hxy hyb ?_ hq
    have hs : s(a,x) = s(x,a) := Sym2.eq_swap
    simpa only [hs] using hcover
  · exact restore_distinct_outer_pair (isolatePair_le G x y)
      (isolatePair_left_isolated G x y) (isolatePair_right_isolated G x y)
      hax hxy hyb hab hay hxb hcover hq

theorem degree_two_other_neighbor (G : SimpleGraph V) {x y : V}
    (hxy : G.Adj x y) (hx2 : G.degree x = 2) :
    ∃ a, G.Adj x a ∧ a ≠ y := by
  classical
  have hc : ((G.neighborFinset x).erase y).card = 1 := by
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset x y).mpr hxy),
      card_neighborFinset_eq_degree, hx2]
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < ((G.neighborFinset x).erase y).card by omega)
  exact ⟨a, (G.mem_neighborFinset x a).mp (Finset.mem_of_mem_erase ha), (Finset.mem_erase.mp ha).1⟩

/-- Every actual B0--B0 candidate edge has the unconditional cost-one local
restoration, for every supplied residual path partition. -/
theorem restore_core_degree_two_pair (G : SimpleGraph V) {x y : V}
    (hx : x ∈ coreDegreeTwoVertices G) (hy : y ∈ coreDegreeTwoVertices G)
    (hxy : G.Adj x y) {q : ℕ}
    (hq : HasPathPartition (isolatePair G x y) q) : HasPathPartition G (q + 1) := by
  have hx2 := coreDegreeTwoVertices_degree G x hx
  have hy2 := coreDegreeTwoVertices_degree G y hy
  obtain ⟨a, hxa, hay⟩ := degree_two_other_neighbor G hxy hx2
  obtain ⟨b, hyb, hbx⟩ := degree_two_other_neighbor G hxy.symm hy2
  apply restore_degree_two_pair G hxa.symm hxy hyb hay hbx.symm hx2 hy2 ?_ hq
  intro hab
  subst b
  exact coreDegreeTwo_common_neighbor_degree_ge_four G hx hy hxy hyb hxa.symm

omit [Fintype V] in
theorem isolatePair_comm (G : SimpleGraph V) (x y : V) :
    isolatePair G x y = isolatePair G y x := by
  ext u v
  simp only [isolatePair_adj]
  tauto

theorem phi_eq_sum_parityWeight (G : SimpleGraph V) :
    phi G = ∑ v : V, parityWeight (G.degree v) := by
  classical
  simp [phi, parityWeight, oddVertices, nonisolatedEvenVertices,
    Finset.sum_add_distrib, Finset.sum_ite, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

theorem parityWeight_even_nonzero {d : ℕ} (he : Even d) (hn : d ≠ 0) :
    parityWeight d = 2 / 3 := by
  simp [parityWeight, he, hn, Nat.not_odd_iff_even.mpr he]

/-- Isolating any set of clean degree-two vertices removes their full potential
and cannot increase the contribution of any remaining vertex. -/
def isolateVertices (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∉ S ∧ v ∉ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

omit [Fintype V] in
theorem isolateVertices_adj (G : SimpleGraph V) (S : Finset V) (u v : V) :
    (isolateVertices G S).Adj u v ↔ G.Adj u v ∧ u ∉ S ∧ v ∉ S := Iff.rfl

omit [Fintype V] in
theorem isolateVertices_isolated (G : SimpleGraph V) (S : Finset V) (x : V)
    (hx : x ∈ S) : (isolateVertices G S).IsIsolated x :=
  fun _ h => h.2.1 hx

theorem isolateVertices_degree_unchanged (G : SimpleGraph V) (S : Finset V) (v : V)
    (hv : v ∉ S) (haway : ∀ x ∈ S, ¬ G.Adj v x) :
    (isolateVertices G S).degree v = G.degree v := by
  have hn : (isolateVertices G S).neighborFinset v = G.neighborFinset v := by
    ext w
    simp only [mem_neighborFinset, isolateVertices_adj]
    exact ⟨And.left, fun h => ⟨h, hv, fun hw => haway w hw h⟩⟩
  rw [← card_neighborFinset_eq_degree, hn, card_neighborFinset_eq_degree]

theorem phi_isolateVertices_drop (G : SimpleGraph V) (S : Finset V)
    (hS : S ⊆ cleanDegreeTwoVertices G) :
    (2 / 3 : ℚ) * S.card ≤ phi G - phi (isolateVertices G S) := by
  classical
  have hpoint (v : V) : parityWeight ((isolateVertices G S).degree v) +
      (if v ∈ S then (2 / 3 : ℚ) else 0) ≤ parityWeight (G.degree v) := by
    by_cases hv : v ∈ S
    · have hg := ((mem_cleanDegreeTwoVertices G v).mp (hS hv)).1
      have hh := (isolateVertices_isolated G S v hv).degree_eq_zero
      norm_num [hv, hg, hh, parityWeight]
    · simp only [if_neg hv, add_zero]
      by_cases hn : ∃ x ∈ S, G.Adj v x
      · obtain ⟨x, hx, hvx⟩ := hn
        have he := ((mem_cleanDegreeTwoVertices G x).mp (hS hx)).2 v hvx.symm
        rw [parityWeight_even_nonzero he (Nat.ne_of_gt hvx.degree_pos_left)]
        exact parityWeight_le_two_thirds _
      · have haway : ∀ x ∈ S, ¬G.Adj v x := by simpa using hn
        rw [isolateVertices_degree_unchanged G S v hv haway]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun v _ => hpoint v)
  rw [Finset.sum_add_distrib, ← phi_eq_sum_parityWeight, ← phi_eq_sum_parityWeight] at hsum
  have hs : (∑ v : V, if v ∈ S then (2 / 3 : ℚ) else 0) = (2 / 3 : ℚ) * S.card := by
    simp [mul_comm]
  rw [hs] at hsum
  linarith

omit [Fintype V] in
theorem isolateVertices_pair (G : SimpleGraph V) (x y : V) :
    isolateVertices G {x,y} = isolatePair G x y := by
  ext u v
  simp only [isolateVertices_adj, isolatePair_adj, Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem phi_isolatePair_drop (G : SimpleGraph V) {x y : V}
    (hx : x ∈ coreDegreeTwoVertices G) (hy : y ∈ coreDegreeTwoVertices G)
    (hxy : G.Adj x y) : (4 / 3 : ℚ) ≤ phi G - phi (isolatePair G x y) := by
  classical
  have hS : ({x,y} : Finset V) ⊆ cleanDegreeTwoVertices G := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact (Finset.mem_sdiff.mp hx).1
    · exact (Finset.mem_sdiff.mp hy).1
  have h := phi_isolateVertices_drop G {x,y} hS
  norm_num [isolateVertices_pair, hxy.ne] at h
  exact h

/-- The genuine local pair reduction: actual potential payment and restoration
of every supplied residual partition. No baseline theorem is a premise. -/
theorem degree_two_pair_lift (G : SimpleGraph V) {x y : V}
    (hx : x ∈ coreDegreeTwoVertices G) (hy : y ∈ coreDegreeTwoVertices G)
    (hxy : G.Adj x y) :
    (4 / 3 : ℚ) ≤ phi G - phi (isolatePair G x y) ∧
    ∀ q, HasPathPartition (isolatePair G x y) q → HasPathPartition G (q + 1) :=
  ⟨phi_isolatePair_drop G hx hy hxy, fun _ => restore_core_degree_two_pair G hx hy hxy⟩

/-- Conditional use of a residual parity bound. The
condition is an actual path partition bound for the concrete residual graph. -/
theorem pair_saving_of_residual_parity_bound (G : SimpleGraph V) {x y : V}
    (hx : x ∈ coreDegreeTwoVertices G) (hy : y ∈ coreDegreeTwoVertices G)
    (hxy : G.Adj x y)
    (hbase : HasPathBound (isolatePair G x y) (phi (isolatePair G x y))) :
    HasPathBound G (phi G - 1 / 3) := by
  obtain ⟨q, hq, hqbound⟩ := hasPathBound_iff_exists_partition.mp hbase
  apply hasPathBound_iff_exists_partition.mpr
  refine ⟨q + 1, restore_core_degree_two_pair G hx hy hxy hq, ?_⟩
  have hphi := phi_isolatePair_drop G hx hy hxy
  push_cast
  linarith

end Finite

end Erdos583
end
end Source08_Erdos583_PairLift
/- END Erdos583.PairLift -/

/- BEGIN Erdos583.LeafGraph; source SHA256 14de4fe54ba9ac5f60e2adb55a9323d495e6175e3574baeb3ab51b54448a68f2 -/
section Source09_Erdos583_LeafGraph



/-! A genuinely fresh leaf and its actual degree, support and potential costs.
These are graph operations for the baseline reductions, not path bounds. -/

noncomputable section
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*}

def attachLeaf (G : SimpleGraph V) (a : V) : SimpleGraph (Option V) where
  Adj u v := match u,v with
    | some x, some y => G.Adj x y
    | none, some y => y = a
    | some x, none => x = a
    | none, none => False
  symm := ⟨by intro u v h; cases u <;> cases v <;> first | exact h | exact h.symm⟩
  loopless := ⟨by intro u h; cases u with
                 | none => exact h
                 | some u => exact G.loopless.irrefl u h⟩

@[simp] theorem attachLeaf_adj_some (G : SimpleGraph V) (a u v : V) :
    (attachLeaf G a).Adj (some u) (some v) ↔ G.Adj u v := Iff.rfl

@[simp] theorem attachLeaf_adj_new (G : SimpleGraph V) (a v : V) :
    (attachLeaf G a).Adj none (some v) ↔ v = a := Iff.rfl

variable [Fintype V]

theorem attachLeaf_neighbors_new (G : SimpleGraph V) (a : V) :
    (attachLeaf G a).neighborFinset none = {some a} := by
  ext v
  simp only [mem_neighborFinset]
  cases v <;> simp [attachLeaf]

theorem attachLeaf_neighbors_some (G : SimpleGraph V) (a v : V) :
    (attachLeaf G a).neighborFinset (some v) =
      if v = a then insert none ((G.neighborFinset v).map someEmbedding)
      else (G.neighborFinset v).map someEmbedding := by
  ext w
  simp only [mem_neighborFinset]
  cases w <;> by_cases h : v = a <;> simp [attachLeaf, someEmbedding, h]

@[simp] theorem attachLeaf_degree_new (G : SimpleGraph V) (a : V) :
    (attachLeaf G a).degree none = 1 := by
  rw [← card_neighborFinset_eq_degree, attachLeaf_neighbors_new, Finset.card_singleton]

theorem attachLeaf_degree_some (G : SimpleGraph V) (a v : V) :
    (attachLeaf G a).degree (some v) = G.degree v + if v = a then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree, attachLeaf_neighbors_some]
  by_cases h : v = a
  · simp [h, someEmbedding, card_neighborFinset_eq_degree]
  · simp [h, card_neighborFinset_eq_degree]

theorem attachLeaf_degree_some_add (G : SimpleGraph V) (a : V) :
    (∑ v : V, (attachLeaf G a).degree (some v)) = (∑ v : V, G.degree v) + 1 := by
  simp_rw [attachLeaf_degree_some]
  rw [Finset.sum_add_distrib]
  simp

theorem attachLeaf_edge_count (G : SimpleGraph V) (a : V) :
    (attachLeaf G a).edgeFinset.card = G.edgeFinset.card + 1 := by
  have hs := (attachLeaf G a).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_option, attachLeaf_degree_new, attachLeaf_degree_some_add,
    G.sum_degrees_eq_twice_card_edges] at hs
  omega

theorem attachLeaf_old_nonisolated (G : SimpleGraph V) (a : V) (ha : G.degree a ≠ 0) (v : V) :
    (attachLeaf G a).degree (some v) ≠ 0 ↔ G.degree v ≠ 0 := by
  rw [attachLeaf_degree_some]
  by_cases hv : v = a
  · subst v; simp [ha]
  · simp [hv]

theorem attachLeaf_activeVertices (G : SimpleGraph V) (a : V) (ha : G.degree a ≠ 0) :
    activeVertices (attachLeaf G a) = insert none ((activeVertices G).map someEmbedding) := by
  ext v
  cases v with
  | none => simp
  | some v => simp [attachLeaf_old_nonisolated G a ha v, someEmbedding]

theorem attachLeaf_active_count (G : SimpleGraph V) (a : V) (ha : G.degree a ≠ 0) :
    (activeVertices (attachLeaf G a)).card = (activeVertices G).card + 1 := by
  rw [attachLeaf_activeVertices G a ha, card_insert_none_map_some]

theorem attachLeaf_edgeExcess (G : SimpleGraph V) (a : V) (ha : G.degree a ≠ 0) :
    edgeExcess (attachLeaf G a) = edgeExcess G + 1 := by
  have hnonneg := activeVertices_card_le_twice_edges G
  unfold edgeExcess
  rw [attachLeaf_edge_count, attachLeaf_active_count G a ha]
  omega

theorem phi_attachLeaf_even (G : SimpleGraph V) (a : V)
    (ha : Even (G.degree a)) (hapos : G.degree a ≠ 0) :
    phi (attachLeaf G a) = phi G + 1 / 3 := by
  have hnewodd : Odd (G.degree a + 1) := ha.add_odd (by decide)
  have hnewweight : parityWeight (G.degree a + 1) = 1 / 2 := by
    norm_num [parityWeight, hnewodd, Nat.not_even_iff_odd.mpr hnewodd]
  have hpoint (v : V) : parityWeight ((attachLeaf G a).degree (some v)) =
      parityWeight (G.degree v) + if v = a then -(1 / 6 : ℚ) else 0 := by
    rw [attachLeaf_degree_some]
    by_cases hv : v = a
    · subst v
      rw [if_pos rfl, hnewweight, parityWeight_even_nonzero ha hapos]
      norm_num
    · simp [hv]
  rw [phi_eq_sum_parityWeight, Fintype.sum_option, attachLeaf_degree_new]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← phi_eq_sum_parityWeight]
  norm_num [parityWeight]
  ring

end Erdos583
end
end Source09_Erdos583_LeafGraph
/- END Erdos583.LeafGraph -/

/- BEGIN Erdos583.StarRestore; source SHA256 5cded6aa36503361a8b36803daa19148e1fae54b239545e10ff5991d5db22f1f -/
section Source10_Erdos583_StarRestore




/-!
# Endpoint and switching foundations for star restoration

The mixed-partition definitions are interfaces, not assumptions or restoration
theorems. Every theorem below proves its stated graph assertion directly.
-/

namespace Erdos583

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A simple cycle through a specified root, using its original edges. -/
def IsRootedCycleSubgraph (x : V) (H : G.Subgraph) : Prop :=
  ∃ p : G.Walk x x, p.IsCycle ∧ H = p.toSubgraph

/-- A partition into paths and cycles, all cycles through `x`, with explicit
total-part and cycle-count budgets. This definition asserts no existence. -/
def HasMixedPartitionAt (G : SimpleGraph V) (x : V) (a q : ℕ) : Prop := by
  classical
  exact ∃ P C : Finset G.Subgraph,
    (∀ H ∈ P, IsNonemptyPathSubgraph H) ∧
    (∀ H ∈ C, IsRootedCycleSubgraph x H) ∧
    Disjoint P C ∧ IsDecomposition G (P ∪ C) ∧
    P.card + C.card ≤ a ∧ C.card ≤ q

/-- A specified vertex is an endpoint, with the witnessing path oriented from it. -/
def PathStartsAt (H : G.Subgraph) (x : V) : Prop :=
  ∃ (y : V) (p : G.Walk x y), p.IsPath ∧ ¬ p.Nil ∧ H = p.toSubgraph

/-- Number of partition members having the specified vertex as an endpoint. -/
noncomputable def endpointCount (D : Finset G.Subgraph) (x : V) : ℕ := by
  classical
  exact (D.filter fun H => PathStartsAt H x).card

section Finite

variable [Fintype V]
attribute [local instance] Classical.propDecidable

/-- The exact degree profile of a nonempty simple path subgraph. -/
theorem pathSubgraph_degree {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hnil : ¬ p.Nil) (x : V) :
    p.toSubgraph.degree x =
      if x = u ∨ x = v then 1 else if x ∈ p.support then 2 else 0 := by
  classical
  by_cases hxu : x = u
  · subst x
    simp only [true_or, ite_true]
    rw [Subgraph.degree, Set.fintypeCard_eq_ncard,
      hp.neighborSet_toSubgraph_startpoint hnil]
    simp
  · by_cases hxv : x = v
    · subst x
      simp only [or_true, ite_true]
      rw [Subgraph.degree, Set.fintypeCard_eq_ncard,
        hp.neighborSet_toSubgraph_endpoint hnil]
      simp
    · simp only [hxu, hxv, or_self, ite_false]
      by_cases hs : x ∈ p.support
      · rw [if_pos hs]
        obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp hs
        have hi0 : i ≠ 0 := by
          intro hz
          apply hxu
          simpa [hz] using hi.symm
        have hilt : i < p.length := by
          have hine : i ≠ p.length := by
            intro heq
            apply hxv
            simpa [heq] using hi.symm
          omega
        rw [← hi, Subgraph.degree, Set.fintypeCard_eq_ncard]
        exact hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hilt
      · rw [if_neg hs]
        apply Subgraph.degree_of_notMem_verts
        simpa using hs

/-- Odd degree inside one simple path forces the specified vertex to be an endpoint. -/
theorem pathStartsAt_of_odd_subgraph_degree {H : G.Subgraph} (x : V)
    (hH : IsNonemptyPathSubgraph H) (ho : Odd (H.degree x)) : PathStartsAt H x := by
  classical
  obtain ⟨u, v, p, hp, hnil, rfl⟩ := hH
  have hends : x = u ∨ x = v := by
    by_contra hn
    rw [pathSubgraph_degree p hp hnil, if_neg hn] at ho
    split_ifs at ho <;> norm_num at ho
  rcases hends with rfl | rfl
  · exact ⟨v, p, hp, hnil, rfl⟩
  · refine ⟨u, p.reverse, hp.reverse, ?_, p.toSubgraph_reverse.symm⟩
    simpa only [Walk.not_nil_iff_lt_length, Walk.length_reverse] using hnil

/-- An edge partition splits the neighbor set at every vertex. -/
theorem neighborFinset_eq_biUnion_of_decomposition (D : Finset G.Subgraph)
    (hD : IsDecomposition G D) (x : V) :
    G.neighborFinset x = D.biUnion (fun H => (H.neighborSet x).toFinset) := by
  classical
  ext y
  simp only [mem_neighborFinset, Finset.mem_biUnion, Set.mem_toFinset,
    Subgraph.mem_neighborSet]
  constructor
  · intro hxy
    have he : s(x, y) ∈ ⋃ H ∈ D, H.edgeSet := by
      rw [hD.2]
      exact hxy
    obtain ⟨H, he⟩ := Set.mem_iUnion.mp he
    obtain ⟨hH, he⟩ := Set.mem_iUnion.mp he
    exact ⟨H, hH, he⟩
  · rintro ⟨H, _, hxy⟩
    exact H.adj_sub hxy

/-- Edge disjointness implies disjoint neighbor sets at a fixed vertex. -/
theorem pairwiseDisjoint_neighbors_of_decomposition (D : Finset G.Subgraph)
    (hD : IsDecomposition G D) (x : V) :
    Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => (H.neighborSet x).toFinset) := by
  classical
  intro H hH J hJ hne
  change Disjoint (H.neighborSet x).toFinset (J.neighborSet x).toFinset
  apply Finset.disjoint_left.mpr
  intro y hy hy'
  have hd : Disjoint H.edgeSet J.edgeSet := hD.1 hH hJ hne
  have hadj : H.Adj x y := by simpa only [Set.mem_toFinset, Subgraph.mem_neighborSet] using hy
  have hadj' : J.Adj x y := by simpa only [Set.mem_toFinset, Subgraph.mem_neighborSet] using hy'
  have he : s(x, y) ∈ H.edgeSet := hadj
  have he' : s(x, y) ∈ J.edgeSet := hadj'
  exact Set.disjoint_left.mp hd he he'

/-- The ordinary degree is exactly the sum of degrees in the partition members. -/
theorem degree_eq_sum_of_decomposition (D : Finset G.Subgraph)
    (hD : IsDecomposition G D) (x : V) :
    G.degree x = ∑ H ∈ D, H.degree x := by
  rw [← G.card_neighborFinset_eq_degree,
    neighborFinset_eq_biUnion_of_decomposition D hD x,
    Finset.card_biUnion (pairwiseDisjoint_neighbors_of_decomposition D hD x)]
  apply Finset.sum_congr rfl
  intro H _
  exact Subgraph.finset_card_neighborSet_eq_degree

theorem PathStartsAt.degree_eq_one {H : G.Subgraph} {x : V}
    (h : PathStartsAt H x) : H.degree x = 1 := by
  obtain ⟨y, p, hp, hn, rfl⟩ := h
  simp [pathSubgraph_degree p hp hn]

theorem pathStartsAt_iff_odd_degree {H : G.Subgraph} (x : V)
    (hH : IsNonemptyPathSubgraph H) : PathStartsAt H x ↔ Odd (H.degree x) := by
  constructor
  · intro h
    rw [h.degree_eq_one]
    decide
  · exact pathStartsAt_of_odd_subgraph_degree x hH

theorem pathStartsAt_iff_endpoints {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) (hn : ¬ p.Nil) (x : V) :
    PathStartsAt p.toSubgraph x ↔ x = u ∨ x = v := by
  rw [pathStartsAt_iff_odd_degree x ⟨u, v, p, hp, hn, rfl⟩,
    pathSubgraph_degree p hp hn]
  split_ifs <;> simp_all

/-- A partition member can be selected by at most its two endpoints. -/
theorem selected_path_has_at_most_two_endpoints (R : Finset V)
    (owner : V → G.Subgraph) (howner : ∀ v ∈ R, PathStartsAt (owner v) v)
    (H : G.Subgraph) (hH : IsNonemptyPathSubgraph H) :
    (R.filter fun v => owner v = H).card ≤ 2 := by
  classical
  obtain ⟨a, b, p, hp, hn, rfl⟩ := hH
  have hs : (R.filter fun v => owner v = p.toSubgraph) ⊆ {a, b} := by
    intro v hv
    obtain ⟨hvR, heq⟩ := Finset.mem_filter.mp hv
    have he := howner v hvR
    rw [heq, pathStartsAt_iff_endpoints p hp hn v] at he
    simpa using he
  have hab : a ≠ b := hp.nil_iff_eq.not.mp hn
  exact (Finset.card_le_card hs).trans (by simp [hab])

/-- Endpoint multiplicity has exactly the parity of the ambient degree. -/
theorem endpointCount_odd_iff (D : Finset G.Subgraph)
    (hp : ∀ H ∈ D, IsNonemptyPathSubgraph H) (hd : IsDecomposition G D) (x : V) :
    Odd (endpointCount D x) ↔ Odd (G.degree x) := by
  classical
  rw [degree_eq_sum_of_decomposition D hd x, Finset.odd_sum_iff_odd_card_odd]
  unfold endpointCount
  have hf : D.filter (fun H => PathStartsAt H x) = D.filter (fun H => Odd (H.degree x)) := by
    apply Finset.filter_congr
    intro H hH
    exact pathStartsAt_iff_odd_degree x (hp H hH)
  rw [hf]

theorem endpointCount_even_iff (D : Finset G.Subgraph)
    (hp : ∀ H ∈ D, IsNonemptyPathSubgraph H) (hd : IsDecomposition G D) (x : V) :
    Even (endpointCount D x) ↔ Even (G.degree x) := by
  simpa only [Nat.not_odd_iff_even] using (endpointCount_odd_iff D hp hd x).not

/-- Every odd vertex begins some path in EVERY path partition. -/
theorem exists_pathStartsAt_of_odd (D : Finset G.Subgraph)
    (hp : ∀ H ∈ D, IsNonemptyPathSubgraph H) (hd : IsDecomposition G D)
    (x : V) (ho : Odd (G.degree x)) : ∃ H ∈ D, PathStartsAt H x := by
  classical
  have hc := (endpointCount_odd_iff D hp hd x).mpr ho
  have hpos : 0 < endpointCount D x := hc.pos
  obtain ⟨H, hH⟩ := Finset.card_pos.mp hpos
  exact ⟨H, (Finset.mem_filter.mp hH).1, (Finset.mem_filter.mp hH).2⟩

end Finite

/-- Reversing the initial segment before a star switch preserves vertex
simplicity. The given edges are edges of the same ambient graph. -/
theorem path_switch_one_isPath {a c x b : V}
    (p : G.Walk a c) (q : G.Walk x b) (hcx : G.Adj c x) (hax : G.Adj a x)
    (hpq : (p.append (.cons hcx q)).IsPath) :
    (p.reverse.append (.cons hax q)).IsPath := by
  simpa only [Walk.isPath_def, Walk.support_append, Walk.support_cons,
    List.tail_cons, Walk.support_reverse, List.nodup_append,
    List.nodup_reverse, List.mem_reverse] using hpq

/-- Exact exchange identity for the one-endpoint switch: adjoining the removed
edge to the output recovers the input plus the inserted edge. -/
theorem path_switch_one_edge_identity {a c x b : V}
    (p : G.Walk a c) (q : G.Walk x b) (hcx : G.Adj c x) (hax : G.Adj a x) :
    (p.reverse.append (.cons hax q)).edgeSet ∪ {s(c, x)} =
      (p.append (.cons hcx q)).edgeSet ∪ {s(a, x)} := by
  ext e
  simp [Set.mem_insert_iff]
  tauto

/-- The stronger deletion-and-insertion identity, using trail edge uniqueness. -/
theorem path_switch_one_exact_edges {a c x b : V}
    (p : G.Walk a c) (q : G.Walk x b) (hcx : G.Adj c x) (hax : G.Adj a x)
    (hpq : (p.append (.cons hcx q)).IsPath) :
    (p.reverse.append (.cons hax q)).edgeSet =
      insert s(a, x) ((p.append (.cons hcx q)).edgeSet \ {s(c, x)}) := by
  have hn := hpq.isTrail.edges_nodup
  simp only [Walk.edges_append, Walk.edges_cons, List.nodup_append, List.nodup_cons] at hn
  have hcp : s(c, x) ∉ p.edgeSet := by
    intro he
    exact hn.2.2 _ he _ (by simp) rfl
  have hcq : s(c, x) ∉ q.edgeSet := hn.2.1.1
  have hremove : (p.append (.cons hcx q)).edgeSet \ {s(c, x)} = p.edgeSet ∪ q.edgeSet := by
    ext e
    by_cases he : e = s(c, x)
    · subst e
      simp [hcp, hcq]
    · simp [he]
  rw [hremove]
  ext e
  simp
  tauto

/-- Reversing both sides of an internal center gives the two-endpoint switch. -/
theorem path_switch_two_isPath {a c x d b : V}
    (p : G.Walk a c) (q : G.Walk d b)
    (hcx : G.Adj c x) (hxd : G.Adj x d)
    (hax : G.Adj a x) (hxb : G.Adj x b)
    (hpq : (p.append (.cons hcx (.cons hxd q))).IsPath) :
    (p.reverse.append (.cons hax (.cons hxb q.reverse))).IsPath := by
  simp only [Walk.isPath_def, Walk.support_append, Walk.support_cons,
    List.tail_cons, Walk.support_reverse, List.nodup_append,
    List.nodup_cons, List.nodup_reverse, List.mem_reverse, List.mem_cons] at hpq ⊢
  exact hpq

/-- Exact original-edge accounting for the simultaneous two-endpoint switch. -/
theorem path_switch_two_edge_identity {a c x d b : V}
    (p : G.Walk a c) (q : G.Walk d b)
    (hcx : G.Adj c x) (hxd : G.Adj x d)
    (hax : G.Adj a x) (hxb : G.Adj x b) :
    (p.reverse.append (.cons hax (.cons hxb q.reverse))).edgeSet ∪ {s(c, x), s(x, d)} =
      (p.append (.cons hcx (.cons hxd q))).edgeSet ∪ {s(a, x), s(x, b)} := by
  ext e
  simp [Set.mem_insert_iff]
  tauto

theorem path_switch_two_exact_edges {a c x d b : V}
    (p : G.Walk a c) (q : G.Walk d b)
    (hcx : G.Adj c x) (hxd : G.Adj x d)
    (hax : G.Adj a x) (hxb : G.Adj x b)
    (hpq : (p.append (.cons hcx (.cons hxd q))).IsPath) :
    (p.reverse.append (.cons hax (.cons hxb q.reverse))).edgeSet =
      {s(a, x), s(x, b)} ∪
        ((p.append (.cons hcx (.cons hxd q))).edgeSet \ {s(c, x), s(x, d)}) := by
  have hn := hpq.isTrail.edges_nodup
  simp only [Walk.edges_append, Walk.edges_cons, List.nodup_append, List.nodup_cons] at hn
  have hcp : s(c, x) ∉ p.edgeSet := by
    intro he
    exact hn.2.2 _ he _ (by simp) rfl
  have hdp : s(x, d) ∉ p.edgeSet := by
    intro he
    exact hn.2.2 _ he _ (by simp) rfl
  have hcq : s(c, x) ∉ q.edgeSet := by
    intro he
    exact hn.2.1.1 (List.mem_cons_of_mem _ he)
  have hdq : s(x, d) ∉ q.edgeSet := hn.2.1.2.1
  have hremove : (p.append (.cons hcx (.cons hxd q))).edgeSet \ {s(c, x), s(x, d)} =
      p.edgeSet ∪ q.edgeSet := by
    ext e
    by_cases hec : e = s(c, x)
    · subst e
      simp [hcp, hcq]
    · by_cases hed : e = s(x, d)
      · subst e
        simp [hdp, hdq]
      · simp [hec, hed]
  rw [hremove]
  ext e
  simp
  tauto

theorem path_switch_one_nonempty {a c x b : V}
    (p : G.Walk a c) (q : G.Walk x b) (hcx : G.Adj c x) (hax : G.Adj a x)
    (hpq : (p.append (.cons hcx q)).IsPath) :
    IsNonemptyPathSubgraph (p.reverse.append (.cons hax q)).toSubgraph := by
  refine ⟨c, b, p.reverse.append (.cons hax q), path_switch_one_isPath p q hcx hax hpq, ?_, rfl⟩
  rw [Walk.not_nil_iff_lt_length]
  simp only [Walk.length_append, Walk.length_reverse, Walk.length_cons]
  omega

theorem path_switch_two_nonempty {a c x d b : V}
    (p : G.Walk a c) (q : G.Walk d b)
    (hcx : G.Adj c x) (hxd : G.Adj x d)
    (hax : G.Adj a x) (hxb : G.Adj x b)
    (hpq : (p.append (.cons hcx (.cons hxd q))).IsPath) :
    IsNonemptyPathSubgraph (p.reverse.append (.cons hax (.cons hxb q.reverse))).toSubgraph := by
  refine ⟨c, d, p.reverse.append (.cons hax (.cons hxb q.reverse)),
    path_switch_two_isPath p q hcx hxd hax hxb hpq, ?_, rfl⟩
  rw [Walk.not_nil_iff_lt_length]
  simp only [Walk.length_append, Walk.length_reverse, Walk.length_cons]
  omega

/-- A path avoiding the center closes to a simple rooted cycle when both ends
are extended to that center. Nonemptiness excludes a two-edge closed walk. -/
theorem close_path_at_both_ends_isCycle {x a b : V} (p : G.Walk a b)
    (hp : p.IsPath) (hn : ¬ p.Nil) (hx : x ∉ p.support)
    (hxa : G.Adj x a) (hbx : G.Adj b x) :
    (Walk.cons hxa (p.concat hbx)).IsCycle := by
  apply (Walk.cons_isCycle_iff (p.concat hbx) hxa).mpr
  refine ⟨hp.concat hx hbx, ?_⟩
  intro he
  simp only [Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton] at he
  rcases he with he | he
  · exact hx (p.fst_mem_support_of_mem_edges he)
  · have hab : a ≠ b := hp.nil_iff_eq.not.mp hn
    have hne : s(x, a) ≠ s(b, x) := by
      simp [Sym2.eq, Sym2.rel_iff', hxa.ne.symm, hab]
    exact hne he

theorem close_path_at_both_ends_edgeSet {x a b : V} (p : G.Walk a b)
    (hxa : G.Adj x a) (hbx : G.Adj b x) :
    (Walk.cons hxa (p.concat hbx)).edgeSet = {s(x, a), s(x, b)} ∪ p.edgeSet := by
  ext e
  simp [Sym2.eq_swap]
  tauto

/-- The terminal step in a star switch: if the selected endpoint path avoids the
center, a missing original edge can be inserted without increasing the number
of paths. The hypotheses explicitly account for every old and new edge. -/
theorem restore_edge_at_clean_endpoint (D : Finset G.Subgraph)
    (hall : ∀ H ∈ D, IsNonemptyPathSubgraph H)
    (hdisj : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet))
    {x u v : V} (p : G.Walk u v) (hp : p.IsPath) (hx : x ∉ p.support)
    (hxu : G.Adj x u) (hmem : p.toSubgraph ∈ D)
    (hfresh : ∀ H ∈ D, s(x, u) ∉ H.edgeSet)
    (hcover : (⋃ H ∈ D, H.edgeSet) ∪ {s(x, u)} = G.edgeSet) :
    HasPathPartition G D.card := by
  classical
  let Q : G.Subgraph := (Walk.cons hxu p).toSubgraph
  have hQ : IsNonemptyPathSubgraph Q :=
    ⟨x, v, Walk.cons hxu p, hp.cons hx, Walk.not_nil_cons, rfl⟩
  have hQE : Q.edgeSet = insert s(x, u) p.toSubgraph.edgeSet := by simp [Q]
  have hdQ (H : G.Subgraph) (hH : H ∈ D.erase p.toSubgraph) :
      Disjoint Q.edgeSet H.edgeSet := by
    rw [hQE]
    apply Set.disjoint_left.mpr
    intro e he heH
    rcases Set.mem_insert_iff.mp he with rfl | he
    · exact hfresh H (Finset.mem_of_mem_erase hH) heH
    · have hd : Disjoint p.toSubgraph.edgeSet H.edgeSet :=
        hdisj hmem (Finset.mem_of_mem_erase hH) (Finset.mem_erase.mp hH).1.symm
      exact Set.disjoint_left.mp hd he heH
  refine ⟨insert Q (D.erase p.toSubgraph), ?_, ?_, ?_⟩
  · intro H hH
    rcases Finset.mem_insert.mp hH with rfl | hH
    · exact hQ
    · exact hall H (Finset.mem_of_mem_erase hH)
  · constructor
    · intro H hH J hJ hne
      simp only [Finset.mem_coe, Finset.mem_insert] at hH hJ
      rcases hH with rfl | hH <;> rcases hJ with rfl | hJ
      · exact (hne rfl).elim
      · exact hdQ J hJ
      · exact (hdQ H hH).symm
      · exact hdisj (Finset.mem_of_mem_erase hH) (Finset.mem_of_mem_erase hJ) hne
    · rw [← hcover]
      ext e
      simp only [Set.mem_iUnion, exists_prop, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨H, hH, he⟩
        rcases Finset.mem_insert.mp hH with rfl | hH
        · rw [hQE] at he
          rcases Set.mem_insert_iff.mp he with he | he
          · exact Or.inr he
          · exact Or.inl ⟨p.toSubgraph, hmem, he⟩
        · exact Or.inl ⟨H, Finset.mem_of_mem_erase hH, he⟩
      · rintro (⟨H, hH, he⟩ | he)
        · by_cases heq : H = p.toSubgraph
          · subst H
            refine ⟨Q, Finset.mem_insert_self _ _, ?_⟩
            rw [hQE]
            exact Set.mem_insert_of_mem _ he
          · exact ⟨H, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨heq, hH⟩), he⟩
        · refine ⟨Q, Finset.mem_insert_self _ _, ?_⟩
          rw [hQE, he]
          exact Set.mem_insert _ _
  · have hc := Finset.card_insert_le Q (D.erase p.toSubgraph)
    have he := Finset.card_erase_add_one hmem
    omega

section PartialChains

variable {α : Type*}

/-- Extend a partial successor by making its undefined state absorbing. -/
def partialStep (f : α → Option α) (o : Option α) : Option α := o.bind f

/-- A partial injection is injective on transitions with a defined output. -/
theorem partialStep_injective_at_some (f : α → Option α)
    (hinj : ∀ a b c, f a = some c → f b = some c → a = b)
    {o p : Option α} {c : α}
    (ho : partialStep f o = some c) (hp : partialStep f p = some c) : o = p := by
  cases o with
  | none => simp [partialStep] at ho
  | some a =>
    cases p with
    | none => simp [partialStep] at hp
    | some b =>
      exact congrArg some (hinj a b c (by simpa [partialStep] using ho)
        (by simpa [partialStep] using hp))

/-- No positive iterate can reach a start vertex outside the successor image. -/
theorem partialChain_no_return (f : α → Option α) (z : α)
    (hz : ∀ a, f a ≠ some z) (n : ℕ) :
    (partialStep f)^[n + 1] (some z) ≠ some z := by
  rw [Function.iterate_succ_apply']
  intro h
  cases he : (partialStep f)^[n] (some z) with
  | none => simp [he, partialStep] at h
  | some a => exact hz a (by simpa [he, partialStep] using h)

/-- Finite injective successor chains started outside the image must terminate.
This is the termination obligation in the simultaneous Lovász-chain construction. -/
theorem partialChain_terminates [Finite α] (f : α → Option α)
    (hinj : ∀ a b c, f a = some c → f b = some c → a = b)
    (z : α) (hz : ∀ a, f a ≠ some z) :
    ∃ n : ℕ, (partialStep f)^[n] (some z) = none := by
  classical
  by_contra hnever
  push Not at hnever
  have hi : Function.Injective (fun n : ℕ => (partialStep f)^[n] (some z)) := by
    intro m
    induction m with
    | zero =>
      intro n h
      cases n with
      | zero => rfl
      | succ n => exact ((partialChain_no_return f z hz n) h.symm).elim
    | succ m ih =>
      intro n h
      cases n with
      | zero => exact ((partialChain_no_return f z hz m) h).elim
      | succ n =>
        obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (hnever (m + 1))
        have hprev : (partialStep f)^[m] (some z) = (partialStep f)^[n] (some z) := by
          apply partialStep_injective_at_some f hinj (c := c)
          · simpa only [Function.iterate_succ_apply'] using hc
          · simpa only [Function.iterate_succ_apply'] using h.symm.trans hc
        exact congrArg Nat.succ (ih hprev)
  obtain ⟨m, n, hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => (partialStep f)^[n] (some z))
  exact hne (hi heq)

theorem partialStep_ne_source (f : α → Option α) (z : α)
    (hz : ∀ a, f a ≠ some z) (o : Option α) : partialStep f o ≠ some z := by
  cases o with
  | none => simp [partialStep]
  | some a => exact hz a

/-- Two active chains from sources outside the image can meet only at equal
indices from the same source. In particular distinct source chains are disjoint. -/
theorem partialChain_meeting (f : α → Option α)
    (hinj : ∀ a b c, f a = some c → f b = some c → a = b)
    (z w : α) (hz : ∀ a, f a ≠ some z) (hw : ∀ a, f a ≠ some w)
    (m n : ℕ) (c : α)
    (hm : (partialStep f)^[m] (some z) = some c)
    (hn : (partialStep f)^[n] (some w) = some c) : z = w ∧ m = n := by
  induction m generalizing n c with
  | zero =>
    have hzc : z = c := Option.some.inj hm
    cases n with
    | zero => exact ⟨hzc.trans (Option.some.inj hn).symm, rfl⟩
    | succ n =>
      have he : partialStep f ((partialStep f)^[n] (some w)) = some z := by
        simpa only [Function.iterate_succ_apply', ← hzc] using hn
      exact ((partialStep_ne_source f z hz _) he).elim
  | succ m ih =>
    cases n with
    | zero =>
      have hwc : w = c := Option.some.inj hn
      have he : partialStep f ((partialStep f)^[m] (some z)) = some w := by
        simpa only [Function.iterate_succ_apply', ← hwc] using hm
      exact ((partialStep_ne_source f w hw _) he).elim
    | succ n =>
      have hprev : (partialStep f)^[m] (some z) = (partialStep f)^[n] (some w) := by
        apply partialStep_injective_at_some f hinj (c := c)
        · simpa only [Function.iterate_succ_apply'] using hm
        · simpa only [Function.iterate_succ_apply'] using hn
      have hnot : (partialStep f)^[m] (some z) ≠ none := by
        intro he
        simp [Function.iterate_succ_apply', he, partialStep] at hm
      obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hnot
      obtain ⟨hzw, hmn⟩ := ih n d hd (hprev.symm.trans hd)
      exact ⟨hzw, congrArg Nat.succ hmn⟩

/-- A selected reachable vertex cannot be a fixed point of the successor. -/
theorem partialChain_no_fixed_point (f : α → Option α)
    (hinj : ∀ a b c, f a = some c → f b = some c → a = b)
    (z : α) (hz : ∀ a, f a ≠ some z) (n : ℕ) (v : α)
    (hv : (partialStep f)^[n] (some z) = some v) : f v ≠ some v := by
  intro hfix
  have hv' : (partialStep f)^[n + 1] (some z) = some v := by
    simp only [Function.iterate_succ_apply', hv, partialStep, Option.bind_some, hfix]
  have hmeet := partialChain_meeting f hinj z z hz hz n (n + 1) v hv hv'
  omega

/-- Every source has a last defined vertex, whose successor is undefined. -/
theorem partialChain_terminal [Finite α] (f : α → Option α)
    (hinj : ∀ a b c, f a = some c → f b = some c → a = b)
    (z : α) (hz : ∀ a, f a ≠ some z) :
    ∃ n : ℕ, ∃ t : α, (partialStep f)^[n] (some z) = some t ∧ f t = none := by
  obtain ⟨n, hn⟩ := partialChain_terminates f hinj z hz
  suffices h : ∀ n : ℕ, (partialStep f)^[n] (some z) = none →
      ∃ m : ℕ, ∃ t : α, (partialStep f)^[m] (some z) = some t ∧ f t = none from h n hn
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro hn
    cases he : (partialStep f)^[n] (some z) with
    | none => exact ih he
    | some t =>
      exact ⟨n, t, he, by simpa [Function.iterate_succ_apply', he, partialStep] using hn⟩

@[simp] theorem partialStep_iterate_none (f : α → Option α) (n : ℕ) :
    (partialStep f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Function.iterate_succ_apply', ih, partialStep]

/-- After the last defined vertex, every later chain state is undefined. -/
theorem partialChain_after_terminal (f : α → Option α) (z t : α) (n d : ℕ)
    (hn : (partialStep f)^[n] (some z) = some t) (ht : f t = none) :
    (partialStep f)^[n + (d + 1)] (some z) = none := by
  rw [Nat.add_comm n, Function.iterate_add_apply, hn,
    Function.iterate_succ_apply]
  simp [partialStep, ht]

/-- A deterministic chain has a unique terminal vertex, regardless of the
chosen witness for its stopping time. -/
theorem partialChain_terminal_unique (f : α → Option α) (z t u : α) (n m : ℕ)
    (hn : (partialStep f)^[n] (some z) = some t) (ht : f t = none)
    (hm : (partialStep f)^[m] (some z) = some u) (hu : f u = none) : t = u := by
  have hle : ∀ (t u : α) (n m : ℕ),
      (partialStep f)^[n] (some z) = some t → f t = none →
      (partialStep f)^[m] (some z) = some u → n ≤ m → t = u := by
    intro t u n m hn ht hm hnm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    cases d with
    | zero => exact Option.some.inj (hn.symm.trans (by simpa using hm))
    | succ d =>
      have he := partialChain_after_terminal f z t n d hn ht
      rw [hm] at he
      contradiction
  rcases le_total n m with hnm | hmn
  · exact hle t u n m hn ht hm hnm
  · exact (hle u t m n hm hu hn hmn).symm

/-- The terminal assignment from a finite source set is injective. This pays
the terminal-count premise used to bound the number of created cycles. -/
theorem exists_injective_terminal_map [Finite α] (f : α → Option α)
    (hinj : ∀ a b c, f a = some c → f b = some c → a = b)
    (Z : Finset α) (hZ : ∀ z ∈ Z, ∀ a, f a ≠ some z) :
    ∃ t : Z → α, Function.Injective t ∧
      ∀ z : Z, f (t z) = none ∧
        ∃ n : ℕ, (partialStep f)^[n] (some z.val) = some (t z) := by
  classical
  choose n t hor ht using (fun z : Z => partialChain_terminal f hinj z.val (hZ z.val z.property))
  refine ⟨t, ?_, fun z => ⟨ht z, n z, hor z⟩⟩
  intro z w htw
  have hmeet := partialChain_meeting f hinj z.val w.val
    (hZ z.val z.property) (hZ w.val w.property) (n z) (n w) (t z)
    (hor z) ((hor w).trans (congrArg some htw.symm))
  exact Subtype.ext hmeet.1

/-- Exactly one terminal is assigned to each source, and these are all the
reachable terminals. Thus the terminal budget is exactly the source budget. -/
theorem exists_terminal_finset [Finite α] (f : α → Option α)
    (hinj : ∀ a b c, f a = some c → f b = some c → a = b)
    (Z : Finset α) (hZ : ∀ z ∈ Z, ∀ a, f a ≠ some z) :
    ∃ T : Finset α, T.card = Z.card ∧
      (∀ t ∈ T, f t = none) ∧
      (∀ z ∈ Z, ∃ n : ℕ, ∃ t ∈ T, (partialStep f)^[n] (some z) = some t) ∧
      (∀ z ∈ Z, ∀ n : ℕ, ∀ t, (partialStep f)^[n] (some z) = some t →
        f t = none → t ∈ T) := by
  classical
  obtain ⟨t, hti, ht⟩ := exists_injective_terminal_map f hinj Z hZ
  refine ⟨Finset.univ.image t, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hti]
    simp
  · intro v hv
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hv
    exact (ht z).1
  · intro z hz
    obtain ⟨n, hn⟩ := (ht ⟨z, hz⟩).2
    exact ⟨n, t ⟨z, hz⟩, Finset.mem_image.mpr ⟨⟨z, hz⟩, Finset.mem_univ _, rfl⟩, hn⟩
  · intro z hz n v hn hv
    obtain ⟨m, hm⟩ := (ht ⟨z, hz⟩).2
    have heq := partialChain_terminal_unique f z v (t ⟨z, hz⟩) n m hn hv hm (ht ⟨z, hz⟩).1
    exact Finset.mem_image.mpr ⟨⟨z, hz⟩, Finset.mem_univ _, heq.symm⟩

/-- Disjoint pairs of terminals pay two source units per created cycle. This
counts terminals, not original deleted edges incident to the resulting cycle. -/
theorem disjoint_terminal_pairs_bound {ι : Type*} (C : Finset ι) (T : Finset α)
    (pair : ι → Finset α) (hpair : ∀ i ∈ C, (pair i).card = 2)
    (hsub : ∀ i ∈ C, pair i ⊆ T)
    (hd : Set.PairwiseDisjoint (C : Set ι) pair) : 2 * C.card ≤ T.card := by
  classical
  have hc : (C.biUnion pair).card = C.card * 2 := by
    rw [Finset.card_biUnion hd]
    exact Finset.sum_const_nat hpair
  have hs : C.biUnion pair ⊆ T := by
    intro v hv
    obtain ⟨i, hi, hv⟩ := Finset.mem_biUnion.mp hv
    exact hsub i hi hv
  have hcard := Finset.card_le_card hs
  omega

end PartialChains


/-- One orientation is chosen per path subgraph. All endpoint choices for the
same member use this presentation, so opposite-end predecessor comparisons do
not require a separate walk-uniqueness theorem. -/
structure PathPresentation (H : G.Subgraph) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath
  nonempty : ¬ walk.Nil
  toSubgraph_eq : walk.toSubgraph = H

noncomputable def pathPresentation {H : G.Subgraph} (hH : IsNonemptyPathSubgraph H) :
    PathPresentation H := by
  classical
  let a := hH.choose
  let b := hH.choose_spec.choose
  let p := hH.choose_spec.choose_spec.choose
  have hp := hH.choose_spec.choose_spec.choose_spec
  exact ⟨a, b, p, hp.1, hp.2.1, hp.2.2.symm⟩

namespace PathPresentation

/-- Predecessor of the root when the path is traversed from a selected endpoint.
The result is undefined unless the endpoint is valid, distinct from the root,
and the root lies on the path. -/
noncomputable def predecessor {H : G.Subgraph} (P : PathPresentation H) (x v : V) : Option V := by
  classical
  exact if x ∈ P.walk.support ∧ v ≠ x ∧ (v = P.start ∨ v = P.finish) then
    some (if v = P.start then P.walk.getVert (P.walk.support.idxOf x - 1)
      else P.walk.getVert (P.walk.support.idxOf x + 1))
    else none

theorem predecessor_defined_iff {H : G.Subgraph} (P : PathPresentation H) (x v : V) :
    (∃ y, P.predecessor x v = some y) ↔
      x ∈ P.walk.support ∧ v ≠ x ∧ (v = P.start ∨ v = P.finish) := by
  classical
  unfold predecessor
  split <;> simp_all

/-- Each defined predecessor owns an actual edge of the original path member. -/
theorem predecessor_adj {H : G.Subgraph} (P : PathPresentation H) (x v y : V)
    (hy : P.predecessor x v = some y) : H.Adj x y := by
  classical
  have hg := (P.predecessor_defined_iff x v).mp ⟨y, hy⟩
  have hidx := P.walk.getVert_support_idxOf hg.1
  have hle : P.walk.support.idxOf x ≤ P.walk.length := by
    have := List.idxOf_lt_length_of_mem hg.1
    rw [Walk.length_support] at this
    omega
  rw [predecessor, if_pos hg] at hy
  split_ifs at hy with hv
  · have hpos : 0 < P.walk.support.idxOf x := by
      by_contra hn
      have hz : P.walk.support.idxOf x = 0 := by omega
      have hx : P.start = x := by simpa [hz] using hidx
      exact hg.2.1 (hv.trans hx)
    have he := P.walk.toSubgraph_adj_getVert (show P.walk.support.idxOf x - 1 < P.walk.length by omega)
    have heq : P.walk.support.idxOf x - 1 + 1 = P.walk.support.idxOf x := by omega
    rw [heq, hidx, P.toSubgraph_eq] at he
    exact (Option.some.inj hy) ▸ he.symm
  · have hvf : v = P.finish := hg.2.2.resolve_left hv
    have hlt : P.walk.support.idxOf x < P.walk.length := by
      by_contra hn
      have hz : P.walk.support.idxOf x = P.walk.length := by omega
      have hx : P.finish = x := by simpa [hz] using hidx
      exact hg.2.1 (hvf.trans hx)
    have he := P.walk.toSubgraph_adj_getVert hlt
    rw [hidx, P.toSubgraph_eq] at he
    exact (Option.some.inj hy) ▸ he

/-- Opposite endpoints of one simple path have distinct root predecessors. -/
theorem predecessor_injective {H : G.Subgraph} (P : PathPresentation H) (x a b y : V)
    (ha : P.predecessor x a = some y) (hb : P.predecessor x b = some y) : a = b := by
  classical
  have hga := (P.predecessor_defined_iff x a).mp ⟨y, ha⟩
  have hgb := (P.predecessor_defined_iff x b).mp ⟨y, hb⟩
  by_contra hab
  have hboth : x ≠ P.start ∧ x ≠ P.finish := by
    rcases hga.2.2 with ha | ha <;> rcases hgb.2.2 with hb | hb <;> grind
  have hidx := P.walk.getVert_support_idxOf hga.1
  have hle : P.walk.support.idxOf x ≤ P.walk.length := by
    have := List.idxOf_lt_length_of_mem hga.1
    rw [Walk.length_support] at this
    omega
  have hpos : 0 < P.walk.support.idxOf x := by
    by_contra hn
    have hz : P.walk.support.idxOf x = 0 := by omega
    exact hboth.1 (by simpa [hz] using hidx.symm)
  have hlt : P.walk.support.idxOf x < P.walk.length := by
    by_contra hn
    have hz : P.walk.support.idxOf x = P.walk.length := by omega
    exact hboth.2 (by simpa [hz] using hidx.symm)
  have hpne : P.walk.getVert (P.walk.support.idxOf x - 1) ≠
      P.walk.getVert (P.walk.support.idxOf x + 1) := by
    intro he
    have hi := P.isPath.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) he
    omega
  rw [predecessor, if_pos hga] at ha
  rw [predecessor, if_pos hgb] at hb
  split_ifs at ha hb <;> grind

end PathPresentation


/-- An endpoint path is selected for every original neighbor of the root.
This is data available from an arbitrary residual partition when all these
neighbors have odd residual degree. -/
structure EndpointSelection (D : Finset G.Subgraph) (x : V) where
  owner : {v // G.Adj x v} → D
  presentation : ∀ H : D, PathPresentation H.val
  starts : ∀ v, PathStartsAt (owner v).val v.val

noncomputable def endpointSelection [Fintype V] (D : Finset G.Subgraph) (x : V)
    (hp : ∀ H ∈ D, IsNonemptyPathSubgraph H)
    (he : ∀ v, G.Adj x v → ∃ H ∈ D, PathStartsAt H v) : EndpointSelection D x := by
  classical
  choose owner hmem hstart using (fun v : {v // G.Adj x v} => he v.val v.property)
  exact ⟨fun v => ⟨owner v, hmem v⟩, fun H => pathPresentation (hp H.val H.property), hstart⟩

namespace EndpointSelection

noncomputable def predecessor {D : Finset G.Subgraph} {x : V}
    (S : EndpointSelection D x) (v : V) : Option V := by
  classical
  exact if hv : G.Adj x v then (S.presentation (S.owner ⟨v, hv⟩)).predecessor x v else none

/-- A predecessor value identifies an edge in the selected partition member. -/
theorem predecessor_edge {D : Finset G.Subgraph} {x v y : V}
    (S : EndpointSelection D x) (h : S.predecessor v = some y) :
    ∃ hv : G.Adj x v, (S.owner ⟨v, hv⟩).val.Adj x y := by
  classical
  unfold predecessor at h
  split at h
  · rename_i hv
    exact ⟨hv, (S.presentation (S.owner ⟨v, hv⟩)).predecessor_adj x v y h⟩
  · contradiction

/-- Edge disjointness makes the actual path-predecessor map partially injective. -/
theorem predecessor_injective {D : Finset G.Subgraph} {x : V}
    (S : EndpointSelection D x)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) Subgraph.edgeSet)
    (a b y : V) (ha : S.predecessor a = some y) (hb : S.predecessor b = some y) : a = b := by
  classical
  obtain ⟨hxa, hea⟩ := S.predecessor_edge ha
  obtain ⟨hxb, heb⟩ := S.predecessor_edge hb
  have ho : S.owner ⟨a, hxa⟩ = S.owner ⟨b, hxb⟩ := by
    apply Subtype.ext
    by_contra hn
    have hdisj := hd (S.owner ⟨a, hxa⟩).property (S.owner ⟨b, hxb⟩).property hn
    exact Set.disjoint_left.mp hdisj (show s(x,y) ∈ (S.owner ⟨a,hxa⟩).val.edgeSet from hea)
      (show s(x,y) ∈ (S.owner ⟨b,hxb⟩).val.edgeSet from heb)
  simp only [predecessor, dif_pos hxa] at ha
  simp only [predecessor, dif_pos hxb] at hb
  rw [ho] at ha
  exact (S.presentation (S.owner ⟨b, hxb⟩)).predecessor_injective x a b y ha hb

/-- A deleted root edge cannot appear as a predecessor value. -/
theorem deleted_edge_outside_predecessor_image {D : Finset G.Subgraph} {x z : V}
    (S : EndpointSelection D x) (hz : ∀ H ∈ D, ¬ H.Adj x z) :
    ∀ a, S.predecessor a ≠ some z := by
  intro a ha
  obtain ⟨hxa, he⟩ := S.predecessor_edge ha
  exact hz _ (S.owner ⟨a,hxa⟩).property he

/-- The terminal budget for the actual graph-derived map equals the number of
deleted edges. No restoration theorem or cycle bound is assumed here. -/
theorem exists_terminal_set [Finite V] {D : Finset G.Subgraph} {x : V}
    (S : EndpointSelection D x)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) Subgraph.edgeSet)
    (Z : Finset V) (hz : ∀ z ∈ Z, ∀ H ∈ D, ¬ H.Adj x z) :
    ∃ T : Finset V, T.card = Z.card ∧
      (∀ t ∈ T, S.predecessor t = none) ∧
      (∀ z ∈ Z, ∃ n : ℕ, ∃ t ∈ T,
        (partialStep S.predecessor)^[n] (some z) = some t) ∧
      (∀ z ∈ Z, ∀ n : ℕ, ∀ t,
        (partialStep S.predecessor)^[n] (some z) = some t →
        S.predecessor t = none → t ∈ T) := by
  exact exists_terminal_finset S.predecessor (S.predecessor_injective hd) Z
    (fun z hzm => S.deleted_edge_outside_predecessor_image (hz z hzm))

/-- A predecessor is always an original neighbor of the root. -/
theorem predecessor_value_adj {D : Finset G.Subgraph} {x v y : V}
    (S : EndpointSelection D x) (h : S.predecessor v = some y) : G.Adj x y := by
  obtain ⟨hv, he⟩ := S.predecessor_edge h
  exact (S.owner ⟨v,hv⟩).val.adj_sub he

/-- Among original neighbors, the terminal condition says exactly that the
selected endpoint path avoids the root. -/
theorem predecessor_none_iff_avoids [Fintype V] {D : Finset G.Subgraph} {x v : V}
    (S : EndpointSelection D x) (hv : G.Adj x v) :
    S.predecessor v = none ↔ x ∉ (S.presentation (S.owner ⟨v,hv⟩)).walk.support := by
  classical
  let P := S.presentation (S.owner ⟨v,hv⟩)
  have he : v = P.start ∨ v = P.finish := by
    apply (pathStartsAt_iff_endpoints P.walk P.isPath P.nonempty v).mp
    rw [P.toSubgraph_eq]
    exact S.starts ⟨v,hv⟩
  have hne : v ≠ x := hv.ne.symm
  change (if h : G.Adj x v then
    (S.presentation (S.owner ⟨v,h⟩)).predecessor x v else none) = none ↔ _
  rw [dif_pos hv]
  change P.predecessor x v = none ↔ x ∉ P.walk.support
  simp [PathPresentation.predecessor, he, hne]

/-- Every defined chain vertex remains an original neighbor of the root. -/
theorem reachable_vertex_adj {D : Finset G.Subgraph} {x z v : V}
    (S : EndpointSelection D x) (hz : G.Adj x z) (n : ℕ)
    (hn : (partialStep S.predecessor)^[n] (some z) = some v) : G.Adj x v := by
  cases n with
  | zero => simpa using (Option.some.inj hn ▸ hz)
  | succ n =>
    rw [Function.iterate_succ_apply'] at hn
    cases he : (partialStep S.predecessor)^[n] (some z) with
    | none => simp [he, partialStep] at hn
    | some w =>
      exact S.predecessor_value_adj (by simpa [he, partialStep] using hn)

end EndpointSelection

section ReachableSets

variable {α : Type*}

/-- Vertices visited by the partial-function chains starting at a source set. -/
def ChainReachable (f : α → Option α) (Z : Finset α) (v : α) : Prop :=
  ∃ z ∈ Z, ∃ n : ℕ, (partialStep f)^[n] (some z) = some v

theorem chainReachable_source (f : α → Option α) (Z : Finset α) {v : α} (hv : v ∈ Z) :
    ChainReachable f Z v := ⟨v, hv, 0, rfl⟩

theorem chainReachable_successor (f : α → Option α) (Z : Finset α) {v w : α}
    (hv : ChainReachable f Z v) (hvw : f v = some w) : ChainReachable f Z w := by
  obtain ⟨z, hz, n, hn⟩ := hv
  exact ⟨z, hz, n+1, by rw [Function.iterate_succ_apply', hn]; exact hvw⟩

/-- Each reachable non-source has a reachable predecessor. -/
theorem chainReachable_predecessor (f : α → Option α) (Z : Finset α) {v : α}
    (hv : ChainReachable f Z v) (hz : v ∉ Z) :
    ∃ u, ChainReachable f Z u ∧ f u = some v := by
  obtain ⟨z, hzm, n, hn⟩ := hv
  cases n with
  | zero => exact (hz ((Option.some.inj hn) ▸ hzm)).elim
  | succ n =>
    rw [Function.iterate_succ_apply'] at hn
    cases he : (partialStep f)^[n] (some z) with
    | none => simp [he, partialStep] at hn
    | some u => exact ⟨u, ⟨z, hzm, n, he⟩, by simpa [he, partialStep] using hn⟩

/-- The source and chain-edge relation give the exact incoming-edge accounting:
reachable non-sources have a predecessor; sources and outside vertices have none. -/
theorem chainReachable_predecessor_iff (f : α → Option α) (Z : Finset α)
    (hZ : ∀ z ∈ Z, ∀ a, f a ≠ some z) (v : α) :
    (∃ u, ChainReachable f Z u ∧ f u = some v) ↔ ChainReachable f Z v ∧ v ∉ Z := by
  constructor
  · rintro ⟨u, hu, huv⟩
    exact ⟨chainReachable_successor f Z hu huv, fun hv => hZ v hv u huv⟩
  · rintro ⟨hv, hz⟩
    exact chainReachable_predecessor f Z hv hz

theorem chainReachable_no_fixed_point (f : α → Option α)
    (hinj : ∀ a b c, f a = some c → f b = some c → a = b)
    (Z : Finset α) (hZ : ∀ z ∈ Z, ∀ a, f a ≠ some z)
    {v : α} (hv : ChainReachable f Z v) : f v ≠ some v := by
  obtain ⟨z, hz, n, hn⟩ := hv
  exact partialChain_no_fixed_point f hinj z (hZ z hz) n v hn

end ReachableSets

/-- Split immediately before a specified noninitial root occurrence. -/
theorem exists_split_before_root {a b x : V} (p : G.Walk a b)
    (hx : x ∈ p.support) (hxa : x ≠ a) :
    ∃ (c : V) (q : G.Walk a c) (r : G.Walk x b) (hcx : G.Adj c x),
      p = q.append (.cons hcx r) := by
  obtain ⟨q, r, he⟩ := Walk.mem_support_iff_exists_append.mp hx
  cases q using Walk.concatRec with
  | Hnil => exact (hxa rfl).elim
  | Hconcat q h => exact ⟨_, q, r, h, by simpa only [Walk.concat_append] using he⟩

/-- Every noninitial root occurrence admits the actual one-end switch, with
one removed edge, one inserted original edge, and a nonempty simple output. -/
theorem exists_one_endpoint_switch {a b x : V} (p : G.Walk a b)
    (hp : p.IsPath) (hx : x ∈ p.support) (hax : G.Adj a x) :
    ∃ (c : V) (q : G.Walk c b), q.IsPath ∧ ¬ q.Nil ∧
      q.edgeSet = insert s(a,x) (p.edgeSet \ {s(c,x)}) ∧
      s(c,x) ∈ p.edgeSet := by
  obtain ⟨c, l, r, hcx, rfl⟩ := exists_split_before_root p hx hax.ne.symm
  refine ⟨c, l.reverse.append (.cons hax r),
    path_switch_one_isPath l r hcx hax hp, ?_,
    path_switch_one_exact_edges l r hcx hax hp, ?_⟩
  · rw [Walk.not_nil_iff_lt_length]
    simp
  · simp

/-- Split on both sides of an internal root. -/
theorem exists_split_around_root {a b x : V} (p : G.Walk a b)
    (hx : x ∈ p.support) (hxa : x ≠ a) (hxb : x ≠ b) :
    ∃ (c d : V) (q : G.Walk a c) (r : G.Walk d b)
      (hcx : G.Adj c x) (hxd : G.Adj x d),
      p = q.append (.cons hcx (.cons hxd r)) := by
  obtain ⟨c, q, r, hcx, he⟩ := exists_split_before_root p hx hxa
  cases r with
  | nil => exact (hxb rfl).elim
  | cons hxd r => exact ⟨c, _, q, r, hcx, hxd, he⟩

/-- Every internal root occurrence admits the simultaneous two-end switch. -/
theorem exists_two_endpoint_switch {a b x : V} (p : G.Walk a b)
    (hp : p.IsPath) (hx : x ∈ p.support) (hax : G.Adj a x) (hxb : G.Adj x b) :
    ∃ (c d : V) (q : G.Walk c d), q.IsPath ∧ ¬ q.Nil ∧
      q.edgeSet = {s(a,x),s(x,b)} ∪ (p.edgeSet \ {s(c,x),s(x,d)}) ∧
      s(c,x) ∈ p.edgeSet ∧ s(x,d) ∈ p.edgeSet := by
  obtain ⟨c, d, l, r, hcx, hxd, rfl⟩ := exists_split_around_root p hx hax.ne.symm hxb.ne
  refine ⟨c, d, l.reverse.append (.cons hax (.cons hxb r.reverse)),
    path_switch_two_isPath l r hcx hxd hax hxb hp, ?_,
    path_switch_two_exact_edges l r hcx hxd hax hxb hp, ?_, ?_⟩
  · rw [Walk.not_nil_iff_lt_length]
    simp
  · simp
  · simp

/-- The root index in a simple path is determined by a split immediately before it. -/
theorem root_index_of_split [DecidableEq V] {a c x b : V}
    (p : G.Walk a b) (hp : p.IsPath) (l : G.Walk a c) (r : G.Walk x b)
    (hcx : G.Adj c x) (he : p = l.append (.cons hcx r)) :
    p.support.idxOf x = l.length + 1 := by
  have hx : x ∈ p.support := by rw [he]; simp
  have hi := p.getVert_support_idxOf hx
  have hj : p.getVert (l.length+1) = x := by
    rw [he, Walk.getVert_append]
    simp
  apply hp.getVert_injOn _ _ (hi.trans hj.symm)
  · have hh := List.idxOf_lt_length_of_mem hx
    rw [Walk.length_support] at hh
    change p.support.idxOf x ≤ p.length
    omega
  · rw [he]
    simp only [Set.mem_ofPred_eq, Walk.length_append, Walk.length_cons]
    omega

namespace PathPresentation

/-- The canonical predecessor at the first endpoint is the edge exposed by
the actual split used in a one-end switch. -/
theorem predecessor_start_of_split {H : G.Subgraph} (P : PathPresentation H)
    {c x : V} (l : G.Walk P.start c) (r : G.Walk x P.finish)
    (hcx : G.Adj c x) (he : P.walk = l.append (.cons hcx r)) (hx : P.start ≠ x) :
    P.predecessor x P.start = some c := by
  classical
  have hs : x ∈ P.walk.support := by rw [he]; simp
  have hi := root_index_of_split P.walk P.isPath l r hcx he
  rw [predecessor, if_pos ⟨hs, hx, Or.inl rfl⟩, if_pos rfl, hi, Nat.add_sub_cancel]
  rw [he, Walk.getVert_append']
  simp

/-- The canonical predecessor at the last endpoint is the second root edge
exposed by the split used in a two-end switch. -/
theorem predecessor_finish_of_split {H : G.Subgraph} (P : PathPresentation H)
    {c d x : V} (l : G.Walk P.start c) (r : G.Walk d P.finish)
    (hcx : G.Adj c x) (hxd : G.Adj x d)
    (he : P.walk = l.append (.cons hcx (.cons hxd r))) (hx : P.finish ≠ x) :
    P.predecessor x P.finish = some d := by
  classical
  have hs : x ∈ P.walk.support := by rw [he]; simp
  have hi := root_index_of_split P.walk P.isPath l (.cons hxd r) hcx he
  have hne : P.finish ≠ P.start := Ne.symm (P.isPath.nil_iff_eq.not.mp P.nonempty)
  rw [predecessor, if_pos ⟨hs, hx, Or.inr rfl⟩, if_neg hne, hi]
  rw [he, Walk.getVert_append]
  simp [Nat.add_assoc]

end PathPresentation

end Erdos583
end Source10_Erdos583_StarRestore
/- END Erdos583.StarRestore -/

/- BEGIN Erdos583.VertexErase; source SHA256 6cade729dcc0c8be93d8411e3c906cbda52a215be5f98dda2b6aa00f039b0666 -/
section Source11_Erdos583_VertexErase



/-! Removing a vertex from actual simple paths. The vertex type stays fixed;
the removed vertex becomes isolated. -/

noncomputable section

namespace Erdos583

open SimpleGraph
attribute [local instance] Classical.propDecidable

variable {V : Type*} {G : SimpleGraph V}

def isolateVertex (G : SimpleGraph V) (x : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ≠ x ∧ b ≠ x
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

def avoidsVertex (x : V) : Set (Sym2 V) := {e | x ∉ e}

theorem isolateVertex_le (G : SimpleGraph V) (x : V) : isolateVertex G x ≤ G :=
  fun _ _ h => h.1

theorem isolateVertex_edgeSet (G : SimpleGraph V) (x : V) :
    (isolateVertex G x).edgeSet = G.edgeSet ∩ avoidsVertex x := by
  ext e
  induction e using Sym2.ind with
  | _ a b => simp [isolateVertex, avoidsVertex, Sym2.mem_iff, eq_comm]

/-- A simple walk avoiding the removed vertex gives zero or one nonempty path
with exactly the same original edges. Empty walks contribute no part. -/
theorem avoiding_walk_family (x : V) {a b : V} (p : G.Walk a b)
    (hp : p.IsPath) (hx : x ∉ p.support) :
    ∃ D : Finset (isolateVertex G x).Subgraph,
      (∀ P ∈ D, IsNonemptyPathSubgraph P) ∧
      Set.PairwiseDisjoint (D : Set (isolateVertex G x).Subgraph) (fun P => P.edgeSet) ∧
      (⋃ P ∈ D, P.edgeSet) = p.edgeSet ∧ D.card ≤ 1 := by
  classical
  by_cases hn : p.Nil
  · refine ⟨∅, by simp, by simp, ?_, by simp⟩
    have he : p.edgeSet = ∅ := by
      have hl := hn.length_eq_zero
      have hedges : p.edges = [] := List.eq_nil_iff_length_eq_zero.mpr (by simpa using hl)
      simp [Walk.edgeSet, hedges]
    simp [he]
  · have hE : ∀ e ∈ p.edges, e ∈ (isolateVertex G x).edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        exact ⟨p.adj_of_mem_edges he,
          fun heq => hx (heq ▸ p.fst_mem_support_of_mem_edges he),
          fun heq => hx (heq ▸ p.snd_mem_support_of_mem_edges he)⟩
    let q := p.transfer (isolateVertex G x) hE
    have hq : q.IsPath := hp.transfer hE
    have hqn : ¬ q.Nil := by
      simpa only [← Walk.length_eq_zero_iff, q, Walk.length_transfer] using hn
    refine ⟨{q.toSubgraph}, ?_, by simp, ?_, by simp⟩
    · intro P hP
      have hPq : P = q.toSubgraph := Finset.mem_singleton.mp hP
      subst P
      exact ⟨a, b, q, hq, hqn, rfl⟩
    · simpa only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left,
        Walk.edgeSet_toSubgraph] using p.edgeSet_transfer hE

theorem avoiding_walk_edges (x : V) {a b : V} (p : G.Walk a b)
    (hx : x ∉ p.support) : p.edgeSet ⊆ avoidsVertex x := by
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    intro hmem
    rcases Sym2.mem_iff.mp hmem with hxu | hxv
    · exact hx (hxu ▸ p.fst_mem_support_of_mem_edges he)
    · exact hx (hxv ▸ p.snd_mem_support_of_mem_edges he)

private theorem union_partial_families {H : SimpleGraph V}
    (D E : Finset H.Subgraph) (A B : Set (Sym2 V))
    (hDpath : ∀ P ∈ D, IsNonemptyPathSubgraph P)
    (hEpath : ∀ P ∈ E, IsNonemptyPathSubgraph P)
    (hDdis : Set.PairwiseDisjoint (D : Set H.Subgraph) (fun P => P.edgeSet))
    (hEdis : Set.PairwiseDisjoint (E : Set H.Subgraph) (fun P => P.edgeSet))
    (hDA : (⋃ P ∈ D, P.edgeSet) = A) (hEB : (⋃ P ∈ E, P.edgeSet) = B)
    (hAB : Disjoint A B) :
    (∀ P ∈ D ∪ E, IsNonemptyPathSubgraph P) ∧
    Set.PairwiseDisjoint (↑(D ∪ E) : Set H.Subgraph) (fun P => P.edgeSet) ∧
    (⋃ P ∈ D ∪ E, P.edgeSet) = A ∪ B := by
  have hcross (P : H.Subgraph) (hP : P ∈ D) (Q : H.Subgraph) (hQ : Q ∈ E) :
      Disjoint P.edgeSet Q.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heP heQ
    apply Set.disjoint_left.mp hAB
    · rw [← hDA]; exact Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨hP, heP⟩⟩
    · rw [← hEB]; exact Set.mem_iUnion.mpr ⟨Q, Set.mem_iUnion.mpr ⟨hQ, heQ⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro P hP
    exact (Finset.mem_union.mp hP).elim (hDpath P) (hEpath P)
  · intro P hP Q hQ hne
    rcases Finset.mem_union.mp hP with hP | hP <;>
      rcases Finset.mem_union.mp hQ with hQ | hQ
    · exact hDdis hP hQ hne
    · exact hcross P hP Q hQ
    · exact (hcross Q hQ P hP).symm
    · exact hEdis hP hQ hne
  · rw [← hDA, ← hEB]
    ext e
    simp only [Set.mem_iUnion, Finset.mem_union, exists_prop, Set.mem_union]
    aesop

theorem two_avoiding_walks_family (x : V) {a b c d : V}
    (p : G.Walk a b) (q : G.Walk c d) (hp : p.IsPath) (hq : q.IsPath)
    (hpx : x ∉ p.support) (hqx : x ∉ q.support) (hpq : Disjoint p.edgeSet q.edgeSet) :
    ∃ D : Finset (isolateVertex G x).Subgraph,
      (∀ P ∈ D, IsNonemptyPathSubgraph P) ∧
      Set.PairwiseDisjoint (D : Set (isolateVertex G x).Subgraph) (fun P => P.edgeSet) ∧
      (⋃ P ∈ D, P.edgeSet) = p.edgeSet ∪ q.edgeSet ∧ D.card ≤ 2 := by
  obtain ⟨D, hDp, hDd, hDE, hDc⟩ := avoiding_walk_family x p hp hpx
  obtain ⟨E, hEp, hEd, hEE, hEc⟩ := avoiding_walk_family x q hq hqx
  obtain ⟨hpath, hdis, hcover⟩ := union_partial_families D E p.edgeSet q.edgeSet
    hDp hEp hDd hEd hDE hEE hpq
  refine ⟨D ∪ E, hpath, hdis, hcover, ?_⟩
  exact (Finset.card_union_le D E).trans (by omega)

theorem erase_initial_vertex_family {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    ∃ D : Finset (isolateVertex G a).Subgraph,
      (∀ P ∈ D, IsNonemptyPathSubgraph P) ∧
      Set.PairwiseDisjoint (D : Set (isolateVertex G a).Subgraph) (fun P => P.edgeSet) ∧
      (⋃ P ∈ D, P.edgeSet) = p.edgeSet ∩ avoidsVertex a ∧ D.card ≤ 1 := by
  cases p with
  | nil =>
    exact ⟨∅, by simp, by simp, by simp, by simp⟩
  | @cons a c b h p =>
    have hpx : a ∉ p.support := ((Walk.cons_isPath_iff h p).mp hp).2
    obtain ⟨D, hpath, hdis, hcover, hcard⟩ :=
      avoiding_walk_family a p ((Walk.cons_isPath_iff h p).mp hp).1 hpx
    refine ⟨D, hpath, hdis, ?_, hcard⟩
    rw [hcover, Walk.edgeSet_cons]
    have hs := avoiding_walk_edges a p hpx
    ext e
    have hn : s(a,c) ∉ avoidsVertex a := by simp [avoidsVertex]
    simp only [Set.mem_inter_iff, Set.mem_insert_iff]
    constructor
    · intro he; exact ⟨Or.inr he, hs he⟩
    · rintro ⟨he | he, ha⟩
      · subst e; exact (hn ha).elim
      · exact he

/-- Deleting a vertex from one nonempty path creates at most two pieces.
The degree-sensitive bound pays the split by actual incident original edges. -/
theorem erase_path_family [Fintype V] {a b : V} (p : G.Walk a b)
    (hp : p.IsPath) (hn : ¬ p.Nil) (x : V) :
    ∃ D : Finset (isolateVertex G x).Subgraph,
      (∀ P ∈ D, IsNonemptyPathSubgraph P) ∧
      Set.PairwiseDisjoint (D : Set (isolateVertex G x).Subgraph) (fun P => P.edgeSet) ∧
      (⋃ P ∈ D, P.edgeSet) = p.edgeSet ∩ avoidsVertex x ∧
      2 * D.card ≤ 2 + p.toSubgraph.degree x := by
  by_cases hxa : x = a
  · subst x
    obtain ⟨D, hpath, hdis, hcover, hcard⟩ := erase_initial_vertex_family p hp
    exact ⟨D, hpath, hdis, hcover, by omega⟩
  by_cases hxb : x = b
  · subst x
    obtain ⟨D, hpath, hdis, hcover, hcard⟩ := erase_initial_vertex_family p.reverse hp.reverse
    exact ⟨D, hpath, hdis, by simpa using hcover, by omega⟩
  by_cases hxs : x ∈ p.support
  · obtain ⟨c, d, l, r, hcx, hxd, heq⟩ := exists_split_around_root p hxs hxa hxb
    have hsplit : (l.append (.cons hcx (.cons hxd r))).IsPath := heq ▸ hp
    have hlx : x ∉ l.support := by
      intro hx
      exact (hsplit.ne_of_mem_support_of_append hcx.ne.symm hx (by simp)) rfl
    have hrx : x ∉ r.support := ((Walk.cons_isPath_iff hxd r).mp hsplit.of_append_right.tail).2
    have hlr : Disjoint l.edgeSet r.edgeSet := by
      have hnod := hsplit.isTrail.edges_nodup
      simp only [Walk.edges_append, Walk.edges_cons, List.nodup_append, List.nodup_cons] at hnod
      apply Set.disjoint_left.mpr
      intro e hel her
      exact hnod.2.2 e hel e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ her)) rfl
    have hcr : (Walk.cons hcx (Walk.cons hxd r)).IsPath := hsplit.of_append_right
    have hxr : (Walk.cons hxd r).IsPath := (Walk.cons_isPath_iff hcx _).mp hcr |>.1
    have hrp : r.IsPath := (Walk.cons_isPath_iff hxd _).mp hxr |>.1
    obtain ⟨D, hpath, hdis, hcover, hcard⟩ := two_avoiding_walks_family x l r
      hsplit.of_append_left hrp hlx hrx hlr
    refine ⟨D, hpath, hdis, ?_, ?_⟩
    · rw [hcover, heq, Walk.edgeSet_append, Walk.edgeSet_cons, Walk.edgeSet_cons]
      have hl := avoiding_walk_edges x l hlx
      have hr := avoiding_walk_edges x r hrx
      have hc : s(c,x) ∉ avoidsVertex x := by simp [avoidsVertex]
      have hd : s(x,d) ∉ avoidsVertex x := by simp [avoidsVertex]
      ext e
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_insert_iff]
      aesop
    · rw [pathSubgraph_degree p hp hn x, if_neg (by tauto), if_pos hxs]
      omega
  · obtain ⟨D, hpath, hdis, hcover, hcard⟩ := avoiding_walk_family x p hp hxs
    refine ⟨D, hpath, hdis, ?_, by omega⟩
    rw [hcover, Set.inter_eq_left.mpr (avoiding_walk_edges x p hxs)]

/-- Assemble disjoint local path families whose edges are the restrictions of
an original edge partition. This does not assume a path-count inequality. -/
theorem assemble_restricted_families {H : SimpleGraph V} (D : Finset G.Subgraph)
    (hdec : IsDecomposition G D) (hHG : H ≤ G)
    (F : G.Subgraph → Finset H.Subgraph)
    (hpaths : ∀ P ∈ D, ∀ Q ∈ F P, IsNonemptyPathSubgraph Q)
    (hdis : ∀ P ∈ D, Set.PairwiseDisjoint (↑(F P) : Set H.Subgraph) (fun Q => Q.edgeSet))
    (hcover : ∀ P ∈ D, (⋃ Q ∈ F P, Q.edgeSet) = P.edgeSet ∩ H.edgeSet) :
    HasPathPartition H (∑ P ∈ D, (F P).card) := by
  classical
  have hsub (P : G.Subgraph) (hP : P ∈ D) (Q : H.Subgraph) (hQ : Q ∈ F P) :
      Q.edgeSet ⊆ P.edgeSet := by
    intro e he
    have heU : e ∈ ⋃ R ∈ F P, R.edgeSet :=
      Set.mem_iUnion.mpr ⟨Q, Set.mem_iUnion.mpr ⟨hQ, he⟩⟩
    rw [hcover P hP] at heU
    exact heU.1
  refine ⟨D.biUnion F, ?_, ?_, Finset.card_biUnion_le⟩
  · intro Q hQ
    obtain ⟨P, hP, hQ⟩ := Finset.mem_biUnion.mp hQ
    exact hpaths P hP Q hQ
  · constructor
    · intro Q hQ R hR hne
      obtain ⟨P, hP, hQ⟩ := Finset.mem_biUnion.mp hQ
      obtain ⟨S, hS, hR⟩ := Finset.mem_biUnion.mp hR
      by_cases hPS : P = S
      · subst S; exact hdis P hP hQ hR hne
      · exact (hdec.1 hP hS hPS).mono (hsub P hP Q hQ) (hsub S hS R hR)
    · ext e
      simp only [Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨Q, hQ, heQ⟩
        exact Q.edgeSet_subset heQ
      · intro he
        have heG := SimpleGraph.edgeSet_mono hHG he
        rw [← hdec.2] at heG
        simp only [Set.mem_iUnion, exists_prop] at heG
        obtain ⟨P, hP, heP⟩ := heG
        have hlocal : e ∈ ⋃ Q ∈ F P, Q.edgeSet := by
          rw [hcover P hP]
          exact ⟨heP, he⟩
        simp only [Set.mem_iUnion, exists_prop] at hlocal
        obtain ⟨Q, hQ, heQ⟩ := hlocal
        exact ⟨Q, Finset.mem_biUnion.mpr ⟨P, hP, hQ⟩, heQ⟩

/-- Every supplied q-path partition survives deletion of a vertex with at
most degree(x)/2 additional paths. No optimality or exposed endpoint is used. -/
theorem erase_vertex_path_bound [Fintype V] (x : V) {q : ℕ}
    (hq : HasPathPartition G q) :
    HasPathBound (isolateVertex G x) ((q : ℚ) + (G.degree x : ℚ) / 2) := by
  classical
  obtain ⟨D, hpath, hdec, hcard⟩ := hq
  have hex (P : G.Subgraph) (hP : P ∈ D) :
      ∃ E : Finset (isolateVertex G x).Subgraph,
        (∀ Q ∈ E, IsNonemptyPathSubgraph Q) ∧
        Set.PairwiseDisjoint (E : Set (isolateVertex G x).Subgraph) (fun Q => Q.edgeSet) ∧
        (⋃ Q ∈ E, Q.edgeSet) = P.edgeSet ∩ (isolateVertex G x).edgeSet ∧
        2 * E.card ≤ 2 + P.degree x := by
    obtain ⟨a, b, p, hp, hn, rfl⟩ := hpath P hP
    obtain ⟨E, hEp, hEd, hEE, hEc⟩ := erase_path_family p hp hn x
    refine ⟨E, hEp, hEd, ?_, hEc⟩
    rw [hEE, Walk.edgeSet_toSubgraph, isolateVertex_edgeSet]
    ext e
    have hsub := p.edges_subset_edgeSet
    simp only [Set.mem_inter_iff]
    exact ⟨fun h => ⟨h.1, hsub h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  let F : G.Subgraph → Finset (isolateVertex G x).Subgraph := fun P =>
    if hP : P ∈ D then Classical.choose (hex P hP) else ∅
  have hF (P : G.Subgraph) (hP : P ∈ D) :
      (∀ Q ∈ F P, IsNonemptyPathSubgraph Q) ∧
      Set.PairwiseDisjoint (↑(F P) : Set (isolateVertex G x).Subgraph) (fun Q => Q.edgeSet) ∧
      (⋃ Q ∈ F P, Q.edgeSet) = P.edgeSet ∩ (isolateVertex G x).edgeSet ∧
      2 * (F P).card ≤ 2 + P.degree x := by
    simpa only [F, dif_pos hP] using Classical.choose_spec (hex P hP)
  have hpart := assemble_restricted_families D hdec (isolateVertex_le G x) F
    (fun P hP => (hF P hP).1) (fun P hP => (hF P hP).2.1)
    (fun P hP => (hF P hP).2.2.1)
  have hsum : 2 * (∑ P ∈ D, (F P).card) ≤ 2 * D.card + G.degree x := by
    have hs := Finset.sum_le_sum (s := D) (fun P hP => (hF P hP).2.2.2)
    rw [← Finset.mul_sum, Finset.sum_add_distrib] at hs
    simp only [Finset.sum_const_nat] at hs
    rw [← degree_eq_sum_of_decomposition D hdec x] at hs
    omega
  apply hasPathBound_iff_exists_partition.mpr
  refine ⟨_, hpart, ?_⟩
  have hsQ : (2 : ℚ) * (∑ P ∈ D, (F P).card) ≤ 2 * D.card + G.degree x := by
    exact_mod_cast hsum
  have hcQ : (D.card : ℚ) ≤ q := by exact_mod_cast hcard
  linarith

end Erdos583
end
end Source11_Erdos583_VertexErase
/- END Erdos583.VertexErase -/

/- BEGIN Erdos583.HubDelete; source SHA256 6271d81a261bd5bc03b62936f30565918631c0461021025781bf085f5968ba36 -/
section Source12_Erdos583_HubDelete



/-! Delete the actual parity-completion hub from any supplied path partition,
then transfer its original edges back to the original vertex type. -/

noncomputable section

namespace Erdos583

open SimpleGraph
attribute [local instance] Classical.propDecidable

variable {V : Type*} {G : SimpleGraph V}

theorem isolateVertex_walk_avoids (x : V) {a b : V}
    (p : (isolateVertex G x).Walk a b) (hn : ¬ p.Nil) : x ∉ p.support := by
  have aux : ∀ {a b : V} (p : (isolateVertex G x).Walk a b), a ≠ x → x ∉ p.support := by
    intro a b p
    induction p with
    | nil => intro ha; simpa [eq_comm] using ha
    | @cons a b c hab p ih =>
      intro ha
      simp only [Walk.support_cons, List.mem_cons, not_or]
      exact ⟨ha.symm, ih hab.2.2⟩
  cases p with
  | nil => exact (hn (by simp)).elim
  | cons h p => exact aux (.cons h p) h.2.1

variable [Fintype V] [Nonempty V]

def collapseHub (G : SimpleGraph V) :
    isolateVertex (parityCompletion G) none →g G where
  toFun v := v.getD (Classical.choice ‹Nonempty V›)
  map_rel' := by
    intro a b hab
    cases a with
    | none => exact (hab.2.1 rfl).elim
    | some a =>
      cases b with
      | none => exact (hab.2.2 rfl).elim
      | some b => exact hab.1

@[simp] theorem collapseHub_some (G : SimpleGraph V) (v : V) :
    collapseHub G (some v) = v := rfl

theorem collapseHub_injective_away (G : SimpleGraph V) {a b : Option V}
    (ha : a ≠ none) (hb : b ≠ none) (heq : collapseHub G a = collapseHub G b) : a = b := by
  cases a with
  | none => exact (ha rfl).elim
  | some a =>
    cases b with
    | none => exact (hb rfl).elim
    | some b => exact congrArg some heq

theorem collapseHub_edge_left_inverse (G : SimpleGraph V) (e : Sym2 (Option V))
    (he : e ∈ (isolateVertex (parityCompletion G) none).edgeSet) :
    Sym2.map some (Sym2.map (collapseHub G) e) = e := by
  induction e using Sym2.ind with
  | _ a b =>
    cases a with
    | none => exact (he.2.1 rfl).elim
    | some a =>
      cases b with
      | none => exact (he.2.2 rfl).elim
      | some b => rfl

/-- Collapsing an isolated extra vertex preserves every actual nonempty path
and its edge partition. The arbitrary image of the isolate is never visited. -/
theorem collapseHub_path_partition (G : SimpleGraph V) {q : ℕ}
    (hq : HasPathPartition (isolateVertex (parityCompletion G) none) q) :
    HasPathPartition G q := by
  classical
  let H := isolateVertex (parityCompletion G) none
  obtain ⟨D, hpath, hdec, hcard⟩ := hq
  let f : H.Subgraph → G.Subgraph := fun P => P.map (collapseHub G)
  have hfE (P : H.Subgraph) : (f P).edgeSet = Sym2.map (collapseHub G) '' P.edgeSet := by
    simp [f]
  have hfpath (P : H.Subgraph) (hP : IsNonemptyPathSubgraph P) :
      IsNonemptyPathSubgraph (f P) := by
    obtain ⟨a, b, p, hp, hn, rfl⟩ := hP
    have havoid := isolateVertex_walk_avoids none p hn
    have hmap : (p.map (collapseHub G)).IsPath := by
      rw [Walk.isPath_def, Walk.support_map]
      apply hp.support_nodup.map_on
      intro u hu v hv huv
      exact collapseHub_injective_away G (by intro he; subst u; exact havoid hu)
        (by intro he; subst v; exact havoid hv) huv
    refine ⟨collapseHub G a, collapseHub G b, p.map (collapseHub G), hmap, ?_, ?_⟩
    · simpa using hn
    · simp [f]
  refine ⟨D.image f, ?_, ?_, Finset.card_image_le.trans hcard⟩
  · intro P hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    exact hfpath Q (hpath Q hQ)
  · constructor
    · intro P hP Q hQ hne
      obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hQ
      apply Set.disjoint_left.mpr
      intro e heR heS
      change e ∈ (f R).edgeSet at heR
      change e ∈ (f S).edgeSet at heS
      rw [hfE] at heR heS
      obtain ⟨r, hr, hre⟩ := heR
      obtain ⟨s, hs, hse⟩ := heS
      have hrs : r = s := by
        calc
          r = Sym2.map some (Sym2.map (collapseHub G) r) :=
            (collapseHub_edge_left_inverse G r (R.edgeSet_subset hr)).symm
          _ = Sym2.map some (Sym2.map (collapseHub G) s) := congrArg _ (hre.trans hse.symm)
          _ = s := collapseHub_edge_left_inverse G s (S.edgeSet_subset hs)
      have hRS : R ≠ S := fun h => hne (congrArg f h)
      exact Set.disjoint_left.mp (hdec.1 hR hS hRS) hr (hrs.symm ▸ hs)
    · ext e
      simp only [Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨P, hP, heP⟩
        exact P.edgeSet_subset heP
      · intro he
        have hsome : Sym2.map some e ∈ H.edgeSet := by
          induction e using Sym2.ind with
          | _ a b => exact ⟨he, by simp, by simp⟩
        rw [← hdec.2] at hsome
        simp only [Set.mem_iUnion, exists_prop] at hsome
        obtain ⟨P, hP, heP⟩ := hsome
        refine ⟨f P, Finset.mem_image.mpr ⟨P, hP, rfl⟩, ?_⟩
        rw [hfE]
        refine ⟨Sym2.map some e, heP, ?_⟩
        induction e using Sym2.ind with
        | _ a b => rfl

theorem collapseHub_path_bound (G : SimpleGraph V) {b : ℚ}
    (hb : HasPathBound (isolateVertex (parityCompletion G) none) b) :
    HasPathBound G b := by
  obtain ⟨q, hq, hqb⟩ := hasPathBound_iff_exists_partition.mp hb
  exact hasPathBound_iff_exists_partition.mpr ⟨q, collapseHub_path_partition G hq, hqb⟩

/-- The actual hub-deletion inequality, valid for any supplied partition of
the parity completion. Each possible split is paid by two hub-incident edges. -/
theorem parityCompletion_delete_hub (G : SimpleGraph V) {q : ℕ}
    (hq : HasPathPartition (parityCompletion G) q) :
    HasPathBound G ((q : ℚ) + (oddVertices G).card / 2) := by
  have h := erase_vertex_path_bound none hq
  rw [parityCompletion_degree_hub] at h
  exact collapseHub_path_bound G h

end Erdos583
end
end Source12_Erdos583_HubDelete
/- END Erdos583.HubDelete -/

/- BEGIN Erdos583.LeafPaths; source SHA256 625ea4ce4804506dd72573c38c82c2617aa37d7585f4844459d7b8bd6d9ff8fc -/
section Source13_Erdos583_LeafPaths



/-! Removing an actual pendant edge cannot increase the path count. The
proof transports original edges back from the freshly enlarged vertex type. -/

noncomputable section
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

theorem isolate_attachLeaf (G : SimpleGraph V) (a : V) :
    isolateVertex (attachLeaf G a) none = isolateVertex (parityCompletion G) none := by
  ext u v
  cases u <;> cases v <;> simp [isolateVertex, attachLeaf, parityCompletion]

/-- Any supplied path partition of the graph with a fresh leaf yields an
original-edge path partition of G with no increase in its number of pieces. -/
theorem remove_attached_leaf_partition (G : SimpleGraph V) (a : V) {q : ℕ}
    (hq : HasPathPartition (attachLeaf G a) q) : HasPathPartition G q := by
  let : Nonempty V := ⟨a⟩
  have h := erase_vertex_path_bound none hq
  rw [attachLeaf_degree_new, isolate_attachLeaf] at h
  have hG := collapseHub_path_bound G h
  have hpn := hasPathBound_iff_pn_le.mp hG
  have htwo : 2 * pn G ≤ 2 * q + 1 := by
    have hrat : (2 : ℚ) * pn G ≤ 2 * q + 1 := by linarith
    exact_mod_cast hrat
  have hle : pn G ≤ q := by omega
  exact pn_le_iff.mp hle

theorem remove_attached_leaf_bound (G : SimpleGraph V) (a : V) {b : ℚ}
    (hb : HasPathBound (attachLeaf G a) b) : HasPathBound G b := by
  obtain ⟨q, hq, hqb⟩ := hasPathBound_iff_exists_partition.mp hb
  exact hasPathBound_iff_exists_partition.mpr ⟨q, remove_attached_leaf_partition G a hq, hqb⟩

end Erdos583
end
end Source13_Erdos583_LeafPaths
/- END Erdos583.LeafPaths -/

/- BEGIN Erdos583.LovaszGraph; source SHA256 cc0633dd277970608906de64057c387845642fd2928a548b91ee27c4a1b67f5f -/
section Source14_Erdos583_LovaszGraph


/-! Actual graph measures for the mixed path/cycle induction. -/

noncomputable section
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

theorem activeVertices_card_add_isolated (G : SimpleGraph V) :
    (activeVertices G).card + (isolatedVertices G).card = Fintype.card V := by
  have hd : Disjoint (activeVertices G) (isolatedVertices G) := by
    apply Finset.disjoint_left.mpr
    intro v hv hi
    exact (mem_activeVertices G v).mp hv ((mem_isolatedVertices G v).mp hi)
  have hu : activeVertices G ∪ isolatedVertices G = Finset.univ := by
    ext v
    by_cases hv : G.degree v = 0 <;> simp [hv]
  rw [← Finset.card_union_of_disjoint hd, hu, Finset.card_univ]

theorem activeVertices_mono {G H : SimpleGraph V} (hHG : H ≤ G) :
    activeVertices H ⊆ activeVertices G := by
  intro v hv
  apply (mem_activeVertices G v).mpr
  intro hz
  apply (mem_activeVertices H v).mp hv
  apply (H.degree_eq_zero v).mpr
  intro w hw
  exact (G.degree_eq_zero v).mp hz w (hHG hw)

theorem activeVertices_starDeleteEven_bounds (G : SimpleGraph V) (x : V) :
    (activeVertices (starDeleteEven G x)).card ≤ (activeVertices G).card ∧
    (activeVertices G).card ≤ (activeVertices (starDeleteEven G x)).card + 1 := by
  have hi := isolate_count_starDeleteEven_le G x
  have hG := activeVertices_card_add_isolated G
  have hH := activeVertices_card_add_isolated (starDeleteEven G x)
  exact ⟨Finset.card_le_card (activeVertices_mono (starDeleteEven_le G x)), by omega⟩

theorem edgeExcess_starDeleteEven_lt (G : SimpleGraph V) (x : V)
    (hk : 0 < evenNeighborCount G x) :
    edgeExcess (starDeleteEven G x) < edgeExcess G := by
  have hG := activeVertices_card_le_twice_edges G
  have hH := activeVertices_card_le_twice_edges (starDeleteEven G x)
  have hA := (activeVertices_starDeleteEven_bounds G x).2
  have hE := edge_count_starDeleteEven G x
  unfold edgeExcess
  omega

theorem exists_even_star_center (G : SimpleGraph V)
    (he : ∃ v, Even (G.degree v) ∧ G.degree v ≠ 0) :
    ∃ x, 0 < evenNeighborCount G x := by
  obtain ⟨v, hvEven, hvPos⟩ := he
  have hv : ¬G.IsIsolated v := by
    intro hi
    exact hvPos hi.degree_eq_zero
  obtain ⟨x, hvx⟩ := G.exists_adj_iff_not_isIsolated.mpr hv
  apply Exists.intro x
  apply Finset.card_pos.mpr
  exact ⟨v, (mem_evenNeighbors G x v).mpr ⟨hvx.symm, hvEven⟩⟩

theorem edgeExcess_zero_of_degree_le_one (G : SimpleGraph V)
    (hdeg : ∀ v, G.degree v ≤ 1) : edgeExcess G = 0 := by
  have hpoint (v : V) : G.degree v ≤ if v ∈ activeVertices G then 1 else 0 := by
    by_cases hz : G.degree v = 0
    · simp [hz]
    · simp only [if_pos ((mem_activeVertices G v).mpr hz)]
      exact hdeg v
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun v _ => hpoint v)
  rw [G.sum_degrees_eq_twice_card_edges] at hs
  have hcount : (∑ v : V, if v ∈ activeVertices G then 1 else 0) = (activeVertices G).card := by
    simp only [Finset.sum_boole]
    have hset : Finset.univ.filter (fun v => v ∈ activeVertices G) = activeVertices G := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hset]
    norm_num
  rw [hcount] at hs
  exact Nat.sub_eq_zero_of_le hs

theorem exists_degree_ge_three_of_all_odd (G : SimpleGraph V)
    (hodd : ∀ v, G.degree v ≠ 0 → Odd (G.degree v)) (hpos : 0 < edgeExcess G) :
    ∃ x, 3 ≤ G.degree x := by
  by_contra hnone
  push Not at hnone
  have hsmall : ∀ v, G.degree v ≤ 1 := by
    intro v
    by_cases hz : G.degree v = 0
    · omega
    · obtain ⟨k, hk⟩ := hodd v hz
      have hv := hnone v
      omega
  have hz := edgeExcess_zero_of_degree_le_one G hsmall
  omega

end Erdos583
end
end Source14_Erdos583_LovaszGraph
/- END Erdos583.LovaszGraph -/

/- BEGIN Erdos583.LeafStar; source SHA256 db1510b12463deb77b5fdb8aa40602810d96fb147840ef219b46efa60ee9777b -/
section Source15_Erdos583_LeafStar



/-! Actual fresh-leaf/star reductions for the exceptional baseline residues. -/

noncomputable section
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

theorem attachLeaf_evenNeighbors (G : SimpleGraph V) {x a : V}
    (_hxa : G.Adj x a) (ha : Even (G.degree a)) :
    evenNeighbors (attachLeaf G a) (some x) =
      ((evenNeighbors G x).erase a).map someEmbedding := by
  ext v
  cases v with
  | none => simp [mem_evenNeighbors, attachLeaf_degree_new, someEmbedding]
  | some v =>
    have hnot : ¬ Even (G.degree a + 1) :=
      Nat.not_even_iff_odd.mpr (ha.add_odd (by decide))
    by_cases hv : v = a
    · subst v
      simp [someEmbedding, attachLeaf_degree_some, hnot]
    · simp [someEmbedding, attachLeaf_degree_some, hv]

theorem attachLeaf_evenNeighborCount (G : SimpleGraph V) {x a : V}
    (hxa : G.Adj x a) (ha : Even (G.degree a)) :
    evenNeighborCount (attachLeaf G a) (some x) + 1 = evenNeighborCount G x := by
  have hmem := (mem_evenNeighbors G x a).mpr ⟨hxa,ha⟩
  unfold evenNeighborCount
  rw [attachLeaf_evenNeighbors G hxa ha, Finset.card_map]
  exact Finset.card_erase_add_one hmem

theorem attachLeaf_star_retained (G : SimpleGraph V) {x a : V}
    (hxa : G.Adj x a) (ha : Even (G.degree a)) :
    (starDeleteEven (attachLeaf G a) (some x)).Adj (some x) (some a) := by
  have hnot : ¬ Even ((attachLeaf G a).degree (some a)) := by
    rw [attachLeaf_degree_some]
    simpa using Nat.not_even_iff_odd.mpr (ha.add_odd (by decide))
  exact ⟨hxa,fun h => hnot h.2,fun h => hxa.ne (Option.some.inj h.1).symm⟩

theorem attachLeaf_star_active_count (G : SimpleGraph V) {x a : V}
    (hxa : G.Adj x a) (ha : Even (G.degree a)) :
    (activeVertices (starDeleteEven (attachLeaf G a) (some x))).card =
      (activeVertices G).card + 1 := by
  have hx := hxa.degree_pos_left
  have hxL : (attachLeaf G a).degree (some x) ≠ 0 := by
    rw [attachLeaf_degree_some, if_neg hxa.ne]
    omega
  have hxJ := (attachLeaf_star_retained G hxa ha).degree_pos_left
  have hi := isolate_count_starDeleteEven (attachLeaf G a) (some x)
  simp only [if_neg hxL, if_neg (Nat.ne_of_gt hxJ), Nat.add_zero] at hi
  have hL := activeVertices_card_add_isolated (attachLeaf G a)
  have hJ := activeVertices_card_add_isolated (starDeleteEven (attachLeaf G a) (some x))
  have hA := attachLeaf_active_count G a (Nat.ne_of_gt hxa.degree_pos_right)
  omega

theorem attachLeaf_star_edgeExcess (G : SimpleGraph V) {x a : V}
    (hxa : G.Adj x a) (ha : Even (G.degree a)) :
    edgeExcess (starDeleteEven (attachLeaf G a) (some x)) +
      2 * evenNeighborCount G x = edgeExcess G + 3 := by
  have he := edge_count_starDeleteEven (attachLeaf G a) (some x)
  have hk := attachLeaf_evenNeighborCount G hxa ha
  have hm := attachLeaf_edge_count G a
  have hac := attachLeaf_star_active_count G hxa ha
  have hG := activeVertices_card_le_twice_edges G
  have hJ := activeVertices_card_le_twice_edges (starDeleteEven (attachLeaf G a) (some x))
  unfold edgeExcess
  omega

theorem attachLeaf_star_edgeExcess_lt (G : SimpleGraph V) {x a : V}
    (hxa : G.Adj x a) (ha : Even (G.degree a))
    (hk : 2 ≤ evenNeighborCount G x) :
    edgeExcess (starDeleteEven (attachLeaf G a) (some x)) < edgeExcess G := by
  have := attachLeaf_star_edgeExcess G hxa ha
  omega

theorem phi_attachLeaf_star (G : SimpleGraph V) {x a : V}
    (hxa : G.Adj x a) (ha : Even (G.degree a)) (hx : Even (G.degree x))
    (hk : Even (evenNeighborCount G x)) :
    phi G - phi (starDeleteEven (attachLeaf G a) (some x)) =
      ((evenNeighborCount G x : ℚ) - 2) / 6 := by
  have hcnt := attachLeaf_evenNeighborCount G hxa ha
  have hxL : (attachLeaf G a).degree (some x) = G.degree x := by
    rw [attachLeaf_degree_some, if_neg hxa.ne, Nat.add_zero]
  have hkodd : Odd (evenNeighborCount (attachLeaf G a) (some x)) := by
    obtain ⟨j,hj⟩ := hk
    exact ⟨j-1, by omega⟩
  have hle := evenNeighborCount_le_degree (attachLeaf G a) (some x)
  have hxJ : Odd ((starDeleteEven (attachLeaf G a) (some x)).degree (some x)) := by
    rw [degree_starDeleteEven_center, hxL]
    exact Nat.Even.sub_odd (by omega) hx hkodd
  have hwJ : parityWeight ((starDeleteEven (attachLeaf G a) (some x)).degree (some x)) = 1/2 := by
    simp [parityWeight, hxJ, Nat.not_even_iff_odd.mpr hxJ]
  have hwL : parityWeight ((attachLeaf G a).degree (some x)) = 2/3 := by
    rw [hxL]
    exact parityWeight_even_nonzero hx (Nat.ne_of_gt hxa.degree_pos_left)
  have hp := phi_starDeleteEven_exact (attachLeaf G a) (some x)
  rw [hwL,hwJ,phi_attachLeaf_even G a ha (Nat.ne_of_gt hxa.degree_pos_right)] at hp
  have hrat : (evenNeighborCount (attachLeaf G a) (some x) : ℚ) + 1 =
      evenNeighborCount G x := by exact_mod_cast hcnt
  linarith

/-- Complete actual exceptional-star certificate. Removing the fresh leaf
after any supplied reconstruction cannot increase its path budget. -/
theorem attachLeaf_star_certificate (G : SimpleGraph V) {x a : V}
    (hxa : G.Adj x a) (ha : Even (G.degree a)) (hx : Even (G.degree x))
    (hk : Even (evenNeighborCount G x)) (hktwo : 2 ≤ evenNeighborCount G x) :
    let F := attachLeaf G a
    let J := starDeleteEven F (some x)
    evenNeighborCount F (some x) + 1 = evenNeighborCount G x ∧
    J.Adj (some x) (some a) ∧
    (activeVertices J).card = (activeVertices G).card + 1 ∧
    edgeExcess J + 2 * evenNeighborCount G x = edgeExcess G + 3 ∧
    edgeExcess J < edgeExcess G ∧
    phi G - phi J = ((evenNeighborCount G x : ℚ) - 2) / 6 ∧
    (∀ v, F.Adj (some x) v → Odd (J.degree v)) ∧
    (∀ q, HasPathPartition F q → HasPathPartition G q) := by
  exact ⟨attachLeaf_evenNeighborCount G hxa ha,
    attachLeaf_star_retained G hxa ha, attachLeaf_star_active_count G hxa ha,
    attachLeaf_star_edgeExcess G hxa ha, attachLeaf_star_edgeExcess_lt G hxa ha hktwo,
    phi_attachLeaf_star G hxa ha hx hk,
    original_neighbor_odd_after_starDeleteEven _ _,
    fun _ hq => remove_attached_leaf_partition G a hq⟩

end Erdos583
end
end Source15_Erdos583_LeafStar
/- END Erdos583.LeafStar -/

/- BEGIN Erdos583.CycleBouquet; source SHA256 3a7fb1e59acecef84ae62dd19def77ad106bfe4c22237bbcf974c4e6254dba38 -/
section Source16_Erdos583_CycleBouquet



/-!
# Cycle repair primitives for Erdős 583

This section proves small repair steps that preserve original edges.
-/

namespace Erdos583

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Moving an initial segment of a simple cycle to the end preserves simplicity. -/
theorem cycle_append_comm {u v : V} (p : G.Walk u v) (q : G.Walk v u) :
    (p.append q).IsCycle ↔ (q.append p).IsCycle := by
  simp only [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def,
    SimpleGraph.Walk.edges_append, ne_eq, SimpleGraph.Walk.eq_nil_iff_nil,
    SimpleGraph.Walk.nil_append_iff, SimpleGraph.Walk.tail_support_append]
  rw [List.nodup_append_comm (l₁ := p.edges),
    List.nodup_append_comm (l₁ := p.support.tail)]
  tauto

/-- Select an occurrence of an original edge and retain its two walk segments. -/
theorem walk_edge_decomposition {u v : V} (p : G.Walk u v) {e : Sym2 V}
    (he : e ∈ p.edgeSet) :
    ∃ (a b : V) (h : G.Adj a b) (l : G.Walk u a) (r : G.Walk b v),
      p = l.append (SimpleGraph.Walk.cons h r) ∧ e = s(a, b) := by
  induction p with
  | nil => simp at he
  | @cons u w v h p ih =>
    simp only [SimpleGraph.Walk.edgeSet_cons, Set.mem_insert_iff] at he
    rcases he with he | he
    · exact ⟨u, w, h, .nil, p, rfl, he⟩
    · obtain ⟨a, b, hab, l, r, hl, he⟩ := ih he
      exact ⟨a, b, hab, .cons h l, r, by simp [hl], he⟩

/-- Cutting any chosen original edge of a simple cycle leaves a nonempty simple
path and gives an exact disjoint-edge description of the cycle. -/
theorem cycle_cut_edge {v : V} (c : G.Walk v v) (hc : c.IsCycle)
    {e : Sym2 V} (he : e ∈ c.edgeSet) :
    ∃ (a b : V) (p : G.Walk b a), G.Adj a b ∧ p.IsPath ∧ ¬p.Nil ∧
      e = s(a, b) ∧ e ∉ p.edgeSet ∧ insert e p.edgeSet = c.edgeSet := by
  obtain ⟨a, b, h, l, r, hdecomp, heq⟩ := walk_edge_decomposition c he
  have hrot : (SimpleGraph.Walk.cons h (r.append l)).IsCycle := by
    have hcy : (l.append (SimpleGraph.Walk.cons h r)).IsCycle := hdecomp ▸ hc
    simpa using (cycle_append_comm l (SimpleGraph.Walk.cons h r)).mp hcy
  have hparts := (SimpleGraph.Walk.cons_isCycle_iff (r.append l) h).mp hrot
  refine ⟨a, b, r.append l, h, hparts.1,
    SimpleGraph.Walk.not_nil_of_isCycle_cons hrot, heq, ?_, ?_⟩
  · simpa [heq] using hparts.2
  · rw [hdecomp, heq]
    simp only [SimpleGraph.Walk.edgeSet_append, SimpleGraph.Walk.edgeSet_cons]
    ext f
    simp only [Set.mem_insert_iff, Set.mem_union]
    tauto

/-- Cutting a chosen oriented edge yields a path in the opposite orientation. -/
theorem cycle_cut_oriented_edge {v a b : V} (c : G.Walk v v) (hc : c.IsCycle)
    (he : s(a, b) ∈ c.edgeSet) :
    ∃ p : G.Walk b a, p.IsPath ∧ ¬p.Nil ∧ s(a, b) ∉ p.edgeSet ∧
      insert s(a, b) p.edgeSet = c.edgeSet := by
  obtain ⟨x, y, p, _, hp, hnil, heq, hnot, hcut⟩ := cycle_cut_edge c hc he
  rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨p, hp, hnil, hnot, hcut⟩
  · exact ⟨p.reverse, hp.reverse, by simpa using hnil,
      by simpa using hnot, by simpa using hcut⟩

/-- Deleting edges from a nonempty walk cannot introduce vertices. -/
theorem walk_support_subset_of_edgeSet_subset {a b u v : V}
    (p : G.Walk a b) (q : G.Walk u v) (hp : ¬p.Nil)
    (hE : p.edgeSet ⊆ q.edgeSet) : p.support ⊆ q.support := by
  intro x hx
  obtain ⟨e, he, hxe⟩ :=
    (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hp).mp hx
  exact q.mem_support_of_mem_edges (hE he) hxe

/-- A simple cycle has two distinct neighbors at its root. -/
theorem cycle_has_two_neighbors {v : V} (c : G.Walk v v) (hc : c.IsCycle) :
    ∃ a b, a ≠ b ∧ G.Adj v a ∧ G.Adj v b ∧
      s(v, a) ∈ c.edgeSet ∧ s(v, b) ∈ c.edgeSet := by
  cases c with
  | nil => exact (SimpleGraph.Walk.not_isCycle_nil hc).elim
  | @cons v a v h p =>
    have hparts := (SimpleGraph.Walk.cons_isCycle_iff p h).mp hc
    obtain ⟨b, hb, q, hq⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne h.ne p.reverse
    have he : s(v, b) ∈ p.edgeSet := by
      rw [← SimpleGraph.Walk.edgeSet_reverse p, hq]
      simp
    have hab : a ≠ b := by
      intro hab
      subst b
      exact hparts.2 he
    exact ⟨a, b, hab, h, hb, by simp, by simp [he]⟩

/-- A simple cycle has an incident edge avoiding any one prescribed other vertex. -/
theorem cycle_neighbor_avoiding {v : V} (c : G.Walk v v) (hc : c.IsCycle)
    (x z : V) (hx : x ∈ c.support) :
    ∃ y, y ≠ z ∧ G.Adj x y ∧ s(x, y) ∈ c.edgeSet := by
  classical
  have hrot : (c.rotate x hx).IsCycle := hc.rotate hx
  obtain ⟨a, b, hab, ha, hb, hea, heb⟩ := cycle_has_two_neighbors (c.rotate x hx) hrot
  have hE : (c.rotate x hx).edgeSet = c.edgeSet := by
    ext e
    exact (c.rotate_edges x hx).perm.mem_iff
  rw [hE] at hea heb
  by_cases haz : a = z
  · exact ⟨b, fun hbz => hab (haz.trans hbz.symm), hb, heb⟩
  · exact ⟨a, haz, ha, hea⟩

/-- An indexed finite family of paths gives a partition when its original edge
sets are pairwise disjoint and cover the ambient graph. -/
theorem hasPathPartition_of_path_family {I : Type*} [Fintype I]
    (H : I → G.Subgraph) (hp : ∀ i, IsNonemptyPathSubgraph (H i))
    (hd : Pairwise (fun i j => Disjoint (H i).edgeSet (H j).edgeSet))
    (hc : (⋃ i, (H i).edgeSet) = G.edgeSet) :
    HasPathPartition G (Fintype.card I) := by
  classical
  refine ⟨Finset.univ.image H, ?_, ?_, ?_⟩
  · intro J hJ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hJ
    exact hp i
  · constructor
    · intro J hJ K hK hne
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hJ
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hK
      exact hd (fun hij => hne (congrArg H hij))
    · ext e
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨J, _, he⟩
        exact J.edgeSet_subset he
      · intro he
        rw [← hc] at he
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
        exact ⟨H i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hi⟩
  · exact Finset.card_image_le.trans_eq Finset.card_univ

/-- Adding one further edge-disjoint path to an indexed path family. -/
theorem hasPathPartition_of_path_family_and_path {I : Type*} [Fintype I]
    (H : I → G.Subgraph) (R : G.Subgraph)
    (hp : ∀ i, IsNonemptyPathSubgraph (H i)) (hr : IsNonemptyPathSubgraph R)
    (hd : Pairwise (fun i j => Disjoint (H i).edgeSet (H j).edgeSet))
    (hdr : ∀ i, Disjoint (H i).edgeSet R.edgeSet)
    (hc : (⋃ i, (H i).edgeSet) ∪ R.edgeSet = G.edgeSet) :
    HasPathPartition G (Fintype.card I + 1) := by
  classical
  let K : Option I → G.Subgraph := fun i => i.elim R H
  have hpK : ∀ i, IsNonemptyPathSubgraph (K i) := by
    intro i
    cases i with
    | none => exact hr
    | some i => exact hp i
  have hdK : Pairwise (fun i j => Disjoint (K i).edgeSet (K j).edgeSet) := by
    intro i j hne
    cases i with
    | none =>
      cases j with
      | none => exact (hne rfl).elim
      | some j => exact (hdr j).symm
    | some i =>
      cases j with
      | none => exact hdr i
      | some j => exact hd (fun hij => hne (congrArg some hij))
  have hcK : (⋃ i, (K i).edgeSet) = G.edgeSet := by
    rw [← hc]
    ext e
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      cases i with
      | none => exact Or.inr hi
      | some i => exact Or.inl ⟨i, hi⟩
    · rintro (⟨i, hi⟩ | hi)
      · exact ⟨some i, hi⟩
      · exact ⟨none, hi⟩
  simpa using hasPathPartition_of_path_family K hpK hdK hcK

/-- If one edge from every cycle forms a nonempty simple path, cutting those
edges gives one additional simple path beyond the number of cycles. -/
theorem hasPathPartition_of_cycle_cuts_form_path {I : Type*} [Fintype I]
    (a b : I → V) (h : ∀ i, G.Adj (a i) (b i))
    (p : ∀ i, G.Walk (b i) (a i))
    (hp : ∀ i, (SimpleGraph.Walk.cons (h i) (p i)).IsCycle)
    (hd : Pairwise (fun i j => Disjoint
      (SimpleGraph.Walk.cons (h i) (p i)).edgeSet
      (SimpleGraph.Walk.cons (h j) (p j)).edgeSet))
    {u v : V} (r : G.Walk u v) (hr : r.IsPath) (hrnil : ¬r.Nil)
    (hredges : r.edgeSet = {e | ∃ i, e = s(a i, b i)})
    (hc : (⋃ i, (SimpleGraph.Walk.cons (h i) (p i)).edgeSet) = G.edgeSet) :
    HasPathPartition G (Fintype.card I + 1) := by
  classical
  have hparts i := (SimpleGraph.Walk.cons_isCycle_iff (p i) (h i)).mp (hp i)
  apply hasPathPartition_of_path_family_and_path (fun i => (p i).toSubgraph) r.toSubgraph
  · intro i
    exact ⟨b i, a i, p i, (hparts i).1,
      SimpleGraph.Walk.not_nil_of_isCycle_cons (hp i), rfl⟩
  · exact ⟨u, v, r, hr, hrnil, rfl⟩
  · intro i j hij
    rw [SimpleGraph.Walk.edgeSet_toSubgraph, SimpleGraph.Walk.edgeSet_toSubgraph]
    apply Set.disjoint_left.mpr
    intro e he he'
    apply Set.disjoint_left.mp (hd hij) (show e ∈
      (SimpleGraph.Walk.cons (h i) (p i)).edgeSet by simp [he])
    simp [he']
  · intro i
    rw [SimpleGraph.Walk.edgeSet_toSubgraph, SimpleGraph.Walk.edgeSet_toSubgraph]
    apply Set.disjoint_left.mpr
    intro e he her
    rw [hredges] at her
    obtain ⟨j, rfl⟩ := her
    by_cases hij : i = j
    · subst j
      exact (hparts i).2 he
    · apply Set.disjoint_left.mp (hd hij) (show s(a j, b j) ∈
        (SimpleGraph.Walk.cons (h i) (p i)).edgeSet by simp [he])
      simp
  · simp only [SimpleGraph.Walk.edgeSet_toSubgraph]
    rw [← hc]
    ext e
    simp only [Set.mem_union, Set.mem_iUnion, SimpleGraph.Walk.edgeSet_cons,
      Set.mem_insert_iff]
    rw [hredges]
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
      · exact ⟨i, Or.inr hi⟩
      · exact ⟨i, Or.inl hi⟩
    · rintro ⟨i, hi | hi⟩
      · exact Or.inr ⟨i, hi⟩
      · exact Or.inl ⟨i, hi⟩

/-- Two disjoint nonempty path subgraphs covering the graph give a two-path partition. -/
theorem hasPathPartition_of_rainbow_cycle_transversal {I : Type*} [Fintype I]
    (root : I → V) (c : ∀ i, G.Walk (root i) (root i))
    (hc : ∀ i, (c i).IsCycle)
    (hd : Pairwise (fun i j => Disjoint (c i).edgeSet (c j).edgeSet))
    (e : I → Sym2 V) (he : ∀ i, e i ∈ (c i).edgeSet)
    {u v : V} (r : G.Walk u v) (hr : r.IsPath) (hrnil : ¬r.Nil)
    (hredges : r.edgeSet = Set.range e)
    (hcover : (⋃ i, (c i).edgeSet) = G.edgeSet) :
    HasPathPartition G (Fintype.card I + 1) := by
  classical
  choose a b p hab hp hnil heq hne hcut using
    fun i => cycle_cut_edge (c i) (hc i) (he i)
  have hcy i : (SimpleGraph.Walk.cons (hab i) (p i)).IsCycle := by
    apply (SimpleGraph.Walk.cons_isCycle_iff (p i) (hab i)).mpr
    exact ⟨hp i, by simpa [← heq i] using hne i⟩
  have hCE i : (SimpleGraph.Walk.cons (hab i) (p i)).edgeSet = (c i).edgeSet := by
    simpa [SimpleGraph.Walk.edgeSet_cons, ← heq i] using hcut i
  apply hasPathPartition_of_cycle_cuts_form_path a b hab p hcy
  · intro i j hij
    simpa only [hCE] using hd hij
  · exact hr
  · exact hrnil
  · rw [hredges]
    ext f
    simp only [Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, hi.symm.trans (heq i)⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, (heq i).trans hi.symm⟩
  · simpa only [hCE] using hcover

/-- Two disjoint nonempty path subgraphs covering the graph give a two-path partition. -/
theorem hasPathPartition_two_of_subgraphs
    (H₁ H₂ : G.Subgraph)
    (h₁ : IsNonemptyPathSubgraph H₁) (h₂ : IsNonemptyPathSubgraph H₂)
    (hd : Disjoint H₁.edgeSet H₂.edgeSet)
    (hc : H₁.edgeSet ∪ H₂.edgeSet = G.edgeSet) :
    HasPathPartition G 2 := by
  classical
  refine ⟨{H₁, H₂}, ?_, ?_, ?_⟩
  · intro H hH
    simp only [Finset.mem_insert, Finset.mem_singleton] at hH
    rcases hH with rfl | rfl
    · exact h₁
    · exact h₂
  · constructor
    · intro H hH J hJ hne
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hH hJ
      rcases hH with rfl | rfl <;> rcases hJ with rfl | rfl
      · exact (hne rfl).elim
      · exact hd
      · exact hd.symm
      · exact (hne rfl).elim
    · simpa using hc
  · by_cases heq : H₁ = H₂
    · subst H₂
      simp
    · simp [heq]

/-- Splitting a simple cycle at its first edge partitions all its edges into two
nonempty simple paths. Extra isolated vertices in the ambient graph are allowed. -/
theorem hasPathPartition_two_of_cycle {v : V} (p : G.Walk v v)
    (hp : p.IsCycle) (hcover : p.edgeSet = G.edgeSet) :
    HasPathPartition G 2 := by
  classical
  cases p with
  | nil => exact (SimpleGraph.Walk.not_isCycle_nil hp).elim
  | @cons v w v h p =>
    have hparts := (SimpleGraph.Walk.cons_isCycle_iff p h).mp hp
    apply hasPathPartition_two_of_subgraphs h.toWalk.toSubgraph p.toSubgraph
    · exact ⟨v, w, h.toWalk, h.isPath_toWalk,
        SimpleGraph.Walk.not_nil_of_ne h.ne, rfl⟩
    · exact ⟨w, v, p, hparts.1, SimpleGraph.Walk.not_nil_of_isCycle_cons hp, rfl⟩
    · rw [SimpleGraph.Walk.edgeSet_toSubgraph, SimpleGraph.Walk.edgeSet_toSubgraph]
      apply Set.disjoint_left.mpr
      intro e he hpedge
      have heq : e = s(v, w) := by simpa using he
      subst e
      exact hparts.2 hpedge
    · simpa using hcover

/-- Three disjoint nonempty path subgraphs covering the graph give a three-path partition. -/
theorem hasPathPartition_three_of_subgraphs
    (H₁ H₂ H₃ : G.Subgraph)
    (h₁ : IsNonemptyPathSubgraph H₁) (h₂ : IsNonemptyPathSubgraph H₂)
    (h₃ : IsNonemptyPathSubgraph H₃)
    (hd₁₂ : Disjoint H₁.edgeSet H₂.edgeSet)
    (hd₁₃ : Disjoint H₁.edgeSet H₃.edgeSet)
    (hd₂₃ : Disjoint H₂.edgeSet H₃.edgeSet)
    (hc : H₁.edgeSet ∪ (H₂.edgeSet ∪ H₃.edgeSet) = G.edgeSet) :
    HasPathPartition G 3 := by
  classical
  refine ⟨{H₁, H₂, H₃}, ?_, ?_, ?_⟩
  · intro H hH
    simp only [Finset.mem_insert, Finset.mem_singleton] at hH
    rcases hH with rfl | rfl | rfl
    · exact h₁
    · exact h₂
    · exact h₃
  · constructor
    · intro H hH J hJ hne
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hH hJ
      rcases hH with rfl | rfl | rfl <;> rcases hJ with rfl | rfl | rfl
      all_goals
        first
        | exact (hne rfl).elim
        | exact hd₁₂
        | exact hd₁₂.symm
        | exact hd₁₃
        | exact hd₁₃.symm
        | exact hd₂₃
        | exact hd₂₃.symm
    · simpa using hc
  · have h₂₃ : ({H₂, H₃} : Finset G.Subgraph).card ≤ 2 := by
      by_cases heq : H₂ = H₃
      · subst H₃
        simp
      · simp [heq]
    exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right h₂₃ 1)

/-- Two edge-disjoint simple cycles through the same root admit three simple paths.
The cycles may have arbitrary additional common vertices. -/
theorem hasPathPartition_three_of_two_cycles {v : V}
    (p q : G.Walk v v) (hp : p.IsCycle) (hq : q.IsCycle)
    (hd : Disjoint p.edgeSet q.edgeSet)
    (hcover : p.edgeSet ∪ q.edgeSet = G.edgeSet) :
    HasPathPartition G 3 := by
  classical
  cases p with
  | nil => exact (SimpleGraph.Walk.not_isCycle_nil hp).elim
  | @cons v a v ha p =>
    cases q with
    | nil => exact (SimpleGraph.Walk.not_isCycle_nil hq).elim
    | @cons v b v hb q =>
      have hp' := (SimpleGraph.Walk.cons_isCycle_iff p ha).mp hp
      have hq' := (SimpleGraph.Walk.cons_isCycle_iff q hb).mp hq
      have hab : a ≠ b := by
        intro hab
        subst b
        have he : s(v, a) ∈ (SimpleGraph.Walk.cons ha p).edgeSet := by simp
        exact Set.disjoint_left.mp hd he (by simp)
      let r : G.Walk a b := .cons ha.symm hb.toWalk
      have hr : r.IsPath := by
        apply SimpleGraph.Walk.IsPath.cons hb.isPath_toWalk
        simp [ha.ne.symm, hab]
      have hpa : s(v, a) ∉ p.edgeSet := hp'.2
      have hqb : s(v, b) ∉ q.edgeSet := hq'.2
      have hpb : s(v, b) ∉ p.edgeSet := by
        intro h
        have he : s(v, b) ∈ (SimpleGraph.Walk.cons ha p).edgeSet := by simp [h]
        exact Set.disjoint_left.mp hd he (by simp)
      have hqa : s(v, a) ∉ q.edgeSet := by
        intro h
        have he : s(v, a) ∈ (SimpleGraph.Walk.cons ha p).edgeSet := by simp
        exact Set.disjoint_left.mp hd he (by simp [h])
      apply hasPathPartition_three_of_subgraphs p.toSubgraph q.toSubgraph r.toSubgraph
      · exact ⟨a, v, p, hp'.1, SimpleGraph.Walk.not_nil_of_isCycle_cons hp, rfl⟩
      · exact ⟨b, v, q, hq'.1, SimpleGraph.Walk.not_nil_of_isCycle_cons hq, rfl⟩
      · exact ⟨a, b, r, hr, SimpleGraph.Walk.not_nil_of_ne hab, rfl⟩
      · rw [SimpleGraph.Walk.edgeSet_toSubgraph, SimpleGraph.Walk.edgeSet_toSubgraph]
        apply Set.disjoint_left.mpr
        intro e he he'
        have he₁ : e ∈ (SimpleGraph.Walk.cons ha p).edgeSet := by simp [he]
        exact Set.disjoint_left.mp hd he₁ (by simp [he'])
      · rw [SimpleGraph.Walk.edgeSet_toSubgraph, SimpleGraph.Walk.edgeSet_toSubgraph]
        apply Set.disjoint_left.mpr
        intro e he he'
        have he' : e = s(v, a) ∨ e = s(v, b) := by simpa [r, Sym2.eq_swap] using he'
        rcases he' with rfl | rfl
        · exact hpa he
        · exact hpb he
      · rw [SimpleGraph.Walk.edgeSet_toSubgraph, SimpleGraph.Walk.edgeSet_toSubgraph]
        apply Set.disjoint_left.mpr
        intro e he he'
        have he' : e = s(v, a) ∨ e = s(v, b) := by simpa [r, Sym2.eq_swap] using he'
        rcases he' with rfl | rfl
        · exact hqa he
        · exact hqb he
      · rw [SimpleGraph.Walk.edgeSet_toSubgraph, SimpleGraph.Walk.edgeSet_toSubgraph,
          SimpleGraph.Walk.edgeSet_toSubgraph]
        rw [← hcover]
        ext e
        simp [r, Sym2.eq_swap]
        tauto

/-- A walk starting in a set and visiting its complement has an original edge
whose first vertex is in the set and whose second vertex is outside it. -/
theorem walk_first_exit {u w : V} (p : G.Walk u w) (S : Set V)
    (hu : u ∈ S) (hout : ∃ z ∈ p.support, z ∉ S) :
    ∃ a b, G.Adj a b ∧ s(a, b) ∈ p.edgeSet ∧ a ∈ S ∧ b ∉ S := by
  classical
  induction p with
  | @nil u =>
    obtain ⟨z, hz, hzs⟩ := hout
    have hzu : z = u := by simpa using hz
    subst z
    exact (hzs hu).elim
  | @cons u v w h p ih =>
    by_cases hv : v ∈ S
    · have hout' : ∃ z ∈ p.support, z ∉ S := by
        obtain ⟨z, hz, hzs⟩ := hout
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact (hzs hu).elim
        · exact ⟨z, hz, hzs⟩
      obtain ⟨a, b, hab, he, ha, hb⟩ := ih hv hout'
      exact ⟨a, b, hab, by simp [he], ha, hb⟩
    · exact ⟨u, v, h, by simp, hu, hv⟩

/-- The unequal-support reduction for a family of common-root closed walks.
The selected edge starts at a vertex common to every walk and ends outside one
member's support. No assumption about how the other vertices overlap is needed. -/
theorem common_root_family_exit {I : Type*} {v : V}
    (p : I → G.Walk v v)
    (hout : ∃ i j z, z ∈ (p i).support ∧ z ∉ (p j).support) :
    ∃ i j a b, G.Adj a b ∧ s(a, b) ∈ (p i).edgeSet ∧
      (∀ k, a ∈ (p k).support) ∧ b ∉ (p j).support := by
  classical
  obtain ⟨i, j, z, hzi, hzj⟩ := hout
  let S : Set V := {x | ∀ k, x ∈ (p k).support}
  have hv : v ∈ S := fun k => (p k).start_mem_support
  have hz : z ∉ S := fun h => hzj (h j)
  obtain ⟨a, b, hab, he, ha, hb⟩ := walk_first_exit (p i) S hv ⟨z, hzi, hz⟩
  have hb' : ¬ ∀ k, b ∈ (p k).support := hb
  push Not at hb'
  obtain ⟨j', hj'⟩ := hb'
  exact ⟨i, j', a, b, hab, he, ha, hj'⟩

/-- Three cycles with the same vertex support have a simple three-edge rainbow
path. The disjointness of the second and third cycles prevents the final edge
from returning to the preceding vertex. -/
theorem three_equal_support_cycles_rainbow {v : V}
    (p q c : G.Walk v v) (hp : p.IsCycle) (hq : q.IsCycle) (hc : c.IsCycle)
    (hpq : ∀ x, x ∈ p.support ↔ x ∈ q.support)
    (hqc : ∀ x, x ∈ q.support ↔ x ∈ c.support)
    (hd : Disjoint q.edgeSet c.edgeSet) :
    ∃ (a b d : V) (h₁ : G.Adj v a) (h₂ : G.Adj a b) (h₃ : G.Adj b d),
      (SimpleGraph.Walk.cons h₁ (SimpleGraph.Walk.cons h₂ h₃.toWalk)).IsPath ∧
      s(v, a) ∈ p.edgeSet ∧ s(a, b) ∈ q.edgeSet ∧ s(b, d) ∈ c.edgeSet := by
  obtain ⟨a, _, h₁, he₁⟩ := cycle_neighbor_avoiding p hp v v p.start_mem_support
  have haq : a ∈ q.support := (hpq a).mp (p.snd_mem_support_of_mem_edges he₁)
  obtain ⟨b, hbv, h₂, he₂⟩ := cycle_neighbor_avoiding q hq a v haq
  have hbc : b ∈ c.support := (hqc b).mp (q.snd_mem_support_of_mem_edges he₂)
  obtain ⟨d, hdv, h₃, he₃⟩ := cycle_neighbor_avoiding c hc b v hbc
  have hda : d ≠ a := by
    intro hda
    subst d
    apply Set.disjoint_left.mp hd he₂
    simpa only [Sym2.eq_swap] using he₃
  refine ⟨a, b, d, h₁, h₂, h₃, ?_, he₁, he₂, he₃⟩
  apply SimpleGraph.Walk.IsPath.cons
  · apply SimpleGraph.Walk.IsPath.cons h₃.isPath_toWalk
    simp [h₂.ne, hda.symm]
  · simp [h₁.ne, hbv.symm, hdv.symm]

/-- Equal-support triples of edge-disjoint cycles admit four simple paths. -/
theorem hasPathPartition_four_of_three_equal_support_cycles {v : V}
    (c : Fin 3 → G.Walk v v) (hc : ∀ i, (c i).IsCycle)
    (hs : ∀ i x, x ∈ (c 0).support ↔ x ∈ (c i).support)
    (hd : Pairwise (fun i j => Disjoint (c i).edgeSet (c j).edgeSet))
    (hcover : (⋃ i, (c i).edgeSet) = G.edgeSet) :
    HasPathPartition G 4 := by
  classical
  obtain ⟨a, b, d, h₁, h₂, h₃, hr, he₁, he₂, he₃⟩ :=
    three_equal_support_cycles_rainbow (c 0) (c 1) (c 2)
      (hc 0) (hc 1) (hc 2) (hs 1)
      (fun x => (hs 1 x).symm.trans (hs 2 x)) (hd (by decide))
  let e : Fin 3 → Sym2 V := ![s(v, a), s(a, b), s(b, d)]
  let r : G.Walk v d := .cons h₁ (.cons h₂ h₃.toWalk)
  have he : ∀ i, e i ∈ (c i).edgeSet := by
    intro i
    fin_cases i
    · exact he₁
    · exact he₂
    · exact he₃
  have hrnil : ¬r.Nil := by simp [r]
  have hredges : r.edgeSet = Set.range e := by
    ext f
    simp [r, e]
    tauto
  have hresult := hasPathPartition_of_rainbow_cycle_transversal
    (fun _ : Fin 3 => v) c hc hd e he r hr hrnil hredges hcover
  simpa using hresult

set_option maxHeartbeats 800000 in
/-- The unequal-support repair for three cycles, expressed at the selected
common root: the first removed edge can extend the second cycle's tail. -/
theorem hasPathPartition_four_of_three_cycle_escape {v a b d : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hd : G.Adj v d)
    (p : G.Walk a v) (q : G.Walk b v) (r : G.Walk d v)
    (hp : (SimpleGraph.Walk.cons ha p).IsCycle)
    (hq : (SimpleGraph.Walk.cons hb q).IsCycle)
    (hr : (SimpleGraph.Walk.cons hd r).IsCycle)
    (hAB : Disjoint (SimpleGraph.Walk.cons ha p).edgeSet
      (SimpleGraph.Walk.cons hb q).edgeSet)
    (hAC : Disjoint (SimpleGraph.Walk.cons ha p).edgeSet
      (SimpleGraph.Walk.cons hd r).edgeSet)
    (hBC : Disjoint (SimpleGraph.Walk.cons hb q).edgeSet
      (SimpleGraph.Walk.cons hd r).edgeSet)
    (hescape : a ∉ q.support)
    (hcover : (SimpleGraph.Walk.cons ha p).edgeSet ∪
      ((SimpleGraph.Walk.cons hb q).edgeSet ∪
      (SimpleGraph.Walk.cons hd r).edgeSet) = G.edgeSet) :
    HasPathPartition G 4 := by
  classical
  have hp' := (SimpleGraph.Walk.cons_isCycle_iff p ha).mp hp
  have hq' := (SimpleGraph.Walk.cons_isCycle_iff q hb).mp hq
  have hr' := (SimpleGraph.Walk.cons_isCycle_iff r hd).mp hr
  have hba : b ≠ a := by
    intro hba
    subst b
    exact hescape q.start_mem_support
  have hda : d ≠ a := by
    intro hda
    subst d
    have he : s(v, a) ∈ (SimpleGraph.Walk.cons ha p).edgeSet := by simp
    exact Set.disjoint_left.mp hAC he (by simp)
  have hbd : b ≠ d := by
    intro hbd
    subst d
    have he : s(v, b) ∈ (SimpleGraph.Walk.cons hb q).edgeSet := by simp
    exact Set.disjoint_left.mp hBC he (by simp)
  let t : G.Walk b d := .cons hb.symm hd.toWalk
  have ht : t.IsPath := by
    apply SimpleGraph.Walk.IsPath.cons hd.isPath_toWalk
    simp [hb.ne.symm, hbd]
  let H : Fin 3 → G.Subgraph := ![p.toSubgraph, (q.concat ha).toSubgraph, r.toSubgraph]
  have hpaths : ∀ i, IsNonemptyPathSubgraph (H i) := by
    intro i
    fin_cases i
    · exact ⟨a, v, p, hp'.1, SimpleGraph.Walk.not_nil_of_isCycle_cons hp, rfl⟩
    · exact ⟨b, a, q.concat ha, hq'.1.concat hescape ha,
        SimpleGraph.Walk.not_nil_of_ne hba, rfl⟩
    · exact ⟨d, v, r, hr'.1, SimpleGraph.Walk.not_nil_of_isCycle_cons hr, rfl⟩
  have hdisj : Pairwise (fun i j => Disjoint (H i).edgeSet (H j).edgeSet) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals simp_all [H, SimpleGraph.Walk.concat_eq_append,
      Set.disjoint_insert_left, Set.disjoint_insert_right, disjoint_comm]
  have hdt : ∀ i, Disjoint (H i).edgeSet t.toSubgraph.edgeSet := by
    intro i
    fin_cases i
    all_goals simp_all [H, t, SimpleGraph.Walk.concat_eq_append,
      Set.disjoint_insert_left, Set.disjoint_insert_right, Sym2.eq_swap, disjoint_comm,
      ne_comm]
  have hcov : (⋃ i, (H i).edgeSet) ∪ t.toSubgraph.edgeSet = G.edgeSet := by
    rw [← hcover]
    ext e
    simp [H, t, SimpleGraph.Walk.concat_eq_append, Sym2.eq_swap, Fin.exists_fin_succ]
    tauto
  have hres := hasPathPartition_of_path_family_and_path H t.toSubgraph hpaths
    ⟨b, d, t, ht, SimpleGraph.Walk.not_nil_of_ne hbd, rfl⟩ hdisj hdt hcov
  simpa using hres

/-- A specified escape edge at a common vertex yields the unequal-support
three-cycle repair, without requiring any supplied walk orientation. -/
theorem hasPathPartition_four_of_three_cycles_escape_at {v x y : V}
    (c₀ c₁ c₂ : G.Walk v v)
    (hc₀ : c₀.IsCycle) (hc₁ : c₁.IsCycle) (hc₂ : c₂.IsCycle)
    (h01 : Disjoint c₀.edgeSet c₁.edgeSet)
    (h02 : Disjoint c₀.edgeSet c₂.edgeSet)
    (h12 : Disjoint c₁.edgeSet c₂.edgeSet)
    (hxy : G.Adj x y) (he : s(x, y) ∈ c₀.edgeSet)
    (hx₁ : x ∈ c₁.support) (hx₂ : x ∈ c₂.support) (hy : y ∉ c₁.support)
    (hcover : c₀.edgeSet ∪ (c₁.edgeSet ∪ c₂.edgeSet) = G.edgeSet) :
    HasPathPartition G 4 := by
  obtain ⟨b, _, hb, heb⟩ := cycle_neighbor_avoiding c₁ hc₁ x x hx₁
  obtain ⟨d, _, hd, hed⟩ := cycle_neighbor_avoiding c₂ hc₂ x x hx₂
  obtain ⟨p, hp, hpnil, hpnot, hpE⟩ := cycle_cut_oriented_edge c₀ hc₀ he
  obtain ⟨q, hq, hqnil, hqnot, hqE⟩ := cycle_cut_oriented_edge c₁ hc₁ heb
  obtain ⟨r, hr, hrnil, hrnot, hrE⟩ := cycle_cut_oriented_edge c₂ hc₂ hed
  have hpC := (SimpleGraph.Walk.cons_isCycle_iff p hxy).mpr ⟨hp, hpnot⟩
  have hqC := (SimpleGraph.Walk.cons_isCycle_iff q hb).mpr ⟨hq, hqnot⟩
  have hrC := (SimpleGraph.Walk.cons_isCycle_iff r hd).mpr ⟨hr, hrnot⟩
  have hpCE : (SimpleGraph.Walk.cons hxy p).edgeSet = c₀.edgeSet := by simpa using hpE
  have hqCE : (SimpleGraph.Walk.cons hb q).edgeSet = c₁.edgeSet := by simpa using hqE
  have hrCE : (SimpleGraph.Walk.cons hd r).edgeSet = c₂.edgeSet := by simpa using hrE
  apply hasPathPartition_four_of_three_cycle_escape hxy hb hd p q r hpC hqC hrC
  · simpa only [hpCE, hqCE] using h01
  · simpa only [hpCE, hrCE] using h02
  · simpa only [hqCE, hrCE] using h12
  · intro hyq
    apply hy
    apply walk_support_subset_of_edgeSet_subset q c₁ hqnil ?_ hyq
    intro e heq
    rw [← hqE]
    exact Set.mem_insert_of_mem _ heq
  · simpa only [hpCE, hqCE, hrCE] using hcover

/-- Three arbitrary edge-disjoint simple cycles through a common root admit
four simple paths, including unequal and partially overlapping vertex supports. -/
theorem hasPathPartition_four_of_three_cycles {v : V}
    (c : Fin 3 → G.Walk v v) (hc : ∀ i, (c i).IsCycle)
    (hd : Pairwise (fun i j => Disjoint (c i).edgeSet (c j).edgeSet))
    (hcover : (⋃ i, (c i).edgeSet) = G.edgeSet) :
    HasPathPartition G 4 := by
  classical
  by_cases hs : ∀ i x, x ∈ (c 0).support ↔ x ∈ (c i).support
  · exact hasPathPartition_four_of_three_equal_support_cycles c hc hs hd hcover
  · have hout : ∃ i j z, z ∈ (c i).support ∧ z ∉ (c j).support := by
      by_contra! hno
      apply hs
      intro i x
      exact ⟨hno 0 i x, hno i 0 x⟩
    obtain ⟨i, j, x, y, hxy, he, hx, hy⟩ := common_root_family_exit c hout
    have hij : i ≠ j := by
      intro hij
      subst j
      exact hy ((c i).snd_mem_support_of_mem_edges he)
    have hremaining : ∃ k : Fin 3, i ≠ k ∧ j ≠ k ∧
        ∀ l : Fin 3, l = i ∨ l = j ∨ l = k := by
      fin_cases i <;> fin_cases j
      all_goals first | exact (hij rfl).elim | decide
    obtain ⟨k, hik, hjk, hindices⟩ := hremaining
    apply hasPathPartition_four_of_three_cycles_escape_at (c i) (c j) (c k)
      (hc i) (hc j) (hc k) (hd hij) (hd hik) (hd hjk) hxy he (hx j) (hx k) hy
    rw [← hcover]
    ext e
    simp only [Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro (he | he | he)
      · exact ⟨i, he⟩
      · exact ⟨j, he⟩
      · exact ⟨k, he⟩
    · rintro ⟨l, hl⟩
      rcases hindices l with rfl | rfl | rfl
      · exact Or.inl hl
      · exact Or.inr (Or.inl hl)
      · exact Or.inr (Or.inr hl)

end Erdos583
end Source16_Erdos583_CycleBouquet
/- END Erdos583.CycleBouquet -/

/- BEGIN Erdos583.ShortPathRepair; source SHA256 9978ebd396663b11780d90c8c41e7ddedf19f9ff02d78135c9932c9b837c0267 -/
section Source17_Erdos583_ShortPathRepair


/-!
# Short path and cycle repair primitives

This file does not assume the short-path repair theorem. It proves the walk
concatenations and exact original-edge partitions needed to construct it.
-/

namespace Erdos583

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Two nonempty simple paths covering a specified original edge set, exposing
the named endpoints and sharing their other endpoint. -/
def HasPathPairAt (G : SimpleGraph V) (u v : V) (E : Set (Sym2 V)) : Prop :=
  ∃ (a : V) (p : G.Walk a u) (q : G.Walk a v),
    p.IsPath ∧ q.IsPath ∧ ¬p.Nil ∧ ¬q.Nil ∧
      Disjoint p.edgeSet q.edgeSet ∧ p.edgeSet ∪ q.edgeSet = E

theorem HasPathPairAt.toPathPartition {u v : V}
    (h : HasPathPairAt G u v G.edgeSet) : HasPathPartition G 2 := by
  obtain ⟨a, p, q, hp, hq, hpnil, hqnil, hd, hE⟩ := h
  apply hasPathPartition_two_of_subgraphs p.toSubgraph q.toSubgraph
  · exact ⟨a, u, p, hp, hpnil, rfl⟩
  · exact ⟨a, v, q, hq, hqnil, rfl⟩
  · simpa only [SimpleGraph.Walk.edgeSet_toSubgraph] using hd
  · simpa only [SimpleGraph.Walk.edgeSet_toSubgraph] using hE

theorem HasPathPairAt.swap {u v : V} {E : Set (Sym2 V)}
    (h : HasPathPairAt G u v E) : HasPathPairAt G v u E := by
  obtain ⟨a, p, q, hp, hq, hpnil, hqnil, hd, hE⟩ := h
  exact ⟨a, q, p, hq, hp, hqnil, hpnil, hd.symm,
    by simpa only [Set.union_comm] using hE⟩

/-- Paths whose only common support vertex is their joining endpoint concatenate
to a vertex-simple path. Either input may have zero edges. -/
theorem isPath_append_of_support_inter {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) (hp : p.IsPath) (hq : q.IsPath)
    (hm : ∀ x, x ∈ p.support → x ∈ q.support → x = v) :
    (p.append q).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [SimpleGraph.Walk.support_append]
  apply hp.support_nodup.append hq.support_nodup.tail
  intro x hx hxtail
  have hxq : x ∈ q.support := List.mem_of_mem_tail hxtail
  have hxv := hm x hx hxq
  subst x
  have hN := hq.support_nodup
  rw [← q.cons_tail_support] at hN
  exact (List.nodup_cons.mp hN).1 hxtail

/-- Walks meeting in at most one support vertex have no common edge. -/
theorem edgeSet_disjoint_of_support_inter {u v w z x : V}
    (p : G.Walk u v) (q : G.Walk w z)
    (hm : ∀ y, y ∈ p.support → y ∈ q.support → y = x) :
    Disjoint p.edgeSet q.edgeSet := by
  apply Set.disjoint_left.mpr
  intro e he he'
  induction e using Sym2.ind with
  | _ a b =>
    have ha := hm a (p.fst_mem_support_of_mem_edges he) (q.fst_mem_support_of_mem_edges he')
    have hb := hm b (p.snd_mem_support_of_mem_edges he) (q.snd_mem_support_of_mem_edges he')
    have hab : G.Adj a b := p.adj_of_mem_edges he
    exact hab.ne (ha.trans hb.symm)

/-- Attach disjoint exterior tails at the exposed endpoints of a path-pair
certificate. The tail hypotheses are expressed in original edge incidence. -/
theorem HasPathPairAt.attach_tails {u v u' v' : V} {E : Set (Sym2 V)}
    (h : HasPathPairAt G u v E) (L : G.Walk u u') (R : G.Walk v v')
    (hL : L.IsPath) (hR : R.IsPath)
    (hmL : ∀ x, x ∈ L.support → ∀ e ∈ E, x ∈ e → x = u)
    (hmR : ∀ x, x ∈ R.support → ∀ e ∈ E, x ∈ e → x = v)
    (hdLR : Disjoint L.edgeSet R.edgeSet) :
    HasPathPairAt G u' v' (E ∪ (L.edgeSet ∪ R.edgeSet)) := by
  obtain ⟨a, p, q, hp, hq, hpnil, hqnil, hdpq, hpqE⟩ := h
  have hpE : p.edgeSet ⊆ E := by
    rw [← hpqE]
    exact Set.subset_union_left
  have hqE : q.edgeSet ⊆ E := by
    rw [← hpqE]
    exact Set.subset_union_right
  have hpmL : ∀ x, x ∈ p.support → x ∈ L.support → x = u := by
    intro x hxp hxL
    obtain ⟨e, he, hxe⟩ :=
      (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hpnil).mp hxp
    exact hmL x hxL e (hpE he) hxe
  have hqmR : ∀ x, x ∈ q.support → x ∈ R.support → x = v := by
    intro x hxq hxR
    obtain ⟨e, he, hxe⟩ :=
      (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hqnil).mp hxq
    exact hmR x hxR e (hqE he) hxe
  have hdpR : Disjoint p.edgeSet R.edgeSet := by
    apply edgeSet_disjoint_of_support_inter p R
    intro x hxp hxR
    obtain ⟨e, he, hxe⟩ :=
      (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hpnil).mp hxp
    exact hmR x hxR e (hpE he) hxe
  have hdqL : Disjoint q.edgeSet L.edgeSet := by
    apply edgeSet_disjoint_of_support_inter q L
    intro x hxq hxL
    obtain ⟨e, he, hxe⟩ :=
      (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hqnil).mp hxq
    exact hmL x hxL e (hqE he) hxe
  refine ⟨a, p.append L, q.append R,
    isPath_append_of_support_inter p L hp hL hpmL,
    isPath_append_of_support_inter q R hq hR hqmR, ?_, ?_, ?_, ?_⟩
  · intro hn
    exact hpnil ((SimpleGraph.Walk.nil_append_iff).mp hn).1
  · intro hn
    exact hqnil ((SimpleGraph.Walk.nil_append_iff).mp hn).1
  · simp only [SimpleGraph.Walk.edgeSet_append,
      Set.disjoint_union_left, Set.disjoint_union_right]
    exact ⟨⟨hdpq, hdqL.symm⟩, ⟨hdpR, hdLR⟩⟩
  · rw [← hpqE]
    ext e
    simp only [SimpleGraph.Walk.edgeSet_append, Set.mem_union]
    tauto

/-- A simple path ending at its only common vertex with a cycle can be absorbed
without increasing the two-path cost of that cycle. -/
theorem hasPathPartition_two_of_path_cycle_endpoint {u v : V}
    (p : G.Walk u v) (c : G.Walk v v) (hp : p.IsPath) (hc : c.IsCycle)
    (hm : ∀ x, x ∈ p.support → x ∈ c.support → x = v)
    (hcover : p.edgeSet ∪ c.edgeSet = G.edgeSet) :
    HasPathPartition G 2 := by
  classical
  have hdisj := edgeSet_disjoint_of_support_inter p c hm
  cases c with
  | nil => exact (SimpleGraph.Walk.not_isCycle_nil hc).elim
  | @cons v a v ha q =>
    have hq := (SimpleGraph.Walk.cons_isCycle_iff q ha).mp hc
    have hjoin : (p.append q.reverse).IsPath := by
      apply isPath_append_of_support_inter p q.reverse hp hq.1.reverse
      intro x hxp hxq
      apply hm x hxp
      have hxq' : x ∈ q.support := by simpa using hxq
      simp [hxq']
    have hnonempty : ¬(p.append q.reverse).Nil := by
      simp only [SimpleGraph.Walk.nil_append_iff, SimpleGraph.Walk.nil_reverse]
      exact fun h => SimpleGraph.Walk.not_nil_of_isCycle_cons hc h.2
    apply hasPathPartition_two_of_subgraphs ha.toWalk.toSubgraph
      (p.append q.reverse).toSubgraph
    · exact ⟨v, a, ha.toWalk, ha.isPath_toWalk,
        SimpleGraph.Walk.not_nil_of_ne ha.ne, rfl⟩
    · exact ⟨u, a, p.append q.reverse, hjoin, hnonempty, rfl⟩
    · rw [SimpleGraph.Walk.edgeSet_toSubgraph, SimpleGraph.Walk.edgeSet_toSubgraph]
      apply Set.disjoint_left.mpr
      intro e he he'
      have heq : e = s(v, a) := by simpa using he
      subst e
      rw [SimpleGraph.Walk.edgeSet_append, SimpleGraph.Walk.edgeSet_reverse] at he'
      rcases he' with he' | he'
      · exact Set.disjoint_left.mp hdisj he' (by simp)
      · exact hq.2 he'
    · rw [SimpleGraph.Walk.edgeSet_toSubgraph, SimpleGraph.Walk.edgeSet_toSubgraph]
      rw [← hcover]
      ext e
      simp

/-- The two-intersection repair certificate: three internally disjoint u-to-v
paths, with one split at an interior vertex, admit two simple paths. -/
theorem pathPairAt_of_theta_split {u v a : V} {E : Set (Sym2 V)}
    (A₁ : G.Walk u a) (A₂ : G.Walk a v) (B Q : G.Walk u v)
    (hA : (A₁.append A₂).IsPath) (hB : B.IsPath) (hQ : Q.IsPath)
    (hau : a ≠ u) (hav : a ≠ v)
    (hmAB : ∀ x, x ∈ (A₁.append A₂).support → x ∈ B.support → x = u ∨ x = v)
    (hmAQ : ∀ x, x ∈ (A₁.append A₂).support → x ∈ Q.support → x = u ∨ x = v)
    (hdAB : Disjoint (A₁.append A₂).edgeSet B.edgeSet)
    (hdAQ : Disjoint (A₁.append A₂).edgeSet Q.edgeSet)
    (hdBQ : Disjoint B.edgeSet Q.edgeSet)
    (hcover : (A₁.append A₂).edgeSet ∪ (B.edgeSet ∪ Q.edgeSet) = E) :
    HasPathPairAt G v u E := by
  have h₁ : (A₁.reverse.append B).IsPath := by
    apply isPath_append_of_support_inter A₁.reverse B hA.of_append_left.reverse hB
    intro x hx hxb
    have hx₁ : x ∈ A₁.support := by simpa using hx
    have hxA := (A₁.support_subset_support_append_left A₂) hx₁
    rcases hmAB x hxA hxb with hxu | hxv
    · exact hxu
    · subst x
      exact ((hA.ne_of_mem_support_of_append hav.symm hx₁ A₂.end_mem_support) rfl).elim
  have h₂ : (A₂.append Q.reverse).IsPath := by
    apply isPath_append_of_support_inter A₂ Q.reverse hA.of_append_right hQ.reverse
    intro x hx hxq
    have hxq' : x ∈ Q.support := by simpa using hxq
    have hxA := (A₁.support_subset_support_append_right A₂) hx
    rcases hmAQ x hxA hxq' with hxu | hxv
    · subst x
      exact ((hA.ne_of_mem_support_of_append hau.symm A₁.start_mem_support hx) rfl).elim
    · exact hxv
  have hdA : Disjoint A₁.edgeSet A₂.edgeSet := by
    apply Set.disjoint_left.mpr
    exact (SimpleGraph.Walk.isTrail_append A₁ A₂).mp hA.isTrail |>.2.2
  rw [SimpleGraph.Walk.edgeSet_append, Set.disjoint_union_left] at hdAB hdAQ
  refine ⟨a, A₁.reverse.append B, A₂.append Q.reverse, h₁, h₂,
    SimpleGraph.Walk.not_nil_of_ne hav, SimpleGraph.Walk.not_nil_of_ne hau, ?_, ?_⟩
  · simp only [SimpleGraph.Walk.edgeSet_append,
      SimpleGraph.Walk.edgeSet_reverse, Set.disjoint_union_left, Set.disjoint_union_right]
    exact ⟨⟨hdA, hdAB.2.symm⟩, ⟨hdAQ.1, hdBQ⟩⟩
  · rw [← hcover]
    ext e
    simp only [SimpleGraph.Walk.edgeSet_append,
      SimpleGraph.Walk.edgeSet_reverse, Set.mem_union]
    tauto

/-- Splitting a cycle at a second vertex yields two internally disjoint simple
paths, covering exactly the original cycle edges. -/
theorem cycle_two_arcs {u v : V} (c : G.Walk u u) (hc : c.IsCycle)
    (hv : v ∈ c.support) (huv : u ≠ v) :
    ∃ A B : G.Walk u v, A.IsPath ∧ B.IsPath ∧ ¬A.Nil ∧ ¬B.Nil ∧
      Disjoint A.edgeSet B.edgeSet ∧ A.edgeSet ∪ B.edgeSet = c.edgeSet ∧
      (∀ x, x ∈ A.support → x ∈ B.support → x = u ∨ x = v) := by
  classical
  let A := c.takeUntil v hv
  let R := c.dropUntil v hv
  have hsplit : A.append R = c := c.take_spec hv
  have hcy : (A.append R).IsCycle := hsplit ▸ hc
  have hA : A.IsPath := hc.isPath_takeUntil hv
  have hR : R.IsPath := hcy.isPath_of_append_right (SimpleGraph.Walk.not_nil_of_ne huv)
  refine ⟨A, R.reverse, hA, hR.reverse, SimpleGraph.Walk.not_nil_of_ne huv,
    SimpleGraph.Walk.not_nil_of_ne huv, ?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.edgeSet_reverse]
    apply Set.disjoint_left.mpr
    exact (SimpleGraph.Walk.isTrail_append A R).mp hcy.isTrail |>.2.2
  · rw [SimpleGraph.Walk.edgeSet_reverse, ← SimpleGraph.Walk.edgeSet_append, hsplit]
  · intro x hxA hxR
    have hxR' : x ∈ R.support := by simpa using hxR
    by_cases hxu : x = u
    · exact Or.inl hxu
    by_cases hxv : x = v
    · exact Or.inr hxv
    have hxAt : x ∈ A.support.tail := (A.mem_support_iff.mp hxA).resolve_left hxu
    have hxRt : x ∈ R.support.tail := (R.mem_support_iff.mp hxR').resolve_left hxv
    have hN := hcy.support_nodup
    rw [SimpleGraph.Walk.tail_support_append, List.nodup_append'] at hN
    exact (hN.2.2 hxAt hxRt).elim

/-- A path of at least two edges has a split at an interior vertex. -/
theorem path_split_internal {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hlen : 2 ≤ p.length) :
    ∃ (a : V) (A : G.Walk u a) (B : G.Walk a v),
      p = A.append B ∧ a ≠ u ∧ a ≠ v ∧ A.IsPath ∧ B.IsPath := by
  cases p with
  | nil => simp at hlen
  | @cons u a v h p =>
    have hp' := (SimpleGraph.Walk.cons_isPath_iff h p).mp hp
    have hpnil : ¬p.Nil := by
      intro hn
      have hzero := SimpleGraph.Walk.length_eq_zero_iff.mpr hn
      simp [hzero] at hlen
    have hav : a ≠ v := by
      intro hav
      exact hpnil (hp'.1.nil_iff_eq.mpr hav)
    exact ⟨a, h.toWalk, p, by simp, h.ne.symm, hav, h.isPath_toWalk, hp'.1⟩

/-- The theta repair with the interior split extracted from a long first arc. -/
theorem pathPairAt_of_theta_long_arc {u v : V} {E : Set (Sym2 V)}
    (A B Q : G.Walk u v) (hA : A.IsPath) (hB : B.IsPath) (hQ : Q.IsPath)
    (hlen : 2 ≤ A.length)
    (hmAB : ∀ x, x ∈ A.support → x ∈ B.support → x = u ∨ x = v)
    (hmAQ : ∀ x, x ∈ A.support → x ∈ Q.support → x = u ∨ x = v)
    (hdAB : Disjoint A.edgeSet B.edgeSet) (hdAQ : Disjoint A.edgeSet Q.edgeSet)
    (hdBQ : Disjoint B.edgeSet Q.edgeSet)
    (hcover : A.edgeSet ∪ (B.edgeSet ∪ Q.edgeSet) = E) :
    HasPathPairAt G v u E := by
  obtain ⟨a, A₁, A₂, hsplit, hau, hav, _, _⟩ := path_split_internal A hA hlen
  subst A
  exact pathPairAt_of_theta_split A₁ A₂ B Q hA hB hQ hau hav
    hmAB hmAQ hdAB hdAQ hdBQ hcover

/-- A cycle and a path whose only common vertices are the path endpoints admit
two simple paths. The path may have any length and its internal vertices are
outside the cycle. -/
theorem pathPairAt_of_path_cycle_two_endpoints {u v : V} {E : Set (Sym2 V)}
    (c : G.Walk u u) (Q : G.Walk u v) (hc : c.IsCycle) (hQ : Q.IsPath)
    (huv : u ≠ v) (hv : v ∈ c.support)
    (hm : ∀ x, x ∈ c.support → x ∈ Q.support → x = u ∨ x = v)
    (hd : Disjoint c.edgeSet Q.edgeSet)
    (hcover : c.edgeSet ∪ Q.edgeSet = E) :
    HasPathPairAt G v u E := by
  obtain ⟨A, B, hA, hB, hnA, hnB, hdAB, hE, hmAB⟩ := cycle_two_arcs c hc hv huv
  have hEA : A.edgeSet ⊆ c.edgeSet := by
    intro e he
    rw [← hE]
    exact Or.inl he
  have hEB : B.edgeSet ⊆ c.edgeSet := by
    intro e he
    rw [← hE]
    exact Or.inr he
  have hmAQ : ∀ x, x ∈ A.support → x ∈ Q.support → x = u ∨ x = v := by
    intro x hx hxQ
    exact hm x (walk_support_subset_of_edgeSet_subset A c hnA hEA hx) hxQ
  have hmBQ : ∀ x, x ∈ B.support → x ∈ Q.support → x = u ∨ x = v := by
    intro x hx hxQ
    exact hm x (walk_support_subset_of_edgeSet_subset B c hnB hEB hx) hxQ
  have hdAQ : Disjoint A.edgeSet Q.edgeSet := hd.mono_left hEA
  have hdBQ : Disjoint B.edgeSet Q.edgeSet := hd.mono_left hEB
  have hlong : 2 ≤ A.length ∨ 2 ≤ B.length := by
    by_contra! hshort
    have hEq : A = B := SimpleGraph.Walk.eq_of_length_le_one (by omega) (by omega)
    subst B
    have hpA : IsNonemptyPathSubgraph A.toSubgraph := ⟨u, v, A, hA, hnA, rfl⟩
    obtain ⟨e, he⟩ := hpA.edgeSet_nonempty
    rw [SimpleGraph.Walk.edgeSet_toSubgraph] at he
    exact Set.disjoint_left.mp hdAB he he
  have hcov : A.edgeSet ∪ (B.edgeSet ∪ Q.edgeSet) = E := by
    rw [← Set.union_assoc, hE, hcover]
  rcases hlong with hlong | hlong
  · exact pathPairAt_of_theta_long_arc A B Q hA hB hQ hlong
      hmAB hmAQ hdAB hdAQ hdBQ hcov
  · apply pathPairAt_of_theta_long_arc B A Q hB hA hQ hlong
      (fun x hxB hxA => hmAB x hxA hxB) hmBQ hdAB.symm hdBQ hdAQ
    simpa only [Set.union_left_comm] using hcov

/-- One intersection may lie internally on the input path: split that path and
attach its two tails to separate cycle pieces. -/
theorem pathPairAt_of_path_cycle_one_intersection {u v w : V} {E : Set (Sym2 V)}
    (P : G.Walk u w) (c : G.Walk v v) (hp : P.IsPath) (hc : c.IsCycle)
    (hv : v ∈ P.support)
    (hm : ∀ x, x ∈ P.support → x ∈ c.support → x = v)
    (hcover : P.edgeSet ∪ c.edgeSet = E) :
    HasPathPairAt G u w E := by
  classical
  let A := P.takeUntil v hv
  let B := P.dropUntil v hv
  have hsplit : A.append B = P := P.take_spec hv
  have hA : A.IsPath := hp.takeUntil hv
  have hB : B.IsPath := hp.dropUntil hv
  have hAs : A.support ⊆ P.support := P.support_takeUntil_subset_support hv
  have hBs : B.support ⊆ P.support := P.support_dropUntil_subset_support hv
  have hAB : Disjoint A.edgeSet B.edgeSet := by
    apply Set.disjoint_left.mpr
    have htrail : (A.append B).IsTrail := hsplit ▸ hp.isTrail
    exact (SimpleGraph.Walk.isTrail_append A B).mp htrail |>.2.2
  have hPC := edgeSet_disjoint_of_support_inter P c hm
  have hAE : A.edgeSet ⊆ P.edgeSet := by
    rw [← hsplit, SimpleGraph.Walk.edgeSet_append]
    exact Set.subset_union_left
  have hBE : B.edgeSet ⊆ P.edgeSet := by
    rw [← hsplit, SimpleGraph.Walk.edgeSet_append]
    exact Set.subset_union_right
  cases c with
  | nil => exact (SimpleGraph.Walk.not_isCycle_nil hc).elim
  | @cons v a v ha q =>
    have hq := (SimpleGraph.Walk.cons_isCycle_iff q ha).mp hc
    have h₁ : (A.append q.reverse).IsPath := by
      apply isPath_append_of_support_inter A q.reverse hA hq.1.reverse
      intro x hx hxq
      apply hm x (hAs hx)
      have hxq' : x ∈ q.support := by simpa using hxq
      simp [hxq']
    have h₂ : (B.reverse.append ha.toWalk).IsPath := by
      apply isPath_append_of_support_inter B.reverse ha.toWalk hB.reverse ha.isPath_toWalk
      intro x hx hxedge
      have hxB : x ∈ B.support := by simpa using hx
      apply hm x (hBs hxB)
      have hxedge' : x = v ∨ x = a := by simpa using hxedge
      rcases hxedge' with rfl | rfl
      · simp
      · simp [q.start_mem_support]
    have hn₁ : ¬(A.append q.reverse).Nil := by
      simp only [SimpleGraph.Walk.nil_append_iff, SimpleGraph.Walk.nil_reverse]
      exact fun h => SimpleGraph.Walk.not_nil_of_isCycle_cons hc h.2
    have hn₂ : ¬(B.reverse.append ha.toWalk).Nil := by
      simp only [SimpleGraph.Walk.nil_append_iff]
      exact fun h => SimpleGraph.Walk.not_nil_of_ne ha.ne h.2
    have hAq : Disjoint A.edgeSet q.edgeSet := by
      apply (hPC.mono_left hAE).mono_right
      intro e he
      simp [he]
    have hBq : Disjoint B.edgeSet q.edgeSet := by
      apply (hPC.mono_left hBE).mono_right
      intro e he
      simp [he]
    have hAh : Disjoint A.edgeSet ha.toWalk.edgeSet := by
      apply (hPC.mono_left hAE).mono_right
      intro e he
      have heq : e = s(v, a) := by simpa using he
      simp [heq]
    have hqh : Disjoint q.edgeSet ha.toWalk.edgeSet := by
      apply Set.disjoint_left.mpr
      intro e he he'
      have heq : e = s(v, a) := by simpa using he'
      exact hq.2 (heq ▸ he)
    refine ⟨a, (A.append q.reverse).reverse, (B.reverse.append ha.toWalk).reverse,
      h₁.reverse, h₂.reverse,
      by rw [SimpleGraph.Walk.nil_reverse]; exact hn₁,
      by rw [SimpleGraph.Walk.nil_reverse]; exact hn₂, ?_, ?_⟩
    · simp only [SimpleGraph.Walk.edgeSet_append,
        SimpleGraph.Walk.edgeSet_reverse, Set.disjoint_union_left, Set.disjoint_union_right]
      exact ⟨⟨hAB, hBq.symm⟩, ⟨hAh, hqh⟩⟩
    · rw [← hcover, ← hsplit]
      ext e
      simp only [SimpleGraph.Walk.edgeSet_append,
        SimpleGraph.Walk.edgeSet_reverse, SimpleGraph.Walk.edgeSet_cons, Set.mem_union,
        Set.mem_insert_iff]
      simp
      tauto

/-- The two pieces of a simple path have only the split vertex in common. -/
theorem isPath_append_support_inter {u v w : V} (A : G.Walk u v) (B : G.Walk v w)
    (h : (A.append B).IsPath) {x : V} (hxA : x ∈ A.support) (hxB : x ∈ B.support) :
    x = v := by
  by_contra hxv
  exact (h.ne_of_mem_support_of_append hxv hxA hxB) rfl

/-- Given a third cycle vertex, orient the two arcs so the second contains it
and the first avoids it. -/
theorem cycle_two_arcs_through_third {u w v : V} (c : G.Walk u u) (hc : c.IsCycle)
    (hw : w ∈ c.support) (hv : v ∈ c.support)
    (huw : u ≠ w) (hvu : v ≠ u) (hvw : v ≠ w) :
    ∃ A R : G.Walk u w, A.IsPath ∧ R.IsPath ∧ Disjoint A.edgeSet R.edgeSet ∧
      A.edgeSet ∪ R.edgeSet = c.edgeSet ∧
      (∀ x, x ∈ A.support → x ∈ R.support → x = u ∨ x = w) ∧
      v ∈ R.support ∧ v ∉ A.support := by
  obtain ⟨A, B, hA, hB, _, _, hd, hE, hm⟩ := cycle_two_arcs c hc hw huw
  have hvAB : v ∈ A.support ∨ v ∈ B.support := by
    obtain ⟨e, he, hve⟩ :=
      (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hc.not_nil).mp hv
    change e ∈ c.edgeSet at he
    rw [← hE] at he
    rcases he with he | he
    · exact Or.inl (A.mem_support_of_mem_edges he hve)
    · exact Or.inr (B.mem_support_of_mem_edges he hve)
  rcases hvAB with hvA | hvB
  · refine ⟨B, A, hB, hA, hd.symm, ?_, (fun x hxB hxA => hm x hxA hxB), hvA, ?_⟩
    · simpa only [Set.union_comm] using hE
    · intro hvB
      exact (hm v hvA hvB).elim hvu hvw
  · refine ⟨A, B, hA, hB, hd, hE, hm, hvB, ?_⟩
    intro hvA
    exact (hm v hvA hvB).elim hvu hvw

/-- Three distinct cycle vertices cut the cycle into three simple arcs meeting
only at the displayed endpoints. Their original edges remain a partition. -/
theorem cycle_three_arcs {u w v : V} (c : G.Walk u u) (hc : c.IsCycle)
    (hw : w ∈ c.support) (hv : v ∈ c.support)
    (huw : u ≠ w) (hvu : v ≠ u) (hvw : v ≠ w) :
    ∃ (A : G.Walk u w) (B : G.Walk w v) (D : G.Walk v u),
      A.IsPath ∧ B.IsPath ∧ D.IsPath ∧
      Disjoint A.edgeSet B.edgeSet ∧ Disjoint A.edgeSet D.edgeSet ∧
      Disjoint B.edgeSet D.edgeSet ∧
      A.edgeSet ∪ (B.edgeSet ∪ D.edgeSet) = c.edgeSet ∧
      (∀ x, x ∈ A.support → x ∈ B.support → x = w) ∧
      (∀ x, x ∈ A.support → x ∈ D.support → x = u) ∧
      (∀ x, x ∈ B.support → x ∈ D.support → x = v) := by
  classical
  obtain ⟨A, R, hA, hR, hd, hE, hm, hvR, _⟩ :=
    cycle_two_arcs_through_third c hc hw hv huw hvu hvw
  let T := R.takeUntil v hvR
  let U := R.dropUntil v hvR
  have hsplit : T.append U = R := R.take_spec hvR
  have hsplitPath : (T.append U).IsPath := hsplit ▸ hR
  have hT : T.IsPath := hR.takeUntil hvR
  have hU : U.IsPath := hR.dropUntil hvR
  have hTs : T.support ⊆ R.support := R.support_takeUntil_subset_support hvR
  have hUs : U.support ⊆ R.support := R.support_dropUntil_subset_support hvR
  have hdTU : Disjoint T.edgeSet U.edgeSet := by
    apply Set.disjoint_left.mpr
    exact (SimpleGraph.Walk.isTrail_append T U).mp hsplitPath.isTrail |>.2.2
  have hER : T.edgeSet ∪ U.edgeSet = R.edgeSet := by
    rw [← SimpleGraph.Walk.edgeSet_append, hsplit]
  have hdAT : Disjoint A.edgeSet T.edgeSet := hd.mono_right (by
    rw [← hER]
    exact Set.subset_union_left)
  have hdAU : Disjoint A.edgeSet U.edgeSet := hd.mono_right (by
    rw [← hER]
    exact Set.subset_union_right)
  refine ⟨A, U.reverse, T.reverse, hA, hU.reverse, hT.reverse, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [SimpleGraph.Walk.edgeSet_reverse] using hdAU
  · simpa only [SimpleGraph.Walk.edgeSet_reverse] using hdAT
  · simpa only [SimpleGraph.Walk.edgeSet_reverse] using hdTU.symm
  · simp only [SimpleGraph.Walk.edgeSet_reverse]
    rw [Set.union_comm U.edgeSet T.edgeSet, hER, hE]
  · intro x hxA hxU
    have hxU' : x ∈ U.support := by simpa using hxU
    rcases hm x hxA (hUs hxU') with hxu | hxw
    · subst x
      exact ((hsplitPath.ne_of_mem_support_of_append hvu.symm
        T.start_mem_support hxU') rfl).elim
    · exact hxw
  · intro x hxA hxT
    have hxT' : x ∈ T.support := by simpa using hxT
    rcases hm x hxA (hTs hxT') with hxu | hxw
    · exact hxu
    · subst x
      exact ((hsplitPath.ne_of_mem_support_of_append hvw.symm
        hxT' U.end_mem_support) rfl).elim
  · intro x hxU hxT
    apply isPath_append_support_inter T U hsplitPath
    · simpa using hxT
    · simpa using hxU

/-- The three-intersection base case. The first between-intersection segment is
a single original edge; the second has its internal vertices outside the cycle. -/
theorem pathPairAt_of_path_cycle_three_vertices {u w v : V} {E : Set (Sym2 V)}
    (c : G.Walk u u) (h : G.Adj u w) (Q : G.Walk w v)
    (hc : c.IsCycle) (hp : (SimpleGraph.Walk.cons h Q).IsPath)
    (hw : w ∈ c.support) (hv : v ∈ c.support) (hvu : v ≠ u) (hvw : v ≠ w)
    (hmQ : ∀ x, x ∈ c.support → x ∈ Q.support → x = w ∨ x = v)
    (hdPC : Disjoint (SimpleGraph.Walk.cons h Q).edgeSet c.edgeSet)
    (hcover : c.edgeSet ∪ (SimpleGraph.Walk.cons h Q).edgeSet = E) :
    HasPathPairAt G v u E := by
  classical
  have hp' := (SimpleGraph.Walk.cons_isPath_iff h Q).mp hp
  obtain ⟨A, B, D, hA, hB, hD, hdAB, hdAD, hdBD, hCE, hmAB, hmAD, hmBD⟩ :=
    cycle_three_arcs c hc hw hv h.ne hvu hvw
  have hEA : A.edgeSet ⊆ c.edgeSet := by
    rw [← hCE]
    exact Set.subset_union_left
  have hEB : B.edgeSet ⊆ c.edgeSet := by
    rw [← hCE]
    exact Set.subset_union_of_subset_right Set.subset_union_left _
  have hED : D.edgeSet ⊆ c.edgeSet := by
    rw [← hCE]
    exact Set.subset_union_of_subset_right Set.subset_union_right _
  have hCQ : Disjoint c.edgeSet Q.edgeSet := hdPC.symm.mono_right (by
    intro e he
    simp [he])
  have hCh : s(u, w) ∉ c.edgeSet := by
    intro he
    apply Set.disjoint_left.mp hdPC (show s(u, w) ∈
      (SimpleGraph.Walk.cons h Q).edgeSet by simp) he
  have hAlen : 2 ≤ A.length := by
    by_contra hlen
    have hEq : A = h.toWalk := SimpleGraph.Walk.eq_of_length_le_one (by omega) (by simp)
    apply hCh
    apply hEA
    simp [hEq]
  obtain ⟨a, A₁, A₂, hAsplit, hau, haw, _, _⟩ := path_split_internal A hA hAlen
  have hA12 : (A₁.append A₂).IsPath := hAsplit ▸ hA
  have hA₁ : A₁.IsPath := hA12.of_append_left
  have hA₂ : A₂.IsPath := hA12.of_append_right
  have hA₁s : A₁.support ⊆ A.support := by
    rw [hAsplit]
    exact A₁.support_subset_support_append_left A₂
  have hA₂s : A₂.support ⊆ A.support := by
    rw [hAsplit]
    exact A₁.support_subset_support_append_right A₂
  have hA₁E : A₁.edgeSet ⊆ A.edgeSet := by
    rw [hAsplit, SimpleGraph.Walk.edgeSet_append]
    exact Set.subset_union_left
  have hA₂E : A₂.edgeSet ⊆ A.edgeSet := by
    rw [hAsplit, SimpleGraph.Walk.edgeSet_append]
    exact Set.subset_union_right
  have hAu : u ∉ A₂.support := by
    intro hu
    exact (hA12.ne_of_mem_support_of_append hau.symm A₁.start_mem_support hu) rfl
  have hAw : w ∉ A₁.support := by
    intro hw₁
    exact (hA12.ne_of_mem_support_of_append haw.symm hw₁ A₂.end_mem_support) rfl
  have hAv : v ∉ A.support := by
    intro hvA
    exact hvw (hmAB v hvA B.end_mem_support)
  have hBu : u ∉ B.support := by
    intro huB
    exact h.ne (hmAB u A.start_mem_support huB)
  have hDw : w ∉ D.support := by
    intro hwD
    exact h.ne.symm (hmAD w A.end_mem_support hwD)
  have hAs : A.support ⊆ c.support :=
    walk_support_subset_of_edgeSet_subset A c (SimpleGraph.Walk.not_nil_of_ne h.ne) hEA
  have hDs : D.support ⊆ c.support :=
    walk_support_subset_of_edgeSet_subset D c (SimpleGraph.Walk.not_nil_of_ne hvu) hED
  have hQB : (Q.append D).IsPath := by
    apply isPath_append_of_support_inter Q D hp'.1 hD
    intro x hxQ hxD
    rcases hmQ x (hDs hxD) hxQ with hxw | hxv
    · subst x
      exact (hDw hxD).elim
    · exact hxv
  have h₁ : (A₁.reverse.append (SimpleGraph.Walk.cons h B)).IsPath := by
    apply isPath_append_of_support_inter A₁.reverse (SimpleGraph.Walk.cons h B)
      hA₁.reverse (hB.cons hBu)
    intro x hxA hxB
    have hxA' : x ∈ A₁.support := by simpa using hxA
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hxB
    rcases hxB with hxu | hxB
    · exact hxu
    · have hxw := hmAB x (hA₁s hxA') hxB
      exact (hAw (hxw ▸ hxA')).elim
  have h₂ : (A₂.append (Q.append D)).IsPath := by
    apply isPath_append_of_support_inter A₂ (Q.append D) hA₂ hQB
    intro x hxA hxQD
    rw [SimpleGraph.Walk.mem_support_append_iff] at hxQD
    rcases hxQD with hxQ | hxD
    · rcases hmQ x (hAs (hA₂s hxA)) hxQ with hxw | hxv
      · exact hxw
      · exact (hAv (hxv ▸ hA₂s hxA)).elim
    · have hxu := hmAD x (hA₂s hxA) hxD
      exact (hAu (hxu ▸ hxA)).elim
  have hav : a ≠ v := by
    intro hav
    subst a
    exact hAv (hA₁s A₁.end_mem_support)
  have hdA12 : Disjoint A₁.edgeSet A₂.edgeSet := by
    apply Set.disjoint_left.mpr
    exact (SimpleGraph.Walk.isTrail_append A₁ A₂).mp hA12.isTrail |>.2.2
  refine ⟨a, A₁.reverse.append (SimpleGraph.Walk.cons h B), A₂.append (Q.append D),
    h₁, h₂, SimpleGraph.Walk.not_nil_of_ne hav, SimpleGraph.Walk.not_nil_of_ne hau, ?_, ?_⟩
  ·
    apply Set.disjoint_left.mpr
    intro e he₁ he₂
    simp only [SimpleGraph.Walk.edgeSet_append, SimpleGraph.Walk.edgeSet_reverse,
      SimpleGraph.Walk.edgeSet_cons, Set.mem_union, Set.mem_insert_iff] at he₁ he₂
    rcases he₁ with heA₁ | heh | heB <;> rcases he₂ with heA₂ | heQ | heD
    · exact Set.disjoint_left.mp hdA12 heA₁ heA₂
    · exact Set.disjoint_left.mp hCQ (hEA (hA₁E heA₁)) heQ
    · exact Set.disjoint_left.mp hdAD (hA₁E heA₁) heD
    · exact hCh (heh ▸ hEA (hA₂E heA₂))
    · exact hp'.2 (Q.fst_mem_support_of_mem_edges (heh ▸ heQ))
    · exact hCh (heh ▸ hED heD)
    · exact Set.disjoint_left.mp hdAB (hA₂E heA₂) heB
    · exact Set.disjoint_left.mp hCQ (hEB heB) heQ
    · exact Set.disjoint_left.mp hdBD heB heD
  · rw [← hcover, ← hCE, hAsplit]
    ext e
    simp only [SimpleGraph.Walk.edgeSet_append,
      SimpleGraph.Walk.edgeSet_reverse, SimpleGraph.Walk.edgeSet_cons,
      Set.mem_union, Set.mem_insert_iff]
    tauto

/-- Forgetting exposed endpoints gives the ordinary one-intersection bound. -/
theorem hasPathPartition_two_of_path_cycle_one_intersection {u v w : V}
    (P : G.Walk u w) (c : G.Walk v v) (hp : P.IsPath) (hc : c.IsCycle)
    (hv : v ∈ P.support)
    (hm : ∀ x, x ∈ P.support → x ∈ c.support → x = v)
    (hcover : P.edgeSet ∪ c.edgeSet = G.edgeSet) : HasPathPartition G 2 :=
  (pathPairAt_of_path_cycle_one_intersection P c hp hc hv hm hcover).toPathPartition

/-- Forgetting exposed endpoints gives the ordinary two-intersection bound. -/
theorem hasPathPartition_two_of_path_cycle_two_endpoints {u v : V}
    (c : G.Walk u u) (Q : G.Walk u v) (hc : c.IsCycle) (hQ : Q.IsPath)
    (huv : u ≠ v) (hv : v ∈ c.support)
    (hm : ∀ x, x ∈ c.support → x ∈ Q.support → x = u ∨ x = v)
    (hd : Disjoint c.edgeSet Q.edgeSet)
    (hcover : c.edgeSet ∪ Q.edgeSet = G.edgeSet) : HasPathPartition G 2 :=
  (pathPairAt_of_path_cycle_two_endpoints c Q hc hQ huv hv hm hd hcover).toPathPartition

/-- Forgetting exposed endpoints gives the ordinary three-intersection core bound. -/
theorem hasPathPartition_two_of_path_cycle_three_vertices {u w v : V}
    (c : G.Walk u u) (h : G.Adj u w) (Q : G.Walk w v)
    (hc : c.IsCycle) (hp : (SimpleGraph.Walk.cons h Q).IsPath)
    (hw : w ∈ c.support) (hv : v ∈ c.support) (hvu : v ≠ u) (hvw : v ≠ w)
    (hmQ : ∀ x, x ∈ c.support → x ∈ Q.support → x = w ∨ x = v)
    (hdPC : Disjoint (SimpleGraph.Walk.cons h Q).edgeSet c.edgeSet)
    (hcover : c.edgeSet ∪ (SimpleGraph.Walk.cons h Q).edgeSet = G.edgeSet) :
    HasPathPartition G 2 :=
  (pathPairAt_of_path_cycle_three_vertices c h Q hc hp hw hv hvu hvw hmQ hdPC hcover).toPathPartition

end Erdos583
end Source17_Erdos583_ShortPathRepair
/- END Erdos583.ShortPathRepair -/

/- BEGIN Erdos583.ShortPathFour; source SHA256 fd85f80171bf63a2d58913cfccdf32651bea64e3dca3996120ed0c862470bd98 -/
section Source18_Erdos583_ShortPathFour


/-! Exact four-intersection repair, using original cycle arcs. -/
namespace Erdos583
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- Four cyclically ordered simple arcs, with their exact support intersections. -/
structure CycleQuad (G : SimpleGraph V) (u w z v : V) (E : Set (Sym2 V)) where
  A : G.Walk u w
  B : G.Walk w z
  C : G.Walk z v
  D : G.Walk v u
  pathA : A.IsPath
  pathB : B.IsPath
  pathC : C.IsPath
  pathD : D.IsPath
  neUW : u ≠ w
  neUZ : u ≠ z
  neUV : u ≠ v
  neWZ : w ≠ z
  neWV : w ≠ v
  neZV : z ≠ v
  interAB : ∀ x, x ∈ A.support → x ∈ B.support → x = w
  disjAC : ∀ x, x ∈ A.support → x ∈ C.support → False
  interAD : ∀ x, x ∈ A.support → x ∈ D.support → x = u
  interBC : ∀ x, x ∈ B.support → x ∈ C.support → x = z
  disjBD : ∀ x, x ∈ B.support → x ∈ D.support → False
  interCD : ∀ x, x ∈ C.support → x ∈ D.support → x = v
  cover : A.edgeSet ∪ (B.edgeSet ∪ (C.edgeSet ∪ D.edgeSet)) = E

namespace CycleQuad
variable {u w z v : V} {E : Set (Sym2 V)}

theorem arcA_subset (S : CycleQuad G u w z v E) : S.A.edgeSet ⊆ E := by
  intro e he
  have h : e ∈ S.A.edgeSet ∪ (S.B.edgeSet ∪ (S.C.edgeSet ∪ S.D.edgeSet)) := Or.inl he
  rwa [S.cover] at h

theorem arcB_subset (S : CycleQuad G u w z v E) : S.B.edgeSet ⊆ E := by
  intro e he
  have h : e ∈ S.A.edgeSet ∪ (S.B.edgeSet ∪ (S.C.edgeSet ∪ S.D.edgeSet)) := Or.inr (Or.inl he)
  rwa [S.cover] at h

theorem arcC_subset (S : CycleQuad G u w z v E) : S.C.edgeSet ⊆ E := by
  intro e he
  have h : e ∈ S.A.edgeSet ∪ (S.B.edgeSet ∪ (S.C.edgeSet ∪ S.D.edgeSet)) := Or.inr (Or.inr (Or.inl he))
  rwa [S.cover] at h

theorem arcD_subset (S : CycleQuad G u w z v E) : S.D.edgeSet ⊆ E := by
  intro e he
  have h : e ∈ S.A.edgeSet ∪ (S.B.edgeSet ∪ (S.C.edgeSet ∪ S.D.edgeSet)) := Or.inr (Or.inr (Or.inr he))
  rwa [S.cover] at h

theorem long_first_arc (S : CycleQuad G u w z v E) (h : G.Adj u w)
    (he : s(u,w) ∉ E) : 2 ≤ S.A.length := by
  by_contra hn
  have hEq : S.A = h.toWalk := Walk.eq_of_length_le_one (by omega) (by simp)
  apply he
  apply S.arcA_subset
  simp [hEq]

/-- The cyclic order agrees with the three-edge path's order. -/
theorem repair_parallel (S : CycleQuad G u w z v E)
    (h₁ : G.Adj u w) (h₂ : G.Adj w z) (h₃ : G.Adj z v)
    (hd : Disjoint E ({s(u,w), s(w,z), s(z,v)} : Set (Sym2 V))) :
    HasPathPairAt G v u (E ∪ {s(u,w), s(w,z), s(z,v)}) := by
  classical
  have hno : s(u,w) ∉ E := fun he => Set.disjoint_left.mp hd he (by simp)
  obtain ⟨a, L, R, hsplit, hau, haw, hL, hR⟩ :=
    path_split_internal S.A S.pathA (S.long_first_arc h₁ hno)
  have hp : (L.append R).IsPath := hsplit ▸ S.pathA
  have hLs : L.support ⊆ S.A.support := by
    rw [hsplit]; exact L.support_subset_support_append_left R
  have hRs : R.support ⊆ S.A.support := by
    rw [hsplit]; exact L.support_subset_support_append_right R
  have hLE : L.edgeSet ⊆ S.A.edgeSet := by
    rw [hsplit, Walk.edgeSet_append]; exact Set.subset_union_left
  have hRE : R.edgeSet ⊆ S.A.edgeSet := by
    rw [hsplit, Walk.edgeSet_append]; exact Set.subset_union_right
  have hLu : u ∈ L.support := L.start_mem_support
  have hRw : w ∈ R.support := R.end_mem_support
  have hLw : w ∉ L.support := by
    intro hw; exact (hp.ne_of_mem_support_of_append haw.symm hw hRw) rfl
  have hRu : u ∉ R.support := by
    intro hu; exact (hp.ne_of_mem_support_of_append hau.symm hLu hu) rfl
  have hAv : v ∉ S.A.support := fun hv => S.disjAC v hv S.C.end_mem_support
  have hBu : u ∉ S.B.support := fun hu => S.neUW (S.interAB u S.A.start_mem_support hu)
  have hBv : v ∉ S.B.support := fun hv => S.disjBD v hv S.D.start_mem_support
  have hDw : w ∉ S.D.support := fun hw => S.disjBD w S.B.start_mem_support hw
  have hCw : w ∉ S.C.support := fun hw => S.neWZ (S.interBC w S.B.start_mem_support hw)
  have hCD : (S.C.append S.D).IsPath :=
    isPath_append_of_support_inter _ _ S.pathC S.pathD S.interCD
  have hB3 : (S.B.concat h₃).IsPath := S.pathB.concat hBv h₃
  have h1B3 : (Walk.cons h₁ (S.B.concat h₃)).IsPath := by
    apply hB3.cons
    simp only [Walk.support_concat, List.mem_append, List.mem_singleton]
    exact fun hh => hh.elim hBu S.neUV
  have h2CD : (Walk.cons h₂ (S.C.append S.D)).IsPath := by
    apply hCD.cons
    rw [Walk.mem_support_append_iff]
    exact fun hh => hh.elim hCw hDw
  have hp₁ : (L.reverse.append (Walk.cons h₁ (S.B.concat h₃))).IsPath := by
    apply isPath_append_of_support_inter _ _ hL.reverse h1B3
    intro x hxL hxT
    have hx : x ∈ L.support := by simpa using hxL
    simp only [Walk.support_cons, List.mem_cons, Walk.support_concat,
      List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hxT
    rcases hxT with hxu | hxB | hxv
    · exact hxu
    · exact (hLw ((S.interAB x (hLs hx) hxB) ▸ hx)).elim
    · exact (hAv (hxv ▸ hLs hx)).elim
  have hp₂ : (R.append (Walk.cons h₂ (S.C.append S.D))).IsPath := by
    apply isPath_append_of_support_inter _ _ hR h2CD
    intro x hxR hxT
    simp only [Walk.support_cons, List.mem_cons, Walk.mem_support_append_iff] at hxT
    rcases hxT with hxw | hxC | hxD
    · exact hxw
    · exact (S.disjAC x (hRs hxR) hxC).elim
    · exact (hRu ((S.interAD x (hRs hxR) hxD) ▸ hxR)).elim
  have hav : a ≠ v := fun hv => hAv (hv ▸ hLs L.end_mem_support)
  have hdLR : Disjoint L.edgeSet R.edgeSet := by
    apply Set.disjoint_left.mpr
    exact (Walk.isTrail_append L R).mp hp.isTrail |>.2.2
  have hdAC : Disjoint S.A.edgeSet S.C.edgeSet :=
    edgeSet_disjoint_of_support_inter _ _ (fun x hx hy => (S.disjAC x hx hy).elim :
      ∀ x, x ∈ S.A.support → x ∈ S.C.support → x = u)
  have hdAD := edgeSet_disjoint_of_support_inter _ _ S.interAD
  have hdAB := edgeSet_disjoint_of_support_inter _ _ S.interAB
  have hdBC := edgeSet_disjoint_of_support_inter _ _ S.interBC
  have hdBD : Disjoint S.B.edgeSet S.D.edgeSet :=
    edgeSet_disjoint_of_support_inter _ _ (fun x hx hy => (S.disjBD x hx hy).elim :
      ∀ x, x ∈ S.B.support → x ∈ S.D.support → x = u)
  refine ⟨a, _, _, hp₁, hp₂, Walk.not_nil_of_ne hav, Walk.not_nil_of_ne hau, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro e he hf
    simp only [Walk.edgeSet_append, Walk.edgeSet_reverse, Walk.edgeSet_cons,
      Walk.edgeSet_concat, Set.mem_union, Set.mem_insert_iff] at he hf
    have hLno : ∀ e ∈ L.edgeSet, e ∉ ({s(u,w), s(w,z), s(z,v)} : Set (Sym2 V)) :=
      fun e he' hf' => Set.disjoint_left.mp hd (S.arcA_subset (hLE he')) hf'
    have hRno : ∀ e ∈ R.edgeSet, e ∉ ({s(u,w), s(w,z), s(z,v)} : Set (Sym2 V)) :=
      fun e he' hf' => Set.disjoint_left.mp hd (S.arcA_subset (hRE he')) hf'
    have hBno : ∀ e ∈ S.B.edgeSet, e ∉ ({s(u,w), s(w,z), s(z,v)} : Set (Sym2 V)) :=
      fun e he' hf' => Set.disjoint_left.mp hd (S.arcB_subset he') hf'
    have hCno : ∀ e ∈ S.C.edgeSet, e ∉ ({s(u,w), s(w,z), s(z,v)} : Set (Sym2 V)) :=
      fun e he' hf' => Set.disjoint_left.mp hd (S.arcC_subset he') hf'
    have hDno : ∀ e ∈ S.D.edgeSet, e ∉ ({s(u,w), s(w,z), s(z,v)} : Set (Sym2 V)) :=
      fun e he' hf' => Set.disjoint_left.mp hd (S.arcD_subset he') hf'
    have h12 : s(u,w) ≠ s(w,z) := by
      intro heq
      rcases Sym2.eq_iff.mp heq with ⟨hh, _⟩ | ⟨hh, _⟩
      · exact S.neUW hh
      · exact S.neUZ hh
    have h32 : s(z,v) ≠ s(w,z) := by
      intro heq
      rcases Sym2.eq_iff.mp heq with ⟨hh, _⟩ | ⟨_, hh⟩
      · exact S.neWZ hh.symm
      · exact S.neWV hh.symm
    rcases he with heL | he1 | he3 | heB <;> rcases hf with hfR | hf2 | hfC | hfD
    · exact Set.disjoint_left.mp hdLR heL hfR
    · exact hLno e heL (by simp [hf2])
    · exact Set.disjoint_left.mp hdAC (hLE heL) hfC
    · exact Set.disjoint_left.mp hdAD (hLE heL) hfD
    · exact hRno e hfR (by simp [he1])
    · exact h12 (he1.symm.trans hf2)
    · exact hCno e hfC (by simp [he1])
    · exact hDno e hfD (by simp [he1])
    · exact hRno e hfR (by simp [he3])
    · exact h32 (he3.symm.trans hf2)
    · exact hCno e hfC (by simp [he3])
    · exact hDno e hfD (by simp [he3])
    · exact Set.disjoint_left.mp hdAB (hRE hfR) heB
    · exact hBno e heB (by simp [hf2])
    · exact Set.disjoint_left.mp hdBC heB hfC
    · exact Set.disjoint_left.mp hdBD heB hfD
  · conv_rhs => rw [← S.cover, hsplit]
    ext e
    simp only [Walk.edgeSet_append, Walk.edgeSet_reverse, Walk.edgeSet_cons,
      Walk.edgeSet_concat, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

/-- The short path reverses the last pair in the cyclic order. -/
theorem repair_crossed (S : CycleQuad G u w z v E)
    (h₁ : G.Adj u w) (h₂ : G.Adj w v) (h₃ : G.Adj v z)
    (hd : Disjoint E ({s(u,w), s(w,v), s(v,z)} : Set (Sym2 V))) :
    HasPathPairAt G z u (E ∪ {s(u,w), s(w,v), s(v,z)}) := by
  classical
  have hno : s(u,w) ∉ E := fun he => Set.disjoint_left.mp hd he (by simp)
  obtain ⟨a, L, R, hsplit, hau, haw, hL, hR⟩ :=
    path_split_internal S.A S.pathA (S.long_first_arc h₁ hno)
  have hp : (L.append R).IsPath := hsplit ▸ S.pathA
  have hLs : L.support ⊆ S.A.support := by
    rw [hsplit]; exact L.support_subset_support_append_left R
  have hRs : R.support ⊆ S.A.support := by
    rw [hsplit]; exact L.support_subset_support_append_right R
  have hLE : L.edgeSet ⊆ S.A.edgeSet := by
    rw [hsplit, Walk.edgeSet_append]; exact Set.subset_union_left
  have hRE : R.edgeSet ⊆ S.A.edgeSet := by
    rw [hsplit, Walk.edgeSet_append]; exact Set.subset_union_right
  have hLw : w ∉ L.support := by
    intro hw; exact (hp.ne_of_mem_support_of_append haw.symm hw R.end_mem_support) rfl
  have hRu : u ∉ R.support := by
    intro hu; exact (hp.ne_of_mem_support_of_append hau.symm L.start_mem_support hu) rfl
  have hAv : v ∉ S.A.support := fun hv => S.disjAC v hv S.C.end_mem_support
  have hAz : z ∉ S.A.support := fun hz => S.disjAC z hz S.C.start_mem_support
  have hBu : u ∉ S.B.support := fun hu => S.neUW (S.interAB u S.A.start_mem_support hu)
  have hBv : v ∉ S.B.support := fun hv => S.disjBD v hv S.D.start_mem_support
  have hCu : u ∉ S.C.support := fun hu => S.disjAC u S.A.start_mem_support hu
  have hCw : w ∉ S.C.support := fun hw => S.neWZ (S.interBC w S.B.start_mem_support hw)
  have hDz : z ∉ S.D.support := fun hz => S.disjBD z S.B.end_mem_support hz
  have h2C : (Walk.cons h₂ S.C.reverse).IsPath := by
    apply S.pathC.reverse.cons
    simpa using hCw
  have h12C : (Walk.cons h₁ (Walk.cons h₂ S.C.reverse)).IsPath := by
    apply h2C.cons
    simp only [Walk.support_cons, List.mem_cons, Walk.support_reverse, List.mem_reverse]
    exact fun hh => hh.elim S.neUW hCu
  have h3D : (Walk.cons h₃.symm S.D).IsPath := S.pathD.cons hDz
  have hB3D : (S.B.append (Walk.cons h₃.symm S.D)).IsPath := by
    apply isPath_append_of_support_inter _ _ S.pathB h3D
    intro x hxB hxT
    simp only [Walk.support_cons, List.mem_cons] at hxT
    rcases hxT with hxz | hxD
    · exact hxz
    · exact (S.disjBD x hxB hxD).elim
  have hp₁ : (L.reverse.append (Walk.cons h₁ (Walk.cons h₂ S.C.reverse))).IsPath := by
    apply isPath_append_of_support_inter _ _ hL.reverse h12C
    intro x hxL hxT
    have hx : x ∈ L.support := by simpa using hxL
    simp only [Walk.support_cons, List.mem_cons, Walk.support_reverse, List.mem_reverse] at hxT
    rcases hxT with hxu | hxw | hxC
    · exact hxu
    · exact (hLw (hxw ▸ hx)).elim
    · exact (S.disjAC x (hLs hx) hxC).elim
  have hp₂ : (R.append (S.B.append (Walk.cons h₃.symm S.D))).IsPath := by
    apply isPath_append_of_support_inter _ _ hR hB3D
    intro x hxR hxT
    simp only [Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons] at hxT
    rcases hxT with hxB | hxz | hxD
    · exact S.interAB x (hRs hxR) hxB
    · exact (hAz (hxz ▸ hRs hxR)).elim
    · exact (hRu ((S.interAD x (hRs hxR) hxD) ▸ hxR)).elim
  have haz : a ≠ z := fun hz => hAz (hz ▸ hLs L.end_mem_support)
  have hdLR : Disjoint L.edgeSet R.edgeSet := by
    apply Set.disjoint_left.mpr
    exact (Walk.isTrail_append L R).mp hp.isTrail |>.2.2
  have hdAC : Disjoint S.A.edgeSet S.C.edgeSet :=
    edgeSet_disjoint_of_support_inter _ _ (fun x hx hy => (S.disjAC x hx hy).elim :
      ∀ x, x ∈ S.A.support → x ∈ S.C.support → x = u)
  have hdAD := edgeSet_disjoint_of_support_inter _ _ S.interAD
  have hdAB := edgeSet_disjoint_of_support_inter _ _ S.interAB
  have hdBC := edgeSet_disjoint_of_support_inter _ _ S.interBC
  have hdCD := edgeSet_disjoint_of_support_inter _ _ S.interCD
  have hLno : ∀ e ∈ L.edgeSet, e ∉ ({s(u,w), s(w,v), s(v,z)} : Set (Sym2 V)) :=
    fun e he hf => Set.disjoint_left.mp hd (S.arcA_subset (hLE he)) hf
  have hRno : ∀ e ∈ R.edgeSet, e ∉ ({s(u,w), s(w,v), s(v,z)} : Set (Sym2 V)) :=
    fun e he hf => Set.disjoint_left.mp hd (S.arcA_subset (hRE he)) hf
  have hBno : ∀ e ∈ S.B.edgeSet, e ∉ ({s(u,w), s(w,v), s(v,z)} : Set (Sym2 V)) :=
    fun e he hf => Set.disjoint_left.mp hd (S.arcB_subset he) hf
  have hCno : ∀ e ∈ S.C.edgeSet, e ∉ ({s(u,w), s(w,v), s(v,z)} : Set (Sym2 V)) :=
    fun e he hf => Set.disjoint_left.mp hd (S.arcC_subset he) hf
  have hDno : ∀ e ∈ S.D.edgeSet, e ∉ ({s(u,w), s(w,v), s(v,z)} : Set (Sym2 V)) :=
    fun e he hf => Set.disjoint_left.mp hd (S.arcD_subset he) hf
  have h13 : s(u,w) ≠ s(z,v) := by
    intro heq
    rcases Sym2.eq_iff.mp heq with ⟨hh, _⟩ | ⟨hh, _⟩
    · exact S.neUZ hh
    · exact S.neUV hh
  have h23 : s(w,v) ≠ s(z,v) := by
    intro heq
    rcases Sym2.eq_iff.mp heq with ⟨hh, _⟩ | ⟨hh, _⟩
    · exact S.neWZ hh
    · exact S.neWV hh
  refine ⟨a, _, _, hp₁, hp₂, Walk.not_nil_of_ne haz, Walk.not_nil_of_ne hau, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro e he hf
    simp only [Walk.edgeSet_append, Walk.edgeSet_reverse, Walk.edgeSet_cons,
      Set.mem_union, Set.mem_insert_iff] at he hf
    rcases he with heL | he1 | he2 | heC <;> rcases hf with hfR | hfB | hf3 | hfD
    · exact Set.disjoint_left.mp hdLR heL hfR
    · exact Set.disjoint_left.mp hdAB (hLE heL) hfB
    · exact hLno e heL (by simp [hf3, Sym2.eq_swap])
    · exact Set.disjoint_left.mp hdAD (hLE heL) hfD
    · exact hRno e hfR (by simp [he1])
    · exact hBno e hfB (by simp [he1])
    · exact h13 (he1.symm.trans hf3)
    · exact hDno e hfD (by simp [he1])
    · exact hRno e hfR (by simp [he2])
    · exact hBno e hfB (by simp [he2])
    · exact h23 (he2.symm.trans hf3)
    · exact hDno e hfD (by simp [he2])
    · exact Set.disjoint_left.mp hdAC (hRE hfR) heC
    · exact Set.disjoint_left.mp hdBC hfB heC
    · exact hCno e heC (by simp [hf3, Sym2.eq_swap])
    · exact Set.disjoint_left.mp hdCD heC hfD
  · conv_rhs => rw [← S.cover, hsplit]
    ext e
    simp only [Walk.edgeSet_append, Walk.edgeSet_reverse, Walk.edgeSet_cons,
      Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [show s(z,v) = s(v,z) from Sym2.eq_swap]
    tauto

/-- The middle short-path edge is cyclic, and the outer edges cross the cycle. -/
theorem repair_middle (S : CycleQuad G u w z v E)
    (h₁ : G.Adj v w) (h₂ : G.Adj w u) (h₃ : G.Adj u z)
    (hd : Disjoint E ({s(v,w), s(w,u), s(u,z)} : Set (Sym2 V))) :
    HasPathPairAt G z v (E ∪ {s(v,w), s(w,u), s(u,z)}) := by
  classical
  have hno : s(u,w) ∉ E := fun he => Set.disjoint_left.mp hd he (by simp [Sym2.eq_swap])
  obtain ⟨a, L, R, hsplit, hau, haw, hL, hR⟩ :=
    path_split_internal S.A S.pathA (S.long_first_arc h₂.symm hno)
  have hp : (L.append R).IsPath := hsplit ▸ S.pathA
  have hLs : L.support ⊆ S.A.support := by
    rw [hsplit]; exact L.support_subset_support_append_left R
  have hRs : R.support ⊆ S.A.support := by
    rw [hsplit]; exact L.support_subset_support_append_right R
  have hLE : L.edgeSet ⊆ S.A.edgeSet := by
    rw [hsplit, Walk.edgeSet_append]; exact Set.subset_union_left
  have hRE : R.edgeSet ⊆ S.A.edgeSet := by
    rw [hsplit, Walk.edgeSet_append]; exact Set.subset_union_right
  have hLw : w ∉ L.support := by
    intro hw; exact (hp.ne_of_mem_support_of_append haw.symm hw R.end_mem_support) rfl
  have hRu : u ∉ R.support := by
    intro hu; exact (hp.ne_of_mem_support_of_append hau.symm L.start_mem_support hu) rfl
  have hAv : v ∉ S.A.support := fun hv => S.disjAC v hv S.C.end_mem_support
  have hAz : z ∉ S.A.support := fun hz => S.disjAC z hz S.C.start_mem_support
  have hBv : v ∉ S.B.support := fun hv => S.disjBD v hv S.D.start_mem_support
  have hCu : u ∉ S.C.support := fun hu => S.disjAC u S.A.start_mem_support hu
  have hCw : w ∉ S.C.support := fun hw => S.neWZ (S.interBC w S.B.start_mem_support hw)
  have h1B : (Walk.cons h₁ S.B).IsPath := S.pathB.cons hBv
  have hD1B : (S.D.reverse.append (Walk.cons h₁ S.B)).IsPath := by
    apply isPath_append_of_support_inter _ _ S.pathD.reverse h1B
    intro x hxD hxT
    have hxD' : x ∈ S.D.support := by simpa using hxD
    simp only [Walk.support_cons, List.mem_cons] at hxT
    rcases hxT with hxv | hxB
    · exact hxv
    · exact (S.disjBD x hxB hxD').elim
  have h3C : (Walk.cons h₃ S.C).IsPath := S.pathC.cons hCu
  have h23C : (Walk.cons h₂ (Walk.cons h₃ S.C)).IsPath := by
    apply h3C.cons
    simp only [Walk.support_cons, List.mem_cons]
    exact fun hh => hh.elim S.neUW.symm hCw
  have hp₁ : (L.reverse.append (S.D.reverse.append (Walk.cons h₁ S.B))).IsPath := by
    apply isPath_append_of_support_inter _ _ hL.reverse hD1B
    intro x hxL hxT
    have hx : x ∈ L.support := by simpa using hxL
    simp only [Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons,
      Walk.support_reverse, List.mem_reverse] at hxT
    rcases hxT with hxD | hxv | hxB
    · exact S.interAD x (hLs hx) hxD
    · exact (hAv (hxv ▸ hLs hx)).elim
    · exact (hLw ((S.interAB x (hLs hx) hxB) ▸ hx)).elim
  have hp₂ : (R.append (Walk.cons h₂ (Walk.cons h₃ S.C))).IsPath := by
    apply isPath_append_of_support_inter _ _ hR h23C
    intro x hxR hxT
    simp only [Walk.support_cons, List.mem_cons] at hxT
    rcases hxT with hxw | hxu | hxC
    · exact hxw
    · exact (hRu (hxu ▸ hxR)).elim
    · exact (S.disjAC x (hRs hxR) hxC).elim
  have haz : a ≠ z := fun hz => hAz (hz ▸ hLs L.end_mem_support)
  have hav : a ≠ v := fun hv => hAv (hv ▸ hLs L.end_mem_support)
  have hdLR : Disjoint L.edgeSet R.edgeSet := by
    apply Set.disjoint_left.mpr
    exact (Walk.isTrail_append L R).mp hp.isTrail |>.2.2
  have hdAC : Disjoint S.A.edgeSet S.C.edgeSet :=
    edgeSet_disjoint_of_support_inter _ _ (fun x hx hy => (S.disjAC x hx hy).elim :
      ∀ x, x ∈ S.A.support → x ∈ S.C.support → x = u)
  have hdAD := edgeSet_disjoint_of_support_inter _ _ S.interAD
  have hdAB := edgeSet_disjoint_of_support_inter _ _ S.interAB
  have hdBC := edgeSet_disjoint_of_support_inter _ _ S.interBC
  have hdCD := edgeSet_disjoint_of_support_inter _ _ S.interCD
  have hLno : ∀ e ∈ L.edgeSet, e ∉ ({s(v,w), s(w,u), s(u,z)} : Set (Sym2 V)) :=
    fun e he hf => Set.disjoint_left.mp hd (S.arcA_subset (hLE he)) hf
  have hRno : ∀ e ∈ R.edgeSet, e ∉ ({s(v,w), s(w,u), s(u,z)} : Set (Sym2 V)) :=
    fun e he hf => Set.disjoint_left.mp hd (S.arcA_subset (hRE he)) hf
  have hBno : ∀ e ∈ S.B.edgeSet, e ∉ ({s(v,w), s(w,u), s(u,z)} : Set (Sym2 V)) :=
    fun e he hf => Set.disjoint_left.mp hd (S.arcB_subset he) hf
  have hCno : ∀ e ∈ S.C.edgeSet, e ∉ ({s(v,w), s(w,u), s(u,z)} : Set (Sym2 V)) :=
    fun e he hf => Set.disjoint_left.mp hd (S.arcC_subset he) hf
  have hDno : ∀ e ∈ S.D.edgeSet, e ∉ ({s(v,w), s(w,u), s(u,z)} : Set (Sym2 V)) :=
    fun e he hf => Set.disjoint_left.mp hd (S.arcD_subset he) hf
  have h12 : s(v,w) ≠ s(w,u) := by
    intro heq
    rcases Sym2.eq_iff.mp heq with ⟨hh, _⟩ | ⟨hh, _⟩
    · exact S.neWV hh.symm
    · exact S.neUV hh.symm
  have h13 : s(v,w) ≠ s(u,z) := by
    intro heq
    rcases Sym2.eq_iff.mp heq with ⟨hh, _⟩ | ⟨hh, _⟩
    · exact S.neUV hh.symm
    · exact S.neZV hh.symm
  refine ⟨a, _, _, hp₁, hp₂, Walk.not_nil_of_ne haz, Walk.not_nil_of_ne hav, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro e he hf
    simp only [Walk.edgeSet_append, Walk.edgeSet_reverse, Walk.edgeSet_cons,
      Set.mem_union, Set.mem_insert_iff] at he hf
    rcases he with heL | heD | he1 | heB <;> rcases hf with hfR | hf2 | hf3 | hfC
    · exact Set.disjoint_left.mp hdLR heL hfR
    · exact hLno e heL (by simp [hf2])
    · exact hLno e heL (by simp [hf3])
    · exact Set.disjoint_left.mp hdAC (hLE heL) hfC
    · exact Set.disjoint_left.mp hdAD (hRE hfR) heD
    · exact hDno e heD (by simp [hf2])
    · exact hDno e heD (by simp [hf3])
    · exact Set.disjoint_left.mp hdCD hfC heD
    · exact hRno e hfR (by simp [he1])
    · exact h12 (he1.symm.trans hf2)
    · exact h13 (he1.symm.trans hf3)
    · exact hCno e hfC (by simp [he1])
    · exact Set.disjoint_left.mp hdAB (hRE hfR) heB
    · exact hBno e heB (by simp [hf2])
    · exact hBno e heB (by simp [hf3])
    · exact Set.disjoint_left.mp hdBC heB hfC
  · conv_rhs => rw [← S.cover, hsplit]
    ext e
    simp only [Walk.edgeSet_append, Walk.edgeSet_reverse, Walk.edgeSet_cons,
      Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

/-- Rotate the displayed cyclic order without changing any edge. -/
def rotate (S : CycleQuad G u w z v E) : CycleQuad G w z v u E where
  A := S.B
  B := S.C
  C := S.D
  D := S.A
  pathA := S.pathB
  pathB := S.pathC
  pathC := S.pathD
  pathD := S.pathA
  neUW := S.neWZ
  neUZ := S.neWV
  neUV := S.neUW.symm
  neWZ := S.neZV
  neWV := S.neUZ.symm
  neZV := S.neUV.symm
  interAB := S.interBC
  disjAC := S.disjBD
  interAD := fun x hx hy => S.interAB x hy hx
  interBC := S.interCD
  disjBD := fun x hx hy => S.disjAC x hy hx
  interCD := fun x hx hy => S.interAD x hy hx
  cover := by
    calc
      _ = S.A.edgeSet ∪ (S.B.edgeSet ∪ (S.C.edgeSet ∪ S.D.edgeSet)) := by
        ext e; simp only [Set.mem_union]; tauto
      _ = E := S.cover

end CycleQuad

/-- Split the middle of three already extracted cycle arcs at a fourth vertex. -/
theorem cycleQuad_of_split_middle {u w z v : V} {E : Set (Sym2 V)}
    (A : G.Walk u w) (B : G.Walk w v) (D : G.Walk v u)
    (hA : A.IsPath) (hB : B.IsPath) (hD : D.IsPath)
    (huW : u ≠ w) (huZ : u ≠ z) (huV : u ≠ v)
    (hwZ : w ≠ z) (hwV : w ≠ v) (hzV : z ≠ v)
    (hmAB : ∀ x, x ∈ A.support → x ∈ B.support → x = w)
    (hmAD : ∀ x, x ∈ A.support → x ∈ D.support → x = u)
    (hmBD : ∀ x, x ∈ B.support → x ∈ D.support → x = v)
    (hcover : A.edgeSet ∪ (B.edgeSet ∪ D.edgeSet) = E)
    (hz : z ∈ B.support) : Nonempty (CycleQuad G u w z v E) := by
  classical
  let L := B.takeUntil z hz
  let R := B.dropUntil z hz
  have hsplit : L.append R = B := B.take_spec hz
  have hp : (L.append R).IsPath := hsplit ▸ hB
  have hLs : L.support ⊆ B.support := B.support_takeUntil_subset_support hz
  have hRs : R.support ⊆ B.support := B.support_dropUntil_subset_support hz
  have hRw : w ∉ R.support := by
    intro hw
    exact (hp.ne_of_mem_support_of_append hwZ L.start_mem_support hw) rfl
  have hLv : v ∉ L.support := by
    intro hv
    exact (hp.ne_of_mem_support_of_append hzV.symm hv R.end_mem_support) rfl
  refine ⟨{
    A := A, B := L, C := R, D := D
    pathA := hA, pathB := hB.takeUntil hz, pathC := hB.dropUntil hz, pathD := hD
    neUW := huW, neUZ := huZ, neUV := huV
    neWZ := hwZ, neWV := hwV, neZV := hzV
    interAB := fun x hx hy => hmAB x hx (hLs hy)
    disjAC := ?_
    interAD := hmAD
    interBC := fun _ hx hy => isPath_append_support_inter L R hp hx hy
    disjBD := ?_
    interCD := fun x hx hy => hmBD x (hRs hx) hy
    cover := ?_ }⟩
  · intro x hx hy
    exact hRw ((hmAB x hx (hRs hy)) ▸ hy)
  · intro x hx hy
    exact hLv ((hmBD x (hLs hx) hy) ▸ hx)
  · calc
      A.edgeSet ∪ (L.edgeSet ∪ (R.edgeSet ∪ D.edgeSet)) =
          A.edgeSet ∪ ((L.append R).edgeSet ∪ D.edgeSet) := by
        rw [Walk.edgeSet_append]; ext e; simp only [Set.mem_union]; tauto
      _ = E := by rw [hsplit, hcover]

/-- Four distinct cycle vertices have exactly one of the three unoriented
cyclic orders relevant to a three-edge path. The witnesses use actual arcs. -/
theorem cycle_four_arcs {u w z v : V} (c : G.Walk u u) (hc : c.IsCycle)
    (hw : w ∈ c.support) (hz : z ∈ c.support) (hv : v ∈ c.support)
    (huw : u ≠ w) (huz : u ≠ z) (huv : u ≠ v)
    (hwz : w ≠ z) (hwv : w ≠ v) (hzv : z ≠ v) :
    Nonempty (CycleQuad G u w z v c.edgeSet) ∨
      Nonempty (CycleQuad G u w v z c.edgeSet) ∨
      Nonempty (CycleQuad G u z w v c.edgeSet) := by
  obtain ⟨A, B, D, hA, hB, hD, _, _, _, hE, hmAB, hmAD, hmBD⟩ :=
    cycle_three_arcs c hc hw hv huw huv.symm hwv.symm
  have hzABD : z ∈ A.support ∨ z ∈ B.support ∨ z ∈ D.support := by
    obtain ⟨e, he, hze⟩ :=
      (Walk.mem_support_iff_exists_mem_edges_of_not_nil hc.not_nil).mp hz
    change e ∈ c.edgeSet at he
    rw [← hE] at he
    rcases he with he | he | he
    · exact Or.inl (A.mem_support_of_mem_edges he hze)
    · exact Or.inr (Or.inl (B.mem_support_of_mem_edges he hze))
    · exact Or.inr (Or.inr (D.mem_support_of_mem_edges he hze))
  rcases hzABD with hzA | hzB | hzD
  · have hE' : D.edgeSet ∪ (A.edgeSet ∪ B.edgeSet) = c.edgeSet := by
      rw [← hE]; ext e; simp only [Set.mem_union]; tauto
    obtain ⟨S⟩ := cycleQuad_of_split_middle D A B hD hA hB
      huv.symm hzv.symm hwv.symm huz huw hwz.symm
      (fun x hx hy => hmAD x hy hx) (fun x hx hy => hmBD x hy hx)
      hmAB hE' hzA
    exact Or.inr (Or.inr ⟨S.rotate⟩)
  · exact Or.inl (cycleQuad_of_split_middle A B D hA hB hD
      huw huz huv hwz hwv hzv hmAB hmAD hmBD hE hzB)
  · have hE' : B.edgeSet ∪ (D.edgeSet ∪ A.edgeSet) = c.edgeSet := by
      rw [← hE]; ext e; simp only [Set.mem_union]; tauto
    obtain ⟨S⟩ := cycleQuad_of_split_middle B D A hB hD hA
      hwv hwz huw.symm hzv.symm huv.symm huz.symm
      hmBD (fun x hx hy => hmAB x hy hx) (fun x hx hy => hmAD x hy hx) hE' hzD
    exact Or.inr (Or.inl ⟨S.rotate.rotate.rotate⟩)
/-- A cycle together with a disjoint three-edge simple path whose four vertices
are all on the cycle has an exact two-path repair, exposing the input endpoints. -/
theorem pathPairAt_of_path_cycle_four_vertices {u w z v : V} {E : Set (Sym2 V)}
    (c : G.Walk u u) (h₁ : G.Adj u w) (h₂ : G.Adj w z) (h₃ : G.Adj z v)
    (hc : c.IsCycle)
    (hp : (Walk.cons h₁ (Walk.cons h₂ h₃.toWalk)).IsPath)
    (hw : w ∈ c.support) (hz : z ∈ c.support) (hv : v ∈ c.support)
    (hd : Disjoint c.edgeSet (Walk.cons h₁ (Walk.cons h₂ h₃.toWalk)).edgeSet)
    (hcover : c.edgeSet ∪ (Walk.cons h₁ (Walk.cons h₂ h₃.toWalk)).edgeSet = E) :
    HasPathPairAt G v u E := by
  have hP₁ := (Walk.cons_isPath_iff h₁ (Walk.cons h₂ h₃.toWalk)).mp hp
  have hP₂ := (Walk.cons_isPath_iff h₂ h₃.toWalk).mp hP₁.1
  have huz : u ≠ z := fun he => hP₁.2 (by simp [he])
  have huv : u ≠ v := fun he => hP₁.2 (by simp [he])
  have hwv : w ≠ v := fun he => hP₂.2 (by simp [he])
  have hPE : (Walk.cons h₁ (Walk.cons h₂ h₃.toWalk)).edgeSet =
      ({s(u,w), s(w,z), s(z,v)} : Set (Sym2 V)) := by
    ext e
    simp
  have hD : Disjoint c.edgeSet ({s(u,w), s(w,z), s(z,v)} : Set (Sym2 V)) :=
    hPE ▸ hd
  have hC : c.edgeSet ∪ ({s(u,w), s(w,z), s(z,v)} : Set (Sym2 V)) = E := by
    simpa only [hPE] using hcover
  suffices h : HasPathPairAt G v u
      (c.edgeSet ∪ ({s(u,w), s(w,z), s(z,v)} : Set (Sym2 V))) by
    exact hC ▸ h
  rcases cycle_four_arcs c hc hw hz hv h₁.ne huz huv h₂.ne hwv h₃.ne with
    ⟨S⟩ | ⟨S⟩ | ⟨S⟩
  · obtain ⟨T⟩ := S
    exact T.repair_parallel h₁ h₂ h₃ hD
  · obtain ⟨T⟩ := S
    exact T.repair_crossed h₁ h₂ h₃ hD
  · obtain ⟨T⟩ := S
    exact T.rotate.repair_middle h₁ h₂ h₃ hD

theorem hasPathPartition_two_of_path_cycle_four_vertices {u w z v : V}
    (c : G.Walk u u) (h₁ : G.Adj u w) (h₂ : G.Adj w z) (h₃ : G.Adj z v)
    (hc : c.IsCycle)
    (hp : (Walk.cons h₁ (Walk.cons h₂ h₃.toWalk)).IsPath)
    (hw : w ∈ c.support) (hz : z ∈ c.support) (hv : v ∈ c.support)
    (hd : Disjoint c.edgeSet (Walk.cons h₁ (Walk.cons h₂ h₃.toWalk)).edgeSet)
    (hcover : c.edgeSet ∪ (Walk.cons h₁ (Walk.cons h₂ h₃.toWalk)).edgeSet = G.edgeSet) :
    HasPathPartition G 2 :=
  (pathPairAt_of_path_cycle_four_vertices c h₁ h₂ h₃ hc hp hw hz hv hd hcover).toPathPartition

end Erdos583
end Source18_Erdos583_ShortPathFour
/- END Erdos583.ShortPathFour -/

/- BEGIN Erdos583.ShortPathBase; source SHA256 de088f4b8c7bba36cd69526bab73a809ef144922241e2f5e60caddac63ec449b -/
section Source19_Erdos583_ShortPathBase


/-! The complete cycle plus at most three edges repair, assembled from the
proved intersection constructions. -/
namespace Erdos583
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

theorem walk_rotate_edgeSet [DecidableEq V] {r u : V} (c : G.Walk r r)
    (hu : u ∈ c.support) : (c.rotate u hu).edgeSet = c.edgeSet := by
  ext e
  exact (c.rotate_edges u hu).perm.mem_iff

/-- The full bounded-length base when both path endpoints lie on the cycle. -/
theorem pathPairAt_short_cycle_endpoints {u v : V}
    (c : G.Walk u u) (P : G.Walk u v) (hc : c.IsCycle) (hp : P.IsPath)
    (hlen : P.length ≤ 3) (hv : v ∈ c.support)
    (hd : Disjoint c.edgeSet P.edgeSet) :
    HasPathPairAt G v u (c.edgeSet ∪ P.edgeSet) := by
  classical
  cases P with
  | nil =>
    apply pathPairAt_of_path_cycle_one_intersection Walk.nil c hp hc
      (by simp) (by intro x hx _; simpa using hx)
    simp
  | @cons u w v h₁ Q =>
    cases Q with
    | nil =>
      apply pathPairAt_of_path_cycle_two_endpoints c h₁.toWalk hc hp h₁.ne hv
        (by intro x _ hx; simpa using hx) hd rfl
    | @cons w z v h₂ R =>
      have hP₁ := (Walk.cons_isPath_iff h₁ (Walk.cons h₂ R)).mp hp
      have hvu : v ≠ u := by
        intro he
        exact hP₁.2 (he ▸ (Walk.cons h₂ R).end_mem_support)
      cases R with
      | nil =>
        by_cases hw : w ∈ c.support
        · apply pathPairAt_of_path_cycle_three_vertices c h₁ h₂.toWalk hc hp hw hv
            hvu h₂.ne.symm (by intro x _ hx; simpa using hx) hd.symm rfl
        · apply pathPairAt_of_path_cycle_two_endpoints c (Walk.cons h₁ h₂.toWalk)
            hc hp hvu.symm hv _ hd rfl
          intro x hxc hx
          simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hx
          rcases hx with hxu | hxw | hxv
          · exact Or.inl hxu
          · exact (hw (hxw ▸ hxc)).elim
          · exact Or.inr hxv
      | @cons z t v h₃ T =>
        cases T with
        | @cons t s v h₄ U =>
          simp only [Walk.length_cons] at hlen
          omega
        | nil =>
          have hP₂ := (Walk.cons_isPath_iff h₂ h₃.toWalk).mp hP₁.1
          have hvw : v ≠ w := by
            intro he
            exact hP₂.2 (he ▸ h₃.toWalk.end_mem_support)
          by_cases hw : w ∈ c.support
          · by_cases hz : z ∈ c.support
            · exact pathPairAt_of_path_cycle_four_vertices c h₁ h₂ h₃ hc hp hw hz hv hd rfl
            · apply pathPairAt_of_path_cycle_three_vertices c h₁
                (Walk.cons h₂ h₃.toWalk) hc hp hw hv hvu hvw _ hd.symm rfl
              intro x hxc hx
              simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
                List.not_mem_nil, or_false] at hx
              rcases hx with hxw | hxz | hxt
              · exact Or.inl hxw
              · exact (hz (hxz ▸ hxc)).elim
              · exact Or.inr hxt
          · by_cases hz : z ∈ c.support
            · let c' := c.rotate v hv
              have hc' : c'.IsCycle := hc.rotate hv
              have hEc' : c'.edgeSet = c.edgeSet := walk_rotate_edgeSet c hv
              have hrev : (Walk.cons h₁ (Walk.cons h₂ h₃.toWalk)).reverse =
                  Walk.cons h₃.symm (Walk.cons h₂.symm h₁.symm.toWalk) := by
                simp [Walk.reverse_cons]
              have hp' : (Walk.cons h₃.symm (Walk.cons h₂.symm h₁.symm.toWalk)).IsPath := by
                rw [← hrev]; exact hp.reverse
              have hu' : u ∈ c'.support := by simp [c']
              have hz' : z ∈ c'.support := by simpa [c'] using hz
              have hdu : Disjoint (Walk.cons h₃.symm
                  (Walk.cons h₂.symm h₁.symm.toWalk)).edgeSet c'.edgeSet := by
                rw [← hrev, Walk.edgeSet_reverse, hEc']
                exact hd.symm
              have hcov : c'.edgeSet ∪ (Walk.cons h₃.symm
                  (Walk.cons h₂.symm h₁.symm.toWalk)).edgeSet =
                  c.edgeSet ∪ (Walk.cons h₁ (Walk.cons h₂ h₃.toWalk)).edgeSet := by
                rw [← hrev, Walk.edgeSet_reverse, hEc']
              have huz : u ≠ z := by
                intro he
                exact hP₁.2 (by simp [he])
              apply HasPathPairAt.swap
              apply pathPairAt_of_path_cycle_three_vertices c' h₃.symm
                (Walk.cons h₂.symm h₁.symm.toWalk) hc' hp' hz' hu'
                hvu.symm huz _ hdu hcov
              intro x hxc hx
              have hxc' : x ∈ c.support := by simpa [c'] using hxc
              simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
                List.not_mem_nil, or_false] at hx
              rcases hx with hxz | hxw | hxu
              · exact Or.inl hxz
              · exact (hw (hxw ▸ hxc')).elim
              · exact Or.inr hxu
            · apply pathPairAt_of_path_cycle_two_endpoints c
                (Walk.cons h₁ (Walk.cons h₂ h₃.toWalk)) hc hp hvu.symm hv _ hd rfl
              intro x hxc hx
              simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
                List.not_mem_nil, or_false] at hx
              rcases hx with hxu | hxw | hxz | hxt
              · exact Or.inl hxu
              · exact (hw (hxw ▸ hxc)).elim
              · exact (hz (hxz ▸ hxc)).elim
              · exact Or.inr hxt

/-- Restore one exterior endpoint edge using the retained endpoint exposure.
The removed vertex is outside both the residual path and the cycle. -/
theorem pathPairAt_prepend_outside {r u w v : V}
    (c : G.Walk r r) (h : G.Adj u w) (Q : G.Walk w v)
    (hp : (Walk.cons h Q).IsPath) (hu : u ∉ c.support)
    (hpair : HasPathPairAt G v w (c.edgeSet ∪ Q.edgeSet)) :
    HasPathPairAt G v u (c.edgeSet ∪ (Walk.cons h Q).edgeSet) := by
  have huQ := (Walk.cons_isPath_iff h Q).mp hp |>.2
  have hnew := hpair.attach_tails (Walk.nil : G.Walk v v) h.symm.toWalk
    Walk.IsPath.nil h.symm.isPath_toWalk
    (by intro x hx _ _ _; simpa using hx)
    (by
      intro x hx e he hxe
      have hx' : x = w ∨ x = u := by simpa using hx
      rcases hx' with hxw | hxu
      · exact hxw
      · subst x
        rcases he with heC | heQ
        · exact (hu (c.mem_support_of_mem_edges heC hxe)).elim
        · exact (huQ (Q.mem_support_of_mem_edges heQ hxe)).elim)
    (by simp)
  have hE : (c.edgeSet ∪ Q.edgeSet) ∪
      ((Walk.nil : G.Walk v v).edgeSet ∪ h.symm.toWalk.edgeSet) =
      c.edgeSet ∪ (Walk.cons h Q).edgeSet := by
    ext e
    simp only [Adj.toWalk, Walk.edgeSet_nil, Walk.edgeSet_cons,
      Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      false_or]
    rw [show s(w,u) = s(u,w) from Sym2.eq_swap]
    tauto
  exact hE ▸ hnew

/-- Full short-path/cycle base. There is no restriction on other ambient edges,
on the cycle root, or on which path vertices meet the cycle. -/
theorem pathPairAt_of_short_path_cycle {r u v : V}
    (c : G.Walk r r) (P : G.Walk u v) (hc : c.IsCycle) (hp : P.IsPath)
    (hlen : P.length ≤ 3) (hd : Disjoint c.edgeSet P.edgeSet)
    (hmeet : ∃ x, x ∈ P.support ∧ x ∈ c.support) :
    HasPathPairAt G v u (c.edgeSet ∪ P.edgeSet) := by
  classical
  suffices hall : ∀ n, ∀ (u v : V) (P : G.Walk u v), P.length = n →
      P.IsPath → P.length ≤ 3 → Disjoint c.edgeSet P.edgeSet →
      (∃ x, x ∈ P.support ∧ x ∈ c.support) →
      HasPathPairAt G v u (c.edgeSet ∪ P.edgeSet) by
    exact hall P.length u v P rfl hp hlen hd hmeet
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hoff : ∀ (a b : V) (Q : G.Walk a b), Q.length = n →
        Q.IsPath → Q.length ≤ 3 → Disjoint c.edgeSet Q.edgeSet →
        (∃ x, x ∈ Q.support ∧ x ∈ c.support) → a ∉ c.support →
        HasPathPairAt G b a (c.edgeSet ∪ Q.edgeSet) := by
      intro a b Q hqn hQ hlenQ hdQ hmeetQ ha
      cases Q with
      | nil =>
        obtain ⟨x, hx, hxc⟩ := hmeetQ
        have hxa : x = a := by simpa using hx
        exact (ha (hxa ▸ hxc)).elim
      | @cons a w b hab R =>
        have hRp := (Walk.cons_isPath_iff hab R).mp hQ |>.1
        have hRlen : R.length < n := by simp only [Walk.length_cons] at hqn; omega
        have hRbound : R.length ≤ 3 := by simp only [Walk.length_cons] at hlenQ; omega
        have hRd : Disjoint c.edgeSet R.edgeSet := hdQ.mono_right (by
          intro e he; simp [he])
        have hRm : ∃ x, x ∈ R.support ∧ x ∈ c.support := by
          obtain ⟨x, hx, hxc⟩ := hmeetQ
          simp only [Walk.support_cons, List.mem_cons] at hx
          rcases hx with hxa | hxR
          · exact (ha (hxa ▸ hxc)).elim
          · exact ⟨x, hxR, hxc⟩
        exact pathPairAt_prepend_outside c hab R hQ ha
          (ih R.length hRlen w b R rfl hRp hRbound hRd hRm)
    intro u v P hn hp hlen hd hmeet
    by_cases hu : u ∈ c.support
    · by_cases hv : v ∈ c.support
      · let c' := c.rotate u hu
        have hEc' : c'.edgeSet = c.edgeSet := walk_rotate_edgeSet c hu
        have hv' : v ∈ c'.support := by simpa [c'] using hv
        have hd' : Disjoint c'.edgeSet P.edgeSet := hEc'.symm ▸ hd
        have hpair := pathPairAt_short_cycle_endpoints c' P (hc.rotate hu) hp hlen hv' hd'
        simpa only [hEc'] using hpair
      · have hrevlen : P.reverse.length = n := by simpa using hn
        have hrevbound : P.reverse.length ≤ 3 := by simpa using hlen
        have hrevd : Disjoint c.edgeSet P.reverse.edgeSet := by simpa using hd
        have hrevm : ∃ x, x ∈ P.reverse.support ∧ x ∈ c.support := by
          simpa using hmeet
        have hpair := hoff v u P.reverse hrevlen hp.reverse hrevbound hrevd hrevm hv
        simpa only [Walk.edgeSet_reverse] using hpair.swap
    · exact hoff u v P hn hp hlen hd hmeet hu

/-- Ordinary partition version of the full short-path/cycle base. -/
theorem hasPathPartition_two_of_short_path_cycle {r u v : V}
    (c : G.Walk r r) (P : G.Walk u v) (hc : c.IsCycle) (hp : P.IsPath)
    (hlen : P.length ≤ 3) (hd : Disjoint c.edgeSet P.edgeSet)
    (hmeet : ∃ x, x ∈ P.support ∧ x ∈ c.support)
    (hcover : c.edgeSet ∪ P.edgeSet = G.edgeSet) : HasPathPartition G 2 := by
  have hh := pathPairAt_of_short_path_cycle c P hc hp hlen hd hmeet
  exact (hcover ▸ hh).toPathPartition

end Erdos583
end Source19_Erdos583_ShortPathBase
/- END Erdos583.ShortPathBase -/

/- BEGIN Erdos583.EdgePathPartition; source SHA256 433c3e2035f786a0dfaf8f8b15ebe298fd684f4b51119f9d0172bd76ce403315 -/
section Source20_Erdos583_EdgePathPartition


/-! Finite path partitions of a specified original edge subset. -/
namespace Erdos583
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

def HasEdgePathPartition (G : SimpleGraph V) (E : Set (Sym2 V)) (q : ℕ) : Prop :=
  ∃ D : Finset G.Subgraph,
    (∀ H ∈ D, IsNonemptyPathSubgraph H) ∧
    (D : Set G.Subgraph).Pairwise (fun H J => Disjoint H.edgeSet J.edgeSet) ∧
    (⋃ H ∈ D, H.edgeSet) = E ∧ D.card ≤ q

theorem HasEdgePathPartition.mono {E : Set (Sym2 V)} {q r : ℕ}
    (h : HasEdgePathPartition G E q) (hqr : q ≤ r) : HasEdgePathPartition G E r := by
  obtain ⟨D, hp, hd, hE, hc⟩ := h
  exact ⟨D, hp, hd, hE, hc.trans hqr⟩

theorem hasEdgePathPartition_empty : HasEdgePathPartition G ∅ 0 := by
  exact ⟨∅, by simp, by simp, by simp, by simp⟩

theorem HasEdgePathPartition.toPathPartition {q : ℕ}
    (h : HasEdgePathPartition G G.edgeSet q) : HasPathPartition G q := by
  obtain ⟨D, hp, hd, hE, hc⟩ := h
  exact ⟨D, hp, ⟨hd, hE⟩, hc⟩

/-- Insert one disjoint nonempty path, preserving its original ambient edges. -/
theorem HasEdgePathPartition.insert_path {E : Set (Sym2 V)} {q : ℕ} {u v : V}
    (h : HasEdgePathPartition G E q) (P : G.Walk u v) (hp : P.IsPath)
    (hn : ¬P.Nil) (hdP : Disjoint P.edgeSet E) :
    HasEdgePathPartition G (P.edgeSet ∪ E) (q + 1) := by
  classical
  obtain ⟨D, hpaths, hd, hE, hcard⟩ := h
  have hsub : ∀ H ∈ D, H.edgeSet ⊆ E := by
    intro H hH e he
    rw [← hE]
    exact Set.mem_iUnion.mpr ⟨H, Set.mem_iUnion.mpr ⟨hH, he⟩⟩
  refine ⟨insert P.toSubgraph D, ?_, ?_, ?_, ?_⟩
  · intro H hH
    rcases Finset.mem_insert.mp hH with rfl | hH
    · exact ⟨u, v, P, hp, hn, rfl⟩
    · exact hpaths H hH
  · intro H hH J hJ hne
    rcases Finset.mem_insert.mp hH with rfl | hH <;>
      rcases Finset.mem_insert.mp hJ with rfl | hJ
    · exact (hne rfl).elim
    · simpa only [Walk.edgeSet_toSubgraph] using hdP.mono_right (hsub J hJ)
    · simpa only [Walk.edgeSet_toSubgraph] using (hdP.mono_right (hsub H hH)).symm
    · exact hd hH hJ hne
  · ext e
    constructor
    · intro he
      obtain ⟨H, hH, heH⟩ := Set.mem_iUnion₂.mp he
      rcases Finset.mem_insert.mp hH with rfl | hH
      · exact Or.inl (by simpa only [Walk.edgeSet_toSubgraph] using heH)
      · exact Or.inr (hsub H hH heH)
    · rintro (heP | heE)
      · exact Set.mem_iUnion₂.mpr ⟨P.toSubgraph, Finset.mem_insert_self _ _,
          by simpa only [Walk.edgeSet_toSubgraph] using heP⟩
      · rw [← hE] at heE
        obtain ⟨H, hH, heH⟩ := Set.mem_iUnion₂.mp heE
        exact Set.mem_iUnion₂.mpr ⟨H, Finset.mem_insert_of_mem hH, heH⟩
  · exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hcard 1)

/-- A possibly empty simple walk costs at most one nonempty path. -/
theorem hasEdgePathPartition_of_path {u v : V} (P : G.Walk u v) (hp : P.IsPath) :
    HasEdgePathPartition G P.edgeSet 1 := by
  by_cases hn : P.Nil
  · have hE : P.edgeSet = ∅ := by
      cases hn
      simp
    rw [hE]
    exact hasEdgePathPartition_empty.mono (by omega)
  · have h := hasEdgePathPartition_empty.insert_path P hp hn (by simp)
    simpa using h

theorem HasPathPairAt.toEdgePathPartition {u v : V} {E : Set (Sym2 V)}
    (h : HasPathPairAt G u v E) : HasEdgePathPartition G E 2 := by
  obtain ⟨a, P, Q, hp, hq, hpn, hqn, hd, hE⟩ := h
  have hh := (hasEdgePathPartition_of_path Q hq).insert_path P hp hpn hd
  exact hE ▸ hh

end Erdos583
end Source20_Erdos583_EdgePathPartition
/- END Erdos583.EdgePathPartition -/

/- BEGIN Erdos583.CycleFour; source SHA256 47b96c0e0f6a21a340aa32a9b4d4a63b6935c5bf03d508b2be89bc3f39242a3a -/
section Source21_Erdos583_CycleFour



/-! Common-root cycle repair using the proved short-path base. -/
namespace Erdos583
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- Split at the first vertex satisfying a predicate. The prefix can meet the
predicate only at its final vertex. -/
theorem walk_first_meeting {u v : V} (P : G.Walk u v) (M : V → Prop)
    (hm : ∃ x, x ∈ P.support ∧ M x) :
    ∃ (x : V) (L : G.Walk u x) (R : G.Walk x v),
      P = L.append R ∧ M x ∧ (∀ y, y ∈ L.support → M y → y = x) := by
  classical
  induction P with
  | @nil u =>
    obtain ⟨x, hx, hMx⟩ := hm
    have hxu : x = u := by simpa using hx
    subst x
    exact ⟨u, Walk.nil, Walk.nil, rfl, hMx, by intro y hy _; simpa using hy⟩
  | @cons u w v h Q ih =>
    by_cases hMu : M u
    · exact ⟨u, Walk.nil, Walk.cons h Q, rfl, hMu,
        by intro y hy _; simpa using hy⟩
    · have hmQ : ∃ x, x ∈ Q.support ∧ M x := by
        obtain ⟨x, hx, hMx⟩ := hm
        simp only [Walk.support_cons, List.mem_cons] at hx
        rcases hx with hxu | hxQ
        · exact (hMu (hxu ▸ hMx)).elim
        · exact ⟨x, hxQ, hMx⟩
      obtain ⟨x, L, R, hsplit, hMx, hprefix⟩ := ih hmQ
      refine ⟨x, Walk.cons h L, R, ?_, hMx, ?_⟩
      · simp [← hsplit]
      · intro y hy hMy
        simp only [Walk.support_cons, List.mem_cons] at hy
        rcases hy with hyu | hyL
        · exact (hMu (hyu ▸ hMy)).elim
        · exact hprefix y hyL hMy

/-- A cycle edge disjoint from a path of at most two edges has, at any shared
vertex, a cycle neighbor outside that path. -/
theorem cycle_neighbor_outside_short_path {r u v x : V}
    (c : G.Walk r r) (P : G.Walk u v) (hc : c.IsCycle)
    (hlen : P.length ≤ 2) (hd : Disjoint c.edgeSet P.edgeSet)
    (hxC : x ∈ c.support) (hxP : x ∈ P.support) :
    ∃ y, G.Adj x y ∧ s(x,y) ∈ c.edgeSet ∧ y ∉ P.support := by
  cases P with
  | nil =>
    have hxu : x = u := by simpa using hxP
    subst x
    obtain ⟨y, hy, hxy, he⟩ := cycle_neighbor_avoiding c hc u u hxC
    exact ⟨y, hxy, he, by simpa using hy⟩
  | @cons u w v h₁ Q =>
    cases Q with
    | nil =>
      have hx : x = u ∨ x = v := by simpa using hxP
      rcases hx with hx | hx
      · subst x
        obtain ⟨y, hy, hxy, he⟩ := cycle_neighbor_avoiding c hc u v hxC
        refine ⟨y, hxy, he, ?_⟩
        have hyn : y ≠ u := hxy.ne.symm
        simpa using And.intro hyn hy
      · subst x
        obtain ⟨y, hy, hxy, he⟩ := cycle_neighbor_avoiding c hc v u hxC
        refine ⟨y, hxy, he, ?_⟩
        have hyn : y ≠ v := hxy.ne.symm
        simpa using And.intro hy hyn
    | @cons w z v h₂ R =>
      cases R with
      | @cons z t v h₃ T =>
        simp only [Walk.length_cons] at hlen
        omega
      | nil =>
        have hx : x = u ∨ x = w ∨ x = v := by simpa using hxP
        rcases hx with hx | hx | hx
        · subst x
          obtain ⟨y, hy, hxy, he⟩ := cycle_neighbor_avoiding c hc u v hxC
          refine ⟨y, hxy, he, ?_⟩
          intro hyP
          have hh : y = u ∨ y = w ∨ y = v := by simpa using hyP
          rcases hh with hh | hh | hh
          · exact hxy.ne hh.symm
          · exact Set.disjoint_left.mp hd he (by simp [hh])
          · exact hy hh
        · subst x
          obtain ⟨y, hy, hxy, he⟩ := cycle_neighbor_avoiding c hc w u hxC
          refine ⟨y, hxy, he, ?_⟩
          intro hyP
          have hh : y = u ∨ y = w ∨ y = v := by simpa using hyP
          rcases hh with hh | hh | hh
          · exact hy hh
          · exact hxy.ne hh.symm
          · exact Set.disjoint_left.mp hd he (by simp [hh])
        · subst x
          obtain ⟨y, hy, hxy, he⟩ := cycle_neighbor_avoiding c hc v u hxC
          refine ⟨y, hxy, he, ?_⟩
          intro hyP
          have hh : y = u ∨ y = w ∨ y = v := by simpa using hyP
          rcases hh with hh | hh | hh
          · exact hy hh
          · exact Set.disjoint_left.mp hd he (by simp [hh, Sym2.eq_swap])
          · exact hxy.ne hh.symm

/-- A path and a finite family of cycles each meeting it admit the reduced-budget
repair. The cycles may have different roots and arbitrary support overlaps. -/
theorem hasEdgePathPartition_short_path_cycles {I : Type*} {r : I → V}
    (c : (i : I) → G.Walk (r i) (r i)) :
    ∀ (S : Finset I) (u v : V) (P : G.Walk u v), P.IsPath →
      (∀ i ∈ S, (c i).IsCycle) →
      (S : Set I).Pairwise (fun i j => Disjoint (c i).edgeSet (c j).edgeSet) →
      (∀ i ∈ S, Disjoint (c i).edgeSet P.edgeSet) →
      (∀ i ∈ S, ∃ x, x ∈ P.support ∧ x ∈ (c i).support) →
      P.length + S.card ≤ 4 →
      HasEdgePathPartition G (P.edgeSet ∪ (⋃ i ∈ S, (c i).edgeSet)) (S.card + 1) := by
  classical
  intro S
  refine Finset.strongInductionOn S (fun S ih => ?_)
  · intro u v P hp hcy hdd hdP hmet hbudget
    by_cases hS0 : S = ∅
    · subst S
      simpa using hasEdgePathPartition_of_path P hp
    by_cases hS1 : S.card = 1
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hS1
      have hlen : P.length ≤ 3 := by
        simp only [Finset.card_singleton] at hbudget
        omega
      have hh := (pathPairAt_of_short_path_cycle (c i) P (hcy i (by simp)) hp hlen
        (hdP i (by simp)) (hmet i (by simp))).toEdgePathPartition
      simpa only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left, Finset.card_singleton,
        Nat.reduceAdd, Set.union_comm] using hh
    have hSpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS0)
    have hlen : P.length ≤ 2 := by omega
    let M : V → Prop := fun x => ∃ i ∈ S, x ∈ (c i).support
    have hmeet : ∃ x, x ∈ P.support ∧ M x := by
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS0
      obtain ⟨x, hxP, hxC⟩ := hmet i hi
      exact ⟨x, hxP, i, hi, hxC⟩
    obtain ⟨x, L, R, hsplit, hxM, hprefix⟩ := walk_first_meeting P M hmeet
    obtain ⟨i, hi, hxC⟩ := hxM
    have hpLR : (L.append R).IsPath := hsplit ▸ hp
    have hLs : L.support ⊆ P.support := by
      rw [hsplit]; exact L.support_subset_support_append_left R
    have hRs : R.support ⊆ P.support := by
      rw [hsplit]; exact L.support_subset_support_append_right R
    have hLE : L.edgeSet ⊆ P.edgeSet := by
      rw [hsplit, Walk.edgeSet_append]; exact Set.subset_union_left
    have hRE : R.edgeSet ⊆ P.edgeSet := by
      rw [hsplit, Walk.edgeSet_append]; exact Set.subset_union_right
    obtain ⟨y, hxy, heC, hyP⟩ := cycle_neighbor_outside_short_path
      (c i) P (hcy i hi) hlen (hdP i hi) hxC (hLs L.end_mem_support)
    obtain ⟨Q, hQ, hQn, hQno, hcut⟩ := cycle_cut_oriented_edge (c i) (hcy i hi) heC
    have hQE : Q.edgeSet ⊆ (c i).edgeSet := by
      rw [← hcut]; exact Set.subset_insert _ _
    have hQs : Q.support ⊆ (c i).support :=
      walk_support_subset_of_edgeSet_subset Q (c i) hQn hQE
    let F := L.append Q.reverse
    let N := Walk.cons hxy.symm R
    have hF : F.IsPath := by
      apply isPath_append_of_support_inter L Q.reverse hpLR.of_append_left hQ.reverse
      intro z hzL hzQ
      have hzQ' : z ∈ Q.support := by simpa using hzQ
      exact hprefix z hzL ⟨i, hi, hQs hzQ'⟩
    have hFn : ¬F.Nil := by
      intro hnil
      exact hQn (by
        have hqnil := (Walk.nil_append_iff.mp hnil).2
        simpa using hqnil)
    have hN : N.IsPath := hpLR.of_append_right.cons (fun hyR => hyP (hRs hyR))
    have hNL : N.length ≤ P.length + 1 := by
      have hPL : P.length = L.length + R.length := by rw [hsplit, Walk.length_append]
      simp only [N, Walk.length_cons]
      omega
    have hcard : (S.erase i).card + 1 = S.card := Finset.card_erase_add_one hi
    have hsmall : S.erase i ⊂ S := Finset.erase_ssubset hi
    have hcy' : ∀ j ∈ S.erase i, (c j).IsCycle := fun j hj => hcy j (Finset.mem_of_mem_erase hj)
    have hdd' : (S.erase i : Set I).Pairwise
        (fun j k => Disjoint (c j).edgeSet (c k).edgeSet) := by
      intro j hj k hk hne
      exact hdd (Finset.mem_of_mem_erase hj) (Finset.mem_of_mem_erase hk) hne
    have hdi : ∀ j ∈ S.erase i, Disjoint (c i).edgeSet (c j).edgeSet := by
      intro j hj
      exact hdd hi (Finset.mem_of_mem_erase hj) (Finset.mem_erase.mp hj).1.symm
    have hdN : ∀ j ∈ S.erase i, Disjoint (c j).edgeSet N.edgeSet := by
      intro j hj
      apply Set.disjoint_left.mpr
      intro e hej heN
      simp only [N, Walk.edgeSet_cons, Set.mem_insert_iff] at heN
      rcases heN with heq | heR
      · have heCi : e ∈ (c i).edgeSet := by simpa [heq, Sym2.eq_swap] using heC
        exact Set.disjoint_left.mp (hdi j hj) heCi hej
      · exact Set.disjoint_left.mp (hdP j (Finset.mem_of_mem_erase hj)) hej (hRE heR)
    have hnewBudget : N.length + (S.erase i).card ≤ 4 := by omega
    have hmetN : ∀ j ∈ S.erase i, ∃ z, z ∈ N.support ∧ z ∈ (c j).support := by
      intro j hj
      obtain ⟨z, hzP, hzC⟩ := hmet j (Finset.mem_of_mem_erase hj)
      have hzR : z ∈ R.support := by
        rw [hsplit, Walk.mem_support_append_iff] at hzP
        rcases hzP with hzL | hzR
        · have hzx := hprefix z hzL ⟨j, Finset.mem_of_mem_erase hj, hzC⟩
          simpa [hzx] using R.start_mem_support
        · exact hzR
      exact ⟨z, by simp [N, hzR], hzC⟩
    have hpart := ih (S.erase i) hsmall y v N hN hcy' hdd' hdN hmetN hnewBudget
    have hdLR : Disjoint L.edgeSet R.edgeSet := by
      apply Set.disjoint_left.mpr
      exact (Walk.isTrail_append L R).mp hpLR.isTrail |>.2.2
    have hFdisj : Disjoint F.edgeSet (N.edgeSet ∪ (⋃ j ∈ S.erase i, (c j).edgeSet)) := by
      apply Set.disjoint_left.mpr
      intro e heF heRest
      simp only [F, Walk.edgeSet_append, Walk.edgeSet_reverse] at heF
      rcases heRest with heN | heCycles
      · simp only [N, Walk.edgeSet_cons, Set.mem_insert_iff] at heN
        rcases heF with heL | heQ <;> rcases heN with heq | heR
        · have heCi : e ∈ (c i).edgeSet := by simpa [heq, Sym2.eq_swap] using heC
          exact Set.disjoint_left.mp (hdP i hi) heCi (hLE heL)
        · exact Set.disjoint_left.mp hdLR heL heR
        · apply hQno
          simpa [heq, Sym2.eq_swap] using heQ
        · exact Set.disjoint_left.mp (hdP i hi) (hQE heQ) (hRE heR)
      · obtain ⟨j, hj, hej⟩ := Set.mem_iUnion₂.mp heCycles
        rcases heF with heL | heQ
        · exact Set.disjoint_left.mp (hdP j (Finset.mem_of_mem_erase hj)) hej (hLE heL)
        · exact Set.disjoint_left.mp (hdi j hj) (hQE heQ) hej
    have hfinish := hpart.insert_path F hF hFn hFdisj
    have hUnion : (⋃ j ∈ S, (c j).edgeSet) =
        (c i).edgeSet ∪ (⋃ j ∈ S.erase i, (c j).edgeSet) := by
      conv_lhs => rw [← Finset.insert_erase hi]
      simp
    have hEdges : F.edgeSet ∪ (N.edgeSet ∪ (⋃ j ∈ S.erase i, (c j).edgeSet)) =
        P.edgeSet ∪ (⋃ j ∈ S, (c j).edgeSet) := by
      rw [hUnion, ← hcut, hsplit]
      ext e
      simp only [F, N, Walk.edgeSet_append, Walk.edgeSet_reverse, Walk.edgeSet_cons,
        Set.mem_union, Set.mem_insert_iff]
      rw [show s(y,x) = s(x,y) from Sym2.eq_swap]
      tauto
    rw [hEdges] at hfinish
    exact hfinish.mono (by omega)

/-- Up to four edge-disjoint simple cycles with a common root require at most
one more simple path than their number. -/
theorem hasEdgePathPartition_rooted_cycles_le_four {I : Type*} {r : V}
    (c : I → G.Walk r r) (S : Finset I)
    (hcy : ∀ i ∈ S, (c i).IsCycle)
    (hdd : (S : Set I).Pairwise (fun i j => Disjoint (c i).edgeSet (c j).edgeSet))
    (hcard : S.card ≤ 4) :
    HasEdgePathPartition G (⋃ i ∈ S, (c i).edgeSet) (S.card + 1) := by
  have hh := hasEdgePathPartition_short_path_cycles c S r r Walk.nil
    Walk.IsPath.nil hcy hdd (by simp)
    (by intro i _; exact ⟨r, by simp, (c i).start_mem_support⟩) (by simpa using hcard)
  simpa using hh

/-- Whole-graph version of the four-cycle supplier. -/
theorem hasPathPartition_five_of_four_cycles {r : V} (c : Fin 4 → G.Walk r r)
    (hcy : ∀ i, (c i).IsCycle)
    (hdd : Pairwise (fun i j => Disjoint (c i).edgeSet (c j).edgeSet))
    (hcover : (⋃ i, (c i).edgeSet) = G.edgeSet) : HasPathPartition G 5 := by
  have hh := hasEdgePathPartition_rooted_cycles_le_four c Finset.univ
    (by simpa using hcy) (by intro i _ j _ hij; exact hdd hij) (by simp)
  have hE : (⋃ i ∈ (Finset.univ : Finset (Fin 4)), (c i).edgeSet) = G.edgeSet := by
    simpa using hcover
  rw [hE] at hh
  exact (hh.mono (by simp)).toPathPartition

end Erdos583
end Source21_Erdos583_CycleFour
/- END Erdos583.CycleFour -/

/- BEGIN Erdos583.CycleGrouping; source SHA256 1b9ee750cff99376b315c7c3d50efadd4953c7ec5264e833a654a16ad39a2e20 -/
section Source22_Erdos583_CycleGrouping



/-! Grouping common-root cycles in batches of four, and conversion of actual
mixed path/cycle partitions to ordinary simple-path partitions. -/
namespace Erdos583
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

theorem HasEdgePathPartition.union {E F : Set (Sym2 V)} {q t : ℕ}
    (hE : HasEdgePathPartition G E q) (hF : HasEdgePathPartition G F t)
    (hdEF : Disjoint E F) : HasEdgePathPartition G (E ∪ F) (q + t) := by
  classical
  obtain ⟨D, hD, hdD, hDE, hDc⟩ := hE
  obtain ⟨B, hB, hdB, hBF, hBc⟩ := hF
  have hDs : ∀ H ∈ D, H.edgeSet ⊆ E := by
    intro H hH e he
    rw [← hDE]
    exact Set.mem_iUnion₂.mpr ⟨H, hH, he⟩
  have hBs : ∀ H ∈ B, H.edgeSet ⊆ F := by
    intro H hH e he
    rw [← hBF]
    exact Set.mem_iUnion₂.mpr ⟨H, hH, he⟩
  refine ⟨D ∪ B, ?_, ?_, ?_, ?_⟩
  · intro H hH
    exact (Finset.mem_union.mp hH).elim (hD H) (hB H)
  · intro H hH J hJ hne
    rcases Finset.mem_union.mp hH with hHD | hHB <;>
      rcases Finset.mem_union.mp hJ with hJD | hJB
    · exact hdD hHD hJD hne
    · exact hdEF.mono (hDs H hHD) (hBs J hJB)
    · exact (hdEF.mono (hDs J hJD) (hBs H hHB)).symm
    · exact hdB hHB hJB hne
  · ext e
    constructor
    · intro he
      obtain ⟨H, hH, heH⟩ := Set.mem_iUnion₂.mp he
      exact (Finset.mem_union.mp hH).elim
        (fun hh => Or.inl (hDs H hh heH)) (fun hh => Or.inr (hBs H hh heH))
    · rintro (heE | heF)
      · rw [← hDE] at heE
        obtain ⟨H, hH, heH⟩ := Set.mem_iUnion₂.mp heE
        exact Set.mem_iUnion₂.mpr ⟨H, Finset.mem_union_left B hH, heH⟩
      · rw [← hBF] at heF
        obtain ⟨H, hH, heH⟩ := Set.mem_iUnion₂.mp heF
        exact Set.mem_iUnion₂.mpr ⟨H, Finset.mem_union_right D hH, heH⟩
  · exact (Finset.card_union_le D B).trans (Nat.add_le_add hDc hBc)

/-- Arbitrarily many common-root cycles: group four at a time. -/
theorem hasEdgePathPartition_rooted_cycles_group_four {I : Type*} {r : V}
    (c : I → G.Walk r r) : ∀ S : Finset I,
    (∀ i ∈ S, (c i).IsCycle) →
    (S : Set I).Pairwise (fun i j => Disjoint (c i).edgeSet (c j).edgeSet) →
    HasEdgePathPartition G (⋃ i ∈ S, (c i).edgeSet) (S.card + (S.card + 3) / 4) := by
  classical
  intro S
  refine Finset.strongInductionOn S (fun S ih => ?_)
  intro hcy hdd
  by_cases hzero : S = ∅
  · subst S
    simpa using (hasEdgePathPartition_empty (G := G))
  have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hzero)
  by_cases hsmall : S.card ≤ 4
  · exact (hasEdgePathPartition_rooted_cycles_le_four c S hcy hdd hsmall).mono (by omega)
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (show 4 ≤ S.card by omega)
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hdiff : S \ T ⊂ S := Finset.sdiff_ssubset hTS hTne
  have hcyT : ∀ i ∈ T, (c i).IsCycle := fun i hi => hcy i (hTS hi)
  have hcyR : ∀ i ∈ S \ T, (c i).IsCycle := fun i hi => hcy i (Finset.mem_sdiff.mp hi).1
  have hddT : (T : Set I).Pairwise (fun i j => Disjoint (c i).edgeSet (c j).edgeSet) := by
    intro i hi j hj hne
    exact hdd (hTS hi) (hTS hj) hne
  have hddR : ((S \ T : Finset I) : Set I).Pairwise (fun i j => Disjoint (c i).edgeSet (c j).edgeSet) := by
    intro i hi j hj hne
    exact hdd (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hne
  have hpartT := hasEdgePathPartition_rooted_cycles_le_four c T hcyT hddT (by omega)
  have hpartR := ih (S \ T) hdiff hcyR hddR
  have hdTR : Disjoint (⋃ i ∈ T, (c i).edgeSet) (⋃ j ∈ S \ T, (c j).edgeSet) := by
    apply Set.disjoint_left.mpr
    intro e heT heR
    obtain ⟨i, hi, hei⟩ := Set.mem_iUnion₂.mp heT
    obtain ⟨j, hj, hej⟩ := Set.mem_iUnion₂.mp heR
    have hne : i ≠ j := fun hij => (Finset.mem_sdiff.mp hj).2 (hij ▸ hi)
    exact Set.disjoint_left.mp (hdd (hTS hi) (Finset.mem_sdiff.mp hj).1 hne) hei hej
  have hE : (⋃ i ∈ T, (c i).edgeSet) ∪ (⋃ j ∈ S \ T, (c j).edgeSet) =
      (⋃ i ∈ S, (c i).edgeSet) := by
    ext e
    constructor
    · rintro (heT | heR)
      · obtain ⟨i, hi, hei⟩ := Set.mem_iUnion₂.mp heT
        exact Set.mem_iUnion₂.mpr ⟨i, hTS hi, hei⟩
      · obtain ⟨i, hi, hei⟩ := Set.mem_iUnion₂.mp heR
        exact Set.mem_iUnion₂.mpr ⟨i, (Finset.mem_sdiff.mp hi).1, hei⟩
    · intro he
      obtain ⟨i, hi, hei⟩ := Set.mem_iUnion₂.mp he
      by_cases hiT : i ∈ T
      · exact Or.inl (Set.mem_iUnion₂.mpr ⟨i, hiT, hei⟩)
      · exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, Finset.mem_sdiff.mpr ⟨hi, hiT⟩, hei⟩)
  have hpart := hpartT.union hpartR hdTR
  rw [hE] at hpart
  have hcard := Finset.card_sdiff_add_card_eq_card hTS
  exact hpart.mono (by omega)

/-- Convert an actual mixed partition using the proved four-cycle grouping.
The extra cost is the ceiling of one quarter of the cycle budget. -/
theorem HasMixedPartitionAt.toPathPartition_four {x : V} {a q : ℕ}
    (h : HasMixedPartitionAt G x a q) : HasPathPartition G (a + (q + 3) / 4) := by
  classical
  obtain ⟨P, C, hP, hC, hPC, hdec, htotal, hcount⟩ := h
  let c : G.Subgraph → G.Walk x x := fun H =>
    if hH : H ∈ C then Classical.choose (hC H hH) else Walk.nil
  have hspec : ∀ H ∈ C, (c H).IsCycle ∧ H = (c H).toSubgraph := by
    intro H hH
    simpa only [c, dif_pos hH] using Classical.choose_spec (hC H hH)
  have hCE : ∀ H ∈ C, (c H).edgeSet = H.edgeSet := by
    intro H hH
    have hh := congrArg (fun J : G.Subgraph => J.edgeSet) (hspec H hH).2
    simpa only [Walk.edgeSet_toSubgraph] using hh.symm
  have hcycles : ∀ H ∈ C, (c H).IsCycle := fun H hH => (hspec H hH).1
  have hdcycles : (C : Set G.Subgraph).Pairwise
      (fun H J => Disjoint (c H).edgeSet (c J).edgeSet) := by
    intro H hH J hJ hne
    rw [hCE H hH, hCE J hJ]
    exact hdec.1 (Finset.mem_union_right P hH) (Finset.mem_union_right P hJ) hne
  have hcyclePart := hasEdgePathPartition_rooted_cycles_group_four c C hcycles hdcycles
  have hcycleEdges : (⋃ H ∈ C, (c H).edgeSet) = ⋃ H ∈ C, H.edgeSet := by
    apply Set.iUnion_congr
    intro H
    apply Set.iUnion_congr
    intro hH
    exact hCE H hH
  rw [hcycleEdges] at hcyclePart
  have hpathPart : HasEdgePathPartition G (⋃ H ∈ P, H.edgeSet) P.card := by
    refine ⟨P, hP, ?_, rfl, le_rfl⟩
    intro H hH J hJ hne
    exact hdec.1 (Finset.mem_union_left C hH) (Finset.mem_union_left C hJ) hne
  have hd : Disjoint (⋃ H ∈ P, H.edgeSet) (⋃ J ∈ C, J.edgeSet) := by
    apply Set.disjoint_left.mpr
    intro e heP heC
    obtain ⟨H, hH, heH⟩ := Set.mem_iUnion₂.mp heP
    obtain ⟨J, hJ, heJ⟩ := Set.mem_iUnion₂.mp heC
    have hne : H ≠ J := by
      intro heq
      exact Finset.disjoint_left.mp hPC hH (heq.symm ▸ hJ)
    exact Set.disjoint_left.mp
      (hdec.1 (Finset.mem_union_left C hH) (Finset.mem_union_right P hJ) hne) heH heJ
  have hcover : (⋃ H ∈ P, H.edgeSet) ∪ (⋃ H ∈ C, H.edgeSet) = G.edgeSet := by
    calc
      _ = ⋃ H ∈ P ∪ C, H.edgeSet := by
        ext e
        constructor
        · rintro (heP | heC)
          · obtain ⟨H, hH, heH⟩ := Set.mem_iUnion₂.mp heP
            exact Set.mem_iUnion₂.mpr ⟨H, Finset.mem_union_left C hH, heH⟩
          · obtain ⟨H, hH, heH⟩ := Set.mem_iUnion₂.mp heC
            exact Set.mem_iUnion₂.mpr ⟨H, Finset.mem_union_right P hH, heH⟩
        · intro he
          obtain ⟨H, hH, heH⟩ := Set.mem_iUnion₂.mp he
          rcases Finset.mem_union.mp hH with hHP | hHC
          · exact Or.inl (Set.mem_iUnion₂.mpr ⟨H, hHP, heH⟩)
          · exact Or.inr (Set.mem_iUnion₂.mpr ⟨H, hHC, heH⟩)
      _ = G.edgeSet := hdec.2
  have hpart := hpathPart.union hcyclePart hd
  rw [hcover] at hpart
  have hdiv : (C.card + 3) / 4 ≤ (q + 3) / 4 :=
    Nat.div_le_div_right (Nat.add_le_add_right hcount 3)
  exact (hpart.mono (by omega)).toPathPartition

end Erdos583
end Source22_Erdos583_CycleGrouping
/- END Erdos583.CycleGrouping -/

/- BEGIN Erdos583.StarRestoreGlobal; source SHA256 966846d9969a3991bc5b0af032b1804551cfd3869d9f4297d0d345cd9aff4331 -/
section Source23_Erdos583_StarRestoreGlobal


/-!
# Global assembly for star restoration

The final theorem constructs full simultaneous star restoration from an
arbitrary residual path partition with the exact original-neighbor endpoint
hypothesis. All constructions retain explicit original-edge accounting.
-/

namespace Erdos583

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

attribute [local instance] Classical.propDecidable

/-- Edge bookkeeping for the simultaneous switches: each selected endpoint
adds its root edge to its owner and transfers out its predecessor edge. -/
def edgeTransaction {ι α E : Type*} (old : ι → Set E) (edge : α → E)
    (owner : α → ι) (f : α → Option α) (R : Set α) (i : ι) : Set E :=
  (old i \ {e | ∃ u ∈ R, owner u = i ∧ ∃ v, f u = some v ∧ edge v = e}) ∪
    {e | ∃ v ∈ R, owner v = i ∧ edge v = e}

/-- Exact global edge conservation and disjointness under the chain transfer
rule. The hypotheses specify old ownership and source edges explicitly. -/
theorem edgeTransaction_partition {ι α E : Type*}
    (old : ι → Set E) (edge : α → E) (owner : α → ι) (f : α → Option α)
    (R Z : Set α) (hedge : Function.Injective edge)
    (hd : Pairwise fun i j => Disjoint (old i) (old j))
    (hZR : Z ⊆ R)
    (hsource : ∀ z ∈ Z, ∀ i, edge z ∉ old i)
    (hmove : ∀ u ∈ R, ∀ v, f u = some v → edge v ∈ old (owner u))
    (hnext : ∀ u ∈ R, ∀ v, f u = some v → v ∈ R)
    (hprev : ∀ v ∈ R, v ∉ Z → ∃ u ∈ R, f u = some v) :
    (Pairwise fun i j => Disjoint (edgeTransaction old edge owner f R i)
      (edgeTransaction old edge owner f R j)) ∧
      (⋃ i, edgeTransaction old edge owner f R i) = (⋃ i, old i) ∪ edge '' Z := by
  have old_owner {i j : ι} {e : E} (hi : e ∈ old i) (hj : e ∈ old j) : i = j := by
    by_contra hne
    exact Set.disjoint_left.mp (hd hne) hi hj
  have stays_not_added {i : ι} {e : E}
      (hi : e ∈ old i)
      (hn : ¬ ∃ u ∈ R, owner u = i ∧ ∃ v, f u = some v ∧ edge v = e)
      {v : α} (hv : v ∈ R) (he : edge v = e) : False := by
    by_cases hz : v ∈ Z
    · exact hsource v hz i (he.symm ▸ hi)
    · obtain ⟨u, hu, huv⟩ := hprev v hv hz
      have hm := hmove u hu v huv
      have hoi : owner u = i := old_owner (he ▸ hm) hi
      exact hn ⟨u, hu, hoi, v, huv, he⟩
  constructor
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro e hei hej
    rcases hei with ⟨hei, hni⟩ | ⟨v, hv, hvi, he⟩ <;>
      rcases hej with ⟨hej, hnj⟩ | ⟨w, hw, hwj, hwedge⟩
    · exact hij (old_owner hei hej)
    · exact stays_not_added hei hni hw hwedge
    · exact stays_not_added hej hnj hv he
    · have hvw : v = w := hedge (he.trans hwedge.symm)
      exact hij (hvi.symm.trans (hvw ▸ hwj))
  · apply Set.Subset.antisymm
    · intro e he
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
      rcases hi with ⟨hi, _⟩ | ⟨v, hv, _, hve⟩
      · exact Or.inl (Set.mem_iUnion.mpr ⟨i, hi⟩)
      · by_cases hz : v ∈ Z
        · exact Or.inr ⟨v, hz, hve⟩
        · obtain ⟨u, hu, huv⟩ := hprev v hv hz
          exact Or.inl (Set.mem_iUnion.mpr ⟨owner u, hve ▸ hmove u hu v huv⟩)
    · intro e he
      rcases he with he | ⟨v, hv, rfl⟩
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
        by_cases hm : ∃ u ∈ R, owner u = i ∧ ∃ v, f u = some v ∧ edge v = e
        · obtain ⟨u, hu, _, v, huv, hve⟩ := hm
          exact Set.mem_iUnion.mpr ⟨owner v, Or.inr ⟨v, hnext u hu v huv, rfl, hve⟩⟩
        · exact Set.mem_iUnion.mpr ⟨i, Or.inl ⟨hi, hm⟩⟩
      · exact Set.mem_iUnion.mpr ⟨owner v, Or.inr ⟨v, hZR hv, rfl, rfl⟩⟩

namespace EndpointSelection

/-- A total extension of the endpoint-owner assignment. The fallback is never
used on the reachable vertices, all of which are original root neighbors. -/
noncomputable def totalOwner {D : Finset G.Subgraph} {x : V}
    (S : EndpointSelection D x) (fallback : D) (v : V) : D := by
  classical
  exact if hv : G.Adj x v then S.owner ⟨v,hv⟩ else fallback

/-- The exact edge set prescribed for each old member by simultaneous chain
switching. Path/cycle realization of this set is a separate proof obligation. -/
def restorationEdges {D : Finset G.Subgraph} {x : V}
    (S : EndpointSelection D x) (fallback : D) (Z : Finset V) (H : D) : Set (Sym2 V) :=
  edgeTransaction (fun J : D => J.val.edgeSet) (fun v => s(x,v))
    (S.totalOwner fallback) S.predecessor {v | ChainReachable S.predecessor Z v} H

/-- The graph-derived switching prescriptions partition exactly the residual
edges together with the deleted source edges. This proves global edge ownership,
without assuming that the prescribed pieces have already been realized as paths. -/
theorem restorationEdges_partition {D : Finset G.Subgraph} {x : V}
    (S : EndpointSelection D x) (fallback : D)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) Subgraph.edgeSet)
    (Z : Finset V) (hz : ∀ z ∈ Z, G.Adj x z)
    (hmissing : ∀ z ∈ Z, ∀ H ∈ D, ¬ H.Adj x z) :
    (Pairwise fun H J : D => Disjoint (S.restorationEdges fallback Z H)
      (S.restorationEdges fallback Z J)) ∧
      (⋃ H : D, S.restorationEdges fallback Z H) =
        (⋃ H : D, H.val.edgeSet) ∪ (fun v => s(x,v)) '' (Z : Set V) := by
  classical
  apply edgeTransaction_partition
  · exact (Sym2.mkEmbedding x).injective
  · intro H J hne
    exact hd H.property J.property (fun h => hne (Subtype.ext h))
  · intro z hzm
    exact chainReachable_source S.predecessor Z hzm
  · intro z hzm H he
    exact hmissing z hzm H.val H.property he
  · intro u hu v huv
    obtain ⟨z, hzm, n, hn⟩ := hu
    have hxu := S.reachable_vertex_adj (hz z hzm) n hn
    obtain ⟨_, he⟩ := S.predecessor_edge huv
    change (S.totalOwner fallback u).val.Adj x v
    simpa only [totalOwner, dif_pos hxu] using he
  · intro u hu v huv
    exact chainReachable_successor S.predecessor Z hu huv
  · intro v hv hvz
    exact chainReachable_predecessor S.predecessor Z hv hvz

end EndpointSelection

theorem IsRootedCycleSubgraph.edgeSet_nonempty {x : V} {H : G.Subgraph}
    (h : IsRootedCycleSubgraph x H) : H.edgeSet.Nonempty := by
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨s(x,p.snd), p.toSubgraph_adj_snd hp.not_nil⟩

/-- Assemble an indexed family of realized path/cycle pieces into the finset
interface. Nonempty disjoint edge sets prevent accidental duplicate members. -/
theorem hasMixedPartitionAt_of_indexed {ι : Type*} [Fintype ι]
    (out : ι → G.Subgraph) (C : Finset ι) (x : V)
    (hp : ∀ i, i ∉ C → IsNonemptyPathSubgraph (out i))
    (hc : ∀ i ∈ C, IsRootedCycleSubgraph x (out i))
    (hd : Pairwise fun i j => Disjoint (out i).edgeSet (out j).edgeSet)
    (hcover : (⋃ i, (out i).edgeSet) = G.edgeSet) :
    HasMixedPartitionAt G x (Fintype.card ι) C.card := by
  classical
  have hnon (i : ι) : (out i).edgeSet.Nonempty := by
    by_cases hi : i ∈ C
    · exact (hc i hi).edgeSet_nonempty
    · exact (hp i hi).edgeSet_nonempty
  have hout : Function.Injective out := by
    intro i j he
    by_contra hij
    obtain ⟨e, hei⟩ := hnon i
    exact Set.disjoint_left.mp (hd hij) hei (he ▸ hei)
  let A := Finset.univ \ C
  have hAC : A ∪ C = Finset.univ := by
    ext i
    simp [A]
  have hcard : A.card + C.card = Fintype.card ι := by
    have he := Finset.card_union_of_disjoint (show Disjoint A C from Finset.sdiff_disjoint)
    rw [hAC] at he
    simpa using he.symm
  have himage : A.image out ∪ C.image out = Finset.univ.image out := by
    rw [← Finset.image_union, hAC]
  refine ⟨A.image out, C.image out, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro H hH
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hH
    exact hp i (Finset.mem_sdiff.mp hi).2
  · intro H hH
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hH
    exact hc i hi
  · apply Finset.disjoint_left.mpr
    intro H hHP hHC
    obtain ⟨i, hi, hiH⟩ := Finset.mem_image.mp hHP
    obtain ⟨j, hj, hjH⟩ := Finset.mem_image.mp hHC
    have hij := hout (hiH.trans hjH.symm)
    exact (Finset.mem_sdiff.mp hi).2 (hij.symm ▸ hj)
  · rw [himage]
    constructor
    · intro H hH J hJ hne
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hJ
      exact hd (fun he => hne (he ▸ rfl))
    · rw [← hcover]
      ext e
      simp
  · rw [Finset.card_image_of_injective _ hout, Finset.card_image_of_injective _ hout, hcard]
  · rw [Finset.card_image_of_injective _ hout]

/-- In a simple walk, the join vertex occurs at exactly the prefix length. -/
theorem root_index_of_append [DecidableEq V] {a x b : V}
    (p : G.Walk a b) (hp : p.IsPath) (l : G.Walk a x) (r : G.Walk x b)
    (he : p = l.append r) : p.support.idxOf x = l.length := by
  have hx : x ∈ p.support := by rw [he]; simp
  have hi := p.getVert_support_idxOf hx
  have hj : p.getVert l.length = x := by rw [he, Walk.getVert_append']; simp
  apply hp.getVert_injOn _ _ (hi.trans hj.symm)
  · have hh := List.idxOf_lt_length_of_mem hx
    rw [Walk.length_support] at hh
    change p.support.idxOf x ≤ p.length
    omega
  · rw [he]
    simp

namespace PathPresentation

theorem edgeSet_eq {H : G.Subgraph} (P : PathPresentation H) : P.walk.edgeSet = H.edgeSet := by
  rw [← Walk.edgeSet_toSubgraph, P.toSubgraph_eq]

def predecessorEdges {H : G.Subgraph} (P : PathPresentation H) (x v : V) : Set (Sym2 V) :=
  {e | ∃ w, P.predecessor x v = some w ∧ s(x,w) = e}

theorem predecessorEdges_of_some {H : G.Subgraph} (P : PathPresentation H) (x v w : V)
    (h : P.predecessor x v = some w) : P.predecessorEdges x v = {s(x,w)} := by
  ext e
  simp [predecessorEdges, h, eq_comm]

theorem predecessorEdges_of_none {H : G.Subgraph} (P : PathPresentation H) (x v : V)
    (h : P.predecessor x v = none) : P.predecessorEdges x v = ∅ := by
  ext e
  simp [predecessorEdges, h]

theorem predecessor_finish_of_after_split {H : G.Subgraph} (P : PathPresentation H)
    {d x : V} (l : G.Walk P.start x) (r : G.Walk d P.finish)
    (hxd : G.Adj x d) (he : P.walk = l.append (.cons hxd r)) (hx : P.finish ≠ x) :
    P.predecessor x P.finish = some d := by
  classical
  have hs : x ∈ P.walk.support := by rw [he]; simp
  have hi := root_index_of_append P.walk P.isPath l (.cons hxd r) he
  have hne : P.finish ≠ P.start := Ne.symm (P.isPath.nil_iff_eq.not.mp P.nonempty)
  rw [predecessor, if_pos ⟨hs, hx, Or.inr rfl⟩, if_neg hne, hi, he, Walk.getVert_append]
  simp

/-- Realize the prescribed transaction for selecting only the first endpoint. -/
theorem realize_start {H : G.Subgraph} (P : PathPresentation H) (x : V)
    (hxa : G.Adj x P.start) :
    ∃ Q : G.Subgraph, IsNonemptyPathSubgraph Q ∧
      Q.edgeSet = (H.edgeSet \ P.predecessorEdges x P.start) ∪ {s(x,P.start)} := by
  classical
  by_cases hx : x ∈ P.walk.support
  · obtain ⟨c, l, r, hcx, he⟩ := exists_split_before_root P.walk hx hxa.ne
    have hpred := P.predecessor_start_of_split l r hcx he hxa.ne.symm
    have hp : (l.append (.cons hcx r)).IsPath := he ▸ P.isPath
    refine ⟨(l.reverse.append (.cons hxa.symm r)).toSubgraph,
      path_switch_one_nonempty l r hcx hxa.symm hp, ?_⟩
    rw [Walk.edgeSet_toSubgraph, path_switch_one_exact_edges l r hcx hxa.symm hp,
      P.predecessorEdges_of_some x P.start c hpred, ← he]
    rw [P.edgeSet_eq]
    ext e
    simp [Sym2.eq_swap]
  · have hpred : P.predecessor x P.start = none := by simp [predecessor, hx]
    refine ⟨(Walk.cons hxa P.walk).toSubgraph,
      ⟨x, P.finish, Walk.cons hxa P.walk, P.isPath.cons hx, Walk.not_nil_cons, rfl⟩, ?_⟩
    rw [P.predecessorEdges_of_none x P.start hpred, ← P.edgeSet_eq]
    simp [Set.union_comm]

/-- Realize the prescribed transaction for selecting only the last endpoint. -/
theorem realize_finish {H : G.Subgraph} (P : PathPresentation H) (x : V)
    (hxb : G.Adj x P.finish) :
    ∃ Q : G.Subgraph, IsNonemptyPathSubgraph Q ∧
      Q.edgeSet = (H.edgeSet \ P.predecessorEdges x P.finish) ∪ {s(x,P.finish)} := by
  classical
  by_cases hx : x ∈ P.walk.support
  · obtain ⟨l, r, he⟩ := Walk.mem_support_iff_exists_append.mp hx
    cases r with
    | nil => exact (hxb.ne rfl).elim
    | cons hxd r =>
      have hpred := P.predecessor_finish_of_after_split l r hxd he hxb.ne.symm
      have horig : (r.reverse.append (.cons hxd.symm l.reverse)).IsPath := by
        simpa only [he, Walk.reverse_append, Walk.reverse_cons, ← Walk.append_assoc,
          Walk.cons_nil_append]
          using P.isPath.reverse
      refine ⟨(r.append (.cons hxb.symm l.reverse)).toSubgraph, ?_, ?_⟩
      · simpa only [Walk.reverse_reverse] using
          path_switch_one_nonempty r.reverse l.reverse hxd.symm hxb.symm horig
      · have hedge := path_switch_one_exact_edges r.reverse l.reverse hxd.symm hxb.symm horig
        have hrev : P.walk.reverse = r.reverse.append (.cons hxd.symm l.reverse) := by
          simp only [he, Walk.reverse_append, Walk.reverse_cons, ← Walk.append_assoc,
            Walk.cons_nil_append]
        rw [Walk.reverse_reverse, ← hrev, Walk.edgeSet_reverse] at hedge
        rw [Walk.edgeSet_toSubgraph, hedge, P.predecessorEdges_of_some x P.finish _ hpred,
          P.edgeSet_eq]
        ext e
        simp [Sym2.eq_swap]
  · have hpred : P.predecessor x P.finish = none := by simp [predecessor, hx]
    refine ⟨(P.walk.concat hxb.symm).toSubgraph,
      ⟨P.start, x, P.walk.concat hxb.symm, P.isPath.concat hx hxb.symm, ?_, rfl⟩, ?_⟩
    · rw [Walk.not_nil_iff_lt_length]
      simp
    · rw [P.predecessorEdges_of_none x P.finish hpred, ← P.edgeSet_eq]
      simp [Sym2.eq_swap, Set.union_comm]

/-- Realize the transaction for selecting both endpoints. A cycle is created
exactly in the case where the old path avoids the root. -/
theorem realize_both {H : G.Subgraph} (P : PathPresentation H) (x : V)
    (hxa : G.Adj x P.start) (hxb : G.Adj x P.finish) :
    ∃ Q : G.Subgraph,
      (x ∈ P.walk.support → IsNonemptyPathSubgraph Q) ∧
      (x ∉ P.walk.support → IsRootedCycleSubgraph x Q) ∧
      Q.edgeSet = (H.edgeSet \ (P.predecessorEdges x P.start ∪
        P.predecessorEdges x P.finish)) ∪ {s(x,P.start),s(x,P.finish)} := by
  classical
  by_cases hx : x ∈ P.walk.support
  · obtain ⟨c, d, l, r, hcx, hxd, he⟩ :=
      exists_split_around_root P.walk hx hxa.ne hxb.ne
    have hpreda := P.predecessor_start_of_split l (.cons hxd r) hcx he hxa.ne.symm
    have hpredb := P.predecessor_finish_of_split l r hcx hxd he hxb.ne.symm
    have hp : (l.append (.cons hcx (.cons hxd r))).IsPath := he ▸ P.isPath
    refine ⟨(l.reverse.append (.cons hxa.symm (.cons hxb r.reverse))).toSubgraph,
      fun _ => path_switch_two_nonempty l r hcx hxd hxa.symm hxb hp,
      fun hn => (hn hx).elim, ?_⟩
    rw [Walk.edgeSet_toSubgraph, path_switch_two_exact_edges l r hcx hxd hxa.symm hxb hp,
      P.predecessorEdges_of_some x P.start c hpreda,
      P.predecessorEdges_of_some x P.finish d hpredb, ← he, P.edgeSet_eq]
    ext e
    simp [Sym2.eq_swap]
    tauto
  · have hpreda : P.predecessor x P.start = none := by simp [predecessor, hx]
    have hpredb : P.predecessor x P.finish = none := by simp [predecessor, hx]
    refine ⟨(Walk.cons hxa (P.walk.concat hxb.symm)).toSubgraph,
      fun hm => (hx hm).elim,
      fun _ => ⟨_, close_path_at_both_ends_isCycle P.walk P.isPath P.nonempty hx hxa hxb.symm, rfl⟩,
      ?_⟩
    rw [Walk.edgeSet_toSubgraph, close_path_at_both_ends_edgeSet,
      P.predecessorEdges_of_none x P.start hpreda,
      P.predecessorEdges_of_none x P.finish hpredb, P.edgeSet_eq]
    simp [Set.union_comm]

/-- Local form of the prescribed edge transaction. -/
def selectedEdges {H : G.Subgraph} (P : PathPresentation H) (x : V) (A : Set V) : Set (Sym2 V) :=
  (H.edgeSet \ {e | ∃ v ∈ A, e ∈ P.predecessorEdges x v}) ∪
    {e | ∃ v ∈ A, s(x,v) = e}

/-- Every subset of the two endpoints has a realized nonempty path or rooted
cycle with exactly the prescribed edges. This is the local realization step;
the condition identifying a cycle is explicit. -/
theorem realize_selected {H : G.Subgraph} (P : PathPresentation H) (x : V) (A : Set V)
    (hsub : A ⊆ {P.start,P.finish}) (hadj : ∀ v ∈ A, G.Adj x v) :
    ∃ Q : G.Subgraph,
      (¬ (P.start ∈ A ∧ P.finish ∈ A ∧ x ∉ P.walk.support) → IsNonemptyPathSubgraph Q) ∧
      ((P.start ∈ A ∧ P.finish ∈ A ∧ x ∉ P.walk.support) → IsRootedCycleSubgraph x Q) ∧
      Q.edgeSet = P.selectedEdges x A := by
  classical
  have hpath : IsNonemptyPathSubgraph H :=
    ⟨P.start, P.finish, P.walk, P.isPath, P.nonempty, P.toSubgraph_eq.symm⟩
  by_cases ha : P.start ∈ A
  · by_cases hb : P.finish ∈ A
    · have hA : A = {P.start,P.finish} := by
        ext v
        constructor
        · exact fun hv => hsub hv
        · intro hv
          rcases Set.mem_insert_iff.mp hv with rfl | hv
          · exact ha
          · exact (Set.mem_singleton_iff.mp hv) ▸ hb
      obtain ⟨Q, hp, hc, he⟩ := P.realize_both x (hadj _ ha) (hadj _ hb)
      refine ⟨Q, ?_, fun h => hc h.2.2, ?_⟩
      · intro hn
        exact hp (by by_contra hx; exact hn ⟨ha,hb,hx⟩)
      · rw [he, selectedEdges, hA]
        ext e
        simp [eq_comm]
        tauto
    · have hA : A = {P.start} := by
        ext v
        constructor
        · intro hv
          have hv' := hsub hv
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv' ⊢
          rcases hv' with hv' | hv'
          · exact hv'
          · exact (hb (hv' ▸ hv)).elim
        · intro hv
          exact (Set.mem_singleton_iff.mp hv) ▸ ha
      obtain ⟨Q, hp, he⟩ := P.realize_start x (hadj _ ha)
      refine ⟨Q, fun _ => hp, fun h => (hb h.2.1).elim, ?_⟩
      rw [he, selectedEdges, hA]
      simp
  · by_cases hb : P.finish ∈ A
    · have hA : A = {P.finish} := by
        ext v
        constructor
        · intro hv
          have hv' := hsub hv
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv' ⊢
          rcases hv' with hv' | hv'
          · exact (ha (hv' ▸ hv)).elim
          · exact hv'
        · intro hv
          exact (Set.mem_singleton_iff.mp hv) ▸ hb
      obtain ⟨Q, hp, he⟩ := P.realize_finish x (hadj _ hb)
      refine ⟨Q, fun _ => hp, fun h => (ha h.1).elim, ?_⟩
      rw [he, selectedEdges, hA]
      simp
    · have hA : A = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro v hv
        have hv' := hsub hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv'
        rcases hv' with hv' | hv'
        · exact ha (hv' ▸ hv)
        · exact hb (hv' ▸ hv)
      refine ⟨H, fun _ => hpath, fun h => (ha h.1).elim, ?_⟩
      simp [selectedEdges, hA]

end PathPresentation

namespace EndpointSelection

def selectedSet {D : Finset G.Subgraph} {x : V}
    (S : EndpointSelection D x) (fallback : D) (Z : Finset V) (H : D) : Set V :=
  {v | ChainReachable S.predecessor Z v ∧ S.totalOwner fallback v = H}

theorem selected_vertex_adj {D : Finset G.Subgraph} {x : V}
    (S : EndpointSelection D x) (fallback : D) (Z : Finset V)
    (hz : ∀ z ∈ Z, G.Adj x z) {H : D} {v : V}
    (hv : v ∈ S.selectedSet fallback Z H) : G.Adj x v := by
  obtain ⟨z,hzm,n,hn⟩ := hv.1
  exact S.reachable_vertex_adj (hz z hzm) n hn

theorem selected_predecessor_eq {D : Finset G.Subgraph} {x : V}
    (S : EndpointSelection D x) (fallback : D) (Z : Finset V)
    (hz : ∀ z ∈ Z, G.Adj x z) {H : D} {v : V}
    (hv : v ∈ S.selectedSet fallback Z H) :
    S.predecessor v = (S.presentation H).predecessor x v := by
  classical
  have hxv := S.selected_vertex_adj fallback Z hz hv
  have ho : S.owner ⟨v,hxv⟩ = H := by simpa [totalOwner, hxv] using hv.2
  simp only [predecessor, dif_pos hxv]
  rw [ho]

theorem selectedSet_subset_endpoints [Fintype V] {D : Finset G.Subgraph} {x : V}
    (S : EndpointSelection D x) (fallback : D) (Z : Finset V)
    (hz : ∀ z ∈ Z, G.Adj x z) (H : D) :
    S.selectedSet fallback Z H ⊆ {(S.presentation H).start,(S.presentation H).finish} := by
  classical
  intro v hv
  have hxv := S.selected_vertex_adj fallback Z hz hv
  have ho : S.owner ⟨v,hxv⟩ = H := by simpa [totalOwner, hxv] using hv.2
  have he := S.starts ⟨v,hxv⟩
  rw [ho, ← (S.presentation H).toSubgraph_eq] at he
  have hend := (pathStartsAt_iff_endpoints (S.presentation H).walk
    (S.presentation H).isPath (S.presentation H).nonempty v).mp he
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hend

theorem selectedEdges_eq_restorationEdges {D : Finset G.Subgraph} {x : V}
    (S : EndpointSelection D x) (fallback : D) (Z : Finset V)
    (hz : ∀ z ∈ Z, G.Adj x z) (H : D) :
    (S.presentation H).selectedEdges x (S.selectedSet fallback Z H) =
      S.restorationEdges fallback Z H := by
  have hremove :
      {e | ∃ v ∈ S.selectedSet fallback Z H, e ∈ (S.presentation H).predecessorEdges x v} =
      {e | ∃ v, ChainReachable S.predecessor Z v ∧
        S.totalOwner fallback v = H ∧ ∃ w, S.predecessor v = some w ∧ s(x,w) = e} := by
    ext e
    constructor
    · rintro ⟨v,hv,w,hw,he⟩
      exact ⟨v,hv.1,hv.2,w,(S.selected_predecessor_eq fallback Z hz hv).trans hw,he⟩
    · rintro ⟨v,hvr,hvo,w,hw,he⟩
      have hv : v ∈ S.selectedSet fallback Z H := ⟨hvr,hvo⟩
      exact ⟨v,hv,w,(S.selected_predecessor_eq fallback Z hz hv).symm.trans hw,he⟩
  unfold PathPresentation.selectedEdges
  rw [hremove]
  unfold restorationEdges edgeTransaction
  congr 1
  ext e
  simp only [selectedSet, Set.mem_ofPred_eq]
  aesop

def createsCycle {D : Finset G.Subgraph} {x : V}
    (S : EndpointSelection D x) (fallback : D) (Z : Finset V) (H : D) : Prop :=
  (S.presentation H).start ∈ S.selectedSet fallback Z H ∧
  (S.presentation H).finish ∈ S.selectedSet fallback Z H ∧
  x ∉ (S.presentation H).walk.support

/-- Every actual global prescription is realized by one nonempty path or one
rooted cycle. No path or cycle existence is assumed in this construction. -/
theorem realize_restorationEdges [Fintype V] {D : Finset G.Subgraph} {x : V}
    (S : EndpointSelection D x) (fallback : D) (Z : Finset V)
    (hz : ∀ z ∈ Z, G.Adj x z) (H : D) :
    ∃ Q : G.Subgraph,
      (¬ S.createsCycle fallback Z H → IsNonemptyPathSubgraph Q) ∧
      (S.createsCycle fallback Z H → IsRootedCycleSubgraph x Q) ∧
      Q.edgeSet = S.restorationEdges fallback Z H := by
  obtain ⟨Q,hp,hc,he⟩ := (S.presentation H).realize_selected x (S.selectedSet fallback Z H)
    (S.selectedSet_subset_endpoints fallback Z hz H)
    (fun v hv => S.selected_vertex_adj fallback Z hz hv)
  exact ⟨Q,hp,hc,he.trans (S.selectedEdges_eq_restorationEdges fallback Z hz H)⟩

/-- Every cycle index consumes two distinct terminals, and different indices
consume disjoint pairs. Hence twice the number of cycle indices is at most |Z|. -/
theorem cycle_indices_bound [Fintype V] {D : Finset G.Subgraph} {x : V}
    (S : EndpointSelection D x) (fallback : D)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) Subgraph.edgeSet)
    (Z : Finset V) (hz : ∀ z ∈ Z, G.Adj x z)
    (hmissing : ∀ z ∈ Z, ∀ H ∈ D, ¬ H.Adj x z) :
    2 * (Finset.univ.filter (S.createsCycle fallback Z)).card ≤ Z.card := by
  classical
  obtain ⟨T,hcard,_,_,hcomplete⟩ := S.exists_terminal_set hd Z hmissing
  let C := Finset.univ.filter (S.createsCycle fallback Z)
  let pair (H : D) : Finset V := {(S.presentation H).start,(S.presentation H).finish}
  have hselected (H : D) (hH : H ∈ C) (v : V) (hv : v ∈ pair H) :
      v ∈ S.selectedSet fallback Z H := by
    have hc : S.createsCycle fallback Z H := (Finset.mem_filter.mp hH).2
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hc.1
    · exact (Finset.mem_singleton.mp hv) ▸ hc.2.1
  have hpair (H : D) (_ : H ∈ C) : (pair H).card = 2 := by
    have hne := (S.presentation H).isPath.nil_iff_eq.not.mp (S.presentation H).nonempty
    simp [pair, hne]
  have hsub (H : D) (hH : H ∈ C) : pair H ⊆ T := by
    intro v hv
    have hvs := hselected H hH v hv
    have hc : S.createsCycle fallback Z H := (Finset.mem_filter.mp hH).2
    have hterminal : S.predecessor v = none := by
      rw [S.selected_predecessor_eq fallback Z hz hvs]
      simp [PathPresentation.predecessor, hc.2.2]
    obtain ⟨z,hzm,n,hn⟩ := hvs.1
    exact hcomplete z hzm n v hn hterminal
  have hdisj : Set.PairwiseDisjoint (C : Set D) pair := by
    intro H hH J hJ hne
    apply Finset.disjoint_left.mpr
    intro v hvH hvJ
    have hsH := hselected H hH v hvH
    have hsJ := hselected J hJ v hvJ
    exact hne (hsH.2.symm.trans hsJ.2)
  have hbound := disjoint_terminal_pairs_bound C T pair hpair hsub hdisj
  simpa only [hcard] using hbound

/-- Full simultaneous star restoration from a selected endpoint family.
The conclusion contains actual simple path/cycle subgraphs, exact edge cover,
and the paid cycle budget. -/
theorem restore [Fintype V] {D : Finset G.Subgraph} {x : V}
    (S : EndpointSelection D x) (fallback : D)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) Subgraph.edgeSet)
    (Z : Finset V) (hz : ∀ z ∈ Z, G.Adj x z)
    (hmissing : ∀ z ∈ Z, ∀ H ∈ D, ¬ H.Adj x z)
    (hcover : (⋃ H : D, H.val.edgeSet) ∪ (fun v => s(x,v)) '' (Z : Set V) = G.edgeSet) :
    ∃ q : ℕ, 2*q ≤ Z.card ∧ HasMixedPartitionAt G x D.card q := by
  classical
  choose out hp hc he using (fun H : D => S.realize_restorationEdges fallback Z hz H)
  let C := Finset.univ.filter (S.createsCycle fallback Z)
  have htrans := S.restorationEdges_partition fallback hd Z hz hmissing
  have hdout : Pairwise fun H J => Disjoint (out H).edgeSet (out J).edgeSet := by
    intro H J hne
    rw [he H, he J]
    exact htrans.1 hne
  have hcoverout : (⋃ H, (out H).edgeSet) = G.edgeSet := by
    simp_rw [he]
    exact htrans.2.trans hcover
  have hresult := hasMixedPartitionAt_of_indexed out C x
    (fun H hH => hp H (fun h => hH (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)))
    (fun H hH => hc H (Finset.mem_filter.mp hH).2) hdout hcoverout
  exact ⟨C.card, S.cycle_indices_bound fallback hd Z hz hmissing, by simpa using hresult⟩

end EndpointSelection

/-- Star restoration for ANY residual nonempty-simple-path partition, provided
EVERY original neighbor has an endpoint in that partition. Only original edges
are used. At most half as many rooted cycles as restored edges are created. -/
theorem restore_star_from_endpoint_partition [Fintype V]
    (D : Finset G.Subgraph) (x : V) (Z : Finset V)
    (hp : ∀ H ∈ D, IsNonemptyPathSubgraph H)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) Subgraph.edgeSet)
    (hZ : Z.Nonempty) (hz : ∀ z ∈ Z, G.Adj x z)
    (hmissing : ∀ z ∈ Z, ∀ H ∈ D, ¬ H.Adj x z)
    (hcover : (⋃ H : D, H.val.edgeSet) ∪ (fun v => s(x,v)) '' (Z : Set V) = G.edgeSet)
    (hend : ∀ v, G.Adj x v → ∃ H ∈ D, PathStartsAt H v) :
    ∃ q : ℕ, 2*q ≤ Z.card ∧ HasMixedPartitionAt G x D.card q := by
  classical
  let S := endpointSelection D x hp hend
  obtain ⟨z,hzm⟩ := hZ
  exact S.restore (S.owner ⟨z,hz z hzm⟩) hd Z hz hmissing hcover

end Erdos583
end Source23_Erdos583_StarRestoreGlobal
/- END Erdos583.StarRestoreGlobal -/

/- BEGIN Erdos583.StarRestoreEven; source SHA256 dfcbf59af043fa313895988973e120046b6b9443e62f48c70132f34d104230e5 -/
section Source24_Erdos583_StarRestoreEven



/-! Restore the actual even-neighbor star from any residual path partition. -/

namespace Erdos583

open SimpleGraph

variable {V : Type*} {G J : SimpleGraph V}

/-- Regard a subgraph as a subgraph of a larger ambient graph, with identical
vertices and edges. -/
def liftSubgraph (h : J ≤ G) (P : J.Subgraph) : G.Subgraph where
  verts := P.verts
  Adj := P.Adj
  adj_sub := fun hp => h (P.adj_sub hp)
  edge_vert := P.edge_vert
  symm := P.symm

@[simp] theorem liftSubgraph_edgeSet (h : J ≤ G) (P : J.Subgraph) :
    (liftSubgraph h P).edgeSet = P.edgeSet := rfl

theorem liftSubgraph_walk (h : J ≤ G) {a b : V} (p : J.Walk a b) :
    liftSubgraph h p.toSubgraph = (p.mapLe h).toSubgraph := by
  ext v w
  · simp [liftSubgraph]
  · exact (Walk.adj_toSubgraph_mapLe h).symm

theorem IsNonemptyPathSubgraph.lift {P : J.Subgraph}
    (hp : IsNonemptyPathSubgraph P) (h : J ≤ G) :
    IsNonemptyPathSubgraph (liftSubgraph h P) := by
  obtain ⟨a,b,p,hp,hn,rfl⟩ := hp
  refine ⟨a,b,p.mapLe h,hp.mapLe h,?_,liftSubgraph_walk h p⟩
  simpa only [Walk.not_nil_iff_lt_length, Walk.length_mapLe] using hn

theorem PathStartsAt.lift {P : J.Subgraph} {x : V}
    (hp : PathStartsAt P x) (h : J ≤ G) : PathStartsAt (liftSubgraph h P) x := by
  obtain ⟨b,p,hp,hn,rfl⟩ := hp
  refine ⟨b,p.mapLe h,hp.mapLe h,?_,liftSubgraph_walk h p⟩
  simpa only [Walk.not_nil_iff_lt_length, Walk.length_mapLe] using hn

theorem HasMixedPartitionAt.mono_parts {x : V} {a b q : ℕ}
    (h : HasMixedPartitionAt G x a q) (hab : a ≤ b) : HasMixedPartitionAt G x b q := by
  obtain ⟨P,C,hp,hc,hd,hdec,hcard,hq⟩ := h
  exact ⟨P,C,hp,hc,hd,hdec,hcard.trans hab,hq⟩

variable [Fintype V]

/-- The removed set is exactly the original edges from x to its even-degree neighbors. -/
theorem starDeleteEven_edge_cover (G : SimpleGraph V) (x : V) :
    (starDeleteEven G x).edgeSet ∪
      (fun v => s(x,v)) '' (evenNeighbors G x : Set V) = G.edgeSet := by
  classical
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    constructor
    · rintro (he | ⟨v,hv,he⟩)
      · exact (starDeleteEven_le G x) he
      · rw [← he]
        exact (mem_evenNeighbors G x v).mp hv |>.1
    · intro hab
      by_cases hax : a = x ∧ Even (G.degree b)
      · obtain ⟨hax,hb⟩ := hax
        subst a
        exact Or.inr ⟨b,(mem_evenNeighbors G x b).mpr ⟨hab,hb⟩,rfl⟩
      · by_cases hbx : b = x ∧ Even (G.degree a)
        · obtain ⟨hbx,ha⟩ := hbx
          subst b
          exact Or.inr ⟨a,(mem_evenNeighbors G x a).mpr ⟨hab.symm,ha⟩,Sym2.eq_swap⟩
        · exact Or.inl ⟨hab,hax,hbx⟩

/-- Full DK star restoration specialized to the actual all-even-neighbor
deletion. The supplied residual partition is arbitrary. Every original
neighbor's endpoint requirement is proved from its odd residual degree. -/
theorem restore_even_neighbor_star (G : SimpleGraph V) (x : V) {q : ℕ}
    (hk : 0 < evenNeighborCount G x)
    (hq : HasPathPartition (starDeleteEven G x) q) :
    ∃ r : ℕ, 2*r ≤ evenNeighborCount G x ∧ HasMixedPartitionAt G x q r := by
  classical
  let J := starDeleteEven G x
  let hJG : J ≤ G := starDeleteEven_le G x
  obtain ⟨D,hpath,hdec,hcard⟩ := hq
  let E := D.image (liftSubgraph hJG)
  have hEpath : ∀ H ∈ E, IsNonemptyPathSubgraph H := by
    intro H hH
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hH
    exact (hpath P hP).lift hJG
  have hEdis : Set.PairwiseDisjoint (E : Set G.Subgraph) Subgraph.edgeSet := by
    intro H hH K hK hne
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hK
    exact hdec.1 hP hQ (fun he => hne (he ▸ rfl))
  have hEcover : (⋃ H : E, H.val.edgeSet) = J.edgeSet := by
    rw [← hdec.2]
    ext e
    simp [E]
    rfl
  have hmissing : ∀ z ∈ evenNeighbors G x, ∀ H ∈ E, ¬ H.Adj x z := by
    intro z hz H hH hadj
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hH
    have hjadj : J.Adj x z := P.adj_sub hadj
    exact hjadj.2.1 ⟨rfl,(mem_evenNeighbors G x z).mp hz |>.2⟩
  have hend : ∀ v, G.Adj x v → ∃ H ∈ E, PathStartsAt H v := by
    intro v hv
    obtain ⟨P,hP,hpend⟩ := exists_pathStartsAt_of_odd D hpath hdec v
      (original_neighbor_odd_after_starDeleteEven G x v hv)
    exact ⟨liftSubgraph hJG P,Finset.mem_image.mpr ⟨P,hP,rfl⟩,hpend.lift hJG⟩
  obtain ⟨r,hr,hrest⟩ := restore_star_from_endpoint_partition E x (evenNeighbors G x)
    hEpath hEdis (Finset.card_pos.mp hk)
    (fun z hz => (mem_evenNeighbors G x z).mp hz |>.1) hmissing
    (by rw [hEcover]; exact starDeleteEven_edge_cover G x) hend
  exact ⟨r,hr,hrest.mono_parts (Finset.card_image_le.trans hcard)⟩

end Erdos583
end Source24_Erdos583_StarRestoreEven
/- END Erdos583.StarRestoreEven -/

/- BEGIN Erdos583.StarFamily; source SHA256 ca1f97072e52979f683d95799cf7eda088888322b5129c22e06252e976e55e49 -/
section Source25_Erdos583_StarFamily


/-! Actual simultaneous deletion of clean high-even stars on disjoint original
closed supports. This module proves graph accounting and a genuine deletion
trace; cycle conversion and path reconstruction remain separate. -/

noncomputable section
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

abbrev starFamilyDelete (G : SimpleGraph V) (R : Finset V) : SimpleGraph V :=
  isolateVertices G R

omit [Fintype V] in
theorem starFamilyDelete_center_isolated (G : SimpleGraph V) (R : Finset V)
    {x : V} (hx : x ∈ R) : (starFamilyDelete G R).IsIsolated x :=
  isolateVertices_isolated G R x hx

theorem star_support_away_family (G : SimpleGraph V) (x : V) (R : Finset V)
    (hdis : ∀ y ∈ R, Disjoint (closedNeighborhood G x) (closedNeighborhood G y))
    {v : V} (hv : v ∈ closedNeighborhood G x) :
    v ∉ R ∧ ∀ y ∈ R, ¬G.Adj v y := by
  constructor
  · intro hvR
    exact Finset.disjoint_left.mp (hdis v hvR) hv (by simp)
  · intro y hy hvy
    exact Finset.disjoint_left.mp (hdis y hy) hv
      ((mem_closedNeighborhood G y v).mpr (Or.inr hvy.symm))

theorem star_support_degree_unchanged (G : SimpleGraph V) (x : V) (R : Finset V)
    (hdis : ∀ y ∈ R, Disjoint (closedNeighborhood G x) (closedNeighborhood G y))
    {v : V} (hv : v ∈ closedNeighborhood G x) :
    (starFamilyDelete G R).degree v = G.degree v := by
  obtain ⟨hn, ha⟩ := star_support_away_family G x R hdis hv
  exact isolateVertices_degree_unchanged G R v hn ha

theorem starFamilyDelete_outside_degree (G : SimpleGraph V) (R : Finset V) (v : V)
    (hv : v ∉ R) (ha : ∀ x ∈ R, ¬G.Adj v x) :
    (starFamilyDelete G R).degree v = G.degree v :=
  isolateVertices_degree_unchanged G R v hv ha

theorem star_neighbor_not_center (G : SimpleGraph V) (R : Finset V)
    (hdis : (R : Set V).Pairwise
      (fun x y => Disjoint (closedNeighborhood G x) (closedNeighborhood G y)))
    {x v : V} (hx : x ∈ R) (hxv : G.Adj x v) : v ∉ R := by
  intro hv
  exact Finset.disjoint_left.mp (hdis hx hv hxv.ne)
    ((mem_closedNeighborhood G x v).mpr (Or.inr hxv)) (by simp)

theorem star_neighbor_unique_center (G : SimpleGraph V) (R : Finset V)
    (hdis : (R : Set V).Pairwise
      (fun x y => Disjoint (closedNeighborhood G x) (closedNeighborhood G y)))
    {x y v : V} (hx : x ∈ R) (hy : y ∈ R) (hxv : G.Adj x v) (hyv : G.Adj y v) :
    x = y := by
  by_contra hne
  exact Finset.disjoint_left.mp (hdis hx hy hne)
    ((mem_closedNeighborhood G x v).mpr (Or.inr hxv))
    ((mem_closedNeighborhood G y v).mpr (Or.inr hyv))

theorem starFamilyDelete_neighbors_of_neighbor (G : SimpleGraph V) (R : Finset V)
    (hdis : (R : Set V).Pairwise
      (fun x y => Disjoint (closedNeighborhood G x) (closedNeighborhood G y)))
    {x v : V} (hx : x ∈ R) (hxv : G.Adj x v) :
    (starFamilyDelete G R).neighborFinset v = (G.neighborFinset v).erase x := by
  have hvR := star_neighbor_not_center G R hdis hx hxv
  ext w
  simp only [mem_neighborFinset, isolateVertices_adj, Finset.mem_erase]
  constructor
  · rintro ⟨hvw, _, hwR⟩
    exact ⟨fun he => hwR (he ▸ hx), hvw⟩
  · rintro ⟨hwx, hvw⟩
    refine ⟨hvw, hvR, ?_⟩
    intro hwR
    exact hwx (star_neighbor_unique_center G R hdis hwR hx hvw.symm hxv)

theorem starFamilyDelete_degree_of_neighbor (G : SimpleGraph V) (R : Finset V)
    (hdis : (R : Set V).Pairwise
      (fun x y => Disjoint (closedNeighborhood G x) (closedNeighborhood G y)))
    {x v : V} (hx : x ∈ R) (hxv : G.Adj x v) :
    (starFamilyDelete G R).degree v = G.degree v - 1 := by
  rw [← card_neighborFinset_eq_degree, starFamilyDelete_neighbors_of_neighbor G R hdis hx hxv,
    Finset.card_erase_of_mem ((G.mem_neighborFinset v x).mpr hxv.symm), card_neighborFinset_eq_degree]

/-- A surviving original clean star remains a clean high-even star, with all
its original support degrees unchanged after the other deletions. -/
theorem surviving_highEvenCenter (G : SimpleGraph V) (x : V) (R : Finset V)
    (hx : x ∈ highEvenCenters G)
    (hdis : ∀ y ∈ R, Disjoint (closedNeighborhood G x) (closedNeighborhood G y)) :
    x ∈ highEvenCenters (starFamilyDelete G R) ∧
    (starFamilyDelete G R).degree x = G.degree x := by
  have hd := star_support_degree_unchanged G x R hdis (by simp : x ∈ closedNeighborhood G x)
  obtain ⟨he, hfour, hclean⟩ := (mem_highEvenCenters G x).mp hx
  refine ⟨(mem_highEvenCenters _ x).mpr ⟨hd ▸ he, hd ▸ hfour, ?_⟩, hd⟩
  intro v hxv
  have hgv : G.Adj x v := hxv.1
  rw [star_support_degree_unchanged G x R hdis
    ((mem_closedNeighborhood G x v).mpr (Or.inr hgv))]
  exact hclean v hgv

/-- At a clean center, deleting all even-neighbor edges deletes the full star. -/
theorem starDeleteEven_eq_isolate_singleton (G : SimpleGraph V) (x : V)
    (hclean : ∀ v, G.Adj x v → Even (G.degree v)) :
    starDeleteEven G x = isolateVertices G {x} := by
  ext u v
  simp only [starDeleteEven_adj, isolateVertices_adj, Finset.mem_singleton]
  constructor
  · rintro ⟨huv, h1, h2⟩
    refine ⟨huv, ?_, ?_⟩
    · intro hu; subst u; exact h1 ⟨rfl, hclean v huv⟩
    · intro hv; subst v; exact h2 ⟨rfl, hclean u huv.symm⟩
  · rintro ⟨huv, hu, hv⟩
    exact ⟨huv, fun h => hu h.1, fun h => hv h.1⟩

theorem starFamilyDelete_insert (G : SimpleGraph V) (R : Finset V) (x : V)
    (hclean : ∀ v, (starFamilyDelete G R).Adj x v →
      Even ((starFamilyDelete G R).degree v)) :
    starDeleteEven (starFamilyDelete G R) x = starFamilyDelete G (insert x R) := by
  rw [starDeleteEven_eq_isolate_singleton _ x hclean]
  ext u v
  simp only [isolateVertices_adj, Finset.mem_singleton, Finset.mem_insert]
  tauto

/-- Exact payment of one actual clean high-even star. -/
theorem phi_clean_star_exact (G : SimpleGraph V) (x : V) (hx : x ∈ highEvenCenters G) :
    phi G - phi (starDeleteEven G x) = (2 / 3 : ℚ) + (G.degree x : ℚ) / 6 := by
  obtain ⟨he, hfour, hclean⟩ := (mem_highEvenCenters G x).mp hx
  have hk := degree_eq_evenNeighborCount_of_clean G x hclean
  have hz : (starDeleteEven G x).degree x = 0 := by
    rw [degree_starDeleteEven_center, ← hk, Nat.sub_self]
  rw [phi_starDeleteEven_exact, ← hk, hz, parityWeight_zero,
    parityWeight_even_nonzero he (by omega)]
  ring

/-- A genuine sequence of full clean-star deletions. Each step records both
its current graph hypothesis and equality of current and ORIGINAL degree. -/
inductive CleanStarTrace (G : SimpleGraph V) : SimpleGraph V → Finset V → Prop
  | nil : CleanStarTrace G G ∅
  | snoc {H : SimpleGraph V} {R : Finset V} (tail : CleanStarTrace G H R)
      (x : V) (hne : x ∉ R) (hclean : x ∈ highEvenCenters H)
      (hdegree : H.degree x = G.degree x) :
      CleanStarTrace G (starDeleteEven H x) (insert x R)

theorem starFamilyDelete_trace (G : SimpleGraph V) (R : Finset V)
    (hR : R ⊆ highEvenCenters G)
    (hdis : (R : Set V).Pairwise
      (fun x y => Disjoint (closedNeighborhood G x) (closedNeighborhood G y))) :
    CleanStarTrace G (starFamilyDelete G R) R := by
  induction R using Finset.induction_on with
  | empty =>
    have heq : starFamilyDelete G ∅ = G := by ext u v; simp [isolateVertices_adj]
    rw [heq]
    exact CleanStarTrace.nil
  | @insert x R hne ih =>
    have hR' : R ⊆ highEvenCenters G := fun v hv => hR (Finset.mem_insert_of_mem hv)
    have hdis' : (R : Set V).Pairwise
        (fun x y => Disjoint (closedNeighborhood G x) (closedNeighborhood G y)) := by
      intro a ha b hb hab
      exact hdis (Finset.mem_insert_of_mem ha) (Finset.mem_insert_of_mem hb) hab
    have haway : ∀ y ∈ R, Disjoint (closedNeighborhood G x) (closedNeighborhood G y) := by
      intro y hy
      exact hdis (by simp) (Finset.mem_insert_of_mem hy) (by intro h; subst y; exact hne hy)
    obtain ⟨hc, hd⟩ := surviving_highEvenCenter G x R (hR (by simp)) haway
    have ht := CleanStarTrace.snoc (ih hR' hdis') x hne hc hd
    rwa [starFamilyDelete_insert G R x ((mem_highEvenCenters _ x).mp hc).2.2] at ht

theorem CleanStarTrace.phi_exact {G H : SimpleGraph V} {R : Finset V}
    (ht : CleanStarTrace G H R) :
    phi G - phi H = ∑ x ∈ R, ((2 / 3 : ℚ) + (G.degree x : ℚ) / 6) := by
  induction ht with
  | nil => simp
  | @snoc H R ht x hne hc hd ih =>
    have hp := phi_clean_star_exact H x hc
    rw [hd] at hp
    rw [Finset.sum_insert hne]
    linarith

theorem CleanStarTrace.edge_count {G H : SimpleGraph V} {R : Finset V}
    (ht : CleanStarTrace G H R) : H.edgeFinset.card + ∑ x ∈ R, G.degree x = G.edgeFinset.card := by
  induction ht with
  | nil => simp
  | @snoc H R ht x hne hc hd ih =>
    have he := edge_count_starDeleteEven H x
    have hk := degree_eq_evenNeighborCount_of_clean H x ((mem_highEvenCenters H x).mp hc).2.2
    rw [← hk, hd] at he
    rw [Finset.sum_insert hne]
    omega


theorem clean_star_parity_counts (G : SimpleGraph V) (x : V) (hx : x ∈ highEvenCenters G) :
    (oddVertices (starDeleteEven G x)).card = (oddVertices G).card + G.degree x ∧
    (isolatedVertices (starDeleteEven G x)).card = (isolatedVertices G).card + 1 ∧
    (nonisolatedEvenVertices (starDeleteEven G x)).card + G.degree x + 1 =
      (nonisolatedEvenVertices G).card := by
  obtain ⟨he,hfour,hclean⟩ := (mem_highEvenCenters G x).mp hx
  have hk := degree_eq_evenNeighborCount_of_clean G x hclean
  have hz : (starDeleteEven G x).degree x = 0 := by
    rw [degree_starDeleteEven_center, ← hk, Nat.sub_self]
  have hn : G.degree x ≠ 0 := by omega
  have ho := odd_count_starDeleteEven G x
  have hi := isolate_count_starDeleteEven G x
  have hv := even_count_starDeleteEven G x
  simp only [← hk, hz, Nat.not_odd_iff_even.mpr he, if_false, if_true, hn] at ho hi hv
  norm_num [he, hn] at ho hi hv
  exact ⟨ho, hi, hv⟩

theorem CleanStarTrace.parity_counts {G H : SimpleGraph V} {R : Finset V}
    (ht : CleanStarTrace G H R) :
    (oddVertices H).card = (oddVertices G).card + ∑ x ∈ R, G.degree x ∧
    (isolatedVertices H).card = (isolatedVertices G).card + R.card ∧
    (nonisolatedEvenVertices H).card + (∑ x ∈ R, G.degree x) + R.card =
      (nonisolatedEvenVertices G).card := by
  induction ht with
  | nil => simp
  | @snoc H R ht x hne hc hd ih =>
    obtain ⟨ho,hi,he⟩ := clean_star_parity_counts H x hc
    rw [hd] at ho he
    rw [Finset.sum_insert hne, Finset.card_insert_of_notMem hne]
    obtain ⟨iho,ihi,ihe⟩ := ih
    omega

theorem CleanStarTrace.subgraph {G H : SimpleGraph V} {R : Finset V}
    (ht : CleanStarTrace G H R) : H ≤ G := by
  induction ht with
  | nil => exact le_rfl
  | @snoc H R ht x hne hc hd ih => exact (starDeleteEven_le H x).trans ih

theorem CleanStarTrace.original_center_degrees {G H : SimpleGraph V} {R : Finset V}
    (ht : CleanStarTrace G H R) : ∀ x ∈ R, Even (G.degree x) ∧ 4 ≤ G.degree x := by
  induction ht with
  | nil => simp
  | @snoc H R ht x hne hc hd ih =>
    intro y hy
    rcases Finset.mem_insert.mp hy with hy | hy
    · subst y
      have h := (mem_highEvenCenters H x).mp hc
      rw [hd] at h
      exact ⟨h.1,h.2.1⟩
    · exact ih y hy

theorem starFamilyDelete_neighbor_odd_nonisolated (G : SimpleGraph V) (R : Finset V)
    (hR : R ⊆ highEvenCenters G)
    (hdis : (R : Set V).Pairwise
      (fun x y => Disjoint (closedNeighborhood G x) (closedNeighborhood G y)))
    {x v : V} (hx : x ∈ R) (hxv : G.Adj x v) :
    Odd ((starFamilyDelete G R).degree v) ∧ (starFamilyDelete G R).degree v ≠ 0 := by
  have he := ((mem_highEvenCenters G x).mp (hR hx)).2.2 v hxv
  have hm : v ∈ evenNeighbors G x := (mem_evenNeighbors G x v).mpr ⟨hxv, he⟩
  have htwo := selected_degree_ge_two G x v hm
  rw [starFamilyDelete_degree_of_neighbor G R hdis hx hxv]
  exact ⟨Nat.Even.sub_odd (by omega) he (by decide), by omega⟩

/-- Exact graph certificate for any supplied family of disjoint clean stars. -/
theorem star_family_certificate (G : SimpleGraph V) (R : Finset V)
    (hR : R ⊆ highEvenCenters G)
    (hdis : (R : Set V).Pairwise
      (fun x y => Disjoint (closedNeighborhood G x) (closedNeighborhood G y))) :
    CleanStarTrace G (starFamilyDelete G R) R ∧
    (∀ x ∈ R, (starFamilyDelete G R).IsIsolated x) ∧
    (∀ x ∈ R, ∀ v, G.Adj x v → (starFamilyDelete G R).degree v = G.degree v - 1) ∧
    (∀ v, v ∉ R → (∀ x ∈ R, ¬G.Adj v x) → (starFamilyDelete G R).degree v = G.degree v) ∧
    phi G - phi (starFamilyDelete G R) = ∑ x ∈ R, ((2 / 3 : ℚ) + (G.degree x : ℚ) / 6) ∧
    (starFamilyDelete G R).edgeFinset.card + ∑ x ∈ R, G.degree x = G.edgeFinset.card ∧
    (oddVertices (starFamilyDelete G R)).card = (oddVertices G).card + ∑ x ∈ R, G.degree x ∧
    (isolatedVertices (starFamilyDelete G R)).card = (isolatedVertices G).card + R.card ∧
    (nonisolatedEvenVertices (starFamilyDelete G R)).card + (∑ x ∈ R, G.degree x) + R.card =
      (nonisolatedEvenVertices G).card := by
  have ht := starFamilyDelete_trace G R hR hdis
  exact ⟨ht, fun _ hx => starFamilyDelete_center_isolated G R hx,
    fun _ hx _ hxv => starFamilyDelete_degree_of_neighbor G R hdis hx hxv,
    starFamilyDelete_outside_degree G R, ht.phi_exact, ht.edge_count, ht.parity_counts⟩

/-- The actual bounded-even-neighborhood packing supplies the graph reduction
and exact potential payment. It supplies no path/cycle conversion theorem. -/
theorem exists_bounded_core_star_reduction (G : SimpleGraph V) (K : ℕ)
    (hcap : ∀ v, evenNeighborCount G v ≤ K) :
    ∃ R ⊆ highEvenCenters G,
      (R : Set V).Pairwise
        (fun x y => Disjoint (closedNeighborhood G x) (closedNeighborhood G y)) ∧
      (highEvenCenters G).card ≤ (K^2+1) * R.card ∧
      CleanStarTrace G (starFamilyDelete G R) R ∧
      (∀ x ∈ R, (starFamilyDelete G R).IsIsolated x) ∧
      (∀ x ∈ R, ∀ v, G.Adj x v → (starFamilyDelete G R).degree v = G.degree v - 1) ∧
      (∀ v, v ∉ R → (∀ x ∈ R, ¬G.Adj v x) → (starFamilyDelete G R).degree v = G.degree v) ∧
      phi G - phi (starFamilyDelete G R) = ∑ x ∈ R, ((2 / 3 : ℚ) + (G.degree x : ℚ) / 6) ∧
      (starFamilyDelete G R).edgeFinset.card + ∑ x ∈ R, G.degree x = G.edgeFinset.card ∧
      (oddVertices (starFamilyDelete G R)).card = (oddVertices G).card + ∑ x ∈ R, G.degree x ∧
      (isolatedVertices (starFamilyDelete G R)).card = (isolatedVertices G).card + R.card ∧
      (nonisolatedEvenVertices (starFamilyDelete G R)).card + (∑ x ∈ R, G.degree x) + R.card =
        (nonisolatedEvenVertices G).card := by
  obtain ⟨R,hR,hd,hc⟩ := exists_highEvenCenters_packing G K hcap
  exact ⟨R,hR,hd,hc,star_family_certificate G R hR hd⟩

end Erdos583
end
end Source25_Erdos583_StarFamily
/- END Erdos583.StarFamily -/

/- BEGIN Erdos583.FourCycleConsumers; source SHA256 1df80d78a93ecbe8520527249e8851d333f83fa36ed68ae659930c94ab241f45 -/
section Source26_Erdos583_FourCycleConsumers




/-! Exact four-cycle repair costs and their consumers on actual star deletions.
All residual path bounds are supplied explicitly. No baseline decomposition
theorem is assumed. -/
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable

theorem four_cycle_fullstar_cost (k q : ℕ) (hk : 0 < k)
    (h₂ : k ≠ 2) (h₃ : k ≠ 3) (h₄ : k ≠ 4) (h₁₀ : k ≠ 10)
    (hq : 2*q ≤ k) :
    6*((q+3)/4) ≤ k + (if k%2 = 1 then 1 else 0) := by
  split_ifs <;> omega

theorem four_cycle_leaf_cost (k q : ℕ) (hk : k = 2 ∨ k = 10)
    (hq : 2*q ≤ k-1) : 6*((q+3)/4) ≤ k-2 := by
  rcases hk with rfl | rfl <;> omega

theorem four_cycle_large_cost (k q : ℕ) (hk : 48 ≤ k)
    (hq : 2*q ≤ k) : k + 48*((q+3)/4) ≤ 8*(k-1) := by
  omega

theorem four_cycle_clean_cost (d q : ℕ) (hd : 4 ≤ d)
    (hq : 2*q ≤ d) : 6*((q+3)/4) ≤ d+2 := by
  omega

/-- The exact natural-number payment contracts used by all four consumers. -/
theorem four_cycle_cost_bundle :
    (∀ k q : ℕ, 0 < k → k ≠ 2 → k ≠ 3 → k ≠ 4 → k ≠ 10 → 2*q ≤ k →
      6*((q+3)/4) ≤ k + (if k%2 = 1 then 1 else 0)) ∧
    (∀ k q : ℕ, (k = 2 ∨ k = 10) → 2*q ≤ k-1 → 6*((q+3)/4) ≤ k-2) ∧
    (∀ k q : ℕ, 48 ≤ k → 2*q ≤ k → k+48*((q+3)/4) ≤ 8*(k-1)) ∧
    (∀ d q : ℕ, 4 ≤ d → 2*q ≤ d → 6*((q+3)/4) ≤ d+2) :=
  ⟨four_cycle_fullstar_cost, four_cycle_leaf_cost, four_cycle_large_cost, four_cycle_clean_cost⟩

variable {V : Type*} [Fintype V]

/-- The stronger potential payment at an originally even center. -/
theorem phi_even_star_drop_four (G : SimpleGraph V) (x : V)
    (he : Even (G.degree x)) (hk : 0 < evenNeighborCount G x) :
    ((evenNeighborCount G x +
      (if evenNeighborCount G x % 2 = 1 then 1 else 0) : ℕ) : ℚ) / 6 ≤
      phi G - phi (starDeleteEven G x) := by
  classical
  have hkd := evenNeighborCount_le_degree G x
  rw [phi_starDeleteEven_exact, parityWeight_even_nonzero he (by omega)]
  by_cases ho : evenNeighborCount G x % 2 = 1
  · have hr : Odd ((starDeleteEven G x).degree x) := by
      rw [Nat.odd_iff, degree_starDeleteEven_center]
      have hd := Nat.even_iff.mp he
      omega
    simp [ho, parityWeight, hr, Nat.not_even_iff_odd.mpr hr]
    ring_nf
    exact le_rfl
  · simp only [ho, ↓reduceIte, Nat.add_zero]
    have hw := parityWeight_le_two_thirds ((starDeleteEven G x).degree x)
    linarith

/-- Full-star restoration at an originally even center outside the four
exceptional neighbor counts, from any supplied residual partition. -/
theorem restore_evenCenter_bound_four (G : SimpleGraph V) (x : V)
    (he : Even (G.degree x)) (hk : 0 < evenNeighborCount G x)
    (h₂ : evenNeighborCount G x ≠ 2) (h₃ : evenNeighborCount G x ≠ 3)
    (h₄ : evenNeighborCount G x ≠ 4) (h₁₀ : evenNeighborCount G x ≠ 10)
    {m : ℕ} (hpart : HasPathPartition (starDeleteEven G x) m) {b : ℚ}
    (hbound : (m : ℚ) ≤ phi (starDeleteEven G x) - b) :
    HasPathBound G (phi G - b) := by
  obtain ⟨q, hq, hmixed⟩ := restore_even_neighbor_star G x hk hpart
  have hcost := four_cycle_fullstar_cost (evenNeighborCount G x) q hk h₂ h₃ h₄ h₁₀ hq
  have hcostRat : (6 : ℚ) * (((q+3)/4 : ℕ) : ℚ) ≤
      ((evenNeighborCount G x +
        (if evenNeighborCount G x % 2 = 1 then 1 else 0) : ℕ) : ℚ) := by
    exact_mod_cast hcost
  have hphi := phi_even_star_drop_four G x he hk
  refine hasPathBound_iff_exists_partition.mpr
    ⟨m+(q+3)/4, hmixed.toPathPartition_four, ?_⟩
  push_cast
  linarith

theorem restore_evenCenter_phi_bound_four (G : SimpleGraph V) (x : V)
    (he : Even (G.degree x)) (hk : 0 < evenNeighborCount G x)
    (h₂ : evenNeighborCount G x ≠ 2) (h₃ : evenNeighborCount G x ≠ 3)
    (h₄ : evenNeighborCount G x ≠ 4) (h₁₀ : evenNeighborCount G x ≠ 10)
    {b : ℚ} (hbound : HasPathBound (starDeleteEven G x) (phi (starDeleteEven G x) - b)) :
    HasPathBound G (phi G - b) := by
  obtain ⟨m, hm, hmb⟩ := hasPathBound_iff_exists_partition.mp hbound
  exact restore_evenCenter_bound_four G x he hk h₂ h₃ h₄ h₁₀ hm hmb

/-- A center of either parity with at least 48 even neighbors yields an actual
restored path partition saving one forty-eighth per removed star edge. -/
theorem restore_largeEvenNeighbor_bound_four (G : SimpleGraph V) (x : V)
    (hk : 48 ≤ evenNeighborCount G x) {m : ℕ}
    (hpart : HasPathPartition (starDeleteEven G x) m) {b : ℚ}
    (hbound : (m : ℚ) ≤ phi (starDeleteEven G x) - b) :
    HasPathBound G (phi G - b - (evenNeighborCount G x : ℚ)/48) := by
  obtain ⟨q, hq, hmixed⟩ := restore_even_neighbor_star G x (by omega) hpart
  have hcost := four_cycle_large_cost (evenNeighborCount G x) q hk hq
  have hcostRat : (evenNeighborCount G x : ℚ) +
      48 * (((q+3)/4 : ℕ) : ℚ) ≤ 8 * ((evenNeighborCount G x-1 : ℕ) : ℚ) := by
    exact_mod_cast hcost
  rw [Nat.cast_sub (by omega)] at hcostRat
  norm_num at hcostRat
  have hphi := phi_starDeleteEven_drop G x
  refine hasPathBound_iff_exists_partition.mpr
    ⟨m+(q+3)/4, hmixed.toPathPartition_four, ?_⟩
  push_cast
  linarith

theorem restore_largeEvenNeighbor_phi_bound_four (G : SimpleGraph V) (x : V)
    (hk : 48 ≤ evenNeighborCount G x) {b : ℚ}
    (hbound : HasPathBound (starDeleteEven G x) (phi (starDeleteEven G x) - b)) :
    HasPathBound G (phi G - b - (evenNeighborCount G x : ℚ)/48) := by
  obtain ⟨m, hm, hmb⟩ := hasPathBound_iff_exists_partition.mp hbound
  exact restore_largeEvenNeighbor_bound_four G x hk hm hmb

/-- Restore an arbitrary supplied residual partition at a clean high-even star.
The exact potential decrease pays all cycle repair and saves one third. -/
theorem restore_highEvenCenter_bound_four (G : SimpleGraph V) (x : V)
    (hx : x ∈ highEvenCenters G) {m : ℕ}
    (hpart : HasPathPartition (starDeleteEven G x) m) {b : ℚ}
    (hbound : (m : ℚ) ≤ phi (starDeleteEven G x) - b) :
    HasPathBound G (phi G - b - 1/3) := by
  classical
  obtain ⟨he, hd, hclean⟩ := (mem_highEvenCenters G x).mp hx
  have hk := degree_eq_evenNeighborCount_of_clean G x hclean
  obtain ⟨q, hq, hmixed⟩ := restore_even_neighbor_star G x (by omega) hpart
  have hcost := four_cycle_clean_cost (G.degree x) q hd (by omega)
  have hcostRat : (6 : ℚ) * (((q+3)/4 : ℕ) : ℚ) ≤ (G.degree x : ℚ) + 2 := by
    exact_mod_cast hcost
  have hphi := phi_clean_star_exact G x hx
  refine hasPathBound_iff_exists_partition.mpr
    ⟨m+(q+3)/4, hmixed.toPathPartition_four, ?_⟩
  push_cast
  linarith

/-- Existential residual-bound interface to the same actual star restoration. -/
theorem restore_highEvenCenter_phi_bound_four (G : SimpleGraph V) (x : V)
    (hx : x ∈ highEvenCenters G) {b : ℚ}
    (hbound : HasPathBound (starDeleteEven G x) (phi (starDeleteEven G x) - b)) :
    HasPathBound G (phi G - b - 1/3) := by
  obtain ⟨m, hm, hmb⟩ := hasPathBound_iff_exists_partition.mp hbound
  exact restore_highEvenCenter_bound_four G x hx hm hmb

/-- An actual clean-star deletion trace restores all original edges while
saving one third for every distinct deleted center. -/
theorem CleanStarTrace.restore_phi_bound_four {G H : SimpleGraph V} {R : Finset V}
    (ht : CleanStarTrace G H R) {b : ℚ}
    (hbound : HasPathBound H (phi H - b)) :
    HasPathBound G (phi G - b - (R.card : ℚ)/3) := by
  classical
  induction ht generalizing b with
  | nil => simpa using hbound
  | @snoc H R ht x hne hx hdegree ih =>
    have hH := restore_highEvenCenter_phi_bound_four H x hx hbound
    have hH' : HasPathBound H (phi H - (b + 1/3)) := by
      convert hH using 1; ring
    have hG := ih hH'
    convert hG using 1
    rw [Finset.card_insert_of_notMem hne]
    push_cast
    ring

/-- Apply the trace consumer to a supplied family of disjoint original clean
stars. The residual bound is an explicit hypothesis. -/
theorem restore_starFamily_phi_bound_four (G : SimpleGraph V) (R : Finset V)
    (hR : R ⊆ highEvenCenters G)
    (hdis : (R : Set V).Pairwise
      (fun x y => Disjoint (closedNeighborhood G x) (closedNeighborhood G y)))
    {b : ℚ} (hbound : HasPathBound (starFamilyDelete G R) (phi (starFamilyDelete G R) - b)) :
    HasPathBound G (phi G - b - (R.card : ℚ)/3) :=
  (starFamilyDelete_trace G R hR hdis).restore_phi_bound_four hbound

end Erdos583
end Source26_Erdos583_FourCycleConsumers
/- END Erdos583.FourCycleConsumers -/

/- BEGIN Erdos583.LeafRestore; source SHA256 728094de26fc57b7955edcddcdddbfc446d3679dae38c04d2aae68787222ac1b -/
section Source27_Erdos583_LeafRestore



/-! Restoring the exceptional two- and ten-neighbor stars on actual graphs. -/
noncomputable section
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

theorem restore_leaf_exception_phi_bound (G : SimpleGraph V) {x a : V}
    (hxa : G.Adj x a) (ha : Even (G.degree a)) (hx : Even (G.degree x))
    (hk : evenNeighborCount G x = 2 ∨ evenNeighborCount G x = 10) {b : ℚ}
    (hbound : HasPathBound (starDeleteEven (attachLeaf G a) (some x))
      (phi (starDeleteEven (attachLeaf G a) (some x)) - b)) :
    HasPathBound G (phi G - b) := by
  classical
  obtain ⟨m,hm,hmb⟩ := hasPathBound_iff_exists_partition.mp hbound
  have hcnt := attachLeaf_evenNeighborCount G hxa ha
  have hkpos : 0 < evenNeighborCount (attachLeaf G a) (some x) := by omega
  obtain ⟨q,hq,hM⟩ := restore_even_neighbor_star (attachLeaf G a) (some x) hkpos hm
  have hcost := four_cycle_leaf_cost (evenNeighborCount G x) q hk (by omega)
  have hcost' : 6 * ((q+3)/4) + 2 ≤ evenNeighborCount G x := by
    rcases hk with hk | hk <;> omega
  have hrat : (6 : ℚ) * (((q+3)/4 : ℕ) : ℚ) + 2 ≤ evenNeighborCount G x := by
    exact_mod_cast hcost'
  have hkeven : Even (evenNeighborCount G x) := by rcases hk with hk | hk <;> norm_num [hk]
  have hphi := phi_attachLeaf_star G hxa ha hx hkeven
  refine hasPathBound_iff_exists_partition.mpr
    ⟨m+(q+3)/4,remove_attached_leaf_partition G a hM.toPathPartition_four,?_⟩
  push_cast
  linarith

end Erdos583
end
end Source27_Erdos583_LeafRestore
/- END Erdos583.LeafRestore -/

/- BEGIN Erdos583.EvenCore; source SHA256 c3e36cf0548416c825175534158e46409bb6db430fc6aac6a98afd3e7088b296 -/
section Source28_Erdos583_EvenCore




/-! The graph induced by the original even-degree vertices, on the original
ambient vertex type. Original odd vertices are retained as isolates. No path
bound, reduction premise, or published theorem is assumed here. -/

noncomputable section

namespace Erdos583

open SimpleGraph
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

def evenCore (G : SimpleGraph V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ Even (G.degree u) ∧ Even (G.degree v)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

@[simp] theorem evenCore_adj (G : SimpleGraph V) (u v : V) :
    (evenCore G).Adj u v ↔ G.Adj u v ∧ Even (G.degree u) ∧ Even (G.degree v) :=
  Iff.rfl

theorem evenCore_le (G : SimpleGraph V) : evenCore G ≤ G := fun _ _ h => h.1

theorem evenCore_neighborFinset_of_even (G : SimpleGraph V) (v : V)
    (hv : Even (G.degree v)) :
    (evenCore G).neighborFinset v = evenNeighbors G v := by
  ext w
  simp only [mem_neighborFinset, evenCore_adj, mem_evenNeighbors]
  tauto

theorem evenCore_neighborFinset_of_odd (G : SimpleGraph V) (v : V)
    (hv : Odd (G.degree v)) : (evenCore G).neighborFinset v = ∅ := by
  ext w
  simp only [mem_neighborFinset, evenCore_adj, Finset.notMem_empty, iff_false]
  exact fun h => (Nat.not_even_iff_odd.mpr hv) h.2.1

theorem evenCore_degree_of_even (G : SimpleGraph V) (v : V)
    (hv : Even (G.degree v)) :
    (evenCore G).degree v = evenNeighborCount G v := by
  rw [← card_neighborFinset_eq_degree, evenCore_neighborFinset_of_even G v hv]
  rfl

theorem evenCore_degree_of_odd (G : SimpleGraph V) (v : V)
    (hv : Odd (G.degree v)) : (evenCore G).degree v = 0 := by
  rw [← card_neighborFinset_eq_degree, evenCore_neighborFinset_of_odd G v hv]
  rfl

theorem evenCore_degree_le (G : SimpleGraph V) (v : V) :
    (evenCore G).degree v ≤ G.degree v := by
  apply Finset.card_le_card
  intro w hw
  exact (G.mem_neighborFinset v w).mpr (((evenCore G).mem_neighborFinset v w).mp hw).1

theorem evenCore_nonisolated_original (G : SimpleGraph V) (v : V)
    (hv : (evenCore G).degree v ≠ 0) : v ∈ nonisolatedEvenVertices G := by
  obtain ⟨w, hw⟩ := ((evenCore G).degree_pos_iff_exists_adj v).mp (Nat.pos_of_ne_zero hv)
  exact (mem_nonisolatedEvenVertices G v).mpr
    ⟨hw.2.1, ne_of_gt ((G.degree_pos_iff_exists_adj v).mpr ⟨w, hw.1⟩)⟩

theorem evenCore_support_subset (G : SimpleGraph V) :
    (evenCore G).support ⊆ {v | Even (G.degree v)} := by
  rintro v ⟨w, hw⟩
  exact hw.2.1

theorem evenCore_eq_spanningCoe_induce (G : SimpleGraph V) :
    evenCore G = (G.induce {v | Even (G.degree v)}).spanningCoe := by
  ext u v
  constructor
  · intro h
    exact ⟨h.1.ne, ⟨u, h.2.1⟩, ⟨v, h.2.2⟩, h.1, rfl, rfl⟩
  · rintro ⟨_, a, b, hab, rfl, rfl⟩
    exact ⟨hab, a.property, b.property⟩

theorem evenCore_induce_eq (G : SimpleGraph V) :
    (evenCore G).induce {v | Even (G.degree v)} =
      G.induce {v | Even (G.degree v)} := by
  rw [evenCore_eq_spanningCoe_induce, induce_spanningCoe]

omit [Fintype V] in
/-- Adding isolated vertices preserves native acyclicity. This support-based
form avoids any choice of an inverse to a subtype inclusion. -/
theorem isAcyclic_iff_induce_of_support_subset (H : SimpleGraph V) (s : Set V)
    (hs : H.support ⊆ s) : H.IsAcyclic ↔ (H.induce s).IsAcyclic := by
  constructor
  · exact fun h => h.induce s
  · intro h v p hp
    have hps : ∀ w ∈ p.support, w ∈ s := by
      intro w hw
      obtain ⟨e, he, hwe⟩ := Walk.mem_support_iff_exists_mem_edges_of_not_nil hp.not_nil |>.mp hw
      have heH := p.edges_subset_edgeSet he
      induction e using Sym2.ind with
      | _ a b =>
        have hab : H.Adj a b := heH
        rcases (Sym2.mem_iff).mp hwe with rfl | rfl
        · exact hs hab.left_mem_support
        · exact hs hab.right_mem_support
    apply h (p.induce s hps)
    apply Walk.IsCycle.of_map (f := (Embedding.induce s).toHom)
    simpa using hp

theorem evenCore_isAcyclic_iff (G : SimpleGraph V) :
    (evenCore G).IsAcyclic ↔ (G.induce {v | Even (G.degree v)}).IsAcyclic := by
  rw [isAcyclic_iff_induce_of_support_subset (evenCore G) _
    (evenCore_support_subset G), evenCore_induce_eq]

/-- These common contacts use parity in the ORIGINAL graph, not in its core. -/
def originalEvenCommonNeighbors (G : SimpleGraph V) (u v : V) : Finset V :=
  evenNeighbors G u ∩ evenNeighbors G v

@[simp] theorem mem_originalEvenCommonNeighbors (G : SimpleGraph V) (u v w : V) :
    w ∈ originalEvenCommonNeighbors G u v ↔
      G.Adj u w ∧ G.Adj v w ∧ Even (G.degree w) := by
  simp only [originalEvenCommonNeighbors, Finset.mem_inter, mem_evenNeighbors]
  tauto

theorem evenCore_commonNeighbors (G : SimpleGraph V) (u v : V)
    (hu : Even (G.degree u)) (hv : Even (G.degree v)) :
    (evenCore G).neighborFinset u ∩ (evenCore G).neighborFinset v =
      originalEvenCommonNeighbors G u v := by
  rw [evenCore_neighborFinset_of_even G u hu, evenCore_neighborFinset_of_even G v hv]
  rfl

theorem evenCore_commonNeighbors_card (G : SimpleGraph V) (u v : V)
    (hu : Even (G.degree u)) (hv : Even (G.degree v)) :
    ((evenCore G).neighborFinset u ∩ (evenCore G).neighborFinset v).card =
      (originalEvenCommonNeighbors G u v).card := by
  rw [evenCore_commonNeighbors G u v hu hv]

/-- The native induced graph has exactly the same ordinary degrees on its
vertices, and exactly the same original edges as the fixed-ambient core. -/
theorem evenCore_induced_degree (G : SimpleGraph V)
    (v : {v | Even (G.degree v)}) :
    (G.induce {v | Even (G.degree v)}).degree v = (evenCore G).degree v := by
  have h := degree_induce_of_support_subset (evenCore_support_subset G) v
  have heq := congrArg (fun H : SimpleGraph {v | Even (G.degree v)} => H.degree v)
    (evenCore_induce_eq G)
  exact heq.symm.trans h

theorem evenCore_induced_edge_card (G : SimpleGraph V) :
    (G.induce {v | Even (G.degree v)}).edgeFinset.card = (evenCore G).edgeFinset.card := by
  have h := card_edgeFinset_induce_of_support_subset (evenCore_support_subset G)
  have heq := congrArg (fun H : SimpleGraph {v | Even (G.degree v)} => H.edgeFinset.card)
    (evenCore_induce_eq G)
  exact heq.symm.trans h

theorem evenCore_component_nonisolated (G : SimpleGraph V)
    (C : (evenCore G).ConnectedComponent) {v : V} (hv : v ∈ C.supp)
    (hn : (evenCore G).degree v ≠ 0) {w : V} (hw : w ∈ C.supp) :
    (evenCore G).degree w ≠ 0 := by
  by_cases h : w = v
  · subst w
    exact hn
  · exact ne_of_gt (((evenCore G).degree_pos_iff_mem_support w).mpr
      (mem_support_of_reachable h (C.reachable_of_mem_supp hw hv)))

/-- A component containing a core edge consists entirely of vertices with
positive even ORIGINAL degree. Closure is in the CORE, not in the original
ambient graph, whose edges to odd vertices may leave this component. -/
theorem evenCore_component_certificate (G : SimpleGraph V)
    (C : (evenCore G).ConnectedComponent) {v : V} (hv : v ∈ C.supp)
    (hn : (evenCore G).degree v ≠ 0) :
    ∃ S : Finset V, (∀ w, w ∈ S ↔ w ∈ C.supp) ∧ v ∈ S ∧
      (∀ w ∈ S, ∀ z, (evenCore G).Adj w z → z ∈ S) ∧
      (∀ w ∈ S, (evenCore G).degree w ≠ 0 ∧ w ∈ nonisolatedEvenVertices G) := by
  refine ⟨C.supp.toFinset, ?_, ?_, ?_, ?_⟩
  · exact fun w => Set.mem_toFinset
  · exact Set.mem_toFinset.mpr hv
  · intro w hw z hwz
    exact Set.mem_toFinset.mpr (C.mem_supp_of_adj_mem_supp (Set.mem_toFinset.mp hw) hwz)
  · intro w hw
    have hnw := evenCore_component_nonisolated G C hv hn (Set.mem_toFinset.mp hw)
    exact ⟨hnw, evenCore_nonisolated_original G w hnw⟩

/-- Complete fixed-ambient certificate. The statements refer to actual graph
neighbors, degrees, edges, components, and native acyclicity. -/
theorem evenCore_certificate (G : SimpleGraph V) :
    evenCore G ≤ G ∧
    (∀ v, Even (G.degree v) →
      (evenCore G).neighborFinset v = evenNeighbors G v ∧
      (evenCore G).degree v = evenNeighborCount G v) ∧
    (∀ v, Odd (G.degree v) → (evenCore G).degree v = 0) ∧
    (∀ v, (evenCore G).degree v ≠ 0 → v ∈ nonisolatedEvenVertices G) ∧
    evenCore G = (G.induce {v | Even (G.degree v)}).spanningCoe ∧
    ((evenCore G).IsAcyclic ↔ (G.induce {v | Even (G.degree v)}).IsAcyclic) ∧
    (G.induce {v | Even (G.degree v)}).edgeFinset.card = (evenCore G).edgeFinset.card ∧
    (∀ u v, Even (G.degree u) → Even (G.degree v) →
      (evenCore G).neighborFinset u ∩ (evenCore G).neighborFinset v =
        originalEvenCommonNeighbors G u v) ∧
    (∀ (C : (evenCore G).ConnectedComponent) (v : V), v ∈ C.supp →
      (evenCore G).degree v ≠ 0 →
      ∃ S : Finset V, (∀ w, w ∈ S ↔ w ∈ C.supp) ∧ v ∈ S ∧
        (∀ w ∈ S, ∀ z, (evenCore G).Adj w z → z ∈ S) ∧
        (∀ w ∈ S, (evenCore G).degree w ≠ 0 ∧ w ∈ nonisolatedEvenVertices G)) := by
  exact ⟨evenCore_le G,
    fun v hv => ⟨evenCore_neighborFinset_of_even G v hv, evenCore_degree_of_even G v hv⟩,
    evenCore_degree_of_odd G, evenCore_nonisolated_original G,
    evenCore_eq_spanningCoe_induce G, evenCore_isAcyclic_iff G,
    evenCore_induced_edge_card G, evenCore_commonNeighbors G,
    fun C _ hv hn => evenCore_component_certificate G C hv hn⟩

end Erdos583
end
end Source28_Erdos583_EvenCore
/- END Erdos583.EvenCore -/

/- BEGIN Erdos583.Mixed; source SHA256 1c0382c2adbfc6bdab414ede3c4be7b023cfa757bbd178ca705147e05d346d01 -/
section Source29_Erdos583_Mixed



/-! Unrooted mixed path/cycle partitions and their exact endpoint budget.
No mixed-decomposition existence theorem is assumed here. -/

noncomputable section

namespace Erdos583

open SimpleGraph
attribute [local instance] Classical.propDecidable

variable {V : Type*} {G : SimpleGraph V}

def IsCycleSubgraph (H : G.Subgraph) : Prop := ∃ x, IsRootedCycleSubgraph x H

def HasMixedBound (G : SimpleGraph V) (b : ℚ) : Prop :=
  ∃ P C : Finset G.Subgraph,
    (∀ H ∈ P, IsNonemptyPathSubgraph H) ∧
    (∀ H ∈ C, IsCycleSubgraph H) ∧
    Disjoint P C ∧ IsDecomposition G (P ∪ C) ∧
    ((P.card + C.card : ℕ) : ℚ) ≤ b

theorem HasMixedBound.mono {a b : ℚ} (h : HasMixedBound G a) (hab : a ≤ b) :
    HasMixedBound G b := by
  obtain ⟨P, C, hp, hc, hd, he, hcard⟩ := h
  exact ⟨P, C, hp, hc, hd, he, hcard.trans hab⟩

theorem hasMixedBound_bot {V : Type*} : HasMixedBound (⊥ : SimpleGraph V) 0 := by
  exact ⟨∅, ∅, by simp, by simp, by simp,
    by simp [IsDecomposition], by simp⟩

theorem HasPathBound.toMixedBound {b : ℚ} (h : HasPathBound G b) : HasMixedBound G b := by
  obtain ⟨P, hp, hd, hc⟩ := h
  exact ⟨P, ∅, hp, by simp, by simp, by simpa using hd, by simpa using hc⟩

theorem HasMixedPartitionAt.toMixedBound {x : V} {a q : ℕ}
    (h : HasMixedPartitionAt G x a q) : HasMixedBound G (a : ℚ) := by
  obtain ⟨P, C, hp, hc, hd, he, hcard, _⟩ := h
  exact ⟨P, C, hp, fun H hH => ⟨x, hc H hH⟩, hd, he, by exact_mod_cast hcard⟩

variable [Fintype V]

theorem cycleSubgraph_degree {x : V} (p : G.Walk x x) (hp : p.IsCycle) (v : V) :
    p.toSubgraph.degree v = if v ∈ p.support then 2 else 0 := by
  by_cases hv : v ∈ p.support
  · rw [if_pos hv, Subgraph.degree, Set.fintypeCard_eq_ncard]
    exact hp.ncard_neighborSet_toSubgraph_eq_two hv
  · rw [if_neg hv]
    exact Subgraph.degree_of_notMem_verts (by simpa using hv)

theorem IsCycleSubgraph.even_degree {H : G.Subgraph} (hH : IsCycleSubgraph H) (v : V) :
    Even (H.degree v) := by
  obtain ⟨x, p, hp, rfl⟩ := hH
  rw [cycleSubgraph_degree p hp v]
  split_ifs <;> decide

theorem endpointCount_odd_iff_sum (P : Finset G.Subgraph)
    (hp : ∀ H ∈ P, IsNonemptyPathSubgraph H) (v : V) :
    Odd (endpointCount P v) ↔ Odd (∑ H ∈ P, H.degree v) := by
  rw [Finset.odd_sum_iff_odd_card_odd]
  unfold endpointCount
  have hf : P.filter (fun H => PathStartsAt H v) = P.filter (fun H => Odd (H.degree v)) := by
    apply Finset.filter_congr
    intro H hH
    exact pathStartsAt_iff_odd_degree v (hp H hH)
  rw [hf]

theorem endpointCount_odd_iff_mixed (P C : Finset G.Subgraph)
    (hp : ∀ H ∈ P, IsNonemptyPathSubgraph H)
    (hc : ∀ H ∈ C, IsCycleSubgraph H) (hPC : Disjoint P C)
    (hd : IsDecomposition G (P ∪ C)) (v : V) :
    Odd (endpointCount P v) ↔ Odd (G.degree v) := by
  rw [endpointCount_odd_iff_sum P hp v, degree_eq_sum_of_decomposition (P ∪ C) hd v,
    Finset.sum_union hPC]
  have he : Even (∑ H ∈ C, H.degree v) := Finset.even_sum (fun H => H.degree v)
    (fun H hH => (hc H hH).even_degree v)
  constructor
  · exact fun h => h.add_even he
  · intro h
    rcases h with ⟨j, hj⟩
    rcases he with ⟨k, hk⟩
    exact Nat.odd_iff.mpr (by omega)

/-- In EVERY mixed partition an odd vertex is an endpoint of an actual path
member. Arbitrary saved cycles cannot consume its odd endpoint requirement. -/
theorem exists_pathStartsAt_of_odd_mixed (P C : Finset G.Subgraph)
    (hp : ∀ H ∈ P, IsNonemptyPathSubgraph H)
    (hc : ∀ H ∈ C, IsCycleSubgraph H) (hPC : Disjoint P C)
    (hd : IsDecomposition G (P ∪ C)) (v : V) (ho : Odd (G.degree v)) :
    ∃ H ∈ P, PathStartsAt H v := by
  have hodd := (endpointCount_odd_iff_mixed P C hp hc hPC hd v).mpr ho
  obtain ⟨H, hH⟩ := Finset.card_pos.mp hodd.pos
  exact ⟨H, (Finset.mem_filter.mp hH).1, (Finset.mem_filter.mp hH).2⟩

theorem path_endpoint_vertices_card {H : G.Subgraph} (hH : IsNonemptyPathSubgraph H) :
    (Finset.univ.filter (PathStartsAt H)).card = 2 := by
  obtain ⟨a, b, p, hp, hn, rfl⟩ := hH
  have hset : Finset.univ.filter (PathStartsAt p.toSubgraph) = {a,b} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      pathStartsAt_iff_endpoints p hp hn v, Finset.mem_insert, Finset.mem_singleton]
  rw [hset]
  simp [hp.nil_iff_eq.not.mp hn]

theorem sum_endpointCount (P : Finset G.Subgraph)
    (hp : ∀ H ∈ P, IsNonemptyPathSubgraph H) :
    (∑ v : V, endpointCount P v) = 2 * P.card := by
  classical
  have hs : (∑ v : V, endpointCount P v) =
      ∑ H ∈ P, (Finset.univ.filter (PathStartsAt H)).card := by
    simp only [endpointCount, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  rw [hs, Finset.sum_congr rfl (fun H hH => path_endpoint_vertices_card (hp H hH))]
  simp [Nat.mul_comm]

theorem mixed_odd_count_le_endpoints (P C : Finset G.Subgraph)
    (hp : ∀ H ∈ P, IsNonemptyPathSubgraph H)
    (hc : ∀ H ∈ C, IsCycleSubgraph H) (hPC : Disjoint P C)
    (hd : IsDecomposition G (P ∪ C)) :
    (oddVertices G).card ≤ 2 * P.card := by
  have hpoint (v : V) : (if Odd (G.degree v) then 1 else 0) ≤ endpointCount P v := by
    by_cases ho : Odd (G.degree v)
    · have hh := (endpointCount_odd_iff_mixed P C hp hc hPC hd v).mpr ho |>.pos
      simp only [if_pos ho]
      omega
    · simp [ho]
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun v _ => hpoint v)
  rw [sum_endpointCount P hp] at hs
  simpa [oddVertices] using hs

/-- If the mixed-piece budget is saturated by odd vertices, there are no
cycles and no path endpoint at any even-degree vertex. -/
theorem mixed_endpoint_saturation (P C : Finset G.Subgraph)
    (hp : ∀ H ∈ P, IsNonemptyPathSubgraph H)
    (hc : ∀ H ∈ C, IsCycleSubgraph H) (hPC : Disjoint P C)
    (hd : IsDecomposition G (P ∪ C))
    (hbudget : 2 * (P.card + C.card) ≤ (oddVertices G).card) :
    C = ∅ ∧ ∀ v, ¬Odd (G.degree v) → endpointCount P v = 0 := by
  have hodd := mixed_odd_count_le_endpoints P C hp hc hPC hd
  have hC : C.card = 0 := by omega
  refine ⟨Finset.card_eq_zero.mp hC, ?_⟩
  intro y hy
  by_contra hne
  have hpoint (v : V) : (if Odd (G.degree v) then 1 else 0) +
      (if v = y then 1 else 0) ≤ endpointCount P v := by
    by_cases hv : v = y
    · subst v
      simp only [if_neg hy, ite_true, zero_add]
      omega
    · simp only [if_neg hv, add_zero]
      by_cases ho : Odd (G.degree v)
      · have hh := (endpointCount_odd_iff_mixed P C hp hc hPC hd v).mpr ho |>.pos
        simp only [if_pos ho]
        omega
      · simp [ho]
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun v _ => hpoint v)
  rw [Finset.sum_add_distrib, sum_endpointCount P hp] at hs
  have hcount : (∑ v : V, if Odd (G.degree v) then 1 else 0) = (oddVertices G).card := by
    simp [oddVertices]
  rw [hcount] at hs
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hs
  omega

end Erdos583
end
end Source29_Erdos583_Mixed
/- END Erdos583.Mixed -/

/- BEGIN Erdos583.OddExchange; source SHA256 4d19be8c6f630475c49d2c73be1d4a4f49ddabda7d5f8fa6f46dbadf571dbff7 -/
section Source30_Erdos583_OddExchange



/-! Odd-neighbor chains for cycle-removing exchanges. Choices are made only
at odd neighbors, never at an arbitrary even neighbor. -/

noncomputable section
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
theorem pathFamily_of_indexed {ι : Type*} [Fintype ι]
    (out : ι → G.Subgraph) (hp : ∀ i, IsNonemptyPathSubgraph (out i))
    (hd : Pairwise fun i j => Disjoint (out i).edgeSet (out j).edgeSet) :
    ∃ Q : Finset G.Subgraph, (∀ H ∈ Q, IsNonemptyPathSubgraph H) ∧
      Set.PairwiseDisjoint (Q : Set G.Subgraph) Subgraph.edgeSet ∧
      (⋃ H : Q, H.val.edgeSet) = (⋃ i, (out i).edgeSet) ∧ Q.card ≤ Fintype.card ι := by
  classical
  refine ⟨Finset.univ.image out, ?_, ?_, ?_, ?_⟩
  · intro H hH
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    exact hp i
  · intro H hH J hJ hne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hJ
    exact hd (fun h => hne (h ▸ rfl))
  · ext e
    simp
  · exact Finset.card_image_le.trans (by simp)

structure OddEndpointSelection (D : Finset G.Subgraph) (x : V) where
  owner : {v // G.Adj x v ∧ Odd (G.degree v)} → D
  presentation : ∀ H : D, PathPresentation H.val
  starts : ∀ v, PathStartsAt (owner v).val v.val

def oddEndpointSelection (P C : Finset G.Subgraph) (x : V)
    (hp : ∀ H ∈ P, IsNonemptyPathSubgraph H)
    (hc : ∀ H ∈ C, IsCycleSubgraph H) (hPC : Disjoint P C)
    (hd : IsDecomposition G (P ∪ C)) : OddEndpointSelection P x := by
  classical
  choose owner hm hs using (fun v : {v // G.Adj x v ∧ Odd (G.degree v)} =>
    exists_pathStartsAt_of_odd_mixed P C hp hc hPC hd v.val v.property.2)
  exact ⟨fun v => ⟨owner v, hm v⟩, fun H => pathPresentation (hp H.val H.property), hs⟩

namespace OddEndpointSelection
variable {D : Finset G.Subgraph} {x : V}

def predecessor (S : OddEndpointSelection D x) (v : V) : Option V :=
  if hv : G.Adj x v ∧ Odd (G.degree v) then
    (S.presentation (S.owner ⟨v,hv⟩)).predecessor x v else none

theorem predecessor_edge (S : OddEndpointSelection D x) {v y : V}
    (h : S.predecessor v = some y) :
    ∃ hv : G.Adj x v ∧ Odd (G.degree v), (S.owner ⟨v,hv⟩).val.Adj x y := by
  unfold predecessor at h
  split at h
  · rename_i hv
    exact ⟨hv, (S.presentation (S.owner ⟨v,hv⟩)).predecessor_adj x v y h⟩
  · contradiction

theorem predecessor_injective (S : OddEndpointSelection D x)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) Subgraph.edgeSet)
    (a b y : V) (ha : S.predecessor a = some y) (hb : S.predecessor b = some y) : a = b := by
  obtain ⟨hxa, hea⟩ := S.predecessor_edge ha
  obtain ⟨hxb, heb⟩ := S.predecessor_edge hb
  have ho : S.owner ⟨a,hxa⟩ = S.owner ⟨b,hxb⟩ := by
    apply Subtype.ext
    by_contra hn
    exact Set.disjoint_left.mp (hd (S.owner ⟨a,hxa⟩).property
      (S.owner ⟨b,hxb⟩).property hn)
      (show s(x,y) ∈ (S.owner ⟨a,hxa⟩).val.edgeSet from hea)
      (show s(x,y) ∈ (S.owner ⟨b,hxb⟩).val.edgeSet from heb)
  simp only [predecessor, dif_pos hxa] at ha
  simp only [predecessor, dif_pos hxb] at hb
  rw [ho] at ha
  exact (S.presentation (S.owner ⟨b,hxb⟩)).predecessor_injective x a b y ha hb

theorem source_outside_image (S : OddEndpointSelection D x) {z : V}
    (hz : ∀ H ∈ D, ¬H.Adj x z) : ∀ a, S.predecessor a ≠ some z := by
  intro a ha
  obtain ⟨hv, he⟩ := S.predecessor_edge ha
  exact hz _ (S.owner ⟨a,hv⟩).property he

theorem predecessor_none_iff (S : OddEndpointSelection D x) {v : V}
    (hv : G.Adj x v ∧ Odd (G.degree v)) :
    S.predecessor v = none ↔ x ∉ (S.presentation (S.owner ⟨v,hv⟩)).walk.support := by
  let P := S.presentation (S.owner ⟨v,hv⟩)
  have he : v = P.start ∨ v = P.finish := by
    apply (pathStartsAt_iff_endpoints P.walk P.isPath P.nonempty v).mp
    rw [P.toSubgraph_eq]
    exact S.starts ⟨v,hv⟩
  simp only [predecessor, dif_pos hv]
  change P.predecessor x v = none ↔ x ∉ P.walk.support
  simp [PathPresentation.predecessor, he, hv.1.ne.symm]

theorem reachable_adj (S : OddEndpointSelection D x) {z v : V}
    (hz : G.Adj x z) (n : ℕ)
    (hn : (partialStep S.predecessor)^[n] (some z) = some v) : G.Adj x v := by
  cases n with
  | zero => exact Option.some.inj hn ▸ hz
  | succ n =>
    rw [Function.iterate_succ_apply'] at hn
    cases he : (partialStep S.predecessor)^[n] (some z) with
    | none => simp [he, partialStep] at hn
    | some w =>
      obtain ⟨hv, hw⟩ := S.predecessor_edge (by simpa [he, partialStep] using hn)
      exact (S.owner ⟨w,hv⟩).val.adj_sub hw

/-- Two distinct source edges outside the path family give two distinct
terminal neighbors. Each is even, or has a selected path avoiding the root. -/
theorem two_terminals (S : OddEndpointSelection D x)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) Subgraph.edgeSet)
    {a b : V} (hab : a ≠ b) (ha : G.Adj x a) (hb : G.Adj x b)
    (hsa : ∀ H ∈ D, ¬H.Adj x a) (hsb : ∀ H ∈ D, ¬H.Adj x b) :
    ∃ t u, t ≠ u ∧ G.Adj x t ∧ G.Adj x u ∧
      S.predecessor t = none ∧ S.predecessor u = none ∧
      (∃ n, (partialStep S.predecessor)^[n] (some a) = some t) ∧
      (∃ n, (partialStep S.predecessor)^[n] (some b) = some u) := by
  obtain ⟨n,t,hnt,ht⟩ := partialChain_terminal S.predecessor
    (S.predecessor_injective hd) a (S.source_outside_image hsa)
  obtain ⟨m,u,hmu,hu⟩ := partialChain_terminal S.predecessor
    (S.predecessor_injective hd) b (S.source_outside_image hsb)
  refine ⟨t,u,?_,S.reachable_adj ha n hnt,S.reachable_adj hb m hmu,
    ht,hu,⟨n,hnt⟩,⟨m,hmu⟩⟩
  intro htu
  exact hab (partialChain_meeting S.predecessor (S.predecessor_injective hd)
    a b (S.source_outside_image hsa) (S.source_outside_image hsb) n m t hnt
    (hmu.trans (congrArg some htu.symm))).1

def chainSelected (S : OddEndpointSelection D x) (z : V) (H : D) : Set V :=
  {v | ChainReachable S.predecessor {z} v ∧
    ∃ hv : G.Adj x v ∧ Odd (G.degree v), S.owner ⟨v,hv⟩ = H}

theorem chainSelected_subset (S : OddEndpointSelection D x) (z : V) (H : D) :
    S.chainSelected z H ⊆ {(S.presentation H).start,(S.presentation H).finish} := by
  intro v hv
  obtain ⟨hvo,he⟩ := hv.2
  have hs := S.starts ⟨v,hvo⟩
  rw [he, ← (S.presentation H).toSubgraph_eq] at hs
  exact (pathStartsAt_iff_endpoints (S.presentation H).walk
    (S.presentation H).isPath (S.presentation H).nonempty v).mp hs

theorem chainSelected_predecessor (S : OddEndpointSelection D x) (z : V) (H : D)
    {v : V} (hv : v ∈ S.chainSelected z H) :
    S.predecessor v = (S.presentation H).predecessor x v := by
  obtain ⟨hvo,he⟩ := hv.2
  simp only [predecessor, dif_pos hvo]
  rw [he]

/-- A single selected chain cannot select both ends of a root-avoiding path:
both ends would be its unique terminal. Therefore it creates no cycles. -/
theorem realize_chainSelected (S : OddEndpointSelection D x) (z : V) (H : D) :
    ∃ Q : G.Subgraph, IsNonemptyPathSubgraph Q ∧
      Q.edgeSet = (S.presentation H).selectedEdges x (S.chainSelected z H) := by
  obtain ⟨Q,hp,_,he⟩ := (S.presentation H).realize_selected x (S.chainSelected z H)
    (S.chainSelected_subset z H) (fun _ hv => hv.2.choose.1)
  refine ⟨Q,hp ?_,he⟩
  rintro ⟨ha,hb,hx⟩
  have terminal (v : V) (hv : v ∈ S.chainSelected z H) : S.predecessor v = none := by
    rw [S.chainSelected_predecessor z H hv]
    simp [PathPresentation.predecessor, hx]
  obtain ⟨za,hza,n,hn⟩ := ha.1
  obtain ⟨zb,hzb,m,hm⟩ := hb.1
  have haz : za = z := Finset.mem_singleton.mp hza
  have hbz : zb = z := Finset.mem_singleton.mp hzb
  subst za
  subst zb
  have hab := partialChain_terminal_unique S.predecessor z
    (S.presentation H).start (S.presentation H).finish n m hn
    (terminal _ ha) hm (terminal _ hb)
  exact (S.presentation H).nonempty ((S.presentation H).isPath.nil_iff_eq.mpr hab)

def exchangeOwner (S : OddEndpointSelection D x) (v : V) : Option D :=
  if hv : G.Adj x v ∧ Odd (G.degree v) then some (S.owner ⟨v,hv⟩) else none

def exchangeOld (D : Finset G.Subgraph) (cut : G.Subgraph) : Option D → Set (Sym2 V)
  | none => cut.edgeSet
  | some H => H.val.edgeSet

def exchangeEdges (S : OddEndpointSelection D x) (z : V) (cut : G.Subgraph)
    (i : Option D) : Set (Sym2 V) :=
  edgeTransaction (exchangeOld D cut) (fun v => s(x,v)) S.exchangeOwner
    S.predecessor {v | ChainReachable S.predecessor {z} v} i

theorem exchangeOwner_some_iff (S : OddEndpointSelection D x) (v : V) (H : D) :
    S.exchangeOwner v = some H ↔
      ∃ hv : G.Adj x v ∧ Odd (G.degree v), S.owner ⟨v,hv⟩ = H := by
  unfold exchangeOwner
  split <;> simp_all

theorem exchangeOwner_none_iff (S : OddEndpointSelection D x) {v : V}
    (hv : G.Adj x v) : S.exchangeOwner v = none ↔ ¬Odd (G.degree v) := by
  simp [exchangeOwner, hv]

theorem selectedEdges_eq_exchangeEdges (S : OddEndpointSelection D x) (z : V)
    (cut : G.Subgraph) (H : D) :
    (S.presentation H).selectedEdges x (S.chainSelected z H) =
      S.exchangeEdges z cut (some H) := by
  have hremove :
      {e | ∃ v ∈ S.chainSelected z H, e ∈ (S.presentation H).predecessorEdges x v} =
      {e | ∃ v, ChainReachable S.predecessor {z} v ∧
        S.exchangeOwner v = some H ∧ ∃ w, S.predecessor v = some w ∧ s(x,w) = e} := by
    ext e
    constructor
    · rintro ⟨v,hv,w,hw,he⟩
      exact ⟨v,hv.1,(S.exchangeOwner_some_iff v H).mpr hv.2,w,
        (S.chainSelected_predecessor z H hv).trans hw,he⟩
    · rintro ⟨v,hvr,hvo,w,hw,he⟩
      have hv : v ∈ S.chainSelected z H :=
        ⟨hvr,(S.exchangeOwner_some_iff v H).mp hvo⟩
      exact ⟨v,hv,w,(S.chainSelected_predecessor z H hv).symm.trans hw,he⟩
  unfold PathPresentation.selectedEdges
  rw [hremove]
  unfold exchangeEdges edgeTransaction exchangeOld
  congr 1
  ext e
  simp only [chainSelected, Set.mem_ofPred_eq, exchangeOwner_some_iff]
  aesop

theorem exchangeEdges_partition (S : OddEndpointSelection D x) (z : V)
    (cut : G.Subgraph)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) Subgraph.edgeSet)
    (hcut : ∀ H ∈ D, Disjoint cut.edgeSet H.edgeSet)
    (hsource : ∀ H ∈ D, ¬H.Adj x z) (hcsource : ¬cut.Adj x z) :
    (Pairwise fun i j => Disjoint (S.exchangeEdges z cut i) (S.exchangeEdges z cut j)) ∧
      (⋃ i, S.exchangeEdges z cut i) =
        cut.edgeSet ∪ (⋃ H : D, H.val.edgeSet) ∪ {s(x,z)} := by
  have hold : Pairwise fun i j : Option D =>
      Disjoint (exchangeOld D cut i) (exchangeOld D cut j) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some J => exact hcut J.val J.property
    | some I =>
      cases j with
      | none => exact (hcut I.val I.property).symm
      | some J =>
        exact hd I.property J.property (fun he => hij (congrArg some (Subtype.ext he)))
  have htrans := edgeTransaction_partition (exchangeOld D cut) (fun v => s(x,v))
    S.exchangeOwner S.predecessor {v | ChainReachable S.predecessor {z} v} {z}
    (Sym2.mkEmbedding x).injective hold
    (fun v hv => chainReachable_source S.predecessor {z} (by simpa using hv))
    (by
      intro v hv i
      have hvz : v = z := Set.mem_singleton_iff.mp hv
      subst v
      cases i with
      | none => exact hcsource
      | some I => exact hsource I.val I.property)
    (by
      intro u _ v huv
      obtain ⟨hu,he⟩ := S.predecessor_edge huv
      simpa only [exchangeOwner, dif_pos hu, exchangeOld] using
        (show s(x,v) ∈ (S.owner ⟨u,hu⟩).val.edgeSet from he))
    (fun _ hu _ huv => chainReachable_successor S.predecessor {z} hu huv)
    (fun v hv hn => chainReachable_predecessor S.predecessor {z} hv (by simpa using hn))
  refine ⟨htrans.1, ?_⟩
  change (⋃ i, edgeTransaction _ _ _ _ _ i) = _
  rw [htrans.2]
  simp only [Set.image_singleton]
  congr 1
  ext e
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i,hi⟩
    cases i with
    | none => exact Or.inl hi
    | some H => exact Or.inr ⟨H,hi⟩
  · rintro (he | ⟨H,he⟩)
    · exact ⟨none,he⟩
    · exact ⟨some H,he⟩

/-- The designated opened cycle receives only the terminal edge, and only
when that terminal is even. It never loses another edge in the transaction. -/
theorem exchangeEdges_none (S : OddEndpointSelection D x) (z t : V)
    (cut : G.Subgraph) (hz : G.Adj x z)
    (ht : S.predecessor t = none)
    (htreach : ChainReachable S.predecessor {z} t) :
    S.exchangeEdges z cut none = cut.edgeSet ∪
      (if Odd (G.degree t) then ∅ else {s(x,t)}) := by
  have removed : {e | ∃ u, ChainReachable S.predecessor {z} u ∧
      S.exchangeOwner u = none ∧ ∃ v, S.predecessor u = some v ∧ s(x,v) = e} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro e ⟨u,_,ho,v,huv,_⟩
    obtain ⟨hu,_⟩ := S.predecessor_edge huv
    simp [exchangeOwner,hu] at ho
  have unique (v : V) (hv : ChainReachable S.predecessor {z} v)
      (ho : S.exchangeOwner v = none) : v = t := by
    have hvnone : S.predecessor v = none := by
      unfold exchangeOwner at ho
      split at ho
      · contradiction
      · rename_i hh
        simp [predecessor,hh]
    obtain ⟨a,ha,n,hn⟩ := hv
    obtain ⟨b,hb,m,hm⟩ := htreach
    have haz : a = z := Finset.mem_singleton.mp ha
    have hbz : b = z := Finset.mem_singleton.mp hb
    subst a
    subst b
    exact partialChain_terminal_unique S.predecessor z v t n m hn hvnone hm ht
  have hxt : G.Adj x t := by
    obtain ⟨a,ha,n,hn⟩ := htreach
    have haz : a = z := Finset.mem_singleton.mp ha
    subst a
    exact S.reachable_adj hz n hn
  unfold exchangeEdges edgeTransaction
  simp only [Set.mem_ofPred_eq]
  rw [removed]
  simp only [Set.sdiff_empty, exchangeOld]
  congr 1
  ext e
  by_cases hot : Odd (G.degree t)
  · simp only [if_pos hot, Set.mem_empty_iff_false, iff_false]
    rintro ⟨v,hv,ho,_⟩
    have hvt := unique v hv ho
    subst v
    exact ((S.exchangeOwner_none_iff hxt).mp ho) hot
  · simp only [if_neg hot, Set.mem_singleton_iff]
    constructor
    · rintro ⟨v,hv,ho,he⟩
      exact he.symm.trans (congrArg (fun w => s(x,w)) (unique v hv ho))
    · intro he
      exact ⟨t,htreach,(S.exchangeOwner_none_iff hxt).mpr hot,he.symm⟩

/-- One bad terminal opens a designated cycle into a path, with exact edge
coverage and no increase in total pieces. Old paths may be chosen at both ends. -/
theorem remove_cycle_along_chain (S : OddEndpointSelection D x)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) Subgraph.edgeSet)
    {r z t : V} (c : G.Walk r r) (hc : c.IsCycle)
    (hdisj : ∀ H ∈ D, Disjoint c.edgeSet H.edgeSet)
    (hz : G.Adj x z) (hzc : s(x,z) ∈ c.edgeSet)
    (ht : S.predecessor t = none)
    (htreach : ChainReachable S.predecessor {z} t)
    (hbad : Odd (G.degree t) ∨ t ∉ c.support) :
    ∃ Q : Finset G.Subgraph, (∀ H ∈ Q, IsNonemptyPathSubgraph H) ∧
      Set.PairwiseDisjoint (Q : Set G.Subgraph) Subgraph.edgeSet ∧
      (⋃ H : Q, H.val.edgeSet) = c.edgeSet ∪ (⋃ H : D, H.val.edgeSet) ∧
      Q.card ≤ D.card + 1 := by
  classical
  obtain ⟨p,hp,hn,hfresh,hcut⟩ := cycle_cut_oriented_edge c hc hzc
  have hpsub : p.edgeSet ⊆ c.edgeSet := by
    intro e he
    rw [← hcut]
    exact Or.inr he
  have hsource : ∀ H ∈ D, ¬H.Adj x z := by
    intro H hH he
    exact Set.disjoint_left.mp (hdisj H hH) hzc he
  have hcutdisj : ∀ H ∈ D, Disjoint p.toSubgraph.edgeSet H.edgeSet := by
    intro H hH
    simpa only [Walk.edgeSet_toSubgraph] using (hdisj H hH).mono_left hpsub
  have htrans := S.exchangeEdges_partition z p.toSubgraph hd hcutdisj hsource
    (by
      intro he
      exact hfresh (by simpa only [Walk.edgeSet_toSubgraph] using
        (show s(x,z) ∈ p.toSubgraph.edgeSet from he)))
  have hxt : G.Adj x t := by
    obtain ⟨a,ha,n,hn⟩ := htreach
    have haz : a = z := Finset.mem_singleton.mp ha
    subst a
    exact S.reachable_adj hz n hn
  have hnone : ∃ Q : G.Subgraph, IsNonemptyPathSubgraph Q ∧
      Q.edgeSet = S.exchangeEdges z p.toSubgraph none := by
    rw [S.exchangeEdges_none z t p.toSubgraph hz ht htreach]
    by_cases hot : Odd (G.degree t)
    · refine ⟨p.toSubgraph,⟨z,x,p,hp,hn,rfl⟩,?_⟩
      simp [hot]
    · have htc : t ∉ c.support := hbad.resolve_left hot
      have htp : t ∉ p.reverse.support := by
        simp only [Walk.support_reverse, List.mem_reverse]
        exact fun h => htc (walk_support_subset_of_edgeSet_subset p c hn hpsub h)
      let q : G.Walk t z := .cons hxt.symm p.reverse
      have hq : q.IsPath := Walk.cons_isPath_iff _ _ |>.mpr ⟨hp.reverse,htp⟩
      refine ⟨q.toSubgraph,⟨t,z,q,hq,by simp [q],rfl⟩,?_⟩
      simp only [hot, if_false, Walk.edgeSet_toSubgraph, q,
        Walk.edgeSet_cons, Walk.edgeSet_reverse, Sym2.eq_swap]
      ext e
      simp
  have hsome (H : D) : ∃ Q : G.Subgraph, IsNonemptyPathSubgraph Q ∧
      Q.edgeSet = S.exchangeEdges z p.toSubgraph (some H) := by
    obtain ⟨Q,hQ,he⟩ := S.realize_chainSelected z H
    exact ⟨Q,hQ,he.trans (S.selectedEdges_eq_exchangeEdges z p.toSubgraph H)⟩
  have hreal (i : Option D) : ∃ Q : G.Subgraph, IsNonemptyPathSubgraph Q ∧
      Q.edgeSet = S.exchangeEdges z p.toSubgraph i := by
    cases i with
    | none => exact hnone
    | some H => exact hsome H
  choose out hout he using hreal
  obtain ⟨Q,hQ,hQD,hQE,hcard⟩ := pathFamily_of_indexed out hout (by
    intro i j hij
    rw [he i,he j]
    exact htrans.1 hij)
  refine ⟨Q,hQ,hQD,?_,by simpa using hcard⟩
  rw [hQE]
  simp_rw [he]
  rw [htrans.2, Walk.edgeSet_toSubgraph, ← hcut]
  ext e
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

end OddEndpointSelection

/-- Cycle count is minimal among actual mixed partitions within the supplied
total-piece budget. This predicate asserts no decomposition existence theorem. -/
def CycleMinimal (P C : Finset G.Subgraph) : Prop :=
  ∀ Q R : Finset G.Subgraph,
    (∀ H ∈ Q, IsNonemptyPathSubgraph H) →
    (∀ H ∈ R, IsCycleSubgraph H) → Disjoint Q R →
    IsDecomposition G (Q ∪ R) → Q.card + R.card ≤ P.card + C.card → C.card ≤ R.card

omit [Fintype V] in
/-- Replacing all old paths and one cycle by at most one additional path
contradicts minimality; saved cycles retain their exact original edges. -/
theorem CycleMinimal.no_path_replacement {P C : Finset G.Subgraph}
    (hmin : CycleMinimal P C) (hc : ∀ H ∈ C, IsCycleSubgraph H)
    (hPC : Disjoint P C) (hd : IsDecomposition G (P ∪ C))
    {A : G.Subgraph} (hA : A ∈ C)
    (Q : Finset G.Subgraph) (hQ : ∀ H ∈ Q, IsNonemptyPathSubgraph H)
    (hQD : Set.PairwiseDisjoint (Q : Set G.Subgraph) Subgraph.edgeSet)
    (hQE : (⋃ H : Q, H.val.edgeSet) = A.edgeSet ∪ (⋃ H : P, H.val.edgeSet))
    (hq : Q.card ≤ P.card + 1) : False := by
  classical
  have cross (H : G.Subgraph) (hH : H ∈ Q) (J : G.Subgraph) (hJ : J ∈ C.erase A) :
      Disjoint H.edgeSet J.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heH heJ
    have heQ : e ∈ ⋃ H : Q, H.val.edgeSet := Set.mem_iUnion.mpr ⟨⟨H,hH⟩,heH⟩
    rw [hQE] at heQ
    have hJC := (Finset.mem_erase.mp hJ).2
    rcases heQ with heA | heP
    · exact Set.disjoint_left.mp
        (hd.1 (Finset.mem_union_right P hA) (Finset.mem_union_right P hJC)
          (Ne.symm (Finset.mem_erase.mp hJ).1)) heA heJ
    · obtain ⟨I,heI⟩ := Set.mem_iUnion.mp heP
      have hIJ : I.val ≠ J := by
        intro hh
        exact Finset.disjoint_left.mp hPC I.property (hh ▸ hJC)
      exact Set.disjoint_left.mp
        (hd.1 (Finset.mem_union_left C I.property) (Finset.mem_union_right P hJC) hIJ) heI heJ
  have hdisj : Disjoint Q (C.erase A) := by
    apply Finset.disjoint_left.mpr
    intro H hH hHC
    obtain ⟨e,he⟩ := (hQ H hH).edgeSet_nonempty
    exact Set.disjoint_left.mp (cross H hH H hHC) he he
  have hdecomp : IsDecomposition G (Q ∪ C.erase A) := by
    constructor
    · intro H hH J hJ hne
      rcases Finset.mem_union.mp hH with hH | hH <;>
        rcases Finset.mem_union.mp hJ with hJ | hJ
      · exact hQD hH hJ hne
      · exact cross H hH J hJ
      · exact (cross J hJ H hH).symm
      · exact hd.1 (Finset.mem_union_right P (Finset.mem_erase.mp hH).2)
          (Finset.mem_union_right P (Finset.mem_erase.mp hJ).2) hne
    · apply Set.Subset.antisymm
      · intro e he
        obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp he
        exact H.edgeSet_subset heH
      · intro e he
        rw [← hd.2] at he
        obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp he
        have fromQ (heQ : e ∈ A.edgeSet ∪ (⋃ I : P, I.val.edgeSet)) :
            e ∈ ⋃ I ∈ Q ∪ C.erase A, I.edgeSet := by
          rw [← hQE] at heQ
          obtain ⟨I,heI⟩ := Set.mem_iUnion.mp heQ
          exact Set.mem_iUnion₂.mpr ⟨I.val,Finset.mem_union_left _ I.property,heI⟩
        rcases Finset.mem_union.mp hH with hH | hH
        · exact fromQ (Or.inr (Set.mem_iUnion.mpr ⟨⟨H,hH⟩,heH⟩))
        · by_cases hHA : H = A
          · exact fromQ (Or.inl (hHA ▸ heH))
          · exact Set.mem_iUnion₂.mpr
              ⟨H,Finset.mem_union_right Q (Finset.mem_erase.mpr ⟨hHA,hH⟩),heH⟩
  have hcard : (C.erase A).card + 1 = C.card := Finset.card_erase_add_one hA
  have hh := hmin Q (C.erase A) hQ
    (fun H hH => hc H (Finset.mem_erase.mp hH).2) hdisj hdecomp (by omega)
  omega

/-- Pyber's local exchange conclusion: every vertex of any cycle member in a
cycle-minimal mixed partition has two distinct ambient-even neighbors on that
cycle. The two incident edges need not be edges of the cycle itself. -/
theorem cycle_minimal_two_even_neighbors (P C : Finset G.Subgraph)
    (hp : ∀ H ∈ P, IsNonemptyPathSubgraph H)
    (hc : ∀ H ∈ C, IsCycleSubgraph H) (hPC : Disjoint P C)
    (hd : IsDecomposition G (P ∪ C)) (hmin : CycleMinimal P C)
    (A : G.Subgraph) (hA : A ∈ C) (x : V) (hx : x ∈ A.verts) :
    ∃ t u : V, t ≠ u ∧ G.Adj x t ∧ G.Adj x u ∧
      Even (G.degree t) ∧ Even (G.degree u) ∧ t ∈ A.verts ∧ u ∈ A.verts := by
  classical
  obtain ⟨r,c,hcc,hce⟩ := hc A hA
  have hxwalk : x ∈ c.support := by simpa [hce] using hx
  let d := c.rotate x hxwalk
  have hdc : d.IsCycle := hcc.rotate hxwalk
  have hde : d.edgeSet = c.edgeSet := by
    ext e
    exact (c.rotate_edges x hxwalk).mem_iff
  obtain ⟨a,b,hab,hxa,hxb,hea,heb⟩ := cycle_has_two_neighbors d hdc
  rw [hde] at hea heb
  let S := oddEndpointSelection P C x hp hc hPC hd
  have hpd : Set.PairwiseDisjoint (P : Set G.Subgraph) Subgraph.edgeSet := by
    intro H hH J hJ hne
    exact hd.1 (Finset.mem_union_left C hH) (Finset.mem_union_left C hJ) hne
  have hdisj : ∀ H ∈ P, Disjoint c.edgeSet H.edgeSet := by
    intro H hH
    have hAH : A ≠ H := by
      intro he
      exact Finset.disjoint_left.mp hPC hH (he ▸ hA)
    have hh := hd.1 (Finset.mem_union_right P hA) (Finset.mem_union_left C hH) hAH
    change Disjoint A.edgeSet H.edgeSet at hh
    simpa only [hce, Walk.edgeSet_toSubgraph] using hh
  have outside (z : V) (hz : s(x,z) ∈ c.edgeSet) : ∀ H ∈ P, ¬H.Adj x z := by
    intro H hH he
    exact Set.disjoint_left.mp (hdisj H hH) hz he
  have good (z t : V) (hz : G.Adj x z) (hzc : s(x,z) ∈ c.edgeSet)
      (ht : S.predecessor t = none) (htr : ChainReachable S.predecessor {z} t) :
      Even (G.degree t) ∧ t ∈ A.verts := by
    have hnot : ¬ (Odd (G.degree t) ∨ t ∉ c.support) := by
      intro hbad
      obtain ⟨Q,hQ,hQD,hQE,hq⟩ := S.remove_cycle_along_chain hpd c hcc hdisj
        hz hzc ht htr hbad
      apply hmin.no_path_replacement hc hPC hd hA Q hQ hQD _ hq
      simpa only [hce, Walk.edgeSet_toSubgraph] using hQE
    refine ⟨Nat.not_odd_iff_even.mp (fun h => hnot (Or.inl h)), ?_⟩
    have htmem : t ∈ c.support := not_not.mp (fun h => hnot (Or.inr h))
    simpa [hce] using htmem
  obtain ⟨t,u,htu,hxt,hxu,ht,hu,⟨n,hn⟩,⟨m,hm⟩⟩ :=
    S.two_terminals hpd hab hxa hxb (outside a hea) (outside b heb)
  have htg := good a t hxa hea ht ⟨a,Finset.mem_singleton_self a,n,hn⟩
  have hug := good b u hxb heb hu ⟨b,Finset.mem_singleton_self b,m,hm⟩
  exact ⟨t,u,htu,hxt,hxu,htg.1,hug.1,htg.2,hug.2⟩

end Erdos583
end
end Source30_Erdos583_OddExchange
/- END Erdos583.OddExchange -/

/- BEGIN Erdos583.LovaszOdd; source SHA256 3c94da80044bbbd1ef32ce6d189124f89de7a2dfe7ea53999127ad3f22a75a2d -/
section Source31_Erdos583_LovaszOdd



/-! Endpoint saturation in the actual edge-subdivision graph. The mixed
partition is supplied explicitly; its existence is proved in the induction. -/

noncomputable section
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

theorem edgeSubdivision_oddVertices (G : SimpleGraph V) {x z : V} (hxz : G.Adj x z) :
    oddVertices (edgeSubdivision G x z) = (oddVertices G).map someEmbedding := by
  ext v
  cases v with
  | none => simp [edgeSubdivision_degree_new G hxz.ne, someEmbedding]
  | some v => simp [edgeSubdivision_degree_some G hxz v, someEmbedding]

theorem edgeSubdivision_odd_count (G : SimpleGraph V) {x z : V} (hxz : G.Adj x z)
    (hodd : ∀ v, G.degree v ≠ 0 → Odd (G.degree v)) :
    (oddVertices (edgeSubdivision G x z)).card = (activeVertices G).card := by
  rw [edgeSubdivision_oddVertices G hxz, Finset.card_map,
    activeVertices_eq_oddVertices_of_all_odd G hodd]

/-- An actual mixed partition of the subdivided all-odd graph at half its
old active-vertex count is pure paths, with no endpoint at the new vertex. -/
theorem subdivision_mixed_saturated (G : SimpleGraph V) {x z : V} (hxz : G.Adj x z)
    (hodd : ∀ v, G.degree v ≠ 0 → Odd (G.degree v))
    (hmixed : HasMixedBound (edgeSubdivision G x z)
      (((activeVertices G).card / 2 : ℕ) : ℚ)) :
    ∃ P : Finset (edgeSubdivision G x z).Subgraph,
      (∀ H ∈ P, IsNonemptyPathSubgraph H) ∧
      IsDecomposition (edgeSubdivision G x z) P ∧
      P.card ≤ (activeVertices G).card / 2 ∧
      ∀ H ∈ P, ¬PathStartsAt H none := by
  obtain ⟨P, C, hp, hc, hPC, hd, hbound⟩ := hmixed
  have hN : P.card + C.card ≤ (activeVertices G).card / 2 := by exact_mod_cast hbound
  have hbudget : 2 * (P.card + C.card) ≤ (oddVertices (edgeSubdivision G x z)).card := by
    rw [edgeSubdivision_odd_count G hxz hodd]
    omega
  obtain ⟨hC, hend⟩ := mixed_endpoint_saturation P C hp hc hPC hd hbudget
  have hzero : endpointCount P none = 0 := by
    apply hend
    rw [edgeSubdivision_degree_new G hxz.ne]
    decide
  refine ⟨P, hp, by simpa only [hC, Finset.union_empty] using hd, ?_, ?_⟩
  · simpa only [hC, Finset.card_empty, add_zero] using hN
  · intro H hH hstart
    have hmem : H ∈ P.filter (fun Q => PathStartsAt Q none) :=
      Finset.mem_filter.mpr ⟨hH, hstart⟩
    have hpos : 0 < endpointCount P none := Finset.card_pos.mpr ⟨H, hmem⟩
    omega

omit [Fintype V] in
theorem subdivisionResidual_le (G : SimpleGraph V) (x z : V) :
    subdivisionResidual G x z ≤ edgeSubdivision G x z :=
  (edgeSubdivision G x z).deleteEdges_le _

omit [Fintype V] in
theorem subdivisionResidual_missing (G : SimpleGraph V) (x z : V) :
    ¬ (subdivisionResidual G x z).Adj (some x) none := by
  simp [subdivisionResidual, deleteEdges_adj, Sym2.eq_swap]

omit [Fintype V] in
theorem subdivisionResidual_edge_cover (G : SimpleGraph V) (x z : V) :
    (subdivisionResidual G x z).edgeSet ∪ {s(some x,none)} =
      (edgeSubdivision G x z).edgeSet := by
  have he : s(some x, none) ∈ (edgeSubdivision G x z).edgeSet := by
    change (edgeSubdivision G x z).Adj (some x) none
    simp [edgeSubdivision]
  rw [subdivisionResidual, SimpleGraph.edgeSet_deleteEdges]
  have hswap : s(none, some x) = s(some x,none) := Sym2.eq_swap
  rw [hswap]
  exact Set.sdiff_union_of_subset (Set.singleton_subset_iff.mpr he)

end Erdos583
end
end Source31_Erdos583_LovaszOdd
/- END Erdos583.LovaszOdd -/

/- BEGIN Erdos583.MixedRestore; source SHA256 bdb1a538e6f1c38008e142d7aeaea994a474b0bd9d5dab3bf22d58884ac6b7ab -/
section Source32_Erdos583_MixedRestore



/-! Restore a star while retaining an arbitrary saved cycle family. -/

namespace Erdos583

open SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V : Type*} {G J : SimpleGraph V}

/-- Rebase one subgraph using exact inclusion of its original edges. Unlike a
global inclusion J≤G, this allows other edges of J to have been removed. -/
def rebaseSubgraph (P : J.Subgraph) (h : P.edgeSet ⊆ G.edgeSet) : G.Subgraph where
  verts := P.verts
  Adj := P.Adj
  adj_sub := fun {v w} hp => show G.Adj v w from h (show s(v,w) ∈ P.edgeSet from hp)
  edge_vert := P.edge_vert
  symm := P.symm

@[simp] theorem rebaseSubgraph_edgeSet (P : J.Subgraph) (h : P.edgeSet ⊆ G.edgeSet) :
    (rebaseSubgraph P h).edgeSet = P.edgeSet := rfl

theorem rebaseSubgraph_walk {a b : V} (p : J.Walk a b)
    (h : p.toSubgraph.edgeSet ⊆ G.edgeSet) :
    rebaseSubgraph p.toSubgraph h =
      (p.transfer G (fun e he => h (by simpa only [Walk.edgeSet_toSubgraph, Walk.mem_edgeSet] using he))).toSubgraph := by
  ext v w
  · simp [rebaseSubgraph]
  · change (s(v,w) ∈ p.toSubgraph.edgeSet) ↔
      s(v,w) ∈ (p.transfer G (fun e he => h (by simpa only [Walk.edgeSet_toSubgraph, Walk.mem_edgeSet] using he))).toSubgraph.edgeSet
    simp only [Walk.edgeSet_toSubgraph, Walk.edgeSet_transfer]

theorem IsNonemptyPathSubgraph.rebase {P : J.Subgraph}
    (hp : IsNonemptyPathSubgraph P) (h : P.edgeSet ⊆ G.edgeSet) :
    IsNonemptyPathSubgraph (rebaseSubgraph P h) := by
  obtain ⟨a,b,p,hp,hn,rfl⟩ := hp
  refine ⟨a,b,p.transfer G (fun e he => h (by simpa only [Walk.edgeSet_toSubgraph, Walk.mem_edgeSet] using he)),hp.transfer _,?_,rebaseSubgraph_walk p h⟩
  simpa only [Walk.not_nil_iff_lt_length, Walk.length_transfer] using hn

theorem PathStartsAt.rebase {P : J.Subgraph} {x : V}
    (hp : PathStartsAt P x) (h : P.edgeSet ⊆ G.edgeSet) :
    PathStartsAt (rebaseSubgraph P h) x := by
  obtain ⟨b,p,hp,hn,rfl⟩ := hp
  refine ⟨b,p.transfer G (fun e he => h (by simpa only [Walk.edgeSet_toSubgraph, Walk.mem_edgeSet] using he)),hp.transfer _,?_,rebaseSubgraph_walk p h⟩
  simpa only [Walk.not_nil_iff_lt_length, Walk.length_transfer] using hn

theorem IsRootedCycleSubgraph.lift {P : J.Subgraph} {x : V}
    (hp : IsRootedCycleSubgraph x P) (h : J ≤ G) :
    IsRootedCycleSubgraph x (liftSubgraph h P) := by
  obtain ⟨p,hp,rfl⟩ := hp
  exact ⟨p.mapLe h,hp.mapLe h,liftSubgraph_walk h p⟩

theorem liftSubgraph_injective (h : J ≤ G) : Function.Injective (liftSubgraph h) := by
  intro P Q he
  ext v w
  · exact iff_of_eq (congrArg (fun R : G.Subgraph => v ∈ R.verts) he)
  · exact iff_of_eq (congrArg (fun R : G.Subgraph => R.Adj v w) he)

theorem IsCycleSubgraph.lift {P : J.Subgraph}
    (hp : IsCycleSubgraph P) (h : J ≤ G) : IsCycleSubgraph (liftSubgraph h P) := by
  obtain ⟨x,hx⟩ := hp
  exact ⟨x,hx.lift h⟩

theorem union_pairwise_edge_disjoint (D E : Finset G.Subgraph)
    (hD : Set.PairwiseDisjoint (D : Set G.Subgraph) Subgraph.edgeSet)
    (hE : Set.PairwiseDisjoint (E : Set G.Subgraph) Subgraph.edgeSet)
    (hcross : ∀ P ∈ D, ∀ Q ∈ E, Disjoint P.edgeSet Q.edgeSet) :
    Set.PairwiseDisjoint ((D ∪ E : Finset G.Subgraph) : Set G.Subgraph) Subgraph.edgeSet := by
  intro P hP Q hQ hne
  rcases Finset.mem_union.mp hP with hP | hP <;>
    rcases Finset.mem_union.mp hQ with hQ | hQ
  · exact hD hP hQ hne
  · exact hcross P hP Q hQ
  · exact (hcross Q hQ P hP).symm
  · exact hE hP hQ hne

/-- Add a saved edge-disjoint cycle family to a mixed decomposition on the
complementary graph. The cycles may meet one another at arbitrary vertices. -/
theorem adjoin_saved_cycles {K : SimpleGraph V} (hKG : K ≤ G) (hJG : J ≤ G)
    (C : Finset J.Subgraph) (hc : ∀ H ∈ C, IsCycleSubgraph H)
    (hcd : Set.PairwiseDisjoint (C : Set J.Subgraph) Subgraph.edgeSet)
    (hdis : Disjoint K.edgeSet (⋃ H ∈ C, H.edgeSet))
    (hcover : K.edgeSet ∪ (⋃ H ∈ C, H.edgeSet) = G.edgeSet)
    {b : ℚ} (hK : HasMixedBound K b) : HasMixedBound G (b + C.card) := by
  classical
  obtain ⟨P0,C0,hp0,hc0,hPC0,hdec0,hcard0⟩ := hK
  let P := P0.image (liftSubgraph hKG)
  let N := C0.image (liftSubgraph hKG)
  let S := C.image (liftSubgraph hJG)
  have hPN : P ∪ N = (P0 ∪ C0).image (liftSubgraph hKG) := by
    exact (Finset.image_union _ _).symm
  have hpncard : P.card + N.card = P0.card + C0.card := by
    simp only [P,N,Finset.card_image_of_injective _ (liftSubgraph_injective hKG)]
  have hscard : S.card = C.card := Finset.card_image_of_injective _ (liftSubgraph_injective hJG)
  have hp : ∀ H ∈ P, IsNonemptyPathSubgraph H := by
    intro H hH
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hH
    exact (hp0 Q hQ).lift hKG
  have hn : ∀ H ∈ N, IsCycleSubgraph H := by
    intro H hH
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hH
    exact (hc0 Q hQ).lift hKG
  have hs : ∀ H ∈ S, IsCycleSubgraph H := by
    intro H hH
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hH
    exact (hc Q hQ).lift hJG
  have hpnDis : Disjoint P N := by
    apply Finset.disjoint_left.mpr
    intro H hHP hHN
    obtain ⟨A,hA,ha⟩ := Finset.mem_image.mp hHP
    obtain ⟨B,hB,hb⟩ := Finset.mem_image.mp hHN
    have he := liftSubgraph_injective hKG (ha.trans hb.symm)
    exact Finset.disjoint_left.mp hPC0 hA (he.symm ▸ hB)
  have hpnEdge : Set.PairwiseDisjoint ((P ∪ N : Finset G.Subgraph) : Set G.Subgraph) Subgraph.edgeSet := by
    rw [hPN]
    intro H hH Q hQ hne
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hQ
    exact hdec0.1 hA hB (fun he => hne (he ▸ rfl))
  have hsEdge : Set.PairwiseDisjoint (S : Set G.Subgraph) Subgraph.edgeSet := by
    intro H hH Q hQ hne
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hQ
    exact hcd hA hB (fun he => hne (he ▸ rfl))
  have hpnCover : (⋃ H ∈ P ∪ N, H.edgeSet) = K.edgeSet := by
    rw [hPN, ← hdec0.2]
    ext e
    simp
  have hsCover : (⋃ H ∈ S, H.edgeSet) = ⋃ H ∈ C, H.edgeSet := by
    ext e
    simp [S]
  have hcross (H : G.Subgraph) (hH : H ∈ P ∪ N) (Q : G.Subgraph) (hQ : Q ∈ S) :
      Disjoint H.edgeSet Q.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heH heQ
    apply Set.disjoint_left.mp hdis
    · rw [← hpnCover]
      exact Set.mem_iUnion.mpr ⟨H,Set.mem_iUnion.mpr ⟨hH,heH⟩⟩
    · rw [← hsCover]
      exact Set.mem_iUnion.mpr ⟨Q,Set.mem_iUnion.mpr ⟨hQ,heQ⟩⟩
  refine ⟨P,N ∪ S,hp,?_,?_,?_,?_⟩
  · intro H hH
    exact (Finset.mem_union.mp hH).elim (hn H) (hs H)
  · apply Finset.disjoint_left.mpr
    intro H hHP hHC
    rcases Finset.mem_union.mp hHC with hHN | hHS
    · exact Finset.disjoint_left.mp hpnDis hHP hHN
    · obtain ⟨e,he⟩ := (hp H hHP).edgeSet_nonempty
      exact Set.disjoint_left.mp (hcross H (Finset.mem_union_left _ hHP) H hHS) he he
  · constructor
    · rw [← Finset.union_assoc]
      exact union_pairwise_edge_disjoint (P ∪ N) S hpnEdge hsEdge hcross
    · rw [← hcover, ← hpnCover, ← hsCover]
      ext e
      simp only [Set.mem_iUnion, exists_prop, Finset.mem_union, Set.mem_union]
      constructor
      · rintro ⟨H,(hH | hH | hH),he⟩
        · exact Or.inl ⟨H,Or.inl hH,he⟩
        · exact Or.inl ⟨H,Or.inr hH,he⟩
        · exact Or.inr ⟨H,hH,he⟩
      · rintro (⟨H,hH,he⟩ | ⟨H,hH,he⟩)
        · rcases hH with hH | hH
          · exact ⟨H,Or.inl hH,he⟩
          · exact ⟨H,Or.inr (Or.inl hH),he⟩
        · exact ⟨H,Or.inr (Or.inr hH),he⟩
  · have hcard : P.card + (N ∪ S).card ≤ P0.card + C0.card + C.card := by
      have hu := Finset.card_union_le N S
      omega
    have hcardQ : ((P.card + (N ∪ S).card : ℕ) : ℚ) ≤
        ((P0.card+C0.card : ℕ) : ℚ) + C.card := by exact_mod_cast hcard
    linarith

/-- Restore a nonempty deleted root star from ANY mixed residual partition.
Every original neighbor has odd residual degree, so an actual path member
provides its endpoint; saved cycles are removed during switching and restored
unchanged afterwards. The total mixed-piece budget is preserved. -/
theorem restore_star_from_mixed_partition [Fintype V]
    (G J : SimpleGraph V) (hJG : J ≤ G) (x : V) (Z : Finset V)
    (hZ : Z.Nonempty) (hz : ∀ z ∈ Z, G.Adj x z)
    (hmissing : ∀ z ∈ Z, ¬ J.Adj x z)
    (hcover : J.edgeSet ∪ (fun v => s(x,v)) '' (Z : Set V) = G.edgeSet)
    (hodd : ∀ v, G.Adj x v → Odd (J.degree v))
    {b : ℚ} (hJ : HasMixedBound J b) : HasMixedBound G b := by
  classical
  obtain ⟨P,C,hp,hc,hPC,hdec,hbudget⟩ := hJ
  let EC : Set (Sym2 V) := ⋃ H ∈ C, H.edgeSet
  let EP : Set (Sym2 V) := ⋃ H ∈ P, H.edgeSet
  let K := G.deleteEdges EC
  have hKG : K ≤ G := G.deleteEdges_le EC
  have hECJ : EC ⊆ J.edgeSet := by
    intro e he
    obtain ⟨H,hH⟩ := Set.mem_iUnion.mp he
    obtain ⟨_,heH⟩ := Set.mem_iUnion.mp hH
    exact H.edgeSet_subset heH
  have hJcover : J.edgeSet = EP ∪ EC := by
    rw [← hdec.2]
    ext e
    simp only [EP,EC,Set.mem_iUnion,exists_prop,Finset.mem_union,Set.mem_union]
    aesop
  have hPnot (H : J.Subgraph) (hH : H ∈ P) (e : Sym2 V) (he : e ∈ H.edgeSet) : e ∉ EC := by
    intro heC
    obtain ⟨Q,hQ⟩ := Set.mem_iUnion.mp heC
    obtain ⟨hQC,heQ⟩ := Set.mem_iUnion.mp hQ
    have hne : H ≠ Q := by
      intro h
      exact Finset.disjoint_left.mp hPC hH (h.symm ▸ hQC)
    exact Set.disjoint_left.mp
      (hdec.1 (Finset.mem_union_left _ hH) (Finset.mem_union_right _ hQC) hne) he heQ
  have hZnot (z : V) (hzm : z ∈ Z) : s(x,z) ∉ EC := by
    intro he
    exact hmissing z hzm (hECJ he)
  have hkeep (H : J.Subgraph) (hH : H ∈ P) : H.edgeSet ⊆ K.edgeSet := by
    intro e he
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact ⟨SimpleGraph.edgeSet_mono hJG (H.edgeSet_subset he),hPnot H hH e he⟩
  let f : P → K.Subgraph := fun H => rebaseSubgraph H.val (hkeep H.val H.property)
  let D := Finset.univ.image f
  have hDpath : ∀ H ∈ D, IsNonemptyPathSubgraph H := by
    intro H hH
    obtain ⟨Q,_,rfl⟩ := Finset.mem_image.mp hH
    exact (hp Q.val Q.property).rebase (hkeep Q.val Q.property)
  have hDdis : Set.PairwiseDisjoint (D : Set K.Subgraph) Subgraph.edgeSet := by
    intro H hH Q hQ hne
    obtain ⟨A,_,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨B,_,rfl⟩ := Finset.mem_image.mp hQ
    have hab : A.val ≠ B.val := fun h => hne (congrArg f (Subtype.ext h))
    exact hdec.1 (Finset.mem_union_left _ A.property) (Finset.mem_union_left _ B.property) hab
  have hDcover : (⋃ H : D, H.val.edgeSet) = EP := by
    ext e
    simp [D,f,EP]
  have hzK : ∀ z ∈ Z, K.Adj x z := by
    intro z hzm
    exact SimpleGraph.deleteEdges_adj.mpr ⟨hz z hzm,hZnot z hzm⟩
  have hDmissing : ∀ z ∈ Z, ∀ H ∈ D, ¬ H.Adj x z := by
    intro z hzm H hH hadj
    obtain ⟨Q,_,rfl⟩ := Finset.mem_image.mp hH
    exact hmissing z hzm (Q.val.adj_sub hadj)
  have hKcover : EP ∪ (fun v => s(x,v)) '' (Z : Set V) = K.edgeSet := by
    rw [SimpleGraph.edgeSet_deleteEdges]
    ext e
    constructor
    · rintro (heP | ⟨z,hzm,rfl⟩)
      · obtain ⟨H,hH⟩ := Set.mem_iUnion.mp heP
        obtain ⟨hHP,heH⟩ := Set.mem_iUnion.mp hH
        exact ⟨SimpleGraph.edgeSet_mono hJG (H.edgeSet_subset heH),hPnot H hHP e heH⟩
      · exact ⟨hz z hzm,hZnot z hzm⟩
    · rintro ⟨heG,heC⟩
      rw [← hcover,hJcover] at heG
      rcases heG with (heP | heC') | heZ
      · exact Or.inl heP
      · exact (heC heC').elim
      · exact Or.inr heZ
  have hend : ∀ v, K.Adj x v → ∃ H ∈ D, PathStartsAt H v := by
    intro v hv
    obtain ⟨H,hHP,hend⟩ := exists_pathStartsAt_of_odd_mixed P C hp hc hPC hdec v
      (hodd v (hKG hv))
    exact ⟨f ⟨H,hHP⟩,Finset.mem_image.mpr ⟨⟨H,hHP⟩,Finset.mem_univ _,rfl⟩,
      hend.rebase (hkeep H hHP)⟩
  obtain ⟨r,_,hrest⟩ := restore_star_from_endpoint_partition D x Z hDpath hDdis
    hZ hzK hDmissing (by rw [hDcover]; exact hKcover) hend
  have hKCdis : Disjoint K.edgeSet EC := by
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact Set.disjoint_sdiff_left
  have hKCcover : K.edgeSet ∪ EC = G.edgeSet := by
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact Set.sdiff_union_of_subset (hECJ.trans (SimpleGraph.edgeSet_mono hJG))
  have hCdis : Set.PairwiseDisjoint (C : Set J.Subgraph) Subgraph.edgeSet := by
    intro H hH Q hQ hne
    exact hdec.1 (Finset.mem_union_right _ hH) (Finset.mem_union_right _ hQ) hne
  have hcombined := adjoin_saved_cycles hKG hJG C hc hCdis hKCdis hKCcover hrest.toMixedBound
  apply hcombined.mono
  have hDcard : D.card ≤ P.card := Finset.card_image_le.trans (by simp)
  have hDcardQ : (D.card : ℚ) ≤ P.card := by exact_mod_cast hDcard
  push_cast at hbudget
  linarith

/-- Concrete mixed-input Case A: restoring all edges from x to its even-degree
neighbors preserves any supplied mixed-decomposition budget. -/
theorem restore_even_neighbor_star_mixed [Fintype V] (G : SimpleGraph V) (x : V)
    (hk : 0 < evenNeighborCount G x) {b : ℚ}
    (hJ : HasMixedBound (starDeleteEven G x) b) : HasMixedBound G b := by
  classical
  apply restore_star_from_mixed_partition G (starDeleteEven G x) (starDeleteEven_le G x)
    x (evenNeighbors G x) (Finset.card_pos.mp hk)
    (fun z hz => (mem_evenNeighbors G x z).mp hz |>.1) _
    (starDeleteEven_edge_cover G x) (original_neighbor_odd_after_starDeleteEven G x) hJ
  intro z hz hj
  exact hj.2.1 ⟨rfl,(mem_evenNeighbors G x z).mp hz |>.2⟩

end Erdos583
end Source32_Erdos583_MixedRestore
/- END Erdos583.MixedRestore -/

/- BEGIN Erdos583.SubdivisionPaths; source SHA256 caf7b02dc2ba5f55ac6c1d9da40c994cef34ad0e5d41b187d98d3244c9eb6ec0 -/
section Source33_Erdos583_SubdivisionPaths



/-! Suppress the new subdivision vertex in an actual path partition when it
is never an endpoint. Every original edge is transported exactly. -/

noncomputable section
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*}

def subdivisionEdgeLift (x z : V) (e : Sym2 V) : Set (Sym2 (Option V)) :=
  if e = s(x,z) then {s(some x,none), s(none,some z)} else {Sym2.map some e}

def subdivisionEdgeExpansion (x z : V) (E : Set (Sym2 V)) : Set (Sym2 (Option V)) :=
  ⋃ e ∈ E, subdivisionEdgeLift x z e

def subdivisionEdgeContract (x z : V) (e : Sym2 (Option V)) : Sym2 V :=
  if none ∈ e then s(x,z) else Sym2.map (fun v => v.getD x) e

theorem subdivisionEdgeLift_nonempty (x z : V) (e : Sym2 V) :
    (subdivisionEdgeLift x z e).Nonempty := by
  unfold subdivisionEdgeLift
  split_ifs <;> simp

theorem subdivisionEdgeContract_lift (x z : V) {e : Sym2 V} {f : Sym2 (Option V)}
    (hf : f ∈ subdivisionEdgeLift x z e) : subdivisionEdgeContract x z f = e := by
  by_cases he : e = s(x,z)
  · subst e
    have hcases : f = s(some x,none) ∨ f = s(none,some z) := by
      simpa [subdivisionEdgeLift] using hf
    rcases hcases with rfl | rfl <;> simp [subdivisionEdgeContract]
  · simp only [subdivisionEdgeLift, if_neg he, Set.mem_singleton_iff] at hf
    subst f
    induction e using Sym2.ind with
    | _ a b => simp [subdivisionEdgeContract]

theorem subdivisionEdgeExpansion_insert (x z : V) (e : Sym2 V) (E : Set (Sym2 V)) :
    subdivisionEdgeExpansion x z (insert e E) =
      subdivisionEdgeLift x z e ∪ subdivisionEdgeExpansion x z E := by
  ext f
  simp only [subdivisionEdgeExpansion, Set.mem_iUnion, Set.mem_insert_iff,
    exists_prop, Set.mem_union]
  aesop

theorem subdivision_two_step (G : SimpleGraph V) {x z a b : V} (hxz : G.Adj x z)
    (ha : (edgeSubdivision G x z).Adj (some a) none)
    (hb : (edgeSubdivision G x z).Adj none (some b)) (hab : a ≠ b) :
    G.Adj a b ∧ subdivisionEdgeLift x z s(a,b) = {s(some a,none), s(none,some b)} := by
  change a = x ∨ a = z at ha
  change b = x ∨ b = z at hb
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> subst a <;> subst b
  · exact (hab rfl).elim
  · exact ⟨hxz, by simp [subdivisionEdgeLift]⟩
  · refine ⟨hxz.symm, ?_⟩
    have he : s(z,x) = s(x,z) := Sym2.eq_swap
    have h1 : s(some z,none) = s(none,some z) := Sym2.eq_swap
    have h2 : s(none,some x) = s(some x,none) := Sym2.eq_swap
    simp only [he, subdivisionEdgeLift, h1, h2]
    exact Set.pair_comm _ _
  · exact (hab rfl).elim

/-- A simple subdivision path whose endpoints are old vertices contracts to
one simple original path. Its expanded edge set is exactly the input edges. -/
theorem suppress_subdivision_walk (G : SimpleGraph V) {x z : V} (hxz : G.Adj x z)
    {a b : V} (p : (edgeSubdivision G x z).Walk (some a) (some b)) (hp : p.IsPath) :
    ∃ q : G.Walk a b, q.IsPath ∧ (∀ v, v ∈ q.support ↔ some v ∈ p.support) ∧
      subdivisionEdgeExpansion x z q.edgeSet = p.edgeSet ∧ (q.Nil ↔ p.Nil) := by
  have aux : ∀ n : ℕ, ∀ a b : V,
      ∀ p : (edgeSubdivision G x z).Walk (some a) (some b), p.length = n → p.IsPath →
      ∃ q : G.Walk a b, q.IsPath ∧ (∀ v, v ∈ q.support ↔ some v ∈ p.support) ∧
        subdivisionEdgeExpansion x z q.edgeSet = p.edgeSet ∧ (q.Nil ↔ p.Nil) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a b p hn hp
      cases p with
      | nil =>
        refine ⟨Walk.nil, by simp, ?_, ?_, by simp⟩
        · intro v; simp
        · simp [subdivisionEdgeExpansion]
      | @cons _ w _ haw t =>
        cases w with
        | some c =>
          have ht : t.IsPath := hp.of_cons
          obtain ⟨q,hq,hqs,hqe,hqn⟩ := ih t.length (by simp only [Walk.length_cons] at hn; omega)
            c b t rfl ht
          have hg : G.Adj a c := (SimpleGraph.deleteEdges_adj.mp haw).1
          have hne : s(a,c) ≠ s(x,z) := by
            simpa using (SimpleGraph.deleteEdges_adj.mp haw).2
          have hnot : a ∉ q.support := by
            intro ha
            exact (List.nodup_cons.mp hp.support_nodup).1 ((hqs a).mp ha)
          refine ⟨Walk.cons hg q, ?_, ?_, ?_, by simp⟩
          · rw [Walk.isPath_def, Walk.support_cons, List.nodup_cons]
            exact ⟨hnot, hq.support_nodup⟩
          · intro v
            simp only [Walk.support_cons, List.mem_cons, Option.some.injEq, hqs]
          · rw [Walk.edgeSet_cons, subdivisionEdgeExpansion_insert, hqe]
            simp [subdivisionEdgeLift, hne, Walk.edgeSet_cons]
        | none =>
          cases t with
          | @cons _ w _ hnw r =>
            cases w with
            | none => exact (hnw : False).elim
            | some c =>
              have hr : r.IsPath := hp.of_cons.of_cons
              obtain ⟨q,hq,hqs,hqe,hqn⟩ := ih r.length (by simp only [Walk.length_cons] at hn; omega)
                c b r rfl hr
              have hnotOld : some a ∉ r.support := by
                have h := (List.nodup_cons.mp hp.support_nodup).1
                simpa only [Walk.support_cons, List.mem_cons, not_or, Option.some_ne_none, not_false_eq_true,
                  true_and] using h
              have hac : a ≠ c := by
                intro he
                subst c
                exact hnotOld r.start_mem_support
              obtain ⟨hg,hlift⟩ := subdivision_two_step G hxz haw hnw hac
              have hnot : a ∉ q.support := fun ha => hnotOld ((hqs a).mp ha)
              refine ⟨Walk.cons hg q, ?_, ?_, ?_, by simp⟩
              · rw [Walk.isPath_def, Walk.support_cons, List.nodup_cons]
                exact ⟨hnot, hq.support_nodup⟩
              · intro v
                simp only [Walk.support_cons, List.mem_cons, Option.some.injEq,
                  Option.some_ne_none, false_or, hqs]
              · rw [Walk.edgeSet_cons, subdivisionEdgeExpansion_insert, hlift, hqe]
                simp only [Walk.edgeSet_cons]
                ext e
                simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
                tauto
  exact aux p.length a b p rfl hp


theorem subdivisionEdgeLift_subset (G : SimpleGraph V) {x z : V}
    {e : Sym2 V} (he : e ∈ G.edgeSet) :
    subdivisionEdgeLift x z e ⊆ (edgeSubdivision G x z).edgeSet := by
  intro f hf
  by_cases heq : e = s(x,z)
  · subst e
    have hcases : f = s(some x,none) ∨ f = s(none,some z) := by
      simpa [subdivisionEdgeLift] using hf
    rcases hcases with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · simp only [subdivisionEdgeLift, if_neg heq, Set.mem_singleton_iff] at hf
    subst f
    induction e using Sym2.ind with
    | _ a b => exact SimpleGraph.deleteEdges_adj.mpr ⟨he, by simpa using heq⟩

theorem subdivision_edge_expansion (G : SimpleGraph V) {x z : V} (hxz : G.Adj x z) :
    subdivisionEdgeExpansion x z G.edgeSet = (edgeSubdivision G x z).edgeSet := by
  apply Set.Subset.antisymm
  · intro f hf
    obtain ⟨e, he, hf⟩ := (show ∃ e ∈ G.edgeSet, f ∈ subdivisionEdgeLift x z e by
      simpa only [subdivisionEdgeExpansion, Set.mem_iUnion, exists_prop] using hf)
    exact subdivisionEdgeLift_subset G he hf
  · intro f hf
    apply Set.mem_iUnion.mpr
    induction f using Sym2.ind with
    | _ a b =>
      cases a with
      | none =>
        cases b with
        | none => exact (hf : False).elim
        | some b =>
          refine ⟨s(x,z), Set.mem_iUnion.mpr ⟨hxz, ?_⟩⟩
          change b = x ∨ b = z at hf
          rcases hf with rfl | rfl
          · simp [subdivisionEdgeLift, Sym2.eq_swap]
          · simp [subdivisionEdgeLift]
      | some a =>
        cases b with
        | none =>
          refine ⟨s(x,z), Set.mem_iUnion.mpr ⟨hxz, ?_⟩⟩
          change a = x ∨ a = z at hf
          rcases hf with rfl | rfl
          · simp [subdivisionEdgeLift]
          · simp [subdivisionEdgeLift, Sym2.eq_swap]
        | some b =>
          have hg : G.Adj a b := hf.1
          have heq : s(a,b) ≠ s(x,z) := by simpa using (SimpleGraph.deleteEdges_adj.mp hf).2
          exact ⟨s(a,b), Set.mem_iUnion.mpr ⟨hg, by simp [subdivisionEdgeLift, heq]⟩⟩

/-- Each input nonempty path avoiding the new vertex as an endpoint has one
nonempty original path with exactly its expanded edge set. -/
theorem suppress_subdivision_pathSubgraph (G : SimpleGraph V) {x z : V} (hxz : G.Adj x z)
    (P : (edgeSubdivision G x z).Subgraph) (hP : IsNonemptyPathSubgraph P)
    (hno : ¬PathStartsAt P none) :
    ∃ Q : G.Subgraph, IsNonemptyPathSubgraph Q ∧
      subdivisionEdgeExpansion x z Q.edgeSet = P.edgeSet := by
  obtain ⟨a,b,p,hp,hn,rfl⟩ := hP
  have hends : ¬(none = a ∨ none = b) := by
    intro he
    rcases he with he | he
    · subst a
      exact hno ⟨b,p,hp,hn,rfl⟩
    · subst b
      apply hno
      refine ⟨a,p.reverse,hp.reverse,?_,?_⟩
      · simpa using hn
      · simp
  cases a with
  | none => exact (hends (Or.inl rfl)).elim
  | some a =>
    cases b with
    | none => exact (hends (Or.inr rfl)).elim
    | some b =>
      obtain ⟨q,hq,_,he,hnil⟩ := suppress_subdivision_walk G hxz p hp
      refine ⟨q.toSubgraph, ⟨a,b,q,hq,fun h => hn (hnil.mp h),rfl⟩, ?_⟩
      simpa only [Walk.edgeSet_toSubgraph] using he

/-- Suppress the actual subdivision vertex in any given original-edge path
partition in which it is never an endpoint. The number of paths does not rise. -/
theorem suppress_subdivision_partition (G : SimpleGraph V) {x z : V} (hxz : G.Adj x z)
    (D : Finset (edgeSubdivision G x z).Subgraph)
    (hpath : ∀ P ∈ D, IsNonemptyPathSubgraph P)
    (hdec : SimpleGraph.IsDecomposition (edgeSubdivision G x z) D)
    (hno : ∀ P ∈ D, ¬PathStartsAt P none) : HasPathPartition G D.card := by
  classical
  have hex (P : (edgeSubdivision G x z).Subgraph) (hP : P ∈ D) :
      ∃ Q : G.Subgraph, IsNonemptyPathSubgraph Q ∧
        subdivisionEdgeExpansion x z Q.edgeSet = P.edgeSet :=
    suppress_subdivision_pathSubgraph G hxz P (hpath P hP) (hno P hP)
  let f : (edgeSubdivision G x z).Subgraph → G.Subgraph :=
    fun P => if hP : P ∈ D then Classical.choose (hex P hP) else ⊥
  have hf (P : (edgeSubdivision G x z).Subgraph) (hP : P ∈ D) :
      IsNonemptyPathSubgraph (f P) ∧
        subdivisionEdgeExpansion x z (f P).edgeSet = P.edgeSet := by
    simpa only [f, dif_pos hP] using Classical.choose_spec (hex P hP)
  refine ⟨D.image f, ?_, ?_, Finset.card_image_le⟩
  · intro Q hQ
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hQ
    exact (hf P hP).1
  · constructor
    · intro P hP Q hQ hne
      obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hQ
      apply Set.disjoint_left.mpr
      intro e heR heS
      obtain ⟨g,hg⟩ := subdivisionEdgeLift_nonempty x z e
      have hgR : g ∈ R.edgeSet := by
        rw [← (hf R hR).2]
        exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨heR,hg⟩⟩
      have hgS : g ∈ S.edgeSet := by
        rw [← (hf S hS).2]
        exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨heS,hg⟩⟩
      have hRS : R ≠ S := fun he => hne (congrArg f he)
      exact Set.disjoint_left.mp (hdec.1 hR hS hRS) hgR hgS
    · ext e
      simp only [Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨P,hP,he⟩
        exact P.edgeSet_subset he
      · intro he
        obtain ⟨g,hg⟩ := subdivisionEdgeLift_nonempty x z e
        have hgH := subdivisionEdgeLift_subset G he hg
        rw [← hdec.2] at hgH
        obtain ⟨P,hP,hgP⟩ := (show ∃ P ∈ D, g ∈ P.edgeSet by
          simpa only [Set.mem_iUnion, exists_prop] using hgH)
        rw [← (hf P hP).2] at hgP
        obtain ⟨e',he',hg'⟩ := (show ∃ e' ∈ (f P).edgeSet, g ∈ subdivisionEdgeLift x z e' by
          simpa only [subdivisionEdgeExpansion, Set.mem_iUnion, exists_prop] using hgP)
        have heq : e = e' := (subdivisionEdgeContract_lift x z hg).symm.trans
          (subdivisionEdgeContract_lift x z hg')
        exact ⟨f P, Finset.mem_image.mpr ⟨P,hP,rfl⟩, heq.symm ▸ he'⟩

end Erdos583
end
end Source33_Erdos583_SubdivisionPaths
/- END Erdos583.SubdivisionPaths -/

/- BEGIN Erdos583.Lovasz; source SHA256 81ae73ab43653f5d7edfc424a53894d687c56daa3aa32fb1be0153be32000c60 -/
section Source34_Erdos583_Lovasz





/-! The classical mixed path/cycle bound, derived from the proved restoration
and graph operations. No external decomposition theorem is an axiom or premise. -/

noncomputable section
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
universe u
variable {V : Type u} [Fintype V]

/-- Every finite simple graph has a mixed original-edge partition with at most
half its number of nonisolated vertices, rounded down. -/
theorem hasMixedBound_half_active (G : SimpleGraph V) :
    HasMixedBound G (((activeVertices G).card / 2 : ℕ) : ℚ) := by
  have aux : ∀ n : ℕ, ∀ {W : Type u} [Fintype W] (G : SimpleGraph W),
      edgeExcess G = n → HasMixedBound G (((activeVertices G).card / 2 : ℕ) : ℚ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W inst G hmeasure
      by_cases hn : n = 0
      · have hz : edgeExcess G = 0 := hmeasure.trans hn
        have hm : G.edgeFinset.card ≤ (activeVertices G).card / 2 := by
          unfold edgeExcess at hz
          omega
        have he : HasPathPartition G G.edgeFinset.card := by
          rw [G.edgeFinset_card]
          exact hasPathPartition_card_edgeSet
        apply (hasPathBound_nat_iff.mpr he).toMixedBound.mono
        exact_mod_cast hm
      · by_cases he : ∃ v, Even (G.degree v) ∧ G.degree v ≠ 0
        · obtain ⟨x, hk⟩ := exists_even_star_center G he
          have hlt : edgeExcess (starDeleteEven G x) < n := by
            have hh := edgeExcess_starDeleteEven_lt G x hk
            omega
          have hJ := ih (edgeExcess (starDeleteEven G x)) hlt (starDeleteEven G x) rfl
          have hr := restore_even_neighbor_star_mixed G x hk hJ
          apply hr.mono
          have hactive := (activeVertices_starDeleteEven_bounds G x).1
          have hhalf : (activeVertices (starDeleteEven G x)).card / 2 ≤
              (activeVertices G).card / 2 := by omega
          exact_mod_cast hhalf
        · have hodd : ∀ v, G.degree v ≠ 0 → Odd (G.degree v) := by
            intro v hv
            apply Nat.not_even_iff_odd.mp
            intro hvEven
            exact he ⟨v, hvEven, hv⟩
          have hpos : 0 < edgeExcess G := by omega
          obtain ⟨x, hx⟩ := exists_degree_ge_three_of_all_odd G hodd hpos
          have hxNoniso : ¬G.IsIsolated x := by
            intro hiso
            have hh := hiso.degree_eq_zero
            omega
          obtain ⟨z, hxz⟩ := G.exists_adj_iff_not_isIsolated.mpr hxNoniso
          have hlt : edgeExcess (subdivisionResidual G x z) < n := by
            have hh := subdivisionResidual_edgeExcess G hxz hx
            omega
          have hJ := ih (edgeExcess (subdivisionResidual G x z)) hlt
            (subdivisionResidual G x z) rfl
          rw [subdivisionResidual_active_half G hxz hx hodd] at hJ
          have hzedge : ∀ y ∈ ({none} : Finset (Option W)),
              (edgeSubdivision G x z).Adj (some x) y := by
            intro y hy
            have hyN : y = none := Finset.mem_singleton.mp hy
            subst y
            simp [edgeSubdivision]
          have hmissing : ∀ y ∈ ({none} : Finset (Option W)),
              ¬(subdivisionResidual G x z).Adj (some x) y := by
            intro y hy
            have hyN : y = none := Finset.mem_singleton.mp hy
            subst y
            exact subdivisionResidual_missing G x z
          have hcover : (subdivisionResidual G x z).edgeSet ∪
              (fun y => s(some x,y)) '' (({none} : Finset (Option W)) : Set (Option W)) =
              (edgeSubdivision G x z).edgeSet := by
            simpa using subdivisionResidual_edge_cover G x z
          have hH := restore_star_from_mixed_partition (edgeSubdivision G x z)
            (subdivisionResidual G x z) (subdivisionResidual_le G x z) (some x) {none}
            (by simp) hzedge hmissing hcover
            (subdivisionResidual_original_neighbors_odd G hxz hodd) hJ
          obtain ⟨P, hp, hd, hcard, hnone⟩ := subdivision_mixed_saturated G hxz hodd hH
          have hP := suppress_subdivision_partition G hxz P hp hd hnone
          exact (hasPathBound_nat_iff.mpr (hP.mono hcard)).toMixedBound
  exact aux (edgeExcess G) G rfl

end Erdos583
end
end Source34_Erdos583_Lovasz
/- END Erdos583.Lovasz -/

/- BEGIN Erdos583.EvenForest; source SHA256 f46ca96fb185a21465ff16e43e19b2b9d3f9bfaf304e2f9e4131e281c57db75f -/
section Source35_Erdos583_EvenForest




/-! The ambient-even forest case, using the proved odd-neighbor exchanges and
the actual mixed-partition existence theorem. Isolated vertices are retained. -/

noncomputable section
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Finite acyclic graphs have a vertex with at most one neighbor, without
connectedness or nontriviality assumptions. -/
theorem acyclic_exists_at_most_one_neighbor [Nonempty V] (hG : G.IsAcyclic) :
    ∃ x : V, ∀ a b, G.Adj x a → G.Adj x b → a = b := by
  obtain ⟨x,y,p,hp,hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  have hs (a : V) (ha : G.Adj x a) : a ∈ p.support := by
    by_contra hnot
    have hh := hmax a y (.cons ha.symm p) (hp.cons hnot)
    simp only [Walk.length_cons] at hh
    omega
  exact ⟨x,fun a b ha hb =>
    (hG.eq_snd_of_adj_start hp ha (hs a ha)).trans
      (hG.eq_snd_of_adj_start hp hb (hs b hb)).symm⟩

/-- Choose the least natural cycle count among mixed partitions within the
given rational budget. No finiteness of the space of walks is needed. -/
theorem exists_cycleMinimal_of_hasMixedBound {b : ℚ} (h : HasMixedBound G b) :
    ∃ P C : Finset G.Subgraph,
      (∀ H ∈ P, IsNonemptyPathSubgraph H) ∧ (∀ H ∈ C, IsCycleSubgraph H) ∧
      Disjoint P C ∧ IsDecomposition G (P ∪ C) ∧
      ((P.card + C.card : ℕ) : ℚ) ≤ b ∧ CycleMinimal P C := by
  classical
  let R (n : ℕ) : Prop := ∃ P C : Finset G.Subgraph,
    (∀ H ∈ P, IsNonemptyPathSubgraph H) ∧ (∀ H ∈ C, IsCycleSubgraph H) ∧
    Disjoint P C ∧ IsDecomposition G (P ∪ C) ∧
    ((P.card + C.card : ℕ) : ℚ) ≤ b ∧ C.card = n
  have hex : ∃ n, R n := by
    obtain ⟨P,C,hp,hc,hd,he,hb⟩ := h
    exact ⟨C.card,P,C,hp,hc,hd,he,hb,rfl⟩
  obtain ⟨P,C,hp,hc,hd,he,hb,hn⟩ := Nat.find_spec hex
  refine ⟨P,C,hp,hc,hd,he,hb,?_⟩
  intro Q T hQ hT hQT hdec hcard
  rw [hn]
  apply Nat.find_min' hex
  refine ⟨Q,T,hQ,hT,hQT,hdec,?_,rfl⟩
  exact (show ((Q.card + T.card : ℕ) : ℚ) ≤ ((P.card + C.card : ℕ) : ℚ)
    by exact_mod_cast hcard).trans hb

/-- If the graph induced by all ambient-even vertices is acyclic, a
cycle-minimal mixed partition has no cycle members. -/
theorem cycleMinimal_empty_of_even_induced_acyclic (P C : Finset G.Subgraph)
    (hp : ∀ H ∈ P, IsNonemptyPathSubgraph H)
    (hc : ∀ H ∈ C, IsCycleSubgraph H) (hPC : Disjoint P C)
    (hd : IsDecomposition G (P ∪ C)) (hmin : CycleMinimal P C)
    (hforest : (G.induce {v | Even (G.degree v)}).IsAcyclic) : C = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro A hA
  obtain ⟨r,c,hcc,hce⟩ := hc A hA
  have hr : r ∈ A.verts := by simp [hce]
  obtain ⟨t,_,_,_,_,hte,_,htA,_⟩ :=
    cycle_minimal_two_even_neighbors P C hp hc hPC hd hmin A hA r hr
  let T : Set V := {v | v ∈ A.verts ∧ Even (G.degree v)}
  let H := G.induce T
  let : Fintype T := Fintype.ofFinite T
  let : Nonempty T := ⟨⟨t,htA,hte⟩⟩
  let f : H →g G.induce {v | Even (G.degree v)} :=
    { toFun := fun v => ⟨v.val,v.property.2⟩
      map_rel' := fun h => h }
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun v : {v // Even (G.degree v)} => v.val) hab)
  have hH : H.IsAcyclic := hforest.comap f hf
  obtain ⟨x,hx⟩ := acyclic_exists_at_most_one_neighbor hH
  obtain ⟨a,b,hab,hxa,hxb,hae,hbe,haA,hbA⟩ :=
    cycle_minimal_two_even_neighbors P C hp hc hPC hd hmin A hA x.val x.property.1
  have hh := hx ⟨a,haA,hae⟩ ⟨b,hbA,hbe⟩ hxa hxb
  exact hab (congrArg Subtype.val hh)

/-- Every supplied mixed budget converts to a path budget when the induced
graph of ambient-even vertices is a forest. All original edges are preserved. -/
theorem hasPathBound_of_hasMixedBound_even_forest {b : ℚ}
    (hforest : (G.induce {v | Even (G.degree v)}).IsAcyclic)
    (h : HasMixedBound G b) : HasPathBound G b := by
  obtain ⟨P,C,hp,hc,hPC,hd,hb,hmin⟩ := exists_cycleMinimal_of_hasMixedBound h
  have hC := cycleMinimal_empty_of_even_induced_acyclic P C hp hc hPC hd hmin hforest
  subst C
  exact ⟨P,hp,by simpa using hd,by simpa using hb⟩

/-- The classical even-induced-forest bound with nonisolated vertex count,
derived from the proved mixed theorem rather than assumed as a premise. -/
theorem hasPathBound_half_active_even_forest (G : SimpleGraph V)
    (hforest : (G.induce {v | Even (G.degree v)}).IsAcyclic) :
    HasPathBound G (((activeVertices G).card / 2 : ℕ) : ℚ) :=
  hasPathBound_of_hasMixedBound_even_forest hforest (hasMixedBound_half_active G)

end Erdos583
end
end Source35_Erdos583_EvenForest
/- END Erdos583.EvenForest -/

/- BEGIN Erdos583.BaselineDegree; source SHA256 888da1b3df1be9ff48c01615d8097acc5e5de7a9d7ca3cd8f42332ce0c6479eb -/
section Source36_Erdos583_BaselineDegree




/-! The degree restriction in a minimal rational-potential counterexample.
The induction hypothesis is explicit and ranges over actual smaller graphs. -/
noncomputable section
universe u
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type u} [Fintype V]

theorem minimal_phi_core_degree (G : SimpleGraph V)
    (ih : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W),
      edgeExcess H < edgeExcess G → HasPathBound H (phi H))
    (hbad : ¬ HasPathBound G (phi G)) (x : V)
    (hxpos : (evenCore G).degree x ≠ 0) :
    (evenCore G).degree x = 3 ∨ (evenCore G).degree x = 4 := by
  classical
  have hx := (mem_nonisolatedEvenVertices G x).mp
    (evenCore_nonisolated_original G x hxpos)
  have hdeg := evenCore_degree_of_even G x hx.1
  have hk : 0 < evenNeighborCount G x := by omega
  by_contra hnone
  have h₃ : evenNeighborCount G x ≠ 3 := by omega
  have h₄ : evenNeighborCount G x ≠ 4 := by omega
  by_cases hleaf : evenNeighborCount G x = 2 ∨ evenNeighborCount G x = 10
  · obtain ⟨a,ha⟩ := Finset.card_pos.mp hk
    have hxa := (mem_evenNeighbors G x a).mp ha
    have htwo : 2 ≤ evenNeighborCount G x := by omega
    have hlt := attachLeaf_star_edgeExcess_lt G hxa.1 hxa.2 htwo
    have hJ := ih (Option V) (starDeleteEven (attachLeaf G a) (some x)) hlt
    have hJ' : HasPathBound (starDeleteEven (attachLeaf G a) (some x))
        (phi (starDeleteEven (attachLeaf G a) (some x)) - 0) := by simpa using hJ
    have hG := restore_leaf_exception_phi_bound G hxa.1 hxa.2 hx.1 hleaf hJ'
    exact hbad (by simpa using hG)
  · have h₂ : evenNeighborCount G x ≠ 2 := by omega
    have h₁₀ : evenNeighborCount G x ≠ 10 := by omega
    have hJ := ih V (starDeleteEven G x) (edgeExcess_starDeleteEven_lt G x hk)
    have hJ' : HasPathBound (starDeleteEven G x) (phi (starDeleteEven G x) - 0) :=
      by simpa using hJ
    have hG := restore_evenCenter_phi_bound_four G x hx.1 hk h₂ h₃ h₄ h₁₀ hJ'
    exact hbad (by simpa using hG)

theorem half_active_le_phi (G : SimpleGraph V) :
    (((activeVertices G).card / 2 : ℕ) : ℚ) ≤ phi G := by
  have hv := vertex_parity_count G
  have ha := activeVertices_card_add_isolated G
  have hcount : (activeVertices G).card =
      (oddVertices G).card + (nonisolatedEvenVertices G).card := by omega
  have hhalf : 2 * ((activeVertices G).card / 2) ≤ (activeVertices G).card := by omega
  have hhalf' : 2 * ((activeVertices G).card / 2) ≤
      (oddVertices G).card + (nonisolatedEvenVertices G).card := by omega
  have hhalfRat : (2 : ℚ) * (((activeVertices G).card / 2 : ℕ) : ℚ) ≤
      (oddVertices G).card + (nonisolatedEvenVertices G).card := by
    exact_mod_cast hhalf'
  unfold phi
  have he : (0 : ℚ) ≤ (nonisolatedEvenVertices G).card := by positivity
  linarith

theorem hasPathBound_phi_even_forest (G : SimpleGraph V)
    (hforest : (evenCore G).IsAcyclic) : HasPathBound G (phi G) :=
  (hasPathBound_half_active_even_forest G ((evenCore_isAcyclic_iff G).mp hforest)).mono
    (half_active_le_phi G)

end Erdos583
end
end Source36_Erdos583_BaselineDegree
/- END Erdos583.BaselineDegree -/

/- BEGIN Erdos583.EndpointDeficit; source SHA256 89c936aba573ea82e55a2e5e8152753dccea8fd411d5ed0093cab98bbf96a49a -/
section Source37_Erdos583_EndpointDeficit




/-! Single-edge restoration with endpoint deficits. The conclusion bounds
the path count without prescribing the full endpoint vector. -/

noncomputable section
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Optional endpoint choices, restricted to actual original root neighbors.
No choice is required at an endpoint-free neighbor. -/
structure PartialEndpointSelection (D : Finset G.Subgraph) (x : V) where
  owner : V → Option D
  presentation : ∀ H : D, PathPresentation H.val
  adjacent : ∀ v H, owner v = some H → G.Adj x v
  starts : ∀ v H, owner v = some H → PathStartsAt H.val v

namespace PartialEndpointSelection
variable {D : Finset G.Subgraph} {x : V}

def predecessor (S : PartialEndpointSelection D x) (v : V) : Option V :=
  (S.owner v).bind (fun H => (S.presentation H).predecessor x v)

omit [Fintype V] in
theorem predecessor_edge (S : PartialEndpointSelection D x) {v w : V}
    (h : S.predecessor v = some w) :
    ∃ H, S.owner v = some H ∧ H.val.Adj x w := by
  unfold predecessor at h
  cases he : S.owner v with
  | none => simp [he] at h
  | some H =>
    exact ⟨H,rfl,(S.presentation H).predecessor_adj x v w (by simpa [he] using h)⟩

omit [Fintype V] in
theorem predecessor_injective (S : PartialEndpointSelection D x)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) Subgraph.edgeSet)
    (a b w : V) (ha : S.predecessor a = some w) (hb : S.predecessor b = some w) : a = b := by
  obtain ⟨A,hA,hea⟩ := S.predecessor_edge ha
  obtain ⟨B,hB,heb⟩ := S.predecessor_edge hb
  have hAB : A = B := by
    apply Subtype.ext
    by_contra hn
    exact Set.disjoint_left.mp (hd A.property B.property hn)
      (show s(x,w) ∈ A.val.edgeSet from hea) (show s(x,w) ∈ B.val.edgeSet from heb)
  subst B
  exact (S.presentation A).predecessor_injective x a b w
    (by simpa [predecessor,hA] using ha) (by simpa [predecessor,hB] using hb)

omit [Fintype V] in
theorem source_outside_image (S : PartialEndpointSelection D x) {z : V}
    (hz : ∀ H ∈ D, ¬H.Adj x z) : ∀ v, S.predecessor v ≠ some z := by
  intro v hv
  obtain ⟨H,_,he⟩ := S.predecessor_edge hv
  exact hz H.val H.property he

def selectedSet (S : PartialEndpointSelection D x) (z : V) (H : D) : Set V :=
  {v | ChainReachable S.predecessor {z} v ∧ S.owner v = some H}

theorem selectedSet_subset (S : PartialEndpointSelection D x) (z : V) (H : D) :
    S.selectedSet z H ⊆ {(S.presentation H).start,(S.presentation H).finish} := by
  intro v hv
  have hs := S.starts v H hv.2
  rw [← (S.presentation H).toSubgraph_eq] at hs
  exact (pathStartsAt_iff_endpoints (S.presentation H).walk
    (S.presentation H).isPath (S.presentation H).nonempty v).mp hs

omit [Fintype V] in
theorem selected_predecessor (S : PartialEndpointSelection D x) (z : V) (H : D)
    {v : V} (hv : v ∈ S.selectedSet z H) :
    S.predecessor v = (S.presentation H).predecessor x v := by
  simp [predecessor,hv.2]

theorem realize_selectedSet (S : PartialEndpointSelection D x) (z : V) (H : D) :
    ∃ Q : G.Subgraph, IsNonemptyPathSubgraph Q ∧
      Q.edgeSet = (S.presentation H).selectedEdges x (S.selectedSet z H) := by
  obtain ⟨Q,hp,_,he⟩ := (S.presentation H).realize_selected x (S.selectedSet z H)
    (S.selectedSet_subset z H) (fun v hv => S.adjacent v H hv.2)
  refine ⟨Q,hp ?_,he⟩
  rintro ⟨ha,hb,hx⟩
  have terminal (v : V) (hv : v ∈ S.selectedSet z H) : S.predecessor v = none := by
    rw [S.selected_predecessor z H hv]
    simp [PathPresentation.predecessor,hx]
  obtain ⟨a,ha',n,hn⟩ := ha.1
  obtain ⟨b,hb',m,hm⟩ := hb.1
  have haz : a = z := Finset.mem_singleton.mp ha'
  have hbz : b = z := Finset.mem_singleton.mp hb'
  subst a
  subst b
  have hab := partialChain_terminal_unique S.predecessor z
    (S.presentation H).start (S.presentation H).finish n m hn (terminal _ ha) hm (terminal _ hb)
  exact (S.presentation H).nonempty ((S.presentation H).isPath.nil_iff_eq.mpr hab)

def totalOwner (S : PartialEndpointSelection D x) (fallback : D) (v : V) : D :=
  (S.owner v).getD fallback

def restorationEdges (S : PartialEndpointSelection D x) (fallback : D) (z : V) (H : D) :
    Set (Sym2 V) := edgeTransaction (fun J : D => J.val.edgeSet) (fun v => s(x,v))
      (S.totalOwner fallback) S.predecessor {v | ChainReachable S.predecessor {z} v} H

omit [Fintype V] in
theorem reachable_owner_of_good_terminal (S : PartialEndpointSelection D x)
    (z t : V) (H : D) (ht : S.predecessor t = none) (ho : S.owner t = some H)
    (htr : ChainReachable S.predecessor {z} t) :
    ∀ v, ChainReachable S.predecessor {z} v → ∃ J, S.owner v = some J := by
  intro v hv
  cases he : S.owner v with
  | some J => exact ⟨J,rfl⟩
  | none =>
    have hvterm : S.predecessor v = none := by simp [predecessor,he]
    obtain ⟨a,ha,n,hn⟩ := hv
    obtain ⟨b,hb,m,hm⟩ := htr
    have haz : a = z := Finset.mem_singleton.mp ha
    have hbz : b = z := Finset.mem_singleton.mp hb
    subst a
    subst b
    have hvt := partialChain_terminal_unique S.predecessor z v t n m hn hvterm hm ht
    subst v
    rw [ho] at he
    contradiction

omit [Fintype V] in
theorem selectedEdges_eq_restorationEdges (S : PartialEndpointSelection D x)
    (fallback : D) (z : V)
    (hall : ∀ v, ChainReachable S.predecessor {z} v → ∃ J, S.owner v = some J)
    (H : D) : (S.presentation H).selectedEdges x (S.selectedSet z H) =
      S.restorationEdges fallback z H := by
  have howner (v : V) (hv : ChainReachable S.predecessor {z} v) :
      S.totalOwner fallback v = H ↔ S.owner v = some H := by
    obtain ⟨J,hJ⟩ := hall v hv
    simp [totalOwner,hJ]
  have hremove :
      {e | ∃ v ∈ S.selectedSet z H, e ∈ (S.presentation H).predecessorEdges x v} =
      {e | ∃ v, ChainReachable S.predecessor {z} v ∧ S.totalOwner fallback v = H ∧
        ∃ w, S.predecessor v = some w ∧ s(x,w) = e} := by
    ext e
    constructor
    · rintro ⟨v,hv,w,hw,he⟩
      exact ⟨v,hv.1,(howner v hv.1).mpr hv.2,w,(S.selected_predecessor z H hv).trans hw,he⟩
    · rintro ⟨v,hvr,hvo,w,hw,he⟩
      have hv : v ∈ S.selectedSet z H := ⟨hvr,(howner v hvr).mp hvo⟩
      exact ⟨v,hv,w,(S.selected_predecessor z H hv).symm.trans hw,he⟩
  unfold PathPresentation.selectedEdges
  rw [hremove]
  unfold restorationEdges edgeTransaction
  congr 1
  ext e
  constructor
  · rintro ⟨v,hv,he⟩
    exact ⟨v,hv.1,(howner v hv.1).mpr hv.2,he⟩
  · rintro ⟨v,hv,ho,he⟩
    exact ⟨v,⟨hv,(howner v hv).mp ho⟩,he⟩

/-- A single chain whose terminal has an endpoint choice restores its missing
source edge without increasing the number of path members. -/
theorem restore_one_of_good_terminal (S : PartialEndpointSelection D x)
    (z t : V) (H : D)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) Subgraph.edgeSet)
    (hz : ∀ J ∈ D, ¬J.Adj x z)
    (hcover : (⋃ J : D, J.val.edgeSet) ∪ {s(x,z)} = G.edgeSet)
    (ht : S.predecessor t = none) (ho : S.owner t = some H)
    (htr : ChainReachable S.predecessor {z} t) : HasPathPartition G D.card := by
  classical
  have hall := S.reachable_owner_of_good_terminal z t H ht ho htr
  have htrans := edgeTransaction_partition (fun J : D => J.val.edgeSet) (fun v => s(x,v))
    (S.totalOwner H) S.predecessor {v | ChainReachable S.predecessor {z} v} {z}
    (Sym2.mkEmbedding x).injective
    (fun I J hne => hd I.property J.property (fun he => hne (Subtype.ext he)))
    (fun v hv => chainReachable_source S.predecessor {z} (by simpa using hv))
    (by
      intro v hv J
      have hvz : v = z := Set.mem_singleton_iff.mp hv
      subst v
      exact hz J.val J.property)
    (by
      intro v _ w hvw
      obtain ⟨J,hJ,he⟩ := S.predecessor_edge hvw
      simpa only [totalOwner,hJ,Option.getD_some] using
        (show s(x,w) ∈ J.val.edgeSet from he))
    (fun _ hv _ hvw => chainReachable_successor S.predecessor {z} hv hvw)
    (fun v hv hn => chainReachable_predecessor S.predecessor {z} hv (by simpa using hn))
  choose out hout he using (fun J : D => S.realize_selectedSet z J)
  have hedges (J : D) : (out J).edgeSet = S.restorationEdges H z J :=
    (he J).trans (S.selectedEdges_eq_restorationEdges H z hall J)
  obtain ⟨Q,hQ,hQD,hQE,hq⟩ := pathFamily_of_indexed out hout (by
    intro I J hij
    rw [hedges I,hedges J]
    exact htrans.1 hij)
  refine ⟨Q,hQ,⟨hQD,?_⟩,by simpa using hq⟩
  have hQE' : (⋃ J : Q, J.val.edgeSet) = G.edgeSet := by
    rw [hQE]
    simp_rw [hedges]
    change (⋃ J, edgeTransaction _ _ _ _ _ J) = _
    rw [htrans.2]
    simpa using hcover
  rw [← hQE']
  ext e
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨J,hJ,he⟩
    exact ⟨⟨J,hJ⟩,he⟩
  · rintro ⟨J,he⟩
    exact ⟨J.val,J.property,he⟩

end PartialEndpointSelection

omit [Fintype V] in
theorem endpointCount_pos_iff (D : Finset G.Subgraph) (v : V) :
    0 < endpointCount D v ↔ ∃ H ∈ D, PathStartsAt H v := by
  simp only [endpointCount, Finset.card_pos, Finset.nonempty_def, Finset.mem_filter]

omit [Fintype V] in
theorem exists_partialEndpointSelection_outside (D : Finset G.Subgraph) (x y : V)
    (hp : ∀ H ∈ D, IsNonemptyPathSubgraph H) :
    ∃ S : PartialEndpointSelection D x, S.owner y = none ∧
      ∀ v, G.Adj x v → v ≠ y →
        ((∃ H, S.owner v = some H) ↔ 0 < endpointCount D v) := by
  classical
  let A := {v : V // G.Adj x v ∧ v ≠ y ∧ 0 < endpointCount D v}
  choose owner hm hs using (fun v : A => (endpointCount_pos_iff D v.val).mp v.property.2.2)
  let S : PartialEndpointSelection D x :=
    { owner := fun v => if hv : G.Adj x v ∧ v ≠ y ∧ 0 < endpointCount D v
        then some ⟨owner ⟨v,hv⟩,hm ⟨v,hv⟩⟩ else none
      presentation := fun H => pathPresentation (hp H.val H.property)
      adjacent := by
        intro v H h
        split at h
        · rename_i hv
          exact hv.1
        · contradiction
      starts := by
        intro v H h
        split at h
        · rename_i hv
          have he := Option.some.inj h
          exact he ▸ hs ⟨v,hv⟩
        · contradiction }
  refine ⟨S,by simp [S],?_⟩
  intro v hv hvy
  simp [S,hv,hvy,hm]

namespace PartialEndpointSelection
variable {D : Finset G.Subgraph} {x : V}

def override (S : PartialEndpointSelection D x) (y : V) (H : D)
    (hy : G.Adj x y) (hs : PathStartsAt H.val y) : PartialEndpointSelection D x where
  owner v := if v = y then some H else S.owner v
  presentation := S.presentation
  adjacent v J h := by
    split at h
    · rename_i hv
      exact hv ▸ hy
    · exact S.adjacent v J h
  starts v J h := by
    split at h
    · rename_i hv
      have he := Option.some.inj h
      subst v
      exact he ▸ hs
    · exact S.starts v J h

omit [Fintype V] in
theorem override_predecessor_ne (S : PartialEndpointSelection D x) (y : V) (H : D)
    (hy : G.Adj x y) (hs : PathStartsAt H.val y) {v : V} (hv : v ≠ y) :
    (S.override y H hy hs).predecessor v = S.predecessor v := by
  simp [override,predecessor,hv]

omit [Fintype V] in
theorem override_predecessor_at (S : PartialEndpointSelection D x) (y : V) (H : D)
    (hy : G.Adj x y) (hs : PathStartsAt H.val y) :
    (S.override y H hy hs).predecessor y = (S.presentation H).predecessor x y := by
  simp [override,predecessor]

omit [Fintype V] in
theorem reachable_ne_missing (S : PartialEndpointSelection D x) {y z v : V}
    (hmissing : ∀ H ∈ D, ¬H.Adj x y) (hzy : z ≠ y)
    (n : ℕ) (hn : (partialStep S.predecessor)^[n] (some z) = some v) : v ≠ y := by
  cases n with
  | zero => exact (Option.some.inj hn) ▸ hzy
  | succ n =>
    intro hvy
    subst v
    rw [Function.iterate_succ_apply'] at hn
    cases he : (partialStep S.predecessor)^[n] (some z) with
    | none => simp [he,partialStep] at hn
    | some w =>
      exact S.source_outside_image hmissing w (by simpa [he,partialStep] using hn)

omit [Fintype V] in
theorem override_iterate (S : PartialEndpointSelection D x) (y : V) (H : D)
    (hy : G.Adj x y) (hs : PathStartsAt H.val y) (z : V)
    (hmissing : ∀ J ∈ D, ¬J.Adj x y) (hzy : z ≠ y) (n : ℕ) :
    (partialStep (S.override y H hy hs).predecessor)^[n] (some z) =
      (partialStep S.predecessor)^[n] (some z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih]
    cases he : (partialStep S.predecessor)^[n] (some z) with
    | none => rfl
    | some v =>
      exact S.override_predecessor_ne y H hy hs (S.reachable_ne_missing hmissing hzy n he)

end PartialEndpointSelection

/-- Restore one missing edge under the endpoint-deficit criterion. This is
the budget conclusion only, without an endpoint-vector assertion. The input
family partitions precisely the original edges other than xy. -/
theorem restore_edge_of_endpoint_deficit (D : Finset G.Subgraph) (x y : V)
    (hp : ∀ H ∈ D, IsNonemptyPathSubgraph H)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) Subgraph.edgeSet)
    (hxy : G.Adj x y) (hmissing : ∀ H ∈ D, ¬H.Adj x y)
    (hcover : (⋃ H : D, H.val.edgeSet) ∪ {s(x,y)} = G.edgeSet)
    (hdef : (Finset.univ.filter (fun v => G.Adj x v ∧ v ≠ y ∧ endpointCount D v = 0)).card <
      endpointCount D y) : HasPathPartition G D.card := by
  classical
  obtain ⟨S,hSy,havailable⟩ := exists_partialEndpointSelection_outside D x y hp
  by_cases hclean : ∃ H : D, PathStartsAt H.val y ∧ x ∉ (S.presentation H).walk.support
  · obtain ⟨H,hs,havoid⟩ := hclean
    let U := S.override y H hxy hs
    apply U.restore_one_of_good_terminal y y H hd hmissing hcover
    · rw [S.override_predecessor_at y H hxy hs]
      simp [PathPresentation.predecessor,havoid]
    · simp [U,PartialEndpointSelection.override]
    · exact chainReachable_source U.predecessor {y} (Finset.mem_singleton_self y)
  let Y := D.filter (fun H => PathStartsAt H y)
  let member (I : Y) : D := ⟨I.val,(Finset.mem_filter.mp I.property).1⟩
  have ystarts (I : Y) : PathStartsAt (member I).val y := (Finset.mem_filter.mp I.property).2
  have hpred (I : Y) : ∃ s, (S.presentation (member I)).predecessor x y = some s := by
    apply (S.presentation (member I)).predecessor_defined_iff x y |>.mpr
    refine ⟨?_,hxy.ne.symm,?_⟩
    · by_contra hh
      exact hclean ⟨member I,ystarts I,hh⟩
    · have hs := ystarts I
      rw [← (S.presentation (member I)).toSubgraph_eq] at hs
      exact (pathStartsAt_iff_endpoints (S.presentation (member I)).walk
        (S.presentation (member I)).isPath (S.presentation (member I)).nonempty y).mp hs
  choose source hsource using hpred
  have source_edge (I : Y) : (member I).val.Adj x (source I) :=
    (S.presentation (member I)).predecessor_adj x y (source I) (hsource I)
  have source_inj : Function.Injective source := by
    intro I J hij
    apply Subtype.ext
    by_contra hne
    exact Set.disjoint_left.mp (hd (member I).property (member J).property hne)
      (show s(x,source I) ∈ (member I).val.edgeSet from source_edge I)
      (show s(x,source I) ∈ (member J).val.edgeSet from hij ▸ source_edge J)
  have source_outside (I : Y) : ∀ v, S.predecessor v ≠ some (source I) := by
    intro v hv
    obtain ⟨J,hJ,heJ⟩ := S.predecessor_edge hv
    have heq : J = member I := by
      apply Subtype.ext
      by_contra hn
      exact Set.disjoint_left.mp (hd J.property (member I).property hn)
        (show s(x,source I) ∈ J.val.edgeSet from heJ)
        (show s(x,source I) ∈ (member I).val.edgeSet from source_edge I)
    subst J
    have hpredv : (S.presentation (member I)).predecessor x v = some (source I) := by
      simpa [PartialEndpointSelection.predecessor,hJ] using hv
    have hvy := (S.presentation (member I)).predecessor_injective x v y (source I)
      hpredv (hsource I)
    subst v
    rw [hSy] at hJ
    contradiction
  have source_ne (I : Y) : source I ≠ y := by
    intro he
    exact hmissing (member I).val (member I).property (he ▸ source_edge I)
  choose n terminal hn ht using (fun I : Y => partialChain_terminal S.predecessor
    (S.predecessor_injective hd) (source I) (source_outside I))
  have terminal_inj : Function.Injective terminal := by
    intro I J hij
    apply source_inj
    exact (partialChain_meeting S.predecessor (S.predecessor_injective hd)
      (source I) (source J) (source_outside I) (source_outside J)
      (n I) (n J) (terminal I) (hn I) ((hn J).trans (congrArg some hij.symm))).1
  have terminal_adj (I : Y) : G.Adj x (terminal I) := by
    cases hnI : n I with
    | zero =>
      have hh : source I = terminal I := Option.some.inj (by simpa [hnI] using hn I)
      exact hh ▸ (member I).val.adj_sub (source_edge I)
    | succ k =>
      have hh := hn I
      rw [hnI,Function.iterate_succ_apply'] at hh
      cases he : (partialStep S.predecessor)^[k] (some (source I)) with
      | none => simp [he,partialStep] at hh
      | some v =>
        obtain ⟨J,_,heJ⟩ := S.predecessor_edge (by simpa [he,partialStep] using hh)
        exact J.val.adj_sub heJ
  have terminal_ne (I : Y) : terminal I ≠ y :=
    S.reachable_ne_missing hmissing (source_ne I) (n I) (hn I)
  have good : ∃ I : Y, 0 < endpointCount D (terminal I) := by
    by_contra hnot
    have hzero (I : Y) : endpointCount D (terminal I) = 0 := by
      have hh : ¬0 < endpointCount D (terminal I) := fun h => hnot ⟨I,h⟩
      omega
    have hsub : Finset.univ.image terminal ⊆
        Finset.univ.filter (fun v => G.Adj x v ∧ v ≠ y ∧ endpointCount D v = 0) := by
      intro v hv
      obtain ⟨I,_,rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,terminal_adj I,terminal_ne I,hzero I⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ terminal_inj,Finset.card_univ] at hcard
    have hY : Fintype.card Y = endpointCount D y := by
      change Fintype.card Y = Y.card
      exact Fintype.card_coe _
    rw [hY] at hcard
    omega
  obtain ⟨I,hgood⟩ := good
  obtain ⟨J,hJ⟩ := (havailable (terminal I) (terminal_adj I) (terminal_ne I)).mpr hgood
  let U := S.override y (member I) hxy (ystarts I)
  have hreach : ChainReachable U.predecessor {y} (terminal I) := by
    refine ⟨y,Finset.mem_singleton_self y,n I + 1,?_⟩
    rw [Function.iterate_succ_apply]
    have hy : partialStep U.predecessor (some y) = some (source I) := by
      change U.predecessor y = some (source I)
      rw [S.override_predecessor_at y (member I) hxy (ystarts I)]
      exact hsource I
    rw [hy,S.override_iterate y (member I) hxy (ystarts I) (source I) hmissing (source_ne I)]
    exact hn I
  apply U.restore_one_of_good_terminal y (terminal I) J hd hmissing hcover
  · rw [S.override_predecessor_ne y (member I) hxy (ystarts I) (terminal_ne I)]
    exact ht I
  · simpa [U,PartialEndpointSelection.override,terminal_ne I] using hJ
  · exact hreach

theorem pathStartsAt_lift_iff {J : SimpleGraph V} (h : J ≤ G) {H : J.Subgraph}
    (hp : IsNonemptyPathSubgraph H) (v : V) :
    PathStartsAt (liftSubgraph h H) v ↔ PathStartsAt H v := by
  rw [pathStartsAt_iff_odd_degree v (hp.lift h),pathStartsAt_iff_odd_degree v hp]
  rfl

theorem endpointCount_lift_image {J : SimpleGraph V} (h : J ≤ G)
    (D : Finset J.Subgraph) (hp : ∀ H ∈ D, IsNonemptyPathSubgraph H) (v : V) :
    endpointCount (D.image (liftSubgraph h)) v = endpointCount D v := by
  classical
  rw [endpointCount,Finset.filter_image,Finset.card_image_of_injective _ (liftSubgraph_injective h)]
  unfold endpointCount
  congr 1
  apply Finset.filter_congr
  intro H hH
  exact pathStartsAt_lift_iff h (hp H hH) v

/-- The literal residual-graph form of the endpoint-deficit criterion. Given
ANY path partition of H, adding one absent edge xy preserves its path budget
when y's endpoint count exceeds the endpoint-free H-neighbors of x. -/
theorem add_edge_pathPartition_of_endpoint_deficit (H : SimpleGraph V)
    (D : Finset H.Subgraph) (hp : ∀ A ∈ D, IsNonemptyPathSubgraph A)
    (hd : IsDecomposition H D) (x y : V) (hne : x ≠ y) (hnadj : ¬H.Adj x y)
    (hdef : (Finset.univ.filter (fun v => H.Adj x v ∧ endpointCount D v = 0)).card <
      endpointCount D y) : HasPathPartition (H ⊔ edge x y) D.card := by
  classical
  let G := H ⊔ edge x y
  have hHG : H ≤ G := le_sup_left
  let E := D.image (liftSubgraph hHG)
  have hEcard : E.card = D.card := Finset.card_image_of_injective _ (liftSubgraph_injective hHG)
  have hEp : ∀ A ∈ E, IsNonemptyPathSubgraph A := by
    intro A hA
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hA
    exact (hp B hB).lift hHG
  have hEd : Set.PairwiseDisjoint (E : Set G.Subgraph) Subgraph.edgeSet := by
    intro A hA B hB hneAB
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hB
    exact hd.1 hI hJ (fun he => hneAB (he ▸ rfl))
  have hxy : G.Adj x y := Or.inr ((edge_adj x y x y).mpr ⟨Or.inl ⟨rfl,rfl⟩,hne⟩)
  have hmissing : ∀ A ∈ E, ¬A.Adj x y := by
    intro A hA
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hA
    exact fun he => hnadj (B.adj_sub he)
  have hEcover : (⋃ A : E, A.val.edgeSet) = H.edgeSet := by
    rw [← hd.2]
    ext e
    simp [E]
  have hcover : (⋃ A : E, A.val.edgeSet) ∪ {s(x,y)} = G.edgeSet := by
    rw [hEcover]
    change H.edgeSet ∪ {s(x,y)} = (H ⊔ edge x y).edgeSet
    rw [edgeSet_sup,edgeSet_edge_of_ne hne]
  have hcount (v : V) : endpointCount E v = endpointCount D v :=
    endpointCount_lift_image hHG D hp v
  have hbad : Finset.univ.filter (fun v => G.Adj x v ∧ v ≠ y ∧ endpointCount E v = 0) =
      Finset.univ.filter (fun v => H.Adj x v ∧ endpointCount D v = 0) := by
    apply Finset.filter_congr
    intro v _
    rw [hcount]
    have hneighbor : G.Adj x v ∧ v ≠ y ↔ H.Adj x v := by
      constructor
      · rintro ⟨hv,hvy⟩
        rcases hv with hv | hv
        · exact hv
        · have hh := (edge_adj x y x v).mp hv
          rcases hh.1 with ⟨_,hvy'⟩ | ⟨hxy',_⟩
          · exact (hvy hvy').elim
          · exact (hne hxy').elim
      · intro hv
        exact ⟨Or.inl hv,fun he => hnadj (he ▸ hv)⟩
    tauto
  have hdefE : (Finset.univ.filter (fun v => G.Adj x v ∧ v ≠ y ∧ endpointCount E v = 0)).card <
      endpointCount E y := by
    rw [hbad,hcount]
    exact hdef
  have hrest := restore_edge_of_endpoint_deficit E x y hEp hEd hxy hmissing hcover
    (by
      convert hdefE using 1
      congr 1
      ext v
      simp)
  rw [hEcard] at hrest
  exact hrest

end Erdos583
end
end Source37_Erdos583_EndpointDeficit
/- END Erdos583.EndpointDeficit -/

/- BEGIN Erdos583.StarRestoreOneEdge; source SHA256 5297f5256b904861f1384338fdcf24e78762eaf7fbcc2e7759ca83c1d7ed698d -/
section Source38_Erdos583_StarRestoreOneEdge


/-!
# One-edge star restoration with a root endpoint

This strengthens simultaneous restoration when exactly one edge is inserted.
-/

namespace Erdos583

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

namespace EndpointSelection

/-- For a single source, its terminal selects a root-avoiding path, and no
other endpoint of that member is selected. -/
theorem singleton_terminal_member [Fintype V] {D : Finset G.Subgraph} {x z : V}
    (S : EndpointSelection D x) (fallback : D)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) Subgraph.edgeSet)
    (hz : G.Adj x z) (hmissing : ∀ H ∈ D, ¬ H.Adj x z) :
    ∃ (t : V) (H : D), G.Adj x t ∧
      S.selectedSet fallback {z} H = {t} ∧
      x ∉ (S.presentation H).walk.support := by
  classical
  have houtside := S.deleted_edge_outside_predecessor_image hmissing
  obtain ⟨n,t,hn,ht⟩ := partialChain_terminal S.predecessor (S.predecessor_injective hd) z houtside
  have hxt := S.reachable_vertex_adj hz n hn
  let H := S.owner ⟨t,hxt⟩
  have havoid : x ∉ (S.presentation H).walk.support :=
    (S.predecessor_none_iff_avoids hxt).mp ht
  have htotal : S.totalOwner fallback t = H := by simp [totalOwner, hxt, H]
  have htselected : t ∈ S.selectedSet fallback {z} H :=
    ⟨⟨z,Finset.mem_singleton_self z,n,hn⟩,htotal⟩
  refine ⟨t,H,hxt,?_,havoid⟩
  ext v
  constructor
  · intro hv
    have hvterminal : S.predecessor v = none := by
      rw [S.selected_predecessor_eq fallback {z} (by simpa using hz) hv]
      simp [PathPresentation.predecessor, havoid]
    obtain ⟨w,hw,m,hm⟩ := hv.1
    have hwz : w = z := Finset.mem_singleton.mp hw
    subst w
    exact partialChain_terminal_unique S.predecessor z v t m n hm hvterminal hn ht
  · intro hv
    exact (Set.mem_singleton_iff.mp hv) ▸ htselected

/-- A realized single terminal transaction has degree one at the root. -/
theorem singleton_transaction_endpoint [Fintype V] {D : Finset G.Subgraph} {x z : V}
    (S : EndpointSelection D x) (fallback : D) (hz : G.Adj x z)
    (H : D) (t : V) (hselected : S.selectedSet fallback {z} H = {t})
    (havoid : x ∉ (S.presentation H).walk.support)
    (Q : G.Subgraph) (hp : IsNonemptyPathSubgraph Q)
    (he : Q.edgeSet = S.restorationEdges fallback {z} H) : PathStartsAt Q x := by
  classical
  let P := S.presentation H
  have hpred : P.predecessor x t = none := by simp [PathPresentation.predecessor, P, havoid]
  change (S.presentation H).predecessor x t = none at hpred
  have hedges : Q.edgeSet = H.val.edgeSet ∪ {s(x,t)} := by
    rw [he, ← S.selectedEdges_eq_restorationEdges fallback {z} (by simpa using hz) H,
      PathPresentation.selectedEdges, hselected]
    simp [PathPresentation.predecessorEdges, hpred]
  have hold (v : V) : ¬ H.val.Adj x v := by
    intro hv
    have hv' : s(x,v) ∈ P.walk.edgeSet := by rw [P.edgeSet_eq]; exact hv
    exact havoid (P.walk.fst_mem_support_of_mem_edges hv')
  have hneighbor : Q.neighborSet x = {t} := by
    ext v
    change Q.Adj x v ↔ v = t
    constructor
    · intro hv
      have hv' : s(x,v) ∈ Q.edgeSet := hv
      rw [hedges] at hv'
      rcases hv' with hv' | hv'
      · exact (hold v hv').elim
      · exact (Sym2.mkEmbedding x).injective (Set.mem_singleton_iff.mp hv')
    · intro hv
      subst v
      change s(x,t) ∈ Q.edgeSet
      rw [hedges]
      simp
  apply pathStartsAt_of_odd_subgraph_degree x hp
  rw [Subgraph.degree, Set.fintypeCard_eq_ncard, hneighbor]
  norm_num

/-- Restore one original edge and obtain a path partition with an endpoint at
the root. The residual partition is arbitrary under the endpoint hypothesis. -/
theorem restore_one [Fintype V] {D : Finset G.Subgraph} {x z : V}
    (S : EndpointSelection D x) (fallback : D)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) Subgraph.edgeSet)
    (hz : G.Adj x z) (hmissing : ∀ H ∈ D, ¬ H.Adj x z)
    (hcover : (⋃ H : D, H.val.edgeSet) ∪ {s(x,z)} = G.edgeSet) :
    ∃ P : Finset G.Subgraph,
      (∀ H ∈ P, IsNonemptyPathSubgraph H) ∧ IsDecomposition G P ∧
      P.card ≤ D.card ∧ ∃ H ∈ P, PathStartsAt H x := by
  classical
  have hzs : ∀ v ∈ ({z} : Finset V), G.Adj x v := by simpa using hz
  have hmiss : ∀ v ∈ ({z} : Finset V), ∀ H ∈ D, ¬ H.Adj x v := by simpa using hmissing
  have hcycles := S.cycle_indices_bound fallback hd {z} hzs hmiss
  have hzero : (Finset.univ.filter (S.createsCycle fallback {z})).card = 0 := by
    simp only [Finset.card_singleton] at hcycles
    omega
  have hncycles (H : D) : ¬ S.createsCycle fallback {z} H := by
    intro hc
    have hmem : H ∈ Finset.univ.filter (S.createsCycle fallback {z}) := by simp [hc]
    rw [Finset.card_eq_zero.mp hzero] at hmem
    exact Finset.notMem_empty H hmem
  choose out hp hc he using (fun H : D => S.realize_restorationEdges fallback {z} hzs H)
  have htrans := S.restorationEdges_partition fallback hd {z} hzs hmiss
  have hdout : Pairwise fun H J => Disjoint (out H).edgeSet (out J).edgeSet := by
    intro H J hne
    rw [he H, he J]
    exact htrans.1 hne
  have hcoverout : (⋃ H, (out H).edgeSet) = G.edgeSet := by
    simp_rw [he]
    rw [htrans.2]
    simpa using hcover
  obtain ⟨t,H,_,hselected,havoid⟩ := S.singleton_terminal_member fallback hd hz hmissing
  have hroot := S.singleton_transaction_endpoint fallback hz H t hselected havoid
    (out H) (hp H (hncycles H)) (he H)
  refine ⟨Finset.univ.image out, ?_, ?_, ?_, out H, Finset.mem_image.mpr ⟨H,Finset.mem_univ _,rfl⟩,hroot⟩
  · intro Q hQ
    obtain ⟨J,_,rfl⟩ := Finset.mem_image.mp hQ
    exact hp J (hncycles J)
  · constructor
    · intro Q hQ R hR hne
      obtain ⟨I,_,rfl⟩ := Finset.mem_image.mp hQ
      obtain ⟨J,_,rfl⟩ := Finset.mem_image.mp hR
      exact hdout (fun h => hne (h ▸ rfl))
    · rw [← hcoverout]
      ext e
      simp
  · exact (Finset.card_image_le).trans (by simp)

end EndpointSelection

theorem restore_one_edge_from_endpoint_partition [Fintype V]
    (D : Finset G.Subgraph) (x z : V)
    (hp : ∀ H ∈ D, IsNonemptyPathSubgraph H)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) Subgraph.edgeSet)
    (hz : G.Adj x z) (hmissing : ∀ H ∈ D, ¬ H.Adj x z)
    (hcover : (⋃ H : D, H.val.edgeSet) ∪ {s(x,z)} = G.edgeSet)
    (hend : ∀ v, G.Adj x v → ∃ H ∈ D, PathStartsAt H v) :
    ∃ P : Finset G.Subgraph,
      (∀ H ∈ P, IsNonemptyPathSubgraph H) ∧ IsDecomposition G P ∧
      P.card ≤ D.card ∧ ∃ H ∈ P, PathStartsAt H x := by
  classical
  let S := endpointSelection D x hp hend
  exact S.restore_one (S.owner ⟨z,hz⟩) hd hz hmissing hcover

end Erdos583
end Source38_Erdos583_StarRestoreOneEdge
/- END Erdos583.StarRestoreOneEdge -/

/- BEGIN Erdos583.ThreeStar; source SHA256 52139aa5d0e8b7bbe6b67a10025140d9361efec672dd210f352e1013b90e8051 -/
section Source39_Erdos583_ThreeStar





/-! Fixed-choice source restriction for a three-edge restoration. The source
subset is applied to the actual predecessor chains and selected path pieces. -/

noncomputable section
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
theorem chainReachable_mono {f : V → Option V} {Z W : Finset V} (hZW : Z ⊆ W)
    {v : V} (hv : ChainReachable f Z v) : ChainReachable f W v := by
  obtain ⟨z,hz,n,hn⟩ := hv
  exact ⟨z,hZW hz,n,hn⟩

namespace EndpointSelection
variable {D : Finset G.Subgraph} {x : V}

omit [Fintype V] in
theorem selectedSet_mono (S : EndpointSelection D x) (fallback : D)
    {Z W : Finset V} (hZW : Z ⊆ W) (H : D) :
    S.selectedSet fallback Z H ⊆ S.selectedSet fallback W H :=
  fun _ hv => ⟨chainReachable_mono hZW hv.1,hv.2⟩

omit [Fintype V] in
theorem createsCycle_mono (S : EndpointSelection D x) (fallback : D)
    {Z W : Finset V} (hZW : Z ⊆ W) (H : D)
    (h : S.createsCycle fallback Z H) : S.createsCycle fallback W H :=
  ⟨S.selectedSet_mono fallback hZW H h.1,S.selectedSet_mono fallback hZW H h.2.1,h.2.2⟩

omit [Fintype V] in
theorem omitted_chain_unreachable (S : EndpointSelection D x)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) Subgraph.edgeSet)
    (Z : Finset V) (hmissing : ∀ z ∈ Z, ∀ H ∈ D, ¬H.Adj x z)
    (z : Z) (n : ℕ) (v : V)
    (hn : (partialStep S.predecessor)^[n] (some z.val) = some v) :
    ¬ChainReachable S.predecessor (Z.erase z.val) v := by
  rintro ⟨w,hw,m,hm⟩
  have hwZ := (Finset.mem_erase.mp hw).2
  have he := (partialChain_meeting S.predecessor (S.predecessor_injective hd)
    w z.val (S.deleted_edge_outside_predecessor_image (hmissing w hwZ))
    (S.deleted_edge_outside_predecessor_image (hmissing z.val z.property)) m n v hm hn).1
  exact (Finset.mem_erase.mp hw).1 he

theorem selectedSet_singleton_of_no_cycle (S : EndpointSelection D x) (fallback : D)
    (Z : Finset V) (hz : ∀ z ∈ Z, G.Adj x z) (H : D) (t : V)
    (ht : t ∈ S.selectedSet fallback Z H)
    (havoid : x ∉ (S.presentation H).walk.support)
    (hnocycle : ¬S.createsCycle fallback Z H) : S.selectedSet fallback Z H = {t} := by
  ext v
  constructor
  · intro hv
    have hvend := S.selectedSet_subset_endpoints fallback Z hz H hv
    have htend := S.selectedSet_subset_endpoints fallback Z hz H ht
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hvend htend ⊢
    rcases hvend with hvend | hvend <;> rcases htend with htend | htend
    · exact hvend.trans htend.symm
    · exact (hnocycle ⟨hvend ▸ hv,htend ▸ ht,havoid⟩).elim
    · exact (hnocycle ⟨htend ▸ ht,hvend ▸ hv,havoid⟩).elim
    · exact hvend.trans htend.symm
  · intro hv
    exact (Set.mem_singleton_iff.mp hv) ▸ ht

/-- With three sources and an actual cycle-producing old member, omit the
source feeding one of its endpoints. The restricted fixed construction has no
cycle and has two distinct root-avoiding old members selected at one end each. -/
theorem three_source_profile (S : EndpointSelection D x) (fallback : D)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) Subgraph.edgeSet)
    (Z : Finset V) (hZ : Z.card = 3) (hz : ∀ z ∈ Z, G.Adj x z)
    (hmissing : ∀ z ∈ Z, ∀ H ∈ D, ¬H.Adj x z)
    (A : D) (hA : S.createsCycle fallback Z A) :
    ∃ b ∈ Z,
      (∀ H : D, ¬S.createsCycle fallback (Z.erase b) H) ∧
      ∃ (H J : D) (t u : V), H ≠ J ∧
        S.selectedSet fallback (Z.erase b) H = {t} ∧
        S.selectedSet fallback (Z.erase b) J = {u} ∧
        x ∉ (S.presentation H).walk.support ∧ x ∉ (S.presentation J).walk.support := by
  classical
  have hout z hz' := S.deleted_edge_outside_predecessor_image (hmissing z hz')
  obtain ⟨terminal,htinj,ht⟩ := exists_injective_terminal_map S.predecessor
    (S.predecessor_injective hd) Z hout
  have hterminal (H : D) (v : V) (hv : v ∈ S.selectedSet fallback Z H)
      (havoid : x ∉ (S.presentation H).walk.support) : S.predecessor v = none := by
    rw [S.selected_predecessor_eq fallback Z hz hv]
    simp [PathPresentation.predecessor,havoid]
  obtain ⟨a,ha,na,hna⟩ := hA.1.1
  obtain ⟨b,hb,nb,hnb⟩ := hA.2.1.1
  let za : Z := ⟨a,ha⟩
  let zb : Z := ⟨b,hb⟩
  have hta : terminal za = (S.presentation A).start := by
    obtain ⟨n,hn⟩ := (ht za).2
    exact partialChain_terminal_unique S.predecessor a (terminal za) _ n na hn (ht za).1
      hna (hterminal A _ hA.1 hA.2.2)
  have htb : terminal zb = (S.presentation A).finish := by
    obtain ⟨n,hn⟩ := (ht zb).2
    exact partialChain_terminal_unique S.predecessor b (terminal zb) _ n nb hn (ht zb).1
      hnb (hterminal A _ hA.2.1 hA.2.2)
  have hab : a ≠ b := by
    intro he
    have hzab : za = zb := Subtype.ext he
    have hend := hta.symm.trans ((congrArg terminal hzab).trans htb)
    exact (S.presentation A).nonempty ((S.presentation A).isPath.nil_iff_eq.mpr hend)
  have hthird : ∃ c ∈ Z, c ≠ a ∧ c ≠ b := by
    by_contra hn
    have hsub : Z ⊆ {a,b} := by
      intro c hc
      by_cases hca : c = a
      · simp [hca]
      · have hcb : c = b := by by_contra hcb; exact hn ⟨c,hc,hca,hcb⟩
        simp [hcb]
    have hh := Finset.card_le_card hsub
    have hpair : ({a,b} : Finset V).card = 2 := by simp [hab]
    omega
  obtain ⟨c,hc,hca,hcb⟩ := hthird
  let zc : Z := ⟨c,hc⟩
  have hbound := S.cycle_indices_bound fallback hd Z hz hmissing
  have hunique (H : D) (hH : S.createsCycle fallback Z H) : H = A := by
    by_contra hne
    have hsub : ({H,A} : Finset D) ⊆ Finset.univ.filter (S.createsCycle fallback Z) := by
      intro J hJ
      rcases Finset.mem_insert.mp hJ with rfl | hJ
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hH⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_singleton.mp hJ) ▸ hA⟩
    have hh := Finset.card_le_card hsub
    have hpair : ({H,A} : Finset D).card = 2 := by simp [hne]
    omega
  have hnoA : ¬S.createsCycle fallback (Z.erase a) A := by
    intro hh
    exact S.omitted_chain_unreachable hd Z hmissing za na _ hna hh.1.1
  have hno (H : D) : ¬S.createsCycle fallback (Z.erase a) H := by
    intro hh
    have he := hunique H (S.createsCycle_mono fallback (Finset.erase_subset a Z) H hh)
    exact hnoA (he ▸ hh)
  have hzb : b ∈ Z.erase a := Finset.mem_erase.mpr ⟨hab.symm,hb⟩
  have hzc : c ∈ Z.erase a := Finset.mem_erase.mpr ⟨hca,hc⟩
  have hzbAdj : ∀ z ∈ Z.erase a, G.Adj x z := fun z hz' => hz z (Finset.mem_erase.mp hz').2
  have hfinish : (S.presentation A).finish ∈ S.selectedSet fallback (Z.erase a) A :=
    ⟨⟨b,hzb,nb,hnb⟩,hA.2.1.2⟩
  obtain ⟨nc,hnc⟩ := (ht zc).2
  have hxtc : G.Adj x (terminal zc) := S.reachable_vertex_adj (hz c hc) nc hnc
  let J := S.owner ⟨terminal zc,hxtc⟩
  have hJavoid : x ∉ (S.presentation J).walk.support :=
    (S.predecessor_none_iff_avoids hxtc).mp (ht zc).1
  have hJselected : terminal zc ∈ S.selectedSet fallback (Z.erase a) J :=
    ⟨⟨c,hzc,nc,hnc⟩,by simp [totalOwner,hxtc,J]⟩
  have hJA : J ≠ A := by
    intro he
    have hend := S.selectedSet_subset_endpoints fallback (Z.erase a) hzbAdj J hJselected
    rw [he] at hend
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hend
    rcases hend with hstart | hfinish
    · have hh := htinj (hstart.trans hta.symm)
      exact hca (congrArg Subtype.val hh)
    · have hh := htinj (hfinish.trans htb.symm)
      exact hcb (congrArg Subtype.val hh)
  refine ⟨a,ha,hno,A,J,(S.presentation A).finish,terminal zc,hJA.symm,?_,?_,hA.2.2,hJavoid⟩
  · exact S.selectedSet_singleton_of_no_cycle fallback (Z.erase a) hzbAdj A _ hfinish hA.2.2 (hno A)
  · exact S.selectedSet_singleton_of_no_cycle fallback (Z.erase a) hzbAdj J _ hJselected hJavoid (hno J)

/-- A singleton selected endpoint on an old root-avoiding path creates an
actual root endpoint, for any chosen source subset. -/
theorem singleton_selected_root_endpoint (S : EndpointSelection D x) (fallback : D)
    (Z : Finset V) (hz : ∀ z ∈ Z, G.Adj x z) (H : D) (t : V)
    (hselected : S.selectedSet fallback Z H = {t})
    (havoid : x ∉ (S.presentation H).walk.support)
    (Q : G.Subgraph) (hp : IsNonemptyPathSubgraph Q)
    (he : Q.edgeSet = S.restorationEdges fallback Z H) : PathStartsAt Q x := by
  let P := S.presentation H
  have hpred : P.predecessor x t = none := by simp [PathPresentation.predecessor,P,havoid]
  change (S.presentation H).predecessor x t = none at hpred
  have hedges : Q.edgeSet = H.val.edgeSet ∪ {s(x,t)} := by
    rw [he, ← S.selectedEdges_eq_restorationEdges fallback Z hz H,
      PathPresentation.selectedEdges,hselected]
    simp [PathPresentation.predecessorEdges,hpred]
  have hold (v : V) : ¬H.val.Adj x v := by
    intro hv
    have hv' : s(x,v) ∈ P.walk.edgeSet := by rw [P.edgeSet_eq]; exact hv
    exact havoid (P.walk.fst_mem_support_of_mem_edges hv')
  have hneighbor : Q.neighborSet x = {t} := by
    ext v
    change Q.Adj x v ↔ v = t
    constructor
    · intro hv
      have hv' : s(x,v) ∈ Q.edgeSet := hv
      rw [hedges] at hv'
      rcases hv' with hv' | hv'
      · exact (hold v hv').elim
      · exact (Sym2.mkEmbedding x).injective (Set.mem_singleton_iff.mp hv')
    · intro hv
      subst v
      change s(x,t) ∈ Q.edgeSet
      rw [hedges]
      simp
  apply pathStartsAt_of_odd_subgraph_degree x hp
  rw [Subgraph.degree,Set.fintypeCard_eq_ncard,hneighbor]
  norm_num

end EndpointSelection

omit [Fintype V] in
theorem pathPartition_two_endpoints_of_indexed {ι : Type*} [Fintype ι]
    (out : ι → G.Subgraph) (hp : ∀ i, IsNonemptyPathSubgraph (out i))
    (hd : Pairwise fun i j => Disjoint (out i).edgeSet (out j).edgeSet)
    (hcover : (⋃ i, (out i).edgeSet) = G.edgeSet)
    (x : V) (i j : ι) (hij : i ≠ j)
    (hi : PathStartsAt (out i) x) (hj : PathStartsAt (out j) x) :
    ∃ P : Finset G.Subgraph, (∀ H ∈ P, IsNonemptyPathSubgraph H) ∧
      IsDecomposition G P ∧ P.card ≤ Fintype.card ι ∧ 2 ≤ endpointCount P x := by
  classical
  let P := Finset.univ.image out
  have hmem (i : ι) : out i ∈ P := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hne : out i ≠ out j := by
    intro he
    obtain ⟨e,hei⟩ := (hp i).edgeSet_nonempty
    exact Set.disjoint_left.mp (hd hij) hei (he ▸ hei)
  refine ⟨P,?_,⟨?_,?_⟩,Finset.card_image_le.trans (by simp),?_⟩
  · intro H hH
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hH
    exact hp k
  · intro H hH J hJ hHJ
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hJ
    exact hd (fun he => hHJ (he ▸ rfl))
  · rw [← hcover]
    ext e
    simp [P]
  · have hsub : {out i,out j} ⊆ P.filter (fun H => PathStartsAt H x) := by
      intro H hH
      rcases Finset.mem_insert.mp hH with rfl | hH
      · exact Finset.mem_filter.mpr ⟨hmem i,hi⟩
      · have he : H = out j := Finset.mem_singleton.mp hH
        subst H
        exact Finset.mem_filter.mpr ⟨hmem j,hj⟩
    have hh := Finset.card_le_card hsub
    simpa only [Finset.card_pair hne,endpointCount] using hh

namespace EndpointSelection
variable {D : Finset G.Subgraph} {x : V}

/-- Three-source fixed-choice restriction, realized in the actual graph with
one original source edge deleted. Two distinct output paths end at the root. -/
theorem restore_three_omit_one (S : EndpointSelection D x) (fallback : D)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) Subgraph.edgeSet)
    (Z : Finset V) (hZ : Z.card = 3) (hz : ∀ z ∈ Z, G.Adj x z)
    (hmissing : ∀ z ∈ Z, ∀ H ∈ D, ¬H.Adj x z)
    (hcover : (⋃ H : D, H.val.edgeSet) ∪ (fun v => s(x,v)) '' (Z : Set V) = G.edgeSet)
    (A : D) (hA : S.createsCycle fallback Z A) :
    ∃ b ∈ Z, ∃ P : Finset (G.deleteEdges {s(x,b)}).Subgraph,
      (∀ H ∈ P, IsNonemptyPathSubgraph H) ∧ IsDecomposition (G.deleteEdges {s(x,b)}) P ∧
      P.card ≤ D.card ∧ 2 ≤ endpointCount P x := by
  classical
  obtain ⟨b,hb,hnocycle,H,J,t,u,hHJ,hHsingle,hJsingle,hHavoid,hJavoid⟩ :=
    S.three_source_profile fallback hd Z hZ hz hmissing A hA
  have hsub : Z.erase b ⊆ Z := Finset.erase_subset b Z
  have hz' : ∀ z ∈ Z.erase b, G.Adj x z := fun z hz' => hz z (hsub hz')
  have hm' : ∀ z ∈ Z.erase b, ∀ H ∈ D, ¬H.Adj x z := fun z hz' => hmissing z (hsub hz')
  choose out hp hc he using (fun I : D => S.realize_restorationEdges fallback (Z.erase b) hz' I)
  have houtp (I : D) : IsNonemptyPathSubgraph (out I) := hp I (hnocycle I)
  have htrans := S.restorationEdges_partition fallback hd (Z.erase b) hz' hm'
  have hdout : Pairwise fun I K : D => Disjoint (out I).edgeSet (out K).edgeSet := by
    intro I K hIK
    rw [he I,he K]
    exact htrans.1 hIK
  have hpartial : (⋃ I : D, (out I).edgeSet) =
      (⋃ I : D, I.val.edgeSet) ∪ (fun v => s(x,v)) '' (Z.erase b : Set V) := by
    simp_rw [he]
    exact htrans.2
  have htarget : (⋃ I : D, (out I).edgeSet) = (G.deleteEdges {s(x,b)}).edgeSet := by
    rw [hpartial,edgeSet_deleteEdges,← hcover]
    ext e
    constructor
    · rintro (he | ⟨v,hv,rfl⟩)
      · refine ⟨Or.inl he,?_⟩
        intro heb
        have heb' : e = s(x,b) := Set.mem_singleton_iff.mp heb
        obtain ⟨I,heI⟩ := Set.mem_iUnion.mp he
        exact hmissing b hb I.val I.property (show s(x,b) ∈ I.val.edgeSet from heb' ▸ heI)
      · refine ⟨Or.inr ⟨v,hsub hv,rfl⟩,?_⟩
        intro hvb
        exact (Finset.mem_erase.mp hv).1 ((Sym2.mkEmbedding x).injective
          (Set.mem_singleton_iff.mp hvb))
    · rintro ⟨he,hn⟩
      rcases he with he | ⟨v,hv,rfl⟩
      · exact Or.inl he
      · refine Or.inr ⟨v,Finset.mem_erase.mpr ⟨?_,hv⟩,rfl⟩
        intro hvb
        apply hn
        simp [hvb]
  have hendH := S.singleton_selected_root_endpoint fallback (Z.erase b) hz' H t hHsingle hHavoid
    (out H) (houtp H) (he H)
  have hendJ := S.singleton_selected_root_endpoint fallback (Z.erase b) hz' J u hJsingle hJavoid
    (out J) (houtp J) (he J)
  have hsubedges (I : D) : (out I).edgeSet ⊆ (G.deleteEdges {s(x,b)}).edgeSet := by
    rw [← htarget]
    exact Set.subset_iUnion (fun I : D => (out I).edgeSet) I
  let rebased (I : D) := rebaseSubgraph (out I) (hsubedges I)
  have hrp (I : D) : IsNonemptyPathSubgraph (rebased I) := (houtp I).rebase (hsubedges I)
  have hrd : Pairwise fun I K : D => Disjoint (rebased I).edgeSet (rebased K).edgeSet := hdout
  have hrc : (⋃ I : D, (rebased I).edgeSet) = (G.deleteEdges {s(x,b)}).edgeSet := htarget
  obtain ⟨P,hP,hPD,hPc,hPe⟩ := pathPartition_two_endpoints_of_indexed rebased hrp hrd hrc
    x H J hHJ (hendH.rebase (hsubedges H)) (hendJ.rebase (hsubedges J))
  exact ⟨b,hb,P,hP,hPD,by simpa using hPc,hPe⟩

theorem restore_no_cycle (S : EndpointSelection D x) (fallback : D)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) Subgraph.edgeSet)
    (Z : Finset V) (hz : ∀ z ∈ Z, G.Adj x z)
    (hmissing : ∀ z ∈ Z, ∀ H ∈ D, ¬H.Adj x z)
    (hcover : (⋃ H : D, H.val.edgeSet) ∪ (fun v => s(x,v)) '' (Z : Set V) = G.edgeSet)
    (hnocycle : ∀ H : D, ¬S.createsCycle fallback Z H) : HasPathPartition G D.card := by
  choose out hp hc he using (fun I : D => S.realize_restorationEdges fallback Z hz I)
  have htrans := S.restorationEdges_partition fallback hd Z hz hmissing
  obtain ⟨P,hP,hPD,hPE,hPc⟩ := pathFamily_of_indexed out
    (fun I => hp I (hnocycle I)) (by
      intro I J hIJ
      rw [he I,he J]
      exact htrans.1 hIJ)
  refine ⟨P,hP,⟨hPD,?_⟩,by simpa using hPc⟩
  have hcov : (⋃ H : P, H.val.edgeSet) = G.edgeSet := by
    rw [hPE]
    simp_rw [he]
    exact htrans.2.trans hcover
  rw [← hcov]
  ext e
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨H,hH,he⟩
    exact ⟨⟨H,hH⟩,he⟩
  · rintro ⟨H,he⟩
    exact ⟨H.val,H.property,he⟩

end EndpointSelection

/-- Actual even-neighbor star deletion with exactly three sources: either all
three edges restore without cycles, or omitting one edge gives two root ends. -/
theorem restore_three_even_neighbors (G : SimpleGraph V) (x : V) {q : ℕ}
    (hthree : evenNeighborCount G x = 3)
    (hq : HasPathPartition (starDeleteEven G x) q) :
    HasPathPartition G q ∨
      ∃ b ∈ evenNeighbors G x, ∃ P : Finset (G.deleteEdges {s(x,b)}).Subgraph,
        (∀ H ∈ P, IsNonemptyPathSubgraph H) ∧ IsDecomposition (G.deleteEdges {s(x,b)}) P ∧
        P.card ≤ q ∧ 2 ≤ endpointCount P x := by
  classical
  let J := starDeleteEven G x
  let hJG : J ≤ G := starDeleteEven_le G x
  obtain ⟨D,hpath,hdec,hcard⟩ := hq
  let E := D.image (liftSubgraph hJG)
  have hEpath : ∀ H ∈ E, IsNonemptyPathSubgraph H := by
    intro H hH
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hH
    exact (hpath P hP).lift hJG
  have hEdis : Set.PairwiseDisjoint (E : Set G.Subgraph) Subgraph.edgeSet := by
    intro H hH K hK hne
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hK
    exact hdec.1 hP hQ (fun he => hne (he ▸ rfl))
  have hEcover : (⋃ H : E, H.val.edgeSet) = J.edgeSet := by
    rw [← hdec.2]
    ext e
    simp [E]
    rfl
  have hmissing : ∀ z ∈ evenNeighbors G x, ∀ H ∈ E, ¬H.Adj x z := by
    intro z hz H hH hadj
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hH
    have hjadj : J.Adj x z := P.adj_sub hadj
    exact hjadj.2.1 ⟨rfl,(mem_evenNeighbors G x z).mp hz |>.2⟩
  have hend : ∀ v, G.Adj x v → ∃ H ∈ E, PathStartsAt H v := by
    intro v hv
    obtain ⟨P,hP,hpend⟩ := exists_pathStartsAt_of_odd D hpath hdec v
      (original_neighbor_odd_after_starDeleteEven G x v hv)
    exact ⟨liftSubgraph hJG P,Finset.mem_image.mpr ⟨P,hP,rfl⟩,hpend.lift hJG⟩
  let S := endpointSelection E x hEpath hend
  have hz : ∀ z ∈ evenNeighbors G x, G.Adj x z := fun z hz => (mem_evenNeighbors G x z).mp hz |>.1
  have hcov : (⋃ H : E, H.val.edgeSet) ∪
      (fun v => s(x,v)) '' (evenNeighbors G x : Set V) = G.edgeSet := by
    rw [hEcover]
    exact starDeleteEven_edge_cover G x
  have hZ : (evenNeighbors G x).card = 3 := hthree
  have hZne : (evenNeighbors G x).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨z,hzZ⟩ := hZne
  let fallback := S.owner ⟨z,hz z hzZ⟩
  have hEcard : E.card ≤ q := Finset.card_image_le.trans hcard
  by_cases hcyc : ∃ A : E, S.createsCycle fallback (evenNeighbors G x) A
  · obtain ⟨A,hA⟩ := hcyc
    obtain ⟨b,hb,P,hP,hPD,hPc,hPe⟩ := S.restore_three_omit_one fallback hEdis
      (evenNeighbors G x) hZ hz hmissing hcov A hA
    exact Or.inr ⟨b,hb,P,hP,hPD,hPc.trans hEcard,hPe⟩
  · have hrest := S.restore_no_cycle fallback hEdis (evenNeighbors G x) hz hmissing hcov
      (fun H hH => hcyc ⟨H,hH⟩)
    obtain ⟨P,hP,hPD,hPc⟩ := hrest
    exact Or.inl ⟨P,hP,hPD,hPc.trans hEcard⟩

/-- At an even center, deleting the omitted incident edge makes its degree
odd. The two distinct exposed root ends therefore force at least three ends. -/
theorem restore_three_even_neighbors_even_center (G : SimpleGraph V) (x : V) {q : ℕ}
    (hthree : evenNeighborCount G x = 3) (heven : Even (G.degree x))
    (hq : HasPathPartition (starDeleteEven G x) q) :
    HasPathPartition G q ∨
      ∃ b ∈ evenNeighbors G x, ∃ P : Finset (G.deleteEdges {s(x,b)}).Subgraph,
        (∀ H ∈ P, IsNonemptyPathSubgraph H) ∧ IsDecomposition (G.deleteEdges {s(x,b)}) P ∧
        P.card ≤ q ∧ 3 ≤ endpointCount P x := by
  classical
  rcases restore_three_even_neighbors G x hthree hq with h | ⟨b,hb,P,hP,hPD,hPc,hPe⟩
  · exact Or.inl h
  · have hxb : G.Adj x b := (mem_evenNeighbors G x b).mp hb |>.1
    have hdegree : (G.deleteEdges {s(x,b)}).degree x + 1 = G.degree x := by
      have hcard := Finset.card_erase_add_one ((mem_neighborFinset G x b).mpr hxb)
      rw [← neighborFinset_delete_single_edge_left G x b] at hcard
      simpa only [card_neighborFinset_eq_degree] using hcard
    have hodd : Odd ((G.deleteEdges {s(x,b)}).degree x) := by
      obtain ⟨k,hk⟩ := heven
      apply Nat.odd_iff.mpr
      omega
    have heodd := (endpointCount_odd_iff P hP hPD x).mpr
      (by
        convert hodd using 1
        unfold degree
        congr 1
        ext v
        simp)
    refine Or.inr ⟨b,hb,P,hP,hPD,hPc,?_⟩
    have hh := Nat.odd_iff.mp heodd
    omega

end Erdos583
end
end Source39_Erdos583_ThreeStar
/- END Erdos583.ThreeStar -/

/- BEGIN Erdos583.TerminalSwitch; source SHA256 b1063060a69e22ee818e58c093829e1db98afd4198049bec828e3a63fe67b94f -/
section Source40_Erdos583_TerminalSwitch




/-! Actual terminal edge restoration from two root endpoints. -/
noncomputable section
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

theorem degree_delete_single_edge_left (G : SimpleGraph V) {x a : V}
    (hxa : G.Adj x a) : (G.deleteEdges {s(x,a)}).degree x = G.degree x - 1 := by
  classical
  rw [← card_neighborFinset_eq_degree, neighborFinset_delete_single_edge_left,
    Finset.card_erase_of_mem ((G.mem_neighborFinset x a).mpr hxa),
    card_neighborFinset_eq_degree]

theorem degree_delete_single_edge_other (G : SimpleGraph V) {x a v : V}
    (hvx : v ≠ x) (hva : v ≠ a) :
    (G.deleteEdges {s(x,a)}).degree v = G.degree v := by
  classical
  rw [← card_neighborFinset_eq_degree,
    neighborFinset_delete_single_edge_other G hvx hva, card_neighborFinset_eq_degree]

/-- All endpoint-free neighbors of the omitted source were originally even;
the even root was removed from its neighborhood. -/
theorem terminal_endpoint_free_card_le_two (G : SimpleGraph V) {x a : V}
    (hxa : G.Adj x a) (hx : Even (G.degree x))
    (ha : evenNeighborCount G a ≤ 3)
    (D : Finset (G.deleteEdges {s(x,a)}).Subgraph)
    (hp : ∀ P ∈ D, IsNonemptyPathSubgraph P)
    (hd : IsDecomposition (G.deleteEdges {s(x,a)}) D) :
    (Finset.univ.filter (fun v => (G.deleteEdges {s(x,a)}).Adj a v ∧
      endpointCount D v = 0)).card ≤ 2 := by
  classical
  have hs : (Finset.univ.filter (fun v => (G.deleteEdges {s(x,a)}).Adj a v ∧
      endpointCount D v = 0)) ⊆ (evenNeighbors G a).erase x := by
    intro v hv
    obtain ⟨_,hvA,hzero⟩ := Finset.mem_filter.mp hv
    have hvx : v ≠ x := by
      intro h; subst v
      exact hvA.2 ⟨Sym2.eq_swap,hxa.ne.symm⟩
    have hva : v ≠ a := hvA.1.ne.symm
    have he : Even (G.degree v) := by
      by_contra hn
      have ho := Nat.not_even_iff_odd.mp hn
      have hdeg := degree_delete_single_edge_other G hvx hva
      have hoJ : Odd ((G.deleteEdges {s(x,a)}).degree v) := by rwa [hdeg]
      have hoE : Odd (endpointCount D v) := by
        apply (endpointCount_odd_iff D hp hd v).mpr
        convert hoJ using 2
      have hpos := hoE.pos
      omega
    exact Finset.mem_erase.mpr ⟨hvx,(mem_evenNeighbors G a v).mpr ⟨hvA.1,he⟩⟩
  have hc := Finset.card_le_card hs
  have hxmem := (mem_evenNeighbors G a x).mpr ⟨hxa.symm,hx⟩
  have he := Finset.card_erase_add_one hxmem
  change ((evenNeighbors G a).erase x).card + 1 = evenNeighborCount G a at he
  omega

/-- Odd root degree promotes two endpoints to at least three; the exact
endpoint-deficit switch then restores the missing original edge for free. -/
theorem restore_terminal_edge (G : SimpleGraph V) {x a : V}
    (hxa : G.Adj x a) (hx : Even (G.degree x))
    (ha : evenNeighborCount G a ≤ 3)
    (D : Finset (G.deleteEdges {s(x,a)}).Subgraph)
    (hp : ∀ P ∈ D, IsNonemptyPathSubgraph P)
    (hd : IsDecomposition (G.deleteEdges {s(x,a)}) D)
    (hend : 2 ≤ endpointCount D x) : HasPathPartition G D.card := by
  classical
  have hxodd : Odd ((G.deleteEdges {s(x,a)}).degree x) := by
    rw [degree_delete_single_edge_left G hxa]
    exact Nat.Even.sub_odd (by have := hxa.degree_pos_left; omega) hx (by decide)
  have heodd : Odd (endpointCount D x) := by
    apply (endpointCount_odd_iff D hp hd x).mpr
    convert hxodd using 2
  have hthree : 3 ≤ endpointCount D x := by obtain ⟨j,hj⟩ := heodd; omega
  have hfree := terminal_endpoint_free_card_le_two G hxa hx ha D hp hd
  have hnot : ¬ (G.deleteEdges {s(x,a)}).Adj a x := by
    intro h
    exact h.2 ⟨Sym2.eq_swap,hxa.ne.symm⟩
  have hbound := add_edge_pathPartition_of_endpoint_deficit _ D hp hd a x hxa.ne.symm hnot
    (by
      have hlt := lt_of_le_of_lt hfree (by omega : 2 < endpointCount D x)
      convert hlt using 2 <;> congr 1)
  have heq : G.deleteEdges {s(x,a)} ⊔ edge a x = G := by
    ext u v
    simp only [sup_adj, deleteEdges_adj, edge_adj, Set.mem_singleton_iff, Sym2.eq_iff]
    constructor
    · rintro (⟨h,_⟩ | ⟨(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩),_⟩)
      · exact h
      · exact hxa.symm
      · exact hxa
    · intro huv
      by_cases he : s(u,v) = s(x,a)
      · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inr ⟨Or.inr ⟨rfl,rfl⟩,huv.ne⟩
        · exact Or.inr ⟨Or.inl ⟨rfl,rfl⟩,huv.ne⟩
      · exact Or.inl ⟨huv, fun h => he (Sym2.eq_iff.mpr h)⟩
  rwa [heq] at hbound

/-- Close a three-neighbor star when each possible omitted source has at
most three original even neighbors. The input partition is arbitrary. -/
theorem restore_terminal_three_star (G : SimpleGraph V) (x : V) {q : ℕ}
    (hthree : evenNeighborCount G x = 3) (hx : Even (G.degree x))
    (hsmall : ∀ a ∈ evenNeighbors G x, evenNeighborCount G a ≤ 3)
    (hq : HasPathPartition (starDeleteEven G x) q) : HasPathPartition G q := by
  classical
  rcases restore_three_even_neighbors_even_center G x hthree hx hq with h | h
  · exact h
  · obtain ⟨a,ha,D,hp,hd,hcard,hend⟩ := h
    have hxa := (mem_evenNeighbors G x a).mp ha
    have hpart := restore_terminal_edge G hxa.1 hx (hsmall a ha) D hp hd (by omega)
    exact hpart.mono hcard

end Erdos583
end
end Source40_Erdos583_TerminalSwitch
/- END Erdos583.TerminalSwitch -/

/- BEGIN Erdos583.TerminalCore; source SHA256 a2ca3ec5b8ee9a4c4c36580b60a2ae7fdfacc0ae3dfcc7183ed845724161fb0a -/
section Source41_Erdos583_TerminalCore




/-! Concrete closed even-core reductions. The consumers require a path
partition of the displayed residual graph, and assume no baseline theorem. -/

noncomputable section
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

/-- Closure in the original even core bounds every original even neighbor. -/
theorem evenNeighbors_subset_closed (G : SimpleGraph V) (S : Finset V)
    (heven : ∀ u ∈ S, Even (G.degree u))
    (hclosed : ∀ u ∈ S, ∀ v, (evenCore G).Adj u v → v ∈ S)
    {u : V} (hu : u ∈ S) : evenNeighbors G u ⊆ S.erase u := by
  intro v hv
  obtain ⟨huv, hvEven⟩ := (mem_evenNeighbors G u v).mp hv
  exact Finset.mem_erase.mpr ⟨huv.ne.symm,
    hclosed u hu v ⟨huv, heven u hu, hvEven⟩⟩

/-- A universal vertex in a closed set sees exactly the other set members
among the original even vertices. -/
theorem evenNeighbors_eq_closed_hub (G : SimpleGraph V) (S : Finset V)
    (heven : ∀ u ∈ S, Even (G.degree u))
    (hclosed : ∀ u ∈ S, ∀ v, (evenCore G).Adj u v → v ∈ S)
    {x : V} (hx : x ∈ S) (hhub : ∀ v ∈ S, v ≠ x → G.Adj x v) :
    evenNeighbors G x = S.erase x := by
  apply Finset.Subset.antisymm (evenNeighbors_subset_closed G S heven hclosed hx)
  intro v hv
  obtain ⟨hvx, hvS⟩ := Finset.mem_erase.mp hv
  exact (mem_evenNeighbors G x v).mpr ⟨hhub v hvS hvx, heven v hvS⟩

/-- Every vertex of a closed four-vertex clique has exactly three original
even neighbors. -/
theorem closed_four_evenNeighborCount (G : SimpleGraph V) (S : Finset V)
    (heven : ∀ u ∈ S, Even (G.degree u))
    (hclosed : ∀ u ∈ S, ∀ v, (evenCore G).Adj u v → v ∈ S)
    (hcard : S.card = 4)
    (hclique : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v)
    {u : V} (hu : u ∈ S) : evenNeighborCount G u = 3 := by
  have hE := evenNeighbors_eq_closed_hub G S heven hclosed hu
    (fun v hv hne => hclique u hu v hv hne.symm)
  unfold evenNeighborCount
  rw [hE, Finset.card_erase_of_mem hu, hcard]

/-- The closed four-clique reduction restores any residual partition at the
same path budget. -/
theorem restore_closed_four (G : SimpleGraph V) (S : Finset V)
    (heven : ∀ u ∈ S, Even (G.degree u))
    (hclosed : ∀ u ∈ S, ∀ v, (evenCore G).Adj u v → v ∈ S)
    (hcard : S.card = 4)
    (hclique : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v)
    {x : V} (hx : x ∈ S) {q : ℕ}
    (hq : HasPathPartition (starDeleteEven G x) q) : HasPathPartition G q := by
  apply restore_terminal_three_star G x
    (closed_four_evenNeighborCount G S heven hclosed hcard hclique hx)
    (heven x hx) _ hq
  intro a ha
  have haS := (Finset.mem_erase.mp
    (evenNeighbors_subset_closed G S heven hclosed hx ha)).2
  exact le_of_eq (closed_four_evenNeighborCount G S heven hclosed hcard hclique haS)

/-- The actual four-clique residual strictly lowers the induction measure,
does not increase the potential, and suffices at its own potential budget. -/
theorem closed_four_reduction (G : SimpleGraph V) (S : Finset V)
    (heven : ∀ u ∈ S, Even (G.degree u))
    (hclosed : ∀ u ∈ S, ∀ v, (evenCore G).Adj u v → v ∈ S)
    (hcard : S.card = 4)
    (hclique : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v)
    {x : V} (hx : x ∈ S) :
    edgeExcess (starDeleteEven G x) < edgeExcess G ∧
    phi (starDeleteEven G x) ≤ phi G ∧
    (HasPathBound (starDeleteEven G x) (phi (starDeleteEven G x)) →
      HasPathBound G (phi G)) := by
  have hk := closed_four_evenNeighborCount G S heven hclosed hcard hclique hx
  have hdrop := phi_starDeleteEven_drop G x
  rw [hk] at hdrop
  have hphi : phi (starDeleteEven G x) ≤ phi G := by norm_num at hdrop; linarith
  refine ⟨edgeExcess_starDeleteEven_lt G x (by omega), hphi, ?_⟩
  intro hb
  obtain ⟨q, hq, hqb⟩ := hasPathBound_iff_exists_partition.mp hb
  exact hasPathBound_iff_exists_partition.mpr ⟨q,
    restore_closed_four G S heven hclosed hcard hclique hx hq, hqb.trans hphi⟩

/-- Attaching a leaf to an original even vertex removes that vertex from
every old vertex's even-neighbor set, whether or not they are adjacent. -/
theorem attachLeaf_evenNeighbors_any (G : SimpleGraph V) (f u : V)
    (hf : Even (G.degree f)) :
    evenNeighbors (attachLeaf G f) (some u) =
      ((evenNeighbors G u).erase f).map someEmbedding := by
  ext v
  cases v with
  | none => simp [mem_evenNeighbors, attachLeaf_degree_new, someEmbedding]
  | some v =>
    have hnot : ¬ Even (G.degree f + 1) :=
      Nat.not_even_iff_odd.mpr (hf.add_odd (by decide))
    by_cases hv : v = f
    · subst v
      simp [someEmbedding, attachLeaf_degree_some, hnot]
    · simp [someEmbedding, attachLeaf_degree_some, hv]

/-- In a closed five-vertex original-even set, attaching a leaf to one
member leaves at most three even neighbors at every other member. -/
theorem closed_five_leaf_neighbor_bound (G : SimpleGraph V) (S : Finset V)
    (heven : ∀ u ∈ S, Even (G.degree u))
    (hclosed : ∀ u ∈ S, ∀ v, (evenCore G).Adj u v → v ∈ S)
    (hcard : S.card = 5) {f u : V} (hf : f ∈ S) (hu : u ∈ S) (huf : u ≠ f) :
    evenNeighborCount (attachLeaf G f) (some u) ≤ 3 := by
  unfold evenNeighborCount
  rw [attachLeaf_evenNeighbors_any G f u (heven f hf), Finset.card_map]
  have hsub : (evenNeighbors G u).erase f ⊆ (S.erase u).erase f :=
    Finset.erase_subset_erase f (evenNeighbors_subset_closed G S heven hclosed hu)
  have hf' : f ∈ S.erase u := Finset.mem_erase.mpr ⟨huf.symm, hf⟩
  have hc : ((S.erase u).erase f).card = 3 := by
    rw [Finset.card_erase_of_mem hf', Finset.card_erase_of_mem hu, hcard]
  simpa [hc] using Finset.card_le_card hsub

/-- A closed five-vertex set with a universal vertex has an actual fresh-leaf
three-star reduction. Internal edges between the other four vertices are
unrestricted. Every residual path partition lifts with its budget unchanged. -/
theorem restore_closed_five (G : SimpleGraph V) (S : Finset V)
    (heven : ∀ u ∈ S, Even (G.degree u))
    (hclosed : ∀ u ∈ S, ∀ v, (evenCore G).Adj u v → v ∈ S)
    (hcard : S.card = 5) {x f : V} (hx : x ∈ S) (hf : f ∈ S) (hfx : f ≠ x)
    (hhub : ∀ v ∈ S, v ≠ x → G.Adj x v) {q : ℕ}
    (hq : HasPathPartition (starDeleteEven (attachLeaf G f) (some x)) q) :
    HasPathPartition G q := by
  have hE := evenNeighbors_eq_closed_hub G S heven hclosed hx hhub
  have hk : evenNeighborCount G x = 4 := by
    unfold evenNeighborCount
    rw [hE, Finset.card_erase_of_mem hx, hcard]
  have hk' := attachLeaf_evenNeighborCount G (hhub f hf hfx) (heven f hf)
  have hthree : evenNeighborCount (attachLeaf G f) (some x) = 3 := by omega
  have hxEven : Even ((attachLeaf G f).degree (some x)) := by
    rw [attachLeaf_degree_some]
    simpa [hfx.symm] using heven x hx
  apply remove_attached_leaf_partition G f
  apply restore_terminal_three_star (attachLeaf G f) (some x) hthree hxEven _ hq
  intro a ha
  rw [attachLeaf_evenNeighbors_any G f x (heven f hf)] at ha
  obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨huf, huE⟩ := Finset.mem_erase.mp hu
  have huS := (Finset.mem_erase.mp
    (evenNeighbors_subset_closed G S heven hclosed hx huE)).2
  exact closed_five_leaf_neighbor_bound G S heven hclosed hcard hf huS huf

/-- Exact measure and potential costs for the five-vertex terminal reduction,
with a consumer requiring only the explicit residual graph's path bound. -/
theorem closed_five_reduction (G : SimpleGraph V) (S : Finset V)
    (heven : ∀ u ∈ S, Even (G.degree u))
    (hclosed : ∀ u ∈ S, ∀ v, (evenCore G).Adj u v → v ∈ S)
    (hcard : S.card = 5) {x f : V} (hx : x ∈ S) (hf : f ∈ S) (hfx : f ≠ x)
    (hhub : ∀ v ∈ S, v ≠ x → G.Adj x v) :
    let J := starDeleteEven (attachLeaf G f) (some x)
    edgeExcess J + 8 = edgeExcess G + 3 ∧
    edgeExcess J < edgeExcess G ∧
    phi G - phi J = 1 / 3 ∧
    (HasPathBound J (phi J) → HasPathBound G (phi G)) := by
  dsimp only
  have hE := evenNeighbors_eq_closed_hub G S heven hclosed hx hhub
  have hk : evenNeighborCount G x = 4 := by
    unfold evenNeighborCount
    rw [hE, Finset.card_erase_of_mem hx, hcard]
  have hxa := hhub f hf hfx
  have hmeasure := attachLeaf_star_edgeExcess G hxa (heven f hf)
  rw [hk] at hmeasure
  have hdrop := phi_attachLeaf_star G hxa (heven f hf) (heven x hx)
    (by rw [hk]; decide)
  rw [hk] at hdrop
  norm_num at hdrop hmeasure
  refine ⟨hmeasure, attachLeaf_star_edgeExcess_lt G hxa (heven f hf) (by omega),
    hdrop, ?_⟩
  intro hb
  obtain ⟨q, hq, hqb⟩ := hasPathBound_iff_exists_partition.mp hb
  exact hasPathBound_iff_exists_partition.mpr ⟨q,
    restore_closed_five G S heven hclosed hcard hx hf hfx hhub hq, by linarith⟩

/-- Bundled verification target for both concrete terminal reductions. The
only path-bound premises concern their explicitly constructed residuals. -/
theorem terminal_core_reductions (G : SimpleGraph V) (S : Finset V)
    (heven : ∀ u ∈ S, Even (G.degree u))
    (hclosed : ∀ u ∈ S, ∀ v, (evenCore G).Adj u v → v ∈ S) :
    (S.card = 4 →
      (∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v) →
      ∀ x ∈ S,
        edgeExcess (starDeleteEven G x) < edgeExcess G ∧
        phi (starDeleteEven G x) ≤ phi G ∧
        (HasPathBound (starDeleteEven G x) (phi (starDeleteEven G x)) →
          HasPathBound G (phi G))) ∧
    (S.card = 5 → ∀ x ∈ S, ∀ f ∈ S, f ≠ x →
      (∀ v ∈ S, v ≠ x → G.Adj x v) →
      let J := starDeleteEven (attachLeaf G f) (some x)
      edgeExcess J + 8 = edgeExcess G + 3 ∧
      edgeExcess J < edgeExcess G ∧
      phi G - phi J = 1 / 3 ∧
      (HasPathBound J (phi J) → HasPathBound G (phi G))) := by
  constructor
  · intro hc hcl x hx
    exact closed_four_reduction G S heven hclosed hc hcl hx
  · intro hc x hx f hf hfx hh
    exact closed_five_reduction G S heven hclosed hc hx hf hfx hh

end Erdos583
end
end Source41_Erdos583_TerminalCore
/- END Erdos583.TerminalCore -/

/- BEGIN Erdos583.DKStructure; source SHA256 5e0af380874cbabd9cc7588c073f3b6a2b2410e118680aac4834e40b6ad2df6d -/
section Source42_Erdos583_DKStructure



/-! A constructive terminal-component classification under the exact local
structural premises used in the Dean--Kouider baseline argument. Establishing
these premises from path reductions is separate and is not assumed proved. -/

noncomputable section
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

def commonNeighborFinset (G : SimpleGraph V) (x y : V) : Finset V :=
  G.neighborFinset x ∩ G.neighborFinset y

@[simp] theorem mem_commonNeighborFinset (G : SimpleGraph V) (x y z : V) :
    z ∈ commonNeighborFinset G x y ↔ G.Adj x z ∧ G.Adj y z := by
  simp [commonNeighborFinset]

/-- Structural hypotheses only. No path bound or restoration appears here. -/
structure DKTerminal (G : SimpleGraph V) : Prop where
  degree : ∀ x, G.degree x ≠ 0 → G.degree x = 3 ∨ G.degree x = 4
  common_pos : ∀ x y, G.Adj x y → 1 ≤ (commonNeighborFinset G x y).card
  common_one : ∀ x y, G.Adj x y → (commonNeighborFinset G x y).card = 1 →
    G.degree x = 3 ∧ G.degree y = 3
  common_two : ∀ x y, G.Adj x y → (commonNeighborFinset G x y).card = 2 →
    ¬(G.degree x = 4 ∧ G.degree y = 4)

theorem commonNeighborFinset_subset_erase (G : SimpleGraph V) (x y : V) :
    commonNeighborFinset G x y ⊆ (G.neighborFinset y).erase x := by
  intro z hz
  obtain ⟨hxz, hyz⟩ := (mem_commonNeighborFinset G x y z).mp hz
  exact Finset.mem_erase.mpr ⟨hxz.ne.symm, (G.mem_neighborFinset y z).mpr hyz⟩

theorem commonNeighborFinset_card_lt_degree (G : SimpleGraph V) {x y : V}
    (hxy : G.Adj x y) : (commonNeighborFinset G x y).card < G.degree y := by
  have hc := Finset.card_le_card (commonNeighborFinset_subset_erase G x y)
  rw [Finset.card_erase_of_mem ((G.mem_neighborFinset y x).mpr hxy.symm),
    card_neighborFinset_eq_degree] at hc
  have hp := hxy.degree_pos_right
  omega

theorem DKTerminal.exists_common_neighbor {G : SimpleGraph V} (hG : DKTerminal G)
    {x y : V} (hxy : G.Adj x y) : ∃ z, G.Adj x z ∧ G.Adj y z := by
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (hG.common_pos x y hxy)
  exact ⟨z, (mem_commonNeighborFinset G x y z).mp hz⟩

/-- A degree-four vertex forces every neighbor's remaining neighbors to lie
inside its own four-neighbor set. -/
theorem DKTerminal.degree_four_common_eq {G : SimpleGraph V} (hG : DKTerminal G)
    {x y : V} (hx : G.degree x = 4) (hxy : G.Adj x y) :
    commonNeighborFinset G x y = (G.neighborFinset y).erase x := by
  apply Finset.eq_of_subset_of_card_le (commonNeighborFinset_subset_erase G x y)
  rw [Finset.card_erase_of_mem ((G.mem_neighborFinset y x).mpr hxy.symm),
    card_neighborFinset_eq_degree]
  have hp := hG.common_pos x y hxy
  have hu := commonNeighborFinset_card_lt_degree G hxy
  have h1 : (commonNeighborFinset G x y).card ≠ 1 := by
    intro h
    have := (hG.common_one x y hxy h).1
    omega
  rcases hG.degree y (Nat.ne_of_gt hxy.degree_pos_right) with hy | hy
  · omega
  · have h2 : (commonNeighborFinset G x y).card ≠ 2 := by
      intro h
      exact hG.common_two x y hxy h ⟨hx, hy⟩
    omega

theorem DKTerminal.degree_four_closed {G : SimpleGraph V} (hG : DKTerminal G)
    {x : V} (hx : G.degree x = 4) :
    ∀ y ∈ closedNeighborhood G x, ∀ z, G.Adj y z → z ∈ closedNeighborhood G x := by
  intro y hy z hyz
  rcases (mem_closedNeighborhood G x y).mp hy with rfl | hxy
  · exact (mem_closedNeighborhood G _ z).mpr (Or.inr hyz)
  · by_cases hzx : z = x
    · exact (mem_closedNeighborhood G x z).mpr (Or.inl hzx)
    · have hz : z ∈ (G.neighborFinset y).erase x :=
        Finset.mem_erase.mpr ⟨hzx, (G.mem_neighborFinset y z).mpr hyz⟩
      rw [← hG.degree_four_common_eq hx hxy] at hz
      exact (mem_closedNeighborhood G x z).mpr
        (Or.inr ((mem_commonNeighborFinset G x y z).mp hz).1)

theorem DKTerminal.degree_four_closed_five {G : SimpleGraph V} (hG : DKTerminal G)
    {x : V} (hx : G.degree x = 4) :
    (closedNeighborhood G x).card = 5 ∧
    (∀ y ∈ closedNeighborhood G x, ∀ z, G.Adj y z → z ∈ closedNeighborhood G x) ∧
    (∀ y ∈ closedNeighborhood G x, 3 ≤ G.degree y) ∧
    (∀ y ∈ closedNeighborhood G x, y ≠ x → G.Adj x y) := by
  refine ⟨?_, hG.degree_four_closed hx, ?_, ?_⟩
  · simp [closedNeighborhood, card_neighborFinset_eq_degree, hx]
  · intro y hy
    rcases (mem_closedNeighborhood G x y).mp hy with rfl | hxy
    · omega
    · rcases hG.degree y (Nat.ne_of_gt hxy.degree_pos_right) with hd | hd <;> omega
  · intro y hy hne
    exact ((mem_closedNeighborhood G x y).mp hy).resolve_left hne


theorem neighborFinset_eq_triple_of_degree_three (G : SimpleGraph V)
    {x a b c : V} (hxa : G.Adj x a) (hxb : G.Adj x b) (hxc : G.Adj x c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hx : G.degree x = 3) :
    G.neighborFinset x = {a,b,c} := by
  have hs : ({a,b,c} : Finset V) ⊆ G.neighborFinset x := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> simpa
  apply (Finset.eq_of_subset_of_card_le hs ?_).symm
  simp [card_neighborFinset_eq_degree, hx, hab, hac, hbc]

theorem exists_neighbor_outside_pair (G : SimpleGraph V) {a x c : V}
    (ha : G.degree a = 3) : ∃ d, G.Adj a d ∧ d ≠ x ∧ d ≠ c := by
  have hn : ¬G.neighborFinset a ⊆ {x,c} := by
    intro hs
    have hb := Finset.card_le_card hs
    have hc := Finset.card_insert_le x ({c} : Finset V)
    rw [card_neighborFinset_eq_degree, ha] at hb
    simp only [Finset.card_singleton] at hc
    omega
  obtain ⟨d, hd, hout⟩ := Finset.not_subset.mp hn
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hout
  exact ⟨d, (G.mem_neighborFinset a d).mp hd, hout⟩

/-- A missing edge inside a cubic vertex's neighborhood would force an edge
with no common neighbor. No enumeration of three-vertex graphs is used. -/
theorem DKTerminal.cubic_neighbor_edge {G : SimpleGraph V} (hG : DKTerminal G)
    {x a b c : V} (hNx : G.neighborFinset x = {a,b,c})
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : G.degree a = 3) (hc : G.degree c = 3) : G.Adj a b := by
  have hxa : G.Adj x a := by rw [← G.mem_neighborFinset, hNx]; simp
  have hxb : G.Adj x b := by rw [← G.mem_neighborFinset, hNx]; simp
  have hxc : G.Adj x c := by rw [← G.mem_neighborFinset, hNx]; simp
  have hNx' (v : V) : G.Adj x v ↔ v = a ∨ v = b ∨ v = c := by
    rw [← G.mem_neighborFinset, hNx]; simp
  by_contra hnab
  have hacA : G.Adj a c := by
    obtain ⟨z, hxz, haz⟩ := hG.exists_common_neighbor hxa
    rcases (hNx' z).mp hxz with rfl | rfl | rfl
    · exact (haz.ne rfl).elim
    · exact (hnab haz).elim
    · exact haz
  have hbcA : G.Adj b c := by
    obtain ⟨z, hxz, hbz⟩ := hG.exists_common_neighbor hxb
    rcases (hNx' z).mp hxz with rfl | rfl | rfl
    · exact (hnab hbz.symm).elim
    · exact (hbz.ne rfl).elim
    · exact hbz
  have hNc : G.neighborFinset c = {x,a,b} :=
    neighborFinset_eq_triple_of_degree_three G hxc.symm hacA.symm hbcA.symm
      hxa.ne hxb.ne hab hc
  obtain ⟨d, had, hdx, hdc⟩ := exists_neighbor_outside_pair (x := x) (c := c) G ha
  have hda : d ≠ a := had.ne.symm
  have hdb : d ≠ b := by intro h; subst d; exact hnab had
  have hxnd : ¬G.Adj x d := by
    rw [hNx']; tauto
  have hcnd : ¬G.Adj c d := by
    rw [← G.mem_neighborFinset, hNc]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hNa : G.neighborFinset a = {x,c,d} :=
    neighborFinset_eq_triple_of_degree_three G hxa.symm hacA had hxc.ne hdx.symm hdc.symm ha
  obtain ⟨w, haw, hdw⟩ := hG.exists_common_neighbor had
  have hw : w = x ∨ w = c ∨ w = d := by
    have hm := (G.mem_neighborFinset a w).mpr haw
    rw [hNa] at hm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  rcases hw with rfl | rfl | rfl
  · exact hxnd hdw.symm
  · exact hcnd hdw.symm
  · exact hdw.ne rfl


/-- Saturated degrees make a four-vertex clique closed in the ambient graph. -/
theorem closed_four_clique_of_degrees (G : SimpleGraph V) (S : Finset V)
    (hc : S.card = 4)
    (hclique : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v)
    (hdeg : ∀ u ∈ S, G.degree u = 3) :
    ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S := by
  intro u hu v huv
  have hs : S.erase u ⊆ G.neighborFinset u := by
    intro w hw
    obtain ⟨hwu, hwS⟩ := Finset.mem_erase.mp hw
    exact (G.mem_neighborFinset u w).mpr (hclique u hu w hwS hwu.symm)
  have heq : S.erase u = G.neighborFinset u := by
    apply Finset.eq_of_subset_of_card_le hs
    rw [Finset.card_erase_of_mem hu, hc, card_neighborFinset_eq_degree, hdeg u hu]
  exact Finset.mem_of_mem_erase (heq.symm ▸ (G.mem_neighborFinset u v).mpr huv)

/-- If a cubic vertex has only cubic neighbors, its closed neighborhood is a
closed four-vertex clique. -/
theorem DKTerminal.cubic_closed_four {G : SimpleGraph V} (hG : DKTerminal G)
    {x : V} (hx : G.degree x = 3)
    (hneigh : ∀ y, G.Adj x y → G.degree y = 3) :
    (closedNeighborhood G x).card = 4 ∧
    (∀ u ∈ closedNeighborhood G x, ∀ v ∈ closedNeighborhood G x,
      u ≠ v → G.Adj u v) ∧
    (∀ u ∈ closedNeighborhood G x, ∀ v, G.Adj u v → v ∈ closedNeighborhood G x) := by
  have hncard : (G.neighborFinset x).card = 3 := by rw [card_neighborFinset_eq_degree, hx]
  obtain ⟨a,b,c,hab,hac,hbc,hNx⟩ := Finset.card_eq_three.mp hncard
  have hxa : G.Adj x a := by rw [← G.mem_neighborFinset, hNx]; simp
  have hxb : G.Adj x b := by rw [← G.mem_neighborFinset, hNx]; simp
  have hxc : G.Adj x c := by rw [← G.mem_neighborFinset, hNx]; simp
  have ha := hneigh a hxa
  have hb := hneigh b hxb
  have hc := hneigh c hxc
  have habA := hG.cubic_neighbor_edge hNx hab hac hbc ha hc
  have hacA : G.Adj a c := by
    have hn : G.neighborFinset x = {a,c,b} := by rw [hNx]; ext v; simp; tauto
    exact hG.cubic_neighbor_edge hn hac hab hbc.symm ha hb
  have hbcA : G.Adj b c := by
    have hn : G.neighborFinset x = {b,c,a} := by rw [hNx]; ext v; simp; tauto
    exact hG.cubic_neighbor_edge hn hbc hab.symm hac.symm hb ha
  have hcard : (closedNeighborhood G x).card = 4 := by
    simp [closedNeighborhood, card_neighborFinset_eq_degree, hx]
  have hclique : ∀ u ∈ closedNeighborhood G x, ∀ v ∈ closedNeighborhood G x,
      u ≠ v → G.Adj u v := by
    intro u hu v hv hne
    have hax := hxa.symm
    have hbx := hxb.symm
    have hcx := hxc.symm
    have hba := habA.symm
    have hca := hacA.symm
    have hcb := hbcA.symm
    simp only [closedNeighborhood, hNx, Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl | rfl <;>
      rcases hv with rfl | rfl | rfl | rfl <;> first | assumption | exact (hne rfl).elim
  have hdeg : ∀ u ∈ closedNeighborhood G x, G.degree u = 3 := by
    intro u hu
    rcases (mem_closedNeighborhood G x u).mp hu with rfl | hxu
    · exact hx
    · exact hneigh u hxu
  exact ⟨hcard, hclique, closed_four_clique_of_degrees G _ hcard hclique hdeg⟩

/-- Every nonisolated vertex belongs to an explicit closed set which is
K4, or has five vertices and a universal degree-four vertex. The latter
alternative has ordinary minimum degree at least three. -/
theorem DKTerminal.closed_component_dichotomy {G : SimpleGraph V} (hG : DKTerminal G)
    {v : V} (hv : G.degree v ≠ 0) :
    ∃ S : Finset V, v ∈ S ∧
      (∀ u ∈ S, ∀ w, G.Adj u w → w ∈ S) ∧
      ((S.card = 4 ∧ ∀ u ∈ S, ∀ w ∈ S, u ≠ w → G.Adj u w) ∨
       (S.card = 5 ∧ ∃ x ∈ S, G.degree x = 4 ∧
         (∀ u ∈ S, u ≠ x → G.Adj x u) ∧ (∀ u ∈ S, 3 ≤ G.degree u))) := by
  by_cases hfour : ∃ x ∈ closedNeighborhood G v, G.degree x = 4
  · obtain ⟨x, hxv, hx⟩ := hfour
    obtain ⟨hc, hclosed, hdeg, hhub⟩ := hG.degree_four_closed_five hx
    have hvx : v ∈ closedNeighborhood G x := by
      rcases (mem_closedNeighborhood G v x).mp hxv with h | h
      · subst x; simp
      · exact (mem_closedNeighborhood G x v).mpr (Or.inr h.symm)
    exact ⟨closedNeighborhood G x, hvx, hclosed,
      Or.inr ⟨hc, x, by simp, hx, hhub, hdeg⟩⟩
  · have hnot : ∀ x ∈ closedNeighborhood G v, G.degree x ≠ 4 := by simpa using hfour
    have hv3 : G.degree v = 3 := (hG.degree v hv).resolve_right (hnot v (by simp))
    have hneigh : ∀ x, G.Adj v x → G.degree x = 3 := by
      intro x hvx
      exact (hG.degree x (Nat.ne_of_gt hvx.degree_pos_right)).resolve_right
        (hnot x ((mem_closedNeighborhood G v x).mpr (Or.inr hvx)))
    obtain ⟨hc, hclique, hclosed⟩ := hG.cubic_closed_four hv3 hneigh
    exact ⟨closedNeighborhood G v, by simp, hclosed, Or.inl ⟨hc, hclique⟩⟩


omit [Fintype V] in
theorem mem_of_reachable_of_closed (G : SimpleGraph V) (S : Finset V)
    (hclosed : ∀ u ∈ S, ∀ w, G.Adj u w → w ∈ S)
    {v w : V} (hv : v ∈ S) (h : G.Reachable v w) : w ∈ S := by
  obtain ⟨p⟩ := h
  revert hv
  induction p with
  | nil => exact id
  | @cons a b c hab p ih =>
    intro ha
    exact ih (hclosed a ha b hab)

/-- Exact component support as well as the constructive finite description.
Isolated vertices are deliberately excluded; no global connectedness is used. -/
theorem DKTerminal.component_certificate {G : SimpleGraph V} (hG : DKTerminal G)
    {v : V} (hv : G.degree v ≠ 0) :
    ∃ S : Finset V, v ∈ S ∧
      (∀ w, w ∈ S ↔ G.Reachable v w) ∧
      (∀ u ∈ S, ∀ w, G.Adj u w → w ∈ S) ∧
      ((S.card = 4 ∧ ∀ u ∈ S, ∀ w ∈ S, u ≠ w → G.Adj u w) ∨
       (S.card = 5 ∧ ∃ x ∈ S, G.degree x = 4 ∧
         (∀ u ∈ S, u ≠ x → G.Adj x u) ∧ (∀ u ∈ S, 3 ≤ G.degree u))) := by
  obtain ⟨S, hvS, hc, hform⟩ := hG.closed_component_dichotomy hv
  refine ⟨S, hvS, ?_, hc, hform⟩
  intro w
  refine ⟨?_, mem_of_reachable_of_closed G S hc hvS⟩
  intro hw
  rcases hform with ⟨_, hclique⟩ | ⟨_, x, hx, _, hhub, _⟩
  · by_cases hvw : v = w
    · subst w; exact Reachable.rfl
    · exact (hclique v hvS w hw hvw).reachable
  · have ht : ∀ u ∈ S, G.Reachable u x := by
      intro u hu
      by_cases hux : u = x
      · subst u; exact Reachable.rfl
      · exact (hhub u hu hux).symm.reachable
    exact (ht v hvS).trans (ht w hw).symm

end Erdos583
end
end Source42_Erdos583_DKStructure
/- END Erdos583.DKStructure -/

/- BEGIN Erdos583.BaselineTerminal; source SHA256 981badfb728e1a1dbe2e021557154289a321563049ab99879f56dcdd496c8010 -/
section Source43_Erdos583_BaselineTerminal




/-! Closing the terminal case in the actual smaller-graph induction. -/
noncomputable section
universe u
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type u} [Fintype V]

theorem minimal_phi_not_terminal (G : SimpleGraph V)
    (ih : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W),
      edgeExcess H < edgeExcess G → HasPathBound H (phi H))
    (hbad : ¬ HasPathBound G (phi G)) (hT : DKTerminal (evenCore G)) : False := by
  classical
  have hforest : ¬ (evenCore G).IsAcyclic :=
    fun h => hbad (hasPathBound_phi_even_forest G h)
  have hnoniso : ∃ v, (evenCore G).degree v ≠ 0 := by
    by_contra hn
    have hbot : evenCore G = ⊥ := by
      ext v w
      constructor
      · intro h
        exact False.elim (hn ⟨v,Nat.ne_of_gt h.degree_pos_left⟩)
      · intro h; exact False.elim h
    exact hforest (by rw [hbot]; exact isAcyclic_bot)
  obtain ⟨v,hv⟩ := hnoniso
  obtain ⟨S,hvS,hreach,hclosed,hform⟩ := hT.component_certificate hv
  have hEvenS : ∀ w ∈ S, Even (G.degree w) := by
    intro w hw
    have hnw : (evenCore G).degree w ≠ 0 := by
      by_cases hwv : w = v
      · subst w
        exact hv
      · exact Nat.ne_of_gt (((evenCore G).degree_pos_iff_mem_support w).mpr
          (mem_support_of_reachable hwv ((hreach w).mp hw).symm))
    exact ((mem_nonisolatedEvenVertices G w).mp
      (evenCore_nonisolated_original G w hnw)).1
  rcases hform with ⟨hfour,hclique⟩ | ⟨hfive,x,hx,_,hhub,_⟩
  · have hred := closed_four_reduction G S hEvenS hclosed hfour
      (fun a ha b hb hne => (hclique a ha b hb hne).1) hvS
    have hJ := ih V (starDeleteEven G v) hred.1
    exact hbad (hred.2.2 hJ)
  · have hne : (S.erase x).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem hx,hfive]
      decide
    obtain ⟨f,hf⟩ := hne
    obtain ⟨hfx,hfS⟩ := Finset.mem_erase.mp hf
    have hred := closed_five_reduction G S hEvenS hclosed hfive hx hfS hfx
      (fun a ha hax => (hhub a ha hax).1)
    have hJ := ih (Option V) (starDeleteEven (attachLeaf G f) (some x)) hred.2.1
    exact hbad (hred.2.2.2 hJ)

end Erdos583
end
end Source43_Erdos583_BaselineTerminal
/- END Erdos583.BaselineTerminal -/

/- BEGIN Erdos583.DKTwoStar; source SHA256 8019389576e5409816b284bdcbc7f56a264c9a3e7e6ae9dab6d0627728b4ac51 -/
section Source44_Erdos583_DKTwoStar




/-! Actual deletion graphs for the two-star Dean--Kouider reductions. -/

noncomputable section
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

def dkEdgeDelete (G : SimpleGraph V) (x y : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ ¬(a = x ∧ b = y) ∧ ¬(a = y ∧ b = x)
  symm := ⟨by intro a b h; exact ⟨h.1.symm, by tauto, by tauto⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

omit [Fintype V] in
@[simp] theorem dkEdgeDelete_adj (G : SimpleGraph V) (x y a b : V) :
    (dkEdgeDelete G x y).Adj a b ↔ G.Adj a b ∧ ¬(a = x ∧ b = y) ∧ ¬(a = y ∧ b = x) := Iff.rfl

abbrev dkFirstStar (G : SimpleGraph V) (x y : V) : SimpleGraph V :=
  starDeleteEven (dkEdgeDelete G x y) x
abbrev dkTwoStarResidual (G : SimpleGraph V) (x y : V) : SimpleGraph V :=
  starDeleteEven (dkFirstStar G x y) y

theorem dkEdgeDelete_degree_left (G : SimpleGraph V) {x y : V} (hxy : G.Adj x y) :
    (dkEdgeDelete G x y).degree x = G.degree x - 1 := by
  have he : (dkEdgeDelete G x y).neighborFinset x = (G.neighborFinset x).erase y := by
    ext v
    simp only [mem_neighborFinset, Finset.mem_erase, dkEdgeDelete_adj]
    simp [hxy.ne, eq_comm, and_comm]
  rw [← card_neighborFinset_eq_degree, he,
    Finset.card_erase_of_mem ((G.mem_neighborFinset x y).mpr hxy), card_neighborFinset_eq_degree]

theorem dkEdgeDelete_degree_right (G : SimpleGraph V) {x y : V} (hxy : G.Adj x y) :
    (dkEdgeDelete G x y).degree y = G.degree y - 1 := by
  have he : (dkEdgeDelete G x y).neighborFinset y = (G.neighborFinset y).erase x := by
    ext v
    simp only [mem_neighborFinset, Finset.mem_erase, dkEdgeDelete_adj]
    simp [hxy.ne.symm, eq_comm, and_comm]
  rw [← card_neighborFinset_eq_degree, he,
    Finset.card_erase_of_mem ((G.mem_neighborFinset y x).mpr hxy.symm), card_neighborFinset_eq_degree]

theorem dkEdgeDelete_degree_other (G : SimpleGraph V) {x y v : V}
    (hvx : v ≠ x) (hvy : v ≠ y) : (dkEdgeDelete G x y).degree v = G.degree v := by
  have he : (dkEdgeDelete G x y).neighborFinset v = G.neighborFinset v := by
    ext w
    simp only [mem_neighborFinset, dkEdgeDelete_adj]
    simp [hvx,hvy]
  exact congrArg Finset.card he

theorem dkEdgeDelete_center_odd (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) :
    Odd ((dkEdgeDelete G x y).degree x) ∧ Odd ((dkEdgeDelete G x y).degree y) := by
  have hx := selected_degree_ge_two G y x ((mem_evenNeighbors G y x).mpr ⟨hxy.1.symm,hxy.2.1⟩)
  have hy := selected_degree_ge_two G x y ((mem_evenNeighbors G x y).mpr ⟨hxy.1,hxy.2.2⟩)
  rw [dkEdgeDelete_degree_left G hxy.1, dkEdgeDelete_degree_right G hxy.1]
  exact ⟨Nat.Even.sub_odd (by omega) hxy.2.1 (by decide), Nat.Even.sub_odd (by omega) hxy.2.2 (by decide)⟩

theorem dkEdgeDelete_neighbors_left (G : SimpleGraph V) {x y : V}
    (_hxy : (evenCore G).Adj x y) :
    evenNeighbors (dkEdgeDelete G x y) x = (evenNeighbors G x).erase y := by
  ext v
  by_cases hvx : v = x
  · subst v
    simp [mem_evenNeighbors, dkEdgeDelete, Finset.mem_erase]
  by_cases hvy : v = y
  · subst v
    simp [mem_evenNeighbors, dkEdgeDelete, Finset.mem_erase]
  simp only [mem_evenNeighbors, Finset.mem_erase, dkEdgeDelete_degree_other G hvx hvy]
  simp [dkEdgeDelete, hvx, hvy]

theorem dkEdgeDelete_count_left (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) :
    evenNeighborCount (dkEdgeDelete G x y) x + 1 = (evenCore G).degree x := by
  rw [evenCore_degree_of_even G x hxy.2.1]
  unfold evenNeighborCount
  rw [dkEdgeDelete_neighbors_left G hxy]
  exact Finset.card_erase_add_one ((mem_evenNeighbors G x y).mpr ⟨hxy.1,hxy.2.2⟩)

theorem dkFirstStar_degree_right (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) :
    (dkFirstStar G x y).degree y = G.degree y - 1 := by
  rw [dkFirstStar, degree_starDeleteEven_other _ _ _ hxy.1.ne.symm]
  · exact dkEdgeDelete_degree_right G hxy.1
  · simp [mem_evenNeighbors, dkEdgeDelete]

theorem dkFirstStar_neighbors_right (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) :
    evenNeighbors (dkFirstStar G x y) y =
      (evenNeighbors G y).erase x \ evenNeighbors G x := by
  ext v
  by_cases hvx : v = x
  · subst v
    simp [mem_evenNeighbors, dkFirstStar, starDeleteEven_adj, dkEdgeDelete]
  by_cases hvy : v = y
  · subst v
    simp [mem_evenNeighbors, dkFirstStar]
  have hmem : v ∈ evenNeighbors (dkEdgeDelete G x y) x ↔ v ∈ evenNeighbors G x := by
    rw [dkEdgeDelete_neighbors_left G hxy]
    simp [hvy]
  by_cases hvA : v ∈ evenNeighbors G x
  · have ho := selected_becomes_odd (dkEdgeDelete G x y) x v (hmem.mpr hvA)
    simp only [mem_evenNeighbors, Finset.mem_sdiff, Finset.mem_erase] at *
    have hn := Nat.not_even_iff_odd.mpr ho
    change (_ ∧ Even ((starDeleteEven (dkEdgeDelete G x y) x).degree v)) ↔ _
    tauto
  · have hd : (dkFirstStar G x y).degree v = G.degree v := by
      rw [dkFirstStar, degree_starDeleteEven_other _ _ _ hvx (by simpa [hmem] using hvA),
        dkEdgeDelete_degree_other G hvx hvy]
    simp only [mem_evenNeighbors, Finset.mem_sdiff, Finset.mem_erase, hd]
    have ha : (dkFirstStar G x y).Adj y v ↔ G.Adj y v := by
      simp [dkFirstStar, starDeleteEven_adj, dkEdgeDelete,
        hvx, hvy, hxy.1.ne.symm]
    rw [ha]
    have hn : ¬ (G.Adj x v ∧ Even (G.degree v)) := by
      simpa only [mem_evenNeighbors] using hvA
    tauto

theorem dkFirstStar_count_right (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) :
    evenNeighborCount (dkFirstStar G x y) y +
      (originalEvenCommonNeighbors G x y).card + 1 = (evenCore G).degree y := by
  rw [evenCore_degree_of_even G y hxy.2.2]
  have hx : x ∈ evenNeighbors G y := (mem_evenNeighbors G y x).mpr ⟨hxy.1.symm,hxy.2.1⟩
  have hi : (evenNeighbors G y).erase x ∩ evenNeighbors G x =
      originalEvenCommonNeighbors G x y := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_erase, originalEvenCommonNeighbors]
    constructor
    · tauto
    · rintro ⟨h1,h2⟩
      exact ⟨⟨fun he => (mem_evenNeighbors G x v).mp h1 |>.1.ne he.symm, h2⟩,h1⟩
  have hc := Finset.card_sdiff_add_card_inter ((evenNeighbors G y).erase x) (evenNeighbors G x)
  rw [hi] at hc
  have he := Finset.card_erase_add_one hx
  unfold evenNeighborCount
  rw [dkFirstStar_neighbors_right G hxy]
  omega

theorem dkEdgeDelete_phi (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) : phi G - phi (dkEdgeDelete G x y) = 1 / 3 := by
  have ho := dkEdgeDelete_center_odd G hxy
  have hpoint (v : V) : parityWeight (G.degree v) - parityWeight ((dkEdgeDelete G x y).degree v) =
      (if v = x then (1/6 : ℚ) else 0) + (if v = y then (1/6 : ℚ) else 0) := by
    by_cases hvx : v = x
    · subst v
      rw [parityWeight_even_nonzero hxy.2.1 (ne_of_gt ((G.degree_pos_iff_exists_adj x).mpr ⟨y,hxy.1⟩))]
      norm_num [parityWeight, ho.1, Nat.not_even_iff_odd.mpr ho.1, hxy.1.ne]
    by_cases hvy : v = y
    · subst v
      rw [parityWeight_even_nonzero hxy.2.2 (ne_of_gt ((G.degree_pos_iff_exists_adj y).mpr ⟨x,hxy.1.symm⟩))]
      norm_num [parityWeight, ho.2, Nat.not_even_iff_odd.mpr ho.2, hxy.1.ne.symm]
    rw [dkEdgeDelete_degree_other G hvx hvy]
    simp [hvx,hvy]
  rw [phi_eq_sum_parityWeight, phi_eq_sum_parityWeight, ← Finset.sum_sub_distrib]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  norm_num

/-- Each of these two- or three-edge deletions at an odd center gains at least
one third of the actual parity potential and creates exactly two new odd vertices. -/
theorem short_odd_star_accounting (H : SimpleGraph V) (x : V)
    (ho : Odd (H.degree x))
    (hk : evenNeighborCount H x = 2 ∨ evenNeighborCount H x = 3) :
    (1/3 : ℚ) ≤ phi H - phi (starDeleteEven H x) ∧
    (oddVertices (starDeleteEven H x)).card = (oddVertices H).card + 2 := by
  have hle := evenNeighborCount_le_degree H x
  have hp := phi_starDeleteEven_exact H x
  have hc := odd_count_starDeleteEven H x
  have hw : parityWeight (H.degree x) = 1/2 := by
    norm_num [parityWeight, ho, Nat.not_even_iff_odd.mpr ho]
  rw [hw] at hp
  rcases hk with hk | hk
  · have hr : Odd ((starDeleteEven H x).degree x) := by
      rw [degree_starDeleteEven_center, hk]
      exact Nat.Odd.sub_even (by omega) ho (by decide)
    have hwr : parityWeight ((starDeleteEven H x).degree x) = 1/2 := by
      norm_num [parityWeight, hr, Nat.not_even_iff_odd.mpr hr]
    rw [hk, hwr] at hp
    simp only [if_pos ho, if_pos hr, hk] at hc
    constructor <;> norm_num at hp <;> linarith
  · have hr : Even ((starDeleteEven H x).degree x) := by
      rw [degree_starDeleteEven_center, hk]
      exact Nat.Odd.sub_odd ho (by decide)
    have hn := Nat.not_odd_iff_even.mpr hr
    have hwr := parityWeight_le_two_thirds ((starDeleteEven H x).degree x)
    rw [hk] at hp
    simp only [if_pos ho, if_neg hn, hk] at hc
    constructor <;> norm_num at hp <;> linarith

theorem dkEdgeDelete_edge_count (G : SimpleGraph V) {x y : V} (hxy : G.Adj x y) :
    (dkEdgeDelete G x y).edgeFinset.card + 1 = G.edgeFinset.card := by
  have he : (dkEdgeDelete G x y).edgeFinset = G.edgeFinset.erase s(x,y) := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Finset.mem_erase, mem_edgeFinset, mem_edgeSet, dkEdgeDelete_adj, ne_eq, Sym2.eq_iff]
      tauto
  rw [he]
  exact Finset.card_erase_add_one ((G.mem_edgeFinset).mpr hxy)

theorem dkEdgeDelete_active (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) :
    activeVertices (dkEdgeDelete G x y) = activeVertices G := by
  have ho := dkEdgeDelete_center_odd G hxy
  ext v
  simp only [mem_activeVertices]
  by_cases hx : v = x
  · subst v
    have h1 : (dkEdgeDelete G x y).degree x ≠ 0 := by obtain ⟨k,hk⟩ := ho.1; omega
    have h2 := hxy.1.degree_pos_left.ne'
    exact iff_of_true h1 h2
  by_cases hy : v = y
  · subst v
    have h1 : (dkEdgeDelete G x y).degree y ≠ 0 := by obtain ⟨k,hk⟩ := ho.2; omega
    have h2 := hxy.1.degree_pos_right.ne'
    exact iff_of_true h1 h2
  rw [dkEdgeDelete_degree_other G hx hy]

theorem dkEdgeDelete_excess (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) :
    edgeExcess (dkEdgeDelete G x y) + 2 = edgeExcess G := by
  have he := dkEdgeDelete_edge_count G hxy.1
  have ha := congrArg Finset.card (dkEdgeDelete_active G hxy)
  have hb := activeVertices_card_le_twice_edges (dkEdgeDelete G x y)
  unfold edgeExcess
  omega

theorem dkEdgeDelete_odd_count (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) :
    (oddVertices (dkEdgeDelete G x y)).card = (oddVertices G).card + 2 := by
  have ho := dkEdgeDelete_center_odd G hxy
  have hs : oddVertices (dkEdgeDelete G x y) = insert x (insert y (oddVertices G)) := by
    ext v
    by_cases hx : v = x
    · subst v
      simp [ho.1]
    by_cases hy : v = y
    · subst v
      simp [ho.2]
    simp only [mem_oddVertices, Finset.mem_insert, dkEdgeDelete_degree_other G hx hy]
    tauto
  simp [hs, hxy.1.ne, Nat.not_odd_iff_even.mpr hxy.2.1, Nat.not_odd_iff_even.mpr hxy.2.2, Nat.add_assoc]

def DKFirstConfiguration (G : SimpleGraph V) (x y : V) : Prop :=
  ((evenCore G).degree x = 3 ∨ (evenCore G).degree x = 4) ∧
  ((evenCore G).degree y = 3 ∨ (evenCore G).degree y = 4) ∧
  ((originalEvenCommonNeighbors G x y).card = 0 ∨
    ((originalEvenCommonNeighbors G x y).card = 1 ∧ (evenCore G).degree y = 4))

theorem dkFirstConfiguration_star_sizes (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) (hc : DKFirstConfiguration G x y) :
    (evenNeighborCount (dkEdgeDelete G x y) x = 2 ∨
      evenNeighborCount (dkEdgeDelete G x y) x = 3) ∧
    (evenNeighborCount (dkFirstStar G x y) y = 2 ∨
      evenNeighborCount (dkFirstStar G x y) y = 3) := by
  have ha := dkEdgeDelete_count_left G hxy
  have hb := dkFirstStar_count_right G hxy
  obtain ⟨hx,hy,ht⟩ := hc
  omega

theorem dkFirstConfiguration_accounting (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) (hc : DKFirstConfiguration G x y) :
    (1 : ℚ) ≤ phi G - phi (dkTwoStarResidual G x y) ∧
    (oddVertices (dkTwoStarResidual G x y)).card = (oddVertices G).card + 6 ∧
    (nonisolatedEvenVertices (dkTwoStarResidual G x y)).card + 6 ≤
      (nonisolatedEvenVertices G).card ∧
    edgeExcess (dkTwoStarResidual G x y) < edgeExcess G := by
  have hk := dkFirstConfiguration_star_sizes G hxy hc
  have ho := dkEdgeDelete_center_odd G hxy
  have hoy : Odd ((dkFirstStar G x y).degree y) := by
    rw [dkFirstStar_degree_right G hxy]
    simpa only [dkEdgeDelete_degree_right G hxy.1] using ho.2
  have h1 := short_odd_star_accounting (dkEdgeDelete G x y) x ho.1 hk.1
  have h2 := short_odd_star_accounting (dkFirstStar G x y) y hoy hk.2
  have h0 := dkEdgeDelete_phi G hxy
  have hu0 := dkEdgeDelete_odd_count G hxy
  have hu : (oddVertices (dkTwoStarResidual G x y)).card = (oddVertices G).card + 6 := by
    change (oddVertices (starDeleteEven (dkFirstStar G x y) y)).card = _
    rw [h2.2]
    change (oddVertices (starDeleteEven (dkEdgeDelete G x y) x)).card + 2 = _
    rw [h1.2,hu0]
  have hi : (isolatedVertices G).card ≤ (isolatedVertices (dkTwoStarResidual G x y)).card := by
    apply Finset.card_le_card
    intro v hv
    apply (mem_isolatedVertices _ _).mpr
    apply (SimpleGraph.degree_eq_zero _ _).mpr
    intro w hw
    exact (G.degree_eq_zero v).mp ((mem_isolatedVertices G v).mp hv) w hw.1.1.1
  have hpG := vertex_parity_count G
  have hpJ := vertex_parity_count (dkTwoStarResidual G x y)
  have he0 := dkEdgeDelete_excess G hxy
  have he1 := edgeExcess_starDeleteEven_lt (dkEdgeDelete G x y) x (by rcases hk.1 with h|h <;> omega)
  have he2 := edgeExcess_starDeleteEven_lt (dkFirstStar G x y) y (by rcases hk.2 with h|h <;> omega)
  refine ⟨?_,hu,by omega,?_⟩
  · change (1 : ℚ) ≤ phi G - phi (starDeleteEven (dkFirstStar G x y) y)
    have h1p : (1/3 : ℚ) ≤ phi (dkEdgeDelete G x y) - phi (dkFirstStar G x y) := h1.1
    linarith [h2.1]
  · change edgeExcess (starDeleteEven (dkFirstStar G x y) y) < _
    change edgeExcess (dkFirstStar G x y) < edgeExcess (dkEdgeDelete G x y) at he1
    omega

omit [Fintype V] in
theorem dkEdgeDelete_eq_deleteEdges (G : SimpleGraph V) (x y : V) :
    dkEdgeDelete G x y = G.deleteEdges {s(x,y)} := by
  ext a b
  simp only [dkEdgeDelete_adj, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
  tauto

theorem dkFirstStar_original_neighbors_odd (G : SimpleGraph V) {x y v : V}
    (hxy : G.Adj x y) (hxv : G.Adj x v) (hvy : v ≠ y) :
    Odd ((dkFirstStar G x y).degree v) := by
  apply original_neighbor_odd_after_starDeleteEven (dkEdgeDelete G x y) x v
  exact ⟨hxv,by tauto,fun h => hxy.ne h.1⟩

theorem dkTwoStar_original_neighbors_odd (G : SimpleGraph V) {x y v : V}
    (hxy : G.Adj x y) (hyv : G.Adj y v) (hvx : v ≠ x) :
    Odd ((dkTwoStarResidual G x y).degree v) := by
  apply original_neighbor_odd_after_starDeleteEven (dkFirstStar G x y) y v
  refine ⟨⟨hyv,fun h => hxy.ne h.1.symm,by tauto⟩,?_,?_⟩
  · exact fun h => hxy.ne h.1.symm
  · exact fun h => hvx h.1

theorem dkTwoStar_saved_edge_absent (G : SimpleGraph V) (x y : V) :
    ¬ (dkEdgeDelete G x y).Adj x y ∧ ¬ (dkFirstStar G x y).Adj x y ∧
    ¬ (dkTwoStarResidual G x y).Adj x y := by
  have h : ¬ (dkEdgeDelete G x y).Adj x y := fun ha => ha.2.1 ⟨rfl,rfl⟩
  exact ⟨h,fun ha => h ha.1,fun ha => h ha.1.1⟩

theorem dkTwoStar_edge_count (G : SimpleGraph V) {x y : V} (hxy : G.Adj x y) :
    (dkTwoStarResidual G x y).edgeFinset.card + evenNeighborCount (dkEdgeDelete G x y) x +
      evenNeighborCount (dkFirstStar G x y) y + 1 = G.edgeFinset.card := by
  have h0 := dkEdgeDelete_edge_count G hxy
  have h1 := edge_count_starDeleteEven (dkEdgeDelete G x y) x
  have h2 := edge_count_starDeleteEven (dkFirstStar G x y) y
  change (dkFirstStar G x y).edgeFinset.card + evenNeighborCount (dkEdgeDelete G x y) x =
    (dkEdgeDelete G x y).edgeFinset.card at h1
  change (dkTwoStarResidual G x y).edgeFinset.card + evenNeighborCount (dkFirstStar G x y) y =
    (dkFirstStar G x y).edgeFinset.card at h2
  omega

theorem dkFirstConfiguration_excess_drop (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) (hc : DKFirstConfiguration G x y) :
    edgeExcess (dkTwoStarResidual G x y) + 8 ≤ edgeExcess G := by
  have hk := dkFirstConfiguration_star_sizes G hxy hc
  have hE := dkTwoStar_edge_count G hxy.1
  have hA0 := congrArg Finset.card (dkEdgeDelete_active G hxy)
  have hA1 := (activeVertices_starDeleteEven_bounds (dkEdgeDelete G x y) x).2
  have hA2 := (activeVertices_starDeleteEven_bounds (dkFirstStar G x y) y).2
  change (activeVertices (dkEdgeDelete G x y)).card ≤
    (activeVertices (dkFirstStar G x y)).card + 1 at hA1
  change (activeVertices (dkFirstStar G x y)).card ≤
    (activeVertices (dkTwoStarResidual G x y)).card + 1 at hA2
  have hbG := activeVertices_card_le_twice_edges G
  have hbJ := activeVertices_card_le_twice_edges (dkTwoStarResidual G x y)
  unfold edgeExcess
  rcases hk.1 with h1|h1 <;> rcases hk.2 with h2|h2 <;> omega

/-- Actual graph certificate for t=0, and t=1 with a degree-four y endpoint.
The symmetric one-common-neighbor case is obtained by swapping x and y. -/
theorem dkFirstConfiguration_certificate (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) (hc : DKFirstConfiguration G x y) :
    (1 : ℚ) ≤ phi G - phi (dkTwoStarResidual G x y) ∧
    (oddVertices (dkTwoStarResidual G x y)).card = (oddVertices G).card + 6 ∧
    (nonisolatedEvenVertices (dkTwoStarResidual G x y)).card + 6 ≤
      (nonisolatedEvenVertices G).card ∧
    edgeExcess (dkTwoStarResidual G x y) + 8 ≤ edgeExcess G ∧
    (evenNeighborCount (dkEdgeDelete G x y) x = 2 ∨ evenNeighborCount (dkEdgeDelete G x y) x = 3) ∧
    (evenNeighborCount (dkFirstStar G x y) y = 2 ∨ evenNeighborCount (dkFirstStar G x y) y = 3) ∧
    (∀ v, G.Adj x v → v ≠ y → Odd ((dkFirstStar G x y).degree v)) ∧
    (∀ v, G.Adj y v → v ≠ x → Odd ((dkTwoStarResidual G x y).degree v)) ∧
    ¬ (dkTwoStarResidual G x y).Adj x y := by
  have h := dkFirstConfiguration_accounting G hxy hc
  have hk := dkFirstConfiguration_star_sizes G hxy hc
  exact ⟨h.1,h.2.1,h.2.2.1,dkFirstConfiguration_excess_drop G hxy hc,hk.1,hk.2,
    fun _ => dkFirstStar_original_neighbors_odd G hxy.1,
    fun _ => dkTwoStar_original_neighbors_odd G hxy.1,(dkTwoStar_saved_edge_absent G x y).2.2⟩

end Erdos583
end
end Source44_Erdos583_DKTwoStar
/- END Erdos583.DKTwoStar -/

/- BEGIN Erdos583.CycleBridge; source SHA256 c53cde4b093efd840d07581de9b1f2535c3ec9b942210559deb2a8490c3248e3 -/
section Source45_Erdos583_CycleBridge


/-! Concrete one-cycle/edge and two-cycle/bridge consumers of the full
short-path supplier. Roots of the two cycles need not coincide. -/
namespace Erdos583
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

theorem hasEdgePathPartition_cycle_and_incident_edge {x y : V}
    (c : G.Walk x x) (hc : c.IsCycle) (hxy : G.Adj x y)
    (hout : s(x,y) ∉ c.edgeSet) :
    HasEdgePathPartition G (c.edgeSet ∪ {s(x,y)}) 2 := by
  have hd : Disjoint c.edgeSet hxy.toWalk.edgeSet := by
    simpa using hout
  have hh := (pathPairAt_of_short_path_cycle c hxy.toWalk hc hxy.isPath_toWalk
    (by simp) hd ⟨x, hxy.toWalk.start_mem_support, c.start_mem_support⟩).toEdgePathPartition
  simpa using hh

theorem hasPathPartition_two_of_cycle_and_incident_edge {x y : V}
    (c : G.Walk x x) (hc : c.IsCycle) (hxy : G.Adj x y)
    (hout : s(x,y) ∉ c.edgeSet) (hcover : c.edgeSet ∪ {s(x,y)} = G.edgeSet) :
    HasPathPartition G 2 :=
  (hcover ▸ hasEdgePathPartition_cycle_and_incident_edge c hc hxy hout).toPathPartition

/-- Two edge-disjoint cycles, connected by an original edge outside both,
admit three simple paths even when their other vertices overlap arbitrarily. -/
theorem hasEdgePathPartition_two_cycles_bridge {x y : V}
    (c₀ : G.Walk x x) (c₁ : G.Walk y y) (hc₀ : c₀.IsCycle) (hc₁ : c₁.IsCycle)
    (hxy : G.Adj x y) (hd : Disjoint c₀.edgeSet c₁.edgeSet)
    (hout₀ : s(x,y) ∉ c₀.edgeSet) (hout₁ : s(x,y) ∉ c₁.edgeSet) :
    HasEdgePathPartition G ({s(x,y)} ∪ (c₀.edgeSet ∪ c₁.edgeSet)) 3 := by
  classical
  let roots : Bool → V := fun b => cond b y x
  let c : (b : Bool) → G.Walk (roots b) (roots b) := fun b =>
    match b with
    | false => c₀
    | true => c₁
  have hcy : ∀ b ∈ (Finset.univ : Finset Bool), (c b).IsCycle := by
    intro b _
    cases b
    · exact hc₀
    · exact hc₁
  have hdis : ((Finset.univ : Finset Bool) : Set Bool).Pairwise
      (fun b d => Disjoint (c b).edgeSet (c d).edgeSet) := by
    intro b _ d _ hne
    cases b <;> cases d
    · exact (hne rfl).elim
    · exact hd
    · exact hd.symm
    · exact (hne rfl).elim
  have hdP : ∀ b ∈ (Finset.univ : Finset Bool), Disjoint (c b).edgeSet hxy.toWalk.edgeSet := by
    intro b _
    cases b
    · simpa [c] using hout₀
    · simpa [c] using hout₁
  have hmet : ∀ b ∈ (Finset.univ : Finset Bool),
      ∃ z, z ∈ hxy.toWalk.support ∧ z ∈ (c b).support := by
    intro b _
    cases b
    · exact ⟨x, hxy.toWalk.start_mem_support, c₀.start_mem_support⟩
    · exact ⟨y, hxy.toWalk.end_mem_support, c₁.start_mem_support⟩
  have hh := hasEdgePathPartition_short_path_cycles c Finset.univ x y hxy.toWalk
    hxy.isPath_toWalk hcy hdis hdP hmet (by simp)
  have hE : hxy.toWalk.edgeSet ∪ (⋃ b ∈ (Finset.univ : Finset Bool), (c b).edgeSet) =
      {s(x,y)} ∪ (c₀.edgeSet ∪ c₁.edgeSet) := by
    ext e
    simp [c, roots]
  rw [hE] at hh
  exact hh.mono (by simp)

theorem hasPathPartition_three_of_two_cycles_bridge {x y : V}
    (c₀ : G.Walk x x) (c₁ : G.Walk y y) (hc₀ : c₀.IsCycle) (hc₁ : c₁.IsCycle)
    (hxy : G.Adj x y) (hd : Disjoint c₀.edgeSet c₁.edgeSet)
    (hout₀ : s(x,y) ∉ c₀.edgeSet) (hout₁ : s(x,y) ∉ c₁.edgeSet)
    (hcover : {s(x,y)} ∪ (c₀.edgeSet ∪ c₁.edgeSet) = G.edgeSet) :
    HasPathPartition G 3 :=
  (hcover ▸ hasEdgePathPartition_two_cycles_bridge c₀ c₁ hc₀ hc₁ hxy hd hout₀ hout₁).toPathPartition

end Erdos583
end Source45_Erdos583_CycleBridge
/- END Erdos583.CycleBridge -/

/- BEGIN Erdos583.DKFirstRestore; source SHA256 625a80361f2e5ba934cdda2c9ee81c4a95293a275b11cc27fed4a85eae25a164 -/
section Source46_Erdos583_DKFirstRestore





/-! Count-preserving restoration of the first two-star configuration. -/
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

/-- Restore a deleted star while retaining every saved cycle outside the
restored graph, with the actual rooted cycle count still visible. -/
theorem restore_star_avoiding_saved_cycles
    (G J : SimpleGraph V) (hJG : J ≤ G) (x : V) (Z : Finset V)
    (hZ : Z.Nonempty) (hz : ∀ z ∈ Z, G.Adj x z)
    (hmissing : ∀ z ∈ Z, ¬ J.Adj x z)
    (hcover : J.edgeSet ∪ (fun v => s(x,v)) '' (Z : Set V) = G.edgeSet)
    (hodd : ∀ v, G.Adj x v → Odd (J.degree v))
    (P C : Finset J.Subgraph)
    (hp : ∀ H ∈ P, IsNonemptyPathSubgraph H)
    (hc : ∀ H ∈ C, IsCycleSubgraph H) (hPC : Disjoint P C)
    (hdec : IsDecomposition J (P ∪ C)) :
    ∃ K : SimpleGraph V, K ≤ G ∧
      Disjoint K.edgeSet (⋃ H ∈ C, H.edgeSet) ∧
      K.edgeSet ∪ (⋃ H ∈ C, H.edgeSet) = G.edgeSet ∧
      ∃ q : ℕ, 2*q ≤ Z.card ∧ HasMixedPartitionAt K x P.card q := by
  classical
  let EC : Set (Sym2 V) := ⋃ H ∈ C, H.edgeSet
  let EP : Set (Sym2 V) := ⋃ H ∈ P, H.edgeSet
  let K := G.deleteEdges EC
  have hKG : K ≤ G := G.deleteEdges_le EC
  have hECJ : EC ⊆ J.edgeSet := by
    intro e he
    obtain ⟨H,hH⟩ := Set.mem_iUnion.mp he
    obtain ⟨_,heH⟩ := Set.mem_iUnion.mp hH
    exact H.edgeSet_subset heH
  have hJcover : J.edgeSet = EP ∪ EC := by
    rw [← hdec.2]
    ext e
    simp only [EP,EC,Set.mem_iUnion,exists_prop,Finset.mem_union,Set.mem_union]
    aesop
  have hPnot (H : J.Subgraph) (hH : H ∈ P) (e : Sym2 V) (he : e ∈ H.edgeSet) : e ∉ EC := by
    intro heC
    obtain ⟨Q,hQ⟩ := Set.mem_iUnion.mp heC
    obtain ⟨hQC,heQ⟩ := Set.mem_iUnion.mp hQ
    have hne : H ≠ Q := by
      intro h
      exact Finset.disjoint_left.mp hPC hH (h.symm ▸ hQC)
    exact Set.disjoint_left.mp
      (hdec.1 (Finset.mem_union_left _ hH) (Finset.mem_union_right _ hQC) hne) he heQ
  have hZnot (z : V) (hzm : z ∈ Z) : s(x,z) ∉ EC := by
    intro he
    exact hmissing z hzm (hECJ he)
  have hkeep (H : J.Subgraph) (hH : H ∈ P) : H.edgeSet ⊆ K.edgeSet := by
    intro e he
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact ⟨SimpleGraph.edgeSet_mono hJG (H.edgeSet_subset he),hPnot H hH e he⟩
  let f : P → K.Subgraph := fun H => rebaseSubgraph H.val (hkeep H.val H.property)
  let D := Finset.univ.image f
  have hDpath : ∀ H ∈ D, IsNonemptyPathSubgraph H := by
    intro H hH
    obtain ⟨Q,_,rfl⟩ := Finset.mem_image.mp hH
    exact (hp Q.val Q.property).rebase (hkeep Q.val Q.property)
  have hDdis : Set.PairwiseDisjoint (D : Set K.Subgraph) Subgraph.edgeSet := by
    intro H hH Q hQ hne
    obtain ⟨A,_,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨B,_,rfl⟩ := Finset.mem_image.mp hQ
    have hab : A.val ≠ B.val := fun h => hne (congrArg f (Subtype.ext h))
    exact hdec.1 (Finset.mem_union_left _ A.property) (Finset.mem_union_left _ B.property) hab
  have hDcover : (⋃ H : D, H.val.edgeSet) = EP := by
    ext e
    simp [D,f,EP]
  have hzK : ∀ z ∈ Z, K.Adj x z := by
    intro z hzm
    exact SimpleGraph.deleteEdges_adj.mpr ⟨hz z hzm,hZnot z hzm⟩
  have hDmissing : ∀ z ∈ Z, ∀ H ∈ D, ¬ H.Adj x z := by
    intro z hzm H hH hadj
    obtain ⟨Q,_,rfl⟩ := Finset.mem_image.mp hH
    exact hmissing z hzm (Q.val.adj_sub hadj)
  have hKcover : EP ∪ (fun v => s(x,v)) '' (Z : Set V) = K.edgeSet := by
    rw [SimpleGraph.edgeSet_deleteEdges]
    ext e
    constructor
    · rintro (heP | ⟨z,hzm,rfl⟩)
      · obtain ⟨H,hH⟩ := Set.mem_iUnion.mp heP
        obtain ⟨hHP,heH⟩ := Set.mem_iUnion.mp hH
        exact ⟨SimpleGraph.edgeSet_mono hJG (H.edgeSet_subset heH),hPnot H hHP e heH⟩
      · exact ⟨hz z hzm,hZnot z hzm⟩
    · rintro ⟨heG,heC⟩
      rw [← hcover,hJcover] at heG
      rcases heG with (heP | heC') | heZ
      · exact Or.inl heP
      · exact (heC heC').elim
      · exact Or.inr heZ
  have hend : ∀ v, K.Adj x v → ∃ H ∈ D, PathStartsAt H v := by
    intro v hv
    obtain ⟨H,hHP,hend⟩ := exists_pathStartsAt_of_odd_mixed P C hp hc hPC hdec v
      (hodd v (hKG hv))
    exact ⟨f ⟨H,hHP⟩,Finset.mem_image.mpr ⟨⟨H,hHP⟩,Finset.mem_univ _,rfl⟩,
      hend.rebase (hkeep H hHP)⟩
  obtain ⟨r,hr,hrest⟩ := restore_star_from_endpoint_partition D x Z hDpath hDdis
    hZ hzK hDmissing (by rw [hDcover]; exact hKcover) hend
  have hKCdis : Disjoint K.edgeSet EC := by
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact Set.disjoint_sdiff_left
  have hKCcover : K.edgeSet ∪ EC = G.edgeSet := by
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact Set.sdiff_union_of_subset (hECJ.trans (SimpleGraph.edgeSet_mono hJG))
  have hDcard : D.card ≤ P.card := Finset.card_image_le.trans (by simp)
  exact ⟨K,hKG,hKCdis,hKCcover,r,hr,hrest.mono_parts hDcard⟩

private theorem finset_empty_or_singleton {α : Type*} (S : Finset α) (hc : S.card ≤ 1) :
    S = ∅ ∨ ∃ a, S = {a} := by
  classical
  by_cases hz : S.card = 0
  · exact Or.inl (Finset.card_eq_zero.mp hz)
  · exact Or.inr (Finset.card_eq_one.mp (by omega))

omit [Fintype V] in
/-- Zero or one cycle at each endpoint of an outside original edge can be
replaced by one more path than the number of cycles. -/
theorem rooted_cycle_families_bridge {G K J : SimpleGraph V}
    (hKG : K ≤ G) (hJG : J ≤ G) {x y : V} (hxy : G.Adj x y)
    (Cx : Finset K.Subgraph) (Cy : Finset J.Subgraph)
    (hx : ∀ H ∈ Cx, IsRootedCycleSubgraph x H)
    (hy : ∀ H ∈ Cy, IsRootedCycleSubgraph y H)
    (hcx : Cx.card ≤ 1) (hcy : Cy.card ≤ 1)
    (hd : Disjoint (⋃ H ∈ Cx, H.edgeSet) (⋃ H ∈ Cy, H.edgeSet))
    (hox : s(x,y) ∉ ⋃ H ∈ Cx, H.edgeSet)
    (hoy : s(x,y) ∉ ⋃ H ∈ Cy, H.edgeSet) :
    HasEdgePathPartition G ({s(x,y)} ∪
      ((⋃ H ∈ Cx, H.edgeSet) ∪ (⋃ H ∈ Cy, H.edgeSet)))
      (Cx.card + Cy.card + 1) := by
  classical
  rcases finset_empty_or_singleton Cx hcx with rfl | ⟨A,rfl⟩ <;>
    rcases finset_empty_or_singleton Cy hcy with rfl | ⟨B,rfl⟩
  · simpa using hasEdgePathPartition_of_path hxy.toWalk hxy.isPath_toWalk
  · obtain ⟨c,hc,rfl⟩ := hy B (by simp)
    have hout : s(y,x) ∉ (c.mapLe hJG).edgeSet := by
      simpa [show s(y,x) = s(x,y) from Sym2.eq_swap] using hoy
    have h := hasEdgePathPartition_cycle_and_incident_edge (c.mapLe hJG)
      (hc.mapLe hJG) hxy.symm hout
    simpa [show s(y,x) = s(x,y) from Sym2.eq_swap, Set.union_comm] using h
  · obtain ⟨c,hc,rfl⟩ := hx A (by simp)
    have hout : s(x,y) ∉ (c.mapLe hKG).edgeSet := by simpa using hox
    have h := hasEdgePathPartition_cycle_and_incident_edge (c.mapLe hKG)
      (hc.mapLe hKG) hxy hout
    simpa [Set.union_comm] using h
  · obtain ⟨c,hc,rfl⟩ := hx A (by simp)
    obtain ⟨d,hdc,rfl⟩ := hy B (by simp)
    have hdis : Disjoint (c.mapLe hKG).edgeSet (d.mapLe hJG).edgeSet := by simpa using hd
    have houtx : s(x,y) ∉ (c.mapLe hKG).edgeSet := by simpa using hox
    have houty : s(x,y) ∉ (d.mapLe hJG).edgeSet := by simpa using hoy
    simpa using hasEdgePathPartition_two_cycles_bridge (c.mapLe hKG) (d.mapLe hJG)
      (hc.mapLe hKG) (hdc.mapLe hJG) hxy hdis houtx houty

omit [Fintype V] in
/-- Convert a restored rooted mixed partition and one saved rooted cycle
family, using the outside edge joining their roots. -/
theorem saved_cycle_bridge_consumer {G K J : SimpleGraph V}
    (hKG : K ≤ G) (hJG : J ≤ G) {x y : V} (hxy : G.Adj x y)
    (Cy : Finset J.Subgraph) (hy : ∀ H ∈ Cy, IsRootedCycleSubgraph y H)
    (hcy : Cy.card ≤ 1)
    (hdis : Disjoint K.edgeSet (⋃ H ∈ Cy, H.edgeSet))
    (hcover : (K.edgeSet ∪ (⋃ H ∈ Cy, H.edgeSet)) ∪ {s(x,y)} = G.edgeSet)
    (hox : s(x,y) ∉ K.edgeSet) (hoy : s(x,y) ∉ J.edgeSet)
    {a q : ℕ} (hK : HasMixedPartitionAt K x a q) (hq : q ≤ 1) :
    HasPathPartition G (a + Cy.card + 1) := by
  classical
  obtain ⟨P,Cx,hp,hx,hPC,hdec,hbudget,hcount⟩ := hK
  let EP : Set (Sym2 V) := ⋃ H ∈ P, H.edgeSet
  let EX : Set (Sym2 V) := ⋃ H ∈ Cx, H.edgeSet
  let EY : Set (Sym2 V) := ⋃ H ∈ Cy, H.edgeSet
  have hPK : EP ⊆ K.edgeSet := by
    intro e he
    obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp he
    exact H.edgeSet_subset heH
  have hXK : EX ⊆ K.edgeSet := by
    intro e he
    obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp he
    exact H.edgeSet_subset heH
  have hYJ : EY ⊆ J.edgeSet := by
    intro e he
    obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp he
    exact H.edgeSet_subset heH
  have hPX : Disjoint EP EX := by
    apply Set.disjoint_left.mpr
    intro e heP heX
    obtain ⟨A,hA,heA⟩ := Set.mem_iUnion₂.mp heP
    obtain ⟨B,hB,heB⟩ := Set.mem_iUnion₂.mp heX
    have hne : A ≠ B := fun h => Finset.disjoint_left.mp hPC hA (h.symm ▸ hB)
    exact Set.disjoint_left.mp
      (hdec.1 (Finset.mem_union_left _ hA) (Finset.mem_union_right _ hB) hne) heA heB
  have hpath : HasEdgePathPartition G EP P.card := by
    refine ⟨P.image (liftSubgraph hKG), ?_, ?_, ?_, Finset.card_image_le⟩
    · intro H hH
      obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hH
      exact (hp A hA).lift hKG
    · intro H hH L hL hne
      obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hH
      obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hL
      exact hdec.1 (Finset.mem_union_left _ hA) (Finset.mem_union_left _ hB)
        (fun h => hne (h ▸ rfl))
    · ext e
      simp [EP]
  have hcycle : HasEdgePathPartition G ({s(x,y)} ∪ (EX ∪ EY))
      (Cx.card + Cy.card + 1) :=
    rooted_cycle_families_bridge hKG hJG hxy Cx Cy hx hy (by omega) hcy
      (hdis.mono_left hXK) (fun he => hox (hXK he)) (fun he => hoy (hYJ he))
  have hseparate : Disjoint EP ({s(x,y)} ∪ (EX ∪ EY)) := by
    apply Set.disjoint_left.mpr
    intro e heP heR
    rcases heR with he | heX | heY
    · exact hox (Set.mem_singleton_iff.mp he ▸ hPK heP)
    · exact Set.disjoint_left.mp hPX heP heX
    · exact Set.disjoint_left.mp hdis (hPK heP) heY
  have hKcover : EP ∪ EX = K.edgeSet := by
    rw [← hdec.2]
    ext e
    simp only [EP,EX,Set.mem_union,Set.mem_iUnion,exists_prop,Finset.mem_union]
    aesop
  have hfull : EP ∪ ({s(x,y)} ∪ (EX ∪ EY)) = G.edgeSet := by
    calc
      _ = ((EP ∪ EX) ∪ EY) ∪ {s(x,y)} := by
        ext e
        simp only [Set.mem_union]
        tauto
      _ = G.edgeSet := by rw [hKcover]; exact hcover
  have hpart := hpath.union hcycle hseparate
  rw [hfull] at hpart
  exact (hpart.mono (by omega)).toPathPartition

omit [Fintype V] in
theorem dkEdgeDelete_edge_cover (G : SimpleGraph V) {x y : V}
    (hxy : G.Adj x y) : (dkEdgeDelete G x y).edgeSet ∪ {s(x,y)} = G.edgeSet := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [Set.mem_union,Set.mem_singleton_iff,mem_edgeSet,dkEdgeDelete_adj]
    constructor
    · rintro (he | he)
      · exact he.1
      · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hxy
        · exact hxy.symm
    · intro he
      by_cases hs : s(a,b) = s(x,y)
      · exact Or.inr hs
      · exact Or.inl ⟨he,fun h => hs (Sym2.eq_iff.mpr (Or.inl h)),
          fun h => hs (Sym2.eq_iff.mpr (Or.inr h))⟩

/-- Reverse two nonempty stars of size at most three and restore their saved
joining edge. The supplied residual partition is arbitrary. -/
theorem restore_dkTwoStarResidual (G : SimpleGraph V) {x y : V}
    (hxy : G.Adj x y)
    (hkx : 0 < evenNeighborCount (dkEdgeDelete G x y) x)
    (hkx' : evenNeighborCount (dkEdgeDelete G x y) x ≤ 3)
    (hky : 0 < evenNeighborCount (dkFirstStar G x y) y)
    (hky' : evenNeighborCount (dkFirstStar G x y) y ≤ 3)
    {m : ℕ} (hpart : HasPathPartition (dkTwoStarResidual G x y) m) :
    HasPathPartition G (m+1) := by
  classical
  let G0 := dkEdgeDelete G x y
  let G1 := dkFirstStar G x y
  have h0G : G0 ≤ G := fun _ _ h => h.1
  have h10 : G1 ≤ G0 := starDeleteEven_le G0 x
  have h1G : G1 ≤ G := h10.trans h0G
  obtain ⟨qy,hqy,P,C,hp,hc,hPC,hdec,hbudget,hcount⟩ :=
    restore_even_neighbor_star G1 y hky hpart
  change 2*qy ≤ evenNeighborCount (dkFirstStar G x y) y at hqy
  obtain ⟨K,hK0,hKC,hKcover,qx,hqx,hK⟩ :=
    restore_star_avoiding_saved_cycles G0 G1 h10 x (evenNeighbors G0 x)
      (Finset.card_pos.mp hkx) (fun z hz => (mem_evenNeighbors G0 x z).mp hz |>.1)
      (fun z hz hj => hj.2.1 ⟨rfl,(mem_evenNeighbors G0 x z).mp hz |>.2⟩)
      (starDeleteEven_edge_cover G0 x) (original_neighbor_odd_after_starDeleteEven G0 x)
      P C hp (fun H hH => ⟨y,hc H hH⟩) hPC hdec
  change 2*qx ≤ evenNeighborCount (dkEdgeDelete G x y) x at hqx
  have h0out : s(x,y) ∉ G0.edgeSet := (dkTwoStar_saved_edge_absent G x y).1
  have h1out : s(x,y) ∉ G1.edgeSet := (dkTwoStar_saved_edge_absent G x y).2.1
  have hfull : (K.edgeSet ∪ (⋃ H ∈ C, H.edgeSet)) ∪ {s(x,y)} = G.edgeSet := by
    rw [hKcover]
    exact dkEdgeDelete_edge_cover G hxy
  have hresult := saved_cycle_bridge_consumer (hK0.trans h0G) h1G hxy C hc
    (by omega) hKC hfull (fun he => h0out (SimpleGraph.edgeSet_mono hK0 he)) h1out hK (by omega)
  obtain ⟨D,hD,hdecD,hcardD⟩ := hresult
  exact ⟨D,hD,hdecD,by omega⟩

/-- First DK configuration: its concrete two-star residual lifts with at most
one extra path, keeping every original edge exactly once. -/
theorem restore_dkFirstConfiguration (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) (hc : DKFirstConfiguration G x y)
    {m : ℕ} (hpart : HasPathPartition (dkTwoStarResidual G x y) m) :
    HasPathPartition G (m+1) := by
  obtain ⟨hx,hy⟩ := dkFirstConfiguration_star_sizes G hxy hc
  exact restore_dkTwoStarResidual G hxy.1 (by omega) (by omega) (by omega) (by omega) hpart

/-- The actual potential decrease pays the first configuration's path cost.
The residual potential bound is an explicit hypothesis. -/
theorem restore_dkFirstConfiguration_phi_bound (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) (hc : DKFirstConfiguration G x y) {b : ℚ}
    (hbound : HasPathBound (dkTwoStarResidual G x y) (phi (dkTwoStarResidual G x y)-b)) :
    HasPathBound G (phi G-b) := by
  obtain ⟨m,hm,hmb⟩ := hasPathBound_iff_exists_partition.mp hbound
  have hphi := (dkFirstConfiguration_certificate G hxy hc).1
  refine hasPathBound_iff_exists_partition.mpr
    ⟨m+1,restore_dkFirstConfiguration G hxy hc hm,?_⟩
  push_cast
  linarith

end Erdos583
end Source46_Erdos583_DKFirstRestore
/- END Erdos583.DKFirstRestore -/

/- BEGIN Erdos583.DKRetainedStar; source SHA256 4689f4e2fc41d6276cd1b6f2b3c400aee0e3781a013867b1491f624ee6820b2d -/
section Source47_Erdos583_DKRetainedStar


noncomputable section
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

/-- Delete a specified subset of a star, retaining all ambient vertices. -/
def dkPartialStar (G : SimpleGraph V) (x : V) (S : Finset V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ ¬(a = x ∧ b ∈ S) ∧ ¬(b = x ∧ a ∈ S)
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

omit [Fintype V] in
@[simp] theorem dkPartialStar_adj (G : SimpleGraph V) (x : V) (S : Finset V) (a b : V) :
    (dkPartialStar G x S).Adj a b ↔ G.Adj a b ∧ ¬(a = x ∧ b ∈ S) ∧ ¬(b = x ∧ a ∈ S) := Iff.rfl

theorem dkPartialStar_degree_center (G : SimpleGraph V) (x : V) (S : Finset V)
    (hS : S ⊆ evenNeighbors G x) :
    (dkPartialStar G x S).degree x = G.degree x - S.card := by
  have hs : S ⊆ G.neighborFinset x := hS.trans (evenNeighbors_subset G x)
  have he : (dkPartialStar G x S).neighborFinset x = G.neighborFinset x \ S := by
    ext v
    simp only [mem_neighborFinset, dkPartialStar_adj, Finset.mem_sdiff]
    constructor
    · intro h; exact ⟨h.1, fun hv => h.2.1 ⟨by trivial,hv⟩⟩
    · rintro ⟨h,hn⟩
      exact ⟨h,by tauto,fun he => h.ne he.1.symm⟩
  rw [← card_neighborFinset_eq_degree, he, Finset.card_sdiff_of_subset hs,
    card_neighborFinset_eq_degree]

theorem dkPartialStar_degree_selected (G : SimpleGraph V) (x : V) (S : Finset V)
    (hS : S ⊆ evenNeighbors G x) {v : V} (hv : v ∈ S) :
    (dkPartialStar G x S).degree v = G.degree v - 1 := by
  have ha := (mem_evenNeighbors G x v).mp (hS hv) |>.1
  have he : (dkPartialStar G x S).neighborFinset v = (G.neighborFinset v).erase x := by
    ext w
    simp only [mem_neighborFinset, dkPartialStar_adj, Finset.mem_erase]
    simp [ha.ne.symm,hv,and_comm]
  rw [← card_neighborFinset_eq_degree, he,
    Finset.card_erase_of_mem ((G.mem_neighborFinset v x).mpr ha.symm), card_neighborFinset_eq_degree]

theorem dkPartialStar_degree_other (G : SimpleGraph V) (x : V) (S : Finset V)
    {v : V} (hvx : v ≠ x) (hvS : v ∉ S) :
    (dkPartialStar G x S).degree v = G.degree v := by
  have he : (dkPartialStar G x S).neighborFinset v = G.neighborFinset v := by
    ext w
    simp only [mem_neighborFinset, dkPartialStar_adj]
    simp [hvx,hvS]
  exact congrArg Finset.card he

theorem dkPartialStar_selected_odd (G : SimpleGraph V) (x : V) (S : Finset V)
    (hS : S ⊆ evenNeighbors G x) {v : V} (hv : v ∈ S) :
    Odd ((dkPartialStar G x S).degree v) := by
  rw [dkPartialStar_degree_selected G x S hS hv]
  have hh := selected_degree_ge_two G x v (hS hv)
  exact Nat.Even.sub_odd (by omega) ((mem_evenNeighbors G x v).mp (hS hv)).2 (by decide)

theorem dkPartialStar_phi (G : SimpleGraph V) (x : V) (S : Finset V)
    (hS : S ⊆ evenNeighbors G x) :
    phi G - phi (dkPartialStar G x S) = (S.card : ℚ)/6 +
      parityWeight (G.degree x) - parityWeight ((dkPartialStar G x S).degree x) := by
  have hxS : x ∉ S := fun hx => (mem_evenNeighbors G x x).mp (hS hx) |>.1.ne rfl
  have hpoint (v : V) : parityWeight (G.degree v) - parityWeight ((dkPartialStar G x S).degree v) =
      (if v = x then parityWeight (G.degree x) - parityWeight ((dkPartialStar G x S).degree x) else 0) +
      (if v ∈ S then (1/6 : ℚ) else 0) := by
    by_cases hvx : v = x
    · subst v; simp [hxS]
    by_cases hvS : v ∈ S
    · have he := (mem_evenNeighbors G x v).mp (hS hvS)
      have ho := dkPartialStar_selected_odd G x S hS hvS
      rw [parityWeight_even_nonzero he.2 he.1.degree_pos_right.ne']
      norm_num [hvx,hvS,parityWeight,ho,Nat.not_even_iff_odd.mpr ho]
    · rw [dkPartialStar_degree_other G x S hvx hvS]
      simp [hvx,hvS]
  rw [phi_eq_sum_parityWeight, phi_eq_sum_parityWeight, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun v _ => hpoint v)]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hs : (∑ v : V, if v ∈ S then (1/6 : ℚ) else 0) = (S.card : ℚ)/6 := by
    rw [← Finset.sum_filter]
    have hf : Finset.univ.filter (fun v => v ∈ S) = S := by ext v; simp
    rw [hf,Finset.sum_const]
    simp [nsmul_eq_mul,div_eq_mul_inv]
  rw [hs]
  ring

abbrev dkRetainedFirstStar (G : SimpleGraph V) (x y : V) : SimpleGraph V :=
  dkPartialStar G x ((evenNeighbors G x).erase y)
abbrev dkRetainedResidual (G : SimpleGraph V) (x y : V) : SimpleGraph V :=
  starDeleteEven (dkRetainedFirstStar G x y) y

theorem dkRetained_first_sizes (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) (hx4 : (evenCore G).degree x = 4) :
    ((evenNeighbors G x).erase y).card = 3 ∧
    Odd ((dkRetainedFirstStar G x y).degree x) ∧
    (dkRetainedFirstStar G x y).degree y = G.degree y := by
  have hm := (mem_evenNeighbors G x y).mpr ⟨hxy.1,hxy.2.2⟩
  have hc := Finset.card_erase_add_one hm
  have hn : (evenNeighbors G x).card = 4 := by
    simpa only [evenCore_degree_of_even G x hxy.2.1,evenNeighborCount] using hx4
  have hs : ((evenNeighbors G x).erase y).card = 3 := by omega
  have hsub := Finset.erase_subset (s := evenNeighbors G x) (a := y)
  have hle := evenNeighborCount_le_degree G x
  have ho : Odd ((dkRetainedFirstStar G x y).degree x) := by
    rw [dkPartialStar_degree_center G x _ hsub,hs]
    exact Nat.Even.sub_odd (by unfold evenNeighborCount at hle; omega) hxy.2.1 (by decide)
  exact ⟨hs,ho,dkPartialStar_degree_other G x _ hxy.1.ne.symm (by simp)⟩

theorem dkRetained_neighbors_right (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) (hx4 : (evenCore G).degree x = 4) :
    evenNeighbors (dkRetainedFirstStar G x y) y = evenNeighbors (dkFirstStar G x y) y := by
  rw [dkFirstStar_neighbors_right G hxy]
  ext v
  by_cases hvx : v = x
  · subst v
    have ho := (dkRetained_first_sizes G hxy hx4).2.1
    simp [mem_evenNeighbors, Nat.not_even_iff_odd.mpr ho]
  by_cases hvy : v = y
  · subst v
    simp [mem_evenNeighbors]
  by_cases hvS : v ∈ (evenNeighbors G x).erase y
  · have ho := dkPartialStar_selected_odd G x _ (Finset.erase_subset y _) hvS
    have hvA := (Finset.mem_erase.mp hvS).2
    simp only [Finset.mem_sdiff, Finset.mem_erase, mem_evenNeighbors]
    have hn := Nat.not_even_iff_odd.mpr ho
    have he := (mem_evenNeighbors G x v).mp hvA
    tauto
  · have hd := dkPartialStar_degree_other G x ((evenNeighbors G x).erase y) hvx hvS
    have hvA : v ∉ evenNeighbors G x := by simpa [hvy] using hvS
    simp only [mem_evenNeighbors, Finset.mem_sdiff, Finset.mem_erase, hd, dkPartialStar_adj]
    simp [hxy.1.ne.symm,hvx,hvy,mem_evenNeighbors] at hvA ⊢
    tauto

theorem dkRetained_phi_first (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) (hx4 : (evenCore G).degree x = 4) :
    phi G - phi (dkRetainedFirstStar G x y) = 2/3 := by
  have hs := dkRetained_first_sizes G hxy hx4
  have hp := dkPartialStar_phi G x ((evenNeighbors G x).erase y) (Finset.erase_subset y _)
  rw [hs.1,parityWeight_even_nonzero hxy.2.1 hxy.1.degree_pos_left.ne'] at hp
  have hw : parityWeight ((dkRetainedFirstStar G x y).degree x) = 1/2 := by
    norm_num [parityWeight,hs.2.1,Nat.not_even_iff_odd.mpr hs.2.1]
  rw [hw] at hp
  norm_num at hp
  exact hp

theorem dkPartialStar_edge_count (G : SimpleGraph V) (x : V) (S : Finset V)
    (hS : S ⊆ evenNeighbors G x) :
    (dkPartialStar G x S).edgeFinset.card + S.card = G.edgeFinset.card := by
  have hxS : x ∉ S := fun hx => (mem_evenNeighbors G x x).mp (hS hx) |>.1.ne rfl
  have hsle : S.card ≤ G.degree x := (Finset.card_le_card hS).trans (evenNeighborCount_le_degree G x)
  have hpoint (v : V) : G.degree v = (dkPartialStar G x S).degree v +
      (if v = x then S.card else 0) + (if v ∈ S then 1 else 0) := by
    by_cases hvx : v = x
    · subst v
      rw [dkPartialStar_degree_center G x S hS]
      simp only [if_true,if_neg hxS,add_zero]
      omega
    by_cases hvS : v ∈ S
    · rw [dkPartialStar_degree_selected G x S hS hvS]
      have hp := selected_degree_ge_two G x v (hS hvS)
      simp only [if_neg hvx,if_pos hvS,add_zero]
      omega
    · rw [dkPartialStar_degree_other G x S hvx hvS]
      simp [hvx,hvS]
  have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset V)) rfl (fun v _ => hpoint v)
  rw [G.sum_degrees_eq_twice_card_edges, Finset.sum_add_distrib, Finset.sum_add_distrib,
    (dkPartialStar G x S).sum_degrees_eq_twice_card_edges] at hs
  have hcount : (∑ v : V, if v ∈ S then 1 else 0) = S.card := by
    rw [← Finset.sum_filter]
    have hf : Finset.univ.filter (fun v => v ∈ S) = S := by ext v; simp
    simp [hf]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,hcount] at hs
  omega

theorem dkPartialStar_active_eq (G : SimpleGraph V) (x : V) (S : Finset V)
    (hS : S ⊆ evenNeighbors G x) (hx : (dkPartialStar G x S).degree x ≠ 0) :
    activeVertices (dkPartialStar G x S) = activeVertices G := by
  ext v
  simp only [mem_activeVertices]
  by_cases hvx : v = x
  · subst v
    have hg : G.degree x ≠ 0 := by
      intro hz
      apply hx
      rw [dkPartialStar_degree_center G x S hS,hz,Nat.zero_sub]
    exact iff_of_true hx hg
  by_cases hvS : v ∈ S
  · have hp := selected_degree_ge_two G x v (hS hvS)
    rw [dkPartialStar_degree_selected G x S hS hvS]
    omega
  · rw [dkPartialStar_degree_other G x S hvx hvS]

theorem dkPartialStar_odd_count (G : SimpleGraph V) (x : V) (S : Finset V)
    (hS : S ⊆ evenNeighbors G x) (hx : Even (G.degree x))
    (hnew : Odd ((dkPartialStar G x S).degree x)) :
    (oddVertices (dkPartialStar G x S)).card = (oddVertices G).card + S.card + 1 := by
  have hxS : x ∉ S := fun hx => (mem_evenNeighbors G x x).mp (hS hx) |>.1.ne rfl
  have hxo : x ∉ oddVertices G := by simpa using Nat.not_odd_iff_even.mpr hx
  have hdis : Disjoint (oddVertices G) S := by
    apply Finset.disjoint_left.mpr
    intro v ho hv
    exact (Nat.not_even_iff_odd.mpr ((mem_oddVertices G v).mp ho))
      ((mem_evenNeighbors G x v).mp (hS hv)).2
  have he : oddVertices (dkPartialStar G x S) = insert x (oddVertices G ∪ S) := by
    ext v
    by_cases hvx : v = x
    · subst v; simp [hnew]
    by_cases hvS : v ∈ S
    · simp [dkPartialStar_selected_odd G x S hS hvS,hvS]
    · simp only [mem_oddVertices,Finset.mem_insert,Finset.mem_union,
        dkPartialStar_degree_other G x S hvx hvS]
      tauto
  rw [he,Finset.card_insert_of_notMem (by simp [hxS,hxo]),Finset.card_union_of_disjoint hdis]

theorem dkRetained_original_neighbors_x_odd (G : SimpleGraph V) {x y v : V}
    (hxv : G.Adj x v) (hvy : v ≠ y) :
    Odd ((dkRetainedFirstStar G x y).degree v) := by
  by_cases he : Even (G.degree v)
  · apply dkPartialStar_selected_odd G x _ (Finset.erase_subset y _)
    exact Finset.mem_erase.mpr ⟨hvy,(mem_evenNeighbors G x v).mpr ⟨hxv,he⟩⟩
  · have hnot : v ∉ (evenNeighbors G x).erase y := by simp [he]
    rw [dkPartialStar_degree_other G x _ hxv.ne.symm hnot]
    exact Nat.not_even_iff_odd.mp he

theorem dkRetained_original_neighbors_y_odd (G : SimpleGraph V) {x y v : V}
    (hxy : G.Adj x y) (hyv : G.Adj y v) :
    Odd ((dkRetainedResidual G x y).degree v) := by
  apply original_neighbor_odd_after_starDeleteEven (dkRetainedFirstStar G x y) y v
  refine ⟨hyv,fun h => hxy.ne h.1.symm,?_⟩
  rintro ⟨_,hy⟩
  exact (Finset.mem_erase.mp hy).1 rfl

theorem dkRetained_edge_survives (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) (hx4 : (evenCore G).degree x = 4) :
    (dkRetainedFirstStar G x y).Adj x y ∧ (dkRetainedResidual G x y).Adj x y := by
  have ha : (dkRetainedFirstStar G x y).Adj x y := by
    exact ⟨hxy.1,by simp,fun h => hxy.1.ne h.1.symm⟩
  have ho := (dkRetained_first_sizes G hxy hx4).2.1
  exact ⟨ha,ha,fun h => hxy.1.ne h.1,fun h => (Nat.not_even_iff_odd.mpr ho) h.2⟩

theorem dkRetained_count_right (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) (hx4 : (evenCore G).degree x = 4)
    (hy4 : (evenCore G).degree y = 4) (ht2 : (originalEvenCommonNeighbors G x y).card = 2) :
    evenNeighborCount (dkRetainedFirstStar G x y) y = 1 := by
  have h := dkFirstStar_count_right G hxy
  have hc : evenNeighborCount (dkRetainedFirstStar G x y) y = evenNeighborCount (dkFirstStar G x y) y :=
    congrArg Finset.card (dkRetained_neighbors_right G hxy hx4)
  omega

theorem dkRetained_accounting (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) (hx4 : (evenCore G).degree x = 4)
    (hy4 : (evenCore G).degree y = 4) (ht2 : (originalEvenCommonNeighbors G x y).card = 2) :
    phi G - phi (dkRetainedResidual G x y) = 1 ∧
    (oddVertices (dkRetainedResidual G x y)).card = (oddVertices G).card + 6 ∧
    (nonisolatedEvenVertices (dkRetainedResidual G x y)).card + 6 =
      (nonisolatedEvenVertices G).card ∧
    (activeVertices (dkRetainedResidual G x y)).card = (activeVertices G).card ∧
    (dkRetainedResidual G x y).edgeFinset.card + 4 = G.edgeFinset.card ∧
    edgeExcess (dkRetainedResidual G x y) + 8 = edgeExcess G := by
  have hs := dkRetained_first_sizes G hxy hx4
  have hk := dkRetained_count_right G hxy hx4 hy4 ht2
  have hsub := Finset.erase_subset y (evenNeighbors G x)
  have hxpos : (dkRetainedFirstStar G x y).degree x ≠ 0 := by
    obtain ⟨k,hk⟩ := hs.2.1; omega
  have hactive1 := dkPartialStar_active_eq G x _ hsub hxpos
  have hu1 := dkPartialStar_odd_count G x _ hsub hxy.2.1 hs.2.1
  have he1 := dkPartialStar_edge_count G x _ hsub
  rw [hs.1] at hu1 he1
  change (oddVertices (dkRetainedFirstStar G x y)).card = (oddVertices G).card + 3 + 1 at hu1
  change (dkRetainedFirstStar G x y).edgeFinset.card + 3 = G.edgeFinset.card at he1
  change activeVertices (dkRetainedFirstStar G x y) = activeVertices G at hactive1
  have hyd : (dkRetainedFirstStar G x y).degree y = G.degree y := hs.2.2
  have hypos := hxy.1.degree_pos_right
  have hypos2 : 2 ≤ G.degree y := selected_degree_ge_two G x y
    ((mem_evenNeighbors G x y).mpr ⟨hxy.1,hxy.2.2⟩)
  have hodd : Odd ((dkRetainedResidual G x y).degree y) := by
    rw [degree_starDeleteEven_center, hk, hyd]
    exact Nat.Even.sub_odd (by omega) hxy.2.2 (by decide)
  have hnewpos : (dkRetainedResidual G x y).degree y ≠ 0 := by obtain ⟨k,hk⟩ := hodd; omega
  have hphi1 := dkRetained_phi_first G hxy hx4
  have hphi2 := phi_starDeleteEven_exact (dkRetainedFirstStar G x y) y
  have hw1 : parityWeight ((dkRetainedFirstStar G x y).degree y) = 2/3 := by
    rw [hyd,parityWeight_even_nonzero hxy.2.2 (by omega)]
  have hw2 : parityWeight ((dkRetainedResidual G x y).degree y) = 1/2 := by
    norm_num [parityWeight,hodd,Nat.not_even_iff_odd.mpr hodd]
  rw [hk,hw1,hw2] at hphi2
  have hu2 := odd_count_starDeleteEven (dkRetainedFirstStar G x y) y
  have hnold : ¬ Odd ((dkRetainedFirstStar G x y).degree y) := by
    rw [hyd]; exact Nat.not_odd_iff_even.mpr hxy.2.2
  simp only [if_neg hnold,if_pos hodd,hk] at hu2
  have hi2 := isolate_count_starDeleteEven (dkRetainedFirstStar G x y) y
  have hnold0 : (dkRetainedFirstStar G x y).degree y ≠ 0 := by rw [hyd]; omega
  simp only [if_neg hnold0,if_neg hnewpos,add_zero] at hi2
  have hac1 := congrArg Finset.card hactive1
  have hacG1 := activeVertices_card_add_isolated (dkRetainedFirstStar G x y)
  have hacJ := activeVertices_card_add_isolated (dkRetainedResidual G x y)
  have hacG := activeVertices_card_add_isolated G
  have he2 := edge_count_starDeleteEven (dkRetainedFirstStar G x y) y
  rw [hk] at he2
  have hpG := vertex_parity_count G
  have hpJ := vertex_parity_count (dkRetainedResidual G x y)
  have hboundG := activeVertices_card_le_twice_edges G
  have hboundJ := activeVertices_card_le_twice_edges (dkRetainedResidual G x y)
  change phi (dkRetainedFirstStar G x y) - phi (dkRetainedResidual G x y) = _ at hphi2
  change (oddVertices (dkRetainedResidual G x y)).card + 0 =
    (oddVertices (dkRetainedFirstStar G x y)).card + 1 + 1 at hu2
  change (isolatedVertices (dkRetainedResidual G x y)).card =
    (isolatedVertices (dkRetainedFirstStar G x y)).card at hi2
  change (dkRetainedResidual G x y).edgeFinset.card + 1 =
    (dkRetainedFirstStar G x y).edgeFinset.card at he2
  refine ⟨by norm_num at hphi2; linarith,by omega,by omega,by omega,by omega,?_⟩
  unfold edgeExcess
  omega

omit [Fintype V] in
theorem dkPartialStar_le (G : SimpleGraph V) (x : V) (S : Finset V) :
    dkPartialStar G x S ≤ G := fun _ _ h => h.1

omit [Fintype V] in
theorem dkPartialStar_missing (G : SimpleGraph V) (x : V) (S : Finset V) {z : V}
    (hz : z ∈ S) : ¬ (dkPartialStar G x S).Adj x z := fun h => h.2.1 ⟨rfl,hz⟩

theorem dkPartialStar_edge_cover (G : SimpleGraph V) (x : V) (S : Finset V)
    (hS : S ⊆ evenNeighbors G x) :
    G.edgeSet = (dkPartialStar G x S).edgeSet ∪ {e | ∃ z ∈ S, e = s(x,z)} := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    change G.Adj a b ↔ (dkPartialStar G x S).Adj a b ∨ ∃ z ∈ S, s(a,b) = s(x,z)
    constructor
    · intro hab
      by_cases hax : a = x ∧ b ∈ S
      · obtain ⟨rfl,hb⟩ := hax
        exact Or.inr ⟨b,hb,rfl⟩
      by_cases hbx : b = x ∧ a ∈ S
      · obtain ⟨rfl,ha⟩ := hbx
        exact Or.inr ⟨a,ha,Sym2.eq_swap⟩
      exact Or.inl ⟨hab,hax,hbx⟩
    · rintro (h | ⟨z,hz,he⟩)
      · exact h.1
      · change s(a,b) ∈ G.edgeSet
        rw [he]
        exact ((mem_evenNeighbors G x z).mp (hS hz)).1

theorem dkRetained_unique_edge (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) (hx4 : (evenCore G).degree x = 4)
    (hy4 : (evenCore G).degree y = 4) (ht2 : (originalEvenCommonNeighbors G x y).card = 2) :
    ∃ z : V, evenNeighbors (dkRetainedFirstStar G x y) y = {z} ∧
      G.Adj y z ∧ z ≠ x ∧ z ≠ y ∧ Even (G.degree z) ∧ z ∉ evenNeighbors G x := by
  have hk := dkRetained_count_right G hxy hx4 hy4 ht2
  obtain ⟨z,hz⟩ := Finset.card_eq_one.mp hk
  have hmem : z ∈ evenNeighbors (dkRetainedFirstStar G x y) y := by rw [hz]; simp
  have ha := (mem_evenNeighbors _ y z).mp hmem |>.1
  have hset := dkRetained_neighbors_right G hxy hx4
  rw [dkFirstStar_neighbors_right G hxy] at hset
  rw [hset] at hmem
  obtain ⟨h1,h2⟩ := Finset.mem_sdiff.mp hmem
  obtain ⟨hne,h3⟩ := Finset.mem_erase.mp h1
  have h4 := (mem_evenNeighbors G y z).mp h3
  exact ⟨z,hz,h4.1,hne,ha.ne.symm,h4.2,h2⟩

/-- The retained-xy (4,4,t=2) reduction, with exact original graph accounting
and all neighbor parity inputs for an R1-then-three-edge restoration. -/
theorem dkRetained_certificate (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) (hx4 : (evenCore G).degree x = 4)
    (hy4 : (evenCore G).degree y = 4) (ht2 : (originalEvenCommonNeighbors G x y).card = 2) :
    phi G - phi (dkRetainedResidual G x y) = 1 ∧
    (oddVertices (dkRetainedResidual G x y)).card = (oddVertices G).card + 6 ∧
    (nonisolatedEvenVertices (dkRetainedResidual G x y)).card + 6 =
      (nonisolatedEvenVertices G).card ∧
    (activeVertices (dkRetainedResidual G x y)).card = (activeVertices G).card ∧
    (dkRetainedResidual G x y).edgeFinset.card + 4 = G.edgeFinset.card ∧
    edgeExcess (dkRetainedResidual G x y) + 8 = edgeExcess G ∧
    ((evenNeighbors G x).erase y).card = 3 ∧
    evenNeighborCount (dkRetainedFirstStar G x y) y = 1 ∧
    (∀ v, G.Adj x v → v ≠ y → Odd ((dkRetainedFirstStar G x y).degree v)) ∧
    (∀ v, G.Adj y v → Odd ((dkRetainedResidual G x y).degree v)) ∧
    (dkRetainedResidual G x y).Adj x y ∧
    ∃ z : V, evenNeighbors (dkRetainedFirstStar G x y) y = {z} ∧
      G.Adj y z ∧ z ≠ x ∧ z ≠ y ∧ Even (G.degree z) ∧ z ∉ evenNeighbors G x := by
  have h := dkRetained_accounting G hxy hx4 hy4 ht2
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2,
    (dkRetained_first_sizes G hxy hx4).1,dkRetained_count_right G hxy hx4 hy4 ht2,
    fun _ => dkRetained_original_neighbors_x_odd G,
    fun _ => dkRetained_original_neighbors_y_odd G hxy.1,
    (dkRetained_edge_survives G hxy hx4).2,dkRetained_unique_edge G hxy hx4 hy4 ht2⟩

end Erdos583
end
end Source47_Erdos583_DKRetainedStar
/- END Erdos583.DKRetainedStar -/

/- BEGIN Erdos583.DKRetainedRestore; source SHA256 1a343cfee522c107eae0fb900c997e6b34743486f1cfd8a01c242f401ef9b746 -/
section Source48_Erdos583_DKRetainedRestore





/-! Restore the actual retained-edge (4,4,t=2) reduction from ANY supplied
residual partition. No global path bound or endpoint premise is assumed. -/

noncomputable section
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

/-- A singleton even-neighbor deletion restores without a path-count increase
and supplies an actual path endpoint at the center. -/
theorem restore_single_even_neighbor_with_endpoint (G : SimpleGraph V) (x z : V)
    (hzset : evenNeighbors G x = {z}) {q : ℕ}
    (hq : HasPathPartition (starDeleteEven G x) q) :
    ∃ P : Finset G.Subgraph,
      (∀ H ∈ P, IsNonemptyPathSubgraph H) ∧ IsDecomposition G P ∧
      P.card ≤ q ∧ ∃ H ∈ P, PathStartsAt H x := by
  let J := starDeleteEven G x
  let hJG : J ≤ G := starDeleteEven_le G x
  obtain ⟨D,hpath,hdec,hcard⟩ := hq
  let E := D.image (liftSubgraph hJG)
  have hEpath : ∀ H ∈ E, IsNonemptyPathSubgraph H := by
    intro H hH
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hH
    exact (hpath P hP).lift hJG
  have hEdis : Set.PairwiseDisjoint (E : Set G.Subgraph) Subgraph.edgeSet := by
    intro H hH K hK hne
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hK
    exact hdec.1 hP hQ (fun he => hne (he ▸ rfl))
  have hEcover : (⋃ H : E, H.val.edgeSet) = J.edgeSet := by
    rw [← hdec.2]
    ext e
    simp [E]
    rfl
  have hz : z ∈ evenNeighbors G x := by rw [hzset]; simp
  have hmissing : ∀ H ∈ E, ¬ H.Adj x z := by
    intro H hH hadj
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hH
    have hjadj : J.Adj x z := P.adj_sub hadj
    exact hjadj.2.1 ⟨rfl,(mem_evenNeighbors G x z).mp hz |>.2⟩
  have hend : ∀ v, G.Adj x v → ∃ H ∈ E, PathStartsAt H v := by
    intro v hv
    obtain ⟨P,hP,hpend⟩ := exists_pathStartsAt_of_odd D hpath hdec v
      (original_neighbor_odd_after_starDeleteEven G x v hv)
    exact ⟨liftSubgraph hJG P,Finset.mem_image.mpr ⟨P,hP,rfl⟩,hpend.lift hJG⟩
  have hcover : (⋃ H : E, H.val.edgeSet) ∪ {s(x,z)} = G.edgeSet := by
    rw [hEcover]
    have h := starDeleteEven_edge_cover G x
    rw [hzset] at h
    simpa using h
  obtain ⟨P,hP,hD,hC,hendx⟩ := restore_one_edge_from_endpoint_partition E x z
    hEpath hEdis ((mem_evenNeighbors G x z).mp hz).1 hmissing hcover hend
  exact ⟨P,hP,hD,hC.trans (Finset.card_image_le.trans hcard),hendx⟩

/-- Actual R1 followed by the actual three-edge partial star. The y endpoint
is constructed from the arbitrary input partition before the second step. -/
theorem dkRetained_restore_mixed (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) (hx4 : (evenCore G).degree x = 4)
    (hy4 : (evenCore G).degree y = 4) (ht2 : (originalEvenCommonNeighbors G x y).card = 2)
    {q : ℕ} (hq : HasPathPartition (dkRetainedResidual G x y) q) :
    ∃ r : ℕ, r ≤ 1 ∧ HasMixedPartitionAt G x q r := by
  let H := dkRetainedFirstStar G x y
  let S := (evenNeighbors G x).erase y
  have hSG : S ⊆ evenNeighbors G x := Finset.erase_subset y _
  let hHG : H ≤ G := dkPartialStar_le G x S
  obtain ⟨z,hzset,_⟩ := dkRetained_unique_edge G hxy hx4 hy4 ht2
  obtain ⟨P,hpath,hdec,hcard,Py,hPy,hyend⟩ :=
    restore_single_even_neighbor_with_endpoint H y z hzset hq
  let E := P.image (liftSubgraph hHG)
  have hEpath : ∀ K ∈ E, IsNonemptyPathSubgraph K := by
    intro K hK
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hK
    exact (hpath Q hQ).lift hHG
  have hEdis : Set.PairwiseDisjoint (E : Set G.Subgraph) Subgraph.edgeSet := by
    intro K hK L hL hne
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hL
    exact hdec.1 hQ hR (fun he => hne (he ▸ rfl))
  have hEcover : (⋃ K : E, K.val.edgeSet) = H.edgeSet := by
    rw [← hdec.2]
    ext e
    simp [E]
  have hmissing : ∀ v ∈ S, ∀ K ∈ E, ¬ K.Adj x v := by
    intro v hv K hK hAdj
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hK
    exact dkPartialStar_missing G x S hv (Q.adj_sub hAdj)
  have hend : ∀ v, G.Adj x v → ∃ K ∈ E, PathStartsAt K v := by
    intro v hv
    by_cases hvy : v = y
    · subst v
      exact ⟨liftSubgraph hHG Py,Finset.mem_image.mpr ⟨Py,hPy,rfl⟩,hyend.lift hHG⟩
    · have ho : Odd (H.degree v) := dkRetained_original_neighbors_x_odd G hv hvy
      obtain ⟨Q,hQ,hendQ⟩ := exists_pathStartsAt_of_odd P hpath hdec v ho
      exact ⟨liftSubgraph hHG Q,Finset.mem_image.mpr ⟨Q,hQ,rfl⟩,hendQ.lift hHG⟩
  have hcover : (⋃ K : E, K.val.edgeSet) ∪ (fun v => s(x,v)) '' (S : Set V) = G.edgeSet := by
    rw [hEcover]
    have hi : (fun v => s(x,v)) '' (S : Set V) = {e | ∃ z ∈ S, e = s(x,z)} := by
      ext e
      simp [eq_comm]
    rw [hi]
    exact (dkPartialStar_edge_cover G x S hSG).symm
  have hs : S.card = 3 := (dkRetained_first_sizes G hxy hx4).1
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨r,hr,hmix⟩ := restore_star_from_endpoint_partition E x S hEpath hEdis hSne
    (fun v hv => (mem_evenNeighbors G x v).mp (hSG hv) |>.1) hmissing hcover hend
  refine ⟨r,by omega,hmix.mono_parts ?_⟩
  exact Finset.card_image_le.trans hcard

/-- Every actual residual q-path partition restores to at most q+1 paths in
G, with no prescribed endpoint in the input partition. -/
theorem dkRetained_restore_partition (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) (hx4 : (evenCore G).degree x = 4)
    (hy4 : (evenCore G).degree y = 4) (ht2 : (originalEvenCommonNeighbors G x y).card = 2)
    {q : ℕ} (hq : HasPathPartition (dkRetainedResidual G x y) q) :
    HasPathPartition G (q+1) := by
  obtain ⟨r,hr,hmix⟩ := dkRetained_restore_mixed G hxy hx4 hy4 ht2 hq
  exact hmix.toPathPartition_four.mono (by omega)

/-- Conditional only on the supplied ACTUAL residual bound. This is a local
induction step and does not assume a baseline theorem. -/
theorem dkRetained_restore_bound (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) (hx4 : (evenCore G).degree x = 4)
    (hy4 : (evenCore G).degree y = 4) (ht2 : (originalEvenCommonNeighbors G x y).card = 2)
    (hJ : HasPathBound (dkRetainedResidual G x y) (phi (dkRetainedResidual G x y))) :
    HasPathBound G (phi G) := by
  obtain ⟨q,hq,hb⟩ := hasPathBound_iff_exists_partition.mp hJ
  refine hasPathBound_iff_exists_partition.mpr
    ⟨q+1,dkRetained_restore_partition G hxy hx4 hy4 ht2 hq,?_⟩
  have hp := (dkRetained_accounting G hxy hx4 hy4 ht2).1
  push_cast
  linarith

/-- The local step preserves any rational deficit supplied by the actual
residual partition bound. No positivity restriction on the deficit is needed. -/
theorem restore_dkRetained_phi_bound (G : SimpleGraph V) {x y : V}
    (hxy : (evenCore G).Adj x y) (hx4 : (evenCore G).degree x = 4)
    (hy4 : (evenCore G).degree y = 4) (ht2 : (originalEvenCommonNeighbors G x y).card = 2)
    {b : ℚ}
    (hJ : HasPathBound (dkRetainedResidual G x y) (phi (dkRetainedResidual G x y) - b)) :
    HasPathBound G (phi G - b) := by
  obtain ⟨q,hq,hb⟩ := hasPathBound_iff_exists_partition.mp hJ
  refine hasPathBound_iff_exists_partition.mpr
    ⟨q+1,dkRetained_restore_partition G hxy hx4 hy4 ht2 hq,?_⟩
  have hp := (dkRetained_accounting G hxy hx4 hy4 ht2).1
  push_cast
  linarith

end Erdos583
end
end Source48_Erdos583_DKRetainedRestore
/- END Erdos583.DKRetainedRestore -/

/- BEGIN Erdos583.Baseline; source SHA256 78bfb0b4f75f7d4290f793527b8d33e005466d2510792b8bd5d71584310d9d51 -/
section Source49_Erdos583_Baseline




/-! The full rational Dean--Kouider baseline, derived by actual smaller-graph
induction. No path decomposition theorem appears as a hypothesis. -/
noncomputable section
universe u
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type u} [Fintype V]

theorem minimal_phi_not_first_configuration (G : SimpleGraph V)
    (ih : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W),
      edgeExcess H < edgeExcess G → HasPathBound H (phi H))
    (hbad : ¬ HasPathBound G (phi G)) {x y : V}
    (hxy : (evenCore G).Adj x y) (hc : DKFirstConfiguration G x y) : False := by
  have hmeasure := dkFirstConfiguration_excess_drop G hxy hc
  have hlt : edgeExcess (dkTwoStarResidual G x y) < edgeExcess G := by omega
  have hJ := ih V (dkTwoStarResidual G x y) hlt
  have hG := restore_dkFirstConfiguration_phi_bound G hxy hc
    (b := 0) (by simpa using hJ)
  exact hbad (by simpa using hG)

theorem minimal_phi_not_retained_configuration (G : SimpleGraph V)
    (ih : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W),
      edgeExcess H < edgeExcess G → HasPathBound H (phi H))
    (hbad : ¬ HasPathBound G (phi G)) {x y : V}
    (hxy : (evenCore G).Adj x y) (hx4 : (evenCore G).degree x = 4)
    (hy4 : (evenCore G).degree y = 4)
    (ht2 : (originalEvenCommonNeighbors G x y).card = 2) : False := by
  have hmeasure := (dkRetained_accounting G hxy hx4 hy4 ht2).2.2.2.2.2
  have hlt : edgeExcess (dkRetainedResidual G x y) < edgeExcess G := by omega
  have hJ := ih V (dkRetainedResidual G x y) hlt
  have hG := restore_dkRetained_phi_bound G hxy hx4 hy4 ht2
    (b := 0) (by simpa using hJ)
  exact hbad (by simpa using hG)

theorem minimal_phi_core_terminal (G : SimpleGraph V)
    (ih : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W),
      edgeExcess H < edgeExcess G → HasPathBound H (phi H))
    (hbad : ¬ HasPathBound G (phi G)) : DKTerminal (evenCore G) := by
  classical
  have hdeg := minimal_phi_core_degree G ih hbad
  have hn (x y : V) (hxy : (evenCore G).Adj x y) :
      (evenCore G).degree x ≠ 0 ∧ (evenCore G).degree y ≠ 0 :=
    ⟨Nat.ne_of_gt hxy.degree_pos_left,Nat.ne_of_gt hxy.degree_pos_right⟩
  have hcommon (x y : V) (hxy : (evenCore G).Adj x y) :
      commonNeighborFinset (evenCore G) x y = originalEvenCommonNeighbors G x y :=
    evenCore_commonNeighbors G x y hxy.2.1 hxy.2.2
  have hnot : ∀ {x y : V}, (evenCore G).Adj x y → DKFirstConfiguration G x y → False :=
    fun hxy hc => minimal_phi_not_first_configuration G ih hbad hxy hc
  refine ⟨hdeg,?_,?_,?_⟩
  · intro x y hxy
    by_contra h
    have ht : (originalEvenCommonNeighbors G x y).card = 0 := by
      rw [← hcommon x y hxy]
      omega
    exact hnot hxy ⟨hdeg x (hn x y hxy).1,hdeg y (hn x y hxy).2,Or.inl ht⟩
  · intro x y hxy ht
    have ht' : (originalEvenCommonNeighbors G x y).card = 1 := by
      rwa [← hcommon x y hxy]
    have hx := hdeg x (hn x y hxy).1
    have hy := hdeg y (hn x y hxy).2
    constructor
    · by_contra hnx
      have hx4 : (evenCore G).degree x = 4 := by omega
      have hswap : (originalEvenCommonNeighbors G y x).card = 1 := by
        simpa only [originalEvenCommonNeighbors,Finset.inter_comm] using ht'
      exact hnot hxy.symm ⟨hy,hx,Or.inr ⟨hswap,hx4⟩⟩
    · by_contra hny
      have hy4 : (evenCore G).degree y = 4 := by omega
      exact hnot hxy ⟨hx,hy,Or.inr ⟨ht',hy4⟩⟩
  · intro x y hxy ht hboth
    have ht' : (originalEvenCommonNeighbors G x y).card = 2 := by
      rwa [← hcommon x y hxy]
    exact minimal_phi_not_retained_configuration G ih hbad hxy hboth.1 hboth.2 ht'

/-- Every finite simple graph has an original-edge partition into at most
u/2+2e/3 nonempty vertex-simple paths, with positive-even count e. Isolates
are allowed and contribute no potential. -/
theorem hasPathBound_phi (G : SimpleGraph V) : HasPathBound G (phi G) := by
  classical
  have aux : ∀ m : ℕ, ∀ (W : Type u) [Fintype W] (H : SimpleGraph W),
      edgeExcess H = m → HasPathBound H (phi H) := by
    intro m
    refine Nat.strong_induction_on m ?_
    intro m ih W inst H hm
    have hind : ∀ (T : Type u) [Fintype T] (J : SimpleGraph T),
        edgeExcess J < edgeExcess H → HasPathBound J (phi J) := by
      intro T instT J hlt
      exact ih (edgeExcess J) (by omega) T J rfl
    by_contra hbad
    exact minimal_phi_not_terminal H hind hbad (minimal_phi_core_terminal H hind hbad)
  exact aux (edgeExcess G) V G rfl

end Erdos583
end
end Source49_Erdos583_Baseline
/- END Erdos583.Baseline -/

/- BEGIN Erdos583.PairFamily; source SHA256 69df0d83e258c4bc03530a47b8d4552899b789e0233222ee14e07ca4d415cada -/
section Source50_Erdos583_PairFamily


/-! Simultaneous restoration of degree-two pairs with disjoint original closed
supports. The published residual path bound remains an explicit input only. -/

noncomputable section
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

def pairFamilyVertices (Q : Finset (Sym2 V)) : Finset V := Q.biUnion Sym2.toFinset

omit [Fintype V] in
@[simp] theorem mem_pairFamilyVertices (Q : Finset (Sym2 V)) (v : V) :
    v ∈ pairFamilyVertices Q ↔ ∃ e ∈ Q, v ∈ e := by
  simp [pairFamilyVertices, Sym2.mem_toFinset]

theorem endpoint_mem_pairClosedSet (G : SimpleGraph V) {e : Sym2 V} {v : V}
    (hv : v ∈ e) : v ∈ pairClosedSet G e :=
  (mem_pairClosedSet G e v).mpr ⟨v, hv, Or.inl rfl⟩

theorem neighbor_endpoint_mem_pairClosedSet (G : SimpleGraph V) {e : Sym2 V} {v w : V}
    (hw : w ∈ e) (hvw : G.Adj v w) : v ∈ pairClosedSet G e :=
  (mem_pairClosedSet G e v).mpr ⟨w, hw, Or.inr hvw.symm⟩

theorem pair_support_away_family (G : SimpleGraph V) (e : Sym2 V)
    (Q : Finset (Sym2 V))
    (hdis : ∀ f ∈ Q, Disjoint (pairClosedSet G e) (pairClosedSet G f))
    {v : V} (hv : v ∈ pairClosedSet G e) :
    v ∉ pairFamilyVertices Q ∧ ∀ w ∈ pairFamilyVertices Q, ¬G.Adj v w := by
  constructor
  · intro h
    obtain ⟨f, hf, hvf⟩ := (mem_pairFamilyVertices Q v).mp h
    exact Finset.disjoint_left.mp (hdis f hf) hv (endpoint_mem_pairClosedSet G hvf)
  · intro w hw hadj
    obtain ⟨f, hf, hwf⟩ := (mem_pairFamilyVertices Q w).mp hw
    exact Finset.disjoint_left.mp (hdis f hf) hv
      (neighbor_endpoint_mem_pairClosedSet G hwf hadj)

theorem pair_support_degree_unchanged (G : SimpleGraph V) (e : Sym2 V)
    (Q : Finset (Sym2 V))
    (hdis : ∀ f ∈ Q, Disjoint (pairClosedSet G e) (pairClosedSet G f))
    {v : V} (hv : v ∈ pairClosedSet G e) :
    (isolateVertices G (pairFamilyVertices Q)).degree v = G.degree v := by
  obtain ⟨hn, ha⟩ := pair_support_away_family G e Q hdis hv
  exact isolateVertices_degree_unchanged G _ v hn ha

omit [Fintype V] in
theorem isolateVertices_pairFamily_insert (G : SimpleGraph V) (Q : Finset (Sym2 V))
    (x y : V) :
    isolateVertices G (pairFamilyVertices (insert s(x,y) Q)) =
      isolatePair (isolateVertices G (pairFamilyVertices Q)) x y := by
  ext u v
  simp only [isolateVertices_adj, isolatePair_adj, pairFamilyVertices,
    Finset.biUnion_insert, Sym2.toFinset_mk_eq, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- Other selected pairs cannot alter any degree in this pair's original
closed support, including the common root of a pendant triangle. -/
theorem restore_pair_after_other_pairs (G : SimpleGraph V) (Q : Finset (Sym2 V))
    {x y : V} (hx : x ∈ coreDegreeTwoVertices G) (hy : y ∈ coreDegreeTwoVertices G)
    (hxy : G.Adj x y)
    (hdis : ∀ f ∈ Q, Disjoint (pairClosedSet G s(x,y)) (pairClosedSet G f))
    {q : ℕ} (hq : HasPathPartition
      (isolateVertices G (pairFamilyVertices (insert s(x,y) Q))) q) :
    HasPathPartition (isolateVertices G (pairFamilyVertices Q)) (q + 1) := by
  let H := isolateVertices G (pairFamilyVertices Q)
  have hx2 := coreDegreeTwoVertices_degree G x hx
  have hy2 := coreDegreeTwoVertices_degree G y hy
  obtain ⟨a, hxa, hay⟩ := degree_two_other_neighbor G hxy hx2
  obtain ⟨b, hyb, hbx⟩ := degree_two_other_neighbor G hxy.symm hy2
  have hxs : x ∈ pairClosedSet G s(x,y) := endpoint_mem_pairClosedSet G (by simp)
  have hys : y ∈ pairClosedSet G s(x,y) := endpoint_mem_pairClosedSet G (by simp)
  have has : a ∈ pairClosedSet G s(x,y) :=
    neighbor_endpoint_mem_pairClosedSet G (by simp : x ∈ s(x,y)) hxa.symm
  have hbs : b ∈ pairClosedSet G s(x,y) :=
    neighbor_endpoint_mem_pairClosedSet G (by simp : y ∈ s(x,y)) hyb.symm
  have hadj {u v : V} (hu : u ∈ pairClosedSet G s(x,y))
      (hv : v ∈ pairClosedSet G s(x,y)) (huv : G.Adj u v) : H.Adj u v :=
    ⟨huv, (pair_support_away_family G _ Q hdis hu).1,
      (pair_support_away_family G _ Q hdis hv).1⟩
  apply restore_degree_two_pair H (hadj has hxs hxa.symm) (hadj hxs hys hxy)
    (hadj hys hbs hyb) hay hbx.symm
  · rw [pair_support_degree_unchanged G _ Q hdis hxs]; exact hx2
  · rw [pair_support_degree_unchanged G _ Q hdis hys]; exact hy2
  · intro hab
    rw [pair_support_degree_unchanged G _ Q hdis has]
    subst b
    exact coreDegreeTwo_common_neighbor_degree_ge_four G hx hy hxy hyb hxa.symm
  · simpa only [isolateVertices_pairFamily_insert] using hq

/-- Every supplied partition of the simultaneous residual lifts at cost at
most one path per selected pair. -/
theorem restore_pair_family (G : SimpleGraph V) (Q : Finset (Sym2 V))
    (hQ : Q ⊆ degreeTwoPairs G (coreDegreeTwoVertices G))
    (hdis : (Q : Set (Sym2 V)).Pairwise
      (fun e f => Disjoint (pairClosedSet G e) (pairClosedSet G f)))
    {q : ℕ} (hq : HasPathPartition (isolateVertices G (pairFamilyVertices Q)) q) :
    HasPathPartition G (q + Q.card) := by
  induction Q using Finset.induction_on generalizing q with
  | empty =>
    have heq : isolateVertices G (pairFamilyVertices ∅) = G := by
      ext u v
      simp [isolateVertices_adj, pairFamilyVertices]
    simpa only [heq, Finset.card_empty, add_zero] using hq
  | @insert e Q he ih =>
    have hQ' : Q ⊆ degreeTwoPairs G (coreDegreeTwoVertices G) :=
      fun f hf => hQ (Finset.mem_insert_of_mem hf)
    have hdis' : (Q : Set (Sym2 V)).Pairwise
        (fun e f => Disjoint (pairClosedSet G e) (pairClosedSet G f)) := by
      intro f hf g hg hfg
      exact hdis (Finset.mem_insert_of_mem hf) (Finset.mem_insert_of_mem hg) hfg
    have heQ : e ∈ degreeTwoPairs G (coreDegreeTwoVertices G) := hQ (by simp)
    have hed : ∀ f ∈ Q, Disjoint (pairClosedSet G e) (pairClosedSet G f) := by
      intro f hf
      exact hdis (by simp) (Finset.mem_insert_of_mem hf) (by intro h; subst f; exact he hf)
    have hstep : HasPathPartition (isolateVertices G (pairFamilyVertices Q)) (q+1) := by
      induction e using Sym2.ind with
      | _ x y =>
        obtain ⟨heG, hend⟩ := (mem_degreeTwoPairs G _ s(x,y)).mp heQ
        have hxy : G.Adj x y := by simpa using heG
        exact restore_pair_after_other_pairs G Q (hend x (by simp)) (hend y (by simp)) hxy hed hq
    have hr := ih hQ' hdis' hstep
    simpa only [Finset.card_insert_of_notMem he, Nat.add_assoc, Nat.add_comm 1 Q.card] using hr


theorem pairFamilyVertices_card (G : SimpleGraph V) (Q : Finset (Sym2 V))
    (hQ : Q ⊆ G.edgeFinset)
    (hdis : (Q : Set (Sym2 V)).Pairwise
      (fun e f => Disjoint (pairClosedSet G e) (pairClosedSet G f))) :
    (pairFamilyVertices Q).card = 2 * Q.card := by
  have hd : (Q : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset := by
    intro e he f hf hef
    apply Finset.disjoint_left.mpr
    intro v hve hvf
    exact Finset.disjoint_left.mp (hdis he hf hef)
      (endpoint_mem_pairClosedSet G (Sym2.mem_toFinset.mp hve))
      (endpoint_mem_pairClosedSet G (Sym2.mem_toFinset.mp hvf))
  have hc : ∀ e ∈ Q, e.toFinset.card = 2 := by
    intro e he
    have heG := hQ he
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : G.Adj x y := by simpa using heG
      simp [Sym2.toFinset_mk_eq, hxy.ne]
  rw [pairFamilyVertices, Finset.card_biUnion hd]
  simp only [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul]
  omega

theorem pairFamilyVertices_clean (G : SimpleGraph V) (Q : Finset (Sym2 V))
    (hQ : Q ⊆ degreeTwoPairs G (coreDegreeTwoVertices G)) :
    pairFamilyVertices Q ⊆ cleanDegreeTwoVertices G := by
  intro v hv
  obtain ⟨e, he, hve⟩ := (mem_pairFamilyVertices Q v).mp hv
  have hvB := ((mem_degreeTwoPairs G _ e).mp (hQ he)).2 v hve
  exact (Finset.mem_sdiff.mp hvB).1

theorem phi_pair_family_drop (G : SimpleGraph V) (Q : Finset (Sym2 V))
    (hQ : Q ⊆ degreeTwoPairs G (coreDegreeTwoVertices G))
    (hdis : (Q : Set (Sym2 V)).Pairwise
      (fun e f => Disjoint (pairClosedSet G e) (pairClosedSet G f))) :
    (4 / 3 : ℚ) * Q.card ≤ phi G - phi (isolateVertices G (pairFamilyVertices Q)) := by
  have hc := pairFamilyVertices_card G Q
    (fun e he => ((mem_degreeTwoPairs G _ e).mp (hQ he)).1) hdis
  have hp := phi_isolateVertices_drop G _ (pairFamilyVertices_clean G Q hQ)
  rw [hc] at hp
  push_cast at hp
  linarith

/-- Actual simultaneous pair reduction, with no residual baseline premise. -/
theorem pair_family_lift (G : SimpleGraph V) (Q : Finset (Sym2 V))
    (hQ : Q ⊆ degreeTwoPairs G (coreDegreeTwoVertices G))
    (hdis : (Q : Set (Sym2 V)).Pairwise
      (fun e f => Disjoint (pairClosedSet G e) (pairClosedSet G f))) :
    (pairFamilyVertices Q).card = 2 * Q.card ∧
    (4 / 3 : ℚ) * Q.card ≤ phi G - phi (isolateVertices G (pairFamilyVertices Q)) ∧
    ∀ q, HasPathPartition (isolateVertices G (pairFamilyVertices Q)) q →
      HasPathPartition G (q + Q.card) :=
  ⟨pairFamilyVertices_card G Q
    (fun e he => ((mem_degreeTwoPairs G _ e).mp (hQ he)).1) hdis,
   phi_pair_family_drop G Q hQ hdis, fun _ => restore_pair_family G Q hQ hdis⟩

/-- The saving is conditional only on a genuine path bound for the actual
residual graph, not a scalar saving hypothesis. -/
theorem pair_family_saving_of_residual_bound (G : SimpleGraph V) (Q : Finset (Sym2 V))
    (hQ : Q ⊆ degreeTwoPairs G (coreDegreeTwoVertices G))
    (hdis : (Q : Set (Sym2 V)).Pairwise
      (fun e f => Disjoint (pairClosedSet G e) (pairClosedSet G f)))
    (hbase : HasPathBound (isolateVertices G (pairFamilyVertices Q))
      (phi (isolateVertices G (pairFamilyVertices Q)))) :
    HasPathBound G (phi G - (Q.card : ℚ) / 3) := by
  obtain ⟨q, hq, hqb⟩ := hasPathBound_iff_exists_partition.mp hbase
  apply hasPathBound_iff_exists_partition.mpr
  refine ⟨q + Q.card, restore_pair_family G Q hQ hdis hq, ?_⟩
  have hp := phi_pair_family_drop G Q hQ hdis
  push_cast
  linarith

/-- The actual bounded-core packing produces a simultaneous reduction with
all graph, cardinality, potential, and arbitrary-partition lifting clauses. -/
theorem exists_bounded_core_pair_reduction (G : SimpleGraph V) (K : ℕ)
    (hcap : ∀ v, evenNeighborCount G v ≤ K) :
    ∃ Q ⊆ degreeTwoPairs G (coreDegreeTwoVertices G),
      (Q : Set (Sym2 V)).Pairwise
        (fun e f => Disjoint (pairClosedSet G e) (pairClosedSet G f)) ∧
      (degreeTwoPairs G (coreDegreeTwoVertices G)).card ≤ (4 * (K+2)) * Q.card ∧
      (pairFamilyVertices Q).card = 2 * Q.card ∧
      (4 / 3 : ℚ) * Q.card ≤ phi G - phi (isolateVertices G (pairFamilyVertices Q)) ∧
      ∀ q, HasPathPartition (isolateVertices G (pairFamilyVertices Q)) q →
        HasPathPartition G (q + Q.card) := by
  obtain ⟨Q, hQ, hd, hc⟩ := exists_degreeTwoPairs_packing G (coreDegreeTwoVertices G)
    (fun v hv => coreDegreeTwoVertices_degree G v hv) K hcap
  exact ⟨Q, hQ, hd, hc, pair_family_lift G Q hQ hd⟩

end Erdos583
end
end Source50_Erdos583_PairFamily
/- END Erdos583.PairFamily -/

/- BEGIN Erdos583.CoreBoundFour; source SHA256 5c67929e30491b31656a3d1fe0cbf12aa56cf204b5d56cedf33329459d7edff2 -/
section Source51_Erdos583_CoreBoundFour



/-! The actual bounded-core partition, conditional on the explicitly supplied
rational baseline for its actual residual graphs. -/
noncomputable section
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

theorem bounded_core_four_bound (G : SimpleGraph V)
    (hbase : ∀ H : SimpleGraph V, HasPathBound H (phi H))
    (hcap : ∀ v, evenNeighborCount G v ≤ 47) :
    HasPathBound G (phi G -
      ((nonisolatedEvenVertices G).card - 3*(triangleComponents G).card -
        (2303/2 : ℚ)*(oddVertices G).card)/163611) := by
  classical
  obtain ⟨R,hR,hdis,hpack⟩ := exists_highEvenCenters_packing G 47 hcap
  have hstar := restore_starFamily_phi_bound_four G R hR hdis
    (b := 0) (by simpa using hbase (starFamilyDelete G R))
  have hstarPN := hasPathBound_iff_pn_le.mp hstar
  obtain ⟨Q,hQ,hdisQ,hpackQ⟩ := exists_degreeTwoPairs_packing G
    (coreDegreeTwoVertices G) (fun v hv => coreDegreeTwoVertices_degree G v hv) 47 hcap
  have hpair := pair_family_saving_of_residual_bound G Q hQ hdisQ
    (hbase (isolateVertices G (pairFamilyVertices Q)))
  have hpairPN := hasPathBound_iff_pn_le.mp hpair
  have hbad := badEvenVertices_card_le G 47 hcap
  have hcount := core_degreeTwoPairs_lower_bound_integral G 47 hcap
  norm_num at hpack hpackQ hbad hcount
  have hs : ((highEvenCenters G).card : ℚ) ≤ 2210 * R.card := by exact_mod_cast hpack
  have hp : ((degreeTwoPairs G (coreDegreeTwoVertices G)).card : ℚ) ≤ 196 * Q.card := by
    exact_mod_cast hpackQ
  have hb : ((badEvenVertices G).card : ℚ) ≤ 47*(oddVertices G).card := by exact_mod_cast hbad
  have hc : (2 : ℚ)*(nonisolatedEvenVertices G).card ≤
      4*(degreeTwoPairs G (coreDegreeTwoVertices G)).card +
      49*((highEvenCenters G).card+(badEvenVertices G).card) +
      6*(triangleComponents G).card := by exact_mod_cast hcount
  apply hasPathBound_iff_pn_le.mpr
  linarith

end Erdos583
end
end Source51_Erdos583_CoreBoundFour
/- END Erdos583.CoreBoundFour -/

/- BEGIN Erdos583.Peeling; source SHA256 9488a3a2ab718e0f897ebf8571a26da41ade27df14a4fbc7ef87c23d848d94d3 -/
section Source52_Erdos583_Peeling


/-! A finite certificate of actual star deletions. Path reconstruction is
proved separately from the certificate. -/

noncomputable section

namespace Erdos583

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

/-- Every step deletes all even-neighbor edges at a center with at least 24 of
them. The last parameter is the actual total number of edges deleted. -/
inductive PeelTrace : SimpleGraph V → SimpleGraph V → ℕ → Prop
  | nil (G : SimpleGraph V) : PeelTrace G G 0
  | cons (G : SimpleGraph V) (x : V) (H : SimpleGraph V) (T : ℕ)
      (hk : 24 ≤ evenNeighborCount G x)
      (tail : PeelTrace (starDeleteEven G x) H T) :
      PeelTrace G H (evenNeighborCount G x + T)

def IsPeeled (G : SimpleGraph V) : Prop := ∀ x, evenNeighborCount G x < 24

/-- The construction terminates by strict decrease of the finite edge set. -/
theorem exists_peelTrace (G : SimpleGraph V) :
    ∃ H T, PeelTrace G H T ∧ IsPeeled H := by
  classical
  have aux : ∀ m : ℕ, ∀ G : SimpleGraph V, G.edgeFinset.card = m →
      ∃ H T, PeelTrace G H T ∧ IsPeeled H := by
    intro m
    refine Nat.strong_induction_on m ?_
    intro m ih G hm
    by_cases hdone : IsPeeled G
    · exact ⟨G, 0, PeelTrace.nil G, hdone⟩
    · have hex : ∃ x, 24 ≤ evenNeighborCount G x := by
        simpa only [IsPeeled, not_forall, not_lt] using hdone
      obtain ⟨x, hx⟩ := hex
      have hlt := edge_count_starDeleteEven_lt G x (by omega)
      obtain ⟨H, T, ht, hend⟩ :=
        ih (starDeleteEven G x).edgeFinset.card (by omega) (starDeleteEven G x) rfl
      exact ⟨H, evenNeighborCount G x + T, PeelTrace.cons G x H T hx ht, hend⟩
  exact aux G.edgeFinset.card G rfl

theorem PeelTrace.subgraph {G H : SimpleGraph V} {T : ℕ} (h : PeelTrace G H T) : H ≤ G := by
  induction h with
  | nil => exact le_rfl
  | cons G x H T hk ht ih => exact le_trans ih (starDeleteEven_le G x)

theorem PeelTrace.edge_count {G H : SimpleGraph V} {T : ℕ} (h : PeelTrace G H T) :
    H.edgeFinset.card + T = G.edgeFinset.card := by
  induction h with
  | nil => simp
  | cons G x H T hk ht ih =>
    have hs := edge_count_starDeleteEven G x
    omega

theorem PeelTrace.odd_growth {G H : SimpleGraph V} {T : ℕ} (h : PeelTrace G H T) :
    24 * (oddVertices H).card ≤ 24 * (oddVertices G).card + 25 * T := by
  induction h with
  | nil => simp
  | cons G x H T hk ht ih =>
    have hs := odd_count_starDeleteEven_scaled G x hk
    omega

theorem PeelTrace.isolate_growth {G H : SimpleGraph V} {T : ℕ} (h : PeelTrace G H T) :
    24 * (isolatedVertices H).card ≤ 24 * (isolatedVertices G).card + T := by
  induction h with
  | nil => simp
  | cons G x H T hk ht ih =>
    have hs := isolate_count_starDeleteEven_scaled G x hk
    omega

/-- Actual residual counts from an initially all-even graph without isolates. -/
theorem PeelTrace.eulerian_counts {G H : SimpleGraph V} {T : ℕ}
    (h : PeelTrace G H T) (hodd : (oddVertices G).card = 0)
    (hiso : (isolatedVertices G).card = 0) :
    24 * (oddVertices H).card ≤ 25 * T ∧
    24 * (isolatedVertices H).card ≤ T ∧
    24 * Fintype.card V ≤ 24 * (nonisolatedEvenVertices H).card + 26 * T := by
  have ho := h.odd_growth
  have hi := h.isolate_growth
  have hv := vertex_parity_count H
  simp only [hodd, hiso, mul_zero, zero_add] at ho hi
  constructor
  · exact ho
  constructor
  · exact hi
  · omega

end Erdos583
end
end Source52_Erdos583_Peeling
/- END Erdos583.Peeling -/

/- BEGIN Erdos583.Components; source SHA256 0870d0463788c7811cd9a21f4975fbda65028cc43e16cd60f57fc03573356471 -/
section Source53_Erdos583_Components




/-! Component growth under deleting edges from a connected finite graph. -/

noncomputable section

namespace Erdos583

open SimpleGraph
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

/-- Contract each `H` component, retaining the cross-component edges of `G`. -/
def componentQuotient (G H : SimpleGraph V) : SimpleGraph H.ConnectedComponent where
  Adj C D := C ≠ D ∧ ∃ u v, H.connectedComponentMk u = C ∧
    H.connectedComponentMk v = D ∧ G.Adj u v
  symm := ⟨by
    rintro C D ⟨hne, u, v, hu, hv, hadj⟩
    exact ⟨hne.symm, v, u, hv, hu, hadj.symm⟩⟩
  loopless := ⟨by intro C h; exact h.1 rfl⟩

omit [Fintype V] in
theorem reachable_componentQuotient (G H : SimpleGraph V) {u v : V}
    (h : G.Reachable u v) :
    (componentQuotient G H).Reachable (H.connectedComponentMk u) (H.connectedComponentMk v) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.rfl
  | @cons a b c hadj p ih =>
    by_cases heq : H.connectedComponentMk a = H.connectedComponentMk b
    · simpa only [heq] using ih
    · have hq : (componentQuotient G H).Adj (H.connectedComponentMk a)
          (H.connectedComponentMk b) := ⟨heq, a, b, rfl, rfl, hadj⟩
      exact hq.reachable.trans ih

omit [Fintype V] in
theorem connected_componentQuotient (G H : SimpleGraph V) (hG : G.Connected) :
    (componentQuotient G H).Connected := by
  let : Nonempty V := hG.nonempty
  constructor
  intro C D
  induction C using ConnectedComponent.ind with
  | _ u =>
    induction D using ConnectedComponent.ind with
    | _ v => exact reachable_componentQuotient G H (hG.preconnected u v)

/-- Every quotient edge comes from an original edge missing in `H`. -/
theorem componentQuotient_edges_subset (G H : SimpleGraph V) :
    (componentQuotient G H).edgeFinset ⊆
      (G.edgeFinset \ H.edgeFinset).image (Sym2.map H.connectedComponentMk) := by
  intro e he
  induction e using Sym2.ind with
  | _ C D =>
    have hAdj : (componentQuotient G H).Adj C D :=
      (componentQuotient G H).mem_edgeFinset.mp he
    obtain ⟨hne, u, v, hu, hv, hadj⟩ := hAdj
    have hnot : ¬ H.Adj u v := by
      intro huv
      exact hne (hu.symm.trans ((ConnectedComponent.sound huv.reachable).trans hv))
    refine Finset.mem_image.mpr ⟨s(u, v), ?_, ?_⟩
    · apply Finset.mem_sdiff.mpr
      simpa using (And.intro hadj hnot)
    · simp only [Sym2.map_mk, hu, hv]

/-- Deleting `r` edges can create at most `r+1` components. Ambient isolates
are included in the count. -/
theorem component_count_le_deleted_add_one (G H : SimpleGraph V) (hG : G.Connected) :
    Nat.card H.ConnectedComponent ≤ (G.edgeFinset \ H.edgeFinset).card + 1 := by
  let Q := componentQuotient G H
  have hq := (connected_componentQuotient G H hG).card_vert_le_card_edgeSet_add_one
  have hcard : Q.edgeFinset.card ≤ (G.edgeFinset \ H.edgeFinset).card :=
    (Finset.card_le_card (componentQuotient_edges_subset G H)).trans Finset.card_image_le
  have heq : Nat.card Q.edgeSet = Q.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, Q.edgeFinset_card]
  rw [heq] at hq
  exact hq.trans (Nat.add_le_add_right hcard 1)

/-- The certificate's deleted-edge parameter also pays its actual component
count, including isolated vertices in the residual graph. -/
theorem PeelTrace.component_count {G H : SimpleGraph V} {T : ℕ}
    (h : PeelTrace G H T) (hG : G.Connected) :
    Nat.card H.ConnectedComponent ≤ T + 1 := by
  have hsub : H.edgeFinset ⊆ G.edgeFinset := SimpleGraph.edgeFinset_mono h.subgraph
  have hs := Finset.card_sdiff_add_card_eq_card hsub
  have ht := h.edge_count
  have heq : (G.edgeFinset \ H.edgeFinset).card = T := by omega
  simpa only [heq] using component_count_le_deleted_add_one G H hG

/-- An actual bounded-core reduction with all graph counts needed by the
Eulerian argument. Path restoration and the core path bound remain separate. -/
theorem exists_peeling_certificate (G : SimpleGraph V) (hG : G.Connected)
    (hodd : (oddVertices G).card = 0) (hiso : (isolatedVertices G).card = 0) :
    ∃ H T, PeelTrace G H T ∧
      (∀ x, evenNeighborCount H x ≤ 23) ∧
      Nat.card H.ConnectedComponent ≤ T + 1 ∧
      H.edgeFinset.card + T = G.edgeFinset.card ∧
      24 * (oddVertices H).card ≤ 25 * T ∧
      24 * (isolatedVertices H).card ≤ T ∧
      24 * Fintype.card V ≤ 24 * (nonisolatedEvenVertices H).card + 26 * T := by
  obtain ⟨H, T, ht, hend⟩ := exists_peelTrace G
  obtain ⟨ho, hi, he⟩ := ht.eulerian_counts hodd hiso
  refine ⟨H, T, ht, ?_, ht.component_count hG, ht.edge_count, ho, hi, he⟩
  intro x
  have hx := hend x
  omega

end Erdos583
end
end Source53_Erdos583_Components
/- END Erdos583.Components -/

/- BEGIN Erdos583.PeelingFour; source SHA256 489688757c98bbc01f1b8123b731f78d8b89f9f6bdd2eb8bb03871c9aec80fb2 -/
section Source54_Erdos583_PeelingFour


/-! The cutoff-48 reduction used by the four-cycle repair variant. Earlier
cutoff-24 results are reused through an explicit trace projection. -/

noncomputable section

namespace Erdos583

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

inductive PeelFourTrace : SimpleGraph V → SimpleGraph V → ℕ → Prop
  | nil (G : SimpleGraph V) : PeelFourTrace G G 0
  | cons (G : SimpleGraph V) (x : V) (H : SimpleGraph V) (T : ℕ)
      (hk : 48 ≤ evenNeighborCount G x)
      (tail : PeelFourTrace (starDeleteEven G x) H T) :
      PeelFourTrace G H (evenNeighborCount G x + T)

theorem PeelFourTrace.toPeelTrace {G H : SimpleGraph V} {T : ℕ}
    (h : PeelFourTrace G H T) : PeelTrace G H T := by
  induction h with
  | nil G => exact PeelTrace.nil G
  | cons G x H T hk ht ih => exact PeelTrace.cons G x H T (by omega) ih

theorem exists_peelFourTrace (G : SimpleGraph V) :
    ∃ H T, PeelFourTrace G H T ∧ ∀ x, evenNeighborCount H x ≤ 47 := by
  have aux : ∀ m : ℕ, ∀ G : SimpleGraph V, G.edgeFinset.card = m →
      ∃ H T, PeelFourTrace G H T ∧ ∀ x, evenNeighborCount H x ≤ 47 := by
    intro m
    refine Nat.strong_induction_on m ?_
    intro m ih G hm
    by_cases hend : ∀ x, evenNeighborCount G x ≤ 47
    · exact ⟨G, 0, PeelFourTrace.nil G, hend⟩
    · push Not at hend
      obtain ⟨x, hx⟩ := hend
      have hlt := edge_count_starDeleteEven_lt G x (by omega)
      obtain ⟨H, T, ht, hcap⟩ :=
        ih (starDeleteEven G x).edgeFinset.card (by omega) (starDeleteEven G x) rfl
      exact ⟨H, evenNeighborCount G x + T, PeelFourTrace.cons G x H T (by omega) ht, hcap⟩
  exact aux G.edgeFinset.card G rfl

theorem PeelFourTrace.odd_growth {G H : SimpleGraph V} {T : ℕ}
    (h : PeelFourTrace G H T) :
    48 * (oddVertices H).card ≤ 48 * (oddVertices G).card + 49 * T := by
  induction h with
  | nil => simp
  | cons G x H T hk ht ih =>
    have hs := (odd_count_starDeleteEven_bounds G x).2
    omega

theorem PeelFourTrace.isolate_growth {G H : SimpleGraph V} {T : ℕ}
    (h : PeelFourTrace G H T) :
    48 * (isolatedVertices H).card ≤ 48 * (isolatedVertices G).card + T := by
  induction h with
  | nil => simp
  | cons G x H T hk ht ih =>
    have hs := isolate_count_starDeleteEven_le G x
    omega

theorem PeelFourTrace.eulerian_counts {G H : SimpleGraph V} {T : ℕ}
    (h : PeelFourTrace G H T) (hodd : (oddVertices G).card = 0)
    (hiso : (isolatedVertices G).card = 0) :
    48 * (oddVertices H).card ≤ 49 * T ∧
    48 * (isolatedVertices H).card ≤ T ∧
    48 * Fintype.card V ≤ 48 * (nonisolatedEvenVertices H).card + 50 * T := by
  have ho := h.odd_growth
  have hi := h.isolate_growth
  have hv := vertex_parity_count H
  simp only [hodd, hiso, mul_zero, zero_add] at ho hi
  exact ⟨ho, hi, by omega⟩

theorem exists_four_cycle_peeling_certificate (G : SimpleGraph V) (hG : G.Connected)
    (hodd : (oddVertices G).card = 0) (hiso : (isolatedVertices G).card = 0) :
    ∃ H T, PeelFourTrace G H T ∧
      (∀ x, evenNeighborCount H x ≤ 47) ∧
      Nat.card H.ConnectedComponent ≤ T + 1 ∧
      H.edgeFinset.card + T = G.edgeFinset.card ∧
      48 * (oddVertices H).card ≤ 49 * T ∧
      48 * (isolatedVertices H).card ≤ T ∧
      48 * Fintype.card V ≤ 48 * (nonisolatedEvenVertices H).card + 50 * T := by
  obtain ⟨H, T, ht, hcap⟩ := exists_peelFourTrace G
  obtain ⟨ho, hi, he⟩ := ht.eulerian_counts hodd hiso
  exact ⟨H, T, ht, hcap, ht.toPeelTrace.component_count hG,
    ht.toPeelTrace.edge_count, ho, hi, he⟩

end Erdos583
end
end Source54_Erdos583_PeelingFour
/- END Erdos583.PeelingFour -/

/- BEGIN Erdos583.EulerianBridge; source SHA256 1eec18da73a6f4bff128bb24c74a84ddf93869c37da1850406b48770e1223b6c -/
section Source55_Erdos583_EulerianBridge


/-! Exact graph-level transfer of an Eulerian affine path bound. The Eulerian
and parity bounds are explicit hypotheses of this transfer theorem. -/

noncomputable section

namespace Erdos583

open SimpleGraph
attribute [local instance] Classical.propDecidable

universe u
variable {V : Type u} [Fintype V]

theorem phi_le_vertex_parity_bound (G : SimpleGraph V) :
    phi G ≤ (2 / 3 : ℚ) * Fintype.card V - (oddVertices G).card / 6 := by
  have hV : ((oddVertices G).card : ℚ) + (nonisolatedEvenVertices G).card +
      (isolatedVertices G).card = Fintype.card V := by
    exact_mod_cast vertex_parity_count G
  have hi : (0 : ℚ) ≤ (isolatedVertices G).card := by positivity
  unfold phi
  linarith

/-- This theorem pays the actual hub construction, deletion and original-edge
transport. Its two mathematical bound inputs are intentionally explicit. -/
theorem eulerian_to_general_of_parity_bound (c C : ℚ) (hc : 0 ≤ c)
    (hEuler : ∀ {W : Type u} [Fintype W] (H : SimpleGraph W), H.Connected →
      (∀ v, Even (H.degree v)) → HasPathBound H (c * Fintype.card W + C))
    (G : SimpleGraph V) (hG : G.Connected) (hbase : HasPathBound G (phi G)) :
    HasPathBound G ((1 / 2 + c / 4) * Fintype.card V + (c + C) / 4) := by
  let : Nonempty V := hG.nonempty
  have hA : HasPathBound G
      (c * Fintype.card V + c + C + (oddVertices G).card / 2) := by
    by_cases ho : (oddVertices G).Nonempty
    · have hcomp := hEuler (parityCompletion G)
        (parityCompletion_connected G hG ho) (parityCompletion_even_degree G)
      obtain ⟨q, hq, hqb⟩ := hasPathBound_iff_exists_partition.mp hcomp
      have hdel := parityCompletion_delete_hub G hq
      apply hdel.mono
      rw [Fintype.card_option] at hqb
      push_cast at hqb
      linarith
    · have heven : ∀ v, Even (G.degree v) := by
        intro v
        apply Nat.not_odd_iff_even.mp
        intro hv
        exact ho ⟨v, (mem_oddVertices G v).mpr hv⟩
      have h := hEuler G hG heven
      apply h.mono
      have hu : (0 : ℚ) ≤ (oddVertices G).card := by positivity
      linarith
  have hpA := hasPathBound_iff_pn_le.mp hA
  have hpB := (hasPathBound_iff_pn_le.mp hbase).trans (phi_le_vertex_parity_bound G)
  apply hasPathBound_iff_pn_le.mpr
  linarith

end Erdos583
end
end Source55_Erdos583_EulerianBridge
/- END Erdos583.EulerianBridge -/

/- BEGIN Erdos583.ImprovementFour; source SHA256 d45a2168ef2b16a352b6b64206a43980c5ef231d381299894e0adb60afbb5d5e -/
section Source56_Erdos583_ImprovementFour




/-! Actual graph reconstruction and final coefficients. The classical rational
baseline is an explicit input, supplied by hasPathBound_phi in the final theorem. -/
noncomputable section
universe u
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type u} [Fintype V]

theorem PeelFourTrace.restore_phi_bound {G H : SimpleGraph V} {T : ℕ}
    (ht : PeelFourTrace G H T) {b : ℚ}
    (hbound : HasPathBound H (phi H - b)) :
    HasPathBound G (phi G - b - (T : ℚ)/48) := by
  classical
  induction ht generalizing b with
  | nil => simpa using hbound
  | cons G x H T hk ht ih =>
    have htail := ih hbound
    have htail' : HasPathBound (starDeleteEven G x)
        (phi (starDeleteEven G x) - (b + (T : ℚ)/48)) := by
      convert htail using 1; ring
    have h := restore_largeEvenNeighbor_phi_bound_four G x hk htail'
    convert h using 1
    push_cast
    ring

theorem eulerian_four_of_phi (G : SimpleGraph V) (hG : G.Connected)
    (heven : ∀ v, Even (G.degree v))
    (hbase : ∀ H : SimpleGraph V, HasPathBound H (phi H)) :
    HasPathBound G ((2/3-1/163611 : ℚ)*Fintype.card V + 1/54537) := by
  classical
  rcases subsingleton_or_nontrivial V with hsmall | hbig
  · have := hsmall
    have hbot : G = ⊥ := Subsingleton.elim _ _
    have hpart : HasPathPartition G 0 := by rw [hbot]; exact hasPathPartition_bot
    apply hasPathBound_iff_exists_partition.mpr
    refine ⟨0,hpart,?_⟩
    positivity
  · have := hbig
    have ho : (oddVertices G).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      exact (Nat.not_odd_iff_even.mpr (heven v)) ((mem_oddVertices G v).mp hv)
    have hi : (isolatedVertices G).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      have hp := hG.preconnected.degree_pos_of_nontrivial v
      have hz := (mem_isolatedVertices G v).mp hv
      omega
    obtain ⟨H,T,ht,hcap,hcomp,_,hodd,_,hvertices⟩ :=
      exists_four_cycle_peeling_certificate G hG ho hi
    have hcore := bounded_core_four_bound H hbase hcap
    have hrestore := ht.restore_phi_bound hcore
    have hpn := hasPathBound_iff_pn_le.mp hrestore
    have htri := triangleComponents_card_le_components H
    have htriT : (triangleComponents H).card ≤ T+1 := htri.trans hcomp
    have hoddRat : (48 : ℚ)*(oddVertices H).card ≤ 49*T := by exact_mod_cast hodd
    have hvRat : (48 : ℚ)*Fintype.card V ≤
        48*(nonisolatedEvenVertices H).card + 50*T := by exact_mod_cast hvertices
    have htRat : ((triangleComponents H).card : ℚ) ≤ T+1 := by exact_mod_cast htriT
    have hcount := vertex_parity_count G
    have hecard : (nonisolatedEvenVertices G).card = Fintype.card V := by omega
    have hphi : phi G = (2/3 : ℚ)*Fintype.card V := by
      simp [phi,ho,hecard]
      ring
    rw [hphi] at hpn
    have hT : (0 : ℚ) ≤ T := by positivity
    apply hasPathBound_iff_pn_le.mpr
    linarith

theorem general_four_of_phi
    (hbase : ∀ {W : Type u} [Fintype W] (H : SimpleGraph W), HasPathBound H (phi H))
    (G : SimpleGraph V) (hG : G.Connected) :
    HasPathBound G ((2/3-1/654444 : ℚ)*Fintype.card V + 1/6 + 1/327222) := by
  have h := eulerian_to_general_of_parity_bound (2/3-1/163611) (1/54537)
    (by norm_num) (fun H hH he => eulerian_four_of_phi H hH he hbase) G hG (hbase G)
  convert h using 1
  ring

end Erdos583
end
end Source56_Erdos583_ImprovementFour
/- END Erdos583.ImprovementFour -/

/- BEGIN Erdos583.Statement; source SHA256 dfa8e7780f5ba471d158a5042c1ce51d239fb3bccae22167bf81cf2da67c8e1b -/
section Source57_Erdos583_Statement



/-! Universal original-edge path-partition improvement. All supporting graph
and decomposition bounds are proved in the local import closure. -/
noncomputable section
namespace Erdos583
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

/-- A smaller universal linear coefficient for connected finite simple graphs.
The finite family partitions every original edge exactly once into nonempty
vertex-simple paths. No degree, density, parity or size premise is required. -/
theorem general_path_partition_improvement (G : SimpleGraph V) (hG : G.Connected) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, IsNonemptyPathSubgraph H) ∧ IsDecomposition G D ∧
      (D.card : ℚ) ≤ (2/3-1/654444 : ℚ)*Fintype.card V + 1/6 + 1/327222 :=
  general_four_of_phi (fun H => hasPathBound_phi H) G hG

/-- The corresponding stronger coefficient when every ordinary degree is even. -/
theorem eulerian_path_partition_improvement (G : SimpleGraph V) (hG : G.Connected)
    (heven : ∀ v, Even (G.degree v)) :
    HasPathBound G ((2/3-1/163611 : ℚ)*Fintype.card V + 1/54537) :=
  eulerian_four_of_phi G hG heven (fun H => hasPathBound_phi H)

end Erdos583
end
end Source57_Erdos583_Statement
/- END Erdos583.Statement -/

import Openmath.Attempt6.Reachability
import Openmath.Attempt6.SampledReachability
import Mathlib

/-!
# Actual well-expanding seed extraction

The neighborhood is the explicitly external neighborhood from RobustCore.
Adding one vertex can remove that vertex from the old boundary; the finite
maximality argument below retains this loss rather than treating neighborhoods
as monotone. Every deletion is a finite set of actual original graph edges.
-/

namespace Erdos585.Attempt6.WellExpandingSeed

open SimpleGraph
open RobustCore

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mem_external {G : SimpleGraph V} {S : Finset V} {v : V} :
    v ∈ externalNeighbors G S ↔ v ∉ S ∧ ∃ u ∈ S, G.Adj u v := by
  classical
  simp [externalNeighbors]

/-- Fresh original neighbors outside the seed and its old external boundary. -/
noncomputable def freshNeighbors (G : SimpleGraph V) (S : Finset V) (v : V) : Finset V := by
  classical
  exact (S ∪ externalNeighbors G S)ᶜ.filter (G.Adj v)

/-- The exact finite one-vertex boundary comparison, including its possible
loss of the newly inserted vertex. -/
theorem boundary_add_one (G : SimpleGraph V) (S : Finset V) (v : V) :
    (externalNeighbors G S).card + (freshNeighbors G S v).card ≤
      (externalNeighbors G (insert v S)).card + 1 := by
  classical
  have hd : Disjoint (externalNeighbors G S) (freshNeighbors G S v) := by
    rw [Finset.disjoint_left]
    intro w hw hf
    have hf := Finset.mem_filter.mp hf
    have hn : w ∉ S ∪ externalNeighbors G S := Finset.mem_compl.mp hf.1
    exact hn (Finset.mem_union_right _ hw)
  have hsub : externalNeighbors G S ∪ freshNeighbors G S v ⊆
      insert v (externalNeighbors G (insert v S)) := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · by_cases hwv : w = v
      · exact Finset.mem_insert.mpr (Or.inl hwv)
      · obtain ⟨hwn, u, hu, huw⟩ := mem_external.mp hw
        exact Finset.mem_insert.mpr (Or.inr (mem_external.mpr
          ⟨by simpa using And.intro hwv hwn, u, Finset.mem_insert_of_mem hu, huw⟩))
    · obtain ⟨hwc, hvw⟩ := Finset.mem_filter.mp hw
      have hwn := Finset.mem_compl.mp hwc
      have hws : w ∉ S := fun h => hwn (Finset.mem_union_left _ h)
      have hwv : w ≠ v := hvw.ne.symm
      exact Finset.mem_insert.mpr (Or.inr (mem_external.mpr
        ⟨by simpa using And.intro hwv hws, v, Finset.mem_insert_self _ _, hvw⟩))
  rw [← Finset.card_union_of_disjoint hd]
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

/-- A largest subset satisfying the genuine integer expansion threshold. -/
theorem exists_maximal_good_seed (G : SimpleGraph V) (U : Finset V) (q : ℕ) :
    ∃ S : Finset V, S ⊆ U ∧ q * S.card ≤ (externalNeighbors G S).card ∧
      ∀ T : Finset V, T ⊆ U → q * T.card ≤ (externalNeighbors G T).card → T.card ≤ S.card := by
  classical
  let candidates := U.powerset.filter (fun S => q * S.card ≤ (externalNeighbors G S).card)
  have hne : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by simp⟩
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image candidates Finset.card hne
  have hs := Finset.mem_filter.mp hS
  refine ⟨S, Finset.mem_powerset.mp hs.1, hs.2, ?_⟩
  intro T hTU hgood
  exact hmax T (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTU, hgood⟩)

/-- Delete exactly the actual original graph edges from A to B. -/
noncomputable def cutEdges (G : SimpleGraph V) (A B : Finset V) : Finset (Sym2 V) := by
  classical
  exact A.biUnion (fun a => (B.filter (G.Adj a)).image (fun b => s(a, b)))

theorem cutEdges_subset (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    cutEdges G A B ⊆ G.edgeFinset := by
  classical
  intro e he
  obtain ⟨a, ha, he⟩ := Finset.mem_biUnion.mp he
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp he
  simp only [Finset.mem_filter] at hb
  simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hb.2

theorem cutEdges_card_le (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (q : ℕ)
    (hdeg : ∀ a ∈ A, (B.filter (G.Adj a)).card ≤ q) :
    (cutEdges G A B).card ≤ A.card * q := by
  classical
  apply Finset.card_biUnion_le_card_mul
  intro a ha
  apply Finset.card_image_le.trans
  convert hdeg a ha using 1 <;> congr 1 <;> ext v <;> simp

theorem mk_mem_cutEdges {G : SimpleGraph V} {A B : Finset V} {a b : V}
    (ha : a ∈ A) (hb : b ∈ B) (hab : G.Adj a b) : s(a, b) ∈ cutEdges G A B := by
  classical
  exact Finset.mem_biUnion.mpr ⟨a, ha,
    Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, hab⟩, rfl⟩⟩

/-- Maximality bounds fresh external degrees at the exact integer threshold. -/
theorem maximal_seed_properties (G : SimpleGraph V) (U S : Finset V) (q : ℕ)
    (hS : S ⊆ U) (hgood : q * S.card ≤ (externalNeighbors G S).card)
    (hmax : ∀ T : Finset V, T ⊆ U → q * T.card ≤ (externalNeighbors G T).card →
      T.card ≤ S.card) :
    (∀ v ∈ U \ S, (freshNeighbors G S v).card ≤ q) ∧
      (S ≠ U → (externalNeighbors G S).card ≤ q * (S.card + 1)) := by
  classical
  have hins : ∀ v ∈ U \ S,
      (externalNeighbors G (insert v S)).card < q * (S.card + 1) := by
    intro v hv
    obtain ⟨hvU, hvS⟩ := Finset.mem_sdiff.mp hv
    by_contra hn
    have hnew : q * (insert v S).card ≤ (externalNeighbors G (insert v S)).card := by
      rw [Finset.card_insert_of_notMem hvS]
      exact le_of_not_gt hn
    have hc := hmax (insert v S) (Finset.insert_subset hvU hS) hnew
    rw [Finset.card_insert_of_notMem hvS] at hc
    omega
  constructor
  · intro v hv
    have h := boundary_add_one G S v
    have hi := hins v hv
    simp only [Nat.mul_add, Nat.mul_one] at hi
    omega
  · intro hne
    have hrem : (U \ S).Nonempty := by
      by_contra hn
      have he := Finset.not_nonempty_iff_eq_empty.mp hn
      exact hne (Finset.Subset.antisymm hS (Finset.sdiff_eq_empty_iff_subset.mp he))
    obtain ⟨v, hv⟩ := hrem
    have h := boundary_add_one G S v
    have hi := hins v hv
    omega

/-- The deletion removes every escape from U except through the actual
external boundary of the seed. -/
theorem boundary_after_cut_subset (G : SimpleGraph V) (U S : Finset V) (hS : S ⊆ U) :
    externalNeighbors
      (G.deleteEdges (cutEdges G (U \ S) (S ∪ externalNeighbors G S)ᶜ)) U ⊆
        externalNeighbors G S := by
  classical
  intro w hw
  obtain ⟨hwU, u, huU, huw⟩ := mem_external.mp hw
  have hdel := SimpleGraph.deleteEdges_adj.mp huw
  by_cases huS : u ∈ S
  · exact mem_external.mpr ⟨fun h => hwU (hS h), u, huS, hdel.1⟩
  · by_contra hwS
    have hwB : w ∈ (S ∪ externalNeighbors G S)ᶜ := by
      apply Finset.mem_compl.mpr
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact hwU (hS h)
      · exact hwS h
    exact hdel.2 (mk_mem_cutEdges (Finset.mem_sdiff.mpr ⟨huU, huS⟩) hwB hdel.1)

/-- Integer-threshold form of the seed lemma, with the stronger factor two.
Only actual robust expansion and actual original-edge deletions are used. -/
theorem exists_integer_seed (G : SimpleGraph V) [DecidableRel G.Adj]
    (L epsilon s : ℝ) (hG : RobustExpanderAt G L epsilon s)
    (hL : 1 ≤ L) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (q : ℕ) (hq : 1 ≤ q) (hqs : (q : ℝ) ≤ s)
    (U : Finset V) (hU : (U.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 3) :
    ∃ S : Finset V, S ⊆ U ∧ (q : ℝ) * S.card ≤ (externalNeighbors G S).card ∧
      epsilon * U.card / (2 * (q : ℝ) * L ^ 2) ≤ S.card := by
  classical
  have hLp : 0 < L := by linarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqp : (0 : ℝ) < q := by linarith
  have hden : 0 < 2 * (q : ℝ) * L ^ 2 := by positivity
  by_cases hUempty : U = ∅
  · subst U
    exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
  obtain ⟨S, hSU, hgood, hmax⟩ := exists_maximal_good_seed G U q
  refine ⟨S, hSU, by exact_mod_cast hgood, ?_⟩
  by_cases hfull : S = U
  · rw [hfull]
    apply (div_le_iff₀ hden).mpr
    have hL2 : (1 : ℝ) ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
    have hqL2 : (1 : ℝ) ≤ (q : ℝ) * L ^ 2 :=
      by simpa using mul_le_mul hqR hL2 (by norm_num) hqp.le
    have hcoef : epsilon ≤ 2 * (q : ℝ) * L ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg U.card)
    nlinarith
  obtain ⟨hfresh, hboundary⟩ := maximal_seed_properties G U S q hSU hgood hmax
  let B := (S ∪ externalNeighbors G S)ᶜ
  let F := cutEdges G (U \ S) B
  have hFG : F ⊆ G.edgeFinset := cutEdges_subset G _ _
  have hFq : F.card ≤ U.card * q := by
    apply (cutEdges_card_le G (U \ S) B q ?_).trans
      (Nat.mul_le_mul_right q (Finset.card_le_card Finset.sdiff_subset))
    intro v hv
    convert hfresh v hv using 1 <;> congr 1 <;> ext w <;> simp [freshNeighbors, B]
  have hFs : (F.card : ℝ) ≤ s * U.card := by
    have hcast : (F.card : ℝ) ≤ (U.card : ℝ) * q := by exact_mod_cast hFq
    have hs := mul_le_mul_of_nonneg_left hqs (Nat.cast_nonneg U.card)
    nlinarith
  have hUpos : 1 ≤ U.card := by
    have hne := Finset.nonempty_iff_ne_empty.mpr hUempty
    have hc := Finset.card_pos.mpr hne
    omega
  have hrob := hG U hUpos hU F (by
    simpa only [Finset.subset_iff, SimpleGraph.mem_edgeFinset] using hFG) hFs
  have hc := Finset.card_le_card (boundary_after_cut_subset G U S hSU)
  have hcR : ((externalNeighbors (G.deleteEdges F) U).card : ℝ) ≤
      (externalNeighbors G S).card := by exact_mod_cast hc
  have hN : epsilon * U.card / L ^ 2 ≤ (externalNeighbors G S).card := hrob.trans hcR
  have hSpos : 1 ≤ S.card := by
    by_contra hn
    have he : S = ∅ := Finset.card_eq_zero.mp (by omega)
    have hzero : epsilon * U.card / L ^ 2 ≤ 0 := by simpa [he, externalNeighbors] using hN
    have huR : (0 : ℝ) < U.card := by exact_mod_cast hUpos
    have hp := div_pos (mul_pos hepsilon huR) (sq_pos_of_pos hLp)
    linarith
  have hqk : q ≤ q * S.card := by simpa using Nat.mul_le_mul_left q hSpos
  have hNq : (externalNeighbors G S).card ≤ 2 * q * S.card := by
    have h := hboundary hfull
    simp only [Nat.mul_add, Nat.mul_one] at h
    calc
      _ ≤ q * S.card + q := h
      _ ≤ q * S.card + q * S.card := Nat.add_le_add_left hqk _
      _ = 2 * q * S.card := by ring
  have hNqR : ((externalNeighbors G S).card : ℝ) ≤ 2 * (q : ℝ) * S.card := by
    exact_mod_cast hNq
  have hscaled := (div_le_iff₀ (sq_pos_of_pos hLp)).mp (hN.trans hNqR)
  apply (div_le_iff₀ hden).mpr
  convert hscaled using 1 <;> ring

/-- Outside the old boundary, insertion loses no old external neighbor. -/
theorem boundary_add_no_loss (G : SimpleGraph V) (S : Finset V) (v : V)
    (hv : v ∉ externalNeighbors G S) :
    (externalNeighbors G S).card + (freshNeighbors G S v).card ≤
      (externalNeighbors G (insert v S)).card := by
  classical
  have hd : Disjoint (externalNeighbors G S) (freshNeighbors G S v) := by
    rw [Finset.disjoint_left]
    intro w hw hf
    have hn := Finset.mem_compl.mp (Finset.mem_filter.mp hf).1
    exact hn (Finset.mem_union_right _ hw)
  rw [← Finset.card_union_of_disjoint hd]
  apply Finset.card_le_card
  intro w hw
  rcases Finset.mem_union.mp hw with hw | hw
  · obtain ⟨hwn, u, hu, huw⟩ := mem_external.mp hw
    have hwv : w ≠ v := by intro h; subst w; exact hv (mem_external.mpr ⟨hwn,u,hu,huw⟩)
    exact mem_external.mpr
      ⟨by simpa using And.intro hwv hwn, u, Finset.mem_insert_of_mem hu, huw⟩
  · obtain ⟨hwc, hvw⟩ := Finset.mem_filter.mp hw
    have hwn := Finset.mem_compl.mp hwc
    have hws : w ∉ S := fun h => hwn (Finset.mem_union_left _ h)
    exact mem_external.mpr
      ⟨by simpa using And.intro hvw.ne.symm hws, v, Finset.mem_insert_self _ _, hvw⟩

theorem exists_maximal_real_seed (G : SimpleGraph V) (U : Finset V) (lambda : ℝ) :
    ∃ S : Finset V, S ⊆ U ∧ lambda * S.card ≤ (externalNeighbors G S).card ∧
      ∀ T : Finset V, T ⊆ U → lambda * T.card ≤ (externalNeighbors G T).card →
        T.card ≤ S.card := by
  classical
  let candidates := U.powerset.filter
    (fun S => lambda * S.card ≤ (externalNeighbors G S).card)
  have hne : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by simp⟩
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image candidates Finset.card hne
  have hs := Finset.mem_filter.mp hS
  exact ⟨S, Finset.mem_powerset.mp hs.1, hs.2, fun T hTU hgood =>
    hmax T (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTU, hgood⟩)⟩

theorem cutEdges_card_le_real (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (lambda : ℝ)
    (hdeg : ∀ a ∈ A, ((B.filter (G.Adj a)).card : ℝ) ≤ lambda) :
    ((cutEdges G A B).card : ℝ) ≤ lambda * A.card := by
  classical
  calc
    _ ≤ ((∑ a ∈ A, ((B.filter (G.Adj a)).image (fun b => s(a,b))).card : ℕ) : ℝ) := by
      have hc := Finset.card_biUnion_le (s := A)
        (t := fun a => (B.filter (G.Adj a)).image (fun b => s(a,b)))
      have heq : cutEdges G A B = A.biUnion
          (fun a => (B.filter (G.Adj a)).image (fun b => s(a,b))) := by
        ext e
        simp [cutEdges]
      rw [heq]
      exact_mod_cast hc
    _ = ∑ a ∈ A, (((B.filter (G.Adj a)).image (fun b => s(a,b))).card : ℝ) := by simp
    _ ≤ ∑ a ∈ A, lambda := by
      apply Finset.sum_le_sum
      intro a ha
      have hc : (((B.filter (G.Adj a)).image (fun b => s(a,b))).card : ℝ) ≤
          (B.filter (G.Adj a)).card := by exact_mod_cast Finset.card_image_le
      apply hc.trans
      convert hdeg a ha using 1 <;> congr 1 <;> ext v <;> simp
    _ = lambda * A.card := by simp [mul_comm]

/-- Removing escapes from the vertices outside the closed seed boundary leaves
only the old boundary as possible external neighbors. -/
theorem outside_boundary_after_cut (G : SimpleGraph V) (U S : Finset V) :
    externalNeighbors
      (G.deleteEdges (cutEdges G (U \ (S ∪ externalNeighbors G S))
        (S ∪ externalNeighbors G S)ᶜ)) (U \ (S ∪ externalNeighbors G S)) ⊆
      externalNeighbors G S := by
  classical
  intro w hw
  obtain ⟨hwA, u, huA, huw⟩ := mem_external.mp hw
  have huC := (Finset.mem_sdiff.mp huA).2
  have huS : u ∉ S := fun h => huC (Finset.mem_union_left _ h)
  have hdel := SimpleGraph.deleteEdges_adj.mp huw
  by_contra hwN
  have hwS : w ∉ S := by
    intro hwS
    exact huC (Finset.mem_union_right _ (mem_external.mpr
      ⟨huS,w,hwS,hdel.1.symm⟩))
  have hwB : w ∈ (S ∪ externalNeighbors G S)ᶜ := by simp [hwS,hwN]
  exact hdel.2 (mk_mem_cutEdges huA hwB hdel.1)

/-- Real-parameter seed extraction with the source factor three. The ambient
scale is at least two; the logarithmic specialization follows separately. -/
theorem exists_real_seed (G : SimpleGraph V) [DecidableRel G.Adj]
    (L epsilon s lambda : ℝ) (hG : RobustExpanderAt G L epsilon s)
    (hL : 2 ≤ L) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hlambda : 1 ≤ lambda) (hls : lambda ≤ s)
    (U : Finset V) (hU : (U.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 3) :
    ∃ S : Finset V, S ⊆ U ∧ lambda * S.card ≤ (externalNeighbors G S).card ∧
      epsilon * U.card / (3 * lambda * L ^ 2) ≤ S.card := by
  classical
  have hLp : 0 < L := by linarith
  have hlp : 0 < lambda := by linarith
  have hL2 : 4 ≤ L ^ 2 := by nlinarith
  have hden : 0 < 3 * lambda * L ^ 2 := by positivity
  obtain ⟨S, hSU, hgood, hmax⟩ := exists_maximal_real_seed G U lambda
  refine ⟨S,hSU,hgood,?_⟩
  have hins : ∀ v ∈ U \ S,
      ((externalNeighbors G (insert v S)).card : ℝ) < lambda * (S.card + 1) := by
    intro v hv
    obtain ⟨hvU,hvS⟩ := Finset.mem_sdiff.mp hv
    by_contra hn
    have hc := hmax (insert v S) (Finset.insert_subset hvU hSU) (by
      rw [Finset.card_insert_of_notMem hvS]
      push_cast
      exact le_of_not_gt hn)
    rw [Finset.card_insert_of_notMem hvS] at hc
    omega
  let N := externalNeighbors G S
  let A := U \ (S ∪ N)
  let B := (S ∪ N)ᶜ
  let F := cutEdges G A B
  have hAdeg : ∀ v ∈ A, ((B.filter (G.Adj v)).card : ℝ) ≤ lambda := by
    intro v hv
    have hvU := (Finset.mem_sdiff.mp hv).1
    have hvC := (Finset.mem_sdiff.mp hv).2
    have hvS : v ∉ S := fun h => hvC (Finset.mem_union_left _ h)
    have hvN : v ∉ N := fun h => hvC (Finset.mem_union_right _ h)
    have hb := boundary_add_no_loss G S v hvN
    have hbR : (N.card : ℝ) + (freshNeighbors G S v).card ≤
        (externalNeighbors G (insert v S)).card := by exact_mod_cast hb
    have hi := hins v (Finset.mem_sdiff.mpr ⟨hvU,hvS⟩)
    have hf : ((freshNeighbors G S v).card : ℝ) ≤ lambda := by
      dsimp [N] at hbR
      nlinarith
    have heq : B.filter (G.Adj v) = freshNeighbors G S v := by
      ext w
      simp [freshNeighbors,B,N]
    rw [heq]
    exact hf
  have hFbudget : (F.card : ℝ) ≤ s * A.card := by
    exact (cutEdges_card_le_real G A B lambda hAdeg).trans
      (mul_le_mul_of_nonneg_right hls (Nat.cast_nonneg _))
  have hAF : epsilon * A.card ≤ (N.card : ℝ) * L ^ 2 := by
    by_cases hAe : A = ∅
    · simp only [hAe,Finset.card_empty,Nat.cast_zero,mul_zero]
      positivity
    have hAp : 1 ≤ A.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hAe)
    have hAU : (A.card : ℝ) ≤ U.card := by
      exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : A ⊆ U)
    have hFG := cutEdges_subset G A B
    have hr := hG A hAp (hAU.trans hU) F (by
      simpa only [Finset.subset_iff,SimpleGraph.mem_edgeFinset] using hFG) hFbudget
    have hc := Finset.card_le_card (outside_boundary_after_cut G U S)
    have hcR : ((externalNeighbors (G.deleteEdges F) A).card : ℝ) ≤ N.card := by
      exact_mod_cast hc
    exact (div_le_iff₀ (sq_pos_of_pos hLp)).mp (hr.trans hcR)
  have hcover : U ⊆ A ∪ (S ∪ N) := by
    intro v hv
    by_cases hc : v ∈ S ∪ N
    · exact Finset.mem_union_right _ hc
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hv,hc⟩)
  have hUc : (U.card : ℝ) ≤ A.card + (S.card : ℝ) + N.card := by
    have hc := (Finset.card_le_card hcover).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_union_le _ _) _))
    have hcR : (U.card : ℝ) ≤ A.card + ((S.card : ℝ) + N.card) := by exact_mod_cast hc
    linarith
  have htotal : epsilon * U.card ≤ (N.card : ℝ) * L ^ 2 +
      epsilon * ((S.card : ℝ) + N.card) := by
    have hh := mul_le_mul_of_nonneg_left hUc hepsilon.le
    nlinarith [hAF]
  by_cases hSe : S = ∅
  · have hNe : N = ∅ := by simp [N,hSe,externalNeighbors]
    have hzero : epsilon * U.card ≤ 0 := by simpa [hSe,hNe] using htotal
    have hUe : U = ∅ := by
      apply Finset.card_eq_zero.mp
      have hc : (U.card : ℝ) = 0 := by nlinarith [show (0 : ℝ) ≤ U.card from Nat.cast_nonneg _]
      exact_mod_cast hc
    simp [hSe,hUe]
  have hkNat : 1 ≤ S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hSe)
  have hk : (1 : ℝ) ≤ S.card := by exact_mod_cast hkNat
  by_cases hfull : S = U
  · rw [hfull]
    apply (div_le_iff₀ hden).mpr
    have hm := mul_le_mul_of_nonneg_right
      (show epsilon ≤ 3 * lambda * L ^ 2 by nlinarith) (Nat.cast_nonneg U.card)
    nlinarith
  have hNbound : (N.card : ℝ) < lambda * (S.card + 1) + 1 := by
    have hrem : (U \ S).Nonempty := by
      by_contra hn
      exact hfull (Finset.Subset.antisymm hSU
        (Finset.sdiff_eq_empty_iff_subset.mp (Finset.not_nonempty_iff_eq_empty.mp hn)))
    obtain ⟨v,hv⟩ := hrem
    have hb := boundary_add_one G S v
    have hbR : (N.card : ℝ) + (freshNeighbors G S v).card ≤
        (externalNeighbors G (insert v S)).card + 1 := by exact_mod_cast hb
    have hi := hins v hv
    nlinarith [show (0 : ℝ) ≤ (freshNeighbors G S v).card from Nat.cast_nonneg _]
  by_cases hsmall : (N.card : ℝ) ≤ 2 * lambda * S.card
  · have hterm : epsilon * ((S.card : ℝ) + N.card) ≤
        3 * lambda * S.card := by
      have h1 := mul_le_mul_of_nonneg_right hepsilon1
        (show 0 ≤ (S.card : ℝ) + N.card by positivity)
      have h2 := mul_le_mul_of_nonneg_right hlambda (Nat.cast_nonneg S.card)
      nlinarith
    have hnl := mul_le_mul_of_nonneg_right hsmall (sq_nonneg L)
    have hkl : 3 * lambda * S.card ≤ lambda * S.card * L ^ 2 := by
      have hp : 0 ≤ lambda * S.card := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hL2 hp]
    apply (div_le_iff₀ hden).mpr
    nlinarith [htotal,hnl,hterm,hkl]
  · have hkone : S.card = 1 := by
      by_contra hn
      have hk2 : (2 : ℝ) ≤ S.card := by
        have hn2 : 2 ≤ S.card := by omega
        exact_mod_cast hn2
      have hx : 1 ≤ lambda * ((S.card : ℝ) - 1) := by
        nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (S.card : ℝ) - 1 by linarith) hlp.le]
      nlinarith
    have hUclosed : U ⊆ S ∪ N := by
      intro v hvU
      by_contra hvC
      have hvS : v ∉ S := fun h => hvC (Finset.mem_union_left _ h)
      have hvN : v ∉ N := fun h => hvC (Finset.mem_union_right _ h)
      have hb := boundary_add_no_loss G S v hvN
      have hbR : (N.card : ℝ) + (freshNeighbors G S v).card ≤
          (externalNeighbors G (insert v S)).card := by exact_mod_cast hb
      have hi := hins v (Finset.mem_sdiff.mpr ⟨hvU,hvS⟩)
      rw [hkone] at hi hsmall
      norm_num at hi hsmall
      nlinarith [show (0 : ℝ) ≤ (freshNeighbors G S v).card from Nat.cast_nonneg _]
    have hUc2 : (U.card : ℝ) ≤ (S.card : ℝ) + N.card := by
      exact_mod_cast (Finset.card_le_card hUclosed).trans (Finset.card_union_le _ _)
    rw [hkone] at hUc2 hNbound ⊢
    norm_num at hUc2 hNbound ⊢
    apply (div_le_iff₀ hden).mpr
    have he := mul_le_mul_of_nonneg_right hepsilon1 (Nat.cast_nonneg U.card)
    have hprod := mul_le_mul_of_nonneg_left hL2 hlp.le
    nlinarith

/-- Robust expansion with deletion budget at least one rules out orders two
and three. This uses the actual cut from all but one vertex to that vertex. -/
theorem robust_order_ge_four (G : SimpleGraph V) [DecidableRel G.Adj]
    (L epsilon s : ℝ) (hG : RobustExpanderAt G L epsilon s)
    (hn : 2 ≤ Fintype.card V) (hL : 0 < L) (hepsilon : 0 < epsilon)
    (hs : 1 ≤ s) : 4 ≤ Fintype.card V := by
  classical
  by_contra hn4
  have hn3 : Fintype.card V ≤ 3 := by omega
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v : V := Classical.choice inferInstance
  let A : Finset V := Finset.univ.erase v
  let B : Finset V := {v}
  let F := cutEdges G A B
  have hAc : A.card + 1 = Fintype.card V := by
    simpa [A] using Finset.card_erase_add_one (s := Finset.univ) (Finset.mem_univ v)
  have hAp : 1 ≤ A.card := by omega
  have hAsmall : (A.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 3 := by
    have hAcR : (A.card : ℝ) + 1 = Fintype.card V := by exact_mod_cast hAc
    have hn3R : (Fintype.card V : ℝ) ≤ 3 := by exact_mod_cast hn3
    linarith
  have hFcard : F.card ≤ A.card := by
    have hc := cutEdges_card_le G A B 1 (by
      intro a ha
      exact (Finset.card_filter_le _ _).trans (by simp [B]))
    simpa using hc
  have hFbudget : (F.card : ℝ) ≤ s * A.card := by
    have hcR : (F.card : ℝ) ≤ A.card := by exact_mod_cast hFcard
    have hh := mul_le_mul_of_nonneg_right hs (show (0 : ℝ) ≤ A.card by positivity)
    nlinarith
  have hFG := cutEdges_subset G A B
  have hr := hG A hAp hAsmall F (by
    simpa only [Finset.subset_iff,SimpleGraph.mem_edgeFinset] using hFG) hFbudget
  have hzero : externalNeighbors (G.deleteEdges F) A = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨hwA,u,huA,huw⟩ := mem_external.mp hw
    have hwv : w = v := by
      by_contra hne
      exact hwA (by simp [A,hne])
    have hdel := SimpleGraph.deleteEdges_adj.mp huw
    exact hdel.2 (mk_mem_cutEdges huA (by simp [B,hwv]) hdel.1)
  have hr0 : epsilon * A.card / L ^ 2 ≤ 0 := by simpa [hzero] using hr
  have hAr : (0 : ℝ) < A.card := by exact_mod_cast hAp
  have hp := div_pos (mul_pos hepsilon hAr) (sq_pos_of_pos hL)
  linarith

theorem two_le_logTwo_nat {n : ℕ} (hn : 4 ≤ n) : 2 ≤ logTwo (n : ℝ) := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hnR
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  unfold logTwo
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  linarith

/-- CJMM Lemma7.8 with an explicit ambient logarithmic scale and actual graph
order. All parameters remain real and the source factor three is unchanged. -/
theorem exists_well_expanding_seed (G : SimpleGraph V) [DecidableRel G.Adj]
    (L epsilon s lambda : ℝ) (hG : RobustExpanderAt G L epsilon s)
    (hn : 2 ≤ Fintype.card V) (hlog : logTwo (Fintype.card V : ℝ) ≤ L)
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hlambda : 1 ≤ lambda) (hls : lambda ≤ s)
    (U : Finset V) (hU : (U.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 3) :
    ∃ S : Finset V, S ⊆ U ∧ lambda * S.card ≤ (externalNeighbors G S).card ∧
      epsilon * U.card / (3 * lambda * L ^ 2) ≤ S.card := by
  have hnR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hlog1 : 1 ≤ logTwo (Fintype.card V : ℝ) :=
    (one_le_div (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
      (Real.log_le_log (by norm_num) hnR)
  have hLp : 0 < L := by linarith
  have hn4 := robust_order_ge_four G L epsilon s hG hn hLp hepsilon (hlambda.trans hls)
  exact exists_real_seed G L epsilon s lambda hG
    ((two_le_logTwo_nat hn4).trans hlog) hepsilon hepsilon1 hlambda hls U hU

/-- The literal logarithmic-scale formulation of CJMM Lemma7.8. -/
theorem cjmm_lemma_7_8 (G : SimpleGraph V) [DecidableRel G.Adj]
    (epsilon s lambda : ℝ) (hG : RobustExpander G epsilon s)
    (hn : 2 ≤ Fintype.card V) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hlambda : 1 ≤ lambda) (hls : lambda ≤ s)
    (U : Finset V) (hU : (U.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 3) :
    ∃ S : Finset V, S ⊆ U ∧ lambda * S.card ≤ (externalNeighbors G S).card ∧
      epsilon * U.card / (3 * lambda * (logTwo (Fintype.card V : ℝ)) ^ 2) ≤ S.card := by
  change RobustExpanderAt G (logTwo (Fintype.card V : ℝ)) epsilon s at hG
  exact exists_well_expanding_seed G _ epsilon s lambda hG hn le_rfl
    hepsilon hepsilon1.le hlambda hls U hU

/-- The seed predicate used by the actual sampled-reachability supplier.
The required robustness threshold is explicit and retains the power26 size loss. -/
theorem exists_sampled_well_expanding_seed (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : unitInterval) (L epsilon s : ℝ) (hG : RobustExpanderAt G L epsilon s)
    (hn : 2 ≤ Fintype.card V) (hlog : logTwo (Fintype.card V : ℝ) ≤ L)
    (hp : 0 < (p : ℝ)) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hs : ((p : ℝ)⁻¹) ^ 4 * L ^ 24 ≤ s)
    (U : Finset V) (hU : (U.card : ℝ) ≤ 2 * (Fintype.card V : ℝ) / 3) :
    ∃ S : Finset V, S ⊆ U ∧ SampledReachability.WellExpandingAt G p L S ∧
      epsilon * U.card / (3 * ((p : ℝ)⁻¹) ^ 4 * L ^ 26) ≤ S.card := by
  have hnR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hlog1 : 1 ≤ logTwo (Fintype.card V : ℝ) :=
    (one_le_div (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
      (Real.log_le_log (by norm_num) hnR)
  have hL1 : 1 ≤ L := hlog1.trans hlog
  have hpinv : 1 ≤ (p : ℝ)⁻¹ := (one_le_inv₀ hp).mpr p.property.2
  have hlambda : 1 ≤ ((p : ℝ)⁻¹) ^ 4 * L ^ 24 := by
    simpa using mul_le_mul (one_le_pow₀ hpinv) (one_le_pow₀ hL1)
      (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ ((p : ℝ)⁻¹) ^ 4)
  obtain ⟨S,hSU,hgood,hsize⟩ := exists_well_expanding_seed G L epsilon s
    (((p : ℝ)⁻¹) ^ 4 * L ^ 24) hG hn hlog hepsilon hepsilon1 hlambda hs U hU
  refine ⟨S,hSU,?_,?_⟩
  · unfold SampledReachability.WellExpandingAt
    nlinarith [hgood]
  · have heq : 3 * (((p : ℝ)⁻¹) ^ 4 * L ^ 24) * L ^ 2 =
        3 * ((p : ℝ)⁻¹) ^ 4 * L ^ 26 := by ring
    rwa [heq] at hsize

end Erdos585.Attempt6.WellExpandingSeed

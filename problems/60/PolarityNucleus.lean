import PolarityPathCount
import PolarityAbsoluteBound

namespace Erdos60.Geometry
variable {P L : Type*} [Membership P L]

/-- A minimum-size blocking set has at most one point on a line through an outside point. -/
theorem blocking_unique_on_line [Configuration.ProjectivePlane P L]
    [Fintype P] [Fintype L] (B : Finset P)
    (hcard : B.card = Configuration.ProjectivePlane.order P L + 1)
    (hblock : ∀ l : L, ∃ b ∈ B, b ∈ l)
    {x : P} (hx : x ∉ B) {l : L} (hxl : x ∈ l)
    {a b : P} (ha : a ∈ B) (hb : b ∈ B) (hal : a ∈ l) (hbl : b ∈ l) : a = b := by
  classical
  have hne : ∀ b : B, x ≠ b.val := by intro b h; exact hx (h ▸ b.property)
  let f : B → {l : L // x ∈ l} := fun b =>
    ⟨Configuration.HasLines.mkLine (hne b), (Configuration.HasLines.mkLine_ax (hne b)).1⟩
  have hf : ∀ b : B, b.val ∈ (f b).val := fun b => (Configuration.HasLines.mkLine_ax (hne b)).2
  have hs : Function.Surjective f := by
    intro t
    obtain ⟨b,hb,hbt⟩ := hblock t.val
    refine ⟨⟨b,hb⟩, ?_⟩
    apply Subtype.ext
    exact (Configuration.Nondegenerate.eq_or_eq (f ⟨b,hb⟩).property (hf ⟨b,hb⟩)
      t.property hbt).resolve_left (hne ⟨b,hb⟩)
  have hc : Fintype.card B = Fintype.card {l : L // x ∈ l} := by
    rw [Fintype.card_coe, hcard]
    simpa only [Configuration.lineCount, Nat.card_eq_fintype_card] using
      (Configuration.ProjectivePlane.lineCount_eq L x).symm
  have hi := ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨hs,hc⟩).1
  have hfa : (f ⟨a,ha⟩).val = l :=
    (Configuration.Nondegenerate.eq_or_eq (f ⟨a,ha⟩).property (hf ⟨a,ha⟩) hxl hal).resolve_left (hne ⟨a,ha⟩)
  have hfb : (f ⟨b,hb⟩).val = l :=
    (Configuration.Nondegenerate.eq_or_eq (f ⟨b,hb⟩).property (hf ⟨b,hb⟩) hxl hbl).resolve_left (hne ⟨b,hb⟩)
  exact congrArg Subtype.val (hi (Subtype.ext (hfa.trans hfb.symm)))

/-- A blocking set of q+1 points in a finite projective plane is exactly a line. -/
theorem blocking_set_eq_line [Configuration.ProjectivePlane P L]
    [Fintype P] [Fintype L] (B : Finset P)
    (hcard : B.card = Configuration.ProjectivePlane.order P L + 1)
    (hblock : ∀ l : L, ∃ b ∈ B, b ∈ l) :
    ∃ l : L, ∀ x : P, x ∈ B ↔ x ∈ l := by
  classical
  have hq := Configuration.ProjectivePlane.one_lt_order P L
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (show 1 < B.card by omega)
  let l : L := Configuration.HasLines.mkLine hab
  have hal : a ∈ l := (Configuration.HasLines.mkLine_ax hab).1
  have hbl : b ∈ l := (Configuration.HasLines.mkLine_ax hab).2
  let S : Finset P := Finset.univ.filter (fun x => x ∈ l)
  have hsub : S ⊆ B := by
    intro x hx
    have hxl : x ∈ l := (Finset.mem_filter.mp hx).2
    by_contra hnot
    exact hab (blocking_unique_on_line B hcard hblock hnot hxl ha hb hal hbl)
  have hS : S.card = B.card := by
    rw [hcard, ← Configuration.ProjectivePlane.pointCount_eq P l]
    simp [S, Configuration.pointCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have heq : S = B := Finset.eq_of_subset_of_card_le hsub (by omega)
  refine ⟨l, ?_⟩
  intro x
  rw [← heq]
  simp [S]

/-- Once absolute points have minimum blocking size, polarity yields an actual nucleus.
The cardinality and blocking hypotheses are explicit inputs, not assumed source theorems. -/
theorem Polarity.nucleus_of_absolute_blocking
    [Configuration.ProjectivePlane P L] [Fintype P] [Finite L]
    (π : Polarity (P := P) (L := L))
    (hcard : Nat.card {a : P // π.Absolute a} = Configuration.ProjectivePlane.order P L + 1)
    (hblock : ∀ l : L, ∃ a : P, π.Absolute a ∧ a ∈ l) :
    ∃ w : P, ¬π.Absolute w ∧ ∀ a : P, π.Absolute a → π.graph.Adj w a := by
  classical
  let : Fintype L := Fintype.ofFinite L
  let B : Finset P := Finset.univ.filter π.Absolute
  have hB : ∀ a : P, a ∈ B ↔ π.Absolute a := by intro a; simp [B]
  have hBc : B.card = Configuration.ProjectivePlane.order P L + 1 := by
    simpa [B, Nat.card_eq_fintype_card, Fintype.card_subtype] using hcard
  have hBb : ∀ l : L, ∃ b ∈ B, b ∈ l := by
    intro l
    obtain ⟨a,ha,hal⟩ := hblock l
    exact ⟨a,(hB a).mpr ha,hal⟩
  obtain ⟨l,hl⟩ := blocking_set_eq_line B hBc hBb
  let w := π.line.symm l
  have hw : π.line w = l := π.line.apply_symm_apply l
  have hinc : ∀ a : P, π.Absolute a → a ∈ π.line w := by
    intro a ha
    rw [hw]
    exact (hl a).mp ((hB a).mpr ha)
  have hnabs : ¬π.Absolute w := by
    intro haw
    have hq := Configuration.ProjectivePlane.one_lt_order P L
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (show 1 < B.card by omega)
    have hsame : ∀ a : P, π.Absolute a → a = w := by
      intro a haa
      by_contra hne
      exact π.absolute_not_adjacent haa haw ⟨hne,hinc a haa⟩
    exact hab ((hsame a ((hB a).mp ha)).trans (hsame b ((hB b).mp hb)).symm)
  refine ⟨w,hnabs,?_⟩
  intro a ha
  refine ⟨?_, (π.reciprocal a w).mp (hinc a ha)⟩
  intro h
  exact hnabs (h.symm ▸ ha)

/-- Actual even-order nucleus from the minimum absolute-point count.
The blocking property is proved by the imported odd-cardinality involution argument. -/
theorem Polarity.nucleus_of_even_absolute_card
    [Configuration.ProjectivePlane P L] [Fintype P] [Finite L]
    (π : Polarity (P := P) (L := L))
    (heven : Even (Configuration.ProjectivePlane.order P L))
    (hcard : Nat.card {a : P // π.Absolute a} = Configuration.ProjectivePlane.order P L + 1) :
    ∃ w : P, ¬π.Absolute w ∧ ∀ a : P, π.Absolute a → π.graph.Adj w a := by
  exact π.nucleus_of_absolute_blocking hcard (π.absolute_meets_line heven)

#print axioms Polarity.nucleus_of_even_absolute_card
#print axioms Polarity.nucleus_of_absolute_blocking
#print axioms blocking_unique_on_line
#print axioms blocking_set_eq_line
end Erdos60.Geometry

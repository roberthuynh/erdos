import Openmath.Erdos642.Proofs.DenseMask20261019.GallaiPaths
import Mathlib.Data.Set.Card.Arithmetic

namespace Erdos642.DenseMask20261019.GallaiHitting
open SimpleGraph GallaiComponents GallaiPaths
variable {V : Type*}

private noncomputable def discard {W : Type*} (S : Set W) : Set W := by
  classical
  exact if h : S.Nonempty then S \ {h.choose} else ∅

private theorem discard_card {W : Type*} [Finite W] (S : Set W) :
    (discard S).ncard ≤ 2 * (S.ncard / 2) := by
  classical
  unfold discard
  split_ifs with h
  · rw [Set.ncard_sdiff_singleton_of_mem h.choose_spec]
    omega
  · simp

private theorem remaining_unique {W : Type*} (S : Set W) {x y : W}
    (hx : x ∈ S) (hy : y ∈ S) (hxd : x ∉ discard S) (hyd : y ∉ discard S) : x = y := by
  classical
  have h : S.Nonempty := ⟨x, hx⟩
  simp only [discard, dif_pos h, Set.mem_diff, Set.mem_singleton_iff, not_and,
    not_not] at hxd hyd
  exact (hxd hx).trans (hyd hy).symm

private def terminalSet (G : SimpleGraph V) (A U : Set V)
    (C : (original G U).ConnectedComponent) : Set ↥(Uᶜ) :=
  C.supp ∩ {x | x.val ∈ A}

private theorem terminalSet_card (G : SimpleGraph V) (A U : Set V)
    (C : (original G U).ConnectedComponent) :
    (terminalSet G A U C).ncard = terminals G A U C := by
  let e : {x : C.supp // x.val.val ∈ A} ≃ terminalSet G A U C :=
    { toFun := fun x => ⟨x.val.val, ⟨x.val.property, x.property⟩⟩
      invFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold terminals
  simpa only [Nat.card_coe_set_eq] using (Nat.card_congr e).symm

/-- An actual low-score original deletion yields a small actual terminal-separating set. -/
theorem separating_set_of_score [Fintype V] (G : SimpleGraph V) (A U : Set V) (k : ℕ)
    (hscore : letI := Fintype.ofFinite (original G U).ConnectedComponent
      U.ncard + ∑ C, terminals G A U C / 2 < k) :
    ∃ X : Set V, X.ncard ≤ 2 * k - 2 ∧
      ∀ x y : ↥(Xᶜ), x.val ∈ A → y.val ∈ A →
        (G.induce Xᶜ).Reachable x y → x = y := by
  classical
  letI := Fintype.ofFinite (original G U).ConnectedComponent
  let T : Set ↥(Uᶜ) := ⋃ C, discard (terminalSet G A U C)
  let X : Set V := U ∪ Subtype.val '' T
  have hUT : U ⊆ X := Set.subset_union_left
  have hT : T.ncard ≤ 2 * ∑ C, terminals G A U C / 2 := by
    calc
      T.ncard ≤ ∑ C, (discard (terminalSet G A U C)).ncard :=
        Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ C, 2 * (terminals G A U C / 2) := by
        apply Finset.sum_le_sum
        intro C _
        simpa only [terminalSet_card] using discard_card (terminalSet G A U C)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hX : X.ncard ≤ U.ncard + T.ncard := by
    calc
      X.ncard ≤ U.ncard + (Subtype.val '' T).ncard := Set.ncard_union_le _ _
      _ = _ := by rw [Set.ncard_image_of_injective _ Subtype.val_injective]
  refine ⟨X, by omega, ?_⟩
  let j : G.induce Xᶜ →g original G U :=
    { toFun := fun x => ⟨x.val, fun hu => x.property (hUT hu)⟩
      map_rel' := fun h => h }
  intro x y hxA hyA hxy
  have hr : (original G U).Reachable (j x) (j y) := by
    obtain ⟨p⟩ := hxy
    exact ⟨p.map j⟩
  let C := (original G U).connectedComponentMk (j x)
  have hxC : j x ∈ C.supp := rfl
  have hyC : j y ∈ C.supp := (ConnectedComponent.sound hr).symm
  have hxd : j x ∉ discard (terminalSet G A U C) := by
    intro h
    apply x.property
    exact Or.inr ⟨j x, Set.mem_iUnion.mpr ⟨C, h⟩, rfl⟩
  have hyd : j y ∉ discard (terminalSet G A U C) := by
    intro h
    apply y.property
    exact Or.inr ⟨j y, Set.mem_iUnion.mpr ⟨C, h⟩, rfl⟩
  have he := remaining_unique (terminalSet G A U C) ⟨hxC, hxA⟩ ⟨hyC, hyA⟩ hxd hyd
  have hval := congrArg (fun z : ↥(Uᶜ) => z.val) he
  exact Subtype.ext hval

/-- Gallai's alternative with actual original simple paths and full-support disjointness. -/
theorem gallai_alternative [Fintype V] (G : SimpleGraph V) (A : Set V) (k : ℕ) :
    (∃ p : Fin k → APath G A,
      Pairwise fun i j => Disjoint {x | x ∈ (p i).walk.support} {x | x ∈ (p j).walk.support}) ∨
    (∃ X : Set V, X.ncard ≤ 2 * k - 2 ∧
      ∀ x y : ↥(Xᶜ), x.val ∈ A → y.val ∈ A →
        (G.induce Xᶜ).Reachable x y → x = y) := by
  classical
  by_cases h : ∀ U : Set V,
      letI := Fintype.ofFinite (original G U).ConnectedComponent
      k ≤ U.ncard + ∑ C, terminals G A U C / 2
  · obtain ⟨M, hM, hcard⟩ := GallaiMatching.doubled_matching G A k h
    exact Or.inl (paths_of_doubled_matching G A k M hM hcard)
  · push_neg at h
    obtain ⟨U, hU⟩ := h
    exact Or.inr (separating_set_of_score G A U k hU)

/-- Literal terminal separation meets every original nontrivial terminal path. -/
theorem separation_hits_path (G : SimpleGraph V) (A X : Set V)
    (hsep : ∀ x y : ↥(Xᶜ), x.val ∈ A → y.val ∈ A →
      (G.induce Xᶜ).Reachable x y → x = y) (p : APath G A) :
    ∃ x ∈ p.walk.support, x ∈ X := by
  classical
  by_contra h
  push_neg at h
  have hav : ∀ x ∈ p.walk.support, x ∈ Xᶜ := h
  let q := p.walk.induce Xᶜ hav
  have he := hsep _ _ p.first_mem p.last_mem q.reachable
  exact p.distinct (congrArg Subtype.val he)

/-- The path-hitting formulation, with the same actual packing and sharp integer bound. -/
theorem gallai_path_hitting [Fintype V] (G : SimpleGraph V) (A : Set V) (k : ℕ) :
    (∃ p : Fin k → APath G A,
      Pairwise fun i j => Disjoint {x | x ∈ (p i).walk.support} {x | x ∈ (p j).walk.support}) ∨
    (∃ X : Set V, X.ncard ≤ 2 * k - 2 ∧
      ∀ p : APath G A, ∃ x ∈ p.walk.support, x ∈ X) := by
  rcases gallai_alternative G A k with h | ⟨X, hX, hsep⟩
  · exact Or.inl h
  · exact Or.inr ⟨X, hX, separation_hits_path G A X hsep⟩

end Erdos642.DenseMask20261019.GallaiHitting



import Openmath.Erdos643R3.StarMatchingBase

/-!
# The finite star-plus-matching lower bound

The full star on a center is augmented by a matching of floor((n-1)/3)
triples outside the center. All constructions use actual finite vertex sets,
and the lower bound is for the imported upstream extremal number.
-/
set_option autoImplicit false
namespace Erdos643R3.StarMatching
open Finset
open Erdos643R3.StarMatchingBase
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem mixed_union_impossible {c : V} {S B C D : Finset V}
    (hcC : c ∈ C) (hcB : c ∉ B) (hB : B.card = 3) (hC : C.card = 3)
    (hBD : Disjoint B D) (hu : S ∪ B = C ∪ D) : False := by
  have hsub : B ⊆ C := by
    intro z hz
    have hzU : z ∈ C ∪ D := by rw [← hu]; exact mem_union_right S hz
    exact (mem_union.mp hzU).resolve_right (fun hzD => disjoint_left.mp hBD hz hzD)
  have he : B = C := eq_of_subset_of_card_le hsub (by omega)
  exact hcB (he.symm ▸ hcC)

/-- A full star together with any disjoint matching outside the center avoids
the exact upstream repeated-disjoint-union predicate. -/
theorem star_union_matching_avoids (c : V) (M : Finset (Finset V))
    (hM : M.IsUniform 3) (_hc : ∀ e ∈ M, c ∉ e)
    (hd : ∀ A ∈ M, ∀ B ∈ M, A ≠ B → Disjoint A B) :
    ¬ (star c ∪ M).HasRepeatedDisjointUnion := by
  have hunif : (star c ∪ M).IsUniform 3 := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact star_uniform c e he
    · exact hM e he
  have hmem : ∀ e ∈ star c ∪ M, c ∉ e → e ∈ M := by
    intro e he hce
    rcases mem_union.mp he with he | he
    · exact False.elim (hce (apex_mem he))
    · exact he
  rintro ⟨A,hA,B,hB,C,hC,D,hD,hAB,hCD,hu,h1,h2,h3,h4,h5,h6⟩
  by_cases hcAB : c ∈ A ∪ B
  · have hcCD : c ∈ C ∪ D := by rwa [← hu]
    rcases mem_union.mp hcAB with hcA | hcB
    · have hnB : c ∉ B := fun hh => disjoint_left.mp hAB hcA hh
      have hBM := hmem B hB hnB
      rcases mem_union.mp hcCD with hcC | hcD
      · have hnD : c ∉ D := fun hh => disjoint_left.mp hCD hcC hh
        exact mixed_union_impossible hcC hnB (hunif B hB) (hunif C hC)
          (hd B hBM D (hmem D hD hnD) h6) hu
      · have hnC : c ∉ C := fun hh => disjoint_left.mp hCD hh hcD
        apply mixed_union_impossible hcD hnB (hunif B hB) (hunif D hD)
          (hd B hBM C (hmem C hC hnC) h5)
        rwa [union_comm D C]
    · have hnA : c ∉ A := fun hh => disjoint_left.mp hAB hh hcB
      have hAM := hmem A hA hnA
      rcases mem_union.mp hcCD with hcC | hcD
      · have hnD : c ∉ D := fun hh => disjoint_left.mp hCD hcC hh
        apply mixed_union_impossible hcC hnA (hunif A hA) (hunif C hC)
          (hd A hAM D (hmem D hD hnD) h4)
        rwa [union_comm B A]
      · have hnC : c ∉ C := fun hh => disjoint_left.mp hCD hh hcD
        apply mixed_union_impossible hcD hnA (hunif A hA) (hunif D hD)
          (hd A hAM C (hmem C hC hnC) h3)
        simpa only [union_comm] using hu
  · have hnA : c ∉ A := fun hh => hcAB (mem_union_left B hh)
    have hnC : c ∉ C := by
      intro hh
      apply hcAB
      rw [hu]
      exact mem_union_left D hh
    have hnD : c ∉ D := by
      intro hh
      apply hcAB
      rw [hu]
      exact mem_union_right C hh
    have hAM := hmem A hA hnA
    have hAC := hd A hAM C (hmem C hC hnC) h3
    have hAD := hd A hAM D (hmem D hD hnD) h4
    obtain ⟨z,hz⟩ := card_pos.mp (show 0 < A.card by rw [hunif A hA]; decide)
    have hzU : z ∈ C ∪ D := by rw [← hu]; exact mem_union_left B hz
    rcases mem_union.mp hzU with hzC | hzD
    · exact disjoint_left.mp hAC hz hzC
    · exact disjoint_left.mp hAD hz hzD

/-- Vertex j of block i among the m noncentral vertices of Fin(m+1). -/
def blockVertex (m : ℕ) (i : Fin (m / 3)) (j : Fin 3) : Fin (m+1) :=
  ⟨3 * i.val + j.val + 1, by have hi := i.isLt; have hj := j.isLt; omega⟩

def block (m : ℕ) (i : Fin (m / 3)) : Finset (Fin (m+1)) :=
  univ.image (blockVertex m i)

def center (m : ℕ) : Fin (m+1) := ⟨0, by omega⟩

theorem blockVertex_injective (m : ℕ) (i : Fin (m / 3)) :
    Function.Injective (blockVertex m i) := by
  intro j k he
  apply Fin.ext
  have hh := congrArg Fin.val he
  change 3 * i.val + j.val + 1 = 3 * i.val + k.val + 1 at hh
  omega

theorem block_card (m : ℕ) (i : Fin (m / 3)) : (block m i).card = 3 := by
  rw [block, card_image_of_injective _ (blockVertex_injective m i), card_univ, Fintype.card_fin]

theorem center_not_mem_block (m : ℕ) (i : Fin (m / 3)) : center m ∉ block m i := by
  intro hc
  obtain ⟨j,_,he⟩ := mem_image.mp hc
  have hh := congrArg Fin.val he
  change 3 * i.val + j.val + 1 = 0 at hh
  omega

theorem index_eq_of_mem {m : ℕ} {i k : Fin (m / 3)} {z : Fin (m+1)}
    (hi : z ∈ block m i) (hk : z ∈ block m k) : i = k := by
  obtain ⟨j,_,hj⟩ := mem_image.mp hi
  obtain ⟨l,_,hl⟩ := mem_image.mp hk
  have he := congrArg Fin.val (hj.trans hl.symm)
  change 3 * i.val + j.val + 1 = 3 * k.val + l.val + 1 at he
  have hjb := j.isLt
  have hlb := l.isLt
  apply Fin.ext
  omega

theorem block_injective (m : ℕ) : Function.Injective (block m) := by
  intro i k he
  have hi : blockVertex m i 0 ∈ block m i := mem_image.mpr ⟨0,mem_univ _,rfl⟩
  apply index_eq_of_mem hi
  rwa [← he]

def matching (m : ℕ) : Finset (Finset (Fin (m+1))) :=
  univ.image (block m)

theorem matching_card (m : ℕ) : (matching m).card = m / 3 := by
  rw [matching, card_image_of_injective _ (block_injective m), card_univ, Fintype.card_fin]

theorem matching_uniform (m : ℕ) : (matching m).IsUniform 3 := by
  intro e he
  obtain ⟨i,_,rfl⟩ := mem_image.mp he
  exact block_card m i

theorem center_not_mem_matching (m : ℕ) : ∀ e ∈ matching m, center m ∉ e := by
  intro e he
  obtain ⟨i,_,rfl⟩ := mem_image.mp he
  exact center_not_mem_block m i

theorem matching_disjoint (m : ℕ) :
    ∀ A ∈ matching m, ∀ B ∈ matching m, A ≠ B → Disjoint A B := by
  intro A hA B hB hne
  obtain ⟨i,_,rfl⟩ := mem_image.mp hA
  obtain ⟨k,_,rfl⟩ := mem_image.mp hB
  apply disjoint_left.mpr
  intro z hi hk
  exact hne (congrArg (block m) (index_eq_of_mem hi hk))

def family (m : ℕ) : Finset (Finset (Fin (m+1))) := star (center m) ∪ matching m

theorem family_uniform (m : ℕ) : (family m).IsUniform 3 := by
  intro e he
  rcases mem_union.mp he with he | he
  · exact star_uniform _ e he
  · exact matching_uniform m e he

theorem family_card (m : ℕ) : (family m).card = m.choose 2 + m / 3 := by
  unfold family
  rw [card_union_of_disjoint, star_card, matching_card, Fintype.card_fin]
  · simp
  · apply disjoint_left.mpr
    intro e hs hm
    exact center_not_mem_matching m e hm (apex_mem hs)

theorem family_avoids (m : ℕ) : ¬ (family m).HasRepeatedDisjointUnion :=
  star_union_matching_avoids (center m) (matching m) (matching_uniform m)
    (center_not_mem_matching m) (matching_disjoint m)

/-- The complete finite lower formula in the manuscript, for the actual
imported upstream extremal number, on every n≥1. -/
theorem lower_bound (n : ℕ) (hn : 1 ≤ n) :
    (n-1).choose 2 + (n-1) / 3 ≤
      Hypergraph.extremalNumber n 3 (fun H => ¬ H.HasRepeatedDisjointUnion) := by
  classical
  cases n with
  | zero => omega
  | succ m =>
    simp only [Nat.add_sub_cancel]
    rw [← family_card]
    unfold Hypergraph.extremalNumber
    apply Finset.le_sup (f := Finset.card)
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_,family_avoids m⟩
    intro e he
    exact mem_powersetCard.mpr ⟨subset_univ e,family_uniform m e he⟩

end Erdos643R3.StarMatching

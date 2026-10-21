import Openmath.Erdos642.Proofs.DenseMask20261019.GallaiTwins

namespace Erdos642.DenseMask20261019.GallaiNormalization

open GallaiTwins

variable {V : Type*}

/-- Restoring singly deleted copies yields a deletion set consisting of whole original
fibers, contained in the initial deletion set, with no larger actual obstruction. -/
theorem exists_normalized_deletion [Fintype V] (G : SimpleGraph V) (A : Set V)
    (D : Set (CopyVertex A)) :
    ∃ U : Set V, project ⁻¹' U ⊆ D ∧
      obstruction (doubled G A) (project ⁻¹' U) ≤ obstruction (doubled G A) D := by
  classical
  generalize hn : D.ncard = n
  induction n using Nat.strong_induction_on generalizing D with
  | h n ih =>
    by_cases hbal : ∀ u v : CopyVertex A, project u = project v → u ∈ D → v ∈ D
    · let U : Set V := {x | (Sum.inl x : CopyVertex A) ∈ D}
      have he : project ⁻¹' U = D := by
        ext u
        change (Sum.inl (project u) : CopyVertex A) ∈ D ↔ u ∈ D
        constructor
        · exact hbal (Sum.inl (project u)) u rfl
        · exact hbal u (Sum.inl (project u)) rfl
      refine ⟨U, ?_, ?_⟩ <;> rw [he]
    · push_neg at hbal
      obtain ⟨u, v, hp, hu, hv⟩ := hbal
      have hrestore := doubled_restore_obstruction G A D u v hu hv hp
      have hnot : u ∉ D \ {u} := by simp
      have hins : insert u (D \ {u}) = D := by
        ext w
        simp
        aesop
      have hcard := Set.ncard_insert_of_notMem (s := D \ {u}) hnot
      rw [hins] at hcard
      have hsmall : (D \ {u}).ncard < n := by omega
      obtain ⟨U, hsub, hcost⟩ := ih (D \ {u}).ncard hsmall (D \ {u}) rfl
      exact ⟨U, hsub.trans Set.diff_subset, hcost.trans hrestore⟩

end Erdos642.DenseMask20261019.GallaiNormalization

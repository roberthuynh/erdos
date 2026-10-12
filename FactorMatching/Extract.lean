import FactorMatching.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open SimpleGraph Function

namespace Erdos585.FactorMatching

universe u
variable {V : Type u} {q : ℕ} {G : SimpleGraph V}
variable (M : (gadget q G).Subgraph) (hM : M.IsPerfectMatching)
include hM

theorem matched_unique {x y z : Vertex q G} (hxy : M.Adj x y) (hxz : M.Adj x z) :
    y = z :=
  (Subgraph.isPerfectMatching_iff.mp hM x).unique hxy hxz

theorem slot_unique_stub (v : V) (i : Fin q) :
    ∃! d : G.Dart, M.Adj (.inl (v, i)) (.inr d) := by
  obtain ⟨x, hx, hu⟩ := Subgraph.isPerfectMatching_iff.mp hM (.inl (v, i))
  cases x with
  | inl s => exact False.elim (M.adj_sub hx)
  | inr d =>
    refine ⟨d, hx, ?_⟩
    intro e he
    exact Sum.inr.inj (hu (.inr e) he)

def chosenStub (v : V) (i : Fin q) : G.Dart :=
  Classical.choose (slot_unique_stub M hM v i).exists

theorem chosenStub_matched (v : V) (i : Fin q) :
    M.Adj (.inl (v, i)) (.inr (chosenStub M hM v i)) :=
  Classical.choose_spec (slot_unique_stub M hM v i).exists

@[simp] theorem chosenStub_fst (v : V) (i : Fin q) :
    (chosenStub M hM v i).fst = v :=
  M.adj_sub (chosenStub_matched M hM v i)

theorem twin_slot {v : V} {i : Fin q} {d : G.Dart}
    (hd : M.Adj (.inl (v, i)) (.inr d)) :
    ∃ j : Fin q, M.Adj (.inl (d.snd, j)) (.inr d.symm) := by
  obtain ⟨x, hx, _⟩ := Subgraph.isPerfectMatching_iff.mp hM (.inr d.symm)
  cases x with
  | inl s =>
    have hs : d.snd = s.1 := M.adj_sub hx
    obtain ⟨v, j⟩ := s
    dsimp at hs
    subst v
    exact ⟨j, hx.symm⟩
  | inr e =>
    have he : e = d := by simpa using M.adj_sub hx
    have hback : M.Adj (.inr d) (.inr d.symm) := by simpa only [he] using hx.symm
    have hbad := matched_unique M hM hd.symm hback
    cases hbad

def extractedNext (v : V) (i : Fin q) : V := (chosenStub M hM v i).snd

theorem extracted_original (v : V) (i : Fin q) :
    G.Adj v (extractedNext M hM v i) := by
  have h := (chosenStub M hM v i).adj
  simpa only [chosenStub_fst, extractedNext] using h

theorem extracted_injective (v : V) : Injective (extractedNext M hM v) := by
  intro i j hij
  have hd : chosenStub M hM v i = chosenStub M hM v j := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext ((chosenStub_fst M hM v i).trans (chosenStub_fst M hM v j).symm) hij
  have hslot := matched_unique M hM (chosenStub_matched M hM v i).symm
    (hd.symm ▸ (chosenStub_matched M hM v j).symm)
  exact congrArg Prod.snd (Sum.inl.inj hslot)

theorem extracted_reverse {v w : V} (hvw : ∃ i, extractedNext M hM v i = w) :
    ∃ j, extractedNext M hM w j = v := by
  obtain ⟨i, hi⟩ := hvw
  let d := chosenStub M hM v i
  have hd : M.Adj (.inl (v, i)) (.inr d) := chosenStub_matched M hM v i
  obtain ⟨j, hj⟩ := twin_slot M hM hd
  have hds : d.snd = w := hi
  have hj' : M.Adj (.inl (w, j)) (.inr d.symm) := by simpa only [hds] using hj
  have he : chosenStub M hM w j = d.symm :=
    Sum.inr.inj (matched_unique M hM (chosenStub_matched M hM w j) hj')
  refine ⟨j, ?_⟩
  change (chosenStub M hM w j).snd = v
  rw [he]
  exact chosenStub_fst M hM v i

def extracted : LocalSystem q G where
  next := extractedNext M hM
  original := extracted_original M hM
  injective := extracted_injective M hM
  reciprocal := fun _ _ => ⟨extracted_reverse M hM, extracted_reverse M hM⟩

theorem factor_of_matching [Fintype V] : SpanningFactor q G := by
  classical
  exact (factor_iff_localSystem q G).mpr ⟨extracted M hM⟩

end Erdos585.FactorMatching

import GeneralStar.Types
import Mathlib.Data.List.GetD

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

open Finset
namespace Erdos585.GeneralStar

def rawWord (slot : ℕ → ℕ) (xs : List ℕ) : List ℕ :=
  xs.flatMap fun z => List.replicate (slot z) z

@[simp] theorem rawWord_cons (slot : ℕ → ℕ) (z : ℕ) (zs : List ℕ) :
    rawWord slot (z::zs)=List.replicate (slot z) z ++ rawWord slot zs := rfl

theorem allocateWord_eq_take (slot : ℕ → ℕ) (xs : List ℕ) (m : ℕ) :
    allocateWord slot m xs = (rawWord slot xs).take m := by
  induction xs generalizing m with
  | nil => simp [allocateWord,rawWord]
  | cons z zs ih =>
    have hsub : m-min (slot z) m=m-slot z := by omega
    rw [allocateWord,rawWord_cons,List.take_append,List.length_replicate,List.take_replicate,ih,hsub]
    rw [Nat.min_comm]

theorem rawWord_length (slot : ℕ → ℕ) (xs : List ℕ) :
    (rawWord slot xs).length=(xs.map slot).sum := by
  induction xs with
  | nil => rfl
  | cons z zs ih => simp only [rawWord_cons,List.length_append,List.length_replicate,List.map_cons,List.sum_cons,ih]

theorem allocateWord_length (slot : ℕ → ℕ) (xs : List ℕ) (m : ℕ)
    (hm : m ≤ (xs.map slot).sum) : (allocateWord slot m xs).length=m := by
  rw [allocateWord_eq_take,List.length_take,rawWord_length,Nat.min_eq_left hm]

theorem rawWord_mem (slot : ℕ → ℕ) (xs : List ℕ) (z : ℕ)
    (hz : z ∈ rawWord slot xs) : z ∈ xs := by
  obtain ⟨a,ha,hza⟩ := List.mem_flatMap.mp hz
  have heq : z=a := (List.mem_replicate.mp hza).2
  simpa [heq] using ha

theorem getD_mem_of_lt (xs : List ℕ) (i : ℕ) (hi : i < xs.length) :
    xs.getD i 0 ∈ xs := by
  rw [List.getD_eq_getElem xs 0 hi]
  exact List.getElem_mem hi

theorem getD_take_of_lt (xs : List ℕ) (i m : ℕ) (hi : i < m) :
    (xs.take m).getD i 0=xs.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_take,if_pos hi]

/-- Equal entries lie in one original contiguous run of length at most r. -/
theorem rawWord_equal_span (slot : ℕ → ℕ) (r : ℕ) (xs : List ℕ)
    (hn : xs.Nodup) (hc : ∀ z ∈ xs,slot z ≤ r)
    (i j : ℕ) (hi : i < (rawWord slot xs).length)
    (hj : j < (rawWord slot xs).length)
    (heq : (rawWord slot xs).getD i 0=(rawWord slot xs).getD j 0) :
    i < j+r ∧ j < i+r := by
  induction xs generalizing i j with
  | nil => simp [rawWord] at hi
  | cons z zs ih =>
    obtain ⟨hz,hnzs⟩ := List.nodup_cons.mp hn
    have hcz := hc z (by simp)
    have hct : ∀ a ∈ zs,slot a ≤ r := fun a ha => hc a (by simp [ha])
    rw [rawWord_cons,List.length_append,List.length_replicate] at hi hj
    change (List.replicate (slot z) z ++ rawWord slot zs).getD i 0 =
      (List.replicate (slot z) z ++ rawWord slot zs).getD j 0 at heq
    by_cases hzi : i < slot z
    · by_cases hzj : j < slot z
      · omega
      · have hleft : (List.replicate (slot z) z ++ rawWord slot zs).getD i 0=z := by
          rw [List.getD_append _ _ _ _ (by simpa using hzi)]
          simp [List.getD_eq_getElem?_getD,List.getElem?_replicate,hzi]
        have hright : (List.replicate (slot z) z ++ rawWord slot zs).getD j 0 =
            (rawWord slot zs).getD (j-slot z) 0 := by
          rw [List.getD_append_right _ _ _ _ (by simp only [List.length_replicate];omega),
            List.length_replicate]
        rw [hleft,hright] at heq
        have hm := getD_mem_of_lt (rawWord slot zs) (j-slot z) (by omega)
        rw [← heq] at hm
        exact (hz (rawWord_mem slot zs z hm)).elim
    · by_cases hzj : j < slot z
      · have hleft : (List.replicate (slot z) z ++ rawWord slot zs).getD i 0 =
            (rawWord slot zs).getD (i-slot z) 0 := by
          rw [List.getD_append_right _ _ _ _ (by simp only [List.length_replicate];omega),
            List.length_replicate]
        have hright : (List.replicate (slot z) z ++ rawWord slot zs).getD j 0=z := by
          rw [List.getD_append _ _ _ _ (by simpa using hzj)]
          simp [List.getD_eq_getElem?_getD,List.getElem?_replicate,hzj]
        rw [hleft,hright] at heq
        have hm := getD_mem_of_lt (rawWord slot zs) (i-slot z) (by omega)
        rw [heq] at hm
        exact (hz (rawWord_mem slot zs z hm)).elim
      · rw [List.getD_append_right _ _ _ _ (by simp only [List.length_replicate];omega),
          List.getD_append_right _ _ _ _ (by simp only [List.length_replicate];omega),
          List.length_replicate] at heq
        have hs := ih hnzs hct (i-slot z) (j-slot z) (by omega) (by omega) heq
        omega

theorem allocateWord_residue_injective (slot : ℕ → ℕ) (xs : List ℕ) (r t : ℕ)
    (_hr : 0 < r) (ht : t < r) (hn : xs.Nodup)
    (hc : ∀ z ∈ xs,slot z ≤ r) (hslots : r*r ≤ (xs.map slot).sum) :
    Set.InjOn (fun j => (allocateWord slot (r*r) xs).getD (t+j*r) 0)
      (range r : Set ℕ) := by
  intro i hi j hj heq
  have hi' : i < r := mem_range.mp hi
  have hj' : j < r := mem_range.mp hj
  have hip : t+i*r < r*r := by nlinarith
  have hjp : t+j*r < r*r := by nlinarith
  dsimp only at heq
  rw [allocateWord_eq_take,getD_take_of_lt _ _ _ hip,getD_take_of_lt _ _ _ hjp] at heq
  have hl := rawWord_length slot xs
  have hs := rawWord_equal_span slot r xs hn hc (t+i*r) (t+j*r)
    (by nlinarith) (by nlinarith) heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · nlinarith
  · nlinarith

theorem rawWord_count (slot : ℕ → ℕ) (xs : List ℕ) (hn : xs.Nodup) (z : ℕ) :
    (rawWord slot xs).count z = if z ∈ xs then slot z else 0 := by
  induction xs with
  | nil => simp [rawWord]
  | cons a as ih =>
    obtain ⟨ha,hnas⟩ := List.nodup_cons.mp hn
    by_cases hz : z=a
    · subst z
      rw [rawWord_cons,List.count_append,ih hnas]
      simp [ha]
    · rw [rawWord_cons,List.count_append,ih hnas]
      simp [List.count_replicate,hz,Ne.symm hz]

theorem allocateWord_count_le (slot : ℕ → ℕ) (xs : List ℕ)
    (hn : xs.Nodup) (m z : ℕ) : (allocateWord slot m xs).count z ≤ slot z := by
  rw [allocateWord_eq_take]
  have hs := (List.take_sublist m (rawWord slot xs)).count_le z
  rw [rawWord_count slot xs hn z] at hs
  split_ifs at hs <;> omega

end Erdos585.GeneralStar

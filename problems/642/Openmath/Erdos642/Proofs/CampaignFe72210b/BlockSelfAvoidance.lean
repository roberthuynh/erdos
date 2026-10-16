import Openmath.Erdos642.Proofs.CampaignFe72210b.GoodBlockExtension

namespace Erdos642.FiniteMarkov
open PathCoordinates PathAvoidance
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BlockSelfAvoidance

@[reducible] def blockLength (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | r+1 => k + blockLength k r

@[simp] theorem blockLength_eq (k r : ℕ) : blockLength k r = r*k := by
  induction r with
  | zero => simp [blockLength]
  | succ r ih => simp [blockLength, ih, Nat.add_mul, Nat.add_comm]

def olderExposure (k : ℕ) : (r : ℕ) → V → Path V (blockLength k r) → Finset V
  | 0, _, _ => ∅
  | r+1, x, p => visited x (PathSplit.split (blockLength k r) k p).1

def Success (C : Chain V) (k : ℕ) (β H : ℝ) (r : ℕ)
    (x : V) (p : Path V (blockLength k r)) : Prop :=
  actualSA x p ∧ C.Good k β H (olderExposure k r x p) (C.endpoint x p)
end BlockSelfAvoidance
namespace Chain
open BlockSelfAvoidance
variable (C : Chain V)

theorem olderExposure_append (k r : ℕ) (x : V)
    (p : Path V (blockLength k r)) (s : Path V k) :
    olderExposure k (r+1) x (C.append p s) = visited x p := by
  simp only [olderExposure, C.split_append]

theorem visited_append_sdiff_card_le {m n : ℕ} (x : V) (p : Path V m) (s : Path V n) :
    ((visited x (C.append p s)) \ visited x p).card ≤ n := by
  have hsub : (visited x (C.append p s)) \ visited x p ⊆ (future s).toFinset := by
    intro a ha
    simp only [Finset.mem_sdiff, mem_visited, C.future_append,
      List.mem_cons, List.mem_append, List.mem_toFinset] at ha ⊢
    tauto
  have hc := Finset.card_le_card hsub
  have hf := List.toFinset_card_le (future s)
  rw [future_length] at hf
  exact hc.trans hf

theorem olderExposure_geometry (C : Chain V) (k r : ℕ) (hk : 1 ≤ k) (x : V)
    (p : Path V (blockLength k r)) :
    olderExposure k r x p ⊆ visited x p ∧
      ((visited x p) \ olderExposure k r x p).card ≤ k := by
  cases r with
  | zero =>
    constructor
    · exact Finset.empty_subset _
    · have h := visited_card_le x p
      simp only [olderExposure, Finset.sdiff_empty, blockLength] at h ⊢
      omega
  | succ r =>
    let a := (PathSplit.split (blockLength k r) k p).1
    let s := (PathSplit.split (blockLength k r) k p).2
    have heq : C.append a s = p := C.append_split (blockLength k r) k p
    rw [← heq, C.olderExposure_append]
    exact ⟨C.visited_prefix_subset x a s, C.visited_append_sdiff_card_le x a s⟩

/-- Actual long self-avoidance from local hitting, collision, column, and mixing estimates. -/
theorem block_self_avoidance (k q : ℕ) (β H J M N R : ℝ)
    (hk : 1 ≤ k) (_hq : 1 ≤ q) (hβ : 0 < β) (hβupper : β ≤ 1/6)
    (hN : 0 < N) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hlocal : ∀ v (S : Finset V), S.card ≤ k → C.eventMass k (actualHit S) v ≤ H)
    (hcollision : ∀ v, C.eventMass k (fun z s => ¬ actualSA z s) v ≤ J)
    (hHJ : H+J ≤ β)
    (hcol : ∀ t ∈ Finset.Icc 1 k, ∀ a, ∑ v, (C.transition^t) v a ≤ R)
    (hmix : ∀ x y, (C.transition^k) x y ≤ M/N)
    (horder : M*R*(k:ℝ)*((q*k+1:ℕ):ℝ) ≤ β^2*N) (x : V) :
    (1-3*β)^q ≤ C.eventMass (q*k) actualSA x := by
  classical
  let c : ℝ := 1-3*β
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hind : ∀ r, r ≤ q → c^r ≤
      C.eventMass (blockLength k r) (Success C k β H r) x := by
    intro r
    induction r with
    | zero =>
      intro _
      have hg := C.good_empty k β H hβ.le hlocal x
      simp [eventMass, Success, olderExposure, blockLength, actualSA, future, weight, endpoint, hg]
    | succ r ih =>
      intro hr
      have hrq : r ≤ q := by omega
      have hprev := ih hrq
      have hext : ∀ (p : Path V (blockLength k r)), actualSA x p →
          ∀ O : Finset V, O ⊆ visited x p → ((visited x p) \ O).card ≤ k →
          C.Good k β H O (C.endpoint x p) → (visited x p).card ≤ q*k+1 →
          1-3*β ≤ C.eventMass k (fun z s => actualSA x (C.append p s) ∧
            C.Good k β H (visited x p) (C.endpoint z s)) (C.endpoint x p) := by
        rw [blockLength_eq]
        exact (C.good_block_extension k q r β H J M N R hβ hN hM hR hlocal
            hcollision hHJ hcol hmix horder x)
      have hstep : c * C.eventMass (blockLength k r) (Success C k β H r) x ≤
          C.eventMass (blockLength k (r+1)) (Success C k β H (r+1)) x := by
        change c * C.eventMass (blockLength k r) (Success C k β H r) x ≤
          C.eventMass (k + blockLength k r) (Success C k β H (r+1)) x
        rw [C.eventMass_append_fubini (blockLength k r) k (Success C k β H (r+1)) x]
        unfold eventMass
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro p _
        by_cases hp : Success C k β H r x p
        · simp only [hp, if_true]
          have hg := C.olderExposure_geometry k r hk x p
          have hsize : (visited x p).card ≤ q*k+1 := by
            have hv := visited_card_le x p
            have hl := blockLength_eq k r
            have hm : r*k ≤ q*k := Nat.mul_le_mul_right k hrq
            omega
          have hb := hext p hp.1 (olderExposure k r x p) hg.1 hg.2 hp.2 hsize
          have hmass : c ≤ C.eventMass k
              (fun _ s => Success C k β H (r+1) x (C.append p s)) (C.endpoint x p) := by
            calc
              c = 1-3*β := rfl
              _ ≤ C.eventMass k (fun z s => actualSA x (C.append p s) ∧
                  C.Good k β H (visited x p) (C.endpoint z s)) (C.endpoint x p) := hb
              _ = C.eventMass k (fun _ s => Success C k β H (r+1) x (C.append p s))
                  (C.endpoint x p) := by
                unfold eventMass
                apply Finset.sum_congr rfl
                intro s _
                simp only [Success, C.olderExposure_append, C.endpoint_append]
                split_ifs <;> rfl
          have hw := C.weight_nonneg x p
          simpa only [eventMass, mul_comm c] using mul_le_mul_of_nonneg_left hmass hw
        · simp only [hp, if_false, mul_zero]
          apply mul_nonneg (C.weight_nonneg x p)
          apply Finset.sum_nonneg
          intro s _
          split_ifs
          · exact C.weight_nonneg (C.endpoint x p) s
          · exact le_rfl
      have hmul := mul_le_mul_of_nonneg_left hprev hc
      have hpow : c^(r+1) = c*c^r := by rw [pow_succ]; ring
      rw [hpow]
      exact hmul.trans hstep
  have h := hind q le_rfl
  have hmono := C.eventMass_mono (Success C k β H q) actualSA
    (fun _ _ hs => hs.1) x
  have hf := h.trans hmono
  rw [← blockLength_eq k q]
  exact hf
end Chain
end Erdos642.FiniteMarkov

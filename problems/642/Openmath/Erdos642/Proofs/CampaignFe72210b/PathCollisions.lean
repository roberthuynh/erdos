import Openmath.Erdos642.Proofs.CampaignFe72210b.PathAvoidance

/-! Repeated coordinates under the genuine finite path law. -/

namespace Erdos642.FiniteMarkov

variable {V : Type*} [Fintype V]

namespace Chain

open PathCoordinates PathAvoidance

variable (C : Chain V)

/-- Appending an actual prefix exposes the genuine suffix coordinates. -/
theorem coordinate_append_add {m n : ℕ} (x : V) (p : Path V m) (q : Path V n)
    (i : ℕ) :
    coordinate x (C.append p q) (i + m) = coordinate (C.endpoint x p) q i := by
  induction m generalizing x with
  | zero => simp only [append, endpoint, Nat.add_zero]
  | succ m ih =>
    rcases p with ⟨y, p⟩
    simpa only [Nat.add_succ, append, coordinate, endpoint] using ih y p

theorem coordinate_append_cut {m n : ℕ} (x : V) (p : Path V m) (q : Path V n) :
    coordinate x (C.append p q) m = C.endpoint x p := by
  simpa only [Nat.zero_add, coordinate_zero] using C.coordinate_append_add x p q 0

variable [DecidableEq V]

/-- Actual path splitting, not an assumed joint marginal, controls a pair
of equal coordinates by the actual return diagonal. -/
theorem coordinate_repeat_mass_le_add (i n ell : ℕ) (hell : ell ≤ n) (b : ℝ)
    (hreturn : ∀ v : V, (C.transition ^ ell) v v ≤ b) (x : V) :
    C.eventMass (n + i)
      (fun z p => coordinate z p i = coordinate z p (i + ell)) x ≤ b := by
  classical
  rw [C.eventMass_append_fubini i n]
  have hconditional (p : Path V i) :
      C.eventMass n
        (fun _ q => coordinate x (C.append p q) i =
          coordinate x (C.append p q) (i + ell)) (C.endpoint x p) =
        (C.transition ^ ell) (C.endpoint x p) (C.endpoint x p) := by
    calc
      _ = C.eventMass n (fun z q => coordinate z q ell = z) (C.endpoint x p) := by
        unfold eventMass
        apply Finset.sum_congr rfl
        intro q _
        dsimp only
        have he : coordinate x (C.append p q) (i + ell) =
            coordinate (C.endpoint x p) q ell := by
          simpa only [Nat.add_comm] using C.coordinate_append_add x p q ell
        simp only [C.coordinate_append_cut, he, eq_comm]
      _ = (C.transition ^ ell) (C.endpoint x p) (C.endpoint x p) :=
        C.coordinate_marginal n ell hell (C.endpoint x p) (C.endpoint x p)
  simp_rw [hconditional]
  calc
    (∑ p : Path V i, C.weight x p *
        (C.transition ^ ell) (C.endpoint x p) (C.endpoint x p)) ≤
        ∑ p : Path V i, C.weight x p * b := by
      apply Finset.sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_left (hreturn _) (C.weight_nonneg x p)
    _ = b := by rw [← Finset.sum_mul, C.total_weight, one_mul]

theorem coordinate_repeat_mass_le (k i j : ℕ) (hij : i < j) (hjk : j ≤ k) (b : ℝ)
    (hreturn : ∀ v : V, (C.transition ^ (j - i)) v v ≤ b) (x : V) :
    C.eventMass k (fun z p => coordinate z p i = coordinate z p j) x ≤ b := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le (hij.le.trans hjk)
  have hk : k = n + i := by omega
  rcases hk with rfl
  have hell : j - i ≤ n := by omega
  have he : i + (j - i) = j := by omega
  simpa only [he] using
    C.coordinate_repeat_mass_le_add i n (j - i) hell b hreturn x

end Chain

namespace PathAvoidance

open PathCoordinates

omit [Fintype V] in
/-- Every failure of actual self-avoidance exposes two distinct time indices,
including time zero, with the same actual coordinate. -/
theorem not_actualSA_exists_repeat {n : ℕ} (x : V) (p : Path V n)
    (hbad : ¬ actualSA x p) :
    ∃ i j : ℕ, i < j ∧ j ≤ n ∧ coordinate x p i = coordinate x p j := by
  induction n generalizing x with
  | zero =>
    exfalso
    exact hbad (by simp [actualSA, future])
  | succ n ih =>
    rcases p with ⟨y, p⟩
    have hb : x ∈ y :: future p ∨ ¬ actualSA y p := by
      simpa only [actualSA, future, List.nodup_cons, not_and_or, not_not] using hbad
    rcases hb with hm | hs
    · have hm' : x ∈ future (n := n + 1) ((y, p) : Path V (n + 1)) := hm
      obtain ⟨j, hj, hjn, he⟩ :=
        (mem_future_iff (n := n + 1) x x ((y, p) : Path V (n + 1))).mp hm'
      exact ⟨0, j, by omega, hjn, by change x = _; exact he.symm⟩
    · obtain ⟨i, j, hij, hjn, he⟩ := ih y p hs
      exact ⟨i + 1, j + 1, by omega, by omega, he⟩

end PathAvoidance

namespace Chain

open PathCoordinates PathAvoidance

variable (C : Chain V) [DecidableEq V]

/-- Union over actual repeated coordinate pairs, grouped by separation.
There are at most k pairs of each positive separation. -/
theorem not_actualSA_mass_le_return_sum (k : ℕ) (b : ℕ → ℝ)
    (hb : ∀ ell ∈ Finset.Icc 1 k, 0 ≤ b ell)
    (hreturn : ∀ ell ∈ Finset.Icc 1 k, ∀ v : V,
      (C.transition ^ ell) v v ≤ b ell) (x : V) :
    C.eventMass k (fun z p => ¬ actualSA z p) x ≤
      (k : ℝ) * ∑ ell ∈ Finset.Icc 1 k, b ell := by
  classical
  have hmono := C.eventMass_mono (n := k) (fun z p => ¬ actualSA z p)
    (fun z p => ∃ ell ∈ Finset.Icc 1 k, ∃ i ∈ Finset.range (k + 1 - ell),
      coordinate z p i = coordinate z p (i + ell))
    (by
      intro z p hbad
      obtain ⟨i, j, hij, hjk, he⟩ := not_actualSA_exists_repeat z p hbad
      have hcut : i + (j - i) = j := by omega
      refine ⟨j - i, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
        i, Finset.mem_range.mpr (by omega), ?_⟩
      simpa only [hcut] using he) x
  apply hmono.trans
  apply (C.eventMass_biUnion_le (Finset.Icc 1 k)
    (fun ell z p => ∃ i ∈ Finset.range (k + 1 - ell),
      coordinate z p i = coordinate z p (i + ell)) x).trans
  calc
    (∑ ell ∈ Finset.Icc 1 k, C.eventMass k
        (fun z p => ∃ i ∈ Finset.range (k + 1 - ell),
          coordinate z p i = coordinate z p (i + ell)) x) ≤
        ∑ ell ∈ Finset.Icc 1 k, ∑ _i ∈ Finset.range (k + 1 - ell), b ell := by
      apply Finset.sum_le_sum
      intro ell hell
      apply (C.eventMass_biUnion_le (Finset.range (k + 1 - ell))
        (fun i z p => coordinate z p i = coordinate z p (i + ell)) x).trans
      apply Finset.sum_le_sum
      intro i hi
      have hell' := Finset.mem_Icc.mp hell
      have hi' := Finset.mem_range.mp hi
      have he : i + ell - i = ell := by omega
      apply C.coordinate_repeat_mass_le k i (i + ell) (by omega) (by omega) (b ell)
      intro v
      simpa only [he] using hreturn ell hell v
    _ = ∑ ell ∈ Finset.Icc 1 k, ((k + 1 - ell : ℕ) : ℝ) * b ell := by
      apply Finset.sum_congr rfl
      intro ell _
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ∑ ell ∈ Finset.Icc 1 k, (k : ℝ) * b ell := by
      apply Finset.sum_le_sum
      intro ell hell
      have hell' := Finset.mem_Icc.mp hell
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show k + 1 - ell ≤ k by omega))
        (hb ell hell)
    _ = (k : ℝ) * ∑ ell ∈ Finset.Icc 1 k, b ell := (Finset.mul_sum _ _ _).symm

end Chain

end Erdos642.FiniteMarkov

import Mathlib
import Openmath.Erdos643R3.PwArith

/-!
# Branch-and-bound checkers for pw2312 Computations C1 and C2, and their soundness

The finite computations of the 23/12 argument §4 are re-expressed as branch-and-bound (B&B)
certificates that the Lean kernel re-derives (`decide +kernel` in `PwC1`, `PwC2`; no `native_decide`). Nothing is
read from data: the checkers below recompute every bound.

* All arithmetic is in `ℕ` at the scale `DD = 1200000`: a box bound is a sum of floors `⌊DD · term⌋` of lower bounds
  of the terms of `Φ` (`sN`, `vN`, `e4N`), and upper bounds of `−κ` use ceilings (`kterm`). `DD` is divisible by 12,
  so `23/12` and `11/12` are exact (`2300000`, `1100000`).
* Box lower bounds (pw2312 (E2) and (E4)): on a box `[fl,fh] × [gl,gh]` of the two type-1 counts of a relation,
  `S(f, g, y) + S(g, f, x) ≥ max(S(fl, gh, y) + S(gl, fh, x), E4R(fl, gl, x, y))` (the second only when
  `fl, gl ≥ 1`), and `1/(1 + f + g + t) ≥ 1/(1 + fh + gh + t)`.
* `bb` / `bb2`: fuel-bounded recursion; a box is accepted if every profile in it violates (F), or (C1 only) one
  relation is big on the whole box, or the bound reaches the target; otherwise it is split in two.
* Soundness: `bb_sound` (C1: every feasible profile in the box with no big relation has `Φ ≥ 23/12`) and `bb2_sound`
  (C2: with `ρ_0` big, `Φ ≥ 23/12`), by induction on the fuel; the split rule is irrelevant to soundness.
-/

set_option autoImplicit false

namespace Erdos643R3
namespace PwCheck

open Erdos643R3.Pw2312

/-! ## Big relations -/

/-- `ρ_0` (`R_c`) is big: both type-1 counts `≥ 23`. -/
def Big0 (π : Profile) : Prop := 23 ≤ π.f0 ∧ 23 ≤ π.g1
/-- `ρ_1` (`R_a`) is big. -/
def Big1 (π : Profile) : Prop := 23 ≤ π.f1 ∧ 23 ≤ π.g2
/-- `ρ_2` (`R_b`) is big. -/
def Big2 (π : Profile) : Prop := 23 ≤ π.f2 ∧ 23 ≤ π.g0

/-! ## Scaled term evaluators in `ℕ` -/

/-- The scale. -/
def DD : ℕ := 1200000

/-- `⌊DD · S(p,q,y)⌋`. -/
def sN (p q y : ℕ) : ℕ := DD * (p * p) / (2 * (p + p * q + y))

/-- `⌊DD / (1 + m)⌋`. -/
def vN (m : ℕ) : ℕ := DD / (1 + m)

/-- `⌊DD · max(0, E4R p q x y)⌋`, computed over the common denominator `2(1+p)²(1+q)²`. -/
def e4N (p q x y : ℕ) : ℕ :=
  DD * (2 * ((1 + p) * (1 + p)) * ((1 + q) * (1 + q)) -
      ((1 + p) * ((1 + q) * (1 + q)) + (1 + q) * ((1 + p) * (1 + p)) + y * ((1 + p) * (1 + p)) +
        x * ((1 + q) * (1 + q)))) / (2 * ((1 + p) * (1 + p)) * ((1 + q) * (1 + q)))

/-- Lower bound of `DD · (S(f,g,y) + S(g,f,x))` on the box `[fl,fh] × [gl,gh]`. -/
def relN (fl fh gl gh x y : ℕ) : ℕ :=
  if 1 ≤ fl ∧ 1 ≤ gl then max (sN fl gh y + sN gl fh x) (e4N fl gl x y) else sN fl gh y + sN gl fh x

theorem sN_le (p q y : ℕ) : (sN p q y : ℚ) ≤ 1200000 * S p q y := by
  unfold sN DD
  refine (Nat.cast_div_le).trans (le_of_eq ?_)
  unfold S; push_cast; ring

theorem vN_le (m : ℕ) : (vN m : ℚ) ≤ 1200000 * (1 / (1 + (m : ℚ))) := by
  unfold vN DD
  refine (Nat.cast_div_le).trans (le_of_eq ?_)
  push_cast; ring

theorem E4R_eq (p q x y : ℕ) :
    E4R p q x y = (2 * ((1 + (p : ℚ)) * (1 + p)) * ((1 + (q : ℚ)) * (1 + q)) -
      ((1 + (p : ℚ)) * ((1 + (q : ℚ)) * (1 + q)) + (1 + (q : ℚ)) * ((1 + (p : ℚ)) * (1 + p)) +
        y * ((1 + (p : ℚ)) * (1 + p)) + x * ((1 + (q : ℚ)) * (1 + q)))) /
      (2 * ((1 + (p : ℚ)) * (1 + p)) * ((1 + (q : ℚ)) * (1 + q))) := by
  unfold E4R
  have hp : (0 : ℚ) < 1 + p := by positivity
  have hq : (0 : ℚ) < 1 + q := by positivity
  field_simp
  ring

theorem e4N_le (p q x y : ℕ) : (e4N p q x y : ℚ) ≤ 1200000 * max 0 (E4R p q x y) := by
  unfold e4N DD
  set M : ℕ := 2 * ((1 + p) * (1 + p)) * ((1 + q) * (1 + q)) with hM
  set A : ℕ := (1 + p) * ((1 + q) * (1 + q)) + (1 + q) * ((1 + p) * (1 + p)) + y * ((1 + p) * (1 + p)) +
    x * ((1 + q) * (1 + q)) with hA
  by_cases hAM : A ≤ M
  · refine (Nat.cast_div_le).trans ?_
    have hc : ((1200000 * (M - A) : ℕ) : ℚ) = 1200000 * ((M : ℚ) - A) := by
      rw [Nat.cast_mul, Nat.cast_sub hAM]; norm_num
    rw [hc]
    have hE : E4R p q x y = ((M : ℚ) - A) / M := by
      rw [E4R_eq, hM, hA]; push_cast; ring
    rw [hE]
    have hMpos : (0 : ℚ) < M := by rw [hM]; positivity
    calc 1200000 * ((M : ℚ) - A) / M = 1200000 * (((M : ℚ) - A) / M) := by ring
      _ ≤ 1200000 * max 0 (((M : ℚ) - A) / M) := by
          apply mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
  · have h0 : M - A = 0 := by omega
    rw [h0]
    simp only [mul_zero, Nat.zero_div, Nat.cast_zero]
    exact mul_nonneg (by norm_num) (le_max_left _ _)

/-- Soundness of the relation bound on a box. -/
theorem relN_le {fl fh gl gh f g : ℕ} (x y : ℕ) (hf : fl ≤ f ∧ f ≤ fh) (hg : gl ≤ g ∧ g ≤ gh) :
    (relN fl fh gl gh x y : ℚ) ≤ 1200000 * (S f g y + S g f x) := by
  have hA : ((sN fl gh y + sN gl fh x : ℕ) : ℚ) ≤ 1200000 * (S f g y + S g f x) := by
    have h1 := sN_le fl gh y
    have h2 := sN_le gl fh x
    have h3 := S_corner (y := y) (y' := y) hf.1 hg.2 le_rfl
    have h4 := S_corner (y := x) (y' := x) hg.1 hf.2 le_rfl
    push_cast
    nlinarith
  unfold relN
  split_ifs with h
  · rw [Nat.cast_max]
    refine max_le hA ?_
    refine (e4N_le fl gl x y).trans ?_
    have hE := (E4R_mono x y hf.1 hg.1).trans (E4 x y (le_trans h.1 hf.1) (le_trans h.2 hg.1))
    have hS : 0 ≤ S f g y + S g f x := add_nonneg (S_nonneg _ _ _) (S_nonneg _ _ _)
    apply mul_le_mul_of_nonneg_left (max_le hS hE) (by norm_num)
  · exact hA

/-! ## (F) on boxes -/

/-- Status of `x + t` for `x ∈ [lo, hi]`: `1` surely positive, `0` surely zero, `2` unknown. -/
def st (lo hi t : ℕ) : ℕ := if 1 ≤ t ∨ 1 ≤ lo then 1 else if hi = 0 then 0 else 2

/-- The two sides of a relation have surely different (F)-status. -/
def mism (a c : ℕ) : Bool := (a == 0 && c == 1) || (a == 1 && c == 0)

theorem mism_sound {xl xh x t yl yh y s : ℕ} (hx : xl ≤ x ∧ x ≤ xh) (hy : yl ≤ y ∧ y ≤ yh)
    (h : mism (st xl xh t) (st yl yh s) = true) : ¬ (1 ≤ x + t ↔ 1 ≤ y + s) := by
  unfold mism st at h
  intro hiff
  split_ifs at h <;> simp at h <;>
  · by_cases hA : 1 ≤ x + t
    · have := hiff.mp hA; omega
    · have : ¬ 1 ≤ y + s := fun hB => hA (hiff.mpr hB); omega

/-! ## C1 boxes -/

/-- A box of the six type-1 counts (cyclic coordinates). -/
structure Box where
  f0l : ℕ
  f0h : ℕ
  g0l : ℕ
  g0h : ℕ
  f1l : ℕ
  f1h : ℕ
  g1l : ℕ
  g1h : ℕ
  f2l : ℕ
  f2h : ℕ
  g2l : ℕ
  g2h : ℕ

/-- `π` lies in the box. -/
def Box.mem (b : Box) (π : Profile) : Prop :=
  (b.f0l ≤ π.f0 ∧ π.f0 ≤ b.f0h) ∧ (b.g0l ≤ π.g0 ∧ π.g0 ≤ b.g0h) ∧ (b.f1l ≤ π.f1 ∧ π.f1 ≤ b.f1h) ∧
    (b.g1l ≤ π.g1 ∧ π.g1 ≤ b.g1h) ∧ (b.f2l ≤ π.f2 ∧ π.f2 ≤ b.f2h) ∧ (b.g2l ≤ π.g2 ∧ π.g2 ≤ b.g2h)

/-- Lower bound of `DD · Φ` on a box, for type-2 counts `t0, t1, t2`. -/
def lbN (t0 t1 t2 : ℕ) (b : Box) : ℕ :=
  DD * (t0 + t1 + t2) / 6 + vN (b.f0h + b.g0h + t0) + vN (b.f1h + b.g1h + t1) + vN (b.f2h + b.g2h + t2) +
    relN b.f0l b.f0h b.g1l b.g1h t0 t1 + relN b.f1l b.f1h b.g2l b.g2h t1 t2 +
    relN b.f2l b.f2h b.g0l b.g0h t2 t0

theorem tN_le (t0 t1 t2 : ℕ) : ((DD * (t0 + t1 + t2) / 6 : ℕ) : ℚ) ≤ 1200000 * (((t0 : ℚ) + t1 + t2) / 6) := by
  unfold DD
  refine (Nat.cast_div_le).trans (le_of_eq ?_)
  push_cast; ring

theorem vN_corner {f g t fh gh : ℕ} (hf : f ≤ fh) (hg : g ≤ gh) :
    (vN (fh + gh + t) : ℚ) ≤ 1200000 * (1 / (1 + (f : ℚ) + g + t)) := by
  refine (vN_le _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply one_div_le_one_div_of_le (by positivity)
  have : (f : ℚ) ≤ fh := by exact_mod_cast hf
  have : (g : ℚ) ≤ gh := by exact_mod_cast hg
  push_cast; linarith

theorem lbN_le {b : Box} {π : Profile} (hb : b.mem π) :
    (lbN π.t0 π.t1 π.t2 b : ℚ) ≤ 1200000 * Phi π := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hb
  have a := tN_le π.t0 π.t1 π.t2
  have v0 := vN_corner (t := π.t0) h0.2 h1.2
  have v1 := vN_corner (t := π.t1) h2.2 h3.2
  have v2 := vN_corner (t := π.t2) h4.2 h5.2
  have r0 := relN_le π.t0 π.t1 h0 h3
  have r1 := relN_le π.t1 π.t2 h2 h5
  have r2 := relN_le π.t2 π.t0 h4 h1
  unfold lbN; unfold Phi
  push_cast
  linarith

/-- Every profile in the box violates (F). -/
def infeasN (t0 t1 t2 : ℕ) (b : Box) : Bool :=
  mism (st b.f0l b.f0h t0) (st b.g1l b.g1h t1) || mism (st b.f1l b.f1h t1) (st b.g2l b.g2h t2) ||
    mism (st b.f2l b.f2h t2) (st b.g0l b.g0h t0)

theorem infeasN_sound {b : Box} {π : Profile} (hb : b.mem π)
    (h : infeasN π.t0 π.t1 π.t2 b = true) : ¬ Feas π := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hb
  rintro ⟨F0, F1, F2⟩
  unfold infeasN at h
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact mism_sound h0 h3 h F0
  · exact mism_sound h2 h5 h F1
  · exact mism_sound h4 h1 h F2

/-- Some relation is big on the whole box. -/
def allBigN (b : Box) : Bool :=
  (decide (23 ≤ b.f0l) && decide (23 ≤ b.g1l)) || (decide (23 ≤ b.f1l) && decide (23 ≤ b.g2l)) ||
    (decide (23 ≤ b.f2l) && decide (23 ≤ b.g0l))

theorem allBigN_sound {b : Box} {π : Profile} (hb : b.mem π) (h : allBigN b = true) :
    Big0 π ∨ Big1 π ∨ Big2 π := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hb
  unfold allBigN at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold Big0 Big1 Big2
  omega

/-- The leaf test of C1 (target `23/12`, i.e. `2300000` at scale `DD`). -/
def ok (t0 t1 t2 : ℕ) (b : Box) : Bool :=
  infeasN t0 t1 t2 b || allBigN b || decide (2300000 ≤ lbN t0 t1 t2 b)

theorem ok_sound {b : Box} {π : Profile} (hb : b.mem π) (h : ok π.t0 π.t1 π.t2 b = true)
    (hF : Feas π) (hnb : ¬ (Big0 π ∨ Big1 π ∨ Big2 π)) : 23 / 12 ≤ Phi π := by
  unfold ok at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · exact absurd hF (infeasN_sound hb h)
  · exact absurd (allBigN_sound hb h) hnb
  · have hl := lbN_le hb
    have hc : (2300000 : ℚ) ≤ (lbN π.t0 π.t1 π.t2 b : ℚ) := by exact_mod_cast h
    linarith

/-! ## Splitting -/

/-- Split preference: relative width. -/
def score (lo hi : ℕ) : ℕ := (hi - lo) * 1000 / (lo + 1)

/-- Split point: `[0,0] | [1,hi]` first, then doubling `[lo, 2lo+1] | [2lo+2, hi]`, then halving. -/
def mid (lo hi : ℕ) : ℕ := if lo = 0 then 0 else if 2 * lo + 1 < hi then 2 * lo + 1 else (lo + hi) / 2

/-- Index (0–5) of the coordinate to split. -/
def pick (b : Box) : ℕ :=
  let s0 := score b.f0l b.f0h
  let s1 := score b.g0l b.g0h
  let s2 := score b.f1l b.f1h
  let s3 := score b.g1l b.g1h
  let s4 := score b.f2l b.f2h
  let s5 := score b.g2l b.g2h
  let m01 := if s1 ≤ s0 then 0 else 1
  let v01 := max s0 s1
  let m23 := if s3 ≤ s2 then 2 else 3
  let v23 := max s2 s3
  let m45 := if s5 ≤ s4 then 4 else 5
  let v45 := max s4 s5
  if v23 ≤ v01 then (if v45 ≤ v01 then m01 else m45) else (if v45 ≤ v23 then m23 else m45)

/-- The lower part of the split of coordinate `k`. -/
def lowHalf (b : Box) : ℕ → Box
  | 0 => { b with f0h := mid b.f0l b.f0h }
  | 1 => { b with g0h := mid b.g0l b.g0h }
  | 2 => { b with f1h := mid b.f1l b.f1h }
  | 3 => { b with g1h := mid b.g1l b.g1h }
  | 4 => { b with f2h := mid b.f2l b.f2h }
  | _ => { b with g2h := mid b.g2l b.g2h }

/-- The upper part of the split of coordinate `k`. -/
def highHalf (b : Box) : ℕ → Box
  | 0 => { b with f0l := mid b.f0l b.f0h + 1 }
  | 1 => { b with g0l := mid b.g0l b.g0h + 1 }
  | 2 => { b with f1l := mid b.f1l b.f1h + 1 }
  | 3 => { b with g1l := mid b.g1l b.g1h + 1 }
  | 4 => { b with f2l := mid b.f2l b.f2h + 1 }
  | _ => { b with g2l := mid b.g2l b.g2h + 1 }

theorem split_mem {b : Box} {π : Profile} (hb : b.mem π) (k : ℕ) :
    (lowHalf b k).mem π ∨ (highHalf b k).mem π := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hb
  rcases k with _ | _ | _ | _ | _ | _ | k <;> simp only [lowHalf, highHalf, Box.mem]
  · rcases le_or_gt π.f0 (mid b.f0l b.f0h) with h | h
    · exact Or.inl ⟨⟨h0.1, h⟩, h1, h2, h3, h4, h5⟩
    · exact Or.inr ⟨⟨h, h0.2⟩, h1, h2, h3, h4, h5⟩
  · rcases le_or_gt π.g0 (mid b.g0l b.g0h) with h | h
    · exact Or.inl ⟨h0, ⟨h1.1, h⟩, h2, h3, h4, h5⟩
    · exact Or.inr ⟨h0, ⟨h, h1.2⟩, h2, h3, h4, h5⟩
  · rcases le_or_gt π.f1 (mid b.f1l b.f1h) with h | h
    · exact Or.inl ⟨h0, h1, ⟨h2.1, h⟩, h3, h4, h5⟩
    · exact Or.inr ⟨h0, h1, ⟨h, h2.2⟩, h3, h4, h5⟩
  · rcases le_or_gt π.g1 (mid b.g1l b.g1h) with h | h
    · exact Or.inl ⟨h0, h1, h2, ⟨h3.1, h⟩, h4, h5⟩
    · exact Or.inr ⟨h0, h1, h2, ⟨h, h3.2⟩, h4, h5⟩
  · rcases le_or_gt π.f2 (mid b.f2l b.f2h) with h | h
    · exact Or.inl ⟨h0, h1, h2, h3, ⟨h4.1, h⟩, h5⟩
    · exact Or.inr ⟨h0, h1, h2, h3, ⟨h, h4.2⟩, h5⟩
  all_goals
    rcases le_or_gt π.g2 (mid b.g2l b.g2h) with h | h
    · exact Or.inl ⟨h0, h1, h2, h3, h4, ⟨h5.1, h⟩⟩
    · exact Or.inr ⟨h0, h1, h2, h3, h4, ⟨h, h5.2⟩⟩

/-- The C1 branch-and-bound checker (fuel = depth bound). -/
def bb (t0 t1 t2 : ℕ) : ℕ → Box → Bool
  | 0, b => ok t0 t1 t2 b
  | n + 1, b => ok t0 t1 t2 b || (bb t0 t1 t2 n (lowHalf b (pick b)) && bb t0 t1 t2 n (highHalf b (pick b)))

theorem bb_sound (n : ℕ) : ∀ (b : Box) (π : Profile), bb π.t0 π.t1 π.t2 n b = true → b.mem π → Feas π →
    ¬ (Big0 π ∨ Big1 π ∨ Big2 π) → 23 / 12 ≤ Phi π := by
  induction n with
  | zero => intro b π h hb hF hnb; exact ok_sound hb h hF hnb
  | succ n ih =>
    intro b π h hb hF hnb
    simp only [bb, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact ok_sound hb h hF hnb
    · rcases split_mem hb (pick b) with hm | hm
      · exact ih _ π h1 hm hF hnb
      · exact ih _ π h2 hm hF hnb

/-- The C1 box `[0,92]^6`. -/
def full : Box := ⟨0, 92, 0, 92, 0, 92, 0, 92, 0, 92, 0, 92⟩

/-- C1 for one type-2 triple. -/
def runT (t0 t1 t2 : ℕ) : Bool := bb t0 t1 t2 100 full

/-- C1 for all 364 type-2 triples with `t0 + t1 + t2 ≤ 11`. -/
def allT : Bool :=
  (List.range 12).all fun t0 => (List.range (12 - t0)).all fun t1 =>
    (List.range (12 - t0 - t1)).all fun t2 => runT t0 t1 t2

/-- Soundness of the C1 certificate: `allT = true` gives `Φ ≥ 23/12` on the whole Case II region. -/
theorem caseII_of_allT (hc : allT = true) (π : Profile) (hF : Feas π) (ht : π.t0 + π.t1 + π.t2 ≤ 11)
    (hbox : π.f0 ≤ 92 ∧ π.g0 ≤ 92 ∧ π.f1 ≤ 92 ∧ π.g1 ≤ 92 ∧ π.f2 ≤ 92 ∧ π.g2 ≤ 92)
    (hnb : ¬ (Big0 π ∨ Big1 π ∨ Big2 π)) : 23 / 12 ≤ Phi π := by
  unfold allT at hc
  simp only [List.all_eq_true, List.mem_range] at hc
  have hr : runT π.t0 π.t1 π.t2 = true := hc π.t0 (by omega) π.t1 (by omega) π.t2 (by omega)
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hbox
  exact bb_sound 100 full π hr ⟨⟨Nat.zero_le _, a0⟩, ⟨Nat.zero_le _, a1⟩, ⟨Nat.zero_le _, a2⟩,
    ⟨Nat.zero_le _, a3⟩, ⟨Nat.zero_le _, a4⟩, ⟨Nat.zero_le _, a5⟩⟩ hF hnb

/-! ## C2: the `κ` bound -/

/-- `⌈DD · max(0, −κ(p; u, s))⌉`, over the common denominator `2(1+p)²(1+p+u)`. -/
def kterm (p u s : ℕ) : ℕ :=
  (DD * ((1 + p) * (1 + p + u) + s * (1 + p + u) - 2 * ((1 + p) * (1 + p))) +
      2 * ((1 + p) * (1 + p)) * (1 + p + u) - 1) / (2 * ((1 + p) * (1 + p)) * (1 + p + u))

/-- `max_{p ≤ p' < p + n} kterm p' u s`. -/
def kdLoop (u s : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | p, n + 1 => max (kterm p u s) (kdLoop u s (p + 1) n)

/-- An upper bound of `−DD · k(u,s)`: the maximum of `kterm p u s` over `23 ≤ p < u + 2s`. -/
def kdC (u s : ℕ) : ℕ := kdLoop u s 23 (u + 2 * s - 23)

theorem ceil_ge (a b : ℕ) (hb : 0 < b) : (a : ℚ) / b ≤ (((a + b - 1) / b : ℕ) : ℚ) := by
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  have h3 : a ≤ (a + b - 1) / b * b := by
    have : b * ((a + b - 1) / b) = (a + b - 1) / b * b := Nat.mul_comm _ _
    omega
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast h3

theorem kterm_ge (p u s : ℕ) : -(kappa p u s) * 1200000 ≤ (kterm p u s : ℚ) := by
  set X : ℚ := 1 + p with hX
  set W : ℚ := 1 + p + u with hW
  have hXp : 0 < X := by positivity
  have hWp : 0 < W := by positivity
  have hk : -(kappa p u s) = (X * W + s * W - 2 * X ^ 2) / (2 * X ^ 2 * W) := by
    unfold kappa
    rw [← hX]
    have : (1 : ℚ) + p + u = W := by rw [hW]
    rw [this]
    field_simp
    ring
  by_cases hN : X * W + s * W - 2 * X ^ 2 ≤ 0
  · have : -(kappa p u s) ≤ 0 := by
      rw [hk]; exact div_nonpos_of_nonpos_of_nonneg hN (by positivity)
    have : (0 : ℚ) ≤ (kterm p u s : ℚ) := Nat.cast_nonneg _
    nlinarith
  · rw [not_le] at hN
    have hle : 2 * ((1 + p) * (1 + p)) ≤ (1 + p) * (1 + p + u) + s * (1 + p + u) := by
      have : (2 * ((1 + p) * (1 + p)) : ℚ) ≤ (1 + p) * (1 + p + u) + s * (1 + p + u) := by
        rw [hX, hW] at hN; nlinarith
      exact_mod_cast this
    have hden : 0 < 2 * ((1 + p) * (1 + p)) * (1 + p + u) := by positivity
    unfold kterm DD
    refine le_trans ?_ (ceil_ge _ _ hden)
    rw [hk]
    rw [Nat.cast_mul, Nat.cast_sub hle]
    push_cast
    rw [hX, hW]
    apply le_of_eq
    field_simp

theorem kdLoop_ge (u s : ℕ) : ∀ (n p p' : ℕ), p ≤ p' → p' < p + n → kterm p' u s ≤ kdLoop u s p n := by
  intro n
  induction n with
  | zero => intro p p' h1 h2; omega
  | succ n ih =>
    intro p p' h1 h2
    simp only [kdLoop]
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · subst h; exact le_max_left _ _
    · exact le_max_of_le_right (ih (p + 1) p' h (by omega))

/-- For every `p ≥ 23`: `DD · (−κ(p; u, s)) ≤ kdC u s` (scan plus the tail `kappa_nonneg`). -/
theorem kdC_sound {p : ℕ} (u s : ℕ) (hp : 23 ≤ p) : -(kappa p u s) * 1200000 ≤ (kdC u s : ℚ) := by
  by_cases ht : u + 2 * s ≤ 1 + p
  · have := kappa_nonneg ht
    have : (0 : ℚ) ≤ (kdC u s : ℚ) := Nat.cast_nonneg _
    nlinarith
  · refine (kterm_ge p u s).trans ?_
    exact_mod_cast kdLoop_ge u s (u + 2 * s - 23) 23 p hp (by omega)

/-! ## C2 boxes (Case III, `ρ_0` big) -/

/-- A box of the four type-1 counts `g0 = ab, f1 = ba, f2 = cb, g2 = ca` of the two relations that are not big. -/
structure Box2 where
  g0l : ℕ
  g0h : ℕ
  f1l : ℕ
  f1h : ℕ
  f2l : ℕ
  f2h : ℕ
  g2l : ℕ
  g2h : ℕ

def Box2.mem (b : Box2) (π : Profile) : Prop :=
  (b.g0l ≤ π.g0 ∧ π.g0 ≤ b.g0h) ∧ (b.f1l ≤ π.f1 ∧ π.f1 ≤ b.f1h) ∧ (b.f2l ≤ π.f2 ∧ π.f2 ≤ b.f2h) ∧
    (b.g2l ≤ π.g2 ∧ π.g2 ≤ b.g2h)

/-- `G = 1/(1+n_C) + t/6 + e_a + e_b` (pw2312 Case III). -/
def Gpart (π : Profile) : ℚ :=
  1 / (1 + (π.f2 : ℚ) + π.g2 + π.t2) + ((π.t0 : ℚ) + π.t1 + π.t2) / 6 +
    (S π.f1 π.g2 π.t2 + S π.g2 π.f1 π.t1) + (S π.f2 π.g0 π.t0 + S π.g0 π.f2 π.t2)

theorem Phi_eq_K_add_G (π : Profile) :
    Phi π = (1 / (1 + (π.f0 : ℚ) + π.g0 + π.t0) + 1 / (1 + (π.f1 : ℚ) + π.g1 + π.t1) +
      (S π.f0 π.g1 π.t1 + S π.g1 π.f0 π.t0)) + Gpart π := by
  unfold Phi Gpart; ring

/-- Lower bound of `DD · G` on a box. -/
def lb2N (t0 t1 t2 : ℕ) (b : Box2) : ℕ :=
  DD * (t0 + t1 + t2) / 6 + vN (b.f2h + b.g2h + t2) + relN b.f1l b.f1h b.g2l b.g2h t1 t2 +
    relN b.f2l b.f2h b.g0l b.g0h t2 t0

theorem lb2N_le {b : Box2} {π : Profile} (hb : b.mem π) :
    (lb2N π.t0 π.t1 π.t2 b : ℚ) ≤ 1200000 * Gpart π := by
  obtain ⟨h1, h2, h4, h5⟩ := hb
  have a := tN_le π.t0 π.t1 π.t2
  have v2 := vN_corner (t := π.t2) h4.2 h5.2
  have r1 := relN_le π.t1 π.t2 h2 h5
  have r2 := relN_le π.t2 π.t0 h4 h1
  unfold lb2N Gpart
  push_cast
  linarith

/-- Every profile in the box violates (F) for `ρ_1` or `ρ_2`. -/
def infeas2N (t0 t1 t2 : ℕ) (b : Box2) : Bool :=
  mism (st b.f1l b.f1h t1) (st b.g2l b.g2h t2) || mism (st b.f2l b.f2h t2) (st b.g0l b.g0h t0)

/-- The leaf test of C2: `G − kd_A/DD − kd_B/DD ≥ 11/12`. -/
def ok2 (t0 t1 t2 : ℕ) (b : Box2) : Bool :=
  infeas2N t0 t1 t2 b || (decide (1100000 ≤ lb2N t0 t1 t2 b) &&
    decide (1100000 + kdC (b.g0h + t0) t0 + kdC (b.f1h + t1) t1 ≤ lb2N t0 t1 t2 b))

theorem ok2_sound {b : Box2} {π : Profile} (hb : b.mem π) (h : ok2 π.t0 π.t1 π.t2 b = true)
    (hf0 : 23 ≤ π.f0) (hg1 : 23 ≤ π.g1) (hF : Feas π) : 23 / 12 ≤ Phi π := by
  unfold ok2 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨-, h⟩
  · exfalso
    obtain ⟨h1, h2, h4, h5⟩ := hb
    unfold infeas2N at h
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · exact mism_sound h2 h5 h hF.2.1
    · exact mism_sound h4 h1 h hF.2.2
  · have hl := lb2N_le hb
    obtain ⟨h1, h2, -, -⟩ := hb
    have hK := K_ge π (by omega) (by omega)
    have kA := kappa_anti_u π.f0 π.t0 (show π.g0 + π.t0 ≤ b.g0h + π.t0 by omega)
    have kB := kappa_anti_u π.g1 π.t1 (show π.f1 + π.t1 ≤ b.f1h + π.t1 by omega)
    have dA := kdC_sound (b.g0h + π.t0) π.t0 hf0
    have dB := kdC_sound (b.f1h + π.t1) π.t1 hg1
    have hc : (1100000 : ℚ) + (kdC (b.g0h + π.t0) π.t0 : ℚ) + (kdC (b.f1h + π.t1) π.t1 : ℚ) ≤
        (lb2N π.t0 π.t1 π.t2 b : ℚ) := by exact_mod_cast h
    rw [Phi_eq_K_add_G]
    linarith

/-- Index (0–3) of the coordinate of a `Box2` to split. -/
def pick2 (b : Box2) : ℕ :=
  let s0 := score b.g0l b.g0h
  let s1 := score b.f1l b.f1h
  let s2 := score b.f2l b.f2h
  let s3 := score b.g2l b.g2h
  let m01 := if s1 ≤ s0 then 0 else 1
  let v01 := max s0 s1
  let m23 := if s3 ≤ s2 then 2 else 3
  let v23 := max s2 s3
  if v23 ≤ v01 then m01 else m23

def low2 (b : Box2) : ℕ → Box2
  | 0 => { b with g0h := mid b.g0l b.g0h }
  | 1 => { b with f1h := mid b.f1l b.f1h }
  | 2 => { b with f2h := mid b.f2l b.f2h }
  | _ => { b with g2h := mid b.g2l b.g2h }

def high2 (b : Box2) : ℕ → Box2
  | 0 => { b with g0l := mid b.g0l b.g0h + 1 }
  | 1 => { b with f1l := mid b.f1l b.f1h + 1 }
  | 2 => { b with f2l := mid b.f2l b.f2h + 1 }
  | _ => { b with g2l := mid b.g2l b.g2h + 1 }

theorem split2_mem {b : Box2} {π : Profile} (hb : b.mem π) (k : ℕ) :
    (low2 b k).mem π ∨ (high2 b k).mem π := by
  obtain ⟨h0, h1, h2, h3⟩ := hb
  rcases k with _ | _ | _ | k <;> simp only [low2, high2, Box2.mem]
  · rcases le_or_gt π.g0 (mid b.g0l b.g0h) with h | h
    · exact Or.inl ⟨⟨h0.1, h⟩, h1, h2, h3⟩
    · exact Or.inr ⟨⟨h, h0.2⟩, h1, h2, h3⟩
  · rcases le_or_gt π.f1 (mid b.f1l b.f1h) with h | h
    · exact Or.inl ⟨h0, ⟨h1.1, h⟩, h2, h3⟩
    · exact Or.inr ⟨h0, ⟨h, h1.2⟩, h2, h3⟩
  · rcases le_or_gt π.f2 (mid b.f2l b.f2h) with h | h
    · exact Or.inl ⟨h0, h1, ⟨h2.1, h⟩, h3⟩
    · exact Or.inr ⟨h0, h1, ⟨h, h2.2⟩, h3⟩
  all_goals
    rcases le_or_gt π.g2 (mid b.g2l b.g2h) with h | h
    · exact Or.inl ⟨h0, h1, h2, ⟨h3.1, h⟩⟩
    · exact Or.inr ⟨h0, h1, h2, ⟨h, h3.2⟩⟩

/-- The C2 branch-and-bound checker. -/
def bb2 (t0 t1 t2 : ℕ) : ℕ → Box2 → Bool
  | 0, b => ok2 t0 t1 t2 b
  | n + 1, b => ok2 t0 t1 t2 b || (bb2 t0 t1 t2 n (low2 b (pick2 b)) && bb2 t0 t1 t2 n (high2 b (pick2 b)))

theorem bb2_sound (n : ℕ) : ∀ (b : Box2) (π : Profile), bb2 π.t0 π.t1 π.t2 n b = true → b.mem π →
    23 ≤ π.f0 → 23 ≤ π.g1 → Feas π → 23 / 12 ≤ Phi π := by
  induction n with
  | zero => intro b π h hb hf hg hF; exact ok2_sound hb h hf hg hF
  | succ n ih =>
    intro b π h hb hf hg hF
    simp only [bb2, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact ok2_sound hb h hf hg hF
    · rcases split2_mem hb (pick2 b) with hm | hm
      · exact ih _ π h1 hm hf hg hF
      · exact ih _ π h2 hm hf hg hF

/-- The C2 box `[0,92]^4`. -/
def full2 : Box2 := ⟨0, 92, 0, 92, 0, 92, 0, 92⟩

def runT2 (t0 t1 t2 : ℕ) : Bool := bb2 t0 t1 t2 100 full2

/-- C2 for all 364 type-2 triples with `t ≤ 11`. -/
def allT2 : Bool :=
  (List.range 12).all fun t0 => (List.range (12 - t0)).all fun t1 =>
    (List.range (12 - t0 - t1)).all fun t2 => runT2 t0 t1 t2

/-- Soundness of the C2 certificate: Case III with `ρ_0` big. -/
theorem caseIII_of_allT2 (hc : allT2 = true) (π : Profile) (hF : Feas π) (ht : π.t0 + π.t1 + π.t2 ≤ 11)
    (hf0 : 23 ≤ π.f0) (hg1 : 23 ≤ π.g1)
    (hbox : π.g0 ≤ 92 ∧ π.f1 ≤ 92 ∧ π.f2 ≤ 92 ∧ π.g2 ≤ 92) : 23 / 12 ≤ Phi π := by
  unfold allT2 at hc
  simp only [List.all_eq_true, List.mem_range] at hc
  have hr : runT2 π.t0 π.t1 π.t2 = true := hc π.t0 (by omega) π.t1 (by omega) π.t2 (by omega)
  obtain ⟨a0, a1, a2, a3⟩ := hbox
  exact bb2_sound 100 full2 π hr ⟨⟨Nat.zero_le _, a0⟩, ⟨Nat.zero_le _, a1⟩, ⟨Nat.zero_le _, a2⟩,
    ⟨Nat.zero_le _, a3⟩⟩ hf0 hg1 hF

end PwCheck
end Erdos643R3

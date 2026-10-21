import Mathlib
import Openmath.Erdos643R3.SlotModel
import Openmath.Erdos643R3.Pw2312Defs



set_option autoImplicit false

namespace Erdos643R3
namespace Lemma3

open Finset hiding shadow
open Erdos643R3.Identity Erdos643R3.Weighting Erdos643R3.SlotModel Erdos643R3.Pw2312

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Two general lemmas -/

omit [Fintype V] in
/-- Counting step of Lemma 3 for one relation `r` between `X` and `Y`, with "other" degrees `oX`, `oY`: if every
slot of `Y` with neighbours in both relations has at most one `r`-neighbour, then the `r`-degrees of the slots of `X`
that are type 1 in `r` sum to at most `|P||Q| + |S_Y|`. -/
theorem bip_sum_le {X Y : Finset V} (r : V → V → Prop) [DecidableRel r] (oX oY : V → ℕ)
    (hY : ∀ y ∈ Y, 0 < (X.filter (fun x => r x y)).card → 0 < oY y →
      (X.filter (fun x => r x y)).card ≤ 1) :
    ∑ x ∈ X.filter (fun x => 0 < (Y.filter (r x)).card ∧ oX x = 0), (Y.filter (r x)).card ≤
      (X.filter (fun x => 0 < (Y.filter (r x)).card ∧ oX x = 0)).card *
        (Y.filter (fun y => 0 < (X.filter (fun x => r x y)).card ∧ oY y = 0)).card +
      (Y.filter (fun y => 0 < (X.filter (fun x => r x y)).card ∧ 0 < oY y)).card := by
  set P := X.filter (fun x => 0 < (Y.filter (r x)).card ∧ oX x = 0) with hPdef
  set Q := Y.filter (fun y => 0 < (X.filter (fun x => r x y)).card ∧ oY y = 0) with hQdef
  set SY := Y.filter (fun y => 0 < (X.filter (fun x => r x y)).card ∧ 0 < oY y) with hSdef
  have h1 : ∀ x ∈ P, (Y.filter (r x)).card ≤ Q.card + (SY.filter (r x)).card := by
    intro x hx
    have hxX : x ∈ X := (mem_filter.mp hx).1
    refine (card_le_card ?_).trans (card_union_le Q (SY.filter (r x)))
    intro y hy
    obtain ⟨hyY, hrxy⟩ := mem_filter.mp hy
    have hpos : 0 < (X.filter (fun x' => r x' y)).card :=
      card_pos.mpr ⟨x, mem_filter.mpr ⟨hxX, hrxy⟩⟩
    rcases Nat.eq_zero_or_pos (oY y) with h0 | h0
    · exact mem_union_left _ (mem_filter.mpr ⟨hyY, hpos, h0⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_filter.mpr ⟨hyY, hpos, h0⟩, hrxy⟩)
  have h2 : ∑ x ∈ P, (SY.filter (r x)).card ≤ SY.card := by
    have e := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := P) (t := SY) (r := r)
    simp only [bipartiteAbove, bipartiteBelow] at e
    rw [e, card_eq_sum_ones SY]
    refine sum_le_sum (fun y hy => ?_)
    obtain ⟨hyY, hpos, hoY⟩ := mem_filter.mp hy
    exact (card_le_card (filter_subset_filter _ (filter_subset _ X))).trans (hY y hyY hpos hoY)
  calc ∑ x ∈ P, (Y.filter (r x)).card ≤ ∑ x ∈ P, (Q.card + (SY.filter (r x)).card) := sum_le_sum h1
    _ = P.card * Q.card + ∑ x ∈ P, (SY.filter (r x)).card := by
        rw [sum_add_distrib, sum_const, smul_eq_mul]
    _ ≤ P.card * Q.card + SY.card := by omega

/-- Cauchy–Schwarz step of Lemma 3: if `Σ_{x ∈ P} d(x) ≤ |P| q + s` then
`Σ_{x ∈ P} 1/(2(1 + d(x))) ≥ |P|²/(2 Σ (1 + d)) ≥ S(|P|, q, s)`. -/
theorem S_le_sum {ι : Type*} (P : Finset ι) (d : ι → ℕ) (q s : ℕ)
    (h : ∑ x ∈ P, d x ≤ P.card * q + s) :
    S P.card q s ≤ ∑ x ∈ P, 1 / (2 * (1 + (d x : ℚ))) := by
  rcases P.eq_empty_or_nonempty with hP | hP
  · subst hP; simp [S_zero]
  have hcs := sq_sum_div_le_sum_sq_div P (fun _ => (1 : ℚ)) (g := fun x => 2 * (1 + (d x : ℚ)))
    (fun x _ => by positivity)
  simp only [sum_const, nsmul_eq_mul, mul_one, one_pow] at hcs
  refine le_trans ?_ hcs
  unfold S
  have hsum : ∑ x ∈ P, 2 * (1 + (d x : ℚ)) = 2 * ((P.card : ℚ) + ∑ x ∈ P, (d x : ℚ)) := by
    rw [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]
  rw [hsum]
  have hcast : (∑ x ∈ P, (d x : ℚ)) ≤ (P.card : ℚ) * q + s := by exact_mod_cast h
  have hpos : (0 : ℚ) < P.card := by exact_mod_cast hP.card_pos
  have hd : (0 : ℚ) ≤ ∑ x ∈ P, (d x : ℚ) := by positivity
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  linarith

/-! ## The relation with apex `c` of the view `(a,b,c)`: `R_c` between `A` and `B` -/

variable {H : Finset (Finset V)}

/-- Lemma 2 for the slots of `B` (view `(b,c,a)`), in the form needed by `bip_sum_le`. -/
theorem lemma2_B {a b c : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    ∀ y ∈ grp H b c a, 0 < (nb H b c a y).card → 0 < (nc H b c a y).card → (nb H b c a y).card ≤ 1 :=
  fun _ hy h1 h2 => (lemma2_card (triple_rot hT) hH hav hy h1 h2).1.le

/-- Lemma 2 for the slots of `A` (view `(a,b,c)`), `R_c`-side. -/
theorem lemma2_A {a b c : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    ∀ z ∈ grp H a b c, 0 < (nc H a b c z).card → 0 < (nb H a b c z).card → (nc H a b c z).card ≤ 1 :=
  fun _ hz h1 h2 => (lemma2_card hT hH hav hz h2 h1).2.le

/-- `Σ_{z ∈ P} d(z) ≤ |P||Q| + |S_B|` for `P` the slots of `A` type 1 in `R_c`, `Q` those of `B`. -/
theorem relF_count {a b c : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    ∑ z ∈ fset H a b c, (nc H a b c z).card ≤
      (fset H a b c).card * (gset H b c a).card + (tset H b c a).card :=
  bip_sum_le (X := grp H a b c) (Y := grp H b c a) (rel H c) (fun z => (nb H a b c z).card)
    (fun y => (nc H b c a y).card) (lemma2_B hT hH hav)

/-- The same count from the side of `B`: `Σ_{y ∈ Q} d(y) ≤ |Q||P| + |S_A|`. -/
theorem relG_count {a b c : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    ∑ y ∈ gset H b c a, (nb H b c a y).card ≤
      (gset H b c a).card * (fset H a b c).card + (tset H a b c).card := by
  have e : (grp H a b c).filter (fun z => 0 < (nc H a b c z).card ∧ 0 < (nb H a b c z).card) =
      tset H a b c := by
    unfold tset; exact filter_congr (fun _ _ => and_comm)
  calc ∑ y ∈ gset H b c a, (nb H b c a y).card ≤ (gset H b c a).card * (fset H a b c).card +
        ((grp H a b c).filter (fun z => 0 < (nc H a b c z).card ∧ 0 < (nb H a b c z).card)).card :=
        bip_sum_le (X := grp H b c a) (Y := grp H a b c) (fun y z => rel H c z y)
          (fun y => (nc H b c a y).card) (fun z => (nb H a b c z).card) (lemma2_A hT hH hav)
    _ = _ := by rw [e]

/-- First S-term of the relation `R_c`: `Σ_{f-slots of A} 1/(2(1 + d)) ≥ S(f_0, g_1, t_1)`. -/
theorem relF {a b c : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    S (fset H a b c).card (gset H b c a).card (tset H b c a).card ≤
      ∑ z ∈ fset H a b c, 1 / (2 * (1 + ((nc H a b c z).card : ℚ))) :=
  S_le_sum _ (fun z => (nc H a b c z).card) _ _ (relF_count hT hH hav)

/-- Second S-term of the relation `R_c`: `Σ_{g-slots of B} 1/(2(1 + d)) ≥ S(g_1, f_0, t_0)`. -/
theorem relG {a b c : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    S (gset H b c a).card (fset H a b c).card (tset H a b c).card ≤
      ∑ y ∈ gset H b c a, 1 / (2 * (1 + ((nb H b c a y).card : ℚ))) :=
  S_le_sum _ (fun y => (nb H b c a y).card) _ _ (relG_count hT hH hav)

/-! ## Feasibility -/

theorem one_le_f_add_t {a b c : V} :
    1 ≤ (fset H a b c).card + (tset H a b c).card ↔ ∃ z ∈ grp H a b c, ∃ y, y ∈ nc H a b c z := by
  constructor
  · intro h
    by_cases hf : 1 ≤ (fset H a b c).card
    · obtain ⟨z, hz⟩ := card_pos.mp hf
      obtain ⟨hzA, h1, -⟩ := mem_filter.mp hz
      obtain ⟨y, hy⟩ := card_pos.mp h1
      exact ⟨z, hzA, y, hy⟩
    · obtain ⟨z, hz⟩ := card_pos.mp (show 0 < (tset H a b c).card by omega)
      obtain ⟨hzA, -, h2⟩ := mem_filter.mp hz
      obtain ⟨y, hy⟩ := card_pos.mp h2
      exact ⟨z, hzA, y, hy⟩
  · rintro ⟨z, hzA, y, hy⟩
    have hc : 0 < (nc H a b c z).card := card_pos.mpr ⟨y, hy⟩
    rcases Nat.eq_zero_or_pos (nb H a b c z).card with h0 | h0
    · have : 0 < (fset H a b c).card := card_pos.mpr ⟨z, mem_filter.mpr ⟨hzA, hc, h0⟩⟩
      omega
    · have : 0 < (tset H a b c).card := card_pos.mpr ⟨z, mem_filter.mpr ⟨hzA, h0, hc⟩⟩
      omega

theorem one_le_g_add_t {a b c : V} :
    1 ≤ (gset H a b c).card + (tset H a b c).card ↔ ∃ z ∈ grp H a b c, ∃ x, x ∈ nb H a b c z := by
  constructor
  · intro h
    by_cases hg : 1 ≤ (gset H a b c).card
    · obtain ⟨z, hz⟩ := card_pos.mp hg
      obtain ⟨hzA, h1, -⟩ := mem_filter.mp hz
      obtain ⟨x, hx⟩ := card_pos.mp h1
      exact ⟨z, hzA, x, hx⟩
    · obtain ⟨z, hz⟩ := card_pos.mp (show 0 < (tset H a b c).card by omega)
      obtain ⟨hzA, h1, -⟩ := mem_filter.mp hz
      obtain ⟨x, hx⟩ := card_pos.mp h1
      exact ⟨z, hzA, x, hx⟩
  · rintro ⟨z, hzA, x, hx⟩
    have hb : 0 < (nb H a b c z).card := card_pos.mpr ⟨x, hx⟩
    rcases Nat.eq_zero_or_pos (nc H a b c z).card with h0 | h0
    · have : 0 < (gset H a b c).card := card_pos.mpr ⟨z, mem_filter.mpr ⟨hzA, hb, h0⟩⟩
      omega
    · have : 0 < (tset H a b c).card := card_pos.mpr ⟨z, mem_filter.mpr ⟨hzA, hb, h0⟩⟩
      omega

/-- (F) for the relation `R_c` of the view `(a,b,c)`: `f_0 + t_0 ≥ 1 ↔ g_1 + t_1 ≥ 1`. -/
theorem feas_rel {a b c : V} :
    (1 ≤ (fset H a b c).card + (tset H a b c).card ↔ 1 ≤ (gset H b c a).card + (tset H b c a).card) := by
  rw [one_le_f_add_t, one_le_g_add_t]
  constructor
  · rintro ⟨z, hzA, y, hy⟩
    obtain ⟨hyB, hzy, hczy⟩ := mem_nc.mp hy
    exact ⟨y, hyB, z, mem_nb.mpr ⟨hzA, hzy, hczy⟩⟩
  · rintro ⟨y, hyB, z, hz⟩
    obtain ⟨hzA, hzy, hczy⟩ := mem_nb.mp hz
    exact ⟨z, hzA, y, mem_nc.mpr ⟨hyB, hzy, hczy⟩⟩

/-! ## The profile of a triple and Lemma 3 -/

variable (H) in
/-- The profile of the labelled triple `{a,b,c}` (pw2312 §3) in the cyclic coordinates of `Pw2312.Profile`. -/
def profileOf (a b c : V) : Profile :=
  ⟨(fset H a b c).card, (gset H a b c).card, (tset H a b c).card,
    (fset H b c a).card, (gset H b c a).card, (tset H b c a).card,
    (fset H c a b).card, (gset H c a b).card, (tset H c a b).card⟩

/-- **Lemma 3, pre-isolated form (0.1).** `σ(T) + τ(T) ≥ Φ⁺(profile of T)`. -/
theorem lemma3_plus {a b c : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    PhiPlus (profileOf H a b c) (iset H a b c).card (iset H b c a).card (iset H c a b).card ≤
      sigmaW H {a, b, c} + tauW H {a, b, c} := by
  have hT1 := triple_rot hT
  have hT2 := triple_rot hT1
  rw [sigmaW_slots hT hH, tauW_slots hT hH hav]
  have eA := group_exact hT hH hav
  have eB := group_exact hT1 hH hav
  have eC := group_exact hT2 hH hav
  have f0 := relF hT hH hav
  have g1 := relG hT hH hav
  have f1 := relF hT1 hH hav
  have g2 := relG hT1 hH hav
  have f2 := relF hT2 hH hav
  have g0 := relG hT2 hH hav
  simp only [PhiPlus, Phi, Delta, profileOf]
  linarith

/-- **Lemma 3** (pw2312 §3). `σ(T) + τ(T) ≥ Φ(profile of T)`, and the profile satisfies (F). -/
theorem lemma3 {a b c : V} (hT : ({a, b, c} : Finset V) ∈ H) (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) :
    Phi (profileOf H a b c) ≤ sigmaW H {a, b, c} + tauW H {a, b, c} ∧ Feas (profileOf H a b c) :=
  ⟨(Phi_le_PhiPlus _ _ _ _).trans (lemma3_plus hT hH hav),
    ⟨feas_rel, feas_rel, feas_rel⟩⟩

end Lemma3
end Erdos643R3

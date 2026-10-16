import Mathlib.Combinatorics.Configuration
import Mathlib.Tactic

/-! Elementary ingredients for the completion route. This file does not yet
claim full partial symmetry. The route uses the elementary degree sum bound
in Füredi (1988), printed p.6, instead of invoking Dow uniqueness as an oracle. -/
namespace Erdos60.PartialSymmetryCompletion

open Finset
variable {P L : Type*} [Membership P L]

/-- Scalar endpoint step of the elementary linear-space degree-sum proof. -/
theorem degree_sum_numeric {v k : ℕ} (hk : 3 ≤ k) (hkv : k < v) :
    3*(v-1) ≤ 2*k+k*(v-k) := by
  have ha : k = (k-3)+3 := by omega
  have hb : v-1 = k+(v-1-k) := by omega
  have hc : v-k = (v-1-k)+1 := by omega
  nlinarith [Nat.zero_le ((k-3)*(v-1-k))]

noncomputable def sectionPts [Fintype P] (S : Finset P) (l : L) : Finset P := by
  classical
  exact S.filter (fun x => x ∈ l)

noncomputable def secantsAt [Fintype L] (S : Finset P)
    (x : P) : Finset L := by
  classical
  exact univ.filter (fun l => x ∈ l ∧ 2 ≤ (S.filter (fun y => y ∈ l)).card)

/-- A point outside a line sees its k selected points along k distinct
secants of the selected point set. This is the geometric lower degree bound
used for points outside a largest induced line. -/
theorem outside_secant_degree [Fintype P] [Fintype L]
    [Configuration.HasLines P L] (S : Finset P) (l : L) {x : P}
    (hxS : x ∈ S) (hxl : x ∉ l) :
    (sectionPts S l).card ≤ (secantsAt (L := L) S x).card := by
  classical
  let f : {y // y ∈ sectionPts S l} → {m // m ∈ secantsAt (L := L) S x} := fun y => by
    have hyl : y.val ∈ l := (show y.val ∈ S ∧ y.val ∈ l by simpa [sectionPts] using y.property).2
    have hxy : x ≠ y.val := fun h => hxl (h ▸ hyl)
    let m := Configuration.HasLines.mkLine (L := L) hxy
    have hm := Configuration.HasLines.mkLine_ax (L := L) hxy
    refine ⟨m, ?_⟩
    simp only [secantsAt, mem_filter, mem_univ, true_and]
    refine ⟨hm.1, ?_⟩
    apply Finset.one_lt_card.mpr
    exact ⟨x, by simp [m, hxS, hm.1], y.val,
      by simp [m, (show y.val ∈ S ∧ y.val ∈ l by simpa [sectionPts] using y.property).1, hm.2], hxy⟩
  have hf : Function.Injective f := by
    intro y z he
    have hm : (f y).val = (f z).val := congrArg Subtype.val he
    have hyl : y.val ∈ l := (show y.val ∈ S ∧ y.val ∈ l by simpa [sectionPts] using y.property).2
    have hzl : z.val ∈ l := (show z.val ∈ S ∧ z.val ∈ l by simpa [sectionPts] using z.property).2
    have hxy : x ≠ y.val := fun h => hxl (h ▸ hyl)
    have hxz : x ≠ z.val := fun h => hxl (h ▸ hzl)
    have hmy := (Configuration.HasLines.mkLine_ax (L := L) hxy).2
    have hmz := (Configuration.HasLines.mkLine_ax (L := L) hxz).2
    change Configuration.HasLines.mkLine (L := L) hxy = Configuration.HasLines.mkLine (L := L) hxz at hm
    rw [← hm] at hmz
    have heq := Configuration.Nondegenerate.eq_or_eq hyl hzl hmy hmz
    apply Subtype.ext
    rcases heq with h | h
    · exact h
    · have hxm := (Configuration.HasLines.mkLine_ax (L := L) hxy).1
      rw [← h] at hxm
      exact False.elim (hxl hxm)
  simpa using Fintype.card_le_of_injective f hf

/-- A selected point on a nontrivial induced line is on at least two
selected-point secants, provided another selected point is outside that line. -/
theorem inside_secant_degree [Fintype P] [Fintype L]
    [Configuration.HasLines P L] (S : Finset P) (l : L) {x : P}
    (hxS : x ∈ S) (hxl : x ∈ l) (hk : 2 ≤ (sectionPts S l).card)
    (hz : ∃ z ∈ S, z ∉ l) : 2 ≤ (secantsAt (L := L) S x).card := by
  classical
  obtain ⟨z, hzS, hzl⟩ := hz
  have hxz : x ≠ z := fun h => hzl (h ▸ hxl)
  let m := Configuration.HasLines.mkLine (L := L) hxz
  have hm := Configuration.HasLines.mkLine_ax (L := L) hxz
  have hl : l ∈ secantsAt (L := L) S x := by
    simp only [secantsAt, mem_filter, mem_univ, true_and]
    exact ⟨hxl, hk⟩
  have hmS : m ∈ secantsAt (L := L) S x := by
    simp only [secantsAt, mem_filter, mem_univ, true_and]
    refine ⟨hm.1, Finset.one_lt_card.mpr ?_⟩
    exact ⟨x, by simp [m, hxS, hm.1], z, by simp [m, hzS, hm.2], hxz⟩
  have hlm : l ≠ m := by
    intro he
    have hzm : z ∈ m := hm.2
    rw [← he] at hzm
    exact hzl hzm
  exact Finset.one_lt_card.mpr ⟨l, hl, m, hmS, hlm⟩

/-- If every selected-point line has size at most two, distinct selected
points other than x determine distinct secants through x. -/
theorem two_point_sections_degree [Fintype P] [Fintype L]
    [Configuration.HasLines P L] (S : Finset P) {x : P} (hxS : x ∈ S)
    (hsmall : ∀ l : L, (sectionPts S l).card ≤ 2) :
    S.card-1 ≤ (secantsAt (L := L) S x).card := by
  classical
  let f : {y // y ∈ S.erase x} → {m // m ∈ secantsAt (L := L) S x} := fun y => by
    have hy := mem_erase.mp y.property
    have hxy : x ≠ y.val := Ne.symm hy.1
    let m := Configuration.HasLines.mkLine (L := L) hxy
    have hm := Configuration.HasLines.mkLine_ax (L := L) hxy
    refine ⟨m, ?_⟩
    simp only [secantsAt, mem_filter, mem_univ, true_and]
    refine ⟨hm.1, Finset.one_lt_card.mpr ?_⟩
    exact ⟨x, by simp [m, hxS, hm.1], y.val, by simp [m, hy.2, hm.2], hxy⟩
  have hf : Function.Injective f := by
    intro y z he
    apply Subtype.ext
    by_contra hyz
    have hy := mem_erase.mp y.property
    have hz := mem_erase.mp z.property
    have hxy : x ≠ y.val := Ne.symm hy.1
    have hxz : x ≠ z.val := Ne.symm hz.1
    let m := Configuration.HasLines.mkLine (L := L) hxy
    have hm := Configuration.HasLines.mkLine_ax (L := L) hxy
    have he' : m = Configuration.HasLines.mkLine (L := L) hxz := congrArg Subtype.val he
    have hzline : z.val ∈ m := by
      rw [he']
      exact (Configuration.HasLines.mkLine_ax (L := L) hxz).2
    have hsub : ({x, y.val, z.val} : Finset P) ⊆ sectionPts S m := by
      intro p hp
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · simp [sectionPts, hxS, m, hm.1]
      · simp [sectionPts, hy.2, m, hm.2]
      · simp [sectionPts, hz.2, hzline]
    have hc := Finset.card_le_card hsub
    have hthree : ({x,y.val,z.val} : Finset P).card = 3 := by
      simp [hxy, hxz, hyz]
    have hh := hsmall m
    omega
  have hh := Fintype.card_le_of_injective f hf
  have hh' : (S.erase x).card ≤ (secantsAt (L := L) S x).card := by
    simpa only [Fintype.card_coe] using hh
  rwa [Finset.card_erase_of_mem hxS] at hh'

/-- Elementary nontrivial linear-space degree sum. The maximum induced line
is supplied as a maximizer, not as the desired degree-sum conclusion. -/
theorem secant_degree_sum [Fintype P] [Fintype L]
    [Configuration.HasLines P L] (S : Finset P) (l : L)
    (hv : 3 ≤ S.card) (hz : ∃ z ∈ S, z ∉ l)
    (hmax : ∀ m : L, (sectionPts S m).card ≤ (sectionPts S l).card) :
    3*(S.card-1) ≤ ∑ x ∈ S, (secantsAt (L := L) S x).card := by
  classical
  by_cases hk : (sectionPts S l).card ≤ 2
  · have hsmall : ∀ m : L, (sectionPts S m).card ≤ 2 := fun m => (hmax m).trans hk
    have hh : ∑ x ∈ S, (S.card-1) ≤ ∑ x ∈ S, (secantsAt (L := L) S x).card := by
      apply Finset.sum_le_sum
      intro x hx
      exact two_point_sections_degree S hx hsmall
    simp only [Finset.sum_const, nsmul_eq_mul] at hh
    nlinarith [Nat.zero_le ((S.card-3)*(S.card-1))]
  · have hk3 : 3 ≤ (sectionPts S l).card := by omega
    have hproper : (sectionPts S l).card < S.card := by
      obtain ⟨z, hzS, hzl⟩ := hz
      apply Finset.card_lt_card
      refine ⟨Finset.filter_subset _ _, ?_⟩
      intro h
      have := h hzS
      simpa [sectionPts, hzl] using this
    have hc := degree_sum_numeric hk3 hproper
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (s := S) (p := fun x : P => x ∈ l)
      (f := fun x => (secantsAt (L := L) S x).card)
    have hinside : 2*(sectionPts S l).card ≤
        ∑ x ∈ S.filter (fun x => x ∈ l), (secantsAt (L := L) S x).card := by
      calc
        _ = ∑ x ∈ S.filter (fun x => x ∈ l), 2 := by simp [sectionPts, mul_comm]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro x hx
          have hh := mem_filter.mp hx
          exact inside_secant_degree S l hh.1 hh.2 (by omega) hz
    have houtside : (sectionPts S l).card * (S.filter (fun x => x ∉ l)).card ≤
        ∑ x ∈ S.filter (fun x => x ∉ l), (secantsAt (L := L) S x).card := by
      calc
        _ = ∑ x ∈ S.filter (fun x => x ∉ l), (sectionPts S l).card := by simp [mul_comm]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro x hx
          have hh := mem_filter.mp hx
          exact outside_secant_degree S l hh.1 hh.2
    have hcards := Finset.card_filter_add_card_filter_not (s := S) (fun x : P => x ∈ l)
    have hrest : (S.filter (fun x => x ∉ l)).card = S.card-(sectionPts S l).card := by
      change (S.filter (fun x => x ∈ l)).card + _ = S.card at hcards
      unfold sectionPts
      omega
    rw [hrest] at houtside
    omega

theorem secant_degree_sum_of_not_collinear [Fintype P] [Fintype L]
    [Configuration.HasLines P L] (S : Finset P) (hv : 3 ≤ S.card)
    (hnc : ∀ l : L, ∃ z ∈ S, z ∉ l) :
    3*(S.card-1) ≤ ∑ x ∈ S, (secantsAt (L := L) S x).card := by
  classical
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  obtain ⟨y, hy, hyx⟩ := Finset.exists_mem_ne (show 1 < S.card by omega) x
  let m := Configuration.HasLines.mkLine (L := L) hyx
  obtain ⟨l, hl, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset L)
    (fun l => (sectionPts S l).card) ⟨m, Finset.mem_univ m⟩
  exact secant_degree_sum S l hv (hnc l) (fun a => hmax a (Finset.mem_univ a))

#print axioms degree_sum_numeric
#print axioms outside_secant_degree
#print axioms inside_secant_degree
#print axioms two_point_sections_degree
#print axioms secant_degree_sum_of_not_collinear
end Erdos60.PartialSymmetryCompletion

import Mathlib



set_option autoImplicit false

namespace Erdos643R3
namespace Identity

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Definitions (Section 0) -/

/-- `H` is 3-uniform: every edge has exactly three vertices (the text's "3-graph").
Same body as `Erdos643.HypergraphBasics.Uniform`. -/
def Uniform (H : Finset (Finset V)) : Prop := ∀ e ∈ H, e.card = 3

variable (V) in
/-- The 2-subsets of the vertex set ("pairs" in the text). -/
def pairs : Finset (Finset V) := (Finset.univ : Finset V).powersetCard 2

/-- The shadow `∂H`: pairs contained in at least one edge (equivalently `k_p ≥ 1`). -/
def shadow (H : Finset (Finset V)) : Finset (Finset V) :=
  (pairs V).filter (fun p => ∃ e ∈ H, p ⊆ e)

/-- The codegree `k_p`: the number of edges of `H` containing `p`. -/
def codeg (H : Finset (Finset V)) (p : Finset V) : ℕ := (H.filter (fun e => p ⊆ e)).card

/-- The link `L_p = {v : v ∉ p, p + v ∈ H}`. -/
def link (H : Finset (Finset V)) (p : Finset V) : Finset V :=
  (Finset.univ : Finset V).filter (fun v => v ∉ p ∧ insert v p ∈ H)

/-- The common link `CN(q)`: pairs `P` with `P ∩ q = ∅` and `P + x ∈ H` for every `x ∈ q`.
For `q = {x, y}` this is the text's `{P : P ∩ q = ∅, P + x ∈ H, P + y ∈ H}` (see `mem_CN_pair`). -/
def CN (H : Finset (Finset V)) (q : Finset V) : Finset (Finset V) :=
  (pairs V).filter (fun P => P ∩ q = ∅ ∧ ∀ x ∈ q, insert x P ∈ H)

/-- The co-link pairs: pairs `q` with `s_q = |CN(q)| ≥ 1`. -/
def colink (H : Finset (Finset V)) : Finset (Finset V) :=
  (pairs V).filter (fun q => (CN H q).Nonempty)

/-- `g = |colink(H) \ ∂H|`. -/
def g (H : Finset (Finset V)) : ℕ := (colink H \ shadow H).card

/-- `O(H) = ∂H ∪ colink(H)`. -/
def O (H : Finset (Finset V)) : Finset (Finset V) := shadow H ∪ colink H

/-- `n_1 = #{p ∈ ∂H : k_p = 1}`. -/
def n1 (H : Finset (Finset V)) : ℕ := ((shadow H).filter (fun p => codeg H p = 1)).card

/-- `γ(k) = 2(k-2)/(k(k-1))`, computed in `ℚ`. (Only `k ≥ 2` is used by the text; Lean's `x / 0 = 0`
makes `γ 0 = γ 1 = 0`, which never enters `R` because members of `CN(q)` have codegree `≥ 2`.) -/
def γ (k : ℕ) : ℚ := 2 * ((k : ℚ) - 2) / ((k : ℚ) * ((k : ℚ) - 1))

/-- `R_q = Σ_{P ∈ CN(q)} γ(k_P)`. -/
def R (H : Finset (Finset V)) (q : Finset V) : ℚ := ∑ P ∈ CN H q, γ (codeg H P)

/-! ## Membership lemmas -/

omit [DecidableEq V] in
@[simp] theorem mem_pairs {p : Finset V} : p ∈ pairs V ↔ p.card = 2 := by
  simp [pairs, Finset.mem_powersetCard]

theorem mem_shadow {H : Finset (Finset V)} {p : Finset V} :
    p ∈ shadow H ↔ p.card = 2 ∧ ∃ e ∈ H, p ⊆ e := by
  simp only [shadow, Finset.mem_filter, mem_pairs]

theorem mem_link {H : Finset (Finset V)} {p : Finset V} {v : V} :
    v ∈ link H p ↔ v ∉ p ∧ insert v p ∈ H := by
  simp only [link, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_CN {H : Finset (Finset V)} {q P : Finset V} :
    P ∈ CN H q ↔ P.card = 2 ∧ P ∩ q = ∅ ∧ ∀ x ∈ q, insert x P ∈ H := by
  simp only [CN, Finset.mem_filter, mem_pairs]

/-- The two-point form of `CN`: for `q = {x, y}`, `P ∈ CN(q)` iff `P` is a pair, `P ∩ q = ∅`,
`P + x ∈ H` and `P + y ∈ H`, exactly the written definition. -/
theorem mem_CN_pair {H : Finset (Finset V)} {x y : V} {P : Finset V} :
    P ∈ CN H {x, y} ↔
      P ∈ pairs V ∧ P ∩ {x, y} = ∅ ∧ insert x P ∈ H ∧ insert y P ∈ H := by
  simp only [CN, Finset.mem_filter, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]

theorem mem_colink {H : Finset (Finset V)} {q : Finset V} :
    q ∈ colink H ↔ q.card = 2 ∧ (CN H q).Nonempty := by
  simp only [colink, Finset.mem_filter, mem_pairs]

theorem shadow_subset_pairs (H : Finset (Finset V)) : shadow H ⊆ pairs V :=
  Finset.filter_subset _ _

/-! ## Fact 0 -/

/-- **Fact 0 (incidence).** `P ∈ CN(q)` iff `P` is a pair and `q ⊆ L_P`
(the disjointness `P ∩ q = ∅` is automatic because `L_P ∩ P = ∅`). -/
theorem mem_CN_iff_subset_link {H : Finset (Finset V)} {q P : Finset V} :
    P ∈ CN H q ↔ P ∈ pairs V ∧ q ⊆ link H P := by
  rw [mem_CN, mem_pairs]
  constructor
  · rintro ⟨hc, hdis, hins⟩
    refine ⟨hc, fun x hx => mem_link.mpr ⟨?_, hins x hx⟩⟩
    exact Finset.disjoint_right.mp (Finset.disjoint_iff_inter_eq_empty.mpr hdis) hx
  · rintro ⟨hc, hsub⟩
    refine ⟨hc, ?_, fun x hx => (mem_link.mp (hsub hx)).2⟩
    exact Finset.disjoint_iff_inter_eq_empty.mp
      (Finset.disjoint_right.mpr fun x hx => (mem_link.mp (hsub hx)).1)

/-- Fact 0 in the requested form: for a pair `P` with `P ∩ q = ∅`, `P ∈ CN(q) ↔ q ⊆ L_P`. -/
theorem fact0 {H : Finset (Finset V)} {q P : Finset V} (hP : P ∈ pairs V)
    (_hdis : P ∩ q = ∅) : P ∈ CN H q ↔ q ⊆ link H P := by
  rw [mem_CN_iff_subset_link]
  exact ⟨fun h => h.2, fun h => ⟨hP, h⟩⟩

/-! ## Codegree and link -/

/-- `k_p = |L_p|` for a 2-set `p` in a 3-uniform `H`. -/
theorem codeg_eq_card_link {H : Finset (Finset V)} (hH : Uniform H) {p : Finset V}
    (hp : p.card = 2) : codeg H p = (link H p).card := by
  have himg : H.filter (fun e => p ⊆ e) = (link H p).image (fun v => insert v p) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_image, mem_link]
    constructor
    · rintro ⟨he, hpe⟩
      have hc : (e \ p).card = 1 := by
        have h1 := Finset.card_sdiff_of_subset hpe
        have h2 := hH e he
        omega
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc
      have hvmem : v ∈ e \ p := by rw [hv]; exact Finset.mem_singleton_self v
      rw [Finset.mem_sdiff] at hvmem
      have hins : insert v p = e := by
        rw [Finset.insert_eq, ← hv, Finset.sdiff_union_of_subset hpe]
      exact ⟨v, ⟨hvmem.2, hins ▸ he⟩, hins⟩
    · rintro ⟨v, ⟨_, hvH⟩, rfl⟩
      exact ⟨hvH, Finset.subset_insert v p⟩
  unfold codeg
  rw [himg, Finset.card_image_of_injOn]
  intro v hv w hw hvw
  rw [Finset.mem_coe, mem_link] at hv hw
  have hvw' : insert v p = insert w p := hvw
  have hmem : v ∈ insert w p := by rw [← hvw']; exact Finset.mem_insert_self v p
  rcases Finset.mem_insert.mp hmem with h | h
  · exact h
  · exact absurd h hv.1

/-- For a 3-uniform `H` and a pair `p`, the condition `v ∉ p` in `link` is automatic, so `link H p` is
exactly the text's `L_p = {x : p + x ∈ H}`. -/
theorem mem_link_iff_of_uniform {H : Finset (Finset V)} (hH : Uniform H) {p : Finset V}
    (hp : p.card = 2) {v : V} : v ∈ link H p ↔ insert v p ∈ H := by
  rw [mem_link]
  refine ⟨fun h => h.2, fun h => ⟨fun hvp => ?_, h⟩⟩
  have h3 := hH _ h
  rw [Finset.insert_eq_of_mem hvp, hp] at h3
  omega

theorem codeg_pos_of_mem_shadow {H : Finset (Finset V)} {p : Finset V} (hp : p ∈ shadow H) :
    0 < codeg H p := by
  obtain ⟨-, e, he, hpe⟩ := mem_shadow.mp hp
  exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hpe⟩⟩

/-- `∂H = {p : k_p ≥ 1}`: a pair is in the shadow iff its codegree is positive. -/
theorem mem_shadow_iff_codeg_pos {H : Finset (Finset V)} {p : Finset V} :
    p ∈ shadow H ↔ p ∈ pairs V ∧ 0 < codeg H p := by
  constructor
  · intro hp
    exact ⟨shadow_subset_pairs H hp, codeg_pos_of_mem_shadow hp⟩
  · rintro ⟨hp, hpos⟩
    have hpos' : 0 < (H.filter (fun e => p ⊆ e)).card := hpos
    obtain ⟨e, he⟩ := Finset.card_pos.mp hpos'
    rw [Finset.mem_filter] at he
    exact mem_shadow.mpr ⟨mem_pairs.mp hp, e, he.1, he.2⟩

theorem codeg_eq_zero_of_notMem_shadow {H : Finset (Finset V)} {p : Finset V}
    (hp : p ∈ pairs V) (hns : p ∉ shadow H) : codeg H p = 0 := by
  unfold codeg
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hpe
  exact hns (mem_shadow.mpr ⟨mem_pairs.mp hp, e, he, hpe⟩)

/-- Every member of `CN(q)` has codegree at least 2 (Fact 0). -/
theorem two_le_codeg_of_mem_CN {H : Finset (Finset V)} (hH : Uniform H) {q P : Finset V}
    (hq : q.card = 2) (hP : P ∈ CN H q) : 2 ≤ codeg H P := by
  obtain ⟨hPp, hsub⟩ := mem_CN_iff_subset_link.mp hP
  rw [codeg_eq_card_link hH (mem_pairs.mp hPp)]
  have := Finset.card_le_card hsub
  omega

/-! ## Step (i): Σ_{p ∈ ∂H} k_p = 3|H| -/

theorem shadow_filter_subset {H : Finset (Finset V)} {e : Finset V} (he : e ∈ H) :
    (shadow H).filter (fun p => p ⊆ e) = e.powersetCard 2 := by
  ext p
  simp only [Finset.mem_filter, mem_shadow, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨hc, -⟩, hpe⟩
    exact ⟨hpe, hc⟩
  · rintro ⟨hpe, hc⟩
    exact ⟨⟨hc, e, he, hpe⟩, hpe⟩

/-- **Step (i).** Each edge has exactly three 2-subsets, so `Σ_{p ∈ ∂H} k_p = 3|H|`. -/
theorem sum_codeg_shadow (H : Finset (Finset V)) (hH : Uniform H) :
    ∑ p ∈ shadow H, codeg H p = 3 * H.card := by
  have hswap : ∑ p ∈ shadow H, codeg H p =
      ∑ e ∈ H, ((shadow H).filter (fun p => p ⊆ e)).card := by
    simp only [codeg, Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap]
  have hinner : ∀ e ∈ H, ((shadow H).filter (fun p => p ⊆ e)).card = 3 := by
    intro e he
    rw [shadow_filter_subset he, Finset.card_powersetCard, hH e he]
    decide
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul, mul_comm]

/-! ## Step (ii): Σ_{q ∈ colink} R_q -/

/-- For a pair `P`, the co-link pairs inside `L_P` are exactly the 2-subsets of `L_P`. -/
theorem colink_filter_subset_link (H : Finset (Finset V)) {P : Finset V} (hP : P ∈ pairs V) :
    (colink H).filter (fun q => q ⊆ link H P) = (link H P).powersetCard 2 := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_powersetCard, mem_colink]
  constructor
  · rintro ⟨⟨hc, -⟩, hsub⟩
    exact ⟨hsub, hc⟩
  · rintro ⟨hsub, hc⟩
    exact ⟨⟨hc, P, mem_CN_iff_subset_link.mpr ⟨hP, hsub⟩⟩, hsub⟩

/-- Double counting over the incidence `q ⊆ L_P` (Fact 0):
`Σ_{q ∈ colink} Σ_{P ∈ CN(q)} f(P) = Σ_{P pair} C(|L_P|, 2) f(P)`. -/
theorem sum_colink_sum_CN (H : Finset (Finset V)) (f : Finset V → ℚ) :
    ∑ q ∈ colink H, ∑ P ∈ CN H q, f P =
      ∑ P ∈ pairs V, (((link H P).powersetCard 2).card : ℚ) * f P := by
  have h1 : ∀ q ∈ colink H, ∑ P ∈ CN H q, f P =
      ∑ P ∈ pairs V, if q ⊆ link H P then f P else 0 := by
    intro q _
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext P
    rw [Finset.mem_filter, mem_CN_iff_subset_link]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun P hP => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, colink_filter_subset_link H hP]

/-- `Σ_{q ∈ colink} s_q = Σ_{P pair} C(k_P, 2)` (second half of Fact 0). -/
theorem sum_card_CN (H : Finset (Finset V)) (hH : Uniform H) :
    ∑ q ∈ colink H, ((CN H q).card : ℚ) = ∑ P ∈ pairs V, (((codeg H P).choose 2 : ℕ) : ℚ) := by
  have h := sum_colink_sum_CN H (fun _ => (1 : ℚ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [h]
  refine Finset.sum_congr rfl (fun P hP => ?_)
  rw [Finset.card_powersetCard, codeg_eq_card_link hH (mem_pairs.mp hP)]

/-- `C(k, 2) γ(k) = k - 2 + [k = 1]` for `k ≥ 1`. -/
theorem choose_two_mul_γ {k : ℕ} (hk : 0 < k) :
    ((k.choose 2 : ℕ) : ℚ) * γ k = (k : ℚ) - 2 + (if k = 1 then (1 : ℚ) else 0) := by
  by_cases h1 : k = 1
  · subst h1
    rw [Nat.choose_eq_zero_of_lt (by norm_num : 1 < 2)]
    norm_num
  · have h2 : 2 ≤ k := by omega
    rw [if_neg h1, Nat.cast_choose_two, add_zero]
    have hk0 : (k : ℚ) ≠ 0 := by
      have : (0 : ℚ) < k := by exact_mod_cast hk
      exact ne_of_gt this
    have hk1 : (k : ℚ) - 1 ≠ 0 := by
      have : (2 : ℚ) ≤ k := by exact_mod_cast h2
      intro h
      linarith
    have ha : (k : ℚ) * ((k : ℚ) - 1) ≠ 0 := mul_ne_zero hk0 hk1
    unfold γ
    calc (k : ℚ) * ((k : ℚ) - 1) / 2 * (2 * ((k : ℚ) - 2) / ((k : ℚ) * ((k : ℚ) - 1)))
        = ((k : ℚ) * ((k : ℚ) - 1)) / ((k : ℚ) * ((k : ℚ) - 1)) * ((k : ℚ) - 2) := by ring
      _ = (k : ℚ) - 2 := by rw [div_self ha, one_mul]

/-- **Step (ii).** `Σ_{q ∈ colink} R_q = Σ_{P : k_P ≥ 2} (k_P - 2) = 3|H| - 2|∂H| + n_1`. -/
theorem sum_colink_R (H : Finset (Finset V)) (hH : Uniform H) :
    ∑ q ∈ colink H, R H q = 3 * (H.card : ℚ) - 2 * ((shadow H).card : ℚ) + (n1 H : ℚ) := by
  have h0 : ∑ q ∈ colink H, R H q =
      ∑ P ∈ pairs V, (((codeg H P).choose 2 : ℕ) : ℚ) * γ (codeg H P) := by
    simp only [R]
    rw [sum_colink_sum_CN]
    refine Finset.sum_congr rfl (fun P hP => ?_)
    rw [Finset.card_powersetCard, ← codeg_eq_card_link hH (mem_pairs.mp hP)]
  have hvan : ∀ P ∈ pairs V, P ∉ shadow H →
      (((codeg H P).choose 2 : ℕ) : ℚ) * γ (codeg H P) = 0 := by
    intro P hP hns
    rw [codeg_eq_zero_of_notMem_shadow hP hns, Nat.choose_eq_zero_of_lt (by norm_num : 0 < 2)]
    simp
  have hsh : ∀ P ∈ shadow H, (((codeg H P).choose 2 : ℕ) : ℚ) * γ (codeg H P) =
      (codeg H P : ℚ) - 2 + (if codeg H P = 1 then (1 : ℚ) else 0) :=
    fun P hP => choose_two_mul_γ (codeg_pos_of_mem_shadow hP)
  have hk : ∑ P ∈ shadow H, (codeg H P : ℚ) = 3 * (H.card : ℚ) := by
    exact_mod_cast sum_codeg_shadow H hH
  have hn1 : (n1 H : ℚ) = ∑ P ∈ shadow H, (if codeg H P = 1 then (1 : ℚ) else 0) := by
    rw [n1, Finset.natCast_card_filter]
  rw [h0, ← Finset.sum_subset (shadow_subset_pairs H) hvan, Finset.sum_congr rfl hsh,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, hk, ← hn1, Finset.sum_const, nsmul_eq_mul]
  ring

/-! ## Step (iii): assembly -/

/-- `|O(H)| = |∂H| + g`. -/
theorem card_O_eq_card_shadow_add_g (H : Finset (Finset V)) :
    (O H).card = (shadow H).card + g H := by
  have h := Finset.card_sdiff_add_card (colink H) (shadow H)
  rw [Finset.union_comm] at h
  unfold O g
  omega

/-- `|∂H \ colink| + |colink| = |O(H)|`. -/
theorem card_shadow_sdiff_add_card_colink (H : Finset (Finset V)) :
    (shadow H \ colink H).card + (colink H).card = (O H).card :=
  Finset.card_sdiff_add_card _ _

/-- **Theorem 1, identity (II).** For every finite 3-uniform hypergraph `H` (no avoidance hypothesis),
`3(|O(H)| - |H|) = 2g + |∂H \ colink| + n_1 + Σ_{q ∈ colink} (1 - R_q)`, over `ℚ`. -/
theorem identity_II (H : Finset (Finset V)) (hH : Uniform H) :
    3 * (((O H).card : ℚ) - (H.card : ℚ)) =
      2 * (g H : ℚ) + ((shadow H \ colink H).card : ℚ) + (n1 H : ℚ) +
        ∑ q ∈ colink H, (1 - R H q) := by
  have hO1 : ((O H).card : ℚ) = ((shadow H).card : ℚ) + (g H : ℚ) := by
    exact_mod_cast card_O_eq_card_shadow_add_g H
  have hO2 : ((shadow H \ colink H).card : ℚ) + ((colink H).card : ℚ) = ((O H).card : ℚ) := by
    exact_mod_cast card_shadow_sdiff_add_card_colink H
  rw [Finset.sum_sub_distrib, sum_colink_R H hH, Finset.sum_const, nsmul_eq_mul, mul_one]
  linarith

end Identity
end Erdos643R3

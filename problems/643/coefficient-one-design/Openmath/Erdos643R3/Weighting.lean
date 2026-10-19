import Mathlib
import Openmath.Erdos643R3.HypergraphBasics
import Openmath.Erdos643R3.Identity

/-!
# The weightings `σ`, `τ` and the common-link lemmas (Erdős 643, r = 3)

The foundational weighting definitions and proofs are given below. Everything is for a finite vertex type `V` and a family
`H : Finset (Finset V)`; the definitions `pairs`, `shadow`, `codeg`, `link`, `CN`, `colink` and `Uniform` are those of
`Openmath.Erdos643R3.Identity` (imported, not redefined).

Correspondence with the written text.
* "H is avoiding" is `¬ Erdos643.HypergraphBasics.Forbidden H` exactly: no four pairwise distinct triples
  `A, B, C, D ∈ H` with `A ∩ B = ∅`, `C ∩ D = ∅`, `A ∪ B = C ∪ D`.
* `k_P` is `codeg H P`, `L(P)` is `link H P`, `s_q` is `(CN H q).card`, `∂H` is `shadow H`, `CL(H)` is `colink H`.
* `sigmaW H T` is `σ(T) = Σ_{P ⊂ T, |P| = 2} 1/k_P`, summed over `T.powersetCard 2`.
* `tauW H T` is `τ(T)`, the sum over the options `q` of `T` of `1/(2 s_q)`. As `a` ranges over `T`, the pair
  `P = T.erase a` ranges over the three pairs of `T` (for `|T| = 3`) and `a = a_P` is the vertex of `T` outside `P`;
  the options through `P` are the pairs `{a, z}` with `z ∈ L(P) \ {a_P}`, i.e. `z ∈ (link H P).erase a`.
  `tauW_eq_sum_pairs` restates `τ` as a sum over the pairs `P ∈ T.powersetCard 2` and `z ∈ L(P) \ T`, with the option
  written `insert z (T \ P)` (`T \ P = {a_P}`), and `sigmaW_eq_sum_vertices` restates `σ` over the vertices.
* `s^b_{az} = |L(ab) ∩ L(bz)|` is `(link H {a, b} ∩ link H {b, z}).card`.

Main declarations.
* Lemma 1 (common link): `CN_intersecting`, `exists_common_vertex`, `common_vertex_unique`, `CN_star`, `lemma1`.
* Lemma 2 (option bound): `option_bound_link` (`s_{az} ≤ max(3, s^b_{az}, s^c_{az})`), `option_bound`
  (`≤ max(3, k_ab, k_ac)`), for `T = {a,b,c} ∈ H` and `z ∈ L(bc) \ {a}`.
* Lemma 3 (exchange lemma): `exchange` and its mirror `exchange_mirror`.
* Lemma 4 (double counting, every uniform `H`, no avoidance): `sum_sigmaW`, `sum_tauW`, `lemma4`.
-/

set_option autoImplicit false

namespace Erdos643R3
namespace Weighting

open Finset hiding shadow
open Erdos643R3.Identity

/-! ## Finset facts about 2-sets and 3-sets -/

section FinsetFacts

variable {α : Type*} [DecidableEq α]

lemma triple_ne {a b c : α} (h : ({a, b, c} : Finset α).card = 3) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  refine ⟨fun hab => ?_, fun hac => ?_, fun hbc => ?_⟩
  · rw [hab, insert_eq_of_mem (mem_insert_self b {c})] at h
    have h2 : ({b, c} : Finset α).card ≤ 2 := card_le_two
    omega
  · rw [hac, insert_eq_of_mem (mem_insert_of_mem (mem_singleton_self c))] at h
    have h2 : ({b, c} : Finset α).card ≤ 2 := card_le_two
    omega
  · rw [hbc, insert_eq_of_mem (mem_singleton_self c)] at h
    have h2 : ({a, c} : Finset α).card ≤ 2 := card_le_two
    omega

lemma eq_pair_of_mem {P : Finset α} (hP : P.card = 2) {x y : α} (hxy : x ≠ y)
    (hx : x ∈ P) (hy : y ∈ P) : P = {x, y} := by
  symm
  apply eq_of_subset_of_card_le
  · intro t ht
    rw [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hx
    · exact hy
  · have := card_pair hxy
    omega

lemma exists_eq_pair_of_mem {P : Finset α} (hP : P.card = 2) {w : α} (hw : w ∈ P) :
    ∃ u, u ≠ w ∧ P = {w, u} := by
  obtain ⟨p, q, hpq, rfl⟩ := card_eq_two.mp hP
  rw [mem_insert, mem_singleton] at hw
  rcases hw with h | h
  · refine ⟨q, ?_, ?_⟩
    · rw [h]; exact hpq.symm
    · rw [h]
  · refine ⟨p, ?_, ?_⟩
    · rw [h]; exact hpq
    · rw [h]; exact pair_comm p q

lemma mem_or_mem_of_not_disjoint {x y : α} {Q : Finset α}
    (h : ¬ Disjoint ({x, y} : Finset α) Q) : x ∈ Q ∨ y ∈ Q := by
  obtain ⟨t, ht1, ht2⟩ := not_disjoint_iff.mp h
  rw [mem_insert, mem_singleton] at ht1
  rcases ht1 with rfl | rfl
  · exact Or.inl ht2
  · exact Or.inr ht2

lemma pair_inter_pair_eq_empty {a b c d : α} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : ({a, b} : Finset α) ∩ {c, d} = ∅ := by
  ext t
  simp only [mem_inter, mem_insert, mem_singleton, notMem_empty, iff_false, not_and]
  rintro (rfl | rfl) (h | h)
  · exact hac h
  · exact had h
  · exact hbc h
  · exact hbd h

/-- Lemma 1, second half: a pairwise intersecting family of 2-sets with at least four members has a common
vertex (an intersecting family of 2-sets without a common vertex is a triangle). -/
theorem exists_common_vertex {F : Finset (Finset α)} (hcard : ∀ P ∈ F, P.card = 2)
    (hint : ∀ P ∈ F, ∀ Q ∈ F, ¬ Disjoint P Q) (h4 : 4 ≤ F.card) :
    ∃ w, ∀ P ∈ F, w ∈ P := by
  obtain ⟨P₀, hP₀⟩ : F.Nonempty := card_pos.mp (by omega)
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp (hcard P₀ hP₀)
  have hmeet : ∀ Q ∈ F, u ∈ Q ∨ v ∈ Q := fun Q hQ =>
    mem_or_mem_of_not_disjoint (hint _ hP₀ Q hQ)
  by_cases hu : ∀ Q ∈ F, u ∈ Q
  · exact ⟨u, hu⟩
  by_cases hv : ∀ Q ∈ F, v ∈ Q
  · exact ⟨v, hv⟩
  exfalso
  obtain ⟨A, hA, huA⟩ : ∃ A ∈ F, u ∉ A := by
    by_contra h
    exact hu (fun Q hQ => by by_contra h'; exact h ⟨Q, hQ, h'⟩)
  obtain ⟨B, hB, hvB⟩ : ∃ B ∈ F, v ∉ B := by
    by_contra h
    exact hv (fun Q hQ => by by_contra h'; exact h ⟨Q, hQ, h'⟩)
  have hvA : v ∈ A := (hmeet A hA).resolve_left huA
  have huB : u ∈ B := (hmeet B hB).resolve_right hvB
  obtain ⟨w, hwA, hwB⟩ := not_disjoint_iff.mp (hint A hA B hB)
  have hwu : w ≠ u := fun h => huA (by rw [← h]; exact hwA)
  have hwv : w ≠ v := fun h => hvB (by rw [← h]; exact hwB)
  have hAeq : A = {v, w} := eq_pair_of_mem (hcard A hA) (Ne.symm hwv) hvA hwA
  have hBeq : B = {u, w} := eq_pair_of_mem (hcard B hB) (Ne.symm hwu) huB hwB
  subst hAeq
  subst hBeq
  have hsub : F ⊆ {{u, v}, {u, w}, {v, w}} := by
    intro Q hQ
    have hQc := hcard Q hQ
    have hQA : v ∈ Q ∨ w ∈ Q := mem_or_mem_of_not_disjoint (hint _ hA Q hQ)
    have hQB : u ∈ Q ∨ w ∈ Q := mem_or_mem_of_not_disjoint (hint _ hB Q hQ)
    rw [mem_insert, mem_insert, mem_singleton]
    by_cases huQ : u ∈ Q
    · by_cases hvQ : v ∈ Q
      · exact Or.inl (eq_pair_of_mem hQc huv huQ hvQ)
      · exact Or.inr (Or.inl (eq_pair_of_mem hQc (Ne.symm hwu) huQ (hQA.resolve_left hvQ)))
    · have hvQ := (hmeet Q hQ).resolve_left huQ
      have hwQ := hQB.resolve_left huQ
      exact Or.inr (Or.inr (eq_pair_of_mem hQc (Ne.symm hwv) hvQ hwQ))
  have h1 := card_le_card hsub
  have h2 : ({{u, v}, {u, w}, {v, w}} : Finset (Finset α)).card ≤ 3 := card_le_three
  omega

/-- Lemma 1, uniqueness: two distinct 2-sets share at most one vertex, so a common vertex of a family of
2-sets with at least two members is unique. -/
theorem common_vertex_unique {F : Finset (Finset α)} (hcard : ∀ P ∈ F, P.card = 2)
    (h2 : 2 ≤ F.card) {w w' : α} (hw : ∀ P ∈ F, w ∈ P) (hw' : ∀ P ∈ F, w' ∈ P) : w = w' := by
  by_contra hne
  have hsub : F ⊆ {{w, w'}} := by
    intro P hP
    rw [mem_singleton]
    exact eq_pair_of_mem (hcard P hP) hne (hw P hP) (hw' P hP)
  have := card_le_card hsub
  rw [card_singleton] at this
  omega

/-- For `|T| = 3`, summing over the three pairs of `T` is summing over the vertices `a ∈ T` with `P = T.erase a`. -/
theorem sum_powersetCard_two_eq {T : Finset α} (hT : T.card = 3) (f : Finset α → ℚ) :
    ∑ P ∈ T.powersetCard 2, f P = ∑ a ∈ T, f (T.erase a) := by
  symm
  refine Finset.sum_bij (fun a _ => T.erase a) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro a ha
    show T.erase a ∈ T.powersetCard 2
    rw [mem_powersetCard]
    refine ⟨erase_subset a T, ?_⟩
    have := card_erase_of_mem ha
    omega
  · intro a ha b hb hab
    have hab' : T.erase a = T.erase b := hab
    by_contra hne
    have hmem : a ∈ T.erase b := mem_erase.mpr ⟨hne, ha⟩
    rw [← hab'] at hmem
    exact notMem_erase a T hmem
  · intro P hP
    rw [mem_powersetCard] at hP
    have hc : (T \ P).card = 1 := by
      have := card_sdiff_of_subset hP.1
      omega
    obtain ⟨a, ha⟩ := card_eq_one.mp hc
    have haT : a ∈ T \ P := by rw [ha]; exact mem_singleton_self a
    refine ⟨a, (mem_sdiff.mp haT).1, ?_⟩
    show T.erase a = P
    ext x
    rw [mem_erase]
    constructor
    · rintro ⟨hxa, hxT⟩
      by_contra hxP
      have hx : x ∈ T \ P := mem_sdiff.mpr ⟨hxT, hxP⟩
      rw [ha, mem_singleton] at hx
      exact hxa hx
    · intro hxP
      refine ⟨?_, hP.1 hxP⟩
      rintro rfl
      exact (mem_sdiff.mp haT).2 hxP

/-- For a fixed `a ∈ s`, the pairs `{a, z}` (`z ∈ s`, `z ≠ a`) are exactly the 2-subsets of `s` containing `a`. -/
theorem sum_erase_pair_eq (s : Finset α) (a : α) (ha : a ∈ s) (f : Finset α → ℚ) :
    ∑ z ∈ s.erase a, f {a, z} = ∑ q ∈ (s.powersetCard 2).filter (fun q => a ∈ q), f q := by
  refine Finset.sum_bij (fun z _ => ({a, z} : Finset α)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro z hz
    show ({a, z} : Finset α) ∈ (s.powersetCard 2).filter (fun q => a ∈ q)
    obtain ⟨hza, hzs⟩ := mem_erase.mp hz
    rw [mem_filter, mem_powersetCard]
    refine ⟨⟨?_, card_pair (Ne.symm hza)⟩, mem_insert_self a {z}⟩
    intro t ht
    rw [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact ha
    · exact hzs
  · intro z₁ hz₁ z₂ _ h
    have h' : ({a, z₁} : Finset α) = {a, z₂} := h
    have hm : z₁ ∈ ({a, z₂} : Finset α) := by
      rw [← h']; exact mem_insert_of_mem (mem_singleton_self z₁)
    rw [mem_insert, mem_singleton] at hm
    rcases hm with hm | hm
    · exact absurd hm (mem_erase.mp hz₁).1
    · exact hm
  · intro q hq
    rw [mem_filter, mem_powersetCard] at hq
    obtain ⟨⟨hqs, hqc⟩, haq⟩ := hq
    obtain ⟨u, hua, rfl⟩ := exists_eq_pair_of_mem hqc haq
    exact ⟨u, mem_erase.mpr ⟨hua, hqs (mem_insert_of_mem (mem_singleton_self u))⟩, rfl⟩

/-- Ordered pairs of distinct elements of `s` versus 2-subsets of `s`:
`Σ_{a ∈ s} Σ_{z ∈ s, z ≠ a} f({a,z}) = Σ_{q ⊆ s, |q| = 2} 2 f(q)`. -/
theorem sum_sum_erase_pair (s : Finset α) (f : Finset α → ℚ) :
    ∑ a ∈ s, ∑ z ∈ s.erase a, f {a, z} = ∑ q ∈ s.powersetCard 2, 2 * f q := by
  have hc : ∀ (a : α) (q : Finset α), a ∈ s ∧ q ∈ (s.powersetCard 2).filter (fun q => a ∈ q) ↔
      a ∈ q ∧ q ∈ s.powersetCard 2 := by
    intro a q
    rw [mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨-, ⟨hqs, hqc⟩, haq⟩
      exact ⟨haq, hqs, hqc⟩
    · rintro ⟨haq, hqs, hqc⟩
      exact ⟨hqs haq, ⟨hqs, hqc⟩, haq⟩
  rw [Finset.sum_congr rfl (fun a ha => sum_erase_pair_eq s a ha f), Finset.sum_comm' hc]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  rw [Finset.sum_const, nsmul_eq_mul, (mem_powersetCard.mp hq).2, Nat.cast_ofNat]

end FinsetFacts

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The weightings -/

/-- `σ(T) = Σ_{P ⊂ T, |P| = 2} 1/k_P`, over `ℚ`. -/
def sigmaW (H : Finset (Finset V)) (T : Finset V) : ℚ :=
  ∑ P ∈ T.powersetCard 2, 1 / (codeg H P : ℚ)

/-- `τ(T) = Σ over the options q of T of 1/(2 s_q)`, over `ℚ`: for `a ∈ T` the pair is `P = T.erase a` (so
`a = a_P`), and the options through `P` are `{a, z}` with `z ∈ L(P) \ {a}`. -/
def tauW (H : Finset (Finset V)) (T : Finset V) : ℚ :=
  ∑ a ∈ T, ∑ z ∈ (link H (T.erase a)).erase a, 1 / (2 * ((CN H {a, z}).card : ℚ))

omit [Fintype V] in
theorem sigmaW_eq_sum_vertices {H : Finset (Finset V)} {T : Finset V} (hT : T.card = 3) :
    sigmaW H T = ∑ a ∈ T, 1 / (codeg H (T.erase a) : ℚ) :=
  sum_powersetCard_two_eq hT (fun P => 1 / (codeg H P : ℚ))

/-- `τ` as a sum over the three pairs `P ⊂ T` and `z ∈ L(P) \ {a_P}` (`= L(P) \ T`, since `L(P) ∩ P = ∅`); the
option is `{a_P, z} = insert z (T \ P)`. -/
theorem tauW_eq_sum_pairs {H : Finset (Finset V)} {T : Finset V} (hT : T.card = 3) :
    tauW H T = ∑ P ∈ T.powersetCard 2, ∑ z ∈ link H P \ T,
      1 / (2 * ((CN H (insert z (T \ P))).card : ℚ)) := by
  rw [sum_powersetCard_two_eq hT]
  unfold tauW
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [sdiff_erase_self ha]
  have hset : link H (T.erase a) \ T = (link H (T.erase a)).erase a := by
    ext z
    rw [mem_sdiff, mem_erase]
    constructor
    · rintro ⟨hz, hzT⟩
      exact ⟨fun h => hzT (by rw [h]; exact ha), hz⟩
    · rintro ⟨hza, hz⟩
      refine ⟨hz, fun hzT => ?_⟩
      exact (mem_link.mp hz).1 (mem_erase.mpr ⟨hza, hzT⟩)
  rw [hset]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [pair_comm z a]

/-! ## Lemma 4: double counting (every uniform `H`) -/

/-- **Lemma 4, first identity.** `Σ_{T ∈ H} σ(T) = |∂H|` (no hypothesis on `H`). -/
theorem sum_sigmaW (H : Finset (Finset V)) :
    ∑ T ∈ H, sigmaW H T = ((shadow H).card : ℚ) := by
  have hc : ∀ (T P : Finset V), T ∈ H ∧ P ∈ T.powersetCard 2 ↔
      T ∈ H.filter (fun e => P ⊆ e) ∧ P ∈ shadow H := by
    intro T P
    rw [mem_powersetCard, mem_filter, mem_shadow]
    constructor
    · rintro ⟨hT, hPT, hPc⟩
      exact ⟨⟨hT, hPT⟩, hPc, T, hT, hPT⟩
    · rintro ⟨⟨hT, hPT⟩, hPc, -⟩
      exact ⟨hT, hPT, hPc⟩
  have hin : ∀ P ∈ shadow H, ∑ T ∈ H.filter (fun e => P ⊆ e), 1 / (codeg H P : ℚ) = 1 := by
    intro P hP
    rw [sum_const, nsmul_eq_mul]
    have hpos : (0 : ℚ) < (codeg H P : ℚ) := by exact_mod_cast codeg_pos_of_mem_shadow hP
    have hk : ((H.filter (fun e => P ⊆ e)).card : ℚ) = (codeg H P : ℚ) := rfl
    rw [hk, mul_one_div, div_self (ne_of_gt hpos)]
  unfold sigmaW
  rw [sum_comm' hc, sum_congr rfl hin, sum_const, nsmul_eq_mul, mul_one]

/-- Reindexing incidences `(T, a)` with `a ∈ T ∈ H` as `(P, a)` with `P` a pair and `a ∈ L(P)`
(`P = T.erase a`, `T = insert a P`), for uniform `H`. -/
theorem sum_vertex_eq_sum_link {H : Finset (Finset V)} (hH : Uniform H)
    (F : Finset V → V → ℚ) :
    ∑ T ∈ H, ∑ a ∈ T, F (T.erase a) a = ∑ P ∈ pairs V, ∑ a ∈ link H P, F P a := by
  have h1 : ∀ (T : Finset V) (a : V), T ∈ H ∧ a ∈ T ↔
      T ∈ H.filter (fun e => a ∈ e) ∧ a ∈ (univ : Finset V) := by
    intro T a
    simp only [mem_filter, mem_univ, and_true]
  have h2 : ∀ (P : Finset V) (a : V), P ∈ pairs V ∧ a ∈ link H P ↔
      P ∈ (pairs V).filter (fun p => a ∈ link H p) ∧ a ∈ (univ : Finset V) := by
    intro P a
    simp only [mem_filter, mem_univ, and_true]
  rw [sum_comm' h1, sum_comm' h2]
  refine sum_congr rfl (fun a _ => ?_)
  refine sum_nbij' (fun T => T.erase a) (fun P => insert a P) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    show T.erase a ∈ (pairs V).filter (fun p => a ∈ link H p)
    rw [mem_filter] at hT ⊢
    refine ⟨?_, ?_⟩
    · rw [mem_pairs]
      have h1 := card_erase_of_mem hT.2
      have h2 := hH T hT.1
      omega
    · rw [mem_link]
      exact ⟨notMem_erase a T, by rw [insert_erase hT.2]; exact hT.1⟩
  · intro P hP
    show insert a P ∈ H.filter (fun e => a ∈ e)
    rw [mem_filter] at hP ⊢
    exact ⟨(mem_link.mp hP.2).2, mem_insert_self a P⟩
  · intro T hT
    exact insert_erase (mem_filter.mp hT).2
  · intro P hP
    exact erase_insert (mem_link.mp (mem_filter.mp hP).2).1
  · intro T _
    rfl

/-- **Lemma 4, second identity.** `Σ_{T ∈ H} τ(T) = |CL(H)|` for every uniform `H` (no avoidance). -/
theorem sum_tauW (H : Finset (Finset V)) (hH : Uniform H) :
    ∑ T ∈ H, tauW H T = ((colink H).card : ℚ) := by
  have e1 := sum_vertex_eq_sum_link hH
    (fun P a => ∑ z ∈ (link H P).erase a, 1 / (2 * ((CN H {a, z}).card : ℚ)))
  have e2 : ∀ P ∈ pairs V,
      ∑ a ∈ link H P, ∑ z ∈ (link H P).erase a, 1 / (2 * ((CN H {a, z}).card : ℚ)) =
        ∑ q ∈ (link H P).powersetCard 2, 2 * (1 / (2 * ((CN H q).card : ℚ))) :=
    fun P _ => sum_sum_erase_pair (link H P) (fun q => 1 / (2 * ((CN H q).card : ℚ)))
  have hc : ∀ (P q : Finset V), P ∈ pairs V ∧ q ∈ (link H P).powersetCard 2 ↔
      P ∈ CN H q ∧ q ∈ pairs V := by
    intro P q
    rw [mem_CN_iff_subset_link, mem_powersetCard]
    constructor
    · rintro ⟨hP, hq, hqc⟩
      exact ⟨⟨hP, hq⟩, mem_pairs.mpr hqc⟩
    · rintro ⟨⟨hP, hq⟩, hqc⟩
      exact ⟨hP, hq, mem_pairs.mp hqc⟩
  have hq1 : ∀ q ∈ pairs V, ∑ P ∈ CN H q, 2 * (1 / (2 * ((CN H q).card : ℚ))) =
      if (CN H q).Nonempty then 1 else 0 := by
    intro q _
    rw [sum_const, nsmul_eq_mul]
    by_cases hne : (CN H q).Nonempty
    · rw [if_pos hne]
      have hpos : (0 : ℚ) < ((CN H q).card : ℚ) := by exact_mod_cast hne.card_pos
      have h2 : (2 : ℚ) * ((CN H q).card : ℚ) ≠ 0 := mul_ne_zero two_ne_zero (ne_of_gt hpos)
      calc ((CN H q).card : ℚ) * (2 * (1 / (2 * ((CN H q).card : ℚ))))
          = (2 * ((CN H q).card : ℚ)) / (2 * ((CN H q).card : ℚ)) := by ring
        _ = 1 := div_self h2
    · rw [if_neg hne, not_nonempty_iff_eq_empty.mp hne, card_empty]
      simp
  unfold tauW
  rw [e1, sum_congr rfl e2, sum_comm' hc, sum_congr rfl hq1, colink, natCast_card_filter]

/-- **Lemma 4.** For every uniform `H`: `Σ_{T ∈ H} σ(T) = |∂H|` and `Σ_{T ∈ H} τ(T) = |CL(H)|`. -/
theorem lemma4 (H : Finset (Finset V)) (hH : Uniform H) :
    ∑ T ∈ H, sigmaW H T = ((shadow H).card : ℚ) ∧
      ∑ T ∈ H, tauW H T = ((colink H).card : ℚ) :=
  ⟨sum_sigmaW H, sum_tauW H hH⟩

/-! ## Lemma 1: common links of an avoiding `H` -/

omit [Fintype V] [DecidableEq V] in
/-- `Identity.Uniform` and `HypergraphBasics.Uniform` have the same body. -/
theorem uniform_hb {H : Finset (Finset V)} (hH : Uniform H) :
    Erdos643.HypergraphBasics.Uniform H := hH

/-- A member of `CN(x,y)` is a common pair of `x` and `y` in the sense of `HypergraphBasics`. -/
theorem commonPair_of_mem_CN {H : Finset (Finset V)} {x y : V} {P : Finset V}
    (hP : P ∈ CN H {x, y}) : Erdos643.HypergraphBasics.CommonPair H x y P := by
  obtain ⟨hPp, hdis, hx, hy⟩ := mem_CN_pair.mp hP
  refine ⟨mem_pairs.mp hPp, ?_, ?_, hx, hy⟩
  · intro hxP
    have hm : x ∈ P ∩ {x, y} := mem_inter.mpr ⟨hxP, mem_insert_self x {y}⟩
    rw [hdis] at hm
    exact notMem_empty x hm
  · intro hyP
    have hm : y ∈ P ∩ {x, y} := mem_inter.mpr ⟨hyP, mem_insert_of_mem (mem_singleton_self y)⟩
    rw [hdis] at hm
    exact notMem_empty y hm

/-- **Lemma 1, first half.** If `H` is avoiding (`¬ Forbidden H`), every `CN(x,y)` is intersecting. -/
theorem CN_intersecting {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) {x y : V} (hxy : x ≠ y)
    {P Q : Finset V} (hP : P ∈ CN H {x, y}) (hQ : Q ∈ CN H {x, y}) : ¬ Disjoint P Q := by
  intro hPQ
  exact hav (Erdos643.HypergraphBasics.commonMatching_forbidden (uniform_hb hH)
    ⟨x, y, hxy, P, Q, commonPair_of_mem_CN hP, commonPair_of_mem_CN hQ, hPQ⟩)

/-- Lemma 1: an avoiding `H` has every `CN(x,y)` with at least four members a star (common vertex). -/
theorem CN_star {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) {x y : V} (hxy : x ≠ y)
    (h4 : 4 ≤ (CN H {x, y}).card) : ∃ w, ∀ P ∈ CN H {x, y}, w ∈ P :=
  exists_common_vertex (fun _ hP => (mem_CN.mp hP).1)
    (fun _ hP _ hQ => CN_intersecting hH hav hxy hP hQ) h4

/-- **Lemma 1.** For avoiding `H` and `x ≠ y`: `CN(x,y)` is intersecting, and if it has at least four members it
has exactly one common vertex (its centre). -/
theorem lemma1 {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) {x y : V} (hxy : x ≠ y) :
    (∀ P ∈ CN H {x, y}, ∀ Q ∈ CN H {x, y}, ¬ Disjoint P Q) ∧
      (4 ≤ (CN H {x, y}).card → ∃! w, ∀ P ∈ CN H {x, y}, w ∈ P) := by
  refine ⟨fun P hP Q hQ => CN_intersecting hH hav hxy hP hQ, fun h4 => ?_⟩
  obtain ⟨w, hw⟩ := CN_star hH hav hxy h4
  exact ⟨w, hw, fun w' hw' =>
    common_vertex_unique (fun _ hP => (mem_CN.mp hP).1) (by omega) hw' hw⟩

/-! ## Members through a vertex -/

/-- A pair `{p, r}` disjoint from `{x, y}` with `{p,r} ∪ {x}, {p,r} ∪ {y} ∈ H` lies in `CN(x,y)`. -/
theorem pair_mem_CN {H : Finset (Finset V)} {x y p r : V} (hpr : p ≠ r)
    (hpx : p ≠ x) (hpy : p ≠ y) (hrx : r ≠ x) (hry : r ≠ y)
    (hx : insert x ({p, r} : Finset V) ∈ H) (hy : insert y ({p, r} : Finset V) ∈ H) :
    ({p, r} : Finset V) ∈ CN H {x, y} :=
  mem_CN_pair.mpr ⟨mem_pairs.mpr (card_pair hpr), pair_inter_pair_eq_empty hpx hpy hrx hry, hx, hy⟩

/-- If every member of `CN(x,y)` passes through `w`, then the members are `{w, u}` with
`u ∈ L(xw) ∩ L(wy)`, so `s_{xy} ≤ |L(xw) ∩ L(wy)|`. -/
theorem card_CN_le_of_center {H : Finset (Finset V)} (hH : Uniform H) {x y w : V}
    (hxw : x ≠ w) (hyw : y ≠ w) (hw : ∀ P ∈ CN H {x, y}, w ∈ P) :
    (CN H {x, y}).card ≤ (link H {x, w} ∩ link H {w, y}).card := by
  have hsub : CN H {x, y} ⊆
      (link H {x, w} ∩ link H {w, y}).image (fun u => ({w, u} : Finset V)) := by
    intro P hP
    obtain ⟨hPp, -, hxP, hyP⟩ := mem_CN_pair.mp hP
    obtain ⟨u, -, rfl⟩ := exists_eq_pair_of_mem (mem_pairs.mp hPp) (hw P hP)
    rw [mem_image]
    refine ⟨u, ?_, rfl⟩
    rw [mem_inter, mem_link_iff_of_uniform hH (card_pair hxw),
      mem_link_iff_of_uniform hH (card_pair (Ne.symm hyw))]
    constructor
    · have e : ({u, x, w} : Finset V) = {x, w, u} := by
        ext t; simp only [mem_insert, mem_singleton]; tauto
      rw [e]; exact hxP
    · have e : ({u, w, y} : Finset V) = {y, w, u} := by
        ext t; simp only [mem_insert, mem_singleton]; tauto
      rw [e]; exact hyP
  exact (card_le_card hsub).trans card_image_le

/-! ## Lemma 2: the option bound -/

/-- For `T = {a,b,c} ∈ H` and `z ∈ L(bc)`, the pair `bc` lies in `CN(a,z)`; for `z ≠ a`, `{a,z}` is an option of `T`
through `bc`, so `s_{az} ≥ 1`. -/
theorem option_mem_CN {H : Finset (Finset V)} (hH : Uniform H) {a b c z : V}
    (hT : ({a, b, c} : Finset V) ∈ H) (hz : z ∈ link H {b, c}) :
    ({b, c} : Finset V) ∈ CN H {a, z} := by
  obtain ⟨hab, hac, hbc⟩ := triple_ne (hH _ hT)
  have hzbc : z ∉ ({b, c} : Finset V) := (mem_link.mp hz).1
  have hzb : z ≠ b := fun h => hzbc (by rw [h]; exact mem_insert_self b {c})
  have hzc : z ≠ c := fun h => hzbc (by rw [h]; exact mem_insert_of_mem (mem_singleton_self c))
  exact pair_mem_CN hbc (Ne.symm hab) (Ne.symm hzb) (Ne.symm hac) (Ne.symm hzc) hT
    (mem_link.mp hz).2

/-- **Lemma 2 (option bound), refined form.** For avoiding `H`, `T = {a,b,c} ∈ H` and `z ∈ L(bc) \ {a}`:
`s_{az} ≤ max(3, s^b_{az}, s^c_{az})` with `s^b_{az} = |L(ab) ∩ L(bz)|`, `s^c_{az} = |L(ac) ∩ L(cz)|`. -/
theorem option_bound_link {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) {a b c z : V}
    (hT : ({a, b, c} : Finset V) ∈ H) (hz : z ∈ link H {b, c}) (hza : z ≠ a) :
    (CN H {a, z}).card ≤
      max 3 (max (link H {a, b} ∩ link H {b, z}).card (link H {a, c} ∩ link H {c, z}).card) := by
  obtain ⟨hab, hac, -⟩ := triple_ne (hH _ hT)
  have hzbc : z ∉ ({b, c} : Finset V) := (mem_link.mp hz).1
  have hzb : z ≠ b := fun h => hzbc (by rw [h]; exact mem_insert_self b {c})
  have hzc : z ≠ c := fun h => hzbc (by rw [h]; exact mem_insert_of_mem (mem_singleton_self c))
  have hbcCN := option_mem_CN hH hT hz
  by_cases h4 : 4 ≤ (CN H {a, z}).card
  · obtain ⟨w, hw⟩ := CN_star hH hav (Ne.symm hza) h4
    have hwbc := hw _ hbcCN
    rw [mem_insert, mem_singleton] at hwbc
    rcases hwbc with rfl | rfl
    · have := card_CN_le_of_center hH hab hzb hw
      omega
    · have := card_CN_le_of_center hH hac hzc hw
      omega
  · omega

/-- **Lemma 2 (option bound).** For avoiding `H`, `T = {a,b,c} ∈ H` and `z ∈ L(bc) \ {a}`:
`s_{az} ≤ max(3, k_ab, k_ac)`. -/
theorem option_bound {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) {a b c z : V}
    (hT : ({a, b, c} : Finset V) ∈ H) (hz : z ∈ link H {b, c}) (hza : z ≠ a) :
    (CN H {a, z}).card ≤ max 3 (max (codeg H {a, b}) (codeg H {a, c})) := by
  obtain ⟨hab, hac, -⟩ := triple_ne (hH _ hT)
  have h := option_bound_link hH hav hT hz hza
  have h1 : (link H {a, b} ∩ link H {b, z}).card ≤ codeg H {a, b} := by
    rw [codeg_eq_card_link hH (card_pair hab)]; exact card_le_card inter_subset_left
  have h2 : (link H {a, c} ∩ link H {c, z}).card ≤ codeg H {a, c} := by
    rw [codeg_eq_card_link hH (card_pair hac)]; exact card_le_card inter_subset_left
  omega

/-! ## Lemma 3: the exchange lemma -/

/-- **Lemma 3 (exchange lemma).** For avoiding `H`, `T = {a,b,c} ∈ H`, `z ∈ L(ab) \ {c}` and
`u ∈ (L(ac) ∩ L(az)) \ {b}`: `u ∈ L(ca) \ {b}` (so `{b,u}` is an option of `T` through `ca`),
`s^c_{bu} ≤ 2`, `s_{bu} ≤ max(3, |L(ab) ∩ L(au)|)` and `s_{bu} ≤ max(3, k_ab)`. -/
theorem exchange {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) {a b c z u : V}
    (hT : ({a, b, c} : Finset V) ∈ H) (hz : z ∈ link H {a, b}) (hzc : z ≠ c)
    (hu : u ∈ link H {a, c} ∩ link H {a, z}) (hub : u ≠ b) :
    u ∈ (link H {a, c}).erase b ∧
      ((CN H {b, u}).filter (fun P => c ∈ P)).card ≤ 2 ∧
      (CN H {b, u}).card ≤ max 3 (link H {b, a} ∩ link H {a, u}).card ∧
      (CN H {b, u}).card ≤ max 3 (codeg H {a, b}) := by
  obtain ⟨hab, hac, hbc⟩ := triple_ne (hH _ hT)
  obtain ⟨hu1, hu2⟩ := mem_inter.mp hu
  have hzab : z ∉ ({a, b} : Finset V) := (mem_link.mp hz).1
  have hza : z ≠ a := fun h => hzab (by rw [h]; exact mem_insert_self a {b})
  have hzb : z ≠ b := fun h => hzab (by rw [h]; exact mem_insert_of_mem (mem_singleton_self b))
  have huac : u ∉ ({a, c} : Finset V) := (mem_link.mp hu1).1
  have hua : u ≠ a := fun h => huac (by rw [h]; exact mem_insert_self a {c})
  have huc : u ≠ c := fun h => huac (by rw [h]; exact mem_insert_of_mem (mem_singleton_self c))
  have huaz : u ∉ ({a, z} : Finset V) := (mem_link.mp hu2).1
  have huz : u ≠ z := fun h => huaz (by rw [h]; exact mem_insert_of_mem (mem_singleton_self z))
  have hacCN : ({a, c} : Finset V) ∈ CN H {b, u} := by
    refine pair_mem_CN hac hab (Ne.symm hua) (Ne.symm hbc) (Ne.symm huc) ?_ (mem_link.mp hu1).2
    have e : (insert b ({a, c} : Finset V)) = {a, b, c} := by
      ext t; simp only [mem_insert, mem_singleton]; tauto
    rw [e]; exact hT
  have hazCN : ({a, z} : Finset V) ∈ CN H {b, u} := by
    refine pair_mem_CN (Ne.symm hza) hab (Ne.symm hua) hzb (Ne.symm huz) ?_ (mem_link.mp hu2).2
    have e : (insert b ({a, z} : Finset V)) = insert z ({a, b} : Finset V) := by
      ext t; simp only [mem_insert, mem_singleton]; tauto
    rw [e]; exact (mem_link.mp hz).2
  have hbu : b ≠ u := Ne.symm hub
  have hstar : (CN H {b, u}).card ≤ max 3 (link H {b, a} ∩ link H {a, u}).card := by
    by_cases h4 : 4 ≤ (CN H {b, u}).card
    · obtain ⟨w, hw⟩ := CN_star hH hav hbu h4
      have hw1 := hw _ hacCN
      have hw2 := hw _ hazCN
      have hwa : w = a := by
        rw [mem_insert, mem_singleton] at hw1 hw2
        rcases hw1 with h | h
        · exact h
        · rcases hw2 with h' | h'
          · exact h'
          · exact absurd (h.symm.trans h') (Ne.symm hzc)
      rw [hwa] at hw
      have := card_CN_le_of_center hH (Ne.symm hab) hua hw
      omega
    · omega
  refine ⟨mem_erase.mpr ⟨hub, hu1⟩, ?_, hstar, ?_⟩
  · have hsub : (CN H {b, u}).filter (fun P => c ∈ P) ⊆ {{c, a}, {c, z}} := by
      intro P hP
      rw [mem_filter] at hP
      obtain ⟨hPCN, hcP⟩ := hP
      obtain ⟨t, -, rfl⟩ := exists_eq_pair_of_mem (mem_CN.mp hPCN).1 hcP
      have hmeet := mem_or_mem_of_not_disjoint (CN_intersecting hH hav hbu hazCN hPCN)
      rw [mem_insert, mem_singleton]
      rcases hmeet with h | h
      · rw [mem_insert, mem_singleton] at h
        rcases h with h | h
        · exact absurd h hac
        · left; rw [h]
      · rw [mem_insert, mem_singleton] at h
        rcases h with h | h
        · exact absurd h hzc
        · right; rw [h]
    exact (card_le_card hsub).trans card_le_two
  · have h1 : (link H {b, a} ∩ link H {a, u}).card ≤ codeg H {a, b} := by
      rw [pair_comm a b, codeg_eq_card_link hH (card_pair (Ne.symm hab))]
      exact card_le_card inter_subset_left
    omega

/-- **Lemma 3, mirror form.** For avoiding `H`, `T = {a,b,c} ∈ H`, `z ∈ L(ab) \ {c}` and
`v ∈ (L(bc) ∩ L(bz)) \ {a}`: `{a,v}` is an option of `T` through `bc`, `s^c_{av} ≤ 2`,
`s_{av} ≤ max(3, |L(ab) ∩ L(bv)|)` and `s_{av} ≤ max(3, k_ab)`. -/
theorem exchange_mirror {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) {a b c z v : V}
    (hT : ({a, b, c} : Finset V) ∈ H) (hz : z ∈ link H {a, b}) (hzc : z ≠ c)
    (hv : v ∈ link H {b, c} ∩ link H {b, z}) (hva : v ≠ a) :
    v ∈ (link H {b, c}).erase a ∧
      ((CN H {a, v}).filter (fun P => c ∈ P)).card ≤ 2 ∧
      (CN H {a, v}).card ≤ max 3 (link H {a, b} ∩ link H {b, v}).card ∧
      (CN H {a, v}).card ≤ max 3 (codeg H {a, b}) := by
  have hT' : ({b, a, c} : Finset V) ∈ H := by rw [insert_comm]; exact hT
  have hz' : z ∈ link H {b, a} := by rw [pair_comm]; exact hz
  have h := exchange hH hav hT' hz' hzc hv hva
  rw [pair_comm b a] at h
  exact h

end Weighting
end Erdos643R3

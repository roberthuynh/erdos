import Openmath.Proofs.PaperSupport.B5Resource

/- 
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.B5
open QB4
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace R2Input
variable {q : ℕ} {U W : Finset V}

lemma capU_int (hq : 5 ≤ q) (h : R2Input q G U W) {a : V} (ha : a ∈ U) :
    (dg G W a : ℤ) ≤ 2 * (q : ℤ) - 2 := by
  have hd := h.capU a ha
  omega

lemma capW_int (hq : 5 ≤ q) (h : R2Input q G U W) {w : V} (hw : w ∈ W) :
    (dg G U w : ℤ) ≤ 2 * (q : ℤ) - 2 := by
  have hd := h.capW w hw
  omega

/-- One deficient original row, derived from the integral original sum. -/
lemma unique_deficient (hq : 5 ≤ q) (h : R2Input q G U W) :
    ∃ a ∈ U, dg G W a = 2 * q - 3 ∧
      ∀ b ∈ U, b ≠ a → dg G W b = 2 * q - 2 := by
  let f : V → ℤ := fun a => 2 * (q : ℤ) - 2 - dg G W a
  have hn : ∀ a ∈ U, 0 ≤ f a := fun a ha => sub_nonneg.mpr (h.capU_int hq ha)
  have hs : ∑ a ∈ U, f a = 1 := h.deficient
  have hex : ∃ a ∈ U, 0 < f a := by
    by_contra! hall
    have hle : (∑ a ∈ U, f a) ≤ 0 := by
      calc _ ≤ ∑ _a ∈ U, (0 : ℤ) := sum_le_sum hall
        _ = 0 := by simp
    omega
  obtain ⟨a, ha, hap⟩ := hex
  have hle : f a ≤ ∑ b ∈ U, f b := by
    have ht := sum_le_sum_of_subset_of_nonneg (singleton_subset_iff.mpr ha)
      (fun b hb _ => hn b hb)
    simpa only [sum_singleton] using ht
  have ha1 : f a = 1 := by omega
  have he : ∑ b ∈ U.erase a, f b = 0 := by
    have hr := sum_erase_add U f ha
    omega
  have hz : ∀ b ∈ U.erase a, f b = 0 :=
    (sum_eq_zero_iff_of_nonneg (fun b hb => hn b (mem_of_mem_erase hb))).mp he
  refine ⟨a, ha, ?_, fun b hb hba => ?_⟩
  · dsimp [f] at ha1
    omega
  · have hb0 := hz b (mem_erase.mpr ⟨hba, hb⟩)
    dsimp [f] at hb0
    omega

lemma strong_minU (hq : 5 ≤ q) (h : R2Input q G U W) {a : V} (ha : a ∈ U) :
    2 * q - 3 ≤ dg G W a := by
  obtain ⟨p, hp, hpd, hother⟩ := h.unique_deficient hq
  by_cases hap : a = p
  · simpa [hap, hpd]
  · have hd := hother a ha hap
    omega

lemma theta_full (hq : 5 ≤ q) (h : R2Input q G U W) : theta q G U W W = 0 := by
  simp only [theta, row, sub_self, zero_add, max_eq_right (Nat.cast_nonneg q),
    sum_const, nsmul_eq_mul]
  rw [h.card]
  push_cast
  ring

lemma theta_small_nonempty (hq : 5 ≤ q) (h : R2Input q G U W) {T : Finset V}
    (hne : T.Nonempty) (hsize : #T ≤ 2) : theta q G U W T ≤ 0 := by
  have hs : ∑ a ∈ U, max 0 (row q G W T a) = 0 := by
    refine sum_eq_zero fun a ha => ?_
    have hd := dg_le_card (G := G) T a
    have hm := h.strong_minU hq ha
    have hr : row q G W T a ≤ 0 := by unfold row; omega
    exact max_eq_left hr
  have ht : 1 ≤ #T := card_pos.mpr hne
  have hp : 0 ≤ (q : ℤ) * ((#T : ℤ) - 1) :=
    mul_nonneg (Nat.cast_nonneg q) (by omega)
  unfold theta
  rw [hs]
  nlinarith

lemma edge_cap_T (hq : 5 ≤ q) (h : R2Input q G U W)
    {X T : Finset V} (hX : X ⊆ U) (hT : T ⊆ W) :
    (ec G X T : ℤ) ≤ (2 * (q : ℤ) - 2) * #T := by
  rw [ec_comm, ec, Nat.cast_sum]
  calc
    _ ≤ ∑ _w ∈ T, (2 * (q : ℤ) - 2) := by
      refine sum_le_sum fun w hw => ?_
      have hd := dg_mono (G := G) hX w
      have hc := h.capW_int hq (hT hw)
      omega
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

/-- Every original positive test, including proper and small-support guards. -/
lemma positive_shape (hq : 5 ≤ q) (h : R2Input q G U W) {T : Finset V}
    (hT : T ⊆ W) (hne : T.Nonempty) (hp : 0 < theta q G U W T) :
    3 ≤ #T ∧ #T < #W ∧ theta q G U W T = 1 ∧
      #(canonical q G U W T) = #T + 1 ∧
      deficiency (2 * (q : ℤ) - 2) G W (canonical q G U W T) = 1 ∧
      potential (2 * (q : ℤ) - 2) G (canonical q G U W T) T = 2 * (q : ℤ) + 2 := by
  have h3 : 3 ≤ #T := by
    by_contra! hsmall
    have hh := h.theta_small_nonempty hq hne (by omega)
    omega
  have htw : T ≠ W := fun heq => by subst T; have hf := h.theta_full hq; omega
  have hlt : #T < #W := card_lt_card ⟨hT, fun hback => htw (Subset.antisymm hT hback)⟩
  let C := canonical q G U W T
  let k : ℤ := (#C : ℤ) - #T
  let a : ℤ := deficiency (2 * (q : ℤ) - 2) G W C
  have hCU : C ⊆ U := canonical_subset q U W T
  have hsp := h.sparse C hCU T hT (by omega) (by have hc := card_le_card hCU; omega)
  have han : 0 ≤ a := deficiency_nonneg _ (fun b hb => h.capU_int hq (hCU hb))
  have hal : a ≤ 1 := by
    have hd := deficiency_le_subset (G := G) (2 * (q : ℤ) - 2) hCU
      (fun b hb => h.capU_int hq hb)
    simpa [a, h.deficient] using hd
  have hi := mixed_potential (G := G) q W C T
  rw [mixed_canonical] at hi
  have hik : 2 * theta q G U W T = 2 * (q : ℤ) + 2 * k + 2 * a -
      potential (2 * (q : ℤ) - 2) G C T := hi
  have hk1 : 1 ≤ k := by omega
  have he := h.edge_cap_T hq hCU hT
  have hg : (2 * (q : ℤ) - 2) * k ≤ potential (2 * (q : ℤ) - 2) G C T := by
    dsimp [k]
    unfold potential
    nlinarith
  have hk2 : k < 2 := by
    by_contra! hbad
    have hprod : 0 ≤ ((q : ℤ) - 2) * (k - 2) :=
      mul_nonneg (by omega) (by omega)
    nlinarith
  have hk : k = 1 := by omega
  have ha : a = 1 := by omega
  have ht : theta q G U W T = 1 := by omega
  have hc : #C = #T + 1 := by dsimp [k] at hk; omega
  have hgp : potential (2 * (q : ℤ) - 2) G C T = 2 * (q : ℤ) + 2 := by omega
  exact ⟨h3, hlt, ht, hc, ha, hgp⟩

lemma theta_nonempty_le_one (hq : 5 ≤ q) (h : R2Input q G U W) {T : Finset V}
    (hT : T ⊆ W) (hne : T.Nonempty) : theta q G U W T ≤ 1 := by
  by_cases hp : 0 < theta q G U W T
  · exact (h.positive_shape hq hT hne hp).2.2.1.le
  · omega

end R2Input
#print axioms R2Input.unique_deficient
#print axioms R2Input.positive_shape
end Erdos585.B5

import Openmath.Erdos643R3.L1Top
import Openmath.Erdos643R3.RedistArith
import Openmath.Erdos643R3.Pw2312

/-!
# Rule 2' recipient and apex accounting

These are unconditional finite-sum consequences of the existing `L1Top` definitions.
The final recipient theorem still requires (1) existence of a triangular witness
for a deficient triple and (2) the per-active-bicone pot bound. Neither input is
asserted here to follow from avoidance. The anchor theorem states its per-apex
share hypothesis explicitly; disjointness of anchors and the exact partition of
all deficient witnesses by apex are proved, rather than supplied as hypotheses.
-/

set_option autoImplicit false

namespace Erdos643R3.Redistribution

open Finset hiding shadow
open Erdos643R3.Identity Erdos643R3.L1Top

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A member of an active bicone is counted by `act`. -/
theorem act_pos {H : Finset (Finset V)} {q T : Finset V}
    (hq : q ∈ activePairs H) (hT : T ∈ bicone H q) : 0 < act H T := by
  exact Finset.card_pos.mpr ⟨q, mem_filter.mpr ⟨hq, hT⟩⟩

theorem pot_nonneg (H : Finset (Finset V)) (q : Finset V) : 0 ≤ pot H q := by
  apply sum_nonneg
  intro T hT
  have hd := (mem_filter.mp hT).2
  exact div_nonneg (le_of_lt hd.1) (Nat.cast_nonneg _)

theorem received_nonneg (H : Finset (Finset V)) (T : Finset V) : 0 ≤ received H T := by
  apply sum_nonneg
  intro q hq
  obtain ⟨hqa, hTd⟩ := mem_filter.mp hq
  exact div_nonneg (mul_nonneg (pot_nonneg H q) (le_of_lt (deficit_pos_of_mem_defSet hTd)))
    (le_of_lt (totalDeficit_pos hqa))

theorem active_of_triangular_witness {H : Finset (Finset V)} {q T : Finset V}
    (hq : Triangular H q) (hT : T ∈ bicone H q) (hd : Deficient H T) :
    q ∈ activePairs H := by
  exact mem_activePairs.mpr ⟨mem_pairs.mpr hq.1, hq, T, hT, hd⟩

/-- One adequately funded bicone suffices for a deficient witness. All its other
receipts are nonnegative, so uniqueness of the triangle option is unnecessary here. -/
theorem final_nonneg_of_funded_witness {H : Finset (Finset V)} {q T : Finset V}
    (hq : q ∈ activePairs H) (hT : T ∈ defSet H q)
    (hfund : totalDeficit H q ≤ pot H q) : 0 ≤ final H T := by
  have htotal := totalDeficit_pos hq
  have hd := deficit_pos_of_mem_defSet hT
  have hshare : deficit H T ≤ pot H q * deficit H T / totalDeficit H q := by
    apply (le_div_iff₀ htotal).mpr
    nlinarith
  have hterm : pot H q * deficit H T / totalDeficit H q ≤ received H T := by
    unfold received
    apply single_le_sum (f := fun r => pot H r * deficit H T / totalDeficit H r) (a := q)
    · intro r hr
      obtain ⟨hra, hTr⟩ := mem_filter.mp hr
      exact div_nonneg (mul_nonneg (pot_nonneg H r) (le_of_lt (deficit_pos_of_mem_defSet hTr)))
        (le_of_lt (totalDeficit_pos hra))
    · exact mem_filter.mpr ⟨hq, hT⟩
  have hnot : ¬ Donor H T := by
    intro hdon
    have hc : charge H T < 0 := (mem_defSet.mp hT).2
    linarith [hdon.1]
  unfold final
  rw [if_neg hnot]
  have hr := le_trans hshare hterm
  unfold deficit at hr
  linarith

/-- The recipient condition required by `L1Top.conditional_endpoint`, from an
explicit triangle-existence input and the exact per-bicone funding inequality. -/
theorem hrec_of_funded_bicones (H : Finset (Finset V))
    (hex : ∀ T ∈ H, Deficient H T → ∃ q, Triangular H q ∧ T ∈ bicone H q)
    (hfund : ∀ q ∈ activePairs H, totalDeficit H q ≤ pot H q) :
    ∀ T ∈ H, Deficient H T → 0 ≤ final H T := by
  intro T hT hd
  obtain ⟨q, hqt, hTb⟩ := hex T hT hd
  have hqa := active_of_triangular_witness hqt hTb hd
  exact final_nonneg_of_funded_witness hqa (mem_defSet.mpr ⟨hTb, hd⟩) (hfund q hqa)

/-- Deficient members of a bicone containing the specified apex. -/
noncomputable def apexDefSet (H : Finset (Finset V)) (q : Finset V) (x : V) : Finset (Finset V) :=
  (defSet H q).filter (fun T => x ∈ T)

/-- The exact sum of deficits on one apex. -/
noncomputable def apexDeficit (H : Finset (Finset V)) (q : Finset V) (x : V) : ℚ :=
  ∑ T ∈ apexDefSet H q x, deficit H T

theorem apexDeficit_nonneg (H : Finset (Finset V)) (q : Finset V) (x : V) :
    0 ≤ apexDeficit H q x := by
  apply sum_nonneg
  intro T hT
  exact le_of_lt (deficit_pos_of_mem_defSet (mem_filter.mp hT).1)

/-- Every witness contains exactly one apex. This uses the disjointness in `CN`,
not a separate structural assumption on the bicone. -/
theorem witness_apex_filter {H : Finset (Finset V)} {q T : Finset V}
    (hT : T ∈ bicone H q) : ∃ x ∈ q, q.filter (fun y => y ∈ T) = {x} := by
  obtain ⟨P, hP, x, hx, rfl⟩ := mem_bicone.mp hT
  refine ⟨x, hx, ?_⟩
  have hd : Disjoint P q := disjoint_iff_inter_eq_empty.mpr (mem_CN.mp hP).2.1
  ext y
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hyq, rfl | hyP⟩
    · rfl
    · exact False.elim ((disjoint_left.mp hd) hyP hyq)
  · rintro rfl
    exact ⟨hx, Or.inl rfl⟩

/-- The apex sums partition the full deficient pot exactly. -/
theorem sum_apexDeficit (H : Finset (Finset V)) (q : Finset V) :
    ∑ x ∈ q, apexDeficit H q x = totalDeficit H q := by
  unfold apexDeficit apexDefSet
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro T hT
  obtain ⟨x, hx, he⟩ := witness_apex_filter (mem_defSet.mp hT).1
  rw [← sum_filter, he, sum_singleton]

/-- Apexes supporting at least one deficient witness. -/
noncomputable def deficientApexes (H : Finset (Finset V)) (q : Finset V) : Finset V :=
  q.filter (fun x => 0 < apexDeficit H q x)

theorem sum_deficientApexes (H : Finset (Finset V)) (q : Finset V) :
    ∑ x ∈ deficientApexes H q, apexDeficit H q x = totalDeficit H q := by
  rw [← sum_apexDeficit H q]
  apply sum_subset (filter_subset _ _)
  intro x hx hnot
  have hn : ¬ 0 < apexDeficit H q x := by
    intro hp
    exact hnot (mem_filter.mpr ⟨hx, hp⟩)
  exact le_antisymm (not_lt.mp hn) (apexDeficit_nonneg H q x)

/-- The verified 23/12 bound controls every deficient witness by 1/12. -/
theorem deficit_le_twelfth {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) {T : Finset V} (hT : T ∈ H) :
    deficit H T ≤ (1/12 : ℚ) := by
  have ht := Pw2312Main.per_triple hH hav hT
  unfold deficit charge
  linarith

/-- A subset of three objects omitting at least one has at most two members. -/
theorem card_le_two_of_three {α : Type*} [DecidableEq α] {s : Finset α} {a b c : α}
    (hsub : s ⊆ {a,b,c}) (hnot : ¬ (a ∈ s ∧ b ∈ s ∧ c ∈ s)) : s.card ≤ 2 := by
  have hpair : ∀ d e : α, ({d,e} : Finset α).card ≤ 2 := by
    intro d e
    exact card_le_two
  by_cases ha : a ∈ s
  · by_cases hb : b ∈ s
    · have hc : c ∉ s := fun hc => hnot ⟨ha,hb,hc⟩
      apply (card_le_card (show s ⊆ {a,b} from ?_)).trans (hpair a b)
      intro z hz
      have h := hsub hz
      simp only [mem_insert, mem_singleton] at h ⊢
      rcases h with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact False.elim (hc hz)
    · apply (card_le_card (show s ⊆ {a,c} from ?_)).trans (hpair a c)
      intro z hz
      have h := hsub hz
      simp only [mem_insert, mem_singleton] at h ⊢
      rcases h with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact False.elim (hb hz)
      · exact Or.inr rfl
  · apply (card_le_card (show s ⊆ {b,c} from ?_)).trans (hpair b c)
    intro z hz
    have h := hsub hz
    simp only [mem_insert, mem_singleton] at h ⊢
    rcases h with rfl | rfl | rfl
    · exact False.elim (ha hz)
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- Lemma P applied to an actual set of deficient witnesses: the three apex
edges cannot all be exactly-one-light. -/
theorem apexDefSet_card_le_two {H : Finset (Finset V)} {q : Finset V} {x u v w : V}
    (hsub : apexDefSet H q x ⊆ {insert x {u,v}, insert x {v,w}, insert x {u,w}})
    (huv : insert x {u,v} ∈ apexDefSet H q x → RedistArith.ExactlyOneLight H x u v)
    (hvw : insert x {v,w} ∈ apexDefSet H q x → RedistArith.ExactlyOneLight H x v w)
    (huw : insert x {u,w} ∈ apexDefSet H q x → RedistArith.ExactlyOneLight H x u w) :
    (apexDefSet H q x).card ≤ 2 := by
  apply card_le_two_of_three hsub
  rintro ⟨h1,h2,h3⟩
  have h1' := huv h1
  have h2' := hvw h2
  have h3' := huw h3
  unfold RedistArith.ExactlyOneLight at h1' h2' h3'
  tauto

/-- On a labelled bicone, the deficient witnesses at `x` are among its three
base edges. The other apex cannot occur in a witness containing `x`. -/
theorem apexDefSet_subset_three {H : Finset (Finset V)} {x y u v w : V}
    (hxy : x ≠ y)
    (hCN : CN H {x,y} = ({{u,v},{v,w},{u,w}} : Finset (Finset V))) :
    apexDefSet H {x,y} x ⊆ {insert x {u,v}, insert x {v,w}, insert x {u,w}} := by
  intro T hT
  obtain ⟨hTd, hxT⟩ := mem_filter.mp hT
  obtain ⟨P, hP, z, hz, he⟩ := mem_bicone.mp (mem_defSet.mp hTd).1
  have hxP : x ∉ P := by
    intro hx
    have hd := disjoint_iff_inter_eq_empty.mpr (mem_CN.mp hP).2.1
    exact disjoint_left.mp hd hx (by simp)
  have hz' : z = x ∨ z = y := by simpa using hz
  rcases hz' with rfl | rfl
  · rw [hCN] at hP
    simp only [mem_insert, mem_singleton] at hP
    rcases hP with rfl | rfl | rfl <;> rw [← he] <;> simp
  · rw [← he, mem_insert] at hxT
    rcases hxT with hh | hh
    · exact False.elim (hxy hh)
    · exact False.elim (hxP hh)

/-- Two deficient witnesses cost at most one sixth in total. -/
theorem apexDeficit_le_sixth {H : Finset (Finset V)} (hH : Uniform H)
    (hav : ¬ Erdos643.HypergraphBasics.Forbidden H) {q : Finset V} {x : V}
    (hcard : (apexDefSet H q x).card ≤ 2) : apexDeficit H q x ≤ (1/6 : ℚ) := by
  have he : apexDeficit H q x ≤ ∑ T ∈ apexDefSet H q x, (1/12 : ℚ) := by
    apply sum_le_sum
    intro T hT
    exact deficit_le_twelfth hH hav (defSet_subset H q (mem_filter.mp hT).1)
  rw [sum_const, nsmul_eq_mul] at he
  have hcard' : ((apexDefSet H q x).card : ℚ) ≤ 2 := by exact_mod_cast hcard
  linarith

/-- The anchors supplied on different apexes are distinct because each witness
contains exactly one apex. -/
theorem anchors_injective {H : Finset (Finset V)} {q : Finset V} (A : V → Finset V)
    (hA : ∀ x ∈ deficientApexes H q, A x ∈ bicone H q ∧ x ∈ A x) :
    Set.InjOn A (deficientApexes H q) := by
  intro x hx y hy he
  obtain ⟨z, hzq, hz⟩ := witness_apex_filter (hA x hx).1
  have hxq := (mem_filter.mp hx).1
  have hyq := (mem_filter.mp hy).1
  have hxz : x = z := mem_singleton.mp (hz ▸ mem_filter.mpr ⟨hxq, (hA x hx).2⟩)
  have hyz : y = z := by
    apply mem_singleton.mp
    rw [← hz]
    exact mem_filter.mpr ⟨hyq, he ▸ (hA y hy).2⟩
  exact hxz.trans hyz.symm

/-- Exact active-bicone accounting. A chosen anchor on each deficient apex must
cover that apex's actual deficit with its actual Rule 2' share. The anchors are
proved distinct, are proved donors, and every other donor contributes nonnegatively. -/
theorem pot_ge_totalDeficit_of_apex_shares {H : Finset (Finset V)} {q : Finset V}
    (hq : q ∈ activePairs H) (A : V → Finset V)
    (hA : ∀ x ∈ deficientApexes H q, A x ∈ bicone H q ∧ x ∈ A x)
    (hshare : ∀ x ∈ deficientApexes H q,
      apexDeficit H q x ≤ charge H (A x) / (act H (A x) : ℚ)) :
    totalDeficit H q ≤ pot H q := by
  have hdon : ∀ x ∈ deficientApexes H q, Donor H (A x) := by
    intro x hx
    have hp := (mem_filter.mp hx).2
    have ha := act_pos hq (hA x hx).1
    have har : (0 : ℚ) < (act H (A x) : ℚ) := by exact_mod_cast ha
    have hs : 0 < charge H (A x) / (act H (A x) : ℚ) := lt_of_lt_of_le hp (hshare x hx)
    refine ⟨?_, ha⟩
    rcases (div_pos_iff).mp hs with ⟨hc, _⟩ | ⟨_, hn⟩
    · exact hc
    · linarith
  calc
    totalDeficit H q = ∑ x ∈ deficientApexes H q, apexDeficit H q x :=
      (sum_deficientApexes H q).symm
    _ ≤ ∑ x ∈ deficientApexes H q, charge H (A x) / (act H (A x) : ℚ) :=
      sum_le_sum hshare
    _ = ∑ T ∈ (deficientApexes H q).image A, charge H T / (act H T : ℚ) :=
      (sum_image (f := fun T => charge H T / (act H T : ℚ)) (anchors_injective A hA)).symm
    _ ≤ pot H q := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro T hT
        obtain ⟨x, hx, rfl⟩ := mem_image.mp hT
        exact mem_filter.mpr ⟨(hA x hx).1, hdon x hx⟩
      · intro T hT _
        exact div_nonneg (le_of_lt (mem_filter.mp hT).2.1) (Nat.cast_nonneg _)

/-- The complete algebraic assembly, with both mathematical inputs visible:
existence of a triangular witness and a covering anchor on each deficient apex.
It does not assert that those inputs follow from avoidance. -/
theorem endpoint_of_apex_shares (H : Finset (Finset V)) (hH : Uniform H)
    (hex : ∀ T ∈ H, Deficient H T → ∃ q, Triangular H q ∧ T ∈ bicone H q)
    (hanchors : ∀ q ∈ activePairs H, ∃ A : V → Finset V,
      (∀ x ∈ deficientApexes H q, A x ∈ bicone H q ∧ x ∈ A x) ∧
      (∀ x ∈ deficientApexes H q,
        apexDeficit H q x ≤ charge H (A x) / (act H (A x) : ℚ))) :
    Phi H ≤ 0 ∧ (H.card : ℚ) ≤ (((Fintype.card V).choose 2 : ℕ) : ℚ) := by
  apply conditional_endpoint H hH
  apply hrec_of_funded_bicones H hex
  intro q hq
  obtain ⟨A, hA, hshare⟩ := hanchors q hq
  exact pot_ge_totalDeficit_of_apex_shares hq A hA hshare

end Erdos643R3.Redistribution

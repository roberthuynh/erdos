import Mathlib
import Openmath.Erdos643R3.Weighting



set_option autoImplicit false

namespace Erdos643R3
namespace L1Top

open Finset hiding shadow
open Erdos643R3.Identity Erdos643R3.Weighting

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## (i) The endpoint -/

omit [DecidableEq V] in
/-- The number of pairs of `V` is `C(|V|, 2)`. -/
theorem card_pairs_eq : (pairs V).card = (Fintype.card V).choose 2 := by
  rw [pairs, card_powersetCard, card_univ]

/-- `|∂H| ≤ C(|V|, 2)`: the shadow is a set of pairs of `V`. -/
theorem card_shadow_le (H : Finset (Finset V)) : (shadow H).card ≤ (Fintype.card V).choose 2 := by
  rw [← card_pairs_eq]
  exact card_le_card (shadow_subset_pairs H)

/-- `|CL(H)| ≤ C(|V|, 2)`: the co-link pairs are pairs of `V`. -/
theorem card_colink_le (H : Finset (Finset V)) : (colink H).card ≤ (Fintype.card V).choose 2 := by
  rw [← card_pairs_eq]
  exact card_le_card (filter_subset _ _)

/-- `Φ(H) = 2|H| − |∂H| − |CL(H)|`, over `ℚ`. -/
def Phi (H : Finset (Finset V)) : ℚ :=
  2 * (H.card : ℚ) - ((shadow H).card : ℚ) - ((colink H).card : ℚ)

/-- **Endpoint.** If `2|H| ≤ |∂H| + |CL(H)|` then `|H| ≤ C(|V|, 2)` (no hypothesis on `H`). -/
theorem endpoint (H : Finset (Finset V))
    (h : 2 * (H.card : ℚ) ≤ ((shadow H).card : ℚ) + ((colink H).card : ℚ)) :
    (H.card : ℚ) ≤ (((Fintype.card V).choose 2 : ℕ) : ℚ) := by
  have h1 : ((shadow H).card : ℚ) ≤ (((Fintype.card V).choose 2 : ℕ) : ℚ) := by
    exact_mod_cast card_shadow_le H
  have h2 : ((colink H).card : ℚ) ≤ (((Fintype.card V).choose 2 : ℕ) : ℚ) := by
    exact_mod_cast card_colink_le H
  linarith

/-- **Endpoint**, natural-number form. -/
theorem endpoint_nat (H : Finset (Finset V))
    (h : 2 * H.card ≤ (shadow H).card + (colink H).card) :
    H.card ≤ (Fintype.card V).choose 2 := by
  have h1 := card_shadow_le H
  have h2 := card_colink_le H
  omega

/-- **Endpoint**, `Φ` form: `Φ(H) ≤ 0` implies `|H| ≤ C(|V|, 2)`. -/
theorem endpoint_of_Phi_nonpos (H : Finset (Finset V)) (h : Phi H ≤ 0) :
    (H.card : ℚ) ≤ (((Fintype.card V).choose 2 : ℕ) : ℚ) := by
  apply endpoint H
  unfold Phi at h
  linarith

/-! ## (ii) The charge identity -/

/-- The charge `c(T) = σ(T) + τ(T) − 2`. -/
def charge (H : Finset (Finset V)) (T : Finset V) : ℚ := sigmaW H T + tauW H T - 2

/-- **Charge identity.** For every uniform `H` (no avoidance hypothesis):
`Σ_{T ∈ H} (σ(T) + τ(T) − 2) = |∂H| + |CL(H)| − 2|H|`. -/
theorem sum_charge (H : Finset (Finset V)) (hH : Uniform H) :
    ∑ T ∈ H, charge H T = ((shadow H).card : ℚ) + ((colink H).card : ℚ) - 2 * (H.card : ℚ) := by
  obtain ⟨h1, h2⟩ := lemma4 H hH
  unfold charge
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, h1, h2, Finset.sum_const, nsmul_eq_mul]
  ring

/-- The charge identity in the form `Σ_{T ∈ H} c(T) = −Φ(H)`. -/
theorem sum_charge_eq_neg_Phi (H : Finset (Finset V)) (hH : Uniform H) :
    ∑ T ∈ H, charge H T = - Phi H := by
  rw [sum_charge H hH]
  unfold Phi
  ring

/-! ## (iii) Triangular common links, bicones, deficient triples, Rule 2' -/

/-- `CN(q)` is *triangular*: `q` is a pair and `CN(q) = {uv, vw, uw}` for three distinct vertices `u, v, w`. -/
def Triangular (H : Finset (Finset V)) (q : Finset V) : Prop :=
  q.card = 2 ∧ ∃ u v w : V, u ≠ v ∧ v ≠ w ∧ u ≠ w ∧
    CN H q = ({{u, v}, {v, w}, {u, w}} : Finset (Finset V))

/-- The witness set of `q`: the triples `P ∪ {x}` with `P ∈ CN(q)` and `x ∈ q`. For triangular `q` this is the
bicone `B_q` (`bicone_of_CN_eq`). -/
def bicone (H : Finset (Finset V)) (q : Finset V) : Finset (Finset V) :=
  (CN H q).biUnion (fun P => q.image (fun x => insert x P))

theorem mem_bicone {H : Finset (Finset V)} {q T : Finset V} :
    T ∈ bicone H q ↔ ∃ P ∈ CN H q, ∃ x ∈ q, insert x P = T := by
  simp only [bicone, mem_biUnion, mem_image]

/-- Every witness triple is a triple of `H`. -/
theorem bicone_subset (H : Finset (Finset V)) (q : Finset V) : bicone H q ⊆ H := by
  intro T hT
  obtain ⟨P, hP, x, hx, rfl⟩ := mem_bicone.mp hT
  exact (mem_CN.mp hP).2.2 x hx

/-- For `CN(x,y) = {uv, vw, uw}` the bicone is the set of the six triples
`x+uv, x+vw, x+uw, y+uv, y+vw, y+uw` (redist §1). -/
theorem bicone_of_CN_eq {H : Finset (Finset V)} {x y u v w : V}
    (hCN : CN H {x, y} = ({{u, v}, {v, w}, {u, w}} : Finset (Finset V))) :
    bicone H {x, y} = ({insert x {u, v}, insert x {v, w}, insert x {u, w},
      insert y {u, v}, insert y {v, w}, insert y {u, w}} : Finset (Finset V)) := by
  ext T
  rw [mem_bicone, hCN]
  simp only [mem_insert, mem_singleton]
  constructor
  · rintro ⟨P, hP, z, hz, rfl⟩
    rcases hP with rfl | rfl | rfl <;> rcases hz with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨{u, v}, Or.inl rfl, x, Or.inl rfl, rfl⟩
    · exact ⟨{v, w}, Or.inr (Or.inl rfl), x, Or.inl rfl, rfl⟩
    · exact ⟨{u, w}, Or.inr (Or.inr rfl), x, Or.inl rfl, rfl⟩
    · exact ⟨{u, v}, Or.inl rfl, y, Or.inr rfl, rfl⟩
    · exact ⟨{v, w}, Or.inr (Or.inl rfl), y, Or.inr rfl, rfl⟩
    · exact ⟨{u, w}, Or.inr (Or.inr rfl), y, Or.inr rfl, rfl⟩

/-- `T` is *deficient*: `c(T) < 0`. -/
def Deficient (H : Finset (Finset V)) (T : Finset V) : Prop := charge H T < 0

/-- The deficit `def(T) = −c(T)`. -/
def deficit (H : Finset (Finset V)) (T : Finset V) : ℚ := - charge H T

/-- The bicone `B_q` is *active*: `q` is triangular and `B_q` contains a deficient triple. -/
def Active (H : Finset (Finset V)) (q : Finset V) : Prop :=
  Triangular H q ∧ ∃ T ∈ bicone H q, Deficient H T

noncomputable instance instDecidableTriangular (H : Finset (Finset V)) (q : Finset V) :
    Decidable (Triangular H q) := Classical.dec _

noncomputable instance instDecidableDeficient (H : Finset (Finset V)) (T : Finset V) :
    Decidable (Deficient H T) := Classical.dec _

noncomputable instance instDecidableActive (H : Finset (Finset V)) (q : Finset V) :
    Decidable (Active H q) := Classical.dec _

/-- The pairs `q` whose bicone is active. -/
noncomputable def activePairs (H : Finset (Finset V)) : Finset (Finset V) :=
  (pairs V).filter (fun q => Active H q)

/-- `D_q`: the deficient members of `B_q`. -/
noncomputable def defSet (H : Finset (Finset V)) (q : Finset V) : Finset (Finset V) :=
  (bicone H q).filter (fun T => Deficient H T)

/-- `act(T)`: the number of active bicones containing `T`. -/
noncomputable def act (H : Finset (Finset V)) (T : Finset V) : ℕ :=
  ((activePairs H).filter (fun q => T ∈ bicone H q)).card

/-- A Rule 2' donor: `c(T) > 0` and `act(T) ≥ 1`. -/
def Donor (H : Finset (Finset V)) (T : Finset V) : Prop := 0 < charge H T ∧ 0 < act H T

noncomputable instance instDecidableDonor (H : Finset (Finset V)) (T : Finset V) :
    Decidable (Donor H T) := Classical.dec _

/-- The pot of `B_q`: every donor `T ∈ B_q` sends `c(T)/act(T)`. -/
noncomputable def pot (H : Finset (Finset V)) (q : Finset V) : ℚ :=
  ∑ T ∈ (bicone H q).filter (fun T => Donor H T), charge H T / (act H T : ℚ)

/-- `Σ_{S ∈ D_q} def(S)`. -/
noncomputable def totalDeficit (H : Finset (Finset V)) (q : Finset V) : ℚ :=
  ∑ S ∈ defSet H q, deficit H S

/-- Rule 2' receipt of `T`: over the active `q` with `T ∈ D_q`, the share `pot(q) · def(T) / Σ_{S ∈ D_q} def(S)`. -/
noncomputable def received (H : Finset (Finset V)) (T : Finset V) : ℚ :=
  ∑ q ∈ (activePairs H).filter (fun q => T ∈ defSet H q),
    pot H q * deficit H T / totalDeficit H q

/-- The charge of `T` after Rule 2': donors give away all their charge, every triple adds what it receives. -/
noncomputable def final (H : Finset (Finset V)) (T : Finset V) : ℚ :=
  (if Donor H T then 0 else charge H T) + received H T

/-! ### Basic facts -/

theorem mem_activePairs {H : Finset (Finset V)} {q : Finset V} :
    q ∈ activePairs H ↔ q ∈ pairs V ∧ Active H q := by
  rw [activePairs, mem_filter]

theorem mem_defSet {H : Finset (Finset V)} {q T : Finset V} :
    T ∈ defSet H q ↔ T ∈ bicone H q ∧ Deficient H T := by
  rw [defSet, mem_filter]

theorem defSet_subset (H : Finset (Finset V)) (q : Finset V) : defSet H q ⊆ H :=
  fun _ hT => bicone_subset H q (mem_defSet.mp hT).1

theorem deficit_pos_of_mem_defSet {H : Finset (Finset V)} {q T : Finset V} (hT : T ∈ defSet H q) :
    0 < deficit H T := by
  have h : charge H T < 0 := (mem_defSet.mp hT).2
  unfold deficit
  linarith

/-- An active bicone has positive total deficit. -/
theorem totalDeficit_pos {H : Finset (Finset V)} {q : Finset V} (hq : q ∈ activePairs H) :
    0 < totalDeficit H q := by
  obtain ⟨-, -, T, hTb, hTd⟩ := mem_activePairs.mp hq
  have hT : T ∈ defSet H q := mem_defSet.mpr ⟨hTb, hTd⟩
  exact Finset.sum_pos (fun S hS => deficit_pos_of_mem_defSet hS) ⟨T, hT⟩

/-- **Proportional split.** The pot of an active bicone is fully distributed among `D_q`. -/
theorem rule2p_split (H : Finset (Finset V)) {q : Finset V} (hq : q ∈ activePairs H) :
    ∑ T ∈ defSet H q, pot H q * deficit H T / totalDeficit H q = pot H q := by
  have htd : totalDeficit H q ≠ 0 := ne_of_gt (totalDeficit_pos hq)
  have e : ∀ T ∈ defSet H q, pot H q * deficit H T / totalDeficit H q =
      (pot H q / totalDeficit H q) * deficit H T := by
    intro T _
    ring
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
  change pot H q / totalDeficit H q * totalDeficit H q = pot H q
  exact div_mul_cancel₀ (pot H q) htd

/-- Total receipts equal the total of the active pots. -/
theorem sum_received (H : Finset (Finset V)) :
    ∑ T ∈ H, received H T = ∑ q ∈ activePairs H, pot H q := by
  have hc : ∀ (T q : Finset V), T ∈ H ∧ q ∈ (activePairs H).filter (fun q => T ∈ defSet H q) ↔
      T ∈ defSet H q ∧ q ∈ activePairs H := by
    intro T q
    rw [mem_filter]
    constructor
    · rintro ⟨-, hq, hT⟩
      exact ⟨hT, hq⟩
    · rintro ⟨hT, hq⟩
      exact ⟨defSet_subset H q hT, hq, hT⟩
  unfold received
  rw [Finset.sum_comm' hc]
  exact Finset.sum_congr rfl (fun q hq => rule2p_split H hq)

/-- The total of the active pots equals the total charge of the donors (each donor sends `c(T)/act(T)` to each of
its `act(T)` active bicones). -/
theorem sum_pot (H : Finset (Finset V)) :
    ∑ q ∈ activePairs H, pot H q = ∑ T ∈ H.filter (fun T => Donor H T), charge H T := by
  have hc : ∀ (q T : Finset V), q ∈ activePairs H ∧ T ∈ (bicone H q).filter (fun T => Donor H T) ↔
      q ∈ (activePairs H).filter (fun q => T ∈ bicone H q) ∧ T ∈ H.filter (fun T => Donor H T) := by
    intro q T
    rw [mem_filter, mem_filter, mem_filter]
    constructor
    · rintro ⟨hq, hT, hd⟩
      exact ⟨⟨hq, hT⟩, bicone_subset H q hT, hd⟩
    · rintro ⟨⟨hq, hT⟩, -, hd⟩
      exact ⟨hq, hT, hd⟩
  unfold pot
  rw [Finset.sum_comm' hc]
  refine Finset.sum_congr rfl (fun T hT => ?_)
  have hd : Donor H T := (mem_filter.mp hT).2
  have hpos : (0 : ℚ) < (act H T : ℚ) := by exact_mod_cast hd.2
  rw [Finset.sum_const, nsmul_eq_mul]
  change (act H T : ℚ) * (charge H T / (act H T : ℚ)) = charge H T
  exact mul_div_cancel₀ (charge H T) (ne_of_gt hpos)

/-- What the donors keep: `Σ_{T ∈ H} (0 if donor else c(T)) = Σ_{T ∈ H} c(T) − Σ_{donors} c(T)`. -/
theorem sum_kept (H : Finset (Finset V)) :
    ∑ T ∈ H, (if Donor H T then 0 else charge H T) =
      ∑ T ∈ H, charge H T - ∑ T ∈ H.filter (fun T => Donor H T), charge H T := by
  have e : ∀ T ∈ H, (if Donor H T then 0 else charge H T) =
      charge H T - (if Donor H T then charge H T else 0) := by
    intro T _
    split_ifs <;> ring
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_filter]

/-- **Conservation (Rule 2' moves charge without creating it).** For every `H`:
`Σ_{T ∈ H} final(T) = Σ_{T ∈ H} c(T)`. -/
theorem sum_final (H : Finset (Finset V)) :
    ∑ T ∈ H, final H T = ∑ T ∈ H, charge H T := by
  unfold final
  rw [Finset.sum_add_distrib, sum_kept, sum_received, sum_pot]
  ring

/-- Conservation with the charge identity: for uniform `H`, `Σ_{T ∈ H} final(T) = |∂H| + |CL(H)| − 2|H| = −Φ(H)`. -/
theorem sum_final_eq_neg_Phi (H : Finset (Finset V)) (hH : Uniform H) :
    ∑ T ∈ H, final H T = - Phi H := by
  rw [sum_final, sum_charge_eq_neg_Phi H hH]

/-- A triple that is not deficient receives nothing. -/
theorem received_eq_zero {H : Finset (Finset V)} {T : Finset V} (hT : 0 ≤ charge H T) :
    received H T = 0 := by
  unfold received
  apply Finset.sum_eq_zero
  intro q hq
  have hd : charge H T < 0 := (mem_defSet.mp (mem_filter.mp hq).2).2
  linarith

/-- **Lemma D (donors).** After Rule 2' every triple with `c ≥ 0` has final charge `≥ 0`. -/
theorem final_nonneg_of_charge_nonneg {H : Finset (Finset V)} {T : Finset V} (hT : 0 ≤ charge H T) :
    0 ≤ final H T := by
  unfold final
  rw [received_eq_zero hT, add_zero]
  split_ifs
  · exact le_refl 0
  · exact hT

/-- **Lemma D (donors).** A donor ends at exactly `0`. -/
theorem final_eq_zero_of_donor {H : Finset (Finset V)} {T : Finset V} (hd : Donor H T) :
    final H T = 0 := by
  unfold final
  rw [received_eq_zero (le_of_lt hd.1), add_zero, if_pos hd]

/-- **Conditional endpoint. NOT a verification of the target.** If Rule 2' leaves every deficient triple of a
uniform `H` with nonnegative charge (the unformalized hypothesis of written Theorem C'), then `Φ(H) ≤ 0` and `|H| ≤ C(|V|, 2)`. -/
theorem conditional_endpoint (H : Finset (Finset V)) (hH : Uniform H)
    (hrec : ∀ T ∈ H, Deficient H T → 0 ≤ final H T) :
    Phi H ≤ 0 ∧ (H.card : ℚ) ≤ (((Fintype.card V).choose 2 : ℕ) : ℚ) := by
  have hall : ∀ T ∈ H, 0 ≤ final H T := by
    intro T hT
    by_cases hd : Deficient H T
    · exact hrec T hT hd
    · have hd' : ¬ charge H T < 0 := hd
      exact final_nonneg_of_charge_nonneg (not_lt.mp hd')
  have hsum : 0 ≤ ∑ T ∈ H, final H T := Finset.sum_nonneg hall
  rw [sum_final_eq_neg_Phi H hH] at hsum
  have hPhi : Phi H ≤ 0 := by linarith
  exact ⟨hPhi, endpoint_of_Phi_nonpos H hPhi⟩

end L1Top
end Erdos643R3

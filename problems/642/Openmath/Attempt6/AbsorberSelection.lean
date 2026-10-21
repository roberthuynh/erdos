import Mathlib

namespace Erdos585.Attempt6.AbsorberSelection
noncomputable section
open scoped BigOperators
variable {A C : Type*} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]

def classSet (c : A → C) (a : A) : Finset A := Finset.univ.filter (fun b => c b = c a)
def eligible (c : A → C) : Finset A := Finset.univ.filter (fun a => 2 ≤ (classSet c a).card)

lemma self_mem_class (c : A → C) (a : A) : a ∈ classSet c a := by simp [classSet]
lemma class_eq (c : A → C) {a b : A} (h : c a = c b) : classSet c a = classSet c b := by
  simp [classSet, h]
lemma eligible_class (c : A → C) {a b : A} (h : c a = c b) :
    a ∈ eligible c ↔ b ∈ eligible c := by simp [eligible, class_eq c h]

/-- There is at most one discarded candidate of each class. -/
theorem discarded_card_le (c : A → C) :
    (Finset.univ \ eligible c).card ≤ Fintype.card C := by
  apply Finset.card_le_card_of_injOn c (fun _ _ => Finset.mem_univ _)
  intro a ha b hb hab
  have hsmall : (classSet c a).card < 2 := by
    have hn := (Finset.mem_sdiff.mp ha).2
    simpa [eligible] using hn
  have hbclass : b ∈ classSet c a := by simp [classSet, hab]
  exact Finset.card_le_one.mp (by omega : (classSet c a).card ≤ 1)
    a (self_mem_class c a) b hbclass

theorem eligible_size (c : A → C) (T ell : ℕ)
    (hT : T ≤ Fintype.card A) (hC : Fintype.card C ≤ ell) (hlarge : 2 * ell ≤ T) :
    T ≤ 2 * (eligible c).card := by
  have hd := discarded_card_le c
  have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (eligible c))
  simp only [Finset.card_univ] at hc
  omega

/-- Ordered representation of the class-weighted unordered-pair law.
Choose the first eligible candidate uniformly, then a distinct classmate
uniformly. Forgetting order gives the stated unordered selection. -/
def weight (c : A → C) (p : A × A) : ℝ :=
  if p.1 ∈ eligible c ∧ p.2 ∈ (classSet c p.1).erase p.1 then
    1 / (eligible c).card / ((classSet c p.1).card - 1 : ℕ)
  else 0

lemma weight_nonneg (c : A → C) (p : A × A) : 0 ≤ weight c p := by
  unfold weight
  split_ifs <;> positivity

lemma row_sum (c : A → C) (a : A) :
    (∑ b : A, weight c (a,b)) = if a ∈ eligible c then (1 : ℝ) / (eligible c).card else 0 := by
  classical
  by_cases ha : a ∈ eligible c
  · have hn : 2 ≤ (classSet c a).card := by simpa [eligible] using ha
    have hden : (((classSet c a).card - 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (by omega : (classSet c a).card - 1 ≠ 0)
    have hc : ((classSet c a).erase a).card = (classSet c a).card - 1 :=
      Finset.card_erase_of_mem (self_mem_class c a)
    simp only [weight, ha, true_and, Finset.sum_ite_mem, Finset.univ_inter, if_true]
    rw [Finset.sum_const, nsmul_eq_mul, hc]
    field_simp
  · simp [weight, ha]

theorem weight_sum (c : A → C) (hpos : 0 < (eligible c).card) :
    (∑ p : A × A, weight c p) = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [row_sum]
  simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hne : ((eligible c).card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hpos)
  field_simp

lemma weight_symm (c : A → C) (a b : A) : weight c (a,b) = weight c (b,a) := by
  by_cases hab : c a = c b
  · have he := eligible_class c hab
    have hc := class_eq c hab
    by_cases ha : a ∈ eligible c
    · have hb := he.mp ha
      simp [weight, ha, hb, classSet, hab, eq_comm]
    · have hb : b ∉ eligible c := fun h => ha (he.mpr h)
      simp [weight, ha, hb]
  · have hba : c b ≠ c a := Ne.symm hab
    simp [weight, classSet, hab, hba]

lemma column_sum (c : A → C) (a : A) :
    (∑ b : A, weight c (b,a)) = if a ∈ eligible c then (1 : ℝ) / (eligible c).card else 0 := by
  simp_rw [weight_symm c _ a]
  exact row_sum c a

lemma weight_diag (c : A → C) (a : A) : weight c (a,a) = 0 := by simp [weight]

def selected (p : A × A) : Finset A := {p.1, p.2}

theorem candidate_marginal (c : A → C) (a : A) :
    (∑ p : A × A, if a ∈ selected p then weight c p else 0) =
      if a ∈ eligible c then (2 : ℝ) / (eligible c).card else 0 := by
  have hsplit : ∀ p : A × A,
      (if a ∈ selected p then weight c p else 0) =
      (if p.1 = a then weight c p else 0) + (if p.2 = a then weight c p else 0) := by
    rintro ⟨x,y⟩
    by_cases hx : x = a <;> by_cases hy : y = a <;>
      simp_all [selected, weight_diag, eq_comm]
  have hfirst : (∑ p : A × A, if p.1 = a then weight c p else 0) =
      ∑ b : A, weight c (a,b) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp
  have hsecond : (∑ p : A × A, if p.2 = a then weight c p else 0) =
      ∑ b : A, weight c (b,a) := by
    rw [Fintype.sum_prod_type]
    simp
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, hfirst, hsecond, row_sum, column_sum]
  split_ifs <;> ring


theorem marginal_le (c : A → C) (T ell : ℕ) (hTpos : 0 < T)
    (hT : T ≤ Fintype.card A) (hC : Fintype.card C ≤ ell) (hlarge : 2 * ell ≤ T)
    (a : A) :
    (∑ p : A × A, if a ∈ selected p then weight c p else 0) ≤ 4 / (T : ℝ) := by
  have hsize := eligible_size c T ell hT hC hlarge
  have hpos : 0 < (eligible c).card := by omega
  have hTr : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hSr : (0 : ℝ) < (eligible c).card := by exact_mod_cast hpos
  have hr : (T : ℝ) ≤ 2 * (eligible c).card := by exact_mod_cast hsize
  rw [candidate_marginal]
  split_ifs
  · apply (div_le_div_iff₀ hSr hTr).mpr
    linarith
  · positivity

theorem selected_pair (c : A → C) (p : A × A) (hp : weight c p ≠ 0) :
    (selected p).card = 2 ∧ c p.1 = c p.2 ∧ p.1 ≠ p.2 := by
  have hm : p.1 ∈ eligible c ∧ p.2 ∈ (classSet c p.1).erase p.1 := by
    by_contra hn
    simp only [weight, if_neg hn, ne_eq, not_true_eq_false] at hp
  have hne := (Finset.mem_erase.mp hm.2).1
  have he : c p.2 = c p.1 := by
    simpa [classSet] using (Finset.mem_erase.mp hm.2).2
  exact ⟨by simp [selected, hne, Ne.symm hne], he.symm, Ne.symm hne⟩

                                                                  
                                                                         
                                                            
theorem finite_pair_law (c : A → C) (T ell : ℕ) (hTpos : 0 < T)
    (hT : T ≤ Fintype.card A) (hC : Fintype.card C ≤ ell) (hlarge : 2 * ell ≤ T) :
    (∀ p, 0 ≤ weight c p) ∧ (∑ p : A × A, weight c p) = 1 ∧
    (∀ p, weight c p ≠ 0 →
      (selected p).card = 2 ∧ c p.1 = c p.2 ∧ p.1 ≠ p.2) ∧
    ∀ a, (∑ p : A × A, if a ∈ selected p then weight c p else 0) ≤ 4 / (T : ℝ) := by
  have hsize := eligible_size c T ell hT hC hlarge
  exact ⟨weight_nonneg c, weight_sum c (by omega), selected_pair c,
    marginal_le c T ell hTpos hT hC hlarge⟩

theorem expected_load_identity (c : A → C) (f : A → ℝ) :
    (∑ p : A × A, weight c p * ∑ a ∈ selected p, f a) =
      ∑ a : A, (if a ∈ eligible c then (2 : ℝ) / (eligible c).card else 0) * f a := by
  have hin (p : A × A) : (∑ a ∈ selected p, f a) =
      ∑ a : A, if a ∈ selected p then f a else 0 := by
    simp [Finset.sum_ite_mem]
  simp_rw [hin, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  have he : ∀ p : A × A, weight c p * (if a ∈ selected p then f a else 0) =
      (if a ∈ selected p then weight c p else 0) * f a := by
    intro p; split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.sum_mul, candidate_marginal]

theorem expected_load_le (c : A → C) (T ell : ℕ) (hTpos : 0 < T)
    (hT : T ≤ Fintype.card A) (hC : Fintype.card C ≤ ell) (hlarge : 2 * ell ≤ T)
    (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (∑ p : A × A, weight c p * ∑ a ∈ selected p, f a) ≤
      (4 / (T : ℝ)) * ∑ a : A, f a := by
  rw [expected_load_identity, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_right _ (hf a)
  rw [← candidate_marginal]
  exact marginal_le c T ell hTpos hT hC hlarge a

/-- Disjoint actual candidate interiors turn total candidate neighbor load into
at most the size of the original neighbor set. -/
theorem disjoint_neighbor_load {V : Type*} [DecidableEq V]
    (interior : A → Finset V) (hdis : Pairwise (fun a b => Disjoint (interior a) (interior b)))
    (N : Finset V) :
    (∑ a : A, (N ∩ interior a).card) ≤ N.card := by
  have hd : (↑(Finset.univ : Finset A) : Set A).PairwiseDisjoint (fun a => N ∩ interior a) := by
    intro a _ b _ hab
    exact (hdis hab).mono Finset.inter_subset_right Finset.inter_subset_right
  rw [← Finset.card_biUnion hd]
  apply Finset.card_le_card
  intro v hv
  obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hv
  exact (Finset.mem_inter.mp ha).1

theorem expected_neighbor_load_le {V : Type*} [DecidableEq V]
    (c : A → C) (T ell : ℕ) (hTpos : 0 < T)
    (hT : T ≤ Fintype.card A) (hC : Fintype.card C ≤ ell) (hlarge : 2 * ell ≤ T)
    (interior : A → Finset V) (hdis : Pairwise (fun a b => Disjoint (interior a) (interior b)))
    (N : Finset V) :
    (∑ p : A × A, weight c p * ∑ a ∈ selected p, ((N ∩ interior a).card : ℝ)) ≤
      4 * (N.card : ℝ) / T := by
  have h := expected_load_le c T ell hTpos hT hC hlarge
    (fun a => ((N ∩ interior a).card : ℝ)) (fun _ => Nat.cast_nonneg _)
  have hn : (∑ a : A, ((N ∩ interior a).card : ℝ)) ≤ (N.card : ℝ) := by
    exact_mod_cast disjoint_neighbor_load interior hdis N
  calc
    _ ≤ (4 / (T : ℝ)) * ∑ a : A, ((N ∩ interior a).card : ℝ) := h
    _ ≤ (4 / (T : ℝ)) * N.card := mul_le_mul_of_nonneg_left hn (by positivity)
    _ = _ := by ring


/-- Actual path specialization. Class labels are the positive path lengths minus
one, so at most ell classes are used and the selected paths have equal length. -/
theorem actual_path_pair_law {V : Type*} (G : SimpleGraph V) {x y : V}
    (p : A → G.Walk x y) (ell T : ℕ)
    (hpath : ∀ a, (p a).IsPath) (hlen : ∀ a, 0 < (p a).length ∧ (p a).length ≤ ell)
    (hTpos : 0 < T) (hT : T ≤ Fintype.card A) (hlarge : 2 * ell ≤ T) :
    ∃ w : A × A → ℝ,
      (∀ q, 0 ≤ w q) ∧ (∑ q, w q) = 1 ∧
      (∀ q, w q ≠ 0 → q.1 ≠ q.2 ∧ (p q.1).IsPath ∧ (p q.2).IsPath ∧
        (p q.1).length = (p q.2).length ∧ (p q.1).length ≤ ell) ∧
      ∀ a, (∑ q, if a ∈ selected q then w q else 0) ≤ 4 / (T : ℝ) := by
  let c : A → Fin ell := fun a => ⟨(p a).length - 1, by
    obtain ⟨hp, hle⟩ := hlen a
    omega⟩
  obtain ⟨hn, hs, hp, hm⟩ := finite_pair_law c T ell hTpos hT (by simp) hlarge
  refine ⟨weight c, hn, hs, ?_, hm⟩
  intro q hq
  have hh := hp q hq
  have he := congrArg Fin.val hh.2.1
  have h1 := hlen q.1
  have h2 := hlen q.2
  refine ⟨hh.2.2, hpath _, hpath _, ?_, h1.2⟩
  change (p q.1).length - 1 = (p q.2).length - 1 at he
  omega

namespace ProductLaw
variable {J B : Type*} [Fintype J] [DecidableEq J] [Fintype B]
def mass (w : J → B → ℝ) (ω : J → B) : ℝ := ∏ j, w j (ω j)

theorem nonneg (w : J → B → ℝ) (hw : ∀ j b, 0 ≤ w j b) (ω : J → B) :
    0 ≤ mass w ω := Finset.prod_nonneg (fun j _ => hw j (ω j))

theorem sum_one (w : J → B → ℝ) (hw : ∀ j, ∑ b, w j b = 1) :
    ∑ ω : J → B, mass w ω = 1 := by
  simp only [mass]
  rw [← Fintype.prod_sum]
  simp_rw [hw]
  simp

theorem factorization (w f : J → B → ℝ) :
    (∑ ω : J → B, mass w ω * ∏ j, f j (ω j)) =
      ∏ j, ∑ b, w j b * f j b := by
  simp only [mass, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j b => w j b * f j b)).symm

/-- Independence here is constructed by the explicit product mass. -/
theorem exp_factorization (w X : J → B → ℝ) (t : ℝ) :
    (∑ ω : J → B, mass w ω * Real.exp (t * ∑ j, X j (ω j))) =
      ∏ j, ∑ b, w j b * Real.exp (t * X j b) := by
  have he (ω : J → B) :
      Real.exp (t * ∑ j, X j (ω j)) = ∏ j, Real.exp (t * X j (ω j)) := by
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [he]
  exact factorization w (fun j b => Real.exp (t * X j b))

lemma exp_chord (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (Real.log 2 * x) ≤ 1 + x := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (Real.log 2))
    (sub_nonneg.mpr hx1) hx (by ring : (1-x)+x=1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  rw [mul_comm (Real.log 2) x]
  linarith

theorem block_mgf (w X : B → ℝ) (hw : ∀ b, 0 ≤ w b) (hs : ∑ b, w b = 1)
    (D : ℝ) (hD : 0 < D) (hX : ∀ b, 0 ≤ X b ∧ X b ≤ D) :
    (∑ b, w b * Real.exp (Real.log 2 / D * X b)) ≤
      Real.exp ((∑ b, w b * X b) / D) := by
  calc
    _ ≤ ∑ b, w b * (1 + X b / D) := by
      apply Finset.sum_le_sum
      intro b _
      apply mul_le_mul_of_nonneg_left _ (hw b)
      have h := exp_chord (X b / D) (div_nonneg (hX b).1 hD.le)
        ((div_le_one hD).mpr (hX b).2)
      simpa only [div_mul_eq_mul_div, mul_div_assoc] using h
    _ = 1 + (∑ b, w b * X b) / D := by
      simp only [mul_add, mul_one, ← mul_div_assoc]
      rw [Finset.sum_add_distrib, hs, Finset.sum_div]
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp ((∑ b, w b * X b) / D)

theorem mgf_bound (w X : J → B → ℝ) (hw : ∀ j b, 0 ≤ w j b)
    (hs : ∀ j, ∑ b, w j b = 1) (D : ℝ) (hD : 0 < D)
    (hX : ∀ j b, 0 ≤ X j b ∧ X j b ≤ D) :
    (∑ ω : J → B, mass w ω * Real.exp (Real.log 2 / D * ∑ j, X j (ω j))) ≤
      Real.exp ((∑ j, ∑ b, w j b * X j b) / D) := by
  rw [exp_factorization]
  calc
    _ ≤ ∏ j, Real.exp ((∑ b, w j b * X j b) / D) := by
      apply Finset.prod_le_prod
      · intro j _
        exact Finset.sum_nonneg (fun b _ => mul_nonneg (hw j b) (Real.exp_pos _).le)
      · intro j _
        exact block_mgf (w j) (X j) (hw j) (hs j) D hD (hX j)
    _ = _ := by rw [← Real.exp_sum, Finset.sum_div]

                                                                               
theorem exp_tail {Ω : Type*} [Fintype Ω] (w Z : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (t R : ℝ) (ht : 0 ≤ t) :
    (∑ ω, if R ≤ Z ω then w ω else 0) ≤
      (∑ ω, w ω * Real.exp (t * Z ω)) / Real.exp (t * R) := by
  apply (le_div_iff₀ (Real.exp_pos _)).mpr
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : R ≤ Z ω
  · simp only [h, if_true]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h ht)) (hw ω)
  · simp only [h, if_false, zero_mul]
    exact mul_nonneg (hw ω) (Real.exp_pos _).le

/-- Independent nonnegative blocks in [0,D] obey the exact class-selection
tail at twice the total mean plus 2DL. -/
theorem bounded_block_tail (w X : J → B → ℝ) (hw : ∀ j b, 0 ≤ w j b)
    (hs : ∀ j, ∑ b, w j b = 1) (D : ℝ) (hD : 0 < D)
    (hX : ∀ j b, 0 ≤ X j b ∧ X j b ≤ D) (L : ℝ) :
    (∑ ω : J → B, if
      2 * (∑ j, ∑ b, w j b * X j b) + 2 * D * L ≤ ∑ j, X j (ω j)
      then mass w ω else 0) ≤ Real.exp (-2 * Real.log 2 * L) := by
  let μ : ℝ := ∑ j, ∑ b, w j b * X j b
  have hμ : 0 ≤ μ := Finset.sum_nonneg (fun j _ =>
    Finset.sum_nonneg (fun b _ => mul_nonneg (hw j b) (hX j b).1))
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := exp_tail (mass w) (fun ω => ∑ j, X j (ω j)) (nonneg w hw)
    (Real.log 2 / D) (2 * μ + 2 * D * L) (div_nonneg hlog.le hD.le)
  apply h.trans
  calc
    _ ≤ Real.exp (μ / D) / Real.exp (Real.log 2 / D * (2 * μ + 2 * D * L)) :=
      div_le_div_of_nonneg_right (mgf_bound w X hw hs D hD hX) (Real.exp_pos _).le
    _ = Real.exp (μ / D - Real.log 2 / D * (2 * μ + 2 * D * L)) := by rw [Real.exp_sub]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hloghalf : (1 : ℝ) ≤ 2 * Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hneg : (1 - 2 * Real.log 2) * (μ / D) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (div_nonneg hμ hD.le)
      have he : μ / D - Real.log 2 / D * (2 * μ + 2 * D * L) =
          (1 - 2 * Real.log 2) * (μ / D) - 2 * Real.log 2 * L := by
        field_simp
        <;> ring
      rw [he]
      linarith

                                                                           
theorem bounded_block_tail_of_mean_le (w X : J → B → ℝ) (hw : ∀ j b, 0 ≤ w j b)
    (hs : ∀ j, ∑ b, w j b = 1) (D : ℝ) (hD : 0 < D)
    (hX : ∀ j b, 0 ≤ X j b ∧ X j b ≤ D)
    (M L : ℝ) (hM : (∑ j, ∑ b, w j b * X j b) ≤ M) :
    (∑ ω : J → B, if 2 * M + 2 * D * L ≤ ∑ j, X j (ω j)
      then mass w ω else 0) ≤ Real.exp (-2 * Real.log 2 * L) := by
  apply le_trans _ (bounded_block_tail w X hw hs D hD hX L)
  apply Finset.sum_le_sum
  intro ω _
  split_ifs with h1 h2 h2
  · rfl
  · exfalso
    apply h2
    linarith
  · exact nonneg w hw ω
  · rfl

/-- Finite union bound with a positive-mass witness. -/
theorem exists_avoiding {Ω K : Type*} [Fintype Ω] [Fintype K]
    (w : Ω → ℝ) (Z : K → Ω → ℝ) (R ε : ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hs : ∑ ω, w ω = 1)
    (htail : ∀ k, (∑ ω, if R ≤ Z k ω then w ω else 0) ≤ ε)
    (hsmall : (Fintype.card K : ℝ) * ε < 1) :
    ∃ ω, w ω ≠ 0 ∧ ∀ k, Z k ω < R := by
  classical
  by_contra hn
  push_neg at hn
  have hpoint (ω : Ω) : w ω ≤ ∑ k, if R ≤ Z k ω then w ω else 0 := by
    by_cases hz : w ω = 0
    · simp [hz]
    · obtain ⟨k, hk⟩ := hn ω hz
      have hb := Finset.single_le_sum
        (f := fun k => if R ≤ Z k ω then w ω else 0)
        (fun k _ => by split_ifs; exact hw ω; exact le_rfl) (Finset.mem_univ k)
      simpa only [hk, if_true] using hb
  have hb : (1 : ℝ) ≤ (Fintype.card K : ℝ) * ε := by
    calc
      1 = ∑ ω, w ω := hs.symm
      _ ≤ ∑ ω, ∑ k, if R ≤ Z k ω then w ω else 0 :=
        Finset.sum_le_sum (fun ω _ => hpoint ω)
      _ = ∑ k, ∑ ω, if R ≤ Z k ω then w ω else 0 := Finset.sum_comm
      _ ≤ ∑ _k : K, ε := Finset.sum_le_sum (fun k _ => htail k)
      _ = _ := by simp
  linarith

lemma log_order_union_bound (N : ℝ) (hN : 1 < N) :
    N * Real.exp (-2 * Real.log 2 * (Real.log N / Real.log 2)) < 1 := by
  have hNpos : 0 < N := by linarith
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have he : -2 * Real.log 2 * (Real.log N / Real.log 2) =
      -(Real.log N + Real.log N) := by field_simp; ring
  rw [he, Real.exp_neg, Real.exp_add, Real.exp_log hNpos]
  have hnz : N ≠ 0 := ne_of_gt hNpos
  field_simp
  nlinarith

theorem coordinate_expectation (w : J → B → ℝ) (hs : ∀ j, ∑ b, w j b = 1)
    (k : J) (f : B → ℝ) :
    (∑ ω : J → B, mass w ω * f (ω k)) = ∑ b, w k b * f b := by
  have h := factorization w (fun j b => if j = k then f b else 1)
  have he (ω : J → B) :
      (∏ j, if j = k then f (ω j) else 1) = f (ω k) := by simp
  simp only [he] at h
  have hr (j : J) : (∑ b, w j b * (if j = k then f b else 1)) =
      if j = k then ∑ b, w k b * f b else 1 := by
    by_cases hj : j = k <;> simp [hj, hs]
  simp only [hr] at h
  simpa using h

theorem total_expectation (w X : J → B → ℝ) (hs : ∀ j, ∑ b, w j b = 1) :
    (∑ ω : J → B, mass w ω * ∑ j, X j (ω j)) = ∑ j, ∑ b, w j b * X j b := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact coordinate_expectation w hs j (X j)

end ProductLaw


section Families
variable {J V : Type*} [Fintype J] [DecidableEq J] [DecidableEq V]

def blockLoad (interior : J → A → Finset V) (N : Finset V) (j : J) (p : A × A) : ℝ :=
  ∑ a ∈ selected p, ((N ∩ interior j a).card : ℝ)

def selectedVertices (interior : J → A → Finset V) (ω : J → A × A) : Finset V :=
  Finset.univ.biUnion (fun j => (selected (ω j)).biUnion (interior j))

theorem blockLoad_bounds (interior : J → A → Finset V) (N : Finset V)
    (ell : ℕ) (hinterior : ∀ j a, (interior j a).card ≤ ell) (j : J) (p : A × A) :
    0 ≤ blockLoad interior N j p ∧ blockLoad interior N j p ≤ 2 * (ell : ℝ) := by
  constructor
  · exact Finset.sum_nonneg (fun a _ => Nat.cast_nonneg _)
  · have hb : ∀ a ∈ selected p, ((N ∩ interior j a).card : ℝ) ≤ ell := by
      intro a _
      exact_mod_cast (Finset.card_le_card Finset.inter_subset_right).trans (hinterior j a)
    have hc : (selected p).card ≤ 2 := by
      by_cases h : p.1 = p.2 <;> simp [selected, h]
    have hr : ((selected p).card : ℝ) ≤ 2 := by exact_mod_cast hc
    calc
      blockLoad interior N j p ≤ ∑ _a ∈ selected p, (ell : ℝ) :=
        Finset.sum_le_sum hb
      _ = (selected p).card * (ell : ℝ) := by simp
      _ ≤ 2 * (ell : ℝ) := mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _)

theorem selected_neighbor_load_le (interior : J → A → Finset V) (N : Finset V)
    (ω : J → A × A) :
    ((N ∩ selectedVertices interior ω).card : ℝ) ≤
      ∑ j, blockLoad interior N j (ω j) := by
  have hn : (N ∩ selectedVertices interior ω).card ≤
      ∑ j, ∑ a ∈ selected (ω j), (N ∩ interior j a).card := by
    simp only [selectedVertices, Finset.inter_biUnion]
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro j _
    exact Finset.card_biUnion_le
  simp only [blockLoad]
  exact_mod_cast hn

theorem family_mean_le (c : J → A → C) (T ell : ℕ) (hTpos : 0 < T)
    (hT : T ≤ Fintype.card A) (hC : Fintype.card C ≤ ell) (hlarge : 2 * ell ≤ T)
    (interior : J → A → Finset V)
    (hdis : Pairwise (fun u v : J × A => Disjoint (interior u.1 u.2) (interior v.1 v.2)))
    (N : Finset V) :
    (∑ j, ∑ p : A × A, weight (c j) p * blockLoad interior N j p) ≤
      4 * (N.card : ℝ) / T := by
  have hsum := disjoint_neighbor_load (fun u : J × A => interior u.1 u.2) hdis N
  rw [Fintype.sum_prod_type] at hsum
  have hsumR : (∑ j, ∑ a, ((N ∩ interior j a).card : ℝ)) ≤ N.card := by
    exact_mod_cast hsum
  calc
    _ ≤ ∑ j, (4 / (T : ℝ)) * ∑ a, ((N ∩ interior j a).card : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      exact expected_load_le (c j) T ell hTpos hT hC hlarge _
        (fun _ => Nat.cast_nonneg _)
    _ = (4 / (T : ℝ)) * (∑ j, ∑ a, ((N ∩ interior j a).card : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ (4 / (T : ℝ)) * N.card := mul_le_mul_of_nonneg_left hsumR (by positivity)
    _ = _ := by ring

/-- Actual selected-interior neighbor tail under the constructed independent
class-weighted pair law. No marginal, independence, or mean premise is assumed. -/
theorem family_neighbor_tail (c : J → A → C) (T ell : ℕ) (hTpos : 0 < T)
    (hell : 0 < ell) (hT : T ≤ Fintype.card A) (hC : Fintype.card C ≤ ell)
    (hlarge : 2 * ell ≤ T) (interior : J → A → Finset V)
    (hinterior : ∀ j a, (interior j a).card ≤ ell)
    (hdis : Pairwise (fun u v : J × A => Disjoint (interior u.1 u.2) (interior v.1 v.2)))
    (N : Finset V) (M L : ℝ) (hM : (N.card : ℝ) ≤ M) :
    (∑ ω : J → A × A, if
      8 * M / T + 4 * (ell : ℝ) * L ≤ ((N ∩ selectedVertices interior ω).card : ℝ)
      then ProductLaw.mass (fun j => weight (c j)) ω else 0) ≤
        Real.exp (-2 * Real.log 2 * L) := by
  let w := fun j => weight (c j)
  have hnorm : ∀ j, ∑ p, w j p = 1 := by
    intro j
    exact weight_sum (c j) (by have := eligible_size (c j) T ell hT hC hlarge; omega)
  have hmean : (∑ j, ∑ p, w j p * blockLoad interior N j p) ≤ 4 * M / T := by
    apply (family_mean_le c T ell hTpos hT hC hlarge interior hdis N).trans
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hM (by norm_num))
      (Nat.cast_nonneg _)
  have hD : (0 : ℝ) < 2 * ell := by exact_mod_cast (by omega : 0 < 2 * ell)
  have htail := ProductLaw.bounded_block_tail_of_mean_le w (blockLoad interior N)
    (fun j p => weight_nonneg (c j) p) hnorm (2 * ell) hD
    (blockLoad_bounds interior N ell hinterior) (4 * M / T) L hmean
  have he : 2 * (4 * M / T) + 2 * (2 * (ell : ℝ)) * L =
      8 * M / T + 4 * (ell : ℝ) * L := by ring
  rw [he] at htail
  apply le_trans _ htail
  apply Finset.sum_le_sum
  intro ω _
  split_ifs with ha hb hb
  · rfl
  · exact False.elim (hb (ha.trans (selected_neighbor_load_le interior N ω)))
  · exact ProductLaw.nonneg w (fun j p => weight_nonneg (c j) p) ω
  · rfl
/-- Simultaneously select equal-class pairs with actual neighbor loads below
8M/T+4ell*L. The only failure-budget premise is explicit and numeric. -/
theorem exists_bounded_selection [Fintype V]
    (c : J → A → C) (T ell : ℕ) (hTpos : 0 < T)
    (hell : 0 < ell) (hT : T ≤ Fintype.card A) (hC : Fintype.card C ≤ ell)
    (hlarge : 2 * ell ≤ T) (interior : J → A → Finset V)
    (hinterior : ∀ j a, (interior j a).card ≤ ell)
    (hdis : Pairwise (fun u v : J × A => Disjoint (interior u.1 u.2) (interior v.1 v.2)))
    (N : V → Finset V) (M L : ℝ) (hM : ∀ v, ((N v).card : ℝ) ≤ M)
    (hbudget : (Fintype.card V : ℝ) * Real.exp (-2 * Real.log 2 * L) < 1) :
    ∃ ω : J → A × A,
      (∀ j, (selected (ω j)).card = 2 ∧ c j (ω j).1 = c j (ω j).2 ∧
        (ω j).1 ≠ (ω j).2) ∧
      ∀ v, (((N v) ∩ selectedVertices interior ω).card : ℝ) <
        8 * M / T + 4 * (ell : ℝ) * L := by
  let w := fun j => weight (c j)
  have hnorm : ∀ j, ∑ p, w j p = 1 := by
    intro j
    exact weight_sum (c j) (by have := eligible_size (c j) T ell hT hC hlarge; omega)
  obtain ⟨ω, hω, hload⟩ := ProductLaw.exists_avoiding (ProductLaw.mass w)
    (fun v ω => (((N v) ∩ selectedVertices interior ω).card : ℝ))
    (8 * M / T + 4 * (ell : ℝ) * L) (Real.exp (-2 * Real.log 2 * L))
    (ProductLaw.nonneg w (fun j p => weight_nonneg (c j) p))
    (ProductLaw.sum_one w hnorm)
    (fun v => family_neighbor_tail c T ell hTpos hell hT hC hlarge interior hinterior hdis
      (N v) M L (hM v)) hbudget
  refine ⟨ω, ?_, hload⟩
  intro j
  apply selected_pair (c j)
  have hh : ∀ j ∈ (Finset.univ : Finset J), w j (ω j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hω
  exact hh j (Finset.mem_univ j)

/-- The published-style choice L=log_2 |V| pays the finite union bound for |V|>1. -/
theorem exists_bounded_selection_log [Fintype V]
    (hV : 1 < Fintype.card V)
    (c : J → A → C) (T ell : ℕ) (hTpos : 0 < T)
    (hell : 0 < ell) (hT : T ≤ Fintype.card A) (hC : Fintype.card C ≤ ell)
    (hlarge : 2 * ell ≤ T) (interior : J → A → Finset V)
    (hinterior : ∀ j a, (interior j a).card ≤ ell)
    (hdis : Pairwise (fun u v : J × A => Disjoint (interior u.1 u.2) (interior v.1 v.2)))
    (N : V → Finset V) (M : ℝ) (hM : ∀ v, ((N v).card : ℝ) ≤ M) :
    ∃ ω : J → A × A,
      (∀ j, (selected (ω j)).card = 2 ∧ c j (ω j).1 = c j (ω j).2 ∧
        (ω j).1 ≠ (ω j).2) ∧
      ∀ v, (((N v) ∩ selectedVertices interior ω).card : ℝ) <
        8 * M / T + 4 * (ell : ℝ) *
          (Real.log (Fintype.card V) / Real.log 2) := by
  apply exists_bounded_selection c T ell hTpos hell hT hC hlarge interior hinterior hdis
    N M _ hM
  exact ProductLaw.log_order_union_bound _ (by exact_mod_cast hV)

/-- The actual union's expected neighbor load under the explicit product law,
not merely the sum of separate formal marginal expressions. -/
theorem family_expected_neighbor_load_le
    (c : J → A → C) (T ell : ℕ) (hTpos : 0 < T)
    (hT : T ≤ Fintype.card A) (hC : Fintype.card C ≤ ell) (hlarge : 2 * ell ≤ T)
    (interior : J → A → Finset V)
    (hdis : Pairwise (fun u v : J × A => Disjoint (interior u.1 u.2) (interior v.1 v.2)))
    (N : Finset V) :
    (∑ ω : J → A × A, ProductLaw.mass (fun j => weight (c j)) ω *
      ((N ∩ selectedVertices interior ω).card : ℝ)) ≤ 4 * (N.card : ℝ) / T := by
  let w := fun j => weight (c j)
  have hnorm : ∀ j, ∑ p, w j p = 1 := by
    intro j
    exact weight_sum (c j) (by have := eligible_size (c j) T ell hT hC hlarge; omega)
  calc
    _ ≤ ∑ ω : J → A × A, ProductLaw.mass w ω * ∑ j, blockLoad interior N j (ω j) := by
      apply Finset.sum_le_sum
      intro ω _
      exact mul_le_mul_of_nonneg_left (selected_neighbor_load_le interior N ω)
        (ProductLaw.nonneg w (fun j p => weight_nonneg (c j) p) ω)
    _ = ∑ j, ∑ p, w j p * blockLoad interior N j p :=
      ProductLaw.total_expectation w (blockLoad interior N) hnorm
    _ ≤ _ := family_mean_le c T ell hTpos hT hC hlarge interior hdis N

end Families


section ActualPaths
variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]

def pathInterior {G : SimpleGraph V} {x y : V} (p : G.Walk x y) : Finset V :=
  (p.support.toFinset.erase x).erase y

lemma pathInterior_card_le {G : SimpleGraph V} {x y : V} (p : G.Walk x y) :
    (pathInterior p).card ≤ p.length := by
  have hc := p.support.toFinset_card_le
  rw [p.length_support] at hc
  have hx : x ∈ p.support.toFinset := by simpa using p.start_mem_support
  have he := Finset.card_erase_of_mem hx
  have hy := Finset.card_le_card (Finset.erase_subset y (p.support.toFinset.erase x))
  change (pathInterior p).card ≤ (p.support.toFinset.erase x).card at hy
  omega

/-- Actual same-endpoint simple paths, grouped by their actual lengths, admit
equal-length pair choices with the strengthened simultaneous neighbor bound.
All selected interiors are the walk supports with their two endpoints removed. -/
theorem actual_path_family_selection
    (G : SimpleGraph V) [DecidableRel G.Adj] (hV : 1 < Fintype.card V)
    (x y : J → V) (p : ∀ j, A → G.Walk (x j) (y j))
    (ell T : ℕ) (hell : 0 < ell) (hTpos : 0 < T)
    (hT : T ≤ Fintype.card A) (hlarge : 2 * ell ≤ T)
    (hpath : ∀ j a, (p j a).IsPath)
    (hne : ∀ j a, (pathInterior (p j a)).Nonempty)
    (hlen : ∀ j a, 0 < (p j a).length ∧ (p j a).length ≤ ell)
    (hdis : Pairwise (fun u v : J × A =>
      Disjoint (pathInterior (p u.1 u.2)) (pathInterior (p v.1 v.2))))
    (U : Finset V) (hU : ∀ j a, pathInterior (p j a) ⊆ U)
    (M : ℝ) (hM : ∀ v, ((G.neighborFinset v ∩ U).card : ℝ) ≤ M) :
    ∃ ω : J → A × A,
      (∀ j, (ω j).1 ≠ (ω j).2 ∧ p j (ω j).1 ≠ p j (ω j).2 ∧ (p j (ω j).1).IsPath ∧ (p j (ω j).2).IsPath ∧
        (p j (ω j).1).length = (p j (ω j).2).length) ∧
      ∀ v, ((G.neighborFinset v ∩
        selectedVertices (fun j a => pathInterior (p j a)) ω).card : ℝ) <
        8 * M / T + 4 * (ell : ℝ) * (Real.log (Fintype.card V) / Real.log 2) := by
  let c : J → A → Fin ell := fun j a => ⟨(p j a).length - 1, by
    have := hlen j a
    omega⟩
  let interior : J → A → Finset V := fun j a => pathInterior (p j a)
  have hi : ∀ j a, (interior j a).card ≤ ell := fun j a =>
    (pathInterior_card_le (p j a)).trans (hlen j a).2
  obtain ⟨ω, hp, hn⟩ := exists_bounded_selection_log hV c T ell hTpos hell hT
    (by simp) hlarge interior hi hdis (fun v => G.neighborFinset v ∩ U) M hM
  refine ⟨ω, ?_, ?_⟩
  · intro j
    have he := congrArg Fin.val (hp j).2.1
    have h1 := (hlen j (ω j).1).1
    have h2 := (hlen j (ω j).2).1
    have hpneq : p j (ω j).1 ≠ p j (ω j).2 := by
      intro heq
      have hidx : (j, (ω j).1) ≠ (j, (ω j).2) := by
        intro h
        exact (hp j).2.2 (congrArg Prod.snd h)
      have hd := hdis hidx
      change Disjoint (pathInterior (p j (ω j).1)) (pathInterior (p j (ω j).2)) at hd
      rw [heq] at hd
      obtain ⟨v, hv⟩ := hne j (ω j).2
      exact Finset.disjoint_left.mp hd hv hv
    refine ⟨(hp j).2.2, hpneq, hpath _ _, hpath _ _, ?_⟩
    change (p j (ω j).1).length - 1 = (p j (ω j).2).length - 1 at he
    omega
  · intro v
    have hsub : selectedVertices interior ω ⊆ U := by
      intro z hz
      obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hj
      exact hU j a ha
    have he : (G.neighborFinset v ∩ U) ∩ selectedVertices interior ω =
        G.neighborFinset v ∩ selectedVertices interior ω := by
      ext z
      simp only [Finset.mem_inter]
      constructor
      · exact fun h => ⟨h.1.1, h.2⟩
      · exact fun h => ⟨⟨h.1, hsub h.2⟩, h.2⟩
    simpa only [he] using hn v
end ActualPaths


/-- Push the explicit ordered construction to actual unordered two-element
candidate subsets. -/
def unorderedMass (c : A → C) (q : Finset A) : ℝ :=
  ∑ p : A × A, if selected p = q then weight c p else 0

theorem unorderedMass_nonneg (c : A → C) (q : Finset A) : 0 ≤ unorderedMass c q := by
  apply Finset.sum_nonneg
  intro p _
  split_ifs
  · exact weight_nonneg c p
  · rfl

theorem unorderedMass_sum (c : A → C) (hpos : 0 < (eligible c).card) :
    (∑ q : Finset A, unorderedMass c q) = 1 := by
  unfold unorderedMass
  rw [Finset.sum_comm]
  simpa using weight_sum c hpos

theorem unorderedMass_support (c : A → C) (q : Finset A) (hq : unorderedMass c q ≠ 0) :
    q.card = 2 ∧ ∃ a b, a ≠ b ∧ c a = c b ∧ q = {a,b} := by
  obtain ⟨p, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
  split_ifs at hp with he
  · have hs := selected_pair c p hp
    exact ⟨he ▸ hs.1, p.1, p.2, hs.2.2, hs.2.1, he.symm⟩
  · exact False.elim (hp rfl)

theorem unordered_candidate_marginal (c : A → C) (a : A) :
    (∑ q : Finset A, if a ∈ q then unorderedMass c q else 0) =
      if a ∈ eligible c then (2 : ℝ) / (eligible c).card else 0 := by
  have he (q : Finset A) :
      (if a ∈ q then unorderedMass c q else 0) =
      ∑ p : A × A, if selected p = q then (if a ∈ q then weight c p else 0) else 0 := by
    by_cases ha : a ∈ q <;> simp [unorderedMass, ha]
  simp_rw [he]
  rw [Finset.sum_comm]
  simpa using candidate_marginal c a

theorem unordered_pair_law (c : A → C) (T ell : ℕ) (hTpos : 0 < T)
    (hT : T ≤ Fintype.card A) (hC : Fintype.card C ≤ ell) (hlarge : 2 * ell ≤ T) :
    (∀ q, 0 ≤ unorderedMass c q) ∧ (∑ q : Finset A, unorderedMass c q) = 1 ∧
    (∀ q, unorderedMass c q ≠ 0 → q.card = 2 ∧
      ∃ a b, a ≠ b ∧ c a = c b ∧ q = {a,b}) ∧
    ∀ a, (∑ q : Finset A, if a ∈ q then unorderedMass c q else 0) ≤ 4 / (T : ℝ) := by
  have hsize := eligible_size c T ell hT hC hlarge
  refine ⟨unorderedMass_nonneg c, unorderedMass_sum c (by omega),
    unorderedMass_support c, ?_⟩
  intro a
  rw [unordered_candidate_marginal, ← candidate_marginal]
  exact marginal_le c T ell hTpos hT hC hlarge a

end
end Erdos585.Attempt6.AbsorberSelection

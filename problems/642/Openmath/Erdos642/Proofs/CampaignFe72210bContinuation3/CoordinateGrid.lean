import Openmath.Erdos642.Proofs.CampaignFe72210b.FiniteMarkov

/-! Actual finite coordinate representatives for a weighted Euclidean subspace. -/
namespace Erdos642.CampaignFe72210bContinuation3.CoordinateGrid
open Matrix

noncomputable def eta (μ : ℝ) : ℝ := μ / 1024
noncomputable def step (N : ℕ) (μ : ℝ) : ℝ := eta μ / (10 * (N : ℝ))
noncomputable def alphabet (N : ℕ) (μ : ℝ) : ℕ := ⌊20 * (N : ℝ) / eta μ⌋₊ + 1

 theorem eta_pos {μ : ℝ} (hμ : 0 < μ) : 0 < eta μ := by unfold eta; positivity
 theorem step_pos {N : ℕ} (hN : 1 ≤ N) {μ : ℝ} (hμ : 0 < μ) :
    0 < step N μ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  unfold step
  exact div_pos (eta_pos hμ) (by positivity)

 theorem alphabet_bound {N : ℕ} (hN : 1 ≤ N) {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    (alphabet N μ : ℝ) ≤ 23 * (N : ℝ) / eta μ ∧
      23 * (N : ℝ) / eta μ ≤ 24000 * (N : ℝ) / μ := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have he := eta_pos hμ
  have he1 : eta μ ≤ 1 := by unfold eta; linarith
  have hratio : 1 ≤ (N : ℝ) / eta μ := (le_div_iff₀ he).mpr (by linarith)
  have hf := Nat.floor_le (show 0 ≤ 20 * (N : ℝ) / eta μ by positivity)
  constructor
  · simp only [alphabet, Nat.cast_add, Nat.cast_one]
    simp only [mul_div_assoc] at hf ⊢
    nlinarith
  · unfold eta
    field_simp
    nlinarith

 theorem floor_code_lt {N : ℕ} (hN : 1 ≤ N) {μ a : ℝ} (hμ : 0 < μ)
    (_ha : -1 ≤ a) (ha1 : a ≤ 1) :
    ⌊(a + 1) / step N μ⌋₊ < alphabet N μ := by
  have hs := step_pos hN hμ
  have he := eta_pos hμ
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hup : (a + 1) / step N μ ≤ 20 * (N : ℝ) / eta μ := by
    unfold step
    apply (div_le_iff₀ (by positivity : 0 < eta μ / (10 * (N : ℝ)))).mpr
    field_simp
    nlinarith
  exact Nat.lt_succ_of_le (Nat.floor_mono hup)

 theorem same_floor_dist_lt {s a b : ℝ} (hs : 0 < s)
    (ha : -1 ≤ a) (hb : -1 ≤ b)
    (hcode : ⌊(a + 1) / s⌋₊ = ⌊(b + 1) / s⌋₊) : |a - b| < s := by
  have ha0 : 0 ≤ (a + 1) / s := div_nonneg (by linarith) hs.le
  have hb0 : 0 ≤ (b + 1) / s := div_nonneg (by linarith) hs.le
  have hal := Nat.floor_le ha0
  have hbl := Nat.floor_le hb0
  have hau := Nat.lt_floor_add_one ((a + 1) / s)
  have hbu := Nat.lt_floor_add_one ((b + 1) / s)
  rw [hcode] at hal hau
  have h1 : (a + 1) / s - (b + 1) / s < 1 := by linarith
  have h2 : (b + 1) / s - (a + 1) / s < 1 := by linarith
  have h1' := (mul_lt_mul_of_pos_right h1 hs)
  have h2' := (mul_lt_mul_of_pos_right h2 hs)
  have hea : ((a + 1) / s) * s = a + 1 := div_mul_cancel₀ _ (ne_of_gt hs)
  have heb : ((b + 1) / s) * s = b + 1 := div_mul_cancel₀ _ (ne_of_gt hs)
  rw [sub_mul, hea, heb, one_mul] at h1' h2'
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

 theorem exists_code_representatives {α : Type*} [Fintype α] [DecidableEq α]
    (D K : ℕ) (code : α → (Fin D → Fin K)) :
    ∃ R : Finset α, R.card ≤ K ^ D ∧ ∀ a : α, ∃ b ∈ R, code b = code a := by
  classical
  let I : Finset (Fin D → Fin K) := Finset.univ.image code
  have hsurj : (Set.univ : Set α).SurjOn code I := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨a, _, rfl⟩
    exact ⟨a, Set.mem_univ _, rfl⟩
  obtain ⟨R, _, hinj, himage⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn Set.univ I hsurj
  refine ⟨R, ?_, ?_⟩
  · calc
      R.card = (R.image code).card := (Finset.card_image_of_injOn hinj).symm
      _ = I.card := congrArg Finset.card himage
      _ ≤ Fintype.card (Fin D → Fin K) := I.card_le_univ
      _ = K ^ D := by simp
  · intro a
    have hi : code a ∈ I := Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    rw [← himage] at hi
    exact Finset.mem_image.mp hi

section Weighted
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def weightedVec (u f : V → ℝ) : EuclideanSpace ℝ V :=
  WithLp.toLp 2 (fun x => u x * f x)
omit [Fintype V] [DecidableEq V] in
@[simp] theorem weightedVec_apply (u f : V → ℝ) (x : V) : weightedVec u f x = u x * f x := rfl
omit [DecidableEq V] in
 theorem weightedVec_norm_sq (u f : V → ℝ) :
    ‖weightedVec u f‖ ^ 2 = ∑ x, (u x * f x) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

omit [DecidableEq V] in
 theorem coordinate_bound {D : ℕ} {E : Submodule ℝ (EuclideanSpace ℝ V)}
    (e : OrthonormalBasis (Fin D) ℝ E) (F : E) (hF : ‖F‖ ^ 2 ≤ 1) (i : Fin D) :
    -1 ≤ e.repr F i ∧ e.repr F i ≤ 1 := by
  have heq : (∑ j : Fin D, (e.repr F j) ^ 2) = ‖F‖ ^ 2 := by
    rw [← EuclideanSpace.real_norm_sq_eq, e.repr.norm_map]
  have hi : (e.repr F i) ^ 2 ≤ ∑ j : Fin D, (e.repr F j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  constructor <;> nlinarith

omit [DecidableEq V] in
 theorem coordinate_diff_energy {D : ℕ} {E : Submodule ℝ (EuclideanSpace ℝ V)}
    (e : OrthonormalBasis (Fin D) ℝ E) (F G : E) :
    ‖(F - G : E)‖ ^ 2 = ∑ i : Fin D, (e.repr F i - e.repr G i) ^ 2 := by
  rw [← e.repr.norm_map (F-G), EuclideanSpace.real_norm_sq_eq]
  simp only [map_sub, PiLp.sub_apply]

omit [DecidableEq V] in
 theorem same_code_pointwise {N D : ℕ} (hN : 1 ≤ N) (hDN : D ≤ N)
    {μ : ℝ} (hμ : 0 < μ) (u : V → ℝ)
    (hatom : ∀ x, 1 / (50 * (N : ℝ)) ≤ u x ^ 2)
    {E : Submodule ℝ (EuclideanSpace ℝ V)}
    (e : OrthonormalBasis (Fin D) ℝ E) (F G : E) (f g : V → ℝ)
    (hF : (F : EuclideanSpace ℝ V) = weightedVec u f)
    (hG : (G : EuclideanSpace ℝ V) = weightedVec u g)
    (hFm : ‖F‖ ^ 2 ≤ 1) (hGm : ‖G‖ ^ 2 ≤ 1)
    (hcode : ∀ i, ⌊(e.repr F i + 1) / step N μ⌋₊ =
      ⌊(e.repr G i + 1) / step N μ⌋₊) (x : V) : |f x - g x| ≤ eta μ := by
  have hs := step_pos hN hμ
  have he := eta_pos hμ
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnD : (D : ℝ) ≤ N := by exact_mod_cast hDN
  have hcoord (i : Fin D) : (e.repr F i - e.repr G i) ^ 2 ≤ step N μ ^ 2 := by
    have hh := same_floor_dist_lt hs (coordinate_bound e F hFm i).1
      (coordinate_bound e G hGm i).1 (hcode i)
    have hab := abs_nonneg (e.repr F i - e.repr G i)
    nlinarith [sq_abs (e.repr F i - e.repr G i)]
  have henergy : ‖(F-G : E)‖ ^ 2 ≤ (N : ℝ) * step N μ ^ 2 := by
    rw [coordinate_diff_energy]
    calc
      _ ≤ ∑ i : Fin D, step N μ ^ 2 := Finset.sum_le_sum fun i _ => hcoord i
      _ = (D : ℝ) * step N μ ^ 2 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hnD (sq_nonneg _)
  have hterm : (u x * (f x - g x)) ^ 2 ≤ ‖(F-G : E)‖ ^ 2 := by
    have hh : (u x * (f x-g x)) ^ 2 ≤
        ∑ y, (u y * (f y-g y)) ^ 2 :=
      Finset.single_le_sum (fun y _ => sq_nonneg (u y * (f y-g y))) (Finset.mem_univ x)
    have heq : ‖(F-G : E)‖ ^ 2 = ∑ y, (u y * (f y-g y)) ^ 2 := by
      change ‖((F : EuclideanSpace ℝ V) - (G : EuclideanSpace ℝ V))‖ ^ 2 = _
      rw [hF, hG, EuclideanSpace.real_norm_sq_eq]
      apply Finset.sum_congr rfl
      intro y _
      change (u y * f y - u y * g y) ^ 2 = _
      ring
    rw [heq]
    exact hh
  have hat := mul_le_mul_of_nonneg_right (hatom x) (sq_nonneg (f x-g x))
  have hsmall : (f x-g x) ^ 2 ≤ 50 * (N : ℝ) ^ 2 * step N μ ^ 2 := by
    have ha : (f x-g x) ^ 2 / (50 * (N : ℝ)) ≤ (N : ℝ) * step N μ ^ 2 := by
      calc
        _ = 1 / (50 * (N : ℝ)) * (f x-g x) ^ 2 := by ring
        _ ≤ _ := hat.trans (by simpa only [mul_pow] using hterm.trans henergy)
    have hb := (div_le_iff₀ (by positivity : 0 < 50 * (N : ℝ))).mp ha
    nlinarith
  have heq : 50 * (N : ℝ) ^ 2 * step N μ ^ 2 = eta μ ^ 2 / 2 := by
    unfold step
    field_simp
    ring
  rw [heq] at hsmall
  have hh : (f x-g x) ^ 2 ≤ eta μ ^ 2 := by nlinarith
  exact (sq_le_sq₀ (abs_nonneg _) he.le).mp (by simpa only [sq_abs] using hh)

omit [DecidableEq V] in
 theorem exists_indexed_coordinate_net {α : Type*} [Fintype α] [DecidableEq α]
    {N D : ℕ} (hN : 1 ≤ N) (hDN : D ≤ N) {μ : ℝ} (hμ : 0 < μ)
    (u : V → ℝ) (hatom : ∀ x, 1 / (50 * (N : ℝ)) ≤ u x ^ 2)
    {E : Submodule ℝ (EuclideanSpace ℝ V)}
    (e : OrthonormalBasis (Fin D) ℝ E) (F : α → E) (f : α → V → ℝ)
    (hF : ∀ a, (F a : EuclideanSpace ℝ V) = weightedVec u (f a))
    (hFm : ∀ a, ‖F a‖ ^ 2 ≤ 1) :
    ∃ R : Finset α, R.card ≤ alphabet N μ ^ D ∧
      ∀ a, ∃ b ∈ R, ∀ x, |f a x - f b x| ≤ eta μ := by
  classical
  let code : α → (Fin D → Fin (alphabet N μ)) := fun a i =>
    ⟨⌊(e.repr (F a) i + 1) / step N μ⌋₊,
      floor_code_lt hN hμ (coordinate_bound e (F a) (hFm a) i).1
        (coordinate_bound e (F a) (hFm a) i).2⟩
  obtain ⟨R, hR, hc⟩ := exists_code_representatives D (alphabet N μ) code
  refine ⟨R, hR, ?_⟩
  intro a
  obtain ⟨b, hb, hab⟩ := hc a
  refine ⟨b, hb, ?_⟩
  intro x
  apply same_code_pointwise hN hDN hμ u hatom e (F a) (F b) (f a) (f b)
    (hF a) (hF b) (hFm a) (hFm b) ?_ x
  intro i
  exact (congrArg Fin.val (congrFun hab i)).symm

omit [DecidableEq V] in
/-- Actual function representatives, with no supplied covering premise. -/
 theorem exists_weighted_coordinate_net {N D : ℕ} (hN : 1 ≤ N) (hDN : D ≤ N)
    {μ : ℝ} (hμ : 0 < μ) (u : V → ℝ)
    (hatom : ∀ x, 1 / (50 * (N : ℝ)) ≤ u x ^ 2)
    (E : Submodule ℝ (EuclideanSpace ℝ V)) (e : OrthonormalBasis (Fin D) ℝ E)
    (S : Finset (V → ℝ)) (hmem : ∀ g ∈ S, weightedVec u g ∈ E)
    (hnorm : ∀ g ∈ S, ∑ x, (u x * g x) ^ 2 ≤ 1) :
    ∃ C : Finset (V → ℝ), C ⊆ S ∧ C.card ≤ alphabet N μ ^ D ∧
      ∀ g ∈ S, ∃ h ∈ C, ∀ x, |g x - h x| ≤ eta μ := by
  classical
  let F : {g // g ∈ S} → E := fun g => ⟨weightedVec u g.val, hmem g.val g.property⟩
  have hn (g : {g // g ∈ S}) : ‖F g‖ ^ 2 ≤ 1 := by
    change ‖weightedVec u g.val‖ ^ 2 ≤ 1
    rw [weightedVec_norm_sq]
    exact hnorm g.val g.property
  obtain ⟨R, hR, hc⟩ := exists_indexed_coordinate_net hN hDN hμ u hatom e F
    (fun g => g.val) (fun _ => rfl) hn
  refine ⟨R.image Subtype.val, ?_, (Finset.card_image_le.trans hR), ?_⟩
  · intro g hg
    rcases Finset.mem_image.mp hg with ⟨a, _, rfl⟩
    exact a.property
  · intro g hg
    obtain ⟨b, hb, hh⟩ := hc ⟨g, hg⟩
    exact ⟨b.val, Finset.mem_image.mpr ⟨b, hb, rfl⟩, hh⟩


omit [DecidableEq V] in
                                                                         
 theorem weighted_transition_sqNorm_le (C : Erdos642.FiniteMarkov.Chain V)
    (u : V → ℝ) (hstat : ∀ y, ∑ x, u x ^ 2 * C.transition x y = u y ^ 2)
    (f : V → ℝ) :
    (∑ x, (u x * (C.transition *ᵥ f) x) ^ 2) ≤ ∑ x, (u x * f x) ^ 2 := by
  have hrow (x : V) : (C.transition *ᵥ f) x ^ 2 ≤ ∑ y, C.transition x y * f y ^ 2 := by
    have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset V)
      (r := fun y => C.transition x y * f y)
      (f := fun y => C.transition x y * f y ^ 2)
      (g := fun y => C.transition x y)
      (fun y _ => mul_nonneg (C.nonneg x y) (sq_nonneg _))
      (fun y _ => C.nonneg x y) (fun y _ => le_of_eq (by ring))
    simpa only [Matrix.mulVec, dotProduct, C.row_sum, mul_one] using hh
  calc
    _ = ∑ x, u x ^ 2 * (C.transition *ᵥ f) x ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ ∑ x, u x ^ 2 * ∑ y, C.transition x y * f y ^ 2 :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hrow x) (sq_nonneg _)
    _ = ∑ y, (∑ x, u x ^ 2 * C.transition x y) * f y ^ 2 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      simp_rw [hstat]
      apply Finset.sum_congr rfl
      intro x _
      ring

 theorem weighted_power_sqNorm_le (C : Erdos642.FiniteMarkov.Chain V)
    (u : V → ℝ) (hstat : ∀ y, ∑ x, u x ^ 2 * C.transition x y = u y ^ 2)
    (r : ℕ) (f : V → ℝ) :
    (∑ x, (u x * ((C.transition ^ r) *ᵥ f) x) ^ 2) ≤ ∑ x, (u x * f x) ^ 2 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact (weighted_transition_sqNorm_le C u hstat _).trans ih

noncomputable def projectedFunction (C : Erdos642.FiniteMarkov.Chain V)
    (u : V → ℝ) (E : Submodule ℝ (EuclideanSpace ℝ V)) (r : ℕ) (f : V → ℝ) : V → ℝ :=
  fun x => (E.orthogonalProjectionOnto (weightedVec u ((C.transition ^ r) *ᵥ f)) :
    EuclideanSpace ℝ V) x / u x

 theorem weightedVec_projectedFunction (C : Erdos642.FiniteMarkov.Chain V)
    (u : V → ℝ) (hu : ∀ x, 0 < u x)
    (E : Submodule ℝ (EuclideanSpace ℝ V)) (r : ℕ) (f : V → ℝ) :
    weightedVec u (projectedFunction C u E r f) =
      (E.orthogonalProjectionOnto (weightedVec u ((C.transition ^ r) *ᵥ f)) :
        EuclideanSpace ℝ V) := by
  apply PiLp.ext
  intro x
  change u x * (_ / u x) = _
  exact mul_div_cancel₀ _ (ne_of_gt (hu x))

 theorem projectedFunction_sqNorm_le (C : Erdos642.FiniteMarkov.Chain V)
    (u : V → ℝ) (huPos : ∀ x, 0 < u x) (hu : (∑ x, u x ^ 2) = 1)
    (hstat : ∀ y, ∑ x, u x ^ 2 * C.transition x y = u y ^ 2)
    (E : Submodule ℝ (EuclideanSpace ℝ V)) (r : ℕ) (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    (∑ x, (u x * projectedFunction C u E r f x) ^ 2) ≤ 1 := by
  have hinit : (∑ x, (u x * f x) ^ 2) ≤ 1 := by
    rw [← hu]
    apply Finset.sum_le_sum
    intro x _
    have hh : f x ^ 2 ≤ 1 := by nlinarith [(hf x).1, (hf x).2]
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg (u x))
    nlinarith
  have hp := E.norm_orthogonalProjectionOnto_apply_le (weightedVec u ((C.transition ^ r) *ᵥ f))
  have hp2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
  calc
    _ = ‖weightedVec u (projectedFunction C u E r f)‖ ^ 2 := (weightedVec_norm_sq _ _).symm
    _ = ‖(E.orthogonalProjectionOnto (weightedVec u ((C.transition ^ r) *ᵥ f)) :
        EuclideanSpace ℝ V)‖ ^ 2 := by rw [weightedVec_projectedFunction C u huPos]
    _ ≤ ‖weightedVec u ((C.transition ^ r) *ᵥ f)‖ ^ 2 := hp2
    _ = ∑ x, (u x * ((C.transition ^ r) *ᵥ f) x) ^ 2 := weightedVec_norm_sq _ _
    _ ≤ ∑ x, (u x * f x) ^ 2 := weighted_power_sqNorm_le C u hstat r f
    _ ≤ 1 := hinit

/-- Actual smoothed projections admit actual finite representatives; their unit bound is derived. -/
 theorem exists_projected_coordinate_net {N D : ℕ} (hN : 1 ≤ N) (hDN : D ≤ N)
    {μ : ℝ} (hμ : 0 < μ) (C : Erdos642.FiniteMarkov.Chain V)
    (u : V → ℝ) (huPos : ∀ x, 0 < u x) (hu : (∑ x, u x ^ 2) = 1)
    (hstat : ∀ y, ∑ x, u x ^ 2 * C.transition x y = u y ^ 2)
    (hatom : ∀ x, 1 / (50 * (N : ℝ)) ≤ u x ^ 2)
    (E : Submodule ℝ (EuclideanSpace ℝ V)) (e : OrthonormalBasis (Fin D) ℝ E)
    (r : ℕ) (F : Finset (V → ℝ)) (hf : ∀ f ∈ F, ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    ∃ R : Finset (V → ℝ), R ⊆ F.image (projectedFunction C u E r) ∧
      R.card ≤ alphabet N μ ^ D ∧
      ∀ f ∈ F, ∃ g ∈ R, ∀ x, |projectedFunction C u E r f x - g x| ≤ eta μ := by
  classical
  let S := F.image (projectedFunction C u E r)
  have hmem : ∀ g ∈ S, weightedVec u g ∈ E := by
    intro g hg
    rcases Finset.mem_image.mp hg with ⟨f, _, rfl⟩
    rw [weightedVec_projectedFunction C u huPos]
    exact (E.orthogonalProjectionOnto (weightedVec u ((C.transition ^ r) *ᵥ f))).property
  have hnorm : ∀ g ∈ S, ∑ x, (u x * g x) ^ 2 ≤ 1 := by
    intro g hg
    rcases Finset.mem_image.mp hg with ⟨f, hff, rfl⟩
    exact projectedFunction_sqNorm_le C u huPos hu hstat E r f (hf f hff)
  obtain ⟨R, hRS, hR, hc⟩ := exists_weighted_coordinate_net hN hDN hμ u hatom E e S hmem hnorm
  refine ⟨R, hRS, hR, ?_⟩
  intro f hff
  exact hc _ (Finset.mem_image.mpr ⟨f, hff, rfl⟩)

end Weighted
end Erdos642.CampaignFe72210bContinuation3.CoordinateGrid

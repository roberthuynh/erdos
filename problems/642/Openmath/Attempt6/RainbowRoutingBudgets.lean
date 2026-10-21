import Openmath.Attempt6.RoutingBudgets

   
                                                                        
                                                                           
                                                                       
                                                                     
  
namespace Erdos585.Attempt6.RainbowRoutingBudgets

noncomputable def privateCopies (a : ℝ) : ℕ := ⌈8 * a⌉₊
noncomputable def deletionScale (a : ℝ) (m : ℕ) : ℕ := ⌈2 * a * m⌉₊

theorem local_scale_ge_one (M L lambda : ℝ) (hlambda : 0 < lambda)
    (hlambdaM : lambda ≤ M) (hL : 1 ≤ L) : 1 ≤ M * L ^ 12 / lambda := by
  have hM : 0 ≤ M := (le_of_lt hlambda).trans hlambdaM
  have hp : 1 ≤ L ^ 12 := one_le_pow₀ hL
  have hh := mul_le_mul_of_nonneg_left hp hM
  apply (le_div_iff₀ hlambda).mpr
  nlinarith

theorem private_copies_bounds (a : ℝ) (ha : 1 ≤ a) :
    0 < privateCopies a ∧ 8 * a ≤ privateCopies a ∧
      (privateCopies a : ℝ) ≤ 9 * a := by
  have hp : 0 < a := by linarith
  have hlow := Nat.le_ceil (8 * a)
  have hupp := Nat.ceil_lt_add_one (by positivity : 0 ≤ 8 * a)
  refine ⟨Nat.ceil_pos.mpr (by positivity), hlow, ?_⟩
  change (⌈8 * a⌉₊ : ℝ) ≤ 9 * a
  linarith

theorem deletion_scale_bounds (a : ℝ) (ha : 1 ≤ a) (m : ℕ) (hm : 1 ≤ m) :
    0 < deletionScale a m ∧ 2 * a * m ≤ deletionScale a m ∧
      (deletionScale a m : ℝ) ≤ 4 * a * m ∧
      2 * deletionScale a m ≤ privateCopies a * m := by
  have hp : 0 < a := by linarith
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have ham : 1 ≤ a * m := by nlinarith
  have hlow := Nat.le_ceil (2 * a * (m : ℝ))
  have hupp := Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * a * (m : ℝ))
  have ht : (deletionScale a m : ℝ) ≤ 4 * a * m := by
    unfold deletionScale
    linarith
  have hq := (private_copies_bounds a ha).2.1
  have hmul := mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  have hi : (2 : ℝ) * deletionScale a m ≤ privateCopies a * (m : ℝ) := by
    nlinarith
  exact ⟨Nat.ceil_pos.mpr (by positivity), hlow, ht, by exact_mod_cast hi⟩

theorem private_volume_budget (a : ℝ) (ha : 1 ≤ a) (m r : ℕ)
    (hm : 1 ≤ m) (hmr : m ≤ r) :
    4 * deletionScale a m ≤ 2 * r * privateCopies a := by
  have ht := (deletion_scale_bounds a ha m hm).2.2.2
  calc
    4 * deletionScale a m = 2 * (2 * deletionScale a m) := by omega
    _ ≤ 2 * (privateCopies a * m) := Nat.mul_le_mul_left 2 ht
    _ ≤ 2 * (privateCopies a * r) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (privateCopies a) hmr)
    _ = 2 * r * privateCopies a := by ring

theorem hall_load_budget (a D delta : ℝ) (ha : 1 ≤ a) (hD : 0 ≤ D)
    (hdelta : 0 < delta) (hload : a * D ≤ delta / 16) :
    (privateCopies a : ℝ) * D ≤ (9 / 16 : ℝ) * delta ∧
      (privateCopies a : ℝ) * D < delta := by
  have hq := (private_copies_bounds a ha).2.2
  have hmul := mul_le_mul_of_nonneg_right hq hD
  constructor <;> nlinarith

theorem local_load_normalization (M L lambda D delta : ℝ)
    (hM : 0 < M) (hL : 0 < L) (hlambda : 0 < lambda)
    (hload : D ≤ lambda * delta / (16 * M * L ^ 12)) :
    (M * L ^ 12 / lambda) * D ≤ delta / 16 := by
  have hden : 0 < 16 * M * L ^ 12 := by positivity
  have hh := (le_div_iff₀ hden).mp hload
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hlambda).mpr
  nlinarith

theorem doubled_deleted_edge_budget (M L lambda F : ℝ) (m : ℕ)
    (hM : 0 < M) (hL : 0 < L) (hlambda : 0 < lambda)
    (hF : F ≤ 2 * M * m * L ^ 12) :
    F ≤ lambda * deletionScale (M * L ^ 12 / lambda) m := by
  have ht := Nat.le_ceil (2 * (M * L ^ 12 / lambda) * (m : ℝ))
  have hm := mul_le_mul_of_nonneg_left ht hlambda.le
  have heq : lambda * (2 * (M * L ^ 12 / lambda) * (m : ℝ)) =
      2 * M * m * L ^ 12 := by field_simp
  rw [heq] at hm
  exact hF.trans hm

theorem revised_routing_coefficient :
    (2 / 3 : ℚ) ^ (8 : ℕ) / 192 = 4 / 19683 ∧
      (1 / 10000 : ℚ) ≤ (2 / 3 : ℚ) ^ (8 : ℕ) / 192 := by norm_num

theorem leaf_pair_budget (a : ℝ) (ha : 1 ≤ a) (m r : ℕ)
    (hm : 1 ≤ m) (hmr : m ≤ r) :
    0 < 2 * deletionScale a m - 1 ∧
      2 * deletionScale a m - 1 ≤ privateCopies a * m ∧
      4 * deletionScale a m - 2 ≤ 2 * r * privateCopies a := by
  have ht := deletion_scale_bounds a ha m hm
  have hv := private_volume_budget a ha m r hm hmr
  omega

theorem union_size_budget (L matchingSize S : ℝ) (m : ℕ)
    (hsmall : matchingSize ≤ 2 * ((m - 1 : ℕ) : ℝ) * L ^ 6)
    (hunion : S ≤ matchingSize * L ^ 6) : S ≤ 2 * m * L ^ 12 := by
  have hp : 0 ≤ L ^ 6 := by positivity
  have hm : ((m - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m 1
  have hm6 := mul_le_mul_of_nonneg_right hsmall hp
  have hm12 := mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ L ^ 12)
  nlinarith

theorem integer_rank_budget (L : ℝ) (matchingSize m : ℕ)
    (hlarge : 2 * ((m - 1 : ℕ) : ℝ) * L ^ 6 < matchingSize) :
    2 * ⌊L ^ 6⌋₊ * (m - 1) < matchingSize := by
  have hf := Nat.floor_le (by positivity : 0 ≤ L ^ 6)
  have hm : 0 ≤ ((m - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_left hf (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hm)
  have hout : (2 : ℝ) * (⌊L ^ 6⌋₊ : ℝ) * ((m - 1 : ℕ) : ℝ) < matchingSize := by
    nlinarith
  exact_mod_cast hout

theorem revised_rr_identity (theta s delta Delta L : ℝ)
    (htheta : 0 < theta) (hDelta : 0 < Delta) (hL : 0 < L) :
    (((2 * theta / 3) ^ 8 * s / L ^ 60) * (theta * delta / 6)) /
      (16 * (2 * theta * Delta) * L ^ 12) =
      ((2 / 3 : ℝ) ^ 8 / 192) * (theta ^ 8 * s * delta / (Delta * L ^ 72)) := by
  field_simp
  ring

theorem revised_random_reservoir_capacity (theta s delta Delta L M : ℝ)
    (htheta : 0 < theta) (hs : 0 ≤ s) (hdelta : 0 ≤ delta)
    (hDelta : 0 < Delta) (hL : 0 < L) (hM : 0 < M)
    (hupper : M ≤ 2 * theta * Delta) :
    theta ^ 8 * s * delta / (10000 * Delta * L ^ 72) ≤
      (((2 * theta / 3) ^ 8 * s / L ^ 60) * (theta * delta / 6)) /
        (16 * M * L ^ 12) := by
  have hn : 0 ≤ ((2 * theta / 3) ^ 8 * s / L ^ 60) * (theta * delta / 6) :=
    by positivity
  have hd : 16 * M * L ^ 12 ≤ 16 * (2 * theta * Delta) * L ^ 12 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hupper (by norm_num)) (by positivity)
  have hcap := div_le_div_of_nonneg_left hn (by positivity : 0 < 16 * M * L ^ 12) hd
  rw [revised_rr_identity theta s delta Delta L htheta hDelta hL] at hcap
  have hcoeff : (1 / 10000 : ℝ) ≤ (2 / 3 : ℝ) ^ 8 / 192 := by norm_num
  have hmul := mul_le_mul_of_nonneg_right hcoeff
    (by positivity : 0 ≤ theta ^ 8 * s * delta / (Delta * L ^ 72))
  have hid : theta ^ 8 * s * delta / (10000 * Delta * L ^ 72) =
      (1 / 10000 : ℝ) * (theta ^ 8 * s * delta / (Delta * L ^ 72)) := by ring
  rw [hid]
  exact hmul.trans hcap

theorem revised_pool_capacity (rho C0 d s delta Delta L : ℝ)
    (_hrho : 0 ≤ rho) (hC0 : 0 < C0) (hd : 0 ≤ d)
    (hdelta : 0 ≤ delta) (hDelta : 0 < Delta) (hL : 0 < L)
    (hs : d / L ^ 2 ≤ s) (hratio : Delta ≤ 18 * delta) :
    rho ^ 8 * d / (180000 * C0 ^ 8 * L ^ 74) ≤
      (rho / C0) ^ 8 * s * delta / (10000 * Delta * L ^ 72) := by
  have hsd := (div_le_iff₀ (by positivity : 0 < L ^ 2)).mp hs
  have hr := mul_le_mul_of_nonneg_left hratio hd
  have hm := mul_le_mul_of_nonneg_right hsd hdelta
  have hbase : d / (18 * L ^ 2) ≤ s * delta / Delta := by
    apply (div_le_div_iff₀ (by positivity) hDelta).mpr
    nlinarith
  have hcommon := mul_le_mul_of_nonneg_left hbase
    (by positivity : 0 ≤ (rho / C0) ^ 8 / (10000 * L ^ 72))
  have heqleft : rho ^ 8 * d / (180000 * C0 ^ 8 * L ^ 74) =
      ((rho / C0) ^ 8 / (10000 * L ^ 72)) * (d / (18 * L ^ 2)) := by
    field_simp
    ring
  have heqright : (rho / C0) ^ 8 * s * delta / (10000 * Delta * L ^ 72) =
      ((rho / C0) ^ 8 / (10000 * L ^ 72)) * (s * delta / Delta) := by ring
  rw [heqleft, heqright]
  exact hcommon

theorem pool_coefficient_eventual (C0 : ℝ) :
    ∀ᶠ L : ℝ in Filter.atTop, 180000 * C0 ^ 8 ≤ L ^ 2 := by
  apply Filter.eventually_atTop.mpr
  refine ⟨max 1 (180000 * C0 ^ 8), ?_⟩
  intro L hL
  have h1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hc : 180000 * C0 ^ 8 ≤ L := (le_max_right _ _).trans hL
  nlinarith

theorem pool_capacity_simplification (rho C0 d L : ℝ)
    (_hrho : 0 ≤ rho) (hC0 : 0 < C0) (hd : 0 ≤ d) (hL : 0 < L)
    (hbudget : 180000 * C0 ^ 8 ≤ L ^ 2) :
    rho ^ 8 * d / L ^ 76 ≤ rho ^ 8 * d / (180000 * C0 ^ 8 * L ^ 74) := by
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have hh := mul_le_mul_of_nonneg_right hbudget (by positivity : 0 ≤ L ^ 74)
  calc
    180000 * C0 ^ 8 * L ^ 74 ≤ L ^ 2 * L ^ 74 := hh
    _ = L ^ 76 := by ring

theorem factor_two_local_budget (M L lambda D delta : ℝ) (m r : ℕ)
    (hlambda : 0 < lambda) (hlambdaM : lambda ≤ M) (hL : 1 ≤ L)
    (hD : 0 ≤ D) (hdelta : 0 < delta) (hm : 1 ≤ m) (hmr : m ≤ r)
    (hload : D ≤ lambda * delta / (16 * M * L ^ 12)) :
    let a := M * L ^ 12 / lambda
    0 < privateCopies a ∧
      8 * a ≤ privateCopies a ∧ (privateCopies a : ℝ) ≤ 9 * a ∧
      (privateCopies a : ℝ) * D < delta ∧
      0 < deletionScale a m ∧
      2 * deletionScale a m ≤ privateCopies a * m ∧
      4 * deletionScale a m ≤ 2 * r * privateCopies a ∧
      0 < 2 * deletionScale a m - 1 ∧
      2 * deletionScale a m - 1 ≤ privateCopies a * m ∧
      ∀ matchingSize S F : ℝ,
        matchingSize ≤ 2 * ((m - 1 : ℕ) : ℝ) * L ^ 6 →
        S ≤ matchingSize * L ^ 6 → F ≤ M * S →
        F ≤ lambda * deletionScale a m := by
  dsimp only
  let a := M * L ^ 12 / lambda
  have ha : 1 ≤ a := local_scale_ge_one M L lambda hlambda hlambdaM hL
  have hM : 0 < M := hlambda.trans_le hlambdaM
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hL
  have hq := private_copies_bounds a ha
  have ht := deletion_scale_bounds a ha m hm
  have hv := private_volume_budget a ha m r hm hmr
  have hleaf := leaf_pair_budget a ha m r hm hmr
  have hnorm : a * D ≤ delta / 16 := local_load_normalization M L lambda D delta
    hM hLp hlambda hload
  have hHall := hall_load_budget a D delta ha hD hdelta hnorm
  refine ⟨hq.1, hq.2.1, hq.2.2, hHall.2, ht.1, ht.2.2.2, hv,
    hleaf.1, hleaf.2.1, ?_⟩
  intro matchingSize S F hsmall hunion hF
  have hS := union_size_budget L matchingSize S m hsmall hunion
  have hmS := mul_le_mul_of_nonneg_left hS hM.le
  apply doubled_deleted_edge_budget M L lambda F m hM hLp hlambda
  nlinarith

end Erdos585.Attempt6.RainbowRoutingBudgets

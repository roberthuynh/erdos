import Openmath.Erdos642.Proofs.Adaptive20261018.Parameters
import Openmath.Erdos642.Proofs.CampaignFe72210bContinuation3.StrongGlobalApplicability
namespace Erdos642.Adaptive20261018.OriginalPayment
open Erdos642.CampaignFe72210bContinuation3
open Parameters

def Q : ℝ := 2 * 64 ^ 8

theorem log_eighth_eighth_certificate (x : ℝ) (hx : 1 ≤ x) :
    ∃ u : ℝ, 0 < u ∧ u ^ 8 = x ∧ (Real.log (2 * x)) ^ 8 ≤ Q * u := by
  let r : ℝ := (2 * x) ^ ((64 : ℝ)⁻¹)
  let u : ℝ := x ^ ((8 : ℝ)⁻¹)
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have h2x : 0 < 2 * x := by positivity
  have hr : 0 < r := Real.rpow_pos_of_pos h2x _
  have hu : 0 < u := Real.rpow_pos_of_pos hxpos _
  have hu8 : u ^ 8 = x :=
    Real.rpow_inv_natCast_pow hxpos.le (by norm_num : (8 : ℕ) ≠ 0)
  have hlogr : Real.log r = (64 : ℝ)⁻¹ * Real.log (2 * x) :=
    Real.log_rpow h2x _
  have hlog := Real.log_le_sub_one_of_pos hr
  have hupper : Real.log (2 * x) ≤ 64 * r := by norm_num at hlogr; linarith
  have heighth := pow_le_pow_left₀
    (Real.log_nonneg (show (1 : ℝ) ≤ 2 * x by linarith)) hupper 8
  have hr8 : r ^ 8 = (2 * x) ^ ((8 : ℝ)⁻¹) := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul h2x.le]
    norm_num
  have htwo8 : ((2 : ℝ) ^ ((8 : ℝ)⁻¹)) ^ 8 = 2 :=
    Real.rpow_inv_natCast_pow (by norm_num) (by norm_num : (8 : ℕ) ≠ 0)
  have htwo : (2 : ℝ) ^ ((8 : ℝ)⁻¹) ≤ 2 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    rw [htwo8]
    norm_num
  have hr8prod : r ^ 8 = (2 : ℝ) ^ ((8 : ℝ)⁻¹) * u := by
    rw [hr8, Real.mul_rpow (by norm_num) hxpos.le]
  refine ⟨u, hu, hu8, ?_⟩
  calc
    (Real.log (2 * x)) ^ 8 ≤ (64 * r) ^ 8 := heighth
    _ = (64 : ℝ) ^ 8 * r ^ 8 := by ring
    _ = (64 : ℝ) ^ 8 * ((2 : ℝ) ^ ((8 : ℝ)⁻¹) * u) := by rw [hr8prod]
    _ ≤ (64 : ℝ) ^ 8 * (2 * u) := by gcongr
    _ = Q * u := by dsimp [Q]; ring


theorem log_ratio_monotone (z L : ℝ) (hz : 4 ≤ Real.log z) (hzL : z ≤ L)
    (hzpos : 0 < z) : z^2 / Real.log z ≤ L^2 / Real.log L := by
  have hLpos : 0 < L := hzpos.trans_le hzL
  have hlogL : Real.log z ≤ Real.log L := Real.log_le_log hzpos hzL
  have hratio := Real.log_le_sub_one_of_pos (div_pos hLpos hzpos)
  rw [Real.log_div (ne_of_gt hLpos) (ne_of_gt hzpos)] at hratio
  have hmul := mul_le_mul_of_nonneg_right hratio hzpos.le
  have heq : (L/z-1)*z = L-z := by field_simp
  rw [heq] at hmul
  have hzL0 : 0 ≤ L-z := sub_nonneg.mpr hzL
  have hprod := mul_nonneg hzL0 (show 0 ≤ (L+z)*Real.log z-z by nlinarith)
  have hmul2 := mul_le_mul_of_nonneg_right hmul hzpos.le
  apply (div_le_div_iff₀ (by linarith : 0 < Real.log z) (by linarith : 0 < Real.log L)).mpr
  nlinarith only [hprod,hmul2]

theorem log_root_bound (L v : ℝ) (hL : 1 ≤ L) (hv : 0 < v) (hv8 : v^8=L) :
    1 ≤ v ∧ Real.log L ≤ 8*v := by
  have hv1 : 1 ≤ v := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) hv.le
    simpa only [one_pow,hv8] using hL
  have hlog := Real.log_le_sub_one_of_pos hv
  have he : Real.log L = 8*Real.log v := by rw [← hv8,Real.log_pow]; norm_num
  exact ⟨hv1, by rw [he]; linarith⟩

theorem moment_root_payment (L v d u C W : ℝ) (hv : 1 ≤ v) (hv8 : v^8=L)
    (hu : 0 < u) (hu8 : u^8=d) (hC : 1 ≤ C) (hW : 0 ≤ W) (hWC : W ≤ C)
    (hd : C*v^31 ≤ d) : W*L^7*u ≤ d^2 := by
  have hv0 : 0 ≤ v := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hd0 : 0 ≤ d := by rw [←hu8]; positivity
  have hCpow : W^8 ≤ C^15 :=
    (pow_le_pow_left₀ hW hWC 8).trans (pow_le_pow_right₀ hC (by norm_num : (8:ℕ)≤15))
  have hvpow : v^448 ≤ v^465 := pow_le_pow_right₀ hv (by norm_num)
  have hdpow : (C*v^31)^15 ≤ d^15 := pow_le_pow_left₀ (by positivity) hd 15
  have hbase : W^8*L^56 ≤ d^15 := calc
    _ = W^8*v^448 := by rw [←hv8]; ring
    _ ≤ C^15*v^465 := mul_le_mul hCpow hvpow (by positivity) (by positivity)
    _ = (C*v^31)^15 := by ring
    _ ≤ _ := hdpow
  apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (sq_nonneg d)
  calc
    (W*L^7*u)^8 = (W^8*L^56)*d := by rw [←hu8]; ring
    _ ≤ d^15*d := mul_le_mul_of_nonneg_right hbase hd0
    _ = (d^2)^8 := by ring

theorem order_root_payment (N L v d C P M : ℝ) (hv : 1 ≤ v) (hv8 : v^8=L)
    (hP : 0 < P) (hM : 1 ≤ M) (hC : P*M ≤ C) (hd : C*v^31 ≤ d)
    (hp8 : d^4 ≤ P^4*N) : M*L^7 ≤ N := by
  have hv0 : 0 ≤ v := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hC0 : 0 ≤ C := (mul_nonneg hP.le hM0).trans hC
  have hM4 : M ≤ M^4 := by simpa using pow_le_pow_right₀ hM (by norm_num : (1:ℕ)≤4)
  have hvpow : v^56 ≤ v^124 := pow_le_pow_right₀ hv (by norm_num)
  have hl : P^4*(M*L^7) ≤ d^4 := calc
    _ = P^4*(M*v^56) := by rw [←hv8]; ring
    _ ≤ P^4*(M^4*v^124) := by gcongr
    _ = (P*M)^4*v^124 := by ring
    _ ≤ C^4*v^124 := by gcongr
    _ = (C*v^31)^4 := by ring
    _ ≤ d^4 := pow_le_pow_left₀ (by positivity) hd 4
  exact (mul_le_mul_iff_right₀ (pow_pos hP 4)).mp (hl.trans hp8)

set_option maxHeartbeats 800000 in
theorem exists_uniform_applicability (c b C0 C1 : ℝ)
    (hc : 0 < c) (hb : 0 < b) (hb1 : b ≤ 1) (hC0 : 0 < C0) (hC1 : 0 < C1) :
    ∃ K : ℝ, 0 < K ∧ ∃ n0 : ℕ, 3 ≤ n0 ∧
      ∀ (n N : ℕ) (D d Λ : ℝ), n0 ≤ n → 3 ≤ N → N ≤ n → d < N →
        K * Real.log (n : ℝ)^5 / Real.log (Real.log (n : ℝ)) ≤ D →
        c*D/Real.log (n : ℝ) ≤ d →
        d ≤ 2*C0*Real.log (2*(N : ℝ))^8 →
        1 ≤ Λ → Λ ≤ C1*Real.log (2*d)^8 →
        let γ := b/Real.log (n : ℝ)^2
        let k := MomentHostParameters.k N γ
        Real.exp 4 ≤ Real.log (N : ℝ) ∧ 1 ≤ d ∧ 0 < γ ∧ γ ≤ 1 ∧
        Astar*(k : ℝ)*r N ≤ d ∧
        Astar*Λ*(k : ℝ)*Real.log (N : ℝ)^2 ≤ d^2*γ ∧
        Astar*(k : ℝ)^2*Real.log (N : ℝ) ≤ N := by
  let P := 2*C0*StrongGlobalApplicability.Q
  let T := C1*Q
  let M := 16*Astar/b^2
  let W := 4*Astar*T/b^2
  let C := 1+W+P*M
  let K := (8*C+420*Astar/b)/c
  let L0 := Real.exp (Real.exp 4)+1
  let n0 := max 3 (⌈Real.exp L0⌉₊+1)
  have hA := Astar_pos
  have hA1 : 1 ≤ Astar := one_le_pow₀ (by norm_num)
  have hP : 0 < P := mul_pos (by positivity) StrongGlobalApplicability.Q_pos
  have hT : 0 < T := by dsimp [T,Q]; positivity
  have hM : 1 ≤ M := by
    dsimp [M]
    apply (le_div_iff₀ (sq_pos_of_pos hb)).mpr
    nlinarith
  have hW : 0 < W := by dsimp [W]; positivity
  have hPM : 0 < P*M := mul_pos hP (by linarith)
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hC0 : 0 < C := by linarith
  have hWC : W ≤ C := by dsimp [C]; linarith
  have hPC : P*M ≤ C := by dsimp [C]; linarith
  have hK : 0 < K := by dsimp [K]; positivity
  have hcK : c*K = 8*C+420*Astar/b := by dsimp [K]; field_simp
  have hcK8 : 8*C ≤ c*K := by rw [hcK]; exact le_add_of_nonneg_right (by positivity)
  have hcK420 : 420*Astar/b ≤ c*K := by rw [hcK]; linarith
  refine ⟨K,hK,n0,Nat.le_max_left _ _,?_⟩
  intro n N D d Λ hn hN hNn hdN hD hextract hp8 hΛ1 hΛ
  let L := Real.log (n : ℝ)
  let z := Real.log (N : ℝ)
  let γ := b/L^2
  let k := MomentHostParameters.k N γ
  let v := L^((8:ℝ)⁻¹)
  have hnexp : Real.exp L0 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈Real.exp L0⌉₊ ≤ n from by have := (Nat.le_max_right 3 (⌈Real.exp L0⌉₊+1)).trans hn; omega))
  have hL0 : L0 ≤ L := by
    have hh := Real.log_le_log (Real.exp_pos _) hnexp
    simpa [L] using hh
  have hL : 1 ≤ L := by dsimp [L0] at hL0; linarith [Real.exp_pos (Real.exp 4)]
  have hLpos : 0 < L := by linarith
  have hLbig : Real.exp (Real.exp 4) ≤ L := by dsimp [L0] at hL0; linarith
  have hlogL : 0 < Real.log L := by
    apply Real.log_pos
    have he : 1 < Real.exp (Real.exp 4) := Real.one_lt_exp_iff.mpr (Real.exp_pos _)
    exact he.trans_le hLbig
  have hv : 0 < v := Real.rpow_pos_of_pos hLpos _
  have hv8 : v^8=L := Real.rpow_inv_natCast_pow hLpos.le (by norm_num : (8:ℕ)≠0)
  have hvbounds := log_root_bound L v hL hv hv8
  have hdlower : c*K*L^4/Real.log L ≤ d := calc
    _ = c*(K*L^5/Real.log L)/L := by field_simp
    _ ≤ c*D/L := by gcongr
    _ ≤ d := hextract
  have hdC : C*v^31 ≤ d := by
    have hnum : (C*v^31)*Real.log L ≤ c*K*L^4 := calc
      _ ≤ (C*v^31)*(8*v) := mul_le_mul_of_nonneg_left hvbounds.2 (by positivity)
      _ = (8*C)*L^4 := by rw [←hv8]; ring
      _ ≤ c*K*L^4 := mul_le_mul_of_nonneg_right hcK8 (by positivity)
    exact ((le_div_iff₀ hlogL).mpr hnum).trans hdlower
  have hdL : L ≤ d := calc
    _ = v^8 := hv8.symm
    _ ≤ v^31 := pow_le_pow_right₀ hvbounds.1 (by norm_num)
    _ ≤ C*v^31 := le_mul_of_one_le_left (by positivity) hC
    _ ≤ d := hdC
  have hd1 : 1 ≤ d := hL.trans hdL
  have hdpos : 0 < d := by linarith
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0<N by omega)
  have hzbig : Real.exp 4 ≤ z := by
    apply (Real.le_log_iff_exp_le hNpos).mpr
    exact hLbig.trans (hdL.trans hdN.le)
  have hzpos : 0 < z := (Real.exp_pos _).trans_le hzbig
  have hzL : z ≤ L := Real.log_le_log hNpos (by exact_mod_cast hNn)
  have hγ : 0 < γ := div_pos hb (sq_pos_of_pos hLpos)
  have hγ1 : γ ≤ 1 := by dsimp [γ]; apply (div_le_iff₀ (sq_pos_of_pos hLpos)).mpr; nlinarith
  have hz1 : 1 ≤ z := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<4)).le.trans hzbig
  have ha : 1 ≤ L^2*z/b := by
    apply (le_div_iff₀ hb).mpr
    have hh := mul_le_mul_of_nonneg_left hz1 (sq_nonneg L)
    nlinarith
  have hdiv : z/γ = L^2*z/b := by dsimp [γ]; field_simp
  have hk : (k : ℝ) ≤ 4*(L^2*z/b) := by
    have hh := OldGlobalApplicability.ceil_block_le (L^2*z/b) ha
    change (⌈(2 : ℝ)+z/γ⌉₊ : ℝ) ≤ 4*(L^2*z/b)
    rw [hdiv]
    exact hh
  have hr := r_le_ratio N hzbig
  have hratio := log_ratio_monotone z L (loglog_ge_four hzbig) hzL hzpos
  have hdegree : Astar*(k : ℝ)*r N ≤ d := calc
    _ ≤ Astar*(4*(L^2*z/b))*(105*z/Real.log z) := by gcongr
    _ = (420*Astar/b)*L^2*(z^2/Real.log z) := by ring
    _ ≤ (420*Astar/b)*L^2*(L^2/Real.log L) := by gcongr
    _ = (420*Astar/b)*L^4/Real.log L := by ring
    _ ≤ c*K*L^4/Real.log L := by gcongr
    _ ≤ d := hdlower
  obtain ⟨u,hu,hu8,hlogd⟩ := log_eighth_eighth_certificate d hd1
  have hΛu : Λ ≤ T*u := calc
    _ ≤ C1*Real.log (2*d)^8 := hΛ
    _ ≤ C1*(Q*u) := mul_le_mul_of_nonneg_left hlogd (by linarith)
    _ = _ := by dsimp [T]; ring
  have hmomentRoot := moment_root_payment L v d u C W hvbounds.1 hv8 hu hu8 hC hW.le hWC hdC
  have hp8order : d^4 ≤ P^4*(N : ℝ) :=
    StrongGlobalApplicability.density_fourth_order (N : ℝ) d C0 (by exact_mod_cast (show 1≤N by omega)) hdpos.le (by assumption) hp8
  have horderRoot := order_root_payment (N : ℝ) L v d C P M hvbounds.1 hv8 hP hM hPC hdC hp8order
  have hmoment : Astar*Λ*(k : ℝ)*z^2 ≤ d^2*γ := by
    apply (div_le_iff₀ hγ).mp
    calc
      _ ≤ Astar*(T*u)*(4*(L^2*z/b))*z^2/γ := by gcongr
      _ = W*u*L^4*z^3 := by dsimp [W,γ]; field_simp
      _ ≤ W*u*L^4*L^3 := by gcongr
      _ = W*L^7*u := by ring
      _ ≤ _ := hmomentRoot
  have horder : Astar*(k : ℝ)^2*z ≤ (N : ℝ) := calc
    _ ≤ Astar*(4*(L^2*z/b))^2*z := by gcongr
    _ = M*L^4*z^3 := by dsimp [M]; field_simp <;> ring
    _ ≤ M*L^4*L^3 := by gcongr
    _ = M*L^7 := by ring
    _ ≤ _ := horderRoot
  exact ⟨hzbig,hd1,hγ,hγ1,hdegree,hmoment,horder⟩

theorem exists_uniform_host_applicability (c b C0 C1 : ℝ)
    (hc : 0 < c) (hb : 0 < b) (hb1 : b ≤ 1) (hC0 : 0 < C0) (hC1 : 0 < C1) :
    ∃ K : ℝ, 0 < K ∧ ∃ n0 : ℕ, 3 ≤ n0 ∧
      ∀ (n N : ℕ) (D : ℝ) (d : ℕ) (Λ : ℝ), n0 ≤ n → 3 ≤ N → N ≤ n → d < N →
        K * Real.log (n : ℝ)^5 / Real.log (Real.log (n : ℝ)) ≤ D →
        c*D/Real.log (n : ℝ) ≤ d →
        (d : ℝ) ≤ 2*C0*Real.log (2*(N : ℝ))^8 →
        1 ≤ Λ → Λ ≤ C1*Real.log (2*(d : ℝ))^8 →
        Hstar N d (b/Real.log (n : ℝ)^2) Λ := by
  obtain ⟨K,hK,n0,hn0,h⟩ := exists_uniform_applicability c b C0 C1 hc hb hb1 hC0 hC1
  refine ⟨K,hK,n0,hn0,?_⟩
  intro n N D d Λ hn hN hNn hdN hD hex hp8 hΛ1 hΛ
  have hh := h n N D d Λ hn hN hNn (by exact_mod_cast hdN) hD hex hp8 hΛ1 hΛ
  exact ⟨hN,hh.1,hh.2.2.1,hh.2.2.2.1,hΛ1,hh.2.2.2.2.1,hh.2.2.2.2.2.2,hh.2.2.2.2.2.1⟩

end Erdos642.Adaptive20261018.OriginalPayment

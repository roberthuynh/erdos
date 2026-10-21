import Openmath.Erdos642.Proofs.Joint20261019.Parameters
import Openmath.Erdos642.Proofs.Adaptive20261018.OriginalPayment

namespace Erdos642.Joint20261019.OriginalPayment
open Erdos642.CampaignFe72210bContinuation3
open Parameters

theorem moment_payment (L d u C W : ℝ) (hL : 1 ≤ L)
    (hu : 0 < u) (hu8 : u^8=d) (hC : 1 ≤ C) (hW : 0 ≤ W) (hWC : W ≤ C)
    (hd : C*L^3 ≤ d) : W*L^5*u ≤ d^2 := by
  have hCpow : W^8 ≤ C^15 :=
    (pow_le_pow_left₀ hW hWC 8).trans (pow_le_pow_right₀ hC (by norm_num))
  have hLpow : L^40 ≤ L^45 := pow_le_pow_right₀ hL (by norm_num)
  have hbase : W^8*L^40 ≤ d^15 := calc
    _ ≤ C^15*L^45 := mul_le_mul hCpow hLpow (by positivity) (by positivity)
    _ = (C*L^3)^15 := by ring
    _ ≤ d^15 := pow_le_pow_left₀ (by positivity) hd 15
  have hd0 : 0 ≤ d := by rw [←hu8]; positivity
  apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (sq_nonneg d)
  calc
    (W*L^5*u)^8 = (W^8*L^40)*d := by rw [←hu8]; ring
    _ ≤ d^15*d := mul_le_mul_of_nonneg_right hbase hd0
    _ = (d^2)^8 := by ring

theorem order_payment (N L d C P M : ℝ) (hL : 1 ≤ L)
    (hP : 0 < P) (hM : 1 ≤ M) (hC : P*M ≤ C) (hd : C*L^3 ≤ d)
    (hp8 : d^4 ≤ P^4*N) : M*L^7 ≤ N := by
  have hM0 : 0 ≤ M := by linarith
  have hC0 : 0 ≤ C := (mul_nonneg hP.le hM0).trans hC
  have hM4 : M ≤ M^4 := by simpa using pow_le_pow_right₀ hM (by norm_num : (1:ℕ)≤4)
  have hLpow : L^7 ≤ L^12 := pow_le_pow_right₀ hL (by norm_num)
  have hl : P^4*(M*L^7) ≤ d^4 := calc
    _ ≤ P^4*(M^4*L^12) := by gcongr
    _ = (P*M)^4*L^12 := by ring
    _ ≤ C^4*L^12 := by gcongr
    _ = (C*L^3)^4 := by ring
    _ ≤ d^4 := pow_le_pow_left₀ (by positivity) hd 4
  exact (mul_le_mul_iff_right₀ (pow_pos hP 4)).mp (hl.trans hp8)

set_option maxHeartbeats 800000 in
theorem exists_uniform_applicability (c b C0 C1 : ℝ)
    (hc : 0 < c) (hb : 0 < b) (hb1 : b ≤ 1) (hC0 : 0 < C0) (hC1 : 0 < C1) :
    ∃ K : ℝ, 0 < K ∧ ∃ n0 : ℕ, 3 ≤ n0 ∧
      ∀ (n N : ℕ) (D d Λ : ℝ), n0 ≤ n → 3 ≤ N → N ≤ n → d < N →
        K * Real.log (n : ℝ)^4 ≤ D → c*D/Real.log (n : ℝ) ≤ d →
        d ≤ 2*C0*Real.log (2*(N : ℝ))^8 →
        1 ≤ Λ → Λ ≤ C1*Real.log (2*d)^8 →
        let γ := b/Real.log (n : ℝ)^2
        let k := MomentHostParameters.k N γ
        Real.exp 4 ≤ Real.log (N : ℝ) ∧ 1 ≤ d ∧ 0 < γ ∧ γ ≤ 1 ∧
        Anew*(k : ℝ) ≤ d ∧ Anew*Λ*(k : ℝ) ≤ d^2*γ ∧
        Anew*(k : ℝ)^2*Real.log (N : ℝ) ≤ N := by
  let P := 2*C0*StrongGlobalApplicability.Q
  let T := C1*Adaptive20261018.OriginalPayment.Q
  let M := 16*Anew/b^2
  let W := 4*Anew*T/b^2
  let C := 1+W+P*M+4*Anew/b
  let K := C/c
  let L0 := Real.exp (Real.exp 4)+1
  let n0 := max 3 (⌈Real.exp L0⌉₊+1)
  have hA := Anew_pos
  have hA1 : 1 ≤ Anew := one_le_pow₀ (by norm_num)
  have hP : 0 < P := mul_pos (by positivity) StrongGlobalApplicability.Q_pos
  have hT : 0 < T := by dsimp [T,Adaptive20261018.OriginalPayment.Q]; positivity
  have hM : 1 ≤ M := by
    dsimp [M]
    apply (le_div_iff₀ (sq_pos_of_pos hb)).mpr
    nlinarith
  have hW : 0 < W := by dsimp [W]; positivity
  have hPM : 0 < P*M := mul_pos hP (by linarith)
  have hterm : 0 < 4*Anew/b := by positivity
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hC0 : 0 < C := by linarith
  have hWC : W ≤ C := by dsimp [C]; linarith
  have hPC : P*M ≤ C := by dsimp [C]; linarith
  have hAC : 4*Anew/b ≤ C := by dsimp [C]; linarith
  have hK : 0 < K := by dsimp [K]; positivity
  have hcK : c*K = C := by dsimp [K]; field_simp
  refine ⟨K,hK,n0,Nat.le_max_left _ _,?_⟩
  intro n N D d Λ hn hN hNn hdN hD hextract hp8 hΛ1 hΛ
  let L := Real.log (n : ℝ)
  let z := Real.log (N : ℝ)
  let γ := b/L^2
  let k := MomentHostParameters.k N γ
  have hnexp : Real.exp L0 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈Real.exp L0⌉₊ ≤ n from by
      have := (Nat.le_max_right 3 (⌈Real.exp L0⌉₊+1)).trans hn; omega))
  have hL0 : L0 ≤ L := by
    have hh := Real.log_le_log (Real.exp_pos _) hnexp
    simpa [L] using hh
  have hL : 1 ≤ L := by dsimp [L0] at hL0; linarith [Real.exp_pos (Real.exp 4)]
  have hLpos : 0 < L := by linarith
  have hLbig : Real.exp (Real.exp 4) ≤ L := by dsimp [L0] at hL0; linarith
  have hdC : C*L^3 ≤ d := calc
    _ = c*(K*L^4)/L := by rw [←hcK]; field_simp
    _ ≤ c*D/L := by gcongr
    _ ≤ d := hextract
  have hdL : L ≤ d := calc
    _ ≤ L^3 := by simpa using pow_le_pow_right₀ hL (by norm_num : (1:ℕ)≤3)
    _ ≤ C*L^3 := le_mul_of_one_le_left (by positivity) hC
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
  have hγ1 : γ ≤ 1 := by
    dsimp [γ]; apply (div_le_iff₀ (sq_pos_of_pos hLpos)).mpr; nlinarith
  have hz1 : 1 ≤ z := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<4)).le.trans hzbig
  have ha : 1 ≤ L^2*z/b := by
    apply (le_div_iff₀ hb).mpr
    have hh := mul_le_mul_of_nonneg_left hz1 (sq_nonneg L)
    nlinarith
  have hdiv : z/γ = L^2*z/b := by dsimp [γ]; field_simp
  have hk : (k : ℝ) ≤ 4*(L^2*z/b) := by
    have hh := OldGlobalApplicability.ceil_block_le (L^2*z/b) ha
    change (⌈(2 : ℝ)+z/γ⌉₊ : ℝ) ≤ 4*(L^2*z/b)
    rw [hdiv]; exact hh
  have hdegree : Anew*(k : ℝ) ≤ d := calc
    _ ≤ Anew*(4*(L^2*z/b)) := by gcongr
    _ ≤ Anew*(4*(L^2*L/b)) := by gcongr
    _ = (4*Anew/b)*L^3 := by ring
    _ ≤ C*L^3 := by gcongr
    _ ≤ d := hdC
  obtain ⟨u,hu,hu8,hlogd⟩ := Adaptive20261018.OriginalPayment.log_eighth_eighth_certificate d hd1
  have hΛu : Λ ≤ T*u := calc
    _ ≤ C1*Real.log (2*d)^8 := hΛ
    _ ≤ C1*(Adaptive20261018.OriginalPayment.Q*u) := mul_le_mul_of_nonneg_left hlogd hC1.le
    _ = _ := by dsimp [T]; ring
  have hmroot := moment_payment L d u C W hL hu hu8 hC hW.le hWC hdC
  have hp8order : d^4 ≤ P^4*(N : ℝ) :=
    StrongGlobalApplicability.density_fourth_order (N : ℝ) d C0
      (by exact_mod_cast (show 1≤N by omega)) hdpos.le (by assumption) hp8
  have horoot := order_payment (N : ℝ) L d C P M hL hP hM hPC hdC hp8order
  have hmoment : Anew*Λ*(k : ℝ) ≤ d^2*γ := by
    apply (div_le_iff₀ hγ).mp
    calc
      _ ≤ Anew*(T*u)*(4*(L^2*z/b))/γ := by gcongr
      _ = W*u*L^4*z := by dsimp [W,γ]; field_simp
      _ ≤ W*u*L^4*L := by gcongr
      _ = W*L^5*u := by ring
      _ ≤ _ := hmroot
  have horder : Anew*(k : ℝ)^2*z ≤ (N : ℝ) := calc
    _ ≤ Anew*(4*(L^2*z/b))^2*z := by gcongr
    _ = M*L^4*z^3 := by dsimp [M]; field_simp <;> ring
    _ ≤ M*L^4*L^3 := by gcongr
    _ = M*L^7 := by ring
    _ ≤ _ := horoot
  exact ⟨hzbig,hd1,hγ,hγ1,hdegree,hmoment,horder⟩

theorem exists_uniform_host_applicability (c b C0 C1 : ℝ)
    (hc : 0 < c) (hb : 0 < b) (hb1 : b ≤ 1) (hC0 : 0 < C0) (hC1 : 0 < C1) :
    ∃ K : ℝ, 0 < K ∧ ∃ n0 : ℕ, 3 ≤ n0 ∧
      ∀ (n N : ℕ) (D : ℝ) (d : ℕ) (Λ : ℝ), n0 ≤ n → 3 ≤ N → N ≤ n → d < N →
        K * Real.log (n : ℝ)^4 ≤ D → c*D/Real.log (n : ℝ) ≤ d →
        (d : ℝ) ≤ 2*C0*Real.log (2*(N : ℝ))^8 →
        1 ≤ Λ → Λ ≤ C1*Real.log (2*(d : ℝ))^8 →
        Hnew N d (b/Real.log (n : ℝ)^2) Λ := by
  obtain ⟨K,hK,n0,hn0,h⟩ := exists_uniform_applicability c b C0 C1 hc hb hb1 hC0 hC1
  refine ⟨K,hK,n0,hn0,?_⟩
  intro n N D d Λ hn hN hNn hdN hD hex hp8 hΛ1 hΛ
  have hh := h n N D d Λ hn hN hNn (by exact_mod_cast hdN) hD hex hp8 hΛ1 hΛ
  exact ⟨hN,hh.1,hh.2.2.1,hh.2.2.2.1,hΛ1,hh.2.2.2.2.1,hh.2.2.2.2.2.2,hh.2.2.2.2.2.1⟩

end Erdos642.Joint20261019.OriginalPayment

import Mathlib
import Openmath.Erdos643R3.G1Check
set_option autoImplicit false
namespace Erdos643R3.G1Check2
open Erdos643R3.Pw2312 Erdos643R3.PwCheck

/-- Five violating Case III classes; mode zero has no restriction. -/
def VClass2 (k : ℕ) (π : Profile) : Prop :=
  match k with
  | 1 => 2 ≤ π.f2 + π.g2 + π.t2
  | 2 => π.f2 + π.g2 + π.t2 = 1 ∧ 1 ≤ π.g0
  | 3 => 2 ≤ π.f2 + π.g2 + π.t2
  | 4 => π.f2 + π.g2 + π.t2 = 1 ∧ 1 ≤ π.f1
  | _ => True

def reject2 (k t2 : ℕ) (b : Box2) : Bool :=
  match k with
  | 1 => decide (b.f2h + b.g2h + t2 < 2)
  | 2 => decide (1 < b.f2l + b.g2l + t2 ∨ b.f2h + b.g2h + t2 < 1 ∨ b.g0h < 1)
  | 3 => decide (b.f2h + b.g2h + t2 < 2)
  | 4 => decide (1 < b.f2l + b.g2l + t2 ∨ b.f2h + b.g2h + t2 < 1 ∨ b.f1h < 1)
  | _ => false

theorem reject2_sound {b : Box2} {π : Profile} (hb : b.mem π) (k : ℕ)
    (h : reject2 k π.t2 b = true) : ¬ VClass2 k π := by
  obtain ⟨h0,h1,h2,h3⟩ := hb
  rcases k with _|_|_|_|_|k <;> simp [reject2,VClass2] at h ⊢ <;> omega

/-- C2g leaf target is W ≥ 1, hence Φ ≥ 2. -/
def ok2 (k t0 t1 t2 : ℕ) (b : Box2) : Bool :=
  infeas2N t0 t1 t2 b || reject2 k t2 b ||
    (decide (1200000 ≤ lb2N t0 t1 t2 b) &&
    decide (1200000 + kdC (b.g0h + t0) t0 + kdC (b.f1h + t1) t1 ≤ lb2N t0 t1 t2 b))

theorem ok2_sound {b : Box2} {π : Profile} (hb : b.mem π) (k : ℕ)
    (h : ok2 k π.t0 π.t1 π.t2 b = true) (hf0 : 23 ≤ π.f0) (hg1 : 23 ≤ π.g1)
    (hF : Feas π) (hv : VClass2 k π) : 2 ≤ Phi π := by
  simp only [ok2,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with (h|h)|⟨-,h⟩
  · exfalso
    obtain ⟨h1,h2,h4,h5⟩ := hb
    simp only [infeas2N,Bool.or_eq_true] at h
    rcases h with h|h
    · exact mism_sound h2 h5 h hF.2.1
    · exact mism_sound h4 h1 h hF.2.2
  · exact absurd hv (reject2_sound hb k h)
  · have hl := lb2N_le hb
    obtain ⟨h1,h2,-,-⟩ := hb
    have hK := K_ge π (by omega) (by omega)
    have kA := kappa_anti_u π.f0 π.t0 (show π.g0 + π.t0 ≤ b.g0h + π.t0 by omega)
    have kB := kappa_anti_u π.g1 π.t1 (show π.f1 + π.t1 ≤ b.f1h + π.t1 by omega)
    have dA := kdC_sound (b.g0h + π.t0) π.t0 hf0
    have dB := kdC_sound (b.f1h + π.t1) π.t1 hg1
    have hc : (1200000 : ℚ) + (kdC (b.g0h + π.t0) π.t0 : ℚ) + (kdC (b.f1h + π.t1) π.t1 : ℚ) ≤
        (lb2N π.t0 π.t1 π.t2 b : ℚ) := by exact_mod_cast h
    rw [Phi_eq_K_add_G]
    linarith

def bb2 (k t0 t1 t2 : ℕ) : ℕ → Box2 → Bool
  | 0,b => ok2 k t0 t1 t2 b
  | n+1,b => ok2 k t0 t1 t2 b || (bb2 k t0 t1 t2 n (low2 b (pick2 b)) &&
    bb2 k t0 t1 t2 n (high2 b (pick2 b)))

theorem bb2_sound (n : ℕ) : ∀ (b : Box2) (π : Profile) (k : ℕ),
    bb2 k π.t0 π.t1 π.t2 n b = true → b.mem π → 23 ≤ π.f0 → 23 ≤ π.g1 → Feas π →
    VClass2 k π → 2 ≤ Phi π := by
  induction n with
  | zero => intro b π k h hb hf hg hF hv; exact ok2_sound hb k h hf hg hF hv
  | succ n ih =>
    intro b π k h hb hf hg hF hv
    simp only [bb2,Bool.or_eq_true,Bool.and_eq_true] at h
    rcases h with h|⟨h1,h2⟩
    · exact ok2_sound hb k h hf hg hF hv
    · rcases split2_mem hb (pick2 b) with hm|hm
      · exact ih _ π k h1 hm hf hg hF hv
      · exact ih _ π k h2 hm hf hg hF hv

def runT2 (t0 t1 t2 : ℕ) : Bool := if 2 ≤ t0+t1+t2 then bb2 0 t0 t1 t2 100 full2 else true
def allT2 : Bool := (List.range 12).all fun t0 => (List.range (12-t0)).all fun t1 =>
  (List.range (12-t0-t1)).all fun t2 => runT2 t0 t1 t2

def runV2 (k : ℕ) : Bool :=
  match k with
  | 1 => bb2 1 1 0 0 100 full2
  | 2 => bb2 2 1 0 0 100 full2
  | 3 => bb2 3 0 1 0 100 full2
  | 4 => bb2 4 0 1 0 100 full2
  | _ => bb2 5 0 0 1 100 full2

theorem full2_mem (π : Profile) (hb : π.g0 ≤ 92 ∧ π.f1 ≤ 92 ∧ π.f2 ≤ 92 ∧ π.g2 ≤ 92) : full2.mem π := by
  obtain ⟨h0,h1,h2,h3⟩ := hb
  exact ⟨⟨Nat.zero_le _,h0⟩,⟨Nat.zero_le _,h1⟩,⟨Nat.zero_le _,h2⟩,⟨Nat.zero_le _,h3⟩⟩

theorem caseIII_a (hc : allT2 = true) (π : Profile) (hf : Feas π)
    (ht : 2 ≤ π.t0+π.t1+π.t2) (hu : π.t0+π.t1+π.t2 ≤ 11)
    (h0 : 23 ≤ π.f0) (h1 : 23 ≤ π.g1) (hb : full2.mem π) : 2 ≤ Phi π := by
  simp only [allT2,List.all_eq_true,List.mem_range] at hc
  have h := hc π.t0 (by omega) π.t1 (by omega) π.t2 (by omega)
  simp only [runT2,if_pos ht] at h
  exact bb2_sound 100 full2 π 0 h hb h0 h1 hf trivial
end Erdos643R3.G1Check2

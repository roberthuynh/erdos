import Mathlib
import Openmath.Erdos643R3.PwCheck

set_option autoImplicit false
namespace Erdos643R3.G1Check
open Erdos643R3.Pw2312 Erdos643R3.PwCheck

/-- Noncompliant classes V1–V4 with the unique type-2 slot in group zero. -/
def VClass (k : ℕ) (π : Profile) : Prop :=
  match k with
  | 1 => 2 ≤ π.f1 + π.g1 + π.t1 ∧ 2 ≤ π.f2 + π.g2 + π.t2
  | 2 => π.f1 + π.g1 + π.t1 = 1 ∧ π.f2 + π.g2 + π.t2 = 1
  | 3 => π.f2 + π.g2 + π.t2 = 1 ∧ 1 ≤ π.g0
  | 4 => π.f1 + π.g1 + π.t1 = 1 ∧ 1 ≤ π.f0
  | _ => True

/-- Interval rejection for V1–V4. Mode zero imposes no extra restriction. -/
def reject (k _t0 t1 t2 : ℕ) (b : Box) : Bool :=
  match k with
  | 1 => decide (b.f1h + b.g1h + t1 < 2 ∨ b.f2h + b.g2h + t2 < 2)
  | 2 => decide (1 < b.f1l + b.g1l + t1 ∨ b.f1h + b.g1h + t1 < 1 ∨
      1 < b.f2l + b.g2l + t2 ∨ b.f2h + b.g2h + t2 < 1)
  | 3 => decide (1 < b.f2l + b.g2l + t2 ∨ b.f2h + b.g2h + t2 < 1 ∨ b.g0h < 1)
  | 4 => decide (1 < b.f1l + b.g1l + t1 ∨ b.f1h + b.g1h + t1 < 1 ∨ b.f0h < 1)
  | _ => false

theorem reject_sound {b : Box} {π : Profile} (hb : b.mem π) (k : ℕ)
    (h : reject k π.t0 π.t1 π.t2 b = true) : ¬ VClass k π := by
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := hb
  rcases k with _ | _ | _ | _ | _ | k <;> simp [reject, VClass] at h ⊢ <;> omega

/-- The lower corner, used only when the box is a singleton. -/
def corner (t0 t1 t2 : ℕ) (b : Box) : Profile :=
  ⟨b.f0l,b.g0l,t0,b.f1l,b.g1l,t1,b.f2l,b.g2l,t2⟩
def point (b : Box) : Prop := b.f0l = b.f0h ∧ b.g0l = b.g0h ∧ b.f1l = b.f1h ∧
  b.g1l = b.g1h ∧ b.f2l = b.f2h ∧ b.g2l = b.g2h
instance (b : Box) : Decidable (point b) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

theorem corner_eq {b : Box} {π : Profile} (hb : b.mem π) (hp : point b) :
    corner π.t0 π.t1 π.t2 b = π := by
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := hb
  obtain ⟨p0,p1,p2,p3,p4,p5⟩ := hp
  have e0 : b.f0l = π.f0 := by omega
  have e1 : b.g0l = π.g0 := by omega
  have e2 : b.f1l = π.f1 := by omega
  have e3 : b.g1l = π.g1 := by omega
  have e4 : b.f2l = π.f2 := by omega
  have e5 : b.g2l = π.g2 := by omega
  simp only [corner,e0,e1,e2,e3,e4,e5]

def exactOK (t0 t1 t2 : ℕ) (b : Box) : Bool :=
  decide (point b) && decide (2 ≤ Phi (corner t0 t1 t2 b))

theorem exactOK_sound {b : Box} {π : Profile} (hb : b.mem π)
    (h : exactOK π.t0 π.t1 π.t2 b = true) : 2 ≤ Phi π := by
  simp only [exactOK,Bool.and_eq_true,decide_eq_true_eq] at h
  rw [corner_eq hb h.1] at h
  exact h.2

/-- Target 2 with exact singleton fallback, preserving equality profiles. -/
def ok (k t0 t1 t2 : ℕ) (b : Box) : Bool :=
  infeasN t0 t1 t2 b || allBigN b || reject k t0 t1 t2 b ||
    decide (2400000 ≤ lbN t0 t1 t2 b) || exactOK t0 t1 t2 b

theorem ok_sound {b : Box} {π : Profile} (hb : b.mem π) (k : ℕ)
    (h : ok k π.t0 π.t1 π.t2 b = true) (hF : Feas π)
    (hnb : ¬ (Big0 π ∨ Big1 π ∨ Big2 π)) (hv : VClass k π) : 2 ≤ Phi π := by
  simp only [ok,Bool.or_eq_true,decide_eq_true_eq] at h
  rcases h with (((h|h)|h)|h)|h
  · exact absurd hF (infeasN_sound hb h)
  · exact absurd (allBigN_sound hb h) hnb
  · exact absurd hv (reject_sound hb k h)
  · have hl := lbN_le hb
    have hc : (2400000 : ℚ) ≤ (lbN π.t0 π.t1 π.t2 b : ℚ) := by exact_mod_cast h
    linarith
  · exact exactOK_sound hb h

def bb (k t0 t1 t2 : ℕ) : ℕ → Box → Bool
  | 0,b => ok k t0 t1 t2 b
  | n+1,b => ok k t0 t1 t2 b || (bb k t0 t1 t2 n (lowHalf b (pick b)) &&
    bb k t0 t1 t2 n (highHalf b (pick b)))

theorem bb_sound (n : ℕ) : ∀ (b : Box) (π : Profile) (k : ℕ),
    bb k π.t0 π.t1 π.t2 n b = true → b.mem π → Feas π →
    ¬ (Big0 π ∨ Big1 π ∨ Big2 π) → VClass k π → 2 ≤ Phi π := by
  induction n with
  | zero => intro b π k h hb hf hn hv; exact ok_sound hb k h hf hn hv
  | succ n ih =>
    intro b π k h hb hf hn hv
    simp only [bb,Bool.or_eq_true,Bool.and_eq_true] at h
    rcases h with h|⟨h1,h2⟩
    · exact ok_sound hb k h hf hn hv
    · rcases split_mem hb (pick b) with hm|hm
      · exact ih _ π k h1 hm hf hn hv
      · exact ih _ π k h2 hm hf hn hv

def runT (t0 t1 t2 : ℕ) : Bool := if 2 ≤ t0+t1+t2 then bb 0 t0 t1 t2 100 full else true
def allT : Bool := (List.range 12).all fun t0 => (List.range (12-t0)).all fun t1 =>
  (List.range (12-t0-t1)).all fun t2 => runT t0 t1 t2

def runV (k : ℕ) : Bool := bb k 1 0 0 100 full

theorem full_mem (π : Profile)
    (h : π.f0 ≤ 92 ∧ π.g0 ≤ 92 ∧ π.f1 ≤ 92 ∧ π.g1 ≤ 92 ∧ π.f2 ≤ 92 ∧ π.g2 ≤ 92) : full.mem π := by
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := h
  exact ⟨⟨Nat.zero_le _,h0⟩,⟨Nat.zero_le _,h1⟩,⟨Nat.zero_le _,h2⟩,
    ⟨Nat.zero_le _,h3⟩,⟨Nat.zero_le _,h4⟩,⟨Nat.zero_le _,h5⟩⟩

theorem caseII_a (hc : allT = true) (π : Profile) (hf : Feas π)
    (ht : 2 ≤ π.t0+π.t1+π.t2) (hu : π.t0+π.t1+π.t2 ≤ 11)
    (hb : full.mem π) (hn : ¬ (Big0 π ∨ Big1 π ∨ Big2 π)) : 2 ≤ Phi π := by
  simp only [allT,List.all_eq_true,List.mem_range] at hc
  have h := hc π.t0 (by omega) π.t1 (by omega) π.t2 (by omega)
  simp only [runT,if_pos ht] at h
  exact bb_sound 100 full π 0 h hb hf hn trivial

theorem caseII_v (k : ℕ) (hc : runV k = true) (π : Profile) (hf : Feas π)
    (h0 : π.t0=1) (h1 : π.t1=0) (h2 : π.t2=0)
    (hb : full.mem π) (hn : ¬ (Big0 π ∨ Big1 π ∨ Big2 π)) (hv : VClass k π) : 2 ≤ Phi π := by
  have h : bb k π.t0 π.t1 π.t2 100 full = true := by simpa only [runV,h0,h1,h2] using hc
  exact bb_sound 100 full π k h hb hf hn hv

end Erdos643R3.G1Check

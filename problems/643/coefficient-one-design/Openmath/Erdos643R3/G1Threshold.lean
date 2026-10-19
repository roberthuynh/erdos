import Mathlib
import Openmath.Erdos643R3.G1C1
import Openmath.Erdos643R3.G1C2

set_option autoImplicit false
namespace Erdos643R3.G1Threshold
open Erdos643R3.Pw2312 Erdos643R3.PwCheck

/-- The G1 pattern when the unique type-2 slot is in group zero. -/
def Compliant0 (π : Profile) : Prop :=
  ((π.f1+π.g1+π.t1=1) ↔ ¬ (π.f2+π.g2+π.t2=1)) ∧
  (π.f2+π.g2+π.t2=1 → π.g0=0) ∧ (π.f1+π.g1+π.t1=1 → π.f0=0)

/-- Cyclic form of the G1 pattern, used on profiles with exactly one type-2 slot. -/
def Compliant (π : Profile) : Prop :=
  (π.t0=1 → Compliant0 π) ∧ (π.t1=1 → Compliant0 (rot π)) ∧
    (π.t2=1 → Compliant0 (rot (rot π)))

theorem compliant_rot (π : Profile) : Compliant (rot π) ↔ Compliant π := by
  simp only [Compliant,Compliant0,rot]
  tauto

/-- The two domains of Theorem 4g. -/
def Eligible (π : Profile) : Prop := 2 ≤ π.t0+π.t1+π.t2 ∨
  (π.t0+π.t1+π.t2=1 ∧ ¬ Compliant π)

theorem eligible_rot (π : Profile) : Eligible (rot π) ↔ Eligible π := by
  have es : (rot π).t0+(rot π).t1+(rot π).t2 = π.t0+π.t1+π.t2 := by
    simp only [rot]
    omega
  unfold Eligible
  rw [es,compliant_rot]

theorem eligible_pos {π : Profile} (h : Eligible π) : 1 ≤ π.t0+π.t1+π.t2 := by
  rcases h with h|⟨h,-⟩ <;> omega

/-- The four V classes exhaust noncompliance in orientation zero. -/
theorem vclass_of_noncompliant0 (π : Profile) (hf : Feas π)
    (h0 : π.t0=1) (h1 : π.t1=0) (h2 : π.t2=0) (hn : ¬ Compliant0 π) :
    G1Check.VClass 1 π ∨ G1Check.VClass 2 π ∨ G1Check.VClass 3 π ∨ G1Check.VClass 4 π := by
  have f0 := hf.1.mp (show 1 ≤ π.f0+π.t0 by omega)
  have f2 := hf.2.2.mpr (show 1 ≤ π.g0+π.t0 by omega)
  simp only [Compliant0,G1Check.VClass] at *
  omega

theorem caseII_b0 (π : Profile) (hf : Feas π) (h0 : π.t0=1) (h1 : π.t1=0) (h2 : π.t2=0)
    (hb : full.mem π) (hn : ¬ (Big0 π ∨ Big1 π ∨ Big2 π)) (hc : ¬ Compliant0 π) : 2 ≤ Phi π := by
  rcases vclass_of_noncompliant0 π hf h0 h1 h2 hc with h|h|h|h
  · exact G1Check.caseII_v 1 G1C1.cert_v1 π hf h0 h1 h2 hb hn h
  · exact G1Check.caseII_v 2 G1C1.cert_v2 π hf h0 h1 h2 hb hn h
  · exact G1Check.caseII_v 3 G1C1.cert_v3 π hf h0 h1 h2 hb hn h
  · exact G1Check.caseII_v 4 G1C1.cert_v4 π hf h0 h1 h2 hb hn h

theorem full_rot {π : Profile} (hb : full.mem π) : full.mem (rot π) := by
  simp only [Box.mem,full,rot] at *
  tauto

theorem nobig_rot {π : Profile} (hn : ¬ (Big0 π ∨ Big1 π ∨ Big2 π)) :
    ¬ (Big0 (rot π) ∨ Big1 (rot π) ∨ Big2 (rot π)) := by
  simp only [Big0,Big1,Big2,rot] at *
  tauto

theorem caseII (π : Profile) (hf : Feas π) (he : Eligible π) (hu : π.t0+π.t1+π.t2 ≤ 11)
    (hb : full.mem π) (hn : ¬ (Big0 π ∨ Big1 π ∨ Big2 π)) : 2 ≤ Phi π := by
  rcases he with ht|⟨ht,hc⟩
  · exact G1Check.caseII_a G1C1.cert_a π hf ht hu hb hn
  have hcases : (π.t0=1 ∧ π.t1=0 ∧ π.t2=0) ∨ (π.t0=0 ∧ π.t1=1 ∧ π.t2=0) ∨
      (π.t0=0 ∧ π.t1=0 ∧ π.t2=1) := by omega
  rcases hcases with ⟨h0,h1,h2⟩|⟨h0,h1,h2⟩|⟨h0,h1,h2⟩
  · have hc0 : ¬ Compliant0 π := by simpa [Compliant,h0,h1,h2] using hc
    exact caseII_b0 π hf h0 h1 h2 hb hn hc0
  · have hc0 : ¬ Compliant0 (rot π) := by simpa [Compliant,h0,h1,h2] using hc
    rw [← Phi_rot π]
    exact caseII_b0 (rot π) ((Feas_rot π).mpr hf) h1 h2 h0 (full_rot hb) (nobig_rot hn) hc0
  · have hc0 : ¬ Compliant0 (rot (rot π)) := by simpa [Compliant,h0,h1,h2] using hc
    rw [← Phi_rot π,← Phi_rot (rot π)]
    exact caseII_b0 (rot (rot π)) ((Feas_rot (rot π)).mpr ((Feas_rot π).mpr hf)) h2 h0 h1
      (full_rot (full_rot hb)) (nobig_rot (nobig_rot hn)) hc0

/-- C2g on every eligible profile with relation zero big. -/
theorem caseIII (π : Profile) (hf : Feas π) (he : Eligible π) (hu : π.t0+π.t1+π.t2 ≤ 11)
    (hf0 : 23 ≤ π.f0) (hg1 : 23 ≤ π.g1) (hb : full2.mem π) : 2 ≤ Phi π := by
  rcases he with ht|⟨ht,hc⟩
  · exact G1Check2.caseIII_a G1C2.cert_a π hf ht hu hf0 hg1 hb
  have hcases : (π.t0=1 ∧ π.t1=0 ∧ π.t2=0) ∨ (π.t0=0 ∧ π.t1=1 ∧ π.t2=0) ∨
      (π.t0=0 ∧ π.t1=0 ∧ π.t2=1) := by omega
  rcases hcases with ⟨h0,h1,h2⟩|⟨h0,h1,h2⟩|⟨h0,h1,h2⟩
  · have hc0 : ¬ Compliant0 π := by simpa [Compliant,h0,h1,h2] using hc
    have fp := hf.2.2.mpr (show 1 ≤ π.g0+π.t0 by omega)
    have hv : G1Check2.VClass2 1 π ∨ G1Check2.VClass2 2 π := by
      simp only [G1Check2.VClass2,Compliant0] at *
      omega
    rcases hv with hv|hv
    · have hr : G1Check2.bb2 1 π.t0 π.t1 π.t2 100 full2 = true := by
        rw [h0,h1,h2]
        exact G1C2.cert_v1
      exact G1Check2.bb2_sound 100 full2 π 1 hr hb hf0 hg1 hf hv
    · have hr : G1Check2.bb2 2 π.t0 π.t1 π.t2 100 full2 = true := by
        rw [h0,h1,h2]
        exact G1C2.cert_v2
      exact G1Check2.bb2_sound 100 full2 π 2 hr hb hf0 hg1 hf hv
  · have hc0 : ¬ Compliant0 (rot π) := by simpa [Compliant,h0,h1,h2] using hc
    have fp := hf.2.1.mp (show 1 ≤ π.f1+π.t1 by omega)
    have hv : G1Check2.VClass2 3 π ∨ G1Check2.VClass2 4 π := by
      simp only [G1Check2.VClass2,Compliant0,rot] at *
      omega
    rcases hv with hv|hv
    · have hr : G1Check2.bb2 3 π.t0 π.t1 π.t2 100 full2 = true := by
        rw [h0,h1,h2]
        exact G1C2.cert_v3
      exact G1Check2.bb2_sound 100 full2 π 3 hr hb hf0 hg1 hf hv
    · have hr : G1Check2.bb2 4 π.t0 π.t1 π.t2 100 full2 = true := by
        rw [h0,h1,h2]
        exact G1C2.cert_v4
      exact G1Check2.bb2_sound 100 full2 π 4 hr hb hf0 hg1 hf hv
  · have hr : G1Check2.bb2 5 π.t0 π.t1 π.t2 100 full2 = true := by
      rw [h0,h1,h2]
      exact G1C2.cert_v5
    exact G1Check2.bb2_sound 100 full2 π 5 hr hb hf0 hg1 hf trivial

/-- Two big relations give Φ ≥ 2 whenever t ≥ 1. -/
theorem caseI (π : Profile) (ht : 1 ≤ π.t0+π.t1+π.t2)
    (h0 : 23 ≤ π.f0 ∧ 23 ≤ π.g1) (h1 : 23 ≤ π.f1 ∧ 23 ≤ π.g2) : 2 ≤ Phi π := by
  have e0 := big_rel_bound π.t0 π.t1 h0.1 h0.2
  have e1 := big_rel_bound π.t1 π.t2 h1.1 h1.2
  have := S_nonneg π.f2 π.g0 π.t0
  have := S_nonneg π.g0 π.f2 π.t2
  have : (0 : ℚ) ≤ 1 / (1 + (π.f0 : ℚ) + π.g0 + π.t0) := by positivity
  have : (0 : ℚ) ≤ 1 / (1 + (π.f1 : ℚ) + π.g1 + π.t1) := by positivity
  have : (0 : ℚ) ≤ 1 / (1 + (π.f2 : ℚ) + π.g2 + π.t2) := by positivity
  have : (0 : ℚ) ≤ π.t0 := Nat.cast_nonneg _
  have : (0 : ℚ) ≤ π.t1 := Nat.cast_nonneg _
  have : (0 : ℚ) ≤ π.t2 := Nat.cast_nonneg _
  have : (1 : ℚ) ≤ (π.t0 : ℚ)+π.t1+π.t2 := by exact_mod_cast ht
  unfold Phi
  linarith

theorem rel0_trichotomy (π : Profile) (ht : π.t0+π.t1+π.t2 ≤ 11) :
    Big0 π ∨ (¬ Big0 π ∧ π.f0 ≤ 92 ∧ π.g1 ≤ 92) ∨ 2 ≤ Phi π := by
  by_cases hB : Big0 π
  · exact Or.inl hB
  by_cases hs : π.f0 ≤ 92 ∧ π.g1 ≤ 92
  · exact Or.inr (Or.inl ⟨hB,hs⟩)
  right; right
  unfold Big0 at hB
  obtain ⟨h1,h2,-,-,-,-⟩ := S_le_Phi π
  by_cases hf : 93 ≤ π.f0
  · have h := S_corner (p:=93) (q:=22) (y:=11) hf (show π.g1 ≤ 22 by omega) (show π.t1 ≤ 11 by omega)
    rw [S_93] at h
    linarith
  · have h := S_corner (p:=93) (q:=22) (y:=11) (show 93 ≤ π.g1 by omega)
      (show π.f0 ≤ 22 by omega) (show π.t0 ≤ 11 by omega)
    rw [S_93] at h
    linarith

/-- Theorem 4g, including all analytic and certified cases. -/
theorem threshold (π : Profile) (hf : Feas π) (he : Eligible π) : 2 ≤ Phi π := by
  by_cases ht : 12 ≤ π.t0+π.t1+π.t2
  · have h := Phi_ge_t π
    have : (12 : ℚ) ≤ (π.t0 : ℚ)+π.t1+π.t2 := by exact_mod_cast ht
    linarith
  have hu : π.t0+π.t1+π.t2 ≤ 11 := by omega
  have hp := eligible_pos he
  have hf1 := (Feas_rot π).mpr hf
  have hf2 := (Feas_rot (rot π)).mpr hf1
  have he1 := (eligible_rot π).mpr he
  have he2 := (eligible_rot (rot π)).mpr he1
  have hp1 := eligible_pos he1
  have hp2 := eligible_pos he2
  have e1 := Phi_rot π
  have e2 : Phi (rot (rot π)) = Phi π := by rw [Phi_rot,Phi_rot]
  have hu1 : (rot π).t0+(rot π).t1+(rot π).t2 ≤ 11 := by simp only [rot]; omega
  have hu2 : (rot (rot π)).t0+(rot (rot π)).t1+(rot (rot π)).t2 ≤ 11 := by simp only [rot]; omega
  have T0 := rel0_trichotomy π hu
  have T1 := rel0_trichotomy (rot π) hu1
  have T2 := rel0_trichotomy (rot (rot π)) hu2
  rw [e1] at T1
  rw [e2] at T2
  simp only [Big0,rot] at T0 T1 T2
  rcases T0 with B0|⟨N0,S0⟩|D0 <;> rcases T1 with B1|⟨N1,S1⟩|D1 <;>
    rcases T2 with B2|⟨N2,S2⟩|D2
  all_goals first
    | assumption
    | exact caseI π hp B0 B1
    | (rw [←e2]; exact caseI _ hp2 B2 B0)
    | (rw [←e1]; exact caseI _ hp1 B1 B2)
    | exact caseIII π hf he hu B0.1 B0.2 (G1Check2.full2_mem π ⟨S2.2,S1.1,S2.1,S1.2⟩)
    | (rw [←e1]; exact caseIII _ hf1 he1 hu1 B1.1 B1.2 (G1Check2.full2_mem _ ⟨S0.2,S2.1,S0.1,S2.2⟩))
    | (rw [←e2]; exact caseIII _ hf2 he2 hu2 B2.1 B2.2 (G1Check2.full2_mem _ ⟨S1.2,S0.1,S1.1,S0.2⟩))
    | (refine caseII π hf he hu (G1Check.full_mem π ⟨S0.1,S2.2,S1.1,S0.2,S2.1,S1.2⟩) ?_
       unfold Big0 Big1 Big2
       omega)

theorem theorem4g_a (π : Profile) (hf : Feas π) (ht : 2 ≤ π.t0+π.t1+π.t2) : 2 ≤ Phi π :=
  threshold π hf (Or.inl ht)

theorem theorem4g_b (π : Profile) (hf : Feas π) (h0 : π.t0=1) (h1 : π.t1=0) (h2 : π.t2=0)
    (hc : ¬ Compliant0 π) : 2 ≤ Phi π := by
  apply threshold π hf (Or.inr ⟨by omega,?_⟩)
  simpa [Compliant,h0,h1,h2] using hc
end Erdos643R3.G1Threshold

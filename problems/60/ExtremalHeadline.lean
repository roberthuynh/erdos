import LinearRangeHeadline
import ExtremalInterpretation

/-! The exact extremal and supersaturation values for powers of two in the
original headline range. The universal lower bound is supplied by the proved
LinearRangeHeadline theorem; no universal inequality is a premise here. -/
namespace Erdos60.Headline
open scoped Classical
open Construction.ExtremalInterpretation


private theorem cycleCount_decidableEq {V : Type*} [Fintype V]
    (G : SimpleGraph V) (d₁ d₂ : DecidableEq V) :
    @Counting.cycleCount V _ d₁ G = @Counting.cycleCount V _ d₂ G := by
  cases Subsingleton.elim d₁ d₂
  rfl

private theorem edgeFinset_card_instances {V : Type*} (G : SimpleGraph V)
    (f₁ f₂ : Fintype G.edgeSet) :
    (@SimpleGraph.edgeFinset V G f₁).card = (@SimpleGraph.edgeFinset V G f₂).card := by
  cases Subsingleton.elim f₁ f₂
  rfl

/-- Actual binary-field attainment and the universal linear-range theorem
give ex(N,C4)=M and h(N,t)=t(q-1), with q=2^k and the exact original range. -/
theorem power_two_extremal_and_supersaturation (k : ℕ) (hk : k ≠ 0)
    (hq : 10000000000000000 ≤ 2^k) :
    c4Extremal ((2^k)^2+2^k+1) = 2^k*(2^k+1)^2/2 ∧
      ∀ t : ℕ, 1 ≤ t → 100000000*t ≤ 2^k →
        c4Supersaturation ((2^k)^2+2^k+1) t = t*(2^k-1) := by
  have heven : Even (2^k) := by
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    exact even_iff_two_dvd.mpr ⟨2^n,by simp [pow_succ,mul_comm]⟩
  apply power_two_interpretation_of_universal_lower k hk hq
  intro t ht hr G hE
  let concreteEdges : Fintype G.edgeSet := inferInstance
  let classicalEdges : Fintype G.edgeSet := by
    let _ : DecidableEq (Fin ((2^k)^2+2^k+1)) := Classical.decEq _
    infer_instance
  have hEroot : (@SimpleGraph.edgeFinset _ G classicalEdges).card = 2^k*(2^k+1)^2/2+t :=
    (edgeFinset_card_instances G classicalEdges concreteEdges).trans hE
  have hh := linear_range_lower G (2^k) t heven (by norm_num; exact hq) ht
    (by norm_num; exact hr) (by simp) hEroot
  have hc := cycleCount_decidableEq G (Classical.decEq _) inferInstance
  rw [hc] at hh
  exact hh

/-- Exact C4 extremal edge threshold at binary prime-power orders. -/
theorem power_two_c4Extremal (k : ℕ) (hk : k ≠ 0) (hq : 10000000000000000 ≤ 2^k) :
    c4Extremal ((2^k)^2+2^k+1) = 2^k*(2^k+1)^2/2 :=
  (power_two_extremal_and_supersaturation k hk hq).1

/-- Exact minimum ordinary unlabelled C4 count at ex(N,C4)+t edges. -/
theorem power_two_c4Supersaturation (k t : ℕ) (hk : k ≠ 0)
    (hq : 10000000000000000 ≤ 2^k) (ht : 1 ≤ t) (hr : 100000000*t ≤ 2^k) :
    c4Supersaturation ((2^k)^2+2^k+1) t = t*(2^k-1) :=
  (power_two_extremal_and_supersaturation k hk hq).2 t ht hr

#print axioms power_two_extremal_and_supersaturation
#print axioms power_two_c4Extremal
#print axioms power_two_c4Supersaturation
end Erdos60.Headline

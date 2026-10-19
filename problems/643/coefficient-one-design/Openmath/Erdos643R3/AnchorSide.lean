import Openmath.Erdos643R3.HostPsi
import Openmath.Erdos643R3.USideArith
import Openmath.Erdos643R3.AnchorAssemblyArith
import Openmath.Erdos643R3.Pw2312

set_option autoImplicit false
namespace Erdos643R3.AnchorSide
open Finset
open Erdos643R3.Identity Erdos643R3.SlotModel Erdos643R3.AnchorCaps
open Erdos643R3.AnchorW Erdos643R3.AnchorDecomposition Erdos643R3.HostPsi
open Erdos643R3.GeneralizedPsi Erdos643R3.AnchorAssemblyArith
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}
variable {x y u v w : V}

theorem charge_shift_ge_one (h : Host H x y u v w) :
    1 ≤ L1Top.charge H {x,u,v} + 13 / 12 := by
  have hp := Pw2312Main.per_triple h.uniform h.avoiding h.xuv
  unfold L1Top.charge
  linarith

theorem deficit_le_twelfth (h : Host H x y u v w) : L1Top.deficit H {x,u,v} ≤ 1 / 12 := by
  have hh := charge_shift_ge_one h
  unfold L1Top.deficit
  linarith

/-- S10 for the actual host, with every numerical and loss hypothesis discharged. -/
theorem side_s10 (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2)
    (hheavy : 3 ≤ codeg H {x,u}) (hd : L1Top.Deficient H {x,u,v}) :
    2 < uMinus H x u w + (13 / 12 - L1Top.deficit H {x,u,v}) +
      comp (tset H w x u).card (L1Top.deficit H {x,u,v}) := by
  obtain ⟨inJ,hE,hbound⟩ := host_psi_bridge h hcard
  have hr := R1_pos_of_heavy h hheavy
  have hkm := RU_type2_card_le h
  have hS1 := charge_shift_ge_one h
  have hL9 := host_L9 h hcard
  have hdef : L1Top.charge H {x,u,v} + 13 / 12 < 13 / 12 := by
    change L1Top.charge H {x,u,v} < 0 at hd
    linarith
  have hh := lemmaS10_arith hr hkm hE hS1 hL9 hdef hbound
  have hcomp : surplus (L1Top.charge H {x,u,v} + 13 / 12) (tset H w x u).card =
      comp (tset H w x u).card (L1Top.deficit H {x,u,v}) := by
    unfold surplus comp L1Top.deficit
    split_ifs <;> ring
  rw [hcomp] at hh
  unfold L1Top.deficit at hh ⊢
  linarith

/-- Lemma U's complete three-case lower bound, for the actual host quantities. -/
theorem gU_gt_threshold (h : Host H x y u v w) (hcard : (CN H {u,w}).card = 2)
    (hheavy : 3 ≤ codeg H {x,u}) (hd : L1Top.Deficient H {x,u,v}) :
    uThreshold (tset H w x u).card (L1Top.deficit H {x,u,v}) < gU H x u v w := by
  have hi : (0 : ℚ) ≤ (iset H w x u).card := Nat.cast_nonneg _
  have hs := side_s10 h hcard hheavy hd
  by_cases hm0 : (tset H w x u).card = 0
  · simp only [comp, uThreshold, hm0, ↓reduceIte] at hs ⊢
    unfold gU L1Top.deficit at *
    linarith
  · by_cases hm1 : (tset H w x u).card = 1
    · simp [comp, uThreshold, hm1] at hs ⊢
      unfold gU L1Top.deficit at *
      linarith
    · obtain ⟨inJ,hE,hbound⟩ := host_psi_bridge h hcard
      have hr := R1_pos_of_heavy h hheavy
      have hkm := RU_type2_card_le h
      have hL9 := host_L9 h hcard
      have hdef : L1Top.charge H {x,u,v} + 13 / 12 < 13 / 12 := by
        change L1Top.charge H {x,u,v} < 0 at hd
        linarith
      have h9 := G3hpArith.lemma9_arith hr hL9 hdef
      have hu := lemmaUc_arith (d := (D1 H x y u v w).card) (e := (EU H x y u v w).card)
        inJ h9.1 (fun hh => (h9.2 hh).1) (by omega) hkm
      simp only [uThreshold, hm0, hm1, ↓reduceIte]
      unfold gU
      linarith

end Erdos643R3.AnchorSide

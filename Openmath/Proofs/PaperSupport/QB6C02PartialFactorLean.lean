import Openmath.Proofs.PaperSupport.QB6Assembly

/- 

-/
open Finset
namespace Erdos585.QB6C02PartialFactor
open QB4 QB5 QB6Assembly
universe u
variable {V : Type u} [DecidableEq V]

/-- Degrees count the literal pairs in the selected original edge set. -/
def edgeDegree (F : Finset (V × V)) (r : V × V → V) (v : V) : ℕ :=
  #{e ∈ F | r e = v}

/-- Actual C-saturating partial factor after deleting the specified original vertex. -/
def P4DeleteAny : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V), C02Input G A C → ∀ p ∈ A,
      ∃ F : Finset (V × V), F.Nonempty ∧ F ⊆ adjPairs G (A.erase p) C ∧
        (∀ c ∈ C, edgeDegree F Prod.snd c = 4) ∧
        (∀ a ∈ A.erase p, edgeDegree F Prod.fst a ≤ 4) ∧
        (∑ a ∈ A.erase p, (4 - (edgeDegree F Prod.fst a : ℤ))) = 4

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Exact capped actual-neighbor demand. -/
def demandC02 (C U : Finset V) : ℤ :=
  4 * #U - ∑ c ∈ C, min 4 (dg G U c : ℤ)

/-- Exact physical complementary theta with no supplied multiplicity. -/
def thetaC02 (C Z : Finset V) : ℤ :=
  8 - 4 * #Z + ∑ c ∈ C, max 0 ((dg G Z c : ℤ) - 2)

variable {G}
set_option maxHeartbeats 1800000

omit [DecidableEq V] in
theorem c02_cardC {A C : Finset V} (h : C02Input G A C) : 4 ≤ #C := by
  have he : ec G A C = 6 * #C := by
    rw [ec_comm]
    unfold ec
    rw [sum_congr rfl h.satC, sum_const, smul_eq_mul, mul_comm]
  have hlo : 4 * #A ≤ ec G A C := by
    have hs := sum_le_sum h.minA
    change (∑ _a ∈ A, (4 : ℕ)) ≤ ec G A C at hs
    simpa only [sum_const, smul_eq_mul, mul_comm] using hs
  rw [he, h.card] at hlo
  omega

theorem complement_demand {A C U : Finset V} (h : C02Input G A C) (hU : U ⊆ A) :
    demandC02 G C U = thetaC02 G C (A \ U) := by
  have hp : ∀ c ∈ C,
      min 4 (dg G U c : ℤ) + max 0 ((dg G (A \ U) c : ℤ) - 2) = 4 := by
    intro c hc
    have hd := dg_sdiff_add (G := G) hU c
    rw [h.satC c hc] at hd
    omega
  have hs : (∑ c ∈ C, min 4 (dg G U c : ℤ)) +
      (∑ c ∈ C, max 0 ((dg G (A \ U) c : ℤ) - 2)) = 4 * (#C : ℤ) := by
    rw [← sum_add_distrib, sum_congr rfl hp, sum_const, nsmul_eq_mul]
    ring
  have hc : (#(A \ U) : ℤ) + #U = #A := by
    exact_mod_cast card_sdiff_add_card_eq_card hU
  have ha : (#A : ℤ) = #C + 2 := by exact_mod_cast h.card
  unfold demandC02 thetaC02
  linarith

omit [DecidableEq V] in
theorem theta_canonical (C Z : Finset V) :
    thetaC02 G C Z = 8 - 4 * #Z - 2 * #(cpr G C Z) + ec G Z (cpr G C Z) := by
  have he := theta_cpr (G := G) (fun _ : V => 0) C Z
  have h0 : msum (fun _ : V => 0) Z = 0 := by simp [msum]
  unfold theta thetaStar at he
  rw [h0] at he
  unfold thetaC02
  linarith

omit [DecidableEq V] in
theorem theta_proper_bounds {A C Z : Finset V} (h : C02Input G A C)
    (hZ : Z ⊆ A) (hne : Z ≠ A) (h3 : 3 ≤ #Z) :
    thetaC02 G C Z ≤ 1 - ((#Z : ℤ) - #(cpr G C Z)) ∧
    thetaC02 G C Z ≤ 8 + 2 * ((#Z : ℤ) - #(cpr G C Z)) := by
  have hy := cpr_subset (G := G) C Z
  have hyc := card_le_card hy
  have hzc : #Z < #A := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hZ, hne⟩)
  have hg := h.sparse Z hZ (cpr G C Z) hy (by omega) (by omega)
  have hecap : (ec G Z (cpr G C Z) : ℤ) ≤ 6 * (#Z : ℤ) := by
    have hs : ec G Z (cpr G C Z) ≤ 6 * #Z := by
      calc
        ec G Z (cpr G C Z) ≤ ec G Z C := ec_mono_right Z hy
        _ ≤ ∑ _a ∈ Z, 6 := sum_le_sum fun a ha => h.capA a (hZ ha)
        _ = 6 * #Z := by simp only [sum_const, smul_eq_mul, mul_comm]
    exact_mod_cast hs
  have ht := theta_canonical (G := G) C Z
  unfold gv at hg
  constructor <;> linarith

omit [DecidableEq V] in
theorem theta_whole {A C : Finset V} (h : C02Input G A C) : thetaC02 G C A = 0 := by
  have hs : (∑ c ∈ C, max 0 ((dg G A c : ℤ) - 2)) = 4 * (#C : ℤ) := by
    have hp : ∀ c ∈ C, max 0 ((dg G A c : ℤ) - 2) = 4 := by
      intro c hc
      rw [h.satC c hc]
      norm_num
    rw [sum_congr rfl hp, sum_const, nsmul_eq_mul]
    ring
  have ha : (#A : ℤ) = #C + 2 := by exact_mod_cast h.card
  unfold thetaC02
  rw [hs]
  linarith

theorem theta_three {A C Z : Finset V} (h : C02Input G A C)
    (hZ : Z ⊆ A) (h3 : 3 ≤ #Z) : thetaC02 G C Z ≤ 3 := by
  by_cases heq : Z = A
  · rw [heq, theta_whole h]
    norm_num
  · have hb := theta_proper_bounds h hZ heq h3
    omega

omit [DecidableEq V] in
theorem theta_small (C : Finset V) {Z : Finset V} (h2 : #Z ≤ 2) :
    thetaC02 G C Z = 8 - 4 * #Z := by
  have hs : (∑ c ∈ C, max 0 ((dg G Z c : ℤ) - 2)) = 0 := by
    refine sum_eq_zero fun c _ => ?_
    have hd := dg_le_card (G := G) Z c
    omega
  unfold thetaC02
  rw [hs]
  ring

theorem theta_nonempty {A C Z : Finset V} (h : C02Input G A C)
    (hZ : Z ⊆ A) (hz : Z.Nonempty) : thetaC02 G C Z ≤ 4 := by
  by_cases h3 : 3 ≤ #Z
  · exact (theta_three h hZ h3).trans (by norm_num)
  · have hp := card_pos.mpr hz
    rw [theta_small C (by omega)]
    omega

theorem demand_delete_bound {A C U : Finset V} (h : C02Input G A C)
    {p : V} (hp : p ∈ A) (hU : U ⊆ A.erase p) : demandC02 G C U ≤ 4 := by
  have hUA : U ⊆ A := hU.trans (erase_subset _ _)
  rw [complement_demand h hUA]
  apply theta_nonempty h sdiff_subset
  refine ⟨p, mem_sdiff.mpr ⟨hp, ?_⟩⟩
  exact fun hpu => (mem_erase.mp (hU hpu)).1 rfl

/-- The unbalanced cut is derived in its actual C-source, retained-A-sink orientation. -/
theorem delete_cut {A C : Finset V} (h : C02Input G A C) {p : V} (hp : p ∈ A) :
    ∀ S ⊆ C, ∀ T ⊆ A.erase p,
      4 * #S ≤ ec G S (A.erase p \ T) + 4 * #T := by
  intro S hS T hT
  let U := A.erase p \ T
  have hU : U ⊆ A.erase p := sdiff_subset
  have hd := demand_delete_bound h hp hU
  have hs := sum_sdiff hS (f := fun c => min 4 (dg G U c : ℤ))
  have h1 : (∑ c ∈ S, min 4 (dg G U c : ℤ)) ≤ (ec G U S : ℤ) := by
    rw [ec_comm]
    change (∑ c ∈ S, min 4 (dg G U c : ℤ)) ≤ ((∑ c ∈ S, dg G U c : ℕ) : ℤ)
    rw [Nat.cast_sum]
    exact sum_le_sum fun c _ => min_le_right _ _
  have h2 : (∑ c ∈ C \ S, min 4 (dg G U c : ℤ)) ≤ 4 * (#(C \ S) : ℤ) := by
    calc
      _ ≤ ∑ _c ∈ C \ S, (4 : ℤ) := sum_le_sum fun c _ => min_le_left _ _
      _ = _ := by rw [sum_const, nsmul_eq_mul]; ring
  have hcS : (#(C \ S) : ℤ) + #S = #C := by exact_mod_cast card_sdiff_add_card_eq_card hS
  have hcT : (#U : ℤ) + #T = #(A.erase p) := by exact_mod_cast card_sdiff_add_card_eq_card hT
  have hcR : (#(A.erase p) : ℤ) = #C + 1 := by
    rw [card_erase_of_mem hp]
    have ha := h.card
    have hpA := card_pos.mpr (show A.Nonempty from ⟨p, hp⟩)
    omega
  have hcut : 4 * (#S : ℤ) ≤ (ec G U S : ℤ) + 4 * #T := by
    unfold demandC02 at hd
    linarith
  rw [ec_comm] at hcut
  exact_mod_cast hcut

/-- Trim every actual first-coordinate fiber independently to exactly four pairs. -/
theorem trim_first {F : Finset (V × V)} {P : Finset V}
    (hlo : ∀ p ∈ P, 4 ≤ edgeDegree F Prod.fst p) :
    ∃ J ⊆ F, ∀ p ∈ P, edgeDegree J Prod.fst p = 4 := by
  classical
  have hex : ∀ p : V, ∃ T ⊆ {e ∈ F | e.1 = p}, p ∈ P → #T = 4 := by
    intro p
    by_cases hp : p ∈ P
    · obtain ⟨T, hT, hc⟩ := exists_subset_card_eq (hlo p hp)
      exact ⟨T, hT, fun _ => hc⟩
    · exact ⟨∅, empty_subset _, fun hh => False.elim (hp hh)⟩
  choose t ht htc using hex
  let J := P.biUnion t
  have hJF : J ⊆ F := by
    intro e he
    obtain ⟨p, hp, he⟩ := mem_biUnion.mp he
    exact (mem_filter.mp (ht p he)).1
  refine ⟨J, hJF, ?_⟩
  intro p hp
  have heq : {e ∈ J | e.1 = p} = t p := by
    ext e
    constructor
    · intro he
      obtain ⟨heJ, hep⟩ := mem_filter.mp he
      obtain ⟨p', hp', het⟩ := mem_biUnion.mp heJ
      have hep' := (mem_filter.mp (ht p' het)).2
      have hepp : p' = p := hep'.symm.trans hep
      exact hepp ▸ het
    · intro he
      exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨p, hp, he⟩, (mem_filter.mp (ht p he)).2⟩
  change #{e ∈ J | e.1 = p} = 4
  rw [heq]
  exact htc p hp

/-- Integral unbalanced four-capacity selection, using the actual QB4 Hall gadget. -/
theorem exists_left_saturated (P Q : Finset V) (hP : P.Nonempty)
    (hcut : ∀ S ⊆ P, ∀ T ⊆ Q, 4 * #S ≤ ec G S (Q \ T) + 4 * #T)
    (hQ4 : ∀ q ∈ Q, 4 ≤ dg G P q) :
    ∃ J ⊆ adjPairs G P Q,
      (∀ p ∈ P, edgeDegree J Prod.fst p = 4) ∧
      (∀ q ∈ Q, edgeDegree J Prod.snd q ≤ 4) := by
  classical
  obtain ⟨p0, hp0⟩ := hP
  have : Nonempty ((V × V) ⊕ (V × ℕ)) := ⟨Sum.inr (p0, 0)⟩
  have hP4 : ∀ p ∈ P, 4 ≤ dg G Q p := fun p hp => four_le_dg_left hcut hp
  obtain ⟨g, hginj, hgt⟩ := exists_injOn_of_hall (gadgetIndex G P Q) (gadget G P Q)
    fun S hS => gadget_hall hcut hP4 hQ4 S hS
  let K := (adjPairs G P Q).filter fun e => g (Sum.inl e) = Sum.inl e
  have hKPQ : K ⊆ adjPairs G P Q := filter_subset _ _
  have hKlo : ∀ p ∈ P, 4 ≤ edgeDegree K Prod.fst p := fun p hp =>
    four_le_card_kept hP4 hginj hgt hp
  have hKhi : ∀ q ∈ Q, edgeDegree K Prod.snd q ≤ 4 := fun q hq =>
    card_kept_le_four hginj hgt hq
  obtain ⟨J, hJK, hJP⟩ := trim_first hKlo
  refine ⟨J, hJK.trans hKPQ, hJP, ?_⟩
  intro q hq
  exact (card_le_card (filter_subset_filter _ hJK)).trans (hKhi q hq)

/-- Every original deletion produces an actual nonempty four-deficit partial factor. -/
theorem p4_delete_any : P4DeleteAny.{u} := by
  intro V _ G _ A C h p hp
  have hC : C.Nonempty := card_pos.mp (by have hc := c02_cardC h; omega)
  obtain ⟨J, hJ, hJC, hJR⟩ := exists_left_saturated C (A.erase p) hC (delete_cut h hp)
    (fun a ha => h.minA a (erase_subset _ _ ha))
  let F := J.map ⟨Prod.swap, Prod.swap_injective⟩
  have hF : F ⊆ adjPairs G (A.erase p) C := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := mem_map.mp he
    have hxadj := (mem_filter.mp (hJ hx)).2
    have hxends := mem_product.mp (mem_filter.mp (hJ hx)).1
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hxends.2, hxends.1⟩, hxadj.symm⟩
  have hFC : ∀ c ∈ C, edgeDegree F Prod.snd c = 4 := by
    intro c hc
    unfold edgeDegree
    dsimp only [F]
    rw [filter_map, card_map]
    change edgeDegree J Prod.fst c = 4
    exact hJC c hc
  have hFR : ∀ a ∈ A.erase p, edgeDegree F Prod.fst a ≤ 4 := by
    intro a ha
    unfold edgeDegree
    dsimp only [F]
    rw [filter_map, card_map]
    change edgeDegree J Prod.snd a ≤ 4
    exact hJR a ha
  have hFne : F.Nonempty := by
    obtain ⟨c, hc⟩ := hC
    obtain ⟨e, he⟩ := card_pos.mp (show 0 < #{e ∈ F | e.2 = c} from by
      change 0 < edgeDegree F Prod.snd c
      rw [hFC c hc]
      norm_num)
    exact ⟨e, (mem_filter.mp he).1⟩
  have hsR : #F = ∑ a ∈ A.erase p, edgeDegree F Prod.fst a :=
    card_eq_sum_card_fiberwise fun e he => (mem_product.mp (mem_filter.mp (hF he)).1).1
  have hsC : #F = ∑ c ∈ C, edgeDegree F Prod.snd c :=
    card_eq_sum_card_fiberwise fun e he => (mem_product.mp (mem_filter.mp (hF he)).1).2
  have hcF : (#F : ℤ) = 4 * #C := by
    rw [sum_congr rfl hFC, sum_const, smul_eq_mul, mul_comm] at hsC
    exact_mod_cast hsC
  have hsRi : (∑ a ∈ A.erase p, (edgeDegree F Prod.fst a : ℤ)) = #F := by
    exact_mod_cast hsR.symm
  have hcR : (#(A.erase p) : ℤ) = #C + 1 := by
    rw [card_erase_of_mem hp]
    have ha := h.card
    have hpA := card_pos.mpr (show A.Nonempty from ⟨p, hp⟩)
    omega
  refine ⟨F, hFne, hF, hFC, hFR, ?_⟩
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, hsRi]
  linarith

/- -/
structure PhysicalPartial (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V) (p : V) (F : Finset (V × V)) : Prop where
  nonempty : F.Nonempty
  actual : F ⊆ adjPairs G (A.erase p) C
  cdegree : ∀ c ∈ C, edgeDegree F Prod.snd c = 4
  acap : ∀ a ∈ A.erase p, edgeDegree F Prod.fst a ≤ 4
  deficit : (∑ a ∈ A.erase p, (4 - (edgeDegree F Prod.fst a : ℤ))) = 4

/-- Literal deficient-degree counts; the four profiles are not an edge census. -/
def DeficitProfiles (F : Finset (V × V)) (R : Finset V) : Prop :=
  let n1 := #{a ∈ R | edgeDegree F Prod.fst a = 1}
  let n2 := #{a ∈ R | edgeDegree F Prod.fst a = 2}
  let n3 := #{a ∈ R | edgeDegree F Prod.fst a = 3}
  (n1 = 1 ∧ n2 = 0 ∧ n3 = 1) ∨
  (n1 = 0 ∧ n2 = 2 ∧ n3 = 0) ∨
  (n1 = 0 ∧ n2 = 1 ∧ n3 = 2) ∨
  (n1 = 0 ∧ n2 = 0 ∧ n3 = 4)

/-- Existence is paid by P4DeleteAny; no-quartic is explicitly in the original host. -/
def P4PositiveProfiles : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V), C02Input G A C → ¬ Quartic G A C → ∀ p ∈ A,
      ∃ F : Finset (V × V), PhysicalPartial G A C p F ∧
        (∀ a ∈ A.erase p, 0 < edgeDegree F Prod.fst a) ∧ DeficitProfiles F (A.erase p)

theorem zero_row_quartic {A C : Finset V} {p : V} {F : Finset (V × V)}
    (h : PhysicalPartial G A C p F) {a : V} (ha : a ∈ A.erase p)
    (hz : edgeDegree F Prod.fst a = 0) : Quartic G A C := by
  have hs := sum_erase_add (A.erase p) (fun b => (4 - (edgeDegree F Prod.fst b : ℤ))) ha
  rw [h.deficit, hz] at hs
  have hsum0 : (∑ b ∈ (A.erase p).erase a, (4 - (edgeDegree F Prod.fst b : ℤ))) = 0 := by
    omega
  have hother : ∀ b ∈ (A.erase p).erase a, edgeDegree F Prod.fst b = 4 := by
    intro b hb
    have hsingle := single_le_sum (f := fun b => (4 - (edgeDegree F Prod.fst b : ℤ)))
      (s := (A.erase p).erase a) (fun v hv => by
        have hc := h.acap v (erase_subset _ _ hv)
        omega) hb
    rw [hsum0] at hsingle
    have hc := h.acap b (erase_subset _ _ hb)
    omega
  refine ⟨F, h.nonempty, ?_, ?_, ?_, ?_⟩
  · intro e he
    have hends := mem_product.mp (mem_filter.mp (h.actual he)).1
    exact mem_product.mpr ⟨erase_subset _ _ hends.1, hends.2⟩
  · intro e he
    exact (mem_filter.mp (h.actual he)).2
  · intro b
    change edgeDegree F Prod.fst b = 0 ∨ edgeDegree F Prod.fst b = 4
    by_cases hb : b ∈ A.erase p
    · by_cases hba : b = a
      · exact Or.inl (hba ▸ hz)
      · exact Or.inr (hother b (mem_erase.mpr ⟨hba, hb⟩))
    · left
      apply card_eq_zero.mpr
      apply filter_eq_empty_iff.mpr
      intro e he heb
      apply hb
      rw [← heb]
      exact (mem_product.mp (mem_filter.mp (h.actual he)).1).1
  · intro c
    change edgeDegree F Prod.snd c = 0 ∨ edgeDegree F Prod.snd c = 4
    by_cases hc : c ∈ C
    · exact Or.inr (h.cdegree c hc)
    · left
      apply card_eq_zero.mpr
      apply filter_eq_empty_iff.mpr
      intro e he hec
      apply hc
      rw [← hec]
      exact (mem_product.mp (mem_filter.mp (h.actual he)).1).2

theorem no_quartic_positive {A C : Finset V} {p : V} {F : Finset (V × V)}
    (h : PhysicalPartial G A C p F) (hnq : ¬ Quartic G A C) :
    ∀ a ∈ A.erase p, 0 < edgeDegree F Prod.fst a := by
  intro a ha
  by_contra! hz
  exact hnq (zero_row_quartic h ha (by omega))

theorem deficit_profiles {F : Finset (V × V)} {R : Finset V}
    (hp : ∀ a ∈ R, 0 < edgeDegree F Prod.fst a)
    (hc : ∀ a ∈ R, edgeDegree F Prod.fst a ≤ 4)
    (hdef : (∑ a ∈ R, (4 - (edgeDegree F Prod.fst a : ℤ))) = 4) :
    DeficitProfiles F R := by
  have hpoint : ∀ a ∈ R, (4 - (edgeDegree F Prod.fst a : ℤ)) =
      3 * (if edgeDegree F Prod.fst a = 1 then (1 : ℤ) else 0) +
      2 * (if edgeDegree F Prod.fst a = 2 then (1 : ℤ) else 0) +
      (if edgeDegree F Prod.fst a = 3 then (1 : ℤ) else 0) := by
    intro a ha
    have hlo := hp a ha
    have hhi := hc a ha
    omega
  have hcount (n : ℕ) : (∑ a ∈ R, if edgeDegree F Prod.fst a = n then (1 : ℤ) else 0) =
      (#{a ∈ R | edgeDegree F Prod.fst a = n} : ℤ) := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  rw [sum_congr rfl hpoint, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum,
    hcount 1, hcount 2, hcount 3] at hdef
  unfold DeficitProfiles
  omega

theorem p4_positive_profiles : P4PositiveProfiles.{u} := by
  intro V _ G _ A C h hnq p hp
  obtain ⟨F, hne, hF, hC, hA, hdef⟩ := p4_delete_any G A C h p hp
  have hphys : PhysicalPartial G A C p F := ⟨hne, hF, hC, hA, hdef⟩
  have hpos := no_quartic_positive hphys hnq
  exact ⟨F, hphys, hpos, deficit_profiles hpos hA hdef⟩

def PairConnected (F : Finset (V × V)) (R C : Finset V) : Prop :=
  ∀ S ⊆ R, ∀ T ⊆ C, (∀ e ∈ F, e.1 ∈ S ↔ e.2 ∈ T) →
    (S = ∅ ∧ T = ∅) ∨ (S = R ∧ T = C)

def P4NoQuarticShape : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A C : Finset V), C02Input G A C → ¬ Quartic G A C → ∀ p ∈ A,
      ∃ F : Finset (V × V), PhysicalPartial G A C p F ∧
        (∀ a ∈ A.erase p, 0 < edgeDegree F Prod.fst a) ∧
        PairConnected F (A.erase p) C ∧ DeficitProfiles F (A.erase p)

theorem closed_restriction {A C : Finset V} {p : V} {F : Finset (V × V)}
    (h : PhysicalPartial G A C p F) {S T : Finset V} (hS : S ⊆ A.erase p) (hT : T ⊆ C)
    (hcl : ∀ e ∈ F, e.1 ∈ S ↔ e.2 ∈ T) :
    ∃ J ⊆ adjPairs G S T,
      (∀ c ∈ T, edgeDegree J Prod.snd c = 4) ∧
      (∀ a ∈ S, edgeDegree J Prod.fst a ≤ 4) := by
  let J := {e ∈ F | e.1 ∈ S}
  have hJ : J ⊆ adjPairs G S T := by
    intro e he
    obtain ⟨heF, heS⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨mem_product.mpr ⟨heS, (hcl e heF).mp heS⟩,
      (mem_filter.mp (h.actual heF)).2⟩
  have hfst : ∀ a ∈ S, edgeDegree J Prod.fst a = edgeDegree F Prod.fst a := by
    intro a ha
    unfold edgeDegree
    apply congrArg card
    ext e
    simp only [J, mem_filter]
    constructor
    · exact fun he => ⟨he.1.1, he.2⟩
    · intro he
      exact ⟨⟨he.1, he.2 ▸ ha⟩, he.2⟩
  have hsnd : ∀ c ∈ T, edgeDegree J Prod.snd c = edgeDegree F Prod.snd c := by
    intro c hc
    unfold edgeDegree
    apply congrArg card
    ext e
    simp only [J, mem_filter]
    constructor
    · exact fun he => ⟨he.1.1, he.2⟩
    · intro he
      exact ⟨⟨he.1, (hcl e he.1).mpr (he.2 ▸ hc)⟩, he.2⟩
  exact ⟨J, hJ, fun c hc => (hsnd c hc).trans (h.cdegree c (hT hc)),
    fun a ha => (hfst a ha).le.trans (h.acap a (hS ha))⟩

theorem closed_card_strict {A C : Finset V} {p : V} {F : Finset (V × V)}
    (h : PhysicalPartial G A C p F) (hnq : ¬ Quartic G A C)
    {S T : Finset V} (hS : S ⊆ A.erase p) (hT : T ⊆ C) (hneT : T.Nonempty)
    (hcl : ∀ e ∈ F, e.1 ∈ S ↔ e.2 ∈ T) : #T < #S := by
  obtain ⟨J, hJ, hJC, hJA⟩ := closed_restriction h hS hT hcl
  have hsS : #J = ∑ a ∈ S, edgeDegree J Prod.fst a :=
    card_eq_sum_card_fiberwise fun e he => (mem_product.mp (mem_filter.mp (hJ he)).1).1
  have hsT : #J = ∑ c ∈ T, edgeDegree J Prod.snd c :=
    card_eq_sum_card_fiberwise fun e he => (mem_product.mp (mem_filter.mp (hJ he)).1).2
  have hcJ : #J = 4 * #T := by
    rw [sum_congr rfl hJC, sum_const, smul_eq_mul, mul_comm] at hsT
    exact hsT
  have hsumle : (∑ a ∈ S, edgeDegree J Prod.fst a) ≤ ∑ _a ∈ S, (4 : ℕ) := sum_le_sum hJA
  have hs4 : (∑ _a ∈ S, (4 : ℕ)) = 4 * #S := by
    rw [sum_const, smul_eq_mul, mul_comm]
  have hle : #T ≤ #S := by omega
  by_contra! hnot
  have heq : #T = #S := by omega
  have hJ4 : ∀ a ∈ S, edgeDegree J Prod.fst a = 4 := by
    have hse : (∑ a ∈ S, edgeDegree J Prod.fst a) = ∑ _a ∈ S, (4 : ℕ) := by omega
    exact (sum_eq_sum_iff_of_le hJA).mp hse
  have hJne : J.Nonempty := card_pos.mp (by have hp := card_pos.mpr hneT; omega)
  apply hnq
  refine ⟨J, hJne, ?_, ?_, ?_, ?_⟩
  · intro e he
    have heST := mem_product.mp (mem_filter.mp (hJ he)).1
    exact mem_product.mpr ⟨erase_subset _ _ (hS heST.1), hT heST.2⟩
  · intro e he
    exact (mem_filter.mp (hJ he)).2
  · intro a
    change edgeDegree J Prod.fst a = 0 ∨ edgeDegree J Prod.fst a = 4
    by_cases ha : a ∈ S
    · exact Or.inr (hJ4 a ha)
    · left
      apply card_eq_zero.mpr
      apply filter_eq_empty_iff.mpr
      intro e he hea
      apply ha
      rw [← hea]
      exact (mem_product.mp (mem_filter.mp (hJ he)).1).1
  · intro c
    change edgeDegree J Prod.snd c = 0 ∨ edgeDegree J Prod.snd c = 4
    by_cases hc : c ∈ T
    · exact Or.inr (hJC c hc)
    · left
      apply card_eq_zero.mpr
      apply filter_eq_empty_iff.mpr
      intro e he hec
      apply hc
      rw [← hec]
      exact (mem_product.mp (mem_filter.mp (hJ he)).1).2

theorem physical_connected {A C : Finset V} {p : V} {F : Finset (V × V)}
    (h : PhysicalPartial G A C p F) (hnq : ¬ Quartic G A C)
    (hcard : #(A.erase p) = #C + 1) : PairConnected F (A.erase p) C := by
  have hpos := no_quartic_positive h hnq
  have hempty : ∀ S ⊆ A.erase p, ∀ T ⊆ C,
      (∀ e ∈ F, e.1 ∈ S ↔ e.2 ∈ T) → T = ∅ → S = ∅ := by
    intro S hS T hT hcl hTempty
    apply eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨e, he⟩ := card_pos.mp (hpos a (hS ha))
    have heF := (mem_filter.mp he).1
    have hea := (mem_filter.mp he).2
    have heT := (hcl e heF).mp (hea ▸ ha)
    rw [hTempty] at heT
    exact notMem_empty _ heT
  intro S hS T hT hcl
  have hcl' : ∀ e ∈ F, e.1 ∈ A.erase p \ S ↔ e.2 ∈ C \ T := by
    intro e he
    have hends := mem_product.mp (mem_filter.mp (h.actual he)).1
    simp only [mem_sdiff]
    constructor
    · intro hx
      exact ⟨hends.2, fun hh => hx.2 ((hcl e he).mpr hh)⟩
    · intro hx
      exact ⟨hends.1, fun hh => hx.2 ((hcl e he).mp hh)⟩
  by_cases hTempty : T = ∅
  · exact Or.inl ⟨hempty S hS T hT hcl hTempty, hTempty⟩
  by_cases hTwhole : T = C
  · have hscomp : A.erase p \ S = ∅ :=
      hempty (A.erase p \ S) sdiff_subset (C \ T) sdiff_subset hcl' (by simp [hTwhole])
    have hswhole : S = A.erase p := (sdiff_eq_empty_iff_subset.mp hscomp).antisymm hS |>.symm
    exact Or.inr ⟨hswhole, hTwhole⟩
  have hTne : T.Nonempty := nonempty_iff_ne_empty.mpr hTempty
  have hTlt : #T < #C := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hT, hTwhole⟩)
  have hTcompne : (C \ T).Nonempty := card_pos.mp (by
    have he := card_sdiff_add_card_eq_card hT
    omega)
  have hlt := closed_card_strict h hnq hS hT hTne hcl
  have hlt' := closed_card_strict h hnq sdiff_subset sdiff_subset hTcompne hcl'
  have hcS := card_sdiff_add_card_eq_card hS
  have hcT := card_sdiff_add_card_eq_card hT
  omega

theorem p4_no_quartic_shape : P4NoQuarticShape.{u} := by
  intro V _ G _ A C h hnq p hp
  obtain ⟨F, hphys, hpos, hprofiles⟩ := p4_positive_profiles G A C h hnq p hp
  have hcard : #(A.erase p) = #C + 1 := by
    rw [card_erase_of_mem hp, h.card]
    omega
  exact ⟨F, hphys, hpos, physical_connected hphys hnq hcard, hprofiles⟩

#print axioms Erdos585.QB6C02PartialFactor.p4_delete_any
#check Erdos585.QB6C02PartialFactor.p4_delete_any
example : P4DeleteAny.{u} := p4_delete_any
#print axioms Erdos585.QB6C02PartialFactor.p4_positive_profiles
#check Erdos585.QB6C02PartialFactor.p4_positive_profiles
example : P4PositiveProfiles.{u} := p4_positive_profiles
#print axioms Erdos585.QB6C02PartialFactor.p4_no_quartic_shape
#check Erdos585.QB6C02PartialFactor.p4_no_quartic_shape
example : P4NoQuarticShape.{u} := p4_no_quartic_shape

end Erdos585.QB6C02PartialFactor

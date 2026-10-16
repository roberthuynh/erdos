import R643Bridge
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.QB7TwoDegreeFourR676
open QB4 QB7SmallLobeR643
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Original tight tail properties to be derived from a failed fixed pair.
This records a support, not an assumed factor or replacement graph. -/
structure Tail (G : SimpleGraph V) [DecidableRel G.Adj]
    (U P K : Finset V) (z : V) where
  X : Finset V
  Y : Finset V
  left : X ⊆ P
  right : Y ⊆ K
  omitted : z ∈ Y
  scar : df G U Y = 2
  balance : (#X : ℤ) - #Y = 2
  potential : gv G X Y = 16
  closed : ∀ x ∈ U, ∀ y ∈ Y, G.Adj x y → x ∈ X

omit [DecidableEq V] in
lemma degree_of_closed {U X Y : Finset V} (hX : X ⊆ U)
    (hc : ∀ x ∈ U, ∀ y ∈ Y, G.Adj x y → x ∈ X) {y : V} (hy : y ∈ Y) :
    dg G X y = dg G U y := by
  unfold dg
  congr 1
  ext x
  simp only [mem_filter]
  constructor
  · exact fun hx => ⟨hX hx.1,hx.2⟩
  · exact fun hx => ⟨hc x hx.1 y hy (G.adj_symm hx.2),hx.2⟩

lemma Tail.other_six {U W P K : Finset V} {z : V} (t : Tail G U P K z)
    (hi : U2Input G U W) (hK : K ⊆ W) (hz : dg G U z = 4)
    {y : V} (hy : y ∈ t.Y) (hne : y ≠ z) : dg G U y = 6 := by
  have he : df G U (t.Y.erase z) + (6 - (dg G U z : ℤ)) = df G U t.Y :=
    sum_erase_add t.Y (fun v => 6 - (dg G U v : ℤ)) t.omitted
  have hzero : df G U (t.Y.erase z) = 0 := by rw [hz,t.scar] at he; omega
  exact dg_eq_six_of_df_eq_zero
    (fun v hv => hi.capW v (hK (t.right (mem_erase.mp hv).2))) hzero
    (mem_erase.mpr ⟨hne,hy⟩)

lemma Tail.large {U W P K : Finset V} {z : V} (t : Tail G U P K z)
    (hi : U2Input G U W) (hP : P ⊆ U) (hK : K ⊆ W)
    (hz : dg G U z = 4) : 6 ≤ #t.X ∧ 4 ≤ #t.Y := by
  have hdz := degree_of_closed (t.left.trans hP) t.closed t.omitted
  have hfour := dg_le_card (G := G) t.X z
  have hy2 : 2 ≤ #t.Y := by have := t.balance; omega
  have hn : (t.Y.erase z).Nonempty := by
    have he := card_erase_add_one t.omitted
    exact card_pos.mp (by omega)
  obtain ⟨y,hy⟩ := hn
  have hsix := t.other_six hi hK hz (mem_erase.mp hy).2 (mem_erase.mp hy).1
  have hdy := degree_of_closed (t.left.trans hP) t.closed (mem_erase.mp hy).2
  have hb := dg_le_card (G := G) t.X y
  constructor <;> have := t.balance <;> omega

lemma Tail.internal_three {U W S U₁ U₂ W₁ W₂ : Finset V} {z x : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (t : Tail G U U₁ W₁ z) (hz : dg G U z = 4) (hx : x ∈ t.X) :
    3 ≤ dg G t.Y x := by
  have hn := t.large hi h.subsets.1 h.subsets.2.2.1 hz
  have hcard := card_erase_add_one hx
  have hf := h.local_floor hi ((erase_subset x t.X).trans t.left)
    (t.right.trans subset_union_left) (by omega)
  have he := gv_erase_left (G := G) hx t.Y
  rw [t.potential] at he
  omega

lemma Tail.distinct_right_disjoint {U W S U₁ U₂ W₁ W₂ : Finset V} {z z' : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (t : Tail G U U₁ W₁ z) (t' : Tail G U U₁ W₁ z')
    (hz : dg G U z = 4) (hz' : dg G U z' = 4) (hne : z ≠ z') :
    Disjoint t.Y t'.Y := by
  apply disjoint_left.mpr
  intro y hy hy'
  have hyz : y ≠ z := by
    intro he
    have hs := t'.other_six hi h.subsets.2.2.1 hz' hy' (he.symm ▸ hne)
    rw [he,hz] at hs
    omega
  have hs := t.other_six hi h.subsets.2.2.1 hz hy hyz
  have hc : ∀ x ∈ U, ∀ v ∈ t.Y ∩ t'.Y, G.Adj x v → x ∈ t.X ∩ t'.X := by
    intro x hx v hv ha
    exact mem_inter.mpr ⟨t.closed x hx v (mem_inter.mp hv).1 ha,
      t'.closed x hx v (mem_inter.mp hv).2 ha⟩
  have hX : t.X ∩ t'.X ⊆ U₁ := inter_subset_left.trans t.left
  have hY : t.Y ∩ t'.Y ⊆ W₁ := inter_subset_left.trans t.right
  have hd := degree_of_closed (hX.trans h.subsets.1) hc (mem_inter.mpr ⟨hy,hy'⟩)
  have hbound := dg_le_card (G := G) (t.X ∩ t'.X) y
  have hf := h.local_floor hi hX (hY.trans subset_union_left) (by omega)
  have hdf : df G (t.X ∩ t'.X) (t.Y ∩ t'.Y) = 0 := by
    unfold df
    apply sum_eq_zero
    intro v hv
    have hvz : v ≠ z := by
      intro he
      have h6 := t'.other_six hi h.subsets.2.2.1 hz' (mem_inter.mp hv).2 (he.symm ▸ hne)
      rw [he,hz] at h6
      omega
    have h6 := t.other_six hi h.subsets.2.2.1 hz (mem_inter.mp hv).1 hvz
    have he := degree_of_closed (hX.trans h.subsets.1) hc hv
    rw [he,h6]
    norm_num
  have hpot := gv_eq_left (G := G) (t.X ∩ t'.X) (t.Y ∩ t'.Y)
  rw [hdf] at hpot
  have h18 : 18 ≤ gv G (t.X ∩ t'.X) (t.Y ∩ t'.Y) := by omega
  have hlarge := t.large hi h.subsets.1 h.subsets.2.2.1 hz
  have hunion := h.local_floor hi (union_subset t.left t'.left)
    ((union_subset t.right t'.right).trans subset_union_left)
    (by have := card_le_card (subset_union_left : t.X ⊆ t.X ∪ t'.X); omega)
  have hsub := gv_union_add_gv_inter_le (G := G) t.X t'.X t.Y t'.Y
  rw [t.potential,t'.potential] at hsub
  omega

/-- Two distinct original degree-four omissions cannot both have tight original
scarred-lobe tails containing the same original degree-five vertex. -/
theorem no_two_degreefive_tails {U W S U₁ U₂ W₁ W₂ : Finset V} {z z' u0 : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (t : Tail G U U₁ W₁ z) (t' : Tail G U U₁ W₁ z')
    (hz : dg G U z = 4) (hz' : dg G U z' = 4) (hne : z ≠ z')
    (hu : u0 ∈ t.X) (hu' : u0 ∈ t'.X) (hd : dg G W u0 = 5) : False := by
  have hdis := t.distinct_right_disjoint h hi t' hz hz' hne
  have h3 := t.internal_three h hi hz hu
  have h3' := t'.internal_three h hi hz' hu'
  have he := dg_union_of_disjoint (G := G) hdis u0
  have hmono := dg_mono (G := G)
    ((union_subset t.right t'.right).trans h.subsets.2.2.1) u0
  omega

#print axioms no_two_degreefive_tails
end Erdos585.QB7TwoDegreeFourR676

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.QB7TwoDegreeFourR676
open QB4 QB7SmallLobeR643
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Scalar consequences of an actual original lobe cut with separator trace two.
The following theorem derives this record from original supports and the floor. -/
structure TwoBounds (d eps b c v : ℤ) : Prop where
  eps_nonneg : 0 ≤ eps
  eps_le : eps ≤ 1
  v_nonneg : 0 ≤ v
  value : c = b - v
  cap : -4*d ≤ c
  scar : 2*d+2-eps ≤ b
  base : 4 ≤ b
  zero_base : d = 0 → 5-eps ≤ b
  pos_base : 1 ≤ d → 6-eps ≤ b
  large_base : 3 ≤ d → 8-eps ≤ b
  floor : 0 ≤ d → 2-d-eps ≤ c
  equality : 1 ≤ d → b = 6-eps → d = 2 ∨ (d = 1 ∧ 2-eps ≤ c)

lemma original_two_bounds {U W S U₁ U₂ W₁ W₂ X Y Q : Finset V} {z : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hX : X ⊆ U₁) (hY : Y ⊆ W₁) (hz : z ∈ Y) (hdz : dg G U z = 4)
    (hQ : Q ⊆ S) (hq : #Q = 2) :
    TwoBounds ((#X : ℤ)-#Y) (df G W X)
      (2*#X+4*#Y-df G W X-ec G X Y)
      (2*#X+4*#Y-df G W X-ec G X Y-ec G X Q) (ec G X Q) := by
  let eps := df G W X
  let d : ℤ := (#X : ℤ)-#Y
  let b : ℤ := 2*#X+4*#Y-eps-ec G X Y
  let c : ℤ := b-ec G X Q
  have hXu := hX.trans h.subsets.1
  have hYw := hY.trans h.subsets.2.2.1
  have hQw := hQ.trans h.separator
  have heps : 0 ≤ eps ∧ eps ≤ 1 := by
    have hn := df_nonneg (G := G) (fun x hx => hi.capU x (hXu hx))
    have hb := df_le_of_subset (G := G) hXu hi.capU
    rw [hi.defU] at hb
    exact ⟨hn,hb⟩
  have hepsid := df_eq (G := G) W X
  have hYQ : Disjoint Y Q := h.rightSep₁.mono hY hQ
  have hec := ec_union_right (G := G) hYQ X
  have hmono := ec_mono_right (G := G) X (union_subset hYw hQw)
  have hscar : 2 ≤ 6*(#Y : ℤ)-(ec G X Y : ℤ) := by
    have hs := df_le_of_subset (G := G) (singleton_subset_iff.mpr hz)
      (fun y hy => hi.capW y (hYw hy))
    simp only [df,sum_singleton] at hs
    change 6 - (dg G U z : ℤ) ≤ df G U Y at hs
    rw [hdz,df_eq,ec_comm Y U] at hs
    have hem := ec_mono_left (G := G) hXu Y
    omega
  have hypos : 1 ≤ #Y := card_pos.mpr ⟨z,hz⟩
  have hcap : -4*d ≤ c := by dsimp [c,b,d,eps] at *; omega
  have hfloor : 4 ≤ #X+#Y → 8-d-eps ≤ b := by
    intro hn
    have hf := h.local_floor hi hX (hY.trans subset_union_left) hn
    unfold gv at hf
    dsimp [d,b]
    omega
  have hbase : 4 ≤ b ∧
      (d = 0 → 5-eps ≤ b) ∧ (1 ≤ d → 6-eps ≤ b) ∧
      (3 ≤ d → 8-eps ≤ b) := by
    have hbscar : 2*d+2-eps ≤ b := by dsimp [d,b]; omega
    have hbcap : -4*d ≤ b := by
      have hv0 : 0 ≤ (ec G X Q : ℤ) := by positivity
      dsimp [c] at hcap
      omega
    by_cases hn : 4 ≤ #X+#Y
    · have hf := hfloor hn
      constructor
      · by_cases hd : d ≤ -1 <;> omega
      constructor
      · intro hd; omega
      constructor
      · intro hd; omega
      · intro hd; omega
    · have hp := ec_product_bound (G := G) X Y
      have hx : #X ≤ 2 := by omega
      have hy : #Y ≤ 3 := by omega
      dsimp [d,b] at hbscar hbcap ⊢
      interval_cases #X <;> interval_cases #Y <;> norm_num at hp ⊢ <;> omega
  have haug : 0 ≤ d → 2-d-eps ≤ c := by
    intro hd
    have hn : 4 ≤ #X+#(Y ∪ Q) := by
      rw [card_union_of_disjoint hYQ,hq]
      dsimp [d] at hd
      omega
    have hf := h.local_floor hi hX (union_subset (hY.trans subset_union_left) (hQ.trans subset_union_right)) hn
    unfold gv at hf
    rw [card_union_of_disjoint hYQ,hq,hec] at hf
    dsimp [d,b,c]
    omega
  refine ⟨heps.1,heps.2,by positivity,rfl,?_,?_,hbase.1,hbase.2.1,
    hbase.2.2.1,hbase.2.2.2,haug,?_⟩
  · exact hcap
  · omega
  · intro hd heq
    by_cases hd2 : d = 2
    · exact Or.inl hd2
    have hd1 : d = 1 := by
      by_cases hn : 4 ≤ #X+#Y
      · have hf := hfloor hn
        have hg := hbase.2.2.2
        by_cases hh : 3 ≤ d
        · have := hg hh; omega
        · omega
      · dsimp [d] at hd ⊢; omega
    right
    refine ⟨hd1,?_⟩
    have hn : ¬ 4 ≤ #X+#Y := by intro hn; have := hfloor hn; omega
    have hx2 : #X = 2 := by dsimp [d] at hd1; omega
    have hv := ec_product_bound (G := G) X Q
    rw [hx2,hq] at hv
    change 2-eps ≤ b-(ec G X Q : ℤ)
    omega

lemma TwoBounds.other_lower {d eps b c v : ℤ} (h : TwoBounds d eps b c v)
    (hv : v ≤ 12) : -2-eps ≤ c := by
  by_cases hd : d ≤ -1
  · have := h.cap; have := h.eps_nonneg; omega
  · have hf := h.floor (by omega)
    have hs := h.scar
    have he := h.value
    omega

lemma two_failure_classification {d₁ e₁ b₁ c₁ v₁ d₂ e₂ b₂ c₂ v₂ : ℤ}
    (h₁ : TwoBounds d₁ e₁ b₁ c₁ v₁) (h₂ : TwoBounds d₂ e₂ b₂ c₂ v₂)
    (he : e₁+e₂ ≤ 1) (hv : v₁+v₂ ≤ 12) (hneg : c₁+c₂ < 0) :
    d₁ = 2 ∧ d₂ = 2 ∧ e₁+e₂ = 1 ∧ b₁ = 6-e₁ ∧ b₂ = 6-e₂ ∧ v₁+v₂ = 12 := by
  have hp : ∀ (d e b c v d' e' b' c' v' : ℤ),
      TwoBounds d e b c v → TwoBounds d' e' b' c' v' → e+e' ≤ 1 →
      v+v' ≤ 12 → c+c' < 0 → 1 ≤ d := by
    intro d e b c v d' e' b' c' v' h h' he hv hn
    have hl := h'.other_lower (by have := h.v_nonneg; omega)
    have hc := h.cap
    have hc' := h'.cap
    have he0 := h.eps_nonneg
    have he0' := h'.eps_nonneg
    by_cases hd : d ≤ -1
    · omega
    by_contra hpos
    have hd : d = 0 := by omega
    have hf := h.floor (by omega)
    have hb := h.zero_base hd
    have hf' := h'.floor
    have hb' := h'.large_base
    have heq := h.value
    have heq' := h'.value
    by_cases hdp : 3 ≤ d'
    · have := hb' hdp; omega
    · by_cases hdn : 0 ≤ d'
      · have := hf' hdn; omega
      · omega
  have hd₁ := hp d₁ e₁ b₁ c₁ v₁ d₂ e₂ b₂ c₂ v₂ h₁ h₂ he hv hneg
  have hd₂ := hp d₂ e₂ b₂ c₂ v₂ d₁ e₁ b₁ c₁ v₁ h₂ h₁ (by omega) (by omega) (by omega)
  have hb₁ := h₁.pos_base hd₁
  have hb₂ := h₂.pos_base hd₂
  have hv₁ := h₁.value
  have hv₂ := h₂.value
  have hbe₁ : b₁ = 6-e₁ := by omega
  have hbe₂ : b₂ = 6-e₂ := by omega
  have hde₁ := h₁.equality hd₁ hbe₁
  have hde₂ := h₂.equality hd₂ hbe₂
  have hf₁ := h₁.floor (by omega)
  have hf₂ := h₂.floor (by omega)
  rcases hde₁ with hd1|⟨hd1,hc1⟩
  · rcases hde₂ with hd2|⟨hd2,hc2⟩
    · exact ⟨hd1,hd2,by omega,hbe₁,hbe₂,by omega⟩
    · omega
  · rcases hde₂ with hd2|⟨hd2,hc2⟩ <;> omega


lemma original_scarred_vertex {U W X : Finset V} {u0 : V}
    (hi : U2Input G U W) (hX : X ⊆ U) (hu : u0 ∈ U)
    (hd : dg G W u0 = 5) :
    df G W (U.erase u0) = 0 ∧ (df G W X = 1 → u0 ∈ X) := by
  have he : df G W (U.erase u0) + (6-(dg G W u0 : ℤ)) = df G W U :=
    sum_erase_add U (fun x => 6-(dg G W x : ℤ)) hu
  rw [hd,hi.defU] at he
  have hz : df G W (U.erase u0) = 0 := by omega
  refine ⟨hz,?_⟩
  intro hx
  by_contra hn
  have hsub : X ⊆ U.erase u0 := by
    intro x hxx
    exact mem_erase.mpr ⟨fun heq => hn (heq ▸ hxx),hX hxx⟩
  have hl := df_le_of_subset (G := G) hsub
    (fun x hxx => hi.capU x (mem_erase.mp hxx).2)
  omega

lemma tight_support_tail {U W S U₁ U₂ W₁ W₂ X Y : Finset V} {z : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hX : X ⊆ U₁) (hY : Y ⊆ W₁) (hz : z ∈ Y) (hdz : dg G U z = 4)
    (hd : (#X : ℤ)-#Y = 2)
    (hb : 2*#X+4*#Y-df G W X-ec G X Y = 6-df G W X) :
    ∃ t : Tail G U U₁ W₁ z, t.X = X ∧ t.Y = Y := by
  have hXu := hX.trans h.subsets.1
  have hYw := hY.trans h.subsets.2.2.1
  have hs : 2 ≤ df G U Y := by
    have hh := df_le_of_subset (G := G) (singleton_subset_iff.mpr hz)
      (fun y hy => hi.capW y (hYw hy))
    simp only [df,sum_singleton] at hh
    change 6-(dg G U z : ℤ) ≤ df G U Y at hh
    rw [hdz] at hh
    omega
  have he := ec_sdiff_add_left (G := G) hXu Y
  have hdf := df_eq (G := G) U Y
  have hcomm := ec_comm (G := G) Y U
  have hzero : ec G (U \ X) Y = 0 := by omega
  have hscar : df G U Y = 2 := by omega
  have hclosed : ∀ x ∈ U, ∀ y ∈ Y, G.Adj x y → x ∈ X := by
    intro x hx y hy ha
    by_contra hnx
    have hxd : x ∈ U \ X := mem_sdiff.mpr ⟨hx,hnx⟩
    have hdzero : dg G Y x = 0 :=
      (sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hzero x hxd
    have hpos : 0 < dg G Y x := by
      exact card_pos.mpr ⟨y,mem_filter.mpr ⟨hy,ha⟩⟩
    omega
  have hpot : gv G X Y = 16 := by unfold gv; omega
  exact ⟨⟨X,Y,hX,hY,hz,hscar,hd,hpot,hclosed⟩,rfl,rfl⟩

/-- Every negative original trace-two cut supplies a scarred-lobe tight tail
containing the unique original degree-five vertex. -/
theorem trace_two_failure_tail
    {U W S U₁ U₂ W₁ W₂ X₁ X₂ Y₁ Y₂ Q : Finset V} {z₁ z₂ u0 : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hX₁ : X₁ ⊆ U₁) (hX₂ : X₂ ⊆ U₂)
    (hY₁ : Y₁ ⊆ W₁) (hY₂ : Y₂ ⊆ W₂)
    (hz₁ : z₁ ∈ Y₁) (hz₂ : z₂ ∈ Y₂)
    (hd₁ : dg G U z₁ = 4) (hd₂ : dg G U z₂ = 4)
    (hQ : Q ⊆ S) (hq : #Q = 2)
    (hneg : (2*(#X₁ : ℤ)+4*#Y₁-df G W X₁-ec G X₁ Y₁-ec G X₁ Q)+
      (2*(#X₂ : ℤ)+4*#Y₂-df G W X₂-ec G X₂ Y₂-ec G X₂ Q) < 0) :
    ∃ t : Tail G U U₁ W₁ z₁, t.X = X₁ ∧ t.Y = Y₁ ∧ u0 ∈ t.X := by
  have h₁ := original_two_bounds h hi hX₁ hY₁ hz₁ hd₁ hQ hq
  have h₂ := original_two_bounds h.swap hi hX₂ hY₂ hz₂ hd₂ hQ hq
  have hscar := original_scarred_vertex hi (hX₁.trans h.subsets.1) (h.subsets.1 hu) hdu
  have hX₂u : X₂ ⊆ U.erase u0 := by
    intro x hx
    exact mem_erase.mpr ⟨fun heq => disjoint_left.mp h.leftDisjoint hu (heq ▸ hX₂ hx),
      h.subsets.2.1 (hX₂ hx)⟩
  have he₂ : df G W X₂ = 0 := by
    have hn := df_nonneg (G := G) (fun x hx => hi.capU x (h.subsets.2.1 (hX₂ hx)))
    have hl := df_le_of_subset (G := G) hX₂u
      (fun x hx => hi.capU x (mem_erase.mp hx).2)
    omega
  have hv : (ec G X₁ Q : ℤ)+ec G X₂ Q ≤ 12 := by
    have he := ec_union_left (G := G) h.leftDisjoint Q
    rw [h.leftCover] at he
    have hl := ec_mono_left (G := G) hX₁ Q
    have hr := ec_mono_left (G := G) hX₂ Q
    have hc := ec_le_six_mul (G := G) (fun q hqq => hi.capW q (h.separator (hQ hqq)))
    have hcomm := ec_comm (G := G) Q U
    rw [hq] at hc
    omega
  have ht := two_failure_classification h₁ h₂ (by have := h₁.eps_le; omega) hv hneg
  have he₁ : df G W X₁ = 1 := by omega
  obtain ⟨t,htX,htY⟩ := tight_support_tail h hi hX₁ hY₁ hz₁ hd₁ ht.1 ht.2.2.2.1
  exact ⟨t,htX,htY,htX ▸ hscar.2 he₁⟩

#print axioms trace_two_failure_tail

#print axioms original_two_bounds
#print axioms two_failure_classification
end Erdos585.QB7TwoDegreeFourR676

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.QB7TwoDegreeFourR676
open QB4 QB7SmallLobeR643
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def cutCost (G : SimpleGraph V) [DecidableRel G.Adj]
    (W X Y Q : Finset V) : ℤ :=
  2*#X+4*#Y-df G W X-ec G X Y-ec G X Q

lemma original_base_bounds {U W S U₁ U₂ W₁ W₂ X Y : Finset V} {z : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hX : X ⊆ U₁) (hY : Y ⊆ W₁) (hz : z ∈ Y) (hdz : dg G U z = 4) :
    ∃ Q ⊆ S, #Q = 2 ∧ TwoBounds ((#X : ℤ)-#Y) (df G W X)
      (2*#X+4*#Y-df G W X-ec G X Y)
      (cutCost G W X Y Q) (ec G X Q) := by
  obtain ⟨Q,hQ,hq⟩ := exists_subset_card_eq (show 2 ≤ #S by rw [h.cardS]; omega)
  exact ⟨Q,hQ,hq,original_two_bounds h hi hX hY hz hdz hQ hq⟩

lemma original_single_trace_bounds {U W S U₁ U₂ W₁ W₂ X Y Q : Finset V} {z : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hX : X ⊆ U₁) (hY : Y ⊆ W₁) (hz : z ∈ Y) (hdz : dg G U z = 4)
    (hQ : Q ⊆ S) (hq : #Q = 1) :
    2-df G W X ≤ cutCost G W X Y Q ∧
    (cutCost G W X Y Q = 2-df G W X → (#X : ℤ)-#Y = 3) := by
  obtain ⟨Q',hQ',hq',hb⟩ := original_base_bounds h hi hX hY hz hdz
  let d : ℤ := (#X : ℤ)-#Y
  let eps := df G W X
  let b : ℤ := 2*#X+4*#Y-eps-ec G X Y
  let c := cutCost G W X Y Q
  have he : 0 ≤ eps ∧ eps ≤ 1 := ⟨hb.eps_nonneg,hb.eps_le⟩
  have hv : (ec G X Q : ℤ) ≤ 6 := by
    have hm := ec_mono_left (G := G) (hX.trans h.subsets.1) Q
    have hc := ec_le_six_mul (G := G) (fun q hqq => hi.capW q (h.separator (hQ hqq)))
    rw [hq] at hc
    have hcomm := ec_comm (G := G) Q U
    omega
  have hc : c = b-ec G X Q := rfl
  have hYQ := h.rightSep₁.mono hY hQ
  have hec := ec_union_right (G := G) hYQ X
  have hm := ec_mono_right (G := G) X
    (union_subset (hY.trans h.subsets.2.2.1) (hQ.trans h.separator))
  have hd := df_eq (G := G) W X
  have hcap : -4*d ≤ c := by dsimp [c,cutCost,d,b,eps] at *; omega
  have hypos : 1 ≤ #Y := card_pos.mpr ⟨z,hz⟩
  have hfloor : 4 ≤ #X+#Y+#Q → 5-d-eps ≤ c := by
    intro hn
    have hf := h.local_floor hi hX
      (union_subset (hY.trans subset_union_left) (hQ.trans subset_union_right))
      (by rw [card_union_of_disjoint hYQ]; omega)
    unfold gv at hf
    rw [card_union_of_disjoint hYQ,hq,hec] at hf
    dsimp [c,cutCost,d,eps]
    omega
  have hzero : d = 0 → 4-eps ≤ c := by
    intro hdzero
    by_cases hn : 4 ≤ #X+#Y+#Q
    · have hf := hfloor hn; omega
    · have hx1 : #X = 1 := by dsimp [d] at hdzero; omega
      have hy1 : #Y = 1 := by dsimp [d] at hdzero; omega
      have hp := ec_product_bound (G := G) X (Y ∪ Q)
      rw [card_union_of_disjoint hYQ,hq,hx1,hy1,hec] at hp
      dsimp [c,cutCost,eps]
      rw [hx1,hy1]
      omega
  have hposfloor : 1 ≤ d → 5-d-eps ≤ c := by
    intro hdp
    exact hfloor (by dsimp [d] at hdp; omega)
  have hbscar : 2*d+2-eps ≤ b := hb.scar
  have hfinal : 2-eps ≤ c ∧ (c = 2-eps → d = 3) := by
    by_cases hneg : d ≤ -1
    · constructor <;> omega
    by_cases hdzero : d = 0
    · have := hzero hdzero; constructor <;> omega
    have hf := hposfloor (by omega)
    constructor <;> omega
  exact hfinal

lemma original_single_trace_nonnegative
    {U W S U₁ U₂ W₁ W₂ X₁ X₂ Y₁ Y₂ Q : Finset V} {z₁ z₂ : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hX₁ : X₁ ⊆ U₁) (hX₂ : X₂ ⊆ U₂)
    (hY₁ : Y₁ ⊆ W₁) (hY₂ : Y₂ ⊆ W₂)
    (hz₁ : z₁ ∈ Y₁) (hz₂ : z₂ ∈ Y₂)
    (hd₁ : dg G U z₁ = 4) (hd₂ : dg G U z₂ = 4)
    (hQ : Q ⊆ S) (hq : #Q = 1) :
    4 ≤ cutCost G W X₁ Y₁ Q+cutCost G W X₂ Y₂ Q := by
  have h₁ := original_single_trace_bounds h hi hX₁ hY₁ hz₁ hd₁ hQ hq
  have h₂ := original_single_trace_bounds h.swap hi hX₂ hY₂ hz₂ hd₂ hQ hq
  have heps : df G W X₁+df G W X₂ ≤ 1 := by
    have hd : Disjoint X₁ X₂ := h.leftDisjoint.mono hX₁ hX₂
    have hs : X₁ ∪ X₂ ⊆ U := union_subset (hX₁.trans h.subsets.1) (hX₂.trans h.subsets.2.1)
    have he := df_le_of_subset (G := G) hs hi.capU
    unfold df at he
    rw [sum_union hd] at he
    change df G W X₁+df G W X₂ ≤ df G W U at he
    rw [hi.defU] at he
    exact he
  by_contra hn
  have hc₁ : cutCost G W X₁ Y₁ Q = 2-df G W X₁ := by omega
  have hc₂ : cutCost G W X₂ Y₂ Q = 2-df G W X₂ := by omega
  have hdX₁ := h₁.2 hc₁
  have hdX₂ := h₂.2 hc₂
  obtain ⟨Q',hQ',hq',hb₁⟩ := original_base_bounds h hi hX₁ hY₁ hz₁ hd₁
  obtain ⟨Q'',hQ'',hq'',hb₂⟩ := original_base_bounds h.swap hi hX₂ hY₂ hz₂ hd₂
  have hlarge₁ := hb₁.large_base (by omega)
  have hlarge₂ := hb₂.large_base (by omega)
  have hv : (ec G X₁ Q : ℤ)+ec G X₂ Q ≤ 6 := by
    have he := ec_union_left (G := G) h.leftDisjoint Q
    rw [h.leftCover] at he
    have hm₁ := ec_mono_left (G := G) hX₁ Q
    have hm₂ := ec_mono_left (G := G) hX₂ Q
    have hc := ec_le_six_mul (G := G) (fun q hqq => hi.capW q (h.separator (hQ hqq)))
    rw [hq] at hc
    have hcomm := ec_comm (G := G) Q U
    omega
  unfold cutCost at hc₁ hc₂ hn
  omega

lemma degreefour_budgets {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    {z₁ z₂ : V} (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ = 4) (hd₂ : dg G U z₂ = 4) :
    3 ≤ df G U (W₁.erase z₁) ∧ 3 ≤ df G U (W₂.erase z₂) ∧
    df G U (W₁.erase z₁)+df G U (W₂.erase z₂)+df G U S = 9 ∧
    0 ≤ df G U S := by
  have hpart : df G U W₁+df G U W₂+df G U S = 13 := by
    have he := hi.defW
    rw [← h.rightCover] at he
    unfold df at he ⊢
    rw [sum_union (disjoint_union_left.mpr ⟨h.rightSep₁,h.rightSep₂⟩),
      sum_union h.rightDisjoint] at he
    exact he
  have hlow₁ := h.interior_scar hi
  have hlow₂ := h.swap.interior_scar hi
  have he₁ : df G U (W₁.erase z₁)+(6-(dg G U z₁ : ℤ)) = df G U W₁ :=
    sum_erase_add W₁ (fun y => 6-(dg G U y : ℤ)) hz₁
  have he₂ : df G U (W₂.erase z₂)+(6-(dg G U z₂ : ℤ)) = df G U W₂ :=
    sum_erase_add W₂ (fun y => 6-(dg G U y : ℤ)) hz₂
  have hnon := df_nonneg (G := G) (fun s hs => hi.capW s (h.separator hs))
  rw [hd₁] at he₁
  rw [hd₂] at he₂
  omega

lemma degreefour_low_rank {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    {z₁ z₂ : V} (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ = 4) (hd₂ : dg G U z₂ = 4)
    {Y₁ Y₂ R : Finset V} (hY₁ : Y₁ ⊆ W₁.erase z₁) (hY₂ : Y₂ ⊆ W₂.erase z₂)
    (hR : R ⊆ S) (hr : #R ≤ 1) :
    4*(#R : ℤ) ≤ rankTerm G U₁ Y₁ R+rankTerm G U₂ Y₂ R := by
  have hb := degreefour_budgets h hi hz₁ hz₂ hd₁ hd₂
  have hdY₁ := df_le_of_subset (G := G) hY₁
    (fun y hy => hi.capW y (h.subsets.2.2.1 (mem_erase.mp hy).2))
  have hdY₂ := df_le_of_subset (G := G) hY₂
    (fun y hy => hi.capW y (h.subsets.2.2.2 (mem_erase.mp hy).2))
  have hdR := df_le_of_subset (G := G) hR (fun s hs => hi.capW s (h.separator hs))
  have hdRcap : df G U R ≤ 2*#R := by
    unfold df
    calc _ ≤ ∑ _s ∈ R, (2 : ℤ) := sum_le_sum fun s hs => by
            have := hi.minW s (h.separator (hR hs)); omega
      _ = _ := by simp [mul_comm]
  have hfirst := h.capped_rank_lower hi (hY₁.trans (erase_subset z₁ W₁)) hR
  have hsecond := h.swap.capped_rank_lower hi (hY₂.trans (erase_subset z₂ W₂)) hR
  have he := ec_union_left (G := G) h.leftDisjoint R
  rw [h.leftCover] at he
  have hid := df_eq (G := G) U R
  have hcomm := ec_comm (G := G) R U
  by_cases hr0 : #R = 0
  · have hm₁ : max 0 (df G U Y₁+2*#R-6) = 0 := max_eq_left (by omega)
    have hm₂ : max 0 (df G U Y₂+2*#R-6) = 0 := max_eq_left (by omega)
    rw [hm₁] at hfirst
    rw [hm₂] at hsecond
    omega
  · have hr1 : #R = 1 := by omega
    have hloss : max 0 (df G U Y₁+2*#R-6)+max 0 (df G U Y₂+2*#R-6) ≤ 2-df G U R := by
      simp only [max_def]
      split_ifs <;> omega
    omega

lemma local_cost_of_partition {U W S U₁ U₂ W₁ W₂ Y R X : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hY : Y ⊆ W₁) (hR : R ⊆ S) (hX : X ⊆ U₁)
    (he : capped G U₁ (Y ∪ R) = ec G X (Y ∪ R)+4*#(U₁ \ X)) :
    cutCost G W X (W₁ \ Y) (S \ R) = rankTerm G U₁ Y R-4 := by
  have hbalance := h.local_balance hi
  have hxcard := card_sdiff_add_card_eq_card hX
  have hycard := card_sdiff_add_card_eq_card hY
  have hXdegree : ec G X (W₁ ∪ S) = ec G X W := by
    unfold ec
    exact sum_congr rfl fun x hx => h.degree_left (hX hx)
  have hfull := ec_union_right (G := G) h.rightSep₁ X
  have hy := ec_sdiff_add_right (G := G) hY X
  have hr := ec_sdiff_add_right (G := G) hR X
  have hyr := ec_union_right (G := G) (h.rightSep₁.mono hY hR) X
  have hdf := df_eq (G := G) W X
  unfold cutCost rankTerm
  omega

#print axioms original_single_trace_nonnegative
#print axioms degreefour_low_rank
#print axioms local_cost_of_partition
end Erdos585.QB7TwoDegreeFourR676

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
namespace Erdos585.QB7TwoDegreeFourR676
open QB4 QB7SmallLobeR643
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma failed_pair_rank_cut {U W S U₁ U₂ W₁ W₂ : Finset V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    {z₁ z₂ : V} (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hfail : ¬ FixedOmissionFactor G U W z₁ z₂) :
    ∃ Y₁ Y₂ R : Finset V, Y₁ ⊆ W₁.erase z₁ ∧ Y₂ ⊆ W₂.erase z₂ ∧ R ⊆ S ∧
      rankTerm G U₁ Y₁ R+rankTerm G U₂ Y₂ R < 4*(#R : ℤ) := by
  have hex : ∃ T ⊆ (W.erase z₁).erase z₂, capped G U T < 4*#T := by
    by_contra hn
    push Not at hn
    exact hfail (factor_of_right_capped (h.retained_balanced hi hz₁ hz₂) hn)
  obtain ⟨T,hT,hbad⟩ := hex
  let Y₁ := T ∩ W₁.erase z₁
  let Y₂ := T ∩ W₂.erase z₂
  let R := T ∩ S
  have hY₁ : Y₁ ⊆ W₁.erase z₁ := inter_subset_right
  have hY₂ : Y₂ ⊆ W₂.erase z₂ := inter_subset_right
  have hR : R ⊆ S := inter_subset_right
  have hY₁K : Y₁ ⊆ W₁ := hY₁.trans (erase_subset z₁ W₁)
  have hY₂K : Y₂ ⊆ W₂ := hY₂.trans (erase_subset z₂ W₂)
  have hY₁₂ : Disjoint Y₁ Y₂ := h.rightDisjoint.mono hY₁K hY₂K
  have hY₁R : Disjoint Y₁ R := h.rightSep₁.mono hY₁K hR
  have hY₂R : Disjoint Y₂ R := h.rightSep₂.mono hY₂K hR
  have hcover : Y₁ ∪ Y₂ ∪ R = T := by
    ext x
    constructor
    · intro hx
      rcases mem_union.mp hx with hxy|hxr
      · rcases mem_union.mp hxy with hx1|hx2
        · exact (mem_inter.mp hx1).1
        · exact (mem_inter.mp hx2).1
      · exact (mem_inter.mp hxr).1
    · intro hx
      have hxQ := hT hx
      rw [h.retained_cover hz₁ hz₂] at hxQ
      rcases mem_union.mp hxQ with hx12|hxs
      · rcases mem_union.mp hx12 with hx1|hx2
        · exact mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨hx,hx1⟩))
        · exact mem_union_left _ (mem_union_right _ (mem_inter.mpr ⟨hx,hx2⟩))
      · exact mem_union_right _ (mem_inter.mpr ⟨hx,hxs⟩)
  have hcard : #T = #Y₁ + #Y₂ + #R := by
    rw [← hcover,card_union_of_disjoint (disjoint_union_left.mpr ⟨hY₁R,hY₂R⟩),
      card_union_of_disjoint hY₁₂]
  have hleft : ∀ x ∈ U₁, dg G T x = dg G (Y₁ ∪ R) x := by
    intro x hx
    have he : (Y₁ ∪ R) ∪ Y₂ = T := by
      rw [union_assoc,union_comm R Y₂,← union_assoc,hcover]
    have hd := dg_union_of_disjoint (G := G)
      (disjoint_union_left.mpr ⟨hY₁₂,hY₂R.symm⟩) x
    have hz : dg G Y₂ x = 0 := dg_zero fun y hy => h.cross₁ x hx y (hY₂K hy)
    rw [he,hz] at hd
    omega
  have hright : ∀ x ∈ U₂, dg G T x = dg G (Y₂ ∪ R) x := by
    intro x hx
    have he : (Y₂ ∪ R) ∪ Y₁ = T := by
      rw [union_assoc,union_comm R Y₁,← union_assoc,union_comm Y₂ Y₁,hcover]
    have hd := dg_union_of_disjoint (G := G)
      (disjoint_union_left.mpr ⟨hY₁₂.symm,hY₁R.symm⟩) x
    have hz : dg G Y₁ x = 0 := dg_zero fun y hy => h.cross₂ x hx y (hY₁K hy)
    rw [he,hz] at hd
    omega
  have hcap : capped G U T = capped G U₁ (Y₁ ∪ R) + capped G U₂ (Y₂ ∪ R) := by
    unfold capped
    rw [← h.leftCover,sum_union h.leftDisjoint]
    congr 1
    · exact sum_congr rfl fun x hx => by rw [hleft x hx]
    · exact sum_congr rfl fun x hx => by rw [hright x hx]
  refine ⟨Y₁,Y₂,R,hY₁,hY₂,hR,?_⟩
  unfold rankTerm
  omega

/-- Any actual failed original degree-four cross pair yields a tight original
scarred-lobe tail containing the original degree-five vertex. All separator
trace widths are checked before extracting the trace-two equality tail. -/
theorem failed_pair_tail {U W S U₁ U₂ W₁ W₂ : Finset V} {z₁ z₂ u0 : V}
    (h : Split G U W S U₁ U₂ W₁ W₂) (hi : U2Input G U W)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hz₁ : z₁ ∈ W₁) (hz₂ : z₂ ∈ W₂)
    (hd₁ : dg G U z₁ = 4) (hd₂ : dg G U z₂ = 4)
    (hfail : ¬ FixedOmissionFactor G U W z₁ z₂) :
    ∃ t : Tail G U U₁ W₁ z₁, u0 ∈ t.X := by
  obtain ⟨Y₁,Y₂,R,hY₁,hY₂,hR,hneg⟩ := failed_pair_rank_cut h hi hz₁ hz₂ hfail
  have hrmax : #R ≤ 4 := by have := card_le_card hR; rw [h.cardS] at this; exact this
  have hrlo : ¬ #R ≤ 1 := by
    intro hr
    have hc := degreefour_low_rank h hi hz₁ hz₂ hd₁ hd₂ hY₁ hY₂ hR hr
    omega
  have hr4 : #R ≠ 4 := by
    intro hr
    have he : R = S := eq_of_subset_of_card_le hR (by rw [h.cardS]; omega)
    have hc₁ := h.rank_full hi hz₁ (by omega) hY₁
    have hc₂ := h.swap.rank_full hi hz₂ (by omega) hY₂
    rw [← he] at hc₁ hc₂
    omega
  obtain ⟨X₁,hX₁,he₁⟩ := capped_partition (G := G) U₁ (Y₁ ∪ R)
  obtain ⟨X₂,hX₂,he₂⟩ := capped_partition (G := G) U₂ (Y₂ ∪ R)
  let B₁ := W₁ \ Y₁
  let B₂ := W₂ \ Y₂
  let Q := S \ R
  have hB₁ : B₁ ⊆ W₁ := sdiff_subset
  have hB₂ : B₂ ⊆ W₂ := sdiff_subset
  have hQ : Q ⊆ S := sdiff_subset
  have hY₁K := hY₁.trans (erase_subset z₁ W₁)
  have hY₂K := hY₂.trans (erase_subset z₂ W₂)
  have hzB₁ : z₁ ∈ B₁ := mem_sdiff.mpr ⟨hz₁,fun hh => (mem_erase.mp (hY₁ hh)).1 rfl⟩
  have hzB₂ : z₂ ∈ B₂ := mem_sdiff.mpr ⟨hz₂,fun hh => (mem_erase.mp (hY₂ hh)).1 rfl⟩
  have hc₁ := local_cost_of_partition h hi hY₁K hR hX₁ he₁
  have hc₂ := local_cost_of_partition h.swap hi hY₂K hR hX₂ he₂
  have hcard := card_sdiff_add_card_eq_card hR
  rw [h.cardS] at hcard
  have hr3 : #R ≠ 3 := by
    intro hr
    have hq : #Q = 1 := by dsimp [Q]; omega
    have hc := original_single_trace_nonnegative h hi hX₁ hX₂ hB₁ hB₂ hzB₁ hzB₂ hd₁ hd₂ hQ hq
    dsimp [B₁,B₂,Q] at hc
    omega
  have hr2 : #R = 2 := by omega
  have hq : #Q = 2 := by dsimp [Q]; omega
  have hnegative : cutCost G W X₁ B₁ Q+cutCost G W X₂ B₂ Q < 0 := by
    dsimp [B₁,B₂,Q]
    omega
  obtain ⟨t,htX,htY,htu⟩ := trace_two_failure_tail h hi hu hdu hX₁ hX₂ hB₁ hB₂
    hzB₁ hzB₂ hd₁ hd₂ hQ hq hnegative
  exact ⟨t,htu⟩

/-- Literal original U2Input endpoint: with two distinct original degree-four
choices in the scarred lobe, at least one fixed cross pair leaves an actual
original unit-edge quartic on all U and all W except that same pair. -/
theorem original_two_degreefour_choices
    {U W S U₁ U₂ W₁ W₂ : Finset V} {z₁ z₁' z₂ u0 : V}
    (hi : QB7Conditional.U2Input G U W) (h : Split G U W S U₁ U₂ W₁ W₂)
    (hu : u0 ∈ U₁) (hdu : dg G W u0 = 5)
    (hz₁ : z₁ ∈ W₁) (hz₁' : z₁' ∈ W₁) (hne : z₁ ≠ z₁')
    (hz₂ : z₂ ∈ W₂) (hd₁ : dg G U z₁ = 4) (hd₁' : dg G U z₁' = 4)
    (hd₂ : dg G U z₂ = 4) :
    FixedOmissionFactor G U W z₁ z₂ ∨ FixedOmissionFactor G U W z₁' z₂ := by
  classical
  have hi' := U2Input.of_original hi
  by_contra hn
  push Not at hn
  obtain ⟨t,htu⟩ := failed_pair_tail h hi' hu hdu hz₁ hz₂ hd₁ hd₂ hn.1
  obtain ⟨t',ht'u⟩ := failed_pair_tail h hi' hu hdu hz₁' hz₂ hd₁' hd₂ hn.2
  exact no_two_degreefive_tails h hi' t t' hd₁ hd₁' hne htu ht'u hdu

#print axioms original_two_degreefour_choices
#print original_two_degreefour_choices
end Erdos585.QB7TwoDegreeFourR676

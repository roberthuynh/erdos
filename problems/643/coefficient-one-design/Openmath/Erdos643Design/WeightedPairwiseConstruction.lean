import Openmath.Erdos643Design.NormalizedPencil
import Openmath.Erdos643Design.SharedGroupCompletion

/-! Weighted design assembly from actual local designs and a pairwise balanced design. -/
set_option autoImplicit false
namespace Erdos643Design.WeightedPairwiseConstruction
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

def groupBlock (i : I) : Finset (Option (I × Fin 4)) :=
  insert none (univ.image (fun a : Fin 4 => some (i,a)))

omit [Fintype I] in
@[simp] theorem none_groupBlock (i : I) : none ∈ groupBlock i := by simp [groupBlock]
omit [Fintype I] in
@[simp] theorem some_groupBlock (i j : I) (a : Fin 4) :
    some (i,a) ∈ groupBlock j ↔ i = j := by simp [groupBlock, eq_comm]

theorem pair_unique {W : Type*} [DecidableEq W] {H : Finset (Finset W)}
    (hH : H.IsBlockDesign 2 5) (x y : W) (hxy : x ≠ y) :
    ∃! b, b ∈ H ∧ x ∈ b ∧ y ∈ b := by
  obtain ⟨b,hb,hu⟩ := hH.2 {x,y} (by simp [hxy])
  refine ⟨b,⟨hb.1,hb.2 (by simp),hb.2 (by simp)⟩,?_⟩
  intro c hc
  exact hu c ⟨hc.1,by simpa only [insert_subset_iff,singleton_subset_iff] using hc.2⟩

omit [Fintype I] in
/-- The canonical pencil forces every non-pencil block to be transverse. -/
theorem residual_transverse (H : Finset (Finset (Option (I × Fin 4))))
    (hH : H.IsBlockDesign 2 5) (hg : ∀ i, groupBlock i ∈ H)
    {b : Finset (Option (I × Fin 4))} (hb : b ∈ H) (hn : none ∉ b)
    (i : I) (a c : Fin 4) (ha : some (i,a) ∈ b) (hc : some (i,c) ∈ b) : a = c := by
  by_contra hac
  obtain ⟨d,hd,hu⟩ := pair_unique hH (some (i,a)) (some (i,c)) (by simp [hac])
  have hb' : b = d := hu b ⟨hb,ha,hc⟩
  have hg' : groupBlock i = d := hu (groupBlock i) ⟨hg i,by simp,by simp⟩
  exact hn ((hb'.trans hg'.symm).symm ▸ none_groupBlock i)

omit [Fintype I] in
theorem cross_pair_avoids_none (H : Finset (Finset (Option (I × Fin 4))))
    (hH : H.IsBlockDesign 2 5) (hg : ∀ i, groupBlock i ∈ H)
    {b : Finset (Option (I × Fin 4))} (hb : b ∈ H)
    (i j : I) (hij : i ≠ j) (a c : Fin 4)
    (ha : some (i,a) ∈ b) (hc : some (j,c) ∈ b) : none ∉ b := by
  intro hn
  obtain ⟨d,hd,hu⟩ := pair_unique hH none (some (i,a)) (by simp)
  have hb' : b = d := hu b ⟨hb,hn,ha⟩
  have hg' : groupBlock i = d := hu (groupBlock i) ⟨hg i,by simp,by simp⟩
  have hc' : some (j,c) ∈ groupBlock i := (hb'.trans hg'.symm) ▸ hc
  exact hij ((some_groupBlock j i c).mp hc').symm

/-- Remove the canonical pencil, obtaining an actual finite cross-group family. -/
def residual (H : Finset (Finset (Option (I × Fin 4)))) : Finset (Finset (I × Fin 4)) :=
  (H.filter (fun b => none ∉ b)).image Finset.eraseNone

def residualCross (H : Finset (Finset (Option (I × Fin 4))))
    (hH : H.IsBlockDesign 2 5) (hg : ∀ i, groupBlock i ∈ H) :
    Foundation.SharedGroupCompletion.CrossDesign I (Fin 4) 5 where
  cross := residual H
  uniform := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hb
    obtain ⟨hcH,hcn⟩ := mem_filter.mp hc
    rw [card_eraseNone_of_not_mem hcn]
    exact hH.1 c hcH
  transverse := by
    intro b hb p hp q hq he
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hb
    obtain ⟨hcH,hcn⟩ := mem_filter.mp hc
    rcases p with ⟨i,a⟩
    rcases q with ⟨j,d⟩
    simp only at he
    subst j
    exact Prod.ext rfl (residual_transverse H hH hg hcH hcn i a d
      (mem_eraseNone.mp hp) (mem_eraseNone.mp hq))
  unique := by
    intro p q hpq
    obtain ⟨b,hb,hu⟩ := pair_unique hH (some p) (some q) (by
      intro he
      exact hpq (congrArg Prod.fst (Option.some.inj he)))
    have hn : none ∉ b := cross_pair_avoids_none H hH hg hb.1 p.1 q.1 hpq p.2 q.2
      hb.2.1 hb.2.2
    refine ⟨b.eraseNone,⟨mem_image.mpr ⟨b,mem_filter.mpr ⟨hb.1,hn⟩,rfl⟩,
      mem_eraseNone.mpr hb.2.1,mem_eraseNone.mpr hb.2.2⟩,?_⟩
    intro c hc
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hc.1
    have hd' : d = b := hu d ⟨(mem_filter.mp hd).1,
      mem_eraseNone.mp hc.2.1,mem_eraseNone.mp hc.2.2⟩
    exact congrArg Finset.eraseNone hd'

/-- Actual local designs supply the cross-group certificates after pencil normalization. -/
theorem local_cross_exists (D : Finset (Finset (Fin (4 * Fintype.card I + 1))))
    (hD : D.IsBlockDesign 2 5) :
    Nonempty (Foundation.SharedGroupCompletion.CrossDesign I (Fin 4) 5) := by
  obtain ⟨_,H,_,_,hH,hgroups⟩ := NormalizedPencil.normalized_pencil_exists (Fintype.card I) D hD
  let E : Option (Fin (Fintype.card I) × Fin 4) ≃ Option (I × Fin 4) :=
    Equiv.optionCongr (Equiv.prodCongr (Fintype.equivFin I).symm (Equiv.refl (Fin 4)))
  have hm : ∀ i : I,
      (NormalizedPencil.groupBlock (Fintype.equivFin I i)).map E.toEmbedding = groupBlock i := by
    intro i
    ext z
    rw [Finset.mem_map_equiv]
    cases z with
    | none => simp [E,NormalizedPencil.groupBlock,groupBlock]
    | some z =>
      rcases z with ⟨j,a⟩
      change some (Fintype.equivFin I j,a) ∈
        NormalizedPencil.groupBlock (Fintype.equivFin I i) ↔ some (j,a) ∈ groupBlock i
      simp [NormalizedPencil.groupBlock,groupBlock,eq_comm]
  have hg : ∀ i : I, groupBlock i ∈ DesignTransport.relabel E H := by
    intro i
    exact mem_image.mpr ⟨NormalizedPencil.groupBlock (Fintype.equivFin I i),
      hgroups _,hm i⟩
  exact ⟨residualCross _ (DesignTransport.isBlockDesign_relabel E H 2 5 hH) hg⟩

section Assembly
variable {V : Type*} [Fintype V] [DecidableEq V]

def parentEmbedding (b : Finset V) : (b × Fin 4) ↪ V × Fin 4 where
  toFun := fun p => (p.1.val,p.2)
  inj' := by
    rintro ⟨x,a⟩ ⟨y,c⟩ h
    change (x.val,a) = (y.val,c) at h
    exact Prod.ext (Subtype.ext (congrArg (fun z : V × Fin 4 => z.1) h))
      (congrArg (fun z : V × Fin 4 => z.2) h)

omit [Fintype V] [DecidableEq V] in
theorem lift_exact (b : Finset V) (c : Finset (b × Fin 4)) (v : b) (a : Fin 4) :
    (v.val,a) ∈ c.map (parentEmbedding b) ↔ (v,a) ∈ c :=
  Finset.mem_map' (parentEmbedding b) (a := (v,a)) (s := c)

omit [Fintype V] [DecidableEq V] in
theorem lift_support (b : Finset V) (c : Finset (b × Fin 4))
    {p : V × Fin 4} (hp : p ∈ c.map (parentEmbedding b)) : p.1 ∈ b := by
  obtain ⟨q,hq,he⟩ := mem_map.mp hp
  exact congrArg Prod.fst he ▸ q.1.property

omit [Fintype V] in
theorem parent_pair_unique (P : Finset (Finset V)) (hP : P.IsPairwiseBalancedDesign)
    (v w : V) (hvw : v ≠ w) : ∃! b, b ∈ P ∧ v ∈ b ∧ w ∈ b := by
  obtain ⟨b,hb,hu⟩ := hP.2 {v,w} (by simp [hvw])
  refine ⟨b,⟨hb.1,hb.2 (by simp),hb.2 (by simp)⟩,?_⟩
  intro c hc
  exact hu c ⟨hc.1,by simpa only [insert_subset_iff,singleton_subset_iff] using hc.2⟩

/-- Glue actual local cross families through the uniquely determined parent block. -/
def assembledCross (P : Finset (Finset V)) (hP : P.IsPairwiseBalancedDesign)
    (X : ∀ b : P, Foundation.SharedGroupCompletion.CrossDesign b.val (Fin 4) 5) :
    Foundation.SharedGroupCompletion.CrossDesign V (Fin 4) 5 where
  cross := univ.biUnion (fun b : P =>
    (X b).cross.image (fun c => c.map (parentEmbedding b.val)))
  uniform := by
    intro b hb
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hb
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hi
    rw [card_map]
    exact (X i).uniform c hc
  transverse := by
    intro b hb p hp q hq hpq
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hb
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hi
    obtain ⟨r,hr,rfl⟩ := mem_map.mp hp
    obtain ⟨s,hs,rfl⟩ := mem_map.mp hq
    have hrs : r = s := (X i).transverse c hc r hr s hs (Subtype.ext hpq)
    exact congrArg (parentEmbedding i.val) hrs
  unique := by
    intro p q hpq
    obtain ⟨b,hb,hu⟩ := parent_pair_unique P hP p.1 q.1 hpq
    let bi : P := ⟨b,hb.1⟩
    let p' : b × Fin 4 := (⟨p.1,hb.2.1⟩,p.2)
    let q' : b × Fin 4 := (⟨q.1,hb.2.2⟩,q.2)
    obtain ⟨c,hc,hcu⟩ := (X bi).unique p' q' (fun he => hpq (congrArg Subtype.val he))
    refine ⟨c.map (parentEmbedding b),⟨?_,?_,?_⟩,?_⟩
    · exact mem_biUnion.mpr ⟨bi,mem_univ _,mem_image.mpr ⟨c,hc.1,rfl⟩⟩
    · exact (lift_exact b c p'.1 p'.2).mpr hc.2.1
    · exact (lift_exact b c q'.1 q'.2).mpr hc.2.2
    · intro d hd
      obtain ⟨e,_,he⟩ := mem_biUnion.mp hd.1
      obtain ⟨f,hf,rfl⟩ := mem_image.mp he
      have heb : e.val = b := hu e.val ⟨e.property,
        lift_support e.val f hd.2.1,lift_support e.val f hd.2.2⟩
      have heq : e = bi := Subtype.ext heb
      subst e
      exact congrArg (fun a => a.map (parentEmbedding b))
        (hcu f ⟨hf,(lift_exact b f p'.1 p'.2).mp hd.2.1,
          (lift_exact b f q'.1 q'.2).mp hd.2.2⟩)

/-- The complete five-point block fills each global group together with the common point. -/
theorem complete_filling :
    ({univ} : Finset (Finset (Option (Fin 4)))).IsBlockDesign 2 5 := by
  constructor
  · intro b hb
    obtain rfl := mem_singleton.mp hb
    decide
  · intro S _
    refine ⟨univ,⟨mem_singleton_self _,subset_univ _⟩,?_⟩
    intro b hb
    exact mem_singleton.mp hb.1

/-- Weighted substitution requires only actual local designs, not a cross-family assumption. -/
theorem exists_design (P : Finset (Finset V)) (hP : P.IsPairwiseBalancedDesign)
    (hlocal : ∀ b ∈ P, ∃ D : Finset (Finset (Fin (4 * b.card + 1))),
      D.IsBlockDesign 2 5) :
    ∃ H : Finset (Finset (Option (V × Fin 4))), H.IsBlockDesign 2 5 := by
  have hx : ∀ b : P,
      Nonempty (Foundation.SharedGroupCompletion.CrossDesign b.val (Fin 4) 5) := by
    intro b
    obtain ⟨D,hD⟩ := hlocal b.val b.property
    have hc : Fintype.card b.val = b.val.card := Fintype.card_coe _
    have hex : ∃ E : Finset (Finset (Fin (4 * Fintype.card b.val + 1))),
        E.IsBlockDesign 2 5 := by
      rw [hc]
      exact ⟨D,hD⟩
    obtain ⟨E,hE⟩ := hex
    exact local_cross_exists E hE
  let X := fun b : P => Classical.choice (hx b)
  let C := assembledCross P hP X
  exact ⟨Foundation.SharedGroupCompletion.blocks C {univ},
    Foundation.SharedGroupCompletion.isBlockDesign C {univ} complete_filling⟩

/-- Relabel the weighted construction by its exact order `4 * card V + 1`. -/
theorem exists_design_fin (P : Finset (Finset V)) (hP : P.IsPairwiseBalancedDesign)
    (hlocal : ∀ b ∈ P, ∃ D : Finset (Finset (Fin (4 * b.card + 1))),
      D.IsBlockDesign 2 5) :
    ∃ H : Finset (Finset (Fin (4 * Fintype.card V + 1))), H.IsBlockDesign 2 5 := by
  obtain ⟨H,hH⟩ := exists_design P hP hlocal
  have hc : Fintype.card (Option (V × Fin 4)) = 4 * Fintype.card V + 1 := by
    simp only [Fintype.card_option,Fintype.card_prod,Fintype.card_fin]
    omega
  let e := Fintype.equivFinOfCardEq hc
  exact ⟨DesignTransport.relabel e H,DesignTransport.isBlockDesign_relabel e H 2 5 hH⟩

end Assembly
end Erdos643Design.WeightedPairwiseConstruction

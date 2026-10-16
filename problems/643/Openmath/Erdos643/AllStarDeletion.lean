import Openmath.Erdos643.GraphDeletion
import Openmath.Erdos643.TriangleCleanup
namespace Erdos643.AllStarDeletion
set_option linter.unusedSectionVars false
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
abbrev Flags (X Y : Type*) [DecidableEq Y] := Finset (X × Finset Y)
def Valid (H : Flags X Y) : Prop := ∀ z ∈ H, z.2.card = 2
def XActive (H : Flags X Y) (x x' : X) : Prop := x ≠ x' ∧ ∃ P, (x,P) ∈ H ∧ (x',P) ∈ H
def Compatible (H : Flags X Y) (u v y : Y) (x : X) : Prop := (x,{y,u}) ∈ H ∧ (x,{y,v}) ∈ H
def YDiag (H : Flags X Y) (u v : Y) : Prop := u ≠ v ∧ ∃ y a b, y ≠ u ∧ y ≠ v ∧ a ≠ b ∧ Compatible H u v y a ∧ Compatible H u v y b
def XStars (H : Flags X Y) : Prop := ∀ x x', x ≠ x' → (∃ P, (x,P) ∈ H ∧ (x',P) ∈ H) → ∃ c, ∀ P, (x,P) ∈ H → (x',P) ∈ H → c ∈ P
def Transport (H : Flags X Y) : Prop := ∀ u v, u ≠ v → (∃ x y, Compatible H u v y x) → ∃ w, ∀ y, y ≠ u → y ≠ v → y ≠ w → ∀ x x', Compatible H u v y x → Compatible H u v y x' → x = x'
lemma xActive_symm {H : Flags X Y} {x x' : X} : XActive H x x' → XActive H x' x := by
 rintro ⟨hne,P,h,h'⟩; exact ⟨hne.symm,P,h',h⟩
lemma compatible_symm {H : Flags X Y} {u v y : Y} {x : X} : Compatible H u v y x → Compatible H v u y x := And.symm
lemma yDiag_symm {H : Flags X Y} {u v : Y} : YDiag H u v → YDiag H v u := by
 rintro ⟨hne,y,a,b,hyu,hyv,hab,ha,hb⟩
 exact ⟨hne.symm,y,a,b,hyv,hyu,hab,ha.symm,hb.symm⟩
noncomputable def xChargeGraph (H : Flags X Y) : SimpleGraph X where
 Adj := XActive H
 symm := ⟨fun _ _ h => xActive_symm h⟩
 loopless := ⟨fun _ h => h.1 rfl⟩
noncomputable def yChargeGraph (H : Flags X Y) : SimpleGraph Y where
 Adj := YDiag H
 symm := ⟨fun _ _ h => yDiag_symm h⟩
 loopless := ⟨fun _ h => h.1 rfl⟩
noncomputable local instance {W : Type*} [Fintype W] (G : SimpleGraph W) : Fintype G.edgeSet := Fintype.ofFinite _
noncomputable def XChargePairs (H : Flags X Y) : Finset (Finset X) := (xChargeGraph H).edgeFinset.image Sym2.toFinset
noncomputable def YChargePairs (H : Flags X Y) : Finset (Finset Y) := (yChargeGraph H).edgeFinset.image Sym2.toFinset
abbrev Charge (H : Flags X Y) := Sum {e // e ∈ (xChargeGraph H).edgeFinset} {e // e ∈ (yChargeGraph H).edgeFinset}
noncomputable def encodeCharge {H : Flags X Y} : Charge H → Sym2 (Sum X Y)
 | .inl e => e.val.map Sum.inl
 | .inr e => e.val.map Sum.inr
def OwnerCorrect (H : Flags X Y) : Charge H → Y → Prop
 | .inl e, y => ∀ x x', e.val = s(x,x') → ∀ P, (x,P) ∈ H → (x',P) ∈ H → y ∈ P
 | .inr e, y => ∀ u v, e.val = s(u,v) → ∀ z, z ≠ u → z ≠ v → ∀ a b, a ≠ b → Compatible H u v z a → Compatible H u v z b → z = y
lemma owner_exists {H : Flags X Y} (hs : XStars H) (ht : Transport H) (c : Charge H) : ∃ y, OwnerCorrect H c y := by
 classical
 cases c with
 | inl e =>
   rcases e with ⟨e,he⟩
   induction e using Sym2.inductionOn with | _ x x' =>
     have ha : XActive H x x' := SimpleGraph.mem_edgeFinset.mp he
     rcases hs x x' ha.1 ha.2 with ⟨y,hy⟩
     refine ⟨y, ?_⟩
     intro a b hab P hP hP'
     rcases Sym2.eq_iff.mp hab with h | h
     · rcases h with ⟨rfl,rfl⟩; exact hy P hP hP'
     · rcases h with ⟨rfl,rfl⟩; exact hy P hP' hP
 | inr e =>
   rcases e with ⟨e,he⟩
   induction e using Sym2.inductionOn with | _ u v =>
     have hd : YDiag H u v := SimpleGraph.mem_edgeFinset.mp he
     rcases hd.2 with ⟨z,a,b,hzu,hzv,hab,ha,hb⟩
     rcases ht u v hd.1 ⟨a,z,ha⟩ with ⟨y,hy⟩
     refine ⟨y, ?_⟩
     intro p q hpq t htp htq i j hij hi hj
     by_contra hty
     rcases Sym2.eq_iff.mp hpq with h | h
     · rcases h with ⟨rfl,rfl⟩; exact hij (hy t htp htq hty i j hi hj)
     · rcases h with ⟨rfl,rfl⟩; exact hij (hy t htq htp hty i j hi.symm hj.symm)
noncomputable def owner {H : Flags X Y} (hs : XStars H) (ht : Transport H) (c : Charge H) : Y := Classical.choose (owner_exists hs ht c)
lemma owner_correct {H : Flags X Y} (hs : XStars H) (ht : Transport H) (c : Charge H) : OwnerCorrect H c (owner hs ht c) := Classical.choose_spec (owner_exists hs ht c)
noncomputable def bucket {H : Flags X Y} (g : Charge H → Y) (y : Y) : Finset (Charge H) := Finset.univ.filter (fun c => g c = y)
noncomputable def graphBucket {H : Flags X Y} (g : Charge H → Y) (y : Y) : Finset (Sym2 (Sum X Y)) := (bucket g y).image encodeCharge
lemma graphBucket_card_le {H : Flags X Y} (g : Charge H → Y) (y : Y) : (graphBucket g y).card ≤ (bucket g y).card := Finset.card_image_le
lemma bucket_partition {H : Flags X Y} (g : Charge H → Y) : ∑ y : Y, (bucket g y).card = Fintype.card (Charge H) := by
 classical
 simpa [bucket] using (Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := g) (by intro a ha; exact Finset.mem_univ _)).symm
def linkAdj (H : Flags X Y) (y : Y) : Sum X Y → Sum X Y → Prop
 | .inl x, .inr z => y ≠ z ∧ (x,{y,z}) ∈ H
 | .inr z, .inl x => y ≠ z ∧ (x,{y,z}) ∈ H
 | _, _ => False
def yLink (H : Flags X Y) (y : Y) : SimpleGraph (Sum X Y) where
 Adj := linkAdj H y
 symm := ⟨by intro a b h; cases a <;> cases b <;> exact h⟩
 loopless := ⟨by intro a; cases a <;> exact id⟩
lemma yLink_mono {U H : Flags X Y} (h : U ⊆ H) (y : Y) : yLink U y ≤ yLink H y := by
 intro a b hab
 cases a <;> cases b <;> simp only [yLink,linkAdj] at hab ⊢
 · exact ⟨hab.1,h hab.2⟩
 · exact ⟨hab.1,h hab.2⟩
lemma encode_nonloop {H : Flags X Y} (c : Charge H) : ¬ (encodeCharge c).IsDiag := by
 cases c with
 | inl e =>
   exact (Sym2.isDiag_map Sum.inl_injective).not.mpr
     ((xChargeGraph H).not_isDiag_of_mem_edgeFinset e.property)
 | inr e =>
   exact (Sym2.isDiag_map Sum.inr_injective).not.mpr
     ((yChargeGraph H).not_isDiag_of_mem_edgeFinset e.property)

lemma diagonal_owned {H U : Flags X Y} (hUH : U ⊆ H)
    (g : Charge H → Y) (hg : ∀ c, OwnerCorrect H c (g c))
    (y : Y) {p q : Sum X Y} (hd : GraphDeletion.IsDiagonal (yLink U y) p q) :
    ∃ c : Charge H, g c = y ∧ encodeCharge c = s(p,q) := by
 classical
 rcases hd with ⟨hpq,a,b,hab,hpa,hqa,hpb,hqb⟩
 cases p with
 | inl x =>
   cases q with
   | inl x' =>
     cases a with
     | inl z => exact False.elim hpa
     | inr z =>
       cases b with
       | inl z' => exact False.elim hpb
       | inr z' =>
         have hxx : x ≠ x' := fun h => hpq (congrArg Sum.inl h)
         have hzz : z ≠ z' := fun h => hab (congrArg Sum.inr h)
         have he : s(x,x') ∈ (xChargeGraph H).edgeFinset := by
           rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
           exact ⟨hxx,{y,z},hUH hpa.2,hUH hqa.2⟩
         let c : Charge H := .inl ⟨s(x,x'),he⟩
         have hc := hg c
         have hz : g c ∈ ({y,z} : Finset Y) := hc x x' rfl _ (hUH hpa.2) (hUH hqa.2)
         have hz' : g c ∈ ({y,z'} : Finset Y) := hc x x' rfl _ (hUH hpb.2) (hUH hqb.2)
         have hy : g c = y := by
           simp only [Finset.mem_insert,Finset.mem_singleton] at hz hz'
           rcases hz with h | h
           · exact h
           · rcases hz' with h' | h'
             · exact h'
             · exact False.elim (hzz (h.symm.trans h'))
         exact ⟨c,hy,rfl⟩
   | inr v =>
     cases a <;> contradiction
 | inr u =>
   cases q with
   | inl x => cases a <;> contradiction
   | inr v =>
     cases a with
     | inr z => exact False.elim hpa
     | inl i =>
       cases b with
       | inr z => exact False.elim hpb
       | inl j =>
         have huv : u ≠ v := fun h => hpq (congrArg Sum.inr h)
         have hij : i ≠ j := fun h => hab (congrArg Sum.inl h)
         have hi : Compatible H u v y i := ⟨hUH hpa.2,hUH hqa.2⟩
         have hj : Compatible H u v y j := ⟨hUH hpb.2,hUH hqb.2⟩
         have he : s(u,v) ∈ (yChargeGraph H).edgeFinset := by
           rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
           exact ⟨huv,y,i,j,hpa.1,hqa.1,hij,hi,hj⟩
         let c : Charge H := .inr ⟨s(u,v),he⟩
         have hy : y = g c := hg c u v rfl y hpa.1 hqa.1 i j hij hi hj
         exact ⟨c,hy.symm,rfl⟩

lemma diagonals_subset_bucket {H U : Flags X Y} (hUH : U ⊆ H)
    (g : Charge H → Y) (hg : ∀ c, OwnerCorrect H c (g c)) (y : Y) :
    GraphDeletion.diagonals (yLink U y) ⊆ graphBucket g y := by
 classical
 intro e he
 induction e using Sym2.inductionOn with | _ p q =>
   rcases diagonal_owned hUH g hg y (GraphDeletion.mem_diagonals.mp he) with ⟨c,hc,henc⟩
   exact Finset.mem_image.mpr ⟨c,by simp [bucket,hc],henc⟩

/-- Decode an unordered current link edge to its actual typed hyperedge. -/
def decodeSet (y : Y) : Sym2 (Sum X Y) → Finset (X × Finset Y) :=
 Sym2.lift ⟨(fun a b => match a,b with
   | .inl x,.inr z => {(x,{y,z})}
   | .inr z,.inl x => {(x,{y,z})}
   | _,_ => ∅), by intro a b; cases a <;> cases b <;> rfl⟩

noncomputable def removedAt (y : Y) (R : Finset (Sym2 (Sum X Y))) : Flags X Y :=
 R.biUnion (decodeSet y)

lemma decode_card_le (y : Y) (e : Sym2 (Sum X Y)) : (decodeSet y e).card ≤ 1 := by
 induction e using Sym2.inductionOn with | _ a b =>
   cases a <;> cases b <;> simp [decodeSet]

lemma removedAt_card_le (y : Y) (R : Finset (Sym2 (Sum X Y))) :
    (removedAt y R).card ≤ R.card := by
 classical
 calc
  (removedAt y R).card ≤ ∑ e ∈ R, (decodeSet y e).card := Finset.card_biUnion_le
  _ ≤ ∑ _e ∈ R, 1 := Finset.sum_le_sum (fun e he => decode_card_le y e)
  _ = R.card := by simp

lemma removedAt_subset {U : Flags X Y} (y : Y) {R : Finset (Sym2 (Sum X Y))}
    (hR : R ⊆ (yLink U y).edgeFinset) : removedAt y R ⊆ U := by
 classical
 intro f hf
 rcases Finset.mem_biUnion.mp hf with ⟨e,he,hf⟩
 have heU := hR he
 induction e using Sym2.inductionOn with | _ a b =>
   rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] at heU
   cases a <;> cases b <;> simp [decodeSet] at hf
   · subst f; exact heU.2
   · subst f; exact heU.2

lemma pair_fixed_injective (y : Y) : Function.Injective (fun z : Y => ({y,z} : Finset Y)) := by
 intro a b h
 dsimp only at h
 have ha : a = y ∨ a = b := by
   have hm : a ∈ ({y,b} : Finset Y) := h ▸ (by simp)
   simpa only [Finset.mem_insert,Finset.mem_singleton] using hm
 rcases ha with ha | ha
 · subst a
   have hb : b = y := by
     have hm : b ∈ ({y,y} : Finset Y) := h.symm ▸ (by simp)
     simpa using hm
   exact hb.symm
 · exact ha

lemma removedAt_pair_iff {U : Flags X Y} (y : Y)
    {R : Finset (Sym2 (Sum X Y))} (hR : R ⊆ (yLink U y).edgeFinset)
    (x : X) (z : Y) :
    (x,{y,z}) ∈ removedAt y R ↔ s(Sum.inl x,Sum.inr z) ∈ R := by
 classical
 constructor
 · intro hf
   rcases Finset.mem_biUnion.mp hf with ⟨e,he,hf⟩
   have heU := hR he
   induction e using Sym2.inductionOn with | _ a b =>
     rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] at heU
     cases a with
     | inl i =>
       cases b with
       | inl j => exact False.elim heU
       | inr w =>
         have hf' : (x,({y,z} : Finset Y)) = (i,{y,w}) := by simpa [decodeSet] using hf
         have hx : x = i := congrArg Prod.fst hf'
         have hz := pair_fixed_injective y (congrArg Prod.snd hf')
         subst i; subst w; exact he
     | inr w =>
       cases b with
       | inr w' => exact False.elim heU
       | inl i =>
         have hf' : (x,({y,z} : Finset Y)) = (i,{y,w}) := by simpa [decodeSet] using hf
         have hx : x = i := congrArg Prod.fst hf'
         have hz := pair_fixed_injective y (congrArg Prod.snd hf')
         subst i; subst w; simpa only [Sym2.eq_swap] using he
 · intro he
   exact Finset.mem_biUnion.mpr ⟨_,he,by simp [decodeSet]⟩

lemma yLink_removedAt {U : Flags X Y} (y : Y)
    {R : Finset (Sym2 (Sum X Y))} (hR : R ⊆ (yLink U y).edgeFinset) :
    yLink (U \ removedAt y R) y = (yLink U y).deleteEdges (↑R : Set (Sym2 (Sum X Y))) := by
 classical
 ext a b
 rw [SimpleGraph.deleteEdges_adj]
 cases a <;> cases b <;> simp only [yLink,linkAdj,Finset.mem_sdiff]
 · simp
 · rw [removedAt_pair_iff y hR]; tauto
 · rw [removedAt_pair_iff y hR]
   simp only [Sym2.eq_swap]; tauto
 · simp

def Killed {H : Flags X Y} (g : Charge H → Y) (U : Flags X Y) (c : Charge H) : Prop :=
 ∀ p q, encodeCharge c = s(p,q) → ¬ ∃ z,
   (yLink U (g c)).Adj p z ∧ (yLink U (g c)).Adj q z

lemma killed_mono {H U W : Flags X Y} (hWU : W ⊆ U) (g : Charge H → Y)
    (c : Charge H) (hk : Killed g U c) : Killed g W c := by
 intro p q he ⟨z,hp,hq⟩
 exact hk p q he ⟨z,yLink_mono hWU _ hp,yLink_mono hWU _ hq⟩

lemma bucket_step {H U : Flags X Y} (hUH : U ⊆ H)
    (g : Charge H → Y) (hg : ∀ c, OwnerCorrect H c (g c)) (y : Y) :
    ∃ A : Flags X Y, A ⊆ U ∧ A.card ≤ (bucket g y).card ∧
      ∀ c, g c = y → Killed g (U \ A) c := by
 classical
 have hS : ∀ p q, s(p,q) ∈ graphBucket g y → p ≠ q := by
   intro p q he hpq
   rcases Finset.mem_image.mp he with ⟨c,hc,he⟩
   have hn := encode_nonloop c
   rw [he,hpq] at hn
   exact hn (by simp)
 rcases GraphDeletion.deletion_with_charges (yLink U y) (graphBucket g y) hS
   (diagonals_subset_bucket hUH g hg y) with ⟨R,hR,hcard,hkill⟩
 refine ⟨removedAt y R,removedAt_subset y hR,
   (removedAt_card_le y R).trans (hcard.trans (graphBucket_card_le g y)),?_⟩
 intro c hc p q he
 have hmem : s(p,q) ∈ graphBucket g y :=
   Finset.mem_image.mpr ⟨c,by simp [bucket,hc],he⟩
 have hk := hkill p q hmem
 rw [← yLink_removedAt y hR] at hk
 simpa only [hc] using hk

lemma process_buckets {H : Flags X Y} (g : Charge H → Y)
    (hg : ∀ c, OwnerCorrect H c (g c)) (S : Finset Y) :
    ∃ U : Flags X Y, U ⊆ H ∧ H.card ≤ U.card + ∑ y ∈ S, (bucket g y).card ∧
      ∀ c, g c ∈ S → Killed g U c := by
 classical
 induction S using Finset.induction_on with
 | empty => exact ⟨H,Finset.Subset.refl _,by simp,by simp⟩
 | @insert y S hy ih =>
   rcases ih with ⟨U,hUH,hcost,hk⟩
   rcases bucket_step hUH g hg y with ⟨A,hAU,hAcost,hnew⟩
   refine ⟨U \ A,(Finset.sdiff_subset).trans hUH,?_,?_⟩
   · have hcard := Finset.card_sdiff_add_card_eq_card hAU
     rw [Finset.sum_insert hy]
     omega
   · intro c hc
     rcases Finset.mem_insert.mp hc with hc | hc
     · exact hnew c hc
     · exact killed_mono Finset.sdiff_subset g c (hk c hc)

lemma pair_of_card_two {P : Finset Y} (hP : P.card = 2) {y : Y} (hy : y ∈ P) :
    ∃ z, y ≠ z ∧ P = {y,z} := by
 rcases Finset.card_eq_two.mp hP with ⟨a,b,hab,rfl⟩
 simp only [Finset.mem_insert,Finset.mem_singleton] at hy
 rcases hy with rfl | rfl
 · exact ⟨b,hab,rfl⟩
 · exact ⟨a,hab.symm,Finset.pair_comm _ _⟩

/-- Actual deletion bound, stated first using the finite original charge type. -/
theorem deletion_charge_card (H : Flags X Y) (hV : Valid H)
    (hs : XStars H) (ht : Transport H) :
    ∃ R : Flags X Y, R ⊆ H ∧ R.card ≤ Fintype.card (Charge H) ∧
      ∀ x x' P, (x,P) ∈ H \ R → (x',P) ∈ H \ R → x = x' := by
 classical
 let g := owner hs ht
 have hg : ∀ c, OwnerCorrect H c (g c) := owner_correct hs ht
 rcases process_buckets g hg Finset.univ with ⟨U,hUH,hcost,hk⟩
 have hCU : H.card ≤ U.card + Fintype.card (Charge H) := by
   simpa only [bucket_partition] using hcost
 have hsub : H \ (H \ U) = U := Finset.sdiff_sdiff_eq_self hUH
 refine ⟨H \ U,Finset.sdiff_subset,?_,?_⟩
 · have hcard := Finset.card_sdiff_add_card_eq_card hUH
   omega
 · rw [hsub]
   intro x x' P hx hx'
   by_contra hxx
   have he : s(x,x') ∈ (xChargeGraph H).edgeFinset := by
     rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
     exact ⟨hxx,P,hUH hx,hUH hx'⟩
   let c : Charge H := .inl ⟨s(x,x'),he⟩
   have hy : g c ∈ P := hg c x x' rfl P (hUH hx) (hUH hx')
   rcases pair_of_card_two (hV _ (hUH hx)) hy with ⟨z,hyz,hP⟩
   have hzero := hk c (Finset.mem_univ _) (Sum.inl x) (Sum.inl x') rfl
   apply hzero
   refine ⟨Sum.inr z,?_,?_⟩
   · exact ⟨hyz,hP ▸ hx⟩
   · exact ⟨hyz,hP ▸ hx'⟩

lemma toFinset_injective {W : Type*} [DecidableEq W] :
    Function.Injective (Sym2.toFinset : Sym2 W → Finset W) := by
 intro p q h
 apply Sym2.ext
 intro x
 rw [← Sym2.mem_toFinset,← Sym2.mem_toFinset,h]

lemma charge_card (H : Flags X Y) :
    Fintype.card (Charge H) = (XChargePairs H).card + (YChargePairs H).card := by
 classical
 simp only [Charge,Fintype.card_sum,Fintype.card_coe]
 rw [XChargePairs,YChargePairs,Finset.card_image_of_injective _ toFinset_injective,
   Finset.card_image_of_injective _ toFinset_injective]

lemma mem_XChargePairs {H : Flags X Y} {x x' : X} :
    {x,x'} ∈ XChargePairs H ↔ XActive H x x' := by
 classical
 constructor
 · rintro h
   rcases Finset.mem_image.mp h with ⟨e,he,heq⟩
   have he' : e = s(x,x') := toFinset_injective (heq.trans Sym2.toFinset_mk_eq.symm)
   subst e
   exact SimpleGraph.mem_edgeFinset.mp he
 · intro h
   exact Finset.mem_image.mpr ⟨s(x,x'),SimpleGraph.mem_edgeFinset.mpr h,Sym2.toFinset_mk_eq⟩

lemma mem_YChargePairs {H : Flags X Y} {u v : Y} :
    {u,v} ∈ YChargePairs H ↔ YDiag H u v := by
 classical
 constructor
 · rintro h
   rcases Finset.mem_image.mp h with ⟨e,he,heq⟩
   have he' : e = s(u,v) := toFinset_injective (heq.trans Sym2.toFinset_mk_eq.symm)
   subst e
   exact SimpleGraph.mem_edgeFinset.mp he
 · intro h
   exact Finset.mem_image.mpr ⟨s(u,v),SimpleGraph.mem_edgeFinset.mpr h,Sym2.toFinset_mk_eq⟩

/-- The full owner-bucket deletion supplier, with actual original edge subfamily. -/
theorem allStar_deletion (H : Flags X Y) (hV : Valid H)
    (hs : XStars H) (ht : Transport H) :
    ∃ R : Flags X Y, R ⊆ H ∧
      R.card ≤ (XChargePairs H).card + (YChargePairs H).card ∧
      ∀ x x' P, (x,P) ∈ H \ R → (x',P) ∈ H \ R → x = x' := by
 simpa only [charge_card] using deletion_charge_card H hV hs ht

/-- Generic reconstruction on two disjoint vertex types. -/
def liftFlag (z : X × Finset Y) : Finset (Sum X Y) :=
 insert (Sum.inl z.1) (z.2.image Sum.inr)
def liftFlags (H : Flags X Y) : Finset (Finset (Sum X Y)) := H.image liftFlag
lemma liftFlag_injective : Function.Injective (liftFlag (X := X) (Y := Y)) := by
 intro z w he
 have hf : z.1 = w.1 := by
   have hm : Sum.inl z.1 ∈ liftFlag w := by rw [← he]; simp [liftFlag]
   simpa [liftFlag] using hm
 have hs : z.2 = w.2 := by
   ext v
   have hm := congrArg (fun S : Finset (Sum X Y) => Sum.inr v ∈ S) he
   have hp : (v ∈ z.2) = (v ∈ w.2) := by simpa [liftFlag] using hm
   exact Iff.of_eq hp
 exact Prod.ext hf hs
lemma liftFlags_card (H : Flags X Y) : (liftFlags H).card = H.card :=
 Finset.card_image_of_injective _ liftFlag_injective
lemma liftFlags_delete (H R : Flags X Y) : liftFlags (H \ R) = liftFlags H \ liftFlags R := by
 classical
 exact Finset.image_sdiff H R liftFlag_injective
lemma liftFlags_uniform {H : Flags X Y} (hV : Valid H) :
    ∀ E ∈ liftFlags H, E.card = 3 := by
 intro E hE
 rcases Finset.mem_image.mp hE with ⟨z,hz,rfl⟩
 rw [liftFlag,Finset.card_insert_of_notMem (by simp),
   Finset.card_image_of_injective _ Sum.inr_injective,hV z hz]

/-- Every actual one-X/two-Y system admits the typed representation. -/
lemma reconstruction (J : Finset (Finset (Sum X Y)))
    (hJ : ∀ E ∈ J, ∃ z : X × Finset Y, z.2.card = 2 ∧ E = liftFlag z) :
    ∃ H : Flags X Y, Valid H ∧ liftFlags H = J := by
 classical
 let H : Flags X Y := Finset.univ.filter (fun z => z.2.card = 2 ∧ liftFlag z ∈ J)
 refine ⟨H,?_,?_⟩
 · intro z hz
   exact (Finset.mem_filter.mp hz).2.1
 · ext E
   constructor
   · intro hE
     rcases Finset.mem_image.mp hE with ⟨z,hz,rfl⟩
     exact (Finset.mem_filter.mp hz).2.2
   · intro hE
     rcases hJ E hE with ⟨z,hz,rfl⟩
     exact Finset.mem_image.mpr ⟨z,by simp [H,hz,hE],rfl⟩

open HypergraphBasics

/-- Original source charges D union B_X, equal to D union E_X because
E_X is precisely the non-diagonal part of B_X. -/
noncomputable def SourceCharges (H : Flags X Y) : Finset (Finset (Sum X Y)) :=
 TriangleCleanup.Dpairs (liftFlags H) ∪
   (K5Cleaning.Bpairs (liftFlags H)).filter (fun P => ∀ v ∈ P, ∃ x, v = Sum.inl x)

lemma xactive_lift_common {H : Flags X Y} (hV : Valid H) {x x' : X}
    {P : Finset Y} (hx : (x,P) ∈ H) (hx' : (x',P) ∈ H) :
    CommonPair (liftFlags H) (Sum.inl x) (Sum.inl x') (P.image Sum.inr) := by
 refine ⟨?_,by simp,by simp,?_,?_⟩
 · rw [Finset.card_image_of_injective _ Sum.inr_injective,hV _ hx]
 · exact Finset.mem_image.mpr ⟨(x,P),hx,rfl⟩
 · exact Finset.mem_image.mpr ⟨(x',P),hx',rfl⟩

lemma compatible_lift_common {H : Flags X Y} {u v y : Y} {x : X}
    (hyu : y ≠ u) (hyv : y ≠ v) (hc : Compatible H u v y x) :
    CommonPair (liftFlags H) (Sum.inr u) (Sum.inr v) {Sum.inr y,Sum.inl x} := by
 refine ⟨by simp,by simp [hyu.symm],by simp [hyv.symm],?_,?_⟩
 · have hm : liftFlag (x,({y,u} : Finset Y)) ∈ liftFlags H := Finset.mem_image.mpr ⟨_,hc.1,rfl⟩
   simpa only [liftFlag,Finset.image_insert,Finset.image_singleton,Finset.image_union,Finset.insert_eq,
     Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hm
 · have hm : liftFlag (x,({y,v} : Finset Y)) ∈ liftFlags H := Finset.mem_image.mpr ⟨_,hc.2,rfl⟩
   simpa only [liftFlag,Finset.image_insert,Finset.image_singleton,Finset.image_union,Finset.insert_eq,
     Finset.union_comm,Finset.union_left_comm,Finset.union_assoc] using hm

lemma lifted_XCharges_subset {H : Flags X Y} (hV : Valid H) :
    (XChargePairs H).image (Finset.image (Sum.inl : X → Sum X Y)) ⊆ SourceCharges H := by
 classical
 intro S hS
 rcases Finset.mem_image.mp hS with ⟨P,hP,rfl⟩
 rcases Finset.mem_image.mp hP with ⟨e,he,rfl⟩
 induction e using Sym2.inductionOn with | _ x x' =>
   have ha : XActive H x x' := SimpleGraph.mem_edgeFinset.mp he
   rcases ha.2 with ⟨Q,hx,hx'⟩
   simp only [Sym2.toFinset_mk_eq,Finset.image_insert,Finset.image_singleton]
   apply Finset.mem_union_right
   apply Finset.mem_filter.mpr
   refine ⟨K5Cleaning.mem_Bpairs_pair.mpr ⟨by simpa using ha.1,
      Q.image Sum.inr,xactive_lift_common hV hx hx'⟩,?_⟩
   intro z hz
   simp only [Finset.mem_insert,Finset.mem_singleton] at hz
   rcases hz with rfl | rfl <;> exact ⟨_,rfl⟩

lemma lifted_YCharges_subset (H : Flags X Y) :
    (YChargePairs H).image (Finset.image (Sum.inr : Y → Sum X Y)) ⊆ SourceCharges H := by
 classical
 intro S hS
 rcases Finset.mem_image.mp hS with ⟨P,hP,rfl⟩
 rcases Finset.mem_image.mp hP with ⟨e,he,rfl⟩
 induction e using Sym2.inductionOn with | _ u v =>
   have hd : YDiag H u v := SimpleGraph.mem_edgeFinset.mp he
   rcases hd.2 with ⟨y,a,b,hyu,hyv,hab,ha,hb⟩
   simp only [Sym2.toFinset_mk_eq,Finset.image_insert,Finset.image_singleton]
   apply Finset.mem_union_left
   apply TriangleCleanup.mem_Dpairs.mpr
   refine ⟨by simp [hd.1],Sum.inr u,Sum.inr v,by simpa using hd.1,rfl,
     Sum.inr y,Sum.inl a,Sum.inl b,by simpa using hab,
     compatible_lift_common hyu hyv ha,compatible_lift_common hyu hyv hb⟩

lemma lifted_charge_disjoint (H : Flags X Y) :
    Disjoint ((XChargePairs H).image (Finset.image (Sum.inl : X → Sum X Y)))
      ((YChargePairs H).image (Finset.image (Sum.inr : Y → Sum X Y))) := by
 classical
 apply Finset.disjoint_left.mpr
 intro S hx hy
 rcases Finset.mem_image.mp hx with ⟨P,hP,hPS⟩
 rcases Finset.mem_image.mp hy with ⟨Q,hQ,hQS⟩
 rcases Finset.mem_image.mp hP with ⟨e,he,rfl⟩
 obtain ⟨x,hx⟩ := (Finset.nonempty_iff_ne_empty.mpr (Sym2.toFinset_ne_empty e))
 have hxm : Sum.inl x ∈ S := hPS ▸ Finset.mem_image.mpr ⟨x,hx,rfl⟩
 rw [← hQS] at hxm
 simpa using hxm

lemma charge_bound_source {H : Flags X Y} (hV : Valid H) :
    (XChargePairs H).card + (YChargePairs H).card ≤ (SourceCharges H).card := by
 classical
 calc
  _ = (((XChargePairs H).image (Finset.image (Sum.inl : X → Sum X Y))) ∪
      ((YChargePairs H).image (Finset.image (Sum.inr : Y → Sum X Y)))).card := by
    rw [Finset.card_union_of_disjoint (lifted_charge_disjoint H),
      Finset.card_image_of_injective _ (Finset.image_injective Sum.inl_injective),
      Finset.card_image_of_injective _ (Finset.image_injective Sum.inr_injective)]
  _ ≤ _ := Finset.card_le_card (Finset.union_subset
      (lifted_XCharges_subset hV) (lifted_YCharges_subset H))

/-- Complete faithful Section2 theorem: actual deleted original triples cost
at most original D union E_X, and no surviving Y-pair has two X roots. -/
theorem allStar_source_deletion (H : Flags X Y) (hV : Valid H)
    (hs : XStars H) (ht : Transport H) :
    ∃ R : Flags X Y, R ⊆ H ∧ (liftFlags R).card ≤ (SourceCharges H).card ∧
      liftFlags (H \ R) = liftFlags H \ liftFlags R ∧
      ∀ x x' P, (x,P) ∈ H \ R → (x',P) ∈ H \ R → x = x' := by
 rcases allStar_deletion H hV hs ht with ⟨R,hR,hcard,hsep⟩
 exact ⟨R,hR,by rw [liftFlags_card]; exact hcard.trans (charge_bound_source hV),
   liftFlags_delete H R,hsep⟩

/-- Source E_X is the non-diagonal part of the active X pairs. -/
noncomputable def EXCharges (H : Flags X Y) : Finset (Finset (Sum X Y)) :=
 ((K5Cleaning.Bpairs (liftFlags H)).filter
   (fun P => ∀ v ∈ P, ∃ x, v = Sum.inl x)) \ TriangleCleanup.Dpairs (liftFlags H)

lemma sourceCharges_eq_D_union_EX (H : Flags X Y) :
    SourceCharges H = TriangleCleanup.Dpairs (liftFlags H) ∪ EXCharges H := by
 classical
 ext P
 simp only [SourceCharges,EXCharges,Finset.mem_union,Finset.mem_sdiff]
 tauto

lemma mem_liftFlags_iff (H : Flags X Y) (z : X × Finset Y) :
    liftFlag z ∈ liftFlags H ↔ z ∈ H := by
 classical
 exact Finset.mem_image.trans ⟨fun ⟨w,hw,he⟩ => liftFlag_injective he ▸ hw,
   fun hz => ⟨z,hz,rfl⟩⟩

/-- Actual original triples, not merely a graph surrogate, are deleted. -/
theorem actual_allStar_deletion (H : Flags X Y) (hV : Valid H)
    (hs : XStars H) (ht : Transport H) :
    ∃ A : Finset (Finset (Sum X Y)), A ⊆ liftFlags H ∧
      A.card ≤ (TriangleCleanup.Dpairs (liftFlags H) ∪ EXCharges H).card ∧
      ∀ x x' P, liftFlag (x,P) ∈ liftFlags H \ A →
        liftFlag (x',P) ∈ liftFlags H \ A → x = x' := by
 rcases allStar_source_deletion H hV hs ht with ⟨R,hR,hcard,hdelete,hsep⟩
 refine ⟨liftFlags R,Finset.image_subset_image hR,?_,?_⟩
 · simpa only [sourceCharges_eq_D_union_EX] using hcard
 · intro x x' P hx hx'
   rw [← hdelete,mem_liftFlags_iff] at hx hx'
   exact hsep x x' P hx hx'

end Erdos643.AllStarDeletion

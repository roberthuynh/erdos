import Openmath.Erdos643.Projection
import Openmath.Erdos643.TriangleCleanup

namespace Erdos643.ProjectionBridge
open Finset HypergraphBasics Projection TriangleCleanup K5Cleaning
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma mem_projected_iff {H : TripleSystem V} (hu : Uniform H) {x : V} {P : Finset V} :
    (x,P) ∈ projected H ↔ x ∉ P ∧ insert x P ∈ H := by
  constructor
  · intro hz
    exact ⟨(projected_pair hu hz).2, reconstruct hz⟩
  · rintro ⟨hx, hH⟩
    apply mem_biUnion.mpr
    refine ⟨insert x P, hH, ?_⟩
    apply mem_image.mpr
    refine ⟨x, by simp, ?_⟩
    simp [hx]

/-- Actual pair-sharing of the projected X roots. -/
def XActive (T : Finset (V × Finset V)) (x y : V) : Prop :=
  x ≠ y ∧ ∃ P, (x,P) ∈ T ∧ (y,P) ∈ T

lemma xactive_iff_commonPair {H : TripleSystem V} (hu : Uniform H) {x y : V} :
    XActive (projected H) x y ↔ x ≠ y ∧ ∃ P, CommonPair H x y P := by
  constructor
  · rintro ⟨hxy,P,hx,hy⟩
    obtain ⟨hxP,hxH⟩ := (mem_projected_iff hu).mp hx
    obtain ⟨hyP,hyH⟩ := (mem_projected_iff hu).mp hy
    exact ⟨hxy,P,(projected_pair hu hx).1,hxP,hyP,hxH,hyH⟩
  · rintro ⟨hxy,P,hc,hx,hy,hxH,hyH⟩
    exact ⟨hxy,P,(mem_projected_iff hu).mpr ⟨hx,hxH⟩,
      (mem_projected_iff hu).mpr ⟨hy,hyH⟩⟩

lemma flag_iff_link_adj {H : TripleSystem V} (hu : Uniform H) {x y u : V} :
    (x,({y,u} : Finset V)) ∈ projected H ↔ (linkGraph H y).Adj u x := by
  constructor
  · intro hz
    obtain ⟨hx,hE⟩ := (mem_projected_iff hu).mp hz
    have hyu : y ≠ u := by
      intro he
      have hc := (projected_pair hu hz).1
      simp [he] at hc
    have hxy : x ≠ y := by intro he; exact hx (by simp [he])
    have hxu : x ≠ u := by intro he; exact hx (by simp [he])
    refine ⟨hyu,hxy.symm,hxu.symm,?_⟩
    simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,
      Finset.union_assoc] using hE
  · intro h
    apply (mem_projected_iff hu).mpr
    refine ⟨by simp [h.2.1.symm,h.2.2.1.symm],?_⟩
    simpa only [Finset.insert_eq,Finset.union_comm,Finset.union_left_comm,
      Finset.union_assoc] using h.2.2.2

def Compatible (T : Finset (V × Finset V)) (u v y x : V) : Prop :=
  (x,{y,u}) ∈ T ∧ (x,{y,v}) ∈ T

lemma compatible_iff_commonPair {H : TripleSystem V} (hu : Uniform H)
    {u v y x : V} :
    Compatible (projected H) u v y x ↔ CommonPair H u v {y,x} := by
  rw [Compatible,flag_iff_link_adj hu,flag_iff_link_adj hu,fixed_commonPair_link]

/-- Y diagonals in actual Y links, omitting unused charges from X links. -/
def YDiag (T : Finset (V × Finset V)) (u v : V) : Prop :=
  u ≠ v ∧ ∃ y a b, y ≠ u ∧ y ≠ v ∧ a ≠ b ∧
    Compatible T u v y a ∧ Compatible T u v y b

lemma ydiag_iff_link_diagonal {H : TripleSystem V} (hu : Uniform H) {u v : V} :
    YDiag (projected H) u v ↔ ∃ y, GraphDeletion.IsDiagonal (linkGraph H y) u v := by
  constructor
  · rintro ⟨huv,y,a,b,hyu,hyv,hab,⟨hau,hav⟩,⟨hbu,hbv⟩⟩
    exact ⟨y,huv,a,b,hab,(flag_iff_link_adj hu).mp hau,
      (flag_iff_link_adj hu).mp hav,(flag_iff_link_adj hu).mp hbu,
      (flag_iff_link_adj hu).mp hbv⟩
  · rintro ⟨y,huv,a,b,hab,hua,hva,hub,hvb⟩
    exact ⟨huv,y,a,b,hua.1,hva.1,hab,
      ⟨(flag_iff_link_adj hu).mpr hua,(flag_iff_link_adj hu).mpr hva⟩,
      ⟨(flag_iff_link_adj hu).mpr hub,(flag_iff_link_adj hu).mpr hvb⟩⟩

noncomputable def XCharges (T : Finset (V × Finset V)) : Finset (Finset V) := by
  classical
  exact (univ.powersetCard 2).filter (fun S => ∃ x y, S = {x,y} ∧ XActive T x y)

noncomputable def YCharges (T : Finset (V × Finset V)) : Finset (Finset V) := by
  classical
  exact (univ.powersetCard 2).filter (fun S => ∃ u v, S = {u,v} ∧ YDiag T u v)

/-- The first actual charge family is exactly original B(H), not all pairs. -/
theorem xcharges_eq_Bpairs {H : TripleSystem V} (hu : Uniform H) :
    XCharges (projected H) = Bpairs H := by
  classical
  ext S
  simp only [XCharges,mem_filter,mem_powersetCard,subset_univ,true_and,mem_Bpairs,
    xactive_iff_commonPair hu]
  constructor
  · rintro ⟨hc,x,y,he,hxy,hP⟩
    exact ⟨hc,x,y,hxy,he,hP⟩
  · rintro ⟨hc,x,y,hxy,he,hP⟩
    exact ⟨hc,x,y,he,hxy,hP⟩

/-- The second actual charge family is exactly original D(H). -/
theorem ycharges_eq_Dpairs {H : TripleSystem V} (hu : Uniform H) :
    YCharges (projected H) = Dpairs H := by
  classical
  ext S
  simp only [YCharges,mem_filter,mem_powersetCard,subset_univ,true_and,
    Dpairs_iff_link_diagonal,ydiag_iff_link_diagonal hu]
  aesop

/-- Original all-star common links supply the actual X-root star hypothesis. -/
theorem projected_x_stars {H : TripleSystem V} (hu : Uniform H) (hs : AllStars H)
    {x y : V} (hxy : x ≠ y) :
    ∃ w, ∀ P, (x,P) ∈ projected H → (y,P) ∈ projected H → w ∈ P := by
  obtain ⟨w, hw⟩ := hs x y hxy
  refine ⟨w, ?_⟩
  intro P hx hy
  obtain ⟨hxP,hxH⟩ := (mem_projected_iff hu).mp hx
  obtain ⟨hyP,hyH⟩ := (mem_projected_iff hu).mp hy
  exact hw P ⟨(projected_pair hu hx).1,hxP,hyP,hxH,hyH⟩

/-- The Y transport hypothesis is proved from the original common-link star;
its center depends on the pair and no dominant vertex is assumed. -/
theorem projected_y_transport {H : TripleSystem V} (hu : Uniform H) (hs : AllStars H)
    {u v : V} (huv : u ≠ v) :
    ∃ w, ∀ y, y ≠ u → y ≠ v → y ≠ w → ∀ x z,
      Compatible (projected H) u v y x → Compatible (projected H) u v y z → x = z := by
  obtain ⟨w, hw⟩ := hs u v huv
  refine ⟨w, ?_⟩
  intro y hyu hyv hyw x z hx hz
  have hxw := hw {y,x} ((compatible_iff_commonPair hu).mp hx)
  have hzw := hw {y,z} ((compatible_iff_commonPair hu).mp hz)
  simp only [mem_insert,mem_singleton] at hxw hzw
  have hwx : w = x := hxw.resolve_left hyw.symm
  have hwz : w = z := hzw.resolve_left hyw.symm
  exact hwx.symm.trans hwz

end Erdos643.ProjectionBridge

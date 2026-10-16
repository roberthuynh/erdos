import Mathlib

/-! A single actual matching step from a minimum-cardinality neighborhood choice. -/
namespace Erdos642.CampaignFe72210bContinuation3.MinimalNeighborhoodHall

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The full actual graph neighborhood of a finite left set. -/
def neighbors (S : Finset V) : Finset V := S.biUnion (fun a => G.neighborFinset a)

@[simp] theorem mem_neighbors (S : Finset V) (v : V) :
    v ∈ neighbors G S ↔ ∃ a ∈ S, G.Adj a v := by
  simp [neighbors]

theorem neighbors_mono {S T : Finset V} (h : S ⊆ T) :
    neighbors G S ⊆ neighbors G T := by
  intro v hv
  obtain ⟨a, ha, hav⟩ := (mem_neighbors G S v).mp hv
  exact (mem_neighbors G T v).mpr ⟨a, h ha, hav⟩

/-- All equal-shore, Hall and adjacency-bijection conclusions are derived from minimality. -/
theorem exists_minimal_neighborhood_matching (A B : Finset V)
    (hA : A.Nonempty) (hdisjoint : Disjoint A B) (hcard : B.card ≤ A.card)
    (hcontain : ∀ a ∈ A, G.neighborFinset a ⊆ B)
    (hpositive : ∀ a ∈ A, 0 < G.degree a) :
    ∃ C : Finset V,
      C ⊆ A ∧ C.Nonempty ∧
      neighbors G C ⊆ B ∧ (neighbors G C).Nonempty ∧
      Disjoint C (neighbors G C) ∧ C.card = (neighbors G C).card ∧
      (∀ S : Finset V, S ⊆ C → S.card ≤ (neighbors G S).card) ∧
      ∃ e : (C : Set V) ≃ (neighbors G C : Set V),
        ∀ x : (C : Set V), G.Adj x.val (e x).val := by
  classical
  have hneighborsA : neighbors G A ⊆ B := by
    intro v hv
    obtain ⟨a, ha, hav⟩ := (mem_neighbors G A v).mp hv
    exact hcontain a ha (by simpa using hav)
  let candidates : Finset (Finset V) :=
    A.powerset.filter (fun S => S.Nonempty ∧ (neighbors G S).card ≤ S.card)
  have hAcandidate : A ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.refl A, hA, (Finset.card_le_card hneighborsA).trans hcard⟩
  obtain ⟨C, hC, hminimal⟩ := Finset.exists_min_image candidates Finset.card
    ⟨A, hAcandidate⟩
  have hCdata := Finset.mem_filter.mp hC
  have hCA : C ⊆ A := Finset.mem_powerset.mp hCdata.1
  have hCnonempty : C.Nonempty := hCdata.2.1
  have hCsmall : (neighbors G C).card ≤ C.card := hCdata.2.2
  have hmin : ∀ S : Finset V, S ⊆ A → S.Nonempty →
      (neighbors G S).card ≤ S.card → C.card ≤ S.card := by
    intro S hSA hSne hSsmall
    exact hminimal S (Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hSA, hSne, hSsmall⟩)
  have hNB : neighbors G C ⊆ B := (neighbors_mono G hCA).trans hneighborsA
  have hNnonempty : (neighbors G C).Nonempty := by
    obtain ⟨a, ha⟩ := hCnonempty
    obtain ⟨v, hav⟩ := (G.degree_pos_iff_exists_adj a).mp (hpositive a (hCA ha))
    exact ⟨v, (mem_neighbors G C v).mpr ⟨a, ha, hav⟩⟩
  have hCequal : C.card = (neighbors G C).card := by
    apply Nat.le_antisymm ?_ hCsmall
    by_contra hnot
    have hstrict : (neighbors G C).card < C.card := by omega
    obtain ⟨a, ha⟩ := hCnonempty
    have herasecard := Finset.card_erase_add_one ha
    have hNpos := hNnonempty.card_pos
    have herasenonempty : (C.erase a).Nonempty := Finset.card_pos.mp (by omega)
    have herasesmall : (neighbors G (C.erase a)).card ≤ (C.erase a).card := by
      have hmono := Finset.card_le_card (neighbors_mono G (Finset.erase_subset a C))
      omega
    have hbad := hmin (C.erase a) ((Finset.erase_subset a C).trans hCA)
      herasenonempty herasesmall
    omega
  have hHall : ∀ S : Finset V, S ⊆ C → S.card ≤ (neighbors G S).card := by
    intro S hSC
    rcases Finset.eq_empty_or_nonempty S with rfl | hSne
    · simp [neighbors]
    · by_contra hnot
      have hstrict : (neighbors G S).card < S.card := by omega
      have hminS := hmin S (hSC.trans hCA) hSne hstrict.le
      have hEq : S = C := Finset.eq_of_subset_of_card_le hSC hminS
      subst S
      omega
  have hHallSubtype : ∀ s : Finset (C : Set V),
      s.card ≤ (s.biUnion (fun x => G.neighborFinset x.val)).card := by
    intro s
    have himage : s.image Subtype.val ⊆ C := by
      intro a ha
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
      exact x.property
    have hh := hHall (s.image Subtype.val) himage
    rw [Finset.card_image_of_injective s Subtype.val_injective] at hh
    simpa only [neighbors, Finset.image_biUnion] using hh
  obtain ⟨f, hfInjective, hfNeighbor⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective
      (fun x : (C : Set V) => G.neighborFinset x.val)).mp hHallSubtype
  have hfIn : ∀ x : (C : Set V), f x ∈ neighbors G C := by
    intro x
    exact (mem_neighbors G C (f x)).mpr
      ⟨x.val, x.property, by simpa using hfNeighbor x⟩
  let g : ↥(C : Set V) → ↥(neighbors G C : Set V) := fun x => ⟨f x, hfIn x⟩
  have hgInjective : Function.Injective g := by
    intro x y hxy
    exact hfInjective (congrArg Subtype.val hxy)
  have hTypesCard : Fintype.card (C : Set V) = Fintype.card (neighbors G C : Set V) := by
    calc
      Fintype.card (C : Set V) = C.card :=
        Fintype.card_of_finset' C (fun _ => Iff.rfl)
      _ = (neighbors G C).card := hCequal
      _ = Fintype.card (neighbors G C : Set V) :=
        (Fintype.card_of_finset' (neighbors G C) (fun _ => Iff.rfl)).symm
  have hgBijective : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).mpr ⟨hgInjective, hTypesCard⟩
  refine ⟨C, hCA, hCnonempty, hNB, hNnonempty, hdisjoint.mono hCA hNB,
    hCequal, hHall, Equiv.ofBijective g hgBijective, ?_⟩
  intro x
  change G.Adj x.val (f x)
  simpa using hfNeighbor x

end Erdos642.CampaignFe72210bContinuation3.MinimalNeighborhoodHall

import Openmath.Attempt6.RainbowMatching

/-! Finite routing selection from actual small-set avoidance. -/
namespace Erdos585.Attempt6
open scoped BigOperators

variable {I X : Type*} [Fintype I] [DecidableEq I] [DecidableEq X]

theorem large_matching_of_small_set_avoidance
    (H : I → Finset (Finset X)) (r b : ℕ) (J : Finset I)
    (hrank : ∀ i e, e ∈ H i → e.card ≤ r)
    (hne : ∀ i e, e ∈ H i → e.Nonempty)
    (havoid : ∀ S : Finset X, S.card ≤ r * b →
      ∃ i ∈ J, ∃ e ∈ H i, Disjoint e S) :
    ∃ M : Finset (Finset X),
      (∀ e ∈ M, ∃ i ∈ J, e ∈ H i) ∧
      (M : Set (Finset X)).Pairwise (fun e f => Disjoint e f) ∧ b < M.card := by
  classical
  let U : Finset (Finset X) := J.biUnion H
  let C : Finset (Finset (Finset X)) := U.powerset.filter (fun M : Finset (Finset X) =>
    (M : Set (Finset X)).Pairwise (fun e f => Disjoint e f))
  have hCne : C.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [C]
  obtain ⟨M, hMC, hmax⟩ := Finset.exists_max_image C Finset.card hCne
  have hMsub : M ⊆ U := Finset.mem_powerset.mp (Finset.mem_filter.mp hMC).1
  have hMpair := (Finset.mem_filter.mp hMC).2
  have hMmem : ∀ e ∈ M, ∃ i ∈ J, e ∈ H i := by
    intro e he
    exact Finset.mem_biUnion.mp (hMsub he)
  refine ⟨M, hMmem, hMpair, ?_⟩
  by_contra hn
  have hsmall : M.card ≤ b := Nat.le_of_not_gt hn
  let S := M.biUnion id
  have hScard : S.card ≤ r * b := by
    calc
      S.card ≤ M.card * r := Finset.card_biUnion_le_card_mul M id r (by
        intro e he
        obtain ⟨i, _, hei⟩ := hMmem e he
        exact hrank i e hei)
      _ ≤ b * r := Nat.mul_le_mul_right r hsmall
      _ = r * b := Nat.mul_comm _ _
  obtain ⟨i, hi, e, hei, heS⟩ := havoid S hScard
  have heU : e ∈ U := Finset.mem_biUnion.mpr ⟨i, hi, hei⟩
  have hsub : ∀ f ∈ M, f ⊆ S := by
    intro f hf x hx
    exact Finset.mem_biUnion.mpr ⟨f, hf, hx⟩
  have heM : e ∉ M := by
    intro hem
    obtain ⟨x, hx⟩ := hne i e hei
    exact Finset.disjoint_left.mp heS hx
      (Finset.mem_biUnion.mpr ⟨e, hem, hx⟩)
  have hins : insert e M ∈ C := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset heU hMsub), ?_⟩
    intro a ha c hc hac
    have haCases : a = e ∨ a ∈ M := Finset.mem_insert.mp ha
    have hcCases : c = e ∨ c ∈ M := Finset.mem_insert.mp hc
    rcases haCases with hae | haM
    · have hcM : c ∈ M := hcCases.resolve_left (fun hce => hac (hae.trans hce.symm))
      rw [hae]
      exact heS.mono_right (hsub c hcM)
    · rcases hcCases with hce | hcM
      · rw [hce]
        exact (heS.mono_right (hsub a haM)).symm
      · exact hMpair haM hcM hac
  have hb := hmax (insert e M) hins
  rw [Finset.card_insert_of_notMem heM] at hb
  omega

theorem rainbow_matching_of_small_set_avoidance
    (H : I → Finset (Finset X)) (r : ℕ)
    (hrank : ∀ i e, e ∈ H i → e.card ≤ r)
    (hne : ∀ i e, e ∈ H i → e.Nonempty)
    (havoid : ∀ J : Finset I, J.Nonempty → ∀ S : Finset X,
      S.card ≤ r * (2 * r * (J.card - 1)) →
      ∃ i ∈ J, ∃ e ∈ H i, Disjoint e S) :
    ∃ f : I → Finset X, (∀ i, f i ∈ H i) ∧
      Pairwise (fun i j => Disjoint (f i) (f j)) := by
  apply RainbowMatching.rainbow_matching_of_union_matching H r hrank
  intro J hJ
  exact large_matching_of_small_set_avoidance H r (2 * r * (J.card - 1)) J
    hrank hne (havoid J hJ)

/-- An actual original-graph path with its exact, nonempty interior recorded. -/
def SupportsRoute {V : Type*} [DecidableEq V] (G : SimpleGraph V) (U : Finset V)
    (ell : ℕ) (x y : V) (T : Finset V) : Prop :=
  T.Nonempty ∧ T ⊆ U ∧ x ∉ T ∧ y ∉ T ∧ T.card ≤ ell ∧
    ∃ p : G.Walk x y, p.IsPath ∧ p.length ≤ ell ∧
      p.support.toFinset = insert x (insert y T)

/-- Small-set avoidance for one requested route in every sublist supplies all
requested routes with pairwise disjoint actual interiors. -/
theorem select_disjoint_routes {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (ell : ℕ) (x y : I → V)
    (havoid : ∀ J : Finset I, J.Nonempty → ∀ S : Finset V,
      S.card ≤ ell * (2 * ell * (J.card - 1)) →
      ∃ i ∈ J, ∃ T, SupportsRoute G U ell (x i) (y i) T ∧ Disjoint T S) :
    ∃ T : I → Finset V, (∀ i, SupportsRoute G U ell (x i) (y i) (T i)) ∧
      Pairwise (fun i j => Disjoint (T i) (T j)) := by
  classical
  let H : I → Finset (Finset V) := fun i => Finset.univ.filter
    (SupportsRoute G U ell (x i) (y i))
  have hmem : ∀ i T, T ∈ H i ↔ SupportsRoute G U ell (x i) (y i) T := by
    intro i T
    simp [H]
  apply rainbow_matching_of_small_set_avoidance H ell
    (fun i T hT => ((hmem i T).mp hT).2.2.2.2.1)
    (fun i T hT => ((hmem i T).mp hT).1) ?_ |>.imp (fun T hT => ?_)
  · intro J hJ S hS
    obtain ⟨i, hi, T, hT, hdis⟩ := havoid J hJ S hS
    exact ⟨i, hi, T, (hmem i T).mpr hT, hdis⟩
  · exact ⟨fun i => (hmem i (T i)).mp (hT.1 i), hT.2⟩

end Erdos585.Attempt6

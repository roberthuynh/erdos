import Openmath.Erdos642.Proofs.CampaignFe72210b.ForestParameters
import Openmath.Erdos642.Proofs.CampaignFe72210b.QuantitativePruning
import Openmath.Erdos642.Proofs.CampaignFe72210b.LargeStarForest
import Openmath.Erdos642.Proofs.CampaignFe72210b.ForestBundleInduction

/-! Actual rounded root-disjoint star-forest extraction from original graph degrees. -/
namespace Erdos642.CampaignFe72210b
namespace RoundedForestExtraction

open ForestParameters

/-- Rounded roots and ceiling stars retain the reviewed forbidden-root charge. -/
theorem root_charge (N d i : ℕ) (hd : 100000000 ≤ d) (hN : 2 * d ≤ N)
    (hi : i < q d) :
    (i : ℝ) * (m N d : ℝ) * (100 * (d : ℝ)) ≤
      (0.001001 : ℝ) * (N : ℝ) * (d : ℝ) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hile : (i : ℝ) ≤ (d : ℝ) / 100000 := by
    have h' : (i : ℝ) ≤ (q d : ℝ) := by exact_mod_cast (Nat.le_of_lt hi)
    exact h'.trans (q_bounds d hd).2
  have hm := (m_bounds N d hd hN).2.2
  have hprod := mul_le_mul hile hm (Nat.cast_nonneg (m N d))
    (div_nonneg (Nat.cast_nonneg d) (by norm_num : (0 : ℝ) ≤ 100000))
  have hcharge := mul_le_mul_of_nonneg_right hprod
    (by positivity : (0 : ℝ) ≤ 100 * (d : ℝ))
  have hdd : (d : ℝ) * (d : ℝ) ≤ (N : ℝ) * (d : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg d)
    exact_mod_cast (show d ≤ N by omega)
  calc
    _ ≤ ((d : ℝ) / 100000) * ((N : ℝ) / (100000 * (d : ℝ)) + 1) *
        (100 * (d : ℝ)) := hcharge
    _ = (N : ℝ) * (d : ℝ) / 100000000 + (d : ℝ) * (d : ℝ) / 1000 := by
      field_simp [hdpos.ne']
      ring
    _ ≤ _ := by nlinarith [mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]

/-- The actual retained budget is strictly above the accepted 0.248Nd threshold. -/
theorem budget_lower (N d i : ℕ) (hd : 100000000 ≤ d) (hN : 2 * d ≤ N)
    (hi : i < q d) :
    (0.248 : ℝ) * (N : ℝ) * (d : ℝ) <
      (N : ℝ) * (d : ℝ) / 4 - (i : ℝ) * (m N d : ℝ) * (100 * (d : ℝ)) := by
  have hc := root_charge N d i hd hN hi
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  nlinarith [mul_pos hNpos hdpos]

/-- The reviewed scalar contradiction uses the true ceiling and quotient parameters. -/
theorem star_criterion (N d a f : ℕ) (hd : 100000000 ≤ d) (hN : 0 < N)
    (hA : (N : ℝ) / 100250 < (a : ℝ)) (hf : f < m N d) :
    (100 * (d : ℝ)) * (f : ℝ) * (b d : ℝ) <
      ((a : ℝ) - (f : ℝ)) * ((d : ℝ) / 4 - (b d : ℝ)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdbig : (100000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have haf : (N : ℝ) < 100250 * (a : ℝ) := by linarith
  have hapos : (0 : ℝ) < a := by linarith
  have hfd := (lt_div_iff₀ (by positivity : (0 : ℝ) < 100000 * (d : ℝ))).mp
    (lt_ratio_of_lt_m N d f hf)
  have hb := (b_bounds d hd).2
  have hbprod : 10000000 * (b d : ℝ) ≤ (d : ℝ) := by linarith
  have hfprod := mul_le_mul_of_nonneg_left hbprod (Nat.cast_nonneg f : (0 : ℝ) ≤ f)
  have hfb : (f : ℝ) * (b d : ℝ) < (N : ℝ) / 1000000000000 := by
    nlinarith
  have hlarge : (401000 : ℝ) ≤ 100000 * (d : ℝ) := by linarith
  have hlargef := mul_le_mul_of_nonneg_left hlarge (Nat.cast_nonneg f : (0 : ℝ) ≤ f)
  have hfour : 4 * (f : ℝ) < (a : ℝ) := by nlinarith
  have hgap : (d : ℝ) / 5 ≤ (d : ℝ) / 4 - (b d : ℝ) := by linarith
  have hnonneg : 0 ≤ (a : ℝ) - (f : ℝ) := by linarith [(Nat.cast_nonneg f : (0 : ℝ) ≤ f)]
  have hgapmul := mul_le_mul_of_nonneg_left hgap hnonneg
  have hfourmul := mul_lt_mul_of_pos_right hfour hdpos
  have hadpos : 0 < (a : ℝ) * (d : ℝ) := mul_pos hapos hdpos
  have hlower : (a : ℝ) * (d : ℝ) / 8 <
      ((a : ℝ) - (f : ℝ)) * ((d : ℝ) / 4 - (b d : ℝ)) := by
    nlinarith
  have hafmul := mul_lt_mul_of_pos_right haf hdpos
  have hmiddle : (N : ℝ) * (d : ℝ) / 10000000000 < (a : ℝ) * (d : ℝ) / 8 := by
    nlinarith
  have hfbmul := mul_lt_mul_of_pos_right hfb
    (by positivity : (0 : ℝ) < 100 * (d : ℝ))
  have hupper : (100 * (d : ℝ)) * (f : ℝ) * (b d : ℝ) <
      (N : ℝ) * (d : ℝ) / 10000000000 := by nlinarith
  exact hupper.trans (hmiddle.trans hlower)

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Original bipartite positive degrees force at least d vertices in each shore. -/
theorem two_degree_le_card (A B : Finset V) (d : ℕ) (hd : 0 < d)
    (hmin : ∀ x : V, d ≤ G.degree x)
    (hbi : G.IsBipartiteWith (A : Set V) (B : Set V)) :
    2 * d ≤ Fintype.card V := by
  classical
  let x : V := Classical.choice (inferInstance : Nonempty V)
  obtain ⟨y, hxy⟩ := (G.degree_pos_iff_exists_adj x).mp (hd.trans_le (hmin x))
  have hshores : d ≤ A.card ∧ d ≤ B.card := by
    rcases hbi.mem_of_adj hxy with hab | hba
    · exact ⟨(hmin y).trans (G.isBipartiteWith_degree_le' hbi hab.2),
        (hmin x).trans (G.isBipartiteWith_degree_le hbi hab.1)⟩
    · exact ⟨(hmin x).trans (G.isBipartiteWith_degree_le' hbi hba.1),
        (hmin y).trans (G.isBipartiteWith_degree_le hbi hba.2)⟩
  have hdis : Disjoint A B := Finset.disjoint_coe.mp hbi.disjoint
  have hcard := Finset.card_union_of_disjoint hdis
  have horder : (A ∪ B).card ≤ Fintype.card V := Finset.card_le_univ _
  omega

/-- Every actual previously used root set admits a new indexed forest avoiding it. -/
theorem exists_avoiding_indexed_forest (A B : Finset V) (d : ℕ) (hd : 100000000 ≤ d)
    (hmin : ∀ x : V, d ≤ G.degree x) (hmax : ∀ x : V, G.degree x ≤ 100 * d)
    (hbi : G.IsBipartiteWith (A : Set V) (B : Set V))
    (i : ℕ) (hi : i < q d) (U : Finset V)
    (hU : U.card = i * m (Fintype.card V) d) :
    ∃ H : IndexedForest G A B (m (Fintype.card V) d) (b d), ∀ j, H.root j ∉ U := by
  let N := Fintype.card V
  have hdNat : 0 < d := by omega
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hdNat
  have hN := two_degree_le_card G A B d hdNat hmin hbi
  have hNpos : 0 < N := Fintype.card_pos
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hbudget0 := budget_lower N d i hd hN hi
  have hbudget : (0.248 : ℝ) * (N : ℝ) * (d : ℝ) <
      (N : ℝ) * (d : ℝ) / 4 - (U.card : ℝ) * ((100 * d : ℕ) : ℝ) := by
    simpa only [hU, Nat.cast_mul, Nat.cast_ofNat] using hbudget0
  have hpos : 0 < (N : ℝ) * (d : ℝ) / 4 - (U.card : ℝ) * ((100 * d : ℕ) : ℝ) :=
    (by positivity : (0 : ℝ) < 0.248 * (N : ℝ) * (d : ℝ)).trans hbudget
  obtain ⟨W, hWsub, _hWne, hWmin, hWmax, _hWedges, hWbi, hWshore⟩ :=
    exists_quantitative_bipartite_pruning G U A B d (100 * d) hdNat hmin hmax hbi hpos
  have hAd : (0.248 : ℝ) * (N : ℝ) * (d : ℝ) <
      ((A ∩ W).card : ℝ) * ((100 * d : ℕ) : ℝ) := hbudget.trans_le hWshore
  push_cast at hAd
  have hAd' : ((0.248 : ℝ) * (N : ℝ)) * (d : ℝ) <
      (((A ∩ W).card : ℝ) * 100) * (d : ℝ) := by nlinarith
  have hcancel := (mul_lt_mul_iff_of_pos_right hdreal).mp hAd'
  have hshoreSize : (N : ℝ) / 100250 < ((A ∩ W).card : ℝ) := by linarith
  have hAB : Disjoint (A ∩ W) (B ∩ W) := Finset.disjoint_coe.mp hWbi.disjoint
  have hcover : ∀ r ∈ A ∩ W, (mask G W).neighborFinset r ⊆ B ∩ W := by
    intro r hr v hv
    exact hWbi.mem_of_mem_adj hr (((mask G W).mem_neighborFinset r v).mp hv)
  have hlower : ∀ r ∈ A ∩ W, (d : ℝ) / 4 ≤ ((mask G W).degree r : ℝ) := by
    intro r hr
    exact hWmin r (Finset.mem_inter.mp hr).2
  have hupper : ∀ v ∈ B ∩ W, (mask G W).degree v ≤ 100 * d := fun v _ => hWmax v
  have hnum : ∀ f : ℕ, f < m N d → f ≤ (A ∩ W).card →
      ((100 * d : ℕ) : ℝ) * (f : ℝ) * (b d : ℝ) <
        (((A ∩ W).card : ℝ) - (f : ℝ)) * ((d : ℝ) / 4 - (b d : ℝ)) := by
    intro f hf _hfa
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      star_criterion N d (A ∩ W).card f hd hNpos hshoreSize hf
  obtain ⟨F, hF⟩ := exists_exact_partial_star_forest (mask G W) (A ∩ W) (B ∩ W)
    (b d) (m N d) (100 * d) ((d : ℝ) / 4) hAB hcover hlower hupper hnum
  obtain ⟨root, leaves, hinj, hroot, hleaves, hcard, hadj, hdis⟩ :=
    F.indexed_of_roots_card_eq (m N d) hF
  let H : IndexedForest G A B (m N d) (b d) := {
    root := root
    leaves := leaves
    root_mem := fun j => (Finset.mem_inter.mp (hroot j)).1
    leaves_subset := fun j v hv => (Finset.mem_inter.mp (hleaves j hv)).1
    leaves_card := hcard
    adjacent := fun j v hv => (hadj j v hv).1
    root_injective := hinj
    leaves_disjoint := hdis }
  refine ⟨H, ?_⟩
  intro j
  exact (Finset.mem_sdiff.mp (hWsub (Finset.mem_inter.mp (hroot j)).2)).2

/-- Original finite bipartite degree hypotheses supply the full rounded root-disjoint bundle. -/
theorem exists_rounded_forestBundle (A B : Finset V) (d : ℕ) (hd : 100000000 ≤ d)
    (hmin : ∀ x : V, d ≤ G.degree x) (hmax : ∀ x : V, G.degree x ≤ 100 * d)
    (hbi : G.IsBipartiteWith (A : Set V) (B : Set V)) :
    Nonempty (ForestBundle G A B (q d) (m (Fintype.card V) d) (b d)) := by
  refine exists_forestBundle_of_supplier G A B (m (Fintype.card V) d) (b d) (q d)
    (Finset.disjoint_coe.mp hbi.disjoint) ?_
  intro i hi U _hUsubset hU
  exact exists_avoiding_indexed_forest G A B d hd hmin hmax hbi i hi U hU

end RoundedForestExtraction
end Erdos642.CampaignFe72210b

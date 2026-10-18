import Openmath.IncidenceRepair.ChartTransport

noncomputable section
namespace Erdos85.IncidenceRepair

/-- Chart j uses global coordinates (1,j+2,0), matching local (x,y,z).
The family has exactly n−1 charts and includes the rank-two case. -/
def canonicalChart (n : ℕ) (hn : 2 ≤ n) (j : Fin (n - 1)) : Fin 3 ↪ Fin (n + 1) where
  toFun := ![⟨1, by omega⟩, ⟨j.val + 2, by omega⟩, 0]
  inj' := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [Fin.ext_iff] <;> omega

@[simp] theorem canonicalChart_zero (n : ℕ) (hn : 2 ≤ n) (j : Fin (n - 1)) :
    canonicalChart n hn j 0 = ⟨1, by omega⟩ := rfl

@[simp] theorem canonicalChart_one (n : ℕ) (hn : 2 ≤ n) (j : Fin (n - 1)) :
    canonicalChart n hn j 1 = ⟨j.val + 2, by omega⟩ := rfl

@[simp] theorem canonicalChart_two (n : ℕ) (hn : 2 ≤ n) (j : Fin (n - 1)) :
    canonicalChart n hn j 2 = 0 := rfl

theorem canonical_chart_exists (n : ℕ) (hn : 2 ≤ n) : Nonempty (Fin (n - 1)) := by
  exact ⟨⟨0, by omega⟩⟩

end Erdos85.IncidenceRepair

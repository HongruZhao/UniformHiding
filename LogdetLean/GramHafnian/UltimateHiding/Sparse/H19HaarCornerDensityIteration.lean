import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19HaarCornerBaseColumn

/-!
# Iterating the Haar-corner density successor rule

This file contains the purely logical induction driver for Jiang's density.
The `N = 1` case is the completed foundations-only theorem.  The successor
step is supplied as an ordinary theorem argument, so a concrete geometric
successor theorem can be instantiated downstream without adding a scientific
assumption or creating an import cycle.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

/-- Starting from the proved one-column formula, any foundations-only
successor rule yields Jiang's density for every positive `N` in the regime
`N ≤ K` and `K + N ≤ M`.

The successor parameter receives exactly the inequalities available at the
current induction stage, followed by the density formula at `n`, and must
return the formula at `n+1`.  It is a theorem parameter, not a declaration or
scientific assumption. -/
theorem jiang_2009_prop2_1_unscaledTallHaarCorner_density_of_successorRule
    {M K N : ℕ}
    (hK : 0 < K) (hN : 0 < N) (hNK : N ≤ K)
    (hsize : K + N ≤ M)
    (hsucc : ∀ {n : ℕ},
      0 < n → n + 1 ≤ K → K + (n + 1) ≤ M →
      jiangUnscaledTallHaarCornerLaw M K n =
          (complexRectangularLebesgueVolume K n).withDensity
            (jiangUnscaledTallHaarCornerPDF M K n) →
      jiangUnscaledTallHaarCornerLaw M K (n + 1) =
          (complexRectangularLebesgueVolume K (n + 1)).withDensity
            (jiangUnscaledTallHaarCornerPDF M K (n + 1))) :
    jiangUnscaledTallHaarCornerLaw M K N =
      (complexRectangularLebesgueVolume K N).withDensity
        (jiangUnscaledTallHaarCornerPDF M K N) := by
  induction N with
  | zero => omega
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        exact jiang_2009_prop2_1_unscaledTallHaarCorner_density_N1 hK
          (by omega)
      · exact hsucc (Nat.pos_of_ne_zero hn) (by omega) (by omega)
          (ih (Nat.pos_of_ne_zero hn) (by omega) (by omega))

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse

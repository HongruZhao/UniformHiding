import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19HaarCornerDensityIteration

/-!
# Strict-size iteration of the Haar-corner density successor rule

The quantitative H19 endpoint uses `K+N<M`.  This driver propagates that
strict inequality through every induction stage, allowing the pointwise
successor balance to avoid the terminal exponent-zero boundary.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

/-- The strict-size Jiang density follows from the proved one-column case
and a strict-size successor rule. -/
theorem jiang_2009_prop2_1_unscaledTallHaarCorner_density_of_strict_successorRule
    {M K N : ℕ}
    (hK : 0 < K) (hN : 0 < N) (hNK : N ≤ K)
    (hsize : K + N < M)
    (hsucc : ∀ {n : ℕ},
      0 < n → n + 1 ≤ K → K + (n + 1) < M →
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

#print axioms
  jiang_2009_prop2_1_unscaledTallHaarCorner_density_of_strict_successorRule

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse

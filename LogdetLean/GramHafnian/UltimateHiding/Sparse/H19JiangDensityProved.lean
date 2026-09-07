import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19HaarCornerDensityIteration
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19HaarCornerDensityIterationStrict
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19HaarCornerWithDensitySuccessor
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19JiangDensityTransport

/-!
# Internally proved Jiang density endpoints

This module combines the foundations-only one-column density, the concrete
Haar-corner successor rule, and the strict-size induction driver.  It then
uses the elementary square-root scaling adapters to expose both the `ℝ≥0∞`
and ordinary-real density formulations used by quantitative H19.

The current internal successor proof assumes `K + N < M`.  This is precisely
the ambient regime used by the quantitative endpoint; the terminal equality
case `K + N = M` is deliberately not claimed here.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

/-- Strict-size Jiang Proposition 2.1, obtained from the proved one-column
case by iterating the internally proved Haar-corner successor rule. -/
theorem jiang_2009_prop2_1_unscaledTallHaarCorner_density_proved_strict
    {M N K : ℕ} (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K)
    (hs : K + N < M) :
    jiangUnscaledTallHaarCornerLaw M K N =
      (complexRectangularLebesgueVolume K N).withDensity
        (jiangUnscaledTallHaarCornerPDF M K N) := by
  refine
    jiang_2009_prop2_1_unscaledTallHaarCorner_density_of_strict_successorRule
      hK hN hNK hs ?_
  intro n _hn _hnK hnsize hprev
  exact jiangUnscaledTallHaarCorner_density_succ_proved hK hnsize hprev

/-- The internally proved strict-size density after entrywise multiplication
by `sqrt M`, in the native `ℝ≥0∞` density form. -/
theorem jiangSqrtScaledTallHaarCornerLaw_eq_withDensity_proved_strict
    {M N K : ℕ} (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K)
    (hs : K + N < M) :
    jiangSqrtScaledTallHaarCornerLaw M K N =
      (complexRectangularLebesgueVolume K N).withDensity
        (jiangSqrtScaledTallHaarCornerPDF M K N) := by
  exact jiangSqrtScaledTallHaarCornerLaw_eq_withDensity_of_unscaled
    (by omega : 0 < M)
    (jiang_2009_prop2_1_unscaledTallHaarCorner_density_proved_strict
      hN hK hNK hs)

/-- The internally proved strict-size scaled Jiang law expressed through its
ordinary nonnegative real density. -/
theorem jiangSqrtScaledTallHaarCornerLaw_eq_withDensity_ofReal_proved_strict
    {M N K : ℕ} (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K)
    (hs : K + N < M) :
    jiangSqrtScaledTallHaarCornerLaw M K N =
      (complexRectangularLebesgueVolume K N).withDensity
        (fun Z ↦ ENNReal.ofReal
          (jiangSqrtScaledTallHaarCornerRealPDF M K N Z)) := by
  exact jiangSqrtScaledTallHaarCornerLaw_eq_withDensity_ofReal_of_unscaled
    (by omega : 0 < M)
    (jiang_2009_prop2_1_unscaledTallHaarCorner_density_proved_strict
      hN hK hNK hs)

#print axioms
  jiang_2009_prop2_1_unscaledTallHaarCorner_density_proved_strict
#print axioms
  jiangSqrtScaledTallHaarCornerLaw_eq_withDensity_proved_strict
#print axioms
  jiangSqrtScaledTallHaarCornerLaw_eq_withDensity_ofReal_proved_strict

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse

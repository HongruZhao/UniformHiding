import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCenteredLikelihood
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalMomentBoundsExternal
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredLikelihoodBellCalculus
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredScoreProductLaw
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Classical fixed-order centered log-score moments

This file records the remaining classical finite-dimensional moment input for
the fourth-order COE score calculation.  Each declaration concerns one
literal monomial in the logarithmic derivatives of the determinant-density
likelihood in the traceless direction `Q_v=P_v-I/N`.  No Bell polynomial,
density-score norm, event derivative, total-variation estimate, local step,
or hiding conclusion is asserted.

The finiteness threshold `K >= 2N+8` is the order-four inverse-Wishart
integrability threshold.  The dimension-sharp estimates are deliberately
scoped only to `K >= 16N`.  They are standard consequences of the exact COE
corner density and the R20--R23 trace expansion, together with the order-four
inverse real-Wishart moment formula of Matsumoto, J. Theoret. Probab. 25
(2012), Theorem 2 / Section 5 and the mixed trace formulas in Theorem 3 /
Section 6.1 (arXiv:1004.4717).  The powers of `N` and the generous constant
below are our derived estimates, not verbatim theorem statements in that
source.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

/-- One common generous constant for the five literal Bell-four log-score
monomials. -/
def centeredLogScoreFourthMomentConstant : ℝ :=
  denseClassicalMomentConstant ^ 4

def concreteCenteredEll (r N K : ℕ) :
    ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
  fun p ↦ concreteCenteredLogScore r N K p.2 p.1

/-! Each literal monomial has one external moment package.  Its two public
projections retain finiteness at `2N+8≤K` and the sharp bound at `16N≤K`,
without counting those projections as independent scientific assumptions. -/

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

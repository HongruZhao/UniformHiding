import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalMomentBoundsExternal

/-!
# Primitive centered matrix-trace moments

These are narrowly scoped fixed-degree beta-prime/Wishart moment inputs for
the exact third projective contraction.  They concern only the three literal
traces of `S=Y-(N+1)I` and their displayed monomials.  No likelihood score,
event derivative, total variation, or hiding estimate occurs here.

Source category: Muirhead, *Aspects of Multivariate Statistical Theory*
(1982), Chapter 3, Sections 3.2--3.3, together with fixed-degree Gaussian
Holder/Poincare estimates.  The margin `2N+8≤K` supplies the displayed
finiteness assertions; the dimension-uniform sharp norm scales are asserted
only in the dense range `16N≤K`.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-- `Tr S`, for `S=Y-(N+1)I`. -/
def betaPrimeCenteredMatrixTraceOne (N K : ℕ) (u : Fin 4 → ℝ) : ℝ :=
  betaPrimeYTraceOne N K u - (N : ℝ) * ((N : ℝ) + 1)

/-- `Tr S²`. -/
def betaPrimeCenteredMatrixTraceTwo (N K : ℕ) (u : Fin 4 → ℝ) : ℝ :=
  betaPrimeYTraceTwo N K u -
    2 * ((N : ℝ) + 1) * betaPrimeYTraceOne N K u +
    (N : ℝ) * ((N : ℝ) + 1) ^ 2

/-- `Tr S³`. -/
def betaPrimeCenteredMatrixTraceThree (N K : ℕ) (u : Fin 4 → ℝ) : ℝ :=
  betaPrimeYTraceThree N K u -
    3 * ((N : ℝ) + 1) * betaPrimeYTraceTwo N K u +
    3 * ((N : ℝ) + 1) ^ 2 * betaPrimeYTraceOne N K u -
    (N : ℝ) * ((N : ℝ) + 1) ^ 3

/-! Each external source input below is bundled once: finiteness at the
order-three threshold and, conditionally, the sharp dense-regime norm bound.
This avoids treating the two projections of one classical moment estimate as
two independent axioms.  The public projection theorem names are retained. -/

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

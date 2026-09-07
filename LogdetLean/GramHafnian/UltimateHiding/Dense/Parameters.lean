import Mathlib.Probability.Distributions.Beta
import Mathlib.Tactic

/-!
# Parameters for the dense one column recursion

This file formalizes the scalar data in the exact ambient recursion.  It does
not assert the Haar recursion itself.  In the complex Haar setting the radial
eigenvalue has beta parameters `m - N + 1` and `N`, without the factors of two
that occur in the real orthogonal setting.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

/-- Left beta shape in the one column deletion recursion. -/
def oneColumnBetaShapeLeft (m N : ℕ) : ℝ :=
  (m : ℝ) - (N : ℝ) + 1

/-- Right beta shape in the one column deletion recursion. -/
def oneColumnBetaShapeRight (N : ℕ) : ℝ :=
  N

/-- The exact beta law of the surviving eigenvalue `q = 1 - ‖u‖²`. -/
def oneColumnBetaLaw (m N : ℕ) : Measure ℝ :=
  betaMeasure (oneColumnBetaShapeLeft m N) (oneColumnBetaShapeRight N)

theorem oneColumnBetaShapeLeft_pos {m N : ℕ} (hNm : N ≤ m) :
    0 < oneColumnBetaShapeLeft m N := by
  unfold oneColumnBetaShapeLeft
  rw [← Nat.cast_sub hNm]
  positivity

theorem oneColumnBetaShapeRight_pos {N : ℕ} (hN : 1 ≤ N) :
    0 < oneColumnBetaShapeRight N := by
  unfold oneColumnBetaShapeRight
  exact_mod_cast hN

theorem oneColumnBetaLaw_isProbability {m N : ℕ}
    (hN : 1 ≤ N) (hNm : N ≤ m) :
    IsProbabilityMeasure (oneColumnBetaLaw m N) := by
  unfold oneColumnBetaLaw
  exact isProbabilityMeasureBeta
    (oneColumnBetaShapeLeft_pos hNm)
    (oneColumnBetaShapeRight_pos hN)

/-- The scalar normalization in the logarithm of the ambient update. -/
def oneColumnScalarLog (m : ℕ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (1 + 1 / (m : ℝ))

/-- The rank one logarithmic coefficient associated with a beta sample `q`. -/
def oneColumnRankOneLog (q : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log q

/-- The scalar coefficient after separating the trace free direction. -/
def oneColumnCenteredScalarLog (m N : ℕ) (q : ℝ) : ℝ :=
  oneColumnScalarLog m + oneColumnRankOneLog q / (N : ℝ)

/-- The trace free part of a rank one direction, written in an arbitrary real
module.  The argument called `identity` will later be instantiated by the
identity matrix. -/
def centeredRankOneDirection
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (N : ℕ) (identity rankOne : E) : E :=
  rankOne - ((N : ℝ)⁻¹) • identity

/-- Exact algebraic split

`a I + b P = (a + b/N) I + b (P - I/N)`.

This is the finite algebra used before the scalar and orbital estimates are
handled separately. -/
theorem oneColumn_logarithm_split
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {N : ℕ} (hN : 1 ≤ N) (m : ℕ) (q : ℝ)
    (identity rankOne : E) :
    oneColumnScalarLog m • identity + oneColumnRankOneLog q • rankOne =
      oneColumnCenteredScalarLog m N q • identity +
        oneColumnRankOneLog q •
          centeredRankOneDirection N identity rankOne := by
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  simp only [oneColumnCenteredScalarLog, centeredRankOneDirection,
    div_eq_mul_inv, add_smul, smul_sub, mul_smul]
  module

end

end LogdetLean.GramHafnian.UltimateHiding.Dense

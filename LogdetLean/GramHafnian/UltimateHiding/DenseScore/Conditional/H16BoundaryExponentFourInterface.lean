import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalCOEExternal
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# H16 order-four boundary exponents: exact interface

This lightweight module fixes the scalar contract used by the corrected
zero-extension proof.  It contains no matrix, boundary-measure, `L1`, event,
or H5 conclusion.  The intended implementation is elementary real arithmetic
and `Real.rpow` calculus.

This file is an uncompiled interface checkpoint.  It introduces no axiom and
does not claim that a value of the structure has been constructed.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-- Exact scalar facts at the threshold `2*N+8 <= K`.

The strict positivity field is deliberately indexed by `Fin 4`, so it covers
only boundary traces of orders zero through three.  The fourth-order field is
integrability (`alpha - 4 > -1`), not positivity or boundedness. -/
structure COEBoundaryExponentFourFacts
    (N K : ℕ) (_hboundary : 2 * N + 8 ≤ K) : Prop where
  exponent_ge_seven_halves :
    (7 : ℝ) / 2 ≤ coeCornerDensityExponent N K
  boundary_trace_exponent_pos :
    ∀ s : Fin 4,
      0 < coeCornerDensityExponent N K - ((s : ℕ) : ℝ)
  fourth_exponent_gt_neg_one :
    -1 < coeCornerDensityExponent N K - 4
  boundary_rpow_tendsto_zero :
    ∀ s : Fin 4,
      Tendsto
        (fun epsilon : ℝ ↦
          epsilon ^
            (coeCornerDensityExponent N K - ((s : ℕ) : ℝ)))
        (𝓝[>] 0) (𝓝 0)
  fourth_scalar_integrable :
    IntegrableOn
      (fun u : ℝ ↦
        u ^ (coeCornerDensityExponent N K - 4))
      (Set.Ioc 0 1)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

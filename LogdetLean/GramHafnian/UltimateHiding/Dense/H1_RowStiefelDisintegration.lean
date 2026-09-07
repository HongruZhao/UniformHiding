import LogdetLean.GramHafnian.UltimateHiding.Dense.H1_ColumnParameterAlgebra
import LogdetLean.GramHafnian.UltimateHiding.Dense.H1_RowDeletionCoupling
import LogdetLean.GramHafnian.UltimateHiding.Dense.H1_RightInvariance
import LogdetLean.GramHafnian.UltimateHiding.Dense.H1_OrbitMeasureIdentification

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

open LogdetLean.GramHafnian.CurrentPRL

theorem complexRowStiefel_scaledLastColumnDisintegration_external
    (N m : ℕ) (hN : 1 ≤ N) (hNm : N ≤ m) :
    Measure.map (sqrtScaledDeleteLastTopRows (hNm.trans (Nat.le_succ m)))
        (unitaryHaarProbabilityMeasure (m + 1)) =
      Measure.map (scaledRowStiefelDeletionUpdate hNm)
        ((unitaryHaarProbabilityMeasure m).prod
          (concreteOneColumnParameterLaw m N)) := by
  let rho := h1RowDeletionCouplingSource m
  let X := h1RowDeletionCouplingLeft (hNm.trans (Nat.le_succ m))
  let Y := h1RowDeletionCouplingRight hN hNm
  have hcoupled : Measure.map X rho = Measure.map Y rho := by
    apply rightUnitaryInvariant_map_eq_of_ae_hermitianRowGram_eq
      rho X Y
    · exact measurable_h1RowDeletionCouplingLeft
        (hNm.trans (Nat.le_succ m))
    · exact measurable_h1RowDeletionCouplingRight hN hNm
    · intro V
      dsimp only [X, rho]
      rw [map_h1RowDeletionCouplingLeft]
      exact map_sqrtScaledDeleteLastTopRows_rightUnitary_invariant
        (hNm.trans (Nat.le_succ m)) V
    · intro V
      dsimp only [Y, rho]
      rw [map_h1RowDeletionCouplingRight]
      exact map_scaledRowStiefelDeletionUpdate_rightUnitary_invariant
        hN hNm V
    · filter_upwards [] with p
      let qv := h1AmbientUnitaryColumnParameter hN hNm p.1
      have hq : 0 ≤ qv.1 := by
        exact h1HaarColumnParameter_fst_nonneg hN hNm _
      change hermitianRowGram
          (sqrtScaledDeleteLastTopRows
            (hNm.trans (Nat.le_succ m)) p.1) =
        hermitianRowGram
          (scaledRowStiefelDeletionUpdate hNm (p.2, qv))
      rw [hermitianRowGram_sqrtScaledDeleteLastTopRows,
        hermitianRowGram_scaledRowStiefelDeletionUpdate hN hNm p.2
          qv.1 hq qv.2]
      unfold qv h1AmbientUnitaryColumnParameter
      rw [h1AmbientUnitaryColumnParameter_rankOne hN hNm p.1]
  calc
    Measure.map (sqrtScaledDeleteLastTopRows
        (hNm.trans (Nat.le_succ m)))
        (unitaryHaarProbabilityMeasure (m + 1)) =
        Measure.map X rho := by
      exact (map_h1RowDeletionCouplingLeft
        (hNm.trans (Nat.le_succ m))).symm
    _ = Measure.map Y rho := hcoupled
    _ = Measure.map (scaledRowStiefelDeletionUpdate hNm)
        ((unitaryHaarProbabilityMeasure m).prod
          (concreteOneColumnParameterLaw m N)) :=
      map_h1RowDeletionCouplingRight hN hNm

end

end LogdetLean.GramHafnian.UltimateHiding.Dense


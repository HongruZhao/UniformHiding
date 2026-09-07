import LogdetLean.GramHafnian.UltimateHiding.Dense.H1_HaarColumnParameter
import LogdetLean.GramHafnian.UltimateHiding.Dense.H1_RowStiefelDefinitions

/-!
# Common coupling for the two H1 row-deletion laws

The coupling uses an ambient Haar unitary and an independent lower-dimensional
Haar unitary.  Its left coordinate is the deleted ambient row block; its right
coordinate is the one-column update driven by the ambient last-column
parameter.  This file proves the two marginal identities only.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

open LogdetLean.GramHafnian.LocalAnticoncentration

/-- The last-column beta/sphere parameter extracted from an ambient Haar
unitary. -/
def h1AmbientUnitaryColumnParameter {N m : ℕ}
    (hN : 1 ≤ N) (hNm : N ≤ m)
    (U : Matrix.unitaryGroup (Fin (m + 1)) ℂ) :
    ℝ × ComplexUnitSphere N :=
  h1HaarColumnParameter hN hNm
    (haarLastColumnSphere (Nat.succ_le_succ (Nat.zero_le m)) U)

theorem measurable_h1AmbientUnitaryColumnParameter
    {N m : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    Measurable (h1AmbientUnitaryColumnParameter hN hNm) :=
  (measurable_h1HaarColumnParameter hN hNm).comp
    (measurable_haarLastColumnSphere
      (Nat.succ_le_succ (Nat.zero_le m)))

/-- The common source probability for H1. -/
def h1RowDeletionCouplingSource (m : ℕ) : Measure
    (Matrix.unitaryGroup (Fin (m + 1)) ℂ ×
      Matrix.unitaryGroup (Fin m) ℂ) :=
  (unitaryHaarProbabilityMeasure (m + 1)).prod
    (unitaryHaarProbabilityMeasure m)

instance h1RowDeletionCouplingSource_isProbability (m : ℕ) :
    IsProbabilityMeasure (h1RowDeletionCouplingSource m) := by
  unfold h1RowDeletionCouplingSource
  letI : IsProbabilityMeasure (unitaryHaarProbabilityMeasure (m + 1)) :=
    unitaryHaarProbabilityMeasure_isProbability (m + 1)
  letI : IsProbabilityMeasure (unitaryHaarProbabilityMeasure m) :=
    unitaryHaarProbabilityMeasure_isProbability m
  infer_instance

/-- Left coordinate of the H1 coupling: delete the last ambient column. -/
def h1RowDeletionCouplingLeft {N m : ℕ} (hNsucc : N ≤ m + 1) :
    Matrix.unitaryGroup (Fin (m + 1)) ℂ ×
        Matrix.unitaryGroup (Fin m) ℂ →
      Matrix (Fin N) (Fin m) ℂ :=
  fun p ↦ sqrtScaledDeleteLastTopRows hNsucc p.1

theorem measurable_h1RowDeletionCouplingLeft
    {N m : ℕ} (hNsucc : N ≤ m + 1) :
    Measurable (h1RowDeletionCouplingLeft hNsucc) :=
  (measurable_sqrtScaledDeleteLastTopRows hNsucc).comp measurable_fst

/-- Right coordinate of the H1 coupling: update an independent Haar row
block using the ambient last-column parameter. -/
def h1RowDeletionCouplingRight {N m : ℕ}
    (hN : 1 ≤ N) (hNm : N ≤ m) :
    Matrix.unitaryGroup (Fin (m + 1)) ℂ ×
        Matrix.unitaryGroup (Fin m) ℂ →
      Matrix (Fin N) (Fin m) ℂ :=
  fun p ↦ scaledRowStiefelDeletionUpdate hNm
    (p.2, h1AmbientUnitaryColumnParameter hN hNm p.1)

theorem measurable_h1RowDeletionCouplingRight
    {N m : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    Measurable (h1RowDeletionCouplingRight hN hNm) := by
  exact (measurable_scaledRowStiefelDeletionUpdate hNm).comp
    (measurable_snd.prodMk
      ((measurable_h1AmbientUnitaryColumnParameter hN hNm).comp
        measurable_fst))

/-- The left coupling marginal is the literal deleted-row law. -/
theorem map_h1RowDeletionCouplingLeft
    {N m : ℕ} (hNsucc : N ≤ m + 1) :
    Measure.map (h1RowDeletionCouplingLeft hNsucc)
        (h1RowDeletionCouplingSource m) =
      Measure.map (sqrtScaledDeleteLastTopRows hNsucc)
        (unitaryHaarProbabilityMeasure (m + 1)) := by
  letI : IsProbabilityMeasure (unitaryHaarProbabilityMeasure m) :=
    unitaryHaarProbabilityMeasure_isProbability m
  rw [show h1RowDeletionCouplingLeft hNsucc =
      sqrtScaledDeleteLastTopRows hNsucc ∘ Prod.fst by rfl]
  rw [← Measure.map_map
    (measurable_sqrtScaledDeleteLastTopRows hNsucc) measurable_fst]
  unfold h1RowDeletionCouplingSource
  rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- The right coupling marginal is the independent beta/sphere update law. -/
theorem map_h1RowDeletionCouplingRight
    {N m : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    Measure.map (h1RowDeletionCouplingRight hN hNm)
        (h1RowDeletionCouplingSource m) =
      Measure.map (scaledRowStiefelDeletionUpdate hNm)
        ((unitaryHaarProbabilityMeasure m).prod
          (concreteOneColumnParameterLaw m N)) := by
  let ambient := unitaryHaarProbabilityMeasure (m + 1)
  let lower := unitaryHaarProbabilityMeasure m
  let parameter := concreteOneColumnParameterLaw m N
  let pmap := h1AmbientUnitaryColumnParameter hN hNm
  let reorder : Matrix.unitaryGroup (Fin (m + 1)) ℂ ×
      Matrix.unitaryGroup (Fin m) ℂ →
      Matrix.unitaryGroup (Fin m) ℂ ×
        (ℝ × ComplexUnitSphere N) :=
    Prod.map id pmap ∘ Prod.swap
  have hpmap : Measurable pmap :=
    measurable_h1AmbientUnitaryColumnParameter hN hNm
  have hreorder : Measurable reorder :=
    (measurable_id.prodMap hpmap).comp measurable_swap
  have hparam : Measure.map pmap ambient = parameter := by
    dsimp only [pmap, ambient, parameter, h1AmbientUnitaryColumnParameter]
    exact map_h1HaarColumnParameter_haarLastColumn hN hNm
  have hreorderLaw : Measure.map reorder (ambient.prod lower) =
      lower.prod parameter := by
    calc
      Measure.map reorder (ambient.prod lower) =
          Measure.map (Prod.map id pmap)
            (Measure.map Prod.swap (ambient.prod lower)) := by
        exact (Measure.map_map (measurable_id.prodMap hpmap)
          measurable_swap).symm
      _ = Measure.map (Prod.map id pmap) (lower.prod ambient) := by
        rw [Measure.prod_swap]
      _ = (Measure.map id lower).prod (Measure.map pmap ambient) :=
        (Measure.map_prod_map lower ambient measurable_id hpmap).symm
      _ = lower.prod parameter := by rw [Measure.map_id, hparam]
  have hfun : h1RowDeletionCouplingRight hN hNm =
      scaledRowStiefelDeletionUpdate hNm ∘ reorder := by
    funext p
    rfl
  rw [hfun, ← Measure.map_map
    (measurable_scaledRowStiefelDeletionUpdate hNm) hreorder]
  change Measure.map (scaledRowStiefelDeletionUpdate hNm)
      (Measure.map reorder (ambient.prod lower)) = _
  rw [hreorderLaw]

end

end LogdetLean.GramHafnian.UltimateHiding.Dense

import LogdetLean.GramHafnian.ThreePaper.GBSDefinitions
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Equiv.Fintype

/-!
# Haar row permutation symmetry for the current manuscript

This module closes the row symmetry step used for an independently and
uniformly chosen collision free output pattern.  An arbitrary injective list
of `N` selected rows is related to the canonical first `N` rows by a finite
permutation.  Its permutation matrix is unitary, and normalized Haar measure
is invariant under left multiplication by that unitary.  Consequently the
selected block has exactly the same law as the canonical upper left block.

No new external axiom is introduced here.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.LocalAnticoncentration

noncomputable section

/-! ## A permutation unitary carrying canonical rows to selected rows -/

/-- A permutation extending the assignment from the first `N` row indices
to an arbitrary injective selected row list. -/
def selectedRowPermutation {M N : ℕ} (hNM : N <= M)
    (rows : Fin N ↪ Fin M) : Equiv.Perm (Fin M) :=
  Classical.choose
    (Equiv.Perm.exists_extending_pair
      (Fin.castLE hNM) rows (Fin.castLE_injective hNM) rows.injective)

@[simp]
theorem selectedRowPermutation_castLE {M N : ℕ} (hNM : N <= M)
    (rows : Fin N ↪ Fin M) (i : Fin N) :
    selectedRowPermutation hNM rows (Fin.castLE hNM i) = rows i :=
  (Classical.choose_spec
    (Equiv.Perm.exists_extending_pair
      (Fin.castLE hNM) rows (Fin.castLE_injective hNM) rows.injective)) i

/-- The permutation matrix, regarded as an element of the unitary group. -/
def selectedRowPermutationUnitary {M N : ℕ} (hNM : N <= M)
    (rows : Fin N ↪ Fin M) : Matrix.unitaryGroup (Fin M) ℂ := by
  let sigma := selectedRowPermutation hNM rows
  refine ⟨sigma.permMatrix ℂ, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_permMatrix]
  rw [← Matrix.permMatrix_mul]
  simp

/-! ## Selected blocks -/

/-- The `N x K` block obtained from an arbitrary injective selected row list
and the canonical first `K` columns. -/
def selectedRowsUnitaryBlock {M N K : ℕ} (hKM : K <= M)
    (rows : Fin N ↪ Fin M) (U : Matrix.unitaryGroup (Fin M) ℂ) :
    Matrix (Fin N) (Fin K) ℂ :=
  fun i j =>
    (U : Matrix (Fin M) (Fin M) ℂ) (rows i) (Fin.castLE hKM j)

@[fun_prop]
theorem measurable_selectedRowsUnitaryBlock {M N K : ℕ}
    (hKM : K <= M) (rows : Fin N ↪ Fin M) :
    Measurable (selectedRowsUnitaryBlock hKM rows) := by
  unfold selectedRowsUnitaryBlock
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  have hcoe : Measurable
      (fun U : Matrix.unitaryGroup (Fin M) ℂ =>
        (U : Matrix (Fin M) (Fin M) ℂ)) :=
    measurable_subtype_coe
  exact (measurable_pi_apply (Fin.castLE hKM j)).comp
    ((measurable_pi_apply (rows i)).comp hcoe)

/-- Left multiplication on the unitary subtype is measurable for its induced
matrix measurable structure.  We prove this entrywise because the local
unitary subtype does not expose a global `MeasurableMul` instance. -/
theorem measurable_unitary_mul_left {M : ℕ}
    (P : Matrix.unitaryGroup (Fin M) ℂ) :
    Measurable (fun U : Matrix.unitaryGroup (Fin M) ℂ => P * U) := by
  apply Measurable.subtype_mk
  change Measurable
    (fun U : Matrix.unitaryGroup (Fin M) ℂ =>
      (P : Matrix (Fin M) (Fin M) ℂ) *
        (U : Matrix (Fin M) (Fin M) ℂ))
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [Matrix.mul_apply]
  refine Finset.measurable_sum _ fun a _ => ?_
  have hcoe : Measurable
      (fun U : Matrix.unitaryGroup (Fin M) ℂ =>
        (U : Matrix (Fin M) (Fin M) ℂ)) :=
    measurable_subtype_coe
  exact measurable_const.mul
    ((measurable_pi_apply j).comp ((measurable_pi_apply a).comp hcoe))

/-- Left multiplication by the permutation unitary turns the canonical block
into the block on the selected rows. -/
theorem topLeftUnitaryBlock_selectedRowPermutation_mul
    {M N K : ℕ} (hNM : N <= M) (hKM : K <= M)
    (rows : Fin N ↪ Fin M) (U : Matrix.unitaryGroup (Fin M) ℂ) :
    topLeftUnitaryBlock hNM hKM
        (selectedRowPermutationUnitary hNM rows * U) =
      selectedRowsUnitaryBlock hKM rows U := by
  ext i j
  change
    ((selectedRowPermutation hNM rows).permMatrix ℂ *
        (U : Matrix (Fin M) (Fin M) ℂ))
          (Fin.castLE hNM i) (Fin.castLE hKM j) =
      (U : Matrix (Fin M) (Fin M) ℂ) (rows i) (Fin.castLE hKM j)
  simpa [Matrix.mul_apply] using congrFun
    (Matrix.permMatrix_mulVec (R := ℂ)
      (selectedRowPermutation hNM rows)
      (v := fun a =>
        (U : Matrix (Fin M) (Fin M) ℂ) a (Fin.castLE hKM j)))
    (Fin.castLE hNM i)

/-! ## Exact equality of selected and canonical block laws -/

/-- The law of every fixed injective selected row block is exactly the law of
the canonical upper left block.  This is the literal Haar row symmetry bridge
used by the manuscript. -/
theorem selectedRowsUnitaryBlock_map_eq_topLeftUnitaryBlock_map
    (H : UnitaryHaarProbabilityFamily) {M N K : ℕ}
    (hNM : N <= M) (hKM : K <= M) (rows : Fin N ↪ Fin M) :
    Measure.map (selectedRowsUnitaryBlock hKM rows) (H.law M) =
      Measure.map (topLeftUnitaryBlock hNM hKM) (H.law M) := by
  let P := selectedRowPermutationUnitary hNM rows
  letI : IsProbabilityMeasure (H.law M) := H.isProbability M
  letI : Measure.IsHaarMeasure (H.law M) := H.isHaar M
  calc
    Measure.map (selectedRowsUnitaryBlock hKM rows) (H.law M) =
        Measure.map
          (fun U => topLeftUnitaryBlock hNM hKM (P * U))
          (H.law M) := by
            apply Measure.map_congr
            filter_upwards with U
            exact (topLeftUnitaryBlock_selectedRowPermutation_mul
              hNM hKM rows U).symm
    _ = Measure.map (topLeftUnitaryBlock hNM hKM)
          (Measure.map (fun U => P * U) (H.law M)) := by
            rw [Measure.map_map]
            · rfl
            · exact measurable_topLeftUnitaryBlock hNM hKM
            · exact measurable_unitary_mul_left P
    _ = Measure.map (topLeftUnitaryBlock hNM hKM) (H.law M) := by
          rw [MeasureTheory.map_mul_left_eq_self]

/-! ## Gram, hafnian, and uniform pattern consequences -/

/-- Scale the transpose Gram matrix by the ambient mode number. -/
def scaledRectangularTransposeGram (M N K : ℕ)
    (G : Matrix (Fin N) (Fin K) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (M : ℂ) * rectangularTransposeGram G i j

/-- Law of the scaled transpose Gram matrix formed from selected rows. -/
def selectedRowsScaledTransposeGramLaw
    (H : UnitaryHaarProbabilityFamily) {M N K : ℕ}
    (hKM : K <= M) (rows : Fin N ↪ Fin M) :
    Measure (Matrix (Fin N) (Fin N) ℂ) :=
  Measure.map
    (scaledRectangularTransposeGram M N K)
    (Measure.map (selectedRowsUnitaryBlock hKM rows) (H.law M))

theorem measurable_scaledRectangularTransposeGram (M N K : ℕ) :
    Measurable (scaledRectangularTransposeGram M N K) := by
  unfold scaledRectangularTransposeGram
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  exact measurable_const.mul
    ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp
        (measurable_rectangularTransposeGram N K)))

/-- Selected row scaling and transpose Gram have the canonical law. -/
theorem selectedRowsScaledTransposeGramLaw_eq
    (H : UnitaryHaarProbabilityFamily) {M N K : ℕ}
    (hNM : N <= M) (hKM : K <= M) (rows : Fin N ↪ Fin M) :
    selectedRowsScaledTransposeGramLaw H hKM rows =
      scaledHaarTransposeGramLaw H M N K := by
  unfold selectedRowsScaledTransposeGramLaw scaledHaarTransposeGramLaw
  rw [dif_pos ⟨hNM, hKM⟩]
  rw [selectedRowsUnitaryBlock_map_eq_topLeftUnitaryBlock_map
    H hNM hKM rows]
  rw [Measure.map_map]
  · rfl
  · exact measurable_scaledRectangularTransposeGram M N K
  · exact measurable_topLeftUnitaryBlock hNM hKM

/-- The selected pattern scaled Gram hafnian law. -/
def selectedRowsScaledGramHafnianLaw
    (H : UnitaryHaarProbabilityFamily) {M n K : ℕ}
    (hKM : K <= M) (rows : Fin (2 * n) ↪ Fin M) : Measure ℂ :=
  Measure.map (hafnianMatrixObservable n)
    (selectedRowsScaledTransposeGramLaw H hKM rows)

/-- Every fixed collision free selected row pattern has the canonical scaled
Gram hafnian law. -/
theorem selectedRowsScaledGramHafnianLaw_eq
    (H : UnitaryHaarProbabilityFamily) {M n K : ℕ}
    (hNM : 2 * n <= M) (hKM : K <= M)
    (rows : Fin (2 * n) ↪ Fin M) :
    selectedRowsScaledGramHafnianLaw H hKM rows =
      scaledHaarGramHafnianLaw H M n K := by
  unfold selectedRowsScaledGramHafnianLaw scaledHaarGramHafnianLaw
  rw [selectedRowsScaledTransposeGramLaw_eq H hNM hKM rows]

/-- An independently uniform choice from any finite family of injective row
patterns has exactly the canonical event probability.  No union bound and no
pattern count appear. -/
theorem uniformSelectedRowsProbability_eq_canonical
    (H : UnitaryHaarProbabilityFamily) {M n K : ℕ}
    (hNM : 2 * n <= M) (hKM : K <= M)
    {Pattern : Type*} [Fintype Pattern] [Nonempty Pattern]
    (rows : Pattern → (Fin (2 * n) ↪ Fin M)) (event : Set ℂ) :
    uniformFinitePatternProbability
        (fun pattern =>
          (selectedRowsScaledGramHafnianLaw H hKM (rows pattern)).real event) =
      (scaledHaarGramHafnianLaw H M n K).real event := by
  apply uniformFinitePatternProbability_eq_of_rowSymmetry
  exact fun pattern => selectedRowsScaledGramHafnianLaw_eq
    H hNM hKM (rows pattern)

/-- Bound form of independent uniform pattern selection, now with Haar row
symmetry discharged rather than assumed. -/
theorem uniformSelectedRowsProbability_le_canonicalBound
    (H : UnitaryHaarProbabilityFamily) {M n K : ℕ}
    (hNM : 2 * n <= M) (hKM : K <= M)
    {Pattern : Type*} [Fintype Pattern] [Nonempty Pattern]
    (rows : Pattern → (Fin (2 * n) ↪ Fin M))
    (event : Set ℂ) (bound : ℝ)
    (hbound : (scaledHaarGramHafnianLaw H M n K).real event <= bound) :
    uniformFinitePatternProbability
        (fun pattern =>
          (selectedRowsScaledGramHafnianLaw H hKM (rows pattern)).real event) <=
      bound := by
  rw [uniformSelectedRowsProbability_eq_canonical
    H hNM hKM rows event]
  exact hbound

end

end LogdetLean.GramHafnian.LocalAnticoncentration

import LogdetLean.GramHafnian.UltimateHiding.Dense.RowStiefelDeletionExternal
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

/-!
# Deriving the H1 Gram recursion from structural row-Stiefel deletion

All results in this file are internal consequences of the K-free,
Gram-free structural disintegration in `RowStiefelDeletionExternal`.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

open LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.UltimateHiding
open LogdetLean.GramHafnian.UltimateHiding.Sparse

/-- Restrict an `N x m` row block to its first `K` columns. -/
def restrictInitialColumns {N K m : ℕ} (hKm : K ≤ m)
    (X : Matrix (Fin N) (Fin m) ℂ) : Matrix (Fin N) (Fin K) ℂ :=
  fun i j => X i (Fin.castLE hKm j)

theorem measurable_restrictInitialColumns {N K m : ℕ} (hKm : K ≤ m) :
    Measurable (restrictInitialColumns (N := N) hKm) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  exact (measurable_pi_apply (Fin.castLE hKm j)).comp
    (measurable_pi_apply i)

theorem restrictInitialColumns_sqrtScaledFullTopRows
    {N K m : ℕ} (hNm : N ≤ m) (hKm : K ≤ m)
    (U : Matrix.unitaryGroup (Fin m) ℂ) :
    restrictInitialColumns hKm (sqrtScaledFullTopRows hNm U) =
      sqrtScaledHaarBlockMatrix hNm hKm U := by
  ext i j
  simp [restrictInitialColumns, sqrtScaledFullTopRows,
    sqrtScaledHaarBlockMatrix, topLeftUnitaryBlock]

theorem restrictInitialColumns_sqrtScaledDeleteLastTopRows
    {N K m : ℕ} (hNsucc : N ≤ m + 1) (hKm : K ≤ m)
    (U : Matrix.unitaryGroup (Fin (m + 1)) ℂ) :
    restrictInitialColumns hKm (sqrtScaledDeleteLastTopRows hNsucc U) =
      sqrtScaledHaarBlockMatrix hNsucc
        (hKm.trans (Nat.le_succ m)) U := by
  ext i j
  simp [restrictInitialColumns, sqrtScaledDeleteLastTopRows,
    sqrtScaledHaarBlockMatrix, topLeftUnitaryBlock]

theorem restrictInitialColumns_mul
    {N K m : ℕ} (hKm : K ≤ m)
    (F : Matrix (Fin N) (Fin N) ℂ) (X : Matrix (Fin N) (Fin m) ℂ) :
    restrictInitialColumns hKm (F * X) =
      F * restrictInitialColumns hKm X := by
  ext i j
  rfl

/-- Rectangular version of the one-column update. -/
def scaledRectangularOneColumnUpdate (m N K : ℕ) :
    Matrix (Fin N) (Fin K) ℂ × (ℝ × ComplexUnitSphere N) →
      Matrix (Fin N) (Fin K) ℂ :=
  fun p => concreteOneColumnFactor m N p.2.1 p.2.2 * p.1

theorem measurable_scaledRectangularOneColumnUpdate (m N K : ℕ) :
    Measurable (scaledRectangularOneColumnUpdate m N K) := by
  have hF : Measurable fun p :
      Matrix (Fin N) (Fin K) ℂ × (ℝ × ComplexUnitSphere N) =>
      concreteOneColumnFactor m N p.2.1 p.2.2 :=
    (measurable_concreteOneColumnFactor m N).comp measurable_snd
  exact measurable_complexMatrix_mul hF measurable_fst

/-- The structural atom after restricting to the first `K` columns. -/
theorem map_sqrtScaledHaarBlockMatrix_succ_eq_update
    (N K m : ℕ) (hN : 1 ≤ N) (hNm : N ≤ m) (hKm : K ≤ m) :
    Measure.map
        (sqrtScaledHaarBlockMatrix
          (hNm.trans (Nat.le_succ m))
          (hKm.trans (Nat.le_succ m)))
        (unitaryHaarProbabilityMeasure (m + 1)) =
      Measure.map
        (fun p : Matrix.unitaryGroup (Fin m) ℂ ×
            (ℝ × ComplexUnitSphere N) =>
          concreteOneColumnFactor m N p.2.1 p.2.2 *
            sqrtScaledHaarBlockMatrix hNm hKm p.1)
        ((unitaryHaarProbabilityMeasure m).prod
          (concreteOneColumnParameterLaw m N)) := by
  let R := restrictInitialColumns (N := N) hKm
  have hR : Measurable R := measurable_restrictInitialColumns hKm
  have h := congrArg (Measure.map R)
    (complexRowStiefel_scaledLastColumnDisintegration_external
      N m hN hNm)
  rw [Measure.map_map hR
      (measurable_sqrtScaledDeleteLastTopRows
        (hNm.trans (Nat.le_succ m))),
    Measure.map_map hR (measurable_scaledRowStiefelDeletionUpdate hNm)] at h
  calc
    Measure.map
        (sqrtScaledHaarBlockMatrix
          (hNm.trans (Nat.le_succ m))
          (hKm.trans (Nat.le_succ m)))
        (unitaryHaarProbabilityMeasure (m + 1)) =
      Measure.map (R ∘
          sqrtScaledDeleteLastTopRows (hNm.trans (Nat.le_succ m)))
        (unitaryHaarProbabilityMeasure (m + 1)) := by
          apply Measure.map_congr
          filter_upwards with U
          exact (restrictInitialColumns_sqrtScaledDeleteLastTopRows
            (hNm.trans (Nat.le_succ m)) hKm U).symm
    _ = Measure.map (R ∘ scaledRowStiefelDeletionUpdate hNm)
        ((unitaryHaarProbabilityMeasure m).prod
          (concreteOneColumnParameterLaw m N)) := h
    _ = Measure.map
        (fun p : Matrix.unitaryGroup (Fin m) ℂ ×
            (ℝ × ComplexUnitSphere N) =>
          concreteOneColumnFactor m N p.2.1 p.2.2 *
            sqrtScaledHaarBlockMatrix hNm hKm p.1)
        ((unitaryHaarProbabilityMeasure m).prod
          (concreteOneColumnParameterLaw m N)) := by
          apply Measure.map_congr
          filter_upwards with p
          change restrictInitialColumns hKm
              (concreteOneColumnFactor m N p.2.1 p.2.2 *
                sqrtScaledFullTopRows hNm p.1) = _
          rw [restrictInitialColumns_mul,
            restrictInitialColumns_sqrtScaledFullTopRows]

/-- Exact scaled rectangular-block recursion obtained from the structural
Stiefel atom. -/
theorem sqrtScaledHaarBlockLaw_oneColumn
    (N K m : ℕ) (hN : 1 ≤ N) (hNm : N ≤ m) (hKm : K ≤ m) :
    sqrtScaledHaarBlockLaw canonicalUnitaryHaarProbabilityFamily
        (m + 1) N K =
      Measure.map (scaledRectangularOneColumnUpdate m N K)
        ((sqrtScaledHaarBlockLaw canonicalUnitaryHaarProbabilityFamily
            m N K).prod (concreteOneColumnParameterLaw m N)) := by
  let block : Matrix.unitaryGroup (Fin m) ℂ →
      Matrix (Fin N) (Fin K) ℂ :=
    sqrtScaledHaarBlockMatrix hNm hKm
  have hblock : Measurable block :=
    measurable_sqrtScaledHaarBlockMatrix hNm hKm
  have hid : Measurable (id : (ℝ × ComplexUnitSphere N) →
      ℝ × ComplexUnitSphere N) := measurable_id
  let _ : IsProbabilityMeasure (concreteOneColumnParameterLaw m N) :=
    concreteOneColumnParameterLaw_isProbability hN hNm
  have hprod := Measure.map_prod_map
    (unitaryHaarProbabilityMeasure m)
    (concreteOneColumnParameterLaw m N) hblock hid
  rw [Measure.map_id] at hprod
  have hsucc :
      sqrtScaledHaarBlockLaw canonicalUnitaryHaarProbabilityFamily
          (m + 1) N K =
        Measure.map
          (sqrtScaledHaarBlockMatrix
            (hNm.trans (Nat.le_succ m))
            (hKm.trans (Nat.le_succ m)))
          (unitaryHaarProbabilityMeasure (m + 1)) := by
    rw [sqrtScaledHaarBlockLaw,
      dif_pos ⟨hNm.trans (Nat.le_succ m), hKm.trans (Nat.le_succ m)⟩]
    rfl
  have hold :
      sqrtScaledHaarBlockLaw canonicalUnitaryHaarProbabilityFamily m N K =
        Measure.map block (unitaryHaarProbabilityMeasure m) := by
    rw [sqrtScaledHaarBlockLaw, dif_pos ⟨hNm, hKm⟩]
    rfl
  rw [hsucc, hold]
  rw [map_sqrtScaledHaarBlockMatrix_succ_eq_update N K m hN hNm hKm]
  rw [hprod, Measure.map_map
    (measurable_scaledRectangularOneColumnUpdate m N K)
    (hblock.prodMap hid)]
  apply Measure.map_congr
  filter_upwards with p
  rfl

/-- The normalized transpose-Gram statistic applied to a scaled rectangular
block. -/
def normalizedBlockTransposeGram (N K : ℕ) :
    Matrix (Fin N) (Fin K) ℂ → Matrix (Fin N) (Fin N) ℂ :=
  fun X => normalizeTransposeGram N K (rectangularTransposeGram X)

theorem measurable_normalizedBlockTransposeGram (N K : ℕ) :
    Measurable (normalizedBlockTransposeGram N K) :=
  (measurable_normalizeTransposeGram N K).comp
    (measurable_rectangularTransposeGram N K)

/-- The stored normalized Haar Gram law is the image of the scaled block law
under `normalizedBlockTransposeGram`. -/
theorem concreteHaarAmbientLaw_eq_map_normalizedBlock
    (N K M : ℕ) (hNM : N ≤ M) (hKM : K ≤ M) :
    concreteHaarAmbientLaw canonicalUnitaryHaarProbabilityFamily N K M =
      Measure.map (normalizedBlockTransposeGram N K)
        (sqrtScaledHaarBlockLaw canonicalUnitaryHaarProbabilityFamily
          M N K) := by
  unfold concreteHaarAmbientLaw normalizedHaarTransposeGramLaw
  rw [← map_rectangularTransposeGram_sqrtScaledHaarBlockLaw
      canonicalUnitaryHaarProbabilityFamily hNM hKM,
    Measure.map_map (measurable_normalizeTransposeGram N K)
      (measurable_rectangularTransposeGram N K)]
  rfl

/-- Deterministic compatibility of the rectangular update with the
normalized transpose-Gram statistic. -/
theorem normalizedBlockTransposeGram_scaledRectangularUpdate
    (m N K : ℕ) (X : Matrix (Fin N) (Fin K) ℂ)
    (q : ℝ) (v : ComplexUnitSphere N) :
    normalizedBlockTransposeGram N K
        (concreteOneColumnFactor m N q v * X) =
      concreteOneColumnMatrixUpdate m N q v
        (normalizedBlockTransposeGram N K X) := by
  unfold normalizedBlockTransposeGram normalizeTransposeGram
    rectangularTransposeGram concreteOneColumnMatrixUpdate
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul]

/-- Kernel sampling semantics specialized to the concrete one-column
matrix update. -/
theorem concreteOneColumnMatrixKernel_comp_eq_map_prod
    {m N : ℕ}
    (mu : Measure (Matrix (Fin N) (Fin N) ℂ))
    [IsProbabilityMeasure mu]
    (hN : 1 ≤ N) (hNm : N ≤ m) :
    concreteOneColumnMatrixKernel m N ∘ₘ mu =
      Measure.map
        (fun p : Matrix (Fin N) (Fin N) ℂ ×
            (ℝ × ComplexUnitSphere N) =>
          concreteOneColumnMatrixUpdate m N p.2.1 p.2.2 p.1)
        (mu.prod (concreteOneColumnParameterLaw m N)) := by
  let _ : IsProbabilityMeasure (concreteOneColumnParameterLaw m N) :=
    concreteOneColumnParameterLaw_isProbability hN hNm
  let update : Matrix (Fin N) (Fin N) ℂ ×
      (ℝ × ComplexUnitSphere N) → Matrix (Fin N) (Fin N) ℂ :=
    fun p => concreteOneColumnMatrixUpdate m N p.2.1 p.2.2 p.1
  have hupdate : Measurable update :=
    measurable_concreteOneColumnMatrixUpdate m N
  change
    (((Kernel.id : Kernel (Matrix (Fin N) (Fin N) ℂ)
          (Matrix (Fin N) (Fin N) ℂ)) ×ₖ
        Kernel.const (Matrix (Fin N) (Fin N) ℂ)
          (concreteOneColumnParameterLaw m N)).map update) ∘ₘ mu = _
  ext A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _),
    Measure.map_apply hupdate hA, Measure.prod_apply (hupdate hA)]
  congr 1
  funext X
  rw [Kernel.map_apply _ hupdate, Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod]
  rw [Measure.map_map hupdate measurable_prodMk_left]
  rw [Measure.map_apply (hupdate.comp measurable_prodMk_left) hA]
  rfl

/-- **H1 derived from the structural Stiefel disintegration.** -/
theorem complexStiefel_oneColumnRecursion_from_rowStiefel
    (N K m : ℕ)
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKm : K ≤ m) :
    concreteHaarAmbientLaw canonicalUnitaryHaarProbabilityFamily N K (m + 1) =
      concreteOneColumnMatrixKernel m N ∘ₘ
        concreteHaarAmbientLaw canonicalUnitaryHaarProbabilityFamily N K m := by
  have hNm : N ≤ m := hNK.trans hKm
  have hNsucc : N ≤ m + 1 := hNm.trans (Nat.le_succ m)
  have hKsucc : K ≤ m + 1 := hKm.trans (Nat.le_succ m)
  let oldBlock := sqrtScaledHaarBlockLaw
    canonicalUnitaryHaarProbabilityFamily m N K
  let param := concreteOneColumnParameterLaw m N
  let gram := normalizedBlockTransposeGram N K
  let rectUpdate := scaledRectangularOneColumnUpdate m N K
  let matrixUpdate : Matrix (Fin N) (Fin N) ℂ ×
      (ℝ × ComplexUnitSphere N) → Matrix (Fin N) (Fin N) ℂ :=
    fun p => concreteOneColumnMatrixUpdate m N p.2.1 p.2.2 p.1
  have hgram : Measurable gram := measurable_normalizedBlockTransposeGram N K
  have hrect : Measurable rectUpdate :=
    measurable_scaledRectangularOneColumnUpdate m N K
  have hmatrix : Measurable matrixUpdate :=
    measurable_concreteOneColumnMatrixUpdate m N
  let _ : IsProbabilityMeasure oldBlock :=
    sqrtScaledHaarBlockLaw_isProbability
      canonicalUnitaryHaarProbabilityFamily hNm hKm
  let _ : IsProbabilityMeasure param :=
    concreteOneColumnParameterLaw_isProbability hN hNm
  let oldGram := concreteHaarAmbientLaw
    canonicalUnitaryHaarProbabilityFamily N K m
  have holdGram : oldGram = Measure.map gram oldBlock :=
    concreteHaarAmbientLaw_eq_map_normalizedBlock N K m hNm hKm
  let _ : IsProbabilityMeasure oldGram := by
    rw [holdGram]
    exact Measure.isProbabilityMeasure_map hgram.aemeasurable
  have hkernel := concreteOneColumnMatrixKernel_comp_eq_map_prod
    oldGram hN hNm
  have hblock := sqrtScaledHaarBlockLaw_oneColumn
    N K m hN hNm hKm
  calc
    concreteHaarAmbientLaw canonicalUnitaryHaarProbabilityFamily N K (m + 1) =
        Measure.map gram
          (sqrtScaledHaarBlockLaw canonicalUnitaryHaarProbabilityFamily
            (m + 1) N K) :=
      concreteHaarAmbientLaw_eq_map_normalizedBlock
        N K (m + 1) hNsucc hKsucc
    _ = Measure.map gram (Measure.map rectUpdate (oldBlock.prod param)) := by
      rw [hblock]
    _ = Measure.map (gram ∘ rectUpdate) (oldBlock.prod param) := by
      rw [Measure.map_map hgram hrect]
    _ = Measure.map (matrixUpdate ∘ Prod.map gram id)
          (oldBlock.prod param) := by
      apply Measure.map_congr
      filter_upwards with p
      exact normalizedBlockTransposeGram_scaledRectangularUpdate
        m N K p.1 p.2.1 p.2.2
    _ = Measure.map matrixUpdate
          (Measure.map (Prod.map gram id) (oldBlock.prod param)) := by
      rw [Measure.map_map hmatrix (hgram.prodMap measurable_id)]
    _ = Measure.map matrixUpdate
          ((Measure.map gram oldBlock).prod param) := by
      have hprodGram :=
        Measure.map_prod_map oldBlock param hgram measurable_id
      rw [Measure.map_id] at hprodGram
      exact congrArg (Measure.map matrixUpdate) hprodGram.symm
    _ = Measure.map matrixUpdate (oldGram.prod param) := by rw [holdGram]
    _ = concreteOneColumnMatrixKernel m N ∘ₘ oldGram := hkernel.symm
    _ = concreteOneColumnMatrixKernel m N ∘ₘ
          concreteHaarAmbientLaw canonicalUnitaryHaarProbabilityFamily N K m := rfl

end

end LogdetLean.GramHafnian.UltimateHiding.Dense

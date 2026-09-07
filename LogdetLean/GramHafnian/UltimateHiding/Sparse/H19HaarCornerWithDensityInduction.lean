import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19HaarCornerDensityInduction
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19HaarCornerSupportInterior
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19FiberwiseMeasureTransport
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Measure-theoretic induction for the Haar-corner density

This file isolates the measure-theoretic `N -> N+1` step suggested by the
column decomposition of a Haar corner.  The probabilistic representation of
the new column is deliberately a theorem argument: no new scientific axiom is
introduced here.

The source coordinates are `(A,u)`, and the literal triangular map is

`(A,u) |-> [A, (I-AA*)^(1/2)u]`.

The generic transport theorem below packages the product-density and
change-of-variables bookkeeping.  Its Jiang specialization says that an
`N`-column density theorem and an exact joint-law representation imply the
`N+1`-column density theorem once the (purely geometric) base-volume
Jacobian and pointwise density balance have been supplied.
-/

open MeasureTheory Matrix Filter
open scoped ENNReal BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

open LocalAnticoncentration

local instance h19HaarCornerInductionMatrixBorelSpace (K N : ℕ) :
    BorelSpace (Matrix (Fin K) (Fin N) ℂ) := by
  exact inferInstanceAs (BorelSpace (Fin K → Fin N → ℂ))

/-! ## Literal successor-column coordinates -/

/-- Append the column `(I-AA*)^(1/2)u`, and identify
`Fin N + Fin 1` with `Fin (N+1)`. -/
def haarCornerAppendSqrtColumn {K N : ℕ}
    (z : Matrix (Fin K) (Fin N) ℂ × (Fin K → ℂ)) :
    Matrix (Fin K) (Fin (N + 1)) ℂ :=
  Matrix.reindex (Equiv.refl (Fin K))
      (finSumFinEquiv : Fin N ⊕ Fin 1 ≃ Fin (N + 1))
    (Matrix.fromCols z.1
      (haarCornerDefectSqrt z.1 * complexColumnMatrix z.2))

@[simp]
theorem haarCornerAppendSqrtColumn_castSucc
    {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℂ)
    (u : Fin K → ℂ) (i : Fin K) (j : Fin N) :
    haarCornerAppendSqrtColumn (A, u) i j.castSucc = A i j := by
  simp [haarCornerAppendSqrtColumn, Matrix.reindex_apply]

@[simp]
theorem haarCornerAppendSqrtColumn_last
    {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℂ)
    (u : Fin K → ℂ) (i : Fin K) :
    haarCornerAppendSqrtColumn (A, u) i (Fin.last N) =
      (haarCornerDefectSqrt A *ᵥ u) i := by
  simp [haarCornerAppendSqrtColumn, Matrix.reindex_apply,
    Matrix.mul_apply, complexColumnMatrix]
  rfl

/-! ## The plain append-column volume coordinates -/

/-- Append one scalar to a row, placing it at `Fin.last N`.  This is the
literal coordinate permutation used to identify a matrix/column product
with an `(N+1)`-column matrix. -/
def haarCornerRowAppendMeasurableEquiv (N : ℕ) :
    ((Fin N → ℂ) × ℂ) ≃ᵐ (Fin (N + 1) → ℂ) :=
  MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (N + 1) ↦ ℂ) (Fin.last N)).symm

/-- Rowwise append gives a measurable equivalence between a rectangular
matrix together with one column and the successor rectangular matrix. -/
def haarCornerAppendColumnMeasurableEquiv (K N : ℕ) :
    (Matrix (Fin K) (Fin N) ℂ × (Fin K → ℂ)) ≃ᵐ
      Matrix (Fin K) (Fin (N + 1)) ℂ :=
  (MeasurableEquiv.arrowProdEquivProdArrow
      (Fin N → ℂ) ℂ (Fin K)).symm.trans
    (MeasurableEquiv.piCongrRight
      (fun _ : Fin K ↦ haarCornerRowAppendMeasurableEquiv N))

@[simp]
theorem haarCornerAppendColumnMeasurableEquiv_castSucc
    {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℂ)
    (x : Fin K → ℂ) (i : Fin K) (j : Fin N) :
    haarCornerAppendColumnMeasurableEquiv K N (A, x) i j.castSucc =
      A i j := by
  change ((MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (N + 1) ↦ ℂ) (Fin.last N)).symm
      (x i, A i)) j.castSucc = A i j
  simp

@[simp]
theorem haarCornerAppendColumnMeasurableEquiv_last
    {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℂ)
    (x : Fin K → ℂ) (i : Fin K) :
    haarCornerAppendColumnMeasurableEquiv K N (A, x) i (Fin.last N) =
      x i := by
  change ((MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (N + 1) ↦ ℂ) (Fin.last N)).symm
      (x i, A i)) (Fin.last N) = x i
  simp

/-- The triangular append map is the plain append equivalence after applying
the defect square root in the last fiber. -/
theorem haarCornerAppendSqrtColumn_eq_appendColumnEquiv
    {K N : ℕ} :
    haarCornerAppendSqrtColumn =
      fun z : Matrix (Fin K) (Fin N) ℂ × (Fin K → ℂ) ↦
        haarCornerAppendColumnMeasurableEquiv K N
          (z.1, haarCornerDefectSqrt z.1 *ᵥ z.2) := by
  funext z
  rcases z with ⟨A, u⟩
  ext i j
  refine Fin.lastCases ?_ (fun q ↦ ?_) j
  · rw [haarCornerAppendSqrtColumn_last,
      haarCornerAppendColumnMeasurableEquiv_last]
  · rw [haarCornerAppendSqrtColumn_castSucc,
      haarCornerAppendColumnMeasurableEquiv_castSucc]

/-- Appending one scalar to a row preserves the coordinatewise complex
Lebesgue volume. -/
theorem measurePreserving_haarCornerRowAppendMeasurableEquiv (N : ℕ) :
    MeasurePreserving (haarCornerRowAppendMeasurableEquiv N)
      ((Measure.pi fun _ : Fin N ↦ (volume : Measure ℂ)).prod
        (volume : Measure ℂ))
      (Measure.pi fun _ : Fin (N + 1) ↦ (volume : Measure ℂ)) := by
  have hswap : MeasurePreserving
      (MeasurableEquiv.prodComm : ((Fin N → ℂ) × ℂ) ≃ᵐ
        (ℂ × (Fin N → ℂ)))
      ((Measure.pi fun _ : Fin N ↦ (volume : Measure ℂ)).prod
        (volume : Measure ℂ))
      ((volume : Measure ℂ).prod
        (Measure.pi fun _ : Fin N ↦ (volume : Measure ℂ))) := by
    change MeasurePreserving Prod.swap
      ((Measure.pi fun _ : Fin N ↦ (volume : Measure ℂ)).prod
        (volume : Measure ℂ))
      ((volume : Measure ℂ).prod
        (Measure.pi fun _ : Fin N ↦ (volume : Measure ℂ)))
    exact Measure.measurePreserving_swap
  have hins : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (N + 1) ↦ ℂ) (Fin.last N)).symm
      ((volume : Measure ℂ).prod
        (Measure.pi fun _ : Fin N ↦ (volume : Measure ℂ)))
      (Measure.pi fun _ : Fin (N + 1) ↦ (volume : Measure ℂ)) := by
    simpa using
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (N + 1) ↦ (volume : Measure ℂ)) (Fin.last N)).symm
  exact hins.comp hswap

/-- The matrix/last-column coordinate equivalence preserves rectangular
complex Lebesgue volume exactly. -/
theorem measurePreserving_haarCornerAppendColumnMeasurableEquiv
    (K N : ℕ) :
    MeasurePreserving (haarCornerAppendColumnMeasurableEquiv K N)
      ((complexRectangularLebesgueVolume K N).prod
        (complexColumnLebesgueVolume K))
      (complexRectangularLebesgueVolume K (N + 1)) := by
  have hpair : MeasurePreserving
      (MeasurableEquiv.arrowProdEquivProdArrow
        (Fin N → ℂ) ℂ (Fin K)).symm
      ((Measure.pi fun _ : Fin K ↦
          Measure.pi fun _ : Fin N ↦ (volume : Measure ℂ)).prod
        (Measure.pi fun _ : Fin K ↦ (volume : Measure ℂ)))
      (Measure.pi fun _ : Fin K ↦
        (Measure.pi fun _ : Fin N ↦ (volume : Measure ℂ)).prod
          (volume : Measure ℂ)) := by
    simpa using
      (measurePreserving_arrowProdEquivProdArrow
        (Fin N → ℂ) ℂ (Fin K)
        (fun _ : Fin K ↦
          Measure.pi fun _ : Fin N ↦ (volume : Measure ℂ))
        (fun _ : Fin K ↦ (volume : Measure ℂ))).symm
  have hrows : MeasurePreserving
      (fun z : Fin K → ((Fin N → ℂ) × ℂ) ↦
        fun i ↦ haarCornerRowAppendMeasurableEquiv N (z i)) :=
    measurePreserving_pi
      (fun _ : Fin K ↦
        (Measure.pi fun _ : Fin N ↦ (volume : Measure ℂ)).prod
          (volume : Measure ℂ))
      (fun _ : Fin K ↦
        Measure.pi fun _ : Fin (N + 1) ↦ (volume : Measure ℂ))
      (fun _ : Fin K ↦
        measurePreserving_haarCornerRowAppendMeasurableEquiv N)
  change MeasurePreserving (haarCornerAppendColumnMeasurableEquiv K N)
      ((Measure.pi fun _ : Fin K ↦
          Measure.pi fun _ : Fin N ↦ (volume : Measure ℂ)).prod
        (Measure.pi fun _ : Fin K ↦ (volume : Measure ℂ)))
      (Measure.pi fun _ : Fin K ↦
        Measure.pi fun _ : Fin (N + 1) ↦ (volume : Measure ℂ))
  exact hrows.comp hpair

theorem map_haarCornerAppendColumnMeasurableEquiv_volume
    (K N : ℕ) :
    Measure.map (haarCornerAppendColumnMeasurableEquiv K N)
        ((complexRectangularLebesgueVolume K N).prod
          (complexColumnLebesgueVolume K)) =
      complexRectangularLebesgueVolume K (N + 1) := by
  exact (measurePreserving_haarCornerAppendColumnMeasurableEquiv K N).map_eq

/-! ## A measurable version of the almost-everywhere positive square root -/

/-- On the old Jiang density, the defect square root is almost-everywhere
measurable.  The only points used by the density have positive definite
defect; continuity of CFC square root on the nonnegative cone therefore
suffices. -/
theorem aemeasurable_haarCornerDefectSqrt_under_jiangDensity
    {M K N : ℕ} (hsize : K + (N + 1) ≤ M) :
    AEMeasurable (@haarCornerDefectSqrt K N)
      ((complexRectangularLebesgueVolume K N).withDensity
        (jiangUnscaledTallHaarCornerPDF M K N)) := by
  let mu := (complexRectangularLebesgueVolume K N).withDensity
    (jiangUnscaledTallHaarCornerPDF M K N)
  let s : Set (Matrix (Fin K) (Fin N) ℂ) :=
    {A | (haarCornerLeftDefect A).PosSemidef}
  have hs : MeasurableSet s := by
    have heq : s = {A | jiangUnscaledTallHaarCornerSupport A} := by
      ext A
      exact ((jiangUnscaledTallHaarCornerSupport_iff_posSemidef A).trans
        (posSemidef_one_sub_conjTranspose_mul_iff_one_sub_mul_conjTranspose A)).symm
    rw [heq]
    exact (isClosed_jiangUnscaledTallHaarCornerSupport K N).measurableSet
  have hc : ContinuousOn (@haarCornerDefectSqrt K N) s := by
    have hd : Continuous
        (haarCornerLeftDefect : Matrix (Fin K) (Fin N) ℂ →
          Matrix (Fin K) (Fin K) ℂ) := by
      unfold haarCornerLeftDefect
      fun_prop
    have hsqrt : ContinuousOn
        (CFC.sqrt : Matrix (Fin K) (Fin K) ℂ →
          Matrix (Fin K) (Fin K) ℂ)
        {D | 0 ≤ D} :=
      CFC.continuousOn_sqrt (A := Matrix (Fin K) (Fin K) ℂ)
    exact hsqrt.comp hd.continuousOn (fun A hA ↦ hA.nonneg)
  have hmem : ∀ᵐ A ∂mu, A ∈ s := by
    dsimp only [mu]
    filter_upwards [ae_haarCornerLeftDefect_posDef_under_jiangDensity hsize]
      with A hA
    exact hA.posSemidef
  have hr : mu.restrict s = mu :=
    Measure.restrict_eq_self_of_ae_mem hmem
  have hm : AEMeasurable (@haarCornerDefectSqrt K N) (mu.restrict s) :=
    hc.aemeasurable hs
  rwa [hr] at hm

/-- A globally measurable representative of the defect square root, equal
to the canonical CFC square root almost everywhere under the old density. -/
def measurableHaarCornerDefectSqrt
    {M K N : ℕ} (hsize : K + (N + 1) ≤ M) :
    Matrix (Fin K) (Fin N) ℂ → Matrix (Fin K) (Fin K) ℂ :=
  AEMeasurable.mk _
    (aemeasurable_haarCornerDefectSqrt_under_jiangDensity hsize)

theorem measurable_measurableHaarCornerDefectSqrt
    {M K N : ℕ} (hsize : K + (N + 1) ≤ M) :
    Measurable (@measurableHaarCornerDefectSqrt M K N hsize) :=
  (aemeasurable_haarCornerDefectSqrt_under_jiangDensity hsize).measurable_mk

theorem ae_haarCornerDefectSqrt_eq_measurableVersion
    {M K N : ℕ} (hsize : K + (N + 1) ≤ M) :
    haarCornerDefectSqrt =ᵐ[
      (complexRectangularLebesgueVolume K N).withDensity
        (jiangUnscaledTallHaarCornerPDF M K N)]
      measurableHaarCornerDefectSqrt hsize :=
  (aemeasurable_haarCornerDefectSqrt_under_jiangDensity hsize).ae_eq_mk

/-- The measurable triangular fiber map used in the Fubini argument. -/
def measurableHaarCornerFiberMap
    {M K N : ℕ} (hsize : K + (N + 1) ≤ M)
    (A : Matrix (Fin K) (Fin N) ℂ) (u : Fin K → ℂ) : Fin K → ℂ :=
  measurableHaarCornerDefectSqrt hsize A *ᵥ u

theorem measurable_measurableHaarCornerFiberMap
    {M K N : ℕ} (hsize : K + (N + 1) ≤ M) :
    Measurable (fun z : Matrix (Fin K) (Fin N) ℂ × (Fin K → ℂ) ↦
      measurableHaarCornerFiberMap hsize z.1 z.2) := by
  refine measurable_pi_lambda _ fun i ↦ ?_
  unfold measurableHaarCornerFiberMap Matrix.mulVec dotProduct
  refine Finset.measurable_sum _ fun j _ ↦ ?_
  exact ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp
        ((measurable_measurableHaarCornerDefectSqrt hsize).comp measurable_fst))).mul
    ((measurable_pi_apply j).comp measurable_snd)

/-- Reindexing the columns of a rectangular matrix only reindexes its
column Gram matrix, and hence does not change the Gram determinant. -/
theorem det_one_sub_reindexColumns_conjTranspose_mul
    {m n n' : Type*} [Fintype m] [Fintype n] [Fintype n']
    [DecidableEq m] [DecidableEq n] [DecidableEq n']
    (e : n ≃ n') (C : Matrix m n ℂ) :
    Matrix.det
        (1 -
          (Matrix.reindex (Equiv.refl m) e C).conjTranspose *
            Matrix.reindex (Equiv.refl m) e C) =
      Matrix.det (1 - C.conjTranspose * C) := by
  have hgram :
      (Matrix.reindex (Equiv.refl m) e C).conjTranspose *
          Matrix.reindex (Equiv.refl m) e C =
        Matrix.reindex e e (C.conjTranspose * C) := by
    rw [Matrix.conjTranspose_reindex]
    simpa using
      (Matrix.reindexLinearEquiv_mul (R := ℂ) (A := ℂ)
        e (Equiv.refl m) e C.conjTranspose C)
  rw [hgram]
  have hsub :
      (1 : Matrix n' n' ℂ) - Matrix.reindex e e (C.conjTranspose * C) =
        Matrix.reindex e e (1 - C.conjTranspose * C) := by
    ext i j
    simp [Matrix.reindex_apply, Matrix.one_apply]
  rw [hsub, Matrix.det_reindex_self]

/-- Determinant separation for the literal `Fin (N+1)` successor map. -/
theorem det_one_sub_haarCornerAppendSqrtColumn_eq
    {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℂ)
    (hA : (haarCornerLeftDefect A).PosDef)
    (u : Fin K → ℂ) :
    Matrix.det
        (1 - (haarCornerAppendSqrtColumn (A, u)).conjTranspose *
          haarCornerAppendSqrtColumn (A, u)) =
      Matrix.det (haarCornerLeftDefect A) *
        ((1 - complexColumnNormSq u : ℝ) : ℂ) := by
  rw [haarCornerAppendSqrtColumn]
  rw [det_one_sub_reindexColumns_conjTranspose_mul]
  exact det_one_sub_appended_sqrtColumn_eq_defect_mul_one_sub_normSq
    A hA u

/-! ## The one-column beta density -/

/-- The extra factor in Jiang's normalizer when one passes from `N` to
`N+1` columns. -/
def jiangHaarCornerSuccFiberNormalizer (M K N : ℕ) : ℝ :=
  (Real.pi ^ K)⁻¹ *
    (((Nat.factorial (M - (N + 1)) : ℕ) : ℝ) /
      ((Nat.factorial (M - (N + 1) - K) : ℕ) : ℝ))

/-- The complex unit-ball density of the independent successor coordinate.
Its exponent is the new Jiang exponent. -/
def jiangHaarCornerSuccFiberPDF (M K N : ℕ)
    (u : Fin K → ℂ) : ℝ≥0∞ :=
  if complexColumnNormSq u ≤ 1 then
    ENNReal.ofReal
      (jiangHaarCornerSuccFiberNormalizer M K N *
        (1 - complexColumnNormSq u) ^ (M - K - (N + 1)))
  else 0

theorem measurable_complexColumnNormSq (K : ℕ) :
    Measurable (@complexColumnNormSq K) := by
  unfold complexColumnNormSq
  fun_prop

theorem measurable_jiangHaarCornerSuccFiberPDF
    (M K N : ℕ) :
    Measurable (jiangHaarCornerSuccFiberPDF M K N) := by
  unfold jiangHaarCornerSuccFiberPDF
  apply Measurable.ite
  · have hnorm : Continuous
        (fun u : Fin K → ℂ ↦ complexColumnNormSq u) := by
      unfold complexColumnNormSq
      fun_prop
    exact (isClosed_le hnorm continuous_const).measurableSet
  · exact (measurable_const.mul
      ((measurable_const.sub (measurable_complexColumnNormSq K)).pow_const _)).ennreal_ofReal
  · exact measurable_const

/-- The source product density in independent `(A,u)` coordinates. -/
def jiangHaarCornerSuccSourcePDF (M K N : ℕ)
    (z : Matrix (Fin K) (Fin N) ℂ × (Fin K → ℂ)) : ℝ≥0∞ :=
  jiangUnscaledTallHaarCornerPDF M K N z.1 *
    jiangHaarCornerSuccFiberPDF M K N z.2

theorem measurable_jiangHaarCornerSuccSourcePDF
    (M K N : ℕ) :
    Measurable (jiangHaarCornerSuccSourcePDF M K N) := by
  exact
    ((measurable_jiangUnscaledTallHaarCornerPDF M K N).comp measurable_fst).mul
      ((measurable_jiangHaarCornerSuccFiberPDF M K N).comp measurable_snd)

/-! ## Scalar cancellation behind the density step -/

/-- The old determinant power, the unit-ball power, and the real Jacobian
combine into the new determinant power.  This is the exact scalar identity
used after the determinant factorization. -/
theorem jiang_succ_normalizer_det_power_balance
    {M K N : ℕ} (hsize : K + (N + 1) ≤ M)
    (d q : ℝ) :
    (jiangUnscaledTallHaarCornerNormalizer M K N *
        d ^ (M - K - N)) *
      (jiangHaarCornerSuccFiberNormalizer M K N *
        q ^ (M - K - (N + 1))) =
      d *
        (jiangUnscaledTallHaarCornerNormalizer M K (N + 1) *
          (d * q) ^ (M - K - (N + 1))) := by
  rw [jiangUnscaledTallHaarCornerNormalizer_succ_column]
  unfold jiangHaarCornerSuccFiberNormalizer
  let c : ℝ :=
    (Real.pi ^ K)⁻¹ *
      (((Nat.factorial (M - (N + 1)) : ℕ) : ℝ) /
        ((Nat.factorial (M - (N + 1) - K) : ℕ) : ℝ))
  have hpow := jacobian_mul_detFactor_pow_succColumn hsize d q
  calc
    (jiangUnscaledTallHaarCornerNormalizer M K N *
          d ^ (M - K - N)) *
        (c * q ^ (M - K - (N + 1))) =
      (jiangUnscaledTallHaarCornerNormalizer M K N * c) *
        (d ^ (M - K - N) * q ^ (M - K - (N + 1))) := by ring
    _ =
      (jiangUnscaledTallHaarCornerNormalizer M K N * c) *
        (d * (d * q) ^ (M - K - (N + 1))) := by rw [hpow]
    _ =
      d *
        ((jiangUnscaledTallHaarCornerNormalizer M K N * c) *
          (d * q) ^ (M - K - (N + 1))) := by ring
    _ =
      d *
        (jiangUnscaledTallHaarCornerNormalizer M K N *
            (Real.pi ^ K)⁻¹ *
            (((Nat.factorial (M - (N + 1)) : ℕ) : ℝ) /
              ((Nat.factorial (M - (N + 1) - K) : ℕ) : ℝ)) *
          (d * q) ^ (M - K - (N + 1))) := by
            simp only [c]
            ring

/-! ## A generic product-density transport lemma -/

/-- Product densities transported through a measurable equivalence.  The
factor `j` is the density of the pushed-forward base measure; `hbalance` is
exactly the Jacobian cancellation with the transported source density. -/
theorem map_prod_withDensity_of_measurableEquiv
    {alpha beta gamma : Type*}
    [MeasurableSpace alpha] [MeasurableSpace beta] [MeasurableSpace gamma]
    (mu : Measure alpha) (nu : Measure beta) (omega : Measure gamma)
    [SFinite mu] [SFinite nu]
    (e : (alpha × beta) ≃ᵐ gamma)
    (f : alpha → ℝ≥0∞) (g : beta → ℝ≥0∞)
    (j h : gamma → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hj : Measurable j)
    (hbase : Measure.map e (mu.prod nu) = omega.withDensity j)
    (hbalance : ∀ y,
      j y * (f (e.symm y).1 * g (e.symm y).2) = h y) :
    Measure.map e ((mu.withDensity f).prod (nu.withDensity g)) =
      omega.withDensity h := by
  have hf' : Measurable (fun z : alpha × beta ↦ f z.1) :=
    hf.comp measurable_fst
  have hg' : Measurable (fun z : alpha × beta ↦ g z.2) :=
    hg.comp measurable_snd
  have hfg : Measurable (fun z : alpha × beta ↦ f z.1 * g z.2) :=
    hf'.mul hg'
  rw [prod_withDensity hf hg]
  rw [LogdetLean.GramHafnian.map_measurableEquiv_withDensity_localAnticoncentration
    e (mu.prod nu) (fun z : alpha × beta ↦ f z.1 * g z.2) hfg]
  rw [hbase]
  let q : gamma → ℝ≥0∞ :=
    (fun z : alpha × beta ↦ f z.1 * g z.2) ∘ e.symm
  have hq : Measurable q := hfg.comp e.symm.measurable
  change (omega.withDensity j).withDensity q = omega.withDensity h
  calc
    (omega.withDensity j).withDensity q =
        omega.withDensity (j * q) := (withDensity_mul omega hj hq).symm
    _ = omega.withDensity h := by
      congr 1
      funext y
      exact hbalance y

/-! ## Jiang `N -> N+1` induction adapter -/

/-- Abstract, but fully kernel-checked, measure-theoretic successor step.

`hrepresentation` is the exact probabilistic input: it says that the
`N+1`-column Haar corner is obtained by appending
`(I-AA*)^(1/2)u` to the `N`-column corner.  It is an ordinary theorem
argument, not an axiom.  The measurable equivalence `e` may differ from the
literal triangular map only on a null set of the represented source law;
this permits a harmless extension across the singular boundary.

`hbase` is the base-volume change of variables and `hbalance` is the
pointwise Jacobian/density identity.  The preceding algebraic lemmas provide
their determinant, exponent, and normalizer components. -/
theorem jiangUnscaledTallHaarCorner_density_succ_of_appendSqrt_representation
    {M K N : ℕ}
    (e :
      (Matrix (Fin K) (Fin N) ℂ × (Fin K → ℂ)) ≃ᵐ
        Matrix (Fin K) (Fin (N + 1)) ℂ)
    (j : Matrix (Fin K) (Fin (N + 1)) ℂ → ℝ≥0∞)
    (hj : Measurable j)
    (hbase :
      Measure.map e
          ((complexRectangularLebesgueVolume K N).prod
            (complexColumnLebesgueVolume K)) =
        (complexRectangularLebesgueVolume K (N + 1)).withDensity j)
    (hbalance : ∀ Y,
      j Y *
          jiangHaarCornerSuccSourcePDF M K N (e.symm Y) =
        jiangUnscaledTallHaarCornerPDF M K (N + 1) Y)
    (hprev :
      jiangUnscaledTallHaarCornerLaw M K N =
        (complexRectangularLebesgueVolume K N).withDensity
          (jiangUnscaledTallHaarCornerPDF M K N))
    (hrepresentation :
      jiangUnscaledTallHaarCornerLaw M K (N + 1) =
        Measure.map haarCornerAppendSqrtColumn
          ((jiangUnscaledTallHaarCornerLaw M K N).prod
            ((complexColumnLebesgueVolume K).withDensity
              (jiangHaarCornerSuccFiberPDF M K N))))
    (he :
      haarCornerAppendSqrtColumn =ᵐ[
        (jiangUnscaledTallHaarCornerLaw M K N).prod
          ((complexColumnLebesgueVolume K).withDensity
            (jiangHaarCornerSuccFiberPDF M K N))] e) :
    jiangUnscaledTallHaarCornerLaw M K (N + 1) =
      (complexRectangularLebesgueVolume K (N + 1)).withDensity
        (jiangUnscaledTallHaarCornerPDF M K (N + 1)) := by
  rw [hrepresentation, Measure.map_congr he, hprev]
  exact map_prod_withDensity_of_measurableEquiv
    (complexRectangularLebesgueVolume K N)
    (complexColumnLebesgueVolume K)
    (complexRectangularLebesgueVolume K (N + 1))
    e
    (jiangUnscaledTallHaarCornerPDF M K N)
    (jiangHaarCornerSuccFiberPDF M K N)
    j
    (jiangUnscaledTallHaarCornerPDF M K (N + 1))
    (measurable_jiangUnscaledTallHaarCornerPDF M K N)
    (measurable_jiangHaarCornerSuccFiberPDF M K N)
    hj hbase (by
      intro Y
      simpa [jiangHaarCornerSuccSourcePDF] using hbalance Y)

#print axioms jiang_succ_normalizer_det_power_balance
#print axioms map_prod_withDensity_of_measurableEquiv
#print axioms jiangUnscaledTallHaarCorner_density_succ_of_appendSqrt_representation

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse

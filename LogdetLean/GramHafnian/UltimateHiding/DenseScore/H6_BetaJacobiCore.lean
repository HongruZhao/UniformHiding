import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_CoordinateAlgebra
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_RadialMeasureAdapters
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Axiom-free beta-Jacobi core

This module contains only the measure definitions, coordinate maps, elementary
contracts, collision set, and permutation-invariant power-sum tests shared by
the H6 A2' and A3 routes.  It declares no scientific axiom and contains no
COE ensemble law or H6 endpoint.
-/

open scoped BigOperators ENNReal ComplexConjugate
open Set MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open H6CoordinateAlgebra H6RadialMeasureAdapters

/-! ## Literal normalized density measures -/

/-- The paper's open coordinate cube. -/
abbrev betaJacobiOpenCube (n : ℕ) : Set (Fin n → ℝ) :=
  openUnitCube n

/-- Unordered pairs, represented once by `i < j`. -/
def a2StrictPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ ×ˢ Finset.univ).filter fun p ↦ p.1 < p.2

/-- The beta-Jacobi kernel in the literal variables `n,a,b,beta,lambda_i`. -/
def betaJacobiKernel (n : ℕ) (a b beta : ℝ)
    (lambda_i : Fin n → ℝ) : ℝ≥0∞ :=
  (∏ i,
      (ENNReal.ofReal (lambda_i i)).rpow
          (beta * (a + 1) / 2 - 1) *
      (ENNReal.ofReal (1 - lambda_i i)).rpow
          (beta * (b + 1) / 2 - 1)) *
    ∏ p ∈ a2StrictPairs n,
      (ENNReal.ofReal |lambda_i p.2 - lambda_i p.1|).rpow beta

/-- The beta-Jacobi raw measure. -/
def betaJacobiRawMeasure (n : ℕ) (a b beta : ℝ) :
    Measure (Fin n → ℝ) :=
  (volume.restrict (betaJacobiOpenCube n)).withDensity
    (betaJacobiKernel n a b beta)

/-- Beta-Jacobi normalization, defined by the displayed integral. -/
def betaJacobiNormalization (n : ℕ) (a b beta : ℝ) : ℝ≥0∞ :=
  betaJacobiRawMeasure n a b beta Set.univ

/-- Totalized normalized beta-Jacobi measure. -/
def betaJacobiProbabilityMeasure (n : ℕ) (a b beta : ℝ) :
    Measure (Fin n → ℝ) :=
  normalizeMeasure (betaJacobiRawMeasure n a b beta)

/-- Forrester equation-(1.7) kernel, with unsquared `lambda_i`. -/
def forresterEq17Kernel (m : ℕ) (beta alpha : ℝ)
    (lambda_i : Fin m → ℝ) : ℝ≥0∞ :=
  (∏ i, (ENNReal.ofReal (lambda_i i)).rpow (beta * alpha)) *
    ∏ p ∈ a2StrictPairs m,
      (ENNReal.ofReal
        |(lambda_i p.2) ^ 2 - (lambda_i p.1) ^ 2|).rpow beta

/-- The raw equation-(1.7) measure. -/
def forresterEq17RawMeasure (m : ℕ) (beta alpha : ℝ) :
    Measure (Fin m → ℝ) :=
  (volume.restrict (betaJacobiOpenCube m)).withDensity
    (forresterEq17Kernel m beta alpha)

/-- Equation-(1.7) normalization, defined by the displayed integral. -/
def forresterEq17Normalization (m : ℕ) (beta alpha : ℝ) : ℝ≥0∞ :=
  forresterEq17RawMeasure m beta alpha Set.univ

/-- Totalized normalized equation-(1.7) measure. -/
def forresterEq17ProbabilityMeasure (m : ℕ) (beta alpha : ℝ) :
    Measure (Fin m → ℝ) :=
  normalizeMeasure (forresterEq17RawMeasure m beta alpha)

/-! ## Explicit square and reflection maps -/

/-- Coordinatewise squaring of the paper's unsquared singular values. -/
def a2CoordinateSquare (m : ℕ) : (Fin m → ℝ) → (Fin m → ℝ) :=
  fun lambda_i i ↦ (lambda_i i) ^ 2

/-- Coordinatewise reflection `u_i ↦ 1-u_i`. -/
def a2CoordinateReflection (m : ℕ) :
    (Fin m → ℝ) → (Fin m → ℝ) :=
  fun u i ↦ 1 - u i

theorem measurable_a2CoordinateSquare (m : ℕ) :
    Measurable (a2CoordinateSquare m) := by
  unfold a2CoordinateSquare
  fun_prop

theorem measurable_a2CoordinateReflection (m : ℕ) :
    Measurable (a2CoordinateReflection m) := by
  unfold a2CoordinateReflection
  fun_prop

theorem a2CoordinateReflection_involutive (m : ℕ) :
    Function.Involutive (a2CoordinateReflection m) := by
  intro u
  funext i
  simp [a2CoordinateReflection]

theorem a2CoordinateReflection_mem_openCube_iff
    {m : ℕ} {u : Fin m → ℝ} :
    a2CoordinateReflection m u ∈ betaJacobiOpenCube m ↔
      u ∈ betaJacobiOpenCube m := by
  simp only [betaJacobiOpenCube, openUnitCube, mem_ofPred_eq, mem_Ioo,
    a2CoordinateReflection]
  constructor <;> intro h i
  · constructor <;> linarith [(h i).1, (h i).2]
  · constructor <;> linarith [(h i).1, (h i).2]

/-- The exact scalar `2^(-m)` from `u_i=lambda_i^2`. -/
def a2SquaringScale (m : ℕ) : NNReal := ((2 : NNReal) ^ m)⁻¹

theorem a2SquaringScale_ne_zero (m : ℕ) : a2SquaringScale m ≠ 0 := by
  simp [a2SquaringScale]

/-- The beta-Jacobi `a` parameter after squaring equation (1.7). -/
def a2JacobiA (beta alpha : ℝ) : ℝ := alpha + beta⁻¹ - 1

/-- The beta-Jacobi `b` parameter after squaring equation (1.7). -/
def a2JacobiB (beta : ℝ) : ℝ := 2 / beta - 1

/-! ## Independent raw contracts and proved normalization cancellation -/

/-- **CONDITIONAL elementary contract.**  This is only the raw square-chart
Jacobian identity; it contains no matrix law, A2 assertion, H5, or H6. -/
structure ForresterEq17RawSquaringContract
    (m : ℕ) (beta alpha : ℝ) : Prop where
  raw_square :
    Measure.map (a2CoordinateSquare m)
        (forresterEq17RawMeasure m beta alpha) =
      (a2SquaringScale m : ℝ≥0∞) •
        betaJacobiRawMeasure m (a2JacobiA beta alpha)
          (a2JacobiB beta) beta

/-- **CONDITIONAL elementary contract.**  Reflection swaps `a,b` in the raw
beta-Jacobi law.  It is independent of Forrester's source ensemble. -/
structure BetaJacobiRawReflectionContract
    (m : ℕ) (a b beta : ℝ) : Prop where
  raw_reflection :
    Measure.map (a2CoordinateReflection m)
        (betaJacobiRawMeasure m a b beta) =
      betaJacobiRawMeasure m b a beta

/-- Total mass bookkeeping for a measurable pushforward known up to a finite
nonzero `NNReal` scalar. -/
theorem totalMass_eq_of_map_eq_nnreal_smul
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (f : α → β) (c : NNReal)
    (hf : Measurable f)
    (hmap : Measure.map f μ = (c : ℝ≥0∞) • ν) :
    μ Set.univ = (c : ℝ≥0∞) * ν Set.univ := by
  calc
    μ Set.univ = Measure.map f μ Set.univ := by
      rw [Measure.map_apply hf MeasurableSet.univ]
      simp
    _ = ((c : ℝ≥0∞) • ν) Set.univ :=
      congrArg (fun ξ : Measure β ↦ ξ Set.univ) hmap
    _ = (c : ℝ≥0∞) * ν Set.univ := by
      rw [Measure.smul_apply]
      rfl

theorem ForresterEq17RawSquaringContract.normalization_square
    {m : ℕ} {beta alpha : ℝ}
    (h : ForresterEq17RawSquaringContract m beta alpha) :
    forresterEq17Normalization m beta alpha =
      (a2SquaringScale m : ℝ≥0∞) *
        betaJacobiNormalization m (a2JacobiA beta alpha)
          (a2JacobiB beta) beta := by
  exact totalMass_eq_of_map_eq_nnreal_smul
    (forresterEq17RawMeasure m beta alpha)
    (betaJacobiRawMeasure m (a2JacobiA beta alpha)
      (a2JacobiB beta) beta)
    (a2CoordinateSquare m) (a2SquaringScale m)
    (measurable_a2CoordinateSquare m) h.raw_square

/-- The raw `2^(-m)` factor cancels after normalization. -/
theorem ForresterEq17RawSquaringContract.probability_square
    {m : ℕ} {beta alpha : ℝ}
    (h : ForresterEq17RawSquaringContract m beta alpha) :
    Measure.map (a2CoordinateSquare m)
        (forresterEq17ProbabilityMeasure m beta alpha) =
      betaJacobiProbabilityMeasure m (a2JacobiA beta alpha)
        (a2JacobiB beta) beta := by
  exact map_normalizeMeasure_of_map_eq_nnreal_smul
    (forresterEq17RawMeasure m beta alpha)
    (betaJacobiRawMeasure m (a2JacobiA beta alpha)
      (a2JacobiB beta) beta)
    (a2CoordinateSquare m) (a2SquaringScale m)
    (measurable_a2CoordinateSquare m) (a2SquaringScale_ne_zero m)
    h.raw_square

theorem BetaJacobiRawReflectionContract.normalization_reflection
    {m : ℕ} {a b beta : ℝ}
    (h : BetaJacobiRawReflectionContract m a b beta) :
    betaJacobiNormalization m a b beta =
      betaJacobiNormalization m b a beta := by
  have hmap : Measure.map (a2CoordinateReflection m)
      (betaJacobiRawMeasure m a b beta) =
        ((1 : NNReal) : ℝ≥0∞) •
          betaJacobiRawMeasure m b a beta := by
    simpa using h.raw_reflection
  simpa [betaJacobiNormalization] using totalMass_eq_of_map_eq_nnreal_smul
    (betaJacobiRawMeasure m a b beta)
    (betaJacobiRawMeasure m b a beta)
    (a2CoordinateReflection m) (1 : NNReal)
    (measurable_a2CoordinateReflection m) hmap

/-- Reflection swaps the normalized beta-Jacobi parameters without any
axiomatized normalizing constant. -/
theorem BetaJacobiRawReflectionContract.probability_reflection
    {m : ℕ} {a b beta : ℝ}
    (h : BetaJacobiRawReflectionContract m a b beta) :
    Measure.map (a2CoordinateReflection m)
        (betaJacobiProbabilityMeasure m a b beta) =
      betaJacobiProbabilityMeasure m b a beta := by
  apply map_normalizeMeasure_of_map_eq_nnreal_smul
    (betaJacobiRawMeasure m a b beta)
    (betaJacobiRawMeasure m b a beta)
    (a2CoordinateReflection m) (1 : NNReal)
    (measurable_a2CoordinateReflection m) one_ne_zero
  simpa using h.raw_reflection

/-! ## Collision-nullity as a separate obligation -/

def betaJacobiCollisionSet (n : ℕ) : Set (Fin n → ℝ) :=
  {lambda_i | ∃ i j, i ≠ j ∧ lambda_i i = lambda_i j}

/-- **CONDITIONAL foundational contract.**  The sole field is the Lebesgue
nullity of the finite union of coordinate hyperplanes. -/
structure BetaJacobiCollisionVolumeContract (n : ℕ) : Prop where
  volume_collision : volume (betaJacobiCollisionSet n) = 0

theorem BetaJacobiCollisionVolumeContract.betaJacobi_collision_null
    {n : ℕ} (h : BetaJacobiCollisionVolumeContract n)
    (a b beta : ℝ) :
    betaJacobiProbabilityMeasure n a b beta
        (betaJacobiCollisionSet n) = 0 := by
  have hbase : (volume.restrict (betaJacobiOpenCube n))
      (betaJacobiCollisionSet n) = 0 :=
    Measure.absolutelyContinuous_restrict h.volume_collision
  have hraw : betaJacobiRawMeasure n a b beta
      (betaJacobiCollisionSet n) = 0 := by
    exact withDensity_absolutelyContinuous
      (volume.restrict (betaJacobiOpenCube n))
      (betaJacobiKernel n a b beta) hbase
  unfold betaJacobiProbabilityMeasure normalizeMeasure
  rw [Measure.smul_apply, hraw]
  simp

/-! ## Unordered symmetric tests -/

def a2PermuteCoordinates {n : ℕ} (sigma : Equiv.Perm (Fin n))
    (lambda_i : Fin n → ℝ) : Fin n → ℝ :=
  lambda_i ∘ sigma

def IsA2SymmetricTest {n : ℕ} {γ : Type*} (F : (Fin n → ℝ) → γ) : Prop :=
  ∀ (sigma : Equiv.Perm (Fin n)) (lambda_i : Fin n → ℝ),
    F (a2PermuteCoordinates sigma lambda_i) = F lambda_i

def a2SpectralPowerSumVector (r n : ℕ)
    (lambda_i : Fin n → ℝ) : Fin r → ℝ :=
  fun j ↦ ∑ i, (lambda_i i) ^ (j.1 + 1)

theorem measurable_a2SpectralPowerSumVector (r n : ℕ) :
    Measurable (a2SpectralPowerSumVector r n) := by
  unfold a2SpectralPowerSumVector
  fun_prop

theorem a2SpectralPowerSumVector_perm
    (r n : ℕ) (sigma : Equiv.Perm (Fin n))
    (lambda_i : Fin n → ℝ) :
    a2SpectralPowerSumVector r n
        (a2PermuteCoordinates sigma lambda_i) =
      a2SpectralPowerSumVector r n lambda_i := by
  funext j
  unfold a2SpectralPowerSumVector a2PermuteCoordinates
  exact Equiv.sum_comp sigma (fun i ↦ (lambda_i i) ^ (j.1 + 1))

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

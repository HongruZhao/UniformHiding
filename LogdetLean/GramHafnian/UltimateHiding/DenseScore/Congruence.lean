import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Map

/-!
# Exact transpose-congruence action

This file records the deterministic action used by the dense hiding draft:

`rho_g(C) = g * C * g.transpose`.

The composition order, transpose convention, exponential flow, and induced
pushforward of measures are all literal definitions.  There is no COE density,
moment estimate, or differentiability assertion in this file.
-/

open MeasureTheory NormedSpace

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-- A square complex matrix of size `N`. -/
abbrev ComplexSquareMatrix (N : ℕ) := Matrix (Fin N) (Fin N) ℂ

/-- Coordinatewise measurable structure used for the matrix-law definitions
in this self-contained branch. -/
instance denseScoreComplexSquareMatrixMeasurableSpace (N : ℕ) :
    MeasurableSpace (ComplexSquareMatrix N) := by
  unfold ComplexSquareMatrix Matrix
  infer_instance

/-- Transpose congruence, with no complex conjugation on the right factor. -/
def transposeCongruence {N : ℕ}
    (g C : ComplexSquareMatrix N) : ComplexSquareMatrix N :=
  g * C * g.transpose

@[simp]
theorem transposeCongruence_one {N : ℕ} (C : ComplexSquareMatrix N) :
    transposeCongruence 1 C = C := by
  simp [transposeCongruence]

@[simp]
theorem transposeCongruence_zero {N : ℕ} (g : ComplexSquareMatrix N) :
    transposeCongruence g 0 = 0 := by
  simp [transposeCongruence]

theorem transposeCongruence_add {N : ℕ}
    (g C D : ComplexSquareMatrix N) :
    transposeCongruence g (C + D) =
      transposeCongruence g C + transposeCongruence g D := by
  simp [transposeCongruence, Matrix.mul_add, Matrix.add_mul]

theorem transposeCongruence_smul {N : ℕ}
    (g C : ComplexSquareMatrix N) (z : ℂ) :
    transposeCongruence g (z • C) = z • transposeCongruence g C := by
  simp [transposeCongruence]

/-- Exact left-action law: `rho_(g*h) = rho_g o rho_h`. -/
theorem transposeCongruence_mul {N : ℕ}
    (g h C : ComplexSquareMatrix N) :
    transposeCongruence (g * h) C =
      transposeCongruence g (transposeCongruence h C) := by
  simp only [transposeCongruence, Matrix.transpose_mul]
  noncomm_ring

/-- Exact first/quadratic expansion around the identity.  This is a matrix
identity, not an asymptotic statement. -/
theorem transposeCongruence_one_add {N : ℕ}
    (T C : ComplexSquareMatrix N) :
    transposeCongruence (1 + T) C =
      C + (T * C + C * T.transpose) + T * C * T.transpose := by
  simp only [transposeCongruence, Matrix.transpose_add, Matrix.transpose_one]
  noncomm_ring

/-- Transposition commutes with transpose congruence. -/
theorem transposeCongruence_transpose {N : ℕ}
    (g C : ComplexSquareMatrix N) :
    (transposeCongruence g C).transpose =
      transposeCongruence g C.transpose := by
  simp [transposeCongruence, Matrix.transpose_mul, Matrix.mul_assoc]

/-- Transpose congruence preserves the complex symmetric locus. -/
theorem transposeCongruence_isSymm {N : ℕ}
    (g : ComplexSquareMatrix N) {C : ComplexSquareMatrix N}
    (hC : C.IsSymm) : (transposeCongruence g C).IsSymm := by
  show (transposeCongruence g C).transpose = transposeCongruence g C
  rw [transposeCongruence_transpose, hC.eq]

/-- The literal exponential congruence orbit `rho_(exp(tA))(C)`. -/
def transposeCongruenceFlow {N : ℕ}
    (A : ComplexSquareMatrix N) (t : ℝ) (C : ComplexSquareMatrix N) :
    ComplexSquareMatrix N :=
  transposeCongruence (exp (((t : ℂ)) • A)) C

/-- Expanded literal form of the exponential congruence flow; in particular,
the right factor is `exp(t A.transpose)`, with transpose rather than adjoint. -/
theorem transposeCongruenceFlow_eq {N : ℕ}
    (A : ComplexSquareMatrix N) (t : ℝ) (C : ComplexSquareMatrix N) :
    transposeCongruenceFlow A t C =
      exp (((t : ℂ)) • A) * C * exp (((t : ℂ)) • A.transpose) := by
  simp [transposeCongruenceFlow, transposeCongruence,
    ← Matrix.exp_transpose]

@[simp]
theorem transposeCongruenceFlow_zero {N : ℕ}
    (A C : ComplexSquareMatrix N) :
    transposeCongruenceFlow A 0 C = C := by
  simp [transposeCongruenceFlow]

private theorem commute_real_smul_self {N : ℕ}
    (A : ComplexSquareMatrix N) (s t : ℝ) :
    Commute (((s : ℂ)) • A) (((t : ℂ)) • A) :=
  ((Commute.refl A).smul_left (s : ℂ)).smul_right (t : ℂ)

/-- The exponential congruences form an exact additive flow. -/
theorem transposeCongruenceFlow_add {N : ℕ}
    (A : ComplexSquareMatrix N) (s t : ℝ) (C : ComplexSquareMatrix N) :
    transposeCongruenceFlow A (s + t) C =
      transposeCongruenceFlow A s (transposeCongruenceFlow A t C) := by
  rw [transposeCongruenceFlow, transposeCongruenceFlow,
    transposeCongruenceFlow, ← transposeCongruence_mul]
  congr 1
  rw [Complex.ofReal_add, add_smul,
    Matrix.exp_add_of_commute _ _ (commute_real_smul_self A s t)]

/-- Exact exponential identity which re-centers the flow at an arbitrary
base time. -/
theorem transposeCongruenceFlow_baseTime_shift {N : ℕ}
    (A C : ComplexSquareMatrix N) (t0 h : ℝ) :
    exp ((((t0 + h : ℝ) : ℂ)) • A) * C *
        exp ((((t0 + h : ℝ) : ℂ)) • A.transpose) =
      exp (((h : ℝ) : ℂ) • A) *
        (exp (((t0 : ℝ) : ℂ) • A) * C *
          exp (((t0 : ℝ) : ℂ) • A.transpose) *
            exp (((h : ℝ) : ℂ) • A.transpose)) := by
  have hflow := transposeCongruenceFlow_add A h t0 C
  rw [add_comm h t0] at hflow
  simpa only [transposeCongruenceFlow_eq, Matrix.mul_assoc] using hflow

/-- Time `-t` is the two-sided inverse of time `t` on matrices. -/
theorem transposeCongruenceFlow_neg_left {N : ℕ}
    (A : ComplexSquareMatrix N) (t : ℝ) (C : ComplexSquareMatrix N) :
    transposeCongruenceFlow A (-t) (transposeCongruenceFlow A t C) = C := by
  rw [← transposeCongruenceFlow_add]
  simp

theorem measurable_transposeCongruence {N : ℕ}
    (g : ComplexSquareMatrix N) :
    Measurable (transposeCongruence g) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [transposeCongruence, Matrix.mul_apply, Matrix.transpose_apply]
  fun_prop

/-- Pushforward of a matrix law by literal transpose congruence. -/
def transposeCongruencePushforward {N : ℕ}
    (g : ComplexSquareMatrix N)
    (mu : Measure (ComplexSquareMatrix N)) :
    Measure (ComplexSquareMatrix N) :=
  Measure.map (transposeCongruence g) mu

/-- The exact matrix action law passes to pushforward measures. -/
theorem transposeCongruencePushforward_mul {N : ℕ}
    (g h : ComplexSquareMatrix N)
    (mu : Measure (ComplexSquareMatrix N)) :
    transposeCongruencePushforward g
        (transposeCongruencePushforward h mu) =
      transposeCongruencePushforward (g * h) mu := by
  unfold transposeCongruencePushforward
  rw [Measure.map_map (measurable_transposeCongruence g)
    (measurable_transposeCongruence h)]
  apply Measure.map_congr
  filter_upwards [] with C
  exact (transposeCongruence_mul g h C).symm

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

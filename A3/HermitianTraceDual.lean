import A3.HermitianCoordinates

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section
namespace A3Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def complexTraceCoefficientMatrix {d : ℕ}
    (L : Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j ↦ (L (Matrix.single j i 1) : ℂ) -
    (L (Matrix.single j i Complex.I) : ℂ) * Complex.I

theorem trace_complexTraceCoefficientMatrix {d : ℕ}
    (L : Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] ℝ) (X : Matrix (Fin d) (Fin d) ℂ) :
    ((complexTraceCoefficientMatrix L * X).trace).re = L X := by
  have hL : L X = ∑ i, ∑ j,
      ((X i j).re * L (Matrix.single i j 1) +
        (X i j).im * L (Matrix.single i j Complex.I)) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hs : Matrix.single i j (X i j) =
        (X i j).re • Matrix.single i j (1 : ℂ) +
          (X i j).im • Matrix.single i j Complex.I := by
      rw [Matrix.smul_single, Matrix.smul_single, ← Matrix.single_add]
      congr 1
      simp only [RCLike.real_smul_eq_coe_mul, mul_one]
      exact (Complex.re_add_im (X i j)).symm
    rw [hs, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  change (∑ i, ∑ j, (complexTraceCoefficientMatrix L i j) * X j i).re = _
  rw [Complex.re_sum]
  simp only [Complex.re_sum]
  have hp (i j : Fin d) : (complexTraceCoefficientMatrix L i j * X j i).re =
      (X j i).re * L (Matrix.single j i 1) +
        (X j i).im * L (Matrix.single j i Complex.I) := by
    simp [complexTraceCoefficientMatrix, Complex.mul_re]
    ring
  simp_rw [hp]
  rw [Finset.sum_comm, ← hL]

/-- The real trace pairing represents every real matrix functional on Hermitian inputs. -/
def hermitianTraceRepresentative {d : ℕ}
    (L : Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  (1 / 2 : ℝ) • (complexTraceCoefficientMatrix L + (complexTraceCoefficientMatrix L).conjTranspose)

theorem hermitianTraceRepresentative_isHermitian {d : ℕ}
    (L : Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] ℝ) :
    (hermitianTraceRepresentative L).IsHermitian := by
  unfold hermitianTraceRepresentative Matrix.IsHermitian
  simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, add_comm]

theorem trace_hermitianTraceRepresentative {d : ℕ}
    (L : Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] ℝ)
    (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.IsHermitian) :
    ((hermitianTraceRepresentative L * X).trace).re = L X := by
  let C := complexTraceCoefficientMatrix L
  have hc : (C.conjTranspose * X).trace = star ((C * X).trace) := by
    calc
      _ = (X * C.conjTranspose).trace := Matrix.trace_mul_comm _ _
      _ = ((C * X).conjTranspose).trace := by rw [Matrix.conjTranspose_mul, hX.eq]
      _ = _ := Matrix.trace_conjTranspose _
  unfold hermitianTraceRepresentative
  rw [Matrix.smul_mul, Matrix.add_mul, Matrix.trace_smul, Matrix.trace_add]
  change ((1 / 2 : ℝ) • ((C * X).trace + (C.conjTranspose * X).trace)).re = L X
  rw [hc]
  simp only [Complex.smul_re, Complex.add_re, Complex.star_def, Complex.conj_re,
    smul_eq_mul]
  rw [show (C * X).trace.re = L X from trace_complexTraceCoefficientMatrix L X]
  ring

end A3Research

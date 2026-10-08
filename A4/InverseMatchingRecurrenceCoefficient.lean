import A4.InverseMomentAlgebra

open scoped BigOperators Matrix

noncomputable section
namespace A4Research

set_option maxHeartbeats 400000

/-- A matrix commuting with an invertible Gram matrix also commutes with
its actual nonsingular inverse. -/
theorem gram_inverse_commutes {I : Type*} [Fintype I] [DecidableEq I]
    (G L : Matrix I I ℂ) (hG : IsUnit G.det) (hcomm : L * G = G * L) :
    G⁻¹ * L = L * G⁻¹ := by
  calc
    G⁻¹ * L = (G⁻¹ * L) * (G * G⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ hG, Matrix.mul_one]
    _ = G⁻¹ * (L * G) * G⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (G⁻¹ * G) * L * G⁻¹ := by rw [hcomm]; simp only [Matrix.mul_assoc]
    _ = L * G⁻¹ := by rw [Matrix.nonsing_inv_mul _ hG, Matrix.one_mul]

/-- Inversion of a genuinely proved rectangular degree factorization.
This is finite matrix algebra; the displayed factorization remains explicit. -/
theorem inverse_degree_factorization {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (G : Matrix I I ℂ) (H : Matrix J J ℂ) (E : Matrix I J ℂ)
    (L : Matrix I I ℂ) (hG : IsUnit G.det) (hH : IsUnit H.det)
    (hcomm : L * G = G * L) (hfactor : G * E = L * E * H) :
    L * G⁻¹ * E = E * H⁻¹ := by
  calc
    L * G⁻¹ * E = G⁻¹ * L * E := by rw [gram_inverse_commutes G L hG hcomm]
    _ = G⁻¹ * (L * E * H) * H⁻¹ := by
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hH, Matrix.mul_one]
    _ = G⁻¹ * (G * E) * H⁻¹ := by rw [← hfactor]
    _ = E * H⁻¹ := by
      rw [← Matrix.mul_assoc G⁻¹ G E, Matrix.nonsing_inv_mul _ hG, Matrix.one_mul]

/-- The exact `(-1)^n 2^n = (-2)^n` source normalization transforms the
orthogonal degree factorization into the inverse-entry Stein recurrence. -/
theorem normalized_inverse_degree_factorization {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (q : ℕ) (gamma : ℝ) (G : Matrix I I ℂ) (H : Matrix J J ℂ)
    (E : Matrix I J ℂ) (P : Matrix I I ℂ)
    (hG : IsUnit G.det) (hH : IsUnit H.det)
    (hcomm : ((-2 * (gamma : ℂ)) • (1 : Matrix I I ℂ) + P) * G =
      G * ((-2 * (gamma : ℂ)) • (1 : Matrix I I ℂ) + P))
    (hfactor : G * E =
      ((-2 * (gamma : ℂ)) • (1 : Matrix I I ℂ) + P) * E * H) :
    (gamma : ℂ) • (((-2 : ℂ) ^ (q + 1) • G⁻¹) * E) -
      (1 / 2 : ℂ) • (P * (((-2 : ℂ) ^ (q + 1) • G⁻¹) * E)) =
        E * ((-2 : ℂ) ^ q • H⁻¹) := by
  let L : Matrix I I ℂ := (-2 * (gamma : ℂ)) • (1 : Matrix I I ℂ) + P
  have h := inverse_degree_factorization G H E L hG hH hcomm hfactor
  have hscale : (-1 / 2 : ℂ) * (-2 : ℂ) ^ (q + 1) = (-2 : ℂ) ^ q := by
    rw [pow_succ]
    ring
  have hmain := congrArg (fun X : Matrix I J ℂ ↦
    ((-1 / 2 : ℂ) * (-2 : ℂ) ^ (q + 1)) • X) h
  simp only [L, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul,
    smul_add, smul_smul, hscale] at hmain
  rw [Matrix.mul_smul]
  rw [← hmain]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  rw [← hscale]
  ring

/-- The same normalized recurrence with an explicit finite sum of relabeling
matrices, so each crossed coefficient remains visible. -/
theorem normalized_inverse_degree_factorization_sum {I J K : Type*}
    [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J]
    (q : ℕ) (gamma : ℝ) (G : Matrix I I ℂ) (H : Matrix J J ℂ)
    (E : Matrix I J ℂ) (P : K → Matrix I I ℂ)
    (hG : IsUnit G.det) (hH : IsUnit H.det)
    (hcomm : ((-2 * (gamma : ℂ)) • (1 : Matrix I I ℂ) + ∑ k, P k) * G =
      G * ((-2 * (gamma : ℂ)) • (1 : Matrix I I ℂ) + ∑ k, P k))
    (hfactor : G * E =
      ((-2 * (gamma : ℂ)) • (1 : Matrix I I ℂ) + ∑ k, P k) * E * H) :
    (gamma : ℂ) • (((-2 : ℂ) ^ (q + 1) • G⁻¹) * E) -
      (1 / 2 : ℂ) • (∑ k : K, P k * (((-2 : ℂ) ^ (q + 1) • G⁻¹) * E)) =
        E * ((-2 : ℂ) ^ q • H⁻¹) := by
  rw [← Matrix.sum_mul]
  exact normalized_inverse_degree_factorization q gamma G H E (∑ k, P k)
    hG hH hcomm hfactor

end A4Research

namespace MatsumotoPaper

theorem modifiedGramInverse_isSymm (n : ℕ) (gamma : ℝ) :
    (modifiedGramInverse n gamma).IsSymm := by
  exact (orthogonalGram_isSymm n (-2 * (gamma : ℂ))).inv.smul _

end MatsumotoPaper

import A3.HermitianConjugation
import A3.HermitianSpectrum

open scoped BigOperators Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix MeasureTheory Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace A3Research

theorem prod_strictPairs_mul {M : Type*} [CommMonoid M] {n : ℕ} (d : Fin n → M) :
    (∏ ij : HermitianCoordinateIndex n, d ij.1.1 * d ij.1.2) =
      (∏ i, d i) ^ (n - 1) := by
  classical
  let s : Finset (Fin n × Fin n) := Finset.univ.filter fun p ↦ p.1 < p.2
  let t : Finset (Fin n × Fin n) := Finset.univ.filter fun p ↦ p.2 < p.1
  let q : Finset (Fin n × Fin n) := Finset.univ.filter fun p ↦ p.1 ≠ p.2
  have hflip : (∏ p ∈ s, d p.2) = ∏ p ∈ t, d p.1 := by
    apply Finset.prod_bij (fun p _ ↦ p.swap)
    · intro p hp
      simpa [s, t] using hp
    · intro p hp r hr he
      exact Prod.swap_injective he
    · intro p hp
      refine ⟨p.swap, ?_, rfl⟩
      simpa [s, t] using hp
    · intro p hp
      rfl
  have hdis : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro p hs ht
    exact (lt_asymm (Finset.mem_filter.mp hs).2 (Finset.mem_filter.mp ht).2)
  have hunion : s ∪ t = q := by
    ext p
    simp only [s, t, q, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (h | h)
      · exact ne_of_lt h
      · exact (ne_of_lt h).symm
    · intro hne
      rcases lt_trichotomy p.1 p.2 with h | h | h
      · exact Or.inl h
      · exact (hne h).elim
      · exact Or.inr h
  have hcount : (∏ p ∈ q, d p.1) = (∏ i, d i) ^ (n - 1) := by
    rw [show q = (Finset.univ ×ˢ Finset.univ).filter (fun p ↦ p.1 ≠ p.2) by
      ext p; simp [q], Finset.prod_filter, Finset.prod_product]
    have hrow (i : Fin n) : (∏ j : Fin n, if i ≠ j then d i else 1) = d i ^ (n - 1) := by
      rw [← Finset.prod_filter]
      have he : (Finset.univ.filter (fun j : Fin n ↦ i ≠ j)) = Finset.univ.erase i := by
        ext j
        simp [ne_comm]
      rw [he, Finset.prod_const]
      simp
    simp_rw [hrow]
    exact Finset.prod_pow _ _ _
  have hs : ∀ p, p ∈ s ↔ p.1 < p.2 := by intro p; simp [s]
  rw [← Finset.prod_subtype s hs (fun p ↦ d p.1 * d p.2), Finset.prod_mul_distrib]
  change (∏ p ∈ s, d p.1) * (∏ p ∈ s, d p.2) = _
  rw [hflip, ← Finset.prod_union hdis, hunion, hcount]

variable {n : ℕ} {K : Type*} [RCLike K]

def hermitianDiagonalCongruenceLinearMap (d : Fin n → ℝ) :
    HermitianCoordinates n K →ₗ[ℝ] HermitianCoordinates n K :=
  LinearMap.prodMap
    (LinearMap.pi fun i ↦ ((d i ^ 2) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).comp
      (LinearMap.proj i))
    (LinearMap.pi fun ij ↦ ((d ij.1.1 * d ij.1.2) • (LinearMap.id : K →ₗ[ℝ] K)).comp
      (LinearMap.proj ij))

@[simp] theorem hermitianDiagonalCongruenceLinearMap_apply (d : Fin n → ℝ)
    (x : HermitianCoordinates n K) :
    hermitianDiagonalCongruenceLinearMap d x =
      (fun i ↦ d i ^ 2 • x.1 i, fun ij ↦ (d ij.1.1 * d ij.1.2) • x.2 ij) := rfl

theorem hermitianCoordinateConjugation_diagonal (d : Fin n → ℝ) :
    hermitianCoordinateConjugationLinearMap (Matrix.diagonal (fun i ↦ (d i : K))) =
      hermitianDiagonalCongruenceLinearMap (K := K) d := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · funext i
    change RCLike.re ((Matrix.diagonal (fun i ↦ (d i : K)) *
      hermitianMatrixOfCoordinates x *
        (Matrix.diagonal (fun i ↦ (d i : K))).conjTranspose) i i) = _
    simp [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal,
      RCLike.real_smul_eq_coe_mul, pow_two]
    ring
  · funext ij
    change ((Matrix.diagonal (fun i ↦ (d i : K)) * hermitianMatrixOfCoordinates x *
      (Matrix.diagonal (fun i ↦ (d i : K))).conjTranspose) ij.1.1 ij.1.2) = _
    simp [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal,
      RCLike.real_smul_eq_coe_mul]
    ring

theorem det_hermitianCoordinateConjugation_diagonal (d : Fin n → ℝ) :
    LinearMap.det
      (hermitianCoordinateConjugationLinearMap (Matrix.diagonal (fun i ↦ (d i : K)))) =
      (∏ i, d i) ^ (2 + Module.finrank ℝ K * (n - 1)) := by
  rw [hermitianCoordinateConjugation_diagonal, hermitianDiagonalCongruenceLinearMap,
    LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi]
  simp only [LinearMap.det_smul, LinearMap.det_id, one_mul, mul_one,
    Module.finrank_self, pow_one]
  rw [Finset.prod_pow, Finset.prod_pow, prod_strictPairs_mul, ← pow_mul, ← pow_add]
  congr 1
  ac_rfl

theorem re_det_pos_of_posDef {C : Matrix (Fin n) (Fin n) K} (hC : C.PosDef) :
    0 < RCLike.re C.det := by
  rw [hC.isHermitian.det_eq_prod_eigenvalues,
    ← map_prod (algebraMap ℝ K), RCLike.ofReal_re]
  exact Finset.prod_pos fun i _ ↦ hC.eigenvalues_pos i

/-- The full independent-coordinate determinant of a positive-definite congruence. -/
theorem abs_det_hermitianCoordinateConjugation_posDef
    {C : Matrix (Fin n) (Fin n) K} (hC : C.PosDef) :
    |LinearMap.det (hermitianCoordinateConjugationLinearMap C)| =
      (RCLike.re C.det) ^ (2 + Module.finrank ℝ K * (n - 1)) := by
  let U := hC.isHermitian.eigenvectorUnitary
  let d := hC.isHermitian.eigenvalues
  have hspec : C = (U : Matrix (Fin n) (Fin n) K) *
      Matrix.diagonal (fun i ↦ (d i : K)) *
        star (U : Matrix (Fin n) (Fin n) K) := by
    simpa only [Unitary.conjStarAlgAut_apply, Function.comp_def] using hC.isHermitian.spectral_theorem
  have hu : |LinearMap.det (hermitianCoordinateConjugationLinearMap
      (U : Matrix (Fin n) (Fin n) K))| = 1 :=
    abs_det_hermitianConjugationRepresentation U
  have hus : |LinearMap.det (hermitianCoordinateConjugationLinearMap
      (star (U : Matrix (Fin n) (Fin n) K)))| = 1 :=
    abs_det_hermitianConjugationRepresentation U⁻¹
  have hp : 0 ≤ ∏ i, d i := (Finset.prod_pos fun i _ ↦ hC.eigenvalues_pos i).le
  calc
    _ = |LinearMap.det (hermitianCoordinateConjugationLinearMap
        (U : Matrix (Fin n) (Fin n) K))| *
        |LinearMap.det (hermitianCoordinateConjugationLinearMap
          (Matrix.diagonal (fun i ↦ (d i : K))))| *
        |LinearMap.det (hermitianCoordinateConjugationLinearMap
          (star (U : Matrix (Fin n) (Fin n) K)))| := by
      rw [hspec, hermitianCoordinateConjugation_mul, hermitianCoordinateConjugation_mul]
      simp only [map_mul, abs_mul]
    _ = (∏ i, d i) ^ (2 + Module.finrank ℝ K * (n - 1)) := by
      rw [hu, hus, one_mul, mul_one, det_hermitianCoordinateConjugation_diagonal,
        abs_of_nonneg (pow_nonneg hp _)]
    _ = _ := by
      congr 1
      rw [hC.isHermitian.det_eq_prod_eigenvalues, ← map_prod (algebraMap ℝ K)]
      simp only [RCLike.ofReal_re]
      rfl

theorem det_eq_ofReal_re_of_posDef {C : Matrix (Fin n) (Fin n) K} (hC : C.PosDef) :
    C.det = (RCLike.re C.det : K) := by
  rw [hC.isHermitian.det_eq_prod_eigenvalues, ← map_prod (algebraMap ℝ K)]
  simp only [RCLike.ofReal_re]

/-- The fixed-fiber Jacobian for `A=C J Cᴴ`, with `C` positive definite. -/
theorem abs_det_hermitianCoordinateConjugation_posDef_square
    {C : Matrix (Fin n) (Fin n) K} (hC : C.PosDef) :
    |LinearMap.det (hermitianCoordinateConjugationLinearMap C)| =
      (RCLike.re (C * C).det) ^
        (1 + (Module.finrank ℝ K : ℝ) * (n - 1 : ℕ) / 2) := by
  have hp := re_det_pos_of_posDef hC
  have he : RCLike.re (C * C).det = (RCLike.re C.det) ^ 2 := by
    rw [Matrix.det_mul, det_eq_ofReal_re_of_posDef hC]
    simp [pow_two]
  rw [abs_det_hermitianCoordinateConjugation_posDef hC, he]
  rw [← Real.rpow_natCast (RCLike.re C.det) (2 + Module.finrank ℝ K * (n - 1)),
    ← Real.rpow_natCast (RCLike.re C.det) 2, ← Real.rpow_mul hp.le]
  congr 1
  push_cast
  ring

end A3Research

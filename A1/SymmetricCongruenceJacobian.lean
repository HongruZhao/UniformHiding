import A2.UnitaryCongruenceVolume
import A3.HermitianCongruenceJacobian

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.Elementwise
open Matrix MeasureTheory
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace A1Research

theorem prod_upperPairs_mul {M : Type*} [CommMonoid M] {m : ℕ} (d : Fin m → M) :
    (∏ ij : ComplexSymmetricCoordinateIndex m, d ij.1.1 * d ij.1.2) =
      (∏ i, d i) ^ (m + 1) := by
  classical
  cases m with
  | zero => simp
  | succ m =>
    let upper : Finset (Fin (m + 1) × Fin (m + 1)) :=
      Finset.univ.filter fun p ↦ p.1 ≤ p.2
    let diagonal : Finset (Fin (m + 1) × Fin (m + 1)) :=
      Finset.univ.filter fun p ↦ p.1 = p.2
    let strict : Finset (Fin (m + 1) × Fin (m + 1)) :=
      Finset.univ.filter fun p ↦ p.1 < p.2
    have hdis : Disjoint diagonal strict := by
      apply Finset.disjoint_left.mpr
      intro p hp hq
      exact (ne_of_lt (Finset.mem_filter.mp hq).2) (Finset.mem_filter.mp hp).2
    have hunion : diagonal ∪ strict = upper := by
      ext p
      simp only [diagonal, strict, upper, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and]
      omega
    have hdiag : (∏ p ∈ diagonal, d p.1 * d p.2) = (∏ i, d i) ^ 2 := by
      calc
        _ = ∏ i : Fin (m + 1), d i * d i := by
          symm
          apply Finset.prod_bij (fun i _ ↦ (i, i))
          · intro i hi; simp [diagonal]
          · intro i hi j hj he; exact congrArg Prod.fst he
          · intro p hp
            refine ⟨p.1, Finset.mem_univ _, ?_⟩
            exact Prod.ext rfl (Finset.mem_filter.mp hp).2
          · intro i hi; rfl
        _ = _ := by simp only [← pow_two, Finset.prod_pow]
    have hu : ∀ p, p ∈ upper ↔ p.1 ≤ p.2 := by intro p; simp [upper]
    have hs : ∀ p, p ∈ strict ↔ p.1 < p.2 := by intro p; simp [strict]
    rw [← Finset.prod_subtype upper hu (fun p ↦ d p.1 * d p.2), ← hunion,
      Finset.prod_union hdis, hdiag,
      Finset.prod_subtype strict hs (fun p ↦ d p.1 * d p.2),
      A3Research.prod_strictPairs_mul, ← pow_add]
    congr 1
    omega

def symmetricRealCongruenceLinearMap {m : ℕ} (C : Matrix (Fin m) (Fin m) ℂ) :
    ComplexSymmetricCoordinates m →ₗ[ℝ] ComplexSymmetricCoordinates m :=
  (A2Research.symmetricCongruenceLinearMap C).restrictScalars ℝ

theorem symmetricRealCongruenceLinearMap_mul {m : ℕ}
    (C D : Matrix (Fin m) (Fin m) ℂ) :
    symmetricRealCongruenceLinearMap (C * D) =
      symmetricRealCongruenceLinearMap C * symmetricRealCongruenceLinearMap D := by
  apply LinearMap.ext
  intro x
  change A2Research.symmetricCongruenceLinearMap (C * D) x =
    A2Research.symmetricCongruenceLinearMap C
      (A2Research.symmetricCongruenceLinearMap D x)
  rw [A2Research.symmetricCongruenceLinearMap_mul]
  rfl

def symmetricDiagonalRealCongruenceLinearMap {m : ℕ} (d : Fin m → ℝ) :
    ComplexSymmetricCoordinates m →ₗ[ℝ] ComplexSymmetricCoordinates m :=
  LinearMap.pi fun ij ↦ ((d ij.1.1 * d ij.1.2) • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)).comp
    (LinearMap.proj ij)

theorem symmetricRealCongruenceLinearMap_diagonal {m : ℕ} (d : Fin m → ℝ) :
    symmetricRealCongruenceLinearMap (Matrix.diagonal (fun i ↦ (d i : ℂ))) =
      symmetricDiagonalRealCongruenceLinearMap d := by
  apply LinearMap.ext
  intro x
  funext ij
  change ((Matrix.diagonal (fun i ↦ (d i : ℂ))) *
    complexSymmetricMatrixOfCoordinates x *
      (Matrix.diagonal (fun i ↦ (d i : ℂ))).transpose) ij.1.1 ij.1.2 = _
  simp [symmetricDiagonalRealCongruenceLinearMap, Matrix.diagonal_mul,
    Matrix.mul_diagonal, complexSymmetricMatrixOfCoordinates, ij.property,
    Complex.real_smul, pow_two]
  ring

theorem det_symmetricRealCongruenceLinearMap_diagonal {m : ℕ} (d : Fin m → ℝ) :
    LinearMap.det (symmetricRealCongruenceLinearMap
      (Matrix.diagonal (fun i ↦ (d i : ℂ)))) = (∏ i, d i) ^ (2 * (m + 1)) := by
  rw [symmetricRealCongruenceLinearMap_diagonal,
    symmetricDiagonalRealCongruenceLinearMap, LinearMap.det_pi]
  simp only [LinearMap.det_smul, LinearMap.det_id, mul_one, Complex.finrank_real_complex]
  rw [Finset.prod_pow, prod_upperPairs_mul, ← pow_mul]
  congr 1
  omega

/-- The real Jacobian on every independent complex symmetric coordinate. -/
theorem abs_det_symmetricRealCongruenceLinearMap_posDef {m : ℕ}
    {C : Matrix (Fin m) (Fin m) ℂ} (hC : C.PosDef) :
    |LinearMap.det (symmetricRealCongruenceLinearMap C)| =
      C.det.re ^ (2 * (m + 1)) := by
  let U := hC.isHermitian.eigenvectorUnitary
  let d := hC.isHermitian.eigenvalues
  have hspec : C = (U : Matrix (Fin m) (Fin m) ℂ) *
      Matrix.diagonal (fun i ↦ (d i : ℂ)) *
        star (U : Matrix (Fin m) (Fin m) ℂ) := by
    ext i j
    have ht := congrArg (fun B : Matrix (Fin m) (Fin m) ℂ ↦ B i j)
      hC.isHermitian.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.mul_apply] at ht
    convert ht using 1 <;> rfl
  have hu : |LinearMap.det (symmetricRealCongruenceLinearMap
      (U : Matrix (Fin m) (Fin m) ℂ))| = 1 :=
    A2Research.abs_det_unitaryCongruenceRepresentation m U
  have hus : |LinearMap.det (symmetricRealCongruenceLinearMap
      (star (U : Matrix (Fin m) (Fin m) ℂ)))| = 1 :=
    A2Research.abs_det_unitaryCongruenceRepresentation m U⁻¹
  have hp : 0 ≤ ∏ i, d i := (Finset.prod_pos fun i _ ↦ hC.eigenvalues_pos i).le
  calc
    _ = |LinearMap.det (symmetricRealCongruenceLinearMap
        (U : Matrix (Fin m) (Fin m) ℂ))| *
        |LinearMap.det (symmetricRealCongruenceLinearMap
          (Matrix.diagonal (fun i ↦ (d i : ℂ))))| *
        |LinearMap.det (symmetricRealCongruenceLinearMap
          (star (U : Matrix (Fin m) (Fin m) ℂ)))| := by
      rw [hspec, symmetricRealCongruenceLinearMap_mul, symmetricRealCongruenceLinearMap_mul]
      simp only [map_mul, abs_mul]
    _ = (∏ i, d i) ^ (2 * (m + 1)) := by
      rw [hu, hus, one_mul, mul_one, det_symmetricRealCongruenceLinearMap_diagonal,
        abs_of_nonneg (pow_nonneg hp _)]
    _ = _ := by
      congr 1
      rw [hC.isHermitian.det_eq_prod_eigenvalues, ← map_prod (algebraMap ℝ ℂ)]
      rfl

/-- Square-root congruence has Jacobian `det(T)^(m+1)`. -/
theorem abs_det_symmetricRealCongruenceLinearMap_posDef_square {m : ℕ}
    {C : Matrix (Fin m) (Fin m) ℂ} (hC : C.PosDef) :
    |LinearMap.det (symmetricRealCongruenceLinearMap C)| =
      ((C * C).det.re) ^ (m + 1) := by
  have he : (C * C).det.re = C.det.re ^ 2 := by
    rw [Matrix.det_mul, A3Research.det_eq_ofReal_re_of_posDef hC]
    simp [pow_two]
  rw [abs_det_symmetricRealCongruenceLinearMap_posDef hC, he, pow_mul]

end A1Research

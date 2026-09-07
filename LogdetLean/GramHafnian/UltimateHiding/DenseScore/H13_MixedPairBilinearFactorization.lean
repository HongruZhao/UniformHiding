import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_FullSixWordProjectivePolynomial
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_ProjectiveMixedHolder
import Mathlib.Tactic

/-!
# Bilinear factorization of the mixed H13 projective pairing

The full H13 polynomial contains the two-projector scalar

`m_v(A,B) = Tr(P_v A P_v.transpose B)`.

It factors exactly into two quadratic bilinear forms.  This exposes every
degree-four H13 monomial as a product of four scalar factors, in the precise
shape consumed by `H13_ProjectiveMixedHolder`.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

set_option maxHeartbeats 2400000

/-- The conjugate-bilinear quadratic form `v^* A conjugate(v)`. -/
def complexProjectiveConjugateBilinearPair
    {N : ℕ} (v : ComplexUnitSphere N)
    (A : ConcreteMatrixState N) : ℂ :=
  ∑ i, ∑ j, star (v.1 i) * A i j * star (v.1 j)

/-- The transpose-bilinear quadratic form `v^T B v`. -/
def complexProjectiveTransposeBilinearPair
    {N : ℕ} (v : ComplexUnitSphere N)
    (B : ConcreteMatrixState N) : ℂ :=
  ∑ i, ∑ j, v.1 i * B i j * v.1 j

/-- Exact two-factor decomposition of the mixed transpose trace pairing. -/
theorem complexProjectiveMixedTransposePair_eq_bilinearFactors_h13
    {N : ℕ} (v : ComplexUnitSphere N)
    (A B : ConcreteMatrixState N) :
    complexProjectiveMixedTransposePair v A B =
      complexProjectiveConjugateBilinearPair v A *
        complexProjectiveTransposeBilinearPair v B := by
  unfold complexProjectiveMixedTransposePair
  unfold complexProjectiveConjugateBilinearPair
  unfold complexProjectiveTransposeBilinearPair
  simp only [Matrix.trace, Matrix.diag_apply]
  simp_rw [Matrix.mul_apply]
  unfold complexRankOneProjection
  simp only [Finset.mul_sum, Finset.sum_mul]
  let f : Fin N → Fin N → Fin N → Fin N → ℂ := fun i j k l ↦
    star (v.1 j) * A j k * star (v.1 k) *
      (v.1 l * B l i * v.1 i)
  simp_rw [show ∀ (i l k j : Fin N),
      v.1 i * star (v.1 j) * A j k *
          Matrix.transpose
            (fun r s : Fin N ↦ v.1 r * star (v.1 s)) k l * B l i =
        f i j k l by
    intro i l k j
    change v.1 i * star (v.1 j) * A j k *
        (v.1 l * star (v.1 k)) * B l i = f i j k l
    dsimp only [f]
    ring]
  change (∑ i, ∑ l, ∑ k, ∑ j, f i j k l) =
    ∑ l, ∑ i, ∑ j, ∑ k, f i j k l
  calc
    (∑ i, ∑ l, ∑ k, ∑ j, f i j k l) =
        ∑ l, ∑ i, ∑ k, ∑ j, f i j k l := Finset.sum_comm
    _ = ∑ l, ∑ i, ∑ j, ∑ k, f i j k l := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm

/-- The transpose-bilinear factor of `A^*` is the conjugate of the
conjugate-bilinear factor of `A`. -/
theorem complexProjectiveTransposeBilinearPair_conjTranspose_eq_star_h13
    {N : ℕ} (v : ComplexUnitSphere N)
    (A : ConcreteMatrixState N) :
    complexProjectiveTransposeBilinearPair v A.conjTranspose =
      star (complexProjectiveConjugateBilinearPair v A) := by
  unfold complexProjectiveTransposeBilinearPair
  unfold complexProjectiveConjugateBilinearPair
  simp only [Matrix.conjTranspose_apply, star_sum, star_mul, star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- In the positive conjugate case the mixed pairing is exactly the existing
H14 bilinear norm-square. -/
theorem complexProjectiveMixedTransposePair_conjTranspose_eq_normSq_h13
    {N : ℕ} (v : ComplexUnitSphere N)
    (A : ConcreteMatrixState N) :
    complexProjectiveMixedTransposePair v A A.conjTranspose =
      complexProjectiveBilinearNormSq v A := by
  unfold complexProjectiveMixedTransposePair
  rw [show complexRankOneProjection v * A *
      (complexRankOneProjection v).transpose * A.conjTranspose =
      complexRankOneProjection v *
        (A * ((complexRankOneProjection v).transpose * A.conjTranspose)) by
    noncomm_ring]
  exact trace_rankOne_symmSandwich_eq_bilinearNormSq_h14 v A

/-- Absolute-value form of the exact factorization, ready for scalar Holder. -/
theorem norm_complexProjectiveMixedTransposePair_eq_mul_h13
    {N : ℕ} (v : ComplexUnitSphere N)
    (A B : ConcreteMatrixState N) :
    ‖complexProjectiveMixedTransposePair v A B‖ =
      ‖complexProjectiveConjugateBilinearPair v A‖ *
        ‖complexProjectiveTransposeBilinearPair v B‖ := by
  rw [complexProjectiveMixedTransposePair_eq_bilinearFactors_h13,
    norm_mul]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

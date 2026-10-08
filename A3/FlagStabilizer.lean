import A3.FlagCompactness

open scoped BigOperators Matrix.Norms.Elementwise
open Matrix Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]

theorem flagEvaluation_orbit_mul (μ : Fin n → ℝ)
    (U V : Matrix.unitaryGroup (Fin n) K) :
    flagEvaluation μ (flagOrbit (U * V)) =
      (U : Matrix (Fin n) (Fin n) K) * flagEvaluation μ (flagOrbit V) *
        star (U : Matrix (Fin n) (Fin n) K) := by
  simp only [flagEvaluation_flagOrbit, Matrix.UnitaryGroup.mul_val,
    Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]

theorem commuting_distinct_diagonal_offDiagonal_zero
    (Q : Matrix (Fin n) (Fin n) K) (μ : Fin n → ℝ)
    (hμ : Function.Injective μ)
    (hc : Commute Q (Matrix.diagonal (fun i ↦ (μ i : K))))
    (i j : Fin n) (hij : i ≠ j) : Q i j = 0 := by
  have he := congrArg (fun A : Matrix (Fin n) (Fin n) K ↦ A i j) hc.eq
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
  have hneq : (μ j : K) ≠ (μ i : K) := by
    intro h
    exact hij (hμ (RCLike.ofReal_injective h)).symm
  have hz : Q i j * ((μ j : K) - (μ i : K)) = 0 := by
    rw [mul_sub, he, mul_comm]
    exact sub_self _
  exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hneq)

theorem commuting_distinct_diagonal_eq_diagonal
    (Q : Matrix (Fin n) (Fin n) K) (μ : Fin n → ℝ)
    (hμ : Function.Injective μ)
    (hc : Commute Q (Matrix.diagonal (fun i ↦ (μ i : K)))) :
    Q = Matrix.diagonal (fun i ↦ Q i i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · rw [commuting_distinct_diagonal_offDiagonal_zero Q μ hμ hc i j hij]
    simp [Matrix.diagonal_apply, hij]

/-- The stabilizer of a distinct Hermitian spectrum fixes every ordered projector. -/
theorem flagProjectors_eq_identity_of_distinct_stabilizer
    (Q : Matrix.unitaryGroup (Fin n) K) (μ : Fin n → ℝ)
    (hμ : Function.Injective μ)
    (hQ : flagEvaluation μ (flagOrbit Q) =
      Matrix.diagonal (fun i ↦ (μ i : K))) :
    flagProjectors Q = flagProjectors (1 : Matrix.unitaryGroup (Fin n) K) := by
  have hc : Commute (Q : Matrix (Fin n) (Fin n) K)
      (Matrix.diagonal (fun i ↦ (μ i : K))) := by
    apply (commute_unitary_iff_star_right_conjugate Q.property).mpr
    simpa only [flagEvaluation_flagOrbit, Matrix.star_eq_conjTranspose] using hQ
  have hdiag := commuting_distinct_diagonal_eq_diagonal
    (Q : Matrix (Fin n) (Fin n) K) μ hμ hc
  funext i
  have hi : Commute (Q : Matrix (Fin n) (Fin n) K) (Matrix.single i i 1) := by
    rw [hdiag, ← Matrix.diagonal_single]
    exact Matrix.commute_diagonal _ _
  have he := (commute_unitary_iff_star_right_conjugate Q.property).mp hi
  simpa only [flagProjectors, Matrix.UnitaryGroup.one_val, Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one, Matrix.star_eq_conjTranspose] using he

theorem flagProjectors_mul (U V : Matrix.unitaryGroup (Fin n) K) (i : Fin n) :
    flagProjectors (U * V) i =
      (U : Matrix (Fin n) (Fin n) K) * flagProjectors V i *
        star (U : Matrix (Fin n) (Fin n) K) := by
  simp only [flagProjectors, Matrix.UnitaryGroup.mul_val,
    Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]

theorem flagProjectors_eq_of_distinct_evaluation
    (μ : Fin n → ℝ) (hμ : Function.Injective μ)
    (U V : Matrix.unitaryGroup (Fin n) K)
    (h : flagEvaluation μ (flagOrbit U) = flagEvaluation μ (flagOrbit V)) :
    flagProjectors U = flagProjectors V := by
  let Q := U⁻¹ * V
  have hQ : flagEvaluation μ (flagOrbit Q) =
      Matrix.diagonal (fun i ↦ (μ i : K)) := by
    have h' := congrArg (fun H : Matrix (Fin n) (Fin n) K ↦
      star (U : Matrix (Fin n) (Fin n) K) * H *
        (U : Matrix (Fin n) (Fin n) K)) h
    have hleft : star (U : Matrix (Fin n) (Fin n) K) *
        flagEvaluation μ (flagOrbit U) * (U : Matrix (Fin n) (Fin n) K) =
        Matrix.diagonal (fun i ↦ (μ i : K)) := by
      rw [flagEvaluation_flagOrbit]
      rw [← Matrix.star_eq_conjTranspose]
      simp only [← Matrix.mul_assoc, U.property.1, Matrix.one_mul]
      simp only [Matrix.mul_assoc, U.property.1, Matrix.mul_one]
    rw [hleft] at h'
    rw [show Q = U⁻¹ * V from rfl, flagEvaluation_orbit_mul]
    simpa only [Matrix.UnitaryGroup.inv_val, star_star] using h'.symm
  have hQP := flagProjectors_eq_identity_of_distinct_stabilizer Q μ hμ hQ
  have hV : U * Q = V := by simp [Q]
  funext i
  rw [← hV, flagProjectors_mul, hQP]
  simp [flagProjectors, Matrix.star_eq_conjTranspose]

theorem flagEvaluation_injective (μ : Fin n → ℝ) (hμ : Function.Injective μ) :
    Function.Injective (flagEvaluation (K := K) μ) := by
  intro P R h
  obtain ⟨U, hU⟩ := P.property
  obtain ⟨V, hV⟩ := R.property
  have hP : P = flagOrbit U := Subtype.ext hU.symm
  have hR : R = flagOrbit V := Subtype.ext hV.symm
  subst P R
  exact Subtype.ext (flagProjectors_eq_of_distinct_evaluation μ hμ U V h)

theorem isClosedEmbedding_flagEvaluation (μ : Fin n → ℝ)
    (hμ : Function.Injective μ) :
    Topology.IsClosedEmbedding (flagEvaluation (K := K) μ) :=
  (continuous_flagEvaluation μ).isClosedEmbedding (flagEvaluation_injective μ hμ)

/-- The flag orbit is homeomorphic to its literal fixed-spectrum Hermitian orbit. -/
def flagEvaluationHomeomorph (μ : Fin n → ℝ) (hμ : Function.Injective μ) :
    flagSpace n K ≃ₜ Set.range (flagEvaluation (K := K) μ) :=
  (isClosedEmbedding_flagEvaluation μ hμ).isEmbedding.toHomeomorph

end A3Research

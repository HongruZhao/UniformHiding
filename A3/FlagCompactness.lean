import A3.HermitianCoordinates

open scoped BigOperators Matrix.Norms.Elementwise
open Matrix Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]

/-- The ordered rank-one projectors of a unitary frame. -/
def flagProjectors (U : Matrix.unitaryGroup (Fin n) K) :
    Fin n → Matrix (Fin n) (Fin n) K :=
  fun i ↦ (U : Matrix (Fin n) (Fin n) K) * Matrix.single i i 1 *
    (U : Matrix (Fin n) (Fin n) K).conjTranspose

def flagSpace (n : ℕ) (K : Type*) [RCLike K] :=
  Set.range (flagProjectors : Matrix.unitaryGroup (Fin n) K → _)

def flagOrbit (U : Matrix.unitaryGroup (Fin n) K) : flagSpace n K :=
  ⟨flagProjectors U, Set.mem_range_self U⟩

theorem continuous_flagProjectors :
    Continuous (flagProjectors : Matrix.unitaryGroup (Fin n) K → _) := by
  unfold flagProjectors
  exact continuous_pi fun i ↦ by fun_prop

theorem continuous_flagOrbit :
    Continuous (flagOrbit : Matrix.unitaryGroup (Fin n) K → flagSpace n K) :=
  continuous_flagProjectors.subtype_mk _

theorem unitaryGroup_isCompact_rclike (n : ℕ) (K : Type*) [RCLike K] :
    IsCompact (Matrix.unitaryGroup (Fin n) K : Set (Matrix (Fin n) (Fin n) K)) := by
  let D : Set K := Metric.closedBall 0 1
  have hbox : IsCompact (D.matrix : Set (Matrix (Fin n) (Fin n) K)) :=
    (isCompact_closedBall (0 : K) 1).matrix
  refine hbox.of_isClosed_subset ?_ ?_
  · simpa only using isClosed_unitary (R := Matrix (Fin n) (Fin n) K)
  · intro A hA
    rw [Set.mem_matrix]
    intro i j
    simpa [D, Metric.mem_closedBall, dist_zero_right] using
      entry_norm_bound_of_unitary hA i j

instance unitaryGroup_compactSpace_rclike (n : ℕ) (K : Type*) [RCLike K] :
    CompactSpace (Matrix.unitaryGroup (Fin n) K) :=
  isCompact_iff_compactSpace.mp (unitaryGroup_isCompact_rclike n K)

theorem isCompact_flagSpace (n : ℕ) (K : Type*) [RCLike K] :
    IsCompact (flagSpace n K) := by
  simpa only [flagSpace, Set.image_univ] using
    isCompact_univ.image (continuous_flagProjectors (n := n) (K := K))

instance flagSpace_compactSpace (n : ℕ) (K : Type*) [RCLike K] :
    CompactSpace (flagSpace n K) :=
  isCompact_iff_compactSpace.mp (isCompact_flagSpace n K)

/-- Evaluation of the actual ordered projector flag at real spectral weights. -/
def flagEvaluation (μ : Fin n → ℝ) (P : flagSpace n K) :
    Matrix (Fin n) (Fin n) K :=
  ∑ i, μ i • P.1 i

theorem continuous_flagEvaluation (μ : Fin n → ℝ) :
    Continuous (flagEvaluation (K := K) μ) := by
  unfold flagEvaluation
  exact continuous_finsetSum _ fun i _ ↦
    ((continuous_apply i).comp
      (continuous_subtype_val : Continuous (fun P : flagSpace n K ↦ P.val))).const_smul (μ i)

theorem flagEvaluation_flagOrbit (μ : Fin n → ℝ)
    (U : Matrix.unitaryGroup (Fin n) K) :
    flagEvaluation μ (flagOrbit U) =
      (U : Matrix (Fin n) (Fin n) K) * Matrix.diagonal (fun i ↦ (μ i : K)) *
        (U : Matrix (Fin n) (Fin n) K).conjTranspose := by
  unfold flagEvaluation flagOrbit flagProjectors
  have hs (i : Fin n) :
      μ i • ((U : Matrix (Fin n) (Fin n) K) * Matrix.single i i 1 *
        (U : Matrix (Fin n) (Fin n) K).conjTranspose) =
      (U : Matrix (Fin n) (Fin n) K) * (μ i • Matrix.single i i (1 : K)) *
        (U : Matrix (Fin n) (Fin n) K).conjTranspose := by
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  simp_rw [hs]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have he : (∑ i, μ i • Matrix.single i i (1 : K)) =
      Matrix.diagonal (fun i ↦ (μ i : K)) := by
    simp only [Matrix.smul_single, RCLike.real_smul_eq_coe_mul, mul_one]
    exact Matrix.sum_single_eq_diagonal _
  rw [he]

end A3Research

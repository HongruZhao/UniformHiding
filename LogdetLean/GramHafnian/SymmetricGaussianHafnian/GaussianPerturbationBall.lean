import LogdetLean.GramHafnian.SymmetricGaussianHafnian.GaussianPerturbation
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.CircularGaussianAnderson

/-!
# Centered-ball comparison for arbitrary complex edge perturbations

The proof repeats complete-vertex-star centering under the unchanged product
law of the independent complex Gaussian edges.  Its scalar input is the
axiom-free reflection proof that a centered disk maximizes circular Gaussian
mass.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

set_option maxHeartbeats 800000

private def shiftedStarBall {n : ℕ} (b : Edge (Fin n) → ℂ)
    (a : Fin n → ℂ) (w : ℂ) (rho : ℝ) :
    Set ((Edge (Fin n) → ℂ) × (Fin n → ℂ)) :=
  {p | ‖iidCircularTransposeLinearForm (edgeCofactor (p.1 + b))
    (p.2 + a) - w‖ ≤ rho}

private theorem measurableSet_shiftedStarBall {n : ℕ}
    (b : Edge (Fin n) → ℂ) (a : Fin n → ℂ) (w : ℂ) (rho : ℝ) :
    MeasurableSet (shiftedStarBall b a w rho) := by
  unfold shiftedStarBall iidCircularTransposeLinearForm
  exact measurableSet_le (by fun_prop) measurable_const

private theorem measure_shiftedStarBall_le {n : ℕ}
    (b : Edge (Fin n) → ℂ) (a : Fin n → ℂ) (w : ℂ)
    (rho : ℝ) (hrho : 0 ≤ rho) :
    ((edgeGaussian (Fin n)).prod (standardGaussianProduct (Fin n)))
        (shiftedStarBall b a w rho) ≤
      ((edgeGaussian (Fin n)).prod (standardGaussianProduct (Fin n)))
        (shiftedStarBall b 0 0 rho) := by
  rw [Measure.prod_apply (measurableSet_shiftedStarBall b a w rho),
    Measure.prod_apply (measurableSet_shiftedStarBall b 0 0 rho)]
  apply lintegral_mono
  intro R
  let y := edgeCofactor (R + b)
  have hleft : Prod.mk R ⁻¹' shiftedStarBall b a w rho =
      {g : Fin n → ℂ |
        ‖iidCircularTransposeLinearForm y g +
          (iidCircularTransposeLinearForm y a - w)‖ ≤ rho} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    unfold shiftedStarBall
    change (‖iidCircularTransposeLinearForm y (g + a) - w‖ ≤ rho) ↔ _
    simp only [iidCircularTransposeLinearForm, Pi.add_apply, add_mul,
      Finset.sum_add_distrib]
    ring_nf
  have hright : Prod.mk R ⁻¹' shiftedStarBall b 0 0 rho =
      {g : Fin n → ℂ | ‖iidCircularTransposeLinearForm y g‖ ≤ rho} := by
    ext g
    simp [shiftedStarBall, y]
  change (standardGaussianProduct (Fin n))
      (Prod.mk R ⁻¹' shiftedStarBall b a w rho) ≤
    (standardGaussianProduct (Fin n))
      (Prod.mk R ⁻¹' shiftedStarBall b 0 0 rho)
  rw [hleft, hright]
  exact iidCircularTransposeLinearForm_norm_add_le_centered y
    (iidCircularTransposeLinearForm y a - w) rho hrho

/-- Exact one-star centered-ball comparison at the final vertex. -/
theorem edgeHafnian_ball_le_zeroStar_last
    (n : ℕ) (a : Edge (Fin (n + 1)) → ℂ) (w : ℂ)
    (rho : ℝ) (hrho : 0 ≤ rho) :
    edgeGaussian (Fin (n + 1))
        {x | ‖edgeHafnian (x + a) - w‖ ≤ rho} ≤
      edgeGaussian (Fin (n + 1))
        {x | ‖edgeHafnian (x + zeroStar (Fin.last n) a)‖ ≤ rho} := by
  let b := (lastVertexSplit n a).1
  let c := (lastVertexSplit n a).2
  let Sleft := shiftedStarBall b c w rho
  let Sright := shiftedStarBall b 0 0 rho
  have hSleft : MeasurableSet Sleft :=
    measurableSet_shiftedStarBall b c w rho
  have hSright : MeasurableSet Sright :=
    measurableSet_shiftedStarBall b 0 0 rho
  let Tleft : Set (Edge (Fin (n + 1)) → ℂ) :=
    {x | ‖edgeHafnian (x + a) - w‖ ≤ rho}
  let Tright : Set (Edge (Fin (n + 1)) → ℂ) :=
    {x | ‖edgeHafnian (x + zeroStar (Fin.last n) a)‖ ≤ rho}
  have hpreLeft : Tleft = lastVertexSplit n ⁻¹' Sleft := by
    ext x
    change (‖edgeHafnian (x + a) - w‖ ≤ rho) ↔
      (‖iidCircularTransposeLinearForm
        (edgeCofactor ((lastVertexSplit n x).1 + b))
        ((lastVertexSplit n x).2 + c) - w‖ ≤ rho)
    rw [edgeHafnian_add_lastVertexSplit]
  have hpreRight : Tright = lastVertexSplit n ⁻¹' Sright := by
    ext x
    change (‖edgeHafnian (x + zeroStar (Fin.last n) a)‖ ≤ rho) ↔
      (‖iidCircularTransposeLinearForm
        (edgeCofactor ((lastVertexSplit n x).1 + b))
        ((lastVertexSplit n x).2 + 0) - 0‖ ≤ rho)
    rw [edgeHafnian_add_zeroStar_last]
    simp [b]
  change edgeGaussian (Fin (n + 1)) Tleft ≤
    edgeGaussian (Fin (n + 1)) Tright
  rw [hpreLeft, hpreRight,
    (measurePreserving_lastVertexSplit n).measure_preimage
      hSleft.nullMeasurableSet,
    (measurePreserving_lastVertexSplit n).measure_preimage
      hSright.nullMeasurableSet]
  exact measure_shiftedStarBall_le b c w rho hrho

theorem edgeHafnian_shifted_ball_reindex
    {ι κ : Type*} [Fintype ι] [LinearOrder ι]
    [Fintype κ] [LinearOrder κ]
    (e : ι ≃ κ) (a : Edge κ → ℂ) (w : ℂ) (rho : ℝ) :
    edgeGaussian ι
        {x | ‖edgeHafnian (x + restrictEdges e.toEmbedding a) - w‖ ≤ rho} =
      edgeGaussian κ {x | ‖edgeHafnian (x + a) - w‖ ≤ rho} := by
  have hset : MeasurableSet {x : Edge ι → ℂ |
      ‖edgeHafnian (x + restrictEdges e.toEmbedding a) - w‖ ≤ rho} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [← (measurePreserving_restrictEdges e.toEmbedding).map_eq,
    Measure.map_apply (measurable_restrictEdges e.toEmbedding) hset]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [← restrictEdges_add, edgeHafnian_restrict_equiv]

/-- Centered-ball comparison for any complete vertex star. -/
theorem edgeHafnian_ball_le_zeroStar {m : ℕ}
    (v : Fin m) (a : Edge (Fin m) → ℂ) (w : ℂ)
    (rho : ℝ) (hrho : 0 ≤ rho) :
    edgeGaussian (Fin m) {x | ‖edgeHafnian (x + a) - w‖ ≤ rho} ≤
      edgeGaussian (Fin m)
        {x | ‖edgeHafnian (x + zeroStar v a)‖ ≤ rho} := by
  classical
  cases m with
  | zero => exact Fin.elim0 v
  | succ n =>
      let e := Equiv.swap v (Fin.last n)
      have hzero : restrictEdges e.toEmbedding (zeroStar v a) =
          zeroStar (Fin.last n) (restrictEdges e.toEmbedding a) := by
        simpa only [e, Equiv.swap_apply_right] using
          restrictEdges_zeroStar_equiv e (Fin.last n) a
      calc
        _ = edgeGaussian (Fin (n + 1))
            {x | ‖edgeHafnian
              (x + restrictEdges e.toEmbedding a) - w‖ ≤ rho} :=
          (edgeHafnian_shifted_ball_reindex e a w rho).symm
        _ ≤ edgeGaussian (Fin (n + 1))
            {x | ‖edgeHafnian
              (x + zeroStar (Fin.last n)
                (restrictEdges e.toEmbedding a))‖ ≤ rho} :=
          edgeHafnian_ball_le_zeroStar_last n
            (restrictEdges e.toEmbedding a) w rho hrho
        _ = _ := by
          rw [← hzero]
          simpa only [sub_zero] using
            edgeHafnian_shifted_ball_reindex e (zeroStar v a) 0 rho

/-- Center any finite set of complete vertex stars in the actual edge law. -/
theorem edgeHafnian_ball_le_zeroVertices {m : ℕ}
    (vs : Finset (Fin m)) (a : Edge (Fin m) → ℂ)
    (rho : ℝ) (hrho : 0 ≤ rho) :
    edgeGaussian (Fin m) {x | ‖edgeHafnian (x + a)‖ ≤ rho} ≤
      edgeGaussian (Fin m)
        {x | ‖edgeHafnian (x + zeroVertices vs a)‖ ≤ rho} := by
  classical
  induction vs using Finset.induction_on with
  | empty => simp
  | @insert v vs hv ih =>
      calc
        _ ≤ edgeGaussian (Fin m)
            {x | ‖edgeHafnian (x + zeroVertices vs a)‖ ≤ rho} := ih
        _ ≤ edgeGaussian (Fin m)
            {x | ‖edgeHafnian
              (x + zeroStar v (zeroVertices vs a))‖ ≤ rho} := by
          simpa using edgeHafnian_ball_le_zeroStar v
            (zeroVertices vs a) 0 rho hrho
        _ = _ := by rw [zeroVertices_insert]

/-- Every deterministic edge shift and output center has no larger ball
probability than the centered Gaussian hafnian. -/
theorem deterministicShift_edgeHafnian_ball_le
    (m : ℕ) (hm : 0 < m) (a : Edge (Fin m) → ℂ)
    (w : ℂ) (rho : ℝ) (hrho : 0 ≤ rho) :
    edgeGaussian (Fin m) {x | ‖edgeHafnian (x + a) - w‖ ≤ rho} ≤
      edgeGaussian (Fin m) {x | ‖edgeHafnian x‖ ≤ rho} := by
  let v : Fin m := ⟨0, hm⟩
  calc
    _ ≤ edgeGaussian (Fin m)
        {x | ‖edgeHafnian (x + zeroStar v a)‖ ≤ rho} :=
      edgeHafnian_ball_le_zeroStar v a w rho hrho
    _ ≤ edgeGaussian (Fin m)
        {x | ‖edgeHafnian
          (x + zeroVertices Finset.univ (zeroStar v a))‖ ≤ rho} :=
      edgeHafnian_ball_le_zeroVertices Finset.univ (zeroStar v a) rho hrho
    _ = _ := by simp

/-- Arbitrary independent edge perturbations obey the exact centered-ball
comparison at unit Gaussian noise scale. -/
theorem independentShift_edgeHafnian_ball_le
    (m : ℕ) (hm : 0 < m)
    (nu : Measure (Edge (Fin m) → ℂ)) [IsProbabilityMeasure nu]
    (w : ℂ) (rho : ℝ) (hrho : 0 ≤ rho) :
    ((edgeGaussian (Fin m)).prod nu)
        {p | ‖edgeHafnian (p.1 + p.2) - w‖ ≤ rho} ≤
      edgeGaussian (Fin m) {x | ‖edgeHafnian x‖ ≤ rho} := by
  let S : Set ((Edge (Fin m) → ℂ) × (Edge (Fin m) → ℂ)) :=
    {p | ‖edgeHafnian (p.1 + p.2) - w‖ ≤ rho}
  have hadd : Measurable (fun p :
      (Edge (Fin m) → ℂ) × (Edge (Fin m) → ℂ) ↦ p.1 + p.2) := by
    fun_prop
  have hS : MeasurableSet S := by
    exact measurableSet_le
      ((measurable_edgeHafnian.comp hadd).sub_const w).norm measurable_const
  rw [show ((edgeGaussian (Fin m)).prod nu)
      {p | ‖edgeHafnian (p.1 + p.2) - w‖ ≤ rho} =
        ((edgeGaussian (Fin m)).prod nu) S by rfl,
    Measure.prod_apply_symm hS]
  calc
    (∫⁻ a, edgeGaussian (Fin m) (Prod.swap ∘ Prod.mk a ⁻¹' S) ∂nu) ≤
        ∫⁻ _a, edgeGaussian (Fin m) {x | ‖edgeHafnian x‖ ≤ rho} ∂nu := by
      apply lintegral_mono
      intro a
      change edgeGaussian (Fin m)
          {x | ‖edgeHafnian (x + a) - w‖ ≤ rho} ≤ _
      exact deterministicShift_edgeHafnian_ball_le m hm a w rho hrho
    _ = edgeGaussian (Fin m) {x | ‖edgeHafnian x‖ ≤ rho} := by simp

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian

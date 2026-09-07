import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16AmbientDensity
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-!
# H16: measurable interior exhaustion and zero-off-support jets

This module records the concrete objects used by the direct integration by
parts route.  It does not assume a Sobolev zero-extension theorem.  The sets
`h16COEInteriorExhaustion N K q` stay a positive determinant distance from
the moving boundary and increase to the entire open COE support.
-/

open MeasureTheory
open scoped ComplexOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- The base determinant is a measurable real-valued function of the scaled
matrix. -/
theorem measurable_concreteCOEBaseDeterminant (N K : ℕ) :
    Measurable (concreteCOEBaseDeterminant (N := N) K) := by
  letI : OpensMeasurableSpace (ConcreteMatrixState N) :=
    Pi.opensMeasurableSpace
  have hden : Continuous (fun C : ConcreteMatrixState N ↦
      1 - C.conjTranspose * C) :=
    continuous_const.sub
      (continuous_id.matrix_conjTranspose.matrix_mul continuous_id)
  have hdetComplex : Measurable (fun C : ConcreteMatrixState N ↦
      Matrix.det (1 - C.conjTranspose * C)) :=
    hden.matrix_det.measurable
  exact Complex.measurable_re.comp
    (hdetComplex.comp (measurable_unscaleCOECorner N K))

/-- A countable interior exhaustion.  On its `q`th member the determinant is
larger than `1/(q+1)`, so all inverse-denominator expressions are classical
smooth functions there. -/
def h16COEInteriorExhaustion (N K q : ℕ) :
    Set (ConcreteMatrixState N) :=
  {A | coeCornerSupport (unscaleCOECorner K A) ∧
    1 / ((q + 1 : ℕ) : ℝ) < concreteCOEBaseDeterminant K A}

theorem measurableSet_h16COEInteriorExhaustion (N K q : ℕ) :
    MeasurableSet (h16COEInteriorExhaustion N K q) := by
  exact ((measurableSet_coeCornerSupport N).preimage
    (measurable_unscaleCOECorner N K)).inter
      (measurableSet_lt measurable_const
        (measurable_concreteCOEBaseDeterminant N K))

/-- The determinant cutoffs form an increasing exhaustion. -/
theorem h16COEInteriorExhaustion_mono
    {N K q q' : ℕ} (hqq' : q ≤ q') :
    h16COEInteriorExhaustion N K q ⊆
      h16COEInteriorExhaustion N K q' := by
  intro A hA
  refine ⟨hA.1, ?_⟩
  have hden : (((q + 1 : ℕ) : ℝ)) ≤ ((q' + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right hqq' 1
  have hpos : 0 < (((q + 1 : ℕ) : ℝ)) := by positivity
  exact (one_div_le_one_div_of_le hpos hden).trans_lt hA.2

/-- The determinant cutoffs exhaust exactly the open COE support. -/
theorem iUnion_h16COEInteriorExhaustion (N K : ℕ) :
    (⋃ q : ℕ, h16COEInteriorExhaustion N K q) =
      {A | coeCornerSupport (unscaleCOECorner K A)} := by
  classical
  ext A
  constructor
  · intro hA
    rcases Set.mem_iUnion.mp hA with ⟨q, hq⟩
    exact hq.1
  · intro hsupport
    have hdetComplex :
        0 < Matrix.det
          (1 - (unscaleCOECorner K A).conjTranspose *
            unscaleCOECorner K A) := hsupport.det_pos
    have hdetReal :
        0 < (Matrix.det
          (1 - (unscaleCOECorner K A).conjTranspose *
            unscaleCOECorner K A)).re := by
      exact (RCLike.lt_iff_re_im.mp hdetComplex).1
    have hbase : 0 < concreteCOEBaseDeterminant K A := by
      exact hdetReal
    rcases exists_nat_one_div_lt hbase with ⟨q, hq⟩
    refine Set.mem_iUnion.2 ⟨q, ⟨hsupport, ?_⟩⟩
    simpa only [Nat.cast_add, Nat.cast_one] using hq

/-! ## The same exhaustion in the moving common ambient space -/

/-- Pull the determinant cutoff back by the inverse centered flow. -/
def h16MovingCOEInteriorExhaustion
    (N K : ℕ) (v : ComplexUnitSphere N) (t : ℝ) (q : ℕ) :
    Set (ConcreteMatrixState N) :=
  transposeCongruenceFlow
      (concreteCenteredOrbitalDirection N v) (-t) ⁻¹'
    h16COEInteriorExhaustion N K q

theorem measurableSet_h16MovingCOEInteriorExhaustion
    (N K : ℕ) (v : ComplexUnitSphere N) (t : ℝ) (q : ℕ) :
    MeasurableSet (h16MovingCOEInteriorExhaustion N K v t q) := by
  exact (measurableSet_h16COEInteriorExhaustion N K q).preimage
    (measurable_transposeCongruence _)

theorem h16MovingCOEInteriorExhaustion_mono
    {N K q q' : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (hqq' : q ≤ q') :
    h16MovingCOEInteriorExhaustion N K v t q ⊆
      h16MovingCOEInteriorExhaustion N K v t q' :=
  Set.preimage_mono (h16COEInteriorExhaustion_mono hqq')

/-- The moving cutoffs exhaust exactly the inverse-flow open support used by
the zero-extended density representatives. -/
theorem iUnion_h16MovingCOEInteriorExhaustion
    (N K : ℕ) (v : ComplexUnitSphere N) (t : ℝ) :
    (⋃ q : ℕ, h16MovingCOEInteriorExhaustion N K v t q) =
      {A | coeCornerSupport
        (unscaleCOECorner K
          (transposeCongruenceFlow
            (concreteCenteredOrbitalDirection N v) (-t) A))} := by
  unfold h16MovingCOEInteriorExhaustion
  rw [← Set.preimage_iUnion]
  rw [iUnion_h16COEInteriorExhaustion]
  rfl

/-- The explicit density jet used in the ambient argument.  It agrees with
the literal score on the open support after multiplication by the base
density, and is definitionally zero off support.  Its measurability and `L1`
regularity are proved by the boundary-exhaustion estimates, not postulated in
this definition. -/
def h16ZeroExtendedCenteredDensityJetReal
    (r N K : ℕ) (v : ComplexUnitSphere N)
    (A : ConcreteMatrixState N) : ℝ := by
  classical
  exact if coeCornerSupport (unscaleCOECorner K A) then
      h16ScaledZeroExtendedDeterminantWeightReal N K A *
        concreteCenteredDensityScore r N K v A
    else 0

@[simp]
theorem h16ZeroExtendedCenteredDensityJetReal_of_support
    {r N K : ℕ} (v : ComplexUnitSphere N)
    (A : ConcreteMatrixState N)
    (hA : coeCornerSupport (unscaleCOECorner K A)) :
    h16ZeroExtendedCenteredDensityJetReal r N K v A =
      h16ScaledZeroExtendedDeterminantWeightReal N K A *
        concreteCenteredDensityScore r N K v A := by
  simp [h16ZeroExtendedCenteredDensityJetReal, hA]

@[simp]
theorem h16ZeroExtendedCenteredDensityJetReal_of_not_support
    {r N K : ℕ} (v : ComplexUnitSphere N)
    (A : ConcreteMatrixState N)
    (hA : ¬coeCornerSupport (unscaleCOECorner K A)) :
    h16ZeroExtendedCenteredDensityJetReal r N K v A = 0 := by
  simp [h16ZeroExtendedCenteredDensityJetReal, hA]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

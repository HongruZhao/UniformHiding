import A4.Target

open Matrix ContinuousLinearMap
open scoped BigOperators Matrix.Norms.Operator

noncomputable section

namespace A4Research

local instance matrixInverseNormedAddCommGroup (d : ℕ) :
    NormedAddCommGroup (MatsumotoPaper.RealMatrix d) := Matrix.linftyOpNormedAddCommGroup
local instance matrixInverseNormedSpace (d : ℕ) :
    NormedSpace ℝ (MatsumotoPaper.RealMatrix d) := Matrix.linftyOpNormedSpace
local instance matrixInverseAddCommGroup (d : ℕ) :
    AddCommGroup (MatsumotoPaper.RealMatrix d) :=
  (matrixInverseNormedAddCommGroup d).toAddCommGroup
local instance matrixInverseModule (d : ℕ) : Module ℝ (MatsumotoPaper.RealMatrix d) :=
  (matrixInverseNormedSpace d).toModule
local instance matrixInversePseudoMetricSpace (d : ℕ) :
    PseudoMetricSpace (MatsumotoPaper.RealMatrix d) :=
  (matrixInverseNormedAddCommGroup d).toPseudoMetricSpace
local instance matrixInverseUniformSpace (d : ℕ) : UniformSpace (MatsumotoPaper.RealMatrix d) :=
  (matrixInversePseudoMetricSpace d).toUniformSpace
local instance matrixInverseTopologicalSpace (d : ℕ) :
    TopologicalSpace (MatsumotoPaper.RealMatrix d) :=
  (matrixInverseUniformSpace d).toTopologicalSpace
local instance matrixInverseNormedRing (d : ℕ) : NormedRing (MatsumotoPaper.RealMatrix d) :=
  Matrix.linftyOpNormedRing
local instance matrixInverseNormedAlgebra (d : ℕ) :
    NormedAlgebra ℝ (MatsumotoPaper.RealMatrix d) := Matrix.linftyOpNormedAlgebra

def inverseEntryFunctional {d : ℕ} (i j : Fin d) :
    MatsumotoPaper.RealMatrix d →L[ℝ] ℝ :=
  (show MatsumotoPaper.RealMatrix d →ₗ[ℝ] ℝ from
    { toFun := fun M ↦ M i j
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }).toContinuousLinearMap

/-- The derivative of the literal nonsingular matrix inverse used by A4. -/
theorem hasFDerivAt_matrixInverse {d : ℕ}
    (S : MatsumotoPaper.RealMatrix d) (hS : IsUnit S.det) :
    HasFDerivAt (fun M : MatsumotoPaper.RealMatrix d ↦ M⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ (MatsumotoPaper.RealMatrix d) S⁻¹ S⁻¹) S := by
  have hUnit : IsUnit S := (Matrix.isUnit_iff_isUnit_det S).mpr hS
  rcases hUnit with ⟨u, rfl⟩
  simpa only [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_invertible,
    Matrix.coe_units_inv] using (hasFDerivAt_ringInverse (𝕜 := ℝ) u)

/-- Exact coordinate derivative on an affine symmetric-matrix line. -/
theorem hasDerivAt_inverseEntry_matrixLine {d : ℕ}
    (S D : MatsumotoPaper.RealMatrix d) (hS : IsUnit S.det) (i j : Fin d) :
    HasDerivAt (fun t : ℝ ↦ (S + t • D)⁻¹ i j)
      (-(S⁻¹ * D * S⁻¹) i j) 0 := by
  have hline : HasDerivAt (fun t : ℝ ↦ S + t • D) D 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).smul_const D).const_add S using 1 <;>
      first | rfl | simp only [one_smul]
  have hinv := (hasFDerivAt_matrixInverse S hS).comp_hasDerivAt_of_eq
    (0 : ℝ) hline (by simp only [zero_smul, add_zero])
  have hentry := (inverseEntryFunctional i j).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hinv
  convert hentry using 1 <;>
    first | rfl | simp [inverseEntryFunctional, ContinuousLinearMap.mulLeftRight_apply]

/-- All degrees of an inverse-entry product obey the literal product-rule
derivative. The lemma has no moment or integration-by-parts assumption. -/
theorem hasDerivAt_prod_inverseEntries_matrixLine {d n : ℕ}
    (S D : MatsumotoPaper.RealMatrix d) (hS : IsUnit S.det)
    (a b : Fin n → Fin d) :
    HasDerivAt (fun t : ℝ ↦ ∏ k : Fin n, (S + t • D)⁻¹ (a k) (b k))
      (∑ k : Fin n, (∏ l ∈ Finset.univ.erase k, S⁻¹ (a l) (b l)) *
        (-(S⁻¹ * D * S⁻¹) (a k) (b k))) 0 := by
  simpa using HasDerivAt.fun_finsetProd
    (fun k (_hk : k ∈ (Finset.univ : Finset (Fin n))) ↦
      hasDerivAt_inverseEntry_matrixLine S D hS (a k) (b k))

/-- The complete inverse contraction from A4 is differentiable in every matrix
direction at a nonsingular matrix. The derivative is its explicit finite
inverse-entry product rule, for arbitrary degree and complex test matrices. -/
theorem hasDerivAt_inverseT_matrixLine {d n : ℕ}
    (S D : MatsumotoPaper.RealMatrix d) (hS : IsUnit S.det)
    (g : Equiv.Perm (Fin (2 * n)))
    (m : Fin n → MatsumotoPaper.ComplexMatrix d) :
    HasDerivAt (fun t : ℝ ↦ MatsumotoPaper.T g (S + t • D)⁻¹ m)
      (∑ j : Fin (2 * n) → Fin d,
        (∏ i : Fin n, m i (j (MatsumotoPaper.leftSlot i))
          (j (MatsumotoPaper.rightSlot i))) *
        ((∑ k : Fin n,
          (∏ l ∈ Finset.univ.erase k, S⁻¹ (j (g (MatsumotoPaper.leftSlot l)))
            (j (g (MatsumotoPaper.rightSlot l)))) *
          (-(S⁻¹ * D * S⁻¹) (j (g (MatsumotoPaper.leftSlot k)))
            (j (g (MatsumotoPaper.rightSlot k)))) : ℝ) : ℂ)) 0 := by
  unfold MatsumotoPaper.T
  apply HasDerivAt.fun_sum
  intro j hj
  have hprod := hasDerivAt_prod_inverseEntries_matrixLine S D hS
    (fun i ↦ j (g (MatsumotoPaper.leftSlot i)))
    (fun i ↦ j (g (MatsumotoPaper.rightSlot i)))
  have hcomplex := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hprod
  convert hcomplex.const_mul (∏ i : Fin n,
    m i (j (MatsumotoPaper.leftSlot i)) (j (MatsumotoPaper.rightSlot i))) using 1 <;>
    first | rfl | simp [Function.comp_def, Complex.ofReal_prod]

end A4Research

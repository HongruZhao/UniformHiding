import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.ConcreteCanonicalMatrixEndpoints

/-!
# Uniform product-matrix hiding from exactly A1--A4

This is the single public Lean entry point for the complete uniformly-hiding
theorem.  It exposes both the existential headline and the theorem at the
fully evaluated universal constant.  All mathematical reductions between the
four cited source inputs and these endpoints are checked by Lean.

The four historical source interfaces A1--A4 are now supplied by proved Lean
packages: `A1.MatrixLawProof`, `A2.WeylIntegrationProof`,
`A3.Proposition12Proof`, and `A4.FullTheorem`. Historical declaration names
are retained for compatibility. Their full contracts and the public theorem
are checked by `FinalHidingAudit` and the imported theorem inventory.

No scientific axiom remains in this endpoint's proof dependencies. The
ordinary foundations `propext`, `Classical.choice`, and `Quot.sound` remain.

-/

namespace LogdetLean.GramHafnian.UltimateHiding

noncomputable section

open DenseLocalStep

/-- The fully evaluated universal coefficient in the A1--A4-only theorem. -/
def uniformlyHidingA1A4OnlyConstant : ℝ :=
  615172

/-- The public constant is definitionally the evaluated canonical constant. -/
theorem uniformlyHidingA1A4OnlyConstant_eq_canonical :
    uniformlyHidingA1A4OnlyConstant =
      concreteCanonicalHidingSquaredConstant := by
  rw [concreteCanonicalHidingSquaredConstant_eq]
  rfl

/-- Complete finite, all-rank uniformly-hiding theorem at the explicit
constant, valid for every `1 ≤ N ≤ K ≤ M` at rate
`min {1, C * N^2 / M}`. -/
theorem uniformlyHidingSquaredAt_A1A4Only :
    UniformProductMatrixHidingSquaredAt
      uniformlyHidingA1A4OnlyConstant := by
  rw [uniformlyHidingA1A4OnlyConstant_eq_canonical]
  exact uniformProductMatrixHidingSquaredAt_concreteCanonical

/-- Numeral-only alias of the complete uniformly-hiding theorem. -/
theorem uniformlyHidingSquaredAt_explicitConstant_A1A4Only :
    UniformProductMatrixHidingSquaredAt
      615172 := by
  exact uniformlyHidingSquaredAt_A1A4Only

/-- Public existential headline: one universal constant gives uniform
transpose-Gram hiding over the entire finite range `1 ≤ N ≤ K ≤ M`. -/
theorem uniformlyHiding_A1A4Only : UniformProductMatrixHidingSquared :=
  ⟨uniformlyHidingA1A4OnlyConstant,
    uniformlyHidingSquaredAt_A1A4Only⟩

end

end LogdetLean.GramHafnian.UltimateHiding

/-! Kernel dependency audit for both public forms. -/
#print axioms LogdetLean.GramHafnian.UltimateHiding.uniformlyHidingSquaredAt_explicitConstant_A1A4Only
#print axioms LogdetLean.GramHafnian.UltimateHiding.uniformlyHiding_A1A4Only

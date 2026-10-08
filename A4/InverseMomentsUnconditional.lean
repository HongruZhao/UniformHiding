import A4.InverseWeingartenVertexRecurrence
import A4.InverseSteinVertexRecurrence
import A4.InverseTensorCongruence
import A4.InverseMomentsFull
import A4.WishartDensityRecursive

open scoped BigOperators Matrix

noncomputable section
namespace A4Research

open MatsumotoPaper InverseStein

/-- Identification of the actual and explicit candidate vertex tensors at
identity scale. Both recurrences are independently proved, at the original
real-shape moment threshold. -/
theorem inverseVertexMomentTensor_identity_formula {d n : ℕ} {beta gamma : ℝ}
    (W : W_d d beta (identityScale d))
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (n : ℝ) - 1 < gamma) :
    inverseVertexMomentTensor W n =
      inverseWeingartenVertexTensor n gamma
        (fun a b ↦ ((identityScale d).1⁻¹ a b : ℂ)) := by
  let A : Fin d → Fin d → ℂ := fun a b ↦ ((identityScale d).1⁻¹ a b : ℂ)
  have hA : ∀ a b, A a b = A b a := by
    intro a b
    exact congrArg Complex.ofReal
      ((Matrix.isHermitian_iff_isSymm.mp (identityScale d).2.inv.isHermitian).apply b a)
  have hactual : InverseVertexRecurrenceThrough n gamma A
      (inverseVertexMomentTensor W) := by
    intro q hq j
    have hqgap : (q : ℝ) < gamma := by
      have hle : (q : ℝ) + 1 ≤ n := by exact_mod_cast hq
      linarith
    exact inverseVertexMomentTensor_recurrence_identity W hgamma hqgap j
  have hzero : inverseVertexMomentTensor W 0 =
      inverseWeingartenVertexTensor 0 gamma A := by
    funext j
    rw [inverseVertexMomentTensor_zero, inverseWeingartenVertexTensor_zero]
  exact inverse_vertex_tensor_family_unique n gamma hgap A
    (inverseVertexMomentTensor W) (fun k ↦ inverseWeingartenVertexTensor k gamma A)
    hzero hactual (inverseWeingartenVertexTensor_recurrenceThrough n gamma hgap A hA)
    n le_rfl

theorem inverseEntryMomentTensor_identity_formula {d n : ℕ} {beta gamma : ℝ}
    (W : W_d d beta (identityScale d))
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (n : ℝ) - 1 < gamma) :
    inverseEntryMomentTensor W n =
      inverseWeingartenEntryTensor gamma
        (fun a b ↦ ((identityScale d).1⁻¹ a b : ℂ)) n := by
  funext x
  have h := congrFun (inverseVertexMomentTensor_identity_formula W hgamma hgap)
    (entryPairListVertices x)
  simpa only [inverseVertexMomentTensor, vertexEntryPairList_vertices,
    inverseWeingartenEntryTensor] using h

/-- The complete inverse-entry tensor formula for every SPD scale, real
shape, and degree satisfying the original moment margin. -/
theorem inverseEntryMomentTensor_formula {d n : ℕ} {beta gamma : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma)
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (n : ℝ) - 1 < gamma) :
    inverseEntryMomentTensor W n =
      inverseWeingartenEntryTensor gamma (fun a b ↦ (sigma.1⁻¹ a b : ℂ)) n := by
  cases n with
  | zero =>
    funext x
    rw [inverseEntryMomentTensor_zero, inverseWeingartenEntryTensor_zero]
  | succ q =>
    have hb : ((d : ℝ) - 1) / 2 < beta := by
      have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
      simp only [Nat.cast_add, Nat.cast_one] at hgap
      linarith
    let W0 : W_d d beta (identityScale d) :=
      recursiveBartlettScaledLaw d beta (identityScale d) hb
    exact inverseEntryMomentTensor_eq_of_identityScale W0 W hgamma hgap
      (inverseEntryMomentTensor_identity_formula W0 hgamma hgap)

end A4Research

namespace MatsumotoPaper

open A4Research

/-- A4's full inverse branch in the literal original canonical-matching
notation, for arbitrary complex test matrices and source permutation. -/
theorem W_d.inverse_matching_moment {d n : ℕ} {beta gamma : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma)
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (n : ℝ) - 1 < gamma)
    (m : Fin n → ComplexMatrix d) (g : Equiv.Perm (Fin (2 * n))) :
    expectation W (fun w ↦ T g (SymPosDef.inverse w).1 m) =
      ∑ N : PerfectMatching n, wgTilde (g⁻¹ * N.toPerm) gamma *
        T N.toPerm (SymPosDef.inverse sigma).1 m := by
  apply W.inverse_matching_moment_of_pairFormula hgamma hgap
  exact inverse_pairFormula_of_standard_tensor W
    (inverseEntryMomentTensor_formula W hgamma hgap)

end MatsumotoPaper

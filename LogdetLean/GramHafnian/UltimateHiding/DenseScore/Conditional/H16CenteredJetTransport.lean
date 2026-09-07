import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16CenteredJetBasic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# H16 literal centered jets are exact flow pullbacks

This module is deterministic.  It proves that every globally zero-extended
literal jet at time `t` is the pullback of its time-zero representative by
the inverse centered coordinate flow.  No integrability, boundary
regularity, H5, or event statement is used.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

theorem h16CenteredCoordinateFlow_neg_add
    {N : ℕ} (v : ComplexUnitSphere N) (s t : ℝ)
    (x : ComplexSymmetricCoordinates N) :
    h16CenteredCoordinateFlow v (-(s + t)) x =
      h16CenteredCoordinateFlow v (-s)
        (h16CenteredCoordinateFlow v (-t) x) := by
  rw [show -(s + t) = -s + -t by ring]
  exact h16CenteredCoordinateFlow_add v (-s) (-t) x

theorem h16CenteredTransportSupport_iff_pullback_zero
    {N : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) :
    x ∈ h16CenteredTransportSupport v t ↔
      h16CenteredCoordinateFlow v (-t) x ∈
        h16CenteredTransportSupport v 0 := by
  simp [h16CenteredTransportSupport]

theorem h16CenteredTransportInteriorDensity_add
    {N K : ℕ} (v : ComplexUnitSphere N) (s t : ℝ)
    (x : ComplexSymmetricCoordinates N) :
    h16CenteredTransportInteriorDensity N K v (t + s) x =
      h16CenteredTransportInteriorDensity N K v s
        (h16CenteredCoordinateFlow v (-t) x) := by
  simp only [h16CenteredTransportInteriorDensity,
    h16CenteredTransportGapDeterminant]
  rw [add_comm t s]
  rw [h16CenteredCoordinateFlow_neg_add v s t x]

theorem h16CenteredTransportInterior_iteratedDeriv_eq_zero_pullback
    {N K : ℕ} (r : ℕ) (v : ComplexUnitSphere N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) :
    iteratedDeriv r
        (fun u : ℝ ↦ h16CenteredTransportInteriorDensity N K v u x) t =
      iteratedDeriv r
        (fun u : ℝ ↦ h16CenteredTransportInteriorDensity N K v u
          (h16CenteredCoordinateFlow v (-t) x)) 0 := by
  let f : ℝ → ℝ := fun u ↦
    h16CenteredTransportInteriorDensity N K v u x
  let g : ℝ → ℝ := fun u ↦
    h16CenteredTransportInteriorDensity N K v u
      (h16CenteredCoordinateFlow v (-t) x)
  have hshift : (fun s : ℝ ↦ f (t + s)) = g := by
    funext s
    exact h16CenteredTransportInteriorDensity_add v s t x
  have htranslate := congrFun (iteratedDeriv_comp_const_add r f t) 0
  rw [hshift] at htranslate
  simpa [f, g] using htranslate.symm

/-- Every literal jet is exactly the inverse-flow pullback of its base jet.
This includes the fourth jet only as its globally chosen zero extension; it
does not assert pointwise differentiability at the moving boundary. -/
theorem h16CenteredTransportJet_eq_zero_pullback
    {N K : ℕ} (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) :
    h16CenteredTransportJet N K r v t x =
      h16CenteredTransportJet N K r v 0
        (h16CenteredCoordinateFlow v (-t) x) := by
  classical
  by_cases hx : x ∈ h16CenteredTransportSupport v t
  · have hy : h16CenteredCoordinateFlow v (-t) x ∈
        h16CenteredTransportSupport v 0 :=
      (h16CenteredTransportSupport_iff_pullback_zero v t x).1 hx
    simp only [h16CenteredTransportJet, hx, hy, if_true]
    exact h16CenteredTransportInterior_iteratedDeriv_eq_zero_pullback
      (r : ℕ) v t x
  · have hy : h16CenteredCoordinateFlow v (-t) x ∉
        h16CenteredTransportSupport v 0 := by
      contrapose! hx
      exact (h16CenteredTransportSupport_iff_pullback_zero v t x).2 hx
    simp [h16CenteredTransportJet, hx, hy]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

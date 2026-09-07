import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCenteredLikelihood
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic

/-!
# Axiom-free coordinate types for the cubic hiding differential

This neutral module contains only the finite-dimensional real coordinate map
and generic symmetric trilinear algebra.  Keeping these definitions below the
concrete cubic-score identification prevents elementary H7 calculus from
importing any of the historical moment branches.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- A symmetric continuous real trilinear form, written in curried form. -/
structure SymmetricRealTrilinearForm (V : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V] where
  form : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ
  swap_first : ∀ x y z, form x y z = form y x z
  swap_last : ∀ x y z, form x y z = form x z y

namespace SymmetricRealTrilinearForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Internal cubic polarization for a symmetric trilinear form. -/
theorem diagonal_add_smul
    (T : SymmetricRealTrilinearForm V) (q i : V) (a : ℝ) :
    T.form (q + a • i) (q + a • i) (q + a • i) =
      T.form q q q + 3 * a * T.form i q q +
        3 * a ^ 2 * T.form i i q + a ^ 3 * T.form i i i := by
  have hqiq : T.form q i q = T.form i q q := T.swap_first q i q
  have hqqi : T.form q q i = T.form i q q := by
    rw [T.swap_last q q i, T.swap_first q i q]
  have hiqi : T.form i q i = T.form i i q := T.swap_last i q i
  have hqii : T.form q i i = T.form i i q := by
    rw [T.swap_first q i i, T.swap_last i q i]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply]
  rw [hqiq, hqqi, hiqi, hqii]
  ring

end SymmetricRealTrilinearForm

/-- Real and imaginary entry coordinates of a complex matrix. -/
abbrev ConcreteMatrixRealCoordinates (N : ℕ) :=
  Fin N → Fin N → Fin 2 → ℝ

def concreteMatrixRealCoordinates {N : ℕ} (A : ConcreteMatrixState N) :
    ConcreteMatrixRealCoordinates N := fun i j b ↦
  if b = 0 then (A i j).re else (A i j).im

theorem concreteMatrixRealCoordinates_add
    {N : ℕ} (A B : ConcreteMatrixState N) :
    concreteMatrixRealCoordinates (A + B) =
      concreteMatrixRealCoordinates A + concreteMatrixRealCoordinates B := by
  ext i j b
  fin_cases b <;> simp [concreteMatrixRealCoordinates]

theorem concreteMatrixRealCoordinates_smul
    {N : ℕ} (a : ℝ) (A : ConcreteMatrixState N) :
    concreteMatrixRealCoordinates (a • A) =
      a • concreteMatrixRealCoordinates A := by
  ext i j b
  fin_cases b <;> simp [concreteMatrixRealCoordinates]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

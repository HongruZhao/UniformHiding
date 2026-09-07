import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16CoordinateJacobianOne
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16CoordinateSupportCompact
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
# Determinant-local jet algebra for H16

This file builds the smooth ambient determinant curve used to control the
literal centered jets.  It contains no integration, Gauss--Green theorem,
H5, event, or endpoint.  In particular, order four is treated only through
the sharp radial factor and is never extended continuously at the boundary.
-/

open NormedSpace
open scoped BigOperators ContDiff

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Rank-one projection formula extended from the unit sphere to its ambient
real Euclidean space. -/
def h16AmbientRankOneProjection (N : ℕ)
    (w : EuclideanSpace ℂ (Fin N)) : ConcreteMatrixState N :=
  fun i j ↦ w i * Complex.conjCLE (w j)

/-- The closed centered orbital factor, with the direction variable extended
to the full ambient Euclidean space. -/
def h16AmbientOrbitalFactor (N : ℕ) (s : ℝ)
    (w : EuclideanSpace ℂ (Fin N)) : ConcreteMatrixState N :=
  (((Real.exp (-s / (N : ℝ)) : ℝ) : ℂ)) •
    (1 + (((Real.exp s - 1 : ℝ) : ℂ)) •
      h16AmbientRankOneProjection N w)

/-- Smooth ambient version of the inverse-flow determinant gap.  Restriction
of `w` to the unit sphere is the literal H16 gap. -/
def h16AmbientTransportGap (N : ℕ) :
    ((EuclideanSpace ℂ (Fin N) × ComplexSymmetricCoordinates N) × ℝ) → ℝ :=
  fun p ↦
    let B := h16AmbientOrbitalFactor N (-p.2) p.1.1
    let C := complexSymmetricMatrixOfCoordinates p.1.2
    let D := B * C * B.transpose
    (Matrix.det (1 - D.conjTranspose * D)).re

theorem h16AmbientRankOneProjection_unitSphere
    {N : ℕ} (v : ComplexUnitSphere N) :
    h16AmbientRankOneProjection N v.1 = complexRankOneProjection v := by
  ext i j
  simp [h16AmbientRankOneProjection, complexRankOneProjection,
    Complex.conjCLE_apply]

theorem h16AmbientOrbitalFactor_unitSphere
    {N : ℕ} (s : ℝ) (v : ComplexUnitSphere N) :
    h16AmbientOrbitalFactor N s v.1 = concreteOrbitalFactor N s v := by
  rw [h16AmbientOrbitalFactor, concreteOrbitalFactor,
    h16AmbientRankOneProjection_unitSphere]

theorem h16CenteredTransportGap_eq_ambient
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) :
    h16CenteredTransportGapDeterminant v t x =
      h16AmbientTransportGap N ((v.1, x), t) := by
  unfold h16CenteredTransportGapDeterminant h16CenteredCoordinateFlow
    h16AmbientTransportGap
  rw [transposeCongruenceFlowCoordinates_matrix]
  rw [transposeCongruenceFlow_centered_eq_concreteOrbitalMatrixUpdate hN]
  rw [h16AmbientOrbitalFactor_unitSphere]
  rfl

/-- All ambient variables enter the determinant curve smoothly over `ℝ`.
This is the source of the uniform finite-dimensional raw-jet bounds. -/
theorem contDiff_h16AmbientTransportGap (N : ℕ) :
    ContDiff ℝ ∞ (h16AmbientTransportGap N) := by
  let M :
      ((EuclideanSpace ℂ (Fin N) × ComplexSymmetricCoordinates N) × ℝ) →
        ConcreteMatrixState N :=
    fun p ↦
      let B := h16AmbientOrbitalFactor N (-p.2) p.1.1
      let C := complexSymmetricMatrixOfCoordinates p.1.2
      let D := B * C * B.transpose
      1 - D.conjTranspose * D
  let f :
      ((EuclideanSpace ℂ (Fin N) × ComplexSymmetricCoordinates N) × ℝ) → ℂ :=
    fun p ↦ Matrix.det (M p)
  have hM : ∀ i j : Fin N, ContDiff ℝ ∞ (fun p ↦ M p i j) := by
    intro i j
    let B :
        ((EuclideanSpace ℂ (Fin N) × ComplexSymmetricCoordinates N) × ℝ) →
          ConcreteMatrixState N :=
      fun p ↦ h16AmbientOrbitalFactor N (-p.2) p.1.1
    let C :
        ((EuclideanSpace ℂ (Fin N) × ComplexSymmetricCoordinates N) × ℝ) →
          ConcreteMatrixState N :=
      fun p ↦ complexSymmetricMatrixOfCoordinates p.1.2
    let D :
        ((EuclideanSpace ℂ (Fin N) × ComplexSymmetricCoordinates N) × ℝ) →
          ConcreteMatrixState N :=
      fun p ↦ B p * C p * (B p).transpose
    have hB : ∀ a b : Fin N, ContDiff ℝ ∞ (fun p ↦ B p a b) := by
      intro a b
      have hsReal : ContDiff ℝ ∞ (fun p :
          ((EuclideanSpace ℂ (Fin N) × ComplexSymmetricCoordinates N) × ℝ) ↦
          Real.exp (-(-p.2) / (N : ℝ))) := by
        fun_prop
      have hs : ContDiff ℝ ∞ (fun p :
          ((EuclideanSpace ℂ (Fin N) × ComplexSymmetricCoordinates N) × ℝ) ↦
          ((Real.exp (-(-p.2) / (N : ℝ)) : ℝ) : ℂ)) := by
        simpa [Function.comp_def] using
          Complex.ofRealCLM.contDiff.comp hsReal
      have hzReal : ContDiff ℝ ∞ (fun p :
          ((EuclideanSpace ℂ (Fin N) × ComplexSymmetricCoordinates N) × ℝ) ↦
          Real.exp (-p.2) - 1) := by
        fun_prop
      have hz : ContDiff ℝ ∞ (fun p :
          ((EuclideanSpace ℂ (Fin N) × ComplexSymmetricCoordinates N) × ℝ) ↦
          ((Real.exp (-p.2) - 1 : ℝ) : ℂ)) := by
        simpa [Function.comp_def] using
          Complex.ofRealCLM.contDiff.comp hzReal
      have hwa : ContDiff ℝ ∞ (fun p :
          ((EuclideanSpace ℂ (Fin N) × ComplexSymmetricCoordinates N) × ℝ) ↦
          p.1.1 a) := by
        fun_prop
      have hwb : ContDiff ℝ ∞ (fun p :
          ((EuclideanSpace ℂ (Fin N) × ComplexSymmetricCoordinates N) × ℝ) ↦
          Complex.conjCLE (p.1.1 b)) := by
        exact Complex.conjCLE.contDiff.comp (by fun_prop)
      have hformula : (fun p ↦ B p a b) = fun p ↦
          ((Real.exp (-(-p.2) / (N : ℝ)) : ℝ) : ℂ) *
            ((if a = b then 1 else 0) +
              ((Real.exp (-p.2) - 1 : ℝ) : ℂ) *
                (p.1.1 a * Complex.conjCLE (p.1.1 b))) := by
        funext p
        by_cases hab : a = b
        · subst b
          simp [B, h16AmbientOrbitalFactor,
            h16AmbientRankOneProjection, Matrix.one_apply,
            Complex.conjCLE_apply, Complex.star_def, smul_eq_mul]
          ring
        · simp [B, h16AmbientOrbitalFactor,
            h16AmbientRankOneProjection, Matrix.one_apply,
            Complex.conjCLE_apply, Complex.star_def, smul_eq_mul, hab]
      rw [hformula]
      exact hs.mul (contDiff_const.add (hz.mul (hwa.mul hwb)))
    have hC : ∀ a b : Fin N, ContDiff ℝ ∞ (fun p ↦ C p a b) := by
      intro a b
      unfold C complexSymmetricMatrixOfCoordinates
      split_ifs <;> fun_prop
    have hBC : ∀ a b : Fin N,
        ContDiff ℝ ∞ (fun p ↦ (B p * C p) a b) := by
      intro a b
      simp only [Matrix.mul_apply]
      exact ContDiff.sum fun k _ ↦ (hB a k).mul (hC k b)
    have hD : ∀ a b : Fin N, ContDiff ℝ ∞ (fun p ↦ D p a b) := by
      intro a b
      unfold D
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      exact ContDiff.sum fun k _ ↦ (hBC a k).mul (hB b k)
    have hconjD : ∀ a b : Fin N,
        ContDiff ℝ ∞ (fun p ↦ star (D p a b)) := by
      intro a b
      have h := Complex.conjCLE.contDiff.comp (hD a b)
      simpa [Function.comp_def, Complex.conjCLE_apply,
        Complex.star_def] using h
    have hgram : ContDiff ℝ ∞
        (fun p ↦ ((D p).conjTranspose * D p) i j) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
      exact ContDiff.sum fun k _ ↦ (hconjD k i).mul (hD k j)
    have hentry : (fun p ↦ M p i j) =
        fun p ↦ (if i = j then 1 else 0) -
          ((D p).conjTranspose * D p) i j := by
      funext p
      rfl
    rw [hentry]
    exact contDiff_const.sub hgram
  have hf : ContDiff ℝ ∞ f := by
    have hprod : ∀ σ : Equiv.Perm (Fin N),
        ContDiff ℝ ∞ (fun p ↦ ∏ i : Fin N, M p (σ i) i) := by
      intro σ
      classical
      have hprodOn : ∀ s : Finset (Fin N), ContDiff ℝ ∞
          (fun p ↦ ∏ i ∈ s, M p (σ i) i) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simpa using (contDiff_const : ContDiff ℝ ∞
            (fun _ :
              ((EuclideanSpace ℂ (Fin N) × ComplexSymmetricCoordinates N) × ℝ) ↦
                (1 : ℂ)))
        | @insert a s ha ih =>
            simp only [Finset.prod_insert ha]
            exact (hM (σ a) a).mul ih
      simpa using hprodOn Finset.univ
    rw [show f = fun p ↦ ∑ σ : Equiv.Perm (Fin N),
        (↑(↑(Equiv.Perm.sign σ) : ℤ) : ℂ) *
          ∏ i : Fin N, M p (σ i) i by
      funext p
      exact Matrix.det_apply' (M p)]
    exact ContDiff.sum fun σ _ ↦ contDiff_const.mul (hprod σ)
  have hre : ContDiff ℝ ∞ (Complex.reCLM ∘ f) :=
    Complex.reCLM.contDiff.comp hf
  change ContDiff ℝ ∞ (fun p ↦ (f p).re) at hre
  have hgap : h16AmbientTransportGap N = fun p ↦ (f p).re := by
    rfl
  rw [hgap]
  exact hre

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

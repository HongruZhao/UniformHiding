import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DeterminantJetAlgebra
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Real-analytic determinant curves for H16

The centered determinant gap is a finite determinant expression in real
exponentials.  This file upgrades the existing `ContDiff` result to real
analyticity in the flow parameter.  The upgrade is the entry point for an
isolated-zero / finite-order factorization proof of the supported-power FTC,
without any monotonicity hypothesis and without adding a scientific axiom.
-/

open NormedSpace
open scoped BigOperators ContDiff

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- For fixed ambient direction and coordinate state, the H16 determinant gap
is real analytic in the flow parameter. -/
theorem analyticAt_h16AmbientTransportGap_time
    (N : ℕ) (q : EuclideanSpace ℂ (Fin N) × ComplexSymmetricCoordinates N)
    (t : ℝ) :
    AnalyticAt ℝ (fun u : ℝ ↦ h16AmbientTransportGap N (q, u)) t := by
  let B : ℝ → ConcreteMatrixState N :=
    fun u ↦ h16AmbientOrbitalFactor N (-u) q.1
  let C : ConcreteMatrixState N := complexSymmetricMatrixOfCoordinates q.2
  let D : ℝ → ConcreteMatrixState N := fun u ↦ B u * C * (B u).transpose
  let M : ℝ → ConcreteMatrixState N := fun u ↦ 1 - (D u).conjTranspose * D u
  have hB : ∀ a b : Fin N, AnalyticAt ℝ (fun u ↦ B u a b) t := by
    intro a b
    have he1R : AnalyticAt ℝ
        (fun u : ℝ ↦ Real.exp (- -u / (N : ℝ))) t := by
      apply AnalyticAt.rexp'
      fun_prop
    have he1C : AnalyticAt ℝ
        (fun u : ℝ ↦ ((Real.exp (- -u / (N : ℝ)) : ℝ) : ℂ)) t := by
      simpa [Function.comp_def] using
        (Complex.ofRealCLM.analyticAt _).comp he1R
    have he2R : AnalyticAt ℝ
        (fun u : ℝ ↦ Real.exp (-u) - 1) t := by
      exact (AnalyticAt.rexp' (by fun_prop)).sub analyticAt_const
    have he2C : AnalyticAt ℝ
        (fun u : ℝ ↦ ((Real.exp (-u) - 1 : ℝ) : ℂ)) t := by
      simpa [Function.comp_def] using
        (Complex.ofRealCLM.analyticAt _).comp he2R
    have hformula : (fun u ↦ B u a b) = fun u ↦
        ((Real.exp (- -u / (N : ℝ)) : ℝ) : ℂ) *
          ((if a = b then 1 else 0) +
            ((Real.exp (-u) - 1 : ℝ) : ℂ) *
              (q.1 a * Complex.conjCLE (q.1 b))) := by
      funext u
      by_cases hab : a = b
      · subst b
        simp [B, h16AmbientOrbitalFactor, h16AmbientRankOneProjection,
          smul_eq_mul]
        ring
      · simp [B, h16AmbientOrbitalFactor, h16AmbientRankOneProjection,
          smul_eq_mul, hab]
    rw [hformula]
    exact he1C.mul (analyticAt_const.add (he2C.mul analyticAt_const))
  have hBC : ∀ a b : Fin N, AnalyticAt ℝ (fun u ↦ (B u * C) a b) t := by
    intro a b
    simp only [Matrix.mul_apply]
    exact Finset.univ.analyticAt_fun_sum fun k _ ↦ (hB a k).mul analyticAt_const
  have hD : ∀ a b : Fin N, AnalyticAt ℝ (fun u ↦ D u a b) t := by
    intro a b
    unfold D
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.univ.analyticAt_fun_sum fun k _ ↦ (hBC a k).mul (hB b k)
  have hconjD : ∀ a b : Fin N, AnalyticAt ℝ (fun u ↦ star (D u a b)) t := by
    intro a b
    have hc : AnalyticAt ℝ (fun z : ℂ ↦ Complex.conjCLE z) (D t a b) :=
      Complex.conjCLE.analyticAt _
    have hcomp : AnalyticAt ℝ
        ((fun z : ℂ ↦ Complex.conjCLE z) ∘ (fun u : ℝ ↦ D u a b)) t :=
      hc.comp (f := fun u : ℝ ↦ D u a b) (x := t) (hD a b)
    simpa [Function.comp_def, Complex.conjCLE_apply, Complex.star_def] using hcomp
  have hM : ∀ i j : Fin N, AnalyticAt ℝ (fun u ↦ M u i j) t := by
    intro i j
    unfold M
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    exact analyticAt_const.sub
      (Finset.univ.analyticAt_fun_sum fun k _ ↦ (hconjD k i).mul (hD k j))
  have hdet : AnalyticAt ℝ (fun u ↦ Matrix.det (M u)) t := by
    rw [show (fun u ↦ Matrix.det (M u)) = fun u ↦ ∑ σ : Equiv.Perm (Fin N),
        (↑(↑(Equiv.Perm.sign σ) : ℤ) : ℂ) * ∏ i : Fin N, M u (σ i) i by
      funext u
      exact Matrix.det_apply' (M u)]
    exact Finset.univ.analyticAt_fun_sum fun σ _ ↦ analyticAt_const.mul
      (Finset.univ.analyticAt_fun_prod fun i _ ↦ hM (σ i) i)
  have hre : AnalyticAt ℝ (fun u ↦ (Matrix.det (M u)).re) t := by
    have hc : AnalyticAt ℝ (fun z : ℂ ↦ Complex.reCLM z)
        (Matrix.det (M t)) := Complex.reCLM.analyticAt _
    have hcomp : AnalyticAt ℝ
        ((fun z : ℂ ↦ Complex.reCLM z) ∘
          (fun u : ℝ ↦ Matrix.det (M u))) t :=
      hc.comp (f := fun u : ℝ ↦ Matrix.det (M u)) (x := t) hdet
    simpa [Function.comp_def] using hcomp
  simpa [h16AmbientTransportGap, B, C, D, M] using hre

/-- The literal centered determinant gap on a unit-sphere direction is real
analytic in the flow parameter. -/
theorem analyticAt_h16CenteredTransportGapDeterminant
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) (t : ℝ) :
    AnalyticAt ℝ (fun u : ℝ ↦ h16CenteredTransportGapDeterminant v u x) t := by
  have h := analyticAt_h16AmbientTransportGap_time N (v.1, x) t
  apply h.congr
  filter_upwards with u
  exact (h16CenteredTransportGap_eq_ambient hN v u x).symm

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

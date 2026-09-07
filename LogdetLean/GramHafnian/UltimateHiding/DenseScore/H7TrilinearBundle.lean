import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7LocalContDiff
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Bundling the literal H7 third differential

This module contains only generic continuous-multilinear algebra.  It averages
the six argument permutations of the literal third Frechet differential and
curries the result into the exact `SymmetricRealTrilinearForm` required by H7.
-/

open Function
open scoped Matrix

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

private abbrev H7CML (V : Type*) [NormedAddCommGroup V]
    [NormedSpace ℝ V] (n : ℕ) :=
  ContinuousMultilinearMap ℝ (fun _ : Fin n => V) ℝ

section Curry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private noncomputable def h7CurryCML1 :
    H7CML V 1 →L[ℝ] (V →L[ℝ] ℝ) :=
  (continuousMultilinearCurryFin1 ℝ V ℝ).toContinuousLinearEquiv.toContinuousLinearMap

private noncomputable def h7CurryCML2 :
    H7CML V 2 →L[ℝ] (V →L[ℝ] V →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ V (H7CML V 1) (V →L[ℝ] ℝ)
      h7CurryCML1).comp
    ((continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin 2 => V) ℝ).toContinuousLinearEquiv.toContinuousLinearMap)

private noncomputable def h7CurryCML3 (A : H7CML V 3) :
    V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ :=
  h7CurryCML2.comp A.curryLeft

@[simp]
private theorem h7CurryCML3_apply (A : H7CML V 3) (x y z : V) :
    h7CurryCML3 A x y z = A ![x, y, z] := by
  change A (Fin.cons x (Fin.cons y (Fin.snoc 0 z))) = A ![x, y, z]
  congr 1
  funext i
  fin_cases i <;> rfl

end Curry

section Symmetrize

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The six-term average, bundled before currying so continuity and
trilinearity are inherited from the continuous-multilinear-map operations. -/
private noncomputable def h7SymmetrizedThirdCML (D : H7CML V 3) : H7CML V 3 :=
  (6 : ℝ)⁻¹ •
    (D +
      D.domDomCongr (Equiv.swap (1 : Fin 3) (2 : Fin 3)) +
      D.domDomCongr (Equiv.swap (0 : Fin 3) (1 : Fin 3)) +
      D.domDomCongr
        ((Equiv.swap (1 : Fin 3) (2 : Fin 3)).trans
          (Equiv.swap (0 : Fin 3) (1 : Fin 3))) +
      D.domDomCongr
        ((Equiv.swap (0 : Fin 3) (1 : Fin 3)).trans
          (Equiv.swap (1 : Fin 3) (2 : Fin 3))) +
      D.domDomCongr (Equiv.swap (0 : Fin 3) (2 : Fin 3)))

private theorem h7SymmetrizedThirdCML_apply
    (D : H7CML V 3) (x y z : V) :
    h7SymmetrizedThirdCML D ![x, y, z] =
      h16SymmetrizedThirdFrechetValue D x y z := by
  have h12 :
      (fun i => ![x, y, z] ((Equiv.swap (1 : Fin 3) (2 : Fin 3)) i)) =
        ![x, z, y] := by
    funext i
    fin_cases i <;> rfl
  have h01 :
      (fun i => ![x, y, z] ((Equiv.swap (0 : Fin 3) (1 : Fin 3)) i)) =
        ![y, x, z] := by
    funext i
    fin_cases i <;> rfl
  have h1201 :
      (fun i => ![x, y, z]
        (((Equiv.swap (1 : Fin 3) (2 : Fin 3)).trans
          (Equiv.swap (0 : Fin 3) (1 : Fin 3))) i)) = ![y, z, x] := by
    funext i
    fin_cases i <;> rfl
  have h0112 :
      (fun i => ![x, y, z]
        (((Equiv.swap (0 : Fin 3) (1 : Fin 3)).trans
          (Equiv.swap (1 : Fin 3) (2 : Fin 3))) i)) = ![z, x, y] := by
    funext i
    fin_cases i <;> rfl
  have h02 :
      (fun i => ![x, y, z] ((Equiv.swap (0 : Fin 3) (2 : Fin 3)) i)) =
        ![z, y, x] := by
    funext i
    fin_cases i <;> rfl
  unfold h7SymmetrizedThirdCML h16SymmetrizedThirdFrechetValue
  simp only [ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul,
    ContinuousMultilinearMap.domDomCongr_apply, h12, h01, h1201, h0112, h02]
  ring

end Symmetrize

/-- Exact symmetric form obtained from the literal real-coordinate third
Frechet differential. -/
noncomputable def h7CoordinateDifferential {N : ℕ} (K : ℕ)
    (A : ConcreteMatrixState N) :
    SymmetricRealTrilinearForm (ConcreteMatrixRealCoordinates N) where
  form := h7CurryCML3 <|
    h7SymmetrizedThirdCML (h16CoordinateThirdFrechetDifferential K A)
  swap_first := by
    intro x y z
    simp only [h7CurryCML3_apply, h7SymmetrizedThirdCML_apply]
    exact h16SymmetrizedThirdFrechetValue_swap_first _ _ _ _
  swap_last := by
    intro x y z
    simp only [h7CurryCML3_apply, h7SymmetrizedThirdCML_apply]
    exact h16SymmetrizedThirdFrechetValue_swap_last _ _ _ _

@[simp]
theorem h7CoordinateDifferential_apply {N K : ℕ}
    (A : ConcreteMatrixState N)
    (x y z : ConcreteMatrixRealCoordinates N) :
    (h7CoordinateDifferential K A).form x y z =
      h16CoordinateCubicValue K A x y z := by
  simp [h7CoordinateDifferential, h16CoordinateCubicValue,
    h7CurryCML3_apply, h7SymmetrizedThirdCML_apply]

/-- The bundled form has the locally justified line diagonal on every
supported state. -/
theorem h7CoordinateDifferential_diagonal_eq_iteratedDeriv
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport
      (unscaleCOECorner K A))
    (x : ConcreteMatrixRealCoordinates N) :
    (h7CoordinateDifferential K A).form x x x =
      iteratedDeriv 3
        (fun t : ℝ => h16CoordinateLikelihoodCore K A (t • x)) 0 := by
  rw [h7CoordinateDifferential_apply]
  exact h16CoordinateCubicValue_diagonal_eq_iteratedDeriv_local A hsupport x

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

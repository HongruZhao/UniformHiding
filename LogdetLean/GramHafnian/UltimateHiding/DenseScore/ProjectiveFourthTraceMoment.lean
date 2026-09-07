import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ProjectiveThirdTraceMoment
import Mathlib.Tactic

/-!
# Exact fourth complex-projective trace moment

This file derives the fourth trace contraction from the internally proved
order-four complex-projective tensor identity.  The final numerator is
the five-partition trace polynomial

`(Tr A)^4 + 6 (Tr A)^2 Tr(A^2) + 3 Tr(A^2)^2 +
  8 Tr A Tr(A^3) + 6 Tr(A^4)`.

No fourth-score, moment bound, total-variation, or hiding statement is an
input.
-/

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

private def permFourS0 : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 1

private def permFourS1 : Equiv.Perm (Fin 4) :=
  Equiv.swap (1 : Fin 4) 2

private def permFourS2 : Equiv.Perm (Fin 4) :=
  Equiv.swap (2 : Fin 4) 3

private def permFour0 : Equiv.Perm (Fin 4) := 1
private def permFour1 : Equiv.Perm (Fin 4) := permFourS0
private def permFour2 : Equiv.Perm (Fin 4) := permFourS1
private def permFour3 : Equiv.Perm (Fin 4) := permFourS2
private def permFour4 : Equiv.Perm (Fin 4) := permFourS0 |>.trans permFourS1
private def permFour5 : Equiv.Perm (Fin 4) := permFourS0 |>.trans permFourS2
private def permFour6 : Equiv.Perm (Fin 4) := permFourS1 |>.trans permFourS0
private def permFour7 : Equiv.Perm (Fin 4) := permFourS1 |>.trans permFourS2
private def permFour8 : Equiv.Perm (Fin 4) := permFourS2 |>.trans permFourS1
private def permFour9 : Equiv.Perm (Fin 4) :=
  (permFourS0 |>.trans permFourS1) |>.trans permFourS0
private def permFour10 : Equiv.Perm (Fin 4) :=
  (permFourS0 |>.trans permFourS1) |>.trans permFourS2
private def permFour11 : Equiv.Perm (Fin 4) :=
  (permFourS0 |>.trans permFourS2) |>.trans permFourS1
private def permFour12 : Equiv.Perm (Fin 4) :=
  (permFourS1 |>.trans permFourS0) |>.trans permFourS2
private def permFour13 : Equiv.Perm (Fin 4) :=
  (permFourS1 |>.trans permFourS2) |>.trans permFourS1
private def permFour14 : Equiv.Perm (Fin 4) :=
  (permFourS2 |>.trans permFourS1) |>.trans permFourS0
private def permFour15 : Equiv.Perm (Fin 4) :=
  ((permFourS0 |>.trans permFourS1) |>.trans permFourS0) |>.trans permFourS2
private def permFour16 : Equiv.Perm (Fin 4) :=
  ((permFourS0 |>.trans permFourS1) |>.trans permFourS2) |>.trans permFourS1
private def permFour17 : Equiv.Perm (Fin 4) :=
  ((permFourS0 |>.trans permFourS2) |>.trans permFourS1) |>.trans permFourS0
private def permFour18 : Equiv.Perm (Fin 4) :=
  ((permFourS1 |>.trans permFourS0) |>.trans permFourS2) |>.trans permFourS1
private def permFour19 : Equiv.Perm (Fin 4) :=
  ((permFourS1 |>.trans permFourS2) |>.trans permFourS1) |>.trans permFourS0
private def permFour20 : Equiv.Perm (Fin 4) :=
  (((permFourS0 |>.trans permFourS1) |>.trans permFourS0) |>.trans permFourS2)
    |>.trans permFourS1
private def permFour21 : Equiv.Perm (Fin 4) :=
  (((permFourS0 |>.trans permFourS1) |>.trans permFourS2) |>.trans permFourS1)
    |>.trans permFourS0
private def permFour22 : Equiv.Perm (Fin 4) :=
  (((permFourS1 |>.trans permFourS0) |>.trans permFourS2) |>.trans permFourS1)
    |>.trans permFourS0
private def permFour23 : Equiv.Perm (Fin 4) :=
  ((((permFourS0 |>.trans permFourS1) |>.trans permFourS0) |>.trans permFourS2)
    |>.trans permFourS1) |>.trans permFourS0

private theorem sum_toFinset_of_nodup
    {alpha M : Type*} [DecidableEq alpha] [AddCommMonoid M]
    (F : alpha -> M) (l : List alpha) (hl : l.Nodup) :
    (∑ x ∈ l.toFinset, F x) = (l.map F).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.nodup_cons] at hl
      have ha : a ∉ l.toFinset := by simpa using hl.1
      rw [List.toFinset_cons, Finset.sum_insert ha, ih hl.2]
      simp

private theorem sum_perm_fin_four (F : Equiv.Perm (Fin 4) -> ℂ) :
    (∑ pi, F pi) =
      F permFour0 + F permFour1 + F permFour2 + F permFour3 +
      F permFour4 + F permFour5 + F permFour6 + F permFour7 +
      F permFour8 + F permFour9 + F permFour10 + F permFour11 +
      F permFour12 + F permFour13 + F permFour14 + F permFour15 +
      F permFour16 + F permFour17 + F permFour18 + F permFour19 +
      F permFour20 + F permFour21 + F permFour22 + F permFour23 := by
  let perms : List (Equiv.Perm (Fin 4)) :=
    [permFour0, permFour1, permFour2, permFour3, permFour4, permFour5,
      permFour6, permFour7, permFour8, permFour9, permFour10, permFour11,
      permFour12, permFour13, permFour14, permFour15, permFour16, permFour17,
      permFour18, permFour19, permFour20, permFour21, permFour22, permFour23]
  have hnodup : perms.Nodup := by decide
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 4))) = perms.toFinset := by
    decide
  rw [huniv, sum_toFinset_of_nodup F perms hnodup]
  simp only [perms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  ring

/-- For a fixed permutation, the Kronecker constraints determine the second
four-index function uniquely. -/
private theorem sum_projectiveFourthPermutationDelta_fixed
    {N : ℕ} (i : Fin 4 -> Fin N) (pi : Equiv.Perm (Fin 4))
    (A : ConcreteMatrixState N) :
    (∑ j : Fin 4 -> Fin N,
      (∏ a : Fin 4, if i a = j (pi a) then (1 : ℂ) else 0) *
        ∏ a : Fin 4, A (j a) (i a)) =
      ∏ a : Fin 4, A (i (pi.symm a)) (i a) := by
  classical
  let j0 : Fin 4 -> Fin N := fun b => i (pi.symm b)
  rw [Fintype.sum_eq_single j0]
  · simp [j0]
  · intro j hj
    have hne : j ≠ j0 := by simpa [eq_comm] using hj
    have hb : ∃ b, j b ≠ j0 b := by
      by_contra h
      apply hne
      funext b
      exact not_ne_iff.mp (not_exists.mp h b)
    rcases hb with ⟨b, hb⟩
    have hfactor :
        (if i (pi.symm b) = j (pi (pi.symm b)) then (1 : ℂ) else 0) = 0 := by
      rw [pi.apply_symm_apply]
      exact if_neg (Ne.symm hb)
    have hzero :
        (∏ a : Fin 4, if i a = j (pi a) then (1 : ℂ) else 0) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ (pi.symm b)) hfactor
    rw [hzero, zero_mul]

/-- The raw fourth Kronecker contraction, kept as the literal permutation
symmetrizer rather than promoted to a new external atom. -/
private def projectiveFourthPermutationDelta {N : ℕ}
    (i j : Fin 4 -> Fin N) : ℂ :=
  ∑ pi : Equiv.Perm (Fin 4),
    ∏ a : Fin 4, if i a = j (pi a) then (1 : ℂ) else 0

/-- A product of four projective-matrix entries is integrable. -/
theorem integrable_complexRankOneProjection_entry_mul_four
    {N : ℕ} (hN : 1 ≤ N) (i j : Fin 4 -> Fin N) :
    Integrable (fun v : ComplexUnitSphere N ↦
      ∏ a : Fin 4, complexRankOneProjection v (i a) (j a))
      (complexUnitSphereProbabilityMeasure N) := by
  letI : IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  apply (integrable_const (1 : ℝ)).mono
  · exact (Finset.aestronglyMeasurable_fun_prod _ fun a _ ↦
      ((measurable_pi_apply (j a)).comp
        ((measurable_pi_apply (i a)).comp
          (measurable_complexRankOneProjection N))).aestronglyMeasurable)
  · filter_upwards [] with v
    rw [norm_one, norm_prod]
    exact Finset.prod_le_one (fun _ _ ↦ norm_nonneg _)
      (fun a _ ↦ norm_complexRankOneProjection_entry_le_one v (i a) (j a))

/-- Exact fourth entry moment, specialized from the proved low-order
projective tensor identity. -/
theorem integral_complexRankOneProjection_entry_mul_four
    {N : ℕ} (hN : 1 ≤ N) (i j : Fin 4 -> Fin N) :
    (∫ v : ComplexUnitSphere N,
      ∏ a : Fin 4, complexRankOneProjection v (i a) (j a)
      ∂(complexUnitSphereProbabilityMeasure N)) =
      ((((N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2) *
        ((N : ℝ) + 3))⁻¹ : ℝ) : ℂ) *
        projectiveFourthPermutationDelta i j := by
  have h := complexProjectiveTensorMoment_le_four_internal
    (N := N) (r := 4) hN (by norm_num) i j
  simpa [complexProjectiveTensorMomentCoordinate,
    complexProjectiveSymmetrizerCoordinate,
    complexProjectiveRisingFactorial, Fin.prod_univ_four,
    projectiveFourthPermutationDelta] using h

/-! ## The permutation trace contraction -/

/-- A four-coordinate function, used to expose a finite sum over
`Fin 4 -> alpha` as four ordinary finite sums. -/
private def finFourTuple {alpha : Type*} (a b c d : alpha) : Fin 4 -> alpha :=
  fun i => Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d))) i

@[simp] private theorem finFourTuple_zero {alpha : Type*} (a b c d : alpha) :
    finFourTuple a b c d 0 = a := rfl

@[simp] private theorem finFourTuple_one {alpha : Type*} (a b c d : alpha) :
    finFourTuple a b c d 1 = b := rfl

@[simp] private theorem finFourTuple_two {alpha : Type*} (a b c d : alpha) :
    finFourTuple a b c d 2 = c := rfl

@[simp] private theorem finFourTuple_three {alpha : Type*} (a b c d : alpha) :
    finFourTuple a b c d 3 = d := rfl

private def finFourFunctionEquiv (alpha : Type*) :
    (Fin 4 -> alpha) ≃ alpha × alpha × alpha × alpha where
  toFun f := (f 0, f 1, f 2, f 3)
  invFun x := finFourTuple x.1 x.2.1 x.2.2.1 x.2.2.2
  left_inv f := by
    funext i
    fin_cases i <;> rfl
  right_inv x := by
    rcases x with ⟨a, b, c, d⟩
    rfl

private theorem sum_finFourFunction
    {alpha M : Type*} [Fintype alpha] [AddCommMonoid M]
    (F : (Fin 4 -> alpha) -> M) :
    (∑ x, F x) = ∑ a, ∑ b, ∑ c, ∑ d, F (finFourTuple a b c d) := by
  rw [← (finFourFunctionEquiv alpha).symm.sum_comp F]
  simp only [Fintype.sum_prod_type]
  rfl

private theorem sum_four_congr
    {alpha M : Type*} [Fintype alpha] [AddCommMonoid M]
    (f g : alpha -> alpha -> alpha -> alpha -> M)
    (h : ∀ a b c d, f a b c d = g a b c d) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ a, ∑ b, ∑ c, ∑ d, g a b c d := by
  apply Fintype.sum_congr
  intro a
  apply Fintype.sum_congr
  intro b
  apply Fintype.sum_congr
  intro c
  apply Fintype.sum_congr
  intro d
  exact h a b c d

/-- The trace contraction associated with one permutation. -/
private def projectiveFourthCycleTerm {N : ℕ}
    (pi : Equiv.Perm (Fin 4)) (A : ConcreteMatrixState N) : ℂ :=
  ∑ x : Fin 4 -> Fin N, ∏ a : Fin 4, A (x (pi.symm a)) (x a)

/-- Reindexing the four tensor slots conjugates the permutation and leaves
the trace contraction unchanged. -/
private theorem projectiveFourthCycleTerm_conjugate
    {N : ℕ} (sigma pi : Equiv.Perm (Fin 4))
    (A : ConcreteMatrixState N) :
    projectiveFourthCycleTerm (sigma.symm.trans (pi.trans sigma)) A =
      projectiveFourthCycleTerm pi A := by
  let e : (Fin 4 -> Fin N) ≃ (Fin 4 -> Fin N) :=
    { toFun := fun x => x ∘ sigma.symm
      invFun := fun x => x ∘ sigma
      left_inv := by
        intro x
        funext a
        simp [Function.comp_def]
      right_inv := by
        intro x
        funext a
        simp [Function.comp_def] }
  unfold projectiveFourthCycleTerm
  rw [← e.sum_comp]
  apply Fintype.sum_congr
  intro x
  change (∏ a : Fin 4,
      A (x (sigma.symm ((sigma.symm.trans (pi.trans sigma)).symm a)))
        (x (sigma.symm a))) = _
  have hreindex := sigma.symm.prod_comp
    (fun a : Fin 4 => A (x (pi.symm a)) (x a))
  simpa [Equiv.trans_apply] using hreindex

private theorem projectiveFourthCycleTerm_id
    {N : ℕ} (A : ConcreteMatrixState N) :
    projectiveFourthCycleTerm permFour0 A = Matrix.trace A ^ 4 := by
  have hsymm : permFour0.symm = permFour0 := by decide
  unfold projectiveFourthCycleTerm
  rw [hsymm]
  rw [sum_finFourFunction]
  simp [Fin.prod_univ_four, permFour0, finFourTuple_zero,
    finFourTuple_one, finFourTuple_two, finFourTuple_three]
  simp only [Matrix.trace, Matrix.diag_apply, pow_succ, pow_two,
    Finset.sum_mul, Finset.mul_sum]
  apply sum_four_congr
  intros
  ring

private theorem projectiveFourthCycleTerm_transposition
    {N : ℕ} (A : ConcreteMatrixState N) :
    projectiveFourthCycleTerm permFour1 A =
      Matrix.trace A ^ 2 * Matrix.trace (A * A) := by
  unfold projectiveFourthCycleTerm
  rw [sum_finFourFunction]
  simp [Fin.prod_univ_four, permFour1, permFourS0,
    Equiv.swap_apply_def, finFourTuple_zero, finFourTuple_one,
    finFourTuple_two, finFourTuple_three]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    pow_two, Finset.sum_mul, Finset.mul_sum]
  apply sum_four_congr
  intros
  ring

private theorem projectiveFourthCycleTerm_doubleTransposition
    {N : ℕ} (A : ConcreteMatrixState N) :
    projectiveFourthCycleTerm permFour5 A = Matrix.trace (A * A) ^ 2 := by
  unfold projectiveFourthCycleTerm
  rw [sum_finFourFunction]
  simp [Fin.prod_univ_four, permFour5, permFourS0, permFourS2,
    Equiv.trans_apply, Equiv.swap_apply_def, finFourTuple_zero,
    finFourTuple_one, finFourTuple_two, finFourTuple_three]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    pow_two, Finset.sum_mul, Finset.mul_sum]
  apply sum_four_congr
  intros
  ring

private theorem projectiveFourthCycleTerm_threeCycle
    {N : ℕ} (A : ConcreteMatrixState N) :
    projectiveFourthCycleTerm permFour4 A =
      Matrix.trace A * Matrix.trace (A * A * A) := by
  unfold projectiveFourthCycleTerm
  rw [sum_finFourFunction]
  simp [Fin.prod_univ_four, permFour4, permFourS0, permFourS1,
    Equiv.trans_apply, Equiv.swap_apply_def, finFourTuple_zero,
    finFourTuple_one, finFourTuple_two, finFourTuple_three]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum]
  apply sum_four_congr
  intros
  ring

private theorem projectiveFourthCycleTerm_fourCycle
    {N : ℕ} (A : ConcreteMatrixState N) :
    projectiveFourthCycleTerm permFour10 A =
      Matrix.trace (A * A * A * A) := by
  unfold projectiveFourthCycleTerm
  rw [sum_finFourFunction]
  simp [Fin.prod_univ_four, permFour10, permFourS0, permFourS1,
    permFourS2, Equiv.trans_apply, Equiv.swap_apply_def,
    finFourTuple_zero, finFourTuple_one, finFourTuple_two,
    finFourTuple_three]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum]
  apply sum_four_congr
  intros
  ring

/-- Summing the 24 permutation contractions gives the five cycle-type
trace monomials with their exact class sizes `1, 6, 3, 8, 6`. -/
private theorem sum_projectiveFourthCycleTerm
    {N : ℕ} (A : ConcreteMatrixState N) :
    (∑ pi : Equiv.Perm (Fin 4), projectiveFourthCycleTerm pi A) =
      Matrix.trace A ^ 4 +
      6 * (Matrix.trace A ^ 2 * Matrix.trace (A * A)) +
      3 * Matrix.trace (A * A) ^ 2 +
      8 * (Matrix.trace A * Matrix.trace (A * A * A)) +
      6 * Matrix.trace (A * A * A * A) := by
  have h2 : projectiveFourthCycleTerm permFour2 A =
      projectiveFourthCycleTerm permFour1 A := by
    rw [show permFour2 =
      permFour6.symm.trans (permFour1.trans permFour6) by decide,
      projectiveFourthCycleTerm_conjugate]
  have h3 : projectiveFourthCycleTerm permFour3 A =
      projectiveFourthCycleTerm permFour1 A := by
    rw [show permFour3 =
      permFour18.symm.trans (permFour1.trans permFour18) by decide,
      projectiveFourthCycleTerm_conjugate]
  have h6 : projectiveFourthCycleTerm permFour6 A =
      projectiveFourthCycleTerm permFour4 A := by
    rw [show permFour6 =
      permFour1.symm.trans (permFour4.trans permFour1) by decide,
      projectiveFourthCycleTerm_conjugate]
  have h7 : projectiveFourthCycleTerm permFour7 A =
      projectiveFourthCycleTerm permFour4 A := by
    rw [show permFour7 =
      permFour14.symm.trans (permFour4.trans permFour14) by decide,
      projectiveFourthCycleTerm_conjugate]
  have h8 : projectiveFourthCycleTerm permFour8 A =
      projectiveFourthCycleTerm permFour4 A := by
    rw [show permFour8 =
      permFour17.symm.trans (permFour4.trans permFour17) by decide,
      projectiveFourthCycleTerm_conjugate]
  have h9 : projectiveFourthCycleTerm permFour9 A =
      projectiveFourthCycleTerm permFour1 A := by
    rw [show permFour9 =
      permFour2.symm.trans (permFour1.trans permFour2) by decide,
      projectiveFourthCycleTerm_conjugate]
  have h11 : projectiveFourthCycleTerm permFour11 A =
      projectiveFourthCycleTerm permFour10 A := by
    rw [show permFour11 =
      permFour3.symm.trans (permFour10.trans permFour3) by decide,
      projectiveFourthCycleTerm_conjugate]
  have h12 : projectiveFourthCycleTerm permFour12 A =
      projectiveFourthCycleTerm permFour10 A := by
    rw [show permFour12 =
      permFour1.symm.trans (permFour10.trans permFour1) by decide,
      projectiveFourthCycleTerm_conjugate]
  have h13 : projectiveFourthCycleTerm permFour13 A =
      projectiveFourthCycleTerm permFour1 A := by
    rw [show permFour13 =
      permFour12.symm.trans (permFour1.trans permFour12) by decide,
      projectiveFourthCycleTerm_conjugate]
  have h14 : projectiveFourthCycleTerm permFour14 A =
      projectiveFourthCycleTerm permFour10 A := by
    rw [show permFour14 =
      permFour5.symm.trans (permFour10.trans permFour5) by decide,
      projectiveFourthCycleTerm_conjugate]
  have h15 : projectiveFourthCycleTerm permFour15 A =
      projectiveFourthCycleTerm permFour4 A := by
    rw [show permFour15 =
      permFour8.symm.trans (permFour4.trans permFour8) by decide,
      projectiveFourthCycleTerm_conjugate]
  have h16 : projectiveFourthCycleTerm permFour16 A =
      projectiveFourthCycleTerm permFour4 A := by
    rw [show permFour16 =
      permFour3.symm.trans (permFour4.trans permFour3) by decide,
      projectiveFourthCycleTerm_conjugate]
  have h17 : projectiveFourthCycleTerm permFour17 A =
      projectiveFourthCycleTerm permFour4 A := by
    rw [show permFour17 =
      permFour11.symm.trans (permFour4.trans permFour11) by decide,
      projectiveFourthCycleTerm_conjugate]
  have h18 : projectiveFourthCycleTerm permFour18 A =
      projectiveFourthCycleTerm permFour5 A := by
    rw [show permFour18 =
      permFour2.symm.trans (permFour5.trans permFour2) by decide,
      projectiveFourthCycleTerm_conjugate]
  have h19 : projectiveFourthCycleTerm permFour19 A =
      projectiveFourthCycleTerm permFour4 A := by
    rw [show permFour19 =
      permFour5.symm.trans (permFour4.trans permFour5) by decide,
      projectiveFourthCycleTerm_conjugate]
  have h20 : projectiveFourthCycleTerm permFour20 A =
      projectiveFourthCycleTerm permFour10 A := by
    rw [show permFour20 =
      permFour2.symm.trans (permFour10.trans permFour2) by decide,
      projectiveFourthCycleTerm_conjugate]
  have h21 : projectiveFourthCycleTerm permFour21 A =
      projectiveFourthCycleTerm permFour1 A := by
    rw [show permFour21 =
      permFour7.symm.trans (permFour1.trans permFour7) by decide,
      projectiveFourthCycleTerm_conjugate]
  have h22 : projectiveFourthCycleTerm permFour22 A =
      projectiveFourthCycleTerm permFour10 A := by
    rw [show permFour22 =
      permFour6.symm.trans (permFour10.trans permFour6) by decide,
      projectiveFourthCycleTerm_conjugate]
  have h23 : projectiveFourthCycleTerm permFour23 A =
      projectiveFourthCycleTerm permFour5 A := by
    rw [show permFour23 =
      permFour6.symm.trans (permFour5.trans permFour6) by decide,
      projectiveFourthCycleTerm_conjugate]
  rw [sum_perm_fin_four, h2, h3, h6, h7, h8, h9, h11, h12, h13,
    h14, h15, h16, h17, h18, h19, h20, h21, h22, h23,
    projectiveFourthCycleTerm_id,
    projectiveFourthCycleTerm_transposition,
    projectiveFourthCycleTerm_doubleTransposition,
    projectiveFourthCycleTerm_threeCycle,
    projectiveFourthCycleTerm_fourCycle]
  ring

/-- Contracting the raw fourth entry moment against four copies of a matrix
produces the exact five-partition trace polynomial. -/
private theorem sum_projectiveFourthPermutationDelta_same
    {N : ℕ} (d : ℂ) (A : ConcreteMatrixState N) :
    (∑ i : Fin 4 -> Fin N, ∑ j : Fin 4 -> Fin N,
      (d * projectiveFourthPermutationDelta i j) *
        ∏ a : Fin 4, A (j a) (i a)) =
      d * (Matrix.trace A ^ 4 +
        6 * (Matrix.trace A ^ 2 * Matrix.trace (A * A)) +
        3 * Matrix.trace (A * A) ^ 2 +
        8 * (Matrix.trace A * Matrix.trace (A * A * A)) +
        6 * Matrix.trace (A * A * A * A)) := by
  classical
  calc
    (∑ i : Fin 4 -> Fin N, ∑ j : Fin 4 -> Fin N,
      (d * projectiveFourthPermutationDelta i j) *
        ∏ a : Fin 4, A (j a) (i a)) =
        ∑ i : Fin 4 -> Fin N, ∑ pi : Equiv.Perm (Fin 4),
          d * (∑ j : Fin 4 -> Fin N,
            (∏ a : Fin 4, if i a = j (pi a) then (1 : ℂ) else 0) *
              ∏ a : Fin 4, A (j a) (i a)) := by
      unfold projectiveFourthPermutationDelta
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      apply Fintype.sum_congr
      intro i
      rw [Finset.sum_comm]
    _ = ∑ i : Fin 4 -> Fin N, ∑ pi : Equiv.Perm (Fin 4),
          d * ∏ a : Fin 4, A (i (pi.symm a)) (i a) := by
      apply Fintype.sum_congr
      intro i
      apply Fintype.sum_congr
      intro pi
      rw [sum_projectiveFourthPermutationDelta_fixed]
    _ = d * ∑ pi : Equiv.Perm (Fin 4), projectiveFourthCycleTerm pi A := by
      unfold projectiveFourthCycleTerm
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = d * (Matrix.trace A ^ 4 +
        6 * (Matrix.trace A ^ 2 * Matrix.trace (A * A)) +
        3 * Matrix.trace (A * A) ^ 2 +
        8 * (Matrix.trace A * Matrix.trace (A * A * A)) +
        6 * Matrix.trace (A * A * A * A)) := by
      rw [sum_projectiveFourthCycleTerm]

/-- Expanding a fourth power of a trace pairing as the two four-index
function sums used by the tensor contraction. -/
private theorem complexProjectiveTracePair_fourth_eq_sum
    {N : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    complexProjectiveTracePair v A ^ 4 =
      ∑ i : Fin 4 -> Fin N, ∑ j : Fin 4 -> Fin N,
        (∏ a : Fin 4, complexRankOneProjection v (i a) (j a)) *
          ∏ a : Fin 4, A (j a) (i a) := by
  unfold complexProjectiveTracePair
  rw [show (∑ i : Fin N, ∑ j : Fin N,
      complexRankOneProjection v i j * A j i) =
      ∑ ij : Fin N × Fin N,
        complexRankOneProjection v ij.1 ij.2 * A ij.2 ij.1 by
    simp only [Fintype.sum_prod_type]]
  rw [Fintype.sum_pow]
  let e := Equiv.arrowProdEquivProdArrow (Fin 4)
    (fun _ => Fin N) (fun _ => Fin N)
  rw [← e.symm.sum_comp]
  simp only [e, Fintype.sum_prod_type,
    Equiv.arrowProdEquivProdArrow_symm_apply, Finset.prod_mul_distrib]

/-- A fourth power of one projective trace pairing is integrable. -/
theorem integrable_complexProjectiveTracePair_fourth
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N) :
    Integrable (fun v : ComplexUnitSphere N ↦
      complexProjectiveTracePair v A ^ 4)
      (complexUnitSphereProbabilityMeasure N) := by
  rw [show (fun v : ComplexUnitSphere N ↦
      complexProjectiveTracePair v A ^ 4) =
      fun v ↦ ∑ i : Fin 4 -> Fin N, ∑ j : Fin 4 -> Fin N,
        (∏ a : Fin 4, complexRankOneProjection v (i a) (j a)) *
          ∏ a : Fin 4, A (j a) (i a) by
    funext v
    exact complexProjectiveTracePair_fourth_eq_sum v A]
  exact integrable_finsetSum _ fun i _ ↦
    integrable_finsetSum _ fun j _ ↦
      (integrable_complexRankOneProjection_entry_mul_four hN i j).mul_const _

/-- The invariant fourth trace-pairing moment

`E[Tr(P_v A)^4] = ((Tr A)^4 + 6(Tr A)^2 Tr(A^2)
  + 3 Tr(A^2)^2 + 8 Tr A Tr(A^3) + 6 Tr(A^4)) /
  (N(N+1)(N+2)(N+3))`.

This is derived from the internally proved order-four projective tensor
identity and contains no fourth-score or norm estimate. -/
theorem integral_complexProjectiveTracePair_fourth
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N) :
    (∫ v : ComplexUnitSphere N,
      complexProjectiveTracePair v A ^ 4
      ∂(complexUnitSphereProbabilityMeasure N)) =
      ((((N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2) *
        ((N : ℝ) + 3))⁻¹ : ℝ) : ℂ) *
        (Matrix.trace A ^ 4 +
          6 * (Matrix.trace A ^ 2 * Matrix.trace (A * A)) +
          3 * Matrix.trace (A * A) ^ 2 +
          8 * (Matrix.trace A * Matrix.trace (A * A * A)) +
          6 * Matrix.trace (A * A * A * A)) := by
  rw [show (fun v : ComplexUnitSphere N ↦
      complexProjectiveTracePair v A ^ 4) =
      fun v ↦ ∑ i : Fin 4 -> Fin N, ∑ j : Fin 4 -> Fin N,
        (∏ a : Fin 4, complexRankOneProjection v (i a) (j a)) *
          ∏ a : Fin 4, A (j a) (i a) by
    funext v
    exact complexProjectiveTracePair_fourth_eq_sum v A]
  calc
    (∫ v : ComplexUnitSphere N,
      ∑ i : Fin 4 -> Fin N, ∑ j : Fin 4 -> Fin N,
        (∏ a : Fin 4, complexRankOneProjection v (i a) (j a)) *
          ∏ a : Fin 4, A (j a) (i a)
      ∂(complexUnitSphereProbabilityMeasure N)) =
      ∑ i : Fin 4 -> Fin N, ∑ j : Fin 4 -> Fin N,
        ∫ v : ComplexUnitSphere N,
          (∏ a : Fin 4, complexRankOneProjection v (i a) (j a)) *
            ∏ a : Fin 4, A (j a) (i a)
          ∂(complexUnitSphereProbabilityMeasure N) := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum]
        exact fun j _ ↦
          (integrable_complexRankOneProjection_entry_mul_four hN i j).mul_const _
      · exact fun i _ ↦ integrable_finsetSum _ fun j _ ↦
          (integrable_complexRankOneProjection_entry_mul_four hN i j).mul_const _
    _ = ((((N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2) *
        ((N : ℝ) + 3))⁻¹ : ℝ) : ℂ) *
        (Matrix.trace A ^ 4 +
          6 * (Matrix.trace A ^ 2 * Matrix.trace (A * A)) +
          3 * Matrix.trace (A * A) ^ 2 +
          8 * (Matrix.trace A * Matrix.trace (A * A * A)) +
          6 * Matrix.trace (A * A * A * A)) := by
      simp_rw [integral_mul_const,
        integral_complexRankOneProjection_entry_mul_four hN]
      exact sum_projectiveFourthPermutationDelta_same _ A

/-! ## One-dimensional sanity check -/

/-- In projective dimension one, the five cycle-type coefficients add to
`|S₄| = 24`. -/
theorem projectiveFourthTracePolynomial_fin_one (a : ℂ) :
    a ^ 4 + 6 * (a ^ 2 * a ^ 2) + 3 * (a ^ 2) ^ 2 +
      8 * (a * a ^ 3) + 6 * a ^ 4 = 24 * a ^ 4 := by
  ring

/-- The one-dimensional normalization denominator is also `24`, so the
normalized fourth projective moment is exactly `a^4`. -/
theorem projectiveFourthTraceMoment_fin_one (a : ℂ) :
    (((1 : ℂ) * 2 * 3 * 4)⁻¹) *
      (a ^ 4 + 6 * (a ^ 2 * a ^ 2) + 3 * (a ^ 2) ^ 2 +
        8 * (a * a ^ 3) + 6 * a ^ 4) = a ^ 4 := by
  rw [projectiveFourthTracePolynomial_fin_one]
  ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

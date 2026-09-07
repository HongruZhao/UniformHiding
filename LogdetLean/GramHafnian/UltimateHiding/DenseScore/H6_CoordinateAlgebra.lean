import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-!
# H6 coordinate algebra

This module isolates the elementary coordinate change used in the
Takagi--Muirhead beta-prime calculation.  It contains only scalar and
finite-product algebra and measurability facts; it makes no probabilistic or
matrix-density assumption.
-/

open Set

namespace H6CoordinateAlgebra

noncomputable section

/-- The beta-to-beta-prime coordinate change `lambda ↦ lambda / (1-lambda)`. -/
def betaPrimeForward (lambda : ℝ) : ℝ :=
  lambda / (1 - lambda)

/-- The inverse beta-prime-to-beta coordinate change `x ↦ x / (1+x)`. -/
def betaPrimeInverse (x : ℝ) : ℝ :=
  x / (1 + x)

/-- Coordinatewise beta-to-beta-prime transformation. -/
def betaPrimeForwardVector (r : ℕ) (lambda : Fin r → ℝ) : Fin r → ℝ :=
  fun i ↦ betaPrimeForward (lambda i)

/-- Coordinatewise beta-prime-to-beta transformation. -/
def betaPrimeInverseVector (r : ℕ) (x : Fin r → ℝ) : Fin r → ℝ :=
  fun i ↦ betaPrimeInverse (x i)

/-- The open unit cube, expressed coordinatewise. -/
def openUnitCube (r : ℕ) : Set (Fin r → ℝ) :=
  {lambda | ∀ i, lambda i ∈ Ioo (0 : ℝ) 1}

/-- The open positive orthant, expressed coordinatewise. -/
def openPositiveOrthant (r : ℕ) : Set (Fin r → ℝ) :=
  {x | ∀ i, 0 < x i}

theorem measurable_betaPrimeForward : Measurable betaPrimeForward := by
  unfold betaPrimeForward
  fun_prop

theorem measurable_betaPrimeInverse : Measurable betaPrimeInverse := by
  unfold betaPrimeInverse
  fun_prop

theorem measurable_betaPrimeForwardVector (r : ℕ) :
    Measurable (betaPrimeForwardVector r) := by
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact measurable_betaPrimeForward.comp (measurable_pi_apply i)

theorem measurable_betaPrimeInverseVector (r : ℕ) :
    Measurable (betaPrimeInverseVector r) := by
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact measurable_betaPrimeInverse.comp (measurable_pi_apply i)

theorem betaPrimeInverse_forward {lambda : ℝ} (hlambda : lambda ≠ 1) :
    betaPrimeInverse (betaPrimeForward lambda) = lambda := by
  have hden : 1 - lambda ≠ 0 := sub_ne_zero.mpr hlambda.symm
  unfold betaPrimeInverse betaPrimeForward
  field_simp [hden]
  ring

theorem betaPrimeForward_inverse {x : ℝ} (hx : x ≠ -1) :
    betaPrimeForward (betaPrimeInverse x) = x := by
  have hden : 1 + x ≠ 0 := by
    intro h
    apply hx
    linarith
  unfold betaPrimeForward betaPrimeInverse
  field_simp [hden]
  ring

theorem betaPrimeForward_pos_iff {lambda : ℝ} :
    0 < betaPrimeForward lambda ↔ 0 < lambda ∧ lambda < 1 := by
  unfold betaPrimeForward
  constructor
  · intro h
    rcases (div_pos_iff.mp h) with hpos | hneg
    · exact ⟨hpos.1, sub_pos.mp hpos.2⟩
    · exfalso
      linarith [hneg.1, hneg.2]
  · rintro ⟨hlambda0, hlambda1⟩
    exact div_pos hlambda0 (sub_pos.mpr hlambda1)

theorem betaPrimeInverse_mem_Ioo {x : ℝ} (hx : 0 < x) :
    betaPrimeInverse x ∈ Ioo (0 : ℝ) 1 := by
  have hden : 0 < 1 + x := by linarith
  constructor
  · exact div_pos hx hden
  · exact (div_lt_one hden).2 (by linarith)

theorem betaPrimeInverse_mem_Ioo_iff {x : ℝ} :
    betaPrimeInverse x ∈ Ioo (0 : ℝ) 1 ↔ 0 < x := by
  constructor
  · intro h
    have hxne : x ≠ -1 := by
      intro hx
      subst x
      norm_num [betaPrimeInverse] at h
    have hpos : 0 < betaPrimeForward (betaPrimeInverse x) :=
      betaPrimeForward_pos_iff.mpr h
    rwa [betaPrimeForward_inverse hxne] at hpos
  · exact betaPrimeInverse_mem_Ioo

theorem betaPrimeForwardVector_mem_openPositiveOrthant_iff
    {r : ℕ} {lambda : Fin r → ℝ} :
    betaPrimeForwardVector r lambda ∈ openPositiveOrthant r ↔
      lambda ∈ openUnitCube r := by
  simp only [betaPrimeForwardVector, openPositiveOrthant, openUnitCube,
    mem_ofPred_eq, mem_Ioo, betaPrimeForward_pos_iff]

theorem betaPrimeInverseVector_mem_openUnitCube_iff
    {r : ℕ} {x : Fin r → ℝ} :
    betaPrimeInverseVector r x ∈ openUnitCube r ↔
      x ∈ openPositiveOrthant r := by
  simp only [betaPrimeInverseVector, openUnitCube, openPositiveOrthant,
    mem_ofPred_eq, betaPrimeInverse_mem_Ioo_iff]

theorem betaPrimeInverseVector_forwardVector
    {r : ℕ} {lambda : Fin r → ℝ} (hlambda : lambda ∈ openUnitCube r) :
    betaPrimeInverseVector r (betaPrimeForwardVector r lambda) = lambda := by
  funext i
  apply betaPrimeInverse_forward
  have hi := (hlambda i).2
  linarith

theorem betaPrimeForwardVector_inverseVector
    {r : ℕ} {x : Fin r → ℝ} (hx : x ∈ openPositiveOrthant r) :
    betaPrimeForwardVector r (betaPrimeInverseVector r x) = x := by
  funext i
  apply betaPrimeForward_inverse
  have hi := hx i
  linarith

/-- Exact support correspondence for the coordinatewise forward map. -/
theorem betaPrimeForwardVector_image_openUnitCube (r : ℕ) :
    betaPrimeForwardVector r '' openUnitCube r = openPositiveOrthant r := by
  ext x
  constructor
  · rintro ⟨lambda, hlambda, rfl⟩
    exact betaPrimeForwardVector_mem_openPositiveOrthant_iff.mpr hlambda
  · intro hx
    refine ⟨betaPrimeInverseVector r x, ?_, ?_⟩
    · exact betaPrimeInverseVector_mem_openUnitCube_iff.mpr hx
    · exact betaPrimeForwardVector_inverseVector hx

/-- Scalar Jacobian factor for the forward coordinate change. -/
def betaPrimeForwardJacobian (lambda : ℝ) : ℝ :=
  1 / (1 - lambda) ^ 2

/-- Scalar Jacobian factor for the inverse coordinate change. -/
def betaPrimeInverseJacobian (x : ℝ) : ℝ :=
  1 / (1 + x) ^ 2

theorem hasDerivAt_betaPrimeForward {lambda : ℝ} (hlambda : lambda ≠ 1) :
    HasDerivAt betaPrimeForward (betaPrimeForwardJacobian lambda) lambda := by
  have hden : HasDerivAt (fun u : ℝ ↦ 1 - u) (-1) lambda :=
    (hasDerivAt_id lambda).const_sub 1
  have h := (hasDerivAt_id lambda).div hden
    (sub_ne_zero.mpr hlambda.symm)
  apply h.congr_deriv
  unfold betaPrimeForwardJacobian
  field_simp [sub_ne_zero.mpr hlambda.symm]
  simp only [id_eq]
  ring

theorem hasDerivAt_betaPrimeInverse {x : ℝ} (hx : x ≠ -1) :
    HasDerivAt betaPrimeInverse (betaPrimeInverseJacobian x) x := by
  have hden0 : 1 + x ≠ 0 := by
    intro h
    apply hx
    linarith
  have hden : HasDerivAt (fun y : ℝ ↦ 1 + y) 1 x := by
    simpa only [id_eq] using (hasDerivAt_id x).const_add 1
  have h := (hasDerivAt_id x).div hden hden0
  apply h.congr_deriv
  unfold betaPrimeInverseJacobian
  field_simp [hden0]
  simp only [id_eq]
  ring

theorem betaPrimeForwardJacobian_pos {lambda : ℝ}
    (hlambda : lambda ∈ Ioo (0 : ℝ) 1) :
    0 < betaPrimeForwardJacobian lambda := by
  unfold betaPrimeForwardJacobian
  exact one_div_pos.mpr (sq_pos_of_pos (sub_pos.mpr hlambda.2))

theorem betaPrimeInverseJacobian_pos {x : ℝ} (hx : 0 < x) :
    0 < betaPrimeInverseJacobian x := by
  unfold betaPrimeInverseJacobian
  exact one_div_pos.mpr (sq_pos_of_pos (by linarith))

/-- Pairwise-difference identity in the forward coordinates. -/
theorem betaPrimeForward_sub (lambda mu : ℝ)
    (hlambda : lambda ≠ 1) (hmu : mu ≠ 1) :
    betaPrimeForward lambda - betaPrimeForward mu =
      (lambda - mu) / ((1 - lambda) * (1 - mu)) := by
  have hlambdaDen : 1 - lambda ≠ 0 := sub_ne_zero.mpr hlambda.symm
  have hmuDen : 1 - mu ≠ 0 := sub_ne_zero.mpr hmu.symm
  unfold betaPrimeForward
  field_simp [hlambdaDen, hmuDen]
  ring

/-- Pairwise-difference identity after writing beta coordinates as
`x / (1+x)`.  This is the exact Vandermonde transformation used in H6. -/
theorem betaPrimeInverse_sub (x y : ℝ) (hx : x ≠ -1) (hy : y ≠ -1) :
    betaPrimeInverse x - betaPrimeInverse y =
      (x - y) / ((1 + x) * (1 + y)) := by
  have hxDen : 1 + x ≠ 0 := by
    intro h
    apply hx
    linarith
  have hyDen : 1 + y ≠ 0 := by
    intro h
    apply hy
    linarith
  unfold betaPrimeInverse
  field_simp [hxDen, hyDen]
  ring

theorem betaPrimeInverseVector_sub
    {r : ℕ} {x : Fin r → ℝ} (hx : x ∈ openPositiveOrthant r)
    (i j : Fin r) :
    betaPrimeInverseVector r x i - betaPrimeInverseVector r x j =
      (x i - x j) / ((1 + x i) * (1 + x j)) := by
  apply betaPrimeInverse_sub
  · have hi := hx i
    linarith
  · have hj := hx j
    linarith

end

end H6CoordinateAlgebra

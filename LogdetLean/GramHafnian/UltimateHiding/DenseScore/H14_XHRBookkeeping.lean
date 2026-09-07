import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Tactic

/-!
# Explicit `X_H R` bookkeeping for the H14 score estimate

This module replaces an opaque coefficient ledger by the literal four-term
identity used in the score calculation.  It is deterministic normed-ring
algebra and is deliberately independent of the probabilistic traceless-
bracket contract.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-- The exact four-term expression

`X_H R = 2 Ω H R - H R + R conjugate(H)
  + (2/c) R conjugate(H) R† Ω⁻¹ R`.

`Hbar`, `Rdagger`, and `OmegaInv` keep the entrywise conjugate, adjoint, and
inverse operations visible without imposing a particular matrix model on the
pure norm bookkeeping theorem. -/
def h14ExplicitXHRExpression
    {A : Type*} [NormedRing A] [NormedSpace ℝ A]
    (c : ℝ) (Omega H Hbar R Rdagger OmegaInv : A) : A :=
  (2 : ℝ) • (Omega * H * R) - H * R + R * Hbar +
    (2 / c : ℝ) • (R * Hbar * (Rdagger * OmegaInv * R))

theorem h14ExplicitXHRExpression_identity
    {A : Type*} [NormedRing A] [NormedSpace ℝ A]
    (c : ℝ) (Omega H Hbar R Rdagger OmegaInv : A) :
    h14ExplicitXHRExpression c Omega H Hbar R Rdagger OmegaInv =
      (2 : ℝ) • (Omega * H * R) - H * R + R * Hbar +
        (2 / c : ℝ) • (R * Hbar * (Rdagger * OmegaInv * R)) := rfl

/-- Explicit term-by-term proof of the reviewer-requested `4u` estimate.

The assumptions are exactly the four operator-norm facts used after the
identity is established in the concrete matrix model:

* `‖Ω‖ ≤ u`;
* `‖H‖ ≤ 1` and `‖conjugate(H)‖ ≤ 1`;
* `‖R† Ω⁻¹ R‖ ≤ y`;
* `u = 1 + y/c`, with `c > 0` and `y ≥ 0`.

No score moment or probability law occurs here. -/
theorem h14ExplicitXHRExpression_norm_le_four
    {A : Type*} [NormedRing A] [NormedSpace ℝ A]
    {c u y : ℝ} {Omega H Hbar R Rdagger OmegaInv : A}
    (hc : 0 < c) (hy : 0 ≤ y) (hu : u = 1 + y / c)
    (hOmega : ‖Omega‖ ≤ u)
    (hH : ‖H‖ ≤ 1) (hHbar : ‖Hbar‖ ≤ 1)
    (hGram : ‖Rdagger * OmegaInv * R‖ ≤ y) :
    ‖h14ExplicitXHRExpression c Omega H Hbar R Rdagger OmegaInv‖ ≤
      4 * u * ‖R‖ := by
  have hu0 : 0 ≤ u := by
    rw [hu]
    positivity
  let tOne : A := (2 : ℝ) • (Omega * H * R)
  let tTwo : A := H * R
  let tThree : A := R * Hbar
  let tFour : A :=
    (2 / c : ℝ) • (R * Hbar * (Rdagger * OmegaInv * R))
  have hOmegaH : ‖Omega * H‖ ≤ u := by
    calc
      ‖Omega * H‖ ≤ ‖Omega‖ * ‖H‖ := norm_mul_le _ _
      _ ≤ u * 1 := mul_le_mul hOmega hH (norm_nonneg H) hu0
      _ = u := mul_one u
  have hOneCore : ‖Omega * H * R‖ ≤ u * ‖R‖ := by
    calc
      ‖Omega * H * R‖ ≤ ‖Omega * H‖ * ‖R‖ := norm_mul_le _ _
      _ ≤ u * ‖R‖ := mul_le_mul_of_nonneg_right hOmegaH (norm_nonneg R)
  have hOne : ‖tOne‖ ≤ 2 * u * ‖R‖ := by
    dsimp only [tOne]
    rw [norm_smul, Real.norm_eq_abs]
    norm_num
    linarith
  have hTwo : ‖tTwo‖ ≤ ‖R‖ := by
    dsimp only [tTwo]
    calc
      ‖H * R‖ ≤ ‖H‖ * ‖R‖ := norm_mul_le _ _
      _ ≤ 1 * ‖R‖ := mul_le_mul_of_nonneg_right hH (norm_nonneg R)
      _ = ‖R‖ := one_mul _
  have hThree : ‖tThree‖ ≤ ‖R‖ := by
    dsimp only [tThree]
    calc
      ‖R * Hbar‖ ≤ ‖R‖ * ‖Hbar‖ := norm_mul_le _ _
      _ ≤ ‖R‖ * 1 := mul_le_mul_of_nonneg_left hHbar (norm_nonneg R)
      _ = ‖R‖ := mul_one _
  have hFourCore :
      ‖R * Hbar * (Rdagger * OmegaInv * R)‖ ≤ ‖R‖ * y := by
    have hRH : ‖R * Hbar‖ ≤ ‖R‖ := by
      exact hThree
    calc
      ‖R * Hbar * (Rdagger * OmegaInv * R)‖ ≤
          ‖R * Hbar‖ * ‖Rdagger * OmegaInv * R‖ := norm_mul_le _ _
      _ ≤ ‖R‖ * y :=
        mul_le_mul hRH hGram (norm_nonneg _) (norm_nonneg R)
  have hCoef : 0 ≤ 2 / c := by positivity
  have hFour : ‖tFour‖ ≤ 2 * (y / c) * ‖R‖ := by
    dsimp only [tFour]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hCoef]
    calc
      (2 / c) * ‖R * Hbar * (Rdagger * OmegaInv * R)‖ ≤
          (2 / c) * (‖R‖ * y) :=
        mul_le_mul_of_nonneg_left hFourCore hCoef
      _ = 2 * (y / c) * ‖R‖ := by ring
  have hTriangle :
      ‖tOne - tTwo + tThree + tFour‖ ≤
        ‖tOne‖ + ‖tTwo‖ + ‖tThree‖ + ‖tFour‖ := by
    calc
      ‖tOne - tTwo + tThree + tFour‖ ≤
          ‖tOne - tTwo + tThree‖ + ‖tFour‖ := norm_add_le _ _
      _ ≤ (‖tOne - tTwo‖ + ‖tThree‖) + ‖tFour‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ((‖tOne‖ + ‖tTwo‖) + ‖tThree‖) + ‖tFour‖ := by
        gcongr
        exact norm_sub_le _ _
      _ = ‖tOne‖ + ‖tTwo‖ + ‖tThree‖ + ‖tFour‖ := by ring
  unfold h14ExplicitXHRExpression
  change ‖tOne - tTwo + tThree + tFour‖ ≤ 4 * u * ‖R‖
  calc
    ‖tOne - tTwo + tThree + tFour‖ ≤
        ‖tOne‖ + ‖tTwo‖ + ‖tThree‖ + ‖tFour‖ := hTriangle
    _ ≤ 2 * u * ‖R‖ + ‖R‖ + ‖R‖ +
        2 * (y / c) * ‖R‖ := by linarith
    _ = 4 * u * ‖R‖ := by rw [hu]; ring

/-- The same checkable identity gives the manuscript's looser `6u` row. -/
theorem h14ExplicitXHRExpression_norm_le_six
    {A : Type*} [NormedRing A] [NormedSpace ℝ A]
    {c u y : ℝ} {Omega H Hbar R Rdagger OmegaInv : A}
    (hc : 0 < c) (hy : 0 ≤ y) (hu : u = 1 + y / c)
    (hOmega : ‖Omega‖ ≤ u)
    (hH : ‖H‖ ≤ 1) (hHbar : ‖Hbar‖ ≤ 1)
    (hGram : ‖Rdagger * OmegaInv * R‖ ≤ y) :
    ‖h14ExplicitXHRExpression c Omega H Hbar R Rdagger OmegaInv‖ ≤
      6 * u * ‖R‖ := by
  have hFour := h14ExplicitXHRExpression_norm_le_four
    hc hy hu hOmega hH hHbar hGram
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  exact hFour.trans (by
    have hR0 : 0 ≤ ‖R‖ := norm_nonneg R
    nlinarith [mul_nonneg hu0 hR0])

/-- Consumer form: an actual derivative `XHR` inherits the `4u` estimate
from the literal identity, rather than from an opaque coefficient ledger. -/
theorem h14_XHR_norm_le_four_of_explicit_identity
    {A : Type*} [NormedRing A] [NormedSpace ℝ A]
    {c u y : ℝ} {Omega H Hbar R Rdagger OmegaInv XHR : A}
    (hIdentity : XHR =
      h14ExplicitXHRExpression c Omega H Hbar R Rdagger OmegaInv)
    (hc : 0 < c) (hy : 0 ≤ y) (hu : u = 1 + y / c)
    (hOmega : ‖Omega‖ ≤ u)
    (hH : ‖H‖ ≤ 1) (hHbar : ‖Hbar‖ ≤ 1)
    (hGram : ‖Rdagger * OmegaInv * R‖ ≤ y) :
    ‖XHR‖ ≤ 4 * u * ‖R‖ := by
  rw [hIdentity]
  exact h14ExplicitXHRExpression_norm_le_four
    hc hy hu hOmega hH hHbar hGram

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

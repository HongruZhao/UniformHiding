import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Recurrence
import Mathlib.Tactic

/-!
# Finite COE-corner likelihood algebra

This file kernel-checks the finite polynomial identities used by the dense
score argument.  It deliberately does **not** assert the COE corner density,
the Takagi beta-prime representation, or any inverse-Wishart moment estimate.

For a rank-one congruence direction, `x` and `w` denote the two scalar
statistics in the exact likelihood ratio and `c = K - 2 N - 1`.  The four
definitions below are the first four logarithmic derivatives for the fixed
forward convention.  The sign is therefore explicit at the public interface.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-- First logarithmic likelihood derivative in a rank-one direction. -/
def coeRankOneLogScoreOne (c N x : ℝ) : ℝ :=
  2 * (c * x - (N + 1))

/-- Second logarithmic likelihood derivative in a rank-one direction. -/
def coeRankOneLogScoreTwo (c x w : ℝ) : ℝ :=
  -4 * c * (x + x ^ 2 + w)

/-- Third logarithmic likelihood derivative in a rank-one direction. -/
def coeRankOneLogScoreThree (c x w : ℝ) : ℝ :=
  8 * c * (x + 3 * x ^ 2 + 2 * x ^ 3 + 3 * w + 6 * x * w)

/-- Fourth logarithmic likelihood derivative in a rank-one direction.

This is equation (R0) of the reverse audit, included literally rather than
hidden behind an `O(·)` estimate. -/
def coeRankOneLogScoreFour (c x w : ℝ) : ℝ :=
  -16 * c *
    (x + 7 * x ^ 2 + 12 * x ^ 3 + 6 * x ^ 4 +
      (7 + 36 * x + 36 * x ^ 2) * w + 6 * w ^ 2)

/-- The exact fourth rank-one logarithmic score is nonpositive whenever the
COE exponent and the two scalar support statistics are nonnegative. -/
theorem coeRankOneLogScoreFour_nonpos
    {c x w : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (hw : 0 ≤ w) :
    coeRankOneLogScoreFour c x w ≤ 0 := by
  have hpoly : 0 ≤
      x + 7 * x ^ 2 + 12 * x ^ 3 + 6 * x ^ 4 +
        (7 + 36 * x + 36 * x ^ 2) * w + 6 * w ^ 2 := by
    positivity
  unfold coeRankOneLogScoreFour
  exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith) hpoly

/-- Third density Bell polynomial. -/
def densityBellThree (ellOne ellTwo ellThree : ℝ) : ℝ :=
  ellOne ^ 3 + 3 * ellOne * ellTwo + ellThree

/-- Fourth density Bell polynomial. -/
def densityBellFour (ellOne ellTwo ellThree ellFour : ℝ) : ℝ :=
  ellOne ^ 4 + 6 * ellOne ^ 2 * ellTwo + 3 * ellTwo ^ 2 +
    4 * ellOne * ellThree + ellFour

/-- The rank-one third density score. -/
def coeRankOneDensityScoreThree (c N x w : ℝ) : ℝ :=
  densityBellThree
    (coeRankOneLogScoreOne c N x)
    (coeRankOneLogScoreTwo c x w)
    (coeRankOneLogScoreThree c x w)

/-- Exact cancellation of every term containing `w` in the third rank-one
density score:

`L₃(x,w) - L₃(x,0) = 24 c ((N+2)w - (c-2)xw)`.

This is equation (R12).  Taking absolute values before this identity would
lose the projective cancellation needed for the `O(N)` averaged cubic score.
-/
theorem coeRankOneDensityScoreThree_w_cancellation
    (c N x w : ℝ) :
    coeRankOneDensityScoreThree c N x w -
        coeRankOneDensityScoreThree c N x 0 =
      24 * c * ((N + 2) * w - (c - 2) * x * w) := by
  simp only [coeRankOneDensityScoreThree, densityBellThree,
    coeRankOneLogScoreOne, coeRankOneLogScoreTwo,
    coeRankOneLogScoreThree]
  ring

/-- Absolute-value majorant for the fourth Bell polynomial.  This is the
purely algebraic last step turning fixed-degree logarithmic-score moment
bounds into a fourth density-score bound. -/
theorem abs_densityBellFour_le
    (ellOne ellTwo ellThree ellFour : ℝ) :
    |densityBellFour ellOne ellTwo ellThree ellFour| ≤
      |ellOne| ^ 4 + 6 * |ellOne| ^ 2 * |ellTwo| +
        3 * |ellTwo| ^ 2 + 4 * |ellOne| * |ellThree| + |ellFour| := by
  unfold densityBellFour
  let a := ellOne ^ 4
  let b := 6 * ellOne ^ 2 * ellTwo
  let c := 3 * ellTwo ^ 2
  let d := 4 * ellOne * ellThree
  let e := ellFour
  calc
    |ellOne ^ 4 + 6 * ellOne ^ 2 * ellTwo + 3 * ellTwo ^ 2 +
        4 * ellOne * ellThree + ellFour|
        ≤ |a| + |b| + |c| + |d| + |e| := by
          change |(((a + b) + c) + d) + e| ≤
            |a| + |b| + |c| + |d| + |e|
          calc
            |(((a + b) + c) + d) + e| ≤ |((a + b) + c) + d| + |e| :=
              abs_add_le _ _
            _ ≤ (|(a + b) + c| + |d|) + |e| :=
              add_le_add (abs_add_le _ _) le_rfl
            _ ≤ ((|a + b| + |c|) + |d|) + |e| :=
              add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
            _ ≤ (((|a| + |b|) + |c|) + |d|) + |e| :=
              add_le_add (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl) le_rfl
            _ = |a| + |b| + |c| + |d| + |e| := by ring
    _ = |ellOne| ^ 4 + 6 * |ellOne| ^ 2 * |ellTwo| +
          3 * |ellTwo| ^ 2 + 4 * |ellOne| * |ellThree| + |ellFour| := by
      simp only [a, b, c, d, e, abs_pow, abs_mul]
      norm_num

/-- Numerical closure of the fourth-score estimate.  The five hypotheses are
exactly the product moments appearing after applying Hölder to
`abs_densityBellFour_le`; no probabilistic input is smuggled into this lemma.
-/
theorem densityBellFour_term_budget
    {N B : ℝ}
    {tOne tOneTwo tTwo tOneThree tFour : ℝ}
    (hOne : tOne ≤ B * N ^ 2)
    (hOneTwo : tOneTwo ≤ B * N ^ 2)
    (hTwo : tTwo ≤ B * N ^ 2)
    (hOneThree : tOneThree ≤ B * N ^ 2)
    (hFour : tFour ≤ B * N ^ 2) :
    tOne + 6 * tOneTwo + 3 * tTwo + 4 * tOneThree + tFour ≤
      15 * B * N ^ 2 := by
  have h6 := mul_le_mul_of_nonneg_left hOneTwo (by norm_num : (0 : ℝ) ≤ 6)
  have h3 := mul_le_mul_of_nonneg_left hTwo (by norm_num : (0 : ℝ) ≤ 3)
  have h4 := mul_le_mul_of_nonneg_left hOneThree (by norm_num : (0 : ℝ) ≤ 4)
  linarith

/-- Exact centered cubic identity (R25), written in a commutative algebra.
Only the central scalar generator commutes with the rank-one generator in the
analytic application; no false general commutativity claim is needed. -/
theorem centeredProjectiveCubic_identity
    {R : Type*} [Field R]
    (N scalar rankOneSecond rankOneThird centeredSecond : R)
    (hN : N ≠ 0)
    (hcenteredSecond :
      centeredSecond = rankOneSecond - scalar ^ 2 / N ^ 2) :
    rankOneThird - 3 * (scalar / N) * rankOneSecond +
          3 * (scalar ^ 2 / N ^ 2) * (scalar / N) -
          scalar ^ 3 / N ^ 3 =
      rankOneThird - 3 * (scalar / N) * centeredSecond -
          scalar ^ 3 / N ^ 3 := by
  rw [hcenteredSecond]
  field_simp [hN]
  ring

/-- The support exponent `c/2` is strictly larger than three under the clean
integer condition `K ≥ 2N+8`.  This is the boundary-regularity threshold
needed to exclude boundary signed measures through order four. -/
theorem coe_boundary_exponent_gt_three
    {N K : ℕ} (hK : 2 * N + 8 ≤ K) :
    3 < (((K : ℝ) - 2 * (N : ℝ) - 1) / 2) := by
  have hKr : ((2 * N + 8 : ℕ) : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hK
  norm_num [Nat.cast_add, Nat.cast_mul] at hKr
  linarith

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

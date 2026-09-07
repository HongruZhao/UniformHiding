import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ProjectiveContractions
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Tactic

/-!
# Centered trace closure for the quadratic COE score

This file performs the part of (R30)--(R31) which is genuinely specific to
the cancellation in the averaged quadratic score.  The bracket from (R30)
is rewritten as a linear combination of *three primitive centered trace
polynomials*.  Its `L^2` estimate is then proved from corresponding primitive
Wishart moment bounds.

No bound on the final bracket, density score, total variation, or hiding
distance is assumed.  A concrete probabilistic layer supplies the three
standard fixed-degree centered trace estimates.  The mean cancellation is
*not* a Wishart-moment input: it is derived below from zero total mass of the
second density derivative.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-- Coefficient of `Tr Y^2` in the bracket of (R30). -/
def quadraticTraceCoeffTwo (N c : ℝ) : ℝ :=
  1 - (N - 2) / (c * N)

/-- Coefficient of `(Tr Y)^2` in the bracket of (R30). -/
def quadraticTraceCoeffSquare (N c : ℝ) : ℝ :=
  -(1 / N + 1 / c)

/-- Coefficient of `Tr Y` in the bracket of (R30). -/
def quadraticTraceCoeffOne (N : ℝ) : ℝ :=
  -((N - 1) * (N + 2) / N)

/-- The literal bracket in (R30), before multiplication by
`4 / (N (N+1))`. -/
def centeredQuadraticTraceBracket (N c tOne tTwo : ℝ) : ℝ :=
  tTwo - tOne ^ 2 / N - ((N - 1) * (N + 2) / N) * tOne -
    (1 / c) * (tOne ^ 2 + ((N - 2) / N) * tTwo)

/-- Collecting the three coefficients in the bracket of (R30). -/
theorem centeredQuadraticTraceBracket_collect
    {N c tOne tTwo : ℝ} (hN : N ≠ 0) (hc : c ≠ 0) :
    centeredQuadraticTraceBracket N c tOne tTwo =
      quadraticTraceCoeffTwo N c * tTwo +
        quadraticTraceCoeffSquare N c * tOne ^ 2 +
        quadraticTraceCoeffOne N * tOne := by
  simp only [centeredQuadraticTraceBracket, quadraticTraceCoeffTwo,
    quadraticTraceCoeffSquare, quadraticTraceCoeffOne]
  field_simp [hN, hc]
  ring

/-- Exact centering decomposition.  The sole scalar hypothesis is the
fixed-degree Wishart mean identity for the three trace polynomials; the
pointwise cancellation is proved here. -/
theorem centeredQuadraticTraceBracket_eq_centered_components
    {N c tOne tTwo meanOne meanSquare meanTwo : ℝ}
    (hN : N ≠ 0) (hc : c ≠ 0)
    (hmean :
      quadraticTraceCoeffTwo N c * meanTwo +
          quadraticTraceCoeffSquare N c * meanSquare +
          quadraticTraceCoeffOne N * meanOne = 0) :
    centeredQuadraticTraceBracket N c tOne tTwo =
      quadraticTraceCoeffTwo N c * (tTwo - meanTwo) +
        quadraticTraceCoeffSquare N c * (tOne ^ 2 - meanSquare) +
        quadraticTraceCoeffOne N * (tOne - meanOne) := by
  rw [centeredQuadraticTraceBracket_collect hN hc]
  linarith

/-! ## Dimension-explicit coefficient estimates -/

/-- In the dense range `c ≥ N ≥ 1`, the quadratic-trace coefficient is
bounded by two. -/
theorem abs_quadraticTraceCoeffTwo_le_two
    {N c : ℝ} (hN : 1 ≤ N) (hc : N ≤ c) :
    |quadraticTraceCoeffTwo N c| ≤ 2 := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hcpos : 0 < c := hNpos.trans_le hc
  have hNmTwo : |N - 2| ≤ N := by
    rw [abs_le]
    constructor <;> linarith
  have hden : 0 < c * N := mul_pos hcpos hNpos
  have hfrac : |(N - 2) / (c * N)| ≤ 1 := by
    rw [abs_div]
    have hcN : N ≤ c * N := by nlinarith
    have habsden : |c * N| = c * N := abs_of_pos hden
    rw [habsden]
    exact (div_le_one hden).2 (hNmTwo.trans hcN)
  unfold quadraticTraceCoeffTwo
  calc
    |1 - (N - 2) / (c * N)| ≤ |1| + |(N - 2) / (c * N)| :=
      abs_sub _ _
    _ ≤ 2 := by
      norm_num
      linarith [hfrac]

/-- The coefficient of `(Tr Y)^2` carries the essential reciprocal
dimension. -/
theorem abs_quadraticTraceCoeffSquare_le
    {N c : ℝ} (hN : 1 ≤ N) (hc : N ≤ c) :
    |quadraticTraceCoeffSquare N c| ≤ 2 / N := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hcpos : 0 < c := hNpos.trans_le hc
  have hinv : 1 / c ≤ 1 / N := by
    exact one_div_le_one_div_of_le hNpos hc
  unfold quadraticTraceCoeffSquare
  rw [abs_neg, abs_of_nonneg (add_nonneg (by positivity) (by positivity))]
  calc
    1 / N + 1 / c ≤ 1 / N + 1 / N := by
      simpa [add_comm] using add_le_add_left hinv (1 / N)
    _ = 2 / N := by ring

/-- The linear-trace coefficient is at most `3N`. -/
theorem abs_quadraticTraceCoeffOne_le
    {N : ℝ} (hN : 1 ≤ N) :
    |quadraticTraceCoeffOne N| ≤ 3 * N := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hprod : 0 ≤ (N - 1) * (N + 2) := mul_nonneg (by linarith) (by linarith)
  unfold quadraticTraceCoeffOne
  rw [abs_neg, abs_of_nonneg (div_nonneg hprod hNpos.le)]
  apply (div_le_iff₀ hNpos).2
  nlinarith [sq_nonneg (N - 1)]

/-! ## Primitive fixed-Wishart inputs and internal `L²` closure -/

/-- Primitive probabilistic inputs for the (R30) bracket.

The three norm bounds are on the individual centered trace polynomials,
before their COE-score coefficients are applied.  These are the quantities
obtained from Gaussian Poincare plus the fixed inverse-Wishart moments in
(R30a)--(R30b). -/
structure CenteredQuadraticTraceInputs
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (N c COne CSquare CTwo : ℝ)
    (tOne tTwo : Omega → ℝ)
    (meanOne meanSquare meanTwo : ℝ) : Prop where
  trace_one_integrable : Integrable tOne mu
  trace_square_integrable : Integrable (fun ω ↦ tOne ω ^ 2) mu
  trace_two_integrable : Integrable tTwo mu
  mean_one_eq : meanOne = ∫ ω, tOne ω ∂mu
  mean_square_eq : meanSquare = ∫ ω, tOne ω ^ 2 ∂mu
  mean_two_eq : meanTwo = ∫ ω, tTwo ω ∂mu
  /-- This equality is supplied by probability normalization after the
  concrete density-derivative theorem, not by a moment estimate. -/
  bracket_integral_zero :
    (∫ ω, centeredQuadraticTraceBracket N c (tOne ω) (tTwo ω) ∂mu) = 0
  centered_one_memLp :
    MemLp (fun ω ↦ tOne ω - meanOne) 2 mu
  centered_square_memLp :
    MemLp (fun ω ↦ tOne ω ^ 2 - meanSquare) 2 mu
  centered_two_memLp :
    MemLp (fun ω ↦ tTwo ω - meanTwo) 2 mu
  centered_one_lpNorm_le :
    lpNorm (fun ω ↦ tOne ω - meanOne) 2 mu ≤ COne * N
  centered_square_lpNorm_le :
    lpNorm (fun ω ↦ tOne ω ^ 2 - meanSquare) 2 mu ≤ CSquare * N ^ 3
  centered_two_lpNorm_le :
    lpNorm (fun ω ↦ tTwo ω - meanTwo) 2 mu ≤ CTwo * N ^ 2

namespace CenteredQuadraticTraceInputs

variable {Omega : Type*} [MeasurableSpace Omega]
variable {mu : Measure Omega}
variable {N c COne CSquare CTwo meanOne meanSquare meanTwo : ℝ}
variable {tOne tTwo : Omega → ℝ}

/-- The R30 centering identity follows from zero total mass of the second
density derivative and ordinary integral linearity.  It is therefore not an
external Wishart moment assumption. -/
theorem mean_identity
    (hN : N ≠ 0) (hc : c ≠ 0)
    (H : CenteredQuadraticTraceInputs mu N c COne CSquare CTwo
      tOne tTwo meanOne meanSquare meanTwo) :
    quadraticTraceCoeffTwo N c * meanTwo +
        quadraticTraceCoeffSquare N c * meanSquare +
        quadraticTraceCoeffOne N * meanOne = 0 := by
  have hpoint :
      (fun ω ↦ centeredQuadraticTraceBracket N c (tOne ω) (tTwo ω)) =
        (fun ω ↦ quadraticTraceCoeffTwo N c * tTwo ω +
          quadraticTraceCoeffSquare N c * tOne ω ^ 2 +
          quadraticTraceCoeffOne N * tOne ω) := by
    funext ω
    exact centeredQuadraticTraceBracket_collect hN hc
  have hIntegral :
      (∫ ω, centeredQuadraticTraceBracket N c (tOne ω) (tTwo ω) ∂mu) =
        quadraticTraceCoeffTwo N c * (∫ ω, tTwo ω ∂mu) +
          quadraticTraceCoeffSquare N c * (∫ ω, tOne ω ^ 2 ∂mu) +
          quadraticTraceCoeffOne N * (∫ ω, tOne ω ∂mu) := by
    rw [show (∫ ω, centeredQuadraticTraceBracket N c (tOne ω) (tTwo ω) ∂mu) =
        ∫ ω, (quadraticTraceCoeffTwo N c * tTwo ω +
          quadraticTraceCoeffSquare N c * tOne ω ^ 2 +
          quadraticTraceCoeffOne N * tOne ω) ∂mu by rw [hpoint]]
    calc
      (∫ ω, (quadraticTraceCoeffTwo N c * tTwo ω +
          quadraticTraceCoeffSquare N c * tOne ω ^ 2) +
          quadraticTraceCoeffOne N * tOne ω ∂mu) =
        (∫ ω, quadraticTraceCoeffTwo N c * tTwo ω +
          quadraticTraceCoeffSquare N c * tOne ω ^ 2 ∂mu) +
        (∫ ω, quadraticTraceCoeffOne N * tOne ω ∂mu) :=
          integral_add
            ((H.trace_two_integrable.const_mul _).add
              (H.trace_square_integrable.const_mul _))
            (H.trace_one_integrable.const_mul _)
      _ = ((∫ ω, quadraticTraceCoeffTwo N c * tTwo ω ∂mu) +
            (∫ ω, quadraticTraceCoeffSquare N c * tOne ω ^ 2 ∂mu)) +
          (∫ ω, quadraticTraceCoeffOne N * tOne ω ∂mu) := by
            rw [integral_add (H.trace_two_integrable.const_mul _)
              (H.trace_square_integrable.const_mul _)]
      _ = quadraticTraceCoeffTwo N c * (∫ ω, tTwo ω ∂mu) +
          quadraticTraceCoeffSquare N c * (∫ ω, tOne ω ^ 2 ∂mu) +
          quadraticTraceCoeffOne N * (∫ ω, tOne ω ∂mu) := by
            rw [integral_const_mul, integral_const_mul, integral_const_mul]
  rw [H.mean_one_eq, H.mean_square_eq, H.mean_two_eq]
  rw [← hIntegral, H.bracket_integral_zero]

/-- Internal closure of the centered quadratic estimate (R31).  In
particular, the `O(N²)` bracket estimate is a conclusion, not an input. -/
theorem bracket_lpNorm_two_le
    (hN : 1 ≤ N) (hc : N ≤ c)
    (hCOne : 0 ≤ COne) (hCSquare : 0 ≤ CSquare) (hCTwo : 0 ≤ CTwo)
    (H : CenteredQuadraticTraceInputs mu N c COne CSquare CTwo
      tOne tTwo meanOne meanSquare meanTwo) :
    lpNorm (fun ω ↦ centeredQuadraticTraceBracket N c (tOne ω) (tTwo ω))
        2 mu ≤
      (2 * CTwo + 2 * CSquare + 3 * COne) * N ^ 2 := by
  have hN0 : N ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hN)
  have hc0 : c ≠ 0 := ne_of_gt ((lt_of_lt_of_le zero_lt_one hN).trans_le hc)
  let eTwo : Omega → ℝ := fun ω ↦ tTwo ω - meanTwo
  let eSquare : Omega → ℝ := fun ω ↦ tOne ω ^ 2 - meanSquare
  let eOne : Omega → ℝ := fun ω ↦ tOne ω - meanOne
  let a := quadraticTraceCoeffTwo N c
  let b := quadraticTraceCoeffSquare N c
  let d := quadraticTraceCoeffOne N
  have hpoint :
      (fun ω ↦ centeredQuadraticTraceBracket N c (tOne ω) (tTwo ω)) =
        a • eTwo + b • eSquare + d • eOne := by
    funext ω
    change centeredQuadraticTraceBracket N c (tOne ω) (tTwo ω) =
      a * eTwo ω + b * eSquare ω + d * eOne ω
    exact centeredQuadraticTraceBracket_eq_centered_components hN0 hc0
      (H.mean_identity hN0 hc0)
  rw [hpoint]
  have hTwo : MemLp eTwo 2 mu := H.centered_two_memLp
  have hSquare : MemLp eSquare 2 mu := H.centered_square_memLp
  have hOne : MemLp eOne 2 mu := H.centered_one_memLp
  have hab : MemLp (a • eTwo + b • eSquare) 2 mu :=
    (hTwo.const_smul a).add (hSquare.const_smul b)
  have ha : |a| ≤ 2 := by
    simpa [a] using abs_quadraticTraceCoeffTwo_le_two hN hc
  have hb : |b| ≤ 2 / N := by
    simpa [b] using abs_quadraticTraceCoeffSquare_le hN hc
  have hd : |d| ≤ 3 * N := by
    simpa [d] using abs_quadraticTraceCoeffOne_le hN
  have hTwoNorm : lpNorm eTwo 2 mu ≤ CTwo * N ^ 2 := by
    simpa [eTwo] using H.centered_two_lpNorm_le
  have hSquareNorm : lpNorm eSquare 2 mu ≤ CSquare * N ^ 3 := by
    simpa [eSquare] using H.centered_square_lpNorm_le
  have hOneNorm : lpNorm eOne 2 mu ≤ COne * N := by
    simpa [eOne] using H.centered_one_lpNorm_le
  have hTwoProduct : |a| * lpNorm eTwo 2 mu ≤ 2 * (CTwo * N ^ 2) :=
    mul_le_mul ha hTwoNorm lpNorm_nonneg (by norm_num)
  have hSquareProduct : |b| * lpNorm eSquare 2 mu ≤
      (2 / N) * (CSquare * N ^ 3) :=
    mul_le_mul hb hSquareNorm lpNorm_nonneg (by positivity)
  have hOneProduct : |d| * lpNorm eOne 2 mu ≤
      (3 * N) * (COne * N) :=
    mul_le_mul hd hOneNorm lpNorm_nonneg (by positivity)
  calc
    lpNorm (a • eTwo + b • eSquare + d • eOne) 2 mu ≤
        lpNorm (a • eTwo + b • eSquare) 2 mu +
          lpNorm (d • eOne) 2 mu := lpNorm_add_le hab (by norm_num)
    _ ≤ (lpNorm (a • eTwo) 2 mu + lpNorm (b • eSquare) 2 mu) +
          lpNorm (d • eOne) 2 mu := by
      gcongr
      exact lpNorm_add_le (hTwo.const_smul a) (by norm_num)
    _ = |a| * lpNorm eTwo 2 mu + |b| * lpNorm eSquare 2 mu +
          |d| * lpNorm eOne 2 mu := by
      simp only [lpNorm_const_smul]
      change ‖a‖ * lpNorm eTwo 2 mu + ‖b‖ * lpNorm eSquare 2 mu +
          ‖d‖ * lpNorm eOne 2 mu =
        |a| * lpNorm eTwo 2 mu + |b| * lpNorm eSquare 2 mu +
          |d| * lpNorm eOne 2 mu
      simp only [Real.norm_eq_abs]
    _ ≤ 2 * (CTwo * N ^ 2) + (2 / N) * (CSquare * N ^ 3) +
          (3 * N) * (COne * N) := by
      exact add_le_add (add_le_add hTwoProduct hSquareProduct) hOneProduct
    _ = (2 * CTwo + 2 * CSquare + 3 * COne) * N ^ 2 := by
      field_simp [hN0]

/-- After inserting the exact prefactor `4/(N(N+1))`, the averaged
quadratic density score is bounded by a dimension-free constant. -/
theorem normalized_bracket_lpNorm_two_le
    (hN : 1 ≤ N) (hc : N ≤ c)
    (hCOne : 0 ≤ COne) (hCSquare : 0 ≤ CSquare) (hCTwo : 0 ≤ CTwo)
    (H : CenteredQuadraticTraceInputs mu N c COne CSquare CTwo
      tOne tTwo meanOne meanSquare meanTwo) :
    lpNorm (fun ω ↦
        (4 / (N * (N + 1))) *
          centeredQuadraticTraceBracket N c (tOne ω) (tTwo ω)) 2 mu ≤
      4 * (2 * CTwo + 2 * CSquare + 3 * COne) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hNpOne : 0 < N + 1 := by linarith
  have hbase := bracket_lpNorm_two_le hN hc hCOne hCSquare hCTwo H
  rw [show (fun ω ↦ (4 / (N * (N + 1))) *
      centeredQuadraticTraceBracket N c (tOne ω) (tTwo ω)) =
      (4 / (N * (N + 1))) •
        (fun ω ↦ centeredQuadraticTraceBracket N c (tOne ω) (tTwo ω)) by rfl,
    lpNorm_const_smul]
  change ‖4 / (N * (N + 1))‖ *
      lpNorm (fun ω ↦ centeredQuadraticTraceBracket N c (tOne ω) (tTwo ω)) 2 mu ≤
    4 * (2 * CTwo + 2 * CSquare + 3 * COne)
  rw [Real.norm_eq_abs,
    abs_of_pos (div_pos (by norm_num) (mul_pos hNpos hNpOne))]
  calc
    4 / (N * (N + 1)) *
        lpNorm (fun ω ↦ centeredQuadraticTraceBracket N c (tOne ω) (tTwo ω)) 2 mu ≤
      4 / (N * (N + 1)) *
        ((2 * CTwo + 2 * CSquare + 3 * COne) * N ^ 2) := by
          gcongr
    _ ≤ 4 * (2 * CTwo + 2 * CSquare + 3 * COne) := by
      have hC : 0 ≤ 2 * CTwo + 2 * CSquare + 3 * COne := by positivity
      have hratio : N / (N + 1) ≤ 1 := (div_le_one hNpOne).2 (by linarith)
      calc
        4 / (N * (N + 1)) *
            ((2 * CTwo + 2 * CSquare + 3 * COne) * N ^ 2) =
          4 * (2 * CTwo + 2 * CSquare + 3 * COne) * (N / (N + 1)) := by
            field_simp [ne_of_gt hNpos, ne_of_gt hNpOne]
        _ ≤ 4 * (2 * CTwo + 2 * CSquare + 3 * COne) * 1 := by
          gcongr
        _ = 4 * (2 * CTwo + 2 * CSquare + 3 * COne) := by ring

end CenteredQuadraticTraceInputs

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

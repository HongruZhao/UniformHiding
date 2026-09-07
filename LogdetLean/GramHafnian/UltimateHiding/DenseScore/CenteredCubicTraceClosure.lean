import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ProjectiveContractions
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Tactic

/-!
# Primitive trace-moment closure for the averaged cubic score

This file starts with the exact `w_v` contraction (R14), not with an
arbitrary score ledger.  It proves the `O(N)` estimate from three explicit
fixed-degree trace monomials with their natural powers of `c` retained.

The primitive monomials are

* `Tr(Z(I+Z))`;
* `Tr Z * Tr(Z(I+Z))`;
* `Tr(Z^2(I+Z))`.

Those are precisely the quantities supplied by standard fixed
inverse-Wishart moments.  No centered cubic-score or total-variation bound is
an input.
-/

open MeasureTheory
open scoped ENNReal

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-- The right-hand side of the exact contraction (R14). -/
def averagedCubicWTraceExpression
    (N c traceZW traceZTraceZW traceZTwoW : ℝ) : ℝ :=
  48 * c / (N * (N + 1) * (N + 2)) *
    ((N + 2) ^ 2 * traceZW -
      (c - 2) * (traceZTraceZW + 2 * traceZTwoW))

/-- A coefficient bound for the first monomial in (R14). -/
theorem averagedCubicW_first_coefficient_le
    {N c : ℝ} (hN : 1 ≤ N) (hc : 1 ≤ c) :
    |48 * c / (N * (N + 1) * (N + 2)) * (N + 2) ^ 2| ≤
      72 * c / N := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hNpOne : 0 < N + 1 := by linarith
  have hNpTwo : 0 < N + 2 := by linarith
  rw [abs_of_pos (mul_pos (div_pos (mul_pos (by norm_num) hcpos)
    (mul_pos (mul_pos hNpos hNpOne) hNpTwo)) (sq_pos_of_pos hNpTwo))]
  calc
    48 * c / (N * (N + 1) * (N + 2)) * (N + 2) ^ 2 =
        (48 * c * (N + 2) / (N + 1)) / N := by
      field_simp [ne_of_gt hNpos, ne_of_gt hNpOne, ne_of_gt hNpTwo]
    _ ≤ (72 * c) / N := (div_le_div_iff_of_pos_right hNpos).2 <| by
      apply (div_le_iff₀ hNpOne).2
      nlinarith
    _ = 72 * c / N := by ring

/-- The factor `|c-2|` costs at most one more power of `c` for `c≥1`. -/
theorem abs_sub_two_le_self {c : ℝ} (hc : 1 ≤ c) :
    |c - 2| ≤ c := by
  rw [abs_le]
  constructor <;> linarith

/-- Coefficient bound for `Tr Z * Tr(Z(I+Z))`. -/
theorem averagedCubicW_product_coefficient_le
    {N c : ℝ} (hN : 1 ≤ N) (hc : 1 ≤ c) :
    |48 * c / (N * (N + 1) * (N + 2)) * (c - 2)| ≤
      48 * c ^ 2 / N ^ 3 := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hNpOne : 0 < N + 1 := by linarith
  have hNpTwo : 0 < N + 2 := by linarith
  rw [abs_mul, abs_of_pos (div_pos (mul_pos (by norm_num) hcpos)
    (mul_pos (mul_pos hNpos hNpOne) hNpTwo))]
  have habs := abs_sub_two_le_self hc
  have hden : N ^ 3 ≤ N * (N + 1) * (N + 2) := by nlinarith
  have hinvden : 1 / (N * (N + 1) * (N + 2)) ≤ 1 / N ^ 3 := by
    exact one_div_le_one_div_of_le (pow_pos hNpos 3) hden
  calc
    48 * c / (N * (N + 1) * (N + 2)) * |c - 2| ≤
        48 * c / (N * (N + 1) * (N + 2)) * c := by
      gcongr
    _ ≤ 48 * c * (1 / N ^ 3) * c := by
      have hscale : 0 ≤ 48 * c * c := by positivity
      calc
        48 * c / (N * (N + 1) * (N + 2)) * c =
            (48 * c * c) * (1 / (N * (N + 1) * (N + 2))) := by ring
        _ ≤ (48 * c * c) * (1 / N ^ 3) :=
          mul_le_mul_of_nonneg_left hinvden hscale
        _ = 48 * c * (1 / N ^ 3) * c := by ring
    _ = 48 * c ^ 2 / N ^ 3 := by ring

/-- Coefficient bound for the `2 Tr(Z^2(I+Z))` monomial. -/
theorem averagedCubicW_two_coefficient_le
    {N c : ℝ} (hN : 1 ≤ N) (hc : 1 ≤ c) :
    |48 * c / (N * (N + 1) * (N + 2)) * (c - 2) * 2| ≤
      96 * c ^ 2 / N ^ 3 := by
  calc
    |48 * c / (N * (N + 1) * (N + 2)) * (c - 2) * 2| =
        2 * |48 * c / (N * (N + 1) * (N + 2)) * (c - 2)| := by
          rw [abs_mul]
          norm_num
          ring
    _ ≤ 2 * (48 * c ^ 2 / N ^ 3) := by
      gcongr
      exact averagedCubicW_product_coefficient_le hN hc
    _ = 96 * c ^ 2 / N ^ 3 := by ring

/-- Primitive fixed-degree trace moments for (R14), with their exact
dimension and exponent scales visible. -/
structure AveragedCubicWTraceInputs
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (N c CZW CProduct CZTwoW : ℝ)
    (traceZW traceZTraceZW traceZTwoW : Omega → ℝ) : Prop where
  traceZW_memLp : MemLp traceZW 1 mu
  traceZTraceZW_memLp : MemLp traceZTraceZW 1 mu
  traceZTwoW_memLp : MemLp traceZTwoW 1 mu
  traceZW_lpNorm_le : lpNorm traceZW 1 mu ≤ CZW * N ^ 2 / c
  traceZTraceZW_lpNorm_le :
    lpNorm traceZTraceZW 1 mu ≤ CProduct * N ^ 4 / c ^ 2
  traceZTwoW_lpNorm_le :
    lpNorm traceZTwoW 1 mu ≤ CZTwoW * N ^ 3 / c ^ 2

namespace AveragedCubicWTraceInputs

variable {Omega : Type*} [MeasurableSpace Omega]
variable {mu : Measure Omega}
variable {N c CZW CProduct CZTwoW : ℝ}
variable {traceZW traceZTraceZW traceZTwoW : Omega → ℝ}

/-- Internal R14-to-R16 closure. -/
theorem expression_lpNorm_one_le
    (hN : 1 ≤ N) (hc : 1 ≤ c)
    (hCZW : 0 ≤ CZW) (hCProduct : 0 ≤ CProduct) (hCZTwoW : 0 ≤ CZTwoW)
    (H : AveragedCubicWTraceInputs mu N c CZW CProduct CZTwoW
      traceZW traceZTraceZW traceZTwoW) :
    lpNorm (fun ω ↦ averagedCubicWTraceExpression N c
        (traceZW ω) (traceZTraceZW ω) (traceZTwoW ω)) 1 mu ≤
      (72 * CZW + 48 * CProduct + 96 * CZTwoW) * N := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  let a := 48 * c / (N * (N + 1) * (N + 2)) * (N + 2) ^ 2
  let b := -(48 * c / (N * (N + 1) * (N + 2)) * (c - 2))
  let d := -(48 * c / (N * (N + 1) * (N + 2)) * (c - 2) * 2)
  have hpoint :
      (fun ω ↦ averagedCubicWTraceExpression N c
        (traceZW ω) (traceZTraceZW ω) (traceZTwoW ω)) =
      a • traceZW + b • traceZTraceZW + d • traceZTwoW := by
    funext ω
    change averagedCubicWTraceExpression N c
      (traceZW ω) (traceZTraceZW ω) (traceZTwoW ω) =
      a * traceZW ω + b * traceZTraceZW ω + d * traceZTwoW ω
    simp only [averagedCubicWTraceExpression, a, b, d]
    ring
  rw [hpoint]
  have habMem : MemLp (a • traceZW + b • traceZTraceZW) 1 mu :=
    (H.traceZW_memLp.const_smul a).add (H.traceZTraceZW_memLp.const_smul b)
  have ha : |a| ≤ 72 * c / N := by
    simpa [a] using averagedCubicW_first_coefficient_le hN hc
  have hb : |b| ≤ 48 * c ^ 2 / N ^ 3 := by
    simpa [b] using averagedCubicW_product_coefficient_le hN hc
  have hd : |d| ≤ 96 * c ^ 2 / N ^ 3 := by
    simpa [d] using averagedCubicW_two_coefficient_le hN hc
  have hAprod : |a| * lpNorm traceZW 1 mu ≤ 72 * CZW * N := by
    calc
      |a| * lpNorm traceZW 1 mu ≤
          (72 * c / N) * (CZW * N ^ 2 / c) :=
        mul_le_mul ha H.traceZW_lpNorm_le lpNorm_nonneg (by positivity)
      _ = 72 * CZW * N := by field_simp [ne_of_gt hNpos, ne_of_gt hcpos]
  have hBprod : |b| * lpNorm traceZTraceZW 1 mu ≤ 48 * CProduct * N := by
    calc
      |b| * lpNorm traceZTraceZW 1 mu ≤
          (48 * c ^ 2 / N ^ 3) * (CProduct * N ^ 4 / c ^ 2) :=
        mul_le_mul hb H.traceZTraceZW_lpNorm_le lpNorm_nonneg (by positivity)
      _ = 48 * CProduct * N := by field_simp [ne_of_gt hNpos, ne_of_gt hcpos]
  have hDprod : |d| * lpNorm traceZTwoW 1 mu ≤ 96 * CZTwoW := by
    calc
      |d| * lpNorm traceZTwoW 1 mu ≤
          (96 * c ^ 2 / N ^ 3) * (CZTwoW * N ^ 3 / c ^ 2) :=
        mul_le_mul hd H.traceZTwoW_lpNorm_le lpNorm_nonneg (by positivity)
      _ = 96 * CZTwoW := by field_simp [ne_of_gt hNpos, ne_of_gt hcpos]
  calc
    lpNorm (a • traceZW + b • traceZTraceZW + d • traceZTwoW) 1 mu ≤
        lpNorm (a • traceZW + b • traceZTraceZW) 1 mu +
          lpNorm (d • traceZTwoW) 1 mu := lpNorm_add_le habMem (by norm_num)
    _ ≤ (lpNorm (a • traceZW) 1 mu +
          lpNorm (b • traceZTraceZW) 1 mu) +
          lpNorm (d • traceZTwoW) 1 mu := by
      gcongr
      exact lpNorm_add_le (H.traceZW_memLp.const_smul a) (by norm_num)
    _ = |a| * lpNorm traceZW 1 mu + |b| * lpNorm traceZTraceZW 1 mu +
          |d| * lpNorm traceZTwoW 1 mu := by
      simp only [lpNorm_const_smul]
      change ‖a‖ * lpNorm traceZW 1 mu + ‖b‖ * lpNorm traceZTraceZW 1 mu +
          ‖d‖ * lpNorm traceZTwoW 1 mu =
        |a| * lpNorm traceZW 1 mu + |b| * lpNorm traceZTraceZW 1 mu +
          |d| * lpNorm traceZTwoW 1 mu
      simp only [Real.norm_eq_abs]
    _ ≤ 72 * CZW * N + 48 * CProduct * N + 96 * CZTwoW :=
      add_le_add (add_le_add hAprod hBprod) hDprod
    _ ≤ (72 * CZW + 48 * CProduct + 96 * CZTwoW) * N := by
      have hNnonneg : 0 ≤ N := hNpos.le
      nlinarith

end AveragedCubicWTraceInputs

/-! ## Non-`w` cubic closure -/

/-- The averaged non-`w` polynomial after the exact centered-coordinate
expansion in `coeRankOneDensityScoreThree_nonW_centered_expansion`, with
`p=N+1`.  The three arguments are the projective averages of `s`, `s²`,
and `s³`. -/
def averagedCubicNonWExpression
    (N c meanS meanSSquare meanSCube : ℝ) : ℝ :=
  8 * (cubicTraceCoefficientThree c * meanSCube +
    cubicTraceCoefficientTwo c (N + 1) * meanSSquare +
    cubicTraceCoefficientOne c (N + 1) * meanS +
    cubicTraceCoefficientZero c (N + 1))

/-- Primitive projective/Wishart moments for the non-`w` part of the cubic.
The final cubic score does not occur in this interface. -/
structure AveragedCubicNonWInputs
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (N COne CTwo CThree : ℝ)
    (meanS meanSSquare meanSCube : Omega → ℝ) : Prop where
  meanS_memLp : MemLp meanS 1 mu
  meanSSquare_memLp : MemLp meanSSquare 1 mu
  meanSCube_memLp : MemLp meanSCube 1 mu
  meanS_lpNorm_le : lpNorm meanS 1 mu ≤ COne
  meanSSquare_lpNorm_le : lpNorm meanSSquare 1 mu ≤ CTwo * N
  meanSCube_lpNorm_le : lpNorm meanSCube 1 mu ≤ CThree * N

namespace AveragedCubicNonWInputs

variable {Omega : Type*} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {N c COne CTwo CThree : ℝ}
variable {meanS meanSSquare meanSCube : Omega → ℝ}

/-- Exact non-`w` cubic closure before the elementary coefficient estimates
in the dense range. -/
theorem expression_lpNorm_one_le
    (hN : 0 ≤ N)
    (hCOne : 0 ≤ COne) (hCTwo : 0 ≤ CTwo) (hCThree : 0 ≤ CThree)
    (H : AveragedCubicNonWInputs mu N COne CTwo CThree
      meanS meanSSquare meanSCube) :
    lpNorm (fun ω ↦ averagedCubicNonWExpression N c
        (meanS ω) (meanSSquare ω) (meanSCube ω)) 1 mu ≤
      8 * (|cubicTraceCoefficientThree c| * (CThree * N) +
        |cubicTraceCoefficientTwo c (N + 1)| * (CTwo * N) +
        |cubicTraceCoefficientOne c (N + 1)| * COne +
        |cubicTraceCoefficientZero c (N + 1)|) := by
  let a := 8 * cubicTraceCoefficientThree c
  let b := 8 * cubicTraceCoefficientTwo c (N + 1)
  let d := 8 * cubicTraceCoefficientOne c (N + 1)
  let e := 8 * cubicTraceCoefficientZero c (N + 1)
  have hpoint :
      (fun ω ↦ averagedCubicNonWExpression N c
        (meanS ω) (meanSSquare ω) (meanSCube ω)) =
      a • meanSCube + b • meanSSquare + d • meanS + fun _ ↦ e := by
    funext ω
    change averagedCubicNonWExpression N c
      (meanS ω) (meanSSquare ω) (meanSCube ω) =
      a * meanSCube ω + b * meanSSquare ω + d * meanS ω + e
    simp only [averagedCubicNonWExpression, a, b, d, e]
    ring
  rw [hpoint]
  have hab : MemLp (a • meanSCube + b • meanSSquare) 1 mu :=
    (H.meanSCube_memLp.const_smul a).add (H.meanSSquare_memLp.const_smul b)
  have habd : MemLp (a • meanSCube + b • meanSSquare + d • meanS) 1 mu :=
    hab.add (H.meanS_memLp.const_smul d)
  have hAprod : |a| * lpNorm meanSCube 1 mu ≤
      8 * |cubicTraceCoefficientThree c| * (CThree * N) := by
    have ha : |a| = 8 * |cubicTraceCoefficientThree c| := by
      simp [a, abs_mul]
    rw [ha]
    exact mul_le_mul_of_nonneg_left H.meanSCube_lpNorm_le (by positivity)
  have hBprod : |b| * lpNorm meanSSquare 1 mu ≤
      8 * |cubicTraceCoefficientTwo c (N + 1)| * (CTwo * N) := by
    have hb : |b| = 8 * |cubicTraceCoefficientTwo c (N + 1)| := by
      simp [b, abs_mul]
    rw [hb]
    exact mul_le_mul_of_nonneg_left H.meanSSquare_lpNorm_le (by positivity)
  have hDprod : |d| * lpNorm meanS 1 mu ≤
      8 * |cubicTraceCoefficientOne c (N + 1)| * COne := by
    have hd : |d| = 8 * |cubicTraceCoefficientOne c (N + 1)| := by
      simp [d, abs_mul]
    rw [hd]
    exact mul_le_mul_of_nonneg_left H.meanS_lpNorm_le (by positivity)
  have hconst : lpNorm (fun _ : Omega ↦ e) 1 mu = |e| := by
    rw [lpNorm_const (p := (1 : ℝ≥0∞)) one_ne_zero
      (IsProbabilityMeasure.ne_zero mu) e]
    simp [Real.norm_eq_abs]
  calc
    lpNorm (a • meanSCube + b • meanSSquare + d • meanS + fun _ ↦ e) 1 mu ≤
        lpNorm (a • meanSCube + b • meanSSquare + d • meanS) 1 mu +
          lpNorm (fun _ : Omega ↦ e) 1 mu := lpNorm_add_le habd (by norm_num)
    _ ≤ (lpNorm (a • meanSCube + b • meanSSquare) 1 mu +
          lpNorm (d • meanS) 1 mu) + lpNorm (fun _ : Omega ↦ e) 1 mu := by
      gcongr
      exact lpNorm_add_le hab (by norm_num)
    _ ≤ ((lpNorm (a • meanSCube) 1 mu + lpNorm (b • meanSSquare) 1 mu) +
          lpNorm (d • meanS) 1 mu) + lpNorm (fun _ : Omega ↦ e) 1 mu := by
      gcongr
      exact lpNorm_add_le (H.meanSCube_memLp.const_smul a) (by norm_num)
    _ = (|a| * lpNorm meanSCube 1 mu + |b| * lpNorm meanSSquare 1 mu) +
          |d| * lpNorm meanS 1 mu + |e| := by
      rw [hconst]
      simp only [lpNorm_const_smul]
      change (‖a‖ * lpNorm meanSCube 1 mu + ‖b‖ * lpNorm meanSSquare 1 mu) +
          ‖d‖ * lpNorm meanS 1 mu + |e| = _
      simp only [Real.norm_eq_abs]
    _ ≤ (8 * |cubicTraceCoefficientThree c| * (CThree * N) +
          8 * |cubicTraceCoefficientTwo c (N + 1)| * (CTwo * N)) +
          8 * |cubicTraceCoefficientOne c (N + 1)| * COne + |e| :=
      add_le_add (add_le_add (add_le_add hAprod hBprod) hDprod) le_rfl
    _ = 8 * (|cubicTraceCoefficientThree c| * (CThree * N) +
        |cubicTraceCoefficientTwo c (N + 1)| * (CTwo * N) +
        |cubicTraceCoefficientOne c (N + 1)| * COne +
        |cubicTraceCoefficientZero c (N + 1)|) := by
      simp [e, abs_mul]
      ring

end AveragedCubicNonWInputs

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

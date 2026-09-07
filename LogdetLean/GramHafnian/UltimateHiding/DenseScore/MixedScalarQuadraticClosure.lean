import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredTraceAlgebra
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Tactic

/-!
# Mixed scalar--quadratic closure

This file closes the middle term in the exact centered cubic identity (R25).
It keeps the derivative of the explicit R30 trace bracket visible, proves its
dimension scale from literal trace monomials, and applies Holder internally to
the product of the scalar score with the normalized quadratic density.

No `X_I D₂`, cubic-score, total-variation, or hiding estimate is an input.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-! ## Exact scalar derivative of the R30 bracket -/

/-- `X_I Tr Y = 4(Tr Y + Tr Y²/c)`. -/
def centralTraceOneDerivative (c tOne tTwo : ℝ) : ℝ :=
  4 * (tOne + tTwo / c)

/-- `X_I Tr Y² = 8(Tr Y² + Tr Y³/c)`. -/
def centralTraceTwoDerivative (c tTwo tThree : ℝ) : ℝ :=
  8 * (tTwo + tThree / c)

/-- Chain-rule derivative of the literal bracket in (R30). -/
def centralDerivativeQuadraticTraceBracket
    (N c tOne tTwo tThree : ℝ) : ℝ :=
  quadraticTraceCoeffTwo N c * centralTraceTwoDerivative c tTwo tThree +
    quadraticTraceCoeffSquare N c *
      (2 * tOne * centralTraceOneDerivative c tOne tTwo) +
    quadraticTraceCoeffOne N * centralTraceOneDerivative c tOne tTwo

/-- Denominator-cleared algebraic verification of the R30 scalar derivative.
The hypotheses name the two trace derivatives, so no analytic chain rule is
hidden in this identity. -/
theorem centralDerivativeQuadraticTraceBracket_exact
    {N c tOne tTwo tThree dtOne dtTwo : ℝ}
    (hN : N ≠ 0) (hc : c ≠ 0)
    (hdtOne : dtOne = 4 * (tOne + tTwo / c))
    (hdtTwo : dtTwo = 8 * (tTwo + tThree / c)) :
    quadraticTraceCoeffTwo N c * dtTwo +
        quadraticTraceCoeffSquare N c * (2 * tOne * dtOne) +
        quadraticTraceCoeffOne N * dtOne =
      centralDerivativeQuadraticTraceBracket N c tOne tTwo tThree := by
  rw [hdtOne, hdtTwo]
  simp only [centralDerivativeQuadraticTraceBracket,
    centralTraceOneDerivative, centralTraceTwoDerivative]

/-! ## Primitive trace-monomial closure -/

/-- Fixed-degree trace inputs used by the derivative in (R27).

The five functions are exactly `Tr Y`, `Tr Y²`, `Tr Y³`, `(Tr Y)²`, and
`Tr Y * Tr Y²`.  Their powers of `N` are the standard dense inverse-Wishart
scales. -/
structure CentralQuadraticDerivativeTraceInputs
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (N COne CTwo CThree COneSquare COneTwo : ℝ)
    (tOne tTwo tThree : Omega → ℝ) : Prop where
  one_memLp : MemLp tOne 1 mu
  two_memLp : MemLp tTwo 1 mu
  three_memLp : MemLp tThree 1 mu
  oneSquare_memLp : MemLp (fun ω ↦ tOne ω ^ 2) 1 mu
  oneTwo_memLp : MemLp (fun ω ↦ tOne ω * tTwo ω) 1 mu
  one_lpNorm_le : lpNorm tOne 1 mu ≤ COne * N ^ 2
  two_lpNorm_le : lpNorm tTwo 1 mu ≤ CTwo * N ^ 3
  three_lpNorm_le : lpNorm tThree 1 mu ≤ CThree * N ^ 4
  oneSquare_lpNorm_le :
    lpNorm (fun ω ↦ tOne ω ^ 2) 1 mu ≤ COneSquare * N ^ 4
  oneTwo_lpNorm_le :
    lpNorm (fun ω ↦ tOne ω * tTwo ω) 1 mu ≤ COneTwo * N ^ 5

namespace CentralQuadraticDerivativeTraceInputs

variable {Omega : Type*} [MeasurableSpace Omega]
variable {mu : Measure Omega}
variable {N c COne CTwo CThree COneSquare COneTwo : ℝ}
variable {tOne tTwo tThree : Omega → ℝ}

/-- The unnormalized derivative of the R30 bracket is `O(N³)` in `L¹`.
All constants are explicit and intentionally generous. -/
theorem derivative_lpNorm_one_le
    (hN : 1 ≤ N) (hc : N ≤ c)
    (hCOne : 0 ≤ COne) (hCTwo : 0 ≤ CTwo)
    (hCThree : 0 ≤ CThree) (hCOneSquare : 0 ≤ COneSquare)
    (hCOneTwo : 0 ≤ COneTwo)
    (H : CentralQuadraticDerivativeTraceInputs mu N
      COne CTwo CThree COneSquare COneTwo tOne tTwo tThree) :
    lpNorm (fun ω ↦ centralDerivativeQuadraticTraceBracket N c
        (tOne ω) (tTwo ω) (tThree ω)) 1 mu ≤
      (16 * CTwo + 16 * CThree + 16 * COneSquare +
        16 * COneTwo + 12 * COne + 12 * CTwo) * N ^ 3 := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hcpos : 0 < c := hNpos.trans_le hc
  let a := quadraticTraceCoeffTwo N c
  let b := quadraticTraceCoeffSquare N c
  let d := quadraticTraceCoeffOne N
  let fTwo : Omega → ℝ := fun ω ↦ 8 * tTwo ω
  let fThree : Omega → ℝ := fun ω ↦ 8 * tThree ω / c
  let fOneSquare : Omega → ℝ := fun ω ↦ 8 * tOne ω ^ 2
  let fOneTwo : Omega → ℝ := fun ω ↦ 8 * (tOne ω * tTwo ω) / c
  let fOne : Omega → ℝ := fun ω ↦ 4 * tOne ω
  let fTwoCentral : Omega → ℝ := fun ω ↦ 4 * tTwo ω / c
  have hpoint :
      (fun ω ↦ centralDerivativeQuadraticTraceBracket N c
        (tOne ω) (tTwo ω) (tThree ω)) =
      a • fTwo + a • fThree + b • fOneSquare + b • fOneTwo +
        d • fOne + d • fTwoCentral := by
    funext ω
    change centralDerivativeQuadraticTraceBracket N c
      (tOne ω) (tTwo ω) (tThree ω) =
        a * fTwo ω + a * fThree ω + b * fOneSquare ω + b * fOneTwo ω +
          d * fOne ω + d * fTwoCentral ω
    simp only [centralDerivativeQuadraticTraceBracket,
      centralTraceOneDerivative, centralTraceTwoDerivative,
      a, b, d, fTwo, fThree, fOneSquare, fOneTwo, fOne, fTwoCentral]
    ring
  rw [hpoint]
  have ha : |a| ≤ 2 := by
    simpa [a] using abs_quadraticTraceCoeffTwo_le_two hN hc
  have hb : |b| ≤ 2 / N := by
    simpa [b] using abs_quadraticTraceCoeffSquare_le hN hc
  have hd : |d| ≤ 3 * N := by
    simpa [d] using abs_quadraticTraceCoeffOne_le hN
  have hfTwo : MemLp fTwo 1 mu := (H.two_memLp.const_mul 8)
  have hfThree : MemLp fThree 1 mu := by
    rw [show fThree = (8 / c) • tThree by
      funext ω; simp [fThree]; ring]
    exact H.three_memLp.const_smul (8 / c)
  have hfOneSquare : MemLp fOneSquare 1 mu := H.oneSquare_memLp.const_mul 8
  have hfOneTwo : MemLp fOneTwo 1 mu := by
    rw [show fOneTwo = (8 / c) • (fun ω ↦ tOne ω * tTwo ω) by
      funext ω; simp [fOneTwo]; ring]
    exact H.oneTwo_memLp.const_smul (8 / c)
  have hfOne : MemLp fOne 1 mu := H.one_memLp.const_mul 4
  have hfTwoCentral : MemLp fTwoCentral 1 mu := by
    rw [show fTwoCentral = (4 / c) • tTwo by
      funext ω; simp [fTwoCentral]; ring]
    exact H.two_memLp.const_smul (4 / c)
  have hsum1 : MemLp (a • fTwo + a • fThree) 1 mu :=
    (hfTwo.const_smul a).add (hfThree.const_smul a)
  have hsum2 : MemLp (a • fTwo + a • fThree + b • fOneSquare) 1 mu :=
    hsum1.add (hfOneSquare.const_smul b)
  have hsum3 : MemLp
      (a • fTwo + a • fThree + b • fOneSquare + b • fOneTwo) 1 mu :=
    hsum2.add (hfOneTwo.const_smul b)
  have hsum4 : MemLp
      (a • fTwo + a • fThree + b • fOneSquare + b • fOneTwo + d • fOne)
      1 mu := hsum3.add (hfOne.const_smul d)
  have htriangle :
      lpNorm (a • fTwo + a • fThree + b • fOneSquare + b • fOneTwo +
          d • fOne + d • fTwoCentral) 1 mu ≤
        |a| * lpNorm fTwo 1 mu + |a| * lpNorm fThree 1 mu +
          |b| * lpNorm fOneSquare 1 mu + |b| * lpNorm fOneTwo 1 mu +
          |d| * lpNorm fOne 1 mu + |d| * lpNorm fTwoCentral 1 mu := by
    have h6 : lpNorm
        (a • fTwo + a • fThree + b • fOneSquare + b • fOneTwo +
          d • fOne + d • fTwoCentral) 1 mu ≤
        lpNorm (a • fTwo + a • fThree + b • fOneSquare + b • fOneTwo +
          d • fOne) 1 mu + lpNorm (d • fTwoCentral) 1 mu :=
      lpNorm_add_le hsum4 (by norm_num)
    have h5 := lpNorm_add_le hsum3 (g := d • fOne) (by norm_num)
    have h4 := lpNorm_add_le hsum2 (g := b • fOneTwo) (by norm_num)
    have h3 := lpNorm_add_le hsum1 (g := b • fOneSquare) (by norm_num)
    have h2 := lpNorm_add_le (hfTwo.const_smul a) (g := a • fThree) (by norm_num)
    simp only [lpNorm_const_smul, coe_nnnorm, Real.norm_eq_abs] at h6 h5 h4 h3 h2 ⊢
    linarith
  have hfTwoNorm : lpNorm fTwo 1 mu ≤ 8 * CTwo * N ^ 3 := by
    rw [show fTwo = (8 : ℝ) • tTwo by funext ω; simp [fTwo],
      lpNorm_const_smul, coe_nnnorm, Real.norm_eq_abs]
    norm_num
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left H.two_lpNorm_le
      (by norm_num : (0 : ℝ) ≤ 8)
  have hfThreeNorm : lpNorm fThree 1 mu ≤ 8 * CThree * N ^ 3 := by
    rw [show fThree = (8 / c) • tThree by
      funext ω; simp [fThree]; ring, lpNorm_const_smul, coe_nnnorm,
      Real.norm_eq_abs,
      abs_of_pos (div_pos (by norm_num) hcpos)]
    calc
      8 / c * lpNorm tThree 1 mu ≤ 8 / c * (CThree * N ^ 4) :=
        mul_le_mul_of_nonneg_left H.three_lpNorm_le
          (le_of_lt (div_pos (by norm_num) hcpos))
      _ ≤ 8 * CThree * N ^ 3 := by
        have hratio : N / c ≤ 1 := (div_le_one hcpos).2 hc
        have hnonneg : 0 ≤ CThree * N ^ 3 := by positivity
        calc
          8 / c * (CThree * N ^ 4) =
              8 * CThree * N ^ 3 * (N / c) := by ring
          _ ≤ 8 * CThree * N ^ 3 * 1 :=
            mul_le_mul_of_nonneg_left hratio (by positivity)
          _ = 8 * CThree * N ^ 3 := by ring
  have hfOneSquareNorm : lpNorm fOneSquare 1 mu ≤ 8 * COneSquare * N ^ 4 := by
    rw [show fOneSquare = (8 : ℝ) • (fun ω ↦ tOne ω ^ 2) by
      funext ω; simp [fOneSquare], lpNorm_const_smul, coe_nnnorm,
      Real.norm_eq_abs]
    norm_num
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left H.oneSquare_lpNorm_le
      (by norm_num : (0 : ℝ) ≤ 8)
  have hfOneTwoNorm : lpNorm fOneTwo 1 mu ≤ 8 * COneTwo * N ^ 4 := by
    rw [show fOneTwo = (8 / c) • (fun ω ↦ tOne ω * tTwo ω) by
      funext ω; simp [fOneTwo]; ring, lpNorm_const_smul, coe_nnnorm,
      Real.norm_eq_abs,
      abs_of_pos (div_pos (by norm_num) hcpos)]
    calc
      8 / c * lpNorm (fun ω ↦ tOne ω * tTwo ω) 1 mu ≤
          8 / c * (COneTwo * N ^ 5) :=
        mul_le_mul_of_nonneg_left H.oneTwo_lpNorm_le
          (le_of_lt (div_pos (by norm_num) hcpos))
      _ ≤ 8 * COneTwo * N ^ 4 := by
        have hratio : N / c ≤ 1 := (div_le_one hcpos).2 hc
        have hnonneg : 0 ≤ COneTwo * N ^ 4 := by positivity
        calc
          8 / c * (COneTwo * N ^ 5) =
              8 * COneTwo * N ^ 4 * (N / c) := by ring
          _ ≤ 8 * COneTwo * N ^ 4 * 1 :=
            mul_le_mul_of_nonneg_left hratio (by positivity)
          _ = 8 * COneTwo * N ^ 4 := by ring
  have hfOneNorm : lpNorm fOne 1 mu ≤ 4 * COne * N ^ 2 := by
    rw [show fOne = (4 : ℝ) • tOne by funext ω; simp [fOne],
      lpNorm_const_smul, coe_nnnorm, Real.norm_eq_abs]
    norm_num
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left H.one_lpNorm_le
      (by norm_num : (0 : ℝ) ≤ 4)
  have hfTwoCentralNorm : lpNorm fTwoCentral 1 mu ≤ 4 * CTwo * N ^ 2 := by
    rw [show fTwoCentral = (4 / c) • tTwo by
      funext ω; simp [fTwoCentral]; ring, lpNorm_const_smul, coe_nnnorm,
      Real.norm_eq_abs,
      abs_of_pos (div_pos (by norm_num) hcpos)]
    calc
      4 / c * lpNorm tTwo 1 mu ≤ 4 / c * (CTwo * N ^ 3) :=
        mul_le_mul_of_nonneg_left H.two_lpNorm_le
          (le_of_lt (div_pos (by norm_num) hcpos))
      _ ≤ 4 * CTwo * N ^ 2 := by
        have hratio : N / c ≤ 1 := (div_le_one hcpos).2 hc
        have hnonneg : 0 ≤ CTwo * N ^ 2 := by positivity
        calc
          4 / c * (CTwo * N ^ 3) = 4 * CTwo * N ^ 2 * (N / c) := by ring
          _ ≤ 4 * CTwo * N ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left hratio (by positivity)
          _ = 4 * CTwo * N ^ 2 := by ring
  calc
    lpNorm (a • fTwo + a • fThree + b • fOneSquare + b • fOneTwo +
        d • fOne + d • fTwoCentral) 1 mu ≤ _ := htriangle
    _ ≤ 2 * (8 * CTwo * N ^ 3) + 2 * (8 * CThree * N ^ 3) +
          (2 / N) * (8 * COneSquare * N ^ 4) +
          (2 / N) * (8 * COneTwo * N ^ 4) +
          (3 * N) * (4 * COne * N ^ 2) +
          (3 * N) * (4 * CTwo * N ^ 2) := by
      exact add_le_add
        (add_le_add
          (add_le_add
            (add_le_add
              (add_le_add
                (mul_le_mul ha hfTwoNorm lpNorm_nonneg (by positivity))
                (mul_le_mul ha hfThreeNorm lpNorm_nonneg (by positivity)))
              (mul_le_mul hb hfOneSquareNorm lpNorm_nonneg (by positivity)))
            (mul_le_mul hb hfOneTwoNorm lpNorm_nonneg (by positivity)))
          (mul_le_mul hd hfOneNorm lpNorm_nonneg (by positivity)))
        (mul_le_mul hd hfTwoCentralNorm lpNorm_nonneg (by positivity))
    _ = (16 * CTwo + 16 * CThree + 16 * COneSquare +
        16 * COneTwo + 12 * COne + 12 * CTwo) * N ^ 3 := by
      field_simp [ne_of_gt hNpos]
      ring

/-- After multiplication by the exact `4/[N(N+1)]` prefactor, the scalar
derivative of the averaged quadratic density is `O(N)` in `L¹`. -/
theorem normalized_derivative_lpNorm_one_le
    (hN : 1 ≤ N) (hc : N ≤ c)
    (hCOne : 0 ≤ COne) (hCTwo : 0 ≤ CTwo)
    (hCThree : 0 ≤ CThree) (hCOneSquare : 0 ≤ COneSquare)
    (hCOneTwo : 0 ≤ COneTwo)
    (H : CentralQuadraticDerivativeTraceInputs mu N
      COne CTwo CThree COneSquare COneTwo tOne tTwo tThree) :
    lpNorm (fun ω ↦ (4 / (N * (N + 1))) *
        centralDerivativeQuadraticTraceBracket N c
          (tOne ω) (tTwo ω) (tThree ω)) 1 mu ≤
      4 * (16 * CTwo + 16 * CThree + 16 * COneSquare +
        16 * COneTwo + 12 * COne + 12 * CTwo) * N := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hNpOne : 0 < N + 1 := by linarith
  have hbase := derivative_lpNorm_one_le hN hc hCOne hCTwo hCThree
    hCOneSquare hCOneTwo H
  rw [show (fun ω ↦ (4 / (N * (N + 1))) *
      centralDerivativeQuadraticTraceBracket N c
        (tOne ω) (tTwo ω) (tThree ω)) =
      (4 / (N * (N + 1))) •
        (fun ω ↦ centralDerivativeQuadraticTraceBracket N c
          (tOne ω) (tTwo ω) (tThree ω)) by rfl,
    lpNorm_const_smul, coe_nnnorm, Real.norm_eq_abs,
    abs_of_pos (div_pos (by norm_num) (mul_pos hNpos hNpOne))]
  calc
    4 / (N * (N + 1)) *
        lpNorm (fun ω ↦ centralDerivativeQuadraticTraceBracket N c
          (tOne ω) (tTwo ω) (tThree ω)) 1 mu ≤
      4 / (N * (N + 1)) *
        ((16 * CTwo + 16 * CThree + 16 * COneSquare +
          16 * COneTwo + 12 * COne + 12 * CTwo) * N ^ 3) :=
      mul_le_mul_of_nonneg_left hbase
        (div_nonneg (by norm_num) (mul_pos hNpos hNpOne).le)
    _ ≤ 4 * (16 * CTwo + 16 * CThree + 16 * COneSquare +
          16 * COneTwo + 12 * COne + 12 * CTwo) * N := by
      have hC : 0 ≤ 16 * CTwo + 16 * CThree + 16 * COneSquare +
          16 * COneTwo + 12 * COne + 12 * CTwo := by positivity
      have hratio : N / (N + 1) ≤ 1 := (div_le_one hNpOne).2 (by linarith)
      calc
        4 / (N * (N + 1)) *
            ((16 * CTwo + 16 * CThree + 16 * COneSquare +
              16 * COneTwo + 12 * COne + 12 * CTwo) * N ^ 3) =
          4 * (16 * CTwo + 16 * CThree + 16 * COneSquare +
              16 * COneTwo + 12 * COne + 12 * CTwo) * N *
              (N / (N + 1)) := by
            field_simp [ne_of_gt hNpos, ne_of_gt hNpOne]
        _ ≤ 4 * (16 * CTwo + 16 * CThree + 16 * COneSquare +
              16 * COneTwo + 12 * COne + 12 * CTwo) * N * 1 :=
            mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = 4 * (16 * CTwo + 16 * CThree + 16 * COneSquare +
              16 * COneTwo + 12 * COne + 12 * CTwo) * N := by ring

end CentralQuadraticDerivativeTraceInputs

/-! ## Holder closure for `X_I D₂` -/

/-- Cauchy--Schwarz in real `lpNorm` form. -/
theorem lpNorm_mul_le_lpNorm_two_mul
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {f g : Omega → ℝ} (hf : MemLp f 2 mu) (hg : MemLp g 2 mu) :
    lpNorm (fun ω ↦ f ω * g ω) 1 mu ≤ lpNorm f 2 mu * lpNorm g 2 mu := by
  have hprod : MemLp (fun ω ↦ f ω * g ω) 1 mu := hg.mul' hf
  have he : eLpNorm (fun ω ↦ f ω * g ω) 1 mu ≤
      eLpNorm f 2 mu * eLpNorm g 2 mu := by
    simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      hf.aestronglyMeasurable hg.aestronglyMeasurable
      (fun x y : ℝ ↦ x * y) 1 (by
        filter_upwards [] with ω
        simp [nnnorm_mul])
  rw [← toReal_eLpNorm hprod.aestronglyMeasurable,
    ← toReal_eLpNorm hf.aestronglyMeasurable,
    ← toReal_eLpNorm hg.aestronglyMeasurable,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top) he

/-- Primitive inputs for the signed density
`X_I(D₂ μ) = (s_I Φ - X_I Φ) μ`.

The final mixed density is not a field.  It is assembled below from the
scalar-score `L²`, quadratic-density `L²`, and explicit trace-derivative
`L¹` inputs. -/
structure MixedScalarQuadraticDensityInputs
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (N CScore CPhi CDeriv : ℝ)
    (scalarScore phi xPhi : Omega → ℝ) : Prop where
  scalarScore_memLp : MemLp scalarScore 2 mu
  phi_memLp : MemLp phi 2 mu
  xPhi_memLp : MemLp xPhi 1 mu
  scalarScore_lpNorm_le : lpNorm scalarScore 2 mu ≤ CScore * N
  phi_lpNorm_le : lpNorm phi 2 mu ≤ CPhi
  xPhi_lpNorm_le : lpNorm xPhi 1 mu ≤ CDeriv * N

namespace MixedScalarQuadraticDensityInputs

variable {Omega : Type*} [MeasurableSpace Omega]
variable {mu : Measure Omega}
variable {N CScore CPhi CDeriv : ℝ}
variable {scalarScore phi xPhi : Omega → ℝ}

/-- Internal proof of the mixed estimate (R27a). -/
theorem mixedDensity_lpNorm_one_le
    (hN : 0 ≤ N) (hCScore : 0 ≤ CScore)
    (hCPhi : 0 ≤ CPhi) (hCDeriv : 0 ≤ CDeriv)
    (H : MixedScalarQuadraticDensityInputs mu N CScore CPhi CDeriv
      scalarScore phi xPhi) :
    lpNorm (fun ω ↦ scalarScore ω * phi ω - xPhi ω) 1 mu ≤
      (CScore * CPhi + CDeriv) * N := by
  have hprod : MemLp (fun ω ↦ scalarScore ω * phi ω) 1 mu :=
    H.phi_memLp.mul' H.scalarScore_memLp
  have hholder := lpNorm_mul_le_lpNorm_two_mul
    H.scalarScore_memLp H.phi_memLp
  have hprodBound :
      lpNorm (fun ω ↦ scalarScore ω * phi ω) 1 mu ≤
        CScore * CPhi * N := by
    calc
      _ ≤ lpNorm scalarScore 2 mu * lpNorm phi 2 mu := hholder
      _ ≤ (CScore * N) * CPhi :=
        mul_le_mul H.scalarScore_lpNorm_le H.phi_lpNorm_le lpNorm_nonneg
          (mul_nonneg hCScore hN)
      _ = CScore * CPhi * N := by ring
  calc
    lpNorm (fun ω ↦ scalarScore ω * phi ω - xPhi ω) 1 mu ≤
        lpNorm (fun ω ↦ scalarScore ω * phi ω) 1 mu +
          lpNorm xPhi 1 mu := by
      change lpNorm ((fun ω ↦ scalarScore ω * phi ω) - xPhi) 1 mu ≤ _
      exact lpNorm_sub_le hprod (by norm_num)
    _ ≤ CScore * CPhi * N + CDeriv * N :=
      add_le_add hprodBound H.xPhi_lpNorm_le
    _ = (CScore * CPhi + CDeriv) * N := by ring

end MixedScalarQuadraticDensityInputs

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

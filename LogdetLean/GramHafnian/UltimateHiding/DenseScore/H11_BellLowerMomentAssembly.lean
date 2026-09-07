import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_FourthBellNormalizationReducer
import Mathlib.Tactic

/-!
# Sharp assembly of the lower Bell-four package

The public monomial endpoints all use the same deliberately huge constant.
Applying the triangle inequality to those already-inflated statements would
lose a factor `14`.  This module instead assembles the lower Bell polynomial
from three sharp inputs, deriving the mixed `ellOne^2 * ellTwo` term by
Young's inequality.  Its exact budget is

`4 * C1 + 6 * C2 + 4 * C13`.

Thus the small constants exposed by the H12 and H14 proofs, together with a
sharp H13 producer, can be combined without changing the paper-facing H11
constant.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Three sharp monomial inputs suffice for the complete lower Bell-four
polynomial.  The fourth lower monomial is obtained by Young's inequality. -/
structure H11BellLowerSharpMonomialPackage
    (N K : ℕ) (C1 C2 C13 : ℝ) : Prop where
  oneFourth_memLp :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p ^ 4) 1
      (concreteCenteredScoreProductLaw N K)
  twoSquare_memLp :
    MemLp (fun p ↦ concreteCenteredEll 2 N K p ^ 2) 1
      (concreteCenteredScoreProductLaw N K)
  oneThree_memLp :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p *
      concreteCenteredEll 3 N K p) 1
      (concreteCenteredScoreProductLaw N K)
  oneFourth_lpNorm_le : 16 * N ≤ K →
    lpNorm (fun p ↦ concreteCenteredEll 1 N K p ^ 4) 1
        (concreteCenteredScoreProductLaw N K) ≤ C1 * (N : ℝ) ^ 2
  twoSquare_lpNorm_le : 16 * N ≤ K →
    lpNorm (fun p ↦ concreteCenteredEll 2 N K p ^ 2) 1
        (concreteCenteredScoreProductLaw N K) ≤ C2 * (N : ℝ) ^ 2
  oneThree_lpNorm_le : 16 * N ≤ K →
    lpNorm (fun p ↦ concreteCenteredEll 1 N K p *
      concreteCenteredEll 3 N K p) 1
        (concreteCenteredScoreProductLaw N K) ≤ C13 * (N : ℝ) ^ 2

/-- Pointwise Young/triangle envelope for the four lower Bell monomials. -/
theorem concreteCenteredBellFourLowerProduct_norm_le_sharpEnvelope
    {N K : ℕ} (p : ConcreteMatrixState N × ComplexUnitSphere N) :
    ‖concreteCenteredBellFourLowerProduct N K p‖ ≤
      4 * concreteCenteredEll 1 N K p ^ 4 +
        6 * concreteCenteredEll 2 N K p ^ 2 +
        4 * |concreteCenteredEll 1 N K p *
          concreteCenteredEll 3 N K p| := by
  let x := concreteCenteredEll 1 N K p
  let y := concreteCenteredEll 2 N K p
  let z := concreteCenteredEll 3 N K p
  have hYoung : |x ^ 2 * y| ≤ (1 / 2 : ℝ) * (x ^ 4 + y ^ 2) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg x)]
    nlinarith [sq_nonneg (x ^ 2 - |y|), sq_abs y]
  have hTri :
      |x ^ 4 + 6 * x ^ 2 * y + 3 * y ^ 2 + 4 * x * z| ≤
        |x ^ 4| + |6 * x ^ 2 * y| + |3 * y ^ 2| + |4 * x * z| := by
    calc
      |x ^ 4 + 6 * x ^ 2 * y + 3 * y ^ 2 + 4 * x * z| ≤
          |x ^ 4 + 6 * x ^ 2 * y + 3 * y ^ 2| + |4 * x * z| :=
        abs_add_le _ _
      _ ≤ (|x ^ 4 + 6 * x ^ 2 * y| + |3 * y ^ 2|) + |4 * x * z| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ ((|x ^ 4| + |6 * x ^ 2 * y|) + |3 * y ^ 2|) + |4 * x * z| := by
        gcongr
        exact abs_add_le _ _
      _ = |x ^ 4| + |6 * x ^ 2 * y| + |3 * y ^ 2| + |4 * x * z| := by ring
  rw [Real.norm_eq_abs]
  change |x ^ 4 + 6 * x ^ 2 * y + 3 * y ^ 2 + 4 * x * z| ≤
    4 * x ^ 4 + 6 * y ^ 2 + 4 * |x * z|
  calc
    |x ^ 4 + 6 * x ^ 2 * y + 3 * y ^ 2 + 4 * x * z| ≤
        |x ^ 4| + |6 * x ^ 2 * y| + |3 * y ^ 2| + |4 * x * z| := hTri
    _ = x ^ 4 + 6 * |x ^ 2 * y| + 3 * y ^ 2 + 4 * |x * z| := by
      rw [abs_of_nonneg (by positivity : 0 ≤ x ^ 4)]
      norm_num [abs_mul, abs_of_nonneg (sq_nonneg x),
        abs_of_nonneg (sq_nonneg y)]
      ring
    _ ≤ 4 * x ^ 4 + 6 * y ^ 2 + 4 * |x * z| := by
      nlinarith [hYoung, sq_nonneg x, sq_nonneg y]

/-- Sharp three-monomial data assembles the aggregate lower-Bell package
whenever its exact coefficient budget fits the paper-facing constant. -/
theorem h11BellFourLowerMomentPackage_of_sharpMonomials
    {N K : ℕ} {C1 C2 C13 : ℝ}
    (hN : 1 ≤ N)
    (H : H11BellLowerSharpMonomialPackage N K C1 C2 C13)
    (hbudget : 4 * C1 + 6 * C2 + 4 * C13 ≤
      centeredLogScoreFourthMomentConstant) :
    H11BellFourLowerMomentPackage N K := by
  let law := concreteCenteredScoreProductLaw N K
  let f1 : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun p ↦ concreteCenteredEll 1 N K p ^ 4
  let f2 : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun p ↦ concreteCenteredEll 2 N K p ^ 2
  let f13 : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun p ↦ concreteCenteredEll 1 N K p * concreteCenteredEll 3 N K p
  let envelope : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    (4 : ℝ) • f1 + (6 : ℝ) • f2 +
      (4 : ℝ) • (fun p ↦ ‖f13 p‖)
  have hf1 : MemLp f1 1 law := by simpa only [f1, law] using H.oneFourth_memLp
  have hf2 : MemLp f2 1 law := by simpa only [f2, law] using H.twoSquare_memLp
  have hf13 : MemLp f13 1 law := by simpa only [f13, law] using H.oneThree_memLp
  have he1 : MemLp ((4 : ℝ) • f1) 1 law := hf1.const_smul 4
  have he2 : MemLp ((6 : ℝ) • f2) 1 law := hf2.const_smul 6
  have he13 : MemLp ((4 : ℝ) • (fun p ↦ ‖f13 p‖)) 1 law :=
    hf13.norm.const_smul 4
  have hEnvelope : MemLp envelope 1 law := by
    exact (he1.add he2).add he13
  have hLowerMeas : AEStronglyMeasurable
      (concreteCenteredBellFourLowerProduct N K) law := by
    have h1 := measurable_concreteCenteredEll_one (N := N) (K := K) hN
    have h2 := measurable_concreteCenteredEll_two (N := N) (K := K) hN
    have h3 := measurable_concreteCenteredEll_three (N := N) (K := K) hN
    exact (((((h1.pow_const 4).add
      (((h1.pow_const 2).const_mul 6).mul h2)).add
      ((h2.pow_const 2).const_mul 3)).add
      ((h1.const_mul 4).mul h3))).aestronglyMeasurable
  have hdom : ∀ p, ‖concreteCenteredBellFourLowerProduct N K p‖ ≤
      envelope p := by
    intro p
    simpa only [envelope, f1, f2, f13, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Real.norm_eq_abs] using
      concreteCenteredBellFourLowerProduct_norm_le_sharpEnvelope
        (N := N) (K := K) p
  have hLower : MemLp (concreteCenteredBellFourLowerProduct N K) 1 law := by
    apply hEnvelope.of_le hLowerMeas
    exact Filter.Eventually.of_forall fun p ↦ by
      have hp := hdom p
      have hnonneg : 0 ≤ envelope p := by
        simp only [envelope, f1, f2, f13, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul]
        positivity
      simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hp
  refine ⟨by simpa only [law] using hLower, ?_⟩
  intro hdense
  have hf1Bound : lpNorm f1 1 law ≤ C1 * (N : ℝ) ^ 2 := by
    simpa only [f1, law] using H.oneFourth_lpNorm_le hdense
  have hf2Bound : lpNorm f2 1 law ≤ C2 * (N : ℝ) ^ 2 := by
    simpa only [f2, law] using H.twoSquare_lpNorm_le hdense
  have hf13Bound : lpNorm f13 1 law ≤ C13 * (N : ℝ) ^ 2 := by
    simpa only [f13, law] using H.oneThree_lpNorm_le hdense
  have hmono : lpNorm (concreteCenteredBellFourLowerProduct N K) 1 law ≤
      lpNorm envelope 1 law := lpNorm_mono_real hEnvelope hdom
  have hsum1 : lpNorm (((4 : ℝ) • f1) + (6 : ℝ) • f2) 1 law ≤
      lpNorm ((4 : ℝ) • f1) 1 law + lpNorm ((6 : ℝ) • f2) 1 law :=
    lpNorm_add_le he1 (by norm_num)
  have hsum2 : lpNorm envelope 1 law ≤
      lpNorm (((4 : ℝ) • f1) + (6 : ℝ) • f2) 1 law +
        lpNorm ((4 : ℝ) • (fun p ↦ ‖f13 p‖)) 1 law := by
    exact lpNorm_add_le (he1.add he2) (by norm_num)
  have hsum : lpNorm envelope 1 law ≤
      lpNorm ((4 : ℝ) • f1) 1 law + lpNorm ((6 : ℝ) • f2) 1 law +
        lpNorm ((4 : ℝ) • (fun p ↦ ‖f13 p‖)) 1 law := by
    calc
      lpNorm envelope 1 law ≤
          lpNorm (((4 : ℝ) • f1) + (6 : ℝ) • f2) 1 law +
            lpNorm ((4 : ℝ) • (fun p ↦ ‖f13 p‖)) 1 law := hsum2
      _ ≤ (lpNorm ((4 : ℝ) • f1) 1 law +
            lpNorm ((6 : ℝ) • f2) 1 law) +
            lpNorm ((4 : ℝ) • (fun p ↦ ‖f13 p‖)) 1 law := by
        gcongr
  have hscaled :
      lpNorm ((4 : ℝ) • f1) 1 law + lpNorm ((6 : ℝ) • f2) 1 law +
          lpNorm ((4 : ℝ) • (fun p ↦ ‖f13 p‖)) 1 law =
        4 * lpNorm f1 1 law + 6 * lpNorm f2 1 law + 4 * lpNorm f13 1 law := by
    rw [lpNorm_const_smul, lpNorm_const_smul, lpNorm_const_smul,
      lpNorm_norm hf13.aestronglyMeasurable]
    norm_num
  have hcoeff :
      4 * lpNorm f1 1 law + 6 * lpNorm f2 1 law + 4 * lpNorm f13 1 law ≤
        (4 * C1 + 6 * C2 + 4 * C13) * (N : ℝ) ^ 2 := by
    nlinarith [hf1Bound, hf2Bound, hf13Bound]
  have hbudgetN :
      (4 * C1 + 6 * C2 + 4 * C13) * (N : ℝ) ^ 2 ≤
        centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right hbudget (sq_nonneg (N : ℝ))
  change lpNorm (concreteCenteredBellFourLowerProduct N K) 1 law ≤ _
  exact hmono.trans (hsum.trans_eq hscaled)
    |>.trans hcoeff |>.trans hbudgetN

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

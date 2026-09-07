import LogdetLean.GramHafnian.UltimateHiding.DenseScore.COELikelihoodAlgebra
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Tactic

/-!
# Fourth Bell-score closure from explicit log-score monomials

The fourth density score is not an input here.  The five fields below are the
literal five monomials in the fourth Bell polynomial.  In the concrete COE
application their bounds follow from the fixed log-score moments in (R23)
and ordinary Holder inequalities.  This file proves the Bell-polynomial
assembly internally.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-- Primitive fixed-degree monomial moments for the fourth logarithmic Bell
polynomial.  Unlike an arbitrary term ledger, every function is fixed
literally by `ellOne`, ..., `ellFour`. -/
structure FourthLogScoreProductMoments
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (N COne COneTwo CTwo COneThree CFour : ℝ)
    (ellOne ellTwo ellThree ellFour : Omega → ℝ) : Prop where
  oneFourth_memLp : MemLp (fun ω ↦ ellOne ω ^ 4) 1 mu
  oneSquareTwo_memLp : MemLp (fun ω ↦ ellOne ω ^ 2 * ellTwo ω) 1 mu
  twoSquare_memLp : MemLp (fun ω ↦ ellTwo ω ^ 2) 1 mu
  oneThree_memLp : MemLp (fun ω ↦ ellOne ω * ellThree ω) 1 mu
  four_memLp : MemLp ellFour 1 mu
  oneFourth_lpNorm_le :
    lpNorm (fun ω ↦ ellOne ω ^ 4) 1 mu ≤ COne * N ^ 2
  oneSquareTwo_lpNorm_le :
    lpNorm (fun ω ↦ ellOne ω ^ 2 * ellTwo ω) 1 mu ≤ COneTwo * N ^ 2
  twoSquare_lpNorm_le :
    lpNorm (fun ω ↦ ellTwo ω ^ 2) 1 mu ≤ CTwo * N ^ 2
  oneThree_lpNorm_le :
    lpNorm (fun ω ↦ ellOne ω * ellThree ω) 1 mu ≤ COneThree * N ^ 2
  four_lpNorm_le : lpNorm ellFour 1 mu ≤ CFour * N ^ 2

namespace FourthLogScoreProductMoments

variable {Omega : Type*} [MeasurableSpace Omega]
variable {mu : Measure Omega}
variable {N COne COneTwo CTwo COneThree CFour : ℝ}
variable {ellOne ellTwo ellThree ellFour : Omega → ℝ}

set_option maxHeartbeats 1000000 in
/-- Exact Bell-four closure; this is the internal step yielding (R24) once
the five primitive monomial moments are instantiated. -/
theorem bellFour_lpNorm_one_le
    (H : FourthLogScoreProductMoments mu N COne COneTwo CTwo COneThree CFour
      ellOne ellTwo ellThree ellFour) :
    lpNorm (fun ω ↦ densityBellFour
        (ellOne ω) (ellTwo ω) (ellThree ω) (ellFour ω)) 1 mu ≤
      (COne + 6 * COneTwo + 3 * CTwo + 4 * COneThree + CFour) * N ^ 2 := by
  let fOne : Omega → ℝ := fun ω ↦ ellOne ω ^ 4
  let fOneTwo : Omega → ℝ := fun ω ↦ ellOne ω ^ 2 * ellTwo ω
  let fTwo : Omega → ℝ := fun ω ↦ ellTwo ω ^ 2
  let fOneThree : Omega → ℝ := fun ω ↦ ellOne ω * ellThree ω
  let fFour : Omega → ℝ := ellFour
  have hpoint :
      (fun ω ↦ densityBellFour
        (ellOne ω) (ellTwo ω) (ellThree ω) (ellFour ω)) =
      fOne + (6 : ℝ) • fOneTwo + (3 : ℝ) • fTwo +
        (4 : ℝ) • fOneThree + fFour := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply]
    simp only [densityBellFour, fOne, fOneTwo, fTwo, fOneThree, fFour]
    ring
  rw [hpoint]
  have h1 : MemLp fOne 1 mu := H.oneFourth_memLp
  have h12 : MemLp fOneTwo 1 mu := H.oneSquareTwo_memLp
  have h2 : MemLp fTwo 1 mu := H.twoSquare_memLp
  have h13 : MemLp fOneThree 1 mu := H.oneThree_memLp
  have h4 : MemLp fFour 1 mu := H.four_memLp
  have hm12 : MemLp (fOne + (6 : ℝ) • fOneTwo) 1 mu :=
    h1.add (h12.const_smul (6 : ℝ))
  have hm2 : MemLp (fOne + (6 : ℝ) • fOneTwo + (3 : ℝ) • fTwo) 1 mu :=
    hm12.add (h2.const_smul (3 : ℝ))
  have hm13 : MemLp (fOne + (6 : ℝ) • fOneTwo + (3 : ℝ) • fTwo +
      (4 : ℝ) • fOneThree) 1 mu :=
    hm2.add (h13.const_smul (4 : ℝ))
  have hadd4 :
      lpNorm (fOne + (6 : ℝ) • fOneTwo + (3 : ℝ) • fTwo +
          (4 : ℝ) • fOneThree + fFour) 1 mu ≤
        lpNorm (fOne + (6 : ℝ) • fOneTwo + (3 : ℝ) • fTwo +
          (4 : ℝ) • fOneThree) 1 mu + lpNorm fFour 1 mu :=
    lpNorm_add_le hm13 (by norm_num)
  have hadd3 :
      lpNorm (fOne + (6 : ℝ) • fOneTwo + (3 : ℝ) • fTwo +
          (4 : ℝ) • fOneThree) 1 mu ≤
        lpNorm (fOne + (6 : ℝ) • fOneTwo + (3 : ℝ) • fTwo) 1 mu +
          lpNorm ((4 : ℝ) • fOneThree) 1 mu :=
    lpNorm_add_le hm2 (by norm_num)
  have hadd2 :
      lpNorm (fOne + (6 : ℝ) • fOneTwo + (3 : ℝ) • fTwo) 1 mu ≤
        lpNorm (fOne + (6 : ℝ) • fOneTwo) 1 mu +
          lpNorm ((3 : ℝ) • fTwo) 1 mu :=
    lpNorm_add_le hm12 (by norm_num)
  have hadd1 :
      lpNorm (fOne + (6 : ℝ) • fOneTwo) 1 mu ≤
        lpNorm fOne 1 mu + lpNorm ((6 : ℝ) • fOneTwo) 1 mu :=
    lpNorm_add_le h1 (by norm_num)
  have htotal :
      lpNorm (fOne + (6 : ℝ) • fOneTwo + (3 : ℝ) • fTwo +
          (4 : ℝ) • fOneThree + fFour) 1 mu ≤
        (((lpNorm fOne 1 mu + lpNorm ((6 : ℝ) • fOneTwo) 1 mu) +
          lpNorm ((3 : ℝ) • fTwo) 1 mu) +
          lpNorm ((4 : ℝ) • fOneThree) 1 mu) +
          lpNorm fFour 1 mu := by
    linarith [hadd4, hadd3, hadd2, hadd1]
  simp only [lpNorm_const_smul] at htotal
  norm_num at htotal
  calc
    lpNorm (fOne + (6 : ℝ) • fOneTwo + (3 : ℝ) • fTwo +
        (4 : ℝ) • fOneThree + fFour) 1 mu ≤
        (((COne * N ^ 2 + 6 * (COneTwo * N ^ 2)) +
          3 * (CTwo * N ^ 2)) + 4 * (COneThree * N ^ 2)) +
          CFour * N ^ 2 := by
      linarith [H.oneFourth_lpNorm_le, H.oneSquareTwo_lpNorm_le,
        H.twoSquare_lpNorm_le, H.oneThree_lpNorm_le, H.four_lpNorm_le]
    _ = (COne + 6 * COneTwo + 3 * CTwo + 4 * COneThree + CFour) * N ^ 2 := by
      ring

end FourthLogScoreProductMoments

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

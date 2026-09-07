import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11H13_ExactIndependentReduction
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredLogScoreOneSquareTwoDerived
import Mathlib.Tactic

/-!
# H11 reduction after internal fourth-score measurability

The total literal fourth log score is now known to be measurable by the
finite-difference construction in `CenteredLogScoreOneSquareTwoDerived`.
Consequently the remaining deterministic H11 input is only the pointwise
open-support operator-radius estimate below.

There is no probability or scientific axiom in this file.
-/

open MeasureTheory
open Filter Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Public determinant-log jet underlying every centered log score. -/
def concreteCenteredLogDeterminantJet (r N K : ℕ)
    (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) : ℝ :=
  iteratedDeriv r (fun t : ℝ => Real.log
    (concreteCOECenteredInverseDeterminant K v t A)) 0

/-- On the open support, the literal fourth log score is the determinant-log
fourth jet multiplied by the Friedman--Mello exponent. -/
theorem concreteCenteredEll_four_eq_logDeterminantJet_h11_internal
    {N K : ℕ} (hN : 1 ≤ N)
    (A : ConcreteMatrixState N) (v : ComplexUnitSphere N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredEll 4 N K (A, v) =
      coeCornerDensityExponent N K *
        concreteCenteredLogDeterminantJet 4 N K v A := by
  let d : ℝ → ℝ := fun t =>
    concreteCOECenteredInverseDeterminant K v t A
  let p : ℝ := coeCornerDensityExponent N K
  let L : ℝ → ℝ := fun t => p * (Real.log (d t) - Real.log (d 0))
  have hd0 : d 0 = concreteCOEBaseDeterminant K A := by
    simp [d, concreteCOECenteredInverseDeterminant,
      concreteCOEBaseDeterminant, transposeCongruenceFlow,
      transposeCongruence]
  have hbasePos : 0 < d 0 := by
    rw [hd0]
    unfold concreteCOEBaseDeterminant
    exact (RCLike.lt_iff_re_im.mp hsupport.det_pos).1
  have hdSmooth : ContDiff ℝ ⊤ d := by
    dsimp only [d, concreteCOECenteredInverseDeterminant]
    simp_rw [transposeCongruenceFlow_centered_eq_concreteOrbitalMatrixUpdate hN]
    simp only [concreteOrbitalMatrixUpdate, concreteOrbitalFactor,
      Matrix.det_apply, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.transpose_apply,
      Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply]
    apply Complex.reCLM.contDiff.comp
    fun_prop
  have hdcont : ContinuousAt d 0 := hdSmooth.continuous.continuousAt
  have hpos : ∀ᶠ t in nhds 0, 0 < d t :=
    continuousAt_const.eventually_lt hdcont hbasePos
  have hlike :
      (fun t => Real.log (concreteCenteredLikelihoodCore K v t A)) =ᶠ[nhds 0]
        L := by
    filter_upwards [hpos] with t ht
    have hratio : 0 < d t / d 0 := div_pos ht hbasePos
    unfold L p
    rw [show concreteCenteredLikelihoodCore K v t A =
        Real.rpow (d t / d 0) (coeCornerDensityExponent N K) by
      unfold concreteCenteredLikelihoodCore
      rw [if_neg (ne_of_gt (by simpa [hd0] using hbasePos))]
      congr 2
      exact hd0.symm]
    rw [show Real.log (Real.rpow (d t / d 0)
          (coeCornerDensityExponent N K)) =
        coeCornerDensityExponent N K * Real.log (d t / d 0) by
      exact Real.log_rpow hratio _]
    rw [Real.log_div (ne_of_gt ht) (ne_of_gt hbasePos)]
  unfold concreteCenteredEll concreteCenteredLogScore
  rw [hlike.iteratedDeriv_eq 4]
  unfold L
  rw [iteratedDeriv_const_mul_field]
  have hsub : iteratedDeriv 4
      (fun t => Real.log (d t) - Real.log (d 0)) 0 =
      iteratedDeriv 4 (fun t => Real.log (d t)) 0 := by
    simpa [sub_eq_add_neg, add_comm] using
      (iteratedDeriv_const_add (f := fun t => Real.log (d t))
        (x := (0 : ℝ)) (n := 4) (by norm_num) (-Real.log (d 0)))
  rw [hsub]
  rfl

/-- Score-free form of the remaining H11 pointwise calculation. -/
structure H11FourthLogDeterminantJetEnvelope (N K : ℕ) : Prop where
  abs_le_on_support :
    ∀ (A : ConcreteMatrixState N) (v : ComplexUnitSphere N),
      coeCornerSupport (unscaleCOECorner K A) →
      |concreteCenteredLogDeterminantJet 4 N K v A| ≤
        8192 *
          (concreteHigherScoreOpRadius N K A /
            concreteCOEExponent N K) *
          (1 + concreteHigherScoreOpRadius N K A /
            concreteCOEExponent N K) ^ 3

/-- The determinant-jet estimate gives the exact literal fourth-score radial
bound. -/
theorem concreteCenteredEll_four_abs_le_of_logDeterminantJet_h11
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N) (v : ComplexUnitSphere N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    (hjet :
      |concreteCenteredLogDeterminantJet 4 N K v A| ≤
        8192 *
          (concreteHigherScoreOpRadius N K A /
            concreteCOEExponent N K) *
          (1 + concreteHigherScoreOpRadius N K A /
            concreteCOEExponent N K) ^ 3) :
    |concreteCenteredEll 4 N K (A, v)| ≤
      h11HigherScoreRadialEnvelope N K A := by
  let c : ℝ := concreteCOEExponent N K
  let r : ℝ := concreteHigherScoreOpRadius N K A
  let b : ℝ := 1 + r / c
  have hc : 0 < c := by
    simpa only [c] using concreteCOEExponent_pos_of_higherScoreGap hgap
  have hp_eq : coeCornerDensityExponent N K = c / 2 := by
    rfl
  have hp : 0 ≤ coeCornerDensityExponent N K := by
    rw [hp_eq]
    positivity
  rw [concreteCenteredEll_four_eq_logDeterminantJet_h11_internal
    hN A v hsupport, abs_mul, abs_of_nonneg hp]
  change coeCornerDensityExponent N K *
      |concreteCenteredLogDeterminantJet 4 N K v A| ≤ _
  calc
    coeCornerDensityExponent N K *
        |concreteCenteredLogDeterminantJet 4 N K v A| ≤
        coeCornerDensityExponent N K *
          (8192 * (r / c) * b ^ 3) :=
      mul_le_mul_of_nonneg_left (by simpa only [r, c, b] using hjet) hp
    _ = 4096 * r * b ^ 3 := by
      rw [hp_eq]
      field_simp [ne_of_gt hc]
      <;> ring
    _ = h11HigherScoreRadialEnvelope N K A := by
      unfold h11HigherScoreRadialEnvelope
      rfl

/-- The sole remaining deterministic H11 calculation after measurability is
proved internally. -/
structure H11FourthScoreSupportEnvelope (N K : ℕ) : Prop where
  abs_le_on_support :
    ∀ (A : ConcreteMatrixState N) (v : ComplexUnitSphere N),
      (unscaleCOECorner K A).IsSymm →
      coeCornerSupport (unscaleCOECorner K A) →
      |concreteCenteredEll 4 N K (A, v)| ≤
        h11HigherScoreRadialEnvelope N K A

/-- The score-free determinant-jet package supplies the support-only H11
envelope. -/
theorem h11FourthScoreSupportEnvelope_of_logDeterminantJet
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (H : H11FourthLogDeterminantJetEnvelope N K) :
    H11FourthScoreSupportEnvelope N K where
  abs_le_on_support := by
    intro A v _hsymm hsupport
    exact concreteCenteredEll_four_abs_le_of_logDeterminantJet_h11
      hN hgap A v hsupport (H.abs_le_on_support A v hsupport)

/-- The support-only envelope supplies the former two-field H11
deterministic interface; fourth-score measurability is no longer assumed. -/
theorem h11HigherScoreDeterministicEnvelope_of_supportEnvelope
    {N K : ℕ} (hN : 1 ≤ N)
    (H : H11FourthScoreSupportEnvelope N K) :
    H11HigherScoreDeterministicEnvelope N K where
  measurable_score := measurable_concreteCenteredEll_four hN
  abs_le_on_support := H.abs_le_on_support

/-- Direct H11 endpoint reducer whose only deterministic hypothesis is the
literal pointwise support estimate. -/
theorem centeredLogScore_four_momentPackage_of_opRadiusL4_and_supportEnvelope
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (Hradius : ConcreteHigherScoreOpRadiusL4Package N K)
    (Hsupport : H11FourthScoreSupportEnvelope N K) :
    MemLp (concreteCenteredEll 4 N K) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (concreteCenteredEll 4 N K) 1
            (concreteCenteredScoreProductLaw N K) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) :=
  centeredLogScore_four_momentPackage_of_opRadiusL4_and_deterministic
    hN hgap Hradius
      (h11HigherScoreDeterministicEnvelope_of_supportEnvelope hN Hsupport)

/-- Direct H11 reducer with a score-free determinant-log fourth-jet
hypothesis. -/
theorem centeredLogScore_four_momentPackage_of_opRadiusL4_and_logDeterminantJet
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (Hradius : ConcreteHigherScoreOpRadiusL4Package N K)
    (Hjet : H11FourthLogDeterminantJetEnvelope N K) :
    MemLp (concreteCenteredEll 4 N K) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (concreteCenteredEll 4 N K) 1
            (concreteCenteredScoreProductLaw N K) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) :=
  centeredLogScore_four_momentPackage_of_opRadiusL4_and_supportEnvelope
    hN hgap Hradius
      (h11FourthScoreSupportEnvelope_of_logDeterminantJet hN hgap Hjet)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

import LogdetLean.GramHafnian.UltimateHiding.DenseScore.MatsumotoWishartPushforward
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.InverseWishartEntryProductIntegrability
import Mathlib.Tactic

/-!
# Internal closure of the Matsumoto A4 inverse-trace integrability premise

The checked inverse-Wishart entry-product engine already proves fourth
inverse-Gram trace integrability under the half-Gaussian source at the exact
threshold used by the A4 specialization.  This module transports that fact
through the proved positive-definite Gram lift and its pushforward law.

No determinant Laplace transform, literature atom, or endpoint declaration
is introduced here.
-/

open MeasureTheory
open scoped BigOperators Matrix

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart

private theorem matsumoto_trace_pow_four_eq_cycleSum
    {d : Nat} (A : Matrix (Fin d) (Fin d) Real) :
    Matrix.trace (A ^ 4) =
      ∑ a : Fin d, ∑ e : Fin d, ∑ c : Fin d, ∑ b : Fin d,
        A a b * A b c * A c e * A e a := by
  simp [Matrix.trace, Matrix.mul_apply, pow_succ, Finset.sum_mul]

private theorem integrable_halfGaussian_inverseWishart_entryProduct_four_cycle
    {k d : Nat} (hgap : d + 8 <= k) (a e c b : Fin d) :
    Integrable
      (fun R : Matrix (Fin k) (Fin d) Real =>
        (realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ b c *
          (realWishartGram R)⁻¹ c e * (realWishartGram R)⁻¹ e a)
      (halfGaussianMatrix k d) := by
  let indices : Fin 4 → Fin d × Fin d :=
    ![(a, b), (b, c), (c, e), (e, a)]
  have hbase :=
    U08.integrable_inverseWishartEntryProduct_halfGaussianMatrix
      (k := k) (p := d) (q := 4) hgap indices
  apply hbase.congr
  filter_upwards [] with R
  simp [indices, U08.inverseWishartEntryProduct, Fin.prod_univ_four]

private theorem integrable_halfGaussian_inverseWishart_trace_four_internal
    {k d : Nat} (hgap : d + 8 <= k) :
    Integrable
      (fun R : Matrix (Fin k) (Fin d) Real =>
        Matrix.trace (((realWishartGram R)⁻¹) ^ 4))
      (halfGaussianMatrix k d) := by
  rw [show (fun R : Matrix (Fin k) (Fin d) Real =>
      Matrix.trace (((realWishartGram R)⁻¹) ^ 4)) =
      fun R => ∑ a : Fin d, ∑ e : Fin d, ∑ c : Fin d, ∑ b : Fin d,
        (realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ b c *
          (realWishartGram R)⁻¹ c e * (realWishartGram R)⁻¹ e a by
    funext R
    exact matsumoto_trace_pow_four_eq_cycleSum (realWishartGram R)⁻¹]
  exact integrable_finsetSum Finset.univ fun a ha =>
    integrable_finsetSum Finset.univ fun e he =>
      integrable_finsetSum Finset.univ fun c hc =>
        integrable_finsetSum Finset.univ fun b hb =>
          integrable_halfGaussian_inverseWishart_entryProduct_four_cycle
            hgap a e c b

/-- The literal paper-side inverse trace-four integrand is measurable. -/
theorem measurable_matsumotoPaperInverseTraceFourIntegrand (d : Nat) :
    Measurable (matsumotoPaperInverseTraceFourIntegrand d) := by
  have hmatrixInv : @Measurable
      (MatsumotoPaper.RealMatrix d) (MatsumotoPaper.RealMatrix d)
      (MatsumotoPaper.instMeasurableSpaceRealMatrix d)
      (MatsumotoPaper.instMeasurableSpaceRealMatrix d)
      (fun A => A⁻¹) := by
    rw [← projectRealMatrixMeasurableSpace_eq_matsumoto d]
    exact measurable_realMatrix_inv d
  have hinv : Measurable
      (fun w : MatsumotoPaper.SymPosDef d => w.1⁻¹) :=
    hmatrixInv.comp measurable_subtype_coe
  have hcoordinate (a b : Fin d) : Measurable
      (fun A : MatsumotoPaper.RealMatrix d => A a b) := by
    rw [← projectRealMatrixMeasurableSpace_eq_matsumoto d]
    exact (measurable_pi_apply b).comp (measurable_pi_apply a)
  have hentry (a b : Fin d) : Measurable
      (fun w : MatsumotoPaper.SymPosDef d => w.1⁻¹ a b) :=
    (hcoordinate a b).comp hinv
  unfold matsumotoPaperInverseTraceFourIntegrand MatsumotoPaper.T
    MatsumotoPaper.SymPosDef.inverse
  apply Finset.measurable_sum
  intro j hj
  apply Measurable.mul
  · exact Finset.measurable_prod _ fun i hi => measurable_const
  · apply Finset.measurable_prod
    intro i hi
    exact RCLike.measurable_ofReal.comp
      (hentry
        (j (matsumotoTraceFourPermutation (MatsumotoPaper.leftSlot i)))
        (j (matsumotoTraceFourPermutation (MatsumotoPaper.rightSlot i))))

/-- The source-side checked fourth inverse-trace moment transports to any
literal Matsumoto law certified by the proved half-Gaussian Gram pushforward. -/
theorem matsumotoPaperInverseTraceFour_integrable_of_halfGaussianPushforward
    {d k : Nat} (hgap : d + 8 <= k)
    (law : HalfGaussianMatsumotoWishartPushforward d k) :
    Integrable (matsumotoPaperInverseTraceFourIntegrand d)
      law.W.toMeasure := by
  have hrawReal : Integrable
      (fun R : Matrix (Fin k) (Fin d) Real =>
        Matrix.trace (((realWishartGram R)⁻¹) ^ 4))
      (halfGaussianMatrix k d) :=
    integrable_halfGaussian_inverseWishart_trace_four_internal hgap
  have hrawComplex : Integrable
      (fun R : Matrix (Fin k) (Fin d) Real =>
        ((Matrix.trace (((realWishartGram R)⁻¹) ^ 4) : Real) : Complex))
      (halfGaussianMatrix k d) :=
    hrawReal.ofReal
  have hcomp : Integrable
      (fun R : Matrix (Fin k) (Fin d) Real =>
        matsumotoPaperInverseTraceFourIntegrand d (law.gramLift R))
      (halfGaussianMatrix k d) := by
    apply hrawComplex.congr
    exact (matsumotoPaperInverseTraceFour_comp_gramLift_ae law).symm
  have hmap : Integrable (matsumotoPaperInverseTraceFourIntegrand d)
      (Measure.map law.gramLift (halfGaussianMatrix k d)) := by
    apply (integrable_map_measure
      (measurable_matsumotoPaperInverseTraceFourIntegrand d).aestronglyMeasurable
      law.measurable_gramLift.aemeasurable).2
    change Integrable
      (fun R : Matrix (Fin k) (Fin d) Real =>
        matsumotoPaperInverseTraceFourIntegrand d (law.gramLift R))
      (halfGaussianMatrix k d)
    exact hcomp
  rwa [law.map_eq] at hmap

/-- A4 now consumes only the proved Gaussian-to-Matsumoto pushforward law;
the former separate paper-side integrability premise is internal. -/
theorem h12h14_matsumotoIdentityTraceFourMoment_of_A4_of_pushforward
    {d k : Nat} (hd : 0 < d) (hgap : d + 7 < k)
    (law : HalfGaussianMatsumotoWishartPushforward d k) :
    H12H14MatsumotoIdentityTraceFourMoment d k
      (halfGaussianMatsumotoGamma d k)
      (matsumotoA4TraceFourValue d k) := by
  apply h12h14_matsumotoIdentityTraceFourMoment_of_A4 hd hgap law
  exact matsumotoPaperInverseTraceFour_integrable_of_halfGaussianPushforward
    (by omega) law

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

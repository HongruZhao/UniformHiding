import LogdetLean.GramHafnian.UltimateHiding.DenseScore.MatsumotoTheorem3ProjectBridge

/-!
# Half-Gaussian Gram to literal Matsumoto Wishart

This module isolates the exact remaining source-side law conversion.  It
constructs the measurable positive-definite lift of `R^T R` on its singular
null set and packages the resulting pushforward as Matsumoto's literal
`W_d(k/2, I; R)` once the determinant Laplace transform is supplied.

The Laplace-transform hypothesis in the final theorem is written out
literally.  It is not an axiom or a replacement scientific interface.
-/

open MeasureTheory
open scoped Matrix

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart

/-- A nonsingular real Gram matrix is positive definite. -/
theorem realWishartGram_posDef_of_isUnit_det
    {d k : Nat} (R : Matrix (Fin k) (Fin d) Real)
    (hdet : IsUnit (realWishartGram R).det) :
    (realWishartGram R).PosDef := by
  have hunit : IsUnit (realWishartGram R) :=
    (realWishartGram R).isUnit_iff_isUnit_det.mpr hdet
  have hgramInjective :
      Function.Injective (realWishartGram R).mulVec :=
    Matrix.mulVec_injective_of_isUnit hunit
  have hRInjective : Function.Injective R.mulVec := by
    intro x y hxy
    apply hgramInjective
    simpa only [realWishartGram, ← Matrix.mulVec_mulVec] using
      congrArg (fun z => R.transpose *ᵥ z) hxy
  simpa [realWishartGram] using
    (Matrix.PosDef.conjTranspose_mul_self R hRInjective)

/--
Total positive-definite lift of the real Gram map.  On the singular set it
uses the identity matrix; the next theorem proves that this change occurs
only on a null set when `d <= k`.
-/
noncomputable def halfGaussianGramPosDefLift (d k : Nat)
    (R : Matrix (Fin k) (Fin d) Real) :
    MatsumotoPaper.SymPosDef d := by
  classical
  refine ⟨if (realWishartGram R).det = 0 then
      (1 : Matrix (Fin d) (Fin d) Real)
    else realWishartGram R, ?_⟩
  by_cases hzero : (realWishartGram R).det = 0
  · simpa [hzero, matsumotoIdentityScale] using
      (matsumotoIdentityScale d).2
  · simpa [hzero] using
      realWishartGram_posDef_of_isUnit_det R
        (isUnit_iff_ne_zero.mpr hzero)

private theorem measurableSet_eq_zero_det_realWishartGram (d k : Nat) :
    MeasurableSet
      {R : Matrix (Fin k) (Fin d) Real |
        (realWishartGram R).det = 0} := by
  have hdet : Measurable
      (fun R : Matrix (Fin k) (Fin d) Real =>
        (realWishartGram R).det) := by
    simp only [Matrix.det_apply', realWishartGram, Matrix.mul_apply,
      Matrix.transpose_apply]
    fun_prop
  have hset :
      {R : Matrix (Fin k) (Fin d) Real |
        (realWishartGram R).det = 0} =
        (fun R : Matrix (Fin k) (Fin d) Real =>
          (realWishartGram R).det) ⁻¹' ({0} : Set Real) := by
    ext R
    simp
  rw [hset]
  exact hdet (measurableSet_singleton (0 : Real))

/-- The project's concrete matrix measurable space is the Borel space used by
the literal Matsumoto development. -/
theorem projectRealMatrixMeasurableSpace_eq_matsumoto (d : Nat) :
    realMatrixMeasurableSpace (Fin d) (Fin d) =
      MatsumotoPaper.instMeasurableSpaceRealMatrix d := by
  change realMatrixMeasurableSpace (Fin d) (Fin d) =
    borel (Matrix (Fin d) (Fin d) Real)
  letI : MeasurableSpace (Matrix (Fin d) (Fin d) Real) :=
    realMatrixMeasurableSpace (Fin d) (Fin d)
  letI : BorelSpace (Matrix (Fin d) (Fin d) Real) := by
    change BorelSpace (Fin d -> Fin d -> Real)
    infer_instance
  exact BorelSpace.measurable_eq

/-- The null-set SPD lift is a measurable map into Matsumoto's cone. -/
theorem measurable_halfGaussianGramPosDefLift (d k : Nat) :
    Measurable (halfGaussianGramPosDefLift d k) := by
  classical
  have hgram : Measurable
      (realWishartGram :
        Matrix (Fin k) (Fin d) Real -> Matrix (Fin d) (Fin d) Real) :=
    by
      rw [← projectRealMatrixMeasurableSpace_eq_matsumoto d]
      exact measurable_realWishartGram_genericSteinHaff
  have hpiece : Measurable
      (fun R : Matrix (Fin k) (Fin d) Real =>
        if (realWishartGram R).det = 0 then
          (1 : Matrix (Fin d) (Fin d) Real)
        else
          realWishartGram R) :=
    Measurable.ite (measurableSet_eq_zero_det_realWishartGram d k)
      measurable_const hgram
  apply Measurable.subtype_mk
  exact hpiece

/-- The SPD lift agrees almost everywhere with the literal Gram matrix. -/
theorem halfGaussianGramPosDefLift_eq_gram_ae
    {d k : Nat} (hdk : d <= k) :
    ∀ᵐ R ∂halfGaussianMatrix k d,
      (halfGaussianGramPosDefLift d k R).1 = realWishartGram R := by
  classical
  filter_upwards
    [ae_isUnit_det_realWishartGram_halfGaussianMatrix k d hdk] with R hdet
  have hne : (realWishartGram R).det ≠ 0 := hdet.ne_zero
  simp [halfGaussianGramPosDefLift, hne]

/--
Exact conversion from the one remaining analytic identity to the literal
Matsumoto Wishart pushforward certificate.  The hypothesis is precisely the
determinant Laplace transform for the unmodified half-Gaussian Gram; all SPD
lifting, probability, pushforward, and almost-everywhere transport steps are
proved in this module.
-/
noncomputable def halfGaussianMatsumotoWishartPushforward_of_determinantLaplace
    {d k : Nat} (hdk : d <= k)
    (hlaplace :
      forall theta : MatsumotoPaper.Sym d,
        ((matsumotoIdentityScale d).1⁻¹ - theta.1).PosDef ->
          (∫ R : Matrix (Fin k) (Fin d) Real,
              MatsumotoPaper.etr (theta.1 * realWishartGram R)
              ∂halfGaussianMatrix k d) =
            Real.rpow
              (Matrix.det
                (1 - theta.1 * (matsumotoIdentityScale d).1))
              (-halfGaussianMatsumotoBeta k)) :
    HalfGaussianMatsumotoWishartPushforward d k := by
  let lift := halfGaussianGramPosDefLift d k
  have hliftMeas : Measurable lift := by
    simpa [lift] using measurable_halfGaussianGramPosDefLift d k
  have hliftAE :
      ∀ᵐ R ∂halfGaussianMatrix k d,
        (lift R).1 = realWishartGram R := by
    simpa [lift] using halfGaussianGramPosDefLift_eq_gram_ae hdk
  let W : MatsumotoPaper.W_d d (halfGaussianMatsumotoBeta k)
      (matsumotoIdentityScale d) :=
    { toMeasure := Measure.map lift (halfGaussianMatrix k d)
      probability := by
        exact Measure.isProbabilityMeasure_map hliftMeas.aemeasurable
      laplace_transform := by
        intro theta htheta
        have hmeas : Measurable
            (fun w : MatsumotoPaper.SymPosDef d =>
              MatsumotoPaper.etr (theta.1 * w.1)) := by
          have hmatrix : Measurable
              (fun A : MatsumotoPaper.RealMatrix d =>
                MatsumotoPaper.etr (theta.1 * A)) := by
            letI : BorelSpace (MatsumotoPaper.RealMatrix d) := ⟨rfl⟩
            apply Continuous.measurable
            unfold MatsumotoPaper.etr
            simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
            fun_prop
          exact hmatrix.comp measurable_subtype_coe
        rw [integral_map hliftMeas.aemeasurable
          hmeas.aestronglyMeasurable]
        calc
          (∫ R : Matrix (Fin k) (Fin d) Real,
              MatsumotoPaper.etr (theta.1 * (lift R).1)
              ∂halfGaussianMatrix k d) =
              ∫ R : Matrix (Fin k) (Fin d) Real,
                MatsumotoPaper.etr (theta.1 * realWishartGram R)
                ∂halfGaussianMatrix k d := by
            apply integral_congr_ae
            filter_upwards [hliftAE] with R hR
            rw [hR]
          _ = Real.rpow
                (Matrix.det
                  (1 - theta.1 * (matsumotoIdentityScale d).1))
                (-halfGaussianMatsumotoBeta k) :=
            hlaplace theta htheta }
  exact
    { gramLift := lift
      measurable_gramLift := hliftMeas
      gramLift_eq_gram := hliftAE
      W := W
      map_eq := rfl }

#print axioms realWishartGram_posDef_of_isUnit_det
#print axioms measurable_halfGaussianGramPosDefLift
#print axioms halfGaussianGramPosDefLift_eq_gram_ae
#print axioms halfGaussianMatsumotoWishartPushforward_of_determinantLaplace

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

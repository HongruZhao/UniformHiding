import LogdetLean.GramHafnian.UltimateHiding.DenseScore.MatsumotoWishartPushforward
import LogdetLean.GaussianPairLaplace
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-!
# The half-Gaussian Gram determinant Laplace transform

This file develops the remaining Gaussian transform needed to construct the
literal Matsumoto Wishart pushforward.  The proof is split into a scalar
Gaussian-square transform, orthogonal diagonalization of a symmetric tilt,
and finite-product transport over the iid matrix rows.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix RealInnerProductSpace

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart

/-- Exact square Laplace transform for one variance-one-half Gaussian. -/
theorem integral_exp_mul_sq_halfGaussian
    (lambda : Real) (hlambda : lambda < 1) :
    (∫ x : Real, Real.exp (lambda * x ^ 2)
        ∂gaussianReal 0 halfGaussianVariance) =
      (Real.sqrt (1 - lambda))⁻¹ := by
  let c : Real := (Real.sqrt 2)⁻¹
  have hcmeas : Measurable (fun x : Real => c * x) := by fun_prop
  have hfmeas : AEStronglyMeasurable
      (fun x : Real => Real.exp (lambda * x ^ 2))
      (Measure.map (fun x : Real => c * x) (gaussianReal 0 1)) := by
    exact (by fun_prop : Measurable
      (fun x : Real => Real.exp (lambda * x ^ 2))).aestronglyMeasurable
  rw [← map_invSqrtTwo_gaussianReal_zero_one]
  change (∫ x : Real, Real.exp (lambda * x ^ 2)
      ∂Measure.map (fun x : Real => c * x) (gaussianReal 0 1)) = _
  rw [integral_map hcmeas.aemeasurable hfmeas]
  have hA : -(1 / 2 : Real) < -lambda / 2 := by linarith
  have hbase := integral_exp_neg_mul_sq_add_mul_gaussianReal
    (-lambda / 2) 0 hA
  rw [gaussianQuadraticIntegral_zero _ hA] at hbase
  calc
    (∫ x : Real, Real.exp (lambda * (c * x) ^ 2)
        ∂gaussianReal 0 1) =
        ∫ x : Real, Real.exp (-(-lambda / 2) * x ^ 2 + 0 * x)
          ∂gaussianReal 0 1 := by
      apply integral_congr_ae
      filter_upwards [] with x
      congr 1
      dsimp [c]
      have hsqrt : Real.sqrt (2 : Real) ^ 2 = 2 := by norm_num
      rw [mul_pow, inv_pow, hsqrt]
      ring
    _ = (Real.sqrt (1 + 2 * (-lambda / 2)))⁻¹ := hbase
    _ = (Real.sqrt (1 - lambda))⁻¹ := by ring_nf

/-- Coordinates of a raw row in a Hermitian matrix's real eigenbasis. -/
private def halfGaussianEigenRotate {d : Nat}
    {theta : Matrix (Fin d) (Fin d) Real} (htheta : theta.IsHermitian) :
    (Fin d → Real) ≃ᵐ (Fin d → Real) :=
  (MeasurableEquiv.toLp 2 (Fin d → Real)).trans
    (htheta.eigenvectorBasis.repr.toMeasurableEquiv.trans
      (MeasurableEquiv.toLp 2 (Fin d → Real)).symm)

private theorem measurePreserving_halfGaussianEigenRotate {d : Nat}
    {theta : Matrix (Fin d) (Fin d) Real} (htheta : theta.IsHermitian) :
    MeasurePreserving (halfGaussianEigenRotate htheta)
      (Measure.pi (fun _ : Fin d =>
        gaussianReal 0 halfGaussianVariance))
      (Measure.pi (fun _ : Fin d =>
        gaussianReal 0 halfGaussianVariance)) := by
  let E := EuclideanSpace Real (Fin d)
  let c : Real := (Real.sqrt 2)⁻¹
  let scale : E → E := fun x => c • x
  let eLp := MeasurableEquiv.toLp 2 (Fin d → Real)
  let eRep := htheta.eigenvectorBasis.repr.toMeasurableEquiv
  let muScaled : Measure E := Measure.map scale (stdGaussian E)
  have hLp : MeasurePreserving eLp
      (Measure.pi (fun _ : Fin d =>
        gaussianReal 0 halfGaussianVariance)) muScaled := by
    refine ⟨eLp.measurable, ?_⟩
    change Measure.map (WithLp.toLp 2)
      (Measure.pi (fun _ : Fin d =>
        gaussianReal 0 halfGaussianVariance)) = muScaled
    simpa [eLp, muScaled, scale, E, c] using
      map_toLp_halfGaussianVector d
  have hRep : MeasurePreserving eRep muScaled muScaled := by
    refine ⟨eRep.measurable, ?_⟩
    have hscale : Measurable scale := by
      dsimp [scale]
      fun_prop
    have hcomm : (eRep ∘ scale) = (scale ∘ eRep) := by
      funext x
      change htheta.eigenvectorBasis.repr (c • x) =
        c • htheta.eigenvectorBasis.repr x
      exact map_smul _ _ _
    dsimp only [muScaled]
    rw [Measure.map_map eRep.measurable hscale]
    rw [hcomm]
    rw [← Measure.map_map hscale eRep.measurable]
    change Measure.map scale
      (Measure.map htheta.eigenvectorBasis.repr (stdGaussian E)) = _
    rw [stdGaussian_map htheta.eigenvectorBasis.repr]
  have hLpInv := MeasurePreserving.symm eLp hLp
  change MeasurePreserving
    (fun x => (htheta.eigenvectorBasis.repr (WithLp.toLp 2 x)).ofLp)
    (Measure.pi (fun _ : Fin d =>
      gaussianReal 0 halfGaussianVariance))
    (Measure.pi (fun _ : Fin d =>
      gaussianReal 0 halfGaussianVariance))
  exact hLpInv.comp (hRep.comp hLp)

private def halfGaussianRowsEigenRotate {k d : Nat}
    {theta : Matrix (Fin d) (Fin d) Real} (htheta : theta.IsHermitian) :
    (Fin k → Fin d → Real) ≃ᵐ (Fin k → Fin d → Real) :=
  MeasurableEquiv.piCongrRight (fun _ => halfGaussianEigenRotate htheta)

private def halfGaussianMatrixEigenRotate {k d : Nat}
    {theta : Matrix (Fin d) (Fin d) Real} (htheta : theta.IsHermitian)
    (R : Matrix (Fin k) (Fin d) Real) :
    Matrix (Fin k) (Fin d) Real :=
  fun a => halfGaussianEigenRotate htheta (R a)

private theorem halfGaussianMatrixEigenRotate_eq_mul {k d : Nat}
    {theta : Matrix (Fin d) (Fin d) Real} (htheta : theta.IsHermitian)
    (R : Matrix (Fin k) (Fin d) Real) :
    halfGaussianMatrixEigenRotate htheta R =
      R * (htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) Real) := by
  ext a i
  change (htheta.eigenvectorBasis.repr (WithLp.toLp 2 (R a))).ofLp i = _
  rw [OrthonormalBasis.repr_apply_apply]
  change inner Real (htheta.eigenvectorBasis i) (WithLp.toLp 2 (R a)) =
    ∑ j, R a j * Matrix.transpose
      (htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) Real) i j
  rw [htheta.eigenvectorUnitary_transpose_apply]
  simp [PiLp.inner_apply]

private theorem realWishartGram_halfGaussianMatrixEigenRotate {k d : Nat}
    {theta : Matrix (Fin d) (Fin d) Real} (htheta : theta.IsHermitian)
    (R : Matrix (Fin k) (Fin d) Real) :
    realWishartGram (halfGaussianMatrixEigenRotate htheta R) =
      star (htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) Real) *
        realWishartGram R *
          (htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) Real) := by
  rw [halfGaussianMatrixEigenRotate_eq_mul htheta R]
  simp only [realWishartGram, Matrix.transpose_mul, Matrix.mul_assoc]
  congr 1

private theorem trace_mul_eq_diagonal_eigenRotate {d : Nat}
    {theta W : Matrix (Fin d) (Fin d) Real} (htheta : theta.IsHermitian) :
    Matrix.trace (theta * W) =
      Matrix.trace (Matrix.diagonal htheta.eigenvalues *
        (star (htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) Real) * W *
          (htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) Real))) := by
  conv_lhs => rw [htheta.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply]
  change
    ((htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) Real) *
      Matrix.diagonal htheta.eigenvalues *
      star (htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) Real) * W).trace = _
  calc
    _ = ((htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) Real) *
          (Matrix.diagonal htheta.eigenvalues *
            star (htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) Real) * W)).trace := by
          simp only [Matrix.mul_assoc]
    _ = ((Matrix.diagonal htheta.eigenvalues *
            star (htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) Real) * W) *
          (htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) Real)).trace :=
          Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

/-- Pointwise diagonalization of the arbitrary symmetric quadratic tilt. -/
theorem trace_mul_realWishartGram_eq_sum_eigenRotate {k d : Nat}
    {theta : Matrix (Fin d) (Fin d) Real} (htheta : theta.IsHermitian)
    (R : Matrix (Fin k) (Fin d) Real) :
    Matrix.trace (theta * realWishartGram R) =
      ∑ a : Fin k, ∑ i : Fin d,
        htheta.eigenvalues i *
          (halfGaussianMatrixEigenRotate htheta R a i) ^ 2 := by
  rw [trace_mul_eq_diagonal_eigenRotate htheta]
  rw [← realWishartGram_halfGaussianMatrixEigenRotate htheta R]
  simp [realWishartGram, Matrix.trace, Matrix.mul_apply,
    Matrix.diagonal_apply, Finset.mul_sum, pow_two]
  rw [Finset.sum_comm]

private theorem measurePreserving_halfGaussianRowsEigenRotate {k d : Nat}
    {theta : Matrix (Fin d) (Fin d) Real} (htheta : theta.IsHermitian) :
    MeasurePreserving (halfGaussianRowsEigenRotate (k := k) htheta)
      (halfGaussianRowProduct k d) (halfGaussianRowProduct k d) := by
  change MeasurePreserving
    (fun R : Fin k → Fin d → Real =>
      fun a => halfGaussianEigenRotate htheta (R a))
    (halfGaussianRowProduct k d) (halfGaussianRowProduct k d)
  unfold halfGaussianRowProduct
  exact measurePreserving_pi
    (fun _ : Fin k => Measure.pi (fun _ : Fin d =>
      gaussianReal 0 halfGaussianVariance))
    (fun _ : Fin k => Measure.pi (fun _ : Fin d =>
      gaussianReal 0 halfGaussianVariance))
    (fun _ => measurePreserving_halfGaussianEigenRotate htheta)

private theorem integral_exp_sum_sq_halfGaussianRowProduct
    (k d : Nat) (lambda : Fin d → Real) :
    (∫ R : Fin k → Fin d → Real,
        Real.exp (∑ a : Fin k, ∑ i : Fin d,
          lambda i * (R a i) ^ 2)
        ∂halfGaussianRowProduct k d) =
      (∏ i : Fin d,
        ∫ x : Real, Real.exp (lambda i * x ^ 2)
          ∂gaussianReal 0 halfGaussianVariance) ^ k := by
  have hpoint : (fun R : Fin k → Fin d → Real =>
      Real.exp (∑ a : Fin k, ∑ i : Fin d,
        lambda i * (R a i) ^ 2)) =
      fun R => ∏ a : Fin k, ∏ i : Fin d,
        Real.exp (lambda i * (R a i) ^ 2) := by
    funext R
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro a ha
    rw [Real.exp_sum]
  rw [hpoint]
  unfold halfGaussianRowProduct
  let rowMeasure : Measure (Fin d → Real) :=
    Measure.pi (fun _ : Fin d => gaussianReal 0 halfGaussianVariance)
  let rowIntegrand : (Fin d → Real) → Real :=
    fun x => ∏ i : Fin d, Real.exp (lambda i * (x i) ^ 2)
  change (∫ R : Fin k → Fin d → Real,
      ∏ a : Fin k, rowIntegrand (R a)
      ∂Measure.pi (fun _ : Fin k => rowMeasure)) = _
  rw [integral_fintype_prod_eq_pow rowIntegrand]
  dsimp only [rowIntegrand, rowMeasure]
  rw [Fintype.card_fin]
  congr 1
  exact integral_fintype_prod_eq_prod
    (fun i : Fin d => fun x : Real =>
      Real.exp (lambda i * x ^ 2))

/-- The full matrix integral reduces exactly to the product of the scalar
Gaussian-square transforms in the eigenbasis of an arbitrary symmetric tilt. -/
theorem integral_etr_realWishartGram_eq_eigen_product
    {k d : Nat} {theta : Matrix (Fin d) (Fin d) Real}
    (htheta : theta.IsHermitian)
    (hlambda : ∀ i : Fin d, htheta.eigenvalues i < 1) :
    (∫ R : Matrix (Fin k) (Fin d) Real,
        MatsumotoPaper.etr (theta * realWishartGram R)
        ∂halfGaussianMatrix k d) =
      (∏ i : Fin d,
        (Real.sqrt (1 - htheta.eigenvalues i))⁻¹) ^ k := by
  let muRows := halfGaussianRowProduct k d
  let rotate := halfGaussianRowsEigenRotate (k := k) htheta
  let diagonalIntegrand : (Fin k → Fin d → Real) → Real :=
    fun R => Real.exp (∑ a : Fin k, ∑ i : Fin d,
      htheta.eigenvalues i * (R a i) ^ 2)
  have hcurried : MeasurePreserving (curriedMatrixMeasurableEquiv k d)
      muRows (halfGaussianMatrix k d) := by
    refine ⟨(curriedMatrixMeasurableEquiv k d).measurable, ?_⟩
    exact map_curriedMatrix_halfGaussianRowProduct k d
  calc
    (∫ R : Matrix (Fin k) (Fin d) Real,
        MatsumotoPaper.etr (theta * realWishartGram R)
        ∂halfGaussianMatrix k d) =
        ∫ R : Fin k → Fin d → Real,
          MatsumotoPaper.etr
            (theta * realWishartGram (curriedMatrixMeasurableEquiv k d R))
          ∂muRows := by
      symm
      exact hcurried.integral_comp'
        (fun R => MatsumotoPaper.etr (theta * realWishartGram R))
    _ = ∫ R : Fin k → Fin d → Real,
          diagonalIntegrand (rotate R) ∂muRows := by
      apply integral_congr_ae
      filter_upwards [] with R
      unfold MatsumotoPaper.etr diagonalIntegrand rotate
      rw [trace_mul_realWishartGram_eq_sum_eigenRotate htheta]
      rfl
    _ = ∫ R : Fin k → Fin d → Real,
          diagonalIntegrand R ∂muRows := by
      have hrot := (measurePreserving_halfGaussianRowsEigenRotate
        (k := k) htheta).integral_comp' diagonalIntegrand
      simpa [muRows, rotate] using hrot
    _ = (∏ i : Fin d,
          ∫ x : Real, Real.exp (htheta.eigenvalues i * x ^ 2)
            ∂gaussianReal 0 halfGaussianVariance) ^ k := by
      simpa [diagonalIntegrand, muRows] using
        (integral_exp_sum_sq_halfGaussianRowProduct
          k d htheta.eigenvalues)
    _ = (∏ i : Fin d,
        (Real.sqrt (1 - htheta.eigenvalues i))⁻¹) ^ k := by
      congr 2
      funext i
      exact integral_exp_mul_sq_halfGaussian _ (hlambda i)

/-- Positive definiteness of `I - theta` puts every eigenvalue of `theta`
strictly below one. -/
theorem eigenvalues_lt_one_of_one_sub_posDef {d : Nat}
    {theta : Matrix (Fin d) (Fin d) Real} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) (i : Fin d) :
    htheta.eigenvalues i < 1 := by
  let v : Fin d → Real := ⇑(htheta.eigenvectorBasis i)
  have hv : v ≠ 0 := by
    exact (WithLp.ofLp_eq_zero 2).ne.2 <|
      htheta.eigenvectorBasis.orthonormal.ne_zero i
  have hthetaV : theta *ᵥ v = (htheta.eigenvalues i) • v := by
    simpa [v] using htheta.mulVec_eigenvectorBasis i
  have honeSubV : (1 - theta) *ᵥ v =
      (1 - htheta.eigenvalues i) • v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hthetaV]
    ext j
    simp [sub_mul]
  have hquad := hpos.dotProduct_mulVec_pos hv
  rw [honeSubV] at hquad
  have hvdot : 0 < star v ⬝ᵥ v :=
    Matrix.dotProduct_star_self_pos_iff.mpr hv
  rw [dotProduct_smul] at hquad
  have hfactor : 0 < 1 - htheta.eigenvalues i := by
    change 0 < (1 - htheta.eigenvalues i) * (star v ⬝ᵥ v) at hquad
    nlinarith
  linarith

/-- Spectral determinant identity for an arbitrary real Hermitian tilt. -/
theorem det_one_sub_eq_prod_one_sub_eigenvalues {d : Nat}
    {theta : Matrix (Fin d) (Fin d) Real} (htheta : theta.IsHermitian) :
    Matrix.det (1 - theta) =
      ∏ i : Fin d, (1 - htheta.eigenvalues i) := by
  let U : Matrix (Fin d) (Fin d) Real := htheta.eigenvectorUnitary
  let D : Matrix (Fin d) (Fin d) Real :=
    Matrix.diagonal htheta.eigenvalues
  have hthetaSpec : theta = U * D * star U := by
    simpa [U, D, Unitary.conjStarAlgAut_apply] using htheta.spectral_theorem
  have hunit : U * star U = 1 := by
    dsimp [U]
    rw [← Unitary.coe_star, Unitary.coe_mul_star_self]
  have hone : (1 : Matrix (Fin d) (Fin d) Real) = U * 1 * star U := by
    rw [mul_one, hunit]
  have hdiag : (1 : Matrix (Fin d) (Fin d) Real) - D =
      Matrix.diagonal (fun i => 1 - htheta.eigenvalues i) := by
    ext i j
    by_cases hij : i = j <;> simp [D, hij]
  have hmatrix : (1 : Matrix (Fin d) (Fin d) Real) - theta =
      U * Matrix.diagonal (fun i => 1 - htheta.eigenvalues i) * star U := by
    calc
      (1 : Matrix (Fin d) (Fin d) Real) - theta =
          1 - (U * D * star U) :=
        congrArg (fun X : Matrix (Fin d) (Fin d) Real => 1 - X) hthetaSpec
      _ = (U * 1 * star U) - (U * D * star U) := by rw [← hone]
      _ = U * (1 - D) * star U := by noncomm_ring
      _ = U * Matrix.diagonal (fun i => 1 - htheta.eigenvalues i) * star U := by
        rw [hdiag]
  rw [hmatrix, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hdetUnit : Matrix.det U * Matrix.det (star U) = 1 := by
    rw [← Matrix.det_mul, hunit, Matrix.det_one]
  calc
    Matrix.det U * (∏ i : Fin d, (1 - htheta.eigenvalues i)) *
        Matrix.det (star U) =
        (Matrix.det U * Matrix.det (star U)) *
          (∏ i : Fin d, (1 - htheta.eigenvalues i)) := by ring
    _ = _ := by rw [hdetUnit, one_mul]

/-- Determinant form of the half-Gaussian Gram Laplace transform for an
arbitrary Hermitian tilt below the identity. -/
theorem integral_etr_realWishartGram_eq_det_rpow {k d : Nat}
    {theta : Matrix (Fin d) (Fin d) Real} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) :
    (∫ R : Matrix (Fin k) (Fin d) Real,
        MatsumotoPaper.etr (theta * realWishartGram R)
        ∂halfGaussianMatrix k d) =
      Real.rpow (Matrix.det (1 - theta))
        (-halfGaussianMatsumotoBeta k) := by
  rw [Real.rpow_eq_pow]
  have hlambda : ∀ i : Fin d, htheta.eigenvalues i < 1 :=
    eigenvalues_lt_one_of_one_sub_posDef htheta hpos
  rw [integral_etr_realWishartGram_eq_eigen_product htheta hlambda]
  have hfactor : ∀ i : Fin d, 0 ≤ 1 - htheta.eigenvalues i :=
    fun i => (sub_pos.mpr (hlambda i)).le
  have hprod :
      (∏ i : Fin d,
          (Real.sqrt (1 - htheta.eigenvalues i))⁻¹) =
        Matrix.det (1 - theta) ^ (-1 / 2 : Real) := by
    rw [det_one_sub_eq_prod_one_sub_eigenvalues htheta]
    calc
      (∏ i : Fin d,
          (Real.sqrt (1 - htheta.eigenvalues i))⁻¹) =
          ∏ i : Fin d,
            (1 - htheta.eigenvalues i) ^ (-1 / 2 : Real) := by
        apply Finset.prod_congr rfl
        intro i _hi
        calc
          (Real.sqrt (1 - htheta.eigenvalues i))⁻¹ =
              ((1 - htheta.eigenvalues i) ^ (1 / 2 : Real))⁻¹ := by
            rw [Real.sqrt_eq_rpow]
          _ = (1 - htheta.eigenvalues i) ^ (-(1 / 2 : Real)) :=
            (Real.rpow_neg (hfactor i) (1 / 2 : Real)).symm
          _ = (1 - htheta.eigenvalues i) ^ (-1 / 2 : Real) := by
            congr 1
            ring
      _ = (∏ i : Fin d, (1 - htheta.eigenvalues i)) ^
          (-1 / 2 : Real) := by
        exact Real.finsetProd_rpow Finset.univ
          (fun i => 1 - htheta.eigenvalues i)
          (fun i _hi => hfactor i) (-1 / 2 : Real)
  rw [hprod]
  rw [← Real.rpow_mul_natCast hpos.det_pos.le (-1 / 2 : Real) k]
  congr 1
  unfold halfGaussianMatsumotoBeta
  ring

/-- The exact determinant-Laplace premise required by the literal Matsumoto
pushforward constructor at identity scale. -/
theorem halfGaussian_determinantLaplace {k d : Nat}
    (theta : MatsumotoPaper.Sym d)
    (hpos : ((matsumotoIdentityScale d).1⁻¹ - theta.1).PosDef) :
    (∫ R : Matrix (Fin k) (Fin d) Real,
        MatsumotoPaper.etr (theta.1 * realWishartGram R)
        ∂halfGaussianMatrix k d) =
      Real.rpow
        (Matrix.det (1 - theta.1 * (matsumotoIdentityScale d).1))
        (-halfGaussianMatsumotoBeta k) := by
  have htheta : theta.1.IsHermitian := by
    exact Matrix.isHermitian_iff_isSymm.mpr theta.property
  have hpos' : (1 - theta.1).PosDef := by
    simpa [matsumotoIdentityScale] using hpos
  simpa [matsumotoIdentityScale] using
    (integral_etr_realWishartGram_eq_det_rpow
      (k := k) htheta hpos')

/-- Kernel-checked half-Gaussian Gram realization of Matsumoto's Wishart law.
The only dimension hypothesis is the full-rank threshold used by the SPD
lift, not by the determinant transform itself. -/
noncomputable def halfGaussianMatsumotoWishartPushforward_internal
    {d k : Nat} (hdk : d ≤ k) :
    HalfGaussianMatsumotoWishartPushforward d k :=
  halfGaussianMatsumotoWishartPushforward_of_determinantLaplace hdk
    (fun theta htheta => halfGaussian_determinantLaplace theta htheta)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

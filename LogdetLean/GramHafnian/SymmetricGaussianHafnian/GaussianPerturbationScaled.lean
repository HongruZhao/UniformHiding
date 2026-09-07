import LogdetLean.GramHafnian.SymmetricGaussianHafnian.GaussianPerturbation
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.GaussianPerturbationBall
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.Main

/-!
# Arbitrary-scale independent complex Gaussian perturbations

This module supplies the literal `tau > 0` versions of the complex
perturbation Laplace and small-ball statements.  The perturbation law is
arbitrary and independent of the Gaussian edge array; its coordinates need
not be independent and no moment assumption is imposed.

The rescaling is proved from the finite matching-sum definition of the
hafnian.  In particular, the noise amplitude `tau` produces the exact output
amplitude `tau ^ n` on `2n` vertices.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

/-- Scaling every complex edge by `c` scales the `2n`-vertex hafnian by
`c ^ n`. -/
theorem edgeHafnian_const_mul (n : ℕ) (c : ℂ)
    (x : Edge (Fin (2 * n)) → ℂ) :
    edgeHafnian (fun e ↦ c * x e) = c ^ n * edgeHafnian x := by
  unfold edgeHafnian
  have hmatrix : matrixOfEdges (fun e ↦ c * x e) =
      fun i j ↦ c * matrixOfEdges x i j := by
    funext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [matrixOfEdges, hij]
  rw [hmatrix]
  exact typeHafnian_const_mul_of_card n (by simp) c (matrixOfEdges x)

/-- Pointwise factorization of a deterministic perturbation plus a positive
Gaussian noise scale. -/
theorem edgeHafnian_add_posScale
    (n : ℕ) (tau : ℝ) (htau : 0 < tau)
    (a x : Edge (Fin (2 * n)) → ℂ) :
    edgeHafnian (a + fun e ↦ (tau : ℂ) * x e) =
      ((tau ^ n : ℝ) : ℂ) *
        edgeHafnian (x + fun e ↦ ((tau⁻¹ : ℝ) : ℂ) * a e) := by
  have htau0 : (tau : ℂ) ≠ 0 := by exact_mod_cast htau.ne'
  have hscale : a + (fun e ↦ (tau : ℂ) * x e) =
      fun e ↦ (tau : ℂ) *
        (x + fun d ↦ ((tau⁻¹ : ℝ) : ℂ) * a d) e := by
    funext e
    change a e + (tau : ℂ) * x e =
      (tau : ℂ) * (x e + ((tau⁻¹ : ℝ) : ℂ) * a e)
    push_cast
    field_simp [htau.ne']
    ring
  rw [hscale, edgeHafnian_const_mul]
  norm_cast

/-- Exact event rescaling at the paper normalization. -/
theorem edgeHafnian_add_posScale_norm_iff
    (n : ℕ) (tau : ℝ) (htau : 0 < tau)
    (a x : Edge (Fin (2 * n)) → ℂ) (w : ℂ) (epsilon : ℝ) :
    ‖edgeHafnian (a + fun e ↦ (tau : ℂ) * x e) - w‖ ≤
        epsilon * tau ^ n * sigma n ↔
      ‖edgeHafnian (x + fun e ↦ ((tau⁻¹ : ℝ) : ℂ) * a e) -
          (((tau ^ n)⁻¹ : ℝ) : ℂ) * w‖ ≤ epsilon * sigma n := by
  rw [edgeHafnian_add_posScale n tau htau]
  have hpow : 0 < tau ^ n := pow_pos htau n
  have hfactor :
      ((tau ^ n : ℝ) : ℂ) *
          edgeHafnian (x + fun e ↦ ((tau⁻¹ : ℝ) : ℂ) * a e) - w =
        ((tau ^ n : ℝ) : ℂ) *
          (edgeHafnian (x + fun e ↦ ((tau⁻¹ : ℝ) : ℂ) * a e) -
            (((tau ^ n)⁻¹ : ℝ) : ℂ) * w) := by
    have hc : ((tau ^ n : ℝ) : ℂ) * (((tau ^ n)⁻¹ : ℝ) : ℂ) = 1 := by
      norm_cast
      exact mul_inv_cancel₀ hpow.ne'
    rw [mul_sub]
    congr 1
    rw [← mul_assoc, hc, one_mul]
  rw [hfactor, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hpow]
  have hrhs : epsilon * tau ^ n * sigma n =
      tau ^ n * (epsilon * sigma n) := by ring
  rw [hrhs]
  constructor <;> intro h
  · exact le_of_mul_le_mul_left h hpow
  · exact mul_le_mul_of_nonneg_left h hpow.le

/-- Arbitrary-scale version of the independent-perturbation Laplace
comparison.  This is the complex specialization of the paper's
`perturb-laplace` display. -/
theorem symmetricHafnian_independentShift_scaled_laplace_le
    (n : ℕ) (hn : 1 ≤ n) (tau : ℝ) (htau : 0 < tau)
    (nu : Measure (Edge (Fin (2 * n)) → ℂ)) [IsProbabilityMeasure nu]
    (w : ℂ) (s : ℝ) (hs : 0 ≤ s) :
    (∫ p : (Edge (Fin (2 * n)) → ℂ) × (Edge (Fin (2 * n)) → ℂ),
      Real.exp (-s *
        ‖edgeHafnian (p.2 + fun e ↦ (tau : ℂ) * p.1 e) - w‖ ^ 2)
        ∂((edgeGaussian (Fin (2 * n))).prod nu)) ≤
      ∫ x, Real.exp (-s * tau ^ (2 * n) * ‖edgeHafnian x‖ ^ 2)
        ∂edgeGaussian (Fin (2 * n)) := by
  let f : (Edge (Fin (2 * n)) → ℂ) × (Edge (Fin (2 * n)) → ℂ) → ℝ :=
    fun p ↦ Real.exp (-s *
      ‖edgeHafnian (p.2 + fun e ↦ (tau : ℂ) * p.1 e) - w‖ ^ 2)
  have hf : Integrable f ((edgeGaussian (Fin (2 * n))).prod nu) := by
    apply Integrable.of_bound (by dsimp [f]; fun_prop) 1
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (sq_nonneg _))
  let q : ℝ := s * tau ^ (2 * n)
  have hq : 0 ≤ q := mul_nonneg hs (pow_nonneg htau.le _)
  have hpow : 0 < tau ^ n := pow_pos htau n
  have hrewrite (a x : Edge (Fin (2 * n)) → ℂ) :
      Real.exp (-s * ‖edgeHafnian (a + fun e ↦ (tau : ℂ) * x e) - w‖ ^ 2) =
        Real.exp (-q *
          ‖edgeHafnian (x + fun e ↦ ((tau⁻¹ : ℝ) : ℂ) * a e) -
            (((tau ^ n)⁻¹ : ℝ) : ℂ) * w‖ ^ 2) := by
    rw [edgeHafnian_add_posScale n tau htau]
    have hfactor :
        ((tau ^ n : ℝ) : ℂ) *
            edgeHafnian (x + fun e ↦ ((tau⁻¹ : ℝ) : ℂ) * a e) - w =
          ((tau ^ n : ℝ) : ℂ) *
            (edgeHafnian (x + fun e ↦ ((tau⁻¹ : ℝ) : ℂ) * a e) -
              (((tau ^ n)⁻¹ : ℝ) : ℂ) * w) := by
      have hc : ((tau ^ n : ℝ) : ℂ) * (((tau ^ n)⁻¹ : ℝ) : ℂ) = 1 := by
        norm_cast
        exact mul_inv_cancel₀ hpow.ne'
      rw [mul_sub]
      congr 1
      rw [← mul_assoc, hc, one_mul]
    rw [hfactor, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpow]
    dsimp [q]
    congr 1
    rw [mul_pow]
    have hpow2 : (tau ^ n) ^ 2 = tau ^ (2 * n) := by ring
    rw [hpow2]
    ring
  calc
    _ = ∫ a, ∫ x, f (x, a) ∂edgeGaussian (Fin (2 * n)) ∂nu :=
      integral_prod_symm f hf
    _ ≤ ∫ _a, (∫ x, Real.exp (-q * ‖edgeHafnian x‖ ^ 2)
        ∂edgeGaussian (Fin (2 * n))) ∂nu := by
      apply integral_mono hf.integral_prod_right (integrable_const _)
      intro a
      change (∫ x, f (x, a) ∂edgeGaussian (Fin (2 * n))) ≤ _
      calc
        _ = ∫ x, Real.exp (-q *
              ‖edgeHafnian
                  (x + fun e ↦ ((tau⁻¹ : ℝ) : ℂ) * a e) -
                (((tau ^ n)⁻¹ : ℝ) : ℂ) * w‖ ^ 2)
              ∂edgeGaussian (Fin (2 * n)) := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact hrewrite a x
        _ ≤ _ := deterministicShift_edgeHafnian_laplace_le (2 * n) (by omega)
          (fun e ↦ ((tau⁻¹ : ℝ) : ℂ) * a e)
          ((((tau ^ n)⁻¹ : ℝ) : ℂ) * w) q hq
    _ = ∫ x, Real.exp (-q * ‖edgeHafnian x‖ ^ 2)
        ∂edgeGaussian (Fin (2 * n)) := by simp
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [q]
      congr 1
      ring

/-- Exact arbitrary-scale comparison with the centered Gaussian small ball.
The first coordinate is the complete independent complex Gaussian edge
array and the second coordinate has the arbitrary perturbation law `nu`.
Thus the product measure encodes precisely the required independence, while
allowing arbitrary dependence among the perturbation coordinates. -/
theorem symmetricHafnian_independentShift_scaled_ball_le_centered
    (n : ℕ) (hn : 1 ≤ n) (tau : ℝ) (htau : 0 < tau)
    (nu : Measure (Edge (Fin (2 * n)) → ℂ)) [IsProbabilityMeasure nu]
    (w : ℂ) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    ((edgeGaussian (Fin (2 * n))).prod nu)
      {p | ‖edgeHafnian (p.2 + fun e ↦ (tau : ℂ) * p.1 e) - w‖ ≤
        epsilon * tau ^ n * sigma n} ≤
      edgeGaussian (Fin (2 * n))
        {x | ‖edgeHafnian x‖ ≤ epsilon * sigma n} := by
  let S : Set ((Edge (Fin (2 * n)) → ℂ) × (Edge (Fin (2 * n)) → ℂ)) :=
    {p | ‖edgeHafnian (p.2 + fun e ↦ (tau : ℂ) * p.1 e) - w‖ ≤
      epsilon * tau ^ n * sigma n}
  have hS : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_le (by fun_prop) measurable_const
  rw [show ((edgeGaussian (Fin (2 * n))).prod nu)
      {p | ‖edgeHafnian (p.2 + fun e ↦ (tau : ℂ) * p.1 e) - w‖ ≤
        epsilon * tau ^ n * sigma n} =
      ((edgeGaussian (Fin (2 * n))).prod nu) S by rfl,
    Measure.prod_apply_symm hS]
  calc
    (∫⁻ a, edgeGaussian (Fin (2 * n)) (Prod.swap ∘ Prod.mk a ⁻¹' S) ∂nu) ≤
        ∫⁻ _a, edgeGaussian (Fin (2 * n))
          {x | ‖edgeHafnian x‖ ≤ epsilon * sigma n} ∂nu := by
      apply lintegral_mono
      intro a
      have hset : (Prod.swap ∘ Prod.mk a ⁻¹' S) =
          {x | ‖edgeHafnian
              (x + fun e ↦ ((tau⁻¹ : ℝ) : ℂ) * a e) -
                (((tau ^ n)⁻¹ : ℝ) : ℂ) * w‖ ≤ epsilon * sigma n} := by
        ext x
        change (‖edgeHafnian (a + fun e ↦ (tau : ℂ) * x e) - w‖ ≤
          epsilon * tau ^ n * sigma n) ↔ _
        exact edgeHafnian_add_posScale_norm_iff n tau htau a x w epsilon
      change edgeGaussian (Fin (2 * n)) (Prod.swap ∘ Prod.mk a ⁻¹' S) ≤ _
      rw [hset]
      exact deterministicShift_edgeHafnian_ball_le (2 * n) (by omega)
        (fun e ↦ ((tau⁻¹ : ℝ) : ℂ) * a e)
        ((((tau ^ n)⁻¹ : ℝ) : ℂ) * w)
        (epsilon * sigma n) (mul_nonneg hepsilon (sigma_nonneg n))
    _ = edgeGaussian (Fin (2 * n))
          {x | ‖edgeHafnian x‖ ≤ epsilon * sigma n} := by simp

/-- Literal arbitrary-scale independent-perturbation small-ball endpoint.
This combines the exact centered-ball comparison with the verified centered
hafnian small-ball estimate, and is the complex specialization of the paper's
`perturb-ball` display. -/
theorem symmetricHafnian_independentShift_scaled_smallBall
    (n : ℕ) (hn : 1 ≤ n) (tau : ℝ) (htau : 0 < tau)
    (nu : Measure (Edge (Fin (2 * n)) → ℂ)) [IsProbabilityMeasure nu]
    (w : ℂ) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    ((edgeGaussian (Fin (2 * n))).prod nu)
      {p | ‖edgeHafnian (p.2 + fun e ↦ (tau : ℂ) * p.1 e) - w‖ ≤
        epsilon * tau ^ n * sigma n} ≤
      min 1 (ENNReal.ofReal (coefficient n * epsilon ^ 2)) := by
  calc
    _ ≤ edgeGaussian (Fin (2 * n))
          {x | ‖edgeHafnian x‖ ≤ epsilon * sigma n} :=
      symmetricHafnian_independentShift_scaled_ball_le_centered
        n hn tau htau nu w epsilon hepsilon
    _ ≤ min 1 (ENNReal.ofReal (coefficient n * epsilon ^ 2)) := by
      simpa only [sub_zero] using
        (symmetricHafnian_shifted_smallBall n hn 0 epsilon hepsilon)

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian

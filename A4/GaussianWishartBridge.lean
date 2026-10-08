import A4.TriangularGaussianLaplace
import A4.MatrixLaplaceUniqueness

open MeasureTheory ProbabilityTheory Filter Set Topology Matrix
open scoped BigOperators

noncomputable section

namespace A4Research

def standardGaussianVector (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ : Fin d ↦ gaussianReal 0 1

def standardGaussianRows (k d : ℕ) : Measure (Fin k → Fin d → ℝ) :=
  Measure.pi fun _ : Fin k ↦ standardGaussianVector d

instance (d : ℕ) : IsProbabilityMeasure (standardGaussianVector d) := by
  unfold standardGaussianVector
  infer_instance

instance (k d : ℕ) : IsProbabilityMeasure (standardGaussianRows k d) := by
  unfold standardGaussianRows
  infer_instance

theorem map_standardGaussianVector_half (d : ℕ) :
    (standardGaussianVector d).map
      (fun x : Fin d → ℝ ↦ fun i ↦ (Real.sqrt 2)⁻¹ * x i) =
      Measure.pi (fun _ : Fin d ↦ gaussianReal 0 (1 / 2)) := by
  unfold standardGaussianVector
  rw [Measure.pi_map_pi (fun _ ↦
    (show Measurable (fun x : ℝ ↦ (Real.sqrt 2)⁻¹ * x) by fun_prop).aemeasurable)]
  congr 1
  funext i
  exact map_invSqrtTwo_gaussian

/-- Standard iid Gaussian quadratic integration, normalized to Wishart's
identity scale convention. -/
theorem standardGaussianVector_integral_quadratic_half {d : ℕ}
    {theta : Matrix (Fin d) (Fin d) ℝ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) :
    (∫ x : Fin d → ℝ, Real.exp ((x ⬝ᵥ (theta *ᵥ x)) / 2)
      ∂standardGaussianVector d) = Matrix.det (1 - theta) ^ (-1 / 2 : ℝ) := by
  let scale : (Fin d → ℝ) → (Fin d → ℝ) :=
    fun x i ↦ (Real.sqrt 2)⁻¹ * x i
  have hscale : Measurable scale := by fun_prop
  have hquad (x : Fin d → ℝ) :
      scale x ⬝ᵥ (theta *ᵥ scale x) = (x ⬝ᵥ (theta *ᵥ x)) / 2 := by
    have hc : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
      rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    change (∑ i, ((Real.sqrt 2)⁻¹ * x i) *
      ∑ j, theta i j * ((Real.sqrt 2)⁻¹ * x j)) = _
    simp only [dotProduct, Matrix.mulVec, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 * (x i * (theta i j * x j)) := by ring
      _ = _ := by rw [hc]; ring
  have h := gaussianHalfVector_integral_quadratic_det htheta hpos
    (0 : Fin d → ℝ)
  simp only [zero_dotProduct, mul_zero, add_zero, Real.exp_zero, mul_one] at h
  rw [← map_standardGaussianVector_half d,
    integral_map hscale.aemeasurable (by fun_prop)] at h
  simpa only [Function.comp_def, hquad] using h

/-- A real Gram matrix from `k` standard Gaussian rows, divided by two.
Its shape is `k/2` and its scale in A4's convention is the identity. -/
def standardGaussianGram {k d : ℕ} (z : Fin k → Fin d → ℝ) :
    MatsumotoPaper.RealMatrix d :=
  Matrix.of fun i j ↦ (∑ c : Fin k, z c i * z c j) / 2

theorem standardGaussianGram_isSymm {k d : ℕ} (z : Fin k → Fin d → ℝ) :
    (standardGaussianGram z).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [standardGaussianGram, Matrix.of_apply, mul_comm]

theorem measurable_standardGaussianGram (k d : ℕ) :
    Measurable (standardGaussianGram : (Fin k → Fin d → ℝ) →
      MatsumotoPaper.RealMatrix d) := by
  haveI : BorelSpace (MatsumotoPaper.RealMatrix d) := ⟨rfl⟩
  apply Continuous.measurable
  change Continuous (fun z : Fin k → Fin d → ℝ ↦
    fun i j ↦ (∑ c : Fin k, z c i * z c j) / 2)
  fun_prop

theorem trace_standardGaussianGram {k d : ℕ}
    (theta : MatsumotoPaper.RealMatrix d) (z : Fin k → Fin d → ℝ) :
    Matrix.trace (theta * standardGaussianGram z) =
      ∑ c : Fin k, (z c ⬝ᵥ (theta *ᵥ z c)) / 2 := by
  change (∑ i : Fin d, ∑ j : Fin d,
    theta i j * standardGaussianGram z j i) = _
  simp only [standardGaussianGram,
    Matrix.of_apply, Matrix.mulVec, dotProduct, Finset.mul_sum,
    Finset.sum_div, mul_div_assoc]
  calc
    _ = ∑ i : Fin d, ∑ c : Fin k, ∑ j : Fin d,
        theta i j * (z c j * z c i) / 2 := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [mul_div_assoc] using
        Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
          (f := fun (j : Fin d) (c : Fin k) ↦ theta i j * (z c j * z c i) / 2)
    _ = ∑ c : Fin k, ∑ i : Fin d, ∑ j : Fin d,
        theta i j * (z c j * z c i) / 2 :=
      Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun (i : Fin d) (c : Fin k) ↦
          ∑ j : Fin d, theta i j * (z c j * z c i) / 2)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The exact Gram Laplace transform in every natural row count, including
singular Gram laws. No full-rank assumption is needed for this identity. -/
theorem standardGaussianGram_integral_etr {k d : ℕ}
    (theta : MatsumotoPaper.Sym d) (hpos : (1 - theta.1).PosDef) :
    (∫ z, MatsumotoPaper.etr (theta.1 * standardGaussianGram z)
      ∂standardGaussianRows k d) =
      Matrix.det (1 - theta.1) ^ (-((k : ℝ) / 2)) := by
  have htheta := Matrix.isHermitian_iff_isSymm.mpr theta.2
  simp only [MatsumotoPaper.etr, trace_standardGaussianGram, Real.exp_sum,
    standardGaussianRows]
  rw [integral_fintype_prod_eq_prod
    (fun _ : Fin k ↦ fun x : Fin d → ℝ ↦
      Real.exp ((x ⬝ᵥ (theta.1 *ᵥ x)) / 2))]
  simp only [standardGaussianVector_integral_quadratic_half htheta hpos,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Real.rpow_mul_natCast hpos.det_pos.le]
  congr 1
  ring

end A4Research

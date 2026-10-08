import A4.TriangularFactorization
import A4.WishartDensityGamma
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi

open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory

noncomputable section

namespace A4Research

local instance (d : ℕ) : BorelSpace (MatsumotoPaper.RealMatrix d) := ⟨rfl⟩

/-- A total positive square root. Its fallback is used only on the null set
where a Gamma pivot is nonpositive. -/
def positiveSqrt (x : ℝ) : ℝ := if 0 < x then Real.sqrt x else 1

theorem positiveSqrt_pos (x : ℝ) : 0 < positiveSqrt x := by
  unfold positiveSqrt
  split_ifs with h
  · exact Real.sqrt_pos.mpr h
  · norm_num

theorem measurable_positiveSqrt : Measurable positiveSqrt := by
  exact Measurable.ite measurableSet_Ioi Real.continuous_sqrt.measurable measurable_const

theorem positiveSqrt_eq_sqrt {x : ℝ} (hx : 0 < x) :
    positiveSqrt x = Real.sqrt x := if_pos hx

/-- Squared diagonal Gamma coordinates and raw off-diagonal Gaussian entries.
The unused upper triangle is integrated out under a probability law. -/
abbrev BartlettCoordinates (d : ℕ) :=
  (Fin d → ℝ) × (Fin d → Fin d → ℝ)

/-- Shape of pivot `i` in Matsumoto's scale convention. -/
def bartlettShape (beta : ℝ) {d : ℕ} (i : Fin d) : ℝ := beta - (i : ℝ) / 2

/-- The lower triangular Bartlett factor, defined globally on raw coordinates. -/
def bartlettFactor (d : ℕ) (q : BartlettCoordinates d) : MatsumotoPaper.RealMatrix d :=
  fun i j => if j < i then q.2 i j else if i = j then positiveSqrt (q.1 i) else 0

theorem bartlettFactor_triangular (d : ℕ) (q : BartlettCoordinates d) :
    (bartlettFactor d q).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  simp only [bartlettFactor, if_neg (not_lt.mpr hij.le), if_neg hij.ne]

theorem bartlettFactor_diag (d : ℕ) (q : BartlettCoordinates d) (i : Fin d) :
    bartlettFactor d q i i = positiveSqrt (q.1 i) := by
  simp [bartlettFactor]

theorem bartlettFactor_diag_pos (d : ℕ) (q : BartlettCoordinates d) (i : Fin d) :
    0 < bartlettFactor d q i i := by
  rw [bartlettFactor_diag]
  exact positiveSqrt_pos _

theorem bartlettFactor_isUnit (d : ℕ) (q : BartlettCoordinates d) :
    IsUnit (bartlettFactor d q) :=
  lowerTriangular_isUnit (bartlettFactor_triangular d q) (bartlettFactor_diag_pos d q)

theorem bartlettFactor_square_posDef (d : ℕ) (q : BartlettCoordinates d) :
    (bartlettFactor d q * (bartlettFactor d q)ᵀ).PosDef := by
  let := (bartlettFactor_isUnit d q).invertible
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.mul_conjTranspose_self (bartlettFactor d q)
      (Matrix.vecMul_injective_of_invertible _)

theorem measurable_bartlettFactor (d : ℕ) : Measurable (bartlettFactor d) := by
  change @Measurable (BartlettCoordinates d) (Fin d → Fin d → ℝ)
    _ (borel _) (bartlettFactor d)
  rw [← @BorelSpace.measurable_eq (Fin d → Fin d → ℝ) _
    MeasurableSpace.pi Pi.borelSpace]
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  unfold bartlettFactor
  split_ifs
  · fun_prop
  · exact measurable_positiveSqrt.comp ((measurable_pi_apply i).comp measurable_fst)
  · fun_prop

/-- Independent Gamma pivots and variance-one-half real Gaussian entries.
No half-integer shape restriction is imposed. -/
def bartlettCoordinatesMeasure (d : ℕ) (beta : ℝ) : Measure (BartlettCoordinates d) :=
  (Measure.pi (fun i : Fin d => gammaMeasure (bartlettShape beta i) 1)).prod
    (Measure.pi (fun _ : Fin d =>
      Measure.pi (fun _ : Fin d => gaussianReal 0 (1 / 2))))

theorem bartlettShape_pos {d : ℕ} {beta : ℝ}
    (hb : ((d : ℝ) - 1) / 2 < beta) (i : Fin d) :
    0 < bartlettShape beta i := by
  have hi : (i : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast i.isLt
  unfold bartlettShape
  linarith

/-- The inverse-moment hypothesis in the full A4 target makes every pivot
shape greater than the complete degree, not only greater than zero. -/
theorem bartlettShape_sub_degree_pos {d n : ℕ} {beta gamma : ℝ}
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2)
    (hgap : (n : ℝ) - 1 < gamma) (i : Fin d) :
    0 < bartlettShape beta i - (n : ℝ) := by
  have hi : (i : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast i.isLt
  unfold bartlettShape
  linarith

theorem bartlettCoordinatesMeasure_probability {d : ℕ} {beta : ℝ}
    (hb : ((d : ℝ) - 1) / 2 < beta) :
    IsProbabilityMeasure (bartlettCoordinatesMeasure d beta) := by
  let (i : Fin d) : IsProbabilityMeasure (gammaMeasure (bartlettShape beta i) 1) :=
    isProbabilityMeasure_gammaMeasure (bartlettShape_pos hb i) (by norm_num)
  unfold bartlettCoordinatesMeasure
  infer_instance

/-- A concrete SPD-valued random matrix for every real admissible shape.
The Laplace identity must be proved before this candidate is identified with
the `W_d` law in the original target. -/
def bartlettSPD (d : ℕ) (sigma : MatsumotoPaper.SymPosDef d)
    (q : BartlettCoordinates d) : MatsumotoPaper.SymPosDef d :=
  ⟨cholesky sigma.2 *
      (bartlettFactor d q * (bartlettFactor d q)ᵀ) * (cholesky sigma.2)ᵀ,
    by
      simpa only [Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial] using
        (Matrix.IsUnit.posDef_star_right_conjugate_iff (cholesky_isUnit sigma.2)).mpr
          (bartlettFactor_square_posDef d q)⟩

theorem measurable_bartlettSPD (d : ℕ) (sigma : MatsumotoPaper.SymPosDef d) :
    Measurable (bartlettSPD d sigma) := by
  apply Measurable.subtype_mk
  change Measurable (fun q : BartlettCoordinates d =>
    cholesky sigma.2 * (bartlettFactor d q * (bartlettFactor d q)ᵀ) *
      (cholesky sigma.2)ᵀ)
  change @Measurable (BartlettCoordinates d) (Fin d → Fin d → ℝ)
    _ (borel _) _
  rw [← @BorelSpace.measurable_eq (Fin d → Fin d → ℝ) _
    MeasurableSpace.pi Pi.borelSpace]
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  have hm := measurable_bartlettFactor d
  have hentries (i j : Fin d) : Measurable (fun q => bartlettFactor d q i j) := by
    have hc : Continuous (fun A : MatsumotoPaper.RealMatrix d => A i j) := by fun_prop
    exact hc.borel_measurable.comp hm
  fun_prop

/-- The arbitrary-real-shape Bartlett probability measure on the SPD cone. -/
def bartlettMeasure (d : ℕ) (beta : ℝ) (sigma : MatsumotoPaper.SymPosDef d) :
    Measure (MatsumotoPaper.SymPosDef d) :=
  (bartlettCoordinatesMeasure d beta).map (bartlettSPD d sigma)

theorem bartlettMeasure_probability {d : ℕ} {beta : ℝ}
    (sigma : MatsumotoPaper.SymPosDef d) (hb : ((d : ℝ) - 1) / 2 < beta) :
    IsProbabilityMeasure (bartlettMeasure d beta sigma) := by
  let := bartlettCoordinatesMeasure_probability hb
  exact Measure.isProbabilityMeasure_map (measurable_bartlettSPD d sigma).aemeasurable

theorem bartlettCoordinatesMeasure_ae_pivots_pos {d : ℕ} {beta : ℝ}
    (hb : ((d : ℝ) - 1) / 2 < beta) :
    ∀ᵐ q ∂bartlettCoordinatesMeasure d beta, ∀ i, 0 < q.1 i := by
  let (i : Fin d) : IsProbabilityMeasure (gammaMeasure (bartlettShape beta i) 1) :=
    isProbabilityMeasure_gammaMeasure (bartlettShape_pos hb i) (by norm_num)
  have hp : ∀ᵐ x ∂Measure.pi (fun i : Fin d => gammaMeasure (bartlettShape beta i) 1),
      ∀ i, 0 < x i :=
    Filter.eventually_all.mpr fun i =>
      (Measure.tendsto_eval_ae_ae).eventually
        (gammaMeasure_ae_pos (bartlettShape beta i) 1)
  exact (Measure.quasiMeasurePreserving_fst).ae hp

/-- Determinant factorization in the independent triangular coordinates. -/
theorem bartlettSPD_det {d : ℕ} (sigma : MatsumotoPaper.SymPosDef d)
    (q : BartlettCoordinates d) :
    Matrix.det (bartlettSPD d sigma q).1 =
      Matrix.det sigma.1 * ∏ i : Fin d, positiveSqrt (q.1 i) ^ 2 := by
  have hS : Matrix.det sigma.1 = Matrix.det (cholesky sigma.2) ^ 2 := by
    have h := congrArg Matrix.det (cholesky_mul_transpose sigma.2)
    simpa only [Matrix.det_mul, Matrix.det_transpose, pow_two] using h.symm
  have hT : Matrix.det (bartlettFactor d q) = ∏ i : Fin d, positiveSqrt (q.1 i) := by
    rw [Matrix.det_of_isLowerTriangular _ (bartlettFactor_triangular d q)]
    simp only [bartlettFactor_diag]
  change Matrix.det (cholesky sigma.2 *
    (bartlettFactor d q * (bartlettFactor d q)ᵀ) * (cholesky sigma.2)ᵀ) = _
  simp only [Matrix.det_mul, Matrix.det_transpose, hT]
  rw [hS]
  have hprod : (∏ i : Fin d, positiveSqrt (q.1 i) ^ 2) =
      (∏ i : Fin d, positiveSqrt (q.1 i)) ^ 2 := by
    rw [Finset.prod_pow]
  rw [hprod]
  ring

theorem bartlettSPD_det_ae {d : ℕ} {beta : ℝ}
    (sigma : MatsumotoPaper.SymPosDef d) (hb : ((d : ℝ) - 1) / 2 < beta) :
    (fun q => Matrix.det (bartlettSPD d sigma q).1) =ᵐ[bartlettCoordinatesMeasure d beta]
      (fun q => Matrix.det sigma.1 * ∏ i : Fin d, q.1 i) := by
  filter_upwards [bartlettCoordinatesMeasure_ae_pivots_pos hb] with q hq
  rw [bartlettSPD_det]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [positiveSqrt_eq_sqrt (hq i), Real.sq_sqrt (hq i).le]

/-- Every real power of the candidate Bartlett determinant has the complete
Gamma-product moment, with the exact pivot integrability conditions. -/
theorem bartlettMeasure_integral_det_rpow {d : ℕ} {beta p : ℝ}
    (sigma : MatsumotoPaper.SymPosDef d) (hb : ((d : ℝ) - 1) / 2 < beta)
    (hp : ∀ i : Fin d, 0 < bartlettShape beta i + p) :
    (∫ w : MatsumotoPaper.SymPosDef d, Matrix.det w.1 ^ p
      ∂bartlettMeasure d beta sigma) =
      Matrix.det sigma.1 ^ p *
        ∏ i : Fin d, Real.Gamma (bartlettShape beta i + p) /
          Real.Gamma (bartlettShape beta i) := by
  let (i : Fin d) : IsProbabilityMeasure (gammaMeasure (bartlettShape beta i) 1) :=
    isProbabilityMeasure_gammaMeasure (bartlettShape_pos hb i) (by norm_num)
  have hdet : Measurable (fun w : MatsumotoPaper.SymPosDef d => Matrix.det w.1 ^ p) := by
    have hc : Continuous (Matrix.det : MatsumotoPaper.RealMatrix d → ℝ) :=
      continuous_id.matrix_det
    exact (hc.borel_measurable.comp measurable_subtype_coe).pow_const p
  rw [bartlettMeasure, integral_map (measurable_bartlettSPD d sigma).aemeasurable
    hdet.aestronglyMeasurable]
  have heq : (fun q => Matrix.det (bartlettSPD d sigma q).1 ^ p) =ᵐ[
      bartlettCoordinatesMeasure d beta]
      (fun q => Matrix.det sigma.1 ^ p * ∏ i : Fin d, q.1 i ^ p) := by
    filter_upwards [bartlettCoordinatesMeasure_ae_pivots_pos hb,
      bartlettSPD_det_ae sigma hb] with q hq hdetq
    rw [hdetq, Real.mul_rpow sigma.2.det_pos.le
      (Finset.prod_nonneg fun i _ => (hq i).le),
      ← Real.finsetProd_rpow Finset.univ _ (fun i _ => (hq i).le) p]
  rw [integral_congr_ae heq, bartlettCoordinatesMeasure, integral_const_mul]
  have hsep : (fun q : BartlettCoordinates d => ∏ i : Fin d, q.1 i ^ p) =
      (fun q => (∏ i : Fin d, q.1 i ^ p) * (1 : ℝ)) := by simp
  rw [hsep, integral_prod_mul (fun x : Fin d → ℝ => ∏ i : Fin d, x i ^ p)
    (fun _ : Fin d → Fin d → ℝ => (1 : ℝ)), integral_const]
  rw [probReal_univ, one_smul, mul_one,
    integral_fintype_prod_eq_prod (fun i : Fin d => fun x : ℝ => x ^ p)]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [gammaMeasure_integral_rpow (bartlettShape_pos hb i) (by norm_num) (hp i)]
  simp only [Real.one_rpow, one_mul]

theorem bartlettMeasure_integrable_det_rpow {d : ℕ} {beta p : ℝ}
    (sigma : MatsumotoPaper.SymPosDef d) (hb : ((d : ℝ) - 1) / 2 < beta)
    (hp : ∀ i : Fin d, 0 < bartlettShape beta i + p) :
    Integrable (fun w : MatsumotoPaper.SymPosDef d => Matrix.det w.1 ^ p)
      (bartlettMeasure d beta sigma) := by
  apply Integrable.of_integral_ne_zero
  rw [bartlettMeasure_integral_det_rpow sigma hb hp]
  apply (mul_pos (Real.rpow_pos_of_pos sigma.2.det_pos p) _).ne'
  apply Finset.prod_pos
  intro i _
  exact div_pos (Real.Gamma_pos_of_pos (hp i))
    (Real.Gamma_pos_of_pos (bartlettShape_pos hb i))

/-- The full A4 gap hypothesis proves the determinant inverse integrability
required by the triangular density approach, in every degree. -/
theorem bartlettMeasure_integrable_det_inverse_degree {d n : ℕ} {beta gamma : ℝ}
    (sigma : MatsumotoPaper.SymPosDef d)
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2)
    (hgap : (n : ℝ) - 1 < gamma) :
    Integrable (fun w : MatsumotoPaper.SymPosDef d => Matrix.det w.1 ^ (-(n : ℝ)))
      (bartlettMeasure d beta sigma) := by
  have hb : ((d : ℝ) - 1) / 2 < beta := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  apply bartlettMeasure_integrable_det_rpow sigma hb
  intro i
  simpa only [sub_eq_add_neg] using bartlettShape_sub_degree_pos hgamma hgap i

end A4Research

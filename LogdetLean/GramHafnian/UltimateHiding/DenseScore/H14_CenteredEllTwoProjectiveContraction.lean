import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_CenteredEllTwoProjectiveCancellationConditional
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.PositiveTraceMomentInternal
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ProjectiveBilinearNormSq
import Mathlib.Tactic

/-!
# Finite projective contraction for the centered second score

This module is strictly below literal H14.  It expands the two centered
sandwiches at a fixed supported matrix, performs all projective contractions
before absolute values, and targets the explicit fixed-matrix contract from
`H14_CenteredEllTwoProjectiveCancellationConditional`.
-/

open scoped BigOperators ComplexConjugate ComplexOrder
open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open Matrix
open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

set_option maxHeartbeats 1200000

/-! ## Coordinate-to-matrix bridges -/

theorem complexCenteredRankOneProjection_eq_orbitalDirection_apply_h14
    {N : ℕ} (v : ComplexUnitSphere N) (i j : Fin N) :
    complexCenteredRankOneProjection N v i j =
      concreteCenteredOrbitalDirection N v i j := by
  unfold complexCenteredRankOneProjection concreteCenteredOrbitalDirection
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

theorem complexCenteredProjectiveSandwich_eq_trace_h14
    {N : ℕ} (v : ComplexUnitSphere N)
    (W Y : ConcreteMatrixState N) :
    complexCenteredProjectiveSandwich v W Y =
      Matrix.trace
        (concreteCenteredOrbitalDirection N v *
          (W * (concreteCenteredOrbitalDirection N v * Y))) := by
  unfold complexCenteredProjectiveSandwich
  simp_rw [complexCenteredRankOneProjection_eq_orbitalDirection_apply_h14]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  simp only [Finset.mul_sum, mul_assoc]

theorem complexCenteredProjectiveConjugateSandwich_eq_trace_h14
    {N : ℕ} (v : ComplexUnitSphere N)
    (R : ConcreteMatrixState N) :
    complexCenteredProjectiveConjugateSandwich v R =
      Matrix.trace
        (concreteCenteredOrbitalDirection N v *
          (R * ((concreteCenteredOrbitalDirection N v).transpose *
            R.conjTranspose))) := by
  unfold complexCenteredProjectiveConjugateSandwich
  simp_rw [complexCenteredRankOneProjection_eq_orbitalDirection_apply_h14]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.conjTranspose_apply]
  simp only [Finset.mul_sum, mul_assoc]

/-- Rank-one compression, the algebraic input that turns four projective
coordinates into a product of two trace pairings before integration. -/
theorem complexRankOneProjection_mul_mul_eq_tracePair_smul_h14
    {N : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    complexRankOneProjection v * A * complexRankOneProjection v =
      complexProjectiveTracePair v A • complexRankOneProjection v := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply]
  unfold complexProjectiveTracePair complexRankOneProjection
  change
    (∑ y, (∑ x, v.1 i * star (v.1 x) * A x y) *
        (v.1 y * star (v.1 j))) =
      (∑ x, ∑ y, v.1 x * star (v.1 y) * A y x) *
        (v.1 i * star (v.1 j))
  simp only [Finset.sum_mul]
  calc
    (∑ y, ∑ x,
        (v.1 i * star (v.1 x) * A x y) *
          (v.1 y * star (v.1 j))) =
        v.1 i * star (v.1 j) *
          (∑ y, ∑ x, star (v.1 x) * A x y * v.1 y) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = v.1 i * star (v.1 j) *
        (∑ x, ∑ y, v.1 x * star (v.1 y) * A y x) := by
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = ∑ x, ∑ y,
        (v.1 x * star (v.1 y) * A y x) *
          (v.1 i * star (v.1 j)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring

theorem trace_rankOne_mul_mul_mul_h14
    {N : ℕ} (v : ComplexUnitSphere N)
    (A B : ConcreteMatrixState N) :
    Matrix.trace
        (complexRankOneProjection v * A * complexRankOneProjection v * B) =
      complexProjectiveTracePair v A *
        complexProjectiveTracePair v B := by
  rw [complexRankOneProjection_mul_mul_eq_tracePair_smul_h14]
  rw [Matrix.smul_mul, Matrix.trace_smul]
  simp only [smul_eq_mul]
  rw [← complexProjectiveTracePair_eq_trace]

/-- The uncentered conjugate sandwich is the literal bilinear norm-square.
This is only a finite reindexing of the four projective coordinates. -/
theorem trace_rankOne_symmSandwich_eq_bilinearNormSq_h14
    {N : ℕ} (v : ComplexUnitSphere N) (R : ConcreteMatrixState N) :
    Matrix.trace
        (complexRankOneProjection v *
          (R * ((complexRankOneProjection v).transpose *
            R.conjTranspose))) =
      complexProjectiveBilinearNormSq v R := by
  unfold complexProjectiveBilinearNormSq
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.conjTranspose_apply]
  simp only [Finset.mul_sum, mul_assoc]
  calc
    (∑ a, ∑ b, ∑ c, ∑ d,
        complexRankOneProjection v a b *
          (R b c * (complexRankOneProjection v d c * star (R a d)))) =
        ∑ b, ∑ a, ∑ c, ∑ d,
          complexRankOneProjection v a b *
            (R b c * (complexRankOneProjection v d c * star (R a d))) := by
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ c, ∑ a, ∑ d,
          complexRankOneProjection v a b *
            (R b c * (complexRankOneProjection v d c * star (R a d))) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ c, ∑ a, ∑ d,
          complexRankOneProjection v a b *
            (R b c * (complexRankOneProjection v d c * star (R a d))) := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro d _
      ring

/-- For a symmetric matrix, the other mixed term in the centered conjugate
sandwich is the same positive trace pairing. -/
theorem trace_symm_mul_transpose_rankOne_mul_conjTranspose_h14
    {N : ℕ} (v : ComplexUnitSphere N) (R : ConcreteMatrixState N)
    (hR : R.IsSymm) :
    Matrix.trace
        (R * ((complexRankOneProjection v).transpose *
          R.conjTranspose)) =
      complexProjectiveTracePair v (R * R.conjTranspose) := by
  classical
  have hsymm : ∀ i j, R j i = R i j := Matrix.IsSymm.ext_iff.mp hR
  rw [complexProjectiveTracePair_eq_trace]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.conjTranspose_apply]
  simp only [Finset.mul_sum, mul_assoc]
  calc
    (∑ a, ∑ b, ∑ c,
        R a b * (complexRankOneProjection v c b * star (R a c))) =
        ∑ a, ∑ b, ∑ c,
          R b a * (complexRankOneProjection v c b * star (R c a)) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      rw [hsymm a b, hsymm a c]
    _ = ∑ b, ∑ a, ∑ c,
          R b a * (complexRankOneProjection v c b * star (R c a)) := by
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ c, ∑ a,
          R b a * (complexRankOneProjection v c b * star (R c a)) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ b, ∑ a,
          R b a * (complexRankOneProjection v c b * star (R c a)) := by
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ b, ∑ a,
          complexRankOneProjection v c b * (R b a * star (R c a)) := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      ring

/-! ## Four-factor integrability layer -/

theorem norm_complexCenteredRankOneProjection_entry_le_two_h14
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N) (i j : Fin N) :
    ‖complexCenteredRankOneProjection N v i j‖ ≤ 2 := by
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hNr
  have hinv : ((N : ℝ)⁻¹ : ℝ) ≤ 1 := by
    exact (inv_le_one₀ hNpos).2 hNr
  have ha :
      ‖((((N : ℝ)⁻¹ : ℝ) : ℂ) * (if i = j then 1 else 0))‖ ≤ 1 := by
    by_cases hij : i = j
    · simp only [hij, if_true, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr hNpos.le)]
      exact hinv
    · simp [hij]
  unfold complexCenteredRankOneProjection
  calc
    ‖complexRankOneProjection v i j -
        (((N : ℝ)⁻¹ : ℝ) : ℂ) * (if i = j then 1 else 0)‖ ≤
        ‖complexRankOneProjection v i j‖ +
          ‖((((N : ℝ)⁻¹ : ℝ) : ℂ) * (if i = j then 1 else 0))‖ :=
      norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add
      (norm_complexRankOneProjection_entry_le_one v i j) ha
    _ = 2 := by norm_num

/-- Any four centered projective entries have an integrable product.  This
bounded finite lemma is the measurability layer beneath polarization. -/
theorem integrable_complexCenteredRankOneProjection_entry_mul_four_h14
    {N : ℕ} (hN : 1 ≤ N)
    (i j k l p q r s : Fin N) :
    Integrable (fun v : ComplexUnitSphere N ↦
      complexCenteredRankOneProjection N v i j *
        complexCenteredRankOneProjection N v k l *
        complexCenteredRankOneProjection N v p q *
        complexCenteredRankOneProjection N v r s)
      (complexUnitSphereProbabilityMeasure N) := by
  have hi := integrable_complexCenteredRankOneProjection_entry hN i j
  have hk := integrable_complexCenteredRankOneProjection_entry hN k l
  have hp := integrable_complexCenteredRankOneProjection_entry hN p q
  have hr := integrable_complexCenteredRankOneProjection_entry hN r s
  have hik : Integrable (fun v : ComplexUnitSphere N ↦
      complexCenteredRankOneProjection N v i j *
        complexCenteredRankOneProjection N v k l)
      (complexUnitSphereProbabilityMeasure N) :=
    hk.bdd_mul hi.aestronglyMeasurable
      (Filter.Eventually.of_forall fun v ↦
        norm_complexCenteredRankOneProjection_entry_le_two_h14 hN v i j)
  have hikp : Integrable (fun v : ComplexUnitSphere N ↦
      (complexCenteredRankOneProjection N v i j *
        complexCenteredRankOneProjection N v k l) *
          complexCenteredRankOneProjection N v p q)
      (complexUnitSphereProbabilityMeasure N) :=
    hik.mul_bdd hp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun v ↦
        norm_complexCenteredRankOneProjection_entry_le_two_h14 hN v p q)
  have hikprs : Integrable (fun v : ComplexUnitSphere N ↦
      ((complexCenteredRankOneProjection N v i j *
        complexCenteredRankOneProjection N v k l) *
          complexCenteredRankOneProjection N v p q) *
            complexCenteredRankOneProjection N v r s)
      (complexUnitSphereProbabilityMeasure N) :=
    hikp.mul_bdd hr.aestronglyMeasurable
      (Filter.Eventually.of_forall fun v ↦
        norm_complexCenteredRankOneProjection_entry_le_two_h14 hN v r s)
  simpa only [mul_assoc] using hikprs

/-- Square-integrability of every finite quadratic polynomial in centered
projective entries.  The four factors are kept explicit for later exact
fourth-moment contraction. -/
theorem integrable_centeredProjectiveQuadraticPolynomial_sq_h14
    {N : ℕ} (hN : 1 ≤ N)
    (F : Fin N → Fin N → Fin N → Fin N → ℂ) :
    Integrable (fun v : ComplexUnitSphere N ↦
      (∑ a, ∑ b, ∑ c, ∑ d,
        complexCenteredRankOneProjection N v a b *
          complexCenteredRankOneProjection N v c d * F a b c d) ^ 2)
      (complexUnitSphereProbabilityMeasure N) := by
  rw [show (fun v : ComplexUnitSphere N ↦
      (∑ a, ∑ b, ∑ c, ∑ d,
        complexCenteredRankOneProjection N v a b *
          complexCenteredRankOneProjection N v c d * F a b c d) ^ 2) =
      fun v ↦ ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, ∑ g, ∑ h,
        (complexCenteredRankOneProjection N v a b *
          complexCenteredRankOneProjection N v c d *
          complexCenteredRankOneProjection N v e f *
          complexCenteredRankOneProjection N v g h) *
            (F a b c d * F e f g h) by
    funext v
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro f _
    apply Finset.sum_congr rfl
    intro g _
    apply Finset.sum_congr rfl
    intro h _
    ring]
  exact integrable_finsetSum _ fun a _ ↦
    integrable_finsetSum _ fun b _ ↦
      integrable_finsetSum _ fun c _ ↦
        integrable_finsetSum _ fun d _ ↦
          integrable_finsetSum _ fun e _ ↦
            integrable_finsetSum _ fun f _ ↦
              integrable_finsetSum _ fun g _ ↦
                integrable_finsetSum _ fun h _ ↦
                  (integrable_complexCenteredRankOneProjection_entry_mul_four_h14
                    hN a b c d e f g h).mul_const _

private theorem integrable_re_sq_of_complex_mul_self_h14
    {X : Type*} [MeasurableSpace X] {mu : Measure X} (f : X → ℂ)
    (hf : Integrable f mu) (hff : Integrable (fun x ↦ f x * f x) mu) :
    Integrable (fun x ↦ (f x).re ^ 2) mu := by
  apply hff.mono
  · exact AEStronglyMeasurable.pow hf.re.aestronglyMeasurable 2
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul]
    have hre := Complex.abs_re_le_norm (f x)
    have hsq := mul_self_le_mul_self (abs_nonneg (f x).re) hre
    calc
      (f x).re ^ 2 = |(f x).re| * |(f x).re| := by
        rw [pow_two, abs_mul_abs_self]
      _ ≤ ‖f x‖ * ‖f x‖ := hsq

theorem integrable_complexCenteredProjectiveSandwich_re_sq_h14
    {N : ℕ} (hN : 1 ≤ N) (W Y : ConcreteMatrixState N) :
    Integrable (fun v : ComplexUnitSphere N ↦
      (complexCenteredProjectiveSandwich v W Y).re ^ 2)
      (complexUnitSphereProbabilityMeasure N) := by
  let F : Fin N → Fin N → Fin N → Fin N → ℂ :=
    fun a b c d ↦ W b c * Y d a
  have hpoly : ∀ v : ComplexUnitSphere N,
      complexCenteredProjectiveSandwich v W Y =
        ∑ a, ∑ b, ∑ c, ∑ d,
          complexCenteredRankOneProjection N v a b *
            complexCenteredRankOneProjection N v c d * F a b c d := by
    intro v
    unfold complexCenteredProjectiveSandwich
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    simp only [F]
    ring
  have hsq := integrable_centeredProjectiveQuadraticPolynomial_sq_h14 hN F
  have hmul : Integrable (fun v : ComplexUnitSphere N ↦
      complexCenteredProjectiveSandwich v W Y *
        complexCenteredProjectiveSandwich v W Y)
      (complexUnitSphereProbabilityMeasure N) := by
    apply hsq.congr
    filter_upwards [] with v
    rw [hpoly v, pow_two]
  exact integrable_re_sq_of_complex_mul_self_h14 _
    (integrable_complexCenteredProjectiveSandwich hN W Y) hmul

theorem integrable_complexCenteredProjectiveConjugateSandwich_re_sq_h14
    {N : ℕ} (hN : 1 ≤ N) (R : ConcreteMatrixState N) :
    Integrable (fun v : ComplexUnitSphere N ↦
      (complexCenteredProjectiveConjugateSandwich v R).re ^ 2)
      (complexUnitSphereProbabilityMeasure N) := by
  let F : Fin N → Fin N → Fin N → Fin N → ℂ :=
    fun a b c d ↦ R b d * star (R a c)
  have hpoly : ∀ v : ComplexUnitSphere N,
      complexCenteredProjectiveConjugateSandwich v R =
        ∑ a, ∑ b, ∑ c, ∑ d,
          complexCenteredRankOneProjection N v a b *
            complexCenteredRankOneProjection N v c d * F a b c d := by
    intro v
    unfold complexCenteredProjectiveConjugateSandwich
    calc
      (∑ a, ∑ b, ∑ c, ∑ d,
        complexCenteredRankOneProjection N v a b * R b c *
          complexCenteredRankOneProjection N v d c * star (R a d)) =
          ∑ a, ∑ b, ∑ d, ∑ c,
            complexCenteredRankOneProjection N v a b * R b c *
              complexCenteredRankOneProjection N v d c * star (R a d) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.sum_comm]
      _ = ∑ a, ∑ b, ∑ c, ∑ d,
          complexCenteredRankOneProjection N v a b *
            complexCenteredRankOneProjection N v c d * F a b c d := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro d _
        simp only [F]
        ring
  have hsq := integrable_centeredProjectiveQuadraticPolynomial_sq_h14 hN F
  have hmul : Integrable (fun v : ComplexUnitSphere N ↦
      complexCenteredProjectiveConjugateSandwich v R *
        complexCenteredProjectiveConjugateSandwich v R)
      (complexUnitSphereProbabilityMeasure N) := by
    apply hsq.congr
    filter_upwards [] with v
    rw [hpoly v, pow_two]
  exact integrable_re_sq_of_complex_mul_self_h14 _
    (integrable_complexCenteredProjectiveConjugateSandwich hN R) hmul

/-! ## Exact scalar expansions before absolute values -/

def h14ProjectiveSandwichExpansion {N : ℕ} (K : ℕ)
    (v : ComplexUnitSphere N) (Y : ConcreteMatrixState N) : ℂ :=
  let a : ℂ := (((N : ℝ)⁻¹ : ℝ) : ℂ)
  let s : ℂ := (((concreteCOEExponent N K)⁻¹ : ℝ) : ℂ)
  let b := complexProjectiveTracePair v Y
  let e := complexProjectiveTracePair v (Y * Y)
  (1 - 2 * a) * b + a ^ 2 * Matrix.trace Y +
    s * (b ^ 2 - 2 * a * e + a ^ 2 * Matrix.trace (Y * Y))

theorem complexCenteredProjectiveSandwich_expansion_h14
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    complexCenteredProjectiveSandwich v
        (concreteCOEWMatrix N K A) (concreteCOEY N K A) =
      h14ProjectiveSandwichExpansion K v (concreteCOEY N K A) := by
  let P := complexRankOneProjection v
  let Q := concreteCenteredOrbitalDirection N v
  let Y := concreteCOEY N K A
  let a : ℂ := (((N : ℝ)⁻¹ : ℝ) : ℂ)
  let s : ℂ := (((concreteCOEExponent N K)⁻¹ : ℝ) : ℂ)
  have hP : P * P = P := by
    simpa only [P] using complexRankOneProjection_mul_self v
  have hQ : Q = P - a • (1 : ConcreteMatrixState N) := by rfl
  have hW : concreteCOEWMatrix N K A = 1 + s • Y := by rfl
  have hsplit :
      Q * ((1 + s • Y) * (Q * Y)) =
        Q * (Q * Y) + s • (Q * (Y * (Q * Y))) := by
    simp only [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul,
      Matrix.mul_add, Matrix.mul_smul, smul_smul]
  have hQtwo :
      Q * (Q * Y) =
        (1 - 2 * a) • (P * Y) + a ^ 2 • Y := by
    rw [hQ]
    have hexpand :
        (P - a • (1 : ConcreteMatrixState N)) *
            ((P - a • (1 : ConcreteMatrixState N)) * Y) =
          (P * P) * Y - (2 * a) • (P * Y) + a ^ 2 • Y := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one,
        Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Matrix.mul_assoc]
      module
    rw [hexpand, hP]
    module
  have hQYQY :
      Q * (Y * (Q * Y)) =
        P * (Y * (P * Y)) - a • (P * (Y * Y)) -
          a • (Y * (P * Y)) + a ^ 2 • (Y * Y) := by
    rw [hQ]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one,
      Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.mul_assoc]
    module
  rw [complexCenteredProjectiveSandwich_eq_trace_h14]
  change Matrix.trace (Q * (concreteCOEWMatrix N K A * (Q * Y))) = _
  rw [hW, hsplit, hQtwo, hQYQY]
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    smul_eq_mul]
  have hcycle : Matrix.trace (Y * (P * Y)) =
      Matrix.trace (P * (Y * Y)) := by
    exact (Matrix.trace_mul_cycle' P Y Y).symm
  have hquad : Matrix.trace (P * (Y * (P * Y))) =
      complexProjectiveTracePair v Y ^ 2 := by
    rw [show P * (Y * (P * Y)) = P * Y * P * Y by
      simp only [Matrix.mul_assoc]]
    simpa only [P, pow_two] using trace_rankOne_mul_mul_mul_h14 v Y Y
  have hlin : Matrix.trace (P * Y) = complexProjectiveTracePair v Y := by
    simpa only [P] using
      (complexProjectiveTracePair_eq_trace v Y).symm
  have hsquare : Matrix.trace (P * (Y * Y)) =
      complexProjectiveTracePair v (Y * Y) := by
    simpa only [P] using
      (complexProjectiveTracePair_eq_trace v (Y * Y)).symm
  rw [hcycle, hquad, hlin, hsquare]
  unfold h14ProjectiveSandwichExpansion
  simp only [Y, a, s]
  ring

def h14ProjectiveConjugateSandwichExpansion {N : ℕ}
    (v : ComplexUnitSphere N) (R : ConcreteMatrixState N) : ℂ :=
  let a : ℂ := (((N : ℝ)⁻¹ : ℝ) : ℂ)
  let d := complexProjectiveTracePair v (R * R.conjTranspose)
  complexProjectiveBilinearNormSq v R - 2 * a * d +
    a ^ 2 * Matrix.trace (R * R.conjTranspose)

/-- Exact expansion of the centered conjugate sandwich.  Symmetry makes its
two mixed terms coincide before any absolute value is introduced. -/
theorem complexCenteredProjectiveConjugateSandwich_expansion_h14
    {N : ℕ} (v : ComplexUnitSphere N) (R : ConcreteMatrixState N)
    (hR : R.IsSymm) :
    complexCenteredProjectiveConjugateSandwich v R =
      h14ProjectiveConjugateSandwichExpansion v R := by
  let P := complexRankOneProjection v
  let Q := concreteCenteredOrbitalDirection N v
  let a : ℂ := (((N : ℝ)⁻¹ : ℝ) : ℂ)
  have hQ : Q = P - a • (1 : ConcreteMatrixState N) := by rfl
  have hQt : Q.transpose = P.transpose - a • (1 : ConcreteMatrixState N) := by
    rw [hQ]
    simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
  have hexpand :
      Q * (R * (Q.transpose * R.conjTranspose)) =
        P * (R * (P.transpose * R.conjTranspose)) -
          a • (P * (R * R.conjTranspose)) -
          a • (R * (P.transpose * R.conjTranspose)) +
          a ^ 2 • (R * R.conjTranspose) := by
    rw [hQt, hQ]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one,
      Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.mul_assoc]
    module
  rw [complexCenteredProjectiveConjugateSandwich_eq_trace_h14]
  change Matrix.trace (Q * (R * (Q.transpose * R.conjTranspose))) = _
  rw [hexpand]
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    smul_eq_mul]
  rw [show Matrix.trace (P * (R * (P.transpose * R.conjTranspose))) =
      complexProjectiveBilinearNormSq v R by
    simpa only [P] using
      trace_rankOne_symmSandwich_eq_bilinearNormSq_h14 v R]
  rw [show Matrix.trace (P * (R * R.conjTranspose)) =
      complexProjectiveTracePair v (R * R.conjTranspose) by
    simpa only [P] using
      (complexProjectiveTracePair_eq_trace v (R * R.conjTranspose)).symm]
  rw [show Matrix.trace (R * (P.transpose * R.conjTranspose)) =
      complexProjectiveTracePair v (R * R.conjTranspose) by
    simpa only [P] using
      trace_symm_mul_transpose_rankOne_mul_conjTranspose_h14 v R hR]
  unfold h14ProjectiveConjugateSandwichExpansion
  simp only [a]
  ring

/-! ## Exact coefficient subledger -/

/-- The separate square bound produced by the `S = Tr(QWQY)` factor. -/
def h14ProjectiveSandwichSecondMomentEnvelope (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  8 * (concreteCOETraceOne N K A ^ 2 / (N : ℝ) ^ 2) +
    4 * (concreteCOETraceTwo N K A / (N : ℝ) ^ 2) +
    96 * (concreteCOETraceOne N K A ^ 4 /
      ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2)) +
    4 * (concreteCOETraceTwo N K A ^ 2 /
      ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2))

/-- The separate square bound produced by the
`C = Tr(Q R Qᵀ Rᴴ)` factor. -/
def h14ProjectiveConjugateSecondMomentEnvelope (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  40 * (concreteCOETraceOne N K A ^ 2 / (N : ℝ) ^ 2) +
    36 * (concreteCOETraceTwo N K A / (N : ℝ) ^ 2) +
    76 * (concreteCOETraceTwo N K A ^ 2 /
      ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2))

/-- PROVED scalar ledger: the factor coefficients become exactly
`1536,1280,3072,2560` after the score square contributes the factor `32`. -/
theorem h14_factorMomentEnvelopes_collect_sharpCoefficients
    (N K : ℕ) (A : ConcreteMatrixState N) :
    32 * (h14ProjectiveSandwichSecondMomentEnvelope N K A +
      h14ProjectiveConjugateSecondMomentEnvelope N K A) =
      h14ProjectiveCancellationSharpEnvelope N K A := by
  unfold h14ProjectiveSandwichSecondMomentEnvelope
    h14ProjectiveConjugateSecondMomentEnvelope
    h14ProjectiveCancellationSharpEnvelope
  ring

/-- **CONDITIONAL, non-endpoint.**  This is the remaining two-line finite
projective moment calculation after the exact `S` and `C` expansions above.
It asks only for the two separated square integrals and their sharp bounds;
it contains neither a score endpoint nor any beta-prime probability law. -/
def H14CenteredEllTwoSeparatedFactorMomentContract (N K : ℕ) : Prop :=
  ∀ (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)),
    Integrable (fun v : ComplexUnitSphere N ↦
      (complexCenteredProjectiveSandwich v
        (concreteCOEWMatrix N K A) (concreteCOEY N K A)).re ^ 2)
        (complexUnitSphereProbabilityMeasure N) ∧
    (∫ v : ComplexUnitSphere N,
      (complexCenteredProjectiveSandwich v
        (concreteCOEWMatrix N K A) (concreteCOEY N K A)).re ^ 2
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
      h14ProjectiveSandwichSecondMomentEnvelope N K A ∧
    Integrable (fun v : ComplexUnitSphere N ↦
      (complexCenteredProjectiveConjugateSandwich v
        (concreteCOERMatrix N K A)).re ^ 2)
        (complexUnitSphereProbabilityMeasure N) ∧
    (∫ v : ComplexUnitSphere N,
      (complexCenteredProjectiveConjugateSandwich v
        (concreteCOERMatrix N K A)).re ^ 2
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
      h14ProjectiveConjugateSecondMomentEnvelope N K A

/-- **CONDITIONAL, minimal non-endpoint blocker.**  Measurability and all
four-factor integrability are now proved above, so only these two numerical
finite-projective integral inequalities remain. -/
def H14CenteredEllTwoSeparatedFactorIntegralBoundsContract
    (N K : ℕ) : Prop :=
  ∀ (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)),
    (∫ v : ComplexUnitSphere N,
      (complexCenteredProjectiveSandwich v
        (concreteCOEWMatrix N K A) (concreteCOEY N K A)).re ^ 2
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
      h14ProjectiveSandwichSecondMomentEnvelope N K A ∧
    (∫ v : ComplexUnitSphere N,
      (complexCenteredProjectiveConjugateSandwich v
        (concreteCOERMatrix N K A)).re ^ 2
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
      h14ProjectiveConjugateSecondMomentEnvelope N K A

/-- PROVED reduction: the minimal two-inequality contract supplies the older
factor package because all its integrability fields are now internal. -/
theorem h14_separatedFactorMomentContract_of_integralBounds
    {N K : ℕ}
    (Hbounds : H14CenteredEllTwoSeparatedFactorIntegralBoundsContract N K) :
    H14CenteredEllTwoSeparatedFactorMomentContract N K := by
  intro hN hgap A hsymm hsupport
  rcases Hbounds hN hgap A hsymm hsupport with ⟨hS, hC⟩
  exact ⟨
    integrable_complexCenteredProjectiveSandwich_re_sq_h14 hN
      (concreteCOEWMatrix N K A) (concreteCOEY N K A),
    hS,
    integrable_complexCenteredProjectiveConjugateSandwich_re_sq_h14 hN
      (concreteCOERMatrix N K A),
    hC⟩

/-- Maximal axiom-free closure around the remaining separated finite-moment
contract.  In particular, all score algebra, integrability assembly, the
factor `32`, and the four final coefficients are discharged here. -/
theorem h14_centeredEllTwoProjectiveContraction_of_separatedFactorMoments
    {N K : ℕ}
    (Hfactor : H14CenteredEllTwoSeparatedFactorMomentContract N K) :
    H14CenteredEllTwoProjectiveContractionContract N K := by
  intro hN hgap A hsymm hsupport
  rcases Hfactor hN hgap A hsymm hsupport with
    ⟨hSint, hSbound, hCint, hCbound⟩
  let S : ComplexUnitSphere N → ℝ := fun v ↦
    (complexCenteredProjectiveSandwich v
      (concreteCOEWMatrix N K A) (concreteCOEY N K A)).re
  let C : ComplexUnitSphere N → ℝ := fun v ↦
    (complexCenteredProjectiveConjugateSandwich v
      (concreteCOERMatrix N K A)).re
  have hSbase : Integrable S (complexUnitSphereProbabilityMeasure N) := by
    have h := (integrable_complexCenteredProjectiveSandwich hN
      (concreteCOEWMatrix N K A) (concreteCOEY N K A)).re
    apply h.congr
    filter_upwards [] with v
    rfl
  have hCbase : Integrable C (complexUnitSphereProbabilityMeasure N) := by
    have h := (integrable_complexCenteredProjectiveConjugateSandwich hN
      (concreteCOERMatrix N K A)).re
    apply h.congr
    filter_upwards [] with v
    rfl
  have hSint' : Integrable (fun v ↦ S v ^ 2)
      (complexUnitSphereProbabilityMeasure N) := by
    simpa only [S] using hSint
  have hCint' : Integrable (fun v ↦ C v ^ 2)
      (complexUnitSphereProbabilityMeasure N) := by
    simpa only [C] using hCint
  have hmajorInt : Integrable (fun v ↦ 32 * (S v ^ 2 + C v ^ 2))
      (complexUnitSphereProbabilityMeasure N) :=
    (hSint'.add hCint').const_mul 32
  have hscoreMeas : AEStronglyMeasurable
      (h14CenteredSandwichSecondSquare N K A)
      (complexUnitSphereProbabilityMeasure N) := by
    unfold h14CenteredSandwichSecondSquare h14CenteredSandwichSecondScore
    exact AEStronglyMeasurable.pow
      ((hSbase.aestronglyMeasurable.add hCbase.aestronglyMeasurable).const_mul (-4)) 2
  have hpoint : ∀ v : ComplexUnitSphere N,
      ‖h14CenteredSandwichSecondSquare N K A v‖ ≤
        32 * (S v ^ 2 + C v ^ 2) := by
    intro v
    rw [Real.norm_eq_abs, abs_of_nonneg
      (h14CenteredSandwichSecondSquare_nonneg N K A v)]
    unfold h14CenteredSandwichSecondSquare h14CenteredSandwichSecondScore
    change (-4 * (S v + C v)) ^ 2 ≤ 32 * (S v ^ 2 + C v ^ 2)
    nlinarith [sq_nonneg (S v - C v)]
  have hscoreInt : Integrable (h14CenteredSandwichSecondSquare N K A)
      (complexUnitSphereProbabilityMeasure N) :=
    hmajorInt.mono' hscoreMeas (Filter.Eventually.of_forall hpoint)
  refine ⟨hscoreInt, ?_⟩
  calc
    (∫ v, ‖h14CenteredSandwichSecondSquare N K A v‖
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
        ∫ v, 32 * (S v ^ 2 + C v ^ 2)
          ∂(complexUnitSphereProbabilityMeasure N) :=
      integral_mono hscoreInt.norm hmajorInt hpoint
    _ = 32 * ((∫ v, S v ^ 2 ∂(complexUnitSphereProbabilityMeasure N)) +
        ∫ v, C v ^ 2 ∂(complexUnitSphereProbabilityMeasure N)) := by
      rw [integral_const_mul, integral_add hSint' hCint']
    _ ≤ 32 * (h14ProjectiveSandwichSecondMomentEnvelope N K A +
        h14ProjectiveConjugateSecondMomentEnvelope N K A) := by
      have hSbound' : (∫ v, S v ^ 2
          ∂(complexUnitSphereProbabilityMeasure N)) ≤
          h14ProjectiveSandwichSecondMomentEnvelope N K A := by
        simpa only [S] using hSbound
      have hCbound' : (∫ v, C v ^ 2
          ∂(complexUnitSphereProbabilityMeasure N)) ≤
          h14ProjectiveConjugateSecondMomentEnvelope N K A := by
        simpa only [C] using hCbound
      nlinarith
    _ = h14ProjectiveCancellationSharpEnvelope N K A :=
      h14_factorMomentEnvelopes_collect_sharpCoefficients N K A

/-- Final non-endpoint reduction directly from the smallest remaining pair
of finite-projective integral inequalities. -/
theorem h14_centeredEllTwoProjectiveContraction_of_integralBounds
    {N K : ℕ}
    (Hbounds : H14CenteredEllTwoSeparatedFactorIntegralBoundsContract N K) :
    H14CenteredEllTwoProjectiveContractionContract N K :=
  h14_centeredEllTwoProjectiveContraction_of_separatedFactorMoments
    (h14_separatedFactorMomentContract_of_integralBounds Hbounds)

#print axioms complexCenteredRankOneProjection_eq_orbitalDirection_apply_h14
#print axioms complexCenteredProjectiveSandwich_eq_trace_h14
#print axioms complexCenteredProjectiveConjugateSandwich_eq_trace_h14
#print axioms complexRankOneProjection_mul_mul_eq_tracePair_smul_h14
#print axioms trace_rankOne_mul_mul_mul_h14
#print axioms trace_rankOne_symmSandwich_eq_bilinearNormSq_h14
#print axioms trace_symm_mul_transpose_rankOne_mul_conjTranspose_h14
#print axioms complexCenteredProjectiveSandwich_expansion_h14
#print axioms complexCenteredProjectiveConjugateSandwich_expansion_h14
#print axioms integrable_complexCenteredRankOneProjection_entry_mul_four_h14
#print axioms integrable_complexCenteredProjectiveSandwich_re_sq_h14
#print axioms integrable_complexCenteredProjectiveConjugateSandwich_re_sq_h14
#print axioms h14_factorMomentEnvelopes_collect_sharpCoefficients
#print axioms h14_separatedFactorMomentContract_of_integralBounds
#print axioms h14_centeredEllTwoProjectiveContraction_of_separatedFactorMoments
#print axioms h14_centeredEllTwoProjectiveContraction_of_integralBounds

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

import A4.MatchingGramCanonical

/-!
# The exact finite inverse-moment Gram system

These algebraic identities retain every degree and the literal Gram inverse
in the A4 statement.  Solving the finite system is separated from proving
the analytic inverse-Wishart recurrence and the negative-parameter
nonsingularity assertion; those are not assumed to be completed here.
-/

open scoped BigOperators Matrix

noncomputable section

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

theorem orthogonalGram_transport {n : ℕ} (z : ℂ)
    (g : Equiv.Perm (Fin (2 * n))) (M N : PM n) :
    orthogonalGram n z (transportPairPartition g M) (transportPairPartition g N) =
      orthogonalGram n z M N := by
  simp only [orthogonalGram, matchingKappa_transport]

theorem orthogonalGram_submatrix_relabel {n : ℕ} (z : ℂ)
    (g : Equiv.Perm (Fin (2 * n))) :
    (orthogonalGram n z).submatrix (matchingRelabelEquiv g) (matchingRelabelEquiv g) =
      orthogonalGram n z := by
  ext M N
  exact orthogonalGram_transport z g M N

theorem orthogonalGram_inv_transport {n : ℕ} (z : ℂ)
    (g : Equiv.Perm (Fin (2 * n))) (M N : PM n) :
    (orthogonalGram n z)⁻¹ (transportPairPartition g M) (transportPairPartition g N) =
      (orthogonalGram n z)⁻¹ M N := by
  have heq :
      ((orthogonalGram n z)⁻¹).submatrix (matchingRelabelEquiv g) (matchingRelabelEquiv g) =
        (orthogonalGram n z)⁻¹ := by
    rw [← Matrix.inv_submatrix_equiv, orthogonalGram_submatrix_relabel]
  exact congrFun (congrFun heq M) N

theorem orthogonalWg_relative {n : ℕ} (z : ℂ)
    (g h : Equiv.Perm (Fin (2 * n))) :
    orthogonalWg (g⁻¹ * h) z =
      (orthogonalGram n z)⁻¹ (transportedPairPartition g) (transportedPairPartition h) := by
  unfold orthogonalWg transportedPairPartition
  have heq := orthogonalGram_inv_transport z g (standardPairPartition n)
    (transportPairPartition (g⁻¹ * h) (standardPairPartition n))
  simpa only [← transportPairPartition_mul, mul_inv_cancel_left] using heq.symm

/-- Scalar inversion commutes with the totalized inverse, including singular matrices. -/
theorem matrix_inv_smul_complex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (c : ℂ) (hc : c ≠ 0) :
    (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  by_cases hA : IsUnit A.det
  · apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_inv_cancel₀ hc, one_smul, Matrix.mul_nonsing_inv A hA]
  · have hdet : A.det = 0 := by
      simpa only [isUnit_iff_ne_zero, not_not] using hA
    have hscaled : ¬IsUnit (c • A).det := by
      rw [Matrix.det_smul, hdet, mul_zero]
      exact not_isUnit_zero
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hscaled,
      Matrix.nonsing_inv_apply_not_isUnit _ hA, smul_zero]

/-- The normalized negative Gram operator whose inverse is Matsumoto's modified coefficient. -/
def normalizedOrthogonalGram (n : ℕ) (gamma : ℝ) : Matrix (PM n) (PM n) ℂ :=
  ((-2 : ℂ) ^ n)⁻¹ • orthogonalGram n (-2 * (gamma : ℂ))

/-- All entries of the modified inverse coefficient matrix, including the literal source scaling. -/
def modifiedGramInverse (n : ℕ) (gamma : ℝ) : Matrix (PM n) (PM n) ℂ :=
  ((-1 : ℂ) ^ n * (2 : ℂ) ^ n) • (orthogonalGram n (-2 * (gamma : ℂ)))⁻¹

theorem modifiedGramInverse_eq_inv_normalized (n : ℕ) (gamma : ℝ) :
    modifiedGramInverse n gamma = (normalizedOrthogonalGram n gamma)⁻¹ := by
  unfold modifiedGramInverse normalizedOrthogonalGram
  rw [matrix_inv_smul_complex _ _ (inv_ne_zero (pow_ne_zero n (by norm_num)))]
  simp only [inv_inv, ← mul_pow]
  norm_num

@[simp] theorem normalizedOrthogonalGram_diag {n : ℕ} (gamma : ℝ) (M : PM n) :
    normalizedOrthogonalGram n gamma M M = (gamma : ℂ) ^ n := by
  simp only [normalizedOrthogonalGram, Matrix.smul_apply, smul_eq_mul,
    orthogonalGram_diag, mul_pow]
  exact inv_mul_cancel_left₀ (pow_ne_zero n (by norm_num : (-2 : ℂ) ≠ 0)) _

theorem wgTilde_relative {n : ℕ} (gamma : ℝ)
    (g h : Equiv.Perm (Fin (2 * n))) :
    wgTilde (g⁻¹ * h) gamma = modifiedGramInverse n gamma
      (transportedPairPartition g) (transportedPairPartition h) := by
  simp only [wgTilde, modifiedGramInverse, Matrix.smul_apply, smul_eq_mul,
    orthogonalWg_relative]

theorem normalizedOrthogonalGram_mul_modified {n : ℕ} (gamma : ℝ)
    (hdet : IsUnit (orthogonalGram n (-2 * (gamma : ℂ))).det) :
    normalizedOrthogonalGram n gamma * modifiedGramInverse n gamma = 1 := by
  unfold normalizedOrthogonalGram modifiedGramInverse
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← mul_pow, Matrix.mul_nonsing_inv _ hdet]
  norm_num

theorem modified_mul_normalizedOrthogonalGram {n : ℕ} (gamma : ℝ)
    (hdet : IsUnit (orthogonalGram n (-2 * (gamma : ℂ))).det) :
    modifiedGramInverse n gamma * normalizedOrthogonalGram n gamma = 1 := by
  unfold normalizedOrthogonalGram modifiedGramInverse
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← mul_pow, Matrix.nonsing_inv_mul _ hdet]
  norm_num

/-- A proved right-inverse recurrence identifies the coefficient matrix without another axiom. -/
theorem modifiedGramInverse_eq_of_rightInverse {n : ℕ} (gamma : ℝ)
    (B : Matrix (PM n) (PM n) ℂ)
    (hB : normalizedOrthogonalGram n gamma * B = 1) :
    modifiedGramInverse n gamma = B := by
  rw [modifiedGramInverse_eq_inv_normalized]
  exact Matrix.inv_eq_right_inv hB

/-- The same recurrence supplies the missing Gram nonsingularity fact. -/
theorem orthogonalGram_isUnit_det_of_rightInverse {n : ℕ} (gamma : ℝ)
    (B : Matrix (PM n) (PM n) ℂ)
    (hB : normalizedOrthogonalGram n gamma * B = 1) :
    IsUnit (orthogonalGram n (-2 * (gamma : ℂ))).det := by
  have hscaled := Matrix.isUnit_det_of_right_inverse hB
  unfold normalizedOrthogonalGram at hscaled
  rw [Matrix.det_smul] at hscaled
  exact isUnit_of_mul_isUnit_right hscaled

/-- The exact finite matching convolution, with Matsumoto's normalization. -/
theorem wgTilde_matching_convolution {n : ℕ} (gamma : ℝ)
    (hdet : IsUnit (orthogonalGram n (-2 * (gamma : ℂ))).det)
    (g h : Equiv.Perm (Fin (2 * n))) :
    ∑ M : PerfectMatching n,
      (((-2 : ℂ) ^ n)⁻¹ * (-2 * (gamma : ℂ)) ^ kappa (g⁻¹ * M.toPerm)) *
        wgTilde (M.toPerm⁻¹ * h) gamma =
      if transportedPairPartition g = transportedPairPartition h then 1 else 0 := by
  classical
  have hsum := congrFun
    (congrFun (normalizedOrthogonalGram_mul_modified gamma hdet)
      (transportedPairPartition g)) (transportedPairPartition h)
  change
    (∑ P : PM n, normalizedOrthogonalGram n gamma (transportedPairPartition g) P *
      modifiedGramInverse n gamma P (transportedPairPartition h)) = _ at hsum
  rw [← sum_canonical_eq_sum_pairPartition] at hsum
  simpa only [normalizedOrthogonalGram, canonicalToPairPartition, Matrix.smul_apply,
    smul_eq_mul, orthogonalGram, ← kappa_relative, ← wgTilde_relative,
    Matrix.one_apply] using hsum

/-- Any independently proved solution of the exact full matching system has the stated coefficients. -/
theorem wgTilde_eq_of_matching_system {n : ℕ} (gamma : ℝ)
    (B : Matrix (PM n) (PM n) ℂ)
    (hB : ∀ P Q : PM n,
      (∑ R : PM n, normalizedOrthogonalGram n gamma P R * B R Q) =
        if P = Q then 1 else 0)
    (g h : Equiv.Perm (Fin (2 * n))) :
    wgTilde (g⁻¹ * h) gamma = B (transportedPairPartition g) (transportedPairPartition h) := by
  classical
  have hmat : normalizedOrthogonalGram n gamma * B = 1 := by
    ext P Q
    exact hB P Q
  rw [wgTilde_relative, modifiedGramInverse_eq_of_rightInverse gamma B hmat]

@[simp] theorem orthogonalGram_one (z : ℂ) :
    orthogonalGram 1 z = z • (1 : Matrix (PM 1) (PM 1) ℂ) := by
  ext M N
  have hMN : M = N := Subsingleton.elim _ _
  subst N
  simp only [orthogonalGram_diag, pow_one, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply_eq, mul_one]

theorem orthogonalGram_one_isUnit (gamma : ℝ) (hgamma : 0 < gamma) :
    IsUnit (orthogonalGram 1 (-2 * (gamma : ℂ))).det := by
  rw [orthogonalGram_one, Matrix.det_smul]
  have hgammaC : (gamma : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hgamma
  simp only [Matrix.det_one, mul_one]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ (mul_ne_zero (by norm_num) hgammaC))

@[simp] theorem orthogonalWg_one (g : Equiv.Perm (Fin (2 * 1))) (z : ℂ) :
    orthogonalWg g z = z⁻¹ := by
  by_cases hz : z = 0
  · subst z
    simp [orthogonalWg, orthogonalGram_one]
  · unfold orthogonalWg
    rw [orthogonalGram_one, matrix_inv_smul_complex _ z hz]
    simp only [inv_one, Matrix.smul_apply, smul_eq_mul]
    have hMN : standardPairPartition 1 = transportedPairPartition g := Subsingleton.elim _ _
    rw [hMN, Matrix.one_apply_eq, mul_one]

@[simp] theorem wgTilde_one (g : Equiv.Perm (Fin (2 * 1))) (gamma : ℝ) :
    wgTilde g gamma = (gamma : ℂ)⁻¹ := by
  norm_num [wgTilde, orthogonalWg_one, mul_inv_rev, inv_neg]
  ring

end MatsumotoPaper

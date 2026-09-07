import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.EvenScoreFormalMeanConditional
import LogdetLean.GramHafnian.AuxiliaryGaussian
import Mathlib.Tactic

/-!
# Finite Gaussian Wick contractions for the beta-prime numerator

The module proves the elementary numerator identities isolated by
`BetaPrimeSecondOrderFiniteWickFormula`.  It starts from the literal scalar
Gaussian moments, transfers the four-coordinate pairing rule to a finite
Gaussian matrix, and contracts the resulting Wishart entry tensor.  No
inverse-Wishart moment theorem is used here.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart

@[simp]
private theorem colorMultiplicity_fin_four
    {p : ℕ} (a b c d x : Fin p) :
    colorMultiplicity (![a, b, c, d] : Fin 4 → Fin p) x =
      (if a = x then 1 else 0) + (if b = x then 1 else 0) +
        (if c = x then 1 else 0) + (if d = x then 1 else 0) := by
  unfold colorMultiplicity
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_four]
  simp
  rfl

private theorem prod_standardRealGaussianMoment_eq_zero_of_odd
    {p r : ℕ} (c : Fin r → Fin p) (a : Fin p)
    (ha : Odd (colorMultiplicity c a)) :
    (∏ x : Fin p, standardRealGaussianMoment (colorMultiplicity c x)) = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  simp [standardRealGaussianMoment, ha]

private theorem prod_standardRealGaussianMoment_four_same
    {p : ℕ} (a : Fin p) :
    (∏ x : Fin p,
      standardRealGaussianMoment
        (colorMultiplicity (![a, a, a, a] : Fin 4 → Fin p) x)) = 3 := by
  rw [Finset.prod_eq_single a]
  · norm_num [standardRealGaussianMoment]
  · intro b hb hba
    have hab : a ≠ b := Ne.symm hba
    simp [standardRealGaussianMoment, hab]
  · simp

private theorem prod_standardRealGaussianMoment_two_pairs
    {p : ℕ} (a b : Fin p) (hab : a ≠ b) :
    (∏ x : Fin p,
      standardRealGaussianMoment
        (colorMultiplicity (![a, a, b, b] : Fin 4 → Fin p) x)) = 1 := by
  apply Finset.prod_eq_one
  intro x hx
  by_cases hxa : x = a
  · subst x
    simp [standardRealGaussianMoment, hab, Ne.symm hab]
  · by_cases hxb : x = b
    · subst x
      simp [standardRealGaussianMoment, hab, Ne.symm hab]
    · have hax : a ≠ x := Ne.symm hxa
      have hbx : b ≠ x := Ne.symm hxb
      simp [standardRealGaussianMoment, hxa, hxb, hax, hbx]

private theorem prod_standardRealGaussianMoment_four_pairings
    {p : ℕ} (i j k l : Fin p) :
    (∏ x : Fin p,
      standardRealGaussianMoment
        (colorMultiplicity (![i, j, k, l] : Fin 4 → Fin p) x)) =
      realKroneckerDelta i j * realKroneckerDelta k l +
        realKroneckerDelta i k * realKroneckerDelta j l +
        realKroneckerDelta i l * realKroneckerDelta j k := by
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      by_cases hil : i = l
      · subst l
        convert prod_standardRealGaussianMoment_four_same i using 1 <;>
          norm_num [realKroneckerDelta]
      · simpa [realKroneckerDelta, hil] using
          prod_standardRealGaussianMoment_eq_zero_of_odd
            (![i, i, i, l] : Fin 4 → Fin p) i
              (by simp [hil, Ne.symm hil] <;> norm_num)
    · by_cases hil : i = l
      · subst l
        simpa [realKroneckerDelta, hik, Ne.symm hik] using
          prod_standardRealGaussianMoment_eq_zero_of_odd
            (![i, i, k, i] : Fin 4 → Fin p) i
              (by simp [hik, Ne.symm hik] <;> norm_num)
      · by_cases hkl : k = l
        · subst l
          simpa [realKroneckerDelta, hik, Ne.symm hik] using
            prod_standardRealGaussianMoment_two_pairs i k hik
        · simpa [realKroneckerDelta, hik, hil, hkl,
              Ne.symm hik, Ne.symm hil, Ne.symm hkl] using
            prod_standardRealGaussianMoment_eq_zero_of_odd
              (![i, i, k, l] : Fin 4 → Fin p) k
                (by simp [hik, hkl, Ne.symm hik, Ne.symm hkl] <;> norm_num)
  · by_cases hik : i = k
    · subst k
      by_cases hil : i = l
      · subst l
        simpa [realKroneckerDelta, hij, Ne.symm hij] using
          prod_standardRealGaussianMoment_eq_zero_of_odd
            (![i, j, i, i] : Fin 4 → Fin p) i
              (by simp [hij, Ne.symm hij] <;> norm_num)
      · by_cases hjl : j = l
        · subst l
          simpa [realKroneckerDelta, hij, Ne.symm hij,
              add_comm, add_left_comm, add_assoc] using
            prod_standardRealGaussianMoment_two_pairs i j hij
        · simpa [realKroneckerDelta, hij, hil, hjl,
              Ne.symm hij, Ne.symm hil, Ne.symm hjl] using
            prod_standardRealGaussianMoment_eq_zero_of_odd
              (![i, j, i, l] : Fin 4 → Fin p) j
                (by simp [hij, hjl, Ne.symm hij, Ne.symm hjl] <;> norm_num)
    · by_cases hil : i = l
      · subst l
        by_cases hjk : j = k
        · subst k
          simpa [realKroneckerDelta, hij, Ne.symm hij,
              add_comm, add_left_comm, add_assoc] using
            prod_standardRealGaussianMoment_two_pairs i j hij
        · simpa [realKroneckerDelta, hij, hik, hjk,
              Ne.symm hij, Ne.symm hik, Ne.symm hjk] using
            prod_standardRealGaussianMoment_eq_zero_of_odd
              (![i, j, k, i] : Fin 4 → Fin p) j
                (by simp [hij, hjk, Ne.symm hij, Ne.symm hjk] <;> norm_num)
      · by_cases hjk : j = k
        · subst k
          by_cases hjl : j = l
          · subst l
            simpa [realKroneckerDelta, hij, Ne.symm hij] using
              prod_standardRealGaussianMoment_eq_zero_of_odd
                (![i, j, j, j] : Fin 4 → Fin p) j
                  (by simp [hij, Ne.symm hij] <;> norm_num)
          · simpa [realKroneckerDelta, hij, hil, hjl,
                Ne.symm hij, Ne.symm hil, Ne.symm hjl] using
              prod_standardRealGaussianMoment_eq_zero_of_odd
                (![i, j, j, l] : Fin 4 → Fin p) i
                  (by simp [hij, hil, Ne.symm hij, Ne.symm hil] <;> norm_num)
        · by_cases hjl : j = l
          · subst l
            simpa [realKroneckerDelta, hij, hik, hjk,
                Ne.symm hij, Ne.symm hik, Ne.symm hjk] using
              prod_standardRealGaussianMoment_eq_zero_of_odd
                (![i, j, k, j] : Fin 4 → Fin p) i
                  (by simp [hij, hik, Ne.symm hij, Ne.symm hik] <;> norm_num)
          · by_cases hkl : k = l
            · subst l
              simpa [realKroneckerDelta, hij, hik, hjk,
                  Ne.symm hij, Ne.symm hik, Ne.symm hjk] using
                prod_standardRealGaussianMoment_eq_zero_of_odd
                  (![i, j, k, k] : Fin 4 → Fin p) i
                    (by simp [hij, hik, Ne.symm hij, Ne.symm hik] <;> norm_num)
            · simpa [realKroneckerDelta, hij, hik, hil, hjk, hjl, hkl,
                  Ne.symm hij, Ne.symm hik, Ne.symm hil, Ne.symm hjk,
                  Ne.symm hjl, Ne.symm hkl] using
                prod_standardRealGaussianMoment_eq_zero_of_odd
                  (![i, j, k, l] : Fin 4 → Fin p) i
                    (by simp [hij, hik, hil, Ne.symm hij, Ne.symm hik,
                      Ne.symm hil] <;> norm_num)

/-- The real standard-Gaussian four-coordinate Wick formula. -/
theorem integral_standardRealGaussianVector_coordinate_four
    {p : ℕ} (i j k l : Fin p) :
    (∫ x : Fin p → ℝ, x i * x j * x k * x l
      ∂standardRealGaussianVectorMeasure p) =
      realKroneckerDelta i j * realKroneckerDelta k l +
        realKroneckerDelta i k * realKroneckerDelta j l +
        realKroneckerDelta i l * realKroneckerDelta j k := by
  classical
  let c : Fin 4 → Fin p := ![i, j, k, l]
  calc
    (∫ x : Fin p → ℝ, x i * x j * x k * x l
      ∂standardRealGaussianVectorMeasure p) =
        ∫ x : Fin p → ℝ, ∏ t : Fin 4, x (c t)
          ∂standardRealGaussianVectorMeasure p := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [Fin.prod_univ_four]
      simp [c]
    _ = ∫ x : Fin p → ℝ,
          realCoordinatePowerProduct (colorMultiplicity c) x
          ∂standardRealGaussianVectorMeasure p := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact prod_comp_eq_coordinatePowerProduct c x
    _ = ∏ a : Fin p,
          ∫ z : ℝ, z ^ colorMultiplicity c a ∂gaussianReal 0 1 := by
      exact integral_realCoordinatePowerProduct_pi
        (K := Fin p) (gaussianReal 0 1) (colorMultiplicity c)
    _ = _ := by
      simp_rw [integral_pow_gaussianReal_eq_standardRealGaussianMoment]
      dsimp only [c]
      exact prod_standardRealGaussianMoment_four_pairings i j k l

/-- Four selected coordinates of a standard real Gaussian vector are
integrable. -/
theorem integrable_standardRealGaussianVector_coordinate_four
    {p : ℕ} (i j k l : Fin p) :
    Integrable (fun x : Fin p → ℝ ↦ x i * x j * x k * x l)
      (standardRealGaussianVectorMeasure p) := by
  classical
  let c : Fin 4 → Fin p := ![i, j, k, l]
  simpa [c, Fin.prod_univ_four, mul_assoc] using
    (integrable_realColorProduct_standardGaussian c)

/-- Four matrix coordinates obey the row-and-column Wick pairing rule. -/
theorem integral_standardRealGaussianMatrix_coordinate_four
    {rows p : ℕ} (a b : Fin rows) (i j k l : Fin p) :
    (∫ R : Matrix (Fin rows) (Fin p) ℝ,
        R a i * R a j * R b k * R b l
        ∂standardRealGaussianMatrixMeasure rows p) =
      realKroneckerDelta i j * realKroneckerDelta k l +
        realKroneckerDelta a b *
          (realKroneckerDelta i k * realKroneckerDelta j l +
            realKroneckerDelta i l * realKroneckerDelta j k) := by
  classical
  rw [← show Measure.map (curriedMatrixMeasurableEquiv rows p)
      (Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p) =
      standardRealGaussianMatrixMeasure rows p by
    unfold standardRealGaussianMatrixMeasure
    change Measure.map (id : (Fin rows → Fin p → ℝ) →
        (Fin rows → Fin p → ℝ))
      (Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p) =
      Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p
    exact Measure.map_id]
  rw [integral_map (curriedMatrixMeasurableEquiv rows p).measurable.aemeasurable
    (show AEStronglyMeasurable
      (fun R : Matrix (Fin rows) (Fin p) ℝ ↦
        R a i * R a j * R b k * R b l)
      (Measure.map (curriedMatrixMeasurableEquiv rows p)
        (Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p)) by
      fun_prop)]
  change (∫ R : Fin rows → Fin p → ℝ,
      R a i * R a j * R b k * R b l
      ∂Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p) = _
  by_cases hab : a = b
  · subst b
    calc
      (∫ R : Fin rows → Fin p → ℝ,
          R a i * R a j * R a k * R a l
          ∂Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p) =
          ∫ x : Fin p → ℝ, x i * x j * x k * x l
            ∂standardRealGaussianVectorMeasure p :=
        integral_comp_eval
          (μ := fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p)
          (i := a)
          (integrable_standardRealGaussianVector_coordinate_four i j k l).aestronglyMeasurable
      _ = _ := by
        rw [integral_standardRealGaussianVector_coordinate_four]
        simp [realKroneckerDelta, add_assoc]
  · let f : Fin rows → (Fin p → ℝ) → ℝ := fun r x ↦
        if r = a then x i * x j
        else if r = b then x k * x l
        else 1
    have hpoint (R : Fin rows → Fin p → ℝ) :
        (∏ r, f r (R r)) = R a i * R a j * R b k * R b l := by
      have hprod := Finset.prod_eq_mul_of_mem
        (s := Finset.univ) (f := fun r ↦ f r (R r))
        a b (Finset.mem_univ a) (Finset.mem_univ b) hab
        (by
          intro r hr hne
          simp [f, hne.1, hne.2])
      simpa [f, hab, Ne.symm hab, mul_assoc] using hprod
    calc
      (∫ R : Fin rows → Fin p → ℝ,
          R a i * R a j * R b k * R b l
          ∂Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p) =
          ∫ R : Fin rows → Fin p → ℝ, ∏ r, f r (R r)
            ∂Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p := by
        apply integral_congr_ae
        filter_upwards [] with R
        exact (hpoint R).symm
      _ = ∏ r, ∫ x : Fin p → ℝ, f r x
            ∂standardRealGaussianVectorMeasure p := by
        exact integral_fintype_prod_eq_prod f
      _ = (if i = j then 1 else 0) * (if k = l then 1 else 0) := by
        have hprod := Finset.prod_eq_mul_of_mem
          (s := Finset.univ)
          (f := fun r ↦ ∫ x : Fin p → ℝ, f r x
            ∂standardRealGaussianVectorMeasure p)
          a b (Finset.mem_univ a) (Finset.mem_univ b) hab
          (by
            intro r hr hne
            simp [f, hne.1, hne.2])
        simpa [f, hab, Ne.symm hab,
          integral_standardRealGaussianVector_coordinate_mul] using hprod
      _ = _ := by
        simp [realKroneckerDelta, hab, Ne.symm hab]

/-- Four selected entries of a finite standard-Gaussian matrix are
integrable. -/
theorem integrable_standardRealGaussianMatrix_coordinate_four
    {rows p : ℕ} (a b : Fin rows) (i j k l : Fin p) :
    Integrable
      (fun R : Matrix (Fin rows) (Fin p) ℝ ↦
        R a i * R a j * R b k * R b l)
      (standardRealGaussianMatrixMeasure rows p) := by
  have h442 : ENNReal.HolderTriple 4 4 2 :=
    ENNReal.HolderTriple.of_toReal (by constructor <;> norm_num)
  let _ := h442
  have hij : MemLp
      (fun R : Matrix (Fin rows) (Fin p) ℝ ↦ R a i * R a j) 2
      (standardRealGaussianMatrixMeasure rows p) :=
    (standardRealGaussianMatrix_coordinate_memLp_four a j).mul'
      (standardRealGaussianMatrix_coordinate_memLp_four a i)
  have hkl : MemLp
      (fun R : Matrix (Fin rows) (Fin p) ℝ ↦ R b k * R b l) 2
      (standardRealGaussianMatrixMeasure rows p) :=
    (standardRealGaussianMatrix_coordinate_memLp_four b l).mul'
      (standardRealGaussianMatrix_coordinate_memLp_four b k)
  have h221 : ENNReal.HolderTriple 2 2 1 :=
    ENNReal.HolderTriple.of_toReal (by constructor <;> norm_num)
  let _ := h221
  simpa [mul_assoc] using memLp_one_iff_integrable.mp (hkl.mul' hij)

/-- Exact second entry tensor of a variance-one real Wishart matrix. -/
theorem integral_realWishartGram_entry_mul_entry_standardGaussian_eq
    {rows p : ℕ} (i j k l : Fin p) :
    (∫ R : Matrix (Fin rows) (Fin p) ℝ,
        realWishartGram R i j * realWishartGram R k l
        ∂standardRealGaussianMatrixMeasure rows p) =
      (rows : ℝ) ^ 2 *
          (realKroneckerDelta i j * realKroneckerDelta k l) +
      (rows : ℝ) *
          (realKroneckerDelta i k * realKroneckerDelta j l +
            realKroneckerDelta i l * realKroneckerDelta j k) := by
  classical
  let A : ℝ := realKroneckerDelta i j * realKroneckerDelta k l
  let B : ℝ := realKroneckerDelta i k * realKroneckerDelta j l +
    realKroneckerDelta i l * realKroneckerDelta j k
  calc
    (∫ R : Matrix (Fin rows) (Fin p) ℝ,
        realWishartGram R i j * realWishartGram R k l
        ∂standardRealGaussianMatrixMeasure rows p) =
        ∑ b : Fin rows, ∑ a : Fin rows,
          ∫ R : Matrix (Fin rows) (Fin p) ℝ,
            R a i * R a j * (R b k * R b l)
            ∂standardRealGaussianMatrixMeasure rows p := by
      simp only [realWishartGram, Matrix.mul_apply, Matrix.transpose_apply,
        Finset.sum_mul, Finset.mul_sum]
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro b hb
        rw [integral_finsetSum]
        intro a ha
        simpa [mul_assoc] using
          integrable_standardRealGaussianMatrix_coordinate_four a b i j k l
      · intro b hb
        exact integrable_finsetSum Finset.univ fun a ha ↦ by
          simpa [mul_assoc] using
            integrable_standardRealGaussianMatrix_coordinate_four a b i j k l
    _ = ∑ b : Fin rows, ∑ a : Fin rows,
          (A + realKroneckerDelta a b * B) := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro a ha
      rw [show (fun R : Matrix (Fin rows) (Fin p) ℝ ↦
          R a i * R a j * (R b k * R b l)) =
          (fun R ↦ R a i * R a j * R b k * R b l) by
        funext R
        ring]
      simpa only [A, B] using
        integral_standardRealGaussianMatrix_coordinate_four a b i j k l
    _ = ∑ b : Fin rows, ((rows : ℝ) * A + B) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul,
        sum_realKroneckerDelta_right]
      ring
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, A, B]
      ring

private theorem wishart_traceTwo_tensor_contraction
    {p : ℕ} (n : ℝ) (C : Matrix (Fin p) (Fin p) ℝ)
    (hC : C.IsSymm) :
    (∑ i : Fin p, ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
      C i j * C k l *
        (n ^ 2 * realKroneckerDelta j k * realKroneckerDelta l i +
          n * (realKroneckerDelta j l * realKroneckerDelta k i +
            realKroneckerDelta j i * realKroneckerDelta k l))) =
      n * (n + 1) * Matrix.trace (C ^ 2) +
        n * Matrix.trace C ^ 2 := by
  classical
  have hsymm : ∀ i j, C j i = C i j := Matrix.IsSymm.ext_iff.mp hC
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, pow_two]
  ring_nf
  simp [realKroneckerDelta, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_mul,
    mul_ite, ite_mul, Fintype.sum_ite_eq, Fintype.sum_ite_eq',
    Finset.sum_ite_eq, Finset.sum_ite_eq', hsymm]
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  have hmul_comm :
      (∑ x : Fin p, ∑ y : Fin p, C x y * C x y * n) =
        ∑ x : Fin p, ∑ y : Fin p, n * (C x y * C x y) := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    ring
  have hmul_sq_comm :
      (∑ x : Fin p, ∑ y : Fin p, C x y * C x y * (n * n)) =
        ∑ x : Fin p, ∑ y : Fin p, n * n * (C x y * C x y) := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    ring
  have hdiag_comm :
      (∑ x : Fin p, ∑ y : Fin p, C x x * C y y * n) =
        ∑ x : Fin p, ∑ y : Fin p, n * (C y y * C x x) := by
    calc
      (∑ x : Fin p, ∑ y : Fin p, C x x * C y y * n) =
          ∑ x : Fin p, ∑ y : Fin p, n * (C x x * C y y) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = _ := by rw [Finset.sum_comm]
  rw [hmul_comm, hmul_sq_comm, hdiag_comm]

private theorem wishart_traceOneSquare_tensor_contraction
    {p : ℕ} (n : ℝ) (C : Matrix (Fin p) (Fin p) ℝ)
    (hC : C.IsSymm) :
    (∑ i : Fin p, ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
      C i j * C k l *
        (n ^ 2 * realKroneckerDelta j i * realKroneckerDelta l k +
          n * (realKroneckerDelta j l * realKroneckerDelta i k +
            realKroneckerDelta j k * realKroneckerDelta i l))) =
      n ^ 2 * Matrix.trace C ^ 2 +
        2 * n * Matrix.trace (C ^ 2) := by
  classical
  have hsymm : ∀ i j, C j i = C i j := Matrix.IsSymm.ext_iff.mp hC
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, pow_two]
  ring_nf
  simp [realKroneckerDelta, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_mul,
    mul_ite, ite_mul, Fintype.sum_ite_eq, Fintype.sum_ite_eq',
    Finset.sum_ite_eq, Finset.sum_ite_eq', hsymm]
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  have hmul_comm :
      (∑ x : Fin p, ∑ y : Fin p, C x y * C x y * n) =
        ∑ x : Fin p, ∑ y : Fin p, n * (C x y * C x y) := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    ring
  have hdiag_comm :
      (∑ x : Fin p, ∑ y : Fin p, C x x * C y y * (n * n)) =
        ∑ x : Fin p, ∑ y : Fin p, n * n * (C y y * C x x) := by
    calc
      (∑ x : Fin p, ∑ y : Fin p, C x x * C y y * (n * n)) =
          ∑ x : Fin p, ∑ y : Fin p, n * n * (C x x * C y y) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = _ := by rw [Finset.sum_comm]
  have hdouble :
      (∑ x : Fin p, ∑ y : Fin p, n * (C x y * C x y) * 2) =
        (∑ x : Fin p, ∑ y : Fin p, n * (C x y * C x y)) +
          ∑ x : Fin p, ∑ y : Fin p, n * (C x y * C x y) := by
    calc
      (∑ x : Fin p, ∑ y : Fin p, n * (C x y * C x y) * 2) =
          ∑ x : Fin p, ∑ y : Fin p,
            (n * (C x y * C x y) + n * (C x y * C x y)) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = _ := by simp only [Finset.sum_add_distrib]
  rw [hmul_comm, hdiag_comm, hdouble]

private theorem trace_const_mul_matrix_sq_expansion
    {p : ℕ} (C W : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace ((C * W) ^ 2) =
      ∑ i : Fin p, ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
        C i j * C k l * (W j k * W l i) := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, pow_two,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∑ k : Fin p, ∑ l : Fin p, ∑ j : Fin p,
        C i j * W j k * (C k l * W l i)) =
        ∑ k : Fin p, ∑ j : Fin p, ∑ l : Fin p,
          C i j * W j k * (C k l * W l i) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
    _ = ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
          C i j * W j k * (C k l * W l i) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      ring

private theorem trace_const_mul_matrix_square_expansion
    {p : ℕ} (C W : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace (C * W) ^ 2 =
      ∑ i : Fin p, ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
        C i j * C k l * (W j i * W l k) := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, pow_two,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

private theorem integral_fintype_sum_four
    {Omega I J L M : Type*} [MeasurableSpace Omega]
    [Fintype I] [Fintype J] [Fintype L] [Fintype M]
    (mu : Measure Omega) (f : I → J → L → M → Omega → ℝ)
    (hf : ∀ i j l m, Integrable (f i j l m) mu) :
    (∫ omega, ∑ i : I, ∑ j : J, ∑ l : L, ∑ m : M,
        f i j l m omega ∂mu) =
      ∑ i : I, ∑ j : J, ∑ l : L, ∑ m : M,
        ∫ omega, f i j l m omega ∂mu := by
  classical
  calc
    (∫ omega, ∑ i : I, ∑ j : J, ∑ l : L, ∑ m : M,
        f i j l m omega ∂mu) =
        ∑ i : I, ∫ omega, ∑ j : J, ∑ l : L, ∑ m : M,
          f i j l m omega ∂mu := by
      exact integral_finsetSum Finset.univ fun i hi ↦
        integrable_finsetSum Finset.univ fun j hj ↦
          integrable_finsetSum Finset.univ fun l hl ↦
            integrable_finsetSum Finset.univ fun m hm ↦ hf i j l m
    _ = ∑ i : I, ∑ j : J,
          ∫ omega, ∑ l : L, ∑ m : M, f i j l m omega ∂mu := by
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finsetSum Finset.univ fun j hj ↦
        integrable_finsetSum Finset.univ fun l hl ↦
          integrable_finsetSum Finset.univ fun m hm ↦ hf i j l m
    _ = ∑ i : I, ∑ j : J, ∑ l : L,
          ∫ omega, ∑ m : M, f i j l m omega ∂mu := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact integral_finsetSum Finset.univ fun l hl ↦
        integrable_finsetSum Finset.univ fun m hm ↦ hf i j l m
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro l hl
      exact integral_finsetSum Finset.univ fun m hm ↦ hf i j l m

/-- Conditional expectation of `tr((C W)^2)` for a fixed symmetric matrix
`C` and a variance-one real Wishart matrix `W`. -/
theorem integral_trace_const_mul_realWishartGram_sq_standardGaussian
    {rows p : ℕ} (C : Matrix (Fin p) (Fin p) ℝ) (hC : C.IsSymm) :
    (∫ R : Matrix (Fin rows) (Fin p) ℝ,
        Matrix.trace ((C * realWishartGram R) ^ 2)
        ∂standardRealGaussianMatrixMeasure rows p) =
      (rows : ℝ) * ((rows : ℝ) + 1) * Matrix.trace (C ^ 2) +
        (rows : ℝ) * Matrix.trace C ^ 2 := by
  classical
  let mu := standardRealGaussianMatrixMeasure rows p
  let W : Matrix (Fin rows) (Fin p) ℝ → Matrix (Fin p) (Fin p) ℝ :=
    fun R ↦ realWishartGram R
  calc
    (∫ R : Matrix (Fin rows) (Fin p) ℝ,
        Matrix.trace ((C * realWishartGram R) ^ 2) ∂mu) =
        ∫ R, ∑ i : Fin p, ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
          C i j * C k l * (W R j k * W R l i) ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with R
      exact trace_const_mul_matrix_sq_expansion C (realWishartGram R)
    _ = ∑ i : Fin p, ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
          ∫ R, C i j * C k l * (W R j k * W R l i) ∂mu := by
      exact integral_fintype_sum_four mu
        (fun i j k l R ↦ C i j * C k l * (W R j k * W R l i))
        (fun i j k l ↦ by
          exact (integrable_realWishartGram_entry_mul_entry_standardGaussian
            (rows := rows) j k l i).const_mul (C i j * C k l))
    _ = ∑ i : Fin p, ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
          C i j * C k l *
            ((rows : ℝ) ^ 2 *
                realKroneckerDelta j k * realKroneckerDelta l i +
              (rows : ℝ) *
                (realKroneckerDelta j l * realKroneckerDelta k i +
                  realKroneckerDelta j i * realKroneckerDelta k l)) := by
      simp_rw [integral_const_mul]
      simp_rw [show ∀ j k l i : Fin p,
          (∫ R : Matrix (Fin rows) (Fin p) ℝ, W R j k * W R l i ∂mu) =
            (rows : ℝ) ^ 2 *
                (realKroneckerDelta j k * realKroneckerDelta l i) +
              (rows : ℝ) *
                (realKroneckerDelta j l * realKroneckerDelta k i +
                  realKroneckerDelta j i * realKroneckerDelta k l) by
        intro j k l i
        exact integral_realWishartGram_entry_mul_entry_standardGaussian_eq
          j k l i]
      simp only [mul_assoc]
    _ = _ := wishart_traceTwo_tensor_contraction (rows : ℝ) C hC

/-- Conditional expectation of `tr(C W)^2` for a fixed symmetric matrix
`C` and a variance-one real Wishart matrix `W`. -/
theorem integral_trace_const_mul_realWishartGram_square_standardGaussian
    {rows p : ℕ} (C : Matrix (Fin p) (Fin p) ℝ) (hC : C.IsSymm) :
    (∫ R : Matrix (Fin rows) (Fin p) ℝ,
        Matrix.trace (C * realWishartGram R) ^ 2
        ∂standardRealGaussianMatrixMeasure rows p) =
      (rows : ℝ) ^ 2 * Matrix.trace C ^ 2 +
        2 * (rows : ℝ) * Matrix.trace (C ^ 2) := by
  classical
  let mu := standardRealGaussianMatrixMeasure rows p
  let W : Matrix (Fin rows) (Fin p) ℝ → Matrix (Fin p) (Fin p) ℝ :=
    fun R ↦ realWishartGram R
  calc
    (∫ R : Matrix (Fin rows) (Fin p) ℝ,
        Matrix.trace (C * realWishartGram R) ^ 2 ∂mu) =
        ∫ R, ∑ i : Fin p, ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
          C i j * C k l * (W R j i * W R l k) ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with R
      exact trace_const_mul_matrix_square_expansion C (realWishartGram R)
    _ = ∑ i : Fin p, ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
          ∫ R, C i j * C k l * (W R j i * W R l k) ∂mu := by
      exact integral_fintype_sum_four mu
        (fun i j k l R ↦ C i j * C k l * (W R j i * W R l k))
        (fun i j k l ↦ by
          exact (integrable_realWishartGram_entry_mul_entry_standardGaussian
            (rows := rows) j i l k).const_mul (C i j * C k l))
    _ = ∑ i : Fin p, ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
          C i j * C k l *
            ((rows : ℝ) ^ 2 *
                realKroneckerDelta j i * realKroneckerDelta l k +
              (rows : ℝ) *
                (realKroneckerDelta j l * realKroneckerDelta i k +
                  realKroneckerDelta j k * realKroneckerDelta i l)) := by
      simp_rw [integral_const_mul]
      simp_rw [show ∀ j i l k : Fin p,
          (∫ R : Matrix (Fin rows) (Fin p) ℝ, W R j i * W R l k ∂mu) =
            (rows : ℝ) ^ 2 *
                (realKroneckerDelta j i * realKroneckerDelta l k) +
              (rows : ℝ) *
                (realKroneckerDelta j l * realKroneckerDelta i k +
                  realKroneckerDelta j k * realKroneckerDelta i l) by
        intro j i l k
        exact integral_realWishartGram_entry_mul_entry_standardGaussian_eq
          j i l k]
      simp only [mul_assoc]
    _ = _ := wishart_traceOneSquare_tensor_contraction (rows : ℝ) C hC

/-- The scaled inverse-Wishart denominator is symmetric pointwise. -/
theorem scaledInverseWishartMatrix_isSymm
    (N K : ℕ) (H : Matrix (Fin (K - N)) (Fin N) ℝ) :
    (scaledInverseWishartMatrix N K H).IsSymm := by
  exact (realWishartGram_inv_isSymm H).smul (concreteCOEExponent N K)

/-- The trace of the squared scaled inverse-Wishart denominator is
integrable at the common H8/H10 threshold. -/
theorem integrable_scaledInverseWishartMatrix_trace_sq
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    Integrable
      (fun H : Matrix (Fin (K - N)) (Fin N) ℝ ↦
        Matrix.trace ((scaledInverseWishartMatrix N K H) ^ 2))
      (standardRealGaussianMatrixMeasure (K - N) N) := by
  let muB := standardRealGaussianMatrixMeasure (K - N) N
  letI : IsProbabilityMeasure muB :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  have hbase := inverseWishartTraceSquare_memLp_two_standardGaussian
    (k := K - N) (p := N) (by omega)
  have hbaseInt : Integrable
      (fun H : Matrix (Fin (K - N)) (Fin N) ℝ ↦
        Matrix.trace ((realWishartGram H)⁻¹ ^ 2)) muB :=
    memLp_one_iff_integrable.mp (hbase.mono_exponent (by norm_num))
  have hscaled := hbaseInt.const_mul (concreteCOEExponent N K ^ 2)
  simpa [muB, scaledInverseWishartMatrix, pow_two, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_assoc] using hscaled

/-- The square of the trace of the scaled inverse-Wishart denominator is
integrable at the same threshold. -/
theorem integrable_scaledInverseWishartMatrix_trace_square
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    Integrable
      (fun H : Matrix (Fin (K - N)) (Fin N) ℝ ↦
        Matrix.trace (scaledInverseWishartMatrix N K H) ^ 2)
      (standardRealGaussianMatrixMeasure (K - N) N) := by
  let muB := standardRealGaussianMatrixMeasure (K - N) N
  letI : IsProbabilityMeasure muB :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  have hbase := inverseWishartTrace_memLp_four_standardGaussian
    (k := K - N) (p := N) (by omega)
  have hbaseTwo := hbase.mono_exponent (show (2 : ENNReal) ≤ 4 by norm_num)
  have hbaseInt : Integrable
      (fun H : Matrix (Fin (K - N)) (Fin N) ℝ ↦
        Matrix.trace (realWishartGram H)⁻¹ ^ 2) muB :=
    hbaseTwo.integrable_sq
  have hscaled := hbaseInt.const_mul (concreteCOEExponent N K ^ 2)
  simpa [muB, scaledInverseWishartMatrix, Matrix.trace_smul, smul_eq_mul,
    pow_two, mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- The two exact finite-Gaussian numerator Wick identities.  This removes
`BetaPrimeSecondOrderFiniteWickFormula` from the conditional boundary. -/
theorem betaPrimeSecondOrderFiniteWickFormula_internal
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    BetaPrimeSecondOrderFiniteWickFormula N K := by
  let muA := standardRealGaussianMatrixMeasure (N + 1) N
  let muB := standardRealGaussianMatrixMeasure (K - N) N
  letI : IsProbabilityMeasure muA :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  letI : IsProbabilityMeasure muB :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  have hC (H : Matrix (Fin (K - N)) (Fin N) ℝ) :
      (scaledInverseWishartMatrix N K H).IsSymm :=
    scaledInverseWishartMatrix_isSymm N K H
  have htwoInner (H : Matrix (Fin (K - N)) (Fin N) ℝ) :
      (∫ G : Matrix (Fin (N + 1)) (Fin N) ℝ,
          betaPrimeTraceTwoSource N K (G, H) ∂muA) =
        ((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ) *
            Matrix.trace ((scaledInverseWishartMatrix N K H) ^ 2) +
          ((N + 1 : ℕ) : ℝ) *
            Matrix.trace (scaledInverseWishartMatrix N K H) ^ 2 := by
    calc
      (∫ G : Matrix (Fin (N + 1)) (Fin N) ℝ,
          betaPrimeTraceTwoSource N K (G, H) ∂muA) =
          ∫ G, Matrix.trace
            ((scaledInverseWishartMatrix N K H * realWishartGram G) ^ 2)
            ∂muA := by
        apply integral_congr_ae
        filter_upwards [] with G
        rw [betaPrimeTraceTwoSource_eq_scaledInverseWishart_trace]
        simp only [scaledInverseWishartDenominator,
          scaledInverseWishartMatrix, pow_two, mul_assoc]
      _ = _ := by
        have h := integral_trace_const_mul_realWishartGram_sq_standardGaussian
          (rows := N + 1) (scaledInverseWishartMatrix N K H) (hC H)
        simpa only [muA, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
          add_assoc, one_add_one_eq_two] using h
  have honeInner (H : Matrix (Fin (K - N)) (Fin N) ℝ) :
      (∫ G : Matrix (Fin (N + 1)) (Fin N) ℝ,
          betaPrimeTraceOneSource N K (G, H) ^ 2 ∂muA) =
        ((N + 1 : ℕ) : ℝ) ^ 2 *
            Matrix.trace (scaledInverseWishartMatrix N K H) ^ 2 +
          2 * ((N + 1 : ℕ) : ℝ) *
            Matrix.trace ((scaledInverseWishartMatrix N K H) ^ 2) := by
    calc
      (∫ G : Matrix (Fin (N + 1)) (Fin N) ℝ,
          betaPrimeTraceOneSource N K (G, H) ^ 2 ∂muA) =
          ∫ G, Matrix.trace
            (scaledInverseWishartMatrix N K H * realWishartGram G) ^ 2
            ∂muA := by
        apply integral_congr_ae
        filter_upwards [] with G
        rw [betaPrimeTraceOneSource_eq_scaledInverseWishart_trace]
        simp only [scaledInverseWishartDenominator,
          scaledInverseWishartMatrix]
      _ = _ := by
        simpa only [muA] using
          integral_trace_const_mul_realWishartGram_square_standardGaussian
            (rows := N + 1) (scaledInverseWishartMatrix N K H) (hC H)
  have htraceTwoInt := integrable_scaledInverseWishartMatrix_trace_sq hgap
  have htraceOneSqInt :=
    integrable_scaledInverseWishartMatrix_trace_square hgap
  refine ⟨?_, ?_⟩
  · have hsource := integrable_betaPrimeTraceTwoSource_internal hgap
    change Integrable (betaPrimeTraceTwoSource N K) (muA.prod muB) at hsource
    calc
      (∫ source, betaPrimeTraceTwoSource N K source
          ∂realBetaPrimeGaussianSourceLaw N K) =
          ∫ H, ∫ G, betaPrimeTraceTwoSource N K (G, H) ∂muA ∂muB := by
        change (∫ source, betaPrimeTraceTwoSource N K source ∂muA.prod muB) = _
        exact integral_prod_symm _ hsource
      _ = ∫ H,
          (((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ) *
              Matrix.trace ((scaledInverseWishartMatrix N K H) ^ 2) +
            ((N + 1 : ℕ) : ℝ) *
              Matrix.trace (scaledInverseWishartMatrix N K H) ^ 2) ∂muB := by
        apply integral_congr_ae
        filter_upwards [] with H
        exact htwoInner H
      _ = _ := by
        rw [integral_add
          (htraceTwoInt.const_mul
            (((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ)))
          (htraceOneSqInt.const_mul ((N + 1 : ℕ) : ℝ)),
          integral_const_mul, integral_const_mul]
  · have hsource := integrable_betaPrimeTraceOneSource_sq_internal hgap
    change Integrable (fun source ↦ betaPrimeTraceOneSource N K source ^ 2)
      (muA.prod muB) at hsource
    calc
      (∫ source, betaPrimeTraceOneSource N K source ^ 2
          ∂realBetaPrimeGaussianSourceLaw N K) =
          ∫ H, ∫ G, betaPrimeTraceOneSource N K (G, H) ^ 2 ∂muA ∂muB := by
        change (∫ source, betaPrimeTraceOneSource N K source ^ 2
          ∂muA.prod muB) = _
        exact integral_prod_symm _ hsource
      _ = ∫ H,
          (((N + 1 : ℕ) : ℝ) ^ 2 *
              Matrix.trace (scaledInverseWishartMatrix N K H) ^ 2 +
            2 * ((N + 1 : ℕ) : ℝ) *
              Matrix.trace ((scaledInverseWishartMatrix N K H) ^ 2)) ∂muB := by
        apply integral_congr_ae
        filter_upwards [] with H
        exact honeInner H
      _ = _ := by
        rw [integral_add
          (htraceOneSqInt.const_mul (((N + 1 : ℕ) : ℝ) ^ 2))
          (htraceTwoInt.const_mul (2 * ((N + 1 : ℕ) : ℝ))),
          integral_const_mul, integral_const_mul]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

import A4.InverseSteinProductLp
import A4.InverseSteinRecursionTuples
import A4.InverseEntryRecurrenceRealShape

open MeasureTheory Matrix
open scoped BigOperators Matrix ENNReal

noncomputable section
namespace A4Research.InverseStein

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def inverseEntryDirection {d : ℕ} (a b : Fin d) : Matrix (Fin d) (Fin d) ℝ :=
  (1 / 2 : ℝ) • (Matrix.single a b 1 + Matrix.single b a 1)

theorem inverseEntryDirection_isSymm {d : ℕ} (a b : Fin d) :
    (inverseEntryDirection a b).IsSymm := by
  apply Matrix.IsSymm.smul
  unfold Matrix.IsSymm
  rw [Matrix.transpose_add, Matrix.transpose_single, Matrix.transpose_single]
  exact add_comm _ _

theorem trace_inverseEntryDirection {d : ℕ} (a b : Fin d) :
    Matrix.trace (inverseEntryDirection a b) = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst b
    norm_num [inverseEntryDirection]
  · simp [inverseEntryDirection, h, Ne.symm h]

theorem trace_mul_inverseEntryDirection {d : ℕ}
    (X : Matrix (Fin d) (Fin d) ℝ) (hX : X.IsSymm) (a b : Fin d) :
    Matrix.trace (X * inverseEntryDirection a b) = X a b := by
  rw [Matrix.trace_mul_comm]
  simp only [inverseEntryDirection, Matrix.smul_mul, Matrix.add_mul,
    Matrix.trace_smul, Matrix.trace_add, Matrix.trace_single_mul,
    smul_eq_mul, one_mul, hX.apply a b]
  ring

theorem single_sandwich_entry {d : ℕ}
    (X : Matrix (Fin d) (Fin d) ℝ) (a b i j : Fin d) :
    (X * (Matrix.single a b (1 : ℝ) : Matrix (Fin d) (Fin d) ℝ) * X) i j =
      X i a * X b j := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem sandwich_inverseEntryDirection {d : ℕ}
    (X : Matrix (Fin d) (Fin d) ℝ) (a b i j : Fin d) :
    (X * inverseEntryDirection a b * X) i j =
      (1 / 2 : ℝ) * (X i a * X b j + X i b * X a j) := by
  simp only [inverseEntryDirection, Matrix.mul_smul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.add_mul, Matrix.smul_apply, Matrix.add_apply,
    smul_eq_mul, single_sandwich_entry]

/-- Actual Gaussian integration by parts for every finite product of inverse
Gram entries. Every regularity and integrability hypothesis is discharged. -/
theorem inverseEntryProduct_steinHaff_halfGaussianMatrix {k d q n : ℕ}
    (W : MatsumotoPaper.W_d d ((k : ℝ) / 2) (MatsumotoPaper.identityScale d))
    (hmargin : 32 * ((q : ℝ) + 2) - 1 < ((k : ℝ) - d - 1) / 2)
    (hdim : n + 1 = k * d) (indices : Fin q → Fin d × Fin d)
    (D : Matrix (Fin d) (Fin d) ℝ) (hD : D.IsSymm) :
    (∫ R, inverseEntryProduct indices R *
      (((k : ℝ) - d - 1) / 2 * Matrix.trace ((realWishartGram R)⁻¹ * D))
      ∂halfGaussianMatrix k d) =
    ∫ R, inverseEntryProduct indices R * Matrix.trace D +
      ∑ r : Fin q, (((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹)
        (indices r).1 (indices r).2) *
        ∏ s ∈ Finset.univ.erase r, (realWishartGram R)⁻¹ (indices s).1 (indices s).2
      ∂halfGaussianMatrix k d := by
  let qfun : Matrix (Fin k) (Fin d) ℝ → ℝ := fun R ↦
    -∑ r : Fin q, (((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹)
      (indices r).1 (indices r).2) *
      ∏ s ∈ Finset.univ.erase r, (realWishartGram R)⁻¹ (indices s).1 (indices s).2
  have hQ : Integrable qfun (halfGaussianMatrix k d) :=
    (memLp_inverseEntryProductSandwichSum_two W hmargin indices D).integrable
      (by norm_num)
  obtain ⟨hv, hd, hr⟩ := inverseEntryProduct_flattenedSteinFamilies
    W hmargin hdim indices D
  have h := steinHaff_halfGaussianMatrix_of_nonsingular_fderiv_and_flattenedSteinFamilies
    hdim (sample_margin_column_lt hmargin)
    (inverseEntryProduct indices) (inverseEntryProductDerivative indices) D qfun
    (hasFDerivAt_inverseEntryProduct indices)
    (fun R hR ↦ inverseEntryProductDerivative_steinVectorFieldValue indices R D hD hR)
    hQ hv hd hr
  simpa only [inverseGramScoreCoefficient, Fintype.card_fin, qfun, sub_neg_eq_add]
    using h.2.2

theorem integrable_inverseEntryProduct_bounded_degree {k d q t : ℕ}
    (W : MatsumotoPaper.W_d d ((k : ℝ) / 2) (MatsumotoPaper.identityScale d))
    (hmargin : 32 * ((q : ℝ) + 2) - 1 < ((k : ℝ) - d - 1) / 2)
    (indices : Fin t → Fin d × Fin d) (ht : t ≤ q + 1) :
    Integrable (inverseEntryProduct indices : Matrix (Fin k) (Fin d) ℝ → ℝ)
      (halfGaussianMatrix k d) := by
  have htr : (t : ℝ) ≤ (q : ℝ) + 1 := by exact_mod_cast ht
  have hq := Nat.cast_nonneg (α := ℝ) q
  have h := memLp_inverseEntryProduct_halfGaussianMatrix W (p := 2)
    (by norm_num) (by linarith) indices
  exact h.integrable (by norm_num)

theorem inverseEntryProduct_direction_score {k d q : ℕ}
    (indices : Fin q → Fin d × Fin d) (R : Matrix (Fin k) (Fin d) ℝ)
    (a b : Fin d) :
    inverseEntryProduct indices R *
        Matrix.trace ((realWishartGram R)⁻¹ * inverseEntryDirection a b) =
      inverseEntryProduct (prependInverseEntry indices a b) R := by
  rw [trace_mul_inverseEntryDirection _ (realWishartGram_inv_isSymm R)]
  simp only [inverseEntryProduct, product_prependInverseEntry]
  ring

theorem inverseEntryProduct_direction_rhs {k d q : ℕ}
    (indices : Fin q → Fin d × Fin d) (R : Matrix (Fin k) (Fin d) ℝ)
    (a b : Fin d) :
    inverseEntryProduct indices R * Matrix.trace (inverseEntryDirection a b) +
        ∑ r : Fin q,
          (((realWishartGram R)⁻¹ * inverseEntryDirection a b * (realWishartGram R)⁻¹)
            (indices r).1 (indices r).2) *
          ∏ s ∈ Finset.univ.erase r, (realWishartGram R)⁻¹ (indices s).1 (indices s).2 =
      (if a = b then 1 else 0 : ℝ) * inverseEntryProduct indices R +
        (1 / 2 : ℝ) * ∑ r : Fin q,
          (inverseEntryProduct (inverseSwapLeft indices a b r) R +
            inverseEntryProduct (inverseSwapRight indices a b r) R) := by
  simp only [trace_inverseEntryDirection, sandwich_inverseEntryDirection,
    inverseEntryProduct, product_inverseSwapLeft, product_inverseSwapRight]
  rw [Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro r _
    ring

/-- The literal inverse-entry recurrence on the actual half-variance Gaussian
source. The swap terms are complete degree `q+1` products. -/
theorem inverse_entry_recurrence_halfGaussianMatrix {k d q n : ℕ}
    (W : MatsumotoPaper.W_d d ((k : ℝ) / 2) (MatsumotoPaper.identityScale d))
    (hmargin : 32 * ((q : ℝ) + 2) - 1 < ((k : ℝ) - d - 1) / 2)
    (hdim : n + 1 = k * d) (indices : Fin q → Fin d × Fin d)
    (a b : Fin d) :
    (((k : ℝ) - d - 1) / 2) *
        (∫ R, inverseEntryProduct (prependInverseEntry indices a b) R
          ∂halfGaussianMatrix k d) -
      (1 / 2 : ℝ) * ∑ r : Fin q,
        ((∫ R, inverseEntryProduct (inverseSwapLeft indices a b r) R
            ∂halfGaussianMatrix k d) +
          (∫ R, inverseEntryProduct (inverseSwapRight indices a b r) R
            ∂halfGaussianMatrix k d)) -
      (if a = b then 1 else 0 : ℝ) *
        (∫ R, inverseEntryProduct indices R ∂halfGaussianMatrix k d) = 0 := by
  have h := inverseEntryProduct_steinHaff_halfGaussianMatrix W hmargin hdim indices
    (inverseEntryDirection a b) (inverseEntryDirection_isSymm a b)
  have hprod := integrable_inverseEntryProduct_bounded_degree W hmargin indices
    (Nat.le_succ q)
  have hleft (r : Fin q) := integrable_inverseEntryProduct_bounded_degree W hmargin
    (inverseSwapLeft indices a b r) (Nat.le_refl (q + 1))
  have hright (r : Fin q) := integrable_inverseEntryProduct_bounded_degree W hmargin
    (inverseSwapRight indices a b r) (Nat.le_refl (q + 1))
  have hsum : Integrable (fun R : Matrix (Fin k) (Fin d) ℝ ↦ ∑ r : Fin q,
      (inverseEntryProduct (inverseSwapLeft indices a b r) R +
        inverseEntryProduct (inverseSwapRight indices a b r) R))
      (halfGaussianMatrix k d) :=
    integrable_finsetSum Finset.univ (fun r _ ↦ (hleft r).add (hright r))
  have hL : (∫ R, inverseEntryProduct indices R *
      (((k : ℝ) - d - 1) / 2 *
        Matrix.trace ((realWishartGram R)⁻¹ * inverseEntryDirection a b))
      ∂halfGaussianMatrix k d) =
      (((k : ℝ) - d - 1) / 2) *
        (∫ R, inverseEntryProduct (prependInverseEntry indices a b) R
          ∂halfGaussianMatrix k d) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with R
    rw [← inverseEntryProduct_direction_score indices R a b]
    ring
  have hR : (∫ R, inverseEntryProduct indices R *
      Matrix.trace (inverseEntryDirection a b) +
      ∑ r : Fin q, (((realWishartGram R)⁻¹ * inverseEntryDirection a b *
          (realWishartGram R)⁻¹) (indices r).1 (indices r).2) *
        ∏ s ∈ Finset.univ.erase r, (realWishartGram R)⁻¹ (indices s).1 (indices s).2
      ∂halfGaussianMatrix k d) =
      (if a = b then 1 else 0 : ℝ) *
        (∫ R, inverseEntryProduct indices R ∂halfGaussianMatrix k d) +
        (1 / 2 : ℝ) * ∑ r : Fin q,
          ((∫ R, inverseEntryProduct (inverseSwapLeft indices a b r) R
              ∂halfGaussianMatrix k d) +
            (∫ R, inverseEntryProduct (inverseSwapRight indices a b r) R
              ∂halfGaussianMatrix k d)) := by
    calc
      _ = ∫ R, (if a = b then 1 else 0 : ℝ) * inverseEntryProduct indices R +
          (1 / 2 : ℝ) * ∑ r : Fin q,
            (inverseEntryProduct (inverseSwapLeft indices a b r) R +
              inverseEntryProduct (inverseSwapRight indices a b r) R)
          ∂halfGaussianMatrix k d := by
        apply integral_congr_ae
        filter_upwards [] with R
        exact inverseEntryProduct_direction_rhs indices R a b
      _ = _ := by
        rw [integral_add (hprod.const_mul _) (hsum.const_mul _),
          integral_const_mul, integral_const_mul,
          integral_finsetSum Finset.univ
            (f := fun r R ↦ inverseEntryProduct (inverseSwapLeft indices a b r) R +
              inverseEntryProduct (inverseSwapRight indices a b r) R)
            (fun r _ ↦ (hleft r).add (hright r))]
        congr 2
        apply Finset.sum_congr rfl
        intro r _
        exact integral_add (hleft r) (hright r)
  rw [hL, hR] at h
  linarith

theorem integral_inverseEntryProduct_eq_Wishart {k d q : ℕ}
    (W : MatsumotoPaper.W_d d ((k : ℝ) / 2) (MatsumotoPaper.identityScale d))
    (indices : Fin q → Fin d × Fin d) :
    (∫ R, inverseEntryProduct indices R ∂halfGaussianMatrix k d) =
      MatsumotoPaper.inverseEntryMoment W indices := by
  have hmeas := measurable_inverseMatrixEntryProduct indices
  calc
    _ = ∫ X, inverseMatrixEntryProduct indices X ∂W.matrixLaw := by
      rw [wishart_matrixLaw_eq_halfGaussianGramLaw W]
      exact (integral_map (measurable_realWishartGram k d).aemeasurable
        hmeas.aestronglyMeasurable).symm
    _ = _ := by
      rw [MatsumotoPaper.W_d.matrixLaw,
        integral_map measurable_subtype_coe.aemeasurable hmeas.aestronglyMeasurable]
      rfl

/-- The all-degree Gaussian Stein--Haff entry recurrence at every sufficiently
large natural sample shape. No Stein identity or sample moment is assumed. -/
theorem inverse_entry_recurrence_half_integer {k d q : ℕ}
    (W : MatsumotoPaper.W_d d ((k : ℝ) / 2) (MatsumotoPaper.identityScale d))
    (hk : d + 64 * (q + 2) + 2 ≤ k)
    (indices : Fin q → Fin d × Fin d) (a b : Fin d) :
    (((k : ℝ) / 2) - ((d : ℝ) + 1) / 2) *
        MatsumotoPaper.inverseEntryMoment W (prependInverseEntry indices a b) -
      (1 / 2 : ℝ) * ∑ r : Fin q,
        (MatsumotoPaper.inverseEntryMoment W (inverseSwapLeft indices a b r) +
          MatsumotoPaper.inverseEntryMoment W (inverseSwapRight indices a b r)) -
      (MatsumotoPaper.identityScale d).1⁻¹ a b *
        MatsumotoPaper.inverseEntryMoment W indices = 0 := by
  have hkr : (d : ℝ) + 64 * ((q : ℝ) + 2) + 2 ≤ k := by exact_mod_cast hk
  have hmargin : 32 * ((q : ℝ) + 2) - 1 < ((k : ℝ) - d - 1) / 2 := by
    linarith
  have hdp : 0 < d := Nat.zero_lt_of_lt a.isLt
  have hkp : 0 < k := lt_trans hdp (sample_margin_column_lt hmargin)
  have hdim : (k * d - 1) + 1 = k * d := by
    have hpos := Nat.mul_pos hkp hdp
    omega
  have h := inverse_entry_recurrence_halfGaussianMatrix W hmargin hdim indices a b
  simp_rw [integral_inverseEntryProduct_eq_Wishart W] at h
  have hid : (MatsumotoPaper.identityScale d).1⁻¹ a b =
      (if a = b then 1 else 0 : ℝ) := by
    simp [MatsumotoPaper.identityScale, Matrix.one_apply]
  rw [hid]
  convert h using 2 <;> ring

end A4Research.InverseStein

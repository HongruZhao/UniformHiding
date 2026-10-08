import A4.InverseSteinFieldLp

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal NNReal

noncomputable section
namespace A4Research.InverseStein

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

local instance : ENNReal.HolderTriple 16 16 8 := by
  have hr : Real.HolderTriple 16 16 8 := ⟨by norm_num, by norm_num, by norm_num⟩
  simpa only [ENNReal.ofReal_ofNat] using hr.ennrealOfReal
local instance : ENNReal.HolderTriple 8 8 4 := by
  have hr : Real.HolderTriple 8 8 4 := ⟨by norm_num, by norm_num, by norm_num⟩
  simpa only [ENNReal.ofReal_ofNat] using hr.ennrealOfReal
local instance : ENNReal.HolderTriple 4 4 2 := by
  have hr : Real.HolderTriple 4 4 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  simpa only [ENNReal.ofReal_ofNat] using hr.ennrealOfReal
local instance : ENNReal.HolderTriple 2 2 1 := by
  have hr : Real.HolderTriple 2 2 1 := ⟨by norm_num, by norm_num, by norm_num⟩
  simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using hr.ennrealOfReal

theorem sample_margin_entry32 {k d q : ℕ}
    (hmargin : 32 * ((q : ℝ) + 2) - 1 < ((k : ℝ) - d - 1) / 2) :
    31 < ((k : ℝ) - d - 1) / 2 := by
  have hq := Nat.cast_nonneg (α := ℝ) q
  linarith

theorem sample_margin_column_lt {k d q : ℕ}
    (hmargin : 32 * ((q : ℝ) + 2) - 1 < ((k : ℝ) - d - 1) / 2) : d < k := by
  have hg := sample_margin_entry32 hmargin
  exact_mod_cast (show (d : ℝ) < k by linarith)

theorem memLp_inverseEntryProduct_four {k d q : ℕ}
    (W : MatsumotoPaper.W_d d ((k : ℝ) / 2) (MatsumotoPaper.identityScale d))
    (hmargin : 32 * ((q : ℝ) + 2) - 1 < ((k : ℝ) - d - 1) / 2)
    (indices : Fin q → Fin d × Fin d) :
    MemLp (inverseEntryProduct indices : Matrix (Fin k) (Fin d) ℝ → ℝ)
      4 (halfGaussianMatrix k d) := by
  have hq := Nat.cast_nonneg (α := ℝ) q
  have h := memLp_inverseEntryProduct_halfGaussianMatrix W (p := 4)
    (by norm_num) (by linarith) indices
  simpa only [ENNReal.ofReal_ofNat] using h

theorem memLp_erased_inverseEntryProduct_four {k d q : ℕ}
    (W : MatsumotoPaper.W_d d ((k : ℝ) / 2) (MatsumotoPaper.identityScale d))
    (hmargin : 32 * ((q : ℝ) + 2) - 1 < ((k : ℝ) - d - 1) / 2)
    (indices : Fin q → Fin d × Fin d) (r : Fin q) :
    MemLp (fun R : Matrix (Fin k) (Fin d) ℝ ↦
      ∏ s ∈ Finset.univ.erase r, (realWishartGram R)⁻¹ (indices s).1 (indices s).2)
      4 (halfGaussianMatrix k d) := by
  have hcardN : (Finset.univ.erase r : Finset (Fin q)).card ≤ q := by
    simpa using Finset.card_le_card (Finset.erase_subset r Finset.univ)
  have hcard : ((Finset.univ.erase r : Finset (Fin q)).card : ℝ) ≤ q := by
    exact_mod_cast hcardN
  have hq := Nat.cast_nonneg (α := ℝ) q
  have h := memLp_finset_inverseProduct_exponent W (Finset.univ.erase r) indices
    (p := 4) (by norm_num) (by linarith)
  simpa only [ENNReal.ofReal_ofNat] using h

theorem memLp_inverseSandwich_entry {k d : ℕ}
    (W : MatsumotoPaper.W_d d ((k : ℝ) / 2) (MatsumotoPaper.identityScale d))
    (hgap : 31 < ((k : ℝ) - d - 1) / 2)
    (D : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    MemLp (fun R : Matrix (Fin k) (Fin d) ℝ ↦
      ((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) i j)
      4 (halfGaussianMatrix k d) := by
  have hG8 (i j : Fin d) := (memLp_inverseGram_entry_32 W hgap i j).mono_exponent
    (by norm_num : (8 : ℝ≥0∞) ≤ 32)
  have hGD8 := memLp_matrix_mul_const_entry _ D hG8
  exact memLp_matrix_mul_entry (r := 4) _ _ hGD8 hG8 i j

theorem memLp_inverseGramDirectionalSandwich_entry {k d : ℕ}
    (W : MatsumotoPaper.W_d d ((k : ℝ) / 2) (MatsumotoPaper.identityScale d))
    (hgap : 31 < ((k : ℝ) - d - 1) / 2)
    (E : Matrix (Fin k) (Fin d) ℝ) (i j : Fin d) :
    MemLp (fun R : Matrix (Fin k) (Fin d) ℝ ↦
      ((realWishartGram R)⁻¹ * (E.transpose * R + R.transpose * E) *
        (realWishartGram R)⁻¹) i j) 4 (halfGaussianMatrix k d) := by
  have hR16 (a : Fin k) (j : Fin d) :=
    memLp_matrixCoordinate_halfGaussianMatrix a j 16 (by norm_num)
  have hG32 := memLp_inverseGram_entry_32 W hgap
  have hG16 (i j : Fin d) := (hG32 i j).mono_exponent (by norm_num : (16 : ℝ≥0∞) ≤ 32)
  have hG8 (i j : Fin d) := (hG32 i j).mono_exponent (by norm_num : (8 : ℝ≥0∞) ≤ 32)
  have hEtR16 := memLp_const_matrix_mul_entry E.transpose _ hR16
  have hRtE16 := memLp_matrix_mul_const_entry
    (fun R : Matrix (Fin k) (Fin d) ℝ ↦ R.transpose) E (fun i j ↦ hR16 j i)
  have hvariation16 (i j : Fin d) := (hEtR16 i j).add (hRtE16 i j)
  have hfirst8 := memLp_matrix_mul_entry (r := 8) _ _ hG16 hvariation16
  exact memLp_matrix_mul_entry (r := 4) _ _ hfirst8 hG8 i j

theorem memLp_inverseEntryProductDerivative_two {k d q : ℕ}
    (W : MatsumotoPaper.W_d d ((k : ℝ) / 2) (MatsumotoPaper.identityScale d))
    (hmargin : 32 * ((q : ℝ) + 2) - 1 < ((k : ℝ) - d - 1) / 2)
    (indices : Fin q → Fin d × Fin d) (E : Matrix (Fin k) (Fin d) ℝ) :
    MemLp (fun R : Matrix (Fin k) (Fin d) ℝ ↦ inverseEntryProductDerivative indices R E)
      2 (halfGaussianMatrix k d) := by
  have hterm (r : Fin q) :=
    (memLp_erased_inverseEntryProduct_four W hmargin indices r).mul' (r := 2)
      (memLp_inverseGramDirectionalSandwich_entry W (sample_margin_entry32 hmargin)
        E (indices r).1 (indices r).2)
  have hsum := (memLp_finsetSum Finset.univ (fun r _ ↦ hterm r)).neg
  refine MemLp.ae_eq ?_ hsum
  filter_upwards [ae_isUnit_det_realWishartGram_halfGaussianMatrix
    k d (Nat.le_of_lt (sample_margin_column_lt hmargin))] with R hR
  exact (inverseEntryProductDerivative_apply indices R E hR).symm

theorem memLp_inverseEntryProductSandwichSum_two {k d q : ℕ}
    (W : MatsumotoPaper.W_d d ((k : ℝ) / 2) (MatsumotoPaper.identityScale d))
    (hmargin : 32 * ((q : ℝ) + 2) - 1 < ((k : ℝ) - d - 1) / 2)
    (indices : Fin q → Fin d × Fin d) (D : Matrix (Fin d) (Fin d) ℝ) :
    MemLp (fun R : Matrix (Fin k) (Fin d) ℝ ↦
      -∑ r, (((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹)
        (indices r).1 (indices r).2) *
        ∏ s ∈ Finset.univ.erase r, (realWishartGram R)⁻¹ (indices s).1 (indices s).2)
      2 (halfGaussianMatrix k d) := by
  exact (memLp_finsetSum _ (fun r _ ↦
    (memLp_erased_inverseEntryProduct_four W hmargin indices r).mul'
      (memLp_inverseSandwich_entry W (sample_margin_entry32 hmargin)
        D (indices r).1 (indices r).2))).neg

/-- All three literal component families required by Gaussian integration by
parts are integrable, for every inverse-product degree. -/
theorem inverseEntryProduct_flattenedSteinFamilies {k d q n : ℕ}
    (W : MatsumotoPaper.W_d d ((k : ℝ) / 2) (MatsumotoPaper.identityScale d))
    (hmargin : 32 * ((q : ℝ) + 2) - 1 < ((k : ℝ) - d - 1) / 2)
    (hdim : n + 1 = k * d) (indices : Fin q → Fin d × Fin d)
    (D : Matrix (Fin d) (Fin d) ℝ) :
    (∀ i, Integrable
      (flattenedWeightedSteinComponent hdim (inverseEntryProduct indices) D i)
      (halfGaussianPi (n + 1))) ∧
    (∀ i, Integrable
      (flattenedWeightedSteinComponentDerivative hdim (inverseEntryProduct indices)
        (inverseEntryProductDerivative indices) D i)
      (halfGaussianPi (n + 1))) ∧
    (∀ i, Integrable (fun x ↦ 2 * x i *
      flattenedWeightedSteinComponent hdim (inverseEntryProduct indices) D i x)
      (halfGaussianPi (n + 1))) := by
  have hprod4 := memLp_inverseEntryProduct_four W hmargin indices
  have hprod2 := hprod4.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)
  have hV2 (a : Fin k) (j : Fin d) :=
    (memLp_steinVectorFieldValue_entry W (sample_margin_entry32 hmargin) D a j).mono_exponent
      (by norm_num : (2 : ℝ≥0∞) ≤ 16)
  have hlin2 (E : Matrix (Fin k) (Fin d) ℝ) (a : Fin k) (j : Fin d) :=
    (memLp_steinVectorFieldLinearization_entry W (sample_margin_entry32 hmargin) D E a j).mono_exponent
      (by norm_num : (2 : ℝ≥0∞) ≤ 4)
  have hv (a : Fin k) (j : Fin d) : Integrable
      (fun R : Matrix (Fin k) (Fin d) ℝ ↦ inverseEntryProduct indices R *
        steinVectorFieldValue R D a j) (halfGaussianMatrix k d) :=
    memLp_one_iff_integrable.mp ((hV2 a j).mul' hprod2)
  have hd (E : Matrix (Fin k) (Fin d) ℝ) (a : Fin k) (j : Fin d) : Integrable
      (fun R : Matrix (Fin k) (Fin d) ℝ ↦
        inverseEntryProductDerivative indices R E * steinVectorFieldValue R D a j +
          inverseEntryProduct indices R * steinVectorFieldLinearization R D E a j)
      (halfGaussianMatrix k d) :=
    memLp_one_iff_integrable.mp
      (((hV2 a j).mul' (memLp_inverseEntryProductDerivative_two W hmargin indices E)).add
        ((hlin2 E a j).mul' hprod2))
  have hr (a : Fin k) (j : Fin d) : Integrable
      (fun R : Matrix (Fin k) (Fin d) ℝ ↦ 2 * R a j *
        (inverseEntryProduct indices R * steinVectorFieldValue R D a j))
      (halfGaussianMatrix k d) := by
    have hR4 := memLp_matrixCoordinate_halfGaussianMatrix a j 4 (by norm_num)
    have hRG2 := hprod4.mul' (r := 2) hR4
    have h := memLp_one_iff_integrable.mp (((hV2 a j).mul' hRG2).const_mul (2 : ℝ))
    apply h.congr
    filter_upwards [] with R
    ring
  have hmp := measurePreserving_flatSuccMatrixMeasurableEquiv hdim
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have h := hmp.integrable_comp_of_integrable
      (hv (flatCoordinateRow hdim i) (flatCoordinateColumn hdim i))
    exact h
  · intro i
    have h := hmp.integrable_comp_of_integrable
      (hd (flatCoordinateMatrixUnit hdim i)
        (flatCoordinateRow hdim i) (flatCoordinateColumn hdim i))
    exact h
  · intro i
    have h := hmp.integrable_comp_of_integrable
      (hr (flatCoordinateRow hdim i) (flatCoordinateColumn hdim i))
    apply h.congr
    filter_upwards [] with x
    simp only [Function.comp_def, flattenedWeightedSteinComponent,
      flatSuccMatrix_apply_flatCoordinatePair]

end A4Research.InverseStein

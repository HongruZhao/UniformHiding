import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H5_FriedmanMelloA1External
import Mathlib.Tactic

/-!
# Project adapter for approved Friedman--Mello A1

After the disclosed Haar-transpose convention has been included in the A1
source contract, every remaining change from its `n,m,s` notation to the
project notation is proved here.  The approved A1 axiom itself is not restated
or strengthened.  In particular, this file proves `m = N`, `n = K`, and that
the leading block of the project representative is `C` before deriving the
frozen H5 measure equality.
-/

open scoped ENNReal ComplexConjugate ComplexOrder
open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.CurrentPRL
open LogdetLean.GramHafnian.UltimateHiding
open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- The unscaled upper-left `N × N` corner of `U Uᵀ`, written directly as
the transpose Gram matrix of the first `N` rows of `U`. -/
def unscaledCOECornerMatrix {N K : ℕ} (hNK : N ≤ K)
    (U : Matrix.unitaryGroup (Fin K) ℂ) : ConcreteMatrixState N :=
  rectangularTransposeGram (topLeftUnitaryBlock hNK le_rfl U)

theorem measurable_unscaledCOECornerMatrix {N K : ℕ} (hNK : N ≤ K) :
    Measurable (unscaledCOECornerMatrix hNK) :=
  (measurable_rectangularTransposeGram N K).comp
    (measurable_topLeftUnitaryBlock hNK le_rfl)

/-- The nested project normalization cancels at the square base: the H5
left-hand side is Haar measure pushed through `U ↦ (U Uᵀ)_[N]`. -/
theorem concreteUnscaledCOECornerLaw_eq_map_unscaledCOECornerMatrix
    {N K : ℕ} (hK : 1 ≤ K) (hNK : N ≤ K) :
    concreteUnscaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K =
      Measure.map (unscaledCOECornerMatrix hNK)
        (unitaryHaarProbabilityMeasure K) := by
  unfold concreteUnscaledCOECornerLaw concreteScaledCOECornerLaw
    concreteHaarAmbientLaw normalizedHaarTransposeGramLaw
    scaledHaarTransposeGramLaw
  rw [dif_pos ⟨hNK, le_rfl⟩]
  rw [Measure.map_map (measurable_unscaleCOECorner N K)
      (measurable_normalizeTransposeGram N K),
    Measure.map_map
      ((measurable_unscaleCOECorner N K).comp
        (measurable_normalizeTransposeGram N K))
      (measurable_scaledHaarTransposeGramMatrix hNK le_rfl)]
  apply Measure.map_congr
  filter_upwards with U
  ext i j
  have hsqrt : Real.sqrt (K : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hK))
  have hsqrt_sq :
      Real.sqrt (K : ℝ) * Real.sqrt (K : ℝ) = (K : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg K)
  simp only [Function.comp_apply, unscaleCOECorner,
    normalizeTransposeGram, scaledHaarTransposeGramMatrix,
    Matrix.smul_apply, unscaledCOECornerMatrix]
  change (((Real.sqrt (K : ℝ))⁻¹ : ℝ) : ℂ) *
      ((((Real.sqrt (K : ℝ))⁻¹ : ℝ) : ℂ) *
        ((K : ℂ) *
          rectangularTransposeGram
            (topLeftUnitaryBlock hNK le_rfl U) i j)) = _
  have hscalarR :
      (Real.sqrt (K : ℝ))⁻¹ *
          ((Real.sqrt (K : ℝ))⁻¹ * (K : ℝ)) = 1 := by
    nth_rewrite 3 [← hsqrt_sq]
    calc
      (Real.sqrt (K : ℝ))⁻¹ *
          ((Real.sqrt (K : ℝ))⁻¹ *
            (Real.sqrt (K : ℝ) * Real.sqrt (K : ℝ))) =
        ((Real.sqrt (K : ℝ))⁻¹ * Real.sqrt (K : ℝ)) *
          ((Real.sqrt (K : ℝ))⁻¹ * Real.sqrt (K : ℝ)) := by ring
      _ = 1 := by rw [inv_mul_cancel₀ hsqrt, one_mul]
  have hscalarC :
      (((Real.sqrt (K : ℝ))⁻¹ : ℝ) : ℂ) *
          ((((Real.sqrt (K : ℝ))⁻¹ : ℝ) : ℂ) * (K : ℂ)) = 1 := by
    have hc := congrArg Complex.ofReal hscalarR
    simpa only [Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_natCast, Complex.ofReal_one] using hc
  calc
    (((Real.sqrt (K : ℝ))⁻¹ : ℝ) : ℂ) *
        ((((Real.sqrt (K : ℝ))⁻¹ : ℝ) : ℂ) *
          ((K : ℂ) * rectangularTransposeGram
            (topLeftUnitaryBlock hNK le_rfl U) i j)) =
        (((Real.sqrt (K : ℝ))⁻¹ : ℝ) : ℂ) *
          ((((Real.sqrt (K : ℝ))⁻¹ : ℝ) : ℂ) * (K : ℂ)) *
          rectangularTransposeGram
            (topLeftUnitaryBlock hNK le_rfl U) i j := by ring
    _ = rectangularTransposeGram
          (topLeftUnitaryBlock hNK le_rfl U) i j := by
      rw [hscalarC, one_mul]

/-- The literal paper support becomes the project's support after the
matrix variable is renamed from `s` to `C`. -/
theorem friedmanMello1985_A1_support_s_eq_projectSupport_C
    {N : ℕ} (C : ConcreteMatrixState N) :
    FriedmanMelloA1.support C ↔ coeCornerSupport C :=
  Iff.rfl

/-- The paper exponent becomes the project exponent under `m = N, n = K`. -/
theorem friedmanMello1985_A1_exponent_m_eq_N_n_eq_K (N K : ℕ) :
    FriedmanMelloA1.densityExponent K N =
      coeCornerDensityExponent N K :=
  rfl

/-- The literal paper weight becomes the project weight. -/
theorem friedmanMello1985_A1_weight_m_eq_N_n_eq_K (N K : ℕ) :
    FriedmanMelloA1.determinantWeight K N =
      coeCornerDeterminantWeight N K :=
  rfl

/-- The raw paper density becomes the project's raw density. -/
theorem friedmanMello1985_A1_rawMeasure_m_eq_N_n_eq_K (N K : ℕ) :
    FriedmanMelloA1.rawDeterminantDensityMeasure K N =
      coeCornerRawDeterminantDensityMeasure N K :=
  rfl

/-- The self-normalized paper density becomes exact project H5. -/
theorem friedmanMello1985_A1_probabilityMeasure_m_eq_N_n_eq_K
    (N K : ℕ) :
    FriedmanMelloA1.determinantDensityProbabilityMeasure K N =
      coeCornerDeterminantDensityProbabilityMeasure N K :=
  rfl

/-- The leading block `s` of A1's law-equivalent `U Uᵀ` representative is
exactly the project's corner `C`. -/
theorem friedmanMello1985_A1_s_eq_C
    {N K : ℕ} (hNK : N ≤ K)
    (U : Matrix.unitaryGroup (Fin K) ℂ) :
    FriedmanMelloA1.s hNK (FriedmanMelloA1.S U) =
      unscaledCOECornerMatrix hNK U := by
  ext i j
  simp [FriedmanMelloA1.s, FriedmanMelloA1.S,
    unscaledCOECornerMatrix, rectangularTransposeGram,
    topLeftUnitaryBlock, Matrix.mul_apply]

/-- The approved A1 contract after only `m=N`, `n=K`; its Haar-transpose
convention is already part of that contract. -/
theorem friedmanMello1985_A1_matrixLaw_m_eq_N_n_eq_K
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    Measure.map
        (fun U : Matrix.unitaryGroup (Fin K) ℂ ↦
          let S := FriedmanMelloA1.S U
          let s := FriedmanMelloA1.s
            (FriedmanMelloA1.dimensionLe h2NK) S
          s)
        (unitaryHaarProbabilityMeasure K) =
      FriedmanMelloA1.determinantDensityProbabilityMeasure K N :=
  FriedmanMelloA1.matrixLaw_external hN h2NK

/-- The separately proved `s=C` adapter identifies the two pushforwards. -/
theorem friedmanMello1985_A1_principalBlockPushforward_eq_project
    {N K : ℕ} (h2NK : 2 * N ≤ K) :
    Measure.map
        (fun U : Matrix.unitaryGroup (Fin K) ℂ ↦
          let S := FriedmanMelloA1.S U
          let s := FriedmanMelloA1.s
            (FriedmanMelloA1.dimensionLe h2NK) S
          s)
        (unitaryHaarProbabilityMeasure K) =
      Measure.map
        (unscaledCOECornerMatrix (FriedmanMelloA1.dimensionLe h2NK))
        (unitaryHaarProbabilityMeasure K) := by
  apply Measure.map_congr
  filter_upwards with U
  exact friedmanMello1985_A1_s_eq_C
    (FriedmanMelloA1.dimensionLe h2NK) U

/-- Exact frozen H5 endpoint derived from approved A1 through the separately
proved substitutions `m=N`, `n=K`, and `s=C`.  No explicit gamma/pi
normalizer is used. -/
theorem friedmanMello1985_unscaledCOECornerLaw_eq_determinantDensity_of_A1
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    concreteUnscaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K =
      coeCornerDeterminantDensityProbabilityMeasure N K := by
  have hNK : N ≤ K := FriedmanMelloA1.dimensionLe h2NK
  have hK : 1 ≤ K := le_trans hN hNK
  calc
    concreteUnscaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K =
        Measure.map (unscaledCOECornerMatrix hNK)
          (unitaryHaarProbabilityMeasure K) :=
      concreteUnscaledCOECornerLaw_eq_map_unscaledCOECornerMatrix hK hNK
    _ = Measure.map
          (fun U : Matrix.unitaryGroup (Fin K) ℂ ↦
            let S := FriedmanMelloA1.S U
            let s := FriedmanMelloA1.s hNK S
            s)
          (unitaryHaarProbabilityMeasure K) :=
      (friedmanMello1985_A1_principalBlockPushforward_eq_project
        h2NK).symm
    _ = FriedmanMelloA1.determinantDensityProbabilityMeasure K N :=
      friedmanMello1985_A1_matrixLaw_m_eq_N_n_eq_K hN h2NK
    _ = coeCornerDeterminantDensityProbabilityMeasure N K :=
      friedmanMello1985_A1_probabilityMeasure_m_eq_N_n_eq_K N K

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

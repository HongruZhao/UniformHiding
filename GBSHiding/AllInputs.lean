import LogdetLean.GramHafnian.ThreePaper.Verification.HidingOutsideCDPaperFacing

/-! All input counts, using the existing rectangular bound in the tall orientation.
No new literature assumption is introduced. -/
open MeasureTheory
open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.CurrentPRL
open LogdetLean.GramHafnian.UltimateHiding

namespace GBSHiding
noncomputable section
set_option maxHeartbeats 2400000

private theorem probabilityTV_one {α : Type*} [MeasurableSpace α]
    (mu nu : Measure α) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    probabilityTotalVariationLE mu nu 1 := by
  refine ⟨by norm_num, fun E _hE ↦ ?_⟩
  have hmu : mu.real E ≤ 1 := measureReal_le_one
  have hnu : nu.real E ≤ 1 := measureReal_le_one
  have hm0 : 0 ≤ mu.real E := measureReal_nonneg
  have hn0 : 0 ≤ nu.real E := measureReal_nonneg
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- All-input version of the literal normalized matrix law, including K < N. -/
theorem normalizedHidingAllInputs
    (H : UnitaryHaarProbabilityFamily)
    (M N K : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M)
    (hK : 1 ≤ K) (hKM : K ≤ M) :
    probabilityTotalVariationLE
      (normalizedHaarTransposeGramLaw H M N K)
      (normalizedGaussianTransposeGramLaw N K)
      (min 1 (615172 * ultimateSquaredHidingRate M N)) := by
  by_cases hNK : N ≤ K
  · exact ThreePaper.PRXQUniformHiding.normalizedMatrixLaw H M N K hN hNK hKM
  have hKN : K ≤ N := by omega
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  letI : IsProbabilityMeasure (scaledHaarTransposeGramLaw H M N K) :=
    scaledHaarTransposeGramLaw_isProbability H hNM hKM
  letI : IsProbabilityMeasure (normalizedHaarTransposeGramLaw H M N K) :=
    Measure.isProbabilityMeasure_map (measurable_normalizeTransposeGram N K).aemeasurable
  letI : IsProbabilityMeasure (normalizedGaussianTransposeGramLaw N K) :=
    Measure.isProbabilityMeasure_map (measurable_normalizeTransposeGram N K).aemeasurable
  by_cases hsmall : 615172 * ultimateSquaredHidingRate M N < 1
  · have hlarge : 615172 * (N : ℝ)^2 < M := by
      have hh : (615172 * (N : ℝ)^2) / M < 1 := by
        simpa only [ultimateSquaredHidingRate, mul_div_assoc] using hsmall
      exact (div_lt_one hM).mp hh
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hKNr : (K : ℝ) ≤ N := by exact_mod_cast hKN
    have hstrict : N + K < M := by
      have hreal : (N : ℝ) + K < M := by nlinarith
      exact_mod_cast hreal
    have hb := ThreePaper.Verification.sqrtScaledHaarBlock_probabilityTotalVariationLE_A1A2A3A4
      (N := K) (K := N) H (by omega) (by omega) hKN hstrict
    have hmap := Sparse.probabilityTotalVariationLE_map
      (rectangularTransposeGram : Matrix (Fin N) (Fin K) ℂ → Matrix (Fin N) (Fin N) ℂ)
      (measurable_rectangularTransposeGram N K) hb
    rw [Sparse.map_rectangularTransposeGram_sqrtScaledHaarBlockLaw H hNM hKM,
      Sparse.map_rectangularTransposeGram_standardGaussianBlockLaw N K] at hmap
    have hraw : probabilityTotalVariationLE
        (scaledHaarTransposeGramLaw H M N K) (gaussianTransposeGramLaw N K)
        (((N : ℝ) + K) * Real.sqrt ((N : ℝ) * K) / M) :=
      ⟨by positivity, hmap⟩
    have hnorm := hraw.map (measurable_normalizeTransposeGram N K)
    change probabilityTotalVariationLE
      (normalizedHaarTransposeGramLaw H M N K)
      (normalizedGaussianTransposeGramLaw N K) _ at hnorm
    rw [min_eq_right hsmall.le]
    apply hnorm.mono
    have hsqrt : Real.sqrt ((N : ℝ) * K) ≤ (N : ℝ) := by
      calc
        _ ≤ Real.sqrt ((N : ℝ)^2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = (N : ℝ) := Real.sqrt_sq (Nat.cast_nonneg N)
    simp only [ultimateSquaredHidingRate, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hM.le
    calc
      ((N : ℝ) + K) * Real.sqrt ((N : ℝ) * K) ≤
          ((N : ℝ) + N) * N :=
        mul_le_mul (by linarith) hsqrt (Real.sqrt_nonneg _) (by positivity)
      _ ≤ 615172 * (N : ℝ)^2 := by nlinarith
  · rw [min_eq_left (le_of_not_gt hsmall)]
    exact probabilityTV_one _ _

/-- Every measurable observable of a union block inherits the all-input bound.
This includes overlapping fixed panels and their measurable order statistics. -/
theorem observableHidingAllInputs
    {α : Type*} [MeasurableSpace α]
    (H : UnitaryHaarProbabilityFamily)
    (M L K : ℕ) (hL : 1 ≤ L) (hLM : L ≤ M)
    (hK : 1 ≤ K) (hKM : K ≤ M)
    (f : Matrix (Fin L) (Fin L) ℂ → α) (hf : Measurable f) :
    probabilityTotalVariationLE
      ((normalizedHaarTransposeGramLaw H M L K).map f)
      ((normalizedGaussianTransposeGramLaw L K).map f)
      (min 1 (615172 * ultimateSquaredHidingRate M L)) :=
  (normalizedHidingAllInputs H M L K hL hLM hK hKM).map hf

open LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding

/-- Literal common-source ordered panel, with no restriction L ≤ K. -/
theorem orderedFixedPatternPanelAllInputs
    (H : UnitaryHaarProbabilityFamily)
    {q N L K M : Nat} (hL : 1 ≤ L) (hLM : L ≤ M)
    (hK : 1 ≤ K) (hKM : K ≤ M)
    (rows : Fin q → (Fin N ↪ Fin L)) :
    probabilityTotalVariationLE
      (Measure.map (orderedPatternPanel rows)
        (Measure.map
          (preselectedPrincipalSubmatrixTuple q L (orderedPatternSets rows))
          (normalizedHaarTransposeGramLaw H M L K)))
      (Measure.map
        (fun G j ↦ ThreePaper.DisjointGaussianRows.orderedNormalizedGram
          (K := K) (rows j) G)
        (standardComplexGaussianRectangularMeasure L K))
      (min 1 (615172 * ultimateSquaredHidingRate M L)) := by
  have hbase := observableHidingAllInputs H M L K hL hLM hK hKM
    (preselectedPrincipalSubmatrixTuple q L (orderedPatternSets rows))
    (measurable_preselectedPrincipalSubmatrixTuple q L (orderedPatternSets rows))
  have hpanel := hbase.map (measurable_orderedPatternPanel rows)
  rw [orderedGaussianPatternPanelLaw rows] at hpanel
  exact hpanel

#print axioms orderedFixedPatternPanelAllInputs
#print axioms normalizedHidingAllInputs
#print axioms observableHidingAllInputs
end
end GBSHiding

import LogdetLean.GramHafnian.SymmetricGaussianHafnian.LiteralCharacteristic
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.EdgeMatrixReconstruction

/-!
# Fourier compression for the literal independent-edge cofactor law

This file identifies the actual cofactor characteristic function with the
scalar-plus-bilinear Gaussian conditional integral.  The background law,
the three exposed Gaussian blocks, and the deterministic hafnian expansion
are all proved identities.  Consequently the global two-coordinate and
radial compression results have no distributional or compression gates.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal BigOperators Real

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

set_option maxHeartbeats 1600000

/-- Coefficient of the additional exposed scalar edge. -/
def edgeBackgroundEll {m : ℕ} (R : Edge (Fin m) → ℂ)
    (w : Fin (m + 2) → ℂ) : ℂ :=
  ∑ j : Fin m, w (remainingIndex m j) * edgeCofactor R j

/-- Matrix of the exposed bilinear phase, with its Fourier weights. -/
def edgeBackgroundMatrix {m : ℕ} (R : Edge (Fin m) → ℂ)
    (w : Fin (m + 2) → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  fun a b ↦ ∑ j : Fin m,
    w (remainingIndex m j) * fixedBackgroundM (matrixOfEdges R) j a b

@[fun_prop]
theorem measurable_edgeBackgroundEll {m : ℕ} (w : Fin (m + 2) → ℂ) :
    Measurable (fun R : Edge (Fin m) → ℂ ↦ edgeBackgroundEll R w) := by
  unfold edgeBackgroundEll
  fun_prop

@[fun_prop]
theorem measurable_edgeBackgroundMatrix_entry
    {m : ℕ} (w : Fin (m + 2) → ℂ) (a b : Fin m) :
    Measurable (fun R : Edge (Fin m) → ℂ ↦ edgeBackgroundMatrix R w a b) := by
  unfold edgeBackgroundMatrix
  apply Finset.measurable_sum
  intro j _hj
  apply measurable_const.mul
  by_cases h : b ≠ j ∧ a ≠ j ∧ a ≠ b
  · simp only [fixedBackgroundM, if_pos h]
    apply Continuous.measurable
    apply continuous_typeHafnian.comp
    fun_prop
  · simp only [fixedBackgroundM, if_neg h]
    exact measurable_const

/-- Dependence of the scalar coefficient only on uncompressed weights. -/
theorem edgeBackgroundEll_congr_weights {m : ℕ}
    (R : Edge (Fin m) → ℂ) {w v : Fin (m + 2) → ℂ}
    (hwv : ∀ j : Fin m, w (remainingIndex m j) = v (remainingIndex m j)) :
    edgeBackgroundEll R w = edgeBackgroundEll R v := by
  unfold edgeBackgroundEll
  apply Finset.sum_congr rfl
  intro j _hj
  rw [hwv j]

/-- Dependence of the bilinear matrix only on uncompressed weights. -/
theorem edgeBackgroundMatrix_congr_weights {m : ℕ}
    (R : Edge (Fin m) → ℂ) {w v : Fin (m + 2) → ℂ}
    (hwv : ∀ j : Fin m, w (remainingIndex m j) = v (remainingIndex m j)) :
    edgeBackgroundMatrix R w = edgeBackgroundMatrix R v := by
  funext a b
  unfold edgeBackgroundMatrix
  apply Finset.sum_congr rfl
  intro j _hj
  rw [hwv j]

/-- Exact phase after splitting the actual edge variables into their
background, common scalar edge, and two exposed stars. -/
theorem edgeCofactorPhase_twoExposedSplit {m : ℕ}
    (x : Edge (Fin (m + 2)) → ℂ) (w : Fin (m + 2) → ℂ) :
    edgeCofactorPhase x w =
      ((twoExposedSplit m x).2.1 * edgeBackgroundEll (twoExposedSplit m x).1 w).re +
        complexBilinearPhase (edgeBackgroundMatrix (twoExposedSplit m x).1 w)
          (edgeCofactor (twoExposedSplit m x).1)
          (w (exposedXIndex m)) (w (exposedYIndex m))
          (twoExposedSplit m x).2.2.1 (twoExposedSplit m x).2.2.2 := by
  unfold edgeCofactorPhase
  simp_rw [edgeCofactor_eq_matrixCofactor]
  rw [← twoExposedMatrix_twoExposedSplit m x, weightedCofactorSum_twoExposedMatrix]
  unfold edgeBackgroundEll edgeBackgroundMatrix complexBilinearPhase
  simp_rw [edgeCofactor_eq_matrixCofactor]
  change _ = ((twoExposedSplit m x).2.1 *
      (∑ j : Fin m, w (remainingIndex m j) *
        matrixCofactor (matrixOfEdges (twoExposedSplit m x).1) j)).re +
    (transposeBilinear (twoExposedSplit m x).2.2.1
      (fun a b ↦ ∑ j : Fin m, w (remainingIndex m j) *
        fixedBackgroundM (matrixOfEdges (twoExposedSplit m x).1) j a b)
      (twoExposedSplit m x).2.2.2 +
    w (exposedXIndex m) * transposeDot (twoExposedSplit m x).2.2.2
      (matrixCofactor (matrixOfEdges (twoExposedSplit m x).1)) +
    w (exposedYIndex m) * transposeDot (twoExposedSplit m x).2.2.1
      (matrixCofactor (matrixOfEdges (twoExposedSplit m x).1))).re
  simp only [Complex.add_re]
  ring

/-- The displayed conditional phase on the genuine exposed Gaussian
product space. -/
def edgeConditionalPhaseCharacter {m : ℕ} (w : Fin (m + 2) → ℂ)
    (p : (Edge (Fin m) → ℂ) × ComplexExposedSample m) : ℂ :=
  Complex.exp (((((p.2.1 * edgeBackgroundEll p.1 w).re +
    complexBilinearPhase (edgeBackgroundMatrix p.1 w) (edgeCofactor p.1)
      (w (exposedXIndex m)) (w (exposedYIndex m)) p.2.2.1 p.2.2.2) : ℝ) : ℂ) * Complex.I)

@[fun_prop]
theorem measurable_edgeConditionalPhaseCharacter {m : ℕ} (w : Fin (m + 2) → ℂ) :
    Measurable (edgeConditionalPhaseCharacter w) := by
  have hM := measurable_edgeBackgroundMatrix_entry w
  have hell := measurable_edgeBackgroundEll w
  have hq := measurable_edgeCofactor (ι := Fin m)
  unfold edgeConditionalPhaseCharacter complexBilinearPhase transposeBilinear transposeDot
  fun_prop

theorem integrable_edgeConditionalPhaseCharacter {m : ℕ} (w : Fin (m + 2) → ℂ) :
    Integrable (edgeConditionalPhaseCharacter w)
      ((edgeGaussian (Fin m)).prod (complexExposedMeasure m)) := by
  apply Integrable.of_bound (measurable_edgeConditionalPhaseCharacter w).aestronglyMeasurable 1
  filter_upwards [] with p
  unfold edgeConditionalPhaseCharacter
  rw [Complex.norm_exp]
  simp

/-- The literal cofactor characteristic function equals the average of
the independently exposed scalar-plus-bilinear Gaussian kernel. -/
theorem edgeCofactorCharacteristic_eq_integral_complexConditionalKernel
    {m : ℕ} (w : Fin (m + 2) → ℂ) :
    edgeCofactorCharacteristic (Fin (m + 2)) w =
      ∫ R : Edge (Fin m) → ℂ,
        complexConditionalKernel (edgeBackgroundEll R w) (edgeBackgroundMatrix R w)
          (edgeCofactor R) (w (exposedXIndex m)) (w (exposedYIndex m))
        ∂edgeGaussian (Fin m) := by
  have hsplit : MeasurePreserving (twoExposedSplit m)
      (edgeGaussian (Fin (m + 2)))
      ((edgeGaussian (Fin m)).prod (complexExposedMeasure m)) :=
    measurePreserving_twoExposedSplit m
  have htransport :
      (∫ x : Edge (Fin (m + 2)) → ℂ,
        edgeConditionalPhaseCharacter w (twoExposedSplit m x) ∂edgeGaussian (Fin (m + 2))) =
      ∫ p, edgeConditionalPhaseCharacter w p
        ∂((edgeGaussian (Fin m)).prod (complexExposedMeasure m)) := by
    have h := integral_map (μ := edgeGaussian (Fin (m + 2)))
      hsplit.measurable.aemeasurable
      (measurable_edgeConditionalPhaseCharacter w).aestronglyMeasurable
    rw [hsplit.map_eq] at h
    exact h.symm
  unfold edgeCofactorCharacteristic
  calc
    (∫ x : Edge (Fin (m + 2)) → ℂ, edgeCofactorPhaseCharacter w x
      ∂edgeGaussian (Fin (m + 2))) =
        ∫ x : Edge (Fin (m + 2)) → ℂ,
          edgeConditionalPhaseCharacter w (twoExposedSplit m x)
          ∂edgeGaussian (Fin (m + 2)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      unfold edgeCofactorPhaseCharacter edgeConditionalPhaseCharacter
      rw [edgeCofactorPhase_twoExposedSplit]
    _ = ∫ p, edgeConditionalPhaseCharacter w p
        ∂((edgeGaussian (Fin m)).prod (complexExposedMeasure m)) := htransport
    _ = _ := by
      rw [integral_prod _ (integrable_edgeConditionalPhaseCharacter w)]
      rfl

/-- The actual local two-coordinate bound.  All distributional, algebraic,
realification, and integration ingredients are instantiated; only the
elementary relation between the three displayed coefficient vectors remains
in the statement. -/
theorem edgeCofactorCharacteristic_two_exposed_max
    {m : ℕ} (w wLeft wRight : Fin (m + 2) → ℂ)
    {theta : ℝ} (htheta : 0 < theta) (htheta_one : theta < 1)
    (hbgLeft : ∀ j : Fin m, wLeft (remainingIndex m j) = w (remainingIndex m j))
    (hbgRight : ∀ j : Fin m, wRight (remainingIndex m j) = w (remainingIndex m j))
    (hLeftY : wLeft (exposedYIndex m) = 0)
    (hRightX : wRight (exposedXIndex m) = 0)
    (hscaleX : w (exposedXIndex m) = Real.sqrt theta • wLeft (exposedXIndex m))
    (hscaleY : w (exposedYIndex m) = Real.sqrt (1 - theta) • wRight (exposedYIndex m)) :
    ‖edgeCofactorCharacteristic (Fin (m + 2)) w‖ ≤
      max ‖edgeCofactorCharacteristic (Fin (m + 2)) wLeft‖
        ‖edgeCofactorCharacteristic (Fin (m + 2)) wRight‖ := by
  have hellLeft R := edgeBackgroundEll_congr_weights R hbgLeft
  have hellRight R := edgeBackgroundEll_congr_weights R hbgRight
  have hMLeft R := edgeBackgroundMatrix_congr_weights R hbgLeft
  have hMRight R := edgeBackgroundMatrix_congr_weights R hbgRight
  rw [edgeCofactorCharacteristic_eq_integral_complexConditionalKernel w,
    edgeCofactorCharacteristic_eq_integral_complexConditionalKernel wLeft,
    edgeCofactorCharacteristic_eq_integral_complexConditionalKernel wRight]
  simp_rw [hellLeft, hellRight, hMLeft, hMRight, hLeftY, hRightX, hscaleX, hscaleY]
  exact norm_integral_complexConditionalKernel_sqrt_le_max
    (edgeGaussian (Fin m))
    (fun R ↦ edgeBackgroundEll R w) (fun R ↦ edgeBackgroundMatrix R w) edgeCofactor
    (measurable_edgeBackgroundEll w) (measurable_edgeBackgroundMatrix_entry w)
    measurable_edgeCofactor (wLeft (exposedXIndex m)) (wRight (exposedYIndex m))
    htheta htheta_one

/-- Explicit local compression decreases support while preserving the
exact Fourier energy for the literal cofactor characteristic function. -/
theorem edgeCofactorCharacteristic_penultimate_final_two_endpoints
    (m : ℕ) (w : Fin (m + 2) → ℂ)
    (hX : w (exposedXIndex m) ≠ 0) (hY : w (exposedYIndex m) ≠ 0) :
    ∃ wLeft wRight : Fin (m + 2) → ℂ,
      coordinateSupportCard wLeft < coordinateSupportCard w ∧
      coordinateSupportCard wRight < coordinateSupportCard w ∧
      coordinateEnergy wLeft = coordinateEnergy w ∧
      coordinateEnergy wRight = coordinateEnergy w ∧
      ‖edgeCofactorCharacteristic (Fin (m + 2)) w‖ ≤
        max ‖edgeCofactorCharacteristic (Fin (m + 2)) wLeft‖
          ‖edgeCofactorCharacteristic (Fin (m + 2)) wRight‖ := by
  refine ⟨leftExposedEndpoint w (exposedTheta w), rightExposedEndpoint w (exposedTheta w),
    coordinateSupportCard_leftExposedEndpoint_lt hX hY,
    coordinateSupportCard_rightExposedEndpoint_lt hX hY,
    coordinateEnergy_leftExposedEndpoint hX hY,
    coordinateEnergy_rightExposedEndpoint hX hY, ?_⟩
  apply edgeCofactorCharacteristic_two_exposed_max
    w (leftExposedEndpoint w (exposedTheta w)) (rightExposedEndpoint w (exposedTheta w))
    (exposedTheta_pos hX hY) (exposedTheta_lt_one hX hY)
  · exact leftExposedEndpoint_background w (exposedTheta w)
  · exact rightExposedEndpoint_background w (exposedTheta w)
  · exact leftExposedEndpoint_Y w (exposedTheta w)
  · exact rightExposedEndpoint_X w (exposedTheta w)
  · rw [leftExposedEndpoint_X, smul_smul,
      mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (exposedTheta_pos hX hY)), one_smul]
  · rw [rightExposedEndpoint_Y, smul_smul,
      mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (sub_pos.mpr (exposedTheta_lt_one hX hY))),
      one_smul]

/-- Any two nonzero Fourier coordinates can be exposed and compressed in
the literal independent-edge ensemble. -/
theorem edgeCofactorCharacteristic_global_two_endpoints (m : ℕ) :
    ∀ w : Fin (m + 2) → ℂ, 1 < coordinateSupportCard w →
      ∃ wLeft wRight : Fin (m + 2) → ℂ,
        coordinateSupportCard wLeft < coordinateSupportCard w ∧
        coordinateSupportCard wRight < coordinateSupportCard w ∧
        coordinateEnergy wLeft = coordinateEnergy w ∧
        coordinateEnergy wRight = coordinateEnergy w ∧
        ‖edgeCofactorCharacteristic (Fin (m + 2)) w‖ ≤
          max ‖edgeCofactorCharacteristic (Fin (m + 2)) wLeft‖
            ‖edgeCofactorCharacteristic (Fin (m + 2)) wRight‖ := by
  apply global_two_endpoints_of_penultimate_final
    (edgeCofactorCharacteristic (Fin (m + 2)))
    (edgeCofactorCharacteristic_permutationInvariant (m + 2))
  intro w hX hY
  exact edgeCofactorCharacteristic_penultimate_final_two_endpoints m w hX hY

/-- Fully iterated radial compression of the literal level-`r` cofactor
vector.  No local compression or distributional hypothesis is assumed. -/
theorem edgeCofactorCharacteristic_norm_le_singleton
    (r : ℕ) (hr : 2 ≤ r) (base : Fin (2 * r - 1)) (w : Fin (2 * r - 1) → ℂ) :
    ‖edgeCofactorCharacteristic (Fin (2 * r - 1)) w‖ ≤
      ‖edgeCofactorCharacteristic (Fin (2 * r - 1))
        (singleCoordinate base (Real.sqrt (coordinateEnergy w) : ℂ))‖ := by
  let : Nonempty (Fin (2 * r - 1)) := ⟨base⟩
  have hdim : (2 * r - 3) + 2 = 2 * r - 1 := by omega
  have htwo := edgeCofactorCharacteristic_global_two_endpoints (2 * r - 3)
  rw [hdim] at htwo
  exact finite_coordinate_compression_of_two_endpoints
    (edgeCofactorCharacteristic (Fin (2 * r - 1))) base
    edgeCofactorCharacteristic_singletonExchangeable
    (edgeCofactorCharacteristic_commonPhaseInvariant
      (r := r - 1) (by simp; omega) (by omega)) htwo w

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian

import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H18_CompactL1_Proof

/-!
# CONDITIONAL H17 from compact-time zero-extended `L^1` envelopes

The first four projective differentiation identities come from the compact
H18 module.  Lower derivatives are therefore differentiable.  At order four,
the compact-time direction envelope and fixed-direction continuity give
dominated continuity at every real time.
-/

open TopologicalSpace MeasureTheory Set Filter
open scoped Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- CONDITIONAL H17 using the moving-support-safe compact-time route. -/
theorem coeCorner_centeredProjective_eventPath_contDiff_four_compactL1_conditional
    (hH16 : CoeCornerCenteredFixedDirectionH16Contract)
    (hfixedC4 : CoeCornerCenteredFixedDirectionC4Contract)
    (hzero : CoeCornerCenteredZeroExtScoreAgreementContract)
    (henvelope : CoeCornerCenteredCompactZeroExtL1EnvelopeContract)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    ContDiff ℝ 4
      (concreteProjectiveAveragedCenteredCOEEventPath N K event) := by
  have hdiff : ∀ m : ℕ, m < 4 →
      Differentiable ℝ
        (iteratedDeriv m
          (concreteProjectiveAveragedCenteredCOEEventPath N K event)) := by
    intro m hm
    have hfun :
        iteratedDeriv m
            (concreteProjectiveAveragedCenteredCOEEventPath N K event) =
          fun x : ℝ ↦ ∫ v : ComplexUnitSphere N,
            iteratedDeriv m
                (concreteCenteredRankOneCOEEventPath K v event) x
              ∂(complexUnitSphereProbabilityMeasure N) := by
      funext x
      exact
        coeCorner_centeredProjective_eventPath_derivative_interchange_at_compactL1_conditional
          hH16 hfixedC4 hzero henvelope hN hboundary
            (Nat.le_of_lt hm) event hevent x
    rw [hfun]
    intro x
    exact (hasDerivAt_integral_iteratedDeriv_compact_zeroExt
      hH16 hfixedC4 hzero henvelope hN hboundary hm
        event hevent x).differentiableAt
  refine (contDiff_nat_iff_iteratedDeriv
    (𝕜 := ℝ) (n := 4)
    (f := concreteProjectiveAveragedCenteredCOEEventPath N K event)).2 ?_
  constructor
  · intro m hm
    by_cases htop : m = 4
    · subst m
      have hfun :
          iteratedDeriv 4
              (concreteProjectiveAveragedCenteredCOEEventPath N K event) =
            fun x : ℝ ↦ ∫ v : ComplexUnitSphere N,
              iteratedDeriv 4
                  (concreteCenteredRankOneCOEEventPath K v event) x
                ∂(complexUnitSphereProbabilityMeasure N) := by
        funext x
        exact
          coeCorner_centeredProjective_eventPath_derivative_interchange_at_compactL1_conditional
            hH16 hfixedC4 hzero henvelope hN hboundary
              (by omega) event hevent x
      rw [hfun, continuous_iff_continuousAt]
      intro y
      let R : ℝ := |y| + 1
      have hR : 0 < R := by
        dsimp [R]
        positivity
      have hy : y ∈ Set.Ioo (-R) R := by
        dsimp [R]
        constructor
        · linarith [neg_le_abs y]
        · linarith [le_abs_self y]
      have hs : Set.Ioo (-R) R ∈ 𝓝 y := isOpen_Ioo.mem_nhds hy
      obtain ⟨B, hB, hInt, hboundCompact⟩ :=
        exists_compact_directionMajorant_iteratedDeriv_zeroExt
          hH16 hzero henvelope hN hboundary (by omega : 4 ≤ 4)
            event hevent R hR
      let F : ℝ → ComplexUnitSphere N → ℝ := fun x v ↦
        iteratedDeriv 4
          (concreteCenteredRankOneCOEEventPath K v event) x
      have hF_meas : ∀ᶠ x in 𝓝 y,
          AEStronglyMeasurable (F x)
            (complexUnitSphereProbabilityMeasure N) := by
        filter_upwards [hs] with x hx
        exact (hInt x ⟨le_of_lt hx.1, le_of_lt hx.2⟩).1
      have h_bound : ∀ᶠ x in 𝓝 y,
          ∀ᵐ v ∂(complexUnitSphereProbabilityMeasure N),
            ‖F x v‖ ≤ B v := by
        filter_upwards [hs] with x hx
        exact hboundCompact.mono fun v hv ↦
          hv x ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      have h_cont :
          ∀ᵐ v ∂(complexUnitSphereProbabilityMeasure N),
            ContinuousAt (fun x ↦ F x v) y := by
        filter_upwards [] with v
        exact
          (hfixedC4 hN hboundary v event hevent).continuous_iteratedDeriv' 4
            |>.continuousAt
      exact continuousAt_of_dominated hF_meas h_bound hB h_cont
    · exact (hdiff m (by omega)).continuous
  · intro m hm
    exact hdiff m hm

/-- Exact-quantifier wrapper matching the original H17 declaration. -/
theorem coeCorner_centeredProjective_eventPath_contDiff_four_H17_compactL1_conditional
    (hH16 : CoeCornerCenteredFixedDirectionH16Contract)
    (hfixedC4 : CoeCornerCenteredFixedDirectionC4Contract)
    (hzero : CoeCornerCenteredZeroExtScoreAgreementContract)
    (henvelope : CoeCornerCenteredCompactZeroExtL1EnvelopeContract)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    ContDiff ℝ 4
      (concreteProjectiveAveragedCenteredCOEEventPath N K event) := by
  exact
    coeCorner_centeredProjective_eventPath_contDiff_four_compactL1_conditional
      hH16 hfixedC4 hzero henvelope hN hboundary event hevent

/-- Exact H17 wrapper using only the order-independent a.e. support contract
instead of a separate score-agreement premise. -/
theorem coeCorner_centeredProjective_eventPath_contDiff_four_H17_compactL1_support_conditional
    (hH16 : CoeCornerCenteredFixedDirectionH16Contract)
    (hfixedC4 : CoeCornerCenteredFixedDirectionC4Contract)
    (hsupport : CoeCornerCenteredScaledCOESupportContract)
    (henvelope : CoeCornerCenteredCompactZeroExtL1EnvelopeContract)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    ContDiff ℝ 4
      (concreteProjectiveAveragedCenteredCOEEventPath N K event) := by
  exact
    coeCorner_centeredProjective_eventPath_contDiff_four_H17_compactL1_conditional
      hH16 hfixedC4 (zeroExtScoreAgreement_of_scaledCOESupport hsupport)
        henvelope hN hboundary event hevent

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

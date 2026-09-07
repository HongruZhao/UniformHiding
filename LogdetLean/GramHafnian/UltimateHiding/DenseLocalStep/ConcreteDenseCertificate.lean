import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.ConcreteCorrelatedPath
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.BetaLogMomentAdapter
import LogdetLean.GramHafnian.UltimateHiding.Dense.HaarRecursionExternal
import LogdetLean.GramHafnian.UltimateHiding.Dense.SquaredEndpoint

/-!
# Uniform concrete score certificate and dense local-step composition

This file isolates the one remaining analytic target as a transparent
proposition.  It is exactly the concrete same-beta score structure, uniformly
over the dense parameter range, with four explicit constants.  No score bound
is assumed or declared here.

Given a proof of that proposition, the beta-log moment adapter, exact Haar
one-column recursion, normalization transport, and arithmetic bookkeeping
produce the literal `ConcreteDenseSquaredLocalStepAt` endpoint.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

noncomputable section

open LocalAnticoncentration

/-- The exact remaining dense score obligation, with no hidden theorem-valued
fields beyond `ConcreteSharedBetaScoreBoundsAt` itself.  The constants are
fixed uniformly over all Haar presentations and all dimensions in the
`K >= 16 N`, `m >= 24 N^2` window. -/
def UniformConcreteSharedBetaScoreCertificateAt
    (CscoreOne CscoreTwo CorbitalTwo CorbitalThree : ℝ) : Prop :=
  ∀ (H : UnitaryHaarProbabilityFamily) (N K m : ℕ),
    1 ≤ N → N ≤ K → K ≤ m → 24 * N ^ 2 ≤ m → 16 * N ≤ K →
      ConcreteSharedBetaScoreBoundsAt m N
        (Dense.concreteHaarAmbientLaw H N K m)
        CscoreOne CscoreTwo CorbitalTwo CorbitalThree

/-- The normalized ambient Haar law is a probability measure throughout the
physical range. -/
theorem concreteHaarAmbientLaw_isProbability
    (H : UnitaryHaarProbabilityFamily) {N K m : ℕ}
    (hNK : N ≤ K) (hKm : K ≤ m) :
    IsProbabilityMeasure (Dense.concreteHaarAmbientLaw H N K m) := by
  let _ : IsProbabilityMeasure
      (scaledHaarTransposeGramLaw H m N K) :=
    scaledHaarTransposeGramLaw_isProbability H (hNK.trans hKm) hKm
  unfold Dense.concreteHaarAmbientLaw normalizedHaarTransposeGramLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_normalizeTransposeGram N K).aemeasurable

/-- Undoing the common `1/sqrt K` normalization recovers the literal scaled
Haar transpose-Gram law used by the squared hiding endpoint. -/
theorem map_denormalize_concreteHaarAmbientLaw
    (H : UnitaryHaarProbabilityFamily) (N m : ℕ)
    {K : ℕ} (hK : 1 ≤ K) :
    Measure.map (denormalizeTransposeGram N K)
        (Dense.concreteHaarAmbientLaw H N K m) =
      Dense.denseHaarAmbientLaw H N K m := by
  unfold Dense.concreteHaarAmbientLaw normalizedHaarTransposeGramLaw
  rw [Measure.map_map (measurable_denormalizeTransposeGram N K)
    (measurable_normalizeTransposeGram N K)]
  have hcomp :
      denormalizeTransposeGram N K ∘ normalizeTransposeGram N K = id := by
    funext A
    exact denormalize_normalizeTransposeGram N hK A
  simpa [hcomp]

/-- A uniform concrete score certificate closes the exact dense one-step
obligation.  The displayed constant is the literal substitution of the
proved beta constants `(4,5,4,12)` into the same-beta Taylor bridge, plus the
proved bad-event constant `72`. -/
theorem concreteDenseSquaredLocalStepAt_of_uniformScoreCertificate
    {CscoreOne CscoreTwo CorbitalTwo CorbitalThree : ℝ}
    (hscore : UniformConcreteSharedBetaScoreCertificateAt
      CscoreOne CscoreTwo CorbitalTwo CorbitalThree) :
    Dense.ConcreteDenseSquaredLocalStepAt
      (4 * CscoreOne + 5 * CscoreTwo +
        2 * CorbitalTwo + 2 * CorbitalThree + 72) 24 16 := by
  have hsample := hscore
    canonicalUnitaryHaarProbabilityFamily 1 16 24
    (by omega) (by omega) (by omega) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · have h1 := hsample.scoreOne_nonneg
    have h2 := hsample.scoreTwo_nonneg
    have h3 := hsample.orbitalTwo_nonneg
    have h4 := hsample.orbitalThree_nonneg
    nlinarith
  · intro H N K m hN hNK hKm hlarge hdense
    let _ : IsProbabilityMeasure
        (Dense.concreteHaarAmbientLaw H N K m) :=
      concreteHaarAmbientLaw_isProbability H hNK hKm
    have hlargeR : 24 * (N : ℝ) ^ 2 ≤ (m : ℝ) := by
      exact_mod_cast hlarge
    have hmom : OneColumnLogMomentBoundsAt 4 5 4 12 m N :=
      oneColumnLogMomentBoundsAt_concrete_of_twentyFour_sq_le hN hlarge
    have hnormalized := probabilityTVLE_concreteOneColumn_of_scoreBounds
      hN (hNK.trans hKm) hlargeR
      (Dense.concreteHaarAmbientLaw H N K m) hmom
      (hscore H N K m hN hNK hKm hlarge hdense)
    rw [← Dense.concreteHaar_oneColumn_step H hN hNK hKm] at hnormalized
    have hdenormalized := hnormalized.map
      (measurable_denormalizeTransposeGram N K)
    have hK : 1 ≤ K := hN.trans hNK
    rw [map_denormalize_concreteHaarAmbientLaw H N m hK,
      map_denormalize_concreteHaarAmbientLaw H N (m + 1) hK]
      at hdenormalized
    convert hdenormalized using 1
    · rfl
    · unfold Dense.denseTelescopingRate
      ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

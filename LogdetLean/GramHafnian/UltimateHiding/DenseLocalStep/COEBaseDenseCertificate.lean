import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.COEBaseRadialPropagation
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.ConcreteDenseCertificate

/-!
# Dense local theorem from a score certificate only at the canonical COE base

The score calculation is required only for the square scaled-COE corner law.
The preceding radial-propagation module then transports the resulting local
total-variation estimate to every rectangular ambient Haar law without loss.

This avoids asking indicator-event score fields to propagate through a Markov
kernel: an ambient indicator pulls back to a `[0,1]`-valued kernel section.
The local-TV statement, which is the actual input to telescoping, *does*
contract under the radial chain and is therefore the correct interface.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding
open CurrentPRL

/-- The exact remaining score obligation, only at the canonical square
scaled-COE corner.  The one-column index `m` remains explicit because its beta
coefficient is part of the same-beta path, while the input matrix law is the
single square base law at `(N,K)`. -/
def UniformCanonicalScaledCOESharedBetaScoreCertificateAt
    (CscoreOne CscoreTwo CorbitalTwo CorbitalThree : ℝ) : Prop :=
  ∀ (N K m : ℕ),
    1 ≤ N → N ≤ K → K ≤ m → 24 * N ^ 2 ≤ m → 16 * N ≤ K →
      ConcreteSharedBetaScoreBoundsAt m N
        (Dense.concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K)
        CscoreOne CscoreTwo CorbitalTwo CorbitalThree

/-- Haar uniqueness transports the canonical square-base score certificate
to any presentation of normalized unitary Haar probability. -/
theorem UniformCanonicalScaledCOESharedBetaScoreCertificateAt.forHaarFamily
    {CscoreOne CscoreTwo CorbitalTwo CorbitalThree : ℝ}
    (hscore : UniformCanonicalScaledCOESharedBetaScoreCertificateAt
      CscoreOne CscoreTwo CorbitalTwo CorbitalThree)
    (H : UnitaryHaarProbabilityFamily) (N K m : ℕ)
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKm : K ≤ m)
    (hlarge : 24 * N ^ 2 ≤ m) (hdense : 16 * N ≤ K) :
    ConcreteSharedBetaScoreBoundsAt m N
      (Dense.concreteScaledCOECornerLaw H N K)
      CscoreOne CscoreTwo CorbitalTwo CorbitalThree := by
  change ConcreteSharedBetaScoreBoundsAt m N
    (Dense.concreteHaarAmbientLaw H N K K)
    CscoreOne CscoreTwo CorbitalTwo CorbitalThree
  rw [Dense.concreteHaarAmbientLaw_eq_canonical H N K K]
  exact hscore N K m hN hNK hKm hlarge hdense

/-- A canonical square-COE score certificate closes the same concrete dense
local endpoint as the former all-ambient score interface.  The constant is
unchanged: beta moments contribute `(4,5,4,12)` and the bad-event tail
contributes `72`. -/
theorem concreteDenseSquaredLocalStepAt_of_canonicalCOEBaseScoreCertificate
    {CscoreOne CscoreTwo CorbitalTwo CorbitalThree : ℝ}
    (hscore : UniformCanonicalScaledCOESharedBetaScoreCertificateAt
      CscoreOne CscoreTwo CorbitalTwo CorbitalThree) :
    Dense.ConcreteDenseSquaredLocalStepAt
      (4 * CscoreOne + 5 * CscoreTwo +
        2 * CorbitalTwo + 2 * CorbitalThree + 72) 24 16 := by
  have hsample := hscore 1 16 24
    (by omega) (by omega) (by omega) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · have h1 := hsample.scoreOne_nonneg
    have h2 := hsample.scoreTwo_nonneg
    have h3 := hsample.orbitalTwo_nonneg
    have h4 := hsample.orbitalThree_nonneg
    nlinarith
  · intro H N K m hN hNK hKm hlarge hdense
    have hlargeR : 24 * (N : ℝ) ^ 2 ≤ (m : ℝ) := by
      exact_mod_cast hlarge
    have hmom : OneColumnLogMomentBoundsAt 4 5 4 12 m N :=
      oneColumnLogMomentBoundsAt_concrete_of_twentyFour_sq_le hN hlarge
    have hbase :=
      probabilityTVLE_concreteScaledCOECorner_oneColumn_of_scoreBounds
        H hN hNK hKm hlargeR hmom
        (hscore.forHaarFamily H N K m hN hNK hKm hlarge hdense)
    have hambient :=
      probabilityTVLE_concreteHaarAmbient_oneColumn_of_scaledCOE
        H hN hNK hKm (hNK.trans hKm) hbase
    rw [← Dense.concreteHaar_oneColumn_step H hN hNK hKm] at hambient
    have hdenormalized := hambient.map
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

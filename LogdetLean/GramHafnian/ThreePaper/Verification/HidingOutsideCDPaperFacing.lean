import LogdetLean.GramHafnian.ThreePaper.UniformMatrixHiding
import LogdetLean.GramHafnian.UltimateHiding.SquaredCompletionRawDensity
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19QuantitativeEndpoint

/-!
# Literal paper-facing endpoints outside Appendices C and D

This module supplies exact theorem shapes for displays which previously
pointed only to related implementation theorems.  In particular it keeps the
paper's common `K^{-1/2}` normalization in the target-convergence and local
one-column statements, exposes the joint-sampling semantics of the Haar
recursion, and closes the sparse `68 N^2/M` stitch from the proved raw-density
theorem.  It introduces no new scientific assumptions.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.ThreePaper.Verification

noncomputable section

open LogdetLean.GramHafnian
open LocalAnticoncentration
open UltimateHiding
open UltimateHiding.Dense
open UltimateHiding.DenseScore
open UltimateHiding.DenseLocalStep
open UltimateHiding.Sparse
open LogdetLean.GramHafnian.ThreePaper.UniformMatrixHiding

/-! ## Normalized target convergence and one-column step -/

/-- Literal normalized version of the paper's target convergence display:
for fixed positive `N <= K`, every starting ambient dimension has a later
normalized Haar transpose-Gram law within `epsilon` of the normalized
Gaussian target. -/
theorem normalizedHaarTransposeGram_targetConvergence_A1A2A3A4
    (H : UnitaryHaarProbabilityFamily) {N K start : Nat}
    (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K) :
    ∀ epsilon : Real, 0 < epsilon →
      ∃ n : Nat,
        LocalAnticoncentration.probabilityTotalVariationLE
          (normalizedHaarTransposeGramLaw H (start + n) N K)
          (normalizedGaussianTransposeGramLaw N K) epsilon := by
  intro epsilon hepsilon
  obtain ⟨n, hn⟩ :=
    Dense.rawDensity_denseHaarAmbient_targetConvergence_unrestricted
      rawDensityTransposeGramQuantitative_proved H hN hK hNK
      epsilon hepsilon
  refine ⟨n, ?_⟩
  unfold normalizedHaarTransposeGramLaw normalizedGaussianTransposeGramLaw
  exact hn.map (measurable_normalizeTransposeGram N K)

/-- The evaluated dense local coefficient is exactly `615138`. -/
theorem concreteDenseSquaredLocalStepAt_615138_A1A2A3A4 :
    Dense.ConcreteDenseSquaredLocalStepAt 615138 24 16 := by
  have h :=
    concreteDenseSquaredLocalStepAt_of_canonicalCOEBaseScoreCertificate
      uniformCanonicalScaledCOESharedBetaScoreCertificate_combinedSharper
  rw [combinedSharperCanonicalOrbitalThirdConstant_eq] at h
  norm_num [exactVarianceCentralScoreOneConstant,
    exactVarianceCentralScoreTwoConstant,
    exactVarianceOrbitalScoreTwoConstant] at h ⊢
  exact h

/-- Literal normalized adjacent-ambient estimate printed in the paper. -/
theorem normalizedHaarTransposeGram_oneColumnTVLE_615138_A1A2A3A4
    (H : UnitaryHaarProbabilityFamily) {N K m : Nat}
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKm : K ≤ m)
    (hlarge : 24 * N ^ 2 ≤ m) (hdense : 16 * N ≤ K) :
    LocalAnticoncentration.probabilityTotalVariationLE
      (normalizedHaarTransposeGramLaw H m N K)
      (normalizedHaarTransposeGramLaw H (m + 1) N K)
      (615138 * (N : Real) ^ 2 /
        ((m : Real) * ((m + 1 : Nat) : Real))) := by
  have hraw := concreteDenseSquaredLocalStepAt_615138_A1A2A3A4.apply
    H hN hNK hKm hlarge hdense
  have hnormalized := hraw.map (measurable_normalizeTransposeGram N K)
  simpa only [Dense.denseHaarAmbientLaw,
    normalizedHaarTransposeGramLaw, Dense.denseTelescopingRate,
    mul_div_assoc] using hnormalized

/-- Public normalized adjacent ambient estimate with the manuscript constant
`615172`, obtained by monotone weakening of the sharp local estimate. -/
theorem normalizedHaarTransposeGram_oneColumnTVLE_615172_A1A2A3A4
    (H : UnitaryHaarProbabilityFamily) {N K m : Nat}
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKm : K ≤ m)
    (hlarge : 24 * N ^ 2 ≤ m) (hdense : 16 * N ≤ K) :
    LocalAnticoncentration.probabilityTotalVariationLE
      (normalizedHaarTransposeGramLaw H m N K)
      (normalizedHaarTransposeGramLaw H (m + 1) N K)
      (615172 * (N : Real) ^ 2 /
        ((m : Real) * ((m + 1 : Nat) : Real))) := by
  apply (normalizedHaarTransposeGram_oneColumnTVLE_615138_A1A2A3A4
    H hN hNK hKm hlarge hdense).mono
  have hscale : 0 ≤ (N : Real) ^ 2 /
      ((m : Real) * ((m + 1 : Nat) : Real)) := by positivity
  calc
    615138 * (N : Real) ^ 2 /
        ((m : Real) * ((m + 1 : Nat) : Real)) =
        615138 * ((N : Real) ^ 2 /
          ((m : Real) * ((m + 1 : Nat) : Real))) := by ring
    _ ≤ 615172 * ((N : Real) ^ 2 /
          ((m : Real) * ((m + 1 : Nat) : Real))) := by nlinarith
    _ = 615172 * (N : Real) ^ 2 /
        ((m : Real) * ((m + 1 : Nat) : Real)) := by ring

/-- The symbolic dense coefficient used by the article is exactly the printed
`615138`. -/
theorem concreteCanonicalDenseHidingSquaredConstant_eq_615138 :
    MatrixLawEndpoints.concreteCanonicalDenseHidingSquaredConstant = 615138 := by
  unfold MatrixLawEndpoints.concreteCanonicalDenseHidingSquaredConstant
  rw [combinedSharperCanonicalOrbitalThirdConstant_eq]
  norm_num [exactVarianceCentralScoreOneConstant,
    exactVarianceCentralScoreTwoConstant,
    exactVarianceOrbitalScoreTwoConstant]

/-- Literal normalized dense-branch endpoint, with the number appearing in
the manuscript rather than a definitionally related symbolic coefficient. -/
theorem normalizedDenseProductHidingTVLE_615138_A1A2A3A4
    (H : UnitaryHaarProbabilityFamily) {M N K : Nat}
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKM : K ≤ M)
    (hlarge : 24 * N ^ 2 ≤ M) (hdense : 16 * N ≤ K) :
    LocalAnticoncentration.probabilityTotalVariationLE
      (normalizedHaarTransposeGramLaw H M N K)
      (normalizedGaussianTransposeGramLaw N K)
      (615138 * (N : Real) ^ 2 / M) := by
  have h := MatrixLawEndpoints.eq_dense_product_hiding_normalized
    H hN hNK hKM hlarge hdense
  rw [concreteCanonicalDenseHidingSquaredConstant_eq_615138] at h
  simpa only [ultimateSquaredHidingRate, mul_div_assoc] using h

/-- Public dense branch endpoint with the single manuscript constant
`615172`, obtained by monotone weakening of the sharp dense endpoint. -/
theorem normalizedDenseProductHidingTVLE_615172_A1A2A3A4
    (H : UnitaryHaarProbabilityFamily) {M N K : Nat}
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKM : K ≤ M)
    (hlarge : 24 * N ^ 2 ≤ M) (hdense : 16 * N ≤ K) :
    LocalAnticoncentration.probabilityTotalVariationLE
      (normalizedHaarTransposeGramLaw H M N K)
      (normalizedGaussianTransposeGramLaw N K)
      (615172 * (N : Real) ^ 2 / M) := by
  apply (normalizedDenseProductHidingTVLE_615138_A1A2A3A4
    H hN hNK hKM hlarge hdense).mono
  have hscale : 0 ≤ (N : Real) ^ 2 / M := by positivity
  calc
    615138 * (N : Real) ^ 2 / M =
        615138 * ((N : Real) ^ 2 / M) := by ring
    _ ≤ 615172 * ((N : Real) ^ 2 / M) := by nlinarith
    _ = 615172 * (N : Real) ^ 2 / M := by ring

/-! ## Exact recursion sampling and event semantics -/

/-- Literal beta-shape and logarithmic-parameter dictionary used in the
one-column recursion display. -/
theorem oneColumnParameterDictionary
    (m N : Nat) (q : Real) :
    oneColumnBetaLaw m N =
        betaMeasure ((m : Real) - (N : Real) + 1) (N : Real) ∧
      oneColumnScalarLog m =
        (1 / 2 : Real) * Real.log (1 + 1 / (m : Real)) ∧
      oneColumnRankOneLog q = (1 / 2 : Real) * Real.log q := by
  unfold oneColumnBetaLaw oneColumnBetaShapeLeft oneColumnBetaShapeRight
    oneColumnScalarLog oneColumnRankOneLog
  exact ⟨rfl, rfl, rfl⟩

/-- The concrete parameter law is exactly the product of the beta radial law
and the uniform sphere law; this is the formal independence assertion in the
paper's recursion. -/
theorem concreteOneColumnParameterLaw_eq_beta_prod_sphere
    (m N : Nat) :
    concreteOneColumnParameterLaw m N =
      (betaMeasure ((m : Real) - (N : Real) + 1) (N : Real)).prod
        (complexUnitSphereProbabilityMeasure N) := by
  rfl

/-- The recursion law as one pushforward of the product law of the old matrix
and an independent beta/sphere parameter pair. -/
theorem concreteHaarOneColumnRecursion_eq_map_product_A1A2A3A4
    (H : UnitaryHaarProbabilityFamily) {N K m : Nat}
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKm : K ≤ m) :
    concreteHaarAmbientLaw H N K (m + 1) =
      Measure.map
        (fun p : Matrix (Fin N) (Fin N) Complex ×
            (Real × ComplexUnitSphere N) ↦
          concreteOneColumnMatrixUpdate m N p.2.1 p.2.2 p.1)
        ((concreteHaarAmbientLaw H N K m).prod
          (concreteOneColumnParameterLaw m N)) := by
  let _ : IsProbabilityMeasure (concreteHaarAmbientLaw H N K m) :=
    concreteHaarAmbientLaw_isProbability H hNK hKm
  rw [concreteHaarOneColumnRecursion_step_eq H hN hNK hKm]
  exact concreteOneColumnMatrixKernel_comp_eq_map_prod
    (concreteHaarAmbientLaw H N K m) hN (hNK.trans hKm)

/-- Eventwise expansion of the same recursion.  The product measure is the
formal statement that `A_m` and `(q_m,v)` are sampled independently. -/
theorem concreteHaarOneColumnRecursion_event_A1A2A3A4
    (H : UnitaryHaarProbabilityFamily) {N K m : Nat}
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKm : K ≤ m)
    (E : Set (Matrix (Fin N) (Fin N) Complex)) (hE : MeasurableSet E) :
    concreteHaarAmbientLaw H N K (m + 1) E =
      ((concreteHaarAmbientLaw H N K m).prod
        (concreteOneColumnParameterLaw m N))
        ((fun p : Matrix (Fin N) (Fin N) Complex ×
            (Real × ComplexUnitSphere N) ↦
          concreteOneColumnMatrixUpdate m N p.2.1 p.2.2 p.1) ⁻¹' E) := by
  rw [concreteHaarOneColumnRecursion_eq_map_product_A1A2A3A4
    H hN hNK hKm]
  exact Measure.map_apply (measurable_concreteOneColumnMatrixUpdate m N) hE

/-! ## Closed sparse branch and exact `68` stitch -/

private def jiangTallSecondMomentValue (M K N : Nat) : Real :=
  (N : Real) * K * M *
      ((M : Real) * ((N : Real) + K) - (N : Real) * K - 1) /
    ((M : Real) ^ 2 - 1)

private structure JiangTallMomentCertificate (M K N : Nat) : Prop where
  energy : Integrable
    (fun Z : Matrix (Fin K) (Fin N) Complex ↦
      (Matrix.trace (Z.conjTranspose * Z)).re)
    (jiangSqrtScaledTallHaarCornerLaw M K N)
  energyMean :
    (∫ Z : Matrix (Fin K) (Fin N) Complex,
      (Matrix.trace (Z.conjTranspose * Z)).re
        ∂(jiangSqrtScaledTallHaarCornerLaw M K N)) =
      (K : Real) * N
  second : Integrable jiangScaledTallGramSecondEnergy
    (jiangSqrtScaledTallHaarCornerLaw M K N)
  secondMean :
    (∫ Z, jiangScaledTallGramSecondEnergy Z
      ∂(jiangSqrtScaledTallHaarCornerLaw M K N)) =
      jiangTallSecondMomentValue M K N
  secondLower :
    (K : Real) * N *
        (((K : Real) + N) - ((K : Real) + N) ^ 2 / (2 * M)) ≤
      jiangTallSecondMomentValue M K N

/-- The exact first and second Haar-corner moments needed by both the closed
KL and TV wrappers. -/
private theorem jiangTallMomentCertificate_proved
    {M K N : Nat} (hN : 0 < N) (hK : 0 < K)
    (hNK : N ≤ K) (hs : K + N < M) :
    JiangTallMomentCertificate M K N := by
  have hM2 : 2 ≤ M := by omega
  have henergy : Integrable
      (fun Z : Matrix (Fin K) (Fin N) Complex ↦
        (Matrix.trace (Z.conjTranspose * Z)).re)
      (jiangSqrtScaledTallHaarCornerLaw M K N) :=
    integrable_jiangSqrtScaledTallHaarCorner_energy hNK hs.le
  have henergyMean :
      (∫ Z : Matrix (Fin K) (Fin N) Complex,
        (Matrix.trace (Z.conjTranspose * Z)).re
          ∂(jiangSqrtScaledTallHaarCornerLaw M K N)) =
        (K : Real) * N := by
    rw [integral_jiangSqrtScaledTallHaarCorner_energy hN hNK hs.le]
    ring
  have hsecond : Integrable jiangScaledTallGramSecondEnergy
      (jiangSqrtScaledTallHaarCornerLaw M K N) := by
    change Integrable
      (fun Z : Matrix (Fin K) (Fin N) Complex ↦
        (Matrix.trace ((Z.conjTranspose * Z) *
          (Z.conjTranspose * Z))).re)
      (jiangSqrtScaledTallHaarCornerLaw M K N)
    exact integrable_jiangSqrtScaledTallHaarCorner_gramSecondEnergy
      hNK hs.le
  have hsecondMean :
      (∫ Z, jiangScaledTallGramSecondEnergy Z
          ∂(jiangSqrtScaledTallHaarCornerLaw M K N)) =
        jiangTallSecondMomentValue M K N := by
    simpa only [jiangScaledTallGramSecondEnergy,
      jiangTallSecondMomentValue] using
      (integral_jiangSqrtScaledTallHaarCorner_gramSecondEnergy
        hM2 hN hNK hs.le)
  have hMpos : (0 : Real) < M := by
    exact_mod_cast (show 0 < M by omega)
  have hMone : (1 : Real) < M := by
    exact_mod_cast (show 1 < M by omega)
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN
  have hKreal : (1 : Real) ≤ K := by exact_mod_cast hK
  have hsRealKN : (K : Real) + N ≤ M := by exact_mod_cast hs.le
  have hsReal : (N : Real) + K ≤ M := by linarith
  have hsecondLower :
      (K : Real) * N *
          (((K : Real) + N) - ((K : Real) + N) ^ 2 / (2 * M)) ≤
        jiangTallSecondMomentValue M K N := by
    have h := haar_gram_second_moment_coarse_lower_h19
      (M := (M : Real)) (N := (N : Real)) (K := (K : Real))
      hMpos hMone hNreal hKreal hsReal
    simpa only [jiangTallSecondMomentValue] using (show
      (K : Real) * N *
          (((K : Real) + N) - ((K : Real) + N) ^ 2 / (2 * M)) ≤
        (N : Real) * K * M *
            ((M : Real) * ((N : Real) + K) - (N : Real) * K - 1) /
          ((M : Real) ^ 2 - 1) by
      convert h using 1 <;> ring)
  exact ⟨henergy, henergyMean, hsecond, hsecondMean, hsecondLower⟩

/-- Closed form of the manuscript's finite rectangular KL display in Jiang's
literal tall orientation. -/
theorem toReal_klDiv_jiangTall_le_three_quarters_A1A2A3A4
    {M K N : Nat} (hN : 0 < N) (hK : 0 < K)
    (hNK : N ≤ K) (hs : K + N < M) :
    (InformationTheory.klDiv
      (jiangSqrtScaledTallHaarCornerLaw M K N)
      (standardGaussianBlockLaw K N)).toReal ≤
      3 * ((K : Real) * N) * ((K : Real) + N) ^ 2 /
        (4 * (M : Real) ^ 2) := by
  have h := jiangTallMomentCertificate_proved hN hK hNK hs
  exact toReal_klDiv_jiangTall_le_three_quarters_of_moments
    hN hK hNK hs (jiangTallSecondMomentValue M K N)
    h.energy h.energyMean h.second h.secondMean h.secondLower

/-- Closed form of the rectangular block TV display, before transpose-Gram
data processing. -/
theorem jiangTall_probabilityTotalVariationLE_A1A2A3A4
    {M K N : Nat} (hN : 0 < N) (hK : 0 < K)
    (hNK : N ≤ K) (hs : K + N < M) :
    Sparse.probabilityTotalVariationLE
      (jiangSqrtScaledTallHaarCornerLaw M K N)
      (standardGaussianBlockLaw K N)
      (((K : Real) + N) * Real.sqrt ((K : Real) * N) / M) := by
  have h := jiangTallMomentCertificate_proved hN hK hNK hs
  exact jiangTall_probabilityTotalVariationLE_raw_of_moments
    hN hK hNK hs (jiangTallSecondMomentValue M K N)
    h.energy h.energyMean h.second h.secondMean h.secondLower

/-- Jiang's tall law is literally the canonical scaled Haar block law in the
same orientation. -/
theorem jiangSqrtScaledTallHaarCornerLaw_eq_canonicalBlock
    {M K N : Nat} (hM : 0 < M) (hKM : K ≤ M) (hNM : N ≤ M) :
    jiangSqrtScaledTallHaarCornerLaw M K N =
      sqrtScaledHaarBlockLaw canonicalUnitaryHaarProbabilityFamily M K N := by
  have hscale : Measurable
      (fun X : Matrix (Fin K) (Fin N) Complex ↦
        Real.sqrt (M : Real) • X) :=
    (rectangularSqrtScaleMeasurableEquiv M K N hM).measurable
  unfold jiangSqrtScaledTallHaarCornerLaw
    jiangUnscaledTallHaarCornerLaw sqrtScaledHaarBlockLaw
  rw [dif_pos ⟨hKM, hNM⟩, dif_pos ⟨hKM, hNM⟩]
  rw [Measure.map_map hscale
    (measurable_jiangUnscaledTallHaarCornerMatrix hKM hNM)]
  apply Measure.map_congr
  filter_upwards with U
  ext i j
  simp [Function.comp_def, jiangUnscaledTallHaarCornerMatrix,
    sqrtScaledHaarBlockMatrix]

/-- Exact manuscript KL statement for an arbitrary normalized Haar
presentation. -/
theorem toReal_klDiv_sqrtScaledHaarBlock_le_three_quarters_A1A2A3A4
    (H : UnitaryHaarProbabilityFamily) {M K N : Nat}
    (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K) (hs : K + N < M) :
    (InformationTheory.klDiv
      (sqrtScaledHaarBlockLaw H M K N)
    (standardGaussianBlockLaw K N)).toReal ≤
      3 * ((K : Real) * N) * ((K : Real) + N) ^ 2 /
        (4 * (M : Real) ^ 2) := by
  rw [sqrtScaledHaarBlockLaw_eq_canonical H M K N,
    ← jiangSqrtScaledTallHaarCornerLaw_eq_canonicalBlock
      (by omega) (by omega) (by omega)]
  exact toReal_klDiv_jiangTall_le_three_quarters_A1A2A3A4
    hN hK hNK hs

/-- Exact manuscript block-TV statement for an arbitrary normalized Haar
presentation. -/
theorem sqrtScaledHaarBlock_probabilityTotalVariationLE_A1A2A3A4
    (H : UnitaryHaarProbabilityFamily) {M K N : Nat}
    (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K) (hs : K + N < M) :
    Sparse.probabilityTotalVariationLE
      (sqrtScaledHaarBlockLaw H M K N)
      (standardGaussianBlockLaw K N)
      (((K : Real) + N) * Real.sqrt ((K : Real) * N) / M) := by
  rw [sqrtScaledHaarBlockLaw_eq_canonical H M K N,
    ← jiangSqrtScaledTallHaarCornerLaw_eq_canonicalBlock
      (by omega) (by omega) (by omega)]
  exact jiangTall_probabilityTotalVariationLE_A1A2A3A4 hN hK hNK hs

/-- The normalized transpose-Gram consequence of the fully proved raw-density
rectangular estimate. -/
theorem normalizedTransposeGram_probabilityTotalVariationLE_sparse_A1A2A3A4
    (H : UnitaryHaarProbabilityFamily) {M N K : Nat}
    (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K) (hs : K + N < M) :
    LocalAnticoncentration.probabilityTotalVariationLE
      (normalizedHaarTransposeGramLaw H M N K)
      (normalizedGaussianTransposeGramLaw N K)
      (((K : Real) + N) * Real.sqrt ((K : Real) * N) / M) := by
  have hraw := rawDensityTransposeGramQuantitative_proved
    H M N K hN hK hNK hs
  unfold normalizedHaarTransposeGramLaw normalizedGaussianTransposeGramLaw
  exact hraw.map (measurable_normalizeTransposeGram N K)

/-- Exact normalized sparse stitch at the manuscript cutoff `K < 16 N` and
large-ambient threshold `24 N^2 <= M`. -/
theorem normalizedSparseStitchTVLE_68_A1A2A3A4
    (H : UnitaryHaarProbabilityFamily) {M N K : Nat}
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKM : K ≤ M)
    (hlarge : 24 * N ^ 2 ≤ M) (hsparse : K < 16 * N) :
    LocalAnticoncentration.probabilityTotalVariationLE
      (normalizedHaarTransposeGramLaw H M N K)
      (normalizedGaussianTransposeGramLaw N K)
      (68 * (N : Real) ^ 2 / M) := by
  have hNpos : 0 < N := by omega
  have hKpos : 0 < K := hNpos.trans_le hNK
  have hstrict : K + N < M := by
    have hNN : N ≤ N ^ 2 := by nlinarith
    calc
      K + N < 16 * N + N := Nat.add_lt_add_right hsparse N
      _ = 17 * N := by omega
      _ ≤ 17 * N ^ 2 := Nat.mul_le_mul_left 17 hNN
      _ ≤ 24 * N ^ 2 := Nat.mul_le_mul_right (N ^ 2) (by omega)
      _ ≤ M := hlarge
  have htv :=
    normalizedTransposeGram_probabilityTotalVariationLE_sparse_A1A2A3A4
      H hNpos hKpos hNK hstrict
  apply htv.mono
  have hMpos : (0 : Real) < M := by exact_mod_cast (show 0 < M by omega)
  have hKupperNat : K ≤ 16 * N := Nat.le_of_lt hsparse
  have hKupper : (K : Real) ≤ (16 : Real) * N := by
    exact_mod_cast hKupperNat
  have hrate := rawDensity_sparse_rate_le_squared_rate_nat
    (N := (N : Real)) (K := (K : Real)) (M := (M : Real))
    (kappa := 16) (Nat.cast_nonneg N) hMpos hKupper
  rw [rawDensitySparseSquaredCoefficient_sixteen] at hrate
  simpa only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_one, mul_div_assoc] using hrate

/-! ## Ordered fixed-pattern panel -/

/-- Literal common-source ordered panel law for an arbitrary fixed family of
row embeddings, including overlap.  The Gaussian tuple is one deterministic
function of a single `L x K` Gaussian array, so no componentwise independence
is asserted. -/
theorem orderedFixedPatternPanelLaw_A1A2A3A4
    (H : UnitaryHaarProbabilityFamily)
    {q N L K M : Nat} (hL : 1 ≤ L) (hLK : L ≤ K) (hKM : K ≤ M)
    (rows : Fin q → (Fin N ↪ Fin L)) :
    LocalAnticoncentration.probabilityTotalVariationLE
      (Measure.map (orderedPatternPanel rows)
        (Measure.map
          (preselectedPrincipalSubmatrixTuple q L (orderedPatternSets rows))
          (normalizedHaarTransposeGramLaw H M L K)))
      (Measure.map
        (fun G j ↦ ThreePaper.DisjointGaussianRows.orderedNormalizedGram
          (K := K) (rows j) G)
        (standardComplexGaussianRectangularMeasure L K))
      (min 1 (615172 * ultimateSquaredHidingRate M L)) := by
  have hbase := jointPreselectedPatternLaw H M L K q hL hLK hKM
    (orderedPatternSets rows)
  have hpanel := hbase.map (measurable_orderedPatternPanel rows)
  rw [orderedGaussianPatternPanelLaw rows] at hpanel
  exact hpanel

#print axioms normalizedHaarTransposeGram_targetConvergence_A1A2A3A4
#print axioms concreteDenseSquaredLocalStepAt_615138_A1A2A3A4
#print axioms normalizedHaarTransposeGram_oneColumnTVLE_615138_A1A2A3A4
#print axioms concreteCanonicalDenseHidingSquaredConstant_eq_615138
#print axioms normalizedDenseProductHidingTVLE_615138_A1A2A3A4
#print axioms oneColumnParameterDictionary
#print axioms concreteOneColumnParameterLaw_eq_beta_prod_sphere
#print axioms concreteHaarOneColumnRecursion_eq_map_product_A1A2A3A4
#print axioms concreteHaarOneColumnRecursion_event_A1A2A3A4
#print axioms toReal_klDiv_jiangTall_le_three_quarters_A1A2A3A4
#print axioms jiangTall_probabilityTotalVariationLE_A1A2A3A4
#print axioms jiangSqrtScaledTallHaarCornerLaw_eq_canonicalBlock
#print axioms toReal_klDiv_sqrtScaledHaarBlock_le_three_quarters_A1A2A3A4
#print axioms sqrtScaledHaarBlock_probabilityTotalVariationLE_A1A2A3A4
#print axioms normalizedTransposeGram_probabilityTotalVariationLE_sparse_A1A2A3A4
#print axioms normalizedSparseStitchTVLE_68_A1A2A3A4
#print axioms orderedFixedPatternPanelLaw_A1A2A3A4

end

end LogdetLean.GramHafnian.ThreePaper.Verification

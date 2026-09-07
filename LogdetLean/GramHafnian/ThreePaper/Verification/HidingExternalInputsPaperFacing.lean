import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H5_FriedmanMelloA1Adapter
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_A2Prime_A1TraceTransport
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_A3_EdelmanSuttonProp12Conditional
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.MatsumotoTheorem3ProjectBridge
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19QuantitativeRawDensity
import Mathlib.Tactic

/-!
# Exact paper-facing forms of the four external-input displays

This module gives one kernel-checkable declaration for each equation label in
the external-input appendix which is genuinely represented by the existing
four scientific interfaces.  Definition-heavy displays are packaged together
with their normalization and notation dictionaries, so a bare check of a
nearby definition is not mistaken for verification of the whole display.

There is intentionally no theorem for the manuscript's pointwise
`sigma`-Jacobian display.  A2-prime assumes the measurable pushforward formula
in the squared variables; that formula does not logically recover a
pointwise coordinate Jacobian in the unsquared variables.  The cited
`sigma`-Jacobian must therefore remain an unnumbered literature derivation
unless it is deliberately added to the external scientific interface.
-/

open MeasureTheory
open scoped BigOperators ENNReal Matrix ComplexOrder ComplexConjugate

namespace LogdetLean.GramHafnian.ThreePaper.Verification

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.CurrentPRL
open LogdetLean.GramHafnian.UltimateHiding
open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.UltimateHiding.Sparse

/-! ## A1: Friedman--Mello density and the exact project dictionary -/

/-- All literal ingredients of the self-normalized A1 density display,
including the Haar pushforward statement imported from Friedman--Mello. -/
structure ExternalA1DensityEquation (n m : Nat) (h2mn : 2 * m ≤ n) : Prop where
  sourceLaw :
    Measure.map
        (fun U : Matrix.unitaryGroup (Fin n) Complex =>
          let S := FriedmanMelloA1.S U
          let s := FriedmanMelloA1.s (FriedmanMelloA1.dimensionLe h2mn) S
          s)
        (unitaryHaarProbabilityMeasure n) =
      FriedmanMelloA1.determinantDensityProbabilityMeasure n m
  supportLiteral :
    ∀ s : Matrix (Fin m) (Fin m) Complex,
      FriedmanMelloA1.support s ↔ (1 - s.conjTranspose * s).PosDef
  exponentLiteral :
    FriedmanMelloA1.densityExponent n m =
      ((n : Real) - 2 * (m : Real) - 1) / 2
  weightLiteral :
    ∀ x : ComplexSymmetricCoordinates m,
      FriedmanMelloA1.determinantWeight n m x =
        @ite ENNReal
          (FriedmanMelloA1.support
            (complexSymmetricMatrixOfCoordinates x))
          (Classical.propDecidable _)
          (ENNReal.ofReal <| Real.rpow
            (Matrix.det
              (1 - (complexSymmetricMatrixOfCoordinates x).conjTranspose *
                complexSymmetricMatrixOfCoordinates x)).re
            (FriedmanMelloA1.densityExponent n m))
          0
  rawMeasureLiteral :
    FriedmanMelloA1.rawDeterminantDensityMeasure n m =
      Measure.map (complexSymmetricMatrixOfCoordinates (N := m))
        ((complexSymmetricCoordinateVolume m).withDensity
          (FriedmanMelloA1.determinantWeight n m))
  normalizationLiteral :
    FriedmanMelloA1.determinantDensityProbabilityMeasure n m =
      ((FriedmanMelloA1.rawDeterminantDensityMeasure n m Set.univ)⁻¹) •
        FriedmanMelloA1.rawDeterminantDensityMeasure n m

/-- Exact bundled form of paper Eq. `external-A1`. -/
theorem eq_external_A1
    {n m : Nat} (hm : 1 ≤ m) (h2mn : 2 * m ≤ n) :
    ExternalA1DensityEquation n m h2mn := by
  refine
    { sourceLaw := FriedmanMelloA1.matrixLaw_external hm h2mn
      supportLiteral := ?_
      exponentLiteral := rfl
      weightLiteral := ?_
      rawMeasureLiteral := rfl
      normalizationLiteral := rfl }
  intro s
  rfl
  intro x
  rfl

/-- Every component of the paper dictionary `n=K`, `m=N`, `s=C_{N,K}`. -/
structure ExternalA1ProjectDictionary
    (N K : Nat) (h2NK : 2 * N ≤ K) : Prop where
  support : ∀ C : ConcreteMatrixState N,
    FriedmanMelloA1.support C ↔ coeCornerSupport C
  exponent : FriedmanMelloA1.densityExponent K N =
    coeCornerDensityExponent N K
  weight : FriedmanMelloA1.determinantWeight K N =
    coeCornerDeterminantWeight N K
  rawMeasure : FriedmanMelloA1.rawDeterminantDensityMeasure K N =
    coeCornerRawDeterminantDensityMeasure N K
  probabilityMeasure :
    FriedmanMelloA1.determinantDensityProbabilityMeasure K N =
      coeCornerDeterminantDensityProbabilityMeasure N K
  principalBlock : ∀ U : Matrix.unitaryGroup (Fin K) Complex,
    FriedmanMelloA1.s (FriedmanMelloA1.dimensionLe h2NK)
        (FriedmanMelloA1.S U) =
      unscaledCOECornerMatrix (FriedmanMelloA1.dimensionLe h2NK) U
  projectLaw :
    concreteUnscaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K =
      coeCornerDeterminantDensityProbabilityMeasure N K

/-- Exact bundled form of paper Eq. `external-A1-dictionary`. -/
theorem eq_external_A1_dictionary
    {N K : Nat} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    ExternalA1ProjectDictionary N K h2NK := by
  refine
    { support := friedmanMello1985_A1_support_s_eq_projectSupport_C
      exponent := friedmanMello1985_A1_exponent_m_eq_N_n_eq_K N K
      weight := friedmanMello1985_A1_weight_m_eq_N_n_eq_K N K
      rawMeasure := friedmanMello1985_A1_rawMeasure_m_eq_N_n_eq_K N K
      probabilityMeasure :=
        friedmanMello1985_A1_probabilityMeasure_m_eq_N_n_eq_K N K
      principalBlock := ?_
      projectLaw :=
        friedmanMello1985_unscaledCOECornerLaw_eq_determinantDensity_of_A1
          hN h2NK }
  intro U
  exact friedmanMello1985_A1_s_eq_C
    (FriedmanMelloA1.dimensionLe h2NK) U

/-! ## A2-prime: the exact measurable symmetric-test pushforward -/

/-- Exact fixed-test consequence of paper Eq. `external-A2prime`, including
one common positive orbit constant and spectrum measurability. -/
theorem eq_external_A2prime
    {N : Nat} (hN : 1 ≤ N)
    {gammaType : Type} [MeasurableSpace gammaType]
    (F : (Fin N -> Real) -> gammaType) (hF : Measurable F)
    (hSym : IsPermutationInvariantSpectralTest F) :
    ∃ cN : NNReal,
      0 < cN ∧
      Measurable (canonicalGapSquaredSpectrum N) ∧
      Measure.map (F ∘ canonicalGapSquaredSpectrum N)
          (complexSymmetricMatrixVolume N) =
        (cN : ENNReal) •
          Measure.map F (takagiFlatEigenvalueRadialMeasure N) := by
  let h := A2Prime_complexSymmetricTakagiWeyl_symmetricIntegration N hN
  exact ⟨h.orbitConstant, h.orbitConstant_pos, h.measurable_spectrum,
    h.symmetric_flat_radial_law F hF hSym⟩

/-! ## A3: beta-Jacobi density, unordered law, and project dictionary -/

/-- The exact normalized density content of paper Eq. `external-A3-jacobi`. -/
structure ExternalA3JacobiDensityEquation
    (n : Nat) (a b beta : Real) : Prop where
  kernelLiteral : ∀ lambda_i : Fin n -> Real,
    betaJacobiKernel n a b beta lambda_i =
      (∏ i,
          (ENNReal.ofReal (lambda_i i)).rpow
              (beta * (a + 1) / 2 - 1) *
          (ENNReal.ofReal (1 - lambda_i i)).rpow
              (beta * (b + 1) / 2 - 1)) *
        ∏ p ∈ a2StrictPairs n,
          (ENNReal.ofReal |lambda_i p.2 - lambda_i p.1|).rpow beta
  rawMeasureLiteral :
    betaJacobiRawMeasure n a b beta =
      (volume.restrict (betaJacobiOpenCube n)).withDensity
        (betaJacobiKernel n a b beta)
  normalizationLiteral :
    betaJacobiNormalization n a b beta =
      betaJacobiRawMeasure n a b beta Set.univ
  probabilityLiteral :
    betaJacobiProbabilityMeasure n a b beta =
      (betaJacobiNormalization n a b beta)⁻¹ •
        betaJacobiRawMeasure n a b beta

/-- Exact bundled form of paper Eq. `external-A3-jacobi`. -/
theorem eq_external_A3_jacobi (n : Nat) (a b beta : Real) :
    ExternalA3JacobiDensityEquation n a b beta := by
  exact ⟨fun _ => rfl, rfl, rfl, rfl⟩

/-- Exact symmetric-test law in paper Eq. `external-A3-symmetric-test`. -/
theorem eq_external_A3_symmetric_test
    {gammaType : Type} [MeasurableSpace gammaType]
    {n a b : Nat} {beta : Real}
    (hn : 1 ≤ n) (hbeta : beta = 1 ∨ beta = 2)
    (F : (Fin n -> Real) -> gammaType)
    (hF : Measurable F) (hSym : IsA2SymmetricTest F) :
    Measure.map
        (F ∘ edelmanSuttonSquaredGSVCoordinates n a b beta)
        (edelmanSuttonGaussianPairLaw n a b beta) =
      Measure.map F (betaJacobiProbabilityMeasure n (a : Real) (b : Real) beta) :=
  A3_edelmanSutton_unordered_symmetric_test hn hbeta F hF hSym

/-- Arithmetic and row-dimension consequences of the exact specialization
`n=N`, `a=1`, `b=K-2N`, `beta=1`. -/
structure ExternalA3ProjectDictionary (N K : Nat) : Prop where
  firstRows : N + 1 = N + 1
  secondRows : N + (K - 2 * N) = K - N
  aCast : (((1 : Nat) : Real)) = 1
  bCast : (((K - 2 * N : Nat) : Real)) = (K : Real) - 2 * (N : Real)
  betaValue : (1 : Real) = 1

/-- Exact bundled form of paper Eq. `external-A3-dictionary`. -/
theorem eq_external_A3_dictionary
    {N K : Nat} (h2NK : 2 * N ≤ K) :
    ExternalA3ProjectDictionary N K := by
  rcases H6_A3_literal_parameter_substitution h2NK with
    ⟨hrows, ha, hb⟩
  exact ⟨rfl, hrows, ha, hb, rfl⟩

/-! ## A4: Matsumoto's two equations and the project substitution -/

/-- Exact formalization of the two conditions displayed in
`external-A4-gap`.  They are hypotheses of A4, not conclusions of A4. -/
def ExternalA4Gap (d n : Nat) (beta gamma : Real) : Prop :=
  gamma = beta - ((d : Real) + 1) / 2 ∧ (n : Real) - 1 < gamma

theorem eq_external_A4_gap
    {d n : Nat} {beta gamma : Real}
    (hgamma : gamma = beta - ((d : Real) + 1) / 2)
    (hgap : (n : Real) - 1 < gamma) :
    ExternalA4Gap d n beta gamma :=
  ⟨hgamma, hgap⟩

/-- Definitional expansion of paper Eq. `external-A4-Tg`. -/
theorem eq_external_A4_Tg
    {d n : Nat} (g : Equiv.Perm (Fin (2 * n)))
    (x : MatsumotoPaper.RealMatrix d)
    (m : Fin n -> MatsumotoPaper.ComplexMatrix d) :
    MatsumotoPaper.T g x m =
      ∑ j : Fin (2 * n) -> Fin d,
        (∏ i : Fin n,
          m i (j (MatsumotoPaper.leftSlot i))
            (j (MatsumotoPaper.rightSlot i))) *
        ∏ i : Fin n,
          (((x (j (g (MatsumotoPaper.leftSlot i)))
              (j (g (MatsumotoPaper.rightSlot i))) : Real) : Complex)) := by
  rfl

/-- Exact direct-moment half of paper Eq. `external-A4-direct`. -/
theorem eq_external_A4_direct
    (d n : Nat) (beta gamma : Real)
    (hd : 0 < d) (hn : 0 < n)
    (sigma : MatsumotoPaper.SymPosDef d)
    (W : MatsumotoPaper.W_d d beta sigma)
    (hgamma : gamma = beta - ((d : Real) + 1) / 2)
    (hgap : (n : Real) - 1 < gamma)
    (m : Fin n -> MatsumotoPaper.ComplexMatrix d)
    (g : Equiv.Perm (Fin (2 * n))) :
    MatsumotoPaper.expectation W (fun w => MatsumotoPaper.T g w.1 m) =
      (2 : Complex) ^ (-(n : Int)) *
        ∑ matching : MatsumotoPaper.PerfectMatching n,
          (((2 * beta) ^ MatsumotoPaper.kappa
              (g⁻¹ * matching.toPerm) : Real) : Complex) *
            MatsumotoPaper.T matching.toPerm sigma.1 m :=
  (MatsumotoPaper.A4_matsumoto_theorem_3 d n beta gamma hd hn sigma W
    hgamma hgap m g).1

/-- Exact inverse-moment half of paper Eq. `external-A4-inverse`. -/
theorem eq_external_A4_inverse
    (d n : Nat) (beta gamma : Real)
    (hd : 0 < d) (hn : 0 < n)
    (sigma : MatsumotoPaper.SymPosDef d)
    (W : MatsumotoPaper.W_d d beta sigma)
    (hgamma : gamma = beta - ((d : Real) + 1) / 2)
    (hgap : (n : Real) - 1 < gamma)
    (m : Fin n -> MatsumotoPaper.ComplexMatrix d)
    (g : Equiv.Perm (Fin (2 * n))) :
    MatsumotoPaper.expectation W
        (fun w => MatsumotoPaper.T g (MatsumotoPaper.SymPosDef.inverse w).1 m) =
      ∑ matching : MatsumotoPaper.PerfectMatching n,
        MatsumotoPaper.wgTilde (g⁻¹ * matching.toPerm) gamma *
          MatsumotoPaper.T matching.toPerm
            (MatsumotoPaper.SymPosDef.inverse sigma).1 m :=
  (MatsumotoPaper.A4_matsumoto_theorem_3 d n beta gamma hd hn sigma W
    hgamma hgap m g).2

/-- Exact arithmetic content of the paper substitution
`d=N`, `k=K-N`, `beta=k/2`, `gamma=(K-2N-1)/2`. -/
structure ExternalA4ProjectDictionary (N K : Nat) : Prop where
  kCast : (((K - N : Nat) : Real)) = (K : Real) - (N : Real)
  beta : halfGaussianMatsumotoBeta (K - N) =
    ((K : Real) - (N : Real)) / 2
  gamma : halfGaussianMatsumotoGamma N (K - N) =
    ((K : Real) - 2 * (N : Real) - 1) / 2

/-- Exact bundled form of paper Eq. `external-A4-dictionary`. -/
theorem eq_external_A4_dictionary
    {N K : Nat} (hNK : N ≤ K) :
    ExternalA4ProjectDictionary N K := by
  have hk : (((K - N : Nat) : Real)) = (K : Real) - (N : Real) := by
    rw [Nat.cast_sub hNK]
  refine ⟨hk, ?_, ?_⟩
  · unfold halfGaussianMatsumotoBeta
    rw [hk]
  · unfold halfGaussianMatsumotoGamma halfGaussianMatsumotoBeta
    rw [hk]
    ring

/-! ## Rectangular RN derivative: foundations-only exact wrapper -/

/-- The literal real function printed in `rectangular-rn-density`, in Jiang's
native tall orientation.  The support is written non-strictly here; in the
strict-size range the boundary power is zero, so it agrees almost everywhere
with the manuscript's strict indicator. -/
def rectangularRNFormula (M K N : Nat)
    (Z : Matrix (Fin K) (Fin N) Complex) : Real := by
  classical
  exact (∏ i : Fin N × Fin K,
        (1 - rectangularNormalizedIndex K N M i)) *
      Real.exp (Matrix.trace (Z.conjTranspose * Z)).re *
      if jiangUnscaledTallHaarCornerSupport
          ((Real.sqrt (M : Real))⁻¹ • Z) then
        (Matrix.det
          (1 - ((((M : Real)⁻¹ : Real) : Complex)) •
            (Z.conjTranspose * Z))).re ^ (M - K - N)
      else 0

/-- The manuscript's literal strict-support version of the same formula. -/
def rectangularRNFormulaStrict (M K N : Nat)
    (Z : Matrix (Fin K) (Fin N) Complex) : Real := by
  classical
  exact (∏ i : Fin N × Fin K,
        (1 - rectangularNormalizedIndex K N M i)) *
      Real.exp (Matrix.trace (Z.conjTranspose * Z)).re *
      if (1 - ((((M : Real)⁻¹ : Real) : Complex)) •
          (Z.conjTranspose * Z)).PosDef then
        (Matrix.det
          (1 - ((((M : Real)⁻¹ : Real) : Complex)) •
            (Z.conjTranspose * Z))).re ^ (M - K - N)
      else 0

/-- In the strict-size regime the non-strict Jiang support and the strict
indicator give the same displayed density pointwise: on the boundary the
positive determinant power vanishes. -/
theorem rectangularRNFormula_eq_strict
    {M K N : Nat} (hs : K + N < M)
    (Z : Matrix (Fin K) (Fin N) Complex) :
    rectangularRNFormula M K N Z =
      rectangularRNFormulaStrict M K N Z := by
  classical
  have hMnat : 0 < M := by omega
  have hgram := conjTranspose_invSqrt_smul_mul_self hMnat Z
  let D : Matrix (Fin N) (Fin N) Complex :=
    1 - ((((M : Real)⁻¹ : Real) : Complex)) • (Z.conjTranspose * Z)
  by_cases hsupport : jiangUnscaledTallHaarCornerSupport
      ((Real.sqrt (M : Real))⁻¹ • Z)
  · have hPSD : D.PosSemidef := by
      have h :=
        (jiangUnscaledTallHaarCornerSupport_iff_posSemidef _).mp hsupport
      rw [hgram] at h
      simpa only [D] using h
    by_cases hdet : Matrix.det D = 0
    · have hnPD : ¬D.PosDef := by
        intro hPD
        exact (hPSD.posDef_iff_det_ne_zero.mp hPD) hdet
      have hc : M - K - N ≠ 0 := Nat.ne_of_gt (by omega)
      unfold rectangularRNFormula rectangularRNFormulaStrict
      rw [if_pos hsupport, if_neg hnPD]
      have hdet' : Matrix.det
          (1 - ((((M : Real)⁻¹ : Real) : Complex)) •
            (Z.conjTranspose * Z)) = 0 := by
        simpa only [D] using hdet
      rw [hdet']
      simp [hc]
    · have hPD : D.PosDef := hPSD.posDef_iff_det_ne_zero.mpr hdet
      unfold rectangularRNFormula rectangularRNFormulaStrict
      rw [if_pos hsupport, if_pos hPD]
  · have hnPD : ¬D.PosDef := by
      intro hPD
      apply hsupport
      apply (jiangUnscaledTallHaarCornerSupport_iff_posSemidef _).mpr
      rw [hgram]
      simpa only [D] using hPD.posSemidef
    unfold rectangularRNFormula rectangularRNFormulaStrict
    rw [if_neg hsupport, if_neg hnPD]

/-- Pointwise identification of the ratio of the two explicit real densities
with the displayed rectangular RN formula. -/
theorem jiangRealDensity_div_gaussian_eq_rectangularRNFormula
    {M K N : Nat} (hN : 0 < N) (hK : 0 < K) (hs : K + N ≤ M)
    (Z : Matrix (Fin K) (Fin N) Complex) :
    jiangSqrtScaledTallHaarCornerRealPDF M K N Z /
        standardComplexGaussianTallRealPDF K N Z =
      rectangularRNFormula M K N Z := by
  classical
  have hMnat : 0 < M := by omega
  have hpi : Real.pi ^ (K * N) ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hexp : Real.exp (-(Matrix.trace (Z.conjTranspose * Z)).re) ≠ 0 :=
    Real.exp_ne_zero _
  have hgram := conjTranspose_invSqrt_smul_mul_self hMnat Z
  by_cases hsupport : jiangUnscaledTallHaarCornerSupport
      ((Real.sqrt (M : Real))⁻¹ • Z)
  · unfold jiangSqrtScaledTallHaarCornerRealPDF
      standardComplexGaussianTallRealPDF rectangularRNFormula
    rw [if_pos hsupport, if_pos hsupport, hgram]
    rw [show (∏ i : Fin N × Fin K,
          (1 - rectangularNormalizedIndex K N M i)) =
        ((M : Real)⁻¹) ^ (K * N) *
          jiangUnscaledTallHaarCornerNormalizer M K N *
            Real.pi ^ (K * N) by
      rw [← jiangScaledTallNormalizerRatio_eq_rectangularProduct hN hK hs]
      rfl]
    field_simp [hpi, hexp]
    rw [mul_assoc, ← Real.exp_add]
    simp
  · unfold jiangSqrtScaledTallHaarCornerRealPDF rectangularRNFormula
    rw [if_neg hsupport, if_neg hsupport]
    simp

/-- RN derivative of the internally proved strict-size Haar corner law with
respect to the standard Gaussian law, equal almost everywhere (under the
Gaussian reference) to the exact displayed real formula. -/
theorem eq_rectangular_rn_density_ae
    {M K N : Nat} (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K)
    (hs : K + N < M) :
    (jiangSqrtScaledTallHaarCornerLaw M K N).rnDeriv
      (standardGaussianBlockLaw K N) =ᵐ[
          standardGaussianBlockLaw K N]
      (fun Z => ENNReal.ofReal (rectangularRNFormulaStrict M K N Z)) := by
  rw [jiangSqrtScaledTallHaarCornerLaw_eq_withDensity_ofReal_proved_strict
      hN hK hNK hs,
    standardGaussianBlockLaw_eq_withDensity_ofReal_H19 K N]
  let lambda := complexRectangularLebesgueVolume K N
  let f := jiangSqrtScaledTallHaarCornerRealPDF M K N
  let g := standardComplexGaussianTallRealPDF K N
  have hgpos : ∀ Z, 0 < g Z := by
    intro Z
    unfold g standardComplexGaussianTallRealPDF
    exact mul_pos (inv_pos.mpr (pow_pos Real.pi_pos _)) (Real.exp_pos _)
  have hgnezero : ∀ᵐ Z ∂lambda, ENNReal.ofReal (g Z) ≠ 0 :=
    ae_of_all lambda fun Z => ENNReal.ofReal_ne_zero_iff.mpr (hgpos Z)
  have hgnetop : ∀ᵐ Z ∂lambda, ENNReal.ofReal (g Z) ≠ ∞ :=
    ae_of_all lambda fun _ => ENNReal.ofReal_ne_top
  have hright := Measure.rnDeriv_withDensity_right
    (lambda.withDensity (fun Z => ENNReal.ofReal (f Z))) lambda
    (measurable_standardComplexGaussianTallRealPDF K N).ennreal_ofReal.aemeasurable
    hgnezero hgnetop
  have hleft := Measure.rnDeriv_withDensity lambda
    (measurable_jiangSqrtScaledTallHaarCornerRealPDF M K N).ennreal_ofReal
  have hbase :
      (lambda.withDensity (fun Z => ENNReal.ofReal (f Z))).rnDeriv
          (lambda.withDensity (fun Z => ENNReal.ofReal (g Z))) =ᵐ[lambda]
        (fun Z => ENNReal.ofReal (f Z / g Z)) := by
    dsimp only [f, g]
    filter_upwards [hright, hleft] with Z hR hL
    rw [hR, hL, ENNReal.ofReal_div_of_pos (hgpos Z)]
    simp only [g, div_eq_mul_inv, mul_comm]
  have href : lambda.withDensity (fun Z => ENNReal.ofReal (g Z)) ≪ lambda :=
    withDensity_absolutelyContinuous lambda _
  apply href.ae_eq
  filter_upwards [hbase] with Z hZ
  rw [hZ, jiangRealDensity_div_gaussian_eq_rectangularRNFormula
    hN hK hs.le Z, rectangularRNFormula_eq_strict hs Z]

#print axioms eq_external_A1
#print axioms eq_external_A1_dictionary
#print axioms eq_external_A2prime
#print axioms eq_external_A3_jacobi
#print axioms eq_external_A3_symmetric_test
#print axioms eq_external_A3_dictionary
#print axioms eq_external_A4_gap
#print axioms eq_external_A4_Tg
#print axioms eq_external_A4_direct
#print axioms eq_external_A4_inverse
#print axioms eq_external_A4_dictionary
#print axioms rectangularRNFormula_eq_strict
#print axioms jiangRealDensity_div_gaussian_eq_rectangularRNFormula
#print axioms eq_rectangular_rn_density_ae

end

end LogdetLean.GramHafnian.ThreePaper.Verification

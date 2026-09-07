import LogdetLean.GramHafnian.UltimateHiding.Dense.H1_RowGramOrbit

/-!
# Identification of invariant row-matrix laws from a Gram-matching coupling

This is a general compact-orbit argument.  Two right-unitarily invariant
probability laws are equal whenever they admit a measurable coupling whose
Hermitian row Grams agree almost surely.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

local instance matrixBorelSpaceH1OrbitIdentification (N m : ℕ) :
    BorelSpace (Matrix (Fin N) (Fin m) ℂ) := by
  exact inferInstanceAs (BorelSpace (Fin N → Fin m → ℂ))

local instance matrixSecondCountableTopologyH1OrbitIdentification
    (N m : ℕ) :
    SecondCountableTopology (Matrix (Fin N) (Fin m) ℂ) := by
  exact inferInstanceAs
    (SecondCountableTopology (Fin N → Fin m → ℂ))

/-- Right-unitary invariant rectangular-matrix probability laws are
identified by an almost-surely Gram-matching coupling. -/
theorem rightUnitaryInvariant_map_eq_of_ae_hermitianRowGram_eq
    {Omega : Type*} [MeasurableSpace Omega]
    {N m : ℕ} (rho : Measure Omega) [IsProbabilityMeasure rho]
    (X Y : Omega → Matrix (Fin N) (Fin m) ℂ)
    (hX : Measurable X) (hY : Measurable Y)
    (hinvX : ∀ V : Matrix.unitaryGroup (Fin m) ℂ,
      Measure.map (h1RightUnitaryAction (N := N) V)
          (Measure.map X rho) = Measure.map X rho)
    (hinvY : ∀ V : Matrix.unitaryGroup (Fin m) ℂ,
      Measure.map (h1RightUnitaryAction (N := N) V)
          (Measure.map Y rho) = Measure.map Y rho)
    (hgram : ∀ᵐ omega ∂rho,
      X omega * (X omega).conjTranspose =
        Y omega * (Y omega).conjTranspose) :
    Measure.map X rho = Measure.map Y rho := by
  let muX : Measure (Matrix (Fin N) (Fin m) ℂ) := Measure.map X rho
  let muY : Measure (Matrix (Fin N) (Fin m) ℂ) := Measure.map Y rho
  letI : IsProbabilityMeasure muX :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  letI : IsProbabilityMeasure muY :=
    Measure.isProbabilityMeasure_map hY.aemeasurable
  change muX = muY
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have havgX : (∫ Z, f Z ∂muX) =
      ∫ Z, h1RowOrbitAverage f Z ∂muX :=
    integral_eq_h1RowOrbitAverage_of_invariant muX hinvX f
  have havgY : (∫ Z, f Z ∂muY) =
      ∫ Z, h1RowOrbitAverage f Z ∂muY :=
    integral_eq_h1RowOrbitAverage_of_invariant muY hinvY f
  rw [havgX, havgY]
  change (∫ Z, h1RowOrbitAverage f Z ∂Measure.map X rho) =
    ∫ Z, h1RowOrbitAverage f Z ∂Measure.map Y rho
  rw [integral_map hX.aemeasurable
      (measurable_h1RowOrbitAverage f).aestronglyMeasurable,
    integral_map hY.aemeasurable
      (measurable_h1RowOrbitAverage f).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hgram] with omega homega
  exact h1RowOrbitAverage_eq_of_hermitianRowGram_eq
    f (X omega) (Y omega) homega

end

end LogdetLean.GramHafnian.UltimateHiding.Dense

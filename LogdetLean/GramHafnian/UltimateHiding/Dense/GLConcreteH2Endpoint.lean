import LogdetLean.GramHafnian.UltimateHiding.Dense.ConcreteGLFactorActions
import LogdetLean.GramHafnian.UltimateHiding.Dense.HaarAmbientGLInvariant

/-!
# Concrete H2 from the internal finite-measure `GL_N(C)/U(N)` theorem

This module specializes the general Gelfand-pair measure-action theorem to
the centered orbital factor, the beta/sphere one-column factor, and the
canonical Haar transpose-Gram input law.  Its non-foundational inputs are the
general finite-measure Gelfand-pair commutativity theorem and invariance of
uniform complex-sphere measure under unitary rotations; both are now proved
internally.  No scientific axiom or concrete commutation equality is
postulated.
-/

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

open CurrentPRL

theorem glComplex_unitary_oneColumn_orbital_commutation_from_gelfand
    (N K m : ℕ) (s : ℝ)
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKm : K ≤ m) :
    concreteOrbitalMatrixKernel N s ∘ₘ
        (concreteOneColumnMatrixKernel m N ∘ₘ
          concreteHaarAmbientLaw canonicalUnitaryHaarProbabilityFamily N K m) =
      concreteOneColumnMatrixKernel m N ∘ₘ
        (concreteOrbitalMatrixKernel N s ∘ₘ
          concreteHaarAmbientLaw canonicalUnitaryHaarProbabilityFamily N K m) := by
  have hNm : N ≤ m := hNK.trans hKm
  letI : IsProbabilityMeasure (concreteOrbitalGLFactorLaw N s) :=
    concreteOrbitalGLFactorLaw_isProbability hN s
  letI : IsProbabilityMeasure (concreteOneColumnGLFactorLaw m N) :=
    concreteOneColumnGLFactorLaw_isProbability hN hNm
  letI : IsMarkovKernel (concreteOrbitalMatrixKernel N s) :=
    concreteOrbitalMatrixKernel_isMarkov hN s
  letI : IsMarkovKernel (concreteOneColumnMatrixKernel m N) :=
    concreteOneColumnMatrixKernel_isMarkov hN hNm
  letI : IsProbabilityMeasure
      (concreteHaarAmbientLaw canonicalUnitaryHaarProbabilityFamily N K m) :=
    concreteHaarAmbientLaw_isProbability_internal
      canonicalUnitaryHaarProbabilityFamily hNK hKm
  have hcomm := congruenceMeasureActions_commute_of_unitary_invariant
    (concreteOrbitalGLFactorLaw N s)
    (concreteOneColumnGLFactorLaw m N)
    (concreteHaarAmbientLaw canonicalUnitaryHaarProbabilityFamily N K m)
    (concreteHaarAmbientLaw_isUnitaryCongruenceInvariant
      canonicalUnitaryHaarProbabilityFamily hNK hKm)
    (concreteOrbitalGLFactorLaw_preservesUnitaryCongruenceInvariant hN s)
    (concreteOneColumnGLFactorLaw_preservesUnitaryCongruenceInvariant hN hNm)
  simpa only [congruenceMeasureAction_concreteOrbitalGLFactorLaw hN s,
    congruenceMeasureAction_concreteOneColumnGLFactorLaw hN hNm] using hcomm

end


end LogdetLean.GramHafnian.UltimateHiding.Dense

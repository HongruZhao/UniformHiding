import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_CanonicalGapWeylReduction

/-!
# A2-prime: symmetric-test complex-symmetric Takagi--Weyl formula

This module contains only the user-approved replacement literature atom A2'.
It is the invariant (symmetric-test) Weyl integration formula for flat
Lebesgue measure on complex symmetric matrices.  It mentions no COE
determinant weight, project dimension `K`, A1, A3, Wishart source, trace
statistic, or H6 endpoint.

On the regular Weyl chamber, the Takagi singular values satisfy

`sigma_1 > ... > sigma_N > 0`,

the classical Jacobian is, up to a positive dimension-dependent orbit
constant,

`prod_i sigma_i * prod_{i<j} |sigma_i^2 - sigma_j^2|`.

After the substitution `lambda_i = sigma_i^2`, the factors `sigma_i` cancel
against `d lambda_i = 2 sigma_i d sigma_i`.  Thus the flat squared-coordinate
density is `|Delta(lambda)|`.  A canonical eigenvalue routine chooses one
ordering, whereas `takagiFlatEigenvalueRadialMeasure` is on the full positive
orthant.  The invariant statement below therefore tests only
permutation-invariant maps; the finite permutation multiplicity is absorbed
into the unspecified positive orbit constant.

Primary literature provenance:

* S. Helgason, *Groups and Geometric Analysis*, AMS Mathematical Surveys and
  Monographs 83 (2000), Chapter I, Theorem 5.17, gives the tangent-space Weyl
  integration formula.  Applied to `Sp(N,R)/U(N)`, whose tangent space is
  identified with complex symmetric matrices under unitary congruence, its
  restricted-root Jacobian is the product displayed above.  Helgason states the
  formula on compactly supported continuous tests.  Equality on those tests
  identifies the corresponding Radon measures, hence gives the measurable
  pushforward formulation used below.
* R. C. Chen, Y. H. Kim, J. D. Lichtman, S. J. Miller, S. Sweitzer, and
  E. Winsor, *Spectral Statistics of Non-Hermitian Random Matrix Ensembles*,
  Random Matrices: Theory and Applications 8 (2019), 1950005,
  doi:10.1142/S2010326319500059, Appendix A.2, equations (A.15)--(A.16),
  calculate the complex-symmetric Takagi coordinate scaling factors directly;
  equations (A.19)--(A.20) state the resulting positive factor
  `prod_{j<k} |sigma_k^2-sigma_j^2| * prod_j |2 sigma_j|`.  Equation (A.17)
  has an apparent inversion typo in its printed final equality, so it is not
  used here to choose the orientation of the Jacobian.

Thus Helgason supports the unrestricted Lebesgue integration formula, while
Chen et al. corroborate the exact Takagi-coordinate factors used here.  A2' is
not the retired ensemble-specific axiom `A2_forrester_equation_1_7`: it states
only flat Takagi--Weyl radialization.
-/

open scoped ENNReal
open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-- A spectral test is invariant under every permutation of its coordinates.
This neutral definition is part of the transparent interface, not an axiom. -/
def IsPermutationInvariantSpectralTest {N : ℕ} {γ : Type}
    (F : (Fin N → ℝ) → γ) : Prop :=
  ∀ (sigma : Equiv.Perm (Fin N)) (lambda : Fin N → ℝ),
    F (lambda ∘ sigma) = F lambda

/-- The structure of the raw, invariant Takagi--Weyl integration formula.

The target type is any ordinary (`Type 0`) measurable space.  The equality is
the pushforward form of the Weyl formula and is deliberately restricted to
permutation-invariant tests, so it does not identify a canonical ordered
selector with the full unordered orthant. -/
structure TakagiWeylSymmetricIntegrationLaw (N : ℕ) where
  orbitConstant : NNReal
  orbitConstant_pos : 0 < orbitConstant
  measurable_spectrum : Measurable (canonicalGapSquaredSpectrum N)
  symmetric_flat_radial_law :
    ∀ {γ : Type} [MeasurableSpace γ]
      (F : (Fin N → ℝ) → γ),
      Measurable F →
      IsPermutationInvariantSpectralTest F →
      Measure.map (F ∘ canonicalGapSquaredSpectrum N)
          (complexSymmetricMatrixVolume N) =
        (orbitConstant : ℝ≥0∞) •
          Measure.map F (takagiFlatEigenvalueRadialMeasure N)

theorem TakagiWeylSymmetricIntegrationLaw.orbitConstant_ne_zero
    {N : ℕ} (h : TakagiWeylSymmetricIntegrationLaw N) :
    h.orbitConstant ≠ 0 :=
  ne_of_gt h.orbitConstant_pos

/-- **Approved literature atom A2'.**  Raw complex-symmetric Takagi--Weyl
integration for arbitrary measurable permutation-invariant spectral tests.

The axiom returns data rather than an existential proposition so its fields
can be used without eliminating a proposition into a data-valued contract.
-/
axiom A2Prime_complexSymmetricTakagiWeyl_symmetricIntegration
    (N : ℕ) (_hN : 1 ≤ N) :
    TakagiWeylSymmetricIntegrationLaw N

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

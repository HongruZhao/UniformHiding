import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_CanonicalGapWeylReduction

/-!
# A2: symmetric-test complex-symmetric Takagi--Weyl formula

This module contains only the literature input A2. The historical filename
and declaration retain `A2Prime` for source compatibility.
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

Primary literature provenance, revised 2026-09-07:

* W. FitzGerald and J. Warren, *Point-to-line last passage percolation and
  the invariant measure of a system of reflecting Brownian motions*,
  Probability Theory and Related Fields 178 (2020), 121--171,
  doi:10.1007/s00440-020-00972-z, Section 6, printed page 165, the unnumbered
  Jacobian immediately after equation (70). It uses independent complex
  coordinates of a symmetric matrix and eigenvalues of its adjoint product,
  and gives exactly the flat squared-coordinate factor `|Delta(lambda)|`.
* J. An, Z. Wang, and K. Yan, *A generalization of random matrix ensemble I.
  General theory*, Pacific Journal of Mathematics 228 (2006), 1--17,
  doi:10.2140/pjm.2006.228.1, Theorem 4.2 and its following remark, printed
  page 13. The theorem gives orbit integration; the remark permits measurable
  integrands. Unitary congruence on complex symmetric matrices satisfies its
  hypotheses, as detailed in `docs/A2_SOURCE_DERIVATION.md`.

Integrating the compact angular variables gives the scalar formula for every
nonnegative measurable symmetric test, allowing infinite integrals. For any
measurable invariant `F` and measurable target set `B`, apply that formula to
the indicator of `F`'s inverse image of `B`. This yields the pushforward
identity below with one positive finite constant independent of `F` and its
target. Permutation multiplicity changes only that constant; for `N = 1`,
ordinary planar polar coordinates give the constant `pi`.

The other field, global measurability of `canonicalGapSquaredSpectrum`,
follows because `C |-> 1 - C.conjTranspose * C` is continuous on all square
complex matrices and ordered Hermitian eigenvalues are continuous, including
at multiplicities. The fixed coordinate reindexing in the eigenvalue routine
does not change this. The entries are squared singular values as a multiset;
permutation invariance removes the source/code ordering difference.

These deductions establish the mathematical implication from the cited
formula to every field of this contract; they are not separately formalized
here. The contract is a derived formulation, not a verbatim source theorem.
The revision changes only provenance comments, not the declaration, its
fields, or any proof term. No additional project axiom is introduced.
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

/-- **Literature input A2.** Raw complex-symmetric Takagi--Weyl
integration for arbitrary measurable permutation-invariant spectral tests.

The axiom returns data rather than an existential proposition so its fields
can be used without eliminating a proposition into a data-valued contract.
-/
axiom A2Prime_complexSymmetricTakagiWeyl_symmetricIntegration
    (N : ℕ) (_hN : 1 ≤ N) :
    TakagiWeylSymmetricIntegrationLaw N

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

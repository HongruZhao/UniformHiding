import LogdetLean.GramHafnian.UltimateHiding.Dense.GLConcreteH2Endpoint

/-!
# Audited Gelfand-pair input and concrete orbital propagation

On the full matrix state space, the radial and orbital kernels need not
commute pointwise.  The theorem used by the paper is weaker and exact: their
**measure actions** commute after acting on the unitary-congruence-invariant
Haar transpose-Gram law.  This file derives that concrete equality from a
general finite-measure Gelfand-pair convolution theorem and then proves the
arbitrary-ambient propagation internally.

## Source ledger

The general statement that finite `U(N)`-bi-invariant measures on `GL_N(C)`
commute under convolution is proved internally from the standard involution
criterion. This module uses its proved concrete specialization.

* M. Roesler and M. Voit, *Dunkl theory, convolution algebras, and related
  Markov processes*, Section 3.2, equation (3.2), Definition 3.1, and Lemma 3.2,
  https://math.uni-paderborn.de/fileadmin/mathematik/AG_Harmonische_Analysis/
  Publications_Roesler/roesler_voit_angers.pdf .  The bounded
  `U(N)`-bi-invariant measures form a convolution algebra, and for a Gelfand
  pair this algebra is commutative.
* A. B. J. Kuijlaars and P. Roman, *Spherical Functions Approach to Sums of
  Random Hermitian Matrices*, Int. Math. Res. Not. 2019, 1005--1029,
  Remark 1.2, https://doi.org/10.1093/imrn/rnx146 .  This identifies
  `(GL_N(C), U(N))` as the multiplicative Gelfand pair used for products of
  complex matrices.
* J. Faraut and A. Koranyi, *Analysis on Symmetric Cones*, Oxford University
  Press (1994), Chapters VI and XI,
  https://doi.org/10.1093/oso/9780198534778.001.0001 .  Polar decomposition
  identifies positive Hermitian matrices with the double-coset space and
  develops its spherical convolution.

For the one-column factor, the mixing matrix is positive and its distribution
is invariant under unitary conjugation because the direction is uniform on
the complex sphere.  The centered orbital factor has the fixed spectrum of
`exp(s(P_v-I/N))` and the same invariance.  Their measurable `GL_N(C)` lifts,
the conjugation-to-congruence adapter, and invariance of the Haar corner law
are all proved in the imported modules. The general Gelfand-pair theorem then
gives exactly the equality stated below.

No scientific atom is used, and no total-variation, score, differentiability,
moment, or hiding estimate is hidden in this step.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

open LocalAnticoncentration

/-- Measure-action commutation at one specified input law.  Unlike
`KernelsCommute`, this does not claim equality on every matrix state. -/
def KernelActionsCommuteAt
    {State : Type*} [MeasurableSpace State]
    (left right : Kernel State State) (mu : Measure State) : Prop :=
  left ∘ₘ (right ∘ₘ mu) = right ∘ₘ (left ∘ₘ mu)

/-- **Concrete spherical convolution identity at the canonical Haar
transpose-Gram law, derived from the internal Gelfand-pair theorem.**

For `1 <= N <= K <= m`, the centered orbital kernel and the next beta/sphere
radial increment commute after acting on `mu_(m,K)`.  This is precisely the
invariant-law conclusion of the `(GL_N(C),U(N))` Gelfand-pair theorem; it is
deliberately not stated as equality of the two kernels on arbitrary inputs.

The historical public name is retained so downstream paper-facing theorems do
not change, but this declaration is now a theorem rather than an axiom. -/
theorem glComplex_unitary_oneColumn_orbital_commutation_external
    (N K m : ℕ) (s : ℝ)
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKm : K ≤ m) :
    KernelActionsCommuteAt
      (concreteOrbitalMatrixKernel N s)
      (concreteOneColumnMatrixKernel m N)
      (concreteHaarAmbientLaw canonicalUnitaryHaarProbabilityFamily N K m) := by
  unfold KernelActionsCommuteAt
  exact glComplex_unitary_oneColumn_orbital_commutation_from_gelfand
    N K m s hN hNK hKm

/-- Canonical commutation transports to any presentation of normalized Haar
probability using the internally proved uniqueness of Haar measure. -/
theorem concreteHaar_oneColumn_orbital_commutation
    (H : UnitaryHaarProbabilityFamily) {N K m : ℕ} (s : ℝ)
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKm : K ≤ m) :
    KernelActionsCommuteAt
      (concreteOrbitalMatrixKernel N s)
      (concreteOneColumnMatrixKernel m N)
      (concreteHaarAmbientLaw H N K m) := by
  unfold KernelActionsCommuteAt
  rw [concreteHaarAmbientLaw_eq_canonical H N K m]
  exact glComplex_unitary_oneColumn_orbital_commutation_external
    N K m s hN hNK hKm

/-- One exact ambient step with the orbital averaging moved to the square-base
side of the new radial increment. -/
theorem concreteHaar_orbital_step_propagation
    (H : UnitaryHaarProbabilityFamily) {N K m : ℕ} (s : ℝ)
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKm : K ≤ m) :
    orbitalConvolution (concreteOrbitalMatrixKernel N s)
        (concreteHaarAmbientLaw H N K (m + 1)) =
      radialConvolution (concreteOneColumnMatrixKernel m N)
        (orbitalConvolution (concreteOrbitalMatrixKernel N s)
          (concreteHaarAmbientLaw H N K m)) := by
  rw [concreteHaarOneColumnRecursion_step_eq H hN hNK hKm]
  exact concreteHaar_oneColumn_orbital_commutation H s hN hNK hKm

/-- Offset form of full radial propagation: orbital averaging at ambient
dimension `K+r` equals the same finite radial chain applied after orbital
averaging of the square base law. -/
theorem concreteHaar_orbital_radialPropagation_offset
    (H : UnitaryHaarProbabilityFamily) {N K : ℕ}
    (s : ℝ) (hN : 1 ≤ N) (hNK : N ≤ K) : ∀ r,
    orbitalConvolution (concreteOrbitalMatrixKernel N s)
        (concreteHaarAmbientLaw H N K (K + r)) =
      radialConvolution (concreteRadialKernelChain N K r)
        (orbitalConvolution (concreteOrbitalMatrixKernel N s)
          (concreteHaarAmbientLaw H N K K)) := by
  intro r
  induction r with
  | zero =>
      simp [radialConvolution, orbitalConvolution]
  | succ r ihr =>
      calc
        orbitalConvolution (concreteOrbitalMatrixKernel N s)
            (concreteHaarAmbientLaw H N K (K + (r + 1))) =
          orbitalConvolution (concreteOrbitalMatrixKernel N s)
            (concreteHaarAmbientLaw H N K ((K + r) + 1)) := by
              congr 2
        _ = radialConvolution (concreteOneColumnMatrixKernel (K + r) N)
              (orbitalConvolution (concreteOrbitalMatrixKernel N s)
                (concreteHaarAmbientLaw H N K (K + r))) :=
            concreteHaar_orbital_step_propagation H s hN hNK (by omega)
        _ = radialConvolution (concreteOneColumnMatrixKernel (K + r) N)
              (radialConvolution (concreteRadialKernelChain N K r)
                (orbitalConvolution (concreteOrbitalMatrixKernel N s)
                  (concreteHaarAmbientLaw H N K K))) := by rw [ihr]
        _ = radialConvolution (concreteRadialKernelChain N K (r + 1))
              (orbitalConvolution (concreteOrbitalMatrixKernel N s)
                (concreteHaarAmbientLaw H N K K)) := by
            rw [concreteRadialKernelChain_succ]
            exact radialConvolution_assoc _ _ _

/-- Paper-facing arbitrary-ambient spherical commutation identity.  The radial
operator is the actual beta/sphere chain, the orbital operator is the actual
`Q_v` congruence average, and the base is the square Haar law. -/
theorem concreteHaar_orbital_radialPropagation
    (H : UnitaryHaarProbabilityFamily) {N K m : ℕ}
    (s : ℝ) (hN : 1 ≤ N) (hNK : N ≤ K) (hKm : K ≤ m) :
    orbitalConvolution (concreteOrbitalMatrixKernel N s)
        (concreteHaarAmbientLaw H N K m) =
      radialConvolution (concreteRadialKernelChain N K (m - K))
        (orbitalConvolution (concreteOrbitalMatrixKernel N s)
          (concreteHaarAmbientLaw H N K K)) := by
  have hsum : K + (m - K) = m := Nat.add_sub_of_le hKm
  simpa only [hsum] using
    (concreteHaar_orbital_radialPropagation_offset H s hN hNK (m - K))

/-- Equivalent displayed form: on the concrete square base law, the full
radial mixture and the orbital averaging commute as measure actions. -/
theorem concreteHaar_radial_orbital_commutation
    (H : UnitaryHaarProbabilityFamily) {N K m : ℕ}
    (s : ℝ) (hN : 1 ≤ N) (hNK : N ≤ K) (hKm : K ≤ m) :
    orbitalConvolution (concreteOrbitalMatrixKernel N s)
        (radialConvolution (concreteRadialKernelChain N K (m - K))
          (concreteHaarAmbientLaw H N K K)) =
      radialConvolution (concreteRadialKernelChain N K (m - K))
        (orbitalConvolution (concreteOrbitalMatrixKernel N s)
          (concreteHaarAmbientLaw H N K K)) := by
  rw [← concreteHaarAmbientLaw_radialFactorization H hN hNK hKm]
  exact concreteHaar_orbital_radialPropagation H s hN hNK hKm

/-- Score-proof-facing form of spherical commutation, with the input measure
named explicitly as the scaled COE-corner base.  This is the endpoint used to
move any subsequently justified finite-radius orbital derivative through the
entire rectangular radial mixture. -/
theorem concreteScaledCOE_radial_orbital_commutation
    (H : UnitaryHaarProbabilityFamily) {N K m : ℕ}
    (s : ℝ) (hN : 1 ≤ N) (hNK : N ≤ K) (hKm : K ≤ m) :
    orbitalConvolution (concreteOrbitalMatrixKernel N s)
        (radialConvolution (concreteRadialKernelChain N K (m - K))
          (concreteScaledCOECornerLaw H N K)) =
      radialConvolution (concreteRadialKernelChain N K (m - K))
        (orbitalConvolution (concreteOrbitalMatrixKernel N s)
          (concreteScaledCOECornerLaw H N K)) :=
  concreteHaar_radial_orbital_commutation H s hN hNK hKm

end

end LogdetLean.GramHafnian.UltimateHiding.Dense

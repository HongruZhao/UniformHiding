import LogdetLean.GramHafnian.UltimateHiding.Dense.OneColumnRecursion

/-!
# Radial convolution and the Gelfand pair interface

The dense proof factors a corner law into a square angular base followed by a
radial beta convolution.  Orbital rank one averaging commutes with this radial
convolution because both arise from bi-invariant convolution for the
`GL_N(ℂ) / U(N)` Gelfand pair.

Mathlib does not presently package that harmonic analytic theorem.  This file
therefore gives:

* the exact kernel and measure definitions;
* a deliberately strong, generic structure for situations where the kernels
  commute on the entire state space;
* all formal consequences of commutation, proved from kernel associativity.

No concrete commutation statement is postulated.  The actual Haar-corner
application is weaker: commutation holds after the kernels act on the
unitary-congruence-invariant law, not pointwise on arbitrary matrices.  It is
therefore implemented separately by `KernelActionsCommuteAt` in
`RadialGelfandExternal`, without constructing the strong interface below.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

/-- Action of a radial Markov kernel on a measure. -/
def radialConvolution
    {State : Type*} [MeasurableSpace State]
    (radial : Kernel State State) (mu : Measure State) : Measure State :=
  radial ∘ₘ mu

/-- Action of an orbital averaging kernel on a measure. -/
def orbitalConvolution
    {State : Type*} [MeasurableSpace State]
    (orbital : Kernel State State) (mu : Measure State) : Measure State :=
  orbital ∘ₘ mu

theorem radialConvolution_isProbability
    {State : Type*} [MeasurableSpace State]
    (radial : Kernel State State) (mu : Measure State)
    (hradial : IsMarkovKernel radial) (hmu : IsProbabilityMeasure mu) :
    IsProbabilityMeasure (radialConvolution radial mu) := by
  let _ : IsMarkovKernel radial := hradial
  let _ : IsProbabilityMeasure mu := hmu
  unfold radialConvolution
  infer_instance

/-- Algebraic kernel commutation. -/
def KernelsCommute
    {State : Type*} [MeasurableSpace State]
    (left right : Kernel State State) : Prop :=
  left ∘ₖ right = right ∘ₖ left

theorem KernelsCommute.symm
    {State : Type*} [MeasurableSpace State]
    {left right : Kernel State State}
    (h : KernelsCommute left right) : KernelsCommute right left :=
  Eq.symm h

theorem KernelsCommute.measure_actions
    {State : Type*} [MeasurableSpace State]
    {left right : Kernel State State}
    (h : KernelsCommute left right) (mu : Measure State) :
    left ∘ₘ (right ∘ₘ mu) = right ∘ₘ (left ∘ₘ mu) := by
  rw [Measure.comp_assoc, Measure.comp_assoc, h]

/-- A family-level interface for *global* kernel commutation.  This abstraction
is useful when pointwise commutation really holds.  It is intentionally not
instantiated by the concrete Haar transpose-Gram development, where the valid
Gelfand-pair conclusion is only an invariant-law measure equality. -/
structure GelfandPairCommutationInterface
    (State RadialIndex OrbitalIndex : Type*)
    [MeasurableSpace State] where
  radialKernel : RadialIndex → Kernel State State
  orbitalKernel : OrbitalIndex → Kernel State State
  radialIsMarkov : ∀ r, IsMarkovKernel (radialKernel r)
  orbitalIsMarkov : ∀ o, IsMarkovKernel (orbitalKernel o)
  commutes : ∀ r o, KernelsCommute (radialKernel r) (orbitalKernel o)

theorem GelfandPairCommutationInterface.convolve_commute
    {State RadialIndex OrbitalIndex : Type*}
    [MeasurableSpace State]
    (system : GelfandPairCommutationInterface State RadialIndex OrbitalIndex)
    (r : RadialIndex) (o : OrbitalIndex) (mu : Measure State) :
    radialConvolution (system.radialKernel r)
        (orbitalConvolution (system.orbitalKernel o) mu) =
      orbitalConvolution (system.orbitalKernel o)
        (radialConvolution (system.radialKernel r) mu) := by
  exact (system.commutes r o).measure_actions mu

/-- A family of laws is obtained from a common angular base by radial
convolution. -/
def RadialFactorization
    {State Index : Type*} [MeasurableSpace State]
    (base : Measure State) (law : Index → Measure State)
    (radial : Index → Kernel State State) : Prop :=
  ∀ i, law i = radialConvolution (radial i) base

/-- Orbital averaging may be moved through a radial factorization whenever the
two kernels commute.  This is the formal propagation step used to transfer
score estimates from the square angular base to every rectangular corner. -/
theorem RadialFactorization.orbital_propagation
    {State Index OrbitalIndex : Type*} [MeasurableSpace State]
    {base : Measure State} {law : Index → Measure State}
    {radial : Index → Kernel State State}
    (hfactor : RadialFactorization base law radial)
    (orbital : OrbitalIndex → Kernel State State)
    (hcomm : ∀ i o, KernelsCommute (radial i) (orbital o))
    (i : Index) (o : OrbitalIndex) :
    orbitalConvolution (orbital o) (law i) =
      radialConvolution (radial i) (orbitalConvolution (orbital o) base) := by
  rw [hfactor i]
  exact ((hcomm i o).measure_actions base).symm

/-- Two radial layers combine into their composed kernel. -/
theorem radialConvolution_assoc
    {State : Type*} [MeasurableSpace State]
    (outer inner : Kernel State State) (mu : Measure State) :
    radialConvolution outer (radialConvolution inner mu) =
      radialConvolution (outer ∘ₖ inner) mu := by
  exact Measure.comp_assoc

end

end LogdetLean.GramHafnian.UltimateHiding.Dense

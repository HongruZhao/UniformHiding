import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16CenteredWeakGeneratorInterface
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16L1Transport

/-!
# H16 centered order-four zero extension in `L1`: exact interface

This module is the final corrected interface requested for
`coeCenteredTransport_orderFour_zeroExtension`.  The derivative chain is
entirely in `L1(complexSymmetricCoordinateVolume N)`.  No field asserts a
pointwise fourth derivative at moving-boundary times, and no field asks for a
fixed ambient pointwise dominator of the moving fourth-order singularity.

The intended future theorem has the exact type

```lean
theorem coeCenteredTransport_orderFour_zeroExtension
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K) :
    COECenteredOrderFourZeroExtensionFacts N K hN hboundary := by
  ...
```

It must be proved from the scalar, Gauss--Green/weak-generator, and Bochner
layers.  It is not declared here because this lightweight checkpoint contains
no unverified theorem, axiom, or placeholder proof.
-/

open MeasureTheory Filter
open scoped ENNReal Topology ContDiff

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Corrected order-four zero-extension facts for the literal centered COE
coordinate density.  The `jetLp` field chooses the `L1` classes represented by
the globally measurable jets from the weak-generator layer. -/
structure COECenteredOrderFourZeroExtensionFacts
    (N K : ℕ) (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K) : Type where
  weak : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary
  jetLp :
    Fin 5 → ComplexUnitSphere N → ℝ →
      (ComplexSymmetricCoordinates N →₁[
        complexSymmetricCoordinateVolume N] ℝ)
  jetLp_coeFn_ae :
    ∀ (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ),
      (fun x ↦ jetLp r v t x) =ᵐ[
          complexSymmetricCoordinateVolume N]
        h16CenteredTransportJet N K r v t
  jetLp_joint_continuous :
    ∀ r : Fin 5,
      Continuous (fun p : ComplexUnitSphere N × ℝ ↦
        jetLp r p.1 p.2)
  jetLp_derivative_chain :
    ∀ (r : Fin 4) (v : ComplexUnitSphere N) (t : ℝ),
      HasDerivAt
        (fun u : ℝ ↦ jetLp r.castSucc v u)
        (jetLp r.succ v t) t
  densityLp_contDiff_four :
    ∀ v : ComplexUnitSphere N,
      ContDiff ℝ 4 (fun t : ℝ ↦ jetLp 0 v t)
  iteratedDeriv_densityLp :
    ∀ (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ),
      iteratedDeriv (r : ℕ) (fun u : ℝ ↦ jetLp 0 v u) t =
        jetLp r v t
  compactTime_L1_bound :
    ∀ R : ℝ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ),
        |t| ≤ R → ‖jetLp r v t‖ ≤ M
  projective_compactTime_L1_envelope :
    ∀ (r : Fin 5) (R : ℝ),
      ∃ G : ComplexUnitSphere N → ℝ,
        (∀ v, 0 ≤ G v) ∧
        Integrable G (complexUnitSphereProbabilityMeasure N) ∧
        ∀ (v : ComplexUnitSphere N) (t : ℝ),
          |t| ≤ R → ‖jetLp r v t‖ ≤ G v

/-- Exact proposition to be discharged by the future implementation theorem
named `coeCenteredTransport_orderFour_zeroExtension`. -/
abbrev COECenteredTransportOrderFourZeroExtensionStatement : Type :=
  ∀ {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K),
    COECenteredOrderFourZeroExtensionFacts N K hN hboundary

namespace COECenteredOrderFourZeroExtensionFacts

/-- Stable restatement for downstream fixed-direction consumers. -/
theorem fixedDirection_densityLp_contDiff_four
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (H : COECenteredOrderFourZeroExtensionFacts N K hN hboundary)
    (v : ComplexUnitSphere N) :
    ContDiff ℝ 4 (fun t : ℝ ↦ H.jetLp 0 v t) :=
  H.densityLp_contDiff_four v

/-- Stable restatement of the true order-four derivative representative.
This equality is in `L1`; it makes no pointwise boundary claim. -/
theorem fixedDirection_iteratedDeriv_densityLp
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (H : COECenteredOrderFourZeroExtensionFacts N K hN hboundary)
    (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ) :
    iteratedDeriv (r : ℕ) (fun u : ℝ ↦ H.jetLp 0 v u) t =
      H.jetLp r v t :=
  H.iteratedDeriv_densityLp r v t

/-- Stable projective envelope theorem for later H17/H18 integration. -/
theorem exists_projective_compactTime_L1_envelope
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (H : COECenteredOrderFourZeroExtensionFacts N K hN hboundary)
    (r : Fin 5) (R : ℝ) :
    ∃ G : ComplexUnitSphere N → ℝ,
      (∀ v, 0 ≤ G v) ∧
      Integrable G (complexUnitSphereProbabilityMeasure N) ∧
      ∀ (v : ComplexUnitSphere N) (t : ℝ),
        |t| ≤ R → ‖H.jetLp r v t‖ ≤ G v :=
  H.projective_compactTime_L1_envelope r R

end COECenteredOrderFourZeroExtensionFacts

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

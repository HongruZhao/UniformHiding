import LogdetLean.GramHafnian.UltimateHiding.Dense.Telescoping
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19DirectTV

/-!
# Concrete convergence of the dense ambient law to its Gaussian target

For fixed positive block dimensions `N ≤ K`, the dense ambient family at
ambient dimension `M` is exactly the law of

`M U_{N,K} U_{N,K}ᵀ`,

where `U_{N,K}` is the upper-left Haar-unitary block.  The target is exactly
the law of `G Gᵀ` for a standard complex Gaussian `N × K` matrix.

The direct H19 argument starts from Jiang's literal unscaled Haar-corner
density, proves pointwise convergence of its scaled density to the standard
complex-Gaussian density, and applies Scheffe's theorem.  Orientation change
and deterministic transpose-Gram data processing then give the target law
below.  Thus this file discharges the literal target-convergence premise of
`probabilityTVLE_dense_telescope` without a likelihood, KL, moment, or
Rouault-factorization input.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

open LocalAnticoncentration

/-- The concrete dense ambient transpose-Gram law at ambient dimension `M`. -/
abbrev denseHaarAmbientLaw
    (H : UnitaryHaarProbabilityFamily) (N K M : ℕ) :
    Measure (Matrix (Fin N) (Fin N) ℂ) :=
  scaledHaarTransposeGramLaw H M N K

/-- The fixed Gaussian transpose-Gram target for block dimensions `N,K`. -/
abbrev denseGaussianTransposeGramTarget (N K : ℕ) :
    Measure (Matrix (Fin N) (Fin N) ℂ) :=
  gaussianTransposeGramLaw N K

/-- Elementary Archimedean fact used by the concrete target convergence:
every fixed nonnegative numerator divided by `start + n` is eventually below
every positive tolerance. -/
theorem exists_nat_fixed_div_add_le
    (c epsilon : ℝ) (start : ℕ) (hc : 0 ≤ c) (hepsilon : 0 < epsilon) :
    ∃ n : ℕ, c / ((start + n : ℕ) : ℝ) ≤ epsilon := by
  obtain ⟨n, hn⟩ := exists_nat_gt (c / epsilon)
  have hquotient_nonneg : 0 ≤ c / epsilon := div_nonneg hc hepsilon.le
  have hn_pos_real : (0 : ℝ) < n := hquotient_nonneg.trans_lt hn
  have hn_le : (n : ℝ) ≤ ((start + n : ℕ) : ℝ) := by
    exact_mod_cast (show n ≤ start + n by omega)
  have hdenominator : c / ((start + n : ℕ) : ℝ) ≤ c / (n : ℝ) :=
    div_le_div_of_nonneg_left hc hn_pos_real hn_le
  have hc_div_n_lt : c / (n : ℝ) < epsilon := by
    apply (div_lt_iff₀ hn_pos_real).2
    have hc_lt : c < (n : ℝ) * epsilon := (div_lt_iff₀ hepsilon).1 hn
    nlinarith
  exact ⟨n, hdenominator.trans hc_div_n_lt.le⟩

/-- Current-manuscript formulation of target convergence for the concrete dense
ambient family.  Its only scientific source input is Jiang's literal
unscaled Haar-corner density; all scaling, density limits, Scheffe, orientation
transport, and transpose-Gram data processing are proved internally. -/
theorem jiang_denseHaarAmbient_targetConvergence_localAnticoncentration
    (H : UnitaryHaarProbabilityFamily) {N K start : ℕ}
    (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K)
    (hstart : K + N ≤ start) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ n : ℕ,
        LocalAnticoncentration.probabilityTotalVariationLE
          (denseHaarAmbientLaw H N K (start + n))
          (denseGaussianTransposeGramTarget N K) epsilon := by
  intro epsilon hepsilon
  exact Sparse.exists_add_scaledHaarTransposeGramLaw_probabilityTotalVariationLE_H19
    H hN hK hNK epsilon hepsilon

/-- The exact `ProbabilityTVLE` premise required by
`probabilityTVLE_dense_telescope`. -/
theorem jiang_denseHaarAmbient_targetConvergence
    (H : UnitaryHaarProbabilityFamily) {N K start : ℕ}
    (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K)
    (hstart : K + N ≤ start) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ n : ℕ,
        ProbabilityTVLE
          (denseHaarAmbientLaw H N K (start + n))
          (denseGaussianTransposeGramTarget N K) epsilon :=
  jiang_denseHaarAmbient_targetConvergence_localAnticoncentration
    H hN hK hNK hstart

/-- Target convergence from an arbitrary ambient starting point.  The direct
asymptotic theorem is eventual in the ambient dimension, so Jiang's source
range imposes no restriction on `start`. -/
theorem jiang_denseHaarAmbient_targetConvergence_unrestricted
    (H : UnitaryHaarProbabilityFamily) {N K start : ℕ}
    (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ n : ℕ,
        ProbabilityTVLE
          (denseHaarAmbientLaw H N K (start + n))
          (denseGaussianTransposeGramTarget N K) epsilon := by
  intro epsilon hepsilon
  exact Sparse.exists_add_scaledHaarTransposeGramLaw_probabilityTotalVariationLE_H19
    H hN hK hNK epsilon hepsilon

/-- Dense telescope with its target-convergence premise discharged by the
concrete Jiang endpoint.  Only the local one-column estimates remain as an
explicit hypothesis. -/
theorem probabilityTVLE_dense_telescope_to_gaussianTransposeGram
    (H : UnitaryHaarProbabilityFamily) (C : ℝ) {N K start : ℕ}
    (hC : 0 ≤ C) (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K)
    (hstart : K + N ≤ start)
    (hstep : ∀ m,
      ProbabilityTVLE
        (denseHaarAmbientLaw H N K m)
        (denseHaarAmbientLaw H N K (m + 1))
        (denseTelescopingRate C N m)) :
    ProbabilityTVLE
      (denseHaarAmbientLaw H N K start)
      (denseGaussianTransposeGramTarget N K)
      (C * (N : ℝ) ^ 2 / (start : ℝ)) := by
  exact probabilityTVLE_dense_telescope
    (denseHaarAmbientLaw H N K)
    (denseGaussianTransposeGramTarget N K)
    C N start hC (by omega) hstep
    (jiang_denseHaarAmbient_targetConvergence H hN hK hNK hstart)

/-- Dense telescope from an arbitrary starting ambient dimension.  Target
convergence is supplied by the unrestricted endpoint above; only the local
one-column estimate remains explicit. -/
theorem probabilityTVLE_dense_telescope_to_gaussianTransposeGram_unrestricted
    (H : UnitaryHaarProbabilityFamily) (C : ℝ) {N K start : ℕ}
    (hC : 0 ≤ C) (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K)
    (hstart : 1 ≤ start)
    (hstep : ∀ m,
      ProbabilityTVLE
        (denseHaarAmbientLaw H N K m)
        (denseHaarAmbientLaw H N K (m + 1))
        (denseTelescopingRate C N m)) :
    ProbabilityTVLE
      (denseHaarAmbientLaw H N K start)
      (denseGaussianTransposeGramTarget N K)
      (C * (N : ℝ) ^ 2 / (start : ℝ)) := by
  exact probabilityTVLE_dense_telescope
    (denseHaarAmbientLaw H N K)
    (denseGaussianTransposeGramTarget N K)
    C N start hC hstart hstep
    (jiang_denseHaarAmbient_targetConvergence_unrestricted H hN hK hNK)

end

end LogdetLean.GramHafnian.UltimateHiding.Dense

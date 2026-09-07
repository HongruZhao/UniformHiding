import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16BoundaryExponentFourInterface
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Tactic

/-!
# H16 order-four boundary exponents

This module proves the scalar threshold facts used by the corrected
zero-extension argument.  Boundary decay is asserted only through order
three; the fourth exponent is used only for `L1` integrability.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

theorem coe_boundary_exponent_ge_seven_halves
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K) :
    (7 : ℝ) / 2 ≤ coeCornerDensityExponent N K := by
  have hKR : (2 * (N : ℝ) + 8 : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hboundary
  unfold coeCornerDensityExponent
  linarith

theorem coe_boundary_exponent_sub_fin4_pos
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K) (s : Fin 4) :
    0 < coeCornerDensityExponent N K - ((s : ℕ) : ℝ) := by
  have hsN : (s : ℕ) ≤ 3 := by omega
  have hsR : (((s : ℕ) : ℝ)) ≤ 3 := by exact_mod_cast hsN
  linarith [coe_boundary_exponent_ge_seven_halves hboundary]

theorem coe_boundary_exponent_sub_four_gt_neg_one
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K) :
    -1 < coeCornerDensityExponent N K - 4 := by
  linarith [coe_boundary_exponent_ge_seven_halves hboundary]

theorem coe_boundary_rpow_tendsto_zero
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K) (s : Fin 4) :
    Tendsto
      (fun epsilon : ℝ ↦
        epsilon ^
          (coeCornerDensityExponent N K - ((s : ℕ) : ℝ)))
      (𝓝[>] 0) (𝓝 0) := by
  have hp : 0 < coeCornerDensityExponent N K - ((s : ℕ) : ℝ) :=
    coe_boundary_exponent_sub_fin4_pos hboundary s
  have hc : ContinuousAt
      (fun epsilon : ℝ ↦
        epsilon ^
          (coeCornerDensityExponent N K - ((s : ℕ) : ℝ))) 0 :=
    Real.continuousAt_rpow_const 0 _ (Or.inr hp.le)
  change Tendsto
      (fun epsilon : ℝ ↦
        epsilon ^
          (coeCornerDensityExponent N K - ((s : ℕ) : ℝ)))
      (𝓝 0)
      (𝓝 ((0 : ℝ) ^
        (coeCornerDensityExponent N K - ((s : ℕ) : ℝ)))) at hc
  rw [Real.zero_rpow hp.ne'] at hc
  exact hc.mono_left inf_le_left

theorem integrable_coe_boundary_rpow_sub_four
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K) :
    IntegrableOn
      (fun u : ℝ ↦ u ^ (coeCornerDensityExponent N K - 4))
      (Ioc 0 1) := by
  have hIoo : IntegrableOn
      (fun u : ℝ ↦ u ^ (coeCornerDensityExponent N K - 4))
      (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2
      (coe_boundary_exponent_sub_four_gt_neg_one hboundary)
  exact hIoo.congr_set_ae Ioo_ae_eq_Ioc.symm

theorem coeBoundaryExponentFourFacts
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K) :
    COEBoundaryExponentFourFacts N K hboundary where
  exponent_ge_seven_halves :=
    coe_boundary_exponent_ge_seven_halves hboundary
  boundary_trace_exponent_pos :=
    coe_boundary_exponent_sub_fin4_pos hboundary
  fourth_exponent_gt_neg_one :=
    coe_boundary_exponent_sub_four_gt_neg_one hboundary
  boundary_rpow_tendsto_zero :=
    coe_boundary_rpow_tendsto_zero hboundary
  fourth_scalar_integrable :=
    integrable_coe_boundary_rpow_sub_four hboundary

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16L1TestUniqueness
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# From compact-test interval identities to Bochner identities

This module packages a compactly supported smooth test as a continuous
linear functional on `L1`, then uses distributional uniqueness to lift
scalar interval identities to equality in `L1`.  It is generic and contains
no COE, determinant, event, or H5 data.
-/

open MeasureTheory ContinuousLinearMap
open scoped ContDiff ENNReal

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E}

/-- Pair an `L1` class with a compactly supported smooth real test. -/
noncomputable def h16TestPairCLM
    (phi : E → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (hsupp : HasCompactSupport phi) :
    (E →₁[μ] ℝ) →L[ℝ] ℝ :=
  let hmem : MemLp phi ∞ μ :=
    hphi.continuous.memLp_top_of_hasCompactSupport hsupp μ
  ((lsmul ℝ ℝ).lpPairing μ 1 ∞).flip (hmem.toLp phi)

theorem h16TestPairCLM_apply
    (phi : E → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (hsupp : HasCompactSupport phi) (f : E →₁[μ] ℝ) :
    h16TestPairCLM phi hphi hsupp f = ∫ x, phi x * f x ∂μ := by
  let hmem : MemLp phi ∞ μ :=
    hphi.continuous.memLp_top_of_hasCompactSupport hsupp μ
  unfold h16TestPairCLM
  rw [ContinuousLinearMap.flip_apply]
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hmem] with x hx
  simp [hx, smul_eq_mul, mul_comm]

/-- If every compactly supported smooth test sees a Banach-valued interval
identity, then that identity holds in `L1`. -/
theorem h16_l1_intervalIdentity_of_testPairing
    (F G : ℝ → (E →₁[μ] ℝ)) (hG : Continuous G)
    (hpair : ∀ (h : ℝ) (phi : E → ℝ)
      (hphi : ContDiff ℝ ∞ phi) (hsupp : HasCompactSupport phi),
      h16TestPairCLM phi hphi hsupp (F h - F 0) =
        ∫ s in (0 : ℝ)..h, h16TestPairCLM phi hphi hsupp (G s)) :
    ∀ h : ℝ, F h - F 0 = ∫ s in (0 : ℝ)..h, G s := by
  intro h
  let D : E →₁[μ] ℝ :=
    F h - F 0 - ∫ s in (0 : ℝ)..h, G s
  have hD : D = 0 := by
    apply h16_l1_eq_zero_of_integral_test_mul_eq_zero D
    intro phi hphi hsupp
    rw [← h16TestPairCLM_apply phi hphi hsupp D]
    rw [show h16TestPairCLM phi hphi hsupp D =
        h16TestPairCLM phi hphi hsupp (F h - F 0) -
          h16TestPairCLM phi hphi hsupp
            (∫ s in (0 : ℝ)..h, G s) by
      simp [D]]
    rw [← (h16TestPairCLM phi hphi hsupp).intervalIntegral_comp_comm
      (hG.intervalIntegrable 0 h)]
    rw [hpair h phi hphi hsupp]
    exact sub_self _
  exact sub_eq_zero.mp (by simpa [D] using hD)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional

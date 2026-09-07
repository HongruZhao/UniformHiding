import LogdetLean.GramHafnian.CurrentPRL.MixtureDensity

/-!
# Literal supremum norm endpoint for the current PRL density

This module packages the pointwise density estimate as the exact uniform norm
statement printed after Equation (13) in the PRL.
-/

open Set

namespace LogdetLean.GramHafnian

noncomputable section

/-- The ordinary pointwise supremum norm of the real Gram hafnian density.
It is the supremum over all complex centers, not an essential supremum. -/
def currentPRLGramHafnianDensitySupNorm
    {r k : ℕ} (hr : 1 ≤ r) : ℝ :=
  sSup (Set.range fun w : ℂ ↦
    ‖currentPRLGramHafnianDensity (k := k) hr w‖)

/-- The radial Gram hafnian density attains its supremum norm at the origin. -/
theorem currentPRLGramHafnianDensitySupNorm_eq_at_zero
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k) :
    currentPRLGramHafnianDensitySupNorm (k := k) hr =
      currentPRLGramHafnianDensity (k := k) hr 0 := by
  let f : ℂ → ℝ := currentPRLGramHafnianDensity (k := k) hr
  have hnonneg : ∀ w : ℂ, 0 ≤ f w := fun w ↦
    currentPRLGramHafnianDensity_nonneg hr w
  have hmax : ∀ w : ℂ, f w ≤ f 0 := fun w ↦
    currentPRLGramHafnianDensity_le_at_zero hr hk w
  have hbounded : BddAbove (Set.range fun w : ℂ ↦ ‖f w‖) := by
    refine ⟨f 0, ?_⟩
    rintro _ ⟨w, rfl⟩
    simpa [Real.norm_eq_abs, abs_of_nonneg (hnonneg w)] using hmax w
  apply le_antisymm
  · unfold currentPRLGramHafnianDensitySupNorm
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨w, rfl⟩
    simpa [f, Real.norm_eq_abs, abs_of_nonneg (hnonneg w)] using hmax w
  · unfold currentPRLGramHafnianDensitySupNorm
    have hmem : ‖f 0‖ ∈ Set.range (fun w : ℂ ↦ ‖f w‖) := ⟨0, rfl⟩
    have hle : ‖f 0‖ ≤ sSup (Set.range fun w : ℂ ↦ ‖f w‖) :=
      le_csSup hbounded hmem
    simpa [f, Real.norm_eq_abs, abs_of_nonneg (hnonneg 0)] using hle

/-- Literal form of the density estimate printed after Equation (13):
`π σ² ‖f‖∞ ≤ B`. -/
theorem pi_sigma_sq_mul_currentPRLGramHafnianDensitySupNorm_le
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k) :
    Real.pi * gramHafnianSigma k r ^ 2 *
        currentPRLGramHafnianDensitySupNorm (k := k) hr ≤
      shiftedAnticoncentrationConstant k r := by
  rw [currentPRLGramHafnianDensitySupNorm_eq_at_zero hr hk]
  exact pi_sigma_sq_mul_currentPRLGramHafnianDensity_le hr hk 0

end

end LogdetLean.GramHafnian

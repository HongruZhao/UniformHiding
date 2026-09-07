import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! Threshold optimization is order theory, not a new probabilistic assumption.
The proofs below are new in this revision and await a fresh Lean build. -/
namespace GBSHiding
noncomputable section

def optimizedCertificate (E : ℝ → ℝ) : ℝ :=
  sInf (E '' Set.Ici 0)

theorem lowerBound_optimizedCertificate
    (F : ℝ) (E : ℝ → ℝ)
    (h : ∀ t : ℝ, 0 ≤ t → F ≤ E t) :
    F ≤ optimizedCertificate E := by
  apply le_csInf
  · exact ⟨E 0, ⟨0, by simp, rfl⟩⟩
  · rintro y ⟨t, ht, rfl⟩
    exact h t ht

theorem lowerBound_bestOptimizedCertificate
    (F : ℝ) (E₁ E₂ : ℝ → ℝ)
    (h₁ : ∀ t : ℝ, 0 ≤ t → F ≤ E₁ t)
    (h₂ : ∀ t : ℝ, 0 ≤ t → F ≤ E₂ t) :
    F ≤ min (optimizedCertificate E₁) (optimizedCertificate E₂) := by
  exact le_min (lowerBound_optimizedCertificate F E₁ h₁)
    (lowerBound_optimizedCertificate F E₂ h₂)

/-- Scalar part of the additional `K < N` hiding argument. -/
theorem narrowBlockRate_le
    {N K M : ℝ} (hN : 0 ≤ N) (hK : 0 ≤ K)
    (hKN : K ≤ N) (hM : 0 < M) :
    (N + K) * Real.sqrt (N * K) / M ≤ 2 * N ^ 2 / M := by
  have hprod : N * K ≤ N ^ 2 := by nlinarith
  have hs : Real.sqrt (N * K) ≤ N := by
    calc
      Real.sqrt (N * K) ≤ Real.sqrt (N ^ 2) := Real.sqrt_le_sqrt hprod
      _ = N := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hN]
  apply div_le_div_of_nonneg_right _ hM.le
  calc
    (N + K) * Real.sqrt (N * K) ≤ (N + K) * N :=
      mul_le_mul_of_nonneg_left hs (add_nonneg hN hK)
    _ ≤ 2 * N ^ 2 := by nlinarith

end
end GBSHiding

import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.TaylorTV
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.ConcreteCorrelatedPath
import Mathlib.Tactic

/-!
# Propagating an origin cubic score with a fourth-derivative bound

This is the scalar calculus step used after the actual centered COE score
identities have been established.  It contains no probabilistic ledger and
does not assume any COE, moment, total-variation, or hiding theorem.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding

/-- The truncated orbital amplitude used in the concrete bridge lies in the
inverse-dimension window required by fourth-to-third propagation. -/
theorem abs_concreteGoodOrbitalAmplitude_one_le_inverse_dimension
    {N : ℕ} (hN : 1 ≤ N) (q : ℝ) :
    |concreteGoodOrbitalAmplitude N 1 q| ≤ 1 / (N : ℝ) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  unfold concreteGoodOrbitalAmplitude
  split_ifs with hbad
  · simp only [abs_zero]
    positivity
  · have hnot : ¬ |Dense.oneColumnRankOneLog q| > 1 / (N : ℝ) := by
      simpa only [Dense.oneColumnLogBadEvent, Set.mem_ofPred_eq] using hbad
    exact le_of_not_gt hnot

/-- A fourth-derivative bound propagates a third-derivative estimate from the
origin to an arbitrary point. -/
theorem abs_iteratedDeriv_three_le_at_of_fourth
    {path : ℝ → ℝ} {N : ℕ} {Bthree Bfour s : ℝ}
    (hsmooth : ContDiff ℝ 4 path)
    (hzero : |iteratedDeriv 3 path 0| ≤ Bthree * (N : ℝ))
    (hfour : ∀ y ∈ Set.uIcc 0 s,
      |iteratedDeriv 4 path y| ≤ Bfour * (N : ℝ) ^ 2) :
    |iteratedDeriv 3 path s| ≤
      Bthree * (N : ℝ) + Bfour * (N : ℝ) ^ 2 * |s| := by
  have hsmooth3 : ContDiff ℝ 1 (iteratedDeriv 3 path) := by
    have h4 : ContDiff ℝ (3 + 1 : ℕ) path := by simpa using hsmooth
    exact (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp h4).2
  have hderiv : ∀ y ∈ Set.uIcc 0 s,
      |iteratedDeriv 1 (iteratedDeriv 3 path) y| ≤
        Bfour * (N : ℝ) ^ 2 := by
    intro y hy
    simpa [iteratedDeriv_succ] using hfour y hy
  have hgrowth := abs_sub_taylor_zero_le
    (iteratedDeriv 3 path) s (Bfour * (N : ℝ) ^ 2) hsmooth3 hderiv
  calc
    |iteratedDeriv 3 path s| ≤
        |iteratedDeriv 3 path 0| +
          |iteratedDeriv 3 path s - iteratedDeriv 3 path 0| := by
      have h := abs_add_le (iteratedDeriv 3 path 0)
        (iteratedDeriv 3 path s - iteratedDeriv 3 path 0)
      simpa [add_sub_cancel] using h
    _ ≤ Bthree * (N : ℝ) + Bfour * (N : ℝ) ^ 2 * |s| :=
      add_le_add hzero hgrowth

/-- At the one-column cutoff `|s| ≤ 1/N`, an `O(N^2)` fourth score
contributes only `O(N)` to the cubic score. -/
theorem abs_iteratedDeriv_three_le_at_inverse_dimension_of_fourth
    {path : ℝ → ℝ} {N : ℕ} {Bthree Bfour s : ℝ}
    (hN : 1 ≤ N) (hBfour : 0 ≤ Bfour)
    (hsmooth : ContDiff ℝ 4 path)
    (hzero : |iteratedDeriv 3 path 0| ≤ Bthree * (N : ℝ))
    (hfour : ∀ y ∈ Set.uIcc 0 s,
      |iteratedDeriv 4 path y| ≤ Bfour * (N : ℝ) ^ 2)
    (hs : |s| ≤ 1 / (N : ℝ)) :
    |iteratedDeriv 3 path s| ≤ (Bthree + Bfour) * (N : ℝ) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hscale : Bfour * (N : ℝ) ^ 2 * |s| ≤
      Bfour * (N : ℝ) := by
    calc
      Bfour * (N : ℝ) ^ 2 * |s| ≤
          Bfour * (N : ℝ) ^ 2 * (1 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hs (mul_nonneg hBfour (sq_nonneg _))
      _ = Bfour * (N : ℝ) := by field_simp
  exact (abs_iteratedDeriv_three_le_at_of_fourth
    hsmooth hzero hfour).trans <| by
      calc
        Bthree * (N : ℝ) + Bfour * (N : ℝ) ^ 2 * |s| ≤
            Bthree * (N : ℝ) + Bfour * (N : ℝ) :=
          add_le_add le_rfl hscale
        _ = (Bthree + Bfour) * (N : ℝ) := by ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

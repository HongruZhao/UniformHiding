import LogdetLean.GramHafnian.UltimateHiding.Dense.RadialConvolution
import LogdetLean.GramHafnian.CurrentPRL.TotalVariation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Total variation telescoping for the dense hiding argument

This file proves the deterministic bookkeeping which turns consecutive one
column estimates into a bound between an initial law and a limiting law.  The
one step estimates, the partial sum estimate, and convergence to the target are
all explicit hypotheses.  Thus no analytic input is hidden in the formal
telescoping theorem.
-/

open MeasureTheory ProbabilityTheory Finset

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

abbrev ProbabilityTVLE
    {State : Type*} [MeasurableSpace State]
    (mu nu : Measure State) (delta : ℝ) : Prop :=
  CurrentPRL.probabilityTotalVariationLE mu nu delta

theorem probabilityTVLE_refl
    {State : Type*} [MeasurableSpace State] (mu : Measure State) :
    ProbabilityTVLE mu mu 0 := by
  refine ⟨le_rfl, ?_⟩
  intro s hs
  simp

theorem probabilityTVLE_triangle
    {State : Type*} [MeasurableSpace State]
    {mu nu xi : Measure State} {delta epsilon : ℝ}
    (hmunu : ProbabilityTVLE mu nu delta)
    (hnuxi : ProbabilityTVLE nu xi epsilon) :
    ProbabilityTVLE mu xi (delta + epsilon) := by
  refine ⟨add_nonneg hmunu.1 hnuxi.1, ?_⟩
  intro s hs
  calc
    |mu.real s - xi.real s| =
        |(mu.real s - nu.real s) + (nu.real s - xi.real s)| := by ring_nf
    _ ≤ |mu.real s - nu.real s| + |nu.real s - xi.real s| := abs_add_le _ _
    _ ≤ delta + epsilon := add_le_add (hmunu.2 s hs) (hnuxi.2 s hs)

/-- Finite telescoping from `start` through `n` consecutive one column
updates. -/
theorem probabilityTVLE_chain
    {State : Type*} [MeasurableSpace State]
    (law : ℕ → Measure State) (error : ℕ → ℝ)
    (hstep : ∀ m, ProbabilityTVLE (law m) (law (m + 1)) (error m))
    (start n : ℕ) :
    ProbabilityTVLE (law start) (law (start + n))
      (∑ j ∈ Finset.range n, error (start + j)) := by
  induction n with
  | zero =>
      simpa using probabilityTVLE_refl (law start)
  | succ n ih =>
      have htri := probabilityTVLE_triangle ih (hstep (start + n))
      simpa [Finset.sum_range_succ, Nat.add_assoc] using htri

/-- Finite telescoping with a final comparison to a target law. -/
theorem probabilityTVLE_chain_to_target
    {State : Type*} [MeasurableSpace State]
    (law : ℕ → Measure State) (target : Measure State)
    (error : ℕ → ℝ)
    (hstep : ∀ m, ProbabilityTVLE (law m) (law (m + 1)) (error m))
    (start n : ℕ) {remainder : ℝ}
    (htarget : ProbabilityTVLE (law (start + n)) target remainder) :
    ProbabilityTVLE (law start) target
      ((∑ j ∈ Finset.range n, error (start + j)) + remainder) :=
  probabilityTVLE_triangle (probabilityTVLE_chain law error hstep start n) htarget

/-- Infinite telescoping closure.

`hpartial` is the numerical summation estimate and `happroach` is convergence
of the ambient law to the target in the same probability total variation
convention.  These are precisely the two analytic obligations which remain
after the finite chain theorem. -/
theorem probabilityTVLE_telescope_to_limit
    {State : Type*} [MeasurableSpace State]
    (law : ℕ → Measure State) (target : Measure State)
    (error : ℕ → ℝ) (start : ℕ) (budget : ℝ)
    (hbudget : 0 ≤ budget)
    (hstep : ∀ m, ProbabilityTVLE (law m) (law (m + 1)) (error m))
    (hpartial : ∀ n, (∑ j ∈ Finset.range n, error (start + j)) ≤ budget)
    (happroach : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ n, ProbabilityTVLE (law (start + n)) target epsilon) :
    ProbabilityTVLE (law start) target budget := by
  refine ⟨hbudget, ?_⟩
  intro s hs
  by_contra hnot
  have hstrict : budget < |(law start).real s - target.real s| := lt_of_not_ge hnot
  let epsilon : ℝ :=
    (|(law start).real s - target.real s| - budget) / 2
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  obtain ⟨n, hn⟩ := happroach epsilon hepsilon
  have hfinite := probabilityTVLE_chain_to_target law target error hstep start n hn
  have hevent := hfinite.2 s hs
  have hsum := hpartial n
  dsimp [epsilon] at hevent
  linarith

/-- The exact reciprocal difference behind the dense ambient telescope. -/
theorem reciprocal_mul_succ_eq_sub (m : ℕ) (hm : 1 ≤ m) :
    (1 : ℝ) / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) =
      1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have hm10 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  norm_num [Nat.cast_add]

/-- Finite reciprocal products telescope exactly. -/
theorem sum_reciprocal_mul_succ
    (start n : ℕ) (hstart : 1 ≤ start) :
    (∑ j ∈ Finset.range n,
      (1 : ℝ) /
        (((start + j : ℕ) : ℝ) * ((start + j + 1 : ℕ) : ℝ))) =
      1 / (start : ℝ) - 1 / ((start + n : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rw [reciprocal_mul_succ_eq_sub (start + n) (by omega)]
      ring_nf

/-- Canonical `C N² / (m(m+1))` one step budget. -/
def denseTelescopingRate (C : ℝ) (N m : ℕ) : ℝ :=
  C * (N : ℝ) ^ 2 /
    ((m : ℝ) * ((m + 1 : ℕ) : ℝ))

theorem sum_denseTelescopingRate
    (C : ℝ) (N start n : ℕ) (hstart : 1 ≤ start) :
    (∑ j ∈ Finset.range n, denseTelescopingRate C N (start + j)) =
      C * (N : ℝ) ^ 2 *
        (1 / (start : ℝ) - 1 / ((start + n : ℕ) : ℝ)) := by
  have hsum := sum_reciprocal_mul_succ start n hstart
  simp only [one_div] at hsum
  simp only [denseTelescopingRate, div_eq_mul_inv]
  rw [← Finset.mul_sum, hsum]
  simp

theorem sum_denseTelescopingRate_le
    (C : ℝ) (N start n : ℕ) (hC : 0 ≤ C) (hstart : 1 ≤ start) :
    (∑ j ∈ Finset.range n, denseTelescopingRate C N (start + j)) ≤
      C * (N : ℝ) ^ 2 / (start : ℝ) := by
  rw [sum_denseTelescopingRate C N start n hstart]
  have hfactor : 0 ≤ C * (N : ℝ) ^ 2 :=
    mul_nonneg hC (sq_nonneg _)
  have htail : 0 ≤ 1 / ((start + n : ℕ) : ℝ) := by positivity
  have hsub :
      1 / (start : ℝ) - 1 / ((start + n : ℕ) : ℝ) ≤ 1 / (start : ℝ) :=
    sub_le_self _ htail
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hsub hfactor

/-- Dense branch of the hiding telescope.  Once the local analytic estimate is
supplied with the canonical reciprocal product rate, the global
`C N² / start` estimate is fully formal. -/
theorem probabilityTVLE_dense_telescope
    {State : Type*} [MeasurableSpace State]
    (law : ℕ → Measure State) (target : Measure State)
    (C : ℝ) (N start : ℕ) (hC : 0 ≤ C) (hstart : 1 ≤ start)
    (hstep : ∀ m,
      ProbabilityTVLE (law m) (law (m + 1)) (denseTelescopingRate C N m))
    (happroach : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ n, ProbabilityTVLE (law (start + n)) target epsilon) :
    ProbabilityTVLE (law start) target
      (C * (N : ℝ) ^ 2 / (start : ℝ)) := by
  apply probabilityTVLE_telescope_to_limit law target
    (denseTelescopingRate C N) start (C * (N : ℝ) ^ 2 / (start : ℝ))
  · positivity
  · exact hstep
  · intro n
    exact sum_denseTelescopingRate_le C N start n hC hstart
  · exact happroach

end

end LogdetLean.GramHafnian.UltimateHiding.Dense

import LogdetLean.GramHafnian.UltimateHiding.Dense.Telescoping

/-!
# Dense telescoping from a prescribed ambient index

The analytic one-column estimate is valid only from the large-ambient start
onward.  These wrappers carry that hypothesis literally, avoiding any bogus
obligation at ambient index zero.
-/

open MeasureTheory Finset

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

theorem probabilityTVLE_chain_from
    {State : Type*} [MeasurableSpace State]
    (law : ℕ → Measure State) (error : ℕ → ℝ) (start n : ℕ)
    (hstep : ∀ m, start <= m →
      ProbabilityTVLE (law m) (law (m + 1)) (error m)) :
    ProbabilityTVLE (law start) (law (start + n))
      (∑ j ∈ Finset.range n, error (start + j)) := by
  let shiftedLaw : ℕ → Measure State := fun j ↦ law (start + j)
  let shiftedError : ℕ → ℝ := fun j ↦ error (start + j)
  have hshift : ∀ j,
      ProbabilityTVLE (shiftedLaw j) (shiftedLaw (j + 1))
        (shiftedError j) := by
    intro j
    dsimp [shiftedLaw, shiftedError]
    simpa [Nat.add_assoc] using hstep (start + j) (Nat.le_add_right start j)
  have h := probabilityTVLE_chain shiftedLaw shiftedError hshift 0 n
  simpa [shiftedLaw, shiftedError] using h

theorem probabilityTVLE_chain_to_target_from
    {State : Type*} [MeasurableSpace State]
    (law : ℕ → Measure State) (target : Measure State)
    (error : ℕ → ℝ) (start n : ℕ)
    (hstep : ∀ m, start <= m →
      ProbabilityTVLE (law m) (law (m + 1)) (error m))
    {remainder : ℝ}
    (htarget : ProbabilityTVLE (law (start + n)) target remainder) :
    ProbabilityTVLE (law start) target
      ((∑ j ∈ Finset.range n, error (start + j)) + remainder) :=
  probabilityTVLE_triangle
    (probabilityTVLE_chain_from law error start n hstep) htarget

theorem probabilityTVLE_telescope_to_limit_from
    {State : Type*} [MeasurableSpace State]
    (law : ℕ → Measure State) (target : Measure State)
    (error : ℕ → ℝ) (start : ℕ) (budget : ℝ)
    (hbudget : 0 <= budget)
    (hstep : ∀ m, start <= m →
      ProbabilityTVLE (law m) (law (m + 1)) (error m))
    (hpartial : ∀ n,
      (∑ j ∈ Finset.range n, error (start + j)) <= budget)
    (happroach : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ n, ProbabilityTVLE (law (start + n)) target epsilon) :
    ProbabilityTVLE (law start) target budget := by
  refine ⟨hbudget, ?_⟩
  intro s hs
  by_contra hnot
  have hstrict : budget < |(law start).real s - target.real s| :=
    lt_of_not_ge hnot
  let epsilon : ℝ :=
    (|(law start).real s - target.real s| - budget) / 2
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  obtain ⟨n, hn⟩ := happroach epsilon hepsilon
  have hfinite := probabilityTVLE_chain_to_target_from
    law target error start n hstep hn
  have hevent := hfinite.2 s hs
  have hsum := hpartial n
  dsimp [epsilon] at hevent
  linarith

/-- The usable dense telescope: local estimates are required only from
`start` onward. -/
theorem probabilityTVLE_dense_telescope_from
    {State : Type*} [MeasurableSpace State]
    (law : ℕ → Measure State) (target : Measure State)
    (C : ℝ) (N start : ℕ) (hC : 0 <= C) (hstart : 1 <= start)
    (hstep : ∀ m, start <= m →
      ProbabilityTVLE (law m) (law (m + 1))
        (denseTelescopingRate C N m))
    (happroach : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ n, ProbabilityTVLE (law (start + n)) target epsilon) :
    ProbabilityTVLE (law start) target
      (C * (N : ℝ) ^ 2 / (start : ℝ)) := by
  apply probabilityTVLE_telescope_to_limit_from law target
    (denseTelescopingRate C N) start
    (C * (N : ℝ) ^ 2 / (start : ℝ))
  · positivity
  · exact hstep
  · intro n
    exact sum_denseTelescopingRate_le C N start n hC hstart
  · exact happroach

end

end LogdetLean.GramHafnian.UltimateHiding.Dense

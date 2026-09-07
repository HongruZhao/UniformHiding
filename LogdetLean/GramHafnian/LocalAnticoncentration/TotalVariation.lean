import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Probability total variation for the current manuscript

The hiding source uses the probability convention

`d_TV(mu, nu) = sup_s |mu(s) - nu(s)|`.

The predicate below fixes that convention without depending on the
normalization of the total variation norm of a signed measure.
-/

open Filter MeasureTheory Set

namespace LogdetLean.GramHafnian.LocalAnticoncentration

noncomputable section

/-- `probabilityTotalVariationLE mu nu delta` means
`sup_s |mu(s) - nu(s)| <= delta` in the probability convention. -/
def probabilityTotalVariationLE {alpha : Type*} [MeasurableSpace alpha]
    (mu nu : Measure alpha) (delta : ℝ) : Prop :=
  0 <= delta ∧
    ∀ s : Set alpha, MeasurableSet s -> |mu.real s - nu.real s| <= delta

theorem probabilityTotalVariationLE.nonneg
    {alpha : Type*} [MeasurableSpace alpha]
    {mu nu : Measure alpha} {delta : ℝ}
    (h : probabilityTotalVariationLE mu nu delta) : 0 <= delta :=
  h.1

theorem probabilityTotalVariationLE.event_le
    {alpha : Type*} [MeasurableSpace alpha]
    {mu nu : Measure alpha} {delta : ℝ}
    (h : probabilityTotalVariationLE mu nu delta)
    {s : Set alpha} (hs : MeasurableSet s) :
    mu.real s <= nu.real s + delta := by
  have habs := h.2 s hs
  linarith [le_abs_self (mu.real s - nu.real s)]

theorem probabilityTotalVariationLE.event_le_min
    {alpha : Type*} [MeasurableSpace alpha]
    {mu nu : Measure alpha} [IsProbabilityMeasure mu] {delta : ℝ}
    (h : probabilityTotalVariationLE mu nu delta)
    {s : Set alpha} (hs : MeasurableSet s) :
    mu.real s <= min 1 (nu.real s + delta) := by
  exact le_min measureReal_le_one (h.event_le hs)

theorem probabilityTotalVariationLE.symm
    {alpha : Type*} [MeasurableSpace alpha]
    {mu nu : Measure alpha} {delta : ℝ}
    (h : probabilityTotalVariationLE mu nu delta) :
    probabilityTotalVariationLE nu mu delta := by
  refine ⟨h.1, fun s hs => ?_⟩
  simpa [abs_sub_comm] using h.2 s hs

theorem probabilityTotalVariationLE.mono
    {alpha : Type*} [MeasurableSpace alpha]
    {mu nu : Measure alpha} {delta delta' : ℝ}
    (h : probabilityTotalVariationLE mu nu delta) (hdelta : delta <= delta') :
    probabilityTotalVariationLE mu nu delta' := by
  exact ⟨h.1.trans hdelta, fun s hs => (h.2 s hs).trans hdelta⟩

/-- Data processing: a measurable pushforward cannot increase probability
total variation. -/
theorem probabilityTotalVariationLE.map
    {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    {mu nu : Measure alpha} {delta : ℝ}
    (h : probabilityTotalVariationLE mu nu delta)
    {f : alpha -> beta} (hf : Measurable f) :
    probabilityTotalVariationLE (Measure.map f mu) (Measure.map f nu) delta := by
  refine ⟨h.1, fun s hs => ?_⟩
  simp only [MeasureTheory.map_measureReal_apply hf hs]
  exact h.2 (f ⁻¹' s) (hs.preimage hf)

/-- Literal sequence form of an asymptotic probability total variation
estimate.  It says that one nonnegative constant controls the distance by
`C * rate M` for all sufficiently large `M`. -/
def ProbabilityTotalVariationIsBigO
    {alpha : ℕ -> Type*} [∀ M, MeasurableSpace (alpha M)]
    (mu nu : (M : ℕ) -> Measure (alpha M)) (rate : ℕ -> ℝ) : Prop :=
  ∃ C : ℝ, 0 <= C ∧
    ∀ᶠ M in atTop,
      probabilityTotalVariationLE (mu M) (nu M) (C * rate M)

theorem ProbabilityTotalVariationIsBigO.exists_eventual_bound
    {alpha : ℕ -> Type*} [∀ M, MeasurableSpace (alpha M)]
    {mu nu : (M : ℕ) -> Measure (alpha M)} {rate : ℕ -> ℝ}
    (h : ProbabilityTotalVariationIsBigO mu nu rate) :
    ∃ C : ℝ, 0 <= C ∧
      ∀ᶠ M in atTop,
        probabilityTotalVariationLE (mu M) (nu M) (C * rate M) :=
  h

end

end LogdetLean.GramHafnian.LocalAnticoncentration

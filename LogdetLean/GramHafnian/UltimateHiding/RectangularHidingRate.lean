import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Definition-only rectangular hiding rate

The rate is isolated from the historical theorem file that originally also
declared an unused external input.
-/

namespace LogdetLean.GramHafnian.CurrentPRL

/-- The source rate `sqrt(N*K/M)`, with casts made explicit. -/
noncomputable def rectangularHidingRate (M N K : ℕ) : ℝ :=
  Real.sqrt ((((N * K : ℕ) : ℝ)) / (M : ℝ))

end LogdetLean.GramHafnian.CurrentPRL

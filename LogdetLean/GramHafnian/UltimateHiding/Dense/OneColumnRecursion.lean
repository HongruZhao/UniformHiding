import LogdetLean.GramHafnian.UltimateHiding.Dense.Parameters
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# The exact one column recursion as a kernel interface

The finite dimensional Haar calculation has two logically separate pieces:

* the new scalar eigenvalue has the beta law formalized in `Parameters`;
* conditional on that scalar and an independent direction, the old matrix is
  transformed by a measurable ambient update.

This file constructs the resulting Markov kernel and states the exact recursion
as a proposition.  It deliberately does not assert that a particular Haar law
satisfies the proposition.  Proving that equality is the external analytic and
geometric obligation for the future matrix formalization.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

/-- Sample a parameter independently of the current state and then apply a
measurable update. -/
def independentUpdateKernel
    {State Param : Type*} [MeasurableSpace State] [MeasurableSpace Param]
    (paramLaw : Measure Param) (update : State × Param → State) : Kernel State State :=
  ((Kernel.id : Kernel State State) ×ₖ Kernel.const State paramLaw).map update

theorem independentUpdateKernel_isMarkov
    {State Param : Type*} [MeasurableSpace State] [MeasurableSpace Param]
    (paramLaw : Measure Param) (update : State × Param → State)
    (hparam : IsProbabilityMeasure paramLaw) (hupdate : Measurable update) :
    IsMarkovKernel (independentUpdateKernel paramLaw update) := by
  let _ : IsProbabilityMeasure paramLaw := hparam
  unfold independentUpdateKernel
  exact Kernel.IsMarkovKernel.map _ hupdate

/-- Pointwise sampling semantics: at a fixed state, the update kernel is the
pushforward of the independent parameter law. -/
theorem independentUpdateKernel_apply
    {State Param : Type*} [MeasurableSpace State] [MeasurableSpace Param]
    (paramLaw : Measure Param) (update : State × Param → State)
    (hparam : IsProbabilityMeasure paramLaw) (hupdate : Measurable update)
    (x : State) :
    independentUpdateKernel paramLaw update x =
      paramLaw.map (fun p ↦ update (x, p)) := by
  let _ : IsProbabilityMeasure paramLaw := hparam
  unfold independentUpdateKernel
  rw [Kernel.map_apply _ hupdate, Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod]
  have hmk : Measurable (Prod.mk x : Param → State × Param) := by fun_prop
  rw [Measure.map_map hupdate hmk]
  rfl

/-- The joint law of the beta radial variable and an independent direction. -/
def oneColumnParameterLaw
    {Direction : Type*} [MeasurableSpace Direction]
    (m N : ℕ) (directionLaw : Measure Direction) : Measure (ℝ × Direction) :=
  (oneColumnBetaLaw m N).prod directionLaw

theorem oneColumnParameterLaw_isProbability
    {Direction : Type*} [MeasurableSpace Direction]
    {m N : ℕ} (directionLaw : Measure Direction)
    (hN : 1 ≤ N) (hNm : N ≤ m)
    (hdirection : IsProbabilityMeasure directionLaw) :
    IsProbabilityMeasure (oneColumnParameterLaw m N directionLaw) := by
  let _ : IsProbabilityMeasure (oneColumnBetaLaw m N) :=
    oneColumnBetaLaw_isProbability hN hNm
  let _ : IsProbabilityMeasure directionLaw := hdirection
  unfold oneColumnParameterLaw
  infer_instance

/-- The ambient one column update kernel.  The concrete matrix operation is
passed as `update q v x`; this keeps the exact probability layer independent of
the later choice of matrix representation. -/
def ambientOneColumnKernel
    {State Direction : Type*}
    [MeasurableSpace State] [MeasurableSpace Direction]
    (m N : ℕ) (directionLaw : Measure Direction)
    (update : ℝ → Direction → State → State) : Kernel State State :=
  independentUpdateKernel (oneColumnParameterLaw m N directionLaw)
    (fun xp ↦ update xp.2.1 xp.2.2 xp.1)

theorem ambientOneColumnKernel_isMarkov
    {State Direction : Type*}
    [MeasurableSpace State] [MeasurableSpace Direction]
    {m N : ℕ} (directionLaw : Measure Direction)
    (update : ℝ → Direction → State → State)
    (hN : 1 ≤ N) (hNm : N ≤ m)
    (hdirection : IsProbabilityMeasure directionLaw)
    (hupdate : Measurable fun xp : State × (ℝ × Direction) ↦
      update xp.2.1 xp.2.2 xp.1) :
    IsMarkovKernel (ambientOneColumnKernel m N directionLaw update) := by
  apply independentUpdateKernel_isMarkov
  · exact oneColumnParameterLaw_isProbability directionLaw hN hNm hdirection
  · exact hupdate

/-- Exact ambient one column recursion, exposed as a theorem obligation rather
than postulated as an axiom.

With the intended indexing, `law m` is the normalized `N × N` symmetric Gram
corner obtained from ambient dimension `m`, and `step m` adds the next ambient
column. -/
def AmbientOneColumnRecursion
    {State : Type*} [MeasurableSpace State]
    (law : ℕ → Measure State) (step : ℕ → Kernel State State) (start : ℕ) : Prop :=
  ∀ m, start ≤ m → law (m + 1) = step m ∘ₘ law m

theorem AmbientOneColumnRecursion.step_eq
    {State : Type*} [MeasurableSpace State]
    {law : ℕ → Measure State} {step : ℕ → Kernel State State} {start m : ℕ}
    (hrec : AmbientOneColumnRecursion law step start) (hm : start ≤ m) :
    law (m + 1) = step m ∘ₘ law m :=
  hrec m hm

/-- Two consecutive exact recursion steps combine by kernel composition. -/
theorem AmbientOneColumnRecursion.two_steps
    {State : Type*} [MeasurableSpace State]
    {law : ℕ → Measure State} {step : ℕ → Kernel State State} {start m : ℕ}
    (hrec : AmbientOneColumnRecursion law step start) (hm : start ≤ m) :
    law (m + 2) = (step (m + 1) ∘ₖ step m) ∘ₘ law m := by
  calc
    law (m + 2) = law ((m + 1) + 1) := by congr
    _ = step (m + 1) ∘ₘ law (m + 1) := hrec (m + 1) (by omega)
    _ = step (m + 1) ∘ₘ (step m ∘ₘ law m) := by rw [hrec m hm]
    _ = (step (m + 1) ∘ₖ step m) ∘ₘ law m := Measure.comp_assoc

end

end LogdetLean.GramHafnian.UltimateHiding.Dense

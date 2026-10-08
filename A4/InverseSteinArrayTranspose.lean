import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic

namespace A4Research.InverseStein
noncomputable section
open MeasureTheory ProbabilityTheory

/-! ## Transposing a finite iid array -/

/-- Transpose a finite function-valued array.  The measurable structure on
both sides is the coordinatewise product structure. -/
def piTransposeMeasurableEquiv (I J E : Type*) [MeasurableSpace E] :
    (I → J → E) ≃ᵐ (J → I → E) where
  toFun x j i := x i j
  invFun x i j := x j i
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    refine measurable_pi_lambda _ fun j ↦ measurable_pi_lambda _ fun i ↦ ?_
    exact (measurable_pi_apply j).comp (measurable_pi_apply i)
  measurable_invFun := by
    refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
    exact (measurable_pi_apply i).comp (measurable_pi_apply j)

@[simp]
theorem piTransposeMeasurableEquiv_apply
    {I J E : Type*} [MeasurableSpace E] (x : I → J → E) (j : J) (i : I) :
    piTransposeMeasurableEquiv I J E x j i = x i j := rfl

/-- A finite iid scalar array remains an iid array after transposition.  This
is proved from Mathlib's infinite-product curry and reindexing theorems, then
specialized back to finite `Measure.pi` products. -/
theorem map_pi_pi_piTranspose
    {I J E : Type*} [Fintype I] [Fintype J] [MeasurableSpace E]
    (mu : Measure E) [IsProbabilityMeasure mu] :
    Measure.map (piTransposeMeasurableEquiv I J E)
        (Measure.pi fun _ : I ↦ Measure.pi fun _ : J ↦ mu) =
      Measure.pi fun _ : J ↦ Measure.pi fun _ : I ↦ mu := by
  let uncurryRows := (MeasurableEquiv.curry I J E).symm
  let swapIndices := MeasurableEquiv.piCongrLeft
    (fun _ : J × I ↦ E) (Equiv.prodComm I J)
  let curryColumns := MeasurableEquiv.curry J I E
  have hfun :
      curryColumns ∘ swapIndices ∘ uncurryRows =
        piTransposeMeasurableEquiv I J E := by
    funext x
    ext j i
    rfl
  have huncurry :
      Measure.map uncurryRows
          (Measure.infinitePi fun _ : I ↦
            Measure.infinitePi fun _ : J ↦ mu) =
        Measure.infinitePi fun _ : I × J ↦ mu := by
    simpa only [uncurryRows] using
      (Measure.infinitePi_map_curry_symm
        (fun _ : I ↦ fun _ : J ↦ mu))
  have hswap :
      Measure.map swapIndices
          (Measure.infinitePi fun _ : I × J ↦ mu) =
        Measure.infinitePi fun _ : J × I ↦ mu := by
    simpa only [swapIndices] using
      (Measure.infinitePi_map_piCongrLeft
        (fun _ : J × I ↦ mu) (Equiv.prodComm I J))
  have hcurry :
      Measure.map curryColumns
          (Measure.infinitePi fun _ : J × I ↦ mu) =
        Measure.infinitePi fun _ : J ↦
          Measure.infinitePi fun _ : I ↦ mu := by
    simpa only [curryColumns] using
      (Measure.infinitePi_map_curry
        (fun _ : J ↦ fun _ : I ↦ mu))
  rw [← Measure.infinitePi_eq_pi, ← Measure.infinitePi_eq_pi]
  simp_rw [← Measure.infinitePi_eq_pi]
  rw [← hfun]
  calc
    Measure.map (curryColumns ∘ swapIndices ∘ uncurryRows)
        (Measure.infinitePi fun _ : I ↦ Measure.infinitePi fun _ : J ↦ mu) =
      Measure.map curryColumns
        (Measure.map swapIndices
          (Measure.map uncurryRows
            (Measure.infinitePi fun _ : I ↦
              Measure.infinitePi fun _ : J ↦ mu))) := by
        rw [Measure.map_map, Measure.map_map]
        · rfl
        all_goals fun_prop
    _ = Measure.map curryColumns
        (Measure.map swapIndices
          (Measure.infinitePi fun _ : I × J ↦ mu)) := by
      rw [huncurry]
    _ = Measure.map curryColumns
        (Measure.infinitePi fun _ : J × I ↦ mu) := by
      rw [hswap]
    _ = Measure.infinitePi fun _ : J ↦
        Measure.infinitePi fun _ : I ↦ mu := by
      exact hcurry


end
end A4Research.InverseStein

import A2.Target

open MeasureTheory MeasureTheory.Measure Set
open scoped BigOperators ENNReal

noncomputable section

namespace A2Research

set_option maxHeartbeats 600000

/-- The actual fiber of a family of restricted Euclidean charts. -/
def chartFiber {I E Y : Type*} (s : I → Set E) (f : I → E → Y) (y : Y) :=
  Σ i : I, {x : E // x ∈ s i ∧ f i x = y}

/-- On injective chart pieces, counting the charts that hit a point is exactly
counting its source fiber. -/
def chartFiberImageIndexEquiv {I E Y : Type*}
    (s : I → Set E) (f : I → E → Y) (y : Y)
    (hinj : ∀ i, InjOn (f i) (s i)) :
    chartFiber s f y ≃ {i : I // y ∈ f i '' s i} :=
  Equiv.ofBijective
    (fun p ↦ ⟨p.1, ⟨p.2.1, p.2.2.1, p.2.2.2⟩⟩)
    ⟨by
      rintro ⟨i, x⟩ ⟨j, z⟩ h
      have hij : i = j := congrArg Subtype.val h
      subst j
      have hxz : x = z := Subtype.ext (hinj i x.2.1 z.2.1 (x.2.2.trans z.2.2.symm))
      subst z
      rfl,
    by
      rintro ⟨i, hi⟩
      obtain ⟨x, hx, hfx⟩ := hi
      exact ⟨⟨i, ⟨x, hx, hfx⟩⟩, rfl⟩⟩

theorem tsum_imageIndicators_eq_card {I E Y : Type*}
    (s : I → Set E) (f : I → E → Y) (y : Y)
    (hinj : ∀ i, InjOn (f i) (s i)) (k : ℕ)
    (hcard : Nonempty (chartFiber s f y ≃ Fin k)) :
    (∑' i : I, (f i '' s i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y) = k := by
  classical
  let e := chartFiberImageIndexEquiv s f y hinj
  let a : Set I := {i | y ∈ f i '' s i}
  let r := hcard.some
  calc
    (∑' i : I, (f i '' s i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y) =
        ∑' i : I, a.indicator (fun _ ↦ (1 : ℝ≥0∞)) i := by
      congr 1
    _ = ∑' i : a, (1 : ℝ≥0∞) := (tsum_subtype a (fun _ ↦ (1 : ℝ≥0∞))).symm
    _ = ∑' x : chartFiber s f y, (1 : ℝ≥0∞) := (e.tsum_eq (fun _ ↦ (1 : ℝ≥0∞))).symm
    _ = ∑' x : Fin k, (1 : ℝ≥0∞) := r.tsum_eq (fun _ ↦ (1 : ℝ≥0∞))
    _ = k := by simp

/-- The finite-fiber area formula obtained directly from the Euclidean
Jacobian theorem. Each piece is injective, while the complete source has
exactly `k` points above every target point. -/
theorem sum_map_withDensity_abs_det_eq_finite_cover
    {I E : Type*} [Countable I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (s : I → Set E) (f : I → E → E) (f' : I → E → E →L[ℝ] E)
    (hs : ∀ i, MeasurableSet (s i))
    (hf' : ∀ i x, x ∈ s i → HasFDerivWithinAt (f i) (f' i x) (s i) x)
    (hinj : ∀ i, InjOn (f i) (s i))
    (t : Set E) (ht : MeasurableSet t) (himage : ∀ i, f i '' s i ⊆ t)
    (k : ℕ) (hcard : ∀ y ∈ t, Nonempty (chartFiber s f y ≃ Fin k)) :
    Measure.sum (fun i ↦ Measure.map (f i)
      ((μ.restrict (s i)).withDensity (fun x ↦ ENNReal.ofReal |(f' i x).det|))) =
      (k : ℝ≥0∞) • μ.restrict t := by
  classical
  have him : ∀ i, MeasurableSet (f i '' s i) := fun i ↦
    measurable_image_of_fderivWithin (hs i) (hf' i) (hinj i)
  have hcount : (fun y ↦ ∑' i : I,
      (f i '' s i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y) =
      t.indicator (fun _ ↦ (k : ℝ≥0∞)) := by
    funext y
    by_cases hy : y ∈ t
    · rw [indicator_of_mem hy]
      exact tsum_imageIndicators_eq_card s f y hinj k (hcard y hy)
    · rw [indicator_of_notMem hy]
      have hz (i : I) : (f i '' s i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y = 0 :=
        indicator_of_notMem (fun hi ↦ hy (himage i hi)) _
      simp only [hz, tsum_zero]
  calc
    _ = Measure.sum (fun i ↦ μ.restrict (f i '' s i)) := by
      congr 1
      funext i
      exact map_withDensity_abs_det_fderiv_eq_addHaar μ
        (hs i).nullMeasurableSet (hf' i) (hinj i)
    _ = μ.withDensity (fun y ↦ ∑' i : I,
        (f i '' s i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y) := by
      have hfun : (fun y ↦ ∑' i : I,
          (f i '' s i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y) =
          ∑' i : I, (f i '' s i).indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
        funext y
        exact (tsum_apply (Pi.summable.2 fun _ ↦ ENNReal.summable)).symm
      rw [hfun]
      rw [withDensity_tsum (fun i ↦ measurable_const.indicator (him i))]
      congr 1
      funext i
      exact (withDensity_indicator_one (him i)).symm
    _ = μ.withDensity (t.indicator (fun _ ↦ (k : ℝ≥0∞))) := by rw [hcount]
    _ = (k : ℝ≥0∞) • μ.restrict t := by
      rw [withDensity_indicator ht, withDensity_const]

end A2Research

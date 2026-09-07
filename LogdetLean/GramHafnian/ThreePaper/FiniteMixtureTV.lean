import LogdetLean.GramHafnian.UltimateHiding.Basic

/-!
# Total variation for finite mixtures

The elementary mixture bookkeeping used by UH4.  All component comparison
bounds are explicit hypotheses; the file contains no model-specific axiom.
-/

open scoped BigOperators ENNReal
open MeasureTheory Set

namespace LogdetLean.GramHafnian.ThreePaper.FiniteMixtureTV

noncomputable section

open LocalAnticoncentration UltimateHiding

/-- A finite mixture with nonnegative-real weights. -/
def finiteMixture
    {iota beta : Type*} [Fintype iota] [MeasurableSpace beta]
    (w : iota -> NNReal) (mu : iota -> Measure beta) : Measure beta :=
  ∑ i, w i • mu i

lemma finiteMixture_real_apply
    {iota beta : Type*} [Fintype iota] [MeasurableSpace beta]
    (w : iota -> NNReal) (mu : iota -> Measure beta)
    [∀ i, IsFiniteMeasure (mu i)] (s : Set beta) :
    (finiteMixture w mu).real s =
      ∑ i, (w i : Real) * (mu i).real s := by
  unfold finiteMixture
  simp only [Measure.real, Measure.finsetSum_apply,
    Measure.coe_nnreal_smul_apply]
  rw [ENNReal.toReal_sum (by finiteness)]
  simp

/-- Total variation is convex under a common finite mixing law. -/
theorem probabilityTotalVariationLE_finiteMixture
    {iota beta : Type*} [Fintype iota] [MeasurableSpace beta]
    (w : iota -> NNReal) (mu nu : iota -> Measure beta)
    [∀ i, IsFiniteMeasure (mu i)] [∀ i, IsFiniteMeasure (nu i)]
    (delta : iota -> Real)
    (htv : ∀ i, probabilityTotalVariationLE (mu i) (nu i) (delta i)) :
    probabilityTotalVariationLE (finiteMixture w mu) (finiteMixture w nu)
      (∑ i, (w i : Real) * delta i) := by
  refine ⟨Finset.sum_nonneg fun i _ =>
    mul_nonneg (NNReal.coe_nonneg _) (htv i).nonneg, ?_⟩
  intro s hs
  rw [finiteMixture_real_apply, finiteMixture_real_apply]
  calc
    |(∑ i, (w i : Real) * (mu i).real s) -
        ∑ i, (w i : Real) * (nu i).real s| =
        |∑ i, (w i : Real) * ((mu i).real s - (nu i).real s)| := by
      congr 1
      simp only [mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ i, |(w i : Real) * ((mu i).real s - (nu i).real s)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, (w i : Real) * |(mu i).real s - (nu i).real s| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg (NNReal.coe_nonneg _)]
    _ ≤ ∑ i, (w i : Real) * delta i := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left ((htv i).2 s hs) (NNReal.coe_nonneg _)

/-- If every component has the same bound and the weights sum to one, the
mixture has that same bound. -/
theorem probabilityTotalVariationLE_finiteMixture_const
    {iota beta : Type*} [Fintype iota] [MeasurableSpace beta]
    (w : iota -> NNReal) (mu nu : iota -> Measure beta)
    [∀ i, IsFiniteMeasure (mu i)] [∀ i, IsFiniteMeasure (nu i)]
    (hweight : ∑ i, (w i : Real) = 1)
    {delta : Real}
    (htv : ∀ i, probabilityTotalVariationLE (mu i) (nu i) delta) :
    probabilityTotalVariationLE (finiteMixture w mu) (finiteMixture w nu)
      delta := by
  have h := probabilityTotalVariationLE_finiteMixture w mu nu
    (fun _ => delta) htv
  convert h using 1
  rw [← Finset.sum_mul, hweight, one_mul]

/-- The total weight of a declared bad subset of the finite mask space. -/
def badWeight
    {iota : Type*} [Fintype iota]
    (w : iota -> NNReal) (bad : iota -> Prop) [DecidablePred bad] : Real :=
  ∑ i with bad i, (w i : Real)

/-- Good components cost `delta`; arbitrary bad components cost their total
mixing weight.  This is the exact `delta + beta` ledger used in UH4. -/
theorem probabilityTotalVariationLE_finiteMixture_good_bad
    {iota beta : Type*} [Fintype iota] [MeasurableSpace beta]
    (w : iota -> NNReal) (mu nu : iota -> Measure beta)
    [∀ i, IsProbabilityMeasure (mu i)] [∀ i, IsProbabilityMeasure (nu i)]
    (hweight : ∑ i, (w i : Real) = 1)
    (bad : iota -> Prop) [DecidablePred bad]
    {delta : Real} (hdelta : 0 <= delta)
    (hgood : ∀ i, ¬ bad i ->
      probabilityTotalVariationLE (mu i) (nu i) delta) :
    probabilityTotalVariationLE (finiteMixture w mu) (finiteMixture w nu)
      (delta + badWeight w bad) := by
  let localError : iota -> Real := fun i => delta + if bad i then 1 else 0
  have hcomponent (i : iota) :
      probabilityTotalVariationLE (mu i) (nu i) (localError i) := by
    by_cases hi : bad i
    · exact (probabilityTotalVariationLE_one (mu i) (nu i)).mono (by
        dsimp [localError]
        simp [hi, hdelta])
    · simpa [localError, hi] using hgood i hi
  have hmix := probabilityTotalVariationLE_finiteMixture w mu nu
    localError hcomponent
  convert hmix using 1
  simp only [localError, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, hweight, one_mul]
  congr 1
  simp [badWeight, Finset.sum_filter]

/-- Attach the finite mask value to each component output before mixing. -/
def taggedFiniteMixture
    {iota beta : Type*} [Fintype iota]
    [MeasurableSpace iota] [MeasurableSpace beta]
    (w : iota -> NNReal) (mu : iota -> Measure beta) :
    Measure (iota × beta) :=
  finiteMixture w (fun i => Measure.map (fun x => (i, x)) (mu i))

/-- Exact finite-mixture comparison for a recorded mask and its conditional
output. -/
theorem probabilityTotalVariationLE_taggedFiniteMixture_const
    {iota beta : Type*} [Fintype iota]
    [MeasurableSpace iota] [MeasurableSpace beta]
    (w : iota -> NNReal) (mu nu : iota -> Measure beta)
    [∀ i, IsProbabilityMeasure (mu i)] [∀ i, IsProbabilityMeasure (nu i)]
    (hweight : ∑ i, (w i : Real) = 1)
    {delta : Real}
    (htv : ∀ i, probabilityTotalVariationLE (mu i) (nu i) delta) :
    probabilityTotalVariationLE (taggedFiniteMixture w mu)
      (taggedFiniteMixture w nu) delta := by
  apply probabilityTotalVariationLE_finiteMixture_const w
    (fun i => Measure.map (fun x => (i, x)) (mu i))
    (fun i => Measure.map (fun x => (i, x)) (nu i)) hweight
  intro i
  exact (htv i).map (measurable_const.prodMk measurable_id)

/-- Tagged version of the good/bad mask ledger. -/
theorem probabilityTotalVariationLE_taggedFiniteMixture_good_bad
    {iota beta : Type*} [Fintype iota]
    [MeasurableSpace iota] [MeasurableSpace beta]
    (w : iota -> NNReal) (mu nu : iota -> Measure beta)
    [∀ i, IsProbabilityMeasure (mu i)] [∀ i, IsProbabilityMeasure (nu i)]
    (hweight : ∑ i, (w i : Real) = 1)
    (bad : iota -> Prop) [DecidablePred bad]
    {delta : Real} (hdelta : 0 <= delta)
    (hgood : ∀ i, ¬ bad i ->
      probabilityTotalVariationLE (mu i) (nu i) delta) :
    probabilityTotalVariationLE (taggedFiniteMixture w mu)
      (taggedFiniteMixture w nu) (delta + badWeight w bad) := by
  letI : ∀ i, IsProbabilityMeasure
      (Measure.map (fun x => (i, x)) (mu i)) := fun _ =>
    Measure.isProbabilityMeasure_map
      (measurable_const.prodMk measurable_id).aemeasurable
  letI : ∀ i, IsProbabilityMeasure
      (Measure.map (fun x => (i, x)) (nu i)) := fun _ =>
    Measure.isProbabilityMeasure_map
      (measurable_const.prodMk measurable_id).aemeasurable
  apply probabilityTotalVariationLE_finiteMixture_good_bad w
    (fun i => Measure.map (fun x => (i, x)) (mu i))
    (fun i => Measure.map (fun x => (i, x)) (nu i)) hweight bad hdelta
  intro i hi
  exact (hgood i hi).map (measurable_const.prodMk measurable_id)

end


end LogdetLean.GramHafnian.ThreePaper.FiniteMixtureTV

#print axioms LogdetLean.GramHafnian.ThreePaper.FiniteMixtureTV.probabilityTotalVariationLE_finiteMixture_const
#print axioms LogdetLean.GramHafnian.ThreePaper.FiniteMixtureTV.probabilityTotalVariationLE_taggedFiniteMixture_good_bad

import A3.Shared.WeylIntegrationFiniteCover

open MeasureTheory MeasureTheory.Measure Set TopologicalSpace Function
open scoped BigOperators ENNReal Topology

noncomputable section

namespace A3Research

set_option maxHeartbeats 600000

/-- A locally injective map on a measurable subset of a second-countable
space admits an actual disjoint measurable partition into injective pieces. -/
theorem exists_measurable_injective_partition
    {E Y : Type*} [TopologicalSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    (s : Set E) (hs : MeasurableSet s) (f : E → Y)
    (hlocal : ∀ x ∈ s, ∃ u : Set E,
      IsOpen u ∧ x ∈ u ∧ InjOn f (s ∩ u)) :
    ∃ p : ℕ → Set E,
      (∀ n, MeasurableSet (p n)) ∧
      Pairwise (Disjoint on p) ∧
      (⋃ n, p n) = s ∧
      (∀ n, p n ⊆ s) ∧
      (∀ n, InjOn f (p n)) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hnonempty
  · refine ⟨fun _ ↦ ∅, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun _ ↦ MeasurableSet.empty
    · intro i j _
      exact disjoint_bot_left
    · simp
    · exact fun _ ↦ subset_rfl
    · exact fun _ ↦ Set.injOn_empty f
  choose u huo hxu hfu using (fun x : s ↦ hlocal x.1 x.2)
  have hcover : s ⊆ ⋃ x : s, u x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxu ⟨x, hx⟩⟩
  obtain ⟨a, hac, hacover⟩ :=
    (HereditarilyLindelofSpace.isLindelof s).elim_countable_subcover u huo hcover
  have hane : a.Nonempty := by
    obtain ⟨x, hx⟩ := hnonempty
    obtain ⟨z, hz, _⟩ := mem_iUnion₂.mp (hacover hx)
    exact ⟨z, hz⟩
  obtain ⟨e, he⟩ := hac.exists_eq_range hane
  let v : ℕ → Set E := fun n ↦ s ∩ u (e n)
  have hv : (⋃ n, v n) = s := by
    apply Subset.antisymm
    · exact iUnion_subset fun _ ↦ inter_subset_left
    · intro x hx
      obtain ⟨z, hz, hzx⟩ := mem_iUnion₂.mp (hacover hx)
      rw [he] at hz
      obtain ⟨n, rfl⟩ := hz
      exact mem_iUnion.mpr ⟨n, hx, hzx⟩
  refine ⟨disjointed v, ?_, disjoint_disjointed v, ?_, ?_, ?_⟩
  · exact MeasurableSet.disjointed (fun n ↦ hs.inter (huo (e n)).measurableSet)
  · rw [iUnion_disjointed, hv]
  · intro n
    exact (disjointed_subset v n).trans inter_subset_left
  · intro n
    exact (hfu (e n)).mono (disjointed_subset v n)

/-- Smoothness and a nonzero real determinant provide the local injectivity
used above, by the proved inverse function theorem. -/
theorem exists_open_injective_of_contDiffAt_det_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f : E → E} {x : E} {A : E →L[ℝ] E}
    (hf : ContDiffAt ℝ 1 f x) (hA : HasFDerivAt f A x) (hdet : A.det ≠ 0) :
    ∃ u : Set E, IsOpen u ∧ x ∈ u ∧ InjOn f u := by
  let e : E ≃L[ℝ] E :=
    (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr hdet)).toContinuousLinearEquiv
  have he : (e : E →L[ℝ] E) = A := by
    ext v
    exact LinearMap.equivOfIsUnitDet_apply _ v
  have hAe : HasFDerivAt f (e : E →L[ℝ] E) x := he.symm ▸ hA
  let g := hf.toOpenPartialHomeomorph f hAe (by norm_num)
  exact ⟨g.source, g.open_source, hf.mem_toOpenPartialHomeomorph_source hAe (by norm_num),
    g.injOn⟩

/-- Subdividing each source chart by a disjoint partition changes no fiber.
This identifies the analytic injective-piece count with the original orbit
representatives. -/
def partitionedChartFiberEquiv
    {I E Y : Type*} (s : I → Set E) (f : I → E → Y)
    (p : I → ℕ → Set E)
    (hp : ∀ i, Pairwise (Disjoint on p i))
    (hcover : ∀ i, (⋃ n, p i n) = s i) (y : Y) :
    chartFiber (fun a : I × ℕ ↦ p a.1 a.2) (fun a ↦ f a.1) y ≃ chartFiber s f y := by
  classical
  have hsub (i : I) (n : ℕ) : p i n ⊆ s i := by
    rw [← hcover i]
    exact subset_iUnion (p i) n
  refine Equiv.ofBijective
    (fun a ↦ ⟨a.1.1, ⟨a.2.1, hsub _ _ a.2.2.1, a.2.2.2⟩⟩) ⟨?_, ?_⟩
  · rintro ⟨⟨i, n⟩, x⟩ ⟨⟨j, m⟩, z⟩ h
    have hij : i = j := congrArg Sigma.fst h
    subst j
    have hxz : x.1 = z.1 := congrArg (fun a : chartFiber s f y ↦ a.2.1) h
    have hnm : n = m := by
      by_contra hnm
      exact Set.disjoint_left.mp (hp i hnm) x.2.1 (hxz.symm ▸ z.2.1)
    subst m
    have hsubxz : x = z := Subtype.ext hxz
    subst z
    rfl
  · rintro ⟨i, x⟩
    have hx : x.1 ∈ ⋃ n, p i n := by rw [hcover i]; exact x.2.1
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact ⟨⟨⟨i, n⟩, ⟨x.1, hn, x.2.2⟩⟩, rfl⟩

/-- The finite-cover area formula for nonsingular `C¹` charts. The countable
injective subdivision and the corresponding fiber count are constructed in
the proof, rather than supplied as additional hypotheses. -/
theorem sum_map_withDensity_abs_det_eq_regular_cover
    {I E : Type*} [Countable I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (s : I → Set E) (f : I → E → E) (f' : I → E → E →L[ℝ] E)
    (hs : ∀ i, MeasurableSet (s i))
    (hf : ∀ i x, x ∈ s i → ContDiffAt ℝ 1 (f i) x)
    (hf' : ∀ i x, x ∈ s i → HasFDerivAt (f i) (f' i x) x)
    (hdet : ∀ i x, x ∈ s i → (f' i x).det ≠ 0)
    (t : Set E) (ht : MeasurableSet t) (himage : ∀ i, f i '' s i ⊆ t)
    (k : ℕ) (hcard : ∀ y ∈ t, Nonempty (chartFiber s f y ≃ Fin k)) :
    Measure.sum (fun i ↦ Measure.map (f i)
      ((μ.restrict (s i)).withDensity (fun x ↦ ENNReal.ofReal |(f' i x).det|))) =
      (k : ℝ≥0∞) • μ.restrict t := by
  classical
  have hpart (i : I) := exists_measurable_injective_partition (s i) (hs i) (f i) (by
    intro x hx
    obtain ⟨u, hu, hxu, hfu⟩ := exists_open_injective_of_contDiffAt_det_ne_zero
      (hf i x hx) (hf' i x hx) (hdet i x hx)
    exact ⟨u, hu, hxu, hfu.mono inter_subset_right⟩)
  choose p hpmeas hpdisj hpcover hpsub hpinj using hpart
  have hsource (i : I) :
      ((μ.restrict (s i)).withDensity (fun x ↦ ENNReal.ofReal |(f' i x).det|)) =
      Measure.sum (fun n ↦ (μ.restrict (p i n)).withDensity
        (fun x ↦ ENNReal.ofReal |(f' i x).det|)) := by
    rw [← hpcover i, restrict_iUnion (hpdisj i) (hpmeas i), withDensity_sum]
  have hfm (i : I) : AEMeasurable (f i)
      ((μ.restrict (s i)).withDensity (fun x ↦ ENNReal.ofReal |(f' i x).det|)) := by
    refine AEMeasurable.mono_ac ?_ (withDensity_absolutelyContinuous _ _)
    have hcont : ContinuousOn (f i) (s i) := fun x hx ↦
      (hf' i x hx).continuousAt.continuousWithinAt
    exact hcont.aemeasurable (hs i)
  have hpieces :
      Measure.sum (fun a : I × ℕ ↦ Measure.map (f a.1)
        ((μ.restrict (p a.1 a.2)).withDensity
          (fun x ↦ ENNReal.ofReal |(f' a.1 x).det|))) =
          (k : ℝ≥0∞) • μ.restrict t := by
    apply sum_map_withDensity_abs_det_eq_finite_cover μ
      (fun a : I × ℕ ↦ p a.1 a.2) (fun a ↦ f a.1) (fun a ↦ f' a.1)
      (fun a ↦ hpmeas a.1 a.2)
      (fun a x hx ↦ (hf' a.1 x (hpsub a.1 a.2 hx)).hasFDerivWithinAt)
      (fun a ↦ hpinj a.1 a.2) t ht
      (fun a ↦ (image_mono (hpsub a.1 a.2)).trans (himage a.1)) k
    intro y hy
    exact ⟨(partitionedChartFiberEquiv (s := s) f p hpdisj hpcover y).trans
      (hcard y hy).some⟩
  calc
    _ = Measure.sum (fun i ↦ Measure.sum (fun n ↦ Measure.map (f i)
        ((μ.restrict (p i n)).withDensity
          (fun x ↦ ENNReal.ofReal |(f' i x).det|)))) := by
      congr 1
      funext i
      rw [hsource i]
      apply Measure.map_sum
      rw [← hsource i]
      exact hfm i
    _ = _ := by rw [Measure.sum_sum]; exact hpieces

end A3Research

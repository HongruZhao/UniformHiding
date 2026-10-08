import A2.OrbitMeasureChartPartition

open MeasureTheory MeasureTheory.Measure Set Function TopologicalSpace Metric
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

noncomputable section

namespace A2Research

set_option maxHeartbeats 600000

/-- Every identity neighborhood in a compact group has an actual finite
cover by left translates. The covering family is nonempty. -/
theorem exists_finite_left_translates_cover
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (v : Set G) (hv : IsOpen v) (h1 : 1 ∈ v) :
    ∃ c : Finset G, c.Nonempty ∧
      ∀ g : G, ∃ a ∈ c, a⁻¹ * g ∈ v := by
  classical
  let u : G → Set G := fun a ↦ (fun g ↦ a⁻¹ * g) ⁻¹' v
  have hu : ∀ a, IsOpen (u a) := fun a ↦ hv.preimage (by fun_prop)
  have hcover : (univ : Set G) ⊆ ⋃ a, u a := by
    intro g _
    refine mem_iUnion.mpr ⟨g, ?_⟩
    simpa only [u, mem_preimage, inv_mul_cancel] using h1
  obtain ⟨c, hc⟩ := isCompact_univ.elim_finite_subcover u hu hcover
  have he (g : G) : ∃ a ∈ c, a⁻¹ * g ∈ v := by
    obtain ⟨a, ha, hga⟩ := mem_iUnion₂.mp (hc (mem_univ g))
    exact ⟨a, ha, hga⟩
  obtain ⟨a, ha, _⟩ := he 1
  exact ⟨c, ⟨a, ha⟩, he⟩

/-- Continuous angular densities have finite mass on each bounded chart
piece. No Haar normalization or manifold-volume formula is assumed. -/
theorem angular_density_mass_lt_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (r : ℝ) (s : Set E) (hs : s ⊆ ball (0 : E) r)
    (h : E → ℝ) (hh : Continuous h) :
    (∫⁻ x in s, ENNReal.ofReal (h x) ∂μ) < ∞ := by
  have hint : IntegrableOn h (closedBall (0 : E) r) μ :=
    hh.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hs' : s ⊆ closedBall (0 : E) r := hs.trans ball_subset_closedBall
  have hfin : (∫⁻ x in s, ‖h x‖ₑ ∂μ) < ∞ := (hint.mono_set hs').hasFiniteIntegral
  exact lt_of_le_of_lt (lintegral_mono (fun x ↦ Real.ofReal_le_enorm (h x))) hfin

theorem angular_density_ball_mass_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (r : ℝ) (hr : 0 < r) (h : E → ℝ) (hh : Continuous h)
    (hpos : ∀ x ∈ ball (0 : E) r, 0 < h x) :
    0 < (∫⁻ x in ball (0 : E) r, ENNReal.ofReal (h x) ∂μ) := by
  have hs : Function.support (fun x ↦ ENNReal.ofReal (h x)) ∩ ball (0 : E) r =
      ball (0 : E) r := by
    apply inter_eq_right.mpr
    intro x hx
    exact (ENNReal.ofReal_pos.mpr (hpos x hx)).ne'
  rw [setLIntegral_pos_iff (hh.measurable.ennreal_ofReal), hs]
  exact isOpen_ball.measure_pos μ ⟨0, mem_ball_self hr⟩

/-- The sum of angular masses of a finite disjoint atlas is strictly
positive and finite: its first source piece is the full ball, and every
other piece lies in that same bounded coordinate ball. -/
theorem angular_atlas_mass_pos_lt_top
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ] (n : ℕ)
    (r : ℝ) (hr : 0 < r) (φ : Fin (n + 1) → E → G)
    (h : E → ℝ) (hh : Continuous h)
    (hpos : ∀ x ∈ ball (0 : E) r, 0 < h x) :
    0 < (∑ i : Fin (n + 1), ∫⁻ x in angularChartPiece (ball (0 : E) r) φ i,
      ENNReal.ofReal (h x) ∂μ) ∧
      (∑ i : Fin (n + 1), ∫⁻ x in angularChartPiece (ball (0 : E) r) φ i,
        ENNReal.ofReal (h x) ∂μ) < ∞ := by
  classical
  constructor
  · have hzero : angularChartPiece (ball (0 : E) r) φ (0 : Fin (n + 1)) =
        ball (0 : E) r := angularChartPiece_bot _ _
    have hp : 0 < ∫⁻ x in angularChartPiece (ball (0 : E) r) φ (0 : Fin (n + 1)),
        ENNReal.ofReal (h x) ∂μ := by
      rw [hzero]
      exact angular_density_ball_mass_pos μ r hr h hh hpos
    exact hp.trans_le (Finset.single_le_sum
      (f := fun i : Fin (n + 1) ↦ ∫⁻ x in angularChartPiece (ball (0 : E) r) φ i,
        ENNReal.ofReal (h x) ∂μ)
      (fun _ _ ↦ zero_le) (Finset.mem_univ (0 : Fin (n + 1))))
  · exact ENNReal.sum_lt_top.mpr (fun i _ ↦ angular_density_mass_lt_top μ r _
      (angularChartPiece_subset _ _ i) h hh)

end A2Research

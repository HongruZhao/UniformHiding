import A2.WeylIntegrationLocalPartition

open MeasureTheory MeasureTheory.Measure Set Function
open scoped BigOperators ENNReal

noncomputable section

namespace A2Research

set_option maxHeartbeats 600000

/-- Pushing forward a density pulled back along a measurable map commutes
with that density. This uses the actual pushforward integral identity. -/
theorem map_withDensity_comp
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (g : X → Y) (hg : Measurable g)
    (h : Y → ℝ≥0∞) (hh : Measurable h) :
    Measure.map g (μ.withDensity (h ∘ g)) = (Measure.map g μ).withDensity h := by
  ext s hs
  rw [Measure.map_apply hg hs, withDensity_apply _ (hs.preimage hg), withDensity_apply _ hs]
  exact (setLIntegral_map hs hh hg).symm

/-- Integrating a separated density against a radial test gives its actual
angular mass times the radial pushforward. The test target is arbitrary. -/
theorem map_radial_test_separated_density
    {A R Y : Type*} [MeasurableSpace A] [MeasurableSpace R] [MeasurableSpace Y]
    (μ : Measure A) (ν : Measure R) [SFinite μ] [SFinite ν]
    (s : Set A) (p : Set R) (a : A → ℝ≥0∞) (b : R → ℝ≥0∞)
    (ha : Measurable a) (hb : Measurable b) (F : R → Y) (hF : Measurable F) :
    Measure.map (F ∘ Prod.snd)
      (((μ.prod ν).restrict (s ×ˢ p)).withDensity (fun z ↦ a z.1 * b z.2)) =
      (∫⁻ x in s, a x ∂μ) • Measure.map F ((ν.restrict p).withDensity b) := by
  rw [← prod_restrict, ← prod_withDensity ha hb,
    ← Measure.map_map hF measurable_snd, map_snd_prod, Measure.map_smul]
  congr 1
  rw [withDensity_apply _ MeasurableSet.univ]
  simp

/-- The radial/angular coordinate change has normalization exactly one.
Only its proved measure-preservation is used here. -/
theorem map_split_radial_test_separated_density
    {E A R Y : Type*} [MeasurableSpace E] [MeasurableSpace A]
    [MeasurableSpace R] [MeasurableSpace Y]
    (μ : Measure E) (μa : Measure A) (μr : Measure R) [SFinite μa] [SFinite μr]
    (e : E ≃ᵐ A × R) (he : MeasurePreserving e μ (μa.prod μr))
    (s : Set A) (p : Set R) (hs : MeasurableSet s) (hp : MeasurableSet p)
    (a : A → ℝ≥0∞) (b : R → ℝ≥0∞) (ha : Measurable a) (hb : Measurable b)
    (F : R → Y) (hF : Measurable F) :
    Measure.map (fun x ↦ F (e x).2)
      ((μ.restrict (e ⁻¹' (s ×ˢ p))).withDensity
        (fun x ↦ a (e x).1 * b (e x).2)) =
      (∫⁻ x in s, a x ∂μa) • Measure.map F ((μr.restrict p).withDensity b) := by
  have hm : Measurable (fun z : A × R ↦ a z.1 * b z.2) :=
    (ha.comp measurable_fst).mul (hb.comp measurable_snd)
  have hmapped : Measure.map e
      ((μ.restrict (e ⁻¹' (s ×ˢ p))).withDensity
        (fun x ↦ a (e x).1 * b (e x).2)) =
      ((μa.prod μr).restrict (s ×ˢ p)).withDensity (fun z ↦ a z.1 * b z.2) := by
    change Measure.map e ((μ.restrict (e ⁻¹' (s ×ˢ p))).withDensity
      ((fun z : A × R ↦ a z.1 * b z.2) ∘ e)) = _
    rw [map_withDensity_comp _ e e.measurable _ hm,
      ← restrict_map e.measurable (hs.prod hp), he.map_eq]
  have hcomp : (fun x : E ↦ F (e x).2) = (F ∘ Prod.snd) ∘ e := rfl
  rw [hcomp, ← Measure.map_map (hF.comp measurable_snd) e.measurable, hmapped]
  exact map_radial_test_separated_density μa μr s p a b ha hb F hF

theorem sum_smul_measure
    {I Y : Type*} [MeasurableSpace Y] (w : I → ℝ≥0∞) (ν : Measure Y) :
    Measure.sum (fun i ↦ w i • ν) = (∑' i, w i) • ν := by
  ext s hs
  rw [Measure.sum_apply _ hs]
  simp only [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.tsum_mul_right

/-- Once the concrete regular orbit maps and their exact fiber count are
proved, the Euclidean area formula and separated Jacobian yield the raw
symmetric-test pushforward, with no restriction on the measurable target. -/
theorem map_test_eq_separated_regular_cover
    {I E A R Y : Type*} [Countable I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace A]
    [MeasurableSpace R] [MeasurableSpace Y]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (μa : Measure A) (μr : Measure R) [SFinite μa] [SFinite μr]
    (e : E ≃ᵐ A × R) (he : MeasurePreserving e μ (μa.prod μr))
    (s : I → Set A) (p : Set R) (hs : ∀ i, MeasurableSet (s i)) (hp : MeasurableSet p)
    (f : I → E → E) (f' : I → E → E →L[ℝ] E)
    (hfm : ∀ i, Measurable (f i))
    (hf : ∀ i x, e x ∈ s i ×ˢ p → ContDiffAt ℝ 1 (f i) x)
    (hf' : ∀ i x, e x ∈ s i ×ˢ p → HasFDerivAt (f i) (f' i x) x)
    (hdet : ∀ i x, e x ∈ s i ×ˢ p → (f' i x).det ≠ 0)
    (t : Set E) (ht : MeasurableSet t) (htae : ∀ᵐ x ∂μ, x ∈ t)
    (himage : ∀ i, f i '' (e ⁻¹' (s i ×ˢ p)) ⊆ t)
    (k : ℕ) (hk : 0 < k)
    (hcard : ∀ y ∈ t,
      Nonempty (chartFiber (fun i ↦ e ⁻¹' (s i ×ˢ p)) f y ≃ Fin k))
    (a : A → ℝ≥0∞) (b : R → ℝ≥0∞) (ha : Measurable a) (hb : Measurable b)
    (hjac : ∀ i x, e x ∈ s i ×ˢ p →
      ENNReal.ofReal |(f' i x).det| = a (e x).1 * b (e x).2)
    (S : E → Y) (hS : Measurable S) (F : R → Y) (hF : Measurable F)
    (htest : ∀ i x, e x ∈ s i ×ˢ p → S (f i x) = F (e x).2) :
    Measure.map S μ =
      ((k : ℝ≥0∞)⁻¹ * ∑' i, ∫⁻ x in s i, a x ∂μa) •
        Measure.map F ((μr.restrict p).withDensity b) := by
  have hdom (i : I) : MeasurableSet (e ⁻¹' (s i ×ˢ p)) :=
    (hs i).prod hp |>.preimage e.measurable
  let ρ (i : I) := (μ.restrict (e ⁻¹' (s i ×ˢ p))).withDensity
    (fun x ↦ ENNReal.ofReal |(f' i x).det|)
  have harea : Measure.sum (fun i ↦ Measure.map (f i) (ρ i)) = (k : ℝ≥0∞) • μ := by
    rw [← restrict_eq_self_of_ae_mem htae]
    exact sum_map_withDensity_abs_det_eq_regular_cover μ
      (fun i ↦ e ⁻¹' (s i ×ˢ p)) f f' hdom hf hf' hdet t ht himage k hcard
  have hrho (i : I) : ρ i =
      (μ.restrict (e ⁻¹' (s i ×ˢ p))).withDensity
        (fun x ↦ a (e x).1 * b (e x).2) := by
    apply withDensity_congr_ae
    exact (ae_restrict_mem (hdom i)).mono (hjac i)
  have hpush (i : I) : Measure.map S (Measure.map (f i) (ρ i)) =
      (∫⁻ x in s i, a x ∂μa) • Measure.map F ((μr.restrict p).withDensity b) := by
    rw [Measure.map_map hS (hfm i)]
    have htestae : (S ∘ f i) =ᵐ[ρ i] (fun x ↦ F (e x).2) :=
      ((ae_restrict_mem (hdom i)).mono (htest i)).filter_mono
        (withDensity_absolutelyContinuous _ _).ae_le
    rw [Measure.map_congr htestae, hrho i]
    exact map_split_radial_test_separated_density μ μa μr e he
      (s i) p (hs i) hp a b ha hb F hF
  have htotal : (k : ℝ≥0∞) • Measure.map S μ =
      (∑' i, ∫⁻ x in s i, a x ∂μa) • Measure.map F ((μr.restrict p).withDensity b) := by
    calc
      _ = Measure.map S (Measure.sum (fun i ↦ Measure.map (f i) (ρ i))) := by
        rw [harea, Measure.map_smul]
      _ = Measure.sum (fun i ↦ Measure.map S (Measure.map (f i) (ρ i))) :=
        Measure.map_sum hS.aemeasurable
      _ = _ := by
        simp_rw [hpush]
        exact sum_smul_measure _ _
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk.ne'
  have hkfin : (k : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hscaled := congrArg (fun ν : Measure Y ↦ (k : ℝ≥0∞)⁻¹ • ν) htotal
  simpa only [smul_smul, ENNReal.inv_mul_cancel hk0 hkfin, one_smul] using hscaled

end A2Research

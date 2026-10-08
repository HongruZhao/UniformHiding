import A3.WishartGaussianDensity
import A3.WishartCholeskyCoordinates
import A3.WishartProductDensity

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal

noncomputable section

namespace A3Research

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [RCLike K] [MeasureSpace K] [BorelSpace K]

def wishartBartlettShape (alpha : ℝ) {n : ℕ} (K : Type*) [RCLike K] (i : Fin n) : ℝ :=
  alpha - (Module.finrank ℝ K : ℝ) * (i : ℝ) / 2

/-- The independent squared-pivot Bartlett law in the actual Hermitian coordinates. -/
def wishartBartlettMeasure (n : ℕ) (alpha : ℝ) (gaussianField : Measure K) :
    Measure (HermitianCoordinates n K) :=
  (Measure.pi (fun i : Fin n ↦ gammaMeasure (wishartBartlettShape alpha K i) 1)).prod
    (Measure.pi (fun _ : HermitianCoordinateIndex n ↦ gaussianField))

def wishartRealBartlettMeasure (n : ℕ) (alpha : ℝ) : Measure (HermitianCoordinates n ℝ) :=
  wishartBartlettMeasure n alpha (gaussianReal 0 (1 / 2))

def wishartComplexBartlettMeasure (n : ℕ) (alpha : ℝ) : Measure (HermitianCoordinates n ℂ) :=
  wishartBartlettMeasure n alpha LogdetLean.GramHafnian.circularGaussian

@[simp] theorem wishartBartlettShape_real (alpha : ℝ) (i : Fin n) :
    wishartBartlettShape alpha ℝ i = alpha - (i : ℝ) / 2 := by
  simp [wishartBartlettShape]

@[simp] theorem wishartBartlettShape_complex (alpha : ℝ) (i : Fin n) :
    wishartBartlettShape alpha ℂ i = alpha - (i : ℝ) := by
  simp [wishartBartlettShape, Complex.finrank_real_complex]

theorem wishartBartlettMeasure_probability {n : ℕ} {alpha : ℝ}
    (gaussianField : Measure K) [IsProbabilityMeasure gaussianField]
    (ha : ∀ i : Fin n, 0 < wishartBartlettShape alpha K i) :
    IsProbabilityMeasure (wishartBartlettMeasure n alpha gaussianField) := by
  letI (i : Fin n) : IsProbabilityMeasure (gammaMeasure (wishartBartlettShape alpha K i) 1) :=
    isProbabilityMeasure_gammaMeasure (ha i) (by norm_num)
  unfold wishartBartlettMeasure
  infer_instance

theorem wishartGammaMeasure_ae_pos (a r : ℝ) : ∀ᵐ x ∂gammaMeasure a r, 0 < x := by
  rw [gammaMeasure, ae_withDensity_iff]
  · filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
    intro hpdf
    by_contra hpos
    have hneg : x < 0 := lt_of_le_of_ne (not_lt.mp hpos) hx
    exact hpdf (gammaPDF_of_neg hneg)
  · exact (measurable_gammaPDFReal a r).ennreal_ofReal

theorem wishartBartlettMeasure_ae_domain {n : ℕ} {alpha : ℝ}
    (gaussianField : Measure K) [IsProbabilityMeasure gaussianField]
    (ha : ∀ i : Fin n, 0 < wishartBartlettShape alpha K i) :
    ∀ᵐ x ∂wishartBartlettMeasure n alpha gaussianField,
      x ∈ wishartCholeskyDomain n K := by
  letI (i : Fin n) : IsProbabilityMeasure (gammaMeasure (wishartBartlettShape alpha K i) 1) :=
    isProbabilityMeasure_gammaMeasure (ha i) (by norm_num)
  have hp : ∀ᵐ q ∂Measure.pi (fun i : Fin n ↦ gammaMeasure (wishartBartlettShape alpha K i) 1),
      ∀ i, 0 < q i :=
    Filter.eventually_all.mpr fun i ↦ Measure.tendsto_eval_ae_ae.eventually
      (wishartGammaMeasure_ae_pos (wishartBartlettShape alpha K i) 1)
  exact Measure.quasiMeasurePreserving_fst.ae hp

theorem wishartBartlettShape_real_rows_pos {n rows : ℕ} (hn : n ≤ rows) (i : Fin n) :
    0 < wishartBartlettShape ((rows : ℝ) / 2) ℝ i := by
  rw [wishartBartlettShape_real]
  have hi : (i : ℝ) < rows := by exact_mod_cast lt_of_lt_of_le i.isLt hn
  linarith

theorem wishartBartlettShape_complex_rows_pos {n rows : ℕ} (hn : n ≤ rows) (i : Fin n) :
    0 < wishartBartlettShape (rows : ℝ) ℂ i := by
  rw [wishartBartlettShape_complex]
  have hi : (i : ℝ) < rows := by exact_mod_cast lt_of_lt_of_le i.isLt hn
  linarith

def wishartBartlettDensity (n : ℕ) (alpha : ℝ) (g : K → ℝ≥0∞)
    (x : HermitianCoordinates n K) : ℝ≥0∞ :=
  (∏ i, gammaPDF (wishartBartlettShape alpha K i) 1 (x.1 i)) * ∏ ij, g (x.2 ij)

theorem measurable_wishartBartlettDensity (n : ℕ) (alpha : ℝ)
    (g : K → ℝ≥0∞) (hg : Measurable g) : Measurable (wishartBartlettDensity n alpha g) := by
  unfold wishartBartlettDensity
  apply Measurable.mul
  · apply Finset.univ.measurable_prod
    intro i _
    exact ((measurable_gammaPDFReal _ _).ennreal_ofReal).comp
      ((measurable_pi_apply i).comp measurable_fst)
  · apply Finset.univ.measurable_prod
    intro ij _
    exact hg.comp ((measurable_pi_apply ij).comp measurable_snd)

/-- The literal Gamma/Gaussian source has its product density in the shared coordinates. -/
theorem wishartBartlettMeasure_eq_withDensity
    [SigmaFinite (volume : Measure K)] {n : ℕ} {alpha : ℝ}
    (gaussianField : Measure K) [IsProbabilityMeasure gaussianField]
    (g : K → ℝ≥0∞) (hg : Measurable g)
    (hgauss : gaussianField = (volume : Measure K).withDensity g)
    (ha : ∀ i : Fin n, 0 < wishartBartlettShape alpha K i) :
    wishartBartlettMeasure n alpha gaussianField =
      (hermitianCoordinateVolume n K).withDensity (wishartBartlettDensity n alpha g) := by
  letI (i : Fin n) : IsProbabilityMeasure (gammaMeasure (wishartBartlettShape alpha K i) 1) :=
    isProbabilityMeasure_gammaMeasure (ha i) (by norm_num)
  letI : IsProbabilityMeasure ((volume : Measure K).withDensity g) := by
    rw [← hgauss]
    infer_instance
  letI (i : Fin n) : SigmaFinite ((volume : Measure ℝ).withDensity
      (gammaPDF (wishartBartlettShape alpha K i) 1)) := by
    change SigmaFinite (gammaMeasure (wishartBartlettShape alpha K i) 1)
    infer_instance
  unfold wishartBartlettMeasure
  simp_rw [gammaMeasure, hgauss]
  rw [wishart_pi_withDensity (fun _ : Fin n ↦ (volume : Measure ℝ))
      (fun i ↦ gammaPDF (wishartBartlettShape alpha K i) 1)
      (fun i ↦ (measurable_gammaPDFReal _ _).ennreal_ofReal),
    wishart_pi_withDensity (fun _ : HermitianCoordinateIndex n ↦ (volume : Measure K))
      (fun _ ↦ g) (fun _ ↦ hg),
    prod_withDensity
      (f := fun q : Fin n → ℝ ↦ ∏ i, gammaPDF (wishartBartlettShape alpha K i) 1 (q i))
      (g := fun z : HermitianCoordinateIndex n → K ↦ ∏ ij, g (z ij))
      (Finset.univ.measurable_prod (fun i _ ↦
        (measurable_gammaPDFReal _ _).ennreal_ofReal.comp (measurable_pi_apply i)))
      (Finset.univ.measurable_prod (fun ij _ ↦ hg.comp (measurable_pi_apply ij)))]
  simp only [← MeasureTheory.volume_pi]
  rfl

end A3Research

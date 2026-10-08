import A3.HermitianOrbitFiber

open Set Function MeasureTheory MeasureTheory.Measure
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]

/-- Swapping the independent diagonal and upper coordinates has unit volume
normalization. The Euclidean chart itself retains the diagonal-first model. -/
def hermitianAngularRadialEquiv (n : ℕ) (K : Type*) [MeasurableSpace K] :
    HermitianCoordinates n K ≃ᵐ (HermitianCoordinateIndex n → K) × (Fin n → ℝ) :=
  MeasurableEquiv.prodComm

@[simp] theorem hermitianAngularRadialEquiv_apply [MeasurableSpace K]
    (x : HermitianCoordinates n K) :
    hermitianAngularRadialEquiv n K x = (x.2, x.1) := rfl

theorem measurePreserving_hermitianAngularRadialEquiv
    [MeasureSpace K] [SFinite (volume : Measure (HermitianCoordinateIndex n → K))] :
    MeasurePreserving (hermitianAngularRadialEquiv n K) (hermitianCoordinateVolume n K)
      ((volume : Measure (HermitianCoordinateIndex n → K)).prod
        (volume : Measure (Fin n → ℝ))) := measurePreserving_swap

def preimageChartFiberEquiv
    {I E X Y : Type*} (e : E ≃ X) (s : I → Set X) (f : I → X → Y) (y : Y) :
    chartFiber (fun i ↦ e ⁻¹' s i) (fun i ↦ f i ∘ e) y ≃ chartFiber s f y where
  toFun a := ⟨a.1, ⟨e a.2.1, a.2.2.1, a.2.2.2⟩⟩
  invFun a := ⟨a.1, ⟨e.symm a.2.1, by simpa using a.2.2.1,
    by simpa using a.2.2.2⟩⟩
  left_inv := by
    rintro ⟨i, x⟩
    have hx : e.symm (e x.1) = x.1 := e.symm_apply_apply _
    apply Sigma.ext_iff.mpr
    exact ⟨rfl, heq_of_eq (Subtype.ext hx)⟩
  right_inv := by
    rintro ⟨i, x⟩
    have hx : e (e.symm x.1) = x.1 := e.apply_symm_apply _
    apply Sigma.ext_iff.mpr
    exact ⟨rfl, heq_of_eq (Subtype.ext hx)⟩

theorem canonicalHermitianSpectrum_orbit_permutation
    (U : Matrix.unitaryGroup (Fin n) K) (lambda : Fin n → ℝ) :
    ∃ sigma : Equiv.Perm (Fin n),
      canonicalHermitianSpectrum (hermitianOrbitCoordinates U lambda) = lambda ∘ sigma :=
  canonicalHermitianSpectrum_permutation_of_diagonalization _ U lambda (by
    simpa only [hermitianOrbitMatrix, Matrix.star_eq_conjTranspose,
      Function.comp_def] using hermitianOrbitCoordinates_reconstruct U lambda)

theorem hermitianOrbitCoordinates_mem_regular
    (U : Matrix.unitaryGroup (Fin n) K) (lambda : Fin n → ℝ)
    (hlambda : lambda ∈ regularHermitianRadii n) :
    hermitianOrbitCoordinates U lambda ∈ regularHermitianCoordinateSet n K := by
  obtain ⟨sigma, hsigma⟩ := canonicalHermitianSpectrum_orbit_permutation U lambda
  change Injective (canonicalHermitianSpectrum (hermitianOrbitCoordinates U lambda))
  rw [hsigma]
  exact hlambda.comp sigma.injective

theorem invariant_test_hermitianOrbit {Y : Type} (F : (Fin n → ℝ) → Y)
    (hperm : LogdetLean.GramHafnian.UltimateHiding.DenseScore.IsA2SymmetricTest F)
    (U : Matrix.unitaryGroup (Fin n) K) (lambda : Fin n → ℝ) :
    F (canonicalHermitianSpectrum (hermitianOrbitCoordinates U lambda)) = F lambda := by
  obtain ⟨sigma, hsigma⟩ := canonicalHermitianSpectrum_orbit_permutation U lambda
  rw [hsigma]
  exact hperm sigma lambda

/-- Disjoint angular chart coordinates preserve the exact full radial flag
fiber, in the same Euclidean source model used for the derivative. -/
def regularHermitianAtlasFiberEquiv
    {I : Type*} [LinearOrder I] [LocallyFiniteOrderBot I] [MeasurableSpace K]
    (b : Set (HermitianCoordinateIndex n → K))
    (phi : I → (HermitianCoordinateIndex n → K) → flagSpace n K)
    (hinj : ∀ i, InjOn (phi i) b) (hcover : (⋃ i, phi i '' b) = univ)
    (y : HermitianCoordinates n K) :
    chartFiber
      (fun i ↦ (hermitianAngularRadialEquiv n K) ⁻¹'
        (angularChartPiece b phi i ×ˢ regularHermitianRadii n))
      (fun i x ↦ flagCoordinateEvaluation x.1 (phi i x.2)) y ≃
        RegularHermitianFlagFiber y :=
  (preimageChartFiberEquiv (hermitianAngularRadialEquiv n K).toEquiv
    (fun i ↦ angularChartPiece b phi i ×ˢ regularHermitianRadii n)
    (fun i z ↦ flagCoordinateEvaluation z.2 (phi i z.1)) y).trans
      (angularRadialChartFiberEquiv b phi hinj hcover
        (regularHermitianRadii n) (fun z ↦ flagCoordinateEvaluation z.2 z.1) y)

theorem regularHermitianAtlasFiber_equiv_fin
    {I : Type*} [LinearOrder I] [LocallyFiniteOrderBot I] [MeasurableSpace K]
    (b : Set (HermitianCoordinateIndex n → K))
    (phi : I → (HermitianCoordinateIndex n → K) → flagSpace n K)
    (hinj : ∀ i, InjOn (phi i) b) (hcover : (⋃ i, phi i '' b) = univ)
    (y : HermitianCoordinates n K) (hy : y ∈ regularHermitianCoordinateSet n K) :
    Nonempty (chartFiber
      (fun i ↦ (hermitianAngularRadialEquiv n K) ⁻¹'
        (angularChartPiece b phi i ×ˢ regularHermitianRadii n))
      (fun i x ↦ flagCoordinateEvaluation x.1 (phi i x.2)) y ≃ Fin n.factorial) :=
  ⟨(regularHermitianAtlasFiberEquiv b phi hinj hcover y).trans
    (regularHermitianFlagFiber_equiv_fin y hy).some⟩

theorem flagCoordinateEvaluation_translatedChart
    (U : Matrix.unitaryGroup (Fin n) K) (x : HermitianCoordinates n K) :
    flagCoordinateEvaluation x.1 (flagAction U (hermitianAngularFlagChart x.2)) =
      hermitianCayleyOrbitChart U x := by
  simp only [hermitianAngularFlagChart, flagAction_flagOrbit,
    flagCoordinateEvaluation_flagOrbit, hermitianCayleyOrbitChart]

end A3Research

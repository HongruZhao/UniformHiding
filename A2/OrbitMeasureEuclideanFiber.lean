import A2.WeylIntegrationLiteralBridge
import A2.OrbitMeasureChartPartition
import A2.SpectrumTakagiFiber
import A2.TakagiExistence

open Set Function

noncomputable section

namespace A2Research

/-- A bijective radial/angular coordinate change preserves the actual source
fiber of every restricted orbit chart. -/
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

end A2Research

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

set_option maxHeartbeats 600000

theorem takagiMatrixOfRealCoordinates_injective (N : ℕ) :
    Injective (@takagiMatrixOfRealCoordinates N) := by
  intro x y h
  apply (takagiRealComplexCoordinatesEquiv N).injective
  funext ij
  have he := congrArg (fun C : Matrix (Fin N) (Fin N) ℂ ↦ C ij.1.1 ij.1.2) h
  simpa only [takagiMatrixOfRealCoordinates, complexSymmetricMatrixOfCoordinates,
    dif_pos ij.property] using he

/-- Equality in the actual upper real coordinates is exactly equality in the
represented symmetric matrix. This identifies Euclidean and matrix fibers. -/
def takagiRealOrbitFiberEquiv {N : ℕ} (y : TakagiRealCoordinates N) :
    {z : Matrix.unitaryGroup (Fin N) ℂ × (Fin N → ℝ) //
      z.2 ∈ regularTakagiSquaredRadii N ∧ takagiRealOrbitCoordinates z.1 z.2 = y} ≃
      RegularTakagiFiber (takagiMatrixOfRealCoordinates y) where
  toFun z := ⟨z.1, z.2.1, by
    simpa only [takagiMatrixOfRealCoordinates_takagiRealOrbitCoordinates] using
      congrArg (@takagiMatrixOfRealCoordinates N) z.2.2⟩
  invFun z := ⟨z.1, z.2.1, by
    apply takagiMatrixOfRealCoordinates_injective N
    rw [takagiMatrixOfRealCoordinates_takagiRealOrbitCoordinates]
    exact z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The disjoint angular atlas and the real coordinate split preserve the
literal Takagi fiber, including its signs and permutations. -/
def regularOrbitAtlasFiberEquiv
    {I : Type*} [LinearOrder I] [LocallyFiniteOrderBot I] {N : ℕ}
    (b : Set (TakagiAngularCoordinates N))
    (φ : I → TakagiAngularCoordinates N → Matrix.unitaryGroup (Fin N) ℂ)
    (hinj : ∀ i, InjOn (φ i) b) (hcover : (⋃ i, φ i '' b) = univ)
    (y : TakagiRealCoordinates N) :
    A2Research.chartFiber
      (fun i ↦ (takagiAngularRadialCoordinatesEquiv N) ⁻¹'
        (A2Research.angularChartPiece b φ i ×ˢ regularTakagiSquaredRadii N))
      (fun i x ↦ takagiRealOrbitCoordinates
        (φ i (takagiAngularRadialCoordinatesEquiv N x).1)
        (takagiAngularRadialCoordinatesEquiv N x).2) y ≃
      RegularTakagiFiber (takagiMatrixOfRealCoordinates y) :=
  (A2Research.preimageChartFiberEquiv (takagiAngularRadialCoordinatesEquiv N).toEquiv
    (fun i ↦ A2Research.angularChartPiece b φ i ×ˢ regularTakagiSquaredRadii N)
    (fun i z ↦ takagiRealOrbitCoordinates (φ i z.1) z.2) y).trans
      ((A2Research.angularRadialChartFiberEquiv b φ hinj hcover
        (regularTakagiSquaredRadii N) (fun z ↦ takagiRealOrbitCoordinates z.1 z.2) y).trans
          (takagiRealOrbitFiberEquiv y))

theorem regularOrbitAtlasFiber_equiv_fin_of_representation
    {I : Type*} [LinearOrder I] [LocallyFiniteOrderBot I] {N : ℕ}
    (b : Set (TakagiAngularCoordinates N))
    (φ : I → TakagiAngularCoordinates N → Matrix.unitaryGroup (Fin N) ℂ)
    (hinj : ∀ i, InjOn (φ i) b) (hcover : (⋃ i, φ i '' b) = univ)
    (y : TakagiRealCoordinates N) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (lambda : Fin N → ℝ) (hlambda : IsRegularTakagiSpectrum lambda)
    (hy : takagiMatrixOfRealCoordinates y = takagiOrbit U lambda) :
    Nonempty (A2Research.chartFiber
      (fun i ↦ (takagiAngularRadialCoordinatesEquiv N) ⁻¹'
        (A2Research.angularChartPiece b φ i ×ˢ regularTakagiSquaredRadii N))
      (fun i x ↦ takagiRealOrbitCoordinates
        (φ i (takagiAngularRadialCoordinatesEquiv N x).1)
        (takagiAngularRadialCoordinatesEquiv N x).2) y ≃ Fin (2 ^ N * N.factorial)) :=
  ⟨(regularOrbitAtlasFiberEquiv b φ hinj hcover y).trans
    (regularTakagiFiber_equiv_fin_of_representation
      (takagiMatrixOfRealCoordinates y) U lambda hlambda hy).some⟩

/-- Every point of the actual full-measure regular real-coordinate set has
an actual positive, simple-spectrum Takagi representation. -/
theorem exists_regular_takagi_representation_realCoordinates {N : ℕ}
    (y : TakagiRealCoordinates N) (hy : y ∈ regularTakagiRealMatrixSet N) :
    ∃ (U : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ),
      IsRegularTakagiSpectrum lambda ∧
        takagiMatrixOfRealCoordinates y = takagiOrbit U lambda := by
  let C := takagiMatrixOfRealCoordinates y
  have hCs : C.transpose = C :=
    complexSymmetricMatrixOfCoordinates_isSymm (takagiRealComplexCoordinatesEquiv N y)
  obtain ⟨U, r, hr, hC⟩ := exists_takagi_factorization N C hCs
  obtain ⟨sigma, hsigma⟩ :=
    canonicalGapSquaredSpectrum_permutation_of_unitary_congruence C U r hC
  let lambda : Fin N → ℝ := fun i ↦ r i ^ 2
  have hlambda (i : Fin N) : lambda i = canonicalGapSquaredSpectrum N C (sigma.symm i) := by
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      (congrFun hsigma (sigma.symm i)).symm
  have hy' : IsRegularTakagiSpectrum (canonicalGapSquaredSpectrum N C) := hy
  refine ⟨U, lambda, ⟨fun i ↦ ?_, ?_⟩, ?_⟩
  · rw [hlambda]
    exact hy'.1 _
  · intro i j he
    have hs : sigma.symm i = sigma.symm j := hy'.2 (by rwa [← hlambda, ← hlambda])
    exact sigma.symm.injective hs
  · change C = (U : Matrix (Fin N) (Fin N) ℂ) *
      Matrix.diagonal (fun i ↦ (Real.sqrt (r i ^ 2) : ℂ)) *
        (U : Matrix (Fin N) (Fin N) ℂ).transpose
    simpa only [Real.sqrt_sq (hr _)] using hC

/-- Exact regular Euclidean chart fiber cardinality, now with Takagi
surjectivity proved rather than supplied as a representation premise. -/
theorem regularOrbitAtlasFiber_equiv_fin
    {I : Type*} [LinearOrder I] [LocallyFiniteOrderBot I] {N : ℕ}
    (b : Set (TakagiAngularCoordinates N))
    (φ : I → TakagiAngularCoordinates N → Matrix.unitaryGroup (Fin N) ℂ)
    (hinj : ∀ i, InjOn (φ i) b) (hcover : (⋃ i, φ i '' b) = univ)
    (y : TakagiRealCoordinates N) (hy : y ∈ regularTakagiRealMatrixSet N) :
    Nonempty (A2Research.chartFiber
      (fun i ↦ (takagiAngularRadialCoordinatesEquiv N) ⁻¹'
        (A2Research.angularChartPiece b φ i ×ˢ regularTakagiSquaredRadii N))
      (fun i x ↦ takagiRealOrbitCoordinates
        (φ i (takagiAngularRadialCoordinatesEquiv N x).1)
        (takagiAngularRadialCoordinatesEquiv N x).2) y ≃ Fin (2 ^ N * N.factorial)) := by
  obtain ⟨U, lambda, hlambda, he⟩ :=
    exists_regular_takagi_representation_realCoordinates y hy
  exact regularOrbitAtlasFiber_equiv_fin_of_representation b φ hinj hcover y U lambda hlambda he

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

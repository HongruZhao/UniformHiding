import LogdetLean.GramHafnian.UltimateHiding.UniformlyHidingA1A4Only
import LogdetLean.GramHafnian.UltimateHiding.SquaredNormalized
import LogdetLean.GramHafnian.PRXArticle.EquationEndpoints
import LogdetLean.GramHafnian.Hafnian
import LogdetLean.GramHafnian.ThreePaper.DisjointGaussianRows
import LogdetLean.GramHafnian.ThreePaper.FiniteMixtureTV
import LogdetLean.GramHafnian.ThreePaper.FinitePanelLaws
import LogdetLean.GramHafnian.ThreePaper.OverlapGraphConcentration
import Mathlib.Probability.Moments.SubGaussian

/-!
# PRX Quantum endpoint: uniform transpose-Gram hiding

This is the public import surface for the hiding Article.  Its scientific
closure is exactly A1, A2', A3, and A4.  It contains no anticoncentration
claim.  The observable and event corollaries below are data-processing
consequences of the matrix-law theorem, so applications do not need to reopen
the hiding proof.
-/

open scoped BigOperators ENNReal ProbabilityTheory unitInterval
open Filter MeasureTheory ProbabilityTheory Set

namespace LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding

noncomputable section

open CurrentPRL UltimateHiding

/-- The Article's main finite theorem, with the fully evaluated constant. -/
theorem matrixLaw :
    UniformProductMatrixHidingSquaredAt 615172 :=
  uniformlyHidingSquaredAt_explicitConstant_A1A4Only

/-- The paper-native name for the displayed finite hiding remainder. -/
def hidingRemainder (M N : ℕ) : ℝ :=
  min 1 (615172 * ultimateSquaredHidingRate M N)

/-- The normalized Gaussian reference law is a probability measure. -/
instance normalizedGaussianTransposeGramLaw_isProbability_public (N K : ℕ) :
    IsProbabilityMeasure (normalizedGaussianTransposeGramLaw N K) := by
  letI : IsProbabilityMeasure (gaussianTransposeGramLaw N K) :=
    gaussianTransposeGramLaw_isProbability N K
  exact Measure.isProbabilityMeasure_map
    (measurable_normalizeTransposeGram N K).aemeasurable

/-- The Article's main theorem in its printed normalization: the law of
`(M / sqrt K) U Uᵀ` is hidden by the law of `(1 / sqrt K) G Gᵀ`. -/
theorem normalizedMatrixLaw
    (H : UnitaryHaarProbabilityFamily)
    (M N K : ℕ) (hN : 1 ≤ N) (hNK : N ≤ K) (hKM : K ≤ M) :
    probabilityTotalVariationLE
      (normalizedHaarTransposeGramLaw H M N K)
      (normalizedGaussianTransposeGramLaw N K)
      (min 1 (615172 * ultimateSquaredHidingRate M N)) :=
  normalizedProductMatrixHidingSquared_of_unnormalized
    matrixLaw H hN hNK hKM

/-- The displayed ambient-size rule is sufficient for the requested hiding
budget.  This is pure ordered-field arithmetic applied to the certified
constant, not a further random-matrix input. -/
theorem certifiedHidingError_of_ambient
    (M N : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M)
    {delta : ℝ} (hdelta : 0 < delta)
    (hambient :
      (615172 : ℝ) * ((N : ℝ) ^ 2) / delta ≤ (M : ℝ)) :
    hidingRemainder M N ≤ delta := by
  have hMnat : 0 < M := lt_of_lt_of_le (by omega) hNM
  have hMreal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMnat
  have hambient' :
      (615172 : ℝ) * ((N : ℝ) ^ 2) ≤ (M : ℝ) * delta :=
    (div_le_iff₀ hdelta).mp hambient
  have hrate :
      615172 * ultimateSquaredHidingRate M N ≤ delta := by
    unfold ultimateSquaredHidingRate
    calc
      615172 * ((N : ℝ) ^ 2 / (M : ℝ)) =
          (615172 * (N : ℝ) ^ 2) / (M : ℝ) := by ring
      _ ≤ delta := (div_le_iff₀ hMreal).2 (by
        simpa [mul_comm] using hambient')
  exact (min_le_right _ _).trans hrate

/-! ## Generic data-processing adapters used by the Article -/

/-- Eventwise probability total variation controls the expectation of every
measurable statistic taking values in `[0,1]`.  This is the layer-cake step
used in the Article's bounded-statistic application. -/
private theorem boundedExpectationTransfer_of_probabilityTotalVariationLE
    {α : Type*} [MeasurableSpace α]
    (mu nu : Measure α) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {delta : ℝ}
    (htv : probabilityTotalVariationLE mu nu delta)
    (phi : α → ℝ) (hphi : Measurable phi)
    (hphi_nonneg : ∀ x, 0 ≤ phi x) (hphi_le_one : ∀ x, phi x ≤ 1) :
    |(∫ x, phi x ∂mu) - ∫ x, phi x ∂nu| ≤ delta := by
  have hphi_int_mu : Integrable phi mu := by
    apply (integrable_const (1 : ℝ)).mono hphi.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hphi_nonneg x), norm_one]
    exact hphi_le_one x
  have hphi_int_nu : Integrable phi nu := by
    apply (integrable_const (1 : ℝ)).mono hphi.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hphi_nonneg x), norm_one]
    exact hphi_le_one x
  have htail_meas (xi : Measure α) : Measurable fun t : ℝ ↦
      xi.real {x : α | t ≤ phi x} := by
    apply Measurable.ennreal_toReal
    exact Antitone.measurable fun _ _ hst ↦
      measure_mono (fun _ hx ↦ hst.trans hx)
  have htail_int (xi : Measure α) [IsProbabilityMeasure xi] :
      Integrable (fun t : ℝ ↦ xi.real {x : α | t ≤ phi x})
        (volume.restrict (Ioc (0 : ℝ) 1)) := by
    apply (integrable_const (1 : ℝ)).mono
      (htail_meas xi).aestronglyMeasurable.restrict
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg, norm_one]
    exact measureReal_le_one
  have hmu_layer : (∫ x, phi x ∂mu) =
      ∫ t in Ioc (0 : ℝ) 1, mu.real {x : α | t ≤ phi x} :=
    hphi_int_mu.integral_eq_integral_Ioc_meas_le
      (Eventually.of_forall hphi_nonneg) (Eventually.of_forall hphi_le_one)
  have hnu_layer : (∫ x, phi x ∂nu) =
      ∫ t in Ioc (0 : ℝ) 1, nu.real {x : α | t ≤ phi x} :=
    hphi_int_nu.integral_eq_integral_Ioc_meas_le
      (Eventually.of_forall hphi_nonneg) (Eventually.of_forall hphi_le_one)
  have hdiff_int : Integrable (fun t : ℝ ↦
      mu.real {x : α | t ≤ phi x} - nu.real {x : α | t ≤ phi x})
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (htail_int mu).sub (htail_int nu)
  have habs_int : Integrable (fun t : ℝ ↦
      |mu.real {x : α | t ≤ phi x} - nu.real {x : α | t ≤ phi x}|)
      (volume.restrict (Ioc (0 : ℝ) 1)) := hdiff_int.abs
  have hpoint : ∀ t : ℝ,
      |mu.real {x : α | t ≤ phi x} -
        nu.real {x : α | t ≤ phi x}| ≤ delta := by
    intro t
    exact htv.2 _ (measurableSet_le measurable_const hphi)
  rw [hmu_layer, hnu_layer, ← integral_sub (htail_int mu) (htail_int nu)]
  calc
    |∫ t in Ioc (0 : ℝ) 1,
        (mu.real {x : α | t ≤ phi x} -
          nu.real {x : α | t ≤ phi x})| ≤
        ∫ t in Ioc (0 : ℝ) 1,
          |mu.real {x : α | t ≤ phi x} -
            nu.real {x : α | t ≤ phi x}| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _t in Ioc (0 : ℝ) 1, delta := by
      apply integral_mono_ae habs_int (integrable_const delta)
      filter_upwards [] with t
      exact hpoint t
    _ = delta := by simp

/-- Data processing: every measurable observable of the product matrix is
hidden at the same total-variation error. -/
theorem observableLaw
    {β : Type*} [MeasurableSpace β]
    (H : UnitaryHaarProbabilityFamily)
    (M N K : ℕ) (hN : 1 ≤ N) (hNK : N ≤ K) (hKM : K ≤ M)
    (f : Matrix (Fin N) (Fin N) ℂ → β) (hf : Measurable f) :
    probabilityTotalVariationLE
      (Measure.map f (normalizedHaarTransposeGramLaw H M N K))
      (Measure.map f (normalizedGaussianTransposeGramLaw N K))
      (min 1 (615172 * ultimateSquaredHidingRate M N)) :=
  (normalizedMatrixLaw H M N K hN hNK hKM).map hf

/-- Observable-event transfer in the paper's literal pushforward form. -/
theorem observableEventTransfer
    {β : Type*} [MeasurableSpace β]
    (H : UnitaryHaarProbabilityFamily)
    (M N K : ℕ) (hN : 1 ≤ N) (hNK : N ≤ K) (hKM : K ≤ M)
    (f : Matrix (Fin N) (Fin N) ℂ → β) (hf : Measurable f)
    (s : Set β) (hs : MeasurableSet s) :
    (Measure.map f (normalizedHaarTransposeGramLaw H M N K)).real s ≤
      (Measure.map f (normalizedGaussianTransposeGramLaw N K)).real s +
        min 1 (615172 * ultimateSquaredHidingRate M N) :=
  (observableLaw H M N K hN hNK hKM f hf).event_le hs

/-- The reverse observable-event inequality, obtained from symmetry of total
variation. -/
theorem reverseObservableEventTransfer
    {β : Type*} [MeasurableSpace β]
    (H : UnitaryHaarProbabilityFamily)
    (M N K : ℕ) (hN : 1 ≤ N) (hNK : N ≤ K) (hKM : K ≤ M)
    (f : Matrix (Fin N) (Fin N) ℂ → β) (hf : Measurable f)
    (s : Set β) (hs : MeasurableSet s) :
    (Measure.map f (normalizedGaussianTransposeGramLaw N K)).real s ≤
      (Measure.map f (normalizedHaarTransposeGramLaw H M N K)).real s +
        min 1 (615172 * ultimateSquaredHidingRate M N) :=
  (observableLaw H M N K hN hNK hKM f hf).symm.event_le hs

/-- Event transfer: any measurable property of the normalized product
matrix has physical probability at most its Gaussian probability plus the
certified hiding error. -/
theorem eventTransfer
    (H : UnitaryHaarProbabilityFamily)
    (M N K : ℕ) (hN : 1 ≤ N) (hNK : N ≤ K) (hKM : K ≤ M)
    (s : Set (Matrix (Fin N) (Fin N) ℂ)) (hs : MeasurableSet s) :
    (normalizedHaarTransposeGramLaw H M N K).real s ≤
      (normalizedGaussianTransposeGramLaw N K).real s +
        min 1 (615172 * ultimateSquaredHidingRate M N) :=
  (normalizedMatrixLaw H M N K hN hNK hKM).event_le hs

/-- Reverse event transfer for a measurable matrix event. -/
theorem reverseEventTransfer
    (H : UnitaryHaarProbabilityFamily)
    (M N K : ℕ) (hN : 1 ≤ N) (hNK : N ≤ K) (hKM : K ≤ M)
    (s : Set (Matrix (Fin N) (Fin N) ℂ)) (hs : MeasurableSet s) :
    (normalizedGaussianTransposeGramLaw N K).real s ≤
      (normalizedHaarTransposeGramLaw H M N K).real s +
        min 1 (615172 * ultimateSquaredHidingRate M N) :=
  (normalizedMatrixLaw H M N K hN hNK hKM).symm.event_le hs

/-- Transfer of expectations for an arbitrary measurable `[0,1]`-valued
matrix statistic. -/
theorem boundedStatisticExpectationTransfer
    (H : UnitaryHaarProbabilityFamily)
    (M N K : ℕ) (hN : 1 ≤ N) (hNK : N ≤ K) (hKM : K ≤ M)
    (phi : Matrix (Fin N) (Fin N) ℂ → ℝ)
    (hphi : Measurable phi)
    (hphi_nonneg : ∀ A, 0 ≤ phi A) (hphi_le_one : ∀ A, phi A ≤ 1) :
    |(∫ A, phi A ∂normalizedHaarTransposeGramLaw H M N K) -
        ∫ A, phi A ∂normalizedGaussianTransposeGramLaw N K| ≤
      min 1 (615172 * ultimateSquaredHidingRate M N) :=
  letI : IsProbabilityMeasure (scaledHaarTransposeGramLaw H M N K) :=
    scaledHaarTransposeGramLaw_isProbability H (hNK.trans hKM) hKM
  letI : IsProbabilityMeasure (gaussianTransposeGramLaw N K) :=
    gaussianTransposeGramLaw_isProbability N K
  letI : IsProbabilityMeasure (normalizedHaarTransposeGramLaw H M N K) :=
    Measure.isProbabilityMeasure_map
      (measurable_normalizeTransposeGram N K).aemeasurable
  letI : IsProbabilityMeasure (normalizedGaussianTransposeGramLaw N K) :=
    Measure.isProbabilityMeasure_map
      (measurable_normalizeTransposeGram N K).aemeasurable
  boundedExpectationTransfer_of_probabilityTotalVariationLE
      (normalizedHaarTransposeGramLaw H M N K)
      (normalizedGaussianTransposeGramLaw N K)
      (normalizedMatrixLaw H M N K hN hNK hKM)
      phi hphi hphi_nonneg hphi_le_one

/-- Data processing by an arbitrary Markov kernel: noise, coarse graining,
or a randomized classical routine cannot increase the hiding error. -/
theorem markovKernelPostprocessingLaw
    {β : Type*} [MeasurableSpace β]
    (H : UnitaryHaarProbabilityFamily)
    (M N K : ℕ) (hN : 1 ≤ N) (hNK : N ≤ K) (hKM : K ≤ M)
    (Q : Kernel (Matrix (Fin N) (Fin N) ℂ) β) [IsMarkovKernel Q] :
    probabilityTotalVariationLE
      (Q ∘ₘ normalizedHaarTransposeGramLaw H M N K)
      (Q ∘ₘ normalizedGaussianTransposeGramLaw N K)
      (min 1 (615172 * ultimateSquaredHidingRate M N)) :=
  letI : IsProbabilityMeasure (scaledHaarTransposeGramLaw H M N K) :=
    scaledHaarTransposeGramLaw_isProbability H (hNK.trans hKM) hKM
  letI : IsProbabilityMeasure (gaussianTransposeGramLaw N K) :=
    gaussianTransposeGramLaw_isProbability N K
  letI : IsProbabilityMeasure (normalizedHaarTransposeGramLaw H M N K) :=
    Measure.isProbabilityMeasure_map
      (measurable_normalizeTransposeGram N K).aemeasurable
  letI : IsProbabilityMeasure (normalizedGaussianTransposeGramLaw N K) :=
    Measure.isProbabilityMeasure_map
      (measurable_normalizeTransposeGram N K).aemeasurable
  UltimateHiding.DenseLocalStep.probabilityTVLE_kernel_comp
      (normalizedHaarTransposeGramLaw H M N K)
      (normalizedGaussianTransposeGramLaw N K) Q
      (normalizedMatrixLaw H M N K hN hNK hKM)

/-! ## Concrete observables used in the Article -/

/-- Hafnian as a locally named observable on an even-dimensional matrix.
This uses only the finite perfect-matching sum in `GramHafnian.Hafnian`; it
does not import or appeal to the Shou--Miller--Galitski theorem. -/
def hafnianObservable (n : ℕ) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ → ℂ :=
  hafnian

@[fun_prop]
theorem measurable_hafnianObservable (n : ℕ) :
    Measurable (hafnianObservable n) := by
  unfold hafnianObservable hafnian matchingMonomial
  fun_prop

/-- Hiding for the complex hafnian amplitude itself. -/
theorem hafnianObservableLaw
    (H : UnitaryHaarProbabilityFamily)
    (M n K : ℕ) (hn : 1 ≤ n) (hNK : 2 * n ≤ K) (hKM : K ≤ M) :
    probabilityTotalVariationLE
      (Measure.map (hafnianObservable n)
        (normalizedHaarTransposeGramLaw H M (2 * n) K))
      (Measure.map (hafnianObservable n)
        (normalizedGaussianTransposeGramLaw (2 * n) K))
      (min 1 (615172 * ultimateSquaredHidingRate M (2 * n))) :=
  observableLaw H M (2 * n) K (by omega) hNK hKM
    (hafnianObservable n) (measurable_hafnianObservable n)

/-- The tuple of principal submatrices selected by finitely many fixed
patterns inside one common `L × L` union-block Gram matrix. -/
abbrev PreselectedPrincipalSubmatrixTuple
    (r L : ℕ) (S : Fin r → Finset (Fin L)) :=
  (j : Fin r) → Matrix {i // i ∈ S j} {i // i ∈ S j} ℂ

def preselectedPrincipalSubmatrixTuple
    (r L : ℕ) (S : Fin r → Finset (Fin L)) :
    Matrix (Fin L) (Fin L) ℂ → PreselectedPrincipalSubmatrixTuple r L S :=
  fun A j ↦ A.submatrix Subtype.val Subtype.val

@[fun_prop]
theorem measurable_preselectedPrincipalSubmatrixTuple
    (r L : ℕ) (S : Fin r → Finset (Fin L)) :
    Measurable (preselectedPrincipalSubmatrixTuple r L S) := by
  unfold preselectedPrincipalSubmatrixTuple
  apply measurable_pi_lambda
  intro j
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro k
  exact (measurable_pi_apply (Subtype.val k)).comp
    (measurable_pi_apply (Subtype.val i))

/-- Canonical finite pattern sets obtained from ordered row embeddings. -/
def orderedPatternSets {q N L : ℕ} (rows : Fin q → (Fin N ↪ Fin L)) :
    Fin q → Finset (Fin L) :=
  fun j ↦ DisjointGaussianRows.rowRange (rows j)

/-- Reindex the subtype-valued principal blocks back to the common ordered
matrix type used in the paper. -/
def orderedPatternPanel {q N L : ℕ} (rows : Fin q → (Fin N ↪ Fin L)) :
    PreselectedPrincipalSubmatrixTuple q L (orderedPatternSets rows) →
      (Fin q → Matrix (Fin N) (Fin N) ℂ) :=
  fun A j i k ↦ A j
    ⟨rows j i, by simp [orderedPatternSets, DisjointGaussianRows.rowRange]⟩
    ⟨rows j k, by simp [orderedPatternSets, DisjointGaussianRows.rowRange]⟩

@[fun_prop]
theorem measurable_orderedPatternPanel {q N L : ℕ}
    (rows : Fin q → (Fin N ↪ Fin L)) :
    Measurable (orderedPatternPanel rows) := by
  unfold orderedPatternPanel
  fun_prop

/-- Restricting a full normalized transpose Gram to an ordered pattern is
pointwise the normalized transpose Gram of the corresponding ordered raw row
block. -/
theorem orderedPatternPanel_preselected_normalizedGram
    {q N L K : ℕ} (rows : Fin q → (Fin N ↪ Fin L))
    (G : Matrix (Fin L) (Fin K) ℂ) :
    orderedPatternPanel rows
        (preselectedPrincipalSubmatrixTuple q L (orderedPatternSets rows)
          (PRXArticle.normalizedTransposeGramMatrix G)) =
      fun j ↦ DisjointGaussianRows.orderedNormalizedGram
        (K := K) (rows j) G := by
  ext j i k
  simp [orderedPatternPanel, preselectedPrincipalSubmatrixTuple,
    orderedPatternSets, DisjointGaussianRows.orderedNormalizedGram,
    DisjointGaussianRows.orderedRowBlock,
    PRXArticle.normalizedTransposeGramMatrix,
    normalizeTransposeGram, rectangularTransposeGram, Matrix.mul_apply]

/-- Joint hiding for several preselected patterns.  Both tuples are obtained
from one common union-block matrix, so no independence between components is
asserted. -/
theorem jointPreselectedPatternLaw
    (H : UnitaryHaarProbabilityFamily)
    (M L K r : ℕ) (hL : 1 ≤ L) (hLK : L ≤ K) (hKM : K ≤ M)
    (S : Fin r → Finset (Fin L)) :
    probabilityTotalVariationLE
      (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
        (normalizedHaarTransposeGramLaw H M L K))
      (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
        (normalizedGaussianTransposeGramLaw L K))
      (min 1 (615172 * ultimateSquaredHidingRate M L)) :=
  observableLaw H M L K hL hLK hKM
    (preselectedPrincipalSubmatrixTuple r L S)
    (measurable_preselectedPrincipalSubmatrixTuple r L S)

/-- The Gaussian law of an ordered pattern panel is the pushforward of the
concrete iid rectangular source by the corresponding normalized row-block
maps.  No disjointness is needed for this representation identity. -/
theorem orderedGaussianPatternPanelLaw
    {q N L K : ℕ} (rows : Fin q → (Fin N ↪ Fin L)) :
    Measure.map (orderedPatternPanel rows)
        (Measure.map
          (preselectedPrincipalSubmatrixTuple q L (orderedPatternSets rows))
          (normalizedGaussianTransposeGramLaw L K)) =
      Measure.map
        (fun G j ↦ DisjointGaussianRows.orderedNormalizedGram
          (K := K) (rows j) G)
        (standardComplexGaussianRectangularMeasure L K) := by
  have hFullMeas : Measurable
      (PRXArticle.normalizedTransposeGramMatrix :
        Matrix (Fin L) (Fin K) ℂ → Matrix (Fin L) (Fin L) ℂ) :=
    (measurable_normalizeTransposeGram L K).comp
      (measurable_rectangularTransposeGram L K)
  rw [DisjointGaussianRows.normalizedGaussianTransposeGramLaw_eq_map_source]
  rw [Measure.map_map (measurable_orderedPatternPanel rows)
    (measurable_preselectedPrincipalSubmatrixTuple q L
      (orderedPatternSets rows))]
  rw [Measure.map_map
    ((measurable_orderedPatternPanel rows).comp
      (measurable_preselectedPrincipalSubmatrixTuple q L
        (orderedPatternSets rows)))
    hFullMeas]
  apply Measure.map_congr
  apply ae_of_all
  intro G
  simpa [Function.comp_def] using
    orderedPatternPanel_preselected_normalizedGram rows G

/-- Concrete Gaussian product law for pairwise disjoint ordered patterns.
This closes the product-row representation bridge using only the product
measure construction of the project's Gaussian rectangular matrix. -/
theorem orderedDisjointGaussianPatternProductLaw
    {q N L K : ℕ} (rows : Fin q → (Fin N ↪ Fin L))
    (hrows : Pairwise fun a b ↦
      Disjoint (DisjointGaussianRows.rowRange (rows a))
        (DisjointGaussianRows.rowRange (rows b))) :
    Measure.map (orderedPatternPanel rows)
        (Measure.map
          (preselectedPrincipalSubmatrixTuple q L (orderedPatternSets rows))
          (normalizedGaussianTransposeGramLaw L K)) =
      Measure.pi (fun _ : Fin q ↦ normalizedGaussianTransposeGramLaw N K) := by
  let muRaw := standardComplexGaussianRectangularMeasure L K
  let gram : Fin q → Matrix (Fin L) (Fin K) ℂ →
      Matrix (Fin N) (Fin N) ℂ :=
    fun j ↦ DisjointGaussianRows.orderedNormalizedGram (K := K) (rows j)
  have hIndep : iIndepFun gram muRaw := by
    exact DisjointGaussianRows.iIndepFun_orderedNormalizedGrams
      (K := K) rows hrows
  have hLaw : ∀ j, Measure.map (gram j) muRaw =
      normalizedGaussianTransposeGramLaw N K := by
    intro j
    exact DisjointGaussianRows.map_orderedNormalizedGram (K := K) (rows j)
  have hfactor := FinitePanelLaws.iid_product_factorization gram
    (fun j ↦ (DisjointGaussianRows.measurable_orderedNormalizedGram
      (K := K) (rows j)).aemeasurable)
    hIndep (normalizedGaussianTransposeGramLaw N K) hLaw
  have hFullMeas : Measurable
      (PRXArticle.normalizedTransposeGramMatrix :
        Matrix (Fin L) (Fin K) ℂ → Matrix (Fin L) (Fin L) ℂ) :=
    (measurable_normalizeTransposeGram L K).comp
      (measurable_rectangularTransposeGram L K)
  rw [DisjointGaussianRows.normalizedGaussianTransposeGramLaw_eq_map_source]
  rw [Measure.map_map (measurable_orderedPatternPanel rows)
    (measurable_preselectedPrincipalSubmatrixTuple q L
      (orderedPatternSets rows))]
  rw [Measure.map_map
    ((measurable_orderedPatternPanel rows).comp
      (measurable_preselectedPrincipalSubmatrixTuple q L
        (orderedPatternSets rows)))
    hFullMeas]
  calc
    Measure.map
        ((orderedPatternPanel rows ∘
          preselectedPrincipalSubmatrixTuple q L (orderedPatternSets rows)) ∘
          PRXArticle.normalizedTransposeGramMatrix)
        muRaw =
        Measure.map (fun G j ↦ gram j G) muRaw := by
      apply Measure.map_congr
      apply ae_of_all
      intro G
      simpa [Function.comp_def, gram] using
        orderedPatternPanel_preselected_normalizedGram rows G
    _ = Measure.pi
        (fun _ : Fin q ↦ normalizedGaussianTransposeGramLaw N K) := hfactor

/-- UH1 with the concrete disjoint Gaussian row-product bridge fully
discharged.  The ordered embeddings encode the paper's relabeling of each
fixed pattern by `Fin N`. -/
theorem orderedDisjointPatternProductHiding
    (H : UnitaryHaarProbabilityFamily)
    (M L K q N : ℕ) (hL : 1 ≤ L) (hLK : L ≤ K) (hKM : K ≤ M)
    (rows : Fin q → (Fin N ↪ Fin L))
    (hrows : Pairwise fun a b ↦
      Disjoint (DisjointGaussianRows.rowRange (rows a))
        (DisjointGaussianRows.rowRange (rows b))) :
    probabilityTotalVariationLE
      (Measure.map (orderedPatternPanel rows)
        (Measure.map
          (preselectedPrincipalSubmatrixTuple q L (orderedPatternSets rows))
          (normalizedHaarTransposeGramLaw H M L K)))
      (Measure.pi (fun _ : Fin q ↦ normalizedGaussianTransposeGramLaw N K))
      (min 1 (615172 * ultimateSquaredHidingRate M L)) := by
  have htv :=
    (jointPreselectedPatternLaw H M L K q hL hLK hKM
      (orderedPatternSets rows)).map (measurable_orderedPatternPanel rows)
  rw [orderedDisjointGaussianPatternProductLaw rows hrows] at htv
  exact htv

/-! ## Application-level adapters UH1--UH5 -/

/-- Triangle inequality for the eventwise probability-total-variation
predicate used throughout the three-paper package. -/
theorem probabilityTotalVariationLE_trans_add
    {α : Type*} [MeasurableSpace α]
    {mu nu xi : Measure α} {delta eta : ℝ}
    (hmunu : probabilityTotalVariationLE mu nu delta)
    (hnuxi : probabilityTotalVariationLE nu xi eta) :
    probabilityTotalVariationLE mu xi (delta + eta) := by
  refine ⟨add_nonneg hmunu.nonneg hnuxi.nonneg, fun s hs ↦ ?_⟩
  calc
    |mu.real s - xi.real s| =
        |(mu.real s - nu.real s) + (nu.real s - xi.real s)| := by ring_nf
    _ ≤ |mu.real s - nu.real s| + |nu.real s - xi.real s| := abs_add_le _ _
    _ ≤ delta + eta := add_le_add (hmunu.2 s hs) (hnuxi.2 s hs)

/-- UH1: joint hiding against any explicitly identified Gaussian product
reference.  The equality hypothesis is the elementary Gaussian factorization
statement for the chosen disjoint pattern family; no independence assertion is
silently built into the total-variation theorem. -/
theorem disjointPatternProductHiding
    (H : UnitaryHaarProbabilityFamily)
    (M L K r : ℕ) (hL : 1 ≤ L) (hLK : L ≤ K) (hKM : K ≤ M)
    (S : Fin r → Finset (Fin L))
    (productReference : Measure (PreselectedPrincipalSubmatrixTuple r L S))
    (hfactor :
      Measure.map (preselectedPrincipalSubmatrixTuple r L S)
          (normalizedGaussianTransposeGramLaw L K) = productReference) :
    probabilityTotalVariationLE
      (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
        (normalizedHaarTransposeGramLaw H M L K))
      productReference
      (min 1 (615172 * ultimateSquaredHidingRate M L)) := by
  simpa [hfactor] using
    jointPreselectedPatternLaw H M L K r hL hLK hKM S

/-- UH1 with the Gaussian product step discharged from explicit mutual
independence and common marginal laws.  For a concrete disjoint pattern
family, `score j` may be the canonically reindexed `j`th principal block (or
any measurable statistic of that block). -/
theorem disjointPatternIidPanelHiding
    {β : Type*} [MeasurableSpace β]
    (H : UnitaryHaarProbabilityFamily)
    (M L K r : ℕ) (hL : 1 ≤ L) (hLK : L ≤ K) (hKM : K ≤ M)
    (S : Fin r → Finset (Fin L))
    (score : Fin r → PreselectedPrincipalSubmatrixTuple r L S → β)
    (hscoreMeas : ∀ j, Measurable (score j))
    (hIndep : iIndepFun score
      (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
        (normalizedGaussianTransposeGramLaw L K)))
    (P : Measure β)
    (hLaw : ∀ j,
      Measure.map (score j)
        (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
          (normalizedGaussianTransposeGramLaw L K)) = P) :
    probabilityTotalVariationLE
      (Measure.map (fun x j ↦ score j x)
        (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
          (normalizedHaarTransposeGramLaw H M L K)))
      (Measure.pi (fun _ : Fin r ↦ P))
      (min 1 (615172 * ultimateSquaredHidingRate M L)) := by
  have hpanelMeas : Measurable (fun x j ↦ score j x) :=
    measurable_pi_lambda _ hscoreMeas
  have hfactor :=
    FinitePanelLaws.iid_product_factorization score
      (fun j ↦ (hscoreMeas j).aemeasurable) hIndep P hLaw
  have htv := (jointPreselectedPatternLaw H M L K r hL hLK hKM S).map
    hpanelMeas
  rw [hfactor] at htv
  exact htv

/-- Common data-processing endpoint for the maximum score, heavy-count, order
statistics, and every other measurable summary of a preselected tuple. -/
theorem preselectedSummaryLaw
    {β : Type*} [MeasurableSpace β]
    (H : UnitaryHaarProbabilityFamily)
    (M L K r : ℕ) (hL : 1 ≤ L) (hLK : L ≤ K) (hKM : K ≤ M)
    (S : Fin r → Finset (Fin L))
    (summary : PreselectedPrincipalSubmatrixTuple r L S → β)
    (hsummary : Measurable summary) :
    probabilityTotalVariationLE
      (Measure.map summary
        (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
          (normalizedHaarTransposeGramLaw H M L K)))
      (Measure.map summary
        (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
          (normalizedGaussianTransposeGramLaw L K)))
      (min 1 (615172 * ultimateSquaredHidingRate M L)) :=
  (jointPreselectedPatternLaw H M L K r hL hLK hKM S).map hsummary

/-- UH2, maximum-score form.  The name records the paper application; the
proof is exactly measurable data processing. -/
theorem maxScoreTransfer
    (H : UnitaryHaarProbabilityFamily)
    (M L K r : ℕ) (hL : 1 ≤ L) (hLK : L ≤ K) (hKM : K ≤ M)
    (S : Fin r → Finset (Fin L))
    (maxScore : PreselectedPrincipalSubmatrixTuple r L S → ℝ)
    (hmaxScore : Measurable maxScore) :
    probabilityTotalVariationLE
      (Measure.map maxScore
        (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
          (normalizedHaarTransposeGramLaw H M L K)))
      (Measure.map maxScore
        (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
          (normalizedGaussianTransposeGramLaw L K)))
      (min 1 (615172 * ultimateSquaredHidingRate M L)) :=
  preselectedSummaryLaw H M L K r hL hLK hKM S maxScore hmaxScore

/-- UH2, heavy-count form. -/
theorem heavyCountTransfer
    (H : UnitaryHaarProbabilityFamily)
    (M L K r : ℕ) (hL : 1 ≤ L) (hLK : L ≤ K) (hKM : K ≤ M)
    (S : Fin r → Finset (Fin L))
    (heavyCount : PreselectedPrincipalSubmatrixTuple r L S → ℕ)
    (hheavyCount : Measurable heavyCount) :
    probabilityTotalVariationLE
      (Measure.map heavyCount
        (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
          (normalizedHaarTransposeGramLaw H M L K)))
      (Measure.map heavyCount
        (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
          (normalizedGaussianTransposeGramLaw L K)))
      (min 1 (615172 * ultimateSquaredHidingRate M L)) :=
  preselectedSummaryLaw H M L K r hL hLK hKM S heavyCount hheavyCount

/-- UH2, exact maximum-CDF form.  The Gaussian product calculation is
kernel-proved from the displayed `iIndepFun` and common-law premises. -/
theorem maxScoreCdfTransfer_iid
    (H : UnitaryHaarProbabilityFamily)
    (M L K r : ℕ) (hL : 1 ≤ L) (hLK : L ≤ K) (hKM : K ≤ M)
    (S : Fin r → Finset (Fin L))
    (score : Fin r → PreselectedPrincipalSubmatrixTuple r L S → ℝ)
    (hscoreMeas : ∀ j, Measurable (score j))
    (hIndep : iIndepFun score
      (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
        (normalizedGaussianTransposeGramLaw L K)))
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (hLaw : ∀ j,
      Measure.map (score j)
        (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
          (normalizedGaussianTransposeGramLaw L K)) = P)
    (t : ℝ) :
    |(Measure.map (preselectedPrincipalSubmatrixTuple r L S)
        (normalizedHaarTransposeGramLaw H M L K)).real
          {x | ∀ j, score j x ≤ t} -
      (P.real (Set.Iic t)) ^ r| ≤
        min 1 (615172 * ultimateSquaredHidingRate M L) := by
  let μG := Measure.map (preselectedPrincipalSubmatrixTuple r L S)
    (normalizedGaussianTransposeGramLaw L K)
  change iIndepFun score μG at hIndep
  change ∀ j, Measure.map (score j) μG = P at hLaw
  letI : IsProbabilityMeasure μG := hIndep.isProbabilityMeasure
  have hGaussian : μG.real {x | ∀ j, score j x ≤ t} =
      (P.real (Set.Iic t)) ^ r :=
    FinitePanelLaws.iid_max_cdf score hscoreMeas hIndep P hLaw t
  have hevent : MeasurableSet {x | ∀ j, score j x ≤ t} :=
    (Measurable.forall fun j ↦
      measurableSet_setOfPred.mp
        (measurableSet_le (hscoreMeas j) measurable_const)).setOf
  have htv := (jointPreselectedPatternLaw H M L K r hL hLK hKM S).2
    {x | ∀ j, score j x ≤ t} hevent
  change |(Measure.map (preselectedPrincipalSubmatrixTuple r L S)
        (normalizedHaarTransposeGramLaw H M L K)).real
          {x | ∀ j, score j x ≤ t} -
      μG.real {x | ∀ j, score j x ≤ t}| ≤ _ at htv
  rwa [hGaussian] at htv

/-- UH2, exact binomial law for the number of scores above a threshold.
The binomial parameter is the common Gaussian one-coordinate tail. -/
theorem heavyCountBinomialTransfer_iid
    (H : UnitaryHaarProbabilityFamily)
    (M L K r : ℕ) (hL : 1 ≤ L) (hLK : L ≤ K) (hKM : K ≤ M)
    (S : Fin r → Finset (Fin L))
    (score : Fin r → PreselectedPrincipalSubmatrixTuple r L S → ℝ)
    (hscoreMeas : ∀ j, Measurable (score j))
    (hIndep : iIndepFun score
      (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
        (normalizedGaussianTransposeGramLaw L K)))
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (hLaw : ∀ j,
      Measure.map (score j)
        (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
          (normalizedGaussianTransposeGramLaw L K)) = P)
    (t : ℝ) :
    let p : I := ⟨P.real (Set.Ioi t),
      ⟨measureReal_nonneg, measureReal_le_one⟩⟩
    probabilityTotalVariationLE
      (Measure.map
        (fun x ↦ Set.ncard {j : Fin r | t < score j x})
        (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
          (normalizedHaarTransposeGramLaw H M L K)))
      (ProbabilityTheory.binomial r p)
      (min 1 (615172 * ultimateSquaredHidingRate M L)) := by
  dsimp only
  let μG := Measure.map (preselectedPrincipalSubmatrixTuple r L S)
    (normalizedGaussianTransposeGramLaw L K)
  change iIndepFun score μG at hIndep
  change ∀ j, Measure.map (score j) μG = P at hLaw
  letI : IsProbabilityMeasure μG := hIndep.isProbabilityMeasure
  have hcountMeas : Measurable
      (fun x ↦ Set.ncard {j : Fin r | t < score j x}) := by
    fun_prop
  have hGaussian := FinitePanelLaws.iid_threshold_count_binomial
    score hscoreMeas hIndep P hLaw t
  have htv := (jointPreselectedPatternLaw H M L K r hL hLK hKM S).map
    hcountMeas
  change probabilityTotalVariationLE
    (Measure.map (fun x ↦ Set.ncard {j : Fin r | t < score j x})
      (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
        (normalizedHaarTransposeGramLaw H M L K)))
    (Measure.map (fun x ↦ Set.ncard {j : Fin r | t < score j x}) μG)
    _ at htv
  rw [hGaussian] at htv
  exact htv

/-- UH2 maximum-CDF transfer with the concrete disjoint Gaussian row bridge
fully discharged. -/
theorem orderedDisjointMaxScoreCdfTransfer
    (H : UnitaryHaarProbabilityFamily)
    (M L K q N : ℕ) (hL : 1 ≤ L) (hLK : L ≤ K) (hKM : K ≤ M)
    (rows : Fin q → (Fin N ↪ Fin L))
    (hrows : Pairwise fun a b ↦
      Disjoint (DisjointGaussianRows.rowRange (rows a))
        (DisjointGaussianRows.rowRange (rows b)))
    (h : Matrix (Fin N) (Fin N) ℂ → ℝ) (hh : Measurable h)
    (t : ℝ) :
    let P := normalizedGaussianTransposeGramLaw N K
    let muH := Measure.map (orderedPatternPanel rows)
      (Measure.map
        (preselectedPrincipalSubmatrixTuple q L (orderedPatternSets rows))
        (normalizedHaarTransposeGramLaw H M L K))
    |muH.real {A | ∀ j, h (A j) ≤ t} -
      ((Measure.map h P).real (Set.Iic t)) ^ q| ≤
        min 1 (615172 * ultimateSquaredHidingRate M L) := by
  dsimp only
  let P := normalizedGaussianTransposeGramLaw N K
  let muP := Measure.pi (fun _ : Fin q ↦ P)
  let X : Fin q → (Fin q → Matrix (Fin N) (Fin N) ℂ) → ℝ :=
    fun j A ↦ h (A j)
  letI : IsProbabilityMeasure (gaussianTransposeGramLaw N K) :=
    gaussianTransposeGramLaw_isProbability N K
  letI : IsProbabilityMeasure P := Measure.isProbabilityMeasure_map
    (measurable_normalizeTransposeGram N K).aemeasurable
  letI : IsProbabilityMeasure (Measure.map h P) :=
    Measure.isProbabilityMeasure_map hh.aemeasurable
  letI : IsProbabilityMeasure muP := by dsimp [muP]; infer_instance
  have hXmeas : ∀ j, Measurable (X j) := by
    intro j
    exact hh.comp (measurable_pi_apply j)
  have hXindep : iIndepFun X muP := by
    dsimp [X, muP]
    exact iIndepFun_pi (μ := fun _ : Fin q ↦ P)
      (X := fun _ ↦ h) (fun _ ↦ hh.aemeasurable)
  have hXlaw : ∀ j, Measure.map (X j) muP = Measure.map h P := by
    intro j
    change Measure.map (h ∘ fun A : Fin q → Matrix (Fin N) (Fin N) ℂ ↦
      A j) muP = _
    rw [← Measure.map_map hh (measurable_pi_apply j)]
    exact congrArg (Measure.map h)
      (measurePreserving_eval (fun _ : Fin q ↦ P) j).map_eq
  have hGaussian := FinitePanelLaws.iid_max_cdf X hXmeas hXindep
    (Measure.map h P) hXlaw t
  have hevent : MeasurableSet
      {A : Fin q → Matrix (Fin N) (Fin N) ℂ | ∀ j, h (A j) ≤ t} :=
    (Measurable.forall fun j ↦
      measurableSet_setOfPred.mp
        (measurableSet_le (hXmeas j) measurable_const)).setOf
  have htv := (orderedDisjointPatternProductHiding H M L K q N
    hL hLK hKM rows hrows).2
      {A | ∀ j, h (A j) ≤ t} hevent
  change |(Measure.map (orderedPatternPanel rows)
      (Measure.map
        (preselectedPrincipalSubmatrixTuple q L (orderedPatternSets rows))
        (normalizedHaarTransposeGramLaw H M L K))).real
          {A | ∀ j, h (A j) ≤ t} -
      muP.real {A | ∀ j, h (A j) ≤ t}| ≤ _ at htv
  change muP.real {A | ∀ j, h (A j) ≤ t} =
      ((Measure.map h P).real (Set.Iic t)) ^ q at hGaussian
  rwa [hGaussian] at htv

/-- The ordered-pattern Haar panel law used by the concrete UH1--UH2
endpoints.  Naming it keeps the paper-facing count theorem compact. -/
def orderedPatternPanelHaarLaw
    (H : UnitaryHaarProbabilityFamily) (M L K q N : ℕ)
    (rows : Fin q → (Fin N ↪ Fin L)) :
    Measure (Fin q → Matrix (Fin N) (Fin N) ℂ) :=
  Measure.map (orderedPatternPanel rows)
    (Measure.map
      (preselectedPrincipalSubmatrixTuple q L (orderedPatternSets rows))
      (normalizedHaarTransposeGramLaw H M L K))

/-- Number of coordinates whose score exceeds `t`. -/
def orderedPanelHeavyCount {q N : ℕ}
    (h : Matrix (Fin N) (Fin N) ℂ → ℝ) (t : ℝ) :
    (Fin q → Matrix (Fin N) (Fin N) ℂ) → ℕ :=
  fun A ↦ Set.ncard {j : Fin q | t < h (A j)}

@[fun_prop]
theorem measurable_orderedPanelHeavyCount {q N : ℕ}
    (h : Matrix (Fin N) (Fin N) ℂ → ℝ) (hh : Measurable h) (t : ℝ) :
    Measurable (orderedPanelHeavyCount (q := q) h t) := by
  unfold orderedPanelHeavyCount
  fun_prop

/-- Common Gaussian exceedance probability, bundled as a unit-interval
parameter for Mathlib's binomial distribution. -/
def gaussianScoreTailParameter (N K : ℕ)
    (h : Matrix (Fin N) (Fin N) ℂ → ℝ) (t : ℝ) : I :=
  ⟨(normalizedGaussianTransposeGramLaw N K).real {A | t < h A},
    ⟨measureReal_nonneg, measureReal_le_one⟩⟩

/-- UH2 exact binomial threshold-count transfer with the concrete disjoint
Gaussian row bridge fully discharged. -/
theorem orderedDisjointHeavyCountBinomialTransfer
    (H : UnitaryHaarProbabilityFamily)
    (M L K q N : ℕ) (hL : 1 ≤ L) (hLK : L ≤ K) (hKM : K ≤ M)
    (rows : Fin q → (Fin N ↪ Fin L))
    (hrows : Pairwise fun a b ↦
      Disjoint (DisjointGaussianRows.rowRange (rows a))
        (DisjointGaussianRows.rowRange (rows b)))
    (h : Matrix (Fin N) (Fin N) ℂ → ℝ) (hh : Measurable h)
    (t : ℝ) :
    probabilityTotalVariationLE
      (Measure.map (orderedPanelHeavyCount (q := q) h t)
        (orderedPatternPanelHaarLaw H M L K q N rows))
      (ProbabilityTheory.binomial q (gaussianScoreTailParameter N K h t))
      (min 1 (615172 * ultimateSquaredHidingRate M L)) := by
  let P := normalizedGaussianTransposeGramLaw N K
  let muP := Measure.pi (fun _ : Fin q ↦ P)
  let X : Fin q → (Fin q → Matrix (Fin N) (Fin N) ℂ) → ℝ :=
    fun j A ↦ h (A j)
  letI : IsProbabilityMeasure (Measure.map h P) :=
    Measure.isProbabilityMeasure_map hh.aemeasurable
  letI : IsProbabilityMeasure muP := by dsimp [muP]; infer_instance
  have hXmeas : ∀ j, Measurable (X j) := by
    intro j
    exact hh.comp (measurable_pi_apply j)
  have hXindep : iIndepFun X muP := by
    dsimp [X, muP]
    exact iIndepFun_pi (μ := fun _ : Fin q ↦ P)
      (X := fun _ ↦ h) (fun _ ↦ hh.aemeasurable)
  have hXlaw : ∀ j, Measure.map (X j) muP = Measure.map h P := by
    intro j
    change Measure.map (h ∘ fun A : Fin q → Matrix (Fin N) (Fin N) ℂ ↦
      A j) muP = _
    rw [← Measure.map_map hh (measurable_pi_apply j)]
    exact congrArg (Measure.map h)
      (measurePreserving_eval (fun _ : Fin q ↦ P) j).map_eq
  have hGaussian := FinitePanelLaws.iid_threshold_count_binomial X
    hXmeas hXindep (Measure.map h P) hXlaw t
  let pMap : I := ⟨(Measure.map h P).real (Set.Ioi t),
    ⟨measureReal_nonneg, measureReal_le_one⟩⟩
  change Measure.map (orderedPanelHeavyCount h t) muP =
    ProbabilityTheory.binomial q pMap at hGaussian
  have hp : (Measure.map h P).real (Set.Ioi t) =
      P.real {A | t < h A} := by
    rw [map_measureReal_apply hh measurableSet_Ioi]
    rfl
  have hparam : pMap = gaussianScoreTailParameter N K h t := by
    apply Subtype.ext
    exact hp
  have htv := (orderedDisjointPatternProductHiding H M L K q N
    hL hLK hKM rows hrows).map
      (measurable_orderedPanelHeavyCount h hh t)
  change probabilityTotalVariationLE
    (Measure.map (orderedPanelHeavyCount h t)
      (orderedPatternPanelHaarLaw H M L K q N rows))
    (Measure.map (orderedPanelHeavyCount h t) muP) _ at htv
  rw [hparam] at hGaussian
  rw [hGaussian] at htv
  exact htv

/-- UH3: a Gaussian overlap-graph concentration estimate transfers to Haar
with the single union-size hiding remainder.  `hGaussian` is the exact place
where the standard dependency-graph Hoeffding/Janson theorem is used; this
adapter introduces no new declaration or axiom for that literature result. -/
theorem overlapGraphConcentrationTransfer
    (H : UnitaryHaarProbabilityFamily)
    (M L K r : ℕ) (hL : 1 ≤ L) (hLK : L ≤ K) (hKM : K ≤ M)
    (S : Fin r → Finset (Fin L))
    (bad : Set (PreselectedPrincipalSubmatrixTuple r L S))
    (hbad : MeasurableSet bad) {gaussianBound : ℝ}
    (hGaussian :
      (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
        (normalizedGaussianTransposeGramLaw L K)).real bad ≤ gaussianBound) :
    (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
        (normalizedHaarTransposeGramLaw H M L K)).real bad ≤
      gaussianBound + min 1 (615172 * ultimateSquaredHidingRate M L) := by
  calc
    (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
        (normalizedHaarTransposeGramLaw H M L K)).real bad ≤
      (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
          (normalizedGaussianTransposeGramLaw L K)).real bad +
        min 1 (615172 * ultimateSquaredHidingRate M L) :=
      (jointPreselectedPatternLaw H M L K r hL hLK hKM S).event_le hbad
    _ ≤ gaussianBound + min 1 (615172 * ultimateSquaredHidingRate M L) :=
      add_le_add hGaussian le_rfl

/-- UH3 with the Gaussian dependency-graph step discharged in the kernel.
The declaration makes the two structural inputs explicit: a coloring with at
most `Delta + 1` colors, and mutual independence of the Gaussian score
variables inside every color class.  The latter is the precise row-block
independence obligation for a concrete overlap family. -/
theorem overlapGraphConcentrationTransfer_colored
    (H : UnitaryHaarProbabilityFamily)
    (M L K r : ℕ) (hL : 1 ≤ L) (hLK : L ≤ K) (hKM : K ≤ M)
    (S : Fin r → Finset (Fin L))
    {k Delta : ℕ} (hr : 0 < r) (hk : 0 < k)
    (hkDelta : k ≤ Delta + 1)
    (color : Fin r → Fin k)
    (score : Fin r → PreselectedPrincipalSubmatrixTuple r L S → ℝ)
    (hscoreMeas : ∀ j, Measurable (score j))
    (hscore01 : ∀ j x, score j x ∈ Set.Icc (0 : ℝ) 1)
    (hIndep : ∀ a, iIndepFun
      (fun j : {j : Fin r // color j = a} ↦ score j)
      (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
        (normalizedGaussianTransposeGramLaw L K)))
    (m : ℝ)
    (hmean : ∀ j : Fin r,
      ∫ x, score j x ∂(Measure.map
        (preselectedPrincipalSubmatrixTuple r L S)
        (normalizedGaussianTransposeGramLaw L K)) = m)
    {t : ℝ} (ht : 0 ≤ t) :
    (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
      (normalizedHaarTransposeGramLaw H M L K)).real
        {x | t ≤ |(1 / (r : ℝ)) * (∑ j : Fin r, score j x) - m|} ≤
      2 * Real.exp (-2 * (r : ℝ) * t ^ 2 / ((Delta : ℝ) + 1)) +
        min 1 (615172 * ultimateSquaredHidingRate M L) := by
  letI : IsProbabilityMeasure (gaussianTransposeGramLaw L K) :=
    gaussianTransposeGramLaw_isProbability L K
  letI : IsProbabilityMeasure (normalizedGaussianTransposeGramLaw L K) :=
    Measure.isProbabilityMeasure_map
      (measurable_normalizeTransposeGram L K).aemeasurable
  letI : IsProbabilityMeasure
      (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
        (normalizedGaussianTransposeGramLaw L K)) :=
    Measure.isProbabilityMeasure_map
      (measurable_preselectedPrincipalSubmatrixTuple r L S).aemeasurable
  have hGaussian :=
    OverlapGraphConcentration.colored_hoeffding_two_sided_average_maxDegree
      (mu := Measure.map (preselectedPrincipalSubmatrixTuple r L S)
        (normalizedGaussianTransposeGramLaw L K))
      hr hk hkDelta color score
      (fun j ↦ (hscoreMeas j).aemeasurable)
      (fun j ↦ ae_of_all _ (hscore01 j)) hIndep m hmean ht
  have hsumMeas : Measurable
      (fun x : PreselectedPrincipalSubmatrixTuple r L S ↦
        ∑ j : Fin r, score j x) :=
    Finset.measurable_fun_sum Finset.univ fun j _ ↦ hscoreMeas j
  have hbad : MeasurableSet
      {x : PreselectedPrincipalSubmatrixTuple r L S |
        t ≤ |(1 / (r : ℝ)) * (∑ j : Fin r, score j x) - m|} :=
    measurableSet_le measurable_const
      ((measurable_const.mul hsumMeas).sub_const m).abs
  calc
    (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
      (normalizedHaarTransposeGramLaw H M L K)).real
        {x | t ≤ |(1 / (r : ℝ)) * (∑ j : Fin r, score j x) - m|} ≤
      (Measure.map (preselectedPrincipalSubmatrixTuple r L S)
        (normalizedGaussianTransposeGramLaw L K)).real
          {x | t ≤ |(1 / (r : ℝ)) * (∑ j : Fin r, score j x) - m|} +
        min 1 (615172 * ultimateSquaredHidingRate M L) :=
      (jointPreselectedPatternLaw H M L K r hL hLK hKM S).event_le hbad
    _ ≤ 2 * Real.exp (-2 * (r : ℝ) * t ^ 2 / ((Delta : ℝ) + 1)) +
        min 1 (615172 * ultimateSquaredHidingRate M L) :=
      add_le_add hGaussian le_rfl

/-- UH3 for the paper's concrete ordered overlap family.  A proper coloring
is supplied through `hcolorDisjoint`: rows in every color fiber are pairwise
disjoint.  Their Gaussian normalized Gram blocks are then proved independent
from the concrete iid row-product measure, so no `iIndepFun` premise remains
in this paper-facing endpoint. -/
theorem orderedOverlapGraphConcentrationTransfer_colored
    (H : UnitaryHaarProbabilityFamily)
    (M L K r N : ℕ) (hL : 1 ≤ L) (hLK : L ≤ K) (hKM : K ≤ M)
    (rows : Fin r → (Fin N ↪ Fin L))
    {k Delta : ℕ} (hr : 0 < r) (hk : 0 < k)
    (hkDelta : k ≤ Delta + 1)
    (color : Fin r → Fin k)
    (hcolorDisjoint : ∀ a, Pairwise fun i j :
      {j : Fin r // color j = a} ↦
        Disjoint (DisjointGaussianRows.rowRange (rows i))
          (DisjointGaussianRows.rowRange (rows j)))
    (h : Matrix (Fin N) (Fin N) ℂ → ℝ) (hh : Measurable h)
    (h01 : ∀ A, h A ∈ Set.Icc (0 : ℝ) 1)
    (m : ℝ)
    (hmean : ∀ _j : Fin r,
      ∫ A, h A ∂(normalizedGaussianTransposeGramLaw N K) = m)
    {t : ℝ} (ht : 0 ≤ t) :
    (orderedPatternPanelHaarLaw H M L K r N rows).real
        {A | t ≤ |(1 / (r : ℝ)) * (∑ j : Fin r, h (A j)) - m|} ≤
      2 * Real.exp (-2 * (r : ℝ) * t ^ 2 / ((Delta : ℝ) + 1)) +
        min 1 (615172 * ultimateSquaredHidingRate M L) := by
  let muRaw := standardComplexGaussianRectangularMeasure L K
  let Y : Fin r → Matrix (Fin L) (Fin K) ℂ → ℝ :=
    fun j G ↦ h (DisjointGaussianRows.orderedNormalizedGram
      (K := K) (rows j) G)
  have hYmeas : ∀ j, AEMeasurable (Y j) muRaw := by
    intro j
    exact (hh.comp
      (DisjointGaussianRows.measurable_orderedNormalizedGram
        (K := K) (rows j))).aemeasurable
  have hY01 : ∀ j, ∀ᵐ G ∂muRaw, Y j G ∈ Set.Icc (0 : ℝ) 1 := by
    intro j
    exact ae_of_all _ fun G ↦ h01 _
  have hYindep : ∀ a, iIndepFun
      (fun i : {j : Fin r // color j = a} ↦ Y i) muRaw := by
    intro a
    have hmatrix :=
      DisjointGaussianRows.iIndepFun_orderedNormalizedGrams
        (K := K) (fun i : {j : Fin r // color j = a} ↦ rows i)
        (hcolorDisjoint a)
    simpa [Y, Function.comp_def] using hmatrix.comp
      (fun _ ↦ h) (fun _ ↦ hh)
  have hYmean : ∀ j, ∫ G, Y j G ∂muRaw = m := by
    intro j
    calc
      ∫ G, Y j G ∂muRaw =
          ∫ A, h A ∂(Measure.map
            (DisjointGaussianRows.orderedNormalizedGram
              (K := K) (rows j)) muRaw) := by
            symm
            exact integral_map
              (DisjointGaussianRows.measurable_orderedNormalizedGram
                (K := K) (rows j)).aemeasurable
              hh.aestronglyMeasurable
      _ = ∫ A, h A ∂(normalizedGaussianTransposeGramLaw N K) := by
        rw [DisjointGaussianRows.map_orderedNormalizedGram (K := K) (rows j)]
      _ = m := hmean j
  have hGaussianRaw :=
    OverlapGraphConcentration.colored_hoeffding_two_sided_average_maxDegree
      (mu := muRaw) hr hk hkDelta color Y hYmeas hY01 hYindep
      m hYmean ht
  let rawPanel : Matrix (Fin L) (Fin K) ℂ →
      (Fin r → Matrix (Fin N) (Fin N) ℂ) :=
    fun G j ↦ DisjointGaussianRows.orderedNormalizedGram
      (K := K) (rows j) G
  have hrawPanelMeas : Measurable rawPanel := by
    dsimp [rawPanel]
    exact measurable_pi_lambda _ fun j ↦
      DisjointGaussianRows.measurable_orderedNormalizedGram
        (K := K) (rows j)
  let bad : Set (Fin r → Matrix (Fin N) (Fin N) ℂ) :=
    {A | t ≤ |(1 / (r : ℝ)) * (∑ j : Fin r, h (A j)) - m|}
  have hsumMeas : Measurable
      (fun A : Fin r → Matrix (Fin N) (Fin N) ℂ ↦
        ∑ j : Fin r, h (A j)) :=
    Finset.measurable_fun_sum Finset.univ fun j _ ↦
      hh.comp (measurable_pi_apply j)
  have hbad : MeasurableSet bad := by
    dsimp [bad]
    exact measurableSet_le measurable_const
      ((measurable_const.mul hsumMeas).sub_const m).abs
  have hGaussianPanel :
      (Measure.map rawPanel muRaw).real bad ≤
        2 * Real.exp (-2 * (r : ℝ) * t ^ 2 / ((Delta : ℝ) + 1)) := by
    rw [map_measureReal_apply hrawPanelMeas hbad]
    simpa [bad, rawPanel, Y] using hGaussianRaw
  have htv := (jointPreselectedPatternLaw H M L K r hL hLK hKM
    (orderedPatternSets rows)).map (measurable_orderedPatternPanel rows)
  change probabilityTotalVariationLE
    (orderedPatternPanelHaarLaw H M L K r N rows)
    (Measure.map (orderedPatternPanel rows)
      (Measure.map
        (preselectedPrincipalSubmatrixTuple r L (orderedPatternSets rows))
        (normalizedGaussianTransposeGramLaw L K)))
    (min 1 (615172 * ultimateSquaredHidingRate M L)) at htv
  rw [orderedGaussianPatternPanelLaw rows] at htv
  change probabilityTotalVariationLE
    (orderedPatternPanelHaarLaw H M L K r N rows)
    (Measure.map rawPanel muRaw)
    (min 1 (615172 * ultimateSquaredHidingRate M L)) at htv
  calc
    (orderedPatternPanelHaarLaw H M L K r N rows).real
        {A | t ≤ |(1 / (r : ℝ)) * (∑ j : Fin r, h (A j)) - m|} ≤
      (Measure.map rawPanel muRaw).real bad +
        min 1 (615172 * ultimateSquaredHidingRate M L) := by
          simpa [bad] using htv.event_le hbad
    _ ≤ 2 * Real.exp
          (-2 * (r : ℝ) * t ^ 2 / ((Delta : ℝ) + 1)) +
        min 1 (615172 * ultimateSquaredHidingRate M L) :=
      add_le_add hGaussianPanel le_rfl

/-- Literal UH3 display with the common Gaussian mean fixed by the canonical
one-pattern normalized transpose-Gram law. -/
theorem orderedOverlapGraphConcentrationTransfer_colored_canonicalMean
    (H : UnitaryHaarProbabilityFamily)
    (M L K r N : ℕ) (hL : 1 ≤ L) (hLK : L ≤ K) (hKM : K ≤ M)
    (rows : Fin r → (Fin N ↪ Fin L))
    {k Delta : ℕ} (hr : 0 < r) (hk : 0 < k)
    (hkDelta : k ≤ Delta + 1)
    (color : Fin r → Fin k)
    (hcolorDisjoint : ∀ a, Pairwise fun i j :
      {j : Fin r // color j = a} ↦
        Disjoint (DisjointGaussianRows.rowRange (rows i))
          (DisjointGaussianRows.rowRange (rows j)))
    (h : Matrix (Fin N) (Fin N) ℂ → ℝ) (hh : Measurable h)
    (h01 : ∀ A, h A ∈ Set.Icc (0 : ℝ) 1)
    {t : ℝ} (ht : 0 ≤ t) :
    let muG := ∫ A, h A ∂(normalizedGaussianTransposeGramLaw N K)
    (orderedPatternPanelHaarLaw H M L K r N rows).real
        {A | t ≤ |(1 / (r : ℝ)) * (∑ j : Fin r, h (A j)) - muG|} ≤
      2 * Real.exp (-2 * (r : ℝ) * t ^ 2 / ((Delta : ℝ) + 1)) +
        min 1 (615172 * ultimateSquaredHidingRate M L) := by
  dsimp only
  exact orderedOverlapGraphConcentrationTransfer_colored
    H M L K r N hL hLK hKM rows hr hk hkDelta color hcolorDisjoint
    h hh h01 (∫ A, h A ∂(normalizedGaussianTransposeGramLaw N K))
    (fun _ ↦ rfl) ht

/-- UH4: any independent hard-source mask, its flag, and its classical
postprocessing can be bundled into one Markov kernel.  The hiding remainder
cannot increase. -/
theorem hardSourceMaskHiding
    {β : Type*} [MeasurableSpace β]
    (H : UnitaryHaarProbabilityFamily)
    (M N K : ℕ) (hN : 1 ≤ N) (hNK : N ≤ K) (hKM : K ≤ M)
    (maskKernel : Kernel (Matrix (Fin N) (Fin N) ℂ) β)
    [IsMarkovKernel maskKernel] :
    probabilityTotalVariationLE
      (maskKernel ∘ₘ normalizedHaarTransposeGramLaw H M N K)
      (maskKernel ∘ₘ normalizedGaussianTransposeGramLaw N K)
      (min 1 (615172 * ultimateSquaredHidingRate M N)) :=
  markovKernelPostprocessingLaw H M N K hN hNK hKM maskKernel

/-- UH4, exact finite variable-`K` mixture theorem.  The mask is retained in
the output, and a uniform componentwise total-variation bound survives
mixing without loss. -/
theorem hardSourceMaskFiniteMixtureHiding
    {ι β : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSpace β]
    (w : ι → NNReal) (haar gaussian : ι → Measure β)
    [∀ i, IsProbabilityMeasure (haar i)]
    [∀ i, IsProbabilityMeasure (gaussian i)]
    (hweight : ∑ i, (w i : ℝ) = 1)
    {delta : ℝ}
    (hfiber : ∀ i, probabilityTotalVariationLE
      (haar i) (gaussian i) delta) :
    probabilityTotalVariationLE
      (FiniteMixtureTV.taggedFiniteMixture w haar)
      (FiniteMixtureTV.taggedFiniteMixture w gaussian) delta :=
  FiniteMixtureTV.probabilityTotalVariationLE_taggedFiniteMixture_const
    w haar gaussian hweight hfiber

/-- UH4 specialized to canonical conditional laws with a mask-dependent
number of active columns.  Every good fiber is discharged by the Article's
same fixed-`K` endpoint, so the mixture keeps the single remainder
`delta_(M,N)`. -/
theorem canonicalVariableKHardSourceMaskHiding
    {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    (H : UnitaryHaarProbabilityFamily)
    (M N : ℕ) (hN : 1 ≤ N)
    (w : ι → NNReal) (Kmask : ι → ℕ)
    (hweight : ∑ i, (w i : ℝ) = 1)
    (hNK : ∀ i, N ≤ Kmask i) (hKM : ∀ i, Kmask i ≤ M) :
    probabilityTotalVariationLE
      (FiniteMixtureTV.taggedFiniteMixture w
        (fun i ↦ normalizedHaarTransposeGramLaw H M N (Kmask i)))
      (FiniteMixtureTV.taggedFiniteMixture w
        (fun i ↦ normalizedGaussianTransposeGramLaw N (Kmask i)))
      (min 1 (615172 * ultimateSquaredHidingRate M N)) := by
  letI : ∀ i, IsProbabilityMeasure
      (scaledHaarTransposeGramLaw H M N (Kmask i)) := fun i ↦
    scaledHaarTransposeGramLaw_isProbability H
      ((hNK i).trans (hKM i)) (hKM i)
  letI : ∀ i, IsProbabilityMeasure
      (gaussianTransposeGramLaw N (Kmask i)) := fun i ↦
    gaussianTransposeGramLaw_isProbability N (Kmask i)
  letI : ∀ i, IsProbabilityMeasure
      (normalizedHaarTransposeGramLaw H M N (Kmask i)) := fun i ↦
    Measure.isProbabilityMeasure_map
      (measurable_normalizeTransposeGram N (Kmask i)).aemeasurable
  letI : ∀ i, IsProbabilityMeasure
      (normalizedGaussianTransposeGramLaw N (Kmask i)) := fun i ↦
    Measure.isProbabilityMeasure_map
      (measurable_normalizeTransposeGram N (Kmask i)).aemeasurable
  exact hardSourceMaskFiniteMixtureHiding w
    (fun i ↦ normalizedHaarTransposeGramLaw H M N (Kmask i))
    (fun i ↦ normalizedGaussianTransposeGramLaw N (Kmask i)) hweight
    (fun i ↦ normalizedMatrixLaw H M N (Kmask i) hN (hNK i) (hKM i))

/-- UH4, exact bad-mask ledger.  Good fibers cost `delta`; arbitrary bad
fibers cost precisely their total mask probability. -/
theorem hardSourceMaskFiniteMixtureBadLedger
    {ι β : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSpace β]
    (w : ι → NNReal) (haar gaussian : ι → Measure β)
    [∀ i, IsProbabilityMeasure (haar i)]
    [∀ i, IsProbabilityMeasure (gaussian i)]
    (hweight : ∑ i, (w i : ℝ) = 1)
    (bad : ι → Prop) [DecidablePred bad]
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hgood : ∀ i, ¬ bad i → probabilityTotalVariationLE
      (haar i) (gaussian i) delta) :
    probabilityTotalVariationLE
      (FiniteMixtureTV.taggedFiniteMixture w haar)
      (FiniteMixtureTV.taggedFiniteMixture w gaussian)
      (delta + FiniteMixtureTV.badWeight w bad) :=
  FiniteMixtureTV.probabilityTotalVariationLE_taggedFiniteMixture_good_bad
    w haar gaussian hweight bad hdelta hgood

/-- If `beta` upper-bounds the bad-mask probability, the conservative ledger
is `delta + beta`. -/
theorem hardSourceMaskFiniteMixtureBadProbability
    {ι β : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSpace β]
    (w : ι → NNReal) (haar gaussian : ι → Measure β)
    [∀ i, IsProbabilityMeasure (haar i)]
    [∀ i, IsProbabilityMeasure (gaussian i)]
    (hweight : ∑ i, (w i : ℝ) = 1)
    (bad : ι → Prop) [DecidablePred bad]
    {delta beta : ℝ} (hdelta : 0 ≤ delta)
    (hgood : ∀ i, ¬ bad i → probabilityTotalVariationLE
      (haar i) (gaussian i) delta)
    (hbeta : FiniteMixtureTV.badWeight w bad ≤ beta) :
    probabilityTotalVariationLE
      (FiniteMixtureTV.taggedFiniteMixture w haar)
      (FiniteMixtureTV.taggedFiniteMixture w gaussian)
      (delta + beta) :=
  (hardSourceMaskFiniteMixtureBadLedger w haar gaussian hweight bad hdelta
    hgood).mono (by linarith)

/-- A common failure output on every bad mask removes the bad-mass term. -/
theorem hardSourceMaskFiniteMixtureCommonFailure
    {ι β : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSpace β]
    (w : ι → NNReal) (haar gaussian : ι → Measure β)
    [∀ i, IsProbabilityMeasure (haar i)]
    [∀ i, IsProbabilityMeasure (gaussian i)]
    (hweight : ∑ i, (w i : ℝ) = 1)
    (bad : ι → Prop) [DecidablePred bad]
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hgood : ∀ i, ¬ bad i → probabilityTotalVariationLE
      (haar i) (gaussian i) delta)
    (hbadEq : ∀ i, bad i → haar i = gaussian i) :
    probabilityTotalVariationLE
      (FiniteMixtureTV.taggedFiniteMixture w haar)
      (FiniteMixtureTV.taggedFiniteMixture w gaussian) delta := by
  apply hardSourceMaskFiniteMixtureHiding w haar gaussian hweight
  intro i
  by_cases hi : bad i
  · rw [hbadEq i hi]
    refine ⟨hdelta, ?_⟩
    intro s hs
    simpa using hdelta
  · exact hgood i hi

/-- UH4, rare-bad-mask bookkeeping.  Removing a bad set of probability at
most `beta` adds at most `beta` to a good-event bound. -/
theorem rareBadMaskEventBound
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsFiniteMeasure mu] (event bad : Set Ω)
    {target delta beta : ℝ}
    (hgood : mu.real (event \ bad) ≤ target + delta)
    (hbad : mu.real bad ≤ beta) :
    mu.real event ≤ target + delta + beta := by
  calc
    mu.real event ≤ mu.real ((event \ bad) ∪ bad) := by
      exact measureReal_mono (by
        intro x hx
        by_cases hxb : x ∈ bad
        · exact Or.inr hxb
        · exact Or.inl ⟨hx, hxb⟩) (by finiteness)
    _ ≤ mu.real (event \ bad) + mu.real bad := measureReal_union_le _ _
    _ ≤ (target + delta) + beta := add_le_add hgood hbad

/-- UH5: the paper's ensemble-consistency endpoint is the same arbitrary
Markov-kernel contraction, renamed for its benchmarking interpretation. -/
theorem ensembleConsistency
    {β : Type*} [MeasurableSpace β]
    (H : UnitaryHaarProbabilityFamily)
    (M N K : ℕ) (hN : 1 ≤ N) (hNK : N ≤ K) (hKM : K ≤ M)
    (benchmarkKernel : Kernel (Matrix (Fin N) (Fin N) ℂ) β)
    [IsMarkovKernel benchmarkKernel] :
    probabilityTotalVariationLE
      (benchmarkKernel ∘ₘ normalizedHaarTransposeGramLaw H M N K)
      (benchmarkKernel ∘ₘ normalizedGaussianTransposeGramLaw N K)
      (min 1 (615172 * ultimateSquaredHidingRate M N)) :=
  markovKernelPostprocessingLaw H M N K hN hNK hKM benchmarkKernel

/-- UH5, exact one-trial statement.  If the experimental marginal is within
`etaExp` of the postprocessed Haar law, then it is within `etaExp + delta` of
the postprocessed Gaussian law. -/
theorem ensembleConsistencyTriangle
    {β : Type*} [MeasurableSpace β]
    (H : UnitaryHaarProbabilityFamily)
    (M N K : ℕ) (hN : 1 ≤ N) (hNK : N ≤ K) (hKM : K ≤ M)
    (Q : Kernel (Matrix (Fin N) (Fin N) ℂ) β) [IsMarkovKernel Q]
    (Pexp : Measure β) {etaExp : ℝ}
    (hexp : probabilityTotalVariationLE Pexp
      (Q ∘ₘ normalizedHaarTransposeGramLaw H M N K) etaExp) :
    probabilityTotalVariationLE Pexp
      (Q ∘ₘ normalizedGaussianTransposeGramLaw N K)
      (etaExp + min 1 (615172 * ultimateSquaredHidingRate M N)) :=
  probabilityTotalVariationLE_trans_add hexp
    (markovKernelPostprocessingLaw H M N K hN hNK hKM Q)

/-- UH5, exact bounded-score consequence of the one-trial triangle bound. -/
theorem ensembleConsistencyBoundedExpectation
    {β : Type*} [MeasurableSpace β]
    (H : UnitaryHaarProbabilityFamily)
    (M N K : ℕ) (hN : 1 ≤ N) (hNK : N ≤ K) (hKM : K ≤ M)
    (Q : Kernel (Matrix (Fin N) (Fin N) ℂ) β) [IsMarkovKernel Q]
    (Pexp : Measure β) [IsProbabilityMeasure Pexp]
    {etaExp : ℝ}
    (hexp : probabilityTotalVariationLE Pexp
      (Q ∘ₘ normalizedHaarTransposeGramLaw H M N K) etaExp)
    (phi : β → ℝ) (hphi : Measurable phi)
    (hphi_nonneg : ∀ y, 0 ≤ phi y) (hphi_le_one : ∀ y, phi y ≤ 1) :
    |(∫ y, phi y ∂Pexp) -
        ∫ y, phi y ∂(Q ∘ₘ normalizedGaussianTransposeGramLaw N K)| ≤
      etaExp + min 1 (615172 * ultimateSquaredHidingRate M N) := by
  letI : IsProbabilityMeasure (scaledHaarTransposeGramLaw H M N K) :=
    scaledHaarTransposeGramLaw_isProbability H (hNK.trans hKM) hKM
  letI : IsProbabilityMeasure (gaussianTransposeGramLaw N K) :=
    gaussianTransposeGramLaw_isProbability N K
  letI : IsProbabilityMeasure (normalizedHaarTransposeGramLaw H M N K) :=
    Measure.isProbabilityMeasure_map
      (measurable_normalizeTransposeGram N K).aemeasurable
  letI : IsProbabilityMeasure (normalizedGaussianTransposeGramLaw N K) :=
    Measure.isProbabilityMeasure_map
      (measurable_normalizeTransposeGram N K).aemeasurable
  letI : IsProbabilityMeasure
      (Q ∘ₘ normalizedHaarTransposeGramLaw H M N K) := inferInstance
  letI : IsProbabilityMeasure
      (Q ∘ₘ normalizedGaussianTransposeGramLaw N K) := inferInstance
  exact boundedExpectationTransfer_of_probabilityTotalVariationLE
    Pexp (Q ∘ₘ normalizedGaussianTransposeGramLaw N K)
    (ensembleConsistencyTriangle H M N K hN hNK hKM Q Pexp hexp)
    phi hphi hphi_nonneg hphi_le_one

/-- UH5, exact Hoeffding endpoint for independent repetitions of a common
one-trial marginal and a measurable score in `[0,1]`. -/
theorem iidBoundedScoreHoeffding
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (P : Measure β) [IsProbabilityMeasure P]
    {R : ℕ} (hR : 1 ≤ R)
    (Y : Fin R → Ω → β)
    (hYmeas : ∀ i, Measurable (Y i))
    (hYindep : iIndepFun Y mu)
    (hYlaw : ∀ i, Measure.map (Y i) mu = P)
    (phi : β → ℝ) (hphi : Measurable phi)
    (hphi0 : ∀ y, 0 ≤ phi y) (hphi1 : ∀ y, phi y ≤ 1)
    {s : ℝ} (hs : 0 < s) :
    mu.real {ω |
        |((∑ i : Fin R, phi (Y i ω)) / (R : ℝ)) - ∫ y, phi y ∂P| > s} ≤
      2 * Real.exp (-2 * (R : ℝ) * s ^ 2) := by
  let m : ℝ := ∫ y, phi y ∂P
  let X : Fin R → Ω → ℝ := fun i ω ↦ phi (Y i ω) - m
  let c : NNReal := (‖(1 : ℝ) - 0‖₊ / 2) ^ 2
  have hRreal : (0 : ℝ) < R := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR)
  have hXindep : iIndepFun X mu := by
    exact hYindep.comp (fun _ y ↦ phi y - m)
      (fun _ ↦ hphi.sub measurable_const)
  have hmean (i : Fin R) : ∫ ω, phi (Y i ω) ∂mu = m := by
    rw [← integral_map (hYmeas i).aemeasurable hphi.aestronglyMeasurable]
    exact congrArg (fun xi : Measure β ↦ ∫ y, phi y ∂xi) (hYlaw i)
  have hsubG (i : Fin R) : HasSubgaussianMGF (X i) c mu := by
    have hraw := hasSubgaussianMGF_of_mem_Icc
      ((hphi.comp (hYmeas i)).aemeasurable)
      (ae_of_all mu fun ω ↦ ⟨hphi0 _, hphi1 _⟩)
    simpa [X, m, c, hmean i] using hraw
  have hupper :
      mu.real {ω | (R : ℝ) * s ≤ ∑ i : Fin R, X i ω} ≤
        Real.exp (-2 * (R : ℝ) * s ^ 2) := by
    have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      hXindep (s := Finset.univ) (c := fun _ ↦ c)
      (fun i _ ↦ hsubG i) (mul_nonneg hRreal.le hs.le)
    convert h using 1 <;>
      simp [c, div_eq_mul_inv] <;> field_simp <;> ring
  have hnegIndep : iIndepFun (fun i ω ↦ -X i ω) mu := by
    exact hXindep.comp (fun _ : Fin R ↦ fun x : ℝ ↦ -x)
      (fun _ ↦ measurable_neg)
  have hlower :
      mu.real {ω | (R : ℝ) * s ≤ ∑ i : Fin R, -X i ω} ≤
        Real.exp (-2 * (R : ℝ) * s ^ 2) := by
    have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      hnegIndep (s := Finset.univ) (c := fun _ ↦ c)
      (fun i _ ↦ (hsubG i).neg) (mul_nonneg hRreal.le hs.le)
    convert h using 1 <;>
      simp [c, div_eq_mul_inv] <;> field_simp <;> ring
  let upper : Set Ω := {ω | (R : ℝ) * s ≤ ∑ i : Fin R, X i ω}
  let lower : Set Ω := {ω | (R : ℝ) * s ≤ ∑ i : Fin R, -X i ω}
  have hsubset :
      {ω |
        |((∑ i : Fin R, phi (Y i ω)) / (R : ℝ)) - m| > s} ⊆
        upper ∪ lower := by
    intro ω hω
    change s < |((∑ i : Fin R, phi (Y i ω)) / (R : ℝ)) - m| at hω
    rcases lt_abs.mp hω with hpos | hneg
    · left
      dsimp [upper, X]
      have hsum :
          (∑ i : Fin R, (phi (Y i ω) - m)) =
            (∑ i : Fin R, phi (Y i ω)) - (R : ℝ) * m := by simp
      rw [hsum]
      apply le_of_lt
      calc
        (R : ℝ) * s < (R : ℝ) *
            (((∑ i : Fin R, phi (Y i ω)) / (R : ℝ)) - m) :=
          mul_lt_mul_of_pos_left hpos hRreal
        _ = (∑ i : Fin R, phi (Y i ω)) - (R : ℝ) * m := by
          field_simp [hRreal.ne']
    · right
      dsimp [lower, X]
      have hsum :
          (∑ i : Fin R, -(phi (Y i ω) - m)) =
            -((∑ i : Fin R, phi (Y i ω)) - (R : ℝ) * m) := by simp
      rw [hsum]
      apply le_of_lt
      calc
        (R : ℝ) * s < (R : ℝ) *
            (-(((∑ i : Fin R, phi (Y i ω)) / (R : ℝ)) - m)) :=
          mul_lt_mul_of_pos_left hneg hRreal
        _ = -((∑ i : Fin R, phi (Y i ω)) - (R : ℝ) * m) := by
          field_simp [hRreal.ne']
  calc
    mu.real {ω |
        |((∑ i : Fin R, phi (Y i ω)) / (R : ℝ)) - ∫ y, phi y ∂P| > s} =
        mu.real {ω |
          |((∑ i : Fin R, phi (Y i ω)) / (R : ℝ)) - m| > s} := by rfl
    _ ≤ mu.real (upper ∪ lower) := measureReal_mono hsubset (by finiteness)
    _ ≤ mu.real upper + mu.real lower := measureReal_union_le _ _
    _ ≤ Real.exp (-2 * (R : ℝ) * s ^ 2) +
        Real.exp (-2 * (R : ℝ) * s ^ 2) := add_le_add hupper hlower
    _ = 2 * Real.exp (-2 * (R : ℝ) * s ^ 2) := by ring

/-- UH5, the paper's exact rerandomized-score concentration statement. -/
theorem ensembleConsistencyRerandomizedScoreConcentration
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (H : UnitaryHaarProbabilityFamily)
    (M N K : ℕ) (hN : 1 ≤ N) (hNK : N ≤ K) (hKM : K ≤ M)
    (Q : Kernel (Matrix (Fin N) (Fin N) ℂ) β) [IsMarkovKernel Q]
    (Pexp : Measure β) [IsProbabilityMeasure Pexp]
    {etaExp : ℝ}
    (hexp : probabilityTotalVariationLE Pexp
      (Q ∘ₘ normalizedHaarTransposeGramLaw H M N K) etaExp)
    {R : ℕ} (hR : 1 ≤ R)
    (Y : Fin R → Ω → β)
    (hYmeas : ∀ i, Measurable (Y i))
    (hYindep : iIndepFun Y mu)
    (hYlaw : ∀ i, Measure.map (Y i) mu = Pexp)
    (phi : β → ℝ) (hphi : Measurable phi)
    (hphi0 : ∀ y, 0 ≤ phi y) (hphi1 : ∀ y, phi y ≤ 1)
    {s : ℝ} (hs : 0 < s) :
    mu.real {ω |
        |((∑ i : Fin R, phi (Y i ω)) / (R : ℝ)) -
            ∫ y, phi y ∂(Q ∘ₘ normalizedGaussianTransposeGramLaw N K)| >
          etaExp + min 1 (615172 * ultimateSquaredHidingRate M N) + s} ≤
      2 * Real.exp (-2 * (R : ℝ) * s ^ 2) := by
  let PG : Measure β := Q ∘ₘ normalizedGaussianTransposeGramLaw N K
  let d : ℝ := etaExp + min 1 (615172 * ultimateSquaredHidingRate M N)
  have hmean := ensembleConsistencyBoundedExpectation H M N K hN hNK hKM
    Q Pexp hexp phi hphi hphi0 hphi1
  have hsubset :
      {ω |
        |((∑ i : Fin R, phi (Y i ω)) / (R : ℝ)) - ∫ y, phi y ∂PG| > d + s} ⊆
      {ω |
        |((∑ i : Fin R, phi (Y i ω)) / (R : ℝ)) - ∫ y, phi y ∂Pexp| > s} := by
    intro ω hω
    change d + s <
      |((∑ i : Fin R, phi (Y i ω)) / (R : ℝ)) - ∫ y, phi y ∂PG| at hω
    change s <
      |((∑ i : Fin R, phi (Y i ω)) / (R : ℝ)) - ∫ y, phi y ∂Pexp|
    have htri :
        |((∑ i : Fin R, phi (Y i ω)) / (R : ℝ)) - ∫ y, phi y ∂PG| ≤
          |((∑ i : Fin R, phi (Y i ω)) / (R : ℝ)) - ∫ y, phi y ∂Pexp| +
            |(∫ y, phi y ∂Pexp) - ∫ y, phi y ∂PG| := by
      rw [show
        ((∑ i : Fin R, phi (Y i ω)) / (R : ℝ)) - ∫ y, phi y ∂PG =
          (((∑ i : Fin R, phi (Y i ω)) / (R : ℝ)) - ∫ y, phi y ∂Pexp) +
            ((∫ y, phi y ∂Pexp) - ∫ y, phi y ∂PG) by ring]
      exact abs_add_le
        (((∑ i : Fin R, phi (Y i ω)) / (R : ℝ)) - ∫ y, phi y ∂Pexp)
        ((∫ y, phi y ∂Pexp) - ∫ y, phi y ∂PG)
    change |(∫ y, phi y ∂Pexp) - ∫ y, phi y ∂PG| ≤ d at hmean
    linarith
  calc
    mu.real {ω |
        |((∑ i : Fin R, phi (Y i ω)) / (R : ℝ)) -
            ∫ y, phi y ∂(Q ∘ₘ normalizedGaussianTransposeGramLaw N K)| >
          etaExp + min 1 (615172 * ultimateSquaredHidingRate M N) + s} =
        mu.real {ω |
          |((∑ i : Fin R, phi (Y i ω)) / (R : ℝ)) - ∫ y, phi y ∂PG| >
            d + s} := by rfl
    _ ≤ mu.real {ω |
        |((∑ i : Fin R, phi (Y i ω)) / (R : ℝ)) - ∫ y, phi y ∂Pexp| > s} :=
      measureReal_mono hsubset (by finiteness)
    _ ≤ 2 * Real.exp (-2 * (R : ℝ) * s ^ 2) :=
      iidBoundedScoreHoeffding mu Pexp hR Y hYmeas hYindep hYlaw
        phi hphi hphi0 hphi1 hs

end

end LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding

#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.matrixLaw
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.normalizedMatrixLaw
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.certifiedHidingError_of_ambient
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.observableLaw
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.eventTransfer
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.observableEventTransfer
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.reverseObservableEventTransfer
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.reverseEventTransfer
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.boundedStatisticExpectationTransfer
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.markovKernelPostprocessingLaw
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.measurable_hafnianObservable
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.hafnianObservableLaw
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.measurable_preselectedPrincipalSubmatrixTuple
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.jointPreselectedPatternLaw
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.orderedGaussianPatternPanelLaw
#print axioms LogdetLean.GramHafnian.ThreePaper.DisjointGaussianRows.iIndepFun_orderedRowBlocks
#print axioms LogdetLean.GramHafnian.ThreePaper.DisjointGaussianRows.iIndepFun_orderedNormalizedGrams
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.orderedDisjointGaussianPatternProductLaw
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.orderedDisjointPatternProductHiding
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.disjointPatternIidPanelHiding
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.maxScoreCdfTransfer_iid
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.heavyCountBinomialTransfer_iid
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.orderedDisjointMaxScoreCdfTransfer
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.orderedDisjointHeavyCountBinomialTransfer
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.overlapGraphConcentrationTransfer_colored
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.orderedOverlapGraphConcentrationTransfer_colored_canonicalMean
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.hardSourceMaskFiniteMixtureHiding
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.canonicalVariableKHardSourceMaskHiding
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.hardSourceMaskFiniteMixtureBadProbability
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.hardSourceMaskFiniteMixtureCommonFailure
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.ensembleConsistencyTriangle
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.iidBoundedScoreHoeffding
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.ensembleConsistencyRerandomizedScoreConcentration

import GBSHiding.AllInputs

/-! All-input disjoint-pattern applications (Proposition G.2).
The Gaussian independence proof is reused; no comparison assumes `L ≤ K`.
-/
open scoped BigOperators ENNReal ProbabilityTheory unitInterval
open Filter MeasureTheory ProbabilityTheory Set
open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.UltimateHiding
open LogdetLean.GramHafnian.ThreePaper
open LogdetLean.GramHafnian.ThreePaper.UniformMatrixHiding

namespace GBSHiding
noncomputable section
set_option maxHeartbeats 2400000

theorem orderedDisjointPatternProductHidingAllInputs
    (H : UnitaryHaarProbabilityFamily)
    (M L K q N : ℕ) (hL : 1 ≤ L) (hLM : L ≤ M) (hK : 1 ≤ K) (hKM : K ≤ M)
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
  have htv := (observableHidingAllInputs H M L K hL hLM hK hKM
    (preselectedPrincipalSubmatrixTuple q L (orderedPatternSets rows))
    (measurable_preselectedPrincipalSubmatrixTuple q L (orderedPatternSets rows))).map
      (measurable_orderedPatternPanel rows)
  rw [orderedDisjointGaussianPatternProductLaw rows hrows] at htv
  exact htv

theorem orderedDisjointMaxScoreCdfTransferAllInputs
    (H : UnitaryHaarProbabilityFamily)
    (M L K q N : ℕ) (hL : 1 ≤ L) (hLM : L ≤ M) (hK : 1 ≤ K) (hKM : K ≤ M)
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
  have htv := (orderedDisjointPatternProductHidingAllInputs H M L K q N
    hL hLM hK hKM rows hrows).2
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

theorem orderedDisjointHeavyCountBinomialTransferAllInputs
    (H : UnitaryHaarProbabilityFamily)
    (M L K q N : ℕ) (hL : 1 ≤ L) (hLM : L ≤ M) (hK : 1 ≤ K) (hKM : K ≤ M)
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
  have htv := (orderedDisjointPatternProductHidingAllInputs H M L K q N
    hL hLM hK hKM rows hrows).map
      (measurable_orderedPanelHeavyCount h hh t)
  change probabilityTotalVariationLE
    (Measure.map (orderedPanelHeavyCount h t)
      (orderedPatternPanelHaarLaw H M L K q N rows))
    (Measure.map (orderedPanelHeavyCount h t) muP) _ at htv
  rw [hparam] at hGaussian
  rw [hGaussian] at htv
  exact htv

end
end GBSHiding

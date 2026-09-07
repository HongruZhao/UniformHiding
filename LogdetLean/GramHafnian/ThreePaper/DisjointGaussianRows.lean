import LogdetLean.GramHafnian.ThreePaper.FinitePanelLaws
import LogdetLean.GramHafnian.ThreePaper.GroupedIndependence
import LogdetLean.GramHafnian.MatrixLawEndpoints.EquationEndpoints

/-!
# Disjoint blocks of iid Gaussian rows

This file connects the project's concrete product-row Gaussian measure to the
explicit independence premises used by UH1--UH3.  It contains no scientific
axiom.
-/

open scoped BigOperators ENNReal ProbabilityTheory
open MeasureTheory ProbabilityTheory Set

namespace LogdetLean.GramHafnian.ThreePaper.DisjointGaussianRows

noncomputable section

open LocalAnticoncentration MatrixLawEndpoints UltimateHiding

/-- The finite image of an ordered row embedding. -/
def rowRange {N L : Nat} (rows : Fin N ↪ Fin L) : Finset (Fin L) :=
  Finset.univ.map rows

/-- An ambient matrix restricted to an ordered list of rows. -/
def orderedRowBlock {N L K : Nat} (rows : Fin N ↪ Fin L)
    (G : Matrix (Fin L) (Fin K) ℂ) : Matrix (Fin N) (Fin K) ℂ :=
  fun i k => G (rows i) k

@[fun_prop]
theorem measurable_orderedRowBlock {N L K : Nat} (rows : Fin N ↪ Fin L) :
    Measurable (orderedRowBlock (K := K) rows) := by
  unfold orderedRowBlock
  fun_prop

/-- The concrete iid Gaussian rectangular measure has mutually independent
row-vector coordinates. -/
theorem iIndepFun_standardComplexGaussian_rows (L K : Nat) :
    iIndepFun
      (fun i (G : Matrix (Fin L) (Fin K) ℂ) => G i)
      (standardComplexGaussianRectangularMeasure L K) := by
  unfold standardComplexGaussianRectangularMeasure
  change iIndepFun
    (fun i (G : Fin L → Fin K → ℂ) => G i)
    (Measure.map id (Measure.pi fun _ : Fin L => circularGaussianVector K))
  rw [Measure.map_id]
  exact iIndepFun_pi
    (μ := fun _ : Fin L => circularGaussianVector K)
    (X := fun _ => id) (fun _ => aemeasurable_id)

/-- Every row has the standard circular Gaussian vector law. -/
theorem map_gaussian_row (L K : Nat) (i : Fin L) :
    Measure.map (fun G : Matrix (Fin L) (Fin K) ℂ => G i)
      (standardComplexGaussianRectangularMeasure L K) =
      circularGaussianVector K := by
  unfold standardComplexGaussianRectangularMeasure
  change Measure.map (fun G : Fin L → Fin K → ℂ => G i)
      (Measure.map id (Measure.pi fun _ : Fin L => circularGaussianVector K)) = _
  rw [Measure.map_id]
  exact (measurePreserving_eval
    (fun _ : Fin L => circularGaussianVector K) i).map_eq

/-- Pairwise disjoint embedded row ranges give mutually independent ordered
row blocks. -/
theorem iIndepFun_orderedRowBlocks
    {ι : Type*} [Fintype ι] {N L K : Nat}
    (rows : ι → (Fin N ↪ Fin L))
    (hrows : Pairwise fun a b =>
      Disjoint (rowRange (rows a)) (rowRange (rows b))) :
    iIndepFun
      (fun j (G : Matrix (Fin L) (Fin K) ℂ) =>
        orderedRowBlock (K := K) (rows j) G)
      (standardComplexGaussianRectangularMeasure L K) := by
  let source : Fin L → Matrix (Fin L) (Fin K) ℂ → (Fin K → ℂ) :=
    fun i G => G i
  have hsource : iIndepFun source
      (standardComplexGaussianRectangularMeasure L K) :=
    iIndepFun_standardComplexGaussian_rows L K
  have hgroup : iIndepFun
      (fun j (G : Matrix (Fin L) (Fin K) ℂ)
        (i : rowRange (rows j)) => G i)
      (standardComplexGaussianRectangularMeasure L K) :=
    GroupedIndependence.iIndepFun_grouped_finsets
      (Omega := Matrix (Fin L) (Fin K) ℂ)
      source (fun _ => measurable_pi_apply _) hsource
      (fun j => rowRange (rows j)) hrows
  let reindex : (j : ι) →
      ((i : rowRange (rows j)) → Fin K → ℂ) →
        Matrix (Fin N) (Fin K) ℂ :=
    fun j block i k => block
      ⟨rows j i, by simp [rowRange]⟩ k
  have hreindex : ∀ j, Measurable (reindex j) := by
    intro j
    unfold reindex
    fun_prop
  have hout := hgroup.comp reindex hreindex
  have heq : ∀ j,
      (reindex j ∘
        (fun G : Matrix (Fin L) (Fin K) ℂ =>
          fun (i : rowRange (rows j)) => G i)) =ᵐ[
            standardComplexGaussianRectangularMeasure L K]
        orderedRowBlock (K := K) (rows j) := by
    intro j
    apply ae_of_all
    intro G
    ext i k
    rfl
  exact (iIndepFun_congr heq).mp hout

/-- An ordered subset of rows has exactly the smaller iid Gaussian matrix
law. -/
theorem map_orderedRowBlock
    {N L K : Nat} (rows : Fin N ↪ Fin L) :
    Measure.map (orderedRowBlock (K := K) rows)
      (standardComplexGaussianRectangularMeasure L K) =
      standardComplexGaussianRectangularMeasure N K := by
  have hind : iIndepFun
      (fun i (G : Matrix (Fin L) (Fin K) ℂ) => G (rows i))
      (standardComplexGaussianRectangularMeasure L K) :=
    (iIndepFun_standardComplexGaussian_rows L K).precomp rows.injective
  have hmeas (i : Fin N) : Measurable
      (fun G : Matrix (Fin L) (Fin K) ℂ => G (rows i)) :=
    measurable_pi_apply (rows i)
  have hfactor := FinitePanelLaws.iid_product_factorization
    (fun i (G : Matrix (Fin L) (Fin K) ℂ) => G (rows i))
    (fun i => (hmeas i).aemeasurable) hind
    (circularGaussianVector K) (fun i => map_gaussian_row L K (rows i))
  have hstandard : standardComplexGaussianRectangularMeasure N K =
      Measure.pi (fun _ : Fin N => circularGaussianVector K) := by
    unfold standardComplexGaussianRectangularMeasure
    change Measure.map id
      (Measure.pi fun _ : Fin N => circularGaussianVector K) = _
    rw [Measure.map_id]
  rw [hstandard]
  change Measure.map
    (fun G : Matrix (Fin L) (Fin K) ℂ => fun i => G (rows i))
    (standardComplexGaussianRectangularMeasure L K) = _
  exact hfactor

/-- Normalized transpose Gram of an ordered row block. -/
def orderedNormalizedGram {N L K : Nat} (rows : Fin N ↪ Fin L)
    (G : Matrix (Fin L) (Fin K) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  normalizedTransposeGramMatrix (orderedRowBlock (K := K) rows G)

@[fun_prop]
theorem measurable_orderedNormalizedGram {N L K : Nat}
    (rows : Fin N ↪ Fin L) :
    Measurable (orderedNormalizedGram (K := K) rows) :=
  ((measurable_normalizeTransposeGram N K).comp
      (measurable_rectangularTransposeGram N K)).comp
    (measurable_orderedRowBlock (K := K) rows)

/-- Disjoint ordered row blocks give independent normalized transpose-Gram
matrices. -/
theorem iIndepFun_orderedNormalizedGrams
    {ι : Type*} [Fintype ι] {N L K : Nat}
    (rows : ι → (Fin N ↪ Fin L))
    (hrows : Pairwise fun a b =>
      Disjoint (rowRange (rows a)) (rowRange (rows b))) :
    iIndepFun
      (fun j (G : Matrix (Fin L) (Fin K) ℂ) =>
        orderedNormalizedGram (K := K) (rows j) G)
      (standardComplexGaussianRectangularMeasure L K) := by
  simpa [orderedNormalizedGram, Function.comp_def] using
    (iIndepFun_orderedRowBlocks (K := K) rows hrows).comp
      (fun _ => normalizedTransposeGramMatrix)
      (fun _ => (measurable_normalizeTransposeGram N K).comp
        (measurable_rectangularTransposeGram N K))

/-- Every ordered normalized Gram block has the canonical smaller Gaussian
transpose-Gram law. -/
theorem map_orderedNormalizedGram
    {N L K : Nat} (rows : Fin N ↪ Fin L) :
    Measure.map (orderedNormalizedGram (K := K) rows)
      (standardComplexGaussianRectangularMeasure L K) =
      normalizedGaussianTransposeGramLaw N K := by
  unfold orderedNormalizedGram normalizedTransposeGramMatrix
  change Measure.map
      ((normalizeTransposeGram N K ∘ rectangularTransposeGram) ∘
        orderedRowBlock (K := K) rows)
      (standardComplexGaussianRectangularMeasure L K) = _
  rw [← Measure.map_map
    ((measurable_normalizeTransposeGram N K).comp
      (measurable_rectangularTransposeGram N K))
    (measurable_orderedRowBlock (K := K) rows)]
  rw [map_orderedRowBlock rows]
  unfold normalizedGaussianTransposeGramLaw gaussianTransposeGramLaw
  rw [Measure.map_map (measurable_normalizeTransposeGram N K)
    (measurable_rectangularTransposeGram N K)]

/-- The canonical normalized Gaussian Gram law as one pushforward from the
concrete iid row-product source. -/
theorem normalizedGaussianTransposeGramLaw_eq_map_source (N K : Nat) :
    normalizedGaussianTransposeGramLaw N K =
      Measure.map normalizedTransposeGramMatrix
        (standardComplexGaussianRectangularMeasure N K) := by
  unfold normalizedGaussianTransposeGramLaw gaussianTransposeGramLaw
    normalizedTransposeGramMatrix
  rw [Measure.map_map (measurable_normalizeTransposeGram N K)
    (measurable_rectangularTransposeGram N K)]
  rfl

end

end LogdetLean.GramHafnian.ThreePaper.DisjointGaussianRows

#print axioms LogdetLean.GramHafnian.ThreePaper.DisjointGaussianRows.iIndepFun_orderedRowBlocks
#print axioms LogdetLean.GramHafnian.ThreePaper.DisjointGaussianRows.iIndepFun_orderedNormalizedGrams
#print axioms LogdetLean.GramHafnian.ThreePaper.DisjointGaussianRows.map_orderedNormalizedGram
#print axioms LogdetLean.GramHafnian.ThreePaper.DisjointGaussianRows.normalizedGaussianTransposeGramLaw_eq_map_source

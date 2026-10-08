import A2.SpectrumGraph

open scoped BigOperators
open Matrix Polynomial MeasureTheory Set

noncomputable section
namespace A2Research

variable {𝕜 : Type*} [RCLike 𝕜] [PolishSpace 𝕜] {N : ℕ}
variable [MeasurableSpace (Matrix (Fin N) (Fin N) 𝕜)]
variable [BorelSpace (Matrix (Fin N) (Fin N) 𝕜)]

/-- Lusin--Souslin applied to the closed graph of ordered characteristic roots. -/
theorem measurableEmbedding_orderedSpectrumProjection :
    MeasurableEmbedding (orderedSpectrumProjection 𝕜 N) := by
  letI : PolishSpace (Matrix (Fin N) (Fin N) 𝕜) :=
    inferInstanceAs (PolishSpace (Fin N → Fin N → 𝕜))
  letI : PolishSpace (orderedSpectrumGraph 𝕜 N) :=
    (isClosed_orderedSpectrumGraph N).polishSpace
  exact (continuous_orderedSpectrumProjection N).measurableEmbedding
    (injective_orderedSpectrumProjection N)

/-- Mathlib's actual descending eigenvalue list is measurable for every
measurable Hermitian matrix family, including repeated eigenvalues. -/
theorem measurable_hermitian_eigenvalues₀ {α : Type*} [MeasurableSpace α]
    (A : α → Matrix (Fin N) (Fin N) 𝕜) (hA : ∀ x, (A x).IsHermitian)
    (hmeas : Measurable A) :
    Measurable (fun x ↦ (hA x).eigenvalues₀) := by
  let lift : α → orderedSpectrumGraph 𝕜 N :=
    fun x ↦ ⟨(A x, (hA x).eigenvalues₀), eigenvalues₀_mem_orderedSpectrumGraph (hA x)⟩
  have hlift : Measurable lift :=
    (measurableEmbedding_orderedSpectrumProjection.measurable_comp_iff).mp
      (by simpa [Function.comp_def, lift, orderedSpectrumProjection] using hmeas)
  have hsnd := measurable_snd.comp (measurable_subtype_coe.comp hlift)
  simpa [lift, Function.comp_def] using hsnd

/-- The fixed finite reindexing used in `Matrix.IsHermitian.eigenvalues`
preserves global measurability. -/
theorem measurable_hermitian_eigenvalues {α : Type*} [MeasurableSpace α]
    (A : α → Matrix (Fin N) (Fin N) 𝕜) (hA : ∀ x, (A x).IsHermitian)
    (hmeas : Measurable A) :
    Measurable (fun x ↦ (hA x).eigenvalues) := by
  have hordered := measurable_hermitian_eigenvalues₀ A hA hmeas
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa only [Matrix.IsHermitian.eigenvalues, Function.comp_def] using
    (measurable_pi_apply ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)).comp hordered

theorem measurable_eigenvalues₀ :
    Measurable (fun A : {A : Matrix (Fin N) (Fin N) 𝕜 // A.IsHermitian} ↦
      A.property.eigenvalues₀) :=
  measurable_hermitian_eigenvalues₀ Subtype.val (fun A ↦ A.property) measurable_subtype_coe

theorem measurable_eigenvalues :
    Measurable (fun A : {A : Matrix (Fin N) (Fin N) 𝕜 // A.IsHermitian} ↦
      A.property.eigenvalues) :=
  measurable_hermitian_eigenvalues Subtype.val (fun A ↦ A.property) measurable_subtype_coe

end A2Research

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.UltimateHiding.Dense

theorem continuous_coeHermitianGap (N : ℕ) :
    Continuous (coeHermitianGap : ConcreteMatrixState N → ConcreteMatrixState N) := by
  unfold coeHermitianGap
  fun_prop

/-- Global measurability of the paper's literal canonical spectrum map. -/
theorem measurable_canonicalGapSquaredSpectrum (N : ℕ) :
    Measurable (canonicalGapSquaredSpectrum N) := by
  have hgap := A2Research.measurable_hermitian_eigenvalues
    (coeHermitianGap : ConcreteMatrixState N → ConcreteMatrixState N)
    (fun C ↦ coeHermitianGap_isHermitian C) (continuous_coeHermitianGap N).measurable
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact measurable_const.sub ((measurable_pi_apply i).comp hgap)

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

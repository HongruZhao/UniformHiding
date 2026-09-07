import LogdetLean.GramHafnian.UltimateHiding.Dense.OneColumnConcrete
import LogdetLean.GramHafnian.UltimateHiding.Dense.RadialConcrete
import LogdetLean.GramHafnian.UltimateHiding.Dense.HaarAmbientPrefixFoundation
import LogdetLean.GramHafnian.UltimateHiding.HaarGaussianMatrixLaws
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Unitary transpose-congruence invariance of the concrete Haar corner law

The canonical `N x K` corner of a Haar unitary is unchanged in law when its
rows are multiplied by a fixed `U in U(N)`.  The proof embeds `U` as the
block-diagonal ambient unitary `U ⊕ I`, applies left invariance of Haar
measure on `U(m)`, and then transports the exact identity through the
transpose-Gram map and the paper normalization.

There is no scientific input in this file.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

open LocalAnticoncentration

/-- Left multiplication on the unitary subtype is measurable for its induced
matrix measurable structure.  This elementary adapter is local to the hiding
release, so importing the historical manuscript row-symmetry aggregate is unnecessary. -/
theorem measurable_unitary_mul_left_hiding {M : ℕ}
    (P : Matrix.unitaryGroup (Fin M) ℂ) :
    Measurable (fun U : Matrix.unitaryGroup (Fin M) ℂ => P * U) := by
  apply Measurable.subtype_mk
  change Measurable
    (fun U : Matrix.unitaryGroup (Fin M) ℂ =>
      (P : Matrix (Fin M) (Fin M) ℂ) *
        (U : Matrix (Fin M) (Fin M) ℂ))
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [Matrix.mul_apply]
  refine Finset.measurable_sum _ fun a _ => ?_
  have hcoe : Measurable
      (fun U : Matrix.unitaryGroup (Fin M) ℂ =>
        (U : Matrix (Fin M) (Fin M) ℂ)) :=
    measurable_subtype_coe
  exact measurable_const.mul
    ((measurable_pi_apply j).comp ((measurable_pi_apply a).comp hcoe))

/-- Multiplication by a block diagonal matrix, evaluated in its first block.
This small algebra lemma keeps the ambient-coordinate proof independent of
any inequality or probability input. -/
theorem fromBlocks_diagonal_mul_apply_inl
    {n r : Type*} [Fintype n] [Fintype r]
    [DecidableEq n] [DecidableEq r]
    (U : Matrix n n ℂ) (W : Matrix (n ⊕ r) (n ⊕ r) ℂ)
    (i : n) (j : n ⊕ r) :
    (Matrix.fromBlocks U 0 0 (1 : Matrix r r ℂ) * W) (Sum.inl i) j =
      ∑ a : n, U i a * W (Sum.inl a) j := by
  rw [← Matrix.fromBlocks_toBlocks W]
  rcases j with j | j <;>
    simp [Matrix.fromBlocks_multiply, Matrix.mul_apply]

/-- Left multiplication by `U ⊕ I` multiplies the canonical top-left
rectangular block on the left by `U`. -/
theorem topLeftUnitaryBlock_haarAmbientPrefixUnitary_mul
    {N K m : ℕ} (hNm : N ≤ m) (hKm : K ≤ m)
    (U : Matrix.unitaryGroup (Fin N) ℂ)
    (V : Matrix.unitaryGroup (Fin m) ℂ) :
    topLeftUnitaryBlock hNm hKm (haarAmbientPrefixUnitary hNm U * V) =
      (U : Matrix (Fin N) (Fin N) ℂ) *
        topLeftUnitaryBlock hNm hKm V := by
  let e := haarAmbientPrefixEquiv hNm
  let B : Matrix (Fin N ⊕ Fin (m - N)) (Fin N ⊕ Fin (m - N)) ℂ :=
    Matrix.fromBlocks (U : Matrix (Fin N) (Fin N) ℂ) 0 0 1
  let W : Matrix (Fin N ⊕ Fin (m - N)) (Fin N ⊕ Fin (m - N)) ℂ :=
    Matrix.reindex e.symm e.symm (V : Matrix (Fin m) (Fin m) ℂ)
  ext i j
  let s : Fin N ⊕ Fin (m - N) := e.symm (Fin.castLE hKm j)
  have heV : Matrix.reindex e e W =
      (V : Matrix (Fin m) (Fin m) ℂ) := by
    simp [W]
  have hrow : e.symm (Fin.castLE hNm i) = Sum.inl i := by
    apply e.injective
    simp [e]
  have hcol : e.symm (Fin.castLE hKm j) = s := rfl
  calc
    topLeftUnitaryBlock hNm hKm (haarAmbientPrefixUnitary hNm U * V) i j =
        (B * W) (Sum.inl i) s := by
      unfold topLeftUnitaryBlock
      simp only [Submonoid.coe_mul]
      rw [coe_haarAmbientPrefixUnitary]
      change
        ((Matrix.reindex e e B) *
            (V : Matrix (Fin m) (Fin m) ℂ))
              (Fin.castLE hNm i) (Fin.castLE hKm j) = _
      rw [← heV]
      have hmul : Matrix.reindex e e B * Matrix.reindex e e W =
          Matrix.reindex e e (B * W) := by
        change (Matrix.reindexAlgEquiv ℂ ℂ e B) *
            (Matrix.reindexAlgEquiv ℂ ℂ e W) =
          Matrix.reindexAlgEquiv ℂ ℂ e (B * W)
        exact (map_mul (Matrix.reindexAlgEquiv ℂ ℂ e) B W).symm
      rw [hmul]
      change (B * W) (e.symm (Fin.castLE hNm i))
          (e.symm (Fin.castLE hKm j)) = _
      rw [hrow, hcol]
    _ = ∑ a : Fin N,
          (U : Matrix (Fin N) (Fin N) ℂ) i a * W (Sum.inl a) s := by
      exact fromBlocks_diagonal_mul_apply_inl
        (U : Matrix (Fin N) (Fin N) ℂ) W i s
    _ = ((U : Matrix (Fin N) (Fin N) ℂ) *
          topLeftUnitaryBlock hNm hKm V) i j := by
      simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro a ha
      congr 1
      simp [W, s, e, Matrix.reindex_apply, topLeftUnitaryBlock]

/-- The unnormalized transpose-Gram statistic transforms by transpose
congruence under the embedded ambient unitary. -/
theorem scaledHaarTransposeGramMatrix_haarAmbientPrefixUnitary_mul
    {N K m : ℕ} (hNm : N ≤ m) (hKm : K ≤ m)
    (U : Matrix.unitaryGroup (Fin N) ℂ)
    (V : Matrix.unitaryGroup (Fin m) ℂ) :
    scaledHaarTransposeGramMatrix hNm hKm
        (haarAmbientPrefixUnitary hNm U * V) =
      (U : Matrix (Fin N) (Fin N) ℂ) *
          scaledHaarTransposeGramMatrix hNm hKm V *
        (U : Matrix (Fin N) (Fin N) ℂ).transpose := by
  let G := topLeftUnitaryBlock hNm hKm V
  have hblock := topLeftUnitaryBlock_haarAmbientPrefixUnitary_mul
    hNm hKm U V
  change
    (m : ℂ) • rectangularTransposeGram
        (topLeftUnitaryBlock hNm hKm
          (haarAmbientPrefixUnitary hNm U * V)) =
      (U : Matrix (Fin N) (Fin N) ℂ) *
          ((m : ℂ) • rectangularTransposeGram G) *
        (U : Matrix (Fin N) (Fin N) ℂ).transpose
  dsimp only [G]
  rw [hblock]
  unfold rectangularTransposeGram
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]

/-- The common deterministic normalization commutes with transpose
congruence. -/
theorem normalizeTransposeGram_unitaryCongruence
    {N K : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (A : ConcreteMatrixState N) :
    normalizeTransposeGram N K
        ((U : Matrix (Fin N) (Fin N) ℂ) * A *
          (U : Matrix (Fin N) (Fin N) ℂ).transpose) =
      (U : Matrix (Fin N) (Fin N) ℂ) *
          normalizeTransposeGram N K A *
        (U : Matrix (Fin N) (Fin N) ℂ).transpose := by
  unfold normalizeTransposeGram
  simp only [Matrix.mul_smul, Matrix.smul_mul]

theorem measurable_unitaryTransposeCongruence
    {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measurable fun A : ConcreteMatrixState N ↦
      (U : Matrix (Fin N) (Fin N) ℂ) * A *
        (U : Matrix (Fin N) (Fin N) ℂ).transpose := by
  exact measurable_complexMatrix_mul
    (measurable_complexMatrix_mul measurable_const measurable_id)
    (measurable_complexMatrix_transpose measurable_const)

theorem measurable_normalizedScaledHaarTransposeGramMatrix
    {N K m : ℕ} (hNm : N ≤ m) (hKm : K ≤ m) :
    Measurable fun V : Matrix.unitaryGroup (Fin m) ℂ ↦
      normalizeTransposeGram N K
        (scaledHaarTransposeGramMatrix hNm hKm V) :=
  (measurable_normalizeTransposeGram N K).comp
    (measurable_scaledHaarTransposeGramMatrix hNm hKm)

/-- Exact fixed-unitary transpose-congruence invariance of the normalized
Haar transpose-Gram corner law.  It is stated for an arbitrary normalized
Haar family, hence applies in particular to the canonical family. -/
theorem concreteHaarAmbientLaw_map_unitaryCongruence
    (H : LocalAnticoncentration.UnitaryHaarProbabilityFamily)
    {N K m : ℕ} (hNm : N ≤ m) (hKm : K ≤ m)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measure.map (fun A : ConcreteMatrixState N ↦
        (U : Matrix (Fin N) (Fin N) ℂ) * A *
          (U : Matrix (Fin N) (Fin N) ℂ).transpose)
      (concreteHaarAmbientLaw H N K m) =
    concreteHaarAmbientLaw H N K m := by
  let P := haarAmbientPrefixUnitary hNm U
  let stat : Matrix.unitaryGroup (Fin m) ℂ → ConcreteMatrixState N :=
    fun V ↦ normalizeTransposeGram N K
      (scaledHaarTransposeGramMatrix hNm hKm V)
  let act : ConcreteMatrixState N → ConcreteMatrixState N :=
    fun A ↦ (U : Matrix (Fin N) (Fin N) ℂ) * A *
      (U : Matrix (Fin N) (Fin N) ℂ).transpose
  have hstat : Measurable stat :=
    measurable_normalizedScaledHaarTransposeGramMatrix hNm hKm
  have hact : Measurable act := measurable_unitaryTransposeCongruence U
  have hleft : Measurable
      (fun V : Matrix.unitaryGroup (Fin m) ℂ ↦ P * V) :=
    measurable_unitary_mul_left_hiding P
  have hlaw : concreteHaarAmbientLaw H N K m =
      Measure.map stat (H.law m) := by
    unfold concreteHaarAmbientLaw normalizedHaarTransposeGramLaw
      scaledHaarTransposeGramLaw
    rw [dif_pos ⟨hNm, hKm⟩]
    rw [Measure.map_map (measurable_normalizeTransposeGram N K)
      (measurable_scaledHaarTransposeGramMatrix hNm hKm)]
    rfl
  letI : IsProbabilityMeasure (H.law m) := H.isProbability m
  letI : Measure.IsHaarMeasure (H.law m) := H.isHaar m
  rw [hlaw]
  calc
    Measure.map act (Measure.map stat (H.law m)) =
        Measure.map (act ∘ stat) (H.law m) :=
      Measure.map_map hact hstat
    _ = Measure.map (stat ∘ fun V ↦ P * V) (H.law m) := by
      apply Measure.map_congr
      filter_upwards [] with V
      dsimp only [Function.comp_apply, act, stat, P]
      rw [scaledHaarTransposeGramMatrix_haarAmbientPrefixUnitary_mul,
        normalizeTransposeGram_unitaryCongruence]
    _ = Measure.map stat
        (Measure.map (fun V ↦ P * V) (H.law m)) := by
      exact (Measure.map_map hstat hleft).symm
    _ = Measure.map stat (H.law m) := by
      rw [MeasureTheory.map_mul_left_eq_self]

end

end LogdetLean.GramHafnian.UltimateHiding.Dense

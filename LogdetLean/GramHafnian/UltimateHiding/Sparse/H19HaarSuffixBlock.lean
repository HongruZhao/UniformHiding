import LogdetLean.GramHafnian.UltimateHiding.Dense.HaarAmbientPrefixFoundation
import LogdetLean.GramHafnian.UltimateHiding.Dense.H1_RightInvariance
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic

/-!
# A suffix block-unitary rotation for the H19 column induction

For `L ≤ M`, this file embeds `U(M-L)` in the final ambient coordinates as
`I_L ⊕ V`.  Right multiplication by this embedded unitary fixes the first
`L` columns and rotates the remaining columns.  These are finite matrix and
normalized-Haar facts only; no density theorem is used.
-/

open MeasureTheory Matrix

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

/-- The ambient matrix `I_L ⊕ V`, reindexed to `Fin M`. -/
def h19HaarAmbientSuffixMatrix {L M : ℕ} (hLM : L ≤ M)
    (V : Matrix.unitaryGroup (Fin (M - L)) ℂ) :
    Matrix (Fin M) (Fin M) ℂ :=
  Matrix.reindex (haarAmbientPrefixEquiv hLM) (haarAmbientPrefixEquiv hLM)
    (Matrix.fromBlocks (1 : Matrix (Fin L) (Fin L) ℂ) 0 0
      (V : Matrix (Fin (M - L)) (Fin (M - L)) ℂ))

theorem h19HaarAmbientSuffixMatrix_mem_unitary {L M : ℕ} (hLM : L ≤ M)
    (V : Matrix.unitaryGroup (Fin (M - L)) ℂ) :
    h19HaarAmbientSuffixMatrix hLM V ∈ Matrix.unitaryGroup (Fin M) ℂ := by
  let e := haarAmbientPrefixEquiv hLM
  let V0 : Matrix (Fin (M - L)) (Fin (M - L)) ℂ := V
  let B : Matrix (Fin L ⊕ Fin (M - L)) (Fin L ⊕ Fin (M - L)) ℂ :=
    Matrix.fromBlocks (1 : Matrix (Fin L) (Fin L) ℂ) 0 0 V0
  have hV : V0 * Matrix.conjTranspose V0 = 1 := by
    simpa [V0, Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp V.property)
  have hB : B * Matrix.conjTranspose B = 1 := by
    simp [B, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, hV, ← Matrix.fromBlocks_one]
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  change Matrix.reindex e e B * Matrix.conjTranspose (Matrix.reindex e e B) = 1
  rw [Matrix.conjTranspose_reindex]
  calc
    Matrix.reindex e e B *
        Matrix.reindex e e (Matrix.conjTranspose B) =
        Matrix.reindex e e (B * Matrix.conjTranspose B) := by
      change (Matrix.reindexAlgEquiv ℂ ℂ e B) *
          (Matrix.reindexAlgEquiv ℂ ℂ e (Matrix.conjTranspose B)) =
        Matrix.reindexAlgEquiv ℂ ℂ e (B * Matrix.conjTranspose B)
      exact (map_mul (Matrix.reindexAlgEquiv ℂ ℂ e) B
        (Matrix.conjTranspose B)).symm
    _ = Matrix.reindex e e 1 := by rw [hB]
    _ = 1 := by simp

/-- The ambient suffix unitary `I_L ⊕ V`. -/
def h19HaarAmbientSuffixUnitary {L M : ℕ} (hLM : L ≤ M)
    (V : Matrix.unitaryGroup (Fin (M - L)) ℂ) :
    Matrix.unitaryGroup (Fin M) ℂ :=
  ⟨h19HaarAmbientSuffixMatrix hLM V,
    h19HaarAmbientSuffixMatrix_mem_unitary hLM V⟩

@[simp]
theorem coe_h19HaarAmbientSuffixUnitary {L M : ℕ} (hLM : L ≤ M)
    (V : Matrix.unitaryGroup (Fin (M - L)) ℂ) :
    (h19HaarAmbientSuffixUnitary hLM V : Matrix (Fin M) (Fin M) ℂ) =
      Matrix.reindex (haarAmbientPrefixEquiv hLM)
        (haarAmbientPrefixEquiv hLM)
        (Matrix.fromBlocks (1 : Matrix (Fin L) (Fin L) ℂ) 0 0
          (V : Matrix (Fin (M - L)) (Fin (M - L)) ℂ)) := by
  rfl

theorem measurable_h19HaarAmbientSuffixUnitary {L M : ℕ} (hLM : L ≤ M) :
    Measurable (h19HaarAmbientSuffixUnitary hLM) := by
  apply Measurable.subtype_mk
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  let e := haarAmbientPrefixEquiv hLM
  change Measurable fun c : Matrix.unitaryGroup (Fin (M - L)) ℂ ↦
    Matrix.fromBlocks (1 : Matrix (Fin L) (Fin L) ℂ)
      (0 : Matrix (Fin L) (Fin (M - L)) ℂ)
      (0 : Matrix (Fin (M - L)) (Fin L) ℂ)
      (c : Matrix (Fin (M - L)) (Fin (M - L)) ℂ)
      (e.symm i) (e.symm j)
  generalize hi : e.symm i = a
  generalize hj : e.symm j = b
  rcases a with a | a <;> rcases b with b | b
  · simp only [Matrix.fromBlocks_apply₁₁]
    fun_prop
  · simp only [Matrix.fromBlocks_apply₁₂]
    fun_prop
  · simp only [Matrix.fromBlocks_apply₂₁]
    fun_prop
  · simp only [Matrix.fromBlocks_apply₂₂]
    exact (measurable_pi_apply b).comp
      ((measurable_pi_apply a).comp measurable_subtype_coe)

/-- The leading block of `I_L ⊕ V` is literally the identity. -/
@[simp]
theorem h19HaarAmbientSuffixUnitary_apply_leading
    {L M : ℕ} (hLM : L ≤ M)
    (V : Matrix.unitaryGroup (Fin (M - L)) ℂ) (i j : Fin L) :
    (h19HaarAmbientSuffixUnitary hLM V : Matrix (Fin M) (Fin M) ℂ)
        (Fin.castLE hLM i) (Fin.castLE hLM j) =
      if i = j then 1 else 0 := by
  let e := haarAmbientPrefixEquiv hLM
  have hi : e.symm (Fin.castLE hLM i) = Sum.inl i := by
    apply e.injective
    simp [e]
  have hj : e.symm (Fin.castLE hLM j) = Sum.inl j := by
    apply e.injective
    simp [e]
  change Matrix.fromBlocks 1 0 0 (V : Matrix (Fin (M - L)) (Fin (M - L)) ℂ)
      (e.symm (Fin.castLE hLM i)) (e.symm (Fin.castLE hLM j)) = _
  rw [hi, hj]
  simp [Matrix.one_apply]

/-- The leading-to-suffix block of `I_L ⊕ V` is zero. -/
@[simp]
theorem h19HaarAmbientSuffixUnitary_apply_leading_suffix
    {L M : ℕ} (hLM : L ≤ M)
    (V : Matrix.unitaryGroup (Fin (M - L)) ℂ)
    (i : Fin L) (j : Fin (M - L)) :
    (h19HaarAmbientSuffixUnitary hLM V : Matrix (Fin M) (Fin M) ℂ)
        (Fin.castLE hLM i) (haarAmbientPrefixEquiv hLM (Sum.inr j)) = 0 := by
  let e := haarAmbientPrefixEquiv hLM
  have hi : e.symm (Fin.castLE hLM i) = Sum.inl i := by
    apply e.injective
    simp [e]
  change h19HaarAmbientSuffixMatrix hLM V
      (Fin.castLE hLM i) (e (Sum.inr j)) = 0
  change (Matrix.reindex e e
      (Matrix.fromBlocks (1 : Matrix (Fin L) (Fin L) ℂ)
        (0 : Matrix (Fin L) (Fin (M - L)) ℂ)
        (0 : Matrix (Fin (M - L)) (Fin L) ℂ)
        (V : Matrix (Fin (M - L)) (Fin (M - L)) ℂ)))
      (Fin.castLE hLM i) (e (Sum.inr j)) = 0
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, hi, e.symm_apply_apply]
  rfl

/-- The suffix-to-leading block of `I_L ⊕ V` is zero. -/
@[simp]
theorem h19HaarAmbientSuffixUnitary_apply_suffix_leading
    {L M : ℕ} (hLM : L ≤ M)
    (V : Matrix.unitaryGroup (Fin (M - L)) ℂ)
    (i : Fin (M - L)) (j : Fin L) :
    (h19HaarAmbientSuffixUnitary hLM V : Matrix (Fin M) (Fin M) ℂ)
        (haarAmbientPrefixEquiv hLM (Sum.inr i)) (Fin.castLE hLM j) = 0 := by
  let e := haarAmbientPrefixEquiv hLM
  have hj : e.symm (Fin.castLE hLM j) = Sum.inl j := by
    apply e.injective
    simp [e]
  change h19HaarAmbientSuffixMatrix hLM V
      (e (Sum.inr i)) (Fin.castLE hLM j) = 0
  change (Matrix.reindex e e
      (Matrix.fromBlocks (1 : Matrix (Fin L) (Fin L) ℂ)
        (0 : Matrix (Fin L) (Fin (M - L)) ℂ)
        (0 : Matrix (Fin (M - L)) (Fin L) ℂ)
        (V : Matrix (Fin (M - L)) (Fin (M - L)) ℂ)))
      (e (Sum.inr i)) (Fin.castLE hLM j) = 0
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, e.symm_apply_apply, hj]
  rfl

/-- The suffix block of `I_L ⊕ V` is `V`. -/
@[simp]
theorem h19HaarAmbientSuffixUnitary_apply_suffix
    {L M : ℕ} (hLM : L ≤ M)
    (V : Matrix.unitaryGroup (Fin (M - L)) ℂ)
    (i j : Fin (M - L)) :
    (h19HaarAmbientSuffixUnitary hLM V : Matrix (Fin M) (Fin M) ℂ)
        (haarAmbientPrefixEquiv hLM (Sum.inr i))
        (haarAmbientPrefixEquiv hLM (Sum.inr j)) =
      (V : Matrix (Fin (M - L)) (Fin (M - L)) ℂ) i j := by
  simp [h19HaarAmbientSuffixUnitary, h19HaarAmbientSuffixMatrix,
    Matrix.reindex_apply]

/-- Right multiplication by `I_L ⊕ V` leaves each of the first `L` columns
unchanged. -/
theorem mul_h19HaarAmbientSuffixUnitary_apply_leading
    {L M : ℕ} (hLM : L ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ)
    (V : Matrix.unitaryGroup (Fin (M - L)) ℂ)
    (i : Fin M) (j : Fin L) :
    ((U * h19HaarAmbientSuffixUnitary hLM V :
        Matrix.unitaryGroup (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ)
        i (Fin.castLE hLM j) =
      (U : Matrix (Fin M) (Fin M) ℂ) i (Fin.castLE hLM j) := by
  simp only [Submonoid.coe_mul, Matrix.mul_apply]
  let e := haarAmbientPrefixEquiv hLM
  rw [← Fintype.sum_equiv e
    (fun k : Fin L ⊕ Fin (M - L) ↦
      (U : Matrix (Fin M) (Fin M) ℂ) i (e k) *
        (h19HaarAmbientSuffixUnitary hLM V : Matrix (Fin M) (Fin M) ℂ)
          (e k) (Fin.castLE hLM j))
    (fun k : Fin M ↦
      (U : Matrix (Fin M) (Fin M) ℂ) i k *
        (h19HaarAmbientSuffixUnitary hLM V : Matrix (Fin M) (Fin M) ℂ)
          k (Fin.castLE hLM j)) (fun _ ↦ rfl)]
  rw [Fintype.sum_sum_type]
  simp [e, Matrix.one_apply]

/-- Joint measurability of multiplication by the suffix block when both the
ambient unitary and the suffix unitary vary. -/
theorem measurable_mul_h19HaarAmbientSuffixUnitary_uncurry
    {L M : ℕ} (hLM : L ≤ M) :
    Measurable
      (fun p : Matrix.unitaryGroup (Fin M) ℂ ×
          Matrix.unitaryGroup (Fin (M - L)) ℂ ↦
        p.1 * h19HaarAmbientSuffixUnitary hLM p.2) := by
  apply Measurable.subtype_mk
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  change Measurable fun p : Matrix.unitaryGroup (Fin M) ℂ ×
      Matrix.unitaryGroup (Fin (M - L)) ℂ ↦
    ∑ k : Fin M,
      (p.1 : Matrix (Fin M) (Fin M) ℂ) i k *
        (h19HaarAmbientSuffixUnitary hLM p.2 :
          Matrix (Fin M) (Fin M) ℂ) k j
  refine Finset.measurable_sum _ fun k _ ↦ ?_
  have hleft : Measurable fun p : Matrix.unitaryGroup (Fin M) ℂ ×
      Matrix.unitaryGroup (Fin (M - L)) ℂ ↦
      (p.1 : Matrix (Fin M) (Fin M) ℂ) i k :=
    (measurable_pi_apply k).comp ((measurable_pi_apply i).comp
      (measurable_subtype_coe.comp measurable_fst))
  have hright : Measurable fun p : Matrix.unitaryGroup (Fin M) ℂ ×
      Matrix.unitaryGroup (Fin (M - L)) ℂ ↦
      (h19HaarAmbientSuffixUnitary hLM p.2 :
        Matrix (Fin M) (Fin M) ℂ) k j :=
    (measurable_pi_apply j).comp ((measurable_pi_apply k).comp
      (measurable_subtype_coe.comp
        ((measurable_h19HaarAmbientSuffixUnitary hLM).comp measurable_snd)))
  exact hleft.mul hright

/-- Measurability of right multiplication by one fixed suffix block. -/
theorem measurable_mul_h19HaarAmbientSuffixUnitary_right
    {L M : ℕ} (hLM : L ≤ M)
    (V : Matrix.unitaryGroup (Fin (M - L)) ℂ) :
    Measurable (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
      U * h19HaarAmbientSuffixUnitary hLM V) := by
  exact (measurable_mul_h19HaarAmbientSuffixUnitary_uncurry hLM).comp
    (measurable_id.prodMk measurable_const)

/-- Averaging a normalized Haar unitary over an independent suffix rotation
does not change its marginal law. -/
theorem map_mul_h19HaarAmbientSuffixUnitary_prod_haar
    {L M : ℕ} (hLM : L ≤ M) :
    Measure.map
        (fun p : Matrix.unitaryGroup (Fin M) ℂ ×
            Matrix.unitaryGroup (Fin (M - L)) ℂ ↦
          p.1 * h19HaarAmbientSuffixUnitary hLM p.2)
        ((unitaryHaarProbabilityMeasure M).prod
          (unitaryHaarProbabilityMeasure (M - L))) =
      unitaryHaarProbabilityMeasure M := by
  let μ := unitaryHaarProbabilityMeasure M
  let ν := unitaryHaarProbabilityMeasure (M - L)
  let rotate := fun p : Matrix.unitaryGroup (Fin M) ℂ ×
      Matrix.unitaryGroup (Fin (M - L)) ℂ ↦
        p.1 * h19HaarAmbientSuffixUnitary hLM p.2
  have hrotate : Measurable rotate := by
    exact measurable_mul_h19HaarAmbientSuffixUnitary_uncurry hLM
  letI : IsProbabilityMeasure μ :=
    unitaryHaarProbabilityMeasure_isProbability M
  letI : IsProbabilityMeasure ν :=
    unitaryHaarProbabilityMeasure_isProbability (M - L)
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map' hf.aemeasurable hrotate.aemeasurable]
  change (∫⁻ p, (f ∘ rotate) p ∂μ.prod ν) = ∫⁻ U, f U ∂μ
  rw [lintegral_prod_symm _ (hf.comp hrotate).aemeasurable]
  change (∫⁻ V, ∫⁻ U,
      f (U * h19HaarAmbientSuffixUnitary hLM V) ∂μ ∂ν) =
    ∫⁻ U, f U ∂μ
  have hfixed (V : Matrix.unitaryGroup (Fin (M - L)) ℂ) :
      ∫⁻ U, f (U * h19HaarAmbientSuffixUnitary hLM V) ∂μ =
        ∫⁻ U, f U ∂μ := by
    have hmap := map_unitaryHaarProbabilityMeasure_mul_right_h1 M
      (h19HaarAmbientSuffixUnitary hLM V)
    calc
      ∫⁻ U, f (U * h19HaarAmbientSuffixUnitary hLM V) ∂μ =
          ∫⁻ U, f U ∂Measure.map
            (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
              U * h19HaarAmbientSuffixUnitary hLM V) μ := by
        symm
        exact lintegral_map' hf.aemeasurable
          (measurable_mul_h19HaarAmbientSuffixUnitary_right hLM V).aemeasurable
      _ = ∫⁻ U, f U ∂μ := by rw [hmap]
  simp_rw [hfixed]
  rw [lintegral_const]
  simp

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse

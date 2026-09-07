import LogdetLean.GramHafnian.UltimateHiding.Dense.H1_RowStiefelDefinitions
import LogdetLean.GramHafnian.UltimateHiding.Dense.H1_RowGramOrbit
import LogdetLean.GramHafnian.UltimateHiding.Dense.HaarAmbientPrefixFoundation
import Mathlib.Tactic

/-!
# Right-unitary invariance for the two H1 row-block laws

These are the elementary Haar-equivariance lemmas used in the internal
row-Stiefel deletion proof.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

open LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.UltimateHiding.Sparse

local instance matrixBorelSpaceH1 (N K : ℕ) :
    BorelSpace (Matrix (Fin N) (Fin K) ℂ) := by
  exact inferInstanceAs (BorelSpace (Fin N → Fin K → ℂ))

local instance matrixSecondCountableTopologyH1 (N K : ℕ) :
    SecondCountableTopology (Matrix (Fin N) (Fin K) ℂ) := by
  exact inferInstanceAs
    (SecondCountableTopology (Fin N → Fin K → ℂ))

local instance unitaryGroupSecondCountableTopologyH1 (m : ℕ) :
    SecondCountableTopology (Matrix.unitaryGroup (Fin m) ℂ) := by
  exact TopologicalSpace.secondCountableTopology_induced
    (Matrix.unitaryGroup (Fin m) ℂ)
    (Matrix (Fin m) (Fin m) ℂ) Subtype.val

/-- Right multiplication by a block diagonal matrix, evaluated in its first
block. -/
theorem mul_fromBlocks_diagonal_apply_inl_h1
    {n r : Type*} [Fintype n] [Fintype r]
    [DecidableEq n] [DecidableEq r]
    (W : Matrix (n ⊕ r) (n ⊕ r) ℂ) (V : Matrix n n ℂ)
    (i : n ⊕ r) (j : n) :
    (W * Matrix.fromBlocks V 0 0 (1 : Matrix r r ℂ)) i (Sum.inl j) =
      ∑ a : n, W i (Sum.inl a) * V a j := by
  rw [← Matrix.fromBlocks_toBlocks W]
  rcases i with i | i <;>
    simp [Matrix.fromBlocks_multiply, Matrix.mul_apply]

/-- Multiplying the ambient unitary on the right by `V ⊕ 1` multiplies the
deleted top-row block on the right by `V`. -/
theorem sqrtScaledDeleteLastTopRows_mul_prefixUnitary
    {N m : ℕ} (hNsucc : N ≤ m + 1)
    (U : Matrix.unitaryGroup (Fin (m + 1)) ℂ)
    (V : Matrix.unitaryGroup (Fin m) ℂ) :
    sqrtScaledDeleteLastTopRows hNsucc
        (U * haarAmbientPrefixUnitary (Nat.le_succ m) V) =
      sqrtScaledDeleteLastTopRows hNsucc U *
        (V : Matrix (Fin m) (Fin m) ℂ) := by
  let e := haarAmbientPrefixEquiv (Nat.le_succ m)
  let B : Matrix (Fin m ⊕ Fin ((m + 1) - m))
      (Fin m ⊕ Fin ((m + 1) - m)) ℂ :=
    Matrix.fromBlocks (V : Matrix (Fin m) (Fin m) ℂ) 0 0 1
  let W : Matrix (Fin m ⊕ Fin ((m + 1) - m))
      (Fin m ⊕ Fin ((m + 1) - m)) ℂ :=
    Matrix.reindex e.symm e.symm
      (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
  ext i j
  let ri : Fin (m + 1) := Fin.castLE hNsucc i
  have heU : Matrix.reindex e e W =
      (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
    simp [W]
  have hcol : e.symm (Fin.castLE (Nat.le_succ m) j) = Sum.inl j := by
    apply e.injective
    simp [e]
  change ((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
      ((U * haarAmbientPrefixUnitary (Nat.le_succ m) V :
        Matrix.unitaryGroup (Fin (m + 1)) ℂ) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
        ri (Fin.castLE (Nat.le_succ m) j) = _
  simp only [Submonoid.coe_mul]
  rw [coe_haarAmbientPrefixUnitary]
  change ((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
      (((U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) *
        Matrix.reindex e e B) ri (Fin.castLE (Nat.le_succ m) j)) = _
  rw [← heU]
  have hmul : Matrix.reindex e e W * Matrix.reindex e e B =
      Matrix.reindex e e (W * B) := by
    change (Matrix.reindexAlgEquiv ℂ ℂ e W) *
        (Matrix.reindexAlgEquiv ℂ ℂ e B) =
      Matrix.reindexAlgEquiv ℂ ℂ e (W * B)
    exact (map_mul (Matrix.reindexAlgEquiv ℂ ℂ e) W B).symm
  rw [hmul]
  change ((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
      (W * B) (e.symm ri) (e.symm (Fin.castLE (Nat.le_succ m) j)) = _
  rw [hcol]
  rw [mul_fromBlocks_diagonal_apply_inl_h1 W
    (V : Matrix (Fin m) (Fin m) ℂ)]
  simp only [Matrix.mul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hentry := congrArg
    (fun A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ ↦
      A ri (Fin.castLE (Nat.le_succ m) a)) heU
  have hcola : e.symm (Fin.castLE (Nat.le_succ m) a) = Sum.inl a := by
    apply e.injective
    simp [e]
  change W (e.symm ri) (e.symm (Fin.castLE (Nat.le_succ m) a)) =
      (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
        ri (Fin.castLE (Nat.le_succ m) a) at hentry
  rw [hcola] at hentry
  have hentry' : W (e.symm ri) (Sum.inl a) =
      (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
        ri (Fin.castLE (Nat.le_succ m) a) := by
    simpa [Matrix.reindex_apply] using hentry
  rw [hentry']
  change ((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
      ((U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
        ri (Fin.castLE (Nat.le_succ m) a) *
          (V : Matrix (Fin m) (Fin m) ℂ) a j) =
    (((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
      (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
        ri (Fin.castLE (Nat.le_succ m) a)) *
      (V : Matrix (Fin m) (Fin m) ℂ) a j
  ring

/-- The complete scaled top-row block is equivariant for ambient right
multiplication. -/
theorem sqrtScaledFullTopRows_mul
    {N m : ℕ} (hNm : N ≤ m)
    (U V : Matrix.unitaryGroup (Fin m) ℂ) :
    sqrtScaledFullTopRows hNm (U * V) =
      sqrtScaledFullTopRows hNm U *
        (V : Matrix (Fin m) (Fin m) ℂ) := by
  ext i j
  change ((Real.sqrt (m : ℝ) : ℝ) : ℂ) *
      (∑ a : Fin m,
        (U : Matrix (Fin m) (Fin m) ℂ) (Fin.castLE hNm i) a *
          (V : Matrix (Fin m) (Fin m) ℂ) a j) =
    ∑ a : Fin m,
      (((Real.sqrt (m : ℝ) : ℝ) : ℂ) *
        (U : Matrix (Fin m) (Fin m) ℂ) (Fin.castLE hNm i) a) *
          (V : Matrix (Fin m) (Fin m) ℂ) a j
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Normalized Haar probability on a finite unitary group is right
invariant. -/
theorem map_unitaryHaarProbabilityMeasure_mul_right_h1
    (m : ℕ) (V : Matrix.unitaryGroup (Fin m) ℂ) :
    Measure.map (fun U : Matrix.unitaryGroup (Fin m) ℂ ↦ U * V)
        (unitaryHaarProbabilityMeasure m) =
      unitaryHaarProbabilityMeasure m := by
  let G := Matrix.unitaryGroup (Fin m) ℂ
  let μ : Measure G := unitaryHaarProbabilityMeasure m
  let ν : Measure G := Measure.map (fun U : G ↦ U * V) μ
  letI : CompactSpace G :=
    isCompact_iff_compactSpace.mp (unitaryGroup_carrier_isCompact m)
  letI : IsProbabilityMeasure μ :=
    unitaryHaarProbabilityMeasure_isProbability m
  letI : Measure.IsHaarMeasure μ :=
    canonicalUnitaryHaarProbabilityFamily.isHaar m
  haveI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map
      (measurable_mul_const V).aemeasurable
  letI : Measure.IsHaarMeasure ν := by
    dsimp only [ν]
    infer_instance
  have hν : ν = μ :=
    Measure.isHaarMeasure_eq_of_isProbabilityMeasure ν μ
  simpa only [ν, μ] using hν

/-- The law of the deleted scaled top-row block is right-unitarily
invariant. -/
theorem map_sqrtScaledDeleteLastTopRows_rightUnitary_invariant
    {N m : ℕ} (hNsucc : N ≤ m + 1)
    (V : Matrix.unitaryGroup (Fin m) ℂ) :
    Measure.map (h1RightUnitaryAction (N := N) V)
        (Measure.map (sqrtScaledDeleteLastTopRows hNsucc)
          (unitaryHaarProbabilityMeasure (m + 1))) =
      Measure.map (sqrtScaledDeleteLastTopRows hNsucc)
        (unitaryHaarProbabilityMeasure (m + 1)) := by
  let P := haarAmbientPrefixUnitary (Nat.le_succ m) V
  let r : Matrix.unitaryGroup (Fin (m + 1)) ℂ →
      Matrix.unitaryGroup (Fin (m + 1)) ℂ := fun U ↦ U * P
  have hr : Measurable r := measurable_mul_const P
  have hdel : Measurable (sqrtScaledDeleteLastTopRows hNsucc) :=
    measurable_sqrtScaledDeleteLastTopRows hNsucc
  have hact : Measurable (h1RightUnitaryAction (N := N) V) :=
    (continuous_h1RightUnitaryAction (N := N) V).measurable
  calc
    Measure.map (h1RightUnitaryAction (N := N) V)
        (Measure.map (sqrtScaledDeleteLastTopRows hNsucc)
          (unitaryHaarProbabilityMeasure (m + 1))) =
      Measure.map
        (h1RightUnitaryAction (N := N) V ∘
          sqrtScaledDeleteLastTopRows hNsucc)
        (unitaryHaarProbabilityMeasure (m + 1)) :=
      Measure.map_map hact hdel
    _ = Measure.map (sqrtScaledDeleteLastTopRows hNsucc ∘ r)
        (unitaryHaarProbabilityMeasure (m + 1)) := by
      apply Measure.map_congr
      filter_upwards [] with U
      exact (sqrtScaledDeleteLastTopRows_mul_prefixUnitary
        hNsucc U V).symm
    _ = Measure.map (sqrtScaledDeleteLastTopRows hNsucc)
        (Measure.map r (unitaryHaarProbabilityMeasure (m + 1))) :=
      (Measure.map_map hdel hr).symm
    _ = Measure.map (sqrtScaledDeleteLastTopRows hNsucc)
        (unitaryHaarProbabilityMeasure (m + 1)) := by
      rw [show Measure.map r (unitaryHaarProbabilityMeasure (m + 1)) =
          unitaryHaarProbabilityMeasure (m + 1) by
        exact map_unitaryHaarProbabilityMeasure_mul_right_h1 (m + 1) P]

/-- Equivariance of the independent one-column row update under right
multiplication of its Haar input. -/
theorem scaledRowStiefelDeletionUpdate_mul
    {N m : ℕ} (hNm : N ≤ m)
    (U V : Matrix.unitaryGroup (Fin m) ℂ)
    (p : ℝ × ComplexUnitSphere N) :
    scaledRowStiefelDeletionUpdate hNm (U * V, p) =
      h1RightUnitaryAction V
        (scaledRowStiefelDeletionUpdate hNm (U, p)) := by
  unfold scaledRowStiefelDeletionUpdate h1RightUnitaryAction
  rw [sqrtScaledFullTopRows_mul]
  simp only [Matrix.mul_assoc]

/-- The independent beta/sphere one-column update law is right-unitarily
invariant. -/
theorem map_scaledRowStiefelDeletionUpdate_rightUnitary_invariant
    {N m : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m)
    (V : Matrix.unitaryGroup (Fin m) ℂ) :
    Measure.map (h1RightUnitaryAction (N := N) V)
        (Measure.map (scaledRowStiefelDeletionUpdate hNm)
          ((unitaryHaarProbabilityMeasure m).prod
            (concreteOneColumnParameterLaw m N))) =
      Measure.map (scaledRowStiefelDeletionUpdate hNm)
        ((unitaryHaarProbabilityMeasure m).prod
          (concreteOneColumnParameterLaw m N)) := by
  let r : Matrix.unitaryGroup (Fin m) ℂ →
      Matrix.unitaryGroup (Fin m) ℂ := fun U ↦ U * V
  let R : Matrix.unitaryGroup (Fin m) ℂ ×
      (ℝ × ComplexUnitSphere N) →
      Matrix.unitaryGroup (Fin m) ℂ ×
        (ℝ × ComplexUnitSphere N) := Prod.map r id
  have hr : Measurable r := measurable_mul_const V
  have hR : Measurable R := hr.prodMap measurable_id
  have hupd : Measurable (scaledRowStiefelDeletionUpdate hNm) :=
    measurable_scaledRowStiefelDeletionUpdate hNm
  have hact : Measurable (h1RightUnitaryAction (N := N) V) :=
    (continuous_h1RightUnitaryAction (N := N) V).measurable
  letI : IsProbabilityMeasure (concreteOneColumnParameterLaw m N) :=
    concreteOneColumnParameterLaw_isProbability hN hNm
  have hprod : Measure.map R
      ((unitaryHaarProbabilityMeasure m).prod
        (concreteOneColumnParameterLaw m N)) =
      (unitaryHaarProbabilityMeasure m).prod
        (concreteOneColumnParameterLaw m N) := by
    calc
      Measure.map R
          ((unitaryHaarProbabilityMeasure m).prod
            (concreteOneColumnParameterLaw m N)) =
        (Measure.map r (unitaryHaarProbabilityMeasure m)).prod
          (Measure.map id (concreteOneColumnParameterLaw m N)) :=
        (Measure.map_prod_map _ _ hr measurable_id).symm
      _ = (unitaryHaarProbabilityMeasure m).prod
          (concreteOneColumnParameterLaw m N) := by
        rw [Measure.map_id,
          map_unitaryHaarProbabilityMeasure_mul_right_h1 m V]
  calc
    Measure.map (h1RightUnitaryAction (N := N) V)
        (Measure.map (scaledRowStiefelDeletionUpdate hNm)
          ((unitaryHaarProbabilityMeasure m).prod
            (concreteOneColumnParameterLaw m N))) =
      Measure.map
        (h1RightUnitaryAction (N := N) V ∘
          scaledRowStiefelDeletionUpdate hNm)
        ((unitaryHaarProbabilityMeasure m).prod
          (concreteOneColumnParameterLaw m N)) :=
      Measure.map_map hact hupd
    _ = Measure.map (scaledRowStiefelDeletionUpdate hNm ∘ R)
        ((unitaryHaarProbabilityMeasure m).prod
          (concreteOneColumnParameterLaw m N)) := by
      apply Measure.map_congr
      filter_upwards [] with p
      exact (scaledRowStiefelDeletionUpdate_mul hNm p.1 V p.2).symm
    _ = Measure.map (scaledRowStiefelDeletionUpdate hNm)
        (Measure.map R
          ((unitaryHaarProbabilityMeasure m).prod
            (concreteOneColumnParameterLaw m N))) :=
      (Measure.map_map hupd hR).symm
    _ = Measure.map (scaledRowStiefelDeletionUpdate hNm)
        ((unitaryHaarProbabilityMeasure m).prod
          (concreteOneColumnParameterLaw m N)) := by rw [hprod]

end

end LogdetLean.GramHafnian.UltimateHiding.Dense

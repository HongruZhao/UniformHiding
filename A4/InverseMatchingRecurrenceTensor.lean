import A4.InverseMatchingRecurrenceFamily
import A4.InverseMomentAlgebra
import A4.MatchingGramProduct
import A4.WishartDensityInverseIntegrability

open MeasureTheory
open scoped BigOperators Matrix

noncomputable section
namespace A4Research

open MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

/-- The two entries of each ordered pair, as a single vertex-index array. -/
def entryPairListVertices {d n : ℕ} (x : EntryPairList d n) : Fin (2 * n) → Fin d :=
  fun v ↦ if ((matchingSlotEquiv n).symm v).2 = 0 then
    (x ((matchingSlotEquiv n).symm v).1).1
  else (x ((matchingSlotEquiv n).symm v).1).2

/-- The ordered standard pairs in a vertex-index array. -/
def vertexEntryPairList {d n : ℕ} (j : Fin (2 * n) → Fin d) : EntryPairList d n :=
  fun i ↦ (j (leftSlot i), j (rightSlot i))

@[simp] theorem entryPairListVertices_left {d n : ℕ} (x : EntryPairList d n) (i : Fin n) :
    entryPairListVertices x (leftSlot i) = (x i).1 := by
  unfold entryPairListVertices
  rw [← matchingSlotEquiv_zero]
  simp only [Equiv.symm_apply_apply]
  simp

@[simp] theorem entryPairListVertices_right {d n : ℕ} (x : EntryPairList d n) (i : Fin n) :
    entryPairListVertices x (rightSlot i) = (x i).2 := by
  unfold entryPairListVertices
  rw [← matchingSlotEquiv_one]
  simp only [Equiv.symm_apply_apply]
  simp

@[simp] theorem vertexEntryPairList_vertices {d n : ℕ} (x : EntryPairList d n) :
    vertexEntryPairList (entryPairListVertices x) = x := by
  funext i
  simp [vertexEntryPairList]

@[simp] theorem entryPairListVertices_vertexEntryPairList {d n : ℕ}
    (j : Fin (2 * n) → Fin d) : entryPairListVertices (vertexEntryPairList j) = j := by
  funext v
  obtain ⟨⟨i, b⟩, rfl⟩ := (matchingSlotEquiv n).surjective v
  fin_cases b
  · change entryPairListVertices (vertexEntryPairList j) (matchingSlotEquiv n (i, 0)) =
      j (matchingSlotEquiv n (i, 0))
    rw [matchingSlotEquiv_zero, entryPairListVertices_left]
    rfl
  · change entryPairListVertices (vertexEntryPairList j) (matchingSlotEquiv n (i, 1)) =
      j (matchingSlotEquiv n (i, 1))
    rw [matchingSlotEquiv_one, entryPairListVertices_right]
    rfl

/-- The actual complete inverse-entry tensor of the characterized law. -/
def inverseEntryMomentTensor {d : ℕ} {beta : ℝ} {sigma : SymPosDef d}
    (W : W_d d beta sigma) (n : ℕ) (x : EntryPairList d n) : ℂ :=
  Complex.ofReal (∫ w : SymPosDef d,
    ∏ r : Fin n, w.1⁻¹ (x r).1 (x r).2 ∂W.toMeasure)

@[simp] theorem inverseEntryMomentTensor_zero {d : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma) (x : EntryPairList d 0) :
    inverseEntryMomentTensor W 0 x = 1 := by
  let := W.probability
  simp [inverseEntryMomentTensor]

/-- A literal matching monomial evaluated on a symmetric entry weight. -/
def matchingEntryWeight {d n : ℕ} (A : Fin d → Fin d → ℂ)
    (j : Fin (2 * n) → Fin d) (M : PM n) : ℂ :=
  ∏ i : M.pairReps, A (j i.1) (j (M i.1))

/-- Matsumoto's modified inverse coefficients applied to the standard source
pairing. This is the explicit candidate, not an assumed moment identity. -/
def inverseWeingartenVertexTensor {d : ℕ} (n : ℕ) (gamma : ℝ)
    (A : Fin d → Fin d → ℂ) (j : Fin (2 * n) → Fin d) : ℂ :=
  ∑ N : PM n, modifiedGramInverse n gamma (standardPairPartition n) N *
    matchingEntryWeight A j N

def inverseWeingartenEntryTensor {d : ℕ} (gamma : ℝ)
    (A : Fin d → Fin d → ℂ) (n : ℕ) (x : EntryPairList d n) : ℂ :=
  inverseWeingartenVertexTensor n gamma A (entryPairListVertices x)

theorem matchingEntryWeight_relabel {d n : ℕ} (A : Fin d → Fin d → ℂ)
    (hA : ∀ a b, A a b = A b a) (g : Equiv.Perm (Fin (2 * n)))
    (j : Fin (2 * n) → Fin d) (M : PM n) :
    matchingEntryWeight A (j ∘ g) M =
      matchingEntryWeight A j (transportPairPartition g M) := by
  let f : Fin (2 * n) → Fin (2 * n) → ℂ := fun a b ↦ A (j a) (j b)
  have hf : ∀ a b, f a b = f b a := fun a b ↦ hA (j a) (j b)
  have hmatch : transportedPairPartition (g * canonicalMatchingPermutation M) =
      transportPairPartition g M := by
    change transportPairPartition (g * canonicalMatchingPermutation M)
      (standardPairPartition n) = _
    rw [transportPairPartition_mul]
    change transportPairPartition g (transportedPairPartition (canonicalMatchingPermutation M)) = _
    rw [canonicalMatchingPermutation_transport]
  have hfirst := prod_symmetric_pairWeight_transport (canonicalMatchingPermutation M)
    (fun a b ↦ f (g a) (g b)) (fun a b ↦ hf (g a) (g b))
  rw [canonicalMatchingPermutation_transport] at hfirst
  have hsecond := prod_symmetric_pairWeight_transport
    (g * canonicalMatchingPermutation M) f hf
  rw [hmatch] at hsecond
  change (∏ i : M.pairReps, f (g i.1) (g (M i.1))) = _
  rw [← hfirst]
  simpa only [Equiv.Perm.mul_apply, matchingEntryWeight, f] using hsecond

theorem modifiedGramInverse_relabel {n : ℕ} (gamma : ℝ)
    (g : Equiv.Perm (Fin (2 * n))) (M N : PM n) :
    modifiedGramInverse n gamma (transportPairPartition g M)
      (transportPairPartition g N) = modifiedGramInverse n gamma M N := by
  simp only [modifiedGramInverse, Matrix.smul_apply, smul_eq_mul,
    orthogonalGram_inv_transport]

/-- Relabeling the vertex array changes the source matching by exactly the
same relabeling. All output matchings are retained. -/
theorem inverseWeingartenVertexTensor_relabel {d n : ℕ} (gamma : ℝ)
    (A : Fin d → Fin d → ℂ) (hA : ∀ a b, A a b = A b a)
    (g : Equiv.Perm (Fin (2 * n))) (j : Fin (2 * n) → Fin d) :
    inverseWeingartenVertexTensor n gamma A (j ∘ g) =
      ∑ N : PM n, modifiedGramInverse n gamma (transportedPairPartition g) N *
        matchingEntryWeight A j N := by
  classical
  unfold inverseWeingartenVertexTensor
  calc
    _ = ∑ N : PM n, modifiedGramInverse n gamma (transportedPairPartition g)
        (transportPairPartition g N) *
          matchingEntryWeight A j (transportPairPartition g N) := by
      apply Finset.sum_congr rfl
      intro N _
      rw [matchingEntryWeight_relabel A hA g j N]
      change _ = modifiedGramInverse n gamma
        (transportPairPartition g (standardPairPartition n))
        (transportPairPartition g N) * _
      rw [modifiedGramInverse_relabel]
    _ = _ := (matchingRelabelEquiv g).sum_comp
      (fun N ↦ modifiedGramInverse n gamma (transportedPairPartition g) N *
        matchingEntryWeight A j N)

/-- A proved standard ordered-pair tensor formula gives every row of the
exact source matching tensor, without an invariant-basis assumption. -/
theorem inverse_pairFormula_of_standard_tensor {d n : ℕ} {beta gamma : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma)
    (hstandard : inverseEntryMomentTensor W n =
      inverseWeingartenEntryTensor gamma (fun a b ↦ (sigma.1⁻¹ a b : ℂ)) n)
    (M : PM n) (j : Fin (2 * n) → Fin d) :
    Complex.ofReal (∫ w : SymPosDef d, ∏ i : M.pairReps,
      w.1⁻¹ (j i.1) (j (M i.1)) ∂W.toMeasure) =
      ∑ N : PM n, modifiedGramInverse n gamma M N *
        ∏ i : N.pairReps, (sigma.1⁻¹ (j i.1) (j (N i.1)) : ℂ) := by
  let g := canonicalMatchingPermutation M
  let x : EntryPairList d n := vertexEntryPairList (j ∘ g)
  have hprod (w : SymPosDef d) :
      (∏ r : Fin n, w.1⁻¹ (x r).1 (x r).2) =
        ∏ i : M.pairReps, w.1⁻¹ (j i.1) (j (M i.1)) := by
    have h := prod_symmetric_pairWeight_transport g
      (fun a b ↦ w.1⁻¹ (j a) (j b)) (fun a b ↦
        (Matrix.isHermitian_iff_isSymm.mp w.2.inv.isHermitian).apply (j b) (j a))
    rw [show transportedPairPartition g = M from canonicalMatchingPermutation_transport M] at h
    simpa only [g, x, vertexEntryPairList, Function.comp_apply] using h
  have hx := congrFun hstandard x
  unfold inverseEntryMomentTensor at hx
  simp_rw [hprod] at hx
  rw [inverseWeingartenEntryTensor, entryPairListVertices_vertexEntryPairList] at hx
  have hA : ∀ a b : Fin d, (sigma.1⁻¹ a b : ℂ) = (sigma.1⁻¹ b a : ℂ) := by
    intro a b
    exact congrArg Complex.ofReal
      ((Matrix.isHermitian_iff_isSymm.mp sigma.2.inv.isHermitian).apply b a)
  rw [inverseWeingartenVertexTensor_relabel gamma _ hA,
    show transportedPairPartition g = M from canonicalMatchingPermutation_transport M] at hx
  exact hx

end A4Research

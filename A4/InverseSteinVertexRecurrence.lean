import A4.InverseSteinRealShape
import A4.InverseMatchingRecurrenceActual
import A4.MatchingGramDegreeFactorizationSlots

open MeasureTheory Matrix
open scoped BigOperators

noncomputable section
namespace A4Research.InverseStein

open MatsumotoPaper
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def inverseVertexMomentTensor {d : ℕ} {beta : ℝ} {sigma : SymPosDef d}
    (W : W_d d beta sigma) (n : ℕ) (j : Fin (2 * n) → Fin d) : ℂ :=
  inverseEntryMomentTensor W n (vertexEntryPairList j)

@[simp] theorem inverseVertexMomentTensor_zero {d : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma) (j : Fin (2 * 0) → Fin d) :
    inverseVertexMomentTensor W 0 j = 1 :=
  inverseEntryMomentTensor_zero W (vertexEntryPairList j)

@[simp] theorem inverseVertexMomentTensor_vertices {d n : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma) (x : EntryPairList d n) :
    inverseVertexMomentTensor W n (entryPairListVertices x) = inverseEntryMomentTensor W n x := by
  simp only [inverseVertexMomentTensor, vertexEntryPairList_vertices]

theorem firstPairSwitch_remaining_other {q : ℕ} (t s : Fin (2 * q)) (h : s ≠ t) :
    firstPairSwitch q t (remainingVertex q s) = remainingVertex q s := by
  exact Equiv.swap_apply_of_ne_of_ne (remainingVertex_ne_first q s)
    (fun e ↦ h (remainingVertex_injective q e))

theorem inverseVertex_leftSlot_ne_rightSlot {q : ℕ} (i r : Fin q) :
    leftSlot i ≠ rightSlot r := by
  intro h
  have hv := congrArg Fin.val h
  simp only [leftSlot, rightSlot] at hv
  omega

theorem inverseVertex_leftSlot_injective {q : ℕ} :
    Function.Injective (leftSlot : Fin q → Fin (2 * q)) := by
  intro i r h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [leftSlot] at hv
  omega

theorem inverseVertex_rightSlot_injective {q : ℕ} :
    Function.Injective (rightSlot : Fin q → Fin (2 * q)) := by
  intro i r h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [rightSlot] at hv
  omega

@[simp] theorem vertexEntryPairList_remaining {d q : ℕ}
    (j : Fin (2 * (q + 1)) → Fin d) :
    vertexEntryPairList (fun t ↦ j (remainingVertex q t)) =
      Fin.tail (vertexEntryPairList j) := by
  funext i
  simp only [vertexEntryPairList, remainingVertex_leftSlot, remainingVertex_rightSlot,
    Fin.tail]

theorem vertexEntryPairList_switchLeft {d q : ℕ}
    (j : Fin (2 * (q + 1)) → Fin d) (r : Fin q) :
    vertexEntryPairList (j ∘ firstPairSwitch q (leftSlot r)) =
      inverseSwapRight (vertexEntryPairList (fun t ↦ j (remainingVertex q t)))
        (j (firstVertex q)) (j (secondVertex q)) r := by
  funext i
  refine Fin.cases ?_ (fun s ↦ ?_) i
  · simp only [vertexEntryPairList, Function.comp_apply, inverseSwapRight,
      Fin.cons_zero, firstVertex_leftSlot, secondVertex_rightSlot,
      ← remainingVertex_leftSlot, ← remainingVertex_rightSlot]
    rw [← firstVertex_leftSlot, ← secondVertex_rightSlot,
      firstPairSwitch_first, firstPairSwitch_second]
  · by_cases h : s = r
    · subst s
      simp only [vertexEntryPairList, Function.comp_apply, inverseSwapRight,
        Fin.cons_succ, Function.update_self,
        ← remainingVertex_leftSlot, ← remainingVertex_rightSlot]
      rw [firstPairSwitch_remaining_self,
        firstPairSwitch_remaining_other _ _
          (inverseVertex_leftSlot_ne_rightSlot r r).symm]
    · simp only [vertexEntryPairList, Function.comp_apply, inverseSwapRight,
        Fin.cons_succ, Function.update_of_ne h,
        ← remainingVertex_leftSlot, ← remainingVertex_rightSlot]
      rw [firstPairSwitch_remaining_other _ _
          (fun e ↦ h (inverseVertex_leftSlot_injective e)),
        firstPairSwitch_remaining_other _ _
          (inverseVertex_leftSlot_ne_rightSlot r s).symm]

theorem vertexEntryPairList_switchRight {d q : ℕ}
    (j : Fin (2 * (q + 1)) → Fin d) (r : Fin q) :
    vertexEntryPairList (j ∘ firstPairSwitch q (rightSlot r)) =
      Fin.cons (j (remainingVertex q (rightSlot r)), j (secondVertex q))
        (Function.update (vertexEntryPairList (fun t ↦ j (remainingVertex q t))) r
          (j (remainingVertex q (leftSlot r)), j (firstVertex q))) := by
  funext i
  refine Fin.cases ?_ (fun s ↦ ?_) i
  · simp only [vertexEntryPairList, Function.comp_apply, Fin.cons_zero]
    rw [← firstVertex_leftSlot, ← secondVertex_rightSlot,
      firstPairSwitch_first, firstPairSwitch_second]
  · by_cases h : s = r
    · subst s
      simp only [vertexEntryPairList, Function.comp_apply, Fin.cons_succ,
        Function.update_self, ← remainingVertex_leftSlot, ← remainingVertex_rightSlot]
      rw [firstPairSwitch_remaining_other _ _ (inverseVertex_leftSlot_ne_rightSlot r r),
        firstPairSwitch_remaining_self]
    · simp only [vertexEntryPairList, Function.comp_apply, Fin.cons_succ,
        Function.update_of_ne h, ← remainingVertex_leftSlot, ← remainingVertex_rightSlot]
      rw [firstPairSwitch_remaining_other _ _ (inverseVertex_leftSlot_ne_rightSlot s r),
        firstPairSwitch_remaining_other _ _
          (fun e ↦ h (inverseVertex_rightSlot_injective e))]

theorem product_vertexEntryPairList_switchRight {d q : ℕ}
    (j : Fin (2 * (q + 1)) → Fin d) (r : Fin q)
    (X : RealMatrix d) (hX : X.IsSymm) :
    (∏ i : Fin (q + 1), X (vertexEntryPairList
        (j ∘ firstPairSwitch q (rightSlot r)) i).1
      (vertexEntryPairList (j ∘ firstPairSwitch q (rightSlot r)) i).2) =
      ∏ i : Fin (q + 1), X (inverseSwapLeft
          (vertexEntryPairList (fun t ↦ j (remainingVertex q t)))
          (j (firstVertex q)) (j (secondVertex q)) r i).1
        (inverseSwapLeft (vertexEntryPairList (fun t ↦ j (remainingVertex q t)))
          (j (firstVertex q)) (j (secondVertex q)) r i).2 := by
  rw [vertexEntryPairList_switchRight, product_inverseSwapLeft]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [product_updated_pairs]
  simp only [vertexEntryPairList]
  rw [hX.apply (j (remainingVertex q (rightSlot r))) (j (secondVertex q))]
  ring

theorem inverseVertexMomentTensor_switchLeft {d q : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma)
    (j : Fin (2 * (q + 1)) → Fin d) (r : Fin q) :
    inverseVertexMomentTensor W (q + 1) (j ∘ firstPairSwitch q (leftSlot r)) =
      Complex.ofReal (inverseEntryMoment W
        (inverseSwapRight (vertexEntryPairList (fun t ↦ j (remainingVertex q t)))
          (j (firstVertex q)) (j (secondVertex q)) r)) := by
  simp only [inverseVertexMomentTensor, inverseEntryMomentTensor,
    vertexEntryPairList_switchLeft, inverseEntryMoment]

theorem inverseVertexMomentTensor_switchRight {d q : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma)
    (j : Fin (2 * (q + 1)) → Fin d) (r : Fin q) :
    inverseVertexMomentTensor W (q + 1) (j ∘ firstPairSwitch q (rightSlot r)) =
      Complex.ofReal (inverseEntryMoment W
        (inverseSwapLeft (vertexEntryPairList (fun t ↦ j (remainingVertex q t)))
          (j (firstVertex q)) (j (secondVertex q)) r)) := by
  unfold inverseVertexMomentTensor inverseEntryMomentTensor inverseEntryMoment
  congr 1
  apply integral_congr_ae
  filter_upwards [] with w
  exact product_vertexEntryPairList_switchRight j r w.1⁻¹
    (Matrix.isHermitian_iff_isSymm.mp w.2.inv.isHermitian)

theorem prepend_inverseVertexPairList {d q : ℕ}
    (j : Fin (2 * (q + 1)) → Fin d) :
    prependInverseEntry (vertexEntryPairList (fun t ↦ j (remainingVertex q t)))
      (j (firstVertex q)) (j (secondVertex q)) = vertexEntryPairList j := by
  rw [vertexEntryPairList_remaining]
  simpa only [prependInverseEntry, firstVertex_leftSlot, secondVertex_rightSlot,
    vertexEntryPairList] using Fin.cons_self_tail (vertexEntryPairList j)

/-- The actual inverse moment tensor satisfies the first-vertex swap
recurrence for every real shape at the original degree margin. The proof
uses only the independently proved entry recurrence and literal finite
products, with no candidate matching invariance premise. -/
theorem inverseVertexMomentTensor_recurrence_identity
    {d q : ℕ} {beta gamma : ℝ} (W : W_d d beta (identityScale d))
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (q : ℝ) < gamma)
    (j : Fin (2 * (q + 1)) → Fin d) :
    (gamma : ℂ) * inverseVertexMomentTensor W (q + 1) j -
        (1 / 2 : ℂ) * ∑ r : Fin q,
          (inverseVertexMomentTensor W (q + 1)
              (j ∘ firstPairSwitch q (leftSlot r)) +
            inverseVertexMomentTensor W (q + 1)
              (j ∘ firstPairSwitch q (rightSlot r))) =
      ((identityScale d).1⁻¹ (j (firstVertex q)) (j (secondVertex q)) : ℂ) *
        inverseVertexMomentTensor W q (fun t ↦ j (remainingVertex q t)) := by
  have h := congrArg Complex.ofReal (W.inverse_entry_recurrence_identity hgamma hgap
    (vertexEntryPairList (fun t ↦ j (remainingVertex q t)))
    (j (firstVertex q)) (j (secondVertex q)))
  rw [prepend_inverseVertexPairList] at h
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_one, Complex.ofReal_sum,
    Complex.ofReal_add] at h
  simp only [inverseVertexMomentTensor_switchLeft, inverseVertexMomentTensor_switchRight]
  have hs : (∑ r : Fin q,
      (Complex.ofReal (inverseEntryMoment W
          (inverseSwapRight (vertexEntryPairList (fun t ↦ j (remainingVertex q t)))
            (j (firstVertex q)) (j (secondVertex q)) r)) +
        Complex.ofReal (inverseEntryMoment W
          (inverseSwapLeft (vertexEntryPairList (fun t ↦ j (remainingVertex q t)))
            (j (firstVertex q)) (j (secondVertex q)) r)))) =
      ∑ r : Fin q,
      (Complex.ofReal (inverseEntryMoment W
          (inverseSwapLeft (vertexEntryPairList (fun t ↦ j (remainingVertex q t)))
            (j (firstVertex q)) (j (secondVertex q)) r)) +
        Complex.ofReal (inverseEntryMoment W
          (inverseSwapRight (vertexEntryPairList (fun t ↦ j (remainingVertex q t)))
            (j (firstVertex q)) (j (secondVertex q)) r))) := by
    apply Finset.sum_congr rfl
    intro r _
    exact add_comm _ _
  rw [hs]
  exact h

end A4Research.InverseStein

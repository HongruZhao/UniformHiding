import A4.InverseMatchingRecurrenceTensor
import A4.InverseEntryRecurrenceRealShape
import A4.InverseMomentsFull

open MeasureTheory
open scoped BigOperators Matrix

noncomputable section
namespace A4Research

open MatsumotoPaper InverseStein

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

theorem orthogonalGram_zero (z : ℂ) :
    orthogonalGram 0 z = (1 : Matrix (PM 0) (PM 0) ℂ) := by
  classical
  ext M N
  have hMN : M = N := pairPartition_ext (fun i ↦ Fin.elim0 i)
  subst N
  have hk : matchingKappa M M = 0 := by
    simpa using matchingKappa_self M
  simp only [orthogonalGram, hk, pow_zero, Matrix.one_apply_eq]

@[simp] theorem inverseWeingartenEntryTensor_zero {d : ℕ} (gamma : ℝ)
    (A : Fin d → Fin d → ℂ) (x : EntryPairList d 0) :
    inverseWeingartenEntryTensor gamma A 0 x = 1 := by
  classical
  haveI : Subsingleton (PM 0) := ⟨fun M N ↦ pairPartition_ext (fun i ↦ Fin.elim0 i)⟩
  letI : Unique (PM 0) :=
    { default := standardPairPartition 0
      uniq := fun M ↦ Subsingleton.elim M _ }
  simp [inverseWeingartenEntryTensor, inverseWeingartenVertexTensor,
    modifiedGramInverse, orthogonalGram_zero, matchingEntryWeight, Matrix.one_apply]
  exact Subsingleton.elim _ _

@[simp] theorem inverseEntryMomentTensor_eq_ofReal_entryMoment {d q : ℕ}
    {beta : ℝ} {sigma : SymPosDef d} (W : W_d d beta sigma)
    (x : EntryPairList d q) :
    inverseEntryMomentTensor W q x = Complex.ofReal (inverseEntryMoment W x) := rfl

@[simp] theorem prependInverseEntry_tail {d q : ℕ} (x : EntryPairList d (q + 1)) :
    prependInverseEntry (Fin.tail x) (x 0).1 (x 0).2 = x := by
  exact Fin.cons_self_tail x

@[simp] theorem inversePairSwitchLeft_eq_tuple {d q : ℕ}
    (x : EntryPairList d (q + 1)) (r : Fin q) :
    inversePairSwitchLeft r x = inverseSwapLeft (Fin.tail x) (x 0).1 (x 0).2 r := rfl

@[simp] theorem inversePairSwitchRight_eq_tuple {d q : ℕ}
    (x : EntryPairList d (q + 1)) (r : Fin q) :
    inversePairSwitchRight r x = inverseSwapRight (Fin.tail x) (x 0).1 (x 0).2 r := rfl

/-- The actual complete tensor inherits every independently proved real
entry recurrence, without an invariant-tensor or matching-system premise. -/
theorem inverseEntryMomentTensor_recurrenceThrough {d : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma) (n : ℕ) (gamma : ℝ)
    (hentry : ∀ q : ℕ, q < n → ∀ (indices : Fin q → Fin d × Fin d) (a b : Fin d),
      gamma * inverseEntryMoment W (prependInverseEntry indices a b) -
        (1 / 2 : ℝ) * ∑ r : Fin q,
          (inverseEntryMoment W (inverseSwapLeft indices a b r) +
            inverseEntryMoment W (inverseSwapRight indices a b r)) =
        sigma.1⁻¹ a b * inverseEntryMoment W indices) :
    InverseEntryRecurrenceThrough n gamma (fun a b ↦ (sigma.1⁻¹ a b : ℂ))
      (inverseEntryMomentTensor W) := by
  intro q hq x
  have h := congrArg Complex.ofReal (hentry q hq (Fin.tail x) (x 0).1 (x 0).2)
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_sum, Complex.ofReal_add,
    prependInverseEntry_tail] at h
  simpa only [inverseEntrySteinOperator, twoSwitchOperator,
    inverseEntryMomentTensor_eq_ofReal_entryMoment, inversePairSwitchLeft_eq_tuple,
    inversePairSwitchRight_eq_tuple] using h

/-- The rational moment continuation supplies the actual real-shape tensor
recurrence once the displayed Gaussian sample recurrences have been proved. -/
theorem inverseEntryMomentTensor_recurrenceThrough_of_natSamples
    {d n : ℕ} {beta gamma : ℝ} {sigma : SymPosDef d} (W : W_d d beta sigma)
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (n : ℝ) - 1 < gamma)
    (bound : ℕ → ℕ)
    (hsample : ∀ q : ℕ, q < n → ∀ k : ℕ, bound q ≤ k →
      ∀ V : W_d d ((k : ℝ) / 2) sigma,
      ∀ (indices : Fin q → Fin d × Fin d) (a b : Fin d),
      (((k : ℝ) / 2) - ((d : ℝ) + 1) / 2) *
          inverseEntryMoment V (prependInverseEntry indices a b) -
        (1 / 2 : ℝ) * ∑ r : Fin q,
          (inverseEntryMoment V (inverseSwapLeft indices a b r) +
            inverseEntryMoment V (inverseSwapRight indices a b r)) -
        sigma.1⁻¹ a b * inverseEntryMoment V indices = 0) :
    InverseEntryRecurrenceThrough n gamma (fun a b ↦ (sigma.1⁻¹ a b : ℂ))
      (inverseEntryMomentTensor W) := by
  apply inverseEntryMomentTensor_recurrenceThrough W n gamma
  intro q hq indices a b
  have hqgap : (q : ℝ) < gamma := by
    have hle : (q : ℝ) + 1 ≤ n := by exact_mod_cast hq
    linarith
  exact W.inverse_entry_recurrence_of_nat (bound q) (hsample q hq)
    hgamma hqgap indices a b

/-- The complete finite family uniqueness theorem identifies the actual
inverse tensor with the literal modified Gram inverse candidate. Both
recurrences remain displayed inputs until their independent proofs are used. -/
theorem inverseEntryMomentTensor_eq_of_recurrences {d n : ℕ} {beta gamma : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma) (hgap : (n : ℝ) - 1 < gamma)
    (hactual : InverseEntryRecurrenceThrough n gamma (fun a b ↦ (sigma.1⁻¹ a b : ℂ))
      (inverseEntryMomentTensor W))
    (hcandidate : InverseEntryRecurrenceThrough n gamma (fun a b ↦ (sigma.1⁻¹ a b : ℂ))
      (inverseWeingartenEntryTensor gamma (fun a b ↦ (sigma.1⁻¹ a b : ℂ)))) :
    inverseEntryMomentTensor W n =
      inverseWeingartenEntryTensor gamma (fun a b ↦ (sigma.1⁻¹ a b : ℂ)) n := by
  apply inverse_entry_tensor_family_unique n gamma hgap
    (fun a b ↦ (sigma.1⁻¹ a b : ℂ)) _ _ _ hactual hcandidate n le_rfl
  funext x
  rw [inverseEntryMomentTensor_zero, inverseWeingartenEntryTensor_zero]

/-- Exact original inverse `T_g` assembly from the actual and candidate
degree-lowering recurrences. No additional analytic or coefficient premise
is hidden in this adapter. -/
theorem inverse_matching_moment_of_recurrences {d n : ℕ} {beta gamma : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma)
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (n : ℝ) - 1 < gamma)
    (hactual : InverseEntryRecurrenceThrough n gamma (fun a b ↦ (sigma.1⁻¹ a b : ℂ))
      (inverseEntryMomentTensor W))
    (hcandidate : InverseEntryRecurrenceThrough n gamma (fun a b ↦ (sigma.1⁻¹ a b : ℂ))
      (inverseWeingartenEntryTensor gamma (fun a b ↦ (sigma.1⁻¹ a b : ℂ))))
    (m : Fin n → ComplexMatrix d) (g : Equiv.Perm (Fin (2 * n))) :
    expectation W (fun w ↦ T g (SymPosDef.inverse w).1 m) =
      ∑ N : PerfectMatching n, wgTilde (g⁻¹ * N.toPerm) gamma *
        T N.toPerm (SymPosDef.inverse sigma).1 m := by
  apply W.inverse_matching_moment_of_pairFormula hgamma hgap
  exact inverse_pairFormula_of_standard_tensor W
    (inverseEntryMomentTensor_eq_of_recurrences W hgap hactual hcandidate)

end A4Research

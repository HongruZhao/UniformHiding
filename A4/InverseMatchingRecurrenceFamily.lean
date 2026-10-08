import A4.InverseMatchingRecurrenceUniqueness

open scoped BigOperators

noncomputable section
namespace A4Research

/-- A complete tensor family satisfying the stated degree-lowering equation
through a fixed degree. The field is an explicit recurrence to be proved. -/
def InverseEntryRecurrenceThrough {d : ℕ} (n : ℕ) (gamma : ℝ)
    (A : Fin d → Fin d → ℂ)
    (F : ∀ k : ℕ, EntryPairList d k → ℂ) : Prop :=
  ∀ q : ℕ, q < n → ∀ x : EntryPairList d (q + 1),
    inverseEntrySteinOperator gamma (F (q + 1)) x =
      A (x 0).1 (x 0).2 * F q (Fin.tail x)

/-- Agreement in degree zero and independently proved recurrences determine
the complete tensor family through `n`, under the original moment margin. -/
theorem inverse_entry_tensor_family_unique {d : ℕ} (n : ℕ)
    (gamma : ℝ) (hgap : (n : ℝ) - 1 < gamma)
    (A : Fin d → Fin d → ℂ)
    (F G : ∀ k : ℕ, EntryPairList d k → ℂ)
    (hzero : F 0 = G 0)
    (hF : InverseEntryRecurrenceThrough n gamma A F)
    (hG : InverseEntryRecurrenceThrough n gamma A G) :
    ∀ k : ℕ, k ≤ n → F k = G k := by
  intro k hk
  induction k with
  | zero => exact hzero
  | succ q ih =>
    have hqn : q < n := by omega
    have hqgap : (q : ℝ) < gamma := by
      have hle : (q : ℝ) + 1 ≤ n := by exact_mod_cast hk
      linarith
    apply inverseEntrySteinOperator_injective gamma hqgap
    apply funext
    intro x
    rw [hF q hqn x, hG q hqn x, ih (by omega)]

end A4Research

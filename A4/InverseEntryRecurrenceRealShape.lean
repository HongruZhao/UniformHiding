import A4.InverseShapeMoments
import A4.InverseSteinRecursionTuples

open MeasureTheory Matrix
open scoped BigOperators

noncomputable section
namespace MatsumotoPaper

open A4Research.InverseStein

def inverseEntryMoment {d q : ℕ} {beta : ℝ} {sigma : SymPosDef d}
    (W : W_d d beta sigma) (indices : Fin q → Fin d × Fin d) : ℝ :=
  ∫ w : SymPosDef d, ∏ r : Fin q, w.1⁻¹ (indices r).1 (indices r).2 ∂W.toMeasure

abbrev InverseRecurrenceTerm (q : ℕ) := Option (Fin q ⊕ Fin q) ⊕ Unit

def inverseRecurrenceDegree {q : ℕ} : InverseRecurrenceTerm q → ℕ
  | .inl _ => q + 1
  | .inr _ => q

def inverseRecurrenceEntries {d q : ℕ} (indices : Fin q → Fin d × Fin d)
    (a b : Fin d) : (t : InverseRecurrenceTerm q) →
      Fin (inverseRecurrenceDegree t) → Fin d × Fin d
  | .inl none => prependInverseEntry indices a b
  | .inl (some (.inl r)) => inverseSwapLeft indices a b r
  | .inl (some (.inr r)) => inverseSwapRight indices a b r
  | .inr _ => indices

def inverseRecurrenceCoefficient {d q : ℕ} (sigma : RealMatrix d) (a b : Fin d) :
    InverseRecurrenceTerm q → Polynomial ℝ
  | .inl none => Polynomial.X - Polynomial.C (((d : ℝ) + 1) / 2)
  | .inl (some _) => Polynomial.C (-(1 / 2 : ℝ))
  | .inr _ => Polynomial.C (-sigma⁻¹ a b)

theorem inverseRecurrenceDegree_le {q : ℕ} (t : InverseRecurrenceTerm q) :
    inverseRecurrenceDegree t ≤ q + 1 := by
  cases t <;> simp [inverseRecurrenceDegree]

set_option backward.isDefEq.respectTransparency false in
theorem inverseRecurrenceSum_eq {d q : ℕ} {beta : ℝ} {sigma : SymPosDef d}
    (W : W_d d beta sigma) (indices : Fin q → Fin d × Fin d) (a b : Fin d) :
    (∑ t : InverseRecurrenceTerm q,
      (inverseRecurrenceCoefficient sigma.1 a b t).eval beta *
        (∫ w : SymPosDef d, ∏ r : Fin (inverseRecurrenceDegree t),
          w.1⁻¹ (inverseRecurrenceEntries indices a b t r).1
            (inverseRecurrenceEntries indices a b t r).2 ∂W.toMeasure)) =
      (beta - ((d : ℝ) + 1) / 2) * inverseEntryMoment W (prependInverseEntry indices a b) -
        (1 / 2 : ℝ) * ∑ r : Fin q,
          (inverseEntryMoment W (inverseSwapLeft indices a b r) +
            inverseEntryMoment W (inverseSwapRight indices a b r)) -
        sigma.1⁻¹ a b * inverseEntryMoment W indices := by
  classical
  simp only [Fintype.sum_sum_type, Fintype.sum_option, inverseRecurrenceCoefficient,
    inverseRecurrenceEntries, inverseRecurrenceDegree, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Fintype.sum_unique, inverseEntryMoment,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- Rational continuation of the literal all-degree Stein--Haff entry
recurrence. The sufficient Gaussian sampling margin does not change the
sharp real-shape gap in the conclusion. -/
theorem W_d.inverse_entry_recurrence_of_nat
    {d q : ℕ} {sigma : SymPosDef d} (bound : ℕ)
    (hsample : ∀ k : ℕ, bound ≤ k → ∀ V : W_d d ((k : ℝ) / 2) sigma,
      ∀ (indices : Fin q → Fin d × Fin d) (a b : Fin d),
      (((k : ℝ) / 2) - ((d : ℝ) + 1) / 2) *
          inverseEntryMoment V (prependInverseEntry indices a b) -
        (1 / 2 : ℝ) * ∑ r : Fin q,
          (inverseEntryMoment V (inverseSwapLeft indices a b r) +
            inverseEntryMoment V (inverseSwapRight indices a b r)) -
        sigma.1⁻¹ a b * inverseEntryMoment V indices = 0)
    {beta gamma : ℝ} (W : W_d d beta sigma)
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (q : ℝ) < gamma)
    (indices : Fin q → Fin d × Fin d) (a b : Fin d) :
    gamma * inverseEntryMoment W (prependInverseEntry indices a b) -
        (1 / 2 : ℝ) * ∑ r : Fin q,
          (inverseEntryMoment W (inverseSwapLeft indices a b r) +
            inverseEntryMoment W (inverseSwapRight indices a b r)) =
      sigma.1⁻¹ a b * inverseEntryMoment W indices := by
  have hgap' : ((q + 1 : ℕ) : ℝ) - 1 < gamma := by
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hgap
  have h := W.inverseMomentLinearIdentity_of_nat
    (n := q + 1) (I := InverseRecurrenceTerm q) inverseRecurrenceDegree
    (fun t r ↦ (inverseRecurrenceEntries indices a b t r).1)
    (fun t r ↦ (inverseRecurrenceEntries indices a b t r).2)
    (inverseRecurrenceCoefficient sigma.1 a b) 0
    inverseRecurrenceDegree_le bound
    (fun k hk V ↦ by
      rw [Polynomial.eval_zero]
      exact (inverseRecurrenceSum_eq V indices a b).trans (hsample k hk V indices a b))
    hgamma hgap'
  rw [inverseRecurrenceSum_eq W indices a b, Polynomial.eval_zero, ← hgamma] at h
  exact sub_eq_zero.mp h

end MatsumotoPaper

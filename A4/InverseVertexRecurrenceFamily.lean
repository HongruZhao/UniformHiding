import A4.InverseMatchingRecurrenceUniqueness
import A4.MatchingGramDegreeFactorizationSlots

open scoped BigOperators

noncomputable section
namespace A4Research

open MatsumotoPaper

abbrev VertexArray (d n : ℕ) := Fin (2 * n) → Fin d

def inverseVertexSwitchLeft {d q : ℕ} (r : Fin q)
    (j : VertexArray d (q + 1)) : VertexArray d (q + 1) :=
  j ∘ firstPairSwitch q (leftSlot r)

def inverseVertexSwitchRight {d q : ℕ} (r : Fin q)
    (j : VertexArray d (q + 1)) : VertexArray d (q + 1) :=
  j ∘ firstPairSwitch q (rightSlot r)

def inverseVertexSteinOperator {d q : ℕ} (gamma : ℝ)
    (F : VertexArray d (q + 1) → ℂ) : VertexArray d (q + 1) → ℂ :=
  twoSwitchOperator q gamma inverseVertexSwitchLeft inverseVertexSwitchRight F

def InverseVertexRecurrenceThrough {d : ℕ} (n : ℕ) (gamma : ℝ)
    (A : Fin d → Fin d → ℂ)
    (F : ∀ k : ℕ, VertexArray d k → ℂ) : Prop :=
  ∀ q : ℕ, q < n → ∀ j : VertexArray d (q + 1),
    inverseVertexSteinOperator gamma (F (q + 1)) j =
      A (j (firstVertex q)) (j (secondVertex q)) *
        F q (fun t ↦ j (remainingVertex q t))

/-- The vertex form retains exactly two switches for each old pair. -/
theorem inverseVertexSteinOperator_injective {d q : ℕ}
    (gamma : ℝ) (hgap : (q : ℝ) < gamma) :
    Function.Injective (inverseVertexSteinOperator (d := d) (q := q) gamma) :=
  twoSwitchOperator_injective q gamma hgap _ _

/-- Recurrence and degree zero determine every entry of the complete
vertex tensor. No invariance or matching-basis assumption is used. -/
theorem inverse_vertex_tensor_family_unique {d : ℕ} (n : ℕ)
    (gamma : ℝ) (hgap : (n : ℝ) - 1 < gamma)
    (A : Fin d → Fin d → ℂ)
    (F G : ∀ k : ℕ, VertexArray d k → ℂ)
    (hzero : F 0 = G 0)
    (hF : InverseVertexRecurrenceThrough n gamma A F)
    (hG : InverseVertexRecurrenceThrough n gamma A G) :
    ∀ k : ℕ, k ≤ n → F k = G k := by
  intro k hk
  induction k with
  | zero => exact hzero
  | succ q ih =>
    have hqn : q < n := by omega
    have hqgap : (q : ℝ) < gamma := by
      have hle : (q : ℝ) + 1 ≤ n := by exact_mod_cast hk
      linarith
    apply inverseVertexSteinOperator_injective gamma hqgap
    funext j
    rw [hF q hqn j, hG q hqn j, ih (by omega)]

end A4Research

import A4.Target
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Uniqueness of the complete inverse-entry recurrence

The Stein--Haff recurrence contains exactly two crossed pair products for
each old pair.  On its finite index space, the maximum norm therefore gives
uniqueness whenever `gamma` exceeds the number of old pairs.  This retains
the precise all-degree threshold `gamma > n - 1`.
-/

open scoped BigOperators

noncomputable section
namespace A4Research

set_option maxHeartbeats 400000

/-- The finite linear operator with two switches for each old pair. -/
def twoSwitchOperator {I : Type*} (q : ℕ) (gamma : ℝ)
    (left right : Fin q → I → I) (F : I → ℂ) (x : I) : ℂ :=
  (gamma : ℂ) * F x - (1 / 2 : ℂ) *
    ∑ r : Fin q, (F (left r x) + F (right r x))

/-- The exact two-switch operator is injective above the old-pair count.
No symmetry or invariant-tensor assumption is required. -/
theorem twoSwitchOperator_injective {I : Type*} [Fintype I]
    (q : ℕ) (gamma : ℝ) (hgap : (q : ℝ) < gamma)
    (left right : Fin q → I → I) :
    Function.Injective (twoSwitchOperator q gamma left right) := by
  classical
  intro F G hFG
  let H : I → ℂ := fun x ↦ F x - G x
  have hzero (x : I) :
      (gamma : ℂ) * H x = (1 / 2 : ℂ) *
        ∑ r : Fin q, (H (left r x) + H (right r x)) := by
    have hx := congrFun hFG x
    simp only [twoSwitchOperator] at hx
    dsimp only [H]
    rw [show (∑ r : Fin q,
        (F (left r x) - G (left r x) +
          (F (right r x) - G (right r x)))) =
        (∑ r : Fin q, (F (left r x) + F (right r x))) -
          ∑ r : Fin q, (G (left r x) + G (right r x)) by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r _
      ring]
    linear_combination hx
  apply funext
  intro x
  by_contra hx
  have hHx : H x ≠ 0 := sub_ne_zero.mpr hx
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ
    (fun y : I ↦ ‖H y‖) ⟨x, Finset.mem_univ x⟩
  have hnorm : ∀ y : I, ‖H y‖ ≤ ‖H m‖ := fun y ↦ hm y (Finset.mem_univ y)
  have hpositive : 0 < ‖H m‖ := (norm_pos_iff.mpr hHx).trans_le (hnorm x)
  have hgamma : 0 < gamma := (Nat.cast_nonneg q).trans_lt hgap
  have hbound : gamma * ‖H m‖ ≤ (q : ℝ) * ‖H m‖ := by
    calc
      gamma * ‖H m‖ = ‖(gamma : ℂ) * H m‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hgamma]
      _ = ‖(1 / 2 : ℂ) * ∑ r : Fin q,
          (H (left r m) + H (right r m))‖ := by rw [hzero]
      _ = (1 / 2 : ℝ) * ‖∑ r : Fin q,
          (H (left r m) + H (right r m))‖ := by norm_num [norm_mul]
      _ ≤ (1 / 2 : ℝ) *
          ∑ r : Fin q, ‖H (left r m) + H (right r m)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)
      _ ≤ (1 / 2 : ℝ) * ∑ _r : Fin q, (‖H m‖ + ‖H m‖) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro r _
        exact (norm_add_le _ _).trans (add_le_add (hnorm _) (hnorm _))
      _ = (q : ℝ) * ‖H m‖ := by simp; ring
  exact (not_le_of_gt (mul_lt_mul_of_pos_right hgap hpositive)) hbound

/-- A list of ordered matrix-entry pairs indexing a degree `n` tensor. -/
abbrev EntryPairList (d n : ℕ) := Fin n → Fin d × Fin d

/-- The first of the two crossed pair products in Stein--Haff. -/
def inversePairSwitchLeft {d q : ℕ} (r : Fin q) (x : EntryPairList d (q + 1)) :
    EntryPairList d (q + 1) :=
  Fin.cons ((x r.succ).1, (x 0).1)
    (Function.update (Fin.tail x) r ((x 0).2, (x r.succ).2))

/-- The second crossed pair product in Stein--Haff. -/
def inversePairSwitchRight {d q : ℕ} (r : Fin q) (x : EntryPairList d (q + 1)) :
    EntryPairList d (q + 1) :=
  Fin.cons ((x r.succ).1, (x 0).2)
    (Function.update (Fin.tail x) r ((x 0).1, (x r.succ).2))

/-- The literal full inverse-entry Stein--Haff operator. -/
def inverseEntrySteinOperator {d q : ℕ} (gamma : ℝ)
    (F : EntryPairList d (q + 1) → ℂ) : EntryPairList d (q + 1) → ℂ :=
  twoSwitchOperator q gamma inversePairSwitchLeft inversePairSwitchRight F

theorem inverseEntrySteinOperator_injective {d q : ℕ}
    (gamma : ℝ) (hgap : (q : ℝ) < gamma) :
    Function.Injective (inverseEntrySteinOperator (d := d) (q := q) gamma) :=
  twoSwitchOperator_injective q gamma hgap _ _

/-- Equal degree-lowering recurrences identify every entry of the full
inverse tensor, with no additional matching-system premise. -/
theorem inverse_entry_tensor_eq_of_recurrence {d q : ℕ}
    (gamma : ℝ) (hgap : (q : ℝ) < gamma)
    (F G : EntryPairList d (q + 1) → ℂ)
    (hrec : ∀ x,
      (gamma : ℂ) * F x - (1 / 2 : ℂ) *
          ∑ r : Fin q, (F (inversePairSwitchLeft r x) + F (inversePairSwitchRight r x)) =
        (gamma : ℂ) * G x - (1 / 2 : ℂ) *
          ∑ r : Fin q, (G (inversePairSwitchLeft r x) + G (inversePairSwitchRight r x))) :
    F = G := by
  apply inverseEntrySteinOperator_injective gamma hgap
  exact funext hrec

end A4Research

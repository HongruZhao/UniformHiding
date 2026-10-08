import A4.Target
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

open scoped BigOperators
noncomputable section
namespace A4Research.InverseStein

def prependInverseEntry {d q : ℕ} (indices : Fin q → Fin d × Fin d)
    (a b : Fin d) : Fin (q + 1) → Fin d × Fin d :=
  Fin.cons (a, b) indices

def inverseSwapLeft {d q : ℕ} (indices : Fin q → Fin d × Fin d)
    (a b : Fin d) (r : Fin q) : Fin (q + 1) → Fin d × Fin d :=
  Fin.cons ((indices r).1, a) (Function.update indices r (b, (indices r).2))

def inverseSwapRight {d q : ℕ} (indices : Fin q → Fin d × Fin d)
    (a b : Fin d) (r : Fin q) : Fin (q + 1) → Fin d × Fin d :=
  Fin.cons ((indices r).1, b) (Function.update indices r (a, (indices r).2))

theorem product_updated_pairs {d q : ℕ} (indices : Fin q → Fin d × Fin d)
    (X : MatsumotoPaper.RealMatrix d) (a b : Fin d) (r : Fin q) :
    (∏ s : Fin q, X (Function.update indices r (a, b) s).1
      (Function.update indices r (a, b) s).2) =
      X a b * ∏ s ∈ Finset.univ.erase r, X (indices s).1 (indices s).2 := by
  have hfun : (fun s : Fin q ↦ X (Function.update indices r (a, b) s).1
      (Function.update indices r (a, b) s).2) =
      Function.update (fun s ↦ X (indices s).1 (indices s).2) r (X a b) := by
    funext s
    by_cases h : s = r
    · subst s
      simp
    · simp [Function.update_of_ne h, h]
  rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ r)]
  simp only [Finset.sdiff_singleton_eq_erase]

theorem product_prependInverseEntry {d q : ℕ}
    (indices : Fin q → Fin d × Fin d) (X : MatsumotoPaper.RealMatrix d)
    (a b : Fin d) :
    (∏ s : Fin (q + 1), X (prependInverseEntry indices a b s).1
      (prependInverseEntry indices a b s).2) =
      X a b * ∏ s : Fin q, X (indices s).1 (indices s).2 := by
  simp [prependInverseEntry, Fin.prod_univ_succ]

theorem product_inverseSwapLeft {d q : ℕ}
    (indices : Fin q → Fin d × Fin d) (X : MatsumotoPaper.RealMatrix d)
    (a b : Fin d) (r : Fin q) :
    (∏ s : Fin (q + 1), X (inverseSwapLeft indices a b r s).1
      (inverseSwapLeft indices a b r s).2) =
      (X (indices r).1 a * X b (indices r).2) *
        ∏ s ∈ Finset.univ.erase r, X (indices s).1 (indices s).2 := by
  simp only [inverseSwapLeft, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [product_updated_pairs]
  ring

theorem product_inverseSwapRight {d q : ℕ}
    (indices : Fin q → Fin d × Fin d) (X : MatsumotoPaper.RealMatrix d)
    (a b : Fin d) (r : Fin q) :
    (∏ s : Fin (q + 1), X (inverseSwapRight indices a b r s).1
      (inverseSwapRight indices a b r s).2) =
      (X (indices r).1 b * X a (indices r).2) *
        ∏ s ∈ Finset.univ.erase r, X (indices s).1 (indices s).2 := by
  simp only [inverseSwapRight, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [product_updated_pairs]
  ring

end A4Research.InverseStein

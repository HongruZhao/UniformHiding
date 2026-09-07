import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19HaarCornerJointLaw
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19HaarCornerDensityInduction
import LogdetLean.GramHafnian.UltimateHiding.Dense.H1_RowGramOrbit
import Mathlib.Tactic

/-!
# Row-Gram identification for the H19 successor column

The unobserved suffix block of a Haar unitary has row Gram equal to the
left defect of the observed corner.  This is the deterministic bridge from
the exact suffix-rotation coupling to the canonical positive square root.
-/

open Matrix MeasureTheory
open scoped BigOperators

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

/-- Splitting the ambient columns of a unitary after `L` columns identifies
the row Gram of the remaining top block with `I-AA*`. -/
theorem h19HaarTopSuffix_mul_conjTranspose
    {M K L : ℕ} (hKM : K ≤ M) (hLM : L ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ) :
    h19HaarTopSuffix hKM hLM U *
        (h19HaarTopSuffix hKM hLM U).conjTranspose =
      haarCornerLeftDefect (h19HaarTallPast hKM hLM U) := by
  ext i j
  let e := haarAmbientPrefixEquiv hLM
  have hunit := Unitary.coe_mul_star_self U
  have hij := congrArg
    (fun B : Matrix (Fin M) (Fin M) ℂ ↦
      B (Fin.castLE hKM i) (Fin.castLE hKM j)) hunit
  have hfull :
      (∑ k : Fin M,
        (U : Matrix (Fin M) (Fin M) ℂ) (Fin.castLE hKM i) k *
          star ((U : Matrix (Fin M) (Fin M) ℂ)
            (Fin.castLE hKM j) k)) =
        (1 : Matrix (Fin M) (Fin M) ℂ)
          (Fin.castLE hKM i) (Fin.castLE hKM j) := by
    simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply] using hij
  rw [← Fintype.sum_equiv e
    (fun a : Fin L ⊕ Fin (M - L) ↦
      (U : Matrix (Fin M) (Fin M) ℂ) (Fin.castLE hKM i) (e a) *
        star ((U : Matrix (Fin M) (Fin M) ℂ)
          (Fin.castLE hKM j) (e a)))
    (fun k : Fin M ↦
      (U : Matrix (Fin M) (Fin M) ℂ) (Fin.castLE hKM i) k *
        star ((U : Matrix (Fin M) (Fin M) ℂ)
          (Fin.castLE hKM j) k))
    (fun _ ↦ rfl), Fintype.sum_sum_type] at hfull
  change
    (∑ q : Fin (M - L),
      (U : Matrix (Fin M) (Fin M) ℂ) (Fin.castLE hKM i)
          (e (Sum.inr q)) *
        star ((U : Matrix (Fin M) (Fin M) ℂ) (Fin.castLE hKM j)
          (e (Sum.inr q)))) = _
  change
    (∑ q : Fin (M - L),
      (U : Matrix (Fin M) (Fin M) ℂ) (Fin.castLE hKM i)
          (e (Sum.inr q)) *
        star ((U : Matrix (Fin M) (Fin M) ℂ) (Fin.castLE hKM j)
          (e (Sum.inr q)))) =
      (1 : Matrix (Fin K) (Fin K) ℂ) i j -
        ∑ q : Fin L,
          (U : Matrix (Fin M) (Fin M) ℂ) (Fin.castLE hKM i)
              (Fin.castLE hLM q) *
            star ((U : Matrix (Fin M) (Fin M) ℂ) (Fin.castLE hKM j)
              (Fin.castLE hLM q))
  have hdiag :
      (1 : Matrix (Fin M) (Fin M) ℂ)
          (Fin.castLE hKM i) (Fin.castLE hKM j) =
        (1 : Matrix (Fin K) (Fin K) ℂ) i j := by
    simp only [Matrix.one_apply, Fin.castLE_inj]
  simp only [e, haarAmbientPrefixEquiv_inl] at hfull
  rw [hdiag] at hfull
  linear_combination hfull

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse

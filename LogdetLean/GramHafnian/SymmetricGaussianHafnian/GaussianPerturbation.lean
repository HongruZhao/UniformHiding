import LogdetLean.GramHafnian.SymmetricGaussianHafnian.StarCentering

/-!
# Arbitrary independent perturbations of the literal complex Gaussian hafnian

Complete vertex stars may overlap. Only deterministic means are zeroed at
each step; every comparison uses the same product law of independent edge
Gaussians. No independence between stars is asserted or needed.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

/-- Zero every edge mean meeting the visited vertex set. -/
def zeroVertices {ι : Type*} [DecidableEq ι]
    (vs : Finset ι) (a : Edge ι → ℂ) : Edge ι → ℂ :=
  fun e => if Disjoint vs e.val then a e else 0

@[simp] theorem zeroVertices_empty {ι : Type*} [DecidableEq ι]
    (a : Edge ι → ℂ) : zeroVertices ∅ a = a := by
  funext e
  simp [zeroVertices]

theorem zeroVertices_insert {ι : Type*} [DecidableEq ι]
    (v : ι) (vs : Finset ι) (a : Edge ι → ℂ) :
    zeroVertices (insert v vs) a = zeroStar v (zeroVertices vs a) := by
  funext e
  by_cases hv : v ∈ e.val <;> by_cases hd : Disjoint vs e.val <;>
    simp [zeroVertices, zeroStar, Finset.disjoint_insert_left, hv, hd]

@[simp] theorem zeroVertices_univ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Edge ι → ℂ) : zeroVertices Finset.univ a = 0 := by
  funext e
  have he : e.val.Nonempty := Finset.card_pos.mp (by rw [e.property]; norm_num)
  obtain ⟨v, hv⟩ := he
  have hd : ¬ Disjoint (Finset.univ : Finset ι) e.val := by
    intro h
    exact Finset.disjoint_left.mp h (Finset.mem_univ v) hv
  simp [zeroVertices, hd]

/-- Center any finite set of stars in the actual complex Gaussian edge law. -/
theorem edgeHafnian_laplace_le_zeroVertices {m : ℕ}
    (vs : Finset (Fin m)) (a : Edge (Fin m) → ℂ)
    (s : ℝ) (hs : 0 ≤ s) :
    (∫ x, Real.exp (-s * ‖edgeHafnian (x + a)‖ ^ 2) ∂edgeGaussian (Fin m)) ≤
      ∫ x, Real.exp (-s * ‖edgeHafnian (x + zeroVertices vs a)‖ ^ 2)
        ∂edgeGaussian (Fin m) := by
  classical
  induction vs using Finset.induction_on with
  | empty => simp
  | @insert v vs hv ih =>
      calc
        _ ≤ ∫ x, Real.exp (-s * ‖edgeHafnian (x + zeroVertices vs a)‖ ^ 2)
            ∂edgeGaussian (Fin m) := ih
        _ ≤ ∫ x, Real.exp
            (-s * ‖edgeHafnian (x + zeroStar v (zeroVertices vs a))‖ ^ 2)
            ∂edgeGaussian (Fin m) := by
          simpa using edgeHafnian_laplace_le_zeroStar v (zeroVertices vs a) 0 s hs
        _ = _ := by rw [zeroVertices_insert]

/-- The exact centered-model Laplace comparison for every deterministic
edge shift and scalar center. A nonempty vertex type excludes the constant
empty hafnian; odd sizes are harmless and need not be excluded. -/
theorem deterministicShift_edgeHafnian_laplace_le
    (m : ℕ) (hm : 0 < m) (a : Edge (Fin m) → ℂ)
    (w : ℂ) (s : ℝ) (hs : 0 ≤ s) :
    (∫ x, Real.exp (-s * ‖edgeHafnian (x + a) - w‖ ^ 2)
        ∂edgeGaussian (Fin m)) ≤
      ∫ x, Real.exp (-s * ‖edgeHafnian x‖ ^ 2) ∂edgeGaussian (Fin m) := by
  let v : Fin m := ⟨0, hm⟩
  calc
    _ ≤ ∫ x, Real.exp (-s * ‖edgeHafnian (x + zeroStar v a)‖ ^ 2)
        ∂edgeGaussian (Fin m) :=
      edgeHafnian_laplace_le_zeroStar v a w s hs
    _ ≤ ∫ x, Real.exp
        (-s * ‖edgeHafnian (x + zeroVertices Finset.univ (zeroStar v a))‖ ^ 2)
        ∂edgeGaussian (Fin m) :=
      edgeHafnian_laplace_le_zeroVertices Finset.univ (zeroStar v a) s hs
    _ = _ := by simp

/-- Arbitrary probability law for the edge perturbation, independent of
the complete Gaussian edge array. Its coordinates may be dependent and
no moment or boundedness assumption is imposed. -/
theorem independentShift_edgeHafnian_laplace_le
    (m : ℕ) (hm : 0 < m)
    (ν : Measure (Edge (Fin m) → ℂ)) [IsProbabilityMeasure ν]
    (w : ℂ) (s : ℝ) (hs : 0 ≤ s) :
    (∫ p : (Edge (Fin m) → ℂ) × (Edge (Fin m) → ℂ),
      Real.exp (-s * ‖edgeHafnian (p.1 + p.2) - w‖ ^ 2)
        ∂((edgeGaussian (Fin m)).prod ν)) ≤
      ∫ x, Real.exp (-s * ‖edgeHafnian x‖ ^ 2) ∂edgeGaussian (Fin m) := by
  let f : (Edge (Fin m) → ℂ) × (Edge (Fin m) → ℂ) → ℝ :=
    fun p => Real.exp (-s * ‖edgeHafnian (p.1 + p.2) - w‖ ^ 2)
  have hf : Integrable f ((edgeGaussian (Fin m)).prod ν) := by
    apply Integrable.of_bound (by dsimp [f]; fun_prop) 1
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (sq_nonneg _))
  calc
    _ = ∫ a, ∫ x, f (x, a) ∂edgeGaussian (Fin m) ∂ν :=
      integral_prod_symm f hf
    _ ≤ ∫ _a, (∫ x, Real.exp (-s * ‖edgeHafnian x‖ ^ 2)
        ∂edgeGaussian (Fin m)) ∂ν := by
      apply integral_mono hf.integral_prod_right (integrable_const _)
      intro a
      exact deterministicShift_edgeHafnian_laplace_le m hm a w s hs
    _ = _ := by simp

/-- Paper-indexed complex perturbation endpoint at degree n. -/
theorem symmetricHafnian_independentShift_laplace_le
    (n : ℕ) (hn : 1 ≤ n)
    (ν : Measure (Edge (Fin (2 * n)) → ℂ)) [IsProbabilityMeasure ν]
    (w : ℂ) (s : ℝ) (hs : 0 ≤ s) :
    (∫ p : (Edge (Fin (2 * n)) → ℂ) × (Edge (Fin (2 * n)) → ℂ),
      Real.exp (-s * ‖edgeHafnian (p.1 + p.2) - w‖ ^ 2)
        ∂((edgeGaussian (Fin (2 * n))).prod ν)) ≤
      ∫ x, Real.exp (-s * ‖edgeHafnian x‖ ^ 2) ∂edgeGaussian (Fin (2 * n)) :=
  independentShift_edgeHafnian_laplace_le (2 * n) (by omega) ν w s hs

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian

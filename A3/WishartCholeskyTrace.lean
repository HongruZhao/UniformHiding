import A3.WishartCholeskyBlock
import A3.WishartBartlettSplitMeasure
import A3.WishartAmbientKernel

open Matrix
open scoped BigOperators

noncomputable section
namespace A3Research

set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {K : Type*} [RCLike K]

theorem wishartTraceReal_eq_sum (x : HermitianCoordinates n K) :
    wishartTraceReal x = ∑ i, x.1 i := by
  simp [wishartTraceReal, Matrix.trace]

theorem wishartUpperNormSum_cons (p : ℝ) (z : Fin n → K)
    (y : HermitianCoordinates n K) :
    (∑ ij : HermitianCoordinateIndex (n + 1),
      RCLike.normSq ((wishartCoordinatesCons p z y).2 ij)) =
      (∑ j : Fin n, RCLike.normSq (z j)) +
        ∑ ij : HermitianCoordinateIndex n, RCLike.normSq (y.2 ij) := by
  rw [← (wishartUpperIndexHeadTailEquiv n).sum_comp
    (fun ij ↦ RCLike.normSq ((wishartCoordinatesCons p z y).2 ij)), Fintype.sum_sum_type]
  simp [wishartUpperIndexHeadTailEquiv]

theorem wishartTraceReal_gram_cons (p : ℝ) (z : Fin n → K)
    (y : HermitianCoordinates n K) (hp : 0 ≤ p) :
    wishartTraceReal (wishartGramCoordinates (wishartCoordinatesCons p z y)) =
      p + wishartTraceReal (wishartGramCoordinates y) + ∑ j, RCLike.normSq (z j) := by
  rw [wishartTraceReal_eq_sum, Fin.sum_univ_succ]
  have h0 : (wishartGramCoordinates (wishartCoordinatesCons p z y)).1 0 = p := by
    dsimp [wishartGramCoordinates, hermitianCoordinateProjection]
    rw [wishartGramMatrix_cons_zero_zero p z y hp, RCLike.ofReal_re]
  have hs (i : Fin n) : (wishartGramCoordinates (wishartCoordinatesCons p z y)).1 i.succ =
      RCLike.normSq (z i) + (wishartGramCoordinates y).1 i := by
    dsimp [wishartGramCoordinates, hermitianCoordinateProjection]
    rw [wishartGramMatrix_cons_succ_succ, map_add]
    congr 1
    rw [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re,
      RCLike.normSq_eq_def']
  simp only [h0, hs, Finset.sum_add_distrib]
  rw [wishartTraceReal_eq_sum]
  ring

/-- The actual Gram trace is the sum of its squared pivots and squared Gaussian entries. -/
theorem wishartTraceReal_gram (x : HermitianCoordinates n K)
    (hx : x ∈ wishartCholeskyDomain n K) :
    wishartTraceReal (wishartGramCoordinates x) =
      (∑ i, x.1 i) + ∑ ij, RCLike.normSq (x.2 ij) := by
  induction n with
  | zero => simp [wishartTraceReal_eq_sum]
  | succ n ih =>
    let e := wishartCoordinatesSplitLinearEquiv n K
    obtain ⟨⟨p, z, y⟩, hxy⟩ := e.symm.surjective x
    subst x
    dsimp [e, wishartCoordinatesSplitLinearEquiv] at hx ⊢
    obtain ⟨hp, hy⟩ := (wishartCoordinatesCons_mem_domain p z y).mp hx
    rw [wishartTraceReal_gram_cons p z y hp.le, ih y hy, wishartUpperNormSum_cons,
      Fin.sum_univ_succ]
    simp only [wishartCoordinatesCons_diag_zero, wishartCoordinatesCons_diag_succ]
    ring

end A3Research

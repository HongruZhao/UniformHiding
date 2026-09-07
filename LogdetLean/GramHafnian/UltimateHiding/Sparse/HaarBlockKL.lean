import LogdetLean.GramHafnian.UltimateHiding.Sparse.HaarBlockLaw
import LogdetLean.GramHafnian.UltimateHiding.Sparse.RectangularIndices

/-!
# Concrete KL bridge for the finite Haar block comparison

The actual probability laws in this file are the normalized Haar corner
`sqrt M U_{N,K}` and the standard Gaussian block.  The deterministic grid
arising from the truncated unitary density is defined directly, and its sharp
finite upper bound is proved by the scalar calculation in
`RectangularIndices`.

The installed library does not contain a density theorem for a rectangular
corner of Haar unitary measure, nor the corresponding complex matrix beta
log determinant moment.  Consequently this file does not assert the missing
law identification.  Instead, the final two theorems record transparently
what follows once that equality has itself been proved: the block KL bound and
its transpose Gram data processing consequence.  There is no axiom, sorry,
or opaque analytic declaration here.

The precise paper input is T. Jiang, *Approximation of Haar Distributed
Matrices and Limiting Distributions of Eigenvalues of Jacobi Ensembles*,
Probability Theory and Related Fields **144** (2009), Proposition 2.1,
equation (2.4), and Lemma 2.8.  Proposition 2.1 gives the rectangular Haar
corner density and its factorial normalizer; Lemma 2.8 writes the scaled
likelihood ratio against the standard complex Gaussian law.  The required
log-determinant expectation is the derivative in the beta exponent of the
same normalizer, whose Selberg evaluation is Lemma 2.2 of that paper.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

open CurrentPRL

/-- The exact finite grid printed by the matrix beta likelihood calculation,
with `p = K` and `q = N`. -/
def haarBlockKLGrid (M N K : ℕ) : ℝ :=
  ∑ i : Fin N × Fin K,
    klSummand ((((K : ℝ) + N) / M))
      (rectangularNormalizedIndex K N M i)

/-- Kernel checked upper bound for the exact finite KL grid. -/
theorem haarBlockKLGrid_le
    {M N K : ℕ} (hN : 0 < N) (hK : 0 < K) (hs : K + N ≤ M) :
    haarBlockKLGrid M N K ≤
      (K : ℝ) * N * ((K : ℝ) + N) ^ 2 /
        (2 * (M : ℝ) ^ 2) := by
  exact rectangular_scalar_kl_bound (p := K) (q := N) hK hN hs

/-- The pointwise form obtained by combining the truncated unitary
normalizer, the matrix beta logarithmic moment, and the Gaussian trace term. -/
def haarBlockLikelihoodGridSummand (M N K : ℕ)
    (i : Fin N × Fin K) : ℝ :=
  let x := rectangularNormalizedIndex K N M i
  Real.log (1 - x) + 1 -
    (1 - (((K : ℝ) + N) / M)) / (1 - x)

/-- The likelihood form and the scalar `klSummand` form agree pointwise. -/
theorem haarBlockLikelihoodGridSummand_eq_klSummand
    {M N K : ℕ} (hN : 0 < N) (hK : 0 < K) (hs : K + N ≤ M)
    (i : Fin N × Fin K) :
    haarBlockLikelihoodGridSummand M N K i =
      klSummand ((((K : ℝ) + N) / M))
        (rectangularNormalizedIndex K N M i) := by
  let h : ℝ := (((K : ℝ) + N) / M)
  let x : ℝ := rectangularNormalizedIndex K N M i
  have hx : x < 1 := rectangular_index_lt_one hK hN hs i
  have hxne : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx)
  change Real.log (1 - x) + 1 - (1 - h) / (1 - x) =
    Real.log (1 - x) + (h - x) / (1 - x)
  field_simp
  ring

/-- Consequently, summing the likelihood pieces gives exactly the checked KL
grid.  This is the algebraic part of the matrix beta calculation. -/
theorem sum_haarBlockLikelihoodGridSummand_eq_haarBlockKLGrid
    {M N K : ℕ} (hN : 0 < N) (hK : 0 < K) (hs : K + N ≤ M) :
    ∑ i : Fin N × Fin K, haarBlockLikelihoodGridSummand M N K i =
      haarBlockKLGrid M N K := by
  unfold haarBlockKLGrid
  apply Finset.sum_congr rfl
  intro i _
  exact haarBlockLikelihoodGridSummand_eq_klSummand hN hK hs i

/-- A proved exact grid identity for the block KL immediately yields its
finite ENNReal bound.  The equality is an explicit theorem argument, not a
project declaration or hidden interface. -/
theorem block_klDiv_le_of_grid_identity
    (H : UnitaryHaarProbabilityFamily) {M N K : ℕ}
    (hN : 0 < N) (hK : 0 < K) (hs : K + N ≤ M)
    (hgrid :
      InformationTheory.klDiv
          (sqrtScaledHaarBlockLaw H M N K)
          (standardGaussianBlockLaw N K) =
        ENNReal.ofReal (haarBlockKLGrid M N K)) :
    InformationTheory.klDiv
        (sqrtScaledHaarBlockLaw H M N K)
        (standardGaussianBlockLaw N K) ≤
      ENNReal.ofReal
        ((K : ℝ) * N * ((K : ℝ) + N) ^ 2 /
          (2 * (M : ℝ) ^ 2)) := by
  rw [hgrid]
  exact ENNReal.ofReal_le_ofReal (haarBlockKLGrid_le hN hK hs)

/-- It is enough to prove the exact KL grid identity for the canonical Haar
law.  Haar uniqueness transports that single analytic theorem to every
normalized Haar family used by the project. -/
theorem block_klDiv_le_of_canonical_grid_identity
    (H : UnitaryHaarProbabilityFamily) {M N K : ℕ}
    (hN : 0 < N) (hK : 0 < K) (hs : K + N ≤ M)
    (hcanonical :
      InformationTheory.klDiv
          (sqrtScaledHaarBlockLaw
            canonicalUnitaryHaarProbabilityFamily M N K)
          (standardGaussianBlockLaw N K) =
        ENNReal.ofReal (haarBlockKLGrid M N K)) :
    InformationTheory.klDiv
        (sqrtScaledHaarBlockLaw H M N K)
        (standardGaussianBlockLaw N K) ≤
      ENNReal.ofReal
        ((K : ℝ) * N * ((K : ℝ) + N) ^ 2 /
          (2 * (M : ℝ) ^ 2)) := by
  apply block_klDiv_le_of_grid_identity H hN hK hs
  rw [sqrtScaledHaarBlockLaw_eq_canonical H M N K]
  exact hcanonical

/-- The same finite KL bound for the transpose Gram product, by the internally
proved deterministic data processing theorem. -/
theorem transposeGram_klDiv_le_of_block_grid_identity
    (H : UnitaryHaarProbabilityFamily) {M N K : ℕ}
    (hN : 0 < N) (hK : 0 < K) (hs : K + N ≤ M)
    (hgrid :
      InformationTheory.klDiv
          (sqrtScaledHaarBlockLaw H M N K)
          (standardGaussianBlockLaw N K) =
        ENNReal.ofReal (haarBlockKLGrid M N K)) :
    InformationTheory.klDiv
        (scaledHaarTransposeGramLaw H M N K)
        (gaussianTransposeGramLaw N K) ≤
      ENNReal.ofReal
        ((K : ℝ) * N * ((K : ℝ) + N) ^ 2 /
          (2 * (M : ℝ) ^ 2)) := by
  have hNM : N ≤ M := by omega
  have hKM : K ≤ M := by omega
  exact (klDiv_transposeGram_le_block H hNM hKM).trans
    (block_klDiv_le_of_grid_identity H hN hK hs hgrid)

/-- Real valued version of the product KL estimate. -/
theorem toReal_transposeGram_klDiv_le_of_block_grid_identity
    (H : UnitaryHaarProbabilityFamily) {M N K : ℕ}
    (hN : 0 < N) (hK : 0 < K) (hs : K + N ≤ M)
    (hgrid :
      InformationTheory.klDiv
          (sqrtScaledHaarBlockLaw H M N K)
          (standardGaussianBlockLaw N K) =
        ENNReal.ofReal (haarBlockKLGrid M N K)) :
    (InformationTheory.klDiv
        (scaledHaarTransposeGramLaw H M N K)
        (gaussianTransposeGramLaw N K)).toReal ≤
      (K : ℝ) * N * ((K : ℝ) + N) ^ 2 /
        (2 * (M : ℝ) ^ 2) := by
  let b : ℝ :=
    (K : ℝ) * N * ((K : ℝ) + N) ^ 2 /
      (2 * (M : ℝ) ^ 2)
  have hb0 : 0 ≤ b := by
    dsimp [b]
    positivity
  have hle :
      InformationTheory.klDiv
          (scaledHaarTransposeGramLaw H M N K)
          (gaussianTransposeGramLaw N K) ≤
        ENNReal.ofReal b := by
    exact transposeGram_klDiv_le_of_block_grid_identity H hN hK hs hgrid
  have hfinite :
      InformationTheory.klDiv
          (scaledHaarTransposeGramLaw H M N K)
          (gaussianTransposeGramLaw N K) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hreal :=
    (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).2 hle
  rw [ENNReal.toReal_ofReal hb0] at hreal
  exact hreal

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse

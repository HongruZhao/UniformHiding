import LogdetLean.GramHafnian.UltimateHiding.Dense.HaarRecursionFromRowStiefel
import LogdetLean.GramHafnian.UltimateHiding.Sparse.HaarBlockLaw

/-!
# External geometric input for Haar one-column deletion

`OneColumnConcrete` reduces Haar/Stiefel deletion to one literal equality of
finite-dimensional probability measures.  The old version of this file
postulated that final Gram equality directly.  It is now a theorem: the only
geometric input is the K-free, Gram-free scaled row-Stiefel disintegration in
`RowStiefelDeletionExternal`, and all restriction, transpose-Gram,
normalization, kernel, and Haar-family transport steps are internal Lean
proofs.

## Source ledger

The atom is the following standard consequence of complex Stiefel
disintegration.

* P. Bourgade, C. P. Hughes, A. Nikeghbali, and M. Yor,
  *The characteristic polynomial of a random unitary matrix: a probabilistic
  approach*, Duke Math. J. 145 (2008), Proposition 2.1,
  https://doi.org/10.1215/00127094-2008-046 .  Proposition 2.1 gives the
  recursive Haar construction from an independent lower-dimensional Haar
  unitary and a uniform point of the complex unit sphere.
* K. Zyczkowski and H.-J. Sommers, *Induced measures in the space of mixed
  quantum states*, J. Phys. A 34 (2001), Section II, equation (2.9), and
  Appendix A, https://doi.org/10.1088/0305-4470/34/35/335 .  For a uniform
  complex unit vector, the squared coordinate moduli are
  `Dirichlet(1,...,1)`.  Hence the squared norm of its first `N` coordinates is
  `Beta(N,m+1-N)`, its complement `q` is
  `Beta(m-N+1,N)`, and the projected direction is independent and uniform.
* I. Pitaval and O. Tirkkonen, *Joint Grassmann-Stiefel Quantization for MIMO
  Product Codebooks*, IEEE Trans. Wireless Commun. 13 (2014), Lemma 1,
  https://doi.org/10.1109/TWC.2013.111313.130208 . The lemma supplies the
  complex Stiefel truncation/polar Haar factor; the joint independence used by
  the atom is the invariant-disintegration corollary of its proof, not a
  verbatim statement of the lemma.

Writing the last column of an `(m+1)`-dimensional Haar unitary as `c` in the
first `N` rows, polar decomposition of the remaining row-Stiefel block gives

`F = I + (sqrt q - 1) v v*`,  `q = 1 - ||c||^2`.

Thus its first `K` columns are `F` times an independent `N x K` corner at
ambient dimension `m`.  Passing to the transpose Gram matrix and multiplying
by the paper normalization `(m+1)/sqrt K` gives exactly the congruence kernel
below, including its factor `sqrt((m+1)/m)`.  No total-variation, score, tail,
or asymptotic assertion is included in the external atom.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

open LocalAnticoncentration

/-- The normalized transpose-Gram law is independent of the chosen
presentation of normalized Haar probability. -/
theorem concreteHaarAmbientLaw_eq_canonical
    (H : UnitaryHaarProbabilityFamily) (N K m : ℕ) :
    concreteHaarAmbientLaw H N K m =
      concreteHaarAmbientLaw canonicalUnitaryHaarProbabilityFamily N K m := by
  unfold concreteHaarAmbientLaw normalizedHaarTransposeGramLaw
  congr 1
  unfold scaledHaarTransposeGramLaw
  split_ifs with h
  · rw [UltimateHiding.Sparse.normalizedUnitaryHaarLaw_eq_canonical H m]
    rfl
  · rfl

/-- **Derived H1 endpoint: complex Stiefel one-row disintegration.**

For `1 <= N <= K <= m`, the normalized transpose-Gram corner in ambient
dimension `m+1` is obtained from its ambient-`m` law by the literal independent
`Beta(m-N+1,N)` / uniform-complex-sphere congruence kernel defined in
`OneColumnConcrete`.

This formerly endpoint-shaped external equality is now derived from the
structural row-Stiefel disintegration recorded in the source ledger above. -/
theorem complexStiefel_oneColumnRecursion_external
    (N K m : ℕ)
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKm : K ≤ m) :
    concreteHaarAmbientLaw canonicalUnitaryHaarProbabilityFamily N K (m + 1) =
      concreteOneColumnMatrixKernel m N ∘ₘ
        concreteHaarAmbientLaw canonicalUnitaryHaarProbabilityFamily N K m :=
  complexStiefel_oneColumnRecursion_from_rowStiefel
    N K m hN hNK hKm

/-- The canonical external equality transports to any normalized Haar
probability family by Haar uniqueness, an internal Mathlib theorem. -/
theorem concreteHaar_oneColumn_step
    (H : UnitaryHaarProbabilityFamily) {N K m : ℕ}
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKm : K ≤ m) :
    concreteHaarAmbientLaw H N K (m + 1) =
      concreteOneColumnMatrixKernel m N ∘ₘ
        concreteHaarAmbientLaw H N K m := by
  rw [concreteHaarAmbientLaw_eq_canonical H N K (m + 1),
    concreteHaarAmbientLaw_eq_canonical H N K m]
  exact complexStiefel_oneColumnRecursion_external N K m hN hNK hKm

/-- Paper-facing exact recursion, derived from the single external Stiefel
equality. -/
theorem concreteHaarOneColumnRecursion
    (H : UnitaryHaarProbabilityFamily) {N K : ℕ}
    (hN : 1 ≤ N) (hNK : N ≤ K) :
    ConcreteHaarOneColumnRecursion H N K := by
  intro m hKm
  exact concreteHaar_oneColumn_step H hN hNK hKm

/-- One explicit recursion step with the external interface discharged. -/
theorem concreteHaarOneColumnRecursion_step_eq
    (H : UnitaryHaarProbabilityFamily) {N K m : ℕ}
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKm : K ≤ m) :
    concreteHaarAmbientLaw H N K (m + 1) =
      concreteOneColumnMatrixKernel m N ∘ₘ
        concreteHaarAmbientLaw H N K m :=
  ConcreteHaarOneColumnRecursion.step_eq
    (concreteHaarOneColumnRecursion H hN hNK) hKm

/-- Two exact recursion steps, with all kernel composition algebra internal. -/
theorem concreteHaarOneColumnRecursion_two_steps
    (H : UnitaryHaarProbabilityFamily) {N K m : ℕ}
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKm : K ≤ m) :
    concreteHaarAmbientLaw H N K (m + 2) =
      (concreteOneColumnMatrixKernel (m + 1) N ∘ₖ
          concreteOneColumnMatrixKernel m N) ∘ₘ
        concreteHaarAmbientLaw H N K m :=
  ConcreteHaarOneColumnRecursion.two_steps
    (concreteHaarOneColumnRecursion H hN hNK) hKm

end

end LogdetLean.GramHafnian.UltimateHiding.Dense

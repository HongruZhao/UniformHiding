import A4.InverseMomentAlgebra

open scoped BigOperators Matrix

noncomputable section
namespace A4Research

/-- A relabeling matrix with the column-to-row convention used in the
matching degree factorization. -/
def relabelingMatrix {I : Type*} [DecidableEq I] (e : I ≃ I) : Matrix I I ℂ :=
  Matrix.of fun i j ↦ if i = e j then 1 else 0

theorem relabelingMatrix_mul_apply {I J : Type*}
    [Fintype I] [DecidableEq I] (e : I ≃ I) (A : Matrix I J ℂ) (i : I) (j : J) :
    (relabelingMatrix e * A) i j = A (e.symm i) j := by
  classical
  simp only [Matrix.mul_apply, relabelingMatrix, Matrix.of_apply,
    ite_mul, one_mul, zero_mul]
  simp_rw [← e.symm_apply_eq]
  simp

theorem mul_relabelingMatrix_apply {I J : Type*}
    [Fintype I] [DecidableEq I] (e : I ≃ I) (A : Matrix J I ℂ) (j : J) (i : I) :
    (A * relabelingMatrix e) j i = A j (e i) := by
  classical
  simp [Matrix.mul_apply, relabelingMatrix, mul_ite]

/-- Simultaneous relabeling invariance proves actual matrix commutation. -/
theorem relabelingMatrix_commutes_of_invariant {I : Type*}
    [Fintype I] [DecidableEq I] (e : I ≃ I) (A : Matrix I I ℂ)
    (hinvariant : ∀ i j, A (e i) (e j) = A i j) :
    relabelingMatrix e * A = A * relabelingMatrix e := by
  ext i j
  rw [relabelingMatrix_mul_apply, mul_relabelingMatrix_apply]
  simpa only [Equiv.apply_symm_apply] using (hinvariant (e.symm i) j).symm

end A4Research

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

def matchingRelabelMatrix {n : ℕ} (g : Equiv.Perm (Fin (2 * n))) :
    Matrix (PM n) (PM n) ℂ :=
  A4Research.relabelingMatrix (matchingRelabelEquiv g)

theorem matchingRelabelMatrix_apply {n : ℕ} (g : Equiv.Perm (Fin (2 * n)))
    (M N : PM n) :
    matchingRelabelMatrix g M N = if M = transportPairPartition g N then 1 else 0 := rfl

theorem matchingRelabelMatrix_mul_apply {n : ℕ} (g : Equiv.Perm (Fin (2 * n)))
    (A : Matrix (PM n) (PM n) ℂ) (M N : PM n) :
    (matchingRelabelMatrix g * A) M N = A (transportPairPartition g⁻¹ M) N :=
  A4Research.relabelingMatrix_mul_apply _ _ _ _

theorem matchingRelabelMatrix_commutes_orthogonalGram {n : ℕ}
    (g : Equiv.Perm (Fin (2 * n))) (z : ℂ) :
    matchingRelabelMatrix g * orthogonalGram n z =
      orthogonalGram n z * matchingRelabelMatrix g := by
  apply A4Research.relabelingMatrix_commutes_of_invariant
  exact fun M N ↦ orthogonalGram_transport z g M N

theorem matchingRelabelMatrix_commutes_modifiedGramInverse {n : ℕ}
    (g : Equiv.Perm (Fin (2 * n))) (gamma : ℝ) :
    matchingRelabelMatrix g * modifiedGramInverse n gamma =
      modifiedGramInverse n gamma * matchingRelabelMatrix g := by
  apply A4Research.relabelingMatrix_commutes_of_invariant
  intro M N
  change modifiedGramInverse n gamma (transportPairPartition g M)
    (transportPairPartition g N) = modifiedGramInverse n gamma M N
  simp only [modifiedGramInverse, Matrix.smul_apply, smul_eq_mul,
    orthogonalGram_inv_transport]

end MatsumotoPaper

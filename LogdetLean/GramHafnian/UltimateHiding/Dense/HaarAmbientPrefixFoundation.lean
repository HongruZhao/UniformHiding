import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Complex.Basic

/-!
# Elementary ambient block-unitary embedding

This dependency-light module contains only the finite matrix algebra needed
to embed `U(N)` as the leading block of `U(m)`.  Keeping it below the Haar
recursion layer prevents the internal H1 disintegration proof from importing
the historical recursion interface that it is meant to prove.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

/-- The canonical decomposition of the first `N` ambient coordinates and
their complement. -/
def haarAmbientPrefixEquiv {N m : ℕ} (hNm : N ≤ m) :
    Fin N ⊕ Fin (m - N) ≃ Fin m :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hNm))

@[simp]
theorem haarAmbientPrefixEquiv_inl {N m : ℕ} (hNm : N ≤ m)
    (i : Fin N) :
    haarAmbientPrefixEquiv hNm (Sum.inl i) = Fin.castLE hNm i := by
  apply Fin.ext
  simp [haarAmbientPrefixEquiv, Fin.castLE]

/-- The ambient matrix `U ⊕ I_(m-N)`, reindexed to `Fin m`. -/
def haarAmbientPrefixMatrix {N m : ℕ} (hNm : N ≤ m)
    (U : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.reindex (haarAmbientPrefixEquiv hNm) (haarAmbientPrefixEquiv hNm)
    (Matrix.fromBlocks (U : Matrix (Fin N) (Fin N) ℂ) 0 0
      (1 : Matrix (Fin (m - N)) (Fin (m - N)) ℂ))

theorem haarAmbientPrefixMatrix_mem_unitary {N m : ℕ} (hNm : N ≤ m)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    haarAmbientPrefixMatrix hNm U ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  let e := haarAmbientPrefixEquiv hNm
  let U0 : Matrix (Fin N) (Fin N) ℂ := U
  let B : Matrix (Fin N ⊕ Fin (m - N)) (Fin N ⊕ Fin (m - N)) ℂ :=
    Matrix.fromBlocks U0 0 0
      (1 : Matrix (Fin (m - N)) (Fin (m - N)) ℂ)
  have hU : U0 * Matrix.conjTranspose U0 = 1 := by
    simpa [U0, Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp U.property)
  have hB : B * Matrix.conjTranspose B = 1 := by
    simp [B, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, hU, ← Matrix.fromBlocks_one]
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  change Matrix.reindex e e B *
      Matrix.conjTranspose (Matrix.reindex e e B) = 1
  rw [Matrix.conjTranspose_reindex]
  calc
    Matrix.reindex e e B *
        Matrix.reindex e e (Matrix.conjTranspose B) =
        Matrix.reindex e e (B * Matrix.conjTranspose B) := by
      change (Matrix.reindexAlgEquiv ℂ ℂ e B) *
          (Matrix.reindexAlgEquiv ℂ ℂ e (Matrix.conjTranspose B)) =
        Matrix.reindexAlgEquiv ℂ ℂ e (B * Matrix.conjTranspose B)
      exact (map_mul (Matrix.reindexAlgEquiv ℂ ℂ e) B
        (Matrix.conjTranspose B)).symm
    _ = Matrix.reindex e e 1 := by rw [hB]
    _ = 1 := by simp

/-- The ambient block unitary `U ⊕ I_(m-N)`. -/
def haarAmbientPrefixUnitary {N m : ℕ} (hNm : N ≤ m)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Matrix.unitaryGroup (Fin m) ℂ :=
  ⟨haarAmbientPrefixMatrix hNm U,
    haarAmbientPrefixMatrix_mem_unitary hNm U⟩

@[simp]
theorem coe_haarAmbientPrefixUnitary {N m : ℕ} (hNm : N ≤ m)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    (haarAmbientPrefixUnitary hNm U : Matrix (Fin m) (Fin m) ℂ) =
      Matrix.reindex (haarAmbientPrefixEquiv hNm)
        (haarAmbientPrefixEquiv hNm)
        (Matrix.fromBlocks (U : Matrix (Fin N) (Fin N) ℂ) 0 0 1) := by
  rfl

end

end LogdetLean.GramHafnian.UltimateHiding.Dense

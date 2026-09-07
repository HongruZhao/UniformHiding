import LogdetLean.GramHafnian.SymmetricGaussianLimit.Parameters

/-!
# An explicit transpose-Gram factor for every complex symmetric matrix

For a complex symmetric matrix `D`, the rectangular factor

`L(D) = (1/2) [D + I; i(D - I)]`

satisfies `L(D)ᵀ L(D) = D`.  Unlike a Takagi factor, this formula is
polynomial in `D`, so it is directly measurable and introduces no choice of
singular vectors.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian.SymmetricGaussianLimit

noncomputable section

variable {N : ℕ}

/-- Vertical stacking, with a sum type indexing the two row blocks. -/
def vstack (A B : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N ⊕ Fin N) (Fin N) ℂ :=
  fun r j ↦ Sum.elim (fun i ↦ A i j) (fun i ↦ B i j) r

theorem transpose_vstack_mul_vstack
    (A B C E : Matrix (Fin N) (Fin N) ℂ) :
    (vstack A B).transpose * vstack C E =
      A.transpose * C + B.transpose * E := by
  ext i j
  simp [vstack, Matrix.mul_apply, Fintype.sum_sum_type]

/-- Extend a matrix by a block of zero rows.  This is the literal
"top-block" embedding used for rectangular perturbations. -/
def zeroPadRows {r s c : Type*} (A : Matrix r c ℂ) :
    Matrix (r ⊕ s) c ℂ :=
  fun x j ↦ Sum.elim (fun i ↦ A i j) (fun _ ↦ 0) x

/-- Restrict a matrix with sum-indexed rows to its top block. -/
def topRows {r s c : Type*} (X : Matrix (r ⊕ s) c ℂ) :
    Matrix r c ℂ :=
  fun i j ↦ X (Sum.inl i) j

theorem transpose_zeroPadRows_mul_zeroPadRows
    {r s c : Type*} [Fintype r] [Fintype s]
    (A : Matrix r c ℂ) :
    (zeroPadRows (s := s) A).transpose * zeroPadRows (s := s) A =
      A.transpose * A := by
  ext i j
  simp [zeroPadRows, Matrix.mul_apply, Fintype.sum_sum_type]

theorem transpose_mul_zeroPadRows
    {r s c : Type*} [Fintype r] [Fintype s]
    (X : Matrix (r ⊕ s) c ℂ) (A : Matrix r c ℂ) :
    X.transpose * zeroPadRows (s := s) A =
      (topRows X).transpose * A := by
  ext i j
  simp [zeroPadRows, topRows, Matrix.mul_apply, Fintype.sum_sum_type]

theorem transpose_zeroPadRows_mul
    {r s c : Type*} [Fintype r] [Fintype s]
    (A : Matrix r c ℂ) (X : Matrix (r ⊕ s) c ℂ) :
    (zeroPadRows (s := s) A).transpose * X =
      A.transpose * topRows X := by
  ext i j
  simp [zeroPadRows, topRows, Matrix.mul_apply, Fintype.sum_sum_type]

/-- The explicit `2N`-by-`N` factor `L(D)`. -/
def explicitSymmetricGramFactor (D : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N ⊕ Fin N) (Fin N) ℂ :=
  vstack
    ((2 : ℂ)⁻¹ • (D + 1))
    (((2 : ℂ)⁻¹ * Complex.I) • (D - 1))

/-- Every complex symmetric matrix is a transpose-Gram matrix, with the
explicit choice `L(D)`. -/
theorem transpose_explicitSymmetricGramFactor_mul_self
    (D : Matrix (Fin N) (Fin N) ℂ) (hD : D.IsSymm) :
    (explicitSymmetricGramFactor D).transpose *
      explicitSymmetricGramFactor D = D := by
  rw [explicitSymmetricGramFactor, transpose_vstack_mul_vstack]
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
  simp_rw [hD.apply]
  rw [← Finset.sum_add_distrib]
  calc
    ∑ x : Fin N,
        (((2 : ℂ)⁻¹ * (D i x + if x = i then 1 else 0)) *
              ((2 : ℂ)⁻¹ * (D j x + if x = j then 1 else 0)) +
            (((2 : ℂ)⁻¹ * Complex.I) *
                (D i x - if x = i then 1 else 0)) *
              (((2 : ℂ)⁻¹ * Complex.I) *
                (D j x - if x = j then 1 else 0))) =
      ∑ x : Fin N,
        ((2 : ℂ)⁻¹ *
          (D i x * (if x = j then 1 else 0) +
            (if x = i then 1 else 0) * D j x)) := by
      apply Finset.sum_congr rfl
      intro x hx
      ring_nf
      rw [Complex.I_sq]
      ring
    _ = D i j := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      simp [hD.apply]
      ring

/-- Scaling algebra used in the `k=m^4` perturbative Gram limit. -/
theorem scaled_factor_transpose_mul_self
    (D : Matrix (Fin N) (Fin N) ℂ) (hD : D.IsSymm) (m : ℕ) :
    (((m : ℂ) • explicitSymmetricGramFactor D).transpose *
        ((m : ℂ) • explicitSymmetricGramFactor D)) =
      ((m : ℂ) ^ 2) • D := by
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    transpose_explicitSymmetricGramFactor_mul_self D hD]
  congr 1
  ring

/-- After multiplication by `m^{-2}`, the deterministic transpose-Gram term
is exactly `D` for positive `m`. -/
theorem inv_sq_smul_scaled_factor_transpose_mul_self
    (D : Matrix (Fin N) (Fin N) ℂ) (hD : D.IsSymm)
    (m : ℕ) (hm : 0 < m) :
    ((m : ℂ) ^ 2)⁻¹ •
      (((m : ℂ) • explicitSymmetricGramFactor D).transpose *
        ((m : ℂ) • explicitSymmetricGramFactor D)) = D := by
  rw [scaled_factor_transpose_mul_self D hD m]
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hpow : (m : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ hmC
  simp [smul_smul, hpow]

/-- Exact normalized expansion for an arbitrary rectangular factor `F` with
`FᵀF = D`.  This algebraic form is independent of the number of rows. -/
theorem normalized_shifted_transposeGram_expansion_of_factor
    {r : Type*} [Fintype r]
    (D : Matrix (Fin N) (Fin N) ℂ)
    (X F : Matrix r (Fin N) ℂ)
    (m : ℕ) (hm : 0 < m)
    (hfactor : F.transpose * F = D) :
    ((m : ℂ) ^ 2)⁻¹ •
        ((X + (m : ℂ) • F).transpose * (X + (m : ℂ) • F)) =
      ((m : ℂ) ^ 2)⁻¹ • (X.transpose * X) + D +
        (m : ℂ)⁻¹ • (X.transpose * F + F.transpose * X) := by
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul,
    Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [hfactor]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Exact shifted transpose-Gram expansion along the fourth-power
subsequence.  The cross term has coefficient `m^{-1}`, while the deterministic
factor contributes exactly `D`. -/
theorem normalized_shifted_transposeGram_expansion
    (D : Matrix (Fin N) (Fin N) ℂ) (hD : D.IsSymm)
    (X : Matrix (Fin N ⊕ Fin N) (Fin N) ℂ)
    (m : ℕ) (hm : 0 < m) :
    ((m : ℂ) ^ 2)⁻¹ •
        ((X + (m : ℂ) • explicitSymmetricGramFactor D).transpose *
          (X + (m : ℂ) • explicitSymmetricGramFactor D)) =
      ((m : ℂ) ^ 2)⁻¹ • (X.transpose * X) + D +
        (m : ℂ)⁻¹ •
          (X.transpose * explicitSymmetricGramFactor D +
            (explicitSymmetricGramFactor D).transpose * X) := by
  exact normalized_shifted_transposeGram_expansion_of_factor
    D X (explicitSymmetricGramFactor D) m hm
      (transpose_explicitSymmetricGramFactor_mul_self D hD)

/-- The literal top-block construction.  The full matrix may have arbitrarily
many additional rows; only its fixed top `2N` rows occur in the cross term. -/
theorem normalized_zeroPadded_shifted_transposeGram_expansion
    {s : Type*} [Fintype s]
    (D : Matrix (Fin N) (Fin N) ℂ) (hD : D.IsSymm)
    (X : Matrix ((Fin N ⊕ Fin N) ⊕ s) (Fin N) ℂ)
    (m : ℕ) (hm : 0 < m) :
    let L := explicitSymmetricGramFactor D
    let Delta := zeroPadRows (s := s) ((m : ℂ) • L)
    ((m : ℂ) ^ 2)⁻¹ • ((X + Delta).transpose * (X + Delta)) =
      ((m : ℂ) ^ 2)⁻¹ • (X.transpose * X) + D +
        (m : ℂ)⁻¹ •
          ((topRows X).transpose * L + L.transpose * topRows X) := by
  dsimp only
  rw [show zeroPadRows (s := s) ((m : ℂ) • explicitSymmetricGramFactor D) =
      (m : ℂ) • zeroPadRows (s := s) (explicitSymmetricGramFactor D) by
    ext i j
    cases i <;> simp [zeroPadRows]]
  rw [normalized_shifted_transposeGram_expansion_of_factor D X
    (zeroPadRows (s := s) (explicitSymmetricGramFactor D)) m hm
    (by
      rw [transpose_zeroPadRows_mul_zeroPadRows]
      exact transpose_explicitSymmetricGramFactor_mul_self D hD)]
  rw [transpose_mul_zeroPadRows, transpose_zeroPadRows_mul]

/-! ## Literal finite row indexing used in Corollary I.4 -/

/-- Canonical identification of the two `N` row blocks, followed by their
complement, with the paper's literal `Fin k` row index. -/
def finiteBlockRowEquiv (N k : ℕ) (h : N + N ≤ k) :
    ((Fin N ⊕ Fin N) ⊕ Fin (k - (N + N))) ≃ Fin k :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans
    (finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h)))

/-- Reindex only the rows of a finite matrix. -/
def reindexRows {r s c : Type*} (e : r ≃ s) (A : Matrix r c ℂ) :
    Matrix s c ℂ :=
  Matrix.reindex e (Equiv.refl c) A

/-- Concatenate a top row block and a tail row block. -/
def appendRows {r s c : Type*} (A : Matrix r c ℂ) (B : Matrix s c ℂ) :
    Matrix (r ⊕ s) c ℂ :=
  fun x j ↦ Sum.elim (fun i ↦ A i j) (fun i ↦ B i j) x

@[simp] theorem topRows_appendRows {r s c : Type*}
    (A : Matrix r c ℂ) (B : Matrix s c ℂ) :
    topRows (appendRows A B) = A := rfl

@[simp] theorem reindexRows_apply {r s c : Type*} (e : r ≃ s)
    (A : Matrix r c ℂ) (i : s) (j : c) :
    reindexRows e A i j = A (e.symm i) j := rfl

/-- A common row equivalence also preserves a mixed transpose product. -/
theorem transpose_reindexRows_mul_reindexRows_mixed
    {r s c d : Type*} [Fintype r] [Fintype s]
    (e : r ≃ s) (A : Matrix r c ℂ) (B : Matrix r d ℂ) :
    (reindexRows e A).transpose * reindexRows e B = A.transpose * B := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, reindexRows_apply]
  exact Equiv.sum_comp e.symm (fun x : r => A x i * B x j)

/-- A row equivalence does not change a transpose Gram matrix. -/
theorem transpose_reindexRows_mul_reindexRows
    {r s c : Type*} [Fintype r] [Fintype s]
    (e : r ≃ s) (A : Matrix r c ℂ) :
    (reindexRows e A).transpose * reindexRows e A = A.transpose * A := by
  exact transpose_reindexRows_mul_reindexRows_mixed e A A

/-- The explicit factor, first padded by zero rows and then reindexed as a
literal `k` by `N` matrix. -/
def finiteZeroPaddedSymmetricGramFactor
    (D : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) (h : N + N ≤ k) :
    Matrix (Fin k) (Fin N) ℂ :=
  reindexRows (finiteBlockRowEquiv N k h)
    (zeroPadRows (s := Fin (k - (N + N)))
      (explicitSymmetricGramFactor D))

/-- Concatenate the fixed top block and a finite tail, then reindex them as
the paper's literal `Fin k` row matrix. -/
def finiteReindexedRows
    (Y : Matrix (Fin N ⊕ Fin N) (Fin N) ℂ)
    (T : Matrix (Fin (k - (N + N))) (Fin N) ℂ)
    (h : N + N ≤ k) : Matrix (Fin k) (Fin N) ℂ :=
  reindexRows (finiteBlockRowEquiv N k h) (appendRows Y T)

/-- Padding and literal finite row reindexing preserve the exact factor
identity. -/
theorem transpose_finiteZeroPaddedSymmetricGramFactor_mul_self
    (D : Matrix (Fin N) (Fin N) ℂ) (hD : D.IsSymm)
    (k : ℕ) (h : N + N ≤ k) :
    (finiteZeroPaddedSymmetricGramFactor D k h).transpose *
      finiteZeroPaddedSymmetricGramFactor D k h = D := by
  unfold finiteZeroPaddedSymmetricGramFactor
  rw [transpose_reindexRows_mul_reindexRows]
  rw [transpose_zeroPadRows_mul_zeroPadRows]
  exact transpose_explicitSymmetricGramFactor_mul_self D hD

/-- Exact normalized shifted transpose Gram expansion on the literal `Fin k`
row type.  This is the finite indexing bridge that was previously implicit in
the paper application. -/
theorem normalized_finiteZeroPadded_shifted_transposeGram_expansion
    (D : Matrix (Fin N) (Fin N) ℂ) (hD : D.IsSymm)
    (X : Matrix (Fin k) (Fin N) ℂ)
    (m : ℕ) (hm : 0 < m) (h : N + N ≤ k) :
    let F := finiteZeroPaddedSymmetricGramFactor D k h
    ((m : ℂ) ^ 2)⁻¹ •
        ((X + (m : ℂ) • F).transpose * (X + (m : ℂ) • F)) =
      ((m : ℂ) ^ 2)⁻¹ • (X.transpose * X) + D +
        (m : ℂ)⁻¹ • (X.transpose * F + F.transpose * X) := by
  dsimp only
  exact normalized_shifted_transposeGram_expansion_of_factor D X
    (finiteZeroPaddedSymmetricGramFactor D k h) m hm
      (transpose_finiteZeroPaddedSymmetricGramFactor_mul_self D hD k h)

/-- The exact `k = m^4` specialization printed in the proof of Corollary I.4. -/
theorem normalized_fourthPowerZeroPadded_shifted_transposeGram_expansion
    (D : Matrix (Fin N) (Fin N) ℂ) (hD : D.IsSymm)
    (m : ℕ) (X : Matrix (Fin (m ^ 4)) (Fin N) ℂ)
    (hm : 0 < m) (hrows : N + N ≤ m ^ 4) :
    let F := finiteZeroPaddedSymmetricGramFactor D (m ^ 4) hrows
    ((m : ℂ) ^ 2)⁻¹ •
        ((X + (m : ℂ) • F).transpose * (X + (m : ℂ) • F)) =
      ((m : ℂ) ^ 2)⁻¹ • (X.transpose * X) + D +
        (m : ℂ)⁻¹ • (X.transpose * F + F.transpose * X) := by
  exact normalized_finiteZeroPadded_shifted_transposeGram_expansion
    D hD X m hm hrows

/-- Literal fourth power row construction with the cross term reduced to the
single fixed top block `Y`.  This is exactly the deterministic matrix identity
used in the common product coupling for Corollary I.4. -/
theorem normalized_fourthPowerReindexedTopBlock_shifted_transposeGram_expansion
    (D : Matrix (Fin N) (Fin N) ℂ) (hD : D.IsSymm)
    (m : ℕ) (Y : Matrix (Fin N ⊕ Fin N) (Fin N) ℂ)
    (T : Matrix (Fin (m ^ 4 - (N + N))) (Fin N) ℂ)
    (hm : 0 < m) (hrows : N + N ≤ m ^ 4) :
    let X := finiteReindexedRows Y T hrows
    let F := finiteZeroPaddedSymmetricGramFactor D (m ^ 4) hrows
    let L := explicitSymmetricGramFactor D
    ((m : ℂ) ^ 2)⁻¹ •
        ((X + (m : ℂ) • F).transpose * (X + (m : ℂ) • F)) =
      ((m : ℂ) ^ 2)⁻¹ • (X.transpose * X) + D +
        (m : ℂ)⁻¹ • (Y.transpose * L + L.transpose * Y) := by
  dsimp only
  rw [normalized_shifted_transposeGram_expansion_of_factor D
    (finiteReindexedRows Y T hrows)
    (finiteZeroPaddedSymmetricGramFactor D (m ^ 4) hrows) m hm
    (transpose_finiteZeroPaddedSymmetricGramFactor_mul_self
      D hD (m ^ 4) hrows)]
  unfold finiteReindexedRows finiteZeroPaddedSymmetricGramFactor
  rw [transpose_reindexRows_mul_reindexRows_mixed,
    transpose_reindexRows_mul_reindexRows_mixed,
    transpose_reindexRows_mul_reindexRows_mixed]
  rw [transpose_mul_zeroPadRows, transpose_zeroPadRows_mul]
  simp only [topRows_appendRows]

end

end LogdetLean.GramHafnian.SymmetricGaussianLimit

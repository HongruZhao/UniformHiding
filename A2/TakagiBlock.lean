import A2.TakagiVector

open scoped BigOperators Matrix

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

def takagiFirstBlock {N : ℕ} (r : ℂ) (B : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ := fun i j =>
  Fin.cases (Fin.cases r (fun _ => 0) j)
    (fun i => Fin.cases 0 (fun j => B i j) j) i

@[simp] theorem takagiFirstBlock_zero_zero {N : ℕ} (r : ℂ) (B : Matrix (Fin N) (Fin N) ℂ) :
    takagiFirstBlock r B 0 0 = r := rfl

@[simp] theorem takagiFirstBlock_zero_succ {N : ℕ} (r : ℂ)
    (B : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) : takagiFirstBlock r B 0 j.succ = 0 := rfl

@[simp] theorem takagiFirstBlock_succ_zero {N : ℕ} (r : ℂ)
    (B : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) : takagiFirstBlock r B i.succ 0 = 0 := rfl

@[simp] theorem takagiFirstBlock_succ_succ {N : ℕ} (r : ℂ)
    (B : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) : takagiFirstBlock r B i.succ j.succ = B i j := rfl

theorem takagiFirstBlock_mul {N : ℕ} (r s : ℂ) (B D : Matrix (Fin N) (Fin N) ℂ) :
    takagiFirstBlock r B * takagiFirstBlock s D = takagiFirstBlock (r * s) (B * D) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem takagiFirstBlock_transpose {N : ℕ} (r : ℂ) (B : Matrix (Fin N) (Fin N) ℂ) :
    (takagiFirstBlock r B).transpose = takagiFirstBlock r B.transpose := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl

theorem takagiFirstBlock_conjTranspose {N : ℕ} (r : ℂ) (B : Matrix (Fin N) (Fin N) ℂ) :
    (takagiFirstBlock r B).conjTranspose = takagiFirstBlock (star r) B.conjTranspose := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.conjTranspose_apply]

theorem takagiFirstBlock_one (N : ℕ) :
    takagiFirstBlock 1 (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [Matrix.one_apply, eq_comm]

theorem takagiFirstBlock_diagonal {N : ℕ} (r : ℂ) (v : Fin N → ℂ) :
    takagiFirstBlock r (Matrix.diagonal v) = Matrix.diagonal (Fin.cons r v) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [Matrix.diagonal_apply, eq_comm]

def takagiLiftUnitary {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Matrix.unitaryGroup (Fin (N + 1)) ℂ := by
  refine ⟨takagiFirstBlock 1 U, Matrix.mem_unitaryGroup_iff'.mpr ?_⟩
  change (takagiFirstBlock 1 (U : Matrix (Fin N) (Fin N) ℂ)).conjTranspose *
    takagiFirstBlock 1 U = 1
  rw [takagiFirstBlock_conjTranspose, takagiFirstBlock_mul]
  have hu : (U : Matrix (Fin N) (Fin N) ℂ).conjTranspose * U = 1 := U.property.1
  rw [hu]
  simpa only [star_one, one_mul] using takagiFirstBlock_one N

def takagiBasisUnitary {N : ℕ}
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    Matrix.unitaryGroup (Fin N) ℂ :=
  ⟨(EuclideanSpace.basisFun (Fin N) ℂ).toBasis.toMatrix b.toBasis,
    (EuclideanSpace.basisFun (Fin N) ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩

@[simp] theorem takagiBasisUnitary_apply {N : ℕ}
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i j : Fin N) :
    takagiBasisUnitary b i j = b j i := rfl

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

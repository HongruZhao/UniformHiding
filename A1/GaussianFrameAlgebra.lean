import A1.Target

open Matrix WithLp
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section
namespace A1Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The literal rectangular polar normalization; the matrix inverse is totalized. -/
def gaussianPolarFrame {n m : ℕ} (G : Matrix (Fin n) (Fin m) ℂ) :
    Matrix (Fin n) (Fin m) ℂ :=
  G * (CFC.sqrt (G.conjTranspose * G))⁻¹

/-- The actual orthonormal-column carrier, without a quotient or phase convention. -/
abbrev StiefelFrame (n m : ℕ) :=
  {Q : Matrix (Fin n) (Fin m) ℂ // Q.conjTranspose * Q = 1}

def firstColumns {n m : ℕ} (hmn : m ≤ n)
    (U : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin m) ℂ :=
  fun i j ↦ (U : Matrix (Fin n) (Fin n) ℂ) i (Fin.castLE hmn j)

theorem firstColumns_mul {n m : ℕ} (hmn : m ≤ n)
    (U V : Matrix.unitaryGroup (Fin n) ℂ) :
    firstColumns hmn (U * V) =
      (U : Matrix (Fin n) (Fin n) ℂ) * firstColumns hmn V := by
  ext i j
  rfl

theorem firstColumns_gram {n m : ℕ} (hmn : m ≤ n)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (firstColumns hmn U).conjTranspose * firstColumns hmn U = 1 := by
  ext i j
  have h := congrFun (congrFun U.property.1 (Fin.castLE hmn i)) (Fin.castLE hmn j)
  simpa only [firstColumns, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.star_eq_conjTranspose, Matrix.one_apply,
    Fin.castLE_inj] using h

theorem gaussianPolarFrame_gram {n m : ℕ} (G : Matrix (Fin n) (Fin m) ℂ)
    (hG : (G.conjTranspose * G).PosDef) :
    (gaussianPolarFrame G).conjTranspose * gaussianPolarFrame G = 1 := by
  let R := CFC.sqrt (G.conjTranspose * G)
  have hR : R.PosDef := hG.isStrictlyPositive.sqrt.posDef
  have hsq : R * R = G.conjTranspose * G :=
    CFC.sqrt_mul_sqrt_self _ hG.posSemidef.nonneg
  have hunit := (Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit
  simp only [gaussianPolarFrame, Matrix.conjTranspose_mul]
  change (R⁻¹).conjTranspose * G.conjTranspose * (G * R⁻¹) = 1
  rw [hR.inv.isHermitian.eq, ← Matrix.mul_assoc, Matrix.mul_assoc R⁻¹ G.conjTranspose G,
    ← hsq, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul R hunit, Matrix.one_mul,
    Matrix.mul_nonsing_inv R hunit]

theorem gaussianPolarFrame_unitary_mul {n m : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) (G : Matrix (Fin n) (Fin m) ℂ) :
    gaussianPolarFrame ((U : Matrix (Fin n) (Fin n) ℂ) * G) =
      (U : Matrix (Fin n) (Fin n) ℂ) * gaussianPolarFrame G := by
  have hg : ((U : Matrix (Fin n) (Fin n) ℂ) * G).conjTranspose *
      ((U : Matrix (Fin n) (Fin n) ℂ) * G) = G.conjTranspose * G := by
    have hu : (U : Matrix (Fin n) (Fin n) ℂ).conjTranspose * U = 1 := U.property.1
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (U : Matrix (Fin n) (Fin n) ℂ).conjTranspose,
      hu, Matrix.one_mul]
  simp only [gaussianPolarFrame, hg, Matrix.mul_assoc]

theorem gaussianPolarFrame_overlap {n m : ℕ} (G : Matrix (Fin n) (Fin m) ℂ) :
    (gaussianPolarFrame G).transpose * gaussianPolarFrame G =
      (CFC.sqrt (G.conjTranspose * G)).transpose⁻¹ *
        (G.transpose * G) * (CFC.sqrt (G.conjTranspose * G))⁻¹ := by
  simp only [gaussianPolarFrame, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
    Matrix.mul_assoc]

theorem orthonormal_columns_of_gram {n m : ℕ}
    (Q : Matrix (Fin n) (Fin m) ℂ) (hQ : Q.conjTranspose * Q = 1) :
    Orthonormal ℂ (fun j : Fin m ↦ toLp 2 (fun i : Fin n ↦ Q i j)) := by
  rw [orthonormal_iff_ite]
  intro i j
  have h := congrFun (congrFun hQ i) j
  simpa [PiLp.inner_apply, RCLike.inner_apply', Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply, mul_comm] using h

/-- Every literal orthonormal-column matrix is the leading-column block of a unitary.
No measurable choice of a completion is required by the later Haar argument. -/
theorem exists_unitary_firstColumns {n m : ℕ} (hmn : m ≤ n)
    (Q : Matrix (Fin n) (Fin m) ℂ) (hQ : Q.conjTranspose * Q = 1) :
    ∃ U : Matrix.unitaryGroup (Fin n) ℂ, firstColumns hmn U = Q := by
  let e := Equiv.ofInjective (Fin.castLE hmn) (Fin.castLE_injective hmn)
  let v : Fin n → EuclideanSpace ℂ (Fin n) :=
    Function.extend (Fin.castLE hmn)
      (fun j : Fin m ↦ toLp 2 (fun i : Fin n ↦ Q i j)) (fun _ ↦ 0)
  have hv : Orthonormal ℂ ((Set.range (Fin.castLE hmn)).domRestrict v) := by
    convert (orthonormal_columns_of_gram Q hQ).comp e.symm e.symm.injective using 1
    funext j
    obtain ⟨i, hi⟩ := j.property
    have hj : j = e i := Subtype.ext hi.symm
    subst j
    simp only [Set.domRestrict_apply, v, e, Equiv.ofInjective_apply,
      Fin.castLE_injective hmn |>.extend_apply, Function.comp_apply,
      Equiv.ofInjective_symm_apply]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n))
  let a := EuclideanSpace.basisFun (Fin n) ℂ
  let U : Matrix.unitaryGroup (Fin n) ℂ :=
    ⟨a.toBasis.toMatrix b, a.toMatrix_orthonormalBasis_mem_unitary b⟩
  refine ⟨U, ?_⟩
  ext i j
  change a.toBasis.repr (b (Fin.castLE hmn j)) i = Q i j
  rw [hb _ ⟨j, rfl⟩]
  simp [a, v, Fin.castLE_injective hmn |>.extend_apply]

end A1Research

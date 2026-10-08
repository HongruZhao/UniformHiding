import A2.TakagiBlock

open scoped BigOperators Matrix

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

def takagiUnitaryPullback {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (C : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (U : Matrix (Fin N) (Fin N) ℂ).conjTranspose * C *
    (U : Matrix (Fin N) (Fin N) ℂ).conjTranspose.transpose

theorem takagiUnitaryPullback_symmetric {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (C : Matrix (Fin N) (Fin N) ℂ) (hC : C.transpose = C) :
    (takagiUnitaryPullback U C).transpose = takagiUnitaryPullback U C := by
  simp [takagiUnitaryPullback, Matrix.transpose_mul, hC, Matrix.mul_assoc]

theorem takagiUnitaryPullback_recover {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (C : Matrix (Fin N) (Fin N) ℂ) :
    (U : Matrix (Fin N) (Fin N) ℂ) * takagiUnitaryPullback U C *
      (U : Matrix (Fin N) (Fin N) ℂ).transpose = C := by
  have hu : (U : Matrix (Fin N) (Fin N) ℂ) * U.val.conjTranspose = 1 := U.property.2
  change U * (U.val.conjTranspose * C * U.val.conjTranspose.transpose) * U.val.transpose = C
  calc
    _ = ((U : Matrix (Fin N) (Fin N) ℂ) * U.val.conjTranspose) * C *
      ((U : Matrix (Fin N) (Fin N) ℂ) * U.val.conjTranspose).transpose := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = C := by rw [hu]; simp

theorem takagiUnitaryPullback_firstColumn {N : ℕ}
    (C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (u : Fin (N + 1) → ℂ) (r : ℝ) (hTu : takagiConjugateAction C u = r • u)
    (b : OrthonormalBasis (Fin (N + 1)) ℂ (EuclideanSpace ℂ (Fin (N + 1))))
    (hb : b 0 = WithLp.toLp 2 u) :
    (takagiUnitaryPullback (takagiBasisUnitary b) C) *ᵥ Pi.single 0 1 =
      r • (Pi.single 0 1 : Fin (N + 1) → ℂ) := by
  let U := takagiBasisUnitary b
  have hfirst : (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) *ᵥ Pi.single 0 1 = u := by
    rw [Matrix.mulVec_single_one]
    ext i
    change b 0 i = u i
    rw [hb]
  have hlast : (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ).conjTranspose.transpose *ᵥ
      Pi.single 0 1 = star u := by
    rw [Matrix.mulVec_single_one]
    ext i
    change star (b 0 i) = star (u i)
    rw [hb]
  have hback : (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ).conjTranspose *ᵥ u =
      Pi.single 0 1 := by
    rw [← hfirst, Matrix.mulVec_mulVec]
    have hu : (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ).conjTranspose * U = 1 := U.property.1
    rw [hu, Matrix.one_mulVec]
  change (U.val.conjTranspose * C * U.val.conjTranspose.transpose) *ᵥ Pi.single 0 1 = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hlast]
  change U.val.conjTranspose *ᵥ takagiConjugateAction C u = _
  rw [hTu, Matrix.mulVec_smul, hback]

theorem takagiUnitaryPullback_firstBlock {N : ℕ}
    (C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (hC : C.transpose = C)
    (u : Fin (N + 1) → ℂ) (r : ℝ) (hTu : takagiConjugateAction C u = r • u)
    (b : OrthonormalBasis (Fin (N + 1)) ℂ (EuclideanSpace ℂ (Fin (N + 1))))
    (hb : b 0 = WithLp.toLp 2 u) :
    takagiUnitaryPullback (takagiBasisUnitary b) C =
      takagiFirstBlock (r : ℂ)
        ((takagiUnitaryPullback (takagiBasisUnitary b) C).submatrix Fin.succ Fin.succ) := by
  let D := takagiUnitaryPullback (takagiBasisUnitary b) C
  have hcol := takagiUnitaryPullback_firstColumn C u r hTu b hb
  rw [Matrix.mulVec_single_one] at hcol
  have hs : D.transpose = D := takagiUnitaryPullback_symmetric _ _ hC
  have hc (i : Fin (N + 1)) : D i 0 = r • (Pi.single 0 1 : Fin (N + 1) → ℂ) i :=
    congrFun hcol i
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simpa [Complex.real_smul] using hc 0
  · have he : D 0 j.succ = D j.succ 0 :=
      congrArg (fun M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ => M j.succ 0) hs
    change D 0 j.succ = 0
    rw [he]
    simpa using hc j.succ
  · simpa using hc i.succ
  · rfl

/-- Full Autonne--Takagi factorization for every complex symmetric matrix,
with arbitrary nullity and singular-value multiplicities. -/
theorem exists_takagi_factorization (N : ℕ) (C : Matrix (Fin N) (Fin N) ℂ)
    (hC : C.transpose = C) :
    ∃ (U : Matrix.unitaryGroup (Fin N) ℂ) (r : Fin N → ℝ),
      (∀ i, 0 ≤ r i) ∧ C = (U : Matrix (Fin N) (Fin N) ℂ) *
        Matrix.diagonal (fun i => (r i : ℂ)) * (U : Matrix (Fin N) (Fin N) ℂ).transpose := by
  induction N with
  | zero =>
    refine ⟨1, fun i => Fin.elim0 i, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · ext i; exact Fin.elim0 i
  | succ N ih =>
    obtain ⟨r, hr, u, hu, hTu⟩ := exists_normalized_takagiVector N C hC
    obtain ⟨b, hb⟩ := exists_orthonormalBasis_first_takagiVector N (WithLp.toLp 2 u) hu
    let Q := takagiBasisUnitary b
    let B := (takagiUnitaryPullback Q C).submatrix Fin.succ Fin.succ
    have hB : B.transpose = B := by
      ext i j
      exact congrArg (fun M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ => M i.succ j.succ)
        (takagiUnitaryPullback_symmetric Q C hC)
    obtain ⟨V, s, hs, hVs⟩ := ih B hB
    let R := takagiLiftUnitary V
    let t : Fin (N + 1) → ℝ := Fin.cons r s
    refine ⟨Q * R, t, ?_, ?_⟩
    · intro i
      exact Fin.cases hr (fun j => hs j) i
    · have hblock := takagiUnitaryPullback_firstBlock C hC u r hTu b hb
      have hdiag : Matrix.diagonal (fun i : Fin (N + 1) => (t i : ℂ)) =
          takagiFirstBlock (r : ℂ) (Matrix.diagonal (fun i => (s i : ℂ))) := by
        rw [takagiFirstBlock_diagonal]
        congr 1
        funext i
        refine Fin.cases ?_ (fun i => ?_) i <;> rfl
      have hR : (R : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) *
          Matrix.diagonal (fun i : Fin (N + 1) => (t i : ℂ)) * R.val.transpose =
          takagiFirstBlock (r : ℂ) B := by
        rw [hdiag]
        change takagiFirstBlock 1 (V : Matrix (Fin N) (Fin N) ℂ) *
          takagiFirstBlock (r : ℂ) (Matrix.diagonal (fun i => (s i : ℂ))) *
          (takagiFirstBlock 1 (V : Matrix (Fin N) (Fin N) ℂ)).transpose = _
        rw [takagiFirstBlock_transpose, takagiFirstBlock_mul, takagiFirstBlock_mul]
        simp only [one_mul, mul_one]
        rw [← hVs]
      calc
        C = (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) *
            takagiUnitaryPullback Q C * Q.val.transpose := (takagiUnitaryPullback_recover Q C).symm
        _ = Q * (R * Matrix.diagonal (fun i : Fin (N + 1) => (t i : ℂ)) * R.val.transpose) *
            Q.val.transpose := by rw [hblock, hR]
        _ = ((Q * R : Matrix.unitaryGroup (Fin (N + 1)) ℂ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) *
            Matrix.diagonal (fun i : Fin (N + 1) => (t i : ℂ)) *
            ((Q * R : Matrix.unitaryGroup (Fin (N + 1)) ℂ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ).transpose := by
          change Q.val * (R.val * Matrix.diagonal (fun i : Fin (N + 1) => (t i : ℂ)) *
            R.val.transpose) * Q.val.transpose = (Q.val * R.val) *
            Matrix.diagonal (fun i : Fin (N + 1) => (t i : ℂ)) * (Q.val * R.val).transpose
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

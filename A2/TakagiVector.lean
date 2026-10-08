import A2.TakagiAntilinear

open scoped BigOperators Matrix ComplexOrder MatrixOrder

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

/-- Every nonempty complex symmetric matrix has a normalized Takagi vector.
No nonsingularity or distinct-singular-value assumption is used. -/
theorem exists_normalized_takagiVector (N : ℕ) (C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (hC : C.transpose = C) :
    ∃ r : ℝ, 0 ≤ r ∧ ∃ u : Fin (N + 1) → ℂ,
      ‖WithLp.toLp 2 u‖ = 1 ∧ takagiConjugateAction C u = r • u := by
  let hp := Matrix.posSemidef_self_mul_conjTranspose C
  let v : EuclideanSpace ℂ (Fin (N + 1)) := hp.isHermitian.eigenvectorBasis 0
  let lambda := hp.isHermitian.eigenvalues 0
  have hvnorm : ‖v‖ = 1 := hp.isHermitian.eigenvectorBasis.orthonormal.norm_eq_one 0
  have hv : (fun i => v i) ≠ 0 := by
    intro hz
    have hv0 : v = 0 := by ext i; exact congrFun hz i
    rw [hv0, norm_zero] at hvnorm
    norm_num at hvnorm
  have heigen : takagiConjugateAction C (takagiConjugateAction C (fun i => v i)) =
      lambda • (fun i => v i) := by
    rw [takagiConjugateAction_square C hC]
    exact hp.isHermitian.mulVec_eigenvectorBasis 0
  obtain ⟨u, hu, hTu⟩ := exists_takagiVector_of_square_eigenvector C hC
    (fun i => v i) hv lambda (hp.eigenvalues_nonneg 0) heigen
  let z : EuclideanSpace ℂ (Fin (N + 1)) := WithLp.toLp 2 u
  have hz : z ≠ 0 := by simpa [z] using hu
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  refine ⟨Real.sqrt lambda, Real.sqrt_nonneg _, ‖z‖⁻¹ • u, ?_, ?_⟩
  · rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg z)]
    exact inv_mul_cancel₀ hn
  · rw [takagiConjugateAction_real_smul, hTu]
    exact smul_comm _ _ _

/-- A chosen unit Takagi vector can be the first vector of an orthonormal basis. -/
theorem exists_orthonormalBasis_first_takagiVector (N : ℕ)
    (u : EuclideanSpace ℂ (Fin (N + 1))) (hu : ‖u‖ = 1) :
    ∃ b : OrthonormalBasis (Fin (N + 1)) ℂ (EuclideanSpace ℂ (Fin (N + 1))), b 0 = u := by
  let v : Fin (N + 1) → EuclideanSpace ℂ (Fin (N + 1)) := fun _ => u
  have ho : Orthonormal ℂ (({(0 : Fin (N + 1))} : Set (Fin (N + 1))).domRestrict v) := by
    apply orthonormal_subsingleton_iff.mpr
    intro i
    exact hu
  obtain ⟨b, hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℂ (EuclideanSpace ℂ (Fin (N + 1))) = Fintype.card (Fin (N + 1)))
  exact ⟨b, hb 0 (by simp)⟩

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

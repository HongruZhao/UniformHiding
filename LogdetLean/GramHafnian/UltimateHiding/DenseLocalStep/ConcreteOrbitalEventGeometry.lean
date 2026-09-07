import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.ConcreteCorrelatedPath
import Mathlib.Tactic

/-!
# Exact geometry of the centered orbital event path

This file proves the deterministic group identities needed to move an
orbital derivative from an arbitrary path time back to the origin.  It uses
only the closed formula for `exp(s(P_v-I/N))`; there is no density, moment,
score, total-variation, or hiding input.
-/

open MeasureTheory Set

namespace LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- A unit-vector rank-one matrix is an idempotent projection. -/
theorem complexRankOneProjection_mul_self
    {N : ℕ} (v : ComplexUnitSphere N) :
    complexRankOneProjection v * complexRankOneProjection v =
      complexRankOneProjection v := by
  ext i j
  simp only [Matrix.mul_apply, complexRankOneProjection]
  calc
    ∑ k, (v.1 i * star (v.1 k)) * (v.1 k * star (v.1 j)) =
        (v.1 i * star (v.1 j)) * ∑ k, star (v.1 k) * v.1 k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = v.1 i * star (v.1 j) := by
      have hvnorm : ‖v.1‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
      have hsumNorm : ∑ k, ‖v.1 k‖ ^ 2 = 1 := by
        have hsq := PiLp.norm_sq_eq_of_L2 (fun _ : Fin N ↦ ℂ) v.1
        rw [hvnorm] at hsq
        norm_num at hsq ⊢
        exact hsq.symm
      have hsum : ∑ k, star (v.1 k) * v.1 k = (1 : ℂ) := by
        calc
          ∑ k, star (v.1 k) * v.1 k =
              ∑ k, ((‖v.1 k‖ ^ 2 : ℝ) : ℂ) := by
                apply Finset.sum_congr rfl
                intro k _
                have hk : star (v.1 k) * v.1 k =
                    (Complex.normSq (v.1 k) : ℂ) := by
                  simpa using
                    (Complex.normSq_eq_conj_mul_self (z := v.1 k)).symm
                rw [hk, Complex.normSq_eq_norm_sq]
          _ = ((∑ k, ‖v.1 k‖ ^ 2 : ℝ) : ℂ) := by
                rw [Complex.ofReal_sum]
          _ = 1 := by rw [hsumNorm]; norm_num
      rw [hsum, mul_one]

/-- Closed orbital factors form an additive one-parameter group. -/
theorem concreteOrbitalFactor_mul
    {N : ℕ} (hN : 1 ≤ N) (s t : ℝ) (v : ComplexUnitSphere N) :
    concreteOrbitalFactor N s v * concreteOrbitalFactor N t v =
      concreteOrbitalFactor N (s + t) v := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  let P := complexRankOneProjection v
  have hP : P * P = P := complexRankOneProjection_mul_self v
  let aS : ℂ := (Real.exp (-s / (N : ℝ)) : ℝ)
  let aT : ℂ := (Real.exp (-t / (N : ℝ)) : ℝ)
  let bS : ℂ := (Real.exp s - 1 : ℝ)
  let bT : ℂ := (Real.exp t - 1 : ℝ)
  let aST : ℂ := (Real.exp (-(s + t) / (N : ℝ)) : ℝ)
  let bST : ℂ := (Real.exp (s + t) - 1 : ℝ)
  have ha : aS * aT = aST := by
    have haR : Real.exp (-s / (N : ℝ)) * Real.exp (-t / (N : ℝ)) =
        Real.exp (-(s + t) / (N : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      field_simp [hNr]
      ring
    dsimp only [aS, aT, aST]
    norm_cast
  have hb : bS + bT + bS * bT = bST := by
    have hbR : (Real.exp s - 1) + (Real.exp t - 1) +
        (Real.exp s - 1) * (Real.exp t - 1) =
        Real.exp (s + t) - 1 := by
      rw [Real.exp_add]
      ring
    dsimp only [bS, bT, bST]
    norm_cast
  have hinner : (1 + bS • P) * (1 + bT • P) = 1 + bST • P := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, hP, one_smul, smul_smul]
    rw [smul_add, smul_smul]
    have hb' : bS + bT + bT * bS = bST := by
      calc
        bS + bT + bT * bS = bS + bT + bS * bT := by ring
        _ = bST := hb
    rw [← hb']
    module
  change (aS • (1 + bS • P)) * (aT • (1 + bT • P)) =
    aST • (1 + bST • P)
  calc
    (aS • (1 + bS • P)) * (aT • (1 + bT • P)) =
        (aS * aT) • ((1 + bS • P) * (1 + bT • P)) := by
          rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    _ = aST • ((1 + bS • P) * (1 + bT • P)) := by rw [ha]
    _ = aST • (1 + bST • P) := by rw [hinner]

/-- Centered orbital matrix updates form the same additive action. -/
theorem concreteOrbitalMatrixUpdate_add
    {N : ℕ} (hN : 1 ≤ N) (s t : ℝ) (v : ComplexUnitSphere N) :
    concreteOrbitalMatrixUpdate N s v ∘
        concreteOrbitalMatrixUpdate N t v =
      concreteOrbitalMatrixUpdate N (s + t) v := by
  funext A
  unfold concreteOrbitalMatrixUpdate
  rw [← concreteOrbitalFactor_mul hN s t v]
  simp only [Matrix.transpose_mul]
  simp only [Function.comp_apply, Matrix.mul_assoc]

/-- Central and centered-orbital factors commute pointwise. -/
theorem concreteCentralFactor_mul_concreteOrbitalFactor
    (N : ℕ) (c s : ℝ) (v : ComplexUnitSphere N) :
    concreteCentralFactor N c * concreteOrbitalFactor N s v =
      concreteOrbitalFactor N s v * concreteCentralFactor N c := by
  unfold concreteCentralFactor
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]

/-- Scalar and centered-orbital congruence updates commute. -/
theorem concreteCentralMatrixUpdate_comp_concreteOrbitalMatrixUpdate
    (N : ℕ) (c s : ℝ) (v : ComplexUnitSphere N) :
    concreteCentralMatrixUpdate N c ∘ concreteOrbitalMatrixUpdate N s v =
      concreteOrbitalMatrixUpdate N s v ∘ concreteCentralMatrixUpdate N c := by
  funext A
  unfold concreteCentralMatrixUpdate concreteOrbitalMatrixUpdate
  simp only [Function.comp_apply]
  have hcomm := concreteCentralFactor_mul_concreteOrbitalFactor N c s v
  have hcommT := congrArg Matrix.transpose hcomm
  simp only [Matrix.transpose_mul] at hcommT
  calc
    concreteCentralFactor N c *
        (concreteOrbitalFactor N s v * A *
          Matrix.transpose (concreteOrbitalFactor N s v)) *
        Matrix.transpose (concreteCentralFactor N c) =
      (concreteCentralFactor N c * concreteOrbitalFactor N s v) * A *
        (Matrix.transpose (concreteOrbitalFactor N s v) *
          Matrix.transpose (concreteCentralFactor N c)) := by
            simp only [Matrix.mul_assoc]
    _ = (concreteOrbitalFactor N s v * concreteCentralFactor N c) * A *
        (Matrix.transpose (concreteCentralFactor N c) *
          Matrix.transpose (concreteOrbitalFactor N s v)) := by
            rw [hcomm, hcommT]
    _ = concreteOrbitalFactor N s v *
        (concreteCentralFactor N c * A *
          Matrix.transpose (concreteCentralFactor N c)) *
        Matrix.transpose (concreteOrbitalFactor N s v) := by
            simp only [Matrix.mul_assoc]

/-- Fixed-direction orbital updates are measurable in the matrix state. -/
theorem measurable_concreteOrbitalMatrixUpdate_fixed
    (N : ℕ) (s : ℝ) (v : ComplexUnitSphere N) :
    Measurable (concreteOrbitalMatrixUpdate N s v) := by
  unfold concreteOrbitalMatrixUpdate
  exact measurable_complexMatrix_mul
    (measurable_complexMatrix_mul measurable_const measurable_id)
    measurable_const

/-- Fixed-beta, fixed-direction shared updates are measurable in the matrix
state. -/
theorem measurable_concreteSharedBetaPathUpdate_fixed
    (m N : ℕ) (q s : ℝ) (v : ComplexUnitSphere N) :
    Measurable (fun A ↦ concreteSharedBetaPathUpdate m N q s (A, v)) := by
  unfold concreteSharedBetaPathUpdate
  exact (measurable_concreteCentralMatrixUpdate N _).comp
    (measurable_concreteOrbitalMatrixUpdate_fixed N s v)

/-- At fixed beta and fixed direction, shifting orbital time is exactly a
measurable preimage shift of the event. -/
theorem concreteSharedBetaFixedDirectionPath_add
    {m N : ℕ} (hN : 1 ≤ N)
    (mu : Measure (ConcreteMatrixState N))
    (q : ℝ) (v : ComplexUnitSphere N)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event)
    (y t : ℝ) :
    (mu.map (fun A ↦ concreteSharedBetaPathUpdate m N q (y + t) (A, v))).real
        event =
      (mu.map (fun A ↦ concreteSharedBetaPathUpdate m N q t (A, v))).real
        (concreteOrbitalMatrixUpdate N y v ⁻¹' event) := by
  have hleft : Measurable
      (fun A ↦ concreteSharedBetaPathUpdate m N q (y + t) (A, v)) :=
    measurable_concreteSharedBetaPathUpdate_fixed m N q (y + t) v
  have hright : Measurable
      (fun A ↦ concreteSharedBetaPathUpdate m N q t (A, v)) :=
    measurable_concreteSharedBetaPathUpdate_fixed m N q t v
  have horb : Measurable (concreteOrbitalMatrixUpdate N y v) :=
    measurable_concreteOrbitalMatrixUpdate_fixed N y v
  have hupdate : (fun A ↦ concreteSharedBetaPathUpdate m N q (y + t) (A, v)) =
      concreteOrbitalMatrixUpdate N y v ∘
        (fun A ↦ concreteSharedBetaPathUpdate m N q t (A, v)) := by
    funext A
    unfold concreteSharedBetaPathUpdate
    have hadd := congrFun (concreteOrbitalMatrixUpdate_add hN y t v) A
    rw [← hadd]
    have hcomm := congrFun
      (concreteCentralMatrixUpdate_comp_concreteOrbitalMatrixUpdate N
        (oneColumnCenteredScalarLog m N q) y v)
      (concreteOrbitalMatrixUpdate N t v A)
    exact hcomm
  rw [map_measureReal_apply hleft hevent,
    map_measureReal_apply hright (horb hevent)]
  congr 1
  ext A
  simp only [Set.mem_preimage]
  rw [congrFun hupdate A]
  rfl

end

end LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_DeterministicBetaJacobiTransforms

/-!
# Elementary beta-Jacobi normalization without A2

For the project parameters, the beta-Jacobi normalizer is finite and nonzero
for an elementary reason.  After the already proved square and reflection
changes of variables it is the normalizer of Forrester's *raw* beta-one
kernel with a nonnegative natural exponent.  On the open unit cube that raw
kernel is at most one, and it is strictly positive away from the finite union
of collision hyperplanes.

No ensemble-law assertion is used in this file.  In particular, none of the
proofs below depends on `A2_forrester_equation_1_7`.
-/

open scoped BigOperators ENNReal
open Set MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open H6CoordinateAlgebra H6RadialMeasureAdapters

theorem volume_betaJacobiOpenCube (m : ℕ) :
    volume (betaJacobiOpenCube m) = 1 := by
  have hset : betaJacobiOpenCube m =
      Set.pi Set.univ (fun _ : Fin m ↦ Set.Ioo (0 : ℝ) 1) := by
    ext rho
    simp [betaJacobiOpenCube, openUnitCube]
  rw [hset, Real.volume_pi_Ioo]
  simp

theorem forresterEq17Kernel_beta_one_nat_le_one
    {m q : ℕ} {rho : Fin m → ℝ}
    (hrho : rho ∈ betaJacobiOpenCube m) :
    forresterEq17Kernel m 1 (q : ℝ) rho ≤ 1 := by
  classical
  unfold forresterEq17Kernel
  have hleft : (∏ i,
      (ENNReal.ofReal (rho i)).rpow
        ((1 : ℝ) * (q : ℝ))) ≤ 1 := by
    apply Finset.prod_le_one
    · intro i _hi
      exact bot_le
    · intro i _hi
      apply ENNReal.rpow_le_one
      · exact ENNReal.ofReal_le_one.mpr (hrho i).2.le
      · positivity
  have hright : (∏ p ∈ a2StrictPairs m,
      (ENNReal.ofReal
        |(rho p.2) ^ 2 - (rho p.1) ^ 2|).rpow (1 : ℝ)) ≤ 1 := by
    apply Finset.prod_le_one
    · intro p _hp
      exact bot_le
    · intro p hp
      rw [ENNReal.rpow_eq_pow, ENNReal.rpow_one]
      apply ENNReal.ofReal_le_one.mpr
      have hi0 := (hrho p.1).1
      have hi1 := (hrho p.1).2
      have hj0 := (hrho p.2).1
      have hj1 := (hrho p.2).2
      have hiSq : 0 < (rho p.1) ^ 2 := sq_pos_of_pos hi0
      have hiSqOne : (rho p.1) ^ 2 < 1 := by nlinarith
      have hjSq : 0 < (rho p.2) ^ 2 := sq_pos_of_pos hj0
      have hjSqOne : (rho p.2) ^ 2 < 1 := by nlinarith
      rw [abs_le]
      constructor <;> linarith
  exact (mul_le_mul hleft hright bot_le bot_le).trans_eq (one_mul 1)

theorem forresterEq17Kernel_beta_one_nat_pos_of_not_collision
    {m q : ℕ} {rho : Fin m → ℝ}
    (hrho : rho ∈ betaJacobiOpenCube m)
    (hcollision : rho ∉ betaJacobiCollisionSet m) :
    0 < forresterEq17Kernel m 1 (q : ℝ) rho := by
  classical
  unfold forresterEq17Kernel
  apply ENNReal.mul_pos
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _hi
    exact (ENNReal.rpow_pos
      (ENNReal.ofReal_pos.mpr (hrho i).1)
      ENNReal.ofReal_ne_top).ne'
  · apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact (ENNReal.rpow_pos (by
      apply ENNReal.ofReal_pos.mpr
      rw [abs_pos]
      intro hsquare
      have hsum : rho p.2 + rho p.1 ≠ 0 := by
        exact ne_of_gt (add_pos (hrho p.2).1 (hrho p.1).1)
      have heq : rho p.2 = rho p.1 := by
        have hprod :
            (rho p.2 - rho p.1) * (rho p.2 + rho p.1) = 0 := by
          nlinarith [hsquare]
        have hdiff := (mul_eq_zero.mp hprod).resolve_right hsum
        linarith
      apply hcollision
      exact ⟨p.2, p.1, ne_of_gt (Finset.mem_filter.mp hp).2,
        heq⟩) ENNReal.ofReal_ne_top).ne'

theorem forresterEq17RawMeasure_beta_one_nat_le_cube
    (m q : ℕ) :
    forresterEq17RawMeasure m 1 (q : ℝ) ≤
      volume.restrict (betaJacobiOpenCube m) := by
  unfold forresterEq17RawMeasure
  have hAE : forresterEq17Kernel m 1 (q : ℝ) ≤ᵐ[
      volume.restrict (betaJacobiOpenCube m)] 1 := by
    filter_upwards [ae_restrict_mem (measurableSet_openUnitCube_h6 m)]
      with rho hrho
    exact forresterEq17Kernel_beta_one_nat_le_one hrho
  simpa only [withDensity_one] using (withDensity_mono hAE)

theorem forresterEq17Normalization_beta_one_nat_ne_top
    (m q : ℕ) :
    forresterEq17Normalization m 1 (q : ℝ) ≠ ∞ := by
  unfold forresterEq17Normalization
  have hle := (forresterEq17RawMeasure_beta_one_nat_le_cube m q) Set.univ
  have hcube :
      (volume.restrict (betaJacobiOpenCube m)) Set.univ = 1 := by
    simp [volume_betaJacobiOpenCube m]
  rw [hcube] at hle
  exact ne_of_lt (lt_of_le_of_lt hle (by simp))

theorem forresterEq17RawMeasure_beta_one_nat_ne_zero
    (m q : ℕ) :
    forresterEq17RawMeasure m 1 (q : ℝ) ≠ 0 := by
  intro hzero
  have haeZero : forresterEq17Kernel m 1 (q : ℝ) =ᵐ[
      volume.restrict (betaJacobiOpenCube m)] 0 :=
    (withDensity_eq_zero_iff
      (measurable_forresterEq17Kernel_literal m 1 (q : ℝ)).aemeasurable).mp
      (by simpa [forresterEq17RawMeasure] using hzero)
  have hcollisionBase :
      (volume.restrict (betaJacobiOpenCube m))
          (betaJacobiCollisionSet m) = 0 :=
    Measure.absolutelyContinuous_restrict
      (volume_betaJacobiCollisionSet_zero m)
  have haeNotCollision : ∀ᵐ rho ∂(
      volume.restrict (betaJacobiOpenCube m)),
      rho ∉ betaJacobiCollisionSet m := by
    exact (compl_mem_ae_iff.mpr hcollisionBase)
  have haeCube : ∀ᵐ rho ∂(
      volume.restrict (betaJacobiOpenCube m)),
      rho ∈ betaJacobiOpenCube m :=
    ae_restrict_mem (measurableSet_openUnitCube_h6 m)
  have hfalse : ∀ᵐ _rho ∂(
      volume.restrict (betaJacobiOpenCube m)), False := by
    filter_upwards [haeZero, haeNotCollision, haeCube] with rho hzero'
      hnotCollision hrho
    exact (forresterEq17Kernel_beta_one_nat_pos_of_not_collision
      hrho hnotCollision).ne' hzero'
  have hbaseZero :
      volume.restrict (betaJacobiOpenCube m) = 0 := by
    apply Measure.measure_univ_eq_zero.mp
    simpa using (ae_iff.mp hfalse)
  have hmass := congrArg
    (fun μ : Measure (Fin m → ℝ) ↦ μ Set.univ) hbaseZero
  simp [volume_betaJacobiOpenCube m] at hmass

theorem forresterEq17Normalization_beta_one_nat_ne_zero
    (m q : ℕ) :
    forresterEq17Normalization m 1 (q : ℝ) ≠ 0 := by
  unfold forresterEq17Normalization
  intro hmass
  exact (forresterEq17RawMeasure_beta_one_nat_ne_zero m q)
    (Measure.measure_univ_eq_zero.mp hmass)

theorem betaJacobiNormalization_project_ne_zero
    {N K : ℕ} (h2NK : 2 * N ≤ K) :
    betaJacobiNormalization N 1 ((K - 2 * N : ℕ) : ℝ) 1 ≠ 0 := by
  let q := K - 2 * N
  have hsquare := forresterEq17Normalization_beta_one_square N (q : ℝ)
  have hreflect := betaJacobiNormalization_reflection_proved
    N (q : ℝ) 1 1
  have hscale : (a2SquaringScale N : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast a2SquaringScale_ne_zero N
  have hraw := forresterEq17Normalization_beta_one_nat_ne_zero N q
  have hq : a2JacobiA 1 (q : ℝ) = (q : ℝ) := by
    norm_num [a2JacobiA]
  have hone : a2JacobiB (1 : ℝ) = 1 := by
    norm_num [a2JacobiB]
  rw [hq, hone] at hsquare
  rw [← hreflect]
  intro hzero
  rw [hzero, mul_zero] at hsquare
  exact hraw hsquare

theorem betaJacobiNormalization_project_ne_top
    {N K : ℕ} (h2NK : 2 * N ≤ K) :
    betaJacobiNormalization N 1 ((K - 2 * N : ℕ) : ℝ) 1 ≠ ∞ := by
  let q := K - 2 * N
  have hsquare := forresterEq17Normalization_beta_one_square N (q : ℝ)
  have hreflect := betaJacobiNormalization_reflection_proved
    N (q : ℝ) 1 1
  have hscale : (a2SquaringScale N : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast a2SquaringScale_ne_zero N
  have hscaleTop : (a2SquaringScale N : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hraw := forresterEq17Normalization_beta_one_nat_ne_top N q
  have hq : a2JacobiA 1 (q : ℝ) = (q : ℝ) := by
    norm_num [a2JacobiA]
  have hone : a2JacobiB (1 : ℝ) = 1 := by
    norm_num [a2JacobiB]
  rw [hq, hone] at hsquare
  rw [← hreflect]
  intro htop
  rw [htop, ENNReal.mul_top hscale] at hsquare
  exact hraw hsquare

/-- The exact project beta-Jacobi probability normalization, proved without
Forrester's ensemble-law axiom A2. -/
theorem H6_betaJacobiProbabilityMeasure_univ_A2Free
    {N K : ℕ} (_hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    betaJacobiProbabilityMeasure N 1
        ((K - 2 * N : ℕ) : ℝ) 1 Set.univ = 1 := by
  unfold betaJacobiProbabilityMeasure normalizeMeasure
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (betaJacobiNormalization_project_ne_zero h2NK)
    (betaJacobiNormalization_project_ne_top h2NK)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

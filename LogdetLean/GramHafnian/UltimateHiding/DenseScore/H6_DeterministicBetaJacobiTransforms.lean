import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_BetaJacobiCore
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_TakagiSquareJacobian
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Group.Measure

/-!
# Deterministic beta-Jacobi coordinate transforms

This module proves the coordinatewise-square Jacobian, reflection identity,
collision nullity, and normalization facts used by the A2' route.  It imports
the axiom-free beta-Jacobi core and declares no scientific axiom, ensemble law,
or H6 endpoint.
-/

open scoped BigOperators ENNReal
open Set MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open H6CoordinateAlgebra H6RadialMeasureAdapters

/-! ## Measurability of the literal density kernels -/

theorem measurable_betaJacobiKernel_literal
    (n : ℕ) (a b beta : ℝ) :
    Measurable (betaJacobiKernel n a b beta) := by
  classical
  unfold betaJacobiKernel
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro i _hi
    apply Measurable.mul
    · exact ENNReal.continuous_rpow_const.measurable.comp
        (ENNReal.measurable_ofReal.comp (measurable_pi_apply i))
    · exact ENNReal.continuous_rpow_const.measurable.comp
        (ENNReal.measurable_ofReal.comp
          (measurable_const.sub (measurable_pi_apply i)))
  · apply Finset.measurable_prod
    intro p _hp
    exact ENNReal.continuous_rpow_const.measurable.comp
      (ENNReal.measurable_ofReal.comp
        ((measurable_pi_apply p.2).sub
          (measurable_pi_apply p.1)).abs)

theorem measurable_forresterEq17Kernel_literal
    (m : ℕ) (beta alpha : ℝ) :
    Measurable (forresterEq17Kernel m beta alpha) := by
  classical
  unfold forresterEq17Kernel
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro i _hi
    exact ENNReal.continuous_rpow_const.measurable.comp
      (ENNReal.measurable_ofReal.comp (measurable_pi_apply i))
  · apply Finset.measurable_prod
    intro p _hp
    exact ENNReal.continuous_rpow_const.measurable.comp
      (ENNReal.measurable_ofReal.comp
        (((measurable_pi_apply p.2).pow_const 2).sub
          ((measurable_pi_apply p.1).pow_const 2)).abs)

/-! ## Exact square chart on the open cube -/

theorem a2CoordinateSquare_image_openCube (m : ℕ) :
    a2CoordinateSquare m '' betaJacobiOpenCube m =
      betaJacobiOpenCube m := by
  ext u
  constructor
  · rintro ⟨rho, hrho, rfl⟩
    intro i
    have hi := hrho i
    change 0 < (rho i) ^ 2 ∧ (rho i) ^ 2 < 1
    constructor
    · exact sq_pos_of_pos hi.1
    · nlinarith [sq_nonneg (rho i), mul_lt_mul_of_pos_left hi.2 hi.1]
  · intro hu
    let rho : Fin m → ℝ := fun i ↦ Real.sqrt (u i)
    refine ⟨rho, ?_, ?_⟩
    · intro i
      have hi := hu i
      have hsquare : (Real.sqrt (u i)) ^ 2 = u i :=
        Real.sq_sqrt hi.1.le
      constructor
      · exact Real.sqrt_pos.2 hi.1
      · exact (Real.sqrt_lt' zero_lt_one).2 (by simpa using hi.2)
    · funext i
      exact Real.sq_sqrt (hu i).1.le

theorem a2CoordinateSquare_injOn_openCube (m : ℕ) :
    Set.InjOn (a2CoordinateSquare m) (betaJacobiOpenCube m) := by
  intro rho hrho sigma hsigma heq
  funext i
  have hr := hrho i
  have hs := hsigma i
  have hi := congrFun heq i
  dsimp [a2CoordinateSquare] at hi
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hi with hi | hi
  · exact hi
  · nlinarith [hr.1, hs.1]

/-- Change of variables `u_i=rho_i^2` restricted to `(0,1)^m`. -/
theorem lintegral_a2CoordinateSquare_openCube
    (m : ℕ) (f : (Fin m → ℝ) → ℝ≥0∞) :
    (∫⁻ u in betaJacobiOpenCube m, f u) =
      ∫⁻ rho in betaJacobiOpenCube m,
        ENNReal.ofReal (takagiRadiusSquareJacobian m rho) *
          f (a2CoordinateSquare m rho) := by
  calc
    (∫⁻ u in betaJacobiOpenCube m, f u) =
        ∫⁻ u in a2CoordinateSquare m '' betaJacobiOpenCube m, f u := by
      rw [a2CoordinateSquare_image_openCube]
    _ = ∫⁻ rho in betaJacobiOpenCube m,
        ENNReal.ofReal |(fderivTakagiRadiusSquareVector rho).det| *
          f (a2CoordinateSquare m rho) := by
      change (∫⁻ u in takagiRadiusSquareVector m ''
          betaJacobiOpenCube m, f u) =
        ∫⁻ rho in betaJacobiOpenCube m,
          ENNReal.ofReal |(fderivTakagiRadiusSquareVector rho).det| *
            f (takagiRadiusSquareVector m rho)
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
        (measurableSet_openUnitCube_h6 m)
        (fun rho _hrho ↦
          (hasFDerivAt_takagiRadiusSquareVector rho).hasFDerivWithinAt)
        (a2CoordinateSquare_injOn_openCube m)]
    _ = ∫⁻ rho in betaJacobiOpenCube m,
        ENNReal.ofReal (takagiRadiusSquareJacobian m rho) *
          f (a2CoordinateSquare m rho) := by
      refine setLIntegral_congr_fun (measurableSet_openUnitCube_h6 m)
        (fun rho hrho ↦ ?_)
      rw [det_fderivTakagiRadiusSquareVector]
      rw [abs_of_pos]
      exact takagiRadiusSquareJacobian_pos fun i ↦ (hrho i).1

theorem a2SquaringScale_mul_jacobian_eq_coordinateProduct
    {m : ℕ} {rho : Fin m → ℝ}
    (hrho : rho ∈ betaJacobiOpenCube m) :
    (a2SquaringScale m : ℝ≥0∞) *
        ENNReal.ofReal (takagiRadiusSquareJacobian m rho) =
      ∏ i : Fin m, ENNReal.ofReal (rho i) := by
  have hprod : 0 ≤ takagiRadiusProduct m rho :=
    takagiRadiusProduct_nonneg fun i ↦ (hrho i).1
  rw [takagiRadiusSquareJacobian_eq_two_pow_mul]
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ m)]
  rw [ENNReal.ofReal_pow (by positivity : 0 ≤ (2 : ℝ))]
  unfold takagiRadiusProduct
  rw [ENNReal.ofReal_prod_of_nonneg
    (fun i _hi ↦ (hrho i).1.le)]
  unfold a2SquaringScale
  rw [ENNReal.coe_inv
    (pow_ne_zero m (by norm_num : (2 : NNReal) ≠ 0))]
  have hcoe : ((((2 : NNReal) ^ m) : NNReal) : ℝ≥0∞) =
      (2 : ℝ≥0∞) ^ m := by norm_cast
  rw [hcoe]
  rw [show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by norm_num]
  calc
    ((2 : ℝ≥0∞) ^ m)⁻¹ *
          ((2 : ℝ≥0∞) ^ m *
            ∏ i : Fin m, ENNReal.ofReal (rho i)) =
        (((2 : ℝ≥0∞) ^ m)⁻¹ * (2 : ℝ≥0∞) ^ m) *
          ∏ i : Fin m, ENNReal.ofReal (rho i) := by ac_rfl
    _ = ∏ i : Fin m, ENNReal.ofReal (rho i) := by
      rw [ENNReal.inv_mul_cancel
        (pow_ne_zero m (by norm_num : (2 : ℝ≥0∞) ≠ 0))
        (by simp), one_mul]

theorem ennreal_ofReal_rpow_eq_mul_square_rpow
    {x alpha : ℝ} (hx : 0 < x) :
    (ENNReal.ofReal x).rpow alpha =
      ENNReal.ofReal x *
        (ENNReal.ofReal (x ^ 2)).rpow ((alpha - 1) / 2) := by
  let q : ℝ≥0∞ := ENNReal.ofReal x
  have hq0 : q ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr hx
  have hqtop : q ≠ ⊤ := by simp [q]
  have hsq : ENNReal.ofReal (x ^ 2) = q ^ 2 := by
    rw [ENNReal.ofReal_pow hx.le]
  have htwo : q ^ (2 : ℝ) = q ^ (2 : ℕ) :=
    ENNReal.rpow_natCast q 2
  change q ^ alpha = q * (ENNReal.ofReal (x ^ 2)) ^ ((alpha - 1) / 2)
  calc
    q ^ alpha = q ^ (1 + (alpha - 1)) := by
      congr 1
      ring
    _ = q ^ (1 : ℝ) * q ^ (alpha - 1) :=
      ENNReal.rpow_add 1 (alpha - 1) hq0 hqtop
    _ = q * q ^ (2 * ((alpha - 1) / 2)) := by
      congr 1
      · exact ENNReal.rpow_one q
      · congr 1
        ring
    _ = q * (q ^ (2 : ℝ)) ^ ((alpha - 1) / 2) := by
      rw [ENNReal.rpow_mul]
    _ = q * (q ^ (2 : ℕ)) ^ ((alpha - 1) / 2) := by
      rw [htwo]
    _ = q * (ENNReal.ofReal (x ^ 2)) ^ ((alpha - 1) / 2) := by
      rw [hsq]

/-- Pointwise beta-one square-Jacobian identity, including the exact global
factor `2^(-m)`. -/
theorem forresterEq17Kernel_beta_one_square_density
    {m : ℕ} {alpha : ℝ} {rho : Fin m → ℝ}
    (hrho : rho ∈ betaJacobiOpenCube m) :
    forresterEq17Kernel m 1 alpha rho =
      (a2SquaringScale m : ℝ≥0∞) *
        (ENNReal.ofReal (takagiRadiusSquareJacobian m rho) *
          betaJacobiKernel m (a2JacobiA 1 alpha)
            (a2JacobiB 1) 1 (a2CoordinateSquare m rho)) := by
  let V : ℝ≥0∞ :=
    ∏ p ∈ a2StrictPairs m,
      ENNReal.ofReal
        |(rho p.2) ^ 2 - (rho p.1) ^ 2|
  have ha : (a2JacobiA 1 alpha + 1) / 2 - 1 =
      (alpha - 1) / 2 := by
    norm_num [a2JacobiA]
    ring
  have hb : (a2JacobiB 1 + 1) / 2 - 1 = 0 := by
    norm_num [a2JacobiB]
  have hForrester : forresterEq17Kernel m 1 alpha rho =
      (∏ i : Fin m, (ENNReal.ofReal (rho i)).rpow alpha) * V := by
    simp [forresterEq17Kernel, V]
  have hJacobi : betaJacobiKernel m (a2JacobiA 1 alpha)
      (a2JacobiB 1) 1 (a2CoordinateSquare m rho) =
      (∏ i : Fin m,
        (ENNReal.ofReal ((rho i) ^ 2)).rpow ((alpha - 1) / 2)) * V := by
    simp [betaJacobiKernel, a2CoordinateSquare, ha, hb, V]
  have hcoordinates :
      (∏ i : Fin m, (ENNReal.ofReal (rho i)).rpow alpha) =
        (∏ i : Fin m, ENNReal.ofReal (rho i)) *
          ∏ i : Fin m,
            (ENNReal.ofReal ((rho i) ^ 2)).rpow ((alpha - 1) / 2) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _hi ↦
      ennreal_ofReal_rpow_eq_mul_square_rpow (hrho i).1
  rw [hForrester, hJacobi]
  calc
    (∏ i : Fin m, (ENNReal.ofReal (rho i)).rpow alpha) * V =
        ((∏ i : Fin m, ENNReal.ofReal (rho i)) *
          ∏ i : Fin m,
            (ENNReal.ofReal ((rho i) ^ 2)).rpow ((alpha - 1) / 2)) * V := by
      rw [hcoordinates]
    _ = (a2SquaringScale m : ℝ≥0∞) *
        (ENNReal.ofReal (takagiRadiusSquareJacobian m rho) *
          ((∏ i : Fin m,
            (ENNReal.ofReal ((rho i) ^ 2)).rpow ((alpha - 1) / 2)) * V)) := by
      rw [← a2SquaringScale_mul_jacobian_eq_coordinateProduct hrho]
      ac_rfl

/-- The raw A2 beta-one law pushes exactly to beta-Jacobi, with no remaining
square-coordinate contract. -/
theorem map_forresterEq17RawMeasure_beta_one
    (m : ℕ) (alpha : ℝ) :
    Measure.map (a2CoordinateSquare m)
        (forresterEq17RawMeasure m 1 alpha) =
      (a2SquaringScale m : ℝ≥0∞) •
        betaJacobiRawMeasure m (a2JacobiA 1 alpha)
          (a2JacobiB 1) 1 := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg (measurable_a2CoordinateSquare m)]
  unfold forresterEq17RawMeasure
  change (∫⁻ a, (g ∘ a2CoordinateSquare m) a ∂
      (volume.restrict (betaJacobiOpenCube m)).withDensity
        (forresterEq17Kernel m 1 alpha)) = _
  rw [lintegral_withDensity_eq_lintegral_mul₀
    (measurable_forresterEq17Kernel_literal m 1 alpha).aemeasurable
    ((hg.comp (measurable_a2CoordinateSquare m)).aemeasurable)]
  rw [lintegral_smul_measure]
  unfold betaJacobiRawMeasure
  rw [lintegral_withDensity_eq_lintegral_mul₀
    (measurable_betaJacobiKernel_literal m
      (a2JacobiA 1 alpha) (a2JacobiB 1) 1).aemeasurable
    hg.aemeasurable]
  change (∫⁻ rho in betaJacobiOpenCube m,
      forresterEq17Kernel m 1 alpha rho *
        g (a2CoordinateSquare m rho)) =
    (a2SquaringScale m : ℝ≥0∞) *
      ∫⁻ u in betaJacobiOpenCube m,
        betaJacobiKernel m (a2JacobiA 1 alpha)
          (a2JacobiB 1) 1 u * g u
  rw [lintegral_a2CoordinateSquare_openCube m
    (fun u ↦ betaJacobiKernel m (a2JacobiA 1 alpha)
      (a2JacobiB 1) 1 u * g u)]
  have hmeas : Measurable (fun rho : Fin m → ℝ ↦
      ENNReal.ofReal (takagiRadiusSquareJacobian m rho) *
        (betaJacobiKernel m (a2JacobiA 1 alpha)
          (a2JacobiB 1) 1 (a2CoordinateSquare m rho) *
            g (a2CoordinateSquare m rho))) :=
    (ENNReal.measurable_ofReal.comp
      (measurable_takagiRadiusSquareJacobian m)).mul
      (((measurable_betaJacobiKernel_literal m
        (a2JacobiA 1 alpha) (a2JacobiB 1) 1).comp
          (measurable_a2CoordinateSquare m)).mul
        (hg.comp (measurable_a2CoordinateSquare m)))
  rw [← lintegral_const_mul
    (μ := volume.restrict (betaJacobiOpenCube m))
    (a2SquaringScale m : ℝ≥0∞) hmeas]
  refine setLIntegral_congr_fun (measurableSet_openUnitCube_h6 m)
    (fun rho hrho ↦ ?_)
  rw [forresterEq17Kernel_beta_one_square_density hrho]
  ac_rfl

/-- The formerly conditional beta-one squaring contract is inhabited. -/
def forresterEq17RawSquaringContract_beta_one
    (m : ℕ) (alpha : ℝ) :
    ForresterEq17RawSquaringContract m 1 alpha where
  raw_square := map_forresterEq17RawMeasure_beta_one m alpha

theorem forresterEq17Normalization_beta_one_square
    (m : ℕ) (alpha : ℝ) :
    forresterEq17Normalization m 1 alpha =
      (a2SquaringScale m : ℝ≥0∞) *
        betaJacobiNormalization m (a2JacobiA 1 alpha)
          (a2JacobiB 1) 1 :=
  (forresterEq17RawSquaringContract_beta_one m alpha).normalization_square

theorem forresterEq17Probability_beta_one_square
    (m : ℕ) (alpha : ℝ) :
    Measure.map (a2CoordinateSquare m)
        (forresterEq17ProbabilityMeasure m 1 alpha) =
      betaJacobiProbabilityMeasure m (a2JacobiA 1 alpha)
        (a2JacobiB 1) 1 :=
  (forresterEq17RawSquaringContract_beta_one m alpha).probability_square

/-! ## Reflection, including base-volume preservation -/

theorem betaJacobiKernel_reflection
    (m : ℕ) (a b beta : ℝ) (u : Fin m → ℝ) :
    betaJacobiKernel m a b beta u =
      betaJacobiKernel m b a beta (a2CoordinateReflection m u) := by
  classical
  unfold betaJacobiKernel a2CoordinateReflection
  congr 1
  · apply Finset.prod_congr rfl
    intro i _hi
    rw [show 1 - (1 - u i) = u i by ring]
    ac_rfl
  · apply Finset.prod_congr rfl
    intro p _hp
    congr 1
    rw [show (1 - u p.2) - (1 - u p.1) =
      -(u p.2 - u p.1) by ring, abs_neg]

theorem map_a2CoordinateReflection_volume (m : ℕ) :
    Measure.map (a2CoordinateReflection m)
        (volume : Measure (Fin m → ℝ)) = volume := by
  let oneVector : Fin m → ℝ := fun _ ↦ 1
  calc
    Measure.map (a2CoordinateReflection m)
        (volume : Measure (Fin m → ℝ)) =
      Measure.map (fun u : Fin m → ℝ ↦ oneVector + u)
        (Measure.map (fun u : Fin m → ℝ ↦ -u) volume) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          congr 1
    _ = Measure.map (fun u : Fin m → ℝ ↦ oneVector + u) volume := by
      rw [Measure.map_neg_eq_self]
    _ = volume :=
      Measure.IsAddLeftInvariant.map_add_left_eq_self oneVector

theorem a2CoordinateReflection_preimage_openCube (m : ℕ) :
    a2CoordinateReflection m ⁻¹' betaJacobiOpenCube m =
      betaJacobiOpenCube m := by
  ext u
  exact a2CoordinateReflection_mem_openCube_iff

theorem map_a2CoordinateReflection_restrict_openCube (m : ℕ) :
    Measure.map (a2CoordinateReflection m)
        (volume.restrict (betaJacobiOpenCube m)) =
      volume.restrict (betaJacobiOpenCube m) := by
  conv_lhs =>
    rw [← a2CoordinateReflection_preimage_openCube m]
  rw [← Measure.restrict_map (measurable_a2CoordinateReflection m)
    (measurableSet_openUnitCube_h6 m)]
  rw [map_a2CoordinateReflection_volume]

theorem map_betaJacobiRawMeasure_reflection
    (m : ℕ) (a b beta : ℝ) :
    Measure.map (a2CoordinateReflection m)
        (betaJacobiRawMeasure m a b beta) =
      betaJacobiRawMeasure m b a beta := by
  unfold betaJacobiRawMeasure
  rw [show betaJacobiKernel m a b beta =
      betaJacobiKernel m b a beta ∘ a2CoordinateReflection m by
    funext u
    exact betaJacobiKernel_reflection m a b beta u]
  rw [H6RadialMeasureAdapters.map_withDensity_comp
    (volume.restrict (betaJacobiOpenCube m))
    (a2CoordinateReflection m) (betaJacobiKernel m b a beta)
    (measurable_a2CoordinateReflection m)
    (measurable_betaJacobiKernel_literal m b a beta).aemeasurable]
  rw [map_a2CoordinateReflection_restrict_openCube]

/-- The formerly conditional reflection contract is inhabited for all literal
parameters. -/
def betaJacobiRawReflectionContract_proved
    (m : ℕ) (a b beta : ℝ) :
    BetaJacobiRawReflectionContract m a b beta where
  raw_reflection := map_betaJacobiRawMeasure_reflection m a b beta

theorem betaJacobiNormalization_reflection_proved
    (m : ℕ) (a b beta : ℝ) :
    betaJacobiNormalization m a b beta =
      betaJacobiNormalization m b a beta :=
  (betaJacobiRawReflectionContract_proved m a b beta).normalization_reflection

theorem betaJacobiProbability_reflection_proved
    (m : ℕ) (a b beta : ℝ) :
    Measure.map (a2CoordinateReflection m)
        (betaJacobiProbabilityMeasure m a b beta) =
      betaJacobiProbabilityMeasure m b a beta :=
  (betaJacobiRawReflectionContract_proved m a b beta).probability_reflection

/-! ## Collision-nullity from proper linear hyperplanes -/

def a2CollisionLinearMap {n : ℕ} (i j : Fin n) :
    (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ) -
    (LinearMap.proj j : (Fin n → ℝ) →ₗ[ℝ] ℝ)

theorem volume_a2CollisionHyperplane_zero
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    volume {u : Fin n → ℝ | u i = u j} = 0 := by
  rw [show {u : Fin n → ℝ | u i = u j} =
      (LinearMap.ker (a2CollisionLinearMap i j) : Set (Fin n → ℝ)) by
    ext u
    simp [a2CollisionLinearMap, sub_eq_zero]]
  apply Measure.addHaar_submodule (volume : Measure (Fin n → ℝ))
  rw [Ne, LinearMap.ker_eq_top]
  intro hzero
  let e : Fin n → ℝ := fun k ↦ if k = i then 1 else 0
  have heval : a2CollisionLinearMap i j e = 1 := by
    simp [a2CollisionLinearMap, e, hij, Ne.symm hij]
  have hzeroeval : a2CollisionLinearMap i j e = 0 := by
    rw [hzero]
    rfl
  linarith

theorem volume_betaJacobiCollisionSet_zero (n : ℕ) :
    volume (betaJacobiCollisionSet n) = 0 := by
  let I := {p : Fin n × Fin n // p.1 ≠ p.2}
  let H : I → Set (Fin n → ℝ) := fun p ↦
    {u | u p.1.1 = u p.1.2}
  have hsubset : betaJacobiCollisionSet n ⊆ ⋃ p : I, H p := by
    rintro u ⟨i, j, hij, heq⟩
    refine Set.mem_iUnion.2 ⟨⟨(i, j), hij⟩, ?_⟩
    exact heq
  apply measure_mono_null hsubset
  apply measure_iUnion_null
  intro p
  exact volume_a2CollisionHyperplane_zero p.2

/-- The collision-volume contract is now inhabited. -/
def betaJacobiCollisionVolumeContract_proved (n : ℕ) :
    BetaJacobiCollisionVolumeContract n where
  volume_collision := volume_betaJacobiCollisionSet_zero n

theorem betaJacobi_collision_null_proved
    (n : ℕ) (a b beta : ℝ) :
    betaJacobiProbabilityMeasure n a b beta
        (betaJacobiCollisionSet n) = 0 :=
  (betaJacobiCollisionVolumeContract_proved n).betaJacobi_collision_null
    a b beta

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore


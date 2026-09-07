import LogdetLean.GramHafnian.ShiftedAnticoncentration.GaussianGamma
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.RadialScalarBounds
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Probability.Independence.Integration

/-!
# Moment factorization for independent radial and angular variables

This module is the probability-algebra layer of the radial lower bound.  It
does not use the hafnian or Gaussian polar decomposition.  Its hypotheses say
exactly that the radii have rate-one Gamma laws, are mutually independent,
and that their product is independent of a positive angular energy.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian

noncomputable section

/-- Exact first moment of a rate-one Gamma law. -/
theorem integral_id_gammaMeasure_one {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ, x ∂gammaMeasure a 1 = a := by
  have hmellin := LogdetLean.integral_rpow_gammaMeasure
    (a := a) (r := 1) (t := 1) ha (by norm_num) (by linarith)
  have hgamma : Real.Gamma (a + 1) = a * Real.Gamma a :=
    Real.Gamma_add_one ha.ne'
  have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  calc
    (∫ x : ℝ, x ∂gammaMeasure a 1) = a * Real.Gamma a / Real.Gamma a := by
      simpa only [Real.rpow_one, neg_one_mul, Real.one_rpow, one_mul, hgamma] using hmellin
    _ = a := by field_simp

/-- Integrability of the identity under a positive-shape rate-one Gamma law. -/
theorem integrable_id_gammaMeasure_one {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ ↦ x) (gammaMeasure a 1) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_id_gammaMeasure_one ha]
  exact ha.ne'

/-- The product of `d` rate-one Gamma variables of shape `k` has first moment
`k^d` under the canonical finite product measure. -/
theorem integral_gammaRadialProduct
    (k : ℕ) (hk : 0 < k) (d : ℕ) :
    ∫ r : Fin d → ℝ, ∏ i, r i
        ∂Measure.pi (fun _ : Fin d ↦ gammaMeasure (k : ℝ) 1) = (k : ℝ) ^ d := by
  let _ : ∀ _ : Fin d, IsProbabilityMeasure (gammaMeasure (k : ℝ) 1) :=
    fun _ ↦ isProbabilityMeasure_gammaMeasure
      (show (0 : ℝ) < k by exact_mod_cast hk) (by norm_num)
  rw [integral_fintype_prod_eq_prod (fun _ : Fin d ↦ fun x : ℝ ↦ x)]
  simp_rw [integral_id_gammaMeasure_one (show (0 : ℝ) < k by exact_mod_cast hk)]
  simp

/-- The inverse of the product of `d` rate-one Gamma variables of integer
shape `k ≥ 2` has first moment `(k-1)^{-d}`. -/
theorem integral_inv_gammaRadialProduct
    (k : ℕ) (hk : 2 ≤ k) (d : ℕ) :
    ∫ r : Fin d → ℝ, (∏ i, r i)⁻¹
        ∂Measure.pi (fun _ : Fin d ↦ gammaMeasure (k : ℝ) 1) =
      (((k : ℝ) - 1)⁻¹) ^ d := by
  have hshape : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (show 1 < k by omega)
  let _ : ∀ _ : Fin d, IsProbabilityMeasure (gammaMeasure (k : ℝ) 1) :=
    fun _ ↦ isProbabilityMeasure_gammaMeasure (by linarith) (by norm_num)
  simp_rw [← Finset.prod_inv_distrib]
  rw [integral_fintype_prod_eq_prod (fun _ : Fin d ↦ fun x : ℝ ↦ x⁻¹)]
  simp_rw [integral_inv_gammaMeasure_one hshape]
  simp

/-- Integrability of the radial product. -/
theorem integrable_gammaRadialProduct
    (k : ℕ) (hk : 0 < k) (d : ℕ) :
    Integrable (fun r : Fin d → ℝ ↦ ∏ i, r i)
      (Measure.pi (fun _ : Fin d ↦ gammaMeasure (k : ℝ) 1)) := by
  let _ : ∀ _ : Fin d, IsProbabilityMeasure (gammaMeasure (k : ℝ) 1) :=
    fun _ ↦ isProbabilityMeasure_gammaMeasure
      (show (0 : ℝ) < k by exact_mod_cast hk) (by norm_num)
  apply Integrable.fintype_prod (f := fun _ : Fin d ↦ fun x : ℝ ↦ x)
  intro i
  exact integrable_id_gammaMeasure_one (show (0 : ℝ) < k by exact_mod_cast hk)

/-- Integrability of the inverse radial product for integer shape `k ≥ 2`. -/
theorem integrable_inv_gammaRadialProduct
    (k : ℕ) (hk : 2 ≤ k) (d : ℕ) :
    Integrable (fun r : Fin d → ℝ ↦ (∏ i, r i)⁻¹)
      (Measure.pi (fun _ : Fin d ↦ gammaMeasure (k : ℝ) 1)) := by
  have hshape : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (show 1 < k by omega)
  let _ : ∀ _ : Fin d, IsProbabilityMeasure (gammaMeasure (k : ℝ) 1) :=
    fun _ ↦ isProbabilityMeasure_gammaMeasure (by linarith) (by norm_num)
  simp_rw [← Finset.prod_inv_distrib]
  apply Integrable.fintype_prod (f := fun _ : Fin d ↦ fun x : ℝ ↦ x⁻¹)
  intro i
  exact integrable_inv_gammaMeasure_one hshape

/-- Cauchy--Schwarz for a positive random variable: its first moment times its
inverse first moment is at least one. -/
theorem one_le_integral_mul_integral_inv
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (W : Omega → ℝ)
    (hWmeas : AEStronglyMeasurable W mu)
    (hWpos : ∀ᵐ w ∂mu, 0 < W w)
    (hW : Integrable W mu)
    (hWinv : Integrable (fun w ↦ (W w)⁻¹) mu) :
    1 ≤ (∫ w, W w ∂mu) * ∫ w, (W w)⁻¹ ∂mu := by
  let f : Omega → ℝ := fun w ↦ Real.sqrt (W w)
  let g : Omega → ℝ := fun w ↦ Real.sqrt ((W w)⁻¹)
  have hfmeas : AEStronglyMeasurable f mu :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hWmeas
  have hgmeas : AEStronglyMeasurable g mu :=
    Real.continuous_sqrt.comp_aestronglyMeasurable
      hWmeas.aemeasurable.inv.aestronglyMeasurable
  have hfsq : Integrable (fun w ↦ f w ^ 2) mu := by
    apply hW.congr
    filter_upwards [hWpos] with w hw
    exact (Real.sq_sqrt hw.le).symm
  have hgsq : Integrable (fun w ↦ g w ^ 2) mu := by
    apply hWinv.congr
    filter_upwards [hWpos] with w hw
    exact (Real.sq_sqrt (inv_nonneg.mpr hw.le)).symm
  have hfLp : MemLp f 2 mu :=
    (memLp_two_iff_integrable_sq hfmeas).2 hfsq
  have hgLp : MemLp g 2 mu :=
    (memLp_two_iff_integrable_sq hgmeas).2 hgsq
  have hfLp' : MemLp f (ENNReal.ofReal (2 : ℝ)) mu := by simpa using hfLp
  have hgLp' : MemLp g (ENNReal.ofReal (2 : ℝ)) mu := by simpa using hgLp
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (f := f) (g := g) hholder
    (ae_of_all mu fun w ↦ Real.sqrt_nonneg _)
    (ae_of_all mu fun w ↦ Real.sqrt_nonneg _) hfLp' hgLp'
  have hfg : (∫ w, f w * g w ∂mu) = 1 := by
    calc
      (∫ w, f w * g w ∂mu) = ∫ _w, (1 : ℝ) ∂mu := by
        apply integral_congr_ae
        filter_upwards [hWpos] with w hw
        rw [show f w = Real.sqrt (W w) by rfl,
          show g w = Real.sqrt ((W w)⁻¹) by rfl,
          ← Real.sqrt_mul hw.le, mul_inv_cancel₀ hw.ne', Real.sqrt_one]
      _ = 1 := by simp
  have hfint : (∫ w, f w ^ (2 : ℝ) ∂mu) = ∫ w, W w ∂mu := by
    simp_rw [Real.rpow_two]
    apply integral_congr_ae
    filter_upwards [hWpos] with w hw
    exact Real.sq_sqrt hw.le
  have hgint : (∫ w, g w ^ (2 : ℝ) ∂mu) = ∫ w, (W w)⁻¹ ∂mu := by
    simp_rw [Real.rpow_two]
    apply integral_congr_ae
    filter_upwards [hWpos] with w hw
    exact Real.sq_sqrt (inv_nonneg.mpr hw.le)
  rw [hfg, hfint, hgint] at hcs
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hcs
  have hEW : 0 ≤ ∫ w, W w ∂mu :=
    integral_nonneg_of_ae (hWpos.mono fun _ hw ↦ hw.le)
  have hEWinv : 0 ≤ ∫ w, (W w)⁻¹ ∂mu :=
    integral_nonneg_of_ae (hWpos.mono fun _ hw ↦ inv_nonneg.mpr hw.le)
  have hsquare := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hcs 2
  rw [one_pow, mul_pow, Real.sq_sqrt hEW, Real.sq_sqrt hEWinv] at hsquare
  exact hsquare

/-- Product of a finite family of radial variables. -/
def radialProduct {Omega : Type*} {d : ℕ} (R : Fin d → Omega → ℝ) (w : Omega) : ℝ :=
  ∏ i, R i w

/-- Energy obtained by multiplying a radial product and an angular energy. -/
def radialAngularEnergy {Omega : Type*} {d : ℕ}
    (R : Fin d → Omega → ℝ) (W : Omega → ℝ) (w : Omega) : ℝ :=
  radialProduct R w * W w

/-- Exact first moment of mutually independent rate-one Gamma radii. -/
theorem integral_radialProduct_eq_pow
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {d k : ℕ} (hk : 0 < k)
    (R : Fin d → Omega → ℝ)
    (hRmeas : ∀ i, Measurable (R i))
    (hRind : iIndepFun R mu)
    (hRlaw : ∀ i, mu.map (R i) = gammaMeasure (k : ℝ) 1) :
    ∫ w, radialProduct R w ∂mu = (k : ℝ) ^ d := by
  have hRi : ∀ i, (∫ w, R i w ∂mu) = (k : ℝ) := by
    intro i
    calc
      (∫ w, R i w ∂mu) = ∫ x : ℝ, x ∂mu.map (R i) := by
        symm
        exact integral_map (hRmeas i).aemeasurable aestronglyMeasurable_id
      _ = ∫ x : ℝ, x ∂gammaMeasure (k : ℝ) 1 := by rw [hRlaw i]
      _ = (k : ℝ) :=
        integral_id_gammaMeasure_one (show (0 : ℝ) < k by exact_mod_cast hk)
  calc
    (∫ w, radialProduct R w ∂mu) = ∏ i, ∫ w, R i w ∂mu := by
      exact hRind.integral_fun_prod_eq_prod_integral
        (fun i ↦ (hRmeas i).aestronglyMeasurable)
    _ = (k : ℝ) ^ d := by simp_rw [hRi]; simp

/-- Exact inverse first moment of mutually independent rate-one Gamma radii. -/
theorem integral_inv_radialProduct_eq_pow
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {d k : ℕ} (hk : 2 ≤ k)
    (R : Fin d → Omega → ℝ)
    (hRmeas : ∀ i, Measurable (R i))
    (hRind : iIndepFun R mu)
    (hRlaw : ∀ i, mu.map (R i) = gammaMeasure (k : ℝ) 1) :
    ∫ w, (radialProduct R w)⁻¹ ∂mu = (((k : ℝ) - 1)⁻¹) ^ d := by
  have hshape : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (show 1 < k by omega)
  have hRi : ∀ i, (∫ w, (R i w)⁻¹ ∂mu) = ((k : ℝ) - 1)⁻¹ := by
    intro i
    calc
      (∫ w, (R i w)⁻¹ ∂mu) = ∫ x : ℝ, x⁻¹ ∂mu.map (R i) := by
        symm
        exact integral_map (hRmeas i).aemeasurable
          aestronglyMeasurable_id.aemeasurable.inv.aestronglyMeasurable
      _ = ∫ x : ℝ, x⁻¹ ∂gammaMeasure (k : ℝ) 1 := by rw [hRlaw i]
      _ = ((k : ℝ) - 1)⁻¹ := integral_inv_gammaMeasure_one hshape
  have hRinvInd : iIndepFun (fun i ↦ (R i)⁻¹) mu :=
    hRind.comp (fun _ ↦ fun x : ℝ ↦ x⁻¹) (fun _ ↦ measurable_id.inv)
  calc
    (∫ w, (radialProduct R w)⁻¹ ∂mu) =
        ∫ w, ∏ i, (R i w)⁻¹ ∂mu := by
      apply integral_congr_ae
      exact ae_of_all mu fun w ↦ (Finset.prod_inv_distrib fun i ↦ R i w).symm
    _ = ∏ i, ∫ w, (R i w)⁻¹ ∂mu := by
      exact hRinvInd.integral_fun_prod_eq_prod_integral
        (fun i ↦ (hRmeas i).aemeasurable.inv.aestronglyMeasurable)
    _ = (((k : ℝ) - 1)⁻¹) ^ d := by simp_rw [hRi]; simp

/-- Exact first-moment factorization when the angular energy is independent of
the radial product. -/
theorem integral_radialAngularEnergy
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {d k : ℕ} (hk : 0 < k)
    (R : Fin d → Omega → ℝ) (W : Omega → ℝ)
    (hRmeas : ∀ i, Measurable (R i)) (hWmeas : Measurable W)
    (hRind : iIndepFun R mu)
    (hRlaw : ∀ i, mu.map (R i) = gammaMeasure (k : ℝ) 1)
    (hRW : IndepFun (radialProduct R) W mu) :
    ∫ w, radialAngularEnergy R W w ∂mu =
      (k : ℝ) ^ d * ∫ w, W w ∂mu := by
  rw [show (∫ w, radialAngularEnergy R W w ∂mu) =
      (∫ w, radialProduct R w ∂mu) * ∫ w, W w ∂mu by
    exact hRW.integral_fun_mul_eq_mul_integral
      (Finset.univ.measurable_prod fun i _ ↦ hRmeas i).aestronglyMeasurable
      hWmeas.aestronglyMeasurable]
  rw [integral_radialProduct_eq_pow mu hk R hRmeas hRind hRlaw]

/-- Exact inverse-moment factorization for radial times angular energy. -/
theorem integral_inv_radialAngularEnergy
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {d k : ℕ} (hk : 2 ≤ k)
    (R : Fin d → Omega → ℝ) (W : Omega → ℝ)
    (hRmeas : ∀ i, Measurable (R i)) (hWmeas : Measurable W)
    (hRind : iIndepFun R mu)
    (hRlaw : ∀ i, mu.map (R i) = gammaMeasure (k : ℝ) 1)
    (hRW : IndepFun (radialProduct R) W mu) :
    ∫ w, (radialAngularEnergy R W w)⁻¹ ∂mu =
      (((k : ℝ) - 1)⁻¹) ^ d * ∫ w, (W w)⁻¹ ∂mu := by
  have hRprodMeas : Measurable (radialProduct R) :=
    Finset.univ.measurable_prod fun i _ ↦ hRmeas i
  have hinvInd := hRW.comp measurable_inv measurable_inv
  change IndepFun (fun w ↦ (radialProduct R w)⁻¹) (fun w ↦ (W w)⁻¹) mu at hinvInd
  calc
    (∫ w, (radialAngularEnergy R W w)⁻¹ ∂mu) =
        ∫ w, (radialProduct R w)⁻¹ * (W w)⁻¹ ∂mu := by
      apply integral_congr_ae
      exact ae_of_all mu fun w ↦ by simp [radialAngularEnergy, mul_inv_rev, mul_comm]
    _ = (∫ w, (radialProduct R w)⁻¹ ∂mu) * ∫ w, (W w)⁻¹ ∂mu := by
      exact hinvInd.integral_fun_mul_eq_mul_integral
        hRprodMeas.aemeasurable.inv.aestronglyMeasurable
        hWmeas.aemeasurable.inv.aestronglyMeasurable
    _ = (((k : ℝ) - 1)⁻¹) ^ d * ∫ w, (W w)⁻¹ ∂mu := by
      rw [integral_inv_radialProduct_eq_pow mu hk R hRmeas hRind hRlaw]

/-- Exact product of the first and inverse first moments.  This displays the
radial factor and the remaining angular factor separately. -/
theorem radialAngularEnergy_momentProduct_eq
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {d k : ℕ} (hk : 2 ≤ k)
    (R : Fin d → Omega → ℝ) (W : Omega → ℝ)
    (hRmeas : ∀ i, Measurable (R i)) (hWmeas : Measurable W)
    (hRind : iIndepFun R mu)
    (hRlaw : ∀ i, mu.map (R i) = gammaMeasure (k : ℝ) 1)
    (hRW : IndepFun (radialProduct R) W mu) :
    (∫ w, radialAngularEnergy R W w ∂mu) *
        (∫ w, (radialAngularEnergy R W w)⁻¹ ∂mu) =
      (((k : ℝ) / ((k : ℝ) - 1)) ^ d) *
        ((∫ w, W w ∂mu) * ∫ w, (W w)⁻¹ ∂mu) := by
  rw [integral_radialAngularEnergy mu (show 0 < k by omega) R W hRmeas hWmeas hRind hRlaw hRW,
    integral_inv_radialAngularEnergy mu hk R W hRmeas hWmeas hRind hRlaw hRW]
  rw [div_eq_mul_inv, mul_pow]
  ring

/-- The radial contribution alone is a rigorous lower bound for the product
of first and inverse first moments. -/
theorem radialFactor_le_radialAngularEnergy_momentProduct
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {d k : ℕ} (hk : 2 ≤ k)
    (R : Fin d → Omega → ℝ) (W : Omega → ℝ)
    (hRmeas : ∀ i, Measurable (R i)) (hWmeas : Measurable W)
    (hRind : iIndepFun R mu)
    (hRlaw : ∀ i, mu.map (R i) = gammaMeasure (k : ℝ) 1)
    (hRW : IndepFun (radialProduct R) W mu)
    (hWpos : ∀ᵐ w ∂mu, 0 < W w)
    (hW : Integrable W mu)
    (hWinv : Integrable (fun w ↦ (W w)⁻¹) mu) :
    ((k : ℝ) / ((k : ℝ) - 1)) ^ d ≤
      (∫ w, radialAngularEnergy R W w ∂mu) *
        ∫ w, (radialAngularEnergy R W w)⁻¹ ∂mu := by
  rw [radialAngularEnergy_momentProduct_eq mu hk R W hRmeas hWmeas hRind hRlaw hRW]
  apply le_mul_of_one_le_right
  · apply pow_nonneg
    apply div_nonneg
    · positivity
    · have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
  · exact one_le_integral_mul_integral_inv mu W hWmeas.aestronglyMeasurable
      hWpos hW hWinv

/-- Cofactor-indexed specialization of the generic radial lower bound. -/
theorem cofactorRadialFactor_le_radialAngularEnergy_momentProduct
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {n k : ℕ} (hk : 2 ≤ k)
    (R : Fin (2 * n - 1) → Omega → ℝ) (W : Omega → ℝ)
    (hRmeas : ∀ i, Measurable (R i)) (hWmeas : Measurable W)
    (hRind : iIndepFun R mu)
    (hRlaw : ∀ i, mu.map (R i) = gammaMeasure (k : ℝ) 1)
    (hRW : IndepFun (radialProduct R) W mu)
    (hWpos : ∀ᵐ w ∂mu, 0 < W w)
    (hW : Integrable W mu)
    (hWinv : Integrable (fun w ↦ (W w)⁻¹) mu) :
    cofactorRadialFactor k n ≤
      (∫ w, radialAngularEnergy R W w ∂mu) *
        ∫ w, (radialAngularEnergy R W w)⁻¹ ∂mu := by
  exact radialFactor_le_radialAngularEnergy_momentProduct
    mu hk R W hRmeas hWmeas hRind hRlaw hRW hWpos hW hWinv

/-- The explicit `exp(n/k)` lower bound after the probability-algebra layer.
The Gaussian polar module can instantiate this theorem once it supplies the
radial laws, mutual independence, and the positive angular energy. -/
theorem exp_n_div_le_radialAngularEnergy_momentProduct
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (R : Fin (2 * n - 1) → Omega → ℝ) (W : Omega → ℝ)
    (hRmeas : ∀ i, Measurable (R i)) (hWmeas : Measurable W)
    (hRind : iIndepFun R mu)
    (hRlaw : ∀ i, mu.map (R i) = gammaMeasure (k : ℝ) 1)
    (hRW : IndepFun (radialProduct R) W mu)
    (hWpos : ∀ᵐ w ∂mu, 0 < W w)
    (hW : Integrable W mu)
    (hWinv : Integrable (fun w ↦ (W w)⁻¹) mu) :
    Real.exp ((n : ℝ) / (k : ℝ)) ≤
      (∫ w, radialAngularEnergy R W w ∂mu) *
        ∫ w, (radialAngularEnergy R W w)⁻¹ ∂mu := by
  exact (exp_n_div_le_cofactorRadialFactor k n hn hk).trans
    (cofactorRadialFactor_le_radialAngularEnergy_momentProduct
      mu hk R W hRmeas hWmeas hRind hRlaw hRW hWpos hW hWinv)

end

end LogdetLean.GramHafnian

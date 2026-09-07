import LogdetLean.GaussianSphereDirection
import LogdetLean.Coherence.GaussianNormDirectionIndependence
import LogdetLean.GramHafnian.UltimateHiding.CircularGaussianBridge
import LogdetLean.GramHafnian.RankOneGaussianBilinear
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalCOEExternal
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic

/-!
# Low-order complex-projective tensor moments from Gaussian polar coordinates

This file proves the projective tensor identity needed by the headline
argument in orders at most four.  It uses only the literal circular Gaussian,
the already-proved Gaussian polar decomposition, and finite permutation
counting.  In particular it does not use the external general-order
Collins--Sniady tensor identity.
-/

open scoped BigOperators ComplexConjugate ENNReal RealInnerProductSpace
open MeasureTheory ProbabilityTheory Metric

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.UltimateHiding.Dense

private theorem dimensionProduct_two (r : ℕ) :
    dimensionProduct 2 r = (2 : ℝ) ^ r * (r.factorial : ℝ) := by
  induction r with
  | zero => simp [dimensionProduct]
  | succ r ih =>
      rw [dimensionProduct_succ, ih, Nat.factorial_succ, pow_succ]
      push_cast
      ring

private theorem complex_mul_conj_pow_eq_norm_pow (z : ℂ) (r : ℕ) :
    z ^ r * conj z ^ r = ((‖z‖ ^ (2 * r) : ℝ) : ℂ) := by
  rw [← mul_pow, Complex.mul_conj]
  norm_cast
  rw [← Complex.sq_norm]
  exact (pow_mul ‖z‖ 2 r).symm

/-- Balanced moments of the literal standard circular complex Gaussian. -/
theorem integral_pow_mul_conj_pow_circularGaussian_internal (r : ℕ) :
    (∫ z : ℂ, z ^ r * conj z ^ r ∂circularGaussian) =
      (r.factorial : ℂ) := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun z ↦
    complex_mul_conj_pow_eq_norm_pow z r)]
  rw [circularGaussian_eq_map_smul_stdGaussian,
    integral_map (by fun_prop) (by fun_prop)]
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hnorm (z : ℂ) :
      ‖((Real.sqrt 2)⁻¹ : ℝ) • z‖ ^ (2 * r) =
        (Real.sqrt 2)⁻¹ ^ (2 * r) * ‖z‖ ^ (2 * r) := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hsqrt_pos,
      mul_pow]
  simp_rw [hnorm]
  rw [show (fun x : ℂ ↦
      (((Real.sqrt 2)⁻¹ ^ (2 * r) * ‖x‖ ^ (2 * r) : ℝ) : ℂ)) =
      fun x : ℂ ↦ (((Real.sqrt 2)⁻¹ ^ (2 * r) : ℝ) : ℂ) *
        ((‖x‖ ^ (2 * r) : ℝ) : ℂ) by
    funext x
    norm_num]
  rw [integral_const_mul, integral_complex_ofReal]
  rw [integral_norm_pow_two_mul_stdGaussian (E := ℂ) r]
  rw [show Module.finrank ℝ ℂ = 2 by simp, dimensionProduct_two]
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_sq_complex : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    exact_mod_cast hsqrt_sq
  have hsqrt_ne : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  norm_cast <;> push_cast
  rw [inv_pow, pow_mul, hsqrt_sq]
  field_simp

/-- Multiplication by a unit scalar preserves the literal circular law. -/
private theorem measurePreserving_circularGaussian_mul_internal
    (c : ℂ) (hc : ‖c‖ = 1) :
    MeasurePreserving (fun z : ℂ ↦ c * z)
      circularGaussian circularGaussian := by
  let u : Circle := ⟨c, by
    change c ∈ sphere (0 : ℂ) 1
    simpa [mem_sphere] using hc⟩
  let R : ℂ ≃ₗᵢ[ℝ] ℂ := rotation u
  have hR : (stdGaussian ℂ).map R = stdGaussian ℂ := stdGaussian_map R
  refine ⟨by fun_prop, ?_⟩
  rw [circularGaussian_eq_map_smul_stdGaussian]
  let s : ℝ := (Real.sqrt 2)⁻¹
  calc
    ((stdGaussian ℂ).map (fun z : ℂ ↦ s • z)).map
        (fun z : ℂ ↦ c * z) =
        (stdGaussian ℂ).map
          ((fun z : ℂ ↦ c * z) ∘ (fun z : ℂ ↦ s • z)) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
    _ = (stdGaussian ℂ).map ((fun z : ℂ ↦ s • z) ∘ R) := by
          congr 1
          funext z
          change c * ((s : ℂ) * z) = (s : ℂ) * (R z)
          rw [show R z = c * z by rfl]
          ring
    _ = ((stdGaussian ℂ).map R).map (fun z : ℂ ↦ s • z) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
    _ = (stdGaussian ℂ).map (fun z : ℂ ↦ s • z) := by rw [hR]

private theorem integral_mixedComplexMonomial_eq_phase_mul
    (a b : ℕ) (c : ℂ) (hc : ‖c‖ = 1) :
    (∫ z, mixedComplexMonomial a b z ∂circularGaussian) =
      (c ^ a * conj c ^ b) *
        ∫ z, mixedComplexMonomial a b z ∂circularGaussian := by
  let hpres := measurePreserving_circularGaussian_mul_internal c hc
  calc
    (∫ z, mixedComplexMonomial a b z ∂circularGaussian) =
        ∫ z, mixedComplexMonomial a b z
          ∂Measure.map (fun z : ℂ ↦ c * z) circularGaussian := by
            rw [hpres.map_eq]
    _ = ∫ z, mixedComplexMonomial a b (c * z) ∂circularGaussian := by
          rw [integral_map (by fun_prop) (by
            unfold mixedComplexMonomial
            fun_prop)]
    _ = ∫ z, (c ^ a * conj c ^ b) *
          mixedComplexMonomial a b z ∂circularGaussian := by
          apply integral_congr_ae
          filter_upwards [] with z
          simp [mixedComplexMonomial, mul_pow]
          ring
    _ = _ := integral_const_mul _ _

private theorem integral_mixedComplexMonomial_eq_zero_of_phase
    (a b : ℕ) (c : ℂ) (hc : ‖c‖ = 1)
    (hphase : c ^ a * conj c ^ b ≠ 1) :
    (∫ z, mixedComplexMonomial a b z ∂circularGaussian) = 0 := by
  have h := integral_mixedComplexMonomial_eq_phase_mul a b c hc
  have hne : 1 - c ^ a * conj c ^ b ≠ 0 := sub_ne_zero.mpr hphase.symm
  apply (mul_eq_zero.mp ?_).resolve_left hne
  calc
    (1 - c ^ a * conj c ^ b) *
        (∫ z, mixedComplexMonomial a b z ∂circularGaussian) =
      (∫ z, mixedComplexMonomial a b z ∂circularGaussian) -
        (c ^ a * conj c ^ b) *
          ∫ z, mixedComplexMonomial a b z ∂circularGaussian := by ring
    _ = 0 := sub_eq_zero.mpr h

private theorem phase_eighth_root_norm :
    ‖(((1 : ℂ) + Complex.I) / (Real.sqrt 2 : ℝ))‖ = 1 := by
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hnum : ‖(1 : ℂ) + Complex.I‖ = Real.sqrt 2 := by
    convert Complex.norm_add_mul_I 1 1 using 1 <;> norm_num
  rw [norm_div, hnum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hsqrt_pos]
  exact div_self hsqrt_pos.ne'

private theorem phase_eighth_root_pow_four :
    (((1 : ℂ) + Complex.I) / (Real.sqrt 2 : ℝ)) ^ 4 = -1 := by
  have hsqrt_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsqrt_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  field_simp [hsqrt_ne]
  rw [show ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 = 4 by
    calc
      ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 =
          (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) ^ 2 := by ring
      _ = 4 := by rw [hsqrt_sq]; norm_num]
  have hsquare : ((1 : ℂ) + Complex.I) ^ 2 = 2 * Complex.I := by
    calc
      ((1 : ℂ) + Complex.I) ^ 2 =
          1 + 2 * Complex.I + Complex.I ^ 2 := by ring
      _ = 2 * Complex.I := by rw [Complex.I_sq]; ring
  calc
    ((1 : ℂ) + Complex.I) ^ 4 = (((1 : ℂ) + Complex.I) ^ 2) ^ 2 := by ring
    _ = (2 * Complex.I) ^ 2 := by rw [hsquare]
    _ = -4 := by rw [mul_pow, Complex.I_sq]; norm_num

private theorem phase_eighth_root_conj_pow_four :
    conj (((1 : ℂ) + Complex.I) / (Real.sqrt 2 : ℝ)) ^ 4 = -1 := by
  rw [← map_pow, phase_eighth_root_pow_four]
  norm_num

private theorem phase_neg_one_ne_one_of_odd_add
    (a b : ℕ) (hodd : Odd (a + b)) :
    (-1 : ℂ) ^ a * conj (-1 : ℂ) ^ b ≠ 1 := by
  rw [show conj (-1 : ℂ) = -1 by norm_num, ← pow_add,
    hodd.neg_one_pow]
  norm_num

private theorem phase_I_ne_one_of_eq_add_two_left
    (a b : ℕ) (h : a = b + 2) :
    Complex.I ^ a * conj Complex.I ^ b ≠ 1 := by
  subst a
  have hbalanced : Complex.I ^ b * conj Complex.I ^ b = 1 := by
    rw [← mul_pow, Complex.mul_conj]
    simp
  rw [pow_add, show Complex.I ^ 2 = -1 by exact Complex.I_sq,
    mul_assoc]
  calc
    Complex.I ^ b * (-1 * conj Complex.I ^ b) =
        -(Complex.I ^ b * conj Complex.I ^ b) := by ring
    _ = -1 := by rw [hbalanced]
    _ ≠ 1 := by norm_num

private theorem phase_I_ne_one_of_eq_add_two_right
    (a b : ℕ) (h : b = a + 2) :
    Complex.I ^ a * conj Complex.I ^ b ≠ 1 := by
  subst b
  have hbalanced : Complex.I ^ a * conj Complex.I ^ a = 1 := by
    rw [← mul_pow, Complex.mul_conj]
    simp
  rw [pow_add]
  have hconj_sq : conj Complex.I ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq]
    norm_num
  calc
    Complex.I ^ a * (conj Complex.I ^ a * conj Complex.I ^ 2) =
        (Complex.I ^ a * conj Complex.I ^ a) * conj Complex.I ^ 2 := by ring
    _ = -1 := by rw [hbalanced, hconj_sq]; ring
    _ ≠ 1 := by norm_num

/-- Complete scalar circular Wick table through bidegree four. -/
theorem integral_mixedComplexMonomial_circularGaussian_le_four_internal
    (a b : ℕ) (ha : a ≤ 4) (hb : b ≤ 4) :
    (∫ z, mixedComplexMonomial a b z ∂circularGaussian) =
      if a = b then (a.factorial : ℂ) else 0 := by
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl]
    simpa [mixedComplexMonomial] using
      integral_pow_mul_conj_pow_circularGaussian_internal a
  · rw [if_neg hab]
    by_cases hodd : Odd (a + b)
    · exact integral_mixedComplexMonomial_eq_zero_of_phase a b (-1)
        (by norm_num) (phase_neg_one_ne_one_of_odd_add a b hodd)
    · have heven : Even (a + b) := Nat.not_odd_iff_even.mp hodd
      have hcases : a = b + 2 ∨ b = a + 2 ∨
          (a = 4 ∧ b = 0) ∨ (a = 0 ∧ b = 4) := by
        rcases heven with ⟨k, hk⟩
        omega
      rcases hcases with htwo | htwo | hfour | hfour
      · exact integral_mixedComplexMonomial_eq_zero_of_phase a b Complex.I
          (by simp) (phase_I_ne_one_of_eq_add_two_left a b htwo)
      · exact integral_mixedComplexMonomial_eq_zero_of_phase a b Complex.I
          (by simp) (phase_I_ne_one_of_eq_add_two_right a b htwo)
      · rcases hfour with ⟨rfl, rfl⟩
        exact integral_mixedComplexMonomial_eq_zero_of_phase 4 0
          (((1 : ℂ) + Complex.I) / (Real.sqrt 2 : ℝ))
          phase_eighth_root_norm (by
            simpa using (show
              (((1 : ℂ) + Complex.I) / (Real.sqrt 2 : ℝ)) ^ 4 ≠ 1 by
                rw [phase_eighth_root_pow_four]
                norm_num))
      · rcases hfour with ⟨rfl, rfl⟩
        exact integral_mixedComplexMonomial_eq_zero_of_phase 0 4
          (((1 : ℂ) + Complex.I) / (Real.sqrt 2 : ℝ))
          phase_eighth_root_norm (by
            simpa using (show
              conj (((1 : ℂ) + Complex.I) / (Real.sqrt 2 : ℝ)) ^ 4 ≠ 1 by
                rw [phase_eighth_root_conj_pow_four]
                norm_num))

/-! ## Finite-coordinate Wick formula through order four -/

/-- Number of occurrences of a coordinate in an index tuple. -/
def projectiveTupleMultiplicity {N r : ℕ} (i : Fin r → Fin N)
    (p : Fin N) : ℕ :=
  Fintype.card {a : Fin r // i a = p}

private theorem projectiveTupleMultiplicity_le {N r : ℕ}
    (i : Fin r → Fin N) (p : Fin N) :
    projectiveTupleMultiplicity i p ≤ r := by
  simpa [projectiveTupleMultiplicity] using
    (Fintype.card_subtype_le (fun a : Fin r ↦ i a = p))

private theorem prod_comp_eq_prod_pow_projectiveTupleMultiplicity
    {R : Type*} [CommMonoid R] {N r : ℕ}
    (i : Fin r → Fin N) (x : Fin N → R) :
    (∏ a, x (i a)) =
      ∏ p, x p ^ projectiveTupleMultiplicity i p := by
  rw [← Fintype.prod_fiberwise i (fun a ↦ x (i a))]
  apply Finset.prod_congr rfl
  intro p hp
  change (∏ a : {a : Fin r // i a = p}, x (i a)) =
    x p ^ Fintype.card {a : Fin r // i a = p}
  calc
    (∏ a : {a : Fin r // i a = p}, x (i a)) =
        ∏ _a : {a : Fin r // i a = p}, x p := by
          apply Finset.prod_congr rfl
          intro a ha
          rw [a.property]
    _ = _ := by simp

/-- A coordinate of a balanced Gaussian tensor monomial. -/
def complexGaussianTensorMonomial {N r : ℕ}
    (i j : Fin r → Fin N) (x : Fin N → ℂ) : ℂ :=
  ∏ a, x (i a) * conj (x (j a))

private theorem complexGaussianTensorMonomial_eq_mixedMulti
    {N r : ℕ} (i j : Fin r → Fin N) (x : Fin N → ℂ) :
    complexGaussianTensorMonomial i j x =
      mixedComplexMultiMonomial
        (projectiveTupleMultiplicity i)
        (projectiveTupleMultiplicity j) x := by
  unfold complexGaussianTensorMonomial mixedComplexMultiMonomial
    mixedComplexMonomial
  rw [Finset.prod_mul_distrib]
  rw [prod_comp_eq_prod_pow_projectiveTupleMultiplicity i x]
  rw [prod_comp_eq_prod_pow_projectiveTupleMultiplicity j
    (fun p ↦ conj (x p))]
  rw [← Finset.prod_mul_distrib]

/-- The iid complex Gaussian tensor moment through order four, expressed by
coordinate multiplicities. -/
theorem integral_complexGaussianTensorMonomial_le_four_internal
    {N r : ℕ} (hr : r ≤ 4) (i j : Fin r → Fin N) :
    (∫ x : Fin N → ℂ, complexGaussianTensorMonomial i j x
        ∂circularGaussianVector N) =
      if projectiveTupleMultiplicity i = projectiveTupleMultiplicity j then
        ∏ p, ((projectiveTupleMultiplicity i p).factorial : ℂ)
      else 0 := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun x ↦
    complexGaussianTensorMonomial_eq_mixedMulti i j x)]
  unfold circularGaussianVector
  rw [integral_mixedComplexMultiMonomial_iid]
  simp_rw [integral_mixedComplexMonomial_circularGaussian_le_four_internal
    _ _ (le_trans (projectiveTupleMultiplicity_le i _) hr)
      (le_trans (projectiveTupleMultiplicity_le j _) hr)]
  by_cases hij : projectiveTupleMultiplicity i =
      projectiveTupleMultiplicity j
  · rw [if_pos hij]
    apply Finset.prod_congr rfl
    intro p hp
    rw [congrFun hij p, if_pos rfl]
  · rw [if_neg hij]
    have hpoint : ∃ p, projectiveTupleMultiplicity i p ≠
        projectiveTupleMultiplicity j p := by
      by_contra h
      push_neg at h
      exact hij (funext h)
    obtain ⟨p, hp⟩ := hpoint
    exact Finset.prod_eq_zero (Finset.mem_univ p) (if_neg hp)

private theorem projectiveTupleMultiplicity_eq_iff_exists_matchingPerm
    {N r : ℕ} (i j : Fin r → Fin N) :
    projectiveTupleMultiplicity i = projectiveTupleMultiplicity j ↔
      ∃ π : Equiv.Perm (Fin r), i = j ∘ π := by
  constructor
  · intro h
    let e : ∀ p : Fin N, {a : Fin r // i a = p} ≃
        {a : Fin r // j a = p} := fun p ↦
      Fintype.equivOfCardEq (congrFun h p)
    let π : Equiv.Perm (Fin r) := Equiv.ofFiberEquiv e
    refine ⟨π, funext fun a ↦ ?_⟩
    exact (Equiv.ofFiberEquiv_map e a).symm
  · rintro ⟨π, hπ⟩
    funext p
    unfold projectiveTupleMultiplicity
    exact Fintype.card_congr (Equiv.subtypeEquiv π fun a ↦ by
      change i a = p ↔ j (π a) = p
      rw [congrFun hπ a]
      rfl)

private def matchingPermEquivStabilizer {N r : ℕ}
    (i j : Fin r → Fin N) (τ : Equiv.Perm (Fin r))
    (hτ : i = j ∘ τ) :
    {π : Equiv.Perm (Fin r) // i = j ∘ π} ≃
      {σ : Equiv.Perm (Fin r) // j ∘ σ = j} :=
  Equiv.subtypeEquiv (Equiv.mulRight τ.symm) fun π ↦ by
    constructor
    · intro hπ
      funext a
      change j (π (τ.symm a)) = j a
      calc
        j (π (τ.symm a)) = i (τ.symm a) :=
          (congrFun hπ (τ.symm a)).symm
        _ = j (τ (τ.symm a)) := congrFun hτ (τ.symm a)
        _ = j a := by rw [τ.apply_symm_apply]
    · intro hstab
      funext a
      calc
        i a = j (τ a) := congrFun hτ a
        _ = j (π a) := by
          have h := congrFun hstab (τ a)
          change j (π (τ.symm (τ a))) = j (τ a) at h
          rw [τ.symm_apply_apply] at h
          exact h.symm

private theorem card_matchingPermutations {N r : ℕ}
    (i j : Fin r → Fin N) :
    Fintype.card {π : Equiv.Perm (Fin r) // i = j ∘ π} =
      if projectiveTupleMultiplicity i = projectiveTupleMultiplicity j then
        ∏ p, (projectiveTupleMultiplicity i p).factorial
      else 0 := by
  by_cases hmul : projectiveTupleMultiplicity i =
      projectiveTupleMultiplicity j
  · rw [if_pos hmul]
    obtain ⟨τ, hτ⟩ :=
      (projectiveTupleMultiplicity_eq_iff_exists_matchingPerm i j).mp hmul
    calc
      Fintype.card {π : Equiv.Perm (Fin r) // i = j ∘ π} =
          Fintype.card {σ : Equiv.Perm (Fin r) // j ∘ σ = j} :=
        Fintype.card_congr (matchingPermEquivStabilizer i j τ hτ)
      _ = ∏ p, (Fintype.card {a : Fin r // j a = p}).factorial :=
        DomMulAct.stabilizer_card j
      _ = ∏ p, (projectiveTupleMultiplicity j p).factorial := by
        rfl
      _ = ∏ p, (projectiveTupleMultiplicity i p).factorial := by
        rw [hmul]
  · rw [if_neg hmul]
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun π ↦ hmul
      ((projectiveTupleMultiplicity_eq_iff_exists_matchingPerm i j).mpr
        ⟨π.1, π.2⟩)⟩

private theorem projectivePermutationDeltaProduct_eq_indicator
    {N r : ℕ} (i j : Fin r → Fin N) (π : Equiv.Perm (Fin r)) :
    (∏ a : Fin r, if i a = j (π a) then (1 : ℂ) else 0) =
      if i = j ∘ π then 1 else 0 := by
  by_cases hπ : i = j ∘ π
  · rw [if_pos hπ]
    apply Finset.prod_eq_one
    intro a ha
    rw [if_pos]
    exact congrFun hπ a
  · rw [if_neg hπ]
    have hpoint : ∃ a, i a ≠ j (π a) := by
      by_contra h
      push Not at h
      exact hπ (funext h)
    obtain ⟨a, ha⟩ := hpoint
    exact Finset.prod_eq_zero (Finset.mem_univ a) (if_neg ha)

private theorem projectivePermutationDeltaSum_eq_multiplicityProduct
    {N r : ℕ} (i j : Fin r → Fin N) :
    (∑ π : Equiv.Perm (Fin r),
      ∏ a : Fin r, if i a = j (π a) then (1 : ℂ) else 0) =
      if projectiveTupleMultiplicity i = projectiveTupleMultiplicity j then
        ∏ p, ((projectiveTupleMultiplicity i p).factorial : ℂ)
      else 0 := by
  simp_rw [projectivePermutationDeltaProduct_eq_indicator i j]
  calc
    (∑ π : Equiv.Perm (Fin r), if i = j ∘ π then (1 : ℂ) else 0) =
        (Fintype.card {π : Equiv.Perm (Fin r) // i = j ∘ π} : ℂ) := by
      rw [Fintype.card_subtype]
      simpa using (Finset.sum_boole (R := ℂ)
        (fun π : Equiv.Perm (Fin r) ↦ i = j ∘ π) Finset.univ)
    _ = _ := by
      rw [card_matchingPermutations i j]
      split_ifs <;> push_cast <;> simp

/-- The exact finite-dimensional complex Wick formula needed below, proved
from scalar moments and finite permutation counting in orders at most four. -/
theorem integral_complexGaussianTensorMonomial_eq_permutationDelta_le_four_internal
    {N r : ℕ} (hr : r ≤ 4) (i j : Fin r → Fin N) :
    (∫ x : Fin N → ℂ, complexGaussianTensorMonomial i j x
        ∂circularGaussianVector N) =
      ∑ π : Equiv.Perm (Fin r),
        ∏ a : Fin r, if i a = j (π a) then (1 : ℂ) else 0 := by
  rw [integral_complexGaussianTensorMonomial_le_four_internal hr i j,
    projectivePermutationDeltaSum_eq_multiplicityProduct i j]

/-! ## Gaussian polar transfer to the complex unit sphere -/

/-- The same tensor coordinate on complex Euclidean space. -/
def complexEuclideanTensorMonomial {N r : ℕ}
    (i j : Fin r → Fin N) (x : CircularEuclideanSpace N) : ℂ :=
  ∏ a, x (i a) * conj (x (j a))

@[fun_prop]
private theorem measurable_complexEuclideanTensorMonomial
    {N r : ℕ} (i j : Fin r → Fin N) :
    Measurable (complexEuclideanTensorMonomial i j) := by
  unfold complexEuclideanTensorMonomial
  fun_prop

private theorem complexEuclideanTensorMonomial_toLp
    {N r : ℕ} (i j : Fin r → Fin N) (x : Fin N → ℂ) :
    complexEuclideanTensorMonomial i j (WithLp.toLp 2 x) =
      complexGaussianTensorMonomial i j x := by
  rfl

private theorem complexEuclideanTensorMonomial_smul
    {N r : ℕ} (i j : Fin r → Fin N) (s : ℝ)
    (x : CircularEuclideanSpace N) :
    complexEuclideanTensorMonomial i j (s • x) =
      ((s : ℂ) * conj (s : ℂ)) ^ r *
        complexEuclideanTensorMonomial i j x := by
  unfold complexEuclideanTensorMonomial
  have hentry (a : Fin r) :
      (s • x) (i a) * conj ((s • x) (j a)) =
        ((s : ℂ) * conj (s : ℂ)) *
          (x (i a) * conj (x (j a))) := by
    simp only [PiLp.smul_apply, RCLike.real_smul_eq_coe_mul,
      map_mul]
    ac_rfl
  simp_rw [hentry]
  rw [Finset.prod_mul_distrib]
  simp

private theorem complexProjectiveRisingFactorial_succ (N r : ℕ) :
    complexProjectiveRisingFactorial N (r + 1) =
      complexProjectiveRisingFactorial N r * (N + r : ℕ) := by
  unfold complexProjectiveRisingFactorial
  rw [Fin.prod_univ_castSucc]
  simp

private theorem dimensionProduct_two_mul_eq_projectiveRisingFactorial
    (N r : ℕ) :
    dimensionProduct (2 * N) r =
      (2 : ℝ) ^ r * complexProjectiveRisingFactorial N r := by
  induction r with
  | zero => simp [complexProjectiveRisingFactorial]
  | succ r ih =>
      rw [dimensionProduct_succ, complexProjectiveRisingFactorial_succ,
        ih, pow_succ]
      push_cast
      ring

private theorem circularGaussian_scale_energy :
    ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
      conj ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ))) = (2 : ℂ)⁻¹ := by
  rw [Complex.mul_conj, Complex.normSq_ofReal]
  have htwo : (2 : ℂ)⁻¹ = (((2 : ℝ)⁻¹ : ℝ) : ℂ) := by norm_num
  rw [htwo]
  norm_cast
  have hsqrt_ne : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp [hsqrt_ne]
  exact (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)).symm

/-- Transfer the low-order iid circular Wick formula to Mathlib's real
standard Gaussian on complex Euclidean space. -/
theorem integral_complexEuclideanTensorMonomial_stdGaussian_le_four_internal
    {N r : ℕ} (hr : r ≤ 4) (i j : Fin r → Fin N) :
    (∫ x : CircularEuclideanSpace N,
        complexEuclideanTensorMonomial i j x
        ∂stdGaussian (CircularEuclideanSpace N)) =
      (2 : ℂ) ^ r *
        ∑ π : Equiv.Perm (Fin r),
          ∏ a : Fin r, if i a = j (π a) then (1 : ℂ) else 0 := by
  let s : ℝ := (Real.sqrt 2)⁻¹
  let D : ℂ := ∑ π : Equiv.Perm (Fin r),
    ∏ a : Fin r, if i a = j (π a) then (1 : ℂ) else 0
  have hmap :
      Measure.map (WithLp.toLp 2) (circularGaussianVector N) =
        Measure.map (fun x ↦ s • x)
          (stdGaussian (CircularEuclideanSpace N)) := by
    simpa [circularGaussianVector, s] using
      map_toLp_pi_circularGaussian_eq_scaled_stdGaussian N
  have hscaled :
      D = (((s : ℂ) * conj (s : ℂ)) ^ r) *
        ∫ x : CircularEuclideanSpace N,
          complexEuclideanTensorMonomial i j x
          ∂stdGaussian (CircularEuclideanSpace N) := by
    calc
      D = ∫ x : Fin N → ℂ, complexGaussianTensorMonomial i j x
          ∂circularGaussianVector N :=
        (integral_complexGaussianTensorMonomial_eq_permutationDelta_le_four_internal
          hr i j).symm
      _ = ∫ x : CircularEuclideanSpace N,
          complexEuclideanTensorMonomial i j x
          ∂Measure.map (WithLp.toLp 2) (circularGaussianVector N) := by
        rw [integral_map (by fun_prop) (by fun_prop)]
        exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦
          (complexEuclideanTensorMonomial_toLp i j x).symm)
      _ = ∫ x : CircularEuclideanSpace N,
          complexEuclideanTensorMonomial i j x
          ∂Measure.map (fun x ↦ s • x)
            (stdGaussian (CircularEuclideanSpace N)) := by
        rw [hmap]
      _ = ∫ x : CircularEuclideanSpace N,
          complexEuclideanTensorMonomial i j (s • x)
          ∂stdGaussian (CircularEuclideanSpace N) := by
        rw [integral_map (by fun_prop) (by fun_prop)]
      _ = (((s : ℂ) * conj (s : ℂ)) ^ r) *
          ∫ x : CircularEuclideanSpace N,
            complexEuclideanTensorMonomial i j x
            ∂stdGaussian (CircularEuclideanSpace N) := by
        simp_rw [complexEuclideanTensorMonomial_smul]
        rw [integral_const_mul]
  have hbase : ((s : ℂ) * conj (s : ℂ)) = (2 : ℂ)⁻¹ := by
    exact circularGaussian_scale_energy
  rw [hbase] at hscaled
  change (∫ x : CircularEuclideanSpace N,
      complexEuclideanTensorMonomial i j x
      ∂stdGaussian (CircularEuclideanSpace N)) = (2 : ℂ) ^ r * D
  have hcancel : (2 : ℂ) ^ r * ((2 : ℂ)⁻¹) ^ r = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (∫ x : CircularEuclideanSpace N,
        complexEuclideanTensorMonomial i j x
        ∂stdGaussian (CircularEuclideanSpace N)) =
        1 * ∫ x : CircularEuclideanSpace N,
          complexEuclideanTensorMonomial i j x
          ∂stdGaussian (CircularEuclideanSpace N) := by ring
    _ = ((2 : ℂ) ^ r * ((2 : ℂ)⁻¹) ^ r) *
        ∫ x : CircularEuclideanSpace N,
          complexEuclideanTensorMonomial i j x
          ∂stdGaussian (CircularEuclideanSpace N) := by rw [hcancel]
    _ = (2 : ℂ) ^ r *
        (((2 : ℂ)⁻¹) ^ r *
          ∫ x : CircularEuclideanSpace N,
            complexEuclideanTensorMonomial i j x
            ∂stdGaussian (CircularEuclideanSpace N)) := by ring
    _ = (2 : ℂ) ^ r * D := by rw [← hscaled]

private theorem norm_smul_unitDirection_eq
    {N : ℕ} (x : CircularEuclideanSpace N) :
    ‖x‖ • LogdetLean.unitDirection x = x := by
  by_cases hx : x = 0
  · subst x
    simp [LogdetLean.unitDirection]
  · rw [LogdetLean.unitDirection]
    simp only [if_neg hx, smul_smul]
    rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

private theorem complexEuclideanTensorMonomial_polar
    {N r : ℕ} (i j : Fin r → Fin N)
    (x : CircularEuclideanSpace N) :
    complexEuclideanTensorMonomial i j x =
      complexEuclideanTensorMonomial i j (LogdetLean.unitDirection x) *
        ((((‖x‖ ^ 2 : ℝ) : ℂ)) ^ r) := by
  have hnormEnergy :
      ((‖x‖ : ℂ) * conj (‖x‖ : ℂ)) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_ofReal]
    norm_cast
    ring
  calc
    complexEuclideanTensorMonomial i j x =
        complexEuclideanTensorMonomial i j
          (‖x‖ • LogdetLean.unitDirection x) := by
      rw [norm_smul_unitDirection_eq x]
    _ = (((‖x‖ : ℂ) * conj (‖x‖ : ℂ)) ^ r) *
        complexEuclideanTensorMonomial i j (LogdetLean.unitDirection x) :=
      complexEuclideanTensorMonomial_smul i j ‖x‖ _
    _ = complexEuclideanTensorMonomial i j (LogdetLean.unitDirection x) *
        ((((‖x‖ ^ 2 : ℝ) : ℂ)) ^ r) := by
      rw [hnormEnergy]
      ac_rfl

private theorem integral_energy_pow_map_stdGaussian
    {N r : ℕ} (hN : 1 ≤ N) :
    (∫ q : ℝ, (q : ℂ) ^ r
        ∂Measure.map (fun x : CircularEuclideanSpace N ↦ ‖x‖ ^ 2)
          (stdGaussian (CircularEuclideanSpace N))) =
      ((dimensionProduct (2 * N) r : ℝ) : ℂ) := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (by omega)
  letI : Nontrivial (CircularEuclideanSpace N) := inferInstance
  rw [integral_map (by fun_prop) (by fun_prop)]
  rw [show (fun x : CircularEuclideanSpace N ↦
      (((‖x‖ ^ 2 : ℝ) : ℂ) ^ r)) =
      (fun x ↦ (((‖x‖ ^ (2 * r) : ℝ)) : ℂ)) by
    funext x
    rw [← Complex.ofReal_pow, pow_mul]]
  rw [integral_complex_ofReal,
    integral_norm_pow_two_mul_stdGaussian]
  congr 2
  simpa using
    (Module.finrank_mul_finrank ℝ ℂ
      (EuclideanSpace ℂ (Fin N))).symm

private theorem integral_directionTensor_stdGaussian_eq_projective
    {N r : ℕ} (hN : 1 ≤ N) (i j : Fin r → Fin N) :
    (∫ x : CircularEuclideanSpace N,
        complexEuclideanTensorMonomial i j x
        ∂Measure.map LogdetLean.unitDirection
          (stdGaussian (CircularEuclideanSpace N))) =
      complexProjectiveTensorMomentCoordinate N r i j := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (by omega)
  letI : Nontrivial (CircularEuclideanSpace N) := inferInstance
  rw [LogdetLean.map_unitDirection_stdGaussian_eq_uniformSphereSurfaceMeasure]
  rw [integral_map (by fun_prop) (by fun_prop)]
  rfl

private theorem integral_stdGaussian_tensor_eq_projective_mul_dimensionProduct
    {N r : ℕ} (hN : 1 ≤ N) (i j : Fin r → Fin N) :
    (∫ x : CircularEuclideanSpace N,
        complexEuclideanTensorMonomial i j x
        ∂stdGaussian (CircularEuclideanSpace N)) =
      complexProjectiveTensorMomentCoordinate N r i j *
        ((dimensionProduct (2 * N) r : ℝ) : ℂ) := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (by omega)
  letI : Nontrivial (CircularEuclideanSpace N) := inferInstance
  calc
    (∫ x : CircularEuclideanSpace N,
        complexEuclideanTensorMonomial i j x
        ∂stdGaussian (CircularEuclideanSpace N)) =
        ∫ x : CircularEuclideanSpace N,
          complexEuclideanTensorMonomial i j (LogdetLean.unitDirection x) *
            ((((‖x‖ ^ 2 : ℝ) : ℂ)) ^ r)
          ∂stdGaussian (CircularEuclideanSpace N) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact complexEuclideanTensorMonomial_polar i j x
    _ = ∫ z : CircularEuclideanSpace N × ℝ,
        complexEuclideanTensorMonomial i j z.1 * (z.2 : ℂ) ^ r
        ∂Measure.map
          (LogdetLean.Coherence.gaussianDirectionEnergy :
            CircularEuclideanSpace N → CircularEuclideanSpace N × ℝ)
          (stdGaussian (CircularEuclideanSpace N)) := by
      rw [integral_map
        LogdetLean.Coherence.measurable_gaussianDirectionEnergy.aemeasurable
        (by fun_prop)]
      rfl
    _ = ∫ z : CircularEuclideanSpace N × ℝ,
        complexEuclideanTensorMonomial i j z.1 * (z.2 : ℂ) ^ r
        ∂(Measure.map LogdetLean.unitDirection
            (stdGaussian (CircularEuclideanSpace N))).prod
          (Measure.map (fun x : CircularEuclideanSpace N ↦ ‖x‖ ^ 2)
            (stdGaussian (CircularEuclideanSpace N))) := by
      rw [LogdetLean.Coherence.map_gaussianDirectionEnergy_stdGaussian_eq_prod]
    _ = (∫ x : CircularEuclideanSpace N,
        complexEuclideanTensorMonomial i j x
          ∂Measure.map LogdetLean.unitDirection
            (stdGaussian (CircularEuclideanSpace N))) *
        ∫ q : ℝ, (q : ℂ) ^ r
          ∂Measure.map (fun x : CircularEuclideanSpace N ↦ ‖x‖ ^ 2)
            (stdGaussian (CircularEuclideanSpace N)) := by
      exact integral_prod_mul
        (complexEuclideanTensorMonomial i j)
        (fun q : ℝ ↦ (q : ℂ) ^ r)
    _ = complexProjectiveTensorMomentCoordinate N r i j *
        ((dimensionProduct (2 * N) r : ℝ) : ℂ) := by
      rw [integral_directionTensor_stdGaussian_eq_projective hN i j,
        integral_energy_pow_map_stdGaussian hN]

private theorem complexProjectiveRisingFactorial_pos
    {N r : ℕ} (hN : 1 ≤ N) :
    0 < complexProjectiveRisingFactorial N r := by
  unfold complexProjectiveRisingFactorial
  apply Finset.prod_pos
  intro a ha
  exact_mod_cast (show 0 < N + a.1 by omega)

/-- The Collins--Sniady projective tensor coordinate formula in exactly the
orders used by the headline proof.  Unlike the general external theorem,
this statement is proved internally from Gaussian polar coordinates. -/
theorem complexProjectiveTensorMoment_le_four_internal
    {N r : ℕ} (hN : 1 ≤ N) (hr : r ≤ 4)
    (i j : Fin r → Fin N) :
    complexProjectiveTensorMomentCoordinate N r i j =
      complexProjectiveSymmetrizerCoordinate N r i j := by
  let D : ℂ := ∑ π : Equiv.Perm (Fin r),
    ∏ a : Fin r, if i a = j (π a) then (1 : ℂ) else 0
  let R : ℝ := complexProjectiveRisingFactorial N r
  have hstd :=
    integral_complexEuclideanTensorMonomial_stdGaussian_le_four_internal
      hr i j
  have hpolar :=
    integral_stdGaussian_tensor_eq_projective_mul_dimensionProduct hN i j
  have hdim :=
    dimensionProduct_two_mul_eq_projectiveRisingFactorial N r
  have hmain :
      (2 : ℂ) ^ r * D =
        complexProjectiveTensorMomentCoordinate N r i j *
          ((2 : ℂ) ^ r * (R : ℂ)) := by
    calc
      (2 : ℂ) ^ r * D =
          ∫ x : CircularEuclideanSpace N,
            complexEuclideanTensorMonomial i j x
            ∂stdGaussian (CircularEuclideanSpace N) := hstd.symm
      _ = complexProjectiveTensorMomentCoordinate N r i j *
          ((dimensionProduct (2 * N) r : ℝ) : ℂ) := hpolar
      _ = complexProjectiveTensorMomentCoordinate N r i j *
          ((2 : ℂ) ^ r * (R : ℂ)) := by
        rw [hdim]
        dsimp [R]
        push_cast
        rfl
  have htwo : (2 : ℂ) ^ r ≠ 0 := pow_ne_zero r (by norm_num)
  have hDR : D =
      complexProjectiveTensorMomentCoordinate N r i j * (R : ℂ) := by
    apply mul_left_cancel₀ htwo
    calc
      (2 : ℂ) ^ r * D =
          complexProjectiveTensorMomentCoordinate N r i j *
            ((2 : ℂ) ^ r * (R : ℂ)) := hmain
      _ = (2 : ℂ) ^ r *
          (complexProjectiveTensorMomentCoordinate N r i j * (R : ℂ)) := by
        ring
  have hRpos : 0 < R := by
    exact complexProjectiveRisingFactorial_pos hN
  have hRne : (R : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hRpos
  have hsolve :
      complexProjectiveTensorMomentCoordinate N r i j =
        (R : ℂ)⁻¹ * D := by
    calc
      complexProjectiveTensorMomentCoordinate N r i j =
          1 * complexProjectiveTensorMomentCoordinate N r i j := by ring
      _ = ((R : ℂ)⁻¹ * (R : ℂ)) *
          complexProjectiveTensorMomentCoordinate N r i j := by
        rw [inv_mul_cancel₀ hRne]
      _ = (R : ℂ)⁻¹ *
          (complexProjectiveTensorMomentCoordinate N r i j * (R : ℂ)) := by
        ring
      _ = (R : ℂ)⁻¹ * D := by rw [← hDR]
  simpa [complexProjectiveSymmetrizerCoordinate, D, R,
    Complex.ofReal_inv] using hsolve

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

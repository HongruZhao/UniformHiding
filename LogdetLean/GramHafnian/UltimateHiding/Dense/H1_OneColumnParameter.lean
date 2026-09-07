import LogdetLean.GramHafnian.UltimateHiding.Dense.H1_RowGramOrbit
import LogdetLean.Coherence.GaussianNormDirectionIndependence
import LogdetLean.FixedSubspaceGaussian

open scoped InnerProductSpace RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense
noncomputable section

def h1TopComplexSubspace (N r : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (N + r))) where
  carrier := {x | ∀ j : Fin r, x (Fin.natAdd N j) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy j
    simp [hx j, hy j]
  smul_mem' := by
    intro c x hx j
    simp [hx j]

def h1TopComplexCoord (N r : ℕ)
    (x : h1TopComplexSubspace N r) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun i ↦ x.1 (Fin.castAdd r i))

def h1TopComplexEmbed (N r : ℕ)
    (x : EuclideanSpace ℂ (Fin N)) : h1TopComplexSubspace N r :=
  ⟨WithLp.toLp 2 (fun k ↦
      Sum.elim (fun i ↦ x i) (fun _ ↦ 0) (finSumFinEquiv.symm k)), by
    intro j
    simp⟩

@[simp] theorem h1TopComplexCoord_apply (N r : ℕ)
    (x : h1TopComplexSubspace N r) (i : Fin N) :
    h1TopComplexCoord N r x i = x.1 (Fin.castAdd r i) := rfl

@[simp] theorem h1TopComplexEmbed_apply_castAdd (N r : ℕ)
    (x : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    (h1TopComplexEmbed N r x).1 (Fin.castAdd r i) = x i := by
  simp [h1TopComplexEmbed]

@[simp] theorem h1TopComplexEmbed_apply_natAdd (N r : ℕ)
    (x : EuclideanSpace ℂ (Fin N)) (j : Fin r) :
    (h1TopComplexEmbed N r x).1 (Fin.natAdd N j) = 0 := by
  simp [h1TopComplexEmbed]

def h1TopComplexLinearEquiv (N r : ℕ) :
    h1TopComplexSubspace N r ≃ₗ[ℂ] EuclideanSpace ℂ (Fin N) where
  toFun := h1TopComplexCoord N r
  invFun := h1TopComplexEmbed N r
  map_add' x y := by
    ext i
    rfl
  map_smul' c x := by
    ext i
    rfl
  left_inv x := by
    apply Subtype.ext
    ext k
    generalize hq : finSumFinEquiv.symm k = q
    cases q with
    | inl i =>
        have hk : k = Fin.castAdd r i := by
          simpa using congrArg finSumFinEquiv hq
        subst k
        simp
    | inr j =>
        have hk : k = Fin.natAdd N j := by
          simpa using congrArg finSumFinEquiv hq
        subst k
        simp [x.2 j]
  right_inv x := by
    ext i
    simp [h1TopComplexCoord]

theorem h1TopComplexLinearEquiv_inner (N r : ℕ)
    (x y : h1TopComplexSubspace N r) :
    ⟪h1TopComplexLinearEquiv N r x,
      h1TopComplexLinearEquiv N r y⟫_ℂ = ⟪x, y⟫_ℂ := by
  simp only [h1TopComplexLinearEquiv, h1TopComplexCoord,
    PiLp.inner_apply, RCLike.inner_apply, Submodule.coe_inner]
  rw [Fin.sum_univ_add]
  rw [show (∑ i : Fin r,
      y.1 (Fin.natAdd N i) * starRingEnd ℂ (x.1 (Fin.natAdd N i))) = 0 by
    apply Finset.sum_eq_zero
    intro i hi
    rw [x.2 i, y.2 i]
    simp]
  simp

def h1TopComplexIsometryEquiv (N r : ℕ) :
    h1TopComplexSubspace N r ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N) :=
  LinearEquiv.isometryOfInner (𝕜 := ℂ) (h1TopComplexLinearEquiv N r)
    (fun x y ↦ h1TopComplexLinearEquiv_inner N r x y)

def h1TopRealSubspace (N r : ℕ) :
    Submodule ℝ (EuclideanSpace ℂ (Fin (N + r))) :=
  (h1TopComplexSubspace N r).restrictScalars ℝ

def h1TopRealIsometryEquiv (N r : ℕ) :
    h1TopRealSubspace N r ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin N) where
  toFun x := h1TopComplexIsometryEquiv N r ⟨x.1, x.2⟩
  invFun y :=
    ⟨(h1TopComplexIsometryEquiv N r).symm y,
      (h1TopComplexIsometryEquiv N r).symm y |>.property⟩
  left_inv x := by
    apply Subtype.ext
    exact congrArg Subtype.val
      ((h1TopComplexIsometryEquiv N r).symm_apply_apply ⟨x.1, x.2⟩)
  right_inv y := (h1TopComplexIsometryEquiv N r).apply_symm_apply y
  map_add' x y := by
    exact map_add (h1TopComplexIsometryEquiv N r) ⟨x.1, x.2⟩ ⟨y.1, y.2⟩
  map_smul' c x := by
    change h1TopComplexIsometryEquiv N r
        ⟨((c : ℂ) • x.1), ?_⟩ =
      c • h1TopComplexIsometryEquiv N r ⟨x.1, x.2⟩
    exact map_smul (h1TopComplexIsometryEquiv N r) (c : ℂ) ⟨x.1, x.2⟩
  norm_map' x := by
    exact (h1TopComplexIsometryEquiv N r).norm_map ⟨x.1, x.2⟩

def h1DefaultComplexSphere {N : ℕ} (hN : 1 ≤ N) :
    ComplexUnitSphere N :=
  ⟨EuclideanSpace.single ⟨0, hN⟩ 1, by
    simp [Metric.mem_sphere]⟩

theorem h1_unitDirection_eq_inv_norm_smul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) (hx : x ≠ 0) :
    LogdetLean.unitDirection x = ‖x‖⁻¹ • x := by
  simp [LogdetLean.unitDirection, hx]

theorem h1_unitDirection_pos_smul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : ℝ) (ha : 0 < a) (x : E) :
    LogdetLean.unitDirection (a • x) = LogdetLean.unitDirection x := by
  by_cases hx : x = 0
  · subst x
    simp [LogdetLean.unitDirection]
  · have ha0 : a ≠ 0 := ne_of_gt ha
    have hax : a • x ≠ 0 := smul_ne_zero ha0 hx
    rw [h1_unitDirection_eq_inv_norm_smul _ hax,
      h1_unitDirection_eq_inv_norm_smul _ hx,
      norm_smul, Real.norm_eq_abs, abs_of_pos ha, smul_smul]
    congr 1
    field_simp

def h1GaussianComplexSphereDirection {N : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℂ (Fin N)) : ComplexUnitSphere N :=
  if hx : x = 0 then h1DefaultComplexSphere hN else
    ⟨LogdetLean.unitDirection x, by
      change dist (LogdetLean.unitDirection x) 0 = 1
      rw [dist_zero_right]
      rw [show LogdetLean.unitDirection x = ‖x‖⁻¹ • x by
        simp [LogdetLean.unitDirection, hx]]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg x),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

theorem measurable_h1GaussianComplexSphereDirection {N : ℕ}
    (hN : 1 ≤ N) : Measurable (h1GaussianComplexSphereDirection hN) := by
  classical
  apply Measurable.subtype_mk
  have hf : Measurable (fun x : EuclideanSpace ℂ (Fin N) ↦
      if x = 0 then (h1DefaultComplexSphere hN).1
      else LogdetLean.unitDirection x) := by
    apply Measurable.ite
    · exact measurable_id (measurableSet_singleton 0)
    · exact measurable_const
    · exact LogdetLean.measurable_unitDirection
  convert hf using 1
  funext x
  by_cases hx : x = 0
  · have hdir : h1GaussianComplexSphereDirection hN x =
        h1DefaultComplexSphere hN := by
      unfold h1GaussianComplexSphereDirection
      rw [dif_pos hx]
    rw [if_pos hx]
    exact congrArg Subtype.val hdir
  · have hdir : h1GaussianComplexSphereDirection hN x =
        ⟨LogdetLean.unitDirection x, by
          change dist (LogdetLean.unitDirection x) 0 = 1
          rw [dist_zero_right]
          rw [show LogdetLean.unitDirection x = ‖x‖⁻¹ • x by
            simp [LogdetLean.unitDirection, hx]]
          rw [norm_smul, Real.norm_eq_abs, abs_inv,
            abs_of_nonneg (norm_nonneg x),
            inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩ := by
      unfold h1GaussianComplexSphereDirection
      rw [dif_neg hx]
    rw [if_neg hx]
    exact congrArg Subtype.val hdir

theorem coe_h1GaussianComplexSphereDirection_of_ne {N : ℕ}
    (hN : 1 ≤ N) {x : EuclideanSpace ℂ (Fin N)} (hx : x ≠ 0) :
    (h1GaussianComplexSphereDirection hN x : EuclideanSpace ℂ (Fin N)) =
      LogdetLean.unitDirection x := by
  simp [h1GaussianComplexSphereDirection, hx]

theorem h1GaussianComplexSphereDirection_unitDirection_of_ne {N : ℕ}
    (hN : 1 ≤ N) {x : EuclideanSpace ℂ (Fin N)} (hx : x ≠ 0) :
    h1GaussianComplexSphereDirection hN (LogdetLean.unitDirection x) =
      h1GaussianComplexSphereDirection hN x := by
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hunit : LogdetLean.unitDirection x = ‖x‖⁻¹ • x := by
    simp [LogdetLean.unitDirection, hx]
  have hunitne : LogdetLean.unitDirection x ≠ 0 := by
    rw [hunit]
    exact smul_ne_zero (inv_ne_zero hnorm) hx
  have hnormUnit : ‖LogdetLean.unitDirection x‖ = 1 := by
    rw [hunit, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ hnorm]
  have hunitUnit :
      LogdetLean.unitDirection (LogdetLean.unitDirection x) =
        LogdetLean.unitDirection x := by
    rw [h1_unitDirection_eq_inv_norm_smul _ hunitne, hnormUnit]
    simp
  apply Subtype.ext
  rw [coe_h1GaussianComplexSphereDirection_of_ne hN hunitne,
    coe_h1GaussianComplexSphereDirection_of_ne hN hx]
  exact hunitUnit

theorem h1GaussianComplexSphereDirection_pos_smul {N : ℕ}
    (hN : 1 ≤ N) (a : ℝ) (ha : 0 < a)
    (x : EuclideanSpace ℂ (Fin N)) :
    h1GaussianComplexSphereDirection hN (a • x) =
      h1GaussianComplexSphereDirection hN x := by
  by_cases hx : x = 0
  · subst x
    simp [h1GaussianComplexSphereDirection]
  · have hax : a • x ≠ 0 := smul_ne_zero (ne_of_gt ha) hx
    apply Subtype.ext
    rw [coe_h1GaussianComplexSphereDirection_of_ne hN hax,
      coe_h1GaussianComplexSphereDirection_of_ne hN hx]
    exact h1_unitDirection_pos_smul a ha x

theorem map_h1GaussianComplexSphereDirection_stdGaussian
    {N : ℕ} (hN : 1 ≤ N) :
    Measure.map (h1GaussianComplexSphereDirection hN)
        (stdGaussian (EuclideanSpace ℂ (Fin N))) =
      complexUnitSphereProbabilityMeasure N := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (by omega)
  let E := EuclideanSpace ℂ (Fin N)
  let coeSphere : ComplexUnitSphere N → E := Subtype.val
  have hzero : ∀ᵐ x ∂(stdGaussian E), x ≠ 0 := by
    simpa [ae_iff] using stdGaussian_zero_singleton (E := E)
  have hae : (coeSphere ∘ h1GaussianComplexSphereDirection hN) =ᵐ[(stdGaussian E)]
      LogdetLean.unitDirection := by
    filter_upwards [hzero] with x hx
    exact coe_h1GaussianComplexSphereDirection_of_ne hN hx
  have hmapcoe : Measure.map coeSphere
      (Measure.map (h1GaussianComplexSphereDirection hN) (stdGaussian E)) =
      Measure.map coeSphere (complexUnitSphereProbabilityMeasure N) := by
    rw [Measure.map_map measurable_subtype_coe
      (measurable_h1GaussianComplexSphereDirection hN)]
    rw [Measure.map_congr hae]
    exact LogdetLean.map_unitDirection_stdGaussian_eq_uniformSphereSurfaceMeasure
      (E := E)
  exact (MeasurableEmbedding.map_injective
    (MeasurableEmbedding.subtype_coe
      (Metric.isClosed_sphere.measurableSet))) hmapcoe

theorem map_h1GaussianComplexSphereDirectionEnergy_stdGaussian
    {N : ℕ} (hN : 1 ≤ N) :
    Measure.map (fun x : EuclideanSpace ℂ (Fin N) ↦
        (h1GaussianComplexSphereDirection hN x, ‖x‖ ^ 2))
        (stdGaussian (EuclideanSpace ℂ (Fin N))) =
      (complexUnitSphereProbabilityMeasure N).prod
        (gammaMeasure (N : ℝ) (1 / 2)) := by
  let E := EuclideanSpace ℂ (Fin N)
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (by omega)
  let _ : Nontrivial E := by
    dsimp [E]
    infer_instance
  have hzero : ∀ᵐ x ∂(stdGaussian E), x ≠ 0 := by
    simpa [ae_iff] using stdGaussian_zero_singleton (E := E)
  have hidem :
      (fun x : E ↦ h1GaussianComplexSphereDirection hN
        (LogdetLean.unitDirection x)) =ᵐ[(stdGaussian E)]
      h1GaussianComplexSphereDirection hN := by
    filter_upwards [hzero] with x hx
    exact h1GaussianComplexSphereDirection_unitDirection_of_ne hN hx
  have hind0 :=
    LogdetLean.Coherence.indepFun_unitDirection_normSq_stdGaussian (E := E)
  have hind1 := hind0.comp
    (measurable_h1GaussianComplexSphereDirection hN) measurable_id
  have hind : IndepFun (h1GaussianComplexSphereDirection hN)
      (fun x : E ↦ ‖x‖ ^ 2) (stdGaussian E) := by
    apply hind1.congr hidem Filter.EventuallyEq.rfl
  have hdir : HasLaw (h1GaussianComplexSphereDirection hN)
      (complexUnitSphereProbabilityMeasure N) (stdGaussian E) :=
    ⟨(measurable_h1GaussianComplexSphereDirection hN).aemeasurable,
      map_h1GaussianComplexSphereDirection_stdGaussian hN⟩
  have henergy : HasLaw (fun x : E ↦ ‖x‖ ^ 2)
      (gammaMeasure (N : ℝ) (1 / 2)) (stdGaussian E) := by
    refine ⟨(measurable_id.norm.pow_const 2).aemeasurable, ?_⟩
    change LogdetLean.stdGaussianNormSqMeasure E = _
    rw [LogdetLean.stdGaussianNormSqMeasure_eq_gamma E]
    simp [E, finrank_real_of_complex]
  exact (hind.hasLaw_prod hdir henergy).map_eq

def h1TopDirectionEnergy {N r : ℕ} (hN : 1 ≤ N)
    (x : h1TopRealSubspace N r) : ComplexUnitSphere N × ℝ :=
  (h1GaussianComplexSphereDirection hN (h1TopRealIsometryEquiv N r x),
    ‖x‖ ^ 2)

theorem measurable_h1TopDirectionEnergy {N r : ℕ} (hN : 1 ≤ N) :
    Measurable (h1TopDirectionEnergy (r := r) hN) := by
  unfold h1TopDirectionEnergy
  exact (measurable_h1GaussianComplexSphereDirection hN).comp
      (h1TopRealIsometryEquiv N r).continuous.measurable |>.prodMk
    (measurable_id.norm.pow_const 2)

theorem map_h1TopDirectionEnergy_stdGaussian {N r : ℕ} (hN : 1 ≤ N) :
    Measure.map (h1TopDirectionEnergy (r := r) hN)
        (stdGaussian (h1TopRealSubspace N r)) =
      (complexUnitSphereProbabilityMeasure N).prod
        (gammaMeasure (N : ℝ) (1 / 2)) := by
  let e := h1TopRealIsometryEquiv N r
  let G := fun x : EuclideanSpace ℂ (Fin N) ↦
    (h1GaussianComplexSphereDirection hN x, ‖x‖ ^ 2)
  calc
    Measure.map (h1TopDirectionEnergy (r := r) hN)
        (stdGaussian (h1TopRealSubspace N r)) =
        Measure.map G (Measure.map e (stdGaussian (h1TopRealSubspace N r))) := by
      rw [Measure.map_map (by
        exact (measurable_h1GaussianComplexSphereDirection hN).prodMk
          (measurable_id.norm.pow_const 2)) e.continuous.measurable]
      congr 1
      funext x
      apply Prod.ext
      · rfl
      · simp [G, e, h1TopDirectionEnergy]
    _ = Measure.map G (stdGaussian (EuclideanSpace ℂ (Fin N))) := by
      have he : Measure.map
          (fun x : h1TopRealSubspace N r ↦ h1TopRealIsometryEquiv N r x)
          (stdGaussian (h1TopRealSubspace N r)) =
          stdGaussian (EuclideanSpace ℂ (Fin N)) :=
        ProbabilityTheory.stdGaussian_map
          (E := h1TopRealSubspace N r)
          (F := EuclideanSpace ℂ (Fin N))
          (h1TopRealIsometryEquiv N r)
      exact congrArg (Measure.map G) he
    _ = (complexUnitSphereProbabilityMeasure N).prod
        (gammaMeasure (N : ℝ) (1 / 2)) :=
      map_h1GaussianComplexSphereDirectionEnergy_stdGaussian hN

theorem finrank_h1TopRealSubspace (N r : ℕ) :
    Module.finrank ℝ (h1TopRealSubspace N r) = 2 * N := by
  have h := LinearEquiv.finrank_eq
    (h1TopRealIsometryEquiv N r).toLinearEquiv
  rw [finrank_real_of_complex] at h
  simpa using h

theorem finrank_complexEuclideanSpace_real (n : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) = 2 * n := by
  rw [finrank_real_of_complex]
  simp

theorem finrank_h1TopRealSubspace_orthogonal (N r : ℕ) :
    Module.finrank ℝ (h1TopRealSubspace N r).orthogonal = 2 * r := by
  have hadd := (h1TopRealSubspace N r).finrank_add_finrank_orthogonal
  rw [finrank_h1TopRealSubspace,
    finrank_complexEuclideanSpace_real (N + r)] at hadd
  omega

def h1AmbientTopTailData {N r : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℂ (Fin (N + r))) :
    (ComplexUnitSphere N × ℝ) × ℝ :=
  let K := h1TopRealSubspace N r
  (h1TopDirectionEnergy hN (K.orthogonalProjectionOnto x),
    ‖K.orthogonal.orthogonalProjectionOnto x‖ ^ 2)

theorem measurable_h1AmbientTopTailData {N r : ℕ} (hN : 1 ≤ N) :
    Measurable (h1AmbientTopTailData (r := r) hN) := by
  let K := h1TopRealSubspace N r
  unfold h1AmbientTopTailData
  exact (measurable_h1TopDirectionEnergy (r := r) hN).comp
      K.orthogonalProjectionOnto.continuous.measurable |>.prodMk
    (K.orthogonal.orthogonalProjectionOnto.continuous.measurable.norm.pow_const 2)

theorem map_h1AmbientTopTailData_stdGaussian {N r : ℕ}
    (hN : 1 ≤ N) (hr : 1 ≤ r) :
    Measure.map (h1AmbientTopTailData (r := r) hN)
        (stdGaussian (EuclideanSpace ℂ (Fin (N + r)))) =
      ((complexUnitSphereProbabilityMeasure N).prod
          (gammaMeasure (N : ℝ) (1 / 2))).prod
        (gammaMeasure (r : ℝ) (1 / 2)) := by
  let E := EuclideanSpace ℂ (Fin (N + r))
  let K := h1TopRealSubspace N r
  let split : E → K × K.orthogonal := fun x ↦
    (K.orthogonalProjectionOnto x, K.orthogonal.orthogonalProjectionOnto x)
  let F : K × K.orthogonal → (ComplexUnitSphere N × ℝ) × ℝ :=
    fun p ↦ (h1TopDirectionEnergy hN p.1, ‖p.2‖ ^ 2)
  let _ : Nontrivial K :=
    Module.nontrivial_of_finrank_pos (by
      rw [finrank_h1TopRealSubspace]
      omega)
  let _ : Nontrivial K.orthogonal :=
    Module.nontrivial_of_finrank_pos (by
      rw [finrank_h1TopRealSubspace_orthogonal]
      omega)
  have hsplit := (LogdetLean.hasLaw_orthogonalProjections_prod_stdGaussian K).map_eq
  have htop := map_h1TopDirectionEnergy_stdGaussian (r := r) hN
  have htail : Measure.map (fun x : K.orthogonal ↦ ‖x‖ ^ 2)
      (stdGaussian K.orthogonal) = gammaMeasure (r : ℝ) (1 / 2) := by
    change LogdetLean.stdGaussianNormSqMeasure K.orthogonal = _
    rw [LogdetLean.stdGaussianNormSqMeasure_eq_gamma K.orthogonal,
      finrank_h1TopRealSubspace_orthogonal]
    congr 2
    norm_num
  have hsplitMeas : Measurable split := by
    exact K.orthogonalProjectionOnto.continuous.measurable.prodMk
      K.orthogonal.orthogonalProjectionOnto.continuous.measurable
  have hFMeas : Measurable F := by
    exact (measurable_h1TopDirectionEnergy (r := r) hN).comp measurable_fst
      |>.prodMk (measurable_snd.norm.pow_const 2)
  calc
    Measure.map (h1AmbientTopTailData (r := r) hN) (stdGaussian E) =
        Measure.map F (Measure.map split (stdGaussian E)) := by
      rw [Measure.map_map hFMeas hsplitMeas]
      rfl
    _ = Measure.map F ((stdGaussian K).prod (stdGaussian K.orthogonal)) := by
      rw [hsplit]
    _ = (Measure.map (h1TopDirectionEnergy (r := r) hN)
          (stdGaussian K)).prod
        (Measure.map (fun x : K.orthogonal ↦ ‖x‖ ^ 2)
          (stdGaussian K.orthogonal)) := by
      exact (Measure.map_prod_map _ _
        (measurable_h1TopDirectionEnergy (r := r) hN)
        (measurable_id.norm.pow_const 2)).symm
    _ = ((complexUnitSphereProbabilityMeasure N).prod
          (gammaMeasure (N : ℝ) (1 / 2))).prod
        (gammaMeasure (r : ℝ) (1 / 2)) := by
      rw [htop, htail]

def h1TopTailDataToParameter {N : ℕ}
    (p : (ComplexUnitSphere N × ℝ) × ℝ) :
    ℝ × ComplexUnitSphere N :=
  (LogdetLean.gammaRatio (p.2, p.1.2), p.1.1)

theorem measurable_h1TopTailDataToParameter {N : ℕ} :
    Measurable (h1TopTailDataToParameter (N := N)) := by
  unfold h1TopTailDataToParameter LogdetLean.gammaRatio
  fun_prop

theorem map_h1TopTailDataToParameter_product {N r : ℕ}
    (hN : 1 ≤ N) (hr : 1 ≤ r) :
    Measure.map (h1TopTailDataToParameter (N := N))
        (((complexUnitSphereProbabilityMeasure N).prod
          (gammaMeasure (N : ℝ) (1 / 2))).prod
          (gammaMeasure (r : ℝ) (1 / 2))) =
      (betaMeasure (r : ℝ) (N : ℝ)).prod
        (complexUnitSphereProbabilityMeasure N) := by
  let σ := complexUnitSphereProbabilityMeasure N
  let γN := gammaMeasure (N : ℝ) (1 / 2)
  let γr := gammaMeasure (r : ℝ) (1 / 2)
  let assoc : (ComplexUnitSphere N × ℝ) × ℝ →
      ComplexUnitSphere N × (ℝ × ℝ) :=
    MeasurableEquiv.prodAssoc
  let swapEnergy : ComplexUnitSphere N × (ℝ × ℝ) →
      ComplexUnitSphere N × (ℝ × ℝ) :=
    Prod.map id Prod.swap
  let takeRatio : ComplexUnitSphere N × (ℝ × ℝ) →
      ComplexUnitSphere N × ℝ :=
    Prod.map id LogdetLean.gammaRatio
  let swapOut : ComplexUnitSphere N × ℝ →
      ℝ × ComplexUnitSphere N := Prod.swap
  let _ : IsProbabilityMeasure σ :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  let _ : IsProbabilityMeasure γN :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  let _ : IsProbabilityMeasure γr :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  let _ : IsProbabilityMeasure (betaMeasure (r : ℝ) (N : ℝ)) :=
    isProbabilityMeasureBeta (by positivity) (by positivity)
  have hassocMeas : Measurable assoc := by
    exact MeasurableEquiv.prodAssoc.measurable
  have hswapEnergyMeas : Measurable swapEnergy := by
    exact measurable_id.prodMap measurable_swap
  have hgammaRatioMeas : Measurable LogdetLean.gammaRatio := by
    unfold LogdetLean.gammaRatio
    fun_prop
  have htakeRatioMeas : Measurable takeRatio := by
    exact measurable_id.prodMap hgammaRatioMeas
  have hswapOutMeas : Measurable swapOut := measurable_swap
  have hassoc : Measure.map assoc ((σ.prod γN).prod γr) =
      σ.prod (γN.prod γr) :=
    (measurePreserving_prodAssoc σ γN γr).map_eq
  have hswapEnergy : Measure.map swapEnergy (σ.prod (γN.prod γr)) =
      σ.prod (γr.prod γN) := by
    calc
      Measure.map swapEnergy (σ.prod (γN.prod γr)) =
          (Measure.map id σ).prod
            (Measure.map Prod.swap (γN.prod γr)) := by
        exact (Measure.map_prod_map _ _ measurable_id measurable_swap).symm
      _ = σ.prod (γr.prod γN) := by
        rw [Measure.map_id, Measure.prod_swap]
  have hratio : Measure.map LogdetLean.gammaRatio (γr.prod γN) =
      betaMeasure (r : ℝ) (N : ℝ) := by
    exact LogdetLean.map_gammaRatio_prod_gamma
      (by positivity) (by positivity) (by norm_num)
  have htakeRatio : Measure.map takeRatio (σ.prod (γr.prod γN)) =
      σ.prod (betaMeasure (r : ℝ) (N : ℝ)) := by
    calc
      Measure.map takeRatio (σ.prod (γr.prod γN)) =
          (Measure.map id σ).prod
            (Measure.map LogdetLean.gammaRatio (γr.prod γN)) := by
        exact (Measure.map_prod_map _ _ measurable_id (by
          unfold LogdetLean.gammaRatio
          fun_prop)).symm
      _ = σ.prod (betaMeasure (r : ℝ) (N : ℝ)) := by
        rw [Measure.map_id, hratio]
  have hfun : h1TopTailDataToParameter (N := N) =
      swapOut ∘ takeRatio ∘ swapEnergy ∘ assoc := by
    funext p
    rfl
  rw [hfun, ← Measure.map_map hswapOutMeas
      (htakeRatioMeas.comp (hswapEnergyMeas.comp hassocMeas)),
    ← Measure.map_map htakeRatioMeas
      (hswapEnergyMeas.comp hassocMeas),
    ← Measure.map_map hswapEnergyMeas hassocMeas,
    hassoc, hswapEnergy, htakeRatio]
  exact Measure.prod_swap

def h1AmbientGaussianParameter {N r : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℂ (Fin (N + r))) :
    ℝ × ComplexUnitSphere N :=
  h1TopTailDataToParameter (h1AmbientTopTailData (r := r) hN x)

theorem measurable_h1AmbientGaussianParameter {N r : ℕ} (hN : 1 ≤ N) :
    Measurable (h1AmbientGaussianParameter (r := r) hN) :=
  measurable_h1TopTailDataToParameter.comp
    (measurable_h1AmbientTopTailData (r := r) hN)

theorem map_h1AmbientGaussianParameter_stdGaussian {N r : ℕ}
    (hN : 1 ≤ N) (hr : 1 ≤ r) :
    Measure.map (h1AmbientGaussianParameter (r := r) hN)
        (stdGaussian (EuclideanSpace ℂ (Fin (N + r)))) =
      (betaMeasure (r : ℝ) (N : ℝ)).prod
        (complexUnitSphereProbabilityMeasure N) := by
  rw [show h1AmbientGaussianParameter (r := r) hN =
      h1TopTailDataToParameter ∘ h1AmbientTopTailData (r := r) hN by rfl]
  rw [← Measure.map_map measurable_h1TopTailDataToParameter
    (measurable_h1AmbientTopTailData (r := r) hN),
    map_h1AmbientTopTailData_stdGaussian hN hr,
    map_h1TopTailDataToParameter_product hN hr]

theorem h1AmbientGaussianParameter_pos_smul {N r : ℕ}
    (hN : 1 ≤ N) (a : ℝ) (ha : 0 < a)
    (x : EuclideanSpace ℂ (Fin (N + r))) :
    h1AmbientGaussianParameter (r := r) hN (a • x) =
      h1AmbientGaussianParameter (r := r) hN x := by
  unfold h1AmbientGaussianParameter h1TopTailDataToParameter
    h1AmbientTopTailData h1TopDirectionEnergy
  dsimp only
  apply Prod.ext
  · unfold LogdetLean.gammaRatio
    simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    have ha0 : a ≠ 0 := ne_of_gt ha
    field_simp
  · simp only [map_smul]
    exact h1GaussianComplexSphereDirection_pos_smul hN a ha _

def h1AmbientSphereParameter {N r : ℕ} (hN : 1 ≤ N)
    (z : ComplexUnitSphere (N + r)) : ℝ × ComplexUnitSphere N :=
  h1AmbientGaussianParameter (r := r) hN z.1

theorem measurable_h1AmbientSphereParameter {N r : ℕ} (hN : 1 ≤ N) :
    Measurable (h1AmbientSphereParameter (r := r) hN) :=
  (measurable_h1AmbientGaussianParameter (r := r) hN).comp
    measurable_subtype_coe

theorem map_h1AmbientSphereParameter_uniform {N r : ℕ}
    (hN : 1 ≤ N) (hr : 1 ≤ r) :
    Measure.map (h1AmbientSphereParameter (r := r) hN)
        (complexUnitSphereProbabilityMeasure (N + r)) =
      (betaMeasure (r : ℝ) (N : ℝ)).prod
        (complexUnitSphereProbabilityMeasure N) := by
  let E := EuclideanSpace ℂ (Fin (N + r))
  have hNr : 1 ≤ N + r := by omega
  letI : Nonempty (Fin (N + r)) := Fin.pos_iff_nonempty.mp (by omega)
  have hzero : ∀ᵐ x ∂(stdGaussian E), x ≠ 0 := by
    simpa [ae_iff] using stdGaussian_zero_singleton (E := E)
  have hae :
      (h1AmbientSphereParameter (r := r) hN ∘
        h1GaussianComplexSphereDirection hNr) =ᵐ[(stdGaussian E)]
      h1AmbientGaussianParameter (r := r) hN := by
    filter_upwards [hzero] with x hx
    unfold Function.comp h1AmbientSphereParameter
    rw [coe_h1GaussianComplexSphereDirection_of_ne hNr hx]
    have hnormpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    rw [h1_unitDirection_eq_inv_norm_smul x hx]
    exact h1AmbientGaussianParameter_pos_smul hN ‖x‖⁻¹
      (inv_pos.mpr hnormpos) x
  calc
    Measure.map (h1AmbientSphereParameter (r := r) hN)
        (complexUnitSphereProbabilityMeasure (N + r)) =
        Measure.map (h1AmbientSphereParameter (r := r) hN)
          (Measure.map (h1GaussianComplexSphereDirection hNr)
            (stdGaussian E)) := by
      rw [map_h1GaussianComplexSphereDirection_stdGaussian hNr]
    _ = Measure.map
        (h1AmbientSphereParameter (r := r) hN ∘
          h1GaussianComplexSphereDirection hNr) (stdGaussian E) := by
      exact Measure.map_map
        (measurable_h1AmbientSphereParameter (r := r) hN)
        (measurable_h1GaussianComplexSphereDirection hNr)
    _ = Measure.map (h1AmbientGaussianParameter (r := r) hN)
        (stdGaussian E) := Measure.map_congr hae
    _ = (betaMeasure (r : ℝ) (N : ℝ)).prod
        (complexUnitSphereProbabilityMeasure N) :=
      map_h1AmbientGaussianParameter_stdGaussian hN hr



end
end LogdetLean.GramHafnian.UltimateHiding.Dense

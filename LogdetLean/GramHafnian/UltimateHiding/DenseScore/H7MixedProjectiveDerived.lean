import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7ProjectiveHessian
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7CentralLineDerived
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Tactic

/-!
# Exact mixed projective field for H7

The central-shift cocycle identifies the Hessian at a point of the central
line with the normalized Hessian at the inverse-centrally scaled state.
After the already internal fixed-state projective contraction, the derivative
at the origin is exactly the mixed scalar--quadratic density.
-/

open Function MeasureTheory Set
open scoped Matrix Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

attribute [local instance 2000] Real.normedAddCommGroup
  NormedAlgebra.toNormedSpace

private abbrev H7AlgebraRealHasDerivAt
    (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
    (NormedAlgebra.toNormedSpace ℝ).toModule _ _ f f' x

/-- The order-two local line restriction identity used to contract the
literal Hessian against a centered projective direction. -/
private theorem iteratedDeriv_line_eq_iteratedFDeriv_diag_two_of_contDiffAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V → ℝ) (hf : ContDiffAt ℝ 2 f 0) (x : V) :
    iteratedDeriv 2 (fun t : ℝ ↦ f (t • x)) 0 =
      iteratedFDeriv ℝ 2 f 0 ![x, x] := by
  let L : ℝ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℝ).smulRight x
  have hline : (fun t : ℝ ↦ f (t • x)) = f ∘ L := by
    funext t
    simp [L]
  rcases hf.contDiffOn' le_rfl (by norm_num) with ⟨s, hs_open, h0s, hfs⟩
  have hfs' : ContDiffOn ℝ 2 f s := by simpa using hfs
  have hpre_open : IsOpen (L ⁻¹' s) := hs_open.preimage L.continuous
  have h0pre : (0 : ℝ) ∈ L ⁻¹' s := by simpa [L] using h0s
  have hcompAt : ContDiffAt ℝ 2 (f ∘ L) 0 := by
    have hfL0 : ContDiffAt ℝ 2 f (L (0 : ℝ)) := by simpa [L] using hf
    exact hfL0.comp (0 : ℝ) L.contDiff.contDiffAt
  rw [hline,
    ← iteratedDerivWithin_eq_iteratedDeriv hpre_open.uniqueDiffOn hcompAt h0pre,
    iteratedDerivWithin_eq_iteratedFDerivWithin,
    L.iteratedFDerivWithin_comp_right hfs' hs_open.uniqueDiffOn
      hpre_open.uniqueDiffOn h0pre (by norm_num)]
  simp only [map_zero]
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hs_open.uniqueDiffOn hf h0s]
  have hdiag : (fun _ : Fin 2 ↦ x) = ![x, x] := by
    funext i
    fin_cases i <;> rfl
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, L, hdiag]

theorem h7_concreteCOEExponent_pos_of_boundary
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K) :
    0 < concreteCOEExponent N K := by
  have hcast : (2 : ℝ) * (N : ℝ) + 1 < (K : ℝ) := by
    exact_mod_cast (show 2 * N + 1 < K by omega)
  unfold concreteCOEExponent
  linarith

/-- The fixed-state projective Hessian contraction is the literal centered
quadratic density. -/
theorem h7ProjectiveHessianAverage_zero_eq_centeredQuadraticDensity
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    h7ProjectiveHessianAverageCLM N
        (iteratedFDeriv ℝ 2 (h16CoordinateLikelihoodCore K A) 0) =
      concreteCenteredQuadraticDensity N K A := by
  rw [h7ProjectiveHessianAverageCLM_apply hN]
  calc
    (∫ v : ComplexUnitSphere N,
        iteratedFDeriv ℝ 2 (h16CoordinateLikelihoodCore K A) 0
          ![concreteMatrixRealCoordinates
              (concreteCenteredOrbitalDirection N v),
            concreteMatrixRealCoordinates
              (concreteCenteredOrbitalDirection N v)]
        ∂(complexUnitSphereProbabilityMeasure N)) =
        ∫ v : ComplexUnitSphere N,
          concreteCenteredRankOneSecondDensityScore N K v A
          ∂(complexUnitSphereProbabilityMeasure N) := by
      apply integral_congr_ae
      filter_upwards [] with v
      let q := concreteMatrixRealCoordinates
        (concreteCenteredOrbitalDirection N v)
      rw [← iteratedDeriv_line_eq_iteratedFDeriv_diag_two_of_contDiffAt
        (h16CoordinateLikelihoodCore K A)
        ((h16CoordinateLikelihoodCore_contDiffAt_top A hsupport).of_le
          (by norm_num)) q]
      rw [show (fun t : ℝ ↦ h16CoordinateLikelihoodCore K A (t • q)) =
          (fun t : ℝ ↦ concreteCenteredLikelihoodCore K v t A) by
        simpa only [q] using h16CoordinateLikelihoodCore_centered_line hN v A]
      change concreteCenteredDensityScore 2 N K v A = _
      exact coeCorner_centeredDensityScore_two_eq_explicit_external_derived
        hN hboundary v A hsymm hsupport
    _ = concreteCenteredQuadraticDensity N K A := by
      exact integral_concreteCenteredRankOneSecondDensityScore_eq_density
        hN (h7_concreteCOEExponent_ne_zero_of_boundary hboundary) A
        (concreteCOERMatrix_isSymm_of_support A hsymm hsupport)
        (concreteCOEY_trace_im_eq_zero_of_support A hsupport)
        (concreteCOEY_sq_trace_im_eq_zero_of_support A hsupport)
        (concreteCOEWMatrix_trace_re A
          (h7_concreteCOEExponent_ne_zero_of_boundary hboundary))
        (concreteCOEWMatrix_mul_Y_trace_re A
          (h7_concreteCOEExponent_ne_zero_of_boundary hboundary))
        (concreteCOERMatrix_sq_trace_re A
          (h7_concreteCOEExponent_pos_of_boundary hboundary) hsupport)

/-- At nonnegative central time, the literal Hessian factors into the
central likelihood and the Hessian of the inverse-centrally scaled state. -/
theorem h16CoordinateLikelihoodCore_iteratedFDeriv_two_central_shift
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    {s : ℝ} (hs : 0 ≤ s) :
    iteratedFDeriv ℝ 2 (h16CoordinateLikelihoodCore K A)
        (s • concreteMatrixRealCoordinates (1 : ConcreteMatrixState N)) =
      h7CentralLikelihoodCore K A s •
        iteratedFDeriv ℝ 2
          (h16CoordinateLikelihoodCore K
            (h7InverseCentralScaledState A s)) 0 := by
  let i := concreteMatrixRealCoordinates (1 : ConcreteMatrixState N)
  let A' := h7InverseCentralScaledState A s
  let f := h16CoordinateLikelihoodCore K A
  let f' := h16CoordinateLikelihoodCore K A'
  have hsupport' : coeCornerSupport (unscaleCOECorner K A') := by
    simpa only [A'] using h7InverseCentralScaledState_support A hsupport hs
  have heq : (fun x : ConcreteMatrixRealCoordinates N ↦ f (s • i + x))
      =ᶠ[nhds 0] (fun x ↦ h7CentralLikelihoodCore K A s * f' x) := by
    simpa only [f, f', i, A', smul_eq_mul] using
      h16CoordinateLikelihoodCore_central_translate_eventuallyEq
        A hsupport hs
  have hder0 := (heq.iteratedFDeriv ℝ 2).eq_of_nhds
  have hadd := iteratedFDeriv_comp_add_left
    (𝕜 := ℝ) (f := f) 2 (s • i)
      (0 : ConcreteMatrixRealCoordinates N)
  have hf' : ContDiffAt ℝ 2 f' 0 :=
    (h16CoordinateLikelihoodCore_contDiffAt_top A' hsupport').of_le
      (by norm_num)
  have hsmul := iteratedFDeriv_const_smul_apply'
    (a := h7CentralLikelihoodCore K A s) hf'
  calc
    iteratedFDeriv ℝ 2 (h16CoordinateLikelihoodCore K A)
          (s • concreteMatrixRealCoordinates (1 : ConcreteMatrixState N)) =
        iteratedFDeriv ℝ 2 (fun x : ConcreteMatrixRealCoordinates N ↦
          f (s • i + x)) 0 := by
            simpa only [f, i, add_zero] using hadd.symm
    _ = iteratedFDeriv ℝ 2
          (fun x : ConcreteMatrixRealCoordinates N ↦
            h7CentralLikelihoodCore K A s * f' x) 0 := hder0
    _ = h7CentralLikelihoodCore K A s •
          iteratedFDeriv ℝ 2 f' 0 := hsmul
    _ = _ := by rfl

/-- The averaged Hessian path obeys the exact scalar product identity on the
nonnegative central half-line. -/
theorem h7ProjectiveHessianPath_eq_product_of_nonneg
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    {s : ℝ} (hs : 0 ≤ s) :
    h7ProjectiveHessianPath K A s =
      h7CentralLikelihoodCore K A s *
        concreteCenteredQuadraticDensity N K
          (h7InverseCentralScaledState A s) := by
  have hsupport' := h7InverseCentralScaledState_support A hsupport hs
  have hsymm' := h7InverseCentralScaledState_isSymm A hsymm s
  unfold h7ProjectiveHessianPath
  rw [h16CoordinateLikelihoodCore_iteratedFDeriv_two_central_shift
    A hsupport hs]
  rw [map_smul]
  change h7CentralLikelihoodCore K A s *
      h7ProjectiveHessianAverageCLM N
        (iteratedFDeriv ℝ 2
          (h16CoordinateLikelihoodCore K
            (h7InverseCentralScaledState A s)) 0) = _
  rw [h7ProjectiveHessianAverage_zero_eq_centeredQuadraticDensity
    hN hboundary (h7InverseCentralScaledState A s) hsymm' hsupport']

/-- Exact mixed projective mean required by the H7 witness. -/
theorem h7ProjectiveMixedMean_derived
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (∫ v : ComplexUnitSphere N,
      (h7CoordinateDifferential K A).form
        (concreteMatrixRealCoordinates (1 : ConcreteMatrixState N))
        (concreteMatrixRealCoordinates
          (concreteCenteredOrbitalDirection N v))
        (concreteMatrixRealCoordinates
          (concreteCenteredOrbitalDirection N v))
      ∂(complexUnitSphereProbabilityMeasure N)) =
      concreteMixedScalarQuadraticDensity N K A := by
  let c := h7CentralLikelihoodCore K A
  let q : ℝ → ℝ := fun s ↦ concreteCenteredQuadraticDensity N K
    (h7InverseCentralScaledState A s)
  let G := h7ProjectiveHessianPath K A
  have hG := h7ProjectiveHessianPath_hasDerivAt hN A hsupport
  have hc3 := h7CentralLikelihoodCore_contDiffAt_three A hsupport
  have hcdiff : DifferentiableAt ℝ c 0 :=
    hc3.differentiableAt (by norm_num)
  have hc0 : c 0 = 1 := by
    simpa only [c] using h7CentralLikelihoodCore_zero_on_support A hsupport
  have hlogjet :
      iteratedDeriv 1 (fun t : ℝ ↦ Real.log (c t)) 0 =
        concreteCentralLogScoreOne N K A := by
    rw [show (fun t : ℝ ↦ Real.log (c t)) =
        (fun t : ℝ ↦ Real.log (h7CentralLikelihoodCore K A t)) by rfl]
    have heqlog := h7CentralLikelihoodCore_log_eventuallyEq_model A hsupport
    rw [heqlog.iteratedDeriv_eq 1]
    exact h7CentralLogModel_jet_one_derived hboundary A hsupport
  have hlogder : deriv (fun t : ℝ ↦ Real.log (c t)) 0 =
      concreteCentralLogScoreOne N K A := by
    simpa only [iteratedDeriv_one] using hlogjet
  have hlogHas := hcdiff.hasDerivAt.log (by rw [hc0]; norm_num)
  have hcder : deriv c 0 = concreteCentralLogScoreOne N K A := by
    calc
      deriv c 0 = deriv (fun t : ℝ ↦ Real.log (c t)) 0 := by
        simpa only [hc0, div_one] using hlogHas.deriv.symm
      _ = concreteCentralLogScoreOne N K A := hlogder
  have hcHas := hcdiff.hasDerivAt.congr_deriv hcder
  have hqHas := concreteCenteredQuadraticDensity_inverseCentralScaledState_hasDerivAt
    hN A hsupport (h7_concreteCOEExponent_ne_zero_of_boundary hboundary)
  have hprod0 := hcHas.mul hqHas
  have hprod := hprod0.congr_deriv (g' :=
      concreteMixedScalarQuadraticDensity N K A) (by
    simp only [hc0, h7InverseCentralScaledState_zero, one_mul]
    unfold concreteMixedScalarQuadraticDensity
    ring)
  have hGwithin := hG.hasDerivWithinAt (s := Ici 0)
  have hprodWithinG := (hprod.hasDerivWithinAt (s := Ici 0)).congr_of_mem
    (f₁ := G) (fun s hs ↦ by
      exact h7ProjectiveHessianPath_eq_product_of_nonneg
        hN hboundary A hsymm hsupport hs) self_mem_Ici
  exact (uniqueDiffWithinAt_Ici 0).eq_deriv (Ici 0)
    hGwithin hprodWithinG

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

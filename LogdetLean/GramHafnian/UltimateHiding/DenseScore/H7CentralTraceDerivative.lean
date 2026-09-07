import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7CentralLineDerived
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteMixedCubicDefinitions
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic

/-!
# Central derivative of the explicit centered quadratic density

This module differentiates the literal resolvent traces under the inverse
central scaling `A \mapsto exp (-2s) A`.  It supplies the sign-critical
`-X_I` term in the H7 mixed generator calculation.  No density or witness
identity is assumed.
-/

open Function Matrix
open scoped Matrix Topology ComplexConjugate ComplexOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

@[reducible, local instance]
def h7MixedMatrixNormedAddCommGroup {N : ℕ} :
    NormedAddCommGroup (ConcreteMatrixState N) :=
  Matrix.linftyOpNormedAddCommGroup

@[reducible, local instance]
def h7MixedMatrixNormedSpace {N : ℕ} :
    NormedSpace ℂ (ConcreteMatrixState N) := Matrix.linftyOpNormedSpace

@[reducible, local instance]
def h7MixedMatrixRealNormedSpace {N : ℕ} :
    NormedSpace ℝ (ConcreteMatrixState N) := Matrix.linftyOpNormedSpace

@[local instance]
abbrev h7MixedMatrixAddCommGroup {N : ℕ} :
    AddCommGroup (ConcreteMatrixState N) :=
  h7MixedMatrixNormedAddCommGroup.toAddCommGroup

@[local instance]
abbrev h7MixedMatrixModule {N : ℕ} :
    Module ℂ (ConcreteMatrixState N) :=
  h7MixedMatrixNormedSpace.toModule

@[local instance]
abbrev h7MixedMatrixRealModule {N : ℕ} :
    Module ℝ (ConcreteMatrixState N) :=
  h7MixedMatrixRealNormedSpace.toModule

@[local instance]
abbrev h7MixedMatrixPseudoMetricSpace {N : ℕ} :
    PseudoMetricSpace (ConcreteMatrixState N) :=
  h7MixedMatrixNormedAddCommGroup.toPseudoMetricSpace

@[local instance]
abbrev h7MixedMatrixUniformSpace {N : ℕ} :
    UniformSpace (ConcreteMatrixState N) :=
  h7MixedMatrixPseudoMetricSpace.toUniformSpace

@[local instance]
abbrev h7MixedMatrixTopologicalSpace {N : ℕ} :
    TopologicalSpace (ConcreteMatrixState N) :=
  h7MixedMatrixUniformSpace.toTopologicalSpace

@[reducible, local instance]
def h7MixedMatrixNormedRing {N : ℕ} :
    NormedRing (ConcreteMatrixState N) := Matrix.linftyOpNormedRing

@[reducible, local instance]
def h7MixedMatrixNormedAlgebra {N : ℕ} :
    NormedAlgebra ℂ (ConcreteMatrixState N) := Matrix.linftyOpNormedAlgebra

@[reducible, local instance]
def h7MixedMatrixRealNormedAlgebra {N : ℕ} :
    NormedAlgebra ℝ (ConcreteMatrixState N) := Matrix.linftyOpNormedAlgebra

private def h7MixedTraceCLM (N : ℕ) :
    ConcreteMatrixState N →L[ℝ] ℂ :=
  (Matrix.traceLinearMap (Fin N) ℝ ℂ).toContinuousLinearMap

@[simp]
private theorem h7MixedTraceCLM_apply {N : ℕ}
    (M : ConcreteMatrixState N) :
    (h7MixedTraceCLM N) M = Matrix.trace M := by
  rfl

/-- The concrete state after inverse central congruence by time `s`. -/
def h7InverseCentralScaledState {N : ℕ}
    (A : ConcreteMatrixState N) (s : ℝ) : ConcreteMatrixState N :=
  Real.exp (-2 * s) • A

@[simp]
theorem h7InverseCentralScaledState_zero {N : ℕ}
    (A : ConcreteMatrixState N) :
    h7InverseCentralScaledState A 0 = A := by
  simp [h7InverseCentralScaledState]

theorem unscaleCOECorner_inverseCentralScaledState
    {N K : ℕ} (A : ConcreteMatrixState N) (s : ℝ) :
    unscaleCOECorner K (h7InverseCentralScaledState A s) =
      Real.exp (-2 * s) • unscaleCOECorner K A := by
  unfold h7InverseCentralScaledState unscaleCOECorner
  ext i j
  simp only [Matrix.smul_apply, Complex.real_smul]
  ring

private theorem h7_hasDerivAt_nonsingInv_of_hasDerivAt
    {N : ℕ} {F : ℝ → ConcreteMatrixState N}
    {x : ℝ} {F' : ConcreteMatrixState N}
    (hF : HasDerivAt F F' x) (hunit : IsUnit (F x)) :
    HasDerivAt (fun s : ℝ => (F s)⁻¹)
      (-((F x)⁻¹ * F' * (F x)⁻¹)) x := by
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℝ) hunit.unit
  have hcomp := hinv.comp_hasDerivAt x hF
  have hinvEq : (F x)⁻¹ =
      (↑(hunit.unit⁻¹) : ConcreteMatrixState N) := by
    calc
      (F x)⁻¹ = Ring.inverse (F x) := nonsing_inv_eq_ringInverse _
      _ = Ring.inverse (hunit.unit : ConcreteMatrixState N) :=
        congrArg Ring.inverse hunit.unit_spec.symm
      _ = (↑(hunit.unit⁻¹) : ConcreteMatrixState N) := Ring.inverse_unit _
  convert hcomp using 1 <;> try rfl
  · funext s
    simp only [Function.comp_apply, nonsing_inv_eq_ringInverse]
  · simp only [ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.mulLeftRight_apply]
    rw [hinvEq]

private theorem h7_hasDerivAt_exp_neg_four :
    HasDerivAt (fun s : ℝ => Real.exp (-4 * s)) (-4) 0 := by
  have hlin : HasDerivAt (fun s : ℝ => -4 * s) (-4) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (-4)
  simpa [Function.comp_def] using
    (Real.hasDerivAt_exp (-4 * (0 : ℝ))).comp 0 hlin

private theorem h7_scaled_resolvent_hasDerivAt
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    HasDerivAt
      (fun s : ℝ => concreteCOEZ K (h7InverseCentralScaledState A s))
      ((-4 : ℝ) •
        (concreteCOEZ K A + concreteCOEZ K A * concreteCOEZ K A)) 0 := by
  let C := unscaleCOECorner K A
  let B : ConcreteMatrixState N := C.conjTranspose * C
  let F : ℝ → ConcreteMatrixState N := fun s =>
    1 - Real.exp (-4 * s) • B
  let J : ℝ → ConcreteMatrixState N := fun s => (F s)⁻¹
  have hq := h7_hasDerivAt_exp_neg_four
  have hF : HasDerivAt F ((4 : ℝ) • B) 0 := by
    simpa [F] using (hq.smul_const B).const_sub 1
  have hFzero : F 0 = 1 - B := by
    simp [F]
  have hunit : IsUnit (F 0) := by
    rw [hFzero]
    simpa only [B, C] using hsupport.isUnit
  have hJ := h7_hasDerivAt_nonsingInv_of_hasDerivAt hF hunit
  let J0 : ConcreteMatrixState N := (1 - B)⁻¹
  have hJzero : J 0 = J0 := by
    simp [J, F, J0]
  have hJ' : HasDerivAt J ((-4 : ℝ) • (J0 * B * J0)) 0 := by
    have hder :
        -((F 0)⁻¹ * ((4 : ℝ) • B) * (F 0)⁻¹) =
          (-4 : ℝ) • (J0 * B * J0) := by
      rw [hFzero]
      dsimp only [J0]
      simp only [Matrix.mul_smul, Matrix.smul_mul, neg_smul]
    have hJ0 : HasDerivAt J
        (-((F 0)⁻¹ * ((4 : ℝ) • B) * (F 0)⁻¹)) 0 := by
      simpa only [J] using hJ
    exact hJ0.congr_deriv hder
  have hcore : HasDerivAt
      (fun s : ℝ => C * J s * C.conjTranspose)
      ((-4 : ℝ) • (C * J0 * B * J0 * C.conjTranspose)) 0 := by
    have hcore0 : HasDerivAt
        (fun s : ℝ => C * J s * C.conjTranspose)
        (C * ((-4 : ℝ) • (J0 * B * J0)) * C.conjTranspose) 0 :=
      (hJ'.const_mul C).mul_const C.conjTranspose
    apply hcore0.congr_deriv
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    noncomm_ring
  have hqCore : HasDerivAt
      (fun s : ℝ => Real.exp (-4 * s) •
        (C * J s * C.conjTranspose))
      ((-4 : ℝ) • (C * J0 * C.conjTranspose) +
        ((-4 : ℝ) • (C * J0 * B * J0 * C.conjTranspose))) 0 := by
    have hprod := hq.smul hcore
    have hprod' : HasDerivAt
        (fun s : ℝ => Real.exp (-4 * s) •
          (C * J s * C.conjTranspose))
        (Real.exp (-4 * 0) •
            ((-4 : ℝ) • (C * J0 * B * J0 * C.conjTranspose)) +
          (-4 : ℝ) • (C * J 0 * C.conjTranspose)) 0 := by
      apply hprod.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall fun _ => rfl
    apply hprod'.congr_deriv
    rw [hJzero]
    norm_num
    abel
  have hpath :
      (fun s : ℝ => concreteCOEZ K (h7InverseCentralScaledState A s)) =
      (fun s : ℝ => Real.exp (-4 * s) •
        (C * J s * C.conjTranspose)) := by
    funext s
    have hsq : Real.exp (-2 * s) * Real.exp (-2 * s) =
        Real.exp (-4 * s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    unfold concreteCOEZ
    rw [unscaleCOECorner_inverseCentralScaledState]
    dsimp only [C, B, F, J]
    simp only [Matrix.conjTranspose_smul, star_trivial,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hsq]
  rw [hpath]
  apply hqCore.congr_deriv
  unfold concreteCOEZ
  dsimp only
  change
    (-4 : ℝ) • (C * J0 * C.conjTranspose) +
      (-4 : ℝ) • (C * J0 * B * J0 * C.conjTranspose) =
    (-4 : ℝ) • (C * J0 * C.conjTranspose +
      (C * J0 * C.conjTranspose) * (C * J0 * C.conjTranspose))
  have hsquare :
      (C * J0 * C.conjTranspose) * (C * J0 * C.conjTranspose) =
        C * J0 * B * J0 * C.conjTranspose := by
    dsimp only [B]
    noncomm_ring
  rw [hsquare, smul_add]

/-- `Tr Y` has derivative `-4(Tr Y + Tr Y²/c)` under inverse central
scaling. -/
theorem concreteCOETraceOne_inverseCentralScaledState_hasDerivAt
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    (hc : concreteCOEExponent N K ≠ 0) :
    HasDerivAt
      (fun s : ℝ => concreteCOETraceOne N K
        (h7InverseCentralScaledState A s))
      (-centralTraceOneDerivative (concreteCOEExponent N K)
        (concreteCOETraceOne N K A) (concreteCOETraceTwo N K A)) 0 := by
  have hZ := h7_scaled_resolvent_hasDerivAt A hsupport
  have hY := hZ.const_smul (((concreteCOEExponent N K : ℝ) : ℂ))
  have htr := (h7MixedTraceCLM N).hasFDerivAt.comp_hasDerivAt 0 hY
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 htr
  have hre' : HasDerivAt
      (fun s : ℝ => concreteCOETraceOne N K
        (h7InverseCentralScaledState A s))
      (Complex.reCLM ((h7MixedTraceCLM N)
        ((((concreteCOEExponent N K : ℝ) : ℂ)) •
          ((-4 : ℝ) • (concreteCOEZ K A +
            concreteCOEZ K A * concreteCOEZ K A))))) 0 := by
    apply hre.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun s => by
      simp only [Function.comp_apply, Pi.smul_apply]
      rfl
  have hder :
      Complex.reCLM ((h7MixedTraceCLM N)
        ((((concreteCOEExponent N K : ℝ) : ℂ)) •
          ((-4 : ℝ) • (concreteCOEZ K A +
            concreteCOEZ K A * concreteCOEZ K A)))) =
      -centralTraceOneDerivative (concreteCOEExponent N K)
        (concreteCOETraceOne N K A) (concreteCOETraceTwo N K A) := by
    rw [h7MixedTraceCLM_apply]
    simp only [Complex.reCLM_apply]
    change (Matrix.trace
      ((((concreteCOEExponent N K : ℝ) : ℂ)) •
        ((-4 : ℝ) • (concreteCOEZ K A +
          concreteCOEZ K A * concreteCOEZ K A)))).re = _
    unfold centralTraceOneDerivative concreteCOETraceOne concreteCOETraceTwo
      concreteRealTrace concreteCOEY
    simp only [Complex.reCLM_apply, Matrix.trace_smul, Matrix.trace_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_eq_mul, Complex.mul_re,
      Complex.add_re, Complex.sub_re, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    field_simp [hc]
    rw [Complex.smul_re]
    simp only [Complex.add_re, smul_eq_mul]
    ring
  rw [hder] at hre'
  exact hre'

/-- `Tr Y²` has derivative `-8(Tr Y² + Tr Y³/c)` under inverse central
scaling. -/
theorem concreteCOETraceTwo_inverseCentralScaledState_hasDerivAt
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    (hc : concreteCOEExponent N K ≠ 0) :
    HasDerivAt
      (fun s : ℝ => concreteCOETraceTwo N K
        (h7InverseCentralScaledState A s))
      (-centralTraceTwoDerivative (concreteCOEExponent N K)
        (concreteCOETraceTwo N K A) (concreteCOETraceThree N K A)) 0 := by
  have hZ := h7_scaled_resolvent_hasDerivAt A hsupport
  let dY : ConcreteMatrixState N :=
    (((concreteCOEExponent N K : ℝ) : ℂ)) •
      ((-4 : ℝ) • (concreteCOEZ K A +
        concreteCOEZ K A * concreteCOEZ K A))
  have hY0 :=
    hZ.const_smul (((concreteCOEExponent N K : ℝ) : ℂ))
  have hYfun :
      (fun s : ℝ => concreteCOEY N K
        (h7InverseCentralScaledState A s)) =ᶠ[nhds 0]
      ((((concreteCOEExponent N K : ℝ) : ℂ)) •
        (fun s : ℝ => concreteCOEZ K
          (h7InverseCentralScaledState A s))) := by
    exact Filter.Eventually.of_forall fun s => by
      rfl
  have hY1 := hY0.congr_of_eventuallyEq hYfun
  have hY := hY1.congr_deriv (g' := dY) (by rfl)
  have hYY := hY.mul hY
  have htr := (h7MixedTraceCLM N).hasFDerivAt.comp_hasDerivAt 0 hYY
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 htr
  have hre' : HasDerivAt
      (fun s : ℝ => concreteCOETraceTwo N K
        (h7InverseCentralScaledState A s))
      (Complex.reCLM ((h7MixedTraceCLM N)
        (dY * concreteCOEY N K A +
          concreteCOEY N K A * dY))) 0 := by
    have hre0 := hre.congr_deriv
      (g' := Complex.reCLM ((h7MixedTraceCLM N)
        (dY * concreteCOEY N K A +
          concreteCOEY N K A * dY))) (by
        simp only [h7InverseCentralScaledState_zero])
    apply hre0.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun s => by
      simp only [Function.comp_apply, Pi.mul_apply]
      rfl
  have hder :
      Complex.reCLM ((h7MixedTraceCLM N)
        (dY * concreteCOEY N K A +
          concreteCOEY N K A * dY)) =
      -centralTraceTwoDerivative (concreteCOEExponent N K)
        (concreteCOETraceTwo N K A) (concreteCOETraceThree N K A) := by
    rw [h7MixedTraceCLM_apply]
    simp only [Complex.reCLM_apply]
    change (Matrix.trace
      (dY * concreteCOEY N K A + concreteCOEY N K A * dY)).re = _
    unfold dY
    unfold centralTraceTwoDerivative concreteCOETraceTwo concreteCOETraceThree
      concreteRealTrace concreteCOEY
    simp only [Complex.reCLM_apply, Matrix.trace_add,
      Matrix.trace_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.add_mul, Matrix.mul_add, mul_assoc, smul_eq_mul,
      Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    field_simp [hc]
    simp only [Complex.smul_re, Complex.add_re, smul_eq_mul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    ring
  rw [hder] at hre'
  exact hre'

/-- The explicit R30 density differentiates with the generator sign `-X_I`
along inverse central scaling. -/
theorem concreteCenteredQuadraticDensity_inverseCentralScaledState_hasDerivAt
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    (hc : concreteCOEExponent N K ≠ 0) :
    HasDerivAt
      (fun s : ℝ => concreteCenteredQuadraticDensity N K
        (h7InverseCentralScaledState A s))
      (-concreteCentralDerivativeCenteredQuadraticDensity N K A) 0 := by
  have hOne := concreteCOETraceOne_inverseCentralScaledState_hasDerivAt
    A hsupport hc
  have hTwo := concreteCOETraceTwo_inverseCentralScaledState_hasDerivAt
    A hsupport hc
  let a := quadraticTraceCoeffTwo (N : ℝ) (concreteCOEExponent N K)
  let b := quadraticTraceCoeffSquare (N : ℝ) (concreteCOEExponent N K)
  let d := quadraticTraceCoeffOne (N : ℝ)
  let scale := 4 / ((N : ℝ) * ((N : ℝ) + 1))
  have hbracket : HasDerivAt
      (fun s : ℝ =>
        a * concreteCOETraceTwo N K (h7InverseCentralScaledState A s) +
        b * concreteCOETraceOne N K (h7InverseCentralScaledState A s) ^ 2 +
        d * concreteCOETraceOne N K (h7InverseCentralScaledState A s))
      (-centralDerivativeQuadraticTraceBracket (N : ℝ)
        (concreteCOEExponent N K)
        (concreteCOETraceOne N K A) (concreteCOETraceTwo N K A)
        (concreteCOETraceThree N K A)) 0 := by
    have hraw := ((hTwo.const_mul a).add
      ((hOne.mul hOne).const_mul b)).add (hOne.const_mul d)
    have hfun : HasDerivAt
        (fun s : ℝ =>
          a * concreteCOETraceTwo N K (h7InverseCentralScaledState A s) +
          b * concreteCOETraceOne N K (h7InverseCentralScaledState A s) ^ 2 +
          d * concreteCOETraceOne N K (h7InverseCentralScaledState A s))
        (a * (-centralTraceTwoDerivative (concreteCOEExponent N K)
              (concreteCOETraceTwo N K A) (concreteCOETraceThree N K A)) +
          b * ((-centralTraceOneDerivative (concreteCOEExponent N K)
                (concreteCOETraceOne N K A) (concreteCOETraceTwo N K A)) *
              concreteCOETraceOne N K A +
            concreteCOETraceOne N K A *
              (-centralTraceOneDerivative (concreteCOEExponent N K)
                (concreteCOETraceOne N K A) (concreteCOETraceTwo N K A))) +
          d * (-centralTraceOneDerivative (concreteCOEExponent N K)
            (concreteCOETraceOne N K A) (concreteCOETraceTwo N K A))) 0 := by
      have hraw0 := hraw.congr_deriv
        (g' :=
          a * (-centralTraceTwoDerivative (concreteCOEExponent N K)
                (concreteCOETraceTwo N K A) (concreteCOETraceThree N K A)) +
            b * ((-centralTraceOneDerivative (concreteCOEExponent N K)
                  (concreteCOETraceOne N K A) (concreteCOETraceTwo N K A)) *
                concreteCOETraceOne N K A +
              concreteCOETraceOne N K A *
                (-centralTraceOneDerivative (concreteCOEExponent N K)
                  (concreteCOETraceOne N K A) (concreteCOETraceTwo N K A))) +
            d * (-centralTraceOneDerivative (concreteCOEExponent N K)
              (concreteCOETraceOne N K A) (concreteCOETraceTwo N K A)))
        (by simp only [h7InverseCentralScaledState_zero])
      apply hraw0.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall fun s => by
        simp only [Pi.add_apply, Pi.mul_apply]
        ring
    apply hfun.congr_deriv
    unfold centralDerivativeQuadraticTraceBracket a b d
    ring
  have hscaled := hbracket.const_mul scale
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  have hscaled' : HasDerivAt
      (fun s : ℝ => concreteCenteredQuadraticDensity N K
        (h7InverseCentralScaledState A s))
      (scale *
        (-centralDerivativeQuadraticTraceBracket (N : ℝ)
          (concreteCOEExponent N K)
          (concreteCOETraceOne N K A) (concreteCOETraceTwo N K A)
          (concreteCOETraceThree N K A))) 0 := by
    apply hscaled.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun s => by
      unfold concreteCenteredQuadraticDensity
        concreteCenteredQuadraticTraceBracket
      change
        4 / ((N : ℝ) * ((N : ℝ) + 1)) *
            centeredQuadraticTraceBracket (N : ℝ)
              (concreteCOEExponent N K)
              (concreteCOETraceOne N K (h7InverseCentralScaledState A s))
              (concreteCOETraceTwo N K (h7InverseCentralScaledState A s)) =
          scale *
            (a * concreteCOETraceTwo N K (h7InverseCentralScaledState A s) +
              b * concreteCOETraceOne N K
                  (h7InverseCentralScaledState A s) ^ 2 +
              d * concreteCOETraceOne N K
                  (h7InverseCentralScaledState A s))
      rw [centeredQuadraticTraceBracket_collect hN0 hc]
  apply hscaled'.congr_deriv
  unfold concreteCentralDerivativeCenteredQuadraticDensity scale
  ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

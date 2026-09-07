import LogdetLean.GramHafnian.UltimateHiding.Dense.HaarRecursionExternal
import LogdetLean.GramHafnian.UltimateHiding.Dense.RadialConvolution

/-!
# Concrete radial factorization and the orbital kernel

The exact one-column Haar recursion already identifies the radial increment:
it is congruence by

`sqrt((m+1)/m) * (I + (sqrt q - 1) vv*)`,

with the literal beta and uniform-complex-sphere laws.  This file composes
those increments and proves, internally, the exact factorization of every
ambient Haar transpose-Gram law through its square (`m = K`) base law.

It also defines the paper's centered orbital kernel

`K_s mu = E_v (rho_(exp(s (vv* - I/N))))_* mu`

as an actual Markov kernel.  No commutation or score estimate is asserted in
this file.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

open LocalAnticoncentration

abbrev ConcreteMatrixState (N : ℕ) := Matrix (Fin N) (Fin N) ℂ

/-- The square-base law, named at the paper's semantic level.  When the
ambient dimension and retained-column count are both `K`, the underlying
unitary product is the `N x N` principal corner of `U Uᵀ`, hence a scaled
`COE(K)` corner.  The normalization in `concreteHaarAmbientLaw` is exactly
the paper's `sqrt K` scaling. -/
abbrev concreteScaledCOECornerLaw
    (H : UnitaryHaarProbabilityFamily) (N K : ℕ) :
    Measure (ConcreteMatrixState N) :=
  concreteHaarAmbientLaw H N K K

/-! ## The exact radial chain -/

/-- Starting from ambient dimension `K`, compose the first `r` concrete
one-column radial increments.  The newest increment acts on the left, matching
the convention `kernel ∘ₘ measure`. -/
def concreteRadialKernelChain (N K : ℕ) : ℕ → Kernel (ConcreteMatrixState N)
    (ConcreteMatrixState N)
  | 0 => Kernel.id
  | r + 1 => concreteOneColumnMatrixKernel (K + r) N ∘ₖ
      concreteRadialKernelChain N K r

@[simp]
theorem concreteRadialKernelChain_zero (N K : ℕ) :
    concreteRadialKernelChain N K 0 = Kernel.id := rfl

@[simp]
theorem concreteRadialKernelChain_succ (N K r : ℕ) :
    concreteRadialKernelChain N K (r + 1) =
      concreteOneColumnMatrixKernel (K + r) N ∘ₖ
        concreteRadialKernelChain N K r := rfl

/-- Every finite radial chain is a Markov kernel. -/
theorem concreteRadialKernelChain_isMarkov
    {N K : ℕ} (hN : 1 ≤ N) (hNK : N ≤ K) :
    ∀ r, IsMarkovKernel (concreteRadialKernelChain N K r) := by
  intro r
  induction r with
  | zero =>
      rw [concreteRadialKernelChain_zero]
      infer_instance
  | succ r ihr =>
      rw [concreteRadialKernelChain_succ]
      let _ : IsMarkovKernel (concreteRadialKernelChain N K r) := ihr
      let _ : IsMarkovKernel (concreteOneColumnMatrixKernel (K + r) N) :=
        concreteOneColumnMatrixKernel_isMarkov hN (by omega)
      infer_instance

/-- Offset form of the exact radial factorization.  All composition algebra
is kernel checked; the only non-foundational dependency is the already audited
complex-Stiefel one-column equality. -/
theorem concreteHaarAmbientLaw_radialFactorization_offset
    (H : UnitaryHaarProbabilityFamily) {N K : ℕ}
    (hN : 1 ≤ N) (hNK : N ≤ K) : ∀ r,
    concreteHaarAmbientLaw H N K (K + r) =
      radialConvolution (concreteRadialKernelChain N K r)
        (concreteHaarAmbientLaw H N K K) := by
  intro r
  induction r with
  | zero =>
      simp [radialConvolution]
  | succ r ihr =>
      calc
        concreteHaarAmbientLaw H N K (K + (r + 1)) =
            concreteHaarAmbientLaw H N K ((K + r) + 1) := by congr 1
        _ = concreteOneColumnMatrixKernel (K + r) N ∘ₘ
              concreteHaarAmbientLaw H N K (K + r) :=
            concreteHaarOneColumnRecursion_step_eq H hN hNK (by omega)
        _ = concreteOneColumnMatrixKernel (K + r) N ∘ₘ
              radialConvolution (concreteRadialKernelChain N K r)
                (concreteHaarAmbientLaw H N K K) := by rw [ihr]
        _ = radialConvolution (concreteRadialKernelChain N K (r + 1))
              (concreteHaarAmbientLaw H N K K) := by
            rw [concreteRadialKernelChain_succ]
            unfold radialConvolution
            exact Measure.comp_assoc

/-- Paper-facing exact factorization at an arbitrary valid ambient dimension.
The concrete radial kernel is the finite chain of beta/sphere congruence
increments, and the common angular base is the literal square Haar law. -/
theorem concreteHaarAmbientLaw_radialFactorization
    (H : UnitaryHaarProbabilityFamily) {N K m : ℕ}
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKm : K ≤ m) :
    concreteHaarAmbientLaw H N K m =
      radialConvolution (concreteRadialKernelChain N K (m - K))
        (concreteHaarAmbientLaw H N K K) := by
  have hsum : K + (m - K) = m := Nat.add_sub_of_le hKm
  simpa only [hsum] using
    (concreteHaarAmbientLaw_radialFactorization_offset H hN hNK (m - K))

/-- The same factorization with the square law explicitly named as the scaled
COE-corner base used by the dense score proof. -/
theorem concreteHaarAmbientLaw_radialFactorization_fromCOE
    (H : UnitaryHaarProbabilityFamily) {N K m : ℕ}
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKm : K ≤ m) :
    concreteHaarAmbientLaw H N K m =
      radialConvolution (concreteRadialKernelChain N K (m - K))
        (concreteScaledCOECornerLaw H N K) :=
  concreteHaarAmbientLaw_radialFactorization H hN hNK hKm

/-- The preceding theorem is literally the abstract `RadialFactorization`
predicate, indexed by the offset from the square base. -/
theorem concreteHaarAmbientLaw_isRadialFactorization
    (H : UnitaryHaarProbabilityFamily) {N K : ℕ}
    (hN : 1 ≤ N) (hNK : N ≤ K) :
    RadialFactorization
      (concreteHaarAmbientLaw H N K K)
      (fun r ↦ concreteHaarAmbientLaw H N K (K + r))
      (concreteRadialKernelChain N K) :=
  concreteHaarAmbientLaw_radialFactorization_offset H hN hNK

/-! ## The concrete centered orbital kernel -/

/-- The traceless Hermitian rank-one direction `Q_v = vv* - I/N`. -/
def concreteCenteredOrbitalDirection (N : ℕ) (v : ComplexUnitSphere N) :
    ConcreteMatrixState N :=
  complexRankOneProjection v - ((((N : ℝ)⁻¹ : ℝ) : ℂ)) • 1

theorem measurable_concreteCenteredOrbitalDirection (N : ℕ) :
    Measurable (concreteCenteredOrbitalDirection N) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [concreteCenteredOrbitalDirection, Matrix.sub_apply,
    complexRankOneProjection, Matrix.smul_apply, Matrix.one_apply]
  fun_prop

/-- The positive orbital factor `exp(s Q_v)`, written in the measurable
closed form

`exp(-s/N) * (I + (exp(s)-1) vv*)`.

This formula uses only scalar exponentials and the rank-one projection, so it
does not require selecting one of the several noncanonical matrix norms. -/
def concreteOrbitalFactor (N : ℕ) (s : ℝ) (v : ComplexUnitSphere N) :
    ConcreteMatrixState N :=
  (((Real.exp (-s / (N : ℝ)) : ℝ) : ℂ)) •
    (1 + (((Real.exp s - 1 : ℝ) : ℂ)) • complexRankOneProjection v)

theorem measurable_concreteOrbitalFactor (N : ℕ) (s : ℝ) :
    Measurable (concreteOrbitalFactor N s) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [concreteOrbitalFactor, Matrix.smul_apply, Matrix.add_apply,
    Matrix.one_apply, complexRankOneProjection]
  fun_prop

/-- Literal transpose-congruence update along the centered orbital flow. -/
def concreteOrbitalMatrixUpdate (N : ℕ) (s : ℝ)
    (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    ConcreteMatrixState N :=
  concreteOrbitalFactor N s v * A * (concreteOrbitalFactor N s v).transpose

theorem measurable_concreteOrbitalMatrixUpdate (N : ℕ) (s : ℝ) :
    Measurable fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
      concreteOrbitalMatrixUpdate N s Av.2 Av.1 := by
  have hF : Measurable fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
      concreteOrbitalFactor N s Av.2 :=
    (measurable_concreteOrbitalFactor N s).comp measurable_snd
  have hA : Measurable fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
      Av.1 := measurable_fst
  have hFA := measurable_complexMatrix_mul hF hA
  have hFT := measurable_complexMatrix_transpose hF
  exact measurable_complexMatrix_mul hFA hFT

/-- The paper's orbital averaging operator `K_s`, represented as a Markov
kernel on complex square matrices. -/
def concreteOrbitalMatrixKernel (N : ℕ) (s : ℝ) :
    Kernel (ConcreteMatrixState N) (ConcreteMatrixState N) :=
  independentUpdateKernel (complexUnitSphereProbabilityMeasure N)
    (fun Av ↦ concreteOrbitalMatrixUpdate N s Av.2 Av.1)

theorem concreteOrbitalMatrixKernel_isMarkov
    {N : ℕ} (hN : 1 ≤ N) (s : ℝ) :
    IsMarkovKernel (concreteOrbitalMatrixKernel N s) := by
  exact independentUpdateKernel_isMarkov
    (complexUnitSphereProbabilityMeasure N)
    (fun Av ↦ concreteOrbitalMatrixUpdate N s Av.2 Av.1)
    (complexUnitSphereProbabilityMeasure_isProbability hN)
    (measurable_concreteOrbitalMatrixUpdate N s)

/-- The orbital kernel at radius zero is the identity kernel. -/
theorem concreteOrbitalMatrixKernel_zero
    {N : ℕ} (hN : 1 ≤ N) :
    concreteOrbitalMatrixKernel N 0 = Kernel.id := by
  let _ : IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  ext A s hs
  rw [concreteOrbitalMatrixKernel, independentUpdateKernel_apply
    (complexUnitSphereProbabilityMeasure N)
    (fun Av ↦ concreteOrbitalMatrixUpdate N 0 Av.2 Av.1)
    (complexUnitSphereProbabilityMeasure_isProbability hN)
    (measurable_concreteOrbitalMatrixUpdate N 0), Kernel.id_apply]
  have hconst : (fun v : ComplexUnitSphere N ↦
      concreteOrbitalMatrixUpdate N 0 v A) = fun _ ↦ A := by
    funext v
    simp [concreteOrbitalMatrixUpdate, concreteOrbitalFactor]
  rw [hconst, Measure.map_const]
  simp

end

end LogdetLean.GramHafnian.UltimateHiding.Dense

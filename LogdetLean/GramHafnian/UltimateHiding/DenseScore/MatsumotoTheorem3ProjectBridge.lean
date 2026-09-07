import LogdetLean.GramHafnian.UltimateHiding.DenseScore.MatsumotoTheorem3External
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H12_H14_MatsumotoProjectConversion
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.MatrixInverseMeasurability
import Mathlib.Tactic

/-!
# Source-only bridge from approved Matsumoto A4 to H12/H14

The approved atom `MatsumotoPaper.A4_matsumoto_theorem_3` is not changed in
this module.  All declarations below are project-conversion definitions or
proved theorems.

The exact remaining distributional input is exposed as
`HalfGaussianMatsumotoWishartPushforward`: a measurable positive-definite
lift of `R^T R`, equal to that Gram matrix almost everywhere, whose
pushforward is the paper law `W_d(k/2, I; R)`.  No such equality is assumed
globally or installed as an axiom.
-/

open MeasureTheory
open scoped BigOperators Matrix

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart

/-- The paper shape parameter for a `k x d` half-Gaussian matrix. -/
def halfGaussianMatsumotoBeta (k : Nat) : Real :=
  (k : Real) / 2

/-- Matsumoto's `gamma = beta - (d+1)/2` for the half-Gaussian Gram law. -/
def halfGaussianMatsumotoGamma (d k : Nat) : Real :=
  halfGaussianMatsumotoBeta k - ((d : Real) + 1) / 2

/-- Identity scale in the paper cone `Sym^+(d)`. -/
def matsumotoIdentityScale (d : Nat) : MatsumotoPaper.SymPosDef d :=
  ⟨1, Matrix.PosDef.one⟩

theorem halfGaussianMatsumotoGamma_eq (d k : Nat) :
    halfGaussianMatsumotoGamma d k =
      halfGaussianMatsumotoBeta k - ((d : Real) + 1) / 2 :=
  rfl

/-- The inverse-fourth-moment threshold `gamma > 3` in integer dimensions. -/
theorem halfGaussianMatsumotoGamma_gt_three
    {d k : Nat} (hgap : d + 7 < k) :
    (4 : Real) - 1 < halfGaussianMatsumotoGamma d k := by
  have hcast : (d : Real) + 7 < (k : Real) := by
    exact_mod_cast hgap
  unfold halfGaussianMatsumotoGamma halfGaussianMatsumotoBeta
  linarith

/-- The exact doubled scale used when returning to variance-one matrices. -/
theorem two_mul_halfGaussianMatsumotoGamma (d k : Nat) :
    2 * halfGaussianMatsumotoGamma d k =
      (k : Real) - (d : Real) - 1 := by
  unfold halfGaussianMatsumotoGamma halfGaussianMatsumotoBeta
  ring

/-! ## The exact four-cycle specialization of `T_g` -/

private def finEightTuple {alpha : Type*}
    (a0 a1 a2 a3 a4 a5 a6 a7 : alpha) : Fin 8 → alpha :=
  fun i => Fin.cases a0
    (Fin.cases a1
      (Fin.cases a2
        (Fin.cases a3
          (Fin.cases a4
            (Fin.cases a5
              (Fin.cases a6 (fun _ => a7))))))) i

@[simp] private theorem finEightTuple_zero {alpha : Type*}
    (a0 a1 a2 a3 a4 a5 a6 a7 : alpha) :
    finEightTuple a0 a1 a2 a3 a4 a5 a6 a7 0 = a0 := rfl

@[simp] private theorem finEightTuple_one {alpha : Type*}
    (a0 a1 a2 a3 a4 a5 a6 a7 : alpha) :
    finEightTuple a0 a1 a2 a3 a4 a5 a6 a7 1 = a1 := rfl

@[simp] private theorem finEightTuple_two {alpha : Type*}
    (a0 a1 a2 a3 a4 a5 a6 a7 : alpha) :
    finEightTuple a0 a1 a2 a3 a4 a5 a6 a7 2 = a2 := rfl

@[simp] private theorem finEightTuple_three {alpha : Type*}
    (a0 a1 a2 a3 a4 a5 a6 a7 : alpha) :
    finEightTuple a0 a1 a2 a3 a4 a5 a6 a7 3 = a3 := rfl

@[simp] private theorem finEightTuple_four {alpha : Type*}
    (a0 a1 a2 a3 a4 a5 a6 a7 : alpha) :
    finEightTuple a0 a1 a2 a3 a4 a5 a6 a7 4 = a4 := rfl

@[simp] private theorem finEightTuple_five {alpha : Type*}
    (a0 a1 a2 a3 a4 a5 a6 a7 : alpha) :
    finEightTuple a0 a1 a2 a3 a4 a5 a6 a7 5 = a5 := rfl

@[simp] private theorem finEightTuple_six {alpha : Type*}
    (a0 a1 a2 a3 a4 a5 a6 a7 : alpha) :
    finEightTuple a0 a1 a2 a3 a4 a5 a6 a7 6 = a6 := rfl

@[simp] private theorem finEightTuple_seven {alpha : Type*}
    (a0 a1 a2 a3 a4 a5 a6 a7 : alpha) :
    finEightTuple a0 a1 a2 a3 a4 a5 a6 a7 7 = a7 := rfl

private def finEightPairEquiv (alpha : Type*) :
    (Fin 8 → alpha) ≃ (Fin 4 → alpha) × (Fin 4 → alpha) where
  toFun f :=
    (fun i => f (MatsumotoPaper.leftSlot i),
      fun i => f (MatsumotoPaper.rightSlot i))
  invFun p := finEightTuple
    (p.1 0) (p.2 0) (p.1 1) (p.2 1)
    (p.1 2) (p.2 2) (p.1 3) (p.2 3)
  left_inv f := by
    funext i
    fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨i, j⟩
    apply Prod.ext
    · funext a
      fin_cases a <;> rfl
    · funext a
      fin_cases a <;> rfl

/--
The paper permutation whose four `x`-edges become
`x_ab x_bc x_cd x_da` after the identity-matrix Kronecker constraints.
-/
def matsumotoTraceFourPermutation : Equiv.Perm (Fin 8) where
  toFun := finEightTuple 0 2 3 4 5 6 7 1
  invFun := finEightTuple 0 7 1 2 3 4 5 6
  left_inv i := by
    fin_cases i <;> rfl
  right_inv i := by
    fin_cases i <;> rfl

/-- The four paper test matrices are exactly the complex identity matrix. -/
def matsumotoTraceFourTestMatrices (d : Nat) :
    Fin 4 → MatsumotoPaper.ComplexMatrix d :=
  fun _ => 1

private def complexifyRealMatrix {d : Nat}
    (A : MatsumotoPaper.RealMatrix d) : MatsumotoPaper.ComplexMatrix d :=
  fun i j => (A i j : Complex)

private theorem complexifyRealMatrix_mul {d : Nat}
    (A B : MatsumotoPaper.RealMatrix d) :
    complexifyRealMatrix (A * B) =
      complexifyRealMatrix A * complexifyRealMatrix B := by
  ext i j
  simp [complexifyRealMatrix, Matrix.mul_apply]

private theorem complexifyRealMatrix_pow {d : Nat}
    (A : MatsumotoPaper.RealMatrix d) (r : Nat) :
    complexifyRealMatrix (A ^ r) = complexifyRealMatrix A ^ r := by
  induction r with
  | zero =>
      ext i j
      by_cases h : i = j
      · subst j
        simp [complexifyRealMatrix]
      · simp [complexifyRealMatrix, Matrix.one_apply, h]
  | succ r hr =>
      rw [pow_succ, pow_succ, complexifyRealMatrix_mul, hr]

private theorem trace_complexifyRealMatrix {d : Nat}
    (A : MatsumotoPaper.RealMatrix d) :
    Matrix.trace (complexifyRealMatrix A) =
      ((Matrix.trace A : Real) : Complex) := by
  simp [Matrix.trace, complexifyRealMatrix]

private def matsumotoTraceFourPairedTerm {d : Nat}
    (x : MatsumotoPaper.RealMatrix d)
    (i j : Fin 4 → Fin d) : Complex :=
  (∏ a : Fin 4, if i a = j a then (1 : Complex) else 0) *
    (complexifyRealMatrix x (i 0) (i 1) *
      complexifyRealMatrix x (j 1) (i 2) *
      complexifyRealMatrix x (j 2) (i 3) *
      complexifyRealMatrix x (j 3) (j 0))

private theorem matsumoto_T_eq_paired_sum {d : Nat}
    (x : MatsumotoPaper.RealMatrix d) :
    MatsumotoPaper.T matsumotoTraceFourPermutation x
        (matsumotoTraceFourTestMatrices d) =
      ∑ i : Fin 4 → Fin d, ∑ j : Fin 4 → Fin d,
        matsumotoTraceFourPairedTerm x i j := by
  unfold MatsumotoPaper.T
  let F : (Fin 8 → Fin d) → Complex := fun q =>
    (∏ a : Fin 4,
      matsumotoTraceFourTestMatrices d a
        (q (MatsumotoPaper.leftSlot a))
        (q (MatsumotoPaper.rightSlot a))) *
      ∏ a : Fin 4,
        ((x
          (q (matsumotoTraceFourPermutation
            (MatsumotoPaper.leftSlot a)))
          (q (matsumotoTraceFourPermutation
            (MatsumotoPaper.rightSlot a))) : Real) : Complex)
  change (∑ q, F q) = _
  rw [← (finEightPairEquiv (Fin d)).symm.sum_comp F]
  simp only [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro i
  apply Fintype.sum_congr
  intro j
  simp [F, finEightPairEquiv,
    matsumotoTraceFourPermutation, matsumotoTraceFourTestMatrices,
    matsumotoTraceFourPairedTerm, MatsumotoPaper.leftSlot,
    MatsumotoPaper.rightSlot, Fin.prod_univ_four,
    complexifyRealMatrix, Matrix.one_apply]
  by_cases h0 : i 0 = j 0 <;>
    by_cases h1 : i 1 = j 1 <;>
    by_cases h2 : i 2 = j 2 <;>
    by_cases h3 : i 3 = j 3 <;>
    simp [h0, h1, h2, h3]

private def matsumotoTraceFourCycleTerm {d : Nat}
    (A : MatsumotoPaper.ComplexMatrix d) (i : Fin 4 → Fin d) : Complex :=
  A (i 0) (i 1) * A (i 1) (i 2) *
    A (i 2) (i 3) * A (i 3) (i 0)

private theorem sum_matsumotoTraceFourPairedTerm {d : Nat}
    (x : MatsumotoPaper.RealMatrix d) (i : Fin 4 → Fin d) :
    (∑ j : Fin 4 → Fin d, matsumotoTraceFourPairedTerm x i j) =
      matsumotoTraceFourCycleTerm (complexifyRealMatrix x) i := by
  classical
  rw [Fintype.sum_eq_single i]
  · simp [matsumotoTraceFourPairedTerm, matsumotoTraceFourCycleTerm,
      Fin.prod_univ_four]
  · intro j hj
    have hne : j ≠ i := by simpa [eq_comm] using hj
    have ha : ∃ a, j a ≠ i a := by
      by_contra h
      apply hne
      funext a
      exact not_ne_iff.mp (not_exists.mp h a)
    rcases ha with ⟨a, ha⟩
    have hfactor :
        (if i a = j a then (1 : Complex) else 0) = 0 :=
      if_neg (Ne.symm ha)
    have hzero :
        (∏ b : Fin 4, if i b = j b then (1 : Complex) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ a) hfactor
    unfold matsumotoTraceFourPairedTerm
    rw [hzero, zero_mul]

private def finFourTuple {alpha : Type*}
    (a b c d : alpha) : Fin 4 → alpha :=
  fun i => Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d))) i

@[simp] private theorem finFourTuple_zero {alpha : Type*} (a b c d : alpha) :
    finFourTuple a b c d 0 = a := rfl

@[simp] private theorem finFourTuple_one {alpha : Type*} (a b c d : alpha) :
    finFourTuple a b c d 1 = b := rfl

@[simp] private theorem finFourTuple_two {alpha : Type*} (a b c d : alpha) :
    finFourTuple a b c d 2 = c := rfl

@[simp] private theorem finFourTuple_three {alpha : Type*} (a b c d : alpha) :
    finFourTuple a b c d 3 = d := rfl

private def finFourFunctionEquiv (alpha : Type*) :
    (Fin 4 → alpha) ≃ alpha × alpha × alpha × alpha where
  toFun f := (f 0, f 3, f 2, f 1)
  invFun x := finFourTuple x.1 x.2.2.2 x.2.2.1 x.2.1
  left_inv f := by
    funext i
    fin_cases i <;> rfl
  right_inv x := by
    rcases x with ⟨a, b, c, d⟩
    rfl

private theorem sum_finFourFunction
    {alpha M : Type*} [Fintype alpha] [AddCommMonoid M]
  (F : (Fin 4 → alpha) → M) :
    (∑ x, F x) = ∑ a, ∑ b, ∑ c, ∑ d, F (finFourTuple a d c b) := by
  rw [← (finFourFunctionEquiv alpha).symm.sum_comp F]
  simp only [Fintype.sum_prod_type]
  rfl

private theorem sum_four_congr
    {alpha M : Type*} [Fintype alpha] [AddCommMonoid M]
    (f g : alpha → alpha → alpha → alpha → M)
    (h : ∀ a b c d, f a b c d = g a b c d) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ a, ∑ b, ∑ c, ∑ d, g a b c d := by
  apply Fintype.sum_congr
  intro a
  apply Fintype.sum_congr
  intro b
  apply Fintype.sum_congr
  intro c
  apply Fintype.sum_congr
  intro d
  exact h a b c d

private theorem sum_matsumotoTraceFourCycleTerm {d : Nat}
    (A : MatsumotoPaper.ComplexMatrix d) :
    (∑ i : Fin 4 → Fin d, matsumotoTraceFourCycleTerm A i) =
      Matrix.trace (A ^ 4) := by
  rw [sum_finFourFunction]
  unfold matsumotoTraceFourCycleTerm
  simp only [finFourTuple_zero, finFourTuple_one, finFourTuple_two,
    finFourTuple_three]
  rw [show A ^ 4 = ((A * A) * A) * A by noncomm_ring]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  simp_rw [Finset.sum_mul]

/--
Exact paper-to-matrix specialization: the four-cycle `g` and four identity
test matrices turn `T_g(x)` into `Tr(x^4)`.  This theorem is entirely
algebraic and contains no distributional assumption.
-/
theorem matsumoto_T_traceFour_specialization {d : Nat}
    (x : MatsumotoPaper.RealMatrix d) :
    MatsumotoPaper.T matsumotoTraceFourPermutation x
        (matsumotoTraceFourTestMatrices d) =
      ((Matrix.trace (x ^ 4) : Real) : Complex) := by
  rw [matsumoto_T_eq_paired_sum]
  simp_rw [sum_matsumotoTraceFourPairedTerm]
  rw [sum_matsumotoTraceFourCycleTerm]
  rw [← complexifyRealMatrix_pow, trace_complexifyRealMatrix]

/-! ## Exact scale and measurable law conversion boundary -/

private theorem trace_smul_pow_four {d : Nat}
    (gamma : Real) (A : Matrix (Fin d) (Fin d) Real) :
    Matrix.trace ((gamma • A) ^ 4) =
      gamma ^ 4 * Matrix.trace (A ^ 4) := by
  simp [pow_succ, Matrix.trace_smul]
  ring

theorem h12h14_matsumotoScaledTraceFour_eq
    (d k : Nat) (gamma : Real)
    (R : Matrix (Fin k) (Fin d) Real) :
    h12h14MatsumotoIdentityScaledInverseTraceFour d k gamma R =
      gamma ^ 4 *
        Matrix.trace (((realWishartGram R)⁻¹) ^ 4) := by
  unfold h12h14MatsumotoIdentityScaledInverseTraceFour
    h12h14MatsumotoIdentityScaledInverseMatrix
  exact trace_smul_pow_four gamma (realWishartGram R)⁻¹

/--
Exact law-level datum still required from the Gaussian side.  The lift may
change the singular null set only; `gramLift_eq_gram` prevents any hidden
change of scale or random matrix on the full-measure set.
-/
structure HalfGaussianMatsumotoWishartPushforward
    (d k : Nat) where
  gramLift : Matrix (Fin k) (Fin d) Real → MatsumotoPaper.SymPosDef d
  measurable_gramLift : Measurable gramLift
  gramLift_eq_gram :
    ∀ᵐ R ∂halfGaussianMatrix k d, (gramLift R).1 = realWishartGram R
  W : MatsumotoPaper.W_d d (halfGaussianMatsumotoBeta k)
    (matsumotoIdentityScale d)
  map_eq : Measure.map gramLift (halfGaussianMatrix k d) = W.toMeasure

/-- The unscaled inverse trace-four paper integrand. -/
def matsumotoPaperInverseTraceFourIntegrand (d : Nat)
    (w : MatsumotoPaper.SymPosDef d) : Complex :=
  MatsumotoPaper.T matsumotoTraceFourPermutation
    (MatsumotoPaper.SymPosDef.inverse w).1
    (matsumotoTraceFourTestMatrices d)

/--
Exact expectation transport supplied by a proved Gram-pushforward law and
explicit paper-side integrability evidence.  No measurable-space instance is
identified across the paper/project boundary.
-/
theorem matsumotoPaperInverseTraceFour_expectation_eq_halfGaussian
    {d k : Nat} (law : HalfGaussianMatsumotoWishartPushforward d k)
    (hpaper : Integrable (matsumotoPaperInverseTraceFourIntegrand d)
      law.W.toMeasure) :
    MatsumotoPaper.expectation law.W
        (matsumotoPaperInverseTraceFourIntegrand d) =
      ∫ R : Matrix (Fin k) (Fin d) Real,
        matsumotoPaperInverseTraceFourIntegrand d (law.gramLift R)
          ∂halfGaussianMatrix k d := by
  have hmap : Integrable (matsumotoPaperInverseTraceFourIntegrand d)
      (Measure.map law.gramLift (halfGaussianMatrix k d)) := by
    rw [law.map_eq]
    exact hpaper
  unfold MatsumotoPaper.expectation
  rw [← law.map_eq]
  exact integral_map law.measurable_gramLift.aemeasurable
    hmap.aestronglyMeasurable

/-- Paper-side integrability transported exactly to the half-Gaussian lift. -/
theorem matsumotoPaperInverseTraceFour_integrable_comp_halfGaussian
    {d k : Nat} (law : HalfGaussianMatsumotoWishartPushforward d k)
    (hpaper : Integrable (matsumotoPaperInverseTraceFourIntegrand d)
      law.W.toMeasure) :
    Integrable
      (fun R : Matrix (Fin k) (Fin d) Real =>
        matsumotoPaperInverseTraceFourIntegrand d (law.gramLift R))
      (halfGaussianMatrix k d) := by
  have hmap : Integrable (matsumotoPaperInverseTraceFourIntegrand d)
      (Measure.map law.gramLift (halfGaussianMatrix k d)) := by
    rw [law.map_eq]
    exact hpaper
  simpa [Function.comp_def] using
    (integrable_map_measure hmap.aestronglyMeasurable
      law.measurable_gramLift.aemeasurable).mp hmap

theorem matsumotoPaperInverseTraceFour_comp_gramLift_ae
    {d k : Nat} (law : HalfGaussianMatsumotoWishartPushforward d k) :
    (fun R => matsumotoPaperInverseTraceFourIntegrand d (law.gramLift R))
      =ᵐ[halfGaussianMatrix k d]
    (fun R =>
      ((Matrix.trace (((realWishartGram R)⁻¹) ^ 4) : Real) : Complex)) := by
  filter_upwards [law.gramLift_eq_gram] with R hR
  unfold matsumotoPaperInverseTraceFourIntegrand
  rw [matsumoto_T_traceFour_specialization]
  simp only [MatsumotoPaper.SymPosDef.inverse]
  rw [hR]

/-- The matching permutation at the fixed paper order `n = 4`. -/
def matsumotoTraceFourMatchingPermutation
    (matching : MatsumotoPaper.PerfectMatching 4) : Equiv.Perm (Fin 8) :=
  MatsumotoPaper.PerfectMatching.toPerm matching

/-- The literal inverse side of A4 after the four-cycle specialization. -/
def matsumotoA4TraceFourValue (d k : Nat) : Real :=
  halfGaussianMatsumotoGamma d k ^ 4 *
    (∑ matching : MatsumotoPaper.PerfectMatching 4,
      MatsumotoPaper.wgTilde (n := 4)
          (matsumotoTraceFourPermutation⁻¹ *
            matsumotoTraceFourMatchingPermutation matching)
          (halfGaussianMatsumotoGamma d k) *
        MatsumotoPaper.T (n := 4)
          (matsumotoTraceFourMatchingPermutation matching)
          (MatsumotoPaper.SymPosDef.inverse
            (matsumotoIdentityScale d)).1
          (matsumotoTraceFourTestMatrices d)).re

/--
Strongest source-only A4 bridge.  Once the exact Gaussian/Wishart
pushforward certificate and the explicit fourth inverse-trace integrability
proof are supplied, every remaining conversion to the existing H12/H14
moment interface is proved here.
-/
theorem h12h14_matsumotoIdentityTraceFourMoment_of_A4
    {d k : Nat} (hd : 0 < d) (hgap : d + 7 < k)
    (law : HalfGaussianMatsumotoWishartPushforward d k)
    (hpaperIntegrable : Integrable
      (matsumotoPaperInverseTraceFourIntegrand d) law.W.toMeasure) :
    H12H14MatsumotoIdentityTraceFourMoment d k
      (halfGaussianMatsumotoGamma d k)
      (matsumotoA4TraceFourValue d k) := by
  let gamma := halfGaussianMatsumotoGamma d k
  let raw : Matrix (Fin k) (Fin d) Real → Real := fun R =>
    Matrix.trace (((realWishartGram R)⁻¹) ^ 4)
  let rhs : Complex :=
    ∑ matching : MatsumotoPaper.PerfectMatching 4,
      MatsumotoPaper.wgTilde (n := 4)
          (matsumotoTraceFourPermutation⁻¹ *
            matsumotoTraceFourMatchingPermutation matching) gamma *
        MatsumotoPaper.T (n := 4)
          (matsumotoTraceFourMatchingPermutation matching)
          (MatsumotoPaper.SymPosDef.inverse
            (matsumotoIdentityScale d)).1
          (matsumotoTraceFourTestMatrices d)
  have hA4 := (MatsumotoPaper.A4_matsumoto_theorem_3
    d 4 (halfGaussianMatsumotoBeta k) gamma hd (by norm_num)
    (matsumotoIdentityScale d) law.W
    (by rfl) (halfGaussianMatsumotoGamma_gt_three hgap)
    (matsumotoTraceFourTestMatrices d)
    matsumotoTraceFourPermutation).2
  have htransport :=
    matsumotoPaperInverseTraceFour_expectation_eq_halfGaussian law
      hpaperIntegrable
  have hae := matsumotoPaperInverseTraceFour_comp_gramLift_ae law
  have hcomp :=
    matsumotoPaperInverseTraceFour_integrable_comp_halfGaussian law
      hpaperIntegrable
  have hrawComplex : Integrable
      (fun R : Matrix (Fin k) (Fin d) Real => (raw R : Complex))
      (halfGaussianMatrix k d) := by
    apply hcomp.congr
    simpa [raw] using hae
  have hrawReal : Integrable raw (halfGaussianMatrix k d) := by
    simpa [raw] using hrawComplex.re
  have hrawIntegralComplex :
      (∫ R : Matrix (Fin k) (Fin d) Real, (raw R : Complex)
        ∂halfGaussianMatrix k d) = rhs := by
    calc
      (∫ R, (raw R : Complex) ∂halfGaussianMatrix k d) =
          ∫ R, matsumotoPaperInverseTraceFourIntegrand d (law.gramLift R)
            ∂halfGaussianMatrix k d := integral_congr_ae hae.symm
      _ = MatsumotoPaper.expectation law.W
          (matsumotoPaperInverseTraceFourIntegrand d) := htransport.symm
      _ = rhs := by
        rw [show matsumotoPaperInverseTraceFourIntegrand d =
          (fun w : MatsumotoPaper.SymPosDef d =>
            MatsumotoPaper.T matsumotoTraceFourPermutation
              (MatsumotoPaper.SymPosDef.inverse w).1
              (matsumotoTraceFourTestMatrices d)) by rfl]
        simpa [matsumotoTraceFourMatchingPermutation, gamma, rhs] using hA4
  have hrawIntegralReal :
      (∫ R : Matrix (Fin k) (Fin d) Real, raw R
        ∂halfGaussianMatrix k d) = rhs.re := by
    have hre := congrArg Complex.re hrawIntegralComplex
    simpa [integral_complex_ofReal] using hre
  have hpoint :
      h12h14MatsumotoIdentityScaledInverseTraceFour d k gamma =
        fun R => gamma ^ 4 * raw R := by
    funext R
    exact h12h14_matsumotoScaledTraceFour_eq d k gamma R
  refine ⟨?_, ?_⟩
  · rw [show halfGaussianMatsumotoGamma d k = gamma by rfl, hpoint]
    exact hrawReal.const_mul (gamma ^ 4)
  rw [show halfGaussianMatsumotoGamma d k = gamma by rfl, hpoint]
  rw [integral_const_mul, hrawIntegralReal]
  rfl

#print axioms matsumoto_T_traceFour_specialization
#print axioms h12h14_matsumotoScaledTraceFour_eq
#print axioms matsumotoPaperInverseTraceFour_expectation_eq_halfGaussian
#print axioms matsumotoPaperInverseTraceFour_integrable_comp_halfGaussian
#print axioms h12h14_matsumotoIdentityTraceFourMoment_of_A4

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

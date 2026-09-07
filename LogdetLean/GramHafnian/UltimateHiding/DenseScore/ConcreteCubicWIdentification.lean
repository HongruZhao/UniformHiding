import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ProjectiveThirdTraceMoment
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteProjectiveCubicIdentification
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCubicWDefinitions
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredCubicTraceClosure
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.COESupportAlgebra
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ProjectiveBilinearNormSq
import Mathlib.Tactic

/-!
# Exact projective identification of the bilinear cubic terms

This file connects the literal COE statistics

`w_v = |v^* T conjugate(v)|^2` and `x_v w_v`

to the two exact projective contractions used in `(R13)--(R14)`.  Every
identity is derived from the proved low-order projective tensor moment together
with the deterministic support facts `T^T=T` and `TT^*=Z(I+Z)`.  There is no
score estimate, moment bound, total-variation statement, or hiding input.
-/

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

set_option maxHeartbeats 800000

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- The coordinate contraction is exactly the complex coercion of the
literal real bilinear statistic. -/
theorem complexProjectiveBilinearNormSq_eq_concreteCOEW
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    complexProjectiveBilinearNormSq v (concreteCOET K A) =
      (concreteCOEW v K A : ℂ) := by
  rw [show (concreteCOEW v K A : ℂ) =
      star (concreteCOEB v K A) * concreteCOEB v K A by
    unfold concreteCOEW
    exact Complex.normSq_eq_conj_mul_self]
  unfold complexProjectiveBilinearNormSq
  rw [show star (concreteCOEB v K A) =
      ∑ a, ∑ d, v.1 a * star (concreteCOET K A a d) * v.1 d by
    unfold concreteCOEB
    simp only [star_sum, star_mul, star_star]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro d _
    ring]
  unfold concreteCOEB complexRankOneProjection
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- The bilinear norm-square is integrable under a uniform projective
direction. -/
theorem integrable_complexProjectiveBilinearNormSq
    {N : ℕ} (hN : 1 ≤ N) (T : ConcreteMatrixState N) :
    Integrable (fun v : ComplexUnitSphere N ↦
      complexProjectiveBilinearNormSq v T)
      (complexUnitSphereProbabilityMeasure N) := by
  unfold complexProjectiveBilinearNormSq
  simp_rw [show ∀ (v : ComplexUnitSphere N) a b c d,
      complexRankOneProjection v a b * T b c *
          complexRankOneProjection v d c * star (T a d) =
        (complexRankOneProjection v a b *
          complexRankOneProjection v d c) *
            (T b c * star (T a d)) by intros; ring]
  exact integrable_finsetSum _ fun b _ ↦
    integrable_finsetSum _ fun c _ ↦
      integrable_finsetSum _ fun a _ ↦
        integrable_finsetSum _ fun d _ ↦
          (integrable_complexRankOneProjection_entry_mul hN a b d c).mul_const _

private theorem sum_bilinear_second_delta
    {N : ℕ} (u : ℂ) (T : ConcreteMatrixState N) (hT : T.IsSymm) :
    (∑ b, ∑ c, ∑ a, ∑ d,
      (u * ((if a = b then 1 else 0) * (if d = c then 1 else 0) +
        (if a = c then 1 else 0) * (if d = b then 1 else 0))) *
          (T b c * star (T a d))) =
      2 * u * Matrix.trace (T * T.conjTranspose) := by
  classical
  have hsymm : ∀ i j, T j i = T i j := Matrix.IsSymm.ext_iff.mp hT
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  have hfirst :
      (∑ b, ∑ c, ∑ a, ∑ d,
        u * ((if a = b then 1 else 0) * (if d = c then 1 else 0)) *
          (T b c * star (T a d))) =
        u * Matrix.trace (T * T.conjTranspose) := by
    calc
      _ = ∑ a, ∑ d, u * (T a d * star (T a d)) := by simp
      _ = u * Matrix.trace (T * T.conjTranspose) := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
          Matrix.conjTranspose_apply, Finset.mul_sum]
  have hsecond :
      (∑ b, ∑ c, ∑ a, ∑ d,
        u * ((if a = c then 1 else 0) * (if d = b then 1 else 0)) *
          (T b c * star (T a d))) =
        u * Matrix.trace (T * T.conjTranspose) := by
    calc
      _ = ∑ a, ∑ d, u * (T a d * star (T d a)) := by simp
      _ = ∑ a, ∑ d, u * (T a d * star (T a d)) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro d _
        rw [hsymm a d]
      _ = u * Matrix.trace (T * T.conjTranspose) := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
          Matrix.conjTranspose_apply, Finset.mul_sum]
  rw [hfirst, hsecond]
  ring

/-- Exact fourth-sphere-moment contraction

`E_v |v^*T conjugate(v)|^2 = 2 Tr(TT^*)/[N(N+1)]`

for symmetric `T`. -/
theorem integral_complexProjectiveBilinearNormSq
    {N : ℕ} (hN : 1 ≤ N) (T : ConcreteMatrixState N) (hT : T.IsSymm) :
    (∫ v : ComplexUnitSphere N, complexProjectiveBilinearNormSq v T
      ∂(complexUnitSphereProbabilityMeasure N)) =
      2 * (((((N : ℝ) * ((N : ℝ) + 1))⁻¹ : ℝ) : ℂ)) *
        Matrix.trace (T * T.conjTranspose) := by
  unfold complexProjectiveBilinearNormSq
  calc
    (∫ v : ComplexUnitSphere N,
      ∑ b, ∑ c, ∑ a, ∑ d,
        complexRankOneProjection v a b * T b c *
          complexRankOneProjection v d c * star (T a d)
      ∂(complexUnitSphereProbabilityMeasure N)) =
      ∑ b, ∑ c, ∑ a, ∑ d,
        ∫ v : ComplexUnitSphere N,
          (complexRankOneProjection v a b *
            complexRankOneProjection v d c) *
              (T b c * star (T a d))
          ∂(complexUnitSphereProbabilityMeasure N) := by
      simp_rw [show ∀ (v : ComplexUnitSphere N) a d b c,
          complexRankOneProjection v a b * T b c *
              complexRankOneProjection v d c * star (T a d) =
            (complexRankOneProjection v a b *
              complexRankOneProjection v d c) *
                (T b c * star (T a d)) by intros; ring]
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro b _
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro c _
          rw [integral_finsetSum]
          · apply Finset.sum_congr rfl
            intro a _
            rw [integral_finsetSum]
            exact fun d _ ↦
              (integrable_complexRankOneProjection_entry_mul hN a b d c).mul_const _
          · exact fun a _ ↦ integrable_finsetSum _ fun d _ ↦
              (integrable_complexRankOneProjection_entry_mul hN a b d c).mul_const _
        · exact fun c _ ↦ integrable_finsetSum _ fun a _ ↦
            integrable_finsetSum _ fun d _ ↦
              (integrable_complexRankOneProjection_entry_mul hN a b d c).mul_const _
      · exact fun b _ ↦ integrable_finsetSum _ fun c _ ↦
          integrable_finsetSum _ fun a _ ↦
            integrable_finsetSum _ fun d _ ↦
              (integrable_complexRankOneProjection_entry_mul hN a b d c).mul_const _
    _ = 2 * (((((N : ℝ) * ((N : ℝ) + 1))⁻¹ : ℝ) : ℂ)) *
        Matrix.trace (T * T.conjTranspose) := by
      simp_rw [integral_mul_const,
        integral_complexRankOneProjection_entry_mul hN]
      exact sum_bilinear_second_delta _ T hT

/-! ## The mixed `x_v w_v` contraction -/

/-- The six third-projective Kronecker contractions, repeated here as a
transparent local normal form for the mixed bilinear contraction. -/
private def mixedThirdProjectiveDelta {N : ℕ}
    (i j a b d c : Fin N) : ℂ :=
  (if i = j then 1 else 0) * (if a = b then 1 else 0) *
      (if d = c then 1 else 0) +
    (if i = b then 1 else 0) * (if a = j then 1 else 0) *
      (if d = c then 1 else 0) +
    (if i = c then 1 else 0) * (if a = b then 1 else 0) *
      (if d = j then 1 else 0) +
    (if i = j then 1 else 0) * (if a = c then 1 else 0) *
      (if d = b then 1 else 0) +
    (if i = b then 1 else 0) * (if a = c then 1 else 0) *
      (if d = j then 1 else 0) +
    (if i = c then 1 else 0) * (if a = j then 1 else 0) *
      (if d = b then 1 else 0)

private theorem integral_complexRankOneProjection_entry_mul_three_mixed
    {N : ℕ} (hN : 1 ≤ N) (i j a b d c : Fin N) :
    (∫ v : ComplexUnitSphere N,
      complexRankOneProjection v i j *
        complexRankOneProjection v a b *
        complexRankOneProjection v d c
      ∂(complexUnitSphereProbabilityMeasure N)) =
      ((((N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2))⁻¹ : ℝ) : ℂ) *
        mixedThirdProjectiveDelta i j a b d c := by
  change _ = _ *
    ((if i = j then 1 else 0) * (if a = b then 1 else 0) *
        (if d = c then 1 else 0) +
      (if i = b then 1 else 0) * (if a = j then 1 else 0) *
        (if d = c then 1 else 0) +
      (if i = c then 1 else 0) * (if a = b then 1 else 0) *
        (if d = j then 1 else 0) +
      (if i = j then 1 else 0) * (if a = c then 1 else 0) *
        (if d = b then 1 else 0) +
      (if i = b then 1 else 0) * (if a = c then 1 else 0) *
        (if d = j then 1 else 0) +
      (if i = c then 1 else 0) * (if a = j then 1 else 0) *
        (if d = b then 1 else 0))
  exact integral_complexRankOneProjection_entry_mul_three
    hN i j a b d c

private theorem sum_bilinear_third_delta
    {N : ℕ} (u : ℂ) (Z T : ConcreteMatrixState N) (hT : T.IsSymm) :
    (∑ i, ∑ j, ∑ b, ∑ c, ∑ a, ∑ d,
      (u * mixedThirdProjectiveDelta i j a b d c) *
        (Z j i * T b c * star (T a d))) =
      u * (2 * Matrix.trace Z * Matrix.trace (T * T.conjTranspose) +
        4 * Matrix.trace (Z * (T * T.conjTranspose))) := by
  classical
  have hsymm : ∀ i j, T j i = T i j := Matrix.IsSymm.ext_iff.mp hT
  have hdiag :
      (∑ i, ∑ a, ∑ d,
        u * (Z i i * T a d * star (T a d))) =
      u * (Matrix.trace Z * Matrix.trace (T * T.conjTranspose)) := by
    have hTT : Matrix.trace (T * T.conjTranspose) =
        ∑ a, ∑ d, T a d * star (T a d) := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply]
    rw [hTT]
    simp only [Matrix.trace, Matrix.diag_apply]
    calc
      (∑ i, ∑ a, ∑ d,
          u * (Z i i * T a d * star (T a d))) =
        ∑ i, (u * Z i i) *
          (∑ a, ∑ d, T a d * star (T a d)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring
      _ = (∑ i, u * Z i i) *
          (∑ a, ∑ d, T a d * star (T a d)) := by
        exact (Finset.sum_mul Finset.univ (fun i ↦ u * Z i i)
          (∑ a, ∑ d, T a d * star (T a d))).symm
      _ = u * (∑ i, Z i i) *
          (∑ a, ∑ d, T a d * star (T a d)) := by
        have hu : (∑ i, u * Z i i) = u * (∑ i, Z i i) := by
          exact (Finset.mul_sum Finset.univ (fun i ↦ Z i i) u).symm
        rw [hu]
      _ = u * ((∑ i, Z i i) *
          (∑ a, ∑ d, T a d * star (T a d))) := by
        ring
  have hmixed :
      (∑ i, ∑ j, ∑ c,
        u * (Z j i * T i c * star (T j c))) =
      u * Matrix.trace (Z * (T * T.conjTranspose)) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro c _
    ring
  unfold mixedThirdProjectiveDelta
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  have h1 :
      (∑ i, ∑ j, ∑ b, ∑ c, ∑ a, ∑ d,
        u * ((if i = j then 1 else 0) * (if a = b then 1 else 0) *
          (if d = c then 1 else 0)) *
            (Z j i * T b c * star (T a d))) =
      u * (Matrix.trace Z * Matrix.trace (T * T.conjTranspose)) := by
    calc
      _ = ∑ i, ∑ a, ∑ d,
          u * (Z i i * T a d * star (T a d)) := by simp
      _ = _ := hdiag
  have h2 :
      (∑ i, ∑ j, ∑ b, ∑ c, ∑ a, ∑ d,
        u * ((if i = b then 1 else 0) * (if a = j then 1 else 0) *
          (if d = c then 1 else 0)) *
            (Z j i * T b c * star (T a d))) =
      u * Matrix.trace (Z * (T * T.conjTranspose)) := by
    calc
      _ = ∑ i, ∑ j, ∑ c,
          u * (Z j i * T i c * star (T j c)) := by simp
      _ = _ := hmixed
  have h3 :
      (∑ i, ∑ j, ∑ b, ∑ c, ∑ a, ∑ d,
        u * ((if i = c then 1 else 0) * (if a = b then 1 else 0) *
          (if d = j then 1 else 0)) *
            (Z j i * T b c * star (T a d))) =
      u * Matrix.trace (Z * (T * T.conjTranspose)) := by
    calc
      _ = ∑ i, ∑ j, ∑ a,
          u * (Z j i * T a i * star (T a j)) := by simp
      _ = ∑ i, ∑ j, ∑ a,
          u * (Z j i * T i a * star (T j a)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro a _
        rw [hsymm i a, hsymm j a]
      _ = _ := hmixed
  have h4 :
      (∑ i, ∑ j, ∑ b, ∑ c, ∑ a, ∑ d,
        u * ((if i = j then 1 else 0) * (if a = c then 1 else 0) *
          (if d = b then 1 else 0)) *
            (Z j i * T b c * star (T a d))) =
      u * (Matrix.trace Z * Matrix.trace (T * T.conjTranspose)) := by
    calc
      _ = ∑ i, ∑ a, ∑ d,
          u * (Z i i * T a d * star (T d a)) := by simp
      _ = ∑ i, ∑ a, ∑ d,
          u * (Z i i * T a d * star (T a d)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro d _
        rw [hsymm a d]
      _ = _ := hdiag
  have h5 :
      (∑ i, ∑ j, ∑ b, ∑ c, ∑ a, ∑ d,
        u * ((if i = b then 1 else 0) * (if a = c then 1 else 0) *
          (if d = j then 1 else 0)) *
            (Z j i * T b c * star (T a d))) =
      u * Matrix.trace (Z * (T * T.conjTranspose)) := by
    calc
      _ = ∑ i, ∑ j, ∑ a,
          u * (Z j i * T i a * star (T a j)) := by simp
      _ = ∑ i, ∑ j, ∑ a,
          u * (Z j i * T i a * star (T j a)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro a _
        rw [hsymm j a]
      _ = _ := hmixed
  have h6 :
      (∑ i, ∑ j, ∑ b, ∑ c, ∑ a, ∑ d,
        u * ((if i = c then 1 else 0) * (if a = j then 1 else 0) *
          (if d = b then 1 else 0)) *
            (Z j i * T b c * star (T a d))) =
      u * Matrix.trace (Z * (T * T.conjTranspose)) := by
    calc
      _ = ∑ i, ∑ j, ∑ b,
          u * (Z j i * T b i * star (T j b)) := by simp
      _ = ∑ i, ∑ j, ∑ b,
          u * (Z j i * T i b * star (T j b)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro b _
        rw [hsymm i b]
      _ = _ := hmixed
  rw [h1, h2, h3, h4, h5, h6]
  ring

/-- The mixed projective cubic `Tr(P_v Z) |v^*T conjugate(v)|^2` is
integrable.  This is a finite-dimensional consequence of the third
projective tensor moment. -/
private theorem complexProjectiveTracePair_mul_bilinearNormSq_eq_sum
    {N : ℕ} (v : ComplexUnitSphere N) (Z T : ConcreteMatrixState N) :
    complexProjectiveTracePair v Z *
        complexProjectiveBilinearNormSq v T =
      ∑ i, ∑ j, ∑ b, ∑ c, ∑ a, ∑ d,
        (complexRankOneProjection v i j *
          complexRankOneProjection v a b *
          complexRankOneProjection v d c) *
            (Z j i * T b c * star (T a d)) := by
  unfold complexProjectiveTracePair complexProjectiveBilinearNormSq
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem integrable_complexProjectiveTracePair_mul_bilinearNormSq
    {N : ℕ} (hN : 1 ≤ N) (Z T : ConcreteMatrixState N) :
    Integrable (fun v : ComplexUnitSphere N ↦
      complexProjectiveTracePair v Z *
        complexProjectiveBilinearNormSq v T)
      (complexUnitSphereProbabilityMeasure N) := by
  rw [show (fun v : ComplexUnitSphere N ↦
      complexProjectiveTracePair v Z *
        complexProjectiveBilinearNormSq v T) =
      fun v ↦ ∑ i, ∑ j, ∑ b, ∑ c, ∑ a, ∑ d,
        (complexRankOneProjection v i j *
          complexRankOneProjection v a b *
          complexRankOneProjection v d c) *
            (Z j i * T b c * star (T a d)) by
    funext v
    exact complexProjectiveTracePair_mul_bilinearNormSq_eq_sum v Z T]
  exact integrable_finsetSum _ fun i _ ↦
    integrable_finsetSum _ fun j _ ↦
      integrable_finsetSum _ fun b _ ↦
        integrable_finsetSum _ fun c _ ↦
          integrable_finsetSum _ fun a _ ↦
            integrable_finsetSum _ fun d _ ↦
              (integrable_complexRankOneProjection_entry_mul_three
                hN i j a b d c).mul_const _

/-- Exact sixth-sphere-moment contraction

`E_v[Tr(P_v Z) |v^*T conjugate(v)|^2]
 = [2 Tr(Z) Tr(TT^*) + 4 Tr(ZTT^*)]/[N(N+1)(N+2)]`

for symmetric `T`. -/
theorem integral_complexProjectiveTracePair_mul_bilinearNormSq
    {N : ℕ} (hN : 1 ≤ N) (Z T : ConcreteMatrixState N)
    (hT : T.IsSymm) :
    (∫ v : ComplexUnitSphere N,
      complexProjectiveTracePair v Z *
        complexProjectiveBilinearNormSq v T
      ∂(complexUnitSphereProbabilityMeasure N)) =
      (((((N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2))⁻¹ : ℝ) : ℂ) *
        (2 * Matrix.trace Z * Matrix.trace (T * T.conjTranspose) +
          4 * Matrix.trace (Z * (T * T.conjTranspose)))) := by
  rw [show (fun v : ComplexUnitSphere N ↦
      complexProjectiveTracePair v Z *
        complexProjectiveBilinearNormSq v T) =
      fun v ↦ ∑ i, ∑ j, ∑ b, ∑ c, ∑ a, ∑ d,
        (complexRankOneProjection v i j *
          complexRankOneProjection v a b *
          complexRankOneProjection v d c) *
            (Z j i * T b c * star (T a d)) by
    funext v
    exact complexProjectiveTracePair_mul_bilinearNormSq_eq_sum v Z T]
  calc
    (∫ v : ComplexUnitSphere N,
      ∑ i, ∑ j, ∑ b, ∑ c, ∑ a, ∑ d,
        (complexRankOneProjection v i j *
          complexRankOneProjection v a b *
          complexRankOneProjection v d c) *
            (Z j i * T b c * star (T a d))
      ∂(complexUnitSphereProbabilityMeasure N)) =
      ∑ i, ∑ j, ∑ b, ∑ c, ∑ a, ∑ d,
        ∫ v : ComplexUnitSphere N,
          (complexRankOneProjection v i j *
            complexRankOneProjection v a b *
            complexRankOneProjection v d c) *
              (Z j i * T b c * star (T a d))
          ∂(complexUnitSphereProbabilityMeasure N) := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro j _
          rw [integral_finsetSum]
          · apply Finset.sum_congr rfl
            intro b _
            rw [integral_finsetSum]
            · apply Finset.sum_congr rfl
              intro c _
              rw [integral_finsetSum]
              · apply Finset.sum_congr rfl
                intro a _
                rw [integral_finsetSum]
                exact fun d _ ↦
                  (integrable_complexRankOneProjection_entry_mul_three
                    hN i j a b d c).mul_const _
              · exact fun a _ ↦ integrable_finsetSum _ fun d _ ↦
                  (integrable_complexRankOneProjection_entry_mul_three
                    hN i j a b d c).mul_const _
            · exact fun c _ ↦ integrable_finsetSum _ fun a _ ↦
                integrable_finsetSum _ fun d _ ↦
                  (integrable_complexRankOneProjection_entry_mul_three
                    hN i j a b d c).mul_const _
          · exact fun b _ ↦ integrable_finsetSum _ fun c _ ↦
              integrable_finsetSum _ fun a _ ↦
                integrable_finsetSum _ fun d _ ↦
                  (integrable_complexRankOneProjection_entry_mul_three
                    hN i j a b d c).mul_const _
        · exact fun j _ ↦ integrable_finsetSum _ fun b _ ↦
            integrable_finsetSum _ fun c _ ↦
              integrable_finsetSum _ fun a _ ↦
                integrable_finsetSum _ fun d _ ↦
                  (integrable_complexRankOneProjection_entry_mul_three
                    hN i j a b d c).mul_const _
      · exact fun i _ ↦ integrable_finsetSum _ fun j _ ↦
          integrable_finsetSum _ fun b _ ↦
            integrable_finsetSum _ fun c _ ↦
              integrable_finsetSum _ fun a _ ↦
                integrable_finsetSum _ fun d _ ↦
                  (integrable_complexRankOneProjection_entry_mul_three
                    hN i j a b d c).mul_const _
    _ = (((((N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2))⁻¹ : ℝ) : ℂ) *
        (2 * Matrix.trace Z * Matrix.trace (T * T.conjTranspose) +
          4 * Matrix.trace (Z * (T * T.conjTranspose)))) := by
      simp_rw [integral_mul_const,
        integral_complexRankOneProjection_entry_mul_three_mixed hN]
      exact sum_bilinear_third_delta _ Z T hT

/-! ## Concrete COE-support specializations -/

/-- `x_v` is the real part of the projective trace pairing with `Z`. -/
theorem concreteCOEX_eq_re_complexProjectiveTracePair
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    concreteCOEX v K A =
      (complexProjectiveTracePair v (concreteCOEZ K A)).re := by
  unfold concreteCOEX concreteRealTrace
  rw [complexProjectiveTracePair_eq_trace]

/-- `Tr Z` in the `Y=cZ` normalization. -/
theorem concreteCOEZ_trace_re_eq_traceOne_div
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hc : concreteCOEExponent N K ≠ 0) :
    (Matrix.trace (concreteCOEZ K A)).re =
      concreteCOETraceOne N K A / concreteCOEExponent N K := by
  have ht1 : concreteCOETraceOne N K A =
      concreteCOEExponent N K *
        (Matrix.trace (concreteCOEZ K A)).re := by
    simp only [concreteCOETraceOne, concreteRealTrace, concreteCOEY,
      Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [ht1]
  field_simp [hc]

/-- `Tr Z Tr[Z(I+Z)]` in the manuscript normalization. -/
theorem concreteCOEZ_trace_re_mul_traceZW_eq_traceZTraceZW
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hc : concreteCOEExponent N K ≠ 0) :
    (Matrix.trace (concreteCOEZ K A)).re * concreteCOETraceZW N K A =
      concreteCOETraceZTraceZW N K A := by
  rw [concreteCOEZ_trace_re_eq_traceOne_div A hc]
  unfold concreteCOETraceZW concreteCOETraceZTraceZW
  field_simp [hc]

/-- The trace appearing in the projective `w_v` moment is exactly
`Tr[Z(I+Z)]` in the manuscript's `Y=cZ` normalization. -/
theorem concreteCOET_sq_trace_re_eq_traceZW
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hc : concreteCOEExponent N K ≠ 0)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (Matrix.trace
      (concreteCOET K A * (concreteCOET K A).conjTranspose)).re =
      concreteCOETraceZW N K A := by
  let c := concreteCOEExponent N K
  let Z := concreteCOEZ K A
  have hprod :=
    concreteCOET_mul_conjTranspose_eq_Z_mul_one_add_Z A hsupport
  have ht1 : concreteCOETraceOne N K A =
      c * (Matrix.trace Z).re := by
    simp only [concreteCOETraceOne, concreteRealTrace, concreteCOEY,
      Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, c, Z]
  have ht2 : concreteCOETraceTwo N K A =
      c ^ 2 * (Matrix.trace (Z * Z)).re := by
    simp only [concreteCOETraceTwo, concreteRealTrace, concreteCOEY,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul,
      smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, c, Z]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_mul, add_zero, sub_zero]
    ring
  rw [hprod]
  change (Matrix.trace (Z * (1 + Z))).re = _
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.trace_add, Complex.add_re]
  rw [show concreteCOETraceZW N K A =
      concreteCOETraceOne N K A / c +
        concreteCOETraceTwo N K A / c ^ 2 by rfl]
  rw [ht1, ht2]
  field_simp [show c ≠ 0 by simpa only [c] using hc]

/-- The second mixed trace in the `x_v w_v` contraction is exactly
`Tr[Z^2(I+Z)]`. -/
theorem concreteCOEZ_mul_TTstar_trace_re_eq_traceZTwoW
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hc : concreteCOEExponent N K ≠ 0)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (Matrix.trace
      (concreteCOEZ K A *
        (concreteCOET K A * (concreteCOET K A).conjTranspose))).re =
      concreteCOETraceZTwoW N K A := by
  let c := concreteCOEExponent N K
  let Z := concreteCOEZ K A
  have hprod :=
    concreteCOET_mul_conjTranspose_eq_Z_mul_one_add_Z A hsupport
  have ht2 : concreteCOETraceTwo N K A =
      c ^ 2 * (Matrix.trace (Z * Z)).re := by
    simp only [concreteCOETraceTwo, concreteRealTrace, concreteCOEY,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul,
      smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, c, Z]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_mul, add_zero, sub_zero]
    ring
  have ht3 : concreteCOETraceThree N K A =
      c ^ 3 * (Matrix.trace (Z * Z * Z)).re := by
    simp only [concreteCOETraceThree, concreteRealTrace, concreteCOEY,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul,
      smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, c, Z]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_mul, add_zero, sub_zero]
    ring
  rw [hprod]
  change (Matrix.trace (Z * (Z * (1 + Z)))).re = _
  rw [Matrix.mul_add, Matrix.mul_one]
  rw [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.trace_add,
    Complex.add_re]
  rw [show concreteCOETraceZTwoW N K A =
      concreteCOETraceTwo N K A / c ^ 2 +
        concreteCOETraceThree N K A / c ^ 3 by rfl]
  rw [ht2, ht3]
  field_simp [show c ≠ 0 by simpa only [c] using hc]

private theorem trace_im_eq_zero_of_isHermitian_for_W_identification
    {N : ℕ} {A : ConcreteMatrixState N} (hA : A.IsHermitian) :
    (Matrix.trace A).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  have ht := congrArg Matrix.trace hA.eq
  rw [Matrix.trace_conjTranspose] at ht
  exact ht

/-- The literal real `x_v w_v` statistic is the real part of the mixed
complex projective contraction. -/
theorem concreteCOEX_mul_W_eq_re_projective_mixed
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCOEX v K A * concreteCOEW v K A =
      (complexProjectiveTracePair v (concreteCOEZ K A) *
        complexProjectiveBilinearNormSq v (concreteCOET K A)).re := by
  have hZ := concreteCOEZ_isHermitian_of_support A hsupport
  have him := complexProjectiveTracePair_im_eq_zero_of_isHermitian
    v (concreteCOEZ K A) hZ
  rw [concreteCOEX_eq_re_complexProjectiveTracePair,
    complexProjectiveBilinearNormSq_eq_concreteCOEW]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    him, zero_mul, mul_zero, sub_zero]

theorem integrable_concreteCOEW
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N) :
    Integrable (fun v : ComplexUnitSphere N ↦ concreteCOEW v K A)
      (complexUnitSphereProbabilityMeasure N) := by
  have h := (integrable_complexProjectiveBilinearNormSq hN
    (concreteCOET K A)).re
  apply h.congr
  filter_upwards [] with v
  rw [complexProjectiveBilinearNormSq_eq_concreteCOEW]
  simp

theorem integrable_concreteCOEX_mul_W
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    Integrable (fun v : ComplexUnitSphere N ↦
      concreteCOEX v K A * concreteCOEW v K A)
      (complexUnitSphereProbabilityMeasure N) := by
  have h :=
    (integrable_complexProjectiveTracePair_mul_bilinearNormSq hN
      (concreteCOEZ K A) (concreteCOET K A)).re
  apply h.congr
  filter_upwards [] with v
  exact (concreteCOEX_mul_W_eq_re_projective_mixed v A hsupport).symm

/-- Exact projective mean of the literal bilinear statistic `w_v`. -/
theorem integral_concreteCOEW
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hc : concreteCOEExponent N K ≠ 0)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (∫ v : ComplexUnitSphere N, concreteCOEW v K A
      ∂(complexUnitSphereProbabilityMeasure N)) =
      2 * concreteCOETraceZW N K A /
        ((N : ℝ) * ((N : ℝ) + 1)) := by
  have hcomp := integrable_complexProjectiveBilinearNormSq hN
    (concreteCOET K A)
  have hT := concreteCOET_isSymm_of_support A hsymm hsupport
  rw [show (fun v : ComplexUnitSphere N ↦ concreteCOEW v K A) =
      fun v ↦ (complexProjectiveBilinearNormSq v
        (concreteCOET K A)).re by
    funext v
    rw [complexProjectiveBilinearNormSq_eq_concreteCOEW]
    simp]
  change (∫ v : ComplexUnitSphere N,
    RCLike.re (complexProjectiveBilinearNormSq v (concreteCOET K A))
      ∂(complexUnitSphereProbabilityMeasure N)) = _
  rw [integral_re hcomp,
    integral_complexProjectiveBilinearNormSq hN _ hT]
  let q : ℝ := ((N : ℝ) * ((N : ℝ) + 1))⁻¹
  change (2 * (((q : ℝ) : ℂ)) *
    Matrix.trace (concreteCOET K A *
      (concreteCOET K A).conjTranspose)).re = _
  have hre :
      (2 * (((q : ℝ) : ℂ)) *
        Matrix.trace (concreteCOET K A *
          (concreteCOET K A).conjTranspose)).re =
        2 * q * (Matrix.trace (concreteCOET K A *
          (concreteCOET K A).conjTranspose)).re := by
    norm_num [Complex.mul_re, Complex.mul_im]
  rw [hre]
  rw [concreteCOET_sq_trace_re_eq_traceZW A hc hsupport]
  dsimp only [q]
  ring

/-- Exact projective mean of the literal mixed statistic `x_v w_v`. -/
theorem integral_concreteCOEX_mul_W
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hc : concreteCOEExponent N K ≠ 0)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (∫ v : ComplexUnitSphere N,
      concreteCOEX v K A * concreteCOEW v K A
      ∂(complexUnitSphereProbabilityMeasure N)) =
      (2 * concreteCOETraceZTraceZW N K A +
        4 * concreteCOETraceZTwoW N K A) /
          ((N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
  let Z := concreteCOEZ K A
  let T := concreteCOET K A
  let d : ℝ :=
    ((N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2))⁻¹
  have hcomp :=
    integrable_complexProjectiveTracePair_mul_bilinearNormSq hN Z T
  have hZ := concreteCOEZ_isHermitian_of_support A hsupport
  have hT := concreteCOET_isSymm_of_support A hsymm hsupport
  have hzim : (Matrix.trace Z).im = 0 :=
    trace_im_eq_zero_of_isHermitian_for_W_identification hZ
  rw [show (fun v : ComplexUnitSphere N ↦
      concreteCOEX v K A * concreteCOEW v K A) =
      fun v ↦ (complexProjectiveTracePair v Z *
        complexProjectiveBilinearNormSq v T).re by
    funext v
    exact concreteCOEX_mul_W_eq_re_projective_mixed v A hsupport]
  change (∫ v : ComplexUnitSphere N,
    RCLike.re (complexProjectiveTracePair v Z *
      complexProjectiveBilinearNormSq v T)
      ∂(complexUnitSphereProbabilityMeasure N)) = _
  rw [integral_re hcomp,
    integral_complexProjectiveTracePair_mul_bilinearNormSq hN Z T hT]
  change (((d : ℝ) : ℂ) *
      (2 * Matrix.trace Z * Matrix.trace (T * T.conjTranspose) +
        4 * Matrix.trace (Z * (T * T.conjTranspose)))).re = _
  have hre :
      (((d : ℝ) : ℂ) *
        (2 * Matrix.trace Z * Matrix.trace (T * T.conjTranspose) +
          4 * Matrix.trace (Z * (T * T.conjTranspose)))).re =
        d * (2 * (Matrix.trace Z).re *
            (Matrix.trace (T * T.conjTranspose)).re +
          4 * (Matrix.trace (Z * (T * T.conjTranspose))).re) := by
    norm_num [Complex.mul_re, Complex.mul_im, hzim]
  rw [hre]
  dsimp only [Z, T]
  rw [concreteCOET_sq_trace_re_eq_traceZW A hc hsupport,
    concreteCOEZ_mul_TTstar_trace_re_eq_traceZTwoW A hc hsupport]
  rw [show 2 * (Matrix.trace (concreteCOEZ K A)).re *
      concreteCOETraceZW N K A =
      2 * concreteCOETraceZTraceZW N K A by
    rw [mul_assoc,
      concreteCOEZ_trace_re_mul_traceZW_eq_traceZTraceZW A hc]]
  dsimp only [d]
  ring

/-- Exact projective integral of the complete literal `w_v` component of
the rank-one cubic density score.  This is the concrete form of `(R14)` and
is the endpoint consumed by the centered `D3` identification. -/
theorem integral_concreteRankOneCubicW_expression
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hc : concreteCOEExponent N K ≠ 0)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (∫ v : ComplexUnitSphere N,
      24 * concreteCOEExponent N K *
        (((N : ℝ) + 2) * concreteCOEW v K A -
          (concreteCOEExponent N K - 2) *
            concreteCOEX v K A * concreteCOEW v K A)
      ∂(complexUnitSphereProbabilityMeasure N)) =
      averagedCubicWTraceExpression (N : ℝ) (concreteCOEExponent N K)
        (concreteCOETraceZW N K A)
        (concreteCOETraceZTraceZW N K A)
        (concreteCOETraceZTwoW N K A) := by
  let sphere := complexUnitSphereProbabilityMeasure N
  let c := concreteCOEExponent N K
  let meanW := ∫ v : ComplexUnitSphere N, concreteCOEW v K A ∂sphere
  let meanXW := ∫ v : ComplexUnitSphere N,
    concreteCOEX v K A * concreteCOEW v K A ∂sphere
  let traceZ := concreteCOETraceOne N K A / c
  have hw := integrable_concreteCOEW (K := K) hN A
  have hxw := integrable_concreteCOEX_mul_W (K := K) hN A hsupport
  have hinner :
      (∫ v : ComplexUnitSphere N,
        ((N : ℝ) + 2) * concreteCOEW v K A -
          (c - 2) * (concreteCOEX v K A * concreteCOEW v K A) ∂sphere) =
        ((N : ℝ) + 2) * meanW - (c - 2) * meanXW := by
    rw [integral_sub (hw.const_mul _) (hxw.const_mul _),
      integral_const_mul, integral_const_mul]
  have hinnerTarget :
      (∫ v : ComplexUnitSphere N,
        ((N : ℝ) + 2) * concreteCOEW v K A -
          (c - 2) * concreteCOEX v K A * concreteCOEW v K A ∂sphere) =
        ((N : ℝ) + 2) * meanW - (c - 2) * meanXW := by
    rw [show (fun v : ComplexUnitSphere N ↦
        ((N : ℝ) + 2) * concreteCOEW v K A -
          (c - 2) * concreteCOEX v K A * concreteCOEW v K A) =
      fun v ↦ ((N : ℝ) + 2) * concreteCOEW v K A -
        (c - 2) * (concreteCOEX v K A * concreteCOEW v K A) by
      funext v
      ring]
    exact hinner
  have hmeanW : meanW =
      2 * concreteCOETraceZW N K A /
        ((N : ℝ) * ((N : ℝ) + 1)) := by
    simpa only [meanW, sphere] using
      integral_concreteCOEW hN A hc hsymm hsupport
  have hmeanXW : meanXW =
      (2 * concreteCOETraceZTraceZW N K A +
        4 * concreteCOETraceZTwoW N K A) /
          ((N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
    simpa only [meanXW, sphere] using
      integral_concreteCOEX_mul_W hN A hc hsymm hsupport
  have htraceProduct : traceZ * concreteCOETraceZW N K A =
      concreteCOETraceZTraceZW N K A := by
    dsimp only [traceZ, c]
    rw [← concreteCOEZ_trace_re_eq_traceOne_div A hc]
    exact concreteCOEZ_trace_re_mul_traceZW_eq_traceZTraceZW A hc
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hNpOne : (N : ℝ) + 1 ≠ 0 := by positivity
  have hNpTwo : (N : ℝ) + 2 ≠ 0 := by positivity
  calc
    (∫ v : ComplexUnitSphere N,
      24 * concreteCOEExponent N K *
        (((N : ℝ) + 2) * concreteCOEW v K A -
          (concreteCOEExponent N K - 2) *
            concreteCOEX v K A * concreteCOEW v K A) ∂sphere) =
        24 * c * (((N : ℝ) + 2) * meanW -
          (c - 2) * meanXW) := by
      rw [integral_const_mul]
      rw [hinnerTarget]
    _ = 48 * c /
          ((N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2)) *
        (((N : ℝ) + 2) ^ 2 * concreteCOETraceZW N K A -
          (c - 2) * (traceZ * concreteCOETraceZW N K A +
            2 * concreteCOETraceZTwoW N K A)) := by
      apply averagedCubicW_exact_contraction hNr hNpOne hNpTwo
      · exact hmeanW
      · rw [hmeanXW]
        rw [show 2 * traceZ * concreteCOETraceZW N K A =
            2 * concreteCOETraceZTraceZW N K A by
          rw [mul_assoc, htraceProduct]]
    _ = averagedCubicWTraceExpression (N : ℝ) c
        (concreteCOETraceZW N K A)
        (concreteCOETraceZTraceZW N K A)
        (concreteCOETraceZTwoW N K A) := by
      rw [htraceProduct]
      rfl

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

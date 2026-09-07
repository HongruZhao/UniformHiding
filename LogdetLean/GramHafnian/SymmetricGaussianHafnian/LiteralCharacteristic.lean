import LogdetLean.GramHafnian.SymmetricGaussianHafnian.Ensemble
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.CofactorAlgebra
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.ComplexConditionalKernel

/-!
# Characteristic function of the literal symmetric edge-Gaussian cofactors

The underlying probability law is the finite independent-edge product in
`Ensemble`, and each cofactor is the actual perfect-matching hafnian on the
deleted principal submatrix.  Permutation and common-phase symmetries are
proved from this product law and literal hafnian identities.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal BigOperators Real

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

set_option maxHeartbeats 1200000

/-- Raw transpose-pairing Fourier phase of the literal cofactor vector. -/
def edgeCofactorPhase {ι : Type*} [Fintype ι] [LinearOrder ι]
    (x : Edge ι → ℂ) (w : ι → ℂ) : ℝ :=
  (∑ j, w j * edgeCofactor x j).re

/-- The unit-modulus Fourier character associated with the literal phase. -/
def edgeCofactorPhaseCharacter {ι : Type*} [Fintype ι] [LinearOrder ι]
    (w : ι → ℂ) (x : Edge ι → ℂ) : ℂ :=
  Complex.exp ((edgeCofactorPhase x w : ℂ) * Complex.I)

/-- Characteristic functional of the actual independent-edge hafnian
cofactor vector, with raw transpose Fourier coefficients. -/
def edgeCofactorCharacteristic (ι : Type*) [Fintype ι] [LinearOrder ι]
    (w : ι → ℂ) : ℂ :=
  ∫ x : Edge ι → ℂ, edgeCofactorPhaseCharacter w x ∂edgeGaussian ι

@[fun_prop]
theorem continuous_edgeCofactorPhase {ι : Type*} [Fintype ι] [LinearOrder ι]
    (w : ι → ℂ) : Continuous (fun x : Edge ι → ℂ ↦ edgeCofactorPhase x w) := by
  unfold edgeCofactorPhase
  fun_prop

@[fun_prop]
theorem measurable_edgeCofactorPhaseCharacter
    {ι : Type*} [Fintype ι] [LinearOrder ι] (w : ι → ℂ) :
    Measurable (edgeCofactorPhaseCharacter w) := by
  unfold edgeCofactorPhaseCharacter
  exact ((Complex.continuous_ofReal.comp
    (continuous_edgeCofactorPhase w)).mul continuous_const).cexp.measurable

theorem integrable_edgeCofactorPhaseCharacter
    {ι : Type*} [Fintype ι] [LinearOrder ι] (w : ι → ℂ) :
    Integrable (edgeCofactorPhaseCharacter w) (edgeGaussian ι) := by
  apply Integrable.of_bound (measurable_edgeCofactorPhaseCharacter w).aestronglyMeasurable 1
  filter_upwards [] with x
  rw [edgeCofactorPhaseCharacter, Complex.norm_exp]
  simp

/-- The matrix and edge-data definitions are literally the same cofactor. -/
theorem edgeCofactor_eq_matrixCofactor
    {ι : Type*} [Fintype ι] [LinearOrder ι] (x : Edge ι → ℂ) (j : ι) :
    edgeCofactor x j = matrixCofactor (matrixOfEdges x) j := rfl

/-- Simultaneous relabelling transports each actual cofactor coordinate. -/
theorem edgeCofactor_restrict_equiv
    {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
    (e : α ≃ β) (x : Edge β → ℂ) (j : α) :
    edgeCofactor (restrictEdges e.toEmbedding x) j = edgeCofactor x (e j) := by
  rw [edgeCofactor_eq_matrixCofactor, matrixOfEdges_restrict]
  exact matrixCofactor_reindex e (matrixOfEdges x) (matrixOfEdges_symmetric x) j

theorem edgeCofactorPhase_restrict_equiv
    {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
    (e : α ≃ β) (x : Edge β → ℂ) (w : β → ℂ) :
    edgeCofactorPhase (restrictEdges e.toEmbedding x) (fun j ↦ w (e j)) =
      edgeCofactorPhase x w := by
  unfold edgeCofactorPhase
  simp_rw [edgeCofactor_restrict_equiv]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)

/-- The full characteristic functional is invariant under relabelling,
proved by a measure-preserving transformation of the independent edges. -/
theorem edgeCofactorCharacteristic_reindex
    {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
    (e : α ≃ β) (w : β → ℂ) :
    edgeCofactorCharacteristic α (fun j ↦ w (e j)) =
      edgeCofactorCharacteristic β w := by
  unfold edgeCofactorCharacteristic
  rw [← (measurePreserving_restrictEdges e.toEmbedding).map_eq,
    integral_map (measurable_restrictEdges e.toEmbedding).aemeasurable
      (measurable_edgeCofactorPhaseCharacter (fun j ↦ w (e j))).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with x
  unfold edgeCofactorPhaseCharacter
  rw [edgeCofactorPhase_restrict_equiv]

theorem edgeCofactorCharacteristic_permutationInvariant (d : ℕ) :
    PermutationInvariant (edgeCofactorCharacteristic (Fin d)) := by
  intro sigma w
  exact edgeCofactorCharacteristic_reindex sigma.symm w

/-- Singleton coordinates may be exchanged, including in empty or
one-dimensional edge spaces. -/
theorem edgeCofactorCharacteristic_singletonExchangeable
    {ι : Type*} [Fintype ι] [LinearOrder ι] :
    SingletonExchangeable (edgeCofactorCharacteristic ι) := by
  intro i j z
  classical
  by_cases hij : i = j
  · subst j
    rfl
  let sigma : Equiv.Perm ι := Equiv.swap i j
  have h := edgeCofactorCharacteristic_reindex sigma (singleCoordinate j z)
  rw [show (fun l ↦ singleCoordinate j z (sigma l)) = singleCoordinate i z by
    funext l
    by_cases hli : l = i
    · subst l
      simp [sigma, singleCoordinate]
    · by_cases hlj : l = j
      · subst l
        simp [sigma, singleCoordinate, hij, hli]
      · rw [Equiv.swap_apply_of_ne_of_ne hli hlj]
        simp [singleCoordinate, hli, hlj]] at h
  exact h

/-- Common multiplication of every edge multiplies the assembled matrix
by the same scalar; the zero diagonal causes no exception. -/
theorem matrixOfEdges_const_mul
    {ι : Type*} [DecidableEq ι] (c : ℂ) (x : Edge ι → ℂ) :
    matrixOfEdges (fun e ↦ c * x e) = fun i j ↦ c * matrixOfEdges x i j := by
  funext i j
  by_cases hij : i = j
  · subst j
    simp
  · simp [matrixOfEdges, hij]

/-- Literal degree-`r` homogeneity of every cofactor on `2r+1` vertices. -/
theorem edgeCofactor_const_mul
    {ι : Type*} [Fintype ι] [LinearOrder ι] {r : ℕ}
    (hcard : Fintype.card ι = 2 * r + 1)
    (c : ℂ) (x : Edge ι → ℂ) (j : ι) :
    edgeCofactor (fun e ↦ c * x e) j = c ^ r * edgeCofactor x j := by
  unfold edgeCofactor
  rw [matrixOfEdges_const_mul]
  have hdelete : Fintype.card {i : ι // i ≠ j} = 2 * r := by
    rw [Fintype.card_subtype_compl]
    have hone : Fintype.card {i : ι // i = j} = 1 := by simp
    rw [hone, hcard]
    omega
  exact typeHafnian_const_mul_of_card r hdelete c _

/-- Multiplication of all iid edge coordinates by a unit complex number
preserves their full joint law. -/
theorem measurePreserving_edgeGaussian_const_mul
    {ι : Type*} [Fintype ι] (c : ℂ) (hc : ‖c‖ = 1) :
    MeasurePreserving (fun x : Edge ι → ℂ ↦ fun e ↦ c * x e)
      (edgeGaussian ι) (edgeGaussian ι) := by
  exact measurePreserving_pi _ _ (fun _ ↦ measurePreserving_circularGaussian_mul c hc)

/-- Common Fourier phase invariance of the literal cofactor functional in
positive cofactor degree.  It follows from a unit `r`-th root and the actual
joint circular Gaussian edge law. -/
theorem edgeCofactorCharacteristic_commonPhaseInvariant
    {ι : Type*} [Fintype ι] [LinearOrder ι] {r : ℕ}
    (hcard : Fintype.card ι = 2 * r + 1) (hr : 0 < r) :
    CommonPhaseInvariant (edgeCofactorCharacteristic ι) := by
  intro q hq w
  obtain ⟨c, hcPow⟩ := IsAlgClosed.exists_pow_nat_eq q hr
  have hcNormPow : ‖c‖ ^ r = 1 := by
    rw [← norm_pow, hcPow, hq]
  have hcNorm : ‖c‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg c) (Nat.ne_of_gt hr)).mp hcNormPow
  have hg := measurePreserving_edgeGaussian_const_mul (ι := ι) c hcNorm
  unfold edgeCofactorCharacteristic
  calc
    (∫ x, edgeCofactorPhaseCharacter (phaseCoordinates q w) x ∂edgeGaussian ι) =
        ∫ x, edgeCofactorPhaseCharacter w (fun e ↦ c * x e) ∂edgeGaussian ι := by
      apply integral_congr_ae
      filter_upwards [] with x
      unfold edgeCofactorPhaseCharacter edgeCofactorPhase phaseCoordinates
      simp_rw [edgeCofactor_const_mul hcard, hcPow]
      congr 3
      congr 1
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = ∫ x, edgeCofactorPhaseCharacter w x ∂edgeGaussian ι := by
      conv_rhs => rw [← hg.map_eq]
      symm
      exact integral_map hg.measurable.aemeasurable
        (measurable_edgeCofactorPhaseCharacter w).aestronglyMeasurable

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian

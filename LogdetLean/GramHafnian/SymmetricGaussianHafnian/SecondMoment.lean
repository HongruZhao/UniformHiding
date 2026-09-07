import LogdetLean.GramHafnian.SymmetricGaussianHafnian.EdgeSplitting
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.CofactorAlgebra
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.LastVertex
import LogdetLean.GramHafnian.ShiftedAnticoncentration.ConditionalSmallBall
import LogdetLean.GramHafnian.FiniteMomentAlgebra

/-!
# Exact second moment of the literal symmetric Gaussian hafnian

The nonnegative integral is evaluated before integrability is asserted.
The calculation uses the genuine last-vertex product law and deletion of
unordered edge coordinates, rather than an assumed Gaussian cofactor law.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators ENNReal ComplexConjugate

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

set_option backward.isDefEq.respectTransparency false

theorem integrable_normSq_circularGaussian :
    Integrable Complex.normSq circularGaussian := by
  have h := (integrable_mixedComplexMonomial_circularGaussian 1 1
    (by omega) (by omega)).re
  simpa [mixedComplexMonomial, Complex.mul_conj] using h

theorem integral_normSq_circularGaussian :
    (∫ z : ℂ, Complex.normSq z ∂circularGaussian) = 1 := by
  have hi : Integrable (fun z : ℂ ↦ z * conj z) circularGaussian := by
    have h := integrable_mixedComplexMonomial_circularGaussian 1 1 (by omega) (by omega)
    change Integrable (fun z : ℂ ↦ z ^ 1 * conj z ^ 1) circularGaussian at h
    simpa only [pow_one] using h
  have h := integral_re hi
  rw [integral_mul_conj_circularGaussian] at h
  change (∫ z : ℂ, (z * conj z).re ∂circularGaussian) = (1 : ℂ).re at h
  simpa only [Complex.mul_conj, Complex.ofReal_re, Complex.one_re] using h

theorem lintegral_normSq_circularGaussian :
    (∫⁻ z : ℂ, ENNReal.ofReal (Complex.normSq z) ∂circularGaussian) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal integrable_normSq_circularGaussian
    (Filter.Eventually.of_forall Complex.normSq_nonneg), integral_normSq_circularGaussian]
  simp

/-- The conditional second moment holds also for zero coefficients. -/
theorem lintegral_normSq_iidCircularTransposeLinearForm
    {n : ℕ} (y : Fin n → ℂ) :
    (∫⁻ g : Fin n → ℂ,
      ENNReal.ofReal (Complex.normSq (iidCircularTransposeLinearForm y g))
      ∂standardGaussianProduct (Fin n)) =
      ENNReal.ofReal (circularCoefficientEnergy y) := by
  have hmap := map_iidCircularTransposeLinearForm_eq_scaled_circular y
  change (standardGaussianProduct (Fin n)).map (iidCircularTransposeLinearForm y) =
    circularGaussian.map (fun z : ℂ ↦
      Real.sqrt (circularCoefficientEnergy y) • z) at hmap
  have hnorm : Measurable (fun z : ℂ ↦ ENNReal.ofReal (Complex.normSq z)) := by
    fun_prop
  have hV := circularCoefficientEnergy_nonneg y
  calc
    _ = ∫⁻ z : ℂ, ENNReal.ofReal (Complex.normSq z)
        ∂((standardGaussianProduct (Fin n)).map
          (iidCircularTransposeLinearForm y)) := by
      rw [lintegral_map hnorm (measurable_iidCircularTransposeLinearForm y)]
    _ = ∫⁻ z : ℂ, ENNReal.ofReal (Complex.normSq z)
        ∂(circularGaussian.map (fun z : ℂ ↦
          Real.sqrt (circularCoefficientEnergy y) • z)) := by
      rw [hmap]
    _ = ∫⁻ z : ℂ, ENNReal.ofReal
        (Complex.normSq (Real.sqrt (circularCoefficientEnergy y) • z))
        ∂circularGaussian := by
      rw [lintegral_map hnorm (by fun_prop)]
    _ = ∫⁻ z : ℂ, ENNReal.ofReal (circularCoefficientEnergy y) *
        ENNReal.ofReal (Complex.normSq z) ∂circularGaussian := by
      apply lintegral_congr
      intro z
      change ENNReal.ofReal (Complex.normSq
        (((Real.sqrt (circularCoefficientEnergy y) : ℝ) : ℂ) * z)) = _
      rw [Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt hV,
        ENNReal.ofReal_mul hV]
    _ = ENNReal.ofReal (circularCoefficientEnergy y) := by
      rw [lintegral_const_mul _ hnorm, lintegral_normSq_circularGaussian, mul_one]

/-- The literal hafnian is unchanged by simultaneous vertex relabelling. -/
theorem edgeHafnian_restrict_equiv
    {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
    (e : α ≃ β) (x : Edge β → ℂ) :
    edgeHafnian (restrictEdges e.toEmbedding x) = edgeHafnian x := by
  unfold edgeHafnian
  rw [matrixOfEdges_restrict]
  exact typeHafnian_reindex_equiv_of_symmetric e (matrixOfEdges x)
    (matrixOfEdges_symmetric x)

/-- Equality of the full complex hafnian laws under arbitrary finite
vertex equivalences, not merely equality of their moments. -/
theorem edgeHafnianLaw_reindex
    {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
    (e : α ≃ β) : edgeHafnianLaw α = edgeHafnianLaw β := by
  unfold edgeHafnianLaw
  rw [← (measurePreserving_restrictEdges e.toEmbedding).map_eq,
    Measure.map_map measurable_edgeHafnian (measurable_restrictEdges e.toEmbedding)]
  congr 1
  funext x
  exact edgeHafnian_restrict_equiv e x

/-- Extended second moment, defined directly from the literal edge law. -/
def edgeHafnianSecondMoment (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ x : Edge (Fin n) → ℂ, ENNReal.ofReal (Complex.normSq (edgeHafnian x))
    ∂edgeGaussian (Fin n)

@[simp] theorem edgeHafnianSecondMoment_zero : edgeHafnianSecondMoment 0 = 1 := by
  simp [edgeHafnianSecondMoment]

/-- The second moment depends on vertex count and not vertex labels. -/
theorem lintegral_normSq_edgeHafnian_of_card
    {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (hcard : Fintype.card ι = n) :
    (∫⁻ x : Edge ι → ℂ, ENNReal.ofReal (Complex.normSq (edgeHafnian x))
      ∂edgeGaussian ι) = edgeHafnianSecondMoment n := by
  have hm : Measurable (fun z : ℂ ↦ ENNReal.ofReal (Complex.normSq z)) := by fun_prop
  rw [← lintegral_map hm measurable_edgeHafnian]
  change (∫⁻ z : ℂ, ENNReal.ofReal (Complex.normSq z) ∂edgeHafnianLaw ι) = _
  rw [edgeHafnianLaw_reindex (Fintype.equivFinOfCardEq hcard)]
  unfold edgeHafnianLaw edgeHafnianSecondMoment
  rw [lintegral_map hm measurable_edgeHafnian]

/-- Exact deletion-law second moment of each literal cofactor. -/
theorem lintegral_normSq_edgeCofactor {n : ℕ} (j : Fin (n + 1)) :
    (∫⁻ x : Edge (Fin (n + 1)) → ℂ,
      ENNReal.ofReal (Complex.normSq (edgeCofactor x j))
      ∂edgeGaussian (Fin (n + 1))) = edgeHafnianSecondMoment n := by
  have hm : Measurable (fun z : ℂ ↦ ENNReal.ofReal (Complex.normSq z)) := by fun_prop
  have hj : Measurable (fun x : Edge (Fin (n + 1)) → ℂ ↦ edgeCofactor x j) := by
    fun_prop
  rw [← lintegral_map hm hj, edgeCofactor_component_law j]
  unfold edgeHafnianLaw
  rw [lintegral_map hm measurable_edgeHafnian]
  apply lintegral_normSq_edgeHafnian_of_card
  rw [Fintype.card_subtype_compl]
  simp

/-- Tonelli evaluates the sum of cofactor squares with no prior
integrability assumption. -/
theorem lintegral_edgeCofactorEnergy (n : ℕ) :
    (∫⁻ x : Edge (Fin (n + 1)) → ℂ, ENNReal.ofReal (edgeCofactorEnergy x)
      ∂edgeGaussian (Fin (n + 1))) = (n + 1 : ℕ) * edgeHafnianSecondMoment n := by
  classical
  unfold edgeCofactorEnergy
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ sq_nonneg ‖edgeCofactor _ j‖)]
  rw [lintegral_finsetSum _ (fun j _ ↦ by fun_prop)]
  simp_rw [Complex.sq_norm, lintegral_normSq_edgeCofactor]
  simp

/-- Integrating the exact last-vertex Gaussian mixture gives the expected
cofactor energy; this equality is valid as an extended nonnegative integral. -/
theorem edgeHafnianSecondMoment_succ (n : ℕ) :
    edgeHafnianSecondMoment (n + 1) =
      ∫⁻ x : Edge (Fin n) → ℂ, ENNReal.ofReal (edgeCofactorEnergy x)
        ∂edgeGaussian (Fin n) := by
  have hm : Measurable (fun z : ℂ ↦ ENNReal.ofReal (Complex.normSq z)) := by fun_prop
  unfold edgeHafnianSecondMoment
  rw [← lintegral_map hm measurable_edgeHafnian]
  change (∫⁻ z : ℂ, ENNReal.ofReal (Complex.normSq z)
    ∂edgeHafnianLaw (Fin (n + 1))) = _
  rw [edgeHafnianLaw_eq_lastVertexProduct n,
    lintegral_map hm (measurable_conditionalCircularLinearForm measurable_edgeCofactor),
    lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro x
  exact lintegral_normSq_iidCircularTransposeLinearForm (edgeCofactor x)

/-- The literal second-moment recurrence, with no unproved moment or
integrability hypothesis. -/
theorem edgeHafnianSecondMoment_step (n : ℕ) :
    edgeHafnianSecondMoment (n + 2) =
      (n + 1 : ℕ) * edgeHafnianSecondMoment n := by
  rw [show n + 2 = (n + 1) + 1 by omega,
    edgeHafnianSecondMoment_succ, lintegral_edgeCofactorEnergy]

/-- `E[|haf S|²] = (2n-1)!!` first as a finite extended integral. -/
theorem edgeHafnianSecondMoment_even (n : ℕ) :
    edgeHafnianSecondMoment (2 * n) = (oddPairingNat n : ℝ≥0∞) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 2 by omega,
        edgeHafnianSecondMoment_step, ih, oddPairingNat_succ, Nat.cast_mul]
      exact mul_comm _ _

/-- Squared hafnian magnitude is genuinely integrable under the literal
edge law.  Finiteness follows from the evaluated nonnegative integral. -/
theorem integrable_normSq_edgeHafnian (n : ℕ) :
    Integrable (fun x : Edge (Fin (2 * n)) → ℂ ↦ Complex.normSq (edgeHafnian x))
      (edgeGaussian (Fin (2 * n))) := by
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (fun _ ↦ Complex.normSq_nonneg _))]
  change edgeHafnianSecondMoment (2 * n) < ⊤
  rw [edgeHafnianSecondMoment_even]
  exact ENNReal.natCast_lt_top _

/-- Exact probability normalization for the ordinary hafnian observable. -/
theorem integral_normSq_edgeHafnian (n : ℕ) :
    (∫ x : Edge (Fin (2 * n)) → ℂ, Complex.normSq (edgeHafnian x)
      ∂edgeGaussian (Fin (2 * n))) = (oddPairingNat n : ℝ) := by
  apply (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg (fun _ ↦ Complex.normSq_nonneg _)) (Nat.cast_nonneg _)).mp
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_normSq_edgeHafnian n)
    (Filter.Eventually.of_forall (fun _ ↦ Complex.normSq_nonneg _))]
  change edgeHafnianSecondMoment (2 * n) = _
  rw [edgeHafnianSecondMoment_even]
  simp

/-- Closed nonnegative first moment of the odd cofactor energy. -/
theorem lintegral_edgeCofactorEnergy_odd (n : ℕ) :
    (∫⁻ x : Edge (Fin (2 * n + 1)) → ℂ, ENNReal.ofReal (edgeCofactorEnergy x)
      ∂edgeGaussian (Fin (2 * n + 1))) = (oddPairingNat (n + 1) : ℝ≥0∞) := by
  rw [lintegral_edgeCofactorEnergy, edgeHafnianSecondMoment_even,
    oddPairingNat_succ, Nat.cast_mul]
  exact mul_comm _ _

theorem integrable_edgeCofactorEnergy_odd (n : ℕ) :
    Integrable edgeCofactorEnergy (edgeGaussian (Fin (2 * n + 1))) := by
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall edgeCofactorEnergy_nonneg),
    lintegral_edgeCofactorEnergy_odd]
  exact ENNReal.natCast_lt_top _

/-- The ordinary expected odd cofactor energy is `(2n+1)!!`. -/
theorem integral_edgeCofactorEnergy_odd (n : ℕ) :
    (∫ x : Edge (Fin (2 * n + 1)) → ℂ, edgeCofactorEnergy x
      ∂edgeGaussian (Fin (2 * n + 1))) = (oddPairingNat (n + 1) : ℝ) := by
  apply (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg edgeCofactorEnergy_nonneg) (Nat.cast_nonneg _)).mp
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_edgeCofactorEnergy_odd n)
    (Filter.Eventually.of_forall edgeCofactorEnergy_nonneg),
    lintegral_edgeCofactorEnergy_odd]
  simp

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian

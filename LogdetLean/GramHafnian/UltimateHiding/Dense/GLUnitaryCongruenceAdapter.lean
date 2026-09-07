import LogdetLean.GramHafnian.UltimateHiding.Dense.GLUnitaryPolarInternal
import LogdetLean.GramHafnian.UltimateHiding.Dense.RadialConcrete
import LogdetLean.Coherence.ProductMeasureReorder
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# From `GL_N(C) / U(N)` convolution to transpose-congruence actions

This module develops the generic measure-action adapter used by H2.  The
finite-measure Gelfand-pair commutativity statement that was formerly an
external atom is now proved internally here from polar decomposition, the
standard involution argument, and Haar uniqueness.  The remaining definitions
and pushforward identities are ordinary measurable group-action algebra.
-/

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped MeasureTheory ENNReal

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

local instance matrixBorelSpaceAdapter (N K : ℕ) :
    BorelSpace (Matrix (Fin N) (Fin K) ℂ) := by
  exact inferInstanceAs (BorelSpace (Fin N → Fin K → ℂ))

local instance matrixSecondCountableTopologyAdapter (N K : ℕ) :
    SecondCountableTopology (Matrix (Fin N) (Fin K) ℂ) := by
  exact inferInstanceAs
    (SecondCountableTopology (Fin N → Fin K → ℂ))

local instance unitaryGroupSecondCountableTopologyAdapter (N : ℕ) :
    SecondCountableTopology (Matrix.unitaryGroup (Fin N) ℂ) := by
  exact TopologicalSpace.secondCountableTopology_induced
    (Matrix.unitaryGroup (Fin N) ℂ)
    (Matrix (Fin N) (Fin N) ℂ) Subtype.val

/-- Forget that an invertible complex matrix is a unit. -/
def complexMatrixGLVal (N : ℕ) (g : ComplexMatrixGL N) :
    ConcreteMatrixState N :=
  g

theorem measurable_complexMatrixGLVal (N : ℕ) :
    Measurable (complexMatrixGLVal N) := by
  exact comap_measurable _

/-- Matrix multiplication is measurable for the coordinatewise measurable
structure installed on `ComplexMatrixGL`. -/
instance complexMatrixGLMeasurableMul₂ (N : ℕ) :
    MeasurableMul₂ (ComplexMatrixGL N) where
  measurable_mul := by
    rw [measurable_comap_iff]
    have hleft : Measurable fun p : ComplexMatrixGL N × ComplexMatrixGL N ↦
        complexMatrixGLVal N p.1 :=
      (measurable_complexMatrixGLVal N).comp measurable_fst
    have hright : Measurable fun p : ComplexMatrixGL N × ComplexMatrixGL N ↦
        complexMatrixGLVal N p.2 :=
      (measurable_complexMatrixGLVal N).comp measurable_snd
    convert measurable_complexMatrix_mul hleft hright using 1 <;>
      simp [Function.comp_def, complexMatrixGLVal]

/-- Conjugate transpose on matrix units is measurable for the coordinatewise
measurable structure used in the H2 development. -/
theorem measurable_complexMatrixGL_star (N : ℕ) :
    Measurable (fun g : ComplexMatrixGL N ↦ star g) := by
  rw [measurable_comap_iff]
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  change Measurable (fun g : ComplexMatrixGL N ↦
    star ((g : Matrix (Fin N) (Fin N) ℂ) j i))
  rw [RCLike.star_def]
  exact Complex.continuous_conj.measurable.comp
    ((measurable_pi_apply i).comp
      ((measurable_pi_apply j).comp (measurable_complexMatrixGLVal N)))

/-- Conjugate transpose reverses multiplicative convolution. -/
theorem map_star_mconv
    {N : ℕ} (mu nu : Measure (ComplexMatrixGL N))
    [SFinite mu] [SFinite nu] :
    Measure.map (fun g : ComplexMatrixGL N ↦ star g) (mu ∗ₘ nu) =
      Measure.map (fun g : ComplexMatrixGL N ↦ star g) nu ∗ₘ
        Measure.map (fun g : ComplexMatrixGL N ↦ star g) mu := by
  let s : ComplexMatrixGL N → ComplexMatrixGL N := fun g ↦ star g
  let mul : ComplexMatrixGL N × ComplexMatrixGL N → ComplexMatrixGL N :=
    fun p ↦ p.1 * p.2
  have hs : Measurable s := measurable_complexMatrixGL_star N
  have hmul : Measurable mul := by fun_prop
  unfold Measure.mconv
  calc
    Measure.map s (Measure.map mul (mu.prod nu)) =
        Measure.map (s ∘ mul) (mu.prod nu) :=
      Measure.map_map hs hmul
    _ = Measure.map
          ((mul ∘ Prod.map s s) ∘ Prod.swap) (mu.prod nu) := by
      apply Measure.map_congr
      filter_upwards [] with p
      rcases p with ⟨x, y⟩
      simp [s, mul, Function.comp_def, star_mul]
    _ = Measure.map (mul ∘ Prod.map s s)
          (Measure.map Prod.swap (mu.prod nu)) := by
      rw [Measure.map_map (by fun_prop) measurable_swap]
    _ = Measure.map (mul ∘ Prod.map s s) (nu.prod mu) := by
      rw [Measure.prod_swap]
    _ = Measure.map mul
          (Measure.map (Prod.map s s) (nu.prod mu)) := by
      rw [Measure.map_map hmul (hs.prodMap hs)]
    _ = Measure.map mul
          ((Measure.map s nu).prod (Measure.map s mu)) := by
      rw [Measure.map_prod_map nu mu hs hs]

/-- Transpose congruence is the left action of `GL_N(C)` on complex square
matrices relevant for symmetric Gram matrices. -/
def complexGLTransposeCongruence (N : ℕ)
    (g : ComplexMatrixGL N) (A : ConcreteMatrixState N) :
    ConcreteMatrixState N :=
  complexMatrixGLVal N g * A * (complexMatrixGLVal N g).transpose

theorem measurable_complexGLTransposeCongruence (N : ℕ) :
    Measurable fun p : ConcreteMatrixState N × ComplexMatrixGL N ↦
      complexGLTransposeCongruence N p.2 p.1 := by
  have hg : Measurable fun p : ConcreteMatrixState N × ComplexMatrixGL N ↦
      complexMatrixGLVal N p.2 :=
    (measurable_complexMatrixGLVal N).comp measurable_snd
  have hA : Measurable fun p : ConcreteMatrixState N × ComplexMatrixGL N ↦
      p.1 := measurable_fst
  have hgA := measurable_complexMatrix_mul hg hA
  have hgT := measurable_complexMatrix_transpose hg
  exact measurable_complexMatrix_mul hgA hgT

theorem measurable_complexGLTransposeCongruence_const (N : ℕ)
    (g : ComplexMatrixGL N) :
    Measurable (fun A : ConcreteMatrixState N ↦
      complexGLTransposeCongruence N g A) := by
  unfold complexGLTransposeCongruence
  have hg : Measurable (fun _A : ConcreteMatrixState N ↦
      complexMatrixGLVal N g) := measurable_const
  exact measurable_complexMatrix_mul
    (measurable_complexMatrix_mul hg measurable_id)
    (measurable_complexMatrix_transpose hg)

/-- Action of a factor law on a matrix law by transpose congruence.  The
product is ordered as `(state,factor)` to match `independentUpdateKernel`. -/
def congruenceMeasureAction (N : ℕ)
    (xi : Measure (ComplexMatrixGL N))
    (mu : Measure (ConcreteMatrixState N)) :
    Measure (ConcreteMatrixState N) :=
  (mu.prod xi).map
    (fun p ↦ complexGLTransposeCongruence N p.2 p.1)

theorem complexGLTransposeCongruence_mul
    (N : ℕ) (g h : ComplexMatrixGL N) (A : ConcreteMatrixState N) :
    complexGLTransposeCongruence N (g * h) A =
      complexGLTransposeCongruence N g
        (complexGLTransposeCongruence N h A) := by
  unfold complexGLTransposeCongruence complexMatrixGLVal
  simp only [Units.val_mul, Matrix.transpose_mul]
  simp [Matrix.mul_assoc]

/-- Multiplicative convolution of factor laws is composition of their
transpose-congruence actions. -/
theorem congruenceMeasureAction_mconv
    {N : ℕ}
    (xi eta : Measure (ComplexMatrixGL N))
    (mu : Measure (ConcreteMatrixState N))
    [IsProbabilityMeasure xi] [IsProbabilityMeasure eta]
    [IsProbabilityMeasure mu] :
    congruenceMeasureAction N (xi ∗ₘ eta) mu =
      congruenceMeasureAction N xi
        (congruenceMeasureAction N eta mu) := by
  let act : ConcreteMatrixState N × ComplexMatrixGL N →
      ConcreteMatrixState N :=
    fun p ↦ complexGLTransposeCongruence N p.2 p.1
  let mul : ComplexMatrixGL N × ComplexMatrixGL N →
      ComplexMatrixGL N := fun p ↦ p.1 * p.2
  have hact : Measurable act := measurable_complexGLTransposeCongruence N
  have hmul : Measurable mul := by fun_prop
  have hprod :
      mu.prod (xi ∗ₘ eta) =
        Measure.map (Prod.map id mul) (mu.prod (xi.prod eta)) := by
    calc
      mu.prod (xi ∗ₘ eta) =
          (Measure.map id mu).prod
            (Measure.map mul (xi.prod eta)) := by
        rw [Measure.map_id]
        rfl
      _ = Measure.map (Prod.map id mul) (mu.prod (xi.prod eta)) :=
        Measure.map_prod_map mu (xi.prod eta) measurable_id hmul
  have hassoc :
      Measure.map MeasurableEquiv.prodAssoc
          ((mu.prod xi).prod eta) =
        mu.prod (xi.prod eta) :=
    Measure.prodAssoc_prod
  calc
    congruenceMeasureAction N (xi ∗ₘ eta) mu =
        Measure.map act (mu.prod (xi ∗ₘ eta)) := rfl
    _ = Measure.map (act ∘ Prod.map id mul)
          (mu.prod (xi.prod eta)) := by
      rw [hprod]
      exact Measure.map_map hact (measurable_id.prodMap hmul)
    _ = Measure.map
          ((act ∘ Prod.map id mul) ∘ MeasurableEquiv.prodAssoc)
          ((mu.prod xi).prod eta) := by
      rw [← hassoc]
      exact Measure.map_map (by fun_prop)
        MeasurableEquiv.prodAssoc.measurable
    _ = Measure.map (act ∘ Prod.map act id)
          (Measure.map
            (LogdetLean.Coherence.middleToLast :
              (ConcreteMatrixState N × ComplexMatrixGL N) ×
                  ComplexMatrixGL N →
                (ConcreteMatrixState N × ComplexMatrixGL N) ×
                  ComplexMatrixGL N)
            ((mu.prod xi).prod eta)) := by
      rw [Measure.map_map (by fun_prop)
        LogdetLean.Coherence.measurable_middleToLast]
      apply Measure.map_congr
      filter_upwards [] with p
      rcases p with ⟨⟨A, g⟩, h⟩
      exact complexGLTransposeCongruence_mul N g h A
    _ = Measure.map (act ∘ Prod.map act id)
          ((mu.prod eta).prod xi) := by
      rw [LogdetLean.Coherence.map_middleToLast_prod]
    _ = congruenceMeasureAction N xi
          (congruenceMeasureAction N eta mu) := by
      unfold congruenceMeasureAction
      have hp := Measure.map_prod_map (mu.prod eta) xi hact measurable_id
      rw [Measure.map_id] at hp
      rw [hp]
      exact (Measure.map_map hact (hact.prodMap measurable_id)).symm

instance congruenceMeasureAction_isProbability
    (N : ℕ) (xi : Measure (ComplexMatrixGL N))
    (mu : Measure (ConcreteMatrixState N))
    [IsProbabilityMeasure xi] [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (congruenceMeasureAction N xi mu) := by
  unfold congruenceMeasureAction
  exact Measure.isProbabilityMeasure_map
    (measurable_complexGLTransposeCongruence N).aemeasurable

/-! ## Normalized unitary Haar inside `GL_N(C)` -/

theorem measurable_unitaryToComplexMatrixGL (N : ℕ) :
    Measurable (unitaryToComplexMatrixGL N) := by
  rw [measurable_comap_iff]
  exact measurable_subtype_coe

/-- The unitary transpose-congruence action, with the unitary and state bundled
as one argument.  Naming this map keeps later product-measure calculations
from repeatedly unfolding the matrix and `GL` coercions. -/
def unitaryTransposeCongruenceMap (N : ℕ)
    (p : Matrix.unitaryGroup (Fin N) ℂ × ConcreteMatrixState N) :
    ConcreteMatrixState N :=
  complexGLTransposeCongruence N
    (unitaryToComplexMatrixGL N p.1) p.2

theorem measurable_unitaryTransposeCongruenceMap (N : ℕ) :
    Measurable (unitaryTransposeCongruenceMap N) := by
  unfold unitaryTransposeCongruenceMap complexGLTransposeCongruence
  have hg : Measurable
      (fun p : Matrix.unitaryGroup (Fin N) ℂ × ConcreteMatrixState N ↦
        complexMatrixGLVal N (unitaryToComplexMatrixGL N p.1)) :=
    (measurable_complexMatrixGLVal N).comp
      ((measurable_unitaryToComplexMatrixGL N).comp measurable_fst)
  exact measurable_complexMatrix_mul
    (measurable_complexMatrix_mul hg measurable_snd)
    (measurable_complexMatrix_transpose hg)

/-- Normalized Haar probability on `U(N)`, pushed through the canonical
inclusion into `GL_N(C)`. -/
def unitaryHaarGLMeasure (N : ℕ) : Measure (ComplexMatrixGL N) :=
  Measure.map (unitaryToComplexMatrixGL N)
    (LocalAnticoncentration.unitaryHaarProbabilityMeasure N)

instance unitaryHaarGLMeasure_isProbability (N : ℕ) :
    IsProbabilityMeasure (unitaryHaarGLMeasure N) := by
  unfold unitaryHaarGLMeasure
  exact Measure.isProbabilityMeasure_map
    (measurable_unitaryToComplexMatrixGL N).aemeasurable

theorem map_unitaryHaarProbabilityMeasure_mul_right_internal
    (N : ℕ) (V : Matrix.unitaryGroup (Fin N) ℂ) :
    Measure.map (fun U : Matrix.unitaryGroup (Fin N) ℂ ↦ U * V)
        (LocalAnticoncentration.unitaryHaarProbabilityMeasure N) =
      LocalAnticoncentration.unitaryHaarProbabilityMeasure N := by
  let mu : Measure (Matrix.unitaryGroup (Fin N) ℂ) :=
    LocalAnticoncentration.unitaryHaarProbabilityMeasure N
  let nu : Measure (Matrix.unitaryGroup (Fin N) ℂ) :=
    Measure.map (fun U ↦ U * V) mu
  letI : CompactSpace (Matrix.unitaryGroup (Fin N) ℂ) :=
    isCompact_iff_compactSpace.mp
      (LocalAnticoncentration.unitaryGroup_carrier_isCompact N)
  letI : IsProbabilityMeasure mu :=
    LocalAnticoncentration.unitaryHaarProbabilityMeasure_isProbability N
  letI : Measure.IsHaarMeasure mu :=
    LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily.isHaar N
  haveI : IsProbabilityMeasure nu :=
    Measure.isProbabilityMeasure_map
      (measurable_mul_const V).aemeasurable
  letI : Measure.IsHaarMeasure nu := by
    dsimp only [nu]
    infer_instance
  have hnu : nu = mu :=
    Measure.isHaarMeasure_eq_of_isProbabilityMeasure nu mu
  simpa only [nu, mu] using hnu

/-- Normalized Haar probability on `U(N)` is invariant under inversion.  This
is derived from right invariance and uniqueness of normalized Haar measure. -/
theorem map_unitaryHaarProbabilityMeasure_inv_internal (N : ℕ) :
    Measure.map (fun U : Matrix.unitaryGroup (Fin N) ℂ ↦ U⁻¹)
        (LocalAnticoncentration.unitaryHaarProbabilityMeasure N) =
      LocalAnticoncentration.unitaryHaarProbabilityMeasure N := by
  let mu : Measure (Matrix.unitaryGroup (Fin N) ℂ) :=
    LocalAnticoncentration.unitaryHaarProbabilityMeasure N
  let nu : Measure (Matrix.unitaryGroup (Fin N) ℂ) :=
    Measure.map Inv.inv mu
  letI : CompactSpace (Matrix.unitaryGroup (Fin N) ℂ) :=
    isCompact_iff_compactSpace.mp
      (LocalAnticoncentration.unitaryGroup_carrier_isCompact N)
  letI : IsProbabilityMeasure mu :=
    LocalAnticoncentration.unitaryHaarProbabilityMeasure_isProbability N
  letI : Measure.IsHaarMeasure mu :=
    LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily.isHaar N
  letI : Measure.IsMulRightInvariant mu :=
    ⟨map_unitaryHaarProbabilityMeasure_mul_right_internal N⟩
  haveI : IsProbabilityMeasure nu :=
    Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
  letI : Measure.IsHaarMeasure nu := by
    change Measure.IsHaarMeasure mu.inv
    exact {
      toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := inferInstance
    }
  have hnu : nu = mu :=
    Measure.isHaarMeasure_eq_of_isProbabilityMeasure nu mu
  simpa only [nu, mu] using hnu

/-- The pushed-forward unitary Haar measure in `GL_N(C)` is invariant under
conjugate transpose. -/
theorem map_star_unitaryHaarGLMeasure (N : ℕ) :
    Measure.map (fun g : ComplexMatrixGL N ↦ star g)
        (unitaryHaarGLMeasure N) =
      unitaryHaarGLMeasure N := by
  let emb := unitaryToComplexMatrixGL N
  let haar := LocalAnticoncentration.unitaryHaarProbabilityMeasure N
  have hemb : Measurable emb := measurable_unitaryToComplexMatrixGL N
  have hstar : Measurable (fun g : ComplexMatrixGL N ↦ star g) :=
    measurable_complexMatrixGL_star N
  have hinv := map_unitaryHaarProbabilityMeasure_inv_internal N
  calc
    Measure.map (fun g : ComplexMatrixGL N ↦ star g)
        (unitaryHaarGLMeasure N) =
      Measure.map ((fun g : ComplexMatrixGL N ↦ star g) ∘ emb) haar := by
        unfold unitaryHaarGLMeasure
        rw [Measure.map_map hstar hemb]
    _ = Measure.map (emb ∘ Inv.inv) haar := by
      apply Measure.map_congr
      filter_upwards [] with U
      rfl
    _ = Measure.map emb (Measure.map Inv.inv haar) := by
      rw [Measure.map_map hemb measurable_inv]
    _ = unitaryHaarGLMeasure N := by
      rw [hinv]
      rfl

theorem map_unitaryHaarGLMeasure_mul_left
    (N : ℕ) (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measure.map
        (fun g : ComplexMatrixGL N ↦
          unitaryToComplexMatrixGL N U * g)
        (unitaryHaarGLMeasure N) =
      unitaryHaarGLMeasure N := by
  let emb := unitaryToComplexMatrixGL N
  let haar := LocalAnticoncentration.unitaryHaarProbabilityMeasure N
  have hemb : Measurable emb := measurable_unitaryToComplexMatrixGL N
  have hleft :
      Measure.map (fun V : Matrix.unitaryGroup (Fin N) ℂ ↦ U * V) haar =
        haar := by
    letI : Measure.IsHaarMeasure haar :=
      LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily.isHaar N
    exact map_mul_left_eq_self haar U
  calc
    Measure.map (fun g : ComplexMatrixGL N ↦ emb U * g)
        (unitaryHaarGLMeasure N) =
      Measure.map (fun V : Matrix.unitaryGroup (Fin N) ℂ ↦ emb (U * V))
        haar := by
          unfold unitaryHaarGLMeasure
          rw [Measure.map_map (measurable_const_mul _) hemb]
          apply Measure.map_congr
          filter_upwards [] with V
          exact (emb.map_mul U V).symm
    _ = Measure.map emb
        (Measure.map (fun V : Matrix.unitaryGroup (Fin N) ℂ ↦ U * V)
          haar) := by
            exact (Measure.map_map hemb (measurable_const_mul U)).symm
    _ = unitaryHaarGLMeasure N := by
      rw [hleft]
      rfl

theorem map_unitaryHaarGLMeasure_mul_right
    (N : ℕ) (V : Matrix.unitaryGroup (Fin N) ℂ) :
    Measure.map
        (fun g : ComplexMatrixGL N ↦
          g * unitaryToComplexMatrixGL N V)
        (unitaryHaarGLMeasure N) =
      unitaryHaarGLMeasure N := by
  let emb := unitaryToComplexMatrixGL N
  let haar := LocalAnticoncentration.unitaryHaarProbabilityMeasure N
  have hemb : Measurable emb := measurable_unitaryToComplexMatrixGL N
  have hright := map_unitaryHaarProbabilityMeasure_mul_right_internal N V
  calc
    Measure.map (fun g : ComplexMatrixGL N ↦ g * emb V)
        (unitaryHaarGLMeasure N) =
      Measure.map (fun U : Matrix.unitaryGroup (Fin N) ℂ ↦ emb (U * V))
        haar := by
          unfold unitaryHaarGLMeasure
          rw [Measure.map_map (measurable_mul_const _) hemb]
          apply Measure.map_congr
          filter_upwards [] with U
          exact (emb.map_mul U V).symm
    _ = Measure.map emb
        (Measure.map (fun U : Matrix.unitaryGroup (Fin N) ℂ ↦ U * V)
          haar) := by
            exact (Measure.map_map hemb (measurable_mul_const V)).symm
    _ = unitaryHaarGLMeasure N := by
      rw [hright]
      rfl

theorem dirac_unitary_mconv_unitaryHaarGLMeasure
    (N : ℕ) (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measure.dirac (unitaryToComplexMatrixGL N U) ∗ₘ
        unitaryHaarGLMeasure N =
      unitaryHaarGLMeasure N := by
  rw [Measure.dirac_mconv]
  exact map_unitaryHaarGLMeasure_mul_left N U

theorem unitaryHaarGLMeasure_mconv_dirac_unitary
    (N : ℕ) (U : Matrix.unitaryGroup (Fin N) ℂ) :
    unitaryHaarGLMeasure N ∗ₘ
        Measure.dirac (unitaryToComplexMatrixGL N U) =
      unitaryHaarGLMeasure N := by
  rw [Measure.mconv_dirac]
  exact map_unitaryHaarGLMeasure_mul_right N U

/-- Haar-sandwich a factor law on both sides. -/
def unitaryHaarSandwich (N : ℕ)
    (xi : Measure (ComplexMatrixGL N)) : Measure (ComplexMatrixGL N) :=
  (unitaryHaarGLMeasure N ∗ₘ xi) ∗ₘ unitaryHaarGLMeasure N

instance unitaryHaarSandwich_isProbability
    (N : ℕ) (xi : Measure (ComplexMatrixGL N))
    [IsProbabilityMeasure xi] :
    IsProbabilityMeasure (unitaryHaarSandwich N xi) := by
  unfold unitaryHaarSandwich
  infer_instance

theorem unitaryHaarSandwich_isUnitaryBiInvariant
    (N : ℕ) (xi : Measure (ComplexMatrixGL N))
    [IsProbabilityMeasure xi] :
    IsUnitaryBiInvariant N (unitaryHaarSandwich N xi) := by
  intro U V
  let kappa := unitaryHaarGLMeasure N
  let dU : Measure (ComplexMatrixGL N) :=
    Measure.dirac (unitaryToComplexMatrixGL N U)
  let dV : Measure (ComplexMatrixGL N) :=
    Measure.dirac (unitaryToComplexMatrixGL N V)
  have hleft : dU ∗ₘ kappa = kappa :=
    dirac_unitary_mconv_unitaryHaarGLMeasure N U
  have hright : kappa ∗ₘ dV = kappa :=
    unitaryHaarGLMeasure_mconv_dirac_unitary N V
  change (dU ∗ₘ ((kappa ∗ₘ xi) ∗ₘ kappa)) ∗ₘ dV =
    (kappa ∗ₘ xi) ∗ₘ kappa
  calc
    (dU ∗ₘ ((kappa ∗ₘ xi) ∗ₘ kappa)) ∗ₘ dV =
        ((((dU ∗ₘ kappa) ∗ₘ xi) ∗ₘ kappa) ∗ₘ dV) := by
      rw [Measure.mconv_assoc dU kappa xi,
        Measure.mconv_assoc dU (kappa ∗ₘ xi) kappa]
    _ = (((kappa ∗ₘ xi) ∗ₘ kappa) ∗ₘ dV) := by
      rw [hleft]
    _ = (kappa ∗ₘ xi) ∗ₘ (kappa ∗ₘ dV) :=
      Measure.mconv_assoc (kappa ∗ₘ xi) kappa dV
    _ = (kappa ∗ₘ xi) ∗ₘ kappa := by rw [hright]

/-! ## Internal finite-dimensional Gelfand trick -/

/-- The orbital probability measures of `g` and its conjugate transpose are
equal.  Polar decomposition supplies the unitary double-coset identity; Haar
invariance then removes the two unitary factors. -/
theorem unitary_orbitalMeasure_star_eq
    (N : ℕ) (g : ComplexMatrixGL N) :
    (unitaryHaarGLMeasure N ∗ₘ Measure.dirac (star g)) ∗ₘ
        unitaryHaarGLMeasure N =
      (unitaryHaarGLMeasure N ∗ₘ Measure.dirac g) ∗ₘ
        unitaryHaarGLMeasure N := by
  rcases exists_unitary_conjTranspose_eq_mul_self_mul g with ⟨W, hW⟩
  let kappa := unitaryHaarGLMeasure N
  let w : ComplexMatrixGL N := unitaryToComplexMatrixGL N W
  let dW : Measure (ComplexMatrixGL N) := Measure.dirac w
  let dg : Measure (ComplexMatrixGL N) := Measure.dirac g
  have hstarGL : star g = w * g * w := by
    apply Units.ext
    exact hW
  have hdirac : Measure.dirac (star g) = (dW ∗ₘ dg) ∗ₘ dW := by
    rw [hstarGL]
    simp [dW, dg, Measure.dirac_mconv_dirac]
  have hright : kappa ∗ₘ dW = kappa :=
    unitaryHaarGLMeasure_mconv_dirac_unitary N W
  have hleft : dW ∗ₘ kappa = kappa :=
    dirac_unitary_mconv_unitaryHaarGLMeasure N W
  change (kappa ∗ₘ Measure.dirac (star g)) ∗ₘ kappa =
    (kappa ∗ₘ dg) ∗ₘ kappa
  rw [hdirac]
  calc
    (kappa ∗ₘ ((dW ∗ₘ dg) ∗ₘ dW)) ∗ₘ kappa =
        kappa ∗ₘ (dW ∗ₘ (dg ∗ₘ (dW ∗ₘ kappa))) := by
      simp only [Measure.mconv_assoc]
    _ = kappa ∗ₘ (dW ∗ₘ (dg ∗ₘ kappa)) := by rw [hleft]
    _ = (kappa ∗ₘ dW) ∗ₘ (dg ∗ₘ kappa) := by
      rw [Measure.mconv_assoc]
    _ = kappa ∗ₘ (dg ∗ₘ kappa) := by rw [hright]
    _ = (kappa ∗ₘ dg) ∗ₘ kappa :=
      (Measure.mconv_assoc kappa dg kappa).symm

/-- Haar sandwiching cannot distinguish a factor law from its pushforward by
conjugate transpose.  This is Tonelli's theorem applied to the preceding
pointwise orbital identity. -/
theorem unitaryHaarSandwich_map_star_eq
    (N : ℕ) (xi : Measure (ComplexMatrixGL N))
    [IsProbabilityMeasure xi] :
    (unitaryHaarGLMeasure N ∗ₘ
        Measure.map (fun g : ComplexMatrixGL N ↦ star g) xi) ∗ₘ
          unitaryHaarGLMeasure N =
      unitaryHaarSandwich N xi := by
  let kappa := unitaryHaarGLMeasure N
  let s : ComplexMatrixGL N → ComplexMatrixGL N := fun g ↦ star g
  have hs : Measurable s := measurable_complexMatrixGL_star N
  have hswap (rho : Measure (ComplexMatrixGL N)) [SFinite rho]
      (F : ComplexMatrixGL N × ComplexMatrixGL N → ℝ≥0∞)
      (hF : Measurable F) :
      ∫⁻ u, ∫⁻ g, F (u, g) ∂rho ∂kappa =
        ∫⁻ g, ∫⁻ u, F (u, g) ∂kappa ∂rho := by
    calc
      ∫⁻ u, ∫⁻ g, F (u, g) ∂rho ∂kappa =
          ∫⁻ p, F p ∂(kappa.prod rho) :=
        (MeasureTheory.lintegral_prod F hF.aemeasurable).symm
      _ = ∫⁻ g, ∫⁻ u, F (u, g) ∂kappa ∂rho :=
        MeasureTheory.lintegral_prod_symm' F hF
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  let F : ComplexMatrixGL N × ComplexMatrixGL N → ℝ≥0∞ :=
    fun p ↦ ∫⁻ v, f ((p.1 * p.2) * v) ∂kappa
  have hF : Measurable F := by
    dsimp only [F]
    fun_prop
  have horbInt (g : ComplexMatrixGL N) :
      ∫⁻ u, ∫⁻ v, f ((u * star g) * v) ∂kappa ∂kappa =
        ∫⁻ u, ∫⁻ v, f ((u * g) * v) ∂kappa ∂kappa := by
    have horb := unitary_orbitalMeasure_star_eq N g
    have hmeasure := congrArg
      (fun rho : Measure (ComplexMatrixGL N) ↦ ∫⁻ z, f z ∂rho) horb
    calc
      ∫⁻ u, ∫⁻ v, f ((u * star g) * v) ∂kappa ∂kappa =
          ∫⁻ z, f z ∂((kappa ∗ₘ Measure.dirac (star g)) ∗ₘ kappa) := by
        rw [Measure.lintegral_mconv hf,
          Measure.lintegral_mconv (by fun_prop)]
        refine MeasureTheory.lintegral_congr fun u ↦ ?_
        rw [MeasureTheory.lintegral_dirac' (star g) (by fun_prop)]
      _ = ∫⁻ z, f z ∂((kappa ∗ₘ Measure.dirac g) ∗ₘ kappa) :=
        hmeasure
      _ = ∫⁻ u, ∫⁻ v, f ((u * g) * v) ∂kappa ∂kappa := by
        rw [Measure.lintegral_mconv hf,
          Measure.lintegral_mconv (by fun_prop)]
        refine MeasureTheory.lintegral_congr fun u ↦ ?_
        rw [MeasureTheory.lintegral_dirac' g (by fun_prop)]
  change ∫⁻ z, f z ∂((kappa ∗ₘ Measure.map s xi) ∗ₘ kappa) =
    ∫⁻ z, f z ∂((kappa ∗ₘ xi) ∗ₘ kappa)
  calc
    ∫⁻ z, f z ∂((kappa ∗ₘ Measure.map s xi) ∗ₘ kappa) =
        ∫⁻ u, ∫⁻ g, F (u, g) ∂(Measure.map s xi) ∂kappa := by
      rw [Measure.lintegral_mconv hf,
        Measure.lintegral_mconv (by fun_prop)]
    _ = ∫⁻ g, ∫⁻ u, F (u, g) ∂kappa ∂(Measure.map s xi) :=
      hswap (Measure.map s xi) F hF
    _ = ∫⁻ g, ∫⁻ u, F (u, star g) ∂kappa ∂xi := by
      rw [MeasureTheory.lintegral_map (by fun_prop) hs]
    _ = ∫⁻ g, ∫⁻ u, F (u, g) ∂kappa ∂xi := by
      refine MeasureTheory.lintegral_congr fun g ↦ ?_
      exact horbInt g
    _ = ∫⁻ u, ∫⁻ g, F (u, g) ∂xi ∂kappa :=
      (hswap xi F hF).symm
    _ = ∫⁻ z, f z ∂((kappa ∗ₘ xi) ∗ₘ kappa) := by
      rw [Measure.lintegral_mconv hf,
        Measure.lintegral_mconv (by fun_prop)]

/-- Every Haar-sandwiched probability law is invariant under conjugate
transpose. -/
theorem map_star_unitaryHaarSandwich_eq_self
    (N : ℕ) (xi : Measure (ComplexMatrixGL N))
    [IsProbabilityMeasure xi] :
    Measure.map (fun g : ComplexMatrixGL N ↦ star g)
        (unitaryHaarSandwich N xi) =
      unitaryHaarSandwich N xi := by
  let kappa := unitaryHaarGLMeasure N
  let s : ComplexMatrixGL N → ComplexMatrixGL N := fun g ↦ star g
  have hkappa : Measure.map s kappa = kappa :=
    map_star_unitaryHaarGLMeasure N
  calc
    Measure.map s (unitaryHaarSandwich N xi) =
        Measure.map s kappa ∗ₘ
          Measure.map s (kappa ∗ₘ xi) := by
      unfold unitaryHaarSandwich
      exact map_star_mconv (kappa ∗ₘ xi) kappa
    _ = kappa ∗ₘ (Measure.map s xi ∗ₘ Measure.map s kappa) := by
      rw [map_star_mconv kappa xi, hkappa]
    _ = (kappa ∗ₘ Measure.map s xi) ∗ₘ kappa := by
      rw [hkappa]
      exact (Measure.mconv_assoc kappa (Measure.map s xi) kappa).symm
    _ = unitaryHaarSandwich N xi :=
      unitaryHaarSandwich_map_star_eq N xi

/-- The specialized finite-dimensional Gelfand theorem actually used by H2:
two Haar-sandwiched factor laws commute.  It is now derived internally from
polar decomposition, normalized Haar uniqueness, and Tonelli. -/
theorem unitaryHaarSandwich_mconv_comm
    (N : ℕ) (xi eta : Measure (ComplexMatrixGL N))
    [IsProbabilityMeasure xi] [IsProbabilityMeasure eta] :
    unitaryHaarSandwich N xi ∗ₘ unitaryHaarSandwich N eta =
      unitaryHaarSandwich N eta ∗ₘ unitaryHaarSandwich N xi := by
  let kappa := unitaryHaarGLMeasure N
  let xiHat := unitaryHaarSandwich N xi
  let etaHat := unitaryHaarSandwich N eta
  let zeta : Measure (ComplexMatrixGL N) :=
    (xi ∗ₘ kappa) ∗ₘ (kappa ∗ₘ eta)
  letI : IsProbabilityMeasure zeta := by
    dsimp only [zeta]
    infer_instance
  have hproduct : xiHat ∗ₘ etaHat = unitaryHaarSandwich N zeta := by
    dsimp only [xiHat, etaHat, zeta, unitaryHaarSandwich, kappa]
    simp only [Measure.mconv_assoc]
  have hstarProduct :
      Measure.map (fun g : ComplexMatrixGL N ↦ star g)
          (xiHat ∗ₘ etaHat) = xiHat ∗ₘ etaHat := by
    rw [hproduct]
    exact map_star_unitaryHaarSandwich_eq_self N zeta
  have hstarXi :
      Measure.map (fun g : ComplexMatrixGL N ↦ star g) xiHat = xiHat :=
    map_star_unitaryHaarSandwich_eq_self N xi
  have hstarEta :
      Measure.map (fun g : ComplexMatrixGL N ↦ star g) etaHat = etaHat :=
    map_star_unitaryHaarSandwich_eq_self N eta
  change xiHat ∗ₘ etaHat = etaHat ∗ₘ xiHat
  calc
    xiHat ∗ₘ etaHat =
        Measure.map (fun g : ComplexMatrixGL N ↦ star g)
          (xiHat ∗ₘ etaHat) := hstarProduct.symm
    _ = Measure.map (fun g : ComplexMatrixGL N ↦ star g) etaHat ∗ₘ
          Measure.map (fun g : ComplexMatrixGL N ↦ star g) xiHat :=
      map_star_mconv xiHat etaHat
    _ = etaHat ∗ₘ xiHat := by rw [hstarEta, hstarXi]

/-- Backwards-compatible public name for the H2 Gelfand step.  Its former
axiomatic declaration has been replaced by the exact specialized theorem that
the H2 adapter uses: commutativity of two Haar-sandwiched probability laws. -/
theorem glComplex_unitary_biinvariant_finiteMeasure_mconv_comm
    (N : ℕ) (xi eta : Measure (ComplexMatrixGL N))
    [IsProbabilityMeasure xi] [IsProbabilityMeasure eta] :
    unitaryHaarSandwich N xi ∗ₘ unitaryHaarSandwich N eta =
      unitaryHaarSandwich N eta ∗ₘ unitaryHaarSandwich N xi :=
  unitaryHaarSandwich_mconv_comm N xi eta

/-! ## Generic Gelfand-to-action adapter -/

/-- A matrix law is fixed by Haar-averaged unitary transpose congruence. -/
def IsUnitaryCongruenceInvariant (N : ℕ)
    (mu : Measure (ConcreteMatrixState N)) : Prop :=
  congruenceMeasureAction N (unitaryHaarGLMeasure N) mu = mu

/-- Pointwise form of unitary transpose-congruence invariance.  This is the
natural endpoint of a direct Haar-corner equivariance proof. -/
def IsPointwiseUnitaryCongruenceInvariant (N : ℕ)
    (mu : Measure (ConcreteMatrixState N)) : Prop :=
  ∀ U : Matrix.unitaryGroup (Fin N) ℂ,
    Measure.map
        (fun A ↦ complexGLTransposeCongruence N
          (unitaryToComplexMatrixGL N U) A) mu = mu

set_option maxHeartbeats 800000 in
theorem IsPointwiseUnitaryCongruenceInvariant.toAveraged
    {N : ℕ} {mu : Measure (ConcreteMatrixState N)}
    [IsProbabilityMeasure mu]
    (hmu : IsPointwiseUnitaryCongruenceInvariant N mu) :
    IsUnitaryCongruenceInvariant N mu := by
  let haar := LocalAnticoncentration.unitaryHaarProbabilityMeasure N
  let emb := unitaryToComplexMatrixGL N
  let act : ConcreteMatrixState N × ComplexMatrixGL N →
      ConcreteMatrixState N :=
    fun p ↦ complexGLTransposeCongruence N p.2 p.1
  let F := unitaryTransposeCongruenceMap N
  have hemb : Measurable emb := measurable_unitaryToComplexMatrixGL N
  have hact : Measurable act := measurable_complexGLTransposeCongruence N
  have hF : Measurable F := measurable_unitaryTransposeCongruenceMap N
  have hreorder :
      congruenceMeasureAction N (unitaryHaarGLMeasure N) mu =
        Measure.map F (haar.prod mu) := by
    unfold congruenceMeasureAction unitaryHaarGLMeasure
    calc
      Measure.map act (mu.prod (Measure.map emb haar)) =
          Measure.map act
            (Measure.map (Prod.map id emb) (mu.prod haar)) := by
        rw [← Measure.map_prod_map mu haar measurable_id hemb,
          Measure.map_id]
      _ = Measure.map (act ∘ Prod.map id emb) (mu.prod haar) :=
        Measure.map_map hact (measurable_id.prodMap hemb)
      _ = Measure.map (act ∘ Prod.map id emb)
          (Measure.map Prod.swap (haar.prod mu)) := by
        rw [Measure.prod_swap]
      _ = Measure.map ((act ∘ Prod.map id emb) ∘ Prod.swap)
          (haar.prod mu) :=
        Measure.map_map (by fun_prop) measurable_swap
      _ = Measure.map F (haar.prod mu) := by
        apply Measure.map_congr
        filter_upwards [] with p
        rfl
  rw [IsUnitaryCongruenceInvariant, hreorder]
  ext s hs
  rw [Measure.map_apply hF hs, Measure.prod_apply (hF hs)]
  have hsection (U : Matrix.unitaryGroup (Fin N) ℂ) :
      mu (Prod.mk U ⁻¹' (F ⁻¹' s)) = mu s := by
    have hU := congrArg (fun nu : Measure (ConcreteMatrixState N) ↦ nu s)
      (hmu U)
    have hUm : Measurable fun A ↦
        complexGLTransposeCongruence N (emb U) A :=
      measurable_complexGLTransposeCongruence_const N (emb U)
    rw [Measure.map_apply hUm hs] at hU
    exact hU
  simp_rw [hsection]
  letI : IsProbabilityMeasure haar :=
    LocalAnticoncentration.unitaryHaarProbabilityMeasure_isProbability N
  simp

/-- A factor law preserves unitary-congruence-invariant probability laws. -/
def PreservesUnitaryCongruenceInvariant (N : ℕ)
    (xi : Measure (ComplexMatrixGL N)) : Prop :=
  ∀ mu : Measure (ConcreteMatrixState N),
    IsProbabilityMeasure mu →
    IsUnitaryCongruenceInvariant N mu →
    IsUnitaryCongruenceInvariant N (congruenceMeasureAction N xi mu)

theorem unitaryHaarSandwich_action_eq
    {N : ℕ} (xi : Measure (ComplexMatrixGL N))
    (mu : Measure (ConcreteMatrixState N))
    [IsProbabilityMeasure xi] [IsProbabilityMeasure mu]
    (hmu : IsUnitaryCongruenceInvariant N mu)
    (hpres : PreservesUnitaryCongruenceInvariant N xi) :
    congruenceMeasureAction N (unitaryHaarSandwich N xi) mu =
      congruenceMeasureAction N xi mu := by
  let kappa := unitaryHaarGLMeasure N
  have hximu : IsUnitaryCongruenceInvariant N
      (congruenceMeasureAction N xi mu) :=
    hpres mu (by infer_instance) hmu
  unfold unitaryHaarSandwich
  rw [congruenceMeasureAction_mconv,
    congruenceMeasureAction_mconv]
  rw [show congruenceMeasureAction N kappa mu = mu from hmu]
  exact hximu

/-- Generic H2 adapter: two congruence-factor laws commute on every invariant
input law once their Haar sandwiches are passed to the finite-measure
Gelfand-pair theorem. -/
theorem congruenceMeasureActions_commute_of_unitary_invariant
    {N : ℕ}
    (xi eta : Measure (ComplexMatrixGL N))
    (mu : Measure (ConcreteMatrixState N))
    [IsProbabilityMeasure xi] [IsProbabilityMeasure eta]
    [IsProbabilityMeasure mu]
    (hmu : IsUnitaryCongruenceInvariant N mu)
    (hxi : PreservesUnitaryCongruenceInvariant N xi)
    (heta : PreservesUnitaryCongruenceInvariant N eta) :
    congruenceMeasureAction N xi
        (congruenceMeasureAction N eta mu) =
      congruenceMeasureAction N eta
        (congruenceMeasureAction N xi mu) := by
  let xiHat := unitaryHaarSandwich N xi
  let etaHat := unitaryHaarSandwich N eta
  have hcomm : xiHat ∗ₘ etaHat = etaHat ∗ₘ xiHat :=
    unitaryHaarSandwich_mconv_comm N xi eta
  have hetaMu : IsUnitaryCongruenceInvariant N
      (congruenceMeasureAction N eta mu) :=
    heta mu (by infer_instance) hmu
  have hxiMu : IsUnitaryCongruenceInvariant N
      (congruenceMeasureAction N xi mu) :=
    hxi mu (by infer_instance) hmu
  calc
    congruenceMeasureAction N xi (congruenceMeasureAction N eta mu) =
        congruenceMeasureAction N xiHat
          (congruenceMeasureAction N etaHat mu) := by
      rw [unitaryHaarSandwich_action_eq eta mu hmu heta,
        unitaryHaarSandwich_action_eq xi
          (congruenceMeasureAction N eta mu) hetaMu hxi]
    _ = congruenceMeasureAction N (xiHat ∗ₘ etaHat) mu := by
      rw [congruenceMeasureAction_mconv]
    _ = congruenceMeasureAction N (etaHat ∗ₘ xiHat) mu := by rw [hcomm]
    _ = congruenceMeasureAction N etaHat
          (congruenceMeasureAction N xiHat mu) :=
      congruenceMeasureAction_mconv etaHat xiHat mu
    _ = congruenceMeasureAction N eta
          (congruenceMeasureAction N xi mu) := by
      rw [unitaryHaarSandwich_action_eq xi mu hmu hxi,
        unitaryHaarSandwich_action_eq eta
          (congruenceMeasureAction N xi mu) hxiMu heta]

end

end LogdetLean.GramHafnian.UltimateHiding.Dense

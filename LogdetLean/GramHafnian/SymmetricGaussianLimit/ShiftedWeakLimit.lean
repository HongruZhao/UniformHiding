import LogdetLean.GramHafnian.SymmetricGaussianLimit.ExplicitFactor
import LogdetLean.GramHafnian.ShiftedAnticoncentration.CofactorTypeHafnian
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Independent shifts and the symmetric-Gaussian weak limit

This file isolates the Slutsky/continuous-mapping step needed after the
matrix-valued Gram limit.  An arbitrary shift law is placed on a separate
factor of a product probability space, so independence is literal.  A
matrix-valued remainder which tends to zero in probability can then be
added without changing the weak limit, and the result can be pushed through
the hafnian.

The final results record that a fixed finite-dimensional random matrix,
multiplied by `m⁻¹`, tends to zero in probability, and feed this fact directly
into the shifted-hafnian endpoint.  In particular, the explicit-factor cross
term needs no moment assumption on the independent shift law.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace LogdetLean.GramHafnian.SymmetricGaussianLimit

noncomputable section

/-- Pair a weakly convergent random variable with an arbitrary independent
coordinate.  Independence is represented by the product probability
measure; the second coordinate has exactly the prescribed law at every
index. -/
theorem independentPair_tendstoInDistribution_of_weakLimit
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    [SeminormedAddCommGroup E] [SecondCountableTopology E] [BorelSpace E]
    (base : ProbabilityMeasure Omega)
    (shift limitLaw : ProbabilityMeasure E)
    (X : ℕ → Omega → E) (hX : ∀ m, Measurable (X m))
    (hweak : Tendsto
      (fun m ↦ base.map (hX m).aemeasurable)
      atTop (nhds limitLaw)) :
    TendstoInDistribution
      (fun m (p : Omega × E) ↦ (X m p.1, p.2)) atTop
      (fun p : E × E ↦ p)
      (fun _ ↦ ((base.prod shift : ProbabilityMeasure (Omega × E)) :
        Measure (Omega × E)))
      ((limitLaw.prod shift : ProbabilityMeasure (E × E)) :
        Measure (E × E)) := by
  have hprod : Tendsto
      (fun m ↦ (base.map (hX m).aemeasurable).prod shift)
      atTop (nhds (limitLaw.prod shift)) := by
    exact (ProbabilityMeasure.continuous_prod.tendsto (limitLaw, shift)).comp
      (hweak.prodMk_nhds
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ ↦ shift) atTop (nhds shift)))
  refine ⟨?_, measurable_id.aemeasurable, ?_⟩
  · intro m
    exact ((hX m).comp measurable_fst).prodMk measurable_snd |>.aemeasurable
  · have hshift_id :
        shift.map measurable_id.aemeasurable = shift := by
      apply Subtype.ext
      change Measure.map id (shift : Measure E) = (shift : Measure E)
      exact Measure.map_id
    have hsource (m : ℕ) :
        (base.prod shift).map
            (((hX m).comp measurable_fst).prodMk measurable_snd).aemeasurable =
          (base.map (hX m).aemeasurable).prod shift := by
      calc
        _ = (base.map (hX m).aemeasurable).prod
            (shift.map measurable_id.aemeasurable) :=
          (ProbabilityMeasure.map_prod_map base shift (hX m) measurable_id).symm
        _ = _ := by rw [hshift_id]
    have hlimit :
        (limitLaw.prod shift).map measurable_id.aemeasurable =
          limitLaw.prod shift := by
      apply Subtype.ext
      change Measure.map id
        ((limitLaw.prod shift : ProbabilityMeasure (E × E)) : Measure (E × E)) =
          ((limitLaw.prod shift : ProbabilityMeasure (E × E)) : Measure (E × E))
      exact Measure.map_id
    change Tendsto
      (fun m ↦ (base.prod shift).map
        (((hX m).comp measurable_fst).prodMk measurable_snd).aemeasurable)
      atTop (nhds ((limitLaw.prod shift).map measurable_id.aemeasurable))
    simpa only [hsource, hlimit] using hprod

/-- Generic independent-shift Slutsky theorem.  The unshifted law has the
explicit weak-limit premise `hweak`; `shift` is an arbitrary independent
law; and `remainder` is the only quantity required to converge to zero in
probability. -/
theorem independentAdditiveShift_tendstoInDistribution_of_weakLimit
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    [SeminormedAddCommGroup E] [SecondCountableTopology E] [BorelSpace E]
    (base : ProbabilityMeasure Omega)
    (shift limitLaw : ProbabilityMeasure E)
    (X : ℕ → Omega → E) (hX : ∀ m, Measurable (X m))
    (hweak : Tendsto
      (fun m ↦ base.map (hX m).aemeasurable)
      atTop (nhds limitLaw))
    (remainder : ℕ → Omega × E → E)
    (hremainder : TendstoInMeasure
      ((base.prod shift : ProbabilityMeasure (Omega × E)) : Measure (Omega × E))
      remainder atTop 0)
    (hremainder_meas : ∀ m, AEMeasurable (remainder m)
      ((base.prod shift : ProbabilityMeasure (Omega × E)) : Measure (Omega × E))) :
    TendstoInDistribution
      (fun m (p : Omega × E) ↦ X m p.1 + p.2 + remainder m p) atTop
      (fun p : E × E ↦ p.1 + p.2)
      (fun _ ↦ ((base.prod shift : ProbabilityMeasure (Omega × E)) :
        Measure (Omega × E)))
      ((limitLaw.prod shift : ProbabilityMeasure (E × E)) :
        Measure (E × E)) := by
  have hpair := independentPair_tendstoInDistribution_of_weakLimit
    base shift limitLaw X hX hweak
  have hcore : TendstoInDistribution
      (fun m (p : Omega × E) ↦ X m p.1 + p.2) atTop
      (fun p : E × E ↦ p.1 + p.2)
      (fun _ ↦ ((base.prod shift : ProbabilityMeasure (Omega × E)) :
        Measure (Omega × E)))
      ((limitLaw.prod shift : ProbabilityMeasure (E × E)) :
        Measure (E × E)) := by
    exact hpair.continuous_comp (g := fun p : E × E ↦ p.1 + p.2) (by fun_prop)
  have hadd := hcore.add_of_tendstoInMeasure_const
    hremainder hremainder_meas
  exact hadd.congr
    (fun _ ↦ Filter.Eventually.of_forall fun _ ↦ rfl)
    (Filter.Eventually.of_forall fun _ ↦ add_zero _)

/-- Continuous-mapping form of the independent-shift Slutsky theorem. -/
theorem independentAdditiveShift_continuousMap_tendstoInDistribution_of_weakLimit
    {Omega E F : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    [SeminormedAddCommGroup E] [SecondCountableTopology E] [BorelSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    (base : ProbabilityMeasure Omega)
    (shift limitLaw : ProbabilityMeasure E)
    (X : ℕ → Omega → E) (hX : ∀ m, Measurable (X m))
    (hweak : Tendsto
      (fun m ↦ base.map (hX m).aemeasurable)
      atTop (nhds limitLaw))
    (remainder : ℕ → Omega × E → E)
    (hremainder : TendstoInMeasure
      ((base.prod shift : ProbabilityMeasure (Omega × E)) : Measure (Omega × E))
      remainder atTop 0)
    (hremainder_meas : ∀ m, AEMeasurable (remainder m)
      ((base.prod shift : ProbabilityMeasure (Omega × E)) : Measure (Omega × E)))
    (g : E → F) (hg : Continuous g) :
    TendstoInDistribution
      (fun m p ↦ g (X m p.1 + p.2 + remainder m p)) atTop
      (fun p : E × E ↦ g (p.1 + p.2))
      (fun _ ↦ ((base.prod shift : ProbabilityMeasure (Omega × E)) :
        Measure (Omega × E)))
      ((limitLaw.prod shift : ProbabilityMeasure (E × E)) :
        Measure (E × E)) := by
  exact (independentAdditiveShift_tendstoInDistribution_of_weakLimit
    base shift limitLaw X hX hweak remainder hremainder
      hremainder_meas).continuous_comp hg

/-- The literal finite hafnian is continuous in the product topology on its
matrix entries. -/
theorem continuous_hafnian (n : ℕ) :
    Continuous
      (hafnian : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ → ℂ) := by
  rw [show (hafnian : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ → ℂ) =
      typeHafnian by
    funext A
    exact (typeHafnian_fin_eq_hafnian A).symm]
  exact continuous_typeHafnian

/-- Hafnian specialization for any normed finite-dimensional matrix model.
The map `toMatrix` makes the choice of matrix norm/coordinates explicit;
Mathlib intentionally does not choose a global norm on raw `Matrix`. -/
theorem independentAdditiveShiftHafnian_tendstoInDistribution_of_weakLimit
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    [SeminormedAddCommGroup E] [SecondCountableTopology E] [BorelSpace E]
    (n : ℕ) (toMatrix : E → Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (htoMatrix : Continuous toMatrix)
    (base : ProbabilityMeasure Omega)
    (shift limitLaw : ProbabilityMeasure E)
    (X : ℕ → Omega → E) (hX : ∀ m, Measurable (X m))
    (hweak : Tendsto
      (fun m ↦ base.map (hX m).aemeasurable)
      atTop (nhds limitLaw))
    (remainder : ℕ → Omega × E → E)
    (hremainder : TendstoInMeasure
      ((base.prod shift : ProbabilityMeasure (Omega × E)) : Measure (Omega × E))
      remainder atTop 0)
    (hremainder_meas : ∀ m, AEMeasurable (remainder m)
      ((base.prod shift : ProbabilityMeasure (Omega × E)) : Measure (Omega × E))) :
    TendstoInDistribution
      (fun m p ↦ hafnian
        (toMatrix (X m p.1 + p.2 + remainder m p))) atTop
      (fun p : E × E ↦ hafnian (toMatrix (p.1 + p.2)))
      (fun _ ↦ ((base.prod shift : ProbabilityMeasure (Omega × E)) :
        Measure (Omega × E)))
      ((limitLaw.prod shift : ProbabilityMeasure (E × E)) :
        Measure (E × E)) := by
  exact independentAdditiveShift_continuousMap_tendstoInDistribution_of_weakLimit
    base shift limitLaw X hX hweak remainder hremainder hremainder_meas
      (fun A ↦ hafnian (toMatrix A)) ((continuous_hafnian n).comp htoMatrix)

/-- Multiplication of any fixed finite-dimensional random vector by `m⁻¹`
converges to zero in probability.  No integrability or moment bound is used. -/
theorem tendstoInMeasure_inv_nat_smul
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (mu : ProbabilityMeasure Omega) (C : Omega → E)
    (hC : AEStronglyMeasurable C (mu : Measure Omega)) :
    TendstoInMeasure (mu : Measure Omega)
      (fun m : ℕ ↦ fun omega ↦ (m : ℂ)⁻¹ • C omega) atTop 0 := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro m
    exact hC.const_smul _
  · filter_upwards [] with omega
    simpa using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).smul_const (C omega)

/-- Product-space form for a cross term.  The second probability measure is
an arbitrary independent law, and neither law is assumed to have moments. -/
theorem independentCrossTerm_tendstoInMeasure_noMoments
    {Omega Delta E : Type*} [MeasurableSpace Omega]
    [MeasurableSpace Delta] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (base : ProbabilityMeasure Omega) (shift : ProbabilityMeasure Delta)
    (cross : Omega × Delta → E)
    (hcross : AEStronglyMeasurable cross
      ((base.prod shift : ProbabilityMeasure (Omega × Delta)) :
        Measure (Omega × Delta))) :
    TendstoInMeasure
      ((base.prod shift : ProbabilityMeasure
        (Omega × Delta)) : Measure (Omega × Delta))
      (fun m : ℕ ↦ fun p ↦ (m : ℂ)⁻¹ • cross p)
      atTop 0 := by
  apply tendstoInMeasure_inv_nat_smul (base.prod shift)
  exact hcross

/-- Direct shifted-hafnian endpoint for a fixed finite-dimensional cross
term.  Measurability is the only hypothesis on the cross term: the factor
`m⁻¹` forces it to zero in probability under the product law, with no
integrability or moment assumption on the independent shift. -/
theorem
    independentAdditiveShiftHafnian_fixedCross_noMoments_tendstoInDistribution_of_weakLimit
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SecondCountableTopology E] [BorelSpace E]
    (n : ℕ) (toMatrix : E → Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (htoMatrix : Continuous toMatrix)
    (base : ProbabilityMeasure Omega)
    (shift limitLaw : ProbabilityMeasure E)
    (X : ℕ → Omega → E) (hX : ∀ m, Measurable (X m))
    (hweak : Tendsto
      (fun m ↦ base.map (hX m).aemeasurable)
      atTop (nhds limitLaw))
    (cross : Omega × E → E)
    (hcross : AEStronglyMeasurable cross
      ((base.prod shift : ProbabilityMeasure (Omega × E)) :
        Measure (Omega × E))) :
    TendstoInDistribution
      (fun m p ↦ hafnian
        (toMatrix (X m p.1 + p.2 + (m : ℂ)⁻¹ • cross p))) atTop
      (fun p : E × E ↦ hafnian (toMatrix (p.1 + p.2)))
      (fun _ ↦ ((base.prod shift : ProbabilityMeasure (Omega × E)) :
        Measure (Omega × E)))
      ((limitLaw.prod shift : ProbabilityMeasure (E × E)) :
        Measure (E × E)) := by
  apply independentAdditiveShiftHafnian_tendstoInDistribution_of_weakLimit
    n toMatrix htoMatrix base shift limitLaw X hX hweak
      (fun m p ↦ (m : ℂ)⁻¹ • cross p)
  · exact independentCrossTerm_tendstoInMeasure_noMoments base shift cross hcross
  · intro m
    exact (hcross.const_smul _).aemeasurable

end

end LogdetLean.GramHafnian.SymmetricGaussianLimit

import LogdetLean.GramHafnian.UltimateHiding.Dense.CentralOneColumnCommutation
import LogdetLean.GramHafnian.UltimateHiding.Dense.RadialGelfandExternal
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.ConcreteCorrelatedPath
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Propagating a square-COE one-column estimate through the radial chain

This module contains the measure-theoretic bridge that lets the dense score
calculation be carried out only at the square scaled-COE corner law.  It proves
internally that:

* the eventwise probability total-variation convention contracts under every
  Markov kernel;
* the central part of a same-beta one-column factor commutes globally with
  every earlier one-column kernel;
* the orbital part commutes at the actual Haar laws by the separately audited
  fixed-radius Gelfand-pair theorem;
* after retaining the common beta sample, the entire next one-column update
  commutes through the preceding radial chain at the square Haar base.

No new external atom is introduced here.
-/

open scoped ENNReal
open Filter MeasureTheory ProbabilityTheory Set

namespace LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding

set_option maxHeartbeats 1200000

/-! ## Markov-kernel data processing for eventwise probability TV -/

/-- A Markov kernel cannot increase the paper's eventwise probability total
variation.  The proof extends the event bound from indicators to the
`[0,1]`-valued function `x \mapsto k x A` by the layer-cake formula. -/
theorem probabilityTVLE_kernel_comp
    {Source Target : Type*}
    [MeasurableSpace Source] [MeasurableSpace Target]
    (mu nu : Measure Source) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu]
    (k : Kernel Source Target) [IsMarkovKernel k]
    {delta : ℝ} (h : Dense.ProbabilityTVLE mu nu delta) :
    Dense.ProbabilityTVLE (k ∘ₘ mu) (k ∘ₘ nu) delta := by
  refine ⟨h.1, ?_⟩
  intro A hA
  let f : Source → ℝ := fun x ↦ (k x).real A
  have hf_meas : Measurable f := by
    exact (Kernel.measurable_coe k hA).ennreal_toReal
  have hf_nonneg : ∀ x, 0 ≤ f x := fun x ↦ measureReal_nonneg
  have hf_le_one : ∀ x, f x ≤ 1 := by
    intro x
    let _ : IsProbabilityMeasure (k x) := by infer_instance
    exact measureReal_le_one
  have hf_int_mu : Integrable f mu := by
    apply (integrable_const (1 : ℝ)).mono hf_meas.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg x), norm_one]
    exact hf_le_one x
  have hf_int_nu : Integrable f nu := by
    apply (integrable_const (1 : ℝ)).mono hf_meas.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg x), norm_one]
    exact hf_le_one x
  have htail_meas (xi : Measure Source) : Measurable fun t : ℝ ↦
      xi.real {x : Source | t ≤ f x} := by
    apply Measurable.ennreal_toReal
    exact Antitone.measurable fun _ _ hst ↦
      measure_mono (fun _ hx ↦ hst.trans hx)
  have htail_int (xi : Measure Source) [IsProbabilityMeasure xi] :
      Integrable (fun t : ℝ ↦ xi.real {x : Source | t ≤ f x})
        (volume.restrict (Ioc (0 : ℝ) 1)) := by
    apply (integrable_const (1 : ℝ)).mono
      (htail_meas xi).aestronglyMeasurable.restrict
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg, norm_one]
    exact measureReal_le_one
  have hmu_layer : (∫ x, f x ∂mu) =
      ∫ t in Ioc (0 : ℝ) 1, mu.real {x : Source | t ≤ f x} :=
    hf_int_mu.integral_eq_integral_Ioc_meas_le
      (Eventually.of_forall hf_nonneg) (Eventually.of_forall hf_le_one)
  have hnu_layer : (∫ x, f x ∂nu) =
      ∫ t in Ioc (0 : ℝ) 1, nu.real {x : Source | t ≤ f x} :=
    hf_int_nu.integral_eq_integral_Ioc_meas_le
      (Eventually.of_forall hf_nonneg) (Eventually.of_forall hf_le_one)
  have hdiff_int : Integrable (fun t : ℝ ↦
      mu.real {x : Source | t ≤ f x} -
        nu.real {x : Source | t ≤ f x})
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (htail_int mu).sub (htail_int nu)
  have habs_int : Integrable (fun t : ℝ ↦
      |mu.real {x : Source | t ≤ f x} -
        nu.real {x : Source | t ≤ f x}|)
      (volume.restrict (Ioc (0 : ℝ) 1)) := hdiff_int.abs
  have hpoint : ∀ t : ℝ,
      |mu.real {x : Source | t ≤ f x} -
        nu.real {x : Source | t ≤ f x}| ≤ delta := by
    intro t
    exact h.2 _ (measurableSet_le measurable_const hf_meas)
  rw [← integral_kernel_measureReal_eq_comp_measureReal mu k A hA,
    ← integral_kernel_measureReal_eq_comp_measureReal nu k A hA,
    hmu_layer, hnu_layer, ← integral_sub (htail_int mu) (htail_int nu)]
  calc
    |∫ t in Ioc (0 : ℝ) 1,
        (mu.real {x : Source | t ≤ f x} -
          nu.real {x : Source | t ≤ f x})| ≤
        ∫ t in Ioc (0 : ℝ) 1,
          |mu.real {x : Source | t ≤ f x} -
            nu.real {x : Source | t ≤ f x}| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _t in Ioc (0 : ℝ) 1, delta := by
      apply integral_mono_ae habs_int (integrable_const delta)
      filter_upwards [] with t
      exact hpoint t
    _ = delta := by simp

/-! ## Central and fixed-beta radial commutation -/

/-- The internally proved central/one-column commutation propagates through
every finite concrete radial chain. -/
theorem concreteCentralKernel_radialChain_commute
    {N K : ℕ} (hN : 1 ≤ N) (hNK : N ≤ K) (s : ℝ) : ∀ r,
    Dense.KernelsCommute (Dense.concreteCentralMatrixKernel N s)
      (Dense.concreteRadialKernelChain N K r) := by
  intro r
  induction r with
  | zero =>
      unfold Dense.KernelsCommute
      simp
  | succ r ihr =>
      have hstep := Dense.concreteCentralKernel_oneColumn_commute
        (m := K + r) hN (by omega : N ≤ K + r) s
      unfold Dense.KernelsCommute at hstep ihr ⊢
      rw [Dense.concreteRadialKernelChain_succ]
      calc
        Dense.concreteCentralMatrixKernel N s ∘ₖ
              (Dense.concreteOneColumnMatrixKernel (K + r) N ∘ₖ
                Dense.concreteRadialKernelChain N K r) =
            (Dense.concreteCentralMatrixKernel N s ∘ₖ
                Dense.concreteOneColumnMatrixKernel (K + r) N) ∘ₖ
              Dense.concreteRadialKernelChain N K r :=
          (Kernel.comp_assoc _ _ _).symm
        _ = (Dense.concreteOneColumnMatrixKernel (K + r) N ∘ₖ
                Dense.concreteCentralMatrixKernel N s) ∘ₖ
              Dense.concreteRadialKernelChain N K r := by rw [hstep]
        _ = Dense.concreteOneColumnMatrixKernel (K + r) N ∘ₖ
              (Dense.concreteCentralMatrixKernel N s ∘ₖ
                Dense.concreteRadialKernelChain N K r) :=
          Kernel.comp_assoc _ _ _
        _ = Dense.concreteOneColumnMatrixKernel (K + r) N ∘ₖ
              (Dense.concreteRadialKernelChain N K r ∘ₖ
                Dense.concreteCentralMatrixKernel N s) := by rw [ihr]
        _ = (Dense.concreteOneColumnMatrixKernel (K + r) N ∘ₖ
                Dense.concreteRadialKernelChain N K r) ∘ₖ
              Dense.concreteCentralMatrixKernel N s :=
          (Kernel.comp_assoc _ _ _).symm

/-- A fixed-beta same-beta path action is exactly a central deterministic
kernel after the fixed-radius orbital kernel. -/
theorem concreteSharedBetaPathAction_eq_central_orbital
    {m N : ℕ} (hN : 1 ≤ N)
    (mu : Measure (Dense.ConcreteMatrixState N)) [IsProbabilityMeasure mu]
    (q s : ℝ) :
    concreteSharedBetaPathAction m N mu q s =
      Dense.concreteCentralMatrixKernel N
          (Dense.oneColumnCenteredScalarLog m N q) ∘ₘ
        (Dense.concreteOrbitalMatrixKernel N s ∘ₘ mu) := by
  let _ : IsProbabilityMeasure
      (Dense.complexUnitSphereProbabilityMeasure N) :=
    Dense.complexUnitSphereProbabilityMeasure_isProbability hN
  have horbital :
      Dense.concreteOrbitalMatrixKernel N s ∘ₘ mu =
        (mu.prod (Dense.complexUnitSphereProbabilityMeasure N)).map
          (fun Xv ↦ Dense.concreteOrbitalMatrixUpdate N s Xv.2 Xv.1) := by
    unfold Dense.concreteOrbitalMatrixKernel
    exact independentUpdateKernel_comp_eq_map_prod
      mu (Dense.complexUnitSphereProbabilityMeasure N)
      (fun Xv ↦ Dense.concreteOrbitalMatrixUpdate N s Xv.2 Xv.1)
      (Dense.measurable_concreteOrbitalMatrixUpdate N s)
  rw [horbital]
  unfold Dense.concreteCentralMatrixKernel
  rw [Measure.deterministic_comp_eq_map]
  rw [Measure.map_map
    (Dense.measurable_concreteCentralMatrixUpdate N _)
    (Dense.measurable_concreteOrbitalMatrixUpdate N s)]
  rfl

/-- Fixed-beta propagation from the square scaled-COE law to an arbitrary
ambient Haar law.  The orbital equality is the fixed-radius invariant-law
Gelfand theorem; the central equality is the global kernel commutation proved
above. -/
theorem concreteSharedBetaPathAction_radialPropagation
    (H : CurrentPRL.UnitaryHaarProbabilityFamily)
    {N K ambient step : ℕ} (q s : ℝ)
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKambient : K ≤ ambient) :
    concreteSharedBetaPathAction step N
        (Dense.concreteHaarAmbientLaw H N K ambient) q s =
      Dense.radialConvolution
        (Dense.concreteRadialKernelChain N K (ambient - K))
        (concreteSharedBetaPathAction step N
          (Dense.concreteScaledCOECornerLaw H N K) q s) := by
  let base := Dense.concreteScaledCOECornerLaw H N K
  let radial := Dense.concreteRadialKernelChain N K (ambient - K)
  let _ : IsProbabilityMeasure base :=
    concreteScaledCOECornerLaw_isProbability H hNK
  let _ : IsMarkovKernel radial :=
    Dense.concreteRadialKernelChain_isMarkov hN hNK (ambient - K)
  let _ : IsProbabilityMeasure (Dense.radialConvolution radial base) :=
    Dense.radialConvolution_isProbability radial base
      (Dense.concreteRadialKernelChain_isMarkov hN hNK (ambient - K))
      (concreteScaledCOECornerLaw_isProbability H hNK)
  have hfactor := Dense.concreteHaarAmbientLaw_radialFactorization_fromCOE
    H hN hNK hKambient
  let _ : IsProbabilityMeasure
      (Dense.concreteHaarAmbientLaw H N K ambient) := by
    rw [hfactor]
    exact Dense.radialConvolution_isProbability radial base
      (Dense.concreteRadialKernelChain_isMarkov hN hNK (ambient - K))
      (concreteScaledCOECornerLaw_isProbability H hNK)
  have horbital := Dense.concreteScaledCOE_radial_orbital_commutation
    H s hN hNK hKambient
  have hcentral := concreteCentralKernel_radialChain_commute hN hNK
    (Dense.oneColumnCenteredScalarLog step N q) (ambient - K)
  rw [hfactor,
    concreteSharedBetaPathAction_eq_central_orbital hN,
    concreteSharedBetaPathAction_eq_central_orbital hN]
  unfold Dense.radialConvolution at horbital ⊢
  unfold Dense.orbitalConvolution at horbital
  rw [horbital]
  exact hcentral.measure_actions
    (Dense.concreteOrbitalMatrixKernel N s ∘ₘ base)

/-! ## The full same-beta kernel as a beta mixture -/

/-- The central--orbital split evaluated at the literal, untruncated beta
amplitude. -/
def concreteSharedBetaSplitUpdate (m N : ℕ) :
    (ℝ × (Dense.ConcreteMatrixState N × Dense.ComplexUnitSphere N)) →
      Dense.ConcreteMatrixState N :=
  concreteSharedBetaPathUpdateJoint m N ∘
    (fun qXv ↦
      ((qXv.1, Dense.oneColumnRankOneLog qXv.1), qXv.2))

theorem measurable_concreteSharedBetaSplitUpdate (m N : ℕ) :
    Measurable (concreteSharedBetaSplitUpdate m N) := by
  have hb : Measurable (Dense.oneColumnRankOneLog : ℝ → ℝ) := by
    unfold Dense.oneColumnRankOneLog
    fun_prop
  have hembed : Measurable fun qXv :
      ℝ × (Dense.ConcreteMatrixState N × Dense.ComplexUnitSphere N) ↦
        ((qXv.1, Dense.oneColumnRankOneLog qXv.1), qXv.2) :=
    (measurable_fst.prodMk (hb.comp measurable_fst)).prodMk measurable_snd
  exact (measurable_concreteSharedBetaPathUpdate_joint m N).comp hembed

/-- Conditional on `q`, this kernel is exactly the fixed-beta same-beta path
action.  Composing it with the beta law gives the full one-column kernel. -/
def concreteSharedBetaSplitKernel (m N : ℕ)
    (mu : Measure (Dense.ConcreteMatrixState N)) :
    Kernel ℝ (Dense.ConcreteMatrixState N) :=
  (((Kernel.id : Kernel ℝ ℝ) ×ₖ
      Kernel.const ℝ
        (mu.prod (Dense.complexUnitSphereProbabilityMeasure N))).map
    (concreteSharedBetaSplitUpdate m N))

theorem concreteSharedBetaSplitKernel_isMarkov
    {m N : ℕ} (hN : 1 ≤ N)
    (mu : Measure (Dense.ConcreteMatrixState N)) [IsProbabilityMeasure mu] :
    IsMarkovKernel (concreteSharedBetaSplitKernel m N mu) := by
  let _ : IsProbabilityMeasure
      (Dense.complexUnitSphereProbabilityMeasure N) :=
    Dense.complexUnitSphereProbabilityMeasure_isProbability hN
  let inner := mu.prod (Dense.complexUnitSphereProbabilityMeasure N)
  let _ : IsProbabilityMeasure inner := by
    dsimp [inner]
    infer_instance
  unfold concreteSharedBetaSplitKernel
  exact Kernel.IsMarkovKernel.map _
    (measurable_concreteSharedBetaSplitUpdate m N)

theorem concreteSharedBetaSplitKernel_apply
    {m N : ℕ} (hN : 1 ≤ N)
    (mu : Measure (Dense.ConcreteMatrixState N)) [IsProbabilityMeasure mu]
    (q : ℝ) :
    concreteSharedBetaSplitKernel m N mu q =
      concreteSharedBetaPathAction m N mu q
        (Dense.oneColumnRankOneLog q) := by
  let _ : IsProbabilityMeasure
      (Dense.complexUnitSphereProbabilityMeasure N) :=
    Dense.complexUnitSphereProbabilityMeasure_isProbability hN
  unfold concreteSharedBetaSplitKernel concreteSharedBetaPathAction
  rw [Kernel.map_apply _ (measurable_concreteSharedBetaSplitUpdate m N),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    Measure.dirac_prod]
  rw [Measure.map_map (measurable_concreteSharedBetaSplitUpdate m N)
    measurable_prodMk_left]
  rfl

/-- The beta mixture of the split conditional kernel is literally the full
one-column law.  Equality with the central--orbital formula is needed only on
the open beta support, whose complement is null. -/
theorem concreteSharedBetaSplitKernel_comp_beta_eq_fullLaw
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m)
    (mu : Measure (Dense.ConcreteMatrixState N)) [IsProbabilityMeasure mu] :
    concreteSharedBetaSplitKernel m N mu ∘ₘ
        Dense.oneColumnBetaLaw m N =
      concreteSharedBetaFullLaw m N mu := by
  let _ : IsProbabilityMeasure (Dense.oneColumnBetaLaw m N) :=
    Dense.oneColumnBetaLaw_isProbability hN hNm
  let _ : IsProbabilityMeasure
      (Dense.complexUnitSphereProbabilityMeasure N) :=
    Dense.complexUnitSphereProbabilityMeasure_isProbability hN
  let inner := mu.prod (Dense.complexUnitSphereProbabilityMeasure N)
  let _ : IsProbabilityMeasure inner := by
    dsimp [inner]
    infer_instance
  have hprod := independentUpdateKernel_comp_eq_map_prod
    (Dense.oneColumnBetaLaw m N) inner
    (concreteSharedBetaSplitUpdate m N)
    (measurable_concreteSharedBetaSplitUpdate m N)
  have hmix : concreteSharedBetaSplitKernel m N mu ∘ₘ
        Dense.oneColumnBetaLaw m N =
      ((Dense.oneColumnBetaLaw m N).prod inner).map
        (concreteSharedBetaSplitUpdate m N) := by
    simpa [concreteSharedBetaSplitKernel] using hprod
  rw [hmix]
  unfold concreteSharedBetaFullLaw concreteSharedBetaSourceLaw
  change ((Dense.oneColumnBetaLaw m N).prod inner).map
      (concreteSharedBetaSplitUpdate m N) =
    ((Dense.oneColumnBetaLaw m N).prod inner).map
      (concreteSharedBetaFullUpdate m N)
  apply Measure.map_congr
  have hq : ∀ᵐ q ∂(Dense.oneColumnBetaLaw m N), q ∈ Ioo (0 : ℝ) 1 := by
    rw [ae_iff]
    exact Dense.oneColumnBetaLaw_compl_Ioo_eq_zero m N
  have hset : MeasurableSet
      {qXv : ℝ × (Dense.ConcreteMatrixState N × Dense.ComplexUnitSphere N) |
        qXv.1 ∈ Ioo (0 : ℝ) 1} :=
    measurableSet_Ioo.preimage measurable_fst
  have hsupport : ∀ᵐ qXv ∂((Dense.oneColumnBetaLaw m N).prod inner),
      qXv.1 ∈ Ioo (0 : ℝ) 1 := by
    apply (Measure.ae_prod_iff_ae_ae hset).2
    filter_upwards [hq] with q hqmem
    filter_upwards [] with Xv
    exact hqmem
  filter_upwards [hsupport] with qXv hqXv
  unfold concreteSharedBetaSplitUpdate concreteSharedBetaFullUpdate
    concreteSharedBetaFullEmbedding
  simp only [Function.comp_apply]
  exact (Dense.concreteOneColumnMatrixUpdate_eq_central_orbital
    (hN.trans hNm) hN hqXv.1 qXv.2.2 qXv.2.1).symm

/-! ## Whole-one-column radial commutation -/

/-- The conditional same-beta kernel at the ambient Haar law is the radial
chain composed with its square-COE conditional kernel. -/
theorem concreteSharedBetaSplitKernel_radialPropagation
    (H : CurrentPRL.UnitaryHaarProbabilityFamily)
    {N K ambient step : ℕ}
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKambient : K ≤ ambient) :
    concreteSharedBetaSplitKernel step N
        (Dense.concreteHaarAmbientLaw H N K ambient) =
      Dense.concreteRadialKernelChain N K (ambient - K) ∘ₖ
        concreteSharedBetaSplitKernel step N
          (Dense.concreteScaledCOECornerLaw H N K) := by
  let base := Dense.concreteScaledCOECornerLaw H N K
  let radial := Dense.concreteRadialKernelChain N K (ambient - K)
  let _ : IsProbabilityMeasure base :=
    concreteScaledCOECornerLaw_isProbability H hNK
  let _ : IsMarkovKernel radial :=
    Dense.concreteRadialKernelChain_isMarkov hN hNK (ambient - K)
  have hfactor := Dense.concreteHaarAmbientLaw_radialFactorization_fromCOE
    H hN hNK hKambient
  let _ : IsProbabilityMeasure
      (Dense.concreteHaarAmbientLaw H N K ambient) := by
    rw [hfactor]
    exact Dense.radialConvolution_isProbability radial base
      (Dense.concreteRadialKernelChain_isMarkov hN hNK (ambient - K))
      (concreteScaledCOECornerLaw_isProbability H hNK)
  ext q : 1
  rw [concreteSharedBetaSplitKernel_apply hN,
    Kernel.comp_apply,
    concreteSharedBetaSplitKernel_apply hN]
  exact concreteSharedBetaPathAction_radialPropagation
    H q (Dense.oneColumnRankOneLog q) hN hNK hKambient

/-- The full next one-column law commutes through the entire preceding radial
chain at the square scaled-COE base.  The beta sample remains shared between
the central and orbital factors throughout the proof. -/
theorem concreteSharedBetaFullLaw_radialPropagation
    (H : CurrentPRL.UnitaryHaarProbabilityFamily)
    {N K ambient step : ℕ}
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKambient : K ≤ ambient)
    (hNstep : N ≤ step) :
    concreteSharedBetaFullLaw step N
        (Dense.concreteHaarAmbientLaw H N K ambient) =
      Dense.radialConvolution
        (Dense.concreteRadialKernelChain N K (ambient - K))
        (concreteSharedBetaFullLaw step N
          (Dense.concreteScaledCOECornerLaw H N K)) := by
  let base := Dense.concreteScaledCOECornerLaw H N K
  let ambientLaw := Dense.concreteHaarAmbientLaw H N K ambient
  let radial := Dense.concreteRadialKernelChain N K (ambient - K)
  let _ : IsProbabilityMeasure base :=
    concreteScaledCOECornerLaw_isProbability H hNK
  let _ : IsMarkovKernel radial :=
    Dense.concreteRadialKernelChain_isMarkov hN hNK (ambient - K)
  have hfactor := Dense.concreteHaarAmbientLaw_radialFactorization_fromCOE
    H hN hNK hKambient
  let _ : IsProbabilityMeasure ambientLaw := by
    dsimp [ambientLaw]
    rw [hfactor]
    exact Dense.radialConvolution_isProbability radial base
      (Dense.concreteRadialKernelChain_isMarkov hN hNK (ambient - K))
      (concreteScaledCOECornerLaw_isProbability H hNK)
  let _ : IsProbabilityMeasure (Dense.oneColumnBetaLaw step N) :=
    Dense.oneColumnBetaLaw_isProbability hN hNstep
  let _ : IsMarkovKernel
      (concreteSharedBetaSplitKernel step N base) :=
    concreteSharedBetaSplitKernel_isMarkov hN base
  let _ : IsMarkovKernel
      (concreteSharedBetaSplitKernel step N ambientLaw) :=
    concreteSharedBetaSplitKernel_isMarkov hN ambientLaw
  rw [← concreteSharedBetaSplitKernel_comp_beta_eq_fullLaw
      hN hNstep ambientLaw,
    ← concreteSharedBetaSplitKernel_comp_beta_eq_fullLaw
      hN hNstep base,
    concreteSharedBetaSplitKernel_radialPropagation H hN hNK hKambient]
  unfold Dense.radialConvolution
  exact (Measure.comp_assoc
    (μ := Dense.oneColumnBetaLaw step N)
    (κ := concreteSharedBetaSplitKernel step N base)
    (η := radial)).symm

/-- Paper-facing commutation statement: applying the next concrete
one-column kernel to the actual ambient Haar law is the preceding radial chain
applied to the same next-column update at the square scaled-COE base. -/
theorem concreteOneColumn_radial_commutation_at_scaledCOE
    (H : CurrentPRL.UnitaryHaarProbabilityFamily)
    {N K ambient step : ℕ}
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKambient : K ≤ ambient)
    (hNstep : N ≤ step) :
    Dense.concreteOneColumnMatrixKernel step N ∘ₘ
        Dense.concreteHaarAmbientLaw H N K ambient =
      Dense.radialConvolution
        (Dense.concreteRadialKernelChain N K (ambient - K))
        (Dense.concreteOneColumnMatrixKernel step N ∘ₘ
          Dense.concreteScaledCOECornerLaw H N K) := by
  let base := Dense.concreteScaledCOECornerLaw H N K
  let ambientLaw := Dense.concreteHaarAmbientLaw H N K ambient
  let _ : IsProbabilityMeasure base :=
    concreteScaledCOECornerLaw_isProbability H hNK
  have hfactor := Dense.concreteHaarAmbientLaw_radialFactorization_fromCOE
    H hN hNK hKambient
  let _ : IsProbabilityMeasure ambientLaw := by
    dsimp [ambientLaw]
    rw [hfactor]
    exact Dense.radialConvolution_isProbability
      (Dense.concreteRadialKernelChain N K (ambient - K)) base
      (Dense.concreteRadialKernelChain_isMarkov hN hNK (ambient - K))
      (concreteScaledCOECornerLaw_isProbability H hNK)
  rw [← concreteSharedBetaFullLaw_eq_oneColumnKernel hN hNstep ambientLaw,
    ← concreteSharedBetaFullLaw_eq_oneColumnKernel hN hNstep base]
  exact concreteSharedBetaFullLaw_radialPropagation
    H hN hNK hKambient hNstep

/-- A one-column TV estimate proved only at the square scaled-COE base
propagates, with the same constant, to the actual ambient Haar law. -/
theorem probabilityTVLE_concreteHaarAmbient_oneColumn_of_scaledCOE
    (H : CurrentPRL.UnitaryHaarProbabilityFamily)
    {N K ambient step : ℕ}
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKambient : K ≤ ambient)
    (hNstep : N ≤ step) {delta : ℝ}
    (hbase : Dense.ProbabilityTVLE
      (Dense.concreteScaledCOECornerLaw H N K)
      (Dense.concreteOneColumnMatrixKernel step N ∘ₘ
        Dense.concreteScaledCOECornerLaw H N K)
      delta) :
    Dense.ProbabilityTVLE
      (Dense.concreteHaarAmbientLaw H N K ambient)
      (Dense.concreteOneColumnMatrixKernel step N ∘ₘ
        Dense.concreteHaarAmbientLaw H N K ambient)
      delta := by
  let base := Dense.concreteScaledCOECornerLaw H N K
  let radial := Dense.concreteRadialKernelChain N K (ambient - K)
  let baseStep := Dense.concreteOneColumnMatrixKernel step N ∘ₘ base
  let _ : IsProbabilityMeasure base :=
    concreteScaledCOECornerLaw_isProbability H hNK
  let _ : IsMarkovKernel (Dense.concreteOneColumnMatrixKernel step N) :=
    Dense.concreteOneColumnMatrixKernel_isMarkov hN hNstep
  let _ : IsProbabilityMeasure baseStep := by
    dsimp [baseStep]
    infer_instance
  let _ : IsMarkovKernel radial :=
    Dense.concreteRadialKernelChain_isMarkov hN hNK (ambient - K)
  have hcontract := probabilityTVLE_kernel_comp base baseStep radial hbase
  have hfactor := Dense.concreteHaarAmbientLaw_radialFactorization_fromCOE
    H hN hNK hKambient
  have hcommute := concreteOneColumn_radial_commutation_at_scaledCOE
    H hN hNK hKambient hNstep
  dsimp [base, baseStep, radial] at hcontract
  unfold Dense.radialConvolution at hfactor hcommute
  rw [← hfactor, ← hcommute] at hcontract
  exact hcontract

end

end LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

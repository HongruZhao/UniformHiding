import LogdetLean.GramHafnian.UltimateHiding.Dense.OneColumnFactorSplit
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.CorrelatedOneStepBridge
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

/-!
# Concrete same-beta event paths

This file constructs the scalar and orbital event paths used in the dense
one-column argument.  The central coefficient and the orbital coefficient
are evaluated at the same beta sample.  All endpoint and good/bad coupling
identities are measure-theoretic consequences of the concrete matrix update;
the only hypotheses left to a later score theorem concern differentiability
and derivative bounds of the resulting paths.
-/

open scoped ENNReal
open scoped symmDiff
open MeasureTheory ProbabilityTheory Set

namespace LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

noncomputable section

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 800000

open LogdetLean.GramHafnian.UltimateHiding

/-! ## Elementary real-mixture and coupling lemmas -/

/-- Taking real values commutes with a probability-kernel mixture on a
measurable event. -/
theorem integral_kernel_measureReal_eq_comp_measureReal
    {Param State : Type*} [MeasurableSpace Param] [MeasurableSpace State]
    (param : Measure Param) (k : Kernel Param State)
    [IsProbabilityMeasure param] [IsMarkovKernel k]
    (A : Set State) (hA : MeasurableSet A) :
    (∫ p, (k p).real A ∂param) = (k ∘ₘ param).real A := by
  rw [measureReal_def, Measure.bind_apply hA k.aemeasurable]
  exact integral_toReal (Kernel.measurable_coe k hA).aemeasurable
    (ae_of_all _ fun p ↦ (measure_lt_top (k p) A))

/-- Two measurable images of the same finite source differ in eventwise total
variation by at most the source mass on a set outside which the maps agree. -/
theorem probabilityTVLE_map_map_of_eq_off
    {Source State : Type*} [MeasurableSpace Source] [MeasurableSpace State]
    (xi : Measure Source) [IsFiniteMeasure xi]
    (f g : Source → State) (hf : Measurable f) (hg : Measurable g)
    (bad : Set Source) (hbad : MeasurableSet bad)
    (heq : ∀ x, x ∉ bad → f x = g x) :
    Dense.ProbabilityTVLE (xi.map f) (xi.map g) (xi.real bad) := by
  refine ⟨measureReal_nonneg, ?_⟩
  intro A hA
  rw [map_measureReal_apply hf hA, map_measureReal_apply hg hA]
  calc
    |xi.real (f ⁻¹' A) - xi.real (g ⁻¹' A)| ≤
        xi.real ((f ⁻¹' A) ∆ (g ⁻¹' A)) :=
      abs_measureReal_sub_le_measureReal_symmDiff
        (hf hA).nullMeasurableSet (hg hA).nullMeasurableSet
    _ ≤ xi.real bad := by
      apply measureReal_mono (h₂ := by finiteness)
      intro x hx
      by_contra hxbad
      have hfg := heq x hxbad
      simpa [symmDiff_def, hfg] using hx

/-- Fubini in the real-valued event convention used by `ProbabilityTVLE`. -/
theorem integral_map_sections_measureReal_eq_map_prod_measureReal
    {Param Inner State : Type*}
    [MeasurableSpace Param] [MeasurableSpace Inner] [MeasurableSpace State]
    (param : Measure Param) (inner : Measure Inner)
    [IsProbabilityMeasure param] [IsProbabilityMeasure inner]
    (F : Param × Inner → State) (hF : Measurable F)
    (A : Set State) (hA : MeasurableSet A) :
    (∫ p, (inner.map (fun x ↦ F (p, x))).real A ∂param) =
      ((param.prod inner).map F).real A := by
  have hsec (p : Param) : Measurable fun x : Inner ↦ F (p, x) :=
    hF.comp measurable_prodMk_left
  rw [map_measureReal_apply hF hA, measureReal_def,
    Measure.prod_apply (hF hA)]
  rw [← integral_toReal
    (measurable_measure_prodMk_left (hF hA)).aemeasurable
    (ae_of_all _ fun p ↦ measure_lt_top inner _)]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [map_measureReal_apply (hsec p) hA]
  rfl

/-- The section probabilities in the preceding Fubini identity are
integrable. -/
theorem integrable_map_sections_measureReal
    {Param Inner State : Type*}
    [MeasurableSpace Param] [MeasurableSpace Inner] [MeasurableSpace State]
    (param : Measure Param) (inner : Measure Inner)
    [IsProbabilityMeasure param] [IsProbabilityMeasure inner]
    (F : Param × Inner → State) (hF : Measurable F)
    (A : Set State) (hA : MeasurableSet A) :
    Integrable (fun p ↦ (inner.map (fun x ↦ F (p, x))).real A) param := by
  have hsec (p : Param) : Measurable fun x : Inner ↦ F (p, x) :=
    hF.comp measurable_prodMk_left
  have hmeas : Measurable
      (fun p ↦ (inner.map (fun x ↦ F (p, x))).real A) := by
    have h := (measurable_measure_prodMk_left
      (ν := inner) (hF hA)).ennreal_toReal
    simp only [measureReal_def, Measure.map_apply (hsec _) hA]
    change Measurable fun p ↦
      (inner (Prod.mk p ⁻¹' (F ⁻¹' A))).toReal
    exact h
  apply (integrable_const (1 : ℝ)).mono hmeas.aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg, norm_one]
  letI : IsProbabilityMeasure (inner.map (fun x ↦ F (p, x))) :=
    Measure.isProbabilityMeasure_map (hsec p).aemeasurable
  have hle := measureReal_mono
    (μ := inner.map (fun x ↦ F (p, x))) (s₁ := A) (s₂ := Set.univ)
      (by intro x hx; exact mem_univ x) (by finiteness)
  simpa using hle

/-- Acting with `independentUpdateKernel` on a source law is exactly mapping
the product of the source and parameter laws. -/
theorem independentUpdateKernel_comp_eq_map_prod
    {State Param Out : Type*}
    [MeasurableSpace State] [MeasurableSpace Param] [MeasurableSpace Out]
    (mu : Measure State) (param : Measure Param)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure param]
    (update : State × Param → Out) (hupdate : Measurable update) :
    -- The output type is allowed to differ from the input type by spelling
    -- the same sampling construction directly as a kernel.
    (((Kernel.id : Kernel State State) ×ₖ Kernel.const State param).map update) ∘ₘ mu =
      (mu.prod param).map update := by
  ext A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _),
    Measure.map_apply hupdate hA, Measure.prod_apply (hupdate hA)]
  congr 1
  funext X
  rw [Kernel.map_apply _ hupdate, Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod]
  rw [Measure.map_map hupdate measurable_prodMk_left]
  rw [Measure.map_apply (hupdate.comp measurable_prodMk_left) hA]
  rfl

/-! ## Jointly measurable concrete updates -/

theorem measurable_concreteCentralMatrixUpdate_joint (N : ℕ) :
    Measurable fun p : ℝ × Dense.ConcreteMatrixState N ↦
      Dense.concreteCentralMatrixUpdate N p.1 p.2 := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [Dense.concreteCentralMatrixUpdate, Dense.concreteCentralFactor,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.one_apply]
  fun_prop

theorem measurable_concreteOrbitalMatrixUpdate_joint (N : ℕ) :
    Measurable fun p : ℝ ×
        (Dense.ConcreteMatrixState N × Dense.ComplexUnitSphere N) ↦
      Dense.concreteOrbitalMatrixUpdate N p.1 p.2.2 p.2.1 := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [Dense.concreteOrbitalMatrixUpdate, Dense.concreteOrbitalFactor,
    Dense.complexRankOneProjection, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply]
  fun_prop

def concreteCentralMatrixUpdateJointFn (N : ℕ) :
    (ℝ × Dense.ConcreteMatrixState N) → Dense.ConcreteMatrixState N :=
  fun p ↦ Dense.concreteCentralMatrixUpdate N p.1 p.2

theorem measurable_concreteCentralMatrixUpdateJointFn (N : ℕ) :
    Measurable (concreteCentralMatrixUpdateJointFn N) :=
  measurable_concreteCentralMatrixUpdate_joint N

def concreteOrbitalMatrixUpdateJointFn (N : ℕ) :
    (ℝ × (Dense.ConcreteMatrixState N × Dense.ComplexUnitSphere N)) →
      Dense.ConcreteMatrixState N :=
  fun p ↦ Dense.concreteOrbitalMatrixUpdate N p.1 p.2.2 p.2.1

theorem measurable_concreteOrbitalMatrixUpdateJointFn (N : ℕ) :
    Measurable (concreteOrbitalMatrixUpdateJointFn N) :=
  measurable_concreteOrbitalMatrixUpdate_joint N

theorem measurable_oneColumnCenteredScalarLog (m N : ℕ) :
    Measurable (Dense.oneColumnCenteredScalarLog m N) := by
  unfold Dense.oneColumnCenteredScalarLog Dense.oneColumnScalarLog
    Dense.oneColumnRankOneLog
  fun_prop

/-! ## Central action and scalar path -/

/-- Push a matrix law through scalar transpose congruence. -/
def concreteCentralAction (N : ℕ)
    (mu : Measure (Dense.ConcreteMatrixState N)) (s : ℝ) :
    Measure (Dense.ConcreteMatrixState N) :=
  mu.map (Dense.concreteCentralMatrixUpdate N s)

/-- Event path for a central move. -/
def concreteCentralEventPath (N : ℕ)
    (mu : Measure (Dense.ConcreteMatrixState N))
    (A : Set (Dense.ConcreteMatrixState N)) (s : ℝ) : ℝ :=
  (concreteCentralAction N mu s).real A

theorem concreteCentralEventPath_zero
    {N : ℕ} (mu : Measure (Dense.ConcreteMatrixState N))
    (A : Set (Dense.ConcreteMatrixState N)) (hA : MeasurableSet A) :
    concreteCentralEventPath N mu A 0 = mu.real A := by
  rw [concreteCentralEventPath, concreteCentralAction,
    map_measureReal_apply (Dense.measurable_concreteCentralMatrixUpdate N 0) hA]
  congr 1
  ext X i j
  simp [Dense.concreteCentralMatrixUpdate, Dense.concreteCentralFactor]

/-- The beta mixture of central moves. -/
def concreteCentralMixtureLaw (m N : ℕ)
    (mu : Measure (Dense.ConcreteMatrixState N)) :
    Measure (Dense.ConcreteMatrixState N) :=
  ((Dense.oneColumnBetaLaw m N).prod mu).map
    (fun qX ↦ Dense.concreteCentralMatrixUpdate N
      (Dense.oneColumnCenteredScalarLog m N qX.1) qX.2)

/-! ## Same-beta orbital path -/

/-- Central-after-orbital update.  The beta sample occurs only in the central
coefficient here; the path variable `s` will later be set to a function of the
same beta sample. -/
def concreteSharedBetaPathUpdate (m N : ℕ) (q s : ℝ)
    (Xv : Dense.ConcreteMatrixState N × Dense.ComplexUnitSphere N) :
    Dense.ConcreteMatrixState N :=
  Dense.concreteCentralMatrixUpdate N
    (Dense.oneColumnCenteredScalarLog m N q)
    (Dense.concreteOrbitalMatrixUpdate N s Xv.2 Xv.1)

theorem measurable_concreteSharedBetaPathUpdate
    (m N : ℕ) (q s : ℝ) :
    Measurable (concreteSharedBetaPathUpdate m N q s) := by
  exact (Dense.measurable_concreteCentralMatrixUpdate N _).comp
    (Dense.measurable_concreteOrbitalMatrixUpdate N s)

/-- The conditional law at a fixed beta sample `q` and orbital path time `s`. -/
def concreteSharedBetaPathAction (m N : ℕ)
    (mu : Measure (Dense.ConcreteMatrixState N)) (q s : ℝ) :
    Measure (Dense.ConcreteMatrixState N) :=
  (mu.prod (Dense.complexUnitSphereProbabilityMeasure N)).map
    (concreteSharedBetaPathUpdate m N q s)

/-- Correlation-safe orbital event path. -/
def concreteSharedBetaOrbitalEventPath (m N : ℕ)
    (mu : Measure (Dense.ConcreteMatrixState N))
    (q : ℝ) (A : Set (Dense.ConcreteMatrixState N)) (s : ℝ) : ℝ :=
  (concreteSharedBetaPathAction m N mu q s).real A

/-- At orbital time zero, the same-beta path is exactly the central path at
the central coefficient generated by that very beta sample. -/
theorem concreteSharedBetaOrbitalEventPath_zero_sameBeta
    {m N : ℕ} (hN : 1 ≤ N)
    (mu : Measure (Dense.ConcreteMatrixState N))
    (q : ℝ) (A : Set (Dense.ConcreteMatrixState N)) (hA : MeasurableSet A) :
    concreteSharedBetaOrbitalEventPath m N mu q A 0 =
      concreteCentralEventPath N mu A
        (Dense.oneColumnCenteredScalarLog m N q) := by
  letI : IsProbabilityMeasure
      (Dense.complexUnitSphereProbabilityMeasure N) :=
    Dense.complexUnitSphereProbabilityMeasure_isProbability hN
  rw [concreteSharedBetaOrbitalEventPath, concreteSharedBetaPathAction,
    concreteCentralEventPath, concreteCentralAction,
    map_measureReal_apply (measurable_concreteSharedBetaPathUpdate m N q 0) hA,
    map_measureReal_apply (Dense.measurable_concreteCentralMatrixUpdate N _) hA]
  have hupdate : concreteSharedBetaPathUpdate m N q 0 =
      Dense.concreteCentralMatrixUpdate N
        (Dense.oneColumnCenteredScalarLog m N q) ∘ Prod.fst := by
    funext Xv
    unfold concreteSharedBetaPathUpdate
    congr 1
    ext i j
    simp [Dense.concreteOrbitalMatrixUpdate, Dense.concreteOrbitalFactor]
  rw [hupdate]
  change (mu.prod (Dense.complexUnitSphereProbabilityMeasure N)).real
      (Prod.fst ⁻¹' (Dense.concreteCentralMatrixUpdate N
        (Dense.oneColumnCenteredScalarLog m N q) ⁻¹' A)) =
    mu.real (Dense.concreteCentralMatrixUpdate N
      (Dense.oneColumnCenteredScalarLog m N q) ⁻¹' A)
  rw [← map_measureReal_apply measurable_fst
    ((Dense.measurable_concreteCentralMatrixUpdate N _) hA)]
  simp

/-! ## Good truncation and full update -/

/-- The good-event orbital amplitude.  It retains the beta logarithm on the
good event and is zero on the exceptional event. -/
def concreteGoodOrbitalAmplitude (N : ℕ) (c0 q : ℝ) : ℝ :=
  if q ∈ Dense.oneColumnLogBadEvent N c0 then 0
  else Dense.oneColumnRankOneLog q

theorem measurable_concreteGoodOrbitalAmplitude (N : ℕ) (c0 : ℝ) :
    Measurable (concreteGoodOrbitalAmplitude N c0) := by
  unfold concreteGoodOrbitalAmplitude
  exact Measurable.ite (Dense.measurableSet_oneColumnLogBadEvent N c0)
    measurable_const (by
      unfold Dense.oneColumnRankOneLog
      fun_prop)

/-- One common source for the good and full one-column laws. -/
def concreteSharedBetaSourceLaw (m N : ℕ)
    (mu : Measure (Dense.ConcreteMatrixState N)) :
    Measure (ℝ ×
      (Dense.ConcreteMatrixState N × Dense.ComplexUnitSphere N)) :=
  (Dense.oneColumnBetaLaw m N).prod
    (mu.prod (Dense.complexUnitSphereProbabilityMeasure N))

abbrev ConcreteSharedBetaSample (N : ℕ) :=
  ℝ × (Dense.ConcreteMatrixState N × Dense.ComplexUnitSphere N)

def concreteSharedBetaPathUpdateJoint (m N : ℕ) :
    ((ℝ × ℝ) ×
      (Dense.ConcreteMatrixState N × Dense.ComplexUnitSphere N)) →
        Dense.ConcreteMatrixState N :=
  concreteCentralMatrixUpdateJointFn N ∘
    (fun p ↦
      (Dense.oneColumnCenteredScalarLog m N p.1.1,
        concreteOrbitalMatrixUpdateJointFn N (p.1.2, p.2)))

def concreteSharedBetaGoodEmbedding (N : ℕ) (c0 : ℝ) :
    ConcreteSharedBetaSample N →
      ((ℝ × ℝ) ×
        (Dense.ConcreteMatrixState N × Dense.ComplexUnitSphere N)) :=
  fun qXv ↦ ((qXv.1, concreteGoodOrbitalAmplitude N c0 qXv.1), qXv.2)

def concreteSharedBetaGoodUpdate (m N : ℕ) (c0 : ℝ) :
    ConcreteSharedBetaSample N → Dense.ConcreteMatrixState N :=
  concreteSharedBetaPathUpdateJoint m N ∘
    concreteSharedBetaGoodEmbedding N c0

def concreteSharedBetaFullEmbedding (N : ℕ) :
    ConcreteSharedBetaSample N →
      (Dense.ConcreteMatrixState N ×
        (ℝ × Dense.ComplexUnitSphere N)) :=
  fun qXv ↦ (qXv.2.1, (qXv.1, qXv.2.2))

def concreteSharedBetaFullUpdate (m N : ℕ) :
    ConcreteSharedBetaSample N → Dense.ConcreteMatrixState N :=
  (fun xp ↦ Dense.concreteOneColumnMatrixUpdate m N
    xp.2.1 xp.2.2 xp.1) ∘ concreteSharedBetaFullEmbedding N

/-- The good law uses the truncated orbital amplitude and the same beta
sample in the central coefficient. -/
def concreteSharedBetaGoodLaw (m N : ℕ) (c0 : ℝ)
    (mu : Measure (Dense.ConcreteMatrixState N)) :
    Measure (Dense.ConcreteMatrixState N) :=
  (concreteSharedBetaSourceLaw m N mu).map
    (concreteSharedBetaGoodUpdate m N c0)

/-- The full law on the same source, using the literal concrete one-column
matrix update. -/
def concreteSharedBetaFullLaw (m N : ℕ)
    (mu : Measure (Dense.ConcreteMatrixState N)) :
    Measure (Dense.ConcreteMatrixState N) :=
  (concreteSharedBetaSourceLaw m N mu).map
    (concreteSharedBetaFullUpdate m N)

theorem measurable_concreteSharedBetaPathUpdate_joint (m N : ℕ) :
    Measurable (concreteSharedBetaPathUpdateJoint m N) := by
  unfold concreteSharedBetaPathUpdateJoint
  exact (measurable_concreteCentralMatrixUpdateJointFn N).comp
    (((measurable_oneColumnCenteredScalarLog m N).comp measurable_fst.fst).prodMk
      ((measurable_concreteOrbitalMatrixUpdateJointFn N).comp
        (measurable_fst.snd.prodMk measurable_snd)))

theorem measurable_concreteSharedBetaGoodEmbedding (N : ℕ) (c0 : ℝ) :
    Measurable (concreteSharedBetaGoodEmbedding N c0) := by
  unfold concreteSharedBetaGoodEmbedding
  exact (measurable_fst.prodMk
    ((measurable_concreteGoodOrbitalAmplitude N c0).comp measurable_fst)).prodMk
      measurable_snd

theorem measurable_concreteSharedBetaGoodUpdate
    (m N : ℕ) (c0 : ℝ) :
    Measurable (concreteSharedBetaGoodUpdate m N c0) := by
  unfold concreteSharedBetaGoodUpdate
  exact (measurable_concreteSharedBetaPathUpdate_joint m N).comp
    (measurable_concreteSharedBetaGoodEmbedding N c0)

theorem measurable_concreteSharedBetaFullEmbedding (N : ℕ) :
    Measurable (concreteSharedBetaFullEmbedding N) := by
  unfold concreteSharedBetaFullEmbedding
  exact measurable_snd.fst.prodMk
    (measurable_fst.prodMk measurable_snd.snd)

theorem measurable_concreteSharedBetaFullUpdate (m N : ℕ) :
    Measurable (concreteSharedBetaFullUpdate m N) := by
  unfold concreteSharedBetaFullUpdate
  exact (Dense.measurable_concreteOneColumnMatrixUpdate m N).comp
    (measurable_concreteSharedBetaFullEmbedding N)

/-- On the beta support and outside the logarithmic bad event, the good
shared-beta update is pointwise the full one-column update. -/
theorem concreteSharedBetaGoodUpdate_eq_full
    {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N) {c0 q : ℝ}
    (hq0 : 0 < q) (hqgood : q ∉ Dense.oneColumnLogBadEvent N c0)
    (Xv : Dense.ConcreteMatrixState N × Dense.ComplexUnitSphere N) :
    concreteSharedBetaGoodUpdate m N c0 (q, Xv) =
      concreteSharedBetaFullUpdate m N (q, Xv) := by
  unfold concreteSharedBetaGoodUpdate concreteSharedBetaFullUpdate
    concreteSharedBetaPathUpdateJoint concreteSharedBetaGoodEmbedding
    concreteSharedBetaFullEmbedding concreteCentralMatrixUpdateJointFn
    concreteOrbitalMatrixUpdateJointFn
  simp only [Function.comp_apply]
  rw [show concreteGoodOrbitalAmplitude N c0 q =
      Dense.oneColumnRankOneLog q by
    simp [concreteGoodOrbitalAmplitude, hqgood]]
  exact (Dense.concreteOneColumnMatrixUpdate_eq_central_orbital
    hm hN hq0 Xv.2 Xv.1).symm

/-! ## Exact endpoint identities -/

def concreteCentralEndpointUpdate (m N : ℕ) :
    (ℝ × Dense.ConcreteMatrixState N) → Dense.ConcreteMatrixState N :=
  concreteCentralMatrixUpdateJointFn N ∘
    (fun qX ↦ (Dense.oneColumnCenteredScalarLog m N qX.1, qX.2))

theorem measurable_concreteCentralEndpointUpdate (m N : ℕ) :
    Measurable (concreteCentralEndpointUpdate m N) := by
  unfold concreteCentralEndpointUpdate
  exact (measurable_concreteCentralMatrixUpdateJointFn N).comp
    (((measurable_oneColumnCenteredScalarLog m N).comp measurable_fst).prodMk
      measurable_snd)

@[simp]
theorem concreteCentralEndpointUpdate_apply (m N : ℕ) (q : ℝ)
    (X : Dense.ConcreteMatrixState N) :
    concreteCentralEndpointUpdate m N (q, X) =
      Dense.concreteCentralMatrixUpdate N
        (Dense.oneColumnCenteredScalarLog m N q) X := rfl

@[simp]
theorem concreteSharedBetaGoodUpdate_apply (m N : ℕ) (c0 q : ℝ)
    (Xv : Dense.ConcreteMatrixState N × Dense.ComplexUnitSphere N) :
    concreteSharedBetaGoodUpdate m N c0 (q, Xv) =
      concreteSharedBetaPathUpdate m N q
        (concreteGoodOrbitalAmplitude N c0 q) Xv := rfl

theorem concreteCentralMixture_endpoint
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m)
    (mu : Measure (Dense.ConcreteMatrixState N))
    [IsProbabilityMeasure mu]
    (A : Set (Dense.ConcreteMatrixState N)) (hA : MeasurableSet A) :
    (∫ q, concreteCentralEventPath N mu A
        (Dense.oneColumnCenteredScalarLog m N q)
      ∂(Dense.oneColumnBetaLaw m N)) =
      (concreteCentralMixtureLaw m N mu).real A := by
  let _ : IsProbabilityMeasure (Dense.oneColumnBetaLaw m N) :=
    Dense.oneColumnBetaLaw_isProbability hN hNm
  have hmix := integral_map_sections_measureReal_eq_map_prod_measureReal
    (Dense.oneColumnBetaLaw m N) mu
    (concreteCentralEndpointUpdate m N)
    (measurable_concreteCentralEndpointUpdate m N) A hA
  unfold concreteCentralEndpointUpdate concreteCentralMatrixUpdateJointFn at hmix
  change (∫ q, (mu.map (Dense.concreteCentralMatrixUpdate N
      (Dense.oneColumnCenteredScalarLog m N q))).real A
      ∂(Dense.oneColumnBetaLaw m N)) =
    (((Dense.oneColumnBetaLaw m N).prod mu).map
      (fun qX ↦ Dense.concreteCentralMatrixUpdate N
        (Dense.oneColumnCenteredScalarLog m N qX.1) qX.2)).real A at hmix
  simpa only [concreteCentralEventPath, concreteCentralAction,
    concreteCentralMixtureLaw, Function.comp_apply] using hmix

theorem concreteCentralMixture_path_integrable
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m)
    (mu : Measure (Dense.ConcreteMatrixState N))
    [IsProbabilityMeasure mu]
    (A : Set (Dense.ConcreteMatrixState N)) (hA : MeasurableSet A) :
    Integrable
      (fun q ↦ concreteCentralEventPath N mu A
        (Dense.oneColumnCenteredScalarLog m N q))
      (Dense.oneColumnBetaLaw m N) := by
  let _ : IsProbabilityMeasure (Dense.oneColumnBetaLaw m N) :=
    Dense.oneColumnBetaLaw_isProbability hN hNm
  have hint := integrable_map_sections_measureReal
    (Dense.oneColumnBetaLaw m N) mu
    (concreteCentralEndpointUpdate m N)
    (measurable_concreteCentralEndpointUpdate m N) A hA
  unfold concreteCentralEndpointUpdate concreteCentralMatrixUpdateJointFn at hint
  change Integrable
    (fun q ↦ (mu.map (Dense.concreteCentralMatrixUpdate N
      (Dense.oneColumnCenteredScalarLog m N q))).real A)
    (Dense.oneColumnBetaLaw m N) at hint
  simpa only [concreteCentralEventPath, concreteCentralAction,
    Function.comp_apply] using hint

theorem concreteSharedBetaGood_endpoint
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m)
    (mu : Measure (Dense.ConcreteMatrixState N))
    [IsProbabilityMeasure mu]
    (c0 : ℝ) (A : Set (Dense.ConcreteMatrixState N))
    (hA : MeasurableSet A) :
    (∫ q, concreteSharedBetaOrbitalEventPath m N mu q A
        (concreteGoodOrbitalAmplitude N c0 q)
      ∂(Dense.oneColumnBetaLaw m N)) =
      (concreteSharedBetaGoodLaw m N c0 mu).real A := by
  let _ : IsProbabilityMeasure (Dense.oneColumnBetaLaw m N) :=
    Dense.oneColumnBetaLaw_isProbability hN hNm
  let _ : IsProbabilityMeasure
      (Dense.complexUnitSphereProbabilityMeasure N) :=
    Dense.complexUnitSphereProbabilityMeasure_isProbability hN
  let _ : IsProbabilityMeasure
      (mu.prod (Dense.complexUnitSphereProbabilityMeasure N)) := by
    infer_instance
  simpa only [concreteSharedBetaOrbitalEventPath,
    concreteSharedBetaPathAction, concreteSharedBetaGoodLaw,
    concreteSharedBetaSourceLaw, concreteSharedBetaGoodUpdate_apply] using
    (integral_map_sections_measureReal_eq_map_prod_measureReal
      (Dense.oneColumnBetaLaw m N)
      (mu.prod (Dense.complexUnitSphereProbabilityMeasure N))
      (concreteSharedBetaGoodUpdate m N c0)
      (measurable_concreteSharedBetaGoodUpdate m N c0) A hA)

theorem concreteSharedBetaGood_path_integrable
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m)
    (mu : Measure (Dense.ConcreteMatrixState N))
    [IsProbabilityMeasure mu]
    (c0 : ℝ) (A : Set (Dense.ConcreteMatrixState N))
    (hA : MeasurableSet A) :
    Integrable
      (fun q ↦ concreteSharedBetaOrbitalEventPath m N mu q A
        (concreteGoodOrbitalAmplitude N c0 q))
      (Dense.oneColumnBetaLaw m N) := by
  let _ : IsProbabilityMeasure (Dense.oneColumnBetaLaw m N) :=
    Dense.oneColumnBetaLaw_isProbability hN hNm
  let _ : IsProbabilityMeasure
      (Dense.complexUnitSphereProbabilityMeasure N) :=
    Dense.complexUnitSphereProbabilityMeasure_isProbability hN
  let _ : IsProbabilityMeasure
      (mu.prod (Dense.complexUnitSphereProbabilityMeasure N)) := by
    infer_instance
  simpa only [concreteSharedBetaOrbitalEventPath,
    concreteSharedBetaPathAction, concreteSharedBetaGoodUpdate_apply] using
    (integrable_map_sections_measureReal
      (Dense.oneColumnBetaLaw m N)
      (mu.prod (Dense.complexUnitSphereProbabilityMeasure N))
      (concreteSharedBetaGoodUpdate m N c0)
      (measurable_concreteSharedBetaGoodUpdate m N c0) A hA)

theorem concreteSharedBetaZero_path_integrable
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m)
    (mu : Measure (Dense.ConcreteMatrixState N))
    [IsProbabilityMeasure mu]
    (A : Set (Dense.ConcreteMatrixState N)) (hA : MeasurableSet A) :
    Integrable (fun q ↦
      concreteSharedBetaOrbitalEventPath m N mu q A 0)
      (Dense.oneColumnBetaLaw m N) := by
  have heq : (fun q ↦
      concreteSharedBetaOrbitalEventPath m N mu q A 0) =
      fun q ↦ concreteCentralEventPath N mu A
        (Dense.oneColumnCenteredScalarLog m N q) := by
    funext q
    exact concreteSharedBetaOrbitalEventPath_zero_sameBeta hN mu q A hA
  rw [heq]
  exact concreteCentralMixture_path_integrable hN hNm mu A hA

/-! ## Identification with the full one-column kernel and good/bad TV -/

theorem concreteSharedBetaSourceLaw_isProbability
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m)
    (mu : Measure (Dense.ConcreteMatrixState N))
    [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (concreteSharedBetaSourceLaw m N mu) := by
  let _ : IsProbabilityMeasure (Dense.oneColumnBetaLaw m N) :=
    Dense.oneColumnBetaLaw_isProbability hN hNm
  let _ : IsProbabilityMeasure
      (Dense.complexUnitSphereProbabilityMeasure N) :=
    Dense.complexUnitSphereProbabilityMeasure_isProbability hN
  unfold concreteSharedBetaSourceLaw
  infer_instance

/-- The common-source exceptional set consists of the logarithmic bad event
plus the null complement of the open beta support. -/
def concreteSharedBetaExceptionalSet (N : ℕ) (c0 : ℝ) :
    Set (ConcreteSharedBetaSample N) :=
  Prod.fst ⁻¹' (Dense.oneColumnLogBadEvent N c0 ∪ (Ioo (0 : ℝ) 1)ᶜ)

theorem measurableSet_concreteSharedBetaExceptionalSet (N : ℕ) (c0 : ℝ) :
    MeasurableSet (concreteSharedBetaExceptionalSet N c0) := by
  exact ((Dense.measurableSet_oneColumnLogBadEvent N c0).union
    measurableSet_Ioo.compl).preimage measurable_fst

/-- The added support complement is beta-null, so the common-source
exceptional mass is exactly the previously defined bad probability. -/
theorem concreteSharedBetaSourceLaw_exceptional_real
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m)
    (mu : Measure (Dense.ConcreteMatrixState N))
    [IsProbabilityMeasure mu] (c0 : ℝ) :
    (concreteSharedBetaSourceLaw m N mu).real
        (concreteSharedBetaExceptionalSet N c0) =
      Dense.oneColumnLogBadProbability m N c0 := by
  let _ : IsProbabilityMeasure (Dense.oneColumnBetaLaw m N) :=
    Dense.oneColumnBetaLaw_isProbability hN hNm
  let _ : IsProbabilityMeasure
      (Dense.complexUnitSphereProbabilityMeasure N) :=
    Dense.complexUnitSphereProbabilityMeasure_isProbability hN
  let inner := mu.prod (Dense.complexUnitSphereProbabilityMeasure N)
  let _ : IsProbabilityMeasure inner := by
    dsimp [inner]
    infer_instance
  let E : Set ℝ :=
    Dense.oneColumnLogBadEvent N c0 ∪ (Ioo (0 : ℝ) 1)ᶜ
  have hE : MeasurableSet E :=
    (Dense.measurableSet_oneColumnLogBadEvent N c0).union measurableSet_Ioo.compl
  have hfst : Measure.map Prod.fst
      ((Dense.oneColumnBetaLaw m N).prod inner) =
      Dense.oneColumnBetaLaw m N := by
    simp
  have hsupport : ∀ᵐ q ∂(Dense.oneColumnBetaLaw m N), q ∈ Ioo (0 : ℝ) 1 := by
    rw [ae_iff]
    exact Dense.oneColumnBetaLaw_compl_Ioo_eq_zero m N
  have hEeq : (Dense.oneColumnBetaLaw m N).real E =
      (Dense.oneColumnBetaLaw m N).real
        (Dense.oneColumnLogBadEvent N c0) := by
    unfold Measure.real
    congr 1
    apply measure_congr
    filter_upwards [hsupport] with q hq
    dsimp [E]
    apply propext
    change (q ∈ Dense.oneColumnLogBadEvent N c0 ∪ (Ioo (0 : ℝ) 1)ᶜ) ↔
      q ∈ Dense.oneColumnLogBadEvent N c0
    simp only [mem_union, mem_compl_iff]
    exact or_iff_left (not_not_intro hq)
  change (((Dense.oneColumnBetaLaw m N).prod inner).real
      (Prod.fst ⁻¹' E)) =
    (Dense.oneColumnBetaLaw m N).real
      (Dense.oneColumnLogBadEvent N c0)
  calc
    (((Dense.oneColumnBetaLaw m N).prod inner).real
        (Prod.fst ⁻¹' E)) =
        (Measure.map Prod.fst
          ((Dense.oneColumnBetaLaw m N).prod inner)).real E := by
      rw [map_measureReal_apply measurable_fst hE]
    _ = (Dense.oneColumnBetaLaw m N).real E := by rw [hfst]
    _ = _ := hEeq

/-- Reorder `q,(X,v)` into `X,(q,v)`, the source convention used by the
existing ambient one-column kernel. -/
def concreteSharedBetaReorder (N : ℕ) :
    ConcreteSharedBetaSample N →
      (Dense.ConcreteMatrixState N ×
        (ℝ × Dense.ComplexUnitSphere N)) :=
  fun qXv ↦ (qXv.2.1, (qXv.1, qXv.2.2))

theorem measurable_concreteSharedBetaReorder (N : ℕ) :
    Measurable (concreteSharedBetaReorder N) := by
  unfold concreteSharedBetaReorder
  exact measurable_snd.fst.prodMk
    (measurable_fst.prodMk measurable_snd.snd)

theorem map_concreteSharedBetaReorder_source
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m)
    (mu : Measure (Dense.ConcreteMatrixState N))
    [IsProbabilityMeasure mu] :
    (concreteSharedBetaSourceLaw m N mu).map
        (concreteSharedBetaReorder N) =
      mu.prod ((Dense.oneColumnBetaLaw m N).prod
        (Dense.complexUnitSphereProbabilityMeasure N)) := by
  let _ : IsProbabilityMeasure (Dense.oneColumnBetaLaw m N) :=
    Dense.oneColumnBetaLaw_isProbability hN hNm
  let _ : IsProbabilityMeasure
      (Dense.complexUnitSphereProbabilityMeasure N) :=
    Dense.complexUnitSphereProbabilityMeasure_isProbability hN
  let _ : IsProbabilityMeasure (concreteSharedBetaSourceLaw m N mu) :=
    concreteSharedBetaSourceLaw_isProbability hN hNm mu
  let _ : IsProbabilityMeasure
      ((concreteSharedBetaSourceLaw m N mu).map
        (concreteSharedBetaReorder N)) :=
    Measure.isProbabilityMeasure_map
      (measurable_concreteSharedBetaReorder N).aemeasurable
  apply Measure.ext_prod₃
  intro s t u hs ht hu
  rw [Measure.map_apply (measurable_concreteSharedBetaReorder N)
    (hs.prod (ht.prod hu))]
  have hpre : concreteSharedBetaReorder N ⁻¹' (s ×ˢ (t ×ˢ u)) =
      t ×ˢ (s ×ˢ u) := by
    ext x
    constructor
    · rintro ⟨hxS, hxT, hxU⟩
      exact ⟨hxT, hxS, hxU⟩
    · rintro ⟨hxT, hxS, hxU⟩
      exact ⟨hxS, hxT, hxU⟩
  rw [hpre]
  simp [concreteSharedBetaSourceLaw, mul_assoc, mul_left_comm, mul_comm]

/-- The full common-source law is exactly the action of the already defined
concrete one-column kernel. -/
theorem concreteSharedBetaFullLaw_eq_oneColumnKernel
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m)
    (mu : Measure (Dense.ConcreteMatrixState N))
    [IsProbabilityMeasure mu] :
    concreteSharedBetaFullLaw m N mu =
      Dense.concreteOneColumnMatrixKernel m N ∘ₘ mu := by
  let _ : IsProbabilityMeasure (Dense.oneColumnBetaLaw m N) :=
    Dense.oneColumnBetaLaw_isProbability hN hNm
  let _ : IsProbabilityMeasure
      (Dense.complexUnitSphereProbabilityMeasure N) :=
    Dense.complexUnitSphereProbabilityMeasure_isProbability hN
  let param := (Dense.oneColumnBetaLaw m N).prod
    (Dense.complexUnitSphereProbabilityMeasure N)
  let _ : IsProbabilityMeasure param := by
    dsimp [param]
    infer_instance
  let update : Dense.ConcreteMatrixState N ×
      (ℝ × Dense.ComplexUnitSphere N) → Dense.ConcreteMatrixState N :=
    fun xp ↦ Dense.concreteOneColumnMatrixUpdate m N xp.2.1 xp.2.2 xp.1
  have hupdate : Measurable update :=
    Dense.measurable_concreteOneColumnMatrixUpdate m N
  have hprod := independentUpdateKernel_comp_eq_map_prod
    mu param update hupdate
  have hreorder := map_concreteSharedBetaReorder_source hN hNm mu
  unfold concreteSharedBetaFullLaw concreteSharedBetaFullUpdate
    concreteSharedBetaFullEmbedding
  change (concreteSharedBetaSourceLaw m N mu).map
      (update ∘ concreteSharedBetaReorder N) =
    Dense.concreteOneColumnMatrixKernel m N ∘ₘ mu
  rw [← Measure.map_map hupdate (measurable_concreteSharedBetaReorder N),
    hreorder]
  unfold Dense.concreteOneColumnMatrixKernel
    Dense.concreteAmbientOneColumnKernel Dense.ambientOneColumnKernel
    Dense.oneColumnParameterLaw
  exact hprod.symm

/-- Discarding the bad beta event costs exactly its probability; no abstract
coupling premise remains. -/
theorem probabilityTVLE_concreteSharedBetaGood_full
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m)
    (mu : Measure (Dense.ConcreteMatrixState N))
    [IsProbabilityMeasure mu] (c0 : ℝ) (hc0 : 0 < c0) :
    Dense.ProbabilityTVLE
      (concreteSharedBetaGoodLaw m N c0 mu)
      (concreteSharedBetaFullLaw m N mu)
      (Dense.oneColumnLogBadProbability m N c0) := by
  let _ : IsProbabilityMeasure (concreteSharedBetaSourceLaw m N mu) :=
    concreteSharedBetaSourceLaw_isProbability hN hNm mu
  have hcouple := probabilityTVLE_map_map_of_eq_off
    (concreteSharedBetaSourceLaw m N mu)
    (concreteSharedBetaGoodUpdate m N c0)
    (concreteSharedBetaFullUpdate m N)
    (measurable_concreteSharedBetaGoodUpdate m N c0)
    (measurable_concreteSharedBetaFullUpdate m N)
    (concreteSharedBetaExceptionalSet N c0)
    (measurableSet_concreteSharedBetaExceptionalSet N c0)
    (by
      intro qXv hqXv
      have hq : qXv.1 ∉
          Dense.oneColumnLogBadEvent N c0 ∪ (Ioo (0 : ℝ) 1)ᶜ := hqXv
      have hqgood : qXv.1 ∉ Dense.oneColumnLogBadEvent N c0 := by
        intro h
        exact hq (Or.inl h)
      have hqsupport : qXv.1 ∈ Ioo (0 : ℝ) 1 := by
        by_contra h
        exact hq (Or.inr h)
      exact concreteSharedBetaGoodUpdate_eq_full
        (hN.trans hNm) hN hqsupport.1 hqgood qXv.2)
  simpa only [concreteSharedBetaGoodLaw, concreteSharedBetaFullLaw,
    concreteSharedBetaSourceLaw_exceptional_real hN hNm mu c0] using hcouple

/-! ## Truncated-amplitude moments -/

theorem abs_concreteGoodOrbitalAmplitude_le
    (N : ℕ) (c0 q : ℝ) :
    |concreteGoodOrbitalAmplitude N c0 q| ≤
      |Dense.oneColumnRankOneLog q| := by
  unfold concreteGoodOrbitalAmplitude
  split_ifs <;> simp

theorem concreteGoodOrbitalAmplitude_sq_le
    (N : ℕ) (c0 q : ℝ) :
    concreteGoodOrbitalAmplitude N c0 q ^ 2 ≤
      Dense.oneColumnRankOneLog q ^ 2 := by
  unfold concreteGoodOrbitalAmplitude
  split_ifs <;> simp [sq_nonneg]

theorem abs_concreteGoodOrbitalAmplitude_cube_le
    (N : ℕ) (c0 q : ℝ) :
    |concreteGoodOrbitalAmplitude N c0 q| ^ 3 ≤
      |Dense.oneColumnRankOneLog q| ^ 3 := by
  exact pow_le_pow_left₀ (abs_nonneg _)
    (abs_concreteGoodOrbitalAmplitude_le N c0 q) 3

theorem concreteGoodOrbitalAmplitude_sq_integrable
    {Cmean CscalarTwo CbTwo CbThree : ℝ} {m N : ℕ}
    (hmom : OneColumnLogMomentBoundsAt
      Cmean CscalarTwo CbTwo CbThree m N) (c0 : ℝ) :
    Integrable (fun q ↦ concreteGoodOrbitalAmplitude N c0 q ^ 2)
      (Dense.oneColumnBetaLaw m N) := by
  apply hmom.rankOne_sq_integrable.mono
  · exact ((measurable_concreteGoodOrbitalAmplitude N c0).pow_const 2).aestronglyMeasurable
  · filter_upwards [] with q
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
    exact concreteGoodOrbitalAmplitude_sq_le N c0 q

theorem concreteGoodOrbitalAmplitude_cube_integrable
    {Cmean CscalarTwo CbTwo CbThree : ℝ} {m N : ℕ}
    (hmom : OneColumnLogMomentBoundsAt
      Cmean CscalarTwo CbTwo CbThree m N) (c0 : ℝ) :
    Integrable (fun q ↦ |concreteGoodOrbitalAmplitude N c0 q| ^ 3)
      (Dense.oneColumnBetaLaw m N) := by
  apply hmom.rankOne_cube_integrable.mono
  · exact (((measurable_concreteGoodOrbitalAmplitude N c0).abs).pow_const 3).aestronglyMeasurable
  · filter_upwards [] with q
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ |concreteGoodOrbitalAmplitude N c0 q| ^ 3),
      abs_of_nonneg (by positivity : 0 ≤ |Dense.oneColumnRankOneLog q| ^ 3)]
    exact abs_concreteGoodOrbitalAmplitude_cube_le N c0 q

theorem integral_concreteGoodOrbitalAmplitude_sq_le
    {Cmean CscalarTwo CbTwo CbThree : ℝ} {m N : ℕ}
    (hmom : OneColumnLogMomentBoundsAt
      Cmean CscalarTwo CbTwo CbThree m N) (c0 : ℝ) :
    (∫ q, concreteGoodOrbitalAmplitude N c0 q ^ 2
      ∂(Dense.oneColumnBetaLaw m N)) ≤
      ∫ q, Dense.oneColumnRankOneLog q ^ 2
        ∂(Dense.oneColumnBetaLaw m N) := by
  exact integral_mono
    (concreteGoodOrbitalAmplitude_sq_integrable hmom c0)
    hmom.rankOne_sq_integrable
    (fun q ↦ concreteGoodOrbitalAmplitude_sq_le N c0 q)

theorem integral_abs_concreteGoodOrbitalAmplitude_cube_le
    {Cmean CscalarTwo CbTwo CbThree : ℝ} {m N : ℕ}
    (hmom : OneColumnLogMomentBoundsAt
      Cmean CscalarTwo CbTwo CbThree m N) (c0 : ℝ) :
    (∫ q, |concreteGoodOrbitalAmplitude N c0 q| ^ 3
      ∂(Dense.oneColumnBetaLaw m N)) ≤
      ∫ q, |Dense.oneColumnRankOneLog q| ^ 3
        ∂(Dense.oneColumnBetaLaw m N) := by
  exact integral_mono
    (concreteGoodOrbitalAmplitude_cube_integrable hmom c0)
    hmom.rankOne_cube_integrable
    (fun q ↦ abs_concreteGoodOrbitalAmplitude_cube_le N c0 q)

/-! ## Concrete adapter to the correlation-safe Taylor bridge -/

/-- The genuinely analytic obligations for the concrete event paths.  The
moving-support likelihood calculus may be used to establish these fields;
all endpoint, measurability, beta-moment, and good/bad coupling inputs are
proved elsewhere in this file. -/
structure ConcreteSharedBetaScoreBoundsAt
    (m N : ℕ)
    (mu : Measure (Dense.ConcreteMatrixState N))
    (CscoreOne CscoreTwo CorbitalTwo CorbitalThree : ℝ) : Prop where
  scoreOne_nonneg : 0 ≤ CscoreOne
  scoreTwo_nonneg : 0 ≤ CscoreTwo
  orbitalTwo_nonneg : 0 ≤ CorbitalTwo
  orbitalThree_nonneg : 0 ≤ CorbitalThree
  scalarSmooth : ∀ A, MeasurableSet A →
    ContDiff ℝ 2 (concreteCentralEventPath N mu A)
  scalarFirst : ∀ A, MeasurableSet A →
    |iteratedDeriv 1 (concreteCentralEventPath N mu A) 0| ≤
      CscoreOne * (N : ℝ)
  scalarSecond : ∀ A, MeasurableSet A → ∀ q,
    ∀ y ∈ uIcc 0 (Dense.oneColumnCenteredScalarLog m N q),
      |iteratedDeriv 2 (concreteCentralEventPath N mu A) y| ≤
        CscoreTwo * (N : ℝ) ^ 2
  orbitalSmooth : ∀ q A, MeasurableSet A →
    ContDiff ℝ 3 (concreteSharedBetaOrbitalEventPath m N mu q A)
  orbitalFirst : ∀ q A, MeasurableSet A →
    iteratedDeriv 1 (concreteSharedBetaOrbitalEventPath m N mu q A) 0 = 0
  orbitalSecond : ∀ q A, MeasurableSet A →
    |iteratedDeriv 2 (concreteSharedBetaOrbitalEventPath m N mu q A) 0| ≤
      CorbitalTwo
  orbitalThird : ∀ q A, MeasurableSet A → ∀ y ∈
      uIcc 0 (concreteGoodOrbitalAmplitude N 1 q),
    |iteratedDeriv 3 (concreteSharedBetaOrbitalEventPath m N mu q A) y| ≤
      CorbitalThree * (N : ℝ)

/-- Fully concrete same-beta one-column estimate.  Its only unproved inputs
are the beta-log moment bundle (provided by the separate beta calculus) and
the explicit smoothness/score bundle above.  In particular there is no
abstract endpoint law, independence substitution, or bad-event TV premise. -/
theorem probabilityTVLE_concreteOneColumn_of_scoreBounds
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m)
    (hthreshold : 24 * (N : ℝ) ^ 2 ≤ (m : ℝ))
    (mu : Measure (Dense.ConcreteMatrixState N))
    [IsProbabilityMeasure mu]
    {Cmean CscalarTwo CbTwo CbThree : ℝ}
    {CscoreOne CscoreTwo CorbitalTwo CorbitalThree : ℝ}
    (hmom : OneColumnLogMomentBoundsAt
      Cmean CscalarTwo CbTwo CbThree m N)
    (hscore : ConcreteSharedBetaScoreBoundsAt m N mu
      CscoreOne CscoreTwo CorbitalTwo CorbitalThree) :
    Dense.ProbabilityTVLE mu
      (Dense.concreteOneColumnMatrixKernel m N ∘ₘ mu)
      (Dense.denseTelescopingRate
        (CscoreOne * Cmean + CscoreTwo * CscalarTwo +
          (CorbitalTwo * CbTwo / 2 + CorbitalThree * CbThree / 6) + 72)
        N m) := by
  have hraw := probabilityTVLE_denseOneStep_of_correlated_eventPaths
    mu (concreteCentralMixtureLaw m N mu)
      (concreteSharedBetaGoodLaw m N 1 mu)
      (concreteSharedBetaFullLaw m N mu)
      hN hNm hthreshold hmom
      hscore.scoreOne_nonneg hscore.scoreTwo_nonneg
      hscore.orbitalTwo_nonneg hscore.orbitalThree_nonneg
      (concreteCentralEventPath N mu)
      (concreteSharedBetaOrbitalEventPath m N mu)
      (concreteGoodOrbitalAmplitude N 1)
      (fun A hA ↦ concreteCentralEventPath_zero mu A hA)
      (fun A hA ↦ concreteCentralMixture_endpoint hN hNm mu A hA)
      hscore.scalarSmooth hscore.scalarFirst hscore.scalarSecond
      (fun A hA ↦ concreteCentralMixture_path_integrable hN hNm mu A hA)
      (fun q A hA ↦
        concreteSharedBetaOrbitalEventPath_zero_sameBeta hN mu q A hA)
      (fun A hA ↦ concreteSharedBetaGood_endpoint hN hNm mu 1 A hA)
      hscore.orbitalSmooth hscore.orbitalFirst hscore.orbitalSecond
      hscore.orbitalThird
      (fun A hA ↦ concreteSharedBetaZero_path_integrable hN hNm mu A hA)
      (fun A hA ↦ concreteSharedBetaGood_path_integrable hN hNm mu 1 A hA)
      (concreteGoodOrbitalAmplitude_sq_integrable hmom 1)
      (concreteGoodOrbitalAmplitude_cube_integrable hmom 1)
      (integral_concreteGoodOrbitalAmplitude_sq_le hmom 1)
      (integral_abs_concreteGoodOrbitalAmplitude_cube_le hmom 1)
      (probabilityTVLE_concreteSharedBetaGood_full hN hNm mu 1 (by norm_num))
  rw [concreteSharedBetaFullLaw_eq_oneColumnKernel hN hNm mu] at hraw
  exact hraw

/-! ## Scaled-COE base specialization -/

theorem concreteScaledCOECornerLaw_isProbability
    (H : CurrentPRL.UnitaryHaarProbabilityFamily)
    {N K : ℕ} (hNK : N ≤ K) :
    IsProbabilityMeasure (Dense.concreteScaledCOECornerLaw H N K) := by
  let _ : IsProbabilityMeasure
      (CurrentPRL.scaledHaarTransposeGramLaw H K N K) :=
    CurrentPRL.scaledHaarTransposeGramLaw_isProbability H hNK le_rfl
  unfold Dense.concreteScaledCOECornerLaw Dense.concreteHaarAmbientLaw
    normalizedHaarTransposeGramLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_normalizeTransposeGram N K).aemeasurable

/-- Paper-facing base-law adapter.  It introduces no aspect-ratio restriction:
the dense proof may later instantiate it under `K ≥ 16N`, while the global
splice remains free to use the sparse branch below that threshold. -/
theorem probabilityTVLE_concreteScaledCOECorner_oneColumn_of_scoreBounds
    (H : CurrentPRL.UnitaryHaarProbabilityFamily)
    {N K m : ℕ} (hN : 1 ≤ N) (hNK : N ≤ K) (hKm : K ≤ m)
    (hthreshold : 24 * (N : ℝ) ^ 2 ≤ (m : ℝ))
    {Cmean CscalarTwo CbTwo CbThree : ℝ}
    {CscoreOne CscoreTwo CorbitalTwo CorbitalThree : ℝ}
    (hmom : OneColumnLogMomentBoundsAt
      Cmean CscalarTwo CbTwo CbThree m N)
    (hscore : ConcreteSharedBetaScoreBoundsAt m N
      (Dense.concreteScaledCOECornerLaw H N K)
      CscoreOne CscoreTwo CorbitalTwo CorbitalThree) :
    Dense.ProbabilityTVLE
      (Dense.concreteScaledCOECornerLaw H N K)
      (Dense.concreteOneColumnMatrixKernel m N ∘ₘ
        Dense.concreteScaledCOECornerLaw H N K)
      (Dense.denseTelescopingRate
        (CscoreOne * Cmean + CscoreTwo * CscalarTwo +
          (CorbitalTwo * CbTwo / 2 + CorbitalThree * CbThree / 6) + 72)
        N m) := by
  let _ : IsProbabilityMeasure (Dense.concreteScaledCOECornerLaw H N K) :=
    concreteScaledCOECornerLaw_isProbability H hNK
  exact probabilityTVLE_concreteOneColumn_of_scoreBounds
    hN (hNK.trans hKm) hthreshold
    (Dense.concreteScaledCOECornerLaw H N K) hmom hscore

end

end LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

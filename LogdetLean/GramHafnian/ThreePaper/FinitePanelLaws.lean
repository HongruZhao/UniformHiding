import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Independence.Basic

/-!
# Exact laws for a finite iid panel

This file isolates the elementary probability layer used by UH1 and UH2.
Independence and equality of the one-coordinate laws are explicit hypotheses.
No random-matrix input is used here.
-/

open scoped BigOperators ENNReal ProbabilityTheory unitInterval
open Filter MeasureTheory ProbabilityTheory Set

namespace LogdetLean.GramHafnian.ThreePaper.FinitePanelLaws

noncomputable section

/-- A finite mutually independent family with prescribed marginals has the
corresponding product law. -/
theorem iid_product_factorization
    {Omega beta : Type*} [MeasurableSpace Omega] [MeasurableSpace beta]
    {mu : Measure Omega} {q : Nat}
    (X : Fin q -> Omega -> beta)
    (hXmeas : forall i, AEMeasurable (X i) mu)
    (hIndep : iIndepFun X mu)
    (P : Measure beta) (hLaw : forall i, Measure.map (X i) mu = P) :
    Measure.map (fun omega i => X i omega) mu =
      Measure.pi (fun _ : Fin q => P) := by
  rw [hIndep.map_fun_eq_pi_map hXmeas]
  congr 1
  funext i
  exact hLaw i

/-- Exact iid maximum-CDF identity. -/
theorem iid_max_cdf
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu] {q : Nat}
    (X : Fin q -> Omega -> Real)
    (hXmeas : forall i, Measurable (X i))
    (hIndep : iIndepFun X mu)
    (P : Measure Real) [IsProbabilityMeasure P]
    (hLaw : forall i, Measure.map (X i) mu = P)
    (t : Real) :
    mu.real {omega | forall i, X i omega <= t} =
      (P.real (Iic t)) ^ q := by
  let panel : Omega -> (Fin q -> Real) := fun omega i => X i omega
  let box : Set (Fin q -> Real) := Set.pi Set.univ (fun _ => Iic t)
  have hpanel : Measurable panel := measurable_pi_lambda _ hXmeas
  have hbox : MeasurableSet box := MeasurableSet.univ_pi fun _ => measurableSet_Iic
  have hpre : panel ⁻¹' box = {omega | forall i, X i omega <= t} := by
    ext omega
    simp [panel, box, Pi.le_def]
  rw [← hpre, ← map_measureReal_apply hpanel hbox]
  rw [iid_product_factorization X (fun i => (hXmeas i).aemeasurable) hIndep P hLaw]
  change (Measure.pi (fun _ : Fin q => P)).real
      (Set.univ.pi fun _ : Fin q => Iic t) = _
  rw [measureReal_def, Measure.pi_pi]
  simp [measureReal_def]

/-- A predicate-valued random variable is Bernoulli once its success
probability is specified. -/
lemma map_predicate_eq_bernoulliMeasure
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (B : Omega -> Prop) (hB : Measurable B)
    (p : I) (hp : mu.real {omega | B omega} = (p : Real)) :
    Measure.map B mu = Ber(True, False, p) := by
  refine Measure.ext_of_measureReal_singleton fun b => ?_
  by_cases hb : b
  · have hb' : b = True := propext ⟨fun _ => True.intro, fun _ => hb⟩
    subst b
    rw [map_measureReal_apply hB (MeasurableSet.singleton True)]
    have hpre : B ⁻¹' ({True} : Set Prop) = {omega | B omega} := by
      ext omega
      simp
    rw [hpre]
    simp [hp]
  · have hb' : b = False := propext ⟨fun h => (hb h).elim, fun h => h.elim⟩
    subst b
    rw [map_measureReal_apply hB (MeasurableSet.singleton False)]
    have hcomp : B ⁻¹' ({False} : Set Prop) = {omega | B omega}ᶜ := by
      ext omega
      simp
    rw [hcomp, measureReal_compl]
    · simp [hp]
    · exact hB.setOf

/-- The cardinality of a Bernoulli random subset of `Fin q` has Mathlib's
binomial law on `Nat`. -/
lemma map_ncard_setBernoulli_univ_fin_eq_binomial (q : Nat) (p : I) :
    Measure.map Set.ncard setBer((Set.univ : Set (Fin q)), p) = Bin(q, p) := by
  refine Measure.ext_of_measureReal_singleton fun k => ?_
  rw [map_ncard_setBernoulli_real_singleton Set.finite_univ p k]
  rw [binomial_real_singleton]
  simp

/-- Exact binomial law for the number of threshold exceedances in an iid
finite panel.  The parameter is the common one-coordinate tail probability. -/
theorem iid_threshold_count_binomial
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu] {q : Nat}
    (X : Fin q -> Omega -> Real)
    (hXmeas : forall i, Measurable (X i))
    (hIndep : iIndepFun X mu)
    (P : Measure Real) [IsProbabilityMeasure P]
    (hLaw : forall i, Measure.map (X i) mu = P)
    (t : Real) :
    let p : I := ⟨P.real (Ioi t), ⟨measureReal_nonneg,
      measureReal_le_one⟩⟩
    Measure.map (fun omega => Set.ncard {i : Fin q | t < X i omega}) mu =
      Bin(q, p) := by
  dsimp only
  let p : I := ⟨P.real (Ioi t), ⟨measureReal_nonneg,
    measureReal_le_one⟩⟩
  let B : Fin q -> Omega -> Prop := fun i omega => t < X i omega
  have hBmeas (i : Fin q) : Measurable (B i) := by
    exact measurableSet_setOfPred.mp
      (measurableSet_lt measurable_const (hXmeas i))
  have hBindep : iIndepFun B mu := by
    exact hIndep.comp (fun _ x => t < x)
      (fun _ => measurableSet_setOfPred.mp
        (measurableSet_lt measurable_const measurable_id))
  have hBprob (i : Fin q) :
      mu.real {omega | B i omega} = (p : Real) := by
    change mu.real ((X i) ⁻¹' Ioi t) = P.real (Ioi t)
    rw [← map_measureReal_apply (hXmeas i) measurableSet_Ioi, hLaw i]
  have hBlaw (i : Fin q) : Measure.map (B i) mu = Ber(True, False, p) :=
    map_predicate_eq_bernoulliMeasure (B i) (hBmeas i) p (hBprob i)
  have htuple : Measure.map (fun omega i => B i omega) mu =
      Measure.pi (fun _ : Fin q => Ber(True, False, p)) :=
    iid_product_factorization B (fun i => (hBmeas i).aemeasurable)
      hBindep Ber(True, False, p) hBlaw
  have hsetLaw :
      Measure.map (fun omega => {i : Fin q | B i omega}) mu =
        setBer((Set.univ : Set (Fin q)), p) := by
    calc
      Measure.map (fun omega => {i : Fin q | B i omega}) mu =
          Measure.map (fun b : Fin q -> Prop => {i | b i})
            (Measure.map (fun omega i => B i omega) mu) := by
        rw [Measure.map_map measurable_setOfPred
          (measurable_pi_lambda _ hBmeas)]
        rfl
      _ = Measure.map (fun b : Fin q -> Prop => {i | b i})
          (Measure.pi (fun _ : Fin q => Ber(True, False, p))) := by
        rw [htuple]
      _ = setBer((Set.univ : Set (Fin q)), p) := by
        rw [setBernoulli_eq_map, Measure.infinitePi_eq_pi]
        congr 1
  calc
    Measure.map (fun omega => Set.ncard {i : Fin q | t < X i omega}) mu =
        Measure.map Set.ncard
          (Measure.map (fun omega => {i : Fin q | B i omega}) mu) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = Measure.map Set.ncard setBer((Set.univ : Set (Fin q)), p) := by
      rw [hsetLaw]
    _ = Bin(q, p) := map_ncard_setBernoulli_univ_fin_eq_binomial q p

end

end LogdetLean.GramHafnian.ThreePaper.FinitePanelLaws

#print axioms LogdetLean.GramHafnian.ThreePaper.FinitePanelLaws.iid_product_factorization
#print axioms LogdetLean.GramHafnian.ThreePaper.FinitePanelLaws.iid_max_cdf
#print axioms LogdetLean.GramHafnian.ThreePaper.FinitePanelLaws.iid_threshold_count_binomial

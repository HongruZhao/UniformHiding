import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.Real.Sqrt

/-!
# Concentration for finitely colored dependency families

This file proves the analytic core of the overlap-graph application without
introducing any axiom.  A proper coloring reduces the family to independent
color classes.  Hoeffding's lemma is applied inside each class; Mathlib's
general (not necessarily independent) sub-Gaussian addition theorem and a
Cauchy--Schwarz estimate then recover the standard chromatic-number constant.
-/

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Set

namespace LogdetLean.GramHafnian.ThreePaper.OverlapGraphConcentration

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- Increasing the variance proxy preserves the sub-Gaussian MGF property. -/
lemma HasSubgaussianMGF.mono_parameter
    {X : Omega -> Real} {c d : NNReal}
    (hX : HasSubgaussianMGF X c mu) (hcd : c <= d) :
    HasSubgaussianMGF X d mu where
  integrable_exp_mul := hX.integrable_exp_mul
  mgf_le t := (hX.mgf_le t).trans <| by
    apply Real.exp_le_exp.mpr
    have hcdR : (c : Real) <= (d : Real) := by exact_mod_cast hcd
    nlinarith [sq_nonneg t]

/-- A finite sum of sub-Gaussian variables is sub-Gaussian with proxy the
square of the sum of the individual proxy square roots.  No independence is
needed for this statement. -/
lemma HasSubgaussianMGF.finset_sum
    [IsZeroOrProbabilityMeasure mu]
    {iota : Type*} (s : Finset iota) (X : iota -> Omega -> Real)
    (c : iota -> NNReal)
    (hX : forall i, i ∈ s -> HasSubgaussianMGF (X i) (c i) mu) :
    HasSubgaussianMGF
      (fun omega => ∑ i ∈ s, X i omega)
      ((∑ i ∈ s, (c i).sqrt) ^ 2) mu := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (HasSubgaussianMGF.fun_zero (mu := mu))
  | @insert i s hi ih =>
      have hsum := (hX i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => hX j (Finset.mem_insert_of_mem hj)))
      simpa [hi, NNReal.sqrt_sq] using hsum

/-- The centered version of a measurable `[0,1]`-valued variable has
sub-Gaussian proxy `1/4`. -/
lemma unit_interval_centered_subgaussian
    [IsProbabilityMeasure mu]
    {X : Omega -> Real} (hX : AEMeasurable X mu)
    (h01 : ∀ᵐ omega ∂mu, X omega ∈ Icc (0 : Real) 1) :
    HasSubgaussianMGF (fun omega => X omega - mu[X]) (1 / 4 : NNReal) mu := by
  convert (hasSubgaussianMGF_of_mem_Icc (μ := mu) (X := X) hX h01) using 1 <;>
    norm_num

/-- The cardinalities of all fibers of a map sum to the domain cardinality. -/
lemma sum_fiber_card
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    [DecidableEq kappa] (color : iota -> kappa) :
    ∑ a : kappa, Fintype.card {i : iota // color i = a} = Fintype.card iota := by
  simpa using (Fintype.sum_fiberwise color (fun _ : iota => (1 : Nat)))

/-- The Cauchy--Schwarz estimate on fiber sizes that produces the chromatic
number, rather than its square, in the concentration exponent. -/
lemma sq_sum_sqrt_fiber_card_le
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    [DecidableEq kappa] (color : iota -> kappa) :
    (∑ a : kappa, NNReal.sqrt (Fintype.card {i : iota // color i = a})) ^ 2
      <= (Fintype.card kappa : NNReal) * Fintype.card iota := by
  have hcs := NNReal.sum_sqrt_mul_sqrt_le (Finset.univ : Finset kappa)
    (fun a => (Fintype.card {i : iota // color i = a} : NNReal))
    (fun _ => (1 : NNReal))
  simp only [NNReal.sqrt_one, mul_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hcs
  have hfib :
      (∑ a : kappa, (Fintype.card {i : iota // color i = a} : NNReal)) =
        Fintype.card iota := by
    exact_mod_cast sum_fiber_card color
  rw [hfib] at hcs
  calc
    (∑ a : kappa, NNReal.sqrt (Fintype.card {i : iota // color i = a})) ^ 2
        <= (NNReal.sqrt (Fintype.card iota) *
          NNReal.sqrt (Fintype.card kappa)) ^ 2 := by gcongr
    _ = (Fintype.card kappa : NNReal) * Fintype.card iota := by
      rw [mul_pow, NNReal.sq_sqrt, NNReal.sq_sqrt, mul_comm]

/-- The same fiber-size estimate after inserting Hoeffding's `1/4` proxy. -/
lemma sq_sum_sqrt_fiber_quarter_le
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    [DecidableEq kappa] (color : iota -> kappa) :
    (∑ a : kappa,
        NNReal.sqrt ((Fintype.card {i : iota // color i = a} : NNReal) / 4)) ^ 2
      <= ((Fintype.card kappa : NNReal) * Fintype.card iota) / 4 := by
  have h := sq_sum_sqrt_fiber_card_le color
  calc
    (∑ a : kappa,
        NNReal.sqrt ((Fintype.card {i : iota // color i = a} : NNReal) / 4)) ^ 2 =
        ((∑ a : kappa,
          NNReal.sqrt (Fintype.card {i : iota // color i = a})) / 2) ^ 2 := by
      congr 1
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      rw [NNReal.sqrt_div]
      rw [show (4 : NNReal) = (2 : NNReal) ^ 2 by norm_num, NNReal.sqrt_sq]
    _ = (∑ a : kappa,
          NNReal.sqrt (Fintype.card {i : iota // color i = a})) ^ 2 / 4 := by
      ring
    _ <= ((Fintype.card kappa : NNReal) * Fintype.card iota) / 4 := by
      exact div_le_div_of_nonneg_right h (by positivity)

/-- Hoeffding inside one color class.  Independence is required only among
vertices of that class. -/
lemma color_class_centered_sum_subgaussian
    [IsProbabilityMeasure mu]
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    [DecidableEq kappa]
    (color : iota -> kappa) (a : kappa) (X : iota -> Omega -> Real)
    (hXmeas : forall i, AEMeasurable (X i) mu)
    (hX01 : forall i, ∀ᵐ omega ∂mu, X i omega ∈ Icc (0 : Real) 1)
    (hIndep : iIndepFun (fun i : {i : iota // color i = a} => X i) mu) :
    HasSubgaussianMGF
      (fun omega => ∑ i : {i : iota // color i = a},
        (X i omega - mu[X i]))
      ((Fintype.card {i : iota // color i = a} : NNReal) / 4) mu := by
  let centered : {i : iota // color i = a} -> Omega -> Real :=
    fun i omega => X i omega - mu[X i]
  have hIndepCentered : iIndepFun centered mu := by
    have h := hIndep.comp
      (fun i x => x - mu[X i])
      (fun _ => measurable_id.sub measurable_const)
    simpa [centered, Function.comp_def] using h
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun
    (c := fun _ : {i : iota // color i = a} => (1 / 4 : NNReal))
    (s := Finset.univ) hIndepCentered
    (fun i _ => unit_interval_centered_subgaussian (hXmeas i) (hX01 i))
  simpa [centered, div_eq_mul_inv] using hsum

/-- Exact chromatic Hoeffding MGF bound.  A coloring with `k` colors and
independence inside every color class gives proxy `k*q/4` for a family of
`q` variables in `[0,1]`. -/
theorem colored_centered_sum_subgaussian
    [IsProbabilityMeasure mu]
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    [DecidableEq kappa]
    (color : iota -> kappa) (X : iota -> Omega -> Real)
    (hXmeas : forall i, AEMeasurable (X i) mu)
    (hX01 : forall i, ∀ᵐ omega ∂mu, X i omega ∈ Icc (0 : Real) 1)
    (hIndep : forall a, iIndepFun
      (fun i : {i : iota // color i = a} => X i) mu) :
    HasSubgaussianMGF
      (fun omega => ∑ i : iota, (X i omega - mu[X i]))
      (((Fintype.card kappa : NNReal) * Fintype.card iota) / 4) mu := by
  let classSum : kappa -> Omega -> Real := fun a omega =>
    ∑ i : {i : iota // color i = a}, (X i omega - mu[X i])
  let classProxy : kappa -> NNReal := fun a =>
    (Fintype.card {i : iota // color i = a} : NNReal) / 4
  have hClass : forall a, HasSubgaussianMGF (classSum a) (classProxy a) mu :=
    fun a => color_class_centered_sum_subgaussian color a X hXmeas hX01 (hIndep a)
  have hAll := HasSubgaussianMGF.finset_sum
    (mu := mu) (Finset.univ : Finset kappa) classSum classProxy
    (fun a _ => hClass a)
  have hAll' : HasSubgaussianMGF
      (fun omega => ∑ i : iota, (X i omega - mu[X i]))
      ((∑ a : kappa, (classProxy a).sqrt) ^ 2) mu := by
    apply hAll.congr
    filter_upwards [] with omega
    simpa [classSum] using
      (Fintype.sum_fiberwise color (fun i => X i omega - mu[X i]))
  exact LogdetLean.GramHafnian.ThreePaper.OverlapGraphConcentration.HasSubgaussianMGF.mono_parameter
    hAll' (by
    simpa [classProxy] using sq_sum_sqrt_fiber_quarter_le color)

/-- Two-sided Chernoff bound for a sub-Gaussian variable. -/
lemma HasSubgaussianMGF.measure_abs_ge_le
    {X : Omega -> Real} {c : NNReal}
    (hX : HasSubgaussianMGF X c mu) {epsilon : Real}
    (hepsilon : 0 <= epsilon) :
    mu.real {omega | epsilon <= |X omega|} <=
      2 * Real.exp (-epsilon ^ 2 / (2 * (c : Real))) := by
  have hset : {omega | epsilon <= |X omega|} =
      {omega | epsilon <= X omega} ∪ {omega | epsilon <= (-X) omega} := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_union, Pi.neg_apply, le_abs]
  rw [hset]
  calc
    mu.real ({omega | epsilon <= X omega} ∪
        {omega | epsilon <= (-X) omega}) <=
        mu.real {omega | epsilon <= X omega} +
          mu.real {omega | epsilon <= (-X) omega} :=
      measureReal_union_le _ _
    _ <= Real.exp (-epsilon ^ 2 / (2 * (c : Real))) +
        Real.exp (-epsilon ^ 2 / (2 * (c : Real))) :=
      add_le_add (hX.measure_ge_le hepsilon) (hX.neg.measure_ge_le hepsilon)
    _ = 2 * Real.exp (-epsilon ^ 2 / (2 * (c : Real))) := by ring

/-- Exact two-sided chromatic Hoeffding bound in unnormalized-sum form.
Here `q` is the number of variables and `k` is the number of colors. -/
theorem colored_hoeffding_two_sided_sum
    [IsProbabilityMeasure mu]
    {q k : Nat} (hq : 0 < q) (hk : 0 < k)
    (color : Fin q -> Fin k) (X : Fin q -> Omega -> Real)
    (hXmeas : forall i, AEMeasurable (X i) mu)
    (hX01 : forall i, ∀ᵐ omega ∂mu, X i omega ∈ Icc (0 : Real) 1)
    (hIndep : forall a, iIndepFun
      (fun i : {i : Fin q // color i = a} => X i) mu)
    {t : Real} (ht : 0 <= t) :
    mu.real {omega |
      (q : Real) * t <= |∑ i : Fin q, (X i omega - mu[X i])|} <=
      2 * Real.exp (-2 * (q : Real) * t ^ 2 / (k : Real)) := by
  have hsub := colored_centered_sum_subgaussian color X hXmeas hX01 hIndep
  have htail :=
    LogdetLean.GramHafnian.ThreePaper.OverlapGraphConcentration.HasSubgaussianMGF.measure_abs_ge_le
      hsub (epsilon := (q : Real) * t) (mul_nonneg (by positivity) ht)
  convert htail using 1
  congr 2
  have hqR : (0 : Real) < q := by exact_mod_cast hq
  have hkR : (0 : Real) < k := by exact_mod_cast hk
  norm_num
  field_simp
  ring

/-- Paper-normalized form.  If all expectations equal `m`, the average of
the colored dependency family obeys the standard
`2 exp (-2 q t^2 / k)` estimate. -/
theorem colored_hoeffding_two_sided_average
    [IsProbabilityMeasure mu]
    {q k : Nat} (hq : 0 < q) (hk : 0 < k)
    (color : Fin q -> Fin k) (X : Fin q -> Omega -> Real)
    (hXmeas : forall i, AEMeasurable (X i) mu)
    (hX01 : forall i, ∀ᵐ omega ∂mu, X i omega ∈ Icc (0 : Real) 1)
    (hIndep : forall a, iIndepFun
      (fun i : {i : Fin q // color i = a} => X i) mu)
    (m : Real) (hmean : forall i, mu[X i] = m)
    {t : Real} (ht : 0 <= t) :
    mu.real {omega |
      t <= |(1 / (q : Real)) * (∑ i : Fin q, X i omega) - m|} <=
      2 * Real.exp (-2 * (q : Real) * t ^ 2 / (k : Real)) := by
  have hqR : (0 : Real) < q := by exact_mod_cast hq
  have hset :
      {omega | t <= |(1 / (q : Real)) * (∑ i : Fin q, X i omega) - m|} =
      {omega | (q : Real) * t <=
        |∑ i : Fin q, (X i omega - mu[X i])|} := by
    ext omega
    have hcenter :
        (∑ i : Fin q, (X i omega - mu[X i])) =
          (∑ i : Fin q, X i omega) - (q : Real) * m := by
      simp_rw [hmean]
      rw [Finset.sum_sub_distrib]
      simp
    change t <= |(1 / (q : Real)) * (∑ i : Fin q, X i omega) - m| <->
      (q : Real) * t <= |∑ i : Fin q, (X i omega - mu[X i])|
    rw [hcenter]
    have havg :
        (1 / (q : Real)) * (∑ i : Fin q, X i omega) - m =
          ((∑ i : Fin q, X i omega) - (q : Real) * m) / (q : Real) := by
      field_simp
    rw [havg, abs_div, abs_of_pos hqR]
    exact (le_div_iff₀ hqR).trans (by rw [mul_comm])
  rw [hset]
  exact colored_hoeffding_two_sided_sum hq hk color X hXmeas hX01 hIndep ht

/-- Exact form printed in UH3.  It is enough to provide a coloring with
`k <= Delta + 1` and independence inside each color class.  The conclusion
has the paper's `Delta + 1` denominator. -/
theorem colored_hoeffding_two_sided_average_maxDegree
    [IsProbabilityMeasure mu]
    {q k Delta : Nat} (hq : 0 < q) (hk : 0 < k)
    (hkDelta : k <= Delta + 1)
    (color : Fin q -> Fin k) (X : Fin q -> Omega -> Real)
    (hXmeas : forall i, AEMeasurable (X i) mu)
    (hX01 : forall i, ∀ᵐ omega ∂mu, X i omega ∈ Icc (0 : Real) 1)
    (hIndep : forall a, iIndepFun
      (fun i : {i : Fin q // color i = a} => X i) mu)
    (m : Real) (hmean : forall i, mu[X i] = m)
    {t : Real} (ht : 0 <= t) :
    mu.real {omega |
      t <= |(1 / (q : Real)) * (∑ i : Fin q, X i omega) - m|} <=
      2 * Real.exp
        (-2 * (q : Real) * t ^ 2 / ((Delta : Real) + 1)) := by
  calc
    mu.real {omega |
        t <= |(1 / (q : Real)) * (∑ i : Fin q, X i omega) - m|} <=
        2 * Real.exp (-2 * (q : Real) * t ^ 2 / (k : Real)) :=
      colored_hoeffding_two_sided_average hq hk color X hXmeas hX01 hIndep m hmean ht
    _ <= 2 * Real.exp
        (-2 * (q : Real) * t ^ 2 / ((Delta : Real) + 1)) := by
      have hkR : (0 : Real) < k := by exact_mod_cast hk
      have hkDeltaR : (k : Real) <= (Delta : Real) + 1 := by exact_mod_cast hkDelta
      have hnum : 0 <= 2 * (q : Real) * t ^ 2 := by positivity
      have harg :
          -2 * (q : Real) * t ^ 2 / (k : Real) <=
            -2 * (q : Real) * t ^ 2 / ((Delta : Real) + 1) := by
        have hbase := neg_le_neg (div_le_div_of_nonneg_left hnum hkR hkDeltaR)
        have hleft :
            -2 * (q : Real) * t ^ 2 / (k : Real) =
              -(2 * (q : Real) * t ^ 2 / (k : Real)) := by ring
        have hright :
            -2 * (q : Real) * t ^ 2 / ((Delta : Real) + 1) =
              -(2 * (q : Real) * t ^ 2 / ((Delta : Real) + 1)) := by ring
        rw [hleft, hright]
        exact hbase
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by norm_num)

end

end LogdetLean.GramHafnian.ThreePaper.OverlapGraphConcentration

#print axioms LogdetLean.GramHafnian.ThreePaper.OverlapGraphConcentration.colored_centered_sum_subgaussian
#print axioms LogdetLean.GramHafnian.ThreePaper.OverlapGraphConcentration.colored_hoeffding_two_sided_average
#print axioms LogdetLean.GramHafnian.ThreePaper.OverlapGraphConcentration.colored_hoeffding_two_sided_average_maxDegree

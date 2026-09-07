import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalCenteredLogScoreMomentExternal
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloSupportFromDensity
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_DeterministicOperator
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteScaledCOECornerProbability
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.MixedScalarQuadraticClosure
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H8_Proof
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Exact independent reductions for H11 and H13

This file does not use either legacy H11/H13 declaration.  It separates the
two remaining ingredients:

* one common, score-free `L^4` package for the operator radius of the concrete
  beta-prime matrix `Y`;
* one deterministic support formula/envelope for each literal higher score.

The two endpoint reducers are independent: the H11 theorem does not assume
H13 and the H13 theorem does not assume H11.  The dimension-one instances are
proved outright from the fact that the centered direction is zero.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.CurrentPRL
open LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

abbrev higherScoreMatrixLaw (N K : ℕ) : Measure (ConcreteMatrixState N) :=
  concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K

abbrev higherScoreSphereLaw (N : ℕ) : Measure (ComplexUnitSphere N) :=
  complexUnitSphereProbabilityMeasure N

/-- The score-free matrix statistic required by both H11 and H13. -/
def concreteHigherScoreOpRadius (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  ‖concreteCOEY N K A‖

/-- The exact radial envelope used for the fourth logarithmic score. -/
def h11HigherScoreRadialEnvelope (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  4096 * concreteHigherScoreOpRadius N K A *
    (1 + concreteHigherScoreOpRadius N K A / concreteCOEExponent N K) ^ 3

/-- The exact radial envelope used for the `ell_1 ell_3` product. -/
def h13HigherScoreRadialEnvelope (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  1024 * concreteHigherScoreOpRadius N K A ^ 2 *
    (1 + concreteHigherScoreOpRadius N K A / concreteCOEExponent N K) ^ 2

/-- The common score-free scientific blocker.  It is strictly upstream of
both endpoints and mentions neither logarithmic score. -/
structure ConcreteHigherScoreOpRadiusL4Package (N K : ℕ) : Prop where
  memLp_four :
    MemLp (concreteHigherScoreOpRadius N K) 4 (higherScoreMatrixLaw N K)
  lpNorm_four_le : 16 * N ≤ K →
    lpNorm (concreteHigherScoreOpRadius N K) 4
        (higherScoreMatrixLaw N K) ≤
      4096 * (N : ℝ)

/-- The remaining deterministic H11 calculation, stated only on the literal
open-ball support.  Full-domain measurability is kept explicit because the
literal score is defined by a total iterated derivative. -/
structure H11HigherScoreDeterministicEnvelope (N K : ℕ) : Prop where
  measurable_score : Measurable (concreteCenteredEll 4 N K)
  abs_le_on_support :
    ∀ (A : ConcreteMatrixState N) (v : ComplexUnitSphere N),
      (unscaleCOECorner K A).IsSymm →
      coeCornerSupport (unscaleCOECorner K A) →
      |concreteCenteredEll 4 N K (A, v)| ≤
        h11HigherScoreRadialEnvelope N K A

/-- The remaining deterministic H13 calculation.  It is deliberately
separate from H11. -/
structure H13HigherScoreDeterministicEnvelope (N K : ℕ) : Prop where
  measurable_scoreProduct : Measurable (fun p ↦
    concreteCenteredEll 1 N K p * concreteCenteredEll 3 N K p)
  abs_le_on_support :
    ∀ (A : ConcreteMatrixState N) (v : ComplexUnitSphere N),
      (unscaleCOECorner K A).IsSymm →
      coeCornerSupport (unscaleCOECorner K A) →
      |concreteCenteredEll 1 N K (A, v) *
          concreteCenteredEll 3 N K (A, v)| ≤
        h13HigherScoreRadialEnvelope N K A

theorem concreteHigherScoreOpRadius_nonneg
    (N K : ℕ) (A : ConcreteMatrixState N) :
    0 ≤ concreteHigherScoreOpRadius N K A :=
  norm_nonneg _

theorem concreteCOEExponent_pos_of_higherScoreGap
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    0 < concreteCOEExponent N K := by
  unfold concreteCOEExponent
  have hgapR : (2 : ℝ) * (N : ℝ) + 8 ≤ (K : ℝ) := by
    exact_mod_cast hgap
  linarith

theorem concreteCOEExponent_ge_dimension_of_dense
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    (N : ℝ) ≤ concreteCOEExponent N K := by
  unfold concreteCOEExponent
  have hdenseR : (16 : ℝ) * (N : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hdense
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  linarith

theorem h11HigherScoreRadialEnvelope_nonneg
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N) :
    0 ≤ h11HigherScoreRadialEnvelope N K A := by
  have hc := concreteCOEExponent_pos_of_higherScoreGap hgap
  have hr := concreteHigherScoreOpRadius_nonneg N K A
  have hbase : 0 ≤ 1 + concreteHigherScoreOpRadius N K A /
      concreteCOEExponent N K :=
    add_nonneg zero_le_one (div_nonneg hr hc.le)
  unfold h11HigherScoreRadialEnvelope
  exact mul_nonneg (mul_nonneg (by norm_num) hr) (pow_nonneg hbase 3)

theorem h13HigherScoreRadialEnvelope_nonneg
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N) :
    0 ≤ h13HigherScoreRadialEnvelope N K A := by
  have hc := concreteCOEExponent_pos_of_higherScoreGap hgap
  unfold h13HigherScoreRadialEnvelope
  positivity

private theorem h11HigherScore_radial_numeric
    {n c L : ℝ} (hn : 1 ≤ n) (hc : n ≤ c)
    (hL0 : 0 ≤ L) (hL : L ≤ 4096 * n) :
    4096 * (L + (3 / c) * L ^ 2 + (3 / c ^ 2) * L ^ 3 +
        (1 / c ^ 3) * L ^ 4) ≤
      centeredLogScoreFourthMomentConstant * n ^ 2 := by
  have hnpos : 0 < n := zero_lt_one.trans_le hn
  have hcpos : 0 < c := hnpos.trans_le hc
  have hc2 : n ^ 2 ≤ c ^ 2 := by nlinarith
  have hc3 : n ^ 3 ≤ c ^ 3 := by
    exact pow_le_pow_left₀ hnpos.le hc 3
  have hL2 : L ^ 2 ≤ (4096 * n) ^ 2 :=
    pow_le_pow_left₀ hL0 hL 2
  have hL3 : L ^ 3 ≤ (4096 * n) ^ 3 :=
    pow_le_pow_left₀ hL0 hL 3
  have hL4 : L ^ 4 ≤ (4096 * n) ^ 4 :=
    pow_le_pow_left₀ hL0 hL 4
  have h2 : L ^ 2 / c ≤ 4096 ^ 2 * n := by
    apply (div_le_iff₀ hcpos).2
    calc
      L ^ 2 ≤ (4096 * n) ^ 2 := hL2
      _ = (4096 ^ 2 * n) * n := by ring
      _ ≤ (4096 ^ 2 * n) * c :=
        mul_le_mul_of_nonneg_left hc (by positivity)
  have h3 : L ^ 3 / c ^ 2 ≤ 4096 ^ 3 * n := by
    apply (div_le_iff₀ (sq_pos_of_pos hcpos)).2
    calc
      L ^ 3 ≤ (4096 * n) ^ 3 := hL3
      _ = (4096 ^ 3 * n) * n ^ 2 := by ring
      _ ≤ (4096 ^ 3 * n) * c ^ 2 :=
        mul_le_mul_of_nonneg_left hc2 (by positivity)
  have h4 : L ^ 4 / c ^ 3 ≤ 4096 ^ 4 * n := by
    apply (div_le_iff₀ (pow_pos hcpos 3)).2
    calc
      L ^ 4 ≤ (4096 * n) ^ 4 := hL4
      _ = (4096 ^ 4 * n) * n ^ 3 := by ring
      _ ≤ (4096 ^ 4 * n) * c ^ 3 :=
        mul_le_mul_of_nonneg_left hc3 (by positivity)
  have hcore :
      L + (3 / c) * L ^ 2 + (3 / c ^ 2) * L ^ 3 +
          (1 / c ^ 3) * L ^ 4 ≤
        (4096 + 3 * 4096 ^ 2 + 3 * 4096 ^ 3 + 4096 ^ 4) * n := by
    rw [show (3 / c) * L ^ 2 = 3 * (L ^ 2 / c) by ring,
      show (3 / c ^ 2) * L ^ 3 = 3 * (L ^ 3 / c ^ 2) by ring,
      show (1 / c ^ 3) * L ^ 4 = L ^ 4 / c ^ 3 by ring]
    nlinarith
  have hn_sq : n ≤ n ^ 2 := by nlinarith
  calc
    4096 * (L + (3 / c) * L ^ 2 + (3 / c ^ 2) * L ^ 3 +
        (1 / c ^ 3) * L ^ 4) ≤
        4096 *
          ((4096 + 3 * 4096 ^ 2 + 3 * 4096 ^ 3 + 4096 ^ 4) * n) :=
      mul_le_mul_of_nonneg_left hcore (by norm_num)
    _ = (4096 *
        (4096 + 3 * 4096 ^ 2 + 3 * 4096 ^ 3 + 4096 ^ 4)) * n := by
      ring
    _ ≤ centeredLogScoreFourthMomentConstant * n := by
      apply mul_le_mul_of_nonneg_right _ hnpos.le
      norm_num [centeredLogScoreFourthMomentConstant,
        denseClassicalMomentConstant]
    _ ≤ centeredLogScoreFourthMomentConstant * n ^ 2 := by
      apply mul_le_mul_of_nonneg_left hn_sq
      norm_num [centeredLogScoreFourthMomentConstant,
        denseClassicalMomentConstant]

private theorem h13HigherScore_radial_numeric
    {n c L : ℝ} (hn : 1 ≤ n) (hc : n ≤ c)
    (hL0 : 0 ≤ L) (hL : L ≤ 4096 * n) :
    1024 * (L ^ 2 + (2 / c) * L ^ 3 + (1 / c ^ 2) * L ^ 4) ≤
      centeredLogScoreFourthMomentConstant * n ^ 2 := by
  have hnpos : 0 < n := zero_lt_one.trans_le hn
  have hcpos : 0 < c := hnpos.trans_le hc
  have hc2 : n ^ 2 ≤ c ^ 2 := by nlinarith
  have hL2 : L ^ 2 ≤ (4096 * n) ^ 2 :=
    pow_le_pow_left₀ hL0 hL 2
  have hL3 : L ^ 3 ≤ (4096 * n) ^ 3 :=
    pow_le_pow_left₀ hL0 hL 3
  have hL4 : L ^ 4 ≤ (4096 * n) ^ 4 :=
    pow_le_pow_left₀ hL0 hL 4
  have h3 : L ^ 3 / c ≤ 4096 ^ 3 * n ^ 2 := by
    apply (div_le_iff₀ hcpos).2
    calc
      L ^ 3 ≤ (4096 * n) ^ 3 := hL3
      _ = (4096 ^ 3 * n ^ 2) * n := by ring
      _ ≤ (4096 ^ 3 * n ^ 2) * c :=
        mul_le_mul_of_nonneg_left hc (by positivity)
  have h4 : L ^ 4 / c ^ 2 ≤ 4096 ^ 4 * n ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hcpos)).2
    calc
      L ^ 4 ≤ (4096 * n) ^ 4 := hL4
      _ = (4096 ^ 4 * n ^ 2) * n ^ 2 := by ring
      _ ≤ (4096 ^ 4 * n ^ 2) * c ^ 2 :=
        mul_le_mul_of_nonneg_left hc2 (by positivity)
  have hcore :
      L ^ 2 + (2 / c) * L ^ 3 + (1 / c ^ 2) * L ^ 4 ≤
        (4096 ^ 2 + 2 * 4096 ^ 3 + 4096 ^ 4) * n ^ 2 := by
    rw [show (2 / c) * L ^ 3 = 2 * (L ^ 3 / c) by ring,
      show (1 / c ^ 2) * L ^ 4 = L ^ 4 / c ^ 2 by ring]
    nlinarith
  calc
    1024 * (L ^ 2 + (2 / c) * L ^ 3 + (1 / c ^ 2) * L ^ 4) ≤
        1024 * ((4096 ^ 2 + 2 * 4096 ^ 3 + 4096 ^ 4) * n ^ 2) :=
      mul_le_mul_of_nonneg_left hcore (by norm_num)
    _ = (1024 * (4096 ^ 2 + 2 * 4096 ^ 3 + 4096 ^ 4)) * n ^ 2 := by
      ring
    _ ≤ centeredLogScoreFourthMomentConstant * n ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg n)
      norm_num [centeredLogScoreFourthMomentConstant,
        denseClassicalMomentConstant]

/-- A sharp `L^4` radius estimate is sufficient for both radial envelopes.
This is measure-theoretic algebra; no score formula or endpoint occurs. -/
theorem h11H13HigherScoreRadial_momentPackages_of_opRadiusL4
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (H : ConcreteHigherScoreOpRadiusL4Package N K) :
    (MemLp (h11HigherScoreRadialEnvelope N K) 1
        (higherScoreMatrixLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (h11HigherScoreRadialEnvelope N K) 1
            (higherScoreMatrixLaw N K) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2)) ∧
    (MemLp (h13HigherScoreRadialEnvelope N K) 1
        (higherScoreMatrixLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (h13HigherScoreRadialEnvelope N K) 1
            (higherScoreMatrixLaw N K) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2)) := by
  let μ : Measure (ConcreteMatrixState N) := higherScoreMatrixLaw N K
  let r : ConcreteMatrixState N → ℝ := concreteHigherScoreOpRadius N K
  let r2 : ConcreteMatrixState N → ℝ := fun A ↦ r A ^ 2
  let r3 : ConcreteMatrixState N → ℝ := fun A ↦ r A * r2 A
  let r4 : ConcreteMatrixState N → ℝ := fun A ↦ r2 A * r2 A
  let c : ℝ := concreteCOEExponent N K
  let a2 : ℝ := 3 / c
  let a3 : ℝ := 3 / c ^ 2
  let a4 : ℝ := 1 / c ^ 3
  let b3 : ℝ := 2 / c
  let b4 : ℝ := 1 / c ^ 2
  let s2 : ConcreteMatrixState N → ℝ := a2 • r2
  let s3 : ConcreteMatrixState N → ℝ := a3 • r3
  let s4 : ConcreteMatrixState N → ℝ := a4 • r4
  let t3 : ConcreteMatrixState N → ℝ := b3 • r3
  let t4 : ConcreteMatrixState N → ℝ := b4 • r4
  let core11 : ConcreteMatrixState N → ℝ := ((r + s2) + s3) + s4
  let core13 : ConcreteMatrixState N → ℝ := (r2 + t3) + t4
  letI : IsProbabilityMeasure μ :=
    canonicalScaledCOECornerLaw_isProbability (by omega)
  have hcpos : 0 < c := by
    simpa only [c] using concreteCOEExponent_pos_of_higherScoreGap hgap
  have ha2 : 0 ≤ a2 := by dsimp only [a2]; positivity
  have ha3 : 0 ≤ a3 := by dsimp only [a3]; positivity
  have ha4 : 0 ≤ a4 := by dsimp only [a4]; positivity
  have hb3 : 0 ≤ b3 := by dsimp only [b3]; positivity
  have hb4 : 0 ≤ b4 := by dsimp only [b4]; positivity
  have hrFour : MemLp r 4 μ := by
    simpa only [r, μ] using H.memLp_four
  have hrTwo : MemLp r 2 μ :=
    hrFour.mono_exponent (by norm_num)
  have hrOne : MemLp r 1 μ :=
    hrFour.mono_exponent (by norm_num)
  have hr2Two : MemLp r2 2 μ := by
    simpa only [r2] using memLp_sq_two_of_memLp_four hrFour
  have hr2One : MemLp r2 1 μ :=
    hr2Two.mono_exponent (by norm_num)
  have hr3One : MemLp r3 1 μ := by
    simpa only [r3, mul_comm] using hrTwo.mul' hr2Two
  have hr4One : MemLp r4 1 μ := by
    simpa only [r4] using hr2Two.mul' hr2Two
  have hs2 : MemLp s2 1 μ := by
    simpa only [s2] using hr2One.const_smul a2
  have hs3 : MemLp s3 1 μ := by
    simpa only [s3] using hr3One.const_smul a3
  have hs4 : MemLp s4 1 μ := by
    simpa only [s4] using hr4One.const_smul a4
  have ht3 : MemLp t3 1 μ := by
    simpa only [t3] using hr3One.const_smul b3
  have ht4 : MemLp t4 1 μ := by
    simpa only [t4] using hr4One.const_smul b4
  have hcore11 : MemLp core11 1 μ := by
    simpa only [core11] using ((hrOne.add hs2).add hs3).add hs4
  have hcore13 : MemLp core13 1 μ := by
    simpa only [core13] using (hr2One.add ht3).add ht4
  have henv11 : h11HigherScoreRadialEnvelope N K =
      (4096 : ℝ) • core11 := by
    funext A
    simp only [Pi.smul_apply, smul_eq_mul, core11, s2, s3, s4,
      Pi.add_apply, r2, r3, r4, a2, a3, a4, r, c,
      h11HigherScoreRadialEnvelope]
    ring
  have henv13 : h13HigherScoreRadialEnvelope N K =
      (1024 : ℝ) • core13 := by
    funext A
    simp only [Pi.smul_apply, smul_eq_mul, core13, t3, t4,
      Pi.add_apply, r2, r3, r4, b3, b4, r, c,
      h13HigherScoreRadialEnvelope]
    ring
  have henv11Mem : MemLp (h11HigherScoreRadialEnvelope N K) 1 μ := by
    rw [henv11]
    exact hcore11.const_smul 4096
  have henv13Mem : MemLp (h13HigherScoreRadialEnvelope N K) 1 μ := by
    rw [henv13]
    exact hcore13.const_smul 1024
  let L : ℝ := lpNorm r 4 μ
  have hL0 : 0 ≤ L := lpNorm_nonneg
  have hrOneNorm : lpNorm r 1 μ ≤ L := by
    simpa only [L] using
      lpNorm_le_lpNorm_of_exponent_le_probability hrFour (by norm_num)
  have hrTwoNorm : lpNorm r 2 μ ≤ L := by
    simpa only [L] using
      lpNorm_le_lpNorm_of_exponent_le_probability hrFour (by norm_num)
  have hr2TwoNorm : lpNorm r2 2 μ = L ^ 2 := by
    simpa only [r2, L] using lpNorm_sq_two_eq_sq_lpNorm_four hrFour
  have hr2OneNorm : lpNorm r2 1 μ ≤ L ^ 2 := by
    calc
      lpNorm r2 1 μ ≤ lpNorm r2 2 μ :=
        lpNorm_le_lpNorm_of_exponent_le_probability hr2Two (by norm_num)
      _ = L ^ 2 := hr2TwoNorm
  have hr3OneNorm : lpNorm r3 1 μ ≤ L ^ 3 := by
    have hmul := lpNorm_mul_le_lpNorm_two_mul hrTwo hr2Two
    have hraw : lpNorm r3 1 μ ≤ lpNorm r 2 μ * lpNorm r2 2 μ := by
      simpa only [r3, mul_comm] using hmul
    calc
      lpNorm r3 1 μ ≤ lpNorm r 2 μ * lpNorm r2 2 μ := hraw
      _ ≤ L * (L ^ 2) := by
        rw [hr2TwoNorm]
        exact mul_le_mul_of_nonneg_right hrTwoNorm (sq_nonneg L)
      _ = L ^ 3 := by ring
  have hr4OneNorm : lpNorm r4 1 μ ≤ L ^ 4 := by
    have hmul := lpNorm_mul_le_lpNorm_two_mul hr2Two hr2Two
    have hraw : lpNorm r4 1 μ ≤ lpNorm r2 2 μ * lpNorm r2 2 μ := by
      simpa only [r4] using hmul
    calc
      lpNorm r4 1 μ ≤ lpNorm r2 2 μ * lpNorm r2 2 μ := hraw
      _ = (L ^ 2) * (L ^ 2) := by rw [hr2TwoNorm]
      _ = L ^ 4 := by ring
  have hs2Norm : lpNorm s2 1 μ = a2 * lpNorm r2 1 μ := by
    dsimp only [s2]
    rw [lpNorm_const_smul]
    simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg ha2]
  have hs3Norm : lpNorm s3 1 μ = a3 * lpNorm r3 1 μ := by
    dsimp only [s3]
    rw [lpNorm_const_smul]
    simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg ha3]
  have hs4Norm : lpNorm s4 1 μ = a4 * lpNorm r4 1 μ := by
    dsimp only [s4]
    rw [lpNorm_const_smul]
    simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg ha4]
  have ht3Norm : lpNorm t3 1 μ = b3 * lpNorm r3 1 μ := by
    dsimp only [t3]
    rw [lpNorm_const_smul]
    simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hb3]
  have ht4Norm : lpNorm t4 1 μ = b4 * lpNorm r4 1 μ := by
    dsimp only [t4]
    rw [lpNorm_const_smul]
    simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hb4]
  have h12Norm : lpNorm (r + s2) 1 μ ≤
      lpNorm r 1 μ + a2 * lpNorm r2 1 μ := by
    calc
      lpNorm (r + s2) 1 μ ≤ lpNorm r 1 μ + lpNorm s2 1 μ :=
        lpNorm_add_le hrOne (g := s2) (by norm_num)
      _ = lpNorm r 1 μ + a2 * lpNorm r2 1 μ := by rw [hs2Norm]
  have h123Norm : lpNorm ((r + s2) + s3) 1 μ ≤
      (lpNorm r 1 μ + a2 * lpNorm r2 1 μ) +
        a3 * lpNorm r3 1 μ := by
    calc
      lpNorm ((r + s2) + s3) 1 μ ≤
          lpNorm (r + s2) 1 μ + lpNorm s3 1 μ :=
        lpNorm_add_le (hrOne.add hs2) (g := s3) (by norm_num)
      _ ≤ (lpNorm r 1 μ + a2 * lpNorm r2 1 μ) +
          lpNorm s3 1 μ := add_le_add h12Norm le_rfl
      _ = (lpNorm r 1 μ + a2 * lpNorm r2 1 μ) +
          a3 * lpNorm r3 1 μ := by rw [hs3Norm]
  have hcore11Norm : lpNorm core11 1 μ ≤
      ((lpNorm r 1 μ + a2 * lpNorm r2 1 μ) +
        a3 * lpNorm r3 1 μ) + a4 * lpNorm r4 1 μ := by
    calc
      lpNorm core11 1 μ = lpNorm (((r + s2) + s3) + s4) 1 μ := by rfl
      _ ≤ lpNorm ((r + s2) + s3) 1 μ + lpNorm s4 1 μ :=
        lpNorm_add_le ((hrOne.add hs2).add hs3) (g := s4) (by norm_num)
      _ ≤ ((lpNorm r 1 μ + a2 * lpNorm r2 1 μ) +
          a3 * lpNorm r3 1 μ) + lpNorm s4 1 μ :=
        add_le_add h123Norm le_rfl
      _ = ((lpNorm r 1 μ + a2 * lpNorm r2 1 μ) +
          a3 * lpNorm r3 1 μ) + a4 * lpNorm r4 1 μ := by rw [hs4Norm]
  have hcore11L : lpNorm core11 1 μ ≤
      L + a2 * L ^ 2 + a3 * L ^ 3 + a4 * L ^ 4 := by
    calc
      lpNorm core11 1 μ ≤
          ((lpNorm r 1 μ + a2 * lpNorm r2 1 μ) +
            a3 * lpNorm r3 1 μ) + a4 * lpNorm r4 1 μ := hcore11Norm
      _ ≤ ((L + a2 * L ^ 2) + a3 * L ^ 3) + a4 * L ^ 4 := by
        gcongr
  have h23Norm : lpNorm (r2 + t3) 1 μ ≤
      lpNorm r2 1 μ + b3 * lpNorm r3 1 μ := by
    calc
      lpNorm (r2 + t3) 1 μ ≤ lpNorm r2 1 μ + lpNorm t3 1 μ :=
        lpNorm_add_le hr2One (g := t3) (by norm_num)
      _ = lpNorm r2 1 μ + b3 * lpNorm r3 1 μ := by rw [ht3Norm]
  have hcore13Norm : lpNorm core13 1 μ ≤
      (lpNorm r2 1 μ + b3 * lpNorm r3 1 μ) +
        b4 * lpNorm r4 1 μ := by
    calc
      lpNorm core13 1 μ = lpNorm ((r2 + t3) + t4) 1 μ := by rfl
      _ ≤ lpNorm (r2 + t3) 1 μ + lpNorm t4 1 μ :=
        lpNorm_add_le (hr2One.add ht3) (g := t4) (by norm_num)
      _ ≤ (lpNorm r2 1 μ + b3 * lpNorm r3 1 μ) +
          lpNorm t4 1 μ := add_le_add h23Norm le_rfl
      _ = (lpNorm r2 1 μ + b3 * lpNorm r3 1 μ) +
          b4 * lpNorm r4 1 μ := by rw [ht4Norm]
  have hcore13L : lpNorm core13 1 μ ≤
      L ^ 2 + b3 * L ^ 3 + b4 * L ^ 4 := by
    calc
      lpNorm core13 1 μ ≤
          (lpNorm r2 1 μ + b3 * lpNorm r3 1 μ) +
            b4 * lpNorm r4 1 μ := hcore13Norm
      _ ≤ (L ^ 2 + b3 * L ^ 3) + b4 * L ^ 4 := by
        gcongr
  have henv11Norm : lpNorm (h11HigherScoreRadialEnvelope N K) 1 μ =
      4096 * lpNorm core11 1 μ := by
    rw [henv11, lpNorm_const_smul]
    norm_num
  have henv13Norm : lpNorm (h13HigherScoreRadialEnvelope N K) 1 μ =
      1024 * lpNorm core13 1 μ := by
    rw [henv13, lpNorm_const_smul]
    norm_num
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simpa only [μ] using henv11Mem
  · intro hdense
    have hLdense : L ≤ 4096 * (N : ℝ) := by
      simpa only [L, r, μ] using H.lpNorm_four_le hdense
    have hc : (N : ℝ) ≤ c := by
      simpa only [c] using concreteCOEExponent_ge_dimension_of_dense hN hdense
    change lpNorm (h11HigherScoreRadialEnvelope N K) 1 μ ≤ _
    rw [henv11Norm]
    calc
      4096 * lpNorm core11 1 μ ≤
          4096 * (L + a2 * L ^ 2 + a3 * L ^ 3 + a4 * L ^ 4) :=
        mul_le_mul_of_nonneg_left hcore11L (by norm_num)
      _ ≤ centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 := by
        simpa only [a2, a3, a4, c] using
          h11HigherScore_radial_numeric
            (n := (N : ℝ)) (c := c) (L := L)
            (by exact_mod_cast hN) hc hL0 hLdense
  · simpa only [μ] using henv13Mem
  · intro hdense
    have hLdense : L ≤ 4096 * (N : ℝ) := by
      simpa only [L, r, μ] using H.lpNorm_four_le hdense
    have hc : (N : ℝ) ≤ c := by
      simpa only [c] using concreteCOEExponent_ge_dimension_of_dense hN hdense
    change lpNorm (h13HigherScoreRadialEnvelope N K) 1 μ ≤ _
    rw [henv13Norm]
    calc
      1024 * lpNorm core13 1 μ ≤
          1024 * (L ^ 2 + b3 * L ^ 3 + b4 * L ^ 4) :=
        mul_le_mul_of_nonneg_left hcore13L (by norm_num)
      _ ≤ centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 := by
        simpa only [b3, b4, c] using
          h13HigherScore_radial_numeric
            (n := (N : ℝ)) (c := c) (L := L)
            (by exact_mod_cast hN) hc hL0 hLdense

/-- Generic product-law integration step used independently by H11 and H13. -/
private theorem higherScoreEndpoint_momentPackage_of_radialEnvelope
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (f : ConcreteMatrixState N × ComplexUnitSphere N → ℝ)
    (envelope : ConcreteMatrixState N → ℝ)
    (hfMeas : Measurable f)
    (henvNonneg : ∀ A, 0 ≤ envelope A)
    (hSupport : ∀ᵐ A ∂(higherScoreMatrixLaw N K),
      (unscaleCOECorner K A).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K A))
    (hpoint : ∀ (A : ConcreteMatrixState N) (v : ComplexUnitSphere N),
      (unscaleCOECorner K A).IsSymm →
      coeCornerSupport (unscaleCOECorner K A) →
      |f (A, v)| ≤ envelope A)
    (hEnvelope :
      MemLp envelope 1 (higherScoreMatrixLaw N K) ∧
        (16 * N ≤ K →
          lpNorm envelope 1 (higherScoreMatrixLaw N K) ≤
            centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2)) :
    MemLp f 1 (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm f 1 (concreteCenteredScoreProductLaw N K) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) := by
  let μ : Measure (ConcreteMatrixState N) := higherScoreMatrixLaw N K
  let sphere : Measure (ComplexUnitSphere N) := higherScoreSphereLaw N
  letI : IsProbabilityMeasure μ :=
    canonicalScaledCOECornerLaw_isProbability (by omega)
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hfStrong : AEStronglyMeasurable f (μ.prod sphere) := by
    simpa only [μ, sphere, higherScoreSphereLaw] using
      hfMeas.aestronglyMeasurable
  have hSlices : ∀ᵐ A ∂μ,
      Integrable (fun v ↦ f (A, v)) sphere ∧
        (∫ v, ‖f (A, v)‖ ∂sphere) ≤ envelope A := by
    filter_upwards [show ∀ᵐ A ∂μ,
        (unscaleCOECorner K A).IsSymm ∧
          coeCornerSupport (unscaleCOECorner K A) by
      simpa only [μ] using hSupport] with A hA
    have hsliceMeas : AEStronglyMeasurable (fun v ↦ f (A, v)) sphere := by
      have hpair : Measurable (fun v : ComplexUnitSphere N ↦ (A, v)) := by
        fun_prop
      exact (hfMeas.comp hpair).aestronglyMeasurable
    have hsliceInt : Integrable (fun v ↦ f (A, v)) sphere := by
      apply (integrable_const (envelope A)).mono hsliceMeas
      filter_upwards [] with v
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (henvNonneg A)]
      exact hpoint A v hA.1 hA.2
    constructor
    · exact hsliceInt
    · calc
        (∫ v, ‖f (A, v)‖ ∂sphere) ≤
            ∫ _v : ComplexUnitSphere N, envelope A ∂sphere := by
          apply integral_mono hsliceInt.norm (integrable_const _)
          intro v
          change ‖f (A, v)‖ ≤ envelope A
          simpa only [Real.norm_eq_abs] using hpoint A v hA.1 hA.2
        _ = envelope A := by simp
  have hEnvelopeMem : MemLp envelope 1 μ := by
    simpa only [μ] using hEnvelope.1
  have hEnvelopeInt : Integrable envelope μ :=
    memLp_one_iff_integrable.mp hEnvelopeMem
  have hInnerMeas : AEStronglyMeasurable
      (fun A ↦ ∫ v, ‖f (A, v)‖ ∂sphere) μ :=
    hfStrong.norm.integral_prod_right'
  have hInnerInt : Integrable
      (fun A ↦ ∫ v, ‖f (A, v)‖ ∂sphere) μ := by
    apply hEnvelopeInt.mono hInnerMeas
    filter_upwards [hSlices] with A hA
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (henvNonneg A)]
    exact hA.2
  have hfInt : Integrable f (μ.prod sphere) := by
    apply (integrable_prod_iff hfStrong).2
    exact ⟨hSlices.mono fun _ hA ↦ hA.1, hInnerInt⟩
  have hEnvelopeNormEq :
      lpNorm envelope 1 μ = ∫ A, envelope A ∂μ := by
    rw [lpNorm_one_eq_integral_norm hEnvelopeMem.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [] with A
    rw [Real.norm_eq_abs, abs_of_nonneg (henvNonneg A)]
  constructor
  · change MemLp f 1 (μ.prod sphere)
    exact memLp_one_iff_integrable.mpr hfInt
  · intro hdense
    change lpNorm f 1 (μ.prod sphere) ≤ _
    calc
      lpNorm f 1 (μ.prod sphere) =
          ∫ A, ∫ v, ‖f (A, v)‖ ∂sphere ∂μ := by
        rw [lpNorm_one_eq_integral_norm hfStrong]
        exact integral_prod (fun p ↦ ‖f p‖) hfInt.norm
      _ ≤ ∫ A, envelope A ∂μ := by
        apply integral_mono_ae hInnerInt hEnvelopeInt
        filter_upwards [hSlices] with A hA
        exact hA.2
      _ = lpNorm envelope 1 μ := hEnvelopeNormEq.symm
      _ ≤ centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 := by
        simpa only [μ] using hEnvelope.2 hdense

/-- Exact H11 reducer.  It does not mention H13 or its deterministic
contract.  Approved A1 supplies the almost-everywhere support statement. -/
theorem centeredLogScore_four_momentPackage_of_opRadiusL4_and_deterministic
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (Hradius : ConcreteHigherScoreOpRadiusL4Package N K)
    (Hdet : H11HigherScoreDeterministicEnvelope N K) :
    MemLp (concreteCenteredEll 4 N K) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (concreteCenteredEll 4 N K) 1
            (concreteCenteredScoreProductLaw N K) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) := by
  have hSupport : ∀ᵐ A ∂(higherScoreMatrixLaw N K),
      (unscaleCOECorner K A).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K A) :=
    friedmanMello1985_scaledCOECorner_ae_support_from_density
      hN (by omega : 2 * N ≤ K)
  have hRadial :=
    (h11H13HigherScoreRadial_momentPackages_of_opRadiusL4
      hN hgap Hradius).1
  exact higherScoreEndpoint_momentPackage_of_radialEnvelope
    hN hgap (concreteCenteredEll 4 N K)
    (h11HigherScoreRadialEnvelope N K)
    Hdet.measurable_score
    (h11HigherScoreRadialEnvelope_nonneg hgap)
    hSupport Hdet.abs_le_on_support hRadial

/-- Exact H13 reducer, independent of H11. -/
theorem centeredLogScore_oneThree_momentPackage_of_opRadiusL4_and_deterministic
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (Hradius : ConcreteHigherScoreOpRadiusL4Package N K)
    (Hdet : H13HigherScoreDeterministicEnvelope N K) :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p *
      concreteCenteredEll 3 N K p) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 1 N K p *
          concreteCenteredEll 3 N K p) 1
            (concreteCenteredScoreProductLaw N K) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) := by
  have hSupport : ∀ᵐ A ∂(higherScoreMatrixLaw N K),
      (unscaleCOECorner K A).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K A) :=
    friedmanMello1985_scaledCOECorner_ae_support_from_density
      hN (by omega : 2 * N ≤ K)
  have hRadial :=
    (h11H13HigherScoreRadial_momentPackages_of_opRadiusL4
      hN hgap Hradius).2
  exact higherScoreEndpoint_momentPackage_of_radialEnvelope
    hN hgap
    (fun p ↦ concreteCenteredEll 1 N K p * concreteCenteredEll 3 N K p)
    (h13HigherScoreRadialEnvelope N K)
    Hdet.measurable_scoreProduct
    (h13HigherScoreRadialEnvelope_nonneg hgap)
    hSupport Hdet.abs_le_on_support hRadial

/-! ## Exact dimension-one endpoints -/

theorem centeredLogScore_four_momentPackage_fin_one_internal
    {K : ℕ} (_hgap : 2 * 1 + 8 ≤ K) :
    MemLp (concreteCenteredEll 4 1 K) 1
        (concreteCenteredScoreProductLaw 1 K) ∧
      (16 * 1 ≤ K →
        lpNorm (concreteCenteredEll 4 1 K) 1
            (concreteCenteredScoreProductLaw 1 K) ≤
          centeredLogScoreFourthMomentConstant * (1 : ℝ) ^ 2) := by
  have hzero : concreteCenteredEll 4 1 K = 0 := by
    funext p
    exact concreteCenteredLogScore_fin_one_eq_zero (by omega) p.2 p.1
  rw [hzero]
  constructor
  · exact MemLp.zero'
  · intro _
    rw [lpNorm_zero]
    norm_num [centeredLogScoreFourthMomentConstant,
      denseClassicalMomentConstant]

theorem centeredLogScore_oneThree_momentPackage_fin_one_internal
    {K : ℕ} (_hgap : 2 * 1 + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 1 1 K p *
      concreteCenteredEll 3 1 K p) 1
        (concreteCenteredScoreProductLaw 1 K) ∧
      (16 * 1 ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 1 1 K p *
          concreteCenteredEll 3 1 K p) 1
            (concreteCenteredScoreProductLaw 1 K) ≤
          centeredLogScoreFourthMomentConstant * (1 : ℝ) ^ 2) := by
  have hzero : (fun p ↦ concreteCenteredEll 1 1 K p *
      concreteCenteredEll 3 1 K p) = 0 := by
    funext p
    rw [show concreteCenteredEll 1 1 K p = 0 by
      exact concreteCenteredLogScore_fin_one_eq_zero (by omega) p.2 p.1]
    simp
  rw [hzero]
  constructor
  · exact MemLp.zero'
  · intro _
    rw [lpNorm_zero]
    norm_num [centeredLogScoreFourthMomentConstant,
      denseClassicalMomentConstant]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

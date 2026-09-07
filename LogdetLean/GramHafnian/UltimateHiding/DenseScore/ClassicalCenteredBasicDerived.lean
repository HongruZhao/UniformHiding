import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalCenteredMatrixMomentExternal
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.MixedScalarQuadraticClosure
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H9MomentRewire

/-!
# Internally derived basic centered trace moments

The square and cube of the centered first trace are not independent
random-matrix inputs.  They follow directly from the already exposed
centered `L^2` and `L^3` bounds by Holder.  This module records those
consequences so downstream score calculations need not use the corresponding
redundant declarations from `ClassicalCenteredMatrixMomentExternal`.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

private theorem lpNorm_mul_le_of_holder
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {p q s : ENNReal} {f g : Omega → ℝ}
    (hf : MemLp f q mu) (hg : MemLp g p mu)
    [hpqs : ENNReal.HolderTriple p q s] :
    lpNorm (fun omega ↦ g omega * f omega) s mu ≤
      lpNorm g p mu * lpNorm f q mu := by
  have hprod : MemLp (fun omega ↦ g omega * f omega) s mu := hf.mul' hg
  have he : eLpNorm (fun omega ↦ g omega * f omega) s mu ≤
      eLpNorm g p mu * eLpNorm f q mu := by
    simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (p := p) (q := q) (r := s)
      hg.aestronglyMeasurable hf.aestronglyMeasurable
      (fun x y : ℝ ↦ x * y) 1 (by
        filter_upwards [] with omega
        simp [nnnorm_mul])
  rw [← toReal_eLpNorm hprod.aestronglyMeasurable,
    ← toReal_eLpNorm hg.aestronglyMeasurable,
    ← toReal_eLpNorm hf.aestronglyMeasurable,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top hg.eLpNorm_ne_top hf.eLpNorm_ne_top) he

private theorem centeredTraceOne_eq_integral_centered
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    betaPrimeCenteredMatrixTraceOne N K = fun u ↦
      betaPrimeYTraceOne N K u -
        ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K) := by
  funext u
  rw [betaPrimeYTraceOne_integral_external hN (by omega : 2 * N + 2 ≤ K)]
  rfl

/-- The centered first-trace square is `L^1`, internally from its `L^2`
bound. -/
theorem betaPrimeCenteredMatrixTraceOneSquare_memLp_one_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun u ↦ betaPrimeCenteredMatrixTraceOne N K u ^ 2) 1
      (betaPrimeTraceFourLaw N K) := by
  let f : (Fin 4 → ℝ) → ℝ := fun u ↦
    betaPrimeYTraceOne N K u -
      ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)
  have hf : MemLp f 2 (betaPrimeTraceFourLaw N K) := by
    simpa only [f] using
      betaPrimeYTraceOne_centered_memLp_two_proved_allDimensions hN hgap
  have hmul : MemLp (fun u ↦ f u * f u) 1
      (betaPrimeTraceFourLaw N K) := hf.mul' hf
  rw [centeredTraceOne_eq_integral_centered hN hgap]
  simpa only [pow_two] using hmul

/-- The centered first-trace square has the square of the centered `L^2`
bound. -/
theorem betaPrimeCenteredMatrixTraceOneSquare_lpNorm_one_le_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun u ↦ betaPrimeCenteredMatrixTraceOne N K u ^ 2) 1
        (betaPrimeTraceFourLaw N K) ≤
      denseClassicalMomentConstant ^ 2 * (N : ℝ) ^ 2 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let f : (Fin 4 → ℝ) → ℝ := fun u ↦
    betaPrimeYTraceOne N K u -
      ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)
  have hf : MemLp f 2 (betaPrimeTraceFourLaw N K) := by
    simpa only [f] using
      betaPrimeYTraceOne_centered_memLp_two_proved_allDimensions hN hgap
  have hfnorm : lpNorm f 2 (betaPrimeTraceFourLaw N K) ≤
      denseClassicalMomentConstant * (N : ℝ) := by
    simpa only [f] using
      betaPrimeYTraceOne_centered_lpNorm_two_le_proved_allDimensions hN hdense
  rw [centeredTraceOne_eq_integral_centered hN hgap]
  change lpNorm (fun u ↦ f u ^ 2) 1 (betaPrimeTraceFourLaw N K) ≤ _
  calc
    lpNorm (fun u ↦ f u ^ 2) 1 (betaPrimeTraceFourLaw N K) =
        lpNorm (fun u ↦ f u * f u) 1 (betaPrimeTraceFourLaw N K) := by
          congr 1
          funext u
          ring
    _ ≤ lpNorm f 2 (betaPrimeTraceFourLaw N K) *
        lpNorm f 2 (betaPrimeTraceFourLaw N K) :=
      lpNorm_mul_le_lpNorm_two_mul hf hf
    _ ≤ (denseClassicalMomentConstant * (N : ℝ)) *
        (denseClassicalMomentConstant * (N : ℝ)) := by
      exact mul_le_mul hfnorm hfnorm lpNorm_nonneg
        (mul_nonneg (by norm_num [denseClassicalMomentConstant])
          (by exact_mod_cast (Nat.zero_le N)))
    _ = denseClassicalMomentConstant ^ 2 * (N : ℝ) ^ 2 := by ring

/-- The centered first-trace cube is `L^1`, internally from its `L^3`
bound. -/
theorem betaPrimeCenteredMatrixTraceOneCube_memLp_one_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun u ↦ betaPrimeCenteredMatrixTraceOne N K u ^ 3) 1
      (betaPrimeTraceFourLaw N K) := by
  let f : (Fin 4 → ℝ) → ℝ := fun u ↦
    betaPrimeYTraceOne N K u -
      ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)
  have hf : MemLp f 3 (betaPrimeTraceFourLaw N K) := by
    simpa only [f] using
      betaPrimeYTraceOne_centered_memLp_three_proved_allDimensions hN hgap
  let p32 : ENNReal := ((3 / 2 : NNReal) : ENNReal)
  letI : ENNReal.HolderTriple 3 3 p32 := by
    have h : NNReal.HolderTriple 3 3 (3 / 2) := by
      rw [NNReal.holderTriple_iff]
      norm_num
    change ENNReal.HolderTriple
      ((3 : NNReal) : ENNReal) ((3 : NNReal) : ENNReal)
        ((3 / 2 : NNReal) : ENNReal)
    exact h.coe_ennreal (by norm_num)
  have hsq : MemLp (fun u ↦ f u * f u) p32
      (betaPrimeTraceFourLaw N K) := hf.mul' hf
  letI : ENNReal.HolderTriple p32 3 1 := by
    have h : NNReal.HolderTriple (3 / 2) 3 1 := by
      rw [NNReal.holderTriple_iff]
      norm_num
    change ENNReal.HolderTriple
      ((3 / 2 : NNReal) : ENNReal) ((3 : NNReal) : ENNReal)
        ((1 : NNReal) : ENNReal)
    exact h.coe_ennreal (by norm_num)
  have hcube : MemLp (fun u ↦ (f u * f u) * f u) 1
      (betaPrimeTraceFourLaw N K) := hf.mul' hsq
  rw [centeredTraceOne_eq_integral_centered hN hgap]
  convert hcube using 1
  funext u
  ring

/-- The centered first-trace cube has the cube of the centered `L^3`
bound. -/
theorem betaPrimeCenteredMatrixTraceOneCube_lpNorm_one_le_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun u ↦ betaPrimeCenteredMatrixTraceOne N K u ^ 3) 1
        (betaPrimeTraceFourLaw N K) ≤
      denseClassicalMomentConstant ^ 3 * (N : ℝ) ^ 3 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let mu := betaPrimeTraceFourLaw N K
  let f : (Fin 4 → ℝ) → ℝ := fun u ↦
    betaPrimeYTraceOne N K u -
      ∫ z, betaPrimeYTraceOne N K z ∂mu
  have hf : MemLp f 3 mu := by
    simpa only [f, mu] using
      betaPrimeYTraceOne_centered_memLp_three_proved_allDimensions hN hgap
  have hfnorm : lpNorm f 3 mu ≤
      denseClassicalMomentConstant * (N : ℝ) := by
    simpa only [f, mu] using
      betaPrimeYTraceOne_centered_lpNorm_three_le_proved_allDimensions hN hdense
  let p32 : ENNReal := ((3 / 2 : NNReal) : ENNReal)
  letI : ENNReal.HolderTriple 3 3 p32 := by
    have h : NNReal.HolderTriple 3 3 (3 / 2) := by
      rw [NNReal.holderTriple_iff]
      norm_num
    change ENNReal.HolderTriple
      ((3 : NNReal) : ENNReal) ((3 : NNReal) : ENNReal)
        ((3 / 2 : NNReal) : ENNReal)
    exact h.coe_ennreal (by norm_num)
  have hsq : MemLp (fun u ↦ f u * f u) p32 mu := hf.mul' hf
  have hsqNorm : lpNorm (fun u ↦ f u * f u) p32 mu ≤
      lpNorm f 3 mu * lpNorm f 3 mu :=
    lpNorm_mul_le_of_holder hf hf
  letI : ENNReal.HolderTriple p32 3 1 := by
    have h : NNReal.HolderTriple (3 / 2) 3 1 := by
      rw [NNReal.holderTriple_iff]
      norm_num
    change ENNReal.HolderTriple
      ((3 / 2 : NNReal) : ENNReal) ((3 : NNReal) : ENNReal)
        ((1 : NNReal) : ENNReal)
    exact h.coe_ennreal (by norm_num)
  rw [centeredTraceOne_eq_integral_centered hN hgap]
  change lpNorm (fun u ↦ f u ^ 3) 1 mu ≤ _
  calc
    lpNorm (fun u ↦ f u ^ 3) 1 mu =
        lpNorm (fun u ↦ (f u * f u) * f u) 1 mu := by
          congr 1
          funext u
          ring
    _ ≤ lpNorm (fun u ↦ f u * f u) p32 mu *
        lpNorm f 3 mu := lpNorm_mul_le_of_holder hf hsq
    _ ≤ (lpNorm f 3 mu * lpNorm f 3 mu) * lpNorm f 3 mu := by
      exact mul_le_mul_of_nonneg_right hsqNorm lpNorm_nonneg
    _ ≤ ((denseClassicalMomentConstant * (N : ℝ)) *
          (denseClassicalMomentConstant * (N : ℝ))) *
        (denseClassicalMomentConstant * (N : ℝ)) := by
      have hnonneg : 0 ≤ denseClassicalMomentConstant * (N : ℝ) :=
        mul_nonneg (by norm_num [denseClassicalMomentConstant])
          (by exact_mod_cast (Nat.zero_le N))
      exact mul_le_mul
        (mul_le_mul hfnorm hfnorm lpNorm_nonneg hnonneg)
        hfnorm lpNorm_nonneg
        (mul_nonneg hnonneg hnonneg)
    _ = denseClassicalMomentConstant ^ 3 * (N : ℝ) ^ 3 := by ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

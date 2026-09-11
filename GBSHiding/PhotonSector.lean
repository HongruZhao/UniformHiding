import GBSHiding.PhotonPairLaw
import Mathlib.Data.Nat.Factorial.BigOperators

/-! Proposition 4.1: optical sector identification and the exact reference scale. -/
open scoped BigOperators
open MeasureTheory Set Real
open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy

namespace GBSHiding
noncomputable section
set_option maxHeartbeats 2000000

def sectorWeight (K n : ℕ) (r : ℝ) : ℝ :=
  pairCoefficient ((K:ℝ)/2) n * equalSqueezingOpticalPrefactor r (2*n) K

theorem dimensionProduct_half_shape (K n : ℕ) :
    dimensionProduct K n = 2^n * (∏ j ∈ Finset.range n, ((K:ℝ)/2+j)) := by
  unfold dimensionProduct
  calc
    _ = ∏ j ∈ Finset.range n, 2 * ((K:ℝ)/2+j) := by
      apply Finset.prod_congr rfl
      intro j _
      push_cast
      ring
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

/-- The factor identifying the photon sector is proved, not supplied as
the old `hTotalPhoton` hypothesis. -/
theorem sigma_sq_div_factorial_eq_pairCoefficient (K n : ℕ) (hK : 0 < K) :
    gramHafnianSigma K n ^ 2 / ((2*n).factorial : ℝ) = pairCoefficient ((K:ℝ)/2) n := by
  rw [gramHafnianSigma_sq K n hK, closedFirstMoment,
    dimensionProduct_half_shape, pairCoefficient_eq_product]
  have hfac : ((2*n).factorial : ℝ) =
      2^n * (n.factorial:ℝ) * (oddPairingNat n : ℝ) := by
    exact_mod_cast factorial_two_mul_eq_even_mul_odd n
  rw [hfac]
  have ho : (oddPairingNat n : ℝ) ≠ 0 := by exact_mod_cast (oddPairingNat_pos n).ne'
  field_simp
  <;> ring

theorem sectorWeight_eq_optical_secondMoment (K n : ℕ) (hK : 0 < K) (r : ℝ) :
    sectorWeight K n r = equalSqueezingOpticalPrefactor r (2*n) K *
      gramHafnianSigma K n ^ 2 / ((2*n).factorial : ℝ) := by
  rw [mul_div_assoc, sigma_sq_div_factorial_eq_pairCoefficient K n hK]
  exact mul_comm _ _

def finitePopulationFactor (M N : ℕ) : ℝ :=
  ∏ j ∈ Finset.range N, (1-(j:ℝ)/M)

theorem finitePopulationFactor_eq_descFactorial (M N : ℕ) (hNM : N ≤ M) (hM : 0 < M) :
    finitePopulationFactor M N = (M.descFactorial N : ℝ) / (M:ℝ)^N := by
  have hm : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [Nat.descFactorial_eq_prod_range]
  push_cast
  unfold finitePopulationFactor
  have hprod : (∏ j ∈ Finset.range N, (1-(j:ℝ)/M)) =
      ∏ j ∈ Finset.range N, ((M-j : ℕ):ℝ)/(M:ℝ) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hjM : j ≤ M := by have := Finset.mem_range.mp hj; omega
    rw [Nat.cast_sub hjM]
    field_simp
  rw [hprod, Finset.prod_div_distrib]
  simp

/-- Exact displayed identity in Proposition 4.1. -/
theorem proposition4_1_reference_scale (M K n : ℕ) (hM : 0 < M)
    (hNM : 2*n ≤ M) (hK : 0 < K) (r : ℝ) :
    (Nat.choose M (2*n):ℝ) * gbsGaussianReferenceProbability r M K n =
      sectorWeight K n r * finitePopulationFactor M (2*n) := by
  have h := sectorReferenceMass r hM (sectorWeight K n r)
    (sectorWeight_eq_optical_secondMoment K n hK r)
  rw [finitePopulationFactor_eq_descFactorial M (2*n) hNM hM]
  simpa [mul_comm] using h

theorem one_sub_tanh_sq (r : ℝ) :
    1 - Real.tanh r ^ 2 = 1 / Real.cosh r ^ 2 := by
  rw [Real.tanh_eq_sinh_div_cosh, div_pow]
  have hc := (Real.cosh_pos r).ne'
  have hid := Real.cosh_sq_sub_sinh_sq r
  field_simp
  linarith

theorem squeezing_rpow_identity (K : ℕ) (r : ℝ) :
    (1-Real.tanh r^2)^((K:ℝ)/2) = 1 / Real.cosh r^K := by
  have hp : (Real.cosh r ^ 2)^((K:ℝ)/2) = Real.cosh r^K := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (Real.cosh_pos r).le]
    convert Real.rpow_natCast (Real.cosh r) K using 1
    congr 1
    norm_num
    <;> ring
  rw [one_sub_tanh_sq, Real.div_rpow zero_le_one (sq_nonneg _), Real.one_rpow, hp]

theorem sectorWeight_eq_pairMass (K n : ℕ) (r : ℝ) :
    sectorWeight K n r = pairMass ((K:ℝ)/2) (Real.tanh r^2) n := by
  unfold sectorWeight pairMass equalSqueezingOpticalPrefactor
  rw [squeezing_rpow_identity, ← pow_mul]
  ring

/-- The K-mode independent input law gives exactly the paper's W(K,n,r).
The photon count itself is twice this pair count. -/
theorem squeezedInputPairCount_sector_mass (K n : ℕ) (r : ℝ) :
    (squeezedInputPairCount (Real.tanh r^2)
      ⟨sq_nonneg _, Real.tanh_sq_lt_one r⟩ K n).toReal = sectorWeight K n r := by
  have hx : Real.tanh r^2 ∈ Ico 0 1 := ⟨sq_nonneg _, Real.tanh_sq_lt_one r⟩
  have h := congrArg (fun p : PMF ℕ ↦ (p n).toReal)
    (squeezedInputPairCount_eq (Real.tanh r^2) hx K)
  exact h.trans ((photonPairPMF_mass _ _ _ hx n).trans (sectorWeight_eq_pairMass K n r).symm)

/-- The ascending product equals the Gamma quotient, with its hypotheses
discharged for every positive shape. -/
theorem pairCoefficient_eq_gamma {a : ℝ} (ha : 0 < a) (n : ℕ) :
    pairCoefficient a n = Real.Gamma (a+n) / (Real.Gamma a * Real.Gamma (n+1)) := by
  have hg : Real.Gamma (a+n) = Real.Gamma a * ∏ j ∈ Finset.range n, (a+j) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, ← add_assoc,
        Real.Gamma_add_one (by positivity : a+(n:ℝ) ≠ 0), ih, Finset.prod_range_succ]
      ring
  rw [pairCoefficient_eq_product, hg, Real.Gamma_nat_eq_factorial]
  have hga := (Real.Gamma_pos_of_pos ha).ne'
  field_simp

end
end GBSHiding

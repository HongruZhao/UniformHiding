import GBSHiding.PassivePhotonNumber

/-! Squeezed-input number law and its preservation by passive optics.
The single-mode squeezed-vacuum coefficients are the optical model.
Normalization, convolution, generating functions, and sector transport
are proved below. Conditional states inside each number sector may be
arbitrary normalized bosonic vectors: they cannot change the number law. -/
open scoped BigOperators Matrix
open MeasureTheory Set Real
open LogdetLean.GramHafnian

namespace GBSHiding
noncomputable section
set_option maxHeartbeats 1600000

theorem pairCoefficient_half (n : ℕ) :
    pairCoefficient (1/2) n = (Nat.choose (2*n) n : ℝ) / (4:ℝ)^n := by
  have hp : (∏ j ∈ Finset.range n, ((1:ℝ)/2+j)) =
      (oddPairingNat n:ℝ)/(2:ℝ)^n := by
    have h := dimensionProduct_half_shape 1 n
    have he : dimensionProduct 1 n = (oddPairingNat n:ℝ) := by
      simp [dimensionProduct, oddPairingNat, add_comm]
    rw [he] at h
    norm_num only [Nat.cast_one] at h
    apply (eq_div_iff (by positivity : (2:ℝ)^n ≠ 0)).mpr
    simpa [mul_comm] using h.symm
  rw [pairCoefficient_eq_product, hp]
  have hfac : ((2*n).factorial:ℝ) = (2:ℝ)^n*(n.factorial:ℝ)*(oddPairingNat n:ℝ) := by
    exact_mod_cast factorial_two_mul_eq_even_mul_odd n
  have hc : (Nat.choose (2*n) n:ℝ)*(n.factorial:ℝ)*(n.factorial:ℝ) = ((2*n).factorial:ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2*n by omega)
    simpa [show 2*n-n=n by omega] using congrArg (fun x : ℕ ↦ (x:ℝ)) h
  rw [hfac] at hc
  have hc' : (Nat.choose (2*n) n:ℝ)*(n.factorial:ℝ) = (2:ℝ)^n*(oddPairingNat n:ℝ) := by
    apply mul_right_cancel₀ (by positivity : (n.factorial:ℝ) ≠ 0)
    nlinarith [hc]
  have h4 : (4:ℝ)^n = (2:ℝ)^n*(2:ℝ)^n := by rw [← mul_pow]; norm_num
  rw [h4]
  field_simp
  nlinarith [hc']

/-- The standard single squeezed-mode pair weights, explicitly normalized
by `photonPairPMF`. -/
theorem singleMode_pair_mass (r : ℝ) (n : ℕ) :
    pairMass (1/2) (Real.tanh r^2) n =
      (Nat.choose (2*n) n:ℝ)/(4:ℝ)^n * Real.tanh r^(2*n) / Real.cosh r := by
  unfold pairMass
  rw [pairCoefficient_half, show (1-Real.tanh r^2)^((1:ℝ)/2) = 1/Real.cosh r by
    simpa using squeezing_rpow_identity 1 r]
  rw [← pow_mul]
  ring

/-- The generating function in the manuscript, with an explicit convergence
domain. -/
theorem squeezedInputPairCount_generatingFunction (K : ℕ) (r z : ℝ)
    (hz : |Real.tanh r^2*z| < 1) :
    HasSum (fun n ↦
      (squeezedInputPairCount (Real.tanh r^2)
        ⟨sq_nonneg _, Real.tanh_sq_lt_one r⟩ K n).toReal * z^n)
      ((1-Real.tanh r^2*z)^(-((K:ℝ)/2)) / Real.cosh r^K) := by
  have h := (pairCoefficient_hasSum ((K:ℝ)/2) hz).mul_right (1/Real.cosh r^K)
  have hx : 0 ≤ 1-Real.tanh r^2*z := by have := (abs_lt.mp hz).2; linarith
  have heq (n : ℕ) :
      (squeezedInputPairCount (Real.tanh r^2)
        ⟨sq_nonneg _, Real.tanh_sq_lt_one r⟩ K n).toReal * z^n =
      pairCoefficient ((K:ℝ)/2) n * (Real.tanh r^2*z)^n * (1/Real.cosh r^K) := by
    calc
      _ = sectorWeight K n r * z^n :=
        congrArg (fun w : ℝ ↦ w*z^n) (squeezedInputPairCount_sector_mass K n r)
      _ = _ := by
        rw [sectorWeight_eq_pairMass]
        unfold pairMass
        rw [squeezing_rpow_identity, mul_pow]
        ring
  have hs : (1-Real.tanh r^2*z)^(-((K:ℝ)/2)) / Real.cosh r^K =
      1/(1-Real.tanh r^2*z)^((K:ℝ)/2) * (1/Real.cosh r^K) := by
    rw [Real.rpow_neg hx]
    ring
  rw [hs]
  exact h.congr_fun heq

def squeezedInputPhotonCount (K : ℕ) (r : ℝ) : PMF ℕ :=
  (squeezedInputPairCount (Real.tanh r^2)
    ⟨sq_nonneg _, Real.tanh_sq_lt_one r⟩ K).map (fun n ↦ 2*n)

theorem squeezedInputPhotonCount_even (K n : ℕ) (r : ℝ) :
    (squeezedInputPhotonCount K r (2*n)).toReal = sectorWeight K n r := by
  have hp : squeezedInputPhotonCount K r (2*n) =
      squeezedInputPairCount (Real.tanh r^2) ⟨sq_nonneg _, Real.tanh_sq_lt_one r⟩ K n := by
    simp [squeezedInputPhotonCount, PMF.map_apply, Nat.mul_right_inj (show 2 ≠ 0 by omega)]
  rw [hp, squeezedInputPairCount_sector_mass]

theorem squeezedInputPhotonCount_odd (K n : ℕ) (r : ℝ) :
    squeezedInputPhotonCount K r (2*n+1) = 0 := by
  simp only [squeezedInputPhotonCount, PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro j
  rw [if_neg (by omega)]

theorem photonSectorMass_smul {M N : ℕ} (c : ℂ) (v : PhotonConfiguration M N → ℂ) :
    photonSectorMass (fun i ↦ c * v i) = Complex.normSq c * photonSectorMass v := by
  simp [photonSectorMass, map_mul, Finset.mul_sum]

/-- A conditional state carries no sector probability: it has mass one. -/
def BosonicUnitSector (M N : ℕ) :=
  {v : PhotonConfiguration M N → ℂ // IsBosonicSector v ∧ photonSectorMass v = 1}

/-- The sector amplitudes are weighted by the independently derived input
pair-count law. This definition contains no supplied total-photon formula. -/
def squeezedSectorVector {M : ℕ} (K n : ℕ) (r : ℝ)
    (v : BosonicUnitSector M (2*n)) : PhotonConfiguration M (2*n) → ℂ :=
  fun i ↦ (Real.sqrt ((squeezedInputPairCount (Real.tanh r^2)
    ⟨sq_nonneg _, Real.tanh_sq_lt_one r⟩ K n).toReal) : ℂ) * v.val i

/-- Physical sector identification for the adopted squeezed-input and
passive-optics model, uniformly over all normalized conditional sector
states. Neither hTotalPhoton nor number preservation is assumed. -/
theorem proposition4_1_output_sector_probability {M : ℕ}
    (U : Matrix.unitaryGroup (Fin M) ℂ) (K n : ℕ) (r : ℝ)
    (v : BosonicUnitSector M (2*n)) :
    photonSectorMass (photonTensorMatrix U (2*n) *ᵥ squeezedSectorVector K n r v) =
      sectorWeight K n r := by
  rw [passiveOptics_preserves_photonSector]
  unfold squeezedSectorVector
  rw [photonSectorMass_smul, v.property.2, mul_one]
  simp only [Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt ENNReal.toReal_nonneg]
  exact squeezedInputPairCount_sector_mass K n r

end
end GBSHiding

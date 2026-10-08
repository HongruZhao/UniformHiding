import A3.HermitianOrbitChartDerivative
import A3.HermitianSpectrum
import A3.FlagStabilizer

open scoped BigOperators Matrix Matrix.Norms.Elementwise
open Set

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]

theorem hermitianOrbitMatrix_charpoly (U : Matrix.unitaryGroup (Fin n) K)
    (lambda : Fin n → ℝ) :
    (hermitianOrbitMatrix U lambda).charpoly = realRootPolynomial lambda := by
  unfold hermitianOrbitMatrix
  rw [← Matrix.star_eq_conjTranspose, charpoly_unitary_conjugation, Matrix.charpoly_diagonal]
  rfl

theorem hermitianOrbitCoordinates_eq_spectrum_permutation
    (U V : Matrix.unitaryGroup (Fin n) K) (lambda mu : Fin n → ℝ)
    (h : hermitianOrbitCoordinates U lambda = hermitianOrbitCoordinates V mu) :
    ∃ sigma : Equiv.Perm (Fin n), lambda = mu ∘ sigma := by
  have hm := congrArg hermitianMatrixOfCoordinates h
  rw [hermitianOrbitCoordinates_reconstruct, hermitianOrbitCoordinates_reconstruct] at hm
  have hp := congrArg Matrix.charpoly hm
  rw [hermitianOrbitMatrix_charpoly, hermitianOrbitMatrix_charpoly] at hp
  have hr := congrArg (fun p : Polynomial K ↦ p.roots.map RCLike.re) hp
  rw [realRootPolynomial_roots_re, realRootPolynomial_roots_re] at hr
  exact exists_perm_of_multiset_map_univ_eq hr

def flagCoordinateEvaluation (mu : Fin n → ℝ) (P : flagSpace n K) :
    HermitianCoordinates n K := hermitianCoordinateProjection (flagEvaluation mu P)

theorem continuous_flagCoordinateEvaluation (mu : Fin n → ℝ) :
    Continuous (flagCoordinateEvaluation (K := K) mu) :=
  continuous_hermitianCoordinateProjection.comp (continuous_flagEvaluation mu)

theorem flagCoordinateEvaluation_flagOrbit (mu : Fin n → ℝ)
    (U : Matrix.unitaryGroup (Fin n) K) :
    flagCoordinateEvaluation mu (flagOrbit U) = hermitianOrbitCoordinates U mu := by
  rw [flagCoordinateEvaluation, flagEvaluation_flagOrbit]
  rfl

theorem flagCoordinateEvaluation_reconstruct (mu : Fin n → ℝ) (P : flagSpace n K) :
    hermitianMatrixOfCoordinates (flagCoordinateEvaluation mu P) = flagEvaluation mu P := by
  obtain ⟨U, hU⟩ := P.property
  have hP : P = flagOrbit U := Subtype.ext hU.symm
  subst P
  rw [flagCoordinateEvaluation_flagOrbit, hermitianOrbitCoordinates_reconstruct]
  exact (flagEvaluation_flagOrbit mu U).symm

theorem flagCoordinateEvaluation_injective (mu : Fin n → ℝ)
    (hmu : Function.Injective mu) :
    Function.Injective (flagCoordinateEvaluation (K := K) mu) := by
  intro P Q h
  apply flagEvaluation_injective mu hmu
  have hm := congrArg hermitianMatrixOfCoordinates h
  simpa only [flagCoordinateEvaluation_reconstruct] using hm

def hermitianAngularFlagChart (a : HermitianCoordinateIndex n → K) : flagSpace n K :=
  flagOrbit (hermitianAngularCayley a)

theorem continuous_hermitianAngularFlagChart :
    Continuous (hermitianAngularFlagChart : (HermitianCoordinateIndex n → K) → _) :=
  continuous_flagOrbit.comp continuous_hermitianAngularCayley

@[simp] theorem hermitianAngularFlagChart_zero :
    hermitianAngularFlagChart (0 : HermitianCoordinateIndex n → K) = flagOrbit 1 := by
  simp [hermitianAngularFlagChart]

theorem hermitianCayleyOrbitChart_one_reference (mu : Fin n → ℝ)
    (a : HermitianCoordinateIndex n → K) :
    hermitianCayleyOrbitChart (1 : Matrix.unitaryGroup (Fin n) K) (mu, a) =
      flagCoordinateEvaluation mu (hermitianAngularFlagChart a) := by
  simp only [hermitianCayleyOrbitChart, one_mul, hermitianAngularFlagChart,
    flagCoordinateEvaluation_flagOrbit]

theorem hermitianCayleyOrbitChart_one_eq_flag_permutation (mu : Fin n → ℝ)
    (x : HermitianCoordinates n K) (P : flagSpace n K)
    (h : hermitianCayleyOrbitChart (1 : Matrix.unitaryGroup (Fin n) K) x =
      flagCoordinateEvaluation mu P) :
    ∃ sigma : Equiv.Perm (Fin n), x.1 = mu ∘ sigma := by
  obtain ⟨U, hU⟩ := P.property
  have hP : P = flagOrbit U := Subtype.ext hU.symm
  subst P
  rw [flagCoordinateEvaluation_flagOrbit] at h
  simp only [hermitianCayleyOrbitChart, one_mul] at h
  exact hermitianOrbitCoordinates_eq_spectrum_permutation _ _ _ _ h

def hermitianReferenceSpectrum (n : ℕ) : Fin n → ℝ := fun i ↦ i.val

theorem hermitianReferenceSpectrum_injective (n : ℕ) :
    Function.Injective (hermitianReferenceSpectrum n) := by
  intro i j h
  apply Fin.ext
  change (i.val : ℝ) = (j.val : ℝ) at h
  exact_mod_cast h

def hermitianReferenceChamber (n : ℕ) : Set (Fin n → ℝ) :=
  {lambda | ∀ i, |lambda i - hermitianReferenceSpectrum n i| < (1 : ℝ) / 2}

theorem isOpen_hermitianReferenceChamber (n : ℕ) :
    IsOpen (hermitianReferenceChamber n) := by
  unfold hermitianReferenceChamber
  rw [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i ↦
    isOpen_Iio.preimage ((continuous_apply i).sub continuous_const).abs

@[simp] theorem hermitianReferenceSpectrum_mem_chamber (n : ℕ) :
    hermitianReferenceSpectrum n ∈ hermitianReferenceChamber n := by
  simp [hermitianReferenceChamber]

/-- In disjoint coordinate neighborhoods of the reference spectrum, no nontrivial
permutation of that spectrum remains. This fixes the local spectral labels. -/
theorem hermitianReferenceChamber_permutation_unique (lambda : Fin n → ℝ)
    (hlambda : lambda ∈ hermitianReferenceChamber n) (sigma : Equiv.Perm (Fin n))
    (hperm : lambda = hermitianReferenceSpectrum n ∘ sigma) :
    lambda = hermitianReferenceSpectrum n := by
  funext i
  have hnear := hlambda i
  rw [hperm] at hnear
  change |((sigma i).val : ℝ) - (i.val : ℝ)| < (1 : ℝ) / 2 at hnear
  have hbound := abs_lt.mp hnear
  have hle : (sigma i).val ≤ i.val := by
    by_contra h
    have hh : i.val + 1 ≤ (sigma i).val := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge h)
    have hhR : (i.val : ℝ) + 1 ≤ ((sigma i).val : ℝ) := by exact_mod_cast hh
    linarith
  have hge : i.val ≤ (sigma i).val := by
    by_contra h
    have hh : (sigma i).val + 1 ≤ i.val := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge h)
    have hhR : ((sigma i).val : ℝ) + 1 ≤ (i.val : ℝ) := by exact_mod_cast hh
    linarith
  have hi : sigma i = i := Fin.ext (le_antisymm hle hge)
  simpa only [hperm, Function.comp_apply, hi]

end A3Research

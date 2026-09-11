import GBSHiding.PhotonSector
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-! Passive optics acts by U tensor N on the N-photon sector.  We prove
unitarity, preservation of bosonic symmetry, and preservation of every
sector probability.  Number conservation is a conclusion of this concrete
action, not a field assumed of an unspecified optical transformation. -/
open scoped BigOperators Matrix
open Matrix

namespace GBSHiding
noncomputable section
set_option maxHeartbeats 1600000

abbrev PhotonConfiguration (M N : ℕ) := Fin N → Fin M

def photonTensorMatrix {M : ℕ} (U : Matrix.unitaryGroup (Fin M) ℂ) (N : ℕ) :
    Matrix (PhotonConfiguration M N) (PhotonConfiguration M N) ℂ :=
  fun i j ↦ ∏ s, U (i s) (j s)

theorem photonTensorMatrix_unitary {M : ℕ} (U : Matrix.unitaryGroup (Fin M) ℂ) (N : ℕ) :
    star (photonTensorMatrix U N) * photonTensorMatrix U N = 1 := by
  classical
  ext i j
  change (∑ k : PhotonConfiguration M N, star (∏ s, U (k s) (i s)) *
    (∏ s, U (k s) (j s))) = _
  simp_rw [star_prod, ← Finset.prod_mul_distrib]
  change (∑ k : Fin N → Fin M, ∏ s : Fin N,
    star (U.val (k s) (i s)) * U.val (k s) (j s)) = _
  rw [← Fintype.prod_sum (fun (s : Fin N) (k : Fin M) ↦
    star (U.val k (i s)) * U.val k (j s))]
  have hu (s : Fin N) :
      (∑ k : Fin M, star (U k (i s)) * U k (j s)) =
        if i s = j s then (1:ℂ) else 0 := by
    simpa [Matrix.mul_apply, Matrix.one_apply] using
      congrArg (fun A : Matrix (Fin M) (Fin M) ℂ ↦ A (i s) (j s))
        (Matrix.UnitaryGroup.star_mul_self U)
  simp_rw [hu]
  by_cases hij : i = j
  · subst j
    simp
  · have hne : ∃ s, i s ≠ j s := by simpa [funext_iff] using hij
    obtain ⟨s, hs⟩ := hne
    rw [Matrix.one_apply, if_neg hij]
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    simp [hs]

def photonSectorMass {M N : ℕ} (v : PhotonConfiguration M N → ℂ) : ℝ :=
  ∑ i, Complex.normSq (v i)

theorem unitary_preserves_sum_normSq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : star A * A = 1) (v : ι → ℂ) :
    (∑ i, Complex.normSq ((A *ᵥ v) i)) = ∑ i, Complex.normSq (v i) := by
  have h : star (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
    change (star v ᵥ* (star A * A)) ⬝ᵥ v = _
    rw [hA, Matrix.vecMul_one]
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self, dotProduct,
    Pi.star_apply, Complex.star_def] using h

theorem passiveOptics_preserves_photonSector {M N : ℕ}
    (U : Matrix.unitaryGroup (Fin M) ℂ) (v : PhotonConfiguration M N → ℂ) :
    photonSectorMass (photonTensorMatrix U N *ᵥ v) = photonSectorMass v :=
  unitary_preserves_sum_normSq _ (photonTensorMatrix_unitary U N) v

def configurationPermutation {M N : ℕ} (p : Equiv.Perm (Fin N)) :
    PhotonConfiguration M N ≃ PhotonConfiguration M N where
  toFun i := i ∘ p
  invFun i := i ∘ p.symm
  left_inv i := by funext s; simp
  right_inv i := by funext s; simp

theorem photonTensorMatrix_permute {M N : ℕ}
    (U : Matrix.unitaryGroup (Fin M) ℂ) (p : Equiv.Perm (Fin N))
    (i j : PhotonConfiguration M N) :
    photonTensorMatrix U N (i ∘ p) (j ∘ p) = photonTensorMatrix U N i j :=
  Equiv.prod_comp p (fun s ↦ U (i s) (j s))

def IsBosonicSector {M N : ℕ} (v : PhotonConfiguration M N → ℂ) : Prop :=
  ∀ (p : Equiv.Perm (Fin N)) i, v (i ∘ p) = v i

theorem passiveOptics_preserves_bosonicSymmetry {M N : ℕ}
    (U : Matrix.unitaryGroup (Fin M) ℂ) (v : PhotonConfiguration M N → ℂ)
    (hv : IsBosonicSector v) : IsBosonicSector (photonTensorMatrix U N *ᵥ v) := by
  intro p i
  change (∑ j, photonTensorMatrix U N (i ∘ p) j * v j) =
    ∑ j, photonTensorMatrix U N i j * v j
  calc
    _ = ∑ j, photonTensorMatrix U N (i ∘ p) (j ∘ p) * v (j ∘ p) :=
      ((configurationPermutation (M := M) p).sum_comp
        (fun j ↦ photonTensorMatrix U N (i ∘ p) j * v j)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [photonTensorMatrix_permute, hv p j]

abbrev PhotonState (M : ℕ) := (N : ℕ) → PhotonConfiguration M N → ℂ

def passivePhotonState {M : ℕ} (U : Matrix.unitaryGroup (Fin M) ℂ)
    (v : PhotonState M) : PhotonState M := fun N ↦ photonTensorMatrix U N *ᵥ v N

/-- Every number-sector probability is invariant under the concrete passive
action. This also preserves any normalization of the input state. -/
theorem passiveOptics_preserves_photonNumberLaw {M : ℕ}
    (U : Matrix.unitaryGroup (Fin M) ℂ) (v : PhotonState M) :
    (fun N ↦ photonSectorMass (passivePhotonState U v N)) =
      (fun N ↦ photonSectorMass (v N)) := by
  funext N
  exact passiveOptics_preserves_photonSector U (v N)

end
end GBSHiding

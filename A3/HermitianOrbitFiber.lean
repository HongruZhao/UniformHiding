import A3.HermitianOrbitAtlas

open Set Function
open scoped Matrix Matrix.Norms.Elementwise BigOperators

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]

def hermitianPermutationUnitary (sigma : Equiv.Perm (Fin n)) :
    Matrix.unitaryGroup (Fin n) K :=
  ⟨sigma.permMatrix K, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
    simp⟩

theorem hermitianPermutation_conjugation_diagonal
    (sigma : Equiv.Perm (Fin n)) (r : Fin n → K) :
    (hermitianPermutationUnitary (K := K) sigma : Matrix (Fin n) (Fin n) K) *
        Matrix.diagonal r *
          (hermitianPermutationUnitary (K := K) sigma : Matrix (Fin n) (Fin n) K).conjTranspose =
      Matrix.diagonal (r ∘ sigma) := by
  change sigma.permMatrix K * Matrix.diagonal r * (sigma.permMatrix K).conjTranspose = _
  rw [Matrix.conjTranspose_permMatrix]
  change sigma.toPEquiv.toMatrix * Matrix.diagonal r * sigma.symm.toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simpa only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp,
    Equiv.symm_symm] using Matrix.submatrix_diagonal_equiv r sigma

theorem hermitianOrbitCoordinates_mul_permutation
    (U : Matrix.unitaryGroup (Fin n) K) (sigma : Equiv.Perm (Fin n))
    (lambda : Fin n → ℝ) :
    hermitianOrbitCoordinates (U * hermitianPermutationUnitary sigma) lambda =
      hermitianOrbitCoordinates U (lambda ∘ sigma) := by
  unfold hermitianOrbitCoordinates hermitianOrbitMatrix
  congr 1
  simp only [Matrix.UnitaryGroup.mul_val, Matrix.conjTranspose_mul]
  have hp := hermitianPermutation_conjugation_diagonal (K := K) sigma
    (fun i ↦ (lambda i : K))
  calc
    _ = (U : Matrix (Fin n) (Fin n) K) *
      (((hermitianPermutationUnitary (K := K) sigma : Matrix (Fin n) (Fin n) K) *
        Matrix.diagonal (fun i ↦ (lambda i : K))) *
        (hermitianPermutationUnitary (K := K) sigma : Matrix (Fin n) (Fin n) K).conjTranspose) *
      (U : Matrix (Fin n) (Fin n) K).conjTranspose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hp]; rfl

def regularHermitianRadii (n : ℕ) : Set (Fin n → ℝ) := {lambda | Injective lambda}

theorem isOpen_regularHermitianRadii (n : ℕ) : IsOpen (regularHermitianRadii n) := by
  have he : regularHermitianRadii n =
      ⋂ i : Fin n, ⋂ j : Fin n, {lambda | i = j ∨ lambda i ≠ lambda j} := by
    ext lambda
    simp only [regularHermitianRadii, mem_setOf_eq, mem_iInter, Function.Injective]
    constructor
    · intro h i j
      by_cases hij : i = j
      · exact Or.inl hij
      · exact Or.inr (fun hval ↦ hij (h hval))
    · intro h i j hij
      exact (h i j).resolve_right (not_not.mpr hij)
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  by_cases hij : i = j
  · simpa only [hij, true_or, Set.setOf_true] using isOpen_univ
  · have heq : {lambda : Fin n → ℝ | i = j ∨ lambda i ≠ lambda j} =
        {lambda : Fin n → ℝ | lambda i = lambda j}ᶜ := by
      ext lambda
      simp [hij]
    rw [heq]
    exact (isClosed_eq
        (continuous_apply i : Continuous (fun lambda : Fin n → ℝ ↦ lambda i))
        (continuous_apply j : Continuous (fun lambda : Fin n → ℝ ↦ lambda j))).isOpen_compl

def regularHermitianCoordinateSet (n : ℕ) (K : Type*) [RCLike K] :
    Set (HermitianCoordinates n K) :=
  canonicalHermitianSpectrum ⁻¹' regularHermitianRadii n

theorem measurableSet_regularHermitianCoordinateSet
    [MeasurableSpace K] [BorelSpace K] [PolishSpace K] :
    MeasurableSet (regularHermitianCoordinateSet n K) :=
  (isOpen_regularHermitianRadii n).measurableSet.preimage
    measurable_canonicalHermitianSpectrum

/-- The literal Hermitian spectral theorem, in independent coordinates. -/
theorem hermitianCoordinates_spectral_representation (x : HermitianCoordinates n K) :
    x = hermitianOrbitCoordinates (hermitianMatrixOfCoordinates_isHermitian x).eigenvectorUnitary
      (canonicalHermitianSpectrum x) := by
  have hm := (hermitianMatrixOfCoordinates_isHermitian x).spectral_theorem
  have hc := congrArg hermitianCoordinateProjection hm
  simpa only [hermitianCoordinateProjection_ofCoordinates, Unitary.conjStarAlgAut_apply,
    hermitianOrbitCoordinates, hermitianOrbitMatrix, canonicalHermitianSpectrum,
    Function.comp_def, Matrix.star_eq_conjTranspose] using hc

def RegularHermitianFlagFiber (y : HermitianCoordinates n K) :=
  {z : flagSpace n K × (Fin n → ℝ) //
    z.2 ∈ regularHermitianRadii n ∧ flagCoordinateEvaluation z.2 z.1 = y}

def regularHermitianFlagRepresentation (y : HermitianCoordinates n K)
    (U : Matrix.unitaryGroup (Fin n) K) (lambda : Fin n → ℝ)
    (hlambda : Injective lambda) (hy : y = hermitianOrbitCoordinates U lambda)
    (sigma : Equiv.Perm (Fin n)) : RegularHermitianFlagFiber y :=
  ⟨(flagOrbit (U * hermitianPermutationUnitary sigma.symm), lambda ∘ sigma),
    hlambda.comp sigma.injective, by
      rw [flagCoordinateEvaluation_flagOrbit, hermitianOrbitCoordinates_mul_permutation]
      have he : (lambda ∘ sigma) ∘ sigma.symm = lambda := by
        funext i
        simp only [Function.comp_apply, Equiv.apply_symm_apply]
      rw [he]
      exact hy.symm⟩

theorem regularHermitianFlagRepresentation_injective (y : HermitianCoordinates n K)
    (U : Matrix.unitaryGroup (Fin n) K) (lambda : Fin n → ℝ)
    (hlambda : Injective lambda) (hy : y = hermitianOrbitCoordinates U lambda) :
    Injective (regularHermitianFlagRepresentation y U lambda hlambda hy) := by
  intro sigma tau h
  have he : lambda ∘ sigma = lambda ∘ tau := congrArg (fun z ↦ z.1.2) h
  apply Equiv.ext
  intro i
  exact hlambda (congrFun he i)

theorem regularHermitianFlagRepresentation_surjective (y : HermitianCoordinates n K)
    (U : Matrix.unitaryGroup (Fin n) K) (lambda : Fin n → ℝ)
    (hlambda : Injective lambda) (hy : y = hermitianOrbitCoordinates U lambda) :
    Surjective (regularHermitianFlagRepresentation y U lambda hlambda hy) := by
  intro z
  obtain ⟨V, hV⟩ := z.1.1.property
  have hflag : z.1.1 = flagOrbit V := Subtype.ext hV.symm
  have hz : hermitianOrbitCoordinates V z.1.2 = hermitianOrbitCoordinates U lambda := by
    rw [← flagCoordinateEvaluation_flagOrbit, ← hflag]
    exact z.2.2.trans hy
  obtain ⟨sigma, hsigma⟩ := hermitianOrbitCoordinates_eq_spectrum_permutation
    V U z.1.2 lambda hz
  refine ⟨sigma, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply flagCoordinateEvaluation_injective z.1.2 z.2.1
    have he := (regularHermitianFlagRepresentation y U lambda hlambda hy sigma).2.2
    change flagCoordinateEvaluation z.1.2
      (flagOrbit (U * hermitianPermutationUnitary sigma.symm)) = _
    rw [hsigma]
    exact he.trans (by simpa only [← hsigma] using z.2.2.symm)
  · exact hsigma.symm

def regularHermitianFlagFiberEquiv (y : HermitianCoordinates n K)
    (U : Matrix.unitaryGroup (Fin n) K) (lambda : Fin n → ℝ)
    (hlambda : Injective lambda) (hy : y = hermitianOrbitCoordinates U lambda) :
    Equiv.Perm (Fin n) ≃ RegularHermitianFlagFiber y :=
  Equiv.ofBijective (regularHermitianFlagRepresentation y U lambda hlambda hy)
    ⟨regularHermitianFlagRepresentation_injective y U lambda hlambda hy,
      regularHermitianFlagRepresentation_surjective y U lambda hlambda hy⟩

/-- Exact cardinality of the actual projector-flag orbit fiber. The phase and
sign freedom is already removed by the carrier, leaving exactly `n!`. -/
theorem regularHermitianFlagFiber_equiv_fin (y : HermitianCoordinates n K)
    (hy : y ∈ regularHermitianCoordinateSet n K) :
    Nonempty (RegularHermitianFlagFiber y ≃ Fin n.factorial) := by
  let U := (hermitianMatrixOfCoordinates_isHermitian y).eigenvectorUnitary
  let lambda := canonicalHermitianSpectrum y
  let e := regularHermitianFlagFiberEquiv y U lambda hy
    (hermitianCoordinates_spectral_representation y)
  exact ⟨e.symm.trans ((Fintype.equivFin (Equiv.Perm (Fin n))).trans
    (finCongr (by simp [Fintype.card_perm])))⟩

end A3Research

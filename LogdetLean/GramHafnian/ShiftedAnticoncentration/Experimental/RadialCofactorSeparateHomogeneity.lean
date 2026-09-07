import LogdetLean.GramHafnian.ShiftedAnticoncentration.PastCofactorRandomVariables

/-!
# Separate-column homogeneity of the odd Gram-cofactor energy

This experimental module isolates the deterministic algebra behind the radial
factorization.  It proves directly from the literal hafnian and cofactor
definitions that independently rescaling all `2r-1` past columns rescales the
cofactor combination by the product of the column scalars, and its squared
norm by the product of their complex norm-squares.

The file is intentionally not imported by a production root while the full
probabilistic radial/angular factorization is being audited.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

namespace TypePerfectMatching

/-- The larger endpoint of each pair in a matching on a finite ordered type. -/
private def genericUpperReps {α : Type*} [Fintype α] [LinearOrder α]
    (M : TypePerfectMatching α) : Finset α :=
  Finset.univ.filter fun i ↦ M i < i

private theorem image_genericPairReps_eq_genericUpperReps
    {α : Type*} [Fintype α] [LinearOrder α]
    (M : TypePerfectMatching α) :
    (genericPairReps M).image M = genericUpperReps M := by
  classical
  ext i
  constructor
  · intro hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    simpa [genericPairReps, genericUpperReps, M.mate_mate] using hj
  · intro hi
    rw [Finset.mem_image]
    refine ⟨M i, ?_, M.mate_mate i⟩
    simpa [genericPairReps, genericUpperReps, M.mate_mate] using hi

private theorem genericPairReps_disjoint_genericUpperReps
    {α : Type*} [Fintype α] [LinearOrder α]
    (M : TypePerfectMatching α) :
    Disjoint (genericPairReps M) (genericUpperReps M) := by
  classical
  rw [Finset.disjoint_left]
  intro i hlo hiup
  exact (lt_asymm (by simpa [genericPairReps] using hlo)
    (by simpa [genericUpperReps] using hiup))

private theorem genericPairReps_union_genericUpperReps
    {α : Type*} [Fintype α] [LinearOrder α]
    (M : TypePerfectMatching α) :
    genericPairReps M ∪ genericUpperReps M = Finset.univ := by
  classical
  ext i
  simp only [Finset.mem_union, genericPairReps, genericUpperReps,
    Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact lt_or_gt_of_ne (M.mate_ne i).symm

/-- The two scalar endpoints contributed by every matched pair multiply to
the product over all vertices. -/
theorem prod_pairEndpointScalars_eq_prod_univ
    {α R : Type*} [Fintype α] [LinearOrder α] [CommMonoid R]
    (s : α → R) (M : TypePerfectMatching α) :
    (∏ i ∈ genericPairReps M, s i * s (M i)) = ∏ i : α, s i := by
  classical
  rw [Finset.prod_mul_distrib]
  have hmate :
      (∏ i ∈ genericPairReps M, s (M i)) =
        ∏ i ∈ genericUpperReps M, s i := by
    calc
      (∏ i ∈ genericPairReps M, s (M i)) =
          ∏ i ∈ (genericPairReps M).image M, s i := by
            symm
            exact Finset.prod_image
              (fun _ _ _ _ hij ↦ M.mate.injective hij)
      _ = ∏ i ∈ genericUpperReps M, s i := by
        rw [image_genericPairReps_eq_genericUpperReps]
  rw [hmate, ← Finset.prod_union
    (genericPairReps_disjoint_genericUpperReps M),
    genericPairReps_union_genericUpperReps]

end TypePerfectMatching

/-- A matching monomial is separately homogeneous of degree one in every
vertex scale. -/
theorem typeMatchingMonomial_vertexScale
    {α R : Type*} [Fintype α] [LinearOrder α] [CommMonoid R]
    (s : α → R) (B : Matrix α α R) (M : TypePerfectMatching α) :
    typeMatchingMonomial (fun i j ↦ s i * s j * B i j) M =
      (∏ i : α, s i) * typeMatchingMonomial B M := by
  classical
  unfold typeMatchingMonomial
  rw [Finset.prod_mul_distrib]
  rw [TypePerfectMatching.prod_pairEndpointScalars_eq_prod_univ]

/-- The finite-type hafnian is separately homogeneous of degree one in every
vertex scale under diagonal congruence. -/
theorem typeHafnian_vertexScale
    {α R : Type*} [Fintype α] [LinearOrder α] [CommSemiring R]
    (s : α → R) (B : Matrix α α R) :
    typeHafnian (fun i j ↦ s i * s j * B i j) =
      (∏ i : α, s i) * typeHafnian B := by
  classical
  unfold typeHafnian
  simp_rw [typeMatchingMonomial_vertexScale]
  rw [Finset.mul_sum]

/-- Independent column rescaling acts on the transpose Gram matrix by
diagonal congruence. -/
theorem transposeGram_columnScale
    {r k : ℕ}
    (s : Fin (2 * r) → ℂ) (A : ComplexColumnMatrix r k)
    (i j : Fin (2 * r)) :
    transposeGram (rowMatrix (fun q p ↦ s q * A q p)) i j =
      s i * s j * transposeGram (rowMatrix A) i j := by
  unfold transposeGram rowMatrix
  calc
    (∑ x : Fin k, (s i * A i x) * (s j * A j x)) =
        ∑ x : Fin k, (s i * s j) * (A i x * A j x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ = s i * s j * ∑ x : Fin k, A i x * A j x := by
      rw [Finset.mul_sum]

/-- Exact separate-column homogeneity of a literal odd hafnian cofactor. -/
theorem oddHafnianCofactorVector_columnScale
    {r k : ℕ} (hr : 1 ≤ r) (s : Fin (2 * r) → ℂ)
    (X : ComplexColumnMatrix r k) (j : OddCofactorIndex r hr) :
    oddHafnianCofactorVector hr (fun i p ↦ s i * X i p) j =
      (∏ i : TypePerfectMatching.PairComplement
          (evenLastIndex r hr) j.1, s i.1) *
        oddHafnianCofactorVector hr X j := by
  unfold oddHafnianCofactorVector hafnianPairCofactor
  have hmatrix :
      (fun i q : TypePerfectMatching.PairComplement
          (evenLastIndex r hr) j.1 ↦
        transposeGram (rowMatrix (fun i p ↦ s i * X i p)) i.1 q.1) =
      fun i q ↦ s i.1 * s q.1 *
        transposeGram (rowMatrix X) i.1 q.1 := by
    funext i q
    exact transposeGram_columnScale s X i.1 q.1
  rw [hmatrix]
  exact typeHafnian_vertexScale
    (fun i : TypePerfectMatching.PairComplement
      (evenLastIndex r hr) j.1 ↦ s i.1)
    (fun i q ↦ transposeGram (rowMatrix X) i.1 q.1)

/-- The selected column together with the complementary cofactor contains
every past-column scale exactly once. -/
theorem mul_prod_pairComplement_eq_prod_oddCofactorIndex
    {r : ℕ} (hr : 1 ≤ r) (s : Fin (2 * r) → ℂ)
    (j : OddCofactorIndex r hr) :
    s j.1 *
        (∏ i : TypePerfectMatching.PairComplement
          (evenLastIndex r hr) j.1, s i.1) =
      ∏ i : OddCofactorIndex r hr, s i.1 := by
  classical
  let t : Finset (Fin (2 * r)) := Finset.univ.erase (evenLastIndex r hr)
  have hjt : j.1 ∈ t := by
    simp [t, j.2]
  have hodd :
      (∏ i ∈ t, s i) = ∏ i : OddCofactorIndex r hr, s i.1 := by
    apply Finset.prod_subtype t
    intro i
    simp [t]
  have hpair :
      (∏ i ∈ t.erase j.1, s i) =
        ∏ i : TypePerfectMatching.PairComplement
          (evenLastIndex r hr) j.1, s i.1 := by
    apply Finset.prod_subtype (t.erase j.1)
    intro i
    simp only [t, Finset.mem_erase, Finset.mem_univ, and_true]
    tauto
  rw [← hpair, Finset.mul_prod_erase t s hjt, hodd]

/-- The literal coefficient vector `A_r C_r` scales by the product of all
independent past-column scalars. -/
theorem pastCofactorCombination_separateColumnScale
    {r k : ℕ} (hr : 1 ≤ r)
    (a : OddCofactorIndex r hr → ℂ)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) :
    pastCofactorCombination hr (fun j p ↦ a j * A j p) =
      fun p ↦ (∏ j : OddCofactorIndex r hr, a j) *
        pastCofactorCombination hr A p := by
  funext p
  unfold pastCofactorCombination oddCofactorColumnCombination
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  let sfull : Fin (2 * r) → ℂ := fun i ↦
    if hi : i ≠ evenLastIndex r hr then a ⟨i, hi⟩ else 1
  have hscaledMatrix :
      pastCofactorMatrix hr (fun j p ↦ a j * A j p) =
        fun i p ↦ sfull i * pastCofactorMatrix hr A i p := by
    funext i q
    unfold pastCofactorMatrix
    by_cases hi : i = evenLastIndex r hr
    · subst i
      simp [lastColumnProductEquiv_apply_last]
    · rw [lastColumnProductEquiv_apply_nonlast hr
          ((fun j p ↦ a j * A j p), 0) ⟨i, hi⟩,
        lastColumnProductEquiv_apply_nonlast hr (A, 0) ⟨i, hi⟩]
      rw [show sfull i = a ⟨i, hi⟩ by simp [sfull, hi]]
  rw [hscaledMatrix]
  rw [oddHafnianCofactorVector_columnScale hr
    sfull (pastCofactorMatrix hr A) j]
  have hfactor := mul_prod_pairComplement_eq_prod_oddCofactorIndex hr
    sfull j
  have hprod :
      (∏ i : OddCofactorIndex r hr, sfull i.1) =
        ∏ i : OddCofactorIndex r hr, a i := by
    apply Fintype.prod_congr
    intro i
    simp [sfull, i.2]
  have hfactor' :
      sfull j.1 *
          (∏ i : TypePerfectMatching.PairComplement
            (evenLastIndex r hr) j.1, sfull i.1) =
        ∏ i : OddCofactorIndex r hr, a i := by
    exact hfactor.trans hprod
  calc
    (sfull j.1 * pastCofactorMatrix hr A j.1 p) *
        ((∏ i : TypePerfectMatching.PairComplement
          (evenLastIndex r hr) j.1, sfull i.1) *
          oddHafnianCofactorVector hr (pastCofactorMatrix hr A) j) =
      (sfull j.1 *
          (∏ i : TypePerfectMatching.PairComplement
            (evenLastIndex r hr) j.1, sfull i.1)) *
        (pastCofactorMatrix hr A j.1 p *
          oddHafnianCofactorVector hr (pastCofactorMatrix hr A) j) := by ring
    _ = (∏ i : OddCofactorIndex r hr, a i) *
        (pastCofactorMatrix hr A j.1 p *
          oddHafnianCofactorVector hr (pastCofactorMatrix hr A) j) := by
      rw [hfactor']

/-- Squared norm of a complex scalar multiple. -/
theorem normSq_mul_complex (c z : ℂ) :
    Complex.normSq (c * z) = Complex.normSq c * Complex.normSq z := by
  exact Complex.normSq_mul c z

/-- Exact radial scaling of the literal conditional variance `V_r`. -/
theorem pastCofactorV_separateColumnScale
    {r k : ℕ} (hr : 1 ≤ r)
    (a : OddCofactorIndex r hr → ℂ)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) :
    pastCofactorV hr (fun j p ↦ a j * A j p) =
      (∏ j : OddCofactorIndex r hr, Complex.normSq (a j)) *
        pastCofactorV hr A := by
  change (∑ p : Fin k,
      Complex.normSq (pastCofactorCombination hr
        (fun j p ↦ a j * A j p) p)) = _
  rw [pastCofactorCombination_separateColumnScale hr a A]
  simp_rw [normSq_mul_complex]
  rw [← Finset.mul_sum]
  congr 1
  exact map_prod Complex.normSq a Finset.univ

end

end LogdetLean.GramHafnian

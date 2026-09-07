import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16FlowGeneratorCalculus
import Mathlib.LinearAlgebra.Trace
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

/-!
# The centered symmetric-coordinate Jacobian is one

This file is finite-dimensional algebra.  It contains no determinant-density
normalization, boundary estimate, integration-by-parts certificate, event,
or H16 endpoint.
-/

open NormedSpace
open scoped BigOperators

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

private theorem hasDerivAt_concreteOrbitalFactor_entry
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (i j : Fin N) :
    HasDerivAt (fun t : ℝ ↦ concreteOrbitalFactor N t v i j)
      (concreteCenteredOrbitalDirection N v i j) 0 := by
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have harg : HasDerivAt (fun z : ℂ ↦ -z / (N : ℂ))
      (-(N : ℂ)⁻¹) 0 := by
    simpa [div_eq_mul_inv] using
      ((hasDerivAt_id (𝕜 := ℂ) (x := (0 : ℂ))).neg.mul_const
        (N : ℂ)⁻¹)
  have ha : HasDerivAt (fun z : ℂ ↦ Complex.exp (-z / (N : ℂ)))
      (-(N : ℂ)⁻¹) 0 := by
    simpa using harg.cexp
  have hb : HasDerivAt (fun z : ℂ ↦ Complex.exp z - 1) 1 0 := by
    simpa using (Complex.hasDerivAt_exp (0 : ℂ)).sub_const 1
  have hinner : HasDerivAt
      (fun z : ℂ ↦
        (if i = j then 1 else 0) +
          (Complex.exp z - 1) * complexRankOneProjection v i j)
      (complexRankOneProjection v i j) 0 := by
    simpa using (hb.mul_const
      (complexRankOneProjection v i j)).const_add
        (if i = j then 1 else 0)
  have hprod := ha.mul hinner
  change HasDerivAt
      (fun z : ℂ ↦ Complex.exp (-z / (N : ℂ)) *
          ((if i = j then 1 else 0) +
            (Complex.exp z - 1) *
              complexRankOneProjection v i j))
      _ 0 at hprod
  have hprod' : HasDerivAt
      (fun z : ℂ ↦ Complex.exp (-z / (N : ℂ)) *
          ((if i = j then 1 else 0) +
            (Complex.exp z - 1) *
              complexRankOneProjection v i j))
      ((-(N : ℂ)⁻¹ * (if i = j then 1 else 0)) +
        complexRankOneProjection v i j) 0 := by
    simpa using hprod
  have hreal := hprod'.comp_ofReal
  convert hreal using 1
  · simp [concreteOrbitalFactor, Matrix.smul_apply, Matrix.add_apply,
      Matrix.one_apply, smul_eq_mul]
  · by_cases hij : i = j
    · subst j
      simp [concreteCenteredOrbitalDirection, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      ring
    · simp [concreteCenteredOrbitalDirection, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hij]

private theorem hasDerivAt_centeredCoordinateFlow_entry
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N)
    (ij : ComplexSymmetricCoordinateIndex N) :
    HasDerivAt (fun t : ℝ ↦ h16CenteredCoordinateFlow v t x ij)
      ((concreteCenteredOrbitalDirection N v *
          complexSymmetricMatrixOfCoordinates x +
        complexSymmetricMatrixOfCoordinates x *
          (concreteCenteredOrbitalDirection N v).transpose)
        ij.1.1 ij.1.2) 0 := by
  let Q := concreteCenteredOrbitalDirection N v
  let C := complexSymmetricMatrixOfCoordinates x
  let a : Fin N := ij.1.1
  let b : Fin N := ij.1.2
  have hfactor : ∀ i j : Fin N,
      HasDerivAt (fun t : ℝ ↦ concreteOrbitalFactor N t v i j)
        (Q i j) 0 := fun i j ↦
    hasDerivAt_concreteOrbitalFactor_entry hN v i j
  have hleft : ∀ i j : Fin N,
      HasDerivAt
        (fun t : ℝ ↦ ∑ k : Fin N,
          concreteOrbitalFactor N t v i k * C k j)
        ((Q * C) i j) 0 := by
    intro i j
    simpa only [Matrix.mul_apply] using
      HasDerivAt.fun_sum (u := Finset.univ)
        (A := fun k t ↦ concreteOrbitalFactor N t v i k * C k j)
        (A' := fun k ↦ Q i k * C k j)
        (fun k _ ↦ (hfactor i k).mul_const (C k j))
  have hout : HasDerivAt
      (fun t : ℝ ↦ ∑ k : Fin N,
        (∑ l : Fin N, concreteOrbitalFactor N t v a l * C l k) *
          concreteOrbitalFactor N t v b k)
      ((Q * C + C * Q.transpose) a b) 0 := by
    have hsum := HasDerivAt.fun_sum (x := (0 : ℝ)) (u := Finset.univ)
      (A := fun k t ↦
        (∑ l : Fin N, concreteOrbitalFactor N t v a l * C l k) *
          concreteOrbitalFactor N t v b k)
      (A' := fun k ↦
        (Q * C) a k * (1 : ConcreteMatrixState N) b k +
          C a k * Q b k)
      (fun k _ ↦ by
        have hmul := (hleft a k).mul (hfactor b k)
        change HasDerivAt
          (fun t : ℝ ↦
            (∑ l : Fin N, concreteOrbitalFactor N t v a l * C l k) *
              concreteOrbitalFactor N t v b k) _ 0 at hmul
        have hfactor0 : concreteOrbitalFactor N 0 v = 1 := by
          simp [concreteOrbitalFactor]
        have hleft0 : (∑ l : Fin N,
            (1 : ConcreteMatrixState N) a l * C l k) = C a k := by
          simpa only [Matrix.mul_apply] using
            congrArg (fun M : ConcreteMatrixState N ↦ M a k)
              (Matrix.one_mul C)
        rw [hfactor0, hleft0] at hmul
        exact hmul)
    have hderiv :
        (∑ k : Fin N,
          ((Q * C) a k * (1 : ConcreteMatrixState N) b k +
            C a k * Q b k)) =
          (Q * C + C * Q.transpose) a b := by
      simp only [Finset.sum_add_distrib, Matrix.add_apply,
        Matrix.mul_apply, Matrix.transpose_apply]
      simp [Matrix.one_apply, eq_comm]
    exact hderiv ▸ hsum
  unfold h16CenteredCoordinateFlow transposeCongruenceFlowCoordinates
  simp_rw [transposeCongruenceFlow_centered_eq_concreteOrbitalMatrixUpdate hN]
  simpa [complexSymmetricCoordinatesOfMatrix,
    concreteOrbitalMatrixUpdate, Matrix.mul_apply, Q, C, a, b] using hout

private def h16CenteredCoordinateFlowMatrix
    {N : ℕ} (v : ComplexUnitSphere N) (t : ℝ) :
    Matrix (ComplexSymmetricCoordinateIndex N)
      (ComplexSymmetricCoordinateIndex N) ℂ :=
  LinearMap.toMatrix'
    (centeredTransposeCongruenceFlowCoordinateLinearEquiv v t).toLinearMap

private def h16CenteredCoordinateGeneratorMatrix
    {N : ℕ} (v : ComplexUnitSphere N) :
    Matrix (ComplexSymmetricCoordinateIndex N)
      (ComplexSymmetricCoordinateIndex N) ℂ :=
  fun i j ↦
    let C := complexSymmetricMatrixOfCoordinates
      (Pi.single j (1 : ℂ))
    (concreteCenteredOrbitalDirection N v * C +
      C * (concreteCenteredOrbitalDirection N v).transpose)
      i.1.1 i.1.2

private theorem hasDerivAt_h16CenteredCoordinateFlowMatrix_entry
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (i j : ComplexSymmetricCoordinateIndex N) :
    HasDerivAt (fun t : ℝ ↦ h16CenteredCoordinateFlowMatrix v t i j)
      (h16CenteredCoordinateGeneratorMatrix v i j) 0 := by
  simpa [h16CenteredCoordinateFlowMatrix,
    LinearMap.toMatrix'_apply,
    transposeCongruenceFlowCoordinateLinearEquiv_apply,
    h16CenteredCoordinateGeneratorMatrix] using
      hasDerivAt_centeredCoordinateFlow_entry hN v
        (Pi.single j (1 : ℂ)) i

private theorem h16CenteredCoordinateFlowMatrix_zero
    {N : ℕ} (v : ComplexUnitSphere N) :
    h16CenteredCoordinateFlowMatrix v 0 = 1 := by
  ext i j
  simp [h16CenteredCoordinateFlowMatrix, LinearMap.toMatrix'_apply,
    transposeCongruenceFlowCoordinateLinearEquiv_apply,
    transposeCongruenceFlowCoordinates_zero, Matrix.one_apply,
    Pi.single_apply]

private theorem h16CenteredCoordinateGeneratorMatrix_diag
    {N : ℕ} (v : ComplexUnitSphere N)
    (ij : ComplexSymmetricCoordinateIndex N) :
    h16CenteredCoordinateGeneratorMatrix v ij ij =
      concreteCenteredOrbitalDirection N v ij.1.1 ij.1.1 +
        concreteCenteredOrbitalDirection N v ij.1.2 ij.1.2 := by
  classical
  let a : Fin N := ij.1.1
  let b : Fin N := ij.1.2
  have hab : a ≤ b := ij.2
  let C := complexSymmetricMatrixOfCoordinates (Pi.single ij (1 : ℂ))
  have hright : ∀ k : Fin N, C k b = if k = a then 1 else 0 := by
    intro k
    by_cases hka : k = a
    · subst k
      have heq : (⟨(a, b), hab⟩ : ComplexSymmetricCoordinateIndex N) = ij := by
        apply Subtype.ext
        rfl
      simp [C, complexSymmetricMatrixOfCoordinates, hab, heq]
    · by_cases hkb : k ≤ b
      · have hne : (⟨(k, b), hkb⟩ : ComplexSymmetricCoordinateIndex N) ≠ ij := by
          intro heq
          have := congrArg (fun z : ComplexSymmetricCoordinateIndex N ↦ z.1.1) heq
          exact hka this
        simp [C, complexSymmetricMatrixOfCoordinates, hkb, hka, hne]
      · have hne :
          (⟨(b, k), le_of_lt (lt_of_not_ge hkb)⟩ :
            ComplexSymmetricCoordinateIndex N) ≠ ij := by
          intro heq
          have hkbeq := congrArg
            (fun z : ComplexSymmetricCoordinateIndex N ↦ z.1.2) heq
          exact hkb (hkbeq.trans_le (le_refl b))
        simp [C, complexSymmetricMatrixOfCoordinates, hkb, hka, hne]
  have hleft : ∀ k : Fin N, C a k = if k = b then 1 else 0 := by
    intro k
    by_cases hkb : k = b
    · subst k
      have heq : (⟨(a, b), hab⟩ : ComplexSymmetricCoordinateIndex N) = ij := by
        apply Subtype.ext
        rfl
      simp [C, complexSymmetricMatrixOfCoordinates, hab, heq]
    · by_cases hak : a ≤ k
      · have hne : (⟨(a, k), hak⟩ : ComplexSymmetricCoordinateIndex N) ≠ ij := by
          intro heq
          have := congrArg (fun z : ComplexSymmetricCoordinateIndex N ↦ z.1.2) heq
          exact hkb this
        simp [C, complexSymmetricMatrixOfCoordinates, hak, hkb, hne]
      · have hne :
          (⟨(k, a), le_of_lt (lt_of_not_ge hak)⟩ :
            ComplexSymmetricCoordinateIndex N) ≠ ij := by
          intro heq
          have hakeq := congrArg
            (fun z : ComplexSymmetricCoordinateIndex N ↦ z.1.1) heq
          have hka : k = a := by simpa [a] using hakeq
          apply hak
          rw [hka]
        simp [C, complexSymmetricMatrixOfCoordinates, hak, hkb, hne]
  unfold h16CenteredCoordinateGeneratorMatrix
  change
    (∑ k : Fin N, concreteCenteredOrbitalDirection N v a k * C k b) +
        (∑ k : Fin N, C a k * concreteCenteredOrbitalDirection N v b k) =
      concreteCenteredOrbitalDirection N v a a +
        concreteCenteredOrbitalDirection N v b b
  simp_rw [hright, hleft]
  simp

private def h16UpperCoordinateEquivSigmaIci (N : ℕ) :
    ComplexSymmetricCoordinateIndex N ≃
      Σ i : Fin N, Set.Ici i where
  toFun ij := ⟨ij.1.1, ⟨ij.1.2, ij.2⟩⟩
  invFun p := ⟨(p.1, p.2.1), p.2.2⟩
  left_inv := by intro ij; rfl
  right_inv := by intro p; rfl

private def h16UpperCoordinateEquivSigmaIic (N : ℕ) :
    ComplexSymmetricCoordinateIndex N ≃
      Σ j : Fin N, Set.Iic j where
  toFun ij := ⟨ij.1.2, ⟨ij.1.1, ij.2⟩⟩
  invFun p := ⟨(p.2.1, p.1), p.2.2⟩
  left_inv := by intro ij; rfl
  right_inv := by intro p; rfl

private theorem h16_sum_upper_first
    {N : ℕ} (f : Fin N → ℂ) :
    (∑ ij : ComplexSymmetricCoordinateIndex N, f ij.1.1) =
      ∑ i : Fin N, (N - (i : ℕ)) • f i := by
  calc
    (∑ ij : ComplexSymmetricCoordinateIndex N, f ij.1.1) =
        ∑ p : Σ i : Fin N, Set.Ici i, f p.1 := by
      apply Fintype.sum_equiv (h16UpperCoordinateEquivSigmaIci N)
      intro ij
      rfl
    _ = ∑ i : Fin N, (N - (i : ℕ)) • f i := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i hi
      simp [Fin.card_Ici]

private theorem h16_sum_upper_second
    {N : ℕ} (f : Fin N → ℂ) :
    (∑ ij : ComplexSymmetricCoordinateIndex N, f ij.1.2) =
      ∑ i : Fin N, ((i : ℕ) + 1) • f i := by
  calc
    (∑ ij : ComplexSymmetricCoordinateIndex N, f ij.1.2) =
        ∑ p : Σ j : Fin N, Set.Iic j, f p.1 := by
      apply Fintype.sum_equiv (h16UpperCoordinateEquivSigmaIic N)
      intro ij
      rfl
    _ = ∑ i : Fin N, ((i : ℕ) + 1) • f i := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i hi
      simp [Fin.card_Iic]

private theorem h16_sum_upper_both
    {N : ℕ} (f : Fin N → ℂ) :
    (∑ ij : ComplexSymmetricCoordinateIndex N,
        (f ij.1.1 + f ij.1.2)) =
      (N + 1) • ∑ i : Fin N, f i := by
  rw [Finset.sum_add_distrib, h16_sum_upper_first,
    h16_sum_upper_second, ← Finset.sum_add_distrib]
  calc
    (∑ i : Fin N,
        ((N - (i : ℕ)) • f i + ((i : ℕ) + 1) • f i)) =
        ∑ i : Fin N,
          ((N - (i : ℕ)) + ((i : ℕ) + 1)) • f i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (add_nsmul (f i) (N - (i : ℕ)) ((i : ℕ) + 1)).symm
    _ = ∑ i : Fin N, (N + 1) • f i := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      omega
    _ = (N + 1) • ∑ i : Fin N, f i := by
      rw [Finset.smul_sum]

private theorem h16CenteredCoordinateGeneratorMatrix_trace_zero
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N) :
    Matrix.trace (h16CenteredCoordinateGeneratorMatrix v) = 0 := by
  change (∑ ij : ComplexSymmetricCoordinateIndex N,
    h16CenteredCoordinateGeneratorMatrix v ij ij) = 0
  rw [show (∑ ij : ComplexSymmetricCoordinateIndex N,
      h16CenteredCoordinateGeneratorMatrix v ij ij) =
      ∑ ij : ComplexSymmetricCoordinateIndex N,
        (concreteCenteredOrbitalDirection N v ij.1.1 ij.1.1 +
          concreteCenteredOrbitalDirection N v ij.1.2 ij.1.2) by
    apply Finset.sum_congr rfl
    intro ij hij
    exact h16CenteredCoordinateGeneratorMatrix_diag v ij]
  let f : Fin N → ℂ := fun i ↦
    concreteCenteredOrbitalDirection N v i i
  change (∑ ij : ComplexSymmetricCoordinateIndex N,
    (f ij.1.1 + f ij.1.2)) = 0
  rw [h16_sum_upper_both f]
  rw [show (∑ i : Fin N, f i) =
        Matrix.trace (concreteCenteredOrbitalDirection N v) by rfl]
  rw [trace_concreteCenteredOrbitalDirection_eq_zero hN]
  simp

private theorem h16_perm_erase_prod_one_apply_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    (sigma : Equiv.Perm n) (i : n) :
    ∏ j ∈ Finset.univ.erase i,
        (1 : Matrix n n ℂ) (sigma j) j =
      if sigma = 1 then 1 else 0 := by
  classical
  by_cases hsigma : sigma = 1
  · subst sigma
    simp [Matrix.one_apply]
  · rw [if_neg hsigma]
    have hmoved : ∃ j, sigma j ≠ j := by
      by_contra h
      push_neg at h
      apply hsigma
      ext j
      simpa using h j
    obtain ⟨j, hji, hj⟩ : ∃ j, j ≠ i ∧ sigma j ≠ j := by
      by_cases hi : sigma i = i
      · obtain ⟨j, hj⟩ := hmoved
        exact ⟨j, fun hji ↦ hj (hji.symm ▸ hi), hj⟩
      · refine ⟨sigma i, hi, ?_⟩
        intro heq
        exact hi (sigma.injective heq)
    refine Finset.prod_eq_zero (i := j)
      (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩) ?_
    simp [Matrix.one_apply, hj]

private theorem h16_hasDerivAt_det_of_eq_one_real
    {n : Type*} [Fintype n] [DecidableEq n]
    (F : ℝ → Matrix n n ℂ) (F' : Matrix n n ℂ)
    (hF : ∀ i j, HasDerivAt (fun t ↦ F t i j) (F' i j) 0)
    (hF0 : F 0 = 1) :
    HasDerivAt (fun t ↦ Matrix.det (F t)) (Matrix.trace F') 0 := by
  classical
  rw [show (fun t ↦ Matrix.det (F t)) =
      fun t ↦ ∑ sigma : Equiv.Perm n,
        Equiv.Perm.sign sigma • ∏ i, F t (sigma i) i by
    funext t
    exact Matrix.det_apply (F t)]
  have hprod : ∀ sigma : Equiv.Perm n,
      HasDerivAt (fun t ↦ ∏ i, F t (sigma i) i)
        (∑ i, (∏ j ∈ Finset.univ.erase i, F 0 (sigma j) j) *
          F' (sigma i) i) 0 := by
    intro sigma
    simpa only [smul_eq_mul] using
      (HasDerivAt.fun_finsetProd (u := Finset.univ)
        (f := fun i t ↦ F t (sigma i) i)
        (f' := fun i ↦ F' (sigma i) i)
        (fun i _ ↦ hF (sigma i) i))
  have hsum : HasDerivAt
      (fun t ↦ ∑ sigma : Equiv.Perm n,
        Equiv.Perm.sign sigma • ∏ i, F t (sigma i) i)
      (∑ sigma : Equiv.Perm n,
        Equiv.Perm.sign sigma •
          ∑ i, (∏ j ∈ Finset.univ.erase i, F 0 (sigma j) j) *
            F' (sigma i) i) 0 := by
    apply HasDerivAt.fun_sum
    intro sigma hsigma
    exact (hprod sigma).const_smul (Equiv.Perm.sign sigma)
  convert hsum using 1
  rw [hF0]
  simp_rw [h16_perm_erase_prod_one_apply_eq]
  rw [Finset.sum_eq_single 1]
  · simp [Matrix.trace]
  · intro sigma hsigma hne
    simp [hne]
  · simp

private theorem h16CenteredCoordinateComplexDet_hasDerivAt_zero
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N) :
    HasDerivAt
      (fun t : ℝ ↦ LinearMap.det
        (centeredTransposeCongruenceFlowCoordinateLinearEquiv v t).toLinearMap)
      0 0 := by
  have hdet := h16_hasDerivAt_det_of_eq_one_real
    (h16CenteredCoordinateFlowMatrix v)
    (h16CenteredCoordinateGeneratorMatrix v)
    (hasDerivAt_h16CenteredCoordinateFlowMatrix_entry hN v)
    (h16CenteredCoordinateFlowMatrix_zero v)
  rw [h16CenteredCoordinateGeneratorMatrix_trace_zero hN v] at hdet
  simpa [h16CenteredCoordinateFlowMatrix,
    LinearMap.det_toMatrix'] using hdet

private theorem h16CenteredCoordinateComplexDet_add
    {N : ℕ} (v : ComplexUnitSphere N) (s t : ℝ) :
    LinearMap.det
        (centeredTransposeCongruenceFlowCoordinateLinearEquiv v (s + t)).toLinearMap =
      LinearMap.det
          (centeredTransposeCongruenceFlowCoordinateLinearEquiv v s).toLinearMap *
        LinearMap.det
          (centeredTransposeCongruenceFlowCoordinateLinearEquiv v t).toLinearMap := by
  calc
    LinearMap.det
        (centeredTransposeCongruenceFlowCoordinateLinearEquiv v (s + t)).toLinearMap =
        LinearMap.det
          ((centeredTransposeCongruenceFlowCoordinateLinearEquiv v s).toLinearMap.comp
            (centeredTransposeCongruenceFlowCoordinateLinearEquiv v t).toLinearMap) := by
      apply congrArg LinearMap.det
      apply LinearMap.ext
      intro x
      exact h16CenteredCoordinateFlow_add v s t x
    _ = _ := LinearMap.det_comp _ _

private theorem h16CenteredCoordinateComplexDet_hasDerivAt
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ LinearMap.det
        (centeredTransposeCongruenceFlowCoordinateLinearEquiv v s).toLinearMap)
      0 t := by
  let f : ℝ → ℂ := fun s ↦ LinearMap.det
    (centeredTransposeCongruenceFlowCoordinateLinearEquiv v s).toLinearMap
  have hzero : HasDerivAt f 0 0 :=
    h16CenteredCoordinateComplexDet_hasDerivAt_zero hN v
  have hshift : HasDerivAt (fun u : ℝ ↦ f (t + u)) 0 0 := by
    have hmul := hzero.const_mul (f t)
    have heq : (fun u : ℝ ↦ f (t + u)) = fun u ↦ f t * f u := by
      funext u
      exact h16CenteredCoordinateComplexDet_add v t u
    rw [heq]
    simpa using hmul
  have hsub : HasDerivAt (fun s : ℝ ↦ s - t) 1 t :=
    (hasDerivAt_id (𝕜 := ℝ) (x := t)).sub_const t
  have hshift' : HasDerivAt (fun u : ℝ ↦ f (t + u)) 0 (t - t) := by
    simpa using hshift
  have hcomp := hshift'.scomp (h := fun s : ℝ ↦ s - t) t hsub
  simpa [Function.comp_def, f] using hcomp

/-- The independent complex-coordinate Jacobian identity is completely
finite-dimensional: the generator trace is `(N+1) Tr Q_v = 0`, so the
determinant of its one-parameter flow is identically one. -/
theorem h16CenteredCoordinateComplexJacobianOne
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N) (t : ℝ) :
    H16CenteredCoordinateComplexJacobianOne v t := by
  let f : ℝ → ℂ := fun s ↦ LinearMap.det
    (centeredTransposeCongruenceFlowCoordinateLinearEquiv v s).toLinearMap
  have hf : Differentiable ℝ f := fun s ↦
    (h16CenteredCoordinateComplexDet_hasDerivAt hN v s).differentiableAt
  have hconst : Differentiable ℝ (fun _ : ℝ ↦ (1 : ℂ)) := differentiable_const 1
  have hderiv : ∀ s : ℝ,
      fderiv ℝ f s = fderiv ℝ (fun _ : ℝ ↦ (1 : ℂ)) s := by
    intro s
    rw [(h16CenteredCoordinateComplexDet_hasDerivAt hN v s).hasFDerivAt.fderiv]
    rw [(hasDerivAt_const (x := s) (c := (1 : ℂ))).hasFDerivAt.fderiv]
  have hzero : f 0 = 1 := by
    have hm := congrArg Matrix.det
      (h16CenteredCoordinateFlowMatrix_zero v)
    simpa [f, h16CenteredCoordinateFlowMatrix,
      LinearMap.det_toMatrix'] using hm
  have heq : f = fun _ : ℝ ↦ (1 : ℂ) :=
    eq_of_fderiv_eq hf hconst hderiv 0 hzero
  exact congrFun heq t

/-- Universally quantified centered-coordinate complex Jacobian-one family. -/
theorem h16CenteredCoordinateComplexJacobianFamily
    {N : ℕ} (hN : 1 ≤ N) :
    H16CenteredCoordinateComplexJacobianFamily N :=
  fun v t ↦ h16CenteredCoordinateComplexJacobianOne hN v t

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

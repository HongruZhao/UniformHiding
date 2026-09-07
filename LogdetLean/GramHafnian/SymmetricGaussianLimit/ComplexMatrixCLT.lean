import LogdetLean.GramHafnian.SymmetricGaussianLimit.FiniteDimensionalCLT
import LogdetLean.GramHafnian.SymmetricGaussianLimit.ShiftedWeakLimit
import LogdetLean.GramHafnian.CircularGaussianVectorWick
import LogdetLean.GramHafnian.ShiftedAnticoncentration.GaussianDisk
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.CofactorPhaseLaw
import Mathlib.Probability.Independence.InfinitePi

/-!
# The concrete complex transpose Gram matrix CLT

For a fixed number of columns, this file realizes every upper triangular
quadratic monomial of one standard circular Gaussian row, verifies its full
real covariance matrix from the literal Gaussian product measure, applies the
finite dimensional CLT, and reconstructs the symmetric matrix.  This is the
matrix central limit theorem used in Appendix D of the paper.
-/

open Filter MeasureTheory ProbabilityTheory Complex
open scoped BigOperators ComplexConjugate Real RealInnerProductSpace

namespace LogdetLean.GramHafnian.SymmetricGaussianLimit

noncomputable section

open LogdetLean.GramHafnian

/-- Degree two exponent vectors.  They index the upper triangular entries,
including diagonal entries, without choosing an ordering of pairs. -/
def QuadraticCoordinate (p : ℕ) :=
  {a : Fin p → Fin 3 // ∑ i, (a i : ℕ) = 2}

noncomputable instance (p : ℕ) : Fintype (QuadraticCoordinate p) :=
  by
    classical
    unfold QuadraticCoordinate
    exact Fintype.ofFinite _
noncomputable instance (p : ℕ) : DecidableEq (QuadraticCoordinate p) :=
  Classical.decEq _

/-- The ordinary degree two monomial attached to an exponent vector. -/
def quadraticMonomial {p : ℕ} (a : QuadraticCoordinate p)
    (x : Fin p → ℂ) : ℂ :=
  ∏ i, x i ^ (a.1 i : ℕ)

@[fun_prop] theorem continuous_quadraticMonomial {p : ℕ}
    (a : QuadraticCoordinate p) :
    Continuous (quadraticMonomial a : (Fin p → ℂ) → ℂ) := by
  unfold quadraticMonomial
  fun_prop

/-- Its circular Wick variance, equal to one off the diagonal and two on the
diagonal. -/
def quadraticWeight {p : ℕ} (a : QuadraticCoordinate p) : ℝ :=
  ∏ i, ((a.1 i : ℕ).factorial : ℝ)

theorem quadraticExponent_le_two {p : ℕ}
    (a : QuadraticCoordinate p) (i : Fin p) : (a.1 i : ℕ) ≤ 2 := by
  exact Nat.le_of_lt_succ (a.1 i).isLt

theorem quadraticWeight_pos {p : ℕ} (a : QuadraticCoordinate p) :
    0 < quadraticWeight a := by
  unfold quadraticWeight
  positivity

/-- A pair `(i,j)`, with repetition allowed, as a degree two exponent
vector. -/
def pairQuadraticCoordinate {p : ℕ} (i j : Fin p) :
    QuadraticCoordinate p :=
  ⟨fun q ↦ ⟨(if q = i then 1 else 0) + (if q = j then 1 else 0), by
      split_ifs <;> omega⟩, by
    classical
    rw [Finset.sum_add_distrib]
    simp⟩

theorem pairQuadraticCoordinate_swap {p : ℕ} (i j : Fin p) :
    pairQuadraticCoordinate i j = pairQuadraticCoordinate j i := by
  apply Subtype.ext
  funext q
  apply Fin.ext
  simp only [pairQuadraticCoordinate]
  omega

theorem quadraticMonomial_pair {p : ℕ}
    (x : Fin p → ℂ) (i j : Fin p) :
    quadraticMonomial (pairQuadraticCoordinate i j) x = x i * x j := by
  classical
  unfold quadraticMonomial pairQuadraticCoordinate
  by_cases hij : i = j
  · subst j
    rw [Finset.prod_eq_single i]
    · simp [pow_two]
    · intro q _ hqi
      simp [hqi]
    · simp
  · rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
      (show i ∈ (Finset.univ : Finset (Fin p)) by simp)]
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
      (show j ∈ (Finset.univ : Finset (Fin p)) \ {i} by simp [Ne.symm hij])]
    have hrest :
        ∏ q ∈ ((Finset.univ : Finset (Fin p)) \ {i}) \ {j},
            x q ^ ((if q = i then 1 else 0) + (if q = j then 1 else 0)) = 1 := by
      apply Finset.prod_eq_one
      intro q hq
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_singleton] at hq
      simp [hq.1, hq.2]
    rw [hrest]
    simp [hij, Ne.symm hij]

theorem quadraticWeight_pair {p : ℕ} (i j : Fin p) :
    quadraticWeight (pairQuadraticCoordinate i j) =
      if i = j then 2 else 1 := by
  classical
  unfold quadraticWeight pairQuadraticCoordinate
  by_cases hij : i = j
  · subst j
    rw [Finset.prod_eq_single i]
    · simp
    · intro q _ hqi
      simp [hqi]
    · simp
  · rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
      (show i ∈ (Finset.univ : Finset (Fin p)) by simp)]
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
      (show j ∈ (Finset.univ : Finset (Fin p)) \ {i} by simp [Ne.symm hij])]
    have hrest :
        ∏ q ∈ ((Finset.univ : Finset (Fin p)) \ {i}) \ {j},
          (((if q = i then 1 else 0) +
            (if q = j then 1 else 0)).factorial : ℝ) = 1 := by
      apply Finset.prod_eq_one
      intro q hq
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_singleton] at hq
      simp [hq.1, hq.2]
    simp only [Fin.isValue]
    rw [hrest]
    simp [hij, Ne.symm hij]

/-- Real coordinates used by the multivariate CLT: real and imaginary parts
of each upper triangular quadratic monomial. -/
abbrev QuadraticRealCoordinate (p : ℕ) := QuadraticCoordinate p × Fin 2

/-- The Euclidean coordinate space in which the covariance is the identity. -/
abbrev QuadraticEuclideanSpace (p : ℕ) :=
  EuclideanSpace ℝ (QuadraticRealCoordinate p)

/-- One real coordinate of a quadratic monomial. -/
def quadraticRealComponent {p : ℕ} (q : QuadraticRealCoordinate p)
    (x : Fin p → ℂ) : ℝ :=
  if q.2.1 = 0 then (quadraticMonomial q.1 x).re
  else (quadraticMonomial q.1 x).im

/-- Standardize the real and imaginary parts of one quadratic row so that
each real coordinate has variance one. -/
def standardizedQuadraticRow {p : ℕ} (x : Fin p → ℂ) :
    QuadraticEuclideanSpace p :=
  WithLp.toLp 2 fun q ↦
    Real.sqrt (2 / quadraticWeight q.1) *
      quadraticRealComponent q x

@[fun_prop] theorem continuous_standardizedQuadraticRow {p : ℕ} :
    Continuous (standardizedQuadraticRow :
      (Fin p → ℂ) → QuadraticEuclideanSpace p) := by
  unfold standardizedQuadraticRow
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro q
  by_cases hq : q.2.1 = 0
  · simp [quadraticRealComponent, hq]
    unfold quadraticMonomial
    fun_prop
  · simp [quadraticRealComponent, hq]
    unfold quadraticMonomial
    fun_prop

@[fun_prop] theorem measurable_standardizedQuadraticRow {p : ℕ} :
    Measurable (standardizedQuadraticRow :
      (Fin p → ℂ) → QuadraticEuclideanSpace p) :=
  continuous_standardizedQuadraticRow.measurable

/-- Convert standardized real coordinates back to the paper normalized
complex quadratic coordinates. -/
def unstandardizeQuadratic {p : ℕ}
    (y : QuadraticEuclideanSpace p) : QuadraticCoordinate p → ℂ :=
  fun a ↦
    (Real.sqrt (quadraticWeight a / 2) : ℂ) *
      ((y (a, 0) : ℂ) + (y (a, 1) : ℂ) * I)

@[fun_prop] theorem continuous_unstandardizeQuadratic {p : ℕ} :
    Continuous (unstandardizeQuadratic :
      QuadraticEuclideanSpace p → (QuadraticCoordinate p → ℂ)) := by
  unfold unstandardizeQuadratic
  fun_prop

/-- Assemble a complex symmetric matrix from its quadratic coordinates. -/
def matrixOfQuadraticCoordinates {p : ℕ}
    (y : QuadraticCoordinate p → ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  fun i j ↦ y (pairQuadraticCoordinate i j)

@[fun_prop] theorem continuous_matrixOfQuadraticCoordinates {p : ℕ} :
    Continuous (matrixOfQuadraticCoordinates :
      (QuadraticCoordinate p → ℂ) → Matrix (Fin p) (Fin p) ℂ) := by
  unfold matrixOfQuadraticCoordinates
  fun_prop

theorem matrixOfQuadraticCoordinates_symmetric {p : ℕ}
    (y : QuadraticCoordinate p → ℂ) (i j : Fin p) :
    matrixOfQuadraticCoordinates y i j =
      matrixOfQuadraticCoordinates y j i := by
  rw [matrixOfQuadraticCoordinates, matrixOfQuadraticCoordinates,
    pairQuadraticCoordinate_swap]

/-! ## Exact moments of one quadratic row -/

theorem quadraticMonomial_eq_mixedComplexMultiMonomial {p : ℕ}
    (a : QuadraticCoordinate p) (x : Fin p → ℂ) :
    quadraticMonomial a x =
      mixedComplexMultiMonomial (fun i ↦ (a.1 i : ℕ)) (fun _ ↦ 0) x := by
  classical
  unfold quadraticMonomial mixedComplexMultiMonomial mixedComplexMonomial
  apply Finset.prod_congr rfl
  intro i _
  simp

theorem quadraticMonomial_mul_conj_eq_mixedComplexMultiMonomial {p : ℕ}
    (a b : QuadraticCoordinate p) (x : Fin p → ℂ) :
    quadraticMonomial a x * conj (quadraticMonomial b x) =
      mixedComplexMultiMonomial
        (fun i ↦ (a.1 i : ℕ)) (fun i ↦ (b.1 i : ℕ)) x := by
  classical
  unfold quadraticMonomial mixedComplexMultiMonomial mixedComplexMonomial
  simp only [map_prod, map_pow]
  rw [Finset.prod_mul_distrib]

theorem integrable_quadraticMonomial {p : ℕ}
    (a : QuadraticCoordinate p) :
    Integrable (quadraticMonomial a) (circularGaussianVector p) := by
  rw [show quadraticMonomial a =
      mixedComplexMultiMonomial (fun i ↦ (a.1 i : ℕ)) (fun _ ↦ 0) by
    funext x
    exact quadraticMonomial_eq_mixedComplexMultiMonomial a x]
  unfold circularGaussianVector mixedComplexMultiMonomial
  exact Integrable.fintype_prod fun i ↦
    integrable_mixedComplexMonomial_circularGaussian _ _
      (quadraticExponent_le_two a i) (by simp)

theorem integrable_quadraticMonomial_mul_conj {p : ℕ}
    (a b : QuadraticCoordinate p) :
    Integrable
      (fun x ↦ quadraticMonomial a x * conj (quadraticMonomial b x))
      (circularGaussianVector p) := by
  rw [show (fun x ↦ quadraticMonomial a x * conj (quadraticMonomial b x)) =
      mixedComplexMultiMonomial
        (fun i ↦ (a.1 i : ℕ)) (fun i ↦ (b.1 i : ℕ)) by
    funext x
    exact quadraticMonomial_mul_conj_eq_mixedComplexMultiMonomial a b x]
  unfold circularGaussianVector mixedComplexMultiMonomial
  exact Integrable.fintype_prod fun i ↦
    integrable_mixedComplexMonomial_circularGaussian _ _
      (quadraticExponent_le_two a i) (quadraticExponent_le_two b i)

theorem integrable_quadraticMonomial_mul {p : ℕ}
    (a b : QuadraticCoordinate p) :
    Integrable (fun x ↦ quadraticMonomial a x * quadraticMonomial b x)
      (circularGaussianVector p) := by
  have hmeas : AEStronglyMeasurable
      (fun x ↦ quadraticMonomial a x * quadraticMonomial b x)
      (circularGaussianVector p) := by
    have hcont : Continuous
        (fun x ↦ quadraticMonomial a x * quadraticMonomial b x) := by
      fun_prop
    exact hcont.aestronglyMeasurable
  apply (integrable_norm_iff hmeas).mp
  have h := (integrable_quadraticMonomial_mul_conj a b).norm
  apply h.congr
  exact ae_of_all _ fun x ↦ by simp [norm_mul]

theorem integral_quadraticMonomial {p : ℕ}
    (a : QuadraticCoordinate p) :
    ∫ x, quadraticMonomial a x ∂(circularGaussianVector p) = 0 := by
  rw [integral_congr_ae (ae_of_all _ fun x ↦
    quadraticMonomial_eq_mixedComplexMultiMonomial a x)]
  unfold circularGaussianVector
  rw [integral_mixedComplexMultiMonomial_iid]
  have hmoment (i : Fin p) :
      (∫ z, mixedComplexMonomial (a.1 i : ℕ) 0 z ∂circularGaussian) =
        if (a.1 i : ℕ) = 0 then ((a.1 i : ℕ).factorial : ℂ) else 0 :=
    integral_mixedComplexMonomial_circularGaussian _ _
      (quadraticExponent_le_two a i) (by simp)
  simp_rw [hmoment]
  have hne : (fun i ↦ (a.1 i : ℕ)) ≠ 0 := by
    intro h
    have ha : ∑ i, (a.1 i : ℕ) = 2 := a.2
    simp [h] at ha
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  simp only [Pi.zero_apply] at hi
  rw [Finset.prod_eq_zero (Finset.mem_univ i)]
  rw [if_neg hi]

theorem integral_quadraticMonomial_mul_conj {p : ℕ}
    (a b : QuadraticCoordinate p) :
    ∫ x, quadraticMonomial a x * conj (quadraticMonomial b x)
        ∂(circularGaussianVector p) =
      if a = b then (quadraticWeight a : ℂ) else 0 := by
  rw [integral_congr_ae (ae_of_all _ fun x ↦
    quadraticMonomial_mul_conj_eq_mixedComplexMultiMonomial a b x)]
  unfold circularGaussianVector
  rw [integral_mixedComplexMultiMonomial_iid]
  have hmoment (i : Fin p) :
      (∫ z, mixedComplexMonomial (a.1 i : ℕ) (b.1 i : ℕ) z
          ∂circularGaussian) =
        if (a.1 i : ℕ) = (b.1 i : ℕ) then
          ((a.1 i : ℕ).factorial : ℂ) else 0 :=
    integral_mixedComplexMonomial_circularGaussian _ _
      (quadraticExponent_le_two a i) (quadraticExponent_le_two b i)
  simp_rw [hmoment]
  by_cases hab : a = b
  · subst b
    simp [quadraticWeight]
  · have hfun : (fun i ↦ (a.1 i : ℕ)) ≠ fun i ↦ (b.1 i : ℕ) := by
      intro h
      apply hab
      apply Subtype.ext
      funext i
      apply Fin.ext
      exact congrFun h i
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hfun
    have hfactor :
        (if (a.1 i : ℕ) = (b.1 i : ℕ) then
          ((a.1 i : ℕ).factorial : ℂ) else 0) = 0 := by
      rw [if_neg hi]
    have hprod :
        ∏ i, (if (a.1 i : ℕ) = (b.1 i : ℕ) then
          ((a.1 i : ℕ).factorial : ℂ) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hfactor
    rw [hprod]
    simp [hab]

theorem quadraticMonomial_const_mul {p : ℕ}
    (c : ℂ) (a : QuadraticCoordinate p) (x : Fin p → ℂ) :
    quadraticMonomial a (fun i ↦ c * x i) = c ^ 2 * quadraticMonomial a x := by
  classical
  unfold quadraticMonomial
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum Finset.univ (fun i ↦ (a.1 i : ℕ)) c,
    show ∑ i, (a.1 i : ℕ) = 2 from a.2]

/-- A unit phase whose fourth power is minus one. -/
def eighthRootPhase : ℂ :=
  Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I)

theorem norm_eighthRootPhase : ‖eighthRootPhase‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I (Real.pi / 4)

theorem eighthRootPhase_pow_four : eighthRootPhase ^ 4 = -1 := by
  unfold eighthRootPhase
  calc
    Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I) ^ 4 =
        Complex.exp (4 * ((((Real.pi / 4 : ℝ) : ℂ) * I))) := by
          exact (Complex.exp_nat_mul _ 4).symm
    _ = Complex.exp ((Real.pi : ℂ) * I) := by
      congr 1
      norm_num
      ring
    _ = -1 := Complex.exp_pi_mul_I

theorem integral_quadraticMonomial_mul {p : ℕ}
    (a b : QuadraticCoordinate p) :
    ∫ x, quadraticMonomial a x * quadraticMonomial b x
        ∂(circularGaussianVector p) = 0 := by
  let f : (Fin p → ℂ) → ℂ :=
    fun x ↦ quadraticMonomial a x * quadraticMonomial b x
  let rotate : (Fin p → ℂ) → (Fin p → ℂ) :=
    fun x i ↦ eighthRootPhase * x i
  have hmp : MeasurePreserving rotate
      (circularGaussianVector p) (circularGaussianVector p) := by
    exact measurePreserving_circularGaussianVector_mul
      eighthRootPhase norm_eighthRootPhase
  have hchange :
      (∫ x, f (rotate x) ∂(circularGaussianVector p)) =
        ∫ x, f x ∂(circularGaussianVector p) := by
    have hf : AEStronglyMeasurable f
        ((circularGaussianVector p).map rotate) := by
      rw [hmp.map_eq]
      exact (integrable_quadraticMonomial_mul a b).aestronglyMeasurable
    calc
      (∫ x, f (rotate x) ∂(circularGaussianVector p)) =
          ∫ x, f x ∂((circularGaussianVector p).map rotate) := by
            exact (integral_map hmp.measurable.aemeasurable hf).symm
      _ = ∫ x, f x ∂(circularGaussianVector p) := by rw [hmp.map_eq]
  have hphase : ∀ x, f (rotate x) = -f x := by
    intro x
    simp only [f, rotate, quadraticMonomial_const_mul]
    calc
      eighthRootPhase ^ 2 * quadraticMonomial a x *
          (eighthRootPhase ^ 2 * quadraticMonomial b x) =
          eighthRootPhase ^ 4 *
            (quadraticMonomial a x * quadraticMonomial b x) := by ring
      _ = -(quadraticMonomial a x * quadraticMonomial b x) := by
        rw [eighthRootPhase_pow_four]
        ring
  rw [integral_congr_ae (ae_of_all _ hphase), integral_neg] at hchange
  have hzero : (∫ x, f x ∂(circularGaussianVector p)) = 0 := by
    exact neg_eq_self.mp hchange
  simpa [f] using hzero

/-! ## The real covariance matrix of one standardized row -/

theorem integral_quadratic_re_mul_re {p : ℕ}
    (a b : QuadraticCoordinate p) :
    ∫ x, (quadraticMonomial a x).re * (quadraticMonomial b x).re
        ∂(circularGaussianVector p) =
      (if a = b then quadraticWeight a else 0) / 2 := by
  have hc := integrable_quadraticMonomial_mul_conj a b
  have hm := integrable_quadraticMonomial_mul a b
  have hadd := integral_add hc.re hm.re
  simp only [RCLike.re_to_complex] at hadd
  have hcre := integral_re hc
  have hmre := integral_re hm
  simp only [RCLike.re_to_complex] at hcre hmre
  calc
    (∫ x, (quadraticMonomial a x).re * (quadraticMonomial b x).re
        ∂(circularGaussianVector p)) =
        ∫ x, ((quadraticMonomial a x *
              conj (quadraticMonomial b x)).re +
              (quadraticMonomial a x * quadraticMonomial b x).re) / 2
            ∂(circularGaussianVector p) := by
      apply integral_congr_ae
      exact ae_of_all _ fun x ↦ by
        simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
        ring
    _ = (if a = b then quadraticWeight a else 0) / 2 := by
      rw [integral_div, hadd, hcre, hmre,
        integral_quadraticMonomial_mul_conj,
        integral_quadraticMonomial_mul]
      by_cases hab : a = b <;> simp [hab]

theorem integral_quadratic_im_mul_im {p : ℕ}
    (a b : QuadraticCoordinate p) :
    ∫ x, (quadraticMonomial a x).im * (quadraticMonomial b x).im
        ∂(circularGaussianVector p) =
      (if a = b then quadraticWeight a else 0) / 2 := by
  have hc := integrable_quadraticMonomial_mul_conj a b
  have hm := integrable_quadraticMonomial_mul a b
  have hsub := integral_sub hc.re hm.re
  simp only [RCLike.re_to_complex] at hsub
  have hcre := integral_re hc
  have hmre := integral_re hm
  simp only [RCLike.re_to_complex] at hcre hmre
  calc
    (∫ x, (quadraticMonomial a x).im * (quadraticMonomial b x).im
        ∂(circularGaussianVector p)) =
        ∫ x, ((quadraticMonomial a x *
              conj (quadraticMonomial b x)).re -
              (quadraticMonomial a x * quadraticMonomial b x).re) / 2
            ∂(circularGaussianVector p) := by
      apply integral_congr_ae
      exact ae_of_all _ fun x ↦ by
        simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
        ring
    _ = (if a = b then quadraticWeight a else 0) / 2 := by
      rw [integral_div, hsub, hcre, hmre,
        integral_quadraticMonomial_mul_conj,
        integral_quadraticMonomial_mul]
      by_cases hab : a = b <;> simp [hab]

theorem integral_quadratic_re_mul_im {p : ℕ}
    (a b : QuadraticCoordinate p) :
    ∫ x, (quadraticMonomial a x).re * (quadraticMonomial b x).im
        ∂(circularGaussianVector p) = 0 := by
  have hc := integrable_quadraticMonomial_mul_conj a b
  have hm := integrable_quadraticMonomial_mul a b
  have hsub := integral_sub hm.im hc.im
  simp only [RCLike.im_to_complex] at hsub
  have hmim := integral_im hm
  have hcim := integral_im hc
  simp only [RCLike.im_to_complex] at hmim hcim
  calc
    (∫ x, (quadraticMonomial a x).re * (quadraticMonomial b x).im
        ∂(circularGaussianVector p)) =
        ∫ x, ((quadraticMonomial a x * quadraticMonomial b x).im -
              (quadraticMonomial a x *
                conj (quadraticMonomial b x)).im) / 2
            ∂(circularGaussianVector p) := by
      apply integral_congr_ae
      exact ae_of_all _ fun x ↦ by
        simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
        ring
    _ = 0 := by
      rw [integral_div, hsub, hmim, hcim,
        integral_quadraticMonomial_mul,
        integral_quadraticMonomial_mul_conj]
      by_cases hab : a = b <;> simp [hab]

theorem integral_quadratic_im_mul_re {p : ℕ}
    (a b : QuadraticCoordinate p) :
    ∫ x, (quadraticMonomial a x).im * (quadraticMonomial b x).re
        ∂(circularGaussianVector p) = 0 := by
  simpa [mul_comm] using integral_quadratic_re_mul_im b a

theorem integrable_quadraticRealComponent {p : ℕ}
    (q : QuadraticRealCoordinate p) :
    Integrable (quadraticRealComponent q) (circularGaussianVector p) := by
  rcases q with ⟨a, s⟩
  fin_cases s
  · change Integrable (fun x ↦ (quadraticMonomial a x).re) _
    simpa only [RCLike.re_to_complex] using
      (integrable_quadraticMonomial a).re
  · change Integrable (fun x ↦ (quadraticMonomial a x).im) _
    simpa only [RCLike.im_to_complex] using
      (integrable_quadraticMonomial a).im

theorem integral_quadraticRealComponent {p : ℕ}
    (q : QuadraticRealCoordinate p) :
    ∫ x, quadraticRealComponent q x ∂(circularGaussianVector p) = 0 := by
  rcases q with ⟨a, s⟩
  fin_cases s
  · change ∫ x, (quadraticMonomial a x).re
        ∂(circularGaussianVector p) = 0
    have hre := integral_re (integrable_quadraticMonomial a)
    simp only [RCLike.re_to_complex] at hre
    rw [hre, integral_quadraticMonomial]
    simp
  · change ∫ x, (quadraticMonomial a x).im
        ∂(circularGaussianVector p) = 0
    have him := integral_im (integrable_quadraticMonomial a)
    simp only [RCLike.im_to_complex] at him
    rw [him, integral_quadraticMonomial]
    simp

theorem integral_quadraticRealComponent_mul {p : ℕ}
    (q r : QuadraticRealCoordinate p) :
    ∫ x, quadraticRealComponent q x * quadraticRealComponent r x
        ∂(circularGaussianVector p) =
      if q = r then quadraticWeight q.1 / 2 else 0 := by
  rcases q with ⟨a, s⟩
  rcases r with ⟨b, t⟩
  fin_cases s <;> fin_cases t
  · simp only [quadraticRealComponent, Fin.val_zero, if_pos]
    rw [integral_quadratic_re_mul_re]
    by_cases hab : a = b <;> simp [hab]
  · simp [quadraticRealComponent, integral_quadratic_re_mul_im]
  · simp [quadraticRealComponent, integral_quadratic_im_mul_re]
  · simp only [quadraticRealComponent, Fin.val_one, Nat.one_ne_zero, if_false]
    rw [integral_quadratic_im_mul_im]
    by_cases hab : a = b <;> simp [hab]

theorem integral_standardizedQuadraticRow_apply {p : ℕ}
    (q : QuadraticRealCoordinate p) :
    ∫ x, standardizedQuadraticRow x q ∂(circularGaussianVector p) = 0 := by
  simp only [standardizedQuadraticRow, PiLp.toLp_apply]
  rw [integral_const_mul, integral_quadraticRealComponent]
  ring

theorem integral_standardizedQuadraticRow_apply_mul {p : ℕ}
    (q r : QuadraticRealCoordinate p) :
    ∫ x, standardizedQuadraticRow x q * standardizedQuadraticRow x r
        ∂(circularGaussianVector p) = if q = r then 1 else 0 := by
  simp only [standardizedQuadraticRow, PiLp.toLp_apply]
  rw [show (fun x ↦
      (Real.sqrt (2 / quadraticWeight q.1) * quadraticRealComponent q x) *
      (Real.sqrt (2 / quadraticWeight r.1) * quadraticRealComponent r x)) =
      fun x ↦
        (Real.sqrt (2 / quadraticWeight q.1) *
          Real.sqrt (2 / quadraticWeight r.1)) *
        (quadraticRealComponent q x * quadraticRealComponent r x) by
      funext x
      ring,
    integral_const_mul, integral_quadraticRealComponent_mul]
  by_cases hqr : q = r
  · subst r
    rw [if_pos rfl, if_pos rfl]
    have hw : 0 < quadraticWeight q.1 := quadraticWeight_pos q.1
    have hsqrt :
        Real.sqrt (2 / quadraticWeight q.1) ^ 2 =
          2 / quadraticWeight q.1 := by
      rw [Real.sq_sqrt]
      positivity
    rw [← pow_two, hsqrt]
    field_simp
  · simp [hqr]

@[fun_prop] theorem continuous_quadraticRealComponent {p : ℕ}
    (q : QuadraticRealCoordinate p) :
    Continuous (quadraticRealComponent q : (Fin p → ℂ) → ℝ) := by
  unfold quadraticRealComponent
  split_ifs <;> fun_prop

theorem abs_quadraticRealComponent_le_norm {p : ℕ}
    (q : QuadraticRealCoordinate p) (x : Fin p → ℂ) :
    |quadraticRealComponent q x| ≤ ‖quadraticMonomial q.1 x‖ := by
  unfold quadraticRealComponent
  split_ifs
  · exact Complex.abs_re_le_norm _
  · exact Complex.abs_im_le_norm _

theorem integrable_quadraticRealComponent_mul {p : ℕ}
    (q r : QuadraticRealCoordinate p) :
    Integrable
      (fun x ↦ quadraticRealComponent q x * quadraticRealComponent r x)
      (circularGaussianVector p) := by
  have hdom := (integrable_quadraticMonomial_mul_conj q.1 r.1).norm
  apply hdom.mono'
  · exact ((continuous_quadraticRealComponent q).mul
      (continuous_quadraticRealComponent r)).aestronglyMeasurable
  · exact ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_mul, norm_mul, norm_conj]
      exact mul_le_mul
        (abs_quadraticRealComponent_le_norm q x)
        (abs_quadraticRealComponent_le_norm r x)
        (abs_nonneg _) (norm_nonneg _)

theorem integrable_standardizedQuadraticRow_apply {p : ℕ}
    (q : QuadraticRealCoordinate p) :
    Integrable (fun x ↦ standardizedQuadraticRow x q)
      (circularGaussianVector p) := by
  simp only [standardizedQuadraticRow, PiLp.toLp_apply]
  exact (integrable_quadraticRealComponent q).const_mul _

theorem integrable_standardizedQuadraticRow_apply_mul {p : ℕ}
    (q r : QuadraticRealCoordinate p) :
    Integrable
      (fun x ↦ standardizedQuadraticRow x q *
        standardizedQuadraticRow x r)
      (circularGaussianVector p) := by
  simp only [standardizedQuadraticRow, PiLp.toLp_apply]
  rw [show (fun x ↦
      (Real.sqrt (2 / quadraticWeight q.1) * quadraticRealComponent q x) *
      (Real.sqrt (2 / quadraticWeight r.1) * quadraticRealComponent r x)) =
      fun x ↦
        (Real.sqrt (2 / quadraticWeight q.1) *
          Real.sqrt (2 / quadraticWeight r.1)) *
        (quadraticRealComponent q x * quadraticRealComponent r x) by
      funext x
      ring]
  exact (integrable_quadraticRealComponent_mul q r).const_mul _

theorem inner_standardizedQuadraticRow_eq_sum {p : ℕ}
    (t : QuadraticEuclideanSpace p) (x : Fin p → ℂ) :
    inner ℝ t (standardizedQuadraticRow x) =
      ∑ q, t q * standardizedQuadraticRow x q := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro q _
  rw [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  ring

theorem integral_inner_standardizedQuadraticRow {p : ℕ}
    (t : QuadraticEuclideanSpace p) :
    ∫ x, inner ℝ t (standardizedQuadraticRow x)
        ∂(circularGaussianVector p) = 0 := by
  simp_rw [inner_standardizedQuadraticRow_eq_sum]
  rw [integral_finset_sum Finset.univ]
  · simp only [integral_const_mul,
      integral_standardizedQuadraticRow_apply, mul_zero, Finset.sum_const_zero]
  · intro q _
    exact (integrable_standardizedQuadraticRow_apply q).const_mul _

theorem integral_inner_standardizedQuadraticRow_sq {p : ℕ}
    (t : QuadraticEuclideanSpace p) :
    ∫ x, inner ℝ t (standardizedQuadraticRow x) ^ 2
        ∂(circularGaussianVector p) = ‖t‖ ^ 2 := by
  simp_rw [inner_standardizedQuadraticRow_eq_sum, pow_two,
    Finset.sum_mul_sum]
  have hterm (q r : QuadraticRealCoordinate p) : Integrable
      (fun x ↦ (t q * standardizedQuadraticRow x q) *
        (t r * standardizedQuadraticRow x r))
      (circularGaussianVector p) := by
    rw [show (fun x ↦
        (t q * standardizedQuadraticRow x q) *
          (t r * standardizedQuadraticRow x r)) =
        fun x ↦ (t q * t r) *
          (standardizedQuadraticRow x q * standardizedQuadraticRow x r) by
      funext x
      ring]
    exact (integrable_standardizedQuadraticRow_apply_mul q r).const_mul _
  have htermIntegral (q r : QuadraticRealCoordinate p) :
      ∫ x, (t q * standardizedQuadraticRow x q) *
          (t r * standardizedQuadraticRow x r)
          ∂(circularGaussianVector p) =
        (t q * t r) * (if q = r then 1 else 0) := by
    rw [show (fun x ↦
        (t q * standardizedQuadraticRow x q) *
          (t r * standardizedQuadraticRow x r)) =
        fun x ↦ (t q * t r) *
          (standardizedQuadraticRow x q * standardizedQuadraticRow x r) by
      funext x
      ring,
      integral_const_mul,
      integral_standardizedQuadraticRow_apply_mul]
  have hinnerIntegral (q : QuadraticRealCoordinate p) :
      ∫ x, ∑ r ∈ Finset.univ,
          (t q * standardizedQuadraticRow x q) *
            (t r * standardizedQuadraticRow x r)
          ∂(circularGaussianVector p) =
        ∑ r ∈ Finset.univ, (t q * t r) *
          (if q = r then 1 else 0) := by
    rw [integral_finsetSum Finset.univ]
    · simp_rw [htermIntegral]
    · intro r _
      exact hterm q r
  rw [integral_finsetSum Finset.univ]
  · simp_rw [hinnerIntegral]
    have hnorm := EuclideanSpace.real_norm_sq_eq t
    rw [pow_two] at hnorm
    rw [hnorm]
    simp [pow_two]
  · intro q _
    exact integrable_finsetSum Finset.univ fun r _ ↦ hterm q r

/-! ## An explicit independent row space and the closed CLT -/

/-- The countable product sample space carrying the independent Gaussian
rows. -/
abbrev QuadraticRowSampleSpace (p : ℕ) := ℕ → (Fin p → ℂ)

/-- The literal countable product of the standard circular Gaussian row
law. -/
def quadraticRowProductMeasure (p : ℕ) : Measure (QuadraticRowSampleSpace p) :=
  Measure.infinitePi fun _ : ℕ ↦ circularGaussianVector p

noncomputable instance quadraticRowProductMeasure_isProbability (p : ℕ) :
    IsProbabilityMeasure (quadraticRowProductMeasure p) := by
  unfold quadraticRowProductMeasure
  infer_instance

/-- The standardized quadratic vector from row `a` of the product sample. -/
def standardizedQuadraticSample (p : ℕ) (a : ℕ) :
    QuadraticRowSampleSpace p → QuadraticEuclideanSpace p :=
  fun omega ↦ standardizedQuadraticRow (omega a)

theorem measurable_standardizedQuadraticSample (p : ℕ) (a : ℕ) :
    Measurable (standardizedQuadraticSample p a) := by
  unfold standardizedQuadraticSample
  exact measurable_standardizedQuadraticRow.comp (measurable_pi_apply a)

theorem iIndepFun_standardizedQuadraticSample (p : ℕ) :
    iIndepFun (standardizedQuadraticSample p)
      (quadraticRowProductMeasure p) := by
  unfold standardizedQuadraticSample quadraticRowProductMeasure
  exact iIndepFun_infinitePi fun _ ↦ measurable_standardizedQuadraticRow

theorem identDistrib_standardizedQuadraticSample (p : ℕ) (a : ℕ) :
    IdentDistrib (standardizedQuadraticSample p a)
      (standardizedQuadraticSample p 0)
      (quadraticRowProductMeasure p) (quadraticRowProductMeasure p) := by
  let rowLaw : Measure (QuadraticEuclideanSpace p) :=
    (circularGaussianVector p).map standardizedQuadraticRow
  have hrow : HasLaw (standardizedQuadraticRow :
      (Fin p → ℂ) → QuadraticEuclideanSpace p) rowLaw
      (circularGaussianVector p) := by
    refine ⟨measurable_standardizedQuadraticRow.aemeasurable, ?_⟩
    rfl
  have hlaw (j : ℕ) : HasLaw (standardizedQuadraticSample p j) rowLaw
      (quadraticRowProductMeasure p) := by
    have heval := (measurePreserving_eval_infinitePi
      (fun _ : ℕ ↦ circularGaussianVector p) j).hasLaw
    change HasLaw (standardizedQuadraticRow ∘ Function.eval j) rowLaw
      (Measure.infinitePi fun _ : ℕ ↦ circularGaussianVector p)
    exact hrow.comp heval
  exact (hlaw a).identDistrib (hlaw 0)

theorem integral_inner_standardizedQuadraticSample (p : ℕ)
    (t : QuadraticEuclideanSpace p) :
    ∫ omega, inner ℝ t (standardizedQuadraticSample p 0 omega)
        ∂(quadraticRowProductMeasure p) = 0 := by
  let F : (Fin p → ℂ) → ℝ :=
    fun x ↦ inner ℝ t (standardizedQuadraticRow x)
  have hF : AEStronglyMeasurable F (circularGaussianVector p) := by
    apply Continuous.aestronglyMeasurable
    unfold F
    fun_prop
  have hmap : (quadraticRowProductMeasure p).map
      (fun omega ↦ omega 0) = circularGaussianVector p := by
    unfold quadraticRowProductMeasure
    exact (measurePreserving_eval_infinitePi
      (fun _ : ℕ ↦ circularGaussianVector p) 0).map_eq
  have hFmap : AEStronglyMeasurable F
      ((quadraticRowProductMeasure p).map (fun omega ↦ omega 0)) := by
    unfold quadraticRowProductMeasure
    rw [(measurePreserving_eval_infinitePi
      (fun _ : ℕ ↦ circularGaussianVector p) 0).map_eq]
    exact hF
  calc
    (∫ omega, inner ℝ t (standardizedQuadraticSample p 0 omega)
        ∂(quadraticRowProductMeasure p)) =
        ∫ x, F x ∂(circularGaussianVector p) := by
      change (∫ omega, F (omega 0) ∂(quadraticRowProductMeasure p)) = _
      rw [← hmap]
      exact (integral_map (μ := quadraticRowProductMeasure p)
        (measurable_pi_apply 0).aemeasurable hFmap).symm
    _ = 0 := integral_inner_standardizedQuadraticRow t

theorem integral_inner_standardizedQuadraticSample_sq (p : ℕ)
    (t : QuadraticEuclideanSpace p) :
    ∫ omega, inner ℝ t (standardizedQuadraticSample p 0 omega) ^ 2
        ∂(quadraticRowProductMeasure p) = ‖t‖ ^ 2 := by
  let F : (Fin p → ℂ) → ℝ :=
    fun x ↦ inner ℝ t (standardizedQuadraticRow x) ^ 2
  have hF : AEStronglyMeasurable F (circularGaussianVector p) := by
    apply Continuous.aestronglyMeasurable
    unfold F
    fun_prop
  have hmap : (quadraticRowProductMeasure p).map
      (fun omega ↦ omega 0) = circularGaussianVector p := by
    unfold quadraticRowProductMeasure
    exact (measurePreserving_eval_infinitePi
      (fun _ : ℕ ↦ circularGaussianVector p) 0).map_eq
  have hFmap : AEStronglyMeasurable F
      ((quadraticRowProductMeasure p).map (fun omega ↦ omega 0)) := by
    unfold quadraticRowProductMeasure
    rw [(measurePreserving_eval_infinitePi
      (fun _ : ℕ ↦ circularGaussianVector p) 0).map_eq]
    exact hF
  calc
    (∫ omega, inner ℝ t (standardizedQuadraticSample p 0 omega) ^ 2
        ∂(quadraticRowProductMeasure p)) =
        ∫ x, F x ∂(circularGaussianVector p) := by
      change (∫ omega, F (omega 0) ∂(quadraticRowProductMeasure p)) = _
      rw [← hmap]
      exact (integral_map (μ := quadraticRowProductMeasure p)
        (measurable_pi_apply 0).aemeasurable hFmap).symm
    _ = ‖t‖ ^ 2 := integral_inner_standardizedQuadraticRow_sq t

/-- The unconditional fixed dimensional CLT for all standardized real and
imaginary upper triangular quadratic coordinates. -/
theorem tendstoInDistribution_standardizedQuadraticSample (p : ℕ) :
    TendstoInDistribution
      (normalizedPartialSum (standardizedQuadraticSample p)) atTop id
      (fun _ ↦ quadraticRowProductMeasure p)
      (stdGaussian (QuadraticEuclideanSpace p)) := by
  exact tendstoInDistribution_normalizedPartialSum_stdGaussian
    (quadraticRowProductMeasure p) (standardizedQuadraticSample p)
    (fun a ↦ (measurable_standardizedQuadraticSample p a).aemeasurable)
    (iIndepFun_standardizedQuadraticSample p)
    (identDistrib_standardizedQuadraticSample p)
    (integral_inner_standardizedQuadraticSample p)
    (integral_inner_standardizedQuadraticSample_sq p)

/-! ## Reconstruction as the normalized transpose Gram matrix -/

theorem sqrt_quadraticWeight_half_mul_sqrt_two_div {p : ℕ}
    (a : QuadraticCoordinate p) :
    Real.sqrt (quadraticWeight a / 2) *
        Real.sqrt (2 / quadraticWeight a) = 1 := by
  have hw0 : 0 ≤ quadraticWeight a / 2 := by
    exact div_nonneg (quadraticWeight_pos a).le (by norm_num)
  rw [← Real.sqrt_mul hw0]
  have hw : (quadraticWeight a / 2) *
      (2 / quadraticWeight a) = 1 := by
    field_simp [ne_of_gt (quadraticWeight_pos a)]
  rw [hw]
  simp

theorem unstandardize_standardizedQuadraticRow {p : ℕ}
    (x : Fin p → ℂ) (a : QuadraticCoordinate p) :
    unstandardizeQuadratic (standardizedQuadraticRow x) a =
      quadraticMonomial a x := by
  unfold unstandardizeQuadratic standardizedQuadraticRow
  simp only [PiLp.toLp_apply]
  rw [show quadraticRealComponent (a, 0) x =
      (quadraticMonomial a x).re by simp [quadraticRealComponent],
    show quadraticRealComponent (a, 1) x =
      (quadraticMonomial a x).im by simp [quadraticRealComponent]]
  push_cast
  have hscale : (Real.sqrt (quadraticWeight a / 2) : ℂ) *
      (Real.sqrt (2 / quadraticWeight a) : ℂ) = 1 := by
    exact_mod_cast sqrt_quadraticWeight_half_mul_sqrt_two_div a
  calc
    (Real.sqrt (quadraticWeight a / 2) : ℂ) *
        ((Real.sqrt (2 / quadraticWeight a) : ℂ) *
          (quadraticMonomial a x).re +
        (Real.sqrt (2 / quadraticWeight a) : ℂ) *
          (quadraticMonomial a x).im * I) =
      ((Real.sqrt (quadraticWeight a / 2) : ℂ) *
        (Real.sqrt (2 / quadraticWeight a) : ℂ)) *
        ((quadraticMonomial a x).re +
          (quadraticMonomial a x).im * I) := by ring
    _ = (quadraticMonomial a x).re +
          (quadraticMonomial a x).im * I := by rw [hscale, one_mul]
    _ = quadraticMonomial a x := Complex.re_add_im _

/-- The reconstruction map as a real linear map, used to commute it with
the finite normalized sum. -/
def unstandardizeQuadraticLinear (p : ℕ) :
    QuadraticEuclideanSpace p →ₗ[ℝ] (QuadraticCoordinate p → ℂ) where
  toFun := unstandardizeQuadratic
  map_add' := by
    intro y z
    funext a
    unfold unstandardizeQuadratic
    simp only [PiLp.add_apply, Pi.add_apply]
    push_cast
    ring
  map_smul' := by
    intro c y
    funext a
    unfold unstandardizeQuadratic
    simp only [PiLp.smul_apply, Pi.smul_apply, RingHom.id_apply]
    rw [Complex.real_smul]
    push_cast
    simp only [smul_eq_mul]
    rw [show ((c * y (a, 0) : ℝ) : ℂ) =
        (c : ℂ) * (y (a, 0) : ℂ) by exact Complex.ofReal_mul _ _,
      show ((c * y (a, 1) : ℝ) : ℂ) =
        (c : ℂ) * (y (a, 1) : ℂ) by exact Complex.ofReal_mul _ _]
    ring

theorem unstandardizeQuadraticLinear_apply {p : ℕ}
    (y : QuadraticEuclideanSpace p) :
    unstandardizeQuadraticLinear p y = unstandardizeQuadratic y := rfl

theorem unstandardize_normalizedPartialSum_apply (p k : ℕ)
    (omega : QuadraticRowSampleSpace p) (a : QuadraticCoordinate p) :
    unstandardizeQuadratic
        (normalizedPartialSum (standardizedQuadraticSample p) k omega) a =
      (Real.sqrt k)⁻¹ *
        ∑ j ∈ Finset.range k, quadraticMonomial a (omega j) := by
  change (unstandardizeQuadraticLinear p
      (normalizedPartialSum (standardizedQuadraticSample p) k omega)) a = _
  unfold normalizedPartialSum
  rw [LinearMap.map_smul, map_sum]
  simp only [Pi.smul_apply, PiLp.smul_apply, Finset.sum_apply,
    unstandardizeQuadraticLinear_apply, standardizedQuadraticSample,
    unstandardize_standardizedQuadraticRow]
  push_cast
  rw [Complex.real_smul]
  simp only [Complex.ofReal_inv]

/-- The normalized transpose Gram matrix of the first `k` Gaussian rows. -/
def normalizedTransposeGramSample (p k : ℕ)
    (omega : QuadraticRowSampleSpace p) : Fin p → Fin p → ℂ :=
  fun i j ↦ (Real.sqrt k)⁻¹ *
    ∑ a ∈ Finset.range k, omega a i * omega a j

/-- The Gaussian matrix reconstructed from independent standard real
coordinates.  Its upper triangular complex coordinates are independent,
with complex variance one off the diagonal and two on the diagonal. -/
def symmetricGaussianMatrixFromStd (p : ℕ) :
    QuadraticEuclideanSpace p → (Fin p → Fin p → ℂ) :=
  matrixOfQuadraticCoordinates ∘ unstandardizeQuadratic

/-- The same limiting matrix written directly on the finite product of
independent standard real Gaussian coordinates. -/
def symmetricGaussianMatrixFromRealProduct (p : ℕ)
    (r : QuadraticRealCoordinate p → ℝ) : Fin p → Fin p → ℂ :=
  fun i j ↦
    (Real.sqrt ((if i = j then 2 else 1) / 2) : ℂ) *
      ((r (pairQuadraticCoordinate i j, 0) : ℂ) +
        (r (pairQuadraticCoordinate i j, 1) : ℂ) * I)

@[fun_prop] theorem measurable_symmetricGaussianMatrixFromRealProduct (p : ℕ) :
    Measurable (symmetricGaussianMatrixFromRealProduct p) := by
  unfold symmetricGaussianMatrixFromRealProduct
  fun_prop

@[fun_prop] theorem continuous_symmetricGaussianMatrixFromStd (p : ℕ) :
    Continuous (symmetricGaussianMatrixFromStd p) :=
  continuous_matrixOfQuadraticCoordinates.comp continuous_unstandardizeQuadratic

theorem symmetricGaussianMatrixFromStd_toLp_apply (p : ℕ)
    (r : QuadraticRealCoordinate p → ℝ) (i j : Fin p) :
    symmetricGaussianMatrixFromStd p (WithLp.toLp 2 r) i j =
      symmetricGaussianMatrixFromRealProduct p r i j := by
  change matrixOfQuadraticCoordinates
      (unstandardizeQuadratic (WithLp.toLp 2 r)) i j = _
  unfold symmetricGaussianMatrixFromRealProduct
    matrixOfQuadraticCoordinates unstandardizeQuadratic
  simp only [PiLp.toLp_apply]
  rw [quadraticWeight_pair]

/-- The target law in Eq. (D.1) is literally generated by a finite product
of independent standard real Gaussians, two for each upper triangular entry.
The displayed scaling gives complex variance one off the diagonal and two on
the diagonal. -/
theorem symmetricGaussianMatrixFromStd_law_eq_realProduct (p : ℕ) :
    (stdGaussian (QuadraticEuclideanSpace p)).map
        (symmetricGaussianMatrixFromStd p) =
      (Measure.pi fun _ : QuadraticRealCoordinate p ↦ gaussianReal 0 1).map
        (symmetricGaussianMatrixFromRealProduct p) := by
  rw [← map_pi_eq_stdGaussian]
  rw [Measure.map_map
    (continuous_symmetricGaussianMatrixFromStd p).measurable (by fun_prop)]
  congr 1
  funext r
  ext i j
  exact symmetricGaussianMatrixFromStd_toLp_apply p r i j

theorem assembled_normalizedPartialSum_eq_transposeGram (p k : ℕ)
    (omega : QuadraticRowSampleSpace p) :
    symmetricGaussianMatrixFromStd p
        (normalizedPartialSum (standardizedQuadraticSample p) k omega) =
      normalizedTransposeGramSample p k omega := by
  ext i j
  change matrixOfQuadraticCoordinates
      (unstandardizeQuadratic
        (normalizedPartialSum (standardizedQuadraticSample p) k omega)) i j = _
  rw [matrixOfQuadraticCoordinates,
    unstandardize_normalizedPartialSum_apply,
    normalizedTransposeGramSample]
  simp_rw [quadraticMonomial_pair]

/-- Eq. (D.1): the normalized complex transpose Gram matrix converges in
distribution, for fixed matrix size, to the complex symmetric Gaussian law
constructed from independent real standard Gaussian coordinates. -/
theorem tendstoInDistribution_normalizedTransposeGramSample (p : ℕ) :
    TendstoInDistribution
      (normalizedTransposeGramSample p) atTop
      (symmetricGaussianMatrixFromStd p)
      (fun _ ↦ quadraticRowProductMeasure p)
      (stdGaussian (QuadraticEuclideanSpace p)) := by
  have h := (tendstoInDistribution_standardizedQuadraticSample p).continuous_comp
    (continuous_symmetricGaussianMatrixFromStd p)
  apply h.congr
  · intro k
    exact ae_of_all _ fun omega ↦
      assembled_normalizedPartialSum_eq_transposeGram p k omega
  · exact ae_of_all _ fun _ ↦ rfl

/-- The normalized Gram hafnian corresponding to the left side of Eq. (D.2). -/
def normalizedTransposeGramHafnianSample (n k : ℕ)
    (omega : QuadraticRowSampleSpace (2 * n)) : ℂ :=
  hafnian (normalizedTransposeGramSample (2 * n) k omega)

/-- The limiting symmetric Gaussian hafnian corresponding to the right side
of Eq. (D.2). -/
def symmetricGaussianHafnianFromStd (n : ℕ)
    (y : QuadraticEuclideanSpace (2 * n)) : ℂ :=
  hafnian (symmetricGaussianMatrixFromStd (2 * n) y)

/-- Eq. (D.2), unconditionally: the continuous hafnian image of the concrete
matrix CLT. -/
theorem tendstoInDistribution_normalizedTransposeGramHafnianSample (n : ℕ) :
    TendstoInDistribution
      (normalizedTransposeGramHafnianSample n) atTop
      (symmetricGaussianHafnianFromStd n)
      (fun _ ↦ quadraticRowProductMeasure (2 * n))
      (stdGaussian (QuadraticEuclideanSpace (2 * n))) := by
  have hhaf : Continuous
      (fun A : Fin (2 * n) → Fin (2 * n) → ℂ ↦ hafnian A) := by
    exact continuous_hafnian n
  have h := (tendstoInDistribution_normalizedTransposeGramSample (2 * n)).continuous_comp
    hhaf
  apply h.congr
  · intro k
    exact ae_of_all _ fun _ ↦ rfl
  · exact ae_of_all _ fun _ ↦ rfl

end

end LogdetLean.GramHafnian.SymmetricGaussianLimit

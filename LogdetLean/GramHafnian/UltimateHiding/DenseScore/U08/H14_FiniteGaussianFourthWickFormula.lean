import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H14_FiniteGaussianFourthWickClassifier
import Mathlib.Tactic

/-!
# Exact finite Gaussian fourth-Wick formula

This module closes the numerator-only producer
`H14FiniteGaussianFourthWickFormula`.  It uses the already checked
eight-coordinate Gaussian Wick theorem and the explicit 105-matching
classifier.  It does not import a literature atom, H6, or any H3--H18
endpoint.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

set_option maxRecDepth 100000
set_option maxHeartbeats 3600000

/-! ## Four labelled quadratic factors on eight half-edges -/

abbrev H14Factor := Fin 4
abbrev H14Side := Fin 2

/-- The lexicographic factor/side labelling `0,1 | 2,3 | 4,5 | 6,7`. -/
def h14BaseEdgeEquiv : H14Factor × H14Side ≃ H14HalfEdge := by
  simpa using (finProdFinEquiv : Fin 4 × Fin 2 ≃ Fin (4 * 2))

@[simp] private theorem h14BaseEdgeEquiv_00 :
    h14BaseEdgeEquiv ((0 : H14Factor), (0 : H14Side)) = 0 := rfl

@[simp] private theorem h14BaseEdgeEquiv_01 :
    h14BaseEdgeEquiv ((0 : H14Factor), (1 : H14Side)) = 1 := rfl

@[simp] private theorem h14BaseEdgeEquiv_10 :
    h14BaseEdgeEquiv ((1 : H14Factor), (0 : H14Side)) = 2 := rfl

@[simp] private theorem h14BaseEdgeEquiv_11 :
    h14BaseEdgeEquiv ((1 : H14Factor), (1 : H14Side)) = 3 := rfl

@[simp] private theorem h14BaseEdgeEquiv_20 :
    h14BaseEdgeEquiv ((2 : H14Factor), (0 : H14Side)) = 4 := rfl

@[simp] private theorem h14BaseEdgeEquiv_21 :
    h14BaseEdgeEquiv ((2 : H14Factor), (1 : H14Side)) = 5 := rfl

@[simp] private theorem h14BaseEdgeEquiv_30 :
    h14BaseEdgeEquiv ((3 : H14Factor), (0 : H14Side)) = 6 := rfl

@[simp] private theorem h14BaseEdgeEquiv_31 :
    h14BaseEdgeEquiv ((3 : H14Factor), (1 : H14Side)) = 7 := rfl

/-- A permutation sending the four lexicographic coefficient edges to
`(3,0),(1,2),(7,4),(5,6)`, the orientation matching
`tr(C W C W)^2`. -/
def h14TraceTwoVertexEquiv : Equiv.Perm H14HalfEdge where
  toFun := ![3, 0, 1, 2, 7, 4, 5, 6]
  invFun := ![1, 2, 3, 0, 5, 6, 7, 4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Oriented coefficient edges for the squared second trace. -/
def h14TraceTwoEdgeEquiv : H14Factor × H14Side ≃ H14HalfEdge :=
  h14BaseEdgeEquiv.trans h14TraceTwoVertexEquiv

private def h14SideFlip : Equiv.Perm H14Side := Equiv.swap 0 1

private def h14MatchingOfEdgeEquiv
    (e : H14Factor × H14Side ≃ H14HalfEdge) :
    Equiv.Perm H14HalfEdge :=
  e.symm.trans ((Equiv.prodCongr (Equiv.refl H14Factor) h14SideFlip).trans e)

private theorem h14MatchingOfBaseEdgeEquiv :
    h14MatchingOfEdgeEquiv h14BaseEdgeEquiv = h14RowMatching := by
  decide

private theorem h14MatchingOfTraceTwoEdgeEquiv :
    h14MatchingOfEdgeEquiv h14TraceTwoEdgeEquiv =
      h14TraceTwoCoordinateMatching := by
  decide

/-- Product of four matrix entries along the four oriented coefficient
edges.  Symmetry makes it independent of the displayed orientations. -/
def h14EdgeCoefficient {p : ℕ}
    (e : H14Factor × H14Side ≃ H14HalfEdge)
    (C : Matrix (Fin p) (Fin p) ℝ) (x : H14HalfEdge → Fin p) : ℝ :=
  ∏ s : H14Factor, C (x (e (s, 0))) (x (e (s, 1)))

/-- A colouring is constant on every edge of `sigma`. -/
def h14MatchingCompatible {q : ℕ}
    (sigma : Equiv.Perm H14HalfEdge) (x : H14HalfEdge → Fin q) : Prop :=
  ∀ h, x (sigma h) = x h

/-- One fixed-matching coordinate contraction. -/
noncomputable def h14CoordinateContraction {p : ℕ}
    (e : H14Factor × H14Side ≃ H14HalfEdge)
    (sigma : Equiv.Perm H14HalfEdge)
    (C : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  by
    classical
    exact ∑ x : H14HalfEdge → Fin p,
      if h14MatchingCompatible sigma x then h14EdgeCoefficient e C x else 0

/-- The five trace monomials, in the same order as the checked classifier. -/
def h14TracePartitionMonomial {p : ℕ}
    (lambda : H14TracePartitionFour) (C : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  ![Matrix.trace C ^ 4,
    Matrix.trace C ^ 2 * Matrix.trace (C ^ 2),
    Matrix.trace (C ^ 2) ^ 2,
    Matrix.trace C * Matrix.trace (C ^ 3),
    Matrix.trace (C ^ 4)] lambda

/-! ## Five representative matching diagrams -/

private def h14RepMatching0 : Equiv.Perm H14HalfEdge where
  toFun := ![1, 0, 3, 2, 5, 4, 7, 6]
  invFun := ![1, 0, 3, 2, 5, 4, 7, 6]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private def h14RepMatching1 : Equiv.Perm H14HalfEdge where
  toFun := ![2, 3, 0, 1, 5, 4, 7, 6]
  invFun := ![2, 3, 0, 1, 5, 4, 7, 6]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private def h14RepMatching2 : Equiv.Perm H14HalfEdge where
  toFun := ![2, 3, 0, 1, 6, 7, 4, 5]
  invFun := ![2, 3, 0, 1, 6, 7, 4, 5]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private def h14RepMatching3 : Equiv.Perm H14HalfEdge where
  toFun := ![5, 2, 1, 4, 3, 0, 7, 6]
  invFun := ![5, 2, 1, 4, 3, 0, 7, 6]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private def h14RepMatching4 : Equiv.Perm H14HalfEdge where
  toFun := ![7, 2, 1, 4, 3, 6, 5, 0]
  invFun := ![7, 2, 1, 4, 3, 6, 5, 0]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private def h14RepMatching
    (lambda : H14TracePartitionFour) : Equiv.Perm H14HalfEdge :=
  ![h14RepMatching0, h14RepMatching1, h14RepMatching2,
    h14RepMatching3, h14RepMatching4] lambda

private theorem h14RepMatching_isRaw (lambda : H14TracePartitionFour) :
    h14IsRawPerfectMatching (h14RepMatching lambda) = true := by
  fin_cases lambda <;> decide

/-! ## Explicit evaluation of the five representatives -/

private def h14FinEightTuple {alpha : Type*}
    (a b c d e f g h : alpha) : Fin 8 → alpha :=
  ![a, b, c, d, e, f, g, h]

private def h14FinEightFunctionEquiv (alpha : Type*) :
    (Fin 8 → alpha) ≃
      alpha × (alpha × (alpha × (alpha ×
        (alpha × (alpha × (alpha × alpha)))))) where
  toFun x := ⟨x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7⟩
  invFun x := h14FinEightTuple x.1 x.2.1 x.2.2.1 x.2.2.2.1
    x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv x := by
    rcases x with ⟨a, b, c, d, e, f, g, h⟩
    rfl

private theorem h14SumFinEightFunction
    {alpha M : Type*} [Fintype alpha] [AddCommMonoid M]
    (F : (Fin 8 → alpha) → M) :
    (∑ x, F x) = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, ∑ g, ∑ h,
      F (h14FinEightTuple a b c d e f g h) := by
  rw [← (h14FinEightFunctionEquiv alpha).symm.sum_comp F]
  simp only [Fintype.sum_prod_type]
  rfl

private theorem h14Compatible_rep0 {q : ℕ} (x : H14HalfEdge → Fin q) :
    h14MatchingCompatible h14RepMatching0 x ↔
      x 0 = x 1 ∧ x 2 = x 3 ∧ x 4 = x 5 ∧ x 6 = x 7 := by
  constructor
  · intro hx
    exact ⟨by simpa [h14RepMatching0] using hx 1,
      by simpa [h14RepMatching0] using hx 3,
      by simpa [h14RepMatching0] using hx 5,
      by simpa [h14RepMatching0] using hx 7⟩
  · rintro ⟨h01, h23, h45, h67⟩ i
    fin_cases i <;> simp_all [h14RepMatching0]

private theorem h14Compatible_rep1 {q : ℕ} (x : H14HalfEdge → Fin q) :
    h14MatchingCompatible h14RepMatching1 x ↔
      x 0 = x 2 ∧ x 1 = x 3 ∧ x 4 = x 5 ∧ x 6 = x 7 := by
  constructor
  · intro hx
    exact ⟨by simpa [h14RepMatching1] using hx 2,
      by simpa [h14RepMatching1] using hx 3,
      by simpa [h14RepMatching1] using hx 5,
      by simpa [h14RepMatching1] using hx 7⟩
  · rintro ⟨h02, h13, h45, h67⟩ i
    fin_cases i <;> simp_all [h14RepMatching1]

private theorem h14Compatible_rep2 {q : ℕ} (x : H14HalfEdge → Fin q) :
    h14MatchingCompatible h14RepMatching2 x ↔
      x 0 = x 2 ∧ x 1 = x 3 ∧ x 4 = x 6 ∧ x 5 = x 7 := by
  constructor
  · intro hx
    exact ⟨by simpa [h14RepMatching2] using hx 2,
      by simpa [h14RepMatching2] using hx 3,
      by simpa [h14RepMatching2] using hx 6,
      by simpa [h14RepMatching2] using hx 7⟩
  · rintro ⟨h02, h13, h46, h57⟩ i
    fin_cases i <;> simp_all [h14RepMatching2]

private theorem h14Compatible_rep3 {q : ℕ} (x : H14HalfEdge → Fin q) :
    h14MatchingCompatible h14RepMatching3 x ↔
      x 0 = x 5 ∧ x 1 = x 2 ∧ x 3 = x 4 ∧ x 6 = x 7 := by
  constructor
  · intro hx
    exact ⟨by simpa [h14RepMatching3] using hx 5,
      by simpa [h14RepMatching3] using hx 2,
      by simpa [h14RepMatching3] using hx 4,
      by simpa [h14RepMatching3] using hx 7⟩
  · rintro ⟨h05, h12, h34, h67⟩ i
    fin_cases i <;> simp_all [h14RepMatching3]

private theorem h14Compatible_rep4 {q : ℕ} (x : H14HalfEdge → Fin q) :
    h14MatchingCompatible h14RepMatching4 x ↔
      x 0 = x 7 ∧ x 1 = x 2 ∧ x 3 = x 4 ∧ x 5 = x 6 := by
  constructor
  · intro hx
    exact ⟨by simpa [h14RepMatching4] using hx 7,
      by simpa [h14RepMatching4] using hx 2,
      by simpa [h14RepMatching4] using hx 4,
      by simpa [h14RepMatching4] using hx 6⟩
  · rintro ⟨h07, h12, h34, h56⟩ i
    fin_cases i <;> simp_all [h14RepMatching4]

private theorem h14TraceTwoEntrySum {p : ℕ}
    (C : Matrix (Fin p) (Fin p) ℝ) :
    (∑ i : Fin p, ∑ j : Fin p, C i j * C j i) = Matrix.trace (C ^ 2) := by
  simp [Matrix.trace, Matrix.mul_apply, pow_two]

private theorem h14TraceThreeEntrySum {p : ℕ}
    (C : Matrix (Fin p) (Fin p) ℝ) :
    (∑ i : Fin p, ∑ j : Fin p, ∑ k : Fin p,
      C i j * C j k * C k i) = Matrix.trace (C ^ 3) := by
  simp [Matrix.trace, Matrix.mul_apply, pow_succ, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]

private theorem h14TraceFourEntrySum {p : ℕ}
    (C : Matrix (Fin p) (Fin p) ℝ) :
    (∑ i : Fin p, ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
      C i j * C j k * C k l * C l i) = Matrix.trace (C ^ 4) := by
  simp [Matrix.trace, Matrix.mul_apply, pow_succ, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
        C i j * C j k * C k l * C l i) =
        ∑ j : Fin p, ∑ l : Fin p, ∑ k : Fin p,
          C i j * C j k * C k l * C l i := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
    _ = ∑ l : Fin p, ∑ j : Fin p, ∑ k : Fin p,
          C i j * C j k * C k l * C l i := by
      rw [Finset.sum_comm]
    _ = ∑ l : Fin p, ∑ k : Fin p, ∑ j : Fin p,
          C i j * C j k * C k l * C l i := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro j hj
      ring

private theorem h14SumMulSum
    {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℝ) (g : β → ℝ) :
    (∑ a, f a) * (∑ b, g b) = ∑ a, ∑ b, f a * g b := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]

private theorem h14SumTwoMulSum
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → ℝ) (g : γ → ℝ) :
    (∑ a, ∑ b, f a b) * (∑ c, g c) =
      ∑ a, ∑ b, ∑ c, f a b * g c := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]

private theorem h14SumThreeMulSum
    {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → ℝ) (g : δ → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) * (∑ d, g d) =
      ∑ a, ∑ b, ∑ c, ∑ d, f a b c * g d := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mul_sum]

private theorem h14SumTwoMulSumTwo
    {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → ℝ) (g : γ → δ → ℝ) :
    (∑ a, ∑ b, f a b) * (∑ c, ∑ d, g c d) =
      ∑ a, ∑ b, ∑ c, ∑ d, f a b * g c d := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mul_sum]

private theorem h14SumFourSeparable
    {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → ℝ) (g : β → ℝ) (h : γ → ℝ) (k : δ → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a * g b * h c * k d) =
      (∑ a, f a) * (∑ b, g b) * (∑ c, h c) * (∑ d, k d) := by
  symm
  rw [h14SumMulSum]
  rw [h14SumTwoMulSum]
  rw [h14SumThreeMulSum]

private theorem h14SumPairSingletonSingleton
    {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → ℝ) (g : γ → ℝ) (h : δ → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b * g c * h d) =
      (∑ a, ∑ b, f a b) * (∑ c, g c) * (∑ d, h d) := by
  symm
  rw [h14SumTwoMulSum]
  rw [h14SumThreeMulSum]

private theorem h14SumPairPair
    {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → ℝ) (g : γ → δ → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b * g c d) =
      (∑ a, ∑ b, f a b) * (∑ c, ∑ d, g c d) := by
  exact (h14SumTwoMulSumTwo f g).symm

private theorem h14SumTripleSingleton
    {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → ℝ) (g : δ → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c * g d) =
      (∑ a, ∑ b, ∑ c, f a b c) * (∑ d, g d) := by
  exact (h14SumThreeMulSum f g).symm

private theorem h14SymmetricEntrySquareSum {p : ℕ}
    (C : Matrix (Fin p) (Fin p) ℝ) (hC : C.IsSymm) :
    (∑ i : Fin p, ∑ j : Fin p, C i j ^ 2) = Matrix.trace (C ^ 2) := by
  have hsymm : ∀ i j, C j i = C i j := Matrix.IsSymm.ext_iff.mp hC
  calc
    (∑ i : Fin p, ∑ j : Fin p, C i j ^ 2) =
        ∑ i : Fin p, ∑ j : Fin p, C i j * C j i := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hsymm]
      ring
    _ = Matrix.trace (C ^ 2) := h14TraceTwoEntrySum C

private theorem h14SymmetricEntrySelfMulSum {p : ℕ}
    (C : Matrix (Fin p) (Fin p) ℝ) (hC : C.IsSymm) :
    (∑ i : Fin p, ∑ j : Fin p, C i j * C i j) = Matrix.trace (C ^ 2) := by
  simpa [pow_two] using h14SymmetricEntrySquareSum C hC

private theorem h14SymmetricTraceThreeEntrySum {p : ℕ}
    (C : Matrix (Fin p) (Fin p) ℝ) (hC : C.IsSymm) :
    (∑ i : Fin p, ∑ j : Fin p, ∑ k : Fin p,
      C i j * C j k * C i k) = Matrix.trace (C ^ 3) := by
  have hsymm : ∀ i j, C j i = C i j := Matrix.IsSymm.ext_iff.mp hC
  calc
    (∑ i : Fin p, ∑ j : Fin p, ∑ k : Fin p,
        C i j * C j k * C i k) =
        ∑ i : Fin p, ∑ j : Fin p, ∑ k : Fin p,
          C i j * C j k * C k i := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      rw [hsymm i k]
    _ = Matrix.trace (C ^ 3) := h14TraceThreeEntrySum C

private theorem h14SymmetricTraceFourEntrySum {p : ℕ}
    (C : Matrix (Fin p) (Fin p) ℝ) (hC : C.IsSymm) :
    (∑ i : Fin p, ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
      C i j * C j k * C k l * C i l) = Matrix.trace (C ^ 4) := by
  have hsymm : ∀ i j, C j i = C i j := Matrix.IsSymm.ext_iff.mp hC
  calc
    (∑ i : Fin p, ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
        C i j * C j k * C k l * C i l) =
        ∑ i : Fin p, ∑ j : Fin p, ∑ k : Fin p, ∑ l : Fin p,
          C i j * C j k * C k l * C l i := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      rw [hsymm i l]
    _ = Matrix.trace (C ^ 4) := h14TraceFourEntrySum C

private theorem h14CoordinateContraction_rep0 {p : ℕ}
    (C : Matrix (Fin p) (Fin p) ℝ) :
    h14CoordinateContraction h14BaseEdgeEquiv h14RepMatching0 C =
      Matrix.trace C ^ 4 := by
  classical
  unfold h14CoordinateContraction
  rw [h14SumFinEightFunction]
  simp [h14Compatible_rep0, ite_and, h14EdgeCoefficient,
    h14FinEightTuple, Fin.prod_univ_four]
  rw [h14SumFourSeparable]
  simp [Matrix.trace]
  ring

private theorem h14CoordinateContraction_rep1 {p : ℕ}
    (C : Matrix (Fin p) (Fin p) ℝ) (hC : C.IsSymm) :
    h14CoordinateContraction h14BaseEdgeEquiv h14RepMatching1 C =
      Matrix.trace C ^ 2 * Matrix.trace (C ^ 2) := by
  classical
  have hsymm : ∀ i j, C j i = C i j := Matrix.IsSymm.ext_iff.mp hC
  unfold h14CoordinateContraction
  rw [h14SumFinEightFunction]
  simp [h14Compatible_rep1, ite_and, h14EdgeCoefficient,
    h14FinEightTuple, Fin.prod_univ_four, hsymm]
  rw [h14SumPairSingletonSingleton]
  rw [h14SymmetricEntrySelfMulSum C hC]
  simp [Matrix.trace]
  ring

private theorem h14CoordinateContraction_rep2 {p : ℕ}
    (C : Matrix (Fin p) (Fin p) ℝ) (hC : C.IsSymm) :
    h14CoordinateContraction h14BaseEdgeEquiv h14RepMatching2 C =
      Matrix.trace (C ^ 2) ^ 2 := by
  classical
  have hsymm : ∀ i j, C j i = C i j := Matrix.IsSymm.ext_iff.mp hC
  unfold h14CoordinateContraction
  rw [h14SumFinEightFunction]
  simp [h14Compatible_rep2, ite_and, h14EdgeCoefficient,
    h14FinEightTuple, Fin.prod_univ_four, hsymm]
  simp_rw [show ∀ a b c d : Fin p,
      C a b * C a b * C c d * C c d =
        (C a b * C a b) * (C c d * C c d) by
      intro a b c d
      ring]
  rw [h14SumPairPair]
  rw [h14SymmetricEntrySelfMulSum C hC]
  ring

private theorem h14CoordinateContraction_rep3 {p : ℕ}
    (C : Matrix (Fin p) (Fin p) ℝ) (hC : C.IsSymm) :
    h14CoordinateContraction h14BaseEdgeEquiv h14RepMatching3 C =
      Matrix.trace C * Matrix.trace (C ^ 3) := by
  classical
  have hsymm : ∀ i j, C j i = C i j := Matrix.IsSymm.ext_iff.mp hC
  unfold h14CoordinateContraction
  rw [h14SumFinEightFunction]
  simp [h14Compatible_rep3, ite_and, h14EdgeCoefficient,
    h14FinEightTuple, Fin.prod_univ_four, hsymm]
  rw [h14SumTripleSingleton]
  rw [h14SymmetricTraceThreeEntrySum C hC]
  simp [Matrix.trace]
  ring

private theorem h14CoordinateContraction_rep4 {p : ℕ}
    (C : Matrix (Fin p) (Fin p) ℝ) (hC : C.IsSymm) :
    h14CoordinateContraction h14BaseEdgeEquiv h14RepMatching4 C =
      Matrix.trace (C ^ 4) := by
  classical
  have hsymm : ∀ i j, C j i = C i j := Matrix.IsSymm.ext_iff.mp hC
  unfold h14CoordinateContraction
  rw [h14SumFinEightFunction]
  simp [h14Compatible_rep4, ite_and, h14EdgeCoefficient,
    h14FinEightTuple, Fin.prod_univ_four, hsymm]
  exact h14SymmetricTraceFourEntrySum C hC

private theorem h14CoordinateContraction_rep
    {p : ℕ} (lambda : H14TracePartitionFour)
    (C : Matrix (Fin p) (Fin p) ℝ) (hC : C.IsSymm) :
    h14CoordinateContraction h14BaseEdgeEquiv (h14RepMatching lambda) C =
      h14TracePartitionMonomial lambda C := by
  fin_cases lambda
  · exact h14CoordinateContraction_rep0 C
  · exact h14CoordinateContraction_rep1 C hC
  · exact h14CoordinateContraction_rep2 C hC
  · exact h14CoordinateContraction_rep3 C hC
  · exact h14CoordinateContraction_rep4 C hC

/-! ## Relabelling a matching diagram without changing its contraction -/

/-- An automorphism of the four unoriented coefficient edges: it permutes
the factors and may independently reverse each edge. -/
private structure H14EdgeRelabeling where
  factorPerm : Equiv.Perm H14Factor
  sidePerm : H14Factor → Equiv.Perm H14Side
deriving DecidableEq, Fintype

private def H14EdgeRelabeling.onPairs (r : H14EdgeRelabeling) :
    H14Factor × H14Side ≃ H14Factor × H14Side where
  toFun z := (r.factorPerm z.1, r.sidePerm z.1 z.2)
  invFun z :=
    (r.factorPerm.symm z.1,
      (r.sidePerm (r.factorPerm.symm z.1)).symm z.2)
  left_inv z := by
    rcases z with ⟨s, u⟩
    simp
  right_inv z := by
    rcases z with ⟨s, u⟩
    simp

/-- The induced permutation of the eight labelled half-edges, relative to
an oriented presentation of the four coefficient edges. -/
private def H14EdgeRelabeling.toPerm (r : H14EdgeRelabeling)
    (e : H14Factor × H14Side ≃ H14HalfEdge) :
    Equiv.Perm H14HalfEdge :=
  e.symm.trans (r.onPairs.trans e)

private theorem h14PermFinTwo_pair (u : Equiv.Perm H14Side) :
    (u 0 = 0 ∧ u 1 = 1) ∨ (u 0 = 1 ∧ u 1 = 0) := by
  have hvalue : ∀ z : H14Side, z = 0 ∨ z = 1 := by
    intro z
    fin_cases z <;> simp
  have hu0 := hvalue (u 0)
  have hu1 := hvalue (u 1)
  rcases hu0 with h0 | h0 <;> rcases hu1 with h1 | h1
  · exfalso
    have hbad : (0 : H14Side) = 1 :=
      u.injective (h0.trans h1.symm)
    exact Fin.zero_ne_one hbad
  · exact Or.inl ⟨h0, h1⟩
  · exact Or.inr ⟨h0, h1⟩
  · exfalso
    have hbad : (0 : H14Side) = 1 :=
      u.injective (h0.trans h1.symm)
    exact Fin.zero_ne_one hbad

private theorem h14EdgeCoefficient_relabel
    {p : ℕ} (e : H14Factor × H14Side ≃ H14HalfEdge)
    (r : H14EdgeRelabeling) (C : Matrix (Fin p) (Fin p) ℝ)
    (hC : C.IsSymm) (x : H14HalfEdge → Fin p) :
    h14EdgeCoefficient e C (x ∘ r.toPerm e) =
      h14EdgeCoefficient e C x := by
  classical
  unfold h14EdgeCoefficient
  apply Fintype.prod_equiv r.factorPerm
  intro s
  simp only [H14EdgeRelabeling.toPerm, H14EdgeRelabeling.onPairs,
    Equiv.trans_apply, Equiv.symm_apply_apply, Function.comp_apply]
  rcases h14PermFinTwo_pair (r.sidePerm s) with hs | hs
  · simp [hs.1, hs.2]
  · have hsymm : ∀ i j, C j i = C i j := Matrix.IsSymm.ext_iff.mp hC
    simp [hs.1, hs.2, hsymm]

private def h14ColoringRelabelEquiv {q : ℕ}
    (tau : Equiv.Perm H14HalfEdge) :
    (H14HalfEdge → Fin q) ≃ (H14HalfEdge → Fin q) where
  toFun x := x ∘ tau.symm
  invFun x := x ∘ tau
  left_inv x := by
    funext h
    simp
  right_inv x := by
    funext h
    simp

@[simp] private theorem h14ColoringRelabelEquiv_apply {q : ℕ}
    (tau : Equiv.Perm H14HalfEdge) (x : H14HalfEdge → Fin q)
    (h : H14HalfEdge) :
    h14ColoringRelabelEquiv tau x h = x (tau.symm h) := rfl

private theorem h14MatchingCompatible_relabel
    {q : ℕ} {sigma rep tau : Equiv.Perm H14HalfEdge}
    (hconj : ∀ h, rep (tau h) = tau (sigma h))
    (x : H14HalfEdge → Fin q) :
    h14MatchingCompatible sigma x ↔
      h14MatchingCompatible rep (h14ColoringRelabelEquiv tau x) := by
  constructor
  · intro hx h
    obtain ⟨i, rfl⟩ := tau.surjective h
    simp only [h14ColoringRelabelEquiv_apply]
    rw [hconj]
    simpa using hx i
  · intro hx h
    have hh := hx (tau h)
    simp only [h14ColoringRelabelEquiv_apply] at hh
    rw [hconj] at hh
    simpa using hh

private theorem h14CoordinateContraction_relabel
    {p : ℕ} (e : H14Factor × H14Side ≃ H14HalfEdge)
    (sigma rep : Equiv.Perm H14HalfEdge) (r : H14EdgeRelabeling)
    (hconj : ∀ h, rep (r.toPerm e h) = r.toPerm e (sigma h))
    (C : Matrix (Fin p) (Fin p) ℝ) (hC : C.IsSymm) :
    h14CoordinateContraction e sigma C =
      h14CoordinateContraction e rep C := by
  classical
  unfold h14CoordinateContraction
  apply Fintype.sum_equiv (h14ColoringRelabelEquiv (r.toPerm e))
  intro x
  rw [show h14MatchingCompatible sigma x ↔
      h14MatchingCompatible rep
        (h14ColoringRelabelEquiv (r.toPerm e) x) by
    exact h14MatchingCompatible_relabel hconj x]
  split_ifs
  · simpa [h14ColoringRelabelEquiv, Function.comp_def] using
      h14EdgeCoefficient_relabel e r C hC
        (h14ColoringRelabelEquiv (r.toPerm e) x)
  · rfl

/-! ## Exhaustive canonicalization of all 105 Wick matchings -/

private def h14EdgeTransport
    (e : H14Factor × H14Side ≃ H14HalfEdge) :
    Equiv.Perm H14HalfEdge :=
  h14BaseEdgeEquiv.symm.trans e

private def h14RepMatchingAtEdge
    (e : H14Factor × H14Side ≃ H14HalfEdge)
    (lambda : H14TracePartitionFour) : Equiv.Perm H14HalfEdge :=
  (h14EdgeTransport e).symm.trans
    ((h14RepMatching lambda).trans (h14EdgeTransport e))

private theorem h14CoordinateContraction_repAtEdge
    {p : ℕ} (e : H14Factor × H14Side ≃ H14HalfEdge)
    (lambda : H14TracePartitionFour)
    (C : Matrix (Fin p) (Fin p) ℝ) (hC : C.IsSymm) :
    h14CoordinateContraction e (h14RepMatchingAtEdge e lambda) C =
      h14TracePartitionMonomial lambda C := by
  classical
  let v := h14EdgeTransport e
  calc
    h14CoordinateContraction e (h14RepMatchingAtEdge e lambda) C =
        h14CoordinateContraction h14BaseEdgeEquiv
          (h14RepMatching lambda) C := by
      unfold h14CoordinateContraction
      apply Fintype.sum_equiv (h14ColoringRelabelEquiv v.symm)
      intro x
      have he : e = h14BaseEdgeEquiv.trans v := by
        ext z
        simp [v, h14EdgeTransport]
      have hcompat :
          h14MatchingCompatible (h14RepMatchingAtEdge e lambda) x ↔
            h14MatchingCompatible (h14RepMatching lambda)
              (h14ColoringRelabelEquiv v.symm x) := by
        constructor
        · intro hx h
          change x (v ((h14RepMatching lambda) h)) = x (v h)
          have hh := hx (v h)
          simpa [h14RepMatchingAtEdge, v, h14EdgeTransport] using hh
        · intro hx h
          obtain ⟨i, rfl⟩ := v.surjective h
          have hh := hx i
          change x (v ((h14RepMatching lambda) i)) = x (v i) at hh
          simpa [h14RepMatchingAtEdge, v, h14EdgeTransport] using hh
      rw [hcompat]
      split_ifs
      · rw [he]
        rfl
      · rfl
    _ = _ := h14CoordinateContraction_rep lambda C hC

private theorem h14TraceOneCanonicalizer_exists (code : Fin 105) :
    ∃ r : H14EdgeRelabeling, ∀ h : H14HalfEdge,
      h14RepMatchingAtEdge h14BaseEdgeEquiv
          (h14TracePartitionOf h14TraceOneCoordinateMatching
            (h14CanonicalRawPerfectMatching code).1)
          (r.toPerm h14BaseEdgeEquiv h) =
        r.toPerm h14BaseEdgeEquiv
          ((h14CanonicalRawPerfectMatching code).1 h) := by
  fin_cases code <;> decide

private theorem h14TraceTwoCanonicalizer_exists (code : Fin 105) :
    ∃ r : H14EdgeRelabeling, ∀ h : H14HalfEdge,
      h14RepMatchingAtEdge h14TraceTwoEdgeEquiv
          (h14TracePartitionOf h14TraceTwoCoordinateMatching
            (h14CanonicalRawPerfectMatching code).1)
          (r.toPerm h14TraceTwoEdgeEquiv h) =
        r.toPerm h14TraceTwoEdgeEquiv
          ((h14CanonicalRawPerfectMatching code).1 h) := by
  fin_cases code <;> decide

/-- Every one of the canonical 105 Wick matchings contracts to the trace
partition certified by the trace-one classifier. -/
theorem h14CoordinateContraction_traceOne_code_internal
    {p : ℕ} (code : Fin 105) (C : Matrix (Fin p) (Fin p) ℝ)
    (hC : C.IsSymm) :
    h14CoordinateContraction h14BaseEdgeEquiv
        (h14CanonicalRawPerfectMatching code).1 C =
      h14TracePartitionMonomial
        (h14TracePartitionOf h14TraceOneCoordinateMatching
          (h14CanonicalRawPerfectMatching code).1) C := by
  obtain ⟨r, hr⟩ := h14TraceOneCanonicalizer_exists code
  rw [h14CoordinateContraction_relabel h14BaseEdgeEquiv
    (h14CanonicalRawPerfectMatching code).1
    (h14RepMatchingAtEdge h14BaseEdgeEquiv
      (h14TracePartitionOf h14TraceOneCoordinateMatching
        (h14CanonicalRawPerfectMatching code).1)) r hr C hC]
  exact h14CoordinateContraction_repAtEdge _ _ C hC

/-- Every one of the canonical 105 Wick matchings contracts to the trace
partition certified by the trace-two classifier. -/
theorem h14CoordinateContraction_traceTwo_code_internal
    {p : ℕ} (code : Fin 105) (C : Matrix (Fin p) (Fin p) ℝ)
    (hC : C.IsSymm) :
    h14CoordinateContraction h14TraceTwoEdgeEquiv
        (h14CanonicalRawPerfectMatching code).1 C =
      h14TracePartitionMonomial
        (h14TracePartitionOf h14TraceTwoCoordinateMatching
          (h14CanonicalRawPerfectMatching code).1) C := by
  obtain ⟨r, hr⟩ := h14TraceTwoCanonicalizer_exists code
  rw [h14CoordinateContraction_relabel h14TraceTwoEdgeEquiv
    (h14CanonicalRawPerfectMatching code).1
    (h14RepMatchingAtEdge h14TraceTwoEdgeEquiv
      (h14TracePartitionOf h14TraceTwoCoordinateMatching
        (h14CanonicalRawPerfectMatching code).1)) r hr C hC]
  exact h14CoordinateContraction_repAtEdge _ _ C hC

/-! ## Transport the checked eighth-coordinate Wick rule to matrices -/

private theorem map_flatMatrix_standardRealGaussianVectorMeasure_h14
    (rows p : ℕ) :
    Measure.map (flatMatrixMeasurableEquiv rows p)
        (standardRealGaussianVectorMeasure (rows * p)) =
      standardRealGaussianMatrixMeasure rows p := by
  let mu : Measure ℝ := gaussianReal 0 1
  let reindex : (Fin (rows * p) → ℝ) ≃ᵐ (Fin rows × Fin p → ℝ) :=
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (rows * p) ↦ ℝ)
      (finProdFinEquiv : Fin rows × Fin p ≃ Fin (rows * p))).symm
  let curry : (Fin rows × Fin p → ℝ) ≃ᵐ (Fin rows → Fin p → ℝ) :=
    MeasurableEquiv.curry (Fin rows) (Fin p) ℝ
  have hreindex : Measure.map reindex
      (standardRealGaussianVectorMeasure (rows * p)) =
      Measure.pi (fun _ : Fin rows × Fin p ↦ mu) := by
    have hmp := (measurePreserving_piCongrLeft
      (fun _ : Fin (rows * p) ↦ mu)
      (finProdFinEquiv : Fin rows × Fin p ≃ Fin (rows * p))).symm
    simpa [reindex, mu, standardRealGaussianVectorMeasure] using hmp.map_eq
  have hcurry : Measure.map curry
      (Measure.pi (fun _ : Fin rows × Fin p ↦ mu)) =
      standardRealGaussianMatrixMeasure rows p := by
    unfold standardRealGaussianMatrixMeasure standardRealGaussianVectorMeasure
    rw [← Measure.infinitePi_eq_pi, ← Measure.infinitePi_eq_pi]
    simp_rw [← Measure.infinitePi_eq_pi]
    exact Measure.infinitePi_map_curry
      (fun _ : Fin rows ↦ fun _ : Fin p ↦ mu)
  have hfun : curry ∘ reindex = flatMatrixMeasurableEquiv rows p := by
    funext x
    ext a i
    rfl
  rw [← hcurry, ← hreindex]
  rw [Measure.map_map curry.measurable reindex.measurable]
  rw [hfun]
  rfl

/-- Eight selected entries of a finite standard-Gaussian matrix obey the
same exact compatible-pairing count as the flattened iid vector. -/
theorem integral_standardRealGaussianMatrix_coordinate_eight_pairingCount_h14
    {rows p : ℕ} (a : Fin 8 → Fin rows) (i : Fin 8 → Fin p) :
    (∫ R : Matrix (Fin rows) (Fin p) ℝ,
        ∏ t : Fin 8, R (a t) (i t)
        ∂standardRealGaussianMatrixMeasure rows p) =
      (Nat.card (TypePerfectMatching.Compatible
        (fun t : Fin 8 ↦ finProdFinEquiv (a t, i t))) : ℝ) := by
  rw [← map_flatMatrix_standardRealGaussianVectorMeasure_h14 rows p]
  have hmeas : Measurable
      (fun R : Matrix (Fin rows) (Fin p) ℝ ↦
        ∏ t : Fin 8, R (a t) (i t)) := by
    apply Finset.measurable_prod
    intro t ht
    fun_prop
  rw [integral_map
    (flatMatrixMeasurableEquiv rows p).measurable.aemeasurable
    (show AEStronglyMeasurable
      (fun R : Matrix (Fin rows) (Fin p) ℝ ↦
        ∏ t : Fin 8, R (a t) (i t))
      (Measure.map (flatMatrixMeasurableEquiv rows p)
        (standardRealGaussianVectorMeasure (rows * p))) by
      exact hmeas.aestronglyMeasurable)]
  simpa only [flatMatrixMeasurableEquiv_apply] using
    integral_standardRealGaussianVector_coordinate_eight_pairingCount_h14_low
      (fun t : Fin 8 ↦ finProdFinEquiv (a t, i t))

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

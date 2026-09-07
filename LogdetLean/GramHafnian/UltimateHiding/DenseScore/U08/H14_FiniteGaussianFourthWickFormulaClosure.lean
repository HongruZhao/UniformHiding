import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H14_FiniteGaussianFourthWickFormula

/-!
# Finite Gaussian fourth-Wick closure

This module contracts the checked eighth-coordinate Gaussian Wick rule over
the canonical 105 perfect matchings.  It proves both exact fixed-matrix
Wishart fourth identities and packages them as the literal
`H14FiniteGaussianFourthWickFormula` record used by the H14 consumer.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart

set_option maxRecDepth 100000
set_option maxHeartbeats 3600000

def scratchRowColoring {rows : Nat} (a : Fin 4 -> Fin rows) :
    Fin 8 -> Fin rows :=
  ![a 0, a 0, a 1, a 1, a 2, a 2, a 3, a 3]

@[simp] theorem scratchRowColoring_zero {rows : Nat}
    (a : Fin 4 -> Fin rows) : scratchRowColoring a 0 = a 0 := rfl
@[simp] theorem scratchRowColoring_one {rows : Nat}
    (a : Fin 4 -> Fin rows) : scratchRowColoring a 1 = a 0 := rfl
@[simp] theorem scratchRowColoring_two {rows : Nat}
    (a : Fin 4 -> Fin rows) : scratchRowColoring a 2 = a 1 := rfl
@[simp] theorem scratchRowColoring_three {rows : Nat}
    (a : Fin 4 -> Fin rows) : scratchRowColoring a 3 = a 1 := rfl
@[simp] theorem scratchRowColoring_four {rows : Nat}
    (a : Fin 4 -> Fin rows) : scratchRowColoring a 4 = a 2 := rfl
@[simp] theorem scratchRowColoring_five {rows : Nat}
    (a : Fin 4 -> Fin rows) : scratchRowColoring a 5 = a 2 := rfl
@[simp] theorem scratchRowColoring_six {rows : Nat}
    (a : Fin 4 -> Fin rows) : scratchRowColoring a 6 = a 3 := rfl
@[simp] theorem scratchRowColoring_seven {rows : Nat}
    (a : Fin 4 -> Fin rows) : scratchRowColoring a 7 = a 3 := rfl

@[simp] theorem scratchBaseEdge_00 :
    h14BaseEdgeEquiv ((0 : Fin 4), (0 : Fin 2)) = 0 := rfl
@[simp] theorem scratchBaseEdge_01 :
    h14BaseEdgeEquiv ((0 : Fin 4), (1 : Fin 2)) = 1 := rfl
@[simp] theorem scratchBaseEdge_10 :
    h14BaseEdgeEquiv ((1 : Fin 4), (0 : Fin 2)) = 2 := rfl
@[simp] theorem scratchBaseEdge_11 :
    h14BaseEdgeEquiv ((1 : Fin 4), (1 : Fin 2)) = 3 := rfl
@[simp] theorem scratchBaseEdge_20 :
    h14BaseEdgeEquiv ((2 : Fin 4), (0 : Fin 2)) = 4 := rfl
@[simp] theorem scratchBaseEdge_21 :
    h14BaseEdgeEquiv ((2 : Fin 4), (1 : Fin 2)) = 5 := rfl
@[simp] theorem scratchBaseEdge_30 :
    h14BaseEdgeEquiv ((3 : Fin 4), (0 : Fin 2)) = 6 := rfl
@[simp] theorem scratchBaseEdge_31 :
    h14BaseEdgeEquiv ((3 : Fin 4), (1 : Fin 2)) = 7 := rfl

theorem scratch_integrable_coordinate_eight
    {rows p : Nat} (a : Fin 8 -> Fin rows) (i : Fin 8 -> Fin p) :
    Integrable
      (fun R : Matrix (Fin rows) (Fin p) Real =>
        ∏ t : Fin 8, R (a t) (i t))
      (standardRealGaussianMatrixMeasure rows p) := by
  have hmem : MemLp
      (fun R : Matrix (Fin rows) (Fin p) Real =>
        ∏ t : Fin 8, R (a t) (i t)) 1
      (standardRealGaussianMatrixMeasure rows p) := by
    have h := MemLp.prod'
      (p := fun _ : Fin 8 => (8 : ENNReal))
      (s := Finset.univ)
      (f := fun t => fun R : Matrix (Fin rows) (Fin p) Real =>
        R (a t) (i t))
      (fun t ht => standardRealGaussianMatrix_coordinate_memLp_eight_h14_low
        (a t) (i t))
    convert h using 1
    rw [Fin.sum_univ_eight]
    have hsum : (8 : ENNReal)⁻¹ + 8⁻¹ + 8⁻¹ + 8⁻¹ +
        8⁻¹ + 8⁻¹ + 8⁻¹ + 8⁻¹ = 1 := by
      rw [show (8 : ENNReal)⁻¹ + 8⁻¹ + 8⁻¹ + 8⁻¹ +
          8⁻¹ + 8⁻¹ + 8⁻¹ + 8⁻¹ = (8 : ENNReal)⁻¹ * 8 by ring]
      exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
    rw [hsum, inv_one]
  exact memLp_one_iff_integrable.mp hmem

theorem scratch_integral_wishart_entry_product
    {rows p : Nat} (x : Fin 8 -> Fin p) :
    (∫ R : Matrix (Fin rows) (Fin p) Real,
      ∏ t : Fin 4,
        realWishartGram R (x (h14BaseEdgeEquiv (t, 0)))
          (x (h14BaseEdgeEquiv (t, 1)))
      ∂standardRealGaussianMatrixMeasure rows p) =
    ∑ a : Fin 4 -> Fin rows,
      (Nat.card (TypePerfectMatching.Compatible
        (fun h : Fin 8 =>
          finProdFinEquiv (scratchRowColoring a h, x h))) : Real) := by
  classical
  simp only [realWishartGram, Matrix.mul_apply, Matrix.transpose_apply]
  simp_rw [Fintype.prod_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [show (fun R : Matrix (Fin rows) (Fin p) Real =>
        ∏ t : Fin 4,
          R (a t) (x (h14BaseEdgeEquiv (t, 0))) *
            R (a t) (x (h14BaseEdgeEquiv (t, 1)))) =
        (fun R => ∏ h : Fin 8, R (scratchRowColoring a h) (x h)) by
      funext R
      norm_num [Fin.prod_univ_four, Fin.prod_univ_eight]
      ring]
    exact integral_standardRealGaussianMatrix_coordinate_eight_pairingCount_h14
      (scratchRowColoring a) x
  · intro a ha
    rw [show (fun R : Matrix (Fin rows) (Fin p) Real =>
        ∏ t : Fin 4,
          R (a t) (x (h14BaseEdgeEquiv (t, 0))) *
            R (a t) (x (h14BaseEdgeEquiv (t, 1)))) =
        (fun R => ∏ h : Fin 8, R (scratchRowColoring a h) (x h)) by
      funext R
      norm_num [Fin.prod_univ_four, Fin.prod_univ_eight]
      ring]
    exact scratch_integrable_coordinate_eight (scratchRowColoring a) x

noncomputable def scratchCodeEquiv :
    Fin 105 ≃ TypePerfectMatching (Fin 8) :=
  h14CanonicalRawPerfectMatchingEquiv.trans h14RawPerfectMatchingEquiv

@[simp] theorem scratchCodeEquiv_apply (code : Fin 105) (h : Fin 8) :
    scratchCodeEquiv code h = (h14CanonicalRawPerfectMatching code).1 h := rfl

theorem scratch_natCard_compatible_eq_sum_codes
    {q : Nat} (c : Fin 8 -> Fin q) :
    (Nat.card (TypePerfectMatching.Compatible c) : Real) =
      ∑ code : Fin 105,
        if (∀ h, c ((h14CanonicalRawPerfectMatching code).1 h) = c h)
        then 1 else 0 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [show (((Finset.univ.filter fun M : TypePerfectMatching (Fin 8) =>
      ∀ h, c (M h) = c h).card : Nat) : Real) =
      ∑ M : TypePerfectMatching (Fin 8),
        if (∀ h, c (M h) = c h) then 1 else 0 by
    simpa using (Finset.sum_boole
      (R := Real) (fun M : TypePerfectMatching (Fin 8) =>
        ∀ h, c (M h) = c h) Finset.univ).symm]
  symm
  apply Fintype.sum_equiv scratchCodeEquiv
  intro code
  rfl

noncomputable def scratchMatchingIndicator {q : Nat}
    (sigma : Equiv.Perm (Fin 8)) (x : Fin 8 -> Fin q) : Real :=
  by
    classical
    exact if h14MatchingCompatible sigma x then 1 else 0

noncomputable def scratchRowIndicator {rows : Nat}
    (sigma : Equiv.Perm (Fin 8)) (a : Fin 4 -> Fin rows) : Real :=
  scratchMatchingIndicator sigma (scratchRowColoring a)

noncomputable def scratchRowCount (rows : Nat)
    (sigma : Equiv.Perm (Fin 8)) : Real :=
  ∑ a : Fin 4 -> Fin rows, scratchRowIndicator sigma a

theorem scratch_joint_compatible_iff
    {rows p : Nat} (sigma : Equiv.Perm (Fin 8))
    (a : Fin 4 -> Fin rows) (x : Fin 8 -> Fin p) :
    (∀ h, finProdFinEquiv
        (scratchRowColoring a (sigma h), x (sigma h)) =
      finProdFinEquiv (scratchRowColoring a h, x h)) ↔
      h14MatchingCompatible sigma (scratchRowColoring a) ∧
        h14MatchingCompatible sigma x := by
  constructor
  · intro hjoint
    constructor
    · intro h
      have hh := congrArg
        (fun z : Fin (rows * p) => (finProdFinEquiv.symm z).1)
        (hjoint h)
      simpa using hh
    · intro h
      have hh := congrArg
        (fun z : Fin (rows * p) => (finProdFinEquiv.symm z).2)
        (hjoint h)
      simpa using hh
  · rintro ⟨hrow, hx⟩ h
    exact congrArg finProdFinEquiv (Prod.ext (hrow h) (hx h))

theorem scratch_sum_wick_contraction
    {rows p : Nat}
    (e : (Fin 4 × Fin 2) ≃ Fin 8)
    (C : Matrix (Fin p) (Fin p) Real) :
    (∑ x : Fin 8 -> Fin p,
      h14EdgeCoefficient e C x *
        (∫ R : Matrix (Fin rows) (Fin p) Real,
          ∏ t : Fin 4,
            realWishartGram R (x (h14BaseEdgeEquiv (t, 0)))
              (x (h14BaseEdgeEquiv (t, 1)))
          ∂standardRealGaussianMatrixMeasure rows p)) =
      ∑ code : Fin 105,
        scratchRowCount rows (h14CanonicalRawPerfectMatching code).1 *
          h14CoordinateContraction e
            (h14CanonicalRawPerfectMatching code).1 C := by
  classical
  simp_rw [scratch_integral_wishart_entry_product]
  simp_rw [scratch_natCard_compatible_eq_sum_codes]
  simp_rw [scratch_joint_compatible_iff]
  simp_rw [Finset.mul_sum]
  calc
    (∑ x : Fin 8 -> Fin p, ∑ a : Fin 4 -> Fin rows,
      ∑ code : Fin 105,
        h14EdgeCoefficient e C x *
          (if h14MatchingCompatible
                (h14CanonicalRawPerfectMatching code).1
                (scratchRowColoring a) ∧
              h14MatchingCompatible
                (h14CanonicalRawPerfectMatching code).1 x
            then 1 else 0)) =
        ∑ code : Fin 105, ∑ a : Fin 4 -> Fin rows,
          ∑ x : Fin 8 -> Fin p,
            h14EdgeCoefficient e C x *
              (if h14MatchingCompatible
                    (h14CanonicalRawPerfectMatching code).1
                    (scratchRowColoring a) ∧
                  h14MatchingCompatible
                    (h14CanonicalRawPerfectMatching code).1 x
                then 1 else 0) := by
      calc
        _ = ∑ x : Fin 8 -> Fin p, ∑ code : Fin 105,
            ∑ a : Fin 4 -> Fin rows,
              h14EdgeCoefficient e C x *
                (if h14MatchingCompatible
                      (h14CanonicalRawPerfectMatching code).1
                      (scratchRowColoring a) ∧
                    h14MatchingCompatible
                      (h14CanonicalRawPerfectMatching code).1 x
                  then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.sum_comm]
        _ = _ := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro code hcode
          rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro code hcode
      unfold scratchRowCount h14CoordinateContraction
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hrow : h14MatchingCompatible
          (h14CanonicalRawPerfectMatching code).1 (scratchRowColoring a)
      <;> by_cases hcoord : h14MatchingCompatible
          (h14CanonicalRawPerfectMatching code).1 x
      <;> simp [scratchRowIndicator, scratchMatchingIndicator, hrow, hcoord]

theorem scratchRowColoring_compatible {rows : Nat}
    (a : Fin 4 -> Fin rows) :
    h14MatchingCompatible h14RowMatching (scratchRowColoring a) := by
  intro h
  fin_cases h <;> rfl

@[simp] theorem scratchRowMatching_zero : h14RowMatching 0 = 1 := by decide
@[simp] theorem scratchRowMatching_one : h14RowMatching 1 = 0 := by decide
@[simp] theorem scratchRowMatching_two : h14RowMatching 2 = 3 := by decide
@[simp] theorem scratchRowMatching_three : h14RowMatching 3 = 2 := by decide
@[simp] theorem scratchRowMatching_four : h14RowMatching 4 = 5 := by decide
@[simp] theorem scratchRowMatching_five : h14RowMatching 5 = 4 := by decide
@[simp] theorem scratchRowMatching_six : h14RowMatching 6 = 7 := by decide
@[simp] theorem scratchRowMatching_seven : h14RowMatching 7 = 6 := by decide

noncomputable def scratchRowColoringEquiv (rows : Nat) :
    (Fin 4 -> Fin rows) ≃
      {x : Fin 8 -> Fin rows //
        h14MatchingCompatible h14RowMatching x} where
  toFun a := ⟨scratchRowColoring a, scratchRowColoring_compatible a⟩
  invFun x := fun t => x.1 (h14BaseEdgeEquiv (t, 0))
  left_inv a := by
    funext t
    fin_cases t <;> rfl
  right_inv x := by
    apply Subtype.ext
    funext h
    fin_cases h
    · rfl
    · simpa using x.2 1
    · rfl
    · simpa using x.2 3
    · rfl
    · simpa using x.2 5
    · rfl
    · simpa using x.2 7

theorem scratch_matchingCompatible_row_iff {q : Nat}
    (x : Fin 8 -> Fin q) :
    h14MatchingCompatible h14RowMatching x ↔
      x 0 = x 1 ∧ x 2 = x 3 ∧ x 4 = x 5 ∧ x 6 = x 7 := by
  constructor
  · intro hx
    exact ⟨by simpa using hx 1,
      by simpa using hx 3,
      by simpa using hx 5,
      by simpa using hx 7⟩
  · rintro ⟨h01, h23, h45, h67⟩ h
    fin_cases h <;> simp_all

theorem scratch_edgeCoefficient_one
    {q : Nat} (x : Fin 8 -> Fin q) :
    h14EdgeCoefficient h14BaseEdgeEquiv
        (1 : Matrix (Fin q) (Fin q) Real) x =
      scratchMatchingIndicator h14RowMatching x := by
  classical
  unfold scratchMatchingIndicator
  rw [scratch_matchingCompatible_row_iff]
  simp [h14EdgeCoefficient,
    Fin.prod_univ_four, Matrix.one_apply]
  by_cases h01 : x 0 = x 1 <;> by_cases h23 : x 2 = x 3
  <;> by_cases h45 : x 4 = x 5 <;> by_cases h67 : x 6 = x 7
  <;> simp [h01, h23, h45, h67]

theorem scratchRowCount_eq_contraction_one
    (rows : Nat) (sigma : Equiv.Perm (Fin 8)) :
    scratchRowCount rows sigma =
      h14CoordinateContraction h14BaseEdgeEquiv sigma
        (1 : Matrix (Fin rows) (Fin rows) Real) := by
  classical
  calc
    scratchRowCount rows sigma =
        ∑ y : {x : Fin 8 -> Fin rows //
            h14MatchingCompatible h14RowMatching x},
          if h14MatchingCompatible sigma y.1 then 1 else 0 := by
      unfold scratchRowCount scratchRowIndicator scratchMatchingIndicator
      apply Fintype.sum_equiv (scratchRowColoringEquiv rows)
      intro a
      rfl
    _ = ∑ x : Fin 8 -> Fin rows,
          if h14MatchingCompatible h14RowMatching x then
            (if h14MatchingCompatible sigma x then 1 else 0)
          else 0 := by
      symm
      calc
        (∑ x : Fin 8 -> Fin rows,
            if h14MatchingCompatible h14RowMatching x then
              (if h14MatchingCompatible sigma x then (1 : Real) else 0)
            else 0) =
            ∑ x ∈ (Finset.univ.filter fun x : Fin 8 -> Fin rows =>
              h14MatchingCompatible h14RowMatching x),
              if h14MatchingCompatible sigma x then (1 : Real) else 0 := by
          rw [Finset.sum_filter]
        _ = ∑ y : {x : Fin 8 -> Fin rows //
              h14MatchingCompatible h14RowMatching x},
            if h14MatchingCompatible sigma y.1 then (1 : Real) else 0 := by
          apply Finset.sum_subtype
          intro x
          simp
    _ = _ := by
      unfold h14CoordinateContraction
      apply Finset.sum_congr rfl
      intro x hx
      rw [scratch_edgeCoefficient_one]
      unfold scratchMatchingIndicator
      by_cases hrow : h14MatchingCompatible h14RowMatching x
      <;> by_cases hsigma : h14MatchingCompatible sigma x
      <;> simp [hrow, hsigma]

def scratchTracePartitionExponent (lambda : Fin 5) : Nat :=
  ![4, 3, 2, 2, 1] lambda

theorem scratch_componentCount_eq_partitionExponent :
    ∀ code : Fin 105,
      h14AlternatingComponentCount h14RowMatching
          (h14CanonicalRawPerfectMatching code).1 =
        scratchTracePartitionExponent
          (h14TracePartitionOf h14TraceOneCoordinateMatching
            (h14CanonicalRawPerfectMatching code).1) := by
  decide

theorem scratch_tracePartitionMonomial_one
    (rows : Nat) (lambda : Fin 5) :
    h14TracePartitionMonomial lambda
        (1 : Matrix (Fin rows) (Fin rows) Real) =
      (rows : Real) ^ scratchTracePartitionExponent lambda := by
  fin_cases lambda <;>
    simp [h14TracePartitionMonomial, scratchTracePartitionExponent,
      Matrix.trace_one] <;> ring

theorem scratchRowCount_code
    (rows : Nat) (code : Fin 105) :
    scratchRowCount rows (h14CanonicalRawPerfectMatching code).1 =
      (rows : Real) ^
        h14AlternatingComponentCount h14RowMatching
          (h14CanonicalRawPerfectMatching code).1 := by
  rw [scratchRowCount_eq_contraction_one]
  rw [h14CoordinateContraction_traceOne_code_internal code
    (1 : Matrix (Fin rows) (Fin rows) Real) Matrix.isSymm_one]
  rw [scratch_tracePartitionMonomial_one]
  rw [scratch_componentCount_eq_partitionExponent]

def scratchRowExponents : Finset Nat := {1, 2, 3, 4}

theorem scratch_componentCount_cases :
    ∀ code : Fin 105,
      h14AlternatingComponentCount h14RowMatching
          (h14CanonicalRawPerfectMatching code).1 = 1 ∨
      h14AlternatingComponentCount h14RowMatching
          (h14CanonicalRawPerfectMatching code).1 = 2 ∨
      h14AlternatingComponentCount h14RowMatching
          (h14CanonicalRawPerfectMatching code).1 = 3 ∨
      h14AlternatingComponentCount h14RowMatching
          (h14CanonicalRawPerfectMatching code).1 = 4 := by
  decide

def scratchPairingGraph
    (beta : Equiv.Perm (Fin 8)) (code : Fin 105) : Fin 5 × Nat :=
  (h14TracePartitionOf beta (h14CanonicalRawPerfectMatching code).1,
    h14AlternatingComponentCount h14RowMatching
      (h14CanonicalRawPerfectMatching code).1)

theorem scratch_weighted_pairing_sum_grouped
    (beta : Equiv.Perm (Fin 8)) (rows : Nat)
    {p : Nat} (C : Matrix (Fin p) (Fin p) Real) :
    (∑ code : Fin 105,
      (rows : Real) ^
          h14AlternatingComponentCount h14RowMatching
            (h14CanonicalRawPerfectMatching code).1 *
        h14TracePartitionMonomial
          (h14TracePartitionOf beta
            (h14CanonicalRawPerfectMatching code).1) C) =
      ∑ lambda : Fin 5, ∑ r ∈ scratchRowExponents,
        (h14PairingClassifierCount beta lambda r : Real) *
          (rows : Real) ^ r * h14TracePartitionMonomial lambda C := by
  classical
  let graph : Fin 105 -> Fin 5 × Nat := scratchPairingGraph beta
  let target : Finset (Fin 5 × Nat) :=
    Finset.univ.product scratchRowExponents
  let weight : Fin 105 -> Real := fun code =>
    (rows : Real) ^
        h14AlternatingComponentCount h14RowMatching
          (h14CanonicalRawPerfectMatching code).1 *
      h14TracePartitionMonomial
        (h14TracePartitionOf beta
          (h14CanonicalRawPerfectMatching code).1) C
  have hmaps : ∀ code ∈ (Finset.univ : Finset (Fin 105)),
      graph code ∈ target := by
    intro code hcode
    have hcases := scratch_componentCount_cases code
    rcases hcases with hcase | hcase | hcase | hcase <;>
      simp [target, graph, scratchPairingGraph, scratchRowExponents, hcase]
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin 105))) (t := target)
    (g := graph) hmaps weight
  symm
  calc
    (∑ lambda : Fin 5, ∑ r ∈ scratchRowExponents,
        (h14PairingClassifierCount beta lambda r : Real) *
          (rows : Real) ^ r * h14TracePartitionMonomial lambda C) =
        ∑ z ∈ target, ∑ code ∈ (Finset.univ : Finset (Fin 105)) with
          graph code = z, weight code := by
      change (∑ lambda : Fin 5, ∑ r ∈ scratchRowExponents,
          (h14PairingClassifierCount beta lambda r : Real) *
            (rows : Real) ^ r * h14TracePartitionMonomial lambda C) =
        ∑ z ∈ (Finset.univ : Finset (Fin 5)).product scratchRowExponents,
          ∑ code ∈ (Finset.univ : Finset (Fin 105)) with
            graph code = z, weight code
      have hprod :
          (∑ z ∈ (Finset.univ : Finset (Fin 5)).product scratchRowExponents,
              ∑ code ∈ (Finset.univ : Finset (Fin 105)) with
                graph code = z, weight code) =
            ∑ lambda ∈ (Finset.univ : Finset (Fin 5)),
              ∑ r ∈ scratchRowExponents,
                ∑ code ∈ (Finset.univ : Finset (Fin 105)) with
                  graph code = (lambda, r), weight code := by
        simpa using Finset.sum_product
          (Finset.univ : Finset (Fin 5)) scratchRowExponents
          (fun z => ∑ code ∈ (Finset.univ : Finset (Fin 105)) with
            graph code = z, weight code)
      rw [hprod]
      apply Finset.sum_congr rfl
      intro lambda hlambda
      apply Finset.sum_congr rfl
      intro r hr
      have hcard :
          ((Finset.univ : Finset (Fin 105)).filter fun code =>
              graph code = (lambda, r)).card =
            h14PairingClassifierCount beta lambda r := by
        unfold h14PairingClassifierCount graph scratchPairingGraph
        congr 1
        ext code
        simp [Prod.ext_iff, and_comm]
      rw [← hcard]
      rw [mul_assoc, ← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro code hcode
      have hz : graph code = (lambda, r) :=
        (Finset.mem_filter.mp hcode).2
      have hlambdaCode :
          h14TracePartitionOf beta
              (h14CanonicalRawPerfectMatching code).1 = lambda := by
        exact congrArg Prod.fst hz
      have hrCode :
          h14AlternatingComponentCount h14RowMatching
              (h14CanonicalRawPerfectMatching code).1 = r := by
        exact congrArg Prod.snd hz
      simp only [weight]
      rw [hlambdaCode, hrCode]
    _ = ∑ code ∈ (Finset.univ : Finset (Fin 105)), weight code := hfiber
    _ = _ := by rfl

theorem scratch_weighted_traceOne_sum
    (rows : Nat) {p : Nat} (C : Matrix (Fin p) (Fin p) Real) :
    (∑ code : Fin 105,
      (rows : Real) ^
          h14AlternatingComponentCount h14RowMatching
            (h14CanonicalRawPerfectMatching code).1 *
        h14TracePartitionMonomial
          (h14TracePartitionOf h14TraceOneCoordinateMatching
            (h14CanonicalRawPerfectMatching code).1) C) =
      h14TraceOneFourthWickPolynomial rows C := by
  rw [scratch_weighted_pairing_sum_grouped]
  have h1 (lambda : Fin 5) :
      h14PairingClassifierCount h14TraceOneCoordinateMatching lambda 1 =
        h14TraceOneClassifierExpected lambda 1 := by
    simpa using h14_traceOne_pairing_classifier_table lambda (0 : Fin 4)
  have h2 (lambda : Fin 5) :
      h14PairingClassifierCount h14TraceOneCoordinateMatching lambda 2 =
        h14TraceOneClassifierExpected lambda 2 := by
    simpa using h14_traceOne_pairing_classifier_table lambda (1 : Fin 4)
  have h3 (lambda : Fin 5) :
      h14PairingClassifierCount h14TraceOneCoordinateMatching lambda 3 =
        h14TraceOneClassifierExpected lambda 3 := by
    simpa using h14_traceOne_pairing_classifier_table lambda (2 : Fin 4)
  have h4 (lambda : Fin 5) :
      h14PairingClassifierCount h14TraceOneCoordinateMatching lambda 4 =
        h14TraceOneClassifierExpected lambda 4 := by
    simpa using h14_traceOne_pairing_classifier_table lambda (3 : Fin 4)
  simp [scratchRowExponents]
  rw [Fin.sum_univ_five]
  rw [h1 0, h1 1, h1 2, h1 3, h1 4,
    h2 0, h2 1, h2 2, h2 3, h2 4,
    h3 0, h3 1, h3 2, h3 3, h3 4,
    h4 0, h4 1, h4 2, h4 3, h4 4]
  simp [h14TraceOneClassifierExpected, h14TracePartitionMonomial,
    h14TraceOneFourthWickPolynomial]
  ring

theorem scratch_weighted_traceTwo_sum
    (rows : Nat) {p : Nat} (C : Matrix (Fin p) (Fin p) Real) :
    (∑ code : Fin 105,
      (rows : Real) ^
          h14AlternatingComponentCount h14RowMatching
            (h14CanonicalRawPerfectMatching code).1 *
        h14TracePartitionMonomial
          (h14TracePartitionOf h14TraceTwoCoordinateMatching
            (h14CanonicalRawPerfectMatching code).1) C) =
      h14TraceTwoSquareWickPolynomial rows C := by
  rw [scratch_weighted_pairing_sum_grouped]
  have h1 (lambda : Fin 5) :
      h14PairingClassifierCount h14TraceTwoCoordinateMatching lambda 1 =
        h14TraceTwoClassifierExpected lambda 1 := by
    simpa using h14_traceTwoSquare_pairing_classifier_table lambda (0 : Fin 4)
  have h2 (lambda : Fin 5) :
      h14PairingClassifierCount h14TraceTwoCoordinateMatching lambda 2 =
        h14TraceTwoClassifierExpected lambda 2 := by
    simpa using h14_traceTwoSquare_pairing_classifier_table lambda (1 : Fin 4)
  have h3 (lambda : Fin 5) :
      h14PairingClassifierCount h14TraceTwoCoordinateMatching lambda 3 =
        h14TraceTwoClassifierExpected lambda 3 := by
    simpa using h14_traceTwoSquare_pairing_classifier_table lambda (2 : Fin 4)
  have h4 (lambda : Fin 5) :
      h14PairingClassifierCount h14TraceTwoCoordinateMatching lambda 4 =
        h14TraceTwoClassifierExpected lambda 4 := by
    simpa using h14_traceTwoSquare_pairing_classifier_table lambda (3 : Fin 4)
  simp [scratchRowExponents]
  rw [Fin.sum_univ_five]
  rw [h1 0, h1 1, h1 2, h1 3, h1 4,
    h2 0, h2 1, h2 2, h2 3, h2 4,
    h3 0, h3 1, h3 2, h3 3, h3 4,
    h4 0, h4 1, h4 2, h4 3, h4 4]
  simp [h14TraceTwoClassifierExpected, h14TracePartitionMonomial,
    h14TraceTwoSquareWickPolynomial]
  ring

def scratchEdgeColoring {q : Nat}
    (e : (Fin 4 × Fin 2) ≃ Fin 8)
    (is js : Fin 4 -> Fin q) : Fin 8 -> Fin q :=
  fun h => ![is (e.symm h).1, js (e.symm h).1] (e.symm h).2

noncomputable def scratchEdgeColoringEquiv
    (q : Nat) (e : (Fin 4 × Fin 2) ≃ Fin 8) :
    ((Fin 4 -> Fin q) × (Fin 4 -> Fin q)) ≃ (Fin 8 -> Fin q) where
  toFun z := scratchEdgeColoring e z.1 z.2
  invFun x :=
    (fun t => x (e (t, 0)), fun t => x (e (t, 1)))
  left_inv z := by
    rcases z with ⟨is, js⟩
    apply Prod.ext <;> funext t <;> simp [scratchEdgeColoring]
  right_inv x := by
    funext h
    obtain ⟨ts, rfl⟩ := e.surjective h
    rcases ts with ⟨t, s⟩
    fin_cases s <;> simp [scratchEdgeColoring]

theorem scratch_sum_edgeColoring
    {q : Nat} (e : (Fin 4 × Fin 2) ≃ Fin 8)
    {M : Type*} [AddCommMonoid M] (F : (Fin 8 -> Fin q) -> M) :
    (∑ x, F x) = ∑ is : Fin 4 -> Fin q, ∑ js : Fin 4 -> Fin q,
      F (scratchEdgeColoring e is js) := by
  rw [← (scratchEdgeColoringEquiv q e).sum_comp F]
  simp only [Fintype.sum_prod_type]
  rfl

def scratchFinFourTuple {alpha : Type*}
    (a b c d : alpha) : Fin 4 -> alpha := ![a, b, c, d]

def scratchFinFourFunctionEquiv (alpha : Type*) :
    (Fin 4 -> alpha) ≃ alpha × (alpha × (alpha × alpha)) where
  toFun x := ⟨x 0, x 1, x 2, x 3⟩
  invFun x := scratchFinFourTuple x.1 x.2.1 x.2.2.1 x.2.2.2
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv x := by
    rcases x with ⟨a, b, c, d⟩
    rfl

theorem scratch_sum_finFourFunction
    {alpha M : Type*} [Fintype alpha] [AddCommMonoid M]
    (F : (Fin 4 -> alpha) -> M) :
    (∑ x, F x) = ∑ a, ∑ b, ∑ c, ∑ d,
      F (scratchFinFourTuple a b c d) := by
  rw [← (scratchFinFourFunctionEquiv alpha).symm.sum_comp F]
  simp only [Fintype.sum_prod_type]
  rfl

def scratchInterleavedPair {alpha : Type*}
    (a b c d e f g h : alpha) :
    (Fin 4 -> alpha) × (Fin 4 -> alpha) :=
  (![a, b, e, f], ![d, c, h, g])

def scratchInterleavedPairEquiv (alpha : Type*) :
    ((Fin 4 -> alpha) × (Fin 4 -> alpha)) ≃
      alpha × (alpha × (alpha × (alpha ×
        (alpha × (alpha × (alpha × alpha)))))) where
  toFun z :=
    ⟨z.1 0, z.1 1, z.2 1, z.2 0, z.1 2, z.1 3, z.2 3, z.2 2⟩
  invFun z := scratchInterleavedPair z.1 z.2.1 z.2.2.1 z.2.2.2.1
    z.2.2.2.2.1 z.2.2.2.2.2.1 z.2.2.2.2.2.2.1 z.2.2.2.2.2.2.2
  left_inv z := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  right_inv z := by
    rcases z with ⟨a, b, c, d, e, f, g, h⟩
    rfl

theorem scratch_sum_interleavedPair
    {alpha M : Type*} [Fintype alpha] [AddCommMonoid M]
    (F : (Fin 4 -> alpha) -> (Fin 4 -> alpha) -> M) :
    (∑ is, ∑ js, F is js) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, ∑ g, ∑ h,
        F (scratchInterleavedPair a b c d e f g h).1
          (scratchInterleavedPair a b c d e f g h).2 := by
  rw [← Fintype.sum_prod_type' F]
  rw [← (scratchInterleavedPairEquiv alpha).symm.sum_comp
    (fun z => F z.1 z.2)]
  simp only [Fintype.sum_prod_type]
  rfl

theorem scratch_sum_four_square
    {alpha : Type*} [Fintype alpha]
    (F : alpha -> alpha -> alpha -> alpha -> Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) ^ 2 =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, ∑ g, ∑ h,
        F e f g h * F a b c d := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]

@[simp] theorem scratchTraceTwoEdge_00 :
    h14TraceTwoEdgeEquiv ((0 : Fin 4), (0 : Fin 2)) = 3 := rfl
@[simp] theorem scratchTraceTwoEdge_01 :
    h14TraceTwoEdgeEquiv ((0 : Fin 4), (1 : Fin 2)) = 0 := rfl
@[simp] theorem scratchTraceTwoEdge_10 :
    h14TraceTwoEdgeEquiv ((1 : Fin 4), (0 : Fin 2)) = 1 := rfl
@[simp] theorem scratchTraceTwoEdge_11 :
    h14TraceTwoEdgeEquiv ((1 : Fin 4), (1 : Fin 2)) = 2 := rfl
@[simp] theorem scratchTraceTwoEdge_20 :
    h14TraceTwoEdgeEquiv ((2 : Fin 4), (0 : Fin 2)) = 7 := rfl
@[simp] theorem scratchTraceTwoEdge_21 :
    h14TraceTwoEdgeEquiv ((2 : Fin 4), (1 : Fin 2)) = 4 := rfl
@[simp] theorem scratchTraceTwoEdge_30 :
    h14TraceTwoEdgeEquiv ((3 : Fin 4), (0 : Fin 2)) = 5 := rfl
@[simp] theorem scratchTraceTwoEdge_31 :
    h14TraceTwoEdgeEquiv ((3 : Fin 4), (1 : Fin 2)) = 6 := rfl

theorem scratchEdgeColoring_traceTwo
    {q : Nat} (is js : Fin 4 -> Fin q) :
    scratchEdgeColoring h14TraceTwoEdgeEquiv is js =
      ![js 0, is 1, js 1, is 0, js 2, is 3, js 3, is 2] := by
  funext h
  fin_cases h <;> rfl

theorem scratch_traceOne_fourth_pointwise
    {rows p : Nat} (C : Matrix (Fin p) (Fin p) Real)
    (_hC : C.IsSymm) (R : Matrix (Fin rows) (Fin p) Real) :
    Matrix.trace (C * realWishartGram R) ^ 4 =
      ∑ x : Fin 8 -> Fin p,
        h14EdgeCoefficient h14BaseEdgeEquiv C x *
          ∏ t : Fin 4,
            realWishartGram R (x (h14BaseEdgeEquiv (t, 0)))
              (x (h14BaseEdgeEquiv (t, 1))) := by
  classical
  rw [scratch_sum_edgeColoring h14BaseEdgeEquiv]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro is his
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro js hjs
  have hW : ∀ i j, realWishartGram R j i = realWishartGram R i j :=
    Matrix.IsSymm.ext_iff.mp (realWishartGram_isSymm_h14_low R)
  simp [h14EdgeCoefficient, scratchEdgeColoring,
    Fin.prod_univ_four, h14BaseEdgeEquiv]
  simp_rw [hW]
  ring

theorem scratch_traceTwo_square_pointwise
    {rows p : Nat} (C : Matrix (Fin p) (Fin p) Real)
    (R : Matrix (Fin rows) (Fin p) Real) :
    Matrix.trace ((C * realWishartGram R) ^ 2) ^ 2 =
      ∑ x : Fin 8 -> Fin p,
        h14EdgeCoefficient h14TraceTwoEdgeEquiv C x *
          ∏ t : Fin 4,
            realWishartGram R (x (h14BaseEdgeEquiv (t, 0)))
              (x (h14BaseEdgeEquiv (t, 1))) := by
  classical
  rw [scratch_sum_edgeColoring h14TraceTwoEdgeEquiv]
  rw [scratch_sum_interleavedPair]
  have htrace : Matrix.trace ((C * realWishartGram R) ^ 2) =
      ∑ a, ∑ b, ∑ c, ∑ d,
        C a d * realWishartGram R d b * C b c * realWishartGram R c a := by
    simp only [Matrix.trace, Matrix.diag_apply, pow_two,
      Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    ring
  rw [htrace, scratch_sum_four_square]
  simp_rw [scratchEdgeColoring_traceTwo]
  simp [h14EdgeCoefficient,
    scratchInterleavedPair, Fin.prod_univ_four]
  simp only [mul_assoc, mul_left_comm, mul_comm]

theorem scratch_wick_traceOne_contraction
    {rows p : Nat} (C : Matrix (Fin p) (Fin p) Real)
    (hC : C.IsSymm) :
    (∑ x : Fin 8 -> Fin p,
      h14EdgeCoefficient h14BaseEdgeEquiv C x *
        (∫ R : Matrix (Fin rows) (Fin p) Real,
          ∏ t : Fin 4,
            realWishartGram R (x (h14BaseEdgeEquiv (t, 0)))
              (x (h14BaseEdgeEquiv (t, 1)))
          ∂standardRealGaussianMatrixMeasure rows p)) =
      h14TraceOneFourthWickPolynomial rows C := by
  rw [scratch_sum_wick_contraction]
  simp_rw [scratchRowCount_code]
  simp_rw [h14CoordinateContraction_traceOne_code_internal _ C hC]
  exact scratch_weighted_traceOne_sum rows C

theorem scratch_wick_traceTwo_contraction
    {rows p : Nat} (C : Matrix (Fin p) (Fin p) Real)
    (hC : C.IsSymm) :
    (∑ x : Fin 8 -> Fin p,
      h14EdgeCoefficient h14TraceTwoEdgeEquiv C x *
        (∫ R : Matrix (Fin rows) (Fin p) Real,
          ∏ t : Fin 4,
            realWishartGram R (x (h14BaseEdgeEquiv (t, 0)))
              (x (h14BaseEdgeEquiv (t, 1)))
          ∂standardRealGaussianMatrixMeasure rows p)) =
      h14TraceTwoSquareWickPolynomial rows C := by
  rw [scratch_sum_wick_contraction]
  simp_rw [scratchRowCount_code]
  simp_rw [h14CoordinateContraction_traceTwo_code_internal _ C hC]
  exact scratch_weighted_traceTwo_sum rows C

/-- Exact fourth moment of the trace of a constant symmetric matrix times a
standard real Wishart Gram matrix. -/
theorem integral_trace_const_mul_realWishartGram_fourth_standardGaussian
    {rows p : Nat} (C : Matrix (Fin p) (Fin p) Real)
    (hC : C.IsSymm) :
    (∫ R : Matrix (Fin rows) (Fin p) Real,
        Matrix.trace (C * realWishartGram R) ^ 4
        ∂standardRealGaussianMatrixMeasure rows p) =
      h14TraceOneFourthWickPolynomial rows C := by
  calc
    (∫ R : Matrix (Fin rows) (Fin p) Real,
        Matrix.trace (C * realWishartGram R) ^ 4
        ∂standardRealGaussianMatrixMeasure rows p) =
        ∫ R : Matrix (Fin rows) (Fin p) Real,
          ∑ x : Fin 8 -> Fin p,
            h14EdgeCoefficient h14BaseEdgeEquiv C x *
              ∏ t : Fin 4,
                realWishartGram R (x (h14BaseEdgeEquiv (t, 0)))
                  (x (h14BaseEdgeEquiv (t, 1)))
          ∂standardRealGaussianMatrixMeasure rows p := by
      apply integral_congr_ae
      filter_upwards [] with R
      exact scratch_traceOne_fourth_pointwise C hC R
    _ = ∑ x : Fin 8 -> Fin p,
          ∫ R : Matrix (Fin rows) (Fin p) Real,
            h14EdgeCoefficient h14BaseEdgeEquiv C x *
              ∏ t : Fin 4,
                realWishartGram R (x (h14BaseEdgeEquiv (t, 0)))
                  (x (h14BaseEdgeEquiv (t, 1)))
            ∂standardRealGaussianMatrixMeasure rows p := by
      rw [integral_finsetSum]
      intro x hx
      exact (integrable_realWishartGram_entryProduct_four_h14_low
        (rows := rows)
        (fun t =>
          (x (h14BaseEdgeEquiv (t, 0)),
            x (h14BaseEdgeEquiv (t, 1))))).const_mul _
    _ = ∑ x : Fin 8 -> Fin p,
          h14EdgeCoefficient h14BaseEdgeEquiv C x *
            (∫ R : Matrix (Fin rows) (Fin p) Real,
              ∏ t : Fin 4,
                realWishartGram R (x (h14BaseEdgeEquiv (t, 0)))
                  (x (h14BaseEdgeEquiv (t, 1)))
              ∂standardRealGaussianMatrixMeasure rows p) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [integral_const_mul]
    _ = _ := scratch_wick_traceOne_contraction C hC

/-- Exact second moment of the squared trace of a constant symmetric matrix
times a standard real Wishart Gram matrix. -/
theorem integral_trace_const_mul_realWishartGram_sq_square_standardGaussian
    {rows p : Nat} (C : Matrix (Fin p) (Fin p) Real)
    (hC : C.IsSymm) :
    (∫ R : Matrix (Fin rows) (Fin p) Real,
        Matrix.trace ((C * realWishartGram R) ^ 2) ^ 2
        ∂standardRealGaussianMatrixMeasure rows p) =
      h14TraceTwoSquareWickPolynomial rows C := by
  calc
    (∫ R : Matrix (Fin rows) (Fin p) Real,
        Matrix.trace ((C * realWishartGram R) ^ 2) ^ 2
        ∂standardRealGaussianMatrixMeasure rows p) =
        ∫ R : Matrix (Fin rows) (Fin p) Real,
          ∑ x : Fin 8 -> Fin p,
            h14EdgeCoefficient h14TraceTwoEdgeEquiv C x *
              ∏ t : Fin 4,
                realWishartGram R (x (h14BaseEdgeEquiv (t, 0)))
                  (x (h14BaseEdgeEquiv (t, 1)))
          ∂standardRealGaussianMatrixMeasure rows p := by
      apply integral_congr_ae
      filter_upwards [] with R
      exact scratch_traceTwo_square_pointwise C R
    _ = ∑ x : Fin 8 -> Fin p,
          ∫ R : Matrix (Fin rows) (Fin p) Real,
            h14EdgeCoefficient h14TraceTwoEdgeEquiv C x *
              ∏ t : Fin 4,
                realWishartGram R (x (h14BaseEdgeEquiv (t, 0)))
                  (x (h14BaseEdgeEquiv (t, 1)))
            ∂standardRealGaussianMatrixMeasure rows p := by
      rw [integral_finsetSum]
      intro x hx
      exact (integrable_realWishartGram_entryProduct_four_h14_low
        (rows := rows)
        (fun t =>
          (x (h14BaseEdgeEquiv (t, 0)),
            x (h14BaseEdgeEquiv (t, 1))))).const_mul _
    _ = ∑ x : Fin 8 -> Fin p,
          h14EdgeCoefficient h14TraceTwoEdgeEquiv C x *
            (∫ R : Matrix (Fin rows) (Fin p) Real,
              ∏ t : Fin 4,
                realWishartGram R (x (h14BaseEdgeEquiv (t, 0)))
                  (x (h14BaseEdgeEquiv (t, 1)))
              ∂standardRealGaussianMatrixMeasure rows p) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [integral_const_mul]
    _ = _ := scratch_wick_traceTwo_contraction C hC

/-- The finite-dimensional eighth-coordinate Wick rule, the checked
105-matching classifiers, and the coordinate-contraction canonicalizers
jointly discharge the two exact H14 Gaussian numerator formulas. -/
theorem h14FiniteGaussianFourthWickFormula_internal (N K : Nat) :
    H14FiniteGaussianFourthWickFormula N K := by
  refine ⟨?_, ?_⟩
  · intro H
    calc
      (∫ G : Matrix (Fin (N + 1)) (Fin N) Real,
          betaPrimeTraceOneSource N K (G, H) ^ 4
          ∂standardRealGaussianMatrixMeasure (N + 1) N) =
          ∫ G : Matrix (Fin (N + 1)) (Fin N) Real,
            Matrix.trace
              (scaledInverseWishartMatrix N K H * realWishartGram G) ^ 4
            ∂standardRealGaussianMatrixMeasure (N + 1) N := by
        apply integral_congr_ae
        filter_upwards [] with G
        rw [betaPrimeTraceOneSource_eq_scaledInverseWishart_trace_h14_low]
        simp only [scaledInverseWishartDenominator,
          scaledInverseWishartMatrix]
      _ = _ :=
        integral_trace_const_mul_realWishartGram_fourth_standardGaussian
          (scaledInverseWishartMatrix N K H)
          (scaledInverseWishartMatrix_isSymm_h14_low N K H)
  · intro H
    calc
      (∫ G : Matrix (Fin (N + 1)) (Fin N) Real,
          betaPrimeTraceTwoSource N K (G, H) ^ 2
          ∂standardRealGaussianMatrixMeasure (N + 1) N) =
          ∫ G : Matrix (Fin (N + 1)) (Fin N) Real,
            Matrix.trace
              ((scaledInverseWishartMatrix N K H * realWishartGram G) ^ 2) ^ 2
            ∂standardRealGaussianMatrixMeasure (N + 1) N := by
        apply integral_congr_ae
        filter_upwards [] with G
        rw [betaPrimeTraceTwoSource_eq_scaledInverseWishart_trace_h14_low]
        simp only [scaledInverseWishartDenominator,
          scaledInverseWishartMatrix, pow_two, mul_assoc]
      _ = _ :=
        integral_trace_const_mul_realWishartGram_sq_square_standardGaussian
          (scaledInverseWishartMatrix N K H)
          (scaledInverseWishartMatrix_isSymm_h14_low N K H)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

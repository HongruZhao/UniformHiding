import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H14_FourthRadialIntegrabilityLow
import Mathlib.Data.Fintype.Perm

/-!
# Finite classifier for the H14 fourth-Wick contractions

This module formalizes the finite combinatorial ledger in U10's design-only
blueprint.  It deliberately stops below the analytic contraction evaluator:
there is no beta-prime law, inverse-Wishart input, H6, or H3--H18 endpoint.

The computable subtype below is equivalent to the project's abstract perfect
matchings on eight half-edges.  For each Wick matching it computes the
connected components of the union with the row matching and with either of
the two coordinate matchings.  The two exact tables are then kernel theorems
proved by finite evaluation over all `7!! = 105` matchings.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

open LogdetLean.GramHafnian

set_option maxRecDepth 100000
set_option maxHeartbeats 3600000

abbrev H14HalfEdge := Fin 8

/-- A fully computable presentation of a perfect matching on eight points. -/
def h14IsRawPerfectMatching (sigma : Equiv.Perm H14HalfEdge) : Bool :=
  decide ((∀ i, sigma i ≠ i) ∧ ∀ i, sigma (sigma i) = i)

abbrev H14RawPerfectMatching :=
  {sigma : Equiv.Perm H14HalfEdge // h14IsRawPerfectMatching sigma = true}

/-- The computable matching subtype is exactly the abstract project type. -/
def h14RawPerfectMatchingEquiv :
    H14RawPerfectMatching ≃ TypePerfectMatching H14HalfEdge where
  toFun sigma := by
    have hsigma : (∀ i, sigma.1 i ≠ i) ∧ ∀ i, sigma.1 (sigma.1 i) = i :=
      of_decide_eq_true sigma.2
    exact
      { mate := sigma.1
        mate_ne := hsigma.1
        mate_mate := hsigma.2 }
  invFun M :=
    ⟨M.mate, by
      exact decide_eq_true (And.intro M.mate_ne M.mate_mate)⟩
  left_inv sigma := by
    apply Subtype.ext
    rfl
  right_inv M := by
    cases M
    rfl

/-- The common row matching `(01)(23)(45)(67)`. -/
def h14RowMatching : Equiv.Perm H14HalfEdge :=
  Equiv.swap 0 1 * Equiv.swap 2 3 *
    Equiv.swap 4 5 * Equiv.swap 6 7

/-- Coordinate matching for the fourth power of the first trace. -/
def h14TraceOneCoordinateMatching : Equiv.Perm H14HalfEdge :=
  h14RowMatching

/-- Coordinate matching for the square of the second trace. -/
def h14TraceTwoCoordinateMatching : Equiv.Perm H14HalfEdge :=
  Equiv.swap 0 3 * Equiv.swap 1 2 *
    Equiv.swap 4 7 * Equiv.swap 5 6

/-- The orbit in the union of two perfect matchings.  Alternating paths are
`(alpha*beta)^n i` or `alpha ((alpha*beta)^n i)`; eight powers suffice on
eight vertices. -/
def h14AlternatingOrbit (alpha beta : Equiv.Perm H14HalfEdge)
    (i : H14HalfEdge) : Finset H14HalfEdge :=
  Finset.univ.filter fun j =>
    ∃ n : Fin 8,
      ((alpha * beta) ^ (n : Nat)) i = j ∨
        alpha (((alpha * beta) ^ (n : Nat)) i) = j

/-- The least vertex is the canonical representative of an alternating
component.  This is Boolean so the classifier remains executable. -/
def h14IsAlternatingComponentRep
    (alpha beta : Equiv.Perm H14HalfEdge) (i : H14HalfEdge) : Bool :=
  decide (∀ j ∈ h14AlternatingOrbit alpha beta i, i ≤ j)

/-- Number of connected components in the union of two matchings. -/
def h14AlternatingComponentCount
    (alpha beta : Equiv.Perm H14HalfEdge) : Nat :=
  (Finset.univ.filter
    (fun i => h14IsAlternatingComponentRep alpha beta i = true)).card

/-- Number of alternating components having `2*q` vertices. -/
def h14AlternatingHalfSizeCount
    (alpha beta : Equiv.Perm H14HalfEdge) (q : Nat) : Nat :=
  (Finset.univ.filter fun i =>
    h14IsAlternatingComponentRep alpha beta i = true ∧
      (h14AlternatingOrbit alpha beta i).card / 2 = q).card

/-- The five trace partitions of four, ordered as in the H14 polynomials. -/
abbrev H14TracePartitionFour := Fin 5

/-- Trace partition obtained from the coordinate-matching union. -/
def h14TracePartitionOf
    (beta sigma : Equiv.Perm H14HalfEdge) : H14TracePartitionFour :=
  let n1 := h14AlternatingHalfSizeCount beta sigma 1
  let n2 := h14AlternatingHalfSizeCount beta sigma 2
  let n3 := h14AlternatingHalfSizeCount beta sigma 3
  if n1 = 4 then 0
  else if n1 = 2 ∧ n2 = 1 then 1
  else if n2 = 2 then 2
  else if n1 = 1 ∧ n3 = 1 then 3
  else 4

/-- Build a computable raw matching from its eight mate values. -/
private def h14RawPerfectMatchingOfVector
    (v : H14HalfEdge → H14HalfEdge)
    (h : (∀ i, v i ≠ i) ∧ ∀ i, v (v i) = i) :
    H14RawPerfectMatching := by
  have hinv : Function.Involutive v := h.2
  let sigma : Equiv.Perm H14HalfEdge := hinv.toPerm
  refine ⟨sigma, ?_⟩
  exact decide_eq_true (by simpa [sigma] using h)

/-- The canonical recursive list of all `7!! = 105` matchings.  The order is:
pair the least unused vertex with each later vertex, then recurse.  Unlike
enumeration through all `8!` permutations, this closed table is small enough
for kernel reduction. -/
def h14CanonicalRawPerfectMatching : Fin 105 → H14RawPerfectMatching :=
![
    h14RawPerfectMatchingOfVector ![1, 0, 3, 2, 5, 4, 7, 6] (by decide),
    h14RawPerfectMatchingOfVector ![1, 0, 3, 2, 6, 7, 4, 5] (by decide),
    h14RawPerfectMatchingOfVector ![1, 0, 3, 2, 7, 6, 5, 4] (by decide),
    h14RawPerfectMatchingOfVector ![1, 0, 4, 5, 2, 3, 7, 6] (by decide),
    h14RawPerfectMatchingOfVector ![1, 0, 4, 6, 2, 7, 3, 5] (by decide),
    h14RawPerfectMatchingOfVector ![1, 0, 4, 7, 2, 6, 5, 3] (by decide),
    h14RawPerfectMatchingOfVector ![1, 0, 5, 4, 3, 2, 7, 6] (by decide),
    h14RawPerfectMatchingOfVector ![1, 0, 5, 6, 7, 2, 3, 4] (by decide),
    h14RawPerfectMatchingOfVector ![1, 0, 5, 7, 6, 2, 4, 3] (by decide),
    h14RawPerfectMatchingOfVector ![1, 0, 6, 4, 3, 7, 2, 5] (by decide),
    h14RawPerfectMatchingOfVector ![1, 0, 6, 5, 7, 3, 2, 4] (by decide),
    h14RawPerfectMatchingOfVector ![1, 0, 6, 7, 5, 4, 2, 3] (by decide),
    h14RawPerfectMatchingOfVector ![1, 0, 7, 4, 3, 6, 5, 2] (by decide),
    h14RawPerfectMatchingOfVector ![1, 0, 7, 5, 6, 3, 4, 2] (by decide),
    h14RawPerfectMatchingOfVector ![1, 0, 7, 6, 5, 4, 3, 2] (by decide),
    h14RawPerfectMatchingOfVector ![2, 3, 0, 1, 5, 4, 7, 6] (by decide),
    h14RawPerfectMatchingOfVector ![2, 3, 0, 1, 6, 7, 4, 5] (by decide),
    h14RawPerfectMatchingOfVector ![2, 3, 0, 1, 7, 6, 5, 4] (by decide),
    h14RawPerfectMatchingOfVector ![2, 4, 0, 5, 1, 3, 7, 6] (by decide),
    h14RawPerfectMatchingOfVector ![2, 4, 0, 6, 1, 7, 3, 5] (by decide),
    h14RawPerfectMatchingOfVector ![2, 4, 0, 7, 1, 6, 5, 3] (by decide),
    h14RawPerfectMatchingOfVector ![2, 5, 0, 4, 3, 1, 7, 6] (by decide),
    h14RawPerfectMatchingOfVector ![2, 5, 0, 6, 7, 1, 3, 4] (by decide),
    h14RawPerfectMatchingOfVector ![2, 5, 0, 7, 6, 1, 4, 3] (by decide),
    h14RawPerfectMatchingOfVector ![2, 6, 0, 4, 3, 7, 1, 5] (by decide),
    h14RawPerfectMatchingOfVector ![2, 6, 0, 5, 7, 3, 1, 4] (by decide),
    h14RawPerfectMatchingOfVector ![2, 6, 0, 7, 5, 4, 1, 3] (by decide),
    h14RawPerfectMatchingOfVector ![2, 7, 0, 4, 3, 6, 5, 1] (by decide),
    h14RawPerfectMatchingOfVector ![2, 7, 0, 5, 6, 3, 4, 1] (by decide),
    h14RawPerfectMatchingOfVector ![2, 7, 0, 6, 5, 4, 3, 1] (by decide),
    h14RawPerfectMatchingOfVector ![3, 2, 1, 0, 5, 4, 7, 6] (by decide),
    h14RawPerfectMatchingOfVector ![3, 2, 1, 0, 6, 7, 4, 5] (by decide),
    h14RawPerfectMatchingOfVector ![3, 2, 1, 0, 7, 6, 5, 4] (by decide),
    h14RawPerfectMatchingOfVector ![3, 4, 5, 0, 1, 2, 7, 6] (by decide),
    h14RawPerfectMatchingOfVector ![3, 4, 6, 0, 1, 7, 2, 5] (by decide),
    h14RawPerfectMatchingOfVector ![3, 4, 7, 0, 1, 6, 5, 2] (by decide),
    h14RawPerfectMatchingOfVector ![3, 5, 4, 0, 2, 1, 7, 6] (by decide),
    h14RawPerfectMatchingOfVector ![3, 5, 6, 0, 7, 1, 2, 4] (by decide),
    h14RawPerfectMatchingOfVector ![3, 5, 7, 0, 6, 1, 4, 2] (by decide),
    h14RawPerfectMatchingOfVector ![3, 6, 4, 0, 2, 7, 1, 5] (by decide),
    h14RawPerfectMatchingOfVector ![3, 6, 5, 0, 7, 2, 1, 4] (by decide),
    h14RawPerfectMatchingOfVector ![3, 6, 7, 0, 5, 4, 1, 2] (by decide),
    h14RawPerfectMatchingOfVector ![3, 7, 4, 0, 2, 6, 5, 1] (by decide),
    h14RawPerfectMatchingOfVector ![3, 7, 5, 0, 6, 2, 4, 1] (by decide),
    h14RawPerfectMatchingOfVector ![3, 7, 6, 0, 5, 4, 2, 1] (by decide),
    h14RawPerfectMatchingOfVector ![4, 2, 1, 5, 0, 3, 7, 6] (by decide),
    h14RawPerfectMatchingOfVector ![4, 2, 1, 6, 0, 7, 3, 5] (by decide),
    h14RawPerfectMatchingOfVector ![4, 2, 1, 7, 0, 6, 5, 3] (by decide),
    h14RawPerfectMatchingOfVector ![4, 3, 5, 1, 0, 2, 7, 6] (by decide),
    h14RawPerfectMatchingOfVector ![4, 3, 6, 1, 0, 7, 2, 5] (by decide),
    h14RawPerfectMatchingOfVector ![4, 3, 7, 1, 0, 6, 5, 2] (by decide),
    h14RawPerfectMatchingOfVector ![4, 5, 3, 2, 0, 1, 7, 6] (by decide),
    h14RawPerfectMatchingOfVector ![4, 5, 6, 7, 0, 1, 2, 3] (by decide),
    h14RawPerfectMatchingOfVector ![4, 5, 7, 6, 0, 1, 3, 2] (by decide),
    h14RawPerfectMatchingOfVector ![4, 6, 3, 2, 0, 7, 1, 5] (by decide),
    h14RawPerfectMatchingOfVector ![4, 6, 5, 7, 0, 2, 1, 3] (by decide),
    h14RawPerfectMatchingOfVector ![4, 6, 7, 5, 0, 3, 1, 2] (by decide),
    h14RawPerfectMatchingOfVector ![4, 7, 3, 2, 0, 6, 5, 1] (by decide),
    h14RawPerfectMatchingOfVector ![4, 7, 5, 6, 0, 2, 3, 1] (by decide),
    h14RawPerfectMatchingOfVector ![4, 7, 6, 5, 0, 3, 2, 1] (by decide),
    h14RawPerfectMatchingOfVector ![5, 2, 1, 4, 3, 0, 7, 6] (by decide),
    h14RawPerfectMatchingOfVector ![5, 2, 1, 6, 7, 0, 3, 4] (by decide),
    h14RawPerfectMatchingOfVector ![5, 2, 1, 7, 6, 0, 4, 3] (by decide),
    h14RawPerfectMatchingOfVector ![5, 3, 4, 1, 2, 0, 7, 6] (by decide),
    h14RawPerfectMatchingOfVector ![5, 3, 6, 1, 7, 0, 2, 4] (by decide),
    h14RawPerfectMatchingOfVector ![5, 3, 7, 1, 6, 0, 4, 2] (by decide),
    h14RawPerfectMatchingOfVector ![5, 4, 3, 2, 1, 0, 7, 6] (by decide),
    h14RawPerfectMatchingOfVector ![5, 4, 6, 7, 1, 0, 2, 3] (by decide),
    h14RawPerfectMatchingOfVector ![5, 4, 7, 6, 1, 0, 3, 2] (by decide),
    h14RawPerfectMatchingOfVector ![5, 6, 3, 2, 7, 0, 1, 4] (by decide),
    h14RawPerfectMatchingOfVector ![5, 6, 4, 7, 2, 0, 1, 3] (by decide),
    h14RawPerfectMatchingOfVector ![5, 6, 7, 4, 3, 0, 1, 2] (by decide),
    h14RawPerfectMatchingOfVector ![5, 7, 3, 2, 6, 0, 4, 1] (by decide),
    h14RawPerfectMatchingOfVector ![5, 7, 4, 6, 2, 0, 3, 1] (by decide),
    h14RawPerfectMatchingOfVector ![5, 7, 6, 4, 3, 0, 2, 1] (by decide),
    h14RawPerfectMatchingOfVector ![6, 2, 1, 4, 3, 7, 0, 5] (by decide),
    h14RawPerfectMatchingOfVector ![6, 2, 1, 5, 7, 3, 0, 4] (by decide),
    h14RawPerfectMatchingOfVector ![6, 2, 1, 7, 5, 4, 0, 3] (by decide),
    h14RawPerfectMatchingOfVector ![6, 3, 4, 1, 2, 7, 0, 5] (by decide),
    h14RawPerfectMatchingOfVector ![6, 3, 5, 1, 7, 2, 0, 4] (by decide),
    h14RawPerfectMatchingOfVector ![6, 3, 7, 1, 5, 4, 0, 2] (by decide),
    h14RawPerfectMatchingOfVector ![6, 4, 3, 2, 1, 7, 0, 5] (by decide),
    h14RawPerfectMatchingOfVector ![6, 4, 5, 7, 1, 2, 0, 3] (by decide),
    h14RawPerfectMatchingOfVector ![6, 4, 7, 5, 1, 3, 0, 2] (by decide),
    h14RawPerfectMatchingOfVector ![6, 5, 3, 2, 7, 1, 0, 4] (by decide),
    h14RawPerfectMatchingOfVector ![6, 5, 4, 7, 2, 1, 0, 3] (by decide),
    h14RawPerfectMatchingOfVector ![6, 5, 7, 4, 3, 1, 0, 2] (by decide),
    h14RawPerfectMatchingOfVector ![6, 7, 3, 2, 5, 4, 0, 1] (by decide),
    h14RawPerfectMatchingOfVector ![6, 7, 4, 5, 2, 3, 0, 1] (by decide),
    h14RawPerfectMatchingOfVector ![6, 7, 5, 4, 3, 2, 0, 1] (by decide),
    h14RawPerfectMatchingOfVector ![7, 2, 1, 4, 3, 6, 5, 0] (by decide),
    h14RawPerfectMatchingOfVector ![7, 2, 1, 5, 6, 3, 4, 0] (by decide),
    h14RawPerfectMatchingOfVector ![7, 2, 1, 6, 5, 4, 3, 0] (by decide),
    h14RawPerfectMatchingOfVector ![7, 3, 4, 1, 2, 6, 5, 0] (by decide),
    h14RawPerfectMatchingOfVector ![7, 3, 5, 1, 6, 2, 4, 0] (by decide),
    h14RawPerfectMatchingOfVector ![7, 3, 6, 1, 5, 4, 2, 0] (by decide),
    h14RawPerfectMatchingOfVector ![7, 4, 3, 2, 1, 6, 5, 0] (by decide),
    h14RawPerfectMatchingOfVector ![7, 4, 5, 6, 1, 2, 3, 0] (by decide),
    h14RawPerfectMatchingOfVector ![7, 4, 6, 5, 1, 3, 2, 0] (by decide),
    h14RawPerfectMatchingOfVector ![7, 5, 3, 2, 6, 1, 4, 0] (by decide),
    h14RawPerfectMatchingOfVector ![7, 5, 4, 6, 2, 1, 3, 0] (by decide),
    h14RawPerfectMatchingOfVector ![7, 5, 6, 4, 3, 1, 2, 0] (by decide),
    h14RawPerfectMatchingOfVector ![7, 6, 3, 2, 5, 4, 1, 0] (by decide),
    h14RawPerfectMatchingOfVector ![7, 6, 4, 5, 2, 3, 1, 0] (by decide),
    h14RawPerfectMatchingOfVector ![7, 6, 5, 4, 3, 2, 1, 0] (by decide)
  ]

private theorem h14CanonicalRawPerfectMatching_injective :
    Function.Injective h14CanonicalRawPerfectMatching := by
  decide

/-- Joint classifier count by trace partition and row-component exponent.
The enumeration runs over the canonical `7!! = 105` matchings directly. -/
def h14PairingClassifierCount
    (beta : Equiv.Perm H14HalfEdge)
    (lambda : H14TracePartitionFour) (rowExponent : Nat) : Nat :=
  ((Finset.univ : Finset (Fin 105)).filter fun code =>
    let sigma := (h14CanonicalRawPerfectMatching code).1
    h14TracePartitionOf beta sigma = lambda ∧
      h14AlternatingComponentCount h14RowMatching sigma =
        rowExponent).card

/-- Expected trace-one table: the five nonzero cells are
`1,12,12,32,48`. -/
def h14TraceOneClassifierExpected
    (lambda : H14TracePartitionFour) (rowExponent : Nat) : Nat :=
  if lambda = 0 then if rowExponent = 4 then 1 else 0
  else if lambda = 1 then if rowExponent = 3 then 12 else 0
  else if lambda = 2 then if rowExponent = 2 then 12 else 0
  else if lambda = 3 then if rowExponent = 2 then 32 else 0
  else if rowExponent = 1 then 48 else 0

/-- Expected joint trace-two/row table from the transparent row-intersection
classification in the blueprint. -/
def h14TraceTwoClassifierExpected
    (lambda : H14TracePartitionFour) (rowExponent : Nat) : Nat :=
  if lambda = 0 then if rowExponent = 2 then 1 else 0
  else if lambda = 1 then
      if rowExponent = 3 then 2
      else if rowExponent = 2 then 2
      else if rowExponent = 1 then 8 else 0
  else if lambda = 2 then
      if rowExponent = 4 then 1
      else if rowExponent = 3 then 2
      else if rowExponent = 2 then 5
      else if rowExponent = 1 then 4 else 0
  else if lambda = 3 then
      if rowExponent = 2 then 16
      else if rowExponent = 1 then 16 else 0
  else
      if rowExponent = 3 then 8
      else if rowExponent = 2 then 20
      else if rowExponent = 1 then 20 else 0

/-- There are exactly `7!! = 105` computable matchings. -/
theorem h14RawPerfectMatching_card :
    Fintype.card H14RawPerfectMatching = 105 := by
  calc
    Fintype.card H14RawPerfectMatching =
        Fintype.card (TypePerfectMatching H14HalfEdge) :=
      Fintype.card_congr h14RawPerfectMatchingEquiv
    _ = Fintype.card (PerfectMatching 4) := by
      simpa using
        (Fintype.card_congr (TypePerfectMatching.finEquiv 4)).symm
    _ = 105 := by
      rw [TypePerfectMatching.card_perfectMatching]
      norm_num [Nat.doubleFactorial]

private theorem h14CanonicalRawPerfectMatching_bijective :
    Function.Bijective h14CanonicalRawPerfectMatching := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · exact h14CanonicalRawPerfectMatching_injective
  · rw [Fintype.card_fin, h14RawPerfectMatching_card]

/-- Equivalence certifying that the executable 105-entry ledger is exhaustive. -/
noncomputable def h14CanonicalRawPerfectMatchingEquiv :
    Fin 105 ≃ H14RawPerfectMatching :=
  Equiv.ofBijective h14CanonicalRawPerfectMatching
    h14CanonicalRawPerfectMatching_bijective

/-- Exact five-cell classifier for `Q1^4`.  The quantified `Fin 4` column
encodes row exponents `1,2,3,4`. -/
theorem h14_traceOne_pairing_classifier_table :
    ∀ lambda : H14TracePartitionFour, ∀ r : Fin 4,
      h14PairingClassifierCount h14TraceOneCoordinateMatching
          lambda (r + 1) =
        h14TraceOneClassifierExpected lambda (r + 1) := by
  decide

/-- Exact `5 x 4` joint classifier for `Q2^2`. -/
theorem h14_traceTwoSquare_pairing_classifier_table :
    ∀ lambda : H14TracePartitionFour, ∀ r : Fin 4,
      h14PairingClassifierCount h14TraceTwoCoordinateMatching
          lambda (r + 1) =
        h14TraceTwoClassifierExpected lambda (r + 1) := by
  decide

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

import LogdetLean.GramHafnian.PerfectMatching

/-!
# Approved A4: Matsumoto, Theorem 3, in paper variables

This module installs the already-approved literature atom A4 exactly on the
paper side.  In particular, the axiom contains no Gaussian/project variable
and no H12/H14 substitution.

Source: S. Matsumoto, "General Moments of the Inverse Real Wishart
Distribution and Orthogonal Weingarten Functions", J. Theoret. Probab. 25
(2012), 798-822, Theorem 3 on printed page 819.  The definitions below follow
the Wishart notation on printed page 799, matchings and `kappa` on printed
pages 809-811, orthogonal Weingarten notation on printed pages 811 and 814,
and `T_g` on printed page 817.
-/

open scoped BigOperators Matrix
open MeasureTheory

noncomputable section

namespace MatsumotoPaper

/-- A real `d x d` matrix in Matsumoto's paper variables. -/
abbrev RealMatrix (d : Nat) := Matrix (Fin d) (Fin d) Real

/-- A complex `d x d` matrix in Matsumoto's paper variables. -/
abbrev ComplexMatrix (d : Nat) := Matrix (Fin d) (Fin d) Complex

/-- The finite-dimensional Borel measurable structure on real matrices. -/
instance (d : Nat) : MeasurableSpace (RealMatrix d) :=
  borel (RealMatrix d)

/-- The paper's real symmetric-matrix space `Sym(d)`. -/
abbrev Sym (d : Nat) := {x : RealMatrix d // x.IsSymm}

/-- The paper's positive-definite cone `Omega = Sym^+(d)`. -/
abbrev SymPosDef (d : Nat) := {x : RealMatrix d // x.PosDef}

instance (d : Nat) : MeasurableSpace (SymPosDef d) :=
  MeasurableSpace.comap Subtype.val inferInstance

namespace SymPosDef

/-- Matrix inversion inside `Sym^+(d)`. -/
def inverse {d : Nat} (sigma : SymPosDef d) : SymPosDef d :=
  ⟨sigma.1⁻¹, sigma.2.inv⟩

end SymPosDef

/-- Matsumoto's `etr(A) = exp(tr(A))`. -/
def etr {d : Nat} (A : RealMatrix d) : Real :=
  Real.exp (Matrix.trace A)

/--
The real Wishart law `W_d(beta, sigma; R)`, characterized exactly as in
equation (1.1) of the paper.  A value of this structure is the law denoted by
`W ~ W_d(beta, sigma; R)`; existence/admissibility is carried by the value,
not postulated as another axiom.
-/
structure W_d (d : Nat) (beta : Real) (sigma : SymPosDef d) where
  toMeasure : Measure (SymPosDef d)
  probability : IsProbabilityMeasure toMeasure
  laplace_transform :
    ∀ theta : Sym d,
      (sigma.1⁻¹ - theta.1).PosDef →
        (∫ w : SymPosDef d, etr (theta.1 * w.1) ∂toMeasure) =
          Real.rpow (Matrix.det (1 - theta.1 * sigma.1)) (-beta)

/-- Expectation with respect to `W ~ W_d(beta, sigma; R)`. -/
def expectation {d : Nat} {beta : Real} {sigma : SymPosDef d}
    (W : W_d d beta sigma) (F : SymPosDef d → Complex) : Complex :=
  ∫ w, F w ∂W.toMeasure

/-- Zero-based version of the paper position `2i-1`. -/
def leftSlot {n : Nat} (i : Fin n) : Fin (2 * n) :=
  ⟨2 * i.1, by omega⟩

/-- Zero-based version of the paper position `2i`. -/
def rightSlot {n : Nat} (i : Fin n) : Fin (2 * n) :=
  ⟨2 * i.1 + 1, by omega⟩

/--
Matsumoto's multilinear contraction `T_g(x; m_1, ..., m_n)` from printed
page 817, with the paper's one-based indices represented by `Fin`.
-/
def T {d n : Nat} (g : Equiv.Perm (Fin (2 * n)))
    (x : RealMatrix d) (m : Fin n → ComplexMatrix d) : Complex :=
  ∑ j : Fin (2 * n) → Fin d,
    (∏ i : Fin n, m i (j (leftSlot i)) (j (rightSlot i))) *
      ∏ i : Fin n,
        ((x (j (g (leftSlot i))) (j (g (rightSlot i))) : Real) : Complex)

/--
The canonical embedding of a perfect matching into `S_(2n)` used in (4.1):
each pair is increasing, the first endpoint is zero (paper endpoint one), and
the first endpoints are increasing.
-/
def IsCanonicalMatching {n : Nat}
    (matching : Equiv.Perm (Fin (2 * n))) : Prop :=
  (∀ i : Fin n, matching (leftSlot i) < matching (rightSlot i)) ∧
  (∀ hn : 0 < n,
    matching (leftSlot (⟨0, hn⟩ : Fin n)) = ⟨0, by omega⟩) ∧
  (∀ i j : Fin n, i < j →
    matching (leftSlot i) < matching (leftSlot j))

/-- The paper's canonical matching set `M(2n)`, not a project-variable sum. -/
def PerfectMatching (n : Nat) :=
  {matching : Equiv.Perm (Fin (2 * n)) // IsCanonicalMatching matching}

namespace PerfectMatching

/-- The canonical permutation attached to a paper matching. -/
def toPerm {n : Nat} (matching : PerfectMatching n) :
    Equiv.Perm (Fin (2 * n)) :=
  matching.1

instance (n : Nat) : Finite (PerfectMatching n) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance (n : Nat) : Fintype (PerfectMatching n) :=
  Fintype.ofFinite _

end PerfectMatching

private abbrev PairPartition (n : Nat) :=
  LogdetLean.GramHafnian.PerfectMatching n

private def mulCommFinEquiv (n : Nat) : Fin (n * 2) ≃ Fin (2 * n) where
  toFun i := ⟨i.1, by omega⟩
  invFun i := ⟨i.1, by omega⟩
  left_inv i := Fin.ext rfl
  right_inv i := Fin.ext rfl

private def pairCoordinateEquiv (n : Nat) :
    Fin n × Fin 2 ≃ Fin (2 * n) :=
  (finProdFinEquiv : Fin n × Fin 2 ≃ Fin (n * 2)).trans
    (mulCommFinEquiv n)

private def finTwoSwap : Equiv.Perm (Fin 2) :=
  Equiv.swap 0 1

private theorem finTwoSwap_ne (i : Fin 2) : finTwoSwap i ≠ i := by
  fin_cases i <;> decide

private theorem finTwoSwap_involutive (i : Fin 2) :
    finTwoSwap (finTwoSwap i) = i := by
  fin_cases i <;> decide

private def pairFlip (n : Nat) : Equiv.Perm (Fin n × Fin 2) :=
  Equiv.prodCongr (Equiv.refl (Fin n)) finTwoSwap

private theorem pairFlip_ne {n : Nat} (p : Fin n × Fin 2) :
    pairFlip n p ≠ p := by
  intro h
  apply finTwoSwap_ne p.2
  simpa [pairFlip] using congrArg Prod.snd h

private theorem pairFlip_involutive {n : Nat} (p : Fin n × Fin 2) :
    pairFlip n (pairFlip n p) = p := by
  apply Prod.ext
  · simp [pairFlip]
  · simpa [pairFlip] using finTwoSwap_involutive p.2

private def standardMatePerm (n : Nat) : Equiv.Perm (Fin (2 * n)) :=
  ((pairCoordinateEquiv n).symm.trans (pairFlip n)).trans
    (pairCoordinateEquiv n)

private def standardPairPartition (n : Nat) : PairPartition n where
  mate := standardMatePerm n
  mate_ne := by
    intro i hi
    apply pairFlip_ne ((pairCoordinateEquiv n).symm i)
    have h := congrArg (pairCoordinateEquiv n).symm hi
    simpa [standardMatePerm] using h
  mate_mate := by
    intro i
    apply (pairCoordinateEquiv n).symm.injective
    simpa [standardMatePerm] using
      pairFlip_involutive ((pairCoordinateEquiv n).symm i)

private def transportPairPartition {n : Nat}
    (g : Equiv.Perm (Fin (2 * n))) (M : PairPartition n) :
    PairPartition n where
  mate := (g.symm.trans M.mate).trans g
  mate_ne := by
    intro i hi
    apply M.mate_ne (g.symm i)
    have h := congrArg g.symm hi
    simpa using h
  mate_mate := by
    intro i
    simp

private def transportedPairPartition {n : Nat}
    (g : Equiv.Perm (Fin (2 * n))) : PairPartition n :=
  transportPairPartition g (standardPairPartition n)

/-- Adjacency in the union of two perfect matchings. -/
def matchingAdjacent {n : Nat} (M N : PairPartition n)
    (i j : Fin (2 * n)) : Prop :=
  M i = j ∨ N i = j

/-- The vertex set of one connected component of the union graph. -/
noncomputable def componentVertices {n : Nat} (M N : PairPartition n)
    (i : Fin (2 * n)) : Finset (Fin (2 * n)) := by
  classical
  exact Finset.univ.filter fun j =>
    Relation.ReflTransGen (matchingAdjacent M N) i j

/-- Number of connected components in the union of two perfect matchings. -/
noncomputable def matchingKappa {n : Nat} (M N : PairPartition n) : Nat := by
  classical
  exact (Finset.univ.image (componentVertices M N)).card

/--
Matsumoto's `kappa(g)`: the number of components of the graph with fixed
pair edges and the edges transported by `g` (printed pages 809-810).
-/
noncomputable def kappa {n : Nat}
    (g : Equiv.Perm (Fin (2 * n))) : Nat :=
  matchingKappa (standardPairPartition n) (transportedPairPartition g)

/-- The orthogonal perfect-matching Gram matrix at parameter `z`. -/
noncomputable def orthogonalGram (n : Nat) (z : Complex) :
    Matrix (PairPartition n) (PairPartition n) Complex :=
  fun M N => z ^ matchingKappa M N

/--
The paper's orthogonal Weingarten notation `Wg^O(g; z)`, realized as the
corresponding entry of the inverse perfect-matching Gram matrix.  This is a
definition, not an additional literature axiom.
-/
noncomputable def orthogonalWg {n : Nat}
    (g : Equiv.Perm (Fin (2 * n))) (z : Complex) : Complex :=
  (orthogonalGram n z)⁻¹ (standardPairPartition n)
    (transportedPairPartition g)

/--
The modified orthogonal Weingarten function from equation (5.2):
`WgTilde(g; gamma) = (-1)^n 2^n Wg^O(g; -2 gamma)`.
-/
noncomputable def wgTilde {n : Nat}
    (g : Equiv.Perm (Fin (2 * n))) (gamma : Real) : Complex :=
  (-1 : Complex) ^ n * (2 : Complex) ^ n *
    orthogonalWg g (-2 * (gamma : Complex))

/--
Approved literature axiom A4, verbatim in Matsumoto's paper variables and
conditions.  This is Theorem 3 on printed page 819.  The parameter `gamma` is
"as in Theorem 2": `gamma = beta - (d+1)/2` and `gamma > n-1`.
-/
axiom A4_matsumoto_theorem_3
    (d n : Nat) (beta gamma : Real)
    (hd : 0 < d) (hn : 0 < n)
    (sigma : SymPosDef d) (W : W_d d beta sigma)
    (hgamma : gamma = beta - ((d : Real) + 1) / 2)
    (hgap : (n : Real) - 1 < gamma)
    (m : Fin n → ComplexMatrix d)
    (g : Equiv.Perm (Fin (2 * n))) :
    expectation W (fun w => T g w.1 m) =
        (2 : Complex) ^ (-(n : Int)) *
          ∑ matching : PerfectMatching n,
            (((2 * beta) ^ kappa (g⁻¹ * matching.toPerm) : Real) : Complex) *
              T matching.toPerm sigma.1 m ∧
      expectation W (fun w => T g (SymPosDef.inverse w).1 m) =
        ∑ matching : PerfectMatching n,
          wgTilde (g⁻¹ * matching.toPerm) gamma *
            T matching.toPerm (SymPosDef.inverse sigma).1 m

end MatsumotoPaper

#print MatsumotoPaper.A4_matsumoto_theorem_3
#print axioms MatsumotoPaper.A4_matsumoto_theorem_3

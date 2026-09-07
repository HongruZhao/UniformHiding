import Mathlib.Tactic

/-!
# Sharp combined scalar envelope for H13

The pure and mixed Holder ledgers were previously bounded separately by
`128` times the common radial basis.  Keeping the two exact scalar
polynomials together gives the much sharper coefficient `1038 / 5` for
the combination `pure + 3 * mixed`.

The proof is purely algebraic.  After the harmless `t = 0` case, put
`q = n * u / t^2`.  The trace constraint gives `1 <= q`.  The desired
inequality becomes a quadratic in `t`; after shifting
`n = 2 + E`, `q = 1 + R`, its leading and constant coefficients are
positive and its discriminant margin has nineteen positive coefficients.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

set_option maxHeartbeats 2400000

/-- Exact scalar polynomial left by the pure H13 Holder ledger. -/
def h13CombinedSharpPurePolynomial (n t u v : ℝ) : ℝ :=
  23 * t ^ 2 * (n + t) * (n + 2 * t) +
    11 * t *
      ((n + 2 * t) * (t + u) +
        (n + 3 * t + 2 * u) * t +
        (n + t) * (t + 2 * u)) +
    16 * t * (t + 3 * u + 2 * v)

/-- Exact scalar polynomial left by one mixed H13 Holder ledger. -/
def h13CombinedSharpMixedPolynomial (n t u v : ℝ) : ℝ :=
  9 * n * t * (n + 2 * t) * (t + u) +
    6 * n * t * (1 + 2 * t) * (t + u) +
    11 * t * (t + u) * (n + 2 * t) +
    17 * t * (t + 3 * u + 2 * v)

/-- Common trace-one/trace-two radial basis used by the H13 closure. -/
def h13CombinedSharpRadialBasis (n t u : ℝ) : ℝ :=
  n ^ 2 * (t ^ 2 + u) + t ^ 4 + n ^ 2 * u ^ 2

/-- Sharp rational coefficient for the combined pure-plus-three-mixed
H13 scalar ledger. -/
def h13CombinedSharpScalarEnvelopeConstant : ℝ := 1038 / 5

/-! ## Normalized quadratic certificate -/

def h13CombinedSharpNormalizedA (n q : ℝ) : ℝ :=
  h13CombinedSharpScalarEnvelopeConstant * (n * (n + q)) -
    (50 * n ^ 2 + 84 * n + 67)

def h13CombinedSharpNormalizedBN (n q : ℝ) : ℝ :=
  n ^ 2 * (159 + 27 * q) + n * (132 + 84 * q) + 201 * q

def h13CombinedSharpNormalizedDN (n q : ℝ) : ℝ :=
  n *
      (h13CombinedSharpScalarEnvelopeConstant * (1 + q ^ 2) -
        (46 + 90 * q)) -
    266 * q

/-- Positivity and discriminant certificate for the normalized quadratic.
The final conjunct is exactly the nonnegative discriminant margin used in
`h13CombinedSharpScalarEnvelope`. -/
theorem h13CombinedSharpNormalizedCertificate
    (n q : ℝ) (hn : 2 ≤ n) (hq : 1 ≤ q) :
    0 < h13CombinedSharpNormalizedA n q ∧
      0 < h13CombinedSharpNormalizedDN n q ∧
      0 ≤
        4 * h13CombinedSharpNormalizedA n q *
            h13CombinedSharpNormalizedDN n q * n -
          h13CombinedSharpNormalizedBN n q ^ 2 := by
  let E : ℝ := n - 2
  let R : ℝ := q - 1
  have hE : 0 ≤ E := by
    dsimp only [E]
    linarith
  have hR : 0 ≤ R := by
    dsimp only [R]
    linarith
  have hAexpand :
      h13CombinedSharpNormalizedA n q =
        4053 / 5 + (2076 / 5) * R + 754 * E +
          (1038 / 5) * E * R + (788 / 5) * E ^ 2 := by
    dsimp [h13CombinedSharpNormalizedA,
      h13CombinedSharpScalarEnvelopeConstant, E, R]
    ring
  have hDNexpand :
      h13CombinedSharpNormalizedDN n q =
        1462 / 5 + (1922 / 5) * R + (2076 / 5) * R ^ 2 +
          (1396 / 5) * E + (1626 / 5) * E * R +
          (1038 / 5) * E * R ^ 2 := by
    dsimp [h13CombinedSharpNormalizedDN,
      h13CombinedSharpScalarEnvelopeConstant, E, R]
    ring
  have hDeltaExpand :
      4 * h13CombinedSharpNormalizedA n q *
            h13CombinedSharpNormalizedDN n q * n -
          h13CombinedSharpNormalizedBN n q ^ 2 =
        663 / 25 +
          (53758374 / 25) * R + 3741783 * R ^ 2 +
          (34478208 / 25) * R ^ 3 +
          (46963768 / 25) * E +
          (153198872 / 25) * E * R +
          (184270368 / 25) * E * R ^ 2 +
          (51717312 / 25) * E * R ^ 3 +
          (12030524 / 5) * E ^ 2 +
          (130244862 / 25) * E ^ 2 * R +
          (125946522 / 25) * E ^ 2 * R ^ 2 +
          (25858656 / 25) * E ^ 2 * R ^ 3 +
          (25532288 / 25) * E ^ 3 +
          (8708624 / 5) * E ^ 3 * R +
          (35232096 / 25) * E ^ 3 * R ^ 2 +
          (4309776 / 25) * E ^ 3 * R ^ 3 +
          (3535292 / 25) * E ^ 4 +
          (4874052 / 25) * E ^ 4 * R +
          (3253551 / 25) * E ^ 4 * R ^ 2 := by
    dsimp [h13CombinedSharpNormalizedA,
      h13CombinedSharpNormalizedBN, h13CombinedSharpNormalizedDN,
      h13CombinedSharpScalarEnvelopeConstant, E, R]
    ring
  constructor
  · rw [hAexpand]
    positivity
  constructor
  · rw [hDNexpand]
    positivity
  · rw [hDeltaExpand]
    positivity

/-! ## Combined envelope -/

/-- The exact pure ledger plus three times the exact mixed ledger fits in
`(1038 / 5)` times the common H13 radial basis.  This statement uses only
the elementary trace inequalities supplied as hypotheses. -/
theorem h13CombinedSharpScalarEnvelope
    (n t u v : ℝ) (hn : 2 ≤ n) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (htlow : t ^ 2 ≤ n * u) (hv : v ≤ t * u) :
    h13CombinedSharpPurePolynomial n t u v +
        3 * h13CombinedSharpMixedPolynomial n t u v ≤
      h13CombinedSharpScalarEnvelopeConstant *
        h13CombinedSharpRadialBasis n t u := by
  by_cases htzero : t = 0
  · subst t
    simp [h13CombinedSharpPurePolynomial,
      h13CombinedSharpMixedPolynomial, h13CombinedSharpRadialBasis,
      h13CombinedSharpScalarEnvelopeConstant]
    positivity
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm htzero)
    have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
    have ht2pos : 0 < t ^ 2 := sq_pos_of_pos htpos
    let q : ℝ := n * u / t ^ 2
    have hq : 1 ≤ q := by
      dsimp only [q]
      apply (le_div_iff₀ ht2pos).2
      simpa only [one_mul] using htlow
    obtain ⟨hApos, hDNpos, hdisc⟩ :=
      h13CombinedSharpNormalizedCertificate n q hn hq
    let A : ℝ := h13CombinedSharpNormalizedA n q
    let bN : ℝ := h13CombinedSharpNormalizedBN n q
    let DN : ℝ := h13CombinedSharpNormalizedDN n q
    have hApos' : 0 < A := by simpa only [A] using hApos
    have hDNpos' : 0 < DN := by simpa only [DN] using hDNpos
    have hdisc' : 0 ≤ 4 * A * DN * n - bN ^ 2 := by
      simpa only [A, bN, DN] using hdisc
    have hquadratic : 0 ≤ n * A - bN * t + DN * t ^ 2 := by
      have hsquare : 0 ≤ (2 * DN * t - bN) ^ 2 := sq_nonneg _
      have hidentity :
          4 * DN * (n * A - bN * t + DN * t ^ 2) =
            (2 * DN * t - bN) ^ 2 +
              (4 * A * DN * n - bN ^ 2) := by
        ring
      have hproduct :
          0 ≤ 4 * DN * (n * A - bN * t + DN * t ^ 2) := by
        rw [hidentity]
        exact add_nonneg hsquare hdisc'
      by_contra hnot
      have hnegative : n * A - bN * t + DN * t ^ 2 < 0 :=
        lt_of_not_ge hnot
      have : 4 * DN * (n * A - bN * t + DN * t ^ 2) < 0 := by
        exact mul_neg_of_pos_of_neg (by positivity) hnegative
      linarith
    let upper : ℝ :=
      h13CombinedSharpPurePolynomial n t u (t * u) +
        3 * h13CombinedSharpMixedPolynomial n t u (t * u)
    have htv : t * v ≤ t ^ 2 * u := by
      have hmul := mul_le_mul_of_nonneg_left hv ht
      nlinarith
    have hupper :
        h13CombinedSharpPurePolynomial n t u v +
            3 * h13CombinedSharpMixedPolynomial n t u v ≤ upper := by
      dsimp [upper, h13CombinedSharpPurePolynomial,
        h13CombinedSharpMixedPolynomial]
      nlinarith
    have hscaleIdentity :
        n *
            (h13CombinedSharpScalarEnvelopeConstant *
                h13CombinedSharpRadialBasis n t u - upper) =
          t ^ 2 * (n * A - bN * t + DN * t ^ 2) := by
      dsimp [upper, A, bN, DN, q,
        h13CombinedSharpPurePolynomial,
        h13CombinedSharpMixedPolynomial,
        h13CombinedSharpRadialBasis,
        h13CombinedSharpNormalizedA,
        h13CombinedSharpNormalizedBN,
        h13CombinedSharpNormalizedDN,
        h13CombinedSharpScalarEnvelopeConstant]
      field_simp [ne_of_gt hnpos, ne_of_gt ht2pos]
      <;> ring
    have hscaledNonneg :
        0 ≤ n *
          (h13CombinedSharpScalarEnvelopeConstant *
              h13CombinedSharpRadialBasis n t u - upper) := by
      rw [hscaleIdentity]
      exact mul_nonneg (sq_nonneg t) hquadratic
    have hdifference :
        0 ≤ h13CombinedSharpScalarEnvelopeConstant *
            h13CombinedSharpRadialBasis n t u - upper := by
      by_contra hnot
      have hnegative :
          h13CombinedSharpScalarEnvelopeConstant *
              h13CombinedSharpRadialBasis n t u - upper < 0 :=
        lt_of_not_ge hnot
      have :
          n *
              (h13CombinedSharpScalarEnvelopeConstant *
                h13CombinedSharpRadialBasis n t u - upper) < 0 :=
        mul_neg_of_pos_of_neg hnpos hnegative
      linarith
    exact hupper.trans (by linarith)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

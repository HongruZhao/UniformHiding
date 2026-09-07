import LogdetLean.GramHafnian.UltimateHiding.DenseScore.OptimizedCubicNormalizationBound
import Mathlib.Tactic

/-!
# Dense-range cubic remainder coefficient bounds

The original five coefficient estimates use only `n <= c`.  In the canonical
dense regime the exact exponent satisfies the much stronger inequality
`13*n <= c`.  Retaining that inequality gives the constants
`36, 26, 52, 24, 8` below.  All five statements are elementary rational
inequalities and introduce no probabilistic or scientific interface.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

private theorem cubicTraceThreeRemainderDenominator_pos_ultra
    {n c : ℝ} (hn : 1 ≤ n) (hc : 13 * n ≤ c) :
    0 < cubicTraceThreeRemainderDenominator n c := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hcpos : 0 < c := by nlinarith
  unfold cubicTraceThreeRemainderDenominator
  positivity

/-- Dense-range cube coefficient: `100` improves to `36`. -/
theorem cubicTraceThreeRemainderCoeffCube_abs_le_ultra
    {n c : ℝ} (hn : 1 ≤ n) (hc : 13 * n ≤ c) :
    |cubicTraceThreeRemainderCoeffCube n c| ≤ 36 / n ^ 5 := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hdenpos := cubicTraceThreeRemainderDenominator_pos_ultra hn hc
  unfold cubicTraceThreeRemainderCoeffCube
  rw [abs_div, abs_of_pos hdenpos,
    div_le_div_iff₀ hdenpos (pow_pos hnpos 5)]
  rw [← abs_of_pos (pow_pos hnpos 5), ← abs_mul]
  apply abs_le.mpr
  let e : ℝ := n - 1
  let d : ℝ := c - 13 * n
  have he : 0 ≤ e := by dsimp only [e]; linarith
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hnrep : n = 1 + e := by dsimp only [e]; ring
  have hcrep : c = 13 * (1 + e) + d := by
    dsimp only [e, d]
    ring
  constructor <;>
    rw [hnrep, hcrep] <;>
    unfold cubicTraceThreeRemainderCoeffCubeNumerator
      cubicTraceThreeRemainderDenominator <;>
    apply sub_nonneg.mp <;> ring_nf <;> positivity

/-- Dense-range square coefficient: `600` improves to `26`. -/
theorem cubicTraceThreeRemainderCoeffSquare_abs_le_ultra
    {n c : ℝ} (hn : 1 ≤ n) (hc : 13 * n ≤ c) :
    |cubicTraceThreeRemainderCoeffSquare n c| ≤ 26 / n ^ 3 := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hdenpos := cubicTraceThreeRemainderDenominator_pos_ultra hn hc
  unfold cubicTraceThreeRemainderCoeffSquare
  rw [abs_div, abs_of_pos hdenpos,
    div_le_div_iff₀ hdenpos (pow_pos hnpos 3)]
  rw [← abs_of_pos (pow_pos hnpos 3), ← abs_mul]
  apply abs_le.mpr
  let e : ℝ := n - 1
  let d : ℝ := c - 13 * n
  have he : 0 ≤ e := by dsimp only [e]; linarith
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hnrep : n = 1 + e := by dsimp only [e]; ring
  have hcrep : c = 13 * (1 + e) + d := by
    dsimp only [e, d]
    ring
  constructor <;>
    rw [hnrep, hcrep] <;>
    unfold cubicTraceThreeRemainderCoeffSquareNumerator
      cubicTraceThreeRemainderDenominator <;>
    apply sub_nonneg.mp <;> ring_nf <;> positivity

/-- Dense-range mixed coefficient: `600` improves to `52`. -/
theorem cubicTraceThreeRemainderCoeffMixed_abs_le_ultra
    {n c : ℝ} (hn : 1 ≤ n) (hc : 13 * n ≤ c) :
    |cubicTraceThreeRemainderCoeffMixed n c| ≤ 52 / n ^ 4 := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hdenpos := cubicTraceThreeRemainderDenominator_pos_ultra hn hc
  unfold cubicTraceThreeRemainderCoeffMixed
  rw [abs_div, abs_of_pos hdenpos,
    div_le_div_iff₀ hdenpos (pow_pos hnpos 4)]
  rw [← abs_of_pos (pow_pos hnpos 4), ← abs_mul]
  apply abs_le.mpr
  let e : ℝ := n - 1
  let d : ℝ := c - 13 * n
  have he : 0 ≤ e := by dsimp only [e]; linarith
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hnrep : n = 1 + e := by dsimp only [e]; ring
  have hcrep : c = 13 * (1 + e) + d := by
    dsimp only [e, d]
    ring
  constructor <;>
    rw [hnrep, hcrep] <;>
    unfold cubicTraceThreeRemainderCoeffMixedNumerator
      cubicTraceThreeRemainderDenominator <;>
    apply sub_nonneg.mp <;> ring_nf <;> positivity

/-- Dense-range raw-second-trace coefficient: `1000` improves to `24`. -/
theorem cubicTraceThreeRemainderCoeffTwo_abs_le_ultra
    {n c : ℝ} (hn : 1 ≤ n) (hc : 13 * n ≤ c) :
    |cubicTraceThreeRemainderCoeffTwo n c| ≤ 24 / n ^ 2 := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hdenpos := cubicTraceThreeRemainderDenominator_pos_ultra hn hc
  unfold cubicTraceThreeRemainderCoeffTwo
  rw [abs_div, abs_of_pos hdenpos,
    div_le_div_iff₀ hdenpos (pow_pos hnpos 2)]
  rw [← abs_of_pos (pow_pos hnpos 2), ← abs_mul]
  apply abs_le.mpr
  let e : ℝ := n - 1
  let d : ℝ := c - 13 * n
  have he : 0 ≤ e := by dsimp only [e]; linarith
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hnrep : n = 1 + e := by dsimp only [e]; ring
  have hcrep : c = 13 * (1 + e) + d := by
    dsimp only [e, d]
    ring
  constructor <;>
    rw [hnrep, hcrep] <;>
    unfold cubicTraceThreeRemainderCoeffTwoNumerator
      cubicTraceThreeRemainderDenominator <;>
    apply sub_nonneg.mp <;> ring_nf <;> positivity

/-- Dense-range raw-first-trace coefficient: `400` improves to `8`. -/
theorem cubicTraceThreeRemainderCoeffOne_abs_le_ultra
    {n c : ℝ} (hn : 1 ≤ n) (hc : 13 * n ≤ c) :
    |cubicTraceThreeRemainderCoeffOne n c| ≤ 8 / n := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hdenpos := cubicTraceThreeRemainderDenominator_pos_ultra hn hc
  unfold cubicTraceThreeRemainderCoeffOne
  rw [abs_div, abs_of_pos hdenpos,
    div_le_div_iff₀ hdenpos hnpos]
  have habs : |cubicTraceThreeRemainderCoeffOneNumerator n c * n| ≤
      8 * cubicTraceThreeRemainderDenominator n c := by
    apply abs_le.mpr
    let e : ℝ := n - 1
    let d : ℝ := c - 13 * n
    have he : 0 ≤ e := by dsimp only [e]; linarith
    have hd : 0 ≤ d := by dsimp only [d]; linarith
    have hnrep : n = 1 + e := by dsimp only [e]; ring
    have hcrep : c = 13 * (1 + e) + d := by
      dsimp only [e, d]
      ring
    constructor <;>
      rw [hnrep, hcrep] <;>
      unfold cubicTraceThreeRemainderCoeffOneNumerator
        cubicTraceThreeRemainderDenominator <;>
      apply sub_nonneg.mp <;> ring_nf <;> positivity
  calc
    |cubicTraceThreeRemainderCoeffOneNumerator n c| * n =
        |cubicTraceThreeRemainderCoeffOneNumerator n c * n| := by
      rw [abs_mul, abs_of_pos hnpos]
    _ ≤ 8 * cubicTraceThreeRemainderDenominator n c := habs

/-- The raw-third-trace coefficient also retains its asymptotically sharp
constant `16` in the dense range; the compatibility proof used `600`. -/
theorem averagedCenteredCubicTraceThreeCoefficient_abs_le_ultra
    {n c : ℝ} (hn : 1 ≤ n) (hc : 13 * n ≤ c) :
    |averagedCenteredCubicTraceThreeCoefficient n c| ≤ 16 / n ^ 3 := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hc4 : (4 : ℝ) ≤ c := by nlinarith
  have hcn : n ≤ c := by nlinarith
  have hdenpos := cubicTraceThreeRemainderDenominator_pos_ultra hn hc
  have halpha0 : 0 ≤ averagedCenteredCubicTraceThreeCoefficient n c := by
    have hlower := averagedCenteredCubicTraceThreeCoefficient_lower_bound hn hc4
    exact (by positivity : 0 ≤ 4 / (3 * n ^ 3)).trans hlower
  rw [abs_of_nonneg halpha0]
  unfold averagedCenteredCubicTraceThreeCoefficient
  change 16 * (n ^ 2 * (c ^ 2 - 3 * c + 4) +
      12 * n * (c - 1) + 16) /
      cubicTraceThreeRemainderDenominator n c ≤ 16 / n ^ 3
  rw [div_le_div_iff₀ hdenpos (pow_pos hnpos 3)]
  let e : ℝ := n - 1
  let d : ℝ := c - 13 * n
  have he : 0 ≤ e := by dsimp only [e]; linarith
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hnrep : n = 1 + e := by dsimp only [e]; ring
  have hcrep : c = 13 * (1 + e) + d := by
    dsimp only [e, d]
    ring
  rw [hnrep, hcrep]
  unfold cubicTraceThreeRemainderDenominator
  apply sub_nonneg.mp
  ring_nf
  positivity

/-- Canonical square-COE specialization of the sharp coefficient bound. -/
theorem concreteAveragedCenteredCubicTraceThreeCoefficient_abs_le_ultra
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    |averagedCenteredCubicTraceThreeCoefficient (N : ℝ)
        (concreteCOEExponent N K)| ≤ 16 / (N : ℝ) ^ 3 := by
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact averagedCenteredCubicTraceThreeCoefficient_abs_le_ultra hNr
    (U08.thirteen_mul_dimension_le_concreteCOEExponent_of_dense hN hdense)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

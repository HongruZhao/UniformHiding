import LogdetLean.GramHafnian.LocalAnticoncentration.TotalVariation
import LogdetLean.GramHafnian.UltimateHiding.HaarGaussianMatrixLaws

/-!
# Basic interface for uniform product matrix hiding

This file fixes the exact finite theorem that the new proof must establish.
It deliberately reuses the literal Haar and Gaussian transpose Gram laws from
`LocalAnticoncentration`.  No scientific claim is assumed here.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding

noncomputable section

open LocalAnticoncentration

/-- The proposed hiding rate, independent of the squeezing rank `K`. -/
def ultimateHidingRate (M N : ℕ) : ℝ :=
  (N : ℝ) / Real.sqrt (M : ℝ)

/-- The sharpened, `K`-independent rate in the new unified theorem. -/
def ultimateSquaredHidingRate (M N : ℕ) : ℝ :=
  (N : ℝ) ^ 2 / (M : ℝ)

theorem ultimateHidingRate_nonneg (M N : ℕ) :
    0 <= ultimateHidingRate M N := by
  exact div_nonneg (Nat.cast_nonneg N) (Real.sqrt_nonneg _)

theorem ultimateSquaredHidingRate_nonneg (M N : ℕ) :
    0 <= ultimateSquaredHidingRate M N := by
  exact div_nonneg (sq_nonneg (N : ℝ)) (Nat.cast_nonneg M)

/-- Triangle inequality for the probability convention of total variation. -/
theorem probabilityTotalVariationLE_triangle
    {α : Type*} [MeasurableSpace α]
    {μ ν ξ : Measure α} {δ ε : ℝ}
    (hμν : probabilityTotalVariationLE μ ν δ)
    (hνξ : probabilityTotalVariationLE ν ξ ε) :
    probabilityTotalVariationLE μ ξ (δ + ε) := by
  refine ⟨add_nonneg hμν.1 hνξ.1, ?_⟩
  intro s hs
  have hdecomp :
      μ.real s - ξ.real s =
        (μ.real s - ν.real s) + (ν.real s - ξ.real s) := by
    ring
  rw [hdecomp]
  exact (abs_add_le _ _).trans (add_le_add (hμν.2 s hs) (hνξ.2 s hs))

/-- Any two probability measures are at probability total variation at most
one. -/
theorem probabilityTotalVariationLE_one
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    probabilityTotalVariationLE μ ν 1 := by
  refine ⟨by norm_num, ?_⟩
  intro s hs
  rw [abs_le]
  constructor
  · have hμ : 0 <= μ.real s := measureReal_nonneg
    have hν : ν.real s <= 1 := measureReal_le_one
    linarith
  · have hμ : μ.real s <= 1 := measureReal_le_one
    have hν : 0 <= ν.real s := measureReal_nonneg
    linarith

/-- Combine a quantitative estimate with the automatic probability bound
one. -/
theorem probabilityTotalVariationLE_min_one
    {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {δ : ℝ} (hδ : probabilityTotalVariationLE μ ν δ) :
    probabilityTotalVariationLE μ ν (min 1 δ) := by
  have hOne := probabilityTotalVariationLE_one μ ν
  refine ⟨le_min hOne.1 hδ.1, ?_⟩
  intro s hs
  exact le_min (hOne.2 s hs) (hδ.2 s hs)

/-- The literal finite all rank theorem at a fixed nonnegative constant. -/
def UniformProductMatrixHidingAt (C : ℝ) : Prop :=
  0 <= C ∧
    ∀ (H : UnitaryHaarProbabilityFamily) (M N K : ℕ),
      1 <= N -> N <= K -> K <= M ->
      probabilityTotalVariationLE
        (scaledHaarTransposeGramLaw H M N K)
        (gaussianTransposeGramLaw N K)
        (min 1 (C * ultimateHidingRate M N))

/-- The headline theorem is the existence of one absolute constant valid for
all finite triples `1 <= N <= K <= M`. -/
def UniformProductMatrixHiding : Prop :=
  ∃ C : ℝ, UniformProductMatrixHidingAt C

/-- Literal finite all-rank theorem with the sharpened `N^2/M` rate. -/
def UniformProductMatrixHidingSquaredAt (C : ℝ) : Prop :=
  0 <= C ∧
    ∀ (H : UnitaryHaarProbabilityFamily) (M N K : ℕ),
      1 <= N -> N <= K -> K <= M ->
      probabilityTotalVariationLE
        (scaledHaarTransposeGramLaw H M N K)
        (gaussianTransposeGramLaw N K)
        (min 1 (C * ultimateSquaredHidingRate M N))

/-- Headline existence statement for uniform transpose-Gram hiding at rate
`min {1, C N^2/M}`. -/
def UniformProductMatrixHidingSquared : Prop :=
  ∃ C : ℝ, UniformProductMatrixHidingSquaredAt C

theorem UniformProductMatrixHidingAt.constant_nonneg {C : ℝ}
    (h : UniformProductMatrixHidingAt C) : 0 <= C := h.1

theorem UniformProductMatrixHidingAt.apply {C : ℝ}
    (h : UniformProductMatrixHidingAt C)
    (H : UnitaryHaarProbabilityFamily) {M N K : ℕ}
    (hN : 1 <= N) (hNK : N <= K) (hKM : K <= M) :
    probabilityTotalVariationLE
      (scaledHaarTransposeGramLaw H M N K)
      (gaussianTransposeGramLaw N K)
      (min 1 (C * ultimateHidingRate M N)) :=
  h.2 H M N K hN hNK hKM

theorem UniformProductMatrixHidingSquaredAt.constant_nonneg {C : ℝ}
    (h : UniformProductMatrixHidingSquaredAt C) : 0 <= C := h.1

theorem UniformProductMatrixHidingSquaredAt.apply {C : ℝ}
    (h : UniformProductMatrixHidingSquaredAt C)
    (H : UnitaryHaarProbabilityFamily) {M N K : ℕ}
    (hN : 1 <= N) (hNK : N <= K) (hKM : K <= M) :
    probabilityTotalVariationLE
      (scaledHaarTransposeGramLaw H M N K)
      (gaussianTransposeGramLaw N K)
      (min 1 (C * ultimateSquaredHidingRate M N)) :=
  h.2 H M N K hN hNK hKM

end

end LogdetLean.GramHafnian.UltimateHiding

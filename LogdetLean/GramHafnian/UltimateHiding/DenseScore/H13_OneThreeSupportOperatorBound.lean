import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_OneThreeSupportVelocityReduction
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_DeterministicOperator
import Mathlib.Tactic

/-!
# Operator bound for the H13 support normal form

This module bounds the six inverse-free words in the exact H13 third-score
kernel.  It is deterministic finite matrix algebra on the open COE support.
-/

open Matrix
open scoped ComplexOrder
open scoped Matrix.Norms.L2Operator

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

set_option maxHeartbeats 5000000

/-- The input-side support statistic is the transpose of the output-side
statistic.  This is the Takagi-algebra identity behind the last H13 word. -/
theorem h13LedgerTStar_mul_corner_eq_Z_transpose
    {N : ℕ} (C : ConcreteMatrixState N) (hC : C.IsSymm)
    (hsupport : coeCornerSupport C) :
    (h13LedgerT C).conjTranspose * C = (h13LedgerZ C).transpose := by
  let H := h13LedgerInputGap C
  let G := h13LedgerOutputGap C
  have hH : H.PosDef := by
    unfold coeCornerSupport at hsupport
    simpa only [H, h13LedgerInputGap] using hsupport
  have hGherm : G.IsHermitian := by
    dsimp only [G, h13LedgerOutputGap]
    exact Matrix.IsHermitian.sub Matrix.isHermitian_one
      (Matrix.isHermitian_mul_conjTranspose_self C)
  have hHtranspose : H.transpose = G := by
    dsimp only [H, G, h13LedgerInputGap, h13LedgerOutputGap]
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      hC.eq, hC.conjTranspose.eq]
  unfold h13LedgerT h13LedgerZ
  rw [Matrix.conjTranspose_mul, hGherm.inv.eq]
  rw [Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_nonsing_inv, hC.eq, hC.conjTranspose.eq,
    hHtranspose]
  noncomm_ring

/-- Unscaled support Gram identity in the H13 ledger notation. -/
theorem h13LedgerT_mul_conjTranspose_eq_Z_mul_one_add_Z
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    h13LedgerT C * (h13LedgerT C).conjTranspose =
      h13LedgerZ C * (1 + h13LedgerZ C) := by
  have h := concreteCOET_mul_conjTranspose_eq_Z_mul_one_add_Z
    (N := N) (K := 1) C
  have hs : coeCornerSupport (unscaleCOECorner 1 C) := by
    simpa [unscaleCOECorner] using hsupport
  specialize h hs
  simpa [concreteCOET, concreteCOEZ, unscaleCOECorner,
    h13LedgerT, h13LedgerZ, h13LedgerInputGap,
    h13LedgerOutputGap] using h

/-- The unscaled H13 support factor `T` is complex symmetric. -/
theorem h13LedgerT_isSymm
    {N : ℕ} (C : ConcreteMatrixState N) (hC : C.IsSymm)
    (hsupport : coeCornerSupport C) : (h13LedgerT C).IsSymm := by
  have hs : (unscaleCOECorner 1 C).IsSymm := by
    simpa [unscaleCOECorner] using hC
  have hsup : coeCornerSupport (unscaleCOECorner 1 C) := by
    simpa [unscaleCOECorner] using hsupport
  have h := concreteCOET_isSymm_of_support (N := N) (K := 1) C hs hsup
  simpa [concreteCOET, unscaleCOECorner, h13LedgerT,
    h13LedgerOutputGap] using h

/-- The support Gram identity bounds the squared operator norm of `T`. -/
theorem h13LedgerT_l2_opNorm_sq_le_Z_mul_one_add_Z
    {N : ℕ} (hN : 1 ≤ N) (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    ‖h13LedgerT C‖ ^ 2 ≤
      ‖h13LedgerZ C‖ * (1 + ‖h13LedgerZ C‖) := by
  letI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  let T := h13LedgerT C
  let Z := h13LedgerZ C
  have hGram : T * T.conjTranspose = Z * (1 + Z) := by
    simpa only [T, Z] using
      h13LedgerT_mul_conjTranspose_eq_Z_mul_one_add_Z C hsupport
  have hTstar : ‖T.conjTranspose‖ = ‖T‖ :=
    Matrix.l2_opNorm_conjTranspose T
  have hTT : ‖T‖ ^ 2 = ‖T * T.conjTranspose‖ := by
    calc
      ‖T‖ ^ 2 = ‖T.conjTranspose‖ * ‖T.conjTranspose‖ := by
        rw [hTstar]
        ring
      _ = ‖T.conjTranspose.conjTranspose * T.conjTranspose‖ := by
        rw [Matrix.l2_opNorm_conjTranspose_mul_self]
      _ = ‖T * T.conjTranspose‖ := by simp
  rw [hTT, hGram]
  calc
    ‖Z * (1 + Z)‖ ≤ ‖Z‖ * ‖1 + Z‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖Z‖ * (1 + ‖Z‖) := by
      gcongr
      calc
        ‖1 + Z‖ ≤ ‖(1 : ConcreteMatrixState N)‖ + ‖Z‖ := norm_add_le _ _
        _ = 1 + ‖Z‖ := by rw [CStarRing.norm_one]

private theorem h13_l2_opNorm_mul_five_le
    {N : ℕ} [Nonempty (Fin N)] (B₁ B₂ B₃ B₄ B₅ : ConcreteMatrixState N) :
    ‖B₁ * B₂ * B₃ * B₄ * B₅‖ ≤
      (((‖B₁‖ * ‖B₂‖) * ‖B₃‖) * ‖B₄‖) * ‖B₅‖ := by
  calc
    ‖B₁ * B₂ * B₃ * B₄ * B₅‖ ≤
        ‖B₁ * B₂ * B₃ * B₄‖ * ‖B₅‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖B₁ * B₂ * B₃‖ * ‖B₄‖) * ‖B₅‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ ((‖B₁ * B₂‖ * ‖B₃‖) * ‖B₄‖) * ‖B₅‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
        (norm_nonneg _)
    _ ≤ (((‖B₁‖ * ‖B₂‖) * ‖B₃‖) * ‖B₄‖) * ‖B₅‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
          (norm_nonneg _))
        (norm_nonneg _)

private theorem h13_mul_five_mono
    {a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ : ℝ}
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃)
    (h₄ : a₄ ≤ b₄) (h₅ : a₅ ≤ b₅)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃)
    (hb₄ : 0 ≤ b₄) (hb₅ : 0 ≤ b₅)
    (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (ha₄ : 0 ≤ a₄)
    (ha₅ : 0 ≤ a₅) :
    (((a₁ * a₂) * a₃) * a₄) * a₅ ≤
      (((b₁ * b₂) * b₃) * b₄) * b₅ := by
  have h₁₂ : a₁ * a₂ ≤ b₁ * b₂ := mul_le_mul h₁ h₂ ha₂ hb₁
  have h₁₂₃ : (a₁ * a₂) * a₃ ≤ (b₁ * b₂) * b₃ :=
    mul_le_mul h₁₂ h₃ ha₃ (mul_nonneg hb₁ hb₂)
  have h₁₂₃₄ : ((a₁ * a₂) * a₃) * a₄ ≤
      ((b₁ * b₂) * b₃) * b₄ :=
    mul_le_mul h₁₂₃ h₄ ha₄
      (mul_nonneg (mul_nonneg hb₁ hb₂) hb₃)
  exact mul_le_mul h₁₂₃₄ h₅ ha₅
    (mul_nonneg (mul_nonneg (mul_nonneg hb₁ hb₂) hb₃) hb₄)

/-- The six inverse-free H13 words have the dimension-free operator bound
`16 z (1+z)^2`, where `z=||Z||`. -/
theorem h13ThirdTraceKernelSixWord_norm_le
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (C : ConcreteMatrixState N) (hC : C.IsSymm)
    (hsupport : coeCornerSupport C) :
    ‖h13ThirdTraceKernelSixWord
        (concreteCenteredOrbitalDirection N v) C‖ ≤
      16 * ‖h13LedgerZ C‖ * (1 + ‖h13LedgerZ C‖) ^ 2 := by
  letI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  let Q := concreteCenteredOrbitalDirection N v
  let Z := h13LedgerZ C
  let T := h13LedgerT C
  let Ts := T.conjTranspose
  let W : ConcreteMatrixState N := 1 + Z
  let A : ConcreteMatrixState N := 1 + 2 • Z
  let U : ConcreteMatrixState N := 1 + 2 • (Ts * C)
  let z : ℝ := ‖Z‖
  let u : ℝ := 1 + z
  let t : ℝ := ‖T‖
  have hz : 0 ≤ z := norm_nonneg Z
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hzu : z ≤ u := by dsimp only [u]; linarith
  have hQ : ‖Q‖ ≤ 1 := by
    simpa only [Q] using
      concreteCenteredOrbitalDirection_l2_opNorm_le_one_h14 hN v
  have hQt : ‖Q.transpose‖ ≤ 1 := by
    simpa only [Q] using
      concreteCenteredOrbitalDirection_transpose_l2_opNorm_le_one_h14 hN v
  have hTs : ‖Ts‖ = t := by
    dsimp only [Ts, t]
    exact Matrix.l2_opNorm_conjTranspose T
  have hW : ‖W‖ ≤ u := by
    dsimp only [W, u, z]
    calc
      ‖1 + Z‖ ≤ ‖(1 : ConcreteMatrixState N)‖ + ‖Z‖ := norm_add_le _ _
      _ = 1 + ‖Z‖ := by rw [CStarRing.norm_one]
  have hA : ‖A‖ ≤ 2 * u := by
    dsimp only [A, u, z]
    calc
      ‖1 + 2 • Z‖ ≤ ‖(1 : ConcreteMatrixState N)‖ + ‖2 • Z‖ := norm_add_le _ _
      _ = 1 + 2 * ‖Z‖ := by
        rw [CStarRing.norm_one, ← Nat.cast_smul_eq_nsmul ℂ, norm_smul]
        norm_num
      _ ≤ 2 * (1 + ‖Z‖) := by linarith [norm_nonneg Z]
  have hinput : Ts * C = Z.transpose := by
    simpa only [Ts, T, Z] using
      h13LedgerTStar_mul_corner_eq_Z_transpose C hC hsupport
  have hTsy : T.transpose = T := by
    simpa only [T] using (h13LedgerT_isSymm C hC hsupport).eq
  have hTssymm : Ts.transpose = Ts := by
    simpa only [Ts, T] using
      (h13LedgerT_isSymm C hC hsupport).conjTranspose.eq
  have ht0 : 0 ≤ t := norm_nonneg T
  have ht2 : t ^ 2 ≤ z * u := by
    simpa only [t, z, u, T, Z] using
      h13LedgerT_l2_opNorm_sq_le_Z_mul_one_add_Z hN C hsupport
  let e1 := Matrix.trace (Q * W * Q * Z * Q * Z)
  let e2 := Matrix.trace (Q * T * Q.transpose * Ts * Q * Z)
  let e3 := Matrix.trace (Q * W * Q * W * Q * Z)
  let e4 := Matrix.trace (Q * W * Q * T * Q.transpose * Ts)
  let e5 := Matrix.trace (Q * A * Q * T * Q.transpose * Ts)
  let e6 := Matrix.trace (Q * T * Q.transpose * U * Q.transpose * Ts)
  have he1 : ‖e1‖ ≤ 2 * u * z ^ 2 := by
    have hdual := concreteCenteredOrbitalDirection_traceOne_dual_le_two_h14
      hN v (W * Q * Z * Q * Z)
    have htail : ‖W * Q * Z * Q * Z‖ ≤ u * z ^ 2 := by
      calc
        ‖W * Q * Z * Q * Z‖ ≤
            (((‖W‖ * ‖Q‖) * ‖Z‖) * ‖Q‖) * ‖Z‖ :=
          h13_l2_opNorm_mul_five_le W Q Z Q Z
        _ ≤ ((u * 1) * z) * 1 * z := by
          exact h13_mul_five_mono hW hQ (by rfl) hQ (by rfl)
            hu zero_le_one hz zero_le_one hz
            (norm_nonneg Q) (norm_nonneg Z) (norm_nonneg Q) (norm_nonneg Z)
        _ = u * z ^ 2 := by ring
    change ‖Matrix.trace (Q * (W * Q * Z * Q * Z))‖ ≤ _ at hdual
    dsimp only [e1]
    rw [show Q * W * Q * Z * Q * Z = Q * (W * Q * Z * Q * Z) by
      noncomm_ring]
    exact hdual.trans (by nlinarith)
  have he2 : ‖e2‖ ≤ 2 * u * z ^ 2 := by
    have hdual := concreteCenteredOrbitalDirection_traceOne_dual_le_two_h14
      hN v (T * Q.transpose * Ts * Q * Z)
    have htail : ‖T * Q.transpose * Ts * Q * Z‖ ≤ u * z ^ 2 := by
      calc
        ‖T * Q.transpose * Ts * Q * Z‖ ≤
            (((‖T‖ * ‖Q.transpose‖) * ‖Ts‖) * ‖Q‖) * ‖Z‖ :=
          h13_l2_opNorm_mul_five_le T Q.transpose Ts Q Z
        _ ≤ ((t * 1) * t) * 1 * z := by
          exact h13_mul_five_mono (by rfl) hQt hTs.le hQ (by rfl)
            ht0 zero_le_one ht0 zero_le_one hz
            (norm_nonneg Q.transpose) (norm_nonneg Ts) (norm_nonneg Q) (norm_nonneg Z)
        _ ≤ u * z ^ 2 := by nlinarith
    dsimp only [e2]
    rw [show Q * T * Q.transpose * Ts * Q * Z =
        Q * (T * Q.transpose * Ts * Q * Z) by noncomm_ring]
    exact hdual.trans (by nlinarith)
  have he3 : ‖e3‖ ≤ 2 * u ^ 2 * z := by
    have hdual := concreteCenteredOrbitalDirection_traceOne_dual_le_two_h14
      hN v (W * Q * W * Q * Z)
    have htail : ‖W * Q * W * Q * Z‖ ≤ u ^ 2 * z := by
      calc
        ‖W * Q * W * Q * Z‖ ≤
            (((‖W‖ * ‖Q‖) * ‖W‖) * ‖Q‖) * ‖Z‖ :=
          h13_l2_opNorm_mul_five_le W Q W Q Z
        _ ≤ ((u * 1) * u) * 1 * z := by
          exact h13_mul_five_mono hW hQ hW hQ (by rfl)
            hu zero_le_one hu zero_le_one hz
            (norm_nonneg Q) (norm_nonneg W) (norm_nonneg Q) (norm_nonneg Z)
        _ = u ^ 2 * z := by ring
    dsimp only [e3]
    rw [show Q * W * Q * W * Q * Z = Q * (W * Q * W * Q * Z) by noncomm_ring]
    exact hdual.trans (by nlinarith)
  have he4 : ‖e4‖ ≤ 2 * z * u ^ 2 := by
    have hdual := concreteCenteredOrbitalDirection_traceOne_dual_le_two_h14
      hN v (W * Q * T * Q.transpose * Ts)
    have htail : ‖W * Q * T * Q.transpose * Ts‖ ≤ z * u ^ 2 := by
      calc
        ‖W * Q * T * Q.transpose * Ts‖ ≤
            (((‖W‖ * ‖Q‖) * ‖T‖) * ‖Q.transpose‖) * ‖Ts‖ :=
          h13_l2_opNorm_mul_five_le W Q T Q.transpose Ts
        _ ≤ ((u * 1) * t) * 1 * t := by
          exact h13_mul_five_mono hW hQ (by rfl) hQt hTs.le
            hu zero_le_one ht0 zero_le_one ht0
            (norm_nonneg Q) (norm_nonneg T) (norm_nonneg Q.transpose) (norm_nonneg Ts)
        _ ≤ z * u ^ 2 := by nlinarith
    dsimp only [e4]
    rw [show Q * W * Q * T * Q.transpose * Ts =
        Q * (W * Q * T * Q.transpose * Ts) by noncomm_ring]
    exact hdual.trans (by nlinarith)
  have he5 : ‖e5‖ ≤ 4 * z * u ^ 2 := by
    have hdual := concreteCenteredOrbitalDirection_traceOne_dual_le_two_h14
      hN v (A * Q * T * Q.transpose * Ts)
    have htail : ‖A * Q * T * Q.transpose * Ts‖ ≤ 2 * z * u ^ 2 := by
      calc
        ‖A * Q * T * Q.transpose * Ts‖ ≤
            (((‖A‖ * ‖Q‖) * ‖T‖) * ‖Q.transpose‖) * ‖Ts‖ :=
          h13_l2_opNorm_mul_five_le A Q T Q.transpose Ts
        _ ≤ (((2 * u) * 1) * t) * 1 * t := by
          exact h13_mul_five_mono hA hQ (by rfl) hQt hTs.le
            (mul_nonneg (by norm_num) hu) zero_le_one ht0 zero_le_one ht0
            (norm_nonneg Q) (norm_nonneg T) (norm_nonneg Q.transpose) (norm_nonneg Ts)
        _ ≤ 2 * z * u ^ 2 := by nlinarith
    dsimp only [e5]
    rw [show Q * A * Q * T * Q.transpose * Ts =
        Q * (A * Q * T * Q.transpose * Ts) by noncomm_ring]
    exact hdual.trans (by nlinarith)
  have he6 : ‖e6‖ ≤ 4 * z * u ^ 2 := by
    let f₀ := Matrix.trace (Q * T * Q.transpose * Q.transpose * Ts)
    let f₁ := Matrix.trace
      (Q * T * Q.transpose * (Ts * C) * Q.transpose * Ts)
    have he6expand : e6 = f₀ + 2 * f₁ := by
      have hmat :
          Q * T * Q.transpose * (1 + 2 • (Ts * C)) * Q.transpose * Ts =
            Q * T * Q.transpose * Q.transpose * Ts +
              (Q * T * Q.transpose * (Ts * C) * Q.transpose * Ts +
                Q * T * Q.transpose * (Ts * C) * Q.transpose * Ts) := by
        simp only [two_nsmul]
        noncomm_ring
      dsimp only [e6, U, f₀, f₁]
      rw [hmat, Matrix.trace_add, Matrix.trace_add]
      ring
    have hf₀ : ‖f₀‖ ≤ 2 * z * u := by
      have hdual := concreteCenteredOrbitalDirection_traceOne_dual_le_two_h14
        hN v (T * Q.transpose * Q.transpose * Ts)
      have hfive := h13_l2_opNorm_mul_five_le
        T Q.transpose Q.transpose Ts (1 : ConcreteMatrixState N)
      have htail : ‖T * Q.transpose * Q.transpose * Ts‖ ≤ z * u := by
        rw [Matrix.mul_one, CStarRing.norm_one, mul_one] at hfive
        calc
          ‖T * Q.transpose * Q.transpose * Ts‖ ≤
              ((‖T‖ * ‖Q.transpose‖) * ‖Q.transpose‖) * ‖Ts‖ := hfive
          _ ≤ ((t * 1) * 1) * t := by
            have hmono := h13_mul_five_mono (by rfl) hQt hQt hTs.le
              (show (1 : ℝ) ≤ 1 by rfl)
              ht0 zero_le_one zero_le_one ht0 zero_le_one
              (norm_nonneg Q.transpose) (norm_nonneg Q.transpose)
              (norm_nonneg Ts) zero_le_one
            simpa only [mul_one] using hmono
          _ ≤ z * u := by nlinarith
      dsimp only [f₀]
      rw [show Q * T * Q.transpose * Q.transpose * Ts =
          Q * (T * Q.transpose * Q.transpose * Ts) by noncomm_ring]
      exact hdual.trans (by nlinarith)
    have hf₁eq : f₁ =
        Matrix.trace (Q * Z * Q * T * Q.transpose * Ts) := by
      dsimp only [f₁]
      rw [hinput]
      calc
        Matrix.trace (Q * T * Q.transpose * Z.transpose * Q.transpose * Ts) =
            Matrix.trace
              ((Q * T * Q.transpose * Z.transpose * Q.transpose * Ts).transpose) :=
          (Matrix.trace_transpose _).symm
        _ = Matrix.trace (Ts * Q * Z * Q * T * Q.transpose) := by
          congr 1
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hTsy, hTssymm]
          noncomm_ring
        _ = Matrix.trace (Ts * (Q * Z * Q * T * Q.transpose)) := by
          congr 1
          noncomm_ring
        _ = Matrix.trace ((Q * Z * Q * T * Q.transpose) * Ts) :=
          Matrix.trace_mul_comm _ _
        _ = Matrix.trace (Q * Z * Q * T * Q.transpose * Ts) := by rfl
    have hf₁ : ‖f₁‖ ≤ 2 * z ^ 2 * u := by
      have hdual := concreteCenteredOrbitalDirection_traceOne_dual_le_two_h14
        hN v (Z * Q * T * Q.transpose * Ts)
      have htail : ‖Z * Q * T * Q.transpose * Ts‖ ≤ z ^ 2 * u := by
        calc
          ‖Z * Q * T * Q.transpose * Ts‖ ≤
              (((‖Z‖ * ‖Q‖) * ‖T‖) * ‖Q.transpose‖) * ‖Ts‖ :=
            h13_l2_opNorm_mul_five_le Z Q T Q.transpose Ts
          _ ≤ (((z * 1) * t) * 1) * t := by
            exact h13_mul_five_mono (by rfl) hQ (by rfl) hQt hTs.le
              hz zero_le_one ht0 zero_le_one ht0
              (norm_nonneg Q) (norm_nonneg T)
              (norm_nonneg Q.transpose) (norm_nonneg Ts)
          _ ≤ z ^ 2 * u := by nlinarith
      rw [hf₁eq]
      rw [show Q * Z * Q * T * Q.transpose * Ts =
          Q * (Z * Q * T * Q.transpose * Ts) by noncomm_ring]
      exact hdual.trans (by nlinarith)
    rw [he6expand]
    calc
      ‖f₀ + 2 * f₁‖ ≤ ‖f₀‖ + ‖2 * f₁‖ := norm_add_le _ _
      _ = ‖f₀‖ + 2 * ‖f₁‖ := by rw [norm_mul]; norm_num
      _ ≤ (2 * z * u) + 2 * (2 * z ^ 2 * u) := by nlinarith
      _ ≤ 4 * z * u ^ 2 := by
        dsimp only [u]
        nlinarith
  change ‖e1 + e2 + e3 + e4 + e5 + e6‖ ≤ 16 * z * u ^ 2
  calc
    ‖e1 + e2 + e3 + e4 + e5 + e6‖ ≤
        ‖e1‖ + ‖e2‖ + ‖e3‖ + ‖e4‖ + ‖e5‖ + ‖e6‖ := by
      calc
        ‖e1 + e2 + e3 + e4 + e5 + e6‖ ≤
            ‖e1 + e2 + e3 + e4 + e5‖ + ‖e6‖ := norm_add_le _ _
        _ ≤ (‖e1 + e2 + e3 + e4‖ + ‖e5‖) + ‖e6‖ := by
          gcongr; exact norm_add_le _ _
        _ ≤ ((‖e1 + e2 + e3‖ + ‖e4‖) + ‖e5‖) + ‖e6‖ := by
          gcongr; exact norm_add_le _ _
        _ ≤ (((‖e1 + e2‖ + ‖e3‖) + ‖e4‖) + ‖e5‖) + ‖e6‖ := by
          gcongr; exact norm_add_le _ _
        _ ≤ ((((‖e1‖ + ‖e2‖) + ‖e3‖) + ‖e4‖) + ‖e5‖) + ‖e6‖ := by
          gcongr; exact norm_add_le _ _
    _ ≤ 16 * z * u ^ 2 := by nlinarith

/-- The exact six-word identity turns the operator estimate into the
corresponding bound for the differentiated third-score kernel. -/
theorem h13ThirdTraceKernelVelocity_norm_le
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (C : ConcreteMatrixState N) (hC : C.IsSymm)
    (hsupport : coeCornerSupport C) :
    ‖h13ThirdTraceKernelVelocity
        (concreteCenteredOrbitalDirection N v) C‖ ≤
      32 * ‖h13LedgerZ C‖ * (1 + ‖h13LedgerZ C‖) ^ 2 := by
  rw [h13ThirdTraceKernelVelocity_support_sixWord _ C hsupport,
    norm_mul]
  norm_num
  have hSix := h13ThirdTraceKernelSixWord_norm_le hN v C hC hsupport
  nlinarith

/-- Real-part form of the differentiated-kernel bound. -/
theorem h13ThirdTraceKernelVelocity_abs_re_le
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (C : ConcreteMatrixState N) (hC : C.IsSymm)
    (hsupport : coeCornerSupport C) :
    |(h13ThirdTraceKernelVelocity
        (concreteCenteredOrbitalDirection N v) C).re| ≤
      32 * ‖h13LedgerZ C‖ * (1 + ‖h13LedgerZ C‖) ^ 2 :=
  (Complex.abs_re_le_norm _).trans
    (h13ThirdTraceKernelVelocity_norm_le hN v C hC hsupport)

/-- Full derivative-free `ellOne*ellThree` ledger bound before its density
coefficient is restored. -/
theorem h13OneThreeTraceWordLedger_abs_le
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (C Y : ConcreteMatrixState N) (hC : C.IsSymm)
    (hsupport : coeCornerSupport C) :
    |h13OneThreeTraceWordLedger
        (concreteCenteredOrbitalDirection N v) C Y| ≤
      64 * ‖Y‖ * ‖h13LedgerZ C‖ *
        (1 + ‖h13LedgerZ C‖) ^ 2 := by
  unfold h13OneThreeTraceWordLedger
  rw [abs_mul]
  have hFirst := abs_re_trace_centeredDirection_mul_le_two_h14 hN v Y
  have hThird := h13ThirdTraceKernelVelocity_abs_re_le
    hN v C hC hsupport
  have hThird0 : 0 ≤
      32 * ‖h13LedgerZ C‖ * (1 + ‖h13LedgerZ C‖) ^ 2 := by
    positivity
  calc
    |(Matrix.trace (concreteCenteredOrbitalDirection N v * Y)).re| *
        |(h13ThirdTraceKernelVelocity
          (concreteCenteredOrbitalDirection N v) C).re| ≤
        (2 * ‖Y‖) *
          (32 * ‖h13LedgerZ C‖ * (1 + ‖h13LedgerZ C‖) ^ 2) :=
      mul_le_mul hFirst hThird (abs_nonneg _) (by positivity)
    _ = 64 * ‖Y‖ * ‖h13LedgerZ C‖ *
        (1 + ‖h13LedgerZ C‖) ^ 2 := by ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

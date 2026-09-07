import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_OneThreeTraceWordLedger
import Mathlib.Tactic

/-!
# H13 support normal form for the first resolvent velocity

The derivative-free H13 ledger was initially written in product-rule form,
with separate velocities for the corner and the input resolvent.  On the
open matrix ball those terms collapse to the standard output-side formula

`Z' = -((I+Z) Q Z + Z Q (I+Z) + 2 T Qᵀ Tᴴ)`.

This module proves that identity directly from finite matrix algebra.  It
contains no probability estimate or scientific declaration.
-/

open Matrix
open scoped ComplexOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

set_option maxHeartbeats 1200000

/-- Input/output resolvent push-through on the literal open-ball support. -/
theorem h13Ledger_outputInv_mul_corner_eq_corner_mul_inputInv
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    (h13LedgerOutputGap C)⁻¹ * C =
      C * (h13LedgerInputGap C)⁻¹ := by
  let H := h13LedgerInputGap C
  let G := h13LedgerOutputGap C
  have hH : H.PosDef := by
    unfold coeCornerSupport at hsupport
    simpa only [H, h13LedgerInputGap] using hsupport
  letI : Invertible H := hH.isUnit.invertible
  have hdet : Matrix.det G = Matrix.det H := by
    dsimp only [G, H, h13LedgerOutputGap, h13LedgerInputGap]
    exact Matrix.det_one_sub_mul_comm C C.conjTranspose
  have hGunit : IsUnit G := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet]
    exact (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  letI : Invertible G := hGunit.invertible
  have hGC : G * C = C * H := by
    dsimp only [G, H, h13LedgerOutputGap, h13LedgerInputGap]
    noncomm_ring
  change G⁻¹ * C = C * H⁻¹
  apply (Matrix.inv_mul_eq_iff_eq_mul_of_invertible G C (C * H⁻¹)).2
  rw [← Matrix.mul_assoc, hGC, Matrix.mul_assoc,
    Matrix.mul_inv_of_invertible, Matrix.mul_one]

/-- The output resolvent is `I+Z` on support. -/
theorem h13Ledger_outputInv_eq_one_add_Z
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    (h13LedgerOutputGap C)⁻¹ = 1 + h13LedgerZ C := by
  let H := h13LedgerInputGap C
  let G := h13LedgerOutputGap C
  have hH : H.PosDef := by
    unfold coeCornerSupport at hsupport
    simpa only [H, h13LedgerInputGap] using hsupport
  letI : Invertible H := hH.isUnit.invertible
  have hdet : Matrix.det G = Matrix.det H := by
    dsimp only [G, H, h13LedgerOutputGap, h13LedgerInputGap]
    exact Matrix.det_one_sub_mul_comm C C.conjTranspose
  have hGunit : IsUnit G := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet]
    exact (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  letI : Invertible G := hGunit.invertible
  have hpush : G⁻¹ * C = C * H⁻¹ := by
    simpa only [G, H] using
      h13Ledger_outputInv_mul_corner_eq_corner_mul_inputInv C hsupport
  change G⁻¹ = 1 + C * H⁻¹ * C.conjTranspose
  have hterm : G * (C * H⁻¹ * C.conjTranspose) =
      C * C.conjTranspose := by
    calc
      G * (C * H⁻¹ * C.conjTranspose) =
          (G * C) * H⁻¹ * C.conjTranspose := by noncomm_ring
      _ = (C * H) * H⁻¹ * C.conjTranspose := by
        have hGC : G * C = C * H := by
          dsimp only [G, H, h13LedgerOutputGap, h13LedgerInputGap]
          noncomm_ring
        rw [hGC]
      _ = C * (H * H⁻¹) * C.conjTranspose := by noncomm_ring
      _ = C * C.conjTranspose := by
        rw [Matrix.mul_inv_of_invertible, Matrix.mul_one]
  calc
    G⁻¹ = G⁻¹ * 1 := (Matrix.mul_one _).symm
    _ = 1 + C * H⁻¹ * C.conjTranspose :=
      (Matrix.inv_mul_eq_iff_eq_mul_of_invertible G 1
        (1 + C * H⁻¹ * C.conjTranspose)).2 (by
          rw [Matrix.mul_add, Matrix.mul_one, hterm]
          dsimp only [G, h13LedgerOutputGap]
          noncomm_ring)

/-- On support, the product-rule velocity in the exact ledger is the compact
output-side three-word expression. -/
theorem h13LedgerZVelocity_support_normal_form
    {N : ℕ} (Q C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    h13LedgerZVelocity Q C =
      -((1 + h13LedgerZ C) * Q * h13LedgerZ C +
        h13LedgerZ C * Q * (1 + h13LedgerZ C) +
        2 • (h13LedgerT C * Q.transpose *
          (h13LedgerT C).conjTranspose)) := by
  let H := h13LedgerInputGap C
  let G := h13LedgerOutputGap C
  let Hi := H⁻¹
  let W := G⁻¹
  have hH : H.PosDef := by
    unfold coeCornerSupport at hsupport
    simpa only [H, h13LedgerInputGap] using hsupport
  letI : Invertible H := hH.isUnit.invertible
  have hdet : Matrix.det G = Matrix.det H := by
    dsimp only [G, H, h13LedgerOutputGap, h13LedgerInputGap]
    exact Matrix.det_one_sub_mul_comm C C.conjTranspose
  have hGunit : IsUnit G := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet]
    exact (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  letI : Invertible G := hGunit.invertible
  have hpush : W * C = C * Hi := by
    simpa only [W, Hi, G, H] using
      h13Ledger_outputInv_mul_corner_eq_corner_mul_inputInv C hsupport
  have hHherm : H.IsHermitian := by
    dsimp only [H, h13LedgerInputGap]
    exact Matrix.isHermitian_one.sub
      (Matrix.isHermitian_conjTranspose_mul_self C)
  have hGherm : G.IsHermitian := by
    dsimp only [G, h13LedgerOutputGap]
    exact Matrix.isHermitian_one.sub
      (Matrix.isHermitian_mul_conjTranspose_self C)
  have hHinvHerm : Hi.IsHermitian := by
    simpa only [Hi] using hHherm.inv
  have hWinvHerm : W.IsHermitian := by
    simpa only [W] using hGherm.inv
  have hpushStar : Hi * C.conjTranspose = C.conjTranspose * W := by
    have h := congrArg Matrix.conjTranspose hpush
    simpa only [Matrix.conjTranspose_mul, hHinvHerm.eq,
      hWinvHerm.eq] using h.symm
  have hW : W = 1 + h13LedgerZ C := by
    simpa only [W, G] using h13Ledger_outputInv_eq_one_add_Z C hsupport
  have hTstar : (h13LedgerT C).conjTranspose = C.conjTranspose * W := by
    unfold h13LedgerT
    rw [Matrix.conjTranspose_mul]
    have hWstar : W.conjTranspose = W := hWinvHerm.eq
    simpa only [G, W, h13LedgerOutputGap] using
      congrArg (fun X ↦ C.conjTranspose * X) hWstar
  have hZ : W * C * C.conjTranspose = h13LedgerZ C := by
    rw [hpush]
    rfl
  have hTnormal : (1 + h13LedgerZ C) * C = h13LedgerT C := by
    rw [← hW]
    rfl
  have hTstarNormal :
      C.conjTranspose * (1 + h13LedgerZ C) =
        (h13LedgerT C).conjTranspose := by
    rw [← hW]
    exact hTstar.symm
  have hU : C.conjTranspose * h13LedgerT C =
      (h13LedgerT C).conjTranspose * C := by
    rw [hTstar]
    unfold h13LedgerT
    dsimp only [G, W]
    noncomm_ring
  have hTCstar :
      h13LedgerT C * C.conjTranspose = h13LedgerZ C := by
    change W * C * C.conjTranspose = h13LedgerZ C
    exact hZ
  have hCTstar :
      C * (h13LedgerT C).conjTranspose = h13LedgerZ C := by
    rw [hTstar, ← hpushStar]
    unfold h13LedgerZ
    dsimp only [Hi, H]
    noncomm_ring
  have hreshape :
      h13LedgerZVelocity Q C =
        h13LedgerCornerVelocity Q C * (Hi * C.conjTranspose) +
          (C * Hi) * h13LedgerCornerStarVelocity Q C *
            (C * Hi * C.conjTranspose) +
          (C * Hi * C.conjTranspose) *
            h13LedgerCornerVelocity Q C * (Hi * C.conjTranspose) +
          (C * Hi) * h13LedgerCornerStarVelocity Q C := by
    unfold h13LedgerZVelocity h13LedgerInputResolventVelocity
      h13LedgerInputGapVelocity
    dsimp only [Hi, H]
    noncomm_ring
  rw [hreshape, ← hpush, hpushStar]
  rw [hZ]
  change
    h13LedgerCornerVelocity Q C * (C.conjTranspose * W) +
          (W * C) * h13LedgerCornerStarVelocity Q C * h13LedgerZ C +
          h13LedgerZ C * h13LedgerCornerVelocity Q C *
            (C.conjTranspose * W) +
          (W * C) * h13LedgerCornerStarVelocity Q C = _
  rw [show W * C = h13LedgerT C by rfl, ← hTstar]
  let A : ConcreteMatrixState N := 1 + h13LedgerZ C
  have hleft :
      h13LedgerCornerVelocity Q C * (h13LedgerT C).conjTranspose +
          h13LedgerZ C * h13LedgerCornerVelocity Q C *
            (h13LedgerT C).conjTranspose =
        -(A * Q * h13LedgerZ C +
          h13LedgerT C * Q.transpose * (h13LedgerT C).conjTranspose) := by
    calc
      _ = A * h13LedgerCornerVelocity Q C *
          (h13LedgerT C).conjTranspose := by
            dsimp only [A]
            noncomm_ring
      _ = A * (-(Q * C + C * Q.transpose)) *
          (h13LedgerT C).conjTranspose := by
            rfl
      _ = -(A * Q * (C * (h13LedgerT C).conjTranspose) +
          (A * C) * Q.transpose * (h13LedgerT C).conjTranspose) := by
            noncomm_ring
      _ = -(A * Q * h13LedgerZ C +
          h13LedgerT C * Q.transpose * (h13LedgerT C).conjTranspose) := by
            rw [hCTstar]
            rw [show A * C = h13LedgerT C by
              simpa only [A] using hTnormal]
  have hright :
      h13LedgerT C * h13LedgerCornerStarVelocity Q C * h13LedgerZ C +
          h13LedgerT C * h13LedgerCornerStarVelocity Q C =
        -(h13LedgerT C * Q.transpose * (h13LedgerT C).conjTranspose +
          h13LedgerZ C * Q * A) := by
    calc
      _ = h13LedgerT C * h13LedgerCornerStarVelocity Q C * A := by
            dsimp only [A]
            noncomm_ring
      _ = h13LedgerT C *
          (-(Q.transpose * C.conjTranspose + C.conjTranspose * Q)) * A := by
            rfl
      _ = -(h13LedgerT C * Q.transpose * (C.conjTranspose * A) +
          (h13LedgerT C * C.conjTranspose) * Q * A) := by
            noncomm_ring
      _ = -(h13LedgerT C * Q.transpose * (h13LedgerT C).conjTranspose +
          h13LedgerZ C * Q * A) := by
            rw [hTCstar]
            rw [show C.conjTranspose * A =
                (h13LedgerT C).conjTranspose by
              simpa only [A] using hTstarNormal]
  calc
    _ =
        (h13LedgerCornerVelocity Q C * (h13LedgerT C).conjTranspose +
          h13LedgerZ C * h13LedgerCornerVelocity Q C *
            (h13LedgerT C).conjTranspose) +
        (h13LedgerT C * h13LedgerCornerStarVelocity Q C * h13LedgerZ C +
          h13LedgerT C * h13LedgerCornerStarVelocity Q C) := by
            noncomm_ring
    _ =
        -(A * Q * h13LedgerZ C +
          h13LedgerT C * Q.transpose * (h13LedgerT C).conjTranspose) +
        -(h13LedgerT C * Q.transpose * (h13LedgerT C).conjTranspose +
          h13LedgerZ C * Q * A) := by rw [hleft, hright]
    _ =
      -((1 + h13LedgerZ C) * Q * h13LedgerZ C +
        h13LedgerZ C * Q * (1 + h13LedgerZ C) +
        2 • (h13LedgerT C * Q.transpose *
          (h13LedgerT C).conjTranspose)) := by
            dsimp only [A]
            noncomm_ring

/-- The output resolvent has the same compact velocity as `Z`, since on
support it is exactly `I+Z`.  This proof is an independent algebraic check of
the velocity identity, rather than an appeal to differentiation. -/
theorem h13LedgerOutputResolventVelocity_support_normal_form
    {N : ℕ} (Q C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    h13LedgerOutputResolventVelocity Q C =
      -((1 + h13LedgerZ C) * Q * h13LedgerZ C +
        h13LedgerZ C * Q * (1 + h13LedgerZ C) +
        2 • (h13LedgerT C * Q.transpose *
          (h13LedgerT C).conjTranspose)) := by
  let H := h13LedgerInputGap C
  let G := h13LedgerOutputGap C
  let Hi := H⁻¹
  let W := G⁻¹
  have hH : H.PosDef := by
    unfold coeCornerSupport at hsupport
    simpa only [H, h13LedgerInputGap] using hsupport
  letI : Invertible H := hH.isUnit.invertible
  have hdet : Matrix.det G = Matrix.det H := by
    dsimp only [G, H, h13LedgerOutputGap, h13LedgerInputGap]
    exact Matrix.det_one_sub_mul_comm C C.conjTranspose
  have hGunit : IsUnit G := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet]
    exact (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  letI : Invertible G := hGunit.invertible
  have hpush : W * C = C * Hi := by
    simpa only [W, Hi, G, H] using
      h13Ledger_outputInv_mul_corner_eq_corner_mul_inputInv C hsupport
  have hGherm : G.IsHermitian := by
    dsimp only [G, h13LedgerOutputGap]
    exact Matrix.isHermitian_one.sub
      (Matrix.isHermitian_mul_conjTranspose_self C)
  have hWinvHerm : W.IsHermitian := by
    simpa only [W] using hGherm.inv
  have hW : W = 1 + h13LedgerZ C := by
    simpa only [W, G] using h13Ledger_outputInv_eq_one_add_Z C hsupport
  have hTstar : (h13LedgerT C).conjTranspose = C.conjTranspose * W := by
    unfold h13LedgerT
    rw [Matrix.conjTranspose_mul]
    have hWstar : W.conjTranspose = W := hWinvHerm.eq
    simpa only [G, W, h13LedgerOutputGap] using
      congrArg (fun X ↦ C.conjTranspose * X) hWstar
  have hTCstar :
      h13LedgerT C * C.conjTranspose = h13LedgerZ C := by
    change W * C * C.conjTranspose = h13LedgerZ C
    rw [hpush]
    rfl
  have hCTstar :
      C * (h13LedgerT C).conjTranspose = h13LedgerZ C := by
    have hHherm : H.IsHermitian := by
      dsimp only [H, h13LedgerInputGap]
      exact Matrix.isHermitian_one.sub
        (Matrix.isHermitian_conjTranspose_mul_self C)
    have hHinvHerm : Hi.IsHermitian := by
      simpa only [Hi] using hHherm.inv
    have hpushStar : Hi * C.conjTranspose = C.conjTranspose * W := by
      have h := congrArg Matrix.conjTranspose hpush
      simpa only [Matrix.conjTranspose_mul, hHinvHerm.eq,
        hWinvHerm.eq] using h.symm
    rw [hTstar, ← hpushStar]
    unfold h13LedgerZ
    dsimp only [Hi, H]
    noncomm_ring
  calc
    h13LedgerOutputResolventVelocity Q C =
        W * h13LedgerCornerVelocity Q C * (C.conjTranspose * W) +
          (W * C) * h13LedgerCornerStarVelocity Q C * W := by
      unfold h13LedgerOutputResolventVelocity h13LedgerOutputGapVelocity
      dsimp only [W, G]
      noncomm_ring
    _ = W * h13LedgerCornerVelocity Q C *
          (h13LedgerT C).conjTranspose +
        h13LedgerT C * h13LedgerCornerStarVelocity Q C * W := by
      rw [← hTstar, show W * C = h13LedgerT C by rfl]
    _ = -(W * Q * (C * (h13LedgerT C).conjTranspose) +
          (W * C) * Q.transpose * (h13LedgerT C).conjTranspose +
          h13LedgerT C * Q.transpose * (C.conjTranspose * W) +
          (h13LedgerT C * C.conjTranspose) * Q * W) := by
      unfold h13LedgerCornerVelocity h13LedgerCornerStarVelocity
      noncomm_ring
    _ = -(W * Q * h13LedgerZ C +
          h13LedgerZ C * Q * W +
          2 • (h13LedgerT C * Q.transpose *
            (h13LedgerT C).conjTranspose)) := by
      rw [hCTstar, hTCstar, ← hTstar,
        show W * C = h13LedgerT C by rfl]
      noncomm_ring
    _ = -((1 + h13LedgerZ C) * Q * h13LedgerZ C +
          h13LedgerZ C * Q * (1 + h13LedgerZ C) +
          2 • (h13LedgerT C * Q.transpose *
            (h13LedgerT C).conjTranspose)) := by rw [hW]

/-- Compact support normal form for the output-side factor velocity.  With
`U=TᴴC`, it is

`T' = -((I+2Z)QT + TQᵀ(I+2U))`.
-/
theorem h13LedgerTVelocity_support_normal_form
    {N : ℕ} (Q C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    h13LedgerTVelocity Q C =
      -((1 + 2 • h13LedgerZ C) * Q * h13LedgerT C +
        h13LedgerT C * Q.transpose *
          (1 + 2 • ((h13LedgerT C).conjTranspose * C))) := by
  let G := h13LedgerOutputGap C
  let W := G⁻¹
  have hW : W = 1 + h13LedgerZ C := by
    simpa only [W, G] using h13Ledger_outputInv_eq_one_add_Z C hsupport
  have hWC : W * C = h13LedgerT C := by rfl
  have hZC : h13LedgerZ C * C + C = W * C := by
    rw [hW]
    noncomm_ring
  rw [h13LedgerTVelocity]
  rw [h13LedgerOutputResolventVelocity_support_normal_form Q C hsupport]
  change
    -((1 + h13LedgerZ C) * Q * h13LedgerZ C +
        h13LedgerZ C * Q * (1 + h13LedgerZ C) +
        2 • (h13LedgerT C * Q.transpose *
          (h13LedgerT C).conjTranspose)) * C +
      W * h13LedgerCornerVelocity Q C = _
  calc
    _ = -(W * Q * (h13LedgerZ C * C + C) +
          h13LedgerZ C * Q * (W * C) +
          2 • (h13LedgerT C * Q.transpose *
            ((h13LedgerT C).conjTranspose * C)) +
          (W * C) * Q.transpose) := by
      rw [hW]
      unfold h13LedgerCornerVelocity
      noncomm_ring
    _ = -(W * Q * h13LedgerT C +
          h13LedgerZ C * Q * h13LedgerT C +
          2 • (h13LedgerT C * Q.transpose *
            ((h13LedgerT C).conjTranspose * C)) +
          h13LedgerT C * Q.transpose) := by rw [hZC, hWC]
    _ = -((1 + 2 • h13LedgerZ C) * Q * h13LedgerT C +
          h13LedgerT C * Q.transpose *
            (1 + 2 • ((h13LedgerT C).conjTranspose * C))) := by
      rw [hW]
      noncomm_ring

/-- Adjoint compact normal form for the final velocity in the H13 ledger. -/
theorem h13LedgerTStarVelocity_support_normal_form
    {N : ℕ} (Q C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    h13LedgerTStarVelocity Q C =
      -((h13LedgerT C).conjTranspose * Q *
          (1 + 2 • h13LedgerZ C) +
        (1 + 2 • ((h13LedgerT C).conjTranspose * C)) *
          Q.transpose * (h13LedgerT C).conjTranspose) := by
  let G := h13LedgerOutputGap C
  let W := G⁻¹
  have hH : (h13LedgerInputGap C).PosDef := by
    unfold coeCornerSupport at hsupport
    simpa only [h13LedgerInputGap] using hsupport
  have hdet : Matrix.det G = Matrix.det (h13LedgerInputGap C) := by
    dsimp only [G, h13LedgerOutputGap, h13LedgerInputGap]
    exact Matrix.det_one_sub_mul_comm C C.conjTranspose
  have hGunit : IsUnit G := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet]
    exact (Matrix.isUnit_iff_isUnit_det (h13LedgerInputGap C)).mp hH.isUnit
  letI : Invertible G := hGunit.invertible
  have hGherm : G.IsHermitian := by
    dsimp only [G, h13LedgerOutputGap]
    exact Matrix.isHermitian_one.sub
      (Matrix.isHermitian_mul_conjTranspose_self C)
  have hWinvHerm : W.IsHermitian := by
    simpa only [W] using hGherm.inv
  have hW : W = 1 + h13LedgerZ C := by
    simpa only [W, G] using h13Ledger_outputInv_eq_one_add_Z C hsupport
  have hTstar : (h13LedgerT C).conjTranspose = C.conjTranspose * W := by
    unfold h13LedgerT
    rw [Matrix.conjTranspose_mul]
    have hWstar : W.conjTranspose = W := hWinvHerm.eq
    simpa only [G, W, h13LedgerOutputGap] using
      congrArg (fun X ↦ C.conjTranspose * X) hWstar
  have hTstarNormal :
      C.conjTranspose * (1 + h13LedgerZ C) =
        (h13LedgerT C).conjTranspose := by
    rw [← hW]
    exact hTstar.symm
  have hUstar : C.conjTranspose * h13LedgerT C =
      (h13LedgerT C).conjTranspose * C := by
    rw [hTstar]
    unfold h13LedgerT
    dsimp only [G, W]
    noncomm_ring
  rw [h13LedgerTStarVelocity]
  rw [h13LedgerOutputResolventVelocity_support_normal_form Q C hsupport]
  change
    h13LedgerCornerStarVelocity Q C * W +
      C.conjTranspose *
        -((1 + h13LedgerZ C) * Q * h13LedgerZ C +
          h13LedgerZ C * Q * (1 + h13LedgerZ C) +
          2 • (h13LedgerT C * Q.transpose *
            (h13LedgerT C).conjTranspose)) = _
  calc
    _ = -(Q.transpose * (C.conjTranspose * W) +
          (C.conjTranspose + C.conjTranspose * h13LedgerZ C) * Q * W +
          (C.conjTranspose * W) * Q * h13LedgerZ C +
          2 • ((C.conjTranspose * h13LedgerT C) * Q.transpose *
            (h13LedgerT C).conjTranspose)) := by
      rw [hW]
      unfold h13LedgerCornerStarVelocity
      noncomm_ring
    _ = -(Q.transpose * (h13LedgerT C).conjTranspose +
          (h13LedgerT C).conjTranspose * Q * W +
          (h13LedgerT C).conjTranspose * Q * h13LedgerZ C +
          2 • (((h13LedgerT C).conjTranspose * C) * Q.transpose *
            (h13LedgerT C).conjTranspose)) := by
      rw [← hTstar, hUstar, show C.conjTranspose +
          C.conjTranspose * h13LedgerZ C =
          (h13LedgerT C).conjTranspose by
        calc
          C.conjTranspose + C.conjTranspose * h13LedgerZ C =
              C.conjTranspose * (1 + h13LedgerZ C) := by noncomm_ring
          _ = (h13LedgerT C).conjTranspose := hTstarNormal]
    _ = -((h13LedgerT C).conjTranspose * Q *
            (1 + 2 • h13LedgerZ C) +
          (1 + 2 • ((h13LedgerT C).conjTranspose * C)) *
            Q.transpose * (h13LedgerT C).conjTranspose) := by
      rw [hW]
      noncomm_ring

/-- The six cyclic trace words left after all four support velocities are
substituted and cyclic duplicates are collected. -/
def h13ThirdTraceKernelSixWord {N : ℕ}
    (Q C : ConcreteMatrixState N) : ℂ :=
  Matrix.trace
      (Q * (1 + h13LedgerZ C) * Q * h13LedgerZ C * Q * h13LedgerZ C) +
    Matrix.trace
      (Q * h13LedgerT C * Q.transpose * (h13LedgerT C).conjTranspose *
        Q * h13LedgerZ C) +
    Matrix.trace
      (Q * (1 + h13LedgerZ C) * Q * (1 + h13LedgerZ C) *
        Q * h13LedgerZ C) +
    Matrix.trace
      (Q * (1 + h13LedgerZ C) * Q * h13LedgerT C * Q.transpose *
        (h13LedgerT C).conjTranspose) +
    Matrix.trace
      (Q * (1 + 2 • h13LedgerZ C) * Q * h13LedgerT C * Q.transpose *
        (h13LedgerT C).conjTranspose) +
    Matrix.trace
      (Q * h13LedgerT C * Q.transpose *
        (1 + 2 • ((h13LedgerT C).conjTranspose * C)) * Q.transpose *
        (h13LedgerT C).conjTranspose)

/-- Exact inverse-free six-word normal form of the differentiated third-score
kernel on the open matrix ball. -/
theorem h13ThirdTraceKernelVelocity_support_sixWord
    {N : ℕ} (Q C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    h13ThirdTraceKernelVelocity Q C =
      -2 * h13ThirdTraceKernelSixWord Q C := by
  let Z := h13LedgerZ C
  let T := h13LedgerT C
  let Ts := (h13LedgerT C).conjTranspose
  let W : ConcreteMatrixState N := 1 + Z
  let A : ConcreteMatrixState N := 1 + 2 • Z
  let U : ConcreteMatrixState N := 1 + 2 • (Ts * C)
  have hcycA :
      Matrix.trace (Q * Z * Q * W * Q * Z) =
        Matrix.trace (Q * W * Q * Z * Q * Z) := by
    calc
      Matrix.trace (Q * Z * Q * W * Q * Z) =
          Matrix.trace ((Q * Z) * (Q * W * Q * Z)) := by
            congr 1
            noncomm_ring
      _ = Matrix.trace ((Q * W * Q * Z) * (Q * Z)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Q * W * Q * Z * Q * Z) := by
        congr 1
        noncomm_ring
  have hcycB :
      Matrix.trace (Q * W * Q * Z * Q * W) =
        Matrix.trace (Q * W * Q * W * Q * Z) := by
    calc
      Matrix.trace (Q * W * Q * Z * Q * W) =
          Matrix.trace ((Q * W * Q * Z) * (Q * W)) := by
            congr 1
            noncomm_ring
      _ = Matrix.trace ((Q * W) * (Q * W * Q * Z)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Q * W * Q * W * Q * Z) := by
        congr 1
        noncomm_ring
  have hcycC :
      Matrix.trace (Q * T * Q.transpose * Ts * Q * A) =
        Matrix.trace (Q * A * Q * T * Q.transpose * Ts) := by
    calc
      Matrix.trace (Q * T * Q.transpose * Ts * Q * A) =
          Matrix.trace ((Q * T * Q.transpose * Ts) * (Q * A)) := by
            congr 1
            noncomm_ring
      _ = Matrix.trace ((Q * A) * (Q * T * Q.transpose * Ts)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Q * A * Q * T * Q.transpose * Ts) := by
        congr 1
        noncomm_ring
  unfold h13ThirdTraceKernelVelocity
  rw [h13LedgerZVelocity_support_normal_form Q C hsupport,
    h13LedgerTVelocity_support_normal_form Q C hsupport,
    h13LedgerTStarVelocity_support_normal_form Q C hsupport]
  change
    Matrix.trace (Q * (-(W * Q * Z + Z * Q * W +
          2 • (T * Q.transpose * Ts))) * Q * Z) +
      Matrix.trace (Q * W * Q *
        (-(W * Q * Z + Z * Q * W +
          2 • (T * Q.transpose * Ts)))) +
      Matrix.trace (Q *
        (-(A * Q * T + T * Q.transpose * U)) *
          Q.transpose * Ts) +
      Matrix.trace (Q * T * Q.transpose *
        (-(Ts * Q * A + U * Q.transpose * Ts))) = _
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_neg, Matrix.trace_add,
    Matrix.trace_smul, smul_eq_mul]
  change _ = -2 * h13ThirdTraceKernelSixWord Q C
  unfold h13ThirdTraceKernelSixWord
  dsimp only [Z, T, Ts, W, A, U] at hcycA hcycB hcycC ⊢
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc] at hcycA hcycB hcycC ⊢
  rw [hcycA, hcycB, hcycC]
  ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

import A2.TakagiCayleyTangent
import A2.OrbitMeasureCoordinateVolume

open scoped Matrix

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

def takagiAngularEmbed {N : ℕ} (a : TakagiAngularCoordinates N) : TakagiRealCoordinates N :=
  fun p => if hp : IsTakagiRadialKey p then 0 else a ⟨p, hp⟩

def takagiSkewAngularCoordinates {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) :
    TakagiAngularCoordinates N := fun p =>
  if p.val.2 = 0 then (H p.val.1.val.1 p.val.1.val.2).re
  else (H p.val.1.val.1 p.val.1.val.2).im

theorem takagiSkewAngularCoordinates_skewMatrix {N : ℕ} (a : TakagiAngularCoordinates N) :
    takagiSkewAngularCoordinates (takagiSkewMatrix (takagiAngularEmbed a)) = a := by
  funext ⟨⟨⟨⟨i, j⟩, hij⟩, b⟩, hp⟩
  by_cases he : i = j
  · subst j
    have hb : b ≠ 0 := fun h => hp ⟨rfl, h⟩
    have hb' : b = 1 := by fin_cases b <;> simp_all
    subst b
    simp [takagiSkewAngularCoordinates, takagiSkewMatrix, takagiAngularEmbed,
      IsTakagiRadialKey]
  · fin_cases b <;>
      simp [takagiSkewAngularCoordinates, takagiSkewMatrix, takagiAngularEmbed,
        IsTakagiRadialKey, he, hij]

theorem takagiSkewMatrix_angularCoordinates {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
    (hH : H.conjTranspose = -H) :
    takagiSkewMatrix (takagiAngularEmbed (takagiSkewAngularCoordinates H)) = H := by
  ext i j
  have hh (i j : Fin N) : star (H j i) = -H i j :=
    congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M i j) hH
  by_cases he : i = j
  · subst j
    have hr : (H i i).re = 0 := by
      have he' := congrArg Complex.re (hh i i)
      change (H i i).re = -(H i i).re at he'
      linarith
    apply Complex.ext <;>
      simp [takagiSkewMatrix, takagiAngularEmbed, IsTakagiRadialKey,
        takagiSkewAngularCoordinates, hr]
  · by_cases hij : i ≤ j
    · apply Complex.ext <;>
        simp [takagiSkewMatrix, takagiAngularEmbed, IsTakagiRadialKey,
          takagiSkewAngularCoordinates, he, hij]
    · have hji : j ≤ i := le_of_not_ge hij
      simp only [takagiSkewMatrix, he, if_false, hij]
      simp only [takagiAngularEmbed, IsTakagiRadialKey, Ne.symm he,
        false_and, dite_false, takagiSkewAngularCoordinates,
        show (1 : Fin 2) ≠ 0 by decide, if_false, if_true]
      simpa only [neg_eq_iff_eq_neg] using hh i j

def takagiAngularSkewEquiv (N : ℕ) :
    TakagiAngularCoordinates N ≃ₗ[ℝ] takagiSkewHermitianSpace N where
  toFun a := ⟨takagiSkewMatrix (takagiAngularEmbed a), takagiSkewMatrix_skewHermitian _⟩
  invFun H := takagiSkewAngularCoordinates H
  left_inv := takagiSkewAngularCoordinates_skewMatrix
  right_inv H := Subtype.ext (takagiSkewMatrix_angularCoordinates
    (H : Matrix (Fin N) (Fin N) ℂ)
    (show (H : Matrix (Fin N) (Fin N) ℂ).conjTranspose = -H from H.property))
  map_add' a b := by
    apply Subtype.ext
    have he : takagiAngularEmbed (a + b) = takagiAngularEmbed a + takagiAngularEmbed b := by
      funext p
      by_cases hp : IsTakagiRadialKey p <;> simp [takagiAngularEmbed, hp]
    rw [he]
    exact (takagiSkewLinearMap N).map_add _ _
  map_smul' r a := by
    apply Subtype.ext
    have he : takagiAngularEmbed (r • a) = r • takagiAngularEmbed a := by
      funext p
      by_cases hp : IsTakagiRadialKey p <;> simp [takagiAngularEmbed, hp]
    rw [he]
    exact (takagiSkewLinearMap N).map_smul _ _

def takagiCayleyAngularCoordinateEquiv {N : ℕ} (a : TakagiAngularCoordinates N) :
    TakagiAngularCoordinates N ≃ₗ[ℝ] TakagiAngularCoordinates N :=
  (takagiAngularSkewEquiv N).trans
    ((takagiCayleyAngularEquiv (takagiAngularSkewEquiv N a)
      (show ((takagiAngularSkewEquiv N a) : Matrix (Fin N) (Fin N) ℂ).conjTranspose =
        -(takagiAngularSkewEquiv N a) from (takagiAngularSkewEquiv N a).property)).trans
          (takagiAngularSkewEquiv N).symm)

theorem takagiCayleyAngularCoordinateEquiv_det_ne_zero {N : ℕ}
    (a : TakagiAngularCoordinates N) :
    LinearMap.det (takagiCayleyAngularCoordinateEquiv a).toLinearMap ≠ 0 :=
  (takagiCayleyAngularCoordinateEquiv a).isUnit_det'.ne_zero

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

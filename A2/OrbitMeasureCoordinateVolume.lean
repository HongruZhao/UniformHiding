import A2.OrbitJacobianDiagonal

open MeasureTheory MeasureTheory.Measure Set
open scoped BigOperators ENNReal

noncomputable section

namespace A2Research

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

def zeroCoordinateKeyEquiv (J : Type*) : J ≃ {p : J × Fin 2 // p.2 = 0} where
  toFun j := ⟨(j, 0), rfl⟩
  invFun p := p.1.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨j, b⟩, hb⟩
    change b = 0 at hb
    subst b
    rfl

def oneCoordinateKeyEquiv (J : Type*) : J ≃ {p : J × Fin 2 // ¬p.2 = 0} where
  toFun j := ⟨(j, 1), by change (1 : Fin 2) ≠ 0; decide⟩
  invFun p := p.1.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨j, b⟩, hb⟩
    have hb' : b = 1 := by fin_cases b <;> simp_all
    subst b
    rfl

def realPairCoordinateSplitEquiv (J : Type*) :
    (J × Fin 2 → ℝ) ≃ᵐ (J → ℝ) × (J → ℝ) := by
  classical
  exact (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : J × Fin 2 ↦ ℝ)
    (fun p ↦ p.2 = 0)).trans
    ((MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) (zeroCoordinateKeyEquiv J).symm).prodCongr
      (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) (oneCoordinateKeyEquiv J).symm))

theorem volume_preserving_realPairCoordinateSplitEquiv
    (J : Type*) [Fintype J] : MeasurePreserving (realPairCoordinateSplitEquiv J) := by
  classical
  exact ((volume_measurePreserving_piCongrLeft (fun _ ↦ ℝ)
      (zeroCoordinateKeyEquiv J).symm).prod
    (volume_measurePreserving_piCongrLeft (fun _ ↦ ℝ)
      (oneCoordinateKeyEquiv J).symm)).comp
    (volume_preserving_piEquivPiSubtypeProd (fun _ : J × Fin 2 ↦ ℝ)
      (fun p ↦ p.2 = 0))

/-- The Cartesian real/imaginary grouping preserves the actual product
Lebesgue measure, including the normalization of each complex coordinate. -/
theorem volume_preserving_realPairComplexCoordinates
    (J : Type*) [Fintype J] :
    MeasurePreserving (fun x : J × Fin 2 → ℝ ↦
      fun j : J ↦ (⟨x (j, 0), x (j, 1)⟩ : ℂ)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ J
  have hjoin : MeasurePreserving e.symm :=
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ J).symm e
  have hc : MeasurePreserving (fun a : J → ℝ × ℝ ↦
      fun j : J ↦ Complex.measurableEquivRealProd.symm (a j)) :=
    volume_preserving_pi fun _ ↦
      Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  convert hc.comp (hjoin.comp (volume_preserving_realPairCoordinateSplitEquiv J)) using 1
  rfl

end A2Research

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

set_option backward.isDefEq.respectTransparency false

def IsTakagiRadialKey {N : ℕ} (p : TakagiRealCoordinateIndex N) : Prop :=
  p.1.val.1 = p.1.val.2 ∧ p.2 = 0

instance (N : ℕ) : DecidablePred (@IsTakagiRadialKey N) :=
  fun p ↦ inferInstanceAs (Decidable (p.1.val.1 = p.1.val.2 ∧ p.2 = 0))

abbrev TakagiAngularCoordinateIndex (N : ℕ) :=
  {p : TakagiRealCoordinateIndex N // ¬IsTakagiRadialKey p}

abbrev TakagiAngularCoordinates (N : ℕ) := TakagiAngularCoordinateIndex N → ℝ

def takagiRadialKey {N : ℕ} (i : Fin N) : TakagiRealCoordinateIndex N :=
  (⟨(i, i), le_rfl⟩, 0)

def takagiRadialKeyEquiv (N : ℕ) : Fin N ≃ {p : TakagiRealCoordinateIndex N //
    IsTakagiRadialKey p} where
  toFun i := ⟨takagiRadialKey i, ⟨rfl, rfl⟩⟩
  invFun p := p.1.1.val.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨⟨⟨i, j⟩, hij⟩, b⟩, ⟨hd, hb⟩⟩
    change i = j at hd
    change b = 0 at hb
    subst j
    subst b
    rfl

def takagiAngularRadialCoordinatesEquiv (N : ℕ) :
    TakagiRealCoordinates N ≃ᵐ TakagiAngularCoordinates N × (Fin N → ℝ) := by
  classical
  exact ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : TakagiRealCoordinateIndex N ↦ ℝ)
      IsTakagiRadialKey).trans
    ((MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) (takagiRadialKeyEquiv N).symm).prodCongr
      (MeasurableEquiv.refl (TakagiAngularCoordinates N)))).trans
    MeasurableEquiv.prodComm

@[simp] theorem takagiAngularRadialCoordinatesEquiv_fst_apply
    {N : ℕ} (x : TakagiRealCoordinates N) (p : TakagiAngularCoordinateIndex N) :
    (takagiAngularRadialCoordinatesEquiv N x).1 p = x p.1 := rfl

@[simp] theorem takagiAngularRadialCoordinatesEquiv_snd_apply
    {N : ℕ} (x : TakagiRealCoordinates N) (i : Fin N) :
    (takagiAngularRadialCoordinatesEquiv N x).2 i = x (takagiRadialKey i) := rfl

/-- The full real radial/angular key split has product volume exactly. -/
theorem volume_preserving_takagiAngularRadialCoordinatesEquiv (N : ℕ) :
    MeasurePreserving (takagiAngularRadialCoordinatesEquiv N)
      (volume : Measure (TakagiRealCoordinates N))
      (volume : Measure (TakagiAngularCoordinates N × (Fin N → ℝ))) := by
  classical
  have hs := volume_preserving_piEquivPiSubtypeProd
    (fun _ : TakagiRealCoordinateIndex N ↦ ℝ) IsTakagiRadialKey
  have hr := volume_measurePreserving_piCongrLeft (fun _ ↦ ℝ) (takagiRadialKeyEquiv N).symm
  exact (measurePreserving_swap (μ := (volume : Measure (Fin N → ℝ)))
    (ν := (volume : Measure (TakagiAngularCoordinates N)))).comp
    ((hr.prod (MeasurePreserving.id _)).comp hs)

theorem measurePreserving_takagiRealComplexCoordinatesEquiv (N : ℕ) :
    MeasurePreserving (takagiRealComplexCoordinatesEquiv N)
      (volume : Measure (TakagiRealCoordinates N)) (complexSymmetricCoordinateVolume N) :=
  A2Research.volume_preserving_realPairComplexCoordinates (ComplexSymmetricCoordinateIndex N)

theorem map_takagiRealComplexCoordinatesEquiv_volume (N : ℕ) :
    Measure.map (takagiRealComplexCoordinatesEquiv N)
      (volume : Measure (TakagiRealCoordinates N)) = complexSymmetricCoordinateVolume N :=
  (measurePreserving_takagiRealComplexCoordinatesEquiv N).map_eq

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

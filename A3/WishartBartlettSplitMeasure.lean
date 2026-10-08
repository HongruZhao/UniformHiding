import A3.WishartBartlettMeasure
import A3.WishartCholeskySplit

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
namespace A3Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def wishartUpperIndexHeadTailEquiv (n : ℕ) :
    Fin n ⊕ HermitianCoordinateIndex n ≃ HermitianCoordinateIndex (n + 1) where
  toFun := Sum.elim (fun j ↦ ⟨(0, j.succ), Fin.succ_pos j⟩)
    (fun ij ↦ ⟨(ij.1.1.succ, ij.1.2.succ), Fin.succ_lt_succ_iff.mpr ij.2⟩)
  invFun ij := if hi : ij.1.1 = 0 then
    Sum.inl (ij.1.2.pred (ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) ij.2)))
    else Sum.inr ⟨(ij.1.1.pred hi,
      ij.1.2.pred (ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) ij.2))), by
        apply Fin.succ_lt_succ_iff.mp
        simpa only [Fin.succ_pred] using ij.2⟩
  left_inv := by
    rintro (j | ij) <;> simp
  right_inv := by
    intro ij
    by_cases hi : ij.1.1 = 0
    · apply Subtype.ext
      simp [hi]
      exact Prod.ext hi.symm rfl
    · apply Subtype.ext
      simp [hi]

theorem measurePreserving_fourCoordinateShuffle
    {P Q Z Y : Type*} [MeasurableSpace P] [MeasurableSpace Q]
    [MeasurableSpace Z] [MeasurableSpace Y]
    (muP : Measure P) (muQ : Measure Q) (muZ : Measure Z) (muY : Measure Y)
    [SFinite muP] [SFinite muQ] [SFinite muZ] [SFinite muY] :
    MeasurePreserving (fun x : (P × Q) × (Z × Y) ↦ (x.1.1, (x.2.1, (x.1.2, x.2.2))))
      ((muP.prod muQ).prod (muZ.prod muY)) (muP.prod (muZ.prod (muQ.prod muY))) := by
  have h1 := measurePreserving_prodAssoc muP muQ (muZ.prod muY)
  have h2 := (MeasurePreserving.id muP).prod
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc muQ muZ muY))
  have h3 := (MeasurePreserving.id muP).prod
    ((Measure.measurePreserving_swap (μ := muQ) (ν := muZ)).prod (MeasurePreserving.id muY))
  have h4 := (MeasurePreserving.id muP).prod (measurePreserving_prodAssoc muZ muQ muY)
  simpa [Function.comp_def, Prod.map, MeasurableEquiv.prodAssoc] using
    h4.comp (h3.comp (h2.comp h1))

theorem wishartBartlettShape_head {n : ℕ} (alpha : ℝ) (K : Type*) [RCLike K] :
    wishartBartlettShape alpha K (0 : Fin (n + 1)) = alpha := by
  simp [wishartBartlettShape]

theorem wishartBartlettShape_tail {n : ℕ} (alpha : ℝ) (K : Type*) [RCLike K]
    (i : Fin n) :
    wishartBartlettShape alpha K i.succ =
      wishartBartlettShape (alpha - (Module.finrank ℝ K : ℝ) / 2) K i := by
  simp only [wishartBartlettShape, Fin.val_succ, Nat.cast_add, Nat.cast_one]
  ring

theorem measurePreserving_wishartUpperSplit {n : ℕ} {K : Type*}
    [MeasurableSpace K] (gaussianField : Measure K) [SigmaFinite gaussianField] :
    MeasurePreserving
      (fun z : HermitianCoordinateIndex (n + 1) → K ↦
        (fun j ↦ z ⟨(0, j.succ), Fin.succ_pos j⟩,
          fun ij ↦ z ⟨(ij.1.1.succ, ij.1.2.succ), Fin.succ_lt_succ_iff.mpr ij.2⟩))
      (Measure.pi (fun _ : HermitianCoordinateIndex (n + 1) ↦ gaussianField))
      ((Measure.pi (fun _ : Fin n ↦ gaussianField)).prod
        (Measure.pi (fun _ : HermitianCoordinateIndex n ↦ gaussianField))) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : HermitianCoordinateIndex (n + 1) ↦ K)
    (wishartUpperIndexHeadTailEquiv n)
  have h1 := MeasurePreserving.symm e
    (measurePreserving_piCongrLeft (fun _ : HermitianCoordinateIndex (n + 1) ↦ gaussianField)
      (wishartUpperIndexHeadTailEquiv n))
  have h2 := measurePreserving_sumPiEquivProdPi
    (fun _ : Fin n ⊕ HermitianCoordinateIndex n ↦ gaussianField)
  convert h2.comp h1 using 1
  funext z
  apply Prod.ext <;> funext i <;> rfl

theorem measurePreserving_wishartCoordinatesSplit {n : ℕ} {K : Type*}
    [RCLike K] [MeasureSpace K] [BorelSpace K] {alpha : ℝ}
    (gaussianField : Measure K) [IsProbabilityMeasure gaussianField]
    (ha : ∀ i : Fin (n + 1), 0 < wishartBartlettShape alpha K i) :
    MeasurePreserving (wishartCoordinatesSplit : HermitianCoordinates (n + 1) K → _)
      (wishartBartlettMeasure (n + 1) alpha gaussianField)
      ((gammaMeasure alpha 1).prod
        ((Measure.pi (fun _ : Fin n ↦ gaussianField)).prod
          (wishartBartlettMeasure n (alpha - (Module.finrank ℝ K : ℝ) / 2) gaussianField))) := by
  letI (i : Fin (n + 1)) : IsProbabilityMeasure
      (gammaMeasure (wishartBartlettShape alpha K i) 1) :=
    isProbabilityMeasure_gammaMeasure (ha i) (by norm_num)
  have hap : 0 < alpha := by simpa [wishartBartlettShape] using ha 0
  letI : IsProbabilityMeasure (gammaMeasure alpha 1) :=
    isProbabilityMeasure_gammaMeasure hap (by norm_num)
  letI (i : Fin n) : IsProbabilityMeasure
      (gammaMeasure (wishartBartlettShape
        (alpha - (Module.finrank ℝ K : ℝ) / 2) K i) 1) :=
    isProbabilityMeasure_gammaMeasure (by rw [← wishartBartlettShape_tail]; exact ha i.succ)
      (by norm_num)
  have hdiag := measurePreserving_piFinSuccAbove
    (fun i : Fin (n + 1) ↦ gammaMeasure (wishartBartlettShape alpha K i) 1) 0
  have hdiag' : MeasurePreserving (fun q : Fin (n + 1) → ℝ ↦
      (q 0, fun i : Fin n ↦ q i.succ))
      (Measure.pi (fun i : Fin (n + 1) ↦ gammaMeasure (wishartBartlettShape alpha K i) 1))
      ((gammaMeasure alpha 1).prod (Measure.pi (fun i : Fin n ↦
        gammaMeasure (wishartBartlettShape
          (alpha - (Module.finrank ℝ K : ℝ) / 2) K i) 1))) := by
    simp only [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv,
      Fin.zero_succAbove, wishartBartlettShape_head, wishartBartlettShape_tail] at hdiag
    convert! hdiag using 1
  have hsplit := hdiag'.prod (measurePreserving_wishartUpperSplit (n := n) gaussianField)
  have hshuffle := measurePreserving_fourCoordinateShuffle (gammaMeasure alpha 1)
    (Measure.pi (fun i : Fin n ↦ gammaMeasure
      (wishartBartlettShape (alpha - (Module.finrank ℝ K : ℝ) / 2) K i) 1))
    (Measure.pi (fun _ : Fin n ↦ gaussianField))
    (Measure.pi (fun _ : HermitianCoordinateIndex n ↦ gaussianField))
  convert! hshuffle.comp hsplit using 1

theorem wishartComplexBartlettMeasure_split {n : ℕ} {alpha : ℝ}
    (ha : ∀ i : Fin (n + 1), 0 < wishartBartlettShape alpha ℂ i) :
    (wishartComplexBartlettMeasure (n + 1) alpha).map wishartCoordinatesSplit =
      (gammaMeasure alpha 1).prod
        ((LogdetLean.GramHafnian.circularGaussianVector n).prod
          (wishartComplexBartlettMeasure n (alpha - 1))) := by
  letI := circularGaussian_isProbabilityMeasure
  simpa [wishartComplexBartlettMeasure, Complex.finrank_real_complex,
    LogdetLean.GramHafnian.circularGaussianVector] using
    (measurePreserving_wishartCoordinatesSplit
      LogdetLean.GramHafnian.circularGaussian ha).map_eq

end A3Research

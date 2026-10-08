import A3.HermitianFlagChartOpen
import A3.FlagAction
import A3.Shared.OrbitMeasureCompactAtlas

open MeasureTheory MeasureTheory.Measure Set Function Metric
open scoped BigOperators ENNReal

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]

/-- Finite translates of the actual bounded open flag chart. Disjointification
assigns each projector flag to exactly one angular source piece. -/
theorem exists_finite_hermitian_flag_atlas
    (n : ℕ) (K : Type*) [RCLike K] [MeasurableSpace K] [BorelSpace K] [PolishSpace K] :
    ∃ r : ℝ, ∃ m : ℕ, ∃ c : Fin (m + 1) → Matrix.unitaryGroup (Fin n) K,
      let phi := fun i a ↦ flagAction (c i) (hermitianAngularFlagChart a)
      0 < r ∧
      (∀ a : HermitianCoordinateIndex n → K, a ∈ closedBall 0 r →
        0 < hermitianAngularDensity a) ∧
      (∀ i, Continuous (phi i)) ∧
      (∀ i, InjOn (phi i) (ball (0 : HermitianCoordinateIndex n → K) r)) ∧
      (∀ i, IsOpen (phi i '' ball (0 : HermitianCoordinateIndex n → K) r)) ∧
      (⋃ i, phi i '' ball (0 : HermitianCoordinateIndex n → K) r) = univ ∧
      (∀ i, MeasurableSet (angularChartPiece
        (ball (0 : HermitianCoordinateIndex n → K) r) phi i)) := by
  classical
  letI : BorelSpace (Matrix (Fin n) (Fin n) K) :=
    hermitianAmbientMatrixBorelSpace (Fin n) (Fin n) K
  letI : BorelSpace (Fin n → Matrix (Fin n) (Fin n) K) :=
    inferInstanceAs (BorelSpace (Fin n → Fin n → Fin n → K))
  letI : BorelSpace (flagSpace n K) := by
    unfold flagSpace
    infer_instance
  obtain ⟨r, hr, hinj, hopen, h1, hdensity⟩ := exists_hermitian_open_flag_chart n K
  obtain ⟨s, hsne, hscover⟩ := exists_finite_flag_translates_cover _ hopen h1
  have hcard : 0 < Fintype.card s := by
    rw [Fintype.card_coe]
    exact hsne.card_pos
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hcard.ne'
  have e : Fin (m + 1) ≃ s := by
    simpa only [hm] using (Fintype.equivFin s).symm
  let c : Fin (m + 1) → Matrix.unitaryGroup (Fin n) K := fun i ↦ (e i).1
  let phi := fun (i : Fin (m + 1)) a ↦ flagAction (c i) (hermitianAngularFlagChart a)
  have hcont (i : Fin (m + 1)) : Continuous (phi i) :=
    (continuous_flagAction (c i)).comp continuous_hermitianAngularFlagChart
  have hphiInj (i : Fin (m + 1)) : InjOn (phi i) (ball 0 r) := by
    intro x hx y hy hxy
    exact hinj hx hy ((flagActionHomeomorph (c i)).injective hxy)
  have hphiOpen (i : Fin (m + 1)) : IsOpen (phi i '' ball 0 r) := by
    have him : phi i '' ball 0 r =
        (flagActionHomeomorph (c i)) '' (hermitianAngularFlagChart '' ball 0 r) := by
      rw [← image_comp]
      rfl
    rw [him]
    exact (flagActionHomeomorph (c i)).isOpenMap _ hopen
  have hcover : (⋃ i, phi i '' ball (0 : HermitianCoordinateIndex n → K) r) = univ := by
    apply eq_univ_iff_forall.mpr
    intro P
    obtain ⟨U, hU, a, ha, hpsi⟩ := hscover P
    let i := e.symm ⟨U, hU⟩
    apply mem_iUnion.mpr
    refine ⟨i, a, ha, ?_⟩
    have hci : c i = U := congrArg Subtype.val (e.apply_symm_apply ⟨U, hU⟩)
    change flagAction (c i) (hermitianAngularFlagChart a) = P
    rw [hci, hpsi, ← flagAction_mul, mul_inv_cancel, flagAction_one]
  refine ⟨r, m, c, hr, hdensity, hcont, hphiInj, hphiOpen, hcover, ?_⟩
  intro i
  exact measurableSet_angularChartPiece (ball 0 r) phi isOpen_ball.measurableSet
    (fun j ↦ (hcont j).measurable) (fun j ↦ (hphiOpen j).measurableSet) i

section Volume

variable [MeasureSpace K] [BorelSpace K]
  [IsAddHaarMeasure (volume : Measure (HermitianCoordinateIndex n → K))]

def hermitianAtlasAngularMass (r : ℝ) (m : ℕ)
    (c : Fin (m + 1) → Matrix.unitaryGroup (Fin n) K) : ℝ≥0∞ :=
  ∑ i : Fin (m + 1), ∫⁻ a in angularChartPiece
    (ball (0 : HermitianCoordinateIndex n → K) r)
    (fun i a ↦ flagAction (c i) (hermitianAngularFlagChart a)) i,
      ENNReal.ofReal (hermitianAngularDensity a)

theorem hermitianAtlasAngularMass_pos_lt_top (r : ℝ) (hr : 0 < r) (m : ℕ)
    (c : Fin (m + 1) → Matrix.unitaryGroup (Fin n) K)
    (hpos : ∀ a : HermitianCoordinateIndex n → K, a ∈ closedBall 0 r →
      0 < hermitianAngularDensity a) :
    0 < hermitianAtlasAngularMass r m c ∧ hermitianAtlasAngularMass r m c < ∞ := by
  exact angular_atlas_mass_pos_lt_top volume m r hr
    (fun i a ↦ flagAction (c i) (hermitianAngularFlagChart a)) hermitianAngularDensity
    continuous_hermitianAngularDensity (fun a ha ↦ hpos a (ball_subset_closedBall ha))

def hermitianAtlasOrbitConstant (r : ℝ) (m : ℕ)
    (c : Fin (m + 1) → Matrix.unitaryGroup (Fin n) K) : NNReal :=
  (((n.factorial : ℕ) : ℝ≥0∞)⁻¹ * hermitianAtlasAngularMass r m c).toNNReal

theorem hermitianAtlasOrbitConstant_coe (r : ℝ) (hr : 0 < r) (m : ℕ)
    (c : Fin (m + 1) → Matrix.unitaryGroup (Fin n) K)
    (hpos : ∀ a : HermitianCoordinateIndex n → K, a ∈ closedBall 0 r →
      0 < hermitianAngularDensity a) :
    (hermitianAtlasOrbitConstant r m c : ℝ≥0∞) =
      ((n.factorial : ℕ) : ℝ≥0∞)⁻¹ * hermitianAtlasAngularMass r m c := by
  apply ENNReal.coe_toNNReal
  apply ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr ?_)
    (hermitianAtlasAngularMass_pos_lt_top r hr m c hpos).2 |>.ne
  exact_mod_cast n.factorial_pos

theorem hermitianAtlasOrbitConstant_pos (r : ℝ) (hr : 0 < r) (m : ℕ)
    (c : Fin (m + 1) → Matrix.unitaryGroup (Fin n) K)
    (hpos : ∀ a : HermitianCoordinateIndex n → K, a ∈ closedBall 0 r →
      0 < hermitianAngularDensity a) :
    0 < hermitianAtlasOrbitConstant r m c := by
  apply ENNReal.toNNReal_pos_iff.mpr
  constructor
  · exact ENNReal.mul_pos (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _)).ne'
      (hermitianAtlasAngularMass_pos_lt_top r hr m c hpos).1.ne'
  · exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (by
      exact_mod_cast n.factorial_pos))
      (hermitianAtlasAngularMass_pos_lt_top r hr m c hpos).2

end Volume

end A3Research

import A3.Shared.OrbitMeasureCompactAtlas
import A3.Shared.CompactDeterminant

open MeasureTheory Set Function TopologicalSpace Metric
open scoped BigOperators

noncomputable section

namespace A3Research

set_option maxHeartbeats 600000

/-- A bounded open group chart on a compact group gives an actual finite
translated atlas. Its sources are all the same bounded coordinate set. -/
theorem exists_finite_translated_atlas
    {E G : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (b : Set E) (hb : IsOpen b) (ψ : E → G) (hψ : Continuous ψ)
    (hinj : InjOn ψ b) (hopen : IsOpen (ψ '' b)) (h1 : 1 ∈ ψ '' b) :
    ∃ n : ℕ, ∃ c : Fin (n + 1) → G,
      let φ : Fin (n + 1) → E → G := fun i x ↦ c i * ψ x
      (∀ i, Continuous (φ i)) ∧
      (∀ i, InjOn (φ i) b) ∧
      (∀ i, IsOpen (φ i '' b)) ∧
      (⋃ i, φ i '' b) = univ ∧
      (∀ i, MeasurableSet (angularChartPiece b φ i)) := by
  classical
  obtain ⟨s, hsne, hscover⟩ := exists_finite_left_translates_cover (ψ '' b) hopen h1
  have hcard : 0 < Fintype.card s := by
    rw [Fintype.card_coe]
    exact hsne.card_pos
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hcard.ne'
  have e : Fin (n + 1) ≃ s := by
    simpa only [hn] using (Fintype.equivFin s).symm
  let c : Fin (n + 1) → G := fun i ↦ (e i).1
  let φ : Fin (n + 1) → E → G := fun i x ↦ c i * ψ x
  have hcont (i : Fin (n + 1)) : Continuous (φ i) := by
    exact continuous_const.mul hψ
  have hφinj (i : Fin (n + 1)) : InjOn (φ i) b := by
    intro x hx y hy hxy
    exact hinj hx hy (mul_left_cancel hxy)
  have hφopen (i : Fin (n + 1)) : IsOpen (φ i '' b) := by
    have him : φ i '' b = (fun g : G ↦ c i * g) '' (ψ '' b) := by
      rw [← image_comp]
      rfl
    rw [him]
    exact (Homeomorph.mulLeft (c i)).isOpenMap _ hopen
  have hcover : (⋃ i, φ i '' b) = univ := by
    apply eq_univ_iff_forall.mpr
    intro g
    obtain ⟨a, ha, x, hx, hψx⟩ := hscover g
    let i := e.symm ⟨a, ha⟩
    apply mem_iUnion.mpr
    refine ⟨i, x, hx, ?_⟩
    have hci : c i = a := congrArg Subtype.val (e.apply_symm_apply ⟨a, ha⟩)
    change c i * ψ x = g
    rw [hci, hψx, mul_inv_cancel_left]
  refine ⟨n, c, hcont, hφinj, hφopen, hcover, ?_⟩
  intro i
  exact measurableSet_angularChartPiece b φ hb.measurableSet
    (fun j ↦ (hcont j).measurable) (fun j ↦ (hφopen j).measurableSet) i

end A3Research

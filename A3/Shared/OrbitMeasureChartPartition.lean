import A3.Shared.WeylIntegrationFiniteCover

open MeasureTheory Set Function
open scoped BigOperators ENNReal

noncomputable section

namespace A3Research

set_option maxHeartbeats 600000

/-- The angular source portion assigned to a chart after its target images
have been disjointified in their fixed finite order. -/
def angularChartPiece {I E G : Type*} [LinearOrder I] [LocallyFiniteOrderBot I]
    (b : Set E) (φ : I → E → G) (i : I) : Set E :=
  b ∩ (φ i) ⁻¹' disjointed (fun j ↦ φ j '' b) i

theorem angularChartPiece_subset {I E G : Type*}
    [LinearOrder I] [LocallyFiniteOrderBot I]
    (b : Set E) (φ : I → E → G) (i : I) : angularChartPiece b φ i ⊆ b :=
  inter_subset_left

theorem image_angularChartPiece {I E G : Type*}
    [LinearOrder I] [LocallyFiniteOrderBot I]
    (b : Set E) (φ : I → E → G) (i : I) :
    φ i '' angularChartPiece b φ i = disjointed (fun j ↦ φ j '' b) i := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  · intro y hy
    obtain ⟨x, hx, hφx⟩ := disjointed_subset (fun j ↦ φ j '' b) i hy
    refine ⟨x, ⟨hx, ?_⟩, hφx⟩
    change φ i x ∈ disjointed (fun j ↦ φ j '' b) i
    rwa [hφx]

theorem measurableSet_angularChartPiece {I E G : Type*}
    [LinearOrder I] [LocallyFiniteOrderBot I] [Countable I]
    [MeasurableSpace E] [MeasurableSpace G]
    (b : Set E) (φ : I → E → G) (hb : MeasurableSet b)
    (hφ : ∀ i, Measurable (φ i)) (himage : ∀ i, MeasurableSet (φ i '' b)) (i : I) :
    MeasurableSet (angularChartPiece b φ i) := by
  apply hb.inter
  apply MeasurableSet.preimage _ (hφ i)
  rw [disjointed_eq_inter_compl]
  exact (himage i).inter (MeasurableSet.iInter fun j ↦
    MeasurableSet.iInter fun _ ↦ (himage j).compl)

@[simp] theorem angularChartPiece_bot {I E G : Type*}
    [LinearOrder I] [LocallyFiniteOrderBot I] [OrderBot I]
    (b : Set E) (φ : I → E → G) : angularChartPiece b φ ⊥ = b := by
  unfold angularChartPiece
  rw [disjointed_bot]
  apply inter_eq_left.mpr
  intro x hx
  exact mem_image_of_mem _ hx

/-- The disjoint angular atlas represents every group element exactly once.
This is an equivalence of actual source fibers, not just a cardinal estimate. -/
def angularChartFiberEquiv {I E G : Type*}
    [LinearOrder I] [LocallyFiniteOrderBot I]
    (b : Set E) (φ : I → E → G)
    (hφ : ∀ i, InjOn (φ i) b) (hcover : (⋃ i, φ i '' b) = univ) (y : G) :
    chartFiber (angularChartPiece b φ) φ y ≃ Fin 1 := by
  classical
  refine Equiv.ofBijective (fun _ ↦ 0) ⟨?_, ?_⟩
  · rintro ⟨i, x⟩ ⟨j, z⟩ _
    have hij : i = j := by
      by_contra hij
      have hxi : y ∈ disjointed (fun i ↦ φ i '' b) i := by
        rw [← x.2.2]
        exact x.2.1.2
      have hzj : y ∈ disjointed (fun i ↦ φ i '' b) j := by
        rw [← z.2.2]
        exact z.2.1.2
      exact Set.disjoint_left.mp (disjoint_disjointed (fun i ↦ φ i '' b) hij)
        hxi hzj
    subst j
    have hxz : x = z := Subtype.ext (hφ i x.2.1.1 z.2.1.1 (x.2.2.trans z.2.2.symm))
    subst z
    rfl
  · intro t
    have hy : y ∈ ⋃ i, disjointed (fun i ↦ φ i '' b) i := by
      rw [iUnion_disjointed, hcover]
      trivial
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    rw [← image_angularChartPiece b φ i] at hi
    obtain ⟨x, hx, hφx⟩ := hi
    exact ⟨⟨i, ⟨x, hx, hφx⟩⟩, Subsingleton.elim _ _⟩

/-- Replacing each orbit representative by its unique angular chart
coordinates preserves the full radial orbit fiber exactly. -/
def angularRadialChartFiberEquiv {I E G R Y : Type*}
    [LinearOrder I] [LocallyFiniteOrderBot I]
    (b : Set E) (φ : I → E → G)
    (hφ : ∀ i, InjOn (φ i) b) (hcover : (⋃ i, φ i '' b) = univ)
    (p : Set R) (T : G × R → Y) (y : Y) :
    chartFiber (fun i ↦ angularChartPiece b φ i ×ˢ p)
      (fun i z ↦ T (φ i z.1, z.2)) y ≃
      {z : G × R // z.2 ∈ p ∧ T z = y} := by
  classical
  refine Equiv.ofBijective
    (fun a ↦ ⟨(φ a.1 a.2.1.1, a.2.1.2), a.2.2.1.2, a.2.2.2⟩) ⟨?_, ?_⟩
  · rintro ⟨i, x⟩ ⟨j, z⟩ h
    have hrad : x.1.2 = z.1.2 := congrArg (fun a ↦ a.1.2) h
    have hang : φ i x.1.1 = φ j z.1.1 := congrArg (fun a ↦ a.1.1) h
    let a : chartFiber (angularChartPiece b φ) φ (φ i x.1.1) :=
      ⟨i, ⟨x.1.1, x.2.1.1, rfl⟩⟩
    let c : chartFiber (angularChartPiece b φ) φ (φ i x.1.1) :=
      ⟨j, ⟨z.1.1, z.2.1.1, hang.symm⟩⟩
    have hac : a = c := (angularChartFiberEquiv b φ hφ hcover _).injective
      (Subsingleton.elim _ _)
    have hij : i = j := congrArg Sigma.fst hac
    have hxz : x.1.1 = z.1.1 := congrArg (fun a : chartFiber (angularChartPiece b φ) φ
      (φ i x.1.1) ↦ a.2.1) hac
    subst j
    have hsubxz : x = z := Subtype.ext (Prod.ext hxz hrad)
    subst z
    rfl
  · intro z
    let a := (angularChartFiberEquiv b φ hφ hcover z.1.1).symm 0
    exact ⟨⟨a.1, ⟨(a.2.1, z.1.2), ⟨a.2.2.1, z.2.1⟩,
      by simpa only [a.2.2.2] using z.2.2⟩⟩,
      Subtype.ext (Prod.ext a.2.2.2 rfl)⟩

end A3Research

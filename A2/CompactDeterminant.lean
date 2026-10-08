import A2.Definitions

open MeasureTheory Matrix Set

noncomputable section

namespace A2Research

/-- A continuous real multiplicative character of a compact group has absolute
value one. This also applies to determinants of finite-dimensional representations. -/
theorem abs_eq_one_compact_character {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] (χ : G →* ℝ) (hχ : Continuous χ) (g : G) : |χ g| = 1 := by
  have hb : BddAbove (Set.range fun x : G ↦ |χ x|) := by
    simpa only [Set.image_univ] using (isCompact_univ.image hχ.abs).bddAbove
  obtain ⟨b, hbound⟩ := hb
  have hle (x : G) : |χ x| ≤ 1 := by
    by_contra hx
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt b (lt_of_not_ge hx)
    have hbn : |χ x| ^ n ≤ b := by
      simpa only [map_pow, abs_pow] using hbound (Set.mem_range_self (x ^ n))
    exact not_lt_of_ge hbn hn
  have hmul : |χ g| * |χ g⁻¹| = 1 := by
    rw [← abs_mul, ← map_mul, mul_inv_cancel, map_one, abs_one]
  apply le_antisymm (hle g)
  calc
    1 = |χ g| * |χ g⁻¹| := hmul.symm
    _ ≤ |χ g| * 1 := mul_le_mul_of_nonneg_left (hle g⁻¹) (abs_nonneg _)
    _ = |χ g| := mul_one _

theorem unitaryGroup_isCompact (N : ℕ) :
    IsCompact (Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) := by
  let D : Set ℂ := Metric.closedBall 0 1
  have hbox : IsCompact (D.matrix : Set (Matrix (Fin N) (Fin N) ℂ)) :=
    (isCompact_closedBall (0 : ℂ) 1).matrix
  refine hbox.of_isClosed_subset ?_ ?_
  · simpa only using isClosed_unitary (R := Matrix (Fin N) (Fin N) ℂ)
  · intro A hA
    rw [Set.mem_matrix]
    intro i j
    simpa [D, Metric.mem_closedBall, dist_zero_right] using
      entry_norm_bound_of_unitary hA i j

instance unitaryGroup_compactSpace (N : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin N) ℂ) :=
  isCompact_iff_compactSpace.mp (unitaryGroup_isCompact N)

end A2Research

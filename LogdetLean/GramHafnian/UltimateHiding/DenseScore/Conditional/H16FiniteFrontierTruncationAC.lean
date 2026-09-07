import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16TimeSupportFiniteFrontier

/-!
# Absolute continuity after truncation by an open set with finite frontier

This is the topological gluing lemma needed by the literal H16 zero
extension.  A locally absolutely continuous scalar function which vanishes
on the frontier of an open set remains absolutely continuous after it is set
to zero off that open set, provided the frontier is finite on the interval.

The proof first establishes concatenation of absolute continuity at one
intermediate point, then inducts on a finite cover of the interior frontier.
-/

open Filter MeasureTheory Set
open scoped Interval Topology ContDiff

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

private theorem absolutelyContinuousOnInterval_congr_of_eqOn_h16
    {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hfg : Set.EqOn f g [[a, b]]) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hf ε hε
  refine ⟨δ, hδ, ?_⟩
  intro E hE hlength
  have hresult := hbound E hE hlength
  convert hresult using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hfg (hE.1 i hi).1, hfg (hE.1 i hi).2]

private theorem absolutelyContinuousOnInterval_trans_of_le_h16
    {f : ℝ → ℝ} {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hleft : AbsolutelyContinuousOnInterval f a c)
    (hright : AbsolutelyContinuousOnInterval f c b) :
    AbsolutelyContinuousOnInterval f a b := by
  have hderiv : IntervalIntegrable (deriv f) volume a b :=
    hleft.intervalIntegrable_deriv.trans hright.intervalIntegrable_deriv
  have hprimitive : AbsolutelyContinuousOnInterval
      (fun x ↦ ∫ t in a..x, deriv f t) a b :=
    hderiv.absolutelyContinuousOnInterval_intervalIntegral (by simp [hac, hcb])
  have hconst : AbsolutelyContinuousOnInterval (fun _x : ℝ ↦ f a) a b :=
    contDiff_const.contDiffOn.absolutelyContinuousOnInterval
  apply absolutelyContinuousOnInterval_congr_of_eqOn_h16 (hconst.add hprimitive)
  intro x hx
  simp only [Pi.add_apply]
  have hxab : a ≤ x ∧ x ≤ b := by
    simpa only [uIcc_of_le (hac.trans hcb), mem_Icc] using hx
  have hax : (∫ t in a..x, deriv f t) = f x - f a := by
    rcases le_total x c with hxc | hcx
    · have haxAC : AbsolutelyContinuousOnInterval f a x := by
        apply hleft.mono
        intro y hy
        simp only [uIcc_of_le hxab.1, uIcc_of_le hac, mem_Icc] at hy ⊢
        exact ⟨hy.1, hy.2.trans hxc⟩
      exact haxAC.integral_deriv_eq_sub
    · have hcxAC : AbsolutelyContinuousOnInterval f c x := by
        apply hright.mono
        intro y hy
        simp only [uIcc_of_le hcx, uIcc_of_le hcb, mem_Icc] at hy ⊢
        exact ⟨hy.1, hy.2.trans hxab.2⟩
      rw [← intervalIntegral.integral_add_adjacent_intervals
        hleft.intervalIntegrable_deriv hcxAC.intervalIntegrable_deriv,
        hleft.integral_deriv_eq_sub, hcxAC.integral_deriv_eq_sub]
      ring
  rw [hax]
  ring

/-- Absolute continuity concatenates across an intermediate point lying in
the unoriented interval. -/
theorem absolutelyContinuousOnInterval_trans_h16
    {f : ℝ → ℝ} {a c b : ℝ} (hc : c ∈ [[a, b]])
    (hleft : AbsolutelyContinuousOnInterval f a c)
    (hright : AbsolutelyContinuousOnInterval f c b) :
    AbsolutelyContinuousOnInterval f a b := by
  rcases le_total a b with hab | hba
  · have hac : a ≤ c := by
      have hc' : c ∈ Icc a b := by simpa only [uIcc_of_le hab] using hc
      exact hc'.1
    have hcb : c ≤ b := by
      have hc' : c ∈ Icc a b := by simpa only [uIcc_of_le hab] using hc
      exact hc'.2
    exact absolutelyContinuousOnInterval_trans_of_le_h16
      hac hcb hleft hright
  · have hbc : b ≤ c := by
      have hc' : c ∈ Icc b a := by simpa only [uIcc_of_ge hba] using hc
      exact hc'.1
    have hca : c ≤ a := by
      have hc' : c ∈ Icc b a := by simpa only [uIcc_of_ge hba] using hc
      exact hc'.2
    exact (absolutelyContinuousOnInterval_trans_of_le_h16
      hbc hca hright.symm hleft.symm).symm

/-- Zero extension of `F` away from `U`, packaged as a noncomputable
definition so subsequent theorems do not carry decidability parameters. -/
noncomputable def h16OpenTrunc (U : Set ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  U.indicator F x

/-- Setting a locally absolutely continuous function to zero off an open set
preserves absolute continuity when a finite set covers all frontier points in
the interval interior and the function vanishes on that frontier. -/
theorem absolutelyContinuousOnInterval_ite_mem_of_finite_frontier_cover
    {F : ℝ → ℝ} {U C : Set ℝ} {a b : ℝ}
    (hU : IsOpen U)
    (hF : ∀ c d : ℝ, AbsolutelyContinuousOnInterval F c d)
    (hFzero : ∀ x ∈ frontier U, F x = 0)
    (hC : C.Finite)
    (hcover : ∀ x ∈ uIoo a b, x ∈ frontier U → x ∈ C) :
    AbsolutelyContinuousOnInterval
      (h16OpenTrunc U F) a b := by
  induction C, hC using Set.Finite.induction_on generalizing a b with
  | empty =>
      classical
      by_cases hab : a = b
      · subst b
        apply absolutelyContinuousOnInterval_congr_of_eqOn_h16
          (contDiff_const.contDiffOn.absolutelyContinuousOnInterval :
            AbsolutelyContinuousOnInterval
              (fun _x : ℝ ↦ if a ∈ U then F a else 0) a a)
        intro x hx
        simp only [uIcc_self, mem_singleton_iff] at hx
        subst x
        by_cases haU : a ∈ U <;> simp [h16OpenTrunc, haU]
      · let J : Set ℝ := uIoo a b
        have hJclosure : closure J = [[a, b]] := by
          simpa only [J] using closure_uIoo hab
        have hno : ∀ x ∈ J, x ∉ frontier U := by
          intro x hxJ hxfrontier
          have : x ∈ (∅ : Set ℝ) := hcover x (by simpa only [J] using hxJ) hxfrontier
          simpa using this
        have hsplit : J ⊆ U ∪ (closure U)ᶜ := by
          intro x hxJ
          by_cases hxU : x ∈ U
          · exact Or.inl hxU
          · right
            intro hxclosure
            apply hno x hxJ
            exact ⟨hxclosure, by simpa [hU.interior_eq] using hxU⟩
        by_cases hJU : (J ∩ U).Nonempty
        · have hJsub : J ⊆ U :=
            isPreconnected_uIoo.subset_left_of_subset_union
              hU isClosed_closure.isOpen_compl
              (disjoint_compl_right.mono_right
                (compl_subset_compl.mpr subset_closure))
              hsplit hJU
          apply absolutelyContinuousOnInterval_congr_of_eqOn_h16 (hF a b)
          intro x hx
          by_cases hxU : x ∈ U
          · simp [h16OpenTrunc, hxU]
          · have hxJclosure : x ∈ closure J := by
              rw [hJclosure]
              exact hx
            have hxclosureU : x ∈ closure U :=
              closure_mono hJsub hxJclosure
            have hxfrontier : x ∈ frontier U :=
              ⟨hxclosureU, by simpa [hU.interior_eq] using hxU⟩
            simp [h16OpenTrunc, hxU, hFzero x hxfrontier]
        · have hJdisj : ∀ x ∈ J, x ∉ U := by
            intro x hxJ hxU
            exact hJU ⟨x, hxJ, hxU⟩
          apply absolutelyContinuousOnInterval_congr_of_eqOn_h16
            (contDiff_const.contDiffOn.absolutelyContinuousOnInterval :
              AbsolutelyContinuousOnInterval (fun _x : ℝ ↦ (0 : ℝ)) a b)
          intro x hx
          have hxJclosure : x ∈ closure J := by
            rw [hJclosure]
            exact hx
          have hxnotU : x ∉ U := by
            intro hxU
            have hnonempty : (U ∩ J).Nonempty :=
              (mem_closure_iff.mp hxJclosure) U hU hxU
            obtain ⟨y, hyU, hyJ⟩ := hnonempty
            exact hJdisj y hyJ hyU
          simp [h16OpenTrunc, hxnotU]
  | @insert c C hcC hC ih =>
      by_cases hc : c ∈ uIoo a b
      · have hleft := ih (a := a) (b := c) (fun x hx hxfrontier ↦ by
          have hxmain : x ∈ uIoo a b := by
            simp only [uIoo, mem_Ioo] at hc hx ⊢
            grind
          have hxinsert := hcover x hxmain hxfrontier
          simp only [mem_insert_iff] at hxinsert
          rcases hxinsert with hxc | hxC
          · subst x
            simp only [uIoo, mem_Ioo] at hx
            grind
          · exact hxC)
        have hright := ih (a := c) (b := b) (fun x hx hxfrontier ↦ by
          have hxmain : x ∈ uIoo a b := by
            simp only [uIoo, mem_Ioo] at hc hx ⊢
            grind
          have hxinsert := hcover x hxmain hxfrontier
          simp only [mem_insert_iff] at hxinsert
          rcases hxinsert with hxc | hxC
          · subst x
            simp only [uIoo, mem_Ioo] at hx
            grind
          · exact hxC)
        exact absolutelyContinuousOnInterval_trans_h16
          (by
            simp only [uIoo, uIcc, mem_Ioo, mem_Icc] at hc ⊢
            grind)
          hleft hright
      · apply ih (a := a) (b := b)
        intro x hx hxfrontier
        have hxinsert := hcover x hx hxfrontier
        simp only [mem_insert_iff] at hxinsert
        rcases hxinsert with hxc | hxC
        · subst x
          exact (hc hx).elim
        · exact hxC

/-- Convenient finite-frontier specialization of the preceding cover lemma. -/
theorem absolutelyContinuousOnInterval_ite_mem_of_finite_frontier
    {F : ℝ → ℝ} {U : Set ℝ} {a b : ℝ}
    (hU : IsOpen U)
    (hF : ∀ c d : ℝ, AbsolutelyContinuousOnInterval F c d)
    (hFzero : ∀ x ∈ frontier U, F x = 0)
    (hfrontier : ({x : ℝ | x ∈ [[a, b]] ∧ x ∈ frontier U}).Finite) :
    AbsolutelyContinuousOnInterval
      (h16OpenTrunc U F) a b := by
  apply absolutelyContinuousOnInterval_ite_mem_of_finite_frontier_cover
    hU hF hFzero hfrontier
  intro x hx hxfrontier
  exact ⟨by
    simp only [uIoo, uIcc, mem_Ioo, mem_Icc] at hx ⊢
    grind, hxfrontier⟩

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

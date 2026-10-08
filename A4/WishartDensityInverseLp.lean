import A4.WishartDensityInverseIntegrability

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal NNReal

noncomputable section
namespace A4Research

open MatsumotoPaper

/-- A strict inverse moment margin leaves room above any requested positive
finite L^p exponent. -/
theorem exists_inverseLpHolderExponent {d n : ℕ} {beta gamma p : ℝ}
    (hn : 0 < n)
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2)
    (hgap : (n : ℝ) * p - 1 < gamma) :
    ∃ r : ℝ, p < r ∧ ∀ i : Fin d, 0 < bartlettShape beta i - (n : ℝ) * r := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let r : ℝ := (gamma + 1 + (n : ℝ) * p) / (2 * (n : ℝ))
  have hmul : (n : ℝ) * r = (gamma + 1 + (n : ℝ) * p) / 2 := by
    dsimp [r]
    field_simp
  refine ⟨r, ?_, ?_⟩
  · apply (lt_div_iff₀ (mul_pos (by norm_num) hnR)).mpr
    linarith
  · intro i
    have hi : (i : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast i.isLt
    rw [hmul]
    unfold bartlettShape
    linarith

/-- Every inverse entry product has all finite L^p norms up to its exact
real-shape threshold. This includes the L^2 input for Gaussian Stein--Haff. -/
theorem _root_.MatsumotoPaper.W_d.memLp_prod_inverse_entries
    {d n : ℕ} {beta gamma p : ℝ} {sigma : SymPosDef d} (W : W_d d beta sigma)
    (hp : 0 < p) (hgamma : gamma = beta - ((d : ℝ) + 1) / 2)
    (hgap : (n : ℝ) * p - 1 < gamma) (i j : Fin n → Fin d) :
    MemLp (fun w : SymPosDef d => ∏ k : Fin n, w.1⁻¹ (i k) (j k))
      (ENNReal.ofReal p) W.toMeasure := by
  let := W.probability
  by_cases hn0 : n = 0
  · subst n
    simp only [Fin.prod_univ_zero]
    exact memLp_const (1 : ℝ)
  obtain ⟨r, hpr, hshape⟩ := exists_inverseLpHolderExponent
    (Nat.pos_of_ne_zero hn0) hgamma hgap
  have hb : ((d : ℝ) - 1) / 2 < beta := by
    have hn := mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hp.le
    linarith
  have hr : 0 < r := hp.trans hpr
  have hdet := wishart_memLp_det_inverse_degree W hb hr hshape
  let q : ℝ := p * r / (r - p)
  have hq : 0 < q := div_pos (mul_pos hp hr) (sub_pos.mpr hpr)
  have htriple : Real.HolderTriple r q p := by
    refine ⟨?_, hr, hq⟩
    dsimp only [q]
    field_simp [hp.ne', hr.ne', (sub_pos.mpr hpr).ne']
    ring
  let qNN : ℝ≥0 := ⟨q, hq.le⟩
  have hqcoe : ENNReal.ofReal q = (qNN : ℝ≥0∞) := ENNReal.ofReal_eq_coe_nnreal hq.le
  have hadj : MemLp (fun w : SymPosDef d => ∏ k : Fin n, w.1.adjugate (i k) (j k))
      (ENNReal.ofReal q) W.toMeasure := by
    rw [hqcoe]
    exact W.memLp_prod_adjugate_entries i j qNN
  let : ENNReal.HolderTriple (ENNReal.ofReal r) (ENNReal.ofReal q) (ENNReal.ofReal p) :=
    htriple.ennrealOfReal
  have hprod : MemLp (fun w : SymPosDef d =>
      Matrix.det w.1 ^ (-(n : ℝ)) * ∏ k : Fin n, w.1.adjugate (i k) (j k))
      (ENNReal.ofReal p) W.toMeasure := hadj.mul' hdet
  exact (memLp_congr_ae (Filter.Eventually.of_forall fun w =>
    (inverse_prod_entries_eq_det_adjugate w i j).symm)).mp hprod

end A4Research

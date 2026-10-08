import A4.WishartDensityRecursiveMoments
import A4.PolynomialIntegrability
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Data.Real.ConjExponents

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal NNReal

noncomputable section
namespace A4Research

open MatsumotoPaper

local instance (d : ℕ) : BorelSpace (RealMatrix d) := ⟨rfl⟩

/-- The full A4 gap leaves room for a genuine Hölder exponent above one. -/
theorem exists_inverseHolderExponent {d n : ℕ} {beta gamma : ℝ}
    (hn : 0 < n) (hgamma : gamma = beta - ((d : ℝ) + 1) / 2)
    (hgap : (n : ℝ) - 1 < gamma) :
    ∃ p : ℝ, 1 < p ∧ ∀ i : Fin d, 0 < bartlettShape beta i - (n : ℝ) * p := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let p : ℝ := (gamma + 1 + (n : ℝ)) / (2 * (n : ℝ))
  have hmul : (n : ℝ) * p = (gamma + 1 + (n : ℝ)) / 2 := by
    dsimp [p]
    field_simp
  refine ⟨p, ?_, ?_⟩
  · apply (lt_div_iff₀ (mul_pos (by norm_num) hnR)).mpr
    linarith
  · intro i
    have hi : (i : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast i.isLt
    rw [hmul]
    unfold bartlettShape
    linarith

/-- The inverse determinant has every finite L^p norm allowed by its exact
Gamma-shape margin, for the actual characterized Wishart law. -/
theorem wishart_memLp_det_inverse_degree {d n : ℕ} {beta p : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma)
    (hb : ((d : ℝ) - 1) / 2 < beta) (hp : 0 < p)
    (hshape : ∀ i : Fin d, 0 < bartlettShape beta i - (n : ℝ) * p) :
    MemLp (fun w : SymPosDef d => Matrix.det w.1 ^ (-(n : ℝ)))
      (ENNReal.ofReal p) W.toMeasure := by
  have hm : Measurable (fun w : SymPosDef d => Matrix.det w.1 ^ (-(n : ℝ))) := by
    exact ((continuous_id.matrix_det : Continuous (Matrix.det : RealMatrix d → ℝ)).measurable.comp
      measurable_subtype_coe).pow_const _
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  apply (memLp_norm_rpow_iff (p := ENNReal.ofReal p) (q := ENNReal.ofReal p)
    hm.aestronglyMeasurable hp0 ENNReal.ofReal_ne_top).mp
  rw [ENNReal.div_self hp0 ENNReal.ofReal_ne_top]
  apply memLp_one_iff_integrable.mpr
  have hdet := wishart_integrable_det_rpow (p := -(n : ℝ) * p) W hb
    (fun i => by simpa only [sub_eq_add_neg, neg_mul] using hshape i)
  apply hdet.congr
  filter_upwards [] with w
  rw [Real.norm_of_nonneg (Real.rpow_pos_of_pos w.2.det_pos _).le,
    ENNReal.toReal_ofReal hp.le, ← Real.rpow_mul w.2.det_pos.le]

/-- The exact adjugate/determinant identity for arbitrary inverse-entry
products. This retains every index and the complete degree. -/
theorem inverse_prod_entries_eq_det_adjugate {d n : ℕ} (w : SymPosDef d)
    (i j : Fin n → Fin d) :
    (∏ k : Fin n, w.1⁻¹ (i k) (j k)) =
      Matrix.det w.1 ^ (-(n : ℝ)) * ∏ k : Fin n, w.1.adjugate (i k) (j k) := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast, inv_pow]

/-- Every degree-n inverse-entry product is integrable under the exact
real-shape A4 condition. Hölder uses the strict determinant shape margin. -/
theorem _root_.MatsumotoPaper.W_d.integrable_prod_inverse_entries
    {d n : ℕ} {beta gamma : ℝ} {sigma : SymPosDef d} (W : W_d d beta sigma)
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (n : ℝ) - 1 < gamma)
    (i j : Fin n → Fin d) :
    Integrable (fun w : SymPosDef d => ∏ k : Fin n, w.1⁻¹ (i k) (j k)) W.toMeasure := by
  let := W.probability
  by_cases hn0 : n = 0
  · subst n
    simp only [Fin.prod_univ_zero]
    exact integrable_const (1 : ℝ)
  obtain ⟨p, hp, hshape⟩ := exists_inverseHolderExponent (Nat.pos_of_ne_zero hn0) hgamma hgap
  have hb : ((d : ℝ) - 1) / 2 < beta := by
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hdet := wishart_memLp_det_inverse_degree W hb (by linarith : 0 < p) hshape
  let q : ℝ := Real.conjExponent p
  have hconj : Real.HolderConjugate p q := Real.HolderConjugate.conjExponent hp
  have hq : 0 < q := hconj.right_pos
  let qNN : ℝ≥0 := ⟨q, hq.le⟩
  have hqcoe : ENNReal.ofReal q = (qNN : ℝ≥0∞) := ENNReal.ofReal_eq_coe_nnreal hq.le
  have hadj : MemLp (fun w : SymPosDef d => ∏ k : Fin n, w.1.adjugate (i k) (j k))
      (ENNReal.ofReal q) W.toMeasure := by
    rw [hqcoe]
    exact W.memLp_prod_adjugate_entries i j qNN
  let : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) 1 := hconj.ennrealOfReal
  have hprod : Integrable (fun w : SymPosDef d =>
      Matrix.det w.1 ^ (-(n : ℝ)) * ∏ k : Fin n, w.1.adjugate (i k) (j k)) W.toMeasure :=
    memLp_one_iff_integrable.mp (hadj.mul' hdet)
  exact hprod.congr (Filter.Eventually.of_forall fun w =>
    (inverse_prod_entries_eq_det_adjugate w i j).symm)

/-- The complex embedding of every inverse-entry monomial is integrable. -/
theorem _root_.MatsumotoPaper.W_d.integrable_prod_complex_inverse_entries
    {d n : ℕ} {beta gamma : ℝ} {sigma : SymPosDef d} (W : W_d d beta sigma)
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (n : ℝ) - 1 < gamma)
    (i j : Fin n → Fin d) :
    Integrable (fun w : SymPosDef d => ∏ k : Fin n, (w.1⁻¹ (i k) (j k) : ℂ)) W.toMeasure := by
  apply ((W.integrable_prod_inverse_entries hgamma hgap i j).ofReal (𝕜 := ℂ)).congr
  filter_upwards [] with w
  push_cast
  rfl

/-- The entire inverse contraction in the original A4 target is integrable,
for arbitrary complex test matrices and permutation. -/
theorem _root_.MatsumotoPaper.W_d.integrable_inverse_T
    {d n : ℕ} {beta gamma : ℝ} {sigma : SymPosDef d} (W : W_d d beta sigma)
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (n : ℝ) - 1 < gamma)
    (g : Equiv.Perm (Fin (2 * n))) (m : Fin n → ComplexMatrix d) :
    Integrable (fun w : SymPosDef d => T g w.1⁻¹ m) W.toMeasure := by
  unfold T
  apply integrable_finsetSum
  intro j _
  exact (W.integrable_prod_complex_inverse_entries hgamma hgap
    (fun i => j (g (leftSlot i))) (fun i => j (g (rightSlot i)))).const_mul _

/-- The inverse expectation is exactly the finite contraction of its real
entry-moment tensor, with every distribution step justified. -/
theorem _root_.MatsumotoPaper.W_d.expectation_inverse_T_eq_entryMoments
    {d n : ℕ} {beta gamma : ℝ} {sigma : SymPosDef d} (W : W_d d beta sigma)
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (n : ℝ) - 1 < gamma)
    (g : Equiv.Perm (Fin (2 * n))) (m : Fin n → ComplexMatrix d) :
    expectation W (fun w => T g w.1⁻¹ m) =
      ∑ j : Fin (2 * n) → Fin d,
        (∏ i : Fin n, m i (j (leftSlot i)) (j (rightSlot i))) *
          Complex.ofReal (∫ w, ∏ i : Fin n,
            w.1⁻¹ (j (g (leftSlot i))) (j (g (rightSlot i))) ∂W.toMeasure) := by
  unfold expectation T
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul]
    congr 1
    calc
      _ = ∫ w, Complex.ofReal (∏ i : Fin n,
          w.1⁻¹ (j (g (leftSlot i))) (j (g (rightSlot i)))) ∂W.toMeasure := by
        apply integral_congr_ae
        filter_upwards [] with w
        push_cast
        rfl
      _ = _ := integral_complex_ofReal
  · intro j _
    exact (W.integrable_prod_complex_inverse_entries hgamma hgap
      (fun i => j (g (leftSlot i))) (fun i => j (g (rightSlot i)))).const_mul _

end A4Research

import A4.DirectMomentsAnalytic
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

open MeasureTheory Matrix
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace A4Research

/-- Finite products preserve membership in every finite `L^p` space.
The exponents in the finite-product Hölder theorem are chosen explicitly. -/
theorem memLp_fintypeProd_of_all_finite {Ω I : Type*} [MeasurableSpace Ω]
    [Fintype I] {μ : Measure Ω} [IsFiniteMeasure μ]
    (f : I → Ω → ℝ) (hf : ∀ i (p : ℝ≥0), MemLp (f i) p μ) (p : ℝ≥0) :
    MemLp (fun w ↦ ∏ i : I, f i w) p μ := by
  classical
  by_cases hcard : Fintype.card I = 0
  · haveI : IsEmpty I := Fintype.card_eq_zero_iff.mp hcard
    simpa using (memLp_const (μ := μ) (p := (p : ℝ≥0∞)) (1 : ℝ))
  let c : ℝ≥0 := Fintype.card I
  let q : ℝ≥0 := c * p
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    dsimp only [c]
    exact_mod_cast hcard
  have hctop : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hsum : (∑ _ : I, ((q : ℝ≥0∞)⁻¹))⁻¹ = (p : ℝ≥0∞) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change ((c : ℝ≥0∞) * ((q : ℝ≥0∞)⁻¹))⁻¹ = (p : ℝ≥0∞)
    simp only [q, ENNReal.coe_mul]
    rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop),
      inv_inv, ENNReal.inv_mul_cancel_left hc0 hctop]
  have hprod := MemLp.prod' (s := Finset.univ) (p := fun _ : I ↦ (q : ℝ≥0∞))
    (fun i _ ↦ hf i q)
  simpa only [hsum] using hprod

end A4Research

namespace MatsumotoPaper

theorem W_d.memLp_entry {d : ℕ} {beta : ℝ} {sigma : SymPosDef d}
    (W : W_d d beta sigma) (i j : Fin d) (p : ℝ≥0) :
    MemLp (fun w ↦ w.1 i j) p W.toMeasure := by
  exact (memLp_congr_ae
    (Filter.Eventually.of_forall (traceObservable_entryTraceDirection i j))).mp
      (W.memLp_traceObservable (entryTraceDirection i j) p)

theorem W_d.memLp_prod_entries {d : ℕ} {beta : ℝ} {sigma : SymPosDef d}
    (W : W_d d beta sigma) {I : Type*} [Fintype I]
    (i j : I → Fin d) (p : ℝ≥0) :
    MemLp (fun w ↦ ∏ a : I, w.1 (i a) (j a)) p W.toMeasure := by
  letI := W.probability
  exact A4Research.memLp_fintypeProd_of_all_finite
    (fun a (w : SymPosDef d) ↦ w.1 (i a) (j a))
    (fun a q ↦ W.memLp_entry (i a) (j a) q) p

/-- Determinants of matrices whose entries have all finite moments also have
all finite moments, by their exact finite permutation expansion. -/
theorem W_d.memLp_det_of_entries {d : ℕ} {beta : ℝ} {sigma : SymPosDef d}
    (W : W_d d beta sigma) (X : SymPosDef d → RealMatrix d)
    (hX : ∀ i j (p : ℝ≥0), MemLp (fun w ↦ X w i j) p W.toMeasure) (p : ℝ≥0) :
    MemLp (fun w ↦ Matrix.det (X w)) p W.toMeasure := by
  letI := W.probability
  simp_rw [Matrix.det_apply']
  apply memLp_finsetSum
  intro s _
  apply MemLp.const_mul
  exact A4Research.memLp_fintypeProd_of_all_finite
    (fun i w ↦ X w (s i) i) (fun i q ↦ hX (s i) i q) p

/-- Every adjugate entry has all finite moments. This uses the literal
row-replacement determinant definition and adds no inverse-moment hypothesis. -/
theorem W_d.memLp_adjugate_entry {d : ℕ} {beta : ℝ} {sigma : SymPosDef d}
    (W : W_d d beta sigma) (i j : Fin d) (p : ℝ≥0) :
    MemLp (fun w ↦ Matrix.adjugate w.1 i j) p W.toMeasure := by
  letI := W.probability
  simp_rw [Matrix.adjugate_apply]
  apply W.memLp_det_of_entries
  intro a b q
  by_cases h : a = j
  · simpa only [Matrix.updateRow_apply, if_pos h] using
      (memLp_const (μ := W.toMeasure) (p := (q : ℝ≥0∞)) ((Pi.single i 1 : Fin d → ℝ) b))
  · simpa only [Matrix.updateRow_apply, if_neg h] using W.memLp_entry a b q

/-- All finite products of adjugate entries have every finite `L^p` norm,
providing the polynomial factor in the sharp inverse-moment Hölder argument. -/
theorem W_d.memLp_prod_adjugate_entries {d : ℕ} {beta : ℝ} {sigma : SymPosDef d}
    (W : W_d d beta sigma) {I : Type*} [Fintype I]
    (i j : I → Fin d) (p : ℝ≥0) :
    MemLp (fun w ↦ ∏ a : I, Matrix.adjugate w.1 (i a) (j a)) p W.toMeasure := by
  letI := W.probability
  exact A4Research.memLp_fintypeProd_of_all_finite
    (fun a (w : SymPosDef d) ↦ Matrix.adjugate w.1 (i a) (j a))
    (fun a q ↦ W.memLp_adjugate_entry (i a) (j a) q) p

end MatsumotoPaper

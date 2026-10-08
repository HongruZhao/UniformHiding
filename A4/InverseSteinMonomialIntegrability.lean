import A4.InverseSteinWishartLaw
import Mathlib.MeasureTheory.Function.LpSpace.Basic

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal NNReal

noncomputable section
namespace A4Research.InverseStein

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option backward.isDefEq.respectTransparency false

local instance : ENNReal.HolderTriple 2 2 1 := by
  have hr : Real.HolderTriple 2 2 1 := ⟨by norm_num, by norm_num, by norm_num⟩
  simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using hr.ennrealOfReal

theorem memLp_finite_inverseProduct {k d : ℕ} {ι : Type*} [Fintype ι]
    (W : MatsumotoPaper.W_d d ((k : ℝ) / 2) (MatsumotoPaper.identityScale d))
    (indices : ι → Fin d × Fin d)
    (hgap : 2 * (Fintype.card ι : ℝ) - 1 < ((k : ℝ) - d - 1) / 2) :
    MemLp (fun R : Matrix (Fin k) (Fin d) ℝ ↦
      ∏ r, (realWishartGram R)⁻¹ (indices r).1 (indices r).2)
      2 (halfGaussianMatrix k d) := by
  let e := Fintype.equivFin ι
  have h := memLp_inverseEntryProduct_halfGaussianMatrix W (p := 2)
    (by norm_num) (by simpa only [mul_comm] using hgap)
    (fun r ↦ indices (e.symm r))
  simp only [ENNReal.ofReal_ofNat] at h
  refine MemLp.ae_eq ?_ h
  filter_upwards [] with R
  exact e.symm.prod_comp
    (fun r ↦ (realWishartGram R)⁻¹ (indices r).1 (indices r).2)

theorem memLp_finset_inverseProduct {k d : ℕ} {ι : Type*} [DecidableEq ι]
    (W : MatsumotoPaper.W_d d ((k : ℝ) / 2) (MatsumotoPaper.identityScale d))
    (s : Finset ι) (indices : ι → Fin d × Fin d)
    (hgap : 2 * (s.card : ℝ) - 1 < ((k : ℝ) - d - 1) / 2) :
    MemLp (fun R : Matrix (Fin k) (Fin d) ℝ ↦
      ∏ r ∈ s, (realWishartGram R)⁻¹ (indices r).1 (indices r).2)
      2 (halfGaussianMatrix k d) := by
  have h := memLp_finite_inverseProduct W
    (fun r : s ↦ indices r.1) (by simpa using hgap)
  refine MemLp.ae_eq ?_ h
  filter_upwards [] with R
  exact Finset.prod_coe_sort s
    (fun r ↦ (realWishartGram R)⁻¹ (indices r).1 (indices r).2)

theorem memLp_matrixCoordinate_halfGaussianMatrix {k d : ℕ}
    (a : Fin k) (i : Fin d) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun R : Matrix (Fin k) (Fin d) ℝ ↦ R a i)
      p (halfGaussianMatrix k d) := by
  let e := flatMatrixMeasurableEquiv k d
  have hf := (memLp_id_gaussianReal' (μ := 0) (v := halfGaussianVariance) p hp).comp_measurePreserving
      (measurePreserving_eval (μ := fun _ : Fin (k * d) ↦
        gaussianReal 0 halfGaussianVariance) (finProdFinEquiv (a, i)))
  have he := (measurePreserving_flatMatrixMeasurableEquiv k d).symm e
  have h := hf.comp_measurePreserving he
  simpa only [e, Function.comp_def, Function.eval, id_eq,
    flatMatrixMeasurableEquiv_symm_apply, Equiv.symm_apply_apply] using h

theorem memLp_two_matrixCoordinates_halfGaussianMatrix {k d : ℕ}
    (a b : Fin k) (i j : Fin d) :
    MemLp (fun R : Matrix (Fin k) (Fin d) ℝ ↦ R a i * R b j)
      2 (halfGaussianMatrix k d) := by
  have hr : Real.HolderTriple 4 4 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  letI : ENNReal.HolderTriple 4 4 2 := by
    simpa only [ENNReal.ofReal_ofNat] using hr.ennrealOfReal
  exact (memLp_matrixCoordinate_halfGaussianMatrix b j 4 (by norm_num)).mul'
    (memLp_matrixCoordinate_halfGaussianMatrix a i 4 (by norm_num))

theorem integrable_finite_inverseProduct {k d : ℕ} {ι : Type*} [Fintype ι]
    (W : MatsumotoPaper.W_d d ((k : ℝ) / 2) (MatsumotoPaper.identityScale d))
    (indices : ι → Fin d × Fin d)
    (hgap : 2 * (Fintype.card ι : ℝ) - 1 < ((k : ℝ) - d - 1) / 2) :
    Integrable (fun R : Matrix (Fin k) (Fin d) ℝ ↦
      ∏ r, (realWishartGram R)⁻¹ (indices r).1 (indices r).2)
      (halfGaussianMatrix k d) :=
  (memLp_finite_inverseProduct W indices hgap).integrable (by norm_num)

theorem integrable_coordinate_mul_finite_inverseProduct {k d : ℕ}
    {ι : Type*} [Fintype ι]
    (W : MatsumotoPaper.W_d d ((k : ℝ) / 2) (MatsumotoPaper.identityScale d))
    (indices : ι → Fin d × Fin d)
    (hgap : 2 * (Fintype.card ι : ℝ) - 1 < ((k : ℝ) - d - 1) / 2)
    (a : Fin k) (i : Fin d) :
    Integrable (fun R : Matrix (Fin k) (Fin d) ℝ ↦ R a i *
      ∏ r, (realWishartGram R)⁻¹ (indices r).1 (indices r).2)
      (halfGaussianMatrix k d) := by
  exact memLp_one_iff_integrable.mp
    ((memLp_finite_inverseProduct W indices hgap).mul'
      (memLp_matrixCoordinate_halfGaussianMatrix a i 2 (by norm_num)))

theorem integrable_two_coordinates_mul_finite_inverseProduct {k d : ℕ}
    {ι : Type*} [Fintype ι]
    (W : MatsumotoPaper.W_d d ((k : ℝ) / 2) (MatsumotoPaper.identityScale d))
    (indices : ι → Fin d × Fin d)
    (hgap : 2 * (Fintype.card ι : ℝ) - 1 < ((k : ℝ) - d - 1) / 2)
    (a b : Fin k) (i j : Fin d) :
    Integrable (fun R : Matrix (Fin k) (Fin d) ℝ ↦ (R a i * R b j) *
      ∏ r, (realWishartGram R)⁻¹ (indices r).1 (indices r).2)
      (halfGaussianMatrix k d) := by
  exact memLp_one_iff_integrable.mp
    ((memLp_finite_inverseProduct W indices hgap).mul'
      (memLp_two_matrixCoordinates_halfGaussianMatrix a b i j))

end A4Research.InverseStein

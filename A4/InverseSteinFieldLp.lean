import A4.InverseSteinMonomialIntegrability
import A4.InverseSteinNonsingularClosure

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal NNReal

noncomputable section
namespace A4Research.InverseStein

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

local instance : ENNReal.HolderTriple 32 32 16 := by
  have hr : Real.HolderTriple 32 32 16 := ⟨by norm_num, by norm_num, by norm_num⟩
  simpa only [ENNReal.ofReal_ofNat] using hr.ennrealOfReal
local instance : ENNReal.HolderTriple 16 16 8 := by
  have hr : Real.HolderTriple 16 16 8 := ⟨by norm_num, by norm_num, by norm_num⟩
  simpa only [ENNReal.ofReal_ofNat] using hr.ennrealOfReal
local instance : ENNReal.HolderTriple 8 8 4 := by
  have hr : Real.HolderTriple 8 8 4 := ⟨by norm_num, by norm_num, by norm_num⟩
  simpa only [ENNReal.ofReal_ofNat] using hr.ennrealOfReal
local instance : ENNReal.HolderTriple 4 4 2 := by
  have hr : Real.HolderTriple 4 4 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  simpa only [ENNReal.ofReal_ofNat] using hr.ennrealOfReal
local instance : ENNReal.HolderTriple 2 2 1 := by
  have hr : Real.HolderTriple 2 2 1 := ⟨by norm_num, by norm_num, by norm_num⟩
  simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using hr.ennrealOfReal

theorem memLp_matrix_mul_entry {α ι κ ν : Type*} [MeasurableSpace α]
    [Fintype κ] {μ : Measure α} {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    (A : α → Matrix ι κ ℝ) (B : α → Matrix κ ν ℝ)
    (hA : ∀ i l, MemLp (fun x ↦ A x i l) p μ)
    (hB : ∀ l j, MemLp (fun x ↦ B x l j) q μ) (i : ι) (j : ν) :
    MemLp (fun x ↦ (A x * B x) i j) r μ := by
  simp only [Matrix.mul_apply]
  exact memLp_finsetSum _ (fun l _ ↦ (hB l j).mul' (hA i l))

theorem memLp_matrix_mul_const_entry {α ι κ ν : Type*} [MeasurableSpace α]
    [Fintype κ] {μ : Measure α} {p : ℝ≥0∞}
    (A : α → Matrix ι κ ℝ) (B : Matrix κ ν ℝ)
    (hA : ∀ i l, MemLp (fun x ↦ A x i l) p μ) (i : ι) (j : ν) :
    MemLp (fun x ↦ (A x * B) i j) p μ := by
  simp only [Matrix.mul_apply]
  exact memLp_finsetSum _ (fun l _ ↦ (hA i l).mul_const (B l j))

theorem memLp_const_matrix_mul_entry {α ι κ ν : Type*} [MeasurableSpace α]
    [Fintype κ] {μ : Measure α} {p : ℝ≥0∞}
    (A : Matrix ι κ ℝ) (B : α → Matrix κ ν ℝ)
    (hB : ∀ l j, MemLp (fun x ↦ B x l j) p μ) (i : ι) (j : ν) :
    MemLp (fun x ↦ (A * B x) i j) p μ := by
  simp only [Matrix.mul_apply]
  exact memLp_finsetSum _ (fun l _ ↦ (hB l j).const_mul (A i l))

theorem memLp_finite_inverseProduct_exponent {k d : ℕ} {ι : Type*} [Fintype ι]
    (W : MatsumotoPaper.W_d d ((k : ℝ) / 2) (MatsumotoPaper.identityScale d))
    (indices : ι → Fin d × Fin d) {p : ℝ} (hp : 0 < p)
    (hgap : (Fintype.card ι : ℝ) * p - 1 < ((k : ℝ) - d - 1) / 2) :
    MemLp (fun R : Matrix (Fin k) (Fin d) ℝ ↦
      ∏ r, (realWishartGram R)⁻¹ (indices r).1 (indices r).2)
      (ENNReal.ofReal p) (halfGaussianMatrix k d) := by
  let e := Fintype.equivFin ι
  have h := memLp_inverseEntryProduct_halfGaussianMatrix W hp hgap
    (fun r ↦ indices (e.symm r))
  refine MemLp.ae_eq ?_ h
  filter_upwards [] with R
  exact e.symm.prod_comp
    (fun r ↦ (realWishartGram R)⁻¹ (indices r).1 (indices r).2)

theorem memLp_finset_inverseProduct_exponent {k d : ℕ} {ι : Type*} [DecidableEq ι]
    (W : MatsumotoPaper.W_d d ((k : ℝ) / 2) (MatsumotoPaper.identityScale d))
    (s : Finset ι) (indices : ι → Fin d × Fin d) {p : ℝ} (hp : 0 < p)
    (hgap : (s.card : ℝ) * p - 1 < ((k : ℝ) - d - 1) / 2) :
    MemLp (fun R : Matrix (Fin k) (Fin d) ℝ ↦
      ∏ r ∈ s, (realWishartGram R)⁻¹ (indices r).1 (indices r).2)
      (ENNReal.ofReal p) (halfGaussianMatrix k d) := by
  have h := memLp_finite_inverseProduct_exponent W
    (fun r : s ↦ indices r.1) hp (by simpa using hgap)
  refine MemLp.ae_eq ?_ h
  filter_upwards [] with R
  exact Finset.prod_coe_sort s
    (fun r ↦ (realWishartGram R)⁻¹ (indices r).1 (indices r).2)

theorem memLp_inverseGram_entry_32 {k d : ℕ}
    (W : MatsumotoPaper.W_d d ((k : ℝ) / 2) (MatsumotoPaper.identityScale d))
    (hgap : 31 < ((k : ℝ) - d - 1) / 2) (i j : Fin d) :
    MemLp (fun R : Matrix (Fin k) (Fin d) ℝ ↦ (realWishartGram R)⁻¹ i j)
      32 (halfGaussianMatrix k d) := by
  have h := memLp_finite_inverseProduct_exponent W
    (fun _ : Fin 1 ↦ (i, j)) (p := 32) (by norm_num) (by norm_num; exact hgap)
  simpa only [Fin.prod_univ_one, ENNReal.ofReal_ofNat] using h

theorem memLp_steinVectorFieldValue_entry {k d : ℕ}
    (W : MatsumotoPaper.W_d d ((k : ℝ) / 2) (MatsumotoPaper.identityScale d))
    (hgap : 31 < ((k : ℝ) - d - 1) / 2)
    (D : Matrix (Fin d) (Fin d) ℝ) (a : Fin k) (j : Fin d) :
    MemLp (fun R : Matrix (Fin k) (Fin d) ℝ ↦ steinVectorFieldValue R D a j)
      16 (halfGaussianMatrix k d) := by
  have hR (a : Fin k) (j : Fin d) :=
    memLp_matrixCoordinate_halfGaussianMatrix a j 32 (by norm_num)
  have hG := memLp_inverseGram_entry_32 W hgap
  have hRG := memLp_matrix_mul_entry (r := 16)
    (fun R : Matrix (Fin k) (Fin d) ℝ ↦ R)
    (fun R ↦ (realWishartGram R)⁻¹) hR hG
  have hRGD := memLp_matrix_mul_const_entry _ D hRG a j
  simpa only [steinVectorFieldValue, Matrix.smul_apply, smul_eq_mul] using
    hRGD.const_mul (1 / 2 : ℝ)

theorem memLp_steinVectorFieldLinearization_entry {k d : ℕ}
    (W : MatsumotoPaper.W_d d ((k : ℝ) / 2) (MatsumotoPaper.identityScale d))
    (hgap : 31 < ((k : ℝ) - d - 1) / 2)
    (D : Matrix (Fin d) (Fin d) ℝ) (E : Matrix (Fin k) (Fin d) ℝ)
    (a : Fin k) (j : Fin d) :
    MemLp (fun R : Matrix (Fin k) (Fin d) ℝ ↦
      steinVectorFieldLinearization R D E a j) 4 (halfGaussianMatrix k d) := by
  have hR32 (a : Fin k) (j : Fin d) :=
    memLp_matrixCoordinate_halfGaussianMatrix a j 32 (by norm_num)
  have hG32 := memLp_inverseGram_entry_32 W hgap
  have hG4 (i j : Fin d) := (hG32 i j).mono_exponent (by norm_num : (4 : ℝ≥0∞) ≤ 32)
  have hG8 (i j : Fin d) := (hG32 i j).mono_exponent (by norm_num : (8 : ℝ≥0∞) ≤ 32)
  have hR16 (a : Fin k) (j : Fin d) :=
    (hR32 a j).mono_exponent (by norm_num : (16 : ℝ≥0∞) ≤ 32)
  have hRG16 := memLp_matrix_mul_entry (r := 16)
    (fun R : Matrix (Fin k) (Fin d) ℝ ↦ R)
    (fun R ↦ (realWishartGram R)⁻¹) hR32 hG32
  have hRGD16 := memLp_matrix_mul_const_entry _ D hRG16
  have hRGEt16 := memLp_matrix_mul_const_entry _ E.transpose hRG16
  have hsecond8 := memLp_matrix_mul_entry (r := 8) _ _ hRGEt16 hRGD16 a j
  have hRGRt8 := memLp_matrix_mul_entry (r := 8) _ (fun R : Matrix (Fin k) (Fin d) ℝ ↦ R.transpose)
    hRG16 (fun i j ↦ hR16 j i)
  have hRGRtE8 := memLp_matrix_mul_const_entry _ E hRGRt8
  have hGD8 := memLp_matrix_mul_const_entry _ D hG8
  have hthird4 := memLp_matrix_mul_entry (r := 4) _ _ hRGRtE8 hGD8 a j
  have hGD4 := memLp_matrix_mul_const_entry _ D hG4
  have hfirst4 := memLp_const_matrix_mul_entry E _ hGD4 a j
  have hsecond4 := hsecond8.mono_exponent (by norm_num : (4 : ℝ≥0∞) ≤ 8)
  simpa only [steinVectorFieldLinearization, Matrix.smul_apply, Matrix.sub_apply,
    smul_eq_mul, Pi.sub_apply] using
      ((hfirst4.sub hsecond4).sub hthird4).const_mul (1 / 2 : ℝ)

end A4Research.InverseStein

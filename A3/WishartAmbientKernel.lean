import A3.WishartCholeskyCoordinates

open MeasureTheory Matrix Set
open scoped BigOperators ComplexOrder ENNReal

noncomputable section

namespace A3Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def wishartHermitianKappa (n : ℕ) (K : Type*) [RCLike K] : ℝ :=
  1 + (Module.finrank ℝ K : ℝ) * ((n : ℝ) - 1) / 2

variable {n : ℕ} {K : Type*} [RCLike K]

def wishartDetReal (x : HermitianCoordinates n K) : ℝ :=
  RCLike.re (hermitianMatrixOfCoordinates x).det

def wishartTraceReal (x : HermitianCoordinates n K) : ℝ :=
  RCLike.re (hermitianMatrixOfCoordinates x).trace

def wishartAmbientKernel (n : ℕ) (K : Type*) [RCLike K]
    (alpha : ℝ) (x : HermitianCoordinates n K) : ℝ :=
  Real.exp (-wishartTraceReal x) * wishartDetReal x ^ (alpha - wishartHermitianKappa n K)

def wishartAmbientDensity (n : ℕ) (K : Type*) [RCLike K]
    (alpha : ℝ) (x : HermitianCoordinates n K) : ℝ≥0∞ := by
  classical
  exact
  if (hermitianMatrixOfCoordinates x).PosDef then
    ENNReal.ofReal (wishartAmbientKernel n K alpha x) else 0

theorem isClosed_wishartPositiveSemidefiniteDomain :
    IsClosed {x : HermitianCoordinates n K | (hermitianMatrixOfCoordinates x).PosSemidef} := by
  have hnonneg : IsClosed {z : K | 0 ≤ z} := by
    have heq : {z : K | 0 ≤ z} = {z : K | 0 ≤ RCLike.re z} ∩ {z : K | RCLike.im z = 0} := by
      ext z
      exact RCLike.nonneg_iff
    rw [heq]
    exact (isClosed_le continuous_const RCLike.continuous_re).inter
      (isClosed_eq RCLike.continuous_im continuous_const)
  have heq : {x : HermitianCoordinates n K | (hermitianMatrixOfCoordinates x).PosSemidef} =
      ⋂ v : Fin n → K, {x | 0 ≤ star v ⬝ᵥ (hermitianMatrixOfCoordinates x *ᵥ v)} := by
    ext x
    simp only [mem_setOf_eq, mem_iInter, Matrix.posSemidef_iff_dotProduct_mulVec,
      hermitianMatrixOfCoordinates_isHermitian, true_and]
  rw [heq]
  apply isClosed_iInter
  intro v
  apply hnonneg.preimage
  have hm := continuous_hermitianMatrixOfCoordinates (n := n) (K := K)
  unfold dotProduct mulVec
  fun_prop

theorem measurableSet_wishartPositiveDefiniteDomain
    [MeasurableSpace K] [BorelSpace K] : MeasurableSet (wishartPositiveDefiniteDomain n K) := by
  have heq : wishartPositiveDefiniteDomain n K =
      {x : HermitianCoordinates n K | (hermitianMatrixOfCoordinates x).PosSemidef} ∩
        {x | (hermitianMatrixOfCoordinates x).det ≠ 0} := by
    ext x
    constructor
    · intro h
      exact ⟨h.posSemidef, h.det_pos.ne'⟩
    · rintro ⟨h, hd⟩
      exact h.posDef_iff_det_ne_zero.mpr hd
  rw [heq]
  apply isClosed_wishartPositiveSemidefiniteDomain.measurableSet.inter
  have hm := continuous_hermitianMatrixOfCoordinates (n := n) (K := K)
  have hd : Continuous (fun x : HermitianCoordinates n K ↦ (hermitianMatrixOfCoordinates x).det) := by
    fun_prop
  exact (hd.measurable (measurableSet_singleton (0 : K))).compl

theorem wishartDetReal_pos {x : HermitianCoordinates n K}
    (hx : x ∈ wishartPositiveDefiniteDomain n K) : 0 < wishartDetReal x :=
  (RCLike.pos_iff.mp hx.det_pos).1

theorem wishartAmbientKernel_pos (alpha : ℝ) {x : HermitianCoordinates n K}
    (hx : x ∈ wishartPositiveDefiniteDomain n K) : 0 < wishartAmbientKernel n K alpha x :=
  mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (wishartDetReal_pos hx) _)

theorem measurable_wishartAmbientKernel [MeasurableSpace K] [BorelSpace K] (alpha : ℝ) :
    Measurable (wishartAmbientKernel n K alpha) := by
  unfold wishartAmbientKernel wishartTraceReal wishartDetReal
  have hm := continuous_hermitianMatrixOfCoordinates (n := n) (K := K)
  fun_prop

theorem measurable_wishartAmbientDensity [MeasurableSpace K] [BorelSpace K] (alpha : ℝ) :
    Measurable (wishartAmbientDensity n K alpha) := by
  classical
  exact Measurable.ite (measurableSet_wishartPositiveDefiniteDomain (n := n) (K := K))
    (measurable_wishartAmbientKernel (n := n) (K := K) alpha).ennreal_ofReal measurable_const

def wishartAmbientMeasure (n : ℕ) (K : Type*) [RCLike K]
    [MeasureSpace K] [BorelSpace K] (alpha : ℝ) : Measure (HermitianCoordinates n K) :=
  (hermitianCoordinateVolume n K).withDensity (wishartAmbientDensity n K alpha)

end A3Research

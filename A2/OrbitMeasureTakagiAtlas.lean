import A2.OrbitMeasureFiniteAtlas
import A2.TakagiCayleyChart

open MeasureTheory MeasureTheory.Measure Set Function Metric
open scoped BigOperators ENNReal

noncomputable section

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

set_option maxHeartbeats 600000

/-- An actual finite bounded Cayley atlas of the complex unitary group. -/
theorem exists_finite_takagiCayley_atlas (N : ℕ) :
    ∃ n : ℕ, ∃ c : Fin (n + 1) → Matrix.unitaryGroup (Fin N) ℂ,
      let φ := fun i a ↦ c i * takagiAngularCayley a
      (∀ i, Continuous (φ i)) ∧
      (∀ i, InjOn (φ i) (ball (0 : TakagiAngularCoordinates N) 1)) ∧
      (∀ i, IsOpen (φ i '' ball (0 : TakagiAngularCoordinates N) 1)) ∧
      (⋃ i, φ i '' ball (0 : TakagiAngularCoordinates N) 1) = univ ∧
      (∀ i, MeasurableSet (A2Research.angularChartPiece
        (ball (0 : TakagiAngularCoordinates N) 1) φ i)) := by
  exact A2Research.exists_finite_translated_atlas
    (ball (0 : TakagiAngularCoordinates N) 1) isOpen_ball
    (@takagiAngularCayley N) (continuous_takagiAngularCayley N)
    (takagiAngularCayley_injective N).injOn (takagiAngularCayley_ball_isOpen N 1)
    (one_mem_takagiAngularCayley_ball N 1 (by norm_num))

def takagiAtlasAngularMass {N : ℕ} (n : ℕ)
    (c : Fin (n + 1) → Matrix.unitaryGroup (Fin N) ℂ) : ℝ≥0∞ :=
  ∑ i : Fin (n + 1), ∫⁻ a in A2Research.angularChartPiece
    (ball (0 : TakagiAngularCoordinates N) 1)
    (fun i a ↦ c i * takagiAngularCayley a) i,
      ENNReal.ofReal (takagiCayleyAngularDensity a)

theorem takagiAtlasAngularMass_pos_lt_top {N : ℕ} (n : ℕ)
    (c : Fin (n + 1) → Matrix.unitaryGroup (Fin N) ℂ) :
    0 < takagiAtlasAngularMass n c ∧ takagiAtlasAngularMass n c < ∞ := by
  exact A2Research.angular_atlas_mass_pos_lt_top volume n 1 (by norm_num)
    (fun i a ↦ c i * takagiAngularCayley a) takagiCayleyAngularDensity
    (continuous_takagiCayleyAngularDensity N) (fun a _ ↦ takagiCayleyAngularDensity_pos a)

def takagiAtlasOrbitConstant {N : ℕ} (n : ℕ)
    (c : Fin (n + 1) → Matrix.unitaryGroup (Fin N) ℂ) : NNReal :=
  (((2 ^ N * N.factorial : ℕ) : ℝ≥0∞)⁻¹ * takagiAtlasAngularMass n c).toNNReal

theorem takagiAtlasOrbitConstant_coe {N : ℕ} (n : ℕ)
    (c : Fin (n + 1) → Matrix.unitaryGroup (Fin N) ℂ) :
    (takagiAtlasOrbitConstant n c : ℝ≥0∞) =
      (((2 ^ N * N.factorial : ℕ) : ℝ≥0∞)⁻¹ * takagiAtlasAngularMass n c) := by
  apply ENNReal.coe_toNNReal
  apply ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr ?_)
    (takagiAtlasAngularMass_pos_lt_top n c).2 |>.ne
  exact_mod_cast (Nat.mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) N) N.factorial_pos)

theorem takagiAtlasOrbitConstant_pos {N : ℕ} (n : ℕ)
    (c : Fin (n + 1) → Matrix.unitaryGroup (Fin N) ℂ) :
    0 < takagiAtlasOrbitConstant n c := by
  apply ENNReal.toNNReal_pos_iff.mpr
  constructor
  · exact ENNReal.mul_pos (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _)).ne'
      (takagiAtlasAngularMass_pos_lt_top n c).1.ne'
  · exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (by
      exact_mod_cast (Nat.mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) N) N.factorial_pos)))
        (takagiAtlasAngularMass_pos_lt_top n c).2

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

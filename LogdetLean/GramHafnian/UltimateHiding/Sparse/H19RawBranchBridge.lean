import LogdetLean.GramHafnian.UltimateHiding.SquaredRegimeLift
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19RawSquaredRate
import LogdetLean.GramHafnian.UltimateHiding.Sparse.RegimeStitch

/-!
# Branch bridge for a quantitative raw-density H19 theorem

This file isolates the final probabilistic input still required by the raw
Jiang-density route.  The input is a universal rectangular total-variation
estimate at rate

`(K + N) * sqrt (K * N) / M`.

Everything after that input is elementary rate conversion and the existing
small-ambient stitch.  In particular, this module does not import the legacy
pointwise-likelihood or Jacobi-product interface.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding

noncomputable section

open CurrentPRL

namespace Sparse

/-- The universal quantitative statement targeted by the raw Jiang-density
proof.  It deliberately exposes only the rectangular total-variation rate
and the strict dimension range of the raw density. -/
def RawDensityTransposeGramQuantitative : Prop :=
  forall (H : UnitaryHaarProbabilityFamily) (M N K : Nat),
    0 < N -> 0 < K -> N <= K -> K + N < M ->
    probabilityTotalVariationLE
      (scaledHaarTransposeGramLaw H M N K)
      (gaussianTransposeGramLaw N K)
      (((K : Real) + N) * Real.sqrt ((K : Real) * N) / (M : Real))

/-- A raw rectangular bound supplies the very-large sparse squared branch.

The cutoff relation `kappa + 1 <= C0` is needed here, rather than only in the
later regime stitch, because the raw density is stated in the strict range
`K + N < M`.  Together with `K < kappa * N` and `C0 * N^2 <= M`, it proves
that strict range internally. -/
theorem veryLargeSparseSquaredBranchAt_of_rawDensityQuantitative
    {C : Real} {C0 kappa : Nat}
    (hraw : RawDensityTransposeGramQuantitative)
    (hkappaC0 : kappa + 1 <= C0)
    (hC : rawDensitySparseSquaredCoefficient kappa <= C) :
    VeryLargeSparseSquaredBranchAt C C0 kappa := by
  intro H M N K hN hNK hKM hlarge hsparse _hsum
  have hNpos : 0 < N := by omega
  have hKpos : 0 < K := hNpos.trans_le hNK
  have hNN : N <= N ^ 2 := by nlinarith
  have hstrict : K + N < M := by
    calc
      K + N < kappa * N + N := Nat.add_lt_add_right hsparse N
      _ = (kappa + 1) * N := by rw [Nat.add_mul, one_mul]
      _ <= (kappa + 1) * N ^ 2 := Nat.mul_le_mul_left _ hNN
      _ <= C0 * N ^ 2 := Nat.mul_le_mul_right _ hkappaC0
      _ <= M := hlarge
  have hMposNat : 0 < M := by omega
  have hMpos : (0 : Real) < M := by exact_mod_cast hMposNat
  have hKupperNat : K <= kappa * N := Nat.le_of_lt hsparse
  have hKupper : (K : Real) <= (kappa : Real) * (N : Real) := by
    exact_mod_cast hKupperNat
  have hrate :
      ((K : Real) + N) * Real.sqrt ((K : Real) * N) / (M : Real) <=
        rawDensitySparseSquaredCoefficient kappa *
          ultimateSquaredHidingRate M N := by
    have h := rawDensity_sparse_rate_le_squared_rate_nat
      (N := (N : Real)) (K := (K : Real)) (M := (M : Real))
      (kappa := kappa) (Nat.cast_nonneg N) hMpos hKupper
    simpa [ultimateSquaredHidingRate] using h
  have hrateC :
      ((K : Real) + N) * Real.sqrt ((K : Real) * N) / (M : Real) <=
        C * ultimateSquaredHidingRate M N := by
    exact hrate.trans <|
      mul_le_mul_of_nonneg_right hC (ultimateSquaredHidingRate_nonneg M N)
  have hquant := hraw H M N K hNpos hKpos hNK hstrict
  have hquantC := hquant.mono hrateC
  letI : IsProbabilityMeasure (scaledHaarTransposeGramLaw H M N K) :=
    scaledHaarTransposeGramLaw_isProbability H (hNK.trans hKM) hKM
  letI : IsProbabilityMeasure (gaussianTransposeGramLaw N K) :=
    gaussianTransposeGramLaw_isProbability N K
  exact probabilityTotalVariationLE_min_one hquantC

/-- The paper-facing sparse branch obtained by the existing small-ambient
stitch from the raw quantitative theorem. -/
theorem largeAmbientSparseSquaredBranchAt_of_rawDensityQuantitative
    {C : Real} {C0 kappa : Nat}
    (hraw : RawDensityTransposeGramQuantitative)
    (hC0C : (C0 : Real) <= C) (hkappaC0 : kappa + 1 <= C0)
    (hC : rawDensitySparseSquaredCoefficient kappa <= C) :
    LargeAmbientSparseSquaredBranchAt C kappa :=
  LargeAmbientSparseSquaredBranchAt.of_veryLarge hC0C hkappaC0
    (veryLargeSparseSquaredBranchAt_of_rawDensityQuantitative
      hraw hkappaC0 hC)

end Sparse

end

end LogdetLean.GramHafnian.UltimateHiding

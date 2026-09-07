import LogdetLean.GramHafnian.UltimateHiding.DenseScore.MixedScalarQuadraticClosure
import Mathlib.Tactic

/-!
# Four-factor Holder tools for the H13 projective contraction

The rank-one expansion of the H13 trace ledger produces products of four
scalar projective pairings.  This file records the purely measure-theoretic
`L^4 x L^4 x L^4 x L^4 -> L^1` step once, independently of any matrix or
probability input.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-- Real-valued Holder multiplication in the exact form used below. -/
theorem lpNorm_mul_le_of_holder_h13
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {p q s : ENNReal} {f g : Omega -> Real}
    (hf : MemLp f q mu) (hg : MemLp g p mu)
    [ENNReal.HolderTriple p q s] :
    lpNorm (fun omega => g omega * f omega) s mu <=
      lpNorm g p mu * lpNorm f q mu := by
  have hprod : MemLp (fun omega => g omega * f omega) s mu := hf.mul' hg
  have he : eLpNorm (fun omega => g omega * f omega) s mu <=
      eLpNorm g p mu * eLpNorm f q mu := by
    simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (p := p) (q := q) (r := s)
      hg.aestronglyMeasurable hf.aestronglyMeasurable
      (fun x y : Real => x * y) 1 (by
        filter_upwards [] with omega
        simp [nnnorm_mul])
  rw [← toReal_eLpNorm hprod.aestronglyMeasurable,
    ← toReal_eLpNorm hg.aestronglyMeasurable,
    ← toReal_eLpNorm hf.aestronglyMeasurable,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top hg.eLpNorm_ne_top hf.eLpNorm_ne_top) he

/-- Four real `L^4` functions have an `L^1` product. -/
theorem memLp_mul_four_h13
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {f1 f2 f3 f4 : Omega -> Real}
    (h1 : MemLp f1 4 mu) (h2 : MemLp f2 4 mu)
    (h3 : MemLp f3 4 mu) (h4 : MemLp f4 4 mu) :
    MemLp (fun omega => f1 omega * f2 omega * f3 omega * f4 omega) 1 mu := by
  letI : ENNReal.HolderTriple 4 4 2 := by
    have h : NNReal.HolderTriple 4 4 2 := by
      rw [NNReal.holderTriple_iff]
      norm_num
    change ENNReal.HolderTriple
      ((4 : NNReal) : ENNReal) ((4 : NNReal) : ENNReal)
        ((2 : NNReal) : ENNReal)
    exact h.coe_ennreal (by norm_num)
  have h12 : MemLp (fun omega => f1 omega * f2 omega) 2 mu := h2.mul' h1
  have h34 : MemLp (fun omega => f3 omega * f4 omega) 2 mu := h4.mul' h3
  have h1234 : MemLp
      (fun omega => (f1 omega * f2 omega) * (f3 omega * f4 omega)) 1 mu :=
    h34.mul' h12
  simpa only [mul_assoc] using h1234

/-- Quantitative four-factor Holder inequality. -/
theorem lpNorm_mul_four_le_h13
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {f1 f2 f3 f4 : Omega -> Real}
    (h1 : MemLp f1 4 mu) (h2 : MemLp f2 4 mu)
    (h3 : MemLp f3 4 mu) (h4 : MemLp f4 4 mu) :
    lpNorm (fun omega => f1 omega * f2 omega * f3 omega * f4 omega) 1 mu <=
      lpNorm f1 4 mu * lpNorm f2 4 mu *
        lpNorm f3 4 mu * lpNorm f4 4 mu := by
  letI : ENNReal.HolderTriple 4 4 2 := by
    have h : NNReal.HolderTriple 4 4 2 := by
      rw [NNReal.holderTriple_iff]
      norm_num
    change ENNReal.HolderTriple
      ((4 : NNReal) : ENNReal) ((4 : NNReal) : ENNReal)
        ((2 : NNReal) : ENNReal)
    exact h.coe_ennreal (by norm_num)
  have h12 : MemLp (fun omega => f1 omega * f2 omega) 2 mu := h2.mul' h1
  have h34 : MemLp (fun omega => f3 omega * f4 omega) 2 mu := h4.mul' h3
  have houter := lpNorm_mul_le_of_holder_h13 (s := (1 : ENNReal)) h34 h12
  have hleft := lpNorm_mul_le_of_holder_h13 (s := (2 : ENNReal)) h2 h1
  have hright := lpNorm_mul_le_of_holder_h13 (s := (2 : ENNReal)) h4 h3
  calc
    lpNorm (fun omega => f1 omega * f2 omega * f3 omega * f4 omega) 1 mu =
        lpNorm (fun omega =>
          (f1 omega * f2 omega) * (f3 omega * f4 omega)) 1 mu := by
      congr 1
      funext omega
      ring
    _ <= lpNorm (fun omega => f1 omega * f2 omega) 2 mu *
        lpNorm (fun omega => f3 omega * f4 omega) 2 mu := houter
    _ <= (lpNorm f1 4 mu * lpNorm f2 4 mu) *
        (lpNorm f3 4 mu * lpNorm f4 4 mu) :=
      mul_le_mul hleft hright lpNorm_nonneg
        (mul_nonneg lpNorm_nonneg lpNorm_nonneg)
    _ = lpNorm f1 4 mu * lpNorm f2 4 mu *
        lpNorm f3 4 mu * lpNorm f4 4 mu := by ring

/-- Integral-of-absolute-value form of the four-factor Holder inequality. -/
theorem integral_norm_mul_four_le_h13
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {f1 f2 f3 f4 : Omega -> Real}
    (h1 : MemLp f1 4 mu) (h2 : MemLp f2 4 mu)
    (h3 : MemLp f3 4 mu) (h4 : MemLp f4 4 mu) :
    (∫ omega, ‖f1 omega * f2 omega * f3 omega * f4 omega‖ ∂mu) <=
      lpNorm f1 4 mu * lpNorm f2 4 mu *
        lpNorm f3 4 mu * lpNorm f4 4 mu := by
  have hprod := memLp_mul_four_h13 h1 h2 h3 h4
  rw [← lpNorm_one_eq_integral_norm hprod.aestronglyMeasurable]
  exact lpNorm_mul_four_le_h13 h1 h2 h3 h4

/-! ## Complex-valued form for the transpose/bilinear H13 words -/

/-- Complex-valued Holder multiplication. -/
theorem lpNorm_mul_le_of_holder_complex_h13
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {p q s : ENNReal} {f g : Omega -> Complex}
    (hf : MemLp f q mu) (hg : MemLp g p mu)
    [ENNReal.HolderTriple p q s] :
    lpNorm (fun omega => g omega * f omega) s mu <=
      lpNorm g p mu * lpNorm f q mu := by
  have hprod : MemLp (fun omega => g omega * f omega) s mu := hf.mul' hg
  have he : eLpNorm (fun omega => g omega * f omega) s mu <=
      eLpNorm g p mu * eLpNorm f q mu := by
    simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (p := p) (q := q) (r := s)
      hg.aestronglyMeasurable hf.aestronglyMeasurable
      (fun x y : Complex => x * y) 1 (by
        filter_upwards [] with omega
        simp [nnnorm_mul])
  rw [← toReal_eLpNorm hprod.aestronglyMeasurable,
    ← toReal_eLpNorm hg.aestronglyMeasurable,
    ← toReal_eLpNorm hf.aestronglyMeasurable,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top hg.eLpNorm_ne_top hf.eLpNorm_ne_top) he

/-- Four complex `L^4` functions have an `L^1` product. -/
theorem memLp_mul_four_complex_h13
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {f1 f2 f3 f4 : Omega -> Complex}
    (h1 : MemLp f1 4 mu) (h2 : MemLp f2 4 mu)
    (h3 : MemLp f3 4 mu) (h4 : MemLp f4 4 mu) :
    MemLp (fun omega => f1 omega * f2 omega * f3 omega * f4 omega) 1 mu := by
  letI : ENNReal.HolderTriple 4 4 2 := by
    have h : NNReal.HolderTriple 4 4 2 := by
      rw [NNReal.holderTriple_iff]
      norm_num
    change ENNReal.HolderTriple
      ((4 : NNReal) : ENNReal) ((4 : NNReal) : ENNReal)
        ((2 : NNReal) : ENNReal)
    exact h.coe_ennreal (by norm_num)
  have h12 : MemLp (fun omega => f1 omega * f2 omega) 2 mu := h2.mul' h1
  have h34 : MemLp (fun omega => f3 omega * f4 omega) 2 mu := h4.mul' h3
  have h1234 : MemLp
      (fun omega => (f1 omega * f2 omega) * (f3 omega * f4 omega)) 1 mu :=
    h34.mul' h12
  simpa only [mul_assoc] using h1234

/-- Quantitative complex four-factor Holder inequality. -/
theorem lpNorm_mul_four_complex_le_h13
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {f1 f2 f3 f4 : Omega -> Complex}
    (h1 : MemLp f1 4 mu) (h2 : MemLp f2 4 mu)
    (h3 : MemLp f3 4 mu) (h4 : MemLp f4 4 mu) :
    lpNorm (fun omega => f1 omega * f2 omega * f3 omega * f4 omega) 1 mu <=
      lpNorm f1 4 mu * lpNorm f2 4 mu *
        lpNorm f3 4 mu * lpNorm f4 4 mu := by
  letI : ENNReal.HolderTriple 4 4 2 := by
    have h : NNReal.HolderTriple 4 4 2 := by
      rw [NNReal.holderTriple_iff]
      norm_num
    change ENNReal.HolderTriple
      ((4 : NNReal) : ENNReal) ((4 : NNReal) : ENNReal)
        ((2 : NNReal) : ENNReal)
    exact h.coe_ennreal (by norm_num)
  have h12 : MemLp (fun omega => f1 omega * f2 omega) 2 mu := h2.mul' h1
  have h34 : MemLp (fun omega => f3 omega * f4 omega) 2 mu := h4.mul' h3
  have houter := lpNorm_mul_le_of_holder_complex_h13
    (s := (1 : ENNReal)) h34 h12
  have hleft := lpNorm_mul_le_of_holder_complex_h13
    (s := (2 : ENNReal)) h2 h1
  have hright := lpNorm_mul_le_of_holder_complex_h13
    (s := (2 : ENNReal)) h4 h3
  calc
    lpNorm (fun omega => f1 omega * f2 omega * f3 omega * f4 omega) 1 mu =
        lpNorm (fun omega =>
          (f1 omega * f2 omega) * (f3 omega * f4 omega)) 1 mu := by
      congr 1
      funext omega
      ring
    _ <= lpNorm (fun omega => f1 omega * f2 omega) 2 mu *
        lpNorm (fun omega => f3 omega * f4 omega) 2 mu := houter
    _ <= (lpNorm f1 4 mu * lpNorm f2 4 mu) *
        (lpNorm f3 4 mu * lpNorm f4 4 mu) :=
      mul_le_mul hleft hright lpNorm_nonneg
        (mul_nonneg lpNorm_nonneg lpNorm_nonneg)
    _ = lpNorm f1 4 mu * lpNorm f2 4 mu *
        lpNorm f3 4 mu * lpNorm f4 4 mu := by ring

/-- Integral norm bound for four complex factors. -/
theorem integral_norm_mul_four_complex_le_h13
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {f1 f2 f3 f4 : Omega -> Complex}
    (h1 : MemLp f1 4 mu) (h2 : MemLp f2 4 mu)
    (h3 : MemLp f3 4 mu) (h4 : MemLp f4 4 mu) :
    (∫ omega, ‖f1 omega * f2 omega * f3 omega * f4 omega‖ ∂mu) <=
      lpNorm f1 4 mu * lpNorm f2 4 mu *
        lpNorm f3 4 mu * lpNorm f4 4 mu := by
  have hprod := memLp_mul_four_complex_h13 h1 h2 h3 h4
  rw [← lpNorm_one_eq_integral_norm hprod.aestronglyMeasurable]
  exact lpNorm_mul_four_complex_le_h13 h1 h2 h3 h4

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import LogdetLean.GramHafnian.CurrentPRL.TotalVariation

/-!
# Scheffe convergence for real probability densities

This file contains the elementary analytic bridge used by the direct H19
argument.  It is deliberately independent of Haar measure, random matrices,
and Jiang's formula.

If nonnegative integrable densities have the same total mass and converge
almost everywhere, then they converge in `L1`.  The proof is Scheffe's
identity

`|f_n - f| = f_n + f - 2 * min f_n f`

and dominated convergence for `min f_n f`, dominated by `f`.
-/

open Filter MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

/-- Scheffe's lemma for a sequence of real-valued densities. -/
theorem tendsto_integral_abs_sub_zero_of_nonneg_of_integral_eq
    {alpha : Type*} [MeasurableSpace alpha]
    {mu : Measure alpha} {f : Nat -> alpha -> Real} {g : alpha -> Real}
    (hf : forall n, Integrable (f n) mu) (hg : Integrable g mu)
    (hf_nonneg : forall n, ∀ᵐ x ∂mu, 0 <= f n x)
    (hg_nonneg : ∀ᵐ x ∂mu, 0 <= g x)
    (hmass : forall n, ∫ x, f n x ∂mu = ∫ x, g x ∂mu)
    (hlim : ∀ᵐ x ∂mu, Tendsto (fun n => f n x) atTop (nhds (g x))) :
    Tendsto (fun n => ∫ x, |f n x - g x| ∂mu) atTop (nhds 0) := by
  let h : Nat -> alpha -> Real := fun n x => min (f n x) (g x)
  have hh_meas : forall n, AEStronglyMeasurable (h n) mu := by
    intro n
    exact ((hf n).aemeasurable.min hg.aemeasurable).aestronglyMeasurable
  have hh_bound : forall n, ∀ᵐ x ∂mu, ‖h n x‖ <= g x := by
    intro n
    filter_upwards [hf_nonneg n, hg_nonneg] with x hfx hgx
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hfx hgx)]
    exact min_le_right _ _
  have hh_lim : ∀ᵐ x ∂mu,
      Tendsto (fun n => h n x) atTop (nhds (g x)) := by
    filter_upwards [hlim] with x hx
    simpa only [h, min_self] using hx.min
      (tendsto_const_nhds :
        Tendsto (fun _n : Nat => g x) atTop (nhds (g x)))
  have hint_min : Tendsto (fun n => ∫ x, h n x ∂mu) atTop
      (nhds (∫ x, g x ∂mu)) :=
    tendsto_integral_of_dominated_convergence g hh_meas hg hh_bound hh_lim
  have hh_int : forall n, Integrable (h n) mu := by
    intro n
    apply hg.mono (hh_meas n)
    filter_upwards [hh_bound n, hg_nonneg] with x hx hgx
    simpa [Real.norm_eq_abs, abs_of_nonneg hgx] using hx
  have habs_identity : forall n,
      (∫ x, |f n x - g x| ∂mu) =
        (∫ x, f n x ∂mu) + (∫ x, g x ∂mu) -
          2 * (∫ x, h n x ∂mu) := by
    intro n
    calc
      (∫ x, |f n x - g x| ∂mu) =
          ∫ x, (f n x + g x) - 2 * h n x ∂mu := by
        apply integral_congr_ae
        filter_upwards [hf_nonneg n, hg_nonneg] with x hfx hgx
        dsimp only [h]
        rcases le_total (f n x) (g x) with hfg | hgf
        · rw [min_eq_left hfg, abs_of_nonpos (sub_nonpos.mpr hfg)]
          ring
        · rw [min_eq_right hgf, abs_of_nonneg (sub_nonneg.mpr hgf)]
          ring
      _ = (∫ x, f n x + g x ∂mu) -
          ∫ x, 2 * h n x ∂mu := by
        simpa only [Pi.add_apply, Pi.sub_apply] using
          (integral_sub ((hf n).add hg) ((hh_int n).const_mul 2))
      _ = (∫ x, f n x ∂mu) + (∫ x, g x ∂mu) -
          2 * (∫ x, h n x ∂mu) := by
        rw [integral_add (hf n) hg, integral_const_mul]
  simp_rw [habs_identity, hmass]
  have hconst : Tendsto
      (fun _n : Nat => 2 * (∫ x, g x ∂mu)) atTop
      (nhds (2 * (∫ x, g x ∂mu))) := tendsto_const_nhds
  convert hconst.sub (hint_min.const_mul 2) using 1 <;> ring

/-- A nonnegative real density has the expected real set integral under
`withDensity`.  This is the type-generic form needed to turn an `L1` density
estimate into the eventwise probability-total-variation convention used by
the hiding theorem. -/
theorem withDensity_ofReal_measureReal_eq_setIntegral
    {alpha : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) (f : alpha -> Real) (hf : Integrable f mu)
    (hf_nonneg : forall x, 0 <= f x) (s : Set alpha) (hs : MeasurableSet s) :
    (mu.withDensity (fun x => ENNReal.ofReal (f x))).real s =
      ∫ x in s, f x ∂mu := by
  have hint : Integrable f (mu.restrict s) := hf.integrableOn
  have hnonneg_ae : 0 ≤ᵐ[mu.restrict s] f := ae_of_all _ hf_nonneg
  have heq := ofReal_integral_eq_lintegral_ofReal hint hnonneg_ae
  rw [measureReal_def, withDensity_apply _ hs, <- heq,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hnonneg_ae)]

/-- The elementary `L1` upper bound on eventwise probability total variation
for two real densities with respect to a common base measure. -/
theorem probabilityTotalVariationLE_withDensity_ofReal
    {alpha : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) (f g : alpha -> Real)
    (hf : Integrable f mu) (hg : Integrable g mu)
    (hf_nonneg : forall x, 0 <= f x) (hg_nonneg : forall x, 0 <= g x) :
    CurrentPRL.probabilityTotalVariationLE
      (mu.withDensity (fun x => ENNReal.ofReal (f x)))
      (mu.withDensity (fun x => ENNReal.ofReal (g x)))
      (∫ x, |f x - g x| ∂mu) := by
  have habs_int : Integrable (fun x => |f x - g x|) mu :=
    (hf.sub hg).abs
  refine ⟨integral_nonneg fun _ => abs_nonneg _, fun s hs => ?_⟩
  rw [withDensity_ofReal_measureReal_eq_setIntegral mu f hf hf_nonneg s hs,
    withDensity_ofReal_measureReal_eq_setIntegral mu g hg hg_nonneg s hs,
    <- integral_sub hf.integrableOn hg.integrableOn]
  exact abs_integral_le_integral_abs.trans
    (setIntegral_le_integral habs_int (ae_of_all _ fun x => abs_nonneg (f x - g x)))

/-- Scheffe convergence, stated directly in the eventwise probability-total-
variation convention. -/
theorem eventually_probabilityTotalVariationLE_withDensity_ofReal
    {alpha : Type*} [MeasurableSpace alpha]
    {mu : Measure alpha} {f : Nat -> alpha -> Real} {g : alpha -> Real}
    (hf : forall n, Integrable (f n) mu) (hg : Integrable g mu)
    (hf_nonneg : forall n x, 0 <= f n x) (hg_nonneg : forall x, 0 <= g x)
    (hmass : forall n, ∫ x, f n x ∂mu = ∫ x, g x ∂mu)
    (hlim : forall x, Tendsto (fun n => f n x) atTop (nhds (g x)))
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop,
      CurrentPRL.probabilityTotalVariationLE
        (mu.withDensity (fun x => ENNReal.ofReal (f n x)))
        (mu.withDensity (fun x => ENNReal.ofReal (g x))) epsilon := by
  have hL1 := tendsto_integral_abs_sub_zero_of_nonneg_of_integral_eq
    hf hg
    (fun n => ae_of_all _ (hf_nonneg n))
    (ae_of_all _ hg_nonneg) hmass
    (ae_of_all _ hlim)
  have hsmall : ∀ᶠ n in atTop, (∫ x, |f n x - g x| ∂mu) < epsilon :=
    (tendsto_order.1 hL1).2 epsilon hepsilon
  filter_upwards [hsmall] with n hn
  exact (probabilityTotalVariationLE_withDensity_ofReal
    mu (f n) g (hf n) hg (hf_nonneg n) hg_nonneg).mono hn.le

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse

import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19HaarStiefelNextColumn
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19HaarCornerSqrtMeasurable

/-!
# Exact probabilistic successor representation for a Haar corner

This file integrates the fixed-past next-column density over the past Haar
corner.  The result is the exact triangular representation needed by the
Jiang-density induction, with no additional probabilistic interface.
-/

open MeasureTheory Matrix Filter
open scoped ENNReal BigOperators ComplexOrder MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.CurrentPRL

/-- Fiberwise equality of pushforward laws can be integrated over a
measurable base map. -/
theorem map_prod_fiberwise_map_congr
    {alpha alpha' beta delta gamma : Type*}
    [MeasurableSpace alpha] [MeasurableSpace alpha']
    [MeasurableSpace beta] [MeasurableSpace delta]
    [MeasurableSpace gamma]
    (mu : Measure alpha) (nu : Measure beta) (kappa : Measure delta)
    [SFinite mu] [SFinite nu] [SFinite kappa]
    (f : alpha → alpha')
    (T : alpha → beta → gamma)
    (S : alpha' → delta → gamma)
    (hf : Measurable f)
    (hT : Measurable fun z : alpha × beta ↦ T z.1 z.2)
    (hS : Measurable fun z : alpha' × delta ↦ S z.1 z.2)
    (hfiber : ∀ a, Measure.map (T a) nu = Measure.map (S (f a)) kappa) :
    Measure.map (fun z : alpha × beta ↦ (f z.1, T z.1 z.2))
        (mu.prod nu) =
      Measure.map (fun z : alpha' × delta ↦ (z.1, S z.1 z.2))
        ((Measure.map f mu).prod kappa) := by
  let F : alpha × beta → alpha' × gamma :=
    fun z ↦ (f z.1, T z.1 z.2)
  let G : alpha' × delta → alpha' × gamma :=
    fun z ↦ (z.1, S z.1 z.2)
  have hF : Measurable F := (hf.comp measurable_fst).prodMk hT
  have hG : Measurable G := measurable_fst.prodMk hS
  apply Measure.ext_of_lintegral
  intro phi hphi
  rw [lintegral_map' hphi.aemeasurable hF.aemeasurable,
    lintegral_prod (fun z ↦ phi (F z)) (hphi.comp hF).aemeasurable]
  rw [lintegral_map' hphi.aemeasurable hG.aemeasurable,
    lintegral_prod (fun z ↦ phi (G z)) (hphi.comp hG).aemeasurable]
  have houter : Measurable
      (fun a' : alpha' ↦ ∫⁻ d, phi (G (a', d)) ∂kappa) :=
    (hphi.comp hG).lintegral_prod_right'
  rw [lintegral_map' houter.aemeasurable hf.aemeasurable]
  apply lintegral_congr
  intro a
  have hTa : Measurable (T a) :=
    hT.comp (measurable_const.prodMk measurable_id)
  have hSa : Measurable (S (f a)) :=
    hS.comp (measurable_const.prodMk measurable_id)
  have hphia : Measurable (fun y : gamma ↦ phi (f a, y)) :=
    hphi.comp (measurable_const.prodMk measurable_id)
  calc
    ∫⁻ b, phi (F (a, b)) ∂nu =
        ∫⁻ y, phi (f a, y) ∂Measure.map (T a) nu := by
      symm
      exact lintegral_map' hphia.aemeasurable hTa.aemeasurable
    _ = ∫⁻ y, phi (f a, y) ∂Measure.map (S (f a)) kappa := by
      rw [hfiber a]
    _ = ∫⁻ d, phi (G (f a, d)) ∂kappa := by
      exact lintegral_map' hphia.aemeasurable hSa.aemeasurable

#print axioms map_prod_fiberwise_map_congr

/-! ## Specialization to the Haar successor column -/

/-- Forgetting the Euclidean wrapper transports the explicit ball density
to the literal raw complex-column density. -/
theorem map_h19BaseColumnOfLp_withDensity
    (K r : ℕ) :
    Measure.map
        (WithLp.ofLp : EuclideanSpace ℂ (Fin K) → (Fin K → ℂ))
        ((volume : Measure (EuclideanSpace ℂ (Fin K))).withDensity
          (h19BaseColumnVectorPDF K r)) =
      (complexColumnLebesgueVolume K).withDensity
        (h19BaseColumnRawPDF K r) := by
  have htilt := LogdetLean.measurePreserving_map_withDensity_comp
    (measurePreserving_h19BaseColumnOfLp K)
    (h19BaseColumnRawPDF K r)
    (measurable_h19BaseColumnRawPDF K r)
  have hcomp :
      h19BaseColumnRawPDF K r ∘
          (WithLp.ofLp : EuclideanSpace ℂ (Fin K) → (Fin K → ℂ)) =
        h19BaseColumnVectorPDF K r := by
    funext x
    rfl
  rw [hcomp] at htilt
  simpa only [complexColumnLebesgueVolume_eq_volume] using htilt

/-- Appending a defect-square-root column after forgetting the Euclidean
wrapper is the literal triangular successor map. -/
theorem h19AppendColumn_defectSqrt_ofLp_eq
    {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℂ)
    (x : EuclideanSpace ℂ (Fin K)) :
    h19AppendColumn A
        (haarCornerDefectSqrt A *ᵥ WithLp.ofLp x) =
      haarCornerAppendSqrtColumn (A, WithLp.ofLp x) := by
  ext i j
  refine Fin.lastCases ?_ (fun q ↦ ?_) j
  · rw [h19AppendColumn_apply_last, haarCornerAppendSqrtColumn_last]
  · rw [h19AppendColumn_apply_castSucc,
      haarCornerAppendSqrtColumn_castSucc]

/-- The exact `N → N+1` Haar-corner representation with the explicit raw
complex-ball input density. -/
theorem jiangUnscaledTallHaarCornerLaw_succ_eq_map_appendSqrt_baseColumnRawPDF
    {M K N : ℕ} (hK : 1 ≤ K) (hsize : K + (N + 1) ≤ M) :
    jiangUnscaledTallHaarCornerLaw M K (N + 1) =
      Measure.map haarCornerAppendSqrtColumn
        ((jiangUnscaledTallHaarCornerLaw M K N).prod
          ((complexColumnLebesgueVolume K).withDensity
            (h19BaseColumnRawPDF K ((M - N) - K)))) := by
  let mu := unitaryHaarProbabilityMeasure M
  let nu := unitaryHaarProbabilityMeasure (M - N)
  let kappaE : Measure (EuclideanSpace ℂ (Fin K)) :=
    (volume : Measure (EuclideanSpace ℂ (Fin K))).withDensity
      (h19BaseColumnVectorPDF K ((M - N) - K))
  let kappaR : Measure (Fin K → ℂ) :=
    (complexColumnLebesgueVolume K).withDensity
      (h19BaseColumnRawPDF K ((M - N) - K))
  let hKM : K ≤ M := by omega
  let hNM : N ≤ M := by omega
  let hNsuccM : N + 1 ≤ M := by omega
  let hKd : K < M - N := by omega
  let past := h19HaarTallPast hKM hNM
  let generated := fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
    fun V : Matrix.unitaryGroup (Fin (M - N)) ℂ ↦
      h19HaarGeneratedTopColumn hKM hNM (by omega : 0 < M - N) (U, V)
  let canonical := fun A : Matrix (Fin K) (Fin N) ℂ ↦
    fun x : EuclideanSpace ℂ (Fin K) ↦
      haarCornerDefectSqrt A *ᵥ WithLp.ofLp x
  have hpast : Measurable past := measurable_h19HaarTallPast hKM hNM
  have hgenerated : Measurable
      (fun z : Matrix.unitaryGroup (Fin M) ℂ ×
          Matrix.unitaryGroup (Fin (M - N)) ℂ ↦
        generated z.1 z.2) := by
    simpa only [generated] using
      (measurable_h19HaarGeneratedTopColumn hKM hNM
        (by omega : 0 < M - N))
  have hcanonical : Measurable
      (fun z : Matrix (Fin K) (Fin N) ℂ ×
          EuclideanSpace ℂ (Fin K) ↦ canonical z.1 z.2) := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    unfold canonical Matrix.mulVec dotProduct
    refine Finset.measurable_sum _ fun j _ ↦ ?_
    exact ((measurable_pi_apply j).comp
        ((measurable_pi_apply i).comp
          ((measurable_haarCornerDefectSqrt K N).comp measurable_fst))).mul
      ((measurable_pi_apply j).comp
        ((WithLp.measurable_ofLp 2 (Fin K → ℂ)).comp measurable_snd))
  have hfiber (U : Matrix.unitaryGroup (Fin M) ℂ) :
      Measure.map (generated U) nu =
        Measure.map (canonical (past U)) kappaE := by
    simpa only [generated, canonical, past, nu, kappaE] using
      (map_h19HaarGeneratedTopColumn_eq_defectSqrt_baseColumnDensity
        hKM hNM hK hKd U)
  have hjoint := map_prod_fiberwise_map_congr
    mu nu kappaE past generated canonical hpast hgenerated hcanonical hfiber
  have hpastLaw : Measure.map past mu =
      jiangUnscaledTallHaarCornerLaw M K N := by
    rw [jiangUnscaledTallHaarCornerLaw, dif_pos ⟨hKM, hNM⟩]
    rfl
  have hkappa : Measure.map
      (WithLp.ofLp : EuclideanSpace ℂ (Fin K) → (Fin K → ℂ)) kappaE =
      kappaR := by
    simpa only [kappaE, kappaR] using
      (map_h19BaseColumnOfLp_withDensity K ((M - N) - K))
  have hprod :
      (Measure.map past mu).prod kappaR =
        Measure.map
          (Prod.map id
            (WithLp.ofLp : EuclideanSpace ℂ (Fin K) → (Fin K → ℂ)))
          ((Measure.map past mu).prod kappaE) := by
    rw [← hkappa]
    simpa only [Measure.map_id] using
      (Measure.map_prod_map (Measure.map past mu) kappaE
        measurable_id
        (WithLp.measurable_ofLp 2 (Fin K → ℂ)))
  rw [jiangUnscaledTallHaarCornerLaw_succ_eq_suffixHaar_append hKM hNsuccM]
  calc
    Measure.map
        (fun p : Matrix.unitaryGroup (Fin M) ℂ ×
            Matrix.unitaryGroup (Fin (M - N)) ℂ ↦
          h19AppendColumn (past p.1) (generated p.1 p.2))
        (mu.prod nu) =
      Measure.map (fun z ↦ h19AppendColumn z.1 z.2)
        (Measure.map (fun p ↦ (past p.1, generated p.1 p.2))
          (mu.prod nu)) := by
      symm
      exact Measure.map_map (measurable_h19AppendColumn K N)
        ((hpast.comp measurable_fst).prodMk hgenerated)
    _ = Measure.map (fun z ↦ h19AppendColumn z.1 z.2)
        (Measure.map (fun p ↦ (p.1, canonical p.1 p.2))
          ((Measure.map past mu).prod kappaE)) := by
      rw [hjoint]
    _ = Measure.map
        (fun p : Matrix (Fin K) (Fin N) ℂ ×
            EuclideanSpace ℂ (Fin K) ↦
          h19AppendColumn p.1 (canonical p.1 p.2))
        ((Measure.map past mu).prod kappaE) := by
      rw [Measure.map_map (measurable_h19AppendColumn K N)
        (measurable_fst.prodMk hcanonical)]
      rfl
    _ = Measure.map haarCornerAppendSqrtColumn
        ((Measure.map past mu).prod kappaR) := by
      rw [hprod, Measure.map_map]
      · apply Measure.map_congr
        filter_upwards with p
        rcases p with ⟨A, x⟩
        exact h19AppendColumn_defectSqrt_ofLp_eq A x
      · exact measurable_haarCornerAppendSqrtColumn K N
      · fun_prop
    _ = Measure.map haarCornerAppendSqrtColumn
        ((jiangUnscaledTallHaarCornerLaw M K N).prod kappaR) := by
      rw [hpastLaw]

#print axioms map_h19BaseColumnOfLp_withDensity
#print axioms jiangUnscaledTallHaarCornerLaw_succ_eq_map_appendSqrt_baseColumnRawPDF

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse

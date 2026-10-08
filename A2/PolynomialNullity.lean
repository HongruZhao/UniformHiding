import Mathlib

open MeasureTheory

noncomputable section

namespace A2Research

/-- A nonzero univariate polynomial vanishes on a null set for every atomless
measure. No density or probability normalization is required. -/
theorem ae_polynomial_eval_ne_zero {K : Type*} [Field K] [MeasurableSpace K]
    (μ : Measure K) [NullSingletonClass μ] {p : Polynomial K} (hp : p ≠ 0) :
    ∀ᵐ x ∂μ, p.eval x ≠ 0 := by
  rw [ae_iff]
  simpa only [not_not, Polynomial.IsRoot] using
    (Polynomial.finite_setOfPred_isRoot hp).measure_zero μ

/-- Every nonzero multivariate polynomial is nonzero almost everywhere under
the product of an atomless sigma-finite measure. -/
theorem ae_mvPolynomial_eval_ne_zero_fin {K : Type*} [NormedField K]
    [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K] (μ : Measure K)
    [SigmaFinite μ] [NullSingletonClass μ] (n : ℕ)
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin n ↦ μ), MvPolynomial.eval x p ≠ 0 := by
  classical
  induction n with
  | zero =>
      have hconst : MvPolynomial.coeff 0 p ≠ 0 := by
        intro h
        apply hp
        rw [MvPolynomial.eq_C_of_isEmpty p, h, map_zero]
      exact Filter.Eventually.of_forall fun x ↦ by
        rw [MvPolynomial.eq_C_of_isEmpty p, MvPolynomial.eval_C]
        exact hconst
  | succ n ih =>
      let q := MvPolynomial.finSuccEquiv K n p
      have hq : q ≠ 0 := by
        intro h
        apply hp
        exact (MvPolynomial.finSuccEquiv K n).injective (by simpa [q] using h)
      obtain ⟨k, hk⟩ : ∃ k, q.coeff k ≠ 0 := by
        by_contra h
        push Not at h
        apply hq
        exact Polynomial.ext fun k ↦ by simpa using h k
      have ha : ∀ᵐ x ∂(Measure.pi fun _ : Fin n ↦ μ),
          MvPolynomial.eval x (q.coeff k) ≠ 0 := ih _ hk
      have hmeas : Measurable (fun z : (Fin n → K) × K ↦
          MvPolynomial.eval (Fin.cons z.2 z.1) p) :=
        p.continuous_eval.measurable.comp (by fun_prop)
      have hset : MeasurableSet {z : (Fin n → K) × K |
          MvPolynomial.eval (Fin.cons z.2 z.1) p ≠ 0} := by
        simpa only [Set.compl_setOf] using (hmeas.eq_const 0).setOf.compl
      have hprod : ∀ᵐ z ∂((Measure.pi fun _ : Fin n ↦ μ).prod μ),
          MvPolynomial.eval (Fin.cons z.2 z.1) p ≠ 0 := by
        rw [Measure.ae_prod_iff_ae_ae hset]
        filter_upwards [ha] with x hx
        have hs : Polynomial.map (MvPolynomial.eval x) q ≠ 0 := by
          intro h
          have hc := congrArg (fun r : Polynomial K ↦ r.coeff k) h
          simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hc
          exact hx hc
        simpa only [MvPolynomial.eval_eq_eval_mv_eval', q] using
          ae_polynomial_eval_ne_zero μ hs
      let split : (Fin (n + 1) → K) → (Fin n → K) × K :=
        fun x ↦ (Fin.tail x, x 0)
      have hsplit : MeasurePreserving split
          (Measure.pi fun _ : Fin (n + 1) ↦ μ)
          ((Measure.pi fun _ : Fin n ↦ μ).prod μ) := by
        have hfirst := measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) ↦ μ) (0 : Fin (n + 1))
        have hswap := Measure.measurePreserving_swap.comp hfirst
        simpa [split, Function.comp_def, MeasurableEquiv.piFinSuccAbove_apply] using hswap
      have hmap : ∀ᵐ z ∂(Measure.map split
          (Measure.pi fun _ : Fin (n + 1) ↦ μ)),
          MvPolynomial.eval (Fin.cons z.2 z.1) p ≠ 0 := by
        rw [hsplit.map_eq]
        exact hprod
      have hcomp := (ae_map_iff hsplit.measurable.aemeasurable
        hset).mp hmap
      filter_upwards [hcomp] with x hx
      simpa [split] using hx

/-- The polynomial null-set statement is independent of the finite coordinate
indexing chosen for the product measure. -/
theorem ae_mvPolynomial_eval_ne_zero {K ι : Type*} [NormedField K]
    [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K] [Fintype ι]
    (μ : Measure K) [SigmaFinite μ] [NullSingletonClass μ]
    (p : MvPolynomial ι K) (hp : p ≠ 0) :
    ∀ᵐ x ∂(Measure.pi fun _ : ι ↦ μ), MvPolynomial.eval x p ≠ 0 := by
  classical
  let e := Fintype.equivFin ι
  let q := MvPolynomial.rename e p
  have hq : q ≠ 0 := by
    intro h
    apply hp
    exact (MvPolynomial.renameEquiv K e).injective (by simpa [q] using h)
  have hfin := ae_mvPolynomial_eval_ne_zero_fin μ (Fintype.card ι) q hq
  let split : (ι → K) → (Fin (Fintype.card ι) → K) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card ι) ↦ K) e
  have hsplit : MeasurePreserving split
      (Measure.pi fun _ : ι ↦ μ) (Measure.pi fun _ : Fin (Fintype.card ι) ↦ μ) := by
    exact measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card ι) ↦ μ) e
  have hmap : ∀ᵐ y ∂(Measure.map split (Measure.pi fun _ : ι ↦ μ)),
      MvPolynomial.eval y q ≠ 0 := by
    rw [hsplit.map_eq]
    exact hfin
  have hset : MeasurableSet {y : Fin (Fintype.card ι) → K |
      MvPolynomial.eval y q ≠ 0} := by
    simpa only [Set.compl_setOf] using (q.continuous_eval.measurable.eq_const 0).setOf.compl
  have hcomp := (ae_map_iff hsplit.measurable.aemeasurable hset).mp hmap
  filter_upwards [hcomp] with x hx
  have heval : MvPolynomial.eval (split x) q = MvPolynomial.eval x p := by
    dsimp only [q]
    rw [MvPolynomial.eval_rename]
    have hfun : split x ∘ e = x := by
      funext i
      exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ ↦ K) e x i
    rw [hfun]
  rwa [heval] at hx

end A2Research

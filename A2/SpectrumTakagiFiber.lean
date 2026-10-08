import A2.SpectrumTakagiPermutation

open scoped Matrix

noncomputable section

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

def RegularTakagiFiber {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ) :=
  {z : Matrix.unitaryGroup (Fin N) ℂ × (Fin N → ℝ) //
    IsRegularTakagiSpectrum z.2 ∧ takagiOrbit z.1 z.2 = C}

def regularTakagiRepresentation {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ)
    (hlambda : IsRegularTakagiSpectrum lambda)
    (s : TakagiSigns N × Equiv.Perm (Fin N)) :
    RegularTakagiFiber (takagiOrbit U lambda) :=
  ⟨⟨(U * takagiPermutationUnitary s.2.symm) * takagiSignUnitary s.1,
      lambda ∘ s.2⟩, hlambda.comp_perm s.2, by
    rw [takagiOrbit_mul_sign, takagiOrbit_mul_permutation]
    simp [Function.comp_def]⟩

theorem regularTakagiRepresentation_injective {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ)
    (hlambda : IsRegularTakagiSpectrum lambda) :
    Function.Injective (regularTakagiRepresentation U lambda hlambda) := by
  rintro ⟨epsilon, sigma⟩ ⟨eta, tau⟩ h
  have hrad := congrArg (fun z : RegularTakagiFiber (takagiOrbit U lambda) => z.val.2) h
  change lambda ∘ sigma = lambda ∘ tau at hrad
  have hperm : sigma = tau := by
    apply Equiv.ext
    intro i
    exact hlambda.2 (congrFun hrad i)
  subst tau
  have hang := congrArg (fun z : RegularTakagiFiber (takagiOrbit U lambda) => z.val.1) h
  change (U * takagiPermutationUnitary sigma.symm) * takagiSignUnitary epsilon =
    (U * takagiPermutationUnitary sigma.symm) * takagiSignUnitary eta at hang
  exact Prod.ext (takagiSignUnitary_injective (mul_left_cancel hang)) rfl

theorem regularTakagiRepresentation_surjective {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ)
    (hlambda : IsRegularTakagiSpectrum lambda) :
    Function.Surjective (regularTakagiRepresentation U lambda hlambda) := by
  rintro ⟨⟨V, mu⟩, hmu, hV⟩
  obtain ⟨sigma, hsigma, _⟩ :=
    takagiOrbit_eq_spectrum_permutation U V lambda mu hlambda hmu hV
  have hbase : takagiOrbit (U * takagiPermutationUnitary sigma.symm) mu =
      takagiOrbit U lambda := by
    rw [takagiOrbit_mul_permutation, hsigma]
    simp [Function.comp_def]
  obtain ⟨epsilon, hepsilon, _⟩ :=
    (takagiOrbit_eq_iff_exists_unique_sign
      (U * takagiPermutationUnitary sigma.symm) V mu hmu).mp (hV.trans hbase.symm)
  refine ⟨⟨epsilon, sigma⟩, ?_⟩
  apply Subtype.ext
  exact Prod.ext hepsilon.symm hsigma.symm

def regularTakagiFiberEquiv {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ)
    (hlambda : IsRegularTakagiSpectrum lambda) :
    (TakagiSigns N × Equiv.Perm (Fin N)) ≃ RegularTakagiFiber (takagiOrbit U lambda) :=
  Equiv.ofBijective (regularTakagiRepresentation U lambda hlambda)
    ⟨regularTakagiRepresentation_injective U lambda hlambda,
      regularTakagiRepresentation_surjective U lambda hlambda⟩

theorem regularTakagiFiber_natCard {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ)
    (hlambda : IsRegularTakagiSpectrum lambda) :
    Nat.card (RegularTakagiFiber (takagiOrbit U lambda)) = 2 ^ N * N.factorial := by
  rw [← Nat.card_congr (regularTakagiFiberEquiv U lambda hlambda), Nat.card_eq_fintype_card]
  simp [TakagiSigns, Fintype.card_prod, Fintype.card_fun, Fintype.card_perm]

theorem regularTakagiFiber_equiv_fin {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ)
    (hlambda : IsRegularTakagiSpectrum lambda) :
    Nonempty (RegularTakagiFiber (takagiOrbit U lambda) ≃ Fin (2 ^ N * N.factorial)) := by
  let e := regularTakagiFiberEquiv U lambda hlambda
  letI : Fintype (RegularTakagiFiber (takagiOrbit U lambda)) := Fintype.ofEquiv _ e
  refine ⟨Fintype.equivFinOfCardEq ?_⟩
  simpa only [Nat.card_eq_fintype_card] using regularTakagiFiber_natCard U lambda hlambda

theorem regularTakagiFiber_equiv_fin_of_representation {N : ℕ}
    (C : Matrix (Fin N) (Fin N) ℂ)
    (U : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ)
    (hlambda : IsRegularTakagiSpectrum lambda) (hC : C = takagiOrbit U lambda) :
    Nonempty (RegularTakagiFiber C ≃ Fin (2 ^ N * N.factorial)) := by
  subst C
  exact regularTakagiFiber_equiv_fin U lambda hlambda

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

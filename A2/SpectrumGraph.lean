import A2.SpectrumRoots

open scoped BigOperators
open Matrix Polynomial MeasureTheory Set

noncomputable section
namespace A2Research

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The graph of descending real characteristic roots, with multiplicities. -/
def orderedSpectrumGraph (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) :
    Set (Matrix (Fin N) (Fin N) 𝕜 × (Fin (Fintype.card (Fin N)) → ℝ)) :=
  {p | Antitone p.2 ∧ ∀ z : 𝕜,
    (Matrix.scalar (Fin N) z - p.1).det =
      ∏ i, (z - RCLike.ofReal (p.2 i))}

theorem mem_orderedSpectrumGraph_iff {N : ℕ}
    {p : Matrix (Fin N) (Fin N) 𝕜 × (Fin (Fintype.card (Fin N)) → ℝ)} :
    p ∈ orderedSpectrumGraph 𝕜 N ↔
      Antitone p.2 ∧ p.1.charpoly = realRootPolynomial p.2 := by
  constructor
  · intro h
    refine ⟨h.1, Polynomial.funext fun z ↦ ?_⟩
    rw [Matrix.eval_charpoly]
    simpa [realRootPolynomial, Polynomial.eval_prod] using h.2 z
  · intro h
    refine ⟨h.1, fun z ↦ ?_⟩
    have heval := congrArg (Polynomial.eval z) h.2
    simpa [Matrix.eval_charpoly, realRootPolynomial, Polynomial.eval_prod] using heval

theorem isClosed_orderedSpectrumGraph (N : ℕ) :
    IsClosed (orderedSpectrumGraph 𝕜 N) := by
  have hanti : IsClosed
      {p : Matrix (Fin N) (Fin N) 𝕜 × (Fin (Fintype.card (Fin N)) → ℝ) |
        Antitone p.2} := by
    simp only [Antitone, Set.setOf_forall]
    refine isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun _h ↦ ?_
    exact isClosed_le ((continuous_apply j).comp continuous_snd)
      ((continuous_apply i).comp continuous_snd)
  have hpoly : IsClosed
      {p : Matrix (Fin N) (Fin N) 𝕜 × (Fin (Fintype.card (Fin N)) → ℝ) |
        ∀ z : 𝕜, (Matrix.scalar (Fin N) z - p.1).det =
          ∏ i, (z - RCLike.ofReal (p.2 i))} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun z ↦ ?_
    apply isClosed_eq
    · fun_prop
    · fun_prop
  exact hanti.inter hpoly

/-- Projection forgetting the ordered root list. -/
def orderedSpectrumProjection (𝕜 : Type*) [RCLike 𝕜] (N : ℕ) :
    orderedSpectrumGraph 𝕜 N → Matrix (Fin N) (Fin N) 𝕜 :=
  fun p ↦ p.val.1

theorem continuous_orderedSpectrumProjection (N : ℕ) :
    Continuous (orderedSpectrumProjection 𝕜 N) :=
  continuous_fst.comp continuous_subtype_val

theorem injective_orderedSpectrumProjection (N : ℕ) :
    Function.Injective (orderedSpectrumProjection 𝕜 N) := by
  intro a b hab
  apply Subtype.ext
  apply Prod.ext hab
  have ha := mem_orderedSpectrumGraph_iff.mp a.property
  have hb := mem_orderedSpectrumGraph_iff.mp b.property
  exact realRootPolynomial_injective_on_antitone ha.1 hb.1
    (ha.2.symm.trans ((congrArg Matrix.charpoly hab).trans hb.2))

theorem eigenvalues₀_mem_orderedSpectrumGraph {N : ℕ}
    {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian) :
    (A, hA.eigenvalues₀) ∈ orderedSpectrumGraph 𝕜 N := by
  exact mem_orderedSpectrumGraph_iff.mpr
    ⟨hA.eigenvalues₀_antitone, charpoly_eq_realRootPolynomial_eigenvalues₀ hA⟩

end A2Research

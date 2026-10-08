import A3.WishartCholeskySmooth
import A3.WishartColumnJacobian

open Matrix Filter
open scoped BigOperators Topology

noncomputable section

namespace A3Research

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {K : Type*} [RCLike K]

theorem det_fderiv_wishartGramCoordinates_cons (p : ℝ) (z : Fin n → K)
    (y : HermitianCoordinates n K) (hp : 0 < p) (hy : y ∈ wishartCholeskyDomain n K) :
    (fderiv ℝ wishartGramCoordinates (wishartCoordinatesCons p z y)).toLinearMap.det =
      (Real.sqrt p) ^ Module.finrank ℝ (Fin n → K) *
        (fderiv ℝ wishartGramCoordinates y).toLinearMap.det := by
  let e := (wishartCoordinatesSplitLinearEquiv n K).toContinuousLinearEquiv
  let x := wishartCoordinatesCons p z y
  let F : HermitianCoordinates n K → HermitianCoordinates n K := wishartGramCoordinates
  let R : (Fin n → K) → HermitianCoordinates n K := wishartRankOneCoordinates
  let D := wishartColumnDerivative p z (fderiv ℝ F y) (fderiv ℝ R z)
  have hF : HasFDerivAt F (fderiv ℝ F y) y :=
    (contDiffAt_wishartGramCoordinates 1 y hy).differentiableAt_one.hasFDerivAt
  have hR : HasFDerivAt R (fderiv ℝ R z) z :=
    ((contDiff_wishartRankOneCoordinates (n := n) (K := K) 1).differentiable (by norm_num) z).hasFDerivAt
  have hex : e x = (p, (z, y)) := wishartCoordinatesSplit_cons p z y
  have hD : HasFDerivAt (wishartColumnMap F R) D (e x) := by
    rw [hex]
    exact hasFDerivAt_wishartColumnMap p z y hp _ _ hF hR
  have hcomp := e.symm.toContinuousLinearMap.hasFDerivAt.comp x
    (hD.comp x e.toContinuousLinearMap.hasFDerivAt)
  have hpos : ∀ᶠ u in 𝓝 x, 0 < (e u).1 := by
    apply (isOpen_lt continuous_const (continuous_fst.comp e.continuous)).mem_nhds
    change 0 < (e x).1
    rw [hex]
    exact hp
  have heq : wishartGramCoordinates =ᶠ[𝓝 x]
      e.symm ∘ wishartColumnMap F R ∘ e := by
    filter_upwards [hpos] with u hu
    apply e.injective
    simp only [Function.comp_apply, e.apply_symm_apply]
    have ht := wishartGramCoordinates_cons (e u).1 (e u).2.1 (e u).2.2 hu.le
    have hes (v : HermitianCoordinates (n + 1) K) : e v = wishartCoordinatesSplit v := rfl
    simp only [hes] at ht ⊢
    rw [wishartCoordinatesCons_split] at ht
    exact ht
  have hactual := hcomp.congr_of_eventuallyEq heq
  rw [hactual.fderiv]
  simp only [ContinuousLinearMap.toLinearMap_comp]
  have hc : (e.symm.toContinuousLinearMap.toLinearMap.comp
      (D.toLinearMap.comp e.toContinuousLinearMap.toLinearMap)).det = D.toLinearMap.det := by
    convert LinearMap.det_conj D.toLinearMap e.symm.toLinearEquiv using 1
    rfl
  rw [hc]
  exact det_wishartColumnDerivative p z (fderiv ℝ F y) (fderiv ℝ R z)

/-- Exact real Cholesky Jacobian in squared-pivot coordinates, in every dimension. -/
theorem det_fderiv_wishartGramCoordinates (x : HermitianCoordinates n K)
    (hx : x ∈ wishartCholeskyDomain n K) :
    (fderiv ℝ wishartGramCoordinates x).toLinearMap.det =
      ∏ i : Fin n, (Real.sqrt (x.1 i)) ^
        (Module.finrank ℝ K * (n - 1 - (i : ℕ))) := by
  induction n with
  | zero =>
    simp only [Fin.prod_univ_zero]
    exact LinearMap.det_eq_one_of_finrank_eq_zero (by
      exact Module.finrank_zero_of_subsingleton) _
  | succ n ih =>
    let e := wishartCoordinatesSplitLinearEquiv n K
    obtain ⟨⟨p, z, y⟩, hxy⟩ := e.symm.surjective x
    subst x
    dsimp [e, wishartCoordinatesSplitLinearEquiv] at hx ⊢
    obtain ⟨hp, hy⟩ := (wishartCoordinatesCons_mem_domain p z y).mp hx
    rw [det_fderiv_wishartGramCoordinates_cons p z y hp hy, ih y hy,
      Fin.prod_univ_succ]
    simp only [wishartCoordinatesCons_diag_zero, wishartCoordinatesCons_diag_succ,
      Module.finrank_pi_fintype, Fintype.card_fin, Fin.val_zero, Nat.sub_zero,
      Nat.add_sub_cancel]
    congr 1
    · congr 1
      simp [mul_comm]
    · apply Finset.prod_congr rfl
      intro i _
      simp only [Fin.val_succ]
      rw [show n - (i.val + 1) = n - 1 - i.val by omega]

theorem det_fderiv_wishartGramCoordinates_pos (x : HermitianCoordinates n K)
    (hx : x ∈ wishartCholeskyDomain n K) :
    0 < (fderiv ℝ wishartGramCoordinates x).toLinearMap.det := by
  rw [det_fderiv_wishartGramCoordinates x hx]
  apply Finset.prod_pos
  intro i _
  exact pow_pos (Real.sqrt_pos.mpr (hx i)) _

end A3Research

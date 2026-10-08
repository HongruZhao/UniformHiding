import A3.WishartCholeskyBlock

open Matrix

noncomputable section

namespace A3Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem wishartGramCoordinates_injOn {n : ℕ} {K : Type*} [RCLike K] :
    Set.InjOn (wishartGramCoordinates : HermitianCoordinates n K → _)
      (wishartCholeskyDomain n K) := by
  induction n with
  | zero =>
    intro x hx y hy h
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · exact Subsingleton.elim _ _
  | succ n ih =>
    intro x hx y hy hxy
    let e := wishartCoordinatesSplitLinearEquiv n K
    obtain ⟨⟨p, z, u⟩, hx'⟩ := e.symm.surjective x
    obtain ⟨⟨p', z', u'⟩, hy'⟩ := e.symm.surjective y
    have hxc : x = wishartCoordinatesCons p z u := hx'.symm
    have hyc : y = wishartCoordinatesCons p' z' u' := hy'.symm
    subst x
    subst y
    dsimp [e, wishartCoordinatesSplitLinearEquiv] at hx hy hxy ⊢
    obtain ⟨hp, hu⟩ := (wishartCoordinatesCons_mem_domain p z u).mp hx
    obtain ⟨hp', hu'⟩ := (wishartCoordinatesCons_mem_domain p' z' u').mp hy
    have h := congrArg wishartCoordinatesSplit hxy
    rw [wishartGramCoordinates_cons p z u hp.le,
      wishartGramCoordinates_cons p' z' u' hp'.le] at h
    have hpp : p = p' := congrArg Prod.fst h
    subst p'
    have hzz : (Real.sqrt p) • z = (Real.sqrt p) • z' :=
      congrArg (fun x : ℝ × ((Fin n → K) × HermitianCoordinates n K) ↦ x.2.1) h
    have hz : z = z' := by
      have he := congrArg (fun v : Fin n → K ↦ (Real.sqrt p)⁻¹ • v) hzz
      simpa only [smul_smul, inv_mul_cancel₀ (Real.sqrt_pos.mpr hp).ne', one_smul] using he
    subst z'
    have huu : wishartGramCoordinates u = wishartGramCoordinates u' :=
      add_right_cancel (congrArg
        (fun x : ℝ × ((Fin n → K) × HermitianCoordinates n K) ↦ x.2.2) h)
    have huEq := ih hu hu' huu
    subst u'
    rfl

theorem wishartGramCoordinates_bijOn {n : ℕ} {K : Type*} [RCLike K] :
    Set.BijOn (wishartGramCoordinates : HermitianCoordinates n K → _)
      (wishartCholeskyDomain n K) (wishartPositiveDefiniteDomain n K) :=
  ⟨wishartGramCoordinates_posDef, wishartGramCoordinates_injOn, wishartGramCoordinates_surjOn⟩

end A3Research

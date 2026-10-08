import A3.FlagStabilizer

open scoped BigOperators Matrix.Norms.Elementwise
open Matrix Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]

/-- The actual simultaneous unitary action on the ordered rank-one projectors. -/
def flagAction (U : Matrix.unitaryGroup (Fin n) K) (P : flagSpace n K) : flagSpace n K :=
  ⟨fun i ↦ (U : Matrix (Fin n) (Fin n) K) * P.1 i * star (U : Matrix (Fin n) (Fin n) K), by
    obtain ⟨V, hV⟩ := P.property
    refine ⟨U * V, ?_⟩
    funext i
    rw [flagProjectors_mul, hV]⟩

@[simp] theorem flagAction_flagOrbit (U V : Matrix.unitaryGroup (Fin n) K) :
    flagAction U (flagOrbit V) = flagOrbit (U * V) := by
  apply Subtype.ext
  funext i
  exact (flagProjectors_mul U V i).symm

@[simp] theorem flagAction_one (P : flagSpace n K) :
    flagAction (1 : Matrix.unitaryGroup (Fin n) K) P = P := by
  apply Subtype.ext
  funext i
  simp [flagAction]

theorem flagAction_mul (U V : Matrix.unitaryGroup (Fin n) K) (P : flagSpace n K) :
    flagAction (U * V) P = flagAction U (flagAction V P) := by
  apply Subtype.ext
  funext i
  simp only [flagAction, Matrix.UnitaryGroup.mul_val, star_mul, Matrix.mul_assoc]

theorem continuous_flagAction (U : Matrix.unitaryGroup (Fin n) K) :
    Continuous (flagAction U) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun i ↦ by
    change Continuous (fun P : flagSpace n K ↦
      (U : Matrix (Fin n) (Fin n) K) * P.1 i * star (U : Matrix (Fin n) (Fin n) K))
    exact (continuous_const.mul ((continuous_apply i).comp continuous_subtype_val)).mul
      continuous_const

def flagActionHomeomorph (U : Matrix.unitaryGroup (Fin n) K) :
    flagSpace n K ≃ₜ flagSpace n K where
  toFun := flagAction U
  invFun := flagAction U⁻¹
  left_inv := by intro P; rw [← flagAction_mul, inv_mul_cancel, flagAction_one]
  right_inv := by intro P; rw [← flagAction_mul, mul_inv_cancel, flagAction_one]
  continuous_toFun := continuous_flagAction U
  continuous_invFun := continuous_flagAction U⁻¹

/-- Every actual open flag neighborhood has a finite unitary-translated cover. -/
theorem exists_finite_flag_translates_cover
    (v : Set (flagSpace n K)) (hv : IsOpen v)
    (h1 : flagOrbit (1 : Matrix.unitaryGroup (Fin n) K) ∈ v) :
    ∃ c : Finset (Matrix.unitaryGroup (Fin n) K), c.Nonempty ∧
      ∀ P : flagSpace n K, ∃ U ∈ c, flagAction U⁻¹ P ∈ v := by
  classical
  let u : Matrix.unitaryGroup (Fin n) K → Set (flagSpace n K) :=
    fun U ↦ flagAction U⁻¹ ⁻¹' v
  have hu : ∀ U, IsOpen (u U) := fun U ↦ hv.preimage (continuous_flagAction U⁻¹)
  have hcover : (univ : Set (flagSpace n K)) ⊆ ⋃ U, u U := by
    intro P _
    obtain ⟨V, hV⟩ := P.property
    have he : P = flagOrbit V := Subtype.ext hV.symm
    refine mem_iUnion.mpr ⟨V, ?_⟩
    simpa only [u, mem_preimage, he, flagAction_flagOrbit, inv_mul_cancel] using h1
  obtain ⟨c, hc⟩ := isCompact_univ.elim_finite_subcover u hu hcover
  have he (P : flagSpace n K) : ∃ U ∈ c, flagAction U⁻¹ P ∈ v := by
    obtain ⟨U, hU, hP⟩ := mem_iUnion₂.mp (hc (mem_univ P))
    exact ⟨U, hU, hP⟩
  obtain ⟨U, hU, _⟩ := he (flagOrbit 1)
  exact ⟨c, ⟨U, hU⟩, he⟩

end A3Research

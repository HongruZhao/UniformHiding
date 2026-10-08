import A4.Target

open Filter Set Topology Matrix

namespace A4Research

/-- A positive-definite real matrix remains positive definite under a sufficiently
small perturbation in any fixed symmetric direction. The proof uses compactness
of the unit sphere, without selecting eigenvectors continuously. -/
theorem eventually_posDef_sub_smul {d : ℕ}
    {A B : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosDef) (hB : B.IsHermitian) :
    ∀ᶠ t : ℝ in 𝓝 0, (A - t • B).PosDef := by
  have hcont : Continuous (fun z : ℝ × (Fin d → ℝ) ↦
      z.2 ⬝ᵥ ((A - z.1 • B) *ᵥ z.2)) := by
    unfold dotProduct mulVec
    fun_prop
  have hpos : ∀ᶠ t : ℝ in 𝓝 0, ∀ x ∈ Metric.sphere (0 : Fin d → ℝ) 1,
      0 < x ⬝ᵥ ((A - t • B) *ᵥ x) := by
    apply (isCompact_sphere (0 : Fin d → ℝ) 1).eventually_forall_of_forall_eventually
    intro x hx
    have hx0 : x ≠ 0 := by
      intro heq
      simpa [heq] using hx
    have hbase : 0 < x ⬝ᵥ (A *ᵥ x) := by
      simpa only [star_trivial] using hA.dotProduct_mulVec_pos hx0
    exact hcont.continuousAt.eventually (Ioi_mem_nhds (by simpa using hbase))
  filter_upwards [hpos] with t ht
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (hA.isHermitian.sub (hB.smul (IsSelfAdjoint.all t)))
  intro x hx
  let y : Fin d → ℝ := ‖x‖⁻¹ • x
  have hy : y ∈ Metric.sphere (0 : Fin d → ℝ) 1 :=
    mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hx)
  have hypos := ht y hy
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hscale : y ⬝ᵥ ((A - t • B) *ᵥ y) =
      (‖x‖⁻¹ * ‖x‖⁻¹) * (x ⬝ᵥ ((A - t • B) *ᵥ x)) := by
    simp only [y, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  rw [hscale] at hypos
  simpa only [star_trivial] using
    (mul_pos_iff_of_pos_left (mul_pos (inv_pos.mpr hnorm) (inv_pos.mpr hnorm))).mp hypos

end A4Research

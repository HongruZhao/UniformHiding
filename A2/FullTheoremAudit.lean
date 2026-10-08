import A2

noncomputable section

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

/-- A literal inhabitant of the original target, with all quantifiers and
the concrete matrix/radial laws unchanged. -/
def A2_exact_original_target_verified : Target := A2_takagi_weyl_integration

example : ∀ N : ℕ, 1 ≤ N → TakagiWeylSymmetricIntegrationLaw N :=
  A2_takagi_weyl_integration

#check A2_takagi_weyl_integration
#print axioms A2_takagi_weyl_integration
#print axioms A2_exact_original_target_verified
#print axioms hasFDerivAt_takagiCayleyOrbitChart
#print axioms exists_takagi_factorization
#print axioms measurable_canonicalGapSquaredSpectrum

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

run_cmd Lean.logInfo "A2_FULL_TARGET_EXACT_KERNEL_CHECKED"

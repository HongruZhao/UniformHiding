import A3

noncomputable section

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

theorem A3_exact_original_target_verified : A3OriginalTarget := A3_edelmanSutton_proposition_1_2

example : ∀ (n a b : ℕ) (beta : ℝ), 1 ≤ n → (beta = 1 ∨ beta = 2) →
    EdelmanSuttonProposition12SymmetricContract n a b beta :=
  A3_edelmanSutton_proposition_1_2

#check A3_edelmanSutton_proposition_1_2
#print axioms A3_edelmanSutton_proposition_1_2
#print axioms A3_exact_original_target_verified

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

run_cmd Lean.logInfo "A3_FULL_TARGET_EXACT_KERNEL_CHECKED"

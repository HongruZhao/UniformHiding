import A4.FullTheorem

open scoped BigOperators

/-- The original target written out again, so the final audit checks every
quantifier and both literal probability-moment expressions. -/
theorem MatsumotoPaper.A4_exact_original_target_verified :
    ∀ (d n : Nat) (beta gamma : Real)
      (_hd : 0 < d) (_hn : 0 < n)
      (sigma : MatsumotoPaper.SymPosDef d) (W : MatsumotoPaper.W_d d beta sigma)
      (_hgamma : gamma = beta - ((d : Real) + 1) / 2)
      (_hgap : (n : Real) - 1 < gamma)
      (m : Fin n → MatsumotoPaper.ComplexMatrix d)
      (g : Equiv.Perm (Fin (2 * n))),
      MatsumotoPaper.expectation W (fun w => MatsumotoPaper.T g w.1 m) =
          (2 : Complex) ^ (-(n : Int)) *
            ∑ matching : MatsumotoPaper.PerfectMatching n,
              (((2 * beta) ^ MatsumotoPaper.kappa (g⁻¹ * matching.toPerm) : Real) : Complex) *
                MatsumotoPaper.T matching.toPerm sigma.1 m ∧
        MatsumotoPaper.expectation W
            (fun w => MatsumotoPaper.T g (MatsumotoPaper.SymPosDef.inverse w).1 m) =
          ∑ matching : MatsumotoPaper.PerfectMatching n,
            MatsumotoPaper.wgTilde (g⁻¹ * matching.toPerm) gamma *
              MatsumotoPaper.T matching.toPerm (MatsumotoPaper.SymPosDef.inverse sigma).1 m :=
  MatsumotoPaper.completedMatsumotoTheorem3

#check (MatsumotoPaper.completedMatsumotoTheorem3 : MatsumotoPaper.Target)
#print axioms MatsumotoPaper.W_d.direct_matching_moment
#print axioms MatsumotoPaper.W_d.inverse_matching_moment
#print axioms MatsumotoPaper.completedMatsumotoTheorem3
#print axioms MatsumotoPaper.A4_exact_original_target_verified

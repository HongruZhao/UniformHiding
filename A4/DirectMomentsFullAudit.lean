import A4.DirectMomentsFull

open scoped BigOperators

#check MatsumotoPaper.W_d.direct_matching_moment
#print axioms MatsumotoPaper.pairPartitionEntryShapePolynomial_eq_matching
#print axioms MatsumotoPaper.W_d.direct_pairPartition_moment
#print axioms MatsumotoPaper.W_d.direct_permuted_entry_moment
#print axioms MatsumotoPaper.W_d.direct_matching_moment

/-- The direct conjunct with the exact quantifiers and expressions of the
original A4 target. Inverse-moment completion is a separate obligation. -/
theorem MatsumotoPaper.A4_direct_conjunct :
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
              MatsumotoPaper.T matching.toPerm sigma.1 m := by
  intro d n beta gamma hd hn sigma W hgamma hgap m g
  exact W.direct_matching_moment m g

#print axioms MatsumotoPaper.A4_direct_conjunct

import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16FourthSecantIntegralVanishingFromPointwiseFTC

/-!
# Paper-facing endpoint for the Appendix C fourth secant

The paper displays the top-slot Banach derivative of the third
zero-extended likelihood jet.  The local secant-integral theorem proves the
only delicate `3 -> 4` derivative from the exact COE determinant density.
This file exports that composition under a short equation-facing name.
-/

namespace LogdetLean.GramHafnian.ThreePaper.Verification

open LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-- Appendix C Eq. `hide-fourth-secant`: the third zero-extended jet has the
fourth jet as its derivative at zero in the literal `L1` coordinate space.
The only scientific input is the exact Friedman--Mello A1 density. -/
theorem eq_hide_fourth_secant_from_A1
    {N K : Nat} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K) :
    H16CenteredDirectFourthL1DerivativeAtZero
      h16ExactH5Family_from_friedmanMello1985_A1 hN hboundary := by
  exact
    h16CenteredDirectFourthL1DerivativeAtZero_of_secantIntegralVanishing_exactH5
      h16ExactH5Family_from_friedmanMello1985_A1 hN hboundary
      (h16CenteredFourthLocalSecantIntegralVanishing_proved_exactH5
        h16ExactH5Family_from_friedmanMello1985_A1 hN hboundary)

end

end LogdetLean.GramHafnian.ThreePaper.Verification

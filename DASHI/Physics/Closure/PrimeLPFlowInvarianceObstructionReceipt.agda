module DASHI.Physics.Closure.PrimeLPFlowInvarianceObstructionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

primeLPFlowInvarianceObstructionStatement : String
primeLPFlowInvarianceObstructionStatement =
  "Option 2: exact invariance of prime-LP support under NS flow would make adjacent-only vortex stretching exact and close a tridiagonal enstrophy system, but the nonlinear term generally creates sum/difference frequencies outside the carrier support, so exact commutation/invariance is false or at least unproved."

record PrimeLPFlowInvarianceObstructionReceipt : Setω where
  field
    statement :
      String

    statementIsCanonical :
      statement ≡ primeLPFlowInvarianceObstructionStatement

    primeLPFlowInvarianceRequired :
      Bool

    primeLPFlowInvarianceRequiredIsTrue :
      primeLPFlowInvarianceRequired ≡ true

    adjacentOnlyVortexStretchingWouldBeExact :
      Bool

    adjacentOnlyVortexStretchingWouldBeExactIsTrue :
      adjacentOnlyVortexStretchingWouldBeExact ≡ true

    tridiagonalEnstrophySystemWouldClose :
      Bool

    tridiagonalEnstrophySystemWouldCloseIsTrue :
      tridiagonalEnstrophySystemWouldClose ≡ true

    nonlinearTermGeneratesNewFrequencies :
      Bool

    nonlinearTermGeneratesNewFrequenciesIsTrue :
      nonlinearTermGeneratesNewFrequencies ≡ true

    exactCommutationConstructed :
      Bool

    exactCommutationConstructedIsFalse :
      exactCommutationConstructed ≡ false

    exactPrimeLPSupportInvarianceFalseOrUnproved :
      Bool

    exactPrimeLPSupportInvarianceFalseOrUnprovedIsTrue :
      exactPrimeLPSupportInvarianceFalseOrUnproved ≡ true

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

open PrimeLPFlowInvarianceObstructionReceipt public

canonicalPrimeLPFlowInvarianceObstructionReceipt :
  PrimeLPFlowInvarianceObstructionReceipt
canonicalPrimeLPFlowInvarianceObstructionReceipt =
  record
    { statement =
        primeLPFlowInvarianceObstructionStatement
    ; statementIsCanonical =
        refl
    ; primeLPFlowInvarianceRequired =
        true
    ; primeLPFlowInvarianceRequiredIsTrue =
        refl
    ; adjacentOnlyVortexStretchingWouldBeExact =
        true
    ; adjacentOnlyVortexStretchingWouldBeExactIsTrue =
        refl
    ; tridiagonalEnstrophySystemWouldClose =
        true
    ; tridiagonalEnstrophySystemWouldCloseIsTrue =
        refl
    ; nonlinearTermGeneratesNewFrequencies =
        true
    ; nonlinearTermGeneratesNewFrequenciesIsTrue =
        refl
    ; exactCommutationConstructed =
        false
    ; exactCommutationConstructedIsFalse =
        refl
    ; exactPrimeLPSupportInvarianceFalseOrUnproved =
        true
    ; exactPrimeLPSupportInvarianceFalseOrUnprovedIsTrue =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    }

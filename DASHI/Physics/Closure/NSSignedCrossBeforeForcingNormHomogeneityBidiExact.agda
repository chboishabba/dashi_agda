module DASHI.Physics.Closure.NSSignedCrossBeforeForcingNormHomogeneityBidiExact where

------------------------------------------------------------------------
-- SIGNED CROSS BEFORE FORCING NORM: HOMOGENEITY ROUTE AUDIT
--
-- R289 already formalizes the key degree lesson on the mixed-helicity carrier:
-- quadratic companion cells have degree 2, the Navier--Stokes nonlinear tangent
-- has degree 3, and the physically relevant forcing work has degree 5.
--
-- The current R541 x R573 nested forcing carrier is the same forcing side one
-- level downstream.  Taking its norm-square before pairing with the quadratic
-- companion changes the consumer from a quintic signed cross to a sextic
-- positive object.  Differentiating that sextic object would in turn require a
-- degree-7 nonlinear remainder.  This is a proof-search/homogeneity audit, not
-- an analytic estimate and not a theorem that positive norms are never useful.
--
-- CONSEQUENCE
-- -----------
-- The selected outer Gram ledger remains a valid optional diagnostic/majorant,
-- but it is not promoted to the mandatory R503 path.  R503 itself already says
-- its sole analytic leaf is a cutoff-uniform bound on the exact integrated
-- signed off-diagonal direct resolvent cross.  Therefore preserve the nested
-- commutator structure inside the forcing factor, pair with the quadratic
-- companion, aggregate/cancel, and only then introduce a lossy majorant if the
-- resulting scalar consumer descends through it.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNMixedHelicityQuarticFluxHomogeneityRound289Exact as R289

quadraticCompanionDegree : Nat
quadraticCompanionDegree = R289.mixedCellDegree

nestedForcingDegree : Nat
nestedForcingDegree =
  R289.mixedProductTangentDegree R289.nonlinearModalForcingDegree

signedForcingCompanionCrossDegree : Nat
signedForcingCompanionCrossDegree = nestedForcingDegree + quadraticCompanionDegree

forcingNormSquareDegree : Nat
forcingNormSquareDegree = nestedForcingDegree + nestedForcingDegree

nestedForcingNonlinearTangentDegree : Nat
nestedForcingNonlinearTangentDegree = nestedForcingDegree + 1

forcingNormSquareNonlinearTangentDegree : Nat
forcingNormSquareNonlinearTangentDegree =
  nestedForcingDegree + nestedForcingNonlinearTangentDegree

quadraticCompanionIsDegreeTwo : quadraticCompanionDegree ≡ 2
quadraticCompanionIsDegreeTwo = refl

nestedForcingIsDegreeThree : nestedForcingDegree ≡ 3
nestedForcingIsDegreeThree = refl

signedCrossIsDegreeFive : signedForcingCompanionCrossDegree ≡ 5
signedCrossIsDegreeFive = refl

forcingNormSquareIsDegreeSix : forcingNormSquareDegree ≡ 6
forcingNormSquareIsDegreeSix = refl

forcingNormSquareNonlinearTangentIsDegreeSeven :
  forcingNormSquareNonlinearTangentDegree ≡ 7
forcingNormSquareNonlinearTangentIsDegreeSeven = refl

------------------------------------------------------------------------
-- Route boundary.
------------------------------------------------------------------------

record SignedCrossBeforeForcingNormBoundary : Set where
  constructor signed-cross-before-forcing-norm-boundary
  field
    signedCrossMatchesLowerHomogeneityConsumer : Bool
    forcingNormSquareRaisesDegreeBeforeConsumer : Bool
    differentiatingForcingNormOpensHigherDegreeRemainder : Bool
    outerGramRouteStillValidOptionalMajorant : Bool
    outerGramRouteMandatoryForR503 : Bool
    signedCrossShouldRemainFineCarrierUntilPairing : Bool
    homogeneityAuditItselfPaysR503 : Bool

canonicalSignedCrossBeforeForcingNormBoundary :
  SignedCrossBeforeForcingNormBoundary
canonicalSignedCrossBeforeForcingNormBoundary =
  signed-cross-before-forcing-norm-boundary
    true true true true false true false

outerGramRouteMandatoryForR503IsFalse :
  SignedCrossBeforeForcingNormBoundary.outerGramRouteMandatoryForR503
    canonicalSignedCrossBeforeForcingNormBoundary ≡ false
outerGramRouteMandatoryForR503IsFalse = refl

signedCrossShouldRemainFineCarrierUntilPairingIsTrue :
  SignedCrossBeforeForcingNormBoundary.signedCrossShouldRemainFineCarrierUntilPairing
    canonicalSignedCrossBeforeForcingNormBoundary ≡ true
signedCrossShouldRemainFineCarrierUntilPairingIsTrue = refl

homogeneityAuditDoesNotPayR503 :
  SignedCrossBeforeForcingNormBoundary.homogeneityAuditItselfPaysR503
    canonicalSignedCrossBeforeForcingNormBoundary ≡ false
homogeneityAuditDoesNotPayR503 = refl

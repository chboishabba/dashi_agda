module DASHI.Physics.Closure.NSGlobalFourAlternativeMissionExact where

------------------------------------------------------------------------
-- GLOBAL NAVIER--STOKES FOUR-ALTERNATIVE MISSION
--
-- Source authority: Charles L. Fefferman, "Existence and Smoothness of the
-- Navier--Stokes Equation", Clay Mathematics Institute Millennium Problem
-- description (2000). DOI not assigned to the official problem description.
--
-- This owner is deliberately STRONGER than the Clay award criterion:
-- official Clay mathematical resolution needs any one of A/B/C/D; DASHI's
-- global research mission independently tracks A AND B AND C AND D.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNPeriodicNavierStokesSubmissionTheoremExact as BSurface
import DASHI.Physics.Closure.NSTriadKNClayForcedBreakdownFormulationRound523Exact as CD
import DASHI.Physics.Closure.NSTriadKNCanonicalDirectLeafAFrontierRound592Exact as LeafA
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as Cut
import DASHI.Physics.Closure.NSFirstImplementationPriorityLedgerExact as Priority

data NSAlternative : Set where
  A-euclidean-unforced-global : NSAlternative
  B-periodic-unforced-global : NSAlternative
  C-euclidean-forced-breakdown : NSAlternative
  D-periodic-forced-breakdown : NSAlternative

data NSDomain : Set where
  euclideanR3 : NSDomain
  periodicT3 : NSDomain

data NSForcingRegime : Set where
  unforced : NSForcingRegime
  smoothForced : NSForcingRegime

domainOf : NSAlternative → NSDomain
domainOf A-euclidean-unforced-global = euclideanR3
domainOf B-periodic-unforced-global = periodicT3
domainOf C-euclidean-forced-breakdown = euclideanR3
domainOf D-periodic-forced-breakdown = periodicT3

forcingOf : NSAlternative → NSForcingRegime
forcingOf A-euclidean-unforced-global = unforced
forcingOf B-periodic-unforced-global = unforced
forcingOf C-euclidean-forced-breakdown = smoothForced
forcingOf D-periodic-forced-breakdown = smoothForced

data StatementAuthority : Set where
  feffermanOfficialStatement : StatementAuthority
  dashiTypedReconstruction : StatementAuthority
  externalReleasedFormalProofSource : StatementAuthority

data InternalPaymentStatus : Set where
  internallyOpen : InternalPaymentStatus
  internallyPaid : InternalPaymentStatus

record AlternativeMissionStatus : Set where
  constructor alternative-mission-status
  field
    alternative : NSAlternative
    authority : StatementAuthority
    sourceStatementAligned : Bool
    internalPayment : InternalPaymentStatus

open AlternativeMissionStatus public

statusA : AlternativeMissionStatus
statusA = alternative-mission-status
  A-euclidean-unforced-global feffermanOfficialStatement true internallyOpen

statusB : AlternativeMissionStatus
statusB = alternative-mission-status
  B-periodic-unforced-global dashiTypedReconstruction
  BSurface.submissionTheoremStatementConstructed internallyOpen

-- Public 2026-09-08 C/D formal-proof release is source evidence only here.
-- External theorem -> DASHI same-object payment is a separate obligation.
statusC : AlternativeMissionStatus
statusC = alternative-mission-status
  C-euclidean-forced-breakdown externalReleasedFormalProofSource true internallyOpen

statusD : AlternativeMissionStatus
statusD = alternative-mission-status
  D-periodic-forced-breakdown externalReleasedFormalProofSource true internallyOpen

externalCDReleaseDate : String
externalCDReleaseDate = "2026-09-08"

cMapsToRound523 : CD.ClayBreakdownAlternative523
cMapsToRound523 = CD.clayAlternativeC523

dMapsToRound523 : CD.ClayBreakdownAlternative523
dMapsToRound523 = CD.clayAlternativeD523

unforcedLeafAIsCanonicalSingleR503Budget : Bool
unforcedLeafAIsCanonicalSingleR503Budget =
  LeafA.round592CanonicalLeafAIsSingleDirectOffDiagonalBudget

unforcedLeafAPaid : Bool
unforcedLeafAPaid = LeafA.round592CanonicalLeafAClosed

unforcedLeafBIndependent : Bool
unforcedLeafBIndependent = true

unforcedLeafBPaid : Bool
unforcedLeafBPaid = Cut.round504CriticalProductionSliceClosed

data PaymentA : Set where
data PaymentB : Set where
data PaymentC : Set where
data PaymentD : Set where

record GlobalFourAlternativeCompletion : Set where
  constructor global-four-alternative-completion
  field
    paymentA : PaymentA
    paymentB : PaymentB
    paymentC : PaymentC
    paymentD : PaymentD

open GlobalFourAlternativeCompletion public

data AnyOneClayAlternativePayment : Set where
  paidA : PaymentA → AnyOneClayAlternativePayment
  paidB : PaymentB → AnyOneClayAlternativePayment
  paidC : PaymentC → AnyOneClayAlternativePayment
  paidD : PaymentD → AnyOneClayAlternativePayment

allFourImpliesAtLeastOneClayAlternative :
  GlobalFourAlternativeCompletion → AnyOneClayAlternativePayment
allFourImpliesAtLeastOneClayAlternative completion = paidA (paymentA completion)

data OneAlternativeAutomaticallyPaysAllFour : Set where
oneAlternativeDoesNotAutomaticallyPayAllFour :
  OneAlternativeAutomaticallyPaysAllFour → ⊥
oneAlternativeDoesNotAutomaticallyPayAllFour ()

data ForcedPaysUnforced : Set where
data PeriodicPaysEuclidean : Set where
data ExternalSourcePaysInternalProof : Set where
data TimestampPaysMathematics : Set where

forcedDoesNotPayUnforced : ForcedPaysUnforced → ⊥
forcedDoesNotPayUnforced ()
periodicDoesNotPayEuclidean : PeriodicPaysEuclidean → ⊥
periodicDoesNotPayEuclidean ()
externalSourceDoesNotPayInternalProof : ExternalSourcePaysInternalProof → ⊥
externalSourceDoesNotPayInternalProof ()
timestampDoesNotPayMathematics : TimestampPaysMathematics → ⊥
timestampDoesNotPayMathematics ()

data GlobalNSResidual : Set where
  proveUnforcedLeafA : GlobalNSResidual
  proveUnforcedLeafB : GlobalNSResidual
  weldPeriodicBToCompleteSubmission : GlobalNSResidual
  transportPeriodicToEuclideanA : GlobalNSResidual
  independentlyReconstructExternalC : GlobalNSResidual
  independentlyReconstructExternalD : GlobalNSResidual
  globalAllFourComplete : GlobalNSResidual

currentFirstIndependentUnforcedResidual : GlobalNSResidual
currentFirstIndependentUnforcedResidual = proveUnforcedLeafA
currentFirstExternalReconstructionResidual : GlobalNSResidual
currentFirstExternalReconstructionResidual = independentlyReconstructExternalC

roundGlobalFourAlternativeMissionImplemented : Bool
roundGlobalFourAlternativeMissionImplemented = true
roundGlobalAllFourInternallyPaid : Bool
roundGlobalAllFourInternallyPaid = false
roundOfficialClayAnyOneCriterionSeparatedFromAllFourMission : Bool
roundOfficialClayAnyOneCriterionSeparatedFromAllFourMission = true
roundPriorityChronologyDoesNotPromoteNS : Bool
roundPriorityChronologyDoesNotPromoteNS =
  Priority.r503AnalyticPaymentWasAlreadyProvedByThatConsumerCommit

roundGlobalFourAlternativeMissionImplementedIsTrue :
  roundGlobalFourAlternativeMissionImplemented ≡ true
roundGlobalFourAlternativeMissionImplementedIsTrue = refl
roundGlobalAllFourInternallyPaidIsFalse :
  roundGlobalAllFourInternallyPaid ≡ false
roundGlobalAllFourInternallyPaidIsFalse = refl
roundOfficialClayAnyOneCriterionSeparatedFromAllFourMissionIsTrue :
  roundOfficialClayAnyOneCriterionSeparatedFromAllFourMission ≡ true
roundOfficialClayAnyOneCriterionSeparatedFromAllFourMissionIsTrue = refl
roundPriorityChronologyDoesNotPromoteNSIsFalse :
  roundPriorityChronologyDoesNotPromoteNS ≡ false
roundPriorityChronologyDoesNotPromoteNSIsFalse = refl

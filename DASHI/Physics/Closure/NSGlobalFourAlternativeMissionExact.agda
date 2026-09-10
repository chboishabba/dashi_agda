module DASHI.Physics.Closure.NSGlobalFourAlternativeMissionExact where

------------------------------------------------------------------------
-- GLOBAL NAVIER--STOKES FOUR-ALTERNATIVE MISSION
--
-- Source authority: Charles L. Fefferman, "Existence and Smoothness of the
-- Navier--Stokes Equation", Clay Mathematics Institute Millennium Problem
-- description (2000). DOI not assigned to the official problem description.
--
-- This owner is deliberately STRONGER than the Clay award criterion:
--
--   official Clay mathematical resolution: any one of A/B/C/D suffices;
--   DASHI global mission: independently track/pay A AND B AND C AND D.
--
-- A/B are unforced global-regularity alternatives on R^3/T^3.
-- C/D are forced-breakdown alternatives on R^3/T^3.
-- Constructor distinction prevents a forced witness from paying an unforced
-- theorem, or a periodic theorem from silently paying the Euclidean theorem.
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

------------------------------------------------------------------------
-- Four source-distinct alternatives.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Source/status is not mathematical payment.
------------------------------------------------------------------------

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

-- Public 2026-09-08 C/D release status is recorded only as external source
-- evidence. Exact external theorem -> DASHI same-object proof transport is a
-- separate obligation and is NOT represented by internallyPaid.
statusC : AlternativeMissionStatus
statusC = alternative-mission-status
  C-euclidean-forced-breakdown externalReleasedFormalProofSource true internallyOpen

statusD : AlternativeMissionStatus
statusD = alternative-mission-status
  D-periodic-forced-breakdown externalReleasedFormalProofSource true internallyOpen

externalCDReleaseDate : String
externalCDReleaseDate = "2026-09-08"

------------------------------------------------------------------------
-- Source-exact C/D mapping to the existing Round523 formulation.
------------------------------------------------------------------------

cMapsToRound523 : CD.ClayBreakdownAlternative523
cMapsToRound523 = CD.clayAlternativeC523

dMapsToRound523 : CD.ClayBreakdownAlternative523
dMapsToRound523 = CD.clayAlternativeD523

------------------------------------------------------------------------
-- A/B independent research lane.
--
-- The current exact periodic/live carrier reaches the two-leaf R504 cutset.
-- R592 shrinks leaf A to the one R503 cutoff-uniform direct-companion bound.
-- Leaf B remains the phase-sensitive critical-production slice.  This is a
-- concrete producer architecture for unforced regularity; it is not payment.
------------------------------------------------------------------------

unforcedLeafAIsCanonicalSingleR503Budget : Bool
unforcedLeafAIsCanonicalSingleR503Budget =
  LeafA.round592CanonicalLeafAIsSingleDirectOffDiagonalBudget

unforcedLeafAPaid : Bool
unforcedLeafAPaid = LeafA.round592CanonicalLeafAClosed

unforcedLeafBIndependent : Bool
unforcedLeafBIndependent = true

unforcedLeafBPaid : Bool
unforcedLeafBPaid = Cut.round504CriticalProductionSliceClosed

------------------------------------------------------------------------
-- Typed payment tokens. There are deliberately no canonical constructors here:
-- a downstream proof must supply the exact alternative-specific receipt.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Clay's logical criterion versus the stronger global mission.
------------------------------------------------------------------------

data AnyOneClayAlternativePayment : Set where
  paidA : PaymentA → AnyOneClayAlternativePayment
  paidB : PaymentB → AnyOneClayAlternativePayment
  paidC : PaymentC → AnyOneClayAlternativePayment
  paidD : PaymentD → AnyOneClayAlternativePayment

allFourImpliesAtLeastOneClayAlternative :
  GlobalFourAlternativeCompletion → AnyOneClayAlternativePayment
allFourImpliesAtLeastOneClayAlternative completion = paidA (paymentA completion)

-- Converse is intentionally unavailable: paying one official Clay alternative
-- does not complete DASHI's stronger all-four mission.
data OneAlternativeAutomaticallyPaysAllFour : Set where

oneAlternativeDoesNotAutomaticallyPayAllFour :
  OneAlternativeAutomaticallyPaysAllFour → ⊥
oneAlternativeDoesNotAutomaticallyPayAllFour ()

------------------------------------------------------------------------
-- WrongType firewalls between alternatives.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Current global mission frontier.
------------------------------------------------------------------------

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

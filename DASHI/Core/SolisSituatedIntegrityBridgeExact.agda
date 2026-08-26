module DASHI.Core.SolisSituatedIntegrityBridgeExact where

------------------------------------------------------------------------
-- SOLIS / SCN SITUATED-INTEGRITY BRIDGE
--
-- Provenance is deliberately separated from theorem authority.
--
-- Project/concept provenance recovered in the supplied notes:
--   * Instagram handle: @solishood
--   * conceptual bundle: system sensitivity, systemic-integrity checking,
--     "sacred data" / syntax-checker framing, psybernetic dissonance;
--   * archive: chboishabba/dashiTRADE/ignore.TRADER_CANTEXT.md,
--     locally reported around lines 61211--62174, including the 0.5 threshold,
--     AutisticSignal[x] := Check[SystemicIntegrity[x]], and qPARA/collapse-risk
--     handling.
--
-- Historical DASHI substrate:
--   commit 2f45a6da102cf582503281ace8c508031f17fdbb contains the removed
--   Cognition integrity/synchrony/ternary modules.  Those files are ancestors
--   of the present formal vocabulary, not a standalone historical SCN module.
--
-- None of this provenance establishes a peer-reviewed autism mechanism.
-- The exact content below is only control algebra plus a synthetic situated
-- observer specimen.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.DeclaredRealizedIntegrityResidualExact as Integrity
import DASHI.Core.ExceptionalSignalLatticeExact as Exception
import DASHI.Core.DecimalResidualRefinementExact as Decimal

------------------------------------------------------------------------
-- Bounded provenance receipt.
------------------------------------------------------------------------

record SolisProjectSource : Set where
  constructor solisProjectSource
  field
    sourceHandle : String
    platform : String
    archiveRepository : String
    archiveLocation : String
    historicalCommit : String
    sourceRole : String
    peerReviewedMechanismAuthority : Bool
    externalIdentityIndependentlyVerifiedHere : Bool

open SolisProjectSource public

canonicalSolisProjectSource : SolisProjectSource
canonicalSolisProjectSource = solisProjectSource
  "@solishood"
  "Instagram (as identified in supplied project notes)"
  "chboishabba/dashiTRADE"
  "ignore.TRADER_CANTEXT.md:61211-62174 (reported local archive range)"
  "2f45a6da102cf582503281ace8c508031f17fdbb"
  "concept/project provenance for Solis Communicator Notation and system-sensitivity framing"
  false
  false

------------------------------------------------------------------------
-- Exact 0, 1/2, 1 control grid.
--
-- Integrity and incoherence are complements.  The archive's 1/2 threshold is
-- implemented exactly on the smallest finite grid that can represent it.
------------------------------------------------------------------------

data HalfGrid : Set where
  zeroScore halfScore oneScore : HalfGrid

complementScore : HalfGrid → HalfGrid
complementScore zeroScore = oneScore
complementScore halfScore = halfScore
complementScore oneScore = zeroScore

atOrAboveHalf : HalfGrid → Bool
atOrAboveHalf zeroScore = false
atOrAboveHalf halfScore = true
atOrAboveHalf oneScore = true

atOrBelowHalf : HalfGrid → Bool
atOrBelowHalf zeroScore = true
atOrBelowHalf halfScore = true
atOrBelowHalf oneScore = false

data SCNDecision : Set where
  continueDecision flagAndBifurcateDecision : SCNDecision

scnDecisionFromIncoherence : HalfGrid → SCNDecision
scnDecisionFromIncoherence zeroScore = continueDecision
scnDecisionFromIncoherence halfScore = flagAndBifurcateDecision
scnDecisionFromIncoherence oneScore = flagAndBifurcateDecision

scnFlagIndicator : SCNDecision → Bool
scnFlagIndicator continueDecision = false
scnFlagIndicator flagAndBifurcateDecision = true

SCNFromIntegrity : HalfGrid → SCNDecision
SCNFromIntegrity integrity =
  scnDecisionFromIncoherence (complementScore integrity)

scnThresholdSoundness :
  (integrity : HalfGrid) →
  scnFlagIndicator (SCNFromIntegrity integrity) ≡ atOrBelowHalf integrity
scnThresholdSoundness zeroScore = refl
scnThresholdSoundness halfScore = refl
scnThresholdSoundness oneScore = refl

------------------------------------------------------------------------
-- qPARA / exceptional-signal bridge.
--
-- #620 already owns qMETA/qVOID/qPARA/sVOID/sPARA as a typed exception lattice.
-- Reuse it: paradox-state signaling has quarantine priority over ordinary SCN
-- bifurcation.  Absence/void and paradox are not collapsed.
------------------------------------------------------------------------

data SCNAction : Set where
  continueAction bifurcateAction quarantineAction : SCNAction

scnAction : Exception.ExceptionalSignal → HalfGrid → SCNAction
scnAction (Exception.exceptionalSignal mode Exception.paradoxState) integrity =
  quarantineAction
scnAction (Exception.exceptionalSignal mode Exception.metaBoundary) integrity
  with SCNFromIntegrity integrity
... | continueDecision = continueAction
... | flagAndBifurcateDecision = bifurcateAction
scnAction (Exception.exceptionalSignal mode Exception.voidState) integrity
  with SCNFromIntegrity integrity
... | continueDecision = continueAction
... | flagAndBifurcateDecision = bifurcateAction

qPARAQuarantinesAtAnyIntegrity :
  (integrity : HalfGrid) →
  scnAction Exception.qPARA integrity ≡ quarantineAction
qPARAQuarantinesAtAnyIntegrity integrity = refl

qVOIDDoesNotAutoBecomeParadox :
  scnAction Exception.qVOID oneScore ≡ continueAction
qVOIDDoesNotAutoBecomeParadox = refl

------------------------------------------------------------------------
-- Situated social-ecology instantiation.
--
-- The generic declared/realized owner gives the same person and same nominal
-- public-access declaration two different realised affordance residuals across
-- environments.  Map only that synthetic residual to an integrity score:
-- aligned -> high integrity; mismatch -> low integrity.
--
-- This is a mathematical witness of observer non-descent.  It is not evidence
-- that autistic distress is a calibrated detector of external system failure.
------------------------------------------------------------------------

integrityFromResidual : Integrity.ResidualStatus → HalfGrid
integrityFromResidual Integrity.declaredRealizedAligned = oneScore
integrityFromResidual Integrity.declaredRealizedMismatch = zeroScore

situatedIntegrityScore : Integrity.PublicEnvironment → HalfGrid
situatedIntegrityScore environment =
  integrityFromResidual
    (Integrity.integrityResidual
      Integrity.publicAccessObserver
      Integrity.canonicalPerson
      environment)

situatedSCNAction : Integrity.PublicEnvironment → SCNAction
situatedSCNAction environment =
  scnAction Exception.qMETA (situatedIntegrityScore environment)

thirdPlaceContinues :
  situatedSCNAction Integrity.lowDemandThirdPlace ≡ continueAction
thirdPlaceContinues = refl

restrictedSpaceBifurcates :
  situatedSCNAction Integrity.highDemandRestrictedSpace ≡ bifurcateAction
restrictedSpaceBifurcates = refl

sameDeclaredAccessButDifferentSCNAction :
  situatedSCNAction Integrity.lowDemandThirdPlace
  ≡ situatedSCNAction Integrity.highDemandRestrictedSpace →
  ⊥
sameDeclaredAccessButDifferentSCNAction ()

------------------------------------------------------------------------
-- #620 residual-role boundary.
--
-- The decimal complement residual and the declared/realized integrity residual
-- can be structurally analogous while remaining different typed objects.
------------------------------------------------------------------------

data ResidualRole : Set where
  decimalComplementResidual situatedIntegrityResidual : ResidualRole

residualRolesAreDistinct :
  decimalComplementResidual ≡ situatedIntegrityResidual → ⊥
residualRolesAreDistinct ()

stageEightDecimalComplementIsOne :
  Decimal.completedGapNumeratorOverNine Decimal.d8 ≡ 1
stageEightDecimalComplementIsOne = refl

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record SolisSituatedBoundary : Set where
  constructor solis-situated-boundary
  field
    solishoodProjectAttributionRecorded : Bool
    solishoodProjectAttributionRecordedIsTrue :
      solishoodProjectAttributionRecorded ≡ true
    exactHalfThresholdInstalled : Bool
    exactHalfThresholdInstalledIsTrue : exactHalfThresholdInstalled ≡ true
    qPARAReusesExceptionalSignalOwner : Bool
    qPARAReusesExceptionalSignalOwnerIsTrue :
      qPARAReusesExceptionalSignalOwner ≡ true
    declaredRealizedMismatchRepresented : Bool
    declaredRealizedMismatchRepresentedIsTrue :
      declaredRealizedMismatchRepresented ≡ true
    empiricalAutismIntegrityFunctionalInstalled : Bool
    empiricalAutismIntegrityFunctionalInstalledIsFalse :
      empiricalAutismIntegrityFunctionalInstalled ≡ false
    distressProvesExternalSystemFailure : Bool
    distressProvesExternalSystemFailureIsFalse :
      distressProvesExternalSystemFailure ≡ false
    decimalResidualIsSituatedIntegrityResidual : Bool
    decimalResidualIsSituatedIntegrityResidualIsFalse :
      decimalResidualIsSituatedIntegrityResidual ≡ false
    instagramIdentityIndependentlyVerifiedByThisModule : Bool
    instagramIdentityIndependentlyVerifiedByThisModuleIsFalse :
      instagramIdentityIndependentlyVerifiedByThisModule ≡ false

canonicalSolisSituatedBoundary : SolisSituatedBoundary
canonicalSolisSituatedBoundary =
  solis-situated-boundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

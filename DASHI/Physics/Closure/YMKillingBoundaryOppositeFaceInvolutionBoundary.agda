module DASHI.Physics.Closure.YMKillingBoundaryOppositeFaceInvolutionBoundary where

-- Child boundary for the finite YM Killing/full-degree boundary convention.
--
-- This narrows YM-1's flux-cancellation route to the specific finite
-- opposing-face mechanism:
--
--   finite BT boundary face carrier
--   total opposite-face involution
--   oriented normal reversal
--   full-degree/Killing weight preservation
--   gauge compatibility of the face pairing
--   dependency into boundary flux cancellation
--
-- The module is a proof-contract receipt only.  It records the exact rows a
-- future proof must discharge; it does not construct the face set, does not
-- prove the involution or weight theorem, does not prove flux cancellation,
-- does not prove self-adjointness, and keeps YM Clay / terminal promotion
-- false.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMAdmissibleBTBoundaryConventionBoundary
  as Admissible
import DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessDomainContract
  as DomainContract
import DASHI.Physics.Closure.YMKillingBoundaryFluxCancellationBoundary
  as Flux

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Opposite-face vocabulary.

data YMKillingBoundaryOppositeFaceStatus : Set where
  oppositeFaceInvolutionBoundaryRecordedProofStillOpen :
    YMKillingBoundaryOppositeFaceStatus

data FiniteBTBoundaryFaceCarrier : Set where
  orientedInteriorWallFace :
    FiniteBTBoundaryFaceCarrier

  orientedExteriorKillingFace :
    FiniteBTBoundaryFaceCarrier

  gaugeOrbitWallFace :
    FiniteBTBoundaryFaceCarrier

  quotientRepresentativeWallFace :
    FiniteBTBoundaryFaceCarrier

canonicalFiniteBTBoundaryFaceCarriers :
  List FiniteBTBoundaryFaceCarrier
canonicalFiniteBTBoundaryFaceCarriers =
  orientedInteriorWallFace
  ∷ orientedExteriorKillingFace
  ∷ gaugeOrbitWallFace
  ∷ quotientRepresentativeWallFace
  ∷ []

data OppositeFaceInvolutionMechanism : Set where
  finiteBoundaryFaceSetChosen :
    OppositeFaceInvolutionMechanism

  oppositeFaceMapTotalOnBoundaryFaces :
    OppositeFaceInvolutionMechanism

  oppositeFaceMapSquaresToIdentity :
    OppositeFaceInvolutionMechanism

  orientedNormalReversesUnderOpposite :
    OppositeFaceInvolutionMechanism

  fullDegreeKillingWeightPreserved :
    OppositeFaceInvolutionMechanism

  localGaugeRepresentationWeightPreserved :
    OppositeFaceInvolutionMechanism

  finiteGaugeActionCommutesWithOpposite :
    OppositeFaceInvolutionMechanism

  pairedFluxTermsFeedCancellation :
    OppositeFaceInvolutionMechanism

canonicalOppositeFaceInvolutionMechanisms :
  List OppositeFaceInvolutionMechanism
canonicalOppositeFaceInvolutionMechanisms =
  finiteBoundaryFaceSetChosen
  ∷ oppositeFaceMapTotalOnBoundaryFaces
  ∷ oppositeFaceMapSquaresToIdentity
  ∷ orientedNormalReversesUnderOpposite
  ∷ fullDegreeKillingWeightPreserved
  ∷ localGaugeRepresentationWeightPreserved
  ∷ finiteGaugeActionCommutesWithOpposite
  ∷ pairedFluxTermsFeedCancellation
  ∷ []

data OppositeFaceInvolutionDependency : Set where
  consumesFullDegreeKillingConvention :
    OppositeFaceInvolutionDependency

  consumesKillingBoundaryDomainContract :
    OppositeFaceInvolutionDependency

  feedsKillingBoundaryFluxCancellation :
    OppositeFaceInvolutionDependency

  feedsFiniteHodgeIBPBoundaryResidualPairing :
    OppositeFaceInvolutionDependency

  feedsGaugeDomainPreservationOnlyAfterCompatibility :
    OppositeFaceInvolutionDependency

  feedsSelfAdjointnessOnlyThroughFluxBoundary :
    OppositeFaceInvolutionDependency

  keepsHamiltonianDominationSeparate :
    OppositeFaceInvolutionDependency

  keepsOSTransferAndClayPromotionSeparate :
    OppositeFaceInvolutionDependency

canonicalOppositeFaceInvolutionDependencies :
  List OppositeFaceInvolutionDependency
canonicalOppositeFaceInvolutionDependencies =
  consumesFullDegreeKillingConvention
  ∷ consumesKillingBoundaryDomainContract
  ∷ feedsKillingBoundaryFluxCancellation
  ∷ feedsFiniteHodgeIBPBoundaryResidualPairing
  ∷ feedsGaugeDomainPreservationOnlyAfterCompatibility
  ∷ feedsSelfAdjointnessOnlyThroughFluxBoundary
  ∷ keepsHamiltonianDominationSeparate
  ∷ keepsOSTransferAndClayPromotionSeparate
  ∷ []

data OppositeFaceInvolutionObligation : Set where
  constructFiniteBTBoundaryFaceSet :
    OppositeFaceInvolutionObligation

  defineOppositeFaceMapOnEveryBoundaryFace :
    OppositeFaceInvolutionObligation

  proveOppositeFaceMapIsTotal :
    OppositeFaceInvolutionObligation

  proveOppositeFaceMapIsInvolutive :
    OppositeFaceInvolutionObligation

  proveOrientationNormalReversal :
    OppositeFaceInvolutionObligation

  proveFullDegreeKillingWeightPreservation :
    OppositeFaceInvolutionObligation

  proveLocalGaugeWeightPreservation :
    OppositeFaceInvolutionObligation

  proveGaugeActionPreservesOppositeFacePairing :
    OppositeFaceInvolutionObligation

  proveOrientationSignCancellationForPairedFlux :
    OppositeFaceInvolutionObligation

  routeIntoKillingBoundaryFluxCancellation :
    OppositeFaceInvolutionObligation

  rejectInducedBallUnpairedBoundaryFaces :
    OppositeFaceInvolutionObligation

  keepSelfAdjointDominationAndOSPromotionSeparate :
    OppositeFaceInvolutionObligation

canonicalOppositeFaceInvolutionObligations :
  List OppositeFaceInvolutionObligation
canonicalOppositeFaceInvolutionObligations =
  constructFiniteBTBoundaryFaceSet
  ∷ defineOppositeFaceMapOnEveryBoundaryFace
  ∷ proveOppositeFaceMapIsTotal
  ∷ proveOppositeFaceMapIsInvolutive
  ∷ proveOrientationNormalReversal
  ∷ proveFullDegreeKillingWeightPreservation
  ∷ proveLocalGaugeWeightPreservation
  ∷ proveGaugeActionPreservesOppositeFacePairing
  ∷ proveOrientationSignCancellationForPairedFlux
  ∷ routeIntoKillingBoundaryFluxCancellation
  ∷ rejectInducedBallUnpairedBoundaryFaces
  ∷ keepSelfAdjointDominationAndOSPromotionSeparate
  ∷ []

data OppositeFaceInvolutionBlocker : Set where
  missingFiniteBTBoundaryFaceSetConstruction :
    OppositeFaceInvolutionBlocker

  missingOppositeFaceMapDefinition :
    OppositeFaceInvolutionBlocker

  missingOppositeFaceInvolutionTotality :
    OppositeFaceInvolutionBlocker

  missingOppositeFaceInvolutiveProof :
    OppositeFaceInvolutionBlocker

  missingFullDegreeKillingWeightPreservationProof :
    OppositeFaceInvolutionBlocker

  missingLocalGaugeWeightPreservationProof :
    OppositeFaceInvolutionBlocker

  missingOrientationSignCancellationProof :
    OppositeFaceInvolutionBlocker

  missingGaugeCompatibilityProof :
    OppositeFaceInvolutionBlocker

  missingFluxCancellationFeedThroughProof :
    OppositeFaceInvolutionBlocker

  inducedBallFacesRemainUnpairedAndRejected :
    OppositeFaceInvolutionBlocker

  missingSelfAdjointnessDomainFeedThrough :
    OppositeFaceInvolutionBlocker

  missingYMClayAuthorityToken :
    OppositeFaceInvolutionBlocker

canonicalOppositeFaceInvolutionBlockers :
  List OppositeFaceInvolutionBlocker
canonicalOppositeFaceInvolutionBlockers =
  missingFiniteBTBoundaryFaceSetConstruction
  ∷ missingOppositeFaceMapDefinition
  ∷ missingOppositeFaceInvolutionTotality
  ∷ missingOppositeFaceInvolutiveProof
  ∷ missingFullDegreeKillingWeightPreservationProof
  ∷ missingLocalGaugeWeightPreservationProof
  ∷ missingOrientationSignCancellationProof
  ∷ missingGaugeCompatibilityProof
  ∷ missingFluxCancellationFeedThroughProof
  ∷ inducedBallFacesRemainUnpairedAndRejected
  ∷ missingSelfAdjointnessDomainFeedThrough
  ∷ missingYMClayAuthorityToken
  ∷ []

record OppositeFaceInvolutionObligationRow : Set where
  field
    obligation :
      OppositeFaceInvolutionObligation

    label :
      String

    contractText :
      String

    provedHere :
      Bool

    provedHereIsFalse :
      provedHere ≡ false

open OppositeFaceInvolutionObligationRow public

mkOppositeFaceInvolutionObligationRow :
  OppositeFaceInvolutionObligation →
  String →
  String →
  OppositeFaceInvolutionObligationRow
mkOppositeFaceInvolutionObligationRow obligation label contractText =
  record
    { obligation =
        obligation
    ; label =
        label
    ; contractText =
        contractText
    ; provedHere =
        false
    ; provedHereIsFalse =
        refl
    }

canonicalOppositeFaceInvolutionObligationRows :
  List OppositeFaceInvolutionObligationRow
canonicalOppositeFaceInvolutionObligationRows =
  mkOppositeFaceInvolutionObligationRow
    constructFiniteBTBoundaryFaceSet
    "finite BT face set"
    "Construct the oriented finite BT boundary face carrier used by the Killing/full-degree Hamiltonian domain."
  ∷ mkOppositeFaceInvolutionObligationRow
    defineOppositeFaceMapOnEveryBoundaryFace
    "opposite map"
    "Define the opposite-face map on every admissible boundary face, including exterior Killing faces and gauge-orbit faces."
  ∷ mkOppositeFaceInvolutionObligationRow
    proveOppositeFaceMapIsTotal
    "totality"
    "Prove every admissible finite BT boundary face has a paired opposite face inside the full-degree/Killing boundary convention."
  ∷ mkOppositeFaceInvolutionObligationRow
    proveOppositeFaceMapIsInvolutive
    "involution"
    "Prove opposite(opposite(F)) = F on the finite BT boundary face set."
  ∷ mkOppositeFaceInvolutionObligationRow
    proveOrientationNormalReversal
    "orientation reversal"
    "Prove the outward normal orientation changes sign under the opposite-face map."
  ∷ mkOppositeFaceInvolutionObligationRow
    proveFullDegreeKillingWeightPreservation
    "Killing weight"
    "Prove the opposite-face map preserves full-degree/Killing boundary weights inherited from the ambient BT building."
  ∷ mkOppositeFaceInvolutionObligationRow
    proveLocalGaugeWeightPreservation
    "gauge weight"
    "Prove local gauge representation weights are preserved across opposite faces."
  ∷ mkOppositeFaceInvolutionObligationRow
    proveGaugeActionPreservesOppositeFacePairing
    "gauge compatibility"
    "Prove finite gauge transformations commute with the opposite-face pairing up to quotient representative equivalence."
  ∷ mkOppositeFaceInvolutionObligationRow
    proveOrientationSignCancellationForPairedFlux
    "flux signs"
    "Prove the paired opposite faces contribute equal-weight, opposite-sign boundary flux terms."
  ∷ mkOppositeFaceInvolutionObligationRow
    routeIntoKillingBoundaryFluxCancellation
    "flux feed"
    "Feed totality, involutivity, weight preservation, orientation reversal, and gauge compatibility into the flux-cancellation boundary."
  ∷ mkOppositeFaceInvolutionObligationRow
    rejectInducedBallUnpairedBoundaryFaces
    "induced exclusion"
    "Keep induced-ball exterior faces rejected because they may not admit full-degree opposite partners and may collapse the gap signal."
  ∷ mkOppositeFaceInvolutionObligationRow
    keepSelfAdjointDominationAndOSPromotionSeparate
    "promotion guard"
    "Keep self-adjointness, Hamiltonian domination, OS transfer, YM Clay, and terminal promotion separate and false."
  ∷ []

------------------------------------------------------------------------
-- Boundary flags.

boundaryRecorded : Bool
boundaryRecorded =
  true

admissibleBoundaryImported : Bool
admissibleBoundaryImported =
  true

domainContractImported : Bool
domainContractImported =
  true

fluxCancellationBoundaryImported : Bool
fluxCancellationBoundaryImported =
  true

fullDegreeKillingConventionConsumed : Bool
fullDegreeKillingConventionConsumed =
  true

inducedBallOppositeFaceCarrierRejected : Bool
inducedBallOppositeFaceCarrierRejected =
  true

finiteBTBoundaryFaceSetConstructed : Bool
finiteBTBoundaryFaceSetConstructed =
  false

oppositeFaceMapDefined : Bool
oppositeFaceMapDefined =
  false

oppositeFaceMapTotalProved : Bool
oppositeFaceMapTotalProved =
  false

oppositeFaceMapInvolutiveProved : Bool
oppositeFaceMapInvolutiveProved =
  false

orientationReversalProved : Bool
orientationReversalProved =
  false

fullDegreeKillingWeightPreservationProved : Bool
fullDegreeKillingWeightPreservationProved =
  false

localGaugeWeightPreservationProved : Bool
localGaugeWeightPreservationProved =
  false

gaugeCompatibilityProved : Bool
gaugeCompatibilityProved =
  false

orientationSignCancellationProved : Bool
orientationSignCancellationProved =
  false

feedsFluxCancellationProved : Bool
feedsFluxCancellationProved =
  false

selfAdjointnessDomainFeedThroughProved : Bool
selfAdjointnessDomainFeedThroughProved =
  false

hamiltonianDominationProved : Bool
hamiltonianDominationProved =
  false

osContinuumTransferProved : Bool
osContinuumTransferProved =
  false

ymClayPromoted : Bool
ymClayPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

boundaryRecordedIsTrue :
  boundaryRecorded ≡ true
boundaryRecordedIsTrue =
  refl

admissibleBoundaryImportedIsTrue :
  admissibleBoundaryImported ≡ true
admissibleBoundaryImportedIsTrue =
  refl

domainContractImportedIsTrue :
  domainContractImported ≡ true
domainContractImportedIsTrue =
  refl

fluxCancellationBoundaryImportedIsTrue :
  fluxCancellationBoundaryImported ≡ true
fluxCancellationBoundaryImportedIsTrue =
  refl

fullDegreeKillingConventionConsumedIsTrue :
  fullDegreeKillingConventionConsumed ≡ true
fullDegreeKillingConventionConsumedIsTrue =
  refl

inducedBallOppositeFaceCarrierRejectedIsTrue :
  inducedBallOppositeFaceCarrierRejected ≡ true
inducedBallOppositeFaceCarrierRejectedIsTrue =
  refl

finiteBTBoundaryFaceSetConstructedIsFalse :
  finiteBTBoundaryFaceSetConstructed ≡ false
finiteBTBoundaryFaceSetConstructedIsFalse =
  refl

oppositeFaceMapDefinedIsFalse :
  oppositeFaceMapDefined ≡ false
oppositeFaceMapDefinedIsFalse =
  refl

oppositeFaceMapTotalProvedIsFalse :
  oppositeFaceMapTotalProved ≡ false
oppositeFaceMapTotalProvedIsFalse =
  refl

oppositeFaceMapInvolutiveProvedIsFalse :
  oppositeFaceMapInvolutiveProved ≡ false
oppositeFaceMapInvolutiveProvedIsFalse =
  refl

orientationReversalProvedIsFalse :
  orientationReversalProved ≡ false
orientationReversalProvedIsFalse =
  refl

fullDegreeKillingWeightPreservationProvedIsFalse :
  fullDegreeKillingWeightPreservationProved ≡ false
fullDegreeKillingWeightPreservationProvedIsFalse =
  refl

localGaugeWeightPreservationProvedIsFalse :
  localGaugeWeightPreservationProved ≡ false
localGaugeWeightPreservationProvedIsFalse =
  refl

gaugeCompatibilityProvedIsFalse :
  gaugeCompatibilityProved ≡ false
gaugeCompatibilityProvedIsFalse =
  refl

orientationSignCancellationProvedIsFalse :
  orientationSignCancellationProved ≡ false
orientationSignCancellationProvedIsFalse =
  refl

feedsFluxCancellationProvedIsFalse :
  feedsFluxCancellationProved ≡ false
feedsFluxCancellationProvedIsFalse =
  refl

selfAdjointnessDomainFeedThroughProvedIsFalse :
  selfAdjointnessDomainFeedThroughProved ≡ false
selfAdjointnessDomainFeedThroughProvedIsFalse =
  refl

hamiltonianDominationProvedIsFalse :
  hamiltonianDominationProved ≡ false
hamiltonianDominationProvedIsFalse =
  refl

osContinuumTransferProvedIsFalse :
  osContinuumTransferProved ≡ false
osContinuumTransferProvedIsFalse =
  refl

ymClayPromotedIsFalse :
  ymClayPromoted ≡ false
ymClayPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

oppositeFaceInvolutionFormula : String
oppositeFaceInvolutionFormula =
  "opp : Face_Killing -> Face_Killing, opp(opp(F)) = F, weight(opp(F)) = weight(F), normal(opp(F)) = -normal(F)"

fluxCancellationFeedFormula : String
fluxCancellationFeedFormula =
  "total opposite-face involution + weight preservation + orientation reversal + gauge compatibility -> paired boundary flux cancellation"

------------------------------------------------------------------------
-- Canonical child boundary receipt.

record YMKillingBoundaryOppositeFaceInvolutionBoundary : Setω where
  field
    status :
      YMKillingBoundaryOppositeFaceStatus

    admissibleBoundary :
      Admissible.YMAdmissibleBTBoundaryConventionBoundary

    admissibleBoundaryCanonical :
      Bool

    admissibleBoundaryCanonicalIsTrue :
      admissibleBoundaryCanonical ≡ true

    domainContract :
      DomainContract.YMKillingBoundarySelfAdjointnessDomainContract

    domainContractCanonical :
      Bool

    domainContractCanonicalIsTrue :
      domainContractCanonical ≡ true

    fluxCancellationBoundary :
      Flux.YMKillingBoundaryFluxCancellationBoundary

    fluxCancellationBoundaryCanonical :
      Bool

    fluxCancellationBoundaryCanonicalIsTrue :
      fluxCancellationBoundaryCanonical ≡ true

    faceCarriers :
      List FiniteBTBoundaryFaceCarrier

    faceCarriersAreCanonical :
      faceCarriers ≡ canonicalFiniteBTBoundaryFaceCarriers

    faceCarrierCount :
      Nat

    faceCarrierCountIs4 :
      faceCarrierCount ≡ 4

    mechanisms :
      List OppositeFaceInvolutionMechanism

    mechanismsAreCanonical :
      mechanisms ≡ canonicalOppositeFaceInvolutionMechanisms

    mechanismCount :
      Nat

    mechanismCountIs8 :
      mechanismCount ≡ 8

    dependencies :
      List OppositeFaceInvolutionDependency

    dependenciesAreCanonical :
      dependencies ≡ canonicalOppositeFaceInvolutionDependencies

    dependencyCount :
      Nat

    dependencyCountIs8 :
      dependencyCount ≡ 8

    obligations :
      List OppositeFaceInvolutionObligation

    obligationsAreCanonical :
      obligations ≡ canonicalOppositeFaceInvolutionObligations

    obligationCount :
      Nat

    obligationCountIs12 :
      obligationCount ≡ 12

    obligationRows :
      List OppositeFaceInvolutionObligationRow

    obligationRowsAreCanonical :
      obligationRows ≡ canonicalOppositeFaceInvolutionObligationRows

    obligationRowCount :
      Nat

    obligationRowCountIs12 :
      obligationRowCount ≡ 12

    blockers :
      List OppositeFaceInvolutionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalOppositeFaceInvolutionBlockers

    blockerCount :
      Nat

    blockerCountIs12 :
      blockerCount ≡ 12

    firstBlocker :
      OppositeFaceInvolutionBlocker

    firstBlockerIsMissingFaceSet :
      firstBlocker ≡ missingFiniteBTBoundaryFaceSetConstruction

    formula :
      String

    formulaIsCanonical :
      formula ≡ oppositeFaceInvolutionFormula

    feedFormula :
      String

    feedFormulaIsCanonical :
      feedFormula ≡ fluxCancellationFeedFormula

    boundaryRecordedField :
      Bool

    boundaryRecordedFieldIsTrue :
      boundaryRecordedField ≡ true

    fullDegreeKillingConventionConsumedField :
      Bool

    fullDegreeKillingConventionConsumedFieldIsTrue :
      fullDegreeKillingConventionConsumedField ≡ true

    inducedBallOppositeFaceCarrierRejectedField :
      Bool

    inducedBallOppositeFaceCarrierRejectedFieldIsTrue :
      inducedBallOppositeFaceCarrierRejectedField ≡ true

    finiteBTBoundaryFaceSetConstructedField :
      Bool

    finiteBTBoundaryFaceSetConstructedFieldIsFalse :
      finiteBTBoundaryFaceSetConstructedField ≡ false

    oppositeFaceMapDefinedField :
      Bool

    oppositeFaceMapDefinedFieldIsFalse :
      oppositeFaceMapDefinedField ≡ false

    oppositeFaceMapTotalProvedField :
      Bool

    oppositeFaceMapTotalProvedFieldIsFalse :
      oppositeFaceMapTotalProvedField ≡ false

    oppositeFaceMapInvolutiveProvedField :
      Bool

    oppositeFaceMapInvolutiveProvedFieldIsFalse :
      oppositeFaceMapInvolutiveProvedField ≡ false

    orientationReversalProvedField :
      Bool

    orientationReversalProvedFieldIsFalse :
      orientationReversalProvedField ≡ false

    fullDegreeKillingWeightPreservationProvedField :
      Bool

    fullDegreeKillingWeightPreservationProvedFieldIsFalse :
      fullDegreeKillingWeightPreservationProvedField ≡ false

    localGaugeWeightPreservationProvedField :
      Bool

    localGaugeWeightPreservationProvedFieldIsFalse :
      localGaugeWeightPreservationProvedField ≡ false

    gaugeCompatibilityProvedField :
      Bool

    gaugeCompatibilityProvedFieldIsFalse :
      gaugeCompatibilityProvedField ≡ false

    orientationSignCancellationProvedField :
      Bool

    orientationSignCancellationProvedFieldIsFalse :
      orientationSignCancellationProvedField ≡ false

    feedsFluxCancellationProvedField :
      Bool

    feedsFluxCancellationProvedFieldIsFalse :
      feedsFluxCancellationProvedField ≡ false

    selfAdjointnessDomainFeedThroughProvedField :
      Bool

    selfAdjointnessDomainFeedThroughProvedFieldIsFalse :
      selfAdjointnessDomainFeedThroughProvedField ≡ false

    hamiltonianDominationProvedField :
      Bool

    hamiltonianDominationProvedFieldIsFalse :
      hamiltonianDominationProvedField ≡ false

    osContinuumTransferProvedField :
      Bool

    osContinuumTransferProvedFieldIsFalse :
      osContinuumTransferProvedField ≡ false

    ymClayPromotedField :
      Bool

    ymClayPromotedFieldIsFalse :
      ymClayPromotedField ≡ false

    terminalPromotionField :
      Bool

    terminalPromotionFieldIsFalse :
      terminalPromotionField ≡ false

    importedInducedBallStillRejected :
      Admissible.inducedBallAcceptedAsCurrentGapCarrierField
        admissibleBoundary
      ≡
      false

    importedDomainFluxStillOpen :
      DomainContract.boundaryFluxCancellationProvedField
        domainContract
      ≡
      false

    importedDomainSelfAdjointStillOpen :
      DomainContract.selfAdjointQuotientHamiltonianProvedField
        domainContract
      ≡
      false

    importedFluxOppositeInvolutionStillOpen :
      Flux.oppositeFaceInvolutionProvedField
        fluxCancellationBoundary
      ≡
      false

    importedFluxWeightPreservationStillOpen :
      Flux.killingWeightPreservationProvedField
        fluxCancellationBoundary
      ≡
      false

    importedFluxOrientationCancellationStillOpen :
      Flux.oppositeNormalFluxCancellationProvedField
        fluxCancellationBoundary
      ≡
      false

    importedFluxSelfAdjointFeedStillOpen :
      Flux.selfAdjointnessFeedThroughProvedField
        fluxCancellationBoundary
      ≡
      false

    importedFluxYMClayStillOpen :
      Flux.ymClayPromotedField
        fluxCancellationBoundary
      ≡
      false

    notes :
      List String

open YMKillingBoundaryOppositeFaceInvolutionBoundary public

canonicalYMKillingBoundaryOppositeFaceInvolutionBoundary :
  YMKillingBoundaryOppositeFaceInvolutionBoundary
canonicalYMKillingBoundaryOppositeFaceInvolutionBoundary =
  record
    { status =
        oppositeFaceInvolutionBoundaryRecordedProofStillOpen
    ; admissibleBoundary =
        Admissible.canonicalYMAdmissibleBTBoundaryConventionBoundary
    ; admissibleBoundaryCanonical =
        true
    ; admissibleBoundaryCanonicalIsTrue =
        refl
    ; domainContract =
        DomainContract.canonicalYMKillingBoundarySelfAdjointnessDomainContract
    ; domainContractCanonical =
        true
    ; domainContractCanonicalIsTrue =
        refl
    ; fluxCancellationBoundary =
        Flux.canonicalYMKillingBoundaryFluxCancellationBoundary
    ; fluxCancellationBoundaryCanonical =
        true
    ; fluxCancellationBoundaryCanonicalIsTrue =
        refl
    ; faceCarriers =
        canonicalFiniteBTBoundaryFaceCarriers
    ; faceCarriersAreCanonical =
        refl
    ; faceCarrierCount =
        listCount canonicalFiniteBTBoundaryFaceCarriers
    ; faceCarrierCountIs4 =
        refl
    ; mechanisms =
        canonicalOppositeFaceInvolutionMechanisms
    ; mechanismsAreCanonical =
        refl
    ; mechanismCount =
        listCount canonicalOppositeFaceInvolutionMechanisms
    ; mechanismCountIs8 =
        refl
    ; dependencies =
        canonicalOppositeFaceInvolutionDependencies
    ; dependenciesAreCanonical =
        refl
    ; dependencyCount =
        listCount canonicalOppositeFaceInvolutionDependencies
    ; dependencyCountIs8 =
        refl
    ; obligations =
        canonicalOppositeFaceInvolutionObligations
    ; obligationsAreCanonical =
        refl
    ; obligationCount =
        listCount canonicalOppositeFaceInvolutionObligations
    ; obligationCountIs12 =
        refl
    ; obligationRows =
        canonicalOppositeFaceInvolutionObligationRows
    ; obligationRowsAreCanonical =
        refl
    ; obligationRowCount =
        listCount canonicalOppositeFaceInvolutionObligationRows
    ; obligationRowCountIs12 =
        refl
    ; blockers =
        canonicalOppositeFaceInvolutionBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCount =
        listCount canonicalOppositeFaceInvolutionBlockers
    ; blockerCountIs12 =
        refl
    ; firstBlocker =
        missingFiniteBTBoundaryFaceSetConstruction
    ; firstBlockerIsMissingFaceSet =
        refl
    ; formula =
        oppositeFaceInvolutionFormula
    ; formulaIsCanonical =
        refl
    ; feedFormula =
        fluxCancellationFeedFormula
    ; feedFormulaIsCanonical =
        refl
    ; boundaryRecordedField =
        boundaryRecorded
    ; boundaryRecordedFieldIsTrue =
        boundaryRecordedIsTrue
    ; fullDegreeKillingConventionConsumedField =
        fullDegreeKillingConventionConsumed
    ; fullDegreeKillingConventionConsumedFieldIsTrue =
        fullDegreeKillingConventionConsumedIsTrue
    ; inducedBallOppositeFaceCarrierRejectedField =
        inducedBallOppositeFaceCarrierRejected
    ; inducedBallOppositeFaceCarrierRejectedFieldIsTrue =
        inducedBallOppositeFaceCarrierRejectedIsTrue
    ; finiteBTBoundaryFaceSetConstructedField =
        finiteBTBoundaryFaceSetConstructed
    ; finiteBTBoundaryFaceSetConstructedFieldIsFalse =
        finiteBTBoundaryFaceSetConstructedIsFalse
    ; oppositeFaceMapDefinedField =
        oppositeFaceMapDefined
    ; oppositeFaceMapDefinedFieldIsFalse =
        oppositeFaceMapDefinedIsFalse
    ; oppositeFaceMapTotalProvedField =
        oppositeFaceMapTotalProved
    ; oppositeFaceMapTotalProvedFieldIsFalse =
        oppositeFaceMapTotalProvedIsFalse
    ; oppositeFaceMapInvolutiveProvedField =
        oppositeFaceMapInvolutiveProved
    ; oppositeFaceMapInvolutiveProvedFieldIsFalse =
        oppositeFaceMapInvolutiveProvedIsFalse
    ; orientationReversalProvedField =
        orientationReversalProved
    ; orientationReversalProvedFieldIsFalse =
        orientationReversalProvedIsFalse
    ; fullDegreeKillingWeightPreservationProvedField =
        fullDegreeKillingWeightPreservationProved
    ; fullDegreeKillingWeightPreservationProvedFieldIsFalse =
        fullDegreeKillingWeightPreservationProvedIsFalse
    ; localGaugeWeightPreservationProvedField =
        localGaugeWeightPreservationProved
    ; localGaugeWeightPreservationProvedFieldIsFalse =
        localGaugeWeightPreservationProvedIsFalse
    ; gaugeCompatibilityProvedField =
        gaugeCompatibilityProved
    ; gaugeCompatibilityProvedFieldIsFalse =
        gaugeCompatibilityProvedIsFalse
    ; orientationSignCancellationProvedField =
        orientationSignCancellationProved
    ; orientationSignCancellationProvedFieldIsFalse =
        orientationSignCancellationProvedIsFalse
    ; feedsFluxCancellationProvedField =
        feedsFluxCancellationProved
    ; feedsFluxCancellationProvedFieldIsFalse =
        feedsFluxCancellationProvedIsFalse
    ; selfAdjointnessDomainFeedThroughProvedField =
        selfAdjointnessDomainFeedThroughProved
    ; selfAdjointnessDomainFeedThroughProvedFieldIsFalse =
        selfAdjointnessDomainFeedThroughProvedIsFalse
    ; hamiltonianDominationProvedField =
        hamiltonianDominationProved
    ; hamiltonianDominationProvedFieldIsFalse =
        hamiltonianDominationProvedIsFalse
    ; osContinuumTransferProvedField =
        osContinuumTransferProved
    ; osContinuumTransferProvedFieldIsFalse =
        osContinuumTransferProvedIsFalse
    ; ymClayPromotedField =
        ymClayPromoted
    ; ymClayPromotedFieldIsFalse =
        ymClayPromotedIsFalse
    ; terminalPromotionField =
        terminalPromotion
    ; terminalPromotionFieldIsFalse =
        terminalPromotionIsFalse
    ; importedInducedBallStillRejected =
        Admissible.inducedBallAcceptedAsCurrentGapCarrierIsFalse
    ; importedDomainFluxStillOpen =
        DomainContract.boundaryFluxCancellationProvedFieldIsFalse
          DomainContract.canonicalYMKillingBoundarySelfAdjointnessDomainContract
    ; importedDomainSelfAdjointStillOpen =
        DomainContract.canonicalKillingBoundaryDomainSelfAdjointStillFalse
    ; importedFluxOppositeInvolutionStillOpen =
        Flux.oppositeFaceInvolutionProvedIsFalse
    ; importedFluxWeightPreservationStillOpen =
        Flux.killingWeightPreservationProvedIsFalse
    ; importedFluxOrientationCancellationStillOpen =
        Flux.oppositeNormalFluxCancellationProvedIsFalse
    ; importedFluxSelfAdjointFeedStillOpen =
        Flux.canonicalKillingBoundaryFluxSelfAdjointFeedStillFalse
    ; importedFluxYMClayStillOpen =
        Flux.canonicalKillingBoundaryFluxYMClayStillFalse
    ; notes =
        "The opposite-face map must be total and involutive on the finite BT boundary face carrier before flux pairing can be used in finite Hodge integration by parts."
        ∷ "Full-degree/Killing weights and local gauge representation weights must be preserved by the opposite-face map; otherwise paired boundary terms need not cancel."
        ∷ "Orientation reversal supplies the sign cancellation, while gauge compatibility keeps the paired-face domain stable under finite gauge transformations and quotient projection."
        ∷ "This child feeds only the existing Killing boundary flux-cancellation boundary; self-adjointness, Hamiltonian domination, OS transfer, YM Clay, and terminal promotion remain false."
        ∷ []
    }

------------------------------------------------------------------------
-- Guard lemmas.

canonicalOppositeFaceCarrierCountIs4 :
  faceCarrierCount canonicalYMKillingBoundaryOppositeFaceInvolutionBoundary
  ≡
  4
canonicalOppositeFaceCarrierCountIs4 =
  refl

canonicalOppositeFaceMechanismCountIs8 :
  mechanismCount canonicalYMKillingBoundaryOppositeFaceInvolutionBoundary
  ≡
  8
canonicalOppositeFaceMechanismCountIs8 =
  refl

canonicalOppositeFaceObligationCountIs12 :
  obligationCount canonicalYMKillingBoundaryOppositeFaceInvolutionBoundary
  ≡
  12
canonicalOppositeFaceObligationCountIs12 =
  refl

canonicalOppositeFaceFirstBlocker :
  firstBlocker canonicalYMKillingBoundaryOppositeFaceInvolutionBoundary
  ≡
  missingFiniteBTBoundaryFaceSetConstruction
canonicalOppositeFaceFirstBlocker =
  refl

canonicalOppositeFaceMapStillFalse :
  oppositeFaceMapDefinedField
    canonicalYMKillingBoundaryOppositeFaceInvolutionBoundary
  ≡
  false
canonicalOppositeFaceMapStillFalse =
  refl

canonicalOppositeFaceTotalityStillFalse :
  oppositeFaceMapTotalProvedField
    canonicalYMKillingBoundaryOppositeFaceInvolutionBoundary
  ≡
  false
canonicalOppositeFaceTotalityStillFalse =
  refl

canonicalOppositeFaceInvolutionStillFalse :
  oppositeFaceMapInvolutiveProvedField
    canonicalYMKillingBoundaryOppositeFaceInvolutionBoundary
  ≡
  false
canonicalOppositeFaceInvolutionStillFalse =
  refl

canonicalOppositeFaceWeightPreservationStillFalse :
  fullDegreeKillingWeightPreservationProvedField
    canonicalYMKillingBoundaryOppositeFaceInvolutionBoundary
  ≡
  false
canonicalOppositeFaceWeightPreservationStillFalse =
  refl

canonicalOppositeFaceOrientationCancellationStillFalse :
  orientationSignCancellationProvedField
    canonicalYMKillingBoundaryOppositeFaceInvolutionBoundary
  ≡
  false
canonicalOppositeFaceOrientationCancellationStillFalse =
  refl

canonicalOppositeFaceGaugeCompatibilityStillFalse :
  gaugeCompatibilityProvedField
    canonicalYMKillingBoundaryOppositeFaceInvolutionBoundary
  ≡
  false
canonicalOppositeFaceGaugeCompatibilityStillFalse =
  refl

canonicalOppositeFaceFluxFeedStillFalse :
  feedsFluxCancellationProvedField
    canonicalYMKillingBoundaryOppositeFaceInvolutionBoundary
  ≡
  false
canonicalOppositeFaceFluxFeedStillFalse =
  refl

canonicalOppositeFaceSelfAdjointFeedStillFalse :
  selfAdjointnessDomainFeedThroughProvedField
    canonicalYMKillingBoundaryOppositeFaceInvolutionBoundary
  ≡
  false
canonicalOppositeFaceSelfAdjointFeedStillFalse =
  refl

canonicalOppositeFaceYMClayStillFalse :
  ymClayPromotedField
    canonicalYMKillingBoundaryOppositeFaceInvolutionBoundary
  ≡
  false
canonicalOppositeFaceYMClayStillFalse =
  refl

canonicalOppositeFaceTerminalStillFalse :
  terminalPromotionField
    canonicalYMKillingBoundaryOppositeFaceInvolutionBoundary
  ≡
  false
canonicalOppositeFaceTerminalStillFalse =
  refl

data YMKillingBoundaryOppositeFacePromotionToken : Set where

ymKillingBoundaryOppositeFacePromotionTokenImpossibleHere :
  YMKillingBoundaryOppositeFacePromotionToken →
  ⊥
ymKillingBoundaryOppositeFacePromotionTokenImpossibleHere ()

noOppositeFaceInvolutionPromotionFromBoundaryRecordAlone :
  oppositeFaceMapInvolutiveProvedField
    canonicalYMKillingBoundaryOppositeFaceInvolutionBoundary
  ≡
  true →
  ⊥
noOppositeFaceInvolutionPromotionFromBoundaryRecordAlone ()

noWeightPreservationPromotionFromBoundaryRecordAlone :
  fullDegreeKillingWeightPreservationProvedField
    canonicalYMKillingBoundaryOppositeFaceInvolutionBoundary
  ≡
  true →
  ⊥
noWeightPreservationPromotionFromBoundaryRecordAlone ()

noFluxCancellationPromotionFromOppositeFaceBoundaryAlone :
  feedsFluxCancellationProvedField
    canonicalYMKillingBoundaryOppositeFaceInvolutionBoundary
  ≡
  true →
  ⊥
noFluxCancellationPromotionFromOppositeFaceBoundaryAlone ()

noYMClayPromotionFromOppositeFaceBoundaryAlone :
  ymClayPromotedField canonicalYMKillingBoundaryOppositeFaceInvolutionBoundary
  ≡
  true →
  ⊥
noYMClayPromotionFromOppositeFaceBoundaryAlone ()

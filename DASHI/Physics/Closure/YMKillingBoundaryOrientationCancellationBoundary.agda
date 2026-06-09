module DASHI.Physics.Closure.YMKillingBoundaryOrientationCancellationBoundary where

-- Composite boundary for the YM-1 full-degree/Killing boundary sign step.
--
-- This module records the orientation/normal-sign cancellation layer between
-- the opposite-face involution, Killing weight preservation, boundary flux
-- cancellation, and the finite self-adjointness domain contract:
--
--   opposite full-degree faces are paired by the involution boundary
--   full-degree/Killing weights are equal across paired faces
--   outward normals reverse orientation across paired faces
--   equal-weight, opposite-normal flux terms cancel in the boundary sum
--   the result routes only into flux cancellation and the YM-1 domain contract
--
-- It is a proof-contract boundary only.  It does not prove the involution,
-- the weight theorem, normal sign cancellation, finite Hodge adjointness,
-- finite self-adjointness, Hamiltonian domination, OS transfer, YM Clay, or
-- terminal promotion.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMKillingBoundaryFluxCancellationBoundary
  as Flux
import DASHI.Physics.Closure.YMKillingBoundaryOppositeFaceInvolutionBoundary
  as Opposite
import DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessDomainContract
  as DomainContract
import DASHI.Physics.Closure.YMKillingBoundaryWeightPreservationBoundary
  as Weight

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Orientation/normal sign vocabulary.

data YMKillingBoundaryOrientationCancellationStatus : Set where
  orientationNormalCancellationBoundaryRecordedProofStillOpen :
    YMKillingBoundaryOrientationCancellationStatus

data OrientationCancellationInput : Set where
  oppositeFaceInvolutionInput :
    OrientationCancellationInput

  fullDegreeKillingWeightPreservationInput :
    OrientationCancellationInput

  orientedNormalReversalInput :
    OrientationCancellationInput

  gaugeCompatiblePairingInput :
    OrientationCancellationInput

  finiteHodgeBoundaryFluxConsumerInput :
    OrientationCancellationInput

canonicalOrientationCancellationInputs :
  List OrientationCancellationInput
canonicalOrientationCancellationInputs =
  oppositeFaceInvolutionInput
  ∷ fullDegreeKillingWeightPreservationInput
  ∷ orientedNormalReversalInput
  ∷ gaugeCompatiblePairingInput
  ∷ finiteHodgeBoundaryFluxConsumerInput
  ∷ []

data OrientationCancellationMechanism : Set where
  pairEveryAdmissibleKillingFaceWithOpposite :
    OrientationCancellationMechanism

  useSameFullDegreeWeightOnBothFaces :
    OrientationCancellationMechanism

  separatePositiveWeightFromSignedNormal :
    OrientationCancellationMechanism

  reverseNormalOrientationAcrossOppositeFace :
    OrientationCancellationMechanism

  cancelTwoFluxTermsBeforeQuotientDescent :
    OrientationCancellationMechanism

  preservePairingUnderFiniteGaugeAction :
    OrientationCancellationMechanism

  routeOnlyThroughFluxCancellationBoundary :
    OrientationCancellationMechanism

  routeSelfAdjointnessOnlyThroughDomainContract :
    OrientationCancellationMechanism

canonicalOrientationCancellationMechanisms :
  List OrientationCancellationMechanism
canonicalOrientationCancellationMechanisms =
  pairEveryAdmissibleKillingFaceWithOpposite
  ∷ useSameFullDegreeWeightOnBothFaces
  ∷ separatePositiveWeightFromSignedNormal
  ∷ reverseNormalOrientationAcrossOppositeFace
  ∷ cancelTwoFluxTermsBeforeQuotientDescent
  ∷ preservePairingUnderFiniteGaugeAction
  ∷ routeOnlyThroughFluxCancellationBoundary
  ∷ routeSelfAdjointnessOnlyThroughDomainContract
  ∷ []

data OrientationCancellationDependency : Set where
  consumesOppositeFaceInvolutionBoundary :
    OrientationCancellationDependency

  consumesKillingBoundaryWeightPreservationBoundary :
    OrientationCancellationDependency

  feedsKillingBoundaryFluxCancellationBoundary :
    OrientationCancellationDependency

  feedsSelfAdjointnessDomainContractOnlyAfterFlux :
    OrientationCancellationDependency

  keepsHamiltonianDominationAsLaterConsumer :
    OrientationCancellationDependency

  keepsOSTransferAsLaterConsumer :
    OrientationCancellationDependency

  keepsYMClayAndTerminalPromotionFalse :
    OrientationCancellationDependency

canonicalOrientationCancellationDependencies :
  List OrientationCancellationDependency
canonicalOrientationCancellationDependencies =
  consumesOppositeFaceInvolutionBoundary
  ∷ consumesKillingBoundaryWeightPreservationBoundary
  ∷ feedsKillingBoundaryFluxCancellationBoundary
  ∷ feedsSelfAdjointnessDomainContractOnlyAfterFlux
  ∷ keepsHamiltonianDominationAsLaterConsumer
  ∷ keepsOSTransferAsLaterConsumer
  ∷ keepsYMClayAndTerminalPromotionFalse
  ∷ []

data OrientationCancellationObligation : Set where
  importOppositeFaceInvolutionBoundary :
    OrientationCancellationObligation

  importWeightPreservationBoundary :
    OrientationCancellationObligation

  proveOppositeNormalOrientationReversal :
    OrientationCancellationObligation

  proveWeightAndNormalSignFactorization :
    OrientationCancellationObligation

  proveEqualWeightOppositeSignFluxPairCancels :
    OrientationCancellationObligation

  proveCancellationStableUnderGaugeAction :
    OrientationCancellationObligation

  proveCancellationStableUnderQuotientRepresentative :
    OrientationCancellationObligation

  routeCancellationIntoFluxBoundary :
    OrientationCancellationObligation

  routeFluxBoundaryIntoSelfAdjointnessDomain :
    OrientationCancellationObligation

  keepHamiltonianDominationSeparate :
    OrientationCancellationObligation

  keepOSContinuumTransferSeparate :
    OrientationCancellationObligation

  keepYMClayFalse :
    OrientationCancellationObligation

canonicalOrientationCancellationObligations :
  List OrientationCancellationObligation
canonicalOrientationCancellationObligations =
  importOppositeFaceInvolutionBoundary
  ∷ importWeightPreservationBoundary
  ∷ proveOppositeNormalOrientationReversal
  ∷ proveWeightAndNormalSignFactorization
  ∷ proveEqualWeightOppositeSignFluxPairCancels
  ∷ proveCancellationStableUnderGaugeAction
  ∷ proveCancellationStableUnderQuotientRepresentative
  ∷ routeCancellationIntoFluxBoundary
  ∷ routeFluxBoundaryIntoSelfAdjointnessDomain
  ∷ keepHamiltonianDominationSeparate
  ∷ keepOSContinuumTransferSeparate
  ∷ keepYMClayFalse
  ∷ []

data OrientationCancellationBlocker : Set where
  missingOppositeFaceMapProof :
    OrientationCancellationBlocker

  missingFullDegreeWeightEqualityProof :
    OrientationCancellationBlocker

  missingNormalOrientationReversalProof :
    OrientationCancellationBlocker

  missingSignedFluxPairCancellationProof :
    OrientationCancellationBlocker

  missingGaugeCompatibilityProof :
    OrientationCancellationBlocker

  missingQuotientRepresentativeStabilityProof :
    OrientationCancellationBlocker

  missingFluxCancellationFeedThrough :
    OrientationCancellationBlocker

  missingSelfAdjointnessDomainFeedThrough :
    OrientationCancellationBlocker

  missingHamiltonianDominationTheorem :
    OrientationCancellationBlocker

  missingOSTransferAndContinuumNoPollution :
    OrientationCancellationBlocker

  missingYMClayAuthorityToken :
    OrientationCancellationBlocker

canonicalOrientationCancellationBlockers :
  List OrientationCancellationBlocker
canonicalOrientationCancellationBlockers =
  missingOppositeFaceMapProof
  ∷ missingFullDegreeWeightEqualityProof
  ∷ missingNormalOrientationReversalProof
  ∷ missingSignedFluxPairCancellationProof
  ∷ missingGaugeCompatibilityProof
  ∷ missingQuotientRepresentativeStabilityProof
  ∷ missingFluxCancellationFeedThrough
  ∷ missingSelfAdjointnessDomainFeedThrough
  ∷ missingHamiltonianDominationTheorem
  ∷ missingOSTransferAndContinuumNoPollution
  ∷ missingYMClayAuthorityToken
  ∷ []

record OrientationCancellationObligationRow : Set where
  field
    obligation :
      OrientationCancellationObligation

    label :
      String

    contractText :
      String

    provedHere :
      Bool

    provedHereIsFalse :
      provedHere ≡ false

open OrientationCancellationObligationRow public

mkOrientationCancellationObligationRow :
  OrientationCancellationObligation →
  String →
  String →
  OrientationCancellationObligationRow
mkOrientationCancellationObligationRow obligation label contractText =
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

canonicalOrientationCancellationObligationRows :
  List OrientationCancellationObligationRow
canonicalOrientationCancellationObligationRows =
  mkOrientationCancellationObligationRow
    importOppositeFaceInvolutionBoundary
    "opposite faces"
    "Consume the opposite-face involution boundary as the carrier for paired full-degree/Killing faces."
  ∷ mkOrientationCancellationObligationRow
    importWeightPreservationBoundary
    "weight equality"
    "Consume the Killing/full-degree weight-preservation boundary as the equal-positive-weight input."
  ∷ mkOrientationCancellationObligationRow
    proveOppositeNormalOrientationReversal
    "normal reversal"
    "Prove the outward normal orientation changes sign under the opposite-face involution."
  ∷ mkOrientationCancellationObligationRow
    proveWeightAndNormalSignFactorization
    "factorization"
    "Separate positive full-degree weight preservation from signed normal orientation, so sign cancellation is not hidden in the weight theorem."
  ∷ mkOrientationCancellationObligationRow
    proveEqualWeightOppositeSignFluxPairCancels
    "flux pair"
    "Prove each paired face contributes equal-weight, opposite-normal boundary flux terms whose sum is zero."
  ∷ mkOrientationCancellationObligationRow
    proveCancellationStableUnderGaugeAction
    "gauge action"
    "Prove finite gauge transformations preserve the oriented paired-face cancellation row."
  ∷ mkOrientationCancellationObligationRow
    proveCancellationStableUnderQuotientRepresentative
    "quotient representative"
    "Prove representative changes inside a finite gauge orbit do not alter the paired cancellation residual."
  ∷ mkOrientationCancellationObligationRow
    routeCancellationIntoFluxBoundary
    "flux route"
    "Route the completed orientation/normal sign cancellation only into the Killing boundary flux-cancellation boundary."
  ∷ mkOrientationCancellationObligationRow
    routeFluxBoundaryIntoSelfAdjointnessDomain
    "domain route"
    "Route self-adjointness only through the flux boundary and YM-1 self-adjointness domain contract."
  ∷ mkOrientationCancellationObligationRow
    keepHamiltonianDominationSeparate
    "domination guard"
    "Do not infer Hamiltonian domination from this orientation boundary."
  ∷ mkOrientationCancellationObligationRow
    keepOSContinuumTransferSeparate
    "OS guard"
    "Do not infer OS transfer, continuum no-pollution, or Wightman reconstruction from this orientation boundary."
  ∷ mkOrientationCancellationObligationRow
    keepYMClayFalse
    "Clay guard"
    "Keep YM Clay, terminal promotion, and external authority tokens false."
  ∷ []

------------------------------------------------------------------------
-- Boundary flags.

boundaryRecorded : Bool
boundaryRecorded =
  true

oppositeFaceBoundaryImported : Bool
oppositeFaceBoundaryImported =
  true

weightPreservationBoundaryImported : Bool
weightPreservationBoundaryImported =
  true

fluxCancellationBoundaryImported : Bool
fluxCancellationBoundaryImported =
  true

selfAdjointnessDomainContractImported : Bool
selfAdjointnessDomainContractImported =
  true

fullDegreeKillingBoundaryConsumed : Bool
fullDegreeKillingBoundaryConsumed =
  true

oppositeFaceInvolutionProved : Bool
oppositeFaceInvolutionProved =
  false

killingWeightPreservationProved : Bool
killingWeightPreservationProved =
  false

normalOrientationReversalProved : Bool
normalOrientationReversalProved =
  false

orientationNormalFluxCancellationProved : Bool
orientationNormalFluxCancellationProved =
  false

gaugeCancellationStabilityProved : Bool
gaugeCancellationStabilityProved =
  false

quotientCancellationStabilityProved : Bool
quotientCancellationStabilityProved =
  false

fluxBoundaryFeedThroughProved : Bool
fluxBoundaryFeedThroughProved =
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

oppositeFaceBoundaryImportedIsTrue :
  oppositeFaceBoundaryImported ≡ true
oppositeFaceBoundaryImportedIsTrue =
  refl

weightPreservationBoundaryImportedIsTrue :
  weightPreservationBoundaryImported ≡ true
weightPreservationBoundaryImportedIsTrue =
  refl

fluxCancellationBoundaryImportedIsTrue :
  fluxCancellationBoundaryImported ≡ true
fluxCancellationBoundaryImportedIsTrue =
  refl

selfAdjointnessDomainContractImportedIsTrue :
  selfAdjointnessDomainContractImported ≡ true
selfAdjointnessDomainContractImportedIsTrue =
  refl

fullDegreeKillingBoundaryConsumedIsTrue :
  fullDegreeKillingBoundaryConsumed ≡ true
fullDegreeKillingBoundaryConsumedIsTrue =
  refl

oppositeFaceInvolutionProvedIsFalse :
  oppositeFaceInvolutionProved ≡ false
oppositeFaceInvolutionProvedIsFalse =
  refl

killingWeightPreservationProvedIsFalse :
  killingWeightPreservationProved ≡ false
killingWeightPreservationProvedIsFalse =
  refl

normalOrientationReversalProvedIsFalse :
  normalOrientationReversalProved ≡ false
normalOrientationReversalProvedIsFalse =
  refl

orientationNormalFluxCancellationProvedIsFalse :
  orientationNormalFluxCancellationProved ≡ false
orientationNormalFluxCancellationProvedIsFalse =
  refl

gaugeCancellationStabilityProvedIsFalse :
  gaugeCancellationStabilityProved ≡ false
gaugeCancellationStabilityProvedIsFalse =
  refl

quotientCancellationStabilityProvedIsFalse :
  quotientCancellationStabilityProved ≡ false
quotientCancellationStabilityProvedIsFalse =
  refl

fluxBoundaryFeedThroughProvedIsFalse :
  fluxBoundaryFeedThroughProved ≡ false
fluxBoundaryFeedThroughProvedIsFalse =
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

orientationCancellationFormula : String
orientationCancellationFormula =
  "weight_K(F) * normal(F) + weight_K(opp(F)) * normal(opp(F)) = 0"

domainRouteFormula : String
domainRouteFormula =
  "opposite-face involution + weight preservation + normal reversal -> flux cancellation -> YM-1 self-adjointness domain contract"

------------------------------------------------------------------------
-- Composite boundary receipt.

record YMKillingBoundaryOrientationCancellationBoundary : Setω where
  field
    status :
      YMKillingBoundaryOrientationCancellationStatus

    oppositeFaceBoundary :
      Opposite.YMKillingBoundaryOppositeFaceInvolutionBoundary

    oppositeFaceBoundaryCanonical :
      Bool

    oppositeFaceBoundaryCanonicalIsTrue :
      oppositeFaceBoundaryCanonical ≡ true

    weightPreservationBoundary :
      Weight.YMKillingBoundaryWeightPreservationBoundary

    weightPreservationBoundaryCanonical :
      Bool

    weightPreservationBoundaryCanonicalIsTrue :
      weightPreservationBoundaryCanonical ≡ true

    fluxCancellationBoundary :
      Flux.YMKillingBoundaryFluxCancellationBoundary

    fluxCancellationBoundaryCanonical :
      Bool

    fluxCancellationBoundaryCanonicalIsTrue :
      fluxCancellationBoundaryCanonical ≡ true

    selfAdjointnessDomainContract :
      DomainContract.YMKillingBoundarySelfAdjointnessDomainContract

    selfAdjointnessDomainContractCanonical :
      Bool

    selfAdjointnessDomainContractCanonicalIsTrue :
      selfAdjointnessDomainContractCanonical ≡ true

    inputs :
      List OrientationCancellationInput

    inputsAreCanonical :
      inputs ≡ canonicalOrientationCancellationInputs

    inputCount :
      Nat

    inputCountIs5 :
      inputCount ≡ 5

    mechanisms :
      List OrientationCancellationMechanism

    mechanismsAreCanonical :
      mechanisms ≡ canonicalOrientationCancellationMechanisms

    mechanismCount :
      Nat

    mechanismCountIs8 :
      mechanismCount ≡ 8

    dependencies :
      List OrientationCancellationDependency

    dependenciesAreCanonical :
      dependencies ≡ canonicalOrientationCancellationDependencies

    dependencyCount :
      Nat

    dependencyCountIs7 :
      dependencyCount ≡ 7

    obligations :
      List OrientationCancellationObligation

    obligationsAreCanonical :
      obligations ≡ canonicalOrientationCancellationObligations

    obligationCount :
      Nat

    obligationCountIs12 :
      obligationCount ≡ 12

    obligationRows :
      List OrientationCancellationObligationRow

    obligationRowsAreCanonical :
      obligationRows ≡ canonicalOrientationCancellationObligationRows

    obligationRowCount :
      Nat

    obligationRowCountIs12 :
      obligationRowCount ≡ 12

    blockers :
      List OrientationCancellationBlocker

    blockersAreCanonical :
      blockers ≡ canonicalOrientationCancellationBlockers

    blockerCount :
      Nat

    blockerCountIs11 :
      blockerCount ≡ 11

    firstBlocker :
      OrientationCancellationBlocker

    firstBlockerIsMissingOppositeFaceMap :
      firstBlocker ≡ missingOppositeFaceMapProof

    formula :
      String

    formulaIsCanonical :
      formula ≡ orientationCancellationFormula

    routeFormula :
      String

    routeFormulaIsCanonical :
      routeFormula ≡ domainRouteFormula

    boundaryRecordedField :
      Bool

    boundaryRecordedFieldIsTrue :
      boundaryRecordedField ≡ true

    fullDegreeKillingBoundaryConsumedField :
      Bool

    fullDegreeKillingBoundaryConsumedFieldIsTrue :
      fullDegreeKillingBoundaryConsumedField ≡ true

    oppositeFaceInvolutionProvedField :
      Bool

    oppositeFaceInvolutionProvedFieldIsFalse :
      oppositeFaceInvolutionProvedField ≡ false

    killingWeightPreservationProvedField :
      Bool

    killingWeightPreservationProvedFieldIsFalse :
      killingWeightPreservationProvedField ≡ false

    normalOrientationReversalProvedField :
      Bool

    normalOrientationReversalProvedFieldIsFalse :
      normalOrientationReversalProvedField ≡ false

    orientationNormalFluxCancellationProvedField :
      Bool

    orientationNormalFluxCancellationProvedFieldIsFalse :
      orientationNormalFluxCancellationProvedField ≡ false

    gaugeCancellationStabilityProvedField :
      Bool

    gaugeCancellationStabilityProvedFieldIsFalse :
      gaugeCancellationStabilityProvedField ≡ false

    quotientCancellationStabilityProvedField :
      Bool

    quotientCancellationStabilityProvedFieldIsFalse :
      quotientCancellationStabilityProvedField ≡ false

    fluxBoundaryFeedThroughProvedField :
      Bool

    fluxBoundaryFeedThroughProvedFieldIsFalse :
      fluxBoundaryFeedThroughProvedField ≡ false

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

    importedOppositeOrientationStillOpen :
      Opposite.orientationSignCancellationProvedField
        oppositeFaceBoundary
      ≡
      false

    importedOppositeFluxFeedStillOpen :
      Opposite.feedsFluxCancellationProvedField
        oppositeFaceBoundary
      ≡
      false

    importedWeightOrientationSeparationStillOpen :
      Weight.orientationNormalSignSeparationProvedField
        weightPreservationBoundary
      ≡
      false

    importedWeightFluxConsumerStillOpen :
      Weight.fluxCancellationConsumerProvedField
        weightPreservationBoundary
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

    importedDomainFluxCancellationStillOpen :
      DomainContract.boundaryFluxCancellationProvedField
        selfAdjointnessDomainContract
      ≡
      false

    importedDomainSelfAdjointStillOpen :
      DomainContract.selfAdjointQuotientHamiltonianProvedField
        selfAdjointnessDomainContract
      ≡
      false

    importedDomainHamiltonianDominationStillOpen :
      DomainContract.hamiltonianDominationProvedField
        selfAdjointnessDomainContract
      ≡
      false

    importedDomainOSTransferStillOpen :
      DomainContract.osContinuumTransferProvedField
        selfAdjointnessDomainContract
      ≡
      false

    importedDomainYMClayStillOpen :
      DomainContract.ymClayPromotedField
        selfAdjointnessDomainContract
      ≡
      false

    notes :
      List String

open YMKillingBoundaryOrientationCancellationBoundary public

canonicalYMKillingBoundaryOrientationCancellationBoundary :
  YMKillingBoundaryOrientationCancellationBoundary
canonicalYMKillingBoundaryOrientationCancellationBoundary =
  record
    { status =
        orientationNormalCancellationBoundaryRecordedProofStillOpen
    ; oppositeFaceBoundary =
        Opposite.canonicalYMKillingBoundaryOppositeFaceInvolutionBoundary
    ; oppositeFaceBoundaryCanonical =
        true
    ; oppositeFaceBoundaryCanonicalIsTrue =
        refl
    ; weightPreservationBoundary =
        Weight.canonicalYMKillingBoundaryWeightPreservationBoundary
    ; weightPreservationBoundaryCanonical =
        true
    ; weightPreservationBoundaryCanonicalIsTrue =
        refl
    ; fluxCancellationBoundary =
        Flux.canonicalYMKillingBoundaryFluxCancellationBoundary
    ; fluxCancellationBoundaryCanonical =
        true
    ; fluxCancellationBoundaryCanonicalIsTrue =
        refl
    ; selfAdjointnessDomainContract =
        DomainContract.canonicalYMKillingBoundarySelfAdjointnessDomainContract
    ; selfAdjointnessDomainContractCanonical =
        true
    ; selfAdjointnessDomainContractCanonicalIsTrue =
        refl
    ; inputs =
        canonicalOrientationCancellationInputs
    ; inputsAreCanonical =
        refl
    ; inputCount =
        listCount canonicalOrientationCancellationInputs
    ; inputCountIs5 =
        refl
    ; mechanisms =
        canonicalOrientationCancellationMechanisms
    ; mechanismsAreCanonical =
        refl
    ; mechanismCount =
        listCount canonicalOrientationCancellationMechanisms
    ; mechanismCountIs8 =
        refl
    ; dependencies =
        canonicalOrientationCancellationDependencies
    ; dependenciesAreCanonical =
        refl
    ; dependencyCount =
        listCount canonicalOrientationCancellationDependencies
    ; dependencyCountIs7 =
        refl
    ; obligations =
        canonicalOrientationCancellationObligations
    ; obligationsAreCanonical =
        refl
    ; obligationCount =
        listCount canonicalOrientationCancellationObligations
    ; obligationCountIs12 =
        refl
    ; obligationRows =
        canonicalOrientationCancellationObligationRows
    ; obligationRowsAreCanonical =
        refl
    ; obligationRowCount =
        listCount canonicalOrientationCancellationObligationRows
    ; obligationRowCountIs12 =
        refl
    ; blockers =
        canonicalOrientationCancellationBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCount =
        listCount canonicalOrientationCancellationBlockers
    ; blockerCountIs11 =
        refl
    ; firstBlocker =
        missingOppositeFaceMapProof
    ; firstBlockerIsMissingOppositeFaceMap =
        refl
    ; formula =
        orientationCancellationFormula
    ; formulaIsCanonical =
        refl
    ; routeFormula =
        domainRouteFormula
    ; routeFormulaIsCanonical =
        refl
    ; boundaryRecordedField =
        boundaryRecorded
    ; boundaryRecordedFieldIsTrue =
        boundaryRecordedIsTrue
    ; fullDegreeKillingBoundaryConsumedField =
        fullDegreeKillingBoundaryConsumed
    ; fullDegreeKillingBoundaryConsumedFieldIsTrue =
        fullDegreeKillingBoundaryConsumedIsTrue
    ; oppositeFaceInvolutionProvedField =
        oppositeFaceInvolutionProved
    ; oppositeFaceInvolutionProvedFieldIsFalse =
        oppositeFaceInvolutionProvedIsFalse
    ; killingWeightPreservationProvedField =
        killingWeightPreservationProved
    ; killingWeightPreservationProvedFieldIsFalse =
        killingWeightPreservationProvedIsFalse
    ; normalOrientationReversalProvedField =
        normalOrientationReversalProved
    ; normalOrientationReversalProvedFieldIsFalse =
        normalOrientationReversalProvedIsFalse
    ; orientationNormalFluxCancellationProvedField =
        orientationNormalFluxCancellationProved
    ; orientationNormalFluxCancellationProvedFieldIsFalse =
        orientationNormalFluxCancellationProvedIsFalse
    ; gaugeCancellationStabilityProvedField =
        gaugeCancellationStabilityProved
    ; gaugeCancellationStabilityProvedFieldIsFalse =
        gaugeCancellationStabilityProvedIsFalse
    ; quotientCancellationStabilityProvedField =
        quotientCancellationStabilityProved
    ; quotientCancellationStabilityProvedFieldIsFalse =
        quotientCancellationStabilityProvedIsFalse
    ; fluxBoundaryFeedThroughProvedField =
        fluxBoundaryFeedThroughProved
    ; fluxBoundaryFeedThroughProvedFieldIsFalse =
        fluxBoundaryFeedThroughProvedIsFalse
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
    ; importedOppositeOrientationStillOpen =
        Opposite.orientationSignCancellationProvedIsFalse
    ; importedOppositeFluxFeedStillOpen =
        Opposite.feedsFluxCancellationProvedIsFalse
    ; importedWeightOrientationSeparationStillOpen =
        Weight.orientationNormalSignSeparationProvedIsFalse
    ; importedWeightFluxConsumerStillOpen =
        Weight.fluxCancellationConsumerProvedIsFalse
    ; importedFluxOrientationCancellationStillOpen =
        Flux.oppositeNormalFluxCancellationProvedIsFalse
    ; importedFluxSelfAdjointFeedStillOpen =
        Flux.selfAdjointnessFeedThroughProvedIsFalse
    ; importedDomainFluxCancellationStillOpen =
        DomainContract.boundaryFluxCancellationProvedIsFalse
    ; importedDomainSelfAdjointStillOpen =
        DomainContract.selfAdjointQuotientHamiltonianProvedIsFalse
    ; importedDomainHamiltonianDominationStillOpen =
        DomainContract.hamiltonianDominationProvedIsFalse
    ; importedDomainOSTransferStillOpen =
        DomainContract.osContinuumTransferProvedIsFalse
    ; importedDomainYMClayStillOpen =
        DomainContract.ymClayPromotedIsFalse
    ; notes =
        "YM-1 orientation cancellation is recorded as a composite boundary over opposite-face involution and Killing weight preservation."
        ∷ "The route requires equal full-degree/Killing weights and opposite normal signs before any finite Hodge boundary residual may cancel."
        ∷ "Flux cancellation feeds the self-adjointness domain contract; Hamiltonian domination and OS transfer remain downstream and unproved."
        ∷ "YM Clay and terminal promotion remain false."
        ∷ []
    }

------------------------------------------------------------------------
-- Guard lemmas.

canonicalOrientationCancellationInputCountIs5 :
  inputCount canonicalYMKillingBoundaryOrientationCancellationBoundary
  ≡
  5
canonicalOrientationCancellationInputCountIs5 =
  refl

canonicalOrientationCancellationObligationCountIs12 :
  obligationCount canonicalYMKillingBoundaryOrientationCancellationBoundary
  ≡
  12
canonicalOrientationCancellationObligationCountIs12 =
  refl

canonicalOrientationCancellationBlockerCountIs11 :
  blockerCount canonicalYMKillingBoundaryOrientationCancellationBoundary
  ≡
  11
canonicalOrientationCancellationBlockerCountIs11 =
  refl

canonicalOrientationCancellationYMClayFalse :
  ymClayPromotedField
    canonicalYMKillingBoundaryOrientationCancellationBoundary
  ≡
  false
canonicalOrientationCancellationYMClayFalse =
  refl

canonicalOrientationCancellationDominationFalse :
  hamiltonianDominationProvedField
    canonicalYMKillingBoundaryOrientationCancellationBoundary
  ≡
  false
canonicalOrientationCancellationDominationFalse =
  refl

canonicalOrientationCancellationOSTransferFalse :
  osContinuumTransferProvedField
    canonicalYMKillingBoundaryOrientationCancellationBoundary
  ≡
  false
canonicalOrientationCancellationOSTransferFalse =
  refl

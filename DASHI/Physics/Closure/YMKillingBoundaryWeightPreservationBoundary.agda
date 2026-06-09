module DASHI.Physics.Closure.YMKillingBoundaryWeightPreservationBoundary where

-- Child boundary for the YM Killing/full-degree boundary convention.
--
-- This narrows the YM-1 flux-cancellation route to the weight-preservation
-- component of the opposite-face involution:
--
--   full-degree/Killing weight carrier
--   opposite-face involution input
--   weight equality target
--   orientation-normal sign separation
--   gauge compatibility
--   flux-cancellation consumer
--
-- This is a proof-contract receipt only.  It records the exact obligations
-- and blockers a future proof must discharge.  It does not prove the weight
-- formula, does not prove involution compatibility, does not prove gauge
-- invariance, does not prove flux cancellation, and keeps YM Clay / terminal
-- promotion false.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMAdmissibleBTBoundaryConventionBoundary
  as Admissible
import DASHI.Physics.Closure.YMKillingBoundaryFluxCancellationBoundary
  as Flux
import DASHI.Physics.Closure.YMKillingBoundaryOppositeFaceInvolutionBoundary
  as Opposite

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Weight-preservation vocabulary.

data YMKillingBoundaryWeightPreservationStatus : Set where
  killingBoundaryWeightPreservationBoundaryRecordedProofStillOpen :
    YMKillingBoundaryWeightPreservationStatus

data KillingFullDegreeWeightCarrier : Set where
  ambientBTFullDegreeWeight :
    KillingFullDegreeWeightCarrier

  killingBoundaryFaceWeight :
    KillingFullDegreeWeightCarrier

  localGaugeRepresentationWeight :
    KillingFullDegreeWeightCarrier

  quotientRepresentativeWeight :
    KillingFullDegreeWeightCarrier

  inducedBallWeightRejectedForCurrentRoute :
    KillingFullDegreeWeightCarrier

canonicalKillingFullDegreeWeightCarriers :
  List KillingFullDegreeWeightCarrier
canonicalKillingFullDegreeWeightCarriers =
  ambientBTFullDegreeWeight
  ∷ killingBoundaryFaceWeight
  ∷ localGaugeRepresentationWeight
  ∷ quotientRepresentativeWeight
  ∷ inducedBallWeightRejectedForCurrentRoute
  ∷ []

data OppositeFaceWeightInput : Set where
  oppositeFaceMapInput :
    OppositeFaceWeightInput

  oppositeFaceTotalityInput :
    OppositeFaceWeightInput

  oppositeFaceInvolutionInput :
    OppositeFaceWeightInput

  sameBoundaryConventionInput :
    OppositeFaceWeightInput

  finiteGaugeOrbitInput :
    OppositeFaceWeightInput

canonicalOppositeFaceWeightInputs :
  List OppositeFaceWeightInput
canonicalOppositeFaceWeightInputs =
  oppositeFaceMapInput
  ∷ oppositeFaceTotalityInput
  ∷ oppositeFaceInvolutionInput
  ∷ sameBoundaryConventionInput
  ∷ finiteGaugeOrbitInput
  ∷ []

data WeightPreservationMechanism : Set where
  defineWeightOnEveryKillingFace :
    WeightPreservationMechanism

  compareWeightsOnlyAcrossOppositeFaces :
    WeightPreservationMechanism

  separateOrientationNormalSignFromPositiveWeight :
    WeightPreservationMechanism

  preserveAmbientFullDegreeUnderOpposite :
    WeightPreservationMechanism

  preserveLocalGaugeRepresentationWeight :
    WeightPreservationMechanism

  preserveQuotientRepresentativeWeight :
    WeightPreservationMechanism

  rejectInducedBallWeightAsUnpaired :
    WeightPreservationMechanism

  feedEqualWeightOppositeSignFluxPair :
    WeightPreservationMechanism

canonicalWeightPreservationMechanisms :
  List WeightPreservationMechanism
canonicalWeightPreservationMechanisms =
  defineWeightOnEveryKillingFace
  ∷ compareWeightsOnlyAcrossOppositeFaces
  ∷ separateOrientationNormalSignFromPositiveWeight
  ∷ preserveAmbientFullDegreeUnderOpposite
  ∷ preserveLocalGaugeRepresentationWeight
  ∷ preserveQuotientRepresentativeWeight
  ∷ rejectInducedBallWeightAsUnpaired
  ∷ feedEqualWeightOppositeSignFluxPair
  ∷ []

data WeightPreservationConsumer : Set where
  consumesAdmissibleFullDegreeConvention :
    WeightPreservationConsumer

  consumesOppositeFaceInvolutionBoundary :
    WeightPreservationConsumer

  feedsOppositeFaceInvolutionWeightRow :
    WeightPreservationConsumer

  feedsKillingBoundaryFluxCancellation :
    WeightPreservationConsumer

  feedsFiniteHodgeBoundaryResidualPairing :
    WeightPreservationConsumer

  feedsGaugeDomainPreservationOnlyAfterGaugeProof :
    WeightPreservationConsumer

  keepsSelfAdjointnessAsSeparateConsumer :
    WeightPreservationConsumer

  keepsHamiltonianDominationAndOSSeparate :
    WeightPreservationConsumer

canonicalWeightPreservationConsumers :
  List WeightPreservationConsumer
canonicalWeightPreservationConsumers =
  consumesAdmissibleFullDegreeConvention
  ∷ consumesOppositeFaceInvolutionBoundary
  ∷ feedsOppositeFaceInvolutionWeightRow
  ∷ feedsKillingBoundaryFluxCancellation
  ∷ feedsFiniteHodgeBoundaryResidualPairing
  ∷ feedsGaugeDomainPreservationOnlyAfterGaugeProof
  ∷ keepsSelfAdjointnessAsSeparateConsumer
  ∷ keepsHamiltonianDominationAndOSSeparate
  ∷ []

data WeightPreservationObligation : Set where
  defineFullDegreeKillingWeightFormula :
    WeightPreservationObligation

  proveWeightFormulaIndependentOfFaceRepresentative :
    WeightPreservationObligation

  proveOppositeFaceWeightEquality :
    WeightPreservationObligation

  proveOppositeFaceInvolutionCompatibility :
    WeightPreservationObligation

  proveOrientationNormalSignSeparatedFromWeight :
    WeightPreservationObligation

  proveGaugeActionPreservesWeights :
    WeightPreservationObligation

  proveQuotientProjectionPreservesWeights :
    WeightPreservationObligation

  proveInducedBallWeightsRemainRejected :
    WeightPreservationObligation

  routeEqualWeightsIntoFluxCancellation :
    WeightPreservationObligation

  keepSelfAdjointnessAndPromotionSeparate :
    WeightPreservationObligation

canonicalWeightPreservationObligations :
  List WeightPreservationObligation
canonicalWeightPreservationObligations =
  defineFullDegreeKillingWeightFormula
  ∷ proveWeightFormulaIndependentOfFaceRepresentative
  ∷ proveOppositeFaceWeightEquality
  ∷ proveOppositeFaceInvolutionCompatibility
  ∷ proveOrientationNormalSignSeparatedFromWeight
  ∷ proveGaugeActionPreservesWeights
  ∷ proveQuotientProjectionPreservesWeights
  ∷ proveInducedBallWeightsRemainRejected
  ∷ routeEqualWeightsIntoFluxCancellation
  ∷ keepSelfAdjointnessAndPromotionSeparate
  ∷ []

data WeightPreservationBlocker : Set where
  missingWeightFormula :
    WeightPreservationBlocker

  missingRepresentativeIndependenceProof :
    WeightPreservationBlocker

  missingInvolutionCompatibility :
    WeightPreservationBlocker

  missingOrientationSeparation :
    WeightPreservationBlocker

  missingGaugeInvarianceProof :
    WeightPreservationBlocker

  missingQuotientProjectionProof :
    WeightPreservationBlocker

  missingFluxCancellationConsumerProof :
    WeightPreservationBlocker

  inducedBallWeightRouteStillRejected :
    WeightPreservationBlocker

  missingSelfAdjointnessFeedThrough :
    WeightPreservationBlocker

  missingYMClayAuthorityToken :
    WeightPreservationBlocker

canonicalWeightPreservationBlockers :
  List WeightPreservationBlocker
canonicalWeightPreservationBlockers =
  missingWeightFormula
  ∷ missingRepresentativeIndependenceProof
  ∷ missingInvolutionCompatibility
  ∷ missingOrientationSeparation
  ∷ missingGaugeInvarianceProof
  ∷ missingQuotientProjectionProof
  ∷ missingFluxCancellationConsumerProof
  ∷ inducedBallWeightRouteStillRejected
  ∷ missingSelfAdjointnessFeedThrough
  ∷ missingYMClayAuthorityToken
  ∷ []

record WeightPreservationTargetRow : Set where
  field
    obligation :
      WeightPreservationObligation

    label :
      String

    contractText :
      String

    provedHere :
      Bool

    provedHereIsFalse :
      provedHere ≡ false

open WeightPreservationTargetRow public

mkWeightPreservationTargetRow :
  WeightPreservationObligation →
  String →
  String →
  WeightPreservationTargetRow
mkWeightPreservationTargetRow obligation label contractText =
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

canonicalWeightPreservationTargetRows :
  List WeightPreservationTargetRow
canonicalWeightPreservationTargetRows =
  mkWeightPreservationTargetRow
    defineFullDegreeKillingWeightFormula
    "weight formula"
    "Define the full-degree/Killing weight on every admissible finite BT boundary face."
  ∷ mkWeightPreservationTargetRow
    proveWeightFormulaIndependentOfFaceRepresentative
    "representatives"
    "Prove the weight is independent of the chosen finite face representative in the gauge quotient carrier."
  ∷ mkWeightPreservationTargetRow
    proveOppositeFaceWeightEquality
    "weight equality"
    "Prove weight(opp F) = weight(F) for the opposite-face involution under the full-degree/Killing convention."
  ∷ mkWeightPreservationTargetRow
    proveOppositeFaceInvolutionCompatibility
    "involution compatibility"
    "Prove the equality is compatible with opp(opp F) = F and with the finite boundary face domain."
  ∷ mkWeightPreservationTargetRow
    proveOrientationNormalSignSeparatedFromWeight
    "orientation separation"
    "Separate positive weight preservation from normal sign reversal, so flux cancellation uses equal weights and opposite normals."
  ∷ mkWeightPreservationTargetRow
    proveGaugeActionPreservesWeights
    "gauge weights"
    "Prove finite gauge transformations preserve full-degree/Killing and local representation weights on paired faces."
  ∷ mkWeightPreservationTargetRow
    proveQuotientProjectionPreservesWeights
    "quotient projection"
    "Prove quotient representative projection does not change the paired-face weight equality."
  ∷ mkWeightPreservationTargetRow
    proveInducedBallWeightsRemainRejected
    "induced rejection"
    "Keep induced-ball weights rejected as current gap carriers because their exterior faces need not admit full-degree opposite partners."
  ∷ mkWeightPreservationTargetRow
    routeEqualWeightsIntoFluxCancellation
    "flux consumer"
    "Route weight equality, orientation reversal, and gauge compatibility into the Killing boundary flux-cancellation boundary."
  ∷ mkWeightPreservationTargetRow
    keepSelfAdjointnessAndPromotionSeparate
    "promotion guard"
    "Keep finite self-adjointness, Hamiltonian domination, OS transfer, YM Clay, and terminal promotion separate and false."
  ∷ []

------------------------------------------------------------------------
-- Boundary flags.

boundaryRecorded : Bool
boundaryRecorded =
  true

admissibleBoundaryImported : Bool
admissibleBoundaryImported =
  true

oppositeFaceInvolutionImported : Bool
oppositeFaceInvolutionImported =
  true

fluxCancellationBoundaryImported : Bool
fluxCancellationBoundaryImported =
  true

fullDegreeKillingConventionConsumed : Bool
fullDegreeKillingConventionConsumed =
  true

inducedBallWeightRouteRejected : Bool
inducedBallWeightRouteRejected =
  true

weightFormulaDefined : Bool
weightFormulaDefined =
  false

representativeIndependenceProved : Bool
representativeIndependenceProved =
  false

oppositeFaceWeightEqualityProved : Bool
oppositeFaceWeightEqualityProved =
  false

involutionCompatibilityProved : Bool
involutionCompatibilityProved =
  false

orientationNormalSignSeparationProved : Bool
orientationNormalSignSeparationProved =
  false

gaugeWeightInvarianceProved : Bool
gaugeWeightInvarianceProved =
  false

quotientWeightInvarianceProved : Bool
quotientWeightInvarianceProved =
  false

fluxCancellationConsumerProved : Bool
fluxCancellationConsumerProved =
  false

selfAdjointnessFeedThroughProved : Bool
selfAdjointnessFeedThroughProved =
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

oppositeFaceInvolutionImportedIsTrue :
  oppositeFaceInvolutionImported ≡ true
oppositeFaceInvolutionImportedIsTrue =
  refl

fluxCancellationBoundaryImportedIsTrue :
  fluxCancellationBoundaryImported ≡ true
fluxCancellationBoundaryImportedIsTrue =
  refl

fullDegreeKillingConventionConsumedIsTrue :
  fullDegreeKillingConventionConsumed ≡ true
fullDegreeKillingConventionConsumedIsTrue =
  refl

inducedBallWeightRouteRejectedIsTrue :
  inducedBallWeightRouteRejected ≡ true
inducedBallWeightRouteRejectedIsTrue =
  refl

weightFormulaDefinedIsFalse :
  weightFormulaDefined ≡ false
weightFormulaDefinedIsFalse =
  refl

representativeIndependenceProvedIsFalse :
  representativeIndependenceProved ≡ false
representativeIndependenceProvedIsFalse =
  refl

oppositeFaceWeightEqualityProvedIsFalse :
  oppositeFaceWeightEqualityProved ≡ false
oppositeFaceWeightEqualityProvedIsFalse =
  refl

involutionCompatibilityProvedIsFalse :
  involutionCompatibilityProved ≡ false
involutionCompatibilityProvedIsFalse =
  refl

orientationNormalSignSeparationProvedIsFalse :
  orientationNormalSignSeparationProved ≡ false
orientationNormalSignSeparationProvedIsFalse =
  refl

gaugeWeightInvarianceProvedIsFalse :
  gaugeWeightInvarianceProved ≡ false
gaugeWeightInvarianceProvedIsFalse =
  refl

quotientWeightInvarianceProvedIsFalse :
  quotientWeightInvarianceProved ≡ false
quotientWeightInvarianceProvedIsFalse =
  refl

fluxCancellationConsumerProvedIsFalse :
  fluxCancellationConsumerProved ≡ false
fluxCancellationConsumerProvedIsFalse =
  refl

selfAdjointnessFeedThroughProvedIsFalse :
  selfAdjointnessFeedThroughProved ≡ false
selfAdjointnessFeedThroughProvedIsFalse =
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

killingWeightPreservationFormula : String
killingWeightPreservationFormula =
  "weight_K(opp F) = weight_K(F), with normal(opp F) = -normal(F) handled as a separate orientation sign"

fluxCancellationConsumerFormula : String
fluxCancellationConsumerFormula =
  "weight equality + orientation sign reversal + gauge compatibility -> equal-weight opposite-sign boundary flux pair"

------------------------------------------------------------------------
-- Canonical child boundary receipt.

record YMKillingBoundaryWeightPreservationBoundary : Setω where
  field
    status :
      YMKillingBoundaryWeightPreservationStatus

    admissibleBoundary :
      Admissible.YMAdmissibleBTBoundaryConventionBoundary

    admissibleBoundaryCanonical :
      Bool

    admissibleBoundaryCanonicalIsTrue :
      admissibleBoundaryCanonical ≡ true

    oppositeFaceBoundary :
      Opposite.YMKillingBoundaryOppositeFaceInvolutionBoundary

    oppositeFaceBoundaryCanonical :
      Bool

    oppositeFaceBoundaryCanonicalIsTrue :
      oppositeFaceBoundaryCanonical ≡ true

    fluxCancellationBoundary :
      Flux.YMKillingBoundaryFluxCancellationBoundary

    fluxCancellationBoundaryCanonical :
      Bool

    fluxCancellationBoundaryCanonicalIsTrue :
      fluxCancellationBoundaryCanonical ≡ true

    weightCarriers :
      List KillingFullDegreeWeightCarrier

    weightCarriersAreCanonical :
      weightCarriers ≡ canonicalKillingFullDegreeWeightCarriers

    weightCarrierCount :
      Nat

    weightCarrierCountIs5 :
      weightCarrierCount ≡ 5

    oppositeInputs :
      List OppositeFaceWeightInput

    oppositeInputsAreCanonical :
      oppositeInputs ≡ canonicalOppositeFaceWeightInputs

    oppositeInputCount :
      Nat

    oppositeInputCountIs5 :
      oppositeInputCount ≡ 5

    mechanisms :
      List WeightPreservationMechanism

    mechanismsAreCanonical :
      mechanisms ≡ canonicalWeightPreservationMechanisms

    mechanismCount :
      Nat

    mechanismCountIs8 :
      mechanismCount ≡ 8

    consumers :
      List WeightPreservationConsumer

    consumersAreCanonical :
      consumers ≡ canonicalWeightPreservationConsumers

    consumerCount :
      Nat

    consumerCountIs8 :
      consumerCount ≡ 8

    obligations :
      List WeightPreservationObligation

    obligationsAreCanonical :
      obligations ≡ canonicalWeightPreservationObligations

    obligationCount :
      Nat

    obligationCountIs10 :
      obligationCount ≡ 10

    targetRows :
      List WeightPreservationTargetRow

    targetRowsAreCanonical :
      targetRows ≡ canonicalWeightPreservationTargetRows

    targetRowCount :
      Nat

    targetRowCountIs10 :
      targetRowCount ≡ 10

    blockers :
      List WeightPreservationBlocker

    blockersAreCanonical :
      blockers ≡ canonicalWeightPreservationBlockers

    blockerCount :
      Nat

    blockerCountIs10 :
      blockerCount ≡ 10

    firstBlocker :
      WeightPreservationBlocker

    firstBlockerIsMissingWeightFormula :
      firstBlocker ≡ missingWeightFormula

    formula :
      String

    formulaIsCanonical :
      formula ≡ killingWeightPreservationFormula

    consumerFormula :
      String

    consumerFormulaIsCanonical :
      consumerFormula ≡ fluxCancellationConsumerFormula

    boundaryRecordedField :
      Bool

    boundaryRecordedFieldIsTrue :
      boundaryRecordedField ≡ true

    fullDegreeKillingConventionConsumedField :
      Bool

    fullDegreeKillingConventionConsumedFieldIsTrue :
      fullDegreeKillingConventionConsumedField ≡ true

    inducedBallWeightRouteRejectedField :
      Bool

    inducedBallWeightRouteRejectedFieldIsTrue :
      inducedBallWeightRouteRejectedField ≡ true

    weightFormulaDefinedField :
      Bool

    weightFormulaDefinedFieldIsFalse :
      weightFormulaDefinedField ≡ false

    oppositeFaceWeightEqualityProvedField :
      Bool

    oppositeFaceWeightEqualityProvedFieldIsFalse :
      oppositeFaceWeightEqualityProvedField ≡ false

    involutionCompatibilityProvedField :
      Bool

    involutionCompatibilityProvedFieldIsFalse :
      involutionCompatibilityProvedField ≡ false

    orientationNormalSignSeparationProvedField :
      Bool

    orientationNormalSignSeparationProvedFieldIsFalse :
      orientationNormalSignSeparationProvedField ≡ false

    gaugeWeightInvarianceProvedField :
      Bool

    gaugeWeightInvarianceProvedFieldIsFalse :
      gaugeWeightInvarianceProvedField ≡ false

    fluxCancellationConsumerProvedField :
      Bool

    fluxCancellationConsumerProvedFieldIsFalse :
      fluxCancellationConsumerProvedField ≡ false

    selfAdjointnessFeedThroughProvedField :
      Bool

    selfAdjointnessFeedThroughProvedFieldIsFalse :
      selfAdjointnessFeedThroughProvedField ≡ false

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

    importedOppositeWeightStillOpen :
      Opposite.fullDegreeKillingWeightPreservationProvedField
        oppositeFaceBoundary
      ≡
      false

    importedOppositeOrientationStillOpen :
      Opposite.orientationSignCancellationProvedField
        oppositeFaceBoundary
      ≡
      false

    importedOppositeGaugeStillOpen :
      Opposite.gaugeCompatibilityProvedField
        oppositeFaceBoundary
      ≡
      false

    importedFluxWeightStillOpen :
      Flux.killingWeightPreservationProvedField
        fluxCancellationBoundary
      ≡
      false

    importedFluxCancellationStillOpen :
      Flux.oppositeNormalFluxCancellationProvedField
        fluxCancellationBoundary
      ≡
      false

    importedFluxSelfAdjointStillOpen :
      Flux.selfAdjointnessFeedThroughProvedField
        fluxCancellationBoundary
      ≡
      false

    notes :
      List String

open YMKillingBoundaryWeightPreservationBoundary public

canonicalYMKillingBoundaryWeightPreservationBoundary :
  YMKillingBoundaryWeightPreservationBoundary
canonicalYMKillingBoundaryWeightPreservationBoundary =
  record
    { status =
        killingBoundaryWeightPreservationBoundaryRecordedProofStillOpen
    ; admissibleBoundary =
        Admissible.canonicalYMAdmissibleBTBoundaryConventionBoundary
    ; admissibleBoundaryCanonical =
        true
    ; admissibleBoundaryCanonicalIsTrue =
        refl
    ; oppositeFaceBoundary =
        Opposite.canonicalYMKillingBoundaryOppositeFaceInvolutionBoundary
    ; oppositeFaceBoundaryCanonical =
        true
    ; oppositeFaceBoundaryCanonicalIsTrue =
        refl
    ; fluxCancellationBoundary =
        Flux.canonicalYMKillingBoundaryFluxCancellationBoundary
    ; fluxCancellationBoundaryCanonical =
        true
    ; fluxCancellationBoundaryCanonicalIsTrue =
        refl
    ; weightCarriers =
        canonicalKillingFullDegreeWeightCarriers
    ; weightCarriersAreCanonical =
        refl
    ; weightCarrierCount =
        listCount canonicalKillingFullDegreeWeightCarriers
    ; weightCarrierCountIs5 =
        refl
    ; oppositeInputs =
        canonicalOppositeFaceWeightInputs
    ; oppositeInputsAreCanonical =
        refl
    ; oppositeInputCount =
        listCount canonicalOppositeFaceWeightInputs
    ; oppositeInputCountIs5 =
        refl
    ; mechanisms =
        canonicalWeightPreservationMechanisms
    ; mechanismsAreCanonical =
        refl
    ; mechanismCount =
        listCount canonicalWeightPreservationMechanisms
    ; mechanismCountIs8 =
        refl
    ; consumers =
        canonicalWeightPreservationConsumers
    ; consumersAreCanonical =
        refl
    ; consumerCount =
        listCount canonicalWeightPreservationConsumers
    ; consumerCountIs8 =
        refl
    ; obligations =
        canonicalWeightPreservationObligations
    ; obligationsAreCanonical =
        refl
    ; obligationCount =
        listCount canonicalWeightPreservationObligations
    ; obligationCountIs10 =
        refl
    ; targetRows =
        canonicalWeightPreservationTargetRows
    ; targetRowsAreCanonical =
        refl
    ; targetRowCount =
        listCount canonicalWeightPreservationTargetRows
    ; targetRowCountIs10 =
        refl
    ; blockers =
        canonicalWeightPreservationBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCount =
        listCount canonicalWeightPreservationBlockers
    ; blockerCountIs10 =
        refl
    ; firstBlocker =
        missingWeightFormula
    ; firstBlockerIsMissingWeightFormula =
        refl
    ; formula =
        killingWeightPreservationFormula
    ; formulaIsCanonical =
        refl
    ; consumerFormula =
        fluxCancellationConsumerFormula
    ; consumerFormulaIsCanonical =
        refl
    ; boundaryRecordedField =
        boundaryRecorded
    ; boundaryRecordedFieldIsTrue =
        boundaryRecordedIsTrue
    ; fullDegreeKillingConventionConsumedField =
        fullDegreeKillingConventionConsumed
    ; fullDegreeKillingConventionConsumedFieldIsTrue =
        fullDegreeKillingConventionConsumedIsTrue
    ; inducedBallWeightRouteRejectedField =
        inducedBallWeightRouteRejected
    ; inducedBallWeightRouteRejectedFieldIsTrue =
        inducedBallWeightRouteRejectedIsTrue
    ; weightFormulaDefinedField =
        weightFormulaDefined
    ; weightFormulaDefinedFieldIsFalse =
        weightFormulaDefinedIsFalse
    ; oppositeFaceWeightEqualityProvedField =
        oppositeFaceWeightEqualityProved
    ; oppositeFaceWeightEqualityProvedFieldIsFalse =
        oppositeFaceWeightEqualityProvedIsFalse
    ; involutionCompatibilityProvedField =
        involutionCompatibilityProved
    ; involutionCompatibilityProvedFieldIsFalse =
        involutionCompatibilityProvedIsFalse
    ; orientationNormalSignSeparationProvedField =
        orientationNormalSignSeparationProved
    ; orientationNormalSignSeparationProvedFieldIsFalse =
        orientationNormalSignSeparationProvedIsFalse
    ; gaugeWeightInvarianceProvedField =
        gaugeWeightInvarianceProved
    ; gaugeWeightInvarianceProvedFieldIsFalse =
        gaugeWeightInvarianceProvedIsFalse
    ; fluxCancellationConsumerProvedField =
        fluxCancellationConsumerProved
    ; fluxCancellationConsumerProvedFieldIsFalse =
        fluxCancellationConsumerProvedIsFalse
    ; selfAdjointnessFeedThroughProvedField =
        selfAdjointnessFeedThroughProved
    ; selfAdjointnessFeedThroughProvedFieldIsFalse =
        selfAdjointnessFeedThroughProvedIsFalse
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
    ; importedOppositeWeightStillOpen =
        Opposite.canonicalOppositeFaceWeightPreservationStillFalse
    ; importedOppositeOrientationStillOpen =
        Opposite.canonicalOppositeFaceOrientationCancellationStillFalse
    ; importedOppositeGaugeStillOpen =
        Opposite.canonicalOppositeFaceGaugeCompatibilityStillFalse
    ; importedFluxWeightStillOpen =
        Flux.killingWeightPreservationProvedIsFalse
    ; importedFluxCancellationStillOpen =
        Flux.oppositeNormalFluxCancellationProvedIsFalse
    ; importedFluxSelfAdjointStillOpen =
        Flux.canonicalKillingBoundaryFluxSelfAdjointFeedStillFalse
    ; notes =
        "This child isolates full-degree/Killing weight preservation from the rest of the opposite-face involution proof."
        ∷ "The weight equality target is weight_K(opp F) = weight_K(F); normal sign reversal is tracked separately so weight preservation is not confused with orientation cancellation."
        ∷ "Gauge compatibility remains a separate blocker because finite gauge transformations must preserve both the paired faces and their weights before quotient self-adjointness can consume the result."
        ∷ "The only immediate consumer is the Killing boundary flux-cancellation boundary; finite self-adjointness, Hamiltonian domination, OS transfer, YM Clay, and terminal promotion remain false."
        ∷ []
    }

------------------------------------------------------------------------
-- Guard lemmas.

canonicalWeightCarrierCountIs5 :
  weightCarrierCount canonicalYMKillingBoundaryWeightPreservationBoundary
  ≡
  5
canonicalWeightCarrierCountIs5 =
  refl

canonicalWeightMechanismCountIs8 :
  mechanismCount canonicalYMKillingBoundaryWeightPreservationBoundary
  ≡
  8
canonicalWeightMechanismCountIs8 =
  refl

canonicalWeightObligationCountIs10 :
  obligationCount canonicalYMKillingBoundaryWeightPreservationBoundary
  ≡
  10
canonicalWeightObligationCountIs10 =
  refl

canonicalWeightFirstBlocker :
  firstBlocker canonicalYMKillingBoundaryWeightPreservationBoundary
  ≡
  missingWeightFormula
canonicalWeightFirstBlocker =
  refl

canonicalWeightFormulaStillFalse :
  weightFormulaDefinedField canonicalYMKillingBoundaryWeightPreservationBoundary
  ≡
  false
canonicalWeightFormulaStillFalse =
  refl

canonicalWeightEqualityStillFalse :
  oppositeFaceWeightEqualityProvedField
    canonicalYMKillingBoundaryWeightPreservationBoundary
  ≡
  false
canonicalWeightEqualityStillFalse =
  refl

canonicalWeightInvolutionCompatibilityStillFalse :
  involutionCompatibilityProvedField
    canonicalYMKillingBoundaryWeightPreservationBoundary
  ≡
  false
canonicalWeightInvolutionCompatibilityStillFalse =
  refl

canonicalWeightOrientationSeparationStillFalse :
  orientationNormalSignSeparationProvedField
    canonicalYMKillingBoundaryWeightPreservationBoundary
  ≡
  false
canonicalWeightOrientationSeparationStillFalse =
  refl

canonicalWeightGaugeInvarianceStillFalse :
  gaugeWeightInvarianceProvedField
    canonicalYMKillingBoundaryWeightPreservationBoundary
  ≡
  false
canonicalWeightGaugeInvarianceStillFalse =
  refl

canonicalWeightFluxConsumerStillFalse :
  fluxCancellationConsumerProvedField
    canonicalYMKillingBoundaryWeightPreservationBoundary
  ≡
  false
canonicalWeightFluxConsumerStillFalse =
  refl

canonicalWeightSelfAdjointFeedStillFalse :
  selfAdjointnessFeedThroughProvedField
    canonicalYMKillingBoundaryWeightPreservationBoundary
  ≡
  false
canonicalWeightSelfAdjointFeedStillFalse =
  refl

canonicalWeightYMClayStillFalse :
  ymClayPromotedField canonicalYMKillingBoundaryWeightPreservationBoundary
  ≡
  false
canonicalWeightYMClayStillFalse =
  refl

canonicalWeightTerminalStillFalse :
  terminalPromotionField canonicalYMKillingBoundaryWeightPreservationBoundary
  ≡
  false
canonicalWeightTerminalStillFalse =
  refl

data YMKillingBoundaryWeightPreservationPromotionToken : Set where

ymKillingBoundaryWeightPreservationPromotionTokenImpossibleHere :
  YMKillingBoundaryWeightPreservationPromotionToken →
  ⊥
ymKillingBoundaryWeightPreservationPromotionTokenImpossibleHere ()

noWeightFormulaPromotionFromBoundaryRecordAlone :
  weightFormulaDefinedField canonicalYMKillingBoundaryWeightPreservationBoundary
  ≡
  true →
  ⊥
noWeightFormulaPromotionFromBoundaryRecordAlone ()

noWeightEqualityPromotionFromBoundaryRecordAlone :
  oppositeFaceWeightEqualityProvedField
    canonicalYMKillingBoundaryWeightPreservationBoundary
  ≡
  true →
  ⊥
noWeightEqualityPromotionFromBoundaryRecordAlone ()

noFluxCancellationPromotionFromWeightBoundaryAlone :
  fluxCancellationConsumerProvedField
    canonicalYMKillingBoundaryWeightPreservationBoundary
  ≡
  true →
  ⊥
noFluxCancellationPromotionFromWeightBoundaryAlone ()

noYMClayPromotionFromWeightBoundaryAlone :
  ymClayPromotedField canonicalYMKillingBoundaryWeightPreservationBoundary
  ≡
  true →
  ⊥
noYMClayPromotionFromWeightBoundaryAlone ()

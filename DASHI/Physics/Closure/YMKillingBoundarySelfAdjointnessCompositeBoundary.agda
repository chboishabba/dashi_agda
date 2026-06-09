module DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessCompositeBoundary where

-- Composite boundary for the YM-1 Killing/full-degree finite
-- self-adjointness route.
--
-- The child modules below isolate the boundary mechanism needed before a
-- finite Hamiltonian on the gauge quotient can be promoted to a genuine
-- self-adjoint operator theorem:
--
--   opposite-face involution
--   weight preservation
--   orientation cancellation
--   flux cancellation
--   gauge-domain preservation
--   self-adjointness domain contract
--
-- This module composes those surfaces as a route ledger only.  It records the
-- path to the finite self-adjoint Hamiltonian on the gauge quotient, but it
-- does not prove the YM-1 theorem, does not prove Hamiltonian domination, does
-- not prove OS/continuum transfer, and keeps YM Clay / terminal promotion
-- false.

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
import DASHI.Physics.Closure.YMKillingBoundaryWeightPreservationBoundary
  as Weight
import DASHI.Physics.Closure.YMKillingBoundaryOrientationCancellationBoundary
  as Orientation
import DASHI.Physics.Closure.YMKillingBoundaryGaugeDomainPreservationBoundary
  as GaugeDomain
import DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessDomainContract
  as DomainContract
import DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessProxyHarnessResult
  as Harness

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Imported anchors.

record YMKillingBoundarySelfAdjointnessCompositeSupport : Setω where
  field
    fluxCancellationBoundary :
      Flux.YMKillingBoundaryFluxCancellationBoundary

    fluxCancellationBoundaryCanonical :
      Bool

    fluxCancellationBoundaryCanonicalIsTrue :
      fluxCancellationBoundaryCanonical ≡ true

    oppositeFaceInvolutionBoundary :
      Opposite.YMKillingBoundaryOppositeFaceInvolutionBoundary

    oppositeFaceInvolutionBoundaryCanonical :
      Bool

    oppositeFaceInvolutionBoundaryCanonicalIsTrue :
      oppositeFaceInvolutionBoundaryCanonical ≡ true

    weightPreservationBoundary :
      Weight.YMKillingBoundaryWeightPreservationBoundary

    weightPreservationBoundaryCanonical :
      Bool

    weightPreservationBoundaryCanonicalIsTrue :
      weightPreservationBoundaryCanonical ≡ true

    orientationCancellationBoundary :
      Orientation.YMKillingBoundaryOrientationCancellationBoundary

    orientationCancellationBoundaryCanonical :
      Bool

    orientationCancellationBoundaryCanonicalIsTrue :
      orientationCancellationBoundaryCanonical ≡ true

    gaugeDomainPreservationBoundary :
      GaugeDomain.YMKillingBoundaryGaugeDomainPreservationBoundary

    gaugeDomainPreservationBoundaryCanonical :
      Bool

    gaugeDomainPreservationBoundaryCanonicalIsTrue :
      gaugeDomainPreservationBoundaryCanonical ≡ true

    selfAdjointnessDomainContract :
      DomainContract.YMKillingBoundarySelfAdjointnessDomainContract

    selfAdjointnessDomainContractCanonical :
      Bool

    selfAdjointnessDomainContractCanonicalIsTrue :
      selfAdjointnessDomainContractCanonical ≡ true

    proxyHarness :
      Harness.YMKillingBoundarySelfAdjointnessProxyHarnessResult

    proxyHarnessCanonical :
      Bool

    proxyHarnessCanonicalIsTrue :
      proxyHarnessCanonical ≡ true

open YMKillingBoundarySelfAdjointnessCompositeSupport public

canonicalYMKillingBoundarySelfAdjointnessCompositeSupport :
  YMKillingBoundarySelfAdjointnessCompositeSupport
canonicalYMKillingBoundarySelfAdjointnessCompositeSupport =
  record
    { fluxCancellationBoundary =
        Flux.canonicalYMKillingBoundaryFluxCancellationBoundary
    ; fluxCancellationBoundaryCanonical =
        true
    ; fluxCancellationBoundaryCanonicalIsTrue =
        refl
    ; oppositeFaceInvolutionBoundary =
        Opposite.canonicalYMKillingBoundaryOppositeFaceInvolutionBoundary
    ; oppositeFaceInvolutionBoundaryCanonical =
        true
    ; oppositeFaceInvolutionBoundaryCanonicalIsTrue =
        refl
    ; weightPreservationBoundary =
        Weight.canonicalYMKillingBoundaryWeightPreservationBoundary
    ; weightPreservationBoundaryCanonical =
        true
    ; weightPreservationBoundaryCanonicalIsTrue =
        refl
    ; orientationCancellationBoundary =
        Orientation.canonicalYMKillingBoundaryOrientationCancellationBoundary
    ; orientationCancellationBoundaryCanonical =
        true
    ; orientationCancellationBoundaryCanonicalIsTrue =
        refl
    ; gaugeDomainPreservationBoundary =
        GaugeDomain.canonicalYMKillingBoundaryGaugeDomainPreservationBoundary
    ; gaugeDomainPreservationBoundaryCanonical =
        true
    ; gaugeDomainPreservationBoundaryCanonicalIsTrue =
        refl
    ; selfAdjointnessDomainContract =
        DomainContract.canonicalYMKillingBoundarySelfAdjointnessDomainContract
    ; selfAdjointnessDomainContractCanonical =
        true
    ; selfAdjointnessDomainContractCanonicalIsTrue =
        refl
    ; proxyHarness =
        Harness.canonicalYMKillingBoundarySelfAdjointnessProxyHarnessResult
    ; proxyHarnessCanonical =
        true
    ; proxyHarnessCanonicalIsTrue =
        refl
    }

data YMKillingBoundaryCompositeInput : Set where
  fluxCancellationInput :
    YMKillingBoundaryCompositeInput

  oppositeFaceInvolutionInput :
    YMKillingBoundaryCompositeInput

  weightPreservationInput :
    YMKillingBoundaryCompositeInput

  orientationCancellationInput :
    YMKillingBoundaryCompositeInput

  gaugeDomainPreservationInput :
    YMKillingBoundaryCompositeInput

  selfAdjointnessDomainContractInput :
    YMKillingBoundaryCompositeInput

  diagnosticHarnessInput :
    YMKillingBoundaryCompositeInput

canonicalYMKillingBoundaryCompositeInputs :
  List YMKillingBoundaryCompositeInput
canonicalYMKillingBoundaryCompositeInputs =
  fluxCancellationInput
  ∷ oppositeFaceInvolutionInput
  ∷ weightPreservationInput
  ∷ orientationCancellationInput
  ∷ gaugeDomainPreservationInput
  ∷ selfAdjointnessDomainContractInput
  ∷ diagnosticHarnessInput
  ∷ []

------------------------------------------------------------------------
-- Composite route.

data YMKillingBoundarySelfAdjointnessCompositeStatus : Set where
  ym1KillingBoundaryCompositeRecordedProofStillOpen :
    YMKillingBoundarySelfAdjointnessCompositeStatus

data YMKillingBoundarySelfAdjointnessRouteStage : Set where
  chooseFullDegreeKillingBoundary :
    YMKillingBoundarySelfAdjointnessRouteStage

  constructOppositeFaceInvolution :
    YMKillingBoundarySelfAdjointnessRouteStage

  proveOppositeFaceWeightPreservation :
    YMKillingBoundarySelfAdjointnessRouteStage

  proveOrientationNormalCancellation :
    YMKillingBoundarySelfAdjointnessRouteStage

  proveFiniteBoundaryFluxCancellation :
    YMKillingBoundarySelfAdjointnessRouteStage

  proveGaugeActionPreservesKillingDomain :
    YMKillingBoundarySelfAdjointnessRouteStage

  proveGaugeInvariantProjectionDomainDescent :
    YMKillingBoundarySelfAdjointnessRouteStage

  proveHamiltonianActionOnGaugeQuotient :
    YMKillingBoundarySelfAdjointnessRouteStage

  proveSymmetricFiniteMatrixByIBP :
    YMKillingBoundarySelfAdjointnessRouteStage

  proveFiniteSelfAdjointHamiltonianOnGaugeQuotient :
    YMKillingBoundarySelfAdjointnessRouteStage

  feedHamiltonianDominationOnlyAfterFiniteTheorem :
    YMKillingBoundarySelfAdjointnessRouteStage

  keepOSContinuumAndClaySeparate :
    YMKillingBoundarySelfAdjointnessRouteStage

canonicalYMKillingBoundarySelfAdjointnessRoute :
  List YMKillingBoundarySelfAdjointnessRouteStage
canonicalYMKillingBoundarySelfAdjointnessRoute =
  chooseFullDegreeKillingBoundary
  ∷ constructOppositeFaceInvolution
  ∷ proveOppositeFaceWeightPreservation
  ∷ proveOrientationNormalCancellation
  ∷ proveFiniteBoundaryFluxCancellation
  ∷ proveGaugeActionPreservesKillingDomain
  ∷ proveGaugeInvariantProjectionDomainDescent
  ∷ proveHamiltonianActionOnGaugeQuotient
  ∷ proveSymmetricFiniteMatrixByIBP
  ∷ proveFiniteSelfAdjointHamiltonianOnGaugeQuotient
  ∷ feedHamiltonianDominationOnlyAfterFiniteTheorem
  ∷ keepOSContinuumAndClaySeparate
  ∷ []

data YMKillingBoundarySelfAdjointnessRouteStatus : Set where
  importedBoundaryVocabularyRecorded :
    YMKillingBoundarySelfAdjointnessRouteStatus

  childTheoremStillOpen :
    YMKillingBoundarySelfAdjointnessRouteStatus

  quotientSelfAdjointnessStillOpen :
    YMKillingBoundarySelfAdjointnessRouteStatus

  downstreamTheoremStillOpen :
    YMKillingBoundarySelfAdjointnessRouteStatus

  promotionHeldFalse :
    YMKillingBoundarySelfAdjointnessRouteStatus

ymKillingBoundaryRouteStatus :
  YMKillingBoundarySelfAdjointnessRouteStage →
  YMKillingBoundarySelfAdjointnessRouteStatus
ymKillingBoundaryRouteStatus chooseFullDegreeKillingBoundary =
  importedBoundaryVocabularyRecorded
ymKillingBoundaryRouteStatus constructOppositeFaceInvolution =
  childTheoremStillOpen
ymKillingBoundaryRouteStatus proveOppositeFaceWeightPreservation =
  childTheoremStillOpen
ymKillingBoundaryRouteStatus proveOrientationNormalCancellation =
  childTheoremStillOpen
ymKillingBoundaryRouteStatus proveFiniteBoundaryFluxCancellation =
  childTheoremStillOpen
ymKillingBoundaryRouteStatus proveGaugeActionPreservesKillingDomain =
  childTheoremStillOpen
ymKillingBoundaryRouteStatus proveGaugeInvariantProjectionDomainDescent =
  childTheoremStillOpen
ymKillingBoundaryRouteStatus proveHamiltonianActionOnGaugeQuotient =
  quotientSelfAdjointnessStillOpen
ymKillingBoundaryRouteStatus proveSymmetricFiniteMatrixByIBP =
  quotientSelfAdjointnessStillOpen
ymKillingBoundaryRouteStatus proveFiniteSelfAdjointHamiltonianOnGaugeQuotient =
  quotientSelfAdjointnessStillOpen
ymKillingBoundaryRouteStatus feedHamiltonianDominationOnlyAfterFiniteTheorem =
  downstreamTheoremStillOpen
ymKillingBoundaryRouteStatus keepOSContinuumAndClaySeparate =
  promotionHeldFalse

data YMKillingBoundarySelfAdjointnessCompositeBlocker : Set where
  missingOppositeFaceInvolutionComposite :
    YMKillingBoundarySelfAdjointnessCompositeBlocker

  missingKillingWeightPreservationComposite :
    YMKillingBoundarySelfAdjointnessCompositeBlocker

  missingOrientationCancellationComposite :
    YMKillingBoundarySelfAdjointnessCompositeBlocker

  missingFluxCancellationComposite :
    YMKillingBoundarySelfAdjointnessCompositeBlocker

  missingGaugeDomainPreservationComposite :
    YMKillingBoundarySelfAdjointnessCompositeBlocker

  missingQuotientDomainDescentComposite :
    YMKillingBoundarySelfAdjointnessCompositeBlocker

  missingHamiltonianActionOnGaugeQuotientComposite :
    YMKillingBoundarySelfAdjointnessCompositeBlocker

  missingSymmetricFiniteMatrixIBPComposite :
    YMKillingBoundarySelfAdjointnessCompositeBlocker

  missingFiniteSelfAdjointHamiltonianComposite :
    YMKillingBoundarySelfAdjointnessCompositeBlocker

  missingHamiltonianDominationComposite :
    YMKillingBoundarySelfAdjointnessCompositeBlocker

  missingOSTransferComposite :
    YMKillingBoundarySelfAdjointnessCompositeBlocker

  missingYMClayAuthorityTokenComposite :
    YMKillingBoundarySelfAdjointnessCompositeBlocker

canonicalYMKillingBoundarySelfAdjointnessCompositeBlockers :
  List YMKillingBoundarySelfAdjointnessCompositeBlocker
canonicalYMKillingBoundarySelfAdjointnessCompositeBlockers =
  missingOppositeFaceInvolutionComposite
  ∷ missingKillingWeightPreservationComposite
  ∷ missingOrientationCancellationComposite
  ∷ missingFluxCancellationComposite
  ∷ missingGaugeDomainPreservationComposite
  ∷ missingQuotientDomainDescentComposite
  ∷ missingHamiltonianActionOnGaugeQuotientComposite
  ∷ missingSymmetricFiniteMatrixIBPComposite
  ∷ missingFiniteSelfAdjointHamiltonianComposite
  ∷ missingHamiltonianDominationComposite
  ∷ missingOSTransferComposite
  ∷ missingYMClayAuthorityTokenComposite
  ∷ []

------------------------------------------------------------------------
-- Composite flags.

compositeBoundaryRecorded : Bool
compositeBoundaryRecorded =
  true

ym1FiniteSelfAdjointHamiltonianProved : Bool
ym1FiniteSelfAdjointHamiltonianProved =
  false

gaugeQuotientHamiltonianRouteRecorded : Bool
gaugeQuotientHamiltonianRouteRecorded =
  true

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

compositeBoundaryRecordedIsTrue :
  compositeBoundaryRecorded ≡ true
compositeBoundaryRecordedIsTrue =
  refl

ym1FiniteSelfAdjointHamiltonianProvedIsFalse :
  ym1FiniteSelfAdjointHamiltonianProved ≡ false
ym1FiniteSelfAdjointHamiltonianProvedIsFalse =
  refl

gaugeQuotientHamiltonianRouteRecordedIsTrue :
  gaugeQuotientHamiltonianRouteRecorded ≡ true
gaugeQuotientHamiltonianRouteRecordedIsTrue =
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

gaugeQuotientHamiltonianRouteFormula : String
gaugeQuotientHamiltonianRouteFormula =
  "opposite faces + equal Killing weights + opposite normals + gauge-domain descent + finite IBP symmetry -> finite self-adjoint Hamiltonian on the gauge quotient"

------------------------------------------------------------------------
-- Composite receipt.

record YMKillingBoundarySelfAdjointnessCompositeBoundary : Setω where
  field
    status :
      YMKillingBoundarySelfAdjointnessCompositeStatus

    support :
      YMKillingBoundarySelfAdjointnessCompositeSupport

    supportCanonical :
      Bool

    supportCanonicalIsTrue :
      supportCanonical ≡ true

    inputs :
      List YMKillingBoundaryCompositeInput

    inputsAreCanonical :
      inputs ≡ canonicalYMKillingBoundaryCompositeInputs

    inputCount :
      Nat

    inputCountIs7 :
      inputCount ≡ 7

    route :
      List YMKillingBoundarySelfAdjointnessRouteStage

    routeIsCanonical :
      route ≡ canonicalYMKillingBoundarySelfAdjointnessRoute

    routeCount :
      Nat

    routeCountIs12 :
      routeCount ≡ 12

    blockers :
      List YMKillingBoundarySelfAdjointnessCompositeBlocker

    blockersAreCanonical :
      blockers
      ≡
      canonicalYMKillingBoundarySelfAdjointnessCompositeBlockers

    blockerCount :
      Nat

    blockerCountIs12 :
      blockerCount ≡ 12

    firstBlocker :
      YMKillingBoundarySelfAdjointnessCompositeBlocker

    firstBlockerIsOppositeFaceInvolution :
      firstBlocker ≡ missingOppositeFaceInvolutionComposite

    routeFormula :
      String

    routeFormulaIsCanonical :
      routeFormula ≡ gaugeQuotientHamiltonianRouteFormula

    compositeBoundaryRecordedField :
      Bool

    compositeBoundaryRecordedFieldIsTrue :
      compositeBoundaryRecordedField ≡ true

    gaugeQuotientHamiltonianRouteRecordedField :
      Bool

    gaugeQuotientHamiltonianRouteRecordedFieldIsTrue :
      gaugeQuotientHamiltonianRouteRecordedField ≡ true

    ym1FiniteSelfAdjointHamiltonianProvedField :
      Bool

    ym1FiniteSelfAdjointHamiltonianProvedFieldIsFalse :
      ym1FiniteSelfAdjointHamiltonianProvedField ≡ false

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

    importedOppositeFaceInvolutionStillOpen :
      Opposite.oppositeFaceMapInvolutiveProvedField
        (oppositeFaceInvolutionBoundary support)
      ≡
      false

    importedWeightPreservationStillOpen :
      Weight.oppositeFaceWeightEqualityProvedField
        (weightPreservationBoundary support)
      ≡
      false

    importedOrientationCancellationStillOpen :
      Orientation.orientationNormalFluxCancellationProvedField
        (orientationCancellationBoundary support)
      ≡
      false

    importedFluxCancellationStillOpen :
      Flux.oppositeNormalFluxCancellationProvedField
        (fluxCancellationBoundary support)
      ≡
      false

    importedFluxSelfAdjointFeedStillOpen :
      Flux.selfAdjointnessFeedThroughProvedField
        (fluxCancellationBoundary support)
      ≡
      false

    importedGaugeDomainPreservationStillOpen :
      GaugeDomain.gaugeActionDomainPreservationProvedField
        (gaugeDomainPreservationBoundary support)
      ≡
      false

    importedGaugeQuotientDescentStillOpen :
      GaugeDomain.quotientDomainDescentProvedField
        (gaugeDomainPreservationBoundary support)
      ≡
      false

    importedGaugeSelfAdjointConsumerStillOpen :
      GaugeDomain.selfAdjointnessConsumerProvedField
        (gaugeDomainPreservationBoundary support)
      ≡
      false

    importedDomainContractFluxStillOpen :
      DomainContract.boundaryFluxCancellationProvedField
        (selfAdjointnessDomainContract support)
      ≡
      false

    importedDomainContractSelfAdjointStillOpen :
      DomainContract.selfAdjointQuotientHamiltonianProvedField
        (selfAdjointnessDomainContract support)
      ≡
      false

    importedDomainContractDominationStillOpen :
      DomainContract.hamiltonianDominationProvedField
        (selfAdjointnessDomainContract support)
      ≡
      false

    importedHarnessDiagnosticOnly :
      Harness.promotionFlag (proxyHarness support) ≡ false

    importedHarnessYM1SelfAdjointStillOpen :
      Harness.ym1KillingBoundarySelfAdjointnessProved ≡ false

    importedHarnessDominationStillOpen :
      Harness.hamiltonianDominationProved ≡ false

    importedHarnessOSTransferStillOpen :
      Harness.osTransferProved ≡ false

    importedChildClayFlagsStillFalse :
      List Bool

    importedChildClayFlagsStillFalseAreCanonical :
      importedChildClayFlagsStillFalse
      ≡
      ( Opposite.ymClayPromotedField
          (oppositeFaceInvolutionBoundary support)
        ∷ Weight.ymClayPromotedField
          (weightPreservationBoundary support)
        ∷ Orientation.ymClayPromotedField
          (orientationCancellationBoundary support)
        ∷ Flux.ymClayPromotedField
          (fluxCancellationBoundary support)
        ∷ GaugeDomain.ymClayPromotedField
          (gaugeDomainPreservationBoundary support)
        ∷ DomainContract.ymClayPromotedField
          (selfAdjointnessDomainContract support)
        ∷ [] )

    notes :
      List String

open YMKillingBoundarySelfAdjointnessCompositeBoundary public

canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary :
  YMKillingBoundarySelfAdjointnessCompositeBoundary
canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary =
  record
    { status =
        ym1KillingBoundaryCompositeRecordedProofStillOpen
    ; support =
        canonicalYMKillingBoundarySelfAdjointnessCompositeSupport
    ; supportCanonical =
        true
    ; supportCanonicalIsTrue =
        refl
    ; inputs =
        canonicalYMKillingBoundaryCompositeInputs
    ; inputsAreCanonical =
        refl
    ; inputCount =
        listCount canonicalYMKillingBoundaryCompositeInputs
    ; inputCountIs7 =
        refl
    ; route =
        canonicalYMKillingBoundarySelfAdjointnessRoute
    ; routeIsCanonical =
        refl
    ; routeCount =
        listCount canonicalYMKillingBoundarySelfAdjointnessRoute
    ; routeCountIs12 =
        refl
    ; blockers =
        canonicalYMKillingBoundarySelfAdjointnessCompositeBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCount =
        listCount canonicalYMKillingBoundarySelfAdjointnessCompositeBlockers
    ; blockerCountIs12 =
        refl
    ; firstBlocker =
        missingOppositeFaceInvolutionComposite
    ; firstBlockerIsOppositeFaceInvolution =
        refl
    ; routeFormula =
        gaugeQuotientHamiltonianRouteFormula
    ; routeFormulaIsCanonical =
        refl
    ; compositeBoundaryRecordedField =
        compositeBoundaryRecorded
    ; compositeBoundaryRecordedFieldIsTrue =
        compositeBoundaryRecordedIsTrue
    ; gaugeQuotientHamiltonianRouteRecordedField =
        gaugeQuotientHamiltonianRouteRecorded
    ; gaugeQuotientHamiltonianRouteRecordedFieldIsTrue =
        gaugeQuotientHamiltonianRouteRecordedIsTrue
    ; ym1FiniteSelfAdjointHamiltonianProvedField =
        ym1FiniteSelfAdjointHamiltonianProved
    ; ym1FiniteSelfAdjointHamiltonianProvedFieldIsFalse =
        ym1FiniteSelfAdjointHamiltonianProvedIsFalse
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
    ; importedOppositeFaceInvolutionStillOpen =
        Opposite.canonicalOppositeFaceInvolutionStillFalse
    ; importedWeightPreservationStillOpen =
        Weight.canonicalWeightEqualityStillFalse
    ; importedOrientationCancellationStillOpen =
        Orientation.orientationNormalFluxCancellationProvedIsFalse
    ; importedFluxCancellationStillOpen =
        Flux.canonicalKillingBoundaryFluxCancellationStillFalse
    ; importedFluxSelfAdjointFeedStillOpen =
        Flux.canonicalKillingBoundaryFluxSelfAdjointFeedStillFalse
    ; importedGaugeDomainPreservationStillOpen =
        GaugeDomain.canonicalGaugeDomainPreservationStillFalse
    ; importedGaugeQuotientDescentStillOpen =
        GaugeDomain.canonicalGaugeQuotientDescentStillFalse
    ; importedGaugeSelfAdjointConsumerStillOpen =
        GaugeDomain.canonicalGaugeSelfAdjointConsumerStillFalse
    ; importedDomainContractFluxStillOpen =
        DomainContract.boundaryFluxCancellationProvedFieldIsFalse
          DomainContract.canonicalYMKillingBoundarySelfAdjointnessDomainContract
    ; importedDomainContractSelfAdjointStillOpen =
        DomainContract.canonicalKillingBoundaryDomainSelfAdjointStillFalse
    ; importedDomainContractDominationStillOpen =
        DomainContract.canonicalKillingBoundaryDomainDominationStillFalse
    ; importedHarnessDiagnosticOnly =
        Harness.promotion_is_false
    ; importedHarnessYM1SelfAdjointStillOpen =
        Harness.ym1KillingBoundarySelfAdjointnessProvedIsFalse
    ; importedHarnessDominationStillOpen =
        Harness.hamiltonianDominationProvedIsFalse
    ; importedHarnessOSTransferStillOpen =
        Harness.osTransferProvedIsFalse
    ; importedChildClayFlagsStillFalse =
        false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ []
    ; importedChildClayFlagsStillFalseAreCanonical =
        refl
    ; notes =
        "YM-1 finite self-adjointness is routed through six typed child boundary surfaces plus the self-adjointness domain contract."
        ∷ "The finite gauge quotient Hamiltonian target remains a theorem obligation: the route needs opposite-face involution, Killing weight equality, orientation sign cancellation, flux cancellation, gauge-domain preservation, quotient descent, and finite IBP symmetry."
        ∷ "The proxy harness is diagnostic only and agrees that YM-1 Killing-boundary self-adjointness has not been proved."
        ∷ "Hamiltonian domination, OS transfer, continuum transfer, YM Clay, and terminal promotion remain downstream and false."
        ∷ []
    }

------------------------------------------------------------------------
-- Guard lemmas.

canonicalCompositeInputCountIs7 :
  inputCount canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary
  ≡
  7
canonicalCompositeInputCountIs7 =
  refl

canonicalCompositeRouteCountIs12 :
  routeCount canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary
  ≡
  12
canonicalCompositeRouteCountIs12 =
  refl

canonicalCompositeBlockerCountIs12 :
  blockerCount canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary
  ≡
  12
canonicalCompositeBlockerCountIs12 =
  refl

canonicalCompositeFirstBlocker :
  firstBlocker canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary
  ≡
  missingOppositeFaceInvolutionComposite
canonicalCompositeFirstBlocker =
  refl

canonicalCompositeYM1FiniteSelfAdjointHamiltonianFalse :
  ym1FiniteSelfAdjointHamiltonianProvedField
    canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary
  ≡
  false
canonicalCompositeYM1FiniteSelfAdjointHamiltonianFalse =
  refl

canonicalCompositeHamiltonianDominationFalse :
  hamiltonianDominationProvedField
    canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary
  ≡
  false
canonicalCompositeHamiltonianDominationFalse =
  refl

canonicalCompositeOSTransferFalse :
  osContinuumTransferProvedField
    canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary
  ≡
  false
canonicalCompositeOSTransferFalse =
  refl

canonicalCompositeYMClayFalse :
  ymClayPromotedField
    canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary
  ≡
  false
canonicalCompositeYMClayFalse =
  refl

canonicalCompositeTerminalFalse :
  terminalPromotionField
    canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary
  ≡
  false
canonicalCompositeTerminalFalse =
  refl

data YMKillingBoundaryCompositePromotionToken : Set where

ymKillingBoundaryCompositePromotionTokenImpossibleHere :
  YMKillingBoundaryCompositePromotionToken →
  ⊥
ymKillingBoundaryCompositePromotionTokenImpossibleHere ()

noYM1FiniteSelfAdjointPromotionFromCompositeBoundaryAlone :
  ym1FiniteSelfAdjointHamiltonianProvedField
    canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary
  ≡
  true →
  ⊥
noYM1FiniteSelfAdjointPromotionFromCompositeBoundaryAlone ()

noHamiltonianDominationPromotionFromCompositeBoundaryAlone :
  hamiltonianDominationProvedField
    canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary
  ≡
  true →
  ⊥
noHamiltonianDominationPromotionFromCompositeBoundaryAlone ()

noOSTransferPromotionFromCompositeBoundaryAlone :
  osContinuumTransferProvedField
    canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary
  ≡
  true →
  ⊥
noOSTransferPromotionFromCompositeBoundaryAlone ()

noYMClayPromotionFromCompositeBoundaryAlone :
  ymClayPromotedField
    canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary
  ≡
  true →
  ⊥
noYMClayPromotionFromCompositeBoundaryAlone ()

ogfControlCard : String
ogfControlCard =
  "O YM-1 Killing-boundary finite self-adjointness composite; R route finite gauge-quotient Hamiltonian self-adjointness through opposite-face, weight, orientation, flux, gauge-domain, and domain-contract surfaces; C imports six child boundaries plus diagnostic harness; S route recorded true while YM-1 proof, Hamiltonian domination, OS transfer, YM Clay, and terminal promotion are false; L child blockers remain ordered before quotient self-adjointness and domination consumers; P prove child theorems before attempting finite self-adjoint Hamiltonian; G no promotion token is introduced; F composite is a fail-closed boundary ledger only."

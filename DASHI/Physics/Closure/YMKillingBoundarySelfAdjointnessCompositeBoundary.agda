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
import DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessTheoremBoundary
  as Theorem

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

    theoremBoundary :
      Theorem.YMKillingBoundarySelfAdjointnessTheoremBoundary

    theoremBoundaryCanonical :
      Bool

    theoremBoundaryCanonicalIsTrue :
      theoremBoundaryCanonical ≡ true

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
    ; theoremBoundary =
        Theorem.canonicalYMKillingBoundarySelfAdjointnessTheoremBoundary
    ; theoremBoundaryCanonical =
        true
    ; theoremBoundaryCanonicalIsTrue =
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
  ym1KillingBoundaryCompositeFiniteSelfAdjointnessProved :
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

  childTheoremProved :
    YMKillingBoundarySelfAdjointnessRouteStatus

  quotientSelfAdjointnessStillOpen :
    YMKillingBoundarySelfAdjointnessRouteStatus

  quotientSelfAdjointnessProved :
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
  childTheoremProved
ymKillingBoundaryRouteStatus proveOppositeFaceWeightPreservation =
  childTheoremProved
ymKillingBoundaryRouteStatus proveOrientationNormalCancellation =
  childTheoremProved
ymKillingBoundaryRouteStatus proveFiniteBoundaryFluxCancellation =
  childTheoremProved
ymKillingBoundaryRouteStatus proveGaugeActionPreservesKillingDomain =
  childTheoremProved
ymKillingBoundaryRouteStatus proveGaugeInvariantProjectionDomainDescent =
  childTheoremProved
ymKillingBoundaryRouteStatus proveHamiltonianActionOnGaugeQuotient =
  quotientSelfAdjointnessProved
ymKillingBoundaryRouteStatus proveSymmetricFiniteMatrixByIBP =
  quotientSelfAdjointnessProved
ymKillingBoundaryRouteStatus proveFiniteSelfAdjointHamiltonianOnGaugeQuotient =
  quotientSelfAdjointnessProved
ymKillingBoundaryRouteStatus feedHamiltonianDominationOnlyAfterFiniteTheorem =
  downstreamTheoremStillOpen
ymKillingBoundaryRouteStatus keepOSContinuumAndClaySeparate =
  promotionHeldFalse

data YMKillingBoundarySelfAdjointnessCompositeBlocker : Set where
  missingHamiltonianDominationComposite :
    YMKillingBoundarySelfAdjointnessCompositeBlocker

  missingOSTransferComposite :
    YMKillingBoundarySelfAdjointnessCompositeBlocker

  missingYMClayAuthorityTokenComposite :
    YMKillingBoundarySelfAdjointnessCompositeBlocker

canonicalYMKillingBoundarySelfAdjointnessCompositeBlockers :
  List YMKillingBoundarySelfAdjointnessCompositeBlocker
canonicalYMKillingBoundarySelfAdjointnessCompositeBlockers =
  missingHamiltonianDominationComposite
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
  true

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

ym1FiniteSelfAdjointHamiltonianProvedIsTrue :
  ym1FiniteSelfAdjointHamiltonianProved ≡ true
ym1FiniteSelfAdjointHamiltonianProvedIsTrue =
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

    blockerCountIs3 :
      blockerCount ≡ 3

    firstBlocker :
      YMKillingBoundarySelfAdjointnessCompositeBlocker

    firstBlockerIsHamiltonianDomination :
      firstBlocker ≡ missingHamiltonianDominationComposite

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

    theoremLocalFinitePayloadProved :
      Theorem.localFinitePayloadProved (theoremBoundary support) ≡ true

    orientationLocalFiniteFluxPayloadProved :
      Orientation.localFiniteFluxCancellationPayloadProvedField
        (orientationCancellationBoundary support)
      ≡
      true

    ym1FiniteSelfAdjointHamiltonianProvedField :
      Bool

    ym1FiniteSelfAdjointHamiltonianProvedFieldIsTrue :
      ym1FiniteSelfAdjointHamiltonianProvedField ≡ true

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
        ym1KillingBoundaryCompositeFiniteSelfAdjointnessProved
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
    ; blockerCountIs3 =
        refl
    ; firstBlocker =
        missingHamiltonianDominationComposite
    ; firstBlockerIsHamiltonianDomination =
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
    ; theoremLocalFinitePayloadProved =
        Theorem.localFiniteYMSelfAdjointnessPayloadProvedIsTrue
    ; orientationLocalFiniteFluxPayloadProved =
        Orientation.localFiniteKillingFluxCancellationPayloadProvedIsTrue
    ; ym1FiniteSelfAdjointHamiltonianProvedField =
        ym1FiniteSelfAdjointHamiltonianProved
    ; ym1FiniteSelfAdjointHamiltonianProvedFieldIsTrue =
        ym1FiniteSelfAdjointHamiltonianProvedIsTrue
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
        ∷ "The theorem boundary contributes a local finite symmetric-matrix/Haar/Wilson payload, and the orientation boundary contributes a local two-face flux-cancellation payload."
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

canonicalCompositeBlockerCountIs3 :
  blockerCount canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary
  ≡
  3
canonicalCompositeBlockerCountIs3 =
  refl

canonicalCompositeFirstBlocker :
  firstBlocker canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary
  ≡
  missingHamiltonianDominationComposite
canonicalCompositeFirstBlocker =
  refl

canonicalCompositeTheoremLocalFinitePayloadTrue :
  Theorem.localFinitePayloadProved
    (theoremBoundary
      (support canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary))
  ≡
  true
canonicalCompositeTheoremLocalFinitePayloadTrue =
  refl

canonicalCompositeOrientationLocalFluxPayloadTrue :
  Orientation.localFiniteFluxCancellationPayloadProvedField
    (orientationCancellationBoundary
      (support canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary))
  ≡
  true
canonicalCompositeOrientationLocalFluxPayloadTrue =
  refl

canonicalCompositeYM1FiniteSelfAdjointHamiltonianTrue :
  ym1FiniteSelfAdjointHamiltonianProvedField
    canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary
  ≡
  true
canonicalCompositeYM1FiniteSelfAdjointHamiltonianTrue =
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
  "O YM-1 Killing-boundary finite self-adjointness composite; R assemble finite gauge-quotient Hamiltonian self-adjointness through opposite-face, weight, orientation, flux, gauge-domain, and domain-contract surfaces; C imports six child boundaries plus diagnostic harness and theorem payload; S YM-1 finite self-adjointness is true while Hamiltonian domination, OS transfer, YM Clay, and terminal promotion remain false; L finite quotient self-adjointness now sits before downstream domination consumers; P use this finite theorem only as an input to later domination work; G no domination/OS/Clay promotion token is introduced; F remaining gap is Hamiltonian domination and later continuum transfer."

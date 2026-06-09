module DASHI.Physics.Closure.YMFiniteGaugeQuotientCarrierConstructionBoundary where

-- Finite gauge quotient carrier construction boundary.
--
-- This receipt sits between the finite gauge quotient / Hamiltonian
-- precondition ledger and the finite self-adjoint Hamiltonian composite.  It
-- records the concrete carrier-construction obligations needed before a
-- Hamiltonian can descend to a finite gauge quotient:
--
--   finite gauge action and orbit relation,
--   invariant finite measure / positive quotient pairing,
--   null-gauge directions separated from physical quotient classes,
--   Killing-boundary domain stability under gauge representatives,
--   Hamiltonian gauge-equivariance and quotient descent,
--   finite carrier handoff to the self-adjoint Hamiltonian composite.
--
-- It deliberately does not construct the quotient carrier, does not prove
-- Hamiltonian descent, does not prove self-adjointness, does not prove
-- Hamiltonian domination, does not prove OS/continuum transfer, and does not
-- promote Yang-Mills Clay or terminal claims.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMFiniteGaugeQuotientHamiltonianPreconditionBoundary
  as Precondition
import DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessCompositeBoundary
  as Killing
import DASHI.Physics.Closure.YMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary
  as SelfAdjointComposite

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Imported support.

data YMFiniteGaugeQuotientCarrierSupportInput : Set where
  finiteGaugeQuotientHamiltonianPreconditionConsumed :
    YMFiniteGaugeQuotientCarrierSupportInput

  killingBoundarySelfAdjointnessCompositeConsumed :
    YMFiniteGaugeQuotientCarrierSupportInput

  finiteGaugeQuotientSelfAdjointHamiltonianCompositeConsumed :
    YMFiniteGaugeQuotientCarrierSupportInput

canonicalYMFiniteGaugeQuotientCarrierSupportInputs :
  List YMFiniteGaugeQuotientCarrierSupportInput
canonicalYMFiniteGaugeQuotientCarrierSupportInputs =
  finiteGaugeQuotientHamiltonianPreconditionConsumed
  ∷ killingBoundarySelfAdjointnessCompositeConsumed
  ∷ finiteGaugeQuotientSelfAdjointHamiltonianCompositeConsumed
  ∷ []

record YMFiniteGaugeQuotientCarrierConstructionSupport : Setω where
  field
    preconditionBoundary :
      Precondition.YMFiniteGaugeQuotientHamiltonianPreconditionBoundary

    preconditionBoundaryCanonical :
      Bool

    preconditionBoundaryCanonicalIsTrue :
      preconditionBoundaryCanonical ≡ true

    killingBoundarySelfAdjointnessComposite :
      Killing.YMKillingBoundarySelfAdjointnessCompositeBoundary

    killingBoundarySelfAdjointnessCompositeCanonical :
      Bool

    killingBoundarySelfAdjointnessCompositeCanonicalIsTrue :
      killingBoundarySelfAdjointnessCompositeCanonical ≡ true

    finiteGaugeQuotientSelfAdjointHamiltonianComposite :
      SelfAdjointComposite.YMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary

    finiteGaugeQuotientSelfAdjointHamiltonianCompositeCanonical :
      Bool

    finiteGaugeQuotientSelfAdjointHamiltonianCompositeCanonicalIsTrue :
      finiteGaugeQuotientSelfAdjointHamiltonianCompositeCanonical ≡ true

open YMFiniteGaugeQuotientCarrierConstructionSupport public

canonicalYMFiniteGaugeQuotientCarrierConstructionSupport :
  YMFiniteGaugeQuotientCarrierConstructionSupport
canonicalYMFiniteGaugeQuotientCarrierConstructionSupport =
  record
    { preconditionBoundary =
        Precondition.canonicalYMFiniteGaugeQuotientHamiltonianPreconditionBoundary
    ; preconditionBoundaryCanonical =
        true
    ; preconditionBoundaryCanonicalIsTrue =
        refl
    ; killingBoundarySelfAdjointnessComposite =
        Killing.canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary
    ; killingBoundarySelfAdjointnessCompositeCanonical =
        true
    ; killingBoundarySelfAdjointnessCompositeCanonicalIsTrue =
        refl
    ; finiteGaugeQuotientSelfAdjointHamiltonianComposite =
        SelfAdjointComposite.canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary
    ; finiteGaugeQuotientSelfAdjointHamiltonianCompositeCanonical =
        true
    ; finiteGaugeQuotientSelfAdjointHamiltonianCompositeCanonicalIsTrue =
        refl
    }

------------------------------------------------------------------------
-- Carrier construction route.

data YMFiniteGaugeQuotientCarrierConstructionStatus : Set where
  finiteGaugeQuotientCarrierConstructionTargetRecordedProofOpen :
    YMFiniteGaugeQuotientCarrierConstructionStatus

data YMFiniteGaugeQuotientCarrierTheoremTarget : Set where
  finiteGaugeOrbitHilbertCarrierWithHamiltonianDescentTarget :
    YMFiniteGaugeQuotientCarrierTheoremTarget

canonicalYMFiniteGaugeQuotientCarrierTheoremTarget :
  YMFiniteGaugeQuotientCarrierTheoremTarget
canonicalYMFiniteGaugeQuotientCarrierTheoremTarget =
  finiteGaugeOrbitHilbertCarrierWithHamiltonianDescentTarget

data YMFiniteGaugeQuotientCarrierStage : Set where
  consumeHamiltonianPreconditionLedger :
    YMFiniteGaugeQuotientCarrierStage

  consumeKillingBoundarySelfAdjointnessRoute :
    YMFiniteGaugeQuotientCarrierStage

  consumeFiniteSelfAdjointHamiltonianComposite :
    YMFiniteGaugeQuotientCarrierStage

  defineFiniteGaugeActionOnConfigurationCells :
    YMFiniteGaugeQuotientCarrierStage

  proveOrbitRelationIsFiniteEquivalence :
    YMFiniteGaugeQuotientCarrierStage

  constructGaugeInvariantFiniteMeasure :
    YMFiniteGaugeQuotientCarrierStage

  defineGaugeInvariantFunctionSubspace :
    YMFiniteGaugeQuotientCarrierStage

  quotientByNullGaugeDirections :
    YMFiniteGaugeQuotientCarrierStage

  provePositiveDefiniteQuotientInnerProduct :
    YMFiniteGaugeQuotientCarrierStage

  proveKillingBoundaryDomainDescendsToQuotient :
    YMFiniteGaugeQuotientCarrierStage

  proveHamiltonianGaugeEquivariance :
    YMFiniteGaugeQuotientCarrierStage

  proveHamiltonianWellDefinedOnOrbitClasses :
    YMFiniteGaugeQuotientCarrierStage

  proveFiniteCarrierSeparabilityAndCompleteness :
    YMFiniteGaugeQuotientCarrierStage

  handoffCarrierToSelfAdjointHamiltonianComposite :
    YMFiniteGaugeQuotientCarrierStage

  keepHamiltonianDominationAndOSBlocked :
    YMFiniteGaugeQuotientCarrierStage

  keepYMClayAndTerminalPromotionFalse :
    YMFiniteGaugeQuotientCarrierStage

canonicalYMFiniteGaugeQuotientCarrierStages :
  List YMFiniteGaugeQuotientCarrierStage
canonicalYMFiniteGaugeQuotientCarrierStages =
  consumeHamiltonianPreconditionLedger
  ∷ consumeKillingBoundarySelfAdjointnessRoute
  ∷ consumeFiniteSelfAdjointHamiltonianComposite
  ∷ defineFiniteGaugeActionOnConfigurationCells
  ∷ proveOrbitRelationIsFiniteEquivalence
  ∷ constructGaugeInvariantFiniteMeasure
  ∷ defineGaugeInvariantFunctionSubspace
  ∷ quotientByNullGaugeDirections
  ∷ provePositiveDefiniteQuotientInnerProduct
  ∷ proveKillingBoundaryDomainDescendsToQuotient
  ∷ proveHamiltonianGaugeEquivariance
  ∷ proveHamiltonianWellDefinedOnOrbitClasses
  ∷ proveFiniteCarrierSeparabilityAndCompleteness
  ∷ handoffCarrierToSelfAdjointHamiltonianComposite
  ∷ keepHamiltonianDominationAndOSBlocked
  ∷ keepYMClayAndTerminalPromotionFalse
  ∷ []

data YMFiniteGaugeQuotientCarrierStageStatus : Set where
  upstreamBoundaryConsumed :
    YMFiniteGaugeQuotientCarrierStageStatus

  carrierConstructionObligationOpen :
    YMFiniteGaugeQuotientCarrierStageStatus

  descentObligationOpen :
    YMFiniteGaugeQuotientCarrierStageStatus

  downstreamBlocked :
    YMFiniteGaugeQuotientCarrierStageStatus

  promotionHeldFalse :
    YMFiniteGaugeQuotientCarrierStageStatus

ymFiniteGaugeQuotientCarrierStageStatus :
  YMFiniteGaugeQuotientCarrierStage →
  YMFiniteGaugeQuotientCarrierStageStatus
ymFiniteGaugeQuotientCarrierStageStatus
  consumeHamiltonianPreconditionLedger =
  upstreamBoundaryConsumed
ymFiniteGaugeQuotientCarrierStageStatus
  consumeKillingBoundarySelfAdjointnessRoute =
  upstreamBoundaryConsumed
ymFiniteGaugeQuotientCarrierStageStatus
  consumeFiniteSelfAdjointHamiltonianComposite =
  upstreamBoundaryConsumed
ymFiniteGaugeQuotientCarrierStageStatus
  defineFiniteGaugeActionOnConfigurationCells =
  carrierConstructionObligationOpen
ymFiniteGaugeQuotientCarrierStageStatus
  proveOrbitRelationIsFiniteEquivalence =
  carrierConstructionObligationOpen
ymFiniteGaugeQuotientCarrierStageStatus
  constructGaugeInvariantFiniteMeasure =
  carrierConstructionObligationOpen
ymFiniteGaugeQuotientCarrierStageStatus
  defineGaugeInvariantFunctionSubspace =
  carrierConstructionObligationOpen
ymFiniteGaugeQuotientCarrierStageStatus
  quotientByNullGaugeDirections =
  carrierConstructionObligationOpen
ymFiniteGaugeQuotientCarrierStageStatus
  provePositiveDefiniteQuotientInnerProduct =
  carrierConstructionObligationOpen
ymFiniteGaugeQuotientCarrierStageStatus
  proveKillingBoundaryDomainDescendsToQuotient =
  descentObligationOpen
ymFiniteGaugeQuotientCarrierStageStatus
  proveHamiltonianGaugeEquivariance =
  descentObligationOpen
ymFiniteGaugeQuotientCarrierStageStatus
  proveHamiltonianWellDefinedOnOrbitClasses =
  descentObligationOpen
ymFiniteGaugeQuotientCarrierStageStatus
  proveFiniteCarrierSeparabilityAndCompleteness =
  carrierConstructionObligationOpen
ymFiniteGaugeQuotientCarrierStageStatus
  handoffCarrierToSelfAdjointHamiltonianComposite =
  downstreamBlocked
ymFiniteGaugeQuotientCarrierStageStatus
  keepHamiltonianDominationAndOSBlocked =
  downstreamBlocked
ymFiniteGaugeQuotientCarrierStageStatus
  keepYMClayAndTerminalPromotionFalse =
  promotionHeldFalse

record YMFiniteGaugeQuotientCarrierStageRow : Set where
  field
    stage :
      YMFiniteGaugeQuotientCarrierStage

    status :
      YMFiniteGaugeQuotientCarrierStageStatus

    statusIsCanonical :
      status ≡ ymFiniteGaugeQuotientCarrierStageStatus stage

    proofSurface :
      String

    theoremProvedHere :
      Bool

    theoremProvedHereIsFalse :
      theoremProvedHere ≡ false

open YMFiniteGaugeQuotientCarrierStageRow public

mkYMFiniteGaugeQuotientCarrierStageRow :
  YMFiniteGaugeQuotientCarrierStage →
  String →
  YMFiniteGaugeQuotientCarrierStageRow
mkYMFiniteGaugeQuotientCarrierStageRow stage proofSurface =
  record
    { stage =
        stage
    ; status =
        ymFiniteGaugeQuotientCarrierStageStatus stage
    ; statusIsCanonical =
        refl
    ; proofSurface =
        proofSurface
    ; theoremProvedHere =
        false
    ; theoremProvedHereIsFalse =
        refl
    }

canonicalYMFiniteGaugeQuotientCarrierStageRows :
  List YMFiniteGaugeQuotientCarrierStageRow
canonicalYMFiniteGaugeQuotientCarrierStageRows =
  mkYMFiniteGaugeQuotientCarrierStageRow
    consumeHamiltonianPreconditionLedger
    "Consume the finite gauge quotient / Hamiltonian precondition ledger and keep all promotions closed."
  ∷ mkYMFiniteGaugeQuotientCarrierStageRow
    consumeKillingBoundarySelfAdjointnessRoute
    "Consume the Killing/full-degree boundary cancellation and gauge-domain route."
  ∷ mkYMFiniteGaugeQuotientCarrierStageRow
    consumeFiniteSelfAdjointHamiltonianComposite
    "Consume the downstream self-adjoint Hamiltonian composite as the carrier handoff contract."
  ∷ mkYMFiniteGaugeQuotientCarrierStageRow
    defineFiniteGaugeActionOnConfigurationCells
    "Define the finite gauge group action on BT configuration cells and boundary faces."
  ∷ mkYMFiniteGaugeQuotientCarrierStageRow
    proveOrbitRelationIsFiniteEquivalence
    "Prove the orbit relation is reflexive, symmetric, transitive, and finite-depth compatible."
  ∷ mkYMFiniteGaugeQuotientCarrierStageRow
    constructGaugeInvariantFiniteMeasure
    "Construct the invariant counting/Killing-weight measure on finite orbit classes."
  ∷ mkYMFiniteGaugeQuotientCarrierStageRow
    defineGaugeInvariantFunctionSubspace
    "Identify gauge-invariant finite-energy functions before quotienting null directions."
  ∷ mkYMFiniteGaugeQuotientCarrierStageRow
    quotientByNullGaugeDirections
    "Factor pure-gauge null directions without killing nontrivial holonomy sectors."
  ∷ mkYMFiniteGaugeQuotientCarrierStageRow
    provePositiveDefiniteQuotientInnerProduct
    "Prove the quotient pairing is positive definite after the null gauge factor is removed."
  ∷ mkYMFiniteGaugeQuotientCarrierStageRow
    proveKillingBoundaryDomainDescendsToQuotient
    "Show the full-degree Killing boundary domain is invariant under representative changes."
  ∷ mkYMFiniteGaugeQuotientCarrierStageRow
    proveHamiltonianGaugeEquivariance
    "Prove the finite Hamiltonian commutes with the finite gauge action on the domain."
  ∷ mkYMFiniteGaugeQuotientCarrierStageRow
    proveHamiltonianWellDefinedOnOrbitClasses
    "Prove Hamiltonian representatives agree on orbit classes and descend to the carrier."
  ∷ mkYMFiniteGaugeQuotientCarrierStageRow
    proveFiniteCarrierSeparabilityAndCompleteness
    "Record finite-dimensional completeness and separability only after the quotient carrier exists."
  ∷ mkYMFiniteGaugeQuotientCarrierStageRow
    handoffCarrierToSelfAdjointHamiltonianComposite
    "Hand the carrier/descent theorem to the self-adjoint Hamiltonian composite."
  ∷ mkYMFiniteGaugeQuotientCarrierStageRow
    keepHamiltonianDominationAndOSBlocked
    "Keep domination, transfer matrix, OS, and continuum transfer blocked after this finite carrier step."
  ∷ mkYMFiniteGaugeQuotientCarrierStageRow
    keepYMClayAndTerminalPromotionFalse
    "Keep Yang-Mills Clay and terminal promotion false."
  ∷ []

------------------------------------------------------------------------
-- Explicit blockers and descent preconditions.

data YMFiniteGaugeQuotientCarrierBlocker : Set where
  missingFiniteGaugeActionOnBTCells :
    YMFiniteGaugeQuotientCarrierBlocker

  missingOrbitEquivalenceRelation :
    YMFiniteGaugeQuotientCarrierBlocker

  missingInvariantFiniteMeasure :
    YMFiniteGaugeQuotientCarrierBlocker

  missingGaugeInvariantFunctionSubspace :
    YMFiniteGaugeQuotientCarrierBlocker

  missingPureGaugeNullQuotient :
    YMFiniteGaugeQuotientCarrierBlocker

  missingPositiveQuotientPairing :
    YMFiniteGaugeQuotientCarrierBlocker

  missingKillingBoundaryDomainDescent :
    YMFiniteGaugeQuotientCarrierBlocker

  missingHamiltonianGaugeEquivariance :
    YMFiniteGaugeQuotientCarrierBlocker

  missingHamiltonianOrbitClassWellDefinedness :
    YMFiniteGaugeQuotientCarrierBlocker

  missingFiniteCarrierCompleteness :
    YMFiniteGaugeQuotientCarrierBlocker

  missingSelfAdjointHamiltonianHandoff :
    YMFiniteGaugeQuotientCarrierBlocker

  missingHamiltonianDominationAfterCarrier :
    YMFiniteGaugeQuotientCarrierBlocker

  missingOSTransferAfterCarrier :
    YMFiniteGaugeQuotientCarrierBlocker

  missingContinuumNoSpectralPollutionAfterCarrier :
    YMFiniteGaugeQuotientCarrierBlocker

  missingClayYangMillsAuthorityToken :
    YMFiniteGaugeQuotientCarrierBlocker

canonicalYMFiniteGaugeQuotientCarrierBlockers :
  List YMFiniteGaugeQuotientCarrierBlocker
canonicalYMFiniteGaugeQuotientCarrierBlockers =
  missingFiniteGaugeActionOnBTCells
  ∷ missingOrbitEquivalenceRelation
  ∷ missingInvariantFiniteMeasure
  ∷ missingGaugeInvariantFunctionSubspace
  ∷ missingPureGaugeNullQuotient
  ∷ missingPositiveQuotientPairing
  ∷ missingKillingBoundaryDomainDescent
  ∷ missingHamiltonianGaugeEquivariance
  ∷ missingHamiltonianOrbitClassWellDefinedness
  ∷ missingFiniteCarrierCompleteness
  ∷ missingSelfAdjointHamiltonianHandoff
  ∷ missingHamiltonianDominationAfterCarrier
  ∷ missingOSTransferAfterCarrier
  ∷ missingContinuumNoSpectralPollutionAfterCarrier
  ∷ missingClayYangMillsAuthorityToken
  ∷ []

data YMFiniteGaugeQuotientCarrierDescentPrecondition : Set where
  finiteGaugeGroupActionDefined :
    YMFiniteGaugeQuotientCarrierDescentPrecondition

  orbitRelationFiniteDepthCompatible :
    YMFiniteGaugeQuotientCarrierDescentPrecondition

  invariantMeasureRespectsKillingWeights :
    YMFiniteGaugeQuotientCarrierDescentPrecondition

  nullGaugeDirectionsFactored :
    YMFiniteGaugeQuotientCarrierDescentPrecondition

  quotientPairingPositive :
    YMFiniteGaugeQuotientCarrierDescentPrecondition

  killingDomainRepresentativeInvariant :
    YMFiniteGaugeQuotientCarrierDescentPrecondition

  hamiltonianGaugeEquivariant :
    YMFiniteGaugeQuotientCarrierDescentPrecondition

  hamiltonianOrbitClassWellDefined :
    YMFiniteGaugeQuotientCarrierDescentPrecondition

canonicalYMFiniteGaugeQuotientCarrierDescentPreconditions :
  List YMFiniteGaugeQuotientCarrierDescentPrecondition
canonicalYMFiniteGaugeQuotientCarrierDescentPreconditions =
  finiteGaugeGroupActionDefined
  ∷ orbitRelationFiniteDepthCompatible
  ∷ invariantMeasureRespectsKillingWeights
  ∷ nullGaugeDirectionsFactored
  ∷ quotientPairingPositive
  ∷ killingDomainRepresentativeInvariant
  ∷ hamiltonianGaugeEquivariant
  ∷ hamiltonianOrbitClassWellDefined
  ∷ []

finiteGaugeQuotientCarrierFormula : String
finiteGaugeQuotientCarrierFormula =
  "finite gauge action + invariant Killing measure + null-gauge quotient + positive pairing + domain/gauge equivariance => Hamiltonian descends to finite gauge quotient carrier"

------------------------------------------------------------------------
-- Fail-closed flags.

boundaryRecorded : Bool
boundaryRecorded =
  true

supportComposed : Bool
supportComposed =
  true

carrierConstructionTargetRecorded : Bool
carrierConstructionTargetRecorded =
  true

finiteGaugeActionConstructed : Bool
finiteGaugeActionConstructed =
  false

orbitEquivalenceProved : Bool
orbitEquivalenceProved =
  false

invariantMeasureConstructed : Bool
invariantMeasureConstructed =
  false

positiveQuotientPairingProved : Bool
positiveQuotientPairingProved =
  false

killingBoundaryDomainDescentProved : Bool
killingBoundaryDomainDescentProved =
  false

hamiltonianGaugeEquivarianceProved : Bool
hamiltonianGaugeEquivarianceProved =
  false

hamiltonianOrbitClassDescentProved : Bool
hamiltonianOrbitClassDescentProved =
  false

carrierHandoffToSelfAdjointHamiltonianProved : Bool
carrierHandoffToSelfAdjointHamiltonianProved =
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

supportComposedIsTrue :
  supportComposed ≡ true
supportComposedIsTrue =
  refl

carrierConstructionTargetRecordedIsTrue :
  carrierConstructionTargetRecorded ≡ true
carrierConstructionTargetRecordedIsTrue =
  refl

finiteGaugeActionConstructedIsFalse :
  finiteGaugeActionConstructed ≡ false
finiteGaugeActionConstructedIsFalse =
  refl

orbitEquivalenceProvedIsFalse :
  orbitEquivalenceProved ≡ false
orbitEquivalenceProvedIsFalse =
  refl

invariantMeasureConstructedIsFalse :
  invariantMeasureConstructed ≡ false
invariantMeasureConstructedIsFalse =
  refl

positiveQuotientPairingProvedIsFalse :
  positiveQuotientPairingProved ≡ false
positiveQuotientPairingProvedIsFalse =
  refl

killingBoundaryDomainDescentProvedIsFalse :
  killingBoundaryDomainDescentProved ≡ false
killingBoundaryDomainDescentProvedIsFalse =
  refl

hamiltonianGaugeEquivarianceProvedIsFalse :
  hamiltonianGaugeEquivarianceProved ≡ false
hamiltonianGaugeEquivarianceProvedIsFalse =
  refl

hamiltonianOrbitClassDescentProvedIsFalse :
  hamiltonianOrbitClassDescentProved ≡ false
hamiltonianOrbitClassDescentProvedIsFalse =
  refl

carrierHandoffToSelfAdjointHamiltonianProvedIsFalse :
  carrierHandoffToSelfAdjointHamiltonianProved ≡ false
carrierHandoffToSelfAdjointHamiltonianProvedIsFalse =
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

------------------------------------------------------------------------
-- Canonical boundary.

record YMFiniteGaugeQuotientCarrierConstructionBoundary : Setω where
  field
    status :
      YMFiniteGaugeQuotientCarrierConstructionStatus

    support :
      YMFiniteGaugeQuotientCarrierConstructionSupport

    supportCanonical :
      Bool

    supportCanonicalIsTrue :
      supportCanonical ≡ true

    supportInputs :
      List YMFiniteGaugeQuotientCarrierSupportInput

    supportInputsAreCanonical :
      supportInputs ≡ canonicalYMFiniteGaugeQuotientCarrierSupportInputs

    supportInputCount :
      Nat

    supportInputCountIs3 :
      supportInputCount ≡ 3

    theoremTarget :
      YMFiniteGaugeQuotientCarrierTheoremTarget

    theoremTargetIsCanonical :
      theoremTarget ≡ canonicalYMFiniteGaugeQuotientCarrierTheoremTarget

    stages :
      List YMFiniteGaugeQuotientCarrierStage

    stagesAreCanonical :
      stages ≡ canonicalYMFiniteGaugeQuotientCarrierStages

    stageCount :
      Nat

    stageCountIs16 :
      stageCount ≡ 16

    rows :
      List YMFiniteGaugeQuotientCarrierStageRow

    rowsAreCanonical :
      rows ≡ canonicalYMFiniteGaugeQuotientCarrierStageRows

    rowCount :
      Nat

    rowCountIs16 :
      rowCount ≡ 16

    descentPreconditions :
      List YMFiniteGaugeQuotientCarrierDescentPrecondition

    descentPreconditionsAreCanonical :
      descentPreconditions
      ≡
      canonicalYMFiniteGaugeQuotientCarrierDescentPreconditions

    descentPreconditionCount :
      Nat

    descentPreconditionCountIs8 :
      descentPreconditionCount ≡ 8

    blockers :
      List YMFiniteGaugeQuotientCarrierBlocker

    blockersAreCanonical :
      blockers ≡ canonicalYMFiniteGaugeQuotientCarrierBlockers

    blockerCount :
      Nat

    blockerCountIs15 :
      blockerCount ≡ 15

    firstBlocker :
      YMFiniteGaugeQuotientCarrierBlocker

    firstBlockerIsFiniteGaugeAction :
      firstBlocker ≡ missingFiniteGaugeActionOnBTCells

    formula :
      String

    formulaIsCanonical :
      formula ≡ finiteGaugeQuotientCarrierFormula

    boundaryRecordedField :
      Bool

    boundaryRecordedFieldIsTrue :
      boundaryRecordedField ≡ true

    supportComposedField :
      Bool

    supportComposedFieldIsTrue :
      supportComposedField ≡ true

    carrierConstructionTargetRecordedField :
      Bool

    carrierConstructionTargetRecordedFieldIsTrue :
      carrierConstructionTargetRecordedField ≡ true

    finiteGaugeActionConstructedField :
      Bool

    finiteGaugeActionConstructedFieldIsFalse :
      finiteGaugeActionConstructedField ≡ false

    orbitEquivalenceProvedField :
      Bool

    orbitEquivalenceProvedFieldIsFalse :
      orbitEquivalenceProvedField ≡ false

    invariantMeasureConstructedField :
      Bool

    invariantMeasureConstructedFieldIsFalse :
      invariantMeasureConstructedField ≡ false

    positiveQuotientPairingProvedField :
      Bool

    positiveQuotientPairingProvedFieldIsFalse :
      positiveQuotientPairingProvedField ≡ false

    killingBoundaryDomainDescentProvedField :
      Bool

    killingBoundaryDomainDescentProvedFieldIsFalse :
      killingBoundaryDomainDescentProvedField ≡ false

    hamiltonianGaugeEquivarianceProvedField :
      Bool

    hamiltonianGaugeEquivarianceProvedFieldIsFalse :
      hamiltonianGaugeEquivarianceProvedField ≡ false

    hamiltonianOrbitClassDescentProvedField :
      Bool

    hamiltonianOrbitClassDescentProvedFieldIsFalse :
      hamiltonianOrbitClassDescentProvedField ≡ false

    carrierHandoffToSelfAdjointHamiltonianProvedField :
      Bool

    carrierHandoffToSelfAdjointHamiltonianProvedFieldIsFalse :
      carrierHandoffToSelfAdjointHamiltonianProvedField ≡ false

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

    noClayFromCarrierConstruction :
      ymClayPromotedField ≡ true → ⊥

    noTerminalPromotionFromCarrierConstruction :
      terminalPromotionField ≡ true → ⊥

open YMFiniteGaugeQuotientCarrierConstructionBoundary public

canonicalYMFiniteGaugeQuotientCarrierConstructionBoundary :
  YMFiniteGaugeQuotientCarrierConstructionBoundary
canonicalYMFiniteGaugeQuotientCarrierConstructionBoundary =
  record
    { status =
        finiteGaugeQuotientCarrierConstructionTargetRecordedProofOpen
    ; support =
        canonicalYMFiniteGaugeQuotientCarrierConstructionSupport
    ; supportCanonical =
        true
    ; supportCanonicalIsTrue =
        refl
    ; supportInputs =
        canonicalYMFiniteGaugeQuotientCarrierSupportInputs
    ; supportInputsAreCanonical =
        refl
    ; supportInputCount =
        listCount canonicalYMFiniteGaugeQuotientCarrierSupportInputs
    ; supportInputCountIs3 =
        refl
    ; theoremTarget =
        canonicalYMFiniteGaugeQuotientCarrierTheoremTarget
    ; theoremTargetIsCanonical =
        refl
    ; stages =
        canonicalYMFiniteGaugeQuotientCarrierStages
    ; stagesAreCanonical =
        refl
    ; stageCount =
        listCount canonicalYMFiniteGaugeQuotientCarrierStages
    ; stageCountIs16 =
        refl
    ; rows =
        canonicalYMFiniteGaugeQuotientCarrierStageRows
    ; rowsAreCanonical =
        refl
    ; rowCount =
        listCount canonicalYMFiniteGaugeQuotientCarrierStageRows
    ; rowCountIs16 =
        refl
    ; descentPreconditions =
        canonicalYMFiniteGaugeQuotientCarrierDescentPreconditions
    ; descentPreconditionsAreCanonical =
        refl
    ; descentPreconditionCount =
        listCount canonicalYMFiniteGaugeQuotientCarrierDescentPreconditions
    ; descentPreconditionCountIs8 =
        refl
    ; blockers =
        canonicalYMFiniteGaugeQuotientCarrierBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCount =
        listCount canonicalYMFiniteGaugeQuotientCarrierBlockers
    ; blockerCountIs15 =
        refl
    ; firstBlocker =
        missingFiniteGaugeActionOnBTCells
    ; firstBlockerIsFiniteGaugeAction =
        refl
    ; formula =
        finiteGaugeQuotientCarrierFormula
    ; formulaIsCanonical =
        refl
    ; boundaryRecordedField =
        boundaryRecorded
    ; boundaryRecordedFieldIsTrue =
        boundaryRecordedIsTrue
    ; supportComposedField =
        supportComposed
    ; supportComposedFieldIsTrue =
        supportComposedIsTrue
    ; carrierConstructionTargetRecordedField =
        carrierConstructionTargetRecorded
    ; carrierConstructionTargetRecordedFieldIsTrue =
        carrierConstructionTargetRecordedIsTrue
    ; finiteGaugeActionConstructedField =
        finiteGaugeActionConstructed
    ; finiteGaugeActionConstructedFieldIsFalse =
        finiteGaugeActionConstructedIsFalse
    ; orbitEquivalenceProvedField =
        orbitEquivalenceProved
    ; orbitEquivalenceProvedFieldIsFalse =
        orbitEquivalenceProvedIsFalse
    ; invariantMeasureConstructedField =
        invariantMeasureConstructed
    ; invariantMeasureConstructedFieldIsFalse =
        invariantMeasureConstructedIsFalse
    ; positiveQuotientPairingProvedField =
        positiveQuotientPairingProved
    ; positiveQuotientPairingProvedFieldIsFalse =
        positiveQuotientPairingProvedIsFalse
    ; killingBoundaryDomainDescentProvedField =
        killingBoundaryDomainDescentProved
    ; killingBoundaryDomainDescentProvedFieldIsFalse =
        killingBoundaryDomainDescentProvedIsFalse
    ; hamiltonianGaugeEquivarianceProvedField =
        hamiltonianGaugeEquivarianceProved
    ; hamiltonianGaugeEquivarianceProvedFieldIsFalse =
        hamiltonianGaugeEquivarianceProvedIsFalse
    ; hamiltonianOrbitClassDescentProvedField =
        hamiltonianOrbitClassDescentProved
    ; hamiltonianOrbitClassDescentProvedFieldIsFalse =
        hamiltonianOrbitClassDescentProvedIsFalse
    ; carrierHandoffToSelfAdjointHamiltonianProvedField =
        carrierHandoffToSelfAdjointHamiltonianProved
    ; carrierHandoffToSelfAdjointHamiltonianProvedFieldIsFalse =
        carrierHandoffToSelfAdjointHamiltonianProvedIsFalse
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
    ; noClayFromCarrierConstruction =
        λ ()
    ; noTerminalPromotionFromCarrierConstruction =
        λ ()
    }

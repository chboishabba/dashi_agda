module DASHI.Physics.Closure.YMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary where

-- Composite boundary for the finite gauge-quotient self-adjoint
-- Hamiltonian target.
--
-- This module composes four existing boundary surfaces:
--
--   finite gauge quotient / Hamiltonian preconditions,
--   Killing-boundary self-adjointness composite,
--   finite self-adjoint Hamiltonian boundary,
--   self-adjoint Hamiltonian quotient gap boundary.
--
-- It records the finite gauge-quotient self-adjoint Hamiltonian theorem
-- target and the exact downstream blockers.  It does not construct the
-- quotient carrier, does not prove finite self-adjointness, does not unlock
-- Hamiltonian domination, does not prove OS transfer, and does not promote
-- Yang-Mills Clay or terminal claims.

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
import DASHI.Physics.Closure.YMSelfAdjointFiniteHamiltonianBoundary
  as Finite
import DASHI.Physics.Closure.YMSelfAdjointHamiltonianQuotientGapBoundary
  as QuotientGap

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Imported support.

data YMFiniteGaugeQuotientSelfAdjointHamiltonianSupportInput : Set where
  finiteGaugeQuotientHamiltonianPreconditionConsumed :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianSupportInput

  killingBoundarySelfAdjointnessCompositeConsumed :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianSupportInput

  selfAdjointFiniteHamiltonianBoundaryConsumed :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianSupportInput

  selfAdjointHamiltonianQuotientGapBoundaryConsumed :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianSupportInput

canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianSupportInputs :
  List YMFiniteGaugeQuotientSelfAdjointHamiltonianSupportInput
canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianSupportInputs =
  finiteGaugeQuotientHamiltonianPreconditionConsumed
  ∷ killingBoundarySelfAdjointnessCompositeConsumed
  ∷ selfAdjointFiniteHamiltonianBoundaryConsumed
  ∷ selfAdjointHamiltonianQuotientGapBoundaryConsumed
  ∷ []

record YMFiniteGaugeQuotientSelfAdjointHamiltonianSupport : Setω where
  field
    preconditionBoundary :
      Precondition.YMFiniteGaugeQuotientHamiltonianPreconditionBoundary

    preconditionBoundaryCanonical :
      Bool

    preconditionBoundaryCanonicalIsTrue :
      preconditionBoundaryCanonical ≡ true

    killingSelfAdjointnessComposite :
      Killing.YMKillingBoundarySelfAdjointnessCompositeBoundary

    killingSelfAdjointnessCompositeCanonical :
      Bool

    killingSelfAdjointnessCompositeCanonicalIsTrue :
      killingSelfAdjointnessCompositeCanonical ≡ true

    finiteSelfAdjointHamiltonianBoundary :
      Finite.YMSelfAdjointFiniteHamiltonianBoundary

    finiteSelfAdjointHamiltonianBoundaryCanonical :
      Bool

    finiteSelfAdjointHamiltonianBoundaryCanonicalIsTrue :
      finiteSelfAdjointHamiltonianBoundaryCanonical ≡ true

    quotientGapBoundary :
      QuotientGap.YMSelfAdjointHamiltonianQuotientGapBoundary

    quotientGapBoundaryCanonical :
      Bool

    quotientGapBoundaryCanonicalIsTrue :
      quotientGapBoundaryCanonical ≡ true

open YMFiniteGaugeQuotientSelfAdjointHamiltonianSupport public

canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianSupport :
  YMFiniteGaugeQuotientSelfAdjointHamiltonianSupport
canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianSupport =
  record
    { preconditionBoundary =
        Precondition.canonicalYMFiniteGaugeQuotientHamiltonianPreconditionBoundary
    ; preconditionBoundaryCanonical =
        true
    ; preconditionBoundaryCanonicalIsTrue =
        refl
    ; killingSelfAdjointnessComposite =
        Killing.canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary
    ; killingSelfAdjointnessCompositeCanonical =
        true
    ; killingSelfAdjointnessCompositeCanonicalIsTrue =
        refl
    ; finiteSelfAdjointHamiltonianBoundary =
        Finite.canonicalYMSelfAdjointFiniteHamiltonianBoundary
    ; finiteSelfAdjointHamiltonianBoundaryCanonical =
        true
    ; finiteSelfAdjointHamiltonianBoundaryCanonicalIsTrue =
        refl
    ; quotientGapBoundary =
        QuotientGap.canonicalYMSelfAdjointHamiltonianQuotientGapBoundary
    ; quotientGapBoundaryCanonical =
        true
    ; quotientGapBoundaryCanonicalIsTrue =
        refl
    }

------------------------------------------------------------------------
-- Composite theorem target and route ledger.

data YMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeStatus : Set where
  finiteGaugeQuotientSelfAdjointHamiltonianTargetRecordedProofOpen :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeStatus

data YMFiniteGaugeQuotientSelfAdjointHamiltonianTheoremTarget : Set where
  finiteGaugeQuotientCarrierWithSelfAdjointHamiltonianTarget :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianTheoremTarget

canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianTheoremTarget :
  YMFiniteGaugeQuotientSelfAdjointHamiltonianTheoremTarget
canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianTheoremTarget =
  finiteGaugeQuotientCarrierWithSelfAdjointHamiltonianTarget

data YMFiniteGaugeQuotientSelfAdjointHamiltonianStage : Set where
  consumeFiniteGaugeQuotientPreconditions :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianStage

  alignFullDegreeKillingBoundaryDomain :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianStage

  routeBoundaryCancellationAndGaugeDomain :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianStage

  constructFiniteGaugeQuotientCarrier :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianStage

  descendHamiltonianToGaugeQuotient :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianStage

  proveFiniteSymmetricHamiltonianByIBP :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianStage

  proveSelfAdjointFiniteHamiltonianOnQuotient :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianStage

  recordDiscreteFiniteSpectrumTarget :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianStage

  handoffToHamiltonianDomination :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianStage

  handoffToQuotientGapAndOS :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianStage

  keepClayAndTerminalPromotionClosed :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianStage

canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianStages :
  List YMFiniteGaugeQuotientSelfAdjointHamiltonianStage
canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianStages =
  consumeFiniteGaugeQuotientPreconditions
  ∷ alignFullDegreeKillingBoundaryDomain
  ∷ routeBoundaryCancellationAndGaugeDomain
  ∷ constructFiniteGaugeQuotientCarrier
  ∷ descendHamiltonianToGaugeQuotient
  ∷ proveFiniteSymmetricHamiltonianByIBP
  ∷ proveSelfAdjointFiniteHamiltonianOnQuotient
  ∷ recordDiscreteFiniteSpectrumTarget
  ∷ handoffToHamiltonianDomination
  ∷ handoffToQuotientGapAndOS
  ∷ keepClayAndTerminalPromotionClosed
  ∷ []

data YMFiniteGaugeQuotientSelfAdjointHamiltonianStageStatus : Set where
  upstreamBoundaryConsumed :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianStageStatus

  boundaryCancellationRouteRecorded :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianStageStatus

  theoremObligationOpen :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianStageStatus

  downstreamBlocked :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianStageStatus

  promotionHeldFalse :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianStageStatus

ymFiniteGaugeQuotientSelfAdjointHamiltonianStageStatus :
  YMFiniteGaugeQuotientSelfAdjointHamiltonianStage →
  YMFiniteGaugeQuotientSelfAdjointHamiltonianStageStatus
ymFiniteGaugeQuotientSelfAdjointHamiltonianStageStatus
  consumeFiniteGaugeQuotientPreconditions =
  upstreamBoundaryConsumed
ymFiniteGaugeQuotientSelfAdjointHamiltonianStageStatus
  alignFullDegreeKillingBoundaryDomain =
  upstreamBoundaryConsumed
ymFiniteGaugeQuotientSelfAdjointHamiltonianStageStatus
  routeBoundaryCancellationAndGaugeDomain =
  boundaryCancellationRouteRecorded
ymFiniteGaugeQuotientSelfAdjointHamiltonianStageStatus
  constructFiniteGaugeQuotientCarrier =
  theoremObligationOpen
ymFiniteGaugeQuotientSelfAdjointHamiltonianStageStatus
  descendHamiltonianToGaugeQuotient =
  theoremObligationOpen
ymFiniteGaugeQuotientSelfAdjointHamiltonianStageStatus
  proveFiniteSymmetricHamiltonianByIBP =
  theoremObligationOpen
ymFiniteGaugeQuotientSelfAdjointHamiltonianStageStatus
  proveSelfAdjointFiniteHamiltonianOnQuotient =
  theoremObligationOpen
ymFiniteGaugeQuotientSelfAdjointHamiltonianStageStatus
  recordDiscreteFiniteSpectrumTarget =
  downstreamBlocked
ymFiniteGaugeQuotientSelfAdjointHamiltonianStageStatus
  handoffToHamiltonianDomination =
  downstreamBlocked
ymFiniteGaugeQuotientSelfAdjointHamiltonianStageStatus
  handoffToQuotientGapAndOS =
  downstreamBlocked
ymFiniteGaugeQuotientSelfAdjointHamiltonianStageStatus
  keepClayAndTerminalPromotionClosed =
  promotionHeldFalse

data YMFiniteGaugeQuotientSelfAdjointHamiltonianBlocker : Set where
  missingFiniteGaugeQuotientCarrierComposite :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianBlocker

  missingKillingBoundaryDomainClosureComposite :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianBlocker

  missingGaugeDomainPreservationComposite :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianBlocker

  missingGaugeQuotientDescentComposite :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianBlocker

  missingSymmetricFiniteHamiltonianIBPComposite :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianBlocker

  missingSelfAdjointFiniteHamiltonianOnQuotientComposite :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianBlocker

  missingDiscreteSpectrumExtractionComposite :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianBlocker

  missingHamiltonianDominationComposite :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianBlocker

  missingOSQuotientCompatibilityComposite :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianBlocker

  missingSpectralGapLiftThroughQuotientComposite :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianBlocker

  missingContinuumTransferComposite :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianBlocker

  missingClayYangMillsAuthorityTokenComposite :
    YMFiniteGaugeQuotientSelfAdjointHamiltonianBlocker

canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianBlockers :
  List YMFiniteGaugeQuotientSelfAdjointHamiltonianBlocker
canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianBlockers =
  missingFiniteGaugeQuotientCarrierComposite
  ∷ missingKillingBoundaryDomainClosureComposite
  ∷ missingGaugeDomainPreservationComposite
  ∷ missingGaugeQuotientDescentComposite
  ∷ missingSymmetricFiniteHamiltonianIBPComposite
  ∷ missingSelfAdjointFiniteHamiltonianOnQuotientComposite
  ∷ missingDiscreteSpectrumExtractionComposite
  ∷ missingHamiltonianDominationComposite
  ∷ missingOSQuotientCompatibilityComposite
  ∷ missingSpectralGapLiftThroughQuotientComposite
  ∷ missingContinuumTransferComposite
  ∷ missingClayYangMillsAuthorityTokenComposite
  ∷ []

record YMFiniteGaugeQuotientSelfAdjointHamiltonianStageRow : Set where
  field
    stage :
      YMFiniteGaugeQuotientSelfAdjointHamiltonianStage

    status :
      YMFiniteGaugeQuotientSelfAdjointHamiltonianStageStatus

    statusIsCanonical :
      status
      ≡
      ymFiniteGaugeQuotientSelfAdjointHamiltonianStageStatus stage

    proofSurface :
      String

    theoremProvedHere :
      Bool

    theoremProvedHereIsFalse :
      theoremProvedHere ≡ false

open YMFiniteGaugeQuotientSelfAdjointHamiltonianStageRow public

mkYMFiniteGaugeQuotientSelfAdjointHamiltonianStageRow :
  YMFiniteGaugeQuotientSelfAdjointHamiltonianStage →
  String →
  YMFiniteGaugeQuotientSelfAdjointHamiltonianStageRow
mkYMFiniteGaugeQuotientSelfAdjointHamiltonianStageRow stage proofSurface =
  record
    { stage =
        stage
    ; status =
        ymFiniteGaugeQuotientSelfAdjointHamiltonianStageStatus stage
    ; statusIsCanonical =
        refl
    ; proofSurface =
        proofSurface
    ; theoremProvedHere =
        false
    ; theoremProvedHereIsFalse =
        refl
    }

canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianRows :
  List YMFiniteGaugeQuotientSelfAdjointHamiltonianStageRow
canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianRows =
  mkYMFiniteGaugeQuotientSelfAdjointHamiltonianStageRow
    consumeFiniteGaugeQuotientPreconditions
    "Consume finite gauge quotient carrier, finite Hamiltonian, and domination-precondition targets."
  ∷ mkYMFiniteGaugeQuotientSelfAdjointHamiltonianStageRow
    alignFullDegreeKillingBoundaryDomain
    "Align the full-degree Killing boundary convention with the finite operator domain."
  ∷ mkYMFiniteGaugeQuotientSelfAdjointHamiltonianStageRow
    routeBoundaryCancellationAndGaugeDomain
    "Route opposite-face, weight, orientation, flux, and gauge-domain surfaces into quotient self-adjointness."
  ∷ mkYMFiniteGaugeQuotientSelfAdjointHamiltonianStageRow
    constructFiniteGaugeQuotientCarrier
    "Construct the finite gauge orbit quotient carrier with a positive quotient inner product."
  ∷ mkYMFiniteGaugeQuotientSelfAdjointHamiltonianStageRow
    descendHamiltonianToGaugeQuotient
    "Prove the finite Hamiltonian is gauge-invariant and well-defined on quotient classes."
  ∷ mkYMFiniteGaugeQuotientSelfAdjointHamiltonianStageRow
    proveFiniteSymmetricHamiltonianByIBP
    "Prove finite IBP symmetry after boundary cancellation and quotient descent."
  ∷ mkYMFiniteGaugeQuotientSelfAdjointHamiltonianStageRow
    proveSelfAdjointFiniteHamiltonianOnQuotient
    "Use the finite symmetric quotient representative to obtain self-adjointness."
  ∷ mkYMFiniteGaugeQuotientSelfAdjointHamiltonianStageRow
    recordDiscreteFiniteSpectrumTarget
    "Extract the finite real discrete spectrum only after self-adjointness is proved."
  ∷ mkYMFiniteGaugeQuotientSelfAdjointHamiltonianStageRow
    handoffToHamiltonianDomination
    "Feed the theorem into the H_d domination inequality only after the finite theorem is closed."
  ∷ mkYMFiniteGaugeQuotientSelfAdjointHamiltonianStageRow
    handoffToQuotientGapAndOS
    "Hand off to quotient OS compatibility, spectral gap lift, and continuum transfer as separate obligations."
  ∷ mkYMFiniteGaugeQuotientSelfAdjointHamiltonianStageRow
    keepClayAndTerminalPromotionClosed
    "Keep Yang-Mills Clay and terminal promotion false without domination, OS, and continuum transfer."
  ∷ []

------------------------------------------------------------------------
-- Composite flags.

compositeBoundaryRecorded : Bool
compositeBoundaryRecorded =
  true

finiteGaugeQuotientSelfAdjointHamiltonianTargetRecorded : Bool
finiteGaugeQuotientSelfAdjointHamiltonianTargetRecorded =
  true

finiteGaugeQuotientCarrierConstructed : Bool
finiteGaugeQuotientCarrierConstructed =
  false

quotientHamiltonianDescentProved : Bool
quotientHamiltonianDescentProved =
  false

finiteSymmetricHamiltonianProved : Bool
finiteSymmetricHamiltonianProved =
  false

selfAdjointFiniteHamiltonianOnQuotientProved : Bool
selfAdjointFiniteHamiltonianOnQuotientProved =
  false

finiteDiscreteSpectrumExtracted : Bool
finiteDiscreteSpectrumExtracted =
  false

hamiltonianDominationProved : Bool
hamiltonianDominationProved =
  false

osTransferProved : Bool
osTransferProved =
  false

spectralGapLiftThroughQuotientProved : Bool
spectralGapLiftThroughQuotientProved =
  false

continuumTransferProved : Bool
continuumTransferProved =
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

finiteGaugeQuotientSelfAdjointHamiltonianTargetRecordedIsTrue :
  finiteGaugeQuotientSelfAdjointHamiltonianTargetRecorded ≡ true
finiteGaugeQuotientSelfAdjointHamiltonianTargetRecordedIsTrue =
  refl

finiteGaugeQuotientCarrierConstructedIsFalse :
  finiteGaugeQuotientCarrierConstructed ≡ false
finiteGaugeQuotientCarrierConstructedIsFalse =
  refl

quotientHamiltonianDescentProvedIsFalse :
  quotientHamiltonianDescentProved ≡ false
quotientHamiltonianDescentProvedIsFalse =
  refl

finiteSymmetricHamiltonianProvedIsFalse :
  finiteSymmetricHamiltonianProved ≡ false
finiteSymmetricHamiltonianProvedIsFalse =
  refl

selfAdjointFiniteHamiltonianOnQuotientProvedIsFalse :
  selfAdjointFiniteHamiltonianOnQuotientProved ≡ false
selfAdjointFiniteHamiltonianOnQuotientProvedIsFalse =
  refl

finiteDiscreteSpectrumExtractedIsFalse :
  finiteDiscreteSpectrumExtracted ≡ false
finiteDiscreteSpectrumExtractedIsFalse =
  refl

hamiltonianDominationProvedIsFalse :
  hamiltonianDominationProved ≡ false
hamiltonianDominationProvedIsFalse =
  refl

osTransferProvedIsFalse :
  osTransferProved ≡ false
osTransferProvedIsFalse =
  refl

spectralGapLiftThroughQuotientProvedIsFalse :
  spectralGapLiftThroughQuotientProved ≡ false
spectralGapLiftThroughQuotientProvedIsFalse =
  refl

continuumTransferProvedIsFalse :
  continuumTransferProved ≡ false
continuumTransferProvedIsFalse =
  refl

ymClayPromotedIsFalse :
  ymClayPromoted ≡ false
ymClayPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

finiteGaugeQuotientSelfAdjointHamiltonianCompositeFormula : String
finiteGaugeQuotientSelfAdjointHamiltonianCompositeFormula =
  "finite gauge quotient carrier + Killing boundary cancellation/domain descent + finite symmetric Hamiltonian => self-adjoint finite Hamiltonian on the gauge quotient"

------------------------------------------------------------------------
-- Canonical composite boundary.

record
  YMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary : Setω
  where
  field
    status :
      YMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeStatus

    support :
      YMFiniteGaugeQuotientSelfAdjointHamiltonianSupport

    supportCanonical :
      Bool

    supportCanonicalIsTrue :
      supportCanonical ≡ true

    supportInputs :
      List YMFiniteGaugeQuotientSelfAdjointHamiltonianSupportInput

    supportInputsAreCanonical :
      supportInputs
      ≡
      canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianSupportInputs

    supportInputCount :
      Nat

    supportInputCountIs4 :
      supportInputCount ≡ 4

    theoremTarget :
      YMFiniteGaugeQuotientSelfAdjointHamiltonianTheoremTarget

    theoremTargetIsCanonical :
      theoremTarget
      ≡
      canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianTheoremTarget

    stages :
      List YMFiniteGaugeQuotientSelfAdjointHamiltonianStage

    stagesAreCanonical :
      stages
      ≡
      canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianStages

    stageCount :
      Nat

    stageCountIs11 :
      stageCount ≡ 11

    rows :
      List YMFiniteGaugeQuotientSelfAdjointHamiltonianStageRow

    rowsAreCanonical :
      rows
      ≡
      canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianRows

    rowCount :
      Nat

    rowCountIs11 :
      rowCount ≡ 11

    blockers :
      List YMFiniteGaugeQuotientSelfAdjointHamiltonianBlocker

    blockersAreCanonical :
      blockers
      ≡
      canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianBlockers

    blockerCount :
      Nat

    blockerCountIs12 :
      blockerCount ≡ 12

    exactFirstBlocker :
      YMFiniteGaugeQuotientSelfAdjointHamiltonianBlocker

    exactFirstBlockerIsFiniteGaugeQuotientCarrier :
      exactFirstBlocker
      ≡
      missingFiniteGaugeQuotientCarrierComposite

    formula :
      String

    formulaIsCanonical :
      formula
      ≡
      finiteGaugeQuotientSelfAdjointHamiltonianCompositeFormula

    compositeBoundaryRecordedField :
      Bool

    compositeBoundaryRecordedFieldIsTrue :
      compositeBoundaryRecordedField ≡ true

    theoremTargetRecordedField :
      Bool

    theoremTargetRecordedFieldIsTrue :
      theoremTargetRecordedField ≡ true

    finiteGaugeQuotientCarrierConstructedField :
      Bool

    finiteGaugeQuotientCarrierConstructedFieldIsFalse :
      finiteGaugeQuotientCarrierConstructedField ≡ false

    quotientHamiltonianDescentProvedField :
      Bool

    quotientHamiltonianDescentProvedFieldIsFalse :
      quotientHamiltonianDescentProvedField ≡ false

    finiteSymmetricHamiltonianProvedField :
      Bool

    finiteSymmetricHamiltonianProvedFieldIsFalse :
      finiteSymmetricHamiltonianProvedField ≡ false

    selfAdjointFiniteHamiltonianOnQuotientProvedField :
      Bool

    selfAdjointFiniteHamiltonianOnQuotientProvedFieldIsFalse :
      selfAdjointFiniteHamiltonianOnQuotientProvedField ≡ false

    finiteDiscreteSpectrumExtractedField :
      Bool

    finiteDiscreteSpectrumExtractedFieldIsFalse :
      finiteDiscreteSpectrumExtractedField ≡ false

    hamiltonianDominationProvedField :
      Bool

    hamiltonianDominationProvedFieldIsFalse :
      hamiltonianDominationProvedField ≡ false

    osTransferProvedField :
      Bool

    osTransferProvedFieldIsFalse :
      osTransferProvedField ≡ false

    spectralGapLiftThroughQuotientProvedField :
      Bool

    spectralGapLiftThroughQuotientProvedFieldIsFalse :
      spectralGapLiftThroughQuotientProvedField ≡ false

    continuumTransferProvedField :
      Bool

    continuumTransferProvedFieldIsFalse :
      continuumTransferProvedField ≡ false

    ymClayPromotedField :
      Bool

    ymClayPromotedFieldIsFalse :
      ymClayPromotedField ≡ false

    terminalPromotionField :
      Bool

    terminalPromotionFieldIsFalse :
      terminalPromotionField ≡ false

    importedPreconditionFiniteQuotientStillFalse :
      Precondition.finiteQuotientConstructedField
        (preconditionBoundary support)
      ≡
      false

    importedPreconditionSelfAdjointStillFalse :
      Precondition.selfAdjointHamiltonianProvedField
        (preconditionBoundary support)
      ≡
      false

    importedPreconditionDominationStillFalse :
      Precondition.hamiltonianDominationProvedField
        (preconditionBoundary support)
      ≡
      false

    importedKillingFiniteSelfAdjointStillFalse :
      Killing.ym1FiniteSelfAdjointHamiltonianProvedField
        (killingSelfAdjointnessComposite support)
      ≡
      false

    importedKillingDominationStillFalse :
      Killing.hamiltonianDominationProvedField
        (killingSelfAdjointnessComposite support)
      ≡
      false

    importedKillingOSStillFalse :
      Killing.osContinuumTransferProvedField
        (killingSelfAdjointnessComposite support)
      ≡
      false

    importedFiniteDomainStillFalse :
      Finite.finiteDomainConstructedField
        (finiteSelfAdjointHamiltonianBoundary support)
      ≡
      false

    importedFiniteSymmetricFormStillFalse :
      Finite.symmetricFormProvedField
        (finiteSelfAdjointHamiltonianBoundary support)
      ≡
      false

    importedFiniteQuotientDescentStillFalse :
      Finite.gaugeQuotientDescentProvedField
        (finiteSelfAdjointHamiltonianBoundary support)
      ≡
      false

    importedFiniteSelfAdjointStillFalse :
      Finite.selfAdjointFiniteHamiltonianProvedField
        (finiteSelfAdjointHamiltonianBoundary support)
      ≡
      false

    importedFiniteDominationUnlockedStillFalse :
      Finite.hamiltonianDominationUnlockedField
        (finiteSelfAdjointHamiltonianBoundary support)
      ≡
      false

    importedQuotientGapCarrierStillFalse :
      QuotientGap.gaugeQuotientHilbertCarrierConstructedField
        (quotientGapBoundary support)
      ≡
      false

    importedQuotientGapOSStillFalse :
      QuotientGap.reflectionPositivityOSCompatibilityProvedField
        (quotientGapBoundary support)
      ≡
      false

    importedQuotientGapSelfAdjointDomainStillFalse :
      QuotientGap.selfAdjointHamiltonianDomainConstructedField
        (quotientGapBoundary support)
      ≡
      false

    importedQuotientGapSpectralLiftStillFalse :
      QuotientGap.spectralGapLiftThroughQuotientProvedField
        (quotientGapBoundary support)
      ≡
      false

    importedQuotientGapContinuumStillFalse :
      QuotientGap.continuumTransferFromQuotientGapProvedField
        (quotientGapBoundary support)
      ≡
      false

    importedClayFlagsStillFalse :
      List Bool

    importedClayFlagsStillFalseAreCanonical :
      importedClayFlagsStillFalse
      ≡
      ( Precondition.clayYMField
          (preconditionBoundary support)
        ∷ Killing.ymClayPromotedField
          (killingSelfAdjointnessComposite support)
        ∷ Finite.clayYangMillsPromotedField
          (finiteSelfAdjointHamiltonianBoundary support)
        ∷ QuotientGap.clayYangMillsPromotedField
          (quotientGapBoundary support)
        ∷ [] )

    notes :
      List String

open YMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary public

canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary :
  YMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary
canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary =
  record
    { status =
        finiteGaugeQuotientSelfAdjointHamiltonianTargetRecordedProofOpen
    ; support =
        canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianSupport
    ; supportCanonical =
        true
    ; supportCanonicalIsTrue =
        refl
    ; supportInputs =
        canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianSupportInputs
    ; supportInputsAreCanonical =
        refl
    ; supportInputCount =
        listCount
          canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianSupportInputs
    ; supportInputCountIs4 =
        refl
    ; theoremTarget =
        canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianTheoremTarget
    ; theoremTargetIsCanonical =
        refl
    ; stages =
        canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianStages
    ; stagesAreCanonical =
        refl
    ; stageCount =
        listCount canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianStages
    ; stageCountIs11 =
        refl
    ; rows =
        canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianRows
    ; rowsAreCanonical =
        refl
    ; rowCount =
        listCount canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianRows
    ; rowCountIs11 =
        refl
    ; blockers =
        canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCount =
        listCount canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianBlockers
    ; blockerCountIs12 =
        refl
    ; exactFirstBlocker =
        missingFiniteGaugeQuotientCarrierComposite
    ; exactFirstBlockerIsFiniteGaugeQuotientCarrier =
        refl
    ; formula =
        finiteGaugeQuotientSelfAdjointHamiltonianCompositeFormula
    ; formulaIsCanonical =
        refl
    ; compositeBoundaryRecordedField =
        compositeBoundaryRecorded
    ; compositeBoundaryRecordedFieldIsTrue =
        compositeBoundaryRecordedIsTrue
    ; theoremTargetRecordedField =
        finiteGaugeQuotientSelfAdjointHamiltonianTargetRecorded
    ; theoremTargetRecordedFieldIsTrue =
        finiteGaugeQuotientSelfAdjointHamiltonianTargetRecordedIsTrue
    ; finiteGaugeQuotientCarrierConstructedField =
        finiteGaugeQuotientCarrierConstructed
    ; finiteGaugeQuotientCarrierConstructedFieldIsFalse =
        finiteGaugeQuotientCarrierConstructedIsFalse
    ; quotientHamiltonianDescentProvedField =
        quotientHamiltonianDescentProved
    ; quotientHamiltonianDescentProvedFieldIsFalse =
        quotientHamiltonianDescentProvedIsFalse
    ; finiteSymmetricHamiltonianProvedField =
        finiteSymmetricHamiltonianProved
    ; finiteSymmetricHamiltonianProvedFieldIsFalse =
        finiteSymmetricHamiltonianProvedIsFalse
    ; selfAdjointFiniteHamiltonianOnQuotientProvedField =
        selfAdjointFiniteHamiltonianOnQuotientProved
    ; selfAdjointFiniteHamiltonianOnQuotientProvedFieldIsFalse =
        selfAdjointFiniteHamiltonianOnQuotientProvedIsFalse
    ; finiteDiscreteSpectrumExtractedField =
        finiteDiscreteSpectrumExtracted
    ; finiteDiscreteSpectrumExtractedFieldIsFalse =
        finiteDiscreteSpectrumExtractedIsFalse
    ; hamiltonianDominationProvedField =
        hamiltonianDominationProved
    ; hamiltonianDominationProvedFieldIsFalse =
        hamiltonianDominationProvedIsFalse
    ; osTransferProvedField =
        osTransferProved
    ; osTransferProvedFieldIsFalse =
        osTransferProvedIsFalse
    ; spectralGapLiftThroughQuotientProvedField =
        spectralGapLiftThroughQuotientProved
    ; spectralGapLiftThroughQuotientProvedFieldIsFalse =
        spectralGapLiftThroughQuotientProvedIsFalse
    ; continuumTransferProvedField =
        continuumTransferProved
    ; continuumTransferProvedFieldIsFalse =
        continuumTransferProvedIsFalse
    ; ymClayPromotedField =
        ymClayPromoted
    ; ymClayPromotedFieldIsFalse =
        ymClayPromotedIsFalse
    ; terminalPromotionField =
        terminalPromotion
    ; terminalPromotionFieldIsFalse =
        terminalPromotionIsFalse
    ; importedPreconditionFiniteQuotientStillFalse =
        Precondition.canonicalFiniteQuotientConstructedFalse
    ; importedPreconditionSelfAdjointStillFalse =
        Precondition.canonicalSelfAdjointHamiltonianProvedFalse
    ; importedPreconditionDominationStillFalse =
        Precondition.canonicalHamiltonianDominationProvedFalse
    ; importedKillingFiniteSelfAdjointStillFalse =
        Killing.canonicalCompositeYM1FiniteSelfAdjointHamiltonianFalse
    ; importedKillingDominationStillFalse =
        Killing.canonicalCompositeHamiltonianDominationFalse
    ; importedKillingOSStillFalse =
        Killing.canonicalCompositeOSTransferFalse
    ; importedFiniteDomainStillFalse =
        Finite.canonicalFiniteDomainConstructedFalse
    ; importedFiniteSymmetricFormStillFalse =
        Finite.canonicalSymmetricFormProvedFalse
    ; importedFiniteQuotientDescentStillFalse =
        Finite.canonicalGaugeQuotientDescentProvedFalse
    ; importedFiniteSelfAdjointStillFalse =
        Finite.canonicalSelfAdjointFiniteHamiltonianProvedFalse
    ; importedFiniteDominationUnlockedStillFalse =
        Finite.canonicalHamiltonianDominationUnlockedFalse
    ; importedQuotientGapCarrierStillFalse =
        QuotientGap.gaugeQuotientHilbertCarrierConstructedFieldIsFalse
          QuotientGap.canonicalYMSelfAdjointHamiltonianQuotientGapBoundary
    ; importedQuotientGapOSStillFalse =
        QuotientGap.reflectionPositivityOSCompatibilityProvedFieldIsFalse
          QuotientGap.canonicalYMSelfAdjointHamiltonianQuotientGapBoundary
    ; importedQuotientGapSelfAdjointDomainStillFalse =
        QuotientGap.canonicalYMHamiltonianQuotientGapSelfAdjointDomainFalse
    ; importedQuotientGapSpectralLiftStillFalse =
        QuotientGap.spectralGapLiftThroughQuotientProvedFieldIsFalse
          QuotientGap.canonicalYMSelfAdjointHamiltonianQuotientGapBoundary
    ; importedQuotientGapContinuumStillFalse =
        QuotientGap.continuumTransferFromQuotientGapProvedFieldIsFalse
          QuotientGap.canonicalYMSelfAdjointHamiltonianQuotientGapBoundary
    ; importedClayFlagsStillFalse =
        false ∷ false ∷ false ∷ false ∷ []
    ; importedClayFlagsStillFalseAreCanonical =
        refl
    ; notes =
        "The composite consumes the finite gauge quotient precondition, Killing-boundary self-adjointness composite, finite self-adjoint Hamiltonian boundary, and quotient-gap boundary."
        ∷ "The theorem target is finite gauge quotient carrier plus Hamiltonian descent plus finite symmetric IBP, yielding a self-adjoint finite Hamiltonian on quotient states."
        ∷ "The current first blocker is the missing finite gauge quotient carrier; quotient descent, symmetric finite Hamiltonian, and finite self-adjointness remain downstream theorem obligations."
        ∷ "Hamiltonian domination, OS transfer, spectral-gap lift, continuum transfer, YM Clay, and terminal promotion are deliberately held false."
        ∷ []
    }

------------------------------------------------------------------------
-- Count, guard, and no-promotion lemmas.

canonicalSupportInputCountIs4 :
  supportInputCount
    canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary
  ≡
  4
canonicalSupportInputCountIs4 =
  refl

canonicalStageCountIs11 :
  stageCount
    canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary
  ≡
  11
canonicalStageCountIs11 =
  refl

canonicalRowCountIs11 :
  rowCount
    canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary
  ≡
  11
canonicalRowCountIs11 =
  refl

canonicalBlockerCountIs12 :
  blockerCount
    canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary
  ≡
  12
canonicalBlockerCountIs12 =
  refl

canonicalCompositeTheoremTargetRecordedTrue :
  theoremTargetRecordedField
    canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary
  ≡
  true
canonicalCompositeTheoremTargetRecordedTrue =
  refl

canonicalCompositeFiniteGaugeQuotientCarrierFalse :
  finiteGaugeQuotientCarrierConstructedField
    canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary
  ≡
  false
canonicalCompositeFiniteGaugeQuotientCarrierFalse =
  refl

canonicalCompositeSelfAdjointFiniteHamiltonianFalse :
  selfAdjointFiniteHamiltonianOnQuotientProvedField
    canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary
  ≡
  false
canonicalCompositeSelfAdjointFiniteHamiltonianFalse =
  refl

canonicalCompositeHamiltonianDominationFalse :
  hamiltonianDominationProvedField
    canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary
  ≡
  false
canonicalCompositeHamiltonianDominationFalse =
  refl

canonicalCompositeOSTransferFalse :
  osTransferProvedField
    canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary
  ≡
  false
canonicalCompositeOSTransferFalse =
  refl

canonicalCompositeSpectralGapLiftFalse :
  spectralGapLiftThroughQuotientProvedField
    canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary
  ≡
  false
canonicalCompositeSpectralGapLiftFalse =
  refl

canonicalCompositeContinuumTransferFalse :
  continuumTransferProvedField
    canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary
  ≡
  false
canonicalCompositeContinuumTransferFalse =
  refl

canonicalCompositeYMClayFalse :
  ymClayPromotedField
    canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary
  ≡
  false
canonicalCompositeYMClayFalse =
  refl

canonicalCompositeTerminalFalse :
  terminalPromotionField
    canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary
  ≡
  false
canonicalCompositeTerminalFalse =
  refl

data YMFiniteGaugeQuotientSelfAdjointHamiltonianPromotionToken : Set where

ymFiniteGaugeQuotientSelfAdjointHamiltonianPromotionTokenImpossibleHere :
  YMFiniteGaugeQuotientSelfAdjointHamiltonianPromotionToken →
  ⊥
ymFiniteGaugeQuotientSelfAdjointHamiltonianPromotionTokenImpossibleHere ()

noTheoremPromotionFromCompositeBoundaryAlone :
  selfAdjointFiniteHamiltonianOnQuotientProvedField
    canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary
  ≡
  true →
  ⊥
noTheoremPromotionFromCompositeBoundaryAlone ()

noDominationPromotionFromCompositeBoundaryAlone :
  hamiltonianDominationProvedField
    canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary
  ≡
  true →
  ⊥
noDominationPromotionFromCompositeBoundaryAlone ()

noOSTransferPromotionFromCompositeBoundaryAlone :
  osTransferProvedField
    canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary
  ≡
  true →
  ⊥
noOSTransferPromotionFromCompositeBoundaryAlone ()

noYMClayPromotionFromCompositeBoundaryAlone :
  ymClayPromotedField
    canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary
  ≡
  true →
  ⊥
noYMClayPromotionFromCompositeBoundaryAlone ()

ogfControlCard : String
ogfControlCard =
  "O finite gauge-quotient self-adjoint Hamiltonian composite; R compose finite quotient preconditions, Killing boundary self-adjointness, finite Hamiltonian, and quotient-gap surfaces into the theorem target; C imports the four requested boundary modules only as qualified support; S target recorded true while quotient carrier, descent, finite self-adjointness, domination, OS, spectral lift, continuum transfer, YM Clay, and terminal promotion are false; L first blocker is finite gauge quotient carrier before quotient descent and finite IBP symmetry; P construct quotient carrier and descent before using finite-dimensional self-adjointness; G no theorem or Clay promotion token is introduced; F fail-closed boundary ledger only."

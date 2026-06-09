module DASHI.Physics.Closure.YMQuotientHamiltonianDescentCompositeBoundary where

-- Composite boundary for Hamiltonian descent to the finite gauge quotient.
--
-- This receipt sits between the finite gauge quotient carrier construction
-- target and the finite self-adjoint Hamiltonian handoff.  It composes:
--
--   finite gauge quotient carrier construction,
--   finite gauge quotient self-adjoint Hamiltonian composite,
--   Killing/full-degree boundary self-adjointness composite,
--   finite self-adjoint Hamiltonian boundary.
--
-- The theorem target is the well-defined descent of H_d from a finite
-- Killing-boundary domain to gauge-orbit classes, followed by the operator
-- handoff to the finite self-adjoint quotient Hamiltonian.  This module is a
-- fail-closed boundary ledger only: it does not construct the quotient
-- carrier, does not prove gauge equivariance, does not prove descent, does
-- not prove self-adjointness, does not prove Hamiltonian domination, does not
-- prove OS/continuum transfer, and does not promote Yang-Mills Clay or
-- terminal claims.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMFiniteGaugeQuotientCarrierConstructionBoundary
  as Carrier
import DASHI.Physics.Closure.YMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary
  as QuotientSelfAdjoint
import DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessCompositeBoundary
  as Killing
import DASHI.Physics.Closure.YMSelfAdjointFiniteHamiltonianBoundary
  as Finite

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Imported support.

data YMQuotientHamiltonianDescentSupportInput : Set where
  finiteGaugeQuotientCarrierConstructionConsumed :
    YMQuotientHamiltonianDescentSupportInput

  finiteGaugeQuotientSelfAdjointHamiltonianCompositeConsumed :
    YMQuotientHamiltonianDescentSupportInput

  killingBoundarySelfAdjointnessCompositeConsumed :
    YMQuotientHamiltonianDescentSupportInput

  selfAdjointFiniteHamiltonianBoundaryConsumed :
    YMQuotientHamiltonianDescentSupportInput

canonicalYMQuotientHamiltonianDescentSupportInputs :
  List YMQuotientHamiltonianDescentSupportInput
canonicalYMQuotientHamiltonianDescentSupportInputs =
  finiteGaugeQuotientCarrierConstructionConsumed
  ∷ finiteGaugeQuotientSelfAdjointHamiltonianCompositeConsumed
  ∷ killingBoundarySelfAdjointnessCompositeConsumed
  ∷ selfAdjointFiniteHamiltonianBoundaryConsumed
  ∷ []

record YMQuotientHamiltonianDescentSupport : Setω where
  field
    carrierConstructionBoundary :
      Carrier.YMFiniteGaugeQuotientCarrierConstructionBoundary

    carrierConstructionBoundaryCanonical :
      Bool

    carrierConstructionBoundaryCanonicalIsTrue :
      carrierConstructionBoundaryCanonical ≡ true

    quotientSelfAdjointComposite :
      QuotientSelfAdjoint.YMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary

    quotientSelfAdjointCompositeCanonical :
      Bool

    quotientSelfAdjointCompositeCanonicalIsTrue :
      quotientSelfAdjointCompositeCanonical ≡ true

    killingBoundarySelfAdjointnessComposite :
      Killing.YMKillingBoundarySelfAdjointnessCompositeBoundary

    killingBoundarySelfAdjointnessCompositeCanonical :
      Bool

    killingBoundarySelfAdjointnessCompositeCanonicalIsTrue :
      killingBoundarySelfAdjointnessCompositeCanonical ≡ true

    selfAdjointFiniteHamiltonianBoundary :
      Finite.YMSelfAdjointFiniteHamiltonianBoundary

    selfAdjointFiniteHamiltonianBoundaryCanonical :
      Bool

    selfAdjointFiniteHamiltonianBoundaryCanonicalIsTrue :
      selfAdjointFiniteHamiltonianBoundaryCanonical ≡ true

open YMQuotientHamiltonianDescentSupport public

canonicalYMQuotientHamiltonianDescentSupport :
  YMQuotientHamiltonianDescentSupport
canonicalYMQuotientHamiltonianDescentSupport =
  record
    { carrierConstructionBoundary =
        Carrier.canonicalYMFiniteGaugeQuotientCarrierConstructionBoundary
    ; carrierConstructionBoundaryCanonical =
        true
    ; carrierConstructionBoundaryCanonicalIsTrue =
        refl
    ; quotientSelfAdjointComposite =
        QuotientSelfAdjoint.canonicalYMFiniteGaugeQuotientSelfAdjointHamiltonianCompositeBoundary
    ; quotientSelfAdjointCompositeCanonical =
        true
    ; quotientSelfAdjointCompositeCanonicalIsTrue =
        refl
    ; killingBoundarySelfAdjointnessComposite =
        Killing.canonicalYMKillingBoundarySelfAdjointnessCompositeBoundary
    ; killingBoundarySelfAdjointnessCompositeCanonical =
        true
    ; killingBoundarySelfAdjointnessCompositeCanonicalIsTrue =
        refl
    ; selfAdjointFiniteHamiltonianBoundary =
        Finite.canonicalYMSelfAdjointFiniteHamiltonianBoundary
    ; selfAdjointFiniteHamiltonianBoundaryCanonical =
        true
    ; selfAdjointFiniteHamiltonianBoundaryCanonicalIsTrue =
        refl
    }

------------------------------------------------------------------------
-- Descent theorem target and route.

data YMQuotientHamiltonianDescentCompositeStatus : Set where
  quotientHamiltonianDescentTargetRecordedProofOpen :
    YMQuotientHamiltonianDescentCompositeStatus

data YMQuotientHamiltonianDescentTheoremTarget : Set where
  hamiltonianDescendsToFiniteGaugeQuotientAndHandsOffTarget :
    YMQuotientHamiltonianDescentTheoremTarget

canonicalYMQuotientHamiltonianDescentTheoremTarget :
  YMQuotientHamiltonianDescentTheoremTarget
canonicalYMQuotientHamiltonianDescentTheoremTarget =
  hamiltonianDescendsToFiniteGaugeQuotientAndHandsOffTarget

data YMQuotientHamiltonianDescentStage : Set where
  consumeFiniteGaugeQuotientCarrierConstruction :
    YMQuotientHamiltonianDescentStage

  consumeKillingBoundarySelfAdjointnessComposite :
    YMQuotientHamiltonianDescentStage

  consumeFiniteSelfAdjointHamiltonianBoundary :
    YMQuotientHamiltonianDescentStage

  consumeQuotientSelfAdjointHamiltonianComposite :
    YMQuotientHamiltonianDescentStage

  alignFiniteOrbitCarrierWithKillingDomain :
    YMQuotientHamiltonianDescentStage

  proveGaugeActionPreservesOperatorDomain :
    YMQuotientHamiltonianDescentStage

  proveHamiltonianGaugeEquivarianceOnDomain :
    YMQuotientHamiltonianDescentStage

  proveHamiltonianConstantOnOrbitRepresentatives :
    YMQuotientHamiltonianDescentStage

  proveHamiltonianDescendsToQuotientClasses :
    YMQuotientHamiltonianDescentStage

  proveQuotientPairingCompatibility :
    YMQuotientHamiltonianDescentStage

  proveDescendedOperatorSymmetric :
    YMQuotientHamiltonianDescentStage

  handoffToFiniteSelfAdjointQuotientHamiltonian :
    YMQuotientHamiltonianDescentStage

  keepDominationAndSpectralGapBlocked :
    YMQuotientHamiltonianDescentStage

  keepOSTransferContinuumAndClayBlocked :
    YMQuotientHamiltonianDescentStage

canonicalYMQuotientHamiltonianDescentStages :
  List YMQuotientHamiltonianDescentStage
canonicalYMQuotientHamiltonianDescentStages =
  consumeFiniteGaugeQuotientCarrierConstruction
  ∷ consumeKillingBoundarySelfAdjointnessComposite
  ∷ consumeFiniteSelfAdjointHamiltonianBoundary
  ∷ consumeQuotientSelfAdjointHamiltonianComposite
  ∷ alignFiniteOrbitCarrierWithKillingDomain
  ∷ proveGaugeActionPreservesOperatorDomain
  ∷ proveHamiltonianGaugeEquivarianceOnDomain
  ∷ proveHamiltonianConstantOnOrbitRepresentatives
  ∷ proveHamiltonianDescendsToQuotientClasses
  ∷ proveQuotientPairingCompatibility
  ∷ proveDescendedOperatorSymmetric
  ∷ handoffToFiniteSelfAdjointQuotientHamiltonian
  ∷ keepDominationAndSpectralGapBlocked
  ∷ keepOSTransferContinuumAndClayBlocked
  ∷ []

data YMQuotientHamiltonianDescentStageStatus : Set where
  upstreamBoundaryConsumed :
    YMQuotientHamiltonianDescentStageStatus

  carrierDomainAlignmentObligationOpen :
    YMQuotientHamiltonianDescentStageStatus

  quotientDescentObligationOpen :
    YMQuotientHamiltonianDescentStageStatus

  symmetryHandoffObligationOpen :
    YMQuotientHamiltonianDescentStageStatus

  downstreamBlocked :
    YMQuotientHamiltonianDescentStageStatus

  promotionHeldFalse :
    YMQuotientHamiltonianDescentStageStatus

ymQuotientHamiltonianDescentStageStatus :
  YMQuotientHamiltonianDescentStage →
  YMQuotientHamiltonianDescentStageStatus
ymQuotientHamiltonianDescentStageStatus
  consumeFiniteGaugeQuotientCarrierConstruction =
  upstreamBoundaryConsumed
ymQuotientHamiltonianDescentStageStatus
  consumeKillingBoundarySelfAdjointnessComposite =
  upstreamBoundaryConsumed
ymQuotientHamiltonianDescentStageStatus
  consumeFiniteSelfAdjointHamiltonianBoundary =
  upstreamBoundaryConsumed
ymQuotientHamiltonianDescentStageStatus
  consumeQuotientSelfAdjointHamiltonianComposite =
  upstreamBoundaryConsumed
ymQuotientHamiltonianDescentStageStatus
  alignFiniteOrbitCarrierWithKillingDomain =
  carrierDomainAlignmentObligationOpen
ymQuotientHamiltonianDescentStageStatus
  proveGaugeActionPreservesOperatorDomain =
  carrierDomainAlignmentObligationOpen
ymQuotientHamiltonianDescentStageStatus
  proveHamiltonianGaugeEquivarianceOnDomain =
  quotientDescentObligationOpen
ymQuotientHamiltonianDescentStageStatus
  proveHamiltonianConstantOnOrbitRepresentatives =
  quotientDescentObligationOpen
ymQuotientHamiltonianDescentStageStatus
  proveHamiltonianDescendsToQuotientClasses =
  quotientDescentObligationOpen
ymQuotientHamiltonianDescentStageStatus
  proveQuotientPairingCompatibility =
  symmetryHandoffObligationOpen
ymQuotientHamiltonianDescentStageStatus
  proveDescendedOperatorSymmetric =
  symmetryHandoffObligationOpen
ymQuotientHamiltonianDescentStageStatus
  handoffToFiniteSelfAdjointQuotientHamiltonian =
  downstreamBlocked
ymQuotientHamiltonianDescentStageStatus
  keepDominationAndSpectralGapBlocked =
  downstreamBlocked
ymQuotientHamiltonianDescentStageStatus
  keepOSTransferContinuumAndClayBlocked =
  promotionHeldFalse

record YMQuotientHamiltonianDescentStageRow : Set where
  field
    stage :
      YMQuotientHamiltonianDescentStage

    status :
      YMQuotientHamiltonianDescentStageStatus

    statusIsCanonical :
      status ≡ ymQuotientHamiltonianDescentStageStatus stage

    proofSurface :
      String

    theoremProvedHere :
      Bool

    theoremProvedHereIsFalse :
      theoremProvedHere ≡ false

open YMQuotientHamiltonianDescentStageRow public

mkYMQuotientHamiltonianDescentStageRow :
  YMQuotientHamiltonianDescentStage →
  String →
  YMQuotientHamiltonianDescentStageRow
mkYMQuotientHamiltonianDescentStageRow stage proofSurface =
  record
    { stage =
        stage
    ; status =
        ymQuotientHamiltonianDescentStageStatus stage
    ; statusIsCanonical =
        refl
    ; proofSurface =
        proofSurface
    ; theoremProvedHere =
        false
    ; theoremProvedHereIsFalse =
        refl
    }

canonicalYMQuotientHamiltonianDescentStageRows :
  List YMQuotientHamiltonianDescentStageRow
canonicalYMQuotientHamiltonianDescentStageRows =
  mkYMQuotientHamiltonianDescentStageRow
    consumeFiniteGaugeQuotientCarrierConstruction
    "Consume the finite orbit carrier construction target and its descent preconditions."
  ∷ mkYMQuotientHamiltonianDescentStageRow
    consumeKillingBoundarySelfAdjointnessComposite
    "Consume the Killing/full-degree boundary route as the finite-domain symmetry contract."
  ∷ mkYMQuotientHamiltonianDescentStageRow
    consumeFiniteSelfAdjointHamiltonianBoundary
    "Consume the finite Hamiltonian self-adjointness vocabulary and fail-closed flags."
  ∷ mkYMQuotientHamiltonianDescentStageRow
    consumeQuotientSelfAdjointHamiltonianComposite
    "Consume the quotient self-adjoint Hamiltonian composite as the downstream handoff."
  ∷ mkYMQuotientHamiltonianDescentStageRow
    alignFiniteOrbitCarrierWithKillingDomain
    "Align finite orbit representatives with the full-degree Killing-boundary operator domain."
  ∷ mkYMQuotientHamiltonianDescentStageRow
    proveGaugeActionPreservesOperatorDomain
    "Prove each finite gauge action sends admissible domain representatives to admissible representatives."
  ∷ mkYMQuotientHamiltonianDescentStageRow
    proveHamiltonianGaugeEquivarianceOnDomain
    "Prove H_d(g . phi) = g . H_d(phi) on the finite Killing-boundary domain."
  ∷ mkYMQuotientHamiltonianDescentStageRow
    proveHamiltonianConstantOnOrbitRepresentatives
    "Prove equivalent representatives yield equivalent Hamiltonian outputs."
  ∷ mkYMQuotientHamiltonianDescentStageRow
    proveHamiltonianDescendsToQuotientClasses
    "Define the descended quotient operator H_d^quot on finite gauge-orbit classes."
  ∷ mkYMQuotientHamiltonianDescentStageRow
    proveQuotientPairingCompatibility
    "Prove the invariant quotient pairing is respected by the descended operator."
  ∷ mkYMQuotientHamiltonianDescentStageRow
    proveDescendedOperatorSymmetric
    "Use Killing boundary cancellation and quotient pairing compatibility to prove finite symmetry."
  ∷ mkYMQuotientHamiltonianDescentStageRow
    handoffToFiniteSelfAdjointQuotientHamiltonian
    "Hand the descended symmetric finite operator to the quotient self-adjointness composite."
  ∷ mkYMQuotientHamiltonianDescentStageRow
    keepDominationAndSpectralGapBlocked
    "Keep Hamiltonian domination and finite spectral-margin extraction blocked after descent."
  ∷ mkYMQuotientHamiltonianDescentStageRow
    keepOSTransferContinuumAndClayBlocked
    "Keep OS transfer, continuum no-spectral-pollution, Yang-Mills Clay, and terminal promotion false."
  ∷ []

------------------------------------------------------------------------
-- Explicit descent blockers and preconditions.

data YMQuotientHamiltonianDescentBlocker : Set where
  missingCarrierOrbitRepresentativeContract :
    YMQuotientHamiltonianDescentBlocker

  missingKillingDomainGaugeStability :
    YMQuotientHamiltonianDescentBlocker

  missingFiniteHamiltonianGaugeEquivariance :
    YMQuotientHamiltonianDescentBlocker

  missingOrbitClassOutputWellDefinedness :
    YMQuotientHamiltonianDescentBlocker

  missingQuotientOperatorDefinition :
    YMQuotientHamiltonianDescentBlocker

  missingInvariantPairingCompatibility :
    YMQuotientHamiltonianDescentBlocker

  missingDescendedOperatorSymmetry :
    YMQuotientHamiltonianDescentBlocker

  missingFiniteSelfAdjointHandoff :
    YMQuotientHamiltonianDescentBlocker

  missingFiniteDiscreteSpectrumAfterHandoff :
    YMQuotientHamiltonianDescentBlocker

  missingHamiltonianDominationAfterDescent :
    YMQuotientHamiltonianDescentBlocker

  missingOSReflectionPositiveTransfer :
    YMQuotientHamiltonianDescentBlocker

  missingContinuumNoSpectralPollution :
    YMQuotientHamiltonianDescentBlocker

  missingYangMillsClayAuthorityToken :
    YMQuotientHamiltonianDescentBlocker

canonicalYMQuotientHamiltonianDescentBlockers :
  List YMQuotientHamiltonianDescentBlocker
canonicalYMQuotientHamiltonianDescentBlockers =
  missingCarrierOrbitRepresentativeContract
  ∷ missingKillingDomainGaugeStability
  ∷ missingFiniteHamiltonianGaugeEquivariance
  ∷ missingOrbitClassOutputWellDefinedness
  ∷ missingQuotientOperatorDefinition
  ∷ missingInvariantPairingCompatibility
  ∷ missingDescendedOperatorSymmetry
  ∷ missingFiniteSelfAdjointHandoff
  ∷ missingFiniteDiscreteSpectrumAfterHandoff
  ∷ missingHamiltonianDominationAfterDescent
  ∷ missingOSReflectionPositiveTransfer
  ∷ missingContinuumNoSpectralPollution
  ∷ missingYangMillsClayAuthorityToken
  ∷ []

data YMQuotientHamiltonianDescentPrecondition : Set where
  quotientCarrierExists :
    YMQuotientHamiltonianDescentPrecondition

  finiteGaugeOrbitRelationStable :
    YMQuotientHamiltonianDescentPrecondition

  quotientPairingPositiveAndGaugeInvariant :
    YMQuotientHamiltonianDescentPrecondition

  killingBoundaryDomainRepresentativeInvariant :
    YMQuotientHamiltonianDescentPrecondition

  hamiltonianGaugeEquivarianceOnFiniteDomain :
    YMQuotientHamiltonianDescentPrecondition

  hamiltonianOutputRespectsOrbitRelation :
    YMQuotientHamiltonianDescentPrecondition

  descendedOperatorSymmetricForQuotientPairing :
    YMQuotientHamiltonianDescentPrecondition

  finiteSelfAdjointHandoffAccepted :
    YMQuotientHamiltonianDescentPrecondition

canonicalYMQuotientHamiltonianDescentPreconditions :
  List YMQuotientHamiltonianDescentPrecondition
canonicalYMQuotientHamiltonianDescentPreconditions =
  quotientCarrierExists
  ∷ finiteGaugeOrbitRelationStable
  ∷ quotientPairingPositiveAndGaugeInvariant
  ∷ killingBoundaryDomainRepresentativeInvariant
  ∷ hamiltonianGaugeEquivarianceOnFiniteDomain
  ∷ hamiltonianOutputRespectsOrbitRelation
  ∷ descendedOperatorSymmetricForQuotientPairing
  ∷ finiteSelfAdjointHandoffAccepted
  ∷ []

quotientHamiltonianDescentFormula : String
quotientHamiltonianDescentFormula =
  "finite quotient carrier + Killing-domain representative invariance + H_d gauge equivariance + orbit-output well-definedness + quotient-pairing symmetry => descended finite self-adjoint Hamiltonian handoff"

------------------------------------------------------------------------
-- Fail-closed theorem and promotion flags.

boundaryRecorded : Bool
boundaryRecorded =
  true

supportComposed : Bool
supportComposed =
  true

quotientHamiltonianDescentTargetRecorded : Bool
quotientHamiltonianDescentTargetRecorded =
  true

quotientCarrierConstructed : Bool
quotientCarrierConstructed =
  false

killingDomainGaugeStabilityProved : Bool
killingDomainGaugeStabilityProved =
  false

hamiltonianGaugeEquivarianceProved : Bool
hamiltonianGaugeEquivarianceProved =
  false

orbitClassWellDefinednessProved : Bool
orbitClassWellDefinednessProved =
  false

quotientHamiltonianDescentProved : Bool
quotientHamiltonianDescentProved =
  false

descendedOperatorSymmetricProved : Bool
descendedOperatorSymmetricProved =
  false

selfAdjointQuotientHamiltonianHandoffProved : Bool
selfAdjointQuotientHamiltonianHandoffProved =
  false

finiteSpectrumExtracted : Bool
finiteSpectrumExtracted =
  false

hamiltonianDominationProved : Bool
hamiltonianDominationProved =
  false

osTransferProved : Bool
osTransferProved =
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

boundaryRecordedIsTrue :
  boundaryRecorded ≡ true
boundaryRecordedIsTrue =
  refl

supportComposedIsTrue :
  supportComposed ≡ true
supportComposedIsTrue =
  refl

quotientHamiltonianDescentTargetRecordedIsTrue :
  quotientHamiltonianDescentTargetRecorded ≡ true
quotientHamiltonianDescentTargetRecordedIsTrue =
  refl

quotientCarrierConstructedIsFalse :
  quotientCarrierConstructed ≡ false
quotientCarrierConstructedIsFalse =
  refl

killingDomainGaugeStabilityProvedIsFalse :
  killingDomainGaugeStabilityProved ≡ false
killingDomainGaugeStabilityProvedIsFalse =
  refl

hamiltonianGaugeEquivarianceProvedIsFalse :
  hamiltonianGaugeEquivarianceProved ≡ false
hamiltonianGaugeEquivarianceProvedIsFalse =
  refl

orbitClassWellDefinednessProvedIsFalse :
  orbitClassWellDefinednessProved ≡ false
orbitClassWellDefinednessProvedIsFalse =
  refl

quotientHamiltonianDescentProvedIsFalse :
  quotientHamiltonianDescentProved ≡ false
quotientHamiltonianDescentProvedIsFalse =
  refl

descendedOperatorSymmetricProvedIsFalse :
  descendedOperatorSymmetricProved ≡ false
descendedOperatorSymmetricProvedIsFalse =
  refl

selfAdjointQuotientHamiltonianHandoffProvedIsFalse :
  selfAdjointQuotientHamiltonianHandoffProved ≡ false
selfAdjointQuotientHamiltonianHandoffProvedIsFalse =
  refl

finiteSpectrumExtractedIsFalse :
  finiteSpectrumExtracted ≡ false
finiteSpectrumExtractedIsFalse =
  refl

hamiltonianDominationProvedIsFalse :
  hamiltonianDominationProved ≡ false
hamiltonianDominationProvedIsFalse =
  refl

osTransferProvedIsFalse :
  osTransferProved ≡ false
osTransferProvedIsFalse =
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

------------------------------------------------------------------------
-- Canonical boundary.

record YMQuotientHamiltonianDescentCompositeBoundary : Setω where
  field
    support :
      YMQuotientHamiltonianDescentSupport

    supportInputCount :
      Nat

    supportInputCountIsFour :
      supportInputCount ≡ suc (suc (suc (suc zero)))

    theoremTarget :
      YMQuotientHamiltonianDescentTheoremTarget

    status :
      YMQuotientHamiltonianDescentCompositeStatus

    stageRows :
      List YMQuotientHamiltonianDescentStageRow

    stageCount :
      Nat

    stageCountIsFourteen :
      stageCount
      ≡ suc
          (suc
            (suc
              (suc
                (suc
                  (suc
                    (suc
                      (suc
                        (suc
                          (suc
                            (suc
                              (suc
                                (suc (suc zero)))))))))))))

    blockers :
      List YMQuotientHamiltonianDescentBlocker

    blockerCount :
      Nat

    blockerCountIsThirteen :
      blockerCount
      ≡ suc
          (suc
            (suc
              (suc
                (suc
                  (suc
                    (suc
                      (suc
                        (suc
                          (suc
                            (suc
                              (suc (suc zero))))))))))))

    descentPreconditions :
      List YMQuotientHamiltonianDescentPrecondition

    descentPreconditionCount :
      Nat

    descentPreconditionCountIsEight :
      descentPreconditionCount
      ≡ suc (suc (suc (suc (suc (suc (suc (suc zero)))))))

    formula :
      String

    boundaryRecordedField :
      Bool

    boundaryRecordedFieldIsTrue :
      boundaryRecordedField ≡ true

    supportComposedField :
      Bool

    supportComposedFieldIsTrue :
      supportComposedField ≡ true

    quotientHamiltonianDescentTargetRecordedField :
      Bool

    quotientHamiltonianDescentTargetRecordedFieldIsTrue :
      quotientHamiltonianDescentTargetRecordedField ≡ true

    quotientCarrierConstructedField :
      Bool

    quotientCarrierConstructedFieldIsFalse :
      quotientCarrierConstructedField ≡ false

    killingDomainGaugeStabilityProvedField :
      Bool

    killingDomainGaugeStabilityProvedFieldIsFalse :
      killingDomainGaugeStabilityProvedField ≡ false

    hamiltonianGaugeEquivarianceProvedField :
      Bool

    hamiltonianGaugeEquivarianceProvedFieldIsFalse :
      hamiltonianGaugeEquivarianceProvedField ≡ false

    orbitClassWellDefinednessProvedField :
      Bool

    orbitClassWellDefinednessProvedFieldIsFalse :
      orbitClassWellDefinednessProvedField ≡ false

    quotientHamiltonianDescentProvedField :
      Bool

    quotientHamiltonianDescentProvedFieldIsFalse :
      quotientHamiltonianDescentProvedField ≡ false

    descendedOperatorSymmetricProvedField :
      Bool

    descendedOperatorSymmetricProvedFieldIsFalse :
      descendedOperatorSymmetricProvedField ≡ false

    selfAdjointQuotientHamiltonianHandoffProvedField :
      Bool

    selfAdjointQuotientHamiltonianHandoffProvedFieldIsFalse :
      selfAdjointQuotientHamiltonianHandoffProvedField ≡ false

    finiteSpectrumExtractedField :
      Bool

    finiteSpectrumExtractedFieldIsFalse :
      finiteSpectrumExtractedField ≡ false

    hamiltonianDominationProvedField :
      Bool

    hamiltonianDominationProvedFieldIsFalse :
      hamiltonianDominationProvedField ≡ false

    osTransferProvedField :
      Bool

    osTransferProvedFieldIsFalse :
      osTransferProvedField ≡ false

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

    receipt :
      String

open YMQuotientHamiltonianDescentCompositeBoundary public

canonicalYMQuotientHamiltonianDescentCompositeBoundary :
  YMQuotientHamiltonianDescentCompositeBoundary
canonicalYMQuotientHamiltonianDescentCompositeBoundary =
  record
    { support =
        canonicalYMQuotientHamiltonianDescentSupport
    ; supportInputCount =
        listCount canonicalYMQuotientHamiltonianDescentSupportInputs
    ; supportInputCountIsFour =
        refl
    ; theoremTarget =
        canonicalYMQuotientHamiltonianDescentTheoremTarget
    ; status =
        quotientHamiltonianDescentTargetRecordedProofOpen
    ; stageRows =
        canonicalYMQuotientHamiltonianDescentStageRows
    ; stageCount =
        listCount canonicalYMQuotientHamiltonianDescentStageRows
    ; stageCountIsFourteen =
        refl
    ; blockers =
        canonicalYMQuotientHamiltonianDescentBlockers
    ; blockerCount =
        listCount canonicalYMQuotientHamiltonianDescentBlockers
    ; blockerCountIsThirteen =
        refl
    ; descentPreconditions =
        canonicalYMQuotientHamiltonianDescentPreconditions
    ; descentPreconditionCount =
        listCount canonicalYMQuotientHamiltonianDescentPreconditions
    ; descentPreconditionCountIsEight =
        refl
    ; formula =
        quotientHamiltonianDescentFormula
    ; boundaryRecordedField =
        boundaryRecorded
    ; boundaryRecordedFieldIsTrue =
        boundaryRecordedIsTrue
    ; supportComposedField =
        supportComposed
    ; supportComposedFieldIsTrue =
        supportComposedIsTrue
    ; quotientHamiltonianDescentTargetRecordedField =
        quotientHamiltonianDescentTargetRecorded
    ; quotientHamiltonianDescentTargetRecordedFieldIsTrue =
        quotientHamiltonianDescentTargetRecordedIsTrue
    ; quotientCarrierConstructedField =
        quotientCarrierConstructed
    ; quotientCarrierConstructedFieldIsFalse =
        quotientCarrierConstructedIsFalse
    ; killingDomainGaugeStabilityProvedField =
        killingDomainGaugeStabilityProved
    ; killingDomainGaugeStabilityProvedFieldIsFalse =
        killingDomainGaugeStabilityProvedIsFalse
    ; hamiltonianGaugeEquivarianceProvedField =
        hamiltonianGaugeEquivarianceProved
    ; hamiltonianGaugeEquivarianceProvedFieldIsFalse =
        hamiltonianGaugeEquivarianceProvedIsFalse
    ; orbitClassWellDefinednessProvedField =
        orbitClassWellDefinednessProved
    ; orbitClassWellDefinednessProvedFieldIsFalse =
        orbitClassWellDefinednessProvedIsFalse
    ; quotientHamiltonianDescentProvedField =
        quotientHamiltonianDescentProved
    ; quotientHamiltonianDescentProvedFieldIsFalse =
        quotientHamiltonianDescentProvedIsFalse
    ; descendedOperatorSymmetricProvedField =
        descendedOperatorSymmetricProved
    ; descendedOperatorSymmetricProvedFieldIsFalse =
        descendedOperatorSymmetricProvedIsFalse
    ; selfAdjointQuotientHamiltonianHandoffProvedField =
        selfAdjointQuotientHamiltonianHandoffProved
    ; selfAdjointQuotientHamiltonianHandoffProvedFieldIsFalse =
        selfAdjointQuotientHamiltonianHandoffProvedIsFalse
    ; finiteSpectrumExtractedField =
        finiteSpectrumExtracted
    ; finiteSpectrumExtractedFieldIsFalse =
        finiteSpectrumExtractedIsFalse
    ; hamiltonianDominationProvedField =
        hamiltonianDominationProved
    ; hamiltonianDominationProvedFieldIsFalse =
        hamiltonianDominationProvedIsFalse
    ; osTransferProvedField =
        osTransferProved
    ; osTransferProvedFieldIsFalse =
        osTransferProvedIsFalse
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
    ; receipt =
        "O YM quotient Hamiltonian descent composite; R compose finite quotient carrier, Killing self-adjointness, finite self-adjoint Hamiltonian, and quotient self-adjoint Hamiltonian surfaces; C records descent and handoff preconditions only; S target recorded true while quotient carrier, gauge equivariance, orbit well-definedness, descended symmetry, finite spectrum, domination, OS, continuum transfer, YM Clay, and terminal promotion are false; L carrier/domain alignment -> equivariance -> orbit-class descent -> quotient symmetry -> finite self-adjoint handoff -> downstream domination/OS gates; P prove descent before any Hamiltonian domination or mass-gap transfer; G no theorem or promotion token is introduced; F fail-closed boundary receipt only."
    }

------------------------------------------------------------------------
-- Guard lemmas and no-promotion contradictions.

canonicalSupportInputCountIsFour :
  supportInputCount canonicalYMQuotientHamiltonianDescentCompositeBoundary
  ≡ suc (suc (suc (suc zero)))
canonicalSupportInputCountIsFour =
  refl

canonicalStageCountIsFourteen :
  stageCount canonicalYMQuotientHamiltonianDescentCompositeBoundary
  ≡ suc
      (suc
        (suc
          (suc
            (suc
              (suc
                (suc
                  (suc
                    (suc
                      (suc
                        (suc
                          (suc
                            (suc (suc zero)))))))))))))
canonicalStageCountIsFourteen =
  refl

canonicalBlockerCountIsThirteen :
  blockerCount canonicalYMQuotientHamiltonianDescentCompositeBoundary
  ≡ suc
      (suc
        (suc
          (suc
            (suc
              (suc
                (suc
                  (suc
                    (suc
                      (suc
                        (suc
                          (suc (suc zero))))))))))))
canonicalBlockerCountIsThirteen =
  refl

canonicalDescentPreconditionCountIsEight :
  descentPreconditionCount
    canonicalYMQuotientHamiltonianDescentCompositeBoundary
  ≡ suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
canonicalDescentPreconditionCountIsEight =
  refl

descentTargetRecordedButUnproved :
  quotientHamiltonianDescentTargetRecordedField
    canonicalYMQuotientHamiltonianDescentCompositeBoundary
  ≡ true
descentTargetRecordedButUnproved =
  refl

quotientCarrierStillUnconstructed :
  quotientCarrierConstructedField
    canonicalYMQuotientHamiltonianDescentCompositeBoundary
  ≡ false
quotientCarrierStillUnconstructed =
  refl

gaugeEquivarianceStillOpen :
  hamiltonianGaugeEquivarianceProvedField
    canonicalYMQuotientHamiltonianDescentCompositeBoundary
  ≡ false
gaugeEquivarianceStillOpen =
  refl

orbitWellDefinednessStillOpen :
  orbitClassWellDefinednessProvedField
    canonicalYMQuotientHamiltonianDescentCompositeBoundary
  ≡ false
orbitWellDefinednessStillOpen =
  refl

quotientDescentStillOpen :
  quotientHamiltonianDescentProvedField
    canonicalYMQuotientHamiltonianDescentCompositeBoundary
  ≡ false
quotientDescentStillOpen =
  refl

descendedSymmetryStillOpen :
  descendedOperatorSymmetricProvedField
    canonicalYMQuotientHamiltonianDescentCompositeBoundary
  ≡ false
descendedSymmetryStillOpen =
  refl

selfAdjointHandoffStillOpen :
  selfAdjointQuotientHamiltonianHandoffProvedField
    canonicalYMQuotientHamiltonianDescentCompositeBoundary
  ≡ false
selfAdjointHandoffStillOpen =
  refl

noHamiltonianDominationFromDescentBoundaryAlone :
  hamiltonianDominationProvedField
    canonicalYMQuotientHamiltonianDescentCompositeBoundary
  ≡ false
noHamiltonianDominationFromDescentBoundaryAlone =
  refl

noOSOrContinuumTransferFromDescentBoundaryAlone :
  osTransferProvedField canonicalYMQuotientHamiltonianDescentCompositeBoundary
  ≡ false
noOSOrContinuumTransferFromDescentBoundaryAlone =
  refl

noYMClayPromotionFromDescentBoundaryAlone :
  ymClayPromotedField canonicalYMQuotientHamiltonianDescentCompositeBoundary
  ≡ true →
  ⊥
noYMClayPromotionFromDescentBoundaryAlone ()

noTerminalPromotionFromDescentBoundaryAlone :
  terminalPromotionField canonicalYMQuotientHamiltonianDescentCompositeBoundary
  ≡ true →
  ⊥
noTerminalPromotionFromDescentBoundaryAlone ()

ymQuotientHamiltonianDescentCompositeBoundaryReceipt : String
ymQuotientHamiltonianDescentCompositeBoundaryReceipt =
  receipt canonicalYMQuotientHamiltonianDescentCompositeBoundary

module DASHI.Physics.Closure.YMAdmissibleBTBoundaryConventionBoundary where

-- Boundary convention receipt for the finite Bruhat-Tits/YM lane.
--
-- Local finite-tree calculations exposed a necessary precondition for the
-- current route:
--
--   induced finite-ball truncations may collapse the finite-tree spectral gap
--   signal, while full-degree / killing-style boundary conventions preserve
--   the nonamenable-tree gap signal in the tested harnesses.
--
-- This file records that boundary convention as an admissibility gate for the
-- current YM route.  It does not prove the physical Hamiltonian domination
-- theorem, does not construct the finite gauge quotient, does not prove
-- reflection positivity or OS transfer, and keeps YM/Clay promotion false.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMBruhatTitsToOSLatticeTransferBoundary as OS
import DASHI.Physics.Closure.YMHamiltonianDominatesFiniteHodgeDefectBoundary as Ham

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Boundary conventions and local calculation observations.

data BTBoundaryConvention : Set where
  inducedFiniteBallConvention :
    BTBoundaryConvention

  inducedRootAnchoredFiniteBallConvention :
    BTBoundaryConvention

  fullDegreeKillingConvention :
    BTBoundaryConvention

  fullDegreeRootAnchoredKillingConvention :
    BTBoundaryConvention

data LocalFiniteTreeGapSignal : Set where
  inducedFiniteBallMayCollapseGapSignal :
    LocalFiniteTreeGapSignal

  inducedRootAnchoredMayCollapseGapSignal :
    LocalFiniteTreeGapSignal

  fullDegreeKillingPreservesCandidateGapSignal :
    LocalFiniteTreeGapSignal

  fullDegreeRootAnchoredPreservesCandidateGapSignal :
    LocalFiniteTreeGapSignal

data YMAdmissibleBoundaryConventionPrecondition : Set where
  rejectInducedBallAsCurrentGapCarrier :
    YMAdmissibleBoundaryConventionPrecondition

  rejectRootAnchoringAloneAsGapCarrier :
    YMAdmissibleBoundaryConventionPrecondition

  requireFullDegreeKillingStyleBoundary :
    YMAdmissibleBoundaryConventionPrecondition

  keepBoundaryChoiceExplicitInGaugeQuotient :
    YMAdmissibleBoundaryConventionPrecondition

  keepHamiltonianDominationAsSeparateTheorem :
    YMAdmissibleBoundaryConventionPrecondition

  keepOSTransferAsSeparateTheorem :
    YMAdmissibleBoundaryConventionPrecondition

canonicalBTBoundaryConventions :
  List BTBoundaryConvention
canonicalBTBoundaryConventions =
  inducedFiniteBallConvention
  ∷ inducedRootAnchoredFiniteBallConvention
  ∷ fullDegreeKillingConvention
  ∷ fullDegreeRootAnchoredKillingConvention
  ∷ []

canonicalLocalFiniteTreeGapSignals :
  List LocalFiniteTreeGapSignal
canonicalLocalFiniteTreeGapSignals =
  inducedFiniteBallMayCollapseGapSignal
  ∷ inducedRootAnchoredMayCollapseGapSignal
  ∷ fullDegreeKillingPreservesCandidateGapSignal
  ∷ fullDegreeRootAnchoredPreservesCandidateGapSignal
  ∷ []

canonicalYMAdmissibleBoundaryConventionPreconditions :
  List YMAdmissibleBoundaryConventionPrecondition
canonicalYMAdmissibleBoundaryConventionPreconditions =
  rejectInducedBallAsCurrentGapCarrier
  ∷ rejectRootAnchoringAloneAsGapCarrier
  ∷ requireFullDegreeKillingStyleBoundary
  ∷ keepBoundaryChoiceExplicitInGaugeQuotient
  ∷ keepHamiltonianDominationAsSeparateTheorem
  ∷ keepOSTransferAsSeparateTheorem
  ∷ []

------------------------------------------------------------------------
-- Fail-closed route blockers.

data YMAdmissibleBTBoundaryConventionBlocker : Set where
  inducedBallBoundaryConventionNotAdmissibleForCurrentGapRoute :
    YMAdmissibleBTBoundaryConventionBlocker

  missingFiniteGaugeQuotientWithFullDegreeBoundary :
    YMAdmissibleBTBoundaryConventionBlocker

  missingHamiltonianDominatesDefectPlusHolonomy :
    YMAdmissibleBTBoundaryConventionBlocker

  missingReflectionPositiveTransferMatrix :
    YMAdmissibleBTBoundaryConventionBlocker

  missingBruhatTitsToOSLatticeTransfer :
    YMAdmissibleBTBoundaryConventionBlocker

  missingContinuumTransferNoSpectralPollution :
    YMAdmissibleBTBoundaryConventionBlocker

  missingClayYangMillsAuthorityToken :
    YMAdmissibleBTBoundaryConventionBlocker

canonicalYMAdmissibleBTBoundaryConventionBlockers :
  List YMAdmissibleBTBoundaryConventionBlocker
canonicalYMAdmissibleBTBoundaryConventionBlockers =
  inducedBallBoundaryConventionNotAdmissibleForCurrentGapRoute
  ∷ missingFiniteGaugeQuotientWithFullDegreeBoundary
  ∷ missingHamiltonianDominatesDefectPlusHolonomy
  ∷ missingReflectionPositiveTransferMatrix
  ∷ missingBruhatTitsToOSLatticeTransfer
  ∷ missingContinuumTransferNoSpectralPollution
  ∷ missingClayYangMillsAuthorityToken
  ∷ []

------------------------------------------------------------------------
-- Recorded / proved flags.

localFiniteTreeBoundaryConventionCalcRecorded : Bool
localFiniteTreeBoundaryConventionCalcRecorded =
  true

inducedBallCollapseRiskRecorded : Bool
inducedBallCollapseRiskRecorded =
  true

fullDegreeCandidateConventionRecorded : Bool
fullDegreeCandidateConventionRecorded =
  true

fullDegreeConventionAcceptedAsAdmissibleCandidate : Bool
fullDegreeConventionAcceptedAsAdmissibleCandidate =
  true

inducedBallAcceptedAsCurrentGapCarrier : Bool
inducedBallAcceptedAsCurrentGapCarrier =
  false

finiteGaugeQuotientWithFullDegreeBoundaryConstructed : Bool
finiteGaugeQuotientWithFullDegreeBoundaryConstructed =
  false

hamiltonianDominatesDefectPlusHolonomyProved : Bool
hamiltonianDominatesDefectPlusHolonomyProved =
  false

reflectionPositiveTransferMatrixProved : Bool
reflectionPositiveTransferMatrixProved =
  false

bruhatTitsToOSLatticeTransferProved : Bool
bruhatTitsToOSLatticeTransferProved =
  false

continuumTransferNoSpectralPollutionProved : Bool
continuumTransferNoSpectralPollutionProved =
  false

finiteYMMassGapPromoted : Bool
finiteYMMassGapPromoted =
  false

clayYangMillsPromoted : Bool
clayYangMillsPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

localFiniteTreeBoundaryConventionCalcRecordedIsTrue :
  localFiniteTreeBoundaryConventionCalcRecorded ≡ true
localFiniteTreeBoundaryConventionCalcRecordedIsTrue =
  refl

inducedBallCollapseRiskRecordedIsTrue :
  inducedBallCollapseRiskRecorded ≡ true
inducedBallCollapseRiskRecordedIsTrue =
  refl

fullDegreeCandidateConventionRecordedIsTrue :
  fullDegreeCandidateConventionRecorded ≡ true
fullDegreeCandidateConventionRecordedIsTrue =
  refl

fullDegreeConventionAcceptedAsAdmissibleCandidateIsTrue :
  fullDegreeConventionAcceptedAsAdmissibleCandidate ≡ true
fullDegreeConventionAcceptedAsAdmissibleCandidateIsTrue =
  refl

inducedBallAcceptedAsCurrentGapCarrierIsFalse :
  inducedBallAcceptedAsCurrentGapCarrier ≡ false
inducedBallAcceptedAsCurrentGapCarrierIsFalse =
  refl

finiteGaugeQuotientWithFullDegreeBoundaryConstructedIsFalse :
  finiteGaugeQuotientWithFullDegreeBoundaryConstructed ≡ false
finiteGaugeQuotientWithFullDegreeBoundaryConstructedIsFalse =
  refl

hamiltonianDominatesDefectPlusHolonomyProvedIsFalse :
  hamiltonianDominatesDefectPlusHolonomyProved ≡ false
hamiltonianDominatesDefectPlusHolonomyProvedIsFalse =
  refl

bruhatTitsToOSLatticeTransferProvedIsFalse :
  bruhatTitsToOSLatticeTransferProved ≡ false
bruhatTitsToOSLatticeTransferProvedIsFalse =
  refl

clayYangMillsPromotedIsFalse :
  clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

------------------------------------------------------------------------
-- Boundary receipt.

record YMAdmissibleBTBoundaryConventionBoundary : Setω where
  field
    consumedHamiltonianDominationBoundary :
      Ham.YMHamiltonianDominatesFiniteHodgeDefectBoundary

    consumedHamiltonianDominationBoundaryCanonical :
      Bool

    consumedHamiltonianDominationBoundaryCanonicalIsTrue :
      consumedHamiltonianDominationBoundaryCanonical ≡ true

    consumedOSTransferBoundary :
      OS.YMBruhatTitsToOSLatticeTransferBoundary

    consumedOSTransferBoundaryCanonical :
      Bool

    consumedOSTransferBoundaryCanonicalIsTrue :
      consumedOSTransferBoundaryCanonical ≡ true

    boundaryConventions :
      List BTBoundaryConvention

    boundaryConventionsCount :
      listCount boundaryConventions ≡
      listCount canonicalBTBoundaryConventions

    localGapSignals :
      List LocalFiniteTreeGapSignal

    localGapSignalsCount :
      listCount localGapSignals ≡
      listCount canonicalLocalFiniteTreeGapSignals

    admissibilityPreconditions :
      List YMAdmissibleBoundaryConventionPrecondition

    admissibilityPreconditionsCount :
      listCount admissibilityPreconditions ≡
      listCount canonicalYMAdmissibleBoundaryConventionPreconditions

    blockers :
      List YMAdmissibleBTBoundaryConventionBlocker

    blockersCount :
      listCount blockers ≡
      listCount canonicalYMAdmissibleBTBoundaryConventionBlockers

    firstBlocker :
      YMAdmissibleBTBoundaryConventionBlocker

    firstBlockerIsInducedBallConvention :
      firstBlocker ≡
      inducedBallBoundaryConventionNotAdmissibleForCurrentGapRoute

    localCalcRecordedField :
      Bool

    localCalcRecordedFieldIsTrue :
      localCalcRecordedField ≡ true

    inducedBallCollapseRiskRecordedField :
      Bool

    inducedBallCollapseRiskRecordedFieldIsTrue :
      inducedBallCollapseRiskRecordedField ≡ true

    fullDegreeCandidateConventionRecordedField :
      Bool

    fullDegreeCandidateConventionRecordedFieldIsTrue :
      fullDegreeCandidateConventionRecordedField ≡ true

    fullDegreeAdmissibleCandidateField :
      Bool

    fullDegreeAdmissibleCandidateFieldIsTrue :
      fullDegreeAdmissibleCandidateField ≡ true

    inducedBallAcceptedAsCurrentGapCarrierField :
      Bool

    inducedBallAcceptedAsCurrentGapCarrierFieldIsFalse :
      inducedBallAcceptedAsCurrentGapCarrierField ≡ false

    finiteGaugeQuotientWithFullDegreeBoundaryConstructedField :
      Bool

    finiteGaugeQuotientWithFullDegreeBoundaryConstructedFieldIsFalse :
      finiteGaugeQuotientWithFullDegreeBoundaryConstructedField ≡ false

    hamiltonianDominatesDefectPlusHolonomyProvedField :
      Bool

    hamiltonianDominatesDefectPlusHolonomyProvedFieldIsFalse :
      hamiltonianDominatesDefectPlusHolonomyProvedField ≡ false

    reflectionPositiveTransferMatrixProvedField :
      Bool

    reflectionPositiveTransferMatrixProvedFieldIsFalse :
      reflectionPositiveTransferMatrixProvedField ≡ false

    bruhatTitsToOSLatticeTransferProvedField :
      Bool

    bruhatTitsToOSLatticeTransferProvedFieldIsFalse :
      bruhatTitsToOSLatticeTransferProvedField ≡ false

    continuumTransferNoSpectralPollutionProvedField :
      Bool

    continuumTransferNoSpectralPollutionProvedFieldIsFalse :
      continuumTransferNoSpectralPollutionProvedField ≡ false

    finiteYMMassGapPromotedField :
      Bool

    finiteYMMassGapPromotedFieldIsFalse :
      finiteYMMassGapPromotedField ≡ false

    clayYangMillsPromotedField :
      Bool

    clayYangMillsPromotedFieldIsFalse :
      clayYangMillsPromotedField ≡ false

    terminalPromotionField :
      Bool

    terminalPromotionFieldIsFalse :
      terminalPromotionField ≡ false

    notes :
      List String

open YMAdmissibleBTBoundaryConventionBoundary public

canonicalYMAdmissibleBTBoundaryConventionBoundary :
  YMAdmissibleBTBoundaryConventionBoundary
canonicalYMAdmissibleBTBoundaryConventionBoundary =
  record
    { consumedHamiltonianDominationBoundary =
        Ham.canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
    ; consumedHamiltonianDominationBoundaryCanonical =
        true
    ; consumedHamiltonianDominationBoundaryCanonicalIsTrue =
        refl
    ; consumedOSTransferBoundary =
        OS.canonicalYMBruhatTitsToOSLatticeTransferBoundary
    ; consumedOSTransferBoundaryCanonical =
        true
    ; consumedOSTransferBoundaryCanonicalIsTrue =
        refl
    ; boundaryConventions =
        canonicalBTBoundaryConventions
    ; boundaryConventionsCount =
        refl
    ; localGapSignals =
        canonicalLocalFiniteTreeGapSignals
    ; localGapSignalsCount =
        refl
    ; admissibilityPreconditions =
        canonicalYMAdmissibleBoundaryConventionPreconditions
    ; admissibilityPreconditionsCount =
        refl
    ; blockers =
        canonicalYMAdmissibleBTBoundaryConventionBlockers
    ; blockersCount =
        refl
    ; firstBlocker =
        inducedBallBoundaryConventionNotAdmissibleForCurrentGapRoute
    ; firstBlockerIsInducedBallConvention =
        refl
    ; localCalcRecordedField =
        localFiniteTreeBoundaryConventionCalcRecorded
    ; localCalcRecordedFieldIsTrue =
        localFiniteTreeBoundaryConventionCalcRecordedIsTrue
    ; inducedBallCollapseRiskRecordedField =
        inducedBallCollapseRiskRecorded
    ; inducedBallCollapseRiskRecordedFieldIsTrue =
        inducedBallCollapseRiskRecordedIsTrue
    ; fullDegreeCandidateConventionRecordedField =
        fullDegreeCandidateConventionRecorded
    ; fullDegreeCandidateConventionRecordedFieldIsTrue =
        fullDegreeCandidateConventionRecordedIsTrue
    ; fullDegreeAdmissibleCandidateField =
        fullDegreeConventionAcceptedAsAdmissibleCandidate
    ; fullDegreeAdmissibleCandidateFieldIsTrue =
        fullDegreeConventionAcceptedAsAdmissibleCandidateIsTrue
    ; inducedBallAcceptedAsCurrentGapCarrierField =
        inducedBallAcceptedAsCurrentGapCarrier
    ; inducedBallAcceptedAsCurrentGapCarrierFieldIsFalse =
        inducedBallAcceptedAsCurrentGapCarrierIsFalse
    ; finiteGaugeQuotientWithFullDegreeBoundaryConstructedField =
        finiteGaugeQuotientWithFullDegreeBoundaryConstructed
    ; finiteGaugeQuotientWithFullDegreeBoundaryConstructedFieldIsFalse =
        finiteGaugeQuotientWithFullDegreeBoundaryConstructedIsFalse
    ; hamiltonianDominatesDefectPlusHolonomyProvedField =
        hamiltonianDominatesDefectPlusHolonomyProved
    ; hamiltonianDominatesDefectPlusHolonomyProvedFieldIsFalse =
        hamiltonianDominatesDefectPlusHolonomyProvedIsFalse
    ; reflectionPositiveTransferMatrixProvedField =
        reflectionPositiveTransferMatrixProved
    ; reflectionPositiveTransferMatrixProvedFieldIsFalse =
        refl
    ; bruhatTitsToOSLatticeTransferProvedField =
        bruhatTitsToOSLatticeTransferProved
    ; bruhatTitsToOSLatticeTransferProvedFieldIsFalse =
        bruhatTitsToOSLatticeTransferProvedIsFalse
    ; continuumTransferNoSpectralPollutionProvedField =
        continuumTransferNoSpectralPollutionProved
    ; continuumTransferNoSpectralPollutionProvedFieldIsFalse =
        refl
    ; finiteYMMassGapPromotedField =
        finiteYMMassGapPromoted
    ; finiteYMMassGapPromotedFieldIsFalse =
        refl
    ; clayYangMillsPromotedField =
        clayYangMillsPromoted
    ; clayYangMillsPromotedFieldIsFalse =
        clayYangMillsPromotedIsFalse
    ; terminalPromotionField =
        terminalPromotion
    ; terminalPromotionFieldIsFalse =
        terminalPromotionIsFalse
    ; notes =
        "Local finite-tree spectral harnesses exposed a boundary-convention precondition: induced finite balls may collapse the tested gap signal"
        ∷ "Full-degree / killing-style conventions are recorded as the admissible candidate for the current BT/YM route"
        ∷ "The admissible boundary convention is not a Hamiltonian domination theorem and is not an OS/Wightman transfer theorem"
        ∷ "Finite gauge quotient construction, HamiltonianDominatesDefectPlusHolonomy, reflection-positive transfer matrix, BruhatTitsToOSLatticeTransfer, no spectral pollution, Clay Yang-Mills, and terminal promotion remain false"
        ∷ []
    }

canonicalYMAdmissibleBoundaryConventionFirstBlocker :
  firstBlocker canonicalYMAdmissibleBTBoundaryConventionBoundary ≡
  inducedBallBoundaryConventionNotAdmissibleForCurrentGapRoute
canonicalYMAdmissibleBoundaryConventionFirstBlocker =
  refl

canonicalYMAdmissibleBoundaryConventionClayFalse :
  clayYangMillsPromotedField
    canonicalYMAdmissibleBTBoundaryConventionBoundary
  ≡
  false
canonicalYMAdmissibleBoundaryConventionClayFalse =
  refl

canonicalYMAdmissibleBoundaryConventionTerminalFalse :
  terminalPromotionField
    canonicalYMAdmissibleBTBoundaryConventionBoundary
  ≡
  false
canonicalYMAdmissibleBoundaryConventionTerminalFalse =
  refl

noClayPromotionFromAdmissibleBTBoundaryConventionAlone :
  clayYangMillsPromotedField
    canonicalYMAdmissibleBTBoundaryConventionBoundary
  ≡
  true →
  ⊥
noClayPromotionFromAdmissibleBTBoundaryConventionAlone ()

canonicalYMAdmissibleBTBoundaryConventionRecordNames : List String
canonicalYMAdmissibleBTBoundaryConventionRecordNames =
  "YMAdmissibleBTBoundaryConventionBoundary"
  ∷ "BTBoundaryConvention"
  ∷ "LocalFiniteTreeGapSignal"
  ∷ "YMAdmissibleBoundaryConventionPrecondition"
  ∷ "YMAdmissibleBTBoundaryConventionBlocker"
  ∷ "canonicalYMAdmissibleBTBoundaryConventionBoundary"
  ∷ []

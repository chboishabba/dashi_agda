module DASHI.Physics.Closure.YMFiniteGaugeQuotientHamiltonianPreconditionBoundary where

-- Yang-Mills finite gauge quotient / Hamiltonian precondition boundary.
--
-- This receipt records the first-rung operator-theoretic targets needed
-- before the finite BT/YM route can promote a Hamiltonian domination theorem:
--
--   full-degree/Killing boundary domain,
--   finite gauge quotient carrier,
--   self-adjoint finite Hamiltonian,
--   holonomy/action sector split,
--   H_d | Omega^perp >= c1 Delta_YM + c2 Hol - E_d.
--
-- It deliberately does not construct the quotient, does not prove
-- self-adjointness, does not prove the domination inequality, does not prove
-- OS transfer, and does not promote Clay Yang-Mills.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMAdmissibleBTBoundaryConventionBoundary as Admissible
import DASHI.Physics.Closure.YMHamiltonianDominatesFiniteHodgeDefectBoundary as Domination
import DASHI.Physics.Closure.FiniteGaugeHodgeAdjointCompatibility as Adjoint

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- First-rung theorem targets.

data YMFiniteGaugeHamiltonianPreconditionStatus : Set where
  boundaryRecordedFirstRungTargetsOpen :
    YMFiniteGaugeHamiltonianPreconditionStatus

data YMFiniteGaugeHamiltonianPreconditionTarget : Set where
  fullDegreeKillingBoundaryDomainTarget :
    YMFiniteGaugeHamiltonianPreconditionTarget

  finiteGaugeQuotientCarrierTarget :
    YMFiniteGaugeHamiltonianPreconditionTarget

  selfAdjointFiniteHamiltonianTarget :
    YMFiniteGaugeHamiltonianPreconditionTarget

  holonomyActionSectorSplitTarget :
    YMFiniteGaugeHamiltonianPreconditionTarget

  hamiltonianDominatesDeltaHolonomyMinusErrorTarget :
    YMFiniteGaugeHamiltonianPreconditionTarget

canonicalYMFiniteGaugeHamiltonianPreconditionTargets :
  List YMFiniteGaugeHamiltonianPreconditionTarget
canonicalYMFiniteGaugeHamiltonianPreconditionTargets =
  fullDegreeKillingBoundaryDomainTarget
  ∷ finiteGaugeQuotientCarrierTarget
  ∷ selfAdjointFiniteHamiltonianTarget
  ∷ holonomyActionSectorSplitTarget
  ∷ hamiltonianDominatesDeltaHolonomyMinusErrorTarget
  ∷ []

data FullDegreeKillingBoundaryDomain : Set where
  fullDegreeKillingBoundaryDomainStillOpen :
    FullDegreeKillingBoundaryDomain

data GaugeQuotientCarrier : Set where
  finiteGaugeOrbitHilbertCarrierStillOpen :
    GaugeQuotientCarrier

data SelfAdjointFiniteHamiltonian : Set where
  selfAdjointLogTransferHamiltonianStillOpen :
    SelfAdjointFiniteHamiltonian

data HolonomyActionSectorSplit : Set where
  holonomyPositiveActionSectorSplitStillOpen :
    HolonomyActionSectorSplit

data HamiltonianDominationPrerequisiteInequality : Set where
  hamiltonianDominatesDeltaYMHoloMinusErrorStillOpen :
    HamiltonianDominationPrerequisiteInequality

canonicalFullDegreeKillingBoundaryDomain :
  FullDegreeKillingBoundaryDomain
canonicalFullDegreeKillingBoundaryDomain =
  fullDegreeKillingBoundaryDomainStillOpen

canonicalGaugeQuotientCarrier :
  GaugeQuotientCarrier
canonicalGaugeQuotientCarrier =
  finiteGaugeOrbitHilbertCarrierStillOpen

canonicalSelfAdjointFiniteHamiltonian :
  SelfAdjointFiniteHamiltonian
canonicalSelfAdjointFiniteHamiltonian =
  selfAdjointLogTransferHamiltonianStillOpen

canonicalHolonomyActionSectorSplit :
  HolonomyActionSectorSplit
canonicalHolonomyActionSectorSplit =
  holonomyPositiveActionSectorSplitStillOpen

canonicalHamiltonianDominationPrerequisiteInequality :
  HamiltonianDominationPrerequisiteInequality
canonicalHamiltonianDominationPrerequisiteInequality =
  hamiltonianDominatesDeltaYMHoloMinusErrorStillOpen

dominationInequalityFormula : String
dominationInequalityFormula =
  "H_d | Omega^perp >= c1 Delta_YM + c2 Hol - E_d"

------------------------------------------------------------------------
-- Imported support and fail-closed blockers.

data YMFiniteGaugeHamiltonianImportedSupport : Set where
  admissibleBTBoundaryConventionConsumed :
    YMFiniteGaugeHamiltonianImportedSupport

  hamiltonianDominationBoundaryConsumed :
    YMFiniteGaugeHamiltonianImportedSupport

  finiteGaugeHodgeAdjointCompatibilityConsumed :
    YMFiniteGaugeHamiltonianImportedSupport

canonicalYMFiniteGaugeHamiltonianImportedSupport :
  List YMFiniteGaugeHamiltonianImportedSupport
canonicalYMFiniteGaugeHamiltonianImportedSupport =
  admissibleBTBoundaryConventionConsumed
  ∷ hamiltonianDominationBoundaryConsumed
  ∷ finiteGaugeHodgeAdjointCompatibilityConsumed
  ∷ []

data YMFiniteGaugeHamiltonianPreconditionBlocker : Set where
  missingFullDegreeKillingBoundaryDomain :
    YMFiniteGaugeHamiltonianPreconditionBlocker

  missingFiniteGaugeQuotientCarrier :
    YMFiniteGaugeHamiltonianPreconditionBlocker

  missingSelfAdjointFiniteHamiltonian :
    YMFiniteGaugeHamiltonianPreconditionBlocker

  missingHolonomyActionSectorSplit :
    YMFiniteGaugeHamiltonianPreconditionBlocker

  missingHamiltonianDominatesDeltaHolonomyMinusError :
    YMFiniteGaugeHamiltonianPreconditionBlocker

  missingOSTransfer :
    YMFiniteGaugeHamiltonianPreconditionBlocker

  missingContinuumTransferNoSpectralPollution :
    YMFiniteGaugeHamiltonianPreconditionBlocker

  missingClayYangMillsAuthorityToken :
    YMFiniteGaugeHamiltonianPreconditionBlocker

canonicalYMFiniteGaugeHamiltonianPreconditionBlockers :
  List YMFiniteGaugeHamiltonianPreconditionBlocker
canonicalYMFiniteGaugeHamiltonianPreconditionBlockers =
  missingFullDegreeKillingBoundaryDomain
  ∷ missingFiniteGaugeQuotientCarrier
  ∷ missingSelfAdjointFiniteHamiltonian
  ∷ missingHolonomyActionSectorSplit
  ∷ missingHamiltonianDominatesDeltaHolonomyMinusError
  ∷ missingOSTransfer
  ∷ missingContinuumTransferNoSpectralPollution
  ∷ missingClayYangMillsAuthorityToken
  ∷ []

------------------------------------------------------------------------
-- Fail-closed booleans.

boundaryRecorded : Bool
boundaryRecorded =
  true

admissibleBoundaryImported : Bool
admissibleBoundaryImported =
  true

finiteQuotientConstructed : Bool
finiteQuotientConstructed =
  false

selfAdjointHamiltonianProved : Bool
selfAdjointHamiltonianProved =
  false

hamiltonianDominationProved : Bool
hamiltonianDominationProved =
  false

osTransferProved : Bool
osTransferProved =
  false

clayYM : Bool
clayYM =
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

finiteQuotientConstructedIsFalse :
  finiteQuotientConstructed ≡ false
finiteQuotientConstructedIsFalse =
  refl

selfAdjointHamiltonianProvedIsFalse :
  selfAdjointHamiltonianProved ≡ false
selfAdjointHamiltonianProvedIsFalse =
  refl

hamiltonianDominationProvedIsFalse :
  hamiltonianDominationProved ≡ false
hamiltonianDominationProvedIsFalse =
  refl

osTransferProvedIsFalse :
  osTransferProved ≡ false
osTransferProvedIsFalse =
  refl

clayYMIsFalse :
  clayYM ≡ false
clayYMIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

------------------------------------------------------------------------
-- Canonical receipt.

record YMFiniteGaugeQuotientHamiltonianPreconditionBoundary : Setω where
  field
    status :
      YMFiniteGaugeHamiltonianPreconditionStatus

    consumedAdmissibleBoundary :
      Admissible.YMAdmissibleBTBoundaryConventionBoundary

    consumedAdmissibleBoundaryCanonical :
      Bool

    consumedAdmissibleBoundaryCanonicalIsTrue :
      consumedAdmissibleBoundaryCanonical ≡ true

    consumedHamiltonianDominationBoundary :
      Domination.YMHamiltonianDominatesFiniteHodgeDefectBoundary

    consumedHamiltonianDominationBoundaryCanonical :
      Bool

    consumedHamiltonianDominationBoundaryCanonicalIsTrue :
      consumedHamiltonianDominationBoundaryCanonical ≡ true

    consumedFiniteGaugeHodgeAdjointCompatibility :
      Adjoint.FiniteGaugeHodgeAdjointCompatibility

    consumedFiniteGaugeHodgeAdjointCompatibilityCanonical :
      Bool

    consumedFiniteGaugeHodgeAdjointCompatibilityCanonicalIsTrue :
      consumedFiniteGaugeHodgeAdjointCompatibilityCanonical ≡ true

    importedSupport :
      List YMFiniteGaugeHamiltonianImportedSupport

    importedSupportAreCanonical :
      importedSupport ≡ canonicalYMFiniteGaugeHamiltonianImportedSupport

    importedSupportCount :
      Nat

    importedSupportCountIs3 :
      importedSupportCount ≡ 3

    theoremTargets :
      List YMFiniteGaugeHamiltonianPreconditionTarget

    theoremTargetsAreCanonical :
      theoremTargets ≡ canonicalYMFiniteGaugeHamiltonianPreconditionTargets

    theoremTargetCount :
      Nat

    theoremTargetCountIs5 :
      theoremTargetCount ≡ 5

    blockers :
      List YMFiniteGaugeHamiltonianPreconditionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalYMFiniteGaugeHamiltonianPreconditionBlockers

    blockerCount :
      Nat

    blockerCountIs8 :
      blockerCount ≡ 8

    boundaryDomain :
      FullDegreeKillingBoundaryDomain

    boundaryDomainIsCanonical :
      boundaryDomain ≡ canonicalFullDegreeKillingBoundaryDomain

    quotientCarrier :
      GaugeQuotientCarrier

    quotientCarrierIsCanonical :
      quotientCarrier ≡ canonicalGaugeQuotientCarrier

    finiteHamiltonian :
      SelfAdjointFiniteHamiltonian

    finiteHamiltonianIsCanonical :
      finiteHamiltonian ≡ canonicalSelfAdjointFiniteHamiltonian

    sectorSplit :
      HolonomyActionSectorSplit

    sectorSplitIsCanonical :
      sectorSplit ≡ canonicalHolonomyActionSectorSplit

    dominationPrerequisite :
      HamiltonianDominationPrerequisiteInequality

    dominationPrerequisiteIsCanonical :
      dominationPrerequisite
      ≡
      canonicalHamiltonianDominationPrerequisiteInequality

    dominationFormula :
      String

    dominationFormulaIsCanonical :
      dominationFormula ≡ dominationInequalityFormula

    boundaryRecordedField :
      Bool

    boundaryRecordedFieldIsTrue :
      boundaryRecordedField ≡ true

    admissibleBoundaryImportedField :
      Bool

    admissibleBoundaryImportedFieldIsTrue :
      admissibleBoundaryImportedField ≡ true

    finiteQuotientConstructedField :
      Bool

    finiteQuotientConstructedFieldIsFalse :
      finiteQuotientConstructedField ≡ false

    selfAdjointHamiltonianProvedField :
      Bool

    selfAdjointHamiltonianProvedFieldIsFalse :
      selfAdjointHamiltonianProvedField ≡ false

    hamiltonianDominationProvedField :
      Bool

    hamiltonianDominationProvedFieldIsFalse :
      hamiltonianDominationProvedField ≡ false

    osTransferProvedField :
      Bool

    osTransferProvedFieldIsFalse :
      osTransferProvedField ≡ false

    clayYMField :
      Bool

    clayYMFieldIsFalse :
      clayYMField ≡ false

    terminalPromotionField :
      Bool

    terminalPromotionFieldIsFalse :
      terminalPromotionField ≡ false

    notes :
      List String

open YMFiniteGaugeQuotientHamiltonianPreconditionBoundary public

canonicalYMFiniteGaugeQuotientHamiltonianPreconditionBoundary :
  YMFiniteGaugeQuotientHamiltonianPreconditionBoundary
canonicalYMFiniteGaugeQuotientHamiltonianPreconditionBoundary =
  record
    { status =
        boundaryRecordedFirstRungTargetsOpen
    ; consumedAdmissibleBoundary =
        Admissible.canonicalYMAdmissibleBTBoundaryConventionBoundary
    ; consumedAdmissibleBoundaryCanonical =
        true
    ; consumedAdmissibleBoundaryCanonicalIsTrue =
        refl
    ; consumedHamiltonianDominationBoundary =
        Domination.canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
    ; consumedHamiltonianDominationBoundaryCanonical =
        true
    ; consumedHamiltonianDominationBoundaryCanonicalIsTrue =
        refl
    ; consumedFiniteGaugeHodgeAdjointCompatibility =
        Adjoint.canonicalFiniteGaugeHodgeAdjointCompatibility
    ; consumedFiniteGaugeHodgeAdjointCompatibilityCanonical =
        true
    ; consumedFiniteGaugeHodgeAdjointCompatibilityCanonicalIsTrue =
        refl
    ; importedSupport =
        canonicalYMFiniteGaugeHamiltonianImportedSupport
    ; importedSupportAreCanonical =
        refl
    ; importedSupportCount =
        listCount canonicalYMFiniteGaugeHamiltonianImportedSupport
    ; importedSupportCountIs3 =
        refl
    ; theoremTargets =
        canonicalYMFiniteGaugeHamiltonianPreconditionTargets
    ; theoremTargetsAreCanonical =
        refl
    ; theoremTargetCount =
        listCount canonicalYMFiniteGaugeHamiltonianPreconditionTargets
    ; theoremTargetCountIs5 =
        refl
    ; blockers =
        canonicalYMFiniteGaugeHamiltonianPreconditionBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCount =
        listCount canonicalYMFiniteGaugeHamiltonianPreconditionBlockers
    ; blockerCountIs8 =
        refl
    ; boundaryDomain =
        canonicalFullDegreeKillingBoundaryDomain
    ; boundaryDomainIsCanonical =
        refl
    ; quotientCarrier =
        canonicalGaugeQuotientCarrier
    ; quotientCarrierIsCanonical =
        refl
    ; finiteHamiltonian =
        canonicalSelfAdjointFiniteHamiltonian
    ; finiteHamiltonianIsCanonical =
        refl
    ; sectorSplit =
        canonicalHolonomyActionSectorSplit
    ; sectorSplitIsCanonical =
        refl
    ; dominationPrerequisite =
        canonicalHamiltonianDominationPrerequisiteInequality
    ; dominationPrerequisiteIsCanonical =
        refl
    ; dominationFormula =
        dominationInequalityFormula
    ; dominationFormulaIsCanonical =
        refl
    ; boundaryRecordedField =
        boundaryRecorded
    ; boundaryRecordedFieldIsTrue =
        boundaryRecordedIsTrue
    ; admissibleBoundaryImportedField =
        admissibleBoundaryImported
    ; admissibleBoundaryImportedFieldIsTrue =
        admissibleBoundaryImportedIsTrue
    ; finiteQuotientConstructedField =
        finiteQuotientConstructed
    ; finiteQuotientConstructedFieldIsFalse =
        finiteQuotientConstructedIsFalse
    ; selfAdjointHamiltonianProvedField =
        selfAdjointHamiltonianProved
    ; selfAdjointHamiltonianProvedFieldIsFalse =
        selfAdjointHamiltonianProvedIsFalse
    ; hamiltonianDominationProvedField =
        hamiltonianDominationProved
    ; hamiltonianDominationProvedFieldIsFalse =
        hamiltonianDominationProvedIsFalse
    ; osTransferProvedField =
        osTransferProved
    ; osTransferProvedFieldIsFalse =
        osTransferProvedIsFalse
    ; clayYMField =
        clayYM
    ; clayYMFieldIsFalse =
        clayYMIsFalse
    ; terminalPromotionField =
        terminalPromotion
    ; terminalPromotionFieldIsFalse =
        terminalPromotionIsFalse
    ; notes =
        "First-rung YM finite gauge quotient / Hamiltonian preconditions are recorded only as open targets."
        ∷ "Full-degree/Killing boundary domain, gauge quotient carrier, self-adjoint finite Hamiltonian, holonomy/action sector split, and H_d | Omega^perp >= c1 Delta_YM + c2 Hol - E_d remain unproved."
        ∷ "The admissible BT boundary convention, Hamiltonian domination boundary, and finite gauge Hodge adjoint compatibility receipt are consumed as upstream support."
        ∷ "Finite quotient construction, self-adjoint Hamiltonian proof, Hamiltonian domination proof, OS transfer, Clay YM, and terminal promotion remain false."
        ∷ []
    }

------------------------------------------------------------------------
-- Count and guard lemmas.

canonicalImportedSupportCountIs3 :
  importedSupportCount
    canonicalYMFiniteGaugeQuotientHamiltonianPreconditionBoundary
  ≡
  3
canonicalImportedSupportCountIs3 =
  refl

canonicalTheoremTargetCountIs5 :
  theoremTargetCount
    canonicalYMFiniteGaugeQuotientHamiltonianPreconditionBoundary
  ≡
  5
canonicalTheoremTargetCountIs5 =
  refl

canonicalBlockerCountIs8 :
  blockerCount
    canonicalYMFiniteGaugeQuotientHamiltonianPreconditionBoundary
  ≡
  8
canonicalBlockerCountIs8 =
  refl

canonicalBoundaryRecordedTrue :
  boundaryRecordedField
    canonicalYMFiniteGaugeQuotientHamiltonianPreconditionBoundary
  ≡
  true
canonicalBoundaryRecordedTrue =
  refl

canonicalAdmissibleBoundaryImportedTrue :
  admissibleBoundaryImportedField
    canonicalYMFiniteGaugeQuotientHamiltonianPreconditionBoundary
  ≡
  true
canonicalAdmissibleBoundaryImportedTrue =
  refl

canonicalFiniteQuotientConstructedFalse :
  finiteQuotientConstructedField
    canonicalYMFiniteGaugeQuotientHamiltonianPreconditionBoundary
  ≡
  false
canonicalFiniteQuotientConstructedFalse =
  refl

canonicalSelfAdjointHamiltonianProvedFalse :
  selfAdjointHamiltonianProvedField
    canonicalYMFiniteGaugeQuotientHamiltonianPreconditionBoundary
  ≡
  false
canonicalSelfAdjointHamiltonianProvedFalse =
  refl

canonicalHamiltonianDominationProvedFalse :
  hamiltonianDominationProvedField
    canonicalYMFiniteGaugeQuotientHamiltonianPreconditionBoundary
  ≡
  false
canonicalHamiltonianDominationProvedFalse =
  refl

canonicalOSTransferProvedFalse :
  osTransferProvedField
    canonicalYMFiniteGaugeQuotientHamiltonianPreconditionBoundary
  ≡
  false
canonicalOSTransferProvedFalse =
  refl

canonicalClayYMFalse :
  clayYMField
    canonicalYMFiniteGaugeQuotientHamiltonianPreconditionBoundary
  ≡
  false
canonicalClayYMFalse =
  refl

noClayYMFromFiniteGaugeHamiltonianPreconditionBoundaryAlone :
  clayYMField
    canonicalYMFiniteGaugeQuotientHamiltonianPreconditionBoundary
  ≡
  true →
  ⊥
noClayYMFromFiniteGaugeHamiltonianPreconditionBoundaryAlone ()

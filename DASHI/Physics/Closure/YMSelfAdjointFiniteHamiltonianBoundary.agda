module DASHI.Physics.Closure.YMSelfAdjointFiniteHamiltonianBoundary where

-- Finite Yang-Mills Hamiltonian self-adjointness boundary.
--
-- This receipt sits downstream of the finite gauge quotient / Hamiltonian
-- precondition boundary.  It records the finite operator-theoretic theorem
-- that must be supplied before the Hamiltonian domination route can use the
-- finite BT/YM Hamiltonian:
--
--   full-degree/Killing boundary convention,
--   symmetric finite quadratic form,
--   finite domain and gauge-invariant subspace,
--   descent to the gauge quotient,
--   self-adjoint matrix/operator on the quotient,
--   discrete finite spectrum,
--   then only conditionally: domination and OS/continuum transfer.
--
-- It deliberately does not prove self-adjointness, does not prove the
-- Hamiltonian domination inequality, does not prove reflection positivity or
-- OS transfer, and does not promote Clay Yang-Mills.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMAdmissibleBTBoundaryConventionBoundary as Boundary
import DASHI.Physics.Closure.YMFiniteGaugeQuotientHamiltonianPreconditionBoundary
  as Precondition
import DASHI.Physics.Closure.YMSelfAdjointHamiltonianQuotientGapBoundary
  as QuotientGap
import DASHI.Physics.Closure.YMHamiltonianDominatesFiniteHodgeDefectBoundary
  as Domination

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Normalized finite self-adjointness stages.

data YMSelfAdjointFiniteHamiltonianStatus : Set where
  finiteSelfAdjointnessBoundaryRecordedProofStillMissing :
    YMSelfAdjointFiniteHamiltonianStatus

data YMSelfAdjointFiniteHamiltonianStage : Set where
  fullDegreeKillingBoundaryStage :
    YMSelfAdjointFiniteHamiltonianStage

  finiteConfigurationDomainStage :
    YMSelfAdjointFiniteHamiltonianStage

  gaugeInvariantSubspaceStage :
    YMSelfAdjointFiniteHamiltonianStage

  symmetricQuadraticFormStage :
    YMSelfAdjointFiniteHamiltonianStage

  finiteMatrixRepresentativeStage :
    YMSelfAdjointFiniteHamiltonianStage

  gaugeQuotientDescentStage :
    YMSelfAdjointFiniteHamiltonianStage

  selfAdjointFiniteHamiltonianStage :
    YMSelfAdjointFiniteHamiltonianStage

  discreteSpectrumStage :
    YMSelfAdjointFiniteHamiltonianStage

  hamiltonianDominationInputStage :
    YMSelfAdjointFiniteHamiltonianStage

  osContinuumTransferStage :
    YMSelfAdjointFiniteHamiltonianStage

  clayYangMillsPromotionGateStage :
    YMSelfAdjointFiniteHamiltonianStage

canonicalYMSelfAdjointFiniteHamiltonianStages :
  List YMSelfAdjointFiniteHamiltonianStage
canonicalYMSelfAdjointFiniteHamiltonianStages =
  fullDegreeKillingBoundaryStage
  ∷ finiteConfigurationDomainStage
  ∷ gaugeInvariantSubspaceStage
  ∷ symmetricQuadraticFormStage
  ∷ finiteMatrixRepresentativeStage
  ∷ gaugeQuotientDescentStage
  ∷ selfAdjointFiniteHamiltonianStage
  ∷ discreteSpectrumStage
  ∷ hamiltonianDominationInputStage
  ∷ osContinuumTransferStage
  ∷ clayYangMillsPromotionGateStage
  ∷ []

data YMSelfAdjointFiniteHamiltonianStageStatus : Set where
  upstreamPreconditionRecorded :
    YMSelfAdjointFiniteHamiltonianStageStatus

  finiteVocabularyRecorded :
    YMSelfAdjointFiniteHamiltonianStageStatus

  theoremObligationOpen :
    YMSelfAdjointFiniteHamiltonianStageStatus

  downstreamBlocked :
    YMSelfAdjointFiniteHamiltonianStageStatus

  promotionHeldFalse :
    YMSelfAdjointFiniteHamiltonianStageStatus

ymSelfAdjointFiniteHamiltonianStageStatus :
  YMSelfAdjointFiniteHamiltonianStage →
  YMSelfAdjointFiniteHamiltonianStageStatus
ymSelfAdjointFiniteHamiltonianStageStatus fullDegreeKillingBoundaryStage =
  upstreamPreconditionRecorded
ymSelfAdjointFiniteHamiltonianStageStatus finiteConfigurationDomainStage =
  finiteVocabularyRecorded
ymSelfAdjointFiniteHamiltonianStageStatus gaugeInvariantSubspaceStage =
  finiteVocabularyRecorded
ymSelfAdjointFiniteHamiltonianStageStatus symmetricQuadraticFormStage =
  theoremObligationOpen
ymSelfAdjointFiniteHamiltonianStageStatus finiteMatrixRepresentativeStage =
  theoremObligationOpen
ymSelfAdjointFiniteHamiltonianStageStatus gaugeQuotientDescentStage =
  theoremObligationOpen
ymSelfAdjointFiniteHamiltonianStageStatus selfAdjointFiniteHamiltonianStage =
  theoremObligationOpen
ymSelfAdjointFiniteHamiltonianStageStatus discreteSpectrumStage =
  downstreamBlocked
ymSelfAdjointFiniteHamiltonianStageStatus hamiltonianDominationInputStage =
  downstreamBlocked
ymSelfAdjointFiniteHamiltonianStageStatus osContinuumTransferStage =
  downstreamBlocked
ymSelfAdjointFiniteHamiltonianStageStatus clayYangMillsPromotionGateStage =
  promotionHeldFalse

data YMSelfAdjointFiniteHamiltonianBlocker : Set where
  noBlockerForBoundaryVocabulary :
    YMSelfAdjointFiniteHamiltonianBlocker

  missingFiniteDomainClosureUnderKillingBoundary :
    YMSelfAdjointFiniteHamiltonianBlocker

  missingGaugeInvariantSubspaceProjection :
    YMSelfAdjointFiniteHamiltonianBlocker

  missingSymmetricFormIBPBoundaryCancellation :
    YMSelfAdjointFiniteHamiltonianBlocker

  missingFiniteMatrixRepresentativeOnDomain :
    YMSelfAdjointFiniteHamiltonianBlocker

  missingGaugeQuotientDescentWellDefined :
    YMSelfAdjointFiniteHamiltonianBlocker

  missingSelfAdjointFiniteMatrixTheorem :
    YMSelfAdjointFiniteHamiltonianBlocker

  missingDiscreteSpectrumExtraction :
    YMSelfAdjointFiniteHamiltonianBlocker

  missingHamiltonianDominationFromSelfAdjointInput :
    YMSelfAdjointFiniteHamiltonianBlocker

  missingOSTransferFromFiniteSelfAdjointHamiltonian :
    YMSelfAdjointFiniteHamiltonianBlocker

  missingClayYangMillsAuthorityToken :
    YMSelfAdjointFiniteHamiltonianBlocker

ymSelfAdjointFiniteHamiltonianBlocker :
  YMSelfAdjointFiniteHamiltonianStage →
  YMSelfAdjointFiniteHamiltonianBlocker
ymSelfAdjointFiniteHamiltonianBlocker fullDegreeKillingBoundaryStage =
  noBlockerForBoundaryVocabulary
ymSelfAdjointFiniteHamiltonianBlocker finiteConfigurationDomainStage =
  missingFiniteDomainClosureUnderKillingBoundary
ymSelfAdjointFiniteHamiltonianBlocker gaugeInvariantSubspaceStage =
  missingGaugeInvariantSubspaceProjection
ymSelfAdjointFiniteHamiltonianBlocker symmetricQuadraticFormStage =
  missingSymmetricFormIBPBoundaryCancellation
ymSelfAdjointFiniteHamiltonianBlocker finiteMatrixRepresentativeStage =
  missingFiniteMatrixRepresentativeOnDomain
ymSelfAdjointFiniteHamiltonianBlocker gaugeQuotientDescentStage =
  missingGaugeQuotientDescentWellDefined
ymSelfAdjointFiniteHamiltonianBlocker selfAdjointFiniteHamiltonianStage =
  missingSelfAdjointFiniteMatrixTheorem
ymSelfAdjointFiniteHamiltonianBlocker discreteSpectrumStage =
  missingDiscreteSpectrumExtraction
ymSelfAdjointFiniteHamiltonianBlocker hamiltonianDominationInputStage =
  missingHamiltonianDominationFromSelfAdjointInput
ymSelfAdjointFiniteHamiltonianBlocker osContinuumTransferStage =
  missingOSTransferFromFiniteSelfAdjointHamiltonian
ymSelfAdjointFiniteHamiltonianBlocker clayYangMillsPromotionGateStage =
  missingClayYangMillsAuthorityToken

record YMSelfAdjointFiniteHamiltonianStageRow : Set where
  field
    stage :
      YMSelfAdjointFiniteHamiltonianStage

    status :
      YMSelfAdjointFiniteHamiltonianStageStatus

    statusIsCanonical :
      status ≡ ymSelfAdjointFiniteHamiltonianStageStatus stage

    blocker :
      YMSelfAdjointFiniteHamiltonianBlocker

    blockerIsCanonical :
      blocker ≡ ymSelfAdjointFiniteHamiltonianBlocker stage

    proofSurface :
      String

    provedHere :
      Bool

    provedHereIsFalse :
      provedHere ≡ false

open YMSelfAdjointFiniteHamiltonianStageRow public

mkYMSelfAdjointFiniteHamiltonianStageRow :
  YMSelfAdjointFiniteHamiltonianStage →
  String →
  YMSelfAdjointFiniteHamiltonianStageRow
mkYMSelfAdjointFiniteHamiltonianStageRow stage proofSurface =
  record
    { stage =
        stage
    ; status =
        ymSelfAdjointFiniteHamiltonianStageStatus stage
    ; statusIsCanonical =
        refl
    ; blocker =
        ymSelfAdjointFiniteHamiltonianBlocker stage
    ; blockerIsCanonical =
        refl
    ; proofSurface =
        proofSurface
    ; provedHere =
        false
    ; provedHereIsFalse =
        refl
    }

canonicalYMSelfAdjointFiniteHamiltonianRows :
  List YMSelfAdjointFiniteHamiltonianStageRow
canonicalYMSelfAdjointFiniteHamiltonianRows =
  mkYMSelfAdjointFiniteHamiltonianStageRow
    fullDegreeKillingBoundaryStage
    "Consume admissible full-degree/Killing BT boundary convention as finite-domain precondition."
  ∷ mkYMSelfAdjointFiniteHamiltonianStageRow
    finiteConfigurationDomainStage
    "Define the finite cell/configuration domain closed under the Killing boundary convention."
  ∷ mkYMSelfAdjointFiniteHamiltonianStageRow
    gaugeInvariantSubspaceStage
    "Project to gauge-invariant finite states before quotient descent."
  ∷ mkYMSelfAdjointFiniteHamiltonianStageRow
    symmetricQuadraticFormStage
    "Prove <H_d phi, psi> = <phi, H_d psi> from finite Hodge adjointness and boundary cancellation."
  ∷ mkYMSelfAdjointFiniteHamiltonianStageRow
    finiteMatrixRepresentativeStage
    "Represent H_d as a finite symmetric matrix/operator on the chosen domain."
  ∷ mkYMSelfAdjointFiniteHamiltonianStageRow
    gaugeQuotientDescentStage
    "Show H_d is constant on gauge orbits and descends to the finite gauge quotient."
  ∷ mkYMSelfAdjointFiniteHamiltonianStageRow
    selfAdjointFiniteHamiltonianStage
    "Use finite-dimensional symmetry to obtain self-adjointness on the quotient Hilbert carrier."
  ∷ mkYMSelfAdjointFiniteHamiltonianStageRow
    discreteSpectrumStage
    "Extract a real discrete spectrum for the finite quotient Hamiltonian."
  ∷ mkYMSelfAdjointFiniteHamiltonianStageRow
    hamiltonianDominationInputStage
    "Feed the self-adjoint finite Hamiltonian into H_d >= c1 Delta_YM + c2 Hol_d - E_d."
  ∷ mkYMSelfAdjointFiniteHamiltonianStageRow
    osContinuumTransferStage
    "Bridge the finite self-adjoint Hamiltonian to transfer-matrix/OS/continuum hypotheses."
  ∷ mkYMSelfAdjointFiniteHamiltonianStageRow
    clayYangMillsPromotionGateStage
    "Hold Clay Yang-Mills false without domination, OS transfer, and continuum no-spectral-pollution."
  ∷ []

------------------------------------------------------------------------
-- Abstract finite operator theorem surface.

record FiniteYMHamiltonianCarrierBoundary : Setω where
  field
    FiniteDomain :
      Set

    GaugeGroup :
      Set

    GaugeInvariantState :
      Set

    QuotientState :
      Set

    InnerProduct :
      QuotientState → QuotientState → Set

    H-d :
      QuotientState → QuotientState

    vocabularyRecorded :
      Bool

    vocabularyRecordedIsTrue :
      vocabularyRecorded ≡ true

open FiniteYMHamiltonianCarrierBoundary public

record FiniteYMSymmetricFormObligations
  (carrier : FiniteYMHamiltonianCarrierBoundary) : Setω where
  field
    fullDegreeKillingBoundaryClause :
      String

    finiteDomainClause :
      String

    symmetricFormClause :
      String

    gaugeQuotientDescentClause :
      String

    discreteSpectrumClause :
      String

    symmetricFormProved :
      Bool

    symmetricFormProvedIsFalse :
      symmetricFormProved ≡ false

    gaugeQuotientDescentProved :
      Bool

    gaugeQuotientDescentProvedIsFalse :
      gaugeQuotientDescentProved ≡ false

    finiteSelfAdjointnessProved :
      Bool

    finiteSelfAdjointnessProvedIsFalse :
      finiteSelfAdjointnessProved ≡ false

    discreteSpectrumProved :
      Bool

    discreteSpectrumProvedIsFalse :
      discreteSpectrumProved ≡ false

open FiniteYMSymmetricFormObligations public

------------------------------------------------------------------------
-- Imported support ledger.

data YMSelfAdjointFiniteHamiltonianImportedSupport : Set where
  admissibleBTBoundaryConventionConsumed :
    YMSelfAdjointFiniteHamiltonianImportedSupport

  finiteGaugeQuotientPreconditionConsumed :
    YMSelfAdjointFiniteHamiltonianImportedSupport

  olderQuotientGapBoundaryConsumed :
    YMSelfAdjointFiniteHamiltonianImportedSupport

  hamiltonianDominationBoundaryConsumed :
    YMSelfAdjointFiniteHamiltonianImportedSupport

canonicalYMSelfAdjointFiniteHamiltonianImportedSupport :
  List YMSelfAdjointFiniteHamiltonianImportedSupport
canonicalYMSelfAdjointFiniteHamiltonianImportedSupport =
  admissibleBTBoundaryConventionConsumed
  ∷ finiteGaugeQuotientPreconditionConsumed
  ∷ olderQuotientGapBoundaryConsumed
  ∷ hamiltonianDominationBoundaryConsumed
  ∷ []

------------------------------------------------------------------------
-- Fail-closed booleans.

boundaryRecorded : Bool
boundaryRecorded =
  true

finitePreconditionConsumed : Bool
finitePreconditionConsumed =
  true

fullDegreeKillingBoundaryAcceptedAsPrecondition : Bool
fullDegreeKillingBoundaryAcceptedAsPrecondition =
  true

finiteDomainConstructed : Bool
finiteDomainConstructed =
  false

ymFiniteSymmetricFormProved : Bool
ymFiniteSymmetricFormProved =
  false

ymFiniteGaugeQuotientDescentProved : Bool
ymFiniteGaugeQuotientDescentProved =
  false

selfAdjointFiniteHamiltonianProved : Bool
selfAdjointFiniteHamiltonianProved =
  false

ymFiniteDiscreteSpectrumProved : Bool
ymFiniteDiscreteSpectrumProved =
  false

hamiltonianDominationUnlocked : Bool
hamiltonianDominationUnlocked =
  false

osContinuumTransferUnlocked : Bool
osContinuumTransferUnlocked =
  false

clayYangMillsPromoted : Bool
clayYangMillsPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

boundaryRecordedIsTrue :
  boundaryRecorded ≡ true
boundaryRecordedIsTrue =
  refl

finitePreconditionConsumedIsTrue :
  finitePreconditionConsumed ≡ true
finitePreconditionConsumedIsTrue =
  refl

fullDegreeKillingBoundaryAcceptedAsPreconditionIsTrue :
  fullDegreeKillingBoundaryAcceptedAsPrecondition ≡ true
fullDegreeKillingBoundaryAcceptedAsPreconditionIsTrue =
  refl

finiteDomainConstructedIsFalse :
  finiteDomainConstructed ≡ false
finiteDomainConstructedIsFalse =
  refl

ymFiniteSymmetricFormProvedIsFalse :
  ymFiniteSymmetricFormProved ≡ false
ymFiniteSymmetricFormProvedIsFalse =
  refl

ymFiniteGaugeQuotientDescentProvedIsFalse :
  ymFiniteGaugeQuotientDescentProved ≡ false
ymFiniteGaugeQuotientDescentProvedIsFalse =
  refl

selfAdjointFiniteHamiltonianProvedIsFalse :
  selfAdjointFiniteHamiltonianProved ≡ false
selfAdjointFiniteHamiltonianProvedIsFalse =
  refl

ymFiniteDiscreteSpectrumProvedIsFalse :
  ymFiniteDiscreteSpectrumProved ≡ false
ymFiniteDiscreteSpectrumProvedIsFalse =
  refl

hamiltonianDominationUnlockedIsFalse :
  hamiltonianDominationUnlocked ≡ false
hamiltonianDominationUnlockedIsFalse =
  refl

osContinuumTransferUnlockedIsFalse :
  osContinuumTransferUnlocked ≡ false
osContinuumTransferUnlockedIsFalse =
  refl

clayYangMillsPromotedIsFalse :
  clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

hamiltonianDominationFormula : String
hamiltonianDominationFormula =
  "H_d | Omega^perp >= c1 Delta_YM + c2 Hol_d - E_d"

------------------------------------------------------------------------
-- Canonical boundary receipt.

record YMSelfAdjointFiniteHamiltonianBoundary : Setω where
  field
    status :
      YMSelfAdjointFiniteHamiltonianStatus

    admissibleBoundary :
      Boundary.YMAdmissibleBTBoundaryConventionBoundary

    admissibleBoundaryCanonical :
      Bool

    admissibleBoundaryCanonicalIsTrue :
      admissibleBoundaryCanonical ≡ true

    finiteGaugeQuotientPrecondition :
      Precondition.YMFiniteGaugeQuotientHamiltonianPreconditionBoundary

    finiteGaugeQuotientPreconditionCanonical :
      Bool

    finiteGaugeQuotientPreconditionCanonicalIsTrue :
      finiteGaugeQuotientPreconditionCanonical ≡ true

    olderQuotientGapBoundary :
      QuotientGap.YMSelfAdjointHamiltonianQuotientGapBoundary

    olderQuotientGapBoundaryCanonical :
      Bool

    olderQuotientGapBoundaryCanonicalIsTrue :
      olderQuotientGapBoundaryCanonical ≡ true

    hamiltonianDominationBoundary :
      Domination.YMHamiltonianDominatesFiniteHodgeDefectBoundary

    hamiltonianDominationBoundaryCanonical :
      Bool

    hamiltonianDominationBoundaryCanonicalIsTrue :
      hamiltonianDominationBoundaryCanonical ≡ true

    importedSupport :
      List YMSelfAdjointFiniteHamiltonianImportedSupport

    importedSupportIsCanonical :
      importedSupport
      ≡
      canonicalYMSelfAdjointFiniteHamiltonianImportedSupport

    importedSupportCount :
      Nat

    importedSupportCountIs4 :
      importedSupportCount ≡ 4

    stages :
      List YMSelfAdjointFiniteHamiltonianStage

    stagesAreCanonical :
      stages ≡ canonicalYMSelfAdjointFiniteHamiltonianStages

    stageCount :
      Nat

    stageCountIs11 :
      stageCount ≡ 11

    rows :
      List YMSelfAdjointFiniteHamiltonianStageRow

    rowsAreCanonical :
      rows ≡ canonicalYMSelfAdjointFiniteHamiltonianRows

    rowCount :
      Nat

    rowCountIs11 :
      rowCount ≡ 11

    dominationFormula :
      String

    dominationFormulaIsCanonical :
      dominationFormula ≡ hamiltonianDominationFormula

    boundaryRecordedField :
      Bool

    boundaryRecordedFieldIsTrue :
      boundaryRecordedField ≡ true

    finitePreconditionConsumedField :
      Bool

    finitePreconditionConsumedFieldIsTrue :
      finitePreconditionConsumedField ≡ true

    fullDegreeKillingBoundaryAcceptedField :
      Bool

    fullDegreeKillingBoundaryAcceptedFieldIsTrue :
      fullDegreeKillingBoundaryAcceptedField ≡ true

    finiteDomainConstructedField :
      Bool

    finiteDomainConstructedFieldIsFalse :
      finiteDomainConstructedField ≡ false

    symmetricFormProvedField :
      Bool

    symmetricFormProvedFieldIsFalse :
      symmetricFormProvedField ≡ false

    gaugeQuotientDescentProvedField :
      Bool

    gaugeQuotientDescentProvedFieldIsFalse :
      gaugeQuotientDescentProvedField ≡ false

    selfAdjointFiniteHamiltonianProvedField :
      Bool

    selfAdjointFiniteHamiltonianProvedFieldIsFalse :
      selfAdjointFiniteHamiltonianProvedField ≡ false

    discreteSpectrumProvedField :
      Bool

    discreteSpectrumProvedFieldIsFalse :
      discreteSpectrumProvedField ≡ false

    hamiltonianDominationUnlockedField :
      Bool

    hamiltonianDominationUnlockedFieldIsFalse :
      hamiltonianDominationUnlockedField ≡ false

    osContinuumTransferUnlockedField :
      Bool

    osContinuumTransferUnlockedFieldIsFalse :
      osContinuumTransferUnlockedField ≡ false

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

open YMSelfAdjointFiniteHamiltonianBoundary public

canonicalYMSelfAdjointFiniteHamiltonianBoundary :
  YMSelfAdjointFiniteHamiltonianBoundary
canonicalYMSelfAdjointFiniteHamiltonianBoundary =
  record
    { status =
        finiteSelfAdjointnessBoundaryRecordedProofStillMissing
    ; admissibleBoundary =
        Boundary.canonicalYMAdmissibleBTBoundaryConventionBoundary
    ; admissibleBoundaryCanonical =
        true
    ; admissibleBoundaryCanonicalIsTrue =
        refl
    ; finiteGaugeQuotientPrecondition =
        Precondition.canonicalYMFiniteGaugeQuotientHamiltonianPreconditionBoundary
    ; finiteGaugeQuotientPreconditionCanonical =
        true
    ; finiteGaugeQuotientPreconditionCanonicalIsTrue =
        refl
    ; olderQuotientGapBoundary =
        QuotientGap.canonicalYMSelfAdjointHamiltonianQuotientGapBoundary
    ; olderQuotientGapBoundaryCanonical =
        true
    ; olderQuotientGapBoundaryCanonicalIsTrue =
        refl
    ; hamiltonianDominationBoundary =
        Domination.canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
    ; hamiltonianDominationBoundaryCanonical =
        true
    ; hamiltonianDominationBoundaryCanonicalIsTrue =
        refl
    ; importedSupport =
        canonicalYMSelfAdjointFiniteHamiltonianImportedSupport
    ; importedSupportIsCanonical =
        refl
    ; importedSupportCount =
        listCount canonicalYMSelfAdjointFiniteHamiltonianImportedSupport
    ; importedSupportCountIs4 =
        refl
    ; stages =
        canonicalYMSelfAdjointFiniteHamiltonianStages
    ; stagesAreCanonical =
        refl
    ; stageCount =
        listCount canonicalYMSelfAdjointFiniteHamiltonianStages
    ; stageCountIs11 =
        refl
    ; rows =
        canonicalYMSelfAdjointFiniteHamiltonianRows
    ; rowsAreCanonical =
        refl
    ; rowCount =
        listCount canonicalYMSelfAdjointFiniteHamiltonianRows
    ; rowCountIs11 =
        refl
    ; dominationFormula =
        hamiltonianDominationFormula
    ; dominationFormulaIsCanonical =
        refl
    ; boundaryRecordedField =
        boundaryRecorded
    ; boundaryRecordedFieldIsTrue =
        boundaryRecordedIsTrue
    ; finitePreconditionConsumedField =
        finitePreconditionConsumed
    ; finitePreconditionConsumedFieldIsTrue =
        finitePreconditionConsumedIsTrue
    ; fullDegreeKillingBoundaryAcceptedField =
        fullDegreeKillingBoundaryAcceptedAsPrecondition
    ; fullDegreeKillingBoundaryAcceptedFieldIsTrue =
        fullDegreeKillingBoundaryAcceptedAsPreconditionIsTrue
    ; finiteDomainConstructedField =
        finiteDomainConstructed
    ; finiteDomainConstructedFieldIsFalse =
        finiteDomainConstructedIsFalse
    ; symmetricFormProvedField =
        ymFiniteSymmetricFormProved
    ; symmetricFormProvedFieldIsFalse =
        ymFiniteSymmetricFormProvedIsFalse
    ; gaugeQuotientDescentProvedField =
        ymFiniteGaugeQuotientDescentProved
    ; gaugeQuotientDescentProvedFieldIsFalse =
        ymFiniteGaugeQuotientDescentProvedIsFalse
    ; selfAdjointFiniteHamiltonianProvedField =
        selfAdjointFiniteHamiltonianProved
    ; selfAdjointFiniteHamiltonianProvedFieldIsFalse =
        selfAdjointFiniteHamiltonianProvedIsFalse
    ; discreteSpectrumProvedField =
        ymFiniteDiscreteSpectrumProved
    ; discreteSpectrumProvedFieldIsFalse =
        ymFiniteDiscreteSpectrumProvedIsFalse
    ; hamiltonianDominationUnlockedField =
        hamiltonianDominationUnlocked
    ; hamiltonianDominationUnlockedFieldIsFalse =
        hamiltonianDominationUnlockedIsFalse
    ; osContinuumTransferUnlockedField =
        osContinuumTransferUnlocked
    ; osContinuumTransferUnlockedFieldIsFalse =
        osContinuumTransferUnlockedIsFalse
    ; clayYangMillsPromotedField =
        clayYangMillsPromoted
    ; clayYangMillsPromotedFieldIsFalse =
        clayYangMillsPromotedIsFalse
    ; terminalPromotionField =
        terminalPromotion
    ; terminalPromotionFieldIsFalse =
        terminalPromotionIsFalse
    ; notes =
        "This boundary is downstream of the finite gauge quotient Hamiltonian precondition receipt."
        ∷ "The finite theorem still needed is: full-degree/Killing boundary plus finite symmetric form plus gauge quotient descent gives a self-adjoint finite Hamiltonian with discrete spectrum."
        ∷ "Finite-dimensional symmetry would make self-adjointness straightforward only after the domain, quotient descent, and inner product are actually constructed."
        ∷ "Hamiltonian domination, OS transfer, continuum no-spectral-pollution, Clay Yang-Mills, and terminal promotion remain false."
        ∷ []
    }

------------------------------------------------------------------------
-- Guard lemmas and no-promotion contradictions.

canonicalImportedSupportCountIs4 :
  importedSupportCount canonicalYMSelfAdjointFiniteHamiltonianBoundary ≡ 4
canonicalImportedSupportCountIs4 =
  refl

canonicalStageCountIs11 :
  stageCount canonicalYMSelfAdjointFiniteHamiltonianBoundary ≡ 11
canonicalStageCountIs11 =
  refl

canonicalRowCountIs11 :
  rowCount canonicalYMSelfAdjointFiniteHamiltonianBoundary ≡ 11
canonicalRowCountIs11 =
  refl

canonicalBoundaryRecordedTrue :
  boundaryRecordedField canonicalYMSelfAdjointFiniteHamiltonianBoundary
  ≡
  true
canonicalBoundaryRecordedTrue =
  refl

canonicalFinitePreconditionConsumedTrue :
  finitePreconditionConsumedField
    canonicalYMSelfAdjointFiniteHamiltonianBoundary
  ≡
  true
canonicalFinitePreconditionConsumedTrue =
  refl

canonicalFullDegreeKillingBoundaryAcceptedTrue :
  fullDegreeKillingBoundaryAcceptedField
    canonicalYMSelfAdjointFiniteHamiltonianBoundary
  ≡
  true
canonicalFullDegreeKillingBoundaryAcceptedTrue =
  refl

canonicalFiniteDomainConstructedFalse :
  finiteDomainConstructedField canonicalYMSelfAdjointFiniteHamiltonianBoundary
  ≡
  false
canonicalFiniteDomainConstructedFalse =
  refl

canonicalSymmetricFormProvedFalse :
  symmetricFormProvedField canonicalYMSelfAdjointFiniteHamiltonianBoundary
  ≡
  false
canonicalSymmetricFormProvedFalse =
  refl

canonicalGaugeQuotientDescentProvedFalse :
  gaugeQuotientDescentProvedField
    canonicalYMSelfAdjointFiniteHamiltonianBoundary
  ≡
  false
canonicalGaugeQuotientDescentProvedFalse =
  refl

canonicalSelfAdjointFiniteHamiltonianProvedFalse :
  selfAdjointFiniteHamiltonianProvedField
    canonicalYMSelfAdjointFiniteHamiltonianBoundary
  ≡
  false
canonicalSelfAdjointFiniteHamiltonianProvedFalse =
  refl

canonicalDiscreteSpectrumProvedFalse :
  discreteSpectrumProvedField canonicalYMSelfAdjointFiniteHamiltonianBoundary
  ≡
  false
canonicalDiscreteSpectrumProvedFalse =
  refl

canonicalHamiltonianDominationUnlockedFalse :
  hamiltonianDominationUnlockedField
    canonicalYMSelfAdjointFiniteHamiltonianBoundary
  ≡
  false
canonicalHamiltonianDominationUnlockedFalse =
  refl

canonicalOSContinuumTransferUnlockedFalse :
  osContinuumTransferUnlockedField
    canonicalYMSelfAdjointFiniteHamiltonianBoundary
  ≡
  false
canonicalOSContinuumTransferUnlockedFalse =
  refl

canonicalClayYangMillsPromotedFalse :
  clayYangMillsPromotedField canonicalYMSelfAdjointFiniteHamiltonianBoundary
  ≡
  false
canonicalClayYangMillsPromotedFalse =
  refl

canonicalTerminalPromotionFalse :
  terminalPromotionField canonicalYMSelfAdjointFiniteHamiltonianBoundary
  ≡
  false
canonicalTerminalPromotionFalse =
  refl

noHamiltonianDominationFromFiniteSelfAdjointBoundaryAlone :
  hamiltonianDominationUnlockedField
    canonicalYMSelfAdjointFiniteHamiltonianBoundary
  ≡
  true →
  ⊥
noHamiltonianDominationFromFiniteSelfAdjointBoundaryAlone ()

noClayYangMillsFromFiniteSelfAdjointBoundaryAlone :
  clayYangMillsPromotedField canonicalYMSelfAdjointFiniteHamiltonianBoundary
  ≡
  true →
  ⊥
noClayYangMillsFromFiniteSelfAdjointBoundaryAlone ()

noTerminalPromotionFromFiniteSelfAdjointBoundaryAlone :
  terminalPromotionField canonicalYMSelfAdjointFiniteHamiltonianBoundary
  ≡
  true →
  ⊥
noTerminalPromotionFromFiniteSelfAdjointBoundaryAlone ()

canonicalYMSelfAdjointFiniteHamiltonianRecordNames : List String
canonicalYMSelfAdjointFiniteHamiltonianRecordNames =
  "YMSelfAdjointFiniteHamiltonianBoundary"
  ∷ "YMSelfAdjointFiniteHamiltonianStage"
  ∷ "YMSelfAdjointFiniteHamiltonianStageRow"
  ∷ "FiniteYMHamiltonianCarrierBoundary"
  ∷ "FiniteYMSymmetricFormObligations"
  ∷ "canonicalYMSelfAdjointFiniteHamiltonianBoundary"
  ∷ []

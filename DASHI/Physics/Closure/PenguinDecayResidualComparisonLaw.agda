module DASHI.Physics.Closure.PenguinDecayResidualComparisonLaw where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ResidualComparisonLaw as Residual
import DASHI.Physics.Closure.PenguinDecayProjectionDefectReceipt as Projection
import DASHI.Physics.Closure.PenguinDecayObservableContract as Contract
import DASHI.Physics.Closure.PenguinDecayProjectionArtifact as Artifact

------------------------------------------------------------------------
-- Penguin empirical-contact residual comparison law.
--
-- This is a concrete diagnostic request surface.  It consumes the finite
-- penguin projection-defect receipt when present, names the comparison modes
-- a provider must bind, and fails closed until an accepted authority route,
-- complete dataset binding, covariance calibration, and theory-uncertainty
-- budget are supplied.  The accepted law is intentionally empty here.

open Residual public
  using
    ( UniversalResidualComparisonOutcome
    ; acceptedResidualCandidate
    ; borderlineCandidate
    ; rejectedResidualCandidate
    ; insufficientAuthority
    ; theoryUncertaintyDominates
    ; freezeMissing
    ; dataMissing
    )

PenguinResidualComparisonDiagnosticOutcome : Set
PenguinResidualComparisonDiagnosticOutcome =
  UniversalResidualComparisonOutcome

canonicalPenguinResidualComparisonDiagnosticOutcomes :
  List PenguinResidualComparisonDiagnosticOutcome
canonicalPenguinResidualComparisonDiagnosticOutcomes =
  acceptedResidualCandidate
  ∷ borderlineCandidate
  ∷ rejectedResidualCandidate
  ∷ insufficientAuthority
  ∷ theoryUncertaintyDominates
  ∷ freezeMissing
  ∷ dataMissing
  ∷ []

data PenguinResidualComparisonMode : Set where
  normalizedPull :
    PenguinResidualComparisonMode
  covarianceWhitenedResidual :
    PenguinResidualComparisonMode
  angularAnomalyPattern :
    PenguinResidualComparisonMode
  theoryUncertaintyDominatesComparisonMode :
    PenguinResidualComparisonMode

canonicalPenguinResidualComparisonModes :
  List PenguinResidualComparisonMode
canonicalPenguinResidualComparisonModes =
  normalizedPull
  ∷ covarianceWhitenedResidual
  ∷ angularAnomalyPattern
  ∷ theoryUncertaintyDominatesComparisonMode
  ∷ []

data PenguinEmpiricalContact : Set where
  bToSLeptonPairAngularContact :
    PenguinEmpiricalContact
  bToSLeptonPairBranchingRatioContact :
    PenguinEmpiricalContact
  bToDPhotonBranchingRatioContact :
    PenguinEmpiricalContact
  cToULeptonPairNullSearchContact :
    PenguinEmpiricalContact

canonicalPenguinEmpiricalContacts :
  List PenguinEmpiricalContact
canonicalPenguinEmpiricalContacts =
  bToSLeptonPairAngularContact
  ∷ bToSLeptonPairBranchingRatioContact
  ∷ bToDPhotonBranchingRatioContact
  ∷ cToULeptonPairNullSearchContact
  ∷ []

contactDecay :
  PenguinEmpiricalContact →
  Projection.RarePenguinDecay
contactDecay bToSLeptonPairAngularContact =
  Projection.bToSLeptonPair
contactDecay bToSLeptonPairBranchingRatioContact =
  Projection.bToSLeptonPair
contactDecay bToDPhotonBranchingRatioContact =
  Projection.bToDPhoton
contactDecay cToULeptonPairNullSearchContact =
  Projection.cToULeptonPair

contactObservable :
  PenguinEmpiricalContact →
  Projection.IndirectObservable
contactObservable bToSLeptonPairAngularContact =
  Projection.angularCoefficientDeviation
contactObservable bToSLeptonPairBranchingRatioContact =
  Projection.branchingRatioDeviation
contactObservable bToDPhotonBranchingRatioContact =
  Projection.branchingRatioDeviation
contactObservable cToULeptonPairNullSearchContact =
  Projection.branchingRatioDeviation

record PenguinResidualComparisonCandidate : Set where
  constructor mkPenguinResidualComparisonCandidate
  field
    contact :
      PenguinEmpiricalContact

    mode :
      PenguinResidualComparisonMode

    decay :
      Projection.RarePenguinDecay

    observable :
      Projection.IndirectObservable

    indirectWitness :
      Projection.IndirectWitness

    decayMatchesContact :
      decay ≡ contactDecay contact

    observableMatchesContact :
      observable ≡ contactObservable contact

    witnessIsIndirect :
      Projection.extractionMode indirectWitness
      ≡
      Projection.indirectProjectionDefectExtraction

    witnessDefectIsResidual :
      Projection.extractedDefect indirectWitness
      ≡
      Projection.residualDefectSurface

open PenguinResidualComparisonCandidate public

candidateFor :
  PenguinEmpiricalContact →
  PenguinResidualComparisonMode →
  PenguinResidualComparisonCandidate
candidateFor contact mode =
  mkPenguinResidualComparisonCandidate
    contact
    mode
    (contactDecay contact)
    (contactObservable contact)
    (Projection.extractIndirectWitness
      (contactDecay contact)
      (contactObservable contact))
    refl
    refl
    refl
    refl

data PenguinResidualComparisonRequiredBinding : Set where
  requiresExactDatasetAuthority :
    PenguinResidualComparisonRequiredBinding
  requiresChecksumBoundObservableSelection :
    PenguinResidualComparisonRequiredBinding
  requiresNormalizedPullDefinition :
    PenguinResidualComparisonRequiredBinding
  requiresFullCovarianceWhitening :
    PenguinResidualComparisonRequiredBinding
  requiresAngularAnomalyPatternDefinition :
    PenguinResidualComparisonRequiredBinding
  requiresTheoryUncertaintyBudget :
    PenguinResidualComparisonRequiredBinding
  requiresProjectionDefectReceiptBinding :
    PenguinResidualComparisonRequiredBinding
  requiresAcceptedAuthorityRoute :
    PenguinResidualComparisonRequiredBinding

canonicalPenguinResidualComparisonRequiredBindings :
  List PenguinResidualComparisonRequiredBinding
canonicalPenguinResidualComparisonRequiredBindings =
  requiresExactDatasetAuthority
  ∷ requiresChecksumBoundObservableSelection
  ∷ requiresNormalizedPullDefinition
  ∷ requiresFullCovarianceWhitening
  ∷ requiresAngularAnomalyPatternDefinition
  ∷ requiresTheoryUncertaintyBudget
  ∷ requiresProjectionDefectReceiptBinding
  ∷ requiresAcceptedAuthorityRoute
  ∷ []

modeOutcomeWithoutAuthority :
  PenguinResidualComparisonMode →
  PenguinResidualComparisonDiagnosticOutcome
modeOutcomeWithoutAuthority normalizedPull =
  insufficientAuthority
modeOutcomeWithoutAuthority covarianceWhitenedResidual =
  insufficientAuthority
modeOutcomeWithoutAuthority angularAnomalyPattern =
  insufficientAuthority
modeOutcomeWithoutAuthority theoryUncertaintyDominatesComparisonMode =
  theoryUncertaintyDominates

twelve : Nat
twelve =
  suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))

data PenguinResidualSigmaSign : Set where
  negativeSigma :
    PenguinResidualSigmaSign
  positiveSigma :
    PenguinResidualSigmaSign

record PenguinExpectedResidualComparison : Set where
  constructor mkPenguinExpectedResidualComparison
  field
    candidate :
      PenguinResidualComparisonCandidate

    sigmaSign :
      PenguinResidualSigmaSign

    sigmaMagnitudeTenths :
      Nat

    sigmaMagnitudeIsOnePointTwo :
      sigmaMagnitudeTenths ≡ twelve

    sigmaBand :
      Residual.SigmaBand

    sigmaBandIsAtMostTwo :
      sigmaBand ≡ Residual.sigmaAtMostTwo

    sigmaBandMatchesMagnitude :
      Residual.classifyTenthSigmaBand sigmaMagnitudeTenths
      ≡
      sigmaBand

    authorityGatedOutcome :
      PenguinResidualComparisonDiagnosticOutcome

    authorityGatedOutcomeIsInsufficientAuthority :
      authorityGatedOutcome ≡ insufficientAuthority

    authorityGatedOutcomeMatchesMissingAuthority :
      Residual.classifyResidualCandidate
        Residual.authorityMissing
        Residual.freezeAbsent
        Residual.dataAbsent
        Residual.theoryUncertaintyDominant
        sigmaBand
      ≡
      authorityGatedOutcome

open PenguinExpectedResidualComparison public

expectedMinusOnePointTwoSigmaPenguinResidualComparison :
  PenguinExpectedResidualComparison
expectedMinusOnePointTwoSigmaPenguinResidualComparison =
  mkPenguinExpectedResidualComparison
    (candidateFor bToSLeptonPairAngularContact normalizedPull)
    negativeSigma
    twelve
    refl
    Residual.sigmaAtMostTwo
    refl
    refl
    insufficientAuthority
    refl
    refl

record PenguinResidualAcceptedCandidatePrerequisites : Set where
  constructor mkPenguinResidualAcceptedCandidatePrerequisites
  field
    datasetChecksumAuthority :
      Artifact.SuppliedPenguinDatasetChecksumAuthority

    datasetChecksumAuthorityUsesSHA256 :
      Artifact.digestAlgorithm datasetChecksumAuthority
      ≡
      "sha256"

    datasetChecksumAuthorityIsForSelectedThread :
      Artifact.sourceCandidate datasetChecksumAuthority
      ≡
      Contract.lhcbPRD105012010CDS2779103

    selectedThreadChecksumAuthorityPresent :
      Bool

    selectedThreadChecksumAuthorityPresentIsTrue :
      selectedThreadChecksumAuthorityPresent ≡ true

    acceptedAuthorityState :
      Residual.ResidualAuthorityState

    acceptedAuthorityStateIsPresent :
      acceptedAuthorityState ≡ Residual.authorityPresent

    freezeState :
      Residual.ResidualFreezeState

    freezeStateIsPresent :
      freezeState ≡ Residual.freezePresent

    freezeTuple :
      Artifact.PenguinFreezeHashPreRegistrationTuple

    freezeTupleFieldsAreCanonical :
      Artifact.tupleFields freezeTuple
      ≡
      Artifact.canonicalPenguinPreRegistrationTupleFields

    noPosteriorTuningBlockers :
      List Artifact.PenguinNoPosteriorTuningBlocker

    noPosteriorTuningBlockersAreCanonical :
      noPosteriorTuningBlockers
      ≡
      Artifact.canonicalPenguinNoPosteriorTuningBlockers

    dataState :
      Residual.ResidualDataState

    dataStateIsPresent :
      dataState ≡ Residual.dataPresent

    theoryUncertaintyState :
      Residual.ResidualTheoryUncertaintyState

    theoryUncertaintyStateIsControlled :
      theoryUncertaintyState ≡ Residual.theoryUncertaintyControlled

open PenguinResidualAcceptedCandidatePrerequisites public

acceptedResidualCandidateForExpectedMinusOnePointTwoSigma :
  (prerequisites : PenguinResidualAcceptedCandidatePrerequisites) →
  Residual.classifyResidualCandidate
    (acceptedAuthorityState prerequisites)
    (freezeState prerequisites)
    (dataState prerequisites)
    (theoryUncertaintyState prerequisites)
    Residual.sigmaAtMostTwo
  ≡
  acceptedResidualCandidate
acceptedResidualCandidateForExpectedMinusOnePointTwoSigma prerequisites
  rewrite acceptedAuthorityStateIsPresent prerequisites
        | freezeStateIsPresent prerequisites
        | dataStateIsPresent prerequisites
        | theoryUncertaintyStateIsControlled prerequisites =
  refl

expectedMinusOnePointTwoSigmaOutcomeWithMissingAuthority :
  (freeze : Residual.ResidualFreezeState) →
  (dataState : Residual.ResidualDataState) →
  (theory : Residual.ResidualTheoryUncertaintyState) →
  Residual.classifyResidualCandidate
    Residual.authorityMissing
    freeze
    dataState
    theory
    Residual.sigmaAtMostTwo
  ≡
  insufficientAuthority
expectedMinusOnePointTwoSigmaOutcomeWithMissingAuthority freeze dataState theory =
  Residual.authorityMissingPrecedesDataMissing
    freeze
    dataState
    theory
    Residual.sigmaAtMostTwo

acceptedResidualCandidateBridgeForFrozenPenguinTuple :
  (prerequisites : PenguinResidualAcceptedCandidatePrerequisites) →
  Artifact.tupleFields (freezeTuple prerequisites)
  ≡
  Artifact.canonicalPenguinPreRegistrationTupleFields
acceptedResidualCandidateBridgeForFrozenPenguinTuple prerequisites =
  freezeTupleFieldsAreCanonical prerequisites

acceptedResidualCandidateBridgeNoPosteriorTuningBlockers :
  (prerequisites : PenguinResidualAcceptedCandidatePrerequisites) →
  noPosteriorTuningBlockers prerequisites
  ≡
  Artifact.canonicalPenguinNoPosteriorTuningBlockers
acceptedResidualCandidateBridgeNoPosteriorTuningBlockers prerequisites =
  noPosteriorTuningBlockersAreCanonical prerequisites

acceptedResidualCandidateBridgeUsesSuppliedChecksumCanonical :
  (prerequisites : PenguinResidualAcceptedCandidatePrerequisites) →
  Artifact.digestAlgorithm (datasetChecksumAuthority prerequisites)
  ≡
  "sha256"
acceptedResidualCandidateBridgeUsesSuppliedChecksumCanonical prerequisites =
  datasetChecksumAuthorityUsesSHA256 prerequisites

data AcceptedPenguinResidualComparisonLaw : Set where

acceptedPenguinResidualComparisonLawImpossibleHere :
  AcceptedPenguinResidualComparisonLaw →
  ⊥
acceptedPenguinResidualComparisonLawImpossibleHere ()

record PenguinDecayResidualComparisonLaw : Set where
  field
    projectionReceipt :
      Projection.PenguinDecayProjectionDefectReceipt

    currentOutcome :
      PenguinResidualComparisonDiagnosticOutcome

    currentOutcomeIsInsufficientAuthority :
      currentOutcome ≡ insufficientAuthority

    diagnosticOutcomes :
      List PenguinResidualComparisonDiagnosticOutcome

    diagnosticOutcomesAreCanonical :
      diagnosticOutcomes
      ≡
      canonicalPenguinResidualComparisonDiagnosticOutcomes

    comparisonModes :
      List PenguinResidualComparisonMode

    comparisonModesAreCanonical :
      comparisonModes
      ≡
      canonicalPenguinResidualComparisonModes

    empiricalContacts :
      List PenguinEmpiricalContact

    empiricalContactsAreCanonical :
      empiricalContacts
      ≡
      canonicalPenguinEmpiricalContacts

    candidate :
      PenguinEmpiricalContact →
      PenguinResidualComparisonMode →
      PenguinResidualComparisonCandidate

    candidateUsesProjectionDefectReceipt :
      (contact : PenguinEmpiricalContact) →
      (mode : PenguinResidualComparisonMode) →
      Projection.extractedDefect
        (indirectWitness (candidate contact mode))
      ≡
      Projection.residualDefectSurface

    outcomeWithoutAuthority :
      PenguinResidualComparisonMode →
      PenguinResidualComparisonDiagnosticOutcome

    outcomeWithoutAuthorityMatchesModeLaw :
      (mode : PenguinResidualComparisonMode) →
      outcomeWithoutAuthority mode ≡ modeOutcomeWithoutAuthority mode

    requiredBindings :
      List PenguinResidualComparisonRequiredBinding

    requiredBindingsAreCanonical :
      requiredBindings
      ≡
      canonicalPenguinResidualComparisonRequiredBindings

    datasetBindingComplete :
      Bool

    datasetBindingCompleteIsFalse :
      datasetBindingComplete ≡ false

    acceptedAuthorityAvailable :
      Bool

    acceptedAuthorityAvailableIsFalse :
      acceptedAuthorityAvailable ≡ false

    acceptedLawConstructedHere :
      Bool

    acceptedLawConstructedHereIsFalse :
      acceptedLawConstructedHere ≡ false

    acceptedLawImpossibleHere :
      AcceptedPenguinResidualComparisonLaw →
      ⊥

    expectedResidualComparison :
      PenguinExpectedResidualComparison

    expectedResidualComparisonIsMinusOnePointTwoSigma :
      expectedResidualComparison
      ≡
      expectedMinusOnePointTwoSigmaPenguinResidualComparison

    acceptedResidualCandidateWhenAuthorityFreezeDataAndTheoryPresent :
      (prerequisites : PenguinResidualAcceptedCandidatePrerequisites) →
      Residual.classifyResidualCandidate
        (acceptedAuthorityState prerequisites)
        (freezeState prerequisites)
        (dataState prerequisites)
        (theoryUncertaintyState prerequisites)
        Residual.sigmaAtMostTwo
      ≡
      acceptedResidualCandidate

    acceptedResidualCandidateBridgeUsesFrozenTuple :
      (prerequisites : PenguinResidualAcceptedCandidatePrerequisites) →
      Artifact.tupleFields (freezeTuple prerequisites)
      ≡
      Artifact.canonicalPenguinPreRegistrationTupleFields

    acceptedResidualCandidateBridgeUsesNoPosteriorTuningBlockers :
      (prerequisites : PenguinResidualAcceptedCandidatePrerequisites) →
      noPosteriorTuningBlockers prerequisites
      ≡
      Artifact.canonicalPenguinNoPosteriorTuningBlockers

    acceptedResidualCandidateBridgeUsesSuppliedChecksum :
      (prerequisites : PenguinResidualAcceptedCandidatePrerequisites) →
      Artifact.digestAlgorithm (datasetChecksumAuthority prerequisites)
      ≡
      "sha256"

    expectedMinusOnePointTwoSigmaStillInsufficientWithoutAuthority :
      (freeze : Residual.ResidualFreezeState) →
      (dataState : Residual.ResidualDataState) →
      (theory : Residual.ResidualTheoryUncertaintyState) →
      Residual.classifyResidualCandidate
        Residual.authorityMissing
        freeze
        dataState
        theory
        Residual.sigmaAtMostTwo
      ≡
      insufficientAuthority

    requestBoundary :
      List String

open PenguinDecayResidualComparisonLaw public

canonicalPenguinDecayResidualComparisonLaw :
  PenguinDecayResidualComparisonLaw
canonicalPenguinDecayResidualComparisonLaw =
  record
    { projectionReceipt =
        Projection.canonicalPenguinDecayProjectionDefectReceipt
    ; currentOutcome =
        insufficientAuthority
    ; currentOutcomeIsInsufficientAuthority =
        refl
    ; diagnosticOutcomes =
        canonicalPenguinResidualComparisonDiagnosticOutcomes
    ; diagnosticOutcomesAreCanonical =
        refl
    ; comparisonModes =
        canonicalPenguinResidualComparisonModes
    ; comparisonModesAreCanonical =
        refl
    ; empiricalContacts =
        canonicalPenguinEmpiricalContacts
    ; empiricalContactsAreCanonical =
        refl
    ; candidate =
        candidateFor
    ; candidateUsesProjectionDefectReceipt =
        λ _ _ → refl
    ; outcomeWithoutAuthority =
        modeOutcomeWithoutAuthority
    ; outcomeWithoutAuthorityMatchesModeLaw =
        λ _ → refl
    ; requiredBindings =
        canonicalPenguinResidualComparisonRequiredBindings
    ; requiredBindingsAreCanonical =
        refl
    ; datasetBindingComplete =
        false
    ; datasetBindingCompleteIsFalse =
        refl
    ; acceptedAuthorityAvailable =
        false
    ; acceptedAuthorityAvailableIsFalse =
        refl
    ; acceptedLawConstructedHere =
        false
    ; acceptedLawConstructedHereIsFalse =
        refl
    ; acceptedLawImpossibleHere =
        acceptedPenguinResidualComparisonLawImpossibleHere
    ; expectedResidualComparison =
        expectedMinusOnePointTwoSigmaPenguinResidualComparison
    ; expectedResidualComparisonIsMinusOnePointTwoSigma =
        refl
    ; acceptedResidualCandidateWhenAuthorityFreezeDataAndTheoryPresent =
        acceptedResidualCandidateForExpectedMinusOnePointTwoSigma
    ; acceptedResidualCandidateBridgeUsesFrozenTuple =
        acceptedResidualCandidateBridgeForFrozenPenguinTuple
    ; acceptedResidualCandidateBridgeUsesNoPosteriorTuningBlockers =
        acceptedResidualCandidateBridgeNoPosteriorTuningBlockers
    ; acceptedResidualCandidateBridgeUsesSuppliedChecksum =
        acceptedResidualCandidateBridgeUsesSuppliedChecksumCanonical
    ; expectedMinusOnePointTwoSigmaStillInsufficientWithoutAuthority =
        expectedMinusOnePointTwoSigmaOutcomeWithMissingAuthority
    ; requestBoundary =
        "Diagnostic request for penguin empirical-contact residual comparison"
        ∷ "Consumes the finite projection-defect receipt for rare penguin decays"
        ∷ "Comparison modes are normalized pull, covariance-whitened residual, angular anomaly pattern, and theory-uncertainty-dominates"
        ∷ "Fail-closed outcomes use ResidualComparisonLaw: acceptedResidualCandidate, borderlineCandidate, rejectedResidualCandidate, insufficientAuthority, theoryUncertaintyDominates, freezeMissing, and dataMissing"
        ∷ "Expected -1.2 sigma b -> s lepton-pair angular residual is wired as an acceptedResidualCandidate theorem only when a selected-thread sha256 dataset checksum authority, accepted authority, freeze, data, and controlled-theory prerequisites are present"
        ∷ "No canonical acceptedResidualCandidate prerequisite is fabricated here; the live diagnostic remains insufficientAuthority until all selected-thread checksum, authority, freeze, data, and controlled-theory prerequisites are supplied"
        ∷ "Canonical current outcome is insufficientAuthority"
        ∷ "Dataset binding and accepted authority route are absent here"
        ∷ "No accepted residual comparison law or empirical promotion is constructed here"
        ∷ []
    }

canonicalPenguinResidualComparisonCurrentOutcome :
  currentOutcome canonicalPenguinDecayResidualComparisonLaw
  ≡
  insufficientAuthority
canonicalPenguinResidualComparisonCurrentOutcome =
  refl

canonicalPenguinResidualComparisonAcceptedLawImpossible :
  AcceptedPenguinResidualComparisonLaw →
  ⊥
canonicalPenguinResidualComparisonAcceptedLawImpossible =
  acceptedLawImpossibleHere canonicalPenguinDecayResidualComparisonLaw

canonicalPenguinExpectedMinusOnePointTwoSigmaAcceptedWhenPrerequisitesPresent :
  (prerequisites : PenguinResidualAcceptedCandidatePrerequisites) →
  Residual.classifyResidualCandidate
    (acceptedAuthorityState prerequisites)
    (freezeState prerequisites)
    (dataState prerequisites)
    (theoryUncertaintyState prerequisites)
    Residual.sigmaAtMostTwo
  ≡
  acceptedResidualCandidate
canonicalPenguinExpectedMinusOnePointTwoSigmaAcceptedWhenPrerequisitesPresent =
  acceptedResidualCandidateWhenAuthorityFreezeDataAndTheoryPresent
    canonicalPenguinDecayResidualComparisonLaw

canonicalPenguinExpectedMinusOnePointTwoSigmaStillInsufficientWithoutAuthority :
  (freeze : Residual.ResidualFreezeState) →
  (dataState : Residual.ResidualDataState) →
  (theory : Residual.ResidualTheoryUncertaintyState) →
  Residual.classifyResidualCandidate
    Residual.authorityMissing
    freeze
    dataState
    theory
    Residual.sigmaAtMostTwo
  ≡
  insufficientAuthority
canonicalPenguinExpectedMinusOnePointTwoSigmaStillInsufficientWithoutAuthority =
  expectedMinusOnePointTwoSigmaStillInsufficientWithoutAuthority
    canonicalPenguinDecayResidualComparisonLaw

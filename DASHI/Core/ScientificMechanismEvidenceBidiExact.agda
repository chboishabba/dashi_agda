module DASHI.Core.ScientificMechanismEvidenceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SCIENTIFIC MECHANISM / EVIDENCE BIDI
--
-- A source can expose a mechanism without establishing that mechanism as a
-- generally accepted physical law.  Numerical method, experimental observation,
-- source interpretation and established background law are separate fibres.
------------------------------------------------------------------------

data ScientificEvidenceKind : Set where
  establishedBackgroundLaw : ScientificEvidenceKind
  constitutiveOrEngineeringMechanism : ScientificEvidenceKind
  sourceProposedMechanism : ScientificEvidenceKind
  mathematicalReformulation : ScientificEvidenceKind
  numericalMethod : ScientificEvidenceKind
  benchmarkOrValidationTest : ScientificEvidenceKind
  experimentalObservation : ScientificEvidenceKind
  sourceInterpretation : ScientificEvidenceKind
  preliminaryConsistencyClaim : ScientificEvidenceKind
  unresolvedMechanism : ScientificEvidenceKind


data ScientificStatus : Set where
  established : ScientificStatus
  sourceBacked : ScientificStatus
  preliminary : ScientificStatus
  unresolved : ScientificStatus
  contradicted : ScientificStatus


record ScientificMechanismReceipt : Set where
  constructor scientific-mechanism-receipt
  field
    subject : String
    proposition : String
    evidenceKind : ScientificEvidenceKind
    status : ScientificStatus
    sourceReference : String
    boundedReading : String

open ScientificMechanismReceipt public

record MechanismBoundary : Set where
  constructor mechanism-boundary
  field
    sourceProposedMechanismMeansEstablishedLaw : Bool
    sourceProposedMechanismMeansEstablishedLawIsFalse :
      sourceProposedMechanismMeansEstablishedLaw ≡ false
    preliminaryConsistencyMeansIndependentReplication : Bool
    preliminaryConsistencyMeansIndependentReplicationIsFalse :
      preliminaryConsistencyMeansIndependentReplication ≡ false
    benchmarkMeansRealWorldValidation : Bool
    benchmarkMeansRealWorldValidationIsFalse :
      benchmarkMeansRealWorldValidation ≡ false
    numericalMethodMeansPhysicalTruth : Bool
    numericalMethodMeansPhysicalTruthIsFalse :
      numericalMethodMeansPhysicalTruth ≡ false
    publicDescriptionMeansCompleteImplementationReleased : Bool
    publicDescriptionMeansCompleteImplementationReleasedIsFalse :
      publicDescriptionMeansCompleteImplementationReleased ≡ false
    sourceInterpretationMeansWorldTruth : Bool
    sourceInterpretationMeansWorldTruthIsFalse :
      sourceInterpretationMeansWorldTruth ≡ false

canonicalMechanismBoundary : MechanismBoundary
canonicalMechanismBoundary = mechanism-boundary
  false refl
  false refl
  false refl
  false refl
  false refl
  false refl

data ScientificReverseTarget : Set where
  governingEquationReceipt : ScientificReverseTarget
  constitutiveParameterReceipt : ScientificReverseTarget
  numericalSchemeReceipt : ScientificReverseTarget
  benchmarkReceipt : ScientificReverseTarget
  experimentalProtocolReceipt : ScientificReverseTarget
  independentReplicationReceipt : ScientificReverseTarget
  uncertaintyReceipt : ScientificReverseTarget
  mechanismToObservationWeld : ScientificReverseTarget


record ScientificReverseObligation : Set where
  constructor scientific-reverse-obligation
  field
    subject : String
    target : ScientificReverseTarget
    requestedEvidence : String
    whatItCanPromote : String
    whatItCannotPromote : String

open ScientificReverseObligation public

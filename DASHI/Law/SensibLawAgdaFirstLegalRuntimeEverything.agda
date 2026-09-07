module DASHI.Law.SensibLawAgdaFirstLegalRuntimeEverything where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawProductionLegalRuntimeABIExact as Runtime
import DASHI.Law.SensibLawLegalResidualProducerSchedulerExact as Scheduler
import DASHI.Law.SensibLawRuntimeWrongTypeElementFrontierExact as Frontier
import DASHI.Law.SensibLawWrongTypeCausationElementExact as Element
import DASHI.Law.SensibLawTemporalHealthEvidenceWrongTypeExact as TemporalHealth
import DASHI.Law.SensibLawBackupNegativeEvidenceBoundaryExact as BackupEvidence
import DASHI.Law.SensibLawRecordingManifestLineageExact as RecordingLineage
import DASHI.Law.QueenslandWrongTypeCausationDeclarationExact as Queensland

------------------------------------------------------------------------
-- AGDA-FIRST LEGAL RUNTIME CAPSTONE
--
-- Preferred implementation order:
--
-- direct/candidate PNF
--   -> explicit legal residual
--   -> typed source plan / bounded legal follow when required
--   -> legal IR observation
--   -> typed legal meet
--   -> authority/applicability review
--   -> exact WrongType element declaration
--   -> typed evidence/payment
--   -> consumer-indexed closure
--
-- The Rust SLR implementation may consume this ABI only after the formal
-- semantic carrier exists.  The historical SensibLaw implementation remains a
-- reference source for carrier/operational behaviour and does not own new
-- semantics in this tranche.
------------------------------------------------------------------------

data LegalRuntimeCoordinate : Set where
  runtimePNFCoordinate : LegalRuntimeCoordinate
  legalResidualCoordinate : LegalRuntimeCoordinate
  legalSourcePlanCoordinate : LegalRuntimeCoordinate
  legalIRCoordinate : LegalRuntimeCoordinate
  typedMeetCoordinate : LegalRuntimeCoordinate
  authorityCoordinate : LegalRuntimeCoordinate
  applicabilityCoordinate : LegalRuntimeCoordinate
  wrongTypeElementCoordinate : LegalRuntimeCoordinate
  evidencePaymentCoordinate : LegalRuntimeCoordinate
  consumerClosureCoordinate : LegalRuntimeCoordinate


data CoordinateRequirement : Set where
  requiredCoordinate : CoordinateRequirement
  conditionallyRequiredCoordinate : CoordinateRequirement
  downstreamCoordinate : CoordinateRequirement


coordinateRequirement : LegalRuntimeCoordinate → CoordinateRequirement
coordinateRequirement runtimePNFCoordinate = requiredCoordinate
coordinateRequirement legalResidualCoordinate = requiredCoordinate
coordinateRequirement legalSourcePlanCoordinate = conditionallyRequiredCoordinate
coordinateRequirement legalIRCoordinate = conditionallyRequiredCoordinate
coordinateRequirement typedMeetCoordinate = requiredCoordinate
coordinateRequirement authorityCoordinate = requiredCoordinate
coordinateRequirement applicabilityCoordinate = requiredCoordinate
coordinateRequirement wrongTypeElementCoordinate = downstreamCoordinate
coordinateRequirement evidencePaymentCoordinate = downstreamCoordinate
coordinateRequirement consumerClosureCoordinate = downstreamCoordinate

------------------------------------------------------------------------
-- Queensland causation golden vertical.
------------------------------------------------------------------------

ordinaryQueenslandDeclarationKind :
  (weld : Queensland.QueenslandWrongTypeSourceWeld) →
  (elementId : String) →
  Element.kind (Queensland.ordinaryFactualCausationDeclaration weld elementId)
  ≡ Element.ordinaryFactualCausationElement
ordinaryQueenslandDeclarationKind weld elementId = refl

ordinaryQueenslandProducer :
  (weld : Queensland.QueenslandWrongTypeSourceWeld) →
  (elementId : String) →
  Element.producerFor
    (Element.kind (Queensland.ordinaryFactualCausationDeclaration weld elementId))
  ≡ Element.ordinaryButForProducer
ordinaryQueenslandProducer weld elementId = refl

scopeQueenslandDeclarationKind :
  (weld : Queensland.QueenslandWrongTypeSourceWeld) →
  (elementId : String) →
  Element.kind (Queensland.scopeOfLiabilityDeclaration weld elementId)
  ≡ Element.scopeOfLiabilityElement
scopeQueenslandDeclarationKind weld elementId = refl

scopeQueenslandProducer :
  (weld : Queensland.QueenslandWrongTypeSourceWeld) →
  (elementId : String) →
  Element.producerFor
    (Element.kind (Queensland.scopeOfLiabilityDeclaration weld elementId))
  ≡ Element.scopeResponsibilityProducer
scopeQueenslandProducer weld elementId = refl

exceptionalQueenslandDeclarationKind :
  (weld : Queensland.QueenslandWrongTypeSourceWeld) →
  (route : Queensland.ExceptionalRouteAvailability) →
  (elementId : String) →
  Element.kind
    (Queensland.exceptionalFactualCausationDeclaration weld route elementId)
  ≡ Element.exceptionalFactualCausationElement
exceptionalQueenslandDeclarationKind weld route elementId = refl

exceptionalQueenslandProducer :
  (weld : Queensland.QueenslandWrongTypeSourceWeld) →
  (route : Queensland.ExceptionalRouteAvailability) →
  (elementId : String) →
  Element.producerFor
    (Element.kind
      (Queensland.exceptionalFactualCausationDeclaration weld route elementId))
  ≡ Element.exceptionalEstablishedPrinciplesProducer
exceptionalQueenslandProducer weld route elementId = refl

------------------------------------------------------------------------
-- Formal implementation boundary.
------------------------------------------------------------------------

record AgdaFirstLegalRuntimeContract : Set where
  constructor agdaFirstLegalRuntimeContract
  field
    productionRuntimeIsSLR : Bool
    productionRuntimeIsSLRIsTrue : productionRuntimeIsSLR ≡ true

    historicalSensibLawIsReferenceOnly : Bool
    historicalSensibLawIsReferenceOnlyIsTrue :
      historicalSensibLawIsReferenceOnly ≡ true

    runtimeMayInventMissingFormalLegalSemantics : Bool
    runtimeMayInventMissingFormalLegalSemanticsIsFalse :
      runtimeMayInventMissingFormalLegalSemantics ≡ false

    parserCandidateMayBecomeTruthByTransport : Bool
    parserCandidateMayBecomeTruthByTransportIsFalse :
      parserCandidateMayBecomeTruthByTransport ≡ false

    sourceFollowMayBecomeAuthorityByTransport : Bool
    sourceFollowMayBecomeAuthorityByTransportIsFalse :
      sourceFollowMayBecomeAuthorityByTransport ≡ false

    typedMeetMayBecomeViolationByTransport : Bool
    typedMeetMayBecomeViolationByTransportIsFalse :
      typedMeetMayBecomeViolationByTransport ≡ false

    wrongTypeElementPaymentMayBecomeLiabilityByTransport : Bool
    wrongTypeElementPaymentMayBecomeLiabilityByTransportIsFalse :
      wrongTypeElementPaymentMayBecomeLiabilityByTransport ≡ false

canonicalAgdaFirstLegalRuntimeContract : AgdaFirstLegalRuntimeContract
canonicalAgdaFirstLegalRuntimeContract =
  agdaFirstLegalRuntimeContract
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Cross-owner pinning.
------------------------------------------------------------------------

selectedRuntimeBoundary : Runtime.AgdaFirstRuntimeBoundary
selectedRuntimeBoundary = Runtime.canonicalAgdaFirstRuntimeBoundary

selectedResidualSchedulerBoundary : Scheduler.LegalResidualSchedulerBoundary
selectedResidualSchedulerBoundary =
  Scheduler.canonicalLegalResidualSchedulerBoundary

selectedElementBoundary : Frontier.RuntimeWrongTypeElementBoundary
selectedElementBoundary = Frontier.canonicalRuntimeWrongTypeElementBoundary

selectedTemporalHealthEvidenceBoundary :
  TemporalHealth.TemporalHealthEvidenceBoundary
selectedTemporalHealthEvidenceBoundary =
  TemporalHealth.canonicalTemporalHealthEvidenceBoundary

selectedBackupNegativeEvidenceBoundary :
  BackupEvidence.BackupNegativeEvidenceBoundary
selectedBackupNegativeEvidenceBoundary =
  BackupEvidence.canonicalBackupNegativeEvidenceBoundary

selectedRecordingManifestLineageBoundary :
  RecordingLineage.RecordingManifestLineageBoundary
selectedRecordingManifestLineageBoundary =
  RecordingLineage.canonicalRecordingManifestLineageBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RustRuntimeMayDefineUnownedLegalDoctrine : Set where
data ReferenceImplementationMayOverrideAgdaContract : Set where
data QueenslandSection11FactualPaymentEqualsScopePayment : Set where
data ConsumerSourceClosureEqualsFinalLiability : Set where

rustRuntimeDoesNotDefineUnownedDoctrine :
  RustRuntimeMayDefineUnownedLegalDoctrine → ⊥
rustRuntimeDoesNotDefineUnownedDoctrine ()

referenceImplementationDoesNotOverrideFormalContract :
  ReferenceImplementationMayOverrideAgdaContract → ⊥
referenceImplementationDoesNotOverrideFormalContract ()

queenslandFactualPaymentDoesNotEqualScopePayment :
  QueenslandSection11FactualPaymentEqualsScopePayment → ⊥
queenslandFactualPaymentDoesNotEqualScopePayment ()

sourceClosureDoesNotEqualFinalLiability :
  ConsumerSourceClosureEqualsFinalLiability → ⊥
sourceClosureDoesNotEqualFinalLiability ()

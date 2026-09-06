module DASHI.Cognition.PNF.SensibLawRemedyUniversalLegalAlgebraBridgeExact where

------------------------------------------------------------------------
-- UNIVERSAL LEGAL ALGEBRA -> REMEDY OPERATIONAL REALISATION
--
-- #733 determines whether a legal authority/remedy proposition is derivable.
-- #734 asks whether an available remedy is actually authorised, executed,
-- observed, community-successful and feedback-correcting. These are sequential
-- but non-collapsed consumers.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as Elements
import DASHI.Cognition.PNF.SensibLawBillyRemedyOperationalRealisationBidiExact as Realisation
import DASHI.Cognition.PNF.SensibLawBillyEffectiveRemedyTwoEyedSeeingExact as Billy

------------------------------------------------------------------------
-- Remedy availability is a legal proposition; realised remedy is a separate
-- operational state. Neither direction is automatic.
------------------------------------------------------------------------

record RemedyLegalTarget : Set where
  constructor remedy-legal-target
  field
    wrongType : Ontology.WrongType
    remedyId : Ontology.StableId
    availabilityProposition : Algebra.LegalProposition
    propositionKindIsRemedyConstraint :
      Algebra.LegalProposition.propositionKind availabilityProposition
      ≡ Algebra.remedyConstraint

open RemedyLegalTarget public

record LegallyAvailableRemedy
  (graph : Algebra.LegalGraph)
  (facts : Algebra.FactSet)
  (target : RemedyLegalTarget)
  : Set where
  constructor legally-available-remedy
  field
    derivation : Algebra.Reachable graph facts (availabilityProposition target)

open LegallyAvailableRemedy public

record RealisedLegalRemedy
  (graph : Algebra.LegalGraph)
  (facts : Algebra.FactSet)
  (target : RemedyLegalTarget)
  : Set where
  constructor realised-legal-remedy
  field
    legalAvailability : LegallyAvailableRemedy graph facts target
    realisationContract : Realisation.RemedyRealisationContract
    lawfulAuthoritySatisfied : Set
    executionSatisfied : Set
    observedOutcomeSatisfied : Set
    communityDefinedSuccessSatisfied : Set
    feedbackCorrectionSatisfied : Set

open RealisedLegalRemedy public

------------------------------------------------------------------------
-- Reverse/BIDI routing: operational failure reopens the correct consumer and
-- does not erase an already valid legal derivation unless the legal authority
-- itself changed.
------------------------------------------------------------------------

data RemedyResidualKind : Set where
  legalAvailabilityResidual
  lawfulAuthorityResidual
  executionResidual
  observedOutcomeResidual
  communitySuccessResidual
  feedbackCorrectionResidual
  : RemedyResidualKind

record RemedyReopenRequest : Set where
  constructor remedy-reopen-request
  field
    residual : RemedyResidualKind
    reopenLegalRuleGraph : Bool
    reopenExecutionEvidence : Bool
    reopenCommunityOutcomeEvidence : Bool
    reason : String

open RemedyReopenRequest public

executionFailureReopen : RemedyReopenRequest
executionFailureReopen = remedy-reopen-request
  executionResidual false true false
  "legal availability may remain established while execution evidence is reopened"

communityOutcomeFailureReopen : RemedyReopenRequest
communityOutcomeFailureReopen = remedy-reopen-request
  communitySuccessResidual false false true
  "community-defined realised outcome can reopen without rewriting the legal-source derivation"

legalAuthorityFailureReopen : RemedyReopenRequest
legalAuthorityFailureReopen = remedy-reopen-request
  legalAvailabilityResidual true false false
  "changed/revised legal authority reopens the universal legal graph"

------------------------------------------------------------------------
-- Billy remedy coordinates compile to remedy-constraint proposition targets.
------------------------------------------------------------------------

billySystem : Ontology.StableId
billySystem = Ontology.stableId "legal-system:ICCPR-Australia-remedy-translation"

coordinateLabel : Billy.RemedyCoordinate → String
coordinateLabel Billy.adequateCompensation = "adequate compensation"
coordinateLabel Billy.meaningfulConsultation = "meaningful consultation"
coordinateLabel Billy.communityNeedsAssessment = "community needs assessment"
coordinateLabel Billy.continuedSafeExistenceMeasures = "continued safe existence measures"
coordinateLabel Billy.monitoringAndReview = "monitoring and review"
coordinateLabel Billy.correctionOfDeficiencies = "correction of deficiencies"
coordinateLabel Billy.prevention = "prevention"
coordinateLabel Billy.publicationAndDissemination = "publication and dissemination"

coordinateTarget : Ontology.WrongType → Billy.RemedyCoordinate → RemedyLegalTarget
coordinateTarget wrong coordinate = remedy-legal-target
  wrong
  (Ontology.stableId (coordinateLabel coordinate))
  (Algebra.legal-proposition
    (Ontology.stableId (coordinateLabel coordinate))
    Algebra.remedyConstraint
    (Ontology.WrongType.wrongTypeId wrong)
    (Ontology.stableId (coordinateLabel coordinate))
    billySystem
    (coordinateLabel coordinate))
  refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data LegalAvailabilityAutomaticallyMeansRealisedRemedy : Set where
data RealisedOutcomeAutomaticallyCreatesLegalAuthority : Set where
data ExecutionFailureRefutesUnderlyingLegalRule : Set where

availabilityDoesNotEqualRealisation :
  LegalAvailabilityAutomaticallyMeansRealisedRemedy → ⊥
availabilityDoesNotEqualRealisation ()

outcomeDoesNotManufactureAuthority :
  RealisedOutcomeAutomaticallyCreatesLegalAuthority → ⊥
outcomeDoesNotManufactureAuthority ()

executionFailureDoesNotAutomaticallyRefuteLaw :
  ExecutionFailureRefutesUnderlyingLegalRule → ⊥
executionFailureDoesNotAutomaticallyRefuteLaw ()

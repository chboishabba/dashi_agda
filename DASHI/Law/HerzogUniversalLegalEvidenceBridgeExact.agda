module DASHI.Law.HerzogUniversalLegalEvidenceBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Law.SecurityClassificationInputLineageDagExact as Lineage
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawFiniteExecutableLegalSearchExact as Search
import DASHI.Cognition.PNF.SensibLawLegalObserverResidualRefinementBidiExact as Residual

------------------------------------------------------------------------
-- This module is a DASHI bridge, not a new historical source.
-- Source ownership remains in the Herzog/security-classification Law modules.
-- The bridge only states which source-backed or open lineage coordinates are
-- usable as factual inputs to the universal law graph.
------------------------------------------------------------------------

herzogSystem : Ontology.StableId
herzogSystem = Ontology.stableId "legal-system:AU:NSW:Herzog-classification-audit"

herzogEvent : Ontology.StableId
herzogEvent = Ontology.stableId "event:Herzog-protest-intervention"

postHocNarrativeObserved : Algebra.LegalProposition
postHocNarrativeObserved = Algebra.legal-proposition
  (Ontology.stableId "fact:Herzog:post-hoc-police-narrative-observed")
  Algebra.factualFeature herzogEvent herzogEvent herzogSystem
  "post-event police crowd characterisation is present in the current source surface"

preActionClassificationContentEstablished : Algebra.LegalProposition
preActionClassificationContentEstablished = Algebra.legal-proposition
  (Ontology.stableId "fact:Herzog:pre-action-classification-content-established")
  Algebra.factualFeature herzogEvent herzogEvent herzogSystem
  "pre-action security-classification content and carrier are established by source-level lineage evidence"

classificationProducedOperationalOrder : Algebra.LegalProposition
classificationProducedOperationalOrder = Algebra.legal-proposition
  (Ontology.stableId "fact:Herzog:classification-produced-operational-order")
  Algebra.relationalFeature herzogEvent herzogEvent herzogSystem
  "the same classification proposition is shown to have entered the operational order"

operationalOrderProducedFieldTactic : Algebra.LegalProposition
operationalOrderProducedFieldTactic = Algebra.legal-proposition
  (Ontology.stableId "fact:Herzog:operational-order-produced-field-tactic")
  Algebra.relationalFeature herzogEvent herzogEvent herzogSystem
  "the same operational proposition is shown to have reached and contributed to the field tactic"

legalQualificationOfClassification : Algebra.LegalProposition
legalQualificationOfClassification = Algebra.legal-proposition
  (Ontology.stableId "law:Herzog:security-classification-legally-qualified")
  Algebra.doctrinalPredicate herzogEvent herzogEvent herzogSystem
  "a controlling legal source supplies the asserted legal qualification of the security classification"

incidentCausalContribution : Algebra.LegalProposition
incidentCausalContribution = Algebra.legal-proposition
  (Ontology.stableId "fact:Herzog:classification-causal-contribution")
  Algebra.factualFeature herzogEvent herzogEvent herzogSystem
  "the classification or order is shown to have causally contributed to the specific incident conduct"

legalAttribution : Algebra.LegalProposition
legalAttribution = Algebra.legal-proposition
  (Ontology.stableId "law:Herzog:incident-legal-attribution")
  Algebra.doctrinalPredicate herzogEvent herzogEvent herzogSystem
  "a controlling legal rule attributes the incident conduct to the legally relevant actor or authority"

liabilityEstablished : Algebra.LegalProposition
liabilityEstablished = Algebra.legal-proposition
  (Ontology.stableId "law:Herzog:liability-established")
  Algebra.wrongElementPredicate herzogEvent herzogEvent herzogSystem
  "all required elements for the selected legal wrong and liability route are established"

------------------------------------------------------------------------
-- Current facts mirror #756's open lineage: the post-hoc narrative exists, but
-- it cannot backfill the missing pre-action classification lineage.
------------------------------------------------------------------------

currentHerzogFacts : Algebra.FactSet
currentHerzogFacts = Algebra.fact-set (postHocNarrativeObserved ∷ [])

currentHerzogGraph : Algebra.LegalGraph
currentHerzogGraph = Algebra.legal-graph [] []

currentPreActionClassificationStillUnreachable :
  Search.reachable 1 currentHerzogGraph currentHerzogFacts
    preActionClassificationContentEstablished ≡ false
currentPreActionClassificationStillUnreachable = refl

currentOperationalOrderStillUnreachable :
  Search.reachable 1 currentHerzogGraph currentHerzogFacts
    classificationProducedOperationalOrder ≡ false
currentOperationalOrderStillUnreachable = refl

currentFieldTacticLineageStillUnreachable :
  Search.reachable 1 currentHerzogGraph currentHerzogFacts
    operationalOrderProducedFieldTactic ≡ false
currentFieldTacticLineageStillUnreachable = refl

currentLegalQualificationStillUnreachable :
  Search.reachable 1 currentHerzogGraph currentHerzogFacts
    legalQualificationOfClassification ≡ false
currentLegalQualificationStillUnreachable = refl

------------------------------------------------------------------------
-- Herzog lineage residuals compile into the generic legal reopening vocabulary.
------------------------------------------------------------------------

lineageResidualKind : Lineage.LineageResidual → Residual.LegalResidualKind
lineageResidualKind Lineage.foreignInputResidual = Residual.missingProvenanceOrPermission
lineageResidualKind Lineage.privateSecurityInputResidual = Residual.missingProvenanceOrPermission
lineageResidualKind Lineage.classificationContentResidual = Residual.missingFactualFeature
lineageResidualKind Lineage.carrierContentResidual = Residual.missingProvenanceOrPermission
lineageResidualKind Lineage.orderLinkResidual = Residual.missingFactualFeature
lineageResidualKind Lineage.fieldTransmissionResidual = Residual.missingFactualFeature
lineageResidualKind Lineage.lineageClosed = Residual.missingFactualFeature

currentClassificationResidualRoutesToEvidence :
  Residual.preferredRoute
    (lineageResidualKind
      (Lineage.firstLineageResidual
        Lineage.zionistRepertoireReachedClassification
        Lineage.canonicalCurrentLineageCutset))
  ≡ Residual.obtainFactualEvidence
currentClassificationResidualRoutesToEvidence = refl

------------------------------------------------------------------------
-- Source/provenance/evidence and legal consequences remain separate layers.
------------------------------------------------------------------------

data PostHocNarrativeCreatesPreActionClassification : Set where
data RepeatedLanguageCreatesLegalQualification : Set where
data SameIncidentCreatesCausalContribution : Set where
data CausalContributionCreatesLegalAttribution : Set where
data LegalAttributionAutomaticallyCreatesLiability : Set where
data SecurityClassificationIsCourtHolding : Set where

postHocNarrativeDoesNotBackfillLineage :
  PostHocNarrativeCreatesPreActionClassification → ⊥
postHocNarrativeDoesNotBackfillLineage ()

repetitionDoesNotCreateLegalQualification :
  RepeatedLanguageCreatesLegalQualification → ⊥
repetitionDoesNotCreateLegalQualification ()

sameIncidentDoesNotCreateCausation :
  SameIncidentCreatesCausalContribution → ⊥
sameIncidentDoesNotCreateCausation ()

causationDoesNotCreateLegalAttribution :
  CausalContributionCreatesLegalAttribution → ⊥
causationDoesNotCreateLegalAttribution ()

attributionDoesNotAutomaticallyCreateLiability :
  LegalAttributionAutomaticallyCreatesLiability → ⊥
attributionDoesNotAutomaticallyCreateLiability ()

classificationDoesNotBecomeCourtHolding : SecurityClassificationIsCourtHolding → ⊥
classificationDoesNotBecomeCourtHolding ()

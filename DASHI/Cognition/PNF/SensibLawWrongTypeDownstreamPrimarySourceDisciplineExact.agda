module DASHI.Cognition.PNF.SensibLawWrongTypeDownstreamPrimarySourceDisciplineExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as Elements
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Cognition.PNF.SensibLawLegalJurisdictionEvidenceExact as Jurisdiction

------------------------------------------------------------------------
-- PRIMARY-SOURCE DISCIPLINE BELOW WRONGTYPE
--
-- WrongType classification is not the end of source attribution.  Every later
-- legal step may have its own primary source, locator, conditions, limits,
-- defeaters and forum/jurisdiction requirements.  This module refines the
-- existing applicability -> violation -> liability kernel without replacing it.
--
-- A citation remains non-promoting: AttributedSource records provenance and a
-- formalisation relationship but does not itself create legal authority.
------------------------------------------------------------------------

data LegalDecisionStage : Set where
  wrongTypeClassificationStage : LegalDecisionStage
  wrongElementDefinitionStage : LegalDecisionStage
  wrongElementEvaluationStage : LegalDecisionStage
  applicabilityStage : LegalDecisionStage
  violationStage : LegalDecisionStage
  liabilityClassificationStage : LegalDecisionStage
  liabilityConditionStage : LegalDecisionStage
  limitationOrDefeaterStage : LegalDecisionStage
  courtCompetenceStage : LegalDecisionStage
  remedyStage : LegalDecisionStage

record PrimarySourceAttachment (stage : LegalDecisionStage) : Set where
  constructor primary-source-attachment
  field
    source : Source.AttributedSource
    locator : String
    sourceProposition : Algebra.LegalProposition
    formalisationRelationship : String
    citationStillDoesNotCreateAuthority :
      Source.citationCreatesAuthority source ≡ false

open PrimarySourceAttachment public

------------------------------------------------------------------------
-- WrongType and element source attachments.
------------------------------------------------------------------------

record WrongTypePrimarySource
    (wrongType : Ontology.WrongType) : Set where
  constructor wrongtype-primary-source
  field
    attachment : PrimarySourceAttachment wrongTypeClassificationStage
    propositionSystemMatchesWrongType :
      Algebra.legalSystem (sourceProposition attachment)
      ≡ Ontology.WrongType.definingSystem wrongType
    wrongTypeReference : Ontology.StableId
    wrongTypeReferenceIsExact :
      wrongTypeReference ≡ Ontology.WrongType.wrongTypeId wrongType

open WrongTypePrimarySource public

record WrongElementPrimarySource
    {wrongType : Ontology.WrongType}
    (element : Elements.LegalElement wrongType) : Set where
  constructor wrongelement-primary-source
  field
    attachment : PrimarySourceAttachment wrongElementDefinitionStage
    propositionSystemMatchesWrongType :
      Algebra.legalSystem (sourceProposition attachment)
      ≡ Ontology.WrongType.definingSystem wrongType
    elementReference : String
    elementDefinitionReference : String

open WrongElementPrimarySource public

record SourceAttributedElementEvaluation
    {wrongType : Ontology.WrongType}
    (element : Elements.LegalElement wrongType) : Set where
  constructor source-attributed-element-evaluation
  field
    elementSource : WrongElementPrimarySource element
    evaluation : Legal.WrongElementEvaluation
    evaluationWrongTypeMatches :
      Legal.wrongTypeReference evaluation
      ≡ Ontology.WrongType.wrongTypeId wrongType
    evaluationPrimarySources :
      List (PrimarySourceAttachment wrongElementEvaluationStage)
    evaluationReference : String

open SourceAttributedElementEvaluation public

------------------------------------------------------------------------
-- Liability is itself typed.  These constructors are classification labels,
-- not claims that every jurisdiction recognises every family or that the list
-- is exhaustive.  Recognition for a concrete use must be source-paid below.
------------------------------------------------------------------------

data LiabilityFamily : Set where
  directWrongTypeLiability : LiabilityFamily
  vicariousLiability : LiabilityFamily
  statutoryLiability : LiabilityFamily
  contributionLiability : LiabilityFamily
  indemnityLiability : LiabilityFamily
  publicAuthorityLiability : LiabilityFamily
  namedLiabilityFamily : String → LiabilityFamily

record TypedLiabilityProfile
    (wrongType : Ontology.WrongType) : Set where
  constructor typed-liability-profile
  field
    family : LiabilityFamily
    familyPrimarySources :
      List (PrimarySourceAttachment liabilityClassificationStage)
    conditions : List Algebra.LegalProposition
    conditionPrimarySources :
      List (PrimarySourceAttachment liabilityConditionStage)
    limitationsAndDefeaters : List Algebra.LegalProposition
    limitationPrimarySources :
      List (PrimarySourceAttachment limitationOrDefeaterStage)
    competentJurisdictionKind : Status.JurisdictionKind
    profileSystem : Ontology.StableId
    profileSystemMatchesWrongType :
      profileSystem ≡ Ontology.WrongType.definingSystem wrongType
    profileReference : String

open TypedLiabilityProfile public

------------------------------------------------------------------------
-- Court/forum competence is a separate payment.  A source-supported liability
-- family does not decide which court may determine it; a jurisdiction receipt
-- must match the profile's declared competence coordinate.
------------------------------------------------------------------------

record CourtCompetenceReceipt
    {state : Status.SemanticCommitmentState}
    {wrongType : Ontology.WrongType}
    (profile : TypedLiabilityProfile wrongType) : Set where
  constructor court-competence-receipt
  field
    jurisdiction : Jurisdiction.LegalJurisdictionReceiptInState state
    jurisdictionKindMatchesProfile :
      Status.jurisdictionKind (Jurisdiction.legalStatus jurisdiction)
      ≡ competentJurisdictionKind profile
    competencePrimarySources :
      List (PrimarySourceAttachment courtCompetenceStage)
    competenceReference : String

open CourtCompetenceReceipt public

------------------------------------------------------------------------
-- Source-attributed liability decision.
--
-- This wraps, rather than replaces, the existing LiabilityReceipt.  It forces
-- the generic receipt onto one exact WrongType, one liability family/profile,
-- one forum competence receipt, and explicit source surfaces for conditions
-- and limitations.
------------------------------------------------------------------------

record SourceAttributedLiabilityDecision
    {state : Status.SemanticCommitmentState}
    {wrongType : Ontology.WrongType}
    (profile : TypedLiabilityProfile wrongType) : Set where
  constructor source-attributed-liability-decision
  field
    liabilityReceipt : Legal.LiabilityReceipt
    liabilityWrongTypeMatches :
      Legal.wrongType
        (Legal.applicabilityReceipt
          (Legal.violationReceipt liabilityReceipt))
      ≡ wrongType
    courtCompetence : CourtCompetenceReceipt {state} profile
    violationPrimarySources :
      List (PrimarySourceAttachment violationStage)
    liabilityDecisionPrimarySources :
      List (PrimarySourceAttachment liabilityClassificationStage)
    conditionsActuallyChecked : List Algebra.LegalProposition
    limitationsActuallyChecked : List Algebra.LegalProposition
    decisionReference : String

open SourceAttributedLiabilityDecision public

------------------------------------------------------------------------
-- Boundary laws.
------------------------------------------------------------------------

data CitationCreatesWrongType : Set where
data WrongTypeDeterminesElementDisposition : Set where
data ElementSatisfactionAutomaticallyCreatesViolation : Set where
data ViolationDeterminesLiabilityFamily : Set where
data LiabilityFamilyDeterminesCourt : Set where
data CourtCompetenceDeterminesMerits : Set where
data LiabilitySourceDeletesLimitations : Set where
data OnePrimarySourcePaysEveryDownstreamStage : Set where

aCitationDoesNotCreateWrongType : CitationCreatesWrongType → ⊥
aCitationDoesNotCreateWrongType ()

wrongTypeDoesNotDetermineElementDisposition : WrongTypeDeterminesElementDisposition → ⊥
wrongTypeDoesNotDetermineElementDisposition ()

elementSatisfactionDoesNotAutoCreateViolation :
  ElementSatisfactionAutomaticallyCreatesViolation → ⊥
elementSatisfactionDoesNotAutoCreateViolation ()

violationDoesNotDetermineLiabilityFamily : ViolationDeterminesLiabilityFamily → ⊥
violationDoesNotDetermineLiabilityFamily ()

liabilityFamilyDoesNotDetermineCourt : LiabilityFamilyDeterminesCourt → ⊥
liabilityFamilyDoesNotDetermineCourt ()

courtCompetenceDoesNotDetermineMerits : CourtCompetenceDeterminesMerits → ⊥
courtCompetenceDoesNotDetermineMerits ()

liabilitySourceDoesNotDeleteLimitations : LiabilitySourceDeletesLimitations → ⊥
liabilitySourceDoesNotDeleteLimitations ()

oneSourceDoesNotPayEveryStage : OnePrimarySourcePaysEveryDownstreamStage → ⊥
oneSourceDoesNotPayEveryStage ()

sourceDisciplineReading : String
sourceDisciplineReading =
  "Primary-source attribution persists through WrongType, element definition/evaluation, applicability, violation, typed liability family, conditions/limitations, court competence and remedy. A citation remains provenance rather than authority, and no downstream stage is silently paid by an upstream source receipt."

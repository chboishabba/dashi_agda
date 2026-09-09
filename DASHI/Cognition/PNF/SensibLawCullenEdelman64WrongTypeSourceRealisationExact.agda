module DASHI.Cognition.PNF.SensibLawCullenEdelman64WrongTypeSourceRealisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as Elements
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence
import DASHI.Cognition.PNF.SensibLawCullenSourceCorrectDutyRoutesExact as Routes
import DASHI.Cognition.PNF.SensibLawRecentDutyCaseSourceAtlasExact as PrimarySources
import DASHI.Cognition.PNF.SensibLawWrongTypeDownstreamPrimarySourceDisciplineExact as Downstream

------------------------------------------------------------------------
-- CULLEN / EDELMAN J [64] SOURCE REALISATION THROUGH WRONGTYPE
--
-- Exact source anchor:
--   Cullen v New South Wales [2026] HCA 19, Edelman J at [64].
--
-- The retained paragraph states, in substance:
--   * the OSG intervention was not said to be pursuant to statutory power;
--   * any liability would be based on positive acts creating risk, not omission;
--   * the applicable duty includes the ordinary common-law duty to avoid causing
--     reasonably foreseeable injury.
--
-- The direct source propositions below stay distinct from DASHI's later route
-- reconstruction `statutoryPowerNotRequiredOnEdelmanRoute`.
--
-- The exact High Court AttributedSource is retained as a first-class source
-- object.  Its generic attribution law remains non-promoting: citation does not
-- itself import proof or create legal authority.
------------------------------------------------------------------------

edelman64Locator : String
edelman64Locator = "Cullen v New South Wales [2026] HCA 19, Edelman J [64]"

edelman64SourceReference : String
edelman64SourceReference = "source:Cullen:[2026]HCA19#Edelman-[64]"

edelman64PrimarySource : Source.AttributedSource
edelman64PrimarySource = PrimarySources.cullenHCA19

edelman64PrimarySourceDoesNotCreateAuthority :
  Source.citationCreatesAuthority edelman64PrimarySource ≡ false
edelman64PrimarySourceDoesNotCreateAuthority =
  Source.citationCreatesAuthorityIsFalse edelman64PrimarySource

edelman64NoStatutoryPowerInvocation : Algebra.LegalProposition
edelman64NoStatutoryPowerInvocation = Algebra.legal-proposition
  (Ontology.stableId "prop:Cullen:Edelman:64:no-statutory-power-invocation")
  Algebra.institutionalConstraint
  (Ontology.stableId "actor:NSW-police")
  (Ontology.stableId "activity:OSG-intervention")
  Negligence.auCommonLawSystem
  "the OSG intervention was not said in the High Court to be pursuant to any statutory power"

edelman64PositiveActsCreatingRisk : Algebra.LegalProposition
edelman64PositiveActsCreatingRisk = Algebra.legal-proposition
  (Ontology.stableId "prop:Cullen:Edelman:64:positive-acts-creating-risk")
  Algebra.factualFeature
  (Ontology.stableId "actor:NSW-police")
  (Ontology.stableId "activity:OSG-intervention")
  Negligence.auCommonLawSystem
  "the liability route is based on positive acts creating risk rather than an omission to prevent third-party action"

edelman64OrdinaryCommonLawDuty : Algebra.LegalProposition
edelman64OrdinaryCommonLawDuty = Algebra.legal-proposition
  (Ontology.stableId "prop:Cullen:Edelman:64:ordinary-common-law-duty")
  Algebra.doctrinalPredicate
  (Ontology.stableId "actor:NSW-police")
  (Ontology.stableId "issue:negligence:duty")
  Negligence.auCommonLawSystem
  "the applicable duty includes the ordinary common-law duty to avoid causing reasonably foreseeable injury"

edelman64NoStatutoryPowerFact : Algebra.LegalFact
edelman64NoStatutoryPowerFact = Algebra.legal-fact
  edelman64NoStatutoryPowerInvocation
  edelman64Locator
  edelman64SourceReference

edelman64PositiveActsFact : Algebra.LegalFact
edelman64PositiveActsFact = Algebra.legal-fact
  edelman64PositiveActsCreatingRisk
  edelman64Locator
  edelman64SourceReference

edelman64OrdinaryDutyFact : Algebra.LegalFact
edelman64OrdinaryDutyFact = Algebra.legal-fact
  edelman64OrdinaryCommonLawDuty
  edelman64Locator
  edelman64SourceReference

------------------------------------------------------------------------
-- Primary-source attachments for the WrongType and duty-element steps.
--
-- The same judgment may be relevant at more than one stage, but each stage gets
-- its own typed attachment and proposition relationship.  Co-location of a
-- source does not make one attachment pay another stage.
------------------------------------------------------------------------

edelman64WrongTypeAttachment :
  Downstream.PrimarySourceAttachment Downstream.wrongTypeClassificationStage
edelman64WrongTypeAttachment =
  Downstream.primary-source-attachment
    edelman64PrimarySource
    edelman64Locator
    edelman64OrdinaryCommonLawDuty
    "Edelman [64] is a primary judicial source supporting the negligence-duty classification route; the citation itself does not create the WrongType or legal authority."
    edelman64PrimarySourceDoesNotCreateAuthority

edelman64WrongTypePrimarySource :
  Downstream.WrongTypePrimarySource Negligence.negligenceWrongType
edelman64WrongTypePrimarySource =
  Downstream.wrongtype-primary-source
    edelman64WrongTypeAttachment
    refl
    (Ontology.WrongType.wrongTypeId Negligence.negligenceWrongType)
    refl

edelman64DutyElementAttachment :
  Downstream.PrimarySourceAttachment Downstream.wrongElementDefinitionStage
edelman64DutyElementAttachment =
  Downstream.primary-source-attachment
    edelman64PrimarySource
    edelman64Locator
    edelman64OrdinaryCommonLawDuty
    "Edelman [64] is attached to the duty-element definition/use for this Cullen route; breach remains a different element and requires its own evaluation/source payment."
    edelman64PrimarySourceDoesNotCreateAuthority

edelman64DutyElementPrimarySource :
  Downstream.WrongElementPrimarySource Negligence.dutyElement
edelman64DutyElementPrimarySource =
  Downstream.wrongelement-primary-source
    edelman64DutyElementAttachment
    refl
    "element:negligence:duty"
    edelman64Locator

------------------------------------------------------------------------
-- Source proposition -> route reconstruction.
--
-- These are explicit reconstruction receipts, not claims of textual identity.
------------------------------------------------------------------------

record Edelman64RouteReconstruction : Set₁ where
  constructor edelman64-route-reconstruction
  field
    primarySource : Source.AttributedSource
    primarySourceIsCullen : primarySource ≡ edelman64PrimarySource
    sourceNoStatutoryPower : Algebra.LegalFact
    sourcePositiveActs : Algebra.LegalFact
    sourceOrdinaryDuty : Algebra.LegalFact
    route : Routes.CullenReasoningRoute
    routeIsEdelman : route ≡ Routes.edelmanReasons
    reconstructedNoPowerRequirement : Algebra.LegalProposition
    reconstructedNoPowerRequirementIsRouteProposition :
      reconstructedNoPowerRequirement
      ≡ Routes.statutoryPowerNotRequiredOnEdelmanRoute
    reconstructionReference : String

open Edelman64RouteReconstruction public

edelman64RouteReconstruction : Edelman64RouteReconstruction
edelman64RouteReconstruction = edelman64-route-reconstruction
  edelman64PrimarySource
  refl
  edelman64NoStatutoryPowerFact
  edelman64PositiveActsFact
  edelman64OrdinaryDutyFact
  Routes.edelmanReasons
  refl
  Routes.statutoryPowerNotRequiredOnEdelmanRoute
  refl
  "DASHI reconstruction from the three direct propositions anchored at Edelman J [64]; not a claim that the reconstructed proposition is verbatim judicial text."

------------------------------------------------------------------------
-- WrongType / element weld.
--
-- This source route is interpreted only inside the canonical negligence
-- WrongType and specifically against its duty element.
------------------------------------------------------------------------

record Edelman64WrongTypeDutyReceipt : Set₁ where
  constructor edelman64-wrongtype-duty-receipt
  field
    sourceRoute : Edelman64RouteReconstruction
    wrongTypePrimarySource :
      Downstream.WrongTypePrimarySource Negligence.negligenceWrongType
    dutyElementPrimarySource :
      Downstream.WrongElementPrimarySource Negligence.dutyElement
    wrongType : Ontology.WrongType
    wrongTypeIsNegligence : wrongType ≡ Negligence.negligenceWrongType
    targetElement : Elements.LegalElement Negligence.negligenceWrongType
    targetIsDuty : targetElement ≡ Negligence.dutyElement
    wrongTypeSystem : Ontology.StableId
    wrongTypeSystemIsAustralianNegligence :
      wrongTypeSystem ≡ Negligence.auCommonLawSystem
    wrongTypeSystemMatchesWrongType :
      wrongTypeSystem ≡ Ontology.WrongType.definingSystem wrongType
    receiptReference : String

open Edelman64WrongTypeDutyReceipt public

edelman64NegligenceDutyReceipt : Edelman64WrongTypeDutyReceipt
edelman64NegligenceDutyReceipt = edelman64-wrongtype-duty-receipt
  edelman64RouteReconstruction
  edelman64WrongTypePrimarySource
  edelman64DutyElementPrimarySource
  Negligence.negligenceWrongType
  refl
  Negligence.dutyElement
  refl
  Negligence.auCommonLawSystem
  refl
  refl
  "Edelman [64] source route, canonical primary-source object and paragraph locator welded to wrong:AU:negligence / element:negligence:duty."

------------------------------------------------------------------------
-- Hard non-promotions.
------------------------------------------------------------------------

data DirectParagraphFactIsRouteRule : Set where
data NoStatutoryPowerInvocationMeansNoNegligence : Set where
data WrongTypeIdentityAutomaticallyPaysDuty : Set where
data DutyElementIdentityAutomaticallyProvesApplicability : Set where
data EdelmanRouteAutomaticallyEstablishesBreach : Set where
data PrimarySourceAttachmentCreatesAuthority : Set where
data DutySourceAttachmentPaysBreach : Set where

directFactDoesNotBecomeCompiledRule : DirectParagraphFactIsRouteRule → ⊥
directFactDoesNotBecomeCompiledRule ()

noPowerInvocationDoesNotEraseNegligenceWrongType :
  NoStatutoryPowerInvocationMeansNoNegligence → ⊥
noPowerInvocationDoesNotEraseNegligenceWrongType ()

wrongTypeIdentityDoesNotPayDuty : WrongTypeIdentityAutomaticallyPaysDuty → ⊥
wrongTypeIdentityDoesNotPayDuty ()

dutyIdentityDoesNotProveApplicability :
  DutyElementIdentityAutomaticallyProvesApplicability → ⊥
dutyIdentityDoesNotProveApplicability ()

edelmanDutyRouteDoesNotEstablishBreach :
  EdelmanRouteAutomaticallyEstablishesBreach → ⊥
edelmanDutyRouteDoesNotEstablishBreach ()

primarySourceAttachmentDoesNotCreateAuthority :
  PrimarySourceAttachmentCreatesAuthority → ⊥
primarySourceAttachmentDoesNotCreateAuthority ()

dutyAttachmentDoesNotPayBreach : DutySourceAttachmentPaysBreach → ⊥
dutyAttachmentDoesNotPayBreach ()

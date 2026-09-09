module DASHI.Cognition.PNF.SensibLawCullenEdelman64WrongTypeSourceRealisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as Elements
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence
import DASHI.Cognition.PNF.SensibLawCullenSourceCorrectDutyRoutesExact as Routes

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
------------------------------------------------------------------------

edelman64Locator : String
edelman64Locator = "Cullen v New South Wales [2026] HCA 19, Edelman J [64]"

edelman64SourceReference : String
edelman64SourceReference = "source:Cullen:[2026]HCA19#Edelman-[64]"

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
-- Source proposition -> route reconstruction.
--
-- These are explicit reconstruction receipts, not claims of textual identity.
------------------------------------------------------------------------

record Edelman64RouteReconstruction : Set₁ where
  constructor edelman64-route-reconstruction
  field
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
  Negligence.negligenceWrongType
  refl
  Negligence.dutyElement
  refl
  Negligence.auCommonLawSystem
  refl
  refl
  "Edelman [64] source route welded to wrong:AU:negligence / element:negligence:duty."

------------------------------------------------------------------------
-- Hard non-promotions.
------------------------------------------------------------------------

data DirectParagraphFactIsRouteRule : Set where
data NoStatutoryPowerInvocationMeansNoNegligence : Set where
data WrongTypeIdentityAutomaticallyPaysDuty : Set where
data DutyElementIdentityAutomaticallyProvesApplicability : Set where
data EdelmanRouteAutomaticallyEstablishesBreach : Set where

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

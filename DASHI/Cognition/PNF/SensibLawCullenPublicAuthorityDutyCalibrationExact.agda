module DASHI.Cognition.PNF.SensibLawCullenPublicAuthorityDutyCalibrationExact where

------------------------------------------------------------------------
-- CULLEN PUBLIC-AUTHORITY / POSITIVE-ACT DUTY CALIBRATION
--
-- Primary source:
--   High Court of Australia, Cullen v New South Wales [2026] HCA 19,
--   S47/2025, judgment 17 June 2026.
--   Stable identifier: [2026] HCA 19.
--   Stable HCA page:
--   https://www.hcourt.gov.au/cases-and-judgments/judgments/judgments-1998-current/cullen-v-new-south-wales
--
-- The HCA judgment/catchwords concern negligence, duty and scope of duty,
-- public authorities/police, positive operational crowd-control conduct,
-- foreseeable physical injury, statutory functions, and breach. The Court
-- recognised a duty to exercise reasonable care toward members of the crowd and
-- bystanders foreseeably at risk from the operational response, but held breach
-- was not established and dismissed the appeal.
--
-- Statutory sources identified by the HCA judgment:
--   Civil Liability Act 2002 (NSW), ss 5B, 5C, 5D.
--   Law Enforcement (Powers and Responsibilities) Act 2002 (NSW),
--     ss 4, 198, 199, 200, 230, 231.
--   Police Act 1990 (NSW), ss 6, 13, 14.
--
-- This module uses Cullen as a calibration against the invalid categorical
-- shortcut `public authority -> no duty`. It does NOT transfer Cullen's police /
-- crowd-control holding to climate policy, and it does not assert that
-- foreseeability alone is sufficient for every novel duty category.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawPrecedentApplicabilityDistinguishingExact as Precedent
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence
import DASHI.Cognition.PNF.SensibLawLegalObserverResidualRefinementBidiExact as Residual
import DASHI.Cognition.PNF.SensibLawClimateDutyRouteSearchExact as Climate

------------------------------------------------------------------------
-- Source container and proposition-specific precedent receipts.
------------------------------------------------------------------------

cullenLegalSource : Ontology.LegalSource
cullenLegalSource = Ontology.legalSource
  (Ontology.stableId "source:Cullen:[2026]HCA19")
  Negligence.auCommonLawSystem
  Ontology.caseLaw
  "[2026] HCA 19"
  "2026-06-17"
  "Australia / High Court"

cullenSource : Algebra.LegalSourceRef
cullenSource = Algebra.legal-source-ref
  cullenLegalSource
  "High Court of Australia"
  "Cullen v New South Wales"
  "[2026] HCA 19; S47/2025; 17 June 2026"

positiveOperationalAct : Algebra.LegalProposition
positiveOperationalAct = Algebra.legal-proposition
  (Ontology.stableId "prop:Cullen:positive-operational-act")
  Algebra.factualFeature
  (Ontology.stableId "actor:NSW-police")
  (Ontology.stableId "activity:crowd-control")
  Negligence.auCommonLawSystem
  "police positively intervened in crowd-control operations"

foreseeablePhysicalInjuryRisk : Algebra.LegalProposition
foreseeablePhysicalInjuryRisk = Algebra.legal-proposition
  (Ontology.stableId "prop:Cullen:foreseeable-physical-injury-risk")
  Algebra.factualFeature
  (Ontology.stableId "actor:NSW-police")
  (Ontology.stableId "class:crowd-and-bystanders")
  Negligence.auCommonLawSystem
  "members of the crowd and bystanders were foreseeably at risk of physical injury from the operational response"

statutoryPoliceFunction : Algebra.LegalProposition
statutoryPoliceFunction = Algebra.legal-proposition
  (Ontology.stableId "prop:Cullen:statutory-police-function")
  Algebra.institutionalConstraint
  (Ontology.stableId "actor:NSW-police")
  (Ontology.stableId "source:Police-Act-1990-NSW")
  Negligence.auCommonLawSystem
  "the conduct occurred in the exercise of statutory police functions/powers"

cullenDutyProposition : Algebra.LegalProposition
cullenDutyProposition = Algebra.legal-proposition
  (Ontology.stableId "prop:Cullen:duty")
  Algebra.wrongElementPredicate
  (Ontology.stableId "actor:NSW-police")
  (Ontology.stableId "class:crowd-and-bystanders")
  Negligence.auCommonLawSystem
  "police owed reasonable care to members of the crowd and bystanders foreseeably at risk of physical injury from the operational response"

cullenBreachNotEstablished : Algebra.LegalProposition
cullenBreachNotEstablished = Algebra.legal-proposition
  (Ontology.stableId "prop:Cullen:breach-not-established")
  Algebra.wrongElementPredicate
  (Ontology.stableId "actor:NSW-police")
  (Ontology.stableId "case:Cullen")
  Negligence.auCommonLawSystem
  "breach of the recognised duty was not established on the facts"

cullenDutyHolding : Precedent.PrecedentProposition
cullenDutyHolding = Precedent.precedent-proposition
  cullenSource
  "High Court of Australia"
  "Australia"
  "2026-06-17"
  cullenDutyProposition
  Precedent.ratio
  true
  (Ontology.stableId "issue:negligence:duty-public-authority-positive-act")
  (positiveOperationalAct ∷ foreseeablePhysicalInjuryRisk ∷ statutoryPoliceFunction ∷ [])
  "current at 17 June 2026 judgment; later treatment not asserted here"

cullenBreachHolding : Precedent.PrecedentProposition
cullenBreachHolding = Precedent.precedent-proposition
  cullenSource
  "High Court of Australia"
  "Australia"
  "2026-06-17"
  cullenBreachNotEstablished
  Precedent.ratio
  true
  (Ontology.stableId "issue:negligence:breach-public-authority-crowd-control")
  (positiveOperationalAct ∷ foreseeablePhysicalInjuryRisk ∷ [])
  "current at 17 June 2026 judgment; later treatment not asserted here"

------------------------------------------------------------------------
-- Calibration results.
------------------------------------------------------------------------

data PublicAuthorityFunctionCategoricallyPrecludesDuty : Set where
data DutyRecognisedAutomaticallyEstablishesBreach : Set where
data CullenPoliceDutyAutomaticallyEstablishesClimateDuty : Set where
data ForeseeabilityAloneExplainsCullenDuty : Set where

publicAuthorityIsNotCategoricalNoDuty :
  PublicAuthorityFunctionCategoricallyPrecludesDuty → ⊥
publicAuthorityIsNotCategoricalNoDuty ()

dutyAndBreachRemainSeparate :
  DutyRecognisedAutomaticallyEstablishesBreach → ⊥
dutyAndBreachRemainSeparate ()

cullenDoesNotAutoCompileToClimateDuty :
  CullenPoliceDutyAutomaticallyEstablishesClimateDuty → ⊥
cullenDoesNotAutoCompileToClimateDuty ()

cullenDoesNotCollapseToForeseeabilityOnly :
  ForeseeabilityAloneExplainsCullenDuty → ⊥
cullenDoesNotCollapseToForeseeabilityOnly ()

------------------------------------------------------------------------
-- BIDI relevance to James's duty-of-care discussion: if a consumer treats
-- `publicAuthorityFunction` as a categorical blocker, Cullen is a source-backed
-- discriminator requiring that gate to be reopened/refined rather than merely
-- relabelled.
------------------------------------------------------------------------

publicAuthorityResidualKind : Residual.LegalResidualKind
publicAuthorityResidualKind =
  Residual.dutyResidualKind Climate.publicAuthorityFunction

publicAuthorityResidualIsInstitutional :
  publicAuthorityResidualKind ≡ Residual.missingInstitutionalConstraint
publicAuthorityResidualIsInstitutional = refl

publicAuthorityResidualRoutesToReasons :
  Residual.preferredRoute publicAuthorityResidualKind
  ≡ Residual.inspectJudicialReasons
publicAuthorityResidualRoutesToReasons = refl

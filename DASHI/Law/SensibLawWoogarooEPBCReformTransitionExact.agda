module DASHI.Law.SensibLawWoogarooEPBCReformTransitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- EPBC REFORM TRANSITION — EPBC 2019/8575
--
-- Source-bounded transition receipt for the 2026 staged environment-law
-- reforms.  This module keeps three questions separate:
--   (1) which substantive/assessment law applies to this 2019 referral;
--   (2) who may exercise the relevant power under current delegations; and
--   (3) where the public assessment record is currently held/published.
-- None is inferred merely from the existence of the National EPA.
------------------------------------------------------------------------

record TransitionReceipt : Set where
  constructor transition-receipt
  field
    project : String
    referralPredatesCommencement : Bool
    assessmentApproachPredatesCommencement : Bool
    nationalEPAEstablished : String
    augustTransitionCommencement : String
    existingReferralStillAssessedUnderCurrentEPBCAct : Bool
    oldAssessmentFrameworkPotentiallyPreserved : Bool
    newPart9ThreatenedSpeciesRulesAutomaticallyApply : Bool
    counselConstructionStillRequired : Bool

open TransitionReceipt public

epbc8575Transition : TransitionReceipt
epbc8575Transition = transition-receipt
  "Springfield Residential Development — EPBC 2019/8575"
  true
  true
  "1 July 2026"
  "24 August 2026"
  true
  true
  false
  true

------------------------------------------------------------------------
-- Agency/delegation state.
------------------------------------------------------------------------

record FederalDecisionAdministration : Set where
  constructor federal-decision-administration
  field
    nationalEPAOperational : Bool
    nationalEPAProjectAssessmentRole : Bool
    ministerMayDelegateEPBCFunctionsToNEPA : Bool
    currentMinisterToNEPADelegationInstrumentExists : Bool
    currentMinisterToDepartmentDelegationInstrumentExists : Bool
    exact20198575DecisionMakerSupersededByAgencyCreation : Bool
    latestProjectSpecificDelegateEvidence : String
    acquisitionRouting : String

currentFederalDecisionAdministration : FederalDecisionAdministration
currentFederalDecisionAdministration = federal-decision-administration
  true
  true
  true
  true
  true
  false
  "The project-specific s 130(1A) extension notice dated 2 September 2026 names Declan O'Connor-Cox, Branch Head, Environment Assessments Queensland, as the authorised decision-maker for EPBC 2019/8575. National EPA establishment/delegation does not by itself displace that later project-specific evidence."
  "For missing assessment records, query the National EPA/current EPBC records channel and DCCEEW as necessary; ask the recipient to identify the current custodian if the record has migrated. Do not assume website ownership identifies the statutory decision-maker."

------------------------------------------------------------------------
-- August 2026 rule changes relevant to a still-pending older referral.
------------------------------------------------------------------------

record August2026RuleReceipt : Set where
  constructor august-2026-rule-receipt
  field
    nepaRulesCommence24August : Bool
    transparencyRegistersIntroduced : Bool
    augustTransitionalRulesCommence24August : Bool
    preExistingReferralAutomaticallyConvertedToNewAssessmentSystem : Bool
    laterDecisionMayEngageNewCrossCuttingRules : Bool
    exactProvisionMatchingRequired : Bool

august2026RuleReceipt : August2026RuleReceipt
august2026RuleReceipt = august-2026-rule-receipt
  true
  true
  true
  false
  true
  true

------------------------------------------------------------------------
-- Typed boundaries.
------------------------------------------------------------------------

record TransitionBoundary : Set where
  constructor transition-boundary
  field
    currentActTextAloneDoesNotDetermineHistoricReferralRule : Bool
    reformCommencementDoesNotRestartReferral : Bool
    preCommencementReferralDoesNotMeanAllOldLawAutomaticallyApplies : Bool
    preCommencementAssessmentDoesNotMeanAllNewLawAutomaticallyApplies : Bool
    nationalEPAExistenceDoesNotIdentifyExactProjectDelegate : Bool
    recordsCustodianDoesNotEqualDecisionMaker : Bool
    transitionalItemMustBeMatchedToExactProvision : Bool

transitionBoundary : TransitionBoundary
transitionBoundary = transition-boundary true true true true true true true

data NationalEPAExistenceEqualsExact8575DecisionMaker : Set where
data PortalHostEqualsStatutoryDecisionMaker : Set where
data ExistingReferralEqualsNewAssessmentSystem : Set where
data NewRulesExistEqualsAllNewRulesApply : Set where

nationalEPAExistenceDoesNotChoose8575DecisionMaker : NationalEPAExistenceEqualsExact8575DecisionMaker → ⊥
nationalEPAExistenceDoesNotChoose8575DecisionMaker ()

portalHostDoesNotChooseDecisionMaker : PortalHostEqualsStatutoryDecisionMaker → ⊥
portalHostDoesNotChooseDecisionMaker ()

existingReferralDoesNotBecomeNewAssessmentSystem : ExistingReferralEqualsNewAssessmentSystem → ⊥
existingReferralDoesNotBecomeNewAssessmentSystem ()

newRulesDoNotAllAutomaticallyApply : NewRulesExistEqualsAllNewRulesApply → ⊥
newRulesDoNotAllAutomaticallyApply ()

------------------------------------------------------------------------
-- Counsel residual.
------------------------------------------------------------------------

record TransitionResidual : Set where
  constructor transition-residual
  field
    question : String
    sourceState : String
    outcomeAlreadyProved : Bool

transitionResidual : TransitionResidual
transitionResidual = transition-residual
  "For EPBC 2019/8575, identify provision-by-provision which pre-24-August-2026 and post-24-August-2026 rules govern the pending Part 9 decision; confirm the current operative delegation for the exact approval/refusal power; and identify the current records custodian for the 2026 Preliminary Documentation/comments material."
  "DCCEEW's transitional-arrangements page says projects already referred when the new laws take effect continue to be assessed under the current EPBC Act. The National EPA commenced 1 July 2026 and assesses projects/sets approval conditions under delegation. Current EPBC delegation instruments dated 24 August 2026 exist both to the Department and to NEPA. The 2 September 2026 project-specific extension notice remains the strongest exact evidence presently held for who is authorised on 2019/8575."
  false

------------------------------------------------------------------------
-- Attributed public sources.
------------------------------------------------------------------------

nepaActSource : Source.AttributedSource
nepaActSource = Source.mkNoDOISource
  "Commonwealth Parliament"
  "National Environmental Protection Agency Act 2025"
  "Federal Register of Legislation"
  "2025"
  "https://www.legislation.gov.au/C2025A00069/asmade"
  Source.governmentSource
  "Primary source for establishment of the National EPA and its statutory framework; commencement 1 July 2026."
  Source.publicAttribution

nepaRulesSource : Source.AttributedSource
nepaRulesSource = Source.mkNoDOISource
  "Commonwealth of Australia"
  "National Environmental Protection Agency Rules 2026"
  "Federal Register of Legislation — F2026L01105"
  "2026"
  "https://www.legislation.gov.au/F2026L01105/asmade"
  Source.governmentSource
  "Primary source for National EPA transparency registers and registrable decisions; whole instrument commences 24 August 2026."
  Source.publicAttribution

augustTransitionRulesSource : Source.AttributedSource
augustTransitionRulesSource = Source.mkNoDOISource
  "Commonwealth of Australia"
  "Environment Protection Reform (August Commencements) Transitional Rules 2026"
  "Federal Register of Legislation — F2026L01106"
  "2026"
  "https://www.legislation.gov.au/F2026L01106/asmade"
  Source.governmentSource
  "Primary source for 24 August 2026 transitional application/modification rules. Exact effect must be matched provision-by-provision to EPBC 2019/8575."
  Source.publicAttribution

dcceewTransitionSource : Source.AttributedSource
dcceewTransitionSource = Source.mkNoDOISource
  "Department of Climate Change, Energy, the Environment and Water"
  "Transitional arrangements"
  "EPBC Act reform implementation guidance"
  "2026"
  "https://www.dcceew.gov.au/environment/epbc/epbc-act-reform/transitional-arrangements"
  Source.governmentSource
  "Government implementation guidance stating that projects already referred when the new laws take effect will still be assessed under the current EPBC Act."
  Source.publicAttribution

dcceewDelegationRegisterSource : Source.AttributedSource
dcceewDelegationRegisterSource = Source.mkNoDOISource
  "Department of Climate Change, Energy, the Environment and Water"
  "Register of EPBC delegations"
  "DCCEEW public delegation register"
  "2026"
  "https://www.dcceew.gov.au/environment/epbc/register-of-delegations"
  Source.governmentSource
  "Government register showing current Minister/Secretary delegation instruments dated 24 August 2026 to both Departmental and National EPA recipients. It does not by itself identify which delegate is exercising the exact 2019/8575 decision."
  Source.publicAttribution

transitionSourceAtlas : Source.AttributedSourceAtlas
transitionSourceAtlas = Source.mkSourceAtlas
  "Woogaroo EPBC 2019/8575 reform-transition source atlas"
  "DASHI.Law.SensibLawWoogarooEPBCReformTransitionExact"
  (nepaActSource ∷ nepaRulesSource ∷ augustTransitionRulesSource ∷ dcceewTransitionSource ∷ dcceewDelegationRegisterSource ∷ [])
  "Primary legislation/instruments plus government implementation guidance. These sources identify the transition architecture, not the final merits outcome or exact current delegate absent project-specific evidence."

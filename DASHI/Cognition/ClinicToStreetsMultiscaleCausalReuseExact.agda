module DASHI.Cognition.ClinicToStreetsMultiscaleCausalReuseExact where

------------------------------------------------------------------------
-- CLINIC-TO-STREETS -> CANONICAL MULTISCALE CAUSAL ROUTER
--
-- ClinicToStreetsCausalProvenanceExact keeps source-facing labels such as
-- structural / familial / intrapsychic because they are useful for expressing
-- the supplied text.  Those labels are not a second generic causal ontology.
-- Empirical promotion is routed through the already-owned multiscale causal
-- provenance / proof-search carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Biology.MultiscaleCausalProvenanceProofSearchRouterExact as Router
import DASHI.Cognition.ClinicToStreetsCausalProvenanceExact as Clinic

data ClinicCausalValue : Set where
  structuralExposureValue : ClinicCausalValue
  psychicOutcomeValue : ClinicCausalValue

structuralToPsychicCrossLevelClaim : Router.CrossLevelCausalClaim ClinicCausalValue
structuralToPsychicCrossLevelClaim =
  Router.cross-level-causal-claim
    Router.culturalInstitutionalLevel
    Router.thoughtContentLevel
    structuralExposureValue
    psychicOutcomeValue
    "Clinic-to-Streets structural/institutional -> psychic/interpretive causal target"
    "supplied reel/book attribution plus any later same-object structural exposure source"
    "same-object psychic/affective/causal-attribution outcome source"

-- The family/intimate site is preserved as a potential mediator coordinate,
-- not forced into a new global causal-level taxonomy.  Actual mediation payment
-- must use the generic mediation estimand + identification receipts imported by
-- ClinicToStreetsEvidenceAcquisitionMaxCutExact.
familyIntimateSiteRetainedAsMediatorCoordinate : Bool
familyIntimateSiteRetainedAsMediatorCoordinate = true

reusesMultiscaleCausalRouter : Bool
reusesMultiscaleCausalRouter = true

localCausalLevelsOwnEmpiricalPromotion : Bool
localCausalLevelsOwnEmpiricalPromotion = false

inheritedMultiscaleBoundary : Router.MultiscaleCausalProvenanceBoundary
inheritedMultiscaleBoundary = Router.canonicalMultiscaleCausalProvenanceBoundary

-- Preserve the canonical firewalls rather than restating a weaker Clinic-only
-- causal rule.
correlationStillDoesNotIdentifyCause :
  Router.CorrelationMeansCausationPermission → ⊥
correlationStillDoesNotIdentifyCause = Router.correlationDoesNotByItselfIdentifyCause

temporalOrderStillDoesNotIdentifyCause :
  Router.TemporalOrderMeansCausationPermission → ⊥
temporalOrderStillDoesNotIdentifyCause = Router.temporalOrderDoesNotByItselfIdentifyCause

sourceAcquisitionStillDoesNotProveCausation :
  Router.SourceAcquisitionAutomaticallyProvesCausationPermission → ⊥
sourceAcquisitionStillDoesNotProveCausation =
  Router.sourceAcquisitionDoesNotAutomaticallyProveCausation

record ClinicMultiscaleCausalReuseBoundary : Set where
  constructor clinic-multiscale-causal-reuse-boundary
  field
    transcriptFacingLevelsRetained : Bool
    transcriptFacingLevelsAreGenericCausalAuthority : Bool
    multiscaleRouterOwnsEmpiricalPromotionRoute : Bool
    familyIntimateMediatorRemainsExplicit : Bool
    sourceAcquisitionAlonePaysCausalEffect : Bool

canonicalClinicMultiscaleCausalReuseBoundary : ClinicMultiscaleCausalReuseBoundary
canonicalClinicMultiscaleCausalReuseBoundary =
  clinic-multiscale-causal-reuse-boundary true false true true false

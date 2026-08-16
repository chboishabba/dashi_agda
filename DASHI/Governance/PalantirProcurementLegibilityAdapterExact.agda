module DASHI.Governance.PalantirProcurementLegibilityAdapterExact where

------------------------------------------------------------------------
-- BOUNDED EMPIRICAL ADAPTER
--
-- Existing repository primary-policy sources:
--   * White House, "Stopping Waste, Fraud, and Abuse by Eliminating
--     Information Silos", Executive Order 14243, 2025-03-20.
--   * USAspending / Department of Homeland Security,
--     "Homeland Security Investigations case-management and analytics
--     modernization", PIID 70CTD026FC0000018, 2026-06-26.
--
-- The existing Trump policy atlas binds those sources to a Palantir/comparable
-- vendor data-integration and case-management procurement surface.  This module
-- imports that empirical surface and states exactly what it DOES NOT yet prove:
-- procurement alone is not a subject/institution observation channel, an
-- asymmetric-legibility witness, abuse, neutrality, or cross-domain authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.TrumpPsychogeographicPolicyAtlasExact as Trump
import DASHI.Governance.AsymmetricLegibilityContestabilityExact as Legibility
import DASHI.Governance.DomainPermeabilityAuthorityTransport as Domain

palantirProcurementSurface : Trump.PolicyCaseSurface
palantirProcurementSurface = Trump.palantirSurveillanceProcurementSurface

palantirCaseExact :
  Trump.PolicyCaseSurface.policyCase palantirProcurementSurface
  ≡ Trump.palantirSurveillanceProcurementCase
palantirCaseExact = refl

palantirMechanismExact :
  Trump.PolicyCaseSurface.mechanism palantirProcurementSurface
  ≡ Trump.dataIntegrationVendorProcurementMechanism
palantirMechanismExact = refl

------------------------------------------------------------------------
-- Evidence stages.
------------------------------------------------------------------------

record ProcurementEvidence : Set where
  constructor procurementEvidence
  field
    surface : Trump.PolicyCaseSurface
    procurementSourceBound : Bool
    policyContextBound : Bool

canonicalPalantirProcurementEvidence : ProcurementEvidence
canonicalPalantirProcurementEvidence =
  procurementEvidence palantirProcurementSurface true true

record LegibilityInstantiation : Set₁ where
  constructor legibilityInstantiation
  field
    channel : Legibility.LegibilityChannel

record AsymmetryInstantiation (L : LegibilityInstantiation) : Set₁ where
  constructor asymmetryInstantiation
  field
    witness : Legibility.AsymmetricLegibilityWitness
      (LegibilityInstantiation.channel L)

------------------------------------------------------------------------
-- Fail-closed stage boundaries.
------------------------------------------------------------------------

data ProcurementAloneConstructsLegibilityChannel : Set where

data ProcurementAloneConstructsAsymmetryWitness : Set where

data ProcurementAloneEstablishesAbuse : Set where

data ProcurementAloneEstablishesNeutrality : Set where

procurementDoesNotConstructLegibilityChannel :
  ProcurementAloneConstructsLegibilityChannel → ⊥
procurementDoesNotConstructLegibilityChannel ()

procurementDoesNotConstructAsymmetryWitness :
  ProcurementAloneConstructsAsymmetryWitness → ⊥
procurementDoesNotConstructAsymmetryWitness ()

procurementDoesNotEstablishAbuse : ProcurementAloneEstablishesAbuse → ⊥
procurementDoesNotEstablishAbuse ()

procurementDoesNotEstablishNeutrality : ProcurementAloneEstablishesNeutrality → ⊥
procurementDoesNotEstablishNeutrality ()

------------------------------------------------------------------------
-- Cross-domain authority remains separately gated by the existing theorem.
------------------------------------------------------------------------

existingDomainAuthorityBoundary :
  Domain.DomainTransportReceipt.targetDomainNeedsOwnAuthorityWitness
    Domain.canonicalDomainTransportReceipt
  ≡ true
existingDomainAuthorityBoundary = refl

record PalantirProcurementAdapterBoundary : Set where
  constructor palantirProcurementAdapterBoundary
  field
    procurementEvidenceInstalled : Bool
    operationalLegibilityChannelInstalled : Bool
    subjectInstitutionAsymmetryWitnessInstalled : Bool
    contestabilityGapInstalled : Bool
    procurementProvesAbuse : Bool
    procurementProvesNeutrality : Bool
    targetDomainAuthorityStillSeparate : Bool

canonicalPalantirProcurementAdapterBoundary : PalantirProcurementAdapterBoundary
canonicalPalantirProcurementAdapterBoundary =
  palantirProcurementAdapterBoundary true false false false false false true

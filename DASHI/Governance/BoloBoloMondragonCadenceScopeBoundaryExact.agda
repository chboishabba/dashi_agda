module DASHI.Governance.BoloBoloMondragonCadenceScopeBoundaryExact where

open import DASHI.Core.Prelude

import DASHI.Core.CriticalRelationalGrammarSourceRegistryExact as Registry
import DASHI.Governance.BoloBoloComparatorWorkloadLowerBoundExact as Workload

------------------------------------------------------------------------
-- MONDRAGON CADENCE SOURCE-SCOPE BOUNDARY
--
-- Attribution correction / refinement:
--
-- 1. Imaz, Freundlich & Kanpandegi (2023) describe the cooperative-level
--    governance architecture and state that the Management Council acts under
--    Governing Council supervision and reports to it at least monthly.
--
-- 2. Mondragon University's official Social Council page describes FACULTY
--    Social Councils.  It says major issues are handled monthly and that each
--    representative gathers represented workers' views through monthly
--    meetings before those views are channelled onward through faculty
--    governance bodies.
--
-- These are compatible examples of recurrent accountability, but they are not
-- the same institution or source claim.  University-faculty cadence must not be
-- generalized into a corporation-wide rule for every Mondragon cooperative.
------------------------------------------------------------------------

mondragonCooperativeGovernance2023Source : Registry.SourceReference
mondragonCooperativeGovernance2023Source = Registry.source-reference
  "Oier Imaz; Fred Freundlich; Aritz Kanpandegi"
  "The Governance of Multistakeholder Cooperatives in Mondragon: The Evolving Relationship among Purpose, Structure and Process"
  "Humanistic Governance in Democratic Organizations, pp. 285-330"
  2023
  "10.1007/978-3-031-17403-2_10"
  "open-access cooperative-governance case study"
  "source for the described cooperative-level Management Council -> Governing Council supervision/reporting relation, including at-least-monthly reporting; not a universal duration or target-bolo workload law"

mondragonUniversitySocialCouncilSource : Registry.SourceReference
mondragonUniversitySocialCouncilSource = Registry.source-reference
  "Mondragon Unibertsitatea"
  "Social Council"
  "official university social-responsibility and transparency page"
  2026
  "https://www2.mondragon.edu/en/meet-mu/social-responsability-transparency/social-council"
  "official institutional governance description"
  "source specifically for faculty Social Councils handling major issues monthly and representatives meeting represented faculty workers monthly before channeling views to faculty governing bodies"

record MondragonCadenceScope : Set where
  constructor mondragon-cadence-scope
  field
    cooperativeManagementReportsToGoverningAtLeastMonthly : Bool
    universityFacultySocialCouncilMajorIssuesMonthly : Bool
    universityFacultyRepresentativeMeetsRepresentedMonthly : Bool

open MondragonCadenceScope public

canonicalMondragonCadenceScope : MondragonCadenceScope
canonicalMondragonCadenceScope =
  mondragon-cadence-scope true true true

-- The older workload owner retains these booleans as a compact calibration
-- surface.  This scope owner supplies the provenance split that the compact
-- names alone do not express.
legacyManagementCadenceAgrees :
  Workload.mondragonManagementToGoverningAtLeastMonthly
    Workload.canonicalComparatorWorkloadLowerBound ≡
  cooperativeManagementReportsToGoverningAtLeastMonthly
    canonicalMondragonCadenceScope
legacyManagementCadenceAgrees = refl

legacyRepresentativeCadenceAgrees :
  Workload.mondragonRepresentativeToRepresentedMonthly
    Workload.canonicalComparatorWorkloadLowerBound ≡
  universityFacultyRepresentativeMeetsRepresentedMonthly
    canonicalMondragonCadenceScope
legacyRepresentativeCadenceAgrees = refl

record MondragonCadenceBoundary : Set where
  constructor mondragon-cadence-boundary
  field
    cooperativeChapterMonthlyReportingPaid : Bool
    universityFacultyMonthlyProcessPaid : Bool
    universityFacultyCadenceGeneralisesToAllMondragonCooperatives : Bool
    cooperativeChapterMonthlyReportingEqualsUniversityFacultyCadence : Bool
    eitherCadenceIdentifiesMeetingDuration : Bool
    eitherCadenceIdentifiesTargetBoloCost : Bool
    bothMayInformRecurringAccountabilityDesign : Bool

open MondragonCadenceBoundary public

canonicalMondragonCadenceBoundary : MondragonCadenceBoundary
canonicalMondragonCadenceBoundary =
  mondragon-cadence-boundary
    true true
    false false false false
    true

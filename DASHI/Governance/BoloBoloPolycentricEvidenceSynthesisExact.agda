module DASHI.Governance.BoloBoloPolycentricEvidenceSynthesisExact where

open import DASHI.Core.Prelude

import DASHI.Core.CriticalRelationalGrammarSourceRegistryExact as Registry
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- INDEPENDENT POLYCENTRIC-GOVERNANCE SOURCE SYNTHESIS.
--
-- These sources independently motivate nested/polycentric and dynamic-feedback
-- governance questions. They are not attributed to p.m. and do not constitute
-- an empirical bolo cost model.
------------------------------------------------------------------------

ostrom1990Source : Registry.SourceReference
ostrom1990Source = Registry.source-reference
  "Elinor Ostrom"
  "Governing the Commons: The Evolution of Institutions for Collective Action"
  "Cambridge University Press"
  1990
  "10.1017/CBO9780511807763"
  "institutional-analysis monograph / common-pool-resource comparative synthesis"
  "source for design principle 8: for CPRs that are parts of larger systems, appropriation, provision, monitoring, enforcement, conflict resolution and governance activities are organised in multiple layers of nested enterprises; not a prescription of p.m.'s kana/bolo/tega scales and not a bolo optimality theorem"

ostrom2010PolycentricSource : Registry.SourceReference
ostrom2010PolycentricSource = Registry.source-reference
  "Elinor Ostrom"
  "Beyond Markets and States: Polycentric Governance of Complex Economic Systems"
  "American Economic Review 100(3):641-672"
  2010
  "10.1257/aer.100.3.641"
  "polycentric-governance institutional synthesis"
  "broader source context for polycentric governance of complex systems; kept separate from the 1990 nested-enterprises design-principle provenance"

baldwinEtAl2024Source : Registry.SourceReference
baldwinEtAl2024Source = Registry.source-reference
  "Elizabeth Baldwin; Andreas Thiel; Michael McGinnis; Elke Kellner"
  "Empirical research on polycentric governance: Critical gaps and a framework for studying long-term change"
  "Policy Studies Journal 52(2):319-348"
  2024
  "10.1111/psj.12518"
  "systematic empirical-literature review"
  "review of empirical polycentric-governance research showing both positive and negative features in practice, substantial context dependence, weak concept/variable standardization and limited longitudinal evidence; proposes a Context-Operations-Outcomes-Feedbacks framework for studying dynamic evolution; not a bolo effect estimate"

record PolycentricEvidenceSynthesis : Set where
  constructor polycentricEvidenceSynthesis
  field
    initialEmpiricalPeerReviewedArticleCount : Nat
    coreFunctioningPerformanceArticleCount : Nat
    positiveFeaturesObservedInLiterature : Bool
    negativeFeaturesObservedInLiterature : Bool
    polycentricityIsEmpiricalPanacea : Bool
    sharedCrossStudyVariableLanguageAlreadyAdequate : Bool
    contextOftenUnderSpecified : Bool
    longTermChangeEvidenceLimited : Bool
    crossCaseTransportNeedsQualification : Bool

    ostromNestedEnterprisesPrinciplePresent : Bool
    ostromNestedLayersAddressLargerConnectedSystems : Bool
    ostromPrincipleIsBoloEmpiricalOptimum : Bool

    baldwinCOOFFrameworkProposed : Bool
    baldwinFeedbackAdjustmentMechanismsExplicit : Bool
    baldwinFrameworkDirectlyValidatesBolo : Bool

    directBoloCostBoundPaid : Bool

open PolycentricEvidenceSynthesis public

canonicalPolycentricEvidenceSynthesis : PolycentricEvidenceSynthesis
canonicalPolycentricEvidenceSynthesis =
  polycentricEvidenceSynthesis
    179 112 true true false false true true true
    true true false
    true true false
    false

record PolycentricSourceAttributionBoundary : Set where
  constructor polycentricSourceAttributionBoundary
  field
    ostromNestedEnterprisesAttributedToPM : Bool
    pMArchitectureAttributedToOstrom : Bool
    baldwinCOOFAttributedToPM : Bool
    dashiDynamicTheoremsAttributedToOstromOrBaldwin : Bool
    structuralAlignmentMayBeStudiedWithoutAuthorshipCollapse : Bool

open PolycentricSourceAttributionBoundary public

canonicalPolycentricSourceAttributionBoundary : PolycentricSourceAttributionBoundary
canonicalPolycentricSourceAttributionBoundary =
  polycentricSourceAttributionBoundary false false false false true

canonicalPolycentricEvidenceSynthesisReceipt : GenericReceipt.GenericReceipt
canonicalPolycentricEvidenceSynthesisReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "polycentric governance nested-enterprise and dynamic-feedback evidence synthesis"
    "DASHI.Governance.BoloBoloPolycentricEvidenceSynthesisExact"
    "ostrom1990Source / ostrom2010PolycentricSource / baldwinEtAl2024Source / canonicalPolycentricEvidenceSynthesis / canonicalPolycentricSourceAttributionBoundary"
    "records Ostrom's 1990 nested-enterprises design principle for CPRs embedded in larger systems, separately retains Ostrom's 2010 polycentric-governance synthesis, and records the Baldwin-Thiel-McGinnis-Kellner review's 179-paper empirical sample, 112-paper core subset, mixed outcomes and Context-Operations-Outcomes-Feedbacks dynamic framework"
    "nested/polycentric structural similarity does not collapse authorship, none of these sources specifies p.m.'s architecture or target cost coefficients, and the literature strengthens longitudinal/context/feedback obligations rather than validating bolo'bolo directly"
    "agda -i . DASHI/Governance/BoloBoloPolycentricEvidenceSynthesisRegression.agda"

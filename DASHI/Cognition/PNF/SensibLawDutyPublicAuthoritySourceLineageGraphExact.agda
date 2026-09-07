module DASHI.Cognition.PNF.SensibLawDutyPublicAuthoritySourceLineageGraphExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawFiniteExecutableLegalSearchExact as Search
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence
import DASHI.Cognition.PNF.SensibLawClimateDutyRouteSearchExact as Climate
import DASHI.Cognition.PNF.SensibLawCullenPublicAuthorityDutyCalibrationExact as Cullen
import DASHI.Cognition.PNF.SensibLawDoctrinalGateInterventionDistributionExact as Gate
import DASHI.Cognition.PNF.SensibLawTypedLegalAuthorityEdgeExact as Edge

------------------------------------------------------------------------
-- SOURCE-OWNED DUTY / PUBLIC-AUTHORITY LINEAGE GRAPH
--
-- This replaces a one-case calibration carrier with a finite graph whose rules
-- retain three distinct authority sources and proposition families:
--
--   Mallonland [2024] HCA 25
--     -> salient-features / foreseeability-insufficiency constraint;
--   Cullen [2026] HCA 19
--     -> positive operational public-authority duty holding;
--   Pabai [2025] FCA 796
--     -> current pleaded climate-policy obstruction surface.
--
-- The source-specific propositions are calibrated to existing source owners.
-- Whenever this file turns a source proposition/gate into an implication for
-- executable graph search, that implication is marked dashReconstructionRole
-- unless the upstream owner already identifies the proposition as ratio.
------------------------------------------------------------------------

mallonlandSource : Algebra.LegalSourceRef
mallonlandSource = Negligence.edgeSourceRef Gate.mallonlandAuthority

pabaiSource : Algebra.LegalSourceRef
pabaiSource = Negligence.edgeSourceRef Edge.pabaiAuthority

------------------------------------------------------------------------
-- Mallonland: foreseeability is relevant but does not exhaust novel-duty
-- analysis; further salient relational/doctrinal features remain material.
------------------------------------------------------------------------

mallonlandForeseeability : Algebra.LegalProposition
mallonlandForeseeability = Negligence.compileDutyIssue Climate.reasonableForeseeability

mallonlandFurtherSalientFeaturesRequired : Algebra.LegalProposition
mallonlandFurtherSalientFeaturesRequired = Algebra.legal-proposition
  (Ontology.stableId "prop:Mallonland:further-salient-features-required")
  Algebra.doctrinalPredicate
  Negligence.actorD Negligence.actorP Negligence.auCommonLawSystem
  "reasonable foreseeability does not by itself complete the novel-duty inquiry; further salient features remain material"

mallonlandSalientFeaturesRule : Algebra.LegalRule
mallonlandSalientFeaturesRule = Algebra.legal-rule
  (Ontology.stableId "rule:Mallonland:foreseeability-to-further-salient-features")
  (mallonlandForeseeability ∷ [])
  mallonlandFurtherSalientFeaturesRequired
  [] []
  mallonlandSource
  Algebra.dashReconstructionRole
  "source-calibrated to [2024] HCA 25; implication shape is DASHI reconstruction"
  "Australia / High Court negligence duty analysis"

------------------------------------------------------------------------
-- Cullen: the upstream owner already identifies the specific public-authority
-- duty proposition as ratio with the three material features below.
------------------------------------------------------------------------

cullenPositiveOperationalDutyRule : Algebra.LegalRule
cullenPositiveOperationalDutyRule = Algebra.legal-rule
  (Ontology.stableId "rule:Cullen:source-lineage-positive-operational-duty")
  (Cullen.positiveOperationalAct ∷
   Cullen.foreseeablePhysicalInjuryRisk ∷
   Cullen.statutoryPoliceFunction ∷ [])
  Cullen.cullenDutyProposition
  [] []
  Cullen.cullenSource
  Algebra.bindingRatioRole
  "from 2026-06-17"
  "Australia / High Court / NSW police operational conduct"

------------------------------------------------------------------------
-- Pabai: this is a source-calibrated obstruction proposition. The edge below
-- remains DASHI reconstruction; it is deliberately not a universal rule that
-- every core-government-policy classification defeats every negligence duty.
------------------------------------------------------------------------

pabaiCoreGovernmentPolicy : Algebra.LegalProposition
pabaiCoreGovernmentPolicy = Negligence.compileDutyIssue Climate.coreGovernmentPolicy

pabaiCurrentPleadedClimateDutyUnavailable : Algebra.LegalProposition
pabaiCurrentPleadedClimateDutyUnavailable = Algebra.legal-proposition
  (Ontology.stableId "prop:Pabai:current-pleaded-climate-duty-unavailable")
  Algebra.doctrinalPredicate
  Negligence.actorD Negligence.actorP Negligence.auCommonLawSystem
  "the current pleaded negligence duty is unavailable on the encoded Pabai climate-policy obstruction surface"

pabaiPolicyObstructionRule : Algebra.LegalRule
pabaiPolicyObstructionRule = Algebra.legal-rule
  (Ontology.stableId "rule:Pabai:source-lineage-policy-obstruction")
  (pabaiCoreGovernmentPolicy ∷ [])
  pabaiCurrentPleadedClimateDutyUnavailable
  [] []
  pabaiSource
  Algebra.dashReconstructionRole
  "source-calibrated to [2025] FCA 796; graph implication is DASHI reconstruction"
  "Australia / Federal Court / pleaded Commonwealth climate-duty route"

------------------------------------------------------------------------
-- One richer authority graph. Distinct sources remain distinct graph objects.
------------------------------------------------------------------------

dutyPublicAuthoritySourceLineageGraph : Algebra.LegalGraph
dutyPublicAuthoritySourceLineageGraph = Algebra.legal-graph
  (mallonlandSalientFeaturesRule ∷
   cullenPositiveOperationalDutyRule ∷
   pabaiPolicyObstructionRule ∷ [])
  (mallonlandSource ∷ Cullen.cullenSource ∷ pabaiSource ∷ [])

------------------------------------------------------------------------
-- Source-specific fact fibres over the SAME authority graph.
------------------------------------------------------------------------

mallonlandAssessmentFacts : Algebra.FactSet
mallonlandAssessmentFacts = Algebra.fact-set (mallonlandForeseeability ∷ [])

cullenHoldingFacts : Algebra.FactSet
cullenHoldingFacts = Algebra.fact-set
  (Cullen.positiveOperationalAct ∷
   Cullen.foreseeablePhysicalInjuryRisk ∷
   Cullen.statutoryPoliceFunction ∷ [])

pabaiPolicyFacts : Algebra.FactSet
pabaiPolicyFacts = Algebra.fact-set (pabaiCoreGovernmentPolicy ∷ [])

climateComparatorFacts : Algebra.FactSet
climateComparatorFacts = Algebra.fact-set
  (Negligence.compileDutyIssue Climate.reasonableForeseeability ∷
   Negligence.compileDutyIssue Climate.knowledge ∷
   Negligence.compileDutyIssue Climate.control ∷
   pabaiCoreGovernmentPolicy ∷ [])

------------------------------------------------------------------------
-- Executable regressions on the richer source lineage.
------------------------------------------------------------------------

mallonlandConstraintReachable :
  Search.reachable 1 dutyPublicAuthoritySourceLineageGraph mallonlandAssessmentFacts
    mallonlandFurtherSalientFeaturesRequired ≡ true
mallonlandConstraintReachable = refl

cullenSpecificDutyReachable :
  Search.reachable 1 dutyPublicAuthoritySourceLineageGraph cullenHoldingFacts
    Cullen.cullenDutyProposition ≡ true
cullenSpecificDutyReachable = refl

pabaiCurrentObstructionReachable :
  Search.reachable 1 dutyPublicAuthoritySourceLineageGraph pabaiPolicyFacts
    pabaiCurrentPleadedClimateDutyUnavailable ≡ true
pabaiCurrentObstructionReachable = refl

------------------------------------------------------------------------
-- Cross-case non-transfer on the same graph.
--
-- Climate comparator facts do not manufacture Cullen's police/crowd-control
-- ratio, while Cullen facts do not manufacture the Pabai climate obstruction.
------------------------------------------------------------------------

climateFactsDoNotReachCullenSpecificDuty :
  Search.reachable 1 dutyPublicAuthoritySourceLineageGraph climateComparatorFacts
    Cullen.cullenDutyProposition ≡ false
climateFactsDoNotReachCullenSpecificDuty = refl

cullenFactsDoNotReachPabaiClimateObstruction :
  Search.reachable 1 dutyPublicAuthoritySourceLineageGraph cullenHoldingFacts
    pabaiCurrentPleadedClimateDutyUnavailable ≡ false
cullenFactsDoNotReachPabaiClimateObstruction = refl

------------------------------------------------------------------------
-- Proof-relevant positive promotions on the same richer graph.
------------------------------------------------------------------------

mallonlandConstraintProof :
  Algebra.Reachable dutyPublicAuthoritySourceLineageGraph mallonlandAssessmentFacts
    mallonlandFurtherSalientFeaturesRequired
mallonlandConstraintProof = Algebra.byRule
  Algebra.here
  tt
  (Algebra._∷_ (Algebra.fromFact Algebra.here) Algebra.[])
  Algebra.[] Algebra.[]

cullenSpecificDutyProof :
  Algebra.Reachable dutyPublicAuthoritySourceLineageGraph cullenHoldingFacts
    Cullen.cullenDutyProposition
cullenSpecificDutyProof = Algebra.byRule
  (Algebra.there Algebra.here)
  tt
  (Algebra._∷_ (Algebra.fromFact Algebra.here)
    (Algebra._∷_ (Algebra.fromFact (Algebra.there Algebra.here))
      (Algebra._∷_
        (Algebra.fromFact (Algebra.there (Algebra.there Algebra.here)))
        Algebra.[])))
  Algebra.[] Algebra.[]

pabaiCurrentObstructionProof :
  Algebra.Reachable dutyPublicAuthoritySourceLineageGraph pabaiPolicyFacts
    pabaiCurrentPleadedClimateDutyUnavailable
pabaiCurrentObstructionProof = Algebra.byRule
  (Algebra.there (Algebra.there Algebra.here))
  tt
  (Algebra._∷_ (Algebra.fromFact Algebra.here) Algebra.[])
  Algebra.[] Algebra.[]

------------------------------------------------------------------------
-- Attribution / transfer firewalls.
------------------------------------------------------------------------

data MallonlandGraphEdgeIsVerbatimJudicialTest : Set where
data PabaiGraphEdgeIsUniversalCorePolicyNoDutyRule : Set where
data CullenSpecificDutyAutomaticallyTransfersToClimate : Set where
data SharedAuthorityGraphCollapsesSourceRoles : Set where

mallonlandImplicationRemainsReconstruction :
  MallonlandGraphEdgeIsVerbatimJudicialTest → ⊥
mallonlandImplicationRemainsReconstruction ()

pabaiObstructionDoesNotUniversalise :
  PabaiGraphEdgeIsUniversalCorePolicyNoDutyRule → ⊥
pabaiObstructionDoesNotUniversalise ()

cullenStillRequiresMaterialFit :
  CullenSpecificDutyAutomaticallyTransfersToClimate → ⊥
cullenStillRequiresMaterialFit ()

sharedGraphDoesNotFlattenAuthority : SharedAuthorityGraphCollapsesSourceRoles → ⊥
sharedGraphDoesNotFlattenAuthority ()

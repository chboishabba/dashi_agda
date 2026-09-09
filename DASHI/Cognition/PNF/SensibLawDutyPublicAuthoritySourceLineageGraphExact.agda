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
import DASHI.Cognition.PNF.SensibLawCullenSourceCorrectDutyRoutesExact as Cullen
import DASHI.Cognition.PNF.SensibLawDoctrinalGateInterventionDistributionExact as Gate
import DASHI.Cognition.PNF.SensibLawTypedLegalAuthorityEdgeExact as Edge

------------------------------------------------------------------------
-- SOURCE-OWNED DUTY / PUBLIC-AUTHORITY LINEAGE GRAPH
--
-- Mallonland, Cullen and Pabai remain distinct source/proposition families.
-- Cullen now contributes TWO source-correct reasoning fibres rather than the
-- old synthetic "statutory police functions/powers" premise bundle:
--
--   Joint reasons: positive conduct + foreseeable injury + police-function context
--   Edelman: positive risk-creating acts + ordinary common-law duty analysis
--            + no requirement that the intervention invoke statutory power.
--
-- The implication-shaped graph edges are DASHI reconstruction unless an
-- upstream source owner separately certifies a more specific authority role.
------------------------------------------------------------------------

mallonlandSource : Algebra.LegalSourceRef
mallonlandSource = Negligence.edgeSourceRef Gate.mallonlandAuthority

pabaiSource : Algebra.LegalSourceRef
pabaiSource = Negligence.edgeSourceRef Edge.pabaiAuthority

------------------------------------------------------------------------
-- Mallonland.
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
-- Cullen source-correct route aliases.
--
-- Compatibility name retained because downstream cut/reachability modules use
-- it, but its premise list is now the Joint-reasons route and NOT the legacy
-- bundled statutory-functions/powers carrier.
------------------------------------------------------------------------

cullenPositiveOperationalDutyRule : Algebra.LegalRule
cullenPositiveOperationalDutyRule = Cullen.jointReasonsDutyRule

cullenEdelmanDutyRule : Algebra.LegalRule
cullenEdelmanDutyRule = Cullen.edelmanDutyRule

------------------------------------------------------------------------
-- Pabai.
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
-- One richer authority graph.  Distinct Cullen routes remain distinct graph
-- rules even though they share a source and conclusion.
------------------------------------------------------------------------

dutyPublicAuthoritySourceLineageGraph : Algebra.LegalGraph
dutyPublicAuthoritySourceLineageGraph = Algebra.legal-graph
  (mallonlandSalientFeaturesRule ∷
   cullenPositiveOperationalDutyRule ∷
   cullenEdelmanDutyRule ∷
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
   Cullen.policeFunctionContext ∷ [])

cullenEdelmanFacts : Algebra.FactSet
cullenEdelmanFacts = Algebra.fact-set
  (Cullen.positiveRiskCreatingActs ∷
   Cullen.ordinaryCommonLawDutyAnalysis ∷
   Cullen.statutoryPowerNotRequiredOnEdelmanRoute ∷ [])

pabaiPolicyFacts : Algebra.FactSet
pabaiPolicyFacts = Algebra.fact-set (pabaiCoreGovernmentPolicy ∷ [])

climateComparatorFacts : Algebra.FactSet
climateComparatorFacts = Algebra.fact-set
  (Negligence.compileDutyIssue Climate.reasonableForeseeability ∷
   Negligence.compileDutyIssue Climate.knowledge ∷
   Negligence.compileDutyIssue Climate.control ∷
   pabaiCoreGovernmentPolicy ∷ [])

------------------------------------------------------------------------
-- Executable regressions.
------------------------------------------------------------------------

mallonlandConstraintReachable :
  Search.reachable 1 dutyPublicAuthoritySourceLineageGraph mallonlandAssessmentFacts
    mallonlandFurtherSalientFeaturesRequired ≡ true
mallonlandConstraintReachable = refl

cullenSpecificDutyReachable :
  Search.reachable 1 dutyPublicAuthoritySourceLineageGraph cullenHoldingFacts
    Cullen.cullenDutyProposition ≡ true
cullenSpecificDutyReachable = refl

cullenEdelmanDutyReachable :
  Search.reachable 1 dutyPublicAuthoritySourceLineageGraph cullenEdelmanFacts
    Cullen.cullenDutyProposition ≡ true
cullenEdelmanDutyReachable = refl

pabaiCurrentObstructionReachable :
  Search.reachable 1 dutyPublicAuthoritySourceLineageGraph pabaiPolicyFacts
    pabaiCurrentPleadedClimateDutyUnavailable ≡ true
pabaiCurrentObstructionReachable = refl

------------------------------------------------------------------------
-- Cross-case non-transfer on the same graph.
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

cullenEdelmanDutyProof :
  Algebra.Reachable dutyPublicAuthoritySourceLineageGraph cullenEdelmanFacts
    Cullen.cullenDutyProposition
cullenEdelmanDutyProof = Algebra.byRule
  (Algebra.there (Algebra.there Algebra.here))
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
  (Algebra.there (Algebra.there (Algebra.there Algebra.here)))
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
data CullenJointAndEdelmanRoutesAreOnePremiseBundle : Set where

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

cullenRoutesRemainSeparate : CullenJointAndEdelmanRoutesAreOnePremiseBundle → ⊥
cullenRoutesRemainSeparate ()

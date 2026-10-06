module DASHI.Governance.GeneralGroupDecisionQuantitativeEvidenceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- GENERAL GROUP-DECISION QUANTITATIVE EVIDENCE ATLAS.
--
-- Provenance class: EXTERNAL EXPERIMENTAL / META-ANALYTIC LITERATURE.
--
-- These studies are not Occupy studies.  They provide evidence that group size,
-- decision rule, information structure and task can affect decision time,
-- information pooling and quality in specific experimental domains.  They are
-- retained as plausibility / design evidence only and cannot directly validate
-- the OWS archival scaling hypothesis.
------------------------------------------------------------------------

data GeneralEvidenceRole : Set where
  groupSizeDecisionTimeEvidence : GeneralEvidenceRole
  decisionRuleDiscussionTimeEvidence : GeneralEvidenceRole
  informationPoolingModeratorEvidence : GeneralEvidenceRole

record GeneralGroupDecisionSource : Set where
  constructor generalGroupDecisionSource
  field
    authors : String
    title : String
    venue : String
    year : Nat
    identifier : String
    role : GeneralEvidenceRole
    designAndFinding : String
    transferLimit : String

open GeneralGroupDecisionSource public

hwangGuynes1994 : GeneralGroupDecisionSource
hwangGuynes1994 =
  generalGroupDecisionSource
    "Hsin-Ginn Hwang; Jan L. Guynes"
    "The effect of group size on group performance in computer-supported decision making"
    "Information & Management 26(4):189-198"
    1994
    "doi:10.1016/0378-7206(94)90092-2"
    groupSizeDecisionTimeEvidence
    "randomized 3-person versus 9-person computer-supported groups; larger groups generated more alternatives and took longer to reach a final decision, while decision quality could improve"
    "computer-supported laboratory groups are not Occupy working groups; the result does not supply an OWS coefficient or universal monotone law"

millerVanberg2015 : GeneralGroupDecisionSource
millerVanberg2015 =
  generalGroupDecisionSource
    "Luis Miller; Christoph Vanberg"
    "Group size and decision rules in legislative bargaining"
    "European Journal of Political Economy 37:288-302"
    2015
    "doi:10.1016/j.ejpoleco.2014.09.005"
    groupSizeDecisionTimeEvidence
    "Baron-Ferejohn bargaining experiments compare groups of 3 and 7 under majority and unanimity; proposals failed more often in larger groups, increasing costly delay, and unanimity produced more delay than majority"
    "multilateral bargaining with imposed rules is not horizontal Occupy consensus; no direct transfer of treatment effect is licensed"

mckoyEtAl2012 : GeneralGroupDecisionSource
mckoyEtAl2012 =
  generalGroupDecisionSource
    "Marques McKoy; Samantha Spitler; Kelsey Zuchegno; Alana Enslein; Stephen Hobbs; Robert A. Reeves; Tadd B. Patton; W. F. Lawless"
    "An Experimental Physiological Approach to Group Decision Making: Consensus Rule vs Majority Rule"
    "Procedia Technology 5:475-480"
    2012
    "doi:10.1016/j.protcy.2012.09.052"
    decisionRuleDiscussionTimeEvidence
    "small laboratory groups under consensus versus majority rule; the reported three-person results found more utterances under consensus and shorter discussion times under majority, while subsequent five-person task results were mixed and preliminary"
    "small laboratory tasks and preliminary follow-up do not identify an Occupy-wide rule effect; task dependence is material"

luYuanMcLeod2012 : GeneralGroupDecisionSource
luYuanMcLeod2012 =
  generalGroupDecisionSource
    "Li Lu; Y. Connie Yuan; Poppy Lauretta McLeod"
    "Twenty-Five Years of Hidden Profiles in Group Decision Making: A Meta-Analysis"
    "Personality and Social Psychology Review 16(1):54-75"
    2012
    "doi:10.1177/1088868311417243"
    informationPoolingModeratorEvidence
    "meta-analysis of 65 hidden-profile studies / 101 independent effects / 3,189 groups; group size and information load moderated information-pooling and decision-quality effects"
    "hidden-profile laboratory paradigms concern distributed information and do not provide a direct Occupy coordination-cost coefficient"

canonicalGeneralGroupDecisionSources : List GeneralGroupDecisionSource
canonicalGeneralGroupDecisionSources =
  hwangGuynes1994
  ∷ millerVanberg2015
  ∷ mckoyEtAl2012
  ∷ luYuanMcLeod2012
  ∷ []

record GeneralGroupDecisionBoundary : Set where
  constructor generalGroupDecisionBoundary
  field
    largerGroupDelayEvidencePresent : Bool
    consensusRuleTimeEvidencePresent : Bool
    groupSizeInformationPoolingEvidencePresent : Bool

    generalExperimentsDirectlyValidateOccupyScaling : Bool
    effectDirectionUniversalAcrossTasks : Bool
    largerGroupsAlwaysWorse : Bool
    consensusAlwaysSlower : Bool
    laboratoryDecisionTimeEqualsPoliticalCoordinationCost : Bool
    metaAnalysisCreatesOccupyCausalEstimate : Bool
    externalEvidenceCreatesPoliticalAuthority : Bool

open GeneralGroupDecisionBoundary public

canonicalGeneralGroupDecisionBoundary : GeneralGroupDecisionBoundary
canonicalGeneralGroupDecisionBoundary =
  generalGroupDecisionBoundary
    true
    true
    true
    false
    false
    false
    false
    false
    false
    false

canonicalGeneralGroupDecisionEvidenceReceipt : GenericReceipt.GenericReceipt
canonicalGeneralGroupDecisionEvidenceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "general quantitative group-decision evidence atlas"
    "DASHI.Governance.GeneralGroupDecisionQuantitativeEvidenceAtlasExact"
    "canonicalGeneralGroupDecisionBoundary"
    "retains experimental and meta-analytic evidence that group size, decision rule, information structure and task can affect decision delay, discussion and information pooling in specific non-Occupy settings"
    "the literature is external plausibility/design evidence only: it does not directly validate OWS scaling, establish a universal effect direction, equate laboratory time with political coordination cost, or create political authority"
    "agda -i . DASHI/Governance/GeneralGroupDecisionQuantitativeEvidenceAtlasRegression.agda"

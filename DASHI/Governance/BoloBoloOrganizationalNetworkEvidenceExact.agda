module DASHI.Governance.BoloBoloOrganizationalNetworkEvidenceExact where

open import DASHI.Core.Prelude

import DASHI.Core.CriticalRelationalGrammarSourceRegistryExact as Registry
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- ORGANIZATIONAL-NETWORK EVIDENCE FOR MODEL-FAMILY DESIGN.
--
-- These are not democratic-governance comparators. They are independent
-- experiments/field studies showing that centralization effects interact with
-- relational/task context, which constrains the admissible cost-model family.
------------------------------------------------------------------------

dingShiXiao2024Source : Registry.SourceReference
dingShiXiao2024Source = Registry.source-reference
  "Xue Ding; Qian Shi; Chao Xiao"
  "Unveiling the Impact of Communication Network on Engineering Project Team Performance: The Interplay of Centralization and Tie Strength"
  "Psychology Research and Behavior Management 17:1515-1531"
  2024
  "10.2147/PRBM.S454292"
  "720-participant communication-network experiment"
  "evidence that network-centralization performance effects reverse with tie strength in the studied engineering-team simulation; not democratic-governance or bolo evidence"

abiEsberGreerDeHoogh2026Source : Registry.SourceReference
abiEsberGreerDeHoogh2026Source = Registry.source-reference
  "Nicole Abi-Esber; Lindred L. Greer; Annebel H. B. De Hoogh"
  "Team Hierarchical Adaptability: Benefits for Team Coordination and Performance"
  "Academy of Management Journal 69(3):563-592"
  2026
  "10.5465/amj.2023.1308"
  "five-study multimethod organizational-team programme"
  "evidence that teams capable of shifting bidirectionally between flatter and more hierarchical influence structures across tasks can outperform rigid structures; not a bolo institutional optimum"

record OrganizationalNetworkEvidenceBoundary : Set where
  constructor organizationalNetworkEvidenceBoundary
  field
    centralizationHasContextInvariantPositiveEffect : Bool
    decentralizationHasContextInvariantPositiveEffect : Bool
    tieStrengthCanModerateStructuralPerformance : Bool
    adaptiveStructureCanMatterAcrossTasks : Bool
    oneStaticTopologyShouldBeUniversalModelFamily : Bool
    admissibleModelFamilyShouldPermitContextInteractions : Bool
    organizationalTeamEvidenceDirectlyValidatesBolo : Bool

open OrganizationalNetworkEvidenceBoundary public

canonicalOrganizationalNetworkEvidenceBoundary : OrganizationalNetworkEvidenceBoundary
canonicalOrganizationalNetworkEvidenceBoundary =
  organizationalNetworkEvidenceBoundary false false true true false true false

canonicalOrganizationalNetworkEvidenceReceipt : GenericReceipt.GenericReceipt
canonicalOrganizationalNetworkEvidenceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "task-contingent organizational-network evidence for bolo model-family design"
    "DASHI.Governance.BoloBoloOrganizationalNetworkEvidenceExact"
    "canonicalOrganizationalNetworkEvidenceBoundary"
    "adds independent organizational evidence that structural performance is context dependent: the Ding-Shi-Xiao 720-participant experiment reports a centralization-by-tie-strength interaction, while Abi-Esber-Greer-De Hoogh report benefits from bidirectional hierarchy adaptation across tasks in a five-study programme"
    "these studies are not democratic-governance or bolo evaluations; they constrain DASHI's admissible model family by ruling out an evidence-free universal monotone assumption that either more centralization or more decentralization is always better"
    "agda -i . DASHI/Governance/BoloBoloOrganizationalNetworkEvidenceRegression.agda"

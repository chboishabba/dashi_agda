module DASHI.Governance.BoloBoloComparatorEvidenceAtlasExact where

open import DASHI.Core.Prelude

import DASHI.Core.CriticalRelationalGrammarSourceRegistryExact as Registry
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- REAL-WORLD COMPARATOR ATLAS FOR THE BOLO'BOLO COUNTERFACTUAL.
--
-- These cases are not treated as implementations of p.m.'s design.  They are
-- independent empirical / historical comparators that pay different pieces of
-- the calibration problem.  Structural similarity never collapses provenance.
------------------------------------------------------------------------

data ComparatorRole : Set where
  sameContextInterruptedTransition : ComparatorRole
  nestedParticipatoryBudgeting : ComparatorRole
  durableCooperativeFederation : ComparatorRole
  comparativePolycentricCoordination : ComparatorRole
  localSelfGovernancePremise : ComparatorRole

record ComparatorEvidenceCase : Set where
  constructor comparatorEvidenceCase
  field
    source : Registry.SourceReference
    role : ComparatorRole
    nestedDecisionCentersPresent : Bool
    explicitDelegationOrRepresentationPresent : Bool
    localAutonomyRetained : Bool
    verticalCoordinationPresent : Bool
    horizontalCoordinationPresent : Bool
    sameContextFlatToNestedTransitionPresent : Bool
    comparativeCoordinationOutcomePresent : Bool
    directBoloCostBoundPaid : Bool
    boundedRole : String

open ComparatorEvidenceCase public

holmes2023Source : Registry.SourceReference
holmes2023Source = Registry.source-reference
  "Marisa Holmes"
  "Organizing Occupy Wall Street: This is Just Practice"
  "Palgrave Macmillan Singapore"
  2023
  "10.1007/978-981-19-8947-6"
  "participant-organizer retrospective using primary OWS records"
  "source for the creation and early operation of the OWS Spokes Council as a scaling response using working-group/caucus spokes; not a randomized comparison or a bolo cost estimate"

portoAlegre2009Source : Registry.SourceReference
portoAlegre2009Source = Registry.source-reference
  "Enriqueta Aragones and Santiago Sanchez-Pages"
  "A theory of participatory democracy based on the real case of Porto Alegre"
  "European Economic Review 53(1):56-72"
  2009
  "10.1016/j.euroecorev.2008.09.006"
  "formal model grounded in the Porto Alegre participatory-budgeting case"
  "source for the nested regional/thematic assembly -> delegate forum -> participatory-budgeting council architecture and costly participation framing; majority-rule urban budgeting is not OWS consensus or bolo'bolo"

mondragon2023Source : Registry.SourceReference
mondragon2023Source = Registry.source-reference
  "Oier Imaz; Fred Freundlich; Aritz Kanpandegi"
  "The Governance of Multistakeholder Cooperatives in Mondragon: The Evolving Relationship among Purpose, Structure and Process"
  "Humanistic Governance in Democratic Organizations, pp. 285-330"
  2023
  "10.1007/978-3-031-17403-2_10"
  "open-access cooperative-governance case study"
  "source for multi-level cooperative governance, local cooperative authority, representative Congress/area/division bodies, communication/reporting structures and voluntary membership/exit; not a direct deliberative-cost experiment"

pahlWostlKnieper2023Source : Registry.SourceReference
pahlWostlKnieper2023Source = Registry.source-reference
  "Claudia Pahl-Wostl and Christian Knieper"
  "Pathways towards improved water governance: The role of polycentric governance systems and vertical and horizontal coordination"
  "Environmental Science & Policy 144:151-161"
  2023
  "10.1016/j.envsci.2023.03.011"
  "26-case comparative QCA plus in-depth water-governance studies"
  "comparative evidence that decentralisation plus horizontal and vertical coordination is associated with effective coordination while fragmented and centralized-uncoordinated regimes perform poorly; domain-specific and not a bolo cost coefficient"

ostromLamLee1994Source : Registry.SourceReference
ostromLamLee1994Source = Registry.source-reference
  "Elinor Ostrom; Wai Fung Lam; Myungsuk Lee"
  "The Performance of Self-Governing Irrigation Systems in Nepal"
  "Human Systems Management 13(3):197-207"
  1994
  "10.3233/HSM-1994-13305"
  "comparative common-pool-resource governance study"
  "evidence that farmer-managed irrigation systems in the studied Nepal sample tended to outperform state-operated systems on average; supports a local self-governance premise only, not nested federation overhead"

owsSpokesComparator : ComparatorEvidenceCase
owsSpokesComparator = comparatorEvidenceCase
  holmes2023Source
  sameContextInterruptedTransition
  true true true true true true false false
  "closest same-movement flat-to-nested structural transition; strong design relevance but confounded by time, membership/issue changes, rapid organizational learning and the November 2011 eviction"

portoAlegreComparator : ComparatorEvidenceCase
portoAlegreComparator = comparatorEvidenceCase
  portoAlegre2009Source
  nestedParticipatoryBudgeting
  true true true true true false false false
  "large urban nested participation architecture with regional/thematic assemblies, delegate forums and a council; useful for delegation and multi-level participation structure, not a same-rule or same-context cost estimate"

mondragonComparator : ComparatorEvidenceCase
mondragonComparator = comparatorEvidenceCase
  mondragon2023Source
  durableCooperativeFederation
  true true true true true false false false
  "durable federation with bottom-level cooperative authority, higher representative bodies, recurrent reporting and voluntary membership/exit; useful for institutional feasibility and boundary/delegation design, not direct consensus burden"

polycentricWaterComparator : ComparatorEvidenceCase
polycentricWaterComparator = comparatorEvidenceCase
  pahlWostlKnieper2023Source
  comparativePolycentricCoordination
  true false true true true false true false
  "26-case comparative evidence directly relevant to the conjunction decentralisation + coordination; outcome is coordination performance in water governance, not a transferable bolo cost bound"

nepalIrrigationComparator : ComparatorEvidenceCase
nepalIrrigationComparator = comparatorEvidenceCase
  ostromLamLee1994Source
  localSelfGovernancePremise
  false false true false true false true false
  "supports the possibility that local self-governance can outperform agency management in a specific resource domain; does not identify upper-level federation or delegation overhead"

canonicalComparatorEvidenceCases : List ComparatorEvidenceCase
canonicalComparatorEvidenceCases =
  owsSpokesComparator
  ∷ portoAlegreComparator
  ∷ mondragonComparator
  ∷ polycentricWaterComparator
  ∷ nepalIrrigationComparator
  ∷ []

record ComparatorEvidenceBoundary : Set where
  constructor comparatorEvidenceBoundary
  field
    comparatorSimilarityMakesCaseABoloImplementation : Bool
    crossCaseOutcomeAutomaticallyTransfersToTargetBolo : Bool
    sameContextOWSTransitionIsRandomizedExperiment : Bool
    polycentricWaterPerformanceIsBoloCostCoefficient : Bool
    mondragonDurabilityProvesConsensusEfficiency : Bool
    portoAlegreMajorityRuleEqualsOWSConsensus : Bool
    nepalLocalSelfGovernancePaysFederationOverhead : Bool
    comparatorsMayConstrainDesignAndPlausibility : Bool

open ComparatorEvidenceBoundary public

canonicalComparatorEvidenceBoundary : ComparatorEvidenceBoundary
canonicalComparatorEvidenceBoundary =
  comparatorEvidenceBoundary false false false false false false false true

canonicalComparatorEvidenceReceipt : GenericReceipt.GenericReceipt
canonicalComparatorEvidenceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo real-world governance comparator atlas"
    "DASHI.Governance.BoloBoloComparatorEvidenceAtlasExact"
    "canonicalComparatorEvidenceCases / canonicalComparatorEvidenceBoundary"
    "adds independent real-world comparators spanning the OWS Spokes Council transition, Porto Alegre participatory budgeting, Mondragon multi-level cooperative governance, a 26-case polycentric water-governance comparison and Nepal farmer-managed irrigation, each with a bounded evidentiary role"
    "none is re-authored as p.m.'s design or promoted directly to target bolo cost bounds; rule systems, domains, contexts and outcome measures remain explicit transfer barriers"
    "agda -i . DASHI/Governance/BoloBoloComparatorEvidenceAtlasRegression.agda"

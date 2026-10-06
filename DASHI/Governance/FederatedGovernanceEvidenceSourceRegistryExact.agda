module DASHI.Governance.FederatedGovernanceEvidenceSourceRegistryExact where

open import DASHI.Core.Prelude

import DASHI.Core.CriticalRelationalGrammarSourceRegistryExact as Registry
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Canonical bibliography / bounded-role registry for the evidence tranche.
--
-- Reuses the existing generic SourceReference type. Registry membership fixes
-- bibliographic identity and bounded evidentiary role only; it creates no
-- theorem authority and does not merge sources that discuss similar themes.
------------------------------------------------------------------------

boloBolo30thSource : Registry.SourceReference
boloBolo30thSource = Registry.source-reference
  "p.m."
  "bolo'bolo"
  "Autonomedia / Ardent Press, 30th Anniversary Edition"
  2011
  "ISBN 9781570272417"
  "primary political-design / utopian text"
  "primary source for proposed kana/bolo/tega institutional scales, bottom-up coordination language, and the 2011 transition caution; not empirical optimality evidence"

bookchinConfederalismSource : Registry.SourceReference
bookchinConfederalismSource = Registry.source-reference
  "Murray Bookchin"
  "The Meaning of Confederalism"
  "Green Perspectives 20"
  1990
  "no DOI asserted"
  "primary political theory essay"
  "primary source for face-to-face assemblies, mandated/recallable delegates, policy/administration distinction, bottom-up confederal coordination and intercommunity interdependence"

min2015Source : Registry.SourceReference
min2015Source = Registry.source-reference
  "Seong-Jae Min"
  "Occupy Wall Street and Deliberative Decision-Making: Translating Theory to Practice"
  "Communication, Culture & Critique 8(1):73-89"
  2015
  "10.1111/cccr.12074"
  "participant-observer social-movement study"
  "evidence for meaningful deliberative-democratic procedural practice and citizenship development; not a universal scalability theorem"

savio2015Source : Registry.SourceReference
savio2015Source = Registry.source-reference
  "Gianmarco Savio"
  "Coordination outside formal organization: consensus-based decision-making and occupation in the Occupy Wall Street movement"
  "Contemporary Justice Review 18(1):42-54"
  2015
  "10.1080/10282580.2015.1005509"
  "ethnographic social-movement study"
  "evidence that mass assemblies and occupation could operate as coordination mechanisms in OWS; not universal superiority evidence"

hammond2013Source : Registry.SourceReference
hammond2013Source = Registry.source-reference
  "John L. Hammond"
  "The significance of space in Occupy Wall Street"
  "Interface: a journal for and about social movements 5(2):499-524"
  2013
  "no DOI asserted"
  "peer-reviewed movement study"
  "evidence that consensus/openness could be cumbersome and large-assembly governance burdensome; not a quantitative group-size law"

pollettaHoban2016Source : Registry.SourceReference
pollettaHoban2016Source = Registry.source-reference
  "Francesca Polletta and Katt Hoban"
  "Why Consensus?"
  "Journal of Social and Political Psychology 4(1)"
  2016
  "10.5964/jspp.v4i1.524"
  "interview-based social-movement study"
  "evidence that activists pragmatically adapted consensus, including committee devolution and voting in some settings; not a uniform account of all Occupy camps"

kinnaPrichard2019ArchiveSource : Registry.SourceReference
kinnaPrichard2019ArchiveSource = Registry.source-reference
  "Ruth Kinna and Alex Prichard"
  "Archival and workshop materials relating to constitutional practices in grass roots anarchistic organisations 2011-2018"
  "UK Data Service ReShare"
  2019
  "10.5255/UKDA-SN-853247"
  "open archival data collection"
  "source identity for the open OccupyFiles.zip bundle containing General Assembly minutes from Occupy Wall Street, Occupy London St Paul's and Occupy Oakland; corpus availability does not imply complete participant-issue coding"

hwangGuynes1994Source : Registry.SourceReference
hwangGuynes1994Source = Registry.source-reference
  "Hsin-Ginn Hwang and Jan L. Guynes"
  "The effect of group size on group performance in computer-supported decision making"
  "Information & Management 26(4):189-198"
  1994
  "10.1016/0378-7206(94)90092-2"
  "randomized computer-supported group-decision experiment"
  "general evidence that 9-person groups took longer than 3-person groups and generated more alternatives in the studied setting; not direct Occupy evidence or a universal law"

millerVanberg2015Source : Registry.SourceReference
millerVanberg2015Source = Registry.source-reference
  "Luis Miller and Christoph Vanberg"
  "Group size and decision rules in legislative bargaining"
  "European Journal of Political Economy 37:288-302"
  2015
  "10.1016/j.ejpoleco.2014.09.005"
  "experimental legislative-bargaining study"
  "general evidence that larger groups and unanimity increased costly delay in the studied bargaining game; not a direct model of horizontal Occupy consensus"

mckoyEtAl2012Source : Registry.SourceReference
mckoyEtAl2012Source = Registry.source-reference
  "Marques McKoy; Samantha Spitler; Kelsey Zuchegno; Alana Enslein; Stephen Hobbs; Robert A. Reeves; Tadd B. Patton; W. F. Lawless"
  "An Experimental Physiological Approach to Group Decision Making: Consensus Rule vs Majority Rule"
  "Procedia Technology 5:475-480"
  2012
  "10.1016/j.protcy.2012.09.052"
  "small-group laboratory comparison of consensus and majority rules"
  "general evidence about discussion/engagement and decision-time differences with task-dependent follow-up; not an Occupy rule-effect estimate"

luYuanMcLeod2012Source : Registry.SourceReference
luYuanMcLeod2012Source = Registry.source-reference
  "Li Lu; Y. Connie Yuan; Poppy Lauretta McLeod"
  "Twenty-Five Years of Hidden Profiles in Group Decision Making: A Meta-Analysis"
  "Personality and Social Psychology Review 16(1):54-75"
  2012
  "10.1177/1088868311417243"
  "meta-analysis of hidden-profile group-decision studies"
  "general evidence that group size and information structure moderate information pooling and decision quality; not an Occupy coordination-cost coefficient"

ipccSR15Source : Registry.SourceReference
ipccSR15Source = Registry.source-reference
  "Intergovernmental Panel on Climate Change"
  "Global Warming of 1.5 C"
  "IPCC Special Report SR1.5"
  2018
  "ISBN 978-92-9169-151-7; no DOI asserted for report as a whole"
  "intergovernmental scientific assessment"
  "primary assessment source for rapid system transitions, mitigation synergies/trade-offs, low-energy-demand pathway findings and implementation-capacity statements; not a political-governance endorsement"

canonicalGovernanceEvidenceSources : List Registry.SourceReference
canonicalGovernanceEvidenceSources =
  boloBolo30thSource
  ∷ bookchinConfederalismSource
  ∷ min2015Source
  ∷ savio2015Source
  ∷ hammond2013Source
  ∷ pollettaHoban2016Source
  ∷ kinnaPrichard2019ArchiveSource
  ∷ hwangGuynes1994Source
  ∷ millerVanberg2015Source
  ∷ mckoyEtAl2012Source
  ∷ luYuanMcLeod2012Source
  ∷ ipccSR15Source
  ∷ []

record GovernanceEvidenceRegistryBoundary : Set where
  constructor governanceEvidenceRegistryBoundary
  field
    registryEntryCreatesTheoremAuthority : Bool
    sameGovernanceThemeCollapsesProvenance : Bool
    sourceAgreementMakesSourcesIndependentReplications : Bool
    sourceRoleMayExceedBoundedRole : Bool
    bibliographicIdentitySeparatedFromDerivedBridge : Bool

open GovernanceEvidenceRegistryBoundary public

canonicalGovernanceEvidenceRegistryBoundary : GovernanceEvidenceRegistryBoundary
canonicalGovernanceEvidenceRegistryBoundary =
  governanceEvidenceRegistryBoundary
    false
    false
    false
    false
    true

canonicalGovernanceEvidenceSourceRegistryReceipt : GenericReceipt.GenericReceipt
canonicalGovernanceEvidenceSourceRegistryReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "federated governance evidence source registry"
    "DASHI.Governance.FederatedGovernanceEvidenceSourceRegistryExact"
    "canonicalGovernanceEvidenceRegistryBoundary"
    "pins canonical bibliographic identities and bounded roles for bolo'bolo, Bookchin confederalism, Occupy studies and archival data, four external quantitative group-decision sources, and IPCC SR1.5 using the existing generic SourceReference carrier"
    "registry membership creates no theorem authority, structural similarity does not merge provenance, and external group-decision experiments do not become Occupy evidence merely because they share decision-process variables"
    "agda -i . DASHI/Governance/FederatedGovernanceEvidenceSourceRegistryRegression.agda"

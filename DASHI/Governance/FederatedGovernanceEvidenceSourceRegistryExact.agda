module DASHI.Governance.FederatedGovernanceEvidenceSourceRegistryExact where

open import DASHI.Core.Prelude

import DASHI.Core.CriticalRelationalGrammarSourceRegistryExact as Registry
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Canonical bibliography / bounded-role registry for the evidence tranche.
--
-- Reuses the existing generic SourceReference type.  Registry membership fixes
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
    "pins canonical bibliographic identities and bounded evidentiary roles for bolo'bolo, Bookchin confederalism, four Occupy studies, the Kinna-Prichard Occupy archival corpus and IPCC SR1.5 using the existing generic SourceReference carrier"
    "registry membership creates no theorem authority, structural similarity does not merge provenance, and agreement does not manufacture evidentiary independence"
    "agda -i . DASHI/Governance/FederatedGovernanceEvidenceSourceRegistryRegression.agda"

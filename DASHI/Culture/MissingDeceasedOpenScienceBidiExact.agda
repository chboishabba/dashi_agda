module DASHI.Culture.MissingDeceasedOpenScienceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.OpenScienceKnowledgeReleaseBidiExact as O
import DASHI.Core.ViewpointProvenanceBidiExact as V
import DASHI.Culture.MissingDeceasedViewpointEvidenceExact as VE

------------------------------------------------------------------------
-- EMPIRICAL OPEN-SCIENCE / KNOWLEDGE-RELEASE FIXTURE
--
-- Behaviour and belief are deliberately separate.  A paper, patent, public
-- technical profile or institutional release can establish dissemination
-- behaviour without establishing an anti-secrecy ideology.
------------------------------------------------------------------------

amyPublicTechnicalEducation : O.OpenScienceReceipt
amyPublicTechnicalEducation = O.open-science-receipt
  "Amy Eskridge"
  O.publicTechnicalEducation
  O.behaviour
  O.positive
  O.publicArtifact
  "2018 HAL5 public anti-gravity presentation; archived 2020 Zoom transcript"
  "Eskridge publicly presented technical/historical material on gravity modification and unconventional propulsion."

amyTransparencyAdvocacy : O.OpenScienceReceipt
amyTransparencyAdvocacy = O.open-science-receipt
  "Amy Eskridge"
  O.disclosureOrTransparencyAdvocacy
  O.explicitBelief
  O.positive
  O.selfStatement
  "Archived 2020 Amy Eskridge Zoom transcript"
  "Eskridge says the institute was deliberately public-facing and intended to disclose anti-gravity work rather than leave it privately suppressible."

amySuppressionCritique : O.OpenScienceReceipt
amySuppressionCritique = O.open-science-receipt
  "Amy Eskridge"
  O.suppressionOrSecrecyCritique
  O.explicitBelief
  O.positive
  O.selfStatement
  "Archived 2020 Amy Eskridge Zoom transcript"
  "Eskridge explicitly criticizes suppression/private containment of unconventional-propulsion knowledge and frames public visibility as protective."

amyBoundaryCrossingUnproved : O.OpenScienceReceipt
amyBoundaryCrossingUnproved = O.open-science-receipt
  "Amy Eskridge"
  O.restrictedToPublicBoundaryCrossing
  O.behaviour
  O.unknown
  O.selfStatement
  "Archived 2020 Amy Eskridge Zoom transcript plus public presentations"
  "Her disclosure advocacy and public presentations do not by themselves prove that one same knowledge object was previously restricted and then released. O6 remains open pending both sides of the boundary."

loureiroPublicPublication : O.OpenScienceReceipt
loureiroPublicPublication = O.open-science-receipt
  "Nuno F. G. Loureiro"
  O.publicTechnicalPublication
  O.behaviour
  O.positive
  O.publicArtifact
  "Loureiro et al., Viriato, Computer Physics Communications 206 (2016), DOI 10.1016/j.cpc.2016.05.004; MIT/PSFC publication record"
  "Loureiro extensively published technically substantive plasma/reconnection/fusion work in public scientific channels. This is dissemination behaviour, not evidence of an anti-secrecy ideology."

loureiroPublicEducation : O.OpenScienceReceipt
loureiroPublicEducation = O.open-science-receipt
  "Nuno F. G. Loureiro"
  O.publicTechnicalEducation
  O.behaviour
  O.positive
  O.publicArtifact
  "Public interviews/talks including 45 Graus episode 119 and MIT public-facing fusion material"
  "Loureiro publicly explained fusion, reconnection and burning-plasma research to non-specialist audiences."

loureiroBoundaryCrossingUnknown : O.OpenScienceReceipt
loureiroBoundaryCrossingUnknown = O.open-science-receipt
  "Nuno F. G. Loureiro"
  O.restrictedToPublicBoundaryCrossing
  O.behaviour
  O.unknown
  O.publicArtifact
  "Publications/talks located to date"
  "No same-object receipt located showing that material previously restricted/private was later released publicly by Loureiro."

leblancInstitutionalRelease : O.OpenScienceReceipt
leblancInstitutionalRelease = O.open-science-receipt
  "Joshua Kyle LeBlanc"
  O.publicTechnicalPublication
  O.institutionalParticipation
  O.positive
  O.institutionalRelease
  "NASA NTRS 20250008475, NASA 40 kW Fission Surface Power I&C Technology Development Path"
  "LeBlanc is a named author/technical lead on publicly released NASA FSP/SNP I&C material. This establishes participation in public dissemination, not a personal transparency ideology."

leblancBoundaryCrossingUnknown : O.OpenScienceReceipt
leblancBoundaryCrossingUnknown = O.open-science-receipt
  "Joshua Kyle LeBlanc"
  O.restrictedToPublicBoundaryCrossing
  O.institutionalParticipation
  O.unknown
  O.institutionalRelease
  "NASA NTRS material located to date"
  "A public-use NASA release does not establish that the same content was previously restricted or that LeBlanc personally drove declassification/release."

rezaPatentDisclosure : O.OpenScienceReceipt
rezaPatentDisclosure = O.open-science-receipt
  "Monica Jacinto / Monica Reza"
  O.publicTechnicalPublication
  O.behaviour
  O.positive
  O.publicArtifact
  "US20040208777A1 / US10/769,195, Burn-resistant and high tensile strength metal alloys"
  "Named inventorship on a public patent establishes public technical disclosure of the claimed alloy invention. Patent publication does not establish anti-secrecy belief or release of previously restricted knowledge."

rezaBoundaryCrossingUnknown : O.OpenScienceReceipt
rezaBoundaryCrossingUnknown = O.open-science-receipt
  "Monica Jacinto / Monica Reza"
  O.restrictedToPublicBoundaryCrossing
  O.behaviour
  O.unknown
  O.publicArtifact
  "Patent and public role records located to date"
  "No same-object prior-restriction plus public-release receipt has been located for Reza's technical work."

maiwaldPublicPublication : O.OpenScienceReceipt
maiwaldPublicPublication = O.open-science-receipt
  "Frank W. Maiwald"
  O.publicTechnicalPublication
  O.behaviour
  O.positive
  O.publicArtifact
  "JPL planetary mass-spectrometry publications and public FY23 SURP biosignature-action-spectroscopy material"
  "Maiwald's work appears in public scientific and institutional channels. This establishes dissemination behaviour only."

maiwaldBoundaryCrossingUnknown : O.OpenScienceReceipt
maiwaldBoundaryCrossingUnknown = O.open-science-receipt
  "Frank W. Maiwald"
  O.restrictedToPublicBoundaryCrossing
  O.behaviour
  O.unknown
  O.publicArtifact
  "Public publication/project sources located to date"
  "No evidence yet shows a same knowledge object moving from a genuinely restricted/private state into public circulation."

chavezPublicTechnicalEducation : O.OpenScienceReceipt
chavezPublicTechnicalEducation = O.open-science-receipt
  "Anthony Chavez"
  O.publicTechnicalEducation
  O.behaviour
  O.positive
  O.publicArtifact
  "Los Alamos National Security Science, Summer 2025 Engineering issue, Anthony Chavez profile"
  "Chavez publicly explained the engineer-physicist collaboration behind DARHT/Scorpius design work. This is a bounded public-education behaviour receipt."

chavezBoundaryCrossingUnknown : O.OpenScienceReceipt
chavezBoundaryCrossingUnknown = O.open-science-receipt
  "Anthony Chavez"
  O.restrictedToPublicBoundaryCrossing
  O.behaviour
  O.unknown
  O.publicArtifact
  "LANL public profile and programme material located to date"
  "No same-object evidence establishes release of previously restricted technical content."

mccaslandDisclosureParticipation : O.OpenScienceReceipt
mccaslandDisclosureParticipation = O.open-science-receipt
  "William N. McCasland"
  O.disclosureOrTransparencyAdvocacy
  O.institutionalParticipation
  O.unknown
  O.documentedParticipation
  "2016 Podesta/DeLonge email chain"
  "The correspondence supports participation in disclosure-related discussions, but not McCasland's own transparency position."

------------------------------------------------------------------------
-- Exact viewpoint -> open-science bridges for Amy only, where the old receipt
-- is already strong and the semantic relation is direct.
------------------------------------------------------------------------

amyDisclosureStrong : V.StrongViewpointClaim VE.amyDisclosure
amyDisclosureStrong = V.strong-viewpoint-claim refl (inj₁ refl)

amySecrecyStrong : V.StrongViewpointClaim VE.amySecrecyCritique
amySecrecyStrong = V.strong-viewpoint-claim refl (inj₁ refl)

amySensitiveDisclosureStrong : V.StrongViewpointClaim VE.amySensitiveDisclosure
amySensitiveDisclosureStrong = V.strong-viewpoint-claim refl (inj₁ refl)

amyDisclosureBridge :
  O.ViewpointToOpenScienceBridge VE.amyDisclosure amyTransparencyAdvocacy
amyDisclosureBridge = O.viewpoint-to-open-science-bridge
  refl
  O.uapDisclosureSupportsTransparency
  amyDisclosureStrong
  "Same-person direct statement: disclosure support is treated as a child of the transparency-advocacy parent axis."

amySecrecyBridge :
  O.ViewpointToOpenScienceBridge VE.amySecrecyCritique amySuppressionCritique
amySecrecyBridge = O.viewpoint-to-open-science-bridge
  refl
  O.secrecyCritiqueSupportsOpenCritique
  amySecrecyStrong
  "Same-person direct statement: secrecy/suppression critique maps to the open-science anti-suppression axis."

amySensitiveDisclosureBridge :
  O.ViewpointToOpenScienceBridge VE.amySensitiveDisclosure amyTransparencyAdvocacy
amySensitiveDisclosureBridge = O.viewpoint-to-open-science-bridge
  refl
  O.willingDisclosureSupportsTransparency
  amySensitiveDisclosureStrong
  "Same-person direct statement: willingness to disclose sensitive technical material supports transparency advocacy, not O6 boundary crossing by itself."

------------------------------------------------------------------------
-- Strong behaviour/posture receipts.  Note that institutional participation
-- can be source-backed while still failing to establish personal ideology.
------------------------------------------------------------------------

amyTransparencyStrong : O.StrongOpenScienceClaim amyTransparencyAdvocacy
amyTransparencyStrong = O.strong-open-science-claim refl (inj₁ refl)

amySuppressionStrong : O.StrongOpenScienceClaim amySuppressionCritique
amySuppressionStrong = O.strong-open-science-claim refl (inj₁ refl)

loureiroPublicationStrong : O.StrongOpenScienceClaim loureiroPublicPublication
loureiroPublicationStrong = O.strong-open-science-claim refl (inj₂ (inj₁ refl))

leblancReleaseStrong : O.StrongOpenScienceClaim leblancInstitutionalRelease
leblancReleaseStrong = O.strong-open-science-claim refl (inj₂ (inj₂ (inj₁ refl)))

rezaPatentStrong : O.StrongOpenScienceClaim rezaPatentDisclosure
rezaPatentStrong = O.strong-open-science-claim refl (inj₂ (inj₁ refl))

maiwaldPublicationStrong : O.StrongOpenScienceClaim maiwaldPublicPublication
maiwaldPublicationStrong = O.strong-open-science-claim refl (inj₂ (inj₁ refl))

chavezEducationStrong : O.StrongOpenScienceClaim chavezPublicTechnicalEducation
chavezEducationStrong = O.strong-open-science-claim refl (inj₂ (inj₁ refl))

------------------------------------------------------------------------
-- Reverse obligations: this is where the selection hypothesis has to pay for
-- stronger claims, especially O6 restricted -> public transfer.
------------------------------------------------------------------------

amyO6PriorRestriction : O.OpenScienceReverseObligation
amyO6PriorRestriction = O.open-science-reverse-obligation
  "Amy Eskridge"
  O.priorRestrictionReceipt
  "authenticated source showing that one exact technical object was actually restricted/private before public release"
  "the prior-state half of an O6 boundary-crossing claim"
  "the truth of the technical claim, motive, targeting, or perpetration"

amyO6SameObject : O.OpenScienceReverseObligation
amyO6SameObject = O.open-science-reverse-obligation
  "Amy Eskridge"
  O.sameKnowledgeObjectWeld
  "versioned document, correspondence, release record or other same-object provenance joining restricted and public forms"
  "an actual restricted-to-public knowledge transfer"
  "why the transfer occurred or who reacted to it"

mccaslandOwnPosition : O.OpenScienceReverseObligation
mccaslandOwnPosition = O.open-science-reverse-obligation
  "William N. McCasland"
  O.disclosureAdvocacyReceipt
  "McCasland-authored statement, authenticated correspondence or direct contemporaneous testimony establishing his own transparency/disclosure position"
  "personal open-science/disclosure posture"
  "belief merely from participation in another person's disclosure network"

loureiroOpenArtifact : O.OpenScienceReverseObligation
loureiroOpenArtifact = O.open-science-reverse-obligation
  "Nuno F. G. Loureiro"
  O.openArtifactReceipt
  "versioned public source repository, data archive, code release or explicit open-methods record attributable to Loureiro"
  "O2 open-code/data/methods behaviour"
  "anti-secrecy belief or O6 restricted-to-public transfer"

rosterOpenScienceControls : O.OpenScienceReverseObligation
rosterOpenScienceControls = O.open-science-reverse-obligation
  "missing/deceased technical roster"
  O.matchedOpenScienceControls
  "pre-registered matched peers scored on the same O1-O6 rubric before outcome comparison"
  "whether open-science behaviour/posture is actually enriched in the roster"
  "causal selection, actor identity, or event attribution"

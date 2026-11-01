module DASHI.Culture.MissingDeceasedViewpointEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ViewpointProvenanceBidiExact as V

amyDisclosure : V.ViewpointReceipt
amyDisclosure = V.viewpoint-receipt
  "Amy Eskridge"
  V.uapDisclosureSupport
  V.positive
  V.selfStated
  "Archived 2020 Amy Eskridge Zoom transcript; Blocked Epistemology archive"
  "Eskridge says she created the institute as a public-facing vehicle to disclose anti-gravity technology and explicitly contrasts public visibility with private suppression."

amySuppressedPropulsion : V.ViewpointReceipt
amySuppressedPropulsion = V.viewpoint-receipt
  "Amy Eskridge"
  V.suppressedOrExoticPropulsionBelief
  V.positive
  V.selfStated
  "Archived 2020 Amy Eskridge Zoom transcript; 2018 HAL5 anti-gravity presentation context"
  "Eskridge discusses anti-gravity as real technology, says prior discoveries had been suppressed, and frames disclosure as necessary."

amySecrecyCritique : V.ViewpointReceipt
amySecrecyCritique = V.viewpoint-receipt
  "Amy Eskridge"
  V.secrecyOrClassificationCritique
  V.positive
  V.selfStated
  "Archived 2020 Amy Eskridge Zoom transcript"
  "Eskridge explicitly criticizes private suppression and says public disclosure/visibility was protective."

amySensitiveDisclosure : V.ViewpointReceipt
amySensitiveDisclosure = V.viewpoint-receipt
  "Amy Eskridge"
  V.willingSensitiveTechnicalDisclosure
  V.positive
  V.selfStated
  "Archived 2020 Amy Eskridge Zoom transcript"
  "Eskridge states that the institute exists as a public-facing disclosure platform for anti-gravity work."

amyHiddenCapability : V.ViewpointReceipt
amyHiddenCapability = V.viewpoint-receipt
  "Amy Eskridge"
  V.hiddenMajorCapabilityBelief
  V.positive
  V.selfStated
  "Archived 2020 Amy Eskridge Zoom transcript"
  "Eskridge describes anti-gravity technology as repeatedly discovered and suppressed and discusses undisclosed technical capability."

loureiroFusionExpectation : V.ViewpointReceipt
loureiroFusionExpectation = V.viewpoint-receipt
  "Nuno F. G. Loureiro"
  V.transformativeFusionEnergyExpectation
  V.positive
  V.selfStated
  "45 Graus episode 119 transcript; MIT News profile, 1 May 2024"
  "Loureiro publicly discusses fusion as a future major energy source and describes the coming burning-plasma era as a new phase for fusion."

mccaslandDisclosureParticipation : V.ViewpointReceipt
mccaslandDisclosureParticipation = V.viewpoint-receipt
  "William N. McCasland"
  V.uapDisclosureSupport
  V.unknown
  V.contemporaneousDocumentedParticipation
  "2016 Podesta/DeLonge email chain documenting McCasland invitation/participation; DeLonge's follow-up attribution"
  "The email record supports participation in DeLonge/Podesta disclosure-related discussions. It does not by itself establish McCasland's own UAP belief or disclosure position; DeLonge's claim that McCasland was not really a skeptic remains attribution."

chavezViewpointUnknown : V.ViewpointReceipt
chavezViewpointUnknown = V.viewpoint-receipt
  "Anthony Chavez"
  V.secrecyOrClassificationCritique
  V.unknown
  V.selfStated
  "LANL National Security Science, Summer 2025 profile"
  "Located first-person quote concerns collaborative engineering at DARHT/Scorpius, not secrecy, UAPs, suppressed technology, or disclosure."

leblancViewpointUnknown : V.ViewpointReceipt
leblancViewpointUnknown = V.viewpoint-receipt
  "Joshua Kyle LeBlanc"
  V.transformativeFusionEnergyExpectation
  V.unknown
  V.selfStated
  "NASA NTRS 20250008475"
  "Located role/publication evidence establishes space-nuclear I&C responsibility but does not establish a broader public disclosure or transformative-energy viewpoint."

maiwaldViewpointUnknown : V.ViewpointReceipt
maiwaldViewpointUnknown = V.viewpoint-receipt
  "Frank W. Maiwald"
  V.hiddenMajorCapabilityBelief
  V.unknown
  V.selfStated
  "JPL institutional/publication records and obituary material located to date"
  "No first-person source located in this pass establishing UAP disclosure, suppressed technology, secrecy critique, or hidden-capability belief."

rezaViewpointUnknown : V.ViewpointReceipt
rezaViewpointUnknown = V.viewpoint-receipt
  "Monica Jacinto / Monica Reza"
  V.suppressedOrExoticPropulsionBelief
  V.unknown
  V.selfStated
  "Patent and role sources located to date"
  "No first-person source located in this pass establishing suppressed/exotic-propulsion belief, secrecy critique, UAP disclosure, or hidden-capability belief."

mccaslandParticipationDoesNotPromoteBelief :
  V.ParticipationWithoutBelief mccaslandDisclosureParticipation
mccaslandParticipationDoesNotPromoteBelief =
  V.participation-without-belief refl refl

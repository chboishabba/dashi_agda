module DASHI.Culture.MissingDeceasedOpenScienceAcquisition2026_09_05Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.OpenScienceKnowledgeReleaseBidiExact as O
import DASHI.Core.OpenScienceArtifactGranularityBidiExact as A

------------------------------------------------------------------------
-- EVIDENCE ACQUISITION SNAPSHOT — 2026-09-05
------------------------------------------------------------------------

loureiroViriatoMethods : A.ArtifactExposureReceipt
loureiroViriatoMethods = A.artifact-exposure-receipt
  "Nuno F. G. Loureiro / Viriato"
  A.publicMethodDescription
  "Loureiro et al., Computer Physics Communications 206 (2016), DOI 10.1016/j.cpc.2016.05.004; MIT PSFC profile"
  "Public sources describe Viriato's reduced-gyrokinetic formulation, numerical architecture and algorithms."

loureiroViriatoBenchmarks : A.ArtifactExposureReceipt
loureiroViriatoBenchmarks = A.artifact-exposure-receipt
  "Nuno F. G. Loureiro / Viriato"
  A.publicBenchmarkDisclosure
  "Loureiro et al. 2016; APS DPP abstract"
  "Public sources report extensive linear/nonlinear benchmarks and numerical tests."

loureiroMethodsWithoutSourceRelease :
  A.MethodDisclosureWithoutSourceRelease loureiroViriatoMethods loureiroViriatoBenchmarks
loureiroMethodsWithoutSourceRelease =
  A.method-disclosure-without-source-release refl refl true refl

loureiroSourceRelease : A.ArtifactExposureReceipt
loureiroSourceRelease = A.artifact-exposure-receipt
  "Nuno F. G. Loureiro / Viriato"
  A.unresolvedArtifactExposure
  "Public search through 2026-09-05"
  "No sufficiently strong first-party/versioned repository plus licence receipt was located for the Viriato source tree. Do not promote open-source release from method disclosure alone."

leblancPublicUseRelease : O.OpenScienceReceipt
leblancPublicUseRelease = O.open-science-receipt
  "Joshua Kyle LeBlanc"
  O.publicTechnicalPublication
  O.institutionalParticipation
  O.positive
  O.institutionalRelease
  "NASA NTRS 20250008475; Copyright: Public Use Permitted; NASA technical review"
  "The FSP I&C presentation was publicly released and archived. This does not establish that the same material was previously classified/restricted or that LeBlanc personally initiated release."

leblancO6StillUnknown : O.OpenScienceReceipt
leblancO6StillUnknown = O.open-science-receipt
  "Joshua Kyle LeBlanc"
  O.restrictedToPublicBoundaryCrossing
  O.institutionalParticipation
  O.unknown
  O.institutionalRelease
  "NASA NTRS 20250008475"
  "Public-use status supplies the public side only. A prior restriction/declassification record and same-object weld are still missing."

mccaslandDisclosureParticipation : O.OpenScienceReceipt
mccaslandDisclosureParticipation = O.open-science-receipt
  "William N. McCasland"
  O.disclosureOrTransparencyAdvocacy
  O.institutionalParticipation
  O.unknown
  O.documentedParticipation
  "2016 DeLonge/Podesta email chain; meeting invitation includes McCasland"
  "Contemporaneous email evidence supports participation in a disclosure-related meeting/network. It does not establish McCasland's own disclosure belief or any actual release of restricted material."

amyO6StillUnknown : O.OpenScienceReceipt
amyO6StillUnknown = O.open-science-receipt
  "Amy Eskridge"
  O.restrictedToPublicBoundaryCrossing
  O.explicitBelief
  O.unknown
  O.selfStatement
  "Archived 2020 Zoom transcript and public HAL5 material"
  "Eskridge explicitly advocates public disclosure and claims suppression, but a same-object prior-restricted-state plus later public release has not yet been located."

record CurrentOpenScienceAcquisitionState : Set where
  constructor current-open-science-acquisition-state
  field
    loureiroMethodDisclosureSupported : Bool
    loureiroMethodDisclosureSupportedIsTrue : loureiroMethodDisclosureSupported ≡ true
    loureiroSourceCodeReleaseEstablished : Bool
    loureiroSourceCodeReleaseEstablishedIsFalse : loureiroSourceCodeReleaseEstablished ≡ false
    leblancPublicReleaseEstablished : Bool
    leblancPublicReleaseEstablishedIsTrue : leblancPublicReleaseEstablished ≡ true
    leblancRestrictedToPublicEstablished : Bool
    leblancRestrictedToPublicEstablishedIsFalse : leblancRestrictedToPublicEstablished ≡ false
    mccaslandParticipationEstablished : Bool
    mccaslandParticipationEstablishedIsTrue : mccaslandParticipationEstablished ≡ true
    mccaslandPersonalDisclosureAdvocacyEstablished : Bool
    mccaslandPersonalDisclosureAdvocacyEstablishedIsFalse :
      mccaslandPersonalDisclosureAdvocacyEstablished ≡ false
    amyDisclosureAdvocacyEstablished : Bool
    amyDisclosureAdvocacyEstablishedIsTrue : amyDisclosureAdvocacyEstablished ≡ true
    amyRestrictedToPublicSameObjectEstablished : Bool
    amyRestrictedToPublicSameObjectEstablishedIsFalse :
      amyRestrictedToPublicSameObjectEstablished ≡ false

canonicalCurrentOpenScienceAcquisitionState : CurrentOpenScienceAcquisitionState
canonicalCurrentOpenScienceAcquisitionState = current-open-science-acquisition-state
  true refl
  false refl
  true refl
  false refl
  true refl
  false refl
  true refl
  false refl

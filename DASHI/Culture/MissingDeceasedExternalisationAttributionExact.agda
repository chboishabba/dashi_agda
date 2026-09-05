module DASHI.Culture.MissingDeceasedExternalisationAttributionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificWorkAttributionExact as A
import DASHI.Core.ExternalisationAttributionDiscriminationExact as D
import DASHI.Culture.MissingDeceasedTechnicalExternalisationExact as X

------------------------------------------------------------------------
-- LEBLANC / NASA FSP: shared multi-author public artifact
------------------------------------------------------------------------

fspSharedArtifact : D.SharedExternalisedArtifact
fspSharedArtifact = D.shared-externalised-artifact
  X.leblancFspExternalisation
  10
  "NASA NTRS 20250008475 names at least ten authors/contributors on the public presentation, including Robert Okojie, Teresa Benko, Tyler Steiner, Kaiser Aguirre, Christopher Barth, Dianne Ezell, Angel Martinez-Sanchez, Robert Bruckner, Joshua LeBlanc and Jarvis Caffrey."

leblancFspAttribution : A.ScientificWorkAttribution
leblancFspAttribution = A.scientific-work-attribution
  "Joshua Kyle LeBlanc"
  "NASA 40 kW Fission Surface Power I&C Technology Development Path"
  "NASA Fission Surface Power / Space Nuclear Propulsion I&C"
  A.namedAuthor
  A.primaryPublicationRecord
  "NASA NTRS 20250008475"
  "LeBlanc is a named author on a public NASA technical presentation. The artifact is jointly authored; authorship does not identify unique release agency."
  A.externalSourceOwner

leblancSharedExternalisation : D.PersonArtifactAttribution
leblancSharedExternalisation = D.person-artifact-attribution
  leblancFspAttribution
  fspSharedArtifact
  "The public externalisation is attributable to LeBlanc at named-author level, but the same artifact provides comparable public-externalisation evidence for multiple coauthors."

------------------------------------------------------------------------
-- REZA / JACINTO ALLOY PATENT: shared two-inventor public artifact
------------------------------------------------------------------------

rezaPatentSharedArtifact : D.SharedExternalisedArtifact
rezaPatentSharedArtifact = D.shared-externalised-artifact
  X.rezaPatentExternalisation
  2
  "US20040208777A1 names Monica Jacinto and Dallis Hardwick as inventors."

rezaPatentAttribution : A.ScientificWorkAttribution
rezaPatentAttribution = A.scientific-work-attribution
  "Monica Jacinto / Monica Reza"
  "Burn-resistant and high tensile strength metal alloys, US20040208777A1"
  "rocket-engine / high-temperature alloy development"
  A.namedInventor
  A.primaryPatentRecord
  "US20040208777A1 / US10/769,195"
  "The patent names Monica Jacinto as an inventor alongside Dallis Hardwick. Inventorship supports participation in the disclosed invention, not unique responsibility for making it public."
  A.externalSourceOwner

rezaSharedExternalisation : D.PersonArtifactAttribution
rezaSharedExternalisation = D.person-artifact-attribution
  rezaPatentAttribution
  rezaPatentSharedArtifact
  "The patent is a genuine public technical artifact, but its two-inventor structure blocks attribution of the release/externalisation decision uniquely to Reza from the patent record alone."

record CurrentSharedArtifactAssessment : Set where
  constructor current-shared-artifact-assessment
  field
    leblancPublicArtifactShared : Bool
    leblancPublicArtifactSharedIsTrue : leblancPublicArtifactShared ≡ true
    rezaPublicArtifactShared : Bool
    rezaPublicArtifactSharedIsTrue : rezaPublicArtifactShared ≡ true
    leblancUniqueReleaseAgencyEstablished : Bool
    leblancUniqueReleaseAgencyEstablishedIsFalse :
      leblancUniqueReleaseAgencyEstablished ≡ false
    rezaUniqueReleaseAgencyEstablished : Bool
    rezaUniqueReleaseAgencyEstablishedIsFalse :
      rezaUniqueReleaseAgencyEstablished ≡ false

canonicalCurrentSharedArtifactAssessment : CurrentSharedArtifactAssessment
canonicalCurrentSharedArtifactAssessment = current-shared-artifact-assessment
  true refl
  true refl
  false refl
  false refl

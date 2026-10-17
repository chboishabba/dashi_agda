module DASHI.Wikimedia.BH4ProteinWikimediaIdentityRegression where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.BH4ProteinWikimediaIdentityExact as Bio
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity

------------------------------------------------------------------------
-- Regression witnesses for the biology <-> Wikimedia bridge.
------------------------------------------------------------------------

geneQidCannotSilentlyBecomeProteinQid :
  Bio.WikimediaBiologyIdentityBoundary.geneQidMayBeUsedAsProteinQidWithoutP688P702Witness
    Bio.canonicalWikimediaBiologyIdentityBoundary
  ≡ false
geneQidCannotSilentlyBecomeProteinQid = refl

qidDoesNotCreateSequenceIdentity :
  Bio.WikimediaBiologyIdentityBoundary.qidCreatesProteinSequenceIdentity
    Bio.canonicalWikimediaBiologyIdentityBoundary
  ≡ false
qidDoesNotCreateSequenceIdentity = refl

wikipediaDoesNotCreateMechanisticEvidence :
  Bio.WikimediaBiologyIdentityBoundary.wikipediaNarrativeCreatesMechanisticEvidence
    Bio.canonicalWikimediaBiologyIdentityBoundary
  ≡ false
wikipediaDoesNotCreateMechanisticEvidence = refl

wikipediaCoverageDoesNotConfirmWholeGraph :
  Bio.WikimediaBiologyIdentityBoundary.wikipediaCoverageConfirmsKitzerowWholeGraph
    Bio.canonicalWikimediaBiologyIdentityBoundary
  ≡ false
wikipediaCoverageDoesNotConfirmWholeGraph = refl

p352IdentityDoesNotCreateFlux :
  Bio.WikimediaBiologyIdentityBoundary.exactP352CreatesMeasuredBH4Flux
    Bio.canonicalWikimediaBiologyIdentityBoundary
  ≡ false
p352IdentityDoesNotCreateFlux = refl

unresolvedProteinQidDoesNotMeanProteinAbsent :
  Bio.WikimediaBiologyIdentityBoundary.unresolvedProteinQidMeansProteinAbsent
    Bio.canonicalWikimediaBiologyIdentityBoundary
  ≡ false
unresolvedProteinQidDoesNotMeanProteinAbsent = refl

sprProteinQidSeedIsCurrent :
  Bio.proteinQid Bio.sprProteinSeed ≡ "Q409532"
sprProteinQidSeedIsCurrent = refl

thProteinQidSeedIsCurrent :
  Bio.proteinQid Bio.thProteinSeed ≡ "Q420766"
thProteinQidSeedIsCurrent = refl

mtorProteinQidSeedIsCurrent :
  Bio.proteinQid Bio.mtorProteinSeed ≡ "Q21115057"
mtorProteinQidSeedIsCurrent = refl

qdprGeneIdentityCannotCreateAuthority :
  Identity.externalIdentityCreatesAuthority Bio.qdprGeneQid ≡ false
qdprGeneIdentityCannotCreateAuthority = refl

module DASHI.Wikimedia.BH4ProteinWikimediaIdentityRegression where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.BH4ProteinWikimediaIdentityExact as Bio
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity

------------------------------------------------------------------------
-- Regression witnesses for the executed biology <-> Wikimedia acquisition.
------------------------------------------------------------------------

geneQidCannotSilentlyBecomeProteinQid :
  Bio.WikimediaBiologyIdentityBoundary.geneQidMayBeUsedAsProteinQidWithoutP688P702Witness
    Bio.canonicalWikimediaBiologyIdentityBoundary ≡ false
geneQidCannotSilentlyBecomeProteinQid = refl

qidDoesNotCreateSequenceIdentity :
  Bio.WikimediaBiologyIdentityBoundary.qidCreatesProteinSequenceIdentity
    Bio.canonicalWikimediaBiologyIdentityBoundary ≡ false
qidDoesNotCreateSequenceIdentity = refl

wikipediaDoesNotCreateMechanisticEvidence :
  Bio.WikimediaBiologyIdentityBoundary.wikipediaNarrativeCreatesMechanisticEvidence
    Bio.canonicalWikimediaBiologyIdentityBoundary ≡ false
wikipediaDoesNotCreateMechanisticEvidence = refl

wikipediaCoverageDoesNotConfirmWholeGraph :
  Bio.WikimediaBiologyIdentityBoundary.wikipediaCoverageConfirmsKitzerowWholeGraph
    Bio.canonicalWikimediaBiologyIdentityBoundary ≡ false
wikipediaCoverageDoesNotConfirmWholeGraph = refl

p352IdentityDoesNotCreateFlux :
  Bio.WikimediaBiologyIdentityBoundary.exactP352CreatesMeasuredBH4Flux
    Bio.canonicalWikimediaBiologyIdentityBoundary ≡ false
p352IdentityDoesNotCreateFlux = refl

duplicateP352CannotBeSilentlyCollapsed :
  Bio.WikimediaBiologyIdentityBoundary.duplicateExactP352MayBeSilentlyCollapsed
    Bio.canonicalWikimediaBiologyIdentityBoundary ≡ false
duplicateP352CannotBeSilentlyCollapsed = refl

missingProteinEnwikiDoesNotMeanProteinAbsent :
  Bio.WikimediaBiologyIdentityBoundary.absentProteinEnwikiMeansProteinAbsent
    Bio.canonicalWikimediaBiologyIdentityBoundary ≡ false
missingProteinEnwikiDoesNotMeanProteinAbsent = refl

reciprocalEncodingDoesNotCreateMechanism :
  Bio.WikimediaBiologyIdentityBoundary.completeReciprocalEncodingCreatesMechanisticSupport
    Bio.canonicalWikimediaBiologyIdentityBoundary ≡ false
reciprocalEncodingDoesNotCreateMechanism = refl

sprProteinQidIsCurrent :
  Bio.proteinQids Bio.sprIdentity ≡ ("Q409532" ∷ [])
sprProteinQidIsCurrent = refl

thProteinQidIsCurrent :
  Bio.proteinQids Bio.thIdentity ≡ ("Q420766" ∷ [])
thProteinQidIsCurrent = refl

mtorProteinQidCorrectedByAcquisition :
  Bio.proteinQids Bio.mtorIdentity ≡ ("Q285613" ∷ [])
mtorProteinQidCorrectedByAcquisition = refl

qdprRetainsBothExactP352Items :
  Bio.proteinQids Bio.qdprIdentity ≡ ("Q21145902" ∷ "Q7265406" ∷ [])
qdprRetainsBothExactP352Items = refl

qdprResolutionIsAmbiguous :
  Bio.resolution Bio.qdprIdentity ≡ Bio.ambiguousExact
qdprResolutionIsAmbiguous = refl

qdprGeneIdentityCannotCreateAuthority :
  Identity.externalIdentityCreatesAuthority Bio.qdprGeneQid ≡ false
qdprGeneIdentityCannotCreateAuthority = refl

allAcquiredRelationsHaveReciprocalEncodingReceipt :
  Bio.WikimediaPanelAcquisitionSummary.reciprocalEncodingPaidForEveryAcquiredMember
    Bio.canonicalWikimediaPanelAcquisitionSummary ≡ true
allAcquiredRelationsHaveReciprocalEncodingReceipt = refl

completeUniqueIdentityIsFalseBecauseQDPRAmbiguous :
  Bio.WikimediaPanelAcquisitionSummary.completeUniqueIdentity
    Bio.canonicalWikimediaPanelAcquisitionSummary ≡ false
completeUniqueIdentityIsFalseBecauseQDPRAmbiguous = refl

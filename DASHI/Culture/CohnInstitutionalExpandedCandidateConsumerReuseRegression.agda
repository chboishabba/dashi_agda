module DASHI.Culture.CohnInstitutionalExpandedCandidateConsumerReuseRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Culture.CohnInstitutionalExpandedCandidateConsumerReuseExact as Reuse

structuralExclusionHasNeighbour :
  Reuse.structuralEpistemicExclusionStatus Reuse.canonicalExpandedConsumerReuse ≡ Reuse.existingNeighbourConsumer
structuralExclusionHasNeighbour = refl

participationPowerHasNeighbour :
  Reuse.participationPowerStatus Reuse.canonicalExpandedConsumerReuse ≡ Reuse.existingNeighbourConsumer
participationPowerHasNeighbour = refl

internalExclusionHasNeighbour :
  Reuse.internalExclusionStatus Reuse.canonicalExpandedConsumerReuse ≡ Reuse.existingNeighbourConsumer
internalExclusionHasNeighbour = refl

outsiderWithinHasNeighbour :
  Reuse.outsiderWithinStandpointStatus Reuse.canonicalExpandedConsumerReuse ≡ Reuse.existingNeighbourConsumer
outsiderWithinHasNeighbour = refl

governanceHasExactOwner :
  Reuse.governancePermissionStatus Reuse.canonicalExpandedConsumerReuse ≡ Reuse.exactCanonicalOwner
governanceHasExactOwner = refl

sovereigntyHasExactOwner :
  Reuse.sovereigntyStatus Reuse.canonicalExpandedConsumerReuse ≡ Reuse.exactCanonicalOwner
sovereigntyHasExactOwner = refl

epistemicLabourStillOpen :
  Reuse.epistemicLabourStatus Reuse.canonicalExpandedConsumerReuse ≡ Reuse.uninstantiatedCandidate
epistemicLabourStillOpen = refl

epistemicActivismStillOpen :
  Reuse.epistemicActivismStatus Reuse.canonicalExpandedConsumerReuse ≡ Reuse.uninstantiatedCandidate
epistemicActivismStillOpen = refl

relationalResearchBurdenStillOpen :
  Reuse.relationalResearchBurdenStatus Reuse.canonicalExpandedConsumerReuse ≡ Reuse.uninstantiatedCandidate
relationalResearchBurdenStillOpen = refl

neighbourDoesNotCreateIdentity :
  Reuse.neighbouringConsumerDefinitionallyEqualsSourceCoordinate Reuse.canonicalExpandedConsumerReuseBoundary ≡ false
neighbourDoesNotCreateIdentity = refl

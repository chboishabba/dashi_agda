module DASHI.Reasoning.TrialecticHigherDescentMaxCutValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticSetEffectiveDescentExact as Effective
import DASHI.Reasoning.TrialecticRelationalSiteTransportEnrichmentFrontierExact as Transport

setBoundary : Effective.TrialecticSetEffectiveDescentBoundary
setBoundary = Effective.canonicalTrialecticSetEffectiveDescentBoundary

transportBoundary : Transport.TrialecticRelationalSiteTransportEnrichmentBoundary
transportBoundary = Transport.canonicalTrialecticRelationalSiteTransportEnrichmentBoundary

setLevelRealizationPaid : Effective.globalRealizationConstructed setBoundary ≡ true
setLevelRealizationPaid = refl

observationalUniquenessPaid : Effective.observationalUniquenessPaid setBoundary ≡ true
observationalUniquenessPaid = refl

strictRecordUniquenessNotClaimed : Effective.strictRecordEqualityUniquenessClaimed setBoundary ≡ false
strictRecordUniquenessNotClaimed = refl

edgeTransportCoveragePaid : Transport.threeEdgeObjectsCovered transportBoundary ≡ true
edgeTransportCoveragePaid = refl

fullSiteCoverageNotPaid : Transport.existingTransportCoversAllSiteObjects transportBoundary ≡ false
fullSiteCoverageNotPaid = refl

globalVertexFibresRequired : Transport.newGlobalVertexFiberMorphismsRequired transportBoundary ≡ true
globalVertexFibresRequired = refl

groupoidPresheafStillOpen : Transport.groupoidValuedPresheafConstructed transportBoundary ≡ false
groupoidPresheafStillOpen = refl

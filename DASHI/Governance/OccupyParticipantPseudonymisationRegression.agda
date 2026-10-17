module DASHI.Governance.OccupyParticipantPseudonymisationRegression where

open import DASHI.Core.Prelude
import DASHI.Governance.OccupyParticipantPseudonymisationExact as Privacy

noRawNamesInDerivedTables :
  Privacy.rawNamesStoredInDerivedFormalTables Privacy.canonicalPseudonymisationBoundary ≡ false
noRawNamesInDerivedTables = refl

keyNotCommitted :
  Privacy.hmacKeyCommittedToRepository Privacy.canonicalPseudonymisationBoundary ≡ false
keyNotCommitted = refl

mapNotCommitted :
  Privacy.privateNameTokenMapCommittedToRepository Privacy.canonicalPseudonymisationBoundary ≡ false
mapNotCommitted = refl

aliasesNotAutoMerged :
  Privacy.spellingVariantsAutomaticallyUnified Privacy.canonicalPseudonymisationBoundary ≡ false
aliasesNotAutoMerged = refl

collisionAuditPaid :
  Privacy.sixHexCollisionAuditPassedForCurrentTwentyLabels Privacy.canonicalPseudonymisationBoundary ≡ true
collisionAuditPaid = refl

stableCorrelationPreserved :
  Privacy.stablePseudonymSupportsLongitudinalCorrelation Privacy.canonicalPseudonymisationBoundary ≡ true
stableCorrelationPreserved = refl

historyNotPurgedByRedaction :
  Privacy.gitHistoryAutomaticallyPurgedByLiveTreeRedaction Privacy.canonicalPseudonymisationBoundary ≡ false
historyNotPurgedByRedaction = refl

module DASHI.Governance.BoloBoloComparatorEvidenceAtlasRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloComparatorEvidenceAtlasExact as Atlas

owsIsSameContextTransition :
  Atlas.sameContextFlatToNestedTransitionPresent Atlas.owsSpokesComparator ≡ true
owsIsSameContextTransition = refl

owsNotRandomized :
  Atlas.sameContextOWSTransitionIsRandomizedExperiment Atlas.canonicalComparatorEvidenceBoundary ≡ false
owsNotRandomized = refl

waterHasComparativeCoordinationOutcome :
  Atlas.comparativeCoordinationOutcomePresent Atlas.polycentricWaterComparator ≡ true
waterHasComparativeCoordinationOutcome = refl

mondragonRetainsLocalAutonomy :
  Atlas.localAutonomyRetained Atlas.mondragonComparator ≡ true
mondragonRetainsLocalAutonomy = refl

nepalDoesNotPayFederationOverhead :
  Atlas.nepalLocalSelfGovernancePaysFederationOverhead Atlas.canonicalComparatorEvidenceBoundary ≡ false
nepalDoesNotPayFederationOverhead = refl

noComparatorDirectlyPaysBoloCostBound :
  Atlas.directBoloCostBoundPaid Atlas.owsSpokesComparator ≡ false
noComparatorDirectlyPaysBoloCostBound = refl

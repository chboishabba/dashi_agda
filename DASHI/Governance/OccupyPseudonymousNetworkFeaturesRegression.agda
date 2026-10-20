module DASHI.Governance.OccupyPseudonymousNetworkFeaturesRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.OccupyPseudonymousNetworkFeaturesExact as Features

rowCountPinned : Features.featureRowCount Features.canonicalNetworkFeatureRows ≡ 5
rowCountPinned = refl

oct22EdgeCountPinned : Features.edgeCount Features.oct22Features ≡ 18
oct22EdgeCountPinned = refl

nov20ParticipantCountPinned : Features.pseudonymousParticipantCount Features.nov20Features ≡ 6
nov20ParticipantCountPinned = refl

jan08ReturningCountPinned : Features.returningParticipantCount Features.jan08Features ≡ 4
jan08ReturningCountPinned = refl

rawNamesNotRequired : Features.completeNamedParticipantIssueMatrixRequired Features.canonicalNetworkFeatureBoundary ≡ false
rawNamesNotRequired = refl

pseudonymousCorrelationUseful : Features.pseudonymousRelationalFeaturesUseful Features.canonicalNetworkFeatureBoundary ≡ true
pseudonymousCorrelationUseful = refl

featuresNotCoordinationCost : Features.networkFeaturesAreCoordinationCost Features.canonicalNetworkFeatureBoundary ≡ false
featuresNotCoordinationCost = refl

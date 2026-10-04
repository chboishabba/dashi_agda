module DASHI.Physics.Closure.NSClayFacingBAnalyticMaxCut20261004Test where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSClayFacingBAnalyticMaxCut20261004Exact as Cut

representationClosed : Cut.bRepresentationProgrammeClosed ≡ true
representationClosed = refl

b4HighestInformation : Cut.b4HighestInformationAnalyticWall ≡ true
b4HighestInformation = refl

q4ePreferred : Cut.b7QuarticEndpointPreferred ≡ true
q4ePreferred = refl

q5Fallback : Cut.b7DirectQuinticFallback ≡ true
q5Fallback = refl

b1StillOpen : Cut.b1AnalyticClosed ≡ false
b1StillOpen = refl

b2StillOpen : Cut.b2AnalyticClosed ≡ false
b2StillOpen = refl

b3StillOpen : Cut.b3AnalyticClosed ≡ false
b3StillOpen = refl

b4StillOpen : Cut.b4AnalyticClosed ≡ false
b4StillOpen = refl

b7StillOpen : Cut.b7OneProducerClosed ≡ false
b7StillOpen = refl

continuationStillOpen : Cut.bContinuationInputsClosed ≡ false
continuationStillOpen = refl

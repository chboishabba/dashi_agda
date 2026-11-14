module DASHI.Biology.AttributionConsumerNonDescentRegression where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer
import DASHI.Biology.AttributionConsumerNonDescentExact as X

sameSourceCollisionRetained :
  X.provenanceObserve X.wanPrimaryEndpointState ≡
  X.provenanceObserve X.wanSecondaryEndpointState
sameSourceCollisionRetained = refl

endpointConsumerDistinguishes :
  X.endpointConsumer X.wanPrimaryEndpointState ≡
  X.endpointConsumer X.wanSecondaryEndpointState → ⊥
endpointConsumerDistinguishes ()

sourceOnlyNonDescentRetained :
  Consumer.ConsumerNonDescentWitness X.provenanceObserve X.endpointConsumer
sourceOnlyNonDescentRetained = X.wanEndpointSourceOnlyNonDescent

sourceOnlyFactorizationBlocked :
  Consumer.FactorsThrough X.provenanceObserve X.endpointConsumer → ⊥
sourceOnlyFactorizationBlocked = X.sourceIdentityAloneCannotRecoverEndpointMeaning

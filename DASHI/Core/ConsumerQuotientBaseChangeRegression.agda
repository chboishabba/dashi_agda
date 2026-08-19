module DASHI.Core.ConsumerQuotientBaseChangeRegression where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerKernelQuotientPresentationExact as Kernel
import DASHI.Core.ConsumerQuotientBaseChangeExact as BaseChange
import DASHI.Core.SectionedProjectionProvenanceBridgeExact as Sectioned

data Bit2 : Set where
  bit0 bit1 : Bit2

bit0NotBit1 : bit0 ≡ bit1 -> ⊥
bit0NotBit1 ()

State : Set
State = Bit2 × Bit2

publicObserver : State -> Bit2
publicObserver = proj₁

publicConsumer : State -> Bit2
publicConsumer = proj₁

publicSection : Bit2 -> State
publicSection bit = bit , bit0

publicObserverSectioned : Sectioned.SectionedProjection State Bit2
publicObserverSectioned =
  Sectioned.sectionedProjection publicObserver publicSection (λ bit -> refl)

publicObserverSufficient :
  Descent.ConsumerSufficient publicObserver publicConsumer
publicObserverSufficient left right same = same

publicFactorsCanonicalConsumerKernel :
  Kernel.FactorizationThroughConsumerKernel
    publicConsumer
    publicObserver
    (Kernel.canonicalConsumerKernelPresentation publicConsumer)
publicFactorsCanonicalConsumerKernel =
  Kernel.sectionedSufficientObserverFactorsCanonical
    publicObserverSectioned publicConsumer
    publicObserverSufficient

------------------------------------------------------------------------
-- Compatible context restriction: public consumer transports identically.
------------------------------------------------------------------------

restrictPublic : State -> Bit2
restrictPublic = proj₁

fineConsumer : State -> Bit2
fineConsumer = proj₁

coarseConsumer : Bit2 -> Bit2
coarseConsumer bit = bit

compatibleRestriction :
  BaseChange.ConsumerFibreCompatibility
    restrictPublic fineConsumer coarseConsumer
compatibleRestriction left right same = same

fineConsumerSectioned : Sectioned.SectionedProjection State Bit2
fineConsumerSectioned = publicObserverSectioned

publicConsumerBaseChange :
  BaseChange.ConsumerBaseChange
    restrictPublic fineConsumer coarseConsumer
publicConsumerBaseChange =
  BaseChange.sectionedCompatibilityConstructsBaseChange
    restrictPublic coarseConsumer
    fineConsumerSectioned compatibleRestriction

publicConsumerBaseChangeCommutes :
  (state : State) ->
  coarseConsumer (restrictPublic state)
  ≡ BaseChange.transportOutcome publicConsumerBaseChange (fineConsumer state)
publicConsumerBaseChangeCommutes =
  BaseChange.commutes publicConsumerBaseChange

------------------------------------------------------------------------
-- Non-compatible restriction: the source quotient discarded the hidden bit,
-- while the target consumer asks for it.  No induced base change can exist.
------------------------------------------------------------------------

restrictHidden : State -> Bit2
restrictHidden = proj₂

hiddenCompatibilityFails :
  BaseChange.ConsumerFibreCompatibility
    restrictHidden fineConsumer coarseConsumer ->
  ⊥
hiddenCompatibilityFails compatible =
  bit0NotBit1
    (compatible
      (bit0 , bit0)
      (bit0 , bit1)
      refl)

hiddenRestrictionCannotBaseChange :
  BaseChange.ConsumerBaseChange
    restrictHidden fineConsumer coarseConsumer ->
  ⊥
hiddenRestrictionCannotBaseChange change =
  hiddenCompatibilityFails
    (BaseChange.baseChangeImpliesFibreCompatibility change)

record ConsumerQuotientBaseChangeRegressionBoundary : Set where
  constructor consumerQuotientBaseChangeRegressionBoundary
  field
    publicRestrictionTransports : Bool
    hiddenRestrictionTransportExists : Bool
    equalSourceConsumerClassCanSplitAfterBadRestriction : Bool

canonicalConsumerQuotientBaseChangeRegressionBoundary :
  ConsumerQuotientBaseChangeRegressionBoundary
canonicalConsumerQuotientBaseChangeRegressionBoundary =
  consumerQuotientBaseChangeRegressionBoundary true false true

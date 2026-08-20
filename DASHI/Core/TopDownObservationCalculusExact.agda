module DASHI.Core.TopDownObservationCalculusExact where

------------------------------------------------------------------------
-- TOP-DOWN DASHI OBSERVATION CALCULUS
--
-- Canonical workflow:
--
--   observe
--   -> locate collisions
--   -> characterize the fibre
--   -> exploit typed residual/symmetry structure
--   -> retain only what the declared consumer needs
--   -> prove descent.
--
-- The central distinction is between four different obligations:
--
--   consumer sufficiency    : downstream outcome descends through observation
--   reconstruction         : observation separates the fine carrier
--   operation locality     : a fine transition descends to the observation
--   representation economy : cardinal/storage/compute objective (not fixed here)
--
-- The first three are theorem predicates.  They are deliberately not collapsed
-- into one notion of "best representation".
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.DependentRecoverableProjectionExact as Recoverable
import DASHI.Core.ObserverRefinementLatticeExact as Observer

record ConsumerObservationProblem : Set₁ where
  constructor consumerObservationProblem
  field
    State : Set
    Surface : Set
    Outcome : Set
    observe : State → Surface
    consume : State → Outcome

open ConsumerObservationProblem public

Adequate : ConsumerObservationProblem → Set
Adequate problem =
  Descent.ConsumerSufficient (observe problem) (consume problem)

Reconstructive : ConsumerObservationProblem → Set
Reconstructive problem = Observer.Separating (observe problem)

reconstructionImpliesConsumerAdequacy :
  (problem : ConsumerObservationProblem) →
  Reconstructive problem → Adequate problem
reconstructionImpliesConsumerAdequacy problem separating left right sameSurface =
  cong (consume problem) (separating left right sameSurface)

record OperationDescendsThrough
    {State Surface : Set}
    (observe : State → Surface)
    (step : State → State) : Set₁ where
  constructor operationDescendsThrough
  field
    surfaceStep : Surface → Surface
    commutes :
      (state : State) →
      observe (step state) ≡ surfaceStep (observe state)

open OperationDescendsThrough public

operationDescentPreservesOneStepObservationEquality :
  ∀ {State Surface : Set}
    {observe : State → Surface}
    {step : State → State} →
  OperationDescendsThrough observe step →
  ∀ left right →
  observe left ≡ observe right →
  observe (step left) ≡ observe (step right)
operationDescentPreservesOneStepObservationEquality descent left right same =
  trans
    (commutes descent left)
    (trans
      (cong (surfaceStep descent) same)
      (sym (commutes descent right)))

------------------------------------------------------------------------
-- Exact dependent reopening gives a universally adequate observation, but it
-- may retain much more than one consumer needs.
------------------------------------------------------------------------

dependentCodeObserver :
  ∀ {State Surface : Set} →
  (projection : Recoverable.DependentExactRecoverableProjection State Surface) →
  State → Recoverable.DependentCode projection
dependentCodeObserver = Recoverable.encode

dependentCodeIsReconstructive :
  ∀ {State Surface : Set}
    (projection : Recoverable.DependentExactRecoverableProjection State Surface) →
  Observer.Separating (dependentCodeObserver projection)
dependentCodeIsReconstructive = Recoverable.dependentCodeSeparating

dependentCodeIsAdequateForEveryConsumer :
  ∀ {State Surface Outcome : Set}
    (projection : Recoverable.DependentExactRecoverableProjection State Surface)
    (consumer : State → Outcome) →
  Descent.ConsumerSufficient (dependentCodeObserver projection) consumer
dependentCodeIsAdequateForEveryConsumer projection consumer left right sameCode =
  cong consumer
    (Recoverable.dependentCodeSeparating projection left right sameCode)

------------------------------------------------------------------------
-- Exact finite falsifier: consumer sufficiency and operation locality do not
-- imply reconstruction.
------------------------------------------------------------------------

data Bit2 : Set where
  bit0 bit1 : Bit2

bit0NotBit1 : bit0 ≡ bit1 → ⊥
bit0NotBit1 ()

toggle : Bit2 → Bit2
toggle bit0 = bit1
toggle bit1 = bit0

ToyState : Set
ToyState = Bit2 × Bit2

toyObserve : ToyState → Bit2
toyObserve = proj₁

toyConsumer : ToyState → Bit2
toyConsumer = proj₁

toyStep : ToyState → ToyState
toyStep (public , hidden) = toggle public , hidden

toySurfaceStep : Bit2 → Bit2
toySurfaceStep = toggle

toyObserverIsConsumerSufficient :
  Descent.ConsumerSufficient toyObserve toyConsumer
toyObserverIsConsumerSufficient left right same = same

toyOperationDescends : OperationDescendsThrough toyObserve toyStep
toyOperationDescends = operationDescendsThrough toySurfaceStep (λ state → refl)

toyHiddenCollision : Observer.ObserverCollision toyObserve
toyHiddenCollision =
  Observer.observerCollision
    (bit0 , bit0)
    (bit0 , bit1)
    refl
    (λ equality → bit0NotBit1 (cong proj₂ equality))

toyObserverIsNotReconstructive : Observer.Separating toyObserve → ⊥
toyObserverIsNotReconstructive =
  Observer.collisionBlocksSeparation toyHiddenCollision

record TopDownObservationCalculusBoundary : Set where
  constructor topDownObservationCalculusBoundary
  field
    reconstructionImpliesAdequacyForDeclaredConsumer : Bool
    adequacyImpliesWholeStateReconstruction : Bool
    operationLocalityImpliesWholeStateReconstruction : Bool
    exactDependentReopeningIsSeparating : Bool
    exactDependentReopeningIsRequiredForEveryConsumer : Bool
    representationEconomyIsSamePredicateAsAdequacy : Bool
    oneUniversallyBestRepresentationAsserted : Bool

canonicalTopDownObservationCalculusBoundary : TopDownObservationCalculusBoundary
canonicalTopDownObservationCalculusBoundary =
  topDownObservationCalculusBoundary
    true false false true false false false

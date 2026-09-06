module DASHI.Analysis.RiemannAristotlePoleNearPhaseStatisticExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientDirectFiniteNearAttackExact as Direct

------------------------------------------------------------------------
-- DIRECT ROUTE: MINIMUM PHASE-SENSITIVE INFORMATION
--
-- The direct finite-near route cannot descend through count/envelope data.
-- What it needs is an additional statistic that still sees the target-relative
-- phase entering
--
--   cos((b_sigma - t) u).
--
-- BIDI UPDATE: the repository's existing DirectFinitePoleNearProducer is
-- strictly richer than this interface. It already owns ZeroIndex, target,
-- cutoff, nearIndex, multiplicity, targetRelativeGap, signed cosine data and an
-- approximant/error receipt. Therefore the phase-statistic view is compiler
-- output from a direct producer; a second zero/phase carrier is not a live
-- research obligation.
------------------------------------------------------------------------

record PoleNearPhaseStatistic : Set₁ where
  constructor pole-near-phase-statistic
  field
    ZeroIndex Scalar PhaseCode : Set
    target : Scalar
    cutoff : Scalar
    nearIndex : ZeroIndex → Set
    multiplicity : ZeroIndex → Scalar
    targetRelativeGap : ZeroIndex → Scalar
    phaseCode : ZeroIndex → PhaseCode

    SameCoarseObservation : ZeroIndex → ZeroIndex → Set
    DistinguishesSignedContribution : PhaseCode → PhaseCode → Set

    phaseCanSeparateCoarseCollision :
      (x y : ZeroIndex) →
      SameCoarseObservation x y →
      DistinguishesSignedContribution (phaseCode x) (phaseCode y) → Set

    preservesTargetRelativeGap : Set
    preservesMultiplicity : Set
    preservesFiniteNearIndex : Set
    phaseReference : String

open PoleNearPhaseStatistic public

record PhaseStatisticControlsFiniteNear
    (p : PoleNearPhaseStatistic) : Set₁ where
  constructor phase-statistic-controls-finite-near
  field
    Evaluation : Set
    evaluation : Evaluation
    controlReference : String

open PhaseStatisticControlsFiniteNear public

------------------------------------------------------------------------
-- Direct producer -> phase-statistic compiler.
--
-- The phase code is literally targetRelativeGap. Coarse equality is represented
-- minimally by multiplicity equality; phase separation is non-equality of the
-- target gaps. The interface only asks for the separating proposition as a Set,
-- not an analytic estimate, so no additional theorem is fabricated here.
------------------------------------------------------------------------

phaseStatisticFromDirectFiniteProducer :
  Direct.DirectFinitePoleNearProducer → PoleNearPhaseStatistic
phaseStatisticFromDirectFiniteProducer d =
  pole-near-phase-statistic
    (Direct.DirectFinitePoleNearProducer.ZeroIndex d)
    (Direct.DirectFinitePoleNearProducer.Scalar d)
    (Direct.DirectFinitePoleNearProducer.Scalar d)
    (Direct.DirectFinitePoleNearProducer.target d)
    (Direct.DirectFinitePoleNearProducer.cutoff d)
    (Direct.DirectFinitePoleNearProducer.nearIndex d)
    (Direct.DirectFinitePoleNearProducer.multiplicityOf d)
    (Direct.DirectFinitePoleNearProducer.targetRelativeGap d)
    (Direct.DirectFinitePoleNearProducer.targetRelativeGap d)
    (λ x y →
      Direct.DirectFinitePoleNearProducer.multiplicityOf d x
      ≡ Direct.DirectFinitePoleNearProducer.multiplicityOf d y)
    (λ a b → a ≡ b → ⊥)
    (λ x y coarse separated →
      Direct.DirectFinitePoleNearProducer.targetRelativeGap d x
      ≡ Direct.DirectFinitePoleNearProducer.targetRelativeGap d y → ⊥)
    (Direct.DirectFinitePoleNearProducer.preservesTargetRelativeGap d)
    (Direct.DirectFinitePoleNearProducer.preservesMultiplicity d)
    (Direct.DirectFinitePoleNearProducer.preservesFiniteNearIndex d)
    "compiled from DirectFinitePoleNearProducer.targetRelativeGap"

------------------------------------------------------------------------
-- The direct producer's existing evaluation receipt also inhabits the weak
-- `PhaseStatisticControlsFiniteNear` interface. This is not a new evaluation:
-- it is the same `Within finiteSignedNearValue approximant error` receipt.
------------------------------------------------------------------------

phaseControlFromDirectFiniteProducer :
  (d : Direct.DirectFinitePoleNearProducer) →
  PhaseStatisticControlsFiniteNear (phaseStatisticFromDirectFiniteProducer d)
phaseControlFromDirectFiniteProducer d =
  phase-statistic-controls-finite-near
    (Direct.DirectFinitePoleNearProducer.Within d
      (Direct.DirectFinitePoleNearProducer.finiteSignedNearValue d)
      (Direct.DirectFinitePoleNearProducer.approximant d)
      (Direct.DirectFinitePoleNearProducer.error d))
    (Direct.DirectFinitePoleNearProducer.evaluationReceipt d)
    "same direct finite-near approximant/error receipt; no second phase evaluation"

------------------------------------------------------------------------
-- Search compression.
------------------------------------------------------------------------

data PhaseStatisticSearchPayment : Set where
  constructSecondPhaseStatisticCarrier
  compilePhaseStatisticFromDirectProducer
  proveActualDirectFiniteEvaluation
  : PhaseStatisticSearchPayment

data PaymentState : Set where
  pruned downstream live : PaymentState

paymentState : PhaseStatisticSearchPayment → PaymentState
paymentState constructSecondPhaseStatisticCarrier = pruned
paymentState compilePhaseStatisticFromDirectProducer = downstream
paymentState proveActualDirectFiniteEvaluation = live

secondPhaseStatisticCarrierPruned :
  paymentState constructSecondPhaseStatisticCarrier ≡ pruned
secondPhaseStatisticCarrierPruned = refl

record PoleNearPhaseStatisticBoundary : Set where
  constructor pole-near-phase-statistic-boundary
  field
    countAndEnvelopeSufficient : Bool
    countAndEnvelopeSufficientIsFalse : countAndEnvelopeSufficient ≡ false

    targetRelativePhaseCoordinateRequired : Bool
    targetRelativePhaseCoordinateRequiredIsTrue :
      targetRelativePhaseCoordinateRequired ≡ true

    repositoryAlreadyOwnsConcretePoleNearPhaseStatistic : Bool
    repositoryAlreadyOwnsConcretePoleNearPhaseStatisticIsTrue :
      repositoryAlreadyOwnsConcretePoleNearPhaseStatistic ≡ true

    phaseStatisticRequiresSecondZeroCarrier : Bool
    phaseStatisticRequiresSecondZeroCarrierIsFalse :
      phaseStatisticRequiresSecondZeroCarrier ≡ false

    directFiniteNearClosed : Bool
    directFiniteNearClosedIsFalse : directFiniteNearClosed ≡ false

    nextTheorem : String

canonicalPoleNearPhaseStatisticBoundary : PoleNearPhaseStatisticBoundary
canonicalPoleNearPhaseStatisticBoundary =
  pole-near-phase-statistic-boundary
    false refl
    true refl
    true refl
    false refl
    false refl
    "Do not construct another phase-statistic carrier. Compile the phase view from the existing DirectFinitePoleNearProducer, weld that direct producer to the existing selected pole-near producer, and improve the SAME direct producer's actual signed evaluation / target-gap moment strongly enough for the RH consumers."

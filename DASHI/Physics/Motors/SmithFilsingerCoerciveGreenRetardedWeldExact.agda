module DASHI.Physics.Motors.SmithFilsingerCoerciveGreenRetardedWeldExact where

-- F02/F13: REUSE the canonical Balaban finite coercive Green inverse
-- and Smith/Filsinger retarded-flight owner. There is no duplicated
-- Green inverse, no imported elliptic -> hyperbolic causality theorem,
-- and no fabricated Sun/Earth material parameters.
--
-- Mathematical result: a deliberately delayed finite spatial Green
-- RESPONSE is zero strictly before its chosen discrete travel time;
-- at that time it equals the existing inverse of the source at time 0,
-- and inherits the exact original Green norm bound. Whether the delay
-- is the REAL Maxwell/soil/air/ionosphere front is a separate physical
-- proof/measurement obligation. Static elliptic Green != retarded
-- Maxwell dyadic Green.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.YangMills.BalabanFiniteCoerciveGreen as Green
import DASHI.Physics.Motors.SmithFilsingerTimeIndexedTransferExact as Time
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound
import DASHI.Physics.Motors.SmithFilsingerSourceMaxwellBoundaryWeldExact as Original

-- Distinctly CALCULATED temporal delay response: no effect before
-- delay=flight and one original Green application at launch-arrival.
-- A physical waveguide's true kernel can have a long dispersive tail;
-- this is a one-delay finite surrogate, not a claimed exact waveguide.
retardedGreen :
  ∀ {Vector Scalar BoundValue : Set}
  {coercive : Green.CoerciveFiniteOperator Vector Scalar BoundValue} →
  Green.FiniteCoerciveInverseAuthority coercive →
  Vector → (Nat → Vector) → Nat → Nat → Vector
retardedGreen authority sourceZero source zero t =
  Green.inverse authority (source t)
retardedGreen authority sourceZero source (suc delay) zero =
  sourceZero
retardedGreen authority sourceZero source (suc delay) (suc t) =
  retardedGreen authority sourceZero source delay t

-- This is the unambiguous strict temporal order t < delay, not merely
-- a non-strict launch<=arrival label.
data StrictEarlier : Nat → Nat → Set where
  firstEarlier : ∀ {delay} → StrictEarlier zero (suc delay)
  shiftEarlier : ∀ {time delay} →
    StrictEarlier time delay →
    StrictEarlier (suc time) (suc delay)

greenCannotRespondBeforeChosenDelay :
  ∀ {Vector Scalar BoundValue : Set}
  {coercive : Green.CoerciveFiniteOperator Vector Scalar BoundValue}
  (authority : Green.FiniteCoerciveInverseAuthority coercive)
  (sourceZero : Vector) (source : Nat → Vector)
  (delay time : Nat) →
  StrictEarlier time delay →
  retardedGreen authority sourceZero source delay time ≡ sourceZero
greenCannotRespondBeforeChosenDelay authority zeroVector source
  (suc delay) zero firstEarlier = refl
greenCannotRespondBeforeChosenDelay authority zeroVector source
  (suc delay) (suc time) (shiftEarlier earlier) =
  greenCannotRespondBeforeChosenDelay authority zeroVector source
    delay time earlier

greenAtArrivalReadsExactlyLaunchedSource :
  ∀ {Vector Scalar BoundValue : Set}
  {coercive : Green.CoerciveFiniteOperator Vector Scalar BoundValue}
  (authority : Green.FiniteCoerciveInverseAuthority coercive)
  (sourceZero : Vector) (source : Nat → Vector) (flight : Nat) →
  retardedGreen authority sourceZero source flight flight
    ≡ Green.inverse authority (source zero)
greenAtArrivalReadsExactlyLaunchedSource authority zeroVector
  source zero = refl
greenAtArrivalReadsExactlyLaunchedSource authority zeroVector
  source (suc flight) =
  greenAtArrivalReadsExactlyLaunchedSource authority zeroVector
    source flight

-- Use the PRE-EXISTING Green bound, not an asserted bound chosen
-- after seeing the output.
greenAtArrivalInheritsCoerciveBound :
  ∀ {Vector Scalar BoundValue : Set}
  {coercive : Green.CoerciveFiniteOperator Vector Scalar BoundValue}
  (authority : Green.FiniteCoerciveInverseAuthority coercive)
  (sourceZero : Vector) (source : Nat → Vector) (flight : Nat) →
  Green.CoerciveFiniteOperator.LessEqual coercive
    (Green.CoerciveFiniteOperator.vectorNorm coercive
      (retardedGreen authority sourceZero source flight flight))
    (Green.FiniteCoerciveInverseAuthority.multiplyBound authority
      (Green.FiniteCoerciveInverseAuthority.reciprocalCoercivity authority)
      (Green.CoerciveFiniteOperator.vectorNorm coercive (source zero)))
greenAtArrivalInheritsCoerciveBound authority zeroVector source flight
  rewrite greenAtArrivalReadsExactlyLaunchedSource authority
    zeroVector source flight =
  Green.FiniteCoerciveInverseAuthority.inverseNormBound authority
    (source zero)

-- Original typed travel time stays explicit. This result says nothing
-- about displacement-current terminal calibration or real source work.
record OriginalSelectedRetardedGreen
  {Vector Scalar BoundValue : Set}
  (coercive : Green.CoerciveFiniteOperator Vector Scalar BoundValue)
  (authority : Green.FiniteCoerciveInverseAuthority coercive)
  (b : Original.SelectedBoundary)
  (f : Original.FormalFieldToPort b) : Set₁ where
  field
    zeroVector : Vector
    sourceHistory : Nat → Vector
    sensor : Vector → Nat
    sourceAtLaunchIsActualMeasured : Set
    materialLayeredMaxwellKernelMatchesGreen : Set
    physicalLightConeBoundMatchesChosenFlight : Set
    originalTerminalCurrentAndVoltageCalibrated : Set
    independentlyReplenishedSourceWork : Set
    measuredSource : sourceAtLaunchIsActualMeasured
    selectedMaxwellKernel : materialLayeredMaxwellKernelMatchesGreen
    physicalCone : physicalLightConeBoundMatchesChosenFlight
    originalReadback : originalTerminalCurrentAndVoltageCalibrated
    realNaturalWork : independentlyReplenishedSourceWork

selectedRetardedGreenAtArrival :
  ∀ {Vector Scalar BoundValue : Set}
    {coercive : Green.CoerciveFiniteOperator Vector Scalar BoundValue}
    (authority : Green.FiniteCoerciveInverseAuthority coercive)
    (b : Original.SelectedBoundary)
    (f : Original.FormalFieldToPort b)
    (a : OriginalSelectedRetardedGreen coercive authority b f) →
  retardedGreen authority
    (OriginalSelectedRetardedGreen.zeroVector a)
    (OriginalSelectedRetardedGreen.sourceHistory a)
    (Time.RetardedFlight.flight
      (Original.FormalFieldToPort.causalFlight f))
    (Time.RetardedFlight.flight
      (Original.FormalFieldToPort.causalFlight f))
  ≡ Green.inverse authority
      (OriginalSelectedRetardedGreen.sourceHistory a zero)
selectedRetardedGreenAtArrival authority b f a =
  greenAtArrivalReadsExactlyLaunchedSource authority
    (OriginalSelectedRetardedGreen.zeroVector a)
    (OriginalSelectedRetardedGreen.sourceHistory a)
    (Time.RetardedFlight.flight
      (Original.FormalFieldToPort.causalFlight f))

-- F02/ F13 high-alpha physical remainder: real Maxwell dyadic Green,
-- causal support and dispersive memory, exact exterior boundary/return,
-- E/H/J fields, source history and source backaction, measured terminal
-- V/I, all material/controller pump losses, restored natural source cycle.

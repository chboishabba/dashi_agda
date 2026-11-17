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

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.YangMills.BalabanFiniteCoerciveGreen as Green
import DASHI.Physics.Motors.SmithFilsingerTimeIndexedTransferExact as Time
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound
import DASHI.Physics.Motors.SmithFilsingerSourceMaxwellBoundaryWeldExact as Original
import DASHI.Physics.Motors.SmithFilsingerMidpointPhaseWorkExact as Port
import DASHI.Physics.Motors.SmithFilsingerYeeCFLConeGuardExact as Cone

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

-- A selected original flight starts at an ARBITRARY launch clock,
-- not always at t=0. Stamping the Green history avoids the subtle
-- but serious mistake of interpreting a local relative delay as an
-- absolute original-world arrival time.
stampedGreen :
  ∀ {Vector Scalar BoundValue : Set}
  {coercive : Green.CoerciveFiniteOperator Vector Scalar BoundValue} →
  Green.FiniteCoerciveInverseAuthority coercive →
  Vector → (Nat → Vector) → Nat → Nat → Nat → Vector
stampedGreen authority sourceZero source zero flight t =
  retardedGreen authority sourceZero source flight t
stampedGreen authority sourceZero source (suc launch) flight zero =
  sourceZero
stampedGreen authority sourceZero source (suc launch) flight (suc t) =
  stampedGreen authority sourceZero source launch flight t

stampedGreenIsTotalRetardedDelay :
  ∀ {Vector Scalar BoundValue : Set}
  {coercive : Green.CoerciveFiniteOperator Vector Scalar BoundValue}
  (authority : Green.FiniteCoerciveInverseAuthority coercive)
  (sourceZero : Vector) (source : Nat → Vector)
  (launch flight t : Nat) →
  stampedGreen authority sourceZero source launch flight t
    ≡ retardedGreen authority sourceZero source (launch + flight) t
stampedGreenIsTotalRetardedDelay authority sourceZero source zero flight t =
  refl
stampedGreenIsTotalRetardedDelay authority sourceZero source
  (suc launch) flight zero = refl
stampedGreenIsTotalRetardedDelay authority sourceZero source
  (suc launch) flight (suc t) =
  stampedGreenIsTotalRetardedDelay authority sourceZero source
    launch flight t

stampedGreenAtActualArrival :
  ∀ {Vector Scalar BoundValue : Set}
  {coercive : Green.CoerciveFiniteOperator Vector Scalar BoundValue}
  (authority : Green.FiniteCoerciveInverseAuthority coercive)
  (sourceZero : Vector) (source : Nat → Vector)
  (launch flight : Nat) →
  stampedGreen authority sourceZero source launch flight (launch + flight)
    ≡ Green.inverse authority (source zero)
stampedGreenAtActualArrival authority sourceZero source launch flight =
  trans
    (stampedGreenIsTotalRetardedDelay authority sourceZero source
      launch flight (launch + flight))
    (greenAtArrivalReadsExactlyLaunchedSource authority sourceZero source
      (launch + flight))

stampedGreenIsZeroBeforeActualArrival :
  ∀ {Vector Scalar BoundValue : Set}
  {coercive : Green.CoerciveFiniteOperator Vector Scalar BoundValue}
  (authority : Green.FiniteCoerciveInverseAuthority coercive)
  (sourceZero : Vector) (source : Nat → Vector)
  (launch flight t : Nat) →
  StrictEarlier t (launch + flight) →
  stampedGreen authority sourceZero source launch flight t ≡ sourceZero
stampedGreenIsZeroBeforeActualArrival authority sourceZero source
  launch flight t before =
  trans
    (stampedGreenIsTotalRetardedDelay authority sourceZero source
      launch flight t)
    (greenCannotRespondBeforeChosenDelay authority sourceZero source
      (launch + flight) t before)

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
    -- A calibrated terminal-work readout must take the ZERO field
    -- to ZERO claimed electrical work; otherwise a delayed zero field
    -- can be mislabelled as an energized receiver.
    sensor : Vector → Nat
    sensorZero : sensor zeroVector ≡ zero

    -- Same original actual receiver work is a CONTENTFUL equality,
    -- not the inference of power from an arbitrary Green amplitude.
    sameOriginalTerminalWork :
      sensor (Green.inverse authority (sourceHistory zero))
        ≡ Port.MidpointTwoPortWorkWindow.usefulWork
            (Original.FormalFieldToPort.portWindow f)

    -- The source and the physical operator are chosen as actual typed
    -- objects, not unnamed Set witnesses that may be inhabited by Unit.
    originalMeasuredSourceAtLaunch : Vector
    sourceHistoryMatchesActualLaunch :
      sourceHistory zero ≡ originalMeasuredSourceAtLaunch

    originalPhysicalMaxwellSourceResponse : Vector → Vector
    physicalMaxwellGreenMatchesChosenInverse :
      ∀ sourceInput →
      originalPhysicalMaxwellSourceResponse sourceInput
        ≡ Green.inverse authority sourceInput

    -- A finite strictly physical cone needs sourced distance/speed
    -- and an actual bound on THIS SAME typed original flight.
    measuredSourceToCollectorDistance maximumPhysicalFrontSpeed : Nat
    originalPhysicalCone :
      Cone.CalibratedPhysicalCone measuredSourceToCollectorDistance
        maximumPhysicalFrontSpeed
        (Time.RetardedFlight.flight
          (Original.FormalFieldToPort.causalFlight f))

    -- Independent NET natural work is not inferable from a field norm.
    -- It must be the SAME original signed natural incident/outgoing port.
    independentlyMeasuredNaturalNetWork : Nat
    naturalSourceIsSameOriginal :
      Port.MidpointTwoPortWorkWindow.naturalIncident
        (Original.FormalFieldToPort.portWindow f)
      ≡ Port.MidpointTwoPortWorkWindow.naturalOutgoing
          (Original.FormalFieldToPort.portWindow f)
          + independentlyMeasuredNaturalNetWork

    -- Real evidence/physical inverse identification is still OPEN,
    -- including Maxwell constitutive law, materials, boundary conditions,
    -- antenna geometry, full causal support and sensor calibration.

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

-- Before actual arrival no terminal work can be inferred from
-- this delayed Green, PROVIDED the calibrated sensor zero condition
-- is supplied. This is a real Nat equality, not a verbal gate.
selectedRetardedNoUsefulBeforeArrival :
  ∀ {Vector Scalar BoundValue : Set}
    {coercive : Green.CoerciveFiniteOperator Vector Scalar BoundValue}
    (authority : Green.FiniteCoerciveInverseAuthority coercive)
    (b : Original.SelectedBoundary)
    (f : Original.FormalFieldToPort b)
    (a : OriginalSelectedRetardedGreen coercive authority b f)
    (time : Nat) →
  StrictEarlier time
    (Time.RetardedFlight.flight
      (Original.FormalFieldToPort.causalFlight f)) →
  OriginalSelectedRetardedGreen.sensor a
    (retardedGreen authority
      (OriginalSelectedRetardedGreen.zeroVector a)
      (OriginalSelectedRetardedGreen.sourceHistory a)
      (Time.RetardedFlight.flight
        (Original.FormalFieldToPort.causalFlight f))
      time)
  ≡ zero
selectedRetardedNoUsefulBeforeArrival authority b f a time earlier =
  trans
    (cong (OriginalSelectedRetardedGreen.sensor a)
      (greenCannotRespondBeforeChosenDelay authority
        (OriginalSelectedRetardedGreen.zeroVector a)
        (OriginalSelectedRetardedGreen.sourceHistory a)
        (Time.RetardedFlight.flight
          (Original.FormalFieldToPort.causalFlight f))
        time earlier))
    (OriginalSelectedRetardedGreen.sensorZero a)

-- At the chosen arrival time a selected useful-work claim STILL
-- requires the independent calibrated same-original terminal equation.
selectedRetardedGreenMatchesOriginalUsefulPort :
  ∀ {Vector Scalar BoundValue : Set}
    {coercive : Green.CoerciveFiniteOperator Vector Scalar BoundValue}
    (authority : Green.FiniteCoerciveInverseAuthority coercive)
    (b : Original.SelectedBoundary)
    (f : Original.FormalFieldToPort b)
    (a : OriginalSelectedRetardedGreen coercive authority b f) →
  OriginalSelectedRetardedGreen.sensor a
    (retardedGreen authority
      (OriginalSelectedRetardedGreen.zeroVector a)
      (OriginalSelectedRetardedGreen.sourceHistory a)
      (Time.RetardedFlight.flight
        (Original.FormalFieldToPort.causalFlight f))
      (Time.RetardedFlight.flight
        (Original.FormalFieldToPort.causalFlight f)))
  ≡ Port.MidpointTwoPortWorkWindow.usefulWork
      (Original.FormalFieldToPort.portWindow f)
selectedRetardedGreenMatchesOriginalUsefulPort authority b f a =
  trans
    (cong (OriginalSelectedRetardedGreen.sensor a)
      (selectedRetardedGreenAtArrival authority b f a))
    (OriginalSelectedRetardedGreen.sameOriginalTerminalWork a)

-- Absolute selected-original clock: launches may start at t>0.
-- RetardedFlight.travelLaw is the ORIGINAL time index equality,
-- not a new chosen measurement or an arbitrary arbitrary-time waiver.
selectedOriginalGreenAtPhysicalArrival :
  ∀ {Vector Scalar BoundValue : Set}
    {coercive : Green.CoerciveFiniteOperator Vector Scalar BoundValue}
    (authority : Green.FiniteCoerciveInverseAuthority coercive)
    (b : Original.SelectedBoundary)
    (f : Original.FormalFieldToPort b)
    (a : OriginalSelectedRetardedGreen coercive authority b f) →
  let flight = Original.FormalFieldToPort.causalFlight f in
  OriginalSelectedRetardedGreen.sensor a
    (stampedGreen authority
      (OriginalSelectedRetardedGreen.zeroVector a)
      (OriginalSelectedRetardedGreen.sourceHistory a)
      (Time.RetardedFlight.launch flight)
      (Time.RetardedFlight.flight flight)
      (Time.RetardedFlight.arrival flight))
  ≡ Port.MidpointTwoPortWorkWindow.usefulWork
      (Original.FormalFieldToPort.portWindow f)
selectedOriginalGreenAtPhysicalArrival authority b f a
  rewrite sym (Time.RetardedFlight.travelLaw
    (Original.FormalFieldToPort.causalFlight f)) =
  trans
    (cong (OriginalSelectedRetardedGreen.sensor a)
      (stampedGreenAtActualArrival authority
        (OriginalSelectedRetardedGreen.zeroVector a)
        (OriginalSelectedRetardedGreen.sourceHistory a)
        (Time.RetardedFlight.launch
          (Original.FormalFieldToPort.causalFlight f))
        (Time.RetardedFlight.flight
          (Original.FormalFieldToPort.causalFlight f))))
    (OriginalSelectedRetardedGreen.sameOriginalTerminalWork a)

-- F02/ F13 high-alpha physical remainder: real Maxwell dyadic Green,
-- causal support and dispersive memory, exact exterior boundary/return,
-- E/H/J fields, source history and source backaction, measured terminal
-- V/I, all material/controller pump losses, restored natural source cycle.

module DASHI.Biology.Physical.Harmonic369HelixLiftExact where

------------------------------------------------------------------------
-- Exact finite 3 -> 6 -> 9 coordinate lift.
--
-- One C3 phase is represented by two qualitative quadrature coordinates.  For
-- angles 0, 2pi/3, 4pi/3 these are the signs of the exact scaled pair
--
--   (2 cos theta, (2/sqrt 3) sin theta)
--
-- namely (+,0), (-,+), (-,-).  Three phases therefore give three cosine-like
-- and three sine-like slots (H6).  Retaining one winding/history coordinate per
-- phase gives H9.  This reuses the repository's existing interpretation that
-- H3/H6/H9 count accumulated coordinate slots, not candidate cardinality.
--
-- No analytic real-valued sin/cos theorem is claimed here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.RelationalHorizon369 as H
import DASHI.Biology.SSP369JResolutionBifiltrationExact as Existing
import DASHI.Cognition.PNF.GrokkingTaskCharacterPhaseExact as Character
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

zero≢one : 0 ≢ 1
zero≢one ()

data SignedQuadrature : Set where
  qNegative qZero qPositive : SignedQuadrature

record PhaseQuadrature : Set where
  constructor phaseQuadrature
  field
    cosineCoordinate : SignedQuadrature
    sineCoordinate : SignedQuadrature

open PhaseQuadrature public

quadrature : Wheel.DepthWheelPhase → PhaseQuadrature
quadrature Wheel.phase-0 = phaseQuadrature qPositive qZero
quadrature Wheel.phase-1 = phaseQuadrature qNegative qPositive
quadrature Wheel.phase-2 = phaseQuadrature qNegative qNegative

decodeQuadrature : PhaseQuadrature → Wheel.DepthWheelPhase
decodeQuadrature (phaseQuadrature qPositive qZero) = Wheel.phase-0
decodeQuadrature (phaseQuadrature qNegative qPositive) = Wheel.phase-1
decodeQuadrature (phaseQuadrature qNegative qNegative) = Wheel.phase-2
decodeQuadrature _ = Wheel.phase-0

quadratureRoundTrip :
  (phase : Wheel.DepthWheelPhase) →
  decodeQuadrature (quadrature phase) ≡ phase
quadratureRoundTrip Wheel.phase-0 = refl
quadratureRoundTrip Wheel.phase-1 = refl
quadratureRoundTrip Wheel.phase-2 = refl

PhaseTriple : Set
PhaseTriple = H.Horizon3 Wheel.DepthWheelPhase

QuadratureSix : Set
QuadratureSix = H.Horizon6 SignedQuadrature SignedQuadrature

phaseTripleToSix : PhaseTriple → QuadratureSix
phaseTripleToSix (Existing.triple a b c) =
  H.horizon6
    (Existing.triple
      (cosineCoordinate (quadrature a))
      (cosineCoordinate (quadrature b))
      (cosineCoordinate (quadrature c)))
    (Existing.triple
      (sineCoordinate (quadrature a))
      (sineCoordinate (quadrature b))
      (sineCoordinate (quadrature c)))

sixToPhaseTriple : QuadratureSix → PhaseTriple
sixToPhaseTriple
  (H.horizon6
    (Existing.triple ar br cr)
    (Existing.triple ai bi ci)) =
  Existing.triple
    (decodeQuadrature (phaseQuadrature ar ai))
    (decodeQuadrature (phaseQuadrature br bi))
    (decodeQuadrature (phaseQuadrature cr ci))

phaseTripleSixRoundTrip :
  (phases : PhaseTriple) →
  sixToPhaseTriple (phaseTripleToSix phases) ≡ phases
phaseTripleSixRoundTrip (Existing.triple a b c)
  rewrite quadratureRoundTrip a
        | quadratureRoundTrip b
        | quadratureRoundTrip c = refl

------------------------------------------------------------------------
-- Add one unwrapped history/winding coordinate per phase.
------------------------------------------------------------------------

HelicalNine : Set
HelicalNine = H.Horizon9 SignedQuadrature SignedQuadrature Nat

phaseTripleToNine : PhaseTriple → Existing.Triple Nat → HelicalNine
phaseTripleToNine phases winding = H.horizon9 (phaseTripleToSix phases) winding

nineToSixForgetsWinding : HelicalNine → QuadratureSix
nineToSixForgetsWinding = H.project9to6

nineProjectionRecoversQuadrature :
  (phases : PhaseTriple) (winding : Existing.Triple Nat) →
  nineToSixForgetsWinding (phaseTripleToNine phases winding)
    ≡ phaseTripleToSix phases
nineProjectionRecoversQuadrature phases winding = refl

zeroWinding oneWinding : Existing.Triple Nat
zeroWinding = Existing.triple 0 0 0
oneWinding = Existing.triple 1 0 0

zeroWinding≢oneWinding : zeroWinding ≢ oneWinding
zeroWinding≢oneWinding eq = zero≢one (cong Existing.first eq)

samplePhases : PhaseTriple
samplePhases = Existing.triple Wheel.phase-0 Wheel.phase-1 Wheel.phase-2

sampleHelixZero sampleHelixOne : HelicalNine
sampleHelixZero = phaseTripleToNine samplePhases zeroWinding
sampleHelixOne = phaseTripleToNine samplePhases oneWinding

sameCircularProjectionDifferentHistory :
  nineToSixForgetsWinding sampleHelixZero
  ≡ nineToSixForgetsWinding sampleHelixOne
sameCircularProjectionDifferentHistory = refl

helicalHistoriesRemainDistinct : sampleHelixZero ≢ sampleHelixOne
helicalHistoriesRemainDistinct eq =
  zeroWinding≢oneWinding (cong H.third3 eq)

------------------------------------------------------------------------
-- The phase composition used by the harmonic lift is the existing C3 task
-- character law, so the lift cross-pollinates rather than inventing a second
-- C3 operation.
------------------------------------------------------------------------

phaseCompositionRegression :
  Character.phaseComposeC3 Wheel.phase-1 Wheel.phase-2 ≡ Wheel.phase-0
phaseCompositionRegression = refl

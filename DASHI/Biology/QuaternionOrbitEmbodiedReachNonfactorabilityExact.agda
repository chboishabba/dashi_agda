module DASHI.Biology.QuaternionOrbitEmbodiedReachNonfactorabilityExact where

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Biology.ObserverRelativeReachableSubfabricExact as Reach
import DASHI.Mathematics.Topology.QuaternionHopfUnitOrbitExact as Hopf

------------------------------------------------------------------------
-- RAW ORIENTATION SYMMETRY CAN FAIL TO BE FUNCTIONAL SYMMETRY FOR AN
-- EMBODIED CONSUMER
--
-- Heinz Hopf,
-- "Über die Abbildungen der dreidimensionalen Sphäre auf die Kugelfläche".
-- DOI: 10.1007/BF01457962.
--
-- Julien Flamant, Nicolas Le Bihan, Pierre Chainais,
-- "Time-frequency analysis of bivariate signals".
-- DOI: 10.1016/j.acha.2017.05.007.
--
-- The repository's quaternion owner proves exact unit-quaternion orbit
-- invariance of Hopf observables.  We now cross that symmetry with an embodied
-- consumer coordinate.  The raw Hopf observable can remain identical along an
-- orientation orbit while effective reachability differs with body context.
-- This proves that symmetry of the field carrier need not be symmetry for a
-- body-indexed functional observer.
------------------------------------------------------------------------

record OrbitEmbodiedState : Set where
  constructor orbitEmbodiedState
  field
    body : Reach.BodyContext
    orientationPair : Hopf.QuaternionPair

open OrbitEmbodiedState public

hopfSurface : OrbitEmbodiedState → ℚ
hopfSurface state = Hopf.pairHopfScalar (orientationPair state)

embodiedReach : OrbitEmbodiedState → Bool
embodiedReach (orbitEmbodiedState Reach.regulatedContext pair) = true
embodiedReach (orbitEmbodiedState Reach.mobilisedContext pair) = false

rotateState : Hopf.UnitQuaternion → OrbitEmbodiedState → OrbitEmbodiedState
rotateState unit state =
  orbitEmbodiedState
    (body state)
    (Hopf.rightMultiplyPair
      (orientationPair state)
      (Hopf.quaternionValue unit))

hopfSurfaceInvariantUnderRawOrientationOrbit :
  (unit : Hopf.UnitQuaternion) (state : OrbitEmbodiedState) →
  hopfSurface (rotateState unit state) ≡ hopfSurface state
hopfSurfaceInvariantUnderRawOrientationOrbit unit state =
  Hopf.hopfScalarRightUnitInvariant
    (orientationPair state)
    (Hopf.quaternionValue unit)
    (Hopf.unitNorm unit)

regulatedState : Hopf.QuaternionPair → OrbitEmbodiedState
regulatedState pair = orbitEmbodiedState Reach.regulatedContext pair

mobilisedRotatedState :
  Hopf.UnitQuaternion → Hopf.QuaternionPair → OrbitEmbodiedState
mobilisedRotatedState unit pair =
  orbitEmbodiedState Reach.mobilisedContext
    (Hopf.rightMultiplyPair pair (Hopf.quaternionValue unit))

sameRawInvariantDifferentEmbodiedReach :
  (unit : Hopf.UnitQuaternion) (pair : Hopf.QuaternionPair) →
  embodiedReach (regulatedState pair)
  ≡ embodiedReach (mobilisedRotatedState unit pair) → ⊥
sameRawInvariantDifferentEmbodiedReach unit pair ()

orbitEmbodiedReachNonfactorability :
  (unit : Hopf.UnitQuaternion) (pair : Hopf.QuaternionPair) →
  NF.NonFactorabilityWitness hopfSurface embodiedReach
orbitEmbodiedReachNonfactorability unit pair =
  NF.nonFactorabilityWitness
    (regulatedState pair)
    (mobilisedRotatedState unit pair)
    (sym (Hopf.hopfScalarRightUnitInvariant
      pair
      (Hopf.quaternionValue unit)
      (Hopf.unitNorm unit)))
    (sameRawInvariantDifferentEmbodiedReach unit pair)

hopfInvariantCannotDecodeEmbodiedReach :
  (unit : Hopf.UnitQuaternion) (pair : Hopf.QuaternionPair) →
  NF.FactorsThrough hopfSurface embodiedReach → ⊥
hopfInvariantCannotDecodeEmbodiedReach unit pair factor =
  NF.witnessRulesOutEveryFlatFactorisation
    (orbitEmbodiedReachNonfactorability unit pair)
    factor

record QuaternionEmbodiedReachBoundary : Set where
  constructor quaternionEmbodiedReachBoundary
  field
    unitQuaternionOrbitPreservesHopfObservable : Bool
    hopfObservableDeterminesEmbodiedReach : Bool
    rawPhysicalSymmetryImpliesFunctionalSymmetryForEveryConsumer : Bool
    quaternionCarrierIsCompleteNeuralState : Bool

canonicalQuaternionEmbodiedReachBoundary : QuaternionEmbodiedReachBoundary
canonicalQuaternionEmbodiedReachBoundary =
  quaternionEmbodiedReachBoundary true false false false

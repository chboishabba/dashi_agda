module DASHI.Moonshine.OggSSPP2Gamma04DrinfeldLevelNoGoExact where

------------------------------------------------------------------------
-- p=2 GAMMA0(4) SUPERSINGULAR DRINFELD-LEVEL NO-GO
--
-- CLASSICAL INPUT
--
-- Katz--Mazur / Bertolini--Darmon--Prasanna--Conrad:
-- a supersingular elliptic curve in characteristic p admits a unique Drinfeld
-- cyclic subgroup scheme of order p^r, namely ker(F^r).
--
-- At p=2,r=2 this means the supersingular Gamma0(4) level structure is unique
-- over the unique coarse supersingular elliptic curve.
--
-- DASHI CONSEQUENCE
--
-- The classical supersingular Gamma0(4) fibre therefore has one object at the
-- coarse/isomorphism-class level (with nontrivial stack automorphisms possibly
-- retained separately).  It cannot be the ten-component discrete retained-
-- orientation DASHI carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Core.ResidualSymmetryCollisionFibreExact as Action
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Orbit
import DASHI.Core.ActionOrbitRecognitionFunctorExact as Recognition
import DASHI.Moonshine.QuadraticApproximationPrimeCompressionBidiExact as Compression
import DASHI.Moonshine.OggSSPSmallCharacteristicResidualGroupoidExact as Target
import DASHI.Moonshine.OggSSPSmallCharacteristicClassicalSourceAtlasExact as Classical
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. One classical supersingular Gamma0(4) level object.
------------------------------------------------------------------------

data P2Gamma04SupersingularLevel : Set where
  frobeniusSquaredKernelLevel : P2Gamma04SupersingularLevel

unitCombine : ⊤ -> ⊤ -> ⊤
unitCombine tt tt = tt

unitInverse : ⊤ -> ⊤
unitInverse tt = tt

actClassical :
  ⊤ ->
  P2Gamma04SupersingularLevel ->
  P2Gamma04SupersingularLevel
actClassical tt level = level

classicalAction :
  Action.InvertibleSymmetryAction P2Gamma04SupersingularLevel ⊤
classicalAction =
  Action.invertibleSymmetryAction
    tt
    unitCombine
    unitInverse
    actClassical
    (λ level -> refl)
    (λ tt tt level -> refl)
    (λ tt level -> refl)
    (λ tt level -> refl)

classicalOrbitPresentation :
  Orbit.OrbitPresentation classicalAction
classicalOrbitPresentation =
  Orbit.orbitPresentation
    P2Gamma04SupersingularLevel
    (λ level -> level)
    (λ level -> level)
    (λ tt level -> refl)
    (λ level -> refl)
    (λ level -> tt)
    (λ level -> refl)

------------------------------------------------------------------------
-- 2. The retained DASHI target has at least two distinct orbit states.
------------------------------------------------------------------------

lowerTarget :
  Target.P2ResidualObject
lowerTarget =
  Compression.lowerSide , Triadic.zeroOrbit

upperTarget :
  Target.P2ResidualObject
upperTarget =
  Compression.upperSide , Triadic.zeroOrbit

lowerTargetNotUpperTarget :
  lowerTarget ≡ upperTarget -> ⊥
lowerTargetNotUpperTarget ()

------------------------------------------------------------------------
-- 3. No pi0-surjective recognition into the retained discrete target.
------------------------------------------------------------------------

data CandidateFunctor : Set₁ where
  candidateFunctor :
    (functor :
      Recognition.ActionRecognitionFunctor
        classicalAction
        Target.p2DiscreteAction)
    ->
    CandidateFunctor

noPi0SurjectionToRetainedTen :
  (functor :
    Recognition.ActionRecognitionFunctor
      classicalAction
      Target.p2DiscreteAction)
  ->
  (orbitRecognition :
    Recognition.OrbitRecognition
      functor
      classicalOrbitPresentation
      Target.p2DiscreteOrbitPresentation)
  ->
  Recognition.Pi0Surjection orbitRecognition
  ->
  ⊥
noPi0SurjectionToRetainedTen
    functor orbitRecognition surjection =
  lowerTargetNotUpperTarget lowerEqualsUpper
  where
    sourceOrbitForLower :
      P2Gamma04SupersingularLevel
    sourceOrbitForLower =
      Recognition.preimageOrbit surjection lowerTarget

    sourceOrbitForUpper :
      P2Gamma04SupersingularLevel
    sourceOrbitForUpper =
      Recognition.preimageOrbit surjection upperTarget

    uniqueSourceOrbit :
      sourceOrbitForLower ≡ sourceOrbitForUpper
    uniqueSourceOrbit = refl

    lowerHit :
      Recognition.mapOrbit orbitRecognition sourceOrbitForLower
      ≡ lowerTarget
    lowerHit =
      Recognition.hitsEveryTargetOrbit surjection lowerTarget

    upperHit :
      Recognition.mapOrbit orbitRecognition sourceOrbitForUpper
      ≡ upperTarget
    upperHit =
      Recognition.hitsEveryTargetOrbit surjection upperTarget

    lowerEqualsUpper :
      lowerTarget ≡ upperTarget
    lowerEqualsUpper =
      trans
        (sym lowerHit)
        (trans
          (cong (Recognition.mapOrbit orbitRecognition) uniqueSourceOrbit)
          upperHit)

noFullRecognitionToRetainedTen :
  (functor :
    Recognition.ActionRecognitionFunctor
      classicalAction
      Target.p2DiscreteAction)
  ->
  Recognition.OrbitStabilizerRecognition
    functor
    classicalOrbitPresentation
    Target.p2DiscreteOrbitPresentation
  ->
  ⊥
noFullRecognitionToRetainedTen functor full =
  noPi0SurjectionToRetainedTen
    functor
    (Recognition.orbitRecognition full)
    (Recognition.pi0Surjection full)

------------------------------------------------------------------------
-- 4. Attribution and interpretation.
------------------------------------------------------------------------

classicalBoundary :
  Classical.SmallCharacteristicClassicalSourcingBoundary
classicalBoundary =
  Classical.canonicalSmallCharacteristicClassicalSourcingBoundary

data TenDASHIStatesAreTenGamma04LevelStructures : Set where
data UniqueLevelObjectMeansTrivialStackAutomorphism : Set where
data Gamma04NoGoRejectsAllPossibleCMOrientations : Set where

tenDASHIStatesAreNotTenGamma04LevelStructures :
  TenDASHIStatesAreTenGamma04LevelStructures -> ⊥
tenDASHIStatesAreNotTenGamma04LevelStructures ()

uniqueLevelObjectDoesNotKillStackAutomorphisms :
  UniqueLevelObjectMeansTrivialStackAutomorphism -> ⊥
uniqueLevelObjectDoesNotKillStackAutomorphisms ()

gamma04NoGoDoesNotRejectRicherCMOrientations :
  Gamma04NoGoRejectsAllPossibleCMOrientations -> ⊥
gamma04NoGoDoesNotRejectRicherCMOrientations ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction

record P2Gamma04DrinfeldLevelNoGoBoundary : Set where
  constructor p2-gamma04-drinfeld-level-no-go-boundary
  field
    uniqueSupersingularCoarseCurveClassicallySourced : Bool
    uniqueOrderFourDrinfeldCyclicSubgroupClassicallySourced : Bool
    oneCoarseGamma04LevelObjectConstructed : Bool
    retainedDASHITargetHasMultipleDistinctComponents : Bool
    pi0SurjectiveRecognitionToTenBlocked : Bool
    fullRecognitionToTenBlocked : Bool
    tenStatesIdentifiedWithGamma04Points : Bool
    stackAutomorphismsErasedByOneObjectStatement : Bool
    richerOrientedCMMarkedObjectStillOpen : Bool

canonicalP2Gamma04DrinfeldLevelNoGoBoundary :
  P2Gamma04DrinfeldLevelNoGoBoundary
canonicalP2Gamma04DrinfeldLevelNoGoBoundary =
  p2-gamma04-drinfeld-level-no-go-boundary
    true true true true true true false false true

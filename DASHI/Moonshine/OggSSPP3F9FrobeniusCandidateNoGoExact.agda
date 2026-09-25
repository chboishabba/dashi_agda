module DASHI.Moonshine.OggSSPP3F9FrobeniusCandidateNoGoExact where

------------------------------------------------------------------------
-- p=3 F9/F3 FROBENIUS CANDIDATE: EXACT FINITE NEGATIVE CONTROL
--
-- The existing p3 receipt records F9/F3 and Frobenius group Z/2.  This module
-- constructs the literal nine-element extension-field-shaped carrier
--
--   F9 ~= F3[alpha]/(alpha^2+1)
--
-- only at the finite coordinate level needed for Frobenius:
--
--   (a,b) |-> (a,-b).
--
-- Its orbit carrier has six components:
--   three fixed F3 points (b=0) and three conjugate pairs (b=+/-1).
--
-- Therefore the whole F9 point carrier cannot be the arithmetic source for a
-- full recognition into the current p=3 369 target, which has two components.
-- This does NOT rule out a marked quotient/subcarrier derived from F9.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Core.OrbitStabilizerResidualPresentationExact as Generic
import DASHI.Core.ResidualSymmetryCollisionFibreExact as Symmetry
import DASHI.Core.ActionOrbitRecognitionFunctorExact as Recognition
import DASHI.Foundations.BalancedTernaryOrbitStabilizerResidualBridgeExact as C2
import DASHI.Moonshine.OggSSPSmallCharacteristicResidualGroupoidExact as Small
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Source

------------------------------------------------------------------------
-- 1. Three-element base coordinate and nine-element extension carrier.
------------------------------------------------------------------------

data F3 : Set where
  z3 o3 t3 : F3

neg3 : F3 -> F3
neg3 z3 = z3
neg3 o3 = t3
neg3 t3 = o3

neg3Involutive : (x : F3) -> neg3 (neg3 x) ≡ x
neg3Involutive z3 = refl
neg3Involutive o3 = refl
neg3Involutive t3 = refl

data F9Point : Set where
  f9 : F3 -> F3 -> F9Point

frobenius3 : F9Point -> F9Point
frobenius3 (f9 a b) = f9 a (neg3 b)

frobenius3Involutive :
  (x : F9Point) ->
  frobenius3 (frobenius3 x) ≡ x
frobenius3Involutive (f9 a b)
  rewrite neg3Involutive b = refl

------------------------------------------------------------------------
-- 2. Literal C2 action.
------------------------------------------------------------------------

actF9 : C2.C2 -> F9Point -> F9Point
actF9 C2.identity x = x
actF9 C2.flip x = frobenius3 x

identityActsF9 :
  (x : F9Point) ->
  actF9 C2.identity x ≡ x
identityActsF9 x = refl

combineActsF9 :
  (g h : C2.C2) (x : F9Point) ->
  actF9 (C2.combineC2 g h) x
  ≡ actF9 g (actF9 h x)
combineActsF9 C2.identity h x = refl
combineActsF9 C2.flip C2.identity x = refl
combineActsF9 C2.flip C2.flip x =
  frobenius3Involutive x

inverseLeftF9 :
  (g : C2.C2) (x : F9Point) ->
  actF9 (C2.inverseC2 g) (actF9 g x) ≡ x
inverseLeftF9 C2.identity x = refl
inverseLeftF9 C2.flip x = frobenius3Involutive x

inverseRightF9 :
  (g : C2.C2) (x : F9Point) ->
  actF9 g (actF9 (C2.inverseC2 g) x) ≡ x
inverseRightF9 C2.identity x = refl
inverseRightF9 C2.flip x = frobenius3Involutive x

f9FrobeniusAction :
  Symmetry.InvertibleSymmetryAction F9Point C2.C2
f9FrobeniusAction =
  Symmetry.invertibleSymmetryAction
    C2.identity
    C2.combineC2
    C2.inverseC2
    actF9
    identityActsF9
    combineActsF9
    inverseLeftF9
    inverseRightF9

------------------------------------------------------------------------
-- 3. Exact six-orbit presentation.
------------------------------------------------------------------------

data F9FrobeniusOrbit : Set where
  fixed0 fixed1 fixed2 : F9FrobeniusOrbit
  pair0 pair1 pair2 : F9FrobeniusOrbit

classifyF9 : F9Point -> F9FrobeniusOrbit
classifyF9 (f9 z3 z3) = fixed0
classifyF9 (f9 o3 z3) = fixed1
classifyF9 (f9 t3 z3) = fixed2
classifyF9 (f9 z3 o3) = pair0
classifyF9 (f9 z3 t3) = pair0
classifyF9 (f9 o3 o3) = pair1
classifyF9 (f9 o3 t3) = pair1
classifyF9 (f9 t3 o3) = pair2
classifyF9 (f9 t3 t3) = pair2

representativeF9 : F9FrobeniusOrbit -> F9Point
representativeF9 fixed0 = f9 z3 z3
representativeF9 fixed1 = f9 o3 z3
representativeF9 fixed2 = f9 t3 z3
representativeF9 pair0 = f9 z3 o3
representativeF9 pair1 = f9 o3 o3
representativeF9 pair2 = f9 t3 o3

orbitInvariantF9 :
  (g : C2.C2) (x : F9Point) ->
  classifyF9 (actF9 g x) ≡ classifyF9 x
orbitInvariantF9 C2.identity x = refl
orbitInvariantF9 C2.flip (f9 z3 z3) = refl
orbitInvariantF9 C2.flip (f9 o3 z3) = refl
orbitInvariantF9 C2.flip (f9 t3 z3) = refl
orbitInvariantF9 C2.flip (f9 z3 o3) = refl
orbitInvariantF9 C2.flip (f9 z3 t3) = refl
orbitInvariantF9 C2.flip (f9 o3 o3) = refl
orbitInvariantF9 C2.flip (f9 o3 t3) = refl
orbitInvariantF9 C2.flip (f9 t3 o3) = refl
orbitInvariantF9 C2.flip (f9 t3 t3) = refl

representativeReturnsF9Orbit :
  (o : F9FrobeniusOrbit) ->
  classifyF9 (representativeF9 o) ≡ o
representativeReturnsF9Orbit fixed0 = refl
representativeReturnsF9Orbit fixed1 = refl
representativeReturnsF9Orbit fixed2 = refl
representativeReturnsF9Orbit pair0 = refl
representativeReturnsF9Orbit pair1 = refl
representativeReturnsF9Orbit pair2 = refl

transporterF9 : F9Point -> C2.C2
transporterF9 (f9 a z3) = C2.identity
transporterF9 (f9 a o3) = C2.identity
transporterF9 (f9 a t3) = C2.flip

transporterHitsF9 :
  (x : F9Point) ->
  actF9 (transporterF9 x)
    (representativeF9 (classifyF9 x))
  ≡ x
transporterHitsF9 (f9 z3 z3) = refl
transporterHitsF9 (f9 o3 z3) = refl
transporterHitsF9 (f9 t3 z3) = refl
transporterHitsF9 (f9 z3 o3) = refl
transporterHitsF9 (f9 z3 t3) = refl
transporterHitsF9 (f9 o3 o3) = refl
transporterHitsF9 (f9 o3 t3) = refl
transporterHitsF9 (f9 t3 o3) = refl
transporterHitsF9 (f9 t3 t3) = refl

f9FrobeniusOrbitPresentation :
  Generic.OrbitPresentation f9FrobeniusAction
f9FrobeniusOrbitPresentation =
  Generic.orbitPresentation
    F9FrobeniusOrbit
    classifyF9
    representativeF9
    orbitInvariantF9
    representativeReturnsF9Orbit
    transporterF9
    transporterHitsF9

------------------------------------------------------------------------
-- 4. Six source components cannot inject into the two target components.
------------------------------------------------------------------------

fixed0NotFixed1 : fixed0 ≡ fixed1 -> ⊥
fixed0NotFixed1 ()

fixed0NotFixed2 : fixed0 ≡ fixed2 -> ⊥
fixed0NotFixed2 ()

fixed1NotFixed2 : fixed1 ≡ fixed2 -> ⊥
fixed1NotFixed2 ()

noInjectiveF9OrbitToP3Target :
  (mapOrbit : F9FrobeniusOrbit -> Small.ConstantTernaryOrbit) ->
  ((left right : F9FrobeniusOrbit) ->
    mapOrbit left ≡ mapOrbit right ->
    left ≡ right) ->
  ⊥
noInjectiveF9OrbitToP3Target mapOrbit injective
  with mapOrbit fixed0 | mapOrbit fixed1 | mapOrbit fixed2
... | Small.zeroConstantOrbit | Small.zeroConstantOrbit | _ =
  fixed0NotFixed1 (injective fixed0 fixed1 refl)
... | Small.zeroConstantOrbit | Small.nonzeroConstantOrbit | Small.zeroConstantOrbit =
  fixed0NotFixed2 (injective fixed0 fixed2 refl)
... | Small.zeroConstantOrbit | Small.nonzeroConstantOrbit | Small.nonzeroConstantOrbit =
  fixed1NotFixed2 (injective fixed1 fixed2 refl)
... | Small.nonzeroConstantOrbit | Small.zeroConstantOrbit | Small.zeroConstantOrbit =
  fixed1NotFixed2 (injective fixed1 fixed2 refl)
... | Small.nonzeroConstantOrbit | Small.zeroConstantOrbit | Small.nonzeroConstantOrbit =
  fixed0NotFixed2 (injective fixed0 fixed2 refl)
... | Small.nonzeroConstantOrbit | Small.nonzeroConstantOrbit | _ =
  fixed0NotFixed1 (injective fixed0 fixed1 refl)

------------------------------------------------------------------------
-- 5. No full arithmetic -> 369 recognition can use the whole F9 carrier.
------------------------------------------------------------------------

noFullF9FrobeniusRecognitionToP3 :
  (functor :
    Recognition.ActionRecognitionFunctor
      f9FrobeniusAction
      Small.constantC2Action) ->
  Recognition.OrbitStabilizerRecognition
    functor
    f9FrobeniusOrbitPresentation
    Small.constantTernaryOrbitPresentation ->
  ⊥
noFullF9FrobeniusRecognitionToP3 functor full =
  noInjectiveF9OrbitToP3Target
    (Recognition.mapOrbit orbitRecognition)
    injectiveOrbitMap
  where
    orbitRecognition :
      Recognition.OrbitRecognition
        functor
        f9FrobeniusOrbitPresentation
        Small.constantTernaryOrbitPresentation
    orbitRecognition =
      Recognition.orbitRecognition full

    injectiveOrbitMap :
      (left right : F9FrobeniusOrbit) ->
      Recognition.mapOrbit orbitRecognition left
      ≡ Recognition.mapOrbit orbitRecognition right ->
      left ≡ right
    injectiveOrbitMap left right same =
      Recognition.reflectsOrbitEquality
        (Recognition.pi0Embedding full)
        same

------------------------------------------------------------------------
-- 6. Boundary.
------------------------------------------------------------------------

candidateClaimOrigin : Source.ClaimOrigin
candidateClaimOrigin = Source.repositoryFormalReconstruction

record P3F9FrobeniusCandidateBoundary : Set where
  constructor p3-f9-frobenius-candidate-boundary
  field
    literalNinePointCarrierConstructed : Bool
    literalOrderTwoFrobeniusActionConstructed : Bool
    exactSixOrbitPresentationConstructed : Bool
    fullRecognitionNoGoProvedAtRecognitionInterface : Bool
    wholeF9CarrierCanFullyRecognizeTwoOrbit369Target : Bool
    markedQuotientOrSubcarrierStillOpen : Bool
    actualSupersingularMarkedCarrierIdentifiedHere : Bool

canonicalP3F9FrobeniusCandidateBoundary :
  P3F9FrobeniusCandidateBoundary
canonicalP3F9FrobeniusCandidateBoundary =
  p3-f9-frobenius-candidate-boundary
    true true true true false true false

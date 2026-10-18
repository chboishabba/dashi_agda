module DASHI.Moonshine.OggSSPP2OrientedInertiaTenStateRecognitionExact where

------------------------------------------------------------------------
-- p=2 ORIENTED-INERTIA TEN-STATE RECOGNITION
--
-- CLASSICAL FACTORS
--
-- (A) Goren--Love: every imaginary quadratic discriminant has exactly two
--     oriented quadratic orders up to oriented isomorphism, exchanged by
--     nontrivial Galois.
--
-- (B) the characteristic-2 supersingular automorphism group is binary
--     tetrahedral; its seven conjugacy classes yield five inversion-orbits
--     under the repository's explicit inversion quotient.
--
-- DASHI CONSTRUCTION
--
-- Their product is therefore a ten-state enriched marking carrier:
--
--     two oriented-order sheets x five inertia inversion-orbits.
--
-- We prove an exact two-sided rechart to the existing P2CMMarkedState.
--
-- This is NOT the Gamma0(4) supersingular level fibre (which has one Drinfeld
-- cyclic level object), and no source is credited with the product itself or
-- with its identification with Base369 labels.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)

import DASHI.Core.ResidualSymmetryCollisionFibreExact as Action
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Orbit
import DASHI.Core.ActionOrbitRecognitionFunctorExact as Recognition
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Inertia
import DASHI.Moonshine.OggSSPP2RetainedCMMarkedSourceExact as P2Source
import DASHI.Moonshine.OggSSPSmallCharacteristicClassicalSourceAtlasExact as Classical
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Two classical orientation labels.
------------------------------------------------------------------------

data ClassicalQuadraticOrientation : Set where
  firstGaloisOrientation : ClassicalQuadraticOrientation
  conjugateGaloisOrientation : ClassicalQuadraticOrientation

conjugateOrientation :
  ClassicalQuadraticOrientation ->
  ClassicalQuadraticOrientation
conjugateOrientation firstGaloisOrientation = conjugateGaloisOrientation
conjugateOrientation conjugateGaloisOrientation = firstGaloisOrientation

conjugateOrientationInvolutive :
  (orientation : ClassicalQuadraticOrientation) ->
  conjugateOrientation (conjugateOrientation orientation) ≡ orientation
conjugateOrientationInvolutive firstGaloisOrientation = refl
conjugateOrientationInvolutive conjugateGaloisOrientation = refl

------------------------------------------------------------------------
-- 2. Ten-state enriched carrier.
------------------------------------------------------------------------

P2OrientedInertiaState : Set
P2OrientedInertiaState =
  ClassicalQuadraticOrientation × Inertia.BinaryTetrahedralInversionOrbit

orientationToCM :
  ClassicalQuadraticOrientation ->
  P2Source.CMOrientation
orientationToCM firstGaloisOrientation = P2Source.cmLower
orientationToCM conjugateGaloisOrientation = P2Source.cmUpper

cmToOrientation :
  P2Source.CMOrientation ->
  ClassicalQuadraticOrientation
cmToOrientation P2Source.cmLower = firstGaloisOrientation
cmToOrientation P2Source.cmUpper = conjugateGaloisOrientation

orientationRoundTrip :
  (orientation : ClassicalQuadraticOrientation) ->
  cmToOrientation (orientationToCM orientation) ≡ orientation
orientationRoundTrip firstGaloisOrientation = refl
orientationRoundTrip conjugateGaloisOrientation = refl

cmRoundTrip :
  (orientation : P2Source.CMOrientation) ->
  orientationToCM (cmToOrientation orientation) ≡ orientation
cmRoundTrip P2Source.cmLower = refl
cmRoundTrip P2Source.cmUpper = refl

toP2CMMarkedState :
  P2OrientedInertiaState ->
  P2Source.P2CMMarkedState
toP2CMMarkedState (orientation , inertiaOrbit) =
  P2Source.cm-marked-state
    (orientationToCM orientation)
    (Inertia.inertiaToNineOrbit inertiaOrbit)

fromP2CMMarkedState :
  P2Source.P2CMMarkedState ->
  P2OrientedInertiaState
fromP2CMMarkedState (P2Source.cm-marked-state orientation orbit) =
  cmToOrientation orientation ,
  Inertia.nineOrbitToInertia orbit

orientedInertiaRoundTrip :
  (state : P2OrientedInertiaState) ->
  fromP2CMMarkedState (toP2CMMarkedState state) ≡ state
orientedInertiaRoundTrip (firstGaloisOrientation , Inertia.identityInertiaOrbit) = refl
orientedInertiaRoundTrip (firstGaloisOrientation , Inertia.centralMinusOneInertiaOrbit) = refl
orientedInertiaRoundTrip (firstGaloisOrientation , Inertia.orderFourInertiaOrbit) = refl
orientedInertiaRoundTrip (firstGaloisOrientation , Inertia.orderThreePairInertiaOrbit) = refl
orientedInertiaRoundTrip (firstGaloisOrientation , Inertia.orderSixPairInertiaOrbit) = refl
orientedInertiaRoundTrip (conjugateGaloisOrientation , Inertia.identityInertiaOrbit) = refl
orientedInertiaRoundTrip (conjugateGaloisOrientation , Inertia.centralMinusOneInertiaOrbit) = refl
orientedInertiaRoundTrip (conjugateGaloisOrientation , Inertia.orderFourInertiaOrbit) = refl
orientedInertiaRoundTrip (conjugateGaloisOrientation , Inertia.orderThreePairInertiaOrbit) = refl
orientedInertiaRoundTrip (conjugateGaloisOrientation , Inertia.orderSixPairInertiaOrbit) = refl

p2CMRoundTrip :
  (state : P2Source.P2CMMarkedState) ->
  toP2CMMarkedState (fromP2CMMarkedState state) ≡ state
p2CMRoundTrip (P2Source.cm-marked-state P2Source.cmLower orbit)
  rewrite Inertia.nineOrbitRoundTrip orbit = refl
p2CMRoundTrip (P2Source.cm-marked-state P2Source.cmUpper orbit)
  rewrite Inertia.nineOrbitRoundTrip orbit = refl

toP2CMMarkedStateInjective :
  {left right : P2OrientedInertiaState} ->
  toP2CMMarkedState left ≡ toP2CMMarkedState right ->
  left ≡ right
toP2CMMarkedStateInjective {left} {right} same =
  trans
    (sym (orientedInertiaRoundTrip left))
    (trans
      (cong fromP2CMMarkedState same)
      (orientedInertiaRoundTrip right))

------------------------------------------------------------------------
-- 3. Discrete groupoid recognition into the existing ten-state source.
------------------------------------------------------------------------

unitCombine : ⊤ -> ⊤ -> ⊤
unitCombine tt tt = tt

unitInverse : ⊤ -> ⊤
unitInverse tt = tt

actOrientedInertia :
  ⊤ ->
  P2OrientedInertiaState ->
  P2OrientedInertiaState
actOrientedInertia tt state = state

orientedInertiaAction :
  Action.InvertibleSymmetryAction P2OrientedInertiaState ⊤
orientedInertiaAction =
  Action.invertibleSymmetryAction
    tt
    unitCombine
    unitInverse
    actOrientedInertia
    (λ state -> refl)
    (λ tt tt state -> refl)
    (λ tt state -> refl)
    (λ tt state -> refl)

orientedInertiaOrbits :
  Orbit.OrbitPresentation orientedInertiaAction
orientedInertiaOrbits =
  Orbit.orbitPresentation
    P2OrientedInertiaState
    (λ state -> state)
    (λ state -> state)
    (λ tt state -> refl)
    (λ state -> refl)
    (λ state -> tt)
    (λ state -> refl)

orientedInertiaActionRecognition :
  Recognition.ActionRecognitionFunctor
    orientedInertiaAction
    P2Source.p2CMAction
orientedInertiaActionRecognition =
  Recognition.action-recognition-functor
    toP2CMMarkedState
    (λ tt -> tt)
    refl
    (λ tt tt -> refl)
    (λ tt -> refl)
    (λ tt state -> refl)

orientedInertiaOrbitRecognition :
  Recognition.OrbitRecognition
    orientedInertiaActionRecognition
    orientedInertiaOrbits
    P2Source.p2CMOrbitPresentation
orientedInertiaOrbitRecognition =
  Recognition.orbit-recognition
    toP2CMMarkedState
    (λ state -> refl)

orientedInertiaPi0Embedding :
  Recognition.Pi0Embedding orientedInertiaOrbitRecognition
orientedInertiaPi0Embedding =
  Recognition.pi0-embedding
    toP2CMMarkedStateInjective

orientedInertiaPi0Surjection :
  Recognition.Pi0Surjection orientedInertiaOrbitRecognition
orientedInertiaPi0Surjection =
  Recognition.pi0-surjection
    fromP2CMMarkedState
    p2CMRoundTrip

orientedInertiaStabilizerRecognition :
  Recognition.StabilizerRecognition orientedInertiaOrbitRecognition
orientedInertiaStabilizerRecognition =
  Recognition.stabilizer-recognition
    (λ state -> refl)
    (λ state tt fixed -> refl)
    (λ state tt fixed -> refl)

orientedInertiaFullRecognition :
  Recognition.OrbitStabilizerRecognition
    orientedInertiaActionRecognition
    orientedInertiaOrbits
    P2Source.p2CMOrbitPresentation
orientedInertiaFullRecognition =
  Recognition.orbit-stabilizer-recognition
    orientedInertiaOrbitRecognition
    orientedInertiaPi0Embedding
    orientedInertiaPi0Surjection
    orientedInertiaStabilizerRecognition

------------------------------------------------------------------------
-- 4. Attribution boundary.
------------------------------------------------------------------------

classicalBoundary :
  Classical.SmallCharacteristicClassicalSourcingBoundary
classicalBoundary =
  Classical.canonicalSmallCharacteristicClassicalSourcingBoundary

data ProductIsNamedClassicalModuliStack : Set where
data FiveInertiaLabelsHaveBase369Semantics : Set where
data TwoOrientationsAreTenGamma04LevelPoints : Set where
data ProductConstructionProvesMonsterArithmetic : Set where

productNotPromotedToNamedClassicalModuliStack :
  ProductIsNamedClassicalModuliStack -> ⊥
productNotPromotedToNamedClassicalModuliStack ()

inertiaLabelsDoNotAcquireBase369Semantics :
  FiveInertiaLabelsHaveBase369Semantics -> ⊥
inertiaLabelsDoNotAcquireBase369Semantics ()

twoOrientationsDoNotCreateGamma04LevelPoints :
  TwoOrientationsAreTenGamma04LevelPoints -> ⊥
twoOrientationsDoNotCreateGamma04LevelPoints ()

productConstructionDoesNotProveMonsterArithmetic :
  ProductConstructionProvesMonsterArithmetic -> ⊥
productConstructionDoesNotProveMonsterArithmetic ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record P2OrientedInertiaTenStateBoundary : Set where
  constructor p2-oriented-inertia-ten-state-boundary
  field
    twoOrientationFactorClassicallySourced : Bool
    sevenBinaryTetrahedralClassesClassicallySourced : Bool
    fiveInversionOrbitFactorConstructed : Bool
    exactTwoTimesFiveCarrierConstructed : Bool
    exactTenStateRechartToP2CMSourceProved : Bool
    fullDiscreteRecognitionProved : Bool
    namedClassicalModuliObjectIdentified : Bool
    gamma04LevelFibreIdentified : Bool
    base369SemanticIdentityClaimed : Bool
    monsterArithmeticIdentityClaimed : Bool

canonicalP2OrientedInertiaTenStateBoundary :
  P2OrientedInertiaTenStateBoundary
canonicalP2OrientedInertiaTenStateBoundary =
  p2-oriented-inertia-ten-state-boundary
    true true true true true true false false false false

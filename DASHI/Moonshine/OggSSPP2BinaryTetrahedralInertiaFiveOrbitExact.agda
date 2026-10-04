module DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact where

------------------------------------------------------------------------
-- p=2 BINARY-TETRAHEDRAL INERTIA FIVE-ORBIT CARRIER
--
-- CLASSICAL INPUT
--
-- The unique supersingular elliptic curve in characteristic 2 has automorphism
-- group the binary tetrahedral group 2T ~= SL2(F3), of order 24.
--
-- Dadhwal--Pankaj list its seven conjugacy classes.
--
-- DASHI RECONSTRUCTION
--
-- Inversion on automorphisms fixes the identity, central -1, and the order-4
-- class, while pairing the two order-3 classes and the two order-6 classes.
-- Therefore conjugacy classes modulo inversion have exactly five classes.
--
-- This five-element carrier is a natural inertia/orbifold donor for the p=2
-- residual.  The later rechart to NineOrbit is a finite-carrier recognition,
-- NOT a semantic identification of group-theoretic class labels with Base369
-- axis/diagonal labels.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Moonshine.OggSSPSmallCharacteristicClassicalSourceAtlasExact as Classical
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Seven binary-tetrahedral conjugacy classes.
------------------------------------------------------------------------

data BinaryTetrahedralConjugacyClass : Set where
  identityClass : BinaryTetrahedralConjugacyClass
  centralMinusOneClass : BinaryTetrahedralConjugacyClass
  orderFourClass : BinaryTetrahedralConjugacyClass
  orderThreePositiveClass : BinaryTetrahedralConjugacyClass
  orderThreeNegativeClass : BinaryTetrahedralConjugacyClass
  orderSixPositiveClass : BinaryTetrahedralConjugacyClass
  orderSixNegativeClass : BinaryTetrahedralConjugacyClass

inverseClass :
  BinaryTetrahedralConjugacyClass ->
  BinaryTetrahedralConjugacyClass
inverseClass identityClass = identityClass
inverseClass centralMinusOneClass = centralMinusOneClass
inverseClass orderFourClass = orderFourClass
inverseClass orderThreePositiveClass = orderThreeNegativeClass
inverseClass orderThreeNegativeClass = orderThreePositiveClass
inverseClass orderSixPositiveClass = orderSixNegativeClass
inverseClass orderSixNegativeClass = orderSixPositiveClass

inverseClassInvolutive :
  (class : BinaryTetrahedralConjugacyClass) ->
  inverseClass (inverseClass class) ≡ class
inverseClassInvolutive identityClass = refl
inverseClassInvolutive centralMinusOneClass = refl
inverseClassInvolutive orderFourClass = refl
inverseClassInvolutive orderThreePositiveClass = refl
inverseClassInvolutive orderThreeNegativeClass = refl
inverseClassInvolutive orderSixPositiveClass = refl
inverseClassInvolutive orderSixNegativeClass = refl

------------------------------------------------------------------------
-- 2. Five inversion-orbits of conjugacy classes.
------------------------------------------------------------------------

data BinaryTetrahedralInversionOrbit : Set where
  identityInertiaOrbit : BinaryTetrahedralInversionOrbit
  centralMinusOneInertiaOrbit : BinaryTetrahedralInversionOrbit
  orderFourInertiaOrbit : BinaryTetrahedralInversionOrbit
  orderThreePairInertiaOrbit : BinaryTetrahedralInversionOrbit
  orderSixPairInertiaOrbit : BinaryTetrahedralInversionOrbit

quotientByInversion :
  BinaryTetrahedralConjugacyClass ->
  BinaryTetrahedralInversionOrbit
quotientByInversion identityClass = identityInertiaOrbit
quotientByInversion centralMinusOneClass = centralMinusOneInertiaOrbit
quotientByInversion orderFourClass = orderFourInertiaOrbit
quotientByInversion orderThreePositiveClass = orderThreePairInertiaOrbit
quotientByInversion orderThreeNegativeClass = orderThreePairInertiaOrbit
quotientByInversion orderSixPositiveClass = orderSixPairInertiaOrbit
quotientByInversion orderSixNegativeClass = orderSixPairInertiaOrbit

quotientByInversionInvariant :
  (class : BinaryTetrahedralConjugacyClass) ->
  quotientByInversion (inverseClass class)
  ≡ quotientByInversion class
quotientByInversionInvariant identityClass = refl
quotientByInversionInvariant centralMinusOneClass = refl
quotientByInversionInvariant orderFourClass = refl
quotientByInversionInvariant orderThreePositiveClass = refl
quotientByInversionInvariant orderThreeNegativeClass = refl
quotientByInversionInvariant orderSixPositiveClass = refl
quotientByInversionInvariant orderSixNegativeClass = refl

------------------------------------------------------------------------
-- 3. Exact five-carrier rechart to NineOrbit.
--
-- The assignment is deliberately just a bijection.  No semantic equivalence
-- between the labels is claimed.
------------------------------------------------------------------------

inertiaToNineOrbit :
  BinaryTetrahedralInversionOrbit ->
  Triadic.NineOrbit
inertiaToNineOrbit identityInertiaOrbit = Triadic.zeroOrbit
inertiaToNineOrbit centralMinusOneInertiaOrbit = Triadic.firstAxisOrbit
inertiaToNineOrbit orderFourInertiaOrbit = Triadic.secondAxisOrbit
inertiaToNineOrbit orderThreePairInertiaOrbit = Triadic.equalSignOrbit
inertiaToNineOrbit orderSixPairInertiaOrbit = Triadic.oppositeSignOrbit

nineOrbitToInertia :
  Triadic.NineOrbit ->
  BinaryTetrahedralInversionOrbit
nineOrbitToInertia Triadic.zeroOrbit = identityInertiaOrbit
nineOrbitToInertia Triadic.firstAxisOrbit = centralMinusOneInertiaOrbit
nineOrbitToInertia Triadic.secondAxisOrbit = orderFourInertiaOrbit
nineOrbitToInertia Triadic.equalSignOrbit = orderThreePairInertiaOrbit
nineOrbitToInertia Triadic.oppositeSignOrbit = orderSixPairInertiaOrbit

inertiaRoundTrip :
  (orbit : BinaryTetrahedralInversionOrbit) ->
  nineOrbitToInertia (inertiaToNineOrbit orbit) ≡ orbit
inertiaRoundTrip identityInertiaOrbit = refl
inertiaRoundTrip centralMinusOneInertiaOrbit = refl
inertiaRoundTrip orderFourInertiaOrbit = refl
inertiaRoundTrip orderThreePairInertiaOrbit = refl
inertiaRoundTrip orderSixPairInertiaOrbit = refl

nineOrbitRoundTrip :
  (orbit : Triadic.NineOrbit) ->
  inertiaToNineOrbit (nineOrbitToInertia orbit) ≡ orbit
nineOrbitRoundTrip Triadic.zeroOrbit = refl
nineOrbitRoundTrip Triadic.firstAxisOrbit = refl
nineOrbitRoundTrip Triadic.secondAxisOrbit = refl
nineOrbitRoundTrip Triadic.equalSignOrbit = refl
nineOrbitRoundTrip Triadic.oppositeSignOrbit = refl

------------------------------------------------------------------------
-- 4. Attribution boundary.
------------------------------------------------------------------------

classicalBoundary :
  Classical.SmallCharacteristicClassicalSourcingBoundary
classicalBoundary =
  Classical.canonicalSmallCharacteristicClassicalSourcingBoundary

data BinaryTetrahedralClassMeansNineOrbitSemantics : Set where
data SevenClassSourceStatesFiveOrbitQuotient : Set where
data InertiaFiveOrbitIsGamma04LevelFibre : Set where

binaryTetrahedralClassDoesNotCreateNineOrbitSemantics :
  BinaryTetrahedralClassMeansNineOrbitSemantics -> ⊥
binaryTetrahedralClassDoesNotCreateNineOrbitSemantics ()

sevenClassSourceDoesNotStateFiveOrbitQuotient :
  SevenClassSourceStatesFiveOrbitQuotient -> ⊥
sevenClassSourceDoesNotStateFiveOrbitQuotient ()

inertiaFiveOrbitIsNotGamma04LevelFibre :
  InertiaFiveOrbitIsGamma04LevelFibre -> ⊥
inertiaFiveOrbitIsNotGamma04LevelFibre ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record P2BinaryTetrahedralInertiaFiveOrbitBoundary : Set where
  constructor p2-binary-tetrahedral-inertia-five-orbit-boundary
  field
    binaryTetrahedralAutomorphismGroupClassicallySourced : Bool
    sevenConjugacyClassesClassicallySourced : Bool
    inversionActionExplicitlyReconstructed : Bool
    fiveInversionOrbitsProved : Bool
    exactFiveCarrierRechartToNineOrbitProved : Bool
    semanticIdentityWithNineOrbitClaimed : Bool
    gamma04LevelFibreIdentityClaimed : Bool

canonicalP2BinaryTetrahedralInertiaFiveOrbitBoundary :
  P2BinaryTetrahedralInertiaFiveOrbitBoundary
canonicalP2BinaryTetrahedralInertiaFiveOrbitBoundary =
  p2-binary-tetrahedral-inertia-five-orbit-boundary
    true true true true true false false

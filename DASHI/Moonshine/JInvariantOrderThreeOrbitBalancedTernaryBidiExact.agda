module DASHI.Moonshine.JInvariantOrderThreeOrbitBalancedTernaryBidiExact where

------------------------------------------------------------------------
-- KLEIN-j ORDER-THREE ORBIT / BALANCED-TERNARY / BIDI
--
-- The upper-half-plane j plot has an order-three zero at
--   rho = exp(2*pi*i/3) = -1/2 + i*sqrt(3)/2,
-- and j is modular invariant.  For the modular family
--
--   gamma_k = [ 1  1 ; k  k+1 ]
--
-- direct algebra gives the orbit coordinates
--
--   Re(gamma_k rho) = (2k+1) / (2 (k^2+k+1))
--   Im(gamma_k rho) = sqrt(3) / (2 (k^2+k+1)).
--
-- This module keeps that exact Q(sqrt(3))-coordinate shape separate from the
-- still-missing same-object proof that the symbolic coordinate carrier is the
-- analytic Mobius action used by the rendered image.
--
-- The image observation around |Re tau| ~= 0.15 becomes a theorem-shaped
-- arithmetic cut: k=0..6 lie on/outside 3/20 in this family, while k=7 is
-- already inside.  Whether the user's chosen visible beam is exactly this
-- whole family remains a same-object acquisition coordinate.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Moonshine.JInvariantSourceAtlasExact as Sources

------------------------------------------------------------------------
-- 1. One balanced trit, two consumer interpretations.
--
-- We keep all three-way semantics on the canonical KernelTrit carrier.
------------------------------------------------------------------------

data SeamDynamics : Set where
  convergingSeam : SeamDynamics
  seamIdentity : SeamDynamics
  divergingSeam : SeamDynamics

seamDynamics : Triadic.KernelTrit → SeamDynamics
seamDynamics Triadic.negativeTrit = convergingSeam
seamDynamics Triadic.zeroTrit = seamIdentity
seamDynamics Triadic.positiveTrit = divergingSeam

data GluingDynamics : Set where
  antiCommutingGluing : GluingDynamics
  gluingIdentity : GluingDynamics
  commutingGluing : GluingDynamics

gluingDynamics : Triadic.KernelTrit → GluingDynamics
gluingDynamics Triadic.negativeTrit = antiCommutingGluing
gluingDynamics Triadic.zeroTrit = gluingIdentity
gluingDynamics Triadic.positiveTrit = commutingGluing

-- Signed FRACTRAN multiplicity already projects to the same balanced trit.
seamDynamicsOfMultiplicity : SSP.SignedMultiplicity → SeamDynamics
seamDynamicsOfMultiplicity m = seamDynamics (SSP.coarseMultiplicity m)

gluingDynamicsOfMultiplicity : SSP.SignedMultiplicity → GluingDynamics
gluingDynamicsOfMultiplicity m = gluingDynamics (SSP.coarseMultiplicity m)

negativeMultiplicityMeansConverging :
  (n : Nat) →
  seamDynamicsOfMultiplicity (SSP.negativeMultiplicity n) ≡ convergingSeam
negativeMultiplicityMeansConverging n = refl

zeroMultiplicityMeansFibreIdentity :
  seamDynamicsOfMultiplicity SSP.zeroMultiplicity ≡ seamIdentity
zeroMultiplicityMeansFibreIdentity = refl

positiveMultiplicityMeansDiverging :
  (n : Nat) →
  seamDynamicsOfMultiplicity (SSP.positiveMultiplicity n) ≡ divergingSeam
positiveMultiplicityMeansDiverging n = refl

negativeMultiplicityMeansAntiCommutingObserver :
  (n : Nat) →
  gluingDynamicsOfMultiplicity (SSP.negativeMultiplicity n) ≡ antiCommutingGluing
negativeMultiplicityMeansAntiCommutingObserver n = refl

zeroMultiplicityMeansGluingIdentity :
  gluingDynamicsOfMultiplicity SSP.zeroMultiplicity ≡ gluingIdentity
zeroMultiplicityMeansGluingIdentity = refl

positiveMultiplicityMeansCommutingObserver :
  (n : Nat) →
  gluingDynamicsOfMultiplicity (SSP.positiveMultiplicity n) ≡ commutingGluing
positiveMultiplicityMeansCommutingObserver n = refl

------------------------------------------------------------------------
-- 2. Exact symbolic Q(sqrt(3)) coordinates of one order-three orbit family.
------------------------------------------------------------------------

orbitNorm : Nat → Nat
orbitNorm k = k * k + k + 1

orbitXNumerator : Nat → Nat
orbitXNumerator k = 2 * k + 1

orbitCommonDenominator : Nat → Nat
orbitCommonDenominator k = 2 * orbitNorm k

record RhoOrbitCoordinate : Set where
  constructor rho-orbit-coordinate
  field
    index : Nat
    realNumerator : Nat
    commonDenominator : Nat
    imaginarySqrtThreeNumerator : Nat

open RhoOrbitCoordinate public

rhoOrbitCoordinate : Nat → RhoOrbitCoordinate
rhoOrbitCoordinate k =
  rho-orbit-coordinate
    k
    (orbitXNumerator k)
    (orbitCommonDenominator k)
    1

k0Coordinate : rhoOrbitCoordinate 0 ≡ rho-orbit-coordinate 0 1 2 1
k0Coordinate = refl

k1Coordinate : rhoOrbitCoordinate 1 ≡ rho-orbit-coordinate 1 3 6 1
k1Coordinate = refl

k2Coordinate : rhoOrbitCoordinate 2 ≡ rho-orbit-coordinate 2 5 14 1
k2Coordinate = refl

k3Coordinate : rhoOrbitCoordinate 3 ≡ rho-orbit-coordinate 3 7 26 1
k3Coordinate = refl

k4Coordinate : rhoOrbitCoordinate 4 ≡ rho-orbit-coordinate 4 9 42 1
k4Coordinate = refl

k5Coordinate : rhoOrbitCoordinate 5 ≡ rho-orbit-coordinate 5 11 62 1
k5Coordinate = refl

k6Coordinate : rhoOrbitCoordinate 6 ≡ rho-orbit-coordinate 6 13 86 1
k6Coordinate = refl

k7Coordinate : rhoOrbitCoordinate 7 ≡ rho-orbit-coordinate 7 15 114 1
k7Coordinate = refl

------------------------------------------------------------------------
-- 3. Exact 0.15 = 3/20 threshold arithmetic.
--
-- x_k >= 3/20 is tested without division by cross-multiplication:
--   20 * numerator >= 3 * denominator.
-- The positive gaps below are literal Nat witnesses.
------------------------------------------------------------------------

data OuterSevenIndex : Set where
  outer0 outer1 outer2 outer3 outer4 outer5 outer6 : OuterSevenIndex

outerIndex : OuterSevenIndex → Nat
outerIndex outer0 = 0
outerIndex outer1 = 1
outerIndex outer2 = 2
outerIndex outer3 = 3
outerIndex outer4 = 4
outerIndex outer5 = 5
outerIndex outer6 = 6

outerThresholdGap : OuterSevenIndex → Nat
outerThresholdGap outer0 = 14
outerThresholdGap outer1 = 42
outerThresholdGap outer2 = 58
outerThresholdGap outer3 = 62
outerThresholdGap outer4 = 54
outerThresholdGap outer5 = 34
outerThresholdGap outer6 = 2

outerSevenAtOrBeyondThreeTwentieths :
  (i : OuterSevenIndex) →
  3 * orbitCommonDenominator (outerIndex i)
    + outerThresholdGap i
  ≡
  20 * orbitXNumerator (outerIndex i)
outerSevenAtOrBeyondThreeTwentieths outer0 = refl
outerSevenAtOrBeyondThreeTwentieths outer1 = refl
outerSevenAtOrBeyondThreeTwentieths outer2 = refl
outerSevenAtOrBeyondThreeTwentieths outer3 = refl
outerSevenAtOrBeyondThreeTwentieths outer4 = refl
outerSevenAtOrBeyondThreeTwentieths outer5 = refl
outerSevenAtOrBeyondThreeTwentieths outer6 = refl

-- The next family member is already strictly inside |x| = 3/20.
k7FallsInsideThreeTwentiethsByFortyTwo :
  20 * orbitXNumerator 7 + 42
  ≡
  3 * orbitCommonDenominator 7
k7FallsInsideThreeTwentiethsByFortyTwo = refl

-- The two outermost family members share x=1/2 but have different heights.
-- A horizontal-only observer therefore identifies two distinct orbit fibres.
k0AndK1ShareHorizontalCoordinate :
  1 * orbitCommonDenominator 1
  ≡
  3 * orbitCommonDenominator 0
k0AndK1ShareHorizontalCoordinate = refl

k0AndK1HaveDifferentScaleDenominators :
  orbitCommonDenominator 0 ≡ 2
  × orbitCommonDenominator 1 ≡ 6
k0AndK1HaveDifferentScaleDenominators = refl , refl

------------------------------------------------------------------------
-- 4. Modular-zero compiler.
--
-- This is the BIDI consumer theorem.  If the analytic carrier supplies the
-- source theorem j(rho)=0 and modular invariance for this gamma family, every
-- member is automatically an order-three zero on that same j carrier.
------------------------------------------------------------------------

record ModularOrderThreeZeroCarrier : Set₁ where
  field
    Point : Set
    Value : Set
    rho : Point
    gamma : Nat → Point → Point
    j : Point → Value
    zeroValue : Value
    jAtRhoIsZero : j rho ≡ zeroValue
    jInvariantAlongGamma : (k : Nat) → j (gamma k rho) ≡ j rho

open ModularOrderThreeZeroCarrier public

orbitMemberIsJZero :
  (C : ModularOrderThreeZeroCarrier) →
  (k : Nat) →
  j C (gamma C k (rho C)) ≡ zeroValue C
orbitMemberIsJZero C k =
  trans (jInvariantAlongGamma C k) (jAtRhoIsZero C)

------------------------------------------------------------------------
-- 5. Source alignment and introspective frontier.
------------------------------------------------------------------------

sourceKnowsModularInvariantAndRhoZero :
  Sources.inspectedForExactClaim Sources.jDefinitionClaim ≡ true
sourceKnowsModularInvariantAndRhoZero = refl

data OrbitBidiResidual : Set where
  missingAnalyticMobiusCoordinateDerivation : OrbitBidiResidual
  missingRenderedBeamSameObjectIdentification : OrbitBidiResidual
  missingScaleCompatibleSignedFibreTransport : OrbitBidiResidual
  missingActualGluingSquareClassification : OrbitBidiResidual

firstOrbitBidiResidual : OrbitBidiResidual
firstOrbitBidiResidual = missingAnalyticMobiusCoordinateDerivation

record OrbitBidiFrontier : Set where
  constructor orbit-bidi-frontier
  field
    modularZeroSourceCoordinateAvailable : Bool
    symbolicOrderThreeFamilyConstructed : Bool
    sevenMemberThresholdWitnessConstructed : Bool
    nextMemberFallsInsideThreshold : Bool
    balancedTernarySeamObserverConstructed : Bool
    balancedTernaryGluingObserverConstructed : Bool
    renderedBeamProvedSameObject : Bool
    firstResidual : OrbitBidiResidual

canonicalOrbitBidiFrontier : OrbitBidiFrontier
canonicalOrbitBidiFrontier =
  orbit-bidi-frontier
    true true true true true true false
    firstOrbitBidiResidual

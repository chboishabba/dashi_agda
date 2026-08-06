module DASHI.Biology.TernaryCantorWheelDiffusionExact where

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hyper

------------------------------------------------------------------------
-- Finite balanced-ternary address and the polar Cantor restriction.

TernaryAddress : Nat → Set
TernaryAddress d = Vec Triadic.KernelTrit d

data PolarTrit : Set where
  polarNegative : PolarTrit
  polarPositive : PolarTrit

polarToTrit : PolarTrit → Triadic.KernelTrit
polarToTrit polarNegative = Triadic.negativeTrit
polarToTrit polarPositive = Triadic.positiveTrit

PolarAddress : Nat → Set
PolarAddress d = Vec PolarTrit d

embedPolarAddress : ∀ {d : Nat} → PolarAddress d → TernaryAddress d
embedPolarAddress vnil = vnil
embedPolarAddress (x vcons xs) =
  polarToTrit x vcons embedPolarAddress xs

ternaryAddressCount : Nat → Nat
ternaryAddressCount d = Hyper.powNat 3 d

polarAddressCount : Nat → Nat
polarAddressCount d = Hyper.powNat 2 d

ternaryDepthThreeCount : ternaryAddressCount 3 ≡ 27
ternaryDepthThreeCount = refl

polarDepthThreeCount : polarAddressCount 3 ≡ 8
polarDepthThreeCount = refl

canonicalPolarAddress : PolarAddress 3
canonicalPolarAddress =
  polarNegative vcons polarPositive vcons polarNegative vcons vnil

canonicalEmbeddedPolarAddress : TernaryAddress 3
canonicalEmbeddedPolarAddress =
  Triadic.negativeTrit vcons
  Triadic.positiveTrit vcons
  Triadic.negativeTrit vcons
  vnil

polarEmbeddingIsExact :
  embedPolarAddress canonicalPolarAddress ≡ canonicalEmbeddedPolarAddress
polarEmbeddingIsExact = refl

------------------------------------------------------------------------
-- Wheel phase.  This cyclic observation is intentionally distinct from the
-- ordered mediated path negative <-> zero <-> positive.

nextWheelPhase : Triadic.KernelTrit → Triadic.KernelTrit
nextWheelPhase Triadic.negativeTrit = Triadic.zeroTrit
nextWheelPhase Triadic.zeroTrit = Triadic.positiveTrit
nextWheelPhase Triadic.positiveTrit = Triadic.negativeTrit

nextWheelPhaseThree :
  (x : Triadic.KernelTrit) →
  nextWheelPhase (nextWheelPhase (nextWheelPhase x)) ≡ x
nextWheelPhaseThree Triadic.negativeTrit = refl
nextWheelPhaseThree Triadic.zeroTrit = refl
nextWheelPhaseThree Triadic.positiveTrit = refl

rotateWheelAddress :
  ∀ {d : Nat} → TernaryAddress d → TernaryAddress d
rotateWheelAddress vnil = vnil
rotateWheelAddress (x vcons xs) =
  nextWheelPhase x vcons rotateWheelAddress xs

rotateWheelAddressThree :
  ∀ {d : Nat} (xs : TernaryAddress d) →
  rotateWheelAddress
    (rotateWheelAddress
      (rotateWheelAddress xs))
  ≡ xs
rotateWheelAddressThree vnil = refl
rotateWheelAddressThree (x vcons xs)
  with nextWheelPhaseThree x | rotateWheelAddressThree xs
... | refl | refl = refl

------------------------------------------------------------------------
-- Finite diffusion on a three-sector wheel.

record WheelMass : Set where
  constructor wheelMass
  field
    negativeSectorMass : Nat
    zeroSectorMass : Nat
    positiveSectorMass : Nat

open WheelMass public

rotateMassClockwise : WheelMass → WheelMass
rotateMassClockwise (wheelMass negativeMass zeroMass positiveMass) =
  wheelMass positiveMass negativeMass zeroMass

rotateMassClockwiseThree :
  (mass : WheelMass) →
  rotateMassClockwise
    (rotateMassClockwise
      (rotateMassClockwise mass))
  ≡ mass
rotateMassClockwiseThree (wheelMass negativeMass zeroMass positiveMass) = refl

moveOneNegativeToZero : WheelMass → WheelMass
moveOneNegativeToZero (wheelMass zero zeroMass positiveMass) =
  wheelMass zero zeroMass positiveMass
moveOneNegativeToZero (wheelMass (suc negativeMass) zeroMass positiveMass) =
  wheelMass negativeMass (suc zeroMass) positiveMass

canonicalWheelGradient : WheelMass
canonicalWheelGradient = wheelMass 3 0 0

canonicalWheelDiffusionStep :
  moveOneNegativeToZero canonicalWheelGradient ≡ wheelMass 2 1 0
canonicalWheelDiffusionStep = refl

------------------------------------------------------------------------
-- Finite self-similar refinement carrier.

record CantorRefinement : Set where
  constructor cantorRefinement
  field
    parentDepth : Nat
    childDepth : Nat
    parentStateCount : Nat
    childStateCount : Nat
    zeroBranchRetained : Bool

open CantorRefinement public

canonicalPolarRefinement : CantorRefinement
canonicalPolarRefinement =
  cantorRefinement 2 3 4 8 false

canonicalTernaryRefinement : CantorRefinement
canonicalTernaryRefinement =
  cantorRefinement 2 3 9 27 true

record CantorWheelBoundary : Set where
  constructor cantorWheelBoundary
  field
    polarCantorRestrictionEqualsFullTernaryCarrier : Bool
    polarCantorRestrictionEqualsFullTernaryCarrierIsFalse :
      polarCantorRestrictionEqualsFullTernaryCarrier ≡ false

    cyclicWheelEqualsOrderedDialecticalAdjacency : Bool
    cyclicWheelEqualsOrderedDialecticalAdjacencyIsFalse :
      cyclicWheelEqualsOrderedDialecticalAdjacency ≡ false

    finiteWheelIsCanonicalObjectNamedCantorWheel : Bool
    finiteWheelIsCanonicalObjectNamedCantorWheelIsFalse :
      finiteWheelIsCanonicalObjectNamedCantorWheel ≡ false

    diffusionImpliesBiologicalIntent : Bool
    diffusionImpliesBiologicalIntentIsFalse :
      diffusionImpliesBiologicalIntent ≡ false

open CantorWheelBoundary public

canonicalCantorWheelBoundary : CantorWheelBoundary
canonicalCantorWheelBoundary =
  cantorWheelBoundary false refl false refl false refl false refl

module DASHI.Biology.DialecticalSheetSpiralExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic

------------------------------------------------------------------------
-- Literal 3 x 3 ternary sheet and its square symmetries.

record Sheet3 : Set where
  constructor sheet3
  field
    northWest : Triadic.KernelTrit
    north : Triadic.KernelTrit
    northEast : Triadic.KernelTrit
    west : Triadic.KernelTrit
    centre : Triadic.KernelTrit
    east : Triadic.KernelTrit
    southWest : Triadic.KernelTrit
    south : Triadic.KernelTrit
    southEast : Triadic.KernelTrit

open Sheet3 public

rotateQuarter : Sheet3 → Sheet3
rotateQuarter (sheet3 a b c d e f g h i) =
  sheet3 g d a h e b i f c

reflectVertical : Sheet3 → Sheet3
reflectVertical (sheet3 a b c d e f g h i) =
  sheet3 c b a f e d i h g

negateSheet : Sheet3 → Sheet3
negateSheet (sheet3 a b c d e f g h i) =
  sheet3
    (Triadic.negateTrit a)
    (Triadic.negateTrit b)
    (Triadic.negateTrit c)
    (Triadic.negateTrit d)
    (Triadic.negateTrit e)
    (Triadic.negateTrit f)
    (Triadic.negateTrit g)
    (Triadic.negateTrit h)
    (Triadic.negateTrit i)

rotateFour : Sheet3 → Sheet3
rotateFour x =
  rotateQuarter (rotateQuarter (rotateQuarter (rotateQuarter x)))

rotateFourReturnsSheet : (x : Sheet3) → rotateFour x ≡ x
rotateFourReturnsSheet (sheet3 a b c d e f g h i) = refl

reflectionIsInvolutive :
  (x : Sheet3) → reflectVertical (reflectVertical x) ≡ x
reflectionIsInvolutive (sheet3 a b c d e f g h i) = refl

negationIsInvolutive :
  (x : Sheet3) → negateSheet (negateSheet x) ≡ x
negationIsInvolutive (sheet3 a b c d e f g h i)
  with Triadic.negateTritInvolutive a
     | Triadic.negateTritInvolutive b
     | Triadic.negateTritInvolutive c
     | Triadic.negateTritInvolutive d
     | Triadic.negateTritInvolutive e
     | Triadic.negateTritInvolutive f
     | Triadic.negateTritInvolutive g
     | Triadic.negateTritInvolutive h
     | Triadic.negateTritInvolutive i
... | refl | refl | refl | refl | refl | refl | refl | refl | refl = refl

------------------------------------------------------------------------
-- Dialectical spiral lift.  Projection to the sheet can return after four
-- quarter rotations while historical/developmental height strictly advances.

data SpiralSense : Set where
  positiveSpiral : SpiralSense
  negativeSpiral : SpiralSense

flipSense : SpiralSense → SpiralSense
flipSense positiveSpiral = negativeSpiral
flipSense negativeSpiral = positiveSpiral

record SpiralState : Set where
  constructor spiralState
  field
    projectedSheet : Sheet3
    historicalHeight : Nat
    spiralSense : SpiralSense

open SpiralState public

liftRotation : SpiralState → SpiralState
liftRotation (spiralState x h sense) =
  spiralState (rotateQuarter x) (suc h) sense

liftReflection : SpiralState → SpiralState
liftReflection (spiralState x h sense) =
  spiralState (reflectVertical x) (suc h) (flipSense sense)

fourLiftRotations : SpiralState → SpiralState
fourLiftRotations state =
  liftRotation (liftRotation (liftRotation (liftRotation state)))

projectedReturnAfterFour :
  (state : SpiralState) →
  projectedSheet (fourLiftRotations state) ≡ projectedSheet state
projectedReturnAfterFour (spiralState (sheet3 a b c d e f g h i) _ sense) = refl

historicalLiftAfterFour :
  (state : SpiralState) →
  historicalHeight (fourLiftRotations state)
  ≡ suc (suc (suc (suc (historicalHeight state))))
historicalLiftAfterFour (spiralState x h sense) = refl

reflectionFlipsSpiralSense :
  (state : SpiralState) →
  spiralSense (liftReflection state) ≡ flipSense (spiralSense state)
reflectionFlipsSpiralSense (spiralState x h sense) = refl

------------------------------------------------------------------------
-- Boundary: recurrence in projection is not recurrence of the lifted state.

record DialecticalSpiralBoundary : Set where
  constructor dialecticalSpiralBoundary
  field
    projectedCycleErasesHistory : Bool
    projectedCycleErasesHistoryIsFalse :
      projectedCycleErasesHistory ≡ false

    reflectionAndRotationAreMereDecorations : Bool
    reflectionAndRotationAreMereDecorationsIsFalse :
      reflectionAndRotationAreMereDecorations ≡ false

    spiralLiftAloneProvesNavierStokesRegularity : Bool
    spiralLiftAloneProvesNavierStokesRegularityIsFalse :
      spiralLiftAloneProvesNavierStokesRegularity ≡ false

open DialecticalSpiralBoundary public

canonicalDialecticalSpiralBoundary : DialecticalSpiralBoundary
canonicalDialecticalSpiralBoundary =
  dialecticalSpiralBoundary false refl false refl false refl

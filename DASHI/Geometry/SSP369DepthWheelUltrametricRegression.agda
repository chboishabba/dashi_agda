module DASHI.Geometry.SSP369DepthWheelUltrametricRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.SSPPrimeLane369Refinement as Ref
import DASHI.Geometry.SSP369DepthWheelUltrametric as Metric
import DASHI.Physics.Closure.SSPPrimeLane369DepthAddressWheel as Wheel

allThreeAddress : Ref.Lane369Address 3
allThreeAddress =
  Ref.extend
    (Ref.extend
      (Ref.extend Ref.root Ref.digit-3)
      Ref.digit-3)
    Ref.digit-3

canonicalDistanceToAllThreeIsTwo :
  Metric.refinementAddressDistance
    Ref.canonicalThreeSixNineAddress
    allThreeAddress
  ≡ 2
canonicalDistanceToAllThreeIsTwo = refl

rotatedDistanceStillTwo :
  Metric.refinementAddressDistance
    (Wheel.p7AddressWheel Ref.canonicalThreeSixNineAddress)
    (Wheel.p7AddressWheel allThreeAddress)
  ≡ 2
rotatedDistanceStillTwo = refl

canonicalPairIsometry :
  Metric.refinementAddressDistance
    (Wheel.p7AddressWheel Ref.canonicalThreeSixNineAddress)
    (Wheel.p7AddressWheel allThreeAddress)
  ≡ Metric.refinementAddressDistance
      Ref.canonicalThreeSixNineAddress
      allThreeAddress
canonicalPairIsometry =
  Metric.p7RefinementAddressWheelIsometry
    Ref.canonicalThreeSixNineAddress
    allThreeAddress

threeAddressRotationsReturnCanonical :
  Wheel.p7AddressWheel
    (Wheel.p7AddressWheel
      (Wheel.p7AddressWheel Ref.canonicalThreeSixNineAddress))
  ≡ Ref.canonicalThreeSixNineAddress
threeAddressRotationsReturnCanonical =
  Wheel.p7AddressWheelThree Ref.canonicalThreeSixNineAddress

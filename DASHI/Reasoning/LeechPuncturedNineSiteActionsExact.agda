module DASHI.Reasoning.LeechPuncturedNineSiteActionsExact where

-- Finite centre-preserving punctured-nine geometric action.
-- Source point owner: OggSSPP2BalancedTernaryPuncturedPlaneExact.
-- S3 generators are an explicit order-three F3^2 linear matrix
--   R(x,y)=(-y,x-y)
-- and an order-two coordinate transpose
--   S(x,y)=(y,x).
-- They obey R^3=1, S^2=1 and SRS=R^-1. Point inversion (-x,-y)
-- commutes with both. All eight cases are computational reductions.
--
-- These are site-index permutations, not continuous Fourier rotations,
-- independently authenticated remote operations, semantic objections,
-- or proven automorphisms of the Leech lattice.
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.OggSSPP2BalancedTernaryPuncturedPlaneExact as Plane
import DASHI.Reasoning.LeechPuncturedNineLearningBridgeExact as Puncture

Point : Set
Point = Plane.PuncturedNineSheet

rotate3 : Point → Point
rotate3 Plane.negativeFirstAxis = Plane.negativeSecondAxis
rotate3 Plane.positiveFirstAxis = Plane.positiveSecondAxis
rotate3 Plane.negativeSecondAxis = Plane.positiveEqualDiagonal
rotate3 Plane.positiveSecondAxis = Plane.negativeEqualDiagonal
rotate3 Plane.negativeEqualDiagonal = Plane.positiveFirstAxis
rotate3 Plane.positiveEqualDiagonal = Plane.negativeFirstAxis
rotate3 Plane.negativeOppositeDiagonal = Plane.negativeOppositeDiagonal
rotate3 Plane.positiveOppositeDiagonal = Plane.positiveOppositeDiagonal

swapAxes : Point → Point
swapAxes Plane.negativeFirstAxis = Plane.negativeSecondAxis
swapAxes Plane.positiveFirstAxis = Plane.positiveSecondAxis
swapAxes Plane.negativeSecondAxis = Plane.negativeFirstAxis
swapAxes Plane.positiveSecondAxis = Plane.positiveFirstAxis
swapAxes Plane.negativeEqualDiagonal = Plane.negativeEqualDiagonal
swapAxes Plane.positiveEqualDiagonal = Plane.positiveEqualDiagonal
swapAxes Plane.negativeOppositeDiagonal = Plane.positiveOppositeDiagonal
swapAxes Plane.positiveOppositeDiagonal = Plane.negativeOppositeDiagonal

rotateCubed : (p : Point) → rotate3 (rotate3 (rotate3 p)) ≡ p
rotateCubed Plane.negativeFirstAxis = refl
rotateCubed Plane.positiveFirstAxis = refl
rotateCubed Plane.negativeSecondAxis = refl
rotateCubed Plane.positiveSecondAxis = refl
rotateCubed Plane.negativeEqualDiagonal = refl
rotateCubed Plane.positiveEqualDiagonal = refl
rotateCubed Plane.negativeOppositeDiagonal = refl
rotateCubed Plane.positiveOppositeDiagonal = refl

swapTwice : (p : Point) → swapAxes (swapAxes p) ≡ p
swapTwice Plane.negativeFirstAxis = refl
swapTwice Plane.positiveFirstAxis = refl
swapTwice Plane.negativeSecondAxis = refl
swapTwice Plane.positiveSecondAxis = refl
swapTwice Plane.negativeEqualDiagonal = refl
swapTwice Plane.positiveEqualDiagonal = refl
swapTwice Plane.negativeOppositeDiagonal = refl
swapTwice Plane.positiveOppositeDiagonal = refl

s3Conjugation :
  (p : Point) →
  swapAxes (rotate3 (swapAxes p)) ≡ rotate3 (rotate3 p)
s3Conjugation Plane.negativeFirstAxis = refl
s3Conjugation Plane.positiveFirstAxis = refl
s3Conjugation Plane.negativeSecondAxis = refl
s3Conjugation Plane.positiveSecondAxis = refl
s3Conjugation Plane.negativeEqualDiagonal = refl
s3Conjugation Plane.positiveEqualDiagonal = refl
s3Conjugation Plane.negativeOppositeDiagonal = refl
s3Conjugation Plane.positiveOppositeDiagonal = refl

pointSignCommutesWithRotation :
  (p : Point) →
  Puncture.oppositePoint (rotate3 p)
    ≡ rotate3 (Puncture.oppositePoint p)
pointSignCommutesWithRotation Plane.negativeFirstAxis = refl
pointSignCommutesWithRotation Plane.positiveFirstAxis = refl
pointSignCommutesWithRotation Plane.negativeSecondAxis = refl
pointSignCommutesWithRotation Plane.positiveSecondAxis = refl
pointSignCommutesWithRotation Plane.negativeEqualDiagonal = refl
pointSignCommutesWithRotation Plane.positiveEqualDiagonal = refl
pointSignCommutesWithRotation Plane.negativeOppositeDiagonal = refl
pointSignCommutesWithRotation Plane.positiveOppositeDiagonal = refl

pointSignCommutesWithSwap :
  (p : Point) →
  Puncture.oppositePoint (swapAxes p)
    ≡ swapAxes (Puncture.oppositePoint p)
pointSignCommutesWithSwap Plane.negativeFirstAxis = refl
pointSignCommutesWithSwap Plane.positiveFirstAxis = refl
pointSignCommutesWithSwap Plane.negativeSecondAxis = refl
pointSignCommutesWithSwap Plane.positiveSecondAxis = refl
pointSignCommutesWithSwap Plane.negativeEqualDiagonal = refl
pointSignCommutesWithSwap Plane.positiveEqualDiagonal = refl
pointSignCommutesWithSwap Plane.negativeOppositeDiagonal = refl
pointSignCommutesWithSwap Plane.positiveOppositeDiagonal = refl

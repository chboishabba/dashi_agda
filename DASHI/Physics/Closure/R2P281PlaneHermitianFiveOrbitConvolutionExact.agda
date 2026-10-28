module DASHI.Physics.Closure.R2P281PlaneHermitianFiveOrbitConvolutionExact where

------------------------------------------------------------------------
-- EXACT NINE-PLANE FOURIER BILINEAR CONVOLUTION FROM FIVE ORBIT CLASSES
--
-- Reuse: Original BalancedTernaryAntipodalOrbitExact (5 in 9),
--         R2P227729HermitianThirteenPairFourierCodecExact (1+4 compact)
--         R2P227729FourierObserverIncidenceExact (all signed modes)
--         Biology.Physical.C3CubeCyclotomicFourierExact (Q(omega)).
--
-- Two arbitrary admissible Hermitian plane signals, their actual NINE
-- signed modes, ALL 9*9=81 ordered interaction pairs, and ALL 5*5=25
-- integer-frequency output labels. Exact transport is a consumer
-- invariance proof, NOT an FFT, D4 irreducible decomposition, NS Clay,
-- Monster action or a faster numerical implementation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.Closure.R2P2ThreeModeBinaryTernaryNSAliasingCutExact as M
import DASHI.Physics.Closure.R2P227729FourierObserverIncidenceExact as I
import DASHI.Physics.Closure.R2P227729AntipodalThirteenFiveOrbitFourierCutExact as Ant
import DASHI.Physics.Closure.R2P227729HermitianThirteenPairFourierCodecExact as Hermitian
import DASHI.Physics.Closure.R2P227729FiniteQuadraticConvolutionExact as Full
import DASHI.Biology.Physical.C3CubeCyclotomicFourierExact as C3

PlanePair81 : Set
PlanePair81 = Ant.Plane9 × Ant.Plane9

plane9 : List Ant.Plane9
plane9 =
  I.concatMapL (λ a → I.mapL (λ b → a , b) I.allMode3) I.allMode3

planePairs81 : List PlanePair81
planePairs81 =
  I.concatMapL (λ p → I.mapL (λ q → p , q) plane9) plane9

planeCountNine : I.lengthL plane9 ≡ 9
planeCountNine = refl

planePairCountEightyOne : I.lengthL planePairs81 ≡ 81
planePairCountEightyOne = refl

WidePlane25 : Set
WidePlane25 = M.FiveMode × M.FiveMode

planeTruePairSum : PlanePair81 → WidePlane25
planeTruePairSum ((a , b) , (c , d)) =
  M.exactQuadraticModeSum a c , M.exactQuadraticModeSum b d

planeOutputEqual : WidePlane25 → WidePlane25 → Bool
planeOutputEqual (a , b) (c , d) =
  Full._&&B_ (Full.eqWideMode a c) (Full.eqWideMode b d)

choosePlaneCoeff :
  Bool → C3.Cyclotomic3 → C3.Cyclotomic3
choosePlaneCoeff true val = val
choosePlaneCoeff false val = C3.zeroC

sumPlane :
  (List PlanePair81) →
  (PlanePair81 → C3.Cyclotomic3) →
  C3.Cyclotomic3
sumPlane [] weight = C3.zeroC
sumPlane (pair ∷ pairs) weight =
  C3._+C_ (weight pair) (sumPlane pairs weight)

sumPlaneCong :
  (pairs : List PlanePair81) (f g : PlanePair81 → C3.Cyclotomic3) →
  ((pair : PlanePair81) → f pair ≡ g pair) →
  sumPlane pairs f ≡ sumPlane pairs g
sumPlaneCong [] f g pointwise = refl
sumPlaneCong (pair ∷ pairs) f g pointwise
  rewrite pointwise pair
        | sumPlaneCong pairs f g pointwise = refl

planePairContribution :
  (left right : Ant.Plane9 → C3.Cyclotomic3) →
  (target : WidePlane25) →
  PlanePair81 → C3.Cyclotomic3
planePairContribution left right target (p , q) =
  choosePlaneCoeff
    (planeOutputEqual (planeTruePairSum (p , q)) target)
    (C3._*C_ (left p) (right q))

truePlaneBilinearAt :
  (left right : Ant.Plane9 → C3.Cyclotomic3) →
  WidePlane25 → C3.Cyclotomic3
truePlaneBilinearAt left right target =
  sumPlane planePairs81 (planePairContribution left right target)

packedFivePlaneBilinearAt :
  Hermitian.PackedHermitian9 →
  Hermitian.PackedHermitian9 →
  WidePlane25 → C3.Cyclotomic3
packedFivePlaneBilinearAt left right =
  truePlaneBilinearAt (Hermitian.packedPlane9 left)
                      (Hermitian.packedPlane9 right)

packedPlanePairTermMatchesSource :
  (left right : Hermitian.Hermitian9)
  (target : WidePlane25)
  (pair : PlanePair81) →
  planePairContribution
    (Hermitian.packedPlane9 (Hermitian.packHermitian9 left))
    (Hermitian.packedPlane9 (Hermitian.packHermitian9 right))
    target pair
  ≡ planePairContribution
      (Hermitian.coefficient9 left) (Hermitian.coefficient9 right)
      target pair
packedPlanePairTermMatchesSource left right target (p , q)
  rewrite Hermitian.decodeAfterEncodeHermitian9 left p
        | Hermitian.decodeAfterEncodeHermitian9 right q = refl

fiveOrbitPlaneCodecPreservesAll25QuadraticOutputs :
  (left right : Hermitian.Hermitian9) (target : WidePlane25) →
  packedFivePlaneBilinearAt
    (Hermitian.packHermitian9 left)
    (Hermitian.packHermitian9 right) target
  ≡ truePlaneBilinearAt
      (Hermitian.coefficient9 left) (Hermitian.coefficient9 right) target
fiveOrbitPlaneCodecPreservesAll25QuadraticOutputs left right target =
  sumPlaneCong planePairs81
    (planePairContribution
      (Hermitian.packedPlane9 (Hermitian.packHermitian9 left))
      (Hermitian.packedPlane9 (Hermitian.packHermitian9 right)) target)
    (planePairContribution
      (Hermitian.coefficient9 left)
      (Hermitian.coefficient9 right) target)
    (packedPlanePairTermMatchesSource left right target)

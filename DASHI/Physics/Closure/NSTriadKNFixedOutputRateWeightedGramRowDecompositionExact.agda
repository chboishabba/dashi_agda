module DASHI.Physics.Closure.NSTriadKNFixedOutputRateWeightedGramRowDecompositionExact where

------------------------------------------------------------------------
-- RATE-WEIGHTED COHERENT ROW = DIAGONAL + PAIR-RATE OFF-DIAGONAL GRAM
--
-- For a finite family A_i with scalar rates lambda_i, define
--
--   M = sum_i A_i,
--   L = sum_i lambda_i A_i,
--   W(X,Y) = 2 Re <X,Y>.
--
-- Exact Hermitian bilinearity and symmetry give
--
--   W(M,L)
--     = sum_i lambda_i W(A_i,A_i)
--       + sum_{i<j} (lambda_i+lambda_j) W(A_i,A_j).
--
-- This is the finite algebraic hinge between:
--
--   * the fixed-output variable-rate coherent damping used by d1/R414; and
--   * the self-pair plus off-diagonal pair-rate Gram carrier used by R290.
--
-- No positivity, resolvent, inequality, absolute value, cardinality estimate,
-- time integration, or Navier--Stokes-specific analytic assumption is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredMultiplierVectorCovarianceExact as Vector
import DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicityGramRound287Exact as R287

F : C3.RealField _
F = Rational.rationalRealField

pairRateGramAgainstHead :
  (rate : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence →
  ℚ
pairRateGramAgainstHead rate value head [] = 0ℚ
pairRateGramAgainstHead rate value head (x ∷ xs) =
  (rate head + rate x) * Work.coherentWork (value head) (value x)
  + pairRateGramAgainstHead rate value head xs

pairRateOffDiagonalGram :
  (rate : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence →
  ℚ
pairRateOffDiagonalGram rate value [] = 0ℚ
pairRateOffDiagonalGram rate value (head ∷ rest) =
  pairRateGramAgainstHead rate value head rest
  + pairRateOffDiagonalGram rate value rest

rateDiagonalGram :
  (rate : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence →
  ℚ
rateDiagonalGram rate value [] = 0ℚ
rateDiagonalGram rate value (head ∷ rest) =
  rate head * Work.coherentWork (value head) (value head)
  + rateDiagonalGram rate value rest

workAddLeft :
  (leftA leftB right : C3.Complex3 F) →
  Work.coherentWork (C3.complex3Add leftA leftB) right
  ≡ Work.coherentWork leftA right + Work.coherentWork leftB right
workAddLeft leftA leftB right
  rewrite R287.realHermitianCrossSymmetric
    (C3.complex3Add leftA leftB) right
        | R287.realHermitianCrossSymmetric leftA right
        | R287.realHermitianCrossSymmetric leftB right =
  Work.workAddRight right leftA leftB

coherentWorkSymmetric :
  (left right : C3.Complex3 F) →
  Work.coherentWork left right ≡ Work.coherentWork right left
coherentWorkSymmetric left right =
  cong (Work.two *_) (R287.realHermitianCrossSymmetric left right)

weightedHeadAgainstRest :
  (rate : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (head : Physical.PhysicalTriadIncidence) →
  (rest : List Physical.PhysicalTriadIncidence) →
  let
    restSum = R224.foldVector value rest
    restWeighted = Vector.weightedVectorSum rate value rest
  in
  Work.coherentWork (value head) restWeighted
    + rate head * Work.coherentWork restSum (value head)
  ≡ pairRateGramAgainstHead rate value head rest
weightedHeadAgainstRest rate value head [] = solve []
weightedHeadAgainstRest rate value head (x ∷ xs) =
  let
    tailSum = R224.foldVector value xs
    tailWeighted = Vector.weightedVectorSum rate value xs

    first :
      Work.coherentWork (value head)
        (C3.complex3Add
          (R291.realScale (rate x) (value x))
          tailWeighted)
      ≡
      rate x * Work.coherentWork (value head) (value x)
      + Work.coherentWork (value head) tailWeighted
    first =
      trans
        (Work.workAddRight
          (value head)
          (R291.realScale (rate x) (value x))
          tailWeighted)
        (cong₂ _+_
          (Work.workScaleRight (rate x) (value head) (value x))
          refl)

    second :
      rate head
        * Work.coherentWork
            (C3.complex3Add (value x) tailSum)
            (value head)
      ≡
      rate head * Work.coherentWork (value x) (value head)
      + rate head * Work.coherentWork tailSum (value head)
    second =
      trans
        (cong (rate head *_)
          (workAddLeft (value x) tailSum (value head)))
        (solve
          ( rate head
          ∷ Work.coherentWork (value x) (value head)
          ∷ Work.coherentWork tailSum (value head)
          ∷ []))

    tail =
      weightedHeadAgainstRest rate value head xs

    symmetry :
      Work.coherentWork (value x) (value head)
      ≡ Work.coherentWork (value head) (value x)
    symmetry = coherentWorkSymmetric (value x) (value head)
  in
  trans
    (cong₂ _+_ first second)
    (trans
      (cong
        (λ y →
          rate x * Work.coherentWork (value head) (value x)
          + Work.coherentWork (value head) tailWeighted
          + (rate head * y
            + rate head * Work.coherentWork tailSum (value head)))
        symmetry)
      (trans
        (solve
          ( rate head ∷ rate x
          ∷ Work.coherentWork (value head) (value x)
          ∷ Work.coherentWork (value head) tailWeighted
          ∷ Work.coherentWork tailSum (value head)
          ∷ []))
        (cong
          ((rate head + rate x)
            * Work.coherentWork (value head) (value x) +_)
          tail)))

rateWeightedCoherentWorkDecomposition :
  (rate : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  let
    mixed = R224.foldVector value items
    weighted = Vector.weightedVectorSum rate value items
  in
  Work.coherentWork mixed weighted
  ≡ rateDiagonalGram rate value items
      + pairRateOffDiagonalGram rate value items
rateWeightedCoherentWorkDecomposition rate value [] = refl
rateWeightedCoherentWorkDecomposition rate value (head ∷ rest) =
  let
    restSum = R224.foldVector value rest
    restWeighted = Vector.weightedVectorSum rate value rest
    headValue = value head
    headWeighted = R291.realScale (rate head) headValue

    expandLeft :
      Work.coherentWork
        (C3.complex3Add headValue restSum)
        (C3.complex3Add headWeighted restWeighted)
      ≡
      Work.coherentWork headValue headWeighted
      + Work.coherentWork headValue restWeighted
      + (Work.coherentWork restSum headWeighted
        + Work.coherentWork restSum restWeighted)
    expandLeft =
      trans
        (workAddLeft
          headValue restSum
          (C3.complex3Add headWeighted restWeighted))
        (cong₂ _+_
          (Work.workAddRight headValue headWeighted restWeighted)
          (Work.workAddRight restSum headWeighted restWeighted))

    scaleHead :
      Work.coherentWork headValue headWeighted
      ≡ rate head * Work.coherentWork headValue headValue
    scaleHead =
      Work.workScaleRight (rate head) headValue headValue

    scaleRest :
      Work.coherentWork restSum headWeighted
      ≡ rate head * Work.coherentWork restSum headValue
    scaleRest =
      Work.workScaleRight (rate head) restSum headValue

    cross :
      Work.coherentWork headValue restWeighted
        + rate head * Work.coherentWork restSum headValue
      ≡ pairRateGramAgainstHead rate value head rest
    cross =
      weightedHeadAgainstRest rate value head rest

    tail :
      Work.coherentWork restSum restWeighted
      ≡ rateDiagonalGram rate value rest
        + pairRateOffDiagonalGram rate value rest
    tail =
      rateWeightedCoherentWorkDecomposition rate value rest
  in
  trans expandLeft
    (trans
      (cong
        (λ a →
          a
          + Work.coherentWork headValue restWeighted
          + (Work.coherentWork restSum headWeighted
            + Work.coherentWork restSum restWeighted))
        scaleHead)
      (trans
        (cong
          (λ b →
            rate head * Work.coherentWork headValue headValue
            + Work.coherentWork headValue restWeighted
            + (b + Work.coherentWork restSum restWeighted))
          scaleRest)
        (trans
          (solve
            ( rate head
            ∷ Work.coherentWork headValue headValue
            ∷ Work.coherentWork headValue restWeighted
            ∷ Work.coherentWork restSum headValue
            ∷ Work.coherentWork restSum restWeighted
            ∷ []))
          (trans
            (cong₂ _+_ cross tail)
            (solve
              ( rate head
              ∷ Work.coherentWork headValue headValue
              ∷ pairRateGramAgainstHead rate value head rest
              ∷ rateDiagonalGram rate value rest
              ∷ pairRateOffDiagonalGram rate value rest
              ∷ []))))))

rateWeightedGramRowDecompositionClosed : Bool
rateWeightedGramRowDecompositionClosed = true

rateWeightedGramRowUsesAbsoluteValue : Bool
rateWeightedGramRowUsesAbsoluteValue = false

rateWeightedGramRowUsesCardinalityBound : Bool
rateWeightedGramRowUsesCardinalityBound = false

rateWeightedGramRowIntroducesAnalyticEstimate : Bool
rateWeightedGramRowIntroducesAnalyticEstimate = false

clayPromotion : Bool
clayPromotion = false

rateWeightedGramRowDecompositionClosedIsTrue :
  rateWeightedGramRowDecompositionClosed ≡ true
rateWeightedGramRowDecompositionClosedIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl

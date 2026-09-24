module DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceVectorResidualWeldExact where

------------------------------------------------------------------------
-- S2b2d1b2 / COMPLETE-GRAPH VECTOR = EXISTING CENTERED RESIDUAL
--
-- The generic vector-centering owner constructs the literal complete-graph
-- vector
--
--   V = sum_{i<j} (c_i-c_j)(A_i-A_j)
--
-- and proves the closed form
--
--   V = n sum_i c_i A_i - (sum_i c_i)(sum_i A_i).
--
-- The older fixed-output covariance owner already defines exactly the
-- centered-multiplier residual by the right-hand side, but previously only
-- identified its Hermitian work with the SCALAR pair graph.
--
-- This owner welds the vector objects themselves:
--
--   pairVectorDifferenceSum = centeredMultiplierResidual.
--
-- Hence all later centered-frequency/input-Laplacian/cross-gradient identities
-- apply to the literal complete-graph vector, not just to an equal scalar
-- observation of some separately-defined residual.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; 0ℚ; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceVectorCenteringExact as New
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredMultiplierVectorCovarianceExact as Old

F : C3.RealField _
F = Rational.rationalRealField

weightedVectorSumSame :
  (multiplier : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  New.weightedVectorSum multiplier value items
  ≡ Old.weightedVectorSum multiplier value items
weightedVectorSumSame multiplier value [] = refl
weightedVectorSumSame multiplier value (tau ∷ rest) =
  cong
    (C3.complex3Add
      (R291.realScale (multiplier tau) (value tau)))
    (weightedVectorSumSame multiplier value rest)

vectorSumSame :
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  New.vectorSum value items ≡ R224.foldVector value items
vectorSumSame value [] = refl
vectorSumSame value (tau ∷ rest) =
  cong (C3.complex3Add (value tau)) (vectorSumSame value rest)

closedFormIsCenteredMultiplierResidual :
  (multiplier : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  New.closedFormVector multiplier value items
  ≡ Old.centeredMultiplierResidual multiplier value items
closedFormIsCenteredMultiplierResidual multiplier value items =
  let
    n = Pair.natAsRational (length items)
    total = Pair.rateSum multiplier items
    weightedNew = New.weightedVectorSum multiplier value items
    weightedOld = Old.weightedVectorSum multiplier value items
    sumNew = New.vectorSum value items
    sumOld = R224.foldVector value items

    weightedEq : weightedNew ≡ weightedOld
    weightedEq = weightedVectorSumSame multiplier value items

    sumEq : sumNew ≡ sumOld
    sumEq = vectorSumSame value items

    normalize :
      C3.complex3Subtract
        (R291.realScale n weightedOld)
        (R291.realScale total sumOld)
      ≡
      C3.complex3Add
        (R291.realScale n weightedOld)
        (R291.realScale (0ℚ - total) sumOld)
    normalize
      with weightedOld | sumOld
    ... | C3.complex3
          (C3.complex ax ai) (C3.complex ay ayi) (C3.complex az azi)
        | C3.complex3
          (C3.complex bx bi) (C3.complex by byi) (C3.complex bz bzi) =
      Algebra.complex3Ext
        (Algebra.complexExt
          (solve (n ∷ total ∷ ax ∷ ai ∷ bx ∷ bi ∷ []))
          (solve (n ∷ total ∷ ax ∷ ai ∷ bx ∷ bi ∷ [])))
        (Algebra.complexExt
          (solve (n ∷ total ∷ ay ∷ ayi ∷ by ∷ byi ∷ []))
          (solve (n ∷ total ∷ ay ∷ ayi ∷ by ∷ byi ∷ [])))
        (Algebra.complexExt
          (solve (n ∷ total ∷ az ∷ azi ∷ bz ∷ bzi ∷ []))
          (solve (n ∷ total ∷ az ∷ azi ∷ bz ∷ bzi ∷ [])))
  in
  trans
    (cong₂ C3.complex3Subtract
      (cong (R291.realScale n) weightedEq)
      (cong (R291.realScale total) sumEq))
    normalize

pairVectorDifferenceIsCenteredMultiplierResidual :
  (multiplier : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  New.pairVectorDifferenceSum multiplier value items
  ≡ Old.centeredMultiplierResidual multiplier value items
pairVectorDifferenceIsCenteredMultiplierResidual multiplier value items =
  trans
    (New.completeGraphVectorCovarianceIdentity multiplier value items)
    (closedFormIsCenteredMultiplierResidual multiplier value items)

completeGraphVectorSameObjectWeldClosed : Bool
completeGraphVectorSameObjectWeldClosed = true

centeredMultiplierResidualIsLiteralCompleteGraphVector : Bool
centeredMultiplierResidualIsLiteralCompleteGraphVector = true

scalarObservationNeededToIdentifyVectorObjects : Bool
scalarObservationNeededToIdentifyVectorObjects = false

clayPromotion : Bool
clayPromotion = false

completeGraphVectorSameObjectWeldClosedIsTrue :
  completeGraphVectorSameObjectWeldClosed ≡ true
completeGraphVectorSameObjectWeldClosedIsTrue = refl

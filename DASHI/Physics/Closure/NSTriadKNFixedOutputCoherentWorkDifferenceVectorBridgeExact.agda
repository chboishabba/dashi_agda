module DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentWorkDifferenceVectorBridgeExact where

------------------------------------------------------------------------
-- S2b2d1b2 / COHERENT WORK-DIFFERENCE -> LITERAL VECTOR DIFFERENCE
--
-- The coherent-covariance owner already rewrites the centered variable-rate
-- term as the signed scalar pair family
--
--   - sum_{alpha<beta} (r_alpha-r_beta) (w_alpha-w_beta).
--
-- The physical pair-difference programme, meanwhile, works with literal
-- Complex3 vector differences.  This module closes the purely algebraic bridge
-- between those two representations:
--
--   w_alpha - w_beta
--     = W(M , A_alpha - A_beta),
--
-- on the SAME fixed-output mixed-product family.
--
-- No absolute value, Cauchy estimate, positivity, lower separation,
-- radial/Pluecker input, cutoff summation, spacetime bound, or Clay promotion
-- is introduced.  The quantitative signed payment remains open.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair

F = Pair.F

coherentWorkSubtractRight :
  (left rightA rightB : C3.Complex3 F) →
  Work.coherentWork left (C3.complex3Subtract rightA rightB)
  ≡ Work.coherentWork left rightA - Work.coherentWork left rightB
coherentWorkSubtractRight
    (C3.complex3
      (C3.complex lr li) (C3.complex mr mi) (C3.complex nr ni))
    (C3.complex3
      (C3.complex ar ai) (C3.complex br bi) (C3.complex cr ci))
    (C3.complex3
      (C3.complex dr di) (C3.complex er ei) (C3.complex fr fi)) =
  solve
    ( lr ∷ li ∷ mr ∷ mi ∷ nr ∷ ni
    ∷ ar ∷ ai ∷ br ∷ bi ∷ cr ∷ ci
    ∷ dr ∷ di ∷ er ∷ ei ∷ fr ∷ fi ∷ [])

cellWorkDifferenceIsVectorDifferenceWork :
  (mixed : C3.Complex3 F) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Pair.cellWork mixed value alpha - Pair.cellWork mixed value beta
  ≡ Work.coherentWork mixed
      (C3.complex3Subtract (value alpha) (value beta))
cellWorkDifferenceIsVectorDifferenceWork mixed value alpha beta =
  sym (coherentWorkSubtractRight mixed (value alpha) (value beta))

fixedOutputPhysicalWorkDifferenceIsVectorDifferenceWork :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) (output : Z3.FourierMode) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  let
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value (Output.physicalOutputFiber cutoff output)
  in
  Pair.cellWork mixed value alpha - Pair.cellWork mixed value beta
  ≡ Work.coherentWork mixed
      (C3.complex3Subtract (value alpha) (value beta))
fixedOutputPhysicalWorkDifferenceIsVectorDifferenceWork
    S velocity cutoff output alpha beta =
  cellWorkDifferenceIsVectorDifferenceWork
    (R224.foldVector
      (D1a.mixedProductCell S velocity)
      (Output.physicalOutputFiber cutoff output))
    (D1a.mixedProductCell S velocity)
    alpha beta


------------------------------------------------------------------------
-- A1 / aggregate the SAME work-difference bridge through the exact pair sum.
------------------------------------------------------------------------

pairAgainstHeadVectorWork :
  (rate : Physical.PhysicalTriadIncidence → ℚ) →
  (mixed : C3.Complex3 F) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence → ℚ
pairAgainstHeadVectorWork rate mixed value head [] = 0
pairAgainstHeadVectorWork rate mixed value head (x ∷ xs) =
  (rate head - rate x)
    * Work.coherentWork mixed
        (C3.complex3Subtract (value head) (value x))
  + pairAgainstHeadVectorWork rate mixed value head xs

pairDifferenceVectorWorkSum :
  (rate : Physical.PhysicalTriadIncidence → ℚ) →
  (mixed : C3.Complex3 F) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence → ℚ
pairDifferenceVectorWorkSum rate mixed value [] = 0
pairDifferenceVectorWorkSum rate mixed value (x ∷ xs) =
  pairAgainstHeadVectorWork rate mixed value x xs
  + pairDifferenceVectorWorkSum rate mixed value xs

pairAgainstHeadWorkDifferenceIsVectorDifferenceWork :
  (rate : Physical.PhysicalTriadIncidence → ℚ) →
  (mixed : C3.Complex3 F) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (head : Physical.PhysicalTriadIncidence) →
  (xs : List Physical.PhysicalTriadIncidence) →
  Pair.pairAgainstHead rate (Pair.cellWork mixed value) head xs
  ≡ pairAgainstHeadVectorWork rate mixed value head xs
pairAgainstHeadWorkDifferenceIsVectorDifferenceWork rate mixed value head [] = refl
pairAgainstHeadWorkDifferenceIsVectorDifferenceWork rate mixed value head (x ∷ xs) =
  cong₂ _+_
    (cong ((rate head - rate x) *_)
      (cellWorkDifferenceIsVectorDifferenceWork mixed value head x))
    (pairAgainstHeadWorkDifferenceIsVectorDifferenceWork
      rate mixed value head xs)

pairDifferenceWorkSumIsVectorDifferenceWorkSum :
  (rate : Physical.PhysicalTriadIncidence → ℚ) →
  (mixed : C3.Complex3 F) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (xs : List Physical.PhysicalTriadIncidence) →
  Pair.pairDifferenceWorkSum rate (Pair.cellWork mixed value) xs
  ≡ pairDifferenceVectorWorkSum rate mixed value xs
pairDifferenceWorkSumIsVectorDifferenceWorkSum rate mixed value [] = refl
pairDifferenceWorkSumIsVectorDifferenceWorkSum rate mixed value (x ∷ xs) =
  cong₂ _+_
    (pairAgainstHeadWorkDifferenceIsVectorDifferenceWork
      rate mixed value x xs)
    (pairDifferenceWorkSumIsVectorDifferenceWorkSum rate mixed value xs)

fixedOutputPhysicalPairDifferenceIsVectorDifferenceWorkSum :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (rho : Z3.FourierMode → ℚ) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) (output : Z3.FourierMode) →
  let
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
  in
  Pair.pairDifferenceWorkSum
    (Pair.cellRate rho) (Pair.cellWork mixed value) items
  ≡ pairDifferenceVectorWorkSum
      (Pair.cellRate rho) mixed value items
fixedOutputPhysicalPairDifferenceIsVectorDifferenceWorkSum
    rho S velocity cutoff output =
  pairDifferenceWorkSumIsVectorDifferenceWorkSum
    (Pair.cellRate rho)
    (R224.foldVector
      (D1a.mixedProductCell S velocity)
      (Output.physicalOutputFiber cutoff output))
    (D1a.mixedProductCell S velocity)
    (Output.physicalOutputFiber cutoff output)

------------------------------------------------------------------------
-- Trust boundary.
------------------------------------------------------------------------

fixedOutputWorkDifferenceVectorBridgeClosed : Bool
fixedOutputWorkDifferenceVectorBridgeClosed = true

fixedOutputPairDifferenceAggregateVectorBridgeClosed : Bool
fixedOutputPairDifferenceAggregateVectorBridgeClosed = true

fixedOutputPairDifferenceAggregateVectorBridgeClosedIsTrue :
  fixedOutputPairDifferenceAggregateVectorBridgeClosed ≡ true
fixedOutputPairDifferenceAggregateVectorBridgeClosedIsTrue = refl

fixedOutputWorkDifferenceVectorBridgeUsesAbsoluteValue : Bool
fixedOutputWorkDifferenceVectorBridgeUsesAbsoluteValue = false

fixedOutputWorkDifferenceVectorBridgeAddsQuantitativePayment : Bool
fixedOutputWorkDifferenceVectorBridgeAddsQuantitativePayment = false

fixedOutputWorkDifferenceVectorBridgeClosedIsTrue :
  fixedOutputWorkDifferenceVectorBridgeClosed ≡ true
fixedOutputWorkDifferenceVectorBridgeClosedIsTrue = refl

fixedOutputWorkDifferenceVectorBridgeUsesAbsoluteValueIsFalse :
  fixedOutputWorkDifferenceVectorBridgeUsesAbsoluteValue ≡ false
fixedOutputWorkDifferenceVectorBridgeUsesAbsoluteValueIsFalse = refl

fixedOutputWorkDifferenceVectorBridgeAddsQuantitativePaymentIsFalse :
  fixedOutputWorkDifferenceVectorBridgeAddsQuantitativePayment ≡ false
fixedOutputWorkDifferenceVectorBridgeAddsQuantitativePaymentIsFalse = refl

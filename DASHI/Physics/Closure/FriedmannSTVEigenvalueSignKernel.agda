module DASHI.Physics.Closure.FriedmannSTVEigenvalueSignKernel where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

------------------------------------------------------------------------
-- Concrete algebraic kernel for the Alexander-Temple-Vogler STV spectrum.
--
-- The paper gives, at STV order n >= 1,
--
--   lambda_A(n) = 2n / 3
--   lambda_B(n) = (2n - 5) / 3.
--
-- We avoid any analytic or observational promotion here.  This module
-- proves only the exact sign pattern needed by the phase-portrait argument:
-- both A modes are positive, B is negative at n = 1 and n = 2, and B is
-- positive at every n >= 3.  After the n = 1 time-translation gauge mode is
-- removed, the sole remaining negative eigendirection is B at order n = 2.

------------------------------------------------------------------------
-- Exact thirds and their signs.

data Sign : Set where
  positive negative : Sign

record Thirds : Set where
  constructor _/3
  field
    sign : Sign
    magnitude : Nat

open Thirds public

data Positive : Thirds -> Set where
  positiveThirds : {m : Nat} -> Positive (positive /3 m)

data Negative : Thirds -> Set where
  negativeThirds : {m : Nat} -> Negative (negative /3 m)

------------------------------------------------------------------------
-- STV orders.  higher k denotes n = 3 + k.

data STVOrder : Set where
  orderOne orderTwo : STVOrder
  higher : Nat -> STVOrder

orderNumber : STVOrder -> Nat
orderNumber orderOne = 1
orderNumber orderTwo = 2
orderNumber (higher k) = 3 + k

lambdaA : STVOrder -> Thirds
lambdaA orderOne = positive /3 2
lambdaA orderTwo = positive /3 4
lambdaA (higher k) = positive /3 (6 + (k + k))

lambdaB : STVOrder -> Thirds
lambdaB orderOne = negative /3 3
lambdaB orderTwo = negative /3 1
lambdaB (higher k) = positive /3 (1 + (k + k))

lambdaAOrderOneExact : lambdaA orderOne ≡ positive /3 2
lambdaAOrderOneExact = refl

lambdaAOrderTwoExact : lambdaA orderTwo ≡ positive /3 4
lambdaAOrderTwoExact = refl

lambdaBOrderOneExact : lambdaB orderOne ≡ negative /3 3
lambdaBOrderOneExact = refl

lambdaBOrderTwoExact : lambdaB orderTwo ≡ negative /3 1
lambdaBOrderTwoExact = refl

lambdaAHigherExact :
  (k : Nat) -> lambdaA (higher k) ≡ positive /3 (6 + (k + k))
lambdaAHigherExact k = refl

lambdaBHigherExact :
  (k : Nat) -> lambdaB (higher k) ≡ positive /3 (1 + (k + k))
lambdaBHigherExact k = refl

lambdaAAlwaysPositive : (n : STVOrder) -> Positive (lambdaA n)
lambdaAAlwaysPositive orderOne = positiveThirds
lambdaAAlwaysPositive orderTwo = positiveThirds
lambdaAAlwaysPositive (higher k) = positiveThirds

lambdaBOrderOneNegative : Negative (lambdaB orderOne)
lambdaBOrderOneNegative = negativeThirds

lambdaBOrderTwoNegative : Negative (lambdaB orderTwo)
lambdaBOrderTwoNegative = negativeThirds

lambdaBHigherPositive : (k : Nat) -> Positive (lambdaB (higher k))
lambdaBHigherPositive k = positiveThirds

------------------------------------------------------------------------
-- Time-since-the-Big-Bang gauge-fixed spectrum.
--
-- The B mode at order one is the residual SSC time-translation direction.
-- It is therefore absent from the gauge-fixed physical mode family.

data GaugeFixedMode : STVOrder -> Set where
  aOne : GaugeFixedMode orderOne
  aTwo : GaugeFixedMode orderTwo
  bTwo : GaugeFixedMode orderTwo
  aHigher : {k : Nat} -> GaugeFixedMode (higher k)
  bHigher : {k : Nat} -> GaugeFixedMode (higher k)

gaugeFixedEigenvalue : {n : STVOrder} -> GaugeFixedMode n -> Thirds
gaugeFixedEigenvalue aOne = lambdaA orderOne
gaugeFixedEigenvalue aTwo = lambdaA orderTwo
gaugeFixedEigenvalue bTwo = lambdaB orderTwo
gaugeFixedEigenvalue (aHigher {k}) = lambdaA (higher k)
gaugeFixedEigenvalue (bHigher {k}) = lambdaB (higher k)

gaugeFixedOrderOnePositive :
  (m : GaugeFixedMode orderOne) -> Positive (gaugeFixedEigenvalue m)
gaugeFixedOrderOnePositive aOne = positiveThirds

gaugeFixedHigherPositive :
  {k : Nat} ->
  (m : GaugeFixedMode (higher k)) ->
  Positive (gaugeFixedEigenvalue m)
gaugeFixedHigherPositive (aHigher {k}) = positiveThirds
gaugeFixedHigherPositive (bHigher {k}) = positiveThirds

orderTwoBIsNegative : Negative (gaugeFixedEigenvalue bTwo)
orderTwoBIsNegative = negativeThirds

orderTwoBIsUniqueNegative :
  (m : GaugeFixedMode orderTwo) ->
  Negative (gaugeFixedEigenvalue m) ->
  m ≡ bTwo
orderTwoBIsUniqueNegative aTwo ()
orderTwoBIsUniqueNegative bTwo negativeThirds = refl

------------------------------------------------------------------------
-- The theorem-shaped spectral conclusion used by the instability bridge.

record GaugeFixedSTVSpectralKernel : Set where
  field
    orderOneHasOnlyPositivePhysicalMode :
      (m : GaugeFixedMode orderOne) -> Positive (gaugeFixedEigenvalue m)

    orderTwoHasNegativeBMode :
      Negative (gaugeFixedEigenvalue bTwo)

    orderTwoNegativeModeIsUnique :
      (m : GaugeFixedMode orderTwo) ->
      Negative (gaugeFixedEigenvalue m) ->
      m ≡ bTwo

    everyHigherModeIsPositive :
      {k : Nat} ->
      (m : GaugeFixedMode (higher k)) ->
      Positive (gaugeFixedEigenvalue m)

canonicalGaugeFixedSTVSpectralKernel : GaugeFixedSTVSpectralKernel
canonicalGaugeFixedSTVSpectralKernel =
  record
    { orderOneHasOnlyPositivePhysicalMode = gaugeFixedOrderOnePositive
    ; orderTwoHasNegativeBMode = orderTwoBIsNegative
    ; orderTwoNegativeModeIsUnique = orderTwoBIsUniqueNegative
    ; everyHigherModeIsPositive = gaugeFixedHigherPositive
    }

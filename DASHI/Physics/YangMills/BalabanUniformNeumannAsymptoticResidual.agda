module DASHI.Physics.YangMills.BalabanUniformNeumannAsymptoticResidual where

------------------------------------------------------------------------
-- Uniform asymptotic residual theorem for finite Neumann parametrices.
--
-- The theorem deliberately separates two inputs:
--   * the checked finite Neumann telescope and uniform residual-power bound;
--   * eventual vanishing of the common geometric bound power.
--
-- No Archimedean/geometric-convergence fact is assumed here.  It is supplied
-- by BalabanGeometricPowerVanishing.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)
open import Data.Product.Base using (Σ; _,_)

import DASHI.Physics.YangMills.BalabanFiniteNeumannParametrix as Finite
open import DASHI.Physics.YangMills.BalabanUniformWeightedNeumannFamily

record UniformBoundPowerVanishing
  {Index Bound : Set}
  {Carrier : Index → Set}
  {bundle : (index : Index) → Finite.AdditiveParametrixData (Carrier index)}
  (family : UniformWeightedResidualFamily Index Bound Carrier bundle)
  : Set₁ where
  field
    Positive : Bound → Set
    eventuallyBelow : ∀ tolerance → Positive tolerance →
      Σ Nat (λ start →
        ∀ depth → start ≤ depth →
        LessEqual family
          (multiplyBound family
            (uniformBoundPower family depth)
            (oneBound family))
          tolerance)

open UniformBoundPowerVanishing public

uniformUnitBallResidualEventuallyBelow :
  ∀ {Index Bound : Set}
    {Carrier : Index → Set}
    {bundle : (index : Index) → Finite.AdditiveParametrixData (Carrier index)} →
  (family : UniformWeightedResidualFamily Index Bound Carrier bundle) →
  (vanishing : UniformBoundPowerVanishing family) →
  ∀ index value →
  LessEqual family (norm family value) (oneBound family) →
  ∀ tolerance → Positive vanishing tolerance →
  Σ Nat (λ start →
    ∀ depth → start ≤ depth →
    LessEqual family
      (norm family (Finite.residualPower (bundle index) depth value))
      tolerance)
uniformUnitBallResidualEventuallyBelow
  {bundle = bundle} family vanishing index value unitBound tolerance positive
  with eventuallyBelow vanishing tolerance positive
... | start , powerTail =
  start , λ depth start≤depth →
    lessEqualTrans family
      (uniformUnitBallResidualPowerBound
        family index depth value unitBound)
      (powerTail depth start≤depth)

record UniformNeumannAsymptoticResidual
  {Index Bound : Set}
  {Carrier : Index → Set}
  {bundle : (index : Index) → Finite.AdditiveParametrixData (Carrier index)}
  (family : UniformWeightedResidualFamily Index Bound Carrier bundle)
  : Set₁ where
  field
    powerVanishing : UniformBoundPowerVanishing family

open UniformNeumannAsymptoticResidual public

neumannResidualEventuallyBelow :
  ∀ {Index Bound : Set}
    {Carrier : Index → Set}
    {bundle : (index : Index) → Finite.AdditiveParametrixData (Carrier index)} →
  (family : UniformWeightedResidualFamily Index Bound Carrier bundle) →
  (asymptotic : UniformNeumannAsymptoticResidual family) →
  ∀ index value →
  LessEqual family (norm family value) (oneBound family) →
  ∀ tolerance → Positive (powerVanishing asymptotic) tolerance →
  Σ Nat (λ start →
    ∀ depth → start ≤ depth →
    LessEqual family
      (norm family (Finite.residualPower (bundle index) depth value))
      tolerance)
neumannResidualEventuallyBelow family asymptotic =
  uniformUnitBallResidualEventuallyBelow
    family (powerVanishing asymptotic)

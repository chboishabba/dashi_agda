module DASHI.Physics.YangMills.BalabanUniformNeumannAsymptoticResidual where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Nat.Base using (_≤_)
open import Data.Product.Base using (_×_; _,_)

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
    eventuallyBelow :
      ∀ tolerance →
      Positive tolerance →
      Σ Nat (λ start →
        ∀ depth →
        start ≤ depth →
        LessEqual family
          (multiplyBound family
            (uniformBoundPower family depth)
            (oneBound family))
          tolerance)

open UniformBoundPowerVanishing public

uniformUnitBallResidualEventuallyBelow :
  ∀ {Index Bound : Set}
    {Carrier : Index → Set}
    {bundle : (index : Index) → Finite.AdditiveParametrixData (Carrier index)}
    (family : UniformWeightedResidualFamily Index Bound Carrier bundle) →
  (vanishing : UniformBoundPowerVanishing family) →
  ∀ tolerance →
  Positive vanishing tolerance →
  Σ Nat (λ start →
    ∀ index depth value →
    start ≤ depth →
    LessEqual family (norm family value) (oneBound family) →
    LessEqual family
      (norm family
        (Finite.residualPower (bundle index) depth value))
      tolerance)
uniformUnitBallResidualEventuallyBelow family vanishing tolerance positive
  with eventuallyBelow vanishing tolerance positive
... | start , scalarEventually =
  start , λ index depth value start≤depth unitBound →
    lessEqualTrans family
      (uniformUnitBallResidualPowerBound
        family index depth value unitBound)
      (scalarEventually depth start≤depth)

uniformFiniteNeumannEventuallyApproximate :
  ∀ {Index Bound : Set}
    {Carrier : Index → Set}
    {bundle : (index : Index) → Finite.AdditiveParametrixData (Carrier index)}
    (family : UniformWeightedResidualFamily Index Bound Carrier bundle) →
  (vanishing : UniformBoundPowerVanishing family) →
  ∀ tolerance →
  Positive vanishing tolerance →
  Σ Nat (λ start →
    ∀ index depth value →
    start ≤ depth →
    LessEqual family (norm family value) (oneBound family) →
    (Finite.operator (bundle index)
        (Finite.finiteNeumannApproximation (bundle index) depth value)
      ≡ Finite.subtract (bundle index) value
          (Finite.residualPower (bundle index) depth value))
    × LessEqual family
      (norm family
        (Finite.residualPower (bundle index) depth value))
      tolerance)
uniformFiniteNeumannEventuallyApproximate
  {bundle = bundle} family vanishing tolerance positive
  with uniformUnitBallResidualEventuallyBelow
    family vanishing tolerance positive
... | start , residualEventually =
  start , λ index depth value start≤depth unitBound →
    Finite.finiteRightNeumannTelescope (bundle index) depth value
    , residualEventually index depth value start≤depth unitBound

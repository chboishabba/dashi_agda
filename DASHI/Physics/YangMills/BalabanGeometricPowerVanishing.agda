module DASHI.Physics.YangMills.BalabanGeometricPowerVanishing where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.YangMills.BalabanFiniteNeumannParametrix as Finite
open import DASHI.Physics.YangMills.BalabanUniformWeightedNeumannFamily
open import DASHI.Physics.YangMills.BalabanUniformNeumannAsymptoticResidual

------------------------------------------------------------------------
-- The abstract weighted-family record deliberately does not assert enough
-- order structure to infer geometric convergence from rho < 1.  This module
-- adds exactly the missing algebraic order laws and proves the finite tail
-- argument.  The remaining Archimedean fact is isolated as coverage of every
-- positive tolerance by some geometric power.
------------------------------------------------------------------------

record GeometricPowerOrderLaws
  {Index Bound : Set}
  {Carrier : Index → Set}
  {bundle : (index : Index) → Finite.AdditiveParametrixData (Carrier index)}
  (family : UniformWeightedResidualFamily Index Bound Carrier bundle)
  : Set₁ where
  field
    strictToNonStrict : ∀ {left right} →
      StrictLess family left right → LessEqual family left right

    multiplyMonotoneLeft : ∀ suffix {left right} →
      LessEqual family left right →
      LessEqual family
        (multiplyBound family left suffix)
        (multiplyBound family right suffix)

    oneRight : ∀ value →
      multiplyBound family value (oneBound family) ≡ value

open GeometricPowerOrderLaws public

uniformPowerStepBelow :
  ∀ {Index Bound : Set}
    {Carrier : Index → Set}
    {bundle : (index : Index) → Finite.AdditiveParametrixData (Carrier index)}
    (family : UniformWeightedResidualFamily Index Bound Carrier bundle) →
    GeometricPowerOrderLaws family →
    ∀ depth →
    LessEqual family
      (uniformBoundPower family (suc depth))
      (uniformBoundPower family depth)
uniformPowerStepBelow family laws depth =
  subst
    (λ upper →
      LessEqual family
        (multiplyBound family
          (uniformBoundPower family depth)
          (contractionFactor family))
        upper)
    (oneRight laws (uniformBoundPower family depth))
    (multiplyMonotoneRight family
      (uniformBoundPower family depth)
      (strictToNonStrict laws (contractionStrict family)))

uniformPowerAntitone :
  ∀ {Index Bound : Set}
    {Carrier : Index → Set}
    {bundle : (index : Index) → Finite.AdditiveParametrixData (Carrier index)}
    (family : UniformWeightedResidualFamily Index Bound Carrier bundle) →
    (laws : GeometricPowerOrderLaws family) →
    ∀ {start depth} →
    start ≤ depth →
    LessEqual family
      (uniformBoundPower family depth)
      (uniformBoundPower family start)
uniformPowerAntitone family laws {zero} {zero} z≤n =
  lessEqualRefl family (uniformBoundPower family zero)
uniformPowerAntitone family laws {zero} {suc depth} z≤n =
  lessEqualTrans family
    (uniformPowerStepBelow family laws depth)
    (uniformPowerAntitone family laws {zero} {depth} z≤n)
uniformPowerAntitone family laws {suc start} {suc depth} (s≤s start≤depth) =
  multiplyMonotoneLeft laws (contractionFactor family)
    (uniformPowerAntitone family laws start≤depth)

record PowerReachableTolerance
  {Index Bound : Set}
  {Carrier : Index → Set}
  {bundle : (index : Index) → Finite.AdditiveParametrixData (Carrier index)}
  (family : UniformWeightedResidualFamily Index Bound Carrier bundle)
  (tolerance : Bound) : Set where
  constructor reachableTolerance
  field
    reachableDepth : Nat
    powerBelowTolerance :
      LessEqual family
        (multiplyBound family
          (uniformBoundPower family reachableDepth)
          (oneBound family))
        tolerance

open PowerReachableTolerance public

reachablePowerVanishing :
  ∀ {Index Bound : Set}
    {Carrier : Index → Set}
    {bundle : (index : Index) → Finite.AdditiveParametrixData (Carrier index)}
    (family : UniformWeightedResidualFamily Index Bound Carrier bundle) →
    GeometricPowerOrderLaws family →
    UniformBoundPowerVanishing family
reachablePowerVanishing family laws = record
  { Positive = PowerReachableTolerance family
  ; eventuallyBelow = λ tolerance reachable →
      reachableDepth reachable , λ depth start≤depth →
        lessEqualTrans family
          (multiplyMonotoneLeft laws (oneBound family)
            (uniformPowerAntitone family laws start≤depth))
          (powerBelowTolerance reachable)
  }

record ArchimedeanPowerCoverage
  {Index Bound : Set}
  {Carrier : Index → Set}
  {bundle : (index : Index) → Finite.AdditiveParametrixData (Carrier index)}
  (family : UniformWeightedResidualFamily Index Bound Carrier bundle)
  : Set₁ where
  field
    Positive : Bound → Set
    positiveToleranceReachable : ∀ tolerance →
      Positive tolerance → PowerReachableTolerance family tolerance

open ArchimedeanPowerCoverage public

coveragePowerVanishing :
  ∀ {Index Bound : Set}
    {Carrier : Index → Set}
    {bundle : (index : Index) → Finite.AdditiveParametrixData (Carrier index)}
    (family : UniformWeightedResidualFamily Index Bound Carrier bundle) →
    (laws : GeometricPowerOrderLaws family) →
    ArchimedeanPowerCoverage family →
    UniformBoundPowerVanishing family
coveragePowerVanishing family laws coverage = record
  { Positive = Positive coverage
  ; eventuallyBelow = λ tolerance positive →
      eventuallyBelow
        (reachablePowerVanishing family laws)
        tolerance
        (positiveToleranceReachable coverage tolerance positive)
  }

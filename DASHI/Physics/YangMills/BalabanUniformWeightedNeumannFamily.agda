module DASHI.Physics.YangMills.BalabanUniformWeightedNeumannFamily where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (subst; trans)

import DASHI.Physics.YangMills.BalabanFiniteNeumannParametrix as Finite
import DASHI.Physics.YangMills.BalabanWeightedNeumannRemainder as Weighted
import DASHI.Physics.YangMills.BalabanRandomWalkRemainderBound as Remainder

-- The index may jointly encode volume, RG scale, admissible background, and
-- patch family.  A single contraction factor is shared by every index.
record UniformWeightedResidualFamily
  (Index Bound : Set)
  (Carrier : Index → Set)
  (bundle : (index : Index) → Finite.AdditiveParametrixData (Carrier index))
  : Set₁ where
  field
    oneBound : Bound
    multiplyBound : Bound → Bound → Bound
    norm : ∀ {index} → Carrier index → Bound
    LessEqual StrictLess : Bound → Bound → Set
    lessEqualRefl : ∀ value → LessEqual value value
    lessEqualTrans : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    multiplyMonotoneRight : ∀ prefix {left right} →
      LessEqual left right →
      LessEqual (multiplyBound prefix left) (multiplyBound prefix right)
    oneLeft : ∀ value → multiplyBound oneBound value ≡ value
    multiplyAssoc : ∀ left middle right →
      multiplyBound left (multiplyBound middle right)
        ≡ multiplyBound (multiplyBound left middle) right
    contractionFactor : Bound
    contractionStrict : StrictLess contractionFactor oneBound
    residualContracts : ∀ index value →
      LessEqual
        (norm (Finite.residual (bundle index) value))
        (multiplyBound contractionFactor (norm value))

open UniformWeightedResidualFamily public

controlAt :
  ∀ {Index Bound : Set} {Carrier : Index → Set}
    {bundle : (index : Index) → Finite.AdditiveParametrixData (Carrier index)} →
  UniformWeightedResidualFamily Index Bound Carrier bundle →
  (index : Index) →
  Weighted.WeightedResidualContraction (Carrier index) Bound (bundle index)
controlAt family index = record
  { oneBound = oneBound family
  ; multiplyBound = multiplyBound family
  ; norm = norm family
  ; LessEqual = LessEqual family
  ; StrictLess = StrictLess family
  ; lessEqualRefl = lessEqualRefl family
  ; lessEqualTrans = lessEqualTrans family
  ; multiplyMonotoneRight = multiplyMonotoneRight family
  ; oneLeft = oneLeft family
  ; multiplyAssoc = multiplyAssoc family
  ; contractionFactor = contractionFactor family
  ; contractionStrict = contractionStrict family
  ; residualContracts = residualContracts family index
  }

uniformBoundPower :
  ∀ {Index Bound : Set} {Carrier : Index → Set}
    {bundle : (index : Index) → Finite.AdditiveParametrixData (Carrier index)} →
  UniformWeightedResidualFamily Index Bound Carrier bundle → Nat → Bound
uniformBoundPower family zero = oneBound family
uniformBoundPower family (suc depth) =
  multiplyBound family (uniformBoundPower family depth) (contractionFactor family)

controlAtBoundPower :
  ∀ {Index Bound : Set} {Carrier : Index → Set}
    {bundle : (index : Index) → Finite.AdditiveParametrixData (Carrier index)}
    (family : UniformWeightedResidualFamily Index Bound Carrier bundle) →
  ∀ index depth →
  Weighted.boundPower (controlAt family index) depth ≡ uniformBoundPower family depth
controlAtBoundPower family index zero = refl
controlAtBoundPower family index (suc depth)
  rewrite controlAtBoundPower family index depth = refl

uniformResidualPowerBound :
  ∀ {Index Bound : Set} {Carrier : Index → Set}
    {bundle : (index : Index) → Finite.AdditiveParametrixData (Carrier index)}
    (family : UniformWeightedResidualFamily Index Bound Carrier bundle) →
  ∀ index depth value →
  LessEqual family
    (norm family (Finite.residualPower (bundle index) depth value))
    (multiplyBound family (uniformBoundPower family depth) (norm family value))
uniformResidualPowerBound {bundle = bundle} family index depth value =
  subst
    (λ power → LessEqual family
      (norm family (Finite.residualPower (bundle index) depth value))
      (multiplyBound family power (norm family value)))
    (controlAtBoundPower family index depth)
    (Weighted.weightedResidualPowerBound (controlAt family index) depth value)

uniformUnitBallResidualPowerBound :
  ∀ {Index Bound : Set} {Carrier : Index → Set}
    {bundle : (index : Index) → Finite.AdditiveParametrixData (Carrier index)}
    (family : UniformWeightedResidualFamily Index Bound Carrier bundle) →
  ∀ index depth value →
  LessEqual family (norm family value) (oneBound family) →
  LessEqual family
    (norm family (Finite.residualPower (bundle index) depth value))
    (multiplyBound family (uniformBoundPower family depth) (oneBound family))
uniformUnitBallResidualPowerBound family index depth value unitBound =
  lessEqualTrans family
    (uniformResidualPowerBound family index depth value)
    (multiplyMonotoneRight family (uniformBoundPower family depth) unitBound)

uniformFiniteNeumannResidualControl :
  ∀ {Index Bound : Set} {Carrier : Index → Set}
    {bundle : (index : Index) → Finite.AdditiveParametrixData (Carrier index)}
    (family : UniformWeightedResidualFamily Index Bound Carrier bundle) →
  ∀ index depth value →
  (Finite.operator (bundle index)
      (Finite.finiteNeumannApproximation (bundle index) depth value)
    ≡ Finite.subtract (bundle index) value
        (Finite.residualPower (bundle index) depth value))
  × LessEqual family
      (norm family (Finite.residualPower (bundle index) depth value))
      (multiplyBound family (uniformBoundPower family depth) (norm family value))
uniformFiniteNeumannResidualControl {bundle = bundle} family index depth value =
  Finite.finiteRightNeumannTelescope (bundle index) depth value
  , uniformResidualPowerBound family index depth value

uniformRandomWalkRemainderBoundAt :
  ∀ {Index Bound : Set} {Carrier : Index → Set}
    {bundle : (index : Index) → Finite.AdditiveParametrixData (Carrier index)} →
  (family : UniformWeightedResidualFamily Index Bound Carrier bundle) →
  (index : Index) → Carrier index →
  Remainder.RandomWalkRemainderBound (Carrier index) Bound
uniformRandomWalkRemainderBoundAt {bundle = bundle} family index value = record
  { remainder = λ depth → Finite.residualPower (bundle index) depth value
  ; norm = norm family
  ; majorant = λ depth →
      multiplyBound family (uniformBoundPower family depth) (norm family value)
  ; LessEqual = LessEqual family
  ; bound = λ depth → uniformResidualPowerBound family index depth value
  }

uniformUnitBallRandomWalkRemainderBoundAt :
  ∀ {Index Bound : Set} {Carrier : Index → Set}
    {bundle : (index : Index) → Finite.AdditiveParametrixData (Carrier index)} →
  (family : UniformWeightedResidualFamily Index Bound Carrier bundle) →
  (index : Index) → (value : Carrier index) →
  LessEqual family (norm family value) (oneBound family) →
  Remainder.RandomWalkRemainderBound (Carrier index) Bound
uniformUnitBallRandomWalkRemainderBoundAt
  {bundle = bundle} family index value unitBound = record
  { remainder = λ depth → Finite.residualPower (bundle index) depth value
  ; norm = norm family
  ; majorant = λ depth →
      multiplyBound family (uniformBoundPower family depth) (oneBound family)
  ; LessEqual = LessEqual family
  ; bound = λ depth →
      uniformUnitBallResidualPowerBound family index depth value unitBound
  }

module DASHI.Physics.YangMills.BalabanSU2CMP98AveragingWeights where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import DASHI.Physics.YangMills.BalabanFiniteOneStepCore using (fold; map)

record CMP98AveragingWeights (Sample Scalar : Set) : Set₁ where
  field
    samples : List Sample
    weight : Sample → Scalar
    zero one : Scalar
    add : Scalar → Scalar → Scalar
    normalized : fold add zero (map weight samples) ≡ one

open CMP98AveragingWeights public

weightedFold :
  ∀ {Sample Scalar Value}
  (weights : CMP98AveragingWeights Sample Scalar) →
  (scale : Scalar → Value → Value) →
  (combine : Value → Value → Value) →
  Value → (Sample → Value) → Value
weightedFold weights scale combine zeroValue value =
  fold combine zeroValue
    (map (λ sample → scale (weight weights sample) (value sample))
      (samples weights))

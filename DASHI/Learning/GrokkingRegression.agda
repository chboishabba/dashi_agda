module DASHI.Learning.GrokkingRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Learning.GrokkingOperatorContract
open import DASHI.Learning.Mod97WeightDecayReceipt
open import DASHI.Learning.Mod97GrokkingBoundary

modulus-regression : modulus ≡ 97
modulus-regression = refl

pair-count-regression : totalPairs ≡ 9409
pair-count-regression = refl

train-count-regression : trainingPairs ≡ 2822
train-count-regression = refl

test-count-regression : testPairs ≡ 6587
test-count-regression = refl

wd600-seed0-regression :
  test95 (observation wd600-s0) ≡ observedAt 11560
wd600-seed0-regression = refl

wd1000-seed2-regression :
  test95 (observation wd1000-s2) ≡ observedAt 8400
wd1000-seed2-regression = refl

boundary-regression : Horizon15000Boundary
boundary-regression = mod97-boundary-15000

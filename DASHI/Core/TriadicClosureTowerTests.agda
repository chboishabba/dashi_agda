module DASHI.Core.TriadicClosureTowerTests where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import DASHI.Core.TriadicClosureTower

sampleCube : TriadicCube
sampleCube neg = neg
sampleCube zer = zer
sampleCube pos = pos

sampleTension : M6Arrow Trit
sampleTension = tension neg pos

sampleClosure : M9Closure Trit
sampleClosure = promoteSix sampleTension zer

sampleClosureSublates : sublate sampleClosure ≡ zer
sampleClosureSublates = refl

sampleSixOfNine : SixOfNine Trit
sampleSixOfNine = tension sampleClosure (close (tension zer pos) pos)

sampleNineOfNine : NineOfNine Trit
sampleNineOfNine = promoteSixOfNine sampleSixOfNine sampleClosure

sampleNineOfNineSublates : sublate sampleNineOfNine ≡ sampleClosure
sampleNineOfNineSublates = refl

threeTowerTwoWitness : tower 3 2 ≡ 27
threeTowerTwoWitness = threeTowerTwo

-- This checks only the type-level recurrence.  The carrier is intentionally not
-- enumerated: its cardinality is 3 ^ (3 ^ 3), not 27.
threeSuperThreeSuperThreeIdentity :
  ThreeSuperThreeSuperThree → ThreeSuperThreeSuperThree
threeSuperThreeSuperThreeIdentity x = x

-- Eight stacked 9s are represented intensionally as an iterated function space.
nineClosureHeightEightIdentity :
  NineClosureHeightEight → NineClosureHeightEight
nineClosureHeightEightIdentity x = x

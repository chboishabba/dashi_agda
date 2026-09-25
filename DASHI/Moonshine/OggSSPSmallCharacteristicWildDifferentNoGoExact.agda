module DASHI.Moonshine.OggSSPSmallCharacteristicWildDifferentNoGoExact where

------------------------------------------------------------------------
-- RAW WILD-DIFFERENT COEFFICIENT NO-GO
--
-- Kobin--Zureick-Brown compute the wild stacky canonical-divisor contribution
-- at the unique small-characteristic stacky point.  After rigidification, the
-- local wild Riemann--Hurwitz contribution is:
--
--   characteristic 2 : 14
--   characteristic 3 :  7
--
-- The Duncan--Swisher Monster-exponent gaps are:
--
--   p=2 : 10
--   p=3 :  2.
--
-- Therefore the naive rule
--
--   exceptional Monster gap = raw wild different/canonical coefficient
--
-- is false at both primes.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSPSmallCharacteristicWildStackCorrectionConjectureExact as Wild
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

p2WildDifferentCoefficient : Nat
p2WildDifferentCoefficient = 14

p3WildDifferentCoefficient : Nat
p3WildDifferentCoefficient = 7

p2MonsterResidual : Nat
p2MonsterResidual =
  Wild.wildGeometricSectorCount Wild.primeTwo

p3MonsterResidual : Nat
p3MonsterResidual =
  Wild.wildGeometricSectorCount Wild.primeThree

p2WildDifferentIsNotMonsterResidual :
  p2WildDifferentCoefficient ≡ p2MonsterResidual -> ⊥
p2WildDifferentIsNotMonsterResidual ()

p3WildDifferentIsNotMonsterResidual :
  p3WildDifferentCoefficient ≡ p3MonsterResidual -> ⊥
p3WildDifferentIsNotMonsterResidual ()

data RawWildDifferentExplainsP2Gap : Set where
data RawWildDifferentExplainsP3Gap : Set where

rawWildDifferentDoesNotExplainP2Gap :
  RawWildDifferentExplainsP2Gap -> ⊥
rawWildDifferentDoesNotExplainP2Gap ()

rawWildDifferentDoesNotExplainP3Gap :
  RawWildDifferentExplainsP3Gap -> ⊥
rawWildDifferentDoesNotExplainP3Gap ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction

record WildDifferentNoGoBoundary : Set where
  constructor wild-different-no-go-boundary
  field
    p2WildDifferentFourteenRecorded : Bool
    p3WildDifferentSevenRecorded : Bool
    p2ResidualTenRecorded : Bool
    p3ResidualTwoRecorded : Bool
    rawDifferentEqualsP2Residual : Bool
    rawDifferentEqualsP3Residual : Bool
    wildStackMechanismStillPossibleThroughOtherObservable : Bool

canonicalWildDifferentNoGoBoundary :
  WildDifferentNoGoBoundary
canonicalWildDifferentNoGoBoundary =
  wild-different-no-go-boundary
    true true true true false false true

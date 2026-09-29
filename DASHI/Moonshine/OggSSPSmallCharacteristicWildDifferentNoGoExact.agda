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
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Moonshine.OggSSPSmallCharacteristicWildStackCorrectionConjectureExact as Wild
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Exponent
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- 1. SOURCE-NATIVE RAMIFICATION FILTRATION PAYMENT
--
-- Kobin--Zureick-Brown (2025), §4.1, Remarks 4.1 and 4.5:
--     p=3: G0=S3 (order 6), G1=C3 (order 3), jump m=1;
--     p=2: G0=A4 (order 12), G1=V4 (order 4), jump m=1.
-- In the lower-numbered different formula sum_i (|G_i|-1),
-- the first two contributions are therefore 5+2 and 11+3.
-- These are NOT Monster-exponent valuation terms.
------------------------------------------------------------------------

record JumpOneRamificationLayers : Set where
  constructor jump-one-ramification-layers
  field
    fullInertiaOrder : Nat
    firstWildGroupOrder : Nat
    zeroLayerDifferent : Nat
    firstLayerDifferent : Nat
    fullOrderSuccessor : fullInertiaOrder ≡ 1 + zeroLayerDifferent
    wildOrderSuccessor : firstWildGroupOrder ≡ 1 + firstLayerDifferent

open JumpOneRamificationLayers public

p2RamificationLayers : JumpOneRamificationLayers
p2RamificationLayers =
  jump-one-ramification-layers 12 4 11 3 refl refl

p3RamificationLayers : JumpOneRamificationLayers
p3RamificationLayers =
  jump-one-ramification-layers 6 3 5 2 refl refl

differentFromJumpOne :
  JumpOneRamificationLayers -> Nat
differentFromJumpOne layers =
  zeroLayerDifferent layers + firstLayerDifferent layers

p2WildDifferentCoefficient : Nat
p2WildDifferentCoefficient = differentFromJumpOne p2RamificationLayers

p3WildDifferentCoefficient : Nat
p3WildDifferentCoefficient = differentFromJumpOne p3RamificationLayers

p2DifferentDerivedFromFiltration :
  p2WildDifferentCoefficient ≡ 14
p2DifferentDerivedFromFiltration = refl

p3DifferentDerivedFromFiltration :
  p3WildDifferentCoefficient ≡ 7
p3DifferentDerivedFromFiltration = refl

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

-- Attribution-preserving payment: the *arithmetic* gaps come from the
-- Duncan--Swisher continuation owner (which does not claim a p=2/3 theorem).
-- The geometric sectors are independently constructed in Wild.  These
-- equalities compare two sources; they do not identify their meanings.
p2ArithmeticGapIsSectorCount :
  Exponent.monsterOrderExponent Lane.p2
  ≡ Exponent.duncanSwisherExceptionalRHS Lane.p2 + p2MonsterResidual
p2ArithmeticGapIsSectorCount = Exponent.p2ExceptionalGap

p3ArithmeticGapIsSectorCount :
  Exponent.monsterOrderExponent Lane.p3
  ≡ Exponent.duncanSwisherExceptionalRHS Lane.p3 + p3MonsterResidual
p3ArithmeticGapIsSectorCount = Exponent.p3ExceptionalGap

-- The exact source-native filtration produces different coefficients;
-- neither identity can be promoted into the valuation contribution.

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
